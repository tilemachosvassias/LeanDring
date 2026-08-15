/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Data.ColCdd.C018
import LeanDring.P5.Data.ColCdd.C019
import LeanDring.P5.Data.ColRestCheap.C080
import LeanDring.P5.Data.ColRestCheap.C081
import LeanDring.P5.Data.ColRestCheap.C082
import LeanDring.P5.Data.ColRestCheap.C083
import LeanDring.P5.Data.EntryK.C037
import LeanDring.P5.Data.EntryK.C038
import LeanDring.P5.Certificate.RingIsomorphism.MatchCore
import LeanDring.P5.Data.SpeciesDiv.C025
import LeanDring.P5.Data.SpeciesDiv.C026
import LeanDring.P5.Data.SpeciesDiv.C027

/-! # Stage-5 leaves, chunk 40 (auto-emitted).  -/

namespace LeanDring.P5Presentation

open MulAction Finset LeanDring.DRing LeanDring.MonGSet

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.style.longLine false

theorem leaf_137_41_0 (hp : 0 < (Q2.transData.getD 41 []).length)
    (j : Nat) (hj : j < (repChars.getD 137 []).length)
    (hq : (normIsRep.getD 137 []).getD j false = true) :
    species (Q2.reps (⟨41, by decide⟩ : Fin 148)) (colE2 ⟨41, by decide⟩ 0 hp)
        (rowE2 (⟨137, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨41, by decide⟩ : Fin 148))
        (colE1 ⟨41, by decide⟩ 0 (transLenTr ⟨41, by decide⟩ 0 hp))
        (rowE1 (⟨137, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨137, by decide⟩ : Fin 148) ⟨41, by decide⟩ _
      (validAt ⟨137, by decide⟩ (listedAt ⟨137, by decide⟩ hj))
      (colE1 ⟨41, by decide⟩ 0 (transLenTr ⟨41, by decide⟩ 0 hp)) T137_41
      hfix137_41 hinj137_41 hcardT137_41
      (fun i => conj_mem_of_fixedPoints _ _ (T137_41 i) (hfix137_41 i) _)
      ⟨137, by decide⟩ ⟨41, by decide⟩ _
      (Q2.validAt ⟨137, by decide⟩ (Q2.listedAt ⟨137, by decide⟩
        (alnCheck_rep ⟨137, by decide⟩ hj hq).1))
      (colE2 ⟨41, by decide⟩ 0 hp) Q2.T137_41_2 Q2.hfix137_41_2 Q2.hinj137_41_2
      Q2.hcardT137_41_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T137_41_2 i) (Q2.hfix137_41_2 i) _)
      colCert_137_41_0.hD ?_).symm
  rw [alnId_137 j hj]


theorem leaf_137_41_1 (hp : 1 < (Q2.transData.getD 41 []).length)
    (j : Nat) (hj : j < (repChars.getD 137 []).length)
    (hq : (normIsRep.getD 137 []).getD j false = true) :
    species (Q2.reps (⟨41, by decide⟩ : Fin 148)) (colE2 ⟨41, by decide⟩ 1 hp)
        (rowE2 (⟨137, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨41, by decide⟩ : Fin 148))
        (colE1 ⟨41, by decide⟩ 1 (transLenTr ⟨41, by decide⟩ 1 hp))
        (rowE1 (⟨137, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨137, by decide⟩ : Fin 148) ⟨41, by decide⟩ _
      (validAt ⟨137, by decide⟩ (listedAt ⟨137, by decide⟩ hj))
      (colE1 ⟨41, by decide⟩ 1 (transLenTr ⟨41, by decide⟩ 1 hp)) T137_41
      hfix137_41 hinj137_41 hcardT137_41
      (fun i => conj_mem_of_fixedPoints _ _ (T137_41 i) (hfix137_41 i) _)
      ⟨137, by decide⟩ ⟨41, by decide⟩ _
      (Q2.validAt ⟨137, by decide⟩ (Q2.listedAt ⟨137, by decide⟩
        (alnCheck_rep ⟨137, by decide⟩ hj hq).1))
      (colE2 ⟨41, by decide⟩ 1 hp) Q2.T137_41_2 Q2.hfix137_41_2 Q2.hinj137_41_2
      Q2.hcardT137_41_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T137_41_2 i) (Q2.hfix137_41_2 i) _)
      colCert_137_41_1.hD ?_).symm
  rw [alnId_137 j hj]


theorem leaf_137_41_2 (hp : 2 < (Q2.transData.getD 41 []).length)
    (j : Nat) (hj : j < (repChars.getD 137 []).length)
    (hq : (normIsRep.getD 137 []).getD j false = true) :
    species (Q2.reps (⟨41, by decide⟩ : Fin 148)) (colE2 ⟨41, by decide⟩ 2 hp)
        (rowE2 (⟨137, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨41, by decide⟩ : Fin 148))
        (colE1 ⟨41, by decide⟩ 2 (transLenTr ⟨41, by decide⟩ 2 hp))
        (rowE1 (⟨137, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨137, by decide⟩ : Fin 148) ⟨41, by decide⟩ _
      (validAt ⟨137, by decide⟩ (listedAt ⟨137, by decide⟩ hj))
      (colE1 ⟨41, by decide⟩ 2 (transLenTr ⟨41, by decide⟩ 2 hp)) T137_41
      hfix137_41 hinj137_41 hcardT137_41
      (fun i => conj_mem_of_fixedPoints _ _ (T137_41 i) (hfix137_41 i) _)
      ⟨137, by decide⟩ ⟨41, by decide⟩ _
      (Q2.validAt ⟨137, by decide⟩ (Q2.listedAt ⟨137, by decide⟩
        (alnCheck_rep ⟨137, by decide⟩ hj hq).1))
      (colE2 ⟨41, by decide⟩ 2 hp) Q2.T137_41_2 Q2.hfix137_41_2 Q2.hinj137_41_2
      Q2.hcardT137_41_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T137_41_2 i) (Q2.hfix137_41_2 i) _)
      colCert_137_41_2.hD ?_).symm
  rw [alnId_137 j hj]


theorem leaf_137_41_3 (hp : 3 < (Q2.transData.getD 41 []).length)
    (j : Nat) (hj : j < (repChars.getD 137 []).length)
    (hq : (normIsRep.getD 137 []).getD j false = true) :
    species (Q2.reps (⟨41, by decide⟩ : Fin 148)) (colE2 ⟨41, by decide⟩ 3 hp)
        (rowE2 (⟨137, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨41, by decide⟩ : Fin 148))
        (colE1 ⟨41, by decide⟩ 3 (transLenTr ⟨41, by decide⟩ 3 hp))
        (rowE1 (⟨137, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨137, by decide⟩ : Fin 148) ⟨41, by decide⟩ _
      (validAt ⟨137, by decide⟩ (listedAt ⟨137, by decide⟩ hj))
      (colE1 ⟨41, by decide⟩ 3 (transLenTr ⟨41, by decide⟩ 3 hp)) T137_41
      hfix137_41 hinj137_41 hcardT137_41
      (fun i => conj_mem_of_fixedPoints _ _ (T137_41 i) (hfix137_41 i) _)
      ⟨137, by decide⟩ ⟨41, by decide⟩ _
      (Q2.validAt ⟨137, by decide⟩ (Q2.listedAt ⟨137, by decide⟩
        (alnCheck_rep ⟨137, by decide⟩ hj hq).1))
      (colE2 ⟨41, by decide⟩ 3 hp) Q2.T137_41_2 Q2.hfix137_41_2 Q2.hinj137_41_2
      Q2.hcardT137_41_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T137_41_2 i) (Q2.hfix137_41_2 i) _)
      colCert_137_41_3.hD ?_).symm
  rw [alnId_137 j hj]


theorem leaf_137_41_4 (hp : 4 < (Q2.transData.getD 41 []).length)
    (j : Nat) (hj : j < (repChars.getD 137 []).length)
    (hq : (normIsRep.getD 137 []).getD j false = true) :
    species (Q2.reps (⟨41, by decide⟩ : Fin 148)) (colE2 ⟨41, by decide⟩ 4 hp)
        (rowE2 (⟨137, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨41, by decide⟩ : Fin 148))
        (colE1 ⟨41, by decide⟩ 4 (transLenTr ⟨41, by decide⟩ 4 hp))
        (rowE1 (⟨137, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨137, by decide⟩ : Fin 148) ⟨41, by decide⟩ _
      (validAt ⟨137, by decide⟩ (listedAt ⟨137, by decide⟩ hj))
      (colE1 ⟨41, by decide⟩ 4 (transLenTr ⟨41, by decide⟩ 4 hp)) T137_41
      hfix137_41 hinj137_41 hcardT137_41
      (fun i => conj_mem_of_fixedPoints _ _ (T137_41 i) (hfix137_41 i) _)
      ⟨137, by decide⟩ ⟨41, by decide⟩ _
      (Q2.validAt ⟨137, by decide⟩ (Q2.listedAt ⟨137, by decide⟩
        (alnCheck_rep ⟨137, by decide⟩ hj hq).1))
      (colE2 ⟨41, by decide⟩ 4 hp) Q2.T137_41_2 Q2.hfix137_41_2 Q2.hinj137_41_2
      Q2.hcardT137_41_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T137_41_2 i) (Q2.hfix137_41_2 i) _)
      colCert_137_41_4.hD ?_).symm
  rw [alnId_137 j hj]


theorem leaf_137_41_5 (hp : 5 < (Q2.transData.getD 41 []).length)
    (j : Nat) (hj : j < (repChars.getD 137 []).length)
    (hq : (normIsRep.getD 137 []).getD j false = true) :
    species (Q2.reps (⟨41, by decide⟩ : Fin 148)) (colE2 ⟨41, by decide⟩ 5 hp)
        (rowE2 (⟨137, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨41, by decide⟩ : Fin 148))
        (colE1 ⟨41, by decide⟩ 5 (transLenTr ⟨41, by decide⟩ 5 hp))
        (rowE1 (⟨137, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨137, by decide⟩ : Fin 148) ⟨41, by decide⟩ _
      (validAt ⟨137, by decide⟩ (listedAt ⟨137, by decide⟩ hj))
      (colE1 ⟨41, by decide⟩ 5 (transLenTr ⟨41, by decide⟩ 5 hp)) T137_41
      hfix137_41 hinj137_41 hcardT137_41
      (fun i => conj_mem_of_fixedPoints _ _ (T137_41 i) (hfix137_41 i) _)
      ⟨137, by decide⟩ ⟨41, by decide⟩ _
      (Q2.validAt ⟨137, by decide⟩ (Q2.listedAt ⟨137, by decide⟩
        (alnCheck_rep ⟨137, by decide⟩ hj hq).1))
      (colE2 ⟨41, by decide⟩ 5 hp) Q2.T137_41_2 Q2.hfix137_41_2 Q2.hinj137_41_2
      Q2.hcardT137_41_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T137_41_2 i) (Q2.hfix137_41_2 i) _)
      ?_).symm
  rw [show colData1 (⟨137, by decide⟩ : Fin 148)
        ((colE1 ⟨41, by decide⟩ 5 (transLenTr ⟨41, by decide⟩ 5 hp) : ↥(reps ⟨41, by decide⟩)) : Coordinate 1)
        T137_41 = colFn colCertDiv_137_41_5.D1 (m := 5) from colCertDiv_137_41_5.bind1,
    show colData2 (⟨137, by decide⟩ : Fin 148)
        ((colE2 ⟨41, by decide⟩ 5 hp : ↥(Q2.reps ⟨41, by decide⟩)) : Coordinate 2)
        Q2.T137_41_2 = colFn colCertDiv_137_41_5.D2 (m := 5) from colCertDiv_137_41_5.bind2]
  rw [alnId_137 j hj]
  exact fastcode_of_div ⟨137, by decide⟩ _ _ _
    ((alnId_137 j hj) ▸ Q2.listedAt (⟨137, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨137, by decide⟩ : Fin 148) hj hq).1) colCertDiv_137_41_5_match


theorem leaf_137_41_10 (hp : 10 < (Q2.transData.getD 41 []).length)
    (j : Nat) (hj : j < (repChars.getD 137 []).length)
    (hq : (normIsRep.getD 137 []).getD j false = true) :
    species (Q2.reps (⟨41, by decide⟩ : Fin 148)) (colE2 ⟨41, by decide⟩ 10 hp)
        (rowE2 (⟨137, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨41, by decide⟩ : Fin 148))
        (colE1 ⟨41, by decide⟩ 10 (transLenTr ⟨41, by decide⟩ 10 hp))
        (rowE1 (⟨137, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨137, by decide⟩ : Fin 148) ⟨41, by decide⟩ _
      (validAt ⟨137, by decide⟩ (listedAt ⟨137, by decide⟩ hj))
      (colE1 ⟨41, by decide⟩ 10 (transLenTr ⟨41, by decide⟩ 10 hp)) T137_41
      hfix137_41 hinj137_41 hcardT137_41
      (fun i => conj_mem_of_fixedPoints _ _ (T137_41 i) (hfix137_41 i) _)
      ⟨137, by decide⟩ ⟨41, by decide⟩ _
      (Q2.validAt ⟨137, by decide⟩ (Q2.listedAt ⟨137, by decide⟩
        (alnCheck_rep ⟨137, by decide⟩ hj hq).1))
      (colE2 ⟨41, by decide⟩ 10 hp) Q2.T137_41_2 Q2.hfix137_41_2 Q2.hinj137_41_2
      Q2.hcardT137_41_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T137_41_2 i) (Q2.hfix137_41_2 i) _)
      ?_).symm
  rw [show colData1 (⟨137, by decide⟩ : Fin 148)
        ((colE1 ⟨41, by decide⟩ 10 (transLenTr ⟨41, by decide⟩ 10 hp) : ↥(reps ⟨41, by decide⟩)) : Coordinate 1)
        T137_41 = colFn colCertDiv_137_41_10.D1 (m := 5) from colCertDiv_137_41_10.bind1,
    show colData2 (⟨137, by decide⟩ : Fin 148)
        ((colE2 ⟨41, by decide⟩ 10 hp : ↥(Q2.reps ⟨41, by decide⟩)) : Coordinate 2)
        Q2.T137_41_2 = colFn colCertDiv_137_41_10.D2 (m := 5) from colCertDiv_137_41_10.bind2]
  rw [alnId_137 j hj]
  exact fastcode_of_div ⟨137, by decide⟩ _ _ _
    ((alnId_137 j hj) ▸ Q2.listedAt (⟨137, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨137, by decide⟩ : Fin 148) hj hq).1) colCertDiv_137_41_10_match


theorem leaf_137_41_15 (hp : 15 < (Q2.transData.getD 41 []).length)
    (j : Nat) (hj : j < (repChars.getD 137 []).length)
    (hq : (normIsRep.getD 137 []).getD j false = true) :
    species (Q2.reps (⟨41, by decide⟩ : Fin 148)) (colE2 ⟨41, by decide⟩ 15 hp)
        (rowE2 (⟨137, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨41, by decide⟩ : Fin 148))
        (colE1 ⟨41, by decide⟩ 15 (transLenTr ⟨41, by decide⟩ 15 hp))
        (rowE1 (⟨137, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨137, by decide⟩ : Fin 148) ⟨41, by decide⟩ _
      (validAt ⟨137, by decide⟩ (listedAt ⟨137, by decide⟩ hj))
      (colE1 ⟨41, by decide⟩ 15 (transLenTr ⟨41, by decide⟩ 15 hp)) T137_41
      hfix137_41 hinj137_41 hcardT137_41
      (fun i => conj_mem_of_fixedPoints _ _ (T137_41 i) (hfix137_41 i) _)
      ⟨137, by decide⟩ ⟨41, by decide⟩ _
      (Q2.validAt ⟨137, by decide⟩ (Q2.listedAt ⟨137, by decide⟩
        (alnCheck_rep ⟨137, by decide⟩ hj hq).1))
      (colE2 ⟨41, by decide⟩ 15 hp) Q2.T137_41_2 Q2.hfix137_41_2 Q2.hinj137_41_2
      Q2.hcardT137_41_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T137_41_2 i) (Q2.hfix137_41_2 i) _)
      ?_).symm
  rw [show colData1 (⟨137, by decide⟩ : Fin 148)
        ((colE1 ⟨41, by decide⟩ 15 (transLenTr ⟨41, by decide⟩ 15 hp) : ↥(reps ⟨41, by decide⟩)) : Coordinate 1)
        T137_41 = colFn colCertDiv_137_41_15.D1 (m := 5) from colCertDiv_137_41_15.bind1,
    show colData2 (⟨137, by decide⟩ : Fin 148)
        ((colE2 ⟨41, by decide⟩ 15 hp : ↥(Q2.reps ⟨41, by decide⟩)) : Coordinate 2)
        Q2.T137_41_2 = colFn colCertDiv_137_41_15.D2 (m := 5) from colCertDiv_137_41_15.bind2]
  rw [alnId_137 j hj]
  exact fastcode_of_div ⟨137, by decide⟩ _ _ _
    ((alnId_137 j hj) ▸ Q2.listedAt (⟨137, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨137, by decide⟩ : Fin 148) hj hq).1) colCertDiv_137_41_15_match


theorem leaf_137_41_20 (hp : 20 < (Q2.transData.getD 41 []).length)
    (j : Nat) (hj : j < (repChars.getD 137 []).length)
    (hq : (normIsRep.getD 137 []).getD j false = true) :
    species (Q2.reps (⟨41, by decide⟩ : Fin 148)) (colE2 ⟨41, by decide⟩ 20 hp)
        (rowE2 (⟨137, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨41, by decide⟩ : Fin 148))
        (colE1 ⟨41, by decide⟩ 20 (transLenTr ⟨41, by decide⟩ 20 hp))
        (rowE1 (⟨137, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨137, by decide⟩ : Fin 148) ⟨41, by decide⟩ _
      (validAt ⟨137, by decide⟩ (listedAt ⟨137, by decide⟩ hj))
      (colE1 ⟨41, by decide⟩ 20 (transLenTr ⟨41, by decide⟩ 20 hp)) T137_41
      hfix137_41 hinj137_41 hcardT137_41
      (fun i => conj_mem_of_fixedPoints _ _ (T137_41 i) (hfix137_41 i) _)
      ⟨137, by decide⟩ ⟨41, by decide⟩ _
      (Q2.validAt ⟨137, by decide⟩ (Q2.listedAt ⟨137, by decide⟩
        (alnCheck_rep ⟨137, by decide⟩ hj hq).1))
      (colE2 ⟨41, by decide⟩ 20 hp) Q2.T137_41_2 Q2.hfix137_41_2 Q2.hinj137_41_2
      Q2.hcardT137_41_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T137_41_2 i) (Q2.hfix137_41_2 i) _)
      ?_).symm
  rw [show colData1 (⟨137, by decide⟩ : Fin 148)
        ((colE1 ⟨41, by decide⟩ 20 (transLenTr ⟨41, by decide⟩ 20 hp) : ↥(reps ⟨41, by decide⟩)) : Coordinate 1)
        T137_41 = colFn colCertDiv_137_41_20.D1 (m := 5) from colCertDiv_137_41_20.bind1,
    show colData2 (⟨137, by decide⟩ : Fin 148)
        ((colE2 ⟨41, by decide⟩ 20 hp : ↥(Q2.reps ⟨41, by decide⟩)) : Coordinate 2)
        Q2.T137_41_2 = colFn colCertDiv_137_41_20.D2 (m := 5) from colCertDiv_137_41_20.bind2]
  rw [alnId_137 j hj]
  exact fastcode_of_div ⟨137, by decide⟩ _ _ _
    ((alnId_137 j hj) ▸ Q2.listedAt (⟨137, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨137, by decide⟩ : Fin 148) hj hq).1) colCertDiv_137_41_20_match


theorem leaf_137_43_0 (hp : 0 < (Q2.transData.getD 43 []).length)
    (j : Nat) (hj : j < (repChars.getD 137 []).length)
    (hq : (normIsRep.getD 137 []).getD j false = true) :
    species (Q2.reps (⟨43, by decide⟩ : Fin 148)) (colE2 ⟨43, by decide⟩ 0 hp)
        (rowE2 (⟨137, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨43, by decide⟩ : Fin 148))
        (colE1 ⟨43, by decide⟩ 0 (transLenTr ⟨43, by decide⟩ 0 hp))
        (rowE1 (⟨137, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨137, by decide⟩ : Fin 148) ⟨43, by decide⟩ _
      (validAt ⟨137, by decide⟩ (listedAt ⟨137, by decide⟩ hj))
      (colE1 ⟨43, by decide⟩ 0 (transLenTr ⟨43, by decide⟩ 0 hp)) T137_43
      hfix137_43 hinj137_43 hcardT137_43
      (fun i => conj_mem_of_fixedPoints _ _ (T137_43 i) (hfix137_43 i) _)
      ⟨137, by decide⟩ ⟨43, by decide⟩ _
      (Q2.validAt ⟨137, by decide⟩ (Q2.listedAt ⟨137, by decide⟩
        (alnCheck_rep ⟨137, by decide⟩ hj hq).1))
      (colE2 ⟨43, by decide⟩ 0 hp) Q2.T137_43_2 Q2.hfix137_43_2 Q2.hinj137_43_2
      Q2.hcardT137_43_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T137_43_2 i) (Q2.hfix137_43_2 i) _)
      colCert_137_43_0.hD ?_).symm
  rw [alnId_137 j hj]


theorem leaf_137_43_1 (hp : 1 < (Q2.transData.getD 43 []).length)
    (j : Nat) (hj : j < (repChars.getD 137 []).length)
    (hq : (normIsRep.getD 137 []).getD j false = true) :
    species (Q2.reps (⟨43, by decide⟩ : Fin 148)) (colE2 ⟨43, by decide⟩ 1 hp)
        (rowE2 (⟨137, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨43, by decide⟩ : Fin 148))
        (colE1 ⟨43, by decide⟩ 1 (transLenTr ⟨43, by decide⟩ 1 hp))
        (rowE1 (⟨137, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨137, by decide⟩ : Fin 148) ⟨43, by decide⟩ _
      (validAt ⟨137, by decide⟩ (listedAt ⟨137, by decide⟩ hj))
      (colE1 ⟨43, by decide⟩ 1 (transLenTr ⟨43, by decide⟩ 1 hp)) T137_43
      hfix137_43 hinj137_43 hcardT137_43
      (fun i => conj_mem_of_fixedPoints _ _ (T137_43 i) (hfix137_43 i) _)
      ⟨137, by decide⟩ ⟨43, by decide⟩ _
      (Q2.validAt ⟨137, by decide⟩ (Q2.listedAt ⟨137, by decide⟩
        (alnCheck_rep ⟨137, by decide⟩ hj hq).1))
      (colE2 ⟨43, by decide⟩ 1 hp) Q2.T137_43_2 Q2.hfix137_43_2 Q2.hinj137_43_2
      Q2.hcardT137_43_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T137_43_2 i) (Q2.hfix137_43_2 i) _)
      colCert_137_43_1.hD ?_).symm
  rw [alnId_137 j hj]


theorem leaf_137_43_2 (hp : 2 < (Q2.transData.getD 43 []).length)
    (j : Nat) (hj : j < (repChars.getD 137 []).length)
    (hq : (normIsRep.getD 137 []).getD j false = true) :
    species (Q2.reps (⟨43, by decide⟩ : Fin 148)) (colE2 ⟨43, by decide⟩ 2 hp)
        (rowE2 (⟨137, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨43, by decide⟩ : Fin 148))
        (colE1 ⟨43, by decide⟩ 2 (transLenTr ⟨43, by decide⟩ 2 hp))
        (rowE1 (⟨137, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨137, by decide⟩ : Fin 148) ⟨43, by decide⟩ _
      (validAt ⟨137, by decide⟩ (listedAt ⟨137, by decide⟩ hj))
      (colE1 ⟨43, by decide⟩ 2 (transLenTr ⟨43, by decide⟩ 2 hp)) T137_43
      hfix137_43 hinj137_43 hcardT137_43
      (fun i => conj_mem_of_fixedPoints _ _ (T137_43 i) (hfix137_43 i) _)
      ⟨137, by decide⟩ ⟨43, by decide⟩ _
      (Q2.validAt ⟨137, by decide⟩ (Q2.listedAt ⟨137, by decide⟩
        (alnCheck_rep ⟨137, by decide⟩ hj hq).1))
      (colE2 ⟨43, by decide⟩ 2 hp) Q2.T137_43_2 Q2.hfix137_43_2 Q2.hinj137_43_2
      Q2.hcardT137_43_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T137_43_2 i) (Q2.hfix137_43_2 i) _)
      colCert_137_43_2.hD ?_).symm
  rw [alnId_137 j hj]


theorem leaf_137_43_3 (hp : 3 < (Q2.transData.getD 43 []).length)
    (j : Nat) (hj : j < (repChars.getD 137 []).length)
    (hq : (normIsRep.getD 137 []).getD j false = true) :
    species (Q2.reps (⟨43, by decide⟩ : Fin 148)) (colE2 ⟨43, by decide⟩ 3 hp)
        (rowE2 (⟨137, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨43, by decide⟩ : Fin 148))
        (colE1 ⟨43, by decide⟩ 3 (transLenTr ⟨43, by decide⟩ 3 hp))
        (rowE1 (⟨137, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨137, by decide⟩ : Fin 148) ⟨43, by decide⟩ _
      (validAt ⟨137, by decide⟩ (listedAt ⟨137, by decide⟩ hj))
      (colE1 ⟨43, by decide⟩ 3 (transLenTr ⟨43, by decide⟩ 3 hp)) T137_43
      hfix137_43 hinj137_43 hcardT137_43
      (fun i => conj_mem_of_fixedPoints _ _ (T137_43 i) (hfix137_43 i) _)
      ⟨137, by decide⟩ ⟨43, by decide⟩ _
      (Q2.validAt ⟨137, by decide⟩ (Q2.listedAt ⟨137, by decide⟩
        (alnCheck_rep ⟨137, by decide⟩ hj hq).1))
      (colE2 ⟨43, by decide⟩ 3 hp) Q2.T137_43_2 Q2.hfix137_43_2 Q2.hinj137_43_2
      Q2.hcardT137_43_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T137_43_2 i) (Q2.hfix137_43_2 i) _)
      colCert_137_43_3.hD ?_).symm
  rw [alnId_137 j hj]


theorem leaf_137_43_4 (hp : 4 < (Q2.transData.getD 43 []).length)
    (j : Nat) (hj : j < (repChars.getD 137 []).length)
    (hq : (normIsRep.getD 137 []).getD j false = true) :
    species (Q2.reps (⟨43, by decide⟩ : Fin 148)) (colE2 ⟨43, by decide⟩ 4 hp)
        (rowE2 (⟨137, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨43, by decide⟩ : Fin 148))
        (colE1 ⟨43, by decide⟩ 4 (transLenTr ⟨43, by decide⟩ 4 hp))
        (rowE1 (⟨137, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨137, by decide⟩ : Fin 148) ⟨43, by decide⟩ _
      (validAt ⟨137, by decide⟩ (listedAt ⟨137, by decide⟩ hj))
      (colE1 ⟨43, by decide⟩ 4 (transLenTr ⟨43, by decide⟩ 4 hp)) T137_43
      hfix137_43 hinj137_43 hcardT137_43
      (fun i => conj_mem_of_fixedPoints _ _ (T137_43 i) (hfix137_43 i) _)
      ⟨137, by decide⟩ ⟨43, by decide⟩ _
      (Q2.validAt ⟨137, by decide⟩ (Q2.listedAt ⟨137, by decide⟩
        (alnCheck_rep ⟨137, by decide⟩ hj hq).1))
      (colE2 ⟨43, by decide⟩ 4 hp) Q2.T137_43_2 Q2.hfix137_43_2 Q2.hinj137_43_2
      Q2.hcardT137_43_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T137_43_2 i) (Q2.hfix137_43_2 i) _)
      colCert_137_43_4.hD ?_).symm
  rw [alnId_137 j hj]


theorem leaf_137_43_5 (hp : 5 < (Q2.transData.getD 43 []).length)
    (j : Nat) (hj : j < (repChars.getD 137 []).length)
    (hq : (normIsRep.getD 137 []).getD j false = true) :
    species (Q2.reps (⟨43, by decide⟩ : Fin 148)) (colE2 ⟨43, by decide⟩ 5 hp)
        (rowE2 (⟨137, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨43, by decide⟩ : Fin 148))
        (colE1 ⟨43, by decide⟩ 5 (transLenTr ⟨43, by decide⟩ 5 hp))
        (rowE1 (⟨137, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨137, by decide⟩ : Fin 148) ⟨43, by decide⟩ _
      (validAt ⟨137, by decide⟩ (listedAt ⟨137, by decide⟩ hj))
      (colE1 ⟨43, by decide⟩ 5 (transLenTr ⟨43, by decide⟩ 5 hp)) T137_43
      hfix137_43 hinj137_43 hcardT137_43
      (fun i => conj_mem_of_fixedPoints _ _ (T137_43 i) (hfix137_43 i) _)
      ⟨137, by decide⟩ ⟨43, by decide⟩ _
      (Q2.validAt ⟨137, by decide⟩ (Q2.listedAt ⟨137, by decide⟩
        (alnCheck_rep ⟨137, by decide⟩ hj hq).1))
      (colE2 ⟨43, by decide⟩ 5 hp) Q2.T137_43_2 Q2.hfix137_43_2 Q2.hinj137_43_2
      Q2.hcardT137_43_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T137_43_2 i) (Q2.hfix137_43_2 i) _)
      ?_).symm
  rw [show colData1 (⟨137, by decide⟩ : Fin 148)
        ((colE1 ⟨43, by decide⟩ 5 (transLenTr ⟨43, by decide⟩ 5 hp) : ↥(reps ⟨43, by decide⟩)) : Coordinate 1)
        T137_43 = colFn colCertDiv_137_43_5.D1 (m := 5) from colCertDiv_137_43_5.bind1,
    show colData2 (⟨137, by decide⟩ : Fin 148)
        ((colE2 ⟨43, by decide⟩ 5 hp : ↥(Q2.reps ⟨43, by decide⟩)) : Coordinate 2)
        Q2.T137_43_2 = colFn colCertDiv_137_43_5.D2 (m := 5) from colCertDiv_137_43_5.bind2]
  rw [alnId_137 j hj]
  exact fastcode_of_div ⟨137, by decide⟩ _ _ _
    ((alnId_137 j hj) ▸ Q2.listedAt (⟨137, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨137, by decide⟩ : Fin 148) hj hq).1) colCertDiv_137_43_5_match


theorem leaf_137_43_10 (hp : 10 < (Q2.transData.getD 43 []).length)
    (j : Nat) (hj : j < (repChars.getD 137 []).length)
    (hq : (normIsRep.getD 137 []).getD j false = true) :
    species (Q2.reps (⟨43, by decide⟩ : Fin 148)) (colE2 ⟨43, by decide⟩ 10 hp)
        (rowE2 (⟨137, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨43, by decide⟩ : Fin 148))
        (colE1 ⟨43, by decide⟩ 10 (transLenTr ⟨43, by decide⟩ 10 hp))
        (rowE1 (⟨137, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨137, by decide⟩ : Fin 148) ⟨43, by decide⟩ _
      (validAt ⟨137, by decide⟩ (listedAt ⟨137, by decide⟩ hj))
      (colE1 ⟨43, by decide⟩ 10 (transLenTr ⟨43, by decide⟩ 10 hp)) T137_43
      hfix137_43 hinj137_43 hcardT137_43
      (fun i => conj_mem_of_fixedPoints _ _ (T137_43 i) (hfix137_43 i) _)
      ⟨137, by decide⟩ ⟨43, by decide⟩ _
      (Q2.validAt ⟨137, by decide⟩ (Q2.listedAt ⟨137, by decide⟩
        (alnCheck_rep ⟨137, by decide⟩ hj hq).1))
      (colE2 ⟨43, by decide⟩ 10 hp) Q2.T137_43_2 Q2.hfix137_43_2 Q2.hinj137_43_2
      Q2.hcardT137_43_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T137_43_2 i) (Q2.hfix137_43_2 i) _)
      ?_).symm
  rw [show colData1 (⟨137, by decide⟩ : Fin 148)
        ((colE1 ⟨43, by decide⟩ 10 (transLenTr ⟨43, by decide⟩ 10 hp) : ↥(reps ⟨43, by decide⟩)) : Coordinate 1)
        T137_43 = colFn colCertDiv_137_43_10.D1 (m := 5) from colCertDiv_137_43_10.bind1,
    show colData2 (⟨137, by decide⟩ : Fin 148)
        ((colE2 ⟨43, by decide⟩ 10 hp : ↥(Q2.reps ⟨43, by decide⟩)) : Coordinate 2)
        Q2.T137_43_2 = colFn colCertDiv_137_43_10.D2 (m := 5) from colCertDiv_137_43_10.bind2]
  rw [alnId_137 j hj]
  exact fastcode_of_div ⟨137, by decide⟩ _ _ _
    ((alnId_137 j hj) ▸ Q2.listedAt (⟨137, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨137, by decide⟩ : Fin 148) hj hq).1) colCertDiv_137_43_10_match


theorem leaf_137_43_15 (hp : 15 < (Q2.transData.getD 43 []).length)
    (j : Nat) (hj : j < (repChars.getD 137 []).length)
    (hq : (normIsRep.getD 137 []).getD j false = true) :
    species (Q2.reps (⟨43, by decide⟩ : Fin 148)) (colE2 ⟨43, by decide⟩ 15 hp)
        (rowE2 (⟨137, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨43, by decide⟩ : Fin 148))
        (colE1 ⟨43, by decide⟩ 15 (transLenTr ⟨43, by decide⟩ 15 hp))
        (rowE1 (⟨137, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨137, by decide⟩ : Fin 148) ⟨43, by decide⟩ _
      (validAt ⟨137, by decide⟩ (listedAt ⟨137, by decide⟩ hj))
      (colE1 ⟨43, by decide⟩ 15 (transLenTr ⟨43, by decide⟩ 15 hp)) T137_43
      hfix137_43 hinj137_43 hcardT137_43
      (fun i => conj_mem_of_fixedPoints _ _ (T137_43 i) (hfix137_43 i) _)
      ⟨137, by decide⟩ ⟨43, by decide⟩ _
      (Q2.validAt ⟨137, by decide⟩ (Q2.listedAt ⟨137, by decide⟩
        (alnCheck_rep ⟨137, by decide⟩ hj hq).1))
      (colE2 ⟨43, by decide⟩ 15 hp) Q2.T137_43_2 Q2.hfix137_43_2 Q2.hinj137_43_2
      Q2.hcardT137_43_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T137_43_2 i) (Q2.hfix137_43_2 i) _)
      ?_).symm
  rw [show colData1 (⟨137, by decide⟩ : Fin 148)
        ((colE1 ⟨43, by decide⟩ 15 (transLenTr ⟨43, by decide⟩ 15 hp) : ↥(reps ⟨43, by decide⟩)) : Coordinate 1)
        T137_43 = colFn colCertDiv_137_43_15.D1 (m := 5) from colCertDiv_137_43_15.bind1,
    show colData2 (⟨137, by decide⟩ : Fin 148)
        ((colE2 ⟨43, by decide⟩ 15 hp : ↥(Q2.reps ⟨43, by decide⟩)) : Coordinate 2)
        Q2.T137_43_2 = colFn colCertDiv_137_43_15.D2 (m := 5) from colCertDiv_137_43_15.bind2]
  rw [alnId_137 j hj]
  exact fastcode_of_div ⟨137, by decide⟩ _ _ _
    ((alnId_137 j hj) ▸ Q2.listedAt (⟨137, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨137, by decide⟩ : Fin 148) hj hq).1) colCertDiv_137_43_15_match


theorem leaf_137_43_20 (hp : 20 < (Q2.transData.getD 43 []).length)
    (j : Nat) (hj : j < (repChars.getD 137 []).length)
    (hq : (normIsRep.getD 137 []).getD j false = true) :
    species (Q2.reps (⟨43, by decide⟩ : Fin 148)) (colE2 ⟨43, by decide⟩ 20 hp)
        (rowE2 (⟨137, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨43, by decide⟩ : Fin 148))
        (colE1 ⟨43, by decide⟩ 20 (transLenTr ⟨43, by decide⟩ 20 hp))
        (rowE1 (⟨137, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨137, by decide⟩ : Fin 148) ⟨43, by decide⟩ _
      (validAt ⟨137, by decide⟩ (listedAt ⟨137, by decide⟩ hj))
      (colE1 ⟨43, by decide⟩ 20 (transLenTr ⟨43, by decide⟩ 20 hp)) T137_43
      hfix137_43 hinj137_43 hcardT137_43
      (fun i => conj_mem_of_fixedPoints _ _ (T137_43 i) (hfix137_43 i) _)
      ⟨137, by decide⟩ ⟨43, by decide⟩ _
      (Q2.validAt ⟨137, by decide⟩ (Q2.listedAt ⟨137, by decide⟩
        (alnCheck_rep ⟨137, by decide⟩ hj hq).1))
      (colE2 ⟨43, by decide⟩ 20 hp) Q2.T137_43_2 Q2.hfix137_43_2 Q2.hinj137_43_2
      Q2.hcardT137_43_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T137_43_2 i) (Q2.hfix137_43_2 i) _)
      ?_).symm
  rw [show colData1 (⟨137, by decide⟩ : Fin 148)
        ((colE1 ⟨43, by decide⟩ 20 (transLenTr ⟨43, by decide⟩ 20 hp) : ↥(reps ⟨43, by decide⟩)) : Coordinate 1)
        T137_43 = colFn colCertDiv_137_43_20.D1 (m := 5) from colCertDiv_137_43_20.bind1,
    show colData2 (⟨137, by decide⟩ : Fin 148)
        ((colE2 ⟨43, by decide⟩ 20 hp : ↥(Q2.reps ⟨43, by decide⟩)) : Coordinate 2)
        Q2.T137_43_2 = colFn colCertDiv_137_43_20.D2 (m := 5) from colCertDiv_137_43_20.bind2]
  rw [alnId_137 j hj]
  exact fastcode_of_div ⟨137, by decide⟩ _ _ _
    ((alnId_137 j hj) ▸ Q2.listedAt (⟨137, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨137, by decide⟩ : Fin 148) hj hq).1) colCertDiv_137_43_20_match


theorem leaf_137_49_0 (hp : 0 < (Q2.transData.getD 49 []).length)
    (j : Nat) (hj : j < (repChars.getD 137 []).length)
    (hq : (normIsRep.getD 137 []).getD j false = true) :
    species (Q2.reps (⟨49, by decide⟩ : Fin 148)) (colE2 ⟨49, by decide⟩ 0 hp)
        (rowE2 (⟨137, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨49, by decide⟩ : Fin 148))
        (colE1 ⟨49, by decide⟩ 0 (transLenTr ⟨49, by decide⟩ 0 hp))
        (rowE1 (⟨137, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨137, by decide⟩ : Fin 148) ⟨49, by decide⟩ _
      (validAt ⟨137, by decide⟩ (listedAt ⟨137, by decide⟩ hj))
      (colE1 ⟨49, by decide⟩ 0 (transLenTr ⟨49, by decide⟩ 0 hp)) T137_49
      hfix137_49 hinj137_49 hcardT137_49
      (fun i => conj_mem_of_fixedPoints _ _ (T137_49 i) (hfix137_49 i) _)
      ⟨137, by decide⟩ ⟨49, by decide⟩ _
      (Q2.validAt ⟨137, by decide⟩ (Q2.listedAt ⟨137, by decide⟩
        (alnCheck_rep ⟨137, by decide⟩ hj hq).1))
      (colE2 ⟨49, by decide⟩ 0 hp) Q2.T137_49_2 Q2.hfix137_49_2 Q2.hinj137_49_2
      Q2.hcardT137_49_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T137_49_2 i) (Q2.hfix137_49_2 i) _)
      colCert_137_49_0.hD ?_).symm
  rw [alnId_137 j hj]


theorem leaf_137_49_1 (hp : 1 < (Q2.transData.getD 49 []).length)
    (j : Nat) (hj : j < (repChars.getD 137 []).length)
    (hq : (normIsRep.getD 137 []).getD j false = true) :
    species (Q2.reps (⟨49, by decide⟩ : Fin 148)) (colE2 ⟨49, by decide⟩ 1 hp)
        (rowE2 (⟨137, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨49, by decide⟩ : Fin 148))
        (colE1 ⟨49, by decide⟩ 1 (transLenTr ⟨49, by decide⟩ 1 hp))
        (rowE1 (⟨137, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨137, by decide⟩ : Fin 148) ⟨49, by decide⟩ _
      (validAt ⟨137, by decide⟩ (listedAt ⟨137, by decide⟩ hj))
      (colE1 ⟨49, by decide⟩ 1 (transLenTr ⟨49, by decide⟩ 1 hp)) T137_49
      hfix137_49 hinj137_49 hcardT137_49
      (fun i => conj_mem_of_fixedPoints _ _ (T137_49 i) (hfix137_49 i) _)
      ⟨137, by decide⟩ ⟨49, by decide⟩ _
      (Q2.validAt ⟨137, by decide⟩ (Q2.listedAt ⟨137, by decide⟩
        (alnCheck_rep ⟨137, by decide⟩ hj hq).1))
      (colE2 ⟨49, by decide⟩ 1 hp) Q2.T137_49_2 Q2.hfix137_49_2 Q2.hinj137_49_2
      Q2.hcardT137_49_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T137_49_2 i) (Q2.hfix137_49_2 i) _)
      colCert_137_49_1.hD ?_).symm
  rw [alnId_137 j hj]


theorem leaf_137_49_2 (hp : 2 < (Q2.transData.getD 49 []).length)
    (j : Nat) (hj : j < (repChars.getD 137 []).length)
    (hq : (normIsRep.getD 137 []).getD j false = true) :
    species (Q2.reps (⟨49, by decide⟩ : Fin 148)) (colE2 ⟨49, by decide⟩ 2 hp)
        (rowE2 (⟨137, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨49, by decide⟩ : Fin 148))
        (colE1 ⟨49, by decide⟩ 2 (transLenTr ⟨49, by decide⟩ 2 hp))
        (rowE1 (⟨137, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨137, by decide⟩ : Fin 148) ⟨49, by decide⟩ _
      (validAt ⟨137, by decide⟩ (listedAt ⟨137, by decide⟩ hj))
      (colE1 ⟨49, by decide⟩ 2 (transLenTr ⟨49, by decide⟩ 2 hp)) T137_49
      hfix137_49 hinj137_49 hcardT137_49
      (fun i => conj_mem_of_fixedPoints _ _ (T137_49 i) (hfix137_49 i) _)
      ⟨137, by decide⟩ ⟨49, by decide⟩ _
      (Q2.validAt ⟨137, by decide⟩ (Q2.listedAt ⟨137, by decide⟩
        (alnCheck_rep ⟨137, by decide⟩ hj hq).1))
      (colE2 ⟨49, by decide⟩ 2 hp) Q2.T137_49_2 Q2.hfix137_49_2 Q2.hinj137_49_2
      Q2.hcardT137_49_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T137_49_2 i) (Q2.hfix137_49_2 i) _)
      colCert_137_49_2.hD ?_).symm
  rw [alnId_137 j hj]


theorem leaf_137_49_3 (hp : 3 < (Q2.transData.getD 49 []).length)
    (j : Nat) (hj : j < (repChars.getD 137 []).length)
    (hq : (normIsRep.getD 137 []).getD j false = true) :
    species (Q2.reps (⟨49, by decide⟩ : Fin 148)) (colE2 ⟨49, by decide⟩ 3 hp)
        (rowE2 (⟨137, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨49, by decide⟩ : Fin 148))
        (colE1 ⟨49, by decide⟩ 3 (transLenTr ⟨49, by decide⟩ 3 hp))
        (rowE1 (⟨137, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨137, by decide⟩ : Fin 148) ⟨49, by decide⟩ _
      (validAt ⟨137, by decide⟩ (listedAt ⟨137, by decide⟩ hj))
      (colE1 ⟨49, by decide⟩ 3 (transLenTr ⟨49, by decide⟩ 3 hp)) T137_49
      hfix137_49 hinj137_49 hcardT137_49
      (fun i => conj_mem_of_fixedPoints _ _ (T137_49 i) (hfix137_49 i) _)
      ⟨137, by decide⟩ ⟨49, by decide⟩ _
      (Q2.validAt ⟨137, by decide⟩ (Q2.listedAt ⟨137, by decide⟩
        (alnCheck_rep ⟨137, by decide⟩ hj hq).1))
      (colE2 ⟨49, by decide⟩ 3 hp) Q2.T137_49_2 Q2.hfix137_49_2 Q2.hinj137_49_2
      Q2.hcardT137_49_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T137_49_2 i) (Q2.hfix137_49_2 i) _)
      colCert_137_49_3.hD ?_).symm
  rw [alnId_137 j hj]


theorem leaf_137_49_4 (hp : 4 < (Q2.transData.getD 49 []).length)
    (j : Nat) (hj : j < (repChars.getD 137 []).length)
    (hq : (normIsRep.getD 137 []).getD j false = true) :
    species (Q2.reps (⟨49, by decide⟩ : Fin 148)) (colE2 ⟨49, by decide⟩ 4 hp)
        (rowE2 (⟨137, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨49, by decide⟩ : Fin 148))
        (colE1 ⟨49, by decide⟩ 4 (transLenTr ⟨49, by decide⟩ 4 hp))
        (rowE1 (⟨137, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨137, by decide⟩ : Fin 148) ⟨49, by decide⟩ _
      (validAt ⟨137, by decide⟩ (listedAt ⟨137, by decide⟩ hj))
      (colE1 ⟨49, by decide⟩ 4 (transLenTr ⟨49, by decide⟩ 4 hp)) T137_49
      hfix137_49 hinj137_49 hcardT137_49
      (fun i => conj_mem_of_fixedPoints _ _ (T137_49 i) (hfix137_49 i) _)
      ⟨137, by decide⟩ ⟨49, by decide⟩ _
      (Q2.validAt ⟨137, by decide⟩ (Q2.listedAt ⟨137, by decide⟩
        (alnCheck_rep ⟨137, by decide⟩ hj hq).1))
      (colE2 ⟨49, by decide⟩ 4 hp) Q2.T137_49_2 Q2.hfix137_49_2 Q2.hinj137_49_2
      Q2.hcardT137_49_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T137_49_2 i) (Q2.hfix137_49_2 i) _)
      colCert_137_49_4.hD ?_).symm
  rw [alnId_137 j hj]


theorem leaf_137_49_5 (hp : 5 < (Q2.transData.getD 49 []).length)
    (j : Nat) (hj : j < (repChars.getD 137 []).length)
    (hq : (normIsRep.getD 137 []).getD j false = true) :
    species (Q2.reps (⟨49, by decide⟩ : Fin 148)) (colE2 ⟨49, by decide⟩ 5 hp)
        (rowE2 (⟨137, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨49, by decide⟩ : Fin 148))
        (colE1 ⟨49, by decide⟩ 5 (transLenTr ⟨49, by decide⟩ 5 hp))
        (rowE1 (⟨137, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨137, by decide⟩ : Fin 148) ⟨49, by decide⟩ _
      (validAt ⟨137, by decide⟩ (listedAt ⟨137, by decide⟩ hj))
      (colE1 ⟨49, by decide⟩ 5 (transLenTr ⟨49, by decide⟩ 5 hp)) T137_49
      hfix137_49 hinj137_49 hcardT137_49
      (fun i => conj_mem_of_fixedPoints _ _ (T137_49 i) (hfix137_49 i) _)
      ⟨137, by decide⟩ ⟨49, by decide⟩ _
      (Q2.validAt ⟨137, by decide⟩ (Q2.listedAt ⟨137, by decide⟩
        (alnCheck_rep ⟨137, by decide⟩ hj hq).1))
      (colE2 ⟨49, by decide⟩ 5 hp) Q2.T137_49_2 Q2.hfix137_49_2 Q2.hinj137_49_2
      Q2.hcardT137_49_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T137_49_2 i) (Q2.hfix137_49_2 i) _)
      colCert_137_49_5.hD ?_).symm
  rw [alnId_137 j hj]


theorem leaf_137_49_10 (hp : 10 < (Q2.transData.getD 49 []).length)
    (j : Nat) (hj : j < (repChars.getD 137 []).length)
    (hq : (normIsRep.getD 137 []).getD j false = true) :
    species (Q2.reps (⟨49, by decide⟩ : Fin 148)) (colE2 ⟨49, by decide⟩ 10 hp)
        (rowE2 (⟨137, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨49, by decide⟩ : Fin 148))
        (colE1 ⟨49, by decide⟩ 10 (transLenTr ⟨49, by decide⟩ 10 hp))
        (rowE1 (⟨137, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨137, by decide⟩ : Fin 148) ⟨49, by decide⟩ _
      (validAt ⟨137, by decide⟩ (listedAt ⟨137, by decide⟩ hj))
      (colE1 ⟨49, by decide⟩ 10 (transLenTr ⟨49, by decide⟩ 10 hp)) T137_49
      hfix137_49 hinj137_49 hcardT137_49
      (fun i => conj_mem_of_fixedPoints _ _ (T137_49 i) (hfix137_49 i) _)
      ⟨137, by decide⟩ ⟨49, by decide⟩ _
      (Q2.validAt ⟨137, by decide⟩ (Q2.listedAt ⟨137, by decide⟩
        (alnCheck_rep ⟨137, by decide⟩ hj hq).1))
      (colE2 ⟨49, by decide⟩ 10 hp) Q2.T137_49_2 Q2.hfix137_49_2 Q2.hinj137_49_2
      Q2.hcardT137_49_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T137_49_2 i) (Q2.hfix137_49_2 i) _)
      ?_).symm
  rw [show colData1 (⟨137, by decide⟩ : Fin 148)
        ((colE1 ⟨49, by decide⟩ 10 (transLenTr ⟨49, by decide⟩ 10 hp) : ↥(reps ⟨49, by decide⟩)) : Coordinate 1)
        T137_49 = colFn colCertDiv_137_49_10.D1 (m := 5) from colCertDiv_137_49_10.bind1,
    show colData2 (⟨137, by decide⟩ : Fin 148)
        ((colE2 ⟨49, by decide⟩ 10 hp : ↥(Q2.reps ⟨49, by decide⟩)) : Coordinate 2)
        Q2.T137_49_2 = colFn colCertDiv_137_49_10.D2 (m := 5) from colCertDiv_137_49_10.bind2]
  rw [alnId_137 j hj]
  exact fastcode_of_div ⟨137, by decide⟩ _ _ _
    ((alnId_137 j hj) ▸ Q2.listedAt (⟨137, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨137, by decide⟩ : Fin 148) hj hq).1) colCertDiv_137_49_10_match


theorem leaf_137_49_15 (hp : 15 < (Q2.transData.getD 49 []).length)
    (j : Nat) (hj : j < (repChars.getD 137 []).length)
    (hq : (normIsRep.getD 137 []).getD j false = true) :
    species (Q2.reps (⟨49, by decide⟩ : Fin 148)) (colE2 ⟨49, by decide⟩ 15 hp)
        (rowE2 (⟨137, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨49, by decide⟩ : Fin 148))
        (colE1 ⟨49, by decide⟩ 15 (transLenTr ⟨49, by decide⟩ 15 hp))
        (rowE1 (⟨137, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨137, by decide⟩ : Fin 148) ⟨49, by decide⟩ _
      (validAt ⟨137, by decide⟩ (listedAt ⟨137, by decide⟩ hj))
      (colE1 ⟨49, by decide⟩ 15 (transLenTr ⟨49, by decide⟩ 15 hp)) T137_49
      hfix137_49 hinj137_49 hcardT137_49
      (fun i => conj_mem_of_fixedPoints _ _ (T137_49 i) (hfix137_49 i) _)
      ⟨137, by decide⟩ ⟨49, by decide⟩ _
      (Q2.validAt ⟨137, by decide⟩ (Q2.listedAt ⟨137, by decide⟩
        (alnCheck_rep ⟨137, by decide⟩ hj hq).1))
      (colE2 ⟨49, by decide⟩ 15 hp) Q2.T137_49_2 Q2.hfix137_49_2 Q2.hinj137_49_2
      Q2.hcardT137_49_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T137_49_2 i) (Q2.hfix137_49_2 i) _)
      ?_).symm
  rw [show colData1 (⟨137, by decide⟩ : Fin 148)
        ((colE1 ⟨49, by decide⟩ 15 (transLenTr ⟨49, by decide⟩ 15 hp) : ↥(reps ⟨49, by decide⟩)) : Coordinate 1)
        T137_49 = colFn colCertDiv_137_49_15.D1 (m := 5) from colCertDiv_137_49_15.bind1,
    show colData2 (⟨137, by decide⟩ : Fin 148)
        ((colE2 ⟨49, by decide⟩ 15 hp : ↥(Q2.reps ⟨49, by decide⟩)) : Coordinate 2)
        Q2.T137_49_2 = colFn colCertDiv_137_49_15.D2 (m := 5) from colCertDiv_137_49_15.bind2]
  rw [alnId_137 j hj]
  exact fastcode_of_div ⟨137, by decide⟩ _ _ _
    ((alnId_137 j hj) ▸ Q2.listedAt (⟨137, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨137, by decide⟩ : Fin 148) hj hq).1) colCertDiv_137_49_15_match


theorem leaf_137_49_20 (hp : 20 < (Q2.transData.getD 49 []).length)
    (j : Nat) (hj : j < (repChars.getD 137 []).length)
    (hq : (normIsRep.getD 137 []).getD j false = true) :
    species (Q2.reps (⟨49, by decide⟩ : Fin 148)) (colE2 ⟨49, by decide⟩ 20 hp)
        (rowE2 (⟨137, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨49, by decide⟩ : Fin 148))
        (colE1 ⟨49, by decide⟩ 20 (transLenTr ⟨49, by decide⟩ 20 hp))
        (rowE1 (⟨137, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨137, by decide⟩ : Fin 148) ⟨49, by decide⟩ _
      (validAt ⟨137, by decide⟩ (listedAt ⟨137, by decide⟩ hj))
      (colE1 ⟨49, by decide⟩ 20 (transLenTr ⟨49, by decide⟩ 20 hp)) T137_49
      hfix137_49 hinj137_49 hcardT137_49
      (fun i => conj_mem_of_fixedPoints _ _ (T137_49 i) (hfix137_49 i) _)
      ⟨137, by decide⟩ ⟨49, by decide⟩ _
      (Q2.validAt ⟨137, by decide⟩ (Q2.listedAt ⟨137, by decide⟩
        (alnCheck_rep ⟨137, by decide⟩ hj hq).1))
      (colE2 ⟨49, by decide⟩ 20 hp) Q2.T137_49_2 Q2.hfix137_49_2 Q2.hinj137_49_2
      Q2.hcardT137_49_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T137_49_2 i) (Q2.hfix137_49_2 i) _)
      ?_).symm
  rw [show colData1 (⟨137, by decide⟩ : Fin 148)
        ((colE1 ⟨49, by decide⟩ 20 (transLenTr ⟨49, by decide⟩ 20 hp) : ↥(reps ⟨49, by decide⟩)) : Coordinate 1)
        T137_49 = colFn colCertDiv_137_49_20.D1 (m := 5) from colCertDiv_137_49_20.bind1,
    show colData2 (⟨137, by decide⟩ : Fin 148)
        ((colE2 ⟨49, by decide⟩ 20 hp : ↥(Q2.reps ⟨49, by decide⟩)) : Coordinate 2)
        Q2.T137_49_2 = colFn colCertDiv_137_49_20.D2 (m := 5) from colCertDiv_137_49_20.bind2]
  rw [alnId_137 j hj]
  exact fastcode_of_div ⟨137, by decide⟩ _ _ _
    ((alnId_137 j hj) ▸ Q2.listedAt (⟨137, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨137, by decide⟩ : Fin 148) hj hq).1) colCertDiv_137_49_20_match


theorem leaf_137_53_0 (hp : 0 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 137 []).length)
    (hq : (normIsRep.getD 137 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 0 hp)
        (rowE2 (⟨137, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 0 (transLenTr ⟨53, by decide⟩ 0 hp))
        (rowE1 (⟨137, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨137, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨137, by decide⟩ (listedAt ⟨137, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 0 (transLenTr ⟨53, by decide⟩ 0 hp)) T137_53
      hfix137_53 hinj137_53 hcardT137_53
      (fun i => conj_mem_of_fixedPoints _ _ (T137_53 i) (hfix137_53 i) _)
      ⟨137, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨137, by decide⟩ (Q2.listedAt ⟨137, by decide⟩
        (alnCheck_rep ⟨137, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 0 hp) Q2.T137_53_2 Q2.hfix137_53_2 Q2.hinj137_53_2
      Q2.hcardT137_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T137_53_2 i) (Q2.hfix137_53_2 i) _)
      colCert_137_53_0.hD ?_).symm
  rw [alnId_137 j hj]


theorem leaf_137_53_1 (hp : 1 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 137 []).length)
    (hq : (normIsRep.getD 137 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 1 hp)
        (rowE2 (⟨137, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 1 (transLenTr ⟨53, by decide⟩ 1 hp))
        (rowE1 (⟨137, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨137, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨137, by decide⟩ (listedAt ⟨137, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 1 (transLenTr ⟨53, by decide⟩ 1 hp)) T137_53
      hfix137_53 hinj137_53 hcardT137_53
      (fun i => conj_mem_of_fixedPoints _ _ (T137_53 i) (hfix137_53 i) _)
      ⟨137, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨137, by decide⟩ (Q2.listedAt ⟨137, by decide⟩
        (alnCheck_rep ⟨137, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 1 hp) Q2.T137_53_2 Q2.hfix137_53_2 Q2.hinj137_53_2
      Q2.hcardT137_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T137_53_2 i) (Q2.hfix137_53_2 i) _)
      colCert_137_53_1.hD ?_).symm
  rw [alnId_137 j hj]


theorem leaf_137_53_2 (hp : 2 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 137 []).length)
    (hq : (normIsRep.getD 137 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 2 hp)
        (rowE2 (⟨137, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 2 (transLenTr ⟨53, by decide⟩ 2 hp))
        (rowE1 (⟨137, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨137, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨137, by decide⟩ (listedAt ⟨137, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 2 (transLenTr ⟨53, by decide⟩ 2 hp)) T137_53
      hfix137_53 hinj137_53 hcardT137_53
      (fun i => conj_mem_of_fixedPoints _ _ (T137_53 i) (hfix137_53 i) _)
      ⟨137, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨137, by decide⟩ (Q2.listedAt ⟨137, by decide⟩
        (alnCheck_rep ⟨137, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 2 hp) Q2.T137_53_2 Q2.hfix137_53_2 Q2.hinj137_53_2
      Q2.hcardT137_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T137_53_2 i) (Q2.hfix137_53_2 i) _)
      colCert_137_53_2.hD ?_).symm
  rw [alnId_137 j hj]


theorem leaf_137_53_3 (hp : 3 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 137 []).length)
    (hq : (normIsRep.getD 137 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 3 hp)
        (rowE2 (⟨137, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 3 (transLenTr ⟨53, by decide⟩ 3 hp))
        (rowE1 (⟨137, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨137, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨137, by decide⟩ (listedAt ⟨137, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 3 (transLenTr ⟨53, by decide⟩ 3 hp)) T137_53
      hfix137_53 hinj137_53 hcardT137_53
      (fun i => conj_mem_of_fixedPoints _ _ (T137_53 i) (hfix137_53 i) _)
      ⟨137, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨137, by decide⟩ (Q2.listedAt ⟨137, by decide⟩
        (alnCheck_rep ⟨137, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 3 hp) Q2.T137_53_2 Q2.hfix137_53_2 Q2.hinj137_53_2
      Q2.hcardT137_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T137_53_2 i) (Q2.hfix137_53_2 i) _)
      colCert_137_53_3.hD ?_).symm
  rw [alnId_137 j hj]


theorem leaf_137_53_4 (hp : 4 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 137 []).length)
    (hq : (normIsRep.getD 137 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 4 hp)
        (rowE2 (⟨137, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 4 (transLenTr ⟨53, by decide⟩ 4 hp))
        (rowE1 (⟨137, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨137, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨137, by decide⟩ (listedAt ⟨137, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 4 (transLenTr ⟨53, by decide⟩ 4 hp)) T137_53
      hfix137_53 hinj137_53 hcardT137_53
      (fun i => conj_mem_of_fixedPoints _ _ (T137_53 i) (hfix137_53 i) _)
      ⟨137, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨137, by decide⟩ (Q2.listedAt ⟨137, by decide⟩
        (alnCheck_rep ⟨137, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 4 hp) Q2.T137_53_2 Q2.hfix137_53_2 Q2.hinj137_53_2
      Q2.hcardT137_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T137_53_2 i) (Q2.hfix137_53_2 i) _)
      colCert_137_53_4.hD ?_).symm
  rw [alnId_137 j hj]


theorem leaf_137_53_5 (hp : 5 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 137 []).length)
    (hq : (normIsRep.getD 137 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 5 hp)
        (rowE2 (⟨137, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 5 (transLenTr ⟨53, by decide⟩ 5 hp))
        (rowE1 (⟨137, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨137, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨137, by decide⟩ (listedAt ⟨137, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 5 (transLenTr ⟨53, by decide⟩ 5 hp)) T137_53
      hfix137_53 hinj137_53 hcardT137_53
      (fun i => conj_mem_of_fixedPoints _ _ (T137_53 i) (hfix137_53 i) _)
      ⟨137, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨137, by decide⟩ (Q2.listedAt ⟨137, by decide⟩
        (alnCheck_rep ⟨137, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 5 hp) Q2.T137_53_2 Q2.hfix137_53_2 Q2.hinj137_53_2
      Q2.hcardT137_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T137_53_2 i) (Q2.hfix137_53_2 i) _)
      colCert_137_53_5.hD ?_).symm
  rw [alnId_137 j hj]


theorem leaf_137_53_10 (hp : 10 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 137 []).length)
    (hq : (normIsRep.getD 137 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 10 hp)
        (rowE2 (⟨137, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 10 (transLenTr ⟨53, by decide⟩ 10 hp))
        (rowE1 (⟨137, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨137, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨137, by decide⟩ (listedAt ⟨137, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 10 (transLenTr ⟨53, by decide⟩ 10 hp)) T137_53
      hfix137_53 hinj137_53 hcardT137_53
      (fun i => conj_mem_of_fixedPoints _ _ (T137_53 i) (hfix137_53 i) _)
      ⟨137, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨137, by decide⟩ (Q2.listedAt ⟨137, by decide⟩
        (alnCheck_rep ⟨137, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 10 hp) Q2.T137_53_2 Q2.hfix137_53_2 Q2.hinj137_53_2
      Q2.hcardT137_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T137_53_2 i) (Q2.hfix137_53_2 i) _)
      colCert_137_53_10.hD ?_).symm
  rw [alnId_137 j hj]


theorem leaf_137_53_15 (hp : 15 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 137 []).length)
    (hq : (normIsRep.getD 137 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 15 hp)
        (rowE2 (⟨137, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 15 (transLenTr ⟨53, by decide⟩ 15 hp))
        (rowE1 (⟨137, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨137, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨137, by decide⟩ (listedAt ⟨137, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 15 (transLenTr ⟨53, by decide⟩ 15 hp)) T137_53
      hfix137_53 hinj137_53 hcardT137_53
      (fun i => conj_mem_of_fixedPoints _ _ (T137_53 i) (hfix137_53 i) _)
      ⟨137, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨137, by decide⟩ (Q2.listedAt ⟨137, by decide⟩
        (alnCheck_rep ⟨137, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 15 hp) Q2.T137_53_2 Q2.hfix137_53_2 Q2.hinj137_53_2
      Q2.hcardT137_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T137_53_2 i) (Q2.hfix137_53_2 i) _)
      colCert_137_53_15.hD ?_).symm
  rw [alnId_137 j hj]


theorem leaf_137_53_20 (hp : 20 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 137 []).length)
    (hq : (normIsRep.getD 137 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 20 hp)
        (rowE2 (⟨137, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 20 (transLenTr ⟨53, by decide⟩ 20 hp))
        (rowE1 (⟨137, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨137, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨137, by decide⟩ (listedAt ⟨137, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 20 (transLenTr ⟨53, by decide⟩ 20 hp)) T137_53
      hfix137_53 hinj137_53 hcardT137_53
      (fun i => conj_mem_of_fixedPoints _ _ (T137_53 i) (hfix137_53 i) _)
      ⟨137, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨137, by decide⟩ (Q2.listedAt ⟨137, by decide⟩
        (alnCheck_rep ⟨137, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 20 hp) Q2.T137_53_2 Q2.hfix137_53_2 Q2.hinj137_53_2
      Q2.hcardT137_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T137_53_2 i) (Q2.hfix137_53_2 i) _)
      colCert_137_53_20.hD ?_).symm
  rw [alnId_137 j hj]


theorem leaf_137_84_0 (hp : 0 < (Q2.transData.getD 84 []).length)
    (j : Nat) (hj : j < (repChars.getD 137 []).length)
    (hq : (normIsRep.getD 137 []).getD j false = true) :
    species (Q2.reps (⟨84, by decide⟩ : Fin 148)) (colE2 ⟨84, by decide⟩ 0 hp)
        (rowE2 (⟨137, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨84, by decide⟩ : Fin 148))
        (colE1 ⟨84, by decide⟩ 0 (transLenTr ⟨84, by decide⟩ 0 hp))
        (rowE1 (⟨137, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨137, by decide⟩ : Fin 148) ⟨84, by decide⟩ _
      (validAt ⟨137, by decide⟩ (listedAt ⟨137, by decide⟩ hj))
      (colE1 ⟨84, by decide⟩ 0 (transLenTr ⟨84, by decide⟩ 0 hp)) T137_84
      hfix137_84 hinj137_84 hcardT137_84
      (fun i => conj_mem_of_fixedPoints _ _ (T137_84 i) (hfix137_84 i) _)
      ⟨137, by decide⟩ ⟨84, by decide⟩ _
      (Q2.validAt ⟨137, by decide⟩ (Q2.listedAt ⟨137, by decide⟩
        (alnCheck_rep ⟨137, by decide⟩ hj hq).1))
      (colE2 ⟨84, by decide⟩ 0 hp) Q2.T137_84_2 Q2.hfix137_84_2 Q2.hinj137_84_2
      Q2.hcardT137_84_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T137_84_2 i) (Q2.hfix137_84_2 i) _)
      colCert_137_84_0.hD ?_).symm
  rw [alnId_137 j hj]


theorem leaf_137_84_1 (hp : 1 < (Q2.transData.getD 84 []).length)
    (j : Nat) (hj : j < (repChars.getD 137 []).length)
    (hq : (normIsRep.getD 137 []).getD j false = true) :
    species (Q2.reps (⟨84, by decide⟩ : Fin 148)) (colE2 ⟨84, by decide⟩ 1 hp)
        (rowE2 (⟨137, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨84, by decide⟩ : Fin 148))
        (colE1 ⟨84, by decide⟩ 1 (transLenTr ⟨84, by decide⟩ 1 hp))
        (rowE1 (⟨137, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨137, by decide⟩ : Fin 148) ⟨84, by decide⟩ _
      (validAt ⟨137, by decide⟩ (listedAt ⟨137, by decide⟩ hj))
      (colE1 ⟨84, by decide⟩ 1 (transLenTr ⟨84, by decide⟩ 1 hp)) T137_84
      hfix137_84 hinj137_84 hcardT137_84
      (fun i => conj_mem_of_fixedPoints _ _ (T137_84 i) (hfix137_84 i) _)
      ⟨137, by decide⟩ ⟨84, by decide⟩ _
      (Q2.validAt ⟨137, by decide⟩ (Q2.listedAt ⟨137, by decide⟩
        (alnCheck_rep ⟨137, by decide⟩ hj hq).1))
      (colE2 ⟨84, by decide⟩ 1 hp) Q2.T137_84_2 Q2.hfix137_84_2 Q2.hinj137_84_2
      Q2.hcardT137_84_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T137_84_2 i) (Q2.hfix137_84_2 i) _)
      colCert_137_84_1.hD ?_).symm
  rw [alnId_137 j hj]


theorem leaf_137_84_2 (hp : 2 < (Q2.transData.getD 84 []).length)
    (j : Nat) (hj : j < (repChars.getD 137 []).length)
    (hq : (normIsRep.getD 137 []).getD j false = true) :
    species (Q2.reps (⟨84, by decide⟩ : Fin 148)) (colE2 ⟨84, by decide⟩ 2 hp)
        (rowE2 (⟨137, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨84, by decide⟩ : Fin 148))
        (colE1 ⟨84, by decide⟩ 2 (transLenTr ⟨84, by decide⟩ 2 hp))
        (rowE1 (⟨137, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨137, by decide⟩ : Fin 148) ⟨84, by decide⟩ _
      (validAt ⟨137, by decide⟩ (listedAt ⟨137, by decide⟩ hj))
      (colE1 ⟨84, by decide⟩ 2 (transLenTr ⟨84, by decide⟩ 2 hp)) T137_84
      hfix137_84 hinj137_84 hcardT137_84
      (fun i => conj_mem_of_fixedPoints _ _ (T137_84 i) (hfix137_84 i) _)
      ⟨137, by decide⟩ ⟨84, by decide⟩ _
      (Q2.validAt ⟨137, by decide⟩ (Q2.listedAt ⟨137, by decide⟩
        (alnCheck_rep ⟨137, by decide⟩ hj hq).1))
      (colE2 ⟨84, by decide⟩ 2 hp) Q2.T137_84_2 Q2.hfix137_84_2 Q2.hinj137_84_2
      Q2.hcardT137_84_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T137_84_2 i) (Q2.hfix137_84_2 i) _)
      colCert_137_84_2.hD ?_).symm
  rw [alnId_137 j hj]


theorem leaf_137_84_3 (hp : 3 < (Q2.transData.getD 84 []).length)
    (j : Nat) (hj : j < (repChars.getD 137 []).length)
    (hq : (normIsRep.getD 137 []).getD j false = true) :
    species (Q2.reps (⟨84, by decide⟩ : Fin 148)) (colE2 ⟨84, by decide⟩ 3 hp)
        (rowE2 (⟨137, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨84, by decide⟩ : Fin 148))
        (colE1 ⟨84, by decide⟩ 3 (transLenTr ⟨84, by decide⟩ 3 hp))
        (rowE1 (⟨137, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨137, by decide⟩ : Fin 148) ⟨84, by decide⟩ _
      (validAt ⟨137, by decide⟩ (listedAt ⟨137, by decide⟩ hj))
      (colE1 ⟨84, by decide⟩ 3 (transLenTr ⟨84, by decide⟩ 3 hp)) T137_84
      hfix137_84 hinj137_84 hcardT137_84
      (fun i => conj_mem_of_fixedPoints _ _ (T137_84 i) (hfix137_84 i) _)
      ⟨137, by decide⟩ ⟨84, by decide⟩ _
      (Q2.validAt ⟨137, by decide⟩ (Q2.listedAt ⟨137, by decide⟩
        (alnCheck_rep ⟨137, by decide⟩ hj hq).1))
      (colE2 ⟨84, by decide⟩ 3 hp) Q2.T137_84_2 Q2.hfix137_84_2 Q2.hinj137_84_2
      Q2.hcardT137_84_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T137_84_2 i) (Q2.hfix137_84_2 i) _)
      colCert_137_84_3.hD ?_).symm
  rw [alnId_137 j hj]


theorem leaf_137_84_4 (hp : 4 < (Q2.transData.getD 84 []).length)
    (j : Nat) (hj : j < (repChars.getD 137 []).length)
    (hq : (normIsRep.getD 137 []).getD j false = true) :
    species (Q2.reps (⟨84, by decide⟩ : Fin 148)) (colE2 ⟨84, by decide⟩ 4 hp)
        (rowE2 (⟨137, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨84, by decide⟩ : Fin 148))
        (colE1 ⟨84, by decide⟩ 4 (transLenTr ⟨84, by decide⟩ 4 hp))
        (rowE1 (⟨137, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨137, by decide⟩ : Fin 148) ⟨84, by decide⟩ _
      (validAt ⟨137, by decide⟩ (listedAt ⟨137, by decide⟩ hj))
      (colE1 ⟨84, by decide⟩ 4 (transLenTr ⟨84, by decide⟩ 4 hp)) T137_84
      hfix137_84 hinj137_84 hcardT137_84
      (fun i => conj_mem_of_fixedPoints _ _ (T137_84 i) (hfix137_84 i) _)
      ⟨137, by decide⟩ ⟨84, by decide⟩ _
      (Q2.validAt ⟨137, by decide⟩ (Q2.listedAt ⟨137, by decide⟩
        (alnCheck_rep ⟨137, by decide⟩ hj hq).1))
      (colE2 ⟨84, by decide⟩ 4 hp) Q2.T137_84_2 Q2.hfix137_84_2 Q2.hinj137_84_2
      Q2.hcardT137_84_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T137_84_2 i) (Q2.hfix137_84_2 i) _)
      colCert_137_84_4.hD ?_).symm
  rw [alnId_137 j hj]


theorem leaf_137_84_5 (hp : 5 < (Q2.transData.getD 84 []).length)
    (j : Nat) (hj : j < (repChars.getD 137 []).length)
    (hq : (normIsRep.getD 137 []).getD j false = true) :
    species (Q2.reps (⟨84, by decide⟩ : Fin 148)) (colE2 ⟨84, by decide⟩ 5 hp)
        (rowE2 (⟨137, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨84, by decide⟩ : Fin 148))
        (colE1 ⟨84, by decide⟩ 5 (transLenTr ⟨84, by decide⟩ 5 hp))
        (rowE1 (⟨137, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨137, by decide⟩ : Fin 148) ⟨84, by decide⟩ _
      (validAt ⟨137, by decide⟩ (listedAt ⟨137, by decide⟩ hj))
      (colE1 ⟨84, by decide⟩ 5 (transLenTr ⟨84, by decide⟩ 5 hp)) T137_84
      hfix137_84 hinj137_84 hcardT137_84
      (fun i => conj_mem_of_fixedPoints _ _ (T137_84 i) (hfix137_84 i) _)
      ⟨137, by decide⟩ ⟨84, by decide⟩ _
      (Q2.validAt ⟨137, by decide⟩ (Q2.listedAt ⟨137, by decide⟩
        (alnCheck_rep ⟨137, by decide⟩ hj hq).1))
      (colE2 ⟨84, by decide⟩ 5 hp) Q2.T137_84_2 Q2.hfix137_84_2 Q2.hinj137_84_2
      Q2.hcardT137_84_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T137_84_2 i) (Q2.hfix137_84_2 i) _)
      colCert_137_84_5.hD ?_).symm
  rw [alnId_137 j hj]


theorem leaf_137_84_10 (hp : 10 < (Q2.transData.getD 84 []).length)
    (j : Nat) (hj : j < (repChars.getD 137 []).length)
    (hq : (normIsRep.getD 137 []).getD j false = true) :
    species (Q2.reps (⟨84, by decide⟩ : Fin 148)) (colE2 ⟨84, by decide⟩ 10 hp)
        (rowE2 (⟨137, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨84, by decide⟩ : Fin 148))
        (colE1 ⟨84, by decide⟩ 10 (transLenTr ⟨84, by decide⟩ 10 hp))
        (rowE1 (⟨137, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨137, by decide⟩ : Fin 148) ⟨84, by decide⟩ _
      (validAt ⟨137, by decide⟩ (listedAt ⟨137, by decide⟩ hj))
      (colE1 ⟨84, by decide⟩ 10 (transLenTr ⟨84, by decide⟩ 10 hp)) T137_84
      hfix137_84 hinj137_84 hcardT137_84
      (fun i => conj_mem_of_fixedPoints _ _ (T137_84 i) (hfix137_84 i) _)
      ⟨137, by decide⟩ ⟨84, by decide⟩ _
      (Q2.validAt ⟨137, by decide⟩ (Q2.listedAt ⟨137, by decide⟩
        (alnCheck_rep ⟨137, by decide⟩ hj hq).1))
      (colE2 ⟨84, by decide⟩ 10 hp) Q2.T137_84_2 Q2.hfix137_84_2 Q2.hinj137_84_2
      Q2.hcardT137_84_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T137_84_2 i) (Q2.hfix137_84_2 i) _)
      colCert_137_84_10.hD ?_).symm
  rw [alnId_137 j hj]


theorem leaf_137_84_15 (hp : 15 < (Q2.transData.getD 84 []).length)
    (j : Nat) (hj : j < (repChars.getD 137 []).length)
    (hq : (normIsRep.getD 137 []).getD j false = true) :
    species (Q2.reps (⟨84, by decide⟩ : Fin 148)) (colE2 ⟨84, by decide⟩ 15 hp)
        (rowE2 (⟨137, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨84, by decide⟩ : Fin 148))
        (colE1 ⟨84, by decide⟩ 15 (transLenTr ⟨84, by decide⟩ 15 hp))
        (rowE1 (⟨137, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨137, by decide⟩ : Fin 148) ⟨84, by decide⟩ _
      (validAt ⟨137, by decide⟩ (listedAt ⟨137, by decide⟩ hj))
      (colE1 ⟨84, by decide⟩ 15 (transLenTr ⟨84, by decide⟩ 15 hp)) T137_84
      hfix137_84 hinj137_84 hcardT137_84
      (fun i => conj_mem_of_fixedPoints _ _ (T137_84 i) (hfix137_84 i) _)
      ⟨137, by decide⟩ ⟨84, by decide⟩ _
      (Q2.validAt ⟨137, by decide⟩ (Q2.listedAt ⟨137, by decide⟩
        (alnCheck_rep ⟨137, by decide⟩ hj hq).1))
      (colE2 ⟨84, by decide⟩ 15 hp) Q2.T137_84_2 Q2.hfix137_84_2 Q2.hinj137_84_2
      Q2.hcardT137_84_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T137_84_2 i) (Q2.hfix137_84_2 i) _)
      colCert_137_84_15.hD ?_).symm
  rw [alnId_137 j hj]


theorem leaf_137_84_20 (hp : 20 < (Q2.transData.getD 84 []).length)
    (j : Nat) (hj : j < (repChars.getD 137 []).length)
    (hq : (normIsRep.getD 137 []).getD j false = true) :
    species (Q2.reps (⟨84, by decide⟩ : Fin 148)) (colE2 ⟨84, by decide⟩ 20 hp)
        (rowE2 (⟨137, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨84, by decide⟩ : Fin 148))
        (colE1 ⟨84, by decide⟩ 20 (transLenTr ⟨84, by decide⟩ 20 hp))
        (rowE1 (⟨137, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨137, by decide⟩ : Fin 148) ⟨84, by decide⟩ _
      (validAt ⟨137, by decide⟩ (listedAt ⟨137, by decide⟩ hj))
      (colE1 ⟨84, by decide⟩ 20 (transLenTr ⟨84, by decide⟩ 20 hp)) T137_84
      hfix137_84 hinj137_84 hcardT137_84
      (fun i => conj_mem_of_fixedPoints _ _ (T137_84 i) (hfix137_84 i) _)
      ⟨137, by decide⟩ ⟨84, by decide⟩ _
      (Q2.validAt ⟨137, by decide⟩ (Q2.listedAt ⟨137, by decide⟩
        (alnCheck_rep ⟨137, by decide⟩ hj hq).1))
      (colE2 ⟨84, by decide⟩ 20 hp) Q2.T137_84_2 Q2.hfix137_84_2 Q2.hinj137_84_2
      Q2.hcardT137_84_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T137_84_2 i) (Q2.hfix137_84_2 i) _)
      colCert_137_84_20.hD ?_).symm
  rw [alnId_137 j hj]


theorem leaf_137_92_0 (hp : 0 < (Q2.transData.getD 92 []).length)
    (j : Nat) (hj : j < (repChars.getD 137 []).length)
    (hq : (normIsRep.getD 137 []).getD j false = true) :
    species (Q2.reps (⟨92, by decide⟩ : Fin 148)) (colE2 ⟨92, by decide⟩ 0 hp)
        (rowE2 (⟨137, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨92, by decide⟩ : Fin 148))
        (colE1 ⟨92, by decide⟩ 0 (transLenTr ⟨92, by decide⟩ 0 hp))
        (rowE1 (⟨137, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨137, by decide⟩ : Fin 148) ⟨92, by decide⟩ _
      (validAt ⟨137, by decide⟩ (listedAt ⟨137, by decide⟩ hj))
      (colE1 ⟨92, by decide⟩ 0 (transLenTr ⟨92, by decide⟩ 0 hp)) T137_92
      hfix137_92 hinj137_92 hcardT137_92
      (fun i => conj_mem_of_fixedPoints _ _ (T137_92 i) (hfix137_92 i) _)
      ⟨137, by decide⟩ ⟨92, by decide⟩ _
      (Q2.validAt ⟨137, by decide⟩ (Q2.listedAt ⟨137, by decide⟩
        (alnCheck_rep ⟨137, by decide⟩ hj hq).1))
      (colE2 ⟨92, by decide⟩ 0 hp) Q2.T137_92_2 Q2.hfix137_92_2 Q2.hinj137_92_2
      Q2.hcardT137_92_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T137_92_2 i) (Q2.hfix137_92_2 i) _)
      colCert_137_92_0.hD ?_).symm
  rw [alnId_137 j hj]


theorem leaf_137_92_1 (hp : 1 < (Q2.transData.getD 92 []).length)
    (j : Nat) (hj : j < (repChars.getD 137 []).length)
    (hq : (normIsRep.getD 137 []).getD j false = true) :
    species (Q2.reps (⟨92, by decide⟩ : Fin 148)) (colE2 ⟨92, by decide⟩ 1 hp)
        (rowE2 (⟨137, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨92, by decide⟩ : Fin 148))
        (colE1 ⟨92, by decide⟩ 1 (transLenTr ⟨92, by decide⟩ 1 hp))
        (rowE1 (⟨137, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨137, by decide⟩ : Fin 148) ⟨92, by decide⟩ _
      (validAt ⟨137, by decide⟩ (listedAt ⟨137, by decide⟩ hj))
      (colE1 ⟨92, by decide⟩ 1 (transLenTr ⟨92, by decide⟩ 1 hp)) T137_92
      hfix137_92 hinj137_92 hcardT137_92
      (fun i => conj_mem_of_fixedPoints _ _ (T137_92 i) (hfix137_92 i) _)
      ⟨137, by decide⟩ ⟨92, by decide⟩ _
      (Q2.validAt ⟨137, by decide⟩ (Q2.listedAt ⟨137, by decide⟩
        (alnCheck_rep ⟨137, by decide⟩ hj hq).1))
      (colE2 ⟨92, by decide⟩ 1 hp) Q2.T137_92_2 Q2.hfix137_92_2 Q2.hinj137_92_2
      Q2.hcardT137_92_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T137_92_2 i) (Q2.hfix137_92_2 i) _)
      colCert_137_92_1.hD ?_).symm
  rw [alnId_137 j hj]


theorem leaf_137_92_2 (hp : 2 < (Q2.transData.getD 92 []).length)
    (j : Nat) (hj : j < (repChars.getD 137 []).length)
    (hq : (normIsRep.getD 137 []).getD j false = true) :
    species (Q2.reps (⟨92, by decide⟩ : Fin 148)) (colE2 ⟨92, by decide⟩ 2 hp)
        (rowE2 (⟨137, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨92, by decide⟩ : Fin 148))
        (colE1 ⟨92, by decide⟩ 2 (transLenTr ⟨92, by decide⟩ 2 hp))
        (rowE1 (⟨137, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨137, by decide⟩ : Fin 148) ⟨92, by decide⟩ _
      (validAt ⟨137, by decide⟩ (listedAt ⟨137, by decide⟩ hj))
      (colE1 ⟨92, by decide⟩ 2 (transLenTr ⟨92, by decide⟩ 2 hp)) T137_92
      hfix137_92 hinj137_92 hcardT137_92
      (fun i => conj_mem_of_fixedPoints _ _ (T137_92 i) (hfix137_92 i) _)
      ⟨137, by decide⟩ ⟨92, by decide⟩ _
      (Q2.validAt ⟨137, by decide⟩ (Q2.listedAt ⟨137, by decide⟩
        (alnCheck_rep ⟨137, by decide⟩ hj hq).1))
      (colE2 ⟨92, by decide⟩ 2 hp) Q2.T137_92_2 Q2.hfix137_92_2 Q2.hinj137_92_2
      Q2.hcardT137_92_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T137_92_2 i) (Q2.hfix137_92_2 i) _)
      colCert_137_92_2.hD ?_).symm
  rw [alnId_137 j hj]


theorem leaf_137_92_3 (hp : 3 < (Q2.transData.getD 92 []).length)
    (j : Nat) (hj : j < (repChars.getD 137 []).length)
    (hq : (normIsRep.getD 137 []).getD j false = true) :
    species (Q2.reps (⟨92, by decide⟩ : Fin 148)) (colE2 ⟨92, by decide⟩ 3 hp)
        (rowE2 (⟨137, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨92, by decide⟩ : Fin 148))
        (colE1 ⟨92, by decide⟩ 3 (transLenTr ⟨92, by decide⟩ 3 hp))
        (rowE1 (⟨137, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨137, by decide⟩ : Fin 148) ⟨92, by decide⟩ _
      (validAt ⟨137, by decide⟩ (listedAt ⟨137, by decide⟩ hj))
      (colE1 ⟨92, by decide⟩ 3 (transLenTr ⟨92, by decide⟩ 3 hp)) T137_92
      hfix137_92 hinj137_92 hcardT137_92
      (fun i => conj_mem_of_fixedPoints _ _ (T137_92 i) (hfix137_92 i) _)
      ⟨137, by decide⟩ ⟨92, by decide⟩ _
      (Q2.validAt ⟨137, by decide⟩ (Q2.listedAt ⟨137, by decide⟩
        (alnCheck_rep ⟨137, by decide⟩ hj hq).1))
      (colE2 ⟨92, by decide⟩ 3 hp) Q2.T137_92_2 Q2.hfix137_92_2 Q2.hinj137_92_2
      Q2.hcardT137_92_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T137_92_2 i) (Q2.hfix137_92_2 i) _)
      colCert_137_92_3.hD ?_).symm
  rw [alnId_137 j hj]


theorem leaf_137_92_4 (hp : 4 < (Q2.transData.getD 92 []).length)
    (j : Nat) (hj : j < (repChars.getD 137 []).length)
    (hq : (normIsRep.getD 137 []).getD j false = true) :
    species (Q2.reps (⟨92, by decide⟩ : Fin 148)) (colE2 ⟨92, by decide⟩ 4 hp)
        (rowE2 (⟨137, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨92, by decide⟩ : Fin 148))
        (colE1 ⟨92, by decide⟩ 4 (transLenTr ⟨92, by decide⟩ 4 hp))
        (rowE1 (⟨137, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨137, by decide⟩ : Fin 148) ⟨92, by decide⟩ _
      (validAt ⟨137, by decide⟩ (listedAt ⟨137, by decide⟩ hj))
      (colE1 ⟨92, by decide⟩ 4 (transLenTr ⟨92, by decide⟩ 4 hp)) T137_92
      hfix137_92 hinj137_92 hcardT137_92
      (fun i => conj_mem_of_fixedPoints _ _ (T137_92 i) (hfix137_92 i) _)
      ⟨137, by decide⟩ ⟨92, by decide⟩ _
      (Q2.validAt ⟨137, by decide⟩ (Q2.listedAt ⟨137, by decide⟩
        (alnCheck_rep ⟨137, by decide⟩ hj hq).1))
      (colE2 ⟨92, by decide⟩ 4 hp) Q2.T137_92_2 Q2.hfix137_92_2 Q2.hinj137_92_2
      Q2.hcardT137_92_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T137_92_2 i) (Q2.hfix137_92_2 i) _)
      colCert_137_92_4.hD ?_).symm
  rw [alnId_137 j hj]


theorem leaf_137_92_5 (hp : 5 < (Q2.transData.getD 92 []).length)
    (j : Nat) (hj : j < (repChars.getD 137 []).length)
    (hq : (normIsRep.getD 137 []).getD j false = true) :
    species (Q2.reps (⟨92, by decide⟩ : Fin 148)) (colE2 ⟨92, by decide⟩ 5 hp)
        (rowE2 (⟨137, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨92, by decide⟩ : Fin 148))
        (colE1 ⟨92, by decide⟩ 5 (transLenTr ⟨92, by decide⟩ 5 hp))
        (rowE1 (⟨137, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨137, by decide⟩ : Fin 148) ⟨92, by decide⟩ _
      (validAt ⟨137, by decide⟩ (listedAt ⟨137, by decide⟩ hj))
      (colE1 ⟨92, by decide⟩ 5 (transLenTr ⟨92, by decide⟩ 5 hp)) T137_92
      hfix137_92 hinj137_92 hcardT137_92
      (fun i => conj_mem_of_fixedPoints _ _ (T137_92 i) (hfix137_92 i) _)
      ⟨137, by decide⟩ ⟨92, by decide⟩ _
      (Q2.validAt ⟨137, by decide⟩ (Q2.listedAt ⟨137, by decide⟩
        (alnCheck_rep ⟨137, by decide⟩ hj hq).1))
      (colE2 ⟨92, by decide⟩ 5 hp) Q2.T137_92_2 Q2.hfix137_92_2 Q2.hinj137_92_2
      Q2.hcardT137_92_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T137_92_2 i) (Q2.hfix137_92_2 i) _)
      colCert_137_92_5.hD ?_).symm
  rw [alnId_137 j hj]


theorem leaf_137_92_10 (hp : 10 < (Q2.transData.getD 92 []).length)
    (j : Nat) (hj : j < (repChars.getD 137 []).length)
    (hq : (normIsRep.getD 137 []).getD j false = true) :
    species (Q2.reps (⟨92, by decide⟩ : Fin 148)) (colE2 ⟨92, by decide⟩ 10 hp)
        (rowE2 (⟨137, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨92, by decide⟩ : Fin 148))
        (colE1 ⟨92, by decide⟩ 10 (transLenTr ⟨92, by decide⟩ 10 hp))
        (rowE1 (⟨137, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨137, by decide⟩ : Fin 148) ⟨92, by decide⟩ _
      (validAt ⟨137, by decide⟩ (listedAt ⟨137, by decide⟩ hj))
      (colE1 ⟨92, by decide⟩ 10 (transLenTr ⟨92, by decide⟩ 10 hp)) T137_92
      hfix137_92 hinj137_92 hcardT137_92
      (fun i => conj_mem_of_fixedPoints _ _ (T137_92 i) (hfix137_92 i) _)
      ⟨137, by decide⟩ ⟨92, by decide⟩ _
      (Q2.validAt ⟨137, by decide⟩ (Q2.listedAt ⟨137, by decide⟩
        (alnCheck_rep ⟨137, by decide⟩ hj hq).1))
      (colE2 ⟨92, by decide⟩ 10 hp) Q2.T137_92_2 Q2.hfix137_92_2 Q2.hinj137_92_2
      Q2.hcardT137_92_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T137_92_2 i) (Q2.hfix137_92_2 i) _)
      colCert_137_92_10.hD ?_).symm
  rw [alnId_137 j hj]


theorem leaf_137_92_15 (hp : 15 < (Q2.transData.getD 92 []).length)
    (j : Nat) (hj : j < (repChars.getD 137 []).length)
    (hq : (normIsRep.getD 137 []).getD j false = true) :
    species (Q2.reps (⟨92, by decide⟩ : Fin 148)) (colE2 ⟨92, by decide⟩ 15 hp)
        (rowE2 (⟨137, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨92, by decide⟩ : Fin 148))
        (colE1 ⟨92, by decide⟩ 15 (transLenTr ⟨92, by decide⟩ 15 hp))
        (rowE1 (⟨137, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨137, by decide⟩ : Fin 148) ⟨92, by decide⟩ _
      (validAt ⟨137, by decide⟩ (listedAt ⟨137, by decide⟩ hj))
      (colE1 ⟨92, by decide⟩ 15 (transLenTr ⟨92, by decide⟩ 15 hp)) T137_92
      hfix137_92 hinj137_92 hcardT137_92
      (fun i => conj_mem_of_fixedPoints _ _ (T137_92 i) (hfix137_92 i) _)
      ⟨137, by decide⟩ ⟨92, by decide⟩ _
      (Q2.validAt ⟨137, by decide⟩ (Q2.listedAt ⟨137, by decide⟩
        (alnCheck_rep ⟨137, by decide⟩ hj hq).1))
      (colE2 ⟨92, by decide⟩ 15 hp) Q2.T137_92_2 Q2.hfix137_92_2 Q2.hinj137_92_2
      Q2.hcardT137_92_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T137_92_2 i) (Q2.hfix137_92_2 i) _)
      ?_).symm
  rw [show colData1 (⟨137, by decide⟩ : Fin 148)
        ((colE1 ⟨92, by decide⟩ 15 (transLenTr ⟨92, by decide⟩ 15 hp) : ↥(reps ⟨92, by decide⟩)) : Coordinate 1)
        T137_92 = colFn colCertDiv_137_92_15.D1 (m := 5) from colCertDiv_137_92_15.bind1,
    show colData2 (⟨137, by decide⟩ : Fin 148)
        ((colE2 ⟨92, by decide⟩ 15 hp : ↥(Q2.reps ⟨92, by decide⟩)) : Coordinate 2)
        Q2.T137_92_2 = colFn colCertDiv_137_92_15.D2 (m := 5) from colCertDiv_137_92_15.bind2]
  rw [alnId_137 j hj]
  exact fastcode_of_div ⟨137, by decide⟩ _ _ _
    ((alnId_137 j hj) ▸ Q2.listedAt (⟨137, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨137, by decide⟩ : Fin 148) hj hq).1) colCertDiv_137_92_15_match


theorem leaf_137_92_20 (hp : 20 < (Q2.transData.getD 92 []).length)
    (j : Nat) (hj : j < (repChars.getD 137 []).length)
    (hq : (normIsRep.getD 137 []).getD j false = true) :
    species (Q2.reps (⟨92, by decide⟩ : Fin 148)) (colE2 ⟨92, by decide⟩ 20 hp)
        (rowE2 (⟨137, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨92, by decide⟩ : Fin 148))
        (colE1 ⟨92, by decide⟩ 20 (transLenTr ⟨92, by decide⟩ 20 hp))
        (rowE1 (⟨137, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨137, by decide⟩ : Fin 148) ⟨92, by decide⟩ _
      (validAt ⟨137, by decide⟩ (listedAt ⟨137, by decide⟩ hj))
      (colE1 ⟨92, by decide⟩ 20 (transLenTr ⟨92, by decide⟩ 20 hp)) T137_92
      hfix137_92 hinj137_92 hcardT137_92
      (fun i => conj_mem_of_fixedPoints _ _ (T137_92 i) (hfix137_92 i) _)
      ⟨137, by decide⟩ ⟨92, by decide⟩ _
      (Q2.validAt ⟨137, by decide⟩ (Q2.listedAt ⟨137, by decide⟩
        (alnCheck_rep ⟨137, by decide⟩ hj hq).1))
      (colE2 ⟨92, by decide⟩ 20 hp) Q2.T137_92_2 Q2.hfix137_92_2 Q2.hinj137_92_2
      Q2.hcardT137_92_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T137_92_2 i) (Q2.hfix137_92_2 i) _)
      ?_).symm
  rw [show colData1 (⟨137, by decide⟩ : Fin 148)
        ((colE1 ⟨92, by decide⟩ 20 (transLenTr ⟨92, by decide⟩ 20 hp) : ↥(reps ⟨92, by decide⟩)) : Coordinate 1)
        T137_92 = colFn colCertDiv_137_92_20.D1 (m := 5) from colCertDiv_137_92_20.bind1,
    show colData2 (⟨137, by decide⟩ : Fin 148)
        ((colE2 ⟨92, by decide⟩ 20 hp : ↥(Q2.reps ⟨92, by decide⟩)) : Coordinate 2)
        Q2.T137_92_2 = colFn colCertDiv_137_92_20.D2 (m := 5) from colCertDiv_137_92_20.bind2]
  rw [alnId_137 j hj]
  exact fastcode_of_div ⟨137, by decide⟩ _ _ _
    ((alnId_137 j hj) ▸ Q2.listedAt (⟨137, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨137, by decide⟩ : Fin 148) hj hq).1) colCertDiv_137_92_20_match


theorem leaf_137_99_0 (hp : 0 < (Q2.transData.getD 99 []).length)
    (j : Nat) (hj : j < (repChars.getD 137 []).length)
    (hq : (normIsRep.getD 137 []).getD j false = true) :
    species (Q2.reps (⟨99, by decide⟩ : Fin 148)) (colE2 ⟨99, by decide⟩ 0 hp)
        (rowE2 (⟨137, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨99, by decide⟩ : Fin 148))
        (colE1 ⟨99, by decide⟩ 0 (transLenTr ⟨99, by decide⟩ 0 hp))
        (rowE1 (⟨137, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨137, by decide⟩ : Fin 148) ⟨99, by decide⟩ _
      (validAt ⟨137, by decide⟩ (listedAt ⟨137, by decide⟩ hj))
      (colE1 ⟨99, by decide⟩ 0 (transLenTr ⟨99, by decide⟩ 0 hp)) T137_99
      hfix137_99 hinj137_99 hcardT137_99
      (fun i => conj_mem_of_fixedPoints _ _ (T137_99 i) (hfix137_99 i) _)
      ⟨137, by decide⟩ ⟨99, by decide⟩ _
      (Q2.validAt ⟨137, by decide⟩ (Q2.listedAt ⟨137, by decide⟩
        (alnCheck_rep ⟨137, by decide⟩ hj hq).1))
      (colE2 ⟨99, by decide⟩ 0 hp) Q2.T137_99_2 Q2.hfix137_99_2 Q2.hinj137_99_2
      Q2.hcardT137_99_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T137_99_2 i) (Q2.hfix137_99_2 i) _)
      colCert_137_99_0.hD ?_).symm
  rw [alnId_137 j hj]


theorem leaf_137_99_1 (hp : 1 < (Q2.transData.getD 99 []).length)
    (j : Nat) (hj : j < (repChars.getD 137 []).length)
    (hq : (normIsRep.getD 137 []).getD j false = true) :
    species (Q2.reps (⟨99, by decide⟩ : Fin 148)) (colE2 ⟨99, by decide⟩ 1 hp)
        (rowE2 (⟨137, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨99, by decide⟩ : Fin 148))
        (colE1 ⟨99, by decide⟩ 1 (transLenTr ⟨99, by decide⟩ 1 hp))
        (rowE1 (⟨137, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨137, by decide⟩ : Fin 148) ⟨99, by decide⟩ _
      (validAt ⟨137, by decide⟩ (listedAt ⟨137, by decide⟩ hj))
      (colE1 ⟨99, by decide⟩ 1 (transLenTr ⟨99, by decide⟩ 1 hp)) T137_99
      hfix137_99 hinj137_99 hcardT137_99
      (fun i => conj_mem_of_fixedPoints _ _ (T137_99 i) (hfix137_99 i) _)
      ⟨137, by decide⟩ ⟨99, by decide⟩ _
      (Q2.validAt ⟨137, by decide⟩ (Q2.listedAt ⟨137, by decide⟩
        (alnCheck_rep ⟨137, by decide⟩ hj hq).1))
      (colE2 ⟨99, by decide⟩ 1 hp) Q2.T137_99_2 Q2.hfix137_99_2 Q2.hinj137_99_2
      Q2.hcardT137_99_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T137_99_2 i) (Q2.hfix137_99_2 i) _)
      colCert_137_99_1.hD ?_).symm
  rw [alnId_137 j hj]


theorem leaf_137_99_2 (hp : 2 < (Q2.transData.getD 99 []).length)
    (j : Nat) (hj : j < (repChars.getD 137 []).length)
    (hq : (normIsRep.getD 137 []).getD j false = true) :
    species (Q2.reps (⟨99, by decide⟩ : Fin 148)) (colE2 ⟨99, by decide⟩ 2 hp)
        (rowE2 (⟨137, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨99, by decide⟩ : Fin 148))
        (colE1 ⟨99, by decide⟩ 2 (transLenTr ⟨99, by decide⟩ 2 hp))
        (rowE1 (⟨137, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨137, by decide⟩ : Fin 148) ⟨99, by decide⟩ _
      (validAt ⟨137, by decide⟩ (listedAt ⟨137, by decide⟩ hj))
      (colE1 ⟨99, by decide⟩ 2 (transLenTr ⟨99, by decide⟩ 2 hp)) T137_99
      hfix137_99 hinj137_99 hcardT137_99
      (fun i => conj_mem_of_fixedPoints _ _ (T137_99 i) (hfix137_99 i) _)
      ⟨137, by decide⟩ ⟨99, by decide⟩ _
      (Q2.validAt ⟨137, by decide⟩ (Q2.listedAt ⟨137, by decide⟩
        (alnCheck_rep ⟨137, by decide⟩ hj hq).1))
      (colE2 ⟨99, by decide⟩ 2 hp) Q2.T137_99_2 Q2.hfix137_99_2 Q2.hinj137_99_2
      Q2.hcardT137_99_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T137_99_2 i) (Q2.hfix137_99_2 i) _)
      colCert_137_99_2.hD ?_).symm
  rw [alnId_137 j hj]


theorem leaf_137_99_3 (hp : 3 < (Q2.transData.getD 99 []).length)
    (j : Nat) (hj : j < (repChars.getD 137 []).length)
    (hq : (normIsRep.getD 137 []).getD j false = true) :
    species (Q2.reps (⟨99, by decide⟩ : Fin 148)) (colE2 ⟨99, by decide⟩ 3 hp)
        (rowE2 (⟨137, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨99, by decide⟩ : Fin 148))
        (colE1 ⟨99, by decide⟩ 3 (transLenTr ⟨99, by decide⟩ 3 hp))
        (rowE1 (⟨137, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨137, by decide⟩ : Fin 148) ⟨99, by decide⟩ _
      (validAt ⟨137, by decide⟩ (listedAt ⟨137, by decide⟩ hj))
      (colE1 ⟨99, by decide⟩ 3 (transLenTr ⟨99, by decide⟩ 3 hp)) T137_99
      hfix137_99 hinj137_99 hcardT137_99
      (fun i => conj_mem_of_fixedPoints _ _ (T137_99 i) (hfix137_99 i) _)
      ⟨137, by decide⟩ ⟨99, by decide⟩ _
      (Q2.validAt ⟨137, by decide⟩ (Q2.listedAt ⟨137, by decide⟩
        (alnCheck_rep ⟨137, by decide⟩ hj hq).1))
      (colE2 ⟨99, by decide⟩ 3 hp) Q2.T137_99_2 Q2.hfix137_99_2 Q2.hinj137_99_2
      Q2.hcardT137_99_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T137_99_2 i) (Q2.hfix137_99_2 i) _)
      colCert_137_99_3.hD ?_).symm
  rw [alnId_137 j hj]


theorem leaf_137_99_4 (hp : 4 < (Q2.transData.getD 99 []).length)
    (j : Nat) (hj : j < (repChars.getD 137 []).length)
    (hq : (normIsRep.getD 137 []).getD j false = true) :
    species (Q2.reps (⟨99, by decide⟩ : Fin 148)) (colE2 ⟨99, by decide⟩ 4 hp)
        (rowE2 (⟨137, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨99, by decide⟩ : Fin 148))
        (colE1 ⟨99, by decide⟩ 4 (transLenTr ⟨99, by decide⟩ 4 hp))
        (rowE1 (⟨137, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨137, by decide⟩ : Fin 148) ⟨99, by decide⟩ _
      (validAt ⟨137, by decide⟩ (listedAt ⟨137, by decide⟩ hj))
      (colE1 ⟨99, by decide⟩ 4 (transLenTr ⟨99, by decide⟩ 4 hp)) T137_99
      hfix137_99 hinj137_99 hcardT137_99
      (fun i => conj_mem_of_fixedPoints _ _ (T137_99 i) (hfix137_99 i) _)
      ⟨137, by decide⟩ ⟨99, by decide⟩ _
      (Q2.validAt ⟨137, by decide⟩ (Q2.listedAt ⟨137, by decide⟩
        (alnCheck_rep ⟨137, by decide⟩ hj hq).1))
      (colE2 ⟨99, by decide⟩ 4 hp) Q2.T137_99_2 Q2.hfix137_99_2 Q2.hinj137_99_2
      Q2.hcardT137_99_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T137_99_2 i) (Q2.hfix137_99_2 i) _)
      colCert_137_99_4.hD ?_).symm
  rw [alnId_137 j hj]


theorem leaf_137_99_5 (hp : 5 < (Q2.transData.getD 99 []).length)
    (j : Nat) (hj : j < (repChars.getD 137 []).length)
    (hq : (normIsRep.getD 137 []).getD j false = true) :
    species (Q2.reps (⟨99, by decide⟩ : Fin 148)) (colE2 ⟨99, by decide⟩ 5 hp)
        (rowE2 (⟨137, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨99, by decide⟩ : Fin 148))
        (colE1 ⟨99, by decide⟩ 5 (transLenTr ⟨99, by decide⟩ 5 hp))
        (rowE1 (⟨137, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨137, by decide⟩ : Fin 148) ⟨99, by decide⟩ _
      (validAt ⟨137, by decide⟩ (listedAt ⟨137, by decide⟩ hj))
      (colE1 ⟨99, by decide⟩ 5 (transLenTr ⟨99, by decide⟩ 5 hp)) T137_99
      hfix137_99 hinj137_99 hcardT137_99
      (fun i => conj_mem_of_fixedPoints _ _ (T137_99 i) (hfix137_99 i) _)
      ⟨137, by decide⟩ ⟨99, by decide⟩ _
      (Q2.validAt ⟨137, by decide⟩ (Q2.listedAt ⟨137, by decide⟩
        (alnCheck_rep ⟨137, by decide⟩ hj hq).1))
      (colE2 ⟨99, by decide⟩ 5 hp) Q2.T137_99_2 Q2.hfix137_99_2 Q2.hinj137_99_2
      Q2.hcardT137_99_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T137_99_2 i) (Q2.hfix137_99_2 i) _)
      colCert_137_99_5.hD ?_).symm
  rw [alnId_137 j hj]


theorem leaf_137_99_10 (hp : 10 < (Q2.transData.getD 99 []).length)
    (j : Nat) (hj : j < (repChars.getD 137 []).length)
    (hq : (normIsRep.getD 137 []).getD j false = true) :
    species (Q2.reps (⟨99, by decide⟩ : Fin 148)) (colE2 ⟨99, by decide⟩ 10 hp)
        (rowE2 (⟨137, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨99, by decide⟩ : Fin 148))
        (colE1 ⟨99, by decide⟩ 10 (transLenTr ⟨99, by decide⟩ 10 hp))
        (rowE1 (⟨137, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨137, by decide⟩ : Fin 148) ⟨99, by decide⟩ _
      (validAt ⟨137, by decide⟩ (listedAt ⟨137, by decide⟩ hj))
      (colE1 ⟨99, by decide⟩ 10 (transLenTr ⟨99, by decide⟩ 10 hp)) T137_99
      hfix137_99 hinj137_99 hcardT137_99
      (fun i => conj_mem_of_fixedPoints _ _ (T137_99 i) (hfix137_99 i) _)
      ⟨137, by decide⟩ ⟨99, by decide⟩ _
      (Q2.validAt ⟨137, by decide⟩ (Q2.listedAt ⟨137, by decide⟩
        (alnCheck_rep ⟨137, by decide⟩ hj hq).1))
      (colE2 ⟨99, by decide⟩ 10 hp) Q2.T137_99_2 Q2.hfix137_99_2 Q2.hinj137_99_2
      Q2.hcardT137_99_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T137_99_2 i) (Q2.hfix137_99_2 i) _)
      colCert_137_99_10.hD ?_).symm
  rw [alnId_137 j hj]


theorem leaf_137_99_15 (hp : 15 < (Q2.transData.getD 99 []).length)
    (j : Nat) (hj : j < (repChars.getD 137 []).length)
    (hq : (normIsRep.getD 137 []).getD j false = true) :
    species (Q2.reps (⟨99, by decide⟩ : Fin 148)) (colE2 ⟨99, by decide⟩ 15 hp)
        (rowE2 (⟨137, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨99, by decide⟩ : Fin 148))
        (colE1 ⟨99, by decide⟩ 15 (transLenTr ⟨99, by decide⟩ 15 hp))
        (rowE1 (⟨137, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨137, by decide⟩ : Fin 148) ⟨99, by decide⟩ _
      (validAt ⟨137, by decide⟩ (listedAt ⟨137, by decide⟩ hj))
      (colE1 ⟨99, by decide⟩ 15 (transLenTr ⟨99, by decide⟩ 15 hp)) T137_99
      hfix137_99 hinj137_99 hcardT137_99
      (fun i => conj_mem_of_fixedPoints _ _ (T137_99 i) (hfix137_99 i) _)
      ⟨137, by decide⟩ ⟨99, by decide⟩ _
      (Q2.validAt ⟨137, by decide⟩ (Q2.listedAt ⟨137, by decide⟩
        (alnCheck_rep ⟨137, by decide⟩ hj hq).1))
      (colE2 ⟨99, by decide⟩ 15 hp) Q2.T137_99_2 Q2.hfix137_99_2 Q2.hinj137_99_2
      Q2.hcardT137_99_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T137_99_2 i) (Q2.hfix137_99_2 i) _)
      colCert_137_99_15.hD ?_).symm
  rw [alnId_137 j hj]


theorem leaf_137_99_20 (hp : 20 < (Q2.transData.getD 99 []).length)
    (j : Nat) (hj : j < (repChars.getD 137 []).length)
    (hq : (normIsRep.getD 137 []).getD j false = true) :
    species (Q2.reps (⟨99, by decide⟩ : Fin 148)) (colE2 ⟨99, by decide⟩ 20 hp)
        (rowE2 (⟨137, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨99, by decide⟩ : Fin 148))
        (colE1 ⟨99, by decide⟩ 20 (transLenTr ⟨99, by decide⟩ 20 hp))
        (rowE1 (⟨137, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨137, by decide⟩ : Fin 148) ⟨99, by decide⟩ _
      (validAt ⟨137, by decide⟩ (listedAt ⟨137, by decide⟩ hj))
      (colE1 ⟨99, by decide⟩ 20 (transLenTr ⟨99, by decide⟩ 20 hp)) T137_99
      hfix137_99 hinj137_99 hcardT137_99
      (fun i => conj_mem_of_fixedPoints _ _ (T137_99 i) (hfix137_99 i) _)
      ⟨137, by decide⟩ ⟨99, by decide⟩ _
      (Q2.validAt ⟨137, by decide⟩ (Q2.listedAt ⟨137, by decide⟩
        (alnCheck_rep ⟨137, by decide⟩ hj hq).1))
      (colE2 ⟨99, by decide⟩ 20 hp) Q2.T137_99_2 Q2.hfix137_99_2 Q2.hinj137_99_2
      Q2.hcardT137_99_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T137_99_2 i) (Q2.hfix137_99_2 i) _)
      colCert_137_99_20.hD ?_).symm
  rw [alnId_137 j hj]


theorem leaf_137_103_0 (hp : 0 < (Q2.transData.getD 103 []).length)
    (j : Nat) (hj : j < (repChars.getD 137 []).length)
    (hq : (normIsRep.getD 137 []).getD j false = true) :
    species (Q2.reps (⟨103, by decide⟩ : Fin 148)) (colE2 ⟨103, by decide⟩ 0 hp)
        (rowE2 (⟨137, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨103, by decide⟩ : Fin 148))
        (colE1 ⟨103, by decide⟩ 0 (transLenTr ⟨103, by decide⟩ 0 hp))
        (rowE1 (⟨137, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨137, by decide⟩ : Fin 148) ⟨103, by decide⟩ _
      (validAt ⟨137, by decide⟩ (listedAt ⟨137, by decide⟩ hj))
      (colE1 ⟨103, by decide⟩ 0 (transLenTr ⟨103, by decide⟩ 0 hp)) T137_103
      hfix137_103 hinj137_103 hcardT137_103
      (fun i => conj_mem_of_fixedPoints _ _ (T137_103 i) (hfix137_103 i) _)
      ⟨137, by decide⟩ ⟨103, by decide⟩ _
      (Q2.validAt ⟨137, by decide⟩ (Q2.listedAt ⟨137, by decide⟩
        (alnCheck_rep ⟨137, by decide⟩ hj hq).1))
      (colE2 ⟨103, by decide⟩ 0 hp) Q2.T137_103_2 Q2.hfix137_103_2 Q2.hinj137_103_2
      Q2.hcardT137_103_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T137_103_2 i) (Q2.hfix137_103_2 i) _)
      colCert_137_103_0.hD ?_).symm
  rw [alnId_137 j hj]


theorem leaf_137_103_1 (hp : 1 < (Q2.transData.getD 103 []).length)
    (j : Nat) (hj : j < (repChars.getD 137 []).length)
    (hq : (normIsRep.getD 137 []).getD j false = true) :
    species (Q2.reps (⟨103, by decide⟩ : Fin 148)) (colE2 ⟨103, by decide⟩ 1 hp)
        (rowE2 (⟨137, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨103, by decide⟩ : Fin 148))
        (colE1 ⟨103, by decide⟩ 1 (transLenTr ⟨103, by decide⟩ 1 hp))
        (rowE1 (⟨137, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨137, by decide⟩ : Fin 148) ⟨103, by decide⟩ _
      (validAt ⟨137, by decide⟩ (listedAt ⟨137, by decide⟩ hj))
      (colE1 ⟨103, by decide⟩ 1 (transLenTr ⟨103, by decide⟩ 1 hp)) T137_103
      hfix137_103 hinj137_103 hcardT137_103
      (fun i => conj_mem_of_fixedPoints _ _ (T137_103 i) (hfix137_103 i) _)
      ⟨137, by decide⟩ ⟨103, by decide⟩ _
      (Q2.validAt ⟨137, by decide⟩ (Q2.listedAt ⟨137, by decide⟩
        (alnCheck_rep ⟨137, by decide⟩ hj hq).1))
      (colE2 ⟨103, by decide⟩ 1 hp) Q2.T137_103_2 Q2.hfix137_103_2 Q2.hinj137_103_2
      Q2.hcardT137_103_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T137_103_2 i) (Q2.hfix137_103_2 i) _)
      colCert_137_103_1.hD ?_).symm
  rw [alnId_137 j hj]


theorem leaf_137_103_2 (hp : 2 < (Q2.transData.getD 103 []).length)
    (j : Nat) (hj : j < (repChars.getD 137 []).length)
    (hq : (normIsRep.getD 137 []).getD j false = true) :
    species (Q2.reps (⟨103, by decide⟩ : Fin 148)) (colE2 ⟨103, by decide⟩ 2 hp)
        (rowE2 (⟨137, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨103, by decide⟩ : Fin 148))
        (colE1 ⟨103, by decide⟩ 2 (transLenTr ⟨103, by decide⟩ 2 hp))
        (rowE1 (⟨137, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨137, by decide⟩ : Fin 148) ⟨103, by decide⟩ _
      (validAt ⟨137, by decide⟩ (listedAt ⟨137, by decide⟩ hj))
      (colE1 ⟨103, by decide⟩ 2 (transLenTr ⟨103, by decide⟩ 2 hp)) T137_103
      hfix137_103 hinj137_103 hcardT137_103
      (fun i => conj_mem_of_fixedPoints _ _ (T137_103 i) (hfix137_103 i) _)
      ⟨137, by decide⟩ ⟨103, by decide⟩ _
      (Q2.validAt ⟨137, by decide⟩ (Q2.listedAt ⟨137, by decide⟩
        (alnCheck_rep ⟨137, by decide⟩ hj hq).1))
      (colE2 ⟨103, by decide⟩ 2 hp) Q2.T137_103_2 Q2.hfix137_103_2 Q2.hinj137_103_2
      Q2.hcardT137_103_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T137_103_2 i) (Q2.hfix137_103_2 i) _)
      colCert_137_103_2.hD ?_).symm
  rw [alnId_137 j hj]


theorem leaf_137_103_3 (hp : 3 < (Q2.transData.getD 103 []).length)
    (j : Nat) (hj : j < (repChars.getD 137 []).length)
    (hq : (normIsRep.getD 137 []).getD j false = true) :
    species (Q2.reps (⟨103, by decide⟩ : Fin 148)) (colE2 ⟨103, by decide⟩ 3 hp)
        (rowE2 (⟨137, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨103, by decide⟩ : Fin 148))
        (colE1 ⟨103, by decide⟩ 3 (transLenTr ⟨103, by decide⟩ 3 hp))
        (rowE1 (⟨137, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨137, by decide⟩ : Fin 148) ⟨103, by decide⟩ _
      (validAt ⟨137, by decide⟩ (listedAt ⟨137, by decide⟩ hj))
      (colE1 ⟨103, by decide⟩ 3 (transLenTr ⟨103, by decide⟩ 3 hp)) T137_103
      hfix137_103 hinj137_103 hcardT137_103
      (fun i => conj_mem_of_fixedPoints _ _ (T137_103 i) (hfix137_103 i) _)
      ⟨137, by decide⟩ ⟨103, by decide⟩ _
      (Q2.validAt ⟨137, by decide⟩ (Q2.listedAt ⟨137, by decide⟩
        (alnCheck_rep ⟨137, by decide⟩ hj hq).1))
      (colE2 ⟨103, by decide⟩ 3 hp) Q2.T137_103_2 Q2.hfix137_103_2 Q2.hinj137_103_2
      Q2.hcardT137_103_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T137_103_2 i) (Q2.hfix137_103_2 i) _)
      colCert_137_103_3.hD ?_).symm
  rw [alnId_137 j hj]


theorem leaf_137_103_4 (hp : 4 < (Q2.transData.getD 103 []).length)
    (j : Nat) (hj : j < (repChars.getD 137 []).length)
    (hq : (normIsRep.getD 137 []).getD j false = true) :
    species (Q2.reps (⟨103, by decide⟩ : Fin 148)) (colE2 ⟨103, by decide⟩ 4 hp)
        (rowE2 (⟨137, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨103, by decide⟩ : Fin 148))
        (colE1 ⟨103, by decide⟩ 4 (transLenTr ⟨103, by decide⟩ 4 hp))
        (rowE1 (⟨137, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨137, by decide⟩ : Fin 148) ⟨103, by decide⟩ _
      (validAt ⟨137, by decide⟩ (listedAt ⟨137, by decide⟩ hj))
      (colE1 ⟨103, by decide⟩ 4 (transLenTr ⟨103, by decide⟩ 4 hp)) T137_103
      hfix137_103 hinj137_103 hcardT137_103
      (fun i => conj_mem_of_fixedPoints _ _ (T137_103 i) (hfix137_103 i) _)
      ⟨137, by decide⟩ ⟨103, by decide⟩ _
      (Q2.validAt ⟨137, by decide⟩ (Q2.listedAt ⟨137, by decide⟩
        (alnCheck_rep ⟨137, by decide⟩ hj hq).1))
      (colE2 ⟨103, by decide⟩ 4 hp) Q2.T137_103_2 Q2.hfix137_103_2 Q2.hinj137_103_2
      Q2.hcardT137_103_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T137_103_2 i) (Q2.hfix137_103_2 i) _)
      colCert_137_103_4.hD ?_).symm
  rw [alnId_137 j hj]


theorem leaf_137_103_5 (hp : 5 < (Q2.transData.getD 103 []).length)
    (j : Nat) (hj : j < (repChars.getD 137 []).length)
    (hq : (normIsRep.getD 137 []).getD j false = true) :
    species (Q2.reps (⟨103, by decide⟩ : Fin 148)) (colE2 ⟨103, by decide⟩ 5 hp)
        (rowE2 (⟨137, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨103, by decide⟩ : Fin 148))
        (colE1 ⟨103, by decide⟩ 5 (transLenTr ⟨103, by decide⟩ 5 hp))
        (rowE1 (⟨137, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨137, by decide⟩ : Fin 148) ⟨103, by decide⟩ _
      (validAt ⟨137, by decide⟩ (listedAt ⟨137, by decide⟩ hj))
      (colE1 ⟨103, by decide⟩ 5 (transLenTr ⟨103, by decide⟩ 5 hp)) T137_103
      hfix137_103 hinj137_103 hcardT137_103
      (fun i => conj_mem_of_fixedPoints _ _ (T137_103 i) (hfix137_103 i) _)
      ⟨137, by decide⟩ ⟨103, by decide⟩ _
      (Q2.validAt ⟨137, by decide⟩ (Q2.listedAt ⟨137, by decide⟩
        (alnCheck_rep ⟨137, by decide⟩ hj hq).1))
      (colE2 ⟨103, by decide⟩ 5 hp) Q2.T137_103_2 Q2.hfix137_103_2 Q2.hinj137_103_2
      Q2.hcardT137_103_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T137_103_2 i) (Q2.hfix137_103_2 i) _)
      colCert_137_103_5.hD ?_).symm
  rw [alnId_137 j hj]


theorem leaf_137_103_10 (hp : 10 < (Q2.transData.getD 103 []).length)
    (j : Nat) (hj : j < (repChars.getD 137 []).length)
    (hq : (normIsRep.getD 137 []).getD j false = true) :
    species (Q2.reps (⟨103, by decide⟩ : Fin 148)) (colE2 ⟨103, by decide⟩ 10 hp)
        (rowE2 (⟨137, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨103, by decide⟩ : Fin 148))
        (colE1 ⟨103, by decide⟩ 10 (transLenTr ⟨103, by decide⟩ 10 hp))
        (rowE1 (⟨137, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨137, by decide⟩ : Fin 148) ⟨103, by decide⟩ _
      (validAt ⟨137, by decide⟩ (listedAt ⟨137, by decide⟩ hj))
      (colE1 ⟨103, by decide⟩ 10 (transLenTr ⟨103, by decide⟩ 10 hp)) T137_103
      hfix137_103 hinj137_103 hcardT137_103
      (fun i => conj_mem_of_fixedPoints _ _ (T137_103 i) (hfix137_103 i) _)
      ⟨137, by decide⟩ ⟨103, by decide⟩ _
      (Q2.validAt ⟨137, by decide⟩ (Q2.listedAt ⟨137, by decide⟩
        (alnCheck_rep ⟨137, by decide⟩ hj hq).1))
      (colE2 ⟨103, by decide⟩ 10 hp) Q2.T137_103_2 Q2.hfix137_103_2 Q2.hinj137_103_2
      Q2.hcardT137_103_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T137_103_2 i) (Q2.hfix137_103_2 i) _)
      ?_).symm
  rw [show colData1 (⟨137, by decide⟩ : Fin 148)
        ((colE1 ⟨103, by decide⟩ 10 (transLenTr ⟨103, by decide⟩ 10 hp) : ↥(reps ⟨103, by decide⟩)) : Coordinate 1)
        T137_103 = colFn colCertDiv_137_103_10.D1 (m := 5) from colCertDiv_137_103_10.bind1,
    show colData2 (⟨137, by decide⟩ : Fin 148)
        ((colE2 ⟨103, by decide⟩ 10 hp : ↥(Q2.reps ⟨103, by decide⟩)) : Coordinate 2)
        Q2.T137_103_2 = colFn colCertDiv_137_103_10.D2 (m := 5) from colCertDiv_137_103_10.bind2]
  rw [alnId_137 j hj]
  exact fastcode_of_div ⟨137, by decide⟩ _ _ _
    ((alnId_137 j hj) ▸ Q2.listedAt (⟨137, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨137, by decide⟩ : Fin 148) hj hq).1) colCertDiv_137_103_10_match


theorem leaf_137_103_15 (hp : 15 < (Q2.transData.getD 103 []).length)
    (j : Nat) (hj : j < (repChars.getD 137 []).length)
    (hq : (normIsRep.getD 137 []).getD j false = true) :
    species (Q2.reps (⟨103, by decide⟩ : Fin 148)) (colE2 ⟨103, by decide⟩ 15 hp)
        (rowE2 (⟨137, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨103, by decide⟩ : Fin 148))
        (colE1 ⟨103, by decide⟩ 15 (transLenTr ⟨103, by decide⟩ 15 hp))
        (rowE1 (⟨137, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨137, by decide⟩ : Fin 148) ⟨103, by decide⟩ _
      (validAt ⟨137, by decide⟩ (listedAt ⟨137, by decide⟩ hj))
      (colE1 ⟨103, by decide⟩ 15 (transLenTr ⟨103, by decide⟩ 15 hp)) T137_103
      hfix137_103 hinj137_103 hcardT137_103
      (fun i => conj_mem_of_fixedPoints _ _ (T137_103 i) (hfix137_103 i) _)
      ⟨137, by decide⟩ ⟨103, by decide⟩ _
      (Q2.validAt ⟨137, by decide⟩ (Q2.listedAt ⟨137, by decide⟩
        (alnCheck_rep ⟨137, by decide⟩ hj hq).1))
      (colE2 ⟨103, by decide⟩ 15 hp) Q2.T137_103_2 Q2.hfix137_103_2 Q2.hinj137_103_2
      Q2.hcardT137_103_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T137_103_2 i) (Q2.hfix137_103_2 i) _)
      ?_).symm
  rw [show colData1 (⟨137, by decide⟩ : Fin 148)
        ((colE1 ⟨103, by decide⟩ 15 (transLenTr ⟨103, by decide⟩ 15 hp) : ↥(reps ⟨103, by decide⟩)) : Coordinate 1)
        T137_103 = colFn colCertDiv_137_103_15.D1 (m := 5) from colCertDiv_137_103_15.bind1,
    show colData2 (⟨137, by decide⟩ : Fin 148)
        ((colE2 ⟨103, by decide⟩ 15 hp : ↥(Q2.reps ⟨103, by decide⟩)) : Coordinate 2)
        Q2.T137_103_2 = colFn colCertDiv_137_103_15.D2 (m := 5) from colCertDiv_137_103_15.bind2]
  rw [alnId_137 j hj]
  exact fastcode_of_div ⟨137, by decide⟩ _ _ _
    ((alnId_137 j hj) ▸ Q2.listedAt (⟨137, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨137, by decide⟩ : Fin 148) hj hq).1) colCertDiv_137_103_15_match


theorem leaf_137_103_20 (hp : 20 < (Q2.transData.getD 103 []).length)
    (j : Nat) (hj : j < (repChars.getD 137 []).length)
    (hq : (normIsRep.getD 137 []).getD j false = true) :
    species (Q2.reps (⟨103, by decide⟩ : Fin 148)) (colE2 ⟨103, by decide⟩ 20 hp)
        (rowE2 (⟨137, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨103, by decide⟩ : Fin 148))
        (colE1 ⟨103, by decide⟩ 20 (transLenTr ⟨103, by decide⟩ 20 hp))
        (rowE1 (⟨137, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨137, by decide⟩ : Fin 148) ⟨103, by decide⟩ _
      (validAt ⟨137, by decide⟩ (listedAt ⟨137, by decide⟩ hj))
      (colE1 ⟨103, by decide⟩ 20 (transLenTr ⟨103, by decide⟩ 20 hp)) T137_103
      hfix137_103 hinj137_103 hcardT137_103
      (fun i => conj_mem_of_fixedPoints _ _ (T137_103 i) (hfix137_103 i) _)
      ⟨137, by decide⟩ ⟨103, by decide⟩ _
      (Q2.validAt ⟨137, by decide⟩ (Q2.listedAt ⟨137, by decide⟩
        (alnCheck_rep ⟨137, by decide⟩ hj hq).1))
      (colE2 ⟨103, by decide⟩ 20 hp) Q2.T137_103_2 Q2.hfix137_103_2 Q2.hinj137_103_2
      Q2.hcardT137_103_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T137_103_2 i) (Q2.hfix137_103_2 i) _)
      ?_).symm
  rw [show colData1 (⟨137, by decide⟩ : Fin 148)
        ((colE1 ⟨103, by decide⟩ 20 (transLenTr ⟨103, by decide⟩ 20 hp) : ↥(reps ⟨103, by decide⟩)) : Coordinate 1)
        T137_103 = colFn colCertDiv_137_103_20.D1 (m := 5) from colCertDiv_137_103_20.bind1,
    show colData2 (⟨137, by decide⟩ : Fin 148)
        ((colE2 ⟨103, by decide⟩ 20 hp : ↥(Q2.reps ⟨103, by decide⟩)) : Coordinate 2)
        Q2.T137_103_2 = colFn colCertDiv_137_103_20.D2 (m := 5) from colCertDiv_137_103_20.bind2]
  rw [alnId_137 j hj]
  exact fastcode_of_div ⟨137, by decide⟩ _ _ _
    ((alnId_137 j hj) ▸ Q2.listedAt (⟨137, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨137, by decide⟩ : Fin 148) hj hq).1) colCertDiv_137_103_20_match


theorem leaf_137_105_0 (hp : 0 < (Q2.transData.getD 105 []).length)
    (j : Nat) (hj : j < (repChars.getD 137 []).length)
    (hq : (normIsRep.getD 137 []).getD j false = true) :
    species (Q2.reps (⟨105, by decide⟩ : Fin 148)) (colE2 ⟨105, by decide⟩ 0 hp)
        (rowE2 (⟨137, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨105, by decide⟩ : Fin 148))
        (colE1 ⟨105, by decide⟩ 0 (transLenTr ⟨105, by decide⟩ 0 hp))
        (rowE1 (⟨137, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨137, by decide⟩ : Fin 148) ⟨105, by decide⟩ _
      (validAt ⟨137, by decide⟩ (listedAt ⟨137, by decide⟩ hj))
      (colE1 ⟨105, by decide⟩ 0 (transLenTr ⟨105, by decide⟩ 0 hp)) T137_105
      hfix137_105 hinj137_105 hcardT137_105
      (fun i => conj_mem_of_fixedPoints _ _ (T137_105 i) (hfix137_105 i) _)
      ⟨137, by decide⟩ ⟨105, by decide⟩ _
      (Q2.validAt ⟨137, by decide⟩ (Q2.listedAt ⟨137, by decide⟩
        (alnCheck_rep ⟨137, by decide⟩ hj hq).1))
      (colE2 ⟨105, by decide⟩ 0 hp) Q2.T137_105_2 Q2.hfix137_105_2 Q2.hinj137_105_2
      Q2.hcardT137_105_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T137_105_2 i) (Q2.hfix137_105_2 i) _)
      colCert_137_105_0.hD ?_).symm
  rw [alnId_137 j hj]


theorem leaf_137_105_1 (hp : 1 < (Q2.transData.getD 105 []).length)
    (j : Nat) (hj : j < (repChars.getD 137 []).length)
    (hq : (normIsRep.getD 137 []).getD j false = true) :
    species (Q2.reps (⟨105, by decide⟩ : Fin 148)) (colE2 ⟨105, by decide⟩ 1 hp)
        (rowE2 (⟨137, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨105, by decide⟩ : Fin 148))
        (colE1 ⟨105, by decide⟩ 1 (transLenTr ⟨105, by decide⟩ 1 hp))
        (rowE1 (⟨137, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨137, by decide⟩ : Fin 148) ⟨105, by decide⟩ _
      (validAt ⟨137, by decide⟩ (listedAt ⟨137, by decide⟩ hj))
      (colE1 ⟨105, by decide⟩ 1 (transLenTr ⟨105, by decide⟩ 1 hp)) T137_105
      hfix137_105 hinj137_105 hcardT137_105
      (fun i => conj_mem_of_fixedPoints _ _ (T137_105 i) (hfix137_105 i) _)
      ⟨137, by decide⟩ ⟨105, by decide⟩ _
      (Q2.validAt ⟨137, by decide⟩ (Q2.listedAt ⟨137, by decide⟩
        (alnCheck_rep ⟨137, by decide⟩ hj hq).1))
      (colE2 ⟨105, by decide⟩ 1 hp) Q2.T137_105_2 Q2.hfix137_105_2 Q2.hinj137_105_2
      Q2.hcardT137_105_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T137_105_2 i) (Q2.hfix137_105_2 i) _)
      colCert_137_105_1.hD ?_).symm
  rw [alnId_137 j hj]


theorem leaf_137_105_2 (hp : 2 < (Q2.transData.getD 105 []).length)
    (j : Nat) (hj : j < (repChars.getD 137 []).length)
    (hq : (normIsRep.getD 137 []).getD j false = true) :
    species (Q2.reps (⟨105, by decide⟩ : Fin 148)) (colE2 ⟨105, by decide⟩ 2 hp)
        (rowE2 (⟨137, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨105, by decide⟩ : Fin 148))
        (colE1 ⟨105, by decide⟩ 2 (transLenTr ⟨105, by decide⟩ 2 hp))
        (rowE1 (⟨137, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨137, by decide⟩ : Fin 148) ⟨105, by decide⟩ _
      (validAt ⟨137, by decide⟩ (listedAt ⟨137, by decide⟩ hj))
      (colE1 ⟨105, by decide⟩ 2 (transLenTr ⟨105, by decide⟩ 2 hp)) T137_105
      hfix137_105 hinj137_105 hcardT137_105
      (fun i => conj_mem_of_fixedPoints _ _ (T137_105 i) (hfix137_105 i) _)
      ⟨137, by decide⟩ ⟨105, by decide⟩ _
      (Q2.validAt ⟨137, by decide⟩ (Q2.listedAt ⟨137, by decide⟩
        (alnCheck_rep ⟨137, by decide⟩ hj hq).1))
      (colE2 ⟨105, by decide⟩ 2 hp) Q2.T137_105_2 Q2.hfix137_105_2 Q2.hinj137_105_2
      Q2.hcardT137_105_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T137_105_2 i) (Q2.hfix137_105_2 i) _)
      colCert_137_105_2.hD ?_).symm
  rw [alnId_137 j hj]


theorem leaf_137_105_3 (hp : 3 < (Q2.transData.getD 105 []).length)
    (j : Nat) (hj : j < (repChars.getD 137 []).length)
    (hq : (normIsRep.getD 137 []).getD j false = true) :
    species (Q2.reps (⟨105, by decide⟩ : Fin 148)) (colE2 ⟨105, by decide⟩ 3 hp)
        (rowE2 (⟨137, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨105, by decide⟩ : Fin 148))
        (colE1 ⟨105, by decide⟩ 3 (transLenTr ⟨105, by decide⟩ 3 hp))
        (rowE1 (⟨137, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨137, by decide⟩ : Fin 148) ⟨105, by decide⟩ _
      (validAt ⟨137, by decide⟩ (listedAt ⟨137, by decide⟩ hj))
      (colE1 ⟨105, by decide⟩ 3 (transLenTr ⟨105, by decide⟩ 3 hp)) T137_105
      hfix137_105 hinj137_105 hcardT137_105
      (fun i => conj_mem_of_fixedPoints _ _ (T137_105 i) (hfix137_105 i) _)
      ⟨137, by decide⟩ ⟨105, by decide⟩ _
      (Q2.validAt ⟨137, by decide⟩ (Q2.listedAt ⟨137, by decide⟩
        (alnCheck_rep ⟨137, by decide⟩ hj hq).1))
      (colE2 ⟨105, by decide⟩ 3 hp) Q2.T137_105_2 Q2.hfix137_105_2 Q2.hinj137_105_2
      Q2.hcardT137_105_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T137_105_2 i) (Q2.hfix137_105_2 i) _)
      colCert_137_105_3.hD ?_).symm
  rw [alnId_137 j hj]


theorem leaf_137_105_4 (hp : 4 < (Q2.transData.getD 105 []).length)
    (j : Nat) (hj : j < (repChars.getD 137 []).length)
    (hq : (normIsRep.getD 137 []).getD j false = true) :
    species (Q2.reps (⟨105, by decide⟩ : Fin 148)) (colE2 ⟨105, by decide⟩ 4 hp)
        (rowE2 (⟨137, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨105, by decide⟩ : Fin 148))
        (colE1 ⟨105, by decide⟩ 4 (transLenTr ⟨105, by decide⟩ 4 hp))
        (rowE1 (⟨137, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨137, by decide⟩ : Fin 148) ⟨105, by decide⟩ _
      (validAt ⟨137, by decide⟩ (listedAt ⟨137, by decide⟩ hj))
      (colE1 ⟨105, by decide⟩ 4 (transLenTr ⟨105, by decide⟩ 4 hp)) T137_105
      hfix137_105 hinj137_105 hcardT137_105
      (fun i => conj_mem_of_fixedPoints _ _ (T137_105 i) (hfix137_105 i) _)
      ⟨137, by decide⟩ ⟨105, by decide⟩ _
      (Q2.validAt ⟨137, by decide⟩ (Q2.listedAt ⟨137, by decide⟩
        (alnCheck_rep ⟨137, by decide⟩ hj hq).1))
      (colE2 ⟨105, by decide⟩ 4 hp) Q2.T137_105_2 Q2.hfix137_105_2 Q2.hinj137_105_2
      Q2.hcardT137_105_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T137_105_2 i) (Q2.hfix137_105_2 i) _)
      colCert_137_105_4.hD ?_).symm
  rw [alnId_137 j hj]


theorem leaf_137_105_5 (hp : 5 < (Q2.transData.getD 105 []).length)
    (j : Nat) (hj : j < (repChars.getD 137 []).length)
    (hq : (normIsRep.getD 137 []).getD j false = true) :
    species (Q2.reps (⟨105, by decide⟩ : Fin 148)) (colE2 ⟨105, by decide⟩ 5 hp)
        (rowE2 (⟨137, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨105, by decide⟩ : Fin 148))
        (colE1 ⟨105, by decide⟩ 5 (transLenTr ⟨105, by decide⟩ 5 hp))
        (rowE1 (⟨137, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨137, by decide⟩ : Fin 148) ⟨105, by decide⟩ _
      (validAt ⟨137, by decide⟩ (listedAt ⟨137, by decide⟩ hj))
      (colE1 ⟨105, by decide⟩ 5 (transLenTr ⟨105, by decide⟩ 5 hp)) T137_105
      hfix137_105 hinj137_105 hcardT137_105
      (fun i => conj_mem_of_fixedPoints _ _ (T137_105 i) (hfix137_105 i) _)
      ⟨137, by decide⟩ ⟨105, by decide⟩ _
      (Q2.validAt ⟨137, by decide⟩ (Q2.listedAt ⟨137, by decide⟩
        (alnCheck_rep ⟨137, by decide⟩ hj hq).1))
      (colE2 ⟨105, by decide⟩ 5 hp) Q2.T137_105_2 Q2.hfix137_105_2 Q2.hinj137_105_2
      Q2.hcardT137_105_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T137_105_2 i) (Q2.hfix137_105_2 i) _)
      colCert_137_105_5.hD ?_).symm
  rw [alnId_137 j hj]


theorem leaf_137_105_10 (hp : 10 < (Q2.transData.getD 105 []).length)
    (j : Nat) (hj : j < (repChars.getD 137 []).length)
    (hq : (normIsRep.getD 137 []).getD j false = true) :
    species (Q2.reps (⟨105, by decide⟩ : Fin 148)) (colE2 ⟨105, by decide⟩ 10 hp)
        (rowE2 (⟨137, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨105, by decide⟩ : Fin 148))
        (colE1 ⟨105, by decide⟩ 10 (transLenTr ⟨105, by decide⟩ 10 hp))
        (rowE1 (⟨137, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨137, by decide⟩ : Fin 148) ⟨105, by decide⟩ _
      (validAt ⟨137, by decide⟩ (listedAt ⟨137, by decide⟩ hj))
      (colE1 ⟨105, by decide⟩ 10 (transLenTr ⟨105, by decide⟩ 10 hp)) T137_105
      hfix137_105 hinj137_105 hcardT137_105
      (fun i => conj_mem_of_fixedPoints _ _ (T137_105 i) (hfix137_105 i) _)
      ⟨137, by decide⟩ ⟨105, by decide⟩ _
      (Q2.validAt ⟨137, by decide⟩ (Q2.listedAt ⟨137, by decide⟩
        (alnCheck_rep ⟨137, by decide⟩ hj hq).1))
      (colE2 ⟨105, by decide⟩ 10 hp) Q2.T137_105_2 Q2.hfix137_105_2 Q2.hinj137_105_2
      Q2.hcardT137_105_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T137_105_2 i) (Q2.hfix137_105_2 i) _)
      colCert_137_105_10.hD ?_).symm
  rw [alnId_137 j hj]


theorem leaf_137_105_15 (hp : 15 < (Q2.transData.getD 105 []).length)
    (j : Nat) (hj : j < (repChars.getD 137 []).length)
    (hq : (normIsRep.getD 137 []).getD j false = true) :
    species (Q2.reps (⟨105, by decide⟩ : Fin 148)) (colE2 ⟨105, by decide⟩ 15 hp)
        (rowE2 (⟨137, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨105, by decide⟩ : Fin 148))
        (colE1 ⟨105, by decide⟩ 15 (transLenTr ⟨105, by decide⟩ 15 hp))
        (rowE1 (⟨137, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨137, by decide⟩ : Fin 148) ⟨105, by decide⟩ _
      (validAt ⟨137, by decide⟩ (listedAt ⟨137, by decide⟩ hj))
      (colE1 ⟨105, by decide⟩ 15 (transLenTr ⟨105, by decide⟩ 15 hp)) T137_105
      hfix137_105 hinj137_105 hcardT137_105
      (fun i => conj_mem_of_fixedPoints _ _ (T137_105 i) (hfix137_105 i) _)
      ⟨137, by decide⟩ ⟨105, by decide⟩ _
      (Q2.validAt ⟨137, by decide⟩ (Q2.listedAt ⟨137, by decide⟩
        (alnCheck_rep ⟨137, by decide⟩ hj hq).1))
      (colE2 ⟨105, by decide⟩ 15 hp) Q2.T137_105_2 Q2.hfix137_105_2 Q2.hinj137_105_2
      Q2.hcardT137_105_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T137_105_2 i) (Q2.hfix137_105_2 i) _)
      colCert_137_105_15.hD ?_).symm
  rw [alnId_137 j hj]


theorem leaf_137_105_20 (hp : 20 < (Q2.transData.getD 105 []).length)
    (j : Nat) (hj : j < (repChars.getD 137 []).length)
    (hq : (normIsRep.getD 137 []).getD j false = true) :
    species (Q2.reps (⟨105, by decide⟩ : Fin 148)) (colE2 ⟨105, by decide⟩ 20 hp)
        (rowE2 (⟨137, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨105, by decide⟩ : Fin 148))
        (colE1 ⟨105, by decide⟩ 20 (transLenTr ⟨105, by decide⟩ 20 hp))
        (rowE1 (⟨137, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨137, by decide⟩ : Fin 148) ⟨105, by decide⟩ _
      (validAt ⟨137, by decide⟩ (listedAt ⟨137, by decide⟩ hj))
      (colE1 ⟨105, by decide⟩ 20 (transLenTr ⟨105, by decide⟩ 20 hp)) T137_105
      hfix137_105 hinj137_105 hcardT137_105
      (fun i => conj_mem_of_fixedPoints _ _ (T137_105 i) (hfix137_105 i) _)
      ⟨137, by decide⟩ ⟨105, by decide⟩ _
      (Q2.validAt ⟨137, by decide⟩ (Q2.listedAt ⟨137, by decide⟩
        (alnCheck_rep ⟨137, by decide⟩ hj hq).1))
      (colE2 ⟨105, by decide⟩ 20 hp) Q2.T137_105_2 Q2.hfix137_105_2 Q2.hinj137_105_2
      Q2.hcardT137_105_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T137_105_2 i) (Q2.hfix137_105_2 i) _)
      colCert_137_105_20.hD ?_).symm
  rw [alnId_137 j hj]


theorem leaf_137_105_25 (hp : 25 < (Q2.transData.getD 105 []).length)
    (j : Nat) (hj : j < (repChars.getD 137 []).length)
    (hq : (normIsRep.getD 137 []).getD j false = true) :
    species (Q2.reps (⟨105, by decide⟩ : Fin 148)) (colE2 ⟨105, by decide⟩ 25 hp)
        (rowE2 (⟨137, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨105, by decide⟩ : Fin 148))
        (colE1 ⟨105, by decide⟩ 25 (transLenTr ⟨105, by decide⟩ 25 hp))
        (rowE1 (⟨137, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨137, by decide⟩ : Fin 148) ⟨105, by decide⟩ _
      (validAt ⟨137, by decide⟩ (listedAt ⟨137, by decide⟩ hj))
      (colE1 ⟨105, by decide⟩ 25 (transLenTr ⟨105, by decide⟩ 25 hp)) T137_105
      hfix137_105 hinj137_105 hcardT137_105
      (fun i => conj_mem_of_fixedPoints _ _ (T137_105 i) (hfix137_105 i) _)
      ⟨137, by decide⟩ ⟨105, by decide⟩ _
      (Q2.validAt ⟨137, by decide⟩ (Q2.listedAt ⟨137, by decide⟩
        (alnCheck_rep ⟨137, by decide⟩ hj hq).1))
      (colE2 ⟨105, by decide⟩ 25 hp) Q2.T137_105_2 Q2.hfix137_105_2 Q2.hinj137_105_2
      Q2.hcardT137_105_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T137_105_2 i) (Q2.hfix137_105_2 i) _)
      colCert_137_105_25.hD ?_).symm
  rw [alnId_137 j hj]


theorem leaf_137_105_50 (hp : 50 < (Q2.transData.getD 105 []).length)
    (j : Nat) (hj : j < (repChars.getD 137 []).length)
    (hq : (normIsRep.getD 137 []).getD j false = true) :
    species (Q2.reps (⟨105, by decide⟩ : Fin 148)) (colE2 ⟨105, by decide⟩ 50 hp)
        (rowE2 (⟨137, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨105, by decide⟩ : Fin 148))
        (colE1 ⟨105, by decide⟩ 50 (transLenTr ⟨105, by decide⟩ 50 hp))
        (rowE1 (⟨137, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨137, by decide⟩ : Fin 148) ⟨105, by decide⟩ _
      (validAt ⟨137, by decide⟩ (listedAt ⟨137, by decide⟩ hj))
      (colE1 ⟨105, by decide⟩ 50 (transLenTr ⟨105, by decide⟩ 50 hp)) T137_105
      hfix137_105 hinj137_105 hcardT137_105
      (fun i => conj_mem_of_fixedPoints _ _ (T137_105 i) (hfix137_105 i) _)
      ⟨137, by decide⟩ ⟨105, by decide⟩ _
      (Q2.validAt ⟨137, by decide⟩ (Q2.listedAt ⟨137, by decide⟩
        (alnCheck_rep ⟨137, by decide⟩ hj hq).1))
      (colE2 ⟨105, by decide⟩ 50 hp) Q2.T137_105_2 Q2.hfix137_105_2 Q2.hinj137_105_2
      Q2.hcardT137_105_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T137_105_2 i) (Q2.hfix137_105_2 i) _)
      colCert_137_105_50.hD ?_).symm
  rw [alnId_137 j hj]


theorem leaf_137_105_75 (hp : 75 < (Q2.transData.getD 105 []).length)
    (j : Nat) (hj : j < (repChars.getD 137 []).length)
    (hq : (normIsRep.getD 137 []).getD j false = true) :
    species (Q2.reps (⟨105, by decide⟩ : Fin 148)) (colE2 ⟨105, by decide⟩ 75 hp)
        (rowE2 (⟨137, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨105, by decide⟩ : Fin 148))
        (colE1 ⟨105, by decide⟩ 75 (transLenTr ⟨105, by decide⟩ 75 hp))
        (rowE1 (⟨137, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨137, by decide⟩ : Fin 148) ⟨105, by decide⟩ _
      (validAt ⟨137, by decide⟩ (listedAt ⟨137, by decide⟩ hj))
      (colE1 ⟨105, by decide⟩ 75 (transLenTr ⟨105, by decide⟩ 75 hp)) T137_105
      hfix137_105 hinj137_105 hcardT137_105
      (fun i => conj_mem_of_fixedPoints _ _ (T137_105 i) (hfix137_105 i) _)
      ⟨137, by decide⟩ ⟨105, by decide⟩ _
      (Q2.validAt ⟨137, by decide⟩ (Q2.listedAt ⟨137, by decide⟩
        (alnCheck_rep ⟨137, by decide⟩ hj hq).1))
      (colE2 ⟨105, by decide⟩ 75 hp) Q2.T137_105_2 Q2.hfix137_105_2 Q2.hinj137_105_2
      Q2.hcardT137_105_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T137_105_2 i) (Q2.hfix137_105_2 i) _)
      colCert_137_105_75.hD ?_).symm
  rw [alnId_137 j hj]


theorem leaf_137_105_100 (hp : 100 < (Q2.transData.getD 105 []).length)
    (j : Nat) (hj : j < (repChars.getD 137 []).length)
    (hq : (normIsRep.getD 137 []).getD j false = true) :
    species (Q2.reps (⟨105, by decide⟩ : Fin 148)) (colE2 ⟨105, by decide⟩ 100 hp)
        (rowE2 (⟨137, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨105, by decide⟩ : Fin 148))
        (colE1 ⟨105, by decide⟩ 100 (transLenTr ⟨105, by decide⟩ 100 hp))
        (rowE1 (⟨137, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨137, by decide⟩ : Fin 148) ⟨105, by decide⟩ _
      (validAt ⟨137, by decide⟩ (listedAt ⟨137, by decide⟩ hj))
      (colE1 ⟨105, by decide⟩ 100 (transLenTr ⟨105, by decide⟩ 100 hp)) T137_105
      hfix137_105 hinj137_105 hcardT137_105
      (fun i => conj_mem_of_fixedPoints _ _ (T137_105 i) (hfix137_105 i) _)
      ⟨137, by decide⟩ ⟨105, by decide⟩ _
      (Q2.validAt ⟨137, by decide⟩ (Q2.listedAt ⟨137, by decide⟩
        (alnCheck_rep ⟨137, by decide⟩ hj hq).1))
      (colE2 ⟨105, by decide⟩ 100 hp) Q2.T137_105_2 Q2.hfix137_105_2 Q2.hinj137_105_2
      Q2.hcardT137_105_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T137_105_2 i) (Q2.hfix137_105_2 i) _)
      colCert_137_105_100.hD ?_).symm
  rw [alnId_137 j hj]


theorem leaf_137_111_0 (hp : 0 < (Q2.transData.getD 111 []).length)
    (j : Nat) (hj : j < (repChars.getD 137 []).length)
    (hq : (normIsRep.getD 137 []).getD j false = true) :
    species (Q2.reps (⟨111, by decide⟩ : Fin 148)) (colE2 ⟨111, by decide⟩ 0 hp)
        (rowE2 (⟨137, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨111, by decide⟩ : Fin 148))
        (colE1 ⟨111, by decide⟩ 0 (transLenTr ⟨111, by decide⟩ 0 hp))
        (rowE1 (⟨137, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨137, by decide⟩ : Fin 148) ⟨111, by decide⟩ _
      (validAt ⟨137, by decide⟩ (listedAt ⟨137, by decide⟩ hj))
      (colE1 ⟨111, by decide⟩ 0 (transLenTr ⟨111, by decide⟩ 0 hp)) T137_111
      hfix137_111 hinj137_111 hcardT137_111
      (fun i => conj_mem_of_fixedPoints _ _ (T137_111 i) (hfix137_111 i) _)
      ⟨137, by decide⟩ ⟨111, by decide⟩ _
      (Q2.validAt ⟨137, by decide⟩ (Q2.listedAt ⟨137, by decide⟩
        (alnCheck_rep ⟨137, by decide⟩ hj hq).1))
      (colE2 ⟨111, by decide⟩ 0 hp) Q2.T137_111_2 Q2.hfix137_111_2 Q2.hinj137_111_2
      Q2.hcardT137_111_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T137_111_2 i) (Q2.hfix137_111_2 i) _)
      colCert_137_111_0.hD ?_).symm
  rw [alnId_137 j hj]


theorem leaf_137_111_1 (hp : 1 < (Q2.transData.getD 111 []).length)
    (j : Nat) (hj : j < (repChars.getD 137 []).length)
    (hq : (normIsRep.getD 137 []).getD j false = true) :
    species (Q2.reps (⟨111, by decide⟩ : Fin 148)) (colE2 ⟨111, by decide⟩ 1 hp)
        (rowE2 (⟨137, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨111, by decide⟩ : Fin 148))
        (colE1 ⟨111, by decide⟩ 1 (transLenTr ⟨111, by decide⟩ 1 hp))
        (rowE1 (⟨137, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨137, by decide⟩ : Fin 148) ⟨111, by decide⟩ _
      (validAt ⟨137, by decide⟩ (listedAt ⟨137, by decide⟩ hj))
      (colE1 ⟨111, by decide⟩ 1 (transLenTr ⟨111, by decide⟩ 1 hp)) T137_111
      hfix137_111 hinj137_111 hcardT137_111
      (fun i => conj_mem_of_fixedPoints _ _ (T137_111 i) (hfix137_111 i) _)
      ⟨137, by decide⟩ ⟨111, by decide⟩ _
      (Q2.validAt ⟨137, by decide⟩ (Q2.listedAt ⟨137, by decide⟩
        (alnCheck_rep ⟨137, by decide⟩ hj hq).1))
      (colE2 ⟨111, by decide⟩ 1 hp) Q2.T137_111_2 Q2.hfix137_111_2 Q2.hinj137_111_2
      Q2.hcardT137_111_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T137_111_2 i) (Q2.hfix137_111_2 i) _)
      colCert_137_111_1.hD ?_).symm
  rw [alnId_137 j hj]


theorem leaf_137_111_2 (hp : 2 < (Q2.transData.getD 111 []).length)
    (j : Nat) (hj : j < (repChars.getD 137 []).length)
    (hq : (normIsRep.getD 137 []).getD j false = true) :
    species (Q2.reps (⟨111, by decide⟩ : Fin 148)) (colE2 ⟨111, by decide⟩ 2 hp)
        (rowE2 (⟨137, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨111, by decide⟩ : Fin 148))
        (colE1 ⟨111, by decide⟩ 2 (transLenTr ⟨111, by decide⟩ 2 hp))
        (rowE1 (⟨137, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨137, by decide⟩ : Fin 148) ⟨111, by decide⟩ _
      (validAt ⟨137, by decide⟩ (listedAt ⟨137, by decide⟩ hj))
      (colE1 ⟨111, by decide⟩ 2 (transLenTr ⟨111, by decide⟩ 2 hp)) T137_111
      hfix137_111 hinj137_111 hcardT137_111
      (fun i => conj_mem_of_fixedPoints _ _ (T137_111 i) (hfix137_111 i) _)
      ⟨137, by decide⟩ ⟨111, by decide⟩ _
      (Q2.validAt ⟨137, by decide⟩ (Q2.listedAt ⟨137, by decide⟩
        (alnCheck_rep ⟨137, by decide⟩ hj hq).1))
      (colE2 ⟨111, by decide⟩ 2 hp) Q2.T137_111_2 Q2.hfix137_111_2 Q2.hinj137_111_2
      Q2.hcardT137_111_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T137_111_2 i) (Q2.hfix137_111_2 i) _)
      colCert_137_111_2.hD ?_).symm
  rw [alnId_137 j hj]


theorem leaf_137_111_3 (hp : 3 < (Q2.transData.getD 111 []).length)
    (j : Nat) (hj : j < (repChars.getD 137 []).length)
    (hq : (normIsRep.getD 137 []).getD j false = true) :
    species (Q2.reps (⟨111, by decide⟩ : Fin 148)) (colE2 ⟨111, by decide⟩ 3 hp)
        (rowE2 (⟨137, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨111, by decide⟩ : Fin 148))
        (colE1 ⟨111, by decide⟩ 3 (transLenTr ⟨111, by decide⟩ 3 hp))
        (rowE1 (⟨137, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨137, by decide⟩ : Fin 148) ⟨111, by decide⟩ _
      (validAt ⟨137, by decide⟩ (listedAt ⟨137, by decide⟩ hj))
      (colE1 ⟨111, by decide⟩ 3 (transLenTr ⟨111, by decide⟩ 3 hp)) T137_111
      hfix137_111 hinj137_111 hcardT137_111
      (fun i => conj_mem_of_fixedPoints _ _ (T137_111 i) (hfix137_111 i) _)
      ⟨137, by decide⟩ ⟨111, by decide⟩ _
      (Q2.validAt ⟨137, by decide⟩ (Q2.listedAt ⟨137, by decide⟩
        (alnCheck_rep ⟨137, by decide⟩ hj hq).1))
      (colE2 ⟨111, by decide⟩ 3 hp) Q2.T137_111_2 Q2.hfix137_111_2 Q2.hinj137_111_2
      Q2.hcardT137_111_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T137_111_2 i) (Q2.hfix137_111_2 i) _)
      colCert_137_111_3.hD ?_).symm
  rw [alnId_137 j hj]


theorem leaf_137_111_4 (hp : 4 < (Q2.transData.getD 111 []).length)
    (j : Nat) (hj : j < (repChars.getD 137 []).length)
    (hq : (normIsRep.getD 137 []).getD j false = true) :
    species (Q2.reps (⟨111, by decide⟩ : Fin 148)) (colE2 ⟨111, by decide⟩ 4 hp)
        (rowE2 (⟨137, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨111, by decide⟩ : Fin 148))
        (colE1 ⟨111, by decide⟩ 4 (transLenTr ⟨111, by decide⟩ 4 hp))
        (rowE1 (⟨137, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨137, by decide⟩ : Fin 148) ⟨111, by decide⟩ _
      (validAt ⟨137, by decide⟩ (listedAt ⟨137, by decide⟩ hj))
      (colE1 ⟨111, by decide⟩ 4 (transLenTr ⟨111, by decide⟩ 4 hp)) T137_111
      hfix137_111 hinj137_111 hcardT137_111
      (fun i => conj_mem_of_fixedPoints _ _ (T137_111 i) (hfix137_111 i) _)
      ⟨137, by decide⟩ ⟨111, by decide⟩ _
      (Q2.validAt ⟨137, by decide⟩ (Q2.listedAt ⟨137, by decide⟩
        (alnCheck_rep ⟨137, by decide⟩ hj hq).1))
      (colE2 ⟨111, by decide⟩ 4 hp) Q2.T137_111_2 Q2.hfix137_111_2 Q2.hinj137_111_2
      Q2.hcardT137_111_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T137_111_2 i) (Q2.hfix137_111_2 i) _)
      colCert_137_111_4.hD ?_).symm
  rw [alnId_137 j hj]


theorem leaf_137_111_5 (hp : 5 < (Q2.transData.getD 111 []).length)
    (j : Nat) (hj : j < (repChars.getD 137 []).length)
    (hq : (normIsRep.getD 137 []).getD j false = true) :
    species (Q2.reps (⟨111, by decide⟩ : Fin 148)) (colE2 ⟨111, by decide⟩ 5 hp)
        (rowE2 (⟨137, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨111, by decide⟩ : Fin 148))
        (colE1 ⟨111, by decide⟩ 5 (transLenTr ⟨111, by decide⟩ 5 hp))
        (rowE1 (⟨137, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨137, by decide⟩ : Fin 148) ⟨111, by decide⟩ _
      (validAt ⟨137, by decide⟩ (listedAt ⟨137, by decide⟩ hj))
      (colE1 ⟨111, by decide⟩ 5 (transLenTr ⟨111, by decide⟩ 5 hp)) T137_111
      hfix137_111 hinj137_111 hcardT137_111
      (fun i => conj_mem_of_fixedPoints _ _ (T137_111 i) (hfix137_111 i) _)
      ⟨137, by decide⟩ ⟨111, by decide⟩ _
      (Q2.validAt ⟨137, by decide⟩ (Q2.listedAt ⟨137, by decide⟩
        (alnCheck_rep ⟨137, by decide⟩ hj hq).1))
      (colE2 ⟨111, by decide⟩ 5 hp) Q2.T137_111_2 Q2.hfix137_111_2 Q2.hinj137_111_2
      Q2.hcardT137_111_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T137_111_2 i) (Q2.hfix137_111_2 i) _)
      colCert_137_111_5.hD ?_).symm
  rw [alnId_137 j hj]


theorem leaf_137_111_10 (hp : 10 < (Q2.transData.getD 111 []).length)
    (j : Nat) (hj : j < (repChars.getD 137 []).length)
    (hq : (normIsRep.getD 137 []).getD j false = true) :
    species (Q2.reps (⟨111, by decide⟩ : Fin 148)) (colE2 ⟨111, by decide⟩ 10 hp)
        (rowE2 (⟨137, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨111, by decide⟩ : Fin 148))
        (colE1 ⟨111, by decide⟩ 10 (transLenTr ⟨111, by decide⟩ 10 hp))
        (rowE1 (⟨137, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨137, by decide⟩ : Fin 148) ⟨111, by decide⟩ _
      (validAt ⟨137, by decide⟩ (listedAt ⟨137, by decide⟩ hj))
      (colE1 ⟨111, by decide⟩ 10 (transLenTr ⟨111, by decide⟩ 10 hp)) T137_111
      hfix137_111 hinj137_111 hcardT137_111
      (fun i => conj_mem_of_fixedPoints _ _ (T137_111 i) (hfix137_111 i) _)
      ⟨137, by decide⟩ ⟨111, by decide⟩ _
      (Q2.validAt ⟨137, by decide⟩ (Q2.listedAt ⟨137, by decide⟩
        (alnCheck_rep ⟨137, by decide⟩ hj hq).1))
      (colE2 ⟨111, by decide⟩ 10 hp) Q2.T137_111_2 Q2.hfix137_111_2 Q2.hinj137_111_2
      Q2.hcardT137_111_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T137_111_2 i) (Q2.hfix137_111_2 i) _)
      ?_).symm
  rw [show colData1 (⟨137, by decide⟩ : Fin 148)
        ((colE1 ⟨111, by decide⟩ 10 (transLenTr ⟨111, by decide⟩ 10 hp) : ↥(reps ⟨111, by decide⟩)) : Coordinate 1)
        T137_111 = colFn colCertDiv_137_111_10.D1 (m := 5) from colCertDiv_137_111_10.bind1,
    show colData2 (⟨137, by decide⟩ : Fin 148)
        ((colE2 ⟨111, by decide⟩ 10 hp : ↥(Q2.reps ⟨111, by decide⟩)) : Coordinate 2)
        Q2.T137_111_2 = colFn colCertDiv_137_111_10.D2 (m := 5) from colCertDiv_137_111_10.bind2]
  rw [alnId_137 j hj]
  exact fastcode_of_div ⟨137, by decide⟩ _ _ _
    ((alnId_137 j hj) ▸ Q2.listedAt (⟨137, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨137, by decide⟩ : Fin 148) hj hq).1) colCertDiv_137_111_10_match


theorem leaf_137_111_15 (hp : 15 < (Q2.transData.getD 111 []).length)
    (j : Nat) (hj : j < (repChars.getD 137 []).length)
    (hq : (normIsRep.getD 137 []).getD j false = true) :
    species (Q2.reps (⟨111, by decide⟩ : Fin 148)) (colE2 ⟨111, by decide⟩ 15 hp)
        (rowE2 (⟨137, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨111, by decide⟩ : Fin 148))
        (colE1 ⟨111, by decide⟩ 15 (transLenTr ⟨111, by decide⟩ 15 hp))
        (rowE1 (⟨137, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨137, by decide⟩ : Fin 148) ⟨111, by decide⟩ _
      (validAt ⟨137, by decide⟩ (listedAt ⟨137, by decide⟩ hj))
      (colE1 ⟨111, by decide⟩ 15 (transLenTr ⟨111, by decide⟩ 15 hp)) T137_111
      hfix137_111 hinj137_111 hcardT137_111
      (fun i => conj_mem_of_fixedPoints _ _ (T137_111 i) (hfix137_111 i) _)
      ⟨137, by decide⟩ ⟨111, by decide⟩ _
      (Q2.validAt ⟨137, by decide⟩ (Q2.listedAt ⟨137, by decide⟩
        (alnCheck_rep ⟨137, by decide⟩ hj hq).1))
      (colE2 ⟨111, by decide⟩ 15 hp) Q2.T137_111_2 Q2.hfix137_111_2 Q2.hinj137_111_2
      Q2.hcardT137_111_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T137_111_2 i) (Q2.hfix137_111_2 i) _)
      ?_).symm
  rw [show colData1 (⟨137, by decide⟩ : Fin 148)
        ((colE1 ⟨111, by decide⟩ 15 (transLenTr ⟨111, by decide⟩ 15 hp) : ↥(reps ⟨111, by decide⟩)) : Coordinate 1)
        T137_111 = colFn colCertDiv_137_111_15.D1 (m := 5) from colCertDiv_137_111_15.bind1,
    show colData2 (⟨137, by decide⟩ : Fin 148)
        ((colE2 ⟨111, by decide⟩ 15 hp : ↥(Q2.reps ⟨111, by decide⟩)) : Coordinate 2)
        Q2.T137_111_2 = colFn colCertDiv_137_111_15.D2 (m := 5) from colCertDiv_137_111_15.bind2]
  rw [alnId_137 j hj]
  exact fastcode_of_div ⟨137, by decide⟩ _ _ _
    ((alnId_137 j hj) ▸ Q2.listedAt (⟨137, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨137, by decide⟩ : Fin 148) hj hq).1) colCertDiv_137_111_15_match


theorem leaf_137_111_20 (hp : 20 < (Q2.transData.getD 111 []).length)
    (j : Nat) (hj : j < (repChars.getD 137 []).length)
    (hq : (normIsRep.getD 137 []).getD j false = true) :
    species (Q2.reps (⟨111, by decide⟩ : Fin 148)) (colE2 ⟨111, by decide⟩ 20 hp)
        (rowE2 (⟨137, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨111, by decide⟩ : Fin 148))
        (colE1 ⟨111, by decide⟩ 20 (transLenTr ⟨111, by decide⟩ 20 hp))
        (rowE1 (⟨137, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨137, by decide⟩ : Fin 148) ⟨111, by decide⟩ _
      (validAt ⟨137, by decide⟩ (listedAt ⟨137, by decide⟩ hj))
      (colE1 ⟨111, by decide⟩ 20 (transLenTr ⟨111, by decide⟩ 20 hp)) T137_111
      hfix137_111 hinj137_111 hcardT137_111
      (fun i => conj_mem_of_fixedPoints _ _ (T137_111 i) (hfix137_111 i) _)
      ⟨137, by decide⟩ ⟨111, by decide⟩ _
      (Q2.validAt ⟨137, by decide⟩ (Q2.listedAt ⟨137, by decide⟩
        (alnCheck_rep ⟨137, by decide⟩ hj hq).1))
      (colE2 ⟨111, by decide⟩ 20 hp) Q2.T137_111_2 Q2.hfix137_111_2 Q2.hinj137_111_2
      Q2.hcardT137_111_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T137_111_2 i) (Q2.hfix137_111_2 i) _)
      ?_).symm
  rw [show colData1 (⟨137, by decide⟩ : Fin 148)
        ((colE1 ⟨111, by decide⟩ 20 (transLenTr ⟨111, by decide⟩ 20 hp) : ↥(reps ⟨111, by decide⟩)) : Coordinate 1)
        T137_111 = colFn colCertDiv_137_111_20.D1 (m := 5) from colCertDiv_137_111_20.bind1,
    show colData2 (⟨137, by decide⟩ : Fin 148)
        ((colE2 ⟨111, by decide⟩ 20 hp : ↥(Q2.reps ⟨111, by decide⟩)) : Coordinate 2)
        Q2.T137_111_2 = colFn colCertDiv_137_111_20.D2 (m := 5) from colCertDiv_137_111_20.bind2]
  rw [alnId_137 j hj]
  exact fastcode_of_div ⟨137, by decide⟩ _ _ _
    ((alnId_137 j hj) ▸ Q2.listedAt (⟨137, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨137, by decide⟩ : Fin 148) hj hq).1) colCertDiv_137_111_20_match


theorem leaf_137_137_0 (hp : 0 < (Q2.transData.getD 137 []).length)
    (j : Nat) (hj : j < (repChars.getD 137 []).length)
    (hq : (normIsRep.getD 137 []).getD j false = true) :
    species (Q2.reps (⟨137, by decide⟩ : Fin 148)) (colE2 ⟨137, by decide⟩ 0 hp)
        (rowE2 (⟨137, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨137, by decide⟩ : Fin 148))
        (colE1 ⟨137, by decide⟩ 0 (transLenTr ⟨137, by decide⟩ 0 hp))
        (rowE1 (⟨137, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨137, by decide⟩ : Fin 148) ⟨137, by decide⟩ _
      (validAt ⟨137, by decide⟩ (listedAt ⟨137, by decide⟩ hj))
      (colE1 ⟨137, by decide⟩ 0 (transLenTr ⟨137, by decide⟩ 0 hp)) T137_137
      hfix137_137 hinj137_137 hcardT137_137
      (fun i => conj_mem_of_fixedPoints _ _ (T137_137 i) (hfix137_137 i) _)
      ⟨137, by decide⟩ ⟨137, by decide⟩ _
      (Q2.validAt ⟨137, by decide⟩ (Q2.listedAt ⟨137, by decide⟩
        (alnCheck_rep ⟨137, by decide⟩ hj hq).1))
      (colE2 ⟨137, by decide⟩ 0 hp) Q2.T137_137_2 Q2.hfix137_137_2 Q2.hinj137_137_2
      Q2.hcardT137_137_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T137_137_2 i) (Q2.hfix137_137_2 i) _)
      colCert_137_137_0.hD ?_).symm
  rw [alnId_137 j hj]


theorem leaf_137_137_1 (hp : 1 < (Q2.transData.getD 137 []).length)
    (j : Nat) (hj : j < (repChars.getD 137 []).length)
    (hq : (normIsRep.getD 137 []).getD j false = true) :
    species (Q2.reps (⟨137, by decide⟩ : Fin 148)) (colE2 ⟨137, by decide⟩ 1 hp)
        (rowE2 (⟨137, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨137, by decide⟩ : Fin 148))
        (colE1 ⟨137, by decide⟩ 1 (transLenTr ⟨137, by decide⟩ 1 hp))
        (rowE1 (⟨137, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨137, by decide⟩ : Fin 148) ⟨137, by decide⟩ _
      (validAt ⟨137, by decide⟩ (listedAt ⟨137, by decide⟩ hj))
      (colE1 ⟨137, by decide⟩ 1 (transLenTr ⟨137, by decide⟩ 1 hp)) T137_137
      hfix137_137 hinj137_137 hcardT137_137
      (fun i => conj_mem_of_fixedPoints _ _ (T137_137 i) (hfix137_137 i) _)
      ⟨137, by decide⟩ ⟨137, by decide⟩ _
      (Q2.validAt ⟨137, by decide⟩ (Q2.listedAt ⟨137, by decide⟩
        (alnCheck_rep ⟨137, by decide⟩ hj hq).1))
      (colE2 ⟨137, by decide⟩ 1 hp) Q2.T137_137_2 Q2.hfix137_137_2 Q2.hinj137_137_2
      Q2.hcardT137_137_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T137_137_2 i) (Q2.hfix137_137_2 i) _)
      colCert_137_137_1.hD ?_).symm
  rw [alnId_137 j hj]


theorem leaf_137_137_2 (hp : 2 < (Q2.transData.getD 137 []).length)
    (j : Nat) (hj : j < (repChars.getD 137 []).length)
    (hq : (normIsRep.getD 137 []).getD j false = true) :
    species (Q2.reps (⟨137, by decide⟩ : Fin 148)) (colE2 ⟨137, by decide⟩ 2 hp)
        (rowE2 (⟨137, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨137, by decide⟩ : Fin 148))
        (colE1 ⟨137, by decide⟩ 2 (transLenTr ⟨137, by decide⟩ 2 hp))
        (rowE1 (⟨137, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨137, by decide⟩ : Fin 148) ⟨137, by decide⟩ _
      (validAt ⟨137, by decide⟩ (listedAt ⟨137, by decide⟩ hj))
      (colE1 ⟨137, by decide⟩ 2 (transLenTr ⟨137, by decide⟩ 2 hp)) T137_137
      hfix137_137 hinj137_137 hcardT137_137
      (fun i => conj_mem_of_fixedPoints _ _ (T137_137 i) (hfix137_137 i) _)
      ⟨137, by decide⟩ ⟨137, by decide⟩ _
      (Q2.validAt ⟨137, by decide⟩ (Q2.listedAt ⟨137, by decide⟩
        (alnCheck_rep ⟨137, by decide⟩ hj hq).1))
      (colE2 ⟨137, by decide⟩ 2 hp) Q2.T137_137_2 Q2.hfix137_137_2 Q2.hinj137_137_2
      Q2.hcardT137_137_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T137_137_2 i) (Q2.hfix137_137_2 i) _)
      colCert_137_137_2.hD ?_).symm
  rw [alnId_137 j hj]


theorem leaf_137_137_3 (hp : 3 < (Q2.transData.getD 137 []).length)
    (j : Nat) (hj : j < (repChars.getD 137 []).length)
    (hq : (normIsRep.getD 137 []).getD j false = true) :
    species (Q2.reps (⟨137, by decide⟩ : Fin 148)) (colE2 ⟨137, by decide⟩ 3 hp)
        (rowE2 (⟨137, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨137, by decide⟩ : Fin 148))
        (colE1 ⟨137, by decide⟩ 3 (transLenTr ⟨137, by decide⟩ 3 hp))
        (rowE1 (⟨137, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨137, by decide⟩ : Fin 148) ⟨137, by decide⟩ _
      (validAt ⟨137, by decide⟩ (listedAt ⟨137, by decide⟩ hj))
      (colE1 ⟨137, by decide⟩ 3 (transLenTr ⟨137, by decide⟩ 3 hp)) T137_137
      hfix137_137 hinj137_137 hcardT137_137
      (fun i => conj_mem_of_fixedPoints _ _ (T137_137 i) (hfix137_137 i) _)
      ⟨137, by decide⟩ ⟨137, by decide⟩ _
      (Q2.validAt ⟨137, by decide⟩ (Q2.listedAt ⟨137, by decide⟩
        (alnCheck_rep ⟨137, by decide⟩ hj hq).1))
      (colE2 ⟨137, by decide⟩ 3 hp) Q2.T137_137_2 Q2.hfix137_137_2 Q2.hinj137_137_2
      Q2.hcardT137_137_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T137_137_2 i) (Q2.hfix137_137_2 i) _)
      colCert_137_137_3.hD ?_).symm
  rw [alnId_137 j hj]


theorem leaf_137_137_4 (hp : 4 < (Q2.transData.getD 137 []).length)
    (j : Nat) (hj : j < (repChars.getD 137 []).length)
    (hq : (normIsRep.getD 137 []).getD j false = true) :
    species (Q2.reps (⟨137, by decide⟩ : Fin 148)) (colE2 ⟨137, by decide⟩ 4 hp)
        (rowE2 (⟨137, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨137, by decide⟩ : Fin 148))
        (colE1 ⟨137, by decide⟩ 4 (transLenTr ⟨137, by decide⟩ 4 hp))
        (rowE1 (⟨137, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨137, by decide⟩ : Fin 148) ⟨137, by decide⟩ _
      (validAt ⟨137, by decide⟩ (listedAt ⟨137, by decide⟩ hj))
      (colE1 ⟨137, by decide⟩ 4 (transLenTr ⟨137, by decide⟩ 4 hp)) T137_137
      hfix137_137 hinj137_137 hcardT137_137
      (fun i => conj_mem_of_fixedPoints _ _ (T137_137 i) (hfix137_137 i) _)
      ⟨137, by decide⟩ ⟨137, by decide⟩ _
      (Q2.validAt ⟨137, by decide⟩ (Q2.listedAt ⟨137, by decide⟩
        (alnCheck_rep ⟨137, by decide⟩ hj hq).1))
      (colE2 ⟨137, by decide⟩ 4 hp) Q2.T137_137_2 Q2.hfix137_137_2 Q2.hinj137_137_2
      Q2.hcardT137_137_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T137_137_2 i) (Q2.hfix137_137_2 i) _)
      colCert_137_137_4.hD ?_).symm
  rw [alnId_137 j hj]


theorem leaf_137_137_5 (hp : 5 < (Q2.transData.getD 137 []).length)
    (j : Nat) (hj : j < (repChars.getD 137 []).length)
    (hq : (normIsRep.getD 137 []).getD j false = true) :
    species (Q2.reps (⟨137, by decide⟩ : Fin 148)) (colE2 ⟨137, by decide⟩ 5 hp)
        (rowE2 (⟨137, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨137, by decide⟩ : Fin 148))
        (colE1 ⟨137, by decide⟩ 5 (transLenTr ⟨137, by decide⟩ 5 hp))
        (rowE1 (⟨137, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨137, by decide⟩ : Fin 148) ⟨137, by decide⟩ _
      (validAt ⟨137, by decide⟩ (listedAt ⟨137, by decide⟩ hj))
      (colE1 ⟨137, by decide⟩ 5 (transLenTr ⟨137, by decide⟩ 5 hp)) T137_137
      hfix137_137 hinj137_137 hcardT137_137
      (fun i => conj_mem_of_fixedPoints _ _ (T137_137 i) (hfix137_137 i) _)
      ⟨137, by decide⟩ ⟨137, by decide⟩ _
      (Q2.validAt ⟨137, by decide⟩ (Q2.listedAt ⟨137, by decide⟩
        (alnCheck_rep ⟨137, by decide⟩ hj hq).1))
      (colE2 ⟨137, by decide⟩ 5 hp) Q2.T137_137_2 Q2.hfix137_137_2 Q2.hinj137_137_2
      Q2.hcardT137_137_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T137_137_2 i) (Q2.hfix137_137_2 i) _)
      colCert_137_137_5.hD ?_).symm
  rw [alnId_137 j hj]


theorem leaf_137_137_6 (hp : 6 < (Q2.transData.getD 137 []).length)
    (j : Nat) (hj : j < (repChars.getD 137 []).length)
    (hq : (normIsRep.getD 137 []).getD j false = true) :
    species (Q2.reps (⟨137, by decide⟩ : Fin 148)) (colE2 ⟨137, by decide⟩ 6 hp)
        (rowE2 (⟨137, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨137, by decide⟩ : Fin 148))
        (colE1 ⟨137, by decide⟩ 6 (transLenTr ⟨137, by decide⟩ 6 hp))
        (rowE1 (⟨137, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨137, by decide⟩ : Fin 148) ⟨137, by decide⟩ _
      (validAt ⟨137, by decide⟩ (listedAt ⟨137, by decide⟩ hj))
      (colE1 ⟨137, by decide⟩ 6 (transLenTr ⟨137, by decide⟩ 6 hp)) T137_137
      hfix137_137 hinj137_137 hcardT137_137
      (fun i => conj_mem_of_fixedPoints _ _ (T137_137 i) (hfix137_137 i) _)
      ⟨137, by decide⟩ ⟨137, by decide⟩ _
      (Q2.validAt ⟨137, by decide⟩ (Q2.listedAt ⟨137, by decide⟩
        (alnCheck_rep ⟨137, by decide⟩ hj hq).1))
      (colE2 ⟨137, by decide⟩ 6 hp) Q2.T137_137_2 Q2.hfix137_137_2 Q2.hinj137_137_2
      Q2.hcardT137_137_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T137_137_2 i) (Q2.hfix137_137_2 i) _)
      colCert_137_137_6.hD ?_).symm
  rw [alnId_137 j hj]


theorem leaf_137_137_7 (hp : 7 < (Q2.transData.getD 137 []).length)
    (j : Nat) (hj : j < (repChars.getD 137 []).length)
    (hq : (normIsRep.getD 137 []).getD j false = true) :
    species (Q2.reps (⟨137, by decide⟩ : Fin 148)) (colE2 ⟨137, by decide⟩ 7 hp)
        (rowE2 (⟨137, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨137, by decide⟩ : Fin 148))
        (colE1 ⟨137, by decide⟩ 7 (transLenTr ⟨137, by decide⟩ 7 hp))
        (rowE1 (⟨137, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨137, by decide⟩ : Fin 148) ⟨137, by decide⟩ _
      (validAt ⟨137, by decide⟩ (listedAt ⟨137, by decide⟩ hj))
      (colE1 ⟨137, by decide⟩ 7 (transLenTr ⟨137, by decide⟩ 7 hp)) T137_137
      hfix137_137 hinj137_137 hcardT137_137
      (fun i => conj_mem_of_fixedPoints _ _ (T137_137 i) (hfix137_137 i) _)
      ⟨137, by decide⟩ ⟨137, by decide⟩ _
      (Q2.validAt ⟨137, by decide⟩ (Q2.listedAt ⟨137, by decide⟩
        (alnCheck_rep ⟨137, by decide⟩ hj hq).1))
      (colE2 ⟨137, by decide⟩ 7 hp) Q2.T137_137_2 Q2.hfix137_137_2 Q2.hinj137_137_2
      Q2.hcardT137_137_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T137_137_2 i) (Q2.hfix137_137_2 i) _)
      colCert_137_137_7.hD ?_).symm
  rw [alnId_137 j hj]


theorem leaf_137_137_8 (hp : 8 < (Q2.transData.getD 137 []).length)
    (j : Nat) (hj : j < (repChars.getD 137 []).length)
    (hq : (normIsRep.getD 137 []).getD j false = true) :
    species (Q2.reps (⟨137, by decide⟩ : Fin 148)) (colE2 ⟨137, by decide⟩ 8 hp)
        (rowE2 (⟨137, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨137, by decide⟩ : Fin 148))
        (colE1 ⟨137, by decide⟩ 8 (transLenTr ⟨137, by decide⟩ 8 hp))
        (rowE1 (⟨137, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨137, by decide⟩ : Fin 148) ⟨137, by decide⟩ _
      (validAt ⟨137, by decide⟩ (listedAt ⟨137, by decide⟩ hj))
      (colE1 ⟨137, by decide⟩ 8 (transLenTr ⟨137, by decide⟩ 8 hp)) T137_137
      hfix137_137 hinj137_137 hcardT137_137
      (fun i => conj_mem_of_fixedPoints _ _ (T137_137 i) (hfix137_137 i) _)
      ⟨137, by decide⟩ ⟨137, by decide⟩ _
      (Q2.validAt ⟨137, by decide⟩ (Q2.listedAt ⟨137, by decide⟩
        (alnCheck_rep ⟨137, by decide⟩ hj hq).1))
      (colE2 ⟨137, by decide⟩ 8 hp) Q2.T137_137_2 Q2.hfix137_137_2 Q2.hinj137_137_2
      Q2.hcardT137_137_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T137_137_2 i) (Q2.hfix137_137_2 i) _)
      colCert_137_137_8.hD ?_).symm
  rw [alnId_137 j hj]


theorem leaf_137_137_9 (hp : 9 < (Q2.transData.getD 137 []).length)
    (j : Nat) (hj : j < (repChars.getD 137 []).length)
    (hq : (normIsRep.getD 137 []).getD j false = true) :
    species (Q2.reps (⟨137, by decide⟩ : Fin 148)) (colE2 ⟨137, by decide⟩ 9 hp)
        (rowE2 (⟨137, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨137, by decide⟩ : Fin 148))
        (colE1 ⟨137, by decide⟩ 9 (transLenTr ⟨137, by decide⟩ 9 hp))
        (rowE1 (⟨137, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨137, by decide⟩ : Fin 148) ⟨137, by decide⟩ _
      (validAt ⟨137, by decide⟩ (listedAt ⟨137, by decide⟩ hj))
      (colE1 ⟨137, by decide⟩ 9 (transLenTr ⟨137, by decide⟩ 9 hp)) T137_137
      hfix137_137 hinj137_137 hcardT137_137
      (fun i => conj_mem_of_fixedPoints _ _ (T137_137 i) (hfix137_137 i) _)
      ⟨137, by decide⟩ ⟨137, by decide⟩ _
      (Q2.validAt ⟨137, by decide⟩ (Q2.listedAt ⟨137, by decide⟩
        (alnCheck_rep ⟨137, by decide⟩ hj hq).1))
      (colE2 ⟨137, by decide⟩ 9 hp) Q2.T137_137_2 Q2.hfix137_137_2 Q2.hinj137_137_2
      Q2.hcardT137_137_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T137_137_2 i) (Q2.hfix137_137_2 i) _)
      colCert_137_137_9.hD ?_).symm
  rw [alnId_137 j hj]


theorem leaf_137_137_10 (hp : 10 < (Q2.transData.getD 137 []).length)
    (j : Nat) (hj : j < (repChars.getD 137 []).length)
    (hq : (normIsRep.getD 137 []).getD j false = true) :
    species (Q2.reps (⟨137, by decide⟩ : Fin 148)) (colE2 ⟨137, by decide⟩ 10 hp)
        (rowE2 (⟨137, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨137, by decide⟩ : Fin 148))
        (colE1 ⟨137, by decide⟩ 10 (transLenTr ⟨137, by decide⟩ 10 hp))
        (rowE1 (⟨137, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨137, by decide⟩ : Fin 148) ⟨137, by decide⟩ _
      (validAt ⟨137, by decide⟩ (listedAt ⟨137, by decide⟩ hj))
      (colE1 ⟨137, by decide⟩ 10 (transLenTr ⟨137, by decide⟩ 10 hp)) T137_137
      hfix137_137 hinj137_137 hcardT137_137
      (fun i => conj_mem_of_fixedPoints _ _ (T137_137 i) (hfix137_137 i) _)
      ⟨137, by decide⟩ ⟨137, by decide⟩ _
      (Q2.validAt ⟨137, by decide⟩ (Q2.listedAt ⟨137, by decide⟩
        (alnCheck_rep ⟨137, by decide⟩ hj hq).1))
      (colE2 ⟨137, by decide⟩ 10 hp) Q2.T137_137_2 Q2.hfix137_137_2 Q2.hinj137_137_2
      Q2.hcardT137_137_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T137_137_2 i) (Q2.hfix137_137_2 i) _)
      colCert_137_137_10.hD ?_).symm
  rw [alnId_137 j hj]


theorem leaf_137_137_11 (hp : 11 < (Q2.transData.getD 137 []).length)
    (j : Nat) (hj : j < (repChars.getD 137 []).length)
    (hq : (normIsRep.getD 137 []).getD j false = true) :
    species (Q2.reps (⟨137, by decide⟩ : Fin 148)) (colE2 ⟨137, by decide⟩ 11 hp)
        (rowE2 (⟨137, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨137, by decide⟩ : Fin 148))
        (colE1 ⟨137, by decide⟩ 11 (transLenTr ⟨137, by decide⟩ 11 hp))
        (rowE1 (⟨137, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨137, by decide⟩ : Fin 148) ⟨137, by decide⟩ _
      (validAt ⟨137, by decide⟩ (listedAt ⟨137, by decide⟩ hj))
      (colE1 ⟨137, by decide⟩ 11 (transLenTr ⟨137, by decide⟩ 11 hp)) T137_137
      hfix137_137 hinj137_137 hcardT137_137
      (fun i => conj_mem_of_fixedPoints _ _ (T137_137 i) (hfix137_137 i) _)
      ⟨137, by decide⟩ ⟨137, by decide⟩ _
      (Q2.validAt ⟨137, by decide⟩ (Q2.listedAt ⟨137, by decide⟩
        (alnCheck_rep ⟨137, by decide⟩ hj hq).1))
      (colE2 ⟨137, by decide⟩ 11 hp) Q2.T137_137_2 Q2.hfix137_137_2 Q2.hinj137_137_2
      Q2.hcardT137_137_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T137_137_2 i) (Q2.hfix137_137_2 i) _)
      colCert_137_137_11.hD ?_).symm
  rw [alnId_137 j hj]


theorem leaf_137_137_12 (hp : 12 < (Q2.transData.getD 137 []).length)
    (j : Nat) (hj : j < (repChars.getD 137 []).length)
    (hq : (normIsRep.getD 137 []).getD j false = true) :
    species (Q2.reps (⟨137, by decide⟩ : Fin 148)) (colE2 ⟨137, by decide⟩ 12 hp)
        (rowE2 (⟨137, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨137, by decide⟩ : Fin 148))
        (colE1 ⟨137, by decide⟩ 12 (transLenTr ⟨137, by decide⟩ 12 hp))
        (rowE1 (⟨137, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨137, by decide⟩ : Fin 148) ⟨137, by decide⟩ _
      (validAt ⟨137, by decide⟩ (listedAt ⟨137, by decide⟩ hj))
      (colE1 ⟨137, by decide⟩ 12 (transLenTr ⟨137, by decide⟩ 12 hp)) T137_137
      hfix137_137 hinj137_137 hcardT137_137
      (fun i => conj_mem_of_fixedPoints _ _ (T137_137 i) (hfix137_137 i) _)
      ⟨137, by decide⟩ ⟨137, by decide⟩ _
      (Q2.validAt ⟨137, by decide⟩ (Q2.listedAt ⟨137, by decide⟩
        (alnCheck_rep ⟨137, by decide⟩ hj hq).1))
      (colE2 ⟨137, by decide⟩ 12 hp) Q2.T137_137_2 Q2.hfix137_137_2 Q2.hinj137_137_2
      Q2.hcardT137_137_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T137_137_2 i) (Q2.hfix137_137_2 i) _)
      colCert_137_137_12.hD ?_).symm
  rw [alnId_137 j hj]


theorem leaf_137_137_13 (hp : 13 < (Q2.transData.getD 137 []).length)
    (j : Nat) (hj : j < (repChars.getD 137 []).length)
    (hq : (normIsRep.getD 137 []).getD j false = true) :
    species (Q2.reps (⟨137, by decide⟩ : Fin 148)) (colE2 ⟨137, by decide⟩ 13 hp)
        (rowE2 (⟨137, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨137, by decide⟩ : Fin 148))
        (colE1 ⟨137, by decide⟩ 13 (transLenTr ⟨137, by decide⟩ 13 hp))
        (rowE1 (⟨137, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨137, by decide⟩ : Fin 148) ⟨137, by decide⟩ _
      (validAt ⟨137, by decide⟩ (listedAt ⟨137, by decide⟩ hj))
      (colE1 ⟨137, by decide⟩ 13 (transLenTr ⟨137, by decide⟩ 13 hp)) T137_137
      hfix137_137 hinj137_137 hcardT137_137
      (fun i => conj_mem_of_fixedPoints _ _ (T137_137 i) (hfix137_137 i) _)
      ⟨137, by decide⟩ ⟨137, by decide⟩ _
      (Q2.validAt ⟨137, by decide⟩ (Q2.listedAt ⟨137, by decide⟩
        (alnCheck_rep ⟨137, by decide⟩ hj hq).1))
      (colE2 ⟨137, by decide⟩ 13 hp) Q2.T137_137_2 Q2.hfix137_137_2 Q2.hinj137_137_2
      Q2.hcardT137_137_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T137_137_2 i) (Q2.hfix137_137_2 i) _)
      colCert_137_137_13.hD ?_).symm
  rw [alnId_137 j hj]


theorem leaf_137_137_14 (hp : 14 < (Q2.transData.getD 137 []).length)
    (j : Nat) (hj : j < (repChars.getD 137 []).length)
    (hq : (normIsRep.getD 137 []).getD j false = true) :
    species (Q2.reps (⟨137, by decide⟩ : Fin 148)) (colE2 ⟨137, by decide⟩ 14 hp)
        (rowE2 (⟨137, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨137, by decide⟩ : Fin 148))
        (colE1 ⟨137, by decide⟩ 14 (transLenTr ⟨137, by decide⟩ 14 hp))
        (rowE1 (⟨137, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨137, by decide⟩ : Fin 148) ⟨137, by decide⟩ _
      (validAt ⟨137, by decide⟩ (listedAt ⟨137, by decide⟩ hj))
      (colE1 ⟨137, by decide⟩ 14 (transLenTr ⟨137, by decide⟩ 14 hp)) T137_137
      hfix137_137 hinj137_137 hcardT137_137
      (fun i => conj_mem_of_fixedPoints _ _ (T137_137 i) (hfix137_137 i) _)
      ⟨137, by decide⟩ ⟨137, by decide⟩ _
      (Q2.validAt ⟨137, by decide⟩ (Q2.listedAt ⟨137, by decide⟩
        (alnCheck_rep ⟨137, by decide⟩ hj hq).1))
      (colE2 ⟨137, by decide⟩ 14 hp) Q2.T137_137_2 Q2.hfix137_137_2 Q2.hinj137_137_2
      Q2.hcardT137_137_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T137_137_2 i) (Q2.hfix137_137_2 i) _)
      colCert_137_137_14.hD ?_).symm
  rw [alnId_137 j hj]


theorem leaf_137_137_15 (hp : 15 < (Q2.transData.getD 137 []).length)
    (j : Nat) (hj : j < (repChars.getD 137 []).length)
    (hq : (normIsRep.getD 137 []).getD j false = true) :
    species (Q2.reps (⟨137, by decide⟩ : Fin 148)) (colE2 ⟨137, by decide⟩ 15 hp)
        (rowE2 (⟨137, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨137, by decide⟩ : Fin 148))
        (colE1 ⟨137, by decide⟩ 15 (transLenTr ⟨137, by decide⟩ 15 hp))
        (rowE1 (⟨137, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨137, by decide⟩ : Fin 148) ⟨137, by decide⟩ _
      (validAt ⟨137, by decide⟩ (listedAt ⟨137, by decide⟩ hj))
      (colE1 ⟨137, by decide⟩ 15 (transLenTr ⟨137, by decide⟩ 15 hp)) T137_137
      hfix137_137 hinj137_137 hcardT137_137
      (fun i => conj_mem_of_fixedPoints _ _ (T137_137 i) (hfix137_137 i) _)
      ⟨137, by decide⟩ ⟨137, by decide⟩ _
      (Q2.validAt ⟨137, by decide⟩ (Q2.listedAt ⟨137, by decide⟩
        (alnCheck_rep ⟨137, by decide⟩ hj hq).1))
      (colE2 ⟨137, by decide⟩ 15 hp) Q2.T137_137_2 Q2.hfix137_137_2 Q2.hinj137_137_2
      Q2.hcardT137_137_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T137_137_2 i) (Q2.hfix137_137_2 i) _)
      colCert_137_137_15.hD ?_).symm
  rw [alnId_137 j hj]


theorem leaf_137_137_16 (hp : 16 < (Q2.transData.getD 137 []).length)
    (j : Nat) (hj : j < (repChars.getD 137 []).length)
    (hq : (normIsRep.getD 137 []).getD j false = true) :
    species (Q2.reps (⟨137, by decide⟩ : Fin 148)) (colE2 ⟨137, by decide⟩ 16 hp)
        (rowE2 (⟨137, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨137, by decide⟩ : Fin 148))
        (colE1 ⟨137, by decide⟩ 16 (transLenTr ⟨137, by decide⟩ 16 hp))
        (rowE1 (⟨137, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨137, by decide⟩ : Fin 148) ⟨137, by decide⟩ _
      (validAt ⟨137, by decide⟩ (listedAt ⟨137, by decide⟩ hj))
      (colE1 ⟨137, by decide⟩ 16 (transLenTr ⟨137, by decide⟩ 16 hp)) T137_137
      hfix137_137 hinj137_137 hcardT137_137
      (fun i => conj_mem_of_fixedPoints _ _ (T137_137 i) (hfix137_137 i) _)
      ⟨137, by decide⟩ ⟨137, by decide⟩ _
      (Q2.validAt ⟨137, by decide⟩ (Q2.listedAt ⟨137, by decide⟩
        (alnCheck_rep ⟨137, by decide⟩ hj hq).1))
      (colE2 ⟨137, by decide⟩ 16 hp) Q2.T137_137_2 Q2.hfix137_137_2 Q2.hinj137_137_2
      Q2.hcardT137_137_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T137_137_2 i) (Q2.hfix137_137_2 i) _)
      colCert_137_137_16.hD ?_).symm
  rw [alnId_137 j hj]


theorem leaf_137_137_17 (hp : 17 < (Q2.transData.getD 137 []).length)
    (j : Nat) (hj : j < (repChars.getD 137 []).length)
    (hq : (normIsRep.getD 137 []).getD j false = true) :
    species (Q2.reps (⟨137, by decide⟩ : Fin 148)) (colE2 ⟨137, by decide⟩ 17 hp)
        (rowE2 (⟨137, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨137, by decide⟩ : Fin 148))
        (colE1 ⟨137, by decide⟩ 17 (transLenTr ⟨137, by decide⟩ 17 hp))
        (rowE1 (⟨137, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨137, by decide⟩ : Fin 148) ⟨137, by decide⟩ _
      (validAt ⟨137, by decide⟩ (listedAt ⟨137, by decide⟩ hj))
      (colE1 ⟨137, by decide⟩ 17 (transLenTr ⟨137, by decide⟩ 17 hp)) T137_137
      hfix137_137 hinj137_137 hcardT137_137
      (fun i => conj_mem_of_fixedPoints _ _ (T137_137 i) (hfix137_137 i) _)
      ⟨137, by decide⟩ ⟨137, by decide⟩ _
      (Q2.validAt ⟨137, by decide⟩ (Q2.listedAt ⟨137, by decide⟩
        (alnCheck_rep ⟨137, by decide⟩ hj hq).1))
      (colE2 ⟨137, by decide⟩ 17 hp) Q2.T137_137_2 Q2.hfix137_137_2 Q2.hinj137_137_2
      Q2.hcardT137_137_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T137_137_2 i) (Q2.hfix137_137_2 i) _)
      colCert_137_137_17.hD ?_).symm
  rw [alnId_137 j hj]


theorem leaf_137_137_18 (hp : 18 < (Q2.transData.getD 137 []).length)
    (j : Nat) (hj : j < (repChars.getD 137 []).length)
    (hq : (normIsRep.getD 137 []).getD j false = true) :
    species (Q2.reps (⟨137, by decide⟩ : Fin 148)) (colE2 ⟨137, by decide⟩ 18 hp)
        (rowE2 (⟨137, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨137, by decide⟩ : Fin 148))
        (colE1 ⟨137, by decide⟩ 18 (transLenTr ⟨137, by decide⟩ 18 hp))
        (rowE1 (⟨137, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨137, by decide⟩ : Fin 148) ⟨137, by decide⟩ _
      (validAt ⟨137, by decide⟩ (listedAt ⟨137, by decide⟩ hj))
      (colE1 ⟨137, by decide⟩ 18 (transLenTr ⟨137, by decide⟩ 18 hp)) T137_137
      hfix137_137 hinj137_137 hcardT137_137
      (fun i => conj_mem_of_fixedPoints _ _ (T137_137 i) (hfix137_137 i) _)
      ⟨137, by decide⟩ ⟨137, by decide⟩ _
      (Q2.validAt ⟨137, by decide⟩ (Q2.listedAt ⟨137, by decide⟩
        (alnCheck_rep ⟨137, by decide⟩ hj hq).1))
      (colE2 ⟨137, by decide⟩ 18 hp) Q2.T137_137_2 Q2.hfix137_137_2 Q2.hinj137_137_2
      Q2.hcardT137_137_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T137_137_2 i) (Q2.hfix137_137_2 i) _)
      colCert_137_137_18.hD ?_).symm
  rw [alnId_137 j hj]


theorem leaf_137_137_19 (hp : 19 < (Q2.transData.getD 137 []).length)
    (j : Nat) (hj : j < (repChars.getD 137 []).length)
    (hq : (normIsRep.getD 137 []).getD j false = true) :
    species (Q2.reps (⟨137, by decide⟩ : Fin 148)) (colE2 ⟨137, by decide⟩ 19 hp)
        (rowE2 (⟨137, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨137, by decide⟩ : Fin 148))
        (colE1 ⟨137, by decide⟩ 19 (transLenTr ⟨137, by decide⟩ 19 hp))
        (rowE1 (⟨137, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨137, by decide⟩ : Fin 148) ⟨137, by decide⟩ _
      (validAt ⟨137, by decide⟩ (listedAt ⟨137, by decide⟩ hj))
      (colE1 ⟨137, by decide⟩ 19 (transLenTr ⟨137, by decide⟩ 19 hp)) T137_137
      hfix137_137 hinj137_137 hcardT137_137
      (fun i => conj_mem_of_fixedPoints _ _ (T137_137 i) (hfix137_137 i) _)
      ⟨137, by decide⟩ ⟨137, by decide⟩ _
      (Q2.validAt ⟨137, by decide⟩ (Q2.listedAt ⟨137, by decide⟩
        (alnCheck_rep ⟨137, by decide⟩ hj hq).1))
      (colE2 ⟨137, by decide⟩ 19 hp) Q2.T137_137_2 Q2.hfix137_137_2 Q2.hinj137_137_2
      Q2.hcardT137_137_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T137_137_2 i) (Q2.hfix137_137_2 i) _)
      colCert_137_137_19.hD ?_).symm
  rw [alnId_137 j hj]


theorem leaf_137_137_20 (hp : 20 < (Q2.transData.getD 137 []).length)
    (j : Nat) (hj : j < (repChars.getD 137 []).length)
    (hq : (normIsRep.getD 137 []).getD j false = true) :
    species (Q2.reps (⟨137, by decide⟩ : Fin 148)) (colE2 ⟨137, by decide⟩ 20 hp)
        (rowE2 (⟨137, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨137, by decide⟩ : Fin 148))
        (colE1 ⟨137, by decide⟩ 20 (transLenTr ⟨137, by decide⟩ 20 hp))
        (rowE1 (⟨137, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨137, by decide⟩ : Fin 148) ⟨137, by decide⟩ _
      (validAt ⟨137, by decide⟩ (listedAt ⟨137, by decide⟩ hj))
      (colE1 ⟨137, by decide⟩ 20 (transLenTr ⟨137, by decide⟩ 20 hp)) T137_137
      hfix137_137 hinj137_137 hcardT137_137
      (fun i => conj_mem_of_fixedPoints _ _ (T137_137 i) (hfix137_137 i) _)
      ⟨137, by decide⟩ ⟨137, by decide⟩ _
      (Q2.validAt ⟨137, by decide⟩ (Q2.listedAt ⟨137, by decide⟩
        (alnCheck_rep ⟨137, by decide⟩ hj hq).1))
      (colE2 ⟨137, by decide⟩ 20 hp) Q2.T137_137_2 Q2.hfix137_137_2 Q2.hinj137_137_2
      Q2.hcardT137_137_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T137_137_2 i) (Q2.hfix137_137_2 i) _)
      colCert_137_137_20.hD ?_).symm
  rw [alnId_137 j hj]


theorem leaf_137_137_21 (hp : 21 < (Q2.transData.getD 137 []).length)
    (j : Nat) (hj : j < (repChars.getD 137 []).length)
    (hq : (normIsRep.getD 137 []).getD j false = true) :
    species (Q2.reps (⟨137, by decide⟩ : Fin 148)) (colE2 ⟨137, by decide⟩ 21 hp)
        (rowE2 (⟨137, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨137, by decide⟩ : Fin 148))
        (colE1 ⟨137, by decide⟩ 21 (transLenTr ⟨137, by decide⟩ 21 hp))
        (rowE1 (⟨137, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨137, by decide⟩ : Fin 148) ⟨137, by decide⟩ _
      (validAt ⟨137, by decide⟩ (listedAt ⟨137, by decide⟩ hj))
      (colE1 ⟨137, by decide⟩ 21 (transLenTr ⟨137, by decide⟩ 21 hp)) T137_137
      hfix137_137 hinj137_137 hcardT137_137
      (fun i => conj_mem_of_fixedPoints _ _ (T137_137 i) (hfix137_137 i) _)
      ⟨137, by decide⟩ ⟨137, by decide⟩ _
      (Q2.validAt ⟨137, by decide⟩ (Q2.listedAt ⟨137, by decide⟩
        (alnCheck_rep ⟨137, by decide⟩ hj hq).1))
      (colE2 ⟨137, by decide⟩ 21 hp) Q2.T137_137_2 Q2.hfix137_137_2 Q2.hinj137_137_2
      Q2.hcardT137_137_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T137_137_2 i) (Q2.hfix137_137_2 i) _)
      colCert_137_137_21.hD ?_).symm
  rw [alnId_137 j hj]


theorem leaf_137_137_22 (hp : 22 < (Q2.transData.getD 137 []).length)
    (j : Nat) (hj : j < (repChars.getD 137 []).length)
    (hq : (normIsRep.getD 137 []).getD j false = true) :
    species (Q2.reps (⟨137, by decide⟩ : Fin 148)) (colE2 ⟨137, by decide⟩ 22 hp)
        (rowE2 (⟨137, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨137, by decide⟩ : Fin 148))
        (colE1 ⟨137, by decide⟩ 22 (transLenTr ⟨137, by decide⟩ 22 hp))
        (rowE1 (⟨137, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨137, by decide⟩ : Fin 148) ⟨137, by decide⟩ _
      (validAt ⟨137, by decide⟩ (listedAt ⟨137, by decide⟩ hj))
      (colE1 ⟨137, by decide⟩ 22 (transLenTr ⟨137, by decide⟩ 22 hp)) T137_137
      hfix137_137 hinj137_137 hcardT137_137
      (fun i => conj_mem_of_fixedPoints _ _ (T137_137 i) (hfix137_137 i) _)
      ⟨137, by decide⟩ ⟨137, by decide⟩ _
      (Q2.validAt ⟨137, by decide⟩ (Q2.listedAt ⟨137, by decide⟩
        (alnCheck_rep ⟨137, by decide⟩ hj hq).1))
      (colE2 ⟨137, by decide⟩ 22 hp) Q2.T137_137_2 Q2.hfix137_137_2 Q2.hinj137_137_2
      Q2.hcardT137_137_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T137_137_2 i) (Q2.hfix137_137_2 i) _)
      colCert_137_137_22.hD ?_).symm
  rw [alnId_137 j hj]


theorem leaf_137_137_23 (hp : 23 < (Q2.transData.getD 137 []).length)
    (j : Nat) (hj : j < (repChars.getD 137 []).length)
    (hq : (normIsRep.getD 137 []).getD j false = true) :
    species (Q2.reps (⟨137, by decide⟩ : Fin 148)) (colE2 ⟨137, by decide⟩ 23 hp)
        (rowE2 (⟨137, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨137, by decide⟩ : Fin 148))
        (colE1 ⟨137, by decide⟩ 23 (transLenTr ⟨137, by decide⟩ 23 hp))
        (rowE1 (⟨137, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨137, by decide⟩ : Fin 148) ⟨137, by decide⟩ _
      (validAt ⟨137, by decide⟩ (listedAt ⟨137, by decide⟩ hj))
      (colE1 ⟨137, by decide⟩ 23 (transLenTr ⟨137, by decide⟩ 23 hp)) T137_137
      hfix137_137 hinj137_137 hcardT137_137
      (fun i => conj_mem_of_fixedPoints _ _ (T137_137 i) (hfix137_137 i) _)
      ⟨137, by decide⟩ ⟨137, by decide⟩ _
      (Q2.validAt ⟨137, by decide⟩ (Q2.listedAt ⟨137, by decide⟩
        (alnCheck_rep ⟨137, by decide⟩ hj hq).1))
      (colE2 ⟨137, by decide⟩ 23 hp) Q2.T137_137_2 Q2.hfix137_137_2 Q2.hinj137_137_2
      Q2.hcardT137_137_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T137_137_2 i) (Q2.hfix137_137_2 i) _)
      colCert_137_137_23.hD ?_).symm
  rw [alnId_137 j hj]


theorem leaf_137_137_24 (hp : 24 < (Q2.transData.getD 137 []).length)
    (j : Nat) (hj : j < (repChars.getD 137 []).length)
    (hq : (normIsRep.getD 137 []).getD j false = true) :
    species (Q2.reps (⟨137, by decide⟩ : Fin 148)) (colE2 ⟨137, by decide⟩ 24 hp)
        (rowE2 (⟨137, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨137, by decide⟩ : Fin 148))
        (colE1 ⟨137, by decide⟩ 24 (transLenTr ⟨137, by decide⟩ 24 hp))
        (rowE1 (⟨137, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨137, by decide⟩ : Fin 148) ⟨137, by decide⟩ _
      (validAt ⟨137, by decide⟩ (listedAt ⟨137, by decide⟩ hj))
      (colE1 ⟨137, by decide⟩ 24 (transLenTr ⟨137, by decide⟩ 24 hp)) T137_137
      hfix137_137 hinj137_137 hcardT137_137
      (fun i => conj_mem_of_fixedPoints _ _ (T137_137 i) (hfix137_137 i) _)
      ⟨137, by decide⟩ ⟨137, by decide⟩ _
      (Q2.validAt ⟨137, by decide⟩ (Q2.listedAt ⟨137, by decide⟩
        (alnCheck_rep ⟨137, by decide⟩ hj hq).1))
      (colE2 ⟨137, by decide⟩ 24 hp) Q2.T137_137_2 Q2.hfix137_137_2 Q2.hinj137_137_2
      Q2.hcardT137_137_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T137_137_2 i) (Q2.hfix137_137_2 i) _)
      colCert_137_137_24.hD ?_).symm
  rw [alnId_137 j hj]


theorem leaf_138_5_0 (hp : 0 < (Q2.transData.getD 5 []).length)
    (j : Nat) (hj : j < (repChars.getD 138 []).length)
    (hq : (normIsRep.getD 138 []).getD j false = true) :
    species (Q2.reps (⟨5, by decide⟩ : Fin 148)) (colE2 ⟨5, by decide⟩ 0 hp)
        (rowE2 (⟨138, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨5, by decide⟩ : Fin 148))
        (colE1 ⟨5, by decide⟩ 0 (transLenTr ⟨5, by decide⟩ 0 hp))
        (rowE1 (⟨138, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨138, by decide⟩ : Fin 148) ⟨5, by decide⟩ _
      (validAt ⟨138, by decide⟩ (listedAt ⟨138, by decide⟩ hj))
      (colE1 ⟨5, by decide⟩ 0 (transLenTr ⟨5, by decide⟩ 0 hp)) T138_5
      hfix138_5 hinj138_5 hcardT138_5
      (fun i => conj_mem_of_fixedPoints _ _ (T138_5 i) (hfix138_5 i) _)
      ⟨138, by decide⟩ ⟨5, by decide⟩ _
      (Q2.validAt ⟨138, by decide⟩ (Q2.listedAt ⟨138, by decide⟩
        (alnCheck_rep ⟨138, by decide⟩ hj hq).1))
      (colE2 ⟨5, by decide⟩ 0 hp) Q2.T138_5_2 Q2.hfix138_5_2 Q2.hinj138_5_2
      Q2.hcardT138_5_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T138_5_2 i) (Q2.hfix138_5_2 i) _)
      colCert_138_5_0.hD ?_).symm
  rw [alnId_138 j hj]


theorem leaf_138_5_1 (hp : 1 < (Q2.transData.getD 5 []).length)
    (j : Nat) (hj : j < (repChars.getD 138 []).length)
    (hq : (normIsRep.getD 138 []).getD j false = true) :
    species (Q2.reps (⟨5, by decide⟩ : Fin 148)) (colE2 ⟨5, by decide⟩ 1 hp)
        (rowE2 (⟨138, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨5, by decide⟩ : Fin 148))
        (colE1 ⟨5, by decide⟩ 1 (transLenTr ⟨5, by decide⟩ 1 hp))
        (rowE1 (⟨138, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨138, by decide⟩ : Fin 148) ⟨5, by decide⟩ _
      (validAt ⟨138, by decide⟩ (listedAt ⟨138, by decide⟩ hj))
      (colE1 ⟨5, by decide⟩ 1 (transLenTr ⟨5, by decide⟩ 1 hp)) T138_5
      hfix138_5 hinj138_5 hcardT138_5
      (fun i => conj_mem_of_fixedPoints _ _ (T138_5 i) (hfix138_5 i) _)
      ⟨138, by decide⟩ ⟨5, by decide⟩ _
      (Q2.validAt ⟨138, by decide⟩ (Q2.listedAt ⟨138, by decide⟩
        (alnCheck_rep ⟨138, by decide⟩ hj hq).1))
      (colE2 ⟨5, by decide⟩ 1 hp) Q2.T138_5_2 Q2.hfix138_5_2 Q2.hinj138_5_2
      Q2.hcardT138_5_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T138_5_2 i) (Q2.hfix138_5_2 i) _)
      ?_).symm
  rw [show colData1 (⟨138, by decide⟩ : Fin 148)
        ((colE1 ⟨5, by decide⟩ 1 (transLenTr ⟨5, by decide⟩ 1 hp) : ↥(reps ⟨5, by decide⟩)) : Coordinate 1)
        T138_5 = colFn colCertDiv_138_5_1.D1 (m := 5) from colCertDiv_138_5_1.bind1,
    show colData2 (⟨138, by decide⟩ : Fin 148)
        ((colE2 ⟨5, by decide⟩ 1 hp : ↥(Q2.reps ⟨5, by decide⟩)) : Coordinate 2)
        Q2.T138_5_2 = colFn colCertDiv_138_5_1.D2 (m := 5) from colCertDiv_138_5_1.bind2]
  rw [alnId_138 j hj]
  exact fastcode_of_div ⟨138, by decide⟩ _ _ _
    ((alnId_138 j hj) ▸ Q2.listedAt (⟨138, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨138, by decide⟩ : Fin 148) hj hq).1) colCertDiv_138_5_1_match


theorem leaf_138_5_2 (hp : 2 < (Q2.transData.getD 5 []).length)
    (j : Nat) (hj : j < (repChars.getD 138 []).length)
    (hq : (normIsRep.getD 138 []).getD j false = true) :
    species (Q2.reps (⟨5, by decide⟩ : Fin 148)) (colE2 ⟨5, by decide⟩ 2 hp)
        (rowE2 (⟨138, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨5, by decide⟩ : Fin 148))
        (colE1 ⟨5, by decide⟩ 2 (transLenTr ⟨5, by decide⟩ 2 hp))
        (rowE1 (⟨138, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨138, by decide⟩ : Fin 148) ⟨5, by decide⟩ _
      (validAt ⟨138, by decide⟩ (listedAt ⟨138, by decide⟩ hj))
      (colE1 ⟨5, by decide⟩ 2 (transLenTr ⟨5, by decide⟩ 2 hp)) T138_5
      hfix138_5 hinj138_5 hcardT138_5
      (fun i => conj_mem_of_fixedPoints _ _ (T138_5 i) (hfix138_5 i) _)
      ⟨138, by decide⟩ ⟨5, by decide⟩ _
      (Q2.validAt ⟨138, by decide⟩ (Q2.listedAt ⟨138, by decide⟩
        (alnCheck_rep ⟨138, by decide⟩ hj hq).1))
      (colE2 ⟨5, by decide⟩ 2 hp) Q2.T138_5_2 Q2.hfix138_5_2 Q2.hinj138_5_2
      Q2.hcardT138_5_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T138_5_2 i) (Q2.hfix138_5_2 i) _)
      ?_).symm
  rw [show colData1 (⟨138, by decide⟩ : Fin 148)
        ((colE1 ⟨5, by decide⟩ 2 (transLenTr ⟨5, by decide⟩ 2 hp) : ↥(reps ⟨5, by decide⟩)) : Coordinate 1)
        T138_5 = colFn colCertDiv_138_5_2.D1 (m := 5) from colCertDiv_138_5_2.bind1,
    show colData2 (⟨138, by decide⟩ : Fin 148)
        ((colE2 ⟨5, by decide⟩ 2 hp : ↥(Q2.reps ⟨5, by decide⟩)) : Coordinate 2)
        Q2.T138_5_2 = colFn colCertDiv_138_5_2.D2 (m := 5) from colCertDiv_138_5_2.bind2]
  rw [alnId_138 j hj]
  exact fastcode_of_div ⟨138, by decide⟩ _ _ _
    ((alnId_138 j hj) ▸ Q2.listedAt (⟨138, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨138, by decide⟩ : Fin 148) hj hq).1) colCertDiv_138_5_2_match


theorem leaf_138_5_3 (hp : 3 < (Q2.transData.getD 5 []).length)
    (j : Nat) (hj : j < (repChars.getD 138 []).length)
    (hq : (normIsRep.getD 138 []).getD j false = true) :
    species (Q2.reps (⟨5, by decide⟩ : Fin 148)) (colE2 ⟨5, by decide⟩ 3 hp)
        (rowE2 (⟨138, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨5, by decide⟩ : Fin 148))
        (colE1 ⟨5, by decide⟩ 3 (transLenTr ⟨5, by decide⟩ 3 hp))
        (rowE1 (⟨138, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨138, by decide⟩ : Fin 148) ⟨5, by decide⟩ _
      (validAt ⟨138, by decide⟩ (listedAt ⟨138, by decide⟩ hj))
      (colE1 ⟨5, by decide⟩ 3 (transLenTr ⟨5, by decide⟩ 3 hp)) T138_5
      hfix138_5 hinj138_5 hcardT138_5
      (fun i => conj_mem_of_fixedPoints _ _ (T138_5 i) (hfix138_5 i) _)
      ⟨138, by decide⟩ ⟨5, by decide⟩ _
      (Q2.validAt ⟨138, by decide⟩ (Q2.listedAt ⟨138, by decide⟩
        (alnCheck_rep ⟨138, by decide⟩ hj hq).1))
      (colE2 ⟨5, by decide⟩ 3 hp) Q2.T138_5_2 Q2.hfix138_5_2 Q2.hinj138_5_2
      Q2.hcardT138_5_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T138_5_2 i) (Q2.hfix138_5_2 i) _)
      ?_).symm
  rw [show colData1 (⟨138, by decide⟩ : Fin 148)
        ((colE1 ⟨5, by decide⟩ 3 (transLenTr ⟨5, by decide⟩ 3 hp) : ↥(reps ⟨5, by decide⟩)) : Coordinate 1)
        T138_5 = colFn colCertDiv_138_5_3.D1 (m := 5) from colCertDiv_138_5_3.bind1,
    show colData2 (⟨138, by decide⟩ : Fin 148)
        ((colE2 ⟨5, by decide⟩ 3 hp : ↥(Q2.reps ⟨5, by decide⟩)) : Coordinate 2)
        Q2.T138_5_2 = colFn colCertDiv_138_5_3.D2 (m := 5) from colCertDiv_138_5_3.bind2]
  rw [alnId_138 j hj]
  exact fastcode_of_div ⟨138, by decide⟩ _ _ _
    ((alnId_138 j hj) ▸ Q2.listedAt (⟨138, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨138, by decide⟩ : Fin 148) hj hq).1) colCertDiv_138_5_3_match


theorem leaf_138_5_4 (hp : 4 < (Q2.transData.getD 5 []).length)
    (j : Nat) (hj : j < (repChars.getD 138 []).length)
    (hq : (normIsRep.getD 138 []).getD j false = true) :
    species (Q2.reps (⟨5, by decide⟩ : Fin 148)) (colE2 ⟨5, by decide⟩ 4 hp)
        (rowE2 (⟨138, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨5, by decide⟩ : Fin 148))
        (colE1 ⟨5, by decide⟩ 4 (transLenTr ⟨5, by decide⟩ 4 hp))
        (rowE1 (⟨138, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨138, by decide⟩ : Fin 148) ⟨5, by decide⟩ _
      (validAt ⟨138, by decide⟩ (listedAt ⟨138, by decide⟩ hj))
      (colE1 ⟨5, by decide⟩ 4 (transLenTr ⟨5, by decide⟩ 4 hp)) T138_5
      hfix138_5 hinj138_5 hcardT138_5
      (fun i => conj_mem_of_fixedPoints _ _ (T138_5 i) (hfix138_5 i) _)
      ⟨138, by decide⟩ ⟨5, by decide⟩ _
      (Q2.validAt ⟨138, by decide⟩ (Q2.listedAt ⟨138, by decide⟩
        (alnCheck_rep ⟨138, by decide⟩ hj hq).1))
      (colE2 ⟨5, by decide⟩ 4 hp) Q2.T138_5_2 Q2.hfix138_5_2 Q2.hinj138_5_2
      Q2.hcardT138_5_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T138_5_2 i) (Q2.hfix138_5_2 i) _)
      ?_).symm
  rw [show colData1 (⟨138, by decide⟩ : Fin 148)
        ((colE1 ⟨5, by decide⟩ 4 (transLenTr ⟨5, by decide⟩ 4 hp) : ↥(reps ⟨5, by decide⟩)) : Coordinate 1)
        T138_5 = colFn colCertDiv_138_5_4.D1 (m := 5) from colCertDiv_138_5_4.bind1,
    show colData2 (⟨138, by decide⟩ : Fin 148)
        ((colE2 ⟨5, by decide⟩ 4 hp : ↥(Q2.reps ⟨5, by decide⟩)) : Coordinate 2)
        Q2.T138_5_2 = colFn colCertDiv_138_5_4.D2 (m := 5) from colCertDiv_138_5_4.bind2]
  rw [alnId_138 j hj]
  exact fastcode_of_div ⟨138, by decide⟩ _ _ _
    ((alnId_138 j hj) ▸ Q2.listedAt (⟨138, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨138, by decide⟩ : Fin 148) hj hq).1) colCertDiv_138_5_4_match


theorem leaf_138_10_0 (hp : 0 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 138 []).length)
    (hq : (normIsRep.getD 138 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 0 hp)
        (rowE2 (⟨138, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 0 (transLenTr ⟨10, by decide⟩ 0 hp))
        (rowE1 (⟨138, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨138, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨138, by decide⟩ (listedAt ⟨138, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 0 (transLenTr ⟨10, by decide⟩ 0 hp)) T138_10
      hfix138_10 hinj138_10 hcardT138_10
      (fun i => conj_mem_of_fixedPoints _ _ (T138_10 i) (hfix138_10 i) _)
      ⟨138, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨138, by decide⟩ (Q2.listedAt ⟨138, by decide⟩
        (alnCheck_rep ⟨138, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 0 hp) Q2.T138_10_2 Q2.hfix138_10_2 Q2.hinj138_10_2
      Q2.hcardT138_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T138_10_2 i) (Q2.hfix138_10_2 i) _)
      colCert_138_10_0.hD ?_).symm
  rw [alnId_138 j hj]


theorem leaf_138_10_1 (hp : 1 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 138 []).length)
    (hq : (normIsRep.getD 138 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 1 hp)
        (rowE2 (⟨138, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 1 (transLenTr ⟨10, by decide⟩ 1 hp))
        (rowE1 (⟨138, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨138, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨138, by decide⟩ (listedAt ⟨138, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 1 (transLenTr ⟨10, by decide⟩ 1 hp)) T138_10
      hfix138_10 hinj138_10 hcardT138_10
      (fun i => conj_mem_of_fixedPoints _ _ (T138_10 i) (hfix138_10 i) _)
      ⟨138, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨138, by decide⟩ (Q2.listedAt ⟨138, by decide⟩
        (alnCheck_rep ⟨138, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 1 hp) Q2.T138_10_2 Q2.hfix138_10_2 Q2.hinj138_10_2
      Q2.hcardT138_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T138_10_2 i) (Q2.hfix138_10_2 i) _)
      colCert_138_10_1.hD ?_).symm
  rw [alnId_138 j hj]


theorem leaf_138_10_2 (hp : 2 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 138 []).length)
    (hq : (normIsRep.getD 138 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 2 hp)
        (rowE2 (⟨138, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 2 (transLenTr ⟨10, by decide⟩ 2 hp))
        (rowE1 (⟨138, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨138, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨138, by decide⟩ (listedAt ⟨138, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 2 (transLenTr ⟨10, by decide⟩ 2 hp)) T138_10
      hfix138_10 hinj138_10 hcardT138_10
      (fun i => conj_mem_of_fixedPoints _ _ (T138_10 i) (hfix138_10 i) _)
      ⟨138, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨138, by decide⟩ (Q2.listedAt ⟨138, by decide⟩
        (alnCheck_rep ⟨138, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 2 hp) Q2.T138_10_2 Q2.hfix138_10_2 Q2.hinj138_10_2
      Q2.hcardT138_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T138_10_2 i) (Q2.hfix138_10_2 i) _)
      colCert_138_10_2.hD ?_).symm
  rw [alnId_138 j hj]


theorem leaf_138_10_3 (hp : 3 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 138 []).length)
    (hq : (normIsRep.getD 138 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 3 hp)
        (rowE2 (⟨138, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 3 (transLenTr ⟨10, by decide⟩ 3 hp))
        (rowE1 (⟨138, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨138, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨138, by decide⟩ (listedAt ⟨138, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 3 (transLenTr ⟨10, by decide⟩ 3 hp)) T138_10
      hfix138_10 hinj138_10 hcardT138_10
      (fun i => conj_mem_of_fixedPoints _ _ (T138_10 i) (hfix138_10 i) _)
      ⟨138, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨138, by decide⟩ (Q2.listedAt ⟨138, by decide⟩
        (alnCheck_rep ⟨138, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 3 hp) Q2.T138_10_2 Q2.hfix138_10_2 Q2.hinj138_10_2
      Q2.hcardT138_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T138_10_2 i) (Q2.hfix138_10_2 i) _)
      colCert_138_10_3.hD ?_).symm
  rw [alnId_138 j hj]


theorem leaf_138_10_4 (hp : 4 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 138 []).length)
    (hq : (normIsRep.getD 138 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 4 hp)
        (rowE2 (⟨138, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 4 (transLenTr ⟨10, by decide⟩ 4 hp))
        (rowE1 (⟨138, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨138, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨138, by decide⟩ (listedAt ⟨138, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 4 (transLenTr ⟨10, by decide⟩ 4 hp)) T138_10
      hfix138_10 hinj138_10 hcardT138_10
      (fun i => conj_mem_of_fixedPoints _ _ (T138_10 i) (hfix138_10 i) _)
      ⟨138, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨138, by decide⟩ (Q2.listedAt ⟨138, by decide⟩
        (alnCheck_rep ⟨138, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 4 hp) Q2.T138_10_2 Q2.hfix138_10_2 Q2.hinj138_10_2
      Q2.hcardT138_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T138_10_2 i) (Q2.hfix138_10_2 i) _)
      colCert_138_10_4.hD ?_).symm
  rw [alnId_138 j hj]


theorem leaf_138_12_0 (hp : 0 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 138 []).length)
    (hq : (normIsRep.getD 138 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 0 hp)
        (rowE2 (⟨138, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp))
        (rowE1 (⟨138, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨138, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨138, by decide⟩ (listedAt ⟨138, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp)) T138_12
      hfix138_12 hinj138_12 hcardT138_12
      (fun i => conj_mem_of_fixedPoints _ _ (T138_12 i) (hfix138_12 i) _)
      ⟨138, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨138, by decide⟩ (Q2.listedAt ⟨138, by decide⟩
        (alnCheck_rep ⟨138, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 0 hp) Q2.T138_12_2 Q2.hfix138_12_2 Q2.hinj138_12_2
      Q2.hcardT138_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T138_12_2 i) (Q2.hfix138_12_2 i) _)
      colCert_138_12_0.hD ?_).symm
  rw [alnId_138 j hj]


theorem leaf_138_12_1 (hp : 1 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 138 []).length)
    (hq : (normIsRep.getD 138 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 1 hp)
        (rowE2 (⟨138, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp))
        (rowE1 (⟨138, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨138, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨138, by decide⟩ (listedAt ⟨138, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp)) T138_12
      hfix138_12 hinj138_12 hcardT138_12
      (fun i => conj_mem_of_fixedPoints _ _ (T138_12 i) (hfix138_12 i) _)
      ⟨138, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨138, by decide⟩ (Q2.listedAt ⟨138, by decide⟩
        (alnCheck_rep ⟨138, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 1 hp) Q2.T138_12_2 Q2.hfix138_12_2 Q2.hinj138_12_2
      Q2.hcardT138_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T138_12_2 i) (Q2.hfix138_12_2 i) _)
      colCert_138_12_1.hD ?_).symm
  rw [alnId_138 j hj]


theorem leaf_138_12_2 (hp : 2 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 138 []).length)
    (hq : (normIsRep.getD 138 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 2 hp)
        (rowE2 (⟨138, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp))
        (rowE1 (⟨138, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨138, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨138, by decide⟩ (listedAt ⟨138, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp)) T138_12
      hfix138_12 hinj138_12 hcardT138_12
      (fun i => conj_mem_of_fixedPoints _ _ (T138_12 i) (hfix138_12 i) _)
      ⟨138, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨138, by decide⟩ (Q2.listedAt ⟨138, by decide⟩
        (alnCheck_rep ⟨138, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 2 hp) Q2.T138_12_2 Q2.hfix138_12_2 Q2.hinj138_12_2
      Q2.hcardT138_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T138_12_2 i) (Q2.hfix138_12_2 i) _)
      colCert_138_12_2.hD ?_).symm
  rw [alnId_138 j hj]


theorem leaf_138_12_3 (hp : 3 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 138 []).length)
    (hq : (normIsRep.getD 138 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 3 hp)
        (rowE2 (⟨138, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp))
        (rowE1 (⟨138, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨138, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨138, by decide⟩ (listedAt ⟨138, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp)) T138_12
      hfix138_12 hinj138_12 hcardT138_12
      (fun i => conj_mem_of_fixedPoints _ _ (T138_12 i) (hfix138_12 i) _)
      ⟨138, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨138, by decide⟩ (Q2.listedAt ⟨138, by decide⟩
        (alnCheck_rep ⟨138, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 3 hp) Q2.T138_12_2 Q2.hfix138_12_2 Q2.hinj138_12_2
      Q2.hcardT138_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T138_12_2 i) (Q2.hfix138_12_2 i) _)
      colCert_138_12_3.hD ?_).symm
  rw [alnId_138 j hj]


theorem leaf_138_12_4 (hp : 4 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 138 []).length)
    (hq : (normIsRep.getD 138 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 4 hp)
        (rowE2 (⟨138, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp))
        (rowE1 (⟨138, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨138, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨138, by decide⟩ (listedAt ⟨138, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp)) T138_12
      hfix138_12 hinj138_12 hcardT138_12
      (fun i => conj_mem_of_fixedPoints _ _ (T138_12 i) (hfix138_12 i) _)
      ⟨138, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨138, by decide⟩ (Q2.listedAt ⟨138, by decide⟩
        (alnCheck_rep ⟨138, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 4 hp) Q2.T138_12_2 Q2.hfix138_12_2 Q2.hinj138_12_2
      Q2.hcardT138_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T138_12_2 i) (Q2.hfix138_12_2 i) _)
      colCert_138_12_4.hD ?_).symm
  rw [alnId_138 j hj]


theorem leaf_138_23_0 (hp : 0 < (Q2.transData.getD 23 []).length)
    (j : Nat) (hj : j < (repChars.getD 138 []).length)
    (hq : (normIsRep.getD 138 []).getD j false = true) :
    species (Q2.reps (⟨23, by decide⟩ : Fin 148)) (colE2 ⟨23, by decide⟩ 0 hp)
        (rowE2 (⟨138, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨23, by decide⟩ : Fin 148))
        (colE1 ⟨23, by decide⟩ 0 (transLenTr ⟨23, by decide⟩ 0 hp))
        (rowE1 (⟨138, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨138, by decide⟩ : Fin 148) ⟨23, by decide⟩ _
      (validAt ⟨138, by decide⟩ (listedAt ⟨138, by decide⟩ hj))
      (colE1 ⟨23, by decide⟩ 0 (transLenTr ⟨23, by decide⟩ 0 hp)) T138_23
      hfix138_23 hinj138_23 hcardT138_23
      (fun i => conj_mem_of_fixedPoints _ _ (T138_23 i) (hfix138_23 i) _)
      ⟨138, by decide⟩ ⟨23, by decide⟩ _
      (Q2.validAt ⟨138, by decide⟩ (Q2.listedAt ⟨138, by decide⟩
        (alnCheck_rep ⟨138, by decide⟩ hj hq).1))
      (colE2 ⟨23, by decide⟩ 0 hp) Q2.T138_23_2 Q2.hfix138_23_2 Q2.hinj138_23_2
      Q2.hcardT138_23_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T138_23_2 i) (Q2.hfix138_23_2 i) _)
      colCert_138_23_0.hD ?_).symm
  rw [alnId_138 j hj]


theorem leaf_138_23_1 (hp : 1 < (Q2.transData.getD 23 []).length)
    (j : Nat) (hj : j < (repChars.getD 138 []).length)
    (hq : (normIsRep.getD 138 []).getD j false = true) :
    species (Q2.reps (⟨23, by decide⟩ : Fin 148)) (colE2 ⟨23, by decide⟩ 1 hp)
        (rowE2 (⟨138, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨23, by decide⟩ : Fin 148))
        (colE1 ⟨23, by decide⟩ 1 (transLenTr ⟨23, by decide⟩ 1 hp))
        (rowE1 (⟨138, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨138, by decide⟩ : Fin 148) ⟨23, by decide⟩ _
      (validAt ⟨138, by decide⟩ (listedAt ⟨138, by decide⟩ hj))
      (colE1 ⟨23, by decide⟩ 1 (transLenTr ⟨23, by decide⟩ 1 hp)) T138_23
      hfix138_23 hinj138_23 hcardT138_23
      (fun i => conj_mem_of_fixedPoints _ _ (T138_23 i) (hfix138_23 i) _)
      ⟨138, by decide⟩ ⟨23, by decide⟩ _
      (Q2.validAt ⟨138, by decide⟩ (Q2.listedAt ⟨138, by decide⟩
        (alnCheck_rep ⟨138, by decide⟩ hj hq).1))
      (colE2 ⟨23, by decide⟩ 1 hp) Q2.T138_23_2 Q2.hfix138_23_2 Q2.hinj138_23_2
      Q2.hcardT138_23_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T138_23_2 i) (Q2.hfix138_23_2 i) _)
      colCert_138_23_1.hD ?_).symm
  rw [alnId_138 j hj]


theorem leaf_138_23_2 (hp : 2 < (Q2.transData.getD 23 []).length)
    (j : Nat) (hj : j < (repChars.getD 138 []).length)
    (hq : (normIsRep.getD 138 []).getD j false = true) :
    species (Q2.reps (⟨23, by decide⟩ : Fin 148)) (colE2 ⟨23, by decide⟩ 2 hp)
        (rowE2 (⟨138, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨23, by decide⟩ : Fin 148))
        (colE1 ⟨23, by decide⟩ 2 (transLenTr ⟨23, by decide⟩ 2 hp))
        (rowE1 (⟨138, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨138, by decide⟩ : Fin 148) ⟨23, by decide⟩ _
      (validAt ⟨138, by decide⟩ (listedAt ⟨138, by decide⟩ hj))
      (colE1 ⟨23, by decide⟩ 2 (transLenTr ⟨23, by decide⟩ 2 hp)) T138_23
      hfix138_23 hinj138_23 hcardT138_23
      (fun i => conj_mem_of_fixedPoints _ _ (T138_23 i) (hfix138_23 i) _)
      ⟨138, by decide⟩ ⟨23, by decide⟩ _
      (Q2.validAt ⟨138, by decide⟩ (Q2.listedAt ⟨138, by decide⟩
        (alnCheck_rep ⟨138, by decide⟩ hj hq).1))
      (colE2 ⟨23, by decide⟩ 2 hp) Q2.T138_23_2 Q2.hfix138_23_2 Q2.hinj138_23_2
      Q2.hcardT138_23_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T138_23_2 i) (Q2.hfix138_23_2 i) _)
      colCert_138_23_2.hD ?_).symm
  rw [alnId_138 j hj]


theorem leaf_138_23_3 (hp : 3 < (Q2.transData.getD 23 []).length)
    (j : Nat) (hj : j < (repChars.getD 138 []).length)
    (hq : (normIsRep.getD 138 []).getD j false = true) :
    species (Q2.reps (⟨23, by decide⟩ : Fin 148)) (colE2 ⟨23, by decide⟩ 3 hp)
        (rowE2 (⟨138, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨23, by decide⟩ : Fin 148))
        (colE1 ⟨23, by decide⟩ 3 (transLenTr ⟨23, by decide⟩ 3 hp))
        (rowE1 (⟨138, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨138, by decide⟩ : Fin 148) ⟨23, by decide⟩ _
      (validAt ⟨138, by decide⟩ (listedAt ⟨138, by decide⟩ hj))
      (colE1 ⟨23, by decide⟩ 3 (transLenTr ⟨23, by decide⟩ 3 hp)) T138_23
      hfix138_23 hinj138_23 hcardT138_23
      (fun i => conj_mem_of_fixedPoints _ _ (T138_23 i) (hfix138_23 i) _)
      ⟨138, by decide⟩ ⟨23, by decide⟩ _
      (Q2.validAt ⟨138, by decide⟩ (Q2.listedAt ⟨138, by decide⟩
        (alnCheck_rep ⟨138, by decide⟩ hj hq).1))
      (colE2 ⟨23, by decide⟩ 3 hp) Q2.T138_23_2 Q2.hfix138_23_2 Q2.hinj138_23_2
      Q2.hcardT138_23_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T138_23_2 i) (Q2.hfix138_23_2 i) _)
      colCert_138_23_3.hD ?_).symm
  rw [alnId_138 j hj]


theorem leaf_138_23_4 (hp : 4 < (Q2.transData.getD 23 []).length)
    (j : Nat) (hj : j < (repChars.getD 138 []).length)
    (hq : (normIsRep.getD 138 []).getD j false = true) :
    species (Q2.reps (⟨23, by decide⟩ : Fin 148)) (colE2 ⟨23, by decide⟩ 4 hp)
        (rowE2 (⟨138, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨23, by decide⟩ : Fin 148))
        (colE1 ⟨23, by decide⟩ 4 (transLenTr ⟨23, by decide⟩ 4 hp))
        (rowE1 (⟨138, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨138, by decide⟩ : Fin 148) ⟨23, by decide⟩ _
      (validAt ⟨138, by decide⟩ (listedAt ⟨138, by decide⟩ hj))
      (colE1 ⟨23, by decide⟩ 4 (transLenTr ⟨23, by decide⟩ 4 hp)) T138_23
      hfix138_23 hinj138_23 hcardT138_23
      (fun i => conj_mem_of_fixedPoints _ _ (T138_23 i) (hfix138_23 i) _)
      ⟨138, by decide⟩ ⟨23, by decide⟩ _
      (Q2.validAt ⟨138, by decide⟩ (Q2.listedAt ⟨138, by decide⟩
        (alnCheck_rep ⟨138, by decide⟩ hj hq).1))
      (colE2 ⟨23, by decide⟩ 4 hp) Q2.T138_23_2 Q2.hfix138_23_2 Q2.hinj138_23_2
      Q2.hcardT138_23_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T138_23_2 i) (Q2.hfix138_23_2 i) _)
      colCert_138_23_4.hD ?_).symm
  rw [alnId_138 j hj]


theorem leaf_138_23_5 (hp : 5 < (Q2.transData.getD 23 []).length)
    (j : Nat) (hj : j < (repChars.getD 138 []).length)
    (hq : (normIsRep.getD 138 []).getD j false = true) :
    species (Q2.reps (⟨23, by decide⟩ : Fin 148)) (colE2 ⟨23, by decide⟩ 5 hp)
        (rowE2 (⟨138, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨23, by decide⟩ : Fin 148))
        (colE1 ⟨23, by decide⟩ 5 (transLenTr ⟨23, by decide⟩ 5 hp))
        (rowE1 (⟨138, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨138, by decide⟩ : Fin 148) ⟨23, by decide⟩ _
      (validAt ⟨138, by decide⟩ (listedAt ⟨138, by decide⟩ hj))
      (colE1 ⟨23, by decide⟩ 5 (transLenTr ⟨23, by decide⟩ 5 hp)) T138_23
      hfix138_23 hinj138_23 hcardT138_23
      (fun i => conj_mem_of_fixedPoints _ _ (T138_23 i) (hfix138_23 i) _)
      ⟨138, by decide⟩ ⟨23, by decide⟩ _
      (Q2.validAt ⟨138, by decide⟩ (Q2.listedAt ⟨138, by decide⟩
        (alnCheck_rep ⟨138, by decide⟩ hj hq).1))
      (colE2 ⟨23, by decide⟩ 5 hp) Q2.T138_23_2 Q2.hfix138_23_2 Q2.hinj138_23_2
      Q2.hcardT138_23_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T138_23_2 i) (Q2.hfix138_23_2 i) _)
      ?_).symm
  rw [show colData1 (⟨138, by decide⟩ : Fin 148)
        ((colE1 ⟨23, by decide⟩ 5 (transLenTr ⟨23, by decide⟩ 5 hp) : ↥(reps ⟨23, by decide⟩)) : Coordinate 1)
        T138_23 = colFn colCertDiv_138_23_5.D1 (m := 5) from colCertDiv_138_23_5.bind1,
    show colData2 (⟨138, by decide⟩ : Fin 148)
        ((colE2 ⟨23, by decide⟩ 5 hp : ↥(Q2.reps ⟨23, by decide⟩)) : Coordinate 2)
        Q2.T138_23_2 = colFn colCertDiv_138_23_5.D2 (m := 5) from colCertDiv_138_23_5.bind2]
  rw [alnId_138 j hj]
  exact fastcode_of_div ⟨138, by decide⟩ _ _ _
    ((alnId_138 j hj) ▸ Q2.listedAt (⟨138, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨138, by decide⟩ : Fin 148) hj hq).1) colCertDiv_138_23_5_match


theorem leaf_138_23_10 (hp : 10 < (Q2.transData.getD 23 []).length)
    (j : Nat) (hj : j < (repChars.getD 138 []).length)
    (hq : (normIsRep.getD 138 []).getD j false = true) :
    species (Q2.reps (⟨23, by decide⟩ : Fin 148)) (colE2 ⟨23, by decide⟩ 10 hp)
        (rowE2 (⟨138, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨23, by decide⟩ : Fin 148))
        (colE1 ⟨23, by decide⟩ 10 (transLenTr ⟨23, by decide⟩ 10 hp))
        (rowE1 (⟨138, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨138, by decide⟩ : Fin 148) ⟨23, by decide⟩ _
      (validAt ⟨138, by decide⟩ (listedAt ⟨138, by decide⟩ hj))
      (colE1 ⟨23, by decide⟩ 10 (transLenTr ⟨23, by decide⟩ 10 hp)) T138_23
      hfix138_23 hinj138_23 hcardT138_23
      (fun i => conj_mem_of_fixedPoints _ _ (T138_23 i) (hfix138_23 i) _)
      ⟨138, by decide⟩ ⟨23, by decide⟩ _
      (Q2.validAt ⟨138, by decide⟩ (Q2.listedAt ⟨138, by decide⟩
        (alnCheck_rep ⟨138, by decide⟩ hj hq).1))
      (colE2 ⟨23, by decide⟩ 10 hp) Q2.T138_23_2 Q2.hfix138_23_2 Q2.hinj138_23_2
      Q2.hcardT138_23_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T138_23_2 i) (Q2.hfix138_23_2 i) _)
      ?_).symm
  rw [show colData1 (⟨138, by decide⟩ : Fin 148)
        ((colE1 ⟨23, by decide⟩ 10 (transLenTr ⟨23, by decide⟩ 10 hp) : ↥(reps ⟨23, by decide⟩)) : Coordinate 1)
        T138_23 = colFn colCertDiv_138_23_10.D1 (m := 5) from colCertDiv_138_23_10.bind1,
    show colData2 (⟨138, by decide⟩ : Fin 148)
        ((colE2 ⟨23, by decide⟩ 10 hp : ↥(Q2.reps ⟨23, by decide⟩)) : Coordinate 2)
        Q2.T138_23_2 = colFn colCertDiv_138_23_10.D2 (m := 5) from colCertDiv_138_23_10.bind2]
  rw [alnId_138 j hj]
  exact fastcode_of_div ⟨138, by decide⟩ _ _ _
    ((alnId_138 j hj) ▸ Q2.listedAt (⟨138, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨138, by decide⟩ : Fin 148) hj hq).1) colCertDiv_138_23_10_match


theorem leaf_138_23_15 (hp : 15 < (Q2.transData.getD 23 []).length)
    (j : Nat) (hj : j < (repChars.getD 138 []).length)
    (hq : (normIsRep.getD 138 []).getD j false = true) :
    species (Q2.reps (⟨23, by decide⟩ : Fin 148)) (colE2 ⟨23, by decide⟩ 15 hp)
        (rowE2 (⟨138, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨23, by decide⟩ : Fin 148))
        (colE1 ⟨23, by decide⟩ 15 (transLenTr ⟨23, by decide⟩ 15 hp))
        (rowE1 (⟨138, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨138, by decide⟩ : Fin 148) ⟨23, by decide⟩ _
      (validAt ⟨138, by decide⟩ (listedAt ⟨138, by decide⟩ hj))
      (colE1 ⟨23, by decide⟩ 15 (transLenTr ⟨23, by decide⟩ 15 hp)) T138_23
      hfix138_23 hinj138_23 hcardT138_23
      (fun i => conj_mem_of_fixedPoints _ _ (T138_23 i) (hfix138_23 i) _)
      ⟨138, by decide⟩ ⟨23, by decide⟩ _
      (Q2.validAt ⟨138, by decide⟩ (Q2.listedAt ⟨138, by decide⟩
        (alnCheck_rep ⟨138, by decide⟩ hj hq).1))
      (colE2 ⟨23, by decide⟩ 15 hp) Q2.T138_23_2 Q2.hfix138_23_2 Q2.hinj138_23_2
      Q2.hcardT138_23_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T138_23_2 i) (Q2.hfix138_23_2 i) _)
      ?_).symm
  rw [show colData1 (⟨138, by decide⟩ : Fin 148)
        ((colE1 ⟨23, by decide⟩ 15 (transLenTr ⟨23, by decide⟩ 15 hp) : ↥(reps ⟨23, by decide⟩)) : Coordinate 1)
        T138_23 = colFn colCertDiv_138_23_15.D1 (m := 5) from colCertDiv_138_23_15.bind1,
    show colData2 (⟨138, by decide⟩ : Fin 148)
        ((colE2 ⟨23, by decide⟩ 15 hp : ↥(Q2.reps ⟨23, by decide⟩)) : Coordinate 2)
        Q2.T138_23_2 = colFn colCertDiv_138_23_15.D2 (m := 5) from colCertDiv_138_23_15.bind2]
  rw [alnId_138 j hj]
  exact fastcode_of_div ⟨138, by decide⟩ _ _ _
    ((alnId_138 j hj) ▸ Q2.listedAt (⟨138, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨138, by decide⟩ : Fin 148) hj hq).1) colCertDiv_138_23_15_match


theorem leaf_138_23_20 (hp : 20 < (Q2.transData.getD 23 []).length)
    (j : Nat) (hj : j < (repChars.getD 138 []).length)
    (hq : (normIsRep.getD 138 []).getD j false = true) :
    species (Q2.reps (⟨23, by decide⟩ : Fin 148)) (colE2 ⟨23, by decide⟩ 20 hp)
        (rowE2 (⟨138, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨23, by decide⟩ : Fin 148))
        (colE1 ⟨23, by decide⟩ 20 (transLenTr ⟨23, by decide⟩ 20 hp))
        (rowE1 (⟨138, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨138, by decide⟩ : Fin 148) ⟨23, by decide⟩ _
      (validAt ⟨138, by decide⟩ (listedAt ⟨138, by decide⟩ hj))
      (colE1 ⟨23, by decide⟩ 20 (transLenTr ⟨23, by decide⟩ 20 hp)) T138_23
      hfix138_23 hinj138_23 hcardT138_23
      (fun i => conj_mem_of_fixedPoints _ _ (T138_23 i) (hfix138_23 i) _)
      ⟨138, by decide⟩ ⟨23, by decide⟩ _
      (Q2.validAt ⟨138, by decide⟩ (Q2.listedAt ⟨138, by decide⟩
        (alnCheck_rep ⟨138, by decide⟩ hj hq).1))
      (colE2 ⟨23, by decide⟩ 20 hp) Q2.T138_23_2 Q2.hfix138_23_2 Q2.hinj138_23_2
      Q2.hcardT138_23_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T138_23_2 i) (Q2.hfix138_23_2 i) _)
      ?_).symm
  rw [show colData1 (⟨138, by decide⟩ : Fin 148)
        ((colE1 ⟨23, by decide⟩ 20 (transLenTr ⟨23, by decide⟩ 20 hp) : ↥(reps ⟨23, by decide⟩)) : Coordinate 1)
        T138_23 = colFn colCertDiv_138_23_20.D1 (m := 5) from colCertDiv_138_23_20.bind1,
    show colData2 (⟨138, by decide⟩ : Fin 148)
        ((colE2 ⟨23, by decide⟩ 20 hp : ↥(Q2.reps ⟨23, by decide⟩)) : Coordinate 2)
        Q2.T138_23_2 = colFn colCertDiv_138_23_20.D2 (m := 5) from colCertDiv_138_23_20.bind2]
  rw [alnId_138 j hj]
  exact fastcode_of_div ⟨138, by decide⟩ _ _ _
    ((alnId_138 j hj) ▸ Q2.listedAt (⟨138, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨138, by decide⟩ : Fin 148) hj hq).1) colCertDiv_138_23_20_match


theorem leaf_138_31_0 (hp : 0 < (Q2.transData.getD 31 []).length)
    (j : Nat) (hj : j < (repChars.getD 138 []).length)
    (hq : (normIsRep.getD 138 []).getD j false = true) :
    species (Q2.reps (⟨31, by decide⟩ : Fin 148)) (colE2 ⟨31, by decide⟩ 0 hp)
        (rowE2 (⟨138, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨31, by decide⟩ : Fin 148))
        (colE1 ⟨31, by decide⟩ 0 (transLenTr ⟨31, by decide⟩ 0 hp))
        (rowE1 (⟨138, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨138, by decide⟩ : Fin 148) ⟨31, by decide⟩ _
      (validAt ⟨138, by decide⟩ (listedAt ⟨138, by decide⟩ hj))
      (colE1 ⟨31, by decide⟩ 0 (transLenTr ⟨31, by decide⟩ 0 hp)) T138_31
      hfix138_31 hinj138_31 hcardT138_31
      (fun i => conj_mem_of_fixedPoints _ _ (T138_31 i) (hfix138_31 i) _)
      ⟨138, by decide⟩ ⟨31, by decide⟩ _
      (Q2.validAt ⟨138, by decide⟩ (Q2.listedAt ⟨138, by decide⟩
        (alnCheck_rep ⟨138, by decide⟩ hj hq).1))
      (colE2 ⟨31, by decide⟩ 0 hp) Q2.T138_31_2 Q2.hfix138_31_2 Q2.hinj138_31_2
      Q2.hcardT138_31_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T138_31_2 i) (Q2.hfix138_31_2 i) _)
      colCert_138_31_0.hD ?_).symm
  rw [alnId_138 j hj]


theorem leaf_138_31_1 (hp : 1 < (Q2.transData.getD 31 []).length)
    (j : Nat) (hj : j < (repChars.getD 138 []).length)
    (hq : (normIsRep.getD 138 []).getD j false = true) :
    species (Q2.reps (⟨31, by decide⟩ : Fin 148)) (colE2 ⟨31, by decide⟩ 1 hp)
        (rowE2 (⟨138, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨31, by decide⟩ : Fin 148))
        (colE1 ⟨31, by decide⟩ 1 (transLenTr ⟨31, by decide⟩ 1 hp))
        (rowE1 (⟨138, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨138, by decide⟩ : Fin 148) ⟨31, by decide⟩ _
      (validAt ⟨138, by decide⟩ (listedAt ⟨138, by decide⟩ hj))
      (colE1 ⟨31, by decide⟩ 1 (transLenTr ⟨31, by decide⟩ 1 hp)) T138_31
      hfix138_31 hinj138_31 hcardT138_31
      (fun i => conj_mem_of_fixedPoints _ _ (T138_31 i) (hfix138_31 i) _)
      ⟨138, by decide⟩ ⟨31, by decide⟩ _
      (Q2.validAt ⟨138, by decide⟩ (Q2.listedAt ⟨138, by decide⟩
        (alnCheck_rep ⟨138, by decide⟩ hj hq).1))
      (colE2 ⟨31, by decide⟩ 1 hp) Q2.T138_31_2 Q2.hfix138_31_2 Q2.hinj138_31_2
      Q2.hcardT138_31_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T138_31_2 i) (Q2.hfix138_31_2 i) _)
      colCert_138_31_1.hD ?_).symm
  rw [alnId_138 j hj]


theorem leaf_138_31_2 (hp : 2 < (Q2.transData.getD 31 []).length)
    (j : Nat) (hj : j < (repChars.getD 138 []).length)
    (hq : (normIsRep.getD 138 []).getD j false = true) :
    species (Q2.reps (⟨31, by decide⟩ : Fin 148)) (colE2 ⟨31, by decide⟩ 2 hp)
        (rowE2 (⟨138, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨31, by decide⟩ : Fin 148))
        (colE1 ⟨31, by decide⟩ 2 (transLenTr ⟨31, by decide⟩ 2 hp))
        (rowE1 (⟨138, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨138, by decide⟩ : Fin 148) ⟨31, by decide⟩ _
      (validAt ⟨138, by decide⟩ (listedAt ⟨138, by decide⟩ hj))
      (colE1 ⟨31, by decide⟩ 2 (transLenTr ⟨31, by decide⟩ 2 hp)) T138_31
      hfix138_31 hinj138_31 hcardT138_31
      (fun i => conj_mem_of_fixedPoints _ _ (T138_31 i) (hfix138_31 i) _)
      ⟨138, by decide⟩ ⟨31, by decide⟩ _
      (Q2.validAt ⟨138, by decide⟩ (Q2.listedAt ⟨138, by decide⟩
        (alnCheck_rep ⟨138, by decide⟩ hj hq).1))
      (colE2 ⟨31, by decide⟩ 2 hp) Q2.T138_31_2 Q2.hfix138_31_2 Q2.hinj138_31_2
      Q2.hcardT138_31_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T138_31_2 i) (Q2.hfix138_31_2 i) _)
      colCert_138_31_2.hD ?_).symm
  rw [alnId_138 j hj]


theorem leaf_138_31_3 (hp : 3 < (Q2.transData.getD 31 []).length)
    (j : Nat) (hj : j < (repChars.getD 138 []).length)
    (hq : (normIsRep.getD 138 []).getD j false = true) :
    species (Q2.reps (⟨31, by decide⟩ : Fin 148)) (colE2 ⟨31, by decide⟩ 3 hp)
        (rowE2 (⟨138, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨31, by decide⟩ : Fin 148))
        (colE1 ⟨31, by decide⟩ 3 (transLenTr ⟨31, by decide⟩ 3 hp))
        (rowE1 (⟨138, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨138, by decide⟩ : Fin 148) ⟨31, by decide⟩ _
      (validAt ⟨138, by decide⟩ (listedAt ⟨138, by decide⟩ hj))
      (colE1 ⟨31, by decide⟩ 3 (transLenTr ⟨31, by decide⟩ 3 hp)) T138_31
      hfix138_31 hinj138_31 hcardT138_31
      (fun i => conj_mem_of_fixedPoints _ _ (T138_31 i) (hfix138_31 i) _)
      ⟨138, by decide⟩ ⟨31, by decide⟩ _
      (Q2.validAt ⟨138, by decide⟩ (Q2.listedAt ⟨138, by decide⟩
        (alnCheck_rep ⟨138, by decide⟩ hj hq).1))
      (colE2 ⟨31, by decide⟩ 3 hp) Q2.T138_31_2 Q2.hfix138_31_2 Q2.hinj138_31_2
      Q2.hcardT138_31_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T138_31_2 i) (Q2.hfix138_31_2 i) _)
      colCert_138_31_3.hD ?_).symm
  rw [alnId_138 j hj]


theorem leaf_138_31_4 (hp : 4 < (Q2.transData.getD 31 []).length)
    (j : Nat) (hj : j < (repChars.getD 138 []).length)
    (hq : (normIsRep.getD 138 []).getD j false = true) :
    species (Q2.reps (⟨31, by decide⟩ : Fin 148)) (colE2 ⟨31, by decide⟩ 4 hp)
        (rowE2 (⟨138, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨31, by decide⟩ : Fin 148))
        (colE1 ⟨31, by decide⟩ 4 (transLenTr ⟨31, by decide⟩ 4 hp))
        (rowE1 (⟨138, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨138, by decide⟩ : Fin 148) ⟨31, by decide⟩ _
      (validAt ⟨138, by decide⟩ (listedAt ⟨138, by decide⟩ hj))
      (colE1 ⟨31, by decide⟩ 4 (transLenTr ⟨31, by decide⟩ 4 hp)) T138_31
      hfix138_31 hinj138_31 hcardT138_31
      (fun i => conj_mem_of_fixedPoints _ _ (T138_31 i) (hfix138_31 i) _)
      ⟨138, by decide⟩ ⟨31, by decide⟩ _
      (Q2.validAt ⟨138, by decide⟩ (Q2.listedAt ⟨138, by decide⟩
        (alnCheck_rep ⟨138, by decide⟩ hj hq).1))
      (colE2 ⟨31, by decide⟩ 4 hp) Q2.T138_31_2 Q2.hfix138_31_2 Q2.hinj138_31_2
      Q2.hcardT138_31_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T138_31_2 i) (Q2.hfix138_31_2 i) _)
      colCert_138_31_4.hD ?_).symm
  rw [alnId_138 j hj]


theorem leaf_138_31_5 (hp : 5 < (Q2.transData.getD 31 []).length)
    (j : Nat) (hj : j < (repChars.getD 138 []).length)
    (hq : (normIsRep.getD 138 []).getD j false = true) :
    species (Q2.reps (⟨31, by decide⟩ : Fin 148)) (colE2 ⟨31, by decide⟩ 5 hp)
        (rowE2 (⟨138, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨31, by decide⟩ : Fin 148))
        (colE1 ⟨31, by decide⟩ 5 (transLenTr ⟨31, by decide⟩ 5 hp))
        (rowE1 (⟨138, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨138, by decide⟩ : Fin 148) ⟨31, by decide⟩ _
      (validAt ⟨138, by decide⟩ (listedAt ⟨138, by decide⟩ hj))
      (colE1 ⟨31, by decide⟩ 5 (transLenTr ⟨31, by decide⟩ 5 hp)) T138_31
      hfix138_31 hinj138_31 hcardT138_31
      (fun i => conj_mem_of_fixedPoints _ _ (T138_31 i) (hfix138_31 i) _)
      ⟨138, by decide⟩ ⟨31, by decide⟩ _
      (Q2.validAt ⟨138, by decide⟩ (Q2.listedAt ⟨138, by decide⟩
        (alnCheck_rep ⟨138, by decide⟩ hj hq).1))
      (colE2 ⟨31, by decide⟩ 5 hp) Q2.T138_31_2 Q2.hfix138_31_2 Q2.hinj138_31_2
      Q2.hcardT138_31_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T138_31_2 i) (Q2.hfix138_31_2 i) _)
      colCert_138_31_5.hD ?_).symm
  rw [alnId_138 j hj]


theorem leaf_138_31_10 (hp : 10 < (Q2.transData.getD 31 []).length)
    (j : Nat) (hj : j < (repChars.getD 138 []).length)
    (hq : (normIsRep.getD 138 []).getD j false = true) :
    species (Q2.reps (⟨31, by decide⟩ : Fin 148)) (colE2 ⟨31, by decide⟩ 10 hp)
        (rowE2 (⟨138, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨31, by decide⟩ : Fin 148))
        (colE1 ⟨31, by decide⟩ 10 (transLenTr ⟨31, by decide⟩ 10 hp))
        (rowE1 (⟨138, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨138, by decide⟩ : Fin 148) ⟨31, by decide⟩ _
      (validAt ⟨138, by decide⟩ (listedAt ⟨138, by decide⟩ hj))
      (colE1 ⟨31, by decide⟩ 10 (transLenTr ⟨31, by decide⟩ 10 hp)) T138_31
      hfix138_31 hinj138_31 hcardT138_31
      (fun i => conj_mem_of_fixedPoints _ _ (T138_31 i) (hfix138_31 i) _)
      ⟨138, by decide⟩ ⟨31, by decide⟩ _
      (Q2.validAt ⟨138, by decide⟩ (Q2.listedAt ⟨138, by decide⟩
        (alnCheck_rep ⟨138, by decide⟩ hj hq).1))
      (colE2 ⟨31, by decide⟩ 10 hp) Q2.T138_31_2 Q2.hfix138_31_2 Q2.hinj138_31_2
      Q2.hcardT138_31_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T138_31_2 i) (Q2.hfix138_31_2 i) _)
      ?_).symm
  rw [show colData1 (⟨138, by decide⟩ : Fin 148)
        ((colE1 ⟨31, by decide⟩ 10 (transLenTr ⟨31, by decide⟩ 10 hp) : ↥(reps ⟨31, by decide⟩)) : Coordinate 1)
        T138_31 = colFn colCertDiv_138_31_10.D1 (m := 5) from colCertDiv_138_31_10.bind1,
    show colData2 (⟨138, by decide⟩ : Fin 148)
        ((colE2 ⟨31, by decide⟩ 10 hp : ↥(Q2.reps ⟨31, by decide⟩)) : Coordinate 2)
        Q2.T138_31_2 = colFn colCertDiv_138_31_10.D2 (m := 5) from colCertDiv_138_31_10.bind2]
  rw [alnId_138 j hj]
  exact fastcode_of_div ⟨138, by decide⟩ _ _ _
    ((alnId_138 j hj) ▸ Q2.listedAt (⟨138, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨138, by decide⟩ : Fin 148) hj hq).1) colCertDiv_138_31_10_match


theorem leaf_138_31_15 (hp : 15 < (Q2.transData.getD 31 []).length)
    (j : Nat) (hj : j < (repChars.getD 138 []).length)
    (hq : (normIsRep.getD 138 []).getD j false = true) :
    species (Q2.reps (⟨31, by decide⟩ : Fin 148)) (colE2 ⟨31, by decide⟩ 15 hp)
        (rowE2 (⟨138, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨31, by decide⟩ : Fin 148))
        (colE1 ⟨31, by decide⟩ 15 (transLenTr ⟨31, by decide⟩ 15 hp))
        (rowE1 (⟨138, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨138, by decide⟩ : Fin 148) ⟨31, by decide⟩ _
      (validAt ⟨138, by decide⟩ (listedAt ⟨138, by decide⟩ hj))
      (colE1 ⟨31, by decide⟩ 15 (transLenTr ⟨31, by decide⟩ 15 hp)) T138_31
      hfix138_31 hinj138_31 hcardT138_31
      (fun i => conj_mem_of_fixedPoints _ _ (T138_31 i) (hfix138_31 i) _)
      ⟨138, by decide⟩ ⟨31, by decide⟩ _
      (Q2.validAt ⟨138, by decide⟩ (Q2.listedAt ⟨138, by decide⟩
        (alnCheck_rep ⟨138, by decide⟩ hj hq).1))
      (colE2 ⟨31, by decide⟩ 15 hp) Q2.T138_31_2 Q2.hfix138_31_2 Q2.hinj138_31_2
      Q2.hcardT138_31_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T138_31_2 i) (Q2.hfix138_31_2 i) _)
      ?_).symm
  rw [show colData1 (⟨138, by decide⟩ : Fin 148)
        ((colE1 ⟨31, by decide⟩ 15 (transLenTr ⟨31, by decide⟩ 15 hp) : ↥(reps ⟨31, by decide⟩)) : Coordinate 1)
        T138_31 = colFn colCertDiv_138_31_15.D1 (m := 5) from colCertDiv_138_31_15.bind1,
    show colData2 (⟨138, by decide⟩ : Fin 148)
        ((colE2 ⟨31, by decide⟩ 15 hp : ↥(Q2.reps ⟨31, by decide⟩)) : Coordinate 2)
        Q2.T138_31_2 = colFn colCertDiv_138_31_15.D2 (m := 5) from colCertDiv_138_31_15.bind2]
  rw [alnId_138 j hj]
  exact fastcode_of_div ⟨138, by decide⟩ _ _ _
    ((alnId_138 j hj) ▸ Q2.listedAt (⟨138, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨138, by decide⟩ : Fin 148) hj hq).1) colCertDiv_138_31_15_match


theorem leaf_138_31_20 (hp : 20 < (Q2.transData.getD 31 []).length)
    (j : Nat) (hj : j < (repChars.getD 138 []).length)
    (hq : (normIsRep.getD 138 []).getD j false = true) :
    species (Q2.reps (⟨31, by decide⟩ : Fin 148)) (colE2 ⟨31, by decide⟩ 20 hp)
        (rowE2 (⟨138, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨31, by decide⟩ : Fin 148))
        (colE1 ⟨31, by decide⟩ 20 (transLenTr ⟨31, by decide⟩ 20 hp))
        (rowE1 (⟨138, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨138, by decide⟩ : Fin 148) ⟨31, by decide⟩ _
      (validAt ⟨138, by decide⟩ (listedAt ⟨138, by decide⟩ hj))
      (colE1 ⟨31, by decide⟩ 20 (transLenTr ⟨31, by decide⟩ 20 hp)) T138_31
      hfix138_31 hinj138_31 hcardT138_31
      (fun i => conj_mem_of_fixedPoints _ _ (T138_31 i) (hfix138_31 i) _)
      ⟨138, by decide⟩ ⟨31, by decide⟩ _
      (Q2.validAt ⟨138, by decide⟩ (Q2.listedAt ⟨138, by decide⟩
        (alnCheck_rep ⟨138, by decide⟩ hj hq).1))
      (colE2 ⟨31, by decide⟩ 20 hp) Q2.T138_31_2 Q2.hfix138_31_2 Q2.hinj138_31_2
      Q2.hcardT138_31_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T138_31_2 i) (Q2.hfix138_31_2 i) _)
      ?_).symm
  rw [show colData1 (⟨138, by decide⟩ : Fin 148)
        ((colE1 ⟨31, by decide⟩ 20 (transLenTr ⟨31, by decide⟩ 20 hp) : ↥(reps ⟨31, by decide⟩)) : Coordinate 1)
        T138_31 = colFn colCertDiv_138_31_20.D1 (m := 5) from colCertDiv_138_31_20.bind1,
    show colData2 (⟨138, by decide⟩ : Fin 148)
        ((colE2 ⟨31, by decide⟩ 20 hp : ↥(Q2.reps ⟨31, by decide⟩)) : Coordinate 2)
        Q2.T138_31_2 = colFn colCertDiv_138_31_20.D2 (m := 5) from colCertDiv_138_31_20.bind2]
  rw [alnId_138 j hj]
  exact fastcode_of_div ⟨138, by decide⟩ _ _ _
    ((alnId_138 j hj) ▸ Q2.listedAt (⟨138, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨138, by decide⟩ : Fin 148) hj hq).1) colCertDiv_138_31_20_match


theorem leaf_138_33_0 (hp : 0 < (Q2.transData.getD 33 []).length)
    (j : Nat) (hj : j < (repChars.getD 138 []).length)
    (hq : (normIsRep.getD 138 []).getD j false = true) :
    species (Q2.reps (⟨33, by decide⟩ : Fin 148)) (colE2 ⟨33, by decide⟩ 0 hp)
        (rowE2 (⟨138, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨33, by decide⟩ : Fin 148))
        (colE1 ⟨33, by decide⟩ 0 (transLenTr ⟨33, by decide⟩ 0 hp))
        (rowE1 (⟨138, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨138, by decide⟩ : Fin 148) ⟨33, by decide⟩ _
      (validAt ⟨138, by decide⟩ (listedAt ⟨138, by decide⟩ hj))
      (colE1 ⟨33, by decide⟩ 0 (transLenTr ⟨33, by decide⟩ 0 hp)) T138_33
      hfix138_33 hinj138_33 hcardT138_33
      (fun i => conj_mem_of_fixedPoints _ _ (T138_33 i) (hfix138_33 i) _)
      ⟨138, by decide⟩ ⟨33, by decide⟩ _
      (Q2.validAt ⟨138, by decide⟩ (Q2.listedAt ⟨138, by decide⟩
        (alnCheck_rep ⟨138, by decide⟩ hj hq).1))
      (colE2 ⟨33, by decide⟩ 0 hp) Q2.T138_33_2 Q2.hfix138_33_2 Q2.hinj138_33_2
      Q2.hcardT138_33_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T138_33_2 i) (Q2.hfix138_33_2 i) _)
      colCert_138_33_0.hD ?_).symm
  rw [alnId_138 j hj]


theorem leaf_138_33_1 (hp : 1 < (Q2.transData.getD 33 []).length)
    (j : Nat) (hj : j < (repChars.getD 138 []).length)
    (hq : (normIsRep.getD 138 []).getD j false = true) :
    species (Q2.reps (⟨33, by decide⟩ : Fin 148)) (colE2 ⟨33, by decide⟩ 1 hp)
        (rowE2 (⟨138, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨33, by decide⟩ : Fin 148))
        (colE1 ⟨33, by decide⟩ 1 (transLenTr ⟨33, by decide⟩ 1 hp))
        (rowE1 (⟨138, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨138, by decide⟩ : Fin 148) ⟨33, by decide⟩ _
      (validAt ⟨138, by decide⟩ (listedAt ⟨138, by decide⟩ hj))
      (colE1 ⟨33, by decide⟩ 1 (transLenTr ⟨33, by decide⟩ 1 hp)) T138_33
      hfix138_33 hinj138_33 hcardT138_33
      (fun i => conj_mem_of_fixedPoints _ _ (T138_33 i) (hfix138_33 i) _)
      ⟨138, by decide⟩ ⟨33, by decide⟩ _
      (Q2.validAt ⟨138, by decide⟩ (Q2.listedAt ⟨138, by decide⟩
        (alnCheck_rep ⟨138, by decide⟩ hj hq).1))
      (colE2 ⟨33, by decide⟩ 1 hp) Q2.T138_33_2 Q2.hfix138_33_2 Q2.hinj138_33_2
      Q2.hcardT138_33_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T138_33_2 i) (Q2.hfix138_33_2 i) _)
      colCert_138_33_1.hD ?_).symm
  rw [alnId_138 j hj]


theorem leaf_138_33_2 (hp : 2 < (Q2.transData.getD 33 []).length)
    (j : Nat) (hj : j < (repChars.getD 138 []).length)
    (hq : (normIsRep.getD 138 []).getD j false = true) :
    species (Q2.reps (⟨33, by decide⟩ : Fin 148)) (colE2 ⟨33, by decide⟩ 2 hp)
        (rowE2 (⟨138, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨33, by decide⟩ : Fin 148))
        (colE1 ⟨33, by decide⟩ 2 (transLenTr ⟨33, by decide⟩ 2 hp))
        (rowE1 (⟨138, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨138, by decide⟩ : Fin 148) ⟨33, by decide⟩ _
      (validAt ⟨138, by decide⟩ (listedAt ⟨138, by decide⟩ hj))
      (colE1 ⟨33, by decide⟩ 2 (transLenTr ⟨33, by decide⟩ 2 hp)) T138_33
      hfix138_33 hinj138_33 hcardT138_33
      (fun i => conj_mem_of_fixedPoints _ _ (T138_33 i) (hfix138_33 i) _)
      ⟨138, by decide⟩ ⟨33, by decide⟩ _
      (Q2.validAt ⟨138, by decide⟩ (Q2.listedAt ⟨138, by decide⟩
        (alnCheck_rep ⟨138, by decide⟩ hj hq).1))
      (colE2 ⟨33, by decide⟩ 2 hp) Q2.T138_33_2 Q2.hfix138_33_2 Q2.hinj138_33_2
      Q2.hcardT138_33_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T138_33_2 i) (Q2.hfix138_33_2 i) _)
      colCert_138_33_2.hD ?_).symm
  rw [alnId_138 j hj]


theorem leaf_138_33_3 (hp : 3 < (Q2.transData.getD 33 []).length)
    (j : Nat) (hj : j < (repChars.getD 138 []).length)
    (hq : (normIsRep.getD 138 []).getD j false = true) :
    species (Q2.reps (⟨33, by decide⟩ : Fin 148)) (colE2 ⟨33, by decide⟩ 3 hp)
        (rowE2 (⟨138, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨33, by decide⟩ : Fin 148))
        (colE1 ⟨33, by decide⟩ 3 (transLenTr ⟨33, by decide⟩ 3 hp))
        (rowE1 (⟨138, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨138, by decide⟩ : Fin 148) ⟨33, by decide⟩ _
      (validAt ⟨138, by decide⟩ (listedAt ⟨138, by decide⟩ hj))
      (colE1 ⟨33, by decide⟩ 3 (transLenTr ⟨33, by decide⟩ 3 hp)) T138_33
      hfix138_33 hinj138_33 hcardT138_33
      (fun i => conj_mem_of_fixedPoints _ _ (T138_33 i) (hfix138_33 i) _)
      ⟨138, by decide⟩ ⟨33, by decide⟩ _
      (Q2.validAt ⟨138, by decide⟩ (Q2.listedAt ⟨138, by decide⟩
        (alnCheck_rep ⟨138, by decide⟩ hj hq).1))
      (colE2 ⟨33, by decide⟩ 3 hp) Q2.T138_33_2 Q2.hfix138_33_2 Q2.hinj138_33_2
      Q2.hcardT138_33_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T138_33_2 i) (Q2.hfix138_33_2 i) _)
      colCert_138_33_3.hD ?_).symm
  rw [alnId_138 j hj]


theorem leaf_138_33_4 (hp : 4 < (Q2.transData.getD 33 []).length)
    (j : Nat) (hj : j < (repChars.getD 138 []).length)
    (hq : (normIsRep.getD 138 []).getD j false = true) :
    species (Q2.reps (⟨33, by decide⟩ : Fin 148)) (colE2 ⟨33, by decide⟩ 4 hp)
        (rowE2 (⟨138, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨33, by decide⟩ : Fin 148))
        (colE1 ⟨33, by decide⟩ 4 (transLenTr ⟨33, by decide⟩ 4 hp))
        (rowE1 (⟨138, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨138, by decide⟩ : Fin 148) ⟨33, by decide⟩ _
      (validAt ⟨138, by decide⟩ (listedAt ⟨138, by decide⟩ hj))
      (colE1 ⟨33, by decide⟩ 4 (transLenTr ⟨33, by decide⟩ 4 hp)) T138_33
      hfix138_33 hinj138_33 hcardT138_33
      (fun i => conj_mem_of_fixedPoints _ _ (T138_33 i) (hfix138_33 i) _)
      ⟨138, by decide⟩ ⟨33, by decide⟩ _
      (Q2.validAt ⟨138, by decide⟩ (Q2.listedAt ⟨138, by decide⟩
        (alnCheck_rep ⟨138, by decide⟩ hj hq).1))
      (colE2 ⟨33, by decide⟩ 4 hp) Q2.T138_33_2 Q2.hfix138_33_2 Q2.hinj138_33_2
      Q2.hcardT138_33_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T138_33_2 i) (Q2.hfix138_33_2 i) _)
      colCert_138_33_4.hD ?_).symm
  rw [alnId_138 j hj]


theorem leaf_138_33_5 (hp : 5 < (Q2.transData.getD 33 []).length)
    (j : Nat) (hj : j < (repChars.getD 138 []).length)
    (hq : (normIsRep.getD 138 []).getD j false = true) :
    species (Q2.reps (⟨33, by decide⟩ : Fin 148)) (colE2 ⟨33, by decide⟩ 5 hp)
        (rowE2 (⟨138, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨33, by decide⟩ : Fin 148))
        (colE1 ⟨33, by decide⟩ 5 (transLenTr ⟨33, by decide⟩ 5 hp))
        (rowE1 (⟨138, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨138, by decide⟩ : Fin 148) ⟨33, by decide⟩ _
      (validAt ⟨138, by decide⟩ (listedAt ⟨138, by decide⟩ hj))
      (colE1 ⟨33, by decide⟩ 5 (transLenTr ⟨33, by decide⟩ 5 hp)) T138_33
      hfix138_33 hinj138_33 hcardT138_33
      (fun i => conj_mem_of_fixedPoints _ _ (T138_33 i) (hfix138_33 i) _)
      ⟨138, by decide⟩ ⟨33, by decide⟩ _
      (Q2.validAt ⟨138, by decide⟩ (Q2.listedAt ⟨138, by decide⟩
        (alnCheck_rep ⟨138, by decide⟩ hj hq).1))
      (colE2 ⟨33, by decide⟩ 5 hp) Q2.T138_33_2 Q2.hfix138_33_2 Q2.hinj138_33_2
      Q2.hcardT138_33_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T138_33_2 i) (Q2.hfix138_33_2 i) _)
      ?_).symm
  rw [show colData1 (⟨138, by decide⟩ : Fin 148)
        ((colE1 ⟨33, by decide⟩ 5 (transLenTr ⟨33, by decide⟩ 5 hp) : ↥(reps ⟨33, by decide⟩)) : Coordinate 1)
        T138_33 = colFn colCertDiv_138_33_5.D1 (m := 5) from colCertDiv_138_33_5.bind1,
    show colData2 (⟨138, by decide⟩ : Fin 148)
        ((colE2 ⟨33, by decide⟩ 5 hp : ↥(Q2.reps ⟨33, by decide⟩)) : Coordinate 2)
        Q2.T138_33_2 = colFn colCertDiv_138_33_5.D2 (m := 5) from colCertDiv_138_33_5.bind2]
  rw [alnId_138 j hj]
  exact fastcode_of_div ⟨138, by decide⟩ _ _ _
    ((alnId_138 j hj) ▸ Q2.listedAt (⟨138, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨138, by decide⟩ : Fin 148) hj hq).1) colCertDiv_138_33_5_match


theorem leaf_138_33_10 (hp : 10 < (Q2.transData.getD 33 []).length)
    (j : Nat) (hj : j < (repChars.getD 138 []).length)
    (hq : (normIsRep.getD 138 []).getD j false = true) :
    species (Q2.reps (⟨33, by decide⟩ : Fin 148)) (colE2 ⟨33, by decide⟩ 10 hp)
        (rowE2 (⟨138, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨33, by decide⟩ : Fin 148))
        (colE1 ⟨33, by decide⟩ 10 (transLenTr ⟨33, by decide⟩ 10 hp))
        (rowE1 (⟨138, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨138, by decide⟩ : Fin 148) ⟨33, by decide⟩ _
      (validAt ⟨138, by decide⟩ (listedAt ⟨138, by decide⟩ hj))
      (colE1 ⟨33, by decide⟩ 10 (transLenTr ⟨33, by decide⟩ 10 hp)) T138_33
      hfix138_33 hinj138_33 hcardT138_33
      (fun i => conj_mem_of_fixedPoints _ _ (T138_33 i) (hfix138_33 i) _)
      ⟨138, by decide⟩ ⟨33, by decide⟩ _
      (Q2.validAt ⟨138, by decide⟩ (Q2.listedAt ⟨138, by decide⟩
        (alnCheck_rep ⟨138, by decide⟩ hj hq).1))
      (colE2 ⟨33, by decide⟩ 10 hp) Q2.T138_33_2 Q2.hfix138_33_2 Q2.hinj138_33_2
      Q2.hcardT138_33_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T138_33_2 i) (Q2.hfix138_33_2 i) _)
      ?_).symm
  rw [show colData1 (⟨138, by decide⟩ : Fin 148)
        ((colE1 ⟨33, by decide⟩ 10 (transLenTr ⟨33, by decide⟩ 10 hp) : ↥(reps ⟨33, by decide⟩)) : Coordinate 1)
        T138_33 = colFn colCertDiv_138_33_10.D1 (m := 5) from colCertDiv_138_33_10.bind1,
    show colData2 (⟨138, by decide⟩ : Fin 148)
        ((colE2 ⟨33, by decide⟩ 10 hp : ↥(Q2.reps ⟨33, by decide⟩)) : Coordinate 2)
        Q2.T138_33_2 = colFn colCertDiv_138_33_10.D2 (m := 5) from colCertDiv_138_33_10.bind2]
  rw [alnId_138 j hj]
  exact fastcode_of_div ⟨138, by decide⟩ _ _ _
    ((alnId_138 j hj) ▸ Q2.listedAt (⟨138, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨138, by decide⟩ : Fin 148) hj hq).1) colCertDiv_138_33_10_match


theorem leaf_138_33_15 (hp : 15 < (Q2.transData.getD 33 []).length)
    (j : Nat) (hj : j < (repChars.getD 138 []).length)
    (hq : (normIsRep.getD 138 []).getD j false = true) :
    species (Q2.reps (⟨33, by decide⟩ : Fin 148)) (colE2 ⟨33, by decide⟩ 15 hp)
        (rowE2 (⟨138, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨33, by decide⟩ : Fin 148))
        (colE1 ⟨33, by decide⟩ 15 (transLenTr ⟨33, by decide⟩ 15 hp))
        (rowE1 (⟨138, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨138, by decide⟩ : Fin 148) ⟨33, by decide⟩ _
      (validAt ⟨138, by decide⟩ (listedAt ⟨138, by decide⟩ hj))
      (colE1 ⟨33, by decide⟩ 15 (transLenTr ⟨33, by decide⟩ 15 hp)) T138_33
      hfix138_33 hinj138_33 hcardT138_33
      (fun i => conj_mem_of_fixedPoints _ _ (T138_33 i) (hfix138_33 i) _)
      ⟨138, by decide⟩ ⟨33, by decide⟩ _
      (Q2.validAt ⟨138, by decide⟩ (Q2.listedAt ⟨138, by decide⟩
        (alnCheck_rep ⟨138, by decide⟩ hj hq).1))
      (colE2 ⟨33, by decide⟩ 15 hp) Q2.T138_33_2 Q2.hfix138_33_2 Q2.hinj138_33_2
      Q2.hcardT138_33_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T138_33_2 i) (Q2.hfix138_33_2 i) _)
      ?_).symm
  rw [show colData1 (⟨138, by decide⟩ : Fin 148)
        ((colE1 ⟨33, by decide⟩ 15 (transLenTr ⟨33, by decide⟩ 15 hp) : ↥(reps ⟨33, by decide⟩)) : Coordinate 1)
        T138_33 = colFn colCertDiv_138_33_15.D1 (m := 5) from colCertDiv_138_33_15.bind1,
    show colData2 (⟨138, by decide⟩ : Fin 148)
        ((colE2 ⟨33, by decide⟩ 15 hp : ↥(Q2.reps ⟨33, by decide⟩)) : Coordinate 2)
        Q2.T138_33_2 = colFn colCertDiv_138_33_15.D2 (m := 5) from colCertDiv_138_33_15.bind2]
  rw [alnId_138 j hj]
  exact fastcode_of_div ⟨138, by decide⟩ _ _ _
    ((alnId_138 j hj) ▸ Q2.listedAt (⟨138, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨138, by decide⟩ : Fin 148) hj hq).1) colCertDiv_138_33_15_match


theorem leaf_138_33_20 (hp : 20 < (Q2.transData.getD 33 []).length)
    (j : Nat) (hj : j < (repChars.getD 138 []).length)
    (hq : (normIsRep.getD 138 []).getD j false = true) :
    species (Q2.reps (⟨33, by decide⟩ : Fin 148)) (colE2 ⟨33, by decide⟩ 20 hp)
        (rowE2 (⟨138, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨33, by decide⟩ : Fin 148))
        (colE1 ⟨33, by decide⟩ 20 (transLenTr ⟨33, by decide⟩ 20 hp))
        (rowE1 (⟨138, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨138, by decide⟩ : Fin 148) ⟨33, by decide⟩ _
      (validAt ⟨138, by decide⟩ (listedAt ⟨138, by decide⟩ hj))
      (colE1 ⟨33, by decide⟩ 20 (transLenTr ⟨33, by decide⟩ 20 hp)) T138_33
      hfix138_33 hinj138_33 hcardT138_33
      (fun i => conj_mem_of_fixedPoints _ _ (T138_33 i) (hfix138_33 i) _)
      ⟨138, by decide⟩ ⟨33, by decide⟩ _
      (Q2.validAt ⟨138, by decide⟩ (Q2.listedAt ⟨138, by decide⟩
        (alnCheck_rep ⟨138, by decide⟩ hj hq).1))
      (colE2 ⟨33, by decide⟩ 20 hp) Q2.T138_33_2 Q2.hfix138_33_2 Q2.hinj138_33_2
      Q2.hcardT138_33_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T138_33_2 i) (Q2.hfix138_33_2 i) _)
      ?_).symm
  rw [show colData1 (⟨138, by decide⟩ : Fin 148)
        ((colE1 ⟨33, by decide⟩ 20 (transLenTr ⟨33, by decide⟩ 20 hp) : ↥(reps ⟨33, by decide⟩)) : Coordinate 1)
        T138_33 = colFn colCertDiv_138_33_20.D1 (m := 5) from colCertDiv_138_33_20.bind1,
    show colData2 (⟨138, by decide⟩ : Fin 148)
        ((colE2 ⟨33, by decide⟩ 20 hp : ↥(Q2.reps ⟨33, by decide⟩)) : Coordinate 2)
        Q2.T138_33_2 = colFn colCertDiv_138_33_20.D2 (m := 5) from colCertDiv_138_33_20.bind2]
  rw [alnId_138 j hj]
  exact fastcode_of_div ⟨138, by decide⟩ _ _ _
    ((alnId_138 j hj) ▸ Q2.listedAt (⟨138, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨138, by decide⟩ : Fin 148) hj hq).1) colCertDiv_138_33_20_match


theorem leaf_138_42_0 (hp : 0 < (Q2.transData.getD 42 []).length)
    (j : Nat) (hj : j < (repChars.getD 138 []).length)
    (hq : (normIsRep.getD 138 []).getD j false = true) :
    species (Q2.reps (⟨42, by decide⟩ : Fin 148)) (colE2 ⟨42, by decide⟩ 0 hp)
        (rowE2 (⟨138, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨42, by decide⟩ : Fin 148))
        (colE1 ⟨42, by decide⟩ 0 (transLenTr ⟨42, by decide⟩ 0 hp))
        (rowE1 (⟨138, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨138, by decide⟩ : Fin 148) ⟨42, by decide⟩ _
      (validAt ⟨138, by decide⟩ (listedAt ⟨138, by decide⟩ hj))
      (colE1 ⟨42, by decide⟩ 0 (transLenTr ⟨42, by decide⟩ 0 hp)) T138_42
      hfix138_42 hinj138_42 hcardT138_42
      (fun i => conj_mem_of_fixedPoints _ _ (T138_42 i) (hfix138_42 i) _)
      ⟨138, by decide⟩ ⟨42, by decide⟩ _
      (Q2.validAt ⟨138, by decide⟩ (Q2.listedAt ⟨138, by decide⟩
        (alnCheck_rep ⟨138, by decide⟩ hj hq).1))
      (colE2 ⟨42, by decide⟩ 0 hp) Q2.T138_42_2 Q2.hfix138_42_2 Q2.hinj138_42_2
      Q2.hcardT138_42_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T138_42_2 i) (Q2.hfix138_42_2 i) _)
      colCert_138_42_0.hD ?_).symm
  rw [alnId_138 j hj]


theorem leaf_138_42_1 (hp : 1 < (Q2.transData.getD 42 []).length)
    (j : Nat) (hj : j < (repChars.getD 138 []).length)
    (hq : (normIsRep.getD 138 []).getD j false = true) :
    species (Q2.reps (⟨42, by decide⟩ : Fin 148)) (colE2 ⟨42, by decide⟩ 1 hp)
        (rowE2 (⟨138, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨42, by decide⟩ : Fin 148))
        (colE1 ⟨42, by decide⟩ 1 (transLenTr ⟨42, by decide⟩ 1 hp))
        (rowE1 (⟨138, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨138, by decide⟩ : Fin 148) ⟨42, by decide⟩ _
      (validAt ⟨138, by decide⟩ (listedAt ⟨138, by decide⟩ hj))
      (colE1 ⟨42, by decide⟩ 1 (transLenTr ⟨42, by decide⟩ 1 hp)) T138_42
      hfix138_42 hinj138_42 hcardT138_42
      (fun i => conj_mem_of_fixedPoints _ _ (T138_42 i) (hfix138_42 i) _)
      ⟨138, by decide⟩ ⟨42, by decide⟩ _
      (Q2.validAt ⟨138, by decide⟩ (Q2.listedAt ⟨138, by decide⟩
        (alnCheck_rep ⟨138, by decide⟩ hj hq).1))
      (colE2 ⟨42, by decide⟩ 1 hp) Q2.T138_42_2 Q2.hfix138_42_2 Q2.hinj138_42_2
      Q2.hcardT138_42_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T138_42_2 i) (Q2.hfix138_42_2 i) _)
      colCert_138_42_1.hD ?_).symm
  rw [alnId_138 j hj]


theorem leaf_138_42_2 (hp : 2 < (Q2.transData.getD 42 []).length)
    (j : Nat) (hj : j < (repChars.getD 138 []).length)
    (hq : (normIsRep.getD 138 []).getD j false = true) :
    species (Q2.reps (⟨42, by decide⟩ : Fin 148)) (colE2 ⟨42, by decide⟩ 2 hp)
        (rowE2 (⟨138, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨42, by decide⟩ : Fin 148))
        (colE1 ⟨42, by decide⟩ 2 (transLenTr ⟨42, by decide⟩ 2 hp))
        (rowE1 (⟨138, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨138, by decide⟩ : Fin 148) ⟨42, by decide⟩ _
      (validAt ⟨138, by decide⟩ (listedAt ⟨138, by decide⟩ hj))
      (colE1 ⟨42, by decide⟩ 2 (transLenTr ⟨42, by decide⟩ 2 hp)) T138_42
      hfix138_42 hinj138_42 hcardT138_42
      (fun i => conj_mem_of_fixedPoints _ _ (T138_42 i) (hfix138_42 i) _)
      ⟨138, by decide⟩ ⟨42, by decide⟩ _
      (Q2.validAt ⟨138, by decide⟩ (Q2.listedAt ⟨138, by decide⟩
        (alnCheck_rep ⟨138, by decide⟩ hj hq).1))
      (colE2 ⟨42, by decide⟩ 2 hp) Q2.T138_42_2 Q2.hfix138_42_2 Q2.hinj138_42_2
      Q2.hcardT138_42_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T138_42_2 i) (Q2.hfix138_42_2 i) _)
      colCert_138_42_2.hD ?_).symm
  rw [alnId_138 j hj]


theorem leaf_138_42_3 (hp : 3 < (Q2.transData.getD 42 []).length)
    (j : Nat) (hj : j < (repChars.getD 138 []).length)
    (hq : (normIsRep.getD 138 []).getD j false = true) :
    species (Q2.reps (⟨42, by decide⟩ : Fin 148)) (colE2 ⟨42, by decide⟩ 3 hp)
        (rowE2 (⟨138, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨42, by decide⟩ : Fin 148))
        (colE1 ⟨42, by decide⟩ 3 (transLenTr ⟨42, by decide⟩ 3 hp))
        (rowE1 (⟨138, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨138, by decide⟩ : Fin 148) ⟨42, by decide⟩ _
      (validAt ⟨138, by decide⟩ (listedAt ⟨138, by decide⟩ hj))
      (colE1 ⟨42, by decide⟩ 3 (transLenTr ⟨42, by decide⟩ 3 hp)) T138_42
      hfix138_42 hinj138_42 hcardT138_42
      (fun i => conj_mem_of_fixedPoints _ _ (T138_42 i) (hfix138_42 i) _)
      ⟨138, by decide⟩ ⟨42, by decide⟩ _
      (Q2.validAt ⟨138, by decide⟩ (Q2.listedAt ⟨138, by decide⟩
        (alnCheck_rep ⟨138, by decide⟩ hj hq).1))
      (colE2 ⟨42, by decide⟩ 3 hp) Q2.T138_42_2 Q2.hfix138_42_2 Q2.hinj138_42_2
      Q2.hcardT138_42_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T138_42_2 i) (Q2.hfix138_42_2 i) _)
      colCert_138_42_3.hD ?_).symm
  rw [alnId_138 j hj]


theorem leaf_138_42_4 (hp : 4 < (Q2.transData.getD 42 []).length)
    (j : Nat) (hj : j < (repChars.getD 138 []).length)
    (hq : (normIsRep.getD 138 []).getD j false = true) :
    species (Q2.reps (⟨42, by decide⟩ : Fin 148)) (colE2 ⟨42, by decide⟩ 4 hp)
        (rowE2 (⟨138, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨42, by decide⟩ : Fin 148))
        (colE1 ⟨42, by decide⟩ 4 (transLenTr ⟨42, by decide⟩ 4 hp))
        (rowE1 (⟨138, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨138, by decide⟩ : Fin 148) ⟨42, by decide⟩ _
      (validAt ⟨138, by decide⟩ (listedAt ⟨138, by decide⟩ hj))
      (colE1 ⟨42, by decide⟩ 4 (transLenTr ⟨42, by decide⟩ 4 hp)) T138_42
      hfix138_42 hinj138_42 hcardT138_42
      (fun i => conj_mem_of_fixedPoints _ _ (T138_42 i) (hfix138_42 i) _)
      ⟨138, by decide⟩ ⟨42, by decide⟩ _
      (Q2.validAt ⟨138, by decide⟩ (Q2.listedAt ⟨138, by decide⟩
        (alnCheck_rep ⟨138, by decide⟩ hj hq).1))
      (colE2 ⟨42, by decide⟩ 4 hp) Q2.T138_42_2 Q2.hfix138_42_2 Q2.hinj138_42_2
      Q2.hcardT138_42_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T138_42_2 i) (Q2.hfix138_42_2 i) _)
      colCert_138_42_4.hD ?_).symm
  rw [alnId_138 j hj]


theorem leaf_138_42_5 (hp : 5 < (Q2.transData.getD 42 []).length)
    (j : Nat) (hj : j < (repChars.getD 138 []).length)
    (hq : (normIsRep.getD 138 []).getD j false = true) :
    species (Q2.reps (⟨42, by decide⟩ : Fin 148)) (colE2 ⟨42, by decide⟩ 5 hp)
        (rowE2 (⟨138, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨42, by decide⟩ : Fin 148))
        (colE1 ⟨42, by decide⟩ 5 (transLenTr ⟨42, by decide⟩ 5 hp))
        (rowE1 (⟨138, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨138, by decide⟩ : Fin 148) ⟨42, by decide⟩ _
      (validAt ⟨138, by decide⟩ (listedAt ⟨138, by decide⟩ hj))
      (colE1 ⟨42, by decide⟩ 5 (transLenTr ⟨42, by decide⟩ 5 hp)) T138_42
      hfix138_42 hinj138_42 hcardT138_42
      (fun i => conj_mem_of_fixedPoints _ _ (T138_42 i) (hfix138_42 i) _)
      ⟨138, by decide⟩ ⟨42, by decide⟩ _
      (Q2.validAt ⟨138, by decide⟩ (Q2.listedAt ⟨138, by decide⟩
        (alnCheck_rep ⟨138, by decide⟩ hj hq).1))
      (colE2 ⟨42, by decide⟩ 5 hp) Q2.T138_42_2 Q2.hfix138_42_2 Q2.hinj138_42_2
      Q2.hcardT138_42_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T138_42_2 i) (Q2.hfix138_42_2 i) _)
      ?_).symm
  rw [show colData1 (⟨138, by decide⟩ : Fin 148)
        ((colE1 ⟨42, by decide⟩ 5 (transLenTr ⟨42, by decide⟩ 5 hp) : ↥(reps ⟨42, by decide⟩)) : Coordinate 1)
        T138_42 = colFn colCertDiv_138_42_5.D1 (m := 5) from colCertDiv_138_42_5.bind1,
    show colData2 (⟨138, by decide⟩ : Fin 148)
        ((colE2 ⟨42, by decide⟩ 5 hp : ↥(Q2.reps ⟨42, by decide⟩)) : Coordinate 2)
        Q2.T138_42_2 = colFn colCertDiv_138_42_5.D2 (m := 5) from colCertDiv_138_42_5.bind2]
  rw [alnId_138 j hj]
  exact fastcode_of_div ⟨138, by decide⟩ _ _ _
    ((alnId_138 j hj) ▸ Q2.listedAt (⟨138, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨138, by decide⟩ : Fin 148) hj hq).1) colCertDiv_138_42_5_match


theorem leaf_138_42_10 (hp : 10 < (Q2.transData.getD 42 []).length)
    (j : Nat) (hj : j < (repChars.getD 138 []).length)
    (hq : (normIsRep.getD 138 []).getD j false = true) :
    species (Q2.reps (⟨42, by decide⟩ : Fin 148)) (colE2 ⟨42, by decide⟩ 10 hp)
        (rowE2 (⟨138, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨42, by decide⟩ : Fin 148))
        (colE1 ⟨42, by decide⟩ 10 (transLenTr ⟨42, by decide⟩ 10 hp))
        (rowE1 (⟨138, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨138, by decide⟩ : Fin 148) ⟨42, by decide⟩ _
      (validAt ⟨138, by decide⟩ (listedAt ⟨138, by decide⟩ hj))
      (colE1 ⟨42, by decide⟩ 10 (transLenTr ⟨42, by decide⟩ 10 hp)) T138_42
      hfix138_42 hinj138_42 hcardT138_42
      (fun i => conj_mem_of_fixedPoints _ _ (T138_42 i) (hfix138_42 i) _)
      ⟨138, by decide⟩ ⟨42, by decide⟩ _
      (Q2.validAt ⟨138, by decide⟩ (Q2.listedAt ⟨138, by decide⟩
        (alnCheck_rep ⟨138, by decide⟩ hj hq).1))
      (colE2 ⟨42, by decide⟩ 10 hp) Q2.T138_42_2 Q2.hfix138_42_2 Q2.hinj138_42_2
      Q2.hcardT138_42_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T138_42_2 i) (Q2.hfix138_42_2 i) _)
      ?_).symm
  rw [show colData1 (⟨138, by decide⟩ : Fin 148)
        ((colE1 ⟨42, by decide⟩ 10 (transLenTr ⟨42, by decide⟩ 10 hp) : ↥(reps ⟨42, by decide⟩)) : Coordinate 1)
        T138_42 = colFn colCertDiv_138_42_10.D1 (m := 5) from colCertDiv_138_42_10.bind1,
    show colData2 (⟨138, by decide⟩ : Fin 148)
        ((colE2 ⟨42, by decide⟩ 10 hp : ↥(Q2.reps ⟨42, by decide⟩)) : Coordinate 2)
        Q2.T138_42_2 = colFn colCertDiv_138_42_10.D2 (m := 5) from colCertDiv_138_42_10.bind2]
  rw [alnId_138 j hj]
  exact fastcode_of_div ⟨138, by decide⟩ _ _ _
    ((alnId_138 j hj) ▸ Q2.listedAt (⟨138, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨138, by decide⟩ : Fin 148) hj hq).1) colCertDiv_138_42_10_match


theorem leaf_138_42_15 (hp : 15 < (Q2.transData.getD 42 []).length)
    (j : Nat) (hj : j < (repChars.getD 138 []).length)
    (hq : (normIsRep.getD 138 []).getD j false = true) :
    species (Q2.reps (⟨42, by decide⟩ : Fin 148)) (colE2 ⟨42, by decide⟩ 15 hp)
        (rowE2 (⟨138, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨42, by decide⟩ : Fin 148))
        (colE1 ⟨42, by decide⟩ 15 (transLenTr ⟨42, by decide⟩ 15 hp))
        (rowE1 (⟨138, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨138, by decide⟩ : Fin 148) ⟨42, by decide⟩ _
      (validAt ⟨138, by decide⟩ (listedAt ⟨138, by decide⟩ hj))
      (colE1 ⟨42, by decide⟩ 15 (transLenTr ⟨42, by decide⟩ 15 hp)) T138_42
      hfix138_42 hinj138_42 hcardT138_42
      (fun i => conj_mem_of_fixedPoints _ _ (T138_42 i) (hfix138_42 i) _)
      ⟨138, by decide⟩ ⟨42, by decide⟩ _
      (Q2.validAt ⟨138, by decide⟩ (Q2.listedAt ⟨138, by decide⟩
        (alnCheck_rep ⟨138, by decide⟩ hj hq).1))
      (colE2 ⟨42, by decide⟩ 15 hp) Q2.T138_42_2 Q2.hfix138_42_2 Q2.hinj138_42_2
      Q2.hcardT138_42_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T138_42_2 i) (Q2.hfix138_42_2 i) _)
      ?_).symm
  rw [show colData1 (⟨138, by decide⟩ : Fin 148)
        ((colE1 ⟨42, by decide⟩ 15 (transLenTr ⟨42, by decide⟩ 15 hp) : ↥(reps ⟨42, by decide⟩)) : Coordinate 1)
        T138_42 = colFn colCertDiv_138_42_15.D1 (m := 5) from colCertDiv_138_42_15.bind1,
    show colData2 (⟨138, by decide⟩ : Fin 148)
        ((colE2 ⟨42, by decide⟩ 15 hp : ↥(Q2.reps ⟨42, by decide⟩)) : Coordinate 2)
        Q2.T138_42_2 = colFn colCertDiv_138_42_15.D2 (m := 5) from colCertDiv_138_42_15.bind2]
  rw [alnId_138 j hj]
  exact fastcode_of_div ⟨138, by decide⟩ _ _ _
    ((alnId_138 j hj) ▸ Q2.listedAt (⟨138, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨138, by decide⟩ : Fin 148) hj hq).1) colCertDiv_138_42_15_match


theorem leaf_138_42_20 (hp : 20 < (Q2.transData.getD 42 []).length)
    (j : Nat) (hj : j < (repChars.getD 138 []).length)
    (hq : (normIsRep.getD 138 []).getD j false = true) :
    species (Q2.reps (⟨42, by decide⟩ : Fin 148)) (colE2 ⟨42, by decide⟩ 20 hp)
        (rowE2 (⟨138, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨42, by decide⟩ : Fin 148))
        (colE1 ⟨42, by decide⟩ 20 (transLenTr ⟨42, by decide⟩ 20 hp))
        (rowE1 (⟨138, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨138, by decide⟩ : Fin 148) ⟨42, by decide⟩ _
      (validAt ⟨138, by decide⟩ (listedAt ⟨138, by decide⟩ hj))
      (colE1 ⟨42, by decide⟩ 20 (transLenTr ⟨42, by decide⟩ 20 hp)) T138_42
      hfix138_42 hinj138_42 hcardT138_42
      (fun i => conj_mem_of_fixedPoints _ _ (T138_42 i) (hfix138_42 i) _)
      ⟨138, by decide⟩ ⟨42, by decide⟩ _
      (Q2.validAt ⟨138, by decide⟩ (Q2.listedAt ⟨138, by decide⟩
        (alnCheck_rep ⟨138, by decide⟩ hj hq).1))
      (colE2 ⟨42, by decide⟩ 20 hp) Q2.T138_42_2 Q2.hfix138_42_2 Q2.hinj138_42_2
      Q2.hcardT138_42_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T138_42_2 i) (Q2.hfix138_42_2 i) _)
      ?_).symm
  rw [show colData1 (⟨138, by decide⟩ : Fin 148)
        ((colE1 ⟨42, by decide⟩ 20 (transLenTr ⟨42, by decide⟩ 20 hp) : ↥(reps ⟨42, by decide⟩)) : Coordinate 1)
        T138_42 = colFn colCertDiv_138_42_20.D1 (m := 5) from colCertDiv_138_42_20.bind1,
    show colData2 (⟨138, by decide⟩ : Fin 148)
        ((colE2 ⟨42, by decide⟩ 20 hp : ↥(Q2.reps ⟨42, by decide⟩)) : Coordinate 2)
        Q2.T138_42_2 = colFn colCertDiv_138_42_20.D2 (m := 5) from colCertDiv_138_42_20.bind2]
  rw [alnId_138 j hj]
  exact fastcode_of_div ⟨138, by decide⟩ _ _ _
    ((alnId_138 j hj) ▸ Q2.listedAt (⟨138, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨138, by decide⟩ : Fin 148) hj hq).1) colCertDiv_138_42_20_match


theorem leaf_138_44_0 (hp : 0 < (Q2.transData.getD 44 []).length)
    (j : Nat) (hj : j < (repChars.getD 138 []).length)
    (hq : (normIsRep.getD 138 []).getD j false = true) :
    species (Q2.reps (⟨44, by decide⟩ : Fin 148)) (colE2 ⟨44, by decide⟩ 0 hp)
        (rowE2 (⟨138, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨44, by decide⟩ : Fin 148))
        (colE1 ⟨44, by decide⟩ 0 (transLenTr ⟨44, by decide⟩ 0 hp))
        (rowE1 (⟨138, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨138, by decide⟩ : Fin 148) ⟨44, by decide⟩ _
      (validAt ⟨138, by decide⟩ (listedAt ⟨138, by decide⟩ hj))
      (colE1 ⟨44, by decide⟩ 0 (transLenTr ⟨44, by decide⟩ 0 hp)) T138_44
      hfix138_44 hinj138_44 hcardT138_44
      (fun i => conj_mem_of_fixedPoints _ _ (T138_44 i) (hfix138_44 i) _)
      ⟨138, by decide⟩ ⟨44, by decide⟩ _
      (Q2.validAt ⟨138, by decide⟩ (Q2.listedAt ⟨138, by decide⟩
        (alnCheck_rep ⟨138, by decide⟩ hj hq).1))
      (colE2 ⟨44, by decide⟩ 0 hp) Q2.T138_44_2 Q2.hfix138_44_2 Q2.hinj138_44_2
      Q2.hcardT138_44_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T138_44_2 i) (Q2.hfix138_44_2 i) _)
      colCert_138_44_0.hD ?_).symm
  rw [alnId_138 j hj]


theorem leaf_138_44_1 (hp : 1 < (Q2.transData.getD 44 []).length)
    (j : Nat) (hj : j < (repChars.getD 138 []).length)
    (hq : (normIsRep.getD 138 []).getD j false = true) :
    species (Q2.reps (⟨44, by decide⟩ : Fin 148)) (colE2 ⟨44, by decide⟩ 1 hp)
        (rowE2 (⟨138, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨44, by decide⟩ : Fin 148))
        (colE1 ⟨44, by decide⟩ 1 (transLenTr ⟨44, by decide⟩ 1 hp))
        (rowE1 (⟨138, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨138, by decide⟩ : Fin 148) ⟨44, by decide⟩ _
      (validAt ⟨138, by decide⟩ (listedAt ⟨138, by decide⟩ hj))
      (colE1 ⟨44, by decide⟩ 1 (transLenTr ⟨44, by decide⟩ 1 hp)) T138_44
      hfix138_44 hinj138_44 hcardT138_44
      (fun i => conj_mem_of_fixedPoints _ _ (T138_44 i) (hfix138_44 i) _)
      ⟨138, by decide⟩ ⟨44, by decide⟩ _
      (Q2.validAt ⟨138, by decide⟩ (Q2.listedAt ⟨138, by decide⟩
        (alnCheck_rep ⟨138, by decide⟩ hj hq).1))
      (colE2 ⟨44, by decide⟩ 1 hp) Q2.T138_44_2 Q2.hfix138_44_2 Q2.hinj138_44_2
      Q2.hcardT138_44_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T138_44_2 i) (Q2.hfix138_44_2 i) _)
      colCert_138_44_1.hD ?_).symm
  rw [alnId_138 j hj]


theorem leaf_138_44_2 (hp : 2 < (Q2.transData.getD 44 []).length)
    (j : Nat) (hj : j < (repChars.getD 138 []).length)
    (hq : (normIsRep.getD 138 []).getD j false = true) :
    species (Q2.reps (⟨44, by decide⟩ : Fin 148)) (colE2 ⟨44, by decide⟩ 2 hp)
        (rowE2 (⟨138, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨44, by decide⟩ : Fin 148))
        (colE1 ⟨44, by decide⟩ 2 (transLenTr ⟨44, by decide⟩ 2 hp))
        (rowE1 (⟨138, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨138, by decide⟩ : Fin 148) ⟨44, by decide⟩ _
      (validAt ⟨138, by decide⟩ (listedAt ⟨138, by decide⟩ hj))
      (colE1 ⟨44, by decide⟩ 2 (transLenTr ⟨44, by decide⟩ 2 hp)) T138_44
      hfix138_44 hinj138_44 hcardT138_44
      (fun i => conj_mem_of_fixedPoints _ _ (T138_44 i) (hfix138_44 i) _)
      ⟨138, by decide⟩ ⟨44, by decide⟩ _
      (Q2.validAt ⟨138, by decide⟩ (Q2.listedAt ⟨138, by decide⟩
        (alnCheck_rep ⟨138, by decide⟩ hj hq).1))
      (colE2 ⟨44, by decide⟩ 2 hp) Q2.T138_44_2 Q2.hfix138_44_2 Q2.hinj138_44_2
      Q2.hcardT138_44_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T138_44_2 i) (Q2.hfix138_44_2 i) _)
      colCert_138_44_2.hD ?_).symm
  rw [alnId_138 j hj]


theorem leaf_138_44_3 (hp : 3 < (Q2.transData.getD 44 []).length)
    (j : Nat) (hj : j < (repChars.getD 138 []).length)
    (hq : (normIsRep.getD 138 []).getD j false = true) :
    species (Q2.reps (⟨44, by decide⟩ : Fin 148)) (colE2 ⟨44, by decide⟩ 3 hp)
        (rowE2 (⟨138, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨44, by decide⟩ : Fin 148))
        (colE1 ⟨44, by decide⟩ 3 (transLenTr ⟨44, by decide⟩ 3 hp))
        (rowE1 (⟨138, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨138, by decide⟩ : Fin 148) ⟨44, by decide⟩ _
      (validAt ⟨138, by decide⟩ (listedAt ⟨138, by decide⟩ hj))
      (colE1 ⟨44, by decide⟩ 3 (transLenTr ⟨44, by decide⟩ 3 hp)) T138_44
      hfix138_44 hinj138_44 hcardT138_44
      (fun i => conj_mem_of_fixedPoints _ _ (T138_44 i) (hfix138_44 i) _)
      ⟨138, by decide⟩ ⟨44, by decide⟩ _
      (Q2.validAt ⟨138, by decide⟩ (Q2.listedAt ⟨138, by decide⟩
        (alnCheck_rep ⟨138, by decide⟩ hj hq).1))
      (colE2 ⟨44, by decide⟩ 3 hp) Q2.T138_44_2 Q2.hfix138_44_2 Q2.hinj138_44_2
      Q2.hcardT138_44_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T138_44_2 i) (Q2.hfix138_44_2 i) _)
      colCert_138_44_3.hD ?_).symm
  rw [alnId_138 j hj]


theorem leaf_138_44_4 (hp : 4 < (Q2.transData.getD 44 []).length)
    (j : Nat) (hj : j < (repChars.getD 138 []).length)
    (hq : (normIsRep.getD 138 []).getD j false = true) :
    species (Q2.reps (⟨44, by decide⟩ : Fin 148)) (colE2 ⟨44, by decide⟩ 4 hp)
        (rowE2 (⟨138, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨44, by decide⟩ : Fin 148))
        (colE1 ⟨44, by decide⟩ 4 (transLenTr ⟨44, by decide⟩ 4 hp))
        (rowE1 (⟨138, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨138, by decide⟩ : Fin 148) ⟨44, by decide⟩ _
      (validAt ⟨138, by decide⟩ (listedAt ⟨138, by decide⟩ hj))
      (colE1 ⟨44, by decide⟩ 4 (transLenTr ⟨44, by decide⟩ 4 hp)) T138_44
      hfix138_44 hinj138_44 hcardT138_44
      (fun i => conj_mem_of_fixedPoints _ _ (T138_44 i) (hfix138_44 i) _)
      ⟨138, by decide⟩ ⟨44, by decide⟩ _
      (Q2.validAt ⟨138, by decide⟩ (Q2.listedAt ⟨138, by decide⟩
        (alnCheck_rep ⟨138, by decide⟩ hj hq).1))
      (colE2 ⟨44, by decide⟩ 4 hp) Q2.T138_44_2 Q2.hfix138_44_2 Q2.hinj138_44_2
      Q2.hcardT138_44_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T138_44_2 i) (Q2.hfix138_44_2 i) _)
      colCert_138_44_4.hD ?_).symm
  rw [alnId_138 j hj]


theorem leaf_138_44_5 (hp : 5 < (Q2.transData.getD 44 []).length)
    (j : Nat) (hj : j < (repChars.getD 138 []).length)
    (hq : (normIsRep.getD 138 []).getD j false = true) :
    species (Q2.reps (⟨44, by decide⟩ : Fin 148)) (colE2 ⟨44, by decide⟩ 5 hp)
        (rowE2 (⟨138, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨44, by decide⟩ : Fin 148))
        (colE1 ⟨44, by decide⟩ 5 (transLenTr ⟨44, by decide⟩ 5 hp))
        (rowE1 (⟨138, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨138, by decide⟩ : Fin 148) ⟨44, by decide⟩ _
      (validAt ⟨138, by decide⟩ (listedAt ⟨138, by decide⟩ hj))
      (colE1 ⟨44, by decide⟩ 5 (transLenTr ⟨44, by decide⟩ 5 hp)) T138_44
      hfix138_44 hinj138_44 hcardT138_44
      (fun i => conj_mem_of_fixedPoints _ _ (T138_44 i) (hfix138_44 i) _)
      ⟨138, by decide⟩ ⟨44, by decide⟩ _
      (Q2.validAt ⟨138, by decide⟩ (Q2.listedAt ⟨138, by decide⟩
        (alnCheck_rep ⟨138, by decide⟩ hj hq).1))
      (colE2 ⟨44, by decide⟩ 5 hp) Q2.T138_44_2 Q2.hfix138_44_2 Q2.hinj138_44_2
      Q2.hcardT138_44_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T138_44_2 i) (Q2.hfix138_44_2 i) _)
      ?_).symm
  rw [show colData1 (⟨138, by decide⟩ : Fin 148)
        ((colE1 ⟨44, by decide⟩ 5 (transLenTr ⟨44, by decide⟩ 5 hp) : ↥(reps ⟨44, by decide⟩)) : Coordinate 1)
        T138_44 = colFn colCertDiv_138_44_5.D1 (m := 5) from colCertDiv_138_44_5.bind1,
    show colData2 (⟨138, by decide⟩ : Fin 148)
        ((colE2 ⟨44, by decide⟩ 5 hp : ↥(Q2.reps ⟨44, by decide⟩)) : Coordinate 2)
        Q2.T138_44_2 = colFn colCertDiv_138_44_5.D2 (m := 5) from colCertDiv_138_44_5.bind2]
  rw [alnId_138 j hj]
  exact fastcode_of_div ⟨138, by decide⟩ _ _ _
    ((alnId_138 j hj) ▸ Q2.listedAt (⟨138, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨138, by decide⟩ : Fin 148) hj hq).1) colCertDiv_138_44_5_match


theorem leaf_138_44_10 (hp : 10 < (Q2.transData.getD 44 []).length)
    (j : Nat) (hj : j < (repChars.getD 138 []).length)
    (hq : (normIsRep.getD 138 []).getD j false = true) :
    species (Q2.reps (⟨44, by decide⟩ : Fin 148)) (colE2 ⟨44, by decide⟩ 10 hp)
        (rowE2 (⟨138, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨44, by decide⟩ : Fin 148))
        (colE1 ⟨44, by decide⟩ 10 (transLenTr ⟨44, by decide⟩ 10 hp))
        (rowE1 (⟨138, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨138, by decide⟩ : Fin 148) ⟨44, by decide⟩ _
      (validAt ⟨138, by decide⟩ (listedAt ⟨138, by decide⟩ hj))
      (colE1 ⟨44, by decide⟩ 10 (transLenTr ⟨44, by decide⟩ 10 hp)) T138_44
      hfix138_44 hinj138_44 hcardT138_44
      (fun i => conj_mem_of_fixedPoints _ _ (T138_44 i) (hfix138_44 i) _)
      ⟨138, by decide⟩ ⟨44, by decide⟩ _
      (Q2.validAt ⟨138, by decide⟩ (Q2.listedAt ⟨138, by decide⟩
        (alnCheck_rep ⟨138, by decide⟩ hj hq).1))
      (colE2 ⟨44, by decide⟩ 10 hp) Q2.T138_44_2 Q2.hfix138_44_2 Q2.hinj138_44_2
      Q2.hcardT138_44_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T138_44_2 i) (Q2.hfix138_44_2 i) _)
      ?_).symm
  rw [show colData1 (⟨138, by decide⟩ : Fin 148)
        ((colE1 ⟨44, by decide⟩ 10 (transLenTr ⟨44, by decide⟩ 10 hp) : ↥(reps ⟨44, by decide⟩)) : Coordinate 1)
        T138_44 = colFn colCertDiv_138_44_10.D1 (m := 5) from colCertDiv_138_44_10.bind1,
    show colData2 (⟨138, by decide⟩ : Fin 148)
        ((colE2 ⟨44, by decide⟩ 10 hp : ↥(Q2.reps ⟨44, by decide⟩)) : Coordinate 2)
        Q2.T138_44_2 = colFn colCertDiv_138_44_10.D2 (m := 5) from colCertDiv_138_44_10.bind2]
  rw [alnId_138 j hj]
  exact fastcode_of_div ⟨138, by decide⟩ _ _ _
    ((alnId_138 j hj) ▸ Q2.listedAt (⟨138, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨138, by decide⟩ : Fin 148) hj hq).1) colCertDiv_138_44_10_match


theorem leaf_138_44_15 (hp : 15 < (Q2.transData.getD 44 []).length)
    (j : Nat) (hj : j < (repChars.getD 138 []).length)
    (hq : (normIsRep.getD 138 []).getD j false = true) :
    species (Q2.reps (⟨44, by decide⟩ : Fin 148)) (colE2 ⟨44, by decide⟩ 15 hp)
        (rowE2 (⟨138, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨44, by decide⟩ : Fin 148))
        (colE1 ⟨44, by decide⟩ 15 (transLenTr ⟨44, by decide⟩ 15 hp))
        (rowE1 (⟨138, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨138, by decide⟩ : Fin 148) ⟨44, by decide⟩ _
      (validAt ⟨138, by decide⟩ (listedAt ⟨138, by decide⟩ hj))
      (colE1 ⟨44, by decide⟩ 15 (transLenTr ⟨44, by decide⟩ 15 hp)) T138_44
      hfix138_44 hinj138_44 hcardT138_44
      (fun i => conj_mem_of_fixedPoints _ _ (T138_44 i) (hfix138_44 i) _)
      ⟨138, by decide⟩ ⟨44, by decide⟩ _
      (Q2.validAt ⟨138, by decide⟩ (Q2.listedAt ⟨138, by decide⟩
        (alnCheck_rep ⟨138, by decide⟩ hj hq).1))
      (colE2 ⟨44, by decide⟩ 15 hp) Q2.T138_44_2 Q2.hfix138_44_2 Q2.hinj138_44_2
      Q2.hcardT138_44_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T138_44_2 i) (Q2.hfix138_44_2 i) _)
      ?_).symm
  rw [show colData1 (⟨138, by decide⟩ : Fin 148)
        ((colE1 ⟨44, by decide⟩ 15 (transLenTr ⟨44, by decide⟩ 15 hp) : ↥(reps ⟨44, by decide⟩)) : Coordinate 1)
        T138_44 = colFn colCertDiv_138_44_15.D1 (m := 5) from colCertDiv_138_44_15.bind1,
    show colData2 (⟨138, by decide⟩ : Fin 148)
        ((colE2 ⟨44, by decide⟩ 15 hp : ↥(Q2.reps ⟨44, by decide⟩)) : Coordinate 2)
        Q2.T138_44_2 = colFn colCertDiv_138_44_15.D2 (m := 5) from colCertDiv_138_44_15.bind2]
  rw [alnId_138 j hj]
  exact fastcode_of_div ⟨138, by decide⟩ _ _ _
    ((alnId_138 j hj) ▸ Q2.listedAt (⟨138, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨138, by decide⟩ : Fin 148) hj hq).1) colCertDiv_138_44_15_match


theorem leaf_138_44_20 (hp : 20 < (Q2.transData.getD 44 []).length)
    (j : Nat) (hj : j < (repChars.getD 138 []).length)
    (hq : (normIsRep.getD 138 []).getD j false = true) :
    species (Q2.reps (⟨44, by decide⟩ : Fin 148)) (colE2 ⟨44, by decide⟩ 20 hp)
        (rowE2 (⟨138, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨44, by decide⟩ : Fin 148))
        (colE1 ⟨44, by decide⟩ 20 (transLenTr ⟨44, by decide⟩ 20 hp))
        (rowE1 (⟨138, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨138, by decide⟩ : Fin 148) ⟨44, by decide⟩ _
      (validAt ⟨138, by decide⟩ (listedAt ⟨138, by decide⟩ hj))
      (colE1 ⟨44, by decide⟩ 20 (transLenTr ⟨44, by decide⟩ 20 hp)) T138_44
      hfix138_44 hinj138_44 hcardT138_44
      (fun i => conj_mem_of_fixedPoints _ _ (T138_44 i) (hfix138_44 i) _)
      ⟨138, by decide⟩ ⟨44, by decide⟩ _
      (Q2.validAt ⟨138, by decide⟩ (Q2.listedAt ⟨138, by decide⟩
        (alnCheck_rep ⟨138, by decide⟩ hj hq).1))
      (colE2 ⟨44, by decide⟩ 20 hp) Q2.T138_44_2 Q2.hfix138_44_2 Q2.hinj138_44_2
      Q2.hcardT138_44_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T138_44_2 i) (Q2.hfix138_44_2 i) _)
      colCert_138_44_20.hD ?_).symm
  rw [alnId_138 j hj]


theorem leaf_138_50_0 (hp : 0 < (Q2.transData.getD 50 []).length)
    (j : Nat) (hj : j < (repChars.getD 138 []).length)
    (hq : (normIsRep.getD 138 []).getD j false = true) :
    species (Q2.reps (⟨50, by decide⟩ : Fin 148)) (colE2 ⟨50, by decide⟩ 0 hp)
        (rowE2 (⟨138, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨50, by decide⟩ : Fin 148))
        (colE1 ⟨50, by decide⟩ 0 (transLenTr ⟨50, by decide⟩ 0 hp))
        (rowE1 (⟨138, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨138, by decide⟩ : Fin 148) ⟨50, by decide⟩ _
      (validAt ⟨138, by decide⟩ (listedAt ⟨138, by decide⟩ hj))
      (colE1 ⟨50, by decide⟩ 0 (transLenTr ⟨50, by decide⟩ 0 hp)) T138_50
      hfix138_50 hinj138_50 hcardT138_50
      (fun i => conj_mem_of_fixedPoints _ _ (T138_50 i) (hfix138_50 i) _)
      ⟨138, by decide⟩ ⟨50, by decide⟩ _
      (Q2.validAt ⟨138, by decide⟩ (Q2.listedAt ⟨138, by decide⟩
        (alnCheck_rep ⟨138, by decide⟩ hj hq).1))
      (colE2 ⟨50, by decide⟩ 0 hp) Q2.T138_50_2 Q2.hfix138_50_2 Q2.hinj138_50_2
      Q2.hcardT138_50_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T138_50_2 i) (Q2.hfix138_50_2 i) _)
      colCert_138_50_0.hD ?_).symm
  rw [alnId_138 j hj]


theorem leaf_138_50_1 (hp : 1 < (Q2.transData.getD 50 []).length)
    (j : Nat) (hj : j < (repChars.getD 138 []).length)
    (hq : (normIsRep.getD 138 []).getD j false = true) :
    species (Q2.reps (⟨50, by decide⟩ : Fin 148)) (colE2 ⟨50, by decide⟩ 1 hp)
        (rowE2 (⟨138, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨50, by decide⟩ : Fin 148))
        (colE1 ⟨50, by decide⟩ 1 (transLenTr ⟨50, by decide⟩ 1 hp))
        (rowE1 (⟨138, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨138, by decide⟩ : Fin 148) ⟨50, by decide⟩ _
      (validAt ⟨138, by decide⟩ (listedAt ⟨138, by decide⟩ hj))
      (colE1 ⟨50, by decide⟩ 1 (transLenTr ⟨50, by decide⟩ 1 hp)) T138_50
      hfix138_50 hinj138_50 hcardT138_50
      (fun i => conj_mem_of_fixedPoints _ _ (T138_50 i) (hfix138_50 i) _)
      ⟨138, by decide⟩ ⟨50, by decide⟩ _
      (Q2.validAt ⟨138, by decide⟩ (Q2.listedAt ⟨138, by decide⟩
        (alnCheck_rep ⟨138, by decide⟩ hj hq).1))
      (colE2 ⟨50, by decide⟩ 1 hp) Q2.T138_50_2 Q2.hfix138_50_2 Q2.hinj138_50_2
      Q2.hcardT138_50_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T138_50_2 i) (Q2.hfix138_50_2 i) _)
      colCert_138_50_1.hD ?_).symm
  rw [alnId_138 j hj]


theorem leaf_138_50_2 (hp : 2 < (Q2.transData.getD 50 []).length)
    (j : Nat) (hj : j < (repChars.getD 138 []).length)
    (hq : (normIsRep.getD 138 []).getD j false = true) :
    species (Q2.reps (⟨50, by decide⟩ : Fin 148)) (colE2 ⟨50, by decide⟩ 2 hp)
        (rowE2 (⟨138, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨50, by decide⟩ : Fin 148))
        (colE1 ⟨50, by decide⟩ 2 (transLenTr ⟨50, by decide⟩ 2 hp))
        (rowE1 (⟨138, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨138, by decide⟩ : Fin 148) ⟨50, by decide⟩ _
      (validAt ⟨138, by decide⟩ (listedAt ⟨138, by decide⟩ hj))
      (colE1 ⟨50, by decide⟩ 2 (transLenTr ⟨50, by decide⟩ 2 hp)) T138_50
      hfix138_50 hinj138_50 hcardT138_50
      (fun i => conj_mem_of_fixedPoints _ _ (T138_50 i) (hfix138_50 i) _)
      ⟨138, by decide⟩ ⟨50, by decide⟩ _
      (Q2.validAt ⟨138, by decide⟩ (Q2.listedAt ⟨138, by decide⟩
        (alnCheck_rep ⟨138, by decide⟩ hj hq).1))
      (colE2 ⟨50, by decide⟩ 2 hp) Q2.T138_50_2 Q2.hfix138_50_2 Q2.hinj138_50_2
      Q2.hcardT138_50_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T138_50_2 i) (Q2.hfix138_50_2 i) _)
      colCert_138_50_2.hD ?_).symm
  rw [alnId_138 j hj]


theorem leaf_138_50_3 (hp : 3 < (Q2.transData.getD 50 []).length)
    (j : Nat) (hj : j < (repChars.getD 138 []).length)
    (hq : (normIsRep.getD 138 []).getD j false = true) :
    species (Q2.reps (⟨50, by decide⟩ : Fin 148)) (colE2 ⟨50, by decide⟩ 3 hp)
        (rowE2 (⟨138, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨50, by decide⟩ : Fin 148))
        (colE1 ⟨50, by decide⟩ 3 (transLenTr ⟨50, by decide⟩ 3 hp))
        (rowE1 (⟨138, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨138, by decide⟩ : Fin 148) ⟨50, by decide⟩ _
      (validAt ⟨138, by decide⟩ (listedAt ⟨138, by decide⟩ hj))
      (colE1 ⟨50, by decide⟩ 3 (transLenTr ⟨50, by decide⟩ 3 hp)) T138_50
      hfix138_50 hinj138_50 hcardT138_50
      (fun i => conj_mem_of_fixedPoints _ _ (T138_50 i) (hfix138_50 i) _)
      ⟨138, by decide⟩ ⟨50, by decide⟩ _
      (Q2.validAt ⟨138, by decide⟩ (Q2.listedAt ⟨138, by decide⟩
        (alnCheck_rep ⟨138, by decide⟩ hj hq).1))
      (colE2 ⟨50, by decide⟩ 3 hp) Q2.T138_50_2 Q2.hfix138_50_2 Q2.hinj138_50_2
      Q2.hcardT138_50_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T138_50_2 i) (Q2.hfix138_50_2 i) _)
      colCert_138_50_3.hD ?_).symm
  rw [alnId_138 j hj]


theorem leaf_138_50_4 (hp : 4 < (Q2.transData.getD 50 []).length)
    (j : Nat) (hj : j < (repChars.getD 138 []).length)
    (hq : (normIsRep.getD 138 []).getD j false = true) :
    species (Q2.reps (⟨50, by decide⟩ : Fin 148)) (colE2 ⟨50, by decide⟩ 4 hp)
        (rowE2 (⟨138, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨50, by decide⟩ : Fin 148))
        (colE1 ⟨50, by decide⟩ 4 (transLenTr ⟨50, by decide⟩ 4 hp))
        (rowE1 (⟨138, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨138, by decide⟩ : Fin 148) ⟨50, by decide⟩ _
      (validAt ⟨138, by decide⟩ (listedAt ⟨138, by decide⟩ hj))
      (colE1 ⟨50, by decide⟩ 4 (transLenTr ⟨50, by decide⟩ 4 hp)) T138_50
      hfix138_50 hinj138_50 hcardT138_50
      (fun i => conj_mem_of_fixedPoints _ _ (T138_50 i) (hfix138_50 i) _)
      ⟨138, by decide⟩ ⟨50, by decide⟩ _
      (Q2.validAt ⟨138, by decide⟩ (Q2.listedAt ⟨138, by decide⟩
        (alnCheck_rep ⟨138, by decide⟩ hj hq).1))
      (colE2 ⟨50, by decide⟩ 4 hp) Q2.T138_50_2 Q2.hfix138_50_2 Q2.hinj138_50_2
      Q2.hcardT138_50_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T138_50_2 i) (Q2.hfix138_50_2 i) _)
      colCert_138_50_4.hD ?_).symm
  rw [alnId_138 j hj]


theorem leaf_138_50_5 (hp : 5 < (Q2.transData.getD 50 []).length)
    (j : Nat) (hj : j < (repChars.getD 138 []).length)
    (hq : (normIsRep.getD 138 []).getD j false = true) :
    species (Q2.reps (⟨50, by decide⟩ : Fin 148)) (colE2 ⟨50, by decide⟩ 5 hp)
        (rowE2 (⟨138, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨50, by decide⟩ : Fin 148))
        (colE1 ⟨50, by decide⟩ 5 (transLenTr ⟨50, by decide⟩ 5 hp))
        (rowE1 (⟨138, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨138, by decide⟩ : Fin 148) ⟨50, by decide⟩ _
      (validAt ⟨138, by decide⟩ (listedAt ⟨138, by decide⟩ hj))
      (colE1 ⟨50, by decide⟩ 5 (transLenTr ⟨50, by decide⟩ 5 hp)) T138_50
      hfix138_50 hinj138_50 hcardT138_50
      (fun i => conj_mem_of_fixedPoints _ _ (T138_50 i) (hfix138_50 i) _)
      ⟨138, by decide⟩ ⟨50, by decide⟩ _
      (Q2.validAt ⟨138, by decide⟩ (Q2.listedAt ⟨138, by decide⟩
        (alnCheck_rep ⟨138, by decide⟩ hj hq).1))
      (colE2 ⟨50, by decide⟩ 5 hp) Q2.T138_50_2 Q2.hfix138_50_2 Q2.hinj138_50_2
      Q2.hcardT138_50_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T138_50_2 i) (Q2.hfix138_50_2 i) _)
      ?_).symm
  rw [show colData1 (⟨138, by decide⟩ : Fin 148)
        ((colE1 ⟨50, by decide⟩ 5 (transLenTr ⟨50, by decide⟩ 5 hp) : ↥(reps ⟨50, by decide⟩)) : Coordinate 1)
        T138_50 = colFn colCertDiv_138_50_5.D1 (m := 5) from colCertDiv_138_50_5.bind1,
    show colData2 (⟨138, by decide⟩ : Fin 148)
        ((colE2 ⟨50, by decide⟩ 5 hp : ↥(Q2.reps ⟨50, by decide⟩)) : Coordinate 2)
        Q2.T138_50_2 = colFn colCertDiv_138_50_5.D2 (m := 5) from colCertDiv_138_50_5.bind2]
  rw [alnId_138 j hj]
  exact fastcode_of_div ⟨138, by decide⟩ _ _ _
    ((alnId_138 j hj) ▸ Q2.listedAt (⟨138, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨138, by decide⟩ : Fin 148) hj hq).1) colCertDiv_138_50_5_match


theorem leaf_138_50_10 (hp : 10 < (Q2.transData.getD 50 []).length)
    (j : Nat) (hj : j < (repChars.getD 138 []).length)
    (hq : (normIsRep.getD 138 []).getD j false = true) :
    species (Q2.reps (⟨50, by decide⟩ : Fin 148)) (colE2 ⟨50, by decide⟩ 10 hp)
        (rowE2 (⟨138, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨50, by decide⟩ : Fin 148))
        (colE1 ⟨50, by decide⟩ 10 (transLenTr ⟨50, by decide⟩ 10 hp))
        (rowE1 (⟨138, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨138, by decide⟩ : Fin 148) ⟨50, by decide⟩ _
      (validAt ⟨138, by decide⟩ (listedAt ⟨138, by decide⟩ hj))
      (colE1 ⟨50, by decide⟩ 10 (transLenTr ⟨50, by decide⟩ 10 hp)) T138_50
      hfix138_50 hinj138_50 hcardT138_50
      (fun i => conj_mem_of_fixedPoints _ _ (T138_50 i) (hfix138_50 i) _)
      ⟨138, by decide⟩ ⟨50, by decide⟩ _
      (Q2.validAt ⟨138, by decide⟩ (Q2.listedAt ⟨138, by decide⟩
        (alnCheck_rep ⟨138, by decide⟩ hj hq).1))
      (colE2 ⟨50, by decide⟩ 10 hp) Q2.T138_50_2 Q2.hfix138_50_2 Q2.hinj138_50_2
      Q2.hcardT138_50_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T138_50_2 i) (Q2.hfix138_50_2 i) _)
      ?_).symm
  rw [show colData1 (⟨138, by decide⟩ : Fin 148)
        ((colE1 ⟨50, by decide⟩ 10 (transLenTr ⟨50, by decide⟩ 10 hp) : ↥(reps ⟨50, by decide⟩)) : Coordinate 1)
        T138_50 = colFn colCertDiv_138_50_10.D1 (m := 5) from colCertDiv_138_50_10.bind1,
    show colData2 (⟨138, by decide⟩ : Fin 148)
        ((colE2 ⟨50, by decide⟩ 10 hp : ↥(Q2.reps ⟨50, by decide⟩)) : Coordinate 2)
        Q2.T138_50_2 = colFn colCertDiv_138_50_10.D2 (m := 5) from colCertDiv_138_50_10.bind2]
  rw [alnId_138 j hj]
  exact fastcode_of_div ⟨138, by decide⟩ _ _ _
    ((alnId_138 j hj) ▸ Q2.listedAt (⟨138, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨138, by decide⟩ : Fin 148) hj hq).1) colCertDiv_138_50_10_match


theorem leaf_138_50_15 (hp : 15 < (Q2.transData.getD 50 []).length)
    (j : Nat) (hj : j < (repChars.getD 138 []).length)
    (hq : (normIsRep.getD 138 []).getD j false = true) :
    species (Q2.reps (⟨50, by decide⟩ : Fin 148)) (colE2 ⟨50, by decide⟩ 15 hp)
        (rowE2 (⟨138, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨50, by decide⟩ : Fin 148))
        (colE1 ⟨50, by decide⟩ 15 (transLenTr ⟨50, by decide⟩ 15 hp))
        (rowE1 (⟨138, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨138, by decide⟩ : Fin 148) ⟨50, by decide⟩ _
      (validAt ⟨138, by decide⟩ (listedAt ⟨138, by decide⟩ hj))
      (colE1 ⟨50, by decide⟩ 15 (transLenTr ⟨50, by decide⟩ 15 hp)) T138_50
      hfix138_50 hinj138_50 hcardT138_50
      (fun i => conj_mem_of_fixedPoints _ _ (T138_50 i) (hfix138_50 i) _)
      ⟨138, by decide⟩ ⟨50, by decide⟩ _
      (Q2.validAt ⟨138, by decide⟩ (Q2.listedAt ⟨138, by decide⟩
        (alnCheck_rep ⟨138, by decide⟩ hj hq).1))
      (colE2 ⟨50, by decide⟩ 15 hp) Q2.T138_50_2 Q2.hfix138_50_2 Q2.hinj138_50_2
      Q2.hcardT138_50_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T138_50_2 i) (Q2.hfix138_50_2 i) _)
      ?_).symm
  rw [show colData1 (⟨138, by decide⟩ : Fin 148)
        ((colE1 ⟨50, by decide⟩ 15 (transLenTr ⟨50, by decide⟩ 15 hp) : ↥(reps ⟨50, by decide⟩)) : Coordinate 1)
        T138_50 = colFn colCertDiv_138_50_15.D1 (m := 5) from colCertDiv_138_50_15.bind1,
    show colData2 (⟨138, by decide⟩ : Fin 148)
        ((colE2 ⟨50, by decide⟩ 15 hp : ↥(Q2.reps ⟨50, by decide⟩)) : Coordinate 2)
        Q2.T138_50_2 = colFn colCertDiv_138_50_15.D2 (m := 5) from colCertDiv_138_50_15.bind2]
  rw [alnId_138 j hj]
  exact fastcode_of_div ⟨138, by decide⟩ _ _ _
    ((alnId_138 j hj) ▸ Q2.listedAt (⟨138, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨138, by decide⟩ : Fin 148) hj hq).1) colCertDiv_138_50_15_match


theorem leaf_138_50_20 (hp : 20 < (Q2.transData.getD 50 []).length)
    (j : Nat) (hj : j < (repChars.getD 138 []).length)
    (hq : (normIsRep.getD 138 []).getD j false = true) :
    species (Q2.reps (⟨50, by decide⟩ : Fin 148)) (colE2 ⟨50, by decide⟩ 20 hp)
        (rowE2 (⟨138, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨50, by decide⟩ : Fin 148))
        (colE1 ⟨50, by decide⟩ 20 (transLenTr ⟨50, by decide⟩ 20 hp))
        (rowE1 (⟨138, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨138, by decide⟩ : Fin 148) ⟨50, by decide⟩ _
      (validAt ⟨138, by decide⟩ (listedAt ⟨138, by decide⟩ hj))
      (colE1 ⟨50, by decide⟩ 20 (transLenTr ⟨50, by decide⟩ 20 hp)) T138_50
      hfix138_50 hinj138_50 hcardT138_50
      (fun i => conj_mem_of_fixedPoints _ _ (T138_50 i) (hfix138_50 i) _)
      ⟨138, by decide⟩ ⟨50, by decide⟩ _
      (Q2.validAt ⟨138, by decide⟩ (Q2.listedAt ⟨138, by decide⟩
        (alnCheck_rep ⟨138, by decide⟩ hj hq).1))
      (colE2 ⟨50, by decide⟩ 20 hp) Q2.T138_50_2 Q2.hfix138_50_2 Q2.hinj138_50_2
      Q2.hcardT138_50_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T138_50_2 i) (Q2.hfix138_50_2 i) _)
      ?_).symm
  rw [show colData1 (⟨138, by decide⟩ : Fin 148)
        ((colE1 ⟨50, by decide⟩ 20 (transLenTr ⟨50, by decide⟩ 20 hp) : ↥(reps ⟨50, by decide⟩)) : Coordinate 1)
        T138_50 = colFn colCertDiv_138_50_20.D1 (m := 5) from colCertDiv_138_50_20.bind1,
    show colData2 (⟨138, by decide⟩ : Fin 148)
        ((colE2 ⟨50, by decide⟩ 20 hp : ↥(Q2.reps ⟨50, by decide⟩)) : Coordinate 2)
        Q2.T138_50_2 = colFn colCertDiv_138_50_20.D2 (m := 5) from colCertDiv_138_50_20.bind2]
  rw [alnId_138 j hj]
  exact fastcode_of_div ⟨138, by decide⟩ _ _ _
    ((alnId_138 j hj) ▸ Q2.listedAt (⟨138, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨138, by decide⟩ : Fin 148) hj hq).1) colCertDiv_138_50_20_match


theorem leaf_138_53_0 (hp : 0 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 138 []).length)
    (hq : (normIsRep.getD 138 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 0 hp)
        (rowE2 (⟨138, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 0 (transLenTr ⟨53, by decide⟩ 0 hp))
        (rowE1 (⟨138, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨138, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨138, by decide⟩ (listedAt ⟨138, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 0 (transLenTr ⟨53, by decide⟩ 0 hp)) T138_53
      hfix138_53 hinj138_53 hcardT138_53
      (fun i => conj_mem_of_fixedPoints _ _ (T138_53 i) (hfix138_53 i) _)
      ⟨138, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨138, by decide⟩ (Q2.listedAt ⟨138, by decide⟩
        (alnCheck_rep ⟨138, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 0 hp) Q2.T138_53_2 Q2.hfix138_53_2 Q2.hinj138_53_2
      Q2.hcardT138_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T138_53_2 i) (Q2.hfix138_53_2 i) _)
      colCert_138_53_0.hD ?_).symm
  rw [alnId_138 j hj]


theorem leaf_138_53_1 (hp : 1 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 138 []).length)
    (hq : (normIsRep.getD 138 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 1 hp)
        (rowE2 (⟨138, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 1 (transLenTr ⟨53, by decide⟩ 1 hp))
        (rowE1 (⟨138, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨138, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨138, by decide⟩ (listedAt ⟨138, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 1 (transLenTr ⟨53, by decide⟩ 1 hp)) T138_53
      hfix138_53 hinj138_53 hcardT138_53
      (fun i => conj_mem_of_fixedPoints _ _ (T138_53 i) (hfix138_53 i) _)
      ⟨138, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨138, by decide⟩ (Q2.listedAt ⟨138, by decide⟩
        (alnCheck_rep ⟨138, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 1 hp) Q2.T138_53_2 Q2.hfix138_53_2 Q2.hinj138_53_2
      Q2.hcardT138_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T138_53_2 i) (Q2.hfix138_53_2 i) _)
      colCert_138_53_1.hD ?_).symm
  rw [alnId_138 j hj]


theorem leaf_138_53_2 (hp : 2 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 138 []).length)
    (hq : (normIsRep.getD 138 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 2 hp)
        (rowE2 (⟨138, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 2 (transLenTr ⟨53, by decide⟩ 2 hp))
        (rowE1 (⟨138, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨138, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨138, by decide⟩ (listedAt ⟨138, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 2 (transLenTr ⟨53, by decide⟩ 2 hp)) T138_53
      hfix138_53 hinj138_53 hcardT138_53
      (fun i => conj_mem_of_fixedPoints _ _ (T138_53 i) (hfix138_53 i) _)
      ⟨138, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨138, by decide⟩ (Q2.listedAt ⟨138, by decide⟩
        (alnCheck_rep ⟨138, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 2 hp) Q2.T138_53_2 Q2.hfix138_53_2 Q2.hinj138_53_2
      Q2.hcardT138_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T138_53_2 i) (Q2.hfix138_53_2 i) _)
      colCert_138_53_2.hD ?_).symm
  rw [alnId_138 j hj]


theorem leaf_138_53_3 (hp : 3 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 138 []).length)
    (hq : (normIsRep.getD 138 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 3 hp)
        (rowE2 (⟨138, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 3 (transLenTr ⟨53, by decide⟩ 3 hp))
        (rowE1 (⟨138, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨138, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨138, by decide⟩ (listedAt ⟨138, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 3 (transLenTr ⟨53, by decide⟩ 3 hp)) T138_53
      hfix138_53 hinj138_53 hcardT138_53
      (fun i => conj_mem_of_fixedPoints _ _ (T138_53 i) (hfix138_53 i) _)
      ⟨138, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨138, by decide⟩ (Q2.listedAt ⟨138, by decide⟩
        (alnCheck_rep ⟨138, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 3 hp) Q2.T138_53_2 Q2.hfix138_53_2 Q2.hinj138_53_2
      Q2.hcardT138_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T138_53_2 i) (Q2.hfix138_53_2 i) _)
      colCert_138_53_3.hD ?_).symm
  rw [alnId_138 j hj]


theorem leaf_138_53_4 (hp : 4 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 138 []).length)
    (hq : (normIsRep.getD 138 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 4 hp)
        (rowE2 (⟨138, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 4 (transLenTr ⟨53, by decide⟩ 4 hp))
        (rowE1 (⟨138, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨138, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨138, by decide⟩ (listedAt ⟨138, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 4 (transLenTr ⟨53, by decide⟩ 4 hp)) T138_53
      hfix138_53 hinj138_53 hcardT138_53
      (fun i => conj_mem_of_fixedPoints _ _ (T138_53 i) (hfix138_53 i) _)
      ⟨138, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨138, by decide⟩ (Q2.listedAt ⟨138, by decide⟩
        (alnCheck_rep ⟨138, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 4 hp) Q2.T138_53_2 Q2.hfix138_53_2 Q2.hinj138_53_2
      Q2.hcardT138_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T138_53_2 i) (Q2.hfix138_53_2 i) _)
      colCert_138_53_4.hD ?_).symm
  rw [alnId_138 j hj]


theorem leaf_138_53_5 (hp : 5 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 138 []).length)
    (hq : (normIsRep.getD 138 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 5 hp)
        (rowE2 (⟨138, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 5 (transLenTr ⟨53, by decide⟩ 5 hp))
        (rowE1 (⟨138, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨138, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨138, by decide⟩ (listedAt ⟨138, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 5 (transLenTr ⟨53, by decide⟩ 5 hp)) T138_53
      hfix138_53 hinj138_53 hcardT138_53
      (fun i => conj_mem_of_fixedPoints _ _ (T138_53 i) (hfix138_53 i) _)
      ⟨138, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨138, by decide⟩ (Q2.listedAt ⟨138, by decide⟩
        (alnCheck_rep ⟨138, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 5 hp) Q2.T138_53_2 Q2.hfix138_53_2 Q2.hinj138_53_2
      Q2.hcardT138_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T138_53_2 i) (Q2.hfix138_53_2 i) _)
      colCert_138_53_5.hD ?_).symm
  rw [alnId_138 j hj]


theorem leaf_138_53_10 (hp : 10 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 138 []).length)
    (hq : (normIsRep.getD 138 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 10 hp)
        (rowE2 (⟨138, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 10 (transLenTr ⟨53, by decide⟩ 10 hp))
        (rowE1 (⟨138, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨138, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨138, by decide⟩ (listedAt ⟨138, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 10 (transLenTr ⟨53, by decide⟩ 10 hp)) T138_53
      hfix138_53 hinj138_53 hcardT138_53
      (fun i => conj_mem_of_fixedPoints _ _ (T138_53 i) (hfix138_53 i) _)
      ⟨138, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨138, by decide⟩ (Q2.listedAt ⟨138, by decide⟩
        (alnCheck_rep ⟨138, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 10 hp) Q2.T138_53_2 Q2.hfix138_53_2 Q2.hinj138_53_2
      Q2.hcardT138_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T138_53_2 i) (Q2.hfix138_53_2 i) _)
      colCert_138_53_10.hD ?_).symm
  rw [alnId_138 j hj]


theorem leaf_138_53_15 (hp : 15 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 138 []).length)
    (hq : (normIsRep.getD 138 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 15 hp)
        (rowE2 (⟨138, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 15 (transLenTr ⟨53, by decide⟩ 15 hp))
        (rowE1 (⟨138, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨138, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨138, by decide⟩ (listedAt ⟨138, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 15 (transLenTr ⟨53, by decide⟩ 15 hp)) T138_53
      hfix138_53 hinj138_53 hcardT138_53
      (fun i => conj_mem_of_fixedPoints _ _ (T138_53 i) (hfix138_53 i) _)
      ⟨138, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨138, by decide⟩ (Q2.listedAt ⟨138, by decide⟩
        (alnCheck_rep ⟨138, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 15 hp) Q2.T138_53_2 Q2.hfix138_53_2 Q2.hinj138_53_2
      Q2.hcardT138_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T138_53_2 i) (Q2.hfix138_53_2 i) _)
      colCert_138_53_15.hD ?_).symm
  rw [alnId_138 j hj]


theorem leaf_138_53_20 (hp : 20 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 138 []).length)
    (hq : (normIsRep.getD 138 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 20 hp)
        (rowE2 (⟨138, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 20 (transLenTr ⟨53, by decide⟩ 20 hp))
        (rowE1 (⟨138, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨138, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨138, by decide⟩ (listedAt ⟨138, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 20 (transLenTr ⟨53, by decide⟩ 20 hp)) T138_53
      hfix138_53 hinj138_53 hcardT138_53
      (fun i => conj_mem_of_fixedPoints _ _ (T138_53 i) (hfix138_53 i) _)
      ⟨138, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨138, by decide⟩ (Q2.listedAt ⟨138, by decide⟩
        (alnCheck_rep ⟨138, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 20 hp) Q2.T138_53_2 Q2.hfix138_53_2 Q2.hinj138_53_2
      Q2.hcardT138_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T138_53_2 i) (Q2.hfix138_53_2 i) _)
      colCert_138_53_20.hD ?_).symm
  rw [alnId_138 j hj]


theorem leaf_138_84_0 (hp : 0 < (Q2.transData.getD 84 []).length)
    (j : Nat) (hj : j < (repChars.getD 138 []).length)
    (hq : (normIsRep.getD 138 []).getD j false = true) :
    species (Q2.reps (⟨84, by decide⟩ : Fin 148)) (colE2 ⟨84, by decide⟩ 0 hp)
        (rowE2 (⟨138, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨84, by decide⟩ : Fin 148))
        (colE1 ⟨84, by decide⟩ 0 (transLenTr ⟨84, by decide⟩ 0 hp))
        (rowE1 (⟨138, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨138, by decide⟩ : Fin 148) ⟨84, by decide⟩ _
      (validAt ⟨138, by decide⟩ (listedAt ⟨138, by decide⟩ hj))
      (colE1 ⟨84, by decide⟩ 0 (transLenTr ⟨84, by decide⟩ 0 hp)) T138_84
      hfix138_84 hinj138_84 hcardT138_84
      (fun i => conj_mem_of_fixedPoints _ _ (T138_84 i) (hfix138_84 i) _)
      ⟨138, by decide⟩ ⟨84, by decide⟩ _
      (Q2.validAt ⟨138, by decide⟩ (Q2.listedAt ⟨138, by decide⟩
        (alnCheck_rep ⟨138, by decide⟩ hj hq).1))
      (colE2 ⟨84, by decide⟩ 0 hp) Q2.T138_84_2 Q2.hfix138_84_2 Q2.hinj138_84_2
      Q2.hcardT138_84_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T138_84_2 i) (Q2.hfix138_84_2 i) _)
      colCert_138_84_0.hD ?_).symm
  rw [alnId_138 j hj]


theorem leaf_138_84_1 (hp : 1 < (Q2.transData.getD 84 []).length)
    (j : Nat) (hj : j < (repChars.getD 138 []).length)
    (hq : (normIsRep.getD 138 []).getD j false = true) :
    species (Q2.reps (⟨84, by decide⟩ : Fin 148)) (colE2 ⟨84, by decide⟩ 1 hp)
        (rowE2 (⟨138, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨84, by decide⟩ : Fin 148))
        (colE1 ⟨84, by decide⟩ 1 (transLenTr ⟨84, by decide⟩ 1 hp))
        (rowE1 (⟨138, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨138, by decide⟩ : Fin 148) ⟨84, by decide⟩ _
      (validAt ⟨138, by decide⟩ (listedAt ⟨138, by decide⟩ hj))
      (colE1 ⟨84, by decide⟩ 1 (transLenTr ⟨84, by decide⟩ 1 hp)) T138_84
      hfix138_84 hinj138_84 hcardT138_84
      (fun i => conj_mem_of_fixedPoints _ _ (T138_84 i) (hfix138_84 i) _)
      ⟨138, by decide⟩ ⟨84, by decide⟩ _
      (Q2.validAt ⟨138, by decide⟩ (Q2.listedAt ⟨138, by decide⟩
        (alnCheck_rep ⟨138, by decide⟩ hj hq).1))
      (colE2 ⟨84, by decide⟩ 1 hp) Q2.T138_84_2 Q2.hfix138_84_2 Q2.hinj138_84_2
      Q2.hcardT138_84_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T138_84_2 i) (Q2.hfix138_84_2 i) _)
      colCert_138_84_1.hD ?_).symm
  rw [alnId_138 j hj]


theorem leaf_138_84_2 (hp : 2 < (Q2.transData.getD 84 []).length)
    (j : Nat) (hj : j < (repChars.getD 138 []).length)
    (hq : (normIsRep.getD 138 []).getD j false = true) :
    species (Q2.reps (⟨84, by decide⟩ : Fin 148)) (colE2 ⟨84, by decide⟩ 2 hp)
        (rowE2 (⟨138, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨84, by decide⟩ : Fin 148))
        (colE1 ⟨84, by decide⟩ 2 (transLenTr ⟨84, by decide⟩ 2 hp))
        (rowE1 (⟨138, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨138, by decide⟩ : Fin 148) ⟨84, by decide⟩ _
      (validAt ⟨138, by decide⟩ (listedAt ⟨138, by decide⟩ hj))
      (colE1 ⟨84, by decide⟩ 2 (transLenTr ⟨84, by decide⟩ 2 hp)) T138_84
      hfix138_84 hinj138_84 hcardT138_84
      (fun i => conj_mem_of_fixedPoints _ _ (T138_84 i) (hfix138_84 i) _)
      ⟨138, by decide⟩ ⟨84, by decide⟩ _
      (Q2.validAt ⟨138, by decide⟩ (Q2.listedAt ⟨138, by decide⟩
        (alnCheck_rep ⟨138, by decide⟩ hj hq).1))
      (colE2 ⟨84, by decide⟩ 2 hp) Q2.T138_84_2 Q2.hfix138_84_2 Q2.hinj138_84_2
      Q2.hcardT138_84_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T138_84_2 i) (Q2.hfix138_84_2 i) _)
      colCert_138_84_2.hD ?_).symm
  rw [alnId_138 j hj]


theorem leaf_138_84_3 (hp : 3 < (Q2.transData.getD 84 []).length)
    (j : Nat) (hj : j < (repChars.getD 138 []).length)
    (hq : (normIsRep.getD 138 []).getD j false = true) :
    species (Q2.reps (⟨84, by decide⟩ : Fin 148)) (colE2 ⟨84, by decide⟩ 3 hp)
        (rowE2 (⟨138, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨84, by decide⟩ : Fin 148))
        (colE1 ⟨84, by decide⟩ 3 (transLenTr ⟨84, by decide⟩ 3 hp))
        (rowE1 (⟨138, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨138, by decide⟩ : Fin 148) ⟨84, by decide⟩ _
      (validAt ⟨138, by decide⟩ (listedAt ⟨138, by decide⟩ hj))
      (colE1 ⟨84, by decide⟩ 3 (transLenTr ⟨84, by decide⟩ 3 hp)) T138_84
      hfix138_84 hinj138_84 hcardT138_84
      (fun i => conj_mem_of_fixedPoints _ _ (T138_84 i) (hfix138_84 i) _)
      ⟨138, by decide⟩ ⟨84, by decide⟩ _
      (Q2.validAt ⟨138, by decide⟩ (Q2.listedAt ⟨138, by decide⟩
        (alnCheck_rep ⟨138, by decide⟩ hj hq).1))
      (colE2 ⟨84, by decide⟩ 3 hp) Q2.T138_84_2 Q2.hfix138_84_2 Q2.hinj138_84_2
      Q2.hcardT138_84_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T138_84_2 i) (Q2.hfix138_84_2 i) _)
      colCert_138_84_3.hD ?_).symm
  rw [alnId_138 j hj]


theorem leaf_138_84_4 (hp : 4 < (Q2.transData.getD 84 []).length)
    (j : Nat) (hj : j < (repChars.getD 138 []).length)
    (hq : (normIsRep.getD 138 []).getD j false = true) :
    species (Q2.reps (⟨84, by decide⟩ : Fin 148)) (colE2 ⟨84, by decide⟩ 4 hp)
        (rowE2 (⟨138, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨84, by decide⟩ : Fin 148))
        (colE1 ⟨84, by decide⟩ 4 (transLenTr ⟨84, by decide⟩ 4 hp))
        (rowE1 (⟨138, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨138, by decide⟩ : Fin 148) ⟨84, by decide⟩ _
      (validAt ⟨138, by decide⟩ (listedAt ⟨138, by decide⟩ hj))
      (colE1 ⟨84, by decide⟩ 4 (transLenTr ⟨84, by decide⟩ 4 hp)) T138_84
      hfix138_84 hinj138_84 hcardT138_84
      (fun i => conj_mem_of_fixedPoints _ _ (T138_84 i) (hfix138_84 i) _)
      ⟨138, by decide⟩ ⟨84, by decide⟩ _
      (Q2.validAt ⟨138, by decide⟩ (Q2.listedAt ⟨138, by decide⟩
        (alnCheck_rep ⟨138, by decide⟩ hj hq).1))
      (colE2 ⟨84, by decide⟩ 4 hp) Q2.T138_84_2 Q2.hfix138_84_2 Q2.hinj138_84_2
      Q2.hcardT138_84_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T138_84_2 i) (Q2.hfix138_84_2 i) _)
      colCert_138_84_4.hD ?_).symm
  rw [alnId_138 j hj]


theorem leaf_138_84_5 (hp : 5 < (Q2.transData.getD 84 []).length)
    (j : Nat) (hj : j < (repChars.getD 138 []).length)
    (hq : (normIsRep.getD 138 []).getD j false = true) :
    species (Q2.reps (⟨84, by decide⟩ : Fin 148)) (colE2 ⟨84, by decide⟩ 5 hp)
        (rowE2 (⟨138, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨84, by decide⟩ : Fin 148))
        (colE1 ⟨84, by decide⟩ 5 (transLenTr ⟨84, by decide⟩ 5 hp))
        (rowE1 (⟨138, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨138, by decide⟩ : Fin 148) ⟨84, by decide⟩ _
      (validAt ⟨138, by decide⟩ (listedAt ⟨138, by decide⟩ hj))
      (colE1 ⟨84, by decide⟩ 5 (transLenTr ⟨84, by decide⟩ 5 hp)) T138_84
      hfix138_84 hinj138_84 hcardT138_84
      (fun i => conj_mem_of_fixedPoints _ _ (T138_84 i) (hfix138_84 i) _)
      ⟨138, by decide⟩ ⟨84, by decide⟩ _
      (Q2.validAt ⟨138, by decide⟩ (Q2.listedAt ⟨138, by decide⟩
        (alnCheck_rep ⟨138, by decide⟩ hj hq).1))
      (colE2 ⟨84, by decide⟩ 5 hp) Q2.T138_84_2 Q2.hfix138_84_2 Q2.hinj138_84_2
      Q2.hcardT138_84_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T138_84_2 i) (Q2.hfix138_84_2 i) _)
      ?_).symm
  rw [show colData1 (⟨138, by decide⟩ : Fin 148)
        ((colE1 ⟨84, by decide⟩ 5 (transLenTr ⟨84, by decide⟩ 5 hp) : ↥(reps ⟨84, by decide⟩)) : Coordinate 1)
        T138_84 = colFn colCertDiv_138_84_5.D1 (m := 5) from colCertDiv_138_84_5.bind1,
    show colData2 (⟨138, by decide⟩ : Fin 148)
        ((colE2 ⟨84, by decide⟩ 5 hp : ↥(Q2.reps ⟨84, by decide⟩)) : Coordinate 2)
        Q2.T138_84_2 = colFn colCertDiv_138_84_5.D2 (m := 5) from colCertDiv_138_84_5.bind2]
  rw [alnId_138 j hj]
  exact fastcode_of_div ⟨138, by decide⟩ _ _ _
    ((alnId_138 j hj) ▸ Q2.listedAt (⟨138, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨138, by decide⟩ : Fin 148) hj hq).1) colCertDiv_138_84_5_match


theorem leaf_138_84_10 (hp : 10 < (Q2.transData.getD 84 []).length)
    (j : Nat) (hj : j < (repChars.getD 138 []).length)
    (hq : (normIsRep.getD 138 []).getD j false = true) :
    species (Q2.reps (⟨84, by decide⟩ : Fin 148)) (colE2 ⟨84, by decide⟩ 10 hp)
        (rowE2 (⟨138, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨84, by decide⟩ : Fin 148))
        (colE1 ⟨84, by decide⟩ 10 (transLenTr ⟨84, by decide⟩ 10 hp))
        (rowE1 (⟨138, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨138, by decide⟩ : Fin 148) ⟨84, by decide⟩ _
      (validAt ⟨138, by decide⟩ (listedAt ⟨138, by decide⟩ hj))
      (colE1 ⟨84, by decide⟩ 10 (transLenTr ⟨84, by decide⟩ 10 hp)) T138_84
      hfix138_84 hinj138_84 hcardT138_84
      (fun i => conj_mem_of_fixedPoints _ _ (T138_84 i) (hfix138_84 i) _)
      ⟨138, by decide⟩ ⟨84, by decide⟩ _
      (Q2.validAt ⟨138, by decide⟩ (Q2.listedAt ⟨138, by decide⟩
        (alnCheck_rep ⟨138, by decide⟩ hj hq).1))
      (colE2 ⟨84, by decide⟩ 10 hp) Q2.T138_84_2 Q2.hfix138_84_2 Q2.hinj138_84_2
      Q2.hcardT138_84_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T138_84_2 i) (Q2.hfix138_84_2 i) _)
      ?_).symm
  rw [show colData1 (⟨138, by decide⟩ : Fin 148)
        ((colE1 ⟨84, by decide⟩ 10 (transLenTr ⟨84, by decide⟩ 10 hp) : ↥(reps ⟨84, by decide⟩)) : Coordinate 1)
        T138_84 = colFn colCertDiv_138_84_10.D1 (m := 5) from colCertDiv_138_84_10.bind1,
    show colData2 (⟨138, by decide⟩ : Fin 148)
        ((colE2 ⟨84, by decide⟩ 10 hp : ↥(Q2.reps ⟨84, by decide⟩)) : Coordinate 2)
        Q2.T138_84_2 = colFn colCertDiv_138_84_10.D2 (m := 5) from colCertDiv_138_84_10.bind2]
  rw [alnId_138 j hj]
  exact fastcode_of_div ⟨138, by decide⟩ _ _ _
    ((alnId_138 j hj) ▸ Q2.listedAt (⟨138, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨138, by decide⟩ : Fin 148) hj hq).1) colCertDiv_138_84_10_match


theorem leaf_138_84_15 (hp : 15 < (Q2.transData.getD 84 []).length)
    (j : Nat) (hj : j < (repChars.getD 138 []).length)
    (hq : (normIsRep.getD 138 []).getD j false = true) :
    species (Q2.reps (⟨84, by decide⟩ : Fin 148)) (colE2 ⟨84, by decide⟩ 15 hp)
        (rowE2 (⟨138, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨84, by decide⟩ : Fin 148))
        (colE1 ⟨84, by decide⟩ 15 (transLenTr ⟨84, by decide⟩ 15 hp))
        (rowE1 (⟨138, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨138, by decide⟩ : Fin 148) ⟨84, by decide⟩ _
      (validAt ⟨138, by decide⟩ (listedAt ⟨138, by decide⟩ hj))
      (colE1 ⟨84, by decide⟩ 15 (transLenTr ⟨84, by decide⟩ 15 hp)) T138_84
      hfix138_84 hinj138_84 hcardT138_84
      (fun i => conj_mem_of_fixedPoints _ _ (T138_84 i) (hfix138_84 i) _)
      ⟨138, by decide⟩ ⟨84, by decide⟩ _
      (Q2.validAt ⟨138, by decide⟩ (Q2.listedAt ⟨138, by decide⟩
        (alnCheck_rep ⟨138, by decide⟩ hj hq).1))
      (colE2 ⟨84, by decide⟩ 15 hp) Q2.T138_84_2 Q2.hfix138_84_2 Q2.hinj138_84_2
      Q2.hcardT138_84_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T138_84_2 i) (Q2.hfix138_84_2 i) _)
      ?_).symm
  rw [show colData1 (⟨138, by decide⟩ : Fin 148)
        ((colE1 ⟨84, by decide⟩ 15 (transLenTr ⟨84, by decide⟩ 15 hp) : ↥(reps ⟨84, by decide⟩)) : Coordinate 1)
        T138_84 = colFn colCertDiv_138_84_15.D1 (m := 5) from colCertDiv_138_84_15.bind1,
    show colData2 (⟨138, by decide⟩ : Fin 148)
        ((colE2 ⟨84, by decide⟩ 15 hp : ↥(Q2.reps ⟨84, by decide⟩)) : Coordinate 2)
        Q2.T138_84_2 = colFn colCertDiv_138_84_15.D2 (m := 5) from colCertDiv_138_84_15.bind2]
  rw [alnId_138 j hj]
  exact fastcode_of_div ⟨138, by decide⟩ _ _ _
    ((alnId_138 j hj) ▸ Q2.listedAt (⟨138, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨138, by decide⟩ : Fin 148) hj hq).1) colCertDiv_138_84_15_match


theorem leaf_138_84_20 (hp : 20 < (Q2.transData.getD 84 []).length)
    (j : Nat) (hj : j < (repChars.getD 138 []).length)
    (hq : (normIsRep.getD 138 []).getD j false = true) :
    species (Q2.reps (⟨84, by decide⟩ : Fin 148)) (colE2 ⟨84, by decide⟩ 20 hp)
        (rowE2 (⟨138, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨84, by decide⟩ : Fin 148))
        (colE1 ⟨84, by decide⟩ 20 (transLenTr ⟨84, by decide⟩ 20 hp))
        (rowE1 (⟨138, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨138, by decide⟩ : Fin 148) ⟨84, by decide⟩ _
      (validAt ⟨138, by decide⟩ (listedAt ⟨138, by decide⟩ hj))
      (colE1 ⟨84, by decide⟩ 20 (transLenTr ⟨84, by decide⟩ 20 hp)) T138_84
      hfix138_84 hinj138_84 hcardT138_84
      (fun i => conj_mem_of_fixedPoints _ _ (T138_84 i) (hfix138_84 i) _)
      ⟨138, by decide⟩ ⟨84, by decide⟩ _
      (Q2.validAt ⟨138, by decide⟩ (Q2.listedAt ⟨138, by decide⟩
        (alnCheck_rep ⟨138, by decide⟩ hj hq).1))
      (colE2 ⟨84, by decide⟩ 20 hp) Q2.T138_84_2 Q2.hfix138_84_2 Q2.hinj138_84_2
      Q2.hcardT138_84_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T138_84_2 i) (Q2.hfix138_84_2 i) _)
      ?_).symm
  rw [show colData1 (⟨138, by decide⟩ : Fin 148)
        ((colE1 ⟨84, by decide⟩ 20 (transLenTr ⟨84, by decide⟩ 20 hp) : ↥(reps ⟨84, by decide⟩)) : Coordinate 1)
        T138_84 = colFn colCertDiv_138_84_20.D1 (m := 5) from colCertDiv_138_84_20.bind1,
    show colData2 (⟨138, by decide⟩ : Fin 148)
        ((colE2 ⟨84, by decide⟩ 20 hp : ↥(Q2.reps ⟨84, by decide⟩)) : Coordinate 2)
        Q2.T138_84_2 = colFn colCertDiv_138_84_20.D2 (m := 5) from colCertDiv_138_84_20.bind2]
  rw [alnId_138 j hj]
  exact fastcode_of_div ⟨138, by decide⟩ _ _ _
    ((alnId_138 j hj) ▸ Q2.listedAt (⟨138, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨138, by decide⟩ : Fin 148) hj hq).1) colCertDiv_138_84_20_match


theorem leaf_138_93_0 (hp : 0 < (Q2.transData.getD 93 []).length)
    (j : Nat) (hj : j < (repChars.getD 138 []).length)
    (hq : (normIsRep.getD 138 []).getD j false = true) :
    species (Q2.reps (⟨93, by decide⟩ : Fin 148)) (colE2 ⟨93, by decide⟩ 0 hp)
        (rowE2 (⟨138, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨93, by decide⟩ : Fin 148))
        (colE1 ⟨93, by decide⟩ 0 (transLenTr ⟨93, by decide⟩ 0 hp))
        (rowE1 (⟨138, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨138, by decide⟩ : Fin 148) ⟨93, by decide⟩ _
      (validAt ⟨138, by decide⟩ (listedAt ⟨138, by decide⟩ hj))
      (colE1 ⟨93, by decide⟩ 0 (transLenTr ⟨93, by decide⟩ 0 hp)) T138_93
      hfix138_93 hinj138_93 hcardT138_93
      (fun i => conj_mem_of_fixedPoints _ _ (T138_93 i) (hfix138_93 i) _)
      ⟨138, by decide⟩ ⟨93, by decide⟩ _
      (Q2.validAt ⟨138, by decide⟩ (Q2.listedAt ⟨138, by decide⟩
        (alnCheck_rep ⟨138, by decide⟩ hj hq).1))
      (colE2 ⟨93, by decide⟩ 0 hp) Q2.T138_93_2 Q2.hfix138_93_2 Q2.hinj138_93_2
      Q2.hcardT138_93_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T138_93_2 i) (Q2.hfix138_93_2 i) _)
      colCert_138_93_0.hD ?_).symm
  rw [alnId_138 j hj]


theorem leaf_138_93_1 (hp : 1 < (Q2.transData.getD 93 []).length)
    (j : Nat) (hj : j < (repChars.getD 138 []).length)
    (hq : (normIsRep.getD 138 []).getD j false = true) :
    species (Q2.reps (⟨93, by decide⟩ : Fin 148)) (colE2 ⟨93, by decide⟩ 1 hp)
        (rowE2 (⟨138, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨93, by decide⟩ : Fin 148))
        (colE1 ⟨93, by decide⟩ 1 (transLenTr ⟨93, by decide⟩ 1 hp))
        (rowE1 (⟨138, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨138, by decide⟩ : Fin 148) ⟨93, by decide⟩ _
      (validAt ⟨138, by decide⟩ (listedAt ⟨138, by decide⟩ hj))
      (colE1 ⟨93, by decide⟩ 1 (transLenTr ⟨93, by decide⟩ 1 hp)) T138_93
      hfix138_93 hinj138_93 hcardT138_93
      (fun i => conj_mem_of_fixedPoints _ _ (T138_93 i) (hfix138_93 i) _)
      ⟨138, by decide⟩ ⟨93, by decide⟩ _
      (Q2.validAt ⟨138, by decide⟩ (Q2.listedAt ⟨138, by decide⟩
        (alnCheck_rep ⟨138, by decide⟩ hj hq).1))
      (colE2 ⟨93, by decide⟩ 1 hp) Q2.T138_93_2 Q2.hfix138_93_2 Q2.hinj138_93_2
      Q2.hcardT138_93_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T138_93_2 i) (Q2.hfix138_93_2 i) _)
      colCert_138_93_1.hD ?_).symm
  rw [alnId_138 j hj]


theorem leaf_138_93_2 (hp : 2 < (Q2.transData.getD 93 []).length)
    (j : Nat) (hj : j < (repChars.getD 138 []).length)
    (hq : (normIsRep.getD 138 []).getD j false = true) :
    species (Q2.reps (⟨93, by decide⟩ : Fin 148)) (colE2 ⟨93, by decide⟩ 2 hp)
        (rowE2 (⟨138, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨93, by decide⟩ : Fin 148))
        (colE1 ⟨93, by decide⟩ 2 (transLenTr ⟨93, by decide⟩ 2 hp))
        (rowE1 (⟨138, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨138, by decide⟩ : Fin 148) ⟨93, by decide⟩ _
      (validAt ⟨138, by decide⟩ (listedAt ⟨138, by decide⟩ hj))
      (colE1 ⟨93, by decide⟩ 2 (transLenTr ⟨93, by decide⟩ 2 hp)) T138_93
      hfix138_93 hinj138_93 hcardT138_93
      (fun i => conj_mem_of_fixedPoints _ _ (T138_93 i) (hfix138_93 i) _)
      ⟨138, by decide⟩ ⟨93, by decide⟩ _
      (Q2.validAt ⟨138, by decide⟩ (Q2.listedAt ⟨138, by decide⟩
        (alnCheck_rep ⟨138, by decide⟩ hj hq).1))
      (colE2 ⟨93, by decide⟩ 2 hp) Q2.T138_93_2 Q2.hfix138_93_2 Q2.hinj138_93_2
      Q2.hcardT138_93_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T138_93_2 i) (Q2.hfix138_93_2 i) _)
      colCert_138_93_2.hD ?_).symm
  rw [alnId_138 j hj]


theorem leaf_138_93_3 (hp : 3 < (Q2.transData.getD 93 []).length)
    (j : Nat) (hj : j < (repChars.getD 138 []).length)
    (hq : (normIsRep.getD 138 []).getD j false = true) :
    species (Q2.reps (⟨93, by decide⟩ : Fin 148)) (colE2 ⟨93, by decide⟩ 3 hp)
        (rowE2 (⟨138, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨93, by decide⟩ : Fin 148))
        (colE1 ⟨93, by decide⟩ 3 (transLenTr ⟨93, by decide⟩ 3 hp))
        (rowE1 (⟨138, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨138, by decide⟩ : Fin 148) ⟨93, by decide⟩ _
      (validAt ⟨138, by decide⟩ (listedAt ⟨138, by decide⟩ hj))
      (colE1 ⟨93, by decide⟩ 3 (transLenTr ⟨93, by decide⟩ 3 hp)) T138_93
      hfix138_93 hinj138_93 hcardT138_93
      (fun i => conj_mem_of_fixedPoints _ _ (T138_93 i) (hfix138_93 i) _)
      ⟨138, by decide⟩ ⟨93, by decide⟩ _
      (Q2.validAt ⟨138, by decide⟩ (Q2.listedAt ⟨138, by decide⟩
        (alnCheck_rep ⟨138, by decide⟩ hj hq).1))
      (colE2 ⟨93, by decide⟩ 3 hp) Q2.T138_93_2 Q2.hfix138_93_2 Q2.hinj138_93_2
      Q2.hcardT138_93_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T138_93_2 i) (Q2.hfix138_93_2 i) _)
      colCert_138_93_3.hD ?_).symm
  rw [alnId_138 j hj]


theorem leaf_138_93_4 (hp : 4 < (Q2.transData.getD 93 []).length)
    (j : Nat) (hj : j < (repChars.getD 138 []).length)
    (hq : (normIsRep.getD 138 []).getD j false = true) :
    species (Q2.reps (⟨93, by decide⟩ : Fin 148)) (colE2 ⟨93, by decide⟩ 4 hp)
        (rowE2 (⟨138, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨93, by decide⟩ : Fin 148))
        (colE1 ⟨93, by decide⟩ 4 (transLenTr ⟨93, by decide⟩ 4 hp))
        (rowE1 (⟨138, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨138, by decide⟩ : Fin 148) ⟨93, by decide⟩ _
      (validAt ⟨138, by decide⟩ (listedAt ⟨138, by decide⟩ hj))
      (colE1 ⟨93, by decide⟩ 4 (transLenTr ⟨93, by decide⟩ 4 hp)) T138_93
      hfix138_93 hinj138_93 hcardT138_93
      (fun i => conj_mem_of_fixedPoints _ _ (T138_93 i) (hfix138_93 i) _)
      ⟨138, by decide⟩ ⟨93, by decide⟩ _
      (Q2.validAt ⟨138, by decide⟩ (Q2.listedAt ⟨138, by decide⟩
        (alnCheck_rep ⟨138, by decide⟩ hj hq).1))
      (colE2 ⟨93, by decide⟩ 4 hp) Q2.T138_93_2 Q2.hfix138_93_2 Q2.hinj138_93_2
      Q2.hcardT138_93_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T138_93_2 i) (Q2.hfix138_93_2 i) _)
      colCert_138_93_4.hD ?_).symm
  rw [alnId_138 j hj]


theorem leaf_138_93_5 (hp : 5 < (Q2.transData.getD 93 []).length)
    (j : Nat) (hj : j < (repChars.getD 138 []).length)
    (hq : (normIsRep.getD 138 []).getD j false = true) :
    species (Q2.reps (⟨93, by decide⟩ : Fin 148)) (colE2 ⟨93, by decide⟩ 5 hp)
        (rowE2 (⟨138, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨93, by decide⟩ : Fin 148))
        (colE1 ⟨93, by decide⟩ 5 (transLenTr ⟨93, by decide⟩ 5 hp))
        (rowE1 (⟨138, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨138, by decide⟩ : Fin 148) ⟨93, by decide⟩ _
      (validAt ⟨138, by decide⟩ (listedAt ⟨138, by decide⟩ hj))
      (colE1 ⟨93, by decide⟩ 5 (transLenTr ⟨93, by decide⟩ 5 hp)) T138_93
      hfix138_93 hinj138_93 hcardT138_93
      (fun i => conj_mem_of_fixedPoints _ _ (T138_93 i) (hfix138_93 i) _)
      ⟨138, by decide⟩ ⟨93, by decide⟩ _
      (Q2.validAt ⟨138, by decide⟩ (Q2.listedAt ⟨138, by decide⟩
        (alnCheck_rep ⟨138, by decide⟩ hj hq).1))
      (colE2 ⟨93, by decide⟩ 5 hp) Q2.T138_93_2 Q2.hfix138_93_2 Q2.hinj138_93_2
      Q2.hcardT138_93_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T138_93_2 i) (Q2.hfix138_93_2 i) _)
      ?_).symm
  rw [show colData1 (⟨138, by decide⟩ : Fin 148)
        ((colE1 ⟨93, by decide⟩ 5 (transLenTr ⟨93, by decide⟩ 5 hp) : ↥(reps ⟨93, by decide⟩)) : Coordinate 1)
        T138_93 = colFn colCertDiv_138_93_5.D1 (m := 5) from colCertDiv_138_93_5.bind1,
    show colData2 (⟨138, by decide⟩ : Fin 148)
        ((colE2 ⟨93, by decide⟩ 5 hp : ↥(Q2.reps ⟨93, by decide⟩)) : Coordinate 2)
        Q2.T138_93_2 = colFn colCertDiv_138_93_5.D2 (m := 5) from colCertDiv_138_93_5.bind2]
  rw [alnId_138 j hj]
  exact fastcode_of_div ⟨138, by decide⟩ _ _ _
    ((alnId_138 j hj) ▸ Q2.listedAt (⟨138, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨138, by decide⟩ : Fin 148) hj hq).1) colCertDiv_138_93_5_match


theorem leaf_138_93_10 (hp : 10 < (Q2.transData.getD 93 []).length)
    (j : Nat) (hj : j < (repChars.getD 138 []).length)
    (hq : (normIsRep.getD 138 []).getD j false = true) :
    species (Q2.reps (⟨93, by decide⟩ : Fin 148)) (colE2 ⟨93, by decide⟩ 10 hp)
        (rowE2 (⟨138, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨93, by decide⟩ : Fin 148))
        (colE1 ⟨93, by decide⟩ 10 (transLenTr ⟨93, by decide⟩ 10 hp))
        (rowE1 (⟨138, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨138, by decide⟩ : Fin 148) ⟨93, by decide⟩ _
      (validAt ⟨138, by decide⟩ (listedAt ⟨138, by decide⟩ hj))
      (colE1 ⟨93, by decide⟩ 10 (transLenTr ⟨93, by decide⟩ 10 hp)) T138_93
      hfix138_93 hinj138_93 hcardT138_93
      (fun i => conj_mem_of_fixedPoints _ _ (T138_93 i) (hfix138_93 i) _)
      ⟨138, by decide⟩ ⟨93, by decide⟩ _
      (Q2.validAt ⟨138, by decide⟩ (Q2.listedAt ⟨138, by decide⟩
        (alnCheck_rep ⟨138, by decide⟩ hj hq).1))
      (colE2 ⟨93, by decide⟩ 10 hp) Q2.T138_93_2 Q2.hfix138_93_2 Q2.hinj138_93_2
      Q2.hcardT138_93_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T138_93_2 i) (Q2.hfix138_93_2 i) _)
      ?_).symm
  rw [show colData1 (⟨138, by decide⟩ : Fin 148)
        ((colE1 ⟨93, by decide⟩ 10 (transLenTr ⟨93, by decide⟩ 10 hp) : ↥(reps ⟨93, by decide⟩)) : Coordinate 1)
        T138_93 = colFn colCertDiv_138_93_10.D1 (m := 5) from colCertDiv_138_93_10.bind1,
    show colData2 (⟨138, by decide⟩ : Fin 148)
        ((colE2 ⟨93, by decide⟩ 10 hp : ↥(Q2.reps ⟨93, by decide⟩)) : Coordinate 2)
        Q2.T138_93_2 = colFn colCertDiv_138_93_10.D2 (m := 5) from colCertDiv_138_93_10.bind2]
  rw [alnId_138 j hj]
  exact fastcode_of_div ⟨138, by decide⟩ _ _ _
    ((alnId_138 j hj) ▸ Q2.listedAt (⟨138, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨138, by decide⟩ : Fin 148) hj hq).1) colCertDiv_138_93_10_match


theorem leaf_138_93_15 (hp : 15 < (Q2.transData.getD 93 []).length)
    (j : Nat) (hj : j < (repChars.getD 138 []).length)
    (hq : (normIsRep.getD 138 []).getD j false = true) :
    species (Q2.reps (⟨93, by decide⟩ : Fin 148)) (colE2 ⟨93, by decide⟩ 15 hp)
        (rowE2 (⟨138, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨93, by decide⟩ : Fin 148))
        (colE1 ⟨93, by decide⟩ 15 (transLenTr ⟨93, by decide⟩ 15 hp))
        (rowE1 (⟨138, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨138, by decide⟩ : Fin 148) ⟨93, by decide⟩ _
      (validAt ⟨138, by decide⟩ (listedAt ⟨138, by decide⟩ hj))
      (colE1 ⟨93, by decide⟩ 15 (transLenTr ⟨93, by decide⟩ 15 hp)) T138_93
      hfix138_93 hinj138_93 hcardT138_93
      (fun i => conj_mem_of_fixedPoints _ _ (T138_93 i) (hfix138_93 i) _)
      ⟨138, by decide⟩ ⟨93, by decide⟩ _
      (Q2.validAt ⟨138, by decide⟩ (Q2.listedAt ⟨138, by decide⟩
        (alnCheck_rep ⟨138, by decide⟩ hj hq).1))
      (colE2 ⟨93, by decide⟩ 15 hp) Q2.T138_93_2 Q2.hfix138_93_2 Q2.hinj138_93_2
      Q2.hcardT138_93_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T138_93_2 i) (Q2.hfix138_93_2 i) _)
      ?_).symm
  rw [show colData1 (⟨138, by decide⟩ : Fin 148)
        ((colE1 ⟨93, by decide⟩ 15 (transLenTr ⟨93, by decide⟩ 15 hp) : ↥(reps ⟨93, by decide⟩)) : Coordinate 1)
        T138_93 = colFn colCertDiv_138_93_15.D1 (m := 5) from colCertDiv_138_93_15.bind1,
    show colData2 (⟨138, by decide⟩ : Fin 148)
        ((colE2 ⟨93, by decide⟩ 15 hp : ↥(Q2.reps ⟨93, by decide⟩)) : Coordinate 2)
        Q2.T138_93_2 = colFn colCertDiv_138_93_15.D2 (m := 5) from colCertDiv_138_93_15.bind2]
  rw [alnId_138 j hj]
  exact fastcode_of_div ⟨138, by decide⟩ _ _ _
    ((alnId_138 j hj) ▸ Q2.listedAt (⟨138, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨138, by decide⟩ : Fin 148) hj hq).1) colCertDiv_138_93_15_match


theorem leaf_138_93_20 (hp : 20 < (Q2.transData.getD 93 []).length)
    (j : Nat) (hj : j < (repChars.getD 138 []).length)
    (hq : (normIsRep.getD 138 []).getD j false = true) :
    species (Q2.reps (⟨93, by decide⟩ : Fin 148)) (colE2 ⟨93, by decide⟩ 20 hp)
        (rowE2 (⟨138, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨93, by decide⟩ : Fin 148))
        (colE1 ⟨93, by decide⟩ 20 (transLenTr ⟨93, by decide⟩ 20 hp))
        (rowE1 (⟨138, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨138, by decide⟩ : Fin 148) ⟨93, by decide⟩ _
      (validAt ⟨138, by decide⟩ (listedAt ⟨138, by decide⟩ hj))
      (colE1 ⟨93, by decide⟩ 20 (transLenTr ⟨93, by decide⟩ 20 hp)) T138_93
      hfix138_93 hinj138_93 hcardT138_93
      (fun i => conj_mem_of_fixedPoints _ _ (T138_93 i) (hfix138_93 i) _)
      ⟨138, by decide⟩ ⟨93, by decide⟩ _
      (Q2.validAt ⟨138, by decide⟩ (Q2.listedAt ⟨138, by decide⟩
        (alnCheck_rep ⟨138, by decide⟩ hj hq).1))
      (colE2 ⟨93, by decide⟩ 20 hp) Q2.T138_93_2 Q2.hfix138_93_2 Q2.hinj138_93_2
      Q2.hcardT138_93_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T138_93_2 i) (Q2.hfix138_93_2 i) _)
      ?_).symm
  rw [show colData1 (⟨138, by decide⟩ : Fin 148)
        ((colE1 ⟨93, by decide⟩ 20 (transLenTr ⟨93, by decide⟩ 20 hp) : ↥(reps ⟨93, by decide⟩)) : Coordinate 1)
        T138_93 = colFn colCertDiv_138_93_20.D1 (m := 5) from colCertDiv_138_93_20.bind1,
    show colData2 (⟨138, by decide⟩ : Fin 148)
        ((colE2 ⟨93, by decide⟩ 20 hp : ↥(Q2.reps ⟨93, by decide⟩)) : Coordinate 2)
        Q2.T138_93_2 = colFn colCertDiv_138_93_20.D2 (m := 5) from colCertDiv_138_93_20.bind2]
  rw [alnId_138 j hj]
  exact fastcode_of_div ⟨138, by decide⟩ _ _ _
    ((alnId_138 j hj) ▸ Q2.listedAt (⟨138, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨138, by decide⟩ : Fin 148) hj hq).1) colCertDiv_138_93_20_match


theorem leaf_138_95_0 (hp : 0 < (Q2.transData.getD 95 []).length)
    (j : Nat) (hj : j < (repChars.getD 138 []).length)
    (hq : (normIsRep.getD 138 []).getD j false = true) :
    species (Q2.reps (⟨95, by decide⟩ : Fin 148)) (colE2 ⟨95, by decide⟩ 0 hp)
        (rowE2 (⟨138, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨95, by decide⟩ : Fin 148))
        (colE1 ⟨95, by decide⟩ 0 (transLenTr ⟨95, by decide⟩ 0 hp))
        (rowE1 (⟨138, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨138, by decide⟩ : Fin 148) ⟨95, by decide⟩ _
      (validAt ⟨138, by decide⟩ (listedAt ⟨138, by decide⟩ hj))
      (colE1 ⟨95, by decide⟩ 0 (transLenTr ⟨95, by decide⟩ 0 hp)) T138_95
      hfix138_95 hinj138_95 hcardT138_95
      (fun i => conj_mem_of_fixedPoints _ _ (T138_95 i) (hfix138_95 i) _)
      ⟨138, by decide⟩ ⟨95, by decide⟩ _
      (Q2.validAt ⟨138, by decide⟩ (Q2.listedAt ⟨138, by decide⟩
        (alnCheck_rep ⟨138, by decide⟩ hj hq).1))
      (colE2 ⟨95, by decide⟩ 0 hp) Q2.T138_95_2 Q2.hfix138_95_2 Q2.hinj138_95_2
      Q2.hcardT138_95_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T138_95_2 i) (Q2.hfix138_95_2 i) _)
      colCert_138_95_0.hD ?_).symm
  rw [alnId_138 j hj]


theorem leaf_138_95_1 (hp : 1 < (Q2.transData.getD 95 []).length)
    (j : Nat) (hj : j < (repChars.getD 138 []).length)
    (hq : (normIsRep.getD 138 []).getD j false = true) :
    species (Q2.reps (⟨95, by decide⟩ : Fin 148)) (colE2 ⟨95, by decide⟩ 1 hp)
        (rowE2 (⟨138, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨95, by decide⟩ : Fin 148))
        (colE1 ⟨95, by decide⟩ 1 (transLenTr ⟨95, by decide⟩ 1 hp))
        (rowE1 (⟨138, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨138, by decide⟩ : Fin 148) ⟨95, by decide⟩ _
      (validAt ⟨138, by decide⟩ (listedAt ⟨138, by decide⟩ hj))
      (colE1 ⟨95, by decide⟩ 1 (transLenTr ⟨95, by decide⟩ 1 hp)) T138_95
      hfix138_95 hinj138_95 hcardT138_95
      (fun i => conj_mem_of_fixedPoints _ _ (T138_95 i) (hfix138_95 i) _)
      ⟨138, by decide⟩ ⟨95, by decide⟩ _
      (Q2.validAt ⟨138, by decide⟩ (Q2.listedAt ⟨138, by decide⟩
        (alnCheck_rep ⟨138, by decide⟩ hj hq).1))
      (colE2 ⟨95, by decide⟩ 1 hp) Q2.T138_95_2 Q2.hfix138_95_2 Q2.hinj138_95_2
      Q2.hcardT138_95_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T138_95_2 i) (Q2.hfix138_95_2 i) _)
      colCert_138_95_1.hD ?_).symm
  rw [alnId_138 j hj]


theorem leaf_138_95_2 (hp : 2 < (Q2.transData.getD 95 []).length)
    (j : Nat) (hj : j < (repChars.getD 138 []).length)
    (hq : (normIsRep.getD 138 []).getD j false = true) :
    species (Q2.reps (⟨95, by decide⟩ : Fin 148)) (colE2 ⟨95, by decide⟩ 2 hp)
        (rowE2 (⟨138, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨95, by decide⟩ : Fin 148))
        (colE1 ⟨95, by decide⟩ 2 (transLenTr ⟨95, by decide⟩ 2 hp))
        (rowE1 (⟨138, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨138, by decide⟩ : Fin 148) ⟨95, by decide⟩ _
      (validAt ⟨138, by decide⟩ (listedAt ⟨138, by decide⟩ hj))
      (colE1 ⟨95, by decide⟩ 2 (transLenTr ⟨95, by decide⟩ 2 hp)) T138_95
      hfix138_95 hinj138_95 hcardT138_95
      (fun i => conj_mem_of_fixedPoints _ _ (T138_95 i) (hfix138_95 i) _)
      ⟨138, by decide⟩ ⟨95, by decide⟩ _
      (Q2.validAt ⟨138, by decide⟩ (Q2.listedAt ⟨138, by decide⟩
        (alnCheck_rep ⟨138, by decide⟩ hj hq).1))
      (colE2 ⟨95, by decide⟩ 2 hp) Q2.T138_95_2 Q2.hfix138_95_2 Q2.hinj138_95_2
      Q2.hcardT138_95_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T138_95_2 i) (Q2.hfix138_95_2 i) _)
      colCert_138_95_2.hD ?_).symm
  rw [alnId_138 j hj]


theorem leaf_138_95_3 (hp : 3 < (Q2.transData.getD 95 []).length)
    (j : Nat) (hj : j < (repChars.getD 138 []).length)
    (hq : (normIsRep.getD 138 []).getD j false = true) :
    species (Q2.reps (⟨95, by decide⟩ : Fin 148)) (colE2 ⟨95, by decide⟩ 3 hp)
        (rowE2 (⟨138, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨95, by decide⟩ : Fin 148))
        (colE1 ⟨95, by decide⟩ 3 (transLenTr ⟨95, by decide⟩ 3 hp))
        (rowE1 (⟨138, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨138, by decide⟩ : Fin 148) ⟨95, by decide⟩ _
      (validAt ⟨138, by decide⟩ (listedAt ⟨138, by decide⟩ hj))
      (colE1 ⟨95, by decide⟩ 3 (transLenTr ⟨95, by decide⟩ 3 hp)) T138_95
      hfix138_95 hinj138_95 hcardT138_95
      (fun i => conj_mem_of_fixedPoints _ _ (T138_95 i) (hfix138_95 i) _)
      ⟨138, by decide⟩ ⟨95, by decide⟩ _
      (Q2.validAt ⟨138, by decide⟩ (Q2.listedAt ⟨138, by decide⟩
        (alnCheck_rep ⟨138, by decide⟩ hj hq).1))
      (colE2 ⟨95, by decide⟩ 3 hp) Q2.T138_95_2 Q2.hfix138_95_2 Q2.hinj138_95_2
      Q2.hcardT138_95_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T138_95_2 i) (Q2.hfix138_95_2 i) _)
      colCert_138_95_3.hD ?_).symm
  rw [alnId_138 j hj]


theorem leaf_138_95_4 (hp : 4 < (Q2.transData.getD 95 []).length)
    (j : Nat) (hj : j < (repChars.getD 138 []).length)
    (hq : (normIsRep.getD 138 []).getD j false = true) :
    species (Q2.reps (⟨95, by decide⟩ : Fin 148)) (colE2 ⟨95, by decide⟩ 4 hp)
        (rowE2 (⟨138, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨95, by decide⟩ : Fin 148))
        (colE1 ⟨95, by decide⟩ 4 (transLenTr ⟨95, by decide⟩ 4 hp))
        (rowE1 (⟨138, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨138, by decide⟩ : Fin 148) ⟨95, by decide⟩ _
      (validAt ⟨138, by decide⟩ (listedAt ⟨138, by decide⟩ hj))
      (colE1 ⟨95, by decide⟩ 4 (transLenTr ⟨95, by decide⟩ 4 hp)) T138_95
      hfix138_95 hinj138_95 hcardT138_95
      (fun i => conj_mem_of_fixedPoints _ _ (T138_95 i) (hfix138_95 i) _)
      ⟨138, by decide⟩ ⟨95, by decide⟩ _
      (Q2.validAt ⟨138, by decide⟩ (Q2.listedAt ⟨138, by decide⟩
        (alnCheck_rep ⟨138, by decide⟩ hj hq).1))
      (colE2 ⟨95, by decide⟩ 4 hp) Q2.T138_95_2 Q2.hfix138_95_2 Q2.hinj138_95_2
      Q2.hcardT138_95_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T138_95_2 i) (Q2.hfix138_95_2 i) _)
      colCert_138_95_4.hD ?_).symm
  rw [alnId_138 j hj]


theorem leaf_138_95_5 (hp : 5 < (Q2.transData.getD 95 []).length)
    (j : Nat) (hj : j < (repChars.getD 138 []).length)
    (hq : (normIsRep.getD 138 []).getD j false = true) :
    species (Q2.reps (⟨95, by decide⟩ : Fin 148)) (colE2 ⟨95, by decide⟩ 5 hp)
        (rowE2 (⟨138, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨95, by decide⟩ : Fin 148))
        (colE1 ⟨95, by decide⟩ 5 (transLenTr ⟨95, by decide⟩ 5 hp))
        (rowE1 (⟨138, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨138, by decide⟩ : Fin 148) ⟨95, by decide⟩ _
      (validAt ⟨138, by decide⟩ (listedAt ⟨138, by decide⟩ hj))
      (colE1 ⟨95, by decide⟩ 5 (transLenTr ⟨95, by decide⟩ 5 hp)) T138_95
      hfix138_95 hinj138_95 hcardT138_95
      (fun i => conj_mem_of_fixedPoints _ _ (T138_95 i) (hfix138_95 i) _)
      ⟨138, by decide⟩ ⟨95, by decide⟩ _
      (Q2.validAt ⟨138, by decide⟩ (Q2.listedAt ⟨138, by decide⟩
        (alnCheck_rep ⟨138, by decide⟩ hj hq).1))
      (colE2 ⟨95, by decide⟩ 5 hp) Q2.T138_95_2 Q2.hfix138_95_2 Q2.hinj138_95_2
      Q2.hcardT138_95_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T138_95_2 i) (Q2.hfix138_95_2 i) _)
      colCert_138_95_5.hD ?_).symm
  rw [alnId_138 j hj]


theorem leaf_138_95_10 (hp : 10 < (Q2.transData.getD 95 []).length)
    (j : Nat) (hj : j < (repChars.getD 138 []).length)
    (hq : (normIsRep.getD 138 []).getD j false = true) :
    species (Q2.reps (⟨95, by decide⟩ : Fin 148)) (colE2 ⟨95, by decide⟩ 10 hp)
        (rowE2 (⟨138, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨95, by decide⟩ : Fin 148))
        (colE1 ⟨95, by decide⟩ 10 (transLenTr ⟨95, by decide⟩ 10 hp))
        (rowE1 (⟨138, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨138, by decide⟩ : Fin 148) ⟨95, by decide⟩ _
      (validAt ⟨138, by decide⟩ (listedAt ⟨138, by decide⟩ hj))
      (colE1 ⟨95, by decide⟩ 10 (transLenTr ⟨95, by decide⟩ 10 hp)) T138_95
      hfix138_95 hinj138_95 hcardT138_95
      (fun i => conj_mem_of_fixedPoints _ _ (T138_95 i) (hfix138_95 i) _)
      ⟨138, by decide⟩ ⟨95, by decide⟩ _
      (Q2.validAt ⟨138, by decide⟩ (Q2.listedAt ⟨138, by decide⟩
        (alnCheck_rep ⟨138, by decide⟩ hj hq).1))
      (colE2 ⟨95, by decide⟩ 10 hp) Q2.T138_95_2 Q2.hfix138_95_2 Q2.hinj138_95_2
      Q2.hcardT138_95_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T138_95_2 i) (Q2.hfix138_95_2 i) _)
      colCert_138_95_10.hD ?_).symm
  rw [alnId_138 j hj]


theorem leaf_138_95_15 (hp : 15 < (Q2.transData.getD 95 []).length)
    (j : Nat) (hj : j < (repChars.getD 138 []).length)
    (hq : (normIsRep.getD 138 []).getD j false = true) :
    species (Q2.reps (⟨95, by decide⟩ : Fin 148)) (colE2 ⟨95, by decide⟩ 15 hp)
        (rowE2 (⟨138, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨95, by decide⟩ : Fin 148))
        (colE1 ⟨95, by decide⟩ 15 (transLenTr ⟨95, by decide⟩ 15 hp))
        (rowE1 (⟨138, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨138, by decide⟩ : Fin 148) ⟨95, by decide⟩ _
      (validAt ⟨138, by decide⟩ (listedAt ⟨138, by decide⟩ hj))
      (colE1 ⟨95, by decide⟩ 15 (transLenTr ⟨95, by decide⟩ 15 hp)) T138_95
      hfix138_95 hinj138_95 hcardT138_95
      (fun i => conj_mem_of_fixedPoints _ _ (T138_95 i) (hfix138_95 i) _)
      ⟨138, by decide⟩ ⟨95, by decide⟩ _
      (Q2.validAt ⟨138, by decide⟩ (Q2.listedAt ⟨138, by decide⟩
        (alnCheck_rep ⟨138, by decide⟩ hj hq).1))
      (colE2 ⟨95, by decide⟩ 15 hp) Q2.T138_95_2 Q2.hfix138_95_2 Q2.hinj138_95_2
      Q2.hcardT138_95_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T138_95_2 i) (Q2.hfix138_95_2 i) _)
      colCert_138_95_15.hD ?_).symm
  rw [alnId_138 j hj]


theorem leaf_138_95_20 (hp : 20 < (Q2.transData.getD 95 []).length)
    (j : Nat) (hj : j < (repChars.getD 138 []).length)
    (hq : (normIsRep.getD 138 []).getD j false = true) :
    species (Q2.reps (⟨95, by decide⟩ : Fin 148)) (colE2 ⟨95, by decide⟩ 20 hp)
        (rowE2 (⟨138, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨95, by decide⟩ : Fin 148))
        (colE1 ⟨95, by decide⟩ 20 (transLenTr ⟨95, by decide⟩ 20 hp))
        (rowE1 (⟨138, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨138, by decide⟩ : Fin 148) ⟨95, by decide⟩ _
      (validAt ⟨138, by decide⟩ (listedAt ⟨138, by decide⟩ hj))
      (colE1 ⟨95, by decide⟩ 20 (transLenTr ⟨95, by decide⟩ 20 hp)) T138_95
      hfix138_95 hinj138_95 hcardT138_95
      (fun i => conj_mem_of_fixedPoints _ _ (T138_95 i) (hfix138_95 i) _)
      ⟨138, by decide⟩ ⟨95, by decide⟩ _
      (Q2.validAt ⟨138, by decide⟩ (Q2.listedAt ⟨138, by decide⟩
        (alnCheck_rep ⟨138, by decide⟩ hj hq).1))
      (colE2 ⟨95, by decide⟩ 20 hp) Q2.T138_95_2 Q2.hfix138_95_2 Q2.hinj138_95_2
      Q2.hcardT138_95_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T138_95_2 i) (Q2.hfix138_95_2 i) _)
      colCert_138_95_20.hD ?_).symm
  rw [alnId_138 j hj]


theorem leaf_138_95_25 (hp : 25 < (Q2.transData.getD 95 []).length)
    (j : Nat) (hj : j < (repChars.getD 138 []).length)
    (hq : (normIsRep.getD 138 []).getD j false = true) :
    species (Q2.reps (⟨95, by decide⟩ : Fin 148)) (colE2 ⟨95, by decide⟩ 25 hp)
        (rowE2 (⟨138, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨95, by decide⟩ : Fin 148))
        (colE1 ⟨95, by decide⟩ 25 (transLenTr ⟨95, by decide⟩ 25 hp))
        (rowE1 (⟨138, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨138, by decide⟩ : Fin 148) ⟨95, by decide⟩ _
      (validAt ⟨138, by decide⟩ (listedAt ⟨138, by decide⟩ hj))
      (colE1 ⟨95, by decide⟩ 25 (transLenTr ⟨95, by decide⟩ 25 hp)) T138_95
      hfix138_95 hinj138_95 hcardT138_95
      (fun i => conj_mem_of_fixedPoints _ _ (T138_95 i) (hfix138_95 i) _)
      ⟨138, by decide⟩ ⟨95, by decide⟩ _
      (Q2.validAt ⟨138, by decide⟩ (Q2.listedAt ⟨138, by decide⟩
        (alnCheck_rep ⟨138, by decide⟩ hj hq).1))
      (colE2 ⟨95, by decide⟩ 25 hp) Q2.T138_95_2 Q2.hfix138_95_2 Q2.hinj138_95_2
      Q2.hcardT138_95_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T138_95_2 i) (Q2.hfix138_95_2 i) _)
      ?_).symm
  rw [show colData1 (⟨138, by decide⟩ : Fin 148)
        ((colE1 ⟨95, by decide⟩ 25 (transLenTr ⟨95, by decide⟩ 25 hp) : ↥(reps ⟨95, by decide⟩)) : Coordinate 1)
        T138_95 = colFn colCertDiv_138_95_25.D1 (m := 5) from colCertDiv_138_95_25.bind1,
    show colData2 (⟨138, by decide⟩ : Fin 148)
        ((colE2 ⟨95, by decide⟩ 25 hp : ↥(Q2.reps ⟨95, by decide⟩)) : Coordinate 2)
        Q2.T138_95_2 = colFn colCertDiv_138_95_25.D2 (m := 5) from colCertDiv_138_95_25.bind2]
  rw [alnId_138 j hj]
  exact fastcode_of_div ⟨138, by decide⟩ _ _ _
    ((alnId_138 j hj) ▸ Q2.listedAt (⟨138, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨138, by decide⟩ : Fin 148) hj hq).1) colCertDiv_138_95_25_match


theorem leaf_138_95_50 (hp : 50 < (Q2.transData.getD 95 []).length)
    (j : Nat) (hj : j < (repChars.getD 138 []).length)
    (hq : (normIsRep.getD 138 []).getD j false = true) :
    species (Q2.reps (⟨95, by decide⟩ : Fin 148)) (colE2 ⟨95, by decide⟩ 50 hp)
        (rowE2 (⟨138, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨95, by decide⟩ : Fin 148))
        (colE1 ⟨95, by decide⟩ 50 (transLenTr ⟨95, by decide⟩ 50 hp))
        (rowE1 (⟨138, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨138, by decide⟩ : Fin 148) ⟨95, by decide⟩ _
      (validAt ⟨138, by decide⟩ (listedAt ⟨138, by decide⟩ hj))
      (colE1 ⟨95, by decide⟩ 50 (transLenTr ⟨95, by decide⟩ 50 hp)) T138_95
      hfix138_95 hinj138_95 hcardT138_95
      (fun i => conj_mem_of_fixedPoints _ _ (T138_95 i) (hfix138_95 i) _)
      ⟨138, by decide⟩ ⟨95, by decide⟩ _
      (Q2.validAt ⟨138, by decide⟩ (Q2.listedAt ⟨138, by decide⟩
        (alnCheck_rep ⟨138, by decide⟩ hj hq).1))
      (colE2 ⟨95, by decide⟩ 50 hp) Q2.T138_95_2 Q2.hfix138_95_2 Q2.hinj138_95_2
      Q2.hcardT138_95_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T138_95_2 i) (Q2.hfix138_95_2 i) _)
      ?_).symm
  rw [show colData1 (⟨138, by decide⟩ : Fin 148)
        ((colE1 ⟨95, by decide⟩ 50 (transLenTr ⟨95, by decide⟩ 50 hp) : ↥(reps ⟨95, by decide⟩)) : Coordinate 1)
        T138_95 = colFn colCertDiv_138_95_50.D1 (m := 5) from colCertDiv_138_95_50.bind1,
    show colData2 (⟨138, by decide⟩ : Fin 148)
        ((colE2 ⟨95, by decide⟩ 50 hp : ↥(Q2.reps ⟨95, by decide⟩)) : Coordinate 2)
        Q2.T138_95_2 = colFn colCertDiv_138_95_50.D2 (m := 5) from colCertDiv_138_95_50.bind2]
  rw [alnId_138 j hj]
  exact fastcode_of_div ⟨138, by decide⟩ _ _ _
    ((alnId_138 j hj) ▸ Q2.listedAt (⟨138, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨138, by decide⟩ : Fin 148) hj hq).1) colCertDiv_138_95_50_match


theorem leaf_138_95_75 (hp : 75 < (Q2.transData.getD 95 []).length)
    (j : Nat) (hj : j < (repChars.getD 138 []).length)
    (hq : (normIsRep.getD 138 []).getD j false = true) :
    species (Q2.reps (⟨95, by decide⟩ : Fin 148)) (colE2 ⟨95, by decide⟩ 75 hp)
        (rowE2 (⟨138, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨95, by decide⟩ : Fin 148))
        (colE1 ⟨95, by decide⟩ 75 (transLenTr ⟨95, by decide⟩ 75 hp))
        (rowE1 (⟨138, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨138, by decide⟩ : Fin 148) ⟨95, by decide⟩ _
      (validAt ⟨138, by decide⟩ (listedAt ⟨138, by decide⟩ hj))
      (colE1 ⟨95, by decide⟩ 75 (transLenTr ⟨95, by decide⟩ 75 hp)) T138_95
      hfix138_95 hinj138_95 hcardT138_95
      (fun i => conj_mem_of_fixedPoints _ _ (T138_95 i) (hfix138_95 i) _)
      ⟨138, by decide⟩ ⟨95, by decide⟩ _
      (Q2.validAt ⟨138, by decide⟩ (Q2.listedAt ⟨138, by decide⟩
        (alnCheck_rep ⟨138, by decide⟩ hj hq).1))
      (colE2 ⟨95, by decide⟩ 75 hp) Q2.T138_95_2 Q2.hfix138_95_2 Q2.hinj138_95_2
      Q2.hcardT138_95_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T138_95_2 i) (Q2.hfix138_95_2 i) _)
      ?_).symm
  rw [show colData1 (⟨138, by decide⟩ : Fin 148)
        ((colE1 ⟨95, by decide⟩ 75 (transLenTr ⟨95, by decide⟩ 75 hp) : ↥(reps ⟨95, by decide⟩)) : Coordinate 1)
        T138_95 = colFn colCertDiv_138_95_75.D1 (m := 5) from colCertDiv_138_95_75.bind1,
    show colData2 (⟨138, by decide⟩ : Fin 148)
        ((colE2 ⟨95, by decide⟩ 75 hp : ↥(Q2.reps ⟨95, by decide⟩)) : Coordinate 2)
        Q2.T138_95_2 = colFn colCertDiv_138_95_75.D2 (m := 5) from colCertDiv_138_95_75.bind2]
  rw [alnId_138 j hj]
  exact fastcode_of_div ⟨138, by decide⟩ _ _ _
    ((alnId_138 j hj) ▸ Q2.listedAt (⟨138, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨138, by decide⟩ : Fin 148) hj hq).1) colCertDiv_138_95_75_match


theorem leaf_138_95_100 (hp : 100 < (Q2.transData.getD 95 []).length)
    (j : Nat) (hj : j < (repChars.getD 138 []).length)
    (hq : (normIsRep.getD 138 []).getD j false = true) :
    species (Q2.reps (⟨95, by decide⟩ : Fin 148)) (colE2 ⟨95, by decide⟩ 100 hp)
        (rowE2 (⟨138, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨95, by decide⟩ : Fin 148))
        (colE1 ⟨95, by decide⟩ 100 (transLenTr ⟨95, by decide⟩ 100 hp))
        (rowE1 (⟨138, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨138, by decide⟩ : Fin 148) ⟨95, by decide⟩ _
      (validAt ⟨138, by decide⟩ (listedAt ⟨138, by decide⟩ hj))
      (colE1 ⟨95, by decide⟩ 100 (transLenTr ⟨95, by decide⟩ 100 hp)) T138_95
      hfix138_95 hinj138_95 hcardT138_95
      (fun i => conj_mem_of_fixedPoints _ _ (T138_95 i) (hfix138_95 i) _)
      ⟨138, by decide⟩ ⟨95, by decide⟩ _
      (Q2.validAt ⟨138, by decide⟩ (Q2.listedAt ⟨138, by decide⟩
        (alnCheck_rep ⟨138, by decide⟩ hj hq).1))
      (colE2 ⟨95, by decide⟩ 100 hp) Q2.T138_95_2 Q2.hfix138_95_2 Q2.hinj138_95_2
      Q2.hcardT138_95_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T138_95_2 i) (Q2.hfix138_95_2 i) _)
      ?_).symm
  rw [show colData1 (⟨138, by decide⟩ : Fin 148)
        ((colE1 ⟨95, by decide⟩ 100 (transLenTr ⟨95, by decide⟩ 100 hp) : ↥(reps ⟨95, by decide⟩)) : Coordinate 1)
        T138_95 = colFn colCertDiv_138_95_100.D1 (m := 5) from colCertDiv_138_95_100.bind1,
    show colData2 (⟨138, by decide⟩ : Fin 148)
        ((colE2 ⟨95, by decide⟩ 100 hp : ↥(Q2.reps ⟨95, by decide⟩)) : Coordinate 2)
        Q2.T138_95_2 = colFn colCertDiv_138_95_100.D2 (m := 5) from colCertDiv_138_95_100.bind2]
  rw [alnId_138 j hj]
  exact fastcode_of_div ⟨138, by decide⟩ _ _ _
    ((alnId_138 j hj) ▸ Q2.listedAt (⟨138, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨138, by decide⟩ : Fin 148) hj hq).1) colCertDiv_138_95_100_match


theorem leaf_138_104_0 (hp : 0 < (Q2.transData.getD 104 []).length)
    (j : Nat) (hj : j < (repChars.getD 138 []).length)
    (hq : (normIsRep.getD 138 []).getD j false = true) :
    species (Q2.reps (⟨104, by decide⟩ : Fin 148)) (colE2 ⟨104, by decide⟩ 0 hp)
        (rowE2 (⟨138, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨104, by decide⟩ : Fin 148))
        (colE1 ⟨104, by decide⟩ 0 (transLenTr ⟨104, by decide⟩ 0 hp))
        (rowE1 (⟨138, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨138, by decide⟩ : Fin 148) ⟨104, by decide⟩ _
      (validAt ⟨138, by decide⟩ (listedAt ⟨138, by decide⟩ hj))
      (colE1 ⟨104, by decide⟩ 0 (transLenTr ⟨104, by decide⟩ 0 hp)) T138_104
      hfix138_104 hinj138_104 hcardT138_104
      (fun i => conj_mem_of_fixedPoints _ _ (T138_104 i) (hfix138_104 i) _)
      ⟨138, by decide⟩ ⟨104, by decide⟩ _
      (Q2.validAt ⟨138, by decide⟩ (Q2.listedAt ⟨138, by decide⟩
        (alnCheck_rep ⟨138, by decide⟩ hj hq).1))
      (colE2 ⟨104, by decide⟩ 0 hp) Q2.T138_104_2 Q2.hfix138_104_2 Q2.hinj138_104_2
      Q2.hcardT138_104_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T138_104_2 i) (Q2.hfix138_104_2 i) _)
      colCert_138_104_0.hD ?_).symm
  rw [alnId_138 j hj]


theorem leaf_138_104_1 (hp : 1 < (Q2.transData.getD 104 []).length)
    (j : Nat) (hj : j < (repChars.getD 138 []).length)
    (hq : (normIsRep.getD 138 []).getD j false = true) :
    species (Q2.reps (⟨104, by decide⟩ : Fin 148)) (colE2 ⟨104, by decide⟩ 1 hp)
        (rowE2 (⟨138, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨104, by decide⟩ : Fin 148))
        (colE1 ⟨104, by decide⟩ 1 (transLenTr ⟨104, by decide⟩ 1 hp))
        (rowE1 (⟨138, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨138, by decide⟩ : Fin 148) ⟨104, by decide⟩ _
      (validAt ⟨138, by decide⟩ (listedAt ⟨138, by decide⟩ hj))
      (colE1 ⟨104, by decide⟩ 1 (transLenTr ⟨104, by decide⟩ 1 hp)) T138_104
      hfix138_104 hinj138_104 hcardT138_104
      (fun i => conj_mem_of_fixedPoints _ _ (T138_104 i) (hfix138_104 i) _)
      ⟨138, by decide⟩ ⟨104, by decide⟩ _
      (Q2.validAt ⟨138, by decide⟩ (Q2.listedAt ⟨138, by decide⟩
        (alnCheck_rep ⟨138, by decide⟩ hj hq).1))
      (colE2 ⟨104, by decide⟩ 1 hp) Q2.T138_104_2 Q2.hfix138_104_2 Q2.hinj138_104_2
      Q2.hcardT138_104_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T138_104_2 i) (Q2.hfix138_104_2 i) _)
      colCert_138_104_1.hD ?_).symm
  rw [alnId_138 j hj]


theorem leaf_138_104_2 (hp : 2 < (Q2.transData.getD 104 []).length)
    (j : Nat) (hj : j < (repChars.getD 138 []).length)
    (hq : (normIsRep.getD 138 []).getD j false = true) :
    species (Q2.reps (⟨104, by decide⟩ : Fin 148)) (colE2 ⟨104, by decide⟩ 2 hp)
        (rowE2 (⟨138, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨104, by decide⟩ : Fin 148))
        (colE1 ⟨104, by decide⟩ 2 (transLenTr ⟨104, by decide⟩ 2 hp))
        (rowE1 (⟨138, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨138, by decide⟩ : Fin 148) ⟨104, by decide⟩ _
      (validAt ⟨138, by decide⟩ (listedAt ⟨138, by decide⟩ hj))
      (colE1 ⟨104, by decide⟩ 2 (transLenTr ⟨104, by decide⟩ 2 hp)) T138_104
      hfix138_104 hinj138_104 hcardT138_104
      (fun i => conj_mem_of_fixedPoints _ _ (T138_104 i) (hfix138_104 i) _)
      ⟨138, by decide⟩ ⟨104, by decide⟩ _
      (Q2.validAt ⟨138, by decide⟩ (Q2.listedAt ⟨138, by decide⟩
        (alnCheck_rep ⟨138, by decide⟩ hj hq).1))
      (colE2 ⟨104, by decide⟩ 2 hp) Q2.T138_104_2 Q2.hfix138_104_2 Q2.hinj138_104_2
      Q2.hcardT138_104_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T138_104_2 i) (Q2.hfix138_104_2 i) _)
      colCert_138_104_2.hD ?_).symm
  rw [alnId_138 j hj]


theorem leaf_138_104_3 (hp : 3 < (Q2.transData.getD 104 []).length)
    (j : Nat) (hj : j < (repChars.getD 138 []).length)
    (hq : (normIsRep.getD 138 []).getD j false = true) :
    species (Q2.reps (⟨104, by decide⟩ : Fin 148)) (colE2 ⟨104, by decide⟩ 3 hp)
        (rowE2 (⟨138, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨104, by decide⟩ : Fin 148))
        (colE1 ⟨104, by decide⟩ 3 (transLenTr ⟨104, by decide⟩ 3 hp))
        (rowE1 (⟨138, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨138, by decide⟩ : Fin 148) ⟨104, by decide⟩ _
      (validAt ⟨138, by decide⟩ (listedAt ⟨138, by decide⟩ hj))
      (colE1 ⟨104, by decide⟩ 3 (transLenTr ⟨104, by decide⟩ 3 hp)) T138_104
      hfix138_104 hinj138_104 hcardT138_104
      (fun i => conj_mem_of_fixedPoints _ _ (T138_104 i) (hfix138_104 i) _)
      ⟨138, by decide⟩ ⟨104, by decide⟩ _
      (Q2.validAt ⟨138, by decide⟩ (Q2.listedAt ⟨138, by decide⟩
        (alnCheck_rep ⟨138, by decide⟩ hj hq).1))
      (colE2 ⟨104, by decide⟩ 3 hp) Q2.T138_104_2 Q2.hfix138_104_2 Q2.hinj138_104_2
      Q2.hcardT138_104_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T138_104_2 i) (Q2.hfix138_104_2 i) _)
      colCert_138_104_3.hD ?_).symm
  rw [alnId_138 j hj]


theorem leaf_138_104_4 (hp : 4 < (Q2.transData.getD 104 []).length)
    (j : Nat) (hj : j < (repChars.getD 138 []).length)
    (hq : (normIsRep.getD 138 []).getD j false = true) :
    species (Q2.reps (⟨104, by decide⟩ : Fin 148)) (colE2 ⟨104, by decide⟩ 4 hp)
        (rowE2 (⟨138, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨104, by decide⟩ : Fin 148))
        (colE1 ⟨104, by decide⟩ 4 (transLenTr ⟨104, by decide⟩ 4 hp))
        (rowE1 (⟨138, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨138, by decide⟩ : Fin 148) ⟨104, by decide⟩ _
      (validAt ⟨138, by decide⟩ (listedAt ⟨138, by decide⟩ hj))
      (colE1 ⟨104, by decide⟩ 4 (transLenTr ⟨104, by decide⟩ 4 hp)) T138_104
      hfix138_104 hinj138_104 hcardT138_104
      (fun i => conj_mem_of_fixedPoints _ _ (T138_104 i) (hfix138_104 i) _)
      ⟨138, by decide⟩ ⟨104, by decide⟩ _
      (Q2.validAt ⟨138, by decide⟩ (Q2.listedAt ⟨138, by decide⟩
        (alnCheck_rep ⟨138, by decide⟩ hj hq).1))
      (colE2 ⟨104, by decide⟩ 4 hp) Q2.T138_104_2 Q2.hfix138_104_2 Q2.hinj138_104_2
      Q2.hcardT138_104_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T138_104_2 i) (Q2.hfix138_104_2 i) _)
      colCert_138_104_4.hD ?_).symm
  rw [alnId_138 j hj]


theorem leaf_138_104_5 (hp : 5 < (Q2.transData.getD 104 []).length)
    (j : Nat) (hj : j < (repChars.getD 138 []).length)
    (hq : (normIsRep.getD 138 []).getD j false = true) :
    species (Q2.reps (⟨104, by decide⟩ : Fin 148)) (colE2 ⟨104, by decide⟩ 5 hp)
        (rowE2 (⟨138, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨104, by decide⟩ : Fin 148))
        (colE1 ⟨104, by decide⟩ 5 (transLenTr ⟨104, by decide⟩ 5 hp))
        (rowE1 (⟨138, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨138, by decide⟩ : Fin 148) ⟨104, by decide⟩ _
      (validAt ⟨138, by decide⟩ (listedAt ⟨138, by decide⟩ hj))
      (colE1 ⟨104, by decide⟩ 5 (transLenTr ⟨104, by decide⟩ 5 hp)) T138_104
      hfix138_104 hinj138_104 hcardT138_104
      (fun i => conj_mem_of_fixedPoints _ _ (T138_104 i) (hfix138_104 i) _)
      ⟨138, by decide⟩ ⟨104, by decide⟩ _
      (Q2.validAt ⟨138, by decide⟩ (Q2.listedAt ⟨138, by decide⟩
        (alnCheck_rep ⟨138, by decide⟩ hj hq).1))
      (colE2 ⟨104, by decide⟩ 5 hp) Q2.T138_104_2 Q2.hfix138_104_2 Q2.hinj138_104_2
      Q2.hcardT138_104_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T138_104_2 i) (Q2.hfix138_104_2 i) _)
      ?_).symm
  rw [show colData1 (⟨138, by decide⟩ : Fin 148)
        ((colE1 ⟨104, by decide⟩ 5 (transLenTr ⟨104, by decide⟩ 5 hp) : ↥(reps ⟨104, by decide⟩)) : Coordinate 1)
        T138_104 = colFn colCertDiv_138_104_5.D1 (m := 5) from colCertDiv_138_104_5.bind1,
    show colData2 (⟨138, by decide⟩ : Fin 148)
        ((colE2 ⟨104, by decide⟩ 5 hp : ↥(Q2.reps ⟨104, by decide⟩)) : Coordinate 2)
        Q2.T138_104_2 = colFn colCertDiv_138_104_5.D2 (m := 5) from colCertDiv_138_104_5.bind2]
  rw [alnId_138 j hj]
  exact fastcode_of_div ⟨138, by decide⟩ _ _ _
    ((alnId_138 j hj) ▸ Q2.listedAt (⟨138, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨138, by decide⟩ : Fin 148) hj hq).1) colCertDiv_138_104_5_match


theorem leaf_138_104_10 (hp : 10 < (Q2.transData.getD 104 []).length)
    (j : Nat) (hj : j < (repChars.getD 138 []).length)
    (hq : (normIsRep.getD 138 []).getD j false = true) :
    species (Q2.reps (⟨104, by decide⟩ : Fin 148)) (colE2 ⟨104, by decide⟩ 10 hp)
        (rowE2 (⟨138, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨104, by decide⟩ : Fin 148))
        (colE1 ⟨104, by decide⟩ 10 (transLenTr ⟨104, by decide⟩ 10 hp))
        (rowE1 (⟨138, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨138, by decide⟩ : Fin 148) ⟨104, by decide⟩ _
      (validAt ⟨138, by decide⟩ (listedAt ⟨138, by decide⟩ hj))
      (colE1 ⟨104, by decide⟩ 10 (transLenTr ⟨104, by decide⟩ 10 hp)) T138_104
      hfix138_104 hinj138_104 hcardT138_104
      (fun i => conj_mem_of_fixedPoints _ _ (T138_104 i) (hfix138_104 i) _)
      ⟨138, by decide⟩ ⟨104, by decide⟩ _
      (Q2.validAt ⟨138, by decide⟩ (Q2.listedAt ⟨138, by decide⟩
        (alnCheck_rep ⟨138, by decide⟩ hj hq).1))
      (colE2 ⟨104, by decide⟩ 10 hp) Q2.T138_104_2 Q2.hfix138_104_2 Q2.hinj138_104_2
      Q2.hcardT138_104_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T138_104_2 i) (Q2.hfix138_104_2 i) _)
      ?_).symm
  rw [show colData1 (⟨138, by decide⟩ : Fin 148)
        ((colE1 ⟨104, by decide⟩ 10 (transLenTr ⟨104, by decide⟩ 10 hp) : ↥(reps ⟨104, by decide⟩)) : Coordinate 1)
        T138_104 = colFn colCertDiv_138_104_10.D1 (m := 5) from colCertDiv_138_104_10.bind1,
    show colData2 (⟨138, by decide⟩ : Fin 148)
        ((colE2 ⟨104, by decide⟩ 10 hp : ↥(Q2.reps ⟨104, by decide⟩)) : Coordinate 2)
        Q2.T138_104_2 = colFn colCertDiv_138_104_10.D2 (m := 5) from colCertDiv_138_104_10.bind2]
  rw [alnId_138 j hj]
  exact fastcode_of_div ⟨138, by decide⟩ _ _ _
    ((alnId_138 j hj) ▸ Q2.listedAt (⟨138, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨138, by decide⟩ : Fin 148) hj hq).1) colCertDiv_138_104_10_match


theorem leaf_138_104_15 (hp : 15 < (Q2.transData.getD 104 []).length)
    (j : Nat) (hj : j < (repChars.getD 138 []).length)
    (hq : (normIsRep.getD 138 []).getD j false = true) :
    species (Q2.reps (⟨104, by decide⟩ : Fin 148)) (colE2 ⟨104, by decide⟩ 15 hp)
        (rowE2 (⟨138, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨104, by decide⟩ : Fin 148))
        (colE1 ⟨104, by decide⟩ 15 (transLenTr ⟨104, by decide⟩ 15 hp))
        (rowE1 (⟨138, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨138, by decide⟩ : Fin 148) ⟨104, by decide⟩ _
      (validAt ⟨138, by decide⟩ (listedAt ⟨138, by decide⟩ hj))
      (colE1 ⟨104, by decide⟩ 15 (transLenTr ⟨104, by decide⟩ 15 hp)) T138_104
      hfix138_104 hinj138_104 hcardT138_104
      (fun i => conj_mem_of_fixedPoints _ _ (T138_104 i) (hfix138_104 i) _)
      ⟨138, by decide⟩ ⟨104, by decide⟩ _
      (Q2.validAt ⟨138, by decide⟩ (Q2.listedAt ⟨138, by decide⟩
        (alnCheck_rep ⟨138, by decide⟩ hj hq).1))
      (colE2 ⟨104, by decide⟩ 15 hp) Q2.T138_104_2 Q2.hfix138_104_2 Q2.hinj138_104_2
      Q2.hcardT138_104_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T138_104_2 i) (Q2.hfix138_104_2 i) _)
      ?_).symm
  rw [show colData1 (⟨138, by decide⟩ : Fin 148)
        ((colE1 ⟨104, by decide⟩ 15 (transLenTr ⟨104, by decide⟩ 15 hp) : ↥(reps ⟨104, by decide⟩)) : Coordinate 1)
        T138_104 = colFn colCertDiv_138_104_15.D1 (m := 5) from colCertDiv_138_104_15.bind1,
    show colData2 (⟨138, by decide⟩ : Fin 148)
        ((colE2 ⟨104, by decide⟩ 15 hp : ↥(Q2.reps ⟨104, by decide⟩)) : Coordinate 2)
        Q2.T138_104_2 = colFn colCertDiv_138_104_15.D2 (m := 5) from colCertDiv_138_104_15.bind2]
  rw [alnId_138 j hj]
  exact fastcode_of_div ⟨138, by decide⟩ _ _ _
    ((alnId_138 j hj) ▸ Q2.listedAt (⟨138, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨138, by decide⟩ : Fin 148) hj hq).1) colCertDiv_138_104_15_match


theorem leaf_138_104_20 (hp : 20 < (Q2.transData.getD 104 []).length)
    (j : Nat) (hj : j < (repChars.getD 138 []).length)
    (hq : (normIsRep.getD 138 []).getD j false = true) :
    species (Q2.reps (⟨104, by decide⟩ : Fin 148)) (colE2 ⟨104, by decide⟩ 20 hp)
        (rowE2 (⟨138, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨104, by decide⟩ : Fin 148))
        (colE1 ⟨104, by decide⟩ 20 (transLenTr ⟨104, by decide⟩ 20 hp))
        (rowE1 (⟨138, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨138, by decide⟩ : Fin 148) ⟨104, by decide⟩ _
      (validAt ⟨138, by decide⟩ (listedAt ⟨138, by decide⟩ hj))
      (colE1 ⟨104, by decide⟩ 20 (transLenTr ⟨104, by decide⟩ 20 hp)) T138_104
      hfix138_104 hinj138_104 hcardT138_104
      (fun i => conj_mem_of_fixedPoints _ _ (T138_104 i) (hfix138_104 i) _)
      ⟨138, by decide⟩ ⟨104, by decide⟩ _
      (Q2.validAt ⟨138, by decide⟩ (Q2.listedAt ⟨138, by decide⟩
        (alnCheck_rep ⟨138, by decide⟩ hj hq).1))
      (colE2 ⟨104, by decide⟩ 20 hp) Q2.T138_104_2 Q2.hfix138_104_2 Q2.hinj138_104_2
      Q2.hcardT138_104_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T138_104_2 i) (Q2.hfix138_104_2 i) _)
      ?_).symm
  rw [show colData1 (⟨138, by decide⟩ : Fin 148)
        ((colE1 ⟨104, by decide⟩ 20 (transLenTr ⟨104, by decide⟩ 20 hp) : ↥(reps ⟨104, by decide⟩)) : Coordinate 1)
        T138_104 = colFn colCertDiv_138_104_20.D1 (m := 5) from colCertDiv_138_104_20.bind1,
    show colData2 (⟨138, by decide⟩ : Fin 148)
        ((colE2 ⟨104, by decide⟩ 20 hp : ↥(Q2.reps ⟨104, by decide⟩)) : Coordinate 2)
        Q2.T138_104_2 = colFn colCertDiv_138_104_20.D2 (m := 5) from colCertDiv_138_104_20.bind2]
  rw [alnId_138 j hj]
  exact fastcode_of_div ⟨138, by decide⟩ _ _ _
    ((alnId_138 j hj) ▸ Q2.listedAt (⟨138, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨138, by decide⟩ : Fin 148) hj hq).1) colCertDiv_138_104_20_match


theorem leaf_138_106_0 (hp : 0 < (Q2.transData.getD 106 []).length)
    (j : Nat) (hj : j < (repChars.getD 138 []).length)
    (hq : (normIsRep.getD 138 []).getD j false = true) :
    species (Q2.reps (⟨106, by decide⟩ : Fin 148)) (colE2 ⟨106, by decide⟩ 0 hp)
        (rowE2 (⟨138, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨106, by decide⟩ : Fin 148))
        (colE1 ⟨106, by decide⟩ 0 (transLenTr ⟨106, by decide⟩ 0 hp))
        (rowE1 (⟨138, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨138, by decide⟩ : Fin 148) ⟨106, by decide⟩ _
      (validAt ⟨138, by decide⟩ (listedAt ⟨138, by decide⟩ hj))
      (colE1 ⟨106, by decide⟩ 0 (transLenTr ⟨106, by decide⟩ 0 hp)) T138_106
      hfix138_106 hinj138_106 hcardT138_106
      (fun i => conj_mem_of_fixedPoints _ _ (T138_106 i) (hfix138_106 i) _)
      ⟨138, by decide⟩ ⟨106, by decide⟩ _
      (Q2.validAt ⟨138, by decide⟩ (Q2.listedAt ⟨138, by decide⟩
        (alnCheck_rep ⟨138, by decide⟩ hj hq).1))
      (colE2 ⟨106, by decide⟩ 0 hp) Q2.T138_106_2 Q2.hfix138_106_2 Q2.hinj138_106_2
      Q2.hcardT138_106_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T138_106_2 i) (Q2.hfix138_106_2 i) _)
      colCert_138_106_0.hD ?_).symm
  rw [alnId_138 j hj]


theorem leaf_138_106_1 (hp : 1 < (Q2.transData.getD 106 []).length)
    (j : Nat) (hj : j < (repChars.getD 138 []).length)
    (hq : (normIsRep.getD 138 []).getD j false = true) :
    species (Q2.reps (⟨106, by decide⟩ : Fin 148)) (colE2 ⟨106, by decide⟩ 1 hp)
        (rowE2 (⟨138, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨106, by decide⟩ : Fin 148))
        (colE1 ⟨106, by decide⟩ 1 (transLenTr ⟨106, by decide⟩ 1 hp))
        (rowE1 (⟨138, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨138, by decide⟩ : Fin 148) ⟨106, by decide⟩ _
      (validAt ⟨138, by decide⟩ (listedAt ⟨138, by decide⟩ hj))
      (colE1 ⟨106, by decide⟩ 1 (transLenTr ⟨106, by decide⟩ 1 hp)) T138_106
      hfix138_106 hinj138_106 hcardT138_106
      (fun i => conj_mem_of_fixedPoints _ _ (T138_106 i) (hfix138_106 i) _)
      ⟨138, by decide⟩ ⟨106, by decide⟩ _
      (Q2.validAt ⟨138, by decide⟩ (Q2.listedAt ⟨138, by decide⟩
        (alnCheck_rep ⟨138, by decide⟩ hj hq).1))
      (colE2 ⟨106, by decide⟩ 1 hp) Q2.T138_106_2 Q2.hfix138_106_2 Q2.hinj138_106_2
      Q2.hcardT138_106_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T138_106_2 i) (Q2.hfix138_106_2 i) _)
      colCert_138_106_1.hD ?_).symm
  rw [alnId_138 j hj]


theorem leaf_138_106_2 (hp : 2 < (Q2.transData.getD 106 []).length)
    (j : Nat) (hj : j < (repChars.getD 138 []).length)
    (hq : (normIsRep.getD 138 []).getD j false = true) :
    species (Q2.reps (⟨106, by decide⟩ : Fin 148)) (colE2 ⟨106, by decide⟩ 2 hp)
        (rowE2 (⟨138, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨106, by decide⟩ : Fin 148))
        (colE1 ⟨106, by decide⟩ 2 (transLenTr ⟨106, by decide⟩ 2 hp))
        (rowE1 (⟨138, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨138, by decide⟩ : Fin 148) ⟨106, by decide⟩ _
      (validAt ⟨138, by decide⟩ (listedAt ⟨138, by decide⟩ hj))
      (colE1 ⟨106, by decide⟩ 2 (transLenTr ⟨106, by decide⟩ 2 hp)) T138_106
      hfix138_106 hinj138_106 hcardT138_106
      (fun i => conj_mem_of_fixedPoints _ _ (T138_106 i) (hfix138_106 i) _)
      ⟨138, by decide⟩ ⟨106, by decide⟩ _
      (Q2.validAt ⟨138, by decide⟩ (Q2.listedAt ⟨138, by decide⟩
        (alnCheck_rep ⟨138, by decide⟩ hj hq).1))
      (colE2 ⟨106, by decide⟩ 2 hp) Q2.T138_106_2 Q2.hfix138_106_2 Q2.hinj138_106_2
      Q2.hcardT138_106_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T138_106_2 i) (Q2.hfix138_106_2 i) _)
      colCert_138_106_2.hD ?_).symm
  rw [alnId_138 j hj]


theorem leaf_138_106_3 (hp : 3 < (Q2.transData.getD 106 []).length)
    (j : Nat) (hj : j < (repChars.getD 138 []).length)
    (hq : (normIsRep.getD 138 []).getD j false = true) :
    species (Q2.reps (⟨106, by decide⟩ : Fin 148)) (colE2 ⟨106, by decide⟩ 3 hp)
        (rowE2 (⟨138, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨106, by decide⟩ : Fin 148))
        (colE1 ⟨106, by decide⟩ 3 (transLenTr ⟨106, by decide⟩ 3 hp))
        (rowE1 (⟨138, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨138, by decide⟩ : Fin 148) ⟨106, by decide⟩ _
      (validAt ⟨138, by decide⟩ (listedAt ⟨138, by decide⟩ hj))
      (colE1 ⟨106, by decide⟩ 3 (transLenTr ⟨106, by decide⟩ 3 hp)) T138_106
      hfix138_106 hinj138_106 hcardT138_106
      (fun i => conj_mem_of_fixedPoints _ _ (T138_106 i) (hfix138_106 i) _)
      ⟨138, by decide⟩ ⟨106, by decide⟩ _
      (Q2.validAt ⟨138, by decide⟩ (Q2.listedAt ⟨138, by decide⟩
        (alnCheck_rep ⟨138, by decide⟩ hj hq).1))
      (colE2 ⟨106, by decide⟩ 3 hp) Q2.T138_106_2 Q2.hfix138_106_2 Q2.hinj138_106_2
      Q2.hcardT138_106_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T138_106_2 i) (Q2.hfix138_106_2 i) _)
      colCert_138_106_3.hD ?_).symm
  rw [alnId_138 j hj]


theorem leaf_138_106_4 (hp : 4 < (Q2.transData.getD 106 []).length)
    (j : Nat) (hj : j < (repChars.getD 138 []).length)
    (hq : (normIsRep.getD 138 []).getD j false = true) :
    species (Q2.reps (⟨106, by decide⟩ : Fin 148)) (colE2 ⟨106, by decide⟩ 4 hp)
        (rowE2 (⟨138, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨106, by decide⟩ : Fin 148))
        (colE1 ⟨106, by decide⟩ 4 (transLenTr ⟨106, by decide⟩ 4 hp))
        (rowE1 (⟨138, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨138, by decide⟩ : Fin 148) ⟨106, by decide⟩ _
      (validAt ⟨138, by decide⟩ (listedAt ⟨138, by decide⟩ hj))
      (colE1 ⟨106, by decide⟩ 4 (transLenTr ⟨106, by decide⟩ 4 hp)) T138_106
      hfix138_106 hinj138_106 hcardT138_106
      (fun i => conj_mem_of_fixedPoints _ _ (T138_106 i) (hfix138_106 i) _)
      ⟨138, by decide⟩ ⟨106, by decide⟩ _
      (Q2.validAt ⟨138, by decide⟩ (Q2.listedAt ⟨138, by decide⟩
        (alnCheck_rep ⟨138, by decide⟩ hj hq).1))
      (colE2 ⟨106, by decide⟩ 4 hp) Q2.T138_106_2 Q2.hfix138_106_2 Q2.hinj138_106_2
      Q2.hcardT138_106_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T138_106_2 i) (Q2.hfix138_106_2 i) _)
      colCert_138_106_4.hD ?_).symm
  rw [alnId_138 j hj]


theorem leaf_138_106_5 (hp : 5 < (Q2.transData.getD 106 []).length)
    (j : Nat) (hj : j < (repChars.getD 138 []).length)
    (hq : (normIsRep.getD 138 []).getD j false = true) :
    species (Q2.reps (⟨106, by decide⟩ : Fin 148)) (colE2 ⟨106, by decide⟩ 5 hp)
        (rowE2 (⟨138, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨106, by decide⟩ : Fin 148))
        (colE1 ⟨106, by decide⟩ 5 (transLenTr ⟨106, by decide⟩ 5 hp))
        (rowE1 (⟨138, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨138, by decide⟩ : Fin 148) ⟨106, by decide⟩ _
      (validAt ⟨138, by decide⟩ (listedAt ⟨138, by decide⟩ hj))
      (colE1 ⟨106, by decide⟩ 5 (transLenTr ⟨106, by decide⟩ 5 hp)) T138_106
      hfix138_106 hinj138_106 hcardT138_106
      (fun i => conj_mem_of_fixedPoints _ _ (T138_106 i) (hfix138_106 i) _)
      ⟨138, by decide⟩ ⟨106, by decide⟩ _
      (Q2.validAt ⟨138, by decide⟩ (Q2.listedAt ⟨138, by decide⟩
        (alnCheck_rep ⟨138, by decide⟩ hj hq).1))
      (colE2 ⟨106, by decide⟩ 5 hp) Q2.T138_106_2 Q2.hfix138_106_2 Q2.hinj138_106_2
      Q2.hcardT138_106_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T138_106_2 i) (Q2.hfix138_106_2 i) _)
      ?_).symm
  rw [show colData1 (⟨138, by decide⟩ : Fin 148)
        ((colE1 ⟨106, by decide⟩ 5 (transLenTr ⟨106, by decide⟩ 5 hp) : ↥(reps ⟨106, by decide⟩)) : Coordinate 1)
        T138_106 = colFn colCertDiv_138_106_5.D1 (m := 5) from colCertDiv_138_106_5.bind1,
    show colData2 (⟨138, by decide⟩ : Fin 148)
        ((colE2 ⟨106, by decide⟩ 5 hp : ↥(Q2.reps ⟨106, by decide⟩)) : Coordinate 2)
        Q2.T138_106_2 = colFn colCertDiv_138_106_5.D2 (m := 5) from colCertDiv_138_106_5.bind2]
  rw [alnId_138 j hj]
  exact fastcode_of_div ⟨138, by decide⟩ _ _ _
    ((alnId_138 j hj) ▸ Q2.listedAt (⟨138, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨138, by decide⟩ : Fin 148) hj hq).1) colCertDiv_138_106_5_match


theorem leaf_138_106_10 (hp : 10 < (Q2.transData.getD 106 []).length)
    (j : Nat) (hj : j < (repChars.getD 138 []).length)
    (hq : (normIsRep.getD 138 []).getD j false = true) :
    species (Q2.reps (⟨106, by decide⟩ : Fin 148)) (colE2 ⟨106, by decide⟩ 10 hp)
        (rowE2 (⟨138, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨106, by decide⟩ : Fin 148))
        (colE1 ⟨106, by decide⟩ 10 (transLenTr ⟨106, by decide⟩ 10 hp))
        (rowE1 (⟨138, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨138, by decide⟩ : Fin 148) ⟨106, by decide⟩ _
      (validAt ⟨138, by decide⟩ (listedAt ⟨138, by decide⟩ hj))
      (colE1 ⟨106, by decide⟩ 10 (transLenTr ⟨106, by decide⟩ 10 hp)) T138_106
      hfix138_106 hinj138_106 hcardT138_106
      (fun i => conj_mem_of_fixedPoints _ _ (T138_106 i) (hfix138_106 i) _)
      ⟨138, by decide⟩ ⟨106, by decide⟩ _
      (Q2.validAt ⟨138, by decide⟩ (Q2.listedAt ⟨138, by decide⟩
        (alnCheck_rep ⟨138, by decide⟩ hj hq).1))
      (colE2 ⟨106, by decide⟩ 10 hp) Q2.T138_106_2 Q2.hfix138_106_2 Q2.hinj138_106_2
      Q2.hcardT138_106_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T138_106_2 i) (Q2.hfix138_106_2 i) _)
      ?_).symm
  rw [show colData1 (⟨138, by decide⟩ : Fin 148)
        ((colE1 ⟨106, by decide⟩ 10 (transLenTr ⟨106, by decide⟩ 10 hp) : ↥(reps ⟨106, by decide⟩)) : Coordinate 1)
        T138_106 = colFn colCertDiv_138_106_10.D1 (m := 5) from colCertDiv_138_106_10.bind1,
    show colData2 (⟨138, by decide⟩ : Fin 148)
        ((colE2 ⟨106, by decide⟩ 10 hp : ↥(Q2.reps ⟨106, by decide⟩)) : Coordinate 2)
        Q2.T138_106_2 = colFn colCertDiv_138_106_10.D2 (m := 5) from colCertDiv_138_106_10.bind2]
  rw [alnId_138 j hj]
  exact fastcode_of_div ⟨138, by decide⟩ _ _ _
    ((alnId_138 j hj) ▸ Q2.listedAt (⟨138, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨138, by decide⟩ : Fin 148) hj hq).1) colCertDiv_138_106_10_match


theorem leaf_138_106_15 (hp : 15 < (Q2.transData.getD 106 []).length)
    (j : Nat) (hj : j < (repChars.getD 138 []).length)
    (hq : (normIsRep.getD 138 []).getD j false = true) :
    species (Q2.reps (⟨106, by decide⟩ : Fin 148)) (colE2 ⟨106, by decide⟩ 15 hp)
        (rowE2 (⟨138, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨106, by decide⟩ : Fin 148))
        (colE1 ⟨106, by decide⟩ 15 (transLenTr ⟨106, by decide⟩ 15 hp))
        (rowE1 (⟨138, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨138, by decide⟩ : Fin 148) ⟨106, by decide⟩ _
      (validAt ⟨138, by decide⟩ (listedAt ⟨138, by decide⟩ hj))
      (colE1 ⟨106, by decide⟩ 15 (transLenTr ⟨106, by decide⟩ 15 hp)) T138_106
      hfix138_106 hinj138_106 hcardT138_106
      (fun i => conj_mem_of_fixedPoints _ _ (T138_106 i) (hfix138_106 i) _)
      ⟨138, by decide⟩ ⟨106, by decide⟩ _
      (Q2.validAt ⟨138, by decide⟩ (Q2.listedAt ⟨138, by decide⟩
        (alnCheck_rep ⟨138, by decide⟩ hj hq).1))
      (colE2 ⟨106, by decide⟩ 15 hp) Q2.T138_106_2 Q2.hfix138_106_2 Q2.hinj138_106_2
      Q2.hcardT138_106_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T138_106_2 i) (Q2.hfix138_106_2 i) _)
      ?_).symm
  rw [show colData1 (⟨138, by decide⟩ : Fin 148)
        ((colE1 ⟨106, by decide⟩ 15 (transLenTr ⟨106, by decide⟩ 15 hp) : ↥(reps ⟨106, by decide⟩)) : Coordinate 1)
        T138_106 = colFn colCertDiv_138_106_15.D1 (m := 5) from colCertDiv_138_106_15.bind1,
    show colData2 (⟨138, by decide⟩ : Fin 148)
        ((colE2 ⟨106, by decide⟩ 15 hp : ↥(Q2.reps ⟨106, by decide⟩)) : Coordinate 2)
        Q2.T138_106_2 = colFn colCertDiv_138_106_15.D2 (m := 5) from colCertDiv_138_106_15.bind2]
  rw [alnId_138 j hj]
  exact fastcode_of_div ⟨138, by decide⟩ _ _ _
    ((alnId_138 j hj) ▸ Q2.listedAt (⟨138, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨138, by decide⟩ : Fin 148) hj hq).1) colCertDiv_138_106_15_match


theorem leaf_138_106_20 (hp : 20 < (Q2.transData.getD 106 []).length)
    (j : Nat) (hj : j < (repChars.getD 138 []).length)
    (hq : (normIsRep.getD 138 []).getD j false = true) :
    species (Q2.reps (⟨106, by decide⟩ : Fin 148)) (colE2 ⟨106, by decide⟩ 20 hp)
        (rowE2 (⟨138, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨106, by decide⟩ : Fin 148))
        (colE1 ⟨106, by decide⟩ 20 (transLenTr ⟨106, by decide⟩ 20 hp))
        (rowE1 (⟨138, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨138, by decide⟩ : Fin 148) ⟨106, by decide⟩ _
      (validAt ⟨138, by decide⟩ (listedAt ⟨138, by decide⟩ hj))
      (colE1 ⟨106, by decide⟩ 20 (transLenTr ⟨106, by decide⟩ 20 hp)) T138_106
      hfix138_106 hinj138_106 hcardT138_106
      (fun i => conj_mem_of_fixedPoints _ _ (T138_106 i) (hfix138_106 i) _)
      ⟨138, by decide⟩ ⟨106, by decide⟩ _
      (Q2.validAt ⟨138, by decide⟩ (Q2.listedAt ⟨138, by decide⟩
        (alnCheck_rep ⟨138, by decide⟩ hj hq).1))
      (colE2 ⟨106, by decide⟩ 20 hp) Q2.T138_106_2 Q2.hfix138_106_2 Q2.hinj138_106_2
      Q2.hcardT138_106_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T138_106_2 i) (Q2.hfix138_106_2 i) _)
      colCert_138_106_20.hD ?_).symm
  rw [alnId_138 j hj]


theorem leaf_138_112_0 (hp : 0 < (Q2.transData.getD 112 []).length)
    (j : Nat) (hj : j < (repChars.getD 138 []).length)
    (hq : (normIsRep.getD 138 []).getD j false = true) :
    species (Q2.reps (⟨112, by decide⟩ : Fin 148)) (colE2 ⟨112, by decide⟩ 0 hp)
        (rowE2 (⟨138, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨112, by decide⟩ : Fin 148))
        (colE1 ⟨112, by decide⟩ 0 (transLenTr ⟨112, by decide⟩ 0 hp))
        (rowE1 (⟨138, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨138, by decide⟩ : Fin 148) ⟨112, by decide⟩ _
      (validAt ⟨138, by decide⟩ (listedAt ⟨138, by decide⟩ hj))
      (colE1 ⟨112, by decide⟩ 0 (transLenTr ⟨112, by decide⟩ 0 hp)) T138_112
      hfix138_112 hinj138_112 hcardT138_112
      (fun i => conj_mem_of_fixedPoints _ _ (T138_112 i) (hfix138_112 i) _)
      ⟨138, by decide⟩ ⟨112, by decide⟩ _
      (Q2.validAt ⟨138, by decide⟩ (Q2.listedAt ⟨138, by decide⟩
        (alnCheck_rep ⟨138, by decide⟩ hj hq).1))
      (colE2 ⟨112, by decide⟩ 0 hp) Q2.T138_112_2 Q2.hfix138_112_2 Q2.hinj138_112_2
      Q2.hcardT138_112_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T138_112_2 i) (Q2.hfix138_112_2 i) _)
      colCert_138_112_0.hD ?_).symm
  rw [alnId_138 j hj]


theorem leaf_138_112_1 (hp : 1 < (Q2.transData.getD 112 []).length)
    (j : Nat) (hj : j < (repChars.getD 138 []).length)
    (hq : (normIsRep.getD 138 []).getD j false = true) :
    species (Q2.reps (⟨112, by decide⟩ : Fin 148)) (colE2 ⟨112, by decide⟩ 1 hp)
        (rowE2 (⟨138, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨112, by decide⟩ : Fin 148))
        (colE1 ⟨112, by decide⟩ 1 (transLenTr ⟨112, by decide⟩ 1 hp))
        (rowE1 (⟨138, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨138, by decide⟩ : Fin 148) ⟨112, by decide⟩ _
      (validAt ⟨138, by decide⟩ (listedAt ⟨138, by decide⟩ hj))
      (colE1 ⟨112, by decide⟩ 1 (transLenTr ⟨112, by decide⟩ 1 hp)) T138_112
      hfix138_112 hinj138_112 hcardT138_112
      (fun i => conj_mem_of_fixedPoints _ _ (T138_112 i) (hfix138_112 i) _)
      ⟨138, by decide⟩ ⟨112, by decide⟩ _
      (Q2.validAt ⟨138, by decide⟩ (Q2.listedAt ⟨138, by decide⟩
        (alnCheck_rep ⟨138, by decide⟩ hj hq).1))
      (colE2 ⟨112, by decide⟩ 1 hp) Q2.T138_112_2 Q2.hfix138_112_2 Q2.hinj138_112_2
      Q2.hcardT138_112_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T138_112_2 i) (Q2.hfix138_112_2 i) _)
      colCert_138_112_1.hD ?_).symm
  rw [alnId_138 j hj]


theorem leaf_138_112_2 (hp : 2 < (Q2.transData.getD 112 []).length)
    (j : Nat) (hj : j < (repChars.getD 138 []).length)
    (hq : (normIsRep.getD 138 []).getD j false = true) :
    species (Q2.reps (⟨112, by decide⟩ : Fin 148)) (colE2 ⟨112, by decide⟩ 2 hp)
        (rowE2 (⟨138, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨112, by decide⟩ : Fin 148))
        (colE1 ⟨112, by decide⟩ 2 (transLenTr ⟨112, by decide⟩ 2 hp))
        (rowE1 (⟨138, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨138, by decide⟩ : Fin 148) ⟨112, by decide⟩ _
      (validAt ⟨138, by decide⟩ (listedAt ⟨138, by decide⟩ hj))
      (colE1 ⟨112, by decide⟩ 2 (transLenTr ⟨112, by decide⟩ 2 hp)) T138_112
      hfix138_112 hinj138_112 hcardT138_112
      (fun i => conj_mem_of_fixedPoints _ _ (T138_112 i) (hfix138_112 i) _)
      ⟨138, by decide⟩ ⟨112, by decide⟩ _
      (Q2.validAt ⟨138, by decide⟩ (Q2.listedAt ⟨138, by decide⟩
        (alnCheck_rep ⟨138, by decide⟩ hj hq).1))
      (colE2 ⟨112, by decide⟩ 2 hp) Q2.T138_112_2 Q2.hfix138_112_2 Q2.hinj138_112_2
      Q2.hcardT138_112_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T138_112_2 i) (Q2.hfix138_112_2 i) _)
      colCert_138_112_2.hD ?_).symm
  rw [alnId_138 j hj]


theorem leaf_138_112_3 (hp : 3 < (Q2.transData.getD 112 []).length)
    (j : Nat) (hj : j < (repChars.getD 138 []).length)
    (hq : (normIsRep.getD 138 []).getD j false = true) :
    species (Q2.reps (⟨112, by decide⟩ : Fin 148)) (colE2 ⟨112, by decide⟩ 3 hp)
        (rowE2 (⟨138, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨112, by decide⟩ : Fin 148))
        (colE1 ⟨112, by decide⟩ 3 (transLenTr ⟨112, by decide⟩ 3 hp))
        (rowE1 (⟨138, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨138, by decide⟩ : Fin 148) ⟨112, by decide⟩ _
      (validAt ⟨138, by decide⟩ (listedAt ⟨138, by decide⟩ hj))
      (colE1 ⟨112, by decide⟩ 3 (transLenTr ⟨112, by decide⟩ 3 hp)) T138_112
      hfix138_112 hinj138_112 hcardT138_112
      (fun i => conj_mem_of_fixedPoints _ _ (T138_112 i) (hfix138_112 i) _)
      ⟨138, by decide⟩ ⟨112, by decide⟩ _
      (Q2.validAt ⟨138, by decide⟩ (Q2.listedAt ⟨138, by decide⟩
        (alnCheck_rep ⟨138, by decide⟩ hj hq).1))
      (colE2 ⟨112, by decide⟩ 3 hp) Q2.T138_112_2 Q2.hfix138_112_2 Q2.hinj138_112_2
      Q2.hcardT138_112_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T138_112_2 i) (Q2.hfix138_112_2 i) _)
      colCert_138_112_3.hD ?_).symm
  rw [alnId_138 j hj]


end LeanDring.P5Presentation
