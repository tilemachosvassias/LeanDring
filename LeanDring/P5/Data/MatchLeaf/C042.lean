/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Data.ColCdd.C019
import LeanDring.P5.Data.ColCdd.C020
import LeanDring.P5.Data.ColRestCheap.C083
import LeanDring.P5.Data.ColRestCheap.C084
import LeanDring.P5.Data.ColRestCheap.C085
import LeanDring.P5.Data.ColRestCheap.C086
import LeanDring.P5.Data.EntryK.C038
import LeanDring.P5.Data.EntryK.C039
import LeanDring.P5.Certificate.RingIsomorphism.MatchCore
import LeanDring.P5.Data.SpeciesDiv.C027
import LeanDring.P5.Data.SpeciesDiv.C028
import LeanDring.P5.Data.SpeciesDiv.C029

/-! # Stage-5 leaves, chunk 41 (auto-emitted).  -/

namespace LeanDring.P5Presentation

open MulAction Finset LeanDring.DRing LeanDring.MonGSet

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.style.longLine false

theorem leaf_138_112_4 (hp : 4 < (Q2.transData.getD 112 []).length)
    (j : Nat) (hj : j < (repChars.getD 138 []).length)
    (hq : (normIsRep.getD 138 []).getD j false = true) :
    species (Q2.reps (⟨112, by decide⟩ : Fin 148)) (colE2 ⟨112, by decide⟩ 4 hp)
        (rowE2 (⟨138, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨112, by decide⟩ : Fin 148))
        (colE1 ⟨112, by decide⟩ 4 (transLenTr ⟨112, by decide⟩ 4 hp))
        (rowE1 (⟨138, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨138, by decide⟩ : Fin 148) ⟨112, by decide⟩ _
      (validAt ⟨138, by decide⟩ (listedAt ⟨138, by decide⟩ hj))
      (colE1 ⟨112, by decide⟩ 4 (transLenTr ⟨112, by decide⟩ 4 hp)) T138_112
      hfix138_112 hinj138_112 hcardT138_112
      (fun i => conj_mem_of_fixedPoints _ _ (T138_112 i) (hfix138_112 i) _)
      ⟨138, by decide⟩ ⟨112, by decide⟩ _
      (Q2.validAt ⟨138, by decide⟩ (Q2.listedAt ⟨138, by decide⟩
        (alnCheck_rep ⟨138, by decide⟩ hj hq).1))
      (colE2 ⟨112, by decide⟩ 4 hp) Q2.T138_112_2 Q2.hfix138_112_2 Q2.hinj138_112_2
      Q2.hcardT138_112_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T138_112_2 i) (Q2.hfix138_112_2 i) _)
      colCert_138_112_4.hD ?_).symm
  rw [alnId_138 j hj]


theorem leaf_138_112_5 (hp : 5 < (Q2.transData.getD 112 []).length)
    (j : Nat) (hj : j < (repChars.getD 138 []).length)
    (hq : (normIsRep.getD 138 []).getD j false = true) :
    species (Q2.reps (⟨112, by decide⟩ : Fin 148)) (colE2 ⟨112, by decide⟩ 5 hp)
        (rowE2 (⟨138, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨112, by decide⟩ : Fin 148))
        (colE1 ⟨112, by decide⟩ 5 (transLenTr ⟨112, by decide⟩ 5 hp))
        (rowE1 (⟨138, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨138, by decide⟩ : Fin 148) ⟨112, by decide⟩ _
      (validAt ⟨138, by decide⟩ (listedAt ⟨138, by decide⟩ hj))
      (colE1 ⟨112, by decide⟩ 5 (transLenTr ⟨112, by decide⟩ 5 hp)) T138_112
      hfix138_112 hinj138_112 hcardT138_112
      (fun i => conj_mem_of_fixedPoints _ _ (T138_112 i) (hfix138_112 i) _)
      ⟨138, by decide⟩ ⟨112, by decide⟩ _
      (Q2.validAt ⟨138, by decide⟩ (Q2.listedAt ⟨138, by decide⟩
        (alnCheck_rep ⟨138, by decide⟩ hj hq).1))
      (colE2 ⟨112, by decide⟩ 5 hp) Q2.T138_112_2 Q2.hfix138_112_2 Q2.hinj138_112_2
      Q2.hcardT138_112_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T138_112_2 i) (Q2.hfix138_112_2 i) _)
      colCert_138_112_5.hD ?_).symm
  rw [alnId_138 j hj]


theorem leaf_138_112_10 (hp : 10 < (Q2.transData.getD 112 []).length)
    (j : Nat) (hj : j < (repChars.getD 138 []).length)
    (hq : (normIsRep.getD 138 []).getD j false = true) :
    species (Q2.reps (⟨112, by decide⟩ : Fin 148)) (colE2 ⟨112, by decide⟩ 10 hp)
        (rowE2 (⟨138, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨112, by decide⟩ : Fin 148))
        (colE1 ⟨112, by decide⟩ 10 (transLenTr ⟨112, by decide⟩ 10 hp))
        (rowE1 (⟨138, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨138, by decide⟩ : Fin 148) ⟨112, by decide⟩ _
      (validAt ⟨138, by decide⟩ (listedAt ⟨138, by decide⟩ hj))
      (colE1 ⟨112, by decide⟩ 10 (transLenTr ⟨112, by decide⟩ 10 hp)) T138_112
      hfix138_112 hinj138_112 hcardT138_112
      (fun i => conj_mem_of_fixedPoints _ _ (T138_112 i) (hfix138_112 i) _)
      ⟨138, by decide⟩ ⟨112, by decide⟩ _
      (Q2.validAt ⟨138, by decide⟩ (Q2.listedAt ⟨138, by decide⟩
        (alnCheck_rep ⟨138, by decide⟩ hj hq).1))
      (colE2 ⟨112, by decide⟩ 10 hp) Q2.T138_112_2 Q2.hfix138_112_2 Q2.hinj138_112_2
      Q2.hcardT138_112_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T138_112_2 i) (Q2.hfix138_112_2 i) _)
      colCert_138_112_10.hD ?_).symm
  rw [alnId_138 j hj]


theorem leaf_138_112_15 (hp : 15 < (Q2.transData.getD 112 []).length)
    (j : Nat) (hj : j < (repChars.getD 138 []).length)
    (hq : (normIsRep.getD 138 []).getD j false = true) :
    species (Q2.reps (⟨112, by decide⟩ : Fin 148)) (colE2 ⟨112, by decide⟩ 15 hp)
        (rowE2 (⟨138, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨112, by decide⟩ : Fin 148))
        (colE1 ⟨112, by decide⟩ 15 (transLenTr ⟨112, by decide⟩ 15 hp))
        (rowE1 (⟨138, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨138, by decide⟩ : Fin 148) ⟨112, by decide⟩ _
      (validAt ⟨138, by decide⟩ (listedAt ⟨138, by decide⟩ hj))
      (colE1 ⟨112, by decide⟩ 15 (transLenTr ⟨112, by decide⟩ 15 hp)) T138_112
      hfix138_112 hinj138_112 hcardT138_112
      (fun i => conj_mem_of_fixedPoints _ _ (T138_112 i) (hfix138_112 i) _)
      ⟨138, by decide⟩ ⟨112, by decide⟩ _
      (Q2.validAt ⟨138, by decide⟩ (Q2.listedAt ⟨138, by decide⟩
        (alnCheck_rep ⟨138, by decide⟩ hj hq).1))
      (colE2 ⟨112, by decide⟩ 15 hp) Q2.T138_112_2 Q2.hfix138_112_2 Q2.hinj138_112_2
      Q2.hcardT138_112_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T138_112_2 i) (Q2.hfix138_112_2 i) _)
      ?_).symm
  rw [show colData1 (⟨138, by decide⟩ : Fin 148)
        ((colE1 ⟨112, by decide⟩ 15 (transLenTr ⟨112, by decide⟩ 15 hp) : ↥(reps ⟨112, by decide⟩)) : Coordinate 1)
        T138_112 = colFn colCertDiv_138_112_15.D1 (m := 5) from colCertDiv_138_112_15.bind1,
    show colData2 (⟨138, by decide⟩ : Fin 148)
        ((colE2 ⟨112, by decide⟩ 15 hp : ↥(Q2.reps ⟨112, by decide⟩)) : Coordinate 2)
        Q2.T138_112_2 = colFn colCertDiv_138_112_15.D2 (m := 5) from colCertDiv_138_112_15.bind2]
  rw [alnId_138 j hj]
  exact fastcode_of_div ⟨138, by decide⟩ _ _ _
    ((alnId_138 j hj) ▸ Q2.listedAt (⟨138, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨138, by decide⟩ : Fin 148) hj hq).1) colCertDiv_138_112_15_match


theorem leaf_138_112_20 (hp : 20 < (Q2.transData.getD 112 []).length)
    (j : Nat) (hj : j < (repChars.getD 138 []).length)
    (hq : (normIsRep.getD 138 []).getD j false = true) :
    species (Q2.reps (⟨112, by decide⟩ : Fin 148)) (colE2 ⟨112, by decide⟩ 20 hp)
        (rowE2 (⟨138, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨112, by decide⟩ : Fin 148))
        (colE1 ⟨112, by decide⟩ 20 (transLenTr ⟨112, by decide⟩ 20 hp))
        (rowE1 (⟨138, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨138, by decide⟩ : Fin 148) ⟨112, by decide⟩ _
      (validAt ⟨138, by decide⟩ (listedAt ⟨138, by decide⟩ hj))
      (colE1 ⟨112, by decide⟩ 20 (transLenTr ⟨112, by decide⟩ 20 hp)) T138_112
      hfix138_112 hinj138_112 hcardT138_112
      (fun i => conj_mem_of_fixedPoints _ _ (T138_112 i) (hfix138_112 i) _)
      ⟨138, by decide⟩ ⟨112, by decide⟩ _
      (Q2.validAt ⟨138, by decide⟩ (Q2.listedAt ⟨138, by decide⟩
        (alnCheck_rep ⟨138, by decide⟩ hj hq).1))
      (colE2 ⟨112, by decide⟩ 20 hp) Q2.T138_112_2 Q2.hfix138_112_2 Q2.hinj138_112_2
      Q2.hcardT138_112_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T138_112_2 i) (Q2.hfix138_112_2 i) _)
      ?_).symm
  rw [show colData1 (⟨138, by decide⟩ : Fin 148)
        ((colE1 ⟨112, by decide⟩ 20 (transLenTr ⟨112, by decide⟩ 20 hp) : ↥(reps ⟨112, by decide⟩)) : Coordinate 1)
        T138_112 = colFn colCertDiv_138_112_20.D1 (m := 5) from colCertDiv_138_112_20.bind1,
    show colData2 (⟨138, by decide⟩ : Fin 148)
        ((colE2 ⟨112, by decide⟩ 20 hp : ↥(Q2.reps ⟨112, by decide⟩)) : Coordinate 2)
        Q2.T138_112_2 = colFn colCertDiv_138_112_20.D2 (m := 5) from colCertDiv_138_112_20.bind2]
  rw [alnId_138 j hj]
  exact fastcode_of_div ⟨138, by decide⟩ _ _ _
    ((alnId_138 j hj) ▸ Q2.listedAt (⟨138, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨138, by decide⟩ : Fin 148) hj hq).1) colCertDiv_138_112_20_match


theorem leaf_138_138_0 (hp : 0 < (Q2.transData.getD 138 []).length)
    (j : Nat) (hj : j < (repChars.getD 138 []).length)
    (hq : (normIsRep.getD 138 []).getD j false = true) :
    species (Q2.reps (⟨138, by decide⟩ : Fin 148)) (colE2 ⟨138, by decide⟩ 0 hp)
        (rowE2 (⟨138, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨138, by decide⟩ : Fin 148))
        (colE1 ⟨138, by decide⟩ 0 (transLenTr ⟨138, by decide⟩ 0 hp))
        (rowE1 (⟨138, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨138, by decide⟩ : Fin 148) ⟨138, by decide⟩ _
      (validAt ⟨138, by decide⟩ (listedAt ⟨138, by decide⟩ hj))
      (colE1 ⟨138, by decide⟩ 0 (transLenTr ⟨138, by decide⟩ 0 hp)) T138_138
      hfix138_138 hinj138_138 hcardT138_138
      (fun i => conj_mem_of_fixedPoints _ _ (T138_138 i) (hfix138_138 i) _)
      ⟨138, by decide⟩ ⟨138, by decide⟩ _
      (Q2.validAt ⟨138, by decide⟩ (Q2.listedAt ⟨138, by decide⟩
        (alnCheck_rep ⟨138, by decide⟩ hj hq).1))
      (colE2 ⟨138, by decide⟩ 0 hp) Q2.T138_138_2 Q2.hfix138_138_2 Q2.hinj138_138_2
      Q2.hcardT138_138_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T138_138_2 i) (Q2.hfix138_138_2 i) _)
      colCert_138_138_0.hD ?_).symm
  rw [alnId_138 j hj]


theorem leaf_138_138_1 (hp : 1 < (Q2.transData.getD 138 []).length)
    (j : Nat) (hj : j < (repChars.getD 138 []).length)
    (hq : (normIsRep.getD 138 []).getD j false = true) :
    species (Q2.reps (⟨138, by decide⟩ : Fin 148)) (colE2 ⟨138, by decide⟩ 1 hp)
        (rowE2 (⟨138, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨138, by decide⟩ : Fin 148))
        (colE1 ⟨138, by decide⟩ 1 (transLenTr ⟨138, by decide⟩ 1 hp))
        (rowE1 (⟨138, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨138, by decide⟩ : Fin 148) ⟨138, by decide⟩ _
      (validAt ⟨138, by decide⟩ (listedAt ⟨138, by decide⟩ hj))
      (colE1 ⟨138, by decide⟩ 1 (transLenTr ⟨138, by decide⟩ 1 hp)) T138_138
      hfix138_138 hinj138_138 hcardT138_138
      (fun i => conj_mem_of_fixedPoints _ _ (T138_138 i) (hfix138_138 i) _)
      ⟨138, by decide⟩ ⟨138, by decide⟩ _
      (Q2.validAt ⟨138, by decide⟩ (Q2.listedAt ⟨138, by decide⟩
        (alnCheck_rep ⟨138, by decide⟩ hj hq).1))
      (colE2 ⟨138, by decide⟩ 1 hp) Q2.T138_138_2 Q2.hfix138_138_2 Q2.hinj138_138_2
      Q2.hcardT138_138_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T138_138_2 i) (Q2.hfix138_138_2 i) _)
      colCert_138_138_1.hD ?_).symm
  rw [alnId_138 j hj]


theorem leaf_138_138_2 (hp : 2 < (Q2.transData.getD 138 []).length)
    (j : Nat) (hj : j < (repChars.getD 138 []).length)
    (hq : (normIsRep.getD 138 []).getD j false = true) :
    species (Q2.reps (⟨138, by decide⟩ : Fin 148)) (colE2 ⟨138, by decide⟩ 2 hp)
        (rowE2 (⟨138, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨138, by decide⟩ : Fin 148))
        (colE1 ⟨138, by decide⟩ 2 (transLenTr ⟨138, by decide⟩ 2 hp))
        (rowE1 (⟨138, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨138, by decide⟩ : Fin 148) ⟨138, by decide⟩ _
      (validAt ⟨138, by decide⟩ (listedAt ⟨138, by decide⟩ hj))
      (colE1 ⟨138, by decide⟩ 2 (transLenTr ⟨138, by decide⟩ 2 hp)) T138_138
      hfix138_138 hinj138_138 hcardT138_138
      (fun i => conj_mem_of_fixedPoints _ _ (T138_138 i) (hfix138_138 i) _)
      ⟨138, by decide⟩ ⟨138, by decide⟩ _
      (Q2.validAt ⟨138, by decide⟩ (Q2.listedAt ⟨138, by decide⟩
        (alnCheck_rep ⟨138, by decide⟩ hj hq).1))
      (colE2 ⟨138, by decide⟩ 2 hp) Q2.T138_138_2 Q2.hfix138_138_2 Q2.hinj138_138_2
      Q2.hcardT138_138_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T138_138_2 i) (Q2.hfix138_138_2 i) _)
      colCert_138_138_2.hD ?_).symm
  rw [alnId_138 j hj]


theorem leaf_138_138_3 (hp : 3 < (Q2.transData.getD 138 []).length)
    (j : Nat) (hj : j < (repChars.getD 138 []).length)
    (hq : (normIsRep.getD 138 []).getD j false = true) :
    species (Q2.reps (⟨138, by decide⟩ : Fin 148)) (colE2 ⟨138, by decide⟩ 3 hp)
        (rowE2 (⟨138, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨138, by decide⟩ : Fin 148))
        (colE1 ⟨138, by decide⟩ 3 (transLenTr ⟨138, by decide⟩ 3 hp))
        (rowE1 (⟨138, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨138, by decide⟩ : Fin 148) ⟨138, by decide⟩ _
      (validAt ⟨138, by decide⟩ (listedAt ⟨138, by decide⟩ hj))
      (colE1 ⟨138, by decide⟩ 3 (transLenTr ⟨138, by decide⟩ 3 hp)) T138_138
      hfix138_138 hinj138_138 hcardT138_138
      (fun i => conj_mem_of_fixedPoints _ _ (T138_138 i) (hfix138_138 i) _)
      ⟨138, by decide⟩ ⟨138, by decide⟩ _
      (Q2.validAt ⟨138, by decide⟩ (Q2.listedAt ⟨138, by decide⟩
        (alnCheck_rep ⟨138, by decide⟩ hj hq).1))
      (colE2 ⟨138, by decide⟩ 3 hp) Q2.T138_138_2 Q2.hfix138_138_2 Q2.hinj138_138_2
      Q2.hcardT138_138_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T138_138_2 i) (Q2.hfix138_138_2 i) _)
      colCert_138_138_3.hD ?_).symm
  rw [alnId_138 j hj]


theorem leaf_138_138_4 (hp : 4 < (Q2.transData.getD 138 []).length)
    (j : Nat) (hj : j < (repChars.getD 138 []).length)
    (hq : (normIsRep.getD 138 []).getD j false = true) :
    species (Q2.reps (⟨138, by decide⟩ : Fin 148)) (colE2 ⟨138, by decide⟩ 4 hp)
        (rowE2 (⟨138, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨138, by decide⟩ : Fin 148))
        (colE1 ⟨138, by decide⟩ 4 (transLenTr ⟨138, by decide⟩ 4 hp))
        (rowE1 (⟨138, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨138, by decide⟩ : Fin 148) ⟨138, by decide⟩ _
      (validAt ⟨138, by decide⟩ (listedAt ⟨138, by decide⟩ hj))
      (colE1 ⟨138, by decide⟩ 4 (transLenTr ⟨138, by decide⟩ 4 hp)) T138_138
      hfix138_138 hinj138_138 hcardT138_138
      (fun i => conj_mem_of_fixedPoints _ _ (T138_138 i) (hfix138_138 i) _)
      ⟨138, by decide⟩ ⟨138, by decide⟩ _
      (Q2.validAt ⟨138, by decide⟩ (Q2.listedAt ⟨138, by decide⟩
        (alnCheck_rep ⟨138, by decide⟩ hj hq).1))
      (colE2 ⟨138, by decide⟩ 4 hp) Q2.T138_138_2 Q2.hfix138_138_2 Q2.hinj138_138_2
      Q2.hcardT138_138_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T138_138_2 i) (Q2.hfix138_138_2 i) _)
      colCert_138_138_4.hD ?_).symm
  rw [alnId_138 j hj]


theorem leaf_138_138_5 (hp : 5 < (Q2.transData.getD 138 []).length)
    (j : Nat) (hj : j < (repChars.getD 138 []).length)
    (hq : (normIsRep.getD 138 []).getD j false = true) :
    species (Q2.reps (⟨138, by decide⟩ : Fin 148)) (colE2 ⟨138, by decide⟩ 5 hp)
        (rowE2 (⟨138, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨138, by decide⟩ : Fin 148))
        (colE1 ⟨138, by decide⟩ 5 (transLenTr ⟨138, by decide⟩ 5 hp))
        (rowE1 (⟨138, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨138, by decide⟩ : Fin 148) ⟨138, by decide⟩ _
      (validAt ⟨138, by decide⟩ (listedAt ⟨138, by decide⟩ hj))
      (colE1 ⟨138, by decide⟩ 5 (transLenTr ⟨138, by decide⟩ 5 hp)) T138_138
      hfix138_138 hinj138_138 hcardT138_138
      (fun i => conj_mem_of_fixedPoints _ _ (T138_138 i) (hfix138_138 i) _)
      ⟨138, by decide⟩ ⟨138, by decide⟩ _
      (Q2.validAt ⟨138, by decide⟩ (Q2.listedAt ⟨138, by decide⟩
        (alnCheck_rep ⟨138, by decide⟩ hj hq).1))
      (colE2 ⟨138, by decide⟩ 5 hp) Q2.T138_138_2 Q2.hfix138_138_2 Q2.hinj138_138_2
      Q2.hcardT138_138_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T138_138_2 i) (Q2.hfix138_138_2 i) _)
      colCert_138_138_5.hD ?_).symm
  rw [alnId_138 j hj]


theorem leaf_138_138_6 (hp : 6 < (Q2.transData.getD 138 []).length)
    (j : Nat) (hj : j < (repChars.getD 138 []).length)
    (hq : (normIsRep.getD 138 []).getD j false = true) :
    species (Q2.reps (⟨138, by decide⟩ : Fin 148)) (colE2 ⟨138, by decide⟩ 6 hp)
        (rowE2 (⟨138, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨138, by decide⟩ : Fin 148))
        (colE1 ⟨138, by decide⟩ 6 (transLenTr ⟨138, by decide⟩ 6 hp))
        (rowE1 (⟨138, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨138, by decide⟩ : Fin 148) ⟨138, by decide⟩ _
      (validAt ⟨138, by decide⟩ (listedAt ⟨138, by decide⟩ hj))
      (colE1 ⟨138, by decide⟩ 6 (transLenTr ⟨138, by decide⟩ 6 hp)) T138_138
      hfix138_138 hinj138_138 hcardT138_138
      (fun i => conj_mem_of_fixedPoints _ _ (T138_138 i) (hfix138_138 i) _)
      ⟨138, by decide⟩ ⟨138, by decide⟩ _
      (Q2.validAt ⟨138, by decide⟩ (Q2.listedAt ⟨138, by decide⟩
        (alnCheck_rep ⟨138, by decide⟩ hj hq).1))
      (colE2 ⟨138, by decide⟩ 6 hp) Q2.T138_138_2 Q2.hfix138_138_2 Q2.hinj138_138_2
      Q2.hcardT138_138_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T138_138_2 i) (Q2.hfix138_138_2 i) _)
      colCert_138_138_6.hD ?_).symm
  rw [alnId_138 j hj]


theorem leaf_138_138_7 (hp : 7 < (Q2.transData.getD 138 []).length)
    (j : Nat) (hj : j < (repChars.getD 138 []).length)
    (hq : (normIsRep.getD 138 []).getD j false = true) :
    species (Q2.reps (⟨138, by decide⟩ : Fin 148)) (colE2 ⟨138, by decide⟩ 7 hp)
        (rowE2 (⟨138, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨138, by decide⟩ : Fin 148))
        (colE1 ⟨138, by decide⟩ 7 (transLenTr ⟨138, by decide⟩ 7 hp))
        (rowE1 (⟨138, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨138, by decide⟩ : Fin 148) ⟨138, by decide⟩ _
      (validAt ⟨138, by decide⟩ (listedAt ⟨138, by decide⟩ hj))
      (colE1 ⟨138, by decide⟩ 7 (transLenTr ⟨138, by decide⟩ 7 hp)) T138_138
      hfix138_138 hinj138_138 hcardT138_138
      (fun i => conj_mem_of_fixedPoints _ _ (T138_138 i) (hfix138_138 i) _)
      ⟨138, by decide⟩ ⟨138, by decide⟩ _
      (Q2.validAt ⟨138, by decide⟩ (Q2.listedAt ⟨138, by decide⟩
        (alnCheck_rep ⟨138, by decide⟩ hj hq).1))
      (colE2 ⟨138, by decide⟩ 7 hp) Q2.T138_138_2 Q2.hfix138_138_2 Q2.hinj138_138_2
      Q2.hcardT138_138_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T138_138_2 i) (Q2.hfix138_138_2 i) _)
      colCert_138_138_7.hD ?_).symm
  rw [alnId_138 j hj]


theorem leaf_138_138_8 (hp : 8 < (Q2.transData.getD 138 []).length)
    (j : Nat) (hj : j < (repChars.getD 138 []).length)
    (hq : (normIsRep.getD 138 []).getD j false = true) :
    species (Q2.reps (⟨138, by decide⟩ : Fin 148)) (colE2 ⟨138, by decide⟩ 8 hp)
        (rowE2 (⟨138, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨138, by decide⟩ : Fin 148))
        (colE1 ⟨138, by decide⟩ 8 (transLenTr ⟨138, by decide⟩ 8 hp))
        (rowE1 (⟨138, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨138, by decide⟩ : Fin 148) ⟨138, by decide⟩ _
      (validAt ⟨138, by decide⟩ (listedAt ⟨138, by decide⟩ hj))
      (colE1 ⟨138, by decide⟩ 8 (transLenTr ⟨138, by decide⟩ 8 hp)) T138_138
      hfix138_138 hinj138_138 hcardT138_138
      (fun i => conj_mem_of_fixedPoints _ _ (T138_138 i) (hfix138_138 i) _)
      ⟨138, by decide⟩ ⟨138, by decide⟩ _
      (Q2.validAt ⟨138, by decide⟩ (Q2.listedAt ⟨138, by decide⟩
        (alnCheck_rep ⟨138, by decide⟩ hj hq).1))
      (colE2 ⟨138, by decide⟩ 8 hp) Q2.T138_138_2 Q2.hfix138_138_2 Q2.hinj138_138_2
      Q2.hcardT138_138_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T138_138_2 i) (Q2.hfix138_138_2 i) _)
      colCert_138_138_8.hD ?_).symm
  rw [alnId_138 j hj]


theorem leaf_138_138_9 (hp : 9 < (Q2.transData.getD 138 []).length)
    (j : Nat) (hj : j < (repChars.getD 138 []).length)
    (hq : (normIsRep.getD 138 []).getD j false = true) :
    species (Q2.reps (⟨138, by decide⟩ : Fin 148)) (colE2 ⟨138, by decide⟩ 9 hp)
        (rowE2 (⟨138, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨138, by decide⟩ : Fin 148))
        (colE1 ⟨138, by decide⟩ 9 (transLenTr ⟨138, by decide⟩ 9 hp))
        (rowE1 (⟨138, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨138, by decide⟩ : Fin 148) ⟨138, by decide⟩ _
      (validAt ⟨138, by decide⟩ (listedAt ⟨138, by decide⟩ hj))
      (colE1 ⟨138, by decide⟩ 9 (transLenTr ⟨138, by decide⟩ 9 hp)) T138_138
      hfix138_138 hinj138_138 hcardT138_138
      (fun i => conj_mem_of_fixedPoints _ _ (T138_138 i) (hfix138_138 i) _)
      ⟨138, by decide⟩ ⟨138, by decide⟩ _
      (Q2.validAt ⟨138, by decide⟩ (Q2.listedAt ⟨138, by decide⟩
        (alnCheck_rep ⟨138, by decide⟩ hj hq).1))
      (colE2 ⟨138, by decide⟩ 9 hp) Q2.T138_138_2 Q2.hfix138_138_2 Q2.hinj138_138_2
      Q2.hcardT138_138_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T138_138_2 i) (Q2.hfix138_138_2 i) _)
      colCert_138_138_9.hD ?_).symm
  rw [alnId_138 j hj]


theorem leaf_138_138_10 (hp : 10 < (Q2.transData.getD 138 []).length)
    (j : Nat) (hj : j < (repChars.getD 138 []).length)
    (hq : (normIsRep.getD 138 []).getD j false = true) :
    species (Q2.reps (⟨138, by decide⟩ : Fin 148)) (colE2 ⟨138, by decide⟩ 10 hp)
        (rowE2 (⟨138, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨138, by decide⟩ : Fin 148))
        (colE1 ⟨138, by decide⟩ 10 (transLenTr ⟨138, by decide⟩ 10 hp))
        (rowE1 (⟨138, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨138, by decide⟩ : Fin 148) ⟨138, by decide⟩ _
      (validAt ⟨138, by decide⟩ (listedAt ⟨138, by decide⟩ hj))
      (colE1 ⟨138, by decide⟩ 10 (transLenTr ⟨138, by decide⟩ 10 hp)) T138_138
      hfix138_138 hinj138_138 hcardT138_138
      (fun i => conj_mem_of_fixedPoints _ _ (T138_138 i) (hfix138_138 i) _)
      ⟨138, by decide⟩ ⟨138, by decide⟩ _
      (Q2.validAt ⟨138, by decide⟩ (Q2.listedAt ⟨138, by decide⟩
        (alnCheck_rep ⟨138, by decide⟩ hj hq).1))
      (colE2 ⟨138, by decide⟩ 10 hp) Q2.T138_138_2 Q2.hfix138_138_2 Q2.hinj138_138_2
      Q2.hcardT138_138_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T138_138_2 i) (Q2.hfix138_138_2 i) _)
      colCert_138_138_10.hD ?_).symm
  rw [alnId_138 j hj]


theorem leaf_138_138_11 (hp : 11 < (Q2.transData.getD 138 []).length)
    (j : Nat) (hj : j < (repChars.getD 138 []).length)
    (hq : (normIsRep.getD 138 []).getD j false = true) :
    species (Q2.reps (⟨138, by decide⟩ : Fin 148)) (colE2 ⟨138, by decide⟩ 11 hp)
        (rowE2 (⟨138, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨138, by decide⟩ : Fin 148))
        (colE1 ⟨138, by decide⟩ 11 (transLenTr ⟨138, by decide⟩ 11 hp))
        (rowE1 (⟨138, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨138, by decide⟩ : Fin 148) ⟨138, by decide⟩ _
      (validAt ⟨138, by decide⟩ (listedAt ⟨138, by decide⟩ hj))
      (colE1 ⟨138, by decide⟩ 11 (transLenTr ⟨138, by decide⟩ 11 hp)) T138_138
      hfix138_138 hinj138_138 hcardT138_138
      (fun i => conj_mem_of_fixedPoints _ _ (T138_138 i) (hfix138_138 i) _)
      ⟨138, by decide⟩ ⟨138, by decide⟩ _
      (Q2.validAt ⟨138, by decide⟩ (Q2.listedAt ⟨138, by decide⟩
        (alnCheck_rep ⟨138, by decide⟩ hj hq).1))
      (colE2 ⟨138, by decide⟩ 11 hp) Q2.T138_138_2 Q2.hfix138_138_2 Q2.hinj138_138_2
      Q2.hcardT138_138_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T138_138_2 i) (Q2.hfix138_138_2 i) _)
      colCert_138_138_11.hD ?_).symm
  rw [alnId_138 j hj]


theorem leaf_138_138_12 (hp : 12 < (Q2.transData.getD 138 []).length)
    (j : Nat) (hj : j < (repChars.getD 138 []).length)
    (hq : (normIsRep.getD 138 []).getD j false = true) :
    species (Q2.reps (⟨138, by decide⟩ : Fin 148)) (colE2 ⟨138, by decide⟩ 12 hp)
        (rowE2 (⟨138, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨138, by decide⟩ : Fin 148))
        (colE1 ⟨138, by decide⟩ 12 (transLenTr ⟨138, by decide⟩ 12 hp))
        (rowE1 (⟨138, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨138, by decide⟩ : Fin 148) ⟨138, by decide⟩ _
      (validAt ⟨138, by decide⟩ (listedAt ⟨138, by decide⟩ hj))
      (colE1 ⟨138, by decide⟩ 12 (transLenTr ⟨138, by decide⟩ 12 hp)) T138_138
      hfix138_138 hinj138_138 hcardT138_138
      (fun i => conj_mem_of_fixedPoints _ _ (T138_138 i) (hfix138_138 i) _)
      ⟨138, by decide⟩ ⟨138, by decide⟩ _
      (Q2.validAt ⟨138, by decide⟩ (Q2.listedAt ⟨138, by decide⟩
        (alnCheck_rep ⟨138, by decide⟩ hj hq).1))
      (colE2 ⟨138, by decide⟩ 12 hp) Q2.T138_138_2 Q2.hfix138_138_2 Q2.hinj138_138_2
      Q2.hcardT138_138_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T138_138_2 i) (Q2.hfix138_138_2 i) _)
      colCert_138_138_12.hD ?_).symm
  rw [alnId_138 j hj]


theorem leaf_138_138_13 (hp : 13 < (Q2.transData.getD 138 []).length)
    (j : Nat) (hj : j < (repChars.getD 138 []).length)
    (hq : (normIsRep.getD 138 []).getD j false = true) :
    species (Q2.reps (⟨138, by decide⟩ : Fin 148)) (colE2 ⟨138, by decide⟩ 13 hp)
        (rowE2 (⟨138, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨138, by decide⟩ : Fin 148))
        (colE1 ⟨138, by decide⟩ 13 (transLenTr ⟨138, by decide⟩ 13 hp))
        (rowE1 (⟨138, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨138, by decide⟩ : Fin 148) ⟨138, by decide⟩ _
      (validAt ⟨138, by decide⟩ (listedAt ⟨138, by decide⟩ hj))
      (colE1 ⟨138, by decide⟩ 13 (transLenTr ⟨138, by decide⟩ 13 hp)) T138_138
      hfix138_138 hinj138_138 hcardT138_138
      (fun i => conj_mem_of_fixedPoints _ _ (T138_138 i) (hfix138_138 i) _)
      ⟨138, by decide⟩ ⟨138, by decide⟩ _
      (Q2.validAt ⟨138, by decide⟩ (Q2.listedAt ⟨138, by decide⟩
        (alnCheck_rep ⟨138, by decide⟩ hj hq).1))
      (colE2 ⟨138, by decide⟩ 13 hp) Q2.T138_138_2 Q2.hfix138_138_2 Q2.hinj138_138_2
      Q2.hcardT138_138_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T138_138_2 i) (Q2.hfix138_138_2 i) _)
      colCert_138_138_13.hD ?_).symm
  rw [alnId_138 j hj]


theorem leaf_138_138_14 (hp : 14 < (Q2.transData.getD 138 []).length)
    (j : Nat) (hj : j < (repChars.getD 138 []).length)
    (hq : (normIsRep.getD 138 []).getD j false = true) :
    species (Q2.reps (⟨138, by decide⟩ : Fin 148)) (colE2 ⟨138, by decide⟩ 14 hp)
        (rowE2 (⟨138, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨138, by decide⟩ : Fin 148))
        (colE1 ⟨138, by decide⟩ 14 (transLenTr ⟨138, by decide⟩ 14 hp))
        (rowE1 (⟨138, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨138, by decide⟩ : Fin 148) ⟨138, by decide⟩ _
      (validAt ⟨138, by decide⟩ (listedAt ⟨138, by decide⟩ hj))
      (colE1 ⟨138, by decide⟩ 14 (transLenTr ⟨138, by decide⟩ 14 hp)) T138_138
      hfix138_138 hinj138_138 hcardT138_138
      (fun i => conj_mem_of_fixedPoints _ _ (T138_138 i) (hfix138_138 i) _)
      ⟨138, by decide⟩ ⟨138, by decide⟩ _
      (Q2.validAt ⟨138, by decide⟩ (Q2.listedAt ⟨138, by decide⟩
        (alnCheck_rep ⟨138, by decide⟩ hj hq).1))
      (colE2 ⟨138, by decide⟩ 14 hp) Q2.T138_138_2 Q2.hfix138_138_2 Q2.hinj138_138_2
      Q2.hcardT138_138_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T138_138_2 i) (Q2.hfix138_138_2 i) _)
      colCert_138_138_14.hD ?_).symm
  rw [alnId_138 j hj]


theorem leaf_138_138_15 (hp : 15 < (Q2.transData.getD 138 []).length)
    (j : Nat) (hj : j < (repChars.getD 138 []).length)
    (hq : (normIsRep.getD 138 []).getD j false = true) :
    species (Q2.reps (⟨138, by decide⟩ : Fin 148)) (colE2 ⟨138, by decide⟩ 15 hp)
        (rowE2 (⟨138, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨138, by decide⟩ : Fin 148))
        (colE1 ⟨138, by decide⟩ 15 (transLenTr ⟨138, by decide⟩ 15 hp))
        (rowE1 (⟨138, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨138, by decide⟩ : Fin 148) ⟨138, by decide⟩ _
      (validAt ⟨138, by decide⟩ (listedAt ⟨138, by decide⟩ hj))
      (colE1 ⟨138, by decide⟩ 15 (transLenTr ⟨138, by decide⟩ 15 hp)) T138_138
      hfix138_138 hinj138_138 hcardT138_138
      (fun i => conj_mem_of_fixedPoints _ _ (T138_138 i) (hfix138_138 i) _)
      ⟨138, by decide⟩ ⟨138, by decide⟩ _
      (Q2.validAt ⟨138, by decide⟩ (Q2.listedAt ⟨138, by decide⟩
        (alnCheck_rep ⟨138, by decide⟩ hj hq).1))
      (colE2 ⟨138, by decide⟩ 15 hp) Q2.T138_138_2 Q2.hfix138_138_2 Q2.hinj138_138_2
      Q2.hcardT138_138_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T138_138_2 i) (Q2.hfix138_138_2 i) _)
      colCert_138_138_15.hD ?_).symm
  rw [alnId_138 j hj]


theorem leaf_138_138_16 (hp : 16 < (Q2.transData.getD 138 []).length)
    (j : Nat) (hj : j < (repChars.getD 138 []).length)
    (hq : (normIsRep.getD 138 []).getD j false = true) :
    species (Q2.reps (⟨138, by decide⟩ : Fin 148)) (colE2 ⟨138, by decide⟩ 16 hp)
        (rowE2 (⟨138, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨138, by decide⟩ : Fin 148))
        (colE1 ⟨138, by decide⟩ 16 (transLenTr ⟨138, by decide⟩ 16 hp))
        (rowE1 (⟨138, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨138, by decide⟩ : Fin 148) ⟨138, by decide⟩ _
      (validAt ⟨138, by decide⟩ (listedAt ⟨138, by decide⟩ hj))
      (colE1 ⟨138, by decide⟩ 16 (transLenTr ⟨138, by decide⟩ 16 hp)) T138_138
      hfix138_138 hinj138_138 hcardT138_138
      (fun i => conj_mem_of_fixedPoints _ _ (T138_138 i) (hfix138_138 i) _)
      ⟨138, by decide⟩ ⟨138, by decide⟩ _
      (Q2.validAt ⟨138, by decide⟩ (Q2.listedAt ⟨138, by decide⟩
        (alnCheck_rep ⟨138, by decide⟩ hj hq).1))
      (colE2 ⟨138, by decide⟩ 16 hp) Q2.T138_138_2 Q2.hfix138_138_2 Q2.hinj138_138_2
      Q2.hcardT138_138_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T138_138_2 i) (Q2.hfix138_138_2 i) _)
      colCert_138_138_16.hD ?_).symm
  rw [alnId_138 j hj]


theorem leaf_138_138_17 (hp : 17 < (Q2.transData.getD 138 []).length)
    (j : Nat) (hj : j < (repChars.getD 138 []).length)
    (hq : (normIsRep.getD 138 []).getD j false = true) :
    species (Q2.reps (⟨138, by decide⟩ : Fin 148)) (colE2 ⟨138, by decide⟩ 17 hp)
        (rowE2 (⟨138, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨138, by decide⟩ : Fin 148))
        (colE1 ⟨138, by decide⟩ 17 (transLenTr ⟨138, by decide⟩ 17 hp))
        (rowE1 (⟨138, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨138, by decide⟩ : Fin 148) ⟨138, by decide⟩ _
      (validAt ⟨138, by decide⟩ (listedAt ⟨138, by decide⟩ hj))
      (colE1 ⟨138, by decide⟩ 17 (transLenTr ⟨138, by decide⟩ 17 hp)) T138_138
      hfix138_138 hinj138_138 hcardT138_138
      (fun i => conj_mem_of_fixedPoints _ _ (T138_138 i) (hfix138_138 i) _)
      ⟨138, by decide⟩ ⟨138, by decide⟩ _
      (Q2.validAt ⟨138, by decide⟩ (Q2.listedAt ⟨138, by decide⟩
        (alnCheck_rep ⟨138, by decide⟩ hj hq).1))
      (colE2 ⟨138, by decide⟩ 17 hp) Q2.T138_138_2 Q2.hfix138_138_2 Q2.hinj138_138_2
      Q2.hcardT138_138_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T138_138_2 i) (Q2.hfix138_138_2 i) _)
      colCert_138_138_17.hD ?_).symm
  rw [alnId_138 j hj]


theorem leaf_138_138_18 (hp : 18 < (Q2.transData.getD 138 []).length)
    (j : Nat) (hj : j < (repChars.getD 138 []).length)
    (hq : (normIsRep.getD 138 []).getD j false = true) :
    species (Q2.reps (⟨138, by decide⟩ : Fin 148)) (colE2 ⟨138, by decide⟩ 18 hp)
        (rowE2 (⟨138, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨138, by decide⟩ : Fin 148))
        (colE1 ⟨138, by decide⟩ 18 (transLenTr ⟨138, by decide⟩ 18 hp))
        (rowE1 (⟨138, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨138, by decide⟩ : Fin 148) ⟨138, by decide⟩ _
      (validAt ⟨138, by decide⟩ (listedAt ⟨138, by decide⟩ hj))
      (colE1 ⟨138, by decide⟩ 18 (transLenTr ⟨138, by decide⟩ 18 hp)) T138_138
      hfix138_138 hinj138_138 hcardT138_138
      (fun i => conj_mem_of_fixedPoints _ _ (T138_138 i) (hfix138_138 i) _)
      ⟨138, by decide⟩ ⟨138, by decide⟩ _
      (Q2.validAt ⟨138, by decide⟩ (Q2.listedAt ⟨138, by decide⟩
        (alnCheck_rep ⟨138, by decide⟩ hj hq).1))
      (colE2 ⟨138, by decide⟩ 18 hp) Q2.T138_138_2 Q2.hfix138_138_2 Q2.hinj138_138_2
      Q2.hcardT138_138_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T138_138_2 i) (Q2.hfix138_138_2 i) _)
      colCert_138_138_18.hD ?_).symm
  rw [alnId_138 j hj]


theorem leaf_138_138_19 (hp : 19 < (Q2.transData.getD 138 []).length)
    (j : Nat) (hj : j < (repChars.getD 138 []).length)
    (hq : (normIsRep.getD 138 []).getD j false = true) :
    species (Q2.reps (⟨138, by decide⟩ : Fin 148)) (colE2 ⟨138, by decide⟩ 19 hp)
        (rowE2 (⟨138, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨138, by decide⟩ : Fin 148))
        (colE1 ⟨138, by decide⟩ 19 (transLenTr ⟨138, by decide⟩ 19 hp))
        (rowE1 (⟨138, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨138, by decide⟩ : Fin 148) ⟨138, by decide⟩ _
      (validAt ⟨138, by decide⟩ (listedAt ⟨138, by decide⟩ hj))
      (colE1 ⟨138, by decide⟩ 19 (transLenTr ⟨138, by decide⟩ 19 hp)) T138_138
      hfix138_138 hinj138_138 hcardT138_138
      (fun i => conj_mem_of_fixedPoints _ _ (T138_138 i) (hfix138_138 i) _)
      ⟨138, by decide⟩ ⟨138, by decide⟩ _
      (Q2.validAt ⟨138, by decide⟩ (Q2.listedAt ⟨138, by decide⟩
        (alnCheck_rep ⟨138, by decide⟩ hj hq).1))
      (colE2 ⟨138, by decide⟩ 19 hp) Q2.T138_138_2 Q2.hfix138_138_2 Q2.hinj138_138_2
      Q2.hcardT138_138_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T138_138_2 i) (Q2.hfix138_138_2 i) _)
      colCert_138_138_19.hD ?_).symm
  rw [alnId_138 j hj]


theorem leaf_138_138_20 (hp : 20 < (Q2.transData.getD 138 []).length)
    (j : Nat) (hj : j < (repChars.getD 138 []).length)
    (hq : (normIsRep.getD 138 []).getD j false = true) :
    species (Q2.reps (⟨138, by decide⟩ : Fin 148)) (colE2 ⟨138, by decide⟩ 20 hp)
        (rowE2 (⟨138, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨138, by decide⟩ : Fin 148))
        (colE1 ⟨138, by decide⟩ 20 (transLenTr ⟨138, by decide⟩ 20 hp))
        (rowE1 (⟨138, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨138, by decide⟩ : Fin 148) ⟨138, by decide⟩ _
      (validAt ⟨138, by decide⟩ (listedAt ⟨138, by decide⟩ hj))
      (colE1 ⟨138, by decide⟩ 20 (transLenTr ⟨138, by decide⟩ 20 hp)) T138_138
      hfix138_138 hinj138_138 hcardT138_138
      (fun i => conj_mem_of_fixedPoints _ _ (T138_138 i) (hfix138_138 i) _)
      ⟨138, by decide⟩ ⟨138, by decide⟩ _
      (Q2.validAt ⟨138, by decide⟩ (Q2.listedAt ⟨138, by decide⟩
        (alnCheck_rep ⟨138, by decide⟩ hj hq).1))
      (colE2 ⟨138, by decide⟩ 20 hp) Q2.T138_138_2 Q2.hfix138_138_2 Q2.hinj138_138_2
      Q2.hcardT138_138_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T138_138_2 i) (Q2.hfix138_138_2 i) _)
      colCert_138_138_20.hD ?_).symm
  rw [alnId_138 j hj]


theorem leaf_138_138_21 (hp : 21 < (Q2.transData.getD 138 []).length)
    (j : Nat) (hj : j < (repChars.getD 138 []).length)
    (hq : (normIsRep.getD 138 []).getD j false = true) :
    species (Q2.reps (⟨138, by decide⟩ : Fin 148)) (colE2 ⟨138, by decide⟩ 21 hp)
        (rowE2 (⟨138, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨138, by decide⟩ : Fin 148))
        (colE1 ⟨138, by decide⟩ 21 (transLenTr ⟨138, by decide⟩ 21 hp))
        (rowE1 (⟨138, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨138, by decide⟩ : Fin 148) ⟨138, by decide⟩ _
      (validAt ⟨138, by decide⟩ (listedAt ⟨138, by decide⟩ hj))
      (colE1 ⟨138, by decide⟩ 21 (transLenTr ⟨138, by decide⟩ 21 hp)) T138_138
      hfix138_138 hinj138_138 hcardT138_138
      (fun i => conj_mem_of_fixedPoints _ _ (T138_138 i) (hfix138_138 i) _)
      ⟨138, by decide⟩ ⟨138, by decide⟩ _
      (Q2.validAt ⟨138, by decide⟩ (Q2.listedAt ⟨138, by decide⟩
        (alnCheck_rep ⟨138, by decide⟩ hj hq).1))
      (colE2 ⟨138, by decide⟩ 21 hp) Q2.T138_138_2 Q2.hfix138_138_2 Q2.hinj138_138_2
      Q2.hcardT138_138_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T138_138_2 i) (Q2.hfix138_138_2 i) _)
      colCert_138_138_21.hD ?_).symm
  rw [alnId_138 j hj]


theorem leaf_138_138_22 (hp : 22 < (Q2.transData.getD 138 []).length)
    (j : Nat) (hj : j < (repChars.getD 138 []).length)
    (hq : (normIsRep.getD 138 []).getD j false = true) :
    species (Q2.reps (⟨138, by decide⟩ : Fin 148)) (colE2 ⟨138, by decide⟩ 22 hp)
        (rowE2 (⟨138, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨138, by decide⟩ : Fin 148))
        (colE1 ⟨138, by decide⟩ 22 (transLenTr ⟨138, by decide⟩ 22 hp))
        (rowE1 (⟨138, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨138, by decide⟩ : Fin 148) ⟨138, by decide⟩ _
      (validAt ⟨138, by decide⟩ (listedAt ⟨138, by decide⟩ hj))
      (colE1 ⟨138, by decide⟩ 22 (transLenTr ⟨138, by decide⟩ 22 hp)) T138_138
      hfix138_138 hinj138_138 hcardT138_138
      (fun i => conj_mem_of_fixedPoints _ _ (T138_138 i) (hfix138_138 i) _)
      ⟨138, by decide⟩ ⟨138, by decide⟩ _
      (Q2.validAt ⟨138, by decide⟩ (Q2.listedAt ⟨138, by decide⟩
        (alnCheck_rep ⟨138, by decide⟩ hj hq).1))
      (colE2 ⟨138, by decide⟩ 22 hp) Q2.T138_138_2 Q2.hfix138_138_2 Q2.hinj138_138_2
      Q2.hcardT138_138_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T138_138_2 i) (Q2.hfix138_138_2 i) _)
      colCert_138_138_22.hD ?_).symm
  rw [alnId_138 j hj]


theorem leaf_138_138_23 (hp : 23 < (Q2.transData.getD 138 []).length)
    (j : Nat) (hj : j < (repChars.getD 138 []).length)
    (hq : (normIsRep.getD 138 []).getD j false = true) :
    species (Q2.reps (⟨138, by decide⟩ : Fin 148)) (colE2 ⟨138, by decide⟩ 23 hp)
        (rowE2 (⟨138, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨138, by decide⟩ : Fin 148))
        (colE1 ⟨138, by decide⟩ 23 (transLenTr ⟨138, by decide⟩ 23 hp))
        (rowE1 (⟨138, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨138, by decide⟩ : Fin 148) ⟨138, by decide⟩ _
      (validAt ⟨138, by decide⟩ (listedAt ⟨138, by decide⟩ hj))
      (colE1 ⟨138, by decide⟩ 23 (transLenTr ⟨138, by decide⟩ 23 hp)) T138_138
      hfix138_138 hinj138_138 hcardT138_138
      (fun i => conj_mem_of_fixedPoints _ _ (T138_138 i) (hfix138_138 i) _)
      ⟨138, by decide⟩ ⟨138, by decide⟩ _
      (Q2.validAt ⟨138, by decide⟩ (Q2.listedAt ⟨138, by decide⟩
        (alnCheck_rep ⟨138, by decide⟩ hj hq).1))
      (colE2 ⟨138, by decide⟩ 23 hp) Q2.T138_138_2 Q2.hfix138_138_2 Q2.hinj138_138_2
      Q2.hcardT138_138_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T138_138_2 i) (Q2.hfix138_138_2 i) _)
      colCert_138_138_23.hD ?_).symm
  rw [alnId_138 j hj]


theorem leaf_138_138_24 (hp : 24 < (Q2.transData.getD 138 []).length)
    (j : Nat) (hj : j < (repChars.getD 138 []).length)
    (hq : (normIsRep.getD 138 []).getD j false = true) :
    species (Q2.reps (⟨138, by decide⟩ : Fin 148)) (colE2 ⟨138, by decide⟩ 24 hp)
        (rowE2 (⟨138, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨138, by decide⟩ : Fin 148))
        (colE1 ⟨138, by decide⟩ 24 (transLenTr ⟨138, by decide⟩ 24 hp))
        (rowE1 (⟨138, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨138, by decide⟩ : Fin 148) ⟨138, by decide⟩ _
      (validAt ⟨138, by decide⟩ (listedAt ⟨138, by decide⟩ hj))
      (colE1 ⟨138, by decide⟩ 24 (transLenTr ⟨138, by decide⟩ 24 hp)) T138_138
      hfix138_138 hinj138_138 hcardT138_138
      (fun i => conj_mem_of_fixedPoints _ _ (T138_138 i) (hfix138_138 i) _)
      ⟨138, by decide⟩ ⟨138, by decide⟩ _
      (Q2.validAt ⟨138, by decide⟩ (Q2.listedAt ⟨138, by decide⟩
        (alnCheck_rep ⟨138, by decide⟩ hj hq).1))
      (colE2 ⟨138, by decide⟩ 24 hp) Q2.T138_138_2 Q2.hfix138_138_2 Q2.hinj138_138_2
      Q2.hcardT138_138_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T138_138_2 i) (Q2.hfix138_138_2 i) _)
      colCert_138_138_24.hD ?_).symm
  rw [alnId_138 j hj]


theorem leaf_139_5_0 (hp : 0 < (Q2.transData.getD 5 []).length)
    (j : Nat) (hj : j < (repChars.getD 139 []).length)
    (hq : (normIsRep.getD 139 []).getD j false = true) :
    species (Q2.reps (⟨5, by decide⟩ : Fin 148)) (colE2 ⟨5, by decide⟩ 0 hp)
        (rowE2 (⟨139, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨5, by decide⟩ : Fin 148))
        (colE1 ⟨5, by decide⟩ 0 (transLenTr ⟨5, by decide⟩ 0 hp))
        (rowE1 (⟨139, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨139, by decide⟩ : Fin 148) ⟨5, by decide⟩ _
      (validAt ⟨139, by decide⟩ (listedAt ⟨139, by decide⟩ hj))
      (colE1 ⟨5, by decide⟩ 0 (transLenTr ⟨5, by decide⟩ 0 hp)) T139_5
      hfix139_5 hinj139_5 hcardT139_5
      (fun i => conj_mem_of_fixedPoints _ _ (T139_5 i) (hfix139_5 i) _)
      ⟨139, by decide⟩ ⟨5, by decide⟩ _
      (Q2.validAt ⟨139, by decide⟩ (Q2.listedAt ⟨139, by decide⟩
        (alnCheck_rep ⟨139, by decide⟩ hj hq).1))
      (colE2 ⟨5, by decide⟩ 0 hp) Q2.T139_5_2 Q2.hfix139_5_2 Q2.hinj139_5_2
      Q2.hcardT139_5_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T139_5_2 i) (Q2.hfix139_5_2 i) _)
      colCert_139_5_0.hD ?_).symm
  rw [alnId_139 j hj]


theorem leaf_139_5_1 (hp : 1 < (Q2.transData.getD 5 []).length)
    (j : Nat) (hj : j < (repChars.getD 139 []).length)
    (hq : (normIsRep.getD 139 []).getD j false = true) :
    species (Q2.reps (⟨5, by decide⟩ : Fin 148)) (colE2 ⟨5, by decide⟩ 1 hp)
        (rowE2 (⟨139, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨5, by decide⟩ : Fin 148))
        (colE1 ⟨5, by decide⟩ 1 (transLenTr ⟨5, by decide⟩ 1 hp))
        (rowE1 (⟨139, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨139, by decide⟩ : Fin 148) ⟨5, by decide⟩ _
      (validAt ⟨139, by decide⟩ (listedAt ⟨139, by decide⟩ hj))
      (colE1 ⟨5, by decide⟩ 1 (transLenTr ⟨5, by decide⟩ 1 hp)) T139_5
      hfix139_5 hinj139_5 hcardT139_5
      (fun i => conj_mem_of_fixedPoints _ _ (T139_5 i) (hfix139_5 i) _)
      ⟨139, by decide⟩ ⟨5, by decide⟩ _
      (Q2.validAt ⟨139, by decide⟩ (Q2.listedAt ⟨139, by decide⟩
        (alnCheck_rep ⟨139, by decide⟩ hj hq).1))
      (colE2 ⟨5, by decide⟩ 1 hp) Q2.T139_5_2 Q2.hfix139_5_2 Q2.hinj139_5_2
      Q2.hcardT139_5_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T139_5_2 i) (Q2.hfix139_5_2 i) _)
      ?_).symm
  rw [show colData1 (⟨139, by decide⟩ : Fin 148)
        ((colE1 ⟨5, by decide⟩ 1 (transLenTr ⟨5, by decide⟩ 1 hp) : ↥(reps ⟨5, by decide⟩)) : Coordinate 1)
        T139_5 = colFn colCertDiv_139_5_1.D1 (m := 5) from colCertDiv_139_5_1.bind1,
    show colData2 (⟨139, by decide⟩ : Fin 148)
        ((colE2 ⟨5, by decide⟩ 1 hp : ↥(Q2.reps ⟨5, by decide⟩)) : Coordinate 2)
        Q2.T139_5_2 = colFn colCertDiv_139_5_1.D2 (m := 5) from colCertDiv_139_5_1.bind2]
  rw [alnId_139 j hj]
  exact fastcode_of_div ⟨139, by decide⟩ _ _ _
    ((alnId_139 j hj) ▸ Q2.listedAt (⟨139, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨139, by decide⟩ : Fin 148) hj hq).1) colCertDiv_139_5_1_match


theorem leaf_139_5_2 (hp : 2 < (Q2.transData.getD 5 []).length)
    (j : Nat) (hj : j < (repChars.getD 139 []).length)
    (hq : (normIsRep.getD 139 []).getD j false = true) :
    species (Q2.reps (⟨5, by decide⟩ : Fin 148)) (colE2 ⟨5, by decide⟩ 2 hp)
        (rowE2 (⟨139, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨5, by decide⟩ : Fin 148))
        (colE1 ⟨5, by decide⟩ 2 (transLenTr ⟨5, by decide⟩ 2 hp))
        (rowE1 (⟨139, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨139, by decide⟩ : Fin 148) ⟨5, by decide⟩ _
      (validAt ⟨139, by decide⟩ (listedAt ⟨139, by decide⟩ hj))
      (colE1 ⟨5, by decide⟩ 2 (transLenTr ⟨5, by decide⟩ 2 hp)) T139_5
      hfix139_5 hinj139_5 hcardT139_5
      (fun i => conj_mem_of_fixedPoints _ _ (T139_5 i) (hfix139_5 i) _)
      ⟨139, by decide⟩ ⟨5, by decide⟩ _
      (Q2.validAt ⟨139, by decide⟩ (Q2.listedAt ⟨139, by decide⟩
        (alnCheck_rep ⟨139, by decide⟩ hj hq).1))
      (colE2 ⟨5, by decide⟩ 2 hp) Q2.T139_5_2 Q2.hfix139_5_2 Q2.hinj139_5_2
      Q2.hcardT139_5_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T139_5_2 i) (Q2.hfix139_5_2 i) _)
      ?_).symm
  rw [show colData1 (⟨139, by decide⟩ : Fin 148)
        ((colE1 ⟨5, by decide⟩ 2 (transLenTr ⟨5, by decide⟩ 2 hp) : ↥(reps ⟨5, by decide⟩)) : Coordinate 1)
        T139_5 = colFn colCertDiv_139_5_2.D1 (m := 5) from colCertDiv_139_5_2.bind1,
    show colData2 (⟨139, by decide⟩ : Fin 148)
        ((colE2 ⟨5, by decide⟩ 2 hp : ↥(Q2.reps ⟨5, by decide⟩)) : Coordinate 2)
        Q2.T139_5_2 = colFn colCertDiv_139_5_2.D2 (m := 5) from colCertDiv_139_5_2.bind2]
  rw [alnId_139 j hj]
  exact fastcode_of_div ⟨139, by decide⟩ _ _ _
    ((alnId_139 j hj) ▸ Q2.listedAt (⟨139, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨139, by decide⟩ : Fin 148) hj hq).1) colCertDiv_139_5_2_match


theorem leaf_139_5_3 (hp : 3 < (Q2.transData.getD 5 []).length)
    (j : Nat) (hj : j < (repChars.getD 139 []).length)
    (hq : (normIsRep.getD 139 []).getD j false = true) :
    species (Q2.reps (⟨5, by decide⟩ : Fin 148)) (colE2 ⟨5, by decide⟩ 3 hp)
        (rowE2 (⟨139, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨5, by decide⟩ : Fin 148))
        (colE1 ⟨5, by decide⟩ 3 (transLenTr ⟨5, by decide⟩ 3 hp))
        (rowE1 (⟨139, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨139, by decide⟩ : Fin 148) ⟨5, by decide⟩ _
      (validAt ⟨139, by decide⟩ (listedAt ⟨139, by decide⟩ hj))
      (colE1 ⟨5, by decide⟩ 3 (transLenTr ⟨5, by decide⟩ 3 hp)) T139_5
      hfix139_5 hinj139_5 hcardT139_5
      (fun i => conj_mem_of_fixedPoints _ _ (T139_5 i) (hfix139_5 i) _)
      ⟨139, by decide⟩ ⟨5, by decide⟩ _
      (Q2.validAt ⟨139, by decide⟩ (Q2.listedAt ⟨139, by decide⟩
        (alnCheck_rep ⟨139, by decide⟩ hj hq).1))
      (colE2 ⟨5, by decide⟩ 3 hp) Q2.T139_5_2 Q2.hfix139_5_2 Q2.hinj139_5_2
      Q2.hcardT139_5_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T139_5_2 i) (Q2.hfix139_5_2 i) _)
      ?_).symm
  rw [show colData1 (⟨139, by decide⟩ : Fin 148)
        ((colE1 ⟨5, by decide⟩ 3 (transLenTr ⟨5, by decide⟩ 3 hp) : ↥(reps ⟨5, by decide⟩)) : Coordinate 1)
        T139_5 = colFn colCertDiv_139_5_3.D1 (m := 5) from colCertDiv_139_5_3.bind1,
    show colData2 (⟨139, by decide⟩ : Fin 148)
        ((colE2 ⟨5, by decide⟩ 3 hp : ↥(Q2.reps ⟨5, by decide⟩)) : Coordinate 2)
        Q2.T139_5_2 = colFn colCertDiv_139_5_3.D2 (m := 5) from colCertDiv_139_5_3.bind2]
  rw [alnId_139 j hj]
  exact fastcode_of_div ⟨139, by decide⟩ _ _ _
    ((alnId_139 j hj) ▸ Q2.listedAt (⟨139, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨139, by decide⟩ : Fin 148) hj hq).1) colCertDiv_139_5_3_match


theorem leaf_139_5_4 (hp : 4 < (Q2.transData.getD 5 []).length)
    (j : Nat) (hj : j < (repChars.getD 139 []).length)
    (hq : (normIsRep.getD 139 []).getD j false = true) :
    species (Q2.reps (⟨5, by decide⟩ : Fin 148)) (colE2 ⟨5, by decide⟩ 4 hp)
        (rowE2 (⟨139, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨5, by decide⟩ : Fin 148))
        (colE1 ⟨5, by decide⟩ 4 (transLenTr ⟨5, by decide⟩ 4 hp))
        (rowE1 (⟨139, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨139, by decide⟩ : Fin 148) ⟨5, by decide⟩ _
      (validAt ⟨139, by decide⟩ (listedAt ⟨139, by decide⟩ hj))
      (colE1 ⟨5, by decide⟩ 4 (transLenTr ⟨5, by decide⟩ 4 hp)) T139_5
      hfix139_5 hinj139_5 hcardT139_5
      (fun i => conj_mem_of_fixedPoints _ _ (T139_5 i) (hfix139_5 i) _)
      ⟨139, by decide⟩ ⟨5, by decide⟩ _
      (Q2.validAt ⟨139, by decide⟩ (Q2.listedAt ⟨139, by decide⟩
        (alnCheck_rep ⟨139, by decide⟩ hj hq).1))
      (colE2 ⟨5, by decide⟩ 4 hp) Q2.T139_5_2 Q2.hfix139_5_2 Q2.hinj139_5_2
      Q2.hcardT139_5_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T139_5_2 i) (Q2.hfix139_5_2 i) _)
      ?_).symm
  rw [show colData1 (⟨139, by decide⟩ : Fin 148)
        ((colE1 ⟨5, by decide⟩ 4 (transLenTr ⟨5, by decide⟩ 4 hp) : ↥(reps ⟨5, by decide⟩)) : Coordinate 1)
        T139_5 = colFn colCertDiv_139_5_4.D1 (m := 5) from colCertDiv_139_5_4.bind1,
    show colData2 (⟨139, by decide⟩ : Fin 148)
        ((colE2 ⟨5, by decide⟩ 4 hp : ↥(Q2.reps ⟨5, by decide⟩)) : Coordinate 2)
        Q2.T139_5_2 = colFn colCertDiv_139_5_4.D2 (m := 5) from colCertDiv_139_5_4.bind2]
  rw [alnId_139 j hj]
  exact fastcode_of_div ⟨139, by decide⟩ _ _ _
    ((alnId_139 j hj) ▸ Q2.listedAt (⟨139, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨139, by decide⟩ : Fin 148) hj hq).1) colCertDiv_139_5_4_match


theorem leaf_139_10_0 (hp : 0 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 139 []).length)
    (hq : (normIsRep.getD 139 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 0 hp)
        (rowE2 (⟨139, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 0 (transLenTr ⟨10, by decide⟩ 0 hp))
        (rowE1 (⟨139, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨139, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨139, by decide⟩ (listedAt ⟨139, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 0 (transLenTr ⟨10, by decide⟩ 0 hp)) T139_10
      hfix139_10 hinj139_10 hcardT139_10
      (fun i => conj_mem_of_fixedPoints _ _ (T139_10 i) (hfix139_10 i) _)
      ⟨139, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨139, by decide⟩ (Q2.listedAt ⟨139, by decide⟩
        (alnCheck_rep ⟨139, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 0 hp) Q2.T139_10_2 Q2.hfix139_10_2 Q2.hinj139_10_2
      Q2.hcardT139_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T139_10_2 i) (Q2.hfix139_10_2 i) _)
      colCert_139_10_0.hD ?_).symm
  rw [alnId_139 j hj]


theorem leaf_139_10_1 (hp : 1 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 139 []).length)
    (hq : (normIsRep.getD 139 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 1 hp)
        (rowE2 (⟨139, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 1 (transLenTr ⟨10, by decide⟩ 1 hp))
        (rowE1 (⟨139, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨139, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨139, by decide⟩ (listedAt ⟨139, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 1 (transLenTr ⟨10, by decide⟩ 1 hp)) T139_10
      hfix139_10 hinj139_10 hcardT139_10
      (fun i => conj_mem_of_fixedPoints _ _ (T139_10 i) (hfix139_10 i) _)
      ⟨139, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨139, by decide⟩ (Q2.listedAt ⟨139, by decide⟩
        (alnCheck_rep ⟨139, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 1 hp) Q2.T139_10_2 Q2.hfix139_10_2 Q2.hinj139_10_2
      Q2.hcardT139_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T139_10_2 i) (Q2.hfix139_10_2 i) _)
      colCert_139_10_1.hD ?_).symm
  rw [alnId_139 j hj]


theorem leaf_139_10_2 (hp : 2 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 139 []).length)
    (hq : (normIsRep.getD 139 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 2 hp)
        (rowE2 (⟨139, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 2 (transLenTr ⟨10, by decide⟩ 2 hp))
        (rowE1 (⟨139, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨139, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨139, by decide⟩ (listedAt ⟨139, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 2 (transLenTr ⟨10, by decide⟩ 2 hp)) T139_10
      hfix139_10 hinj139_10 hcardT139_10
      (fun i => conj_mem_of_fixedPoints _ _ (T139_10 i) (hfix139_10 i) _)
      ⟨139, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨139, by decide⟩ (Q2.listedAt ⟨139, by decide⟩
        (alnCheck_rep ⟨139, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 2 hp) Q2.T139_10_2 Q2.hfix139_10_2 Q2.hinj139_10_2
      Q2.hcardT139_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T139_10_2 i) (Q2.hfix139_10_2 i) _)
      colCert_139_10_2.hD ?_).symm
  rw [alnId_139 j hj]


theorem leaf_139_10_3 (hp : 3 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 139 []).length)
    (hq : (normIsRep.getD 139 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 3 hp)
        (rowE2 (⟨139, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 3 (transLenTr ⟨10, by decide⟩ 3 hp))
        (rowE1 (⟨139, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨139, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨139, by decide⟩ (listedAt ⟨139, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 3 (transLenTr ⟨10, by decide⟩ 3 hp)) T139_10
      hfix139_10 hinj139_10 hcardT139_10
      (fun i => conj_mem_of_fixedPoints _ _ (T139_10 i) (hfix139_10 i) _)
      ⟨139, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨139, by decide⟩ (Q2.listedAt ⟨139, by decide⟩
        (alnCheck_rep ⟨139, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 3 hp) Q2.T139_10_2 Q2.hfix139_10_2 Q2.hinj139_10_2
      Q2.hcardT139_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T139_10_2 i) (Q2.hfix139_10_2 i) _)
      colCert_139_10_3.hD ?_).symm
  rw [alnId_139 j hj]


theorem leaf_139_10_4 (hp : 4 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 139 []).length)
    (hq : (normIsRep.getD 139 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 4 hp)
        (rowE2 (⟨139, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 4 (transLenTr ⟨10, by decide⟩ 4 hp))
        (rowE1 (⟨139, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨139, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨139, by decide⟩ (listedAt ⟨139, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 4 (transLenTr ⟨10, by decide⟩ 4 hp)) T139_10
      hfix139_10 hinj139_10 hcardT139_10
      (fun i => conj_mem_of_fixedPoints _ _ (T139_10 i) (hfix139_10 i) _)
      ⟨139, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨139, by decide⟩ (Q2.listedAt ⟨139, by decide⟩
        (alnCheck_rep ⟨139, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 4 hp) Q2.T139_10_2 Q2.hfix139_10_2 Q2.hinj139_10_2
      Q2.hcardT139_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T139_10_2 i) (Q2.hfix139_10_2 i) _)
      colCert_139_10_4.hD ?_).symm
  rw [alnId_139 j hj]


theorem leaf_139_12_0 (hp : 0 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 139 []).length)
    (hq : (normIsRep.getD 139 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 0 hp)
        (rowE2 (⟨139, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp))
        (rowE1 (⟨139, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨139, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨139, by decide⟩ (listedAt ⟨139, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp)) T139_12
      hfix139_12 hinj139_12 hcardT139_12
      (fun i => conj_mem_of_fixedPoints _ _ (T139_12 i) (hfix139_12 i) _)
      ⟨139, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨139, by decide⟩ (Q2.listedAt ⟨139, by decide⟩
        (alnCheck_rep ⟨139, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 0 hp) Q2.T139_12_2 Q2.hfix139_12_2 Q2.hinj139_12_2
      Q2.hcardT139_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T139_12_2 i) (Q2.hfix139_12_2 i) _)
      colCert_139_12_0.hD ?_).symm
  rw [alnId_139 j hj]


theorem leaf_139_12_1 (hp : 1 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 139 []).length)
    (hq : (normIsRep.getD 139 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 1 hp)
        (rowE2 (⟨139, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp))
        (rowE1 (⟨139, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨139, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨139, by decide⟩ (listedAt ⟨139, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp)) T139_12
      hfix139_12 hinj139_12 hcardT139_12
      (fun i => conj_mem_of_fixedPoints _ _ (T139_12 i) (hfix139_12 i) _)
      ⟨139, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨139, by decide⟩ (Q2.listedAt ⟨139, by decide⟩
        (alnCheck_rep ⟨139, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 1 hp) Q2.T139_12_2 Q2.hfix139_12_2 Q2.hinj139_12_2
      Q2.hcardT139_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T139_12_2 i) (Q2.hfix139_12_2 i) _)
      colCert_139_12_1.hD ?_).symm
  rw [alnId_139 j hj]


theorem leaf_139_12_2 (hp : 2 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 139 []).length)
    (hq : (normIsRep.getD 139 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 2 hp)
        (rowE2 (⟨139, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp))
        (rowE1 (⟨139, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨139, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨139, by decide⟩ (listedAt ⟨139, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp)) T139_12
      hfix139_12 hinj139_12 hcardT139_12
      (fun i => conj_mem_of_fixedPoints _ _ (T139_12 i) (hfix139_12 i) _)
      ⟨139, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨139, by decide⟩ (Q2.listedAt ⟨139, by decide⟩
        (alnCheck_rep ⟨139, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 2 hp) Q2.T139_12_2 Q2.hfix139_12_2 Q2.hinj139_12_2
      Q2.hcardT139_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T139_12_2 i) (Q2.hfix139_12_2 i) _)
      colCert_139_12_2.hD ?_).symm
  rw [alnId_139 j hj]


theorem leaf_139_12_3 (hp : 3 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 139 []).length)
    (hq : (normIsRep.getD 139 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 3 hp)
        (rowE2 (⟨139, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp))
        (rowE1 (⟨139, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨139, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨139, by decide⟩ (listedAt ⟨139, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp)) T139_12
      hfix139_12 hinj139_12 hcardT139_12
      (fun i => conj_mem_of_fixedPoints _ _ (T139_12 i) (hfix139_12 i) _)
      ⟨139, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨139, by decide⟩ (Q2.listedAt ⟨139, by decide⟩
        (alnCheck_rep ⟨139, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 3 hp) Q2.T139_12_2 Q2.hfix139_12_2 Q2.hinj139_12_2
      Q2.hcardT139_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T139_12_2 i) (Q2.hfix139_12_2 i) _)
      colCert_139_12_3.hD ?_).symm
  rw [alnId_139 j hj]


theorem leaf_139_12_4 (hp : 4 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 139 []).length)
    (hq : (normIsRep.getD 139 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 4 hp)
        (rowE2 (⟨139, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp))
        (rowE1 (⟨139, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨139, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨139, by decide⟩ (listedAt ⟨139, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp)) T139_12
      hfix139_12 hinj139_12 hcardT139_12
      (fun i => conj_mem_of_fixedPoints _ _ (T139_12 i) (hfix139_12 i) _)
      ⟨139, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨139, by decide⟩ (Q2.listedAt ⟨139, by decide⟩
        (alnCheck_rep ⟨139, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 4 hp) Q2.T139_12_2 Q2.hfix139_12_2 Q2.hinj139_12_2
      Q2.hcardT139_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T139_12_2 i) (Q2.hfix139_12_2 i) _)
      colCert_139_12_4.hD ?_).symm
  rw [alnId_139 j hj]


theorem leaf_139_23_0 (hp : 0 < (Q2.transData.getD 23 []).length)
    (j : Nat) (hj : j < (repChars.getD 139 []).length)
    (hq : (normIsRep.getD 139 []).getD j false = true) :
    species (Q2.reps (⟨23, by decide⟩ : Fin 148)) (colE2 ⟨23, by decide⟩ 0 hp)
        (rowE2 (⟨139, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨23, by decide⟩ : Fin 148))
        (colE1 ⟨23, by decide⟩ 0 (transLenTr ⟨23, by decide⟩ 0 hp))
        (rowE1 (⟨139, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨139, by decide⟩ : Fin 148) ⟨23, by decide⟩ _
      (validAt ⟨139, by decide⟩ (listedAt ⟨139, by decide⟩ hj))
      (colE1 ⟨23, by decide⟩ 0 (transLenTr ⟨23, by decide⟩ 0 hp)) T139_23
      hfix139_23 hinj139_23 hcardT139_23
      (fun i => conj_mem_of_fixedPoints _ _ (T139_23 i) (hfix139_23 i) _)
      ⟨139, by decide⟩ ⟨23, by decide⟩ _
      (Q2.validAt ⟨139, by decide⟩ (Q2.listedAt ⟨139, by decide⟩
        (alnCheck_rep ⟨139, by decide⟩ hj hq).1))
      (colE2 ⟨23, by decide⟩ 0 hp) Q2.T139_23_2 Q2.hfix139_23_2 Q2.hinj139_23_2
      Q2.hcardT139_23_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T139_23_2 i) (Q2.hfix139_23_2 i) _)
      colCert_139_23_0.hD ?_).symm
  rw [alnId_139 j hj]


theorem leaf_139_23_1 (hp : 1 < (Q2.transData.getD 23 []).length)
    (j : Nat) (hj : j < (repChars.getD 139 []).length)
    (hq : (normIsRep.getD 139 []).getD j false = true) :
    species (Q2.reps (⟨23, by decide⟩ : Fin 148)) (colE2 ⟨23, by decide⟩ 1 hp)
        (rowE2 (⟨139, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨23, by decide⟩ : Fin 148))
        (colE1 ⟨23, by decide⟩ 1 (transLenTr ⟨23, by decide⟩ 1 hp))
        (rowE1 (⟨139, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨139, by decide⟩ : Fin 148) ⟨23, by decide⟩ _
      (validAt ⟨139, by decide⟩ (listedAt ⟨139, by decide⟩ hj))
      (colE1 ⟨23, by decide⟩ 1 (transLenTr ⟨23, by decide⟩ 1 hp)) T139_23
      hfix139_23 hinj139_23 hcardT139_23
      (fun i => conj_mem_of_fixedPoints _ _ (T139_23 i) (hfix139_23 i) _)
      ⟨139, by decide⟩ ⟨23, by decide⟩ _
      (Q2.validAt ⟨139, by decide⟩ (Q2.listedAt ⟨139, by decide⟩
        (alnCheck_rep ⟨139, by decide⟩ hj hq).1))
      (colE2 ⟨23, by decide⟩ 1 hp) Q2.T139_23_2 Q2.hfix139_23_2 Q2.hinj139_23_2
      Q2.hcardT139_23_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T139_23_2 i) (Q2.hfix139_23_2 i) _)
      colCert_139_23_1.hD ?_).symm
  rw [alnId_139 j hj]


theorem leaf_139_23_2 (hp : 2 < (Q2.transData.getD 23 []).length)
    (j : Nat) (hj : j < (repChars.getD 139 []).length)
    (hq : (normIsRep.getD 139 []).getD j false = true) :
    species (Q2.reps (⟨23, by decide⟩ : Fin 148)) (colE2 ⟨23, by decide⟩ 2 hp)
        (rowE2 (⟨139, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨23, by decide⟩ : Fin 148))
        (colE1 ⟨23, by decide⟩ 2 (transLenTr ⟨23, by decide⟩ 2 hp))
        (rowE1 (⟨139, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨139, by decide⟩ : Fin 148) ⟨23, by decide⟩ _
      (validAt ⟨139, by decide⟩ (listedAt ⟨139, by decide⟩ hj))
      (colE1 ⟨23, by decide⟩ 2 (transLenTr ⟨23, by decide⟩ 2 hp)) T139_23
      hfix139_23 hinj139_23 hcardT139_23
      (fun i => conj_mem_of_fixedPoints _ _ (T139_23 i) (hfix139_23 i) _)
      ⟨139, by decide⟩ ⟨23, by decide⟩ _
      (Q2.validAt ⟨139, by decide⟩ (Q2.listedAt ⟨139, by decide⟩
        (alnCheck_rep ⟨139, by decide⟩ hj hq).1))
      (colE2 ⟨23, by decide⟩ 2 hp) Q2.T139_23_2 Q2.hfix139_23_2 Q2.hinj139_23_2
      Q2.hcardT139_23_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T139_23_2 i) (Q2.hfix139_23_2 i) _)
      colCert_139_23_2.hD ?_).symm
  rw [alnId_139 j hj]


theorem leaf_139_23_3 (hp : 3 < (Q2.transData.getD 23 []).length)
    (j : Nat) (hj : j < (repChars.getD 139 []).length)
    (hq : (normIsRep.getD 139 []).getD j false = true) :
    species (Q2.reps (⟨23, by decide⟩ : Fin 148)) (colE2 ⟨23, by decide⟩ 3 hp)
        (rowE2 (⟨139, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨23, by decide⟩ : Fin 148))
        (colE1 ⟨23, by decide⟩ 3 (transLenTr ⟨23, by decide⟩ 3 hp))
        (rowE1 (⟨139, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨139, by decide⟩ : Fin 148) ⟨23, by decide⟩ _
      (validAt ⟨139, by decide⟩ (listedAt ⟨139, by decide⟩ hj))
      (colE1 ⟨23, by decide⟩ 3 (transLenTr ⟨23, by decide⟩ 3 hp)) T139_23
      hfix139_23 hinj139_23 hcardT139_23
      (fun i => conj_mem_of_fixedPoints _ _ (T139_23 i) (hfix139_23 i) _)
      ⟨139, by decide⟩ ⟨23, by decide⟩ _
      (Q2.validAt ⟨139, by decide⟩ (Q2.listedAt ⟨139, by decide⟩
        (alnCheck_rep ⟨139, by decide⟩ hj hq).1))
      (colE2 ⟨23, by decide⟩ 3 hp) Q2.T139_23_2 Q2.hfix139_23_2 Q2.hinj139_23_2
      Q2.hcardT139_23_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T139_23_2 i) (Q2.hfix139_23_2 i) _)
      colCert_139_23_3.hD ?_).symm
  rw [alnId_139 j hj]


theorem leaf_139_23_4 (hp : 4 < (Q2.transData.getD 23 []).length)
    (j : Nat) (hj : j < (repChars.getD 139 []).length)
    (hq : (normIsRep.getD 139 []).getD j false = true) :
    species (Q2.reps (⟨23, by decide⟩ : Fin 148)) (colE2 ⟨23, by decide⟩ 4 hp)
        (rowE2 (⟨139, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨23, by decide⟩ : Fin 148))
        (colE1 ⟨23, by decide⟩ 4 (transLenTr ⟨23, by decide⟩ 4 hp))
        (rowE1 (⟨139, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨139, by decide⟩ : Fin 148) ⟨23, by decide⟩ _
      (validAt ⟨139, by decide⟩ (listedAt ⟨139, by decide⟩ hj))
      (colE1 ⟨23, by decide⟩ 4 (transLenTr ⟨23, by decide⟩ 4 hp)) T139_23
      hfix139_23 hinj139_23 hcardT139_23
      (fun i => conj_mem_of_fixedPoints _ _ (T139_23 i) (hfix139_23 i) _)
      ⟨139, by decide⟩ ⟨23, by decide⟩ _
      (Q2.validAt ⟨139, by decide⟩ (Q2.listedAt ⟨139, by decide⟩
        (alnCheck_rep ⟨139, by decide⟩ hj hq).1))
      (colE2 ⟨23, by decide⟩ 4 hp) Q2.T139_23_2 Q2.hfix139_23_2 Q2.hinj139_23_2
      Q2.hcardT139_23_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T139_23_2 i) (Q2.hfix139_23_2 i) _)
      colCert_139_23_4.hD ?_).symm
  rw [alnId_139 j hj]


theorem leaf_139_23_5 (hp : 5 < (Q2.transData.getD 23 []).length)
    (j : Nat) (hj : j < (repChars.getD 139 []).length)
    (hq : (normIsRep.getD 139 []).getD j false = true) :
    species (Q2.reps (⟨23, by decide⟩ : Fin 148)) (colE2 ⟨23, by decide⟩ 5 hp)
        (rowE2 (⟨139, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨23, by decide⟩ : Fin 148))
        (colE1 ⟨23, by decide⟩ 5 (transLenTr ⟨23, by decide⟩ 5 hp))
        (rowE1 (⟨139, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨139, by decide⟩ : Fin 148) ⟨23, by decide⟩ _
      (validAt ⟨139, by decide⟩ (listedAt ⟨139, by decide⟩ hj))
      (colE1 ⟨23, by decide⟩ 5 (transLenTr ⟨23, by decide⟩ 5 hp)) T139_23
      hfix139_23 hinj139_23 hcardT139_23
      (fun i => conj_mem_of_fixedPoints _ _ (T139_23 i) (hfix139_23 i) _)
      ⟨139, by decide⟩ ⟨23, by decide⟩ _
      (Q2.validAt ⟨139, by decide⟩ (Q2.listedAt ⟨139, by decide⟩
        (alnCheck_rep ⟨139, by decide⟩ hj hq).1))
      (colE2 ⟨23, by decide⟩ 5 hp) Q2.T139_23_2 Q2.hfix139_23_2 Q2.hinj139_23_2
      Q2.hcardT139_23_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T139_23_2 i) (Q2.hfix139_23_2 i) _)
      ?_).symm
  rw [show colData1 (⟨139, by decide⟩ : Fin 148)
        ((colE1 ⟨23, by decide⟩ 5 (transLenTr ⟨23, by decide⟩ 5 hp) : ↥(reps ⟨23, by decide⟩)) : Coordinate 1)
        T139_23 = colFn colCertDiv_139_23_5.D1 (m := 5) from colCertDiv_139_23_5.bind1,
    show colData2 (⟨139, by decide⟩ : Fin 148)
        ((colE2 ⟨23, by decide⟩ 5 hp : ↥(Q2.reps ⟨23, by decide⟩)) : Coordinate 2)
        Q2.T139_23_2 = colFn colCertDiv_139_23_5.D2 (m := 5) from colCertDiv_139_23_5.bind2]
  rw [alnId_139 j hj]
  exact fastcode_of_div ⟨139, by decide⟩ _ _ _
    ((alnId_139 j hj) ▸ Q2.listedAt (⟨139, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨139, by decide⟩ : Fin 148) hj hq).1) colCertDiv_139_23_5_match


theorem leaf_139_23_10 (hp : 10 < (Q2.transData.getD 23 []).length)
    (j : Nat) (hj : j < (repChars.getD 139 []).length)
    (hq : (normIsRep.getD 139 []).getD j false = true) :
    species (Q2.reps (⟨23, by decide⟩ : Fin 148)) (colE2 ⟨23, by decide⟩ 10 hp)
        (rowE2 (⟨139, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨23, by decide⟩ : Fin 148))
        (colE1 ⟨23, by decide⟩ 10 (transLenTr ⟨23, by decide⟩ 10 hp))
        (rowE1 (⟨139, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨139, by decide⟩ : Fin 148) ⟨23, by decide⟩ _
      (validAt ⟨139, by decide⟩ (listedAt ⟨139, by decide⟩ hj))
      (colE1 ⟨23, by decide⟩ 10 (transLenTr ⟨23, by decide⟩ 10 hp)) T139_23
      hfix139_23 hinj139_23 hcardT139_23
      (fun i => conj_mem_of_fixedPoints _ _ (T139_23 i) (hfix139_23 i) _)
      ⟨139, by decide⟩ ⟨23, by decide⟩ _
      (Q2.validAt ⟨139, by decide⟩ (Q2.listedAt ⟨139, by decide⟩
        (alnCheck_rep ⟨139, by decide⟩ hj hq).1))
      (colE2 ⟨23, by decide⟩ 10 hp) Q2.T139_23_2 Q2.hfix139_23_2 Q2.hinj139_23_2
      Q2.hcardT139_23_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T139_23_2 i) (Q2.hfix139_23_2 i) _)
      ?_).symm
  rw [show colData1 (⟨139, by decide⟩ : Fin 148)
        ((colE1 ⟨23, by decide⟩ 10 (transLenTr ⟨23, by decide⟩ 10 hp) : ↥(reps ⟨23, by decide⟩)) : Coordinate 1)
        T139_23 = colFn colCertDiv_139_23_10.D1 (m := 5) from colCertDiv_139_23_10.bind1,
    show colData2 (⟨139, by decide⟩ : Fin 148)
        ((colE2 ⟨23, by decide⟩ 10 hp : ↥(Q2.reps ⟨23, by decide⟩)) : Coordinate 2)
        Q2.T139_23_2 = colFn colCertDiv_139_23_10.D2 (m := 5) from colCertDiv_139_23_10.bind2]
  rw [alnId_139 j hj]
  exact fastcode_of_div ⟨139, by decide⟩ _ _ _
    ((alnId_139 j hj) ▸ Q2.listedAt (⟨139, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨139, by decide⟩ : Fin 148) hj hq).1) colCertDiv_139_23_10_match


theorem leaf_139_23_15 (hp : 15 < (Q2.transData.getD 23 []).length)
    (j : Nat) (hj : j < (repChars.getD 139 []).length)
    (hq : (normIsRep.getD 139 []).getD j false = true) :
    species (Q2.reps (⟨23, by decide⟩ : Fin 148)) (colE2 ⟨23, by decide⟩ 15 hp)
        (rowE2 (⟨139, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨23, by decide⟩ : Fin 148))
        (colE1 ⟨23, by decide⟩ 15 (transLenTr ⟨23, by decide⟩ 15 hp))
        (rowE1 (⟨139, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨139, by decide⟩ : Fin 148) ⟨23, by decide⟩ _
      (validAt ⟨139, by decide⟩ (listedAt ⟨139, by decide⟩ hj))
      (colE1 ⟨23, by decide⟩ 15 (transLenTr ⟨23, by decide⟩ 15 hp)) T139_23
      hfix139_23 hinj139_23 hcardT139_23
      (fun i => conj_mem_of_fixedPoints _ _ (T139_23 i) (hfix139_23 i) _)
      ⟨139, by decide⟩ ⟨23, by decide⟩ _
      (Q2.validAt ⟨139, by decide⟩ (Q2.listedAt ⟨139, by decide⟩
        (alnCheck_rep ⟨139, by decide⟩ hj hq).1))
      (colE2 ⟨23, by decide⟩ 15 hp) Q2.T139_23_2 Q2.hfix139_23_2 Q2.hinj139_23_2
      Q2.hcardT139_23_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T139_23_2 i) (Q2.hfix139_23_2 i) _)
      ?_).symm
  rw [show colData1 (⟨139, by decide⟩ : Fin 148)
        ((colE1 ⟨23, by decide⟩ 15 (transLenTr ⟨23, by decide⟩ 15 hp) : ↥(reps ⟨23, by decide⟩)) : Coordinate 1)
        T139_23 = colFn colCertDiv_139_23_15.D1 (m := 5) from colCertDiv_139_23_15.bind1,
    show colData2 (⟨139, by decide⟩ : Fin 148)
        ((colE2 ⟨23, by decide⟩ 15 hp : ↥(Q2.reps ⟨23, by decide⟩)) : Coordinate 2)
        Q2.T139_23_2 = colFn colCertDiv_139_23_15.D2 (m := 5) from colCertDiv_139_23_15.bind2]
  rw [alnId_139 j hj]
  exact fastcode_of_div ⟨139, by decide⟩ _ _ _
    ((alnId_139 j hj) ▸ Q2.listedAt (⟨139, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨139, by decide⟩ : Fin 148) hj hq).1) colCertDiv_139_23_15_match


theorem leaf_139_23_20 (hp : 20 < (Q2.transData.getD 23 []).length)
    (j : Nat) (hj : j < (repChars.getD 139 []).length)
    (hq : (normIsRep.getD 139 []).getD j false = true) :
    species (Q2.reps (⟨23, by decide⟩ : Fin 148)) (colE2 ⟨23, by decide⟩ 20 hp)
        (rowE2 (⟨139, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨23, by decide⟩ : Fin 148))
        (colE1 ⟨23, by decide⟩ 20 (transLenTr ⟨23, by decide⟩ 20 hp))
        (rowE1 (⟨139, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨139, by decide⟩ : Fin 148) ⟨23, by decide⟩ _
      (validAt ⟨139, by decide⟩ (listedAt ⟨139, by decide⟩ hj))
      (colE1 ⟨23, by decide⟩ 20 (transLenTr ⟨23, by decide⟩ 20 hp)) T139_23
      hfix139_23 hinj139_23 hcardT139_23
      (fun i => conj_mem_of_fixedPoints _ _ (T139_23 i) (hfix139_23 i) _)
      ⟨139, by decide⟩ ⟨23, by decide⟩ _
      (Q2.validAt ⟨139, by decide⟩ (Q2.listedAt ⟨139, by decide⟩
        (alnCheck_rep ⟨139, by decide⟩ hj hq).1))
      (colE2 ⟨23, by decide⟩ 20 hp) Q2.T139_23_2 Q2.hfix139_23_2 Q2.hinj139_23_2
      Q2.hcardT139_23_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T139_23_2 i) (Q2.hfix139_23_2 i) _)
      ?_).symm
  rw [show colData1 (⟨139, by decide⟩ : Fin 148)
        ((colE1 ⟨23, by decide⟩ 20 (transLenTr ⟨23, by decide⟩ 20 hp) : ↥(reps ⟨23, by decide⟩)) : Coordinate 1)
        T139_23 = colFn colCertDiv_139_23_20.D1 (m := 5) from colCertDiv_139_23_20.bind1,
    show colData2 (⟨139, by decide⟩ : Fin 148)
        ((colE2 ⟨23, by decide⟩ 20 hp : ↥(Q2.reps ⟨23, by decide⟩)) : Coordinate 2)
        Q2.T139_23_2 = colFn colCertDiv_139_23_20.D2 (m := 5) from colCertDiv_139_23_20.bind2]
  rw [alnId_139 j hj]
  exact fastcode_of_div ⟨139, by decide⟩ _ _ _
    ((alnId_139 j hj) ▸ Q2.listedAt (⟨139, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨139, by decide⟩ : Fin 148) hj hq).1) colCertDiv_139_23_20_match


theorem leaf_139_32_0 (hp : 0 < (Q2.transData.getD 32 []).length)
    (j : Nat) (hj : j < (repChars.getD 139 []).length)
    (hq : (normIsRep.getD 139 []).getD j false = true) :
    species (Q2.reps (⟨32, by decide⟩ : Fin 148)) (colE2 ⟨32, by decide⟩ 0 hp)
        (rowE2 (⟨139, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨32, by decide⟩ : Fin 148))
        (colE1 ⟨32, by decide⟩ 0 (transLenTr ⟨32, by decide⟩ 0 hp))
        (rowE1 (⟨139, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨139, by decide⟩ : Fin 148) ⟨32, by decide⟩ _
      (validAt ⟨139, by decide⟩ (listedAt ⟨139, by decide⟩ hj))
      (colE1 ⟨32, by decide⟩ 0 (transLenTr ⟨32, by decide⟩ 0 hp)) T139_32
      hfix139_32 hinj139_32 hcardT139_32
      (fun i => conj_mem_of_fixedPoints _ _ (T139_32 i) (hfix139_32 i) _)
      ⟨139, by decide⟩ ⟨32, by decide⟩ _
      (Q2.validAt ⟨139, by decide⟩ (Q2.listedAt ⟨139, by decide⟩
        (alnCheck_rep ⟨139, by decide⟩ hj hq).1))
      (colE2 ⟨32, by decide⟩ 0 hp) Q2.T139_32_2 Q2.hfix139_32_2 Q2.hinj139_32_2
      Q2.hcardT139_32_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T139_32_2 i) (Q2.hfix139_32_2 i) _)
      colCert_139_32_0.hD ?_).symm
  rw [alnId_139 j hj]


theorem leaf_139_32_1 (hp : 1 < (Q2.transData.getD 32 []).length)
    (j : Nat) (hj : j < (repChars.getD 139 []).length)
    (hq : (normIsRep.getD 139 []).getD j false = true) :
    species (Q2.reps (⟨32, by decide⟩ : Fin 148)) (colE2 ⟨32, by decide⟩ 1 hp)
        (rowE2 (⟨139, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨32, by decide⟩ : Fin 148))
        (colE1 ⟨32, by decide⟩ 1 (transLenTr ⟨32, by decide⟩ 1 hp))
        (rowE1 (⟨139, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨139, by decide⟩ : Fin 148) ⟨32, by decide⟩ _
      (validAt ⟨139, by decide⟩ (listedAt ⟨139, by decide⟩ hj))
      (colE1 ⟨32, by decide⟩ 1 (transLenTr ⟨32, by decide⟩ 1 hp)) T139_32
      hfix139_32 hinj139_32 hcardT139_32
      (fun i => conj_mem_of_fixedPoints _ _ (T139_32 i) (hfix139_32 i) _)
      ⟨139, by decide⟩ ⟨32, by decide⟩ _
      (Q2.validAt ⟨139, by decide⟩ (Q2.listedAt ⟨139, by decide⟩
        (alnCheck_rep ⟨139, by decide⟩ hj hq).1))
      (colE2 ⟨32, by decide⟩ 1 hp) Q2.T139_32_2 Q2.hfix139_32_2 Q2.hinj139_32_2
      Q2.hcardT139_32_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T139_32_2 i) (Q2.hfix139_32_2 i) _)
      colCert_139_32_1.hD ?_).symm
  rw [alnId_139 j hj]


theorem leaf_139_32_2 (hp : 2 < (Q2.transData.getD 32 []).length)
    (j : Nat) (hj : j < (repChars.getD 139 []).length)
    (hq : (normIsRep.getD 139 []).getD j false = true) :
    species (Q2.reps (⟨32, by decide⟩ : Fin 148)) (colE2 ⟨32, by decide⟩ 2 hp)
        (rowE2 (⟨139, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨32, by decide⟩ : Fin 148))
        (colE1 ⟨32, by decide⟩ 2 (transLenTr ⟨32, by decide⟩ 2 hp))
        (rowE1 (⟨139, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨139, by decide⟩ : Fin 148) ⟨32, by decide⟩ _
      (validAt ⟨139, by decide⟩ (listedAt ⟨139, by decide⟩ hj))
      (colE1 ⟨32, by decide⟩ 2 (transLenTr ⟨32, by decide⟩ 2 hp)) T139_32
      hfix139_32 hinj139_32 hcardT139_32
      (fun i => conj_mem_of_fixedPoints _ _ (T139_32 i) (hfix139_32 i) _)
      ⟨139, by decide⟩ ⟨32, by decide⟩ _
      (Q2.validAt ⟨139, by decide⟩ (Q2.listedAt ⟨139, by decide⟩
        (alnCheck_rep ⟨139, by decide⟩ hj hq).1))
      (colE2 ⟨32, by decide⟩ 2 hp) Q2.T139_32_2 Q2.hfix139_32_2 Q2.hinj139_32_2
      Q2.hcardT139_32_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T139_32_2 i) (Q2.hfix139_32_2 i) _)
      colCert_139_32_2.hD ?_).symm
  rw [alnId_139 j hj]


theorem leaf_139_32_3 (hp : 3 < (Q2.transData.getD 32 []).length)
    (j : Nat) (hj : j < (repChars.getD 139 []).length)
    (hq : (normIsRep.getD 139 []).getD j false = true) :
    species (Q2.reps (⟨32, by decide⟩ : Fin 148)) (colE2 ⟨32, by decide⟩ 3 hp)
        (rowE2 (⟨139, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨32, by decide⟩ : Fin 148))
        (colE1 ⟨32, by decide⟩ 3 (transLenTr ⟨32, by decide⟩ 3 hp))
        (rowE1 (⟨139, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨139, by decide⟩ : Fin 148) ⟨32, by decide⟩ _
      (validAt ⟨139, by decide⟩ (listedAt ⟨139, by decide⟩ hj))
      (colE1 ⟨32, by decide⟩ 3 (transLenTr ⟨32, by decide⟩ 3 hp)) T139_32
      hfix139_32 hinj139_32 hcardT139_32
      (fun i => conj_mem_of_fixedPoints _ _ (T139_32 i) (hfix139_32 i) _)
      ⟨139, by decide⟩ ⟨32, by decide⟩ _
      (Q2.validAt ⟨139, by decide⟩ (Q2.listedAt ⟨139, by decide⟩
        (alnCheck_rep ⟨139, by decide⟩ hj hq).1))
      (colE2 ⟨32, by decide⟩ 3 hp) Q2.T139_32_2 Q2.hfix139_32_2 Q2.hinj139_32_2
      Q2.hcardT139_32_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T139_32_2 i) (Q2.hfix139_32_2 i) _)
      colCert_139_32_3.hD ?_).symm
  rw [alnId_139 j hj]


theorem leaf_139_32_4 (hp : 4 < (Q2.transData.getD 32 []).length)
    (j : Nat) (hj : j < (repChars.getD 139 []).length)
    (hq : (normIsRep.getD 139 []).getD j false = true) :
    species (Q2.reps (⟨32, by decide⟩ : Fin 148)) (colE2 ⟨32, by decide⟩ 4 hp)
        (rowE2 (⟨139, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨32, by decide⟩ : Fin 148))
        (colE1 ⟨32, by decide⟩ 4 (transLenTr ⟨32, by decide⟩ 4 hp))
        (rowE1 (⟨139, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨139, by decide⟩ : Fin 148) ⟨32, by decide⟩ _
      (validAt ⟨139, by decide⟩ (listedAt ⟨139, by decide⟩ hj))
      (colE1 ⟨32, by decide⟩ 4 (transLenTr ⟨32, by decide⟩ 4 hp)) T139_32
      hfix139_32 hinj139_32 hcardT139_32
      (fun i => conj_mem_of_fixedPoints _ _ (T139_32 i) (hfix139_32 i) _)
      ⟨139, by decide⟩ ⟨32, by decide⟩ _
      (Q2.validAt ⟨139, by decide⟩ (Q2.listedAt ⟨139, by decide⟩
        (alnCheck_rep ⟨139, by decide⟩ hj hq).1))
      (colE2 ⟨32, by decide⟩ 4 hp) Q2.T139_32_2 Q2.hfix139_32_2 Q2.hinj139_32_2
      Q2.hcardT139_32_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T139_32_2 i) (Q2.hfix139_32_2 i) _)
      colCert_139_32_4.hD ?_).symm
  rw [alnId_139 j hj]


theorem leaf_139_32_5 (hp : 5 < (Q2.transData.getD 32 []).length)
    (j : Nat) (hj : j < (repChars.getD 139 []).length)
    (hq : (normIsRep.getD 139 []).getD j false = true) :
    species (Q2.reps (⟨32, by decide⟩ : Fin 148)) (colE2 ⟨32, by decide⟩ 5 hp)
        (rowE2 (⟨139, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨32, by decide⟩ : Fin 148))
        (colE1 ⟨32, by decide⟩ 5 (transLenTr ⟨32, by decide⟩ 5 hp))
        (rowE1 (⟨139, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨139, by decide⟩ : Fin 148) ⟨32, by decide⟩ _
      (validAt ⟨139, by decide⟩ (listedAt ⟨139, by decide⟩ hj))
      (colE1 ⟨32, by decide⟩ 5 (transLenTr ⟨32, by decide⟩ 5 hp)) T139_32
      hfix139_32 hinj139_32 hcardT139_32
      (fun i => conj_mem_of_fixedPoints _ _ (T139_32 i) (hfix139_32 i) _)
      ⟨139, by decide⟩ ⟨32, by decide⟩ _
      (Q2.validAt ⟨139, by decide⟩ (Q2.listedAt ⟨139, by decide⟩
        (alnCheck_rep ⟨139, by decide⟩ hj hq).1))
      (colE2 ⟨32, by decide⟩ 5 hp) Q2.T139_32_2 Q2.hfix139_32_2 Q2.hinj139_32_2
      Q2.hcardT139_32_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T139_32_2 i) (Q2.hfix139_32_2 i) _)
      colCert_139_32_5.hD ?_).symm
  rw [alnId_139 j hj]


theorem leaf_139_32_10 (hp : 10 < (Q2.transData.getD 32 []).length)
    (j : Nat) (hj : j < (repChars.getD 139 []).length)
    (hq : (normIsRep.getD 139 []).getD j false = true) :
    species (Q2.reps (⟨32, by decide⟩ : Fin 148)) (colE2 ⟨32, by decide⟩ 10 hp)
        (rowE2 (⟨139, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨32, by decide⟩ : Fin 148))
        (colE1 ⟨32, by decide⟩ 10 (transLenTr ⟨32, by decide⟩ 10 hp))
        (rowE1 (⟨139, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨139, by decide⟩ : Fin 148) ⟨32, by decide⟩ _
      (validAt ⟨139, by decide⟩ (listedAt ⟨139, by decide⟩ hj))
      (colE1 ⟨32, by decide⟩ 10 (transLenTr ⟨32, by decide⟩ 10 hp)) T139_32
      hfix139_32 hinj139_32 hcardT139_32
      (fun i => conj_mem_of_fixedPoints _ _ (T139_32 i) (hfix139_32 i) _)
      ⟨139, by decide⟩ ⟨32, by decide⟩ _
      (Q2.validAt ⟨139, by decide⟩ (Q2.listedAt ⟨139, by decide⟩
        (alnCheck_rep ⟨139, by decide⟩ hj hq).1))
      (colE2 ⟨32, by decide⟩ 10 hp) Q2.T139_32_2 Q2.hfix139_32_2 Q2.hinj139_32_2
      Q2.hcardT139_32_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T139_32_2 i) (Q2.hfix139_32_2 i) _)
      colCert_139_32_10.hD ?_).symm
  rw [alnId_139 j hj]


theorem leaf_139_32_15 (hp : 15 < (Q2.transData.getD 32 []).length)
    (j : Nat) (hj : j < (repChars.getD 139 []).length)
    (hq : (normIsRep.getD 139 []).getD j false = true) :
    species (Q2.reps (⟨32, by decide⟩ : Fin 148)) (colE2 ⟨32, by decide⟩ 15 hp)
        (rowE2 (⟨139, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨32, by decide⟩ : Fin 148))
        (colE1 ⟨32, by decide⟩ 15 (transLenTr ⟨32, by decide⟩ 15 hp))
        (rowE1 (⟨139, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨139, by decide⟩ : Fin 148) ⟨32, by decide⟩ _
      (validAt ⟨139, by decide⟩ (listedAt ⟨139, by decide⟩ hj))
      (colE1 ⟨32, by decide⟩ 15 (transLenTr ⟨32, by decide⟩ 15 hp)) T139_32
      hfix139_32 hinj139_32 hcardT139_32
      (fun i => conj_mem_of_fixedPoints _ _ (T139_32 i) (hfix139_32 i) _)
      ⟨139, by decide⟩ ⟨32, by decide⟩ _
      (Q2.validAt ⟨139, by decide⟩ (Q2.listedAt ⟨139, by decide⟩
        (alnCheck_rep ⟨139, by decide⟩ hj hq).1))
      (colE2 ⟨32, by decide⟩ 15 hp) Q2.T139_32_2 Q2.hfix139_32_2 Q2.hinj139_32_2
      Q2.hcardT139_32_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T139_32_2 i) (Q2.hfix139_32_2 i) _)
      colCert_139_32_15.hD ?_).symm
  rw [alnId_139 j hj]


theorem leaf_139_32_20 (hp : 20 < (Q2.transData.getD 32 []).length)
    (j : Nat) (hj : j < (repChars.getD 139 []).length)
    (hq : (normIsRep.getD 139 []).getD j false = true) :
    species (Q2.reps (⟨32, by decide⟩ : Fin 148)) (colE2 ⟨32, by decide⟩ 20 hp)
        (rowE2 (⟨139, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨32, by decide⟩ : Fin 148))
        (colE1 ⟨32, by decide⟩ 20 (transLenTr ⟨32, by decide⟩ 20 hp))
        (rowE1 (⟨139, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨139, by decide⟩ : Fin 148) ⟨32, by decide⟩ _
      (validAt ⟨139, by decide⟩ (listedAt ⟨139, by decide⟩ hj))
      (colE1 ⟨32, by decide⟩ 20 (transLenTr ⟨32, by decide⟩ 20 hp)) T139_32
      hfix139_32 hinj139_32 hcardT139_32
      (fun i => conj_mem_of_fixedPoints _ _ (T139_32 i) (hfix139_32 i) _)
      ⟨139, by decide⟩ ⟨32, by decide⟩ _
      (Q2.validAt ⟨139, by decide⟩ (Q2.listedAt ⟨139, by decide⟩
        (alnCheck_rep ⟨139, by decide⟩ hj hq).1))
      (colE2 ⟨32, by decide⟩ 20 hp) Q2.T139_32_2 Q2.hfix139_32_2 Q2.hinj139_32_2
      Q2.hcardT139_32_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T139_32_2 i) (Q2.hfix139_32_2 i) _)
      colCert_139_32_20.hD ?_).symm
  rw [alnId_139 j hj]


theorem leaf_139_34_0 (hp : 0 < (Q2.transData.getD 34 []).length)
    (j : Nat) (hj : j < (repChars.getD 139 []).length)
    (hq : (normIsRep.getD 139 []).getD j false = true) :
    species (Q2.reps (⟨34, by decide⟩ : Fin 148)) (colE2 ⟨34, by decide⟩ 0 hp)
        (rowE2 (⟨139, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨34, by decide⟩ : Fin 148))
        (colE1 ⟨34, by decide⟩ 0 (transLenTr ⟨34, by decide⟩ 0 hp))
        (rowE1 (⟨139, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨139, by decide⟩ : Fin 148) ⟨34, by decide⟩ _
      (validAt ⟨139, by decide⟩ (listedAt ⟨139, by decide⟩ hj))
      (colE1 ⟨34, by decide⟩ 0 (transLenTr ⟨34, by decide⟩ 0 hp)) T139_34
      hfix139_34 hinj139_34 hcardT139_34
      (fun i => conj_mem_of_fixedPoints _ _ (T139_34 i) (hfix139_34 i) _)
      ⟨139, by decide⟩ ⟨34, by decide⟩ _
      (Q2.validAt ⟨139, by decide⟩ (Q2.listedAt ⟨139, by decide⟩
        (alnCheck_rep ⟨139, by decide⟩ hj hq).1))
      (colE2 ⟨34, by decide⟩ 0 hp) Q2.T139_34_2 Q2.hfix139_34_2 Q2.hinj139_34_2
      Q2.hcardT139_34_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T139_34_2 i) (Q2.hfix139_34_2 i) _)
      colCert_139_34_0.hD ?_).symm
  rw [alnId_139 j hj]


theorem leaf_139_34_1 (hp : 1 < (Q2.transData.getD 34 []).length)
    (j : Nat) (hj : j < (repChars.getD 139 []).length)
    (hq : (normIsRep.getD 139 []).getD j false = true) :
    species (Q2.reps (⟨34, by decide⟩ : Fin 148)) (colE2 ⟨34, by decide⟩ 1 hp)
        (rowE2 (⟨139, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨34, by decide⟩ : Fin 148))
        (colE1 ⟨34, by decide⟩ 1 (transLenTr ⟨34, by decide⟩ 1 hp))
        (rowE1 (⟨139, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨139, by decide⟩ : Fin 148) ⟨34, by decide⟩ _
      (validAt ⟨139, by decide⟩ (listedAt ⟨139, by decide⟩ hj))
      (colE1 ⟨34, by decide⟩ 1 (transLenTr ⟨34, by decide⟩ 1 hp)) T139_34
      hfix139_34 hinj139_34 hcardT139_34
      (fun i => conj_mem_of_fixedPoints _ _ (T139_34 i) (hfix139_34 i) _)
      ⟨139, by decide⟩ ⟨34, by decide⟩ _
      (Q2.validAt ⟨139, by decide⟩ (Q2.listedAt ⟨139, by decide⟩
        (alnCheck_rep ⟨139, by decide⟩ hj hq).1))
      (colE2 ⟨34, by decide⟩ 1 hp) Q2.T139_34_2 Q2.hfix139_34_2 Q2.hinj139_34_2
      Q2.hcardT139_34_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T139_34_2 i) (Q2.hfix139_34_2 i) _)
      colCert_139_34_1.hD ?_).symm
  rw [alnId_139 j hj]


theorem leaf_139_34_2 (hp : 2 < (Q2.transData.getD 34 []).length)
    (j : Nat) (hj : j < (repChars.getD 139 []).length)
    (hq : (normIsRep.getD 139 []).getD j false = true) :
    species (Q2.reps (⟨34, by decide⟩ : Fin 148)) (colE2 ⟨34, by decide⟩ 2 hp)
        (rowE2 (⟨139, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨34, by decide⟩ : Fin 148))
        (colE1 ⟨34, by decide⟩ 2 (transLenTr ⟨34, by decide⟩ 2 hp))
        (rowE1 (⟨139, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨139, by decide⟩ : Fin 148) ⟨34, by decide⟩ _
      (validAt ⟨139, by decide⟩ (listedAt ⟨139, by decide⟩ hj))
      (colE1 ⟨34, by decide⟩ 2 (transLenTr ⟨34, by decide⟩ 2 hp)) T139_34
      hfix139_34 hinj139_34 hcardT139_34
      (fun i => conj_mem_of_fixedPoints _ _ (T139_34 i) (hfix139_34 i) _)
      ⟨139, by decide⟩ ⟨34, by decide⟩ _
      (Q2.validAt ⟨139, by decide⟩ (Q2.listedAt ⟨139, by decide⟩
        (alnCheck_rep ⟨139, by decide⟩ hj hq).1))
      (colE2 ⟨34, by decide⟩ 2 hp) Q2.T139_34_2 Q2.hfix139_34_2 Q2.hinj139_34_2
      Q2.hcardT139_34_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T139_34_2 i) (Q2.hfix139_34_2 i) _)
      colCert_139_34_2.hD ?_).symm
  rw [alnId_139 j hj]


theorem leaf_139_34_3 (hp : 3 < (Q2.transData.getD 34 []).length)
    (j : Nat) (hj : j < (repChars.getD 139 []).length)
    (hq : (normIsRep.getD 139 []).getD j false = true) :
    species (Q2.reps (⟨34, by decide⟩ : Fin 148)) (colE2 ⟨34, by decide⟩ 3 hp)
        (rowE2 (⟨139, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨34, by decide⟩ : Fin 148))
        (colE1 ⟨34, by decide⟩ 3 (transLenTr ⟨34, by decide⟩ 3 hp))
        (rowE1 (⟨139, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨139, by decide⟩ : Fin 148) ⟨34, by decide⟩ _
      (validAt ⟨139, by decide⟩ (listedAt ⟨139, by decide⟩ hj))
      (colE1 ⟨34, by decide⟩ 3 (transLenTr ⟨34, by decide⟩ 3 hp)) T139_34
      hfix139_34 hinj139_34 hcardT139_34
      (fun i => conj_mem_of_fixedPoints _ _ (T139_34 i) (hfix139_34 i) _)
      ⟨139, by decide⟩ ⟨34, by decide⟩ _
      (Q2.validAt ⟨139, by decide⟩ (Q2.listedAt ⟨139, by decide⟩
        (alnCheck_rep ⟨139, by decide⟩ hj hq).1))
      (colE2 ⟨34, by decide⟩ 3 hp) Q2.T139_34_2 Q2.hfix139_34_2 Q2.hinj139_34_2
      Q2.hcardT139_34_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T139_34_2 i) (Q2.hfix139_34_2 i) _)
      colCert_139_34_3.hD ?_).symm
  rw [alnId_139 j hj]


theorem leaf_139_34_4 (hp : 4 < (Q2.transData.getD 34 []).length)
    (j : Nat) (hj : j < (repChars.getD 139 []).length)
    (hq : (normIsRep.getD 139 []).getD j false = true) :
    species (Q2.reps (⟨34, by decide⟩ : Fin 148)) (colE2 ⟨34, by decide⟩ 4 hp)
        (rowE2 (⟨139, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨34, by decide⟩ : Fin 148))
        (colE1 ⟨34, by decide⟩ 4 (transLenTr ⟨34, by decide⟩ 4 hp))
        (rowE1 (⟨139, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨139, by decide⟩ : Fin 148) ⟨34, by decide⟩ _
      (validAt ⟨139, by decide⟩ (listedAt ⟨139, by decide⟩ hj))
      (colE1 ⟨34, by decide⟩ 4 (transLenTr ⟨34, by decide⟩ 4 hp)) T139_34
      hfix139_34 hinj139_34 hcardT139_34
      (fun i => conj_mem_of_fixedPoints _ _ (T139_34 i) (hfix139_34 i) _)
      ⟨139, by decide⟩ ⟨34, by decide⟩ _
      (Q2.validAt ⟨139, by decide⟩ (Q2.listedAt ⟨139, by decide⟩
        (alnCheck_rep ⟨139, by decide⟩ hj hq).1))
      (colE2 ⟨34, by decide⟩ 4 hp) Q2.T139_34_2 Q2.hfix139_34_2 Q2.hinj139_34_2
      Q2.hcardT139_34_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T139_34_2 i) (Q2.hfix139_34_2 i) _)
      colCert_139_34_4.hD ?_).symm
  rw [alnId_139 j hj]


theorem leaf_139_34_5 (hp : 5 < (Q2.transData.getD 34 []).length)
    (j : Nat) (hj : j < (repChars.getD 139 []).length)
    (hq : (normIsRep.getD 139 []).getD j false = true) :
    species (Q2.reps (⟨34, by decide⟩ : Fin 148)) (colE2 ⟨34, by decide⟩ 5 hp)
        (rowE2 (⟨139, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨34, by decide⟩ : Fin 148))
        (colE1 ⟨34, by decide⟩ 5 (transLenTr ⟨34, by decide⟩ 5 hp))
        (rowE1 (⟨139, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨139, by decide⟩ : Fin 148) ⟨34, by decide⟩ _
      (validAt ⟨139, by decide⟩ (listedAt ⟨139, by decide⟩ hj))
      (colE1 ⟨34, by decide⟩ 5 (transLenTr ⟨34, by decide⟩ 5 hp)) T139_34
      hfix139_34 hinj139_34 hcardT139_34
      (fun i => conj_mem_of_fixedPoints _ _ (T139_34 i) (hfix139_34 i) _)
      ⟨139, by decide⟩ ⟨34, by decide⟩ _
      (Q2.validAt ⟨139, by decide⟩ (Q2.listedAt ⟨139, by decide⟩
        (alnCheck_rep ⟨139, by decide⟩ hj hq).1))
      (colE2 ⟨34, by decide⟩ 5 hp) Q2.T139_34_2 Q2.hfix139_34_2 Q2.hinj139_34_2
      Q2.hcardT139_34_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T139_34_2 i) (Q2.hfix139_34_2 i) _)
      ?_).symm
  rw [show colData1 (⟨139, by decide⟩ : Fin 148)
        ((colE1 ⟨34, by decide⟩ 5 (transLenTr ⟨34, by decide⟩ 5 hp) : ↥(reps ⟨34, by decide⟩)) : Coordinate 1)
        T139_34 = colFn colCertDiv_139_34_5.D1 (m := 5) from colCertDiv_139_34_5.bind1,
    show colData2 (⟨139, by decide⟩ : Fin 148)
        ((colE2 ⟨34, by decide⟩ 5 hp : ↥(Q2.reps ⟨34, by decide⟩)) : Coordinate 2)
        Q2.T139_34_2 = colFn colCertDiv_139_34_5.D2 (m := 5) from colCertDiv_139_34_5.bind2]
  rw [alnId_139 j hj]
  exact fastcode_of_div ⟨139, by decide⟩ _ _ _
    ((alnId_139 j hj) ▸ Q2.listedAt (⟨139, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨139, by decide⟩ : Fin 148) hj hq).1) colCertDiv_139_34_5_match


theorem leaf_139_34_10 (hp : 10 < (Q2.transData.getD 34 []).length)
    (j : Nat) (hj : j < (repChars.getD 139 []).length)
    (hq : (normIsRep.getD 139 []).getD j false = true) :
    species (Q2.reps (⟨34, by decide⟩ : Fin 148)) (colE2 ⟨34, by decide⟩ 10 hp)
        (rowE2 (⟨139, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨34, by decide⟩ : Fin 148))
        (colE1 ⟨34, by decide⟩ 10 (transLenTr ⟨34, by decide⟩ 10 hp))
        (rowE1 (⟨139, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨139, by decide⟩ : Fin 148) ⟨34, by decide⟩ _
      (validAt ⟨139, by decide⟩ (listedAt ⟨139, by decide⟩ hj))
      (colE1 ⟨34, by decide⟩ 10 (transLenTr ⟨34, by decide⟩ 10 hp)) T139_34
      hfix139_34 hinj139_34 hcardT139_34
      (fun i => conj_mem_of_fixedPoints _ _ (T139_34 i) (hfix139_34 i) _)
      ⟨139, by decide⟩ ⟨34, by decide⟩ _
      (Q2.validAt ⟨139, by decide⟩ (Q2.listedAt ⟨139, by decide⟩
        (alnCheck_rep ⟨139, by decide⟩ hj hq).1))
      (colE2 ⟨34, by decide⟩ 10 hp) Q2.T139_34_2 Q2.hfix139_34_2 Q2.hinj139_34_2
      Q2.hcardT139_34_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T139_34_2 i) (Q2.hfix139_34_2 i) _)
      ?_).symm
  rw [show colData1 (⟨139, by decide⟩ : Fin 148)
        ((colE1 ⟨34, by decide⟩ 10 (transLenTr ⟨34, by decide⟩ 10 hp) : ↥(reps ⟨34, by decide⟩)) : Coordinate 1)
        T139_34 = colFn colCertDiv_139_34_10.D1 (m := 5) from colCertDiv_139_34_10.bind1,
    show colData2 (⟨139, by decide⟩ : Fin 148)
        ((colE2 ⟨34, by decide⟩ 10 hp : ↥(Q2.reps ⟨34, by decide⟩)) : Coordinate 2)
        Q2.T139_34_2 = colFn colCertDiv_139_34_10.D2 (m := 5) from colCertDiv_139_34_10.bind2]
  rw [alnId_139 j hj]
  exact fastcode_of_div ⟨139, by decide⟩ _ _ _
    ((alnId_139 j hj) ▸ Q2.listedAt (⟨139, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨139, by decide⟩ : Fin 148) hj hq).1) colCertDiv_139_34_10_match


theorem leaf_139_34_15 (hp : 15 < (Q2.transData.getD 34 []).length)
    (j : Nat) (hj : j < (repChars.getD 139 []).length)
    (hq : (normIsRep.getD 139 []).getD j false = true) :
    species (Q2.reps (⟨34, by decide⟩ : Fin 148)) (colE2 ⟨34, by decide⟩ 15 hp)
        (rowE2 (⟨139, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨34, by decide⟩ : Fin 148))
        (colE1 ⟨34, by decide⟩ 15 (transLenTr ⟨34, by decide⟩ 15 hp))
        (rowE1 (⟨139, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨139, by decide⟩ : Fin 148) ⟨34, by decide⟩ _
      (validAt ⟨139, by decide⟩ (listedAt ⟨139, by decide⟩ hj))
      (colE1 ⟨34, by decide⟩ 15 (transLenTr ⟨34, by decide⟩ 15 hp)) T139_34
      hfix139_34 hinj139_34 hcardT139_34
      (fun i => conj_mem_of_fixedPoints _ _ (T139_34 i) (hfix139_34 i) _)
      ⟨139, by decide⟩ ⟨34, by decide⟩ _
      (Q2.validAt ⟨139, by decide⟩ (Q2.listedAt ⟨139, by decide⟩
        (alnCheck_rep ⟨139, by decide⟩ hj hq).1))
      (colE2 ⟨34, by decide⟩ 15 hp) Q2.T139_34_2 Q2.hfix139_34_2 Q2.hinj139_34_2
      Q2.hcardT139_34_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T139_34_2 i) (Q2.hfix139_34_2 i) _)
      ?_).symm
  rw [show colData1 (⟨139, by decide⟩ : Fin 148)
        ((colE1 ⟨34, by decide⟩ 15 (transLenTr ⟨34, by decide⟩ 15 hp) : ↥(reps ⟨34, by decide⟩)) : Coordinate 1)
        T139_34 = colFn colCertDiv_139_34_15.D1 (m := 5) from colCertDiv_139_34_15.bind1,
    show colData2 (⟨139, by decide⟩ : Fin 148)
        ((colE2 ⟨34, by decide⟩ 15 hp : ↥(Q2.reps ⟨34, by decide⟩)) : Coordinate 2)
        Q2.T139_34_2 = colFn colCertDiv_139_34_15.D2 (m := 5) from colCertDiv_139_34_15.bind2]
  rw [alnId_139 j hj]
  exact fastcode_of_div ⟨139, by decide⟩ _ _ _
    ((alnId_139 j hj) ▸ Q2.listedAt (⟨139, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨139, by decide⟩ : Fin 148) hj hq).1) colCertDiv_139_34_15_match


theorem leaf_139_34_20 (hp : 20 < (Q2.transData.getD 34 []).length)
    (j : Nat) (hj : j < (repChars.getD 139 []).length)
    (hq : (normIsRep.getD 139 []).getD j false = true) :
    species (Q2.reps (⟨34, by decide⟩ : Fin 148)) (colE2 ⟨34, by decide⟩ 20 hp)
        (rowE2 (⟨139, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨34, by decide⟩ : Fin 148))
        (colE1 ⟨34, by decide⟩ 20 (transLenTr ⟨34, by decide⟩ 20 hp))
        (rowE1 (⟨139, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨139, by decide⟩ : Fin 148) ⟨34, by decide⟩ _
      (validAt ⟨139, by decide⟩ (listedAt ⟨139, by decide⟩ hj))
      (colE1 ⟨34, by decide⟩ 20 (transLenTr ⟨34, by decide⟩ 20 hp)) T139_34
      hfix139_34 hinj139_34 hcardT139_34
      (fun i => conj_mem_of_fixedPoints _ _ (T139_34 i) (hfix139_34 i) _)
      ⟨139, by decide⟩ ⟨34, by decide⟩ _
      (Q2.validAt ⟨139, by decide⟩ (Q2.listedAt ⟨139, by decide⟩
        (alnCheck_rep ⟨139, by decide⟩ hj hq).1))
      (colE2 ⟨34, by decide⟩ 20 hp) Q2.T139_34_2 Q2.hfix139_34_2 Q2.hinj139_34_2
      Q2.hcardT139_34_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T139_34_2 i) (Q2.hfix139_34_2 i) _)
      ?_).symm
  rw [show colData1 (⟨139, by decide⟩ : Fin 148)
        ((colE1 ⟨34, by decide⟩ 20 (transLenTr ⟨34, by decide⟩ 20 hp) : ↥(reps ⟨34, by decide⟩)) : Coordinate 1)
        T139_34 = colFn colCertDiv_139_34_20.D1 (m := 5) from colCertDiv_139_34_20.bind1,
    show colData2 (⟨139, by decide⟩ : Fin 148)
        ((colE2 ⟨34, by decide⟩ 20 hp : ↥(Q2.reps ⟨34, by decide⟩)) : Coordinate 2)
        Q2.T139_34_2 = colFn colCertDiv_139_34_20.D2 (m := 5) from colCertDiv_139_34_20.bind2]
  rw [alnId_139 j hj]
  exact fastcode_of_div ⟨139, by decide⟩ _ _ _
    ((alnId_139 j hj) ▸ Q2.listedAt (⟨139, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨139, by decide⟩ : Fin 148) hj hq).1) colCertDiv_139_34_20_match


theorem leaf_139_38_0 (hp : 0 < (Q2.transData.getD 38 []).length)
    (j : Nat) (hj : j < (repChars.getD 139 []).length)
    (hq : (normIsRep.getD 139 []).getD j false = true) :
    species (Q2.reps (⟨38, by decide⟩ : Fin 148)) (colE2 ⟨38, by decide⟩ 0 hp)
        (rowE2 (⟨139, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨38, by decide⟩ : Fin 148))
        (colE1 ⟨38, by decide⟩ 0 (transLenTr ⟨38, by decide⟩ 0 hp))
        (rowE1 (⟨139, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨139, by decide⟩ : Fin 148) ⟨38, by decide⟩ _
      (validAt ⟨139, by decide⟩ (listedAt ⟨139, by decide⟩ hj))
      (colE1 ⟨38, by decide⟩ 0 (transLenTr ⟨38, by decide⟩ 0 hp)) T139_38
      hfix139_38 hinj139_38 hcardT139_38
      (fun i => conj_mem_of_fixedPoints _ _ (T139_38 i) (hfix139_38 i) _)
      ⟨139, by decide⟩ ⟨38, by decide⟩ _
      (Q2.validAt ⟨139, by decide⟩ (Q2.listedAt ⟨139, by decide⟩
        (alnCheck_rep ⟨139, by decide⟩ hj hq).1))
      (colE2 ⟨38, by decide⟩ 0 hp) Q2.T139_38_2 Q2.hfix139_38_2 Q2.hinj139_38_2
      Q2.hcardT139_38_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T139_38_2 i) (Q2.hfix139_38_2 i) _)
      colCert_139_38_0.hD ?_).symm
  rw [alnId_139 j hj]


theorem leaf_139_38_1 (hp : 1 < (Q2.transData.getD 38 []).length)
    (j : Nat) (hj : j < (repChars.getD 139 []).length)
    (hq : (normIsRep.getD 139 []).getD j false = true) :
    species (Q2.reps (⟨38, by decide⟩ : Fin 148)) (colE2 ⟨38, by decide⟩ 1 hp)
        (rowE2 (⟨139, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨38, by decide⟩ : Fin 148))
        (colE1 ⟨38, by decide⟩ 1 (transLenTr ⟨38, by decide⟩ 1 hp))
        (rowE1 (⟨139, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨139, by decide⟩ : Fin 148) ⟨38, by decide⟩ _
      (validAt ⟨139, by decide⟩ (listedAt ⟨139, by decide⟩ hj))
      (colE1 ⟨38, by decide⟩ 1 (transLenTr ⟨38, by decide⟩ 1 hp)) T139_38
      hfix139_38 hinj139_38 hcardT139_38
      (fun i => conj_mem_of_fixedPoints _ _ (T139_38 i) (hfix139_38 i) _)
      ⟨139, by decide⟩ ⟨38, by decide⟩ _
      (Q2.validAt ⟨139, by decide⟩ (Q2.listedAt ⟨139, by decide⟩
        (alnCheck_rep ⟨139, by decide⟩ hj hq).1))
      (colE2 ⟨38, by decide⟩ 1 hp) Q2.T139_38_2 Q2.hfix139_38_2 Q2.hinj139_38_2
      Q2.hcardT139_38_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T139_38_2 i) (Q2.hfix139_38_2 i) _)
      colCert_139_38_1.hD ?_).symm
  rw [alnId_139 j hj]


theorem leaf_139_38_2 (hp : 2 < (Q2.transData.getD 38 []).length)
    (j : Nat) (hj : j < (repChars.getD 139 []).length)
    (hq : (normIsRep.getD 139 []).getD j false = true) :
    species (Q2.reps (⟨38, by decide⟩ : Fin 148)) (colE2 ⟨38, by decide⟩ 2 hp)
        (rowE2 (⟨139, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨38, by decide⟩ : Fin 148))
        (colE1 ⟨38, by decide⟩ 2 (transLenTr ⟨38, by decide⟩ 2 hp))
        (rowE1 (⟨139, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨139, by decide⟩ : Fin 148) ⟨38, by decide⟩ _
      (validAt ⟨139, by decide⟩ (listedAt ⟨139, by decide⟩ hj))
      (colE1 ⟨38, by decide⟩ 2 (transLenTr ⟨38, by decide⟩ 2 hp)) T139_38
      hfix139_38 hinj139_38 hcardT139_38
      (fun i => conj_mem_of_fixedPoints _ _ (T139_38 i) (hfix139_38 i) _)
      ⟨139, by decide⟩ ⟨38, by decide⟩ _
      (Q2.validAt ⟨139, by decide⟩ (Q2.listedAt ⟨139, by decide⟩
        (alnCheck_rep ⟨139, by decide⟩ hj hq).1))
      (colE2 ⟨38, by decide⟩ 2 hp) Q2.T139_38_2 Q2.hfix139_38_2 Q2.hinj139_38_2
      Q2.hcardT139_38_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T139_38_2 i) (Q2.hfix139_38_2 i) _)
      colCert_139_38_2.hD ?_).symm
  rw [alnId_139 j hj]


theorem leaf_139_38_3 (hp : 3 < (Q2.transData.getD 38 []).length)
    (j : Nat) (hj : j < (repChars.getD 139 []).length)
    (hq : (normIsRep.getD 139 []).getD j false = true) :
    species (Q2.reps (⟨38, by decide⟩ : Fin 148)) (colE2 ⟨38, by decide⟩ 3 hp)
        (rowE2 (⟨139, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨38, by decide⟩ : Fin 148))
        (colE1 ⟨38, by decide⟩ 3 (transLenTr ⟨38, by decide⟩ 3 hp))
        (rowE1 (⟨139, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨139, by decide⟩ : Fin 148) ⟨38, by decide⟩ _
      (validAt ⟨139, by decide⟩ (listedAt ⟨139, by decide⟩ hj))
      (colE1 ⟨38, by decide⟩ 3 (transLenTr ⟨38, by decide⟩ 3 hp)) T139_38
      hfix139_38 hinj139_38 hcardT139_38
      (fun i => conj_mem_of_fixedPoints _ _ (T139_38 i) (hfix139_38 i) _)
      ⟨139, by decide⟩ ⟨38, by decide⟩ _
      (Q2.validAt ⟨139, by decide⟩ (Q2.listedAt ⟨139, by decide⟩
        (alnCheck_rep ⟨139, by decide⟩ hj hq).1))
      (colE2 ⟨38, by decide⟩ 3 hp) Q2.T139_38_2 Q2.hfix139_38_2 Q2.hinj139_38_2
      Q2.hcardT139_38_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T139_38_2 i) (Q2.hfix139_38_2 i) _)
      colCert_139_38_3.hD ?_).symm
  rw [alnId_139 j hj]


theorem leaf_139_38_4 (hp : 4 < (Q2.transData.getD 38 []).length)
    (j : Nat) (hj : j < (repChars.getD 139 []).length)
    (hq : (normIsRep.getD 139 []).getD j false = true) :
    species (Q2.reps (⟨38, by decide⟩ : Fin 148)) (colE2 ⟨38, by decide⟩ 4 hp)
        (rowE2 (⟨139, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨38, by decide⟩ : Fin 148))
        (colE1 ⟨38, by decide⟩ 4 (transLenTr ⟨38, by decide⟩ 4 hp))
        (rowE1 (⟨139, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨139, by decide⟩ : Fin 148) ⟨38, by decide⟩ _
      (validAt ⟨139, by decide⟩ (listedAt ⟨139, by decide⟩ hj))
      (colE1 ⟨38, by decide⟩ 4 (transLenTr ⟨38, by decide⟩ 4 hp)) T139_38
      hfix139_38 hinj139_38 hcardT139_38
      (fun i => conj_mem_of_fixedPoints _ _ (T139_38 i) (hfix139_38 i) _)
      ⟨139, by decide⟩ ⟨38, by decide⟩ _
      (Q2.validAt ⟨139, by decide⟩ (Q2.listedAt ⟨139, by decide⟩
        (alnCheck_rep ⟨139, by decide⟩ hj hq).1))
      (colE2 ⟨38, by decide⟩ 4 hp) Q2.T139_38_2 Q2.hfix139_38_2 Q2.hinj139_38_2
      Q2.hcardT139_38_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T139_38_2 i) (Q2.hfix139_38_2 i) _)
      colCert_139_38_4.hD ?_).symm
  rw [alnId_139 j hj]


theorem leaf_139_38_5 (hp : 5 < (Q2.transData.getD 38 []).length)
    (j : Nat) (hj : j < (repChars.getD 139 []).length)
    (hq : (normIsRep.getD 139 []).getD j false = true) :
    species (Q2.reps (⟨38, by decide⟩ : Fin 148)) (colE2 ⟨38, by decide⟩ 5 hp)
        (rowE2 (⟨139, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨38, by decide⟩ : Fin 148))
        (colE1 ⟨38, by decide⟩ 5 (transLenTr ⟨38, by decide⟩ 5 hp))
        (rowE1 (⟨139, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨139, by decide⟩ : Fin 148) ⟨38, by decide⟩ _
      (validAt ⟨139, by decide⟩ (listedAt ⟨139, by decide⟩ hj))
      (colE1 ⟨38, by decide⟩ 5 (transLenTr ⟨38, by decide⟩ 5 hp)) T139_38
      hfix139_38 hinj139_38 hcardT139_38
      (fun i => conj_mem_of_fixedPoints _ _ (T139_38 i) (hfix139_38 i) _)
      ⟨139, by decide⟩ ⟨38, by decide⟩ _
      (Q2.validAt ⟨139, by decide⟩ (Q2.listedAt ⟨139, by decide⟩
        (alnCheck_rep ⟨139, by decide⟩ hj hq).1))
      (colE2 ⟨38, by decide⟩ 5 hp) Q2.T139_38_2 Q2.hfix139_38_2 Q2.hinj139_38_2
      Q2.hcardT139_38_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T139_38_2 i) (Q2.hfix139_38_2 i) _)
      ?_).symm
  rw [show colData1 (⟨139, by decide⟩ : Fin 148)
        ((colE1 ⟨38, by decide⟩ 5 (transLenTr ⟨38, by decide⟩ 5 hp) : ↥(reps ⟨38, by decide⟩)) : Coordinate 1)
        T139_38 = colFn colCertDiv_139_38_5.D1 (m := 5) from colCertDiv_139_38_5.bind1,
    show colData2 (⟨139, by decide⟩ : Fin 148)
        ((colE2 ⟨38, by decide⟩ 5 hp : ↥(Q2.reps ⟨38, by decide⟩)) : Coordinate 2)
        Q2.T139_38_2 = colFn colCertDiv_139_38_5.D2 (m := 5) from colCertDiv_139_38_5.bind2]
  rw [alnId_139 j hj]
  exact fastcode_of_div ⟨139, by decide⟩ _ _ _
    ((alnId_139 j hj) ▸ Q2.listedAt (⟨139, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨139, by decide⟩ : Fin 148) hj hq).1) colCertDiv_139_38_5_match


theorem leaf_139_38_10 (hp : 10 < (Q2.transData.getD 38 []).length)
    (j : Nat) (hj : j < (repChars.getD 139 []).length)
    (hq : (normIsRep.getD 139 []).getD j false = true) :
    species (Q2.reps (⟨38, by decide⟩ : Fin 148)) (colE2 ⟨38, by decide⟩ 10 hp)
        (rowE2 (⟨139, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨38, by decide⟩ : Fin 148))
        (colE1 ⟨38, by decide⟩ 10 (transLenTr ⟨38, by decide⟩ 10 hp))
        (rowE1 (⟨139, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨139, by decide⟩ : Fin 148) ⟨38, by decide⟩ _
      (validAt ⟨139, by decide⟩ (listedAt ⟨139, by decide⟩ hj))
      (colE1 ⟨38, by decide⟩ 10 (transLenTr ⟨38, by decide⟩ 10 hp)) T139_38
      hfix139_38 hinj139_38 hcardT139_38
      (fun i => conj_mem_of_fixedPoints _ _ (T139_38 i) (hfix139_38 i) _)
      ⟨139, by decide⟩ ⟨38, by decide⟩ _
      (Q2.validAt ⟨139, by decide⟩ (Q2.listedAt ⟨139, by decide⟩
        (alnCheck_rep ⟨139, by decide⟩ hj hq).1))
      (colE2 ⟨38, by decide⟩ 10 hp) Q2.T139_38_2 Q2.hfix139_38_2 Q2.hinj139_38_2
      Q2.hcardT139_38_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T139_38_2 i) (Q2.hfix139_38_2 i) _)
      ?_).symm
  rw [show colData1 (⟨139, by decide⟩ : Fin 148)
        ((colE1 ⟨38, by decide⟩ 10 (transLenTr ⟨38, by decide⟩ 10 hp) : ↥(reps ⟨38, by decide⟩)) : Coordinate 1)
        T139_38 = colFn colCertDiv_139_38_10.D1 (m := 5) from colCertDiv_139_38_10.bind1,
    show colData2 (⟨139, by decide⟩ : Fin 148)
        ((colE2 ⟨38, by decide⟩ 10 hp : ↥(Q2.reps ⟨38, by decide⟩)) : Coordinate 2)
        Q2.T139_38_2 = colFn colCertDiv_139_38_10.D2 (m := 5) from colCertDiv_139_38_10.bind2]
  rw [alnId_139 j hj]
  exact fastcode_of_div ⟨139, by decide⟩ _ _ _
    ((alnId_139 j hj) ▸ Q2.listedAt (⟨139, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨139, by decide⟩ : Fin 148) hj hq).1) colCertDiv_139_38_10_match


theorem leaf_139_38_15 (hp : 15 < (Q2.transData.getD 38 []).length)
    (j : Nat) (hj : j < (repChars.getD 139 []).length)
    (hq : (normIsRep.getD 139 []).getD j false = true) :
    species (Q2.reps (⟨38, by decide⟩ : Fin 148)) (colE2 ⟨38, by decide⟩ 15 hp)
        (rowE2 (⟨139, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨38, by decide⟩ : Fin 148))
        (colE1 ⟨38, by decide⟩ 15 (transLenTr ⟨38, by decide⟩ 15 hp))
        (rowE1 (⟨139, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨139, by decide⟩ : Fin 148) ⟨38, by decide⟩ _
      (validAt ⟨139, by decide⟩ (listedAt ⟨139, by decide⟩ hj))
      (colE1 ⟨38, by decide⟩ 15 (transLenTr ⟨38, by decide⟩ 15 hp)) T139_38
      hfix139_38 hinj139_38 hcardT139_38
      (fun i => conj_mem_of_fixedPoints _ _ (T139_38 i) (hfix139_38 i) _)
      ⟨139, by decide⟩ ⟨38, by decide⟩ _
      (Q2.validAt ⟨139, by decide⟩ (Q2.listedAt ⟨139, by decide⟩
        (alnCheck_rep ⟨139, by decide⟩ hj hq).1))
      (colE2 ⟨38, by decide⟩ 15 hp) Q2.T139_38_2 Q2.hfix139_38_2 Q2.hinj139_38_2
      Q2.hcardT139_38_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T139_38_2 i) (Q2.hfix139_38_2 i) _)
      ?_).symm
  rw [show colData1 (⟨139, by decide⟩ : Fin 148)
        ((colE1 ⟨38, by decide⟩ 15 (transLenTr ⟨38, by decide⟩ 15 hp) : ↥(reps ⟨38, by decide⟩)) : Coordinate 1)
        T139_38 = colFn colCertDiv_139_38_15.D1 (m := 5) from colCertDiv_139_38_15.bind1,
    show colData2 (⟨139, by decide⟩ : Fin 148)
        ((colE2 ⟨38, by decide⟩ 15 hp : ↥(Q2.reps ⟨38, by decide⟩)) : Coordinate 2)
        Q2.T139_38_2 = colFn colCertDiv_139_38_15.D2 (m := 5) from colCertDiv_139_38_15.bind2]
  rw [alnId_139 j hj]
  exact fastcode_of_div ⟨139, by decide⟩ _ _ _
    ((alnId_139 j hj) ▸ Q2.listedAt (⟨139, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨139, by decide⟩ : Fin 148) hj hq).1) colCertDiv_139_38_15_match


theorem leaf_139_38_20 (hp : 20 < (Q2.transData.getD 38 []).length)
    (j : Nat) (hj : j < (repChars.getD 139 []).length)
    (hq : (normIsRep.getD 139 []).getD j false = true) :
    species (Q2.reps (⟨38, by decide⟩ : Fin 148)) (colE2 ⟨38, by decide⟩ 20 hp)
        (rowE2 (⟨139, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨38, by decide⟩ : Fin 148))
        (colE1 ⟨38, by decide⟩ 20 (transLenTr ⟨38, by decide⟩ 20 hp))
        (rowE1 (⟨139, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨139, by decide⟩ : Fin 148) ⟨38, by decide⟩ _
      (validAt ⟨139, by decide⟩ (listedAt ⟨139, by decide⟩ hj))
      (colE1 ⟨38, by decide⟩ 20 (transLenTr ⟨38, by decide⟩ 20 hp)) T139_38
      hfix139_38 hinj139_38 hcardT139_38
      (fun i => conj_mem_of_fixedPoints _ _ (T139_38 i) (hfix139_38 i) _)
      ⟨139, by decide⟩ ⟨38, by decide⟩ _
      (Q2.validAt ⟨139, by decide⟩ (Q2.listedAt ⟨139, by decide⟩
        (alnCheck_rep ⟨139, by decide⟩ hj hq).1))
      (colE2 ⟨38, by decide⟩ 20 hp) Q2.T139_38_2 Q2.hfix139_38_2 Q2.hinj139_38_2
      Q2.hcardT139_38_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T139_38_2 i) (Q2.hfix139_38_2 i) _)
      ?_).symm
  rw [show colData1 (⟨139, by decide⟩ : Fin 148)
        ((colE1 ⟨38, by decide⟩ 20 (transLenTr ⟨38, by decide⟩ 20 hp) : ↥(reps ⟨38, by decide⟩)) : Coordinate 1)
        T139_38 = colFn colCertDiv_139_38_20.D1 (m := 5) from colCertDiv_139_38_20.bind1,
    show colData2 (⟨139, by decide⟩ : Fin 148)
        ((colE2 ⟨38, by decide⟩ 20 hp : ↥(Q2.reps ⟨38, by decide⟩)) : Coordinate 2)
        Q2.T139_38_2 = colFn colCertDiv_139_38_20.D2 (m := 5) from colCertDiv_139_38_20.bind2]
  rw [alnId_139 j hj]
  exact fastcode_of_div ⟨139, by decide⟩ _ _ _
    ((alnId_139 j hj) ▸ Q2.listedAt (⟨139, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨139, by decide⟩ : Fin 148) hj hq).1) colCertDiv_139_38_20_match


theorem leaf_139_45_0 (hp : 0 < (Q2.transData.getD 45 []).length)
    (j : Nat) (hj : j < (repChars.getD 139 []).length)
    (hq : (normIsRep.getD 139 []).getD j false = true) :
    species (Q2.reps (⟨45, by decide⟩ : Fin 148)) (colE2 ⟨45, by decide⟩ 0 hp)
        (rowE2 (⟨139, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨45, by decide⟩ : Fin 148))
        (colE1 ⟨45, by decide⟩ 0 (transLenTr ⟨45, by decide⟩ 0 hp))
        (rowE1 (⟨139, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨139, by decide⟩ : Fin 148) ⟨45, by decide⟩ _
      (validAt ⟨139, by decide⟩ (listedAt ⟨139, by decide⟩ hj))
      (colE1 ⟨45, by decide⟩ 0 (transLenTr ⟨45, by decide⟩ 0 hp)) T139_45
      hfix139_45 hinj139_45 hcardT139_45
      (fun i => conj_mem_of_fixedPoints _ _ (T139_45 i) (hfix139_45 i) _)
      ⟨139, by decide⟩ ⟨45, by decide⟩ _
      (Q2.validAt ⟨139, by decide⟩ (Q2.listedAt ⟨139, by decide⟩
        (alnCheck_rep ⟨139, by decide⟩ hj hq).1))
      (colE2 ⟨45, by decide⟩ 0 hp) Q2.T139_45_2 Q2.hfix139_45_2 Q2.hinj139_45_2
      Q2.hcardT139_45_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T139_45_2 i) (Q2.hfix139_45_2 i) _)
      colCert_139_45_0.hD ?_).symm
  rw [alnId_139 j hj]


theorem leaf_139_45_1 (hp : 1 < (Q2.transData.getD 45 []).length)
    (j : Nat) (hj : j < (repChars.getD 139 []).length)
    (hq : (normIsRep.getD 139 []).getD j false = true) :
    species (Q2.reps (⟨45, by decide⟩ : Fin 148)) (colE2 ⟨45, by decide⟩ 1 hp)
        (rowE2 (⟨139, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨45, by decide⟩ : Fin 148))
        (colE1 ⟨45, by decide⟩ 1 (transLenTr ⟨45, by decide⟩ 1 hp))
        (rowE1 (⟨139, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨139, by decide⟩ : Fin 148) ⟨45, by decide⟩ _
      (validAt ⟨139, by decide⟩ (listedAt ⟨139, by decide⟩ hj))
      (colE1 ⟨45, by decide⟩ 1 (transLenTr ⟨45, by decide⟩ 1 hp)) T139_45
      hfix139_45 hinj139_45 hcardT139_45
      (fun i => conj_mem_of_fixedPoints _ _ (T139_45 i) (hfix139_45 i) _)
      ⟨139, by decide⟩ ⟨45, by decide⟩ _
      (Q2.validAt ⟨139, by decide⟩ (Q2.listedAt ⟨139, by decide⟩
        (alnCheck_rep ⟨139, by decide⟩ hj hq).1))
      (colE2 ⟨45, by decide⟩ 1 hp) Q2.T139_45_2 Q2.hfix139_45_2 Q2.hinj139_45_2
      Q2.hcardT139_45_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T139_45_2 i) (Q2.hfix139_45_2 i) _)
      colCert_139_45_1.hD ?_).symm
  rw [alnId_139 j hj]


theorem leaf_139_45_2 (hp : 2 < (Q2.transData.getD 45 []).length)
    (j : Nat) (hj : j < (repChars.getD 139 []).length)
    (hq : (normIsRep.getD 139 []).getD j false = true) :
    species (Q2.reps (⟨45, by decide⟩ : Fin 148)) (colE2 ⟨45, by decide⟩ 2 hp)
        (rowE2 (⟨139, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨45, by decide⟩ : Fin 148))
        (colE1 ⟨45, by decide⟩ 2 (transLenTr ⟨45, by decide⟩ 2 hp))
        (rowE1 (⟨139, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨139, by decide⟩ : Fin 148) ⟨45, by decide⟩ _
      (validAt ⟨139, by decide⟩ (listedAt ⟨139, by decide⟩ hj))
      (colE1 ⟨45, by decide⟩ 2 (transLenTr ⟨45, by decide⟩ 2 hp)) T139_45
      hfix139_45 hinj139_45 hcardT139_45
      (fun i => conj_mem_of_fixedPoints _ _ (T139_45 i) (hfix139_45 i) _)
      ⟨139, by decide⟩ ⟨45, by decide⟩ _
      (Q2.validAt ⟨139, by decide⟩ (Q2.listedAt ⟨139, by decide⟩
        (alnCheck_rep ⟨139, by decide⟩ hj hq).1))
      (colE2 ⟨45, by decide⟩ 2 hp) Q2.T139_45_2 Q2.hfix139_45_2 Q2.hinj139_45_2
      Q2.hcardT139_45_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T139_45_2 i) (Q2.hfix139_45_2 i) _)
      colCert_139_45_2.hD ?_).symm
  rw [alnId_139 j hj]


theorem leaf_139_45_3 (hp : 3 < (Q2.transData.getD 45 []).length)
    (j : Nat) (hj : j < (repChars.getD 139 []).length)
    (hq : (normIsRep.getD 139 []).getD j false = true) :
    species (Q2.reps (⟨45, by decide⟩ : Fin 148)) (colE2 ⟨45, by decide⟩ 3 hp)
        (rowE2 (⟨139, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨45, by decide⟩ : Fin 148))
        (colE1 ⟨45, by decide⟩ 3 (transLenTr ⟨45, by decide⟩ 3 hp))
        (rowE1 (⟨139, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨139, by decide⟩ : Fin 148) ⟨45, by decide⟩ _
      (validAt ⟨139, by decide⟩ (listedAt ⟨139, by decide⟩ hj))
      (colE1 ⟨45, by decide⟩ 3 (transLenTr ⟨45, by decide⟩ 3 hp)) T139_45
      hfix139_45 hinj139_45 hcardT139_45
      (fun i => conj_mem_of_fixedPoints _ _ (T139_45 i) (hfix139_45 i) _)
      ⟨139, by decide⟩ ⟨45, by decide⟩ _
      (Q2.validAt ⟨139, by decide⟩ (Q2.listedAt ⟨139, by decide⟩
        (alnCheck_rep ⟨139, by decide⟩ hj hq).1))
      (colE2 ⟨45, by decide⟩ 3 hp) Q2.T139_45_2 Q2.hfix139_45_2 Q2.hinj139_45_2
      Q2.hcardT139_45_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T139_45_2 i) (Q2.hfix139_45_2 i) _)
      colCert_139_45_3.hD ?_).symm
  rw [alnId_139 j hj]


theorem leaf_139_45_4 (hp : 4 < (Q2.transData.getD 45 []).length)
    (j : Nat) (hj : j < (repChars.getD 139 []).length)
    (hq : (normIsRep.getD 139 []).getD j false = true) :
    species (Q2.reps (⟨45, by decide⟩ : Fin 148)) (colE2 ⟨45, by decide⟩ 4 hp)
        (rowE2 (⟨139, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨45, by decide⟩ : Fin 148))
        (colE1 ⟨45, by decide⟩ 4 (transLenTr ⟨45, by decide⟩ 4 hp))
        (rowE1 (⟨139, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨139, by decide⟩ : Fin 148) ⟨45, by decide⟩ _
      (validAt ⟨139, by decide⟩ (listedAt ⟨139, by decide⟩ hj))
      (colE1 ⟨45, by decide⟩ 4 (transLenTr ⟨45, by decide⟩ 4 hp)) T139_45
      hfix139_45 hinj139_45 hcardT139_45
      (fun i => conj_mem_of_fixedPoints _ _ (T139_45 i) (hfix139_45 i) _)
      ⟨139, by decide⟩ ⟨45, by decide⟩ _
      (Q2.validAt ⟨139, by decide⟩ (Q2.listedAt ⟨139, by decide⟩
        (alnCheck_rep ⟨139, by decide⟩ hj hq).1))
      (colE2 ⟨45, by decide⟩ 4 hp) Q2.T139_45_2 Q2.hfix139_45_2 Q2.hinj139_45_2
      Q2.hcardT139_45_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T139_45_2 i) (Q2.hfix139_45_2 i) _)
      colCert_139_45_4.hD ?_).symm
  rw [alnId_139 j hj]


theorem leaf_139_45_5 (hp : 5 < (Q2.transData.getD 45 []).length)
    (j : Nat) (hj : j < (repChars.getD 139 []).length)
    (hq : (normIsRep.getD 139 []).getD j false = true) :
    species (Q2.reps (⟨45, by decide⟩ : Fin 148)) (colE2 ⟨45, by decide⟩ 5 hp)
        (rowE2 (⟨139, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨45, by decide⟩ : Fin 148))
        (colE1 ⟨45, by decide⟩ 5 (transLenTr ⟨45, by decide⟩ 5 hp))
        (rowE1 (⟨139, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨139, by decide⟩ : Fin 148) ⟨45, by decide⟩ _
      (validAt ⟨139, by decide⟩ (listedAt ⟨139, by decide⟩ hj))
      (colE1 ⟨45, by decide⟩ 5 (transLenTr ⟨45, by decide⟩ 5 hp)) T139_45
      hfix139_45 hinj139_45 hcardT139_45
      (fun i => conj_mem_of_fixedPoints _ _ (T139_45 i) (hfix139_45 i) _)
      ⟨139, by decide⟩ ⟨45, by decide⟩ _
      (Q2.validAt ⟨139, by decide⟩ (Q2.listedAt ⟨139, by decide⟩
        (alnCheck_rep ⟨139, by decide⟩ hj hq).1))
      (colE2 ⟨45, by decide⟩ 5 hp) Q2.T139_45_2 Q2.hfix139_45_2 Q2.hinj139_45_2
      Q2.hcardT139_45_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T139_45_2 i) (Q2.hfix139_45_2 i) _)
      ?_).symm
  rw [show colData1 (⟨139, by decide⟩ : Fin 148)
        ((colE1 ⟨45, by decide⟩ 5 (transLenTr ⟨45, by decide⟩ 5 hp) : ↥(reps ⟨45, by decide⟩)) : Coordinate 1)
        T139_45 = colFn colCertDiv_139_45_5.D1 (m := 5) from colCertDiv_139_45_5.bind1,
    show colData2 (⟨139, by decide⟩ : Fin 148)
        ((colE2 ⟨45, by decide⟩ 5 hp : ↥(Q2.reps ⟨45, by decide⟩)) : Coordinate 2)
        Q2.T139_45_2 = colFn colCertDiv_139_45_5.D2 (m := 5) from colCertDiv_139_45_5.bind2]
  rw [alnId_139 j hj]
  exact fastcode_of_div ⟨139, by decide⟩ _ _ _
    ((alnId_139 j hj) ▸ Q2.listedAt (⟨139, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨139, by decide⟩ : Fin 148) hj hq).1) colCertDiv_139_45_5_match


theorem leaf_139_45_10 (hp : 10 < (Q2.transData.getD 45 []).length)
    (j : Nat) (hj : j < (repChars.getD 139 []).length)
    (hq : (normIsRep.getD 139 []).getD j false = true) :
    species (Q2.reps (⟨45, by decide⟩ : Fin 148)) (colE2 ⟨45, by decide⟩ 10 hp)
        (rowE2 (⟨139, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨45, by decide⟩ : Fin 148))
        (colE1 ⟨45, by decide⟩ 10 (transLenTr ⟨45, by decide⟩ 10 hp))
        (rowE1 (⟨139, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨139, by decide⟩ : Fin 148) ⟨45, by decide⟩ _
      (validAt ⟨139, by decide⟩ (listedAt ⟨139, by decide⟩ hj))
      (colE1 ⟨45, by decide⟩ 10 (transLenTr ⟨45, by decide⟩ 10 hp)) T139_45
      hfix139_45 hinj139_45 hcardT139_45
      (fun i => conj_mem_of_fixedPoints _ _ (T139_45 i) (hfix139_45 i) _)
      ⟨139, by decide⟩ ⟨45, by decide⟩ _
      (Q2.validAt ⟨139, by decide⟩ (Q2.listedAt ⟨139, by decide⟩
        (alnCheck_rep ⟨139, by decide⟩ hj hq).1))
      (colE2 ⟨45, by decide⟩ 10 hp) Q2.T139_45_2 Q2.hfix139_45_2 Q2.hinj139_45_2
      Q2.hcardT139_45_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T139_45_2 i) (Q2.hfix139_45_2 i) _)
      ?_).symm
  rw [show colData1 (⟨139, by decide⟩ : Fin 148)
        ((colE1 ⟨45, by decide⟩ 10 (transLenTr ⟨45, by decide⟩ 10 hp) : ↥(reps ⟨45, by decide⟩)) : Coordinate 1)
        T139_45 = colFn colCertDiv_139_45_10.D1 (m := 5) from colCertDiv_139_45_10.bind1,
    show colData2 (⟨139, by decide⟩ : Fin 148)
        ((colE2 ⟨45, by decide⟩ 10 hp : ↥(Q2.reps ⟨45, by decide⟩)) : Coordinate 2)
        Q2.T139_45_2 = colFn colCertDiv_139_45_10.D2 (m := 5) from colCertDiv_139_45_10.bind2]
  rw [alnId_139 j hj]
  exact fastcode_of_div ⟨139, by decide⟩ _ _ _
    ((alnId_139 j hj) ▸ Q2.listedAt (⟨139, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨139, by decide⟩ : Fin 148) hj hq).1) colCertDiv_139_45_10_match


theorem leaf_139_45_15 (hp : 15 < (Q2.transData.getD 45 []).length)
    (j : Nat) (hj : j < (repChars.getD 139 []).length)
    (hq : (normIsRep.getD 139 []).getD j false = true) :
    species (Q2.reps (⟨45, by decide⟩ : Fin 148)) (colE2 ⟨45, by decide⟩ 15 hp)
        (rowE2 (⟨139, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨45, by decide⟩ : Fin 148))
        (colE1 ⟨45, by decide⟩ 15 (transLenTr ⟨45, by decide⟩ 15 hp))
        (rowE1 (⟨139, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨139, by decide⟩ : Fin 148) ⟨45, by decide⟩ _
      (validAt ⟨139, by decide⟩ (listedAt ⟨139, by decide⟩ hj))
      (colE1 ⟨45, by decide⟩ 15 (transLenTr ⟨45, by decide⟩ 15 hp)) T139_45
      hfix139_45 hinj139_45 hcardT139_45
      (fun i => conj_mem_of_fixedPoints _ _ (T139_45 i) (hfix139_45 i) _)
      ⟨139, by decide⟩ ⟨45, by decide⟩ _
      (Q2.validAt ⟨139, by decide⟩ (Q2.listedAt ⟨139, by decide⟩
        (alnCheck_rep ⟨139, by decide⟩ hj hq).1))
      (colE2 ⟨45, by decide⟩ 15 hp) Q2.T139_45_2 Q2.hfix139_45_2 Q2.hinj139_45_2
      Q2.hcardT139_45_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T139_45_2 i) (Q2.hfix139_45_2 i) _)
      colCert_139_45_15.hD ?_).symm
  rw [alnId_139 j hj]


theorem leaf_139_45_20 (hp : 20 < (Q2.transData.getD 45 []).length)
    (j : Nat) (hj : j < (repChars.getD 139 []).length)
    (hq : (normIsRep.getD 139 []).getD j false = true) :
    species (Q2.reps (⟨45, by decide⟩ : Fin 148)) (colE2 ⟨45, by decide⟩ 20 hp)
        (rowE2 (⟨139, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨45, by decide⟩ : Fin 148))
        (colE1 ⟨45, by decide⟩ 20 (transLenTr ⟨45, by decide⟩ 20 hp))
        (rowE1 (⟨139, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨139, by decide⟩ : Fin 148) ⟨45, by decide⟩ _
      (validAt ⟨139, by decide⟩ (listedAt ⟨139, by decide⟩ hj))
      (colE1 ⟨45, by decide⟩ 20 (transLenTr ⟨45, by decide⟩ 20 hp)) T139_45
      hfix139_45 hinj139_45 hcardT139_45
      (fun i => conj_mem_of_fixedPoints _ _ (T139_45 i) (hfix139_45 i) _)
      ⟨139, by decide⟩ ⟨45, by decide⟩ _
      (Q2.validAt ⟨139, by decide⟩ (Q2.listedAt ⟨139, by decide⟩
        (alnCheck_rep ⟨139, by decide⟩ hj hq).1))
      (colE2 ⟨45, by decide⟩ 20 hp) Q2.T139_45_2 Q2.hfix139_45_2 Q2.hinj139_45_2
      Q2.hcardT139_45_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T139_45_2 i) (Q2.hfix139_45_2 i) _)
      ?_).symm
  rw [show colData1 (⟨139, by decide⟩ : Fin 148)
        ((colE1 ⟨45, by decide⟩ 20 (transLenTr ⟨45, by decide⟩ 20 hp) : ↥(reps ⟨45, by decide⟩)) : Coordinate 1)
        T139_45 = colFn colCertDiv_139_45_20.D1 (m := 5) from colCertDiv_139_45_20.bind1,
    show colData2 (⟨139, by decide⟩ : Fin 148)
        ((colE2 ⟨45, by decide⟩ 20 hp : ↥(Q2.reps ⟨45, by decide⟩)) : Coordinate 2)
        Q2.T139_45_2 = colFn colCertDiv_139_45_20.D2 (m := 5) from colCertDiv_139_45_20.bind2]
  rw [alnId_139 j hj]
  exact fastcode_of_div ⟨139, by decide⟩ _ _ _
    ((alnId_139 j hj) ▸ Q2.listedAt (⟨139, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨139, by decide⟩ : Fin 148) hj hq).1) colCertDiv_139_45_20_match


theorem leaf_139_51_0 (hp : 0 < (Q2.transData.getD 51 []).length)
    (j : Nat) (hj : j < (repChars.getD 139 []).length)
    (hq : (normIsRep.getD 139 []).getD j false = true) :
    species (Q2.reps (⟨51, by decide⟩ : Fin 148)) (colE2 ⟨51, by decide⟩ 0 hp)
        (rowE2 (⟨139, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨51, by decide⟩ : Fin 148))
        (colE1 ⟨51, by decide⟩ 0 (transLenTr ⟨51, by decide⟩ 0 hp))
        (rowE1 (⟨139, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨139, by decide⟩ : Fin 148) ⟨51, by decide⟩ _
      (validAt ⟨139, by decide⟩ (listedAt ⟨139, by decide⟩ hj))
      (colE1 ⟨51, by decide⟩ 0 (transLenTr ⟨51, by decide⟩ 0 hp)) T139_51
      hfix139_51 hinj139_51 hcardT139_51
      (fun i => conj_mem_of_fixedPoints _ _ (T139_51 i) (hfix139_51 i) _)
      ⟨139, by decide⟩ ⟨51, by decide⟩ _
      (Q2.validAt ⟨139, by decide⟩ (Q2.listedAt ⟨139, by decide⟩
        (alnCheck_rep ⟨139, by decide⟩ hj hq).1))
      (colE2 ⟨51, by decide⟩ 0 hp) Q2.T139_51_2 Q2.hfix139_51_2 Q2.hinj139_51_2
      Q2.hcardT139_51_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T139_51_2 i) (Q2.hfix139_51_2 i) _)
      colCert_139_51_0.hD ?_).symm
  rw [alnId_139 j hj]


theorem leaf_139_51_1 (hp : 1 < (Q2.transData.getD 51 []).length)
    (j : Nat) (hj : j < (repChars.getD 139 []).length)
    (hq : (normIsRep.getD 139 []).getD j false = true) :
    species (Q2.reps (⟨51, by decide⟩ : Fin 148)) (colE2 ⟨51, by decide⟩ 1 hp)
        (rowE2 (⟨139, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨51, by decide⟩ : Fin 148))
        (colE1 ⟨51, by decide⟩ 1 (transLenTr ⟨51, by decide⟩ 1 hp))
        (rowE1 (⟨139, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨139, by decide⟩ : Fin 148) ⟨51, by decide⟩ _
      (validAt ⟨139, by decide⟩ (listedAt ⟨139, by decide⟩ hj))
      (colE1 ⟨51, by decide⟩ 1 (transLenTr ⟨51, by decide⟩ 1 hp)) T139_51
      hfix139_51 hinj139_51 hcardT139_51
      (fun i => conj_mem_of_fixedPoints _ _ (T139_51 i) (hfix139_51 i) _)
      ⟨139, by decide⟩ ⟨51, by decide⟩ _
      (Q2.validAt ⟨139, by decide⟩ (Q2.listedAt ⟨139, by decide⟩
        (alnCheck_rep ⟨139, by decide⟩ hj hq).1))
      (colE2 ⟨51, by decide⟩ 1 hp) Q2.T139_51_2 Q2.hfix139_51_2 Q2.hinj139_51_2
      Q2.hcardT139_51_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T139_51_2 i) (Q2.hfix139_51_2 i) _)
      colCert_139_51_1.hD ?_).symm
  rw [alnId_139 j hj]


theorem leaf_139_51_2 (hp : 2 < (Q2.transData.getD 51 []).length)
    (j : Nat) (hj : j < (repChars.getD 139 []).length)
    (hq : (normIsRep.getD 139 []).getD j false = true) :
    species (Q2.reps (⟨51, by decide⟩ : Fin 148)) (colE2 ⟨51, by decide⟩ 2 hp)
        (rowE2 (⟨139, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨51, by decide⟩ : Fin 148))
        (colE1 ⟨51, by decide⟩ 2 (transLenTr ⟨51, by decide⟩ 2 hp))
        (rowE1 (⟨139, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨139, by decide⟩ : Fin 148) ⟨51, by decide⟩ _
      (validAt ⟨139, by decide⟩ (listedAt ⟨139, by decide⟩ hj))
      (colE1 ⟨51, by decide⟩ 2 (transLenTr ⟨51, by decide⟩ 2 hp)) T139_51
      hfix139_51 hinj139_51 hcardT139_51
      (fun i => conj_mem_of_fixedPoints _ _ (T139_51 i) (hfix139_51 i) _)
      ⟨139, by decide⟩ ⟨51, by decide⟩ _
      (Q2.validAt ⟨139, by decide⟩ (Q2.listedAt ⟨139, by decide⟩
        (alnCheck_rep ⟨139, by decide⟩ hj hq).1))
      (colE2 ⟨51, by decide⟩ 2 hp) Q2.T139_51_2 Q2.hfix139_51_2 Q2.hinj139_51_2
      Q2.hcardT139_51_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T139_51_2 i) (Q2.hfix139_51_2 i) _)
      colCert_139_51_2.hD ?_).symm
  rw [alnId_139 j hj]


theorem leaf_139_51_3 (hp : 3 < (Q2.transData.getD 51 []).length)
    (j : Nat) (hj : j < (repChars.getD 139 []).length)
    (hq : (normIsRep.getD 139 []).getD j false = true) :
    species (Q2.reps (⟨51, by decide⟩ : Fin 148)) (colE2 ⟨51, by decide⟩ 3 hp)
        (rowE2 (⟨139, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨51, by decide⟩ : Fin 148))
        (colE1 ⟨51, by decide⟩ 3 (transLenTr ⟨51, by decide⟩ 3 hp))
        (rowE1 (⟨139, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨139, by decide⟩ : Fin 148) ⟨51, by decide⟩ _
      (validAt ⟨139, by decide⟩ (listedAt ⟨139, by decide⟩ hj))
      (colE1 ⟨51, by decide⟩ 3 (transLenTr ⟨51, by decide⟩ 3 hp)) T139_51
      hfix139_51 hinj139_51 hcardT139_51
      (fun i => conj_mem_of_fixedPoints _ _ (T139_51 i) (hfix139_51 i) _)
      ⟨139, by decide⟩ ⟨51, by decide⟩ _
      (Q2.validAt ⟨139, by decide⟩ (Q2.listedAt ⟨139, by decide⟩
        (alnCheck_rep ⟨139, by decide⟩ hj hq).1))
      (colE2 ⟨51, by decide⟩ 3 hp) Q2.T139_51_2 Q2.hfix139_51_2 Q2.hinj139_51_2
      Q2.hcardT139_51_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T139_51_2 i) (Q2.hfix139_51_2 i) _)
      colCert_139_51_3.hD ?_).symm
  rw [alnId_139 j hj]


theorem leaf_139_51_4 (hp : 4 < (Q2.transData.getD 51 []).length)
    (j : Nat) (hj : j < (repChars.getD 139 []).length)
    (hq : (normIsRep.getD 139 []).getD j false = true) :
    species (Q2.reps (⟨51, by decide⟩ : Fin 148)) (colE2 ⟨51, by decide⟩ 4 hp)
        (rowE2 (⟨139, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨51, by decide⟩ : Fin 148))
        (colE1 ⟨51, by decide⟩ 4 (transLenTr ⟨51, by decide⟩ 4 hp))
        (rowE1 (⟨139, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨139, by decide⟩ : Fin 148) ⟨51, by decide⟩ _
      (validAt ⟨139, by decide⟩ (listedAt ⟨139, by decide⟩ hj))
      (colE1 ⟨51, by decide⟩ 4 (transLenTr ⟨51, by decide⟩ 4 hp)) T139_51
      hfix139_51 hinj139_51 hcardT139_51
      (fun i => conj_mem_of_fixedPoints _ _ (T139_51 i) (hfix139_51 i) _)
      ⟨139, by decide⟩ ⟨51, by decide⟩ _
      (Q2.validAt ⟨139, by decide⟩ (Q2.listedAt ⟨139, by decide⟩
        (alnCheck_rep ⟨139, by decide⟩ hj hq).1))
      (colE2 ⟨51, by decide⟩ 4 hp) Q2.T139_51_2 Q2.hfix139_51_2 Q2.hinj139_51_2
      Q2.hcardT139_51_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T139_51_2 i) (Q2.hfix139_51_2 i) _)
      colCert_139_51_4.hD ?_).symm
  rw [alnId_139 j hj]


theorem leaf_139_51_5 (hp : 5 < (Q2.transData.getD 51 []).length)
    (j : Nat) (hj : j < (repChars.getD 139 []).length)
    (hq : (normIsRep.getD 139 []).getD j false = true) :
    species (Q2.reps (⟨51, by decide⟩ : Fin 148)) (colE2 ⟨51, by decide⟩ 5 hp)
        (rowE2 (⟨139, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨51, by decide⟩ : Fin 148))
        (colE1 ⟨51, by decide⟩ 5 (transLenTr ⟨51, by decide⟩ 5 hp))
        (rowE1 (⟨139, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨139, by decide⟩ : Fin 148) ⟨51, by decide⟩ _
      (validAt ⟨139, by decide⟩ (listedAt ⟨139, by decide⟩ hj))
      (colE1 ⟨51, by decide⟩ 5 (transLenTr ⟨51, by decide⟩ 5 hp)) T139_51
      hfix139_51 hinj139_51 hcardT139_51
      (fun i => conj_mem_of_fixedPoints _ _ (T139_51 i) (hfix139_51 i) _)
      ⟨139, by decide⟩ ⟨51, by decide⟩ _
      (Q2.validAt ⟨139, by decide⟩ (Q2.listedAt ⟨139, by decide⟩
        (alnCheck_rep ⟨139, by decide⟩ hj hq).1))
      (colE2 ⟨51, by decide⟩ 5 hp) Q2.T139_51_2 Q2.hfix139_51_2 Q2.hinj139_51_2
      Q2.hcardT139_51_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T139_51_2 i) (Q2.hfix139_51_2 i) _)
      ?_).symm
  rw [show colData1 (⟨139, by decide⟩ : Fin 148)
        ((colE1 ⟨51, by decide⟩ 5 (transLenTr ⟨51, by decide⟩ 5 hp) : ↥(reps ⟨51, by decide⟩)) : Coordinate 1)
        T139_51 = colFn colCertDiv_139_51_5.D1 (m := 5) from colCertDiv_139_51_5.bind1,
    show colData2 (⟨139, by decide⟩ : Fin 148)
        ((colE2 ⟨51, by decide⟩ 5 hp : ↥(Q2.reps ⟨51, by decide⟩)) : Coordinate 2)
        Q2.T139_51_2 = colFn colCertDiv_139_51_5.D2 (m := 5) from colCertDiv_139_51_5.bind2]
  rw [alnId_139 j hj]
  exact fastcode_of_div ⟨139, by decide⟩ _ _ _
    ((alnId_139 j hj) ▸ Q2.listedAt (⟨139, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨139, by decide⟩ : Fin 148) hj hq).1) colCertDiv_139_51_5_match


theorem leaf_139_51_10 (hp : 10 < (Q2.transData.getD 51 []).length)
    (j : Nat) (hj : j < (repChars.getD 139 []).length)
    (hq : (normIsRep.getD 139 []).getD j false = true) :
    species (Q2.reps (⟨51, by decide⟩ : Fin 148)) (colE2 ⟨51, by decide⟩ 10 hp)
        (rowE2 (⟨139, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨51, by decide⟩ : Fin 148))
        (colE1 ⟨51, by decide⟩ 10 (transLenTr ⟨51, by decide⟩ 10 hp))
        (rowE1 (⟨139, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨139, by decide⟩ : Fin 148) ⟨51, by decide⟩ _
      (validAt ⟨139, by decide⟩ (listedAt ⟨139, by decide⟩ hj))
      (colE1 ⟨51, by decide⟩ 10 (transLenTr ⟨51, by decide⟩ 10 hp)) T139_51
      hfix139_51 hinj139_51 hcardT139_51
      (fun i => conj_mem_of_fixedPoints _ _ (T139_51 i) (hfix139_51 i) _)
      ⟨139, by decide⟩ ⟨51, by decide⟩ _
      (Q2.validAt ⟨139, by decide⟩ (Q2.listedAt ⟨139, by decide⟩
        (alnCheck_rep ⟨139, by decide⟩ hj hq).1))
      (colE2 ⟨51, by decide⟩ 10 hp) Q2.T139_51_2 Q2.hfix139_51_2 Q2.hinj139_51_2
      Q2.hcardT139_51_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T139_51_2 i) (Q2.hfix139_51_2 i) _)
      ?_).symm
  rw [show colData1 (⟨139, by decide⟩ : Fin 148)
        ((colE1 ⟨51, by decide⟩ 10 (transLenTr ⟨51, by decide⟩ 10 hp) : ↥(reps ⟨51, by decide⟩)) : Coordinate 1)
        T139_51 = colFn colCertDiv_139_51_10.D1 (m := 5) from colCertDiv_139_51_10.bind1,
    show colData2 (⟨139, by decide⟩ : Fin 148)
        ((colE2 ⟨51, by decide⟩ 10 hp : ↥(Q2.reps ⟨51, by decide⟩)) : Coordinate 2)
        Q2.T139_51_2 = colFn colCertDiv_139_51_10.D2 (m := 5) from colCertDiv_139_51_10.bind2]
  rw [alnId_139 j hj]
  exact fastcode_of_div ⟨139, by decide⟩ _ _ _
    ((alnId_139 j hj) ▸ Q2.listedAt (⟨139, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨139, by decide⟩ : Fin 148) hj hq).1) colCertDiv_139_51_10_match


theorem leaf_139_51_15 (hp : 15 < (Q2.transData.getD 51 []).length)
    (j : Nat) (hj : j < (repChars.getD 139 []).length)
    (hq : (normIsRep.getD 139 []).getD j false = true) :
    species (Q2.reps (⟨51, by decide⟩ : Fin 148)) (colE2 ⟨51, by decide⟩ 15 hp)
        (rowE2 (⟨139, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨51, by decide⟩ : Fin 148))
        (colE1 ⟨51, by decide⟩ 15 (transLenTr ⟨51, by decide⟩ 15 hp))
        (rowE1 (⟨139, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨139, by decide⟩ : Fin 148) ⟨51, by decide⟩ _
      (validAt ⟨139, by decide⟩ (listedAt ⟨139, by decide⟩ hj))
      (colE1 ⟨51, by decide⟩ 15 (transLenTr ⟨51, by decide⟩ 15 hp)) T139_51
      hfix139_51 hinj139_51 hcardT139_51
      (fun i => conj_mem_of_fixedPoints _ _ (T139_51 i) (hfix139_51 i) _)
      ⟨139, by decide⟩ ⟨51, by decide⟩ _
      (Q2.validAt ⟨139, by decide⟩ (Q2.listedAt ⟨139, by decide⟩
        (alnCheck_rep ⟨139, by decide⟩ hj hq).1))
      (colE2 ⟨51, by decide⟩ 15 hp) Q2.T139_51_2 Q2.hfix139_51_2 Q2.hinj139_51_2
      Q2.hcardT139_51_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T139_51_2 i) (Q2.hfix139_51_2 i) _)
      ?_).symm
  rw [show colData1 (⟨139, by decide⟩ : Fin 148)
        ((colE1 ⟨51, by decide⟩ 15 (transLenTr ⟨51, by decide⟩ 15 hp) : ↥(reps ⟨51, by decide⟩)) : Coordinate 1)
        T139_51 = colFn colCertDiv_139_51_15.D1 (m := 5) from colCertDiv_139_51_15.bind1,
    show colData2 (⟨139, by decide⟩ : Fin 148)
        ((colE2 ⟨51, by decide⟩ 15 hp : ↥(Q2.reps ⟨51, by decide⟩)) : Coordinate 2)
        Q2.T139_51_2 = colFn colCertDiv_139_51_15.D2 (m := 5) from colCertDiv_139_51_15.bind2]
  rw [alnId_139 j hj]
  exact fastcode_of_div ⟨139, by decide⟩ _ _ _
    ((alnId_139 j hj) ▸ Q2.listedAt (⟨139, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨139, by decide⟩ : Fin 148) hj hq).1) colCertDiv_139_51_15_match


theorem leaf_139_51_20 (hp : 20 < (Q2.transData.getD 51 []).length)
    (j : Nat) (hj : j < (repChars.getD 139 []).length)
    (hq : (normIsRep.getD 139 []).getD j false = true) :
    species (Q2.reps (⟨51, by decide⟩ : Fin 148)) (colE2 ⟨51, by decide⟩ 20 hp)
        (rowE2 (⟨139, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨51, by decide⟩ : Fin 148))
        (colE1 ⟨51, by decide⟩ 20 (transLenTr ⟨51, by decide⟩ 20 hp))
        (rowE1 (⟨139, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨139, by decide⟩ : Fin 148) ⟨51, by decide⟩ _
      (validAt ⟨139, by decide⟩ (listedAt ⟨139, by decide⟩ hj))
      (colE1 ⟨51, by decide⟩ 20 (transLenTr ⟨51, by decide⟩ 20 hp)) T139_51
      hfix139_51 hinj139_51 hcardT139_51
      (fun i => conj_mem_of_fixedPoints _ _ (T139_51 i) (hfix139_51 i) _)
      ⟨139, by decide⟩ ⟨51, by decide⟩ _
      (Q2.validAt ⟨139, by decide⟩ (Q2.listedAt ⟨139, by decide⟩
        (alnCheck_rep ⟨139, by decide⟩ hj hq).1))
      (colE2 ⟨51, by decide⟩ 20 hp) Q2.T139_51_2 Q2.hfix139_51_2 Q2.hinj139_51_2
      Q2.hcardT139_51_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T139_51_2 i) (Q2.hfix139_51_2 i) _)
      ?_).symm
  rw [show colData1 (⟨139, by decide⟩ : Fin 148)
        ((colE1 ⟨51, by decide⟩ 20 (transLenTr ⟨51, by decide⟩ 20 hp) : ↥(reps ⟨51, by decide⟩)) : Coordinate 1)
        T139_51 = colFn colCertDiv_139_51_20.D1 (m := 5) from colCertDiv_139_51_20.bind1,
    show colData2 (⟨139, by decide⟩ : Fin 148)
        ((colE2 ⟨51, by decide⟩ 20 hp : ↥(Q2.reps ⟨51, by decide⟩)) : Coordinate 2)
        Q2.T139_51_2 = colFn colCertDiv_139_51_20.D2 (m := 5) from colCertDiv_139_51_20.bind2]
  rw [alnId_139 j hj]
  exact fastcode_of_div ⟨139, by decide⟩ _ _ _
    ((alnId_139 j hj) ▸ Q2.listedAt (⟨139, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨139, by decide⟩ : Fin 148) hj hq).1) colCertDiv_139_51_20_match


theorem leaf_139_53_0 (hp : 0 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 139 []).length)
    (hq : (normIsRep.getD 139 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 0 hp)
        (rowE2 (⟨139, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 0 (transLenTr ⟨53, by decide⟩ 0 hp))
        (rowE1 (⟨139, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨139, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨139, by decide⟩ (listedAt ⟨139, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 0 (transLenTr ⟨53, by decide⟩ 0 hp)) T139_53
      hfix139_53 hinj139_53 hcardT139_53
      (fun i => conj_mem_of_fixedPoints _ _ (T139_53 i) (hfix139_53 i) _)
      ⟨139, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨139, by decide⟩ (Q2.listedAt ⟨139, by decide⟩
        (alnCheck_rep ⟨139, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 0 hp) Q2.T139_53_2 Q2.hfix139_53_2 Q2.hinj139_53_2
      Q2.hcardT139_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T139_53_2 i) (Q2.hfix139_53_2 i) _)
      colCert_139_53_0.hD ?_).symm
  rw [alnId_139 j hj]


theorem leaf_139_53_1 (hp : 1 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 139 []).length)
    (hq : (normIsRep.getD 139 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 1 hp)
        (rowE2 (⟨139, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 1 (transLenTr ⟨53, by decide⟩ 1 hp))
        (rowE1 (⟨139, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨139, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨139, by decide⟩ (listedAt ⟨139, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 1 (transLenTr ⟨53, by decide⟩ 1 hp)) T139_53
      hfix139_53 hinj139_53 hcardT139_53
      (fun i => conj_mem_of_fixedPoints _ _ (T139_53 i) (hfix139_53 i) _)
      ⟨139, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨139, by decide⟩ (Q2.listedAt ⟨139, by decide⟩
        (alnCheck_rep ⟨139, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 1 hp) Q2.T139_53_2 Q2.hfix139_53_2 Q2.hinj139_53_2
      Q2.hcardT139_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T139_53_2 i) (Q2.hfix139_53_2 i) _)
      colCert_139_53_1.hD ?_).symm
  rw [alnId_139 j hj]


theorem leaf_139_53_2 (hp : 2 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 139 []).length)
    (hq : (normIsRep.getD 139 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 2 hp)
        (rowE2 (⟨139, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 2 (transLenTr ⟨53, by decide⟩ 2 hp))
        (rowE1 (⟨139, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨139, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨139, by decide⟩ (listedAt ⟨139, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 2 (transLenTr ⟨53, by decide⟩ 2 hp)) T139_53
      hfix139_53 hinj139_53 hcardT139_53
      (fun i => conj_mem_of_fixedPoints _ _ (T139_53 i) (hfix139_53 i) _)
      ⟨139, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨139, by decide⟩ (Q2.listedAt ⟨139, by decide⟩
        (alnCheck_rep ⟨139, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 2 hp) Q2.T139_53_2 Q2.hfix139_53_2 Q2.hinj139_53_2
      Q2.hcardT139_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T139_53_2 i) (Q2.hfix139_53_2 i) _)
      colCert_139_53_2.hD ?_).symm
  rw [alnId_139 j hj]


theorem leaf_139_53_3 (hp : 3 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 139 []).length)
    (hq : (normIsRep.getD 139 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 3 hp)
        (rowE2 (⟨139, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 3 (transLenTr ⟨53, by decide⟩ 3 hp))
        (rowE1 (⟨139, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨139, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨139, by decide⟩ (listedAt ⟨139, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 3 (transLenTr ⟨53, by decide⟩ 3 hp)) T139_53
      hfix139_53 hinj139_53 hcardT139_53
      (fun i => conj_mem_of_fixedPoints _ _ (T139_53 i) (hfix139_53 i) _)
      ⟨139, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨139, by decide⟩ (Q2.listedAt ⟨139, by decide⟩
        (alnCheck_rep ⟨139, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 3 hp) Q2.T139_53_2 Q2.hfix139_53_2 Q2.hinj139_53_2
      Q2.hcardT139_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T139_53_2 i) (Q2.hfix139_53_2 i) _)
      colCert_139_53_3.hD ?_).symm
  rw [alnId_139 j hj]


theorem leaf_139_53_4 (hp : 4 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 139 []).length)
    (hq : (normIsRep.getD 139 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 4 hp)
        (rowE2 (⟨139, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 4 (transLenTr ⟨53, by decide⟩ 4 hp))
        (rowE1 (⟨139, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨139, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨139, by decide⟩ (listedAt ⟨139, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 4 (transLenTr ⟨53, by decide⟩ 4 hp)) T139_53
      hfix139_53 hinj139_53 hcardT139_53
      (fun i => conj_mem_of_fixedPoints _ _ (T139_53 i) (hfix139_53 i) _)
      ⟨139, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨139, by decide⟩ (Q2.listedAt ⟨139, by decide⟩
        (alnCheck_rep ⟨139, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 4 hp) Q2.T139_53_2 Q2.hfix139_53_2 Q2.hinj139_53_2
      Q2.hcardT139_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T139_53_2 i) (Q2.hfix139_53_2 i) _)
      colCert_139_53_4.hD ?_).symm
  rw [alnId_139 j hj]


theorem leaf_139_53_5 (hp : 5 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 139 []).length)
    (hq : (normIsRep.getD 139 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 5 hp)
        (rowE2 (⟨139, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 5 (transLenTr ⟨53, by decide⟩ 5 hp))
        (rowE1 (⟨139, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨139, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨139, by decide⟩ (listedAt ⟨139, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 5 (transLenTr ⟨53, by decide⟩ 5 hp)) T139_53
      hfix139_53 hinj139_53 hcardT139_53
      (fun i => conj_mem_of_fixedPoints _ _ (T139_53 i) (hfix139_53 i) _)
      ⟨139, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨139, by decide⟩ (Q2.listedAt ⟨139, by decide⟩
        (alnCheck_rep ⟨139, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 5 hp) Q2.T139_53_2 Q2.hfix139_53_2 Q2.hinj139_53_2
      Q2.hcardT139_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T139_53_2 i) (Q2.hfix139_53_2 i) _)
      colCert_139_53_5.hD ?_).symm
  rw [alnId_139 j hj]


theorem leaf_139_53_10 (hp : 10 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 139 []).length)
    (hq : (normIsRep.getD 139 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 10 hp)
        (rowE2 (⟨139, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 10 (transLenTr ⟨53, by decide⟩ 10 hp))
        (rowE1 (⟨139, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨139, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨139, by decide⟩ (listedAt ⟨139, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 10 (transLenTr ⟨53, by decide⟩ 10 hp)) T139_53
      hfix139_53 hinj139_53 hcardT139_53
      (fun i => conj_mem_of_fixedPoints _ _ (T139_53 i) (hfix139_53 i) _)
      ⟨139, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨139, by decide⟩ (Q2.listedAt ⟨139, by decide⟩
        (alnCheck_rep ⟨139, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 10 hp) Q2.T139_53_2 Q2.hfix139_53_2 Q2.hinj139_53_2
      Q2.hcardT139_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T139_53_2 i) (Q2.hfix139_53_2 i) _)
      colCert_139_53_10.hD ?_).symm
  rw [alnId_139 j hj]


theorem leaf_139_53_15 (hp : 15 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 139 []).length)
    (hq : (normIsRep.getD 139 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 15 hp)
        (rowE2 (⟨139, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 15 (transLenTr ⟨53, by decide⟩ 15 hp))
        (rowE1 (⟨139, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨139, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨139, by decide⟩ (listedAt ⟨139, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 15 (transLenTr ⟨53, by decide⟩ 15 hp)) T139_53
      hfix139_53 hinj139_53 hcardT139_53
      (fun i => conj_mem_of_fixedPoints _ _ (T139_53 i) (hfix139_53 i) _)
      ⟨139, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨139, by decide⟩ (Q2.listedAt ⟨139, by decide⟩
        (alnCheck_rep ⟨139, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 15 hp) Q2.T139_53_2 Q2.hfix139_53_2 Q2.hinj139_53_2
      Q2.hcardT139_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T139_53_2 i) (Q2.hfix139_53_2 i) _)
      colCert_139_53_15.hD ?_).symm
  rw [alnId_139 j hj]


theorem leaf_139_53_20 (hp : 20 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 139 []).length)
    (hq : (normIsRep.getD 139 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 20 hp)
        (rowE2 (⟨139, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 20 (transLenTr ⟨53, by decide⟩ 20 hp))
        (rowE1 (⟨139, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨139, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨139, by decide⟩ (listedAt ⟨139, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 20 (transLenTr ⟨53, by decide⟩ 20 hp)) T139_53
      hfix139_53 hinj139_53 hcardT139_53
      (fun i => conj_mem_of_fixedPoints _ _ (T139_53 i) (hfix139_53 i) _)
      ⟨139, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨139, by decide⟩ (Q2.listedAt ⟨139, by decide⟩
        (alnCheck_rep ⟨139, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 20 hp) Q2.T139_53_2 Q2.hfix139_53_2 Q2.hinj139_53_2
      Q2.hcardT139_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T139_53_2 i) (Q2.hfix139_53_2 i) _)
      colCert_139_53_20.hD ?_).symm
  rw [alnId_139 j hj]


theorem leaf_139_84_0 (hp : 0 < (Q2.transData.getD 84 []).length)
    (j : Nat) (hj : j < (repChars.getD 139 []).length)
    (hq : (normIsRep.getD 139 []).getD j false = true) :
    species (Q2.reps (⟨84, by decide⟩ : Fin 148)) (colE2 ⟨84, by decide⟩ 0 hp)
        (rowE2 (⟨139, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨84, by decide⟩ : Fin 148))
        (colE1 ⟨84, by decide⟩ 0 (transLenTr ⟨84, by decide⟩ 0 hp))
        (rowE1 (⟨139, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨139, by decide⟩ : Fin 148) ⟨84, by decide⟩ _
      (validAt ⟨139, by decide⟩ (listedAt ⟨139, by decide⟩ hj))
      (colE1 ⟨84, by decide⟩ 0 (transLenTr ⟨84, by decide⟩ 0 hp)) T139_84
      hfix139_84 hinj139_84 hcardT139_84
      (fun i => conj_mem_of_fixedPoints _ _ (T139_84 i) (hfix139_84 i) _)
      ⟨139, by decide⟩ ⟨84, by decide⟩ _
      (Q2.validAt ⟨139, by decide⟩ (Q2.listedAt ⟨139, by decide⟩
        (alnCheck_rep ⟨139, by decide⟩ hj hq).1))
      (colE2 ⟨84, by decide⟩ 0 hp) Q2.T139_84_2 Q2.hfix139_84_2 Q2.hinj139_84_2
      Q2.hcardT139_84_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T139_84_2 i) (Q2.hfix139_84_2 i) _)
      colCert_139_84_0.hD ?_).symm
  rw [alnId_139 j hj]


theorem leaf_139_84_1 (hp : 1 < (Q2.transData.getD 84 []).length)
    (j : Nat) (hj : j < (repChars.getD 139 []).length)
    (hq : (normIsRep.getD 139 []).getD j false = true) :
    species (Q2.reps (⟨84, by decide⟩ : Fin 148)) (colE2 ⟨84, by decide⟩ 1 hp)
        (rowE2 (⟨139, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨84, by decide⟩ : Fin 148))
        (colE1 ⟨84, by decide⟩ 1 (transLenTr ⟨84, by decide⟩ 1 hp))
        (rowE1 (⟨139, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨139, by decide⟩ : Fin 148) ⟨84, by decide⟩ _
      (validAt ⟨139, by decide⟩ (listedAt ⟨139, by decide⟩ hj))
      (colE1 ⟨84, by decide⟩ 1 (transLenTr ⟨84, by decide⟩ 1 hp)) T139_84
      hfix139_84 hinj139_84 hcardT139_84
      (fun i => conj_mem_of_fixedPoints _ _ (T139_84 i) (hfix139_84 i) _)
      ⟨139, by decide⟩ ⟨84, by decide⟩ _
      (Q2.validAt ⟨139, by decide⟩ (Q2.listedAt ⟨139, by decide⟩
        (alnCheck_rep ⟨139, by decide⟩ hj hq).1))
      (colE2 ⟨84, by decide⟩ 1 hp) Q2.T139_84_2 Q2.hfix139_84_2 Q2.hinj139_84_2
      Q2.hcardT139_84_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T139_84_2 i) (Q2.hfix139_84_2 i) _)
      colCert_139_84_1.hD ?_).symm
  rw [alnId_139 j hj]


theorem leaf_139_84_2 (hp : 2 < (Q2.transData.getD 84 []).length)
    (j : Nat) (hj : j < (repChars.getD 139 []).length)
    (hq : (normIsRep.getD 139 []).getD j false = true) :
    species (Q2.reps (⟨84, by decide⟩ : Fin 148)) (colE2 ⟨84, by decide⟩ 2 hp)
        (rowE2 (⟨139, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨84, by decide⟩ : Fin 148))
        (colE1 ⟨84, by decide⟩ 2 (transLenTr ⟨84, by decide⟩ 2 hp))
        (rowE1 (⟨139, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨139, by decide⟩ : Fin 148) ⟨84, by decide⟩ _
      (validAt ⟨139, by decide⟩ (listedAt ⟨139, by decide⟩ hj))
      (colE1 ⟨84, by decide⟩ 2 (transLenTr ⟨84, by decide⟩ 2 hp)) T139_84
      hfix139_84 hinj139_84 hcardT139_84
      (fun i => conj_mem_of_fixedPoints _ _ (T139_84 i) (hfix139_84 i) _)
      ⟨139, by decide⟩ ⟨84, by decide⟩ _
      (Q2.validAt ⟨139, by decide⟩ (Q2.listedAt ⟨139, by decide⟩
        (alnCheck_rep ⟨139, by decide⟩ hj hq).1))
      (colE2 ⟨84, by decide⟩ 2 hp) Q2.T139_84_2 Q2.hfix139_84_2 Q2.hinj139_84_2
      Q2.hcardT139_84_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T139_84_2 i) (Q2.hfix139_84_2 i) _)
      colCert_139_84_2.hD ?_).symm
  rw [alnId_139 j hj]


theorem leaf_139_84_3 (hp : 3 < (Q2.transData.getD 84 []).length)
    (j : Nat) (hj : j < (repChars.getD 139 []).length)
    (hq : (normIsRep.getD 139 []).getD j false = true) :
    species (Q2.reps (⟨84, by decide⟩ : Fin 148)) (colE2 ⟨84, by decide⟩ 3 hp)
        (rowE2 (⟨139, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨84, by decide⟩ : Fin 148))
        (colE1 ⟨84, by decide⟩ 3 (transLenTr ⟨84, by decide⟩ 3 hp))
        (rowE1 (⟨139, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨139, by decide⟩ : Fin 148) ⟨84, by decide⟩ _
      (validAt ⟨139, by decide⟩ (listedAt ⟨139, by decide⟩ hj))
      (colE1 ⟨84, by decide⟩ 3 (transLenTr ⟨84, by decide⟩ 3 hp)) T139_84
      hfix139_84 hinj139_84 hcardT139_84
      (fun i => conj_mem_of_fixedPoints _ _ (T139_84 i) (hfix139_84 i) _)
      ⟨139, by decide⟩ ⟨84, by decide⟩ _
      (Q2.validAt ⟨139, by decide⟩ (Q2.listedAt ⟨139, by decide⟩
        (alnCheck_rep ⟨139, by decide⟩ hj hq).1))
      (colE2 ⟨84, by decide⟩ 3 hp) Q2.T139_84_2 Q2.hfix139_84_2 Q2.hinj139_84_2
      Q2.hcardT139_84_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T139_84_2 i) (Q2.hfix139_84_2 i) _)
      colCert_139_84_3.hD ?_).symm
  rw [alnId_139 j hj]


theorem leaf_139_84_4 (hp : 4 < (Q2.transData.getD 84 []).length)
    (j : Nat) (hj : j < (repChars.getD 139 []).length)
    (hq : (normIsRep.getD 139 []).getD j false = true) :
    species (Q2.reps (⟨84, by decide⟩ : Fin 148)) (colE2 ⟨84, by decide⟩ 4 hp)
        (rowE2 (⟨139, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨84, by decide⟩ : Fin 148))
        (colE1 ⟨84, by decide⟩ 4 (transLenTr ⟨84, by decide⟩ 4 hp))
        (rowE1 (⟨139, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨139, by decide⟩ : Fin 148) ⟨84, by decide⟩ _
      (validAt ⟨139, by decide⟩ (listedAt ⟨139, by decide⟩ hj))
      (colE1 ⟨84, by decide⟩ 4 (transLenTr ⟨84, by decide⟩ 4 hp)) T139_84
      hfix139_84 hinj139_84 hcardT139_84
      (fun i => conj_mem_of_fixedPoints _ _ (T139_84 i) (hfix139_84 i) _)
      ⟨139, by decide⟩ ⟨84, by decide⟩ _
      (Q2.validAt ⟨139, by decide⟩ (Q2.listedAt ⟨139, by decide⟩
        (alnCheck_rep ⟨139, by decide⟩ hj hq).1))
      (colE2 ⟨84, by decide⟩ 4 hp) Q2.T139_84_2 Q2.hfix139_84_2 Q2.hinj139_84_2
      Q2.hcardT139_84_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T139_84_2 i) (Q2.hfix139_84_2 i) _)
      colCert_139_84_4.hD ?_).symm
  rw [alnId_139 j hj]


theorem leaf_139_84_5 (hp : 5 < (Q2.transData.getD 84 []).length)
    (j : Nat) (hj : j < (repChars.getD 139 []).length)
    (hq : (normIsRep.getD 139 []).getD j false = true) :
    species (Q2.reps (⟨84, by decide⟩ : Fin 148)) (colE2 ⟨84, by decide⟩ 5 hp)
        (rowE2 (⟨139, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨84, by decide⟩ : Fin 148))
        (colE1 ⟨84, by decide⟩ 5 (transLenTr ⟨84, by decide⟩ 5 hp))
        (rowE1 (⟨139, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨139, by decide⟩ : Fin 148) ⟨84, by decide⟩ _
      (validAt ⟨139, by decide⟩ (listedAt ⟨139, by decide⟩ hj))
      (colE1 ⟨84, by decide⟩ 5 (transLenTr ⟨84, by decide⟩ 5 hp)) T139_84
      hfix139_84 hinj139_84 hcardT139_84
      (fun i => conj_mem_of_fixedPoints _ _ (T139_84 i) (hfix139_84 i) _)
      ⟨139, by decide⟩ ⟨84, by decide⟩ _
      (Q2.validAt ⟨139, by decide⟩ (Q2.listedAt ⟨139, by decide⟩
        (alnCheck_rep ⟨139, by decide⟩ hj hq).1))
      (colE2 ⟨84, by decide⟩ 5 hp) Q2.T139_84_2 Q2.hfix139_84_2 Q2.hinj139_84_2
      Q2.hcardT139_84_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T139_84_2 i) (Q2.hfix139_84_2 i) _)
      ?_).symm
  rw [show colData1 (⟨139, by decide⟩ : Fin 148)
        ((colE1 ⟨84, by decide⟩ 5 (transLenTr ⟨84, by decide⟩ 5 hp) : ↥(reps ⟨84, by decide⟩)) : Coordinate 1)
        T139_84 = colFn colCertDiv_139_84_5.D1 (m := 5) from colCertDiv_139_84_5.bind1,
    show colData2 (⟨139, by decide⟩ : Fin 148)
        ((colE2 ⟨84, by decide⟩ 5 hp : ↥(Q2.reps ⟨84, by decide⟩)) : Coordinate 2)
        Q2.T139_84_2 = colFn colCertDiv_139_84_5.D2 (m := 5) from colCertDiv_139_84_5.bind2]
  rw [alnId_139 j hj]
  exact fastcode_of_div ⟨139, by decide⟩ _ _ _
    ((alnId_139 j hj) ▸ Q2.listedAt (⟨139, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨139, by decide⟩ : Fin 148) hj hq).1) colCertDiv_139_84_5_match


theorem leaf_139_84_10 (hp : 10 < (Q2.transData.getD 84 []).length)
    (j : Nat) (hj : j < (repChars.getD 139 []).length)
    (hq : (normIsRep.getD 139 []).getD j false = true) :
    species (Q2.reps (⟨84, by decide⟩ : Fin 148)) (colE2 ⟨84, by decide⟩ 10 hp)
        (rowE2 (⟨139, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨84, by decide⟩ : Fin 148))
        (colE1 ⟨84, by decide⟩ 10 (transLenTr ⟨84, by decide⟩ 10 hp))
        (rowE1 (⟨139, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨139, by decide⟩ : Fin 148) ⟨84, by decide⟩ _
      (validAt ⟨139, by decide⟩ (listedAt ⟨139, by decide⟩ hj))
      (colE1 ⟨84, by decide⟩ 10 (transLenTr ⟨84, by decide⟩ 10 hp)) T139_84
      hfix139_84 hinj139_84 hcardT139_84
      (fun i => conj_mem_of_fixedPoints _ _ (T139_84 i) (hfix139_84 i) _)
      ⟨139, by decide⟩ ⟨84, by decide⟩ _
      (Q2.validAt ⟨139, by decide⟩ (Q2.listedAt ⟨139, by decide⟩
        (alnCheck_rep ⟨139, by decide⟩ hj hq).1))
      (colE2 ⟨84, by decide⟩ 10 hp) Q2.T139_84_2 Q2.hfix139_84_2 Q2.hinj139_84_2
      Q2.hcardT139_84_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T139_84_2 i) (Q2.hfix139_84_2 i) _)
      ?_).symm
  rw [show colData1 (⟨139, by decide⟩ : Fin 148)
        ((colE1 ⟨84, by decide⟩ 10 (transLenTr ⟨84, by decide⟩ 10 hp) : ↥(reps ⟨84, by decide⟩)) : Coordinate 1)
        T139_84 = colFn colCertDiv_139_84_10.D1 (m := 5) from colCertDiv_139_84_10.bind1,
    show colData2 (⟨139, by decide⟩ : Fin 148)
        ((colE2 ⟨84, by decide⟩ 10 hp : ↥(Q2.reps ⟨84, by decide⟩)) : Coordinate 2)
        Q2.T139_84_2 = colFn colCertDiv_139_84_10.D2 (m := 5) from colCertDiv_139_84_10.bind2]
  rw [alnId_139 j hj]
  exact fastcode_of_div ⟨139, by decide⟩ _ _ _
    ((alnId_139 j hj) ▸ Q2.listedAt (⟨139, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨139, by decide⟩ : Fin 148) hj hq).1) colCertDiv_139_84_10_match


theorem leaf_139_84_15 (hp : 15 < (Q2.transData.getD 84 []).length)
    (j : Nat) (hj : j < (repChars.getD 139 []).length)
    (hq : (normIsRep.getD 139 []).getD j false = true) :
    species (Q2.reps (⟨84, by decide⟩ : Fin 148)) (colE2 ⟨84, by decide⟩ 15 hp)
        (rowE2 (⟨139, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨84, by decide⟩ : Fin 148))
        (colE1 ⟨84, by decide⟩ 15 (transLenTr ⟨84, by decide⟩ 15 hp))
        (rowE1 (⟨139, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨139, by decide⟩ : Fin 148) ⟨84, by decide⟩ _
      (validAt ⟨139, by decide⟩ (listedAt ⟨139, by decide⟩ hj))
      (colE1 ⟨84, by decide⟩ 15 (transLenTr ⟨84, by decide⟩ 15 hp)) T139_84
      hfix139_84 hinj139_84 hcardT139_84
      (fun i => conj_mem_of_fixedPoints _ _ (T139_84 i) (hfix139_84 i) _)
      ⟨139, by decide⟩ ⟨84, by decide⟩ _
      (Q2.validAt ⟨139, by decide⟩ (Q2.listedAt ⟨139, by decide⟩
        (alnCheck_rep ⟨139, by decide⟩ hj hq).1))
      (colE2 ⟨84, by decide⟩ 15 hp) Q2.T139_84_2 Q2.hfix139_84_2 Q2.hinj139_84_2
      Q2.hcardT139_84_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T139_84_2 i) (Q2.hfix139_84_2 i) _)
      ?_).symm
  rw [show colData1 (⟨139, by decide⟩ : Fin 148)
        ((colE1 ⟨84, by decide⟩ 15 (transLenTr ⟨84, by decide⟩ 15 hp) : ↥(reps ⟨84, by decide⟩)) : Coordinate 1)
        T139_84 = colFn colCertDiv_139_84_15.D1 (m := 5) from colCertDiv_139_84_15.bind1,
    show colData2 (⟨139, by decide⟩ : Fin 148)
        ((colE2 ⟨84, by decide⟩ 15 hp : ↥(Q2.reps ⟨84, by decide⟩)) : Coordinate 2)
        Q2.T139_84_2 = colFn colCertDiv_139_84_15.D2 (m := 5) from colCertDiv_139_84_15.bind2]
  rw [alnId_139 j hj]
  exact fastcode_of_div ⟨139, by decide⟩ _ _ _
    ((alnId_139 j hj) ▸ Q2.listedAt (⟨139, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨139, by decide⟩ : Fin 148) hj hq).1) colCertDiv_139_84_15_match


theorem leaf_139_84_20 (hp : 20 < (Q2.transData.getD 84 []).length)
    (j : Nat) (hj : j < (repChars.getD 139 []).length)
    (hq : (normIsRep.getD 139 []).getD j false = true) :
    species (Q2.reps (⟨84, by decide⟩ : Fin 148)) (colE2 ⟨84, by decide⟩ 20 hp)
        (rowE2 (⟨139, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨84, by decide⟩ : Fin 148))
        (colE1 ⟨84, by decide⟩ 20 (transLenTr ⟨84, by decide⟩ 20 hp))
        (rowE1 (⟨139, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨139, by decide⟩ : Fin 148) ⟨84, by decide⟩ _
      (validAt ⟨139, by decide⟩ (listedAt ⟨139, by decide⟩ hj))
      (colE1 ⟨84, by decide⟩ 20 (transLenTr ⟨84, by decide⟩ 20 hp)) T139_84
      hfix139_84 hinj139_84 hcardT139_84
      (fun i => conj_mem_of_fixedPoints _ _ (T139_84 i) (hfix139_84 i) _)
      ⟨139, by decide⟩ ⟨84, by decide⟩ _
      (Q2.validAt ⟨139, by decide⟩ (Q2.listedAt ⟨139, by decide⟩
        (alnCheck_rep ⟨139, by decide⟩ hj hq).1))
      (colE2 ⟨84, by decide⟩ 20 hp) Q2.T139_84_2 Q2.hfix139_84_2 Q2.hinj139_84_2
      Q2.hcardT139_84_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T139_84_2 i) (Q2.hfix139_84_2 i) _)
      ?_).symm
  rw [show colData1 (⟨139, by decide⟩ : Fin 148)
        ((colE1 ⟨84, by decide⟩ 20 (transLenTr ⟨84, by decide⟩ 20 hp) : ↥(reps ⟨84, by decide⟩)) : Coordinate 1)
        T139_84 = colFn colCertDiv_139_84_20.D1 (m := 5) from colCertDiv_139_84_20.bind1,
    show colData2 (⟨139, by decide⟩ : Fin 148)
        ((colE2 ⟨84, by decide⟩ 20 hp : ↥(Q2.reps ⟨84, by decide⟩)) : Coordinate 2)
        Q2.T139_84_2 = colFn colCertDiv_139_84_20.D2 (m := 5) from colCertDiv_139_84_20.bind2]
  rw [alnId_139 j hj]
  exact fastcode_of_div ⟨139, by decide⟩ _ _ _
    ((alnId_139 j hj) ▸ Q2.listedAt (⟨139, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨139, by decide⟩ : Fin 148) hj hq).1) colCertDiv_139_84_20_match


theorem leaf_139_94_0 (hp : 0 < (Q2.transData.getD 94 []).length)
    (j : Nat) (hj : j < (repChars.getD 139 []).length)
    (hq : (normIsRep.getD 139 []).getD j false = true) :
    species (Q2.reps (⟨94, by decide⟩ : Fin 148)) (colE2 ⟨94, by decide⟩ 0 hp)
        (rowE2 (⟨139, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨94, by decide⟩ : Fin 148))
        (colE1 ⟨94, by decide⟩ 0 (transLenTr ⟨94, by decide⟩ 0 hp))
        (rowE1 (⟨139, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨139, by decide⟩ : Fin 148) ⟨94, by decide⟩ _
      (validAt ⟨139, by decide⟩ (listedAt ⟨139, by decide⟩ hj))
      (colE1 ⟨94, by decide⟩ 0 (transLenTr ⟨94, by decide⟩ 0 hp)) T139_94
      hfix139_94 hinj139_94 hcardT139_94
      (fun i => conj_mem_of_fixedPoints _ _ (T139_94 i) (hfix139_94 i) _)
      ⟨139, by decide⟩ ⟨94, by decide⟩ _
      (Q2.validAt ⟨139, by decide⟩ (Q2.listedAt ⟨139, by decide⟩
        (alnCheck_rep ⟨139, by decide⟩ hj hq).1))
      (colE2 ⟨94, by decide⟩ 0 hp) Q2.T139_94_2 Q2.hfix139_94_2 Q2.hinj139_94_2
      Q2.hcardT139_94_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T139_94_2 i) (Q2.hfix139_94_2 i) _)
      colCert_139_94_0.hD ?_).symm
  rw [alnId_139 j hj]


theorem leaf_139_94_1 (hp : 1 < (Q2.transData.getD 94 []).length)
    (j : Nat) (hj : j < (repChars.getD 139 []).length)
    (hq : (normIsRep.getD 139 []).getD j false = true) :
    species (Q2.reps (⟨94, by decide⟩ : Fin 148)) (colE2 ⟨94, by decide⟩ 1 hp)
        (rowE2 (⟨139, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨94, by decide⟩ : Fin 148))
        (colE1 ⟨94, by decide⟩ 1 (transLenTr ⟨94, by decide⟩ 1 hp))
        (rowE1 (⟨139, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨139, by decide⟩ : Fin 148) ⟨94, by decide⟩ _
      (validAt ⟨139, by decide⟩ (listedAt ⟨139, by decide⟩ hj))
      (colE1 ⟨94, by decide⟩ 1 (transLenTr ⟨94, by decide⟩ 1 hp)) T139_94
      hfix139_94 hinj139_94 hcardT139_94
      (fun i => conj_mem_of_fixedPoints _ _ (T139_94 i) (hfix139_94 i) _)
      ⟨139, by decide⟩ ⟨94, by decide⟩ _
      (Q2.validAt ⟨139, by decide⟩ (Q2.listedAt ⟨139, by decide⟩
        (alnCheck_rep ⟨139, by decide⟩ hj hq).1))
      (colE2 ⟨94, by decide⟩ 1 hp) Q2.T139_94_2 Q2.hfix139_94_2 Q2.hinj139_94_2
      Q2.hcardT139_94_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T139_94_2 i) (Q2.hfix139_94_2 i) _)
      colCert_139_94_1.hD ?_).symm
  rw [alnId_139 j hj]


theorem leaf_139_94_2 (hp : 2 < (Q2.transData.getD 94 []).length)
    (j : Nat) (hj : j < (repChars.getD 139 []).length)
    (hq : (normIsRep.getD 139 []).getD j false = true) :
    species (Q2.reps (⟨94, by decide⟩ : Fin 148)) (colE2 ⟨94, by decide⟩ 2 hp)
        (rowE2 (⟨139, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨94, by decide⟩ : Fin 148))
        (colE1 ⟨94, by decide⟩ 2 (transLenTr ⟨94, by decide⟩ 2 hp))
        (rowE1 (⟨139, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨139, by decide⟩ : Fin 148) ⟨94, by decide⟩ _
      (validAt ⟨139, by decide⟩ (listedAt ⟨139, by decide⟩ hj))
      (colE1 ⟨94, by decide⟩ 2 (transLenTr ⟨94, by decide⟩ 2 hp)) T139_94
      hfix139_94 hinj139_94 hcardT139_94
      (fun i => conj_mem_of_fixedPoints _ _ (T139_94 i) (hfix139_94 i) _)
      ⟨139, by decide⟩ ⟨94, by decide⟩ _
      (Q2.validAt ⟨139, by decide⟩ (Q2.listedAt ⟨139, by decide⟩
        (alnCheck_rep ⟨139, by decide⟩ hj hq).1))
      (colE2 ⟨94, by decide⟩ 2 hp) Q2.T139_94_2 Q2.hfix139_94_2 Q2.hinj139_94_2
      Q2.hcardT139_94_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T139_94_2 i) (Q2.hfix139_94_2 i) _)
      colCert_139_94_2.hD ?_).symm
  rw [alnId_139 j hj]


theorem leaf_139_94_3 (hp : 3 < (Q2.transData.getD 94 []).length)
    (j : Nat) (hj : j < (repChars.getD 139 []).length)
    (hq : (normIsRep.getD 139 []).getD j false = true) :
    species (Q2.reps (⟨94, by decide⟩ : Fin 148)) (colE2 ⟨94, by decide⟩ 3 hp)
        (rowE2 (⟨139, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨94, by decide⟩ : Fin 148))
        (colE1 ⟨94, by decide⟩ 3 (transLenTr ⟨94, by decide⟩ 3 hp))
        (rowE1 (⟨139, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨139, by decide⟩ : Fin 148) ⟨94, by decide⟩ _
      (validAt ⟨139, by decide⟩ (listedAt ⟨139, by decide⟩ hj))
      (colE1 ⟨94, by decide⟩ 3 (transLenTr ⟨94, by decide⟩ 3 hp)) T139_94
      hfix139_94 hinj139_94 hcardT139_94
      (fun i => conj_mem_of_fixedPoints _ _ (T139_94 i) (hfix139_94 i) _)
      ⟨139, by decide⟩ ⟨94, by decide⟩ _
      (Q2.validAt ⟨139, by decide⟩ (Q2.listedAt ⟨139, by decide⟩
        (alnCheck_rep ⟨139, by decide⟩ hj hq).1))
      (colE2 ⟨94, by decide⟩ 3 hp) Q2.T139_94_2 Q2.hfix139_94_2 Q2.hinj139_94_2
      Q2.hcardT139_94_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T139_94_2 i) (Q2.hfix139_94_2 i) _)
      colCert_139_94_3.hD ?_).symm
  rw [alnId_139 j hj]


theorem leaf_139_94_4 (hp : 4 < (Q2.transData.getD 94 []).length)
    (j : Nat) (hj : j < (repChars.getD 139 []).length)
    (hq : (normIsRep.getD 139 []).getD j false = true) :
    species (Q2.reps (⟨94, by decide⟩ : Fin 148)) (colE2 ⟨94, by decide⟩ 4 hp)
        (rowE2 (⟨139, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨94, by decide⟩ : Fin 148))
        (colE1 ⟨94, by decide⟩ 4 (transLenTr ⟨94, by decide⟩ 4 hp))
        (rowE1 (⟨139, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨139, by decide⟩ : Fin 148) ⟨94, by decide⟩ _
      (validAt ⟨139, by decide⟩ (listedAt ⟨139, by decide⟩ hj))
      (colE1 ⟨94, by decide⟩ 4 (transLenTr ⟨94, by decide⟩ 4 hp)) T139_94
      hfix139_94 hinj139_94 hcardT139_94
      (fun i => conj_mem_of_fixedPoints _ _ (T139_94 i) (hfix139_94 i) _)
      ⟨139, by decide⟩ ⟨94, by decide⟩ _
      (Q2.validAt ⟨139, by decide⟩ (Q2.listedAt ⟨139, by decide⟩
        (alnCheck_rep ⟨139, by decide⟩ hj hq).1))
      (colE2 ⟨94, by decide⟩ 4 hp) Q2.T139_94_2 Q2.hfix139_94_2 Q2.hinj139_94_2
      Q2.hcardT139_94_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T139_94_2 i) (Q2.hfix139_94_2 i) _)
      colCert_139_94_4.hD ?_).symm
  rw [alnId_139 j hj]


theorem leaf_139_94_5 (hp : 5 < (Q2.transData.getD 94 []).length)
    (j : Nat) (hj : j < (repChars.getD 139 []).length)
    (hq : (normIsRep.getD 139 []).getD j false = true) :
    species (Q2.reps (⟨94, by decide⟩ : Fin 148)) (colE2 ⟨94, by decide⟩ 5 hp)
        (rowE2 (⟨139, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨94, by decide⟩ : Fin 148))
        (colE1 ⟨94, by decide⟩ 5 (transLenTr ⟨94, by decide⟩ 5 hp))
        (rowE1 (⟨139, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨139, by decide⟩ : Fin 148) ⟨94, by decide⟩ _
      (validAt ⟨139, by decide⟩ (listedAt ⟨139, by decide⟩ hj))
      (colE1 ⟨94, by decide⟩ 5 (transLenTr ⟨94, by decide⟩ 5 hp)) T139_94
      hfix139_94 hinj139_94 hcardT139_94
      (fun i => conj_mem_of_fixedPoints _ _ (T139_94 i) (hfix139_94 i) _)
      ⟨139, by decide⟩ ⟨94, by decide⟩ _
      (Q2.validAt ⟨139, by decide⟩ (Q2.listedAt ⟨139, by decide⟩
        (alnCheck_rep ⟨139, by decide⟩ hj hq).1))
      (colE2 ⟨94, by decide⟩ 5 hp) Q2.T139_94_2 Q2.hfix139_94_2 Q2.hinj139_94_2
      Q2.hcardT139_94_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T139_94_2 i) (Q2.hfix139_94_2 i) _)
      ?_).symm
  rw [show colData1 (⟨139, by decide⟩ : Fin 148)
        ((colE1 ⟨94, by decide⟩ 5 (transLenTr ⟨94, by decide⟩ 5 hp) : ↥(reps ⟨94, by decide⟩)) : Coordinate 1)
        T139_94 = colFn colCertDiv_139_94_5.D1 (m := 5) from colCertDiv_139_94_5.bind1,
    show colData2 (⟨139, by decide⟩ : Fin 148)
        ((colE2 ⟨94, by decide⟩ 5 hp : ↥(Q2.reps ⟨94, by decide⟩)) : Coordinate 2)
        Q2.T139_94_2 = colFn colCertDiv_139_94_5.D2 (m := 5) from colCertDiv_139_94_5.bind2]
  rw [alnId_139 j hj]
  exact fastcode_of_div ⟨139, by decide⟩ _ _ _
    ((alnId_139 j hj) ▸ Q2.listedAt (⟨139, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨139, by decide⟩ : Fin 148) hj hq).1) colCertDiv_139_94_5_match


theorem leaf_139_94_10 (hp : 10 < (Q2.transData.getD 94 []).length)
    (j : Nat) (hj : j < (repChars.getD 139 []).length)
    (hq : (normIsRep.getD 139 []).getD j false = true) :
    species (Q2.reps (⟨94, by decide⟩ : Fin 148)) (colE2 ⟨94, by decide⟩ 10 hp)
        (rowE2 (⟨139, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨94, by decide⟩ : Fin 148))
        (colE1 ⟨94, by decide⟩ 10 (transLenTr ⟨94, by decide⟩ 10 hp))
        (rowE1 (⟨139, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨139, by decide⟩ : Fin 148) ⟨94, by decide⟩ _
      (validAt ⟨139, by decide⟩ (listedAt ⟨139, by decide⟩ hj))
      (colE1 ⟨94, by decide⟩ 10 (transLenTr ⟨94, by decide⟩ 10 hp)) T139_94
      hfix139_94 hinj139_94 hcardT139_94
      (fun i => conj_mem_of_fixedPoints _ _ (T139_94 i) (hfix139_94 i) _)
      ⟨139, by decide⟩ ⟨94, by decide⟩ _
      (Q2.validAt ⟨139, by decide⟩ (Q2.listedAt ⟨139, by decide⟩
        (alnCheck_rep ⟨139, by decide⟩ hj hq).1))
      (colE2 ⟨94, by decide⟩ 10 hp) Q2.T139_94_2 Q2.hfix139_94_2 Q2.hinj139_94_2
      Q2.hcardT139_94_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T139_94_2 i) (Q2.hfix139_94_2 i) _)
      ?_).symm
  rw [show colData1 (⟨139, by decide⟩ : Fin 148)
        ((colE1 ⟨94, by decide⟩ 10 (transLenTr ⟨94, by decide⟩ 10 hp) : ↥(reps ⟨94, by decide⟩)) : Coordinate 1)
        T139_94 = colFn colCertDiv_139_94_10.D1 (m := 5) from colCertDiv_139_94_10.bind1,
    show colData2 (⟨139, by decide⟩ : Fin 148)
        ((colE2 ⟨94, by decide⟩ 10 hp : ↥(Q2.reps ⟨94, by decide⟩)) : Coordinate 2)
        Q2.T139_94_2 = colFn colCertDiv_139_94_10.D2 (m := 5) from colCertDiv_139_94_10.bind2]
  rw [alnId_139 j hj]
  exact fastcode_of_div ⟨139, by decide⟩ _ _ _
    ((alnId_139 j hj) ▸ Q2.listedAt (⟨139, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨139, by decide⟩ : Fin 148) hj hq).1) colCertDiv_139_94_10_match


theorem leaf_139_94_15 (hp : 15 < (Q2.transData.getD 94 []).length)
    (j : Nat) (hj : j < (repChars.getD 139 []).length)
    (hq : (normIsRep.getD 139 []).getD j false = true) :
    species (Q2.reps (⟨94, by decide⟩ : Fin 148)) (colE2 ⟨94, by decide⟩ 15 hp)
        (rowE2 (⟨139, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨94, by decide⟩ : Fin 148))
        (colE1 ⟨94, by decide⟩ 15 (transLenTr ⟨94, by decide⟩ 15 hp))
        (rowE1 (⟨139, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨139, by decide⟩ : Fin 148) ⟨94, by decide⟩ _
      (validAt ⟨139, by decide⟩ (listedAt ⟨139, by decide⟩ hj))
      (colE1 ⟨94, by decide⟩ 15 (transLenTr ⟨94, by decide⟩ 15 hp)) T139_94
      hfix139_94 hinj139_94 hcardT139_94
      (fun i => conj_mem_of_fixedPoints _ _ (T139_94 i) (hfix139_94 i) _)
      ⟨139, by decide⟩ ⟨94, by decide⟩ _
      (Q2.validAt ⟨139, by decide⟩ (Q2.listedAt ⟨139, by decide⟩
        (alnCheck_rep ⟨139, by decide⟩ hj hq).1))
      (colE2 ⟨94, by decide⟩ 15 hp) Q2.T139_94_2 Q2.hfix139_94_2 Q2.hinj139_94_2
      Q2.hcardT139_94_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T139_94_2 i) (Q2.hfix139_94_2 i) _)
      ?_).symm
  rw [show colData1 (⟨139, by decide⟩ : Fin 148)
        ((colE1 ⟨94, by decide⟩ 15 (transLenTr ⟨94, by decide⟩ 15 hp) : ↥(reps ⟨94, by decide⟩)) : Coordinate 1)
        T139_94 = colFn colCertDiv_139_94_15.D1 (m := 5) from colCertDiv_139_94_15.bind1,
    show colData2 (⟨139, by decide⟩ : Fin 148)
        ((colE2 ⟨94, by decide⟩ 15 hp : ↥(Q2.reps ⟨94, by decide⟩)) : Coordinate 2)
        Q2.T139_94_2 = colFn colCertDiv_139_94_15.D2 (m := 5) from colCertDiv_139_94_15.bind2]
  rw [alnId_139 j hj]
  exact fastcode_of_div ⟨139, by decide⟩ _ _ _
    ((alnId_139 j hj) ▸ Q2.listedAt (⟨139, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨139, by decide⟩ : Fin 148) hj hq).1) colCertDiv_139_94_15_match


theorem leaf_139_94_20 (hp : 20 < (Q2.transData.getD 94 []).length)
    (j : Nat) (hj : j < (repChars.getD 139 []).length)
    (hq : (normIsRep.getD 139 []).getD j false = true) :
    species (Q2.reps (⟨94, by decide⟩ : Fin 148)) (colE2 ⟨94, by decide⟩ 20 hp)
        (rowE2 (⟨139, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨94, by decide⟩ : Fin 148))
        (colE1 ⟨94, by decide⟩ 20 (transLenTr ⟨94, by decide⟩ 20 hp))
        (rowE1 (⟨139, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨139, by decide⟩ : Fin 148) ⟨94, by decide⟩ _
      (validAt ⟨139, by decide⟩ (listedAt ⟨139, by decide⟩ hj))
      (colE1 ⟨94, by decide⟩ 20 (transLenTr ⟨94, by decide⟩ 20 hp)) T139_94
      hfix139_94 hinj139_94 hcardT139_94
      (fun i => conj_mem_of_fixedPoints _ _ (T139_94 i) (hfix139_94 i) _)
      ⟨139, by decide⟩ ⟨94, by decide⟩ _
      (Q2.validAt ⟨139, by decide⟩ (Q2.listedAt ⟨139, by decide⟩
        (alnCheck_rep ⟨139, by decide⟩ hj hq).1))
      (colE2 ⟨94, by decide⟩ 20 hp) Q2.T139_94_2 Q2.hfix139_94_2 Q2.hinj139_94_2
      Q2.hcardT139_94_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T139_94_2 i) (Q2.hfix139_94_2 i) _)
      ?_).symm
  rw [show colData1 (⟨139, by decide⟩ : Fin 148)
        ((colE1 ⟨94, by decide⟩ 20 (transLenTr ⟨94, by decide⟩ 20 hp) : ↥(reps ⟨94, by decide⟩)) : Coordinate 1)
        T139_94 = colFn colCertDiv_139_94_20.D1 (m := 5) from colCertDiv_139_94_20.bind1,
    show colData2 (⟨139, by decide⟩ : Fin 148)
        ((colE2 ⟨94, by decide⟩ 20 hp : ↥(Q2.reps ⟨94, by decide⟩)) : Coordinate 2)
        Q2.T139_94_2 = colFn colCertDiv_139_94_20.D2 (m := 5) from colCertDiv_139_94_20.bind2]
  rw [alnId_139 j hj]
  exact fastcode_of_div ⟨139, by decide⟩ _ _ _
    ((alnId_139 j hj) ▸ Q2.listedAt (⟨139, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨139, by decide⟩ : Fin 148) hj hq).1) colCertDiv_139_94_20_match


theorem leaf_139_96_0 (hp : 0 < (Q2.transData.getD 96 []).length)
    (j : Nat) (hj : j < (repChars.getD 139 []).length)
    (hq : (normIsRep.getD 139 []).getD j false = true) :
    species (Q2.reps (⟨96, by decide⟩ : Fin 148)) (colE2 ⟨96, by decide⟩ 0 hp)
        (rowE2 (⟨139, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨96, by decide⟩ : Fin 148))
        (colE1 ⟨96, by decide⟩ 0 (transLenTr ⟨96, by decide⟩ 0 hp))
        (rowE1 (⟨139, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨139, by decide⟩ : Fin 148) ⟨96, by decide⟩ _
      (validAt ⟨139, by decide⟩ (listedAt ⟨139, by decide⟩ hj))
      (colE1 ⟨96, by decide⟩ 0 (transLenTr ⟨96, by decide⟩ 0 hp)) T139_96
      hfix139_96 hinj139_96 hcardT139_96
      (fun i => conj_mem_of_fixedPoints _ _ (T139_96 i) (hfix139_96 i) _)
      ⟨139, by decide⟩ ⟨96, by decide⟩ _
      (Q2.validAt ⟨139, by decide⟩ (Q2.listedAt ⟨139, by decide⟩
        (alnCheck_rep ⟨139, by decide⟩ hj hq).1))
      (colE2 ⟨96, by decide⟩ 0 hp) Q2.T139_96_2 Q2.hfix139_96_2 Q2.hinj139_96_2
      Q2.hcardT139_96_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T139_96_2 i) (Q2.hfix139_96_2 i) _)
      colCert_139_96_0.hD ?_).symm
  rw [alnId_139 j hj]


theorem leaf_139_96_1 (hp : 1 < (Q2.transData.getD 96 []).length)
    (j : Nat) (hj : j < (repChars.getD 139 []).length)
    (hq : (normIsRep.getD 139 []).getD j false = true) :
    species (Q2.reps (⟨96, by decide⟩ : Fin 148)) (colE2 ⟨96, by decide⟩ 1 hp)
        (rowE2 (⟨139, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨96, by decide⟩ : Fin 148))
        (colE1 ⟨96, by decide⟩ 1 (transLenTr ⟨96, by decide⟩ 1 hp))
        (rowE1 (⟨139, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨139, by decide⟩ : Fin 148) ⟨96, by decide⟩ _
      (validAt ⟨139, by decide⟩ (listedAt ⟨139, by decide⟩ hj))
      (colE1 ⟨96, by decide⟩ 1 (transLenTr ⟨96, by decide⟩ 1 hp)) T139_96
      hfix139_96 hinj139_96 hcardT139_96
      (fun i => conj_mem_of_fixedPoints _ _ (T139_96 i) (hfix139_96 i) _)
      ⟨139, by decide⟩ ⟨96, by decide⟩ _
      (Q2.validAt ⟨139, by decide⟩ (Q2.listedAt ⟨139, by decide⟩
        (alnCheck_rep ⟨139, by decide⟩ hj hq).1))
      (colE2 ⟨96, by decide⟩ 1 hp) Q2.T139_96_2 Q2.hfix139_96_2 Q2.hinj139_96_2
      Q2.hcardT139_96_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T139_96_2 i) (Q2.hfix139_96_2 i) _)
      colCert_139_96_1.hD ?_).symm
  rw [alnId_139 j hj]


theorem leaf_139_96_2 (hp : 2 < (Q2.transData.getD 96 []).length)
    (j : Nat) (hj : j < (repChars.getD 139 []).length)
    (hq : (normIsRep.getD 139 []).getD j false = true) :
    species (Q2.reps (⟨96, by decide⟩ : Fin 148)) (colE2 ⟨96, by decide⟩ 2 hp)
        (rowE2 (⟨139, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨96, by decide⟩ : Fin 148))
        (colE1 ⟨96, by decide⟩ 2 (transLenTr ⟨96, by decide⟩ 2 hp))
        (rowE1 (⟨139, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨139, by decide⟩ : Fin 148) ⟨96, by decide⟩ _
      (validAt ⟨139, by decide⟩ (listedAt ⟨139, by decide⟩ hj))
      (colE1 ⟨96, by decide⟩ 2 (transLenTr ⟨96, by decide⟩ 2 hp)) T139_96
      hfix139_96 hinj139_96 hcardT139_96
      (fun i => conj_mem_of_fixedPoints _ _ (T139_96 i) (hfix139_96 i) _)
      ⟨139, by decide⟩ ⟨96, by decide⟩ _
      (Q2.validAt ⟨139, by decide⟩ (Q2.listedAt ⟨139, by decide⟩
        (alnCheck_rep ⟨139, by decide⟩ hj hq).1))
      (colE2 ⟨96, by decide⟩ 2 hp) Q2.T139_96_2 Q2.hfix139_96_2 Q2.hinj139_96_2
      Q2.hcardT139_96_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T139_96_2 i) (Q2.hfix139_96_2 i) _)
      colCert_139_96_2.hD ?_).symm
  rw [alnId_139 j hj]


theorem leaf_139_96_3 (hp : 3 < (Q2.transData.getD 96 []).length)
    (j : Nat) (hj : j < (repChars.getD 139 []).length)
    (hq : (normIsRep.getD 139 []).getD j false = true) :
    species (Q2.reps (⟨96, by decide⟩ : Fin 148)) (colE2 ⟨96, by decide⟩ 3 hp)
        (rowE2 (⟨139, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨96, by decide⟩ : Fin 148))
        (colE1 ⟨96, by decide⟩ 3 (transLenTr ⟨96, by decide⟩ 3 hp))
        (rowE1 (⟨139, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨139, by decide⟩ : Fin 148) ⟨96, by decide⟩ _
      (validAt ⟨139, by decide⟩ (listedAt ⟨139, by decide⟩ hj))
      (colE1 ⟨96, by decide⟩ 3 (transLenTr ⟨96, by decide⟩ 3 hp)) T139_96
      hfix139_96 hinj139_96 hcardT139_96
      (fun i => conj_mem_of_fixedPoints _ _ (T139_96 i) (hfix139_96 i) _)
      ⟨139, by decide⟩ ⟨96, by decide⟩ _
      (Q2.validAt ⟨139, by decide⟩ (Q2.listedAt ⟨139, by decide⟩
        (alnCheck_rep ⟨139, by decide⟩ hj hq).1))
      (colE2 ⟨96, by decide⟩ 3 hp) Q2.T139_96_2 Q2.hfix139_96_2 Q2.hinj139_96_2
      Q2.hcardT139_96_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T139_96_2 i) (Q2.hfix139_96_2 i) _)
      colCert_139_96_3.hD ?_).symm
  rw [alnId_139 j hj]


theorem leaf_139_96_4 (hp : 4 < (Q2.transData.getD 96 []).length)
    (j : Nat) (hj : j < (repChars.getD 139 []).length)
    (hq : (normIsRep.getD 139 []).getD j false = true) :
    species (Q2.reps (⟨96, by decide⟩ : Fin 148)) (colE2 ⟨96, by decide⟩ 4 hp)
        (rowE2 (⟨139, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨96, by decide⟩ : Fin 148))
        (colE1 ⟨96, by decide⟩ 4 (transLenTr ⟨96, by decide⟩ 4 hp))
        (rowE1 (⟨139, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨139, by decide⟩ : Fin 148) ⟨96, by decide⟩ _
      (validAt ⟨139, by decide⟩ (listedAt ⟨139, by decide⟩ hj))
      (colE1 ⟨96, by decide⟩ 4 (transLenTr ⟨96, by decide⟩ 4 hp)) T139_96
      hfix139_96 hinj139_96 hcardT139_96
      (fun i => conj_mem_of_fixedPoints _ _ (T139_96 i) (hfix139_96 i) _)
      ⟨139, by decide⟩ ⟨96, by decide⟩ _
      (Q2.validAt ⟨139, by decide⟩ (Q2.listedAt ⟨139, by decide⟩
        (alnCheck_rep ⟨139, by decide⟩ hj hq).1))
      (colE2 ⟨96, by decide⟩ 4 hp) Q2.T139_96_2 Q2.hfix139_96_2 Q2.hinj139_96_2
      Q2.hcardT139_96_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T139_96_2 i) (Q2.hfix139_96_2 i) _)
      colCert_139_96_4.hD ?_).symm
  rw [alnId_139 j hj]


theorem leaf_139_96_5 (hp : 5 < (Q2.transData.getD 96 []).length)
    (j : Nat) (hj : j < (repChars.getD 139 []).length)
    (hq : (normIsRep.getD 139 []).getD j false = true) :
    species (Q2.reps (⟨96, by decide⟩ : Fin 148)) (colE2 ⟨96, by decide⟩ 5 hp)
        (rowE2 (⟨139, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨96, by decide⟩ : Fin 148))
        (colE1 ⟨96, by decide⟩ 5 (transLenTr ⟨96, by decide⟩ 5 hp))
        (rowE1 (⟨139, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨139, by decide⟩ : Fin 148) ⟨96, by decide⟩ _
      (validAt ⟨139, by decide⟩ (listedAt ⟨139, by decide⟩ hj))
      (colE1 ⟨96, by decide⟩ 5 (transLenTr ⟨96, by decide⟩ 5 hp)) T139_96
      hfix139_96 hinj139_96 hcardT139_96
      (fun i => conj_mem_of_fixedPoints _ _ (T139_96 i) (hfix139_96 i) _)
      ⟨139, by decide⟩ ⟨96, by decide⟩ _
      (Q2.validAt ⟨139, by decide⟩ (Q2.listedAt ⟨139, by decide⟩
        (alnCheck_rep ⟨139, by decide⟩ hj hq).1))
      (colE2 ⟨96, by decide⟩ 5 hp) Q2.T139_96_2 Q2.hfix139_96_2 Q2.hinj139_96_2
      Q2.hcardT139_96_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T139_96_2 i) (Q2.hfix139_96_2 i) _)
      ?_).symm
  rw [show colData1 (⟨139, by decide⟩ : Fin 148)
        ((colE1 ⟨96, by decide⟩ 5 (transLenTr ⟨96, by decide⟩ 5 hp) : ↥(reps ⟨96, by decide⟩)) : Coordinate 1)
        T139_96 = colFn colCertDiv_139_96_5.D1 (m := 5) from colCertDiv_139_96_5.bind1,
    show colData2 (⟨139, by decide⟩ : Fin 148)
        ((colE2 ⟨96, by decide⟩ 5 hp : ↥(Q2.reps ⟨96, by decide⟩)) : Coordinate 2)
        Q2.T139_96_2 = colFn colCertDiv_139_96_5.D2 (m := 5) from colCertDiv_139_96_5.bind2]
  rw [alnId_139 j hj]
  exact fastcode_of_div ⟨139, by decide⟩ _ _ _
    ((alnId_139 j hj) ▸ Q2.listedAt (⟨139, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨139, by decide⟩ : Fin 148) hj hq).1) colCertDiv_139_96_5_match


theorem leaf_139_96_10 (hp : 10 < (Q2.transData.getD 96 []).length)
    (j : Nat) (hj : j < (repChars.getD 139 []).length)
    (hq : (normIsRep.getD 139 []).getD j false = true) :
    species (Q2.reps (⟨96, by decide⟩ : Fin 148)) (colE2 ⟨96, by decide⟩ 10 hp)
        (rowE2 (⟨139, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨96, by decide⟩ : Fin 148))
        (colE1 ⟨96, by decide⟩ 10 (transLenTr ⟨96, by decide⟩ 10 hp))
        (rowE1 (⟨139, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨139, by decide⟩ : Fin 148) ⟨96, by decide⟩ _
      (validAt ⟨139, by decide⟩ (listedAt ⟨139, by decide⟩ hj))
      (colE1 ⟨96, by decide⟩ 10 (transLenTr ⟨96, by decide⟩ 10 hp)) T139_96
      hfix139_96 hinj139_96 hcardT139_96
      (fun i => conj_mem_of_fixedPoints _ _ (T139_96 i) (hfix139_96 i) _)
      ⟨139, by decide⟩ ⟨96, by decide⟩ _
      (Q2.validAt ⟨139, by decide⟩ (Q2.listedAt ⟨139, by decide⟩
        (alnCheck_rep ⟨139, by decide⟩ hj hq).1))
      (colE2 ⟨96, by decide⟩ 10 hp) Q2.T139_96_2 Q2.hfix139_96_2 Q2.hinj139_96_2
      Q2.hcardT139_96_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T139_96_2 i) (Q2.hfix139_96_2 i) _)
      ?_).symm
  rw [show colData1 (⟨139, by decide⟩ : Fin 148)
        ((colE1 ⟨96, by decide⟩ 10 (transLenTr ⟨96, by decide⟩ 10 hp) : ↥(reps ⟨96, by decide⟩)) : Coordinate 1)
        T139_96 = colFn colCertDiv_139_96_10.D1 (m := 5) from colCertDiv_139_96_10.bind1,
    show colData2 (⟨139, by decide⟩ : Fin 148)
        ((colE2 ⟨96, by decide⟩ 10 hp : ↥(Q2.reps ⟨96, by decide⟩)) : Coordinate 2)
        Q2.T139_96_2 = colFn colCertDiv_139_96_10.D2 (m := 5) from colCertDiv_139_96_10.bind2]
  rw [alnId_139 j hj]
  exact fastcode_of_div ⟨139, by decide⟩ _ _ _
    ((alnId_139 j hj) ▸ Q2.listedAt (⟨139, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨139, by decide⟩ : Fin 148) hj hq).1) colCertDiv_139_96_10_match


theorem leaf_139_96_15 (hp : 15 < (Q2.transData.getD 96 []).length)
    (j : Nat) (hj : j < (repChars.getD 139 []).length)
    (hq : (normIsRep.getD 139 []).getD j false = true) :
    species (Q2.reps (⟨96, by decide⟩ : Fin 148)) (colE2 ⟨96, by decide⟩ 15 hp)
        (rowE2 (⟨139, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨96, by decide⟩ : Fin 148))
        (colE1 ⟨96, by decide⟩ 15 (transLenTr ⟨96, by decide⟩ 15 hp))
        (rowE1 (⟨139, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨139, by decide⟩ : Fin 148) ⟨96, by decide⟩ _
      (validAt ⟨139, by decide⟩ (listedAt ⟨139, by decide⟩ hj))
      (colE1 ⟨96, by decide⟩ 15 (transLenTr ⟨96, by decide⟩ 15 hp)) T139_96
      hfix139_96 hinj139_96 hcardT139_96
      (fun i => conj_mem_of_fixedPoints _ _ (T139_96 i) (hfix139_96 i) _)
      ⟨139, by decide⟩ ⟨96, by decide⟩ _
      (Q2.validAt ⟨139, by decide⟩ (Q2.listedAt ⟨139, by decide⟩
        (alnCheck_rep ⟨139, by decide⟩ hj hq).1))
      (colE2 ⟨96, by decide⟩ 15 hp) Q2.T139_96_2 Q2.hfix139_96_2 Q2.hinj139_96_2
      Q2.hcardT139_96_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T139_96_2 i) (Q2.hfix139_96_2 i) _)
      ?_).symm
  rw [show colData1 (⟨139, by decide⟩ : Fin 148)
        ((colE1 ⟨96, by decide⟩ 15 (transLenTr ⟨96, by decide⟩ 15 hp) : ↥(reps ⟨96, by decide⟩)) : Coordinate 1)
        T139_96 = colFn colCertDiv_139_96_15.D1 (m := 5) from colCertDiv_139_96_15.bind1,
    show colData2 (⟨139, by decide⟩ : Fin 148)
        ((colE2 ⟨96, by decide⟩ 15 hp : ↥(Q2.reps ⟨96, by decide⟩)) : Coordinate 2)
        Q2.T139_96_2 = colFn colCertDiv_139_96_15.D2 (m := 5) from colCertDiv_139_96_15.bind2]
  rw [alnId_139 j hj]
  exact fastcode_of_div ⟨139, by decide⟩ _ _ _
    ((alnId_139 j hj) ▸ Q2.listedAt (⟨139, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨139, by decide⟩ : Fin 148) hj hq).1) colCertDiv_139_96_15_match


theorem leaf_139_96_20 (hp : 20 < (Q2.transData.getD 96 []).length)
    (j : Nat) (hj : j < (repChars.getD 139 []).length)
    (hq : (normIsRep.getD 139 []).getD j false = true) :
    species (Q2.reps (⟨96, by decide⟩ : Fin 148)) (colE2 ⟨96, by decide⟩ 20 hp)
        (rowE2 (⟨139, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨96, by decide⟩ : Fin 148))
        (colE1 ⟨96, by decide⟩ 20 (transLenTr ⟨96, by decide⟩ 20 hp))
        (rowE1 (⟨139, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨139, by decide⟩ : Fin 148) ⟨96, by decide⟩ _
      (validAt ⟨139, by decide⟩ (listedAt ⟨139, by decide⟩ hj))
      (colE1 ⟨96, by decide⟩ 20 (transLenTr ⟨96, by decide⟩ 20 hp)) T139_96
      hfix139_96 hinj139_96 hcardT139_96
      (fun i => conj_mem_of_fixedPoints _ _ (T139_96 i) (hfix139_96 i) _)
      ⟨139, by decide⟩ ⟨96, by decide⟩ _
      (Q2.validAt ⟨139, by decide⟩ (Q2.listedAt ⟨139, by decide⟩
        (alnCheck_rep ⟨139, by decide⟩ hj hq).1))
      (colE2 ⟨96, by decide⟩ 20 hp) Q2.T139_96_2 Q2.hfix139_96_2 Q2.hinj139_96_2
      Q2.hcardT139_96_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T139_96_2 i) (Q2.hfix139_96_2 i) _)
      ?_).symm
  rw [show colData1 (⟨139, by decide⟩ : Fin 148)
        ((colE1 ⟨96, by decide⟩ 20 (transLenTr ⟨96, by decide⟩ 20 hp) : ↥(reps ⟨96, by decide⟩)) : Coordinate 1)
        T139_96 = colFn colCertDiv_139_96_20.D1 (m := 5) from colCertDiv_139_96_20.bind1,
    show colData2 (⟨139, by decide⟩ : Fin 148)
        ((colE2 ⟨96, by decide⟩ 20 hp : ↥(Q2.reps ⟨96, by decide⟩)) : Coordinate 2)
        Q2.T139_96_2 = colFn colCertDiv_139_96_20.D2 (m := 5) from colCertDiv_139_96_20.bind2]
  rw [alnId_139 j hj]
  exact fastcode_of_div ⟨139, by decide⟩ _ _ _
    ((alnId_139 j hj) ▸ Q2.listedAt (⟨139, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨139, by decide⟩ : Fin 148) hj hq).1) colCertDiv_139_96_20_match


theorem leaf_139_100_0 (hp : 0 < (Q2.transData.getD 100 []).length)
    (j : Nat) (hj : j < (repChars.getD 139 []).length)
    (hq : (normIsRep.getD 139 []).getD j false = true) :
    species (Q2.reps (⟨100, by decide⟩ : Fin 148)) (colE2 ⟨100, by decide⟩ 0 hp)
        (rowE2 (⟨139, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨100, by decide⟩ : Fin 148))
        (colE1 ⟨100, by decide⟩ 0 (transLenTr ⟨100, by decide⟩ 0 hp))
        (rowE1 (⟨139, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨139, by decide⟩ : Fin 148) ⟨100, by decide⟩ _
      (validAt ⟨139, by decide⟩ (listedAt ⟨139, by decide⟩ hj))
      (colE1 ⟨100, by decide⟩ 0 (transLenTr ⟨100, by decide⟩ 0 hp)) T139_100
      hfix139_100 hinj139_100 hcardT139_100
      (fun i => conj_mem_of_fixedPoints _ _ (T139_100 i) (hfix139_100 i) _)
      ⟨139, by decide⟩ ⟨100, by decide⟩ _
      (Q2.validAt ⟨139, by decide⟩ (Q2.listedAt ⟨139, by decide⟩
        (alnCheck_rep ⟨139, by decide⟩ hj hq).1))
      (colE2 ⟨100, by decide⟩ 0 hp) Q2.T139_100_2 Q2.hfix139_100_2 Q2.hinj139_100_2
      Q2.hcardT139_100_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T139_100_2 i) (Q2.hfix139_100_2 i) _)
      colCert_139_100_0.hD ?_).symm
  rw [alnId_139 j hj]


theorem leaf_139_100_1 (hp : 1 < (Q2.transData.getD 100 []).length)
    (j : Nat) (hj : j < (repChars.getD 139 []).length)
    (hq : (normIsRep.getD 139 []).getD j false = true) :
    species (Q2.reps (⟨100, by decide⟩ : Fin 148)) (colE2 ⟨100, by decide⟩ 1 hp)
        (rowE2 (⟨139, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨100, by decide⟩ : Fin 148))
        (colE1 ⟨100, by decide⟩ 1 (transLenTr ⟨100, by decide⟩ 1 hp))
        (rowE1 (⟨139, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨139, by decide⟩ : Fin 148) ⟨100, by decide⟩ _
      (validAt ⟨139, by decide⟩ (listedAt ⟨139, by decide⟩ hj))
      (colE1 ⟨100, by decide⟩ 1 (transLenTr ⟨100, by decide⟩ 1 hp)) T139_100
      hfix139_100 hinj139_100 hcardT139_100
      (fun i => conj_mem_of_fixedPoints _ _ (T139_100 i) (hfix139_100 i) _)
      ⟨139, by decide⟩ ⟨100, by decide⟩ _
      (Q2.validAt ⟨139, by decide⟩ (Q2.listedAt ⟨139, by decide⟩
        (alnCheck_rep ⟨139, by decide⟩ hj hq).1))
      (colE2 ⟨100, by decide⟩ 1 hp) Q2.T139_100_2 Q2.hfix139_100_2 Q2.hinj139_100_2
      Q2.hcardT139_100_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T139_100_2 i) (Q2.hfix139_100_2 i) _)
      colCert_139_100_1.hD ?_).symm
  rw [alnId_139 j hj]


theorem leaf_139_100_2 (hp : 2 < (Q2.transData.getD 100 []).length)
    (j : Nat) (hj : j < (repChars.getD 139 []).length)
    (hq : (normIsRep.getD 139 []).getD j false = true) :
    species (Q2.reps (⟨100, by decide⟩ : Fin 148)) (colE2 ⟨100, by decide⟩ 2 hp)
        (rowE2 (⟨139, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨100, by decide⟩ : Fin 148))
        (colE1 ⟨100, by decide⟩ 2 (transLenTr ⟨100, by decide⟩ 2 hp))
        (rowE1 (⟨139, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨139, by decide⟩ : Fin 148) ⟨100, by decide⟩ _
      (validAt ⟨139, by decide⟩ (listedAt ⟨139, by decide⟩ hj))
      (colE1 ⟨100, by decide⟩ 2 (transLenTr ⟨100, by decide⟩ 2 hp)) T139_100
      hfix139_100 hinj139_100 hcardT139_100
      (fun i => conj_mem_of_fixedPoints _ _ (T139_100 i) (hfix139_100 i) _)
      ⟨139, by decide⟩ ⟨100, by decide⟩ _
      (Q2.validAt ⟨139, by decide⟩ (Q2.listedAt ⟨139, by decide⟩
        (alnCheck_rep ⟨139, by decide⟩ hj hq).1))
      (colE2 ⟨100, by decide⟩ 2 hp) Q2.T139_100_2 Q2.hfix139_100_2 Q2.hinj139_100_2
      Q2.hcardT139_100_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T139_100_2 i) (Q2.hfix139_100_2 i) _)
      colCert_139_100_2.hD ?_).symm
  rw [alnId_139 j hj]


theorem leaf_139_100_3 (hp : 3 < (Q2.transData.getD 100 []).length)
    (j : Nat) (hj : j < (repChars.getD 139 []).length)
    (hq : (normIsRep.getD 139 []).getD j false = true) :
    species (Q2.reps (⟨100, by decide⟩ : Fin 148)) (colE2 ⟨100, by decide⟩ 3 hp)
        (rowE2 (⟨139, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨100, by decide⟩ : Fin 148))
        (colE1 ⟨100, by decide⟩ 3 (transLenTr ⟨100, by decide⟩ 3 hp))
        (rowE1 (⟨139, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨139, by decide⟩ : Fin 148) ⟨100, by decide⟩ _
      (validAt ⟨139, by decide⟩ (listedAt ⟨139, by decide⟩ hj))
      (colE1 ⟨100, by decide⟩ 3 (transLenTr ⟨100, by decide⟩ 3 hp)) T139_100
      hfix139_100 hinj139_100 hcardT139_100
      (fun i => conj_mem_of_fixedPoints _ _ (T139_100 i) (hfix139_100 i) _)
      ⟨139, by decide⟩ ⟨100, by decide⟩ _
      (Q2.validAt ⟨139, by decide⟩ (Q2.listedAt ⟨139, by decide⟩
        (alnCheck_rep ⟨139, by decide⟩ hj hq).1))
      (colE2 ⟨100, by decide⟩ 3 hp) Q2.T139_100_2 Q2.hfix139_100_2 Q2.hinj139_100_2
      Q2.hcardT139_100_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T139_100_2 i) (Q2.hfix139_100_2 i) _)
      colCert_139_100_3.hD ?_).symm
  rw [alnId_139 j hj]


theorem leaf_139_100_4 (hp : 4 < (Q2.transData.getD 100 []).length)
    (j : Nat) (hj : j < (repChars.getD 139 []).length)
    (hq : (normIsRep.getD 139 []).getD j false = true) :
    species (Q2.reps (⟨100, by decide⟩ : Fin 148)) (colE2 ⟨100, by decide⟩ 4 hp)
        (rowE2 (⟨139, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨100, by decide⟩ : Fin 148))
        (colE1 ⟨100, by decide⟩ 4 (transLenTr ⟨100, by decide⟩ 4 hp))
        (rowE1 (⟨139, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨139, by decide⟩ : Fin 148) ⟨100, by decide⟩ _
      (validAt ⟨139, by decide⟩ (listedAt ⟨139, by decide⟩ hj))
      (colE1 ⟨100, by decide⟩ 4 (transLenTr ⟨100, by decide⟩ 4 hp)) T139_100
      hfix139_100 hinj139_100 hcardT139_100
      (fun i => conj_mem_of_fixedPoints _ _ (T139_100 i) (hfix139_100 i) _)
      ⟨139, by decide⟩ ⟨100, by decide⟩ _
      (Q2.validAt ⟨139, by decide⟩ (Q2.listedAt ⟨139, by decide⟩
        (alnCheck_rep ⟨139, by decide⟩ hj hq).1))
      (colE2 ⟨100, by decide⟩ 4 hp) Q2.T139_100_2 Q2.hfix139_100_2 Q2.hinj139_100_2
      Q2.hcardT139_100_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T139_100_2 i) (Q2.hfix139_100_2 i) _)
      colCert_139_100_4.hD ?_).symm
  rw [alnId_139 j hj]


theorem leaf_139_100_5 (hp : 5 < (Q2.transData.getD 100 []).length)
    (j : Nat) (hj : j < (repChars.getD 139 []).length)
    (hq : (normIsRep.getD 139 []).getD j false = true) :
    species (Q2.reps (⟨100, by decide⟩ : Fin 148)) (colE2 ⟨100, by decide⟩ 5 hp)
        (rowE2 (⟨139, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨100, by decide⟩ : Fin 148))
        (colE1 ⟨100, by decide⟩ 5 (transLenTr ⟨100, by decide⟩ 5 hp))
        (rowE1 (⟨139, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨139, by decide⟩ : Fin 148) ⟨100, by decide⟩ _
      (validAt ⟨139, by decide⟩ (listedAt ⟨139, by decide⟩ hj))
      (colE1 ⟨100, by decide⟩ 5 (transLenTr ⟨100, by decide⟩ 5 hp)) T139_100
      hfix139_100 hinj139_100 hcardT139_100
      (fun i => conj_mem_of_fixedPoints _ _ (T139_100 i) (hfix139_100 i) _)
      ⟨139, by decide⟩ ⟨100, by decide⟩ _
      (Q2.validAt ⟨139, by decide⟩ (Q2.listedAt ⟨139, by decide⟩
        (alnCheck_rep ⟨139, by decide⟩ hj hq).1))
      (colE2 ⟨100, by decide⟩ 5 hp) Q2.T139_100_2 Q2.hfix139_100_2 Q2.hinj139_100_2
      Q2.hcardT139_100_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T139_100_2 i) (Q2.hfix139_100_2 i) _)
      colCert_139_100_5.hD ?_).symm
  rw [alnId_139 j hj]


theorem leaf_139_100_10 (hp : 10 < (Q2.transData.getD 100 []).length)
    (j : Nat) (hj : j < (repChars.getD 139 []).length)
    (hq : (normIsRep.getD 139 []).getD j false = true) :
    species (Q2.reps (⟨100, by decide⟩ : Fin 148)) (colE2 ⟨100, by decide⟩ 10 hp)
        (rowE2 (⟨139, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨100, by decide⟩ : Fin 148))
        (colE1 ⟨100, by decide⟩ 10 (transLenTr ⟨100, by decide⟩ 10 hp))
        (rowE1 (⟨139, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨139, by decide⟩ : Fin 148) ⟨100, by decide⟩ _
      (validAt ⟨139, by decide⟩ (listedAt ⟨139, by decide⟩ hj))
      (colE1 ⟨100, by decide⟩ 10 (transLenTr ⟨100, by decide⟩ 10 hp)) T139_100
      hfix139_100 hinj139_100 hcardT139_100
      (fun i => conj_mem_of_fixedPoints _ _ (T139_100 i) (hfix139_100 i) _)
      ⟨139, by decide⟩ ⟨100, by decide⟩ _
      (Q2.validAt ⟨139, by decide⟩ (Q2.listedAt ⟨139, by decide⟩
        (alnCheck_rep ⟨139, by decide⟩ hj hq).1))
      (colE2 ⟨100, by decide⟩ 10 hp) Q2.T139_100_2 Q2.hfix139_100_2 Q2.hinj139_100_2
      Q2.hcardT139_100_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T139_100_2 i) (Q2.hfix139_100_2 i) _)
      colCert_139_100_10.hD ?_).symm
  rw [alnId_139 j hj]


theorem leaf_139_100_15 (hp : 15 < (Q2.transData.getD 100 []).length)
    (j : Nat) (hj : j < (repChars.getD 139 []).length)
    (hq : (normIsRep.getD 139 []).getD j false = true) :
    species (Q2.reps (⟨100, by decide⟩ : Fin 148)) (colE2 ⟨100, by decide⟩ 15 hp)
        (rowE2 (⟨139, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨100, by decide⟩ : Fin 148))
        (colE1 ⟨100, by decide⟩ 15 (transLenTr ⟨100, by decide⟩ 15 hp))
        (rowE1 (⟨139, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨139, by decide⟩ : Fin 148) ⟨100, by decide⟩ _
      (validAt ⟨139, by decide⟩ (listedAt ⟨139, by decide⟩ hj))
      (colE1 ⟨100, by decide⟩ 15 (transLenTr ⟨100, by decide⟩ 15 hp)) T139_100
      hfix139_100 hinj139_100 hcardT139_100
      (fun i => conj_mem_of_fixedPoints _ _ (T139_100 i) (hfix139_100 i) _)
      ⟨139, by decide⟩ ⟨100, by decide⟩ _
      (Q2.validAt ⟨139, by decide⟩ (Q2.listedAt ⟨139, by decide⟩
        (alnCheck_rep ⟨139, by decide⟩ hj hq).1))
      (colE2 ⟨100, by decide⟩ 15 hp) Q2.T139_100_2 Q2.hfix139_100_2 Q2.hinj139_100_2
      Q2.hcardT139_100_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T139_100_2 i) (Q2.hfix139_100_2 i) _)
      colCert_139_100_15.hD ?_).symm
  rw [alnId_139 j hj]


theorem leaf_139_100_20 (hp : 20 < (Q2.transData.getD 100 []).length)
    (j : Nat) (hj : j < (repChars.getD 139 []).length)
    (hq : (normIsRep.getD 139 []).getD j false = true) :
    species (Q2.reps (⟨100, by decide⟩ : Fin 148)) (colE2 ⟨100, by decide⟩ 20 hp)
        (rowE2 (⟨139, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨100, by decide⟩ : Fin 148))
        (colE1 ⟨100, by decide⟩ 20 (transLenTr ⟨100, by decide⟩ 20 hp))
        (rowE1 (⟨139, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨139, by decide⟩ : Fin 148) ⟨100, by decide⟩ _
      (validAt ⟨139, by decide⟩ (listedAt ⟨139, by decide⟩ hj))
      (colE1 ⟨100, by decide⟩ 20 (transLenTr ⟨100, by decide⟩ 20 hp)) T139_100
      hfix139_100 hinj139_100 hcardT139_100
      (fun i => conj_mem_of_fixedPoints _ _ (T139_100 i) (hfix139_100 i) _)
      ⟨139, by decide⟩ ⟨100, by decide⟩ _
      (Q2.validAt ⟨139, by decide⟩ (Q2.listedAt ⟨139, by decide⟩
        (alnCheck_rep ⟨139, by decide⟩ hj hq).1))
      (colE2 ⟨100, by decide⟩ 20 hp) Q2.T139_100_2 Q2.hfix139_100_2 Q2.hinj139_100_2
      Q2.hcardT139_100_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T139_100_2 i) (Q2.hfix139_100_2 i) _)
      colCert_139_100_20.hD ?_).symm
  rw [alnId_139 j hj]


theorem leaf_139_100_25 (hp : 25 < (Q2.transData.getD 100 []).length)
    (j : Nat) (hj : j < (repChars.getD 139 []).length)
    (hq : (normIsRep.getD 139 []).getD j false = true) :
    species (Q2.reps (⟨100, by decide⟩ : Fin 148)) (colE2 ⟨100, by decide⟩ 25 hp)
        (rowE2 (⟨139, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨100, by decide⟩ : Fin 148))
        (colE1 ⟨100, by decide⟩ 25 (transLenTr ⟨100, by decide⟩ 25 hp))
        (rowE1 (⟨139, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨139, by decide⟩ : Fin 148) ⟨100, by decide⟩ _
      (validAt ⟨139, by decide⟩ (listedAt ⟨139, by decide⟩ hj))
      (colE1 ⟨100, by decide⟩ 25 (transLenTr ⟨100, by decide⟩ 25 hp)) T139_100
      hfix139_100 hinj139_100 hcardT139_100
      (fun i => conj_mem_of_fixedPoints _ _ (T139_100 i) (hfix139_100 i) _)
      ⟨139, by decide⟩ ⟨100, by decide⟩ _
      (Q2.validAt ⟨139, by decide⟩ (Q2.listedAt ⟨139, by decide⟩
        (alnCheck_rep ⟨139, by decide⟩ hj hq).1))
      (colE2 ⟨100, by decide⟩ 25 hp) Q2.T139_100_2 Q2.hfix139_100_2 Q2.hinj139_100_2
      Q2.hcardT139_100_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T139_100_2 i) (Q2.hfix139_100_2 i) _)
      ?_).symm
  rw [show colData1 (⟨139, by decide⟩ : Fin 148)
        ((colE1 ⟨100, by decide⟩ 25 (transLenTr ⟨100, by decide⟩ 25 hp) : ↥(reps ⟨100, by decide⟩)) : Coordinate 1)
        T139_100 = colFn colCertDiv_139_100_25.D1 (m := 5) from colCertDiv_139_100_25.bind1,
    show colData2 (⟨139, by decide⟩ : Fin 148)
        ((colE2 ⟨100, by decide⟩ 25 hp : ↥(Q2.reps ⟨100, by decide⟩)) : Coordinate 2)
        Q2.T139_100_2 = colFn colCertDiv_139_100_25.D2 (m := 5) from colCertDiv_139_100_25.bind2]
  rw [alnId_139 j hj]
  exact fastcode_of_div ⟨139, by decide⟩ _ _ _
    ((alnId_139 j hj) ▸ Q2.listedAt (⟨139, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨139, by decide⟩ : Fin 148) hj hq).1) colCertDiv_139_100_25_match


theorem leaf_139_100_50 (hp : 50 < (Q2.transData.getD 100 []).length)
    (j : Nat) (hj : j < (repChars.getD 139 []).length)
    (hq : (normIsRep.getD 139 []).getD j false = true) :
    species (Q2.reps (⟨100, by decide⟩ : Fin 148)) (colE2 ⟨100, by decide⟩ 50 hp)
        (rowE2 (⟨139, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨100, by decide⟩ : Fin 148))
        (colE1 ⟨100, by decide⟩ 50 (transLenTr ⟨100, by decide⟩ 50 hp))
        (rowE1 (⟨139, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨139, by decide⟩ : Fin 148) ⟨100, by decide⟩ _
      (validAt ⟨139, by decide⟩ (listedAt ⟨139, by decide⟩ hj))
      (colE1 ⟨100, by decide⟩ 50 (transLenTr ⟨100, by decide⟩ 50 hp)) T139_100
      hfix139_100 hinj139_100 hcardT139_100
      (fun i => conj_mem_of_fixedPoints _ _ (T139_100 i) (hfix139_100 i) _)
      ⟨139, by decide⟩ ⟨100, by decide⟩ _
      (Q2.validAt ⟨139, by decide⟩ (Q2.listedAt ⟨139, by decide⟩
        (alnCheck_rep ⟨139, by decide⟩ hj hq).1))
      (colE2 ⟨100, by decide⟩ 50 hp) Q2.T139_100_2 Q2.hfix139_100_2 Q2.hinj139_100_2
      Q2.hcardT139_100_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T139_100_2 i) (Q2.hfix139_100_2 i) _)
      ?_).symm
  rw [show colData1 (⟨139, by decide⟩ : Fin 148)
        ((colE1 ⟨100, by decide⟩ 50 (transLenTr ⟨100, by decide⟩ 50 hp) : ↥(reps ⟨100, by decide⟩)) : Coordinate 1)
        T139_100 = colFn colCertDiv_139_100_50.D1 (m := 5) from colCertDiv_139_100_50.bind1,
    show colData2 (⟨139, by decide⟩ : Fin 148)
        ((colE2 ⟨100, by decide⟩ 50 hp : ↥(Q2.reps ⟨100, by decide⟩)) : Coordinate 2)
        Q2.T139_100_2 = colFn colCertDiv_139_100_50.D2 (m := 5) from colCertDiv_139_100_50.bind2]
  rw [alnId_139 j hj]
  exact fastcode_of_div ⟨139, by decide⟩ _ _ _
    ((alnId_139 j hj) ▸ Q2.listedAt (⟨139, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨139, by decide⟩ : Fin 148) hj hq).1) colCertDiv_139_100_50_match


theorem leaf_139_100_75 (hp : 75 < (Q2.transData.getD 100 []).length)
    (j : Nat) (hj : j < (repChars.getD 139 []).length)
    (hq : (normIsRep.getD 139 []).getD j false = true) :
    species (Q2.reps (⟨100, by decide⟩ : Fin 148)) (colE2 ⟨100, by decide⟩ 75 hp)
        (rowE2 (⟨139, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨100, by decide⟩ : Fin 148))
        (colE1 ⟨100, by decide⟩ 75 (transLenTr ⟨100, by decide⟩ 75 hp))
        (rowE1 (⟨139, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨139, by decide⟩ : Fin 148) ⟨100, by decide⟩ _
      (validAt ⟨139, by decide⟩ (listedAt ⟨139, by decide⟩ hj))
      (colE1 ⟨100, by decide⟩ 75 (transLenTr ⟨100, by decide⟩ 75 hp)) T139_100
      hfix139_100 hinj139_100 hcardT139_100
      (fun i => conj_mem_of_fixedPoints _ _ (T139_100 i) (hfix139_100 i) _)
      ⟨139, by decide⟩ ⟨100, by decide⟩ _
      (Q2.validAt ⟨139, by decide⟩ (Q2.listedAt ⟨139, by decide⟩
        (alnCheck_rep ⟨139, by decide⟩ hj hq).1))
      (colE2 ⟨100, by decide⟩ 75 hp) Q2.T139_100_2 Q2.hfix139_100_2 Q2.hinj139_100_2
      Q2.hcardT139_100_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T139_100_2 i) (Q2.hfix139_100_2 i) _)
      ?_).symm
  rw [show colData1 (⟨139, by decide⟩ : Fin 148)
        ((colE1 ⟨100, by decide⟩ 75 (transLenTr ⟨100, by decide⟩ 75 hp) : ↥(reps ⟨100, by decide⟩)) : Coordinate 1)
        T139_100 = colFn colCertDiv_139_100_75.D1 (m := 5) from colCertDiv_139_100_75.bind1,
    show colData2 (⟨139, by decide⟩ : Fin 148)
        ((colE2 ⟨100, by decide⟩ 75 hp : ↥(Q2.reps ⟨100, by decide⟩)) : Coordinate 2)
        Q2.T139_100_2 = colFn colCertDiv_139_100_75.D2 (m := 5) from colCertDiv_139_100_75.bind2]
  rw [alnId_139 j hj]
  exact fastcode_of_div ⟨139, by decide⟩ _ _ _
    ((alnId_139 j hj) ▸ Q2.listedAt (⟨139, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨139, by decide⟩ : Fin 148) hj hq).1) colCertDiv_139_100_75_match


theorem leaf_139_100_100 (hp : 100 < (Q2.transData.getD 100 []).length)
    (j : Nat) (hj : j < (repChars.getD 139 []).length)
    (hq : (normIsRep.getD 139 []).getD j false = true) :
    species (Q2.reps (⟨100, by decide⟩ : Fin 148)) (colE2 ⟨100, by decide⟩ 100 hp)
        (rowE2 (⟨139, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨100, by decide⟩ : Fin 148))
        (colE1 ⟨100, by decide⟩ 100 (transLenTr ⟨100, by decide⟩ 100 hp))
        (rowE1 (⟨139, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨139, by decide⟩ : Fin 148) ⟨100, by decide⟩ _
      (validAt ⟨139, by decide⟩ (listedAt ⟨139, by decide⟩ hj))
      (colE1 ⟨100, by decide⟩ 100 (transLenTr ⟨100, by decide⟩ 100 hp)) T139_100
      hfix139_100 hinj139_100 hcardT139_100
      (fun i => conj_mem_of_fixedPoints _ _ (T139_100 i) (hfix139_100 i) _)
      ⟨139, by decide⟩ ⟨100, by decide⟩ _
      (Q2.validAt ⟨139, by decide⟩ (Q2.listedAt ⟨139, by decide⟩
        (alnCheck_rep ⟨139, by decide⟩ hj hq).1))
      (colE2 ⟨100, by decide⟩ 100 hp) Q2.T139_100_2 Q2.hfix139_100_2 Q2.hinj139_100_2
      Q2.hcardT139_100_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T139_100_2 i) (Q2.hfix139_100_2 i) _)
      ?_).symm
  rw [show colData1 (⟨139, by decide⟩ : Fin 148)
        ((colE1 ⟨100, by decide⟩ 100 (transLenTr ⟨100, by decide⟩ 100 hp) : ↥(reps ⟨100, by decide⟩)) : Coordinate 1)
        T139_100 = colFn colCertDiv_139_100_100.D1 (m := 5) from colCertDiv_139_100_100.bind1,
    show colData2 (⟨139, by decide⟩ : Fin 148)
        ((colE2 ⟨100, by decide⟩ 100 hp : ↥(Q2.reps ⟨100, by decide⟩)) : Coordinate 2)
        Q2.T139_100_2 = colFn colCertDiv_139_100_100.D2 (m := 5) from colCertDiv_139_100_100.bind2]
  rw [alnId_139 j hj]
  exact fastcode_of_div ⟨139, by decide⟩ _ _ _
    ((alnId_139 j hj) ▸ Q2.listedAt (⟨139, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨139, by decide⟩ : Fin 148) hj hq).1) colCertDiv_139_100_100_match


theorem leaf_139_107_0 (hp : 0 < (Q2.transData.getD 107 []).length)
    (j : Nat) (hj : j < (repChars.getD 139 []).length)
    (hq : (normIsRep.getD 139 []).getD j false = true) :
    species (Q2.reps (⟨107, by decide⟩ : Fin 148)) (colE2 ⟨107, by decide⟩ 0 hp)
        (rowE2 (⟨139, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨107, by decide⟩ : Fin 148))
        (colE1 ⟨107, by decide⟩ 0 (transLenTr ⟨107, by decide⟩ 0 hp))
        (rowE1 (⟨139, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨139, by decide⟩ : Fin 148) ⟨107, by decide⟩ _
      (validAt ⟨139, by decide⟩ (listedAt ⟨139, by decide⟩ hj))
      (colE1 ⟨107, by decide⟩ 0 (transLenTr ⟨107, by decide⟩ 0 hp)) T139_107
      hfix139_107 hinj139_107 hcardT139_107
      (fun i => conj_mem_of_fixedPoints _ _ (T139_107 i) (hfix139_107 i) _)
      ⟨139, by decide⟩ ⟨107, by decide⟩ _
      (Q2.validAt ⟨139, by decide⟩ (Q2.listedAt ⟨139, by decide⟩
        (alnCheck_rep ⟨139, by decide⟩ hj hq).1))
      (colE2 ⟨107, by decide⟩ 0 hp) Q2.T139_107_2 Q2.hfix139_107_2 Q2.hinj139_107_2
      Q2.hcardT139_107_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T139_107_2 i) (Q2.hfix139_107_2 i) _)
      colCert_139_107_0.hD ?_).symm
  rw [alnId_139 j hj]


theorem leaf_139_107_1 (hp : 1 < (Q2.transData.getD 107 []).length)
    (j : Nat) (hj : j < (repChars.getD 139 []).length)
    (hq : (normIsRep.getD 139 []).getD j false = true) :
    species (Q2.reps (⟨107, by decide⟩ : Fin 148)) (colE2 ⟨107, by decide⟩ 1 hp)
        (rowE2 (⟨139, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨107, by decide⟩ : Fin 148))
        (colE1 ⟨107, by decide⟩ 1 (transLenTr ⟨107, by decide⟩ 1 hp))
        (rowE1 (⟨139, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨139, by decide⟩ : Fin 148) ⟨107, by decide⟩ _
      (validAt ⟨139, by decide⟩ (listedAt ⟨139, by decide⟩ hj))
      (colE1 ⟨107, by decide⟩ 1 (transLenTr ⟨107, by decide⟩ 1 hp)) T139_107
      hfix139_107 hinj139_107 hcardT139_107
      (fun i => conj_mem_of_fixedPoints _ _ (T139_107 i) (hfix139_107 i) _)
      ⟨139, by decide⟩ ⟨107, by decide⟩ _
      (Q2.validAt ⟨139, by decide⟩ (Q2.listedAt ⟨139, by decide⟩
        (alnCheck_rep ⟨139, by decide⟩ hj hq).1))
      (colE2 ⟨107, by decide⟩ 1 hp) Q2.T139_107_2 Q2.hfix139_107_2 Q2.hinj139_107_2
      Q2.hcardT139_107_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T139_107_2 i) (Q2.hfix139_107_2 i) _)
      colCert_139_107_1.hD ?_).symm
  rw [alnId_139 j hj]


theorem leaf_139_107_2 (hp : 2 < (Q2.transData.getD 107 []).length)
    (j : Nat) (hj : j < (repChars.getD 139 []).length)
    (hq : (normIsRep.getD 139 []).getD j false = true) :
    species (Q2.reps (⟨107, by decide⟩ : Fin 148)) (colE2 ⟨107, by decide⟩ 2 hp)
        (rowE2 (⟨139, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨107, by decide⟩ : Fin 148))
        (colE1 ⟨107, by decide⟩ 2 (transLenTr ⟨107, by decide⟩ 2 hp))
        (rowE1 (⟨139, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨139, by decide⟩ : Fin 148) ⟨107, by decide⟩ _
      (validAt ⟨139, by decide⟩ (listedAt ⟨139, by decide⟩ hj))
      (colE1 ⟨107, by decide⟩ 2 (transLenTr ⟨107, by decide⟩ 2 hp)) T139_107
      hfix139_107 hinj139_107 hcardT139_107
      (fun i => conj_mem_of_fixedPoints _ _ (T139_107 i) (hfix139_107 i) _)
      ⟨139, by decide⟩ ⟨107, by decide⟩ _
      (Q2.validAt ⟨139, by decide⟩ (Q2.listedAt ⟨139, by decide⟩
        (alnCheck_rep ⟨139, by decide⟩ hj hq).1))
      (colE2 ⟨107, by decide⟩ 2 hp) Q2.T139_107_2 Q2.hfix139_107_2 Q2.hinj139_107_2
      Q2.hcardT139_107_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T139_107_2 i) (Q2.hfix139_107_2 i) _)
      colCert_139_107_2.hD ?_).symm
  rw [alnId_139 j hj]


theorem leaf_139_107_3 (hp : 3 < (Q2.transData.getD 107 []).length)
    (j : Nat) (hj : j < (repChars.getD 139 []).length)
    (hq : (normIsRep.getD 139 []).getD j false = true) :
    species (Q2.reps (⟨107, by decide⟩ : Fin 148)) (colE2 ⟨107, by decide⟩ 3 hp)
        (rowE2 (⟨139, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨107, by decide⟩ : Fin 148))
        (colE1 ⟨107, by decide⟩ 3 (transLenTr ⟨107, by decide⟩ 3 hp))
        (rowE1 (⟨139, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨139, by decide⟩ : Fin 148) ⟨107, by decide⟩ _
      (validAt ⟨139, by decide⟩ (listedAt ⟨139, by decide⟩ hj))
      (colE1 ⟨107, by decide⟩ 3 (transLenTr ⟨107, by decide⟩ 3 hp)) T139_107
      hfix139_107 hinj139_107 hcardT139_107
      (fun i => conj_mem_of_fixedPoints _ _ (T139_107 i) (hfix139_107 i) _)
      ⟨139, by decide⟩ ⟨107, by decide⟩ _
      (Q2.validAt ⟨139, by decide⟩ (Q2.listedAt ⟨139, by decide⟩
        (alnCheck_rep ⟨139, by decide⟩ hj hq).1))
      (colE2 ⟨107, by decide⟩ 3 hp) Q2.T139_107_2 Q2.hfix139_107_2 Q2.hinj139_107_2
      Q2.hcardT139_107_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T139_107_2 i) (Q2.hfix139_107_2 i) _)
      colCert_139_107_3.hD ?_).symm
  rw [alnId_139 j hj]


theorem leaf_139_107_4 (hp : 4 < (Q2.transData.getD 107 []).length)
    (j : Nat) (hj : j < (repChars.getD 139 []).length)
    (hq : (normIsRep.getD 139 []).getD j false = true) :
    species (Q2.reps (⟨107, by decide⟩ : Fin 148)) (colE2 ⟨107, by decide⟩ 4 hp)
        (rowE2 (⟨139, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨107, by decide⟩ : Fin 148))
        (colE1 ⟨107, by decide⟩ 4 (transLenTr ⟨107, by decide⟩ 4 hp))
        (rowE1 (⟨139, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨139, by decide⟩ : Fin 148) ⟨107, by decide⟩ _
      (validAt ⟨139, by decide⟩ (listedAt ⟨139, by decide⟩ hj))
      (colE1 ⟨107, by decide⟩ 4 (transLenTr ⟨107, by decide⟩ 4 hp)) T139_107
      hfix139_107 hinj139_107 hcardT139_107
      (fun i => conj_mem_of_fixedPoints _ _ (T139_107 i) (hfix139_107 i) _)
      ⟨139, by decide⟩ ⟨107, by decide⟩ _
      (Q2.validAt ⟨139, by decide⟩ (Q2.listedAt ⟨139, by decide⟩
        (alnCheck_rep ⟨139, by decide⟩ hj hq).1))
      (colE2 ⟨107, by decide⟩ 4 hp) Q2.T139_107_2 Q2.hfix139_107_2 Q2.hinj139_107_2
      Q2.hcardT139_107_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T139_107_2 i) (Q2.hfix139_107_2 i) _)
      colCert_139_107_4.hD ?_).symm
  rw [alnId_139 j hj]


theorem leaf_139_107_5 (hp : 5 < (Q2.transData.getD 107 []).length)
    (j : Nat) (hj : j < (repChars.getD 139 []).length)
    (hq : (normIsRep.getD 139 []).getD j false = true) :
    species (Q2.reps (⟨107, by decide⟩ : Fin 148)) (colE2 ⟨107, by decide⟩ 5 hp)
        (rowE2 (⟨139, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨107, by decide⟩ : Fin 148))
        (colE1 ⟨107, by decide⟩ 5 (transLenTr ⟨107, by decide⟩ 5 hp))
        (rowE1 (⟨139, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨139, by decide⟩ : Fin 148) ⟨107, by decide⟩ _
      (validAt ⟨139, by decide⟩ (listedAt ⟨139, by decide⟩ hj))
      (colE1 ⟨107, by decide⟩ 5 (transLenTr ⟨107, by decide⟩ 5 hp)) T139_107
      hfix139_107 hinj139_107 hcardT139_107
      (fun i => conj_mem_of_fixedPoints _ _ (T139_107 i) (hfix139_107 i) _)
      ⟨139, by decide⟩ ⟨107, by decide⟩ _
      (Q2.validAt ⟨139, by decide⟩ (Q2.listedAt ⟨139, by decide⟩
        (alnCheck_rep ⟨139, by decide⟩ hj hq).1))
      (colE2 ⟨107, by decide⟩ 5 hp) Q2.T139_107_2 Q2.hfix139_107_2 Q2.hinj139_107_2
      Q2.hcardT139_107_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T139_107_2 i) (Q2.hfix139_107_2 i) _)
      ?_).symm
  rw [show colData1 (⟨139, by decide⟩ : Fin 148)
        ((colE1 ⟨107, by decide⟩ 5 (transLenTr ⟨107, by decide⟩ 5 hp) : ↥(reps ⟨107, by decide⟩)) : Coordinate 1)
        T139_107 = colFn colCertDiv_139_107_5.D1 (m := 5) from colCertDiv_139_107_5.bind1,
    show colData2 (⟨139, by decide⟩ : Fin 148)
        ((colE2 ⟨107, by decide⟩ 5 hp : ↥(Q2.reps ⟨107, by decide⟩)) : Coordinate 2)
        Q2.T139_107_2 = colFn colCertDiv_139_107_5.D2 (m := 5) from colCertDiv_139_107_5.bind2]
  rw [alnId_139 j hj]
  exact fastcode_of_div ⟨139, by decide⟩ _ _ _
    ((alnId_139 j hj) ▸ Q2.listedAt (⟨139, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨139, by decide⟩ : Fin 148) hj hq).1) colCertDiv_139_107_5_match


theorem leaf_139_107_10 (hp : 10 < (Q2.transData.getD 107 []).length)
    (j : Nat) (hj : j < (repChars.getD 139 []).length)
    (hq : (normIsRep.getD 139 []).getD j false = true) :
    species (Q2.reps (⟨107, by decide⟩ : Fin 148)) (colE2 ⟨107, by decide⟩ 10 hp)
        (rowE2 (⟨139, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨107, by decide⟩ : Fin 148))
        (colE1 ⟨107, by decide⟩ 10 (transLenTr ⟨107, by decide⟩ 10 hp))
        (rowE1 (⟨139, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨139, by decide⟩ : Fin 148) ⟨107, by decide⟩ _
      (validAt ⟨139, by decide⟩ (listedAt ⟨139, by decide⟩ hj))
      (colE1 ⟨107, by decide⟩ 10 (transLenTr ⟨107, by decide⟩ 10 hp)) T139_107
      hfix139_107 hinj139_107 hcardT139_107
      (fun i => conj_mem_of_fixedPoints _ _ (T139_107 i) (hfix139_107 i) _)
      ⟨139, by decide⟩ ⟨107, by decide⟩ _
      (Q2.validAt ⟨139, by decide⟩ (Q2.listedAt ⟨139, by decide⟩
        (alnCheck_rep ⟨139, by decide⟩ hj hq).1))
      (colE2 ⟨107, by decide⟩ 10 hp) Q2.T139_107_2 Q2.hfix139_107_2 Q2.hinj139_107_2
      Q2.hcardT139_107_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T139_107_2 i) (Q2.hfix139_107_2 i) _)
      ?_).symm
  rw [show colData1 (⟨139, by decide⟩ : Fin 148)
        ((colE1 ⟨107, by decide⟩ 10 (transLenTr ⟨107, by decide⟩ 10 hp) : ↥(reps ⟨107, by decide⟩)) : Coordinate 1)
        T139_107 = colFn colCertDiv_139_107_10.D1 (m := 5) from colCertDiv_139_107_10.bind1,
    show colData2 (⟨139, by decide⟩ : Fin 148)
        ((colE2 ⟨107, by decide⟩ 10 hp : ↥(Q2.reps ⟨107, by decide⟩)) : Coordinate 2)
        Q2.T139_107_2 = colFn colCertDiv_139_107_10.D2 (m := 5) from colCertDiv_139_107_10.bind2]
  rw [alnId_139 j hj]
  exact fastcode_of_div ⟨139, by decide⟩ _ _ _
    ((alnId_139 j hj) ▸ Q2.listedAt (⟨139, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨139, by decide⟩ : Fin 148) hj hq).1) colCertDiv_139_107_10_match


theorem leaf_139_107_15 (hp : 15 < (Q2.transData.getD 107 []).length)
    (j : Nat) (hj : j < (repChars.getD 139 []).length)
    (hq : (normIsRep.getD 139 []).getD j false = true) :
    species (Q2.reps (⟨107, by decide⟩ : Fin 148)) (colE2 ⟨107, by decide⟩ 15 hp)
        (rowE2 (⟨139, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨107, by decide⟩ : Fin 148))
        (colE1 ⟨107, by decide⟩ 15 (transLenTr ⟨107, by decide⟩ 15 hp))
        (rowE1 (⟨139, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨139, by decide⟩ : Fin 148) ⟨107, by decide⟩ _
      (validAt ⟨139, by decide⟩ (listedAt ⟨139, by decide⟩ hj))
      (colE1 ⟨107, by decide⟩ 15 (transLenTr ⟨107, by decide⟩ 15 hp)) T139_107
      hfix139_107 hinj139_107 hcardT139_107
      (fun i => conj_mem_of_fixedPoints _ _ (T139_107 i) (hfix139_107 i) _)
      ⟨139, by decide⟩ ⟨107, by decide⟩ _
      (Q2.validAt ⟨139, by decide⟩ (Q2.listedAt ⟨139, by decide⟩
        (alnCheck_rep ⟨139, by decide⟩ hj hq).1))
      (colE2 ⟨107, by decide⟩ 15 hp) Q2.T139_107_2 Q2.hfix139_107_2 Q2.hinj139_107_2
      Q2.hcardT139_107_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T139_107_2 i) (Q2.hfix139_107_2 i) _)
      ?_).symm
  rw [show colData1 (⟨139, by decide⟩ : Fin 148)
        ((colE1 ⟨107, by decide⟩ 15 (transLenTr ⟨107, by decide⟩ 15 hp) : ↥(reps ⟨107, by decide⟩)) : Coordinate 1)
        T139_107 = colFn colCertDiv_139_107_15.D1 (m := 5) from colCertDiv_139_107_15.bind1,
    show colData2 (⟨139, by decide⟩ : Fin 148)
        ((colE2 ⟨107, by decide⟩ 15 hp : ↥(Q2.reps ⟨107, by decide⟩)) : Coordinate 2)
        Q2.T139_107_2 = colFn colCertDiv_139_107_15.D2 (m := 5) from colCertDiv_139_107_15.bind2]
  rw [alnId_139 j hj]
  exact fastcode_of_div ⟨139, by decide⟩ _ _ _
    ((alnId_139 j hj) ▸ Q2.listedAt (⟨139, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨139, by decide⟩ : Fin 148) hj hq).1) colCertDiv_139_107_15_match


theorem leaf_139_107_20 (hp : 20 < (Q2.transData.getD 107 []).length)
    (j : Nat) (hj : j < (repChars.getD 139 []).length)
    (hq : (normIsRep.getD 139 []).getD j false = true) :
    species (Q2.reps (⟨107, by decide⟩ : Fin 148)) (colE2 ⟨107, by decide⟩ 20 hp)
        (rowE2 (⟨139, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨107, by decide⟩ : Fin 148))
        (colE1 ⟨107, by decide⟩ 20 (transLenTr ⟨107, by decide⟩ 20 hp))
        (rowE1 (⟨139, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨139, by decide⟩ : Fin 148) ⟨107, by decide⟩ _
      (validAt ⟨139, by decide⟩ (listedAt ⟨139, by decide⟩ hj))
      (colE1 ⟨107, by decide⟩ 20 (transLenTr ⟨107, by decide⟩ 20 hp)) T139_107
      hfix139_107 hinj139_107 hcardT139_107
      (fun i => conj_mem_of_fixedPoints _ _ (T139_107 i) (hfix139_107 i) _)
      ⟨139, by decide⟩ ⟨107, by decide⟩ _
      (Q2.validAt ⟨139, by decide⟩ (Q2.listedAt ⟨139, by decide⟩
        (alnCheck_rep ⟨139, by decide⟩ hj hq).1))
      (colE2 ⟨107, by decide⟩ 20 hp) Q2.T139_107_2 Q2.hfix139_107_2 Q2.hinj139_107_2
      Q2.hcardT139_107_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T139_107_2 i) (Q2.hfix139_107_2 i) _)
      colCert_139_107_20.hD ?_).symm
  rw [alnId_139 j hj]


theorem leaf_139_113_0 (hp : 0 < (Q2.transData.getD 113 []).length)
    (j : Nat) (hj : j < (repChars.getD 139 []).length)
    (hq : (normIsRep.getD 139 []).getD j false = true) :
    species (Q2.reps (⟨113, by decide⟩ : Fin 148)) (colE2 ⟨113, by decide⟩ 0 hp)
        (rowE2 (⟨139, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨113, by decide⟩ : Fin 148))
        (colE1 ⟨113, by decide⟩ 0 (transLenTr ⟨113, by decide⟩ 0 hp))
        (rowE1 (⟨139, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨139, by decide⟩ : Fin 148) ⟨113, by decide⟩ _
      (validAt ⟨139, by decide⟩ (listedAt ⟨139, by decide⟩ hj))
      (colE1 ⟨113, by decide⟩ 0 (transLenTr ⟨113, by decide⟩ 0 hp)) T139_113
      hfix139_113 hinj139_113 hcardT139_113
      (fun i => conj_mem_of_fixedPoints _ _ (T139_113 i) (hfix139_113 i) _)
      ⟨139, by decide⟩ ⟨113, by decide⟩ _
      (Q2.validAt ⟨139, by decide⟩ (Q2.listedAt ⟨139, by decide⟩
        (alnCheck_rep ⟨139, by decide⟩ hj hq).1))
      (colE2 ⟨113, by decide⟩ 0 hp) Q2.T139_113_2 Q2.hfix139_113_2 Q2.hinj139_113_2
      Q2.hcardT139_113_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T139_113_2 i) (Q2.hfix139_113_2 i) _)
      colCert_139_113_0.hD ?_).symm
  rw [alnId_139 j hj]


theorem leaf_139_113_1 (hp : 1 < (Q2.transData.getD 113 []).length)
    (j : Nat) (hj : j < (repChars.getD 139 []).length)
    (hq : (normIsRep.getD 139 []).getD j false = true) :
    species (Q2.reps (⟨113, by decide⟩ : Fin 148)) (colE2 ⟨113, by decide⟩ 1 hp)
        (rowE2 (⟨139, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨113, by decide⟩ : Fin 148))
        (colE1 ⟨113, by decide⟩ 1 (transLenTr ⟨113, by decide⟩ 1 hp))
        (rowE1 (⟨139, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨139, by decide⟩ : Fin 148) ⟨113, by decide⟩ _
      (validAt ⟨139, by decide⟩ (listedAt ⟨139, by decide⟩ hj))
      (colE1 ⟨113, by decide⟩ 1 (transLenTr ⟨113, by decide⟩ 1 hp)) T139_113
      hfix139_113 hinj139_113 hcardT139_113
      (fun i => conj_mem_of_fixedPoints _ _ (T139_113 i) (hfix139_113 i) _)
      ⟨139, by decide⟩ ⟨113, by decide⟩ _
      (Q2.validAt ⟨139, by decide⟩ (Q2.listedAt ⟨139, by decide⟩
        (alnCheck_rep ⟨139, by decide⟩ hj hq).1))
      (colE2 ⟨113, by decide⟩ 1 hp) Q2.T139_113_2 Q2.hfix139_113_2 Q2.hinj139_113_2
      Q2.hcardT139_113_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T139_113_2 i) (Q2.hfix139_113_2 i) _)
      colCert_139_113_1.hD ?_).symm
  rw [alnId_139 j hj]


theorem leaf_139_113_2 (hp : 2 < (Q2.transData.getD 113 []).length)
    (j : Nat) (hj : j < (repChars.getD 139 []).length)
    (hq : (normIsRep.getD 139 []).getD j false = true) :
    species (Q2.reps (⟨113, by decide⟩ : Fin 148)) (colE2 ⟨113, by decide⟩ 2 hp)
        (rowE2 (⟨139, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨113, by decide⟩ : Fin 148))
        (colE1 ⟨113, by decide⟩ 2 (transLenTr ⟨113, by decide⟩ 2 hp))
        (rowE1 (⟨139, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨139, by decide⟩ : Fin 148) ⟨113, by decide⟩ _
      (validAt ⟨139, by decide⟩ (listedAt ⟨139, by decide⟩ hj))
      (colE1 ⟨113, by decide⟩ 2 (transLenTr ⟨113, by decide⟩ 2 hp)) T139_113
      hfix139_113 hinj139_113 hcardT139_113
      (fun i => conj_mem_of_fixedPoints _ _ (T139_113 i) (hfix139_113 i) _)
      ⟨139, by decide⟩ ⟨113, by decide⟩ _
      (Q2.validAt ⟨139, by decide⟩ (Q2.listedAt ⟨139, by decide⟩
        (alnCheck_rep ⟨139, by decide⟩ hj hq).1))
      (colE2 ⟨113, by decide⟩ 2 hp) Q2.T139_113_2 Q2.hfix139_113_2 Q2.hinj139_113_2
      Q2.hcardT139_113_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T139_113_2 i) (Q2.hfix139_113_2 i) _)
      colCert_139_113_2.hD ?_).symm
  rw [alnId_139 j hj]


theorem leaf_139_113_3 (hp : 3 < (Q2.transData.getD 113 []).length)
    (j : Nat) (hj : j < (repChars.getD 139 []).length)
    (hq : (normIsRep.getD 139 []).getD j false = true) :
    species (Q2.reps (⟨113, by decide⟩ : Fin 148)) (colE2 ⟨113, by decide⟩ 3 hp)
        (rowE2 (⟨139, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨113, by decide⟩ : Fin 148))
        (colE1 ⟨113, by decide⟩ 3 (transLenTr ⟨113, by decide⟩ 3 hp))
        (rowE1 (⟨139, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨139, by decide⟩ : Fin 148) ⟨113, by decide⟩ _
      (validAt ⟨139, by decide⟩ (listedAt ⟨139, by decide⟩ hj))
      (colE1 ⟨113, by decide⟩ 3 (transLenTr ⟨113, by decide⟩ 3 hp)) T139_113
      hfix139_113 hinj139_113 hcardT139_113
      (fun i => conj_mem_of_fixedPoints _ _ (T139_113 i) (hfix139_113 i) _)
      ⟨139, by decide⟩ ⟨113, by decide⟩ _
      (Q2.validAt ⟨139, by decide⟩ (Q2.listedAt ⟨139, by decide⟩
        (alnCheck_rep ⟨139, by decide⟩ hj hq).1))
      (colE2 ⟨113, by decide⟩ 3 hp) Q2.T139_113_2 Q2.hfix139_113_2 Q2.hinj139_113_2
      Q2.hcardT139_113_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T139_113_2 i) (Q2.hfix139_113_2 i) _)
      colCert_139_113_3.hD ?_).symm
  rw [alnId_139 j hj]


theorem leaf_139_113_4 (hp : 4 < (Q2.transData.getD 113 []).length)
    (j : Nat) (hj : j < (repChars.getD 139 []).length)
    (hq : (normIsRep.getD 139 []).getD j false = true) :
    species (Q2.reps (⟨113, by decide⟩ : Fin 148)) (colE2 ⟨113, by decide⟩ 4 hp)
        (rowE2 (⟨139, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨113, by decide⟩ : Fin 148))
        (colE1 ⟨113, by decide⟩ 4 (transLenTr ⟨113, by decide⟩ 4 hp))
        (rowE1 (⟨139, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨139, by decide⟩ : Fin 148) ⟨113, by decide⟩ _
      (validAt ⟨139, by decide⟩ (listedAt ⟨139, by decide⟩ hj))
      (colE1 ⟨113, by decide⟩ 4 (transLenTr ⟨113, by decide⟩ 4 hp)) T139_113
      hfix139_113 hinj139_113 hcardT139_113
      (fun i => conj_mem_of_fixedPoints _ _ (T139_113 i) (hfix139_113 i) _)
      ⟨139, by decide⟩ ⟨113, by decide⟩ _
      (Q2.validAt ⟨139, by decide⟩ (Q2.listedAt ⟨139, by decide⟩
        (alnCheck_rep ⟨139, by decide⟩ hj hq).1))
      (colE2 ⟨113, by decide⟩ 4 hp) Q2.T139_113_2 Q2.hfix139_113_2 Q2.hinj139_113_2
      Q2.hcardT139_113_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T139_113_2 i) (Q2.hfix139_113_2 i) _)
      colCert_139_113_4.hD ?_).symm
  rw [alnId_139 j hj]


theorem leaf_139_113_5 (hp : 5 < (Q2.transData.getD 113 []).length)
    (j : Nat) (hj : j < (repChars.getD 139 []).length)
    (hq : (normIsRep.getD 139 []).getD j false = true) :
    species (Q2.reps (⟨113, by decide⟩ : Fin 148)) (colE2 ⟨113, by decide⟩ 5 hp)
        (rowE2 (⟨139, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨113, by decide⟩ : Fin 148))
        (colE1 ⟨113, by decide⟩ 5 (transLenTr ⟨113, by decide⟩ 5 hp))
        (rowE1 (⟨139, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨139, by decide⟩ : Fin 148) ⟨113, by decide⟩ _
      (validAt ⟨139, by decide⟩ (listedAt ⟨139, by decide⟩ hj))
      (colE1 ⟨113, by decide⟩ 5 (transLenTr ⟨113, by decide⟩ 5 hp)) T139_113
      hfix139_113 hinj139_113 hcardT139_113
      (fun i => conj_mem_of_fixedPoints _ _ (T139_113 i) (hfix139_113 i) _)
      ⟨139, by decide⟩ ⟨113, by decide⟩ _
      (Q2.validAt ⟨139, by decide⟩ (Q2.listedAt ⟨139, by decide⟩
        (alnCheck_rep ⟨139, by decide⟩ hj hq).1))
      (colE2 ⟨113, by decide⟩ 5 hp) Q2.T139_113_2 Q2.hfix139_113_2 Q2.hinj139_113_2
      Q2.hcardT139_113_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T139_113_2 i) (Q2.hfix139_113_2 i) _)
      colCert_139_113_5.hD ?_).symm
  rw [alnId_139 j hj]


theorem leaf_139_113_10 (hp : 10 < (Q2.transData.getD 113 []).length)
    (j : Nat) (hj : j < (repChars.getD 139 []).length)
    (hq : (normIsRep.getD 139 []).getD j false = true) :
    species (Q2.reps (⟨113, by decide⟩ : Fin 148)) (colE2 ⟨113, by decide⟩ 10 hp)
        (rowE2 (⟨139, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨113, by decide⟩ : Fin 148))
        (colE1 ⟨113, by decide⟩ 10 (transLenTr ⟨113, by decide⟩ 10 hp))
        (rowE1 (⟨139, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨139, by decide⟩ : Fin 148) ⟨113, by decide⟩ _
      (validAt ⟨139, by decide⟩ (listedAt ⟨139, by decide⟩ hj))
      (colE1 ⟨113, by decide⟩ 10 (transLenTr ⟨113, by decide⟩ 10 hp)) T139_113
      hfix139_113 hinj139_113 hcardT139_113
      (fun i => conj_mem_of_fixedPoints _ _ (T139_113 i) (hfix139_113 i) _)
      ⟨139, by decide⟩ ⟨113, by decide⟩ _
      (Q2.validAt ⟨139, by decide⟩ (Q2.listedAt ⟨139, by decide⟩
        (alnCheck_rep ⟨139, by decide⟩ hj hq).1))
      (colE2 ⟨113, by decide⟩ 10 hp) Q2.T139_113_2 Q2.hfix139_113_2 Q2.hinj139_113_2
      Q2.hcardT139_113_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T139_113_2 i) (Q2.hfix139_113_2 i) _)
      ?_).symm
  rw [show colData1 (⟨139, by decide⟩ : Fin 148)
        ((colE1 ⟨113, by decide⟩ 10 (transLenTr ⟨113, by decide⟩ 10 hp) : ↥(reps ⟨113, by decide⟩)) : Coordinate 1)
        T139_113 = colFn colCertDiv_139_113_10.D1 (m := 5) from colCertDiv_139_113_10.bind1,
    show colData2 (⟨139, by decide⟩ : Fin 148)
        ((colE2 ⟨113, by decide⟩ 10 hp : ↥(Q2.reps ⟨113, by decide⟩)) : Coordinate 2)
        Q2.T139_113_2 = colFn colCertDiv_139_113_10.D2 (m := 5) from colCertDiv_139_113_10.bind2]
  rw [alnId_139 j hj]
  exact fastcode_of_div ⟨139, by decide⟩ _ _ _
    ((alnId_139 j hj) ▸ Q2.listedAt (⟨139, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨139, by decide⟩ : Fin 148) hj hq).1) colCertDiv_139_113_10_match


theorem leaf_139_113_15 (hp : 15 < (Q2.transData.getD 113 []).length)
    (j : Nat) (hj : j < (repChars.getD 139 []).length)
    (hq : (normIsRep.getD 139 []).getD j false = true) :
    species (Q2.reps (⟨113, by decide⟩ : Fin 148)) (colE2 ⟨113, by decide⟩ 15 hp)
        (rowE2 (⟨139, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨113, by decide⟩ : Fin 148))
        (colE1 ⟨113, by decide⟩ 15 (transLenTr ⟨113, by decide⟩ 15 hp))
        (rowE1 (⟨139, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨139, by decide⟩ : Fin 148) ⟨113, by decide⟩ _
      (validAt ⟨139, by decide⟩ (listedAt ⟨139, by decide⟩ hj))
      (colE1 ⟨113, by decide⟩ 15 (transLenTr ⟨113, by decide⟩ 15 hp)) T139_113
      hfix139_113 hinj139_113 hcardT139_113
      (fun i => conj_mem_of_fixedPoints _ _ (T139_113 i) (hfix139_113 i) _)
      ⟨139, by decide⟩ ⟨113, by decide⟩ _
      (Q2.validAt ⟨139, by decide⟩ (Q2.listedAt ⟨139, by decide⟩
        (alnCheck_rep ⟨139, by decide⟩ hj hq).1))
      (colE2 ⟨113, by decide⟩ 15 hp) Q2.T139_113_2 Q2.hfix139_113_2 Q2.hinj139_113_2
      Q2.hcardT139_113_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T139_113_2 i) (Q2.hfix139_113_2 i) _)
      ?_).symm
  rw [show colData1 (⟨139, by decide⟩ : Fin 148)
        ((colE1 ⟨113, by decide⟩ 15 (transLenTr ⟨113, by decide⟩ 15 hp) : ↥(reps ⟨113, by decide⟩)) : Coordinate 1)
        T139_113 = colFn colCertDiv_139_113_15.D1 (m := 5) from colCertDiv_139_113_15.bind1,
    show colData2 (⟨139, by decide⟩ : Fin 148)
        ((colE2 ⟨113, by decide⟩ 15 hp : ↥(Q2.reps ⟨113, by decide⟩)) : Coordinate 2)
        Q2.T139_113_2 = colFn colCertDiv_139_113_15.D2 (m := 5) from colCertDiv_139_113_15.bind2]
  rw [alnId_139 j hj]
  exact fastcode_of_div ⟨139, by decide⟩ _ _ _
    ((alnId_139 j hj) ▸ Q2.listedAt (⟨139, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨139, by decide⟩ : Fin 148) hj hq).1) colCertDiv_139_113_15_match


theorem leaf_139_113_20 (hp : 20 < (Q2.transData.getD 113 []).length)
    (j : Nat) (hj : j < (repChars.getD 139 []).length)
    (hq : (normIsRep.getD 139 []).getD j false = true) :
    species (Q2.reps (⟨113, by decide⟩ : Fin 148)) (colE2 ⟨113, by decide⟩ 20 hp)
        (rowE2 (⟨139, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨113, by decide⟩ : Fin 148))
        (colE1 ⟨113, by decide⟩ 20 (transLenTr ⟨113, by decide⟩ 20 hp))
        (rowE1 (⟨139, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨139, by decide⟩ : Fin 148) ⟨113, by decide⟩ _
      (validAt ⟨139, by decide⟩ (listedAt ⟨139, by decide⟩ hj))
      (colE1 ⟨113, by decide⟩ 20 (transLenTr ⟨113, by decide⟩ 20 hp)) T139_113
      hfix139_113 hinj139_113 hcardT139_113
      (fun i => conj_mem_of_fixedPoints _ _ (T139_113 i) (hfix139_113 i) _)
      ⟨139, by decide⟩ ⟨113, by decide⟩ _
      (Q2.validAt ⟨139, by decide⟩ (Q2.listedAt ⟨139, by decide⟩
        (alnCheck_rep ⟨139, by decide⟩ hj hq).1))
      (colE2 ⟨113, by decide⟩ 20 hp) Q2.T139_113_2 Q2.hfix139_113_2 Q2.hinj139_113_2
      Q2.hcardT139_113_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T139_113_2 i) (Q2.hfix139_113_2 i) _)
      ?_).symm
  rw [show colData1 (⟨139, by decide⟩ : Fin 148)
        ((colE1 ⟨113, by decide⟩ 20 (transLenTr ⟨113, by decide⟩ 20 hp) : ↥(reps ⟨113, by decide⟩)) : Coordinate 1)
        T139_113 = colFn colCertDiv_139_113_20.D1 (m := 5) from colCertDiv_139_113_20.bind1,
    show colData2 (⟨139, by decide⟩ : Fin 148)
        ((colE2 ⟨113, by decide⟩ 20 hp : ↥(Q2.reps ⟨113, by decide⟩)) : Coordinate 2)
        Q2.T139_113_2 = colFn colCertDiv_139_113_20.D2 (m := 5) from colCertDiv_139_113_20.bind2]
  rw [alnId_139 j hj]
  exact fastcode_of_div ⟨139, by decide⟩ _ _ _
    ((alnId_139 j hj) ▸ Q2.listedAt (⟨139, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨139, by decide⟩ : Fin 148) hj hq).1) colCertDiv_139_113_20_match


theorem leaf_139_139_0 (hp : 0 < (Q2.transData.getD 139 []).length)
    (j : Nat) (hj : j < (repChars.getD 139 []).length)
    (hq : (normIsRep.getD 139 []).getD j false = true) :
    species (Q2.reps (⟨139, by decide⟩ : Fin 148)) (colE2 ⟨139, by decide⟩ 0 hp)
        (rowE2 (⟨139, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨139, by decide⟩ : Fin 148))
        (colE1 ⟨139, by decide⟩ 0 (transLenTr ⟨139, by decide⟩ 0 hp))
        (rowE1 (⟨139, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨139, by decide⟩ : Fin 148) ⟨139, by decide⟩ _
      (validAt ⟨139, by decide⟩ (listedAt ⟨139, by decide⟩ hj))
      (colE1 ⟨139, by decide⟩ 0 (transLenTr ⟨139, by decide⟩ 0 hp)) T139_139
      hfix139_139 hinj139_139 hcardT139_139
      (fun i => conj_mem_of_fixedPoints _ _ (T139_139 i) (hfix139_139 i) _)
      ⟨139, by decide⟩ ⟨139, by decide⟩ _
      (Q2.validAt ⟨139, by decide⟩ (Q2.listedAt ⟨139, by decide⟩
        (alnCheck_rep ⟨139, by decide⟩ hj hq).1))
      (colE2 ⟨139, by decide⟩ 0 hp) Q2.T139_139_2 Q2.hfix139_139_2 Q2.hinj139_139_2
      Q2.hcardT139_139_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T139_139_2 i) (Q2.hfix139_139_2 i) _)
      colCert_139_139_0.hD ?_).symm
  rw [alnId_139 j hj]


theorem leaf_139_139_1 (hp : 1 < (Q2.transData.getD 139 []).length)
    (j : Nat) (hj : j < (repChars.getD 139 []).length)
    (hq : (normIsRep.getD 139 []).getD j false = true) :
    species (Q2.reps (⟨139, by decide⟩ : Fin 148)) (colE2 ⟨139, by decide⟩ 1 hp)
        (rowE2 (⟨139, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨139, by decide⟩ : Fin 148))
        (colE1 ⟨139, by decide⟩ 1 (transLenTr ⟨139, by decide⟩ 1 hp))
        (rowE1 (⟨139, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨139, by decide⟩ : Fin 148) ⟨139, by decide⟩ _
      (validAt ⟨139, by decide⟩ (listedAt ⟨139, by decide⟩ hj))
      (colE1 ⟨139, by decide⟩ 1 (transLenTr ⟨139, by decide⟩ 1 hp)) T139_139
      hfix139_139 hinj139_139 hcardT139_139
      (fun i => conj_mem_of_fixedPoints _ _ (T139_139 i) (hfix139_139 i) _)
      ⟨139, by decide⟩ ⟨139, by decide⟩ _
      (Q2.validAt ⟨139, by decide⟩ (Q2.listedAt ⟨139, by decide⟩
        (alnCheck_rep ⟨139, by decide⟩ hj hq).1))
      (colE2 ⟨139, by decide⟩ 1 hp) Q2.T139_139_2 Q2.hfix139_139_2 Q2.hinj139_139_2
      Q2.hcardT139_139_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T139_139_2 i) (Q2.hfix139_139_2 i) _)
      colCert_139_139_1.hD ?_).symm
  rw [alnId_139 j hj]


theorem leaf_139_139_2 (hp : 2 < (Q2.transData.getD 139 []).length)
    (j : Nat) (hj : j < (repChars.getD 139 []).length)
    (hq : (normIsRep.getD 139 []).getD j false = true) :
    species (Q2.reps (⟨139, by decide⟩ : Fin 148)) (colE2 ⟨139, by decide⟩ 2 hp)
        (rowE2 (⟨139, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨139, by decide⟩ : Fin 148))
        (colE1 ⟨139, by decide⟩ 2 (transLenTr ⟨139, by decide⟩ 2 hp))
        (rowE1 (⟨139, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨139, by decide⟩ : Fin 148) ⟨139, by decide⟩ _
      (validAt ⟨139, by decide⟩ (listedAt ⟨139, by decide⟩ hj))
      (colE1 ⟨139, by decide⟩ 2 (transLenTr ⟨139, by decide⟩ 2 hp)) T139_139
      hfix139_139 hinj139_139 hcardT139_139
      (fun i => conj_mem_of_fixedPoints _ _ (T139_139 i) (hfix139_139 i) _)
      ⟨139, by decide⟩ ⟨139, by decide⟩ _
      (Q2.validAt ⟨139, by decide⟩ (Q2.listedAt ⟨139, by decide⟩
        (alnCheck_rep ⟨139, by decide⟩ hj hq).1))
      (colE2 ⟨139, by decide⟩ 2 hp) Q2.T139_139_2 Q2.hfix139_139_2 Q2.hinj139_139_2
      Q2.hcardT139_139_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T139_139_2 i) (Q2.hfix139_139_2 i) _)
      colCert_139_139_2.hD ?_).symm
  rw [alnId_139 j hj]


theorem leaf_139_139_3 (hp : 3 < (Q2.transData.getD 139 []).length)
    (j : Nat) (hj : j < (repChars.getD 139 []).length)
    (hq : (normIsRep.getD 139 []).getD j false = true) :
    species (Q2.reps (⟨139, by decide⟩ : Fin 148)) (colE2 ⟨139, by decide⟩ 3 hp)
        (rowE2 (⟨139, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨139, by decide⟩ : Fin 148))
        (colE1 ⟨139, by decide⟩ 3 (transLenTr ⟨139, by decide⟩ 3 hp))
        (rowE1 (⟨139, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨139, by decide⟩ : Fin 148) ⟨139, by decide⟩ _
      (validAt ⟨139, by decide⟩ (listedAt ⟨139, by decide⟩ hj))
      (colE1 ⟨139, by decide⟩ 3 (transLenTr ⟨139, by decide⟩ 3 hp)) T139_139
      hfix139_139 hinj139_139 hcardT139_139
      (fun i => conj_mem_of_fixedPoints _ _ (T139_139 i) (hfix139_139 i) _)
      ⟨139, by decide⟩ ⟨139, by decide⟩ _
      (Q2.validAt ⟨139, by decide⟩ (Q2.listedAt ⟨139, by decide⟩
        (alnCheck_rep ⟨139, by decide⟩ hj hq).1))
      (colE2 ⟨139, by decide⟩ 3 hp) Q2.T139_139_2 Q2.hfix139_139_2 Q2.hinj139_139_2
      Q2.hcardT139_139_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T139_139_2 i) (Q2.hfix139_139_2 i) _)
      colCert_139_139_3.hD ?_).symm
  rw [alnId_139 j hj]


theorem leaf_139_139_4 (hp : 4 < (Q2.transData.getD 139 []).length)
    (j : Nat) (hj : j < (repChars.getD 139 []).length)
    (hq : (normIsRep.getD 139 []).getD j false = true) :
    species (Q2.reps (⟨139, by decide⟩ : Fin 148)) (colE2 ⟨139, by decide⟩ 4 hp)
        (rowE2 (⟨139, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨139, by decide⟩ : Fin 148))
        (colE1 ⟨139, by decide⟩ 4 (transLenTr ⟨139, by decide⟩ 4 hp))
        (rowE1 (⟨139, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨139, by decide⟩ : Fin 148) ⟨139, by decide⟩ _
      (validAt ⟨139, by decide⟩ (listedAt ⟨139, by decide⟩ hj))
      (colE1 ⟨139, by decide⟩ 4 (transLenTr ⟨139, by decide⟩ 4 hp)) T139_139
      hfix139_139 hinj139_139 hcardT139_139
      (fun i => conj_mem_of_fixedPoints _ _ (T139_139 i) (hfix139_139 i) _)
      ⟨139, by decide⟩ ⟨139, by decide⟩ _
      (Q2.validAt ⟨139, by decide⟩ (Q2.listedAt ⟨139, by decide⟩
        (alnCheck_rep ⟨139, by decide⟩ hj hq).1))
      (colE2 ⟨139, by decide⟩ 4 hp) Q2.T139_139_2 Q2.hfix139_139_2 Q2.hinj139_139_2
      Q2.hcardT139_139_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T139_139_2 i) (Q2.hfix139_139_2 i) _)
      colCert_139_139_4.hD ?_).symm
  rw [alnId_139 j hj]


theorem leaf_139_139_5 (hp : 5 < (Q2.transData.getD 139 []).length)
    (j : Nat) (hj : j < (repChars.getD 139 []).length)
    (hq : (normIsRep.getD 139 []).getD j false = true) :
    species (Q2.reps (⟨139, by decide⟩ : Fin 148)) (colE2 ⟨139, by decide⟩ 5 hp)
        (rowE2 (⟨139, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨139, by decide⟩ : Fin 148))
        (colE1 ⟨139, by decide⟩ 5 (transLenTr ⟨139, by decide⟩ 5 hp))
        (rowE1 (⟨139, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨139, by decide⟩ : Fin 148) ⟨139, by decide⟩ _
      (validAt ⟨139, by decide⟩ (listedAt ⟨139, by decide⟩ hj))
      (colE1 ⟨139, by decide⟩ 5 (transLenTr ⟨139, by decide⟩ 5 hp)) T139_139
      hfix139_139 hinj139_139 hcardT139_139
      (fun i => conj_mem_of_fixedPoints _ _ (T139_139 i) (hfix139_139 i) _)
      ⟨139, by decide⟩ ⟨139, by decide⟩ _
      (Q2.validAt ⟨139, by decide⟩ (Q2.listedAt ⟨139, by decide⟩
        (alnCheck_rep ⟨139, by decide⟩ hj hq).1))
      (colE2 ⟨139, by decide⟩ 5 hp) Q2.T139_139_2 Q2.hfix139_139_2 Q2.hinj139_139_2
      Q2.hcardT139_139_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T139_139_2 i) (Q2.hfix139_139_2 i) _)
      colCert_139_139_5.hD ?_).symm
  rw [alnId_139 j hj]


theorem leaf_139_139_6 (hp : 6 < (Q2.transData.getD 139 []).length)
    (j : Nat) (hj : j < (repChars.getD 139 []).length)
    (hq : (normIsRep.getD 139 []).getD j false = true) :
    species (Q2.reps (⟨139, by decide⟩ : Fin 148)) (colE2 ⟨139, by decide⟩ 6 hp)
        (rowE2 (⟨139, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨139, by decide⟩ : Fin 148))
        (colE1 ⟨139, by decide⟩ 6 (transLenTr ⟨139, by decide⟩ 6 hp))
        (rowE1 (⟨139, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨139, by decide⟩ : Fin 148) ⟨139, by decide⟩ _
      (validAt ⟨139, by decide⟩ (listedAt ⟨139, by decide⟩ hj))
      (colE1 ⟨139, by decide⟩ 6 (transLenTr ⟨139, by decide⟩ 6 hp)) T139_139
      hfix139_139 hinj139_139 hcardT139_139
      (fun i => conj_mem_of_fixedPoints _ _ (T139_139 i) (hfix139_139 i) _)
      ⟨139, by decide⟩ ⟨139, by decide⟩ _
      (Q2.validAt ⟨139, by decide⟩ (Q2.listedAt ⟨139, by decide⟩
        (alnCheck_rep ⟨139, by decide⟩ hj hq).1))
      (colE2 ⟨139, by decide⟩ 6 hp) Q2.T139_139_2 Q2.hfix139_139_2 Q2.hinj139_139_2
      Q2.hcardT139_139_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T139_139_2 i) (Q2.hfix139_139_2 i) _)
      colCert_139_139_6.hD ?_).symm
  rw [alnId_139 j hj]


theorem leaf_139_139_7 (hp : 7 < (Q2.transData.getD 139 []).length)
    (j : Nat) (hj : j < (repChars.getD 139 []).length)
    (hq : (normIsRep.getD 139 []).getD j false = true) :
    species (Q2.reps (⟨139, by decide⟩ : Fin 148)) (colE2 ⟨139, by decide⟩ 7 hp)
        (rowE2 (⟨139, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨139, by decide⟩ : Fin 148))
        (colE1 ⟨139, by decide⟩ 7 (transLenTr ⟨139, by decide⟩ 7 hp))
        (rowE1 (⟨139, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨139, by decide⟩ : Fin 148) ⟨139, by decide⟩ _
      (validAt ⟨139, by decide⟩ (listedAt ⟨139, by decide⟩ hj))
      (colE1 ⟨139, by decide⟩ 7 (transLenTr ⟨139, by decide⟩ 7 hp)) T139_139
      hfix139_139 hinj139_139 hcardT139_139
      (fun i => conj_mem_of_fixedPoints _ _ (T139_139 i) (hfix139_139 i) _)
      ⟨139, by decide⟩ ⟨139, by decide⟩ _
      (Q2.validAt ⟨139, by decide⟩ (Q2.listedAt ⟨139, by decide⟩
        (alnCheck_rep ⟨139, by decide⟩ hj hq).1))
      (colE2 ⟨139, by decide⟩ 7 hp) Q2.T139_139_2 Q2.hfix139_139_2 Q2.hinj139_139_2
      Q2.hcardT139_139_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T139_139_2 i) (Q2.hfix139_139_2 i) _)
      colCert_139_139_7.hD ?_).symm
  rw [alnId_139 j hj]


theorem leaf_139_139_8 (hp : 8 < (Q2.transData.getD 139 []).length)
    (j : Nat) (hj : j < (repChars.getD 139 []).length)
    (hq : (normIsRep.getD 139 []).getD j false = true) :
    species (Q2.reps (⟨139, by decide⟩ : Fin 148)) (colE2 ⟨139, by decide⟩ 8 hp)
        (rowE2 (⟨139, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨139, by decide⟩ : Fin 148))
        (colE1 ⟨139, by decide⟩ 8 (transLenTr ⟨139, by decide⟩ 8 hp))
        (rowE1 (⟨139, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨139, by decide⟩ : Fin 148) ⟨139, by decide⟩ _
      (validAt ⟨139, by decide⟩ (listedAt ⟨139, by decide⟩ hj))
      (colE1 ⟨139, by decide⟩ 8 (transLenTr ⟨139, by decide⟩ 8 hp)) T139_139
      hfix139_139 hinj139_139 hcardT139_139
      (fun i => conj_mem_of_fixedPoints _ _ (T139_139 i) (hfix139_139 i) _)
      ⟨139, by decide⟩ ⟨139, by decide⟩ _
      (Q2.validAt ⟨139, by decide⟩ (Q2.listedAt ⟨139, by decide⟩
        (alnCheck_rep ⟨139, by decide⟩ hj hq).1))
      (colE2 ⟨139, by decide⟩ 8 hp) Q2.T139_139_2 Q2.hfix139_139_2 Q2.hinj139_139_2
      Q2.hcardT139_139_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T139_139_2 i) (Q2.hfix139_139_2 i) _)
      colCert_139_139_8.hD ?_).symm
  rw [alnId_139 j hj]


theorem leaf_139_139_9 (hp : 9 < (Q2.transData.getD 139 []).length)
    (j : Nat) (hj : j < (repChars.getD 139 []).length)
    (hq : (normIsRep.getD 139 []).getD j false = true) :
    species (Q2.reps (⟨139, by decide⟩ : Fin 148)) (colE2 ⟨139, by decide⟩ 9 hp)
        (rowE2 (⟨139, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨139, by decide⟩ : Fin 148))
        (colE1 ⟨139, by decide⟩ 9 (transLenTr ⟨139, by decide⟩ 9 hp))
        (rowE1 (⟨139, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨139, by decide⟩ : Fin 148) ⟨139, by decide⟩ _
      (validAt ⟨139, by decide⟩ (listedAt ⟨139, by decide⟩ hj))
      (colE1 ⟨139, by decide⟩ 9 (transLenTr ⟨139, by decide⟩ 9 hp)) T139_139
      hfix139_139 hinj139_139 hcardT139_139
      (fun i => conj_mem_of_fixedPoints _ _ (T139_139 i) (hfix139_139 i) _)
      ⟨139, by decide⟩ ⟨139, by decide⟩ _
      (Q2.validAt ⟨139, by decide⟩ (Q2.listedAt ⟨139, by decide⟩
        (alnCheck_rep ⟨139, by decide⟩ hj hq).1))
      (colE2 ⟨139, by decide⟩ 9 hp) Q2.T139_139_2 Q2.hfix139_139_2 Q2.hinj139_139_2
      Q2.hcardT139_139_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T139_139_2 i) (Q2.hfix139_139_2 i) _)
      colCert_139_139_9.hD ?_).symm
  rw [alnId_139 j hj]


theorem leaf_139_139_10 (hp : 10 < (Q2.transData.getD 139 []).length)
    (j : Nat) (hj : j < (repChars.getD 139 []).length)
    (hq : (normIsRep.getD 139 []).getD j false = true) :
    species (Q2.reps (⟨139, by decide⟩ : Fin 148)) (colE2 ⟨139, by decide⟩ 10 hp)
        (rowE2 (⟨139, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨139, by decide⟩ : Fin 148))
        (colE1 ⟨139, by decide⟩ 10 (transLenTr ⟨139, by decide⟩ 10 hp))
        (rowE1 (⟨139, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨139, by decide⟩ : Fin 148) ⟨139, by decide⟩ _
      (validAt ⟨139, by decide⟩ (listedAt ⟨139, by decide⟩ hj))
      (colE1 ⟨139, by decide⟩ 10 (transLenTr ⟨139, by decide⟩ 10 hp)) T139_139
      hfix139_139 hinj139_139 hcardT139_139
      (fun i => conj_mem_of_fixedPoints _ _ (T139_139 i) (hfix139_139 i) _)
      ⟨139, by decide⟩ ⟨139, by decide⟩ _
      (Q2.validAt ⟨139, by decide⟩ (Q2.listedAt ⟨139, by decide⟩
        (alnCheck_rep ⟨139, by decide⟩ hj hq).1))
      (colE2 ⟨139, by decide⟩ 10 hp) Q2.T139_139_2 Q2.hfix139_139_2 Q2.hinj139_139_2
      Q2.hcardT139_139_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T139_139_2 i) (Q2.hfix139_139_2 i) _)
      colCert_139_139_10.hD ?_).symm
  rw [alnId_139 j hj]


theorem leaf_139_139_11 (hp : 11 < (Q2.transData.getD 139 []).length)
    (j : Nat) (hj : j < (repChars.getD 139 []).length)
    (hq : (normIsRep.getD 139 []).getD j false = true) :
    species (Q2.reps (⟨139, by decide⟩ : Fin 148)) (colE2 ⟨139, by decide⟩ 11 hp)
        (rowE2 (⟨139, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨139, by decide⟩ : Fin 148))
        (colE1 ⟨139, by decide⟩ 11 (transLenTr ⟨139, by decide⟩ 11 hp))
        (rowE1 (⟨139, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨139, by decide⟩ : Fin 148) ⟨139, by decide⟩ _
      (validAt ⟨139, by decide⟩ (listedAt ⟨139, by decide⟩ hj))
      (colE1 ⟨139, by decide⟩ 11 (transLenTr ⟨139, by decide⟩ 11 hp)) T139_139
      hfix139_139 hinj139_139 hcardT139_139
      (fun i => conj_mem_of_fixedPoints _ _ (T139_139 i) (hfix139_139 i) _)
      ⟨139, by decide⟩ ⟨139, by decide⟩ _
      (Q2.validAt ⟨139, by decide⟩ (Q2.listedAt ⟨139, by decide⟩
        (alnCheck_rep ⟨139, by decide⟩ hj hq).1))
      (colE2 ⟨139, by decide⟩ 11 hp) Q2.T139_139_2 Q2.hfix139_139_2 Q2.hinj139_139_2
      Q2.hcardT139_139_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T139_139_2 i) (Q2.hfix139_139_2 i) _)
      colCert_139_139_11.hD ?_).symm
  rw [alnId_139 j hj]


theorem leaf_139_139_12 (hp : 12 < (Q2.transData.getD 139 []).length)
    (j : Nat) (hj : j < (repChars.getD 139 []).length)
    (hq : (normIsRep.getD 139 []).getD j false = true) :
    species (Q2.reps (⟨139, by decide⟩ : Fin 148)) (colE2 ⟨139, by decide⟩ 12 hp)
        (rowE2 (⟨139, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨139, by decide⟩ : Fin 148))
        (colE1 ⟨139, by decide⟩ 12 (transLenTr ⟨139, by decide⟩ 12 hp))
        (rowE1 (⟨139, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨139, by decide⟩ : Fin 148) ⟨139, by decide⟩ _
      (validAt ⟨139, by decide⟩ (listedAt ⟨139, by decide⟩ hj))
      (colE1 ⟨139, by decide⟩ 12 (transLenTr ⟨139, by decide⟩ 12 hp)) T139_139
      hfix139_139 hinj139_139 hcardT139_139
      (fun i => conj_mem_of_fixedPoints _ _ (T139_139 i) (hfix139_139 i) _)
      ⟨139, by decide⟩ ⟨139, by decide⟩ _
      (Q2.validAt ⟨139, by decide⟩ (Q2.listedAt ⟨139, by decide⟩
        (alnCheck_rep ⟨139, by decide⟩ hj hq).1))
      (colE2 ⟨139, by decide⟩ 12 hp) Q2.T139_139_2 Q2.hfix139_139_2 Q2.hinj139_139_2
      Q2.hcardT139_139_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T139_139_2 i) (Q2.hfix139_139_2 i) _)
      colCert_139_139_12.hD ?_).symm
  rw [alnId_139 j hj]


theorem leaf_139_139_13 (hp : 13 < (Q2.transData.getD 139 []).length)
    (j : Nat) (hj : j < (repChars.getD 139 []).length)
    (hq : (normIsRep.getD 139 []).getD j false = true) :
    species (Q2.reps (⟨139, by decide⟩ : Fin 148)) (colE2 ⟨139, by decide⟩ 13 hp)
        (rowE2 (⟨139, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨139, by decide⟩ : Fin 148))
        (colE1 ⟨139, by decide⟩ 13 (transLenTr ⟨139, by decide⟩ 13 hp))
        (rowE1 (⟨139, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨139, by decide⟩ : Fin 148) ⟨139, by decide⟩ _
      (validAt ⟨139, by decide⟩ (listedAt ⟨139, by decide⟩ hj))
      (colE1 ⟨139, by decide⟩ 13 (transLenTr ⟨139, by decide⟩ 13 hp)) T139_139
      hfix139_139 hinj139_139 hcardT139_139
      (fun i => conj_mem_of_fixedPoints _ _ (T139_139 i) (hfix139_139 i) _)
      ⟨139, by decide⟩ ⟨139, by decide⟩ _
      (Q2.validAt ⟨139, by decide⟩ (Q2.listedAt ⟨139, by decide⟩
        (alnCheck_rep ⟨139, by decide⟩ hj hq).1))
      (colE2 ⟨139, by decide⟩ 13 hp) Q2.T139_139_2 Q2.hfix139_139_2 Q2.hinj139_139_2
      Q2.hcardT139_139_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T139_139_2 i) (Q2.hfix139_139_2 i) _)
      colCert_139_139_13.hD ?_).symm
  rw [alnId_139 j hj]


theorem leaf_139_139_14 (hp : 14 < (Q2.transData.getD 139 []).length)
    (j : Nat) (hj : j < (repChars.getD 139 []).length)
    (hq : (normIsRep.getD 139 []).getD j false = true) :
    species (Q2.reps (⟨139, by decide⟩ : Fin 148)) (colE2 ⟨139, by decide⟩ 14 hp)
        (rowE2 (⟨139, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨139, by decide⟩ : Fin 148))
        (colE1 ⟨139, by decide⟩ 14 (transLenTr ⟨139, by decide⟩ 14 hp))
        (rowE1 (⟨139, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨139, by decide⟩ : Fin 148) ⟨139, by decide⟩ _
      (validAt ⟨139, by decide⟩ (listedAt ⟨139, by decide⟩ hj))
      (colE1 ⟨139, by decide⟩ 14 (transLenTr ⟨139, by decide⟩ 14 hp)) T139_139
      hfix139_139 hinj139_139 hcardT139_139
      (fun i => conj_mem_of_fixedPoints _ _ (T139_139 i) (hfix139_139 i) _)
      ⟨139, by decide⟩ ⟨139, by decide⟩ _
      (Q2.validAt ⟨139, by decide⟩ (Q2.listedAt ⟨139, by decide⟩
        (alnCheck_rep ⟨139, by decide⟩ hj hq).1))
      (colE2 ⟨139, by decide⟩ 14 hp) Q2.T139_139_2 Q2.hfix139_139_2 Q2.hinj139_139_2
      Q2.hcardT139_139_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T139_139_2 i) (Q2.hfix139_139_2 i) _)
      colCert_139_139_14.hD ?_).symm
  rw [alnId_139 j hj]


theorem leaf_139_139_15 (hp : 15 < (Q2.transData.getD 139 []).length)
    (j : Nat) (hj : j < (repChars.getD 139 []).length)
    (hq : (normIsRep.getD 139 []).getD j false = true) :
    species (Q2.reps (⟨139, by decide⟩ : Fin 148)) (colE2 ⟨139, by decide⟩ 15 hp)
        (rowE2 (⟨139, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨139, by decide⟩ : Fin 148))
        (colE1 ⟨139, by decide⟩ 15 (transLenTr ⟨139, by decide⟩ 15 hp))
        (rowE1 (⟨139, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨139, by decide⟩ : Fin 148) ⟨139, by decide⟩ _
      (validAt ⟨139, by decide⟩ (listedAt ⟨139, by decide⟩ hj))
      (colE1 ⟨139, by decide⟩ 15 (transLenTr ⟨139, by decide⟩ 15 hp)) T139_139
      hfix139_139 hinj139_139 hcardT139_139
      (fun i => conj_mem_of_fixedPoints _ _ (T139_139 i) (hfix139_139 i) _)
      ⟨139, by decide⟩ ⟨139, by decide⟩ _
      (Q2.validAt ⟨139, by decide⟩ (Q2.listedAt ⟨139, by decide⟩
        (alnCheck_rep ⟨139, by decide⟩ hj hq).1))
      (colE2 ⟨139, by decide⟩ 15 hp) Q2.T139_139_2 Q2.hfix139_139_2 Q2.hinj139_139_2
      Q2.hcardT139_139_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T139_139_2 i) (Q2.hfix139_139_2 i) _)
      colCert_139_139_15.hD ?_).symm
  rw [alnId_139 j hj]


theorem leaf_139_139_16 (hp : 16 < (Q2.transData.getD 139 []).length)
    (j : Nat) (hj : j < (repChars.getD 139 []).length)
    (hq : (normIsRep.getD 139 []).getD j false = true) :
    species (Q2.reps (⟨139, by decide⟩ : Fin 148)) (colE2 ⟨139, by decide⟩ 16 hp)
        (rowE2 (⟨139, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨139, by decide⟩ : Fin 148))
        (colE1 ⟨139, by decide⟩ 16 (transLenTr ⟨139, by decide⟩ 16 hp))
        (rowE1 (⟨139, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨139, by decide⟩ : Fin 148) ⟨139, by decide⟩ _
      (validAt ⟨139, by decide⟩ (listedAt ⟨139, by decide⟩ hj))
      (colE1 ⟨139, by decide⟩ 16 (transLenTr ⟨139, by decide⟩ 16 hp)) T139_139
      hfix139_139 hinj139_139 hcardT139_139
      (fun i => conj_mem_of_fixedPoints _ _ (T139_139 i) (hfix139_139 i) _)
      ⟨139, by decide⟩ ⟨139, by decide⟩ _
      (Q2.validAt ⟨139, by decide⟩ (Q2.listedAt ⟨139, by decide⟩
        (alnCheck_rep ⟨139, by decide⟩ hj hq).1))
      (colE2 ⟨139, by decide⟩ 16 hp) Q2.T139_139_2 Q2.hfix139_139_2 Q2.hinj139_139_2
      Q2.hcardT139_139_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T139_139_2 i) (Q2.hfix139_139_2 i) _)
      colCert_139_139_16.hD ?_).symm
  rw [alnId_139 j hj]


theorem leaf_139_139_17 (hp : 17 < (Q2.transData.getD 139 []).length)
    (j : Nat) (hj : j < (repChars.getD 139 []).length)
    (hq : (normIsRep.getD 139 []).getD j false = true) :
    species (Q2.reps (⟨139, by decide⟩ : Fin 148)) (colE2 ⟨139, by decide⟩ 17 hp)
        (rowE2 (⟨139, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨139, by decide⟩ : Fin 148))
        (colE1 ⟨139, by decide⟩ 17 (transLenTr ⟨139, by decide⟩ 17 hp))
        (rowE1 (⟨139, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨139, by decide⟩ : Fin 148) ⟨139, by decide⟩ _
      (validAt ⟨139, by decide⟩ (listedAt ⟨139, by decide⟩ hj))
      (colE1 ⟨139, by decide⟩ 17 (transLenTr ⟨139, by decide⟩ 17 hp)) T139_139
      hfix139_139 hinj139_139 hcardT139_139
      (fun i => conj_mem_of_fixedPoints _ _ (T139_139 i) (hfix139_139 i) _)
      ⟨139, by decide⟩ ⟨139, by decide⟩ _
      (Q2.validAt ⟨139, by decide⟩ (Q2.listedAt ⟨139, by decide⟩
        (alnCheck_rep ⟨139, by decide⟩ hj hq).1))
      (colE2 ⟨139, by decide⟩ 17 hp) Q2.T139_139_2 Q2.hfix139_139_2 Q2.hinj139_139_2
      Q2.hcardT139_139_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T139_139_2 i) (Q2.hfix139_139_2 i) _)
      colCert_139_139_17.hD ?_).symm
  rw [alnId_139 j hj]


theorem leaf_139_139_18 (hp : 18 < (Q2.transData.getD 139 []).length)
    (j : Nat) (hj : j < (repChars.getD 139 []).length)
    (hq : (normIsRep.getD 139 []).getD j false = true) :
    species (Q2.reps (⟨139, by decide⟩ : Fin 148)) (colE2 ⟨139, by decide⟩ 18 hp)
        (rowE2 (⟨139, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨139, by decide⟩ : Fin 148))
        (colE1 ⟨139, by decide⟩ 18 (transLenTr ⟨139, by decide⟩ 18 hp))
        (rowE1 (⟨139, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨139, by decide⟩ : Fin 148) ⟨139, by decide⟩ _
      (validAt ⟨139, by decide⟩ (listedAt ⟨139, by decide⟩ hj))
      (colE1 ⟨139, by decide⟩ 18 (transLenTr ⟨139, by decide⟩ 18 hp)) T139_139
      hfix139_139 hinj139_139 hcardT139_139
      (fun i => conj_mem_of_fixedPoints _ _ (T139_139 i) (hfix139_139 i) _)
      ⟨139, by decide⟩ ⟨139, by decide⟩ _
      (Q2.validAt ⟨139, by decide⟩ (Q2.listedAt ⟨139, by decide⟩
        (alnCheck_rep ⟨139, by decide⟩ hj hq).1))
      (colE2 ⟨139, by decide⟩ 18 hp) Q2.T139_139_2 Q2.hfix139_139_2 Q2.hinj139_139_2
      Q2.hcardT139_139_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T139_139_2 i) (Q2.hfix139_139_2 i) _)
      colCert_139_139_18.hD ?_).symm
  rw [alnId_139 j hj]


theorem leaf_139_139_19 (hp : 19 < (Q2.transData.getD 139 []).length)
    (j : Nat) (hj : j < (repChars.getD 139 []).length)
    (hq : (normIsRep.getD 139 []).getD j false = true) :
    species (Q2.reps (⟨139, by decide⟩ : Fin 148)) (colE2 ⟨139, by decide⟩ 19 hp)
        (rowE2 (⟨139, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨139, by decide⟩ : Fin 148))
        (colE1 ⟨139, by decide⟩ 19 (transLenTr ⟨139, by decide⟩ 19 hp))
        (rowE1 (⟨139, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨139, by decide⟩ : Fin 148) ⟨139, by decide⟩ _
      (validAt ⟨139, by decide⟩ (listedAt ⟨139, by decide⟩ hj))
      (colE1 ⟨139, by decide⟩ 19 (transLenTr ⟨139, by decide⟩ 19 hp)) T139_139
      hfix139_139 hinj139_139 hcardT139_139
      (fun i => conj_mem_of_fixedPoints _ _ (T139_139 i) (hfix139_139 i) _)
      ⟨139, by decide⟩ ⟨139, by decide⟩ _
      (Q2.validAt ⟨139, by decide⟩ (Q2.listedAt ⟨139, by decide⟩
        (alnCheck_rep ⟨139, by decide⟩ hj hq).1))
      (colE2 ⟨139, by decide⟩ 19 hp) Q2.T139_139_2 Q2.hfix139_139_2 Q2.hinj139_139_2
      Q2.hcardT139_139_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T139_139_2 i) (Q2.hfix139_139_2 i) _)
      colCert_139_139_19.hD ?_).symm
  rw [alnId_139 j hj]


theorem leaf_139_139_20 (hp : 20 < (Q2.transData.getD 139 []).length)
    (j : Nat) (hj : j < (repChars.getD 139 []).length)
    (hq : (normIsRep.getD 139 []).getD j false = true) :
    species (Q2.reps (⟨139, by decide⟩ : Fin 148)) (colE2 ⟨139, by decide⟩ 20 hp)
        (rowE2 (⟨139, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨139, by decide⟩ : Fin 148))
        (colE1 ⟨139, by decide⟩ 20 (transLenTr ⟨139, by decide⟩ 20 hp))
        (rowE1 (⟨139, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨139, by decide⟩ : Fin 148) ⟨139, by decide⟩ _
      (validAt ⟨139, by decide⟩ (listedAt ⟨139, by decide⟩ hj))
      (colE1 ⟨139, by decide⟩ 20 (transLenTr ⟨139, by decide⟩ 20 hp)) T139_139
      hfix139_139 hinj139_139 hcardT139_139
      (fun i => conj_mem_of_fixedPoints _ _ (T139_139 i) (hfix139_139 i) _)
      ⟨139, by decide⟩ ⟨139, by decide⟩ _
      (Q2.validAt ⟨139, by decide⟩ (Q2.listedAt ⟨139, by decide⟩
        (alnCheck_rep ⟨139, by decide⟩ hj hq).1))
      (colE2 ⟨139, by decide⟩ 20 hp) Q2.T139_139_2 Q2.hfix139_139_2 Q2.hinj139_139_2
      Q2.hcardT139_139_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T139_139_2 i) (Q2.hfix139_139_2 i) _)
      colCert_139_139_20.hD ?_).symm
  rw [alnId_139 j hj]


theorem leaf_139_139_21 (hp : 21 < (Q2.transData.getD 139 []).length)
    (j : Nat) (hj : j < (repChars.getD 139 []).length)
    (hq : (normIsRep.getD 139 []).getD j false = true) :
    species (Q2.reps (⟨139, by decide⟩ : Fin 148)) (colE2 ⟨139, by decide⟩ 21 hp)
        (rowE2 (⟨139, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨139, by decide⟩ : Fin 148))
        (colE1 ⟨139, by decide⟩ 21 (transLenTr ⟨139, by decide⟩ 21 hp))
        (rowE1 (⟨139, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨139, by decide⟩ : Fin 148) ⟨139, by decide⟩ _
      (validAt ⟨139, by decide⟩ (listedAt ⟨139, by decide⟩ hj))
      (colE1 ⟨139, by decide⟩ 21 (transLenTr ⟨139, by decide⟩ 21 hp)) T139_139
      hfix139_139 hinj139_139 hcardT139_139
      (fun i => conj_mem_of_fixedPoints _ _ (T139_139 i) (hfix139_139 i) _)
      ⟨139, by decide⟩ ⟨139, by decide⟩ _
      (Q2.validAt ⟨139, by decide⟩ (Q2.listedAt ⟨139, by decide⟩
        (alnCheck_rep ⟨139, by decide⟩ hj hq).1))
      (colE2 ⟨139, by decide⟩ 21 hp) Q2.T139_139_2 Q2.hfix139_139_2 Q2.hinj139_139_2
      Q2.hcardT139_139_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T139_139_2 i) (Q2.hfix139_139_2 i) _)
      colCert_139_139_21.hD ?_).symm
  rw [alnId_139 j hj]


theorem leaf_139_139_22 (hp : 22 < (Q2.transData.getD 139 []).length)
    (j : Nat) (hj : j < (repChars.getD 139 []).length)
    (hq : (normIsRep.getD 139 []).getD j false = true) :
    species (Q2.reps (⟨139, by decide⟩ : Fin 148)) (colE2 ⟨139, by decide⟩ 22 hp)
        (rowE2 (⟨139, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨139, by decide⟩ : Fin 148))
        (colE1 ⟨139, by decide⟩ 22 (transLenTr ⟨139, by decide⟩ 22 hp))
        (rowE1 (⟨139, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨139, by decide⟩ : Fin 148) ⟨139, by decide⟩ _
      (validAt ⟨139, by decide⟩ (listedAt ⟨139, by decide⟩ hj))
      (colE1 ⟨139, by decide⟩ 22 (transLenTr ⟨139, by decide⟩ 22 hp)) T139_139
      hfix139_139 hinj139_139 hcardT139_139
      (fun i => conj_mem_of_fixedPoints _ _ (T139_139 i) (hfix139_139 i) _)
      ⟨139, by decide⟩ ⟨139, by decide⟩ _
      (Q2.validAt ⟨139, by decide⟩ (Q2.listedAt ⟨139, by decide⟩
        (alnCheck_rep ⟨139, by decide⟩ hj hq).1))
      (colE2 ⟨139, by decide⟩ 22 hp) Q2.T139_139_2 Q2.hfix139_139_2 Q2.hinj139_139_2
      Q2.hcardT139_139_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T139_139_2 i) (Q2.hfix139_139_2 i) _)
      colCert_139_139_22.hD ?_).symm
  rw [alnId_139 j hj]


theorem leaf_139_139_23 (hp : 23 < (Q2.transData.getD 139 []).length)
    (j : Nat) (hj : j < (repChars.getD 139 []).length)
    (hq : (normIsRep.getD 139 []).getD j false = true) :
    species (Q2.reps (⟨139, by decide⟩ : Fin 148)) (colE2 ⟨139, by decide⟩ 23 hp)
        (rowE2 (⟨139, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨139, by decide⟩ : Fin 148))
        (colE1 ⟨139, by decide⟩ 23 (transLenTr ⟨139, by decide⟩ 23 hp))
        (rowE1 (⟨139, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨139, by decide⟩ : Fin 148) ⟨139, by decide⟩ _
      (validAt ⟨139, by decide⟩ (listedAt ⟨139, by decide⟩ hj))
      (colE1 ⟨139, by decide⟩ 23 (transLenTr ⟨139, by decide⟩ 23 hp)) T139_139
      hfix139_139 hinj139_139 hcardT139_139
      (fun i => conj_mem_of_fixedPoints _ _ (T139_139 i) (hfix139_139 i) _)
      ⟨139, by decide⟩ ⟨139, by decide⟩ _
      (Q2.validAt ⟨139, by decide⟩ (Q2.listedAt ⟨139, by decide⟩
        (alnCheck_rep ⟨139, by decide⟩ hj hq).1))
      (colE2 ⟨139, by decide⟩ 23 hp) Q2.T139_139_2 Q2.hfix139_139_2 Q2.hinj139_139_2
      Q2.hcardT139_139_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T139_139_2 i) (Q2.hfix139_139_2 i) _)
      colCert_139_139_23.hD ?_).symm
  rw [alnId_139 j hj]


theorem leaf_139_139_24 (hp : 24 < (Q2.transData.getD 139 []).length)
    (j : Nat) (hj : j < (repChars.getD 139 []).length)
    (hq : (normIsRep.getD 139 []).getD j false = true) :
    species (Q2.reps (⟨139, by decide⟩ : Fin 148)) (colE2 ⟨139, by decide⟩ 24 hp)
        (rowE2 (⟨139, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨139, by decide⟩ : Fin 148))
        (colE1 ⟨139, by decide⟩ 24 (transLenTr ⟨139, by decide⟩ 24 hp))
        (rowE1 (⟨139, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨139, by decide⟩ : Fin 148) ⟨139, by decide⟩ _
      (validAt ⟨139, by decide⟩ (listedAt ⟨139, by decide⟩ hj))
      (colE1 ⟨139, by decide⟩ 24 (transLenTr ⟨139, by decide⟩ 24 hp)) T139_139
      hfix139_139 hinj139_139 hcardT139_139
      (fun i => conj_mem_of_fixedPoints _ _ (T139_139 i) (hfix139_139 i) _)
      ⟨139, by decide⟩ ⟨139, by decide⟩ _
      (Q2.validAt ⟨139, by decide⟩ (Q2.listedAt ⟨139, by decide⟩
        (alnCheck_rep ⟨139, by decide⟩ hj hq).1))
      (colE2 ⟨139, by decide⟩ 24 hp) Q2.T139_139_2 Q2.hfix139_139_2 Q2.hinj139_139_2
      Q2.hcardT139_139_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T139_139_2 i) (Q2.hfix139_139_2 i) _)
      colCert_139_139_24.hD ?_).symm
  rw [alnId_139 j hj]


theorem leaf_140_5_0 (hp : 0 < (Q2.transData.getD 5 []).length)
    (j : Nat) (hj : j < (repChars.getD 140 []).length)
    (hq : (normIsRep.getD 140 []).getD j false = true) :
    species (Q2.reps (⟨5, by decide⟩ : Fin 148)) (colE2 ⟨5, by decide⟩ 0 hp)
        (rowE2 (⟨140, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨5, by decide⟩ : Fin 148))
        (colE1 ⟨5, by decide⟩ 0 (transLenTr ⟨5, by decide⟩ 0 hp))
        (rowE1 (⟨140, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨140, by decide⟩ : Fin 148) ⟨5, by decide⟩ _
      (validAt ⟨140, by decide⟩ (listedAt ⟨140, by decide⟩ hj))
      (colE1 ⟨5, by decide⟩ 0 (transLenTr ⟨5, by decide⟩ 0 hp)) T140_5
      hfix140_5 hinj140_5 hcardT140_5
      (fun i => conj_mem_of_fixedPoints _ _ (T140_5 i) (hfix140_5 i) _)
      ⟨140, by decide⟩ ⟨5, by decide⟩ _
      (Q2.validAt ⟨140, by decide⟩ (Q2.listedAt ⟨140, by decide⟩
        (alnCheck_rep ⟨140, by decide⟩ hj hq).1))
      (colE2 ⟨5, by decide⟩ 0 hp) Q2.T140_5_2 Q2.hfix140_5_2 Q2.hinj140_5_2
      Q2.hcardT140_5_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T140_5_2 i) (Q2.hfix140_5_2 i) _)
      colCert_140_5_0.hD ?_).symm
  rw [alnId_140 j hj]


theorem leaf_140_5_1 (hp : 1 < (Q2.transData.getD 5 []).length)
    (j : Nat) (hj : j < (repChars.getD 140 []).length)
    (hq : (normIsRep.getD 140 []).getD j false = true) :
    species (Q2.reps (⟨5, by decide⟩ : Fin 148)) (colE2 ⟨5, by decide⟩ 1 hp)
        (rowE2 (⟨140, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨5, by decide⟩ : Fin 148))
        (colE1 ⟨5, by decide⟩ 1 (transLenTr ⟨5, by decide⟩ 1 hp))
        (rowE1 (⟨140, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨140, by decide⟩ : Fin 148) ⟨5, by decide⟩ _
      (validAt ⟨140, by decide⟩ (listedAt ⟨140, by decide⟩ hj))
      (colE1 ⟨5, by decide⟩ 1 (transLenTr ⟨5, by decide⟩ 1 hp)) T140_5
      hfix140_5 hinj140_5 hcardT140_5
      (fun i => conj_mem_of_fixedPoints _ _ (T140_5 i) (hfix140_5 i) _)
      ⟨140, by decide⟩ ⟨5, by decide⟩ _
      (Q2.validAt ⟨140, by decide⟩ (Q2.listedAt ⟨140, by decide⟩
        (alnCheck_rep ⟨140, by decide⟩ hj hq).1))
      (colE2 ⟨5, by decide⟩ 1 hp) Q2.T140_5_2 Q2.hfix140_5_2 Q2.hinj140_5_2
      Q2.hcardT140_5_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T140_5_2 i) (Q2.hfix140_5_2 i) _)
      ?_).symm
  rw [show colData1 (⟨140, by decide⟩ : Fin 148)
        ((colE1 ⟨5, by decide⟩ 1 (transLenTr ⟨5, by decide⟩ 1 hp) : ↥(reps ⟨5, by decide⟩)) : Coordinate 1)
        T140_5 = colFn colCertDiv_140_5_1.D1 (m := 5) from colCertDiv_140_5_1.bind1,
    show colData2 (⟨140, by decide⟩ : Fin 148)
        ((colE2 ⟨5, by decide⟩ 1 hp : ↥(Q2.reps ⟨5, by decide⟩)) : Coordinate 2)
        Q2.T140_5_2 = colFn colCertDiv_140_5_1.D2 (m := 5) from colCertDiv_140_5_1.bind2]
  rw [alnId_140 j hj]
  exact fastcode_of_div ⟨140, by decide⟩ _ _ _
    ((alnId_140 j hj) ▸ Q2.listedAt (⟨140, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨140, by decide⟩ : Fin 148) hj hq).1) colCertDiv_140_5_1_match


theorem leaf_140_5_2 (hp : 2 < (Q2.transData.getD 5 []).length)
    (j : Nat) (hj : j < (repChars.getD 140 []).length)
    (hq : (normIsRep.getD 140 []).getD j false = true) :
    species (Q2.reps (⟨5, by decide⟩ : Fin 148)) (colE2 ⟨5, by decide⟩ 2 hp)
        (rowE2 (⟨140, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨5, by decide⟩ : Fin 148))
        (colE1 ⟨5, by decide⟩ 2 (transLenTr ⟨5, by decide⟩ 2 hp))
        (rowE1 (⟨140, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨140, by decide⟩ : Fin 148) ⟨5, by decide⟩ _
      (validAt ⟨140, by decide⟩ (listedAt ⟨140, by decide⟩ hj))
      (colE1 ⟨5, by decide⟩ 2 (transLenTr ⟨5, by decide⟩ 2 hp)) T140_5
      hfix140_5 hinj140_5 hcardT140_5
      (fun i => conj_mem_of_fixedPoints _ _ (T140_5 i) (hfix140_5 i) _)
      ⟨140, by decide⟩ ⟨5, by decide⟩ _
      (Q2.validAt ⟨140, by decide⟩ (Q2.listedAt ⟨140, by decide⟩
        (alnCheck_rep ⟨140, by decide⟩ hj hq).1))
      (colE2 ⟨5, by decide⟩ 2 hp) Q2.T140_5_2 Q2.hfix140_5_2 Q2.hinj140_5_2
      Q2.hcardT140_5_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T140_5_2 i) (Q2.hfix140_5_2 i) _)
      ?_).symm
  rw [show colData1 (⟨140, by decide⟩ : Fin 148)
        ((colE1 ⟨5, by decide⟩ 2 (transLenTr ⟨5, by decide⟩ 2 hp) : ↥(reps ⟨5, by decide⟩)) : Coordinate 1)
        T140_5 = colFn colCertDiv_140_5_2.D1 (m := 5) from colCertDiv_140_5_2.bind1,
    show colData2 (⟨140, by decide⟩ : Fin 148)
        ((colE2 ⟨5, by decide⟩ 2 hp : ↥(Q2.reps ⟨5, by decide⟩)) : Coordinate 2)
        Q2.T140_5_2 = colFn colCertDiv_140_5_2.D2 (m := 5) from colCertDiv_140_5_2.bind2]
  rw [alnId_140 j hj]
  exact fastcode_of_div ⟨140, by decide⟩ _ _ _
    ((alnId_140 j hj) ▸ Q2.listedAt (⟨140, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨140, by decide⟩ : Fin 148) hj hq).1) colCertDiv_140_5_2_match


theorem leaf_140_5_3 (hp : 3 < (Q2.transData.getD 5 []).length)
    (j : Nat) (hj : j < (repChars.getD 140 []).length)
    (hq : (normIsRep.getD 140 []).getD j false = true) :
    species (Q2.reps (⟨5, by decide⟩ : Fin 148)) (colE2 ⟨5, by decide⟩ 3 hp)
        (rowE2 (⟨140, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨5, by decide⟩ : Fin 148))
        (colE1 ⟨5, by decide⟩ 3 (transLenTr ⟨5, by decide⟩ 3 hp))
        (rowE1 (⟨140, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨140, by decide⟩ : Fin 148) ⟨5, by decide⟩ _
      (validAt ⟨140, by decide⟩ (listedAt ⟨140, by decide⟩ hj))
      (colE1 ⟨5, by decide⟩ 3 (transLenTr ⟨5, by decide⟩ 3 hp)) T140_5
      hfix140_5 hinj140_5 hcardT140_5
      (fun i => conj_mem_of_fixedPoints _ _ (T140_5 i) (hfix140_5 i) _)
      ⟨140, by decide⟩ ⟨5, by decide⟩ _
      (Q2.validAt ⟨140, by decide⟩ (Q2.listedAt ⟨140, by decide⟩
        (alnCheck_rep ⟨140, by decide⟩ hj hq).1))
      (colE2 ⟨5, by decide⟩ 3 hp) Q2.T140_5_2 Q2.hfix140_5_2 Q2.hinj140_5_2
      Q2.hcardT140_5_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T140_5_2 i) (Q2.hfix140_5_2 i) _)
      ?_).symm
  rw [show colData1 (⟨140, by decide⟩ : Fin 148)
        ((colE1 ⟨5, by decide⟩ 3 (transLenTr ⟨5, by decide⟩ 3 hp) : ↥(reps ⟨5, by decide⟩)) : Coordinate 1)
        T140_5 = colFn colCertDiv_140_5_3.D1 (m := 5) from colCertDiv_140_5_3.bind1,
    show colData2 (⟨140, by decide⟩ : Fin 148)
        ((colE2 ⟨5, by decide⟩ 3 hp : ↥(Q2.reps ⟨5, by decide⟩)) : Coordinate 2)
        Q2.T140_5_2 = colFn colCertDiv_140_5_3.D2 (m := 5) from colCertDiv_140_5_3.bind2]
  rw [alnId_140 j hj]
  exact fastcode_of_div ⟨140, by decide⟩ _ _ _
    ((alnId_140 j hj) ▸ Q2.listedAt (⟨140, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨140, by decide⟩ : Fin 148) hj hq).1) colCertDiv_140_5_3_match


theorem leaf_140_5_4 (hp : 4 < (Q2.transData.getD 5 []).length)
    (j : Nat) (hj : j < (repChars.getD 140 []).length)
    (hq : (normIsRep.getD 140 []).getD j false = true) :
    species (Q2.reps (⟨5, by decide⟩ : Fin 148)) (colE2 ⟨5, by decide⟩ 4 hp)
        (rowE2 (⟨140, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨5, by decide⟩ : Fin 148))
        (colE1 ⟨5, by decide⟩ 4 (transLenTr ⟨5, by decide⟩ 4 hp))
        (rowE1 (⟨140, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨140, by decide⟩ : Fin 148) ⟨5, by decide⟩ _
      (validAt ⟨140, by decide⟩ (listedAt ⟨140, by decide⟩ hj))
      (colE1 ⟨5, by decide⟩ 4 (transLenTr ⟨5, by decide⟩ 4 hp)) T140_5
      hfix140_5 hinj140_5 hcardT140_5
      (fun i => conj_mem_of_fixedPoints _ _ (T140_5 i) (hfix140_5 i) _)
      ⟨140, by decide⟩ ⟨5, by decide⟩ _
      (Q2.validAt ⟨140, by decide⟩ (Q2.listedAt ⟨140, by decide⟩
        (alnCheck_rep ⟨140, by decide⟩ hj hq).1))
      (colE2 ⟨5, by decide⟩ 4 hp) Q2.T140_5_2 Q2.hfix140_5_2 Q2.hinj140_5_2
      Q2.hcardT140_5_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T140_5_2 i) (Q2.hfix140_5_2 i) _)
      ?_).symm
  rw [show colData1 (⟨140, by decide⟩ : Fin 148)
        ((colE1 ⟨5, by decide⟩ 4 (transLenTr ⟨5, by decide⟩ 4 hp) : ↥(reps ⟨5, by decide⟩)) : Coordinate 1)
        T140_5 = colFn colCertDiv_140_5_4.D1 (m := 5) from colCertDiv_140_5_4.bind1,
    show colData2 (⟨140, by decide⟩ : Fin 148)
        ((colE2 ⟨5, by decide⟩ 4 hp : ↥(Q2.reps ⟨5, by decide⟩)) : Coordinate 2)
        Q2.T140_5_2 = colFn colCertDiv_140_5_4.D2 (m := 5) from colCertDiv_140_5_4.bind2]
  rw [alnId_140 j hj]
  exact fastcode_of_div ⟨140, by decide⟩ _ _ _
    ((alnId_140 j hj) ▸ Q2.listedAt (⟨140, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨140, by decide⟩ : Fin 148) hj hq).1) colCertDiv_140_5_4_match


theorem leaf_140_10_0 (hp : 0 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 140 []).length)
    (hq : (normIsRep.getD 140 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 0 hp)
        (rowE2 (⟨140, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 0 (transLenTr ⟨10, by decide⟩ 0 hp))
        (rowE1 (⟨140, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨140, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨140, by decide⟩ (listedAt ⟨140, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 0 (transLenTr ⟨10, by decide⟩ 0 hp)) T140_10
      hfix140_10 hinj140_10 hcardT140_10
      (fun i => conj_mem_of_fixedPoints _ _ (T140_10 i) (hfix140_10 i) _)
      ⟨140, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨140, by decide⟩ (Q2.listedAt ⟨140, by decide⟩
        (alnCheck_rep ⟨140, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 0 hp) Q2.T140_10_2 Q2.hfix140_10_2 Q2.hinj140_10_2
      Q2.hcardT140_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T140_10_2 i) (Q2.hfix140_10_2 i) _)
      colCert_140_10_0.hD ?_).symm
  rw [alnId_140 j hj]


theorem leaf_140_10_1 (hp : 1 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 140 []).length)
    (hq : (normIsRep.getD 140 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 1 hp)
        (rowE2 (⟨140, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 1 (transLenTr ⟨10, by decide⟩ 1 hp))
        (rowE1 (⟨140, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨140, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨140, by decide⟩ (listedAt ⟨140, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 1 (transLenTr ⟨10, by decide⟩ 1 hp)) T140_10
      hfix140_10 hinj140_10 hcardT140_10
      (fun i => conj_mem_of_fixedPoints _ _ (T140_10 i) (hfix140_10 i) _)
      ⟨140, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨140, by decide⟩ (Q2.listedAt ⟨140, by decide⟩
        (alnCheck_rep ⟨140, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 1 hp) Q2.T140_10_2 Q2.hfix140_10_2 Q2.hinj140_10_2
      Q2.hcardT140_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T140_10_2 i) (Q2.hfix140_10_2 i) _)
      colCert_140_10_1.hD ?_).symm
  rw [alnId_140 j hj]


theorem leaf_140_10_2 (hp : 2 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 140 []).length)
    (hq : (normIsRep.getD 140 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 2 hp)
        (rowE2 (⟨140, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 2 (transLenTr ⟨10, by decide⟩ 2 hp))
        (rowE1 (⟨140, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨140, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨140, by decide⟩ (listedAt ⟨140, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 2 (transLenTr ⟨10, by decide⟩ 2 hp)) T140_10
      hfix140_10 hinj140_10 hcardT140_10
      (fun i => conj_mem_of_fixedPoints _ _ (T140_10 i) (hfix140_10 i) _)
      ⟨140, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨140, by decide⟩ (Q2.listedAt ⟨140, by decide⟩
        (alnCheck_rep ⟨140, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 2 hp) Q2.T140_10_2 Q2.hfix140_10_2 Q2.hinj140_10_2
      Q2.hcardT140_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T140_10_2 i) (Q2.hfix140_10_2 i) _)
      colCert_140_10_2.hD ?_).symm
  rw [alnId_140 j hj]


theorem leaf_140_10_3 (hp : 3 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 140 []).length)
    (hq : (normIsRep.getD 140 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 3 hp)
        (rowE2 (⟨140, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 3 (transLenTr ⟨10, by decide⟩ 3 hp))
        (rowE1 (⟨140, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨140, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨140, by decide⟩ (listedAt ⟨140, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 3 (transLenTr ⟨10, by decide⟩ 3 hp)) T140_10
      hfix140_10 hinj140_10 hcardT140_10
      (fun i => conj_mem_of_fixedPoints _ _ (T140_10 i) (hfix140_10 i) _)
      ⟨140, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨140, by decide⟩ (Q2.listedAt ⟨140, by decide⟩
        (alnCheck_rep ⟨140, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 3 hp) Q2.T140_10_2 Q2.hfix140_10_2 Q2.hinj140_10_2
      Q2.hcardT140_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T140_10_2 i) (Q2.hfix140_10_2 i) _)
      colCert_140_10_3.hD ?_).symm
  rw [alnId_140 j hj]


theorem leaf_140_10_4 (hp : 4 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 140 []).length)
    (hq : (normIsRep.getD 140 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 4 hp)
        (rowE2 (⟨140, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 4 (transLenTr ⟨10, by decide⟩ 4 hp))
        (rowE1 (⟨140, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨140, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨140, by decide⟩ (listedAt ⟨140, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 4 (transLenTr ⟨10, by decide⟩ 4 hp)) T140_10
      hfix140_10 hinj140_10 hcardT140_10
      (fun i => conj_mem_of_fixedPoints _ _ (T140_10 i) (hfix140_10 i) _)
      ⟨140, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨140, by decide⟩ (Q2.listedAt ⟨140, by decide⟩
        (alnCheck_rep ⟨140, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 4 hp) Q2.T140_10_2 Q2.hfix140_10_2 Q2.hinj140_10_2
      Q2.hcardT140_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T140_10_2 i) (Q2.hfix140_10_2 i) _)
      colCert_140_10_4.hD ?_).symm
  rw [alnId_140 j hj]


theorem leaf_140_12_0 (hp : 0 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 140 []).length)
    (hq : (normIsRep.getD 140 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 0 hp)
        (rowE2 (⟨140, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp))
        (rowE1 (⟨140, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨140, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨140, by decide⟩ (listedAt ⟨140, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp)) T140_12
      hfix140_12 hinj140_12 hcardT140_12
      (fun i => conj_mem_of_fixedPoints _ _ (T140_12 i) (hfix140_12 i) _)
      ⟨140, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨140, by decide⟩ (Q2.listedAt ⟨140, by decide⟩
        (alnCheck_rep ⟨140, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 0 hp) Q2.T140_12_2 Q2.hfix140_12_2 Q2.hinj140_12_2
      Q2.hcardT140_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T140_12_2 i) (Q2.hfix140_12_2 i) _)
      colCert_140_12_0.hD ?_).symm
  rw [alnId_140 j hj]


theorem leaf_140_12_1 (hp : 1 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 140 []).length)
    (hq : (normIsRep.getD 140 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 1 hp)
        (rowE2 (⟨140, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp))
        (rowE1 (⟨140, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨140, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨140, by decide⟩ (listedAt ⟨140, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp)) T140_12
      hfix140_12 hinj140_12 hcardT140_12
      (fun i => conj_mem_of_fixedPoints _ _ (T140_12 i) (hfix140_12 i) _)
      ⟨140, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨140, by decide⟩ (Q2.listedAt ⟨140, by decide⟩
        (alnCheck_rep ⟨140, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 1 hp) Q2.T140_12_2 Q2.hfix140_12_2 Q2.hinj140_12_2
      Q2.hcardT140_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T140_12_2 i) (Q2.hfix140_12_2 i) _)
      colCert_140_12_1.hD ?_).symm
  rw [alnId_140 j hj]


theorem leaf_140_12_2 (hp : 2 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 140 []).length)
    (hq : (normIsRep.getD 140 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 2 hp)
        (rowE2 (⟨140, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp))
        (rowE1 (⟨140, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨140, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨140, by decide⟩ (listedAt ⟨140, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp)) T140_12
      hfix140_12 hinj140_12 hcardT140_12
      (fun i => conj_mem_of_fixedPoints _ _ (T140_12 i) (hfix140_12 i) _)
      ⟨140, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨140, by decide⟩ (Q2.listedAt ⟨140, by decide⟩
        (alnCheck_rep ⟨140, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 2 hp) Q2.T140_12_2 Q2.hfix140_12_2 Q2.hinj140_12_2
      Q2.hcardT140_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T140_12_2 i) (Q2.hfix140_12_2 i) _)
      colCert_140_12_2.hD ?_).symm
  rw [alnId_140 j hj]


theorem leaf_140_12_3 (hp : 3 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 140 []).length)
    (hq : (normIsRep.getD 140 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 3 hp)
        (rowE2 (⟨140, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp))
        (rowE1 (⟨140, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨140, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨140, by decide⟩ (listedAt ⟨140, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp)) T140_12
      hfix140_12 hinj140_12 hcardT140_12
      (fun i => conj_mem_of_fixedPoints _ _ (T140_12 i) (hfix140_12 i) _)
      ⟨140, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨140, by decide⟩ (Q2.listedAt ⟨140, by decide⟩
        (alnCheck_rep ⟨140, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 3 hp) Q2.T140_12_2 Q2.hfix140_12_2 Q2.hinj140_12_2
      Q2.hcardT140_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T140_12_2 i) (Q2.hfix140_12_2 i) _)
      colCert_140_12_3.hD ?_).symm
  rw [alnId_140 j hj]


theorem leaf_140_12_4 (hp : 4 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 140 []).length)
    (hq : (normIsRep.getD 140 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 4 hp)
        (rowE2 (⟨140, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp))
        (rowE1 (⟨140, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨140, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨140, by decide⟩ (listedAt ⟨140, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp)) T140_12
      hfix140_12 hinj140_12 hcardT140_12
      (fun i => conj_mem_of_fixedPoints _ _ (T140_12 i) (hfix140_12 i) _)
      ⟨140, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨140, by decide⟩ (Q2.listedAt ⟨140, by decide⟩
        (alnCheck_rep ⟨140, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 4 hp) Q2.T140_12_2 Q2.hfix140_12_2 Q2.hinj140_12_2
      Q2.hcardT140_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T140_12_2 i) (Q2.hfix140_12_2 i) _)
      colCert_140_12_4.hD ?_).symm
  rw [alnId_140 j hj]


theorem leaf_140_23_0 (hp : 0 < (Q2.transData.getD 23 []).length)
    (j : Nat) (hj : j < (repChars.getD 140 []).length)
    (hq : (normIsRep.getD 140 []).getD j false = true) :
    species (Q2.reps (⟨23, by decide⟩ : Fin 148)) (colE2 ⟨23, by decide⟩ 0 hp)
        (rowE2 (⟨140, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨23, by decide⟩ : Fin 148))
        (colE1 ⟨23, by decide⟩ 0 (transLenTr ⟨23, by decide⟩ 0 hp))
        (rowE1 (⟨140, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨140, by decide⟩ : Fin 148) ⟨23, by decide⟩ _
      (validAt ⟨140, by decide⟩ (listedAt ⟨140, by decide⟩ hj))
      (colE1 ⟨23, by decide⟩ 0 (transLenTr ⟨23, by decide⟩ 0 hp)) T140_23
      hfix140_23 hinj140_23 hcardT140_23
      (fun i => conj_mem_of_fixedPoints _ _ (T140_23 i) (hfix140_23 i) _)
      ⟨140, by decide⟩ ⟨23, by decide⟩ _
      (Q2.validAt ⟨140, by decide⟩ (Q2.listedAt ⟨140, by decide⟩
        (alnCheck_rep ⟨140, by decide⟩ hj hq).1))
      (colE2 ⟨23, by decide⟩ 0 hp) Q2.T140_23_2 Q2.hfix140_23_2 Q2.hinj140_23_2
      Q2.hcardT140_23_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T140_23_2 i) (Q2.hfix140_23_2 i) _)
      colCert_140_23_0.hD ?_).symm
  rw [alnId_140 j hj]


theorem leaf_140_23_1 (hp : 1 < (Q2.transData.getD 23 []).length)
    (j : Nat) (hj : j < (repChars.getD 140 []).length)
    (hq : (normIsRep.getD 140 []).getD j false = true) :
    species (Q2.reps (⟨23, by decide⟩ : Fin 148)) (colE2 ⟨23, by decide⟩ 1 hp)
        (rowE2 (⟨140, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨23, by decide⟩ : Fin 148))
        (colE1 ⟨23, by decide⟩ 1 (transLenTr ⟨23, by decide⟩ 1 hp))
        (rowE1 (⟨140, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨140, by decide⟩ : Fin 148) ⟨23, by decide⟩ _
      (validAt ⟨140, by decide⟩ (listedAt ⟨140, by decide⟩ hj))
      (colE1 ⟨23, by decide⟩ 1 (transLenTr ⟨23, by decide⟩ 1 hp)) T140_23
      hfix140_23 hinj140_23 hcardT140_23
      (fun i => conj_mem_of_fixedPoints _ _ (T140_23 i) (hfix140_23 i) _)
      ⟨140, by decide⟩ ⟨23, by decide⟩ _
      (Q2.validAt ⟨140, by decide⟩ (Q2.listedAt ⟨140, by decide⟩
        (alnCheck_rep ⟨140, by decide⟩ hj hq).1))
      (colE2 ⟨23, by decide⟩ 1 hp) Q2.T140_23_2 Q2.hfix140_23_2 Q2.hinj140_23_2
      Q2.hcardT140_23_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T140_23_2 i) (Q2.hfix140_23_2 i) _)
      colCert_140_23_1.hD ?_).symm
  rw [alnId_140 j hj]


theorem leaf_140_23_2 (hp : 2 < (Q2.transData.getD 23 []).length)
    (j : Nat) (hj : j < (repChars.getD 140 []).length)
    (hq : (normIsRep.getD 140 []).getD j false = true) :
    species (Q2.reps (⟨23, by decide⟩ : Fin 148)) (colE2 ⟨23, by decide⟩ 2 hp)
        (rowE2 (⟨140, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨23, by decide⟩ : Fin 148))
        (colE1 ⟨23, by decide⟩ 2 (transLenTr ⟨23, by decide⟩ 2 hp))
        (rowE1 (⟨140, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨140, by decide⟩ : Fin 148) ⟨23, by decide⟩ _
      (validAt ⟨140, by decide⟩ (listedAt ⟨140, by decide⟩ hj))
      (colE1 ⟨23, by decide⟩ 2 (transLenTr ⟨23, by decide⟩ 2 hp)) T140_23
      hfix140_23 hinj140_23 hcardT140_23
      (fun i => conj_mem_of_fixedPoints _ _ (T140_23 i) (hfix140_23 i) _)
      ⟨140, by decide⟩ ⟨23, by decide⟩ _
      (Q2.validAt ⟨140, by decide⟩ (Q2.listedAt ⟨140, by decide⟩
        (alnCheck_rep ⟨140, by decide⟩ hj hq).1))
      (colE2 ⟨23, by decide⟩ 2 hp) Q2.T140_23_2 Q2.hfix140_23_2 Q2.hinj140_23_2
      Q2.hcardT140_23_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T140_23_2 i) (Q2.hfix140_23_2 i) _)
      colCert_140_23_2.hD ?_).symm
  rw [alnId_140 j hj]


theorem leaf_140_23_3 (hp : 3 < (Q2.transData.getD 23 []).length)
    (j : Nat) (hj : j < (repChars.getD 140 []).length)
    (hq : (normIsRep.getD 140 []).getD j false = true) :
    species (Q2.reps (⟨23, by decide⟩ : Fin 148)) (colE2 ⟨23, by decide⟩ 3 hp)
        (rowE2 (⟨140, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨23, by decide⟩ : Fin 148))
        (colE1 ⟨23, by decide⟩ 3 (transLenTr ⟨23, by decide⟩ 3 hp))
        (rowE1 (⟨140, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨140, by decide⟩ : Fin 148) ⟨23, by decide⟩ _
      (validAt ⟨140, by decide⟩ (listedAt ⟨140, by decide⟩ hj))
      (colE1 ⟨23, by decide⟩ 3 (transLenTr ⟨23, by decide⟩ 3 hp)) T140_23
      hfix140_23 hinj140_23 hcardT140_23
      (fun i => conj_mem_of_fixedPoints _ _ (T140_23 i) (hfix140_23 i) _)
      ⟨140, by decide⟩ ⟨23, by decide⟩ _
      (Q2.validAt ⟨140, by decide⟩ (Q2.listedAt ⟨140, by decide⟩
        (alnCheck_rep ⟨140, by decide⟩ hj hq).1))
      (colE2 ⟨23, by decide⟩ 3 hp) Q2.T140_23_2 Q2.hfix140_23_2 Q2.hinj140_23_2
      Q2.hcardT140_23_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T140_23_2 i) (Q2.hfix140_23_2 i) _)
      colCert_140_23_3.hD ?_).symm
  rw [alnId_140 j hj]


theorem leaf_140_23_4 (hp : 4 < (Q2.transData.getD 23 []).length)
    (j : Nat) (hj : j < (repChars.getD 140 []).length)
    (hq : (normIsRep.getD 140 []).getD j false = true) :
    species (Q2.reps (⟨23, by decide⟩ : Fin 148)) (colE2 ⟨23, by decide⟩ 4 hp)
        (rowE2 (⟨140, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨23, by decide⟩ : Fin 148))
        (colE1 ⟨23, by decide⟩ 4 (transLenTr ⟨23, by decide⟩ 4 hp))
        (rowE1 (⟨140, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨140, by decide⟩ : Fin 148) ⟨23, by decide⟩ _
      (validAt ⟨140, by decide⟩ (listedAt ⟨140, by decide⟩ hj))
      (colE1 ⟨23, by decide⟩ 4 (transLenTr ⟨23, by decide⟩ 4 hp)) T140_23
      hfix140_23 hinj140_23 hcardT140_23
      (fun i => conj_mem_of_fixedPoints _ _ (T140_23 i) (hfix140_23 i) _)
      ⟨140, by decide⟩ ⟨23, by decide⟩ _
      (Q2.validAt ⟨140, by decide⟩ (Q2.listedAt ⟨140, by decide⟩
        (alnCheck_rep ⟨140, by decide⟩ hj hq).1))
      (colE2 ⟨23, by decide⟩ 4 hp) Q2.T140_23_2 Q2.hfix140_23_2 Q2.hinj140_23_2
      Q2.hcardT140_23_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T140_23_2 i) (Q2.hfix140_23_2 i) _)
      colCert_140_23_4.hD ?_).symm
  rw [alnId_140 j hj]


theorem leaf_140_23_5 (hp : 5 < (Q2.transData.getD 23 []).length)
    (j : Nat) (hj : j < (repChars.getD 140 []).length)
    (hq : (normIsRep.getD 140 []).getD j false = true) :
    species (Q2.reps (⟨23, by decide⟩ : Fin 148)) (colE2 ⟨23, by decide⟩ 5 hp)
        (rowE2 (⟨140, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨23, by decide⟩ : Fin 148))
        (colE1 ⟨23, by decide⟩ 5 (transLenTr ⟨23, by decide⟩ 5 hp))
        (rowE1 (⟨140, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨140, by decide⟩ : Fin 148) ⟨23, by decide⟩ _
      (validAt ⟨140, by decide⟩ (listedAt ⟨140, by decide⟩ hj))
      (colE1 ⟨23, by decide⟩ 5 (transLenTr ⟨23, by decide⟩ 5 hp)) T140_23
      hfix140_23 hinj140_23 hcardT140_23
      (fun i => conj_mem_of_fixedPoints _ _ (T140_23 i) (hfix140_23 i) _)
      ⟨140, by decide⟩ ⟨23, by decide⟩ _
      (Q2.validAt ⟨140, by decide⟩ (Q2.listedAt ⟨140, by decide⟩
        (alnCheck_rep ⟨140, by decide⟩ hj hq).1))
      (colE2 ⟨23, by decide⟩ 5 hp) Q2.T140_23_2 Q2.hfix140_23_2 Q2.hinj140_23_2
      Q2.hcardT140_23_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T140_23_2 i) (Q2.hfix140_23_2 i) _)
      ?_).symm
  rw [show colData1 (⟨140, by decide⟩ : Fin 148)
        ((colE1 ⟨23, by decide⟩ 5 (transLenTr ⟨23, by decide⟩ 5 hp) : ↥(reps ⟨23, by decide⟩)) : Coordinate 1)
        T140_23 = colFn colCertDiv_140_23_5.D1 (m := 5) from colCertDiv_140_23_5.bind1,
    show colData2 (⟨140, by decide⟩ : Fin 148)
        ((colE2 ⟨23, by decide⟩ 5 hp : ↥(Q2.reps ⟨23, by decide⟩)) : Coordinate 2)
        Q2.T140_23_2 = colFn colCertDiv_140_23_5.D2 (m := 5) from colCertDiv_140_23_5.bind2]
  rw [alnId_140 j hj]
  exact fastcode_of_div ⟨140, by decide⟩ _ _ _
    ((alnId_140 j hj) ▸ Q2.listedAt (⟨140, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨140, by decide⟩ : Fin 148) hj hq).1) colCertDiv_140_23_5_match


theorem leaf_140_23_10 (hp : 10 < (Q2.transData.getD 23 []).length)
    (j : Nat) (hj : j < (repChars.getD 140 []).length)
    (hq : (normIsRep.getD 140 []).getD j false = true) :
    species (Q2.reps (⟨23, by decide⟩ : Fin 148)) (colE2 ⟨23, by decide⟩ 10 hp)
        (rowE2 (⟨140, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨23, by decide⟩ : Fin 148))
        (colE1 ⟨23, by decide⟩ 10 (transLenTr ⟨23, by decide⟩ 10 hp))
        (rowE1 (⟨140, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨140, by decide⟩ : Fin 148) ⟨23, by decide⟩ _
      (validAt ⟨140, by decide⟩ (listedAt ⟨140, by decide⟩ hj))
      (colE1 ⟨23, by decide⟩ 10 (transLenTr ⟨23, by decide⟩ 10 hp)) T140_23
      hfix140_23 hinj140_23 hcardT140_23
      (fun i => conj_mem_of_fixedPoints _ _ (T140_23 i) (hfix140_23 i) _)
      ⟨140, by decide⟩ ⟨23, by decide⟩ _
      (Q2.validAt ⟨140, by decide⟩ (Q2.listedAt ⟨140, by decide⟩
        (alnCheck_rep ⟨140, by decide⟩ hj hq).1))
      (colE2 ⟨23, by decide⟩ 10 hp) Q2.T140_23_2 Q2.hfix140_23_2 Q2.hinj140_23_2
      Q2.hcardT140_23_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T140_23_2 i) (Q2.hfix140_23_2 i) _)
      ?_).symm
  rw [show colData1 (⟨140, by decide⟩ : Fin 148)
        ((colE1 ⟨23, by decide⟩ 10 (transLenTr ⟨23, by decide⟩ 10 hp) : ↥(reps ⟨23, by decide⟩)) : Coordinate 1)
        T140_23 = colFn colCertDiv_140_23_10.D1 (m := 5) from colCertDiv_140_23_10.bind1,
    show colData2 (⟨140, by decide⟩ : Fin 148)
        ((colE2 ⟨23, by decide⟩ 10 hp : ↥(Q2.reps ⟨23, by decide⟩)) : Coordinate 2)
        Q2.T140_23_2 = colFn colCertDiv_140_23_10.D2 (m := 5) from colCertDiv_140_23_10.bind2]
  rw [alnId_140 j hj]
  exact fastcode_of_div ⟨140, by decide⟩ _ _ _
    ((alnId_140 j hj) ▸ Q2.listedAt (⟨140, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨140, by decide⟩ : Fin 148) hj hq).1) colCertDiv_140_23_10_match


theorem leaf_140_23_15 (hp : 15 < (Q2.transData.getD 23 []).length)
    (j : Nat) (hj : j < (repChars.getD 140 []).length)
    (hq : (normIsRep.getD 140 []).getD j false = true) :
    species (Q2.reps (⟨23, by decide⟩ : Fin 148)) (colE2 ⟨23, by decide⟩ 15 hp)
        (rowE2 (⟨140, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨23, by decide⟩ : Fin 148))
        (colE1 ⟨23, by decide⟩ 15 (transLenTr ⟨23, by decide⟩ 15 hp))
        (rowE1 (⟨140, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨140, by decide⟩ : Fin 148) ⟨23, by decide⟩ _
      (validAt ⟨140, by decide⟩ (listedAt ⟨140, by decide⟩ hj))
      (colE1 ⟨23, by decide⟩ 15 (transLenTr ⟨23, by decide⟩ 15 hp)) T140_23
      hfix140_23 hinj140_23 hcardT140_23
      (fun i => conj_mem_of_fixedPoints _ _ (T140_23 i) (hfix140_23 i) _)
      ⟨140, by decide⟩ ⟨23, by decide⟩ _
      (Q2.validAt ⟨140, by decide⟩ (Q2.listedAt ⟨140, by decide⟩
        (alnCheck_rep ⟨140, by decide⟩ hj hq).1))
      (colE2 ⟨23, by decide⟩ 15 hp) Q2.T140_23_2 Q2.hfix140_23_2 Q2.hinj140_23_2
      Q2.hcardT140_23_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T140_23_2 i) (Q2.hfix140_23_2 i) _)
      ?_).symm
  rw [show colData1 (⟨140, by decide⟩ : Fin 148)
        ((colE1 ⟨23, by decide⟩ 15 (transLenTr ⟨23, by decide⟩ 15 hp) : ↥(reps ⟨23, by decide⟩)) : Coordinate 1)
        T140_23 = colFn colCertDiv_140_23_15.D1 (m := 5) from colCertDiv_140_23_15.bind1,
    show colData2 (⟨140, by decide⟩ : Fin 148)
        ((colE2 ⟨23, by decide⟩ 15 hp : ↥(Q2.reps ⟨23, by decide⟩)) : Coordinate 2)
        Q2.T140_23_2 = colFn colCertDiv_140_23_15.D2 (m := 5) from colCertDiv_140_23_15.bind2]
  rw [alnId_140 j hj]
  exact fastcode_of_div ⟨140, by decide⟩ _ _ _
    ((alnId_140 j hj) ▸ Q2.listedAt (⟨140, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨140, by decide⟩ : Fin 148) hj hq).1) colCertDiv_140_23_15_match


theorem leaf_140_23_20 (hp : 20 < (Q2.transData.getD 23 []).length)
    (j : Nat) (hj : j < (repChars.getD 140 []).length)
    (hq : (normIsRep.getD 140 []).getD j false = true) :
    species (Q2.reps (⟨23, by decide⟩ : Fin 148)) (colE2 ⟨23, by decide⟩ 20 hp)
        (rowE2 (⟨140, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨23, by decide⟩ : Fin 148))
        (colE1 ⟨23, by decide⟩ 20 (transLenTr ⟨23, by decide⟩ 20 hp))
        (rowE1 (⟨140, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨140, by decide⟩ : Fin 148) ⟨23, by decide⟩ _
      (validAt ⟨140, by decide⟩ (listedAt ⟨140, by decide⟩ hj))
      (colE1 ⟨23, by decide⟩ 20 (transLenTr ⟨23, by decide⟩ 20 hp)) T140_23
      hfix140_23 hinj140_23 hcardT140_23
      (fun i => conj_mem_of_fixedPoints _ _ (T140_23 i) (hfix140_23 i) _)
      ⟨140, by decide⟩ ⟨23, by decide⟩ _
      (Q2.validAt ⟨140, by decide⟩ (Q2.listedAt ⟨140, by decide⟩
        (alnCheck_rep ⟨140, by decide⟩ hj hq).1))
      (colE2 ⟨23, by decide⟩ 20 hp) Q2.T140_23_2 Q2.hfix140_23_2 Q2.hinj140_23_2
      Q2.hcardT140_23_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T140_23_2 i) (Q2.hfix140_23_2 i) _)
      ?_).symm
  rw [show colData1 (⟨140, by decide⟩ : Fin 148)
        ((colE1 ⟨23, by decide⟩ 20 (transLenTr ⟨23, by decide⟩ 20 hp) : ↥(reps ⟨23, by decide⟩)) : Coordinate 1)
        T140_23 = colFn colCertDiv_140_23_20.D1 (m := 5) from colCertDiv_140_23_20.bind1,
    show colData2 (⟨140, by decide⟩ : Fin 148)
        ((colE2 ⟨23, by decide⟩ 20 hp : ↥(Q2.reps ⟨23, by decide⟩)) : Coordinate 2)
        Q2.T140_23_2 = colFn colCertDiv_140_23_20.D2 (m := 5) from colCertDiv_140_23_20.bind2]
  rw [alnId_140 j hj]
  exact fastcode_of_div ⟨140, by decide⟩ _ _ _
    ((alnId_140 j hj) ▸ Q2.listedAt (⟨140, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨140, by decide⟩ : Fin 148) hj hq).1) colCertDiv_140_23_20_match


theorem leaf_140_28_0 (hp : 0 < (Q2.transData.getD 28 []).length)
    (j : Nat) (hj : j < (repChars.getD 140 []).length)
    (hq : (normIsRep.getD 140 []).getD j false = true) :
    species (Q2.reps (⟨28, by decide⟩ : Fin 148)) (colE2 ⟨28, by decide⟩ 0 hp)
        (rowE2 (⟨140, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨28, by decide⟩ : Fin 148))
        (colE1 ⟨28, by decide⟩ 0 (transLenTr ⟨28, by decide⟩ 0 hp))
        (rowE1 (⟨140, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨140, by decide⟩ : Fin 148) ⟨28, by decide⟩ _
      (validAt ⟨140, by decide⟩ (listedAt ⟨140, by decide⟩ hj))
      (colE1 ⟨28, by decide⟩ 0 (transLenTr ⟨28, by decide⟩ 0 hp)) T140_28
      hfix140_28 hinj140_28 hcardT140_28
      (fun i => conj_mem_of_fixedPoints _ _ (T140_28 i) (hfix140_28 i) _)
      ⟨140, by decide⟩ ⟨28, by decide⟩ _
      (Q2.validAt ⟨140, by decide⟩ (Q2.listedAt ⟨140, by decide⟩
        (alnCheck_rep ⟨140, by decide⟩ hj hq).1))
      (colE2 ⟨28, by decide⟩ 0 hp) Q2.T140_28_2 Q2.hfix140_28_2 Q2.hinj140_28_2
      Q2.hcardT140_28_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T140_28_2 i) (Q2.hfix140_28_2 i) _)
      colCert_140_28_0.hD ?_).symm
  rw [alnId_140 j hj]


theorem leaf_140_28_1 (hp : 1 < (Q2.transData.getD 28 []).length)
    (j : Nat) (hj : j < (repChars.getD 140 []).length)
    (hq : (normIsRep.getD 140 []).getD j false = true) :
    species (Q2.reps (⟨28, by decide⟩ : Fin 148)) (colE2 ⟨28, by decide⟩ 1 hp)
        (rowE2 (⟨140, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨28, by decide⟩ : Fin 148))
        (colE1 ⟨28, by decide⟩ 1 (transLenTr ⟨28, by decide⟩ 1 hp))
        (rowE1 (⟨140, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨140, by decide⟩ : Fin 148) ⟨28, by decide⟩ _
      (validAt ⟨140, by decide⟩ (listedAt ⟨140, by decide⟩ hj))
      (colE1 ⟨28, by decide⟩ 1 (transLenTr ⟨28, by decide⟩ 1 hp)) T140_28
      hfix140_28 hinj140_28 hcardT140_28
      (fun i => conj_mem_of_fixedPoints _ _ (T140_28 i) (hfix140_28 i) _)
      ⟨140, by decide⟩ ⟨28, by decide⟩ _
      (Q2.validAt ⟨140, by decide⟩ (Q2.listedAt ⟨140, by decide⟩
        (alnCheck_rep ⟨140, by decide⟩ hj hq).1))
      (colE2 ⟨28, by decide⟩ 1 hp) Q2.T140_28_2 Q2.hfix140_28_2 Q2.hinj140_28_2
      Q2.hcardT140_28_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T140_28_2 i) (Q2.hfix140_28_2 i) _)
      colCert_140_28_1.hD ?_).symm
  rw [alnId_140 j hj]


theorem leaf_140_28_2 (hp : 2 < (Q2.transData.getD 28 []).length)
    (j : Nat) (hj : j < (repChars.getD 140 []).length)
    (hq : (normIsRep.getD 140 []).getD j false = true) :
    species (Q2.reps (⟨28, by decide⟩ : Fin 148)) (colE2 ⟨28, by decide⟩ 2 hp)
        (rowE2 (⟨140, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨28, by decide⟩ : Fin 148))
        (colE1 ⟨28, by decide⟩ 2 (transLenTr ⟨28, by decide⟩ 2 hp))
        (rowE1 (⟨140, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨140, by decide⟩ : Fin 148) ⟨28, by decide⟩ _
      (validAt ⟨140, by decide⟩ (listedAt ⟨140, by decide⟩ hj))
      (colE1 ⟨28, by decide⟩ 2 (transLenTr ⟨28, by decide⟩ 2 hp)) T140_28
      hfix140_28 hinj140_28 hcardT140_28
      (fun i => conj_mem_of_fixedPoints _ _ (T140_28 i) (hfix140_28 i) _)
      ⟨140, by decide⟩ ⟨28, by decide⟩ _
      (Q2.validAt ⟨140, by decide⟩ (Q2.listedAt ⟨140, by decide⟩
        (alnCheck_rep ⟨140, by decide⟩ hj hq).1))
      (colE2 ⟨28, by decide⟩ 2 hp) Q2.T140_28_2 Q2.hfix140_28_2 Q2.hinj140_28_2
      Q2.hcardT140_28_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T140_28_2 i) (Q2.hfix140_28_2 i) _)
      colCert_140_28_2.hD ?_).symm
  rw [alnId_140 j hj]


theorem leaf_140_28_3 (hp : 3 < (Q2.transData.getD 28 []).length)
    (j : Nat) (hj : j < (repChars.getD 140 []).length)
    (hq : (normIsRep.getD 140 []).getD j false = true) :
    species (Q2.reps (⟨28, by decide⟩ : Fin 148)) (colE2 ⟨28, by decide⟩ 3 hp)
        (rowE2 (⟨140, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨28, by decide⟩ : Fin 148))
        (colE1 ⟨28, by decide⟩ 3 (transLenTr ⟨28, by decide⟩ 3 hp))
        (rowE1 (⟨140, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨140, by decide⟩ : Fin 148) ⟨28, by decide⟩ _
      (validAt ⟨140, by decide⟩ (listedAt ⟨140, by decide⟩ hj))
      (colE1 ⟨28, by decide⟩ 3 (transLenTr ⟨28, by decide⟩ 3 hp)) T140_28
      hfix140_28 hinj140_28 hcardT140_28
      (fun i => conj_mem_of_fixedPoints _ _ (T140_28 i) (hfix140_28 i) _)
      ⟨140, by decide⟩ ⟨28, by decide⟩ _
      (Q2.validAt ⟨140, by decide⟩ (Q2.listedAt ⟨140, by decide⟩
        (alnCheck_rep ⟨140, by decide⟩ hj hq).1))
      (colE2 ⟨28, by decide⟩ 3 hp) Q2.T140_28_2 Q2.hfix140_28_2 Q2.hinj140_28_2
      Q2.hcardT140_28_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T140_28_2 i) (Q2.hfix140_28_2 i) _)
      colCert_140_28_3.hD ?_).symm
  rw [alnId_140 j hj]


theorem leaf_140_28_4 (hp : 4 < (Q2.transData.getD 28 []).length)
    (j : Nat) (hj : j < (repChars.getD 140 []).length)
    (hq : (normIsRep.getD 140 []).getD j false = true) :
    species (Q2.reps (⟨28, by decide⟩ : Fin 148)) (colE2 ⟨28, by decide⟩ 4 hp)
        (rowE2 (⟨140, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨28, by decide⟩ : Fin 148))
        (colE1 ⟨28, by decide⟩ 4 (transLenTr ⟨28, by decide⟩ 4 hp))
        (rowE1 (⟨140, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨140, by decide⟩ : Fin 148) ⟨28, by decide⟩ _
      (validAt ⟨140, by decide⟩ (listedAt ⟨140, by decide⟩ hj))
      (colE1 ⟨28, by decide⟩ 4 (transLenTr ⟨28, by decide⟩ 4 hp)) T140_28
      hfix140_28 hinj140_28 hcardT140_28
      (fun i => conj_mem_of_fixedPoints _ _ (T140_28 i) (hfix140_28 i) _)
      ⟨140, by decide⟩ ⟨28, by decide⟩ _
      (Q2.validAt ⟨140, by decide⟩ (Q2.listedAt ⟨140, by decide⟩
        (alnCheck_rep ⟨140, by decide⟩ hj hq).1))
      (colE2 ⟨28, by decide⟩ 4 hp) Q2.T140_28_2 Q2.hfix140_28_2 Q2.hinj140_28_2
      Q2.hcardT140_28_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T140_28_2 i) (Q2.hfix140_28_2 i) _)
      colCert_140_28_4.hD ?_).symm
  rw [alnId_140 j hj]


theorem leaf_140_28_5 (hp : 5 < (Q2.transData.getD 28 []).length)
    (j : Nat) (hj : j < (repChars.getD 140 []).length)
    (hq : (normIsRep.getD 140 []).getD j false = true) :
    species (Q2.reps (⟨28, by decide⟩ : Fin 148)) (colE2 ⟨28, by decide⟩ 5 hp)
        (rowE2 (⟨140, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨28, by decide⟩ : Fin 148))
        (colE1 ⟨28, by decide⟩ 5 (transLenTr ⟨28, by decide⟩ 5 hp))
        (rowE1 (⟨140, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨140, by decide⟩ : Fin 148) ⟨28, by decide⟩ _
      (validAt ⟨140, by decide⟩ (listedAt ⟨140, by decide⟩ hj))
      (colE1 ⟨28, by decide⟩ 5 (transLenTr ⟨28, by decide⟩ 5 hp)) T140_28
      hfix140_28 hinj140_28 hcardT140_28
      (fun i => conj_mem_of_fixedPoints _ _ (T140_28 i) (hfix140_28 i) _)
      ⟨140, by decide⟩ ⟨28, by decide⟩ _
      (Q2.validAt ⟨140, by decide⟩ (Q2.listedAt ⟨140, by decide⟩
        (alnCheck_rep ⟨140, by decide⟩ hj hq).1))
      (colE2 ⟨28, by decide⟩ 5 hp) Q2.T140_28_2 Q2.hfix140_28_2 Q2.hinj140_28_2
      Q2.hcardT140_28_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T140_28_2 i) (Q2.hfix140_28_2 i) _)
      colCert_140_28_5.hD ?_).symm
  rw [alnId_140 j hj]


theorem leaf_140_28_10 (hp : 10 < (Q2.transData.getD 28 []).length)
    (j : Nat) (hj : j < (repChars.getD 140 []).length)
    (hq : (normIsRep.getD 140 []).getD j false = true) :
    species (Q2.reps (⟨28, by decide⟩ : Fin 148)) (colE2 ⟨28, by decide⟩ 10 hp)
        (rowE2 (⟨140, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨28, by decide⟩ : Fin 148))
        (colE1 ⟨28, by decide⟩ 10 (transLenTr ⟨28, by decide⟩ 10 hp))
        (rowE1 (⟨140, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨140, by decide⟩ : Fin 148) ⟨28, by decide⟩ _
      (validAt ⟨140, by decide⟩ (listedAt ⟨140, by decide⟩ hj))
      (colE1 ⟨28, by decide⟩ 10 (transLenTr ⟨28, by decide⟩ 10 hp)) T140_28
      hfix140_28 hinj140_28 hcardT140_28
      (fun i => conj_mem_of_fixedPoints _ _ (T140_28 i) (hfix140_28 i) _)
      ⟨140, by decide⟩ ⟨28, by decide⟩ _
      (Q2.validAt ⟨140, by decide⟩ (Q2.listedAt ⟨140, by decide⟩
        (alnCheck_rep ⟨140, by decide⟩ hj hq).1))
      (colE2 ⟨28, by decide⟩ 10 hp) Q2.T140_28_2 Q2.hfix140_28_2 Q2.hinj140_28_2
      Q2.hcardT140_28_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T140_28_2 i) (Q2.hfix140_28_2 i) _)
      colCert_140_28_10.hD ?_).symm
  rw [alnId_140 j hj]


theorem leaf_140_28_15 (hp : 15 < (Q2.transData.getD 28 []).length)
    (j : Nat) (hj : j < (repChars.getD 140 []).length)
    (hq : (normIsRep.getD 140 []).getD j false = true) :
    species (Q2.reps (⟨28, by decide⟩ : Fin 148)) (colE2 ⟨28, by decide⟩ 15 hp)
        (rowE2 (⟨140, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨28, by decide⟩ : Fin 148))
        (colE1 ⟨28, by decide⟩ 15 (transLenTr ⟨28, by decide⟩ 15 hp))
        (rowE1 (⟨140, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨140, by decide⟩ : Fin 148) ⟨28, by decide⟩ _
      (validAt ⟨140, by decide⟩ (listedAt ⟨140, by decide⟩ hj))
      (colE1 ⟨28, by decide⟩ 15 (transLenTr ⟨28, by decide⟩ 15 hp)) T140_28
      hfix140_28 hinj140_28 hcardT140_28
      (fun i => conj_mem_of_fixedPoints _ _ (T140_28 i) (hfix140_28 i) _)
      ⟨140, by decide⟩ ⟨28, by decide⟩ _
      (Q2.validAt ⟨140, by decide⟩ (Q2.listedAt ⟨140, by decide⟩
        (alnCheck_rep ⟨140, by decide⟩ hj hq).1))
      (colE2 ⟨28, by decide⟩ 15 hp) Q2.T140_28_2 Q2.hfix140_28_2 Q2.hinj140_28_2
      Q2.hcardT140_28_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T140_28_2 i) (Q2.hfix140_28_2 i) _)
      colCert_140_28_15.hD ?_).symm
  rw [alnId_140 j hj]


theorem leaf_140_28_20 (hp : 20 < (Q2.transData.getD 28 []).length)
    (j : Nat) (hj : j < (repChars.getD 140 []).length)
    (hq : (normIsRep.getD 140 []).getD j false = true) :
    species (Q2.reps (⟨28, by decide⟩ : Fin 148)) (colE2 ⟨28, by decide⟩ 20 hp)
        (rowE2 (⟨140, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨28, by decide⟩ : Fin 148))
        (colE1 ⟨28, by decide⟩ 20 (transLenTr ⟨28, by decide⟩ 20 hp))
        (rowE1 (⟨140, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨140, by decide⟩ : Fin 148) ⟨28, by decide⟩ _
      (validAt ⟨140, by decide⟩ (listedAt ⟨140, by decide⟩ hj))
      (colE1 ⟨28, by decide⟩ 20 (transLenTr ⟨28, by decide⟩ 20 hp)) T140_28
      hfix140_28 hinj140_28 hcardT140_28
      (fun i => conj_mem_of_fixedPoints _ _ (T140_28 i) (hfix140_28 i) _)
      ⟨140, by decide⟩ ⟨28, by decide⟩ _
      (Q2.validAt ⟨140, by decide⟩ (Q2.listedAt ⟨140, by decide⟩
        (alnCheck_rep ⟨140, by decide⟩ hj hq).1))
      (colE2 ⟨28, by decide⟩ 20 hp) Q2.T140_28_2 Q2.hfix140_28_2 Q2.hinj140_28_2
      Q2.hcardT140_28_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T140_28_2 i) (Q2.hfix140_28_2 i) _)
      colCert_140_28_20.hD ?_).symm
  rw [alnId_140 j hj]


theorem leaf_140_35_0 (hp : 0 < (Q2.transData.getD 35 []).length)
    (j : Nat) (hj : j < (repChars.getD 140 []).length)
    (hq : (normIsRep.getD 140 []).getD j false = true) :
    species (Q2.reps (⟨35, by decide⟩ : Fin 148)) (colE2 ⟨35, by decide⟩ 0 hp)
        (rowE2 (⟨140, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨35, by decide⟩ : Fin 148))
        (colE1 ⟨35, by decide⟩ 0 (transLenTr ⟨35, by decide⟩ 0 hp))
        (rowE1 (⟨140, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨140, by decide⟩ : Fin 148) ⟨35, by decide⟩ _
      (validAt ⟨140, by decide⟩ (listedAt ⟨140, by decide⟩ hj))
      (colE1 ⟨35, by decide⟩ 0 (transLenTr ⟨35, by decide⟩ 0 hp)) T140_35
      hfix140_35 hinj140_35 hcardT140_35
      (fun i => conj_mem_of_fixedPoints _ _ (T140_35 i) (hfix140_35 i) _)
      ⟨140, by decide⟩ ⟨35, by decide⟩ _
      (Q2.validAt ⟨140, by decide⟩ (Q2.listedAt ⟨140, by decide⟩
        (alnCheck_rep ⟨140, by decide⟩ hj hq).1))
      (colE2 ⟨35, by decide⟩ 0 hp) Q2.T140_35_2 Q2.hfix140_35_2 Q2.hinj140_35_2
      Q2.hcardT140_35_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T140_35_2 i) (Q2.hfix140_35_2 i) _)
      colCert_140_35_0.hD ?_).symm
  rw [alnId_140 j hj]


theorem leaf_140_35_1 (hp : 1 < (Q2.transData.getD 35 []).length)
    (j : Nat) (hj : j < (repChars.getD 140 []).length)
    (hq : (normIsRep.getD 140 []).getD j false = true) :
    species (Q2.reps (⟨35, by decide⟩ : Fin 148)) (colE2 ⟨35, by decide⟩ 1 hp)
        (rowE2 (⟨140, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨35, by decide⟩ : Fin 148))
        (colE1 ⟨35, by decide⟩ 1 (transLenTr ⟨35, by decide⟩ 1 hp))
        (rowE1 (⟨140, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨140, by decide⟩ : Fin 148) ⟨35, by decide⟩ _
      (validAt ⟨140, by decide⟩ (listedAt ⟨140, by decide⟩ hj))
      (colE1 ⟨35, by decide⟩ 1 (transLenTr ⟨35, by decide⟩ 1 hp)) T140_35
      hfix140_35 hinj140_35 hcardT140_35
      (fun i => conj_mem_of_fixedPoints _ _ (T140_35 i) (hfix140_35 i) _)
      ⟨140, by decide⟩ ⟨35, by decide⟩ _
      (Q2.validAt ⟨140, by decide⟩ (Q2.listedAt ⟨140, by decide⟩
        (alnCheck_rep ⟨140, by decide⟩ hj hq).1))
      (colE2 ⟨35, by decide⟩ 1 hp) Q2.T140_35_2 Q2.hfix140_35_2 Q2.hinj140_35_2
      Q2.hcardT140_35_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T140_35_2 i) (Q2.hfix140_35_2 i) _)
      colCert_140_35_1.hD ?_).symm
  rw [alnId_140 j hj]


theorem leaf_140_35_2 (hp : 2 < (Q2.transData.getD 35 []).length)
    (j : Nat) (hj : j < (repChars.getD 140 []).length)
    (hq : (normIsRep.getD 140 []).getD j false = true) :
    species (Q2.reps (⟨35, by decide⟩ : Fin 148)) (colE2 ⟨35, by decide⟩ 2 hp)
        (rowE2 (⟨140, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨35, by decide⟩ : Fin 148))
        (colE1 ⟨35, by decide⟩ 2 (transLenTr ⟨35, by decide⟩ 2 hp))
        (rowE1 (⟨140, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨140, by decide⟩ : Fin 148) ⟨35, by decide⟩ _
      (validAt ⟨140, by decide⟩ (listedAt ⟨140, by decide⟩ hj))
      (colE1 ⟨35, by decide⟩ 2 (transLenTr ⟨35, by decide⟩ 2 hp)) T140_35
      hfix140_35 hinj140_35 hcardT140_35
      (fun i => conj_mem_of_fixedPoints _ _ (T140_35 i) (hfix140_35 i) _)
      ⟨140, by decide⟩ ⟨35, by decide⟩ _
      (Q2.validAt ⟨140, by decide⟩ (Q2.listedAt ⟨140, by decide⟩
        (alnCheck_rep ⟨140, by decide⟩ hj hq).1))
      (colE2 ⟨35, by decide⟩ 2 hp) Q2.T140_35_2 Q2.hfix140_35_2 Q2.hinj140_35_2
      Q2.hcardT140_35_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T140_35_2 i) (Q2.hfix140_35_2 i) _)
      colCert_140_35_2.hD ?_).symm
  rw [alnId_140 j hj]


theorem leaf_140_35_3 (hp : 3 < (Q2.transData.getD 35 []).length)
    (j : Nat) (hj : j < (repChars.getD 140 []).length)
    (hq : (normIsRep.getD 140 []).getD j false = true) :
    species (Q2.reps (⟨35, by decide⟩ : Fin 148)) (colE2 ⟨35, by decide⟩ 3 hp)
        (rowE2 (⟨140, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨35, by decide⟩ : Fin 148))
        (colE1 ⟨35, by decide⟩ 3 (transLenTr ⟨35, by decide⟩ 3 hp))
        (rowE1 (⟨140, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨140, by decide⟩ : Fin 148) ⟨35, by decide⟩ _
      (validAt ⟨140, by decide⟩ (listedAt ⟨140, by decide⟩ hj))
      (colE1 ⟨35, by decide⟩ 3 (transLenTr ⟨35, by decide⟩ 3 hp)) T140_35
      hfix140_35 hinj140_35 hcardT140_35
      (fun i => conj_mem_of_fixedPoints _ _ (T140_35 i) (hfix140_35 i) _)
      ⟨140, by decide⟩ ⟨35, by decide⟩ _
      (Q2.validAt ⟨140, by decide⟩ (Q2.listedAt ⟨140, by decide⟩
        (alnCheck_rep ⟨140, by decide⟩ hj hq).1))
      (colE2 ⟨35, by decide⟩ 3 hp) Q2.T140_35_2 Q2.hfix140_35_2 Q2.hinj140_35_2
      Q2.hcardT140_35_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T140_35_2 i) (Q2.hfix140_35_2 i) _)
      colCert_140_35_3.hD ?_).symm
  rw [alnId_140 j hj]


theorem leaf_140_35_4 (hp : 4 < (Q2.transData.getD 35 []).length)
    (j : Nat) (hj : j < (repChars.getD 140 []).length)
    (hq : (normIsRep.getD 140 []).getD j false = true) :
    species (Q2.reps (⟨35, by decide⟩ : Fin 148)) (colE2 ⟨35, by decide⟩ 4 hp)
        (rowE2 (⟨140, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨35, by decide⟩ : Fin 148))
        (colE1 ⟨35, by decide⟩ 4 (transLenTr ⟨35, by decide⟩ 4 hp))
        (rowE1 (⟨140, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨140, by decide⟩ : Fin 148) ⟨35, by decide⟩ _
      (validAt ⟨140, by decide⟩ (listedAt ⟨140, by decide⟩ hj))
      (colE1 ⟨35, by decide⟩ 4 (transLenTr ⟨35, by decide⟩ 4 hp)) T140_35
      hfix140_35 hinj140_35 hcardT140_35
      (fun i => conj_mem_of_fixedPoints _ _ (T140_35 i) (hfix140_35 i) _)
      ⟨140, by decide⟩ ⟨35, by decide⟩ _
      (Q2.validAt ⟨140, by decide⟩ (Q2.listedAt ⟨140, by decide⟩
        (alnCheck_rep ⟨140, by decide⟩ hj hq).1))
      (colE2 ⟨35, by decide⟩ 4 hp) Q2.T140_35_2 Q2.hfix140_35_2 Q2.hinj140_35_2
      Q2.hcardT140_35_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T140_35_2 i) (Q2.hfix140_35_2 i) _)
      colCert_140_35_4.hD ?_).symm
  rw [alnId_140 j hj]


theorem leaf_140_35_5 (hp : 5 < (Q2.transData.getD 35 []).length)
    (j : Nat) (hj : j < (repChars.getD 140 []).length)
    (hq : (normIsRep.getD 140 []).getD j false = true) :
    species (Q2.reps (⟨35, by decide⟩ : Fin 148)) (colE2 ⟨35, by decide⟩ 5 hp)
        (rowE2 (⟨140, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨35, by decide⟩ : Fin 148))
        (colE1 ⟨35, by decide⟩ 5 (transLenTr ⟨35, by decide⟩ 5 hp))
        (rowE1 (⟨140, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨140, by decide⟩ : Fin 148) ⟨35, by decide⟩ _
      (validAt ⟨140, by decide⟩ (listedAt ⟨140, by decide⟩ hj))
      (colE1 ⟨35, by decide⟩ 5 (transLenTr ⟨35, by decide⟩ 5 hp)) T140_35
      hfix140_35 hinj140_35 hcardT140_35
      (fun i => conj_mem_of_fixedPoints _ _ (T140_35 i) (hfix140_35 i) _)
      ⟨140, by decide⟩ ⟨35, by decide⟩ _
      (Q2.validAt ⟨140, by decide⟩ (Q2.listedAt ⟨140, by decide⟩
        (alnCheck_rep ⟨140, by decide⟩ hj hq).1))
      (colE2 ⟨35, by decide⟩ 5 hp) Q2.T140_35_2 Q2.hfix140_35_2 Q2.hinj140_35_2
      Q2.hcardT140_35_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T140_35_2 i) (Q2.hfix140_35_2 i) _)
      ?_).symm
  rw [show colData1 (⟨140, by decide⟩ : Fin 148)
        ((colE1 ⟨35, by decide⟩ 5 (transLenTr ⟨35, by decide⟩ 5 hp) : ↥(reps ⟨35, by decide⟩)) : Coordinate 1)
        T140_35 = colFn colCertDiv_140_35_5.D1 (m := 5) from colCertDiv_140_35_5.bind1,
    show colData2 (⟨140, by decide⟩ : Fin 148)
        ((colE2 ⟨35, by decide⟩ 5 hp : ↥(Q2.reps ⟨35, by decide⟩)) : Coordinate 2)
        Q2.T140_35_2 = colFn colCertDiv_140_35_5.D2 (m := 5) from colCertDiv_140_35_5.bind2]
  rw [alnId_140 j hj]
  exact fastcode_of_div ⟨140, by decide⟩ _ _ _
    ((alnId_140 j hj) ▸ Q2.listedAt (⟨140, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨140, by decide⟩ : Fin 148) hj hq).1) colCertDiv_140_35_5_match


theorem leaf_140_35_10 (hp : 10 < (Q2.transData.getD 35 []).length)
    (j : Nat) (hj : j < (repChars.getD 140 []).length)
    (hq : (normIsRep.getD 140 []).getD j false = true) :
    species (Q2.reps (⟨35, by decide⟩ : Fin 148)) (colE2 ⟨35, by decide⟩ 10 hp)
        (rowE2 (⟨140, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨35, by decide⟩ : Fin 148))
        (colE1 ⟨35, by decide⟩ 10 (transLenTr ⟨35, by decide⟩ 10 hp))
        (rowE1 (⟨140, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨140, by decide⟩ : Fin 148) ⟨35, by decide⟩ _
      (validAt ⟨140, by decide⟩ (listedAt ⟨140, by decide⟩ hj))
      (colE1 ⟨35, by decide⟩ 10 (transLenTr ⟨35, by decide⟩ 10 hp)) T140_35
      hfix140_35 hinj140_35 hcardT140_35
      (fun i => conj_mem_of_fixedPoints _ _ (T140_35 i) (hfix140_35 i) _)
      ⟨140, by decide⟩ ⟨35, by decide⟩ _
      (Q2.validAt ⟨140, by decide⟩ (Q2.listedAt ⟨140, by decide⟩
        (alnCheck_rep ⟨140, by decide⟩ hj hq).1))
      (colE2 ⟨35, by decide⟩ 10 hp) Q2.T140_35_2 Q2.hfix140_35_2 Q2.hinj140_35_2
      Q2.hcardT140_35_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T140_35_2 i) (Q2.hfix140_35_2 i) _)
      ?_).symm
  rw [show colData1 (⟨140, by decide⟩ : Fin 148)
        ((colE1 ⟨35, by decide⟩ 10 (transLenTr ⟨35, by decide⟩ 10 hp) : ↥(reps ⟨35, by decide⟩)) : Coordinate 1)
        T140_35 = colFn colCertDiv_140_35_10.D1 (m := 5) from colCertDiv_140_35_10.bind1,
    show colData2 (⟨140, by decide⟩ : Fin 148)
        ((colE2 ⟨35, by decide⟩ 10 hp : ↥(Q2.reps ⟨35, by decide⟩)) : Coordinate 2)
        Q2.T140_35_2 = colFn colCertDiv_140_35_10.D2 (m := 5) from colCertDiv_140_35_10.bind2]
  rw [alnId_140 j hj]
  exact fastcode_of_div ⟨140, by decide⟩ _ _ _
    ((alnId_140 j hj) ▸ Q2.listedAt (⟨140, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨140, by decide⟩ : Fin 148) hj hq).1) colCertDiv_140_35_10_match


theorem leaf_140_35_15 (hp : 15 < (Q2.transData.getD 35 []).length)
    (j : Nat) (hj : j < (repChars.getD 140 []).length)
    (hq : (normIsRep.getD 140 []).getD j false = true) :
    species (Q2.reps (⟨35, by decide⟩ : Fin 148)) (colE2 ⟨35, by decide⟩ 15 hp)
        (rowE2 (⟨140, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨35, by decide⟩ : Fin 148))
        (colE1 ⟨35, by decide⟩ 15 (transLenTr ⟨35, by decide⟩ 15 hp))
        (rowE1 (⟨140, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨140, by decide⟩ : Fin 148) ⟨35, by decide⟩ _
      (validAt ⟨140, by decide⟩ (listedAt ⟨140, by decide⟩ hj))
      (colE1 ⟨35, by decide⟩ 15 (transLenTr ⟨35, by decide⟩ 15 hp)) T140_35
      hfix140_35 hinj140_35 hcardT140_35
      (fun i => conj_mem_of_fixedPoints _ _ (T140_35 i) (hfix140_35 i) _)
      ⟨140, by decide⟩ ⟨35, by decide⟩ _
      (Q2.validAt ⟨140, by decide⟩ (Q2.listedAt ⟨140, by decide⟩
        (alnCheck_rep ⟨140, by decide⟩ hj hq).1))
      (colE2 ⟨35, by decide⟩ 15 hp) Q2.T140_35_2 Q2.hfix140_35_2 Q2.hinj140_35_2
      Q2.hcardT140_35_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T140_35_2 i) (Q2.hfix140_35_2 i) _)
      ?_).symm
  rw [show colData1 (⟨140, by decide⟩ : Fin 148)
        ((colE1 ⟨35, by decide⟩ 15 (transLenTr ⟨35, by decide⟩ 15 hp) : ↥(reps ⟨35, by decide⟩)) : Coordinate 1)
        T140_35 = colFn colCertDiv_140_35_15.D1 (m := 5) from colCertDiv_140_35_15.bind1,
    show colData2 (⟨140, by decide⟩ : Fin 148)
        ((colE2 ⟨35, by decide⟩ 15 hp : ↥(Q2.reps ⟨35, by decide⟩)) : Coordinate 2)
        Q2.T140_35_2 = colFn colCertDiv_140_35_15.D2 (m := 5) from colCertDiv_140_35_15.bind2]
  rw [alnId_140 j hj]
  exact fastcode_of_div ⟨140, by decide⟩ _ _ _
    ((alnId_140 j hj) ▸ Q2.listedAt (⟨140, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨140, by decide⟩ : Fin 148) hj hq).1) colCertDiv_140_35_15_match


theorem leaf_140_35_20 (hp : 20 < (Q2.transData.getD 35 []).length)
    (j : Nat) (hj : j < (repChars.getD 140 []).length)
    (hq : (normIsRep.getD 140 []).getD j false = true) :
    species (Q2.reps (⟨35, by decide⟩ : Fin 148)) (colE2 ⟨35, by decide⟩ 20 hp)
        (rowE2 (⟨140, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨35, by decide⟩ : Fin 148))
        (colE1 ⟨35, by decide⟩ 20 (transLenTr ⟨35, by decide⟩ 20 hp))
        (rowE1 (⟨140, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨140, by decide⟩ : Fin 148) ⟨35, by decide⟩ _
      (validAt ⟨140, by decide⟩ (listedAt ⟨140, by decide⟩ hj))
      (colE1 ⟨35, by decide⟩ 20 (transLenTr ⟨35, by decide⟩ 20 hp)) T140_35
      hfix140_35 hinj140_35 hcardT140_35
      (fun i => conj_mem_of_fixedPoints _ _ (T140_35 i) (hfix140_35 i) _)
      ⟨140, by decide⟩ ⟨35, by decide⟩ _
      (Q2.validAt ⟨140, by decide⟩ (Q2.listedAt ⟨140, by decide⟩
        (alnCheck_rep ⟨140, by decide⟩ hj hq).1))
      (colE2 ⟨35, by decide⟩ 20 hp) Q2.T140_35_2 Q2.hfix140_35_2 Q2.hinj140_35_2
      Q2.hcardT140_35_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T140_35_2 i) (Q2.hfix140_35_2 i) _)
      ?_).symm
  rw [show colData1 (⟨140, by decide⟩ : Fin 148)
        ((colE1 ⟨35, by decide⟩ 20 (transLenTr ⟨35, by decide⟩ 20 hp) : ↥(reps ⟨35, by decide⟩)) : Coordinate 1)
        T140_35 = colFn colCertDiv_140_35_20.D1 (m := 5) from colCertDiv_140_35_20.bind1,
    show colData2 (⟨140, by decide⟩ : Fin 148)
        ((colE2 ⟨35, by decide⟩ 20 hp : ↥(Q2.reps ⟨35, by decide⟩)) : Coordinate 2)
        Q2.T140_35_2 = colFn colCertDiv_140_35_20.D2 (m := 5) from colCertDiv_140_35_20.bind2]
  rw [alnId_140 j hj]
  exact fastcode_of_div ⟨140, by decide⟩ _ _ _
    ((alnId_140 j hj) ▸ Q2.listedAt (⟨140, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨140, by decide⟩ : Fin 148) hj hq).1) colCertDiv_140_35_20_match


theorem leaf_140_39_0 (hp : 0 < (Q2.transData.getD 39 []).length)
    (j : Nat) (hj : j < (repChars.getD 140 []).length)
    (hq : (normIsRep.getD 140 []).getD j false = true) :
    species (Q2.reps (⟨39, by decide⟩ : Fin 148)) (colE2 ⟨39, by decide⟩ 0 hp)
        (rowE2 (⟨140, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨39, by decide⟩ : Fin 148))
        (colE1 ⟨39, by decide⟩ 0 (transLenTr ⟨39, by decide⟩ 0 hp))
        (rowE1 (⟨140, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨140, by decide⟩ : Fin 148) ⟨39, by decide⟩ _
      (validAt ⟨140, by decide⟩ (listedAt ⟨140, by decide⟩ hj))
      (colE1 ⟨39, by decide⟩ 0 (transLenTr ⟨39, by decide⟩ 0 hp)) T140_39
      hfix140_39 hinj140_39 hcardT140_39
      (fun i => conj_mem_of_fixedPoints _ _ (T140_39 i) (hfix140_39 i) _)
      ⟨140, by decide⟩ ⟨39, by decide⟩ _
      (Q2.validAt ⟨140, by decide⟩ (Q2.listedAt ⟨140, by decide⟩
        (alnCheck_rep ⟨140, by decide⟩ hj hq).1))
      (colE2 ⟨39, by decide⟩ 0 hp) Q2.T140_39_2 Q2.hfix140_39_2 Q2.hinj140_39_2
      Q2.hcardT140_39_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T140_39_2 i) (Q2.hfix140_39_2 i) _)
      colCert_140_39_0.hD ?_).symm
  rw [alnId_140 j hj]


theorem leaf_140_39_1 (hp : 1 < (Q2.transData.getD 39 []).length)
    (j : Nat) (hj : j < (repChars.getD 140 []).length)
    (hq : (normIsRep.getD 140 []).getD j false = true) :
    species (Q2.reps (⟨39, by decide⟩ : Fin 148)) (colE2 ⟨39, by decide⟩ 1 hp)
        (rowE2 (⟨140, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨39, by decide⟩ : Fin 148))
        (colE1 ⟨39, by decide⟩ 1 (transLenTr ⟨39, by decide⟩ 1 hp))
        (rowE1 (⟨140, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨140, by decide⟩ : Fin 148) ⟨39, by decide⟩ _
      (validAt ⟨140, by decide⟩ (listedAt ⟨140, by decide⟩ hj))
      (colE1 ⟨39, by decide⟩ 1 (transLenTr ⟨39, by decide⟩ 1 hp)) T140_39
      hfix140_39 hinj140_39 hcardT140_39
      (fun i => conj_mem_of_fixedPoints _ _ (T140_39 i) (hfix140_39 i) _)
      ⟨140, by decide⟩ ⟨39, by decide⟩ _
      (Q2.validAt ⟨140, by decide⟩ (Q2.listedAt ⟨140, by decide⟩
        (alnCheck_rep ⟨140, by decide⟩ hj hq).1))
      (colE2 ⟨39, by decide⟩ 1 hp) Q2.T140_39_2 Q2.hfix140_39_2 Q2.hinj140_39_2
      Q2.hcardT140_39_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T140_39_2 i) (Q2.hfix140_39_2 i) _)
      colCert_140_39_1.hD ?_).symm
  rw [alnId_140 j hj]


theorem leaf_140_39_2 (hp : 2 < (Q2.transData.getD 39 []).length)
    (j : Nat) (hj : j < (repChars.getD 140 []).length)
    (hq : (normIsRep.getD 140 []).getD j false = true) :
    species (Q2.reps (⟨39, by decide⟩ : Fin 148)) (colE2 ⟨39, by decide⟩ 2 hp)
        (rowE2 (⟨140, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨39, by decide⟩ : Fin 148))
        (colE1 ⟨39, by decide⟩ 2 (transLenTr ⟨39, by decide⟩ 2 hp))
        (rowE1 (⟨140, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨140, by decide⟩ : Fin 148) ⟨39, by decide⟩ _
      (validAt ⟨140, by decide⟩ (listedAt ⟨140, by decide⟩ hj))
      (colE1 ⟨39, by decide⟩ 2 (transLenTr ⟨39, by decide⟩ 2 hp)) T140_39
      hfix140_39 hinj140_39 hcardT140_39
      (fun i => conj_mem_of_fixedPoints _ _ (T140_39 i) (hfix140_39 i) _)
      ⟨140, by decide⟩ ⟨39, by decide⟩ _
      (Q2.validAt ⟨140, by decide⟩ (Q2.listedAt ⟨140, by decide⟩
        (alnCheck_rep ⟨140, by decide⟩ hj hq).1))
      (colE2 ⟨39, by decide⟩ 2 hp) Q2.T140_39_2 Q2.hfix140_39_2 Q2.hinj140_39_2
      Q2.hcardT140_39_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T140_39_2 i) (Q2.hfix140_39_2 i) _)
      colCert_140_39_2.hD ?_).symm
  rw [alnId_140 j hj]


theorem leaf_140_39_3 (hp : 3 < (Q2.transData.getD 39 []).length)
    (j : Nat) (hj : j < (repChars.getD 140 []).length)
    (hq : (normIsRep.getD 140 []).getD j false = true) :
    species (Q2.reps (⟨39, by decide⟩ : Fin 148)) (colE2 ⟨39, by decide⟩ 3 hp)
        (rowE2 (⟨140, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨39, by decide⟩ : Fin 148))
        (colE1 ⟨39, by decide⟩ 3 (transLenTr ⟨39, by decide⟩ 3 hp))
        (rowE1 (⟨140, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨140, by decide⟩ : Fin 148) ⟨39, by decide⟩ _
      (validAt ⟨140, by decide⟩ (listedAt ⟨140, by decide⟩ hj))
      (colE1 ⟨39, by decide⟩ 3 (transLenTr ⟨39, by decide⟩ 3 hp)) T140_39
      hfix140_39 hinj140_39 hcardT140_39
      (fun i => conj_mem_of_fixedPoints _ _ (T140_39 i) (hfix140_39 i) _)
      ⟨140, by decide⟩ ⟨39, by decide⟩ _
      (Q2.validAt ⟨140, by decide⟩ (Q2.listedAt ⟨140, by decide⟩
        (alnCheck_rep ⟨140, by decide⟩ hj hq).1))
      (colE2 ⟨39, by decide⟩ 3 hp) Q2.T140_39_2 Q2.hfix140_39_2 Q2.hinj140_39_2
      Q2.hcardT140_39_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T140_39_2 i) (Q2.hfix140_39_2 i) _)
      colCert_140_39_3.hD ?_).symm
  rw [alnId_140 j hj]


theorem leaf_140_39_4 (hp : 4 < (Q2.transData.getD 39 []).length)
    (j : Nat) (hj : j < (repChars.getD 140 []).length)
    (hq : (normIsRep.getD 140 []).getD j false = true) :
    species (Q2.reps (⟨39, by decide⟩ : Fin 148)) (colE2 ⟨39, by decide⟩ 4 hp)
        (rowE2 (⟨140, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨39, by decide⟩ : Fin 148))
        (colE1 ⟨39, by decide⟩ 4 (transLenTr ⟨39, by decide⟩ 4 hp))
        (rowE1 (⟨140, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨140, by decide⟩ : Fin 148) ⟨39, by decide⟩ _
      (validAt ⟨140, by decide⟩ (listedAt ⟨140, by decide⟩ hj))
      (colE1 ⟨39, by decide⟩ 4 (transLenTr ⟨39, by decide⟩ 4 hp)) T140_39
      hfix140_39 hinj140_39 hcardT140_39
      (fun i => conj_mem_of_fixedPoints _ _ (T140_39 i) (hfix140_39 i) _)
      ⟨140, by decide⟩ ⟨39, by decide⟩ _
      (Q2.validAt ⟨140, by decide⟩ (Q2.listedAt ⟨140, by decide⟩
        (alnCheck_rep ⟨140, by decide⟩ hj hq).1))
      (colE2 ⟨39, by decide⟩ 4 hp) Q2.T140_39_2 Q2.hfix140_39_2 Q2.hinj140_39_2
      Q2.hcardT140_39_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T140_39_2 i) (Q2.hfix140_39_2 i) _)
      colCert_140_39_4.hD ?_).symm
  rw [alnId_140 j hj]


theorem leaf_140_39_5 (hp : 5 < (Q2.transData.getD 39 []).length)
    (j : Nat) (hj : j < (repChars.getD 140 []).length)
    (hq : (normIsRep.getD 140 []).getD j false = true) :
    species (Q2.reps (⟨39, by decide⟩ : Fin 148)) (colE2 ⟨39, by decide⟩ 5 hp)
        (rowE2 (⟨140, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨39, by decide⟩ : Fin 148))
        (colE1 ⟨39, by decide⟩ 5 (transLenTr ⟨39, by decide⟩ 5 hp))
        (rowE1 (⟨140, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨140, by decide⟩ : Fin 148) ⟨39, by decide⟩ _
      (validAt ⟨140, by decide⟩ (listedAt ⟨140, by decide⟩ hj))
      (colE1 ⟨39, by decide⟩ 5 (transLenTr ⟨39, by decide⟩ 5 hp)) T140_39
      hfix140_39 hinj140_39 hcardT140_39
      (fun i => conj_mem_of_fixedPoints _ _ (T140_39 i) (hfix140_39 i) _)
      ⟨140, by decide⟩ ⟨39, by decide⟩ _
      (Q2.validAt ⟨140, by decide⟩ (Q2.listedAt ⟨140, by decide⟩
        (alnCheck_rep ⟨140, by decide⟩ hj hq).1))
      (colE2 ⟨39, by decide⟩ 5 hp) Q2.T140_39_2 Q2.hfix140_39_2 Q2.hinj140_39_2
      Q2.hcardT140_39_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T140_39_2 i) (Q2.hfix140_39_2 i) _)
      ?_).symm
  rw [show colData1 (⟨140, by decide⟩ : Fin 148)
        ((colE1 ⟨39, by decide⟩ 5 (transLenTr ⟨39, by decide⟩ 5 hp) : ↥(reps ⟨39, by decide⟩)) : Coordinate 1)
        T140_39 = colFn colCertDiv_140_39_5.D1 (m := 5) from colCertDiv_140_39_5.bind1,
    show colData2 (⟨140, by decide⟩ : Fin 148)
        ((colE2 ⟨39, by decide⟩ 5 hp : ↥(Q2.reps ⟨39, by decide⟩)) : Coordinate 2)
        Q2.T140_39_2 = colFn colCertDiv_140_39_5.D2 (m := 5) from colCertDiv_140_39_5.bind2]
  rw [alnId_140 j hj]
  exact fastcode_of_div ⟨140, by decide⟩ _ _ _
    ((alnId_140 j hj) ▸ Q2.listedAt (⟨140, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨140, by decide⟩ : Fin 148) hj hq).1) colCertDiv_140_39_5_match


theorem leaf_140_39_10 (hp : 10 < (Q2.transData.getD 39 []).length)
    (j : Nat) (hj : j < (repChars.getD 140 []).length)
    (hq : (normIsRep.getD 140 []).getD j false = true) :
    species (Q2.reps (⟨39, by decide⟩ : Fin 148)) (colE2 ⟨39, by decide⟩ 10 hp)
        (rowE2 (⟨140, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨39, by decide⟩ : Fin 148))
        (colE1 ⟨39, by decide⟩ 10 (transLenTr ⟨39, by decide⟩ 10 hp))
        (rowE1 (⟨140, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨140, by decide⟩ : Fin 148) ⟨39, by decide⟩ _
      (validAt ⟨140, by decide⟩ (listedAt ⟨140, by decide⟩ hj))
      (colE1 ⟨39, by decide⟩ 10 (transLenTr ⟨39, by decide⟩ 10 hp)) T140_39
      hfix140_39 hinj140_39 hcardT140_39
      (fun i => conj_mem_of_fixedPoints _ _ (T140_39 i) (hfix140_39 i) _)
      ⟨140, by decide⟩ ⟨39, by decide⟩ _
      (Q2.validAt ⟨140, by decide⟩ (Q2.listedAt ⟨140, by decide⟩
        (alnCheck_rep ⟨140, by decide⟩ hj hq).1))
      (colE2 ⟨39, by decide⟩ 10 hp) Q2.T140_39_2 Q2.hfix140_39_2 Q2.hinj140_39_2
      Q2.hcardT140_39_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T140_39_2 i) (Q2.hfix140_39_2 i) _)
      ?_).symm
  rw [show colData1 (⟨140, by decide⟩ : Fin 148)
        ((colE1 ⟨39, by decide⟩ 10 (transLenTr ⟨39, by decide⟩ 10 hp) : ↥(reps ⟨39, by decide⟩)) : Coordinate 1)
        T140_39 = colFn colCertDiv_140_39_10.D1 (m := 5) from colCertDiv_140_39_10.bind1,
    show colData2 (⟨140, by decide⟩ : Fin 148)
        ((colE2 ⟨39, by decide⟩ 10 hp : ↥(Q2.reps ⟨39, by decide⟩)) : Coordinate 2)
        Q2.T140_39_2 = colFn colCertDiv_140_39_10.D2 (m := 5) from colCertDiv_140_39_10.bind2]
  rw [alnId_140 j hj]
  exact fastcode_of_div ⟨140, by decide⟩ _ _ _
    ((alnId_140 j hj) ▸ Q2.listedAt (⟨140, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨140, by decide⟩ : Fin 148) hj hq).1) colCertDiv_140_39_10_match


theorem leaf_140_39_15 (hp : 15 < (Q2.transData.getD 39 []).length)
    (j : Nat) (hj : j < (repChars.getD 140 []).length)
    (hq : (normIsRep.getD 140 []).getD j false = true) :
    species (Q2.reps (⟨39, by decide⟩ : Fin 148)) (colE2 ⟨39, by decide⟩ 15 hp)
        (rowE2 (⟨140, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨39, by decide⟩ : Fin 148))
        (colE1 ⟨39, by decide⟩ 15 (transLenTr ⟨39, by decide⟩ 15 hp))
        (rowE1 (⟨140, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨140, by decide⟩ : Fin 148) ⟨39, by decide⟩ _
      (validAt ⟨140, by decide⟩ (listedAt ⟨140, by decide⟩ hj))
      (colE1 ⟨39, by decide⟩ 15 (transLenTr ⟨39, by decide⟩ 15 hp)) T140_39
      hfix140_39 hinj140_39 hcardT140_39
      (fun i => conj_mem_of_fixedPoints _ _ (T140_39 i) (hfix140_39 i) _)
      ⟨140, by decide⟩ ⟨39, by decide⟩ _
      (Q2.validAt ⟨140, by decide⟩ (Q2.listedAt ⟨140, by decide⟩
        (alnCheck_rep ⟨140, by decide⟩ hj hq).1))
      (colE2 ⟨39, by decide⟩ 15 hp) Q2.T140_39_2 Q2.hfix140_39_2 Q2.hinj140_39_2
      Q2.hcardT140_39_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T140_39_2 i) (Q2.hfix140_39_2 i) _)
      colCert_140_39_15.hD ?_).symm
  rw [alnId_140 j hj]


theorem leaf_140_39_20 (hp : 20 < (Q2.transData.getD 39 []).length)
    (j : Nat) (hj : j < (repChars.getD 140 []).length)
    (hq : (normIsRep.getD 140 []).getD j false = true) :
    species (Q2.reps (⟨39, by decide⟩ : Fin 148)) (colE2 ⟨39, by decide⟩ 20 hp)
        (rowE2 (⟨140, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨39, by decide⟩ : Fin 148))
        (colE1 ⟨39, by decide⟩ 20 (transLenTr ⟨39, by decide⟩ 20 hp))
        (rowE1 (⟨140, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨140, by decide⟩ : Fin 148) ⟨39, by decide⟩ _
      (validAt ⟨140, by decide⟩ (listedAt ⟨140, by decide⟩ hj))
      (colE1 ⟨39, by decide⟩ 20 (transLenTr ⟨39, by decide⟩ 20 hp)) T140_39
      hfix140_39 hinj140_39 hcardT140_39
      (fun i => conj_mem_of_fixedPoints _ _ (T140_39 i) (hfix140_39 i) _)
      ⟨140, by decide⟩ ⟨39, by decide⟩ _
      (Q2.validAt ⟨140, by decide⟩ (Q2.listedAt ⟨140, by decide⟩
        (alnCheck_rep ⟨140, by decide⟩ hj hq).1))
      (colE2 ⟨39, by decide⟩ 20 hp) Q2.T140_39_2 Q2.hfix140_39_2 Q2.hinj140_39_2
      Q2.hcardT140_39_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T140_39_2 i) (Q2.hfix140_39_2 i) _)
      ?_).symm
  rw [show colData1 (⟨140, by decide⟩ : Fin 148)
        ((colE1 ⟨39, by decide⟩ 20 (transLenTr ⟨39, by decide⟩ 20 hp) : ↥(reps ⟨39, by decide⟩)) : Coordinate 1)
        T140_39 = colFn colCertDiv_140_39_20.D1 (m := 5) from colCertDiv_140_39_20.bind1,
    show colData2 (⟨140, by decide⟩ : Fin 148)
        ((colE2 ⟨39, by decide⟩ 20 hp : ↥(Q2.reps ⟨39, by decide⟩)) : Coordinate 2)
        Q2.T140_39_2 = colFn colCertDiv_140_39_20.D2 (m := 5) from colCertDiv_140_39_20.bind2]
  rw [alnId_140 j hj]
  exact fastcode_of_div ⟨140, by decide⟩ _ _ _
    ((alnId_140 j hj) ▸ Q2.listedAt (⟨140, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨140, by decide⟩ : Fin 148) hj hq).1) colCertDiv_140_39_20_match


theorem leaf_140_46_0 (hp : 0 < (Q2.transData.getD 46 []).length)
    (j : Nat) (hj : j < (repChars.getD 140 []).length)
    (hq : (normIsRep.getD 140 []).getD j false = true) :
    species (Q2.reps (⟨46, by decide⟩ : Fin 148)) (colE2 ⟨46, by decide⟩ 0 hp)
        (rowE2 (⟨140, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨46, by decide⟩ : Fin 148))
        (colE1 ⟨46, by decide⟩ 0 (transLenTr ⟨46, by decide⟩ 0 hp))
        (rowE1 (⟨140, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨140, by decide⟩ : Fin 148) ⟨46, by decide⟩ _
      (validAt ⟨140, by decide⟩ (listedAt ⟨140, by decide⟩ hj))
      (colE1 ⟨46, by decide⟩ 0 (transLenTr ⟨46, by decide⟩ 0 hp)) T140_46
      hfix140_46 hinj140_46 hcardT140_46
      (fun i => conj_mem_of_fixedPoints _ _ (T140_46 i) (hfix140_46 i) _)
      ⟨140, by decide⟩ ⟨46, by decide⟩ _
      (Q2.validAt ⟨140, by decide⟩ (Q2.listedAt ⟨140, by decide⟩
        (alnCheck_rep ⟨140, by decide⟩ hj hq).1))
      (colE2 ⟨46, by decide⟩ 0 hp) Q2.T140_46_2 Q2.hfix140_46_2 Q2.hinj140_46_2
      Q2.hcardT140_46_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T140_46_2 i) (Q2.hfix140_46_2 i) _)
      colCert_140_46_0.hD ?_).symm
  rw [alnId_140 j hj]


theorem leaf_140_46_1 (hp : 1 < (Q2.transData.getD 46 []).length)
    (j : Nat) (hj : j < (repChars.getD 140 []).length)
    (hq : (normIsRep.getD 140 []).getD j false = true) :
    species (Q2.reps (⟨46, by decide⟩ : Fin 148)) (colE2 ⟨46, by decide⟩ 1 hp)
        (rowE2 (⟨140, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨46, by decide⟩ : Fin 148))
        (colE1 ⟨46, by decide⟩ 1 (transLenTr ⟨46, by decide⟩ 1 hp))
        (rowE1 (⟨140, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨140, by decide⟩ : Fin 148) ⟨46, by decide⟩ _
      (validAt ⟨140, by decide⟩ (listedAt ⟨140, by decide⟩ hj))
      (colE1 ⟨46, by decide⟩ 1 (transLenTr ⟨46, by decide⟩ 1 hp)) T140_46
      hfix140_46 hinj140_46 hcardT140_46
      (fun i => conj_mem_of_fixedPoints _ _ (T140_46 i) (hfix140_46 i) _)
      ⟨140, by decide⟩ ⟨46, by decide⟩ _
      (Q2.validAt ⟨140, by decide⟩ (Q2.listedAt ⟨140, by decide⟩
        (alnCheck_rep ⟨140, by decide⟩ hj hq).1))
      (colE2 ⟨46, by decide⟩ 1 hp) Q2.T140_46_2 Q2.hfix140_46_2 Q2.hinj140_46_2
      Q2.hcardT140_46_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T140_46_2 i) (Q2.hfix140_46_2 i) _)
      colCert_140_46_1.hD ?_).symm
  rw [alnId_140 j hj]


theorem leaf_140_46_2 (hp : 2 < (Q2.transData.getD 46 []).length)
    (j : Nat) (hj : j < (repChars.getD 140 []).length)
    (hq : (normIsRep.getD 140 []).getD j false = true) :
    species (Q2.reps (⟨46, by decide⟩ : Fin 148)) (colE2 ⟨46, by decide⟩ 2 hp)
        (rowE2 (⟨140, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨46, by decide⟩ : Fin 148))
        (colE1 ⟨46, by decide⟩ 2 (transLenTr ⟨46, by decide⟩ 2 hp))
        (rowE1 (⟨140, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨140, by decide⟩ : Fin 148) ⟨46, by decide⟩ _
      (validAt ⟨140, by decide⟩ (listedAt ⟨140, by decide⟩ hj))
      (colE1 ⟨46, by decide⟩ 2 (transLenTr ⟨46, by decide⟩ 2 hp)) T140_46
      hfix140_46 hinj140_46 hcardT140_46
      (fun i => conj_mem_of_fixedPoints _ _ (T140_46 i) (hfix140_46 i) _)
      ⟨140, by decide⟩ ⟨46, by decide⟩ _
      (Q2.validAt ⟨140, by decide⟩ (Q2.listedAt ⟨140, by decide⟩
        (alnCheck_rep ⟨140, by decide⟩ hj hq).1))
      (colE2 ⟨46, by decide⟩ 2 hp) Q2.T140_46_2 Q2.hfix140_46_2 Q2.hinj140_46_2
      Q2.hcardT140_46_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T140_46_2 i) (Q2.hfix140_46_2 i) _)
      colCert_140_46_2.hD ?_).symm
  rw [alnId_140 j hj]


theorem leaf_140_46_3 (hp : 3 < (Q2.transData.getD 46 []).length)
    (j : Nat) (hj : j < (repChars.getD 140 []).length)
    (hq : (normIsRep.getD 140 []).getD j false = true) :
    species (Q2.reps (⟨46, by decide⟩ : Fin 148)) (colE2 ⟨46, by decide⟩ 3 hp)
        (rowE2 (⟨140, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨46, by decide⟩ : Fin 148))
        (colE1 ⟨46, by decide⟩ 3 (transLenTr ⟨46, by decide⟩ 3 hp))
        (rowE1 (⟨140, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨140, by decide⟩ : Fin 148) ⟨46, by decide⟩ _
      (validAt ⟨140, by decide⟩ (listedAt ⟨140, by decide⟩ hj))
      (colE1 ⟨46, by decide⟩ 3 (transLenTr ⟨46, by decide⟩ 3 hp)) T140_46
      hfix140_46 hinj140_46 hcardT140_46
      (fun i => conj_mem_of_fixedPoints _ _ (T140_46 i) (hfix140_46 i) _)
      ⟨140, by decide⟩ ⟨46, by decide⟩ _
      (Q2.validAt ⟨140, by decide⟩ (Q2.listedAt ⟨140, by decide⟩
        (alnCheck_rep ⟨140, by decide⟩ hj hq).1))
      (colE2 ⟨46, by decide⟩ 3 hp) Q2.T140_46_2 Q2.hfix140_46_2 Q2.hinj140_46_2
      Q2.hcardT140_46_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T140_46_2 i) (Q2.hfix140_46_2 i) _)
      colCert_140_46_3.hD ?_).symm
  rw [alnId_140 j hj]


theorem leaf_140_46_4 (hp : 4 < (Q2.transData.getD 46 []).length)
    (j : Nat) (hj : j < (repChars.getD 140 []).length)
    (hq : (normIsRep.getD 140 []).getD j false = true) :
    species (Q2.reps (⟨46, by decide⟩ : Fin 148)) (colE2 ⟨46, by decide⟩ 4 hp)
        (rowE2 (⟨140, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨46, by decide⟩ : Fin 148))
        (colE1 ⟨46, by decide⟩ 4 (transLenTr ⟨46, by decide⟩ 4 hp))
        (rowE1 (⟨140, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨140, by decide⟩ : Fin 148) ⟨46, by decide⟩ _
      (validAt ⟨140, by decide⟩ (listedAt ⟨140, by decide⟩ hj))
      (colE1 ⟨46, by decide⟩ 4 (transLenTr ⟨46, by decide⟩ 4 hp)) T140_46
      hfix140_46 hinj140_46 hcardT140_46
      (fun i => conj_mem_of_fixedPoints _ _ (T140_46 i) (hfix140_46 i) _)
      ⟨140, by decide⟩ ⟨46, by decide⟩ _
      (Q2.validAt ⟨140, by decide⟩ (Q2.listedAt ⟨140, by decide⟩
        (alnCheck_rep ⟨140, by decide⟩ hj hq).1))
      (colE2 ⟨46, by decide⟩ 4 hp) Q2.T140_46_2 Q2.hfix140_46_2 Q2.hinj140_46_2
      Q2.hcardT140_46_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T140_46_2 i) (Q2.hfix140_46_2 i) _)
      colCert_140_46_4.hD ?_).symm
  rw [alnId_140 j hj]


theorem leaf_140_46_5 (hp : 5 < (Q2.transData.getD 46 []).length)
    (j : Nat) (hj : j < (repChars.getD 140 []).length)
    (hq : (normIsRep.getD 140 []).getD j false = true) :
    species (Q2.reps (⟨46, by decide⟩ : Fin 148)) (colE2 ⟨46, by decide⟩ 5 hp)
        (rowE2 (⟨140, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨46, by decide⟩ : Fin 148))
        (colE1 ⟨46, by decide⟩ 5 (transLenTr ⟨46, by decide⟩ 5 hp))
        (rowE1 (⟨140, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨140, by decide⟩ : Fin 148) ⟨46, by decide⟩ _
      (validAt ⟨140, by decide⟩ (listedAt ⟨140, by decide⟩ hj))
      (colE1 ⟨46, by decide⟩ 5 (transLenTr ⟨46, by decide⟩ 5 hp)) T140_46
      hfix140_46 hinj140_46 hcardT140_46
      (fun i => conj_mem_of_fixedPoints _ _ (T140_46 i) (hfix140_46 i) _)
      ⟨140, by decide⟩ ⟨46, by decide⟩ _
      (Q2.validAt ⟨140, by decide⟩ (Q2.listedAt ⟨140, by decide⟩
        (alnCheck_rep ⟨140, by decide⟩ hj hq).1))
      (colE2 ⟨46, by decide⟩ 5 hp) Q2.T140_46_2 Q2.hfix140_46_2 Q2.hinj140_46_2
      Q2.hcardT140_46_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T140_46_2 i) (Q2.hfix140_46_2 i) _)
      colCert_140_46_5.hD ?_).symm
  rw [alnId_140 j hj]


theorem leaf_140_46_10 (hp : 10 < (Q2.transData.getD 46 []).length)
    (j : Nat) (hj : j < (repChars.getD 140 []).length)
    (hq : (normIsRep.getD 140 []).getD j false = true) :
    species (Q2.reps (⟨46, by decide⟩ : Fin 148)) (colE2 ⟨46, by decide⟩ 10 hp)
        (rowE2 (⟨140, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨46, by decide⟩ : Fin 148))
        (colE1 ⟨46, by decide⟩ 10 (transLenTr ⟨46, by decide⟩ 10 hp))
        (rowE1 (⟨140, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨140, by decide⟩ : Fin 148) ⟨46, by decide⟩ _
      (validAt ⟨140, by decide⟩ (listedAt ⟨140, by decide⟩ hj))
      (colE1 ⟨46, by decide⟩ 10 (transLenTr ⟨46, by decide⟩ 10 hp)) T140_46
      hfix140_46 hinj140_46 hcardT140_46
      (fun i => conj_mem_of_fixedPoints _ _ (T140_46 i) (hfix140_46 i) _)
      ⟨140, by decide⟩ ⟨46, by decide⟩ _
      (Q2.validAt ⟨140, by decide⟩ (Q2.listedAt ⟨140, by decide⟩
        (alnCheck_rep ⟨140, by decide⟩ hj hq).1))
      (colE2 ⟨46, by decide⟩ 10 hp) Q2.T140_46_2 Q2.hfix140_46_2 Q2.hinj140_46_2
      Q2.hcardT140_46_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T140_46_2 i) (Q2.hfix140_46_2 i) _)
      ?_).symm
  rw [show colData1 (⟨140, by decide⟩ : Fin 148)
        ((colE1 ⟨46, by decide⟩ 10 (transLenTr ⟨46, by decide⟩ 10 hp) : ↥(reps ⟨46, by decide⟩)) : Coordinate 1)
        T140_46 = colFn colCertDiv_140_46_10.D1 (m := 5) from colCertDiv_140_46_10.bind1,
    show colData2 (⟨140, by decide⟩ : Fin 148)
        ((colE2 ⟨46, by decide⟩ 10 hp : ↥(Q2.reps ⟨46, by decide⟩)) : Coordinate 2)
        Q2.T140_46_2 = colFn colCertDiv_140_46_10.D2 (m := 5) from colCertDiv_140_46_10.bind2]
  rw [alnId_140 j hj]
  exact fastcode_of_div ⟨140, by decide⟩ _ _ _
    ((alnId_140 j hj) ▸ Q2.listedAt (⟨140, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨140, by decide⟩ : Fin 148) hj hq).1) colCertDiv_140_46_10_match


theorem leaf_140_46_15 (hp : 15 < (Q2.transData.getD 46 []).length)
    (j : Nat) (hj : j < (repChars.getD 140 []).length)
    (hq : (normIsRep.getD 140 []).getD j false = true) :
    species (Q2.reps (⟨46, by decide⟩ : Fin 148)) (colE2 ⟨46, by decide⟩ 15 hp)
        (rowE2 (⟨140, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨46, by decide⟩ : Fin 148))
        (colE1 ⟨46, by decide⟩ 15 (transLenTr ⟨46, by decide⟩ 15 hp))
        (rowE1 (⟨140, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨140, by decide⟩ : Fin 148) ⟨46, by decide⟩ _
      (validAt ⟨140, by decide⟩ (listedAt ⟨140, by decide⟩ hj))
      (colE1 ⟨46, by decide⟩ 15 (transLenTr ⟨46, by decide⟩ 15 hp)) T140_46
      hfix140_46 hinj140_46 hcardT140_46
      (fun i => conj_mem_of_fixedPoints _ _ (T140_46 i) (hfix140_46 i) _)
      ⟨140, by decide⟩ ⟨46, by decide⟩ _
      (Q2.validAt ⟨140, by decide⟩ (Q2.listedAt ⟨140, by decide⟩
        (alnCheck_rep ⟨140, by decide⟩ hj hq).1))
      (colE2 ⟨46, by decide⟩ 15 hp) Q2.T140_46_2 Q2.hfix140_46_2 Q2.hinj140_46_2
      Q2.hcardT140_46_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T140_46_2 i) (Q2.hfix140_46_2 i) _)
      ?_).symm
  rw [show colData1 (⟨140, by decide⟩ : Fin 148)
        ((colE1 ⟨46, by decide⟩ 15 (transLenTr ⟨46, by decide⟩ 15 hp) : ↥(reps ⟨46, by decide⟩)) : Coordinate 1)
        T140_46 = colFn colCertDiv_140_46_15.D1 (m := 5) from colCertDiv_140_46_15.bind1,
    show colData2 (⟨140, by decide⟩ : Fin 148)
        ((colE2 ⟨46, by decide⟩ 15 hp : ↥(Q2.reps ⟨46, by decide⟩)) : Coordinate 2)
        Q2.T140_46_2 = colFn colCertDiv_140_46_15.D2 (m := 5) from colCertDiv_140_46_15.bind2]
  rw [alnId_140 j hj]
  exact fastcode_of_div ⟨140, by decide⟩ _ _ _
    ((alnId_140 j hj) ▸ Q2.listedAt (⟨140, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨140, by decide⟩ : Fin 148) hj hq).1) colCertDiv_140_46_15_match


end LeanDring.P5Presentation
