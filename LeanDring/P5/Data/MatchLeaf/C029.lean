/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Data.ColCdd.C006
import LeanDring.P5.Data.ColCdd.C007
import LeanDring.P5.Data.ColRestCheap.C042
import LeanDring.P5.Data.ColRestCheap.C043
import LeanDring.P5.Data.ColRestCheap.C044
import LeanDring.P5.Data.ColTau.C001
import LeanDring.P5.Data.EntryK.C029
import LeanDring.P5.Certificate.RingIsomorphism.MatchCore
import LeanDring.P5.Data.SpeciesDiv.C059
import LeanDring.P5.Data.SpeciesDiv.C060
import LeanDring.P5.Data.SpeciesDiv.C061
import LeanDring.P5.Data.SpeciesDiv.C062
import LeanDring.P5.Certificate.SpeciesTable.Twin2.SpeciesTau.Chunk02

/-! # Stage-5 leaves, chunk 28 (auto-emitted).  -/

namespace LeanDring.P5Presentation

open MulAction Finset LeanDring.DRing LeanDring.MonGSet

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.style.longLine false

theorem leaf_120_13_6 (hp : 6 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 6 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 6 (transLenTr ⟨13, by decide⟩ 6 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨120, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 6 (transLenTr ⟨13, by decide⟩ 6 hp)) T120_13
      hfix120_13 hinj120_13 hcardT120_13
      (fun i => conj_mem_of_fixedPoints _ _ (T120_13 i) (hfix120_13 i) _)
      ⟨120, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 6 hp) Q2.T120_13_2 Q2.hfix120_13_2 Q2.hinj120_13_2
      Q2.hcardT120_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_13_2 i) (Q2.hfix120_13_2 i) _)
      ?_).symm
  rw [show colData1 (⟨120, by decide⟩ : Fin 148)
        ((colE1 ⟨13, by decide⟩ 6 (transLenTr ⟨13, by decide⟩ 6 hp) : ↥(reps ⟨13, by decide⟩)) : Coordinate 1)
        T120_13 = colFn colCertDiv_120_13_6.D1 (m := 5) from colCertDiv_120_13_6.bind1,
    show colData2 (⟨120, by decide⟩ : Fin 148)
        ((colE2 ⟨13, by decide⟩ 6 hp : ↥(Q2.reps ⟨13, by decide⟩)) : Coordinate 2)
        Q2.T120_13_2 = colFn colCertDiv_120_13_6.D2 (m := 5) from colCertDiv_120_13_6.bind2]
  rw [alnId_120 j hj]
  exact fastcode_of_tau ⟨120, by decide⟩ _ _ _
    ((alnId_120 j hj) ▸ Q2.listedAt (⟨120, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨120, by decide⟩ : Fin 148) hj hq).1) colCertDiv_120_13_6_tau_match


theorem leaf_120_13_7 (hp : 7 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 7 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 7 (transLenTr ⟨13, by decide⟩ 7 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨120, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 7 (transLenTr ⟨13, by decide⟩ 7 hp)) T120_13
      hfix120_13 hinj120_13 hcardT120_13
      (fun i => conj_mem_of_fixedPoints _ _ (T120_13 i) (hfix120_13 i) _)
      ⟨120, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 7 hp) Q2.T120_13_2 Q2.hfix120_13_2 Q2.hinj120_13_2
      Q2.hcardT120_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_13_2 i) (Q2.hfix120_13_2 i) _)
      ?_).symm
  rw [show colData1 (⟨120, by decide⟩ : Fin 148)
        ((colE1 ⟨13, by decide⟩ 7 (transLenTr ⟨13, by decide⟩ 7 hp) : ↥(reps ⟨13, by decide⟩)) : Coordinate 1)
        T120_13 = colFn colCertDiv_120_13_7.D1 (m := 5) from colCertDiv_120_13_7.bind1,
    show colData2 (⟨120, by decide⟩ : Fin 148)
        ((colE2 ⟨13, by decide⟩ 7 hp : ↥(Q2.reps ⟨13, by decide⟩)) : Coordinate 2)
        Q2.T120_13_2 = colFn colCertDiv_120_13_7.D2 (m := 5) from colCertDiv_120_13_7.bind2]
  rw [alnId_120 j hj]
  exact fastcode_of_tau ⟨120, by decide⟩ _ _ _
    ((alnId_120 j hj) ▸ Q2.listedAt (⟨120, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨120, by decide⟩ : Fin 148) hj hq).1) colCertDiv_120_13_7_tau_match


theorem leaf_120_13_8 (hp : 8 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 8 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 8 (transLenTr ⟨13, by decide⟩ 8 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨120, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 8 (transLenTr ⟨13, by decide⟩ 8 hp)) T120_13
      hfix120_13 hinj120_13 hcardT120_13
      (fun i => conj_mem_of_fixedPoints _ _ (T120_13 i) (hfix120_13 i) _)
      ⟨120, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 8 hp) Q2.T120_13_2 Q2.hfix120_13_2 Q2.hinj120_13_2
      Q2.hcardT120_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_13_2 i) (Q2.hfix120_13_2 i) _)
      ?_).symm
  rw [show colData1 (⟨120, by decide⟩ : Fin 148)
        ((colE1 ⟨13, by decide⟩ 8 (transLenTr ⟨13, by decide⟩ 8 hp) : ↥(reps ⟨13, by decide⟩)) : Coordinate 1)
        T120_13 = colFn colCertDiv_120_13_8.D1 (m := 5) from colCertDiv_120_13_8.bind1,
    show colData2 (⟨120, by decide⟩ : Fin 148)
        ((colE2 ⟨13, by decide⟩ 8 hp : ↥(Q2.reps ⟨13, by decide⟩)) : Coordinate 2)
        Q2.T120_13_2 = colFn colCertDiv_120_13_8.D2 (m := 5) from colCertDiv_120_13_8.bind2]
  rw [alnId_120 j hj]
  exact fastcode_of_tau ⟨120, by decide⟩ _ _ _
    ((alnId_120 j hj) ▸ Q2.listedAt (⟨120, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨120, by decide⟩ : Fin 148) hj hq).1) colCertDiv_120_13_8_tau_match


theorem leaf_120_13_9 (hp : 9 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 9 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 9 (transLenTr ⟨13, by decide⟩ 9 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 9 (transLenTr ⟨13, by decide⟩ 9 hp)) T120_13
      hfix120_13 hinj120_13 hcardT120_13
      (fun i => conj_mem_of_fixedPoints _ _ (T120_13 i) (hfix120_13 i) _)
      ⟨120, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 9 hp) Q2.T120_13_2 Q2.hfix120_13_2 Q2.hinj120_13_2
      Q2.hcardT120_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_13_2 i) (Q2.hfix120_13_2 i) _)
      colCert_120_13_9.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_13_10 (hp : 10 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 10 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 10 (transLenTr ⟨13, by decide⟩ 10 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 10 (transLenTr ⟨13, by decide⟩ 10 hp)) T120_13
      hfix120_13 hinj120_13 hcardT120_13
      (fun i => conj_mem_of_fixedPoints _ _ (T120_13 i) (hfix120_13 i) _)
      ⟨120, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 10 hp) Q2.T120_13_2 Q2.hfix120_13_2 Q2.hinj120_13_2
      Q2.hcardT120_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_13_2 i) (Q2.hfix120_13_2 i) _)
      colCert_120_13_10.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_13_11 (hp : 11 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 11 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 11 (transLenTr ⟨13, by decide⟩ 11 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 11 (transLenTr ⟨13, by decide⟩ 11 hp)) T120_13
      hfix120_13 hinj120_13 hcardT120_13
      (fun i => conj_mem_of_fixedPoints _ _ (T120_13 i) (hfix120_13 i) _)
      ⟨120, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 11 hp) Q2.T120_13_2 Q2.hfix120_13_2 Q2.hinj120_13_2
      Q2.hcardT120_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_13_2 i) (Q2.hfix120_13_2 i) _)
      colCert_120_13_11.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_13_12 (hp : 12 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 12 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 12 (transLenTr ⟨13, by decide⟩ 12 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 12 (transLenTr ⟨13, by decide⟩ 12 hp)) T120_13
      hfix120_13 hinj120_13 hcardT120_13
      (fun i => conj_mem_of_fixedPoints _ _ (T120_13 i) (hfix120_13 i) _)
      ⟨120, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 12 hp) Q2.T120_13_2 Q2.hfix120_13_2 Q2.hinj120_13_2
      Q2.hcardT120_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_13_2 i) (Q2.hfix120_13_2 i) _)
      colCert_120_13_12.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_13_13 (hp : 13 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 13 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 13 (transLenTr ⟨13, by decide⟩ 13 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 13 (transLenTr ⟨13, by decide⟩ 13 hp)) T120_13
      hfix120_13 hinj120_13 hcardT120_13
      (fun i => conj_mem_of_fixedPoints _ _ (T120_13 i) (hfix120_13 i) _)
      ⟨120, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 13 hp) Q2.T120_13_2 Q2.hfix120_13_2 Q2.hinj120_13_2
      Q2.hcardT120_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_13_2 i) (Q2.hfix120_13_2 i) _)
      colCert_120_13_13.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_13_14 (hp : 14 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 14 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 14 (transLenTr ⟨13, by decide⟩ 14 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 14 (transLenTr ⟨13, by decide⟩ 14 hp)) T120_13
      hfix120_13 hinj120_13 hcardT120_13
      (fun i => conj_mem_of_fixedPoints _ _ (T120_13 i) (hfix120_13 i) _)
      ⟨120, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 14 hp) Q2.T120_13_2 Q2.hfix120_13_2 Q2.hinj120_13_2
      Q2.hcardT120_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_13_2 i) (Q2.hfix120_13_2 i) _)
      colCert_120_13_14.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_13_15 (hp : 15 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 15 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 15 (transLenTr ⟨13, by decide⟩ 15 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 15 (transLenTr ⟨13, by decide⟩ 15 hp)) T120_13
      hfix120_13 hinj120_13 hcardT120_13
      (fun i => conj_mem_of_fixedPoints _ _ (T120_13 i) (hfix120_13 i) _)
      ⟨120, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 15 hp) Q2.T120_13_2 Q2.hfix120_13_2 Q2.hinj120_13_2
      Q2.hcardT120_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_13_2 i) (Q2.hfix120_13_2 i) _)
      colCert_120_13_15.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_13_16 (hp : 16 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 16 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 16 (transLenTr ⟨13, by decide⟩ 16 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 16 (transLenTr ⟨13, by decide⟩ 16 hp)) T120_13
      hfix120_13 hinj120_13 hcardT120_13
      (fun i => conj_mem_of_fixedPoints _ _ (T120_13 i) (hfix120_13 i) _)
      ⟨120, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 16 hp) Q2.T120_13_2 Q2.hfix120_13_2 Q2.hinj120_13_2
      Q2.hcardT120_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_13_2 i) (Q2.hfix120_13_2 i) _)
      colCert_120_13_16.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_13_17 (hp : 17 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 17 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 17 (transLenTr ⟨13, by decide⟩ 17 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 17 (transLenTr ⟨13, by decide⟩ 17 hp)) T120_13
      hfix120_13 hinj120_13 hcardT120_13
      (fun i => conj_mem_of_fixedPoints _ _ (T120_13 i) (hfix120_13 i) _)
      ⟨120, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 17 hp) Q2.T120_13_2 Q2.hfix120_13_2 Q2.hinj120_13_2
      Q2.hcardT120_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_13_2 i) (Q2.hfix120_13_2 i) _)
      colCert_120_13_17.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_13_18 (hp : 18 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 18 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 18 (transLenTr ⟨13, by decide⟩ 18 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 18 (transLenTr ⟨13, by decide⟩ 18 hp)) T120_13
      hfix120_13 hinj120_13 hcardT120_13
      (fun i => conj_mem_of_fixedPoints _ _ (T120_13 i) (hfix120_13 i) _)
      ⟨120, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 18 hp) Q2.T120_13_2 Q2.hfix120_13_2 Q2.hinj120_13_2
      Q2.hcardT120_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_13_2 i) (Q2.hfix120_13_2 i) _)
      colCert_120_13_18.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_13_19 (hp : 19 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 19 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 19 (transLenTr ⟨13, by decide⟩ 19 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 19 (transLenTr ⟨13, by decide⟩ 19 hp)) T120_13
      hfix120_13 hinj120_13 hcardT120_13
      (fun i => conj_mem_of_fixedPoints _ _ (T120_13 i) (hfix120_13 i) _)
      ⟨120, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 19 hp) Q2.T120_13_2 Q2.hfix120_13_2 Q2.hinj120_13_2
      Q2.hcardT120_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_13_2 i) (Q2.hfix120_13_2 i) _)
      colCert_120_13_19.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_13_20 (hp : 20 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 20 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 20 (transLenTr ⟨13, by decide⟩ 20 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 20 (transLenTr ⟨13, by decide⟩ 20 hp)) T120_13
      hfix120_13 hinj120_13 hcardT120_13
      (fun i => conj_mem_of_fixedPoints _ _ (T120_13 i) (hfix120_13 i) _)
      ⟨120, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 20 hp) Q2.T120_13_2 Q2.hfix120_13_2 Q2.hinj120_13_2
      Q2.hcardT120_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_13_2 i) (Q2.hfix120_13_2 i) _)
      colCert_120_13_20.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_13_21 (hp : 21 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 21 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 21 (transLenTr ⟨13, by decide⟩ 21 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 21 (transLenTr ⟨13, by decide⟩ 21 hp)) T120_13
      hfix120_13 hinj120_13 hcardT120_13
      (fun i => conj_mem_of_fixedPoints _ _ (T120_13 i) (hfix120_13 i) _)
      ⟨120, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 21 hp) Q2.T120_13_2 Q2.hfix120_13_2 Q2.hinj120_13_2
      Q2.hcardT120_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_13_2 i) (Q2.hfix120_13_2 i) _)
      colCert_120_13_21.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_13_22 (hp : 22 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 22 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 22 (transLenTr ⟨13, by decide⟩ 22 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 22 (transLenTr ⟨13, by decide⟩ 22 hp)) T120_13
      hfix120_13 hinj120_13 hcardT120_13
      (fun i => conj_mem_of_fixedPoints _ _ (T120_13 i) (hfix120_13 i) _)
      ⟨120, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 22 hp) Q2.T120_13_2 Q2.hfix120_13_2 Q2.hinj120_13_2
      Q2.hcardT120_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_13_2 i) (Q2.hfix120_13_2 i) _)
      colCert_120_13_22.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_13_23 (hp : 23 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 23 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 23 (transLenTr ⟨13, by decide⟩ 23 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 23 (transLenTr ⟨13, by decide⟩ 23 hp)) T120_13
      hfix120_13 hinj120_13 hcardT120_13
      (fun i => conj_mem_of_fixedPoints _ _ (T120_13 i) (hfix120_13 i) _)
      ⟨120, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 23 hp) Q2.T120_13_2 Q2.hfix120_13_2 Q2.hinj120_13_2
      Q2.hcardT120_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_13_2 i) (Q2.hfix120_13_2 i) _)
      colCert_120_13_23.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_13_24 (hp : 24 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 24 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 24 (transLenTr ⟨13, by decide⟩ 24 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 24 (transLenTr ⟨13, by decide⟩ 24 hp)) T120_13
      hfix120_13 hinj120_13 hcardT120_13
      (fun i => conj_mem_of_fixedPoints _ _ (T120_13 i) (hfix120_13 i) _)
      ⟨120, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 24 hp) Q2.T120_13_2 Q2.hfix120_13_2 Q2.hinj120_13_2
      Q2.hcardT120_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_13_2 i) (Q2.hfix120_13_2 i) _)
      colCert_120_13_24.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_19_0 (hp : 0 < (Q2.transData.getD 19 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨19, by decide⟩ : Fin 148)) (colE2 ⟨19, by decide⟩ 0 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨19, by decide⟩ : Fin 148))
        (colE1 ⟨19, by decide⟩ 0 (transLenTr ⟨19, by decide⟩ 0 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨19, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨19, by decide⟩ 0 (transLenTr ⟨19, by decide⟩ 0 hp)) T120_19
      hfix120_19 hinj120_19 hcardT120_19
      (fun i => conj_mem_of_fixedPoints _ _ (T120_19 i) (hfix120_19 i) _)
      ⟨120, by decide⟩ ⟨19, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨19, by decide⟩ 0 hp) Q2.T120_19_2 Q2.hfix120_19_2 Q2.hinj120_19_2
      Q2.hcardT120_19_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_19_2 i) (Q2.hfix120_19_2 i) _)
      colCert_120_19_0.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_19_1 (hp : 1 < (Q2.transData.getD 19 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨19, by decide⟩ : Fin 148)) (colE2 ⟨19, by decide⟩ 1 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨19, by decide⟩ : Fin 148))
        (colE1 ⟨19, by decide⟩ 1 (transLenTr ⟨19, by decide⟩ 1 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨19, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨19, by decide⟩ 1 (transLenTr ⟨19, by decide⟩ 1 hp)) T120_19
      hfix120_19 hinj120_19 hcardT120_19
      (fun i => conj_mem_of_fixedPoints _ _ (T120_19 i) (hfix120_19 i) _)
      ⟨120, by decide⟩ ⟨19, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨19, by decide⟩ 1 hp) Q2.T120_19_2 Q2.hfix120_19_2 Q2.hinj120_19_2
      Q2.hcardT120_19_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_19_2 i) (Q2.hfix120_19_2 i) _)
      colCert_120_19_1.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_19_2 (hp : 2 < (Q2.transData.getD 19 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨19, by decide⟩ : Fin 148)) (colE2 ⟨19, by decide⟩ 2 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨19, by decide⟩ : Fin 148))
        (colE1 ⟨19, by decide⟩ 2 (transLenTr ⟨19, by decide⟩ 2 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨19, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨19, by decide⟩ 2 (transLenTr ⟨19, by decide⟩ 2 hp)) T120_19
      hfix120_19 hinj120_19 hcardT120_19
      (fun i => conj_mem_of_fixedPoints _ _ (T120_19 i) (hfix120_19 i) _)
      ⟨120, by decide⟩ ⟨19, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨19, by decide⟩ 2 hp) Q2.T120_19_2 Q2.hfix120_19_2 Q2.hinj120_19_2
      Q2.hcardT120_19_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_19_2 i) (Q2.hfix120_19_2 i) _)
      colCert_120_19_2.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_19_3 (hp : 3 < (Q2.transData.getD 19 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨19, by decide⟩ : Fin 148)) (colE2 ⟨19, by decide⟩ 3 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨19, by decide⟩ : Fin 148))
        (colE1 ⟨19, by decide⟩ 3 (transLenTr ⟨19, by decide⟩ 3 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨19, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨19, by decide⟩ 3 (transLenTr ⟨19, by decide⟩ 3 hp)) T120_19
      hfix120_19 hinj120_19 hcardT120_19
      (fun i => conj_mem_of_fixedPoints _ _ (T120_19 i) (hfix120_19 i) _)
      ⟨120, by decide⟩ ⟨19, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨19, by decide⟩ 3 hp) Q2.T120_19_2 Q2.hfix120_19_2 Q2.hinj120_19_2
      Q2.hcardT120_19_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_19_2 i) (Q2.hfix120_19_2 i) _)
      colCert_120_19_3.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_19_4 (hp : 4 < (Q2.transData.getD 19 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨19, by decide⟩ : Fin 148)) (colE2 ⟨19, by decide⟩ 4 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨19, by decide⟩ : Fin 148))
        (colE1 ⟨19, by decide⟩ 4 (transLenTr ⟨19, by decide⟩ 4 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨19, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨19, by decide⟩ 4 (transLenTr ⟨19, by decide⟩ 4 hp)) T120_19
      hfix120_19 hinj120_19 hcardT120_19
      (fun i => conj_mem_of_fixedPoints _ _ (T120_19 i) (hfix120_19 i) _)
      ⟨120, by decide⟩ ⟨19, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨19, by decide⟩ 4 hp) Q2.T120_19_2 Q2.hfix120_19_2 Q2.hinj120_19_2
      Q2.hcardT120_19_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_19_2 i) (Q2.hfix120_19_2 i) _)
      colCert_120_19_4.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_19_5 (hp : 5 < (Q2.transData.getD 19 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨19, by decide⟩ : Fin 148)) (colE2 ⟨19, by decide⟩ 5 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨19, by decide⟩ : Fin 148))
        (colE1 ⟨19, by decide⟩ 5 (transLenTr ⟨19, by decide⟩ 5 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨19, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨19, by decide⟩ 5 (transLenTr ⟨19, by decide⟩ 5 hp)) T120_19
      hfix120_19 hinj120_19 hcardT120_19
      (fun i => conj_mem_of_fixedPoints _ _ (T120_19 i) (hfix120_19 i) _)
      ⟨120, by decide⟩ ⟨19, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨19, by decide⟩ 5 hp) Q2.T120_19_2 Q2.hfix120_19_2 Q2.hinj120_19_2
      Q2.hcardT120_19_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_19_2 i) (Q2.hfix120_19_2 i) _)
      colCert_120_19_5.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_19_10 (hp : 10 < (Q2.transData.getD 19 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨19, by decide⟩ : Fin 148)) (colE2 ⟨19, by decide⟩ 10 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨19, by decide⟩ : Fin 148))
        (colE1 ⟨19, by decide⟩ 10 (transLenTr ⟨19, by decide⟩ 10 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨19, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨19, by decide⟩ 10 (transLenTr ⟨19, by decide⟩ 10 hp)) T120_19
      hfix120_19 hinj120_19 hcardT120_19
      (fun i => conj_mem_of_fixedPoints _ _ (T120_19 i) (hfix120_19 i) _)
      ⟨120, by decide⟩ ⟨19, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨19, by decide⟩ 10 hp) Q2.T120_19_2 Q2.hfix120_19_2 Q2.hinj120_19_2
      Q2.hcardT120_19_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_19_2 i) (Q2.hfix120_19_2 i) _)
      colCert_120_19_10.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_19_15 (hp : 15 < (Q2.transData.getD 19 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨19, by decide⟩ : Fin 148)) (colE2 ⟨19, by decide⟩ 15 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨19, by decide⟩ : Fin 148))
        (colE1 ⟨19, by decide⟩ 15 (transLenTr ⟨19, by decide⟩ 15 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨19, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨19, by decide⟩ 15 (transLenTr ⟨19, by decide⟩ 15 hp)) T120_19
      hfix120_19 hinj120_19 hcardT120_19
      (fun i => conj_mem_of_fixedPoints _ _ (T120_19 i) (hfix120_19 i) _)
      ⟨120, by decide⟩ ⟨19, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨19, by decide⟩ 15 hp) Q2.T120_19_2 Q2.hfix120_19_2 Q2.hinj120_19_2
      Q2.hcardT120_19_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_19_2 i) (Q2.hfix120_19_2 i) _)
      colCert_120_19_15.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_19_20 (hp : 20 < (Q2.transData.getD 19 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨19, by decide⟩ : Fin 148)) (colE2 ⟨19, by decide⟩ 20 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨19, by decide⟩ : Fin 148))
        (colE1 ⟨19, by decide⟩ 20 (transLenTr ⟨19, by decide⟩ 20 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨19, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨19, by decide⟩ 20 (transLenTr ⟨19, by decide⟩ 20 hp)) T120_19
      hfix120_19 hinj120_19 hcardT120_19
      (fun i => conj_mem_of_fixedPoints _ _ (T120_19 i) (hfix120_19 i) _)
      ⟨120, by decide⟩ ⟨19, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨19, by decide⟩ 20 hp) Q2.T120_19_2 Q2.hfix120_19_2 Q2.hinj120_19_2
      Q2.hcardT120_19_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_19_2 i) (Q2.hfix120_19_2 i) _)
      colCert_120_19_20.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_24_0 (hp : 0 < (Q2.transData.getD 24 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨24, by decide⟩ : Fin 148)) (colE2 ⟨24, by decide⟩ 0 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨24, by decide⟩ : Fin 148))
        (colE1 ⟨24, by decide⟩ 0 (transLenTr ⟨24, by decide⟩ 0 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨24, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨24, by decide⟩ 0 (transLenTr ⟨24, by decide⟩ 0 hp)) T120_24
      hfix120_24 hinj120_24 hcardT120_24
      (fun i => conj_mem_of_fixedPoints _ _ (T120_24 i) (hfix120_24 i) _)
      ⟨120, by decide⟩ ⟨24, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨24, by decide⟩ 0 hp) Q2.T120_24_2 Q2.hfix120_24_2 Q2.hinj120_24_2
      Q2.hcardT120_24_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_24_2 i) (Q2.hfix120_24_2 i) _)
      colCert_120_24_0.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_24_1 (hp : 1 < (Q2.transData.getD 24 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨24, by decide⟩ : Fin 148)) (colE2 ⟨24, by decide⟩ 1 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨24, by decide⟩ : Fin 148))
        (colE1 ⟨24, by decide⟩ 1 (transLenTr ⟨24, by decide⟩ 1 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨24, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨24, by decide⟩ 1 (transLenTr ⟨24, by decide⟩ 1 hp)) T120_24
      hfix120_24 hinj120_24 hcardT120_24
      (fun i => conj_mem_of_fixedPoints _ _ (T120_24 i) (hfix120_24 i) _)
      ⟨120, by decide⟩ ⟨24, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨24, by decide⟩ 1 hp) Q2.T120_24_2 Q2.hfix120_24_2 Q2.hinj120_24_2
      Q2.hcardT120_24_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_24_2 i) (Q2.hfix120_24_2 i) _)
      colCert_120_24_1.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_24_2 (hp : 2 < (Q2.transData.getD 24 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨24, by decide⟩ : Fin 148)) (colE2 ⟨24, by decide⟩ 2 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨24, by decide⟩ : Fin 148))
        (colE1 ⟨24, by decide⟩ 2 (transLenTr ⟨24, by decide⟩ 2 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨24, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨24, by decide⟩ 2 (transLenTr ⟨24, by decide⟩ 2 hp)) T120_24
      hfix120_24 hinj120_24 hcardT120_24
      (fun i => conj_mem_of_fixedPoints _ _ (T120_24 i) (hfix120_24 i) _)
      ⟨120, by decide⟩ ⟨24, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨24, by decide⟩ 2 hp) Q2.T120_24_2 Q2.hfix120_24_2 Q2.hinj120_24_2
      Q2.hcardT120_24_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_24_2 i) (Q2.hfix120_24_2 i) _)
      colCert_120_24_2.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_24_3 (hp : 3 < (Q2.transData.getD 24 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨24, by decide⟩ : Fin 148)) (colE2 ⟨24, by decide⟩ 3 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨24, by decide⟩ : Fin 148))
        (colE1 ⟨24, by decide⟩ 3 (transLenTr ⟨24, by decide⟩ 3 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨24, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨24, by decide⟩ 3 (transLenTr ⟨24, by decide⟩ 3 hp)) T120_24
      hfix120_24 hinj120_24 hcardT120_24
      (fun i => conj_mem_of_fixedPoints _ _ (T120_24 i) (hfix120_24 i) _)
      ⟨120, by decide⟩ ⟨24, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨24, by decide⟩ 3 hp) Q2.T120_24_2 Q2.hfix120_24_2 Q2.hinj120_24_2
      Q2.hcardT120_24_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_24_2 i) (Q2.hfix120_24_2 i) _)
      colCert_120_24_3.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_24_4 (hp : 4 < (Q2.transData.getD 24 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨24, by decide⟩ : Fin 148)) (colE2 ⟨24, by decide⟩ 4 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨24, by decide⟩ : Fin 148))
        (colE1 ⟨24, by decide⟩ 4 (transLenTr ⟨24, by decide⟩ 4 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨24, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨24, by decide⟩ 4 (transLenTr ⟨24, by decide⟩ 4 hp)) T120_24
      hfix120_24 hinj120_24 hcardT120_24
      (fun i => conj_mem_of_fixedPoints _ _ (T120_24 i) (hfix120_24 i) _)
      ⟨120, by decide⟩ ⟨24, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨24, by decide⟩ 4 hp) Q2.T120_24_2 Q2.hfix120_24_2 Q2.hinj120_24_2
      Q2.hcardT120_24_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_24_2 i) (Q2.hfix120_24_2 i) _)
      colCert_120_24_4.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_24_5 (hp : 5 < (Q2.transData.getD 24 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨24, by decide⟩ : Fin 148)) (colE2 ⟨24, by decide⟩ 5 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨24, by decide⟩ : Fin 148))
        (colE1 ⟨24, by decide⟩ 5 (transLenTr ⟨24, by decide⟩ 5 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨24, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨24, by decide⟩ 5 (transLenTr ⟨24, by decide⟩ 5 hp)) T120_24
      hfix120_24 hinj120_24 hcardT120_24
      (fun i => conj_mem_of_fixedPoints _ _ (T120_24 i) (hfix120_24 i) _)
      ⟨120, by decide⟩ ⟨24, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨24, by decide⟩ 5 hp) Q2.T120_24_2 Q2.hfix120_24_2 Q2.hinj120_24_2
      Q2.hcardT120_24_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_24_2 i) (Q2.hfix120_24_2 i) _)
      colCert_120_24_5.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_24_10 (hp : 10 < (Q2.transData.getD 24 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨24, by decide⟩ : Fin 148)) (colE2 ⟨24, by decide⟩ 10 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨24, by decide⟩ : Fin 148))
        (colE1 ⟨24, by decide⟩ 10 (transLenTr ⟨24, by decide⟩ 10 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨24, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨24, by decide⟩ 10 (transLenTr ⟨24, by decide⟩ 10 hp)) T120_24
      hfix120_24 hinj120_24 hcardT120_24
      (fun i => conj_mem_of_fixedPoints _ _ (T120_24 i) (hfix120_24 i) _)
      ⟨120, by decide⟩ ⟨24, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨24, by decide⟩ 10 hp) Q2.T120_24_2 Q2.hfix120_24_2 Q2.hinj120_24_2
      Q2.hcardT120_24_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_24_2 i) (Q2.hfix120_24_2 i) _)
      colCert_120_24_10.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_24_15 (hp : 15 < (Q2.transData.getD 24 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨24, by decide⟩ : Fin 148)) (colE2 ⟨24, by decide⟩ 15 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨24, by decide⟩ : Fin 148))
        (colE1 ⟨24, by decide⟩ 15 (transLenTr ⟨24, by decide⟩ 15 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨24, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨24, by decide⟩ 15 (transLenTr ⟨24, by decide⟩ 15 hp)) T120_24
      hfix120_24 hinj120_24 hcardT120_24
      (fun i => conj_mem_of_fixedPoints _ _ (T120_24 i) (hfix120_24 i) _)
      ⟨120, by decide⟩ ⟨24, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨24, by decide⟩ 15 hp) Q2.T120_24_2 Q2.hfix120_24_2 Q2.hinj120_24_2
      Q2.hcardT120_24_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_24_2 i) (Q2.hfix120_24_2 i) _)
      colCert_120_24_15.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_24_20 (hp : 20 < (Q2.transData.getD 24 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨24, by decide⟩ : Fin 148)) (colE2 ⟨24, by decide⟩ 20 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨24, by decide⟩ : Fin 148))
        (colE1 ⟨24, by decide⟩ 20 (transLenTr ⟨24, by decide⟩ 20 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨24, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨24, by decide⟩ 20 (transLenTr ⟨24, by decide⟩ 20 hp)) T120_24
      hfix120_24 hinj120_24 hcardT120_24
      (fun i => conj_mem_of_fixedPoints _ _ (T120_24 i) (hfix120_24 i) _)
      ⟨120, by decide⟩ ⟨24, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨24, by decide⟩ 20 hp) Q2.T120_24_2 Q2.hfix120_24_2 Q2.hinj120_24_2
      Q2.hcardT120_24_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_24_2 i) (Q2.hfix120_24_2 i) _)
      colCert_120_24_20.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_25_0 (hp : 0 < (Q2.transData.getD 25 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨25, by decide⟩ : Fin 148)) (colE2 ⟨25, by decide⟩ 0 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨25, by decide⟩ : Fin 148))
        (colE1 ⟨25, by decide⟩ 0 (transLenTr ⟨25, by decide⟩ 0 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨25, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨25, by decide⟩ 0 (transLenTr ⟨25, by decide⟩ 0 hp)) T120_25
      hfix120_25 hinj120_25 hcardT120_25
      (fun i => conj_mem_of_fixedPoints _ _ (T120_25 i) (hfix120_25 i) _)
      ⟨120, by decide⟩ ⟨25, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨25, by decide⟩ 0 hp) Q2.T120_25_2 Q2.hfix120_25_2 Q2.hinj120_25_2
      Q2.hcardT120_25_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_25_2 i) (Q2.hfix120_25_2 i) _)
      colCert_120_25_0.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_25_1 (hp : 1 < (Q2.transData.getD 25 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨25, by decide⟩ : Fin 148)) (colE2 ⟨25, by decide⟩ 1 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨25, by decide⟩ : Fin 148))
        (colE1 ⟨25, by decide⟩ 1 (transLenTr ⟨25, by decide⟩ 1 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨25, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨25, by decide⟩ 1 (transLenTr ⟨25, by decide⟩ 1 hp)) T120_25
      hfix120_25 hinj120_25 hcardT120_25
      (fun i => conj_mem_of_fixedPoints _ _ (T120_25 i) (hfix120_25 i) _)
      ⟨120, by decide⟩ ⟨25, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨25, by decide⟩ 1 hp) Q2.T120_25_2 Q2.hfix120_25_2 Q2.hinj120_25_2
      Q2.hcardT120_25_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_25_2 i) (Q2.hfix120_25_2 i) _)
      colCert_120_25_1.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_25_2 (hp : 2 < (Q2.transData.getD 25 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨25, by decide⟩ : Fin 148)) (colE2 ⟨25, by decide⟩ 2 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨25, by decide⟩ : Fin 148))
        (colE1 ⟨25, by decide⟩ 2 (transLenTr ⟨25, by decide⟩ 2 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨25, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨25, by decide⟩ 2 (transLenTr ⟨25, by decide⟩ 2 hp)) T120_25
      hfix120_25 hinj120_25 hcardT120_25
      (fun i => conj_mem_of_fixedPoints _ _ (T120_25 i) (hfix120_25 i) _)
      ⟨120, by decide⟩ ⟨25, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨25, by decide⟩ 2 hp) Q2.T120_25_2 Q2.hfix120_25_2 Q2.hinj120_25_2
      Q2.hcardT120_25_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_25_2 i) (Q2.hfix120_25_2 i) _)
      colCert_120_25_2.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_25_3 (hp : 3 < (Q2.transData.getD 25 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨25, by decide⟩ : Fin 148)) (colE2 ⟨25, by decide⟩ 3 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨25, by decide⟩ : Fin 148))
        (colE1 ⟨25, by decide⟩ 3 (transLenTr ⟨25, by decide⟩ 3 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨25, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨25, by decide⟩ 3 (transLenTr ⟨25, by decide⟩ 3 hp)) T120_25
      hfix120_25 hinj120_25 hcardT120_25
      (fun i => conj_mem_of_fixedPoints _ _ (T120_25 i) (hfix120_25 i) _)
      ⟨120, by decide⟩ ⟨25, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨25, by decide⟩ 3 hp) Q2.T120_25_2 Q2.hfix120_25_2 Q2.hinj120_25_2
      Q2.hcardT120_25_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_25_2 i) (Q2.hfix120_25_2 i) _)
      colCert_120_25_3.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_25_4 (hp : 4 < (Q2.transData.getD 25 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨25, by decide⟩ : Fin 148)) (colE2 ⟨25, by decide⟩ 4 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨25, by decide⟩ : Fin 148))
        (colE1 ⟨25, by decide⟩ 4 (transLenTr ⟨25, by decide⟩ 4 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨25, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨25, by decide⟩ 4 (transLenTr ⟨25, by decide⟩ 4 hp)) T120_25
      hfix120_25 hinj120_25 hcardT120_25
      (fun i => conj_mem_of_fixedPoints _ _ (T120_25 i) (hfix120_25 i) _)
      ⟨120, by decide⟩ ⟨25, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨25, by decide⟩ 4 hp) Q2.T120_25_2 Q2.hfix120_25_2 Q2.hinj120_25_2
      Q2.hcardT120_25_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_25_2 i) (Q2.hfix120_25_2 i) _)
      colCert_120_25_4.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_25_5 (hp : 5 < (Q2.transData.getD 25 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨25, by decide⟩ : Fin 148)) (colE2 ⟨25, by decide⟩ 5 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨25, by decide⟩ : Fin 148))
        (colE1 ⟨25, by decide⟩ 5 (transLenTr ⟨25, by decide⟩ 5 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨25, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨25, by decide⟩ 5 (transLenTr ⟨25, by decide⟩ 5 hp)) T120_25
      hfix120_25 hinj120_25 hcardT120_25
      (fun i => conj_mem_of_fixedPoints _ _ (T120_25 i) (hfix120_25 i) _)
      ⟨120, by decide⟩ ⟨25, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨25, by decide⟩ 5 hp) Q2.T120_25_2 Q2.hfix120_25_2 Q2.hinj120_25_2
      Q2.hcardT120_25_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_25_2 i) (Q2.hfix120_25_2 i) _)
      colCert_120_25_5.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_25_10 (hp : 10 < (Q2.transData.getD 25 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨25, by decide⟩ : Fin 148)) (colE2 ⟨25, by decide⟩ 10 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨25, by decide⟩ : Fin 148))
        (colE1 ⟨25, by decide⟩ 10 (transLenTr ⟨25, by decide⟩ 10 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨25, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨25, by decide⟩ 10 (transLenTr ⟨25, by decide⟩ 10 hp)) T120_25
      hfix120_25 hinj120_25 hcardT120_25
      (fun i => conj_mem_of_fixedPoints _ _ (T120_25 i) (hfix120_25 i) _)
      ⟨120, by decide⟩ ⟨25, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨25, by decide⟩ 10 hp) Q2.T120_25_2 Q2.hfix120_25_2 Q2.hinj120_25_2
      Q2.hcardT120_25_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_25_2 i) (Q2.hfix120_25_2 i) _)
      colCert_120_25_10.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_25_15 (hp : 15 < (Q2.transData.getD 25 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨25, by decide⟩ : Fin 148)) (colE2 ⟨25, by decide⟩ 15 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨25, by decide⟩ : Fin 148))
        (colE1 ⟨25, by decide⟩ 15 (transLenTr ⟨25, by decide⟩ 15 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨25, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨25, by decide⟩ 15 (transLenTr ⟨25, by decide⟩ 15 hp)) T120_25
      hfix120_25 hinj120_25 hcardT120_25
      (fun i => conj_mem_of_fixedPoints _ _ (T120_25 i) (hfix120_25 i) _)
      ⟨120, by decide⟩ ⟨25, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨25, by decide⟩ 15 hp) Q2.T120_25_2 Q2.hfix120_25_2 Q2.hinj120_25_2
      Q2.hcardT120_25_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_25_2 i) (Q2.hfix120_25_2 i) _)
      colCert_120_25_15.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_25_20 (hp : 20 < (Q2.transData.getD 25 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨25, by decide⟩ : Fin 148)) (colE2 ⟨25, by decide⟩ 20 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨25, by decide⟩ : Fin 148))
        (colE1 ⟨25, by decide⟩ 20 (transLenTr ⟨25, by decide⟩ 20 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨25, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨25, by decide⟩ 20 (transLenTr ⟨25, by decide⟩ 20 hp)) T120_25
      hfix120_25 hinj120_25 hcardT120_25
      (fun i => conj_mem_of_fixedPoints _ _ (T120_25 i) (hfix120_25 i) _)
      ⟨120, by decide⟩ ⟨25, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨25, by decide⟩ 20 hp) Q2.T120_25_2 Q2.hfix120_25_2 Q2.hinj120_25_2
      Q2.hcardT120_25_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_25_2 i) (Q2.hfix120_25_2 i) _)
      colCert_120_25_20.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_26_0 (hp : 0 < (Q2.transData.getD 26 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨26, by decide⟩ : Fin 148)) (colE2 ⟨26, by decide⟩ 0 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨26, by decide⟩ : Fin 148))
        (colE1 ⟨26, by decide⟩ 0 (transLenTr ⟨26, by decide⟩ 0 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨26, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨26, by decide⟩ 0 (transLenTr ⟨26, by decide⟩ 0 hp)) T120_26
      hfix120_26 hinj120_26 hcardT120_26
      (fun i => conj_mem_of_fixedPoints _ _ (T120_26 i) (hfix120_26 i) _)
      ⟨120, by decide⟩ ⟨26, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨26, by decide⟩ 0 hp) Q2.T120_26_2 Q2.hfix120_26_2 Q2.hinj120_26_2
      Q2.hcardT120_26_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_26_2 i) (Q2.hfix120_26_2 i) _)
      colCert_120_26_0.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_26_1 (hp : 1 < (Q2.transData.getD 26 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨26, by decide⟩ : Fin 148)) (colE2 ⟨26, by decide⟩ 1 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨26, by decide⟩ : Fin 148))
        (colE1 ⟨26, by decide⟩ 1 (transLenTr ⟨26, by decide⟩ 1 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨26, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨26, by decide⟩ 1 (transLenTr ⟨26, by decide⟩ 1 hp)) T120_26
      hfix120_26 hinj120_26 hcardT120_26
      (fun i => conj_mem_of_fixedPoints _ _ (T120_26 i) (hfix120_26 i) _)
      ⟨120, by decide⟩ ⟨26, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨26, by decide⟩ 1 hp) Q2.T120_26_2 Q2.hfix120_26_2 Q2.hinj120_26_2
      Q2.hcardT120_26_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_26_2 i) (Q2.hfix120_26_2 i) _)
      colCert_120_26_1.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_26_2 (hp : 2 < (Q2.transData.getD 26 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨26, by decide⟩ : Fin 148)) (colE2 ⟨26, by decide⟩ 2 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨26, by decide⟩ : Fin 148))
        (colE1 ⟨26, by decide⟩ 2 (transLenTr ⟨26, by decide⟩ 2 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨26, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨26, by decide⟩ 2 (transLenTr ⟨26, by decide⟩ 2 hp)) T120_26
      hfix120_26 hinj120_26 hcardT120_26
      (fun i => conj_mem_of_fixedPoints _ _ (T120_26 i) (hfix120_26 i) _)
      ⟨120, by decide⟩ ⟨26, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨26, by decide⟩ 2 hp) Q2.T120_26_2 Q2.hfix120_26_2 Q2.hinj120_26_2
      Q2.hcardT120_26_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_26_2 i) (Q2.hfix120_26_2 i) _)
      colCert_120_26_2.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_26_3 (hp : 3 < (Q2.transData.getD 26 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨26, by decide⟩ : Fin 148)) (colE2 ⟨26, by decide⟩ 3 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨26, by decide⟩ : Fin 148))
        (colE1 ⟨26, by decide⟩ 3 (transLenTr ⟨26, by decide⟩ 3 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨26, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨26, by decide⟩ 3 (transLenTr ⟨26, by decide⟩ 3 hp)) T120_26
      hfix120_26 hinj120_26 hcardT120_26
      (fun i => conj_mem_of_fixedPoints _ _ (T120_26 i) (hfix120_26 i) _)
      ⟨120, by decide⟩ ⟨26, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨26, by decide⟩ 3 hp) Q2.T120_26_2 Q2.hfix120_26_2 Q2.hinj120_26_2
      Q2.hcardT120_26_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_26_2 i) (Q2.hfix120_26_2 i) _)
      colCert_120_26_3.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_26_4 (hp : 4 < (Q2.transData.getD 26 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨26, by decide⟩ : Fin 148)) (colE2 ⟨26, by decide⟩ 4 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨26, by decide⟩ : Fin 148))
        (colE1 ⟨26, by decide⟩ 4 (transLenTr ⟨26, by decide⟩ 4 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨26, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨26, by decide⟩ 4 (transLenTr ⟨26, by decide⟩ 4 hp)) T120_26
      hfix120_26 hinj120_26 hcardT120_26
      (fun i => conj_mem_of_fixedPoints _ _ (T120_26 i) (hfix120_26 i) _)
      ⟨120, by decide⟩ ⟨26, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨26, by decide⟩ 4 hp) Q2.T120_26_2 Q2.hfix120_26_2 Q2.hinj120_26_2
      Q2.hcardT120_26_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_26_2 i) (Q2.hfix120_26_2 i) _)
      colCert_120_26_4.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_26_5 (hp : 5 < (Q2.transData.getD 26 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨26, by decide⟩ : Fin 148)) (colE2 ⟨26, by decide⟩ 5 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨26, by decide⟩ : Fin 148))
        (colE1 ⟨26, by decide⟩ 5 (transLenTr ⟨26, by decide⟩ 5 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨26, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨26, by decide⟩ 5 (transLenTr ⟨26, by decide⟩ 5 hp)) T120_26
      hfix120_26 hinj120_26 hcardT120_26
      (fun i => conj_mem_of_fixedPoints _ _ (T120_26 i) (hfix120_26 i) _)
      ⟨120, by decide⟩ ⟨26, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨26, by decide⟩ 5 hp) Q2.T120_26_2 Q2.hfix120_26_2 Q2.hinj120_26_2
      Q2.hcardT120_26_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_26_2 i) (Q2.hfix120_26_2 i) _)
      colCert_120_26_5.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_26_10 (hp : 10 < (Q2.transData.getD 26 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨26, by decide⟩ : Fin 148)) (colE2 ⟨26, by decide⟩ 10 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨26, by decide⟩ : Fin 148))
        (colE1 ⟨26, by decide⟩ 10 (transLenTr ⟨26, by decide⟩ 10 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨26, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨26, by decide⟩ 10 (transLenTr ⟨26, by decide⟩ 10 hp)) T120_26
      hfix120_26 hinj120_26 hcardT120_26
      (fun i => conj_mem_of_fixedPoints _ _ (T120_26 i) (hfix120_26 i) _)
      ⟨120, by decide⟩ ⟨26, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨26, by decide⟩ 10 hp) Q2.T120_26_2 Q2.hfix120_26_2 Q2.hinj120_26_2
      Q2.hcardT120_26_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_26_2 i) (Q2.hfix120_26_2 i) _)
      colCert_120_26_10.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_26_15 (hp : 15 < (Q2.transData.getD 26 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨26, by decide⟩ : Fin 148)) (colE2 ⟨26, by decide⟩ 15 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨26, by decide⟩ : Fin 148))
        (colE1 ⟨26, by decide⟩ 15 (transLenTr ⟨26, by decide⟩ 15 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨26, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨26, by decide⟩ 15 (transLenTr ⟨26, by decide⟩ 15 hp)) T120_26
      hfix120_26 hinj120_26 hcardT120_26
      (fun i => conj_mem_of_fixedPoints _ _ (T120_26 i) (hfix120_26 i) _)
      ⟨120, by decide⟩ ⟨26, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨26, by decide⟩ 15 hp) Q2.T120_26_2 Q2.hfix120_26_2 Q2.hinj120_26_2
      Q2.hcardT120_26_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_26_2 i) (Q2.hfix120_26_2 i) _)
      colCert_120_26_15.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_26_20 (hp : 20 < (Q2.transData.getD 26 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨26, by decide⟩ : Fin 148)) (colE2 ⟨26, by decide⟩ 20 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨26, by decide⟩ : Fin 148))
        (colE1 ⟨26, by decide⟩ 20 (transLenTr ⟨26, by decide⟩ 20 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨26, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨26, by decide⟩ 20 (transLenTr ⟨26, by decide⟩ 20 hp)) T120_26
      hfix120_26 hinj120_26 hcardT120_26
      (fun i => conj_mem_of_fixedPoints _ _ (T120_26 i) (hfix120_26 i) _)
      ⟨120, by decide⟩ ⟨26, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨26, by decide⟩ 20 hp) Q2.T120_26_2 Q2.hfix120_26_2 Q2.hinj120_26_2
      Q2.hcardT120_26_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_26_2 i) (Q2.hfix120_26_2 i) _)
      colCert_120_26_20.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_27_0 (hp : 0 < (Q2.transData.getD 27 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨27, by decide⟩ : Fin 148)) (colE2 ⟨27, by decide⟩ 0 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨27, by decide⟩ : Fin 148))
        (colE1 ⟨27, by decide⟩ 0 (transLenTr ⟨27, by decide⟩ 0 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨27, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨27, by decide⟩ 0 (transLenTr ⟨27, by decide⟩ 0 hp)) T120_27
      hfix120_27 hinj120_27 hcardT120_27
      (fun i => conj_mem_of_fixedPoints _ _ (T120_27 i) (hfix120_27 i) _)
      ⟨120, by decide⟩ ⟨27, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨27, by decide⟩ 0 hp) Q2.T120_27_2 Q2.hfix120_27_2 Q2.hinj120_27_2
      Q2.hcardT120_27_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_27_2 i) (Q2.hfix120_27_2 i) _)
      colCert_120_27_0.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_27_1 (hp : 1 < (Q2.transData.getD 27 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨27, by decide⟩ : Fin 148)) (colE2 ⟨27, by decide⟩ 1 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨27, by decide⟩ : Fin 148))
        (colE1 ⟨27, by decide⟩ 1 (transLenTr ⟨27, by decide⟩ 1 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨27, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨27, by decide⟩ 1 (transLenTr ⟨27, by decide⟩ 1 hp)) T120_27
      hfix120_27 hinj120_27 hcardT120_27
      (fun i => conj_mem_of_fixedPoints _ _ (T120_27 i) (hfix120_27 i) _)
      ⟨120, by decide⟩ ⟨27, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨27, by decide⟩ 1 hp) Q2.T120_27_2 Q2.hfix120_27_2 Q2.hinj120_27_2
      Q2.hcardT120_27_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_27_2 i) (Q2.hfix120_27_2 i) _)
      colCert_120_27_1.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_27_2 (hp : 2 < (Q2.transData.getD 27 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨27, by decide⟩ : Fin 148)) (colE2 ⟨27, by decide⟩ 2 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨27, by decide⟩ : Fin 148))
        (colE1 ⟨27, by decide⟩ 2 (transLenTr ⟨27, by decide⟩ 2 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨27, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨27, by decide⟩ 2 (transLenTr ⟨27, by decide⟩ 2 hp)) T120_27
      hfix120_27 hinj120_27 hcardT120_27
      (fun i => conj_mem_of_fixedPoints _ _ (T120_27 i) (hfix120_27 i) _)
      ⟨120, by decide⟩ ⟨27, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨27, by decide⟩ 2 hp) Q2.T120_27_2 Q2.hfix120_27_2 Q2.hinj120_27_2
      Q2.hcardT120_27_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_27_2 i) (Q2.hfix120_27_2 i) _)
      colCert_120_27_2.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_27_3 (hp : 3 < (Q2.transData.getD 27 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨27, by decide⟩ : Fin 148)) (colE2 ⟨27, by decide⟩ 3 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨27, by decide⟩ : Fin 148))
        (colE1 ⟨27, by decide⟩ 3 (transLenTr ⟨27, by decide⟩ 3 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨27, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨27, by decide⟩ 3 (transLenTr ⟨27, by decide⟩ 3 hp)) T120_27
      hfix120_27 hinj120_27 hcardT120_27
      (fun i => conj_mem_of_fixedPoints _ _ (T120_27 i) (hfix120_27 i) _)
      ⟨120, by decide⟩ ⟨27, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨27, by decide⟩ 3 hp) Q2.T120_27_2 Q2.hfix120_27_2 Q2.hinj120_27_2
      Q2.hcardT120_27_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_27_2 i) (Q2.hfix120_27_2 i) _)
      colCert_120_27_3.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_27_4 (hp : 4 < (Q2.transData.getD 27 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨27, by decide⟩ : Fin 148)) (colE2 ⟨27, by decide⟩ 4 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨27, by decide⟩ : Fin 148))
        (colE1 ⟨27, by decide⟩ 4 (transLenTr ⟨27, by decide⟩ 4 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨27, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨27, by decide⟩ 4 (transLenTr ⟨27, by decide⟩ 4 hp)) T120_27
      hfix120_27 hinj120_27 hcardT120_27
      (fun i => conj_mem_of_fixedPoints _ _ (T120_27 i) (hfix120_27 i) _)
      ⟨120, by decide⟩ ⟨27, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨27, by decide⟩ 4 hp) Q2.T120_27_2 Q2.hfix120_27_2 Q2.hinj120_27_2
      Q2.hcardT120_27_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_27_2 i) (Q2.hfix120_27_2 i) _)
      colCert_120_27_4.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_27_5 (hp : 5 < (Q2.transData.getD 27 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨27, by decide⟩ : Fin 148)) (colE2 ⟨27, by decide⟩ 5 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨27, by decide⟩ : Fin 148))
        (colE1 ⟨27, by decide⟩ 5 (transLenTr ⟨27, by decide⟩ 5 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨27, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨27, by decide⟩ 5 (transLenTr ⟨27, by decide⟩ 5 hp)) T120_27
      hfix120_27 hinj120_27 hcardT120_27
      (fun i => conj_mem_of_fixedPoints _ _ (T120_27 i) (hfix120_27 i) _)
      ⟨120, by decide⟩ ⟨27, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨27, by decide⟩ 5 hp) Q2.T120_27_2 Q2.hfix120_27_2 Q2.hinj120_27_2
      Q2.hcardT120_27_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_27_2 i) (Q2.hfix120_27_2 i) _)
      colCert_120_27_5.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_27_10 (hp : 10 < (Q2.transData.getD 27 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨27, by decide⟩ : Fin 148)) (colE2 ⟨27, by decide⟩ 10 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨27, by decide⟩ : Fin 148))
        (colE1 ⟨27, by decide⟩ 10 (transLenTr ⟨27, by decide⟩ 10 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨27, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨27, by decide⟩ 10 (transLenTr ⟨27, by decide⟩ 10 hp)) T120_27
      hfix120_27 hinj120_27 hcardT120_27
      (fun i => conj_mem_of_fixedPoints _ _ (T120_27 i) (hfix120_27 i) _)
      ⟨120, by decide⟩ ⟨27, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨27, by decide⟩ 10 hp) Q2.T120_27_2 Q2.hfix120_27_2 Q2.hinj120_27_2
      Q2.hcardT120_27_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_27_2 i) (Q2.hfix120_27_2 i) _)
      colCert_120_27_10.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_27_15 (hp : 15 < (Q2.transData.getD 27 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨27, by decide⟩ : Fin 148)) (colE2 ⟨27, by decide⟩ 15 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨27, by decide⟩ : Fin 148))
        (colE1 ⟨27, by decide⟩ 15 (transLenTr ⟨27, by decide⟩ 15 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨27, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨27, by decide⟩ 15 (transLenTr ⟨27, by decide⟩ 15 hp)) T120_27
      hfix120_27 hinj120_27 hcardT120_27
      (fun i => conj_mem_of_fixedPoints _ _ (T120_27 i) (hfix120_27 i) _)
      ⟨120, by decide⟩ ⟨27, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨27, by decide⟩ 15 hp) Q2.T120_27_2 Q2.hfix120_27_2 Q2.hinj120_27_2
      Q2.hcardT120_27_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_27_2 i) (Q2.hfix120_27_2 i) _)
      colCert_120_27_15.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_27_20 (hp : 20 < (Q2.transData.getD 27 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨27, by decide⟩ : Fin 148)) (colE2 ⟨27, by decide⟩ 20 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨27, by decide⟩ : Fin 148))
        (colE1 ⟨27, by decide⟩ 20 (transLenTr ⟨27, by decide⟩ 20 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨27, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨27, by decide⟩ 20 (transLenTr ⟨27, by decide⟩ 20 hp)) T120_27
      hfix120_27 hinj120_27 hcardT120_27
      (fun i => conj_mem_of_fixedPoints _ _ (T120_27 i) (hfix120_27 i) _)
      ⟨120, by decide⟩ ⟨27, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨27, by decide⟩ 20 hp) Q2.T120_27_2 Q2.hfix120_27_2 Q2.hinj120_27_2
      Q2.hcardT120_27_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_27_2 i) (Q2.hfix120_27_2 i) _)
      colCert_120_27_20.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_32_0 (hp : 0 < (Q2.transData.getD 32 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨32, by decide⟩ : Fin 148)) (colE2 ⟨32, by decide⟩ 0 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨32, by decide⟩ : Fin 148))
        (colE1 ⟨32, by decide⟩ 0 (transLenTr ⟨32, by decide⟩ 0 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨32, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨32, by decide⟩ 0 (transLenTr ⟨32, by decide⟩ 0 hp)) T120_32
      hfix120_32 hinj120_32 hcardT120_32
      (fun i => conj_mem_of_fixedPoints _ _ (T120_32 i) (hfix120_32 i) _)
      ⟨120, by decide⟩ ⟨32, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨32, by decide⟩ 0 hp) Q2.T120_32_2 Q2.hfix120_32_2 Q2.hinj120_32_2
      Q2.hcardT120_32_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_32_2 i) (Q2.hfix120_32_2 i) _)
      colCert_120_32_0.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_32_1 (hp : 1 < (Q2.transData.getD 32 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨32, by decide⟩ : Fin 148)) (colE2 ⟨32, by decide⟩ 1 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨32, by decide⟩ : Fin 148))
        (colE1 ⟨32, by decide⟩ 1 (transLenTr ⟨32, by decide⟩ 1 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨32, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨32, by decide⟩ 1 (transLenTr ⟨32, by decide⟩ 1 hp)) T120_32
      hfix120_32 hinj120_32 hcardT120_32
      (fun i => conj_mem_of_fixedPoints _ _ (T120_32 i) (hfix120_32 i) _)
      ⟨120, by decide⟩ ⟨32, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨32, by decide⟩ 1 hp) Q2.T120_32_2 Q2.hfix120_32_2 Q2.hinj120_32_2
      Q2.hcardT120_32_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_32_2 i) (Q2.hfix120_32_2 i) _)
      colCert_120_32_1.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_32_2 (hp : 2 < (Q2.transData.getD 32 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨32, by decide⟩ : Fin 148)) (colE2 ⟨32, by decide⟩ 2 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨32, by decide⟩ : Fin 148))
        (colE1 ⟨32, by decide⟩ 2 (transLenTr ⟨32, by decide⟩ 2 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨32, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨32, by decide⟩ 2 (transLenTr ⟨32, by decide⟩ 2 hp)) T120_32
      hfix120_32 hinj120_32 hcardT120_32
      (fun i => conj_mem_of_fixedPoints _ _ (T120_32 i) (hfix120_32 i) _)
      ⟨120, by decide⟩ ⟨32, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨32, by decide⟩ 2 hp) Q2.T120_32_2 Q2.hfix120_32_2 Q2.hinj120_32_2
      Q2.hcardT120_32_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_32_2 i) (Q2.hfix120_32_2 i) _)
      colCert_120_32_2.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_32_3 (hp : 3 < (Q2.transData.getD 32 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨32, by decide⟩ : Fin 148)) (colE2 ⟨32, by decide⟩ 3 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨32, by decide⟩ : Fin 148))
        (colE1 ⟨32, by decide⟩ 3 (transLenTr ⟨32, by decide⟩ 3 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨32, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨32, by decide⟩ 3 (transLenTr ⟨32, by decide⟩ 3 hp)) T120_32
      hfix120_32 hinj120_32 hcardT120_32
      (fun i => conj_mem_of_fixedPoints _ _ (T120_32 i) (hfix120_32 i) _)
      ⟨120, by decide⟩ ⟨32, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨32, by decide⟩ 3 hp) Q2.T120_32_2 Q2.hfix120_32_2 Q2.hinj120_32_2
      Q2.hcardT120_32_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_32_2 i) (Q2.hfix120_32_2 i) _)
      colCert_120_32_3.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_32_4 (hp : 4 < (Q2.transData.getD 32 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨32, by decide⟩ : Fin 148)) (colE2 ⟨32, by decide⟩ 4 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨32, by decide⟩ : Fin 148))
        (colE1 ⟨32, by decide⟩ 4 (transLenTr ⟨32, by decide⟩ 4 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨32, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨32, by decide⟩ 4 (transLenTr ⟨32, by decide⟩ 4 hp)) T120_32
      hfix120_32 hinj120_32 hcardT120_32
      (fun i => conj_mem_of_fixedPoints _ _ (T120_32 i) (hfix120_32 i) _)
      ⟨120, by decide⟩ ⟨32, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨32, by decide⟩ 4 hp) Q2.T120_32_2 Q2.hfix120_32_2 Q2.hinj120_32_2
      Q2.hcardT120_32_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_32_2 i) (Q2.hfix120_32_2 i) _)
      colCert_120_32_4.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_32_5 (hp : 5 < (Q2.transData.getD 32 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨32, by decide⟩ : Fin 148)) (colE2 ⟨32, by decide⟩ 5 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨32, by decide⟩ : Fin 148))
        (colE1 ⟨32, by decide⟩ 5 (transLenTr ⟨32, by decide⟩ 5 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨120, by decide⟩ : Fin 148) ⟨32, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨32, by decide⟩ 5 (transLenTr ⟨32, by decide⟩ 5 hp)) T120_32
      hfix120_32 hinj120_32 hcardT120_32
      (fun i => conj_mem_of_fixedPoints _ _ (T120_32 i) (hfix120_32 i) _)
      ⟨120, by decide⟩ ⟨32, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨32, by decide⟩ 5 hp) Q2.T120_32_2 Q2.hfix120_32_2 Q2.hinj120_32_2
      Q2.hcardT120_32_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_32_2 i) (Q2.hfix120_32_2 i) _)
      ?_).symm
  rw [show colData1 (⟨120, by decide⟩ : Fin 148)
        ((colE1 ⟨32, by decide⟩ 5 (transLenTr ⟨32, by decide⟩ 5 hp) : ↥(reps ⟨32, by decide⟩)) : Coordinate 1)
        T120_32 = colFn colCertDiv_120_32_5.D1 (m := 5) from colCertDiv_120_32_5.bind1,
    show colData2 (⟨120, by decide⟩ : Fin 148)
        ((colE2 ⟨32, by decide⟩ 5 hp : ↥(Q2.reps ⟨32, by decide⟩)) : Coordinate 2)
        Q2.T120_32_2 = colFn colCertDiv_120_32_5.D2 (m := 5) from colCertDiv_120_32_5.bind2]
  rw [alnId_120 j hj]
  exact fastcode_of_div ⟨120, by decide⟩ _ _ _
    ((alnId_120 j hj) ▸ Q2.listedAt (⟨120, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨120, by decide⟩ : Fin 148) hj hq).1) colCertDiv_120_32_5_match


theorem leaf_120_32_10 (hp : 10 < (Q2.transData.getD 32 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨32, by decide⟩ : Fin 148)) (colE2 ⟨32, by decide⟩ 10 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨32, by decide⟩ : Fin 148))
        (colE1 ⟨32, by decide⟩ 10 (transLenTr ⟨32, by decide⟩ 10 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨120, by decide⟩ : Fin 148) ⟨32, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨32, by decide⟩ 10 (transLenTr ⟨32, by decide⟩ 10 hp)) T120_32
      hfix120_32 hinj120_32 hcardT120_32
      (fun i => conj_mem_of_fixedPoints _ _ (T120_32 i) (hfix120_32 i) _)
      ⟨120, by decide⟩ ⟨32, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨32, by decide⟩ 10 hp) Q2.T120_32_2 Q2.hfix120_32_2 Q2.hinj120_32_2
      Q2.hcardT120_32_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_32_2 i) (Q2.hfix120_32_2 i) _)
      ?_).symm
  rw [show colData1 (⟨120, by decide⟩ : Fin 148)
        ((colE1 ⟨32, by decide⟩ 10 (transLenTr ⟨32, by decide⟩ 10 hp) : ↥(reps ⟨32, by decide⟩)) : Coordinate 1)
        T120_32 = colFn colCertDiv_120_32_10.D1 (m := 5) from colCertDiv_120_32_10.bind1,
    show colData2 (⟨120, by decide⟩ : Fin 148)
        ((colE2 ⟨32, by decide⟩ 10 hp : ↥(Q2.reps ⟨32, by decide⟩)) : Coordinate 2)
        Q2.T120_32_2 = colFn colCertDiv_120_32_10.D2 (m := 5) from colCertDiv_120_32_10.bind2]
  rw [alnId_120 j hj]
  exact fastcode_of_div ⟨120, by decide⟩ _ _ _
    ((alnId_120 j hj) ▸ Q2.listedAt (⟨120, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨120, by decide⟩ : Fin 148) hj hq).1) colCertDiv_120_32_10_match


theorem leaf_120_32_15 (hp : 15 < (Q2.transData.getD 32 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨32, by decide⟩ : Fin 148)) (colE2 ⟨32, by decide⟩ 15 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨32, by decide⟩ : Fin 148))
        (colE1 ⟨32, by decide⟩ 15 (transLenTr ⟨32, by decide⟩ 15 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨120, by decide⟩ : Fin 148) ⟨32, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨32, by decide⟩ 15 (transLenTr ⟨32, by decide⟩ 15 hp)) T120_32
      hfix120_32 hinj120_32 hcardT120_32
      (fun i => conj_mem_of_fixedPoints _ _ (T120_32 i) (hfix120_32 i) _)
      ⟨120, by decide⟩ ⟨32, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨32, by decide⟩ 15 hp) Q2.T120_32_2 Q2.hfix120_32_2 Q2.hinj120_32_2
      Q2.hcardT120_32_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_32_2 i) (Q2.hfix120_32_2 i) _)
      ?_).symm
  rw [show colData1 (⟨120, by decide⟩ : Fin 148)
        ((colE1 ⟨32, by decide⟩ 15 (transLenTr ⟨32, by decide⟩ 15 hp) : ↥(reps ⟨32, by decide⟩)) : Coordinate 1)
        T120_32 = colFn colCertDiv_120_32_15.D1 (m := 5) from colCertDiv_120_32_15.bind1,
    show colData2 (⟨120, by decide⟩ : Fin 148)
        ((colE2 ⟨32, by decide⟩ 15 hp : ↥(Q2.reps ⟨32, by decide⟩)) : Coordinate 2)
        Q2.T120_32_2 = colFn colCertDiv_120_32_15.D2 (m := 5) from colCertDiv_120_32_15.bind2]
  rw [alnId_120 j hj]
  exact fastcode_of_div ⟨120, by decide⟩ _ _ _
    ((alnId_120 j hj) ▸ Q2.listedAt (⟨120, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨120, by decide⟩ : Fin 148) hj hq).1) colCertDiv_120_32_15_match


theorem leaf_120_32_20 (hp : 20 < (Q2.transData.getD 32 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨32, by decide⟩ : Fin 148)) (colE2 ⟨32, by decide⟩ 20 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨32, by decide⟩ : Fin 148))
        (colE1 ⟨32, by decide⟩ 20 (transLenTr ⟨32, by decide⟩ 20 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨120, by decide⟩ : Fin 148) ⟨32, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨32, by decide⟩ 20 (transLenTr ⟨32, by decide⟩ 20 hp)) T120_32
      hfix120_32 hinj120_32 hcardT120_32
      (fun i => conj_mem_of_fixedPoints _ _ (T120_32 i) (hfix120_32 i) _)
      ⟨120, by decide⟩ ⟨32, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨32, by decide⟩ 20 hp) Q2.T120_32_2 Q2.hfix120_32_2 Q2.hinj120_32_2
      Q2.hcardT120_32_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_32_2 i) (Q2.hfix120_32_2 i) _)
      ?_).symm
  rw [show colData1 (⟨120, by decide⟩ : Fin 148)
        ((colE1 ⟨32, by decide⟩ 20 (transLenTr ⟨32, by decide⟩ 20 hp) : ↥(reps ⟨32, by decide⟩)) : Coordinate 1)
        T120_32 = colFn colCertDiv_120_32_20.D1 (m := 5) from colCertDiv_120_32_20.bind1,
    show colData2 (⟨120, by decide⟩ : Fin 148)
        ((colE2 ⟨32, by decide⟩ 20 hp : ↥(Q2.reps ⟨32, by decide⟩)) : Coordinate 2)
        Q2.T120_32_2 = colFn colCertDiv_120_32_20.D2 (m := 5) from colCertDiv_120_32_20.bind2]
  rw [alnId_120 j hj]
  exact fastcode_of_div ⟨120, by decide⟩ _ _ _
    ((alnId_120 j hj) ▸ Q2.listedAt (⟨120, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨120, by decide⟩ : Fin 148) hj hq).1) colCertDiv_120_32_20_match


theorem leaf_120_37_0 (hp : 0 < (Q2.transData.getD 37 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨37, by decide⟩ : Fin 148)) (colE2 ⟨37, by decide⟩ 0 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨37, by decide⟩ : Fin 148))
        (colE1 ⟨37, by decide⟩ 0 (transLenTr ⟨37, by decide⟩ 0 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨37, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨37, by decide⟩ 0 (transLenTr ⟨37, by decide⟩ 0 hp)) T120_37
      hfix120_37 hinj120_37 hcardT120_37
      (fun i => conj_mem_of_fixedPoints _ _ (T120_37 i) (hfix120_37 i) _)
      ⟨120, by decide⟩ ⟨37, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨37, by decide⟩ 0 hp) Q2.T120_37_2 Q2.hfix120_37_2 Q2.hinj120_37_2
      Q2.hcardT120_37_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_37_2 i) (Q2.hfix120_37_2 i) _)
      colCert_120_37_0.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_37_1 (hp : 1 < (Q2.transData.getD 37 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨37, by decide⟩ : Fin 148)) (colE2 ⟨37, by decide⟩ 1 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨37, by decide⟩ : Fin 148))
        (colE1 ⟨37, by decide⟩ 1 (transLenTr ⟨37, by decide⟩ 1 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨37, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨37, by decide⟩ 1 (transLenTr ⟨37, by decide⟩ 1 hp)) T120_37
      hfix120_37 hinj120_37 hcardT120_37
      (fun i => conj_mem_of_fixedPoints _ _ (T120_37 i) (hfix120_37 i) _)
      ⟨120, by decide⟩ ⟨37, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨37, by decide⟩ 1 hp) Q2.T120_37_2 Q2.hfix120_37_2 Q2.hinj120_37_2
      Q2.hcardT120_37_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_37_2 i) (Q2.hfix120_37_2 i) _)
      colCert_120_37_1.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_37_2 (hp : 2 < (Q2.transData.getD 37 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨37, by decide⟩ : Fin 148)) (colE2 ⟨37, by decide⟩ 2 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨37, by decide⟩ : Fin 148))
        (colE1 ⟨37, by decide⟩ 2 (transLenTr ⟨37, by decide⟩ 2 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨37, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨37, by decide⟩ 2 (transLenTr ⟨37, by decide⟩ 2 hp)) T120_37
      hfix120_37 hinj120_37 hcardT120_37
      (fun i => conj_mem_of_fixedPoints _ _ (T120_37 i) (hfix120_37 i) _)
      ⟨120, by decide⟩ ⟨37, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨37, by decide⟩ 2 hp) Q2.T120_37_2 Q2.hfix120_37_2 Q2.hinj120_37_2
      Q2.hcardT120_37_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_37_2 i) (Q2.hfix120_37_2 i) _)
      colCert_120_37_2.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_37_3 (hp : 3 < (Q2.transData.getD 37 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨37, by decide⟩ : Fin 148)) (colE2 ⟨37, by decide⟩ 3 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨37, by decide⟩ : Fin 148))
        (colE1 ⟨37, by decide⟩ 3 (transLenTr ⟨37, by decide⟩ 3 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨37, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨37, by decide⟩ 3 (transLenTr ⟨37, by decide⟩ 3 hp)) T120_37
      hfix120_37 hinj120_37 hcardT120_37
      (fun i => conj_mem_of_fixedPoints _ _ (T120_37 i) (hfix120_37 i) _)
      ⟨120, by decide⟩ ⟨37, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨37, by decide⟩ 3 hp) Q2.T120_37_2 Q2.hfix120_37_2 Q2.hinj120_37_2
      Q2.hcardT120_37_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_37_2 i) (Q2.hfix120_37_2 i) _)
      colCert_120_37_3.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_37_4 (hp : 4 < (Q2.transData.getD 37 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨37, by decide⟩ : Fin 148)) (colE2 ⟨37, by decide⟩ 4 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨37, by decide⟩ : Fin 148))
        (colE1 ⟨37, by decide⟩ 4 (transLenTr ⟨37, by decide⟩ 4 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨37, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨37, by decide⟩ 4 (transLenTr ⟨37, by decide⟩ 4 hp)) T120_37
      hfix120_37 hinj120_37 hcardT120_37
      (fun i => conj_mem_of_fixedPoints _ _ (T120_37 i) (hfix120_37 i) _)
      ⟨120, by decide⟩ ⟨37, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨37, by decide⟩ 4 hp) Q2.T120_37_2 Q2.hfix120_37_2 Q2.hinj120_37_2
      Q2.hcardT120_37_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_37_2 i) (Q2.hfix120_37_2 i) _)
      colCert_120_37_4.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_37_5 (hp : 5 < (Q2.transData.getD 37 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨37, by decide⟩ : Fin 148)) (colE2 ⟨37, by decide⟩ 5 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨37, by decide⟩ : Fin 148))
        (colE1 ⟨37, by decide⟩ 5 (transLenTr ⟨37, by decide⟩ 5 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨120, by decide⟩ : Fin 148) ⟨37, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨37, by decide⟩ 5 (transLenTr ⟨37, by decide⟩ 5 hp)) T120_37
      hfix120_37 hinj120_37 hcardT120_37
      (fun i => conj_mem_of_fixedPoints _ _ (T120_37 i) (hfix120_37 i) _)
      ⟨120, by decide⟩ ⟨37, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨37, by decide⟩ 5 hp) Q2.T120_37_2 Q2.hfix120_37_2 Q2.hinj120_37_2
      Q2.hcardT120_37_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_37_2 i) (Q2.hfix120_37_2 i) _)
      ?_).symm
  rw [show colData1 (⟨120, by decide⟩ : Fin 148)
        ((colE1 ⟨37, by decide⟩ 5 (transLenTr ⟨37, by decide⟩ 5 hp) : ↥(reps ⟨37, by decide⟩)) : Coordinate 1)
        T120_37 = colFn colCertDiv_120_37_5.D1 (m := 5) from colCertDiv_120_37_5.bind1,
    show colData2 (⟨120, by decide⟩ : Fin 148)
        ((colE2 ⟨37, by decide⟩ 5 hp : ↥(Q2.reps ⟨37, by decide⟩)) : Coordinate 2)
        Q2.T120_37_2 = colFn colCertDiv_120_37_5.D2 (m := 5) from colCertDiv_120_37_5.bind2]
  rw [alnId_120 j hj]
  exact fastcode_of_div ⟨120, by decide⟩ _ _ _
    ((alnId_120 j hj) ▸ Q2.listedAt (⟨120, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨120, by decide⟩ : Fin 148) hj hq).1) colCertDiv_120_37_5_match


theorem leaf_120_37_10 (hp : 10 < (Q2.transData.getD 37 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨37, by decide⟩ : Fin 148)) (colE2 ⟨37, by decide⟩ 10 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨37, by decide⟩ : Fin 148))
        (colE1 ⟨37, by decide⟩ 10 (transLenTr ⟨37, by decide⟩ 10 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨120, by decide⟩ : Fin 148) ⟨37, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨37, by decide⟩ 10 (transLenTr ⟨37, by decide⟩ 10 hp)) T120_37
      hfix120_37 hinj120_37 hcardT120_37
      (fun i => conj_mem_of_fixedPoints _ _ (T120_37 i) (hfix120_37 i) _)
      ⟨120, by decide⟩ ⟨37, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨37, by decide⟩ 10 hp) Q2.T120_37_2 Q2.hfix120_37_2 Q2.hinj120_37_2
      Q2.hcardT120_37_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_37_2 i) (Q2.hfix120_37_2 i) _)
      ?_).symm
  rw [show colData1 (⟨120, by decide⟩ : Fin 148)
        ((colE1 ⟨37, by decide⟩ 10 (transLenTr ⟨37, by decide⟩ 10 hp) : ↥(reps ⟨37, by decide⟩)) : Coordinate 1)
        T120_37 = colFn colCertDiv_120_37_10.D1 (m := 5) from colCertDiv_120_37_10.bind1,
    show colData2 (⟨120, by decide⟩ : Fin 148)
        ((colE2 ⟨37, by decide⟩ 10 hp : ↥(Q2.reps ⟨37, by decide⟩)) : Coordinate 2)
        Q2.T120_37_2 = colFn colCertDiv_120_37_10.D2 (m := 5) from colCertDiv_120_37_10.bind2]
  rw [alnId_120 j hj]
  exact fastcode_of_div ⟨120, by decide⟩ _ _ _
    ((alnId_120 j hj) ▸ Q2.listedAt (⟨120, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨120, by decide⟩ : Fin 148) hj hq).1) colCertDiv_120_37_10_match


theorem leaf_120_37_15 (hp : 15 < (Q2.transData.getD 37 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨37, by decide⟩ : Fin 148)) (colE2 ⟨37, by decide⟩ 15 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨37, by decide⟩ : Fin 148))
        (colE1 ⟨37, by decide⟩ 15 (transLenTr ⟨37, by decide⟩ 15 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨120, by decide⟩ : Fin 148) ⟨37, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨37, by decide⟩ 15 (transLenTr ⟨37, by decide⟩ 15 hp)) T120_37
      hfix120_37 hinj120_37 hcardT120_37
      (fun i => conj_mem_of_fixedPoints _ _ (T120_37 i) (hfix120_37 i) _)
      ⟨120, by decide⟩ ⟨37, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨37, by decide⟩ 15 hp) Q2.T120_37_2 Q2.hfix120_37_2 Q2.hinj120_37_2
      Q2.hcardT120_37_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_37_2 i) (Q2.hfix120_37_2 i) _)
      ?_).symm
  rw [show colData1 (⟨120, by decide⟩ : Fin 148)
        ((colE1 ⟨37, by decide⟩ 15 (transLenTr ⟨37, by decide⟩ 15 hp) : ↥(reps ⟨37, by decide⟩)) : Coordinate 1)
        T120_37 = colFn colCertDiv_120_37_15.D1 (m := 5) from colCertDiv_120_37_15.bind1,
    show colData2 (⟨120, by decide⟩ : Fin 148)
        ((colE2 ⟨37, by decide⟩ 15 hp : ↥(Q2.reps ⟨37, by decide⟩)) : Coordinate 2)
        Q2.T120_37_2 = colFn colCertDiv_120_37_15.D2 (m := 5) from colCertDiv_120_37_15.bind2]
  rw [alnId_120 j hj]
  exact fastcode_of_div ⟨120, by decide⟩ _ _ _
    ((alnId_120 j hj) ▸ Q2.listedAt (⟨120, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨120, by decide⟩ : Fin 148) hj hq).1) colCertDiv_120_37_15_match


theorem leaf_120_37_20 (hp : 20 < (Q2.transData.getD 37 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨37, by decide⟩ : Fin 148)) (colE2 ⟨37, by decide⟩ 20 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨37, by decide⟩ : Fin 148))
        (colE1 ⟨37, by decide⟩ 20 (transLenTr ⟨37, by decide⟩ 20 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨120, by decide⟩ : Fin 148) ⟨37, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨37, by decide⟩ 20 (transLenTr ⟨37, by decide⟩ 20 hp)) T120_37
      hfix120_37 hinj120_37 hcardT120_37
      (fun i => conj_mem_of_fixedPoints _ _ (T120_37 i) (hfix120_37 i) _)
      ⟨120, by decide⟩ ⟨37, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨37, by decide⟩ 20 hp) Q2.T120_37_2 Q2.hfix120_37_2 Q2.hinj120_37_2
      Q2.hcardT120_37_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_37_2 i) (Q2.hfix120_37_2 i) _)
      ?_).symm
  rw [show colData1 (⟨120, by decide⟩ : Fin 148)
        ((colE1 ⟨37, by decide⟩ 20 (transLenTr ⟨37, by decide⟩ 20 hp) : ↥(reps ⟨37, by decide⟩)) : Coordinate 1)
        T120_37 = colFn colCertDiv_120_37_20.D1 (m := 5) from colCertDiv_120_37_20.bind1,
    show colData2 (⟨120, by decide⟩ : Fin 148)
        ((colE2 ⟨37, by decide⟩ 20 hp : ↥(Q2.reps ⟨37, by decide⟩)) : Coordinate 2)
        Q2.T120_37_2 = colFn colCertDiv_120_37_20.D2 (m := 5) from colCertDiv_120_37_20.bind2]
  rw [alnId_120 j hj]
  exact fastcode_of_div ⟨120, by decide⟩ _ _ _
    ((alnId_120 j hj) ▸ Q2.listedAt (⟨120, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨120, by decide⟩ : Fin 148) hj hq).1) colCertDiv_120_37_20_match


theorem leaf_120_42_0 (hp : 0 < (Q2.transData.getD 42 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨42, by decide⟩ : Fin 148)) (colE2 ⟨42, by decide⟩ 0 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨42, by decide⟩ : Fin 148))
        (colE1 ⟨42, by decide⟩ 0 (transLenTr ⟨42, by decide⟩ 0 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨42, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨42, by decide⟩ 0 (transLenTr ⟨42, by decide⟩ 0 hp)) T120_42
      hfix120_42 hinj120_42 hcardT120_42
      (fun i => conj_mem_of_fixedPoints _ _ (T120_42 i) (hfix120_42 i) _)
      ⟨120, by decide⟩ ⟨42, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨42, by decide⟩ 0 hp) Q2.T120_42_2 Q2.hfix120_42_2 Q2.hinj120_42_2
      Q2.hcardT120_42_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_42_2 i) (Q2.hfix120_42_2 i) _)
      colCert_120_42_0.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_42_1 (hp : 1 < (Q2.transData.getD 42 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨42, by decide⟩ : Fin 148)) (colE2 ⟨42, by decide⟩ 1 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨42, by decide⟩ : Fin 148))
        (colE1 ⟨42, by decide⟩ 1 (transLenTr ⟨42, by decide⟩ 1 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨42, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨42, by decide⟩ 1 (transLenTr ⟨42, by decide⟩ 1 hp)) T120_42
      hfix120_42 hinj120_42 hcardT120_42
      (fun i => conj_mem_of_fixedPoints _ _ (T120_42 i) (hfix120_42 i) _)
      ⟨120, by decide⟩ ⟨42, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨42, by decide⟩ 1 hp) Q2.T120_42_2 Q2.hfix120_42_2 Q2.hinj120_42_2
      Q2.hcardT120_42_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_42_2 i) (Q2.hfix120_42_2 i) _)
      colCert_120_42_1.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_42_2 (hp : 2 < (Q2.transData.getD 42 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨42, by decide⟩ : Fin 148)) (colE2 ⟨42, by decide⟩ 2 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨42, by decide⟩ : Fin 148))
        (colE1 ⟨42, by decide⟩ 2 (transLenTr ⟨42, by decide⟩ 2 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨42, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨42, by decide⟩ 2 (transLenTr ⟨42, by decide⟩ 2 hp)) T120_42
      hfix120_42 hinj120_42 hcardT120_42
      (fun i => conj_mem_of_fixedPoints _ _ (T120_42 i) (hfix120_42 i) _)
      ⟨120, by decide⟩ ⟨42, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨42, by decide⟩ 2 hp) Q2.T120_42_2 Q2.hfix120_42_2 Q2.hinj120_42_2
      Q2.hcardT120_42_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_42_2 i) (Q2.hfix120_42_2 i) _)
      colCert_120_42_2.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_42_3 (hp : 3 < (Q2.transData.getD 42 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨42, by decide⟩ : Fin 148)) (colE2 ⟨42, by decide⟩ 3 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨42, by decide⟩ : Fin 148))
        (colE1 ⟨42, by decide⟩ 3 (transLenTr ⟨42, by decide⟩ 3 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨42, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨42, by decide⟩ 3 (transLenTr ⟨42, by decide⟩ 3 hp)) T120_42
      hfix120_42 hinj120_42 hcardT120_42
      (fun i => conj_mem_of_fixedPoints _ _ (T120_42 i) (hfix120_42 i) _)
      ⟨120, by decide⟩ ⟨42, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨42, by decide⟩ 3 hp) Q2.T120_42_2 Q2.hfix120_42_2 Q2.hinj120_42_2
      Q2.hcardT120_42_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_42_2 i) (Q2.hfix120_42_2 i) _)
      colCert_120_42_3.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_42_4 (hp : 4 < (Q2.transData.getD 42 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨42, by decide⟩ : Fin 148)) (colE2 ⟨42, by decide⟩ 4 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨42, by decide⟩ : Fin 148))
        (colE1 ⟨42, by decide⟩ 4 (transLenTr ⟨42, by decide⟩ 4 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨42, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨42, by decide⟩ 4 (transLenTr ⟨42, by decide⟩ 4 hp)) T120_42
      hfix120_42 hinj120_42 hcardT120_42
      (fun i => conj_mem_of_fixedPoints _ _ (T120_42 i) (hfix120_42 i) _)
      ⟨120, by decide⟩ ⟨42, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨42, by decide⟩ 4 hp) Q2.T120_42_2 Q2.hfix120_42_2 Q2.hinj120_42_2
      Q2.hcardT120_42_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_42_2 i) (Q2.hfix120_42_2 i) _)
      colCert_120_42_4.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_42_5 (hp : 5 < (Q2.transData.getD 42 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨42, by decide⟩ : Fin 148)) (colE2 ⟨42, by decide⟩ 5 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨42, by decide⟩ : Fin 148))
        (colE1 ⟨42, by decide⟩ 5 (transLenTr ⟨42, by decide⟩ 5 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨120, by decide⟩ : Fin 148) ⟨42, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨42, by decide⟩ 5 (transLenTr ⟨42, by decide⟩ 5 hp)) T120_42
      hfix120_42 hinj120_42 hcardT120_42
      (fun i => conj_mem_of_fixedPoints _ _ (T120_42 i) (hfix120_42 i) _)
      ⟨120, by decide⟩ ⟨42, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨42, by decide⟩ 5 hp) Q2.T120_42_2 Q2.hfix120_42_2 Q2.hinj120_42_2
      Q2.hcardT120_42_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_42_2 i) (Q2.hfix120_42_2 i) _)
      ?_).symm
  rw [show colData1 (⟨120, by decide⟩ : Fin 148)
        ((colE1 ⟨42, by decide⟩ 5 (transLenTr ⟨42, by decide⟩ 5 hp) : ↥(reps ⟨42, by decide⟩)) : Coordinate 1)
        T120_42 = colFn colCertDiv_120_42_5.D1 (m := 5) from colCertDiv_120_42_5.bind1,
    show colData2 (⟨120, by decide⟩ : Fin 148)
        ((colE2 ⟨42, by decide⟩ 5 hp : ↥(Q2.reps ⟨42, by decide⟩)) : Coordinate 2)
        Q2.T120_42_2 = colFn colCertDiv_120_42_5.D2 (m := 5) from colCertDiv_120_42_5.bind2]
  rw [alnId_120 j hj]
  exact fastcode_of_div ⟨120, by decide⟩ _ _ _
    ((alnId_120 j hj) ▸ Q2.listedAt (⟨120, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨120, by decide⟩ : Fin 148) hj hq).1) colCertDiv_120_42_5_match


theorem leaf_120_42_10 (hp : 10 < (Q2.transData.getD 42 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨42, by decide⟩ : Fin 148)) (colE2 ⟨42, by decide⟩ 10 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨42, by decide⟩ : Fin 148))
        (colE1 ⟨42, by decide⟩ 10 (transLenTr ⟨42, by decide⟩ 10 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨120, by decide⟩ : Fin 148) ⟨42, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨42, by decide⟩ 10 (transLenTr ⟨42, by decide⟩ 10 hp)) T120_42
      hfix120_42 hinj120_42 hcardT120_42
      (fun i => conj_mem_of_fixedPoints _ _ (T120_42 i) (hfix120_42 i) _)
      ⟨120, by decide⟩ ⟨42, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨42, by decide⟩ 10 hp) Q2.T120_42_2 Q2.hfix120_42_2 Q2.hinj120_42_2
      Q2.hcardT120_42_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_42_2 i) (Q2.hfix120_42_2 i) _)
      ?_).symm
  rw [show colData1 (⟨120, by decide⟩ : Fin 148)
        ((colE1 ⟨42, by decide⟩ 10 (transLenTr ⟨42, by decide⟩ 10 hp) : ↥(reps ⟨42, by decide⟩)) : Coordinate 1)
        T120_42 = colFn colCertDiv_120_42_10.D1 (m := 5) from colCertDiv_120_42_10.bind1,
    show colData2 (⟨120, by decide⟩ : Fin 148)
        ((colE2 ⟨42, by decide⟩ 10 hp : ↥(Q2.reps ⟨42, by decide⟩)) : Coordinate 2)
        Q2.T120_42_2 = colFn colCertDiv_120_42_10.D2 (m := 5) from colCertDiv_120_42_10.bind2]
  rw [alnId_120 j hj]
  exact fastcode_of_div ⟨120, by decide⟩ _ _ _
    ((alnId_120 j hj) ▸ Q2.listedAt (⟨120, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨120, by decide⟩ : Fin 148) hj hq).1) colCertDiv_120_42_10_match


theorem leaf_120_42_15 (hp : 15 < (Q2.transData.getD 42 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨42, by decide⟩ : Fin 148)) (colE2 ⟨42, by decide⟩ 15 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨42, by decide⟩ : Fin 148))
        (colE1 ⟨42, by decide⟩ 15 (transLenTr ⟨42, by decide⟩ 15 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨120, by decide⟩ : Fin 148) ⟨42, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨42, by decide⟩ 15 (transLenTr ⟨42, by decide⟩ 15 hp)) T120_42
      hfix120_42 hinj120_42 hcardT120_42
      (fun i => conj_mem_of_fixedPoints _ _ (T120_42 i) (hfix120_42 i) _)
      ⟨120, by decide⟩ ⟨42, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨42, by decide⟩ 15 hp) Q2.T120_42_2 Q2.hfix120_42_2 Q2.hinj120_42_2
      Q2.hcardT120_42_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_42_2 i) (Q2.hfix120_42_2 i) _)
      ?_).symm
  rw [show colData1 (⟨120, by decide⟩ : Fin 148)
        ((colE1 ⟨42, by decide⟩ 15 (transLenTr ⟨42, by decide⟩ 15 hp) : ↥(reps ⟨42, by decide⟩)) : Coordinate 1)
        T120_42 = colFn colCertDiv_120_42_15.D1 (m := 5) from colCertDiv_120_42_15.bind1,
    show colData2 (⟨120, by decide⟩ : Fin 148)
        ((colE2 ⟨42, by decide⟩ 15 hp : ↥(Q2.reps ⟨42, by decide⟩)) : Coordinate 2)
        Q2.T120_42_2 = colFn colCertDiv_120_42_15.D2 (m := 5) from colCertDiv_120_42_15.bind2]
  rw [alnId_120 j hj]
  exact fastcode_of_div ⟨120, by decide⟩ _ _ _
    ((alnId_120 j hj) ▸ Q2.listedAt (⟨120, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨120, by decide⟩ : Fin 148) hj hq).1) colCertDiv_120_42_15_match


theorem leaf_120_42_20 (hp : 20 < (Q2.transData.getD 42 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨42, by decide⟩ : Fin 148)) (colE2 ⟨42, by decide⟩ 20 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨42, by decide⟩ : Fin 148))
        (colE1 ⟨42, by decide⟩ 20 (transLenTr ⟨42, by decide⟩ 20 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨120, by decide⟩ : Fin 148) ⟨42, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨42, by decide⟩ 20 (transLenTr ⟨42, by decide⟩ 20 hp)) T120_42
      hfix120_42 hinj120_42 hcardT120_42
      (fun i => conj_mem_of_fixedPoints _ _ (T120_42 i) (hfix120_42 i) _)
      ⟨120, by decide⟩ ⟨42, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨42, by decide⟩ 20 hp) Q2.T120_42_2 Q2.hfix120_42_2 Q2.hinj120_42_2
      Q2.hcardT120_42_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_42_2 i) (Q2.hfix120_42_2 i) _)
      ?_).symm
  rw [show colData1 (⟨120, by decide⟩ : Fin 148)
        ((colE1 ⟨42, by decide⟩ 20 (transLenTr ⟨42, by decide⟩ 20 hp) : ↥(reps ⟨42, by decide⟩)) : Coordinate 1)
        T120_42 = colFn colCertDiv_120_42_20.D1 (m := 5) from colCertDiv_120_42_20.bind1,
    show colData2 (⟨120, by decide⟩ : Fin 148)
        ((colE2 ⟨42, by decide⟩ 20 hp : ↥(Q2.reps ⟨42, by decide⟩)) : Coordinate 2)
        Q2.T120_42_2 = colFn colCertDiv_120_42_20.D2 (m := 5) from colCertDiv_120_42_20.bind2]
  rw [alnId_120 j hj]
  exact fastcode_of_div ⟨120, by decide⟩ _ _ _
    ((alnId_120 j hj) ▸ Q2.listedAt (⟨120, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨120, by decide⟩ : Fin 148) hj hq).1) colCertDiv_120_42_20_match


theorem leaf_120_47_0 (hp : 0 < (Q2.transData.getD 47 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨47, by decide⟩ : Fin 148)) (colE2 ⟨47, by decide⟩ 0 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨47, by decide⟩ : Fin 148))
        (colE1 ⟨47, by decide⟩ 0 (transLenTr ⟨47, by decide⟩ 0 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨47, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨47, by decide⟩ 0 (transLenTr ⟨47, by decide⟩ 0 hp)) T120_47
      hfix120_47 hinj120_47 hcardT120_47
      (fun i => conj_mem_of_fixedPoints _ _ (T120_47 i) (hfix120_47 i) _)
      ⟨120, by decide⟩ ⟨47, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨47, by decide⟩ 0 hp) Q2.T120_47_2 Q2.hfix120_47_2 Q2.hinj120_47_2
      Q2.hcardT120_47_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_47_2 i) (Q2.hfix120_47_2 i) _)
      colCert_120_47_0.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_47_1 (hp : 1 < (Q2.transData.getD 47 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨47, by decide⟩ : Fin 148)) (colE2 ⟨47, by decide⟩ 1 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨47, by decide⟩ : Fin 148))
        (colE1 ⟨47, by decide⟩ 1 (transLenTr ⟨47, by decide⟩ 1 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨47, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨47, by decide⟩ 1 (transLenTr ⟨47, by decide⟩ 1 hp)) T120_47
      hfix120_47 hinj120_47 hcardT120_47
      (fun i => conj_mem_of_fixedPoints _ _ (T120_47 i) (hfix120_47 i) _)
      ⟨120, by decide⟩ ⟨47, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨47, by decide⟩ 1 hp) Q2.T120_47_2 Q2.hfix120_47_2 Q2.hinj120_47_2
      Q2.hcardT120_47_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_47_2 i) (Q2.hfix120_47_2 i) _)
      colCert_120_47_1.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_47_2 (hp : 2 < (Q2.transData.getD 47 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨47, by decide⟩ : Fin 148)) (colE2 ⟨47, by decide⟩ 2 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨47, by decide⟩ : Fin 148))
        (colE1 ⟨47, by decide⟩ 2 (transLenTr ⟨47, by decide⟩ 2 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨47, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨47, by decide⟩ 2 (transLenTr ⟨47, by decide⟩ 2 hp)) T120_47
      hfix120_47 hinj120_47 hcardT120_47
      (fun i => conj_mem_of_fixedPoints _ _ (T120_47 i) (hfix120_47 i) _)
      ⟨120, by decide⟩ ⟨47, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨47, by decide⟩ 2 hp) Q2.T120_47_2 Q2.hfix120_47_2 Q2.hinj120_47_2
      Q2.hcardT120_47_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_47_2 i) (Q2.hfix120_47_2 i) _)
      colCert_120_47_2.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_47_3 (hp : 3 < (Q2.transData.getD 47 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨47, by decide⟩ : Fin 148)) (colE2 ⟨47, by decide⟩ 3 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨47, by decide⟩ : Fin 148))
        (colE1 ⟨47, by decide⟩ 3 (transLenTr ⟨47, by decide⟩ 3 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨47, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨47, by decide⟩ 3 (transLenTr ⟨47, by decide⟩ 3 hp)) T120_47
      hfix120_47 hinj120_47 hcardT120_47
      (fun i => conj_mem_of_fixedPoints _ _ (T120_47 i) (hfix120_47 i) _)
      ⟨120, by decide⟩ ⟨47, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨47, by decide⟩ 3 hp) Q2.T120_47_2 Q2.hfix120_47_2 Q2.hinj120_47_2
      Q2.hcardT120_47_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_47_2 i) (Q2.hfix120_47_2 i) _)
      colCert_120_47_3.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_47_4 (hp : 4 < (Q2.transData.getD 47 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨47, by decide⟩ : Fin 148)) (colE2 ⟨47, by decide⟩ 4 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨47, by decide⟩ : Fin 148))
        (colE1 ⟨47, by decide⟩ 4 (transLenTr ⟨47, by decide⟩ 4 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨47, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨47, by decide⟩ 4 (transLenTr ⟨47, by decide⟩ 4 hp)) T120_47
      hfix120_47 hinj120_47 hcardT120_47
      (fun i => conj_mem_of_fixedPoints _ _ (T120_47 i) (hfix120_47 i) _)
      ⟨120, by decide⟩ ⟨47, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨47, by decide⟩ 4 hp) Q2.T120_47_2 Q2.hfix120_47_2 Q2.hinj120_47_2
      Q2.hcardT120_47_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_47_2 i) (Q2.hfix120_47_2 i) _)
      colCert_120_47_4.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_47_5 (hp : 5 < (Q2.transData.getD 47 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨47, by decide⟩ : Fin 148)) (colE2 ⟨47, by decide⟩ 5 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨47, by decide⟩ : Fin 148))
        (colE1 ⟨47, by decide⟩ 5 (transLenTr ⟨47, by decide⟩ 5 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨120, by decide⟩ : Fin 148) ⟨47, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨47, by decide⟩ 5 (transLenTr ⟨47, by decide⟩ 5 hp)) T120_47
      hfix120_47 hinj120_47 hcardT120_47
      (fun i => conj_mem_of_fixedPoints _ _ (T120_47 i) (hfix120_47 i) _)
      ⟨120, by decide⟩ ⟨47, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨47, by decide⟩ 5 hp) Q2.T120_47_2 Q2.hfix120_47_2 Q2.hinj120_47_2
      Q2.hcardT120_47_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_47_2 i) (Q2.hfix120_47_2 i) _)
      ?_).symm
  rw [show colData1 (⟨120, by decide⟩ : Fin 148)
        ((colE1 ⟨47, by decide⟩ 5 (transLenTr ⟨47, by decide⟩ 5 hp) : ↥(reps ⟨47, by decide⟩)) : Coordinate 1)
        T120_47 = colFn colCertDiv_120_47_5.D1 (m := 5) from colCertDiv_120_47_5.bind1,
    show colData2 (⟨120, by decide⟩ : Fin 148)
        ((colE2 ⟨47, by decide⟩ 5 hp : ↥(Q2.reps ⟨47, by decide⟩)) : Coordinate 2)
        Q2.T120_47_2 = colFn colCertDiv_120_47_5.D2 (m := 5) from colCertDiv_120_47_5.bind2]
  rw [alnId_120 j hj]
  exact fastcode_of_div ⟨120, by decide⟩ _ _ _
    ((alnId_120 j hj) ▸ Q2.listedAt (⟨120, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨120, by decide⟩ : Fin 148) hj hq).1) colCertDiv_120_47_5_match


theorem leaf_120_47_10 (hp : 10 < (Q2.transData.getD 47 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨47, by decide⟩ : Fin 148)) (colE2 ⟨47, by decide⟩ 10 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨47, by decide⟩ : Fin 148))
        (colE1 ⟨47, by decide⟩ 10 (transLenTr ⟨47, by decide⟩ 10 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨120, by decide⟩ : Fin 148) ⟨47, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨47, by decide⟩ 10 (transLenTr ⟨47, by decide⟩ 10 hp)) T120_47
      hfix120_47 hinj120_47 hcardT120_47
      (fun i => conj_mem_of_fixedPoints _ _ (T120_47 i) (hfix120_47 i) _)
      ⟨120, by decide⟩ ⟨47, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨47, by decide⟩ 10 hp) Q2.T120_47_2 Q2.hfix120_47_2 Q2.hinj120_47_2
      Q2.hcardT120_47_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_47_2 i) (Q2.hfix120_47_2 i) _)
      ?_).symm
  rw [show colData1 (⟨120, by decide⟩ : Fin 148)
        ((colE1 ⟨47, by decide⟩ 10 (transLenTr ⟨47, by decide⟩ 10 hp) : ↥(reps ⟨47, by decide⟩)) : Coordinate 1)
        T120_47 = colFn colCertDiv_120_47_10.D1 (m := 5) from colCertDiv_120_47_10.bind1,
    show colData2 (⟨120, by decide⟩ : Fin 148)
        ((colE2 ⟨47, by decide⟩ 10 hp : ↥(Q2.reps ⟨47, by decide⟩)) : Coordinate 2)
        Q2.T120_47_2 = colFn colCertDiv_120_47_10.D2 (m := 5) from colCertDiv_120_47_10.bind2]
  rw [alnId_120 j hj]
  exact fastcode_of_div ⟨120, by decide⟩ _ _ _
    ((alnId_120 j hj) ▸ Q2.listedAt (⟨120, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨120, by decide⟩ : Fin 148) hj hq).1) colCertDiv_120_47_10_match


theorem leaf_120_47_15 (hp : 15 < (Q2.transData.getD 47 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨47, by decide⟩ : Fin 148)) (colE2 ⟨47, by decide⟩ 15 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨47, by decide⟩ : Fin 148))
        (colE1 ⟨47, by decide⟩ 15 (transLenTr ⟨47, by decide⟩ 15 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨120, by decide⟩ : Fin 148) ⟨47, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨47, by decide⟩ 15 (transLenTr ⟨47, by decide⟩ 15 hp)) T120_47
      hfix120_47 hinj120_47 hcardT120_47
      (fun i => conj_mem_of_fixedPoints _ _ (T120_47 i) (hfix120_47 i) _)
      ⟨120, by decide⟩ ⟨47, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨47, by decide⟩ 15 hp) Q2.T120_47_2 Q2.hfix120_47_2 Q2.hinj120_47_2
      Q2.hcardT120_47_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_47_2 i) (Q2.hfix120_47_2 i) _)
      ?_).symm
  rw [show colData1 (⟨120, by decide⟩ : Fin 148)
        ((colE1 ⟨47, by decide⟩ 15 (transLenTr ⟨47, by decide⟩ 15 hp) : ↥(reps ⟨47, by decide⟩)) : Coordinate 1)
        T120_47 = colFn colCertDiv_120_47_15.D1 (m := 5) from colCertDiv_120_47_15.bind1,
    show colData2 (⟨120, by decide⟩ : Fin 148)
        ((colE2 ⟨47, by decide⟩ 15 hp : ↥(Q2.reps ⟨47, by decide⟩)) : Coordinate 2)
        Q2.T120_47_2 = colFn colCertDiv_120_47_15.D2 (m := 5) from colCertDiv_120_47_15.bind2]
  rw [alnId_120 j hj]
  exact fastcode_of_div ⟨120, by decide⟩ _ _ _
    ((alnId_120 j hj) ▸ Q2.listedAt (⟨120, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨120, by decide⟩ : Fin 148) hj hq).1) colCertDiv_120_47_15_match


theorem leaf_120_47_20 (hp : 20 < (Q2.transData.getD 47 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨47, by decide⟩ : Fin 148)) (colE2 ⟨47, by decide⟩ 20 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨47, by decide⟩ : Fin 148))
        (colE1 ⟨47, by decide⟩ 20 (transLenTr ⟨47, by decide⟩ 20 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨120, by decide⟩ : Fin 148) ⟨47, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨47, by decide⟩ 20 (transLenTr ⟨47, by decide⟩ 20 hp)) T120_47
      hfix120_47 hinj120_47 hcardT120_47
      (fun i => conj_mem_of_fixedPoints _ _ (T120_47 i) (hfix120_47 i) _)
      ⟨120, by decide⟩ ⟨47, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨47, by decide⟩ 20 hp) Q2.T120_47_2 Q2.hfix120_47_2 Q2.hinj120_47_2
      Q2.hcardT120_47_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_47_2 i) (Q2.hfix120_47_2 i) _)
      ?_).symm
  rw [show colData1 (⟨120, by decide⟩ : Fin 148)
        ((colE1 ⟨47, by decide⟩ 20 (transLenTr ⟨47, by decide⟩ 20 hp) : ↥(reps ⟨47, by decide⟩)) : Coordinate 1)
        T120_47 = colFn colCertDiv_120_47_20.D1 (m := 5) from colCertDiv_120_47_20.bind1,
    show colData2 (⟨120, by decide⟩ : Fin 148)
        ((colE2 ⟨47, by decide⟩ 20 hp : ↥(Q2.reps ⟨47, by decide⟩)) : Coordinate 2)
        Q2.T120_47_2 = colFn colCertDiv_120_47_20.D2 (m := 5) from colCertDiv_120_47_20.bind2]
  rw [alnId_120 j hj]
  exact fastcode_of_div ⟨120, by decide⟩ _ _ _
    ((alnId_120 j hj) ▸ Q2.listedAt (⟨120, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨120, by decide⟩ : Fin 148) hj hq).1) colCertDiv_120_47_20_match


theorem leaf_120_52_0 (hp : 0 < (Q2.transData.getD 52 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨52, by decide⟩ : Fin 148)) (colE2 ⟨52, by decide⟩ 0 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨52, by decide⟩ : Fin 148))
        (colE1 ⟨52, by decide⟩ 0 (transLenTr ⟨52, by decide⟩ 0 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨52, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨52, by decide⟩ 0 (transLenTr ⟨52, by decide⟩ 0 hp)) T120_52
      hfix120_52 hinj120_52 hcardT120_52
      (fun i => conj_mem_of_fixedPoints _ _ (T120_52 i) (hfix120_52 i) _)
      ⟨120, by decide⟩ ⟨52, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨52, by decide⟩ 0 hp) Q2.T120_52_2 Q2.hfix120_52_2 Q2.hinj120_52_2
      Q2.hcardT120_52_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_52_2 i) (Q2.hfix120_52_2 i) _)
      colCert_120_52_0.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_52_1 (hp : 1 < (Q2.transData.getD 52 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨52, by decide⟩ : Fin 148)) (colE2 ⟨52, by decide⟩ 1 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨52, by decide⟩ : Fin 148))
        (colE1 ⟨52, by decide⟩ 1 (transLenTr ⟨52, by decide⟩ 1 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨52, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨52, by decide⟩ 1 (transLenTr ⟨52, by decide⟩ 1 hp)) T120_52
      hfix120_52 hinj120_52 hcardT120_52
      (fun i => conj_mem_of_fixedPoints _ _ (T120_52 i) (hfix120_52 i) _)
      ⟨120, by decide⟩ ⟨52, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨52, by decide⟩ 1 hp) Q2.T120_52_2 Q2.hfix120_52_2 Q2.hinj120_52_2
      Q2.hcardT120_52_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_52_2 i) (Q2.hfix120_52_2 i) _)
      colCert_120_52_1.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_52_2 (hp : 2 < (Q2.transData.getD 52 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨52, by decide⟩ : Fin 148)) (colE2 ⟨52, by decide⟩ 2 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨52, by decide⟩ : Fin 148))
        (colE1 ⟨52, by decide⟩ 2 (transLenTr ⟨52, by decide⟩ 2 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨52, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨52, by decide⟩ 2 (transLenTr ⟨52, by decide⟩ 2 hp)) T120_52
      hfix120_52 hinj120_52 hcardT120_52
      (fun i => conj_mem_of_fixedPoints _ _ (T120_52 i) (hfix120_52 i) _)
      ⟨120, by decide⟩ ⟨52, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨52, by decide⟩ 2 hp) Q2.T120_52_2 Q2.hfix120_52_2 Q2.hinj120_52_2
      Q2.hcardT120_52_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_52_2 i) (Q2.hfix120_52_2 i) _)
      colCert_120_52_2.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_52_3 (hp : 3 < (Q2.transData.getD 52 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨52, by decide⟩ : Fin 148)) (colE2 ⟨52, by decide⟩ 3 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨52, by decide⟩ : Fin 148))
        (colE1 ⟨52, by decide⟩ 3 (transLenTr ⟨52, by decide⟩ 3 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨52, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨52, by decide⟩ 3 (transLenTr ⟨52, by decide⟩ 3 hp)) T120_52
      hfix120_52 hinj120_52 hcardT120_52
      (fun i => conj_mem_of_fixedPoints _ _ (T120_52 i) (hfix120_52 i) _)
      ⟨120, by decide⟩ ⟨52, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨52, by decide⟩ 3 hp) Q2.T120_52_2 Q2.hfix120_52_2 Q2.hinj120_52_2
      Q2.hcardT120_52_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_52_2 i) (Q2.hfix120_52_2 i) _)
      colCert_120_52_3.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_52_4 (hp : 4 < (Q2.transData.getD 52 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨52, by decide⟩ : Fin 148)) (colE2 ⟨52, by decide⟩ 4 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨52, by decide⟩ : Fin 148))
        (colE1 ⟨52, by decide⟩ 4 (transLenTr ⟨52, by decide⟩ 4 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨52, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨52, by decide⟩ 4 (transLenTr ⟨52, by decide⟩ 4 hp)) T120_52
      hfix120_52 hinj120_52 hcardT120_52
      (fun i => conj_mem_of_fixedPoints _ _ (T120_52 i) (hfix120_52 i) _)
      ⟨120, by decide⟩ ⟨52, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨52, by decide⟩ 4 hp) Q2.T120_52_2 Q2.hfix120_52_2 Q2.hinj120_52_2
      Q2.hcardT120_52_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_52_2 i) (Q2.hfix120_52_2 i) _)
      colCert_120_52_4.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_52_5 (hp : 5 < (Q2.transData.getD 52 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨52, by decide⟩ : Fin 148)) (colE2 ⟨52, by decide⟩ 5 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨52, by decide⟩ : Fin 148))
        (colE1 ⟨52, by decide⟩ 5 (transLenTr ⟨52, by decide⟩ 5 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨120, by decide⟩ : Fin 148) ⟨52, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨52, by decide⟩ 5 (transLenTr ⟨52, by decide⟩ 5 hp)) T120_52
      hfix120_52 hinj120_52 hcardT120_52
      (fun i => conj_mem_of_fixedPoints _ _ (T120_52 i) (hfix120_52 i) _)
      ⟨120, by decide⟩ ⟨52, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨52, by decide⟩ 5 hp) Q2.T120_52_2 Q2.hfix120_52_2 Q2.hinj120_52_2
      Q2.hcardT120_52_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_52_2 i) (Q2.hfix120_52_2 i) _)
      ?_).symm
  rw [show colData1 (⟨120, by decide⟩ : Fin 148)
        ((colE1 ⟨52, by decide⟩ 5 (transLenTr ⟨52, by decide⟩ 5 hp) : ↥(reps ⟨52, by decide⟩)) : Coordinate 1)
        T120_52 = colFn colCertDiv_120_52_5.D1 (m := 5) from colCertDiv_120_52_5.bind1,
    show colData2 (⟨120, by decide⟩ : Fin 148)
        ((colE2 ⟨52, by decide⟩ 5 hp : ↥(Q2.reps ⟨52, by decide⟩)) : Coordinate 2)
        Q2.T120_52_2 = colFn colCertDiv_120_52_5.D2 (m := 5) from colCertDiv_120_52_5.bind2]
  rw [alnId_120 j hj]
  exact fastcode_of_div ⟨120, by decide⟩ _ _ _
    ((alnId_120 j hj) ▸ Q2.listedAt (⟨120, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨120, by decide⟩ : Fin 148) hj hq).1) colCertDiv_120_52_5_match


theorem leaf_120_52_10 (hp : 10 < (Q2.transData.getD 52 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨52, by decide⟩ : Fin 148)) (colE2 ⟨52, by decide⟩ 10 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨52, by decide⟩ : Fin 148))
        (colE1 ⟨52, by decide⟩ 10 (transLenTr ⟨52, by decide⟩ 10 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨120, by decide⟩ : Fin 148) ⟨52, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨52, by decide⟩ 10 (transLenTr ⟨52, by decide⟩ 10 hp)) T120_52
      hfix120_52 hinj120_52 hcardT120_52
      (fun i => conj_mem_of_fixedPoints _ _ (T120_52 i) (hfix120_52 i) _)
      ⟨120, by decide⟩ ⟨52, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨52, by decide⟩ 10 hp) Q2.T120_52_2 Q2.hfix120_52_2 Q2.hinj120_52_2
      Q2.hcardT120_52_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_52_2 i) (Q2.hfix120_52_2 i) _)
      ?_).symm
  rw [show colData1 (⟨120, by decide⟩ : Fin 148)
        ((colE1 ⟨52, by decide⟩ 10 (transLenTr ⟨52, by decide⟩ 10 hp) : ↥(reps ⟨52, by decide⟩)) : Coordinate 1)
        T120_52 = colFn colCertDiv_120_52_10.D1 (m := 5) from colCertDiv_120_52_10.bind1,
    show colData2 (⟨120, by decide⟩ : Fin 148)
        ((colE2 ⟨52, by decide⟩ 10 hp : ↥(Q2.reps ⟨52, by decide⟩)) : Coordinate 2)
        Q2.T120_52_2 = colFn colCertDiv_120_52_10.D2 (m := 5) from colCertDiv_120_52_10.bind2]
  rw [alnId_120 j hj]
  exact fastcode_of_div ⟨120, by decide⟩ _ _ _
    ((alnId_120 j hj) ▸ Q2.listedAt (⟨120, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨120, by decide⟩ : Fin 148) hj hq).1) colCertDiv_120_52_10_match


theorem leaf_120_52_15 (hp : 15 < (Q2.transData.getD 52 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨52, by decide⟩ : Fin 148)) (colE2 ⟨52, by decide⟩ 15 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨52, by decide⟩ : Fin 148))
        (colE1 ⟨52, by decide⟩ 15 (transLenTr ⟨52, by decide⟩ 15 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨120, by decide⟩ : Fin 148) ⟨52, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨52, by decide⟩ 15 (transLenTr ⟨52, by decide⟩ 15 hp)) T120_52
      hfix120_52 hinj120_52 hcardT120_52
      (fun i => conj_mem_of_fixedPoints _ _ (T120_52 i) (hfix120_52 i) _)
      ⟨120, by decide⟩ ⟨52, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨52, by decide⟩ 15 hp) Q2.T120_52_2 Q2.hfix120_52_2 Q2.hinj120_52_2
      Q2.hcardT120_52_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_52_2 i) (Q2.hfix120_52_2 i) _)
      ?_).symm
  rw [show colData1 (⟨120, by decide⟩ : Fin 148)
        ((colE1 ⟨52, by decide⟩ 15 (transLenTr ⟨52, by decide⟩ 15 hp) : ↥(reps ⟨52, by decide⟩)) : Coordinate 1)
        T120_52 = colFn colCertDiv_120_52_15.D1 (m := 5) from colCertDiv_120_52_15.bind1,
    show colData2 (⟨120, by decide⟩ : Fin 148)
        ((colE2 ⟨52, by decide⟩ 15 hp : ↥(Q2.reps ⟨52, by decide⟩)) : Coordinate 2)
        Q2.T120_52_2 = colFn colCertDiv_120_52_15.D2 (m := 5) from colCertDiv_120_52_15.bind2]
  rw [alnId_120 j hj]
  exact fastcode_of_div ⟨120, by decide⟩ _ _ _
    ((alnId_120 j hj) ▸ Q2.listedAt (⟨120, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨120, by decide⟩ : Fin 148) hj hq).1) colCertDiv_120_52_15_match


theorem leaf_120_52_20 (hp : 20 < (Q2.transData.getD 52 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨52, by decide⟩ : Fin 148)) (colE2 ⟨52, by decide⟩ 20 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨52, by decide⟩ : Fin 148))
        (colE1 ⟨52, by decide⟩ 20 (transLenTr ⟨52, by decide⟩ 20 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨120, by decide⟩ : Fin 148) ⟨52, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨52, by decide⟩ 20 (transLenTr ⟨52, by decide⟩ 20 hp)) T120_52
      hfix120_52 hinj120_52 hcardT120_52
      (fun i => conj_mem_of_fixedPoints _ _ (T120_52 i) (hfix120_52 i) _)
      ⟨120, by decide⟩ ⟨52, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨52, by decide⟩ 20 hp) Q2.T120_52_2 Q2.hfix120_52_2 Q2.hinj120_52_2
      Q2.hcardT120_52_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_52_2 i) (Q2.hfix120_52_2 i) _)
      ?_).symm
  rw [show colData1 (⟨120, by decide⟩ : Fin 148)
        ((colE1 ⟨52, by decide⟩ 20 (transLenTr ⟨52, by decide⟩ 20 hp) : ↥(reps ⟨52, by decide⟩)) : Coordinate 1)
        T120_52 = colFn colCertDiv_120_52_20.D1 (m := 5) from colCertDiv_120_52_20.bind1,
    show colData2 (⟨120, by decide⟩ : Fin 148)
        ((colE2 ⟨52, by decide⟩ 20 hp : ↥(Q2.reps ⟨52, by decide⟩)) : Coordinate 2)
        Q2.T120_52_2 = colFn colCertDiv_120_52_20.D2 (m := 5) from colCertDiv_120_52_20.bind2]
  rw [alnId_120 j hj]
  exact fastcode_of_div ⟨120, by decide⟩ _ _ _
    ((alnId_120 j hj) ▸ Q2.listedAt (⟨120, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨120, by decide⟩ : Fin 148) hj hq).1) colCertDiv_120_52_20_match


theorem leaf_120_53_0 (hp : 0 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 0 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 0 (transLenTr ⟨53, by decide⟩ 0 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 0 (transLenTr ⟨53, by decide⟩ 0 hp)) T120_53
      hfix120_53 hinj120_53 hcardT120_53
      (fun i => conj_mem_of_fixedPoints _ _ (T120_53 i) (hfix120_53 i) _)
      ⟨120, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 0 hp) Q2.T120_53_2 Q2.hfix120_53_2 Q2.hinj120_53_2
      Q2.hcardT120_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_53_2 i) (Q2.hfix120_53_2 i) _)
      colCert_120_53_0.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_53_1 (hp : 1 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 1 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 1 (transLenTr ⟨53, by decide⟩ 1 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 1 (transLenTr ⟨53, by decide⟩ 1 hp)) T120_53
      hfix120_53 hinj120_53 hcardT120_53
      (fun i => conj_mem_of_fixedPoints _ _ (T120_53 i) (hfix120_53 i) _)
      ⟨120, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 1 hp) Q2.T120_53_2 Q2.hfix120_53_2 Q2.hinj120_53_2
      Q2.hcardT120_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_53_2 i) (Q2.hfix120_53_2 i) _)
      colCert_120_53_1.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_53_2 (hp : 2 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 2 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 2 (transLenTr ⟨53, by decide⟩ 2 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 2 (transLenTr ⟨53, by decide⟩ 2 hp)) T120_53
      hfix120_53 hinj120_53 hcardT120_53
      (fun i => conj_mem_of_fixedPoints _ _ (T120_53 i) (hfix120_53 i) _)
      ⟨120, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 2 hp) Q2.T120_53_2 Q2.hfix120_53_2 Q2.hinj120_53_2
      Q2.hcardT120_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_53_2 i) (Q2.hfix120_53_2 i) _)
      colCert_120_53_2.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_53_3 (hp : 3 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 3 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 3 (transLenTr ⟨53, by decide⟩ 3 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 3 (transLenTr ⟨53, by decide⟩ 3 hp)) T120_53
      hfix120_53 hinj120_53 hcardT120_53
      (fun i => conj_mem_of_fixedPoints _ _ (T120_53 i) (hfix120_53 i) _)
      ⟨120, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 3 hp) Q2.T120_53_2 Q2.hfix120_53_2 Q2.hinj120_53_2
      Q2.hcardT120_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_53_2 i) (Q2.hfix120_53_2 i) _)
      colCert_120_53_3.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_53_4 (hp : 4 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 4 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 4 (transLenTr ⟨53, by decide⟩ 4 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 4 (transLenTr ⟨53, by decide⟩ 4 hp)) T120_53
      hfix120_53 hinj120_53 hcardT120_53
      (fun i => conj_mem_of_fixedPoints _ _ (T120_53 i) (hfix120_53 i) _)
      ⟨120, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 4 hp) Q2.T120_53_2 Q2.hfix120_53_2 Q2.hinj120_53_2
      Q2.hcardT120_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_53_2 i) (Q2.hfix120_53_2 i) _)
      colCert_120_53_4.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_53_5 (hp : 5 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 5 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 5 (transLenTr ⟨53, by decide⟩ 5 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 5 (transLenTr ⟨53, by decide⟩ 5 hp)) T120_53
      hfix120_53 hinj120_53 hcardT120_53
      (fun i => conj_mem_of_fixedPoints _ _ (T120_53 i) (hfix120_53 i) _)
      ⟨120, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 5 hp) Q2.T120_53_2 Q2.hfix120_53_2 Q2.hinj120_53_2
      Q2.hcardT120_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_53_2 i) (Q2.hfix120_53_2 i) _)
      colCert_120_53_5.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_53_10 (hp : 10 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 10 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 10 (transLenTr ⟨53, by decide⟩ 10 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 10 (transLenTr ⟨53, by decide⟩ 10 hp)) T120_53
      hfix120_53 hinj120_53 hcardT120_53
      (fun i => conj_mem_of_fixedPoints _ _ (T120_53 i) (hfix120_53 i) _)
      ⟨120, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 10 hp) Q2.T120_53_2 Q2.hfix120_53_2 Q2.hinj120_53_2
      Q2.hcardT120_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_53_2 i) (Q2.hfix120_53_2 i) _)
      colCert_120_53_10.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_53_15 (hp : 15 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 15 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 15 (transLenTr ⟨53, by decide⟩ 15 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 15 (transLenTr ⟨53, by decide⟩ 15 hp)) T120_53
      hfix120_53 hinj120_53 hcardT120_53
      (fun i => conj_mem_of_fixedPoints _ _ (T120_53 i) (hfix120_53 i) _)
      ⟨120, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 15 hp) Q2.T120_53_2 Q2.hfix120_53_2 Q2.hinj120_53_2
      Q2.hcardT120_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_53_2 i) (Q2.hfix120_53_2 i) _)
      colCert_120_53_15.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_53_20 (hp : 20 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 20 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 20 (transLenTr ⟨53, by decide⟩ 20 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 20 (transLenTr ⟨53, by decide⟩ 20 hp)) T120_53
      hfix120_53 hinj120_53 hcardT120_53
      (fun i => conj_mem_of_fixedPoints _ _ (T120_53 i) (hfix120_53 i) _)
      ⟨120, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 20 hp) Q2.T120_53_2 Q2.hfix120_53_2 Q2.hinj120_53_2
      Q2.hcardT120_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_53_2 i) (Q2.hfix120_53_2 i) _)
      colCert_120_53_20.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_75_0 (hp : 0 < (Q2.transData.getD 75 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨75, by decide⟩ : Fin 148)) (colE2 ⟨75, by decide⟩ 0 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨75, by decide⟩ : Fin 148))
        (colE1 ⟨75, by decide⟩ 0 (transLenTr ⟨75, by decide⟩ 0 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨75, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨75, by decide⟩ 0 (transLenTr ⟨75, by decide⟩ 0 hp)) T120_75
      hfix120_75 hinj120_75 hcardT120_75
      (fun i => conj_mem_of_fixedPoints _ _ (T120_75 i) (hfix120_75 i) _)
      ⟨120, by decide⟩ ⟨75, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨75, by decide⟩ 0 hp) Q2.T120_75_2 Q2.hfix120_75_2 Q2.hinj120_75_2
      Q2.hcardT120_75_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_75_2 i) (Q2.hfix120_75_2 i) _)
      colCert_120_75_0.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_75_1 (hp : 1 < (Q2.transData.getD 75 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨75, by decide⟩ : Fin 148)) (colE2 ⟨75, by decide⟩ 1 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨75, by decide⟩ : Fin 148))
        (colE1 ⟨75, by decide⟩ 1 (transLenTr ⟨75, by decide⟩ 1 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨75, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨75, by decide⟩ 1 (transLenTr ⟨75, by decide⟩ 1 hp)) T120_75
      hfix120_75 hinj120_75 hcardT120_75
      (fun i => conj_mem_of_fixedPoints _ _ (T120_75 i) (hfix120_75 i) _)
      ⟨120, by decide⟩ ⟨75, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨75, by decide⟩ 1 hp) Q2.T120_75_2 Q2.hfix120_75_2 Q2.hinj120_75_2
      Q2.hcardT120_75_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_75_2 i) (Q2.hfix120_75_2 i) _)
      colCert_120_75_1.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_75_2 (hp : 2 < (Q2.transData.getD 75 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨75, by decide⟩ : Fin 148)) (colE2 ⟨75, by decide⟩ 2 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨75, by decide⟩ : Fin 148))
        (colE1 ⟨75, by decide⟩ 2 (transLenTr ⟨75, by decide⟩ 2 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨75, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨75, by decide⟩ 2 (transLenTr ⟨75, by decide⟩ 2 hp)) T120_75
      hfix120_75 hinj120_75 hcardT120_75
      (fun i => conj_mem_of_fixedPoints _ _ (T120_75 i) (hfix120_75 i) _)
      ⟨120, by decide⟩ ⟨75, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨75, by decide⟩ 2 hp) Q2.T120_75_2 Q2.hfix120_75_2 Q2.hinj120_75_2
      Q2.hcardT120_75_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_75_2 i) (Q2.hfix120_75_2 i) _)
      colCert_120_75_2.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_75_3 (hp : 3 < (Q2.transData.getD 75 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨75, by decide⟩ : Fin 148)) (colE2 ⟨75, by decide⟩ 3 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨75, by decide⟩ : Fin 148))
        (colE1 ⟨75, by decide⟩ 3 (transLenTr ⟨75, by decide⟩ 3 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨75, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨75, by decide⟩ 3 (transLenTr ⟨75, by decide⟩ 3 hp)) T120_75
      hfix120_75 hinj120_75 hcardT120_75
      (fun i => conj_mem_of_fixedPoints _ _ (T120_75 i) (hfix120_75 i) _)
      ⟨120, by decide⟩ ⟨75, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨75, by decide⟩ 3 hp) Q2.T120_75_2 Q2.hfix120_75_2 Q2.hinj120_75_2
      Q2.hcardT120_75_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_75_2 i) (Q2.hfix120_75_2 i) _)
      colCert_120_75_3.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_75_4 (hp : 4 < (Q2.transData.getD 75 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨75, by decide⟩ : Fin 148)) (colE2 ⟨75, by decide⟩ 4 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨75, by decide⟩ : Fin 148))
        (colE1 ⟨75, by decide⟩ 4 (transLenTr ⟨75, by decide⟩ 4 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨75, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨75, by decide⟩ 4 (transLenTr ⟨75, by decide⟩ 4 hp)) T120_75
      hfix120_75 hinj120_75 hcardT120_75
      (fun i => conj_mem_of_fixedPoints _ _ (T120_75 i) (hfix120_75 i) _)
      ⟨120, by decide⟩ ⟨75, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨75, by decide⟩ 4 hp) Q2.T120_75_2 Q2.hfix120_75_2 Q2.hinj120_75_2
      Q2.hcardT120_75_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_75_2 i) (Q2.hfix120_75_2 i) _)
      colCert_120_75_4.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_75_5 (hp : 5 < (Q2.transData.getD 75 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨75, by decide⟩ : Fin 148)) (colE2 ⟨75, by decide⟩ 5 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨75, by decide⟩ : Fin 148))
        (colE1 ⟨75, by decide⟩ 5 (transLenTr ⟨75, by decide⟩ 5 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨120, by decide⟩ : Fin 148) ⟨75, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨75, by decide⟩ 5 (transLenTr ⟨75, by decide⟩ 5 hp)) T120_75
      hfix120_75 hinj120_75 hcardT120_75
      (fun i => conj_mem_of_fixedPoints _ _ (T120_75 i) (hfix120_75 i) _)
      ⟨120, by decide⟩ ⟨75, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨75, by decide⟩ 5 hp) Q2.T120_75_2 Q2.hfix120_75_2 Q2.hinj120_75_2
      Q2.hcardT120_75_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_75_2 i) (Q2.hfix120_75_2 i) _)
      ?_).symm
  rw [show colData1 (⟨120, by decide⟩ : Fin 148)
        ((colE1 ⟨75, by decide⟩ 5 (transLenTr ⟨75, by decide⟩ 5 hp) : ↥(reps ⟨75, by decide⟩)) : Coordinate 1)
        T120_75 = colFn colCertDiv_120_75_5.D1 (m := 5) from colCertDiv_120_75_5.bind1,
    show colData2 (⟨120, by decide⟩ : Fin 148)
        ((colE2 ⟨75, by decide⟩ 5 hp : ↥(Q2.reps ⟨75, by decide⟩)) : Coordinate 2)
        Q2.T120_75_2 = colFn colCertDiv_120_75_5.D2 (m := 5) from colCertDiv_120_75_5.bind2]
  rw [alnId_120 j hj]
  exact fastcode_of_div ⟨120, by decide⟩ _ _ _
    ((alnId_120 j hj) ▸ Q2.listedAt (⟨120, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨120, by decide⟩ : Fin 148) hj hq).1) colCertDiv_120_75_5_match


theorem leaf_120_75_6 (hp : 6 < (Q2.transData.getD 75 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨75, by decide⟩ : Fin 148)) (colE2 ⟨75, by decide⟩ 6 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨75, by decide⟩ : Fin 148))
        (colE1 ⟨75, by decide⟩ 6 (transLenTr ⟨75, by decide⟩ 6 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨120, by decide⟩ : Fin 148) ⟨75, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨75, by decide⟩ 6 (transLenTr ⟨75, by decide⟩ 6 hp)) T120_75
      hfix120_75 hinj120_75 hcardT120_75
      (fun i => conj_mem_of_fixedPoints _ _ (T120_75 i) (hfix120_75 i) _)
      ⟨120, by decide⟩ ⟨75, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨75, by decide⟩ 6 hp) Q2.T120_75_2 Q2.hfix120_75_2 Q2.hinj120_75_2
      Q2.hcardT120_75_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_75_2 i) (Q2.hfix120_75_2 i) _)
      ?_).symm
  rw [show colData1 (⟨120, by decide⟩ : Fin 148)
        ((colE1 ⟨75, by decide⟩ 6 (transLenTr ⟨75, by decide⟩ 6 hp) : ↥(reps ⟨75, by decide⟩)) : Coordinate 1)
        T120_75 = colFn colCertDiv_120_75_6.D1 (m := 5) from colCertDiv_120_75_6.bind1,
    show colData2 (⟨120, by decide⟩ : Fin 148)
        ((colE2 ⟨75, by decide⟩ 6 hp : ↥(Q2.reps ⟨75, by decide⟩)) : Coordinate 2)
        Q2.T120_75_2 = colFn colCertDiv_120_75_6.D2 (m := 5) from colCertDiv_120_75_6.bind2]
  rw [alnId_120 j hj]
  exact fastcode_of_div ⟨120, by decide⟩ _ _ _
    ((alnId_120 j hj) ▸ Q2.listedAt (⟨120, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨120, by decide⟩ : Fin 148) hj hq).1) colCertDiv_120_75_6_match


theorem leaf_120_75_7 (hp : 7 < (Q2.transData.getD 75 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨75, by decide⟩ : Fin 148)) (colE2 ⟨75, by decide⟩ 7 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨75, by decide⟩ : Fin 148))
        (colE1 ⟨75, by decide⟩ 7 (transLenTr ⟨75, by decide⟩ 7 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨120, by decide⟩ : Fin 148) ⟨75, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨75, by decide⟩ 7 (transLenTr ⟨75, by decide⟩ 7 hp)) T120_75
      hfix120_75 hinj120_75 hcardT120_75
      (fun i => conj_mem_of_fixedPoints _ _ (T120_75 i) (hfix120_75 i) _)
      ⟨120, by decide⟩ ⟨75, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨75, by decide⟩ 7 hp) Q2.T120_75_2 Q2.hfix120_75_2 Q2.hinj120_75_2
      Q2.hcardT120_75_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_75_2 i) (Q2.hfix120_75_2 i) _)
      ?_).symm
  rw [show colData1 (⟨120, by decide⟩ : Fin 148)
        ((colE1 ⟨75, by decide⟩ 7 (transLenTr ⟨75, by decide⟩ 7 hp) : ↥(reps ⟨75, by decide⟩)) : Coordinate 1)
        T120_75 = colFn colCertDiv_120_75_7.D1 (m := 5) from colCertDiv_120_75_7.bind1,
    show colData2 (⟨120, by decide⟩ : Fin 148)
        ((colE2 ⟨75, by decide⟩ 7 hp : ↥(Q2.reps ⟨75, by decide⟩)) : Coordinate 2)
        Q2.T120_75_2 = colFn colCertDiv_120_75_7.D2 (m := 5) from colCertDiv_120_75_7.bind2]
  rw [alnId_120 j hj]
  exact fastcode_of_div ⟨120, by decide⟩ _ _ _
    ((alnId_120 j hj) ▸ Q2.listedAt (⟨120, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨120, by decide⟩ : Fin 148) hj hq).1) colCertDiv_120_75_7_match


theorem leaf_120_75_8 (hp : 8 < (Q2.transData.getD 75 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨75, by decide⟩ : Fin 148)) (colE2 ⟨75, by decide⟩ 8 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨75, by decide⟩ : Fin 148))
        (colE1 ⟨75, by decide⟩ 8 (transLenTr ⟨75, by decide⟩ 8 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨120, by decide⟩ : Fin 148) ⟨75, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨75, by decide⟩ 8 (transLenTr ⟨75, by decide⟩ 8 hp)) T120_75
      hfix120_75 hinj120_75 hcardT120_75
      (fun i => conj_mem_of_fixedPoints _ _ (T120_75 i) (hfix120_75 i) _)
      ⟨120, by decide⟩ ⟨75, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨75, by decide⟩ 8 hp) Q2.T120_75_2 Q2.hfix120_75_2 Q2.hinj120_75_2
      Q2.hcardT120_75_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_75_2 i) (Q2.hfix120_75_2 i) _)
      ?_).symm
  rw [show colData1 (⟨120, by decide⟩ : Fin 148)
        ((colE1 ⟨75, by decide⟩ 8 (transLenTr ⟨75, by decide⟩ 8 hp) : ↥(reps ⟨75, by decide⟩)) : Coordinate 1)
        T120_75 = colFn colCertDiv_120_75_8.D1 (m := 5) from colCertDiv_120_75_8.bind1,
    show colData2 (⟨120, by decide⟩ : Fin 148)
        ((colE2 ⟨75, by decide⟩ 8 hp : ↥(Q2.reps ⟨75, by decide⟩)) : Coordinate 2)
        Q2.T120_75_2 = colFn colCertDiv_120_75_8.D2 (m := 5) from colCertDiv_120_75_8.bind2]
  rw [alnId_120 j hj]
  exact fastcode_of_div ⟨120, by decide⟩ _ _ _
    ((alnId_120 j hj) ▸ Q2.listedAt (⟨120, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨120, by decide⟩ : Fin 148) hj hq).1) colCertDiv_120_75_8_match


theorem leaf_120_75_9 (hp : 9 < (Q2.transData.getD 75 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨75, by decide⟩ : Fin 148)) (colE2 ⟨75, by decide⟩ 9 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨75, by decide⟩ : Fin 148))
        (colE1 ⟨75, by decide⟩ 9 (transLenTr ⟨75, by decide⟩ 9 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨120, by decide⟩ : Fin 148) ⟨75, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨75, by decide⟩ 9 (transLenTr ⟨75, by decide⟩ 9 hp)) T120_75
      hfix120_75 hinj120_75 hcardT120_75
      (fun i => conj_mem_of_fixedPoints _ _ (T120_75 i) (hfix120_75 i) _)
      ⟨120, by decide⟩ ⟨75, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨75, by decide⟩ 9 hp) Q2.T120_75_2 Q2.hfix120_75_2 Q2.hinj120_75_2
      Q2.hcardT120_75_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_75_2 i) (Q2.hfix120_75_2 i) _)
      ?_).symm
  rw [show colData1 (⟨120, by decide⟩ : Fin 148)
        ((colE1 ⟨75, by decide⟩ 9 (transLenTr ⟨75, by decide⟩ 9 hp) : ↥(reps ⟨75, by decide⟩)) : Coordinate 1)
        T120_75 = colFn colCertDiv_120_75_9.D1 (m := 5) from colCertDiv_120_75_9.bind1,
    show colData2 (⟨120, by decide⟩ : Fin 148)
        ((colE2 ⟨75, by decide⟩ 9 hp : ↥(Q2.reps ⟨75, by decide⟩)) : Coordinate 2)
        Q2.T120_75_2 = colFn colCertDiv_120_75_9.D2 (m := 5) from colCertDiv_120_75_9.bind2]
  rw [alnId_120 j hj]
  exact fastcode_of_div ⟨120, by decide⟩ _ _ _
    ((alnId_120 j hj) ▸ Q2.listedAt (⟨120, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨120, by decide⟩ : Fin 148) hj hq).1) colCertDiv_120_75_9_match


theorem leaf_120_75_10 (hp : 10 < (Q2.transData.getD 75 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨75, by decide⟩ : Fin 148)) (colE2 ⟨75, by decide⟩ 10 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨75, by decide⟩ : Fin 148))
        (colE1 ⟨75, by decide⟩ 10 (transLenTr ⟨75, by decide⟩ 10 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨120, by decide⟩ : Fin 148) ⟨75, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨75, by decide⟩ 10 (transLenTr ⟨75, by decide⟩ 10 hp)) T120_75
      hfix120_75 hinj120_75 hcardT120_75
      (fun i => conj_mem_of_fixedPoints _ _ (T120_75 i) (hfix120_75 i) _)
      ⟨120, by decide⟩ ⟨75, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨75, by decide⟩ 10 hp) Q2.T120_75_2 Q2.hfix120_75_2 Q2.hinj120_75_2
      Q2.hcardT120_75_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_75_2 i) (Q2.hfix120_75_2 i) _)
      ?_).symm
  rw [show colData1 (⟨120, by decide⟩ : Fin 148)
        ((colE1 ⟨75, by decide⟩ 10 (transLenTr ⟨75, by decide⟩ 10 hp) : ↥(reps ⟨75, by decide⟩)) : Coordinate 1)
        T120_75 = colFn colCertDiv_120_75_10.D1 (m := 5) from colCertDiv_120_75_10.bind1,
    show colData2 (⟨120, by decide⟩ : Fin 148)
        ((colE2 ⟨75, by decide⟩ 10 hp : ↥(Q2.reps ⟨75, by decide⟩)) : Coordinate 2)
        Q2.T120_75_2 = colFn colCertDiv_120_75_10.D2 (m := 5) from colCertDiv_120_75_10.bind2]
  rw [alnId_120 j hj]
  exact fastcode_of_div ⟨120, by decide⟩ _ _ _
    ((alnId_120 j hj) ▸ Q2.listedAt (⟨120, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨120, by decide⟩ : Fin 148) hj hq).1) colCertDiv_120_75_10_match


theorem leaf_120_75_11 (hp : 11 < (Q2.transData.getD 75 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨75, by decide⟩ : Fin 148)) (colE2 ⟨75, by decide⟩ 11 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨75, by decide⟩ : Fin 148))
        (colE1 ⟨75, by decide⟩ 11 (transLenTr ⟨75, by decide⟩ 11 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨120, by decide⟩ : Fin 148) ⟨75, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨75, by decide⟩ 11 (transLenTr ⟨75, by decide⟩ 11 hp)) T120_75
      hfix120_75 hinj120_75 hcardT120_75
      (fun i => conj_mem_of_fixedPoints _ _ (T120_75 i) (hfix120_75 i) _)
      ⟨120, by decide⟩ ⟨75, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨75, by decide⟩ 11 hp) Q2.T120_75_2 Q2.hfix120_75_2 Q2.hinj120_75_2
      Q2.hcardT120_75_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_75_2 i) (Q2.hfix120_75_2 i) _)
      ?_).symm
  rw [show colData1 (⟨120, by decide⟩ : Fin 148)
        ((colE1 ⟨75, by decide⟩ 11 (transLenTr ⟨75, by decide⟩ 11 hp) : ↥(reps ⟨75, by decide⟩)) : Coordinate 1)
        T120_75 = colFn colCertDiv_120_75_11.D1 (m := 5) from colCertDiv_120_75_11.bind1,
    show colData2 (⟨120, by decide⟩ : Fin 148)
        ((colE2 ⟨75, by decide⟩ 11 hp : ↥(Q2.reps ⟨75, by decide⟩)) : Coordinate 2)
        Q2.T120_75_2 = colFn colCertDiv_120_75_11.D2 (m := 5) from colCertDiv_120_75_11.bind2]
  rw [alnId_120 j hj]
  exact fastcode_of_div ⟨120, by decide⟩ _ _ _
    ((alnId_120 j hj) ▸ Q2.listedAt (⟨120, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨120, by decide⟩ : Fin 148) hj hq).1) colCertDiv_120_75_11_match


theorem leaf_120_75_12 (hp : 12 < (Q2.transData.getD 75 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨75, by decide⟩ : Fin 148)) (colE2 ⟨75, by decide⟩ 12 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨75, by decide⟩ : Fin 148))
        (colE1 ⟨75, by decide⟩ 12 (transLenTr ⟨75, by decide⟩ 12 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨120, by decide⟩ : Fin 148) ⟨75, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨75, by decide⟩ 12 (transLenTr ⟨75, by decide⟩ 12 hp)) T120_75
      hfix120_75 hinj120_75 hcardT120_75
      (fun i => conj_mem_of_fixedPoints _ _ (T120_75 i) (hfix120_75 i) _)
      ⟨120, by decide⟩ ⟨75, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨75, by decide⟩ 12 hp) Q2.T120_75_2 Q2.hfix120_75_2 Q2.hinj120_75_2
      Q2.hcardT120_75_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_75_2 i) (Q2.hfix120_75_2 i) _)
      ?_).symm
  rw [show colData1 (⟨120, by decide⟩ : Fin 148)
        ((colE1 ⟨75, by decide⟩ 12 (transLenTr ⟨75, by decide⟩ 12 hp) : ↥(reps ⟨75, by decide⟩)) : Coordinate 1)
        T120_75 = colFn colCertDiv_120_75_12.D1 (m := 5) from colCertDiv_120_75_12.bind1,
    show colData2 (⟨120, by decide⟩ : Fin 148)
        ((colE2 ⟨75, by decide⟩ 12 hp : ↥(Q2.reps ⟨75, by decide⟩)) : Coordinate 2)
        Q2.T120_75_2 = colFn colCertDiv_120_75_12.D2 (m := 5) from colCertDiv_120_75_12.bind2]
  rw [alnId_120 j hj]
  exact fastcode_of_div ⟨120, by decide⟩ _ _ _
    ((alnId_120 j hj) ▸ Q2.listedAt (⟨120, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨120, by decide⟩ : Fin 148) hj hq).1) colCertDiv_120_75_12_match


theorem leaf_120_75_13 (hp : 13 < (Q2.transData.getD 75 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨75, by decide⟩ : Fin 148)) (colE2 ⟨75, by decide⟩ 13 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨75, by decide⟩ : Fin 148))
        (colE1 ⟨75, by decide⟩ 13 (transLenTr ⟨75, by decide⟩ 13 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨120, by decide⟩ : Fin 148) ⟨75, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨75, by decide⟩ 13 (transLenTr ⟨75, by decide⟩ 13 hp)) T120_75
      hfix120_75 hinj120_75 hcardT120_75
      (fun i => conj_mem_of_fixedPoints _ _ (T120_75 i) (hfix120_75 i) _)
      ⟨120, by decide⟩ ⟨75, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨75, by decide⟩ 13 hp) Q2.T120_75_2 Q2.hfix120_75_2 Q2.hinj120_75_2
      Q2.hcardT120_75_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_75_2 i) (Q2.hfix120_75_2 i) _)
      ?_).symm
  rw [show colData1 (⟨120, by decide⟩ : Fin 148)
        ((colE1 ⟨75, by decide⟩ 13 (transLenTr ⟨75, by decide⟩ 13 hp) : ↥(reps ⟨75, by decide⟩)) : Coordinate 1)
        T120_75 = colFn colCertDiv_120_75_13.D1 (m := 5) from colCertDiv_120_75_13.bind1,
    show colData2 (⟨120, by decide⟩ : Fin 148)
        ((colE2 ⟨75, by decide⟩ 13 hp : ↥(Q2.reps ⟨75, by decide⟩)) : Coordinate 2)
        Q2.T120_75_2 = colFn colCertDiv_120_75_13.D2 (m := 5) from colCertDiv_120_75_13.bind2]
  rw [alnId_120 j hj]
  exact fastcode_of_div ⟨120, by decide⟩ _ _ _
    ((alnId_120 j hj) ▸ Q2.listedAt (⟨120, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨120, by decide⟩ : Fin 148) hj hq).1) colCertDiv_120_75_13_match


theorem leaf_120_75_14 (hp : 14 < (Q2.transData.getD 75 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨75, by decide⟩ : Fin 148)) (colE2 ⟨75, by decide⟩ 14 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨75, by decide⟩ : Fin 148))
        (colE1 ⟨75, by decide⟩ 14 (transLenTr ⟨75, by decide⟩ 14 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨120, by decide⟩ : Fin 148) ⟨75, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨75, by decide⟩ 14 (transLenTr ⟨75, by decide⟩ 14 hp)) T120_75
      hfix120_75 hinj120_75 hcardT120_75
      (fun i => conj_mem_of_fixedPoints _ _ (T120_75 i) (hfix120_75 i) _)
      ⟨120, by decide⟩ ⟨75, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨75, by decide⟩ 14 hp) Q2.T120_75_2 Q2.hfix120_75_2 Q2.hinj120_75_2
      Q2.hcardT120_75_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_75_2 i) (Q2.hfix120_75_2 i) _)
      ?_).symm
  rw [show colData1 (⟨120, by decide⟩ : Fin 148)
        ((colE1 ⟨75, by decide⟩ 14 (transLenTr ⟨75, by decide⟩ 14 hp) : ↥(reps ⟨75, by decide⟩)) : Coordinate 1)
        T120_75 = colFn colCertDiv_120_75_14.D1 (m := 5) from colCertDiv_120_75_14.bind1,
    show colData2 (⟨120, by decide⟩ : Fin 148)
        ((colE2 ⟨75, by decide⟩ 14 hp : ↥(Q2.reps ⟨75, by decide⟩)) : Coordinate 2)
        Q2.T120_75_2 = colFn colCertDiv_120_75_14.D2 (m := 5) from colCertDiv_120_75_14.bind2]
  rw [alnId_120 j hj]
  exact fastcode_of_div ⟨120, by decide⟩ _ _ _
    ((alnId_120 j hj) ▸ Q2.listedAt (⟨120, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨120, by decide⟩ : Fin 148) hj hq).1) colCertDiv_120_75_14_match


theorem leaf_120_75_15 (hp : 15 < (Q2.transData.getD 75 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨75, by decide⟩ : Fin 148)) (colE2 ⟨75, by decide⟩ 15 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨75, by decide⟩ : Fin 148))
        (colE1 ⟨75, by decide⟩ 15 (transLenTr ⟨75, by decide⟩ 15 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨120, by decide⟩ : Fin 148) ⟨75, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨75, by decide⟩ 15 (transLenTr ⟨75, by decide⟩ 15 hp)) T120_75
      hfix120_75 hinj120_75 hcardT120_75
      (fun i => conj_mem_of_fixedPoints _ _ (T120_75 i) (hfix120_75 i) _)
      ⟨120, by decide⟩ ⟨75, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨75, by decide⟩ 15 hp) Q2.T120_75_2 Q2.hfix120_75_2 Q2.hinj120_75_2
      Q2.hcardT120_75_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_75_2 i) (Q2.hfix120_75_2 i) _)
      ?_).symm
  rw [show colData1 (⟨120, by decide⟩ : Fin 148)
        ((colE1 ⟨75, by decide⟩ 15 (transLenTr ⟨75, by decide⟩ 15 hp) : ↥(reps ⟨75, by decide⟩)) : Coordinate 1)
        T120_75 = colFn colCertDiv_120_75_15.D1 (m := 5) from colCertDiv_120_75_15.bind1,
    show colData2 (⟨120, by decide⟩ : Fin 148)
        ((colE2 ⟨75, by decide⟩ 15 hp : ↥(Q2.reps ⟨75, by decide⟩)) : Coordinate 2)
        Q2.T120_75_2 = colFn colCertDiv_120_75_15.D2 (m := 5) from colCertDiv_120_75_15.bind2]
  rw [alnId_120 j hj]
  exact fastcode_of_div ⟨120, by decide⟩ _ _ _
    ((alnId_120 j hj) ▸ Q2.listedAt (⟨120, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨120, by decide⟩ : Fin 148) hj hq).1) colCertDiv_120_75_15_match


theorem leaf_120_75_16 (hp : 16 < (Q2.transData.getD 75 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨75, by decide⟩ : Fin 148)) (colE2 ⟨75, by decide⟩ 16 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨75, by decide⟩ : Fin 148))
        (colE1 ⟨75, by decide⟩ 16 (transLenTr ⟨75, by decide⟩ 16 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨120, by decide⟩ : Fin 148) ⟨75, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨75, by decide⟩ 16 (transLenTr ⟨75, by decide⟩ 16 hp)) T120_75
      hfix120_75 hinj120_75 hcardT120_75
      (fun i => conj_mem_of_fixedPoints _ _ (T120_75 i) (hfix120_75 i) _)
      ⟨120, by decide⟩ ⟨75, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨75, by decide⟩ 16 hp) Q2.T120_75_2 Q2.hfix120_75_2 Q2.hinj120_75_2
      Q2.hcardT120_75_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_75_2 i) (Q2.hfix120_75_2 i) _)
      ?_).symm
  rw [show colData1 (⟨120, by decide⟩ : Fin 148)
        ((colE1 ⟨75, by decide⟩ 16 (transLenTr ⟨75, by decide⟩ 16 hp) : ↥(reps ⟨75, by decide⟩)) : Coordinate 1)
        T120_75 = colFn colCertDiv_120_75_16.D1 (m := 5) from colCertDiv_120_75_16.bind1,
    show colData2 (⟨120, by decide⟩ : Fin 148)
        ((colE2 ⟨75, by decide⟩ 16 hp : ↥(Q2.reps ⟨75, by decide⟩)) : Coordinate 2)
        Q2.T120_75_2 = colFn colCertDiv_120_75_16.D2 (m := 5) from colCertDiv_120_75_16.bind2]
  rw [alnId_120 j hj]
  exact fastcode_of_div ⟨120, by decide⟩ _ _ _
    ((alnId_120 j hj) ▸ Q2.listedAt (⟨120, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨120, by decide⟩ : Fin 148) hj hq).1) colCertDiv_120_75_16_match


theorem leaf_120_75_17 (hp : 17 < (Q2.transData.getD 75 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨75, by decide⟩ : Fin 148)) (colE2 ⟨75, by decide⟩ 17 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨75, by decide⟩ : Fin 148))
        (colE1 ⟨75, by decide⟩ 17 (transLenTr ⟨75, by decide⟩ 17 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨120, by decide⟩ : Fin 148) ⟨75, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨75, by decide⟩ 17 (transLenTr ⟨75, by decide⟩ 17 hp)) T120_75
      hfix120_75 hinj120_75 hcardT120_75
      (fun i => conj_mem_of_fixedPoints _ _ (T120_75 i) (hfix120_75 i) _)
      ⟨120, by decide⟩ ⟨75, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨75, by decide⟩ 17 hp) Q2.T120_75_2 Q2.hfix120_75_2 Q2.hinj120_75_2
      Q2.hcardT120_75_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_75_2 i) (Q2.hfix120_75_2 i) _)
      ?_).symm
  rw [show colData1 (⟨120, by decide⟩ : Fin 148)
        ((colE1 ⟨75, by decide⟩ 17 (transLenTr ⟨75, by decide⟩ 17 hp) : ↥(reps ⟨75, by decide⟩)) : Coordinate 1)
        T120_75 = colFn colCertDiv_120_75_17.D1 (m := 5) from colCertDiv_120_75_17.bind1,
    show colData2 (⟨120, by decide⟩ : Fin 148)
        ((colE2 ⟨75, by decide⟩ 17 hp : ↥(Q2.reps ⟨75, by decide⟩)) : Coordinate 2)
        Q2.T120_75_2 = colFn colCertDiv_120_75_17.D2 (m := 5) from colCertDiv_120_75_17.bind2]
  rw [alnId_120 j hj]
  exact fastcode_of_div ⟨120, by decide⟩ _ _ _
    ((alnId_120 j hj) ▸ Q2.listedAt (⟨120, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨120, by decide⟩ : Fin 148) hj hq).1) colCertDiv_120_75_17_match


theorem leaf_120_75_18 (hp : 18 < (Q2.transData.getD 75 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨75, by decide⟩ : Fin 148)) (colE2 ⟨75, by decide⟩ 18 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨75, by decide⟩ : Fin 148))
        (colE1 ⟨75, by decide⟩ 18 (transLenTr ⟨75, by decide⟩ 18 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨120, by decide⟩ : Fin 148) ⟨75, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨75, by decide⟩ 18 (transLenTr ⟨75, by decide⟩ 18 hp)) T120_75
      hfix120_75 hinj120_75 hcardT120_75
      (fun i => conj_mem_of_fixedPoints _ _ (T120_75 i) (hfix120_75 i) _)
      ⟨120, by decide⟩ ⟨75, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨75, by decide⟩ 18 hp) Q2.T120_75_2 Q2.hfix120_75_2 Q2.hinj120_75_2
      Q2.hcardT120_75_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_75_2 i) (Q2.hfix120_75_2 i) _)
      ?_).symm
  rw [show colData1 (⟨120, by decide⟩ : Fin 148)
        ((colE1 ⟨75, by decide⟩ 18 (transLenTr ⟨75, by decide⟩ 18 hp) : ↥(reps ⟨75, by decide⟩)) : Coordinate 1)
        T120_75 = colFn colCertDiv_120_75_18.D1 (m := 5) from colCertDiv_120_75_18.bind1,
    show colData2 (⟨120, by decide⟩ : Fin 148)
        ((colE2 ⟨75, by decide⟩ 18 hp : ↥(Q2.reps ⟨75, by decide⟩)) : Coordinate 2)
        Q2.T120_75_2 = colFn colCertDiv_120_75_18.D2 (m := 5) from colCertDiv_120_75_18.bind2]
  rw [alnId_120 j hj]
  exact fastcode_of_div ⟨120, by decide⟩ _ _ _
    ((alnId_120 j hj) ▸ Q2.listedAt (⟨120, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨120, by decide⟩ : Fin 148) hj hq).1) colCertDiv_120_75_18_match


theorem leaf_120_75_19 (hp : 19 < (Q2.transData.getD 75 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨75, by decide⟩ : Fin 148)) (colE2 ⟨75, by decide⟩ 19 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨75, by decide⟩ : Fin 148))
        (colE1 ⟨75, by decide⟩ 19 (transLenTr ⟨75, by decide⟩ 19 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨120, by decide⟩ : Fin 148) ⟨75, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨75, by decide⟩ 19 (transLenTr ⟨75, by decide⟩ 19 hp)) T120_75
      hfix120_75 hinj120_75 hcardT120_75
      (fun i => conj_mem_of_fixedPoints _ _ (T120_75 i) (hfix120_75 i) _)
      ⟨120, by decide⟩ ⟨75, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨75, by decide⟩ 19 hp) Q2.T120_75_2 Q2.hfix120_75_2 Q2.hinj120_75_2
      Q2.hcardT120_75_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_75_2 i) (Q2.hfix120_75_2 i) _)
      ?_).symm
  rw [show colData1 (⟨120, by decide⟩ : Fin 148)
        ((colE1 ⟨75, by decide⟩ 19 (transLenTr ⟨75, by decide⟩ 19 hp) : ↥(reps ⟨75, by decide⟩)) : Coordinate 1)
        T120_75 = colFn colCertDiv_120_75_19.D1 (m := 5) from colCertDiv_120_75_19.bind1,
    show colData2 (⟨120, by decide⟩ : Fin 148)
        ((colE2 ⟨75, by decide⟩ 19 hp : ↥(Q2.reps ⟨75, by decide⟩)) : Coordinate 2)
        Q2.T120_75_2 = colFn colCertDiv_120_75_19.D2 (m := 5) from colCertDiv_120_75_19.bind2]
  rw [alnId_120 j hj]
  exact fastcode_of_div ⟨120, by decide⟩ _ _ _
    ((alnId_120 j hj) ▸ Q2.listedAt (⟨120, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨120, by decide⟩ : Fin 148) hj hq).1) colCertDiv_120_75_19_match


theorem leaf_120_75_20 (hp : 20 < (Q2.transData.getD 75 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨75, by decide⟩ : Fin 148)) (colE2 ⟨75, by decide⟩ 20 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨75, by decide⟩ : Fin 148))
        (colE1 ⟨75, by decide⟩ 20 (transLenTr ⟨75, by decide⟩ 20 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨120, by decide⟩ : Fin 148) ⟨75, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨75, by decide⟩ 20 (transLenTr ⟨75, by decide⟩ 20 hp)) T120_75
      hfix120_75 hinj120_75 hcardT120_75
      (fun i => conj_mem_of_fixedPoints _ _ (T120_75 i) (hfix120_75 i) _)
      ⟨120, by decide⟩ ⟨75, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨75, by decide⟩ 20 hp) Q2.T120_75_2 Q2.hfix120_75_2 Q2.hinj120_75_2
      Q2.hcardT120_75_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_75_2 i) (Q2.hfix120_75_2 i) _)
      ?_).symm
  rw [show colData1 (⟨120, by decide⟩ : Fin 148)
        ((colE1 ⟨75, by decide⟩ 20 (transLenTr ⟨75, by decide⟩ 20 hp) : ↥(reps ⟨75, by decide⟩)) : Coordinate 1)
        T120_75 = colFn colCertDiv_120_75_20.D1 (m := 5) from colCertDiv_120_75_20.bind1,
    show colData2 (⟨120, by decide⟩ : Fin 148)
        ((colE2 ⟨75, by decide⟩ 20 hp : ↥(Q2.reps ⟨75, by decide⟩)) : Coordinate 2)
        Q2.T120_75_2 = colFn colCertDiv_120_75_20.D2 (m := 5) from colCertDiv_120_75_20.bind2]
  rw [alnId_120 j hj]
  exact fastcode_of_div ⟨120, by decide⟩ _ _ _
    ((alnId_120 j hj) ▸ Q2.listedAt (⟨120, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨120, by decide⟩ : Fin 148) hj hq).1) colCertDiv_120_75_20_match


theorem leaf_120_75_21 (hp : 21 < (Q2.transData.getD 75 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨75, by decide⟩ : Fin 148)) (colE2 ⟨75, by decide⟩ 21 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨75, by decide⟩ : Fin 148))
        (colE1 ⟨75, by decide⟩ 21 (transLenTr ⟨75, by decide⟩ 21 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨120, by decide⟩ : Fin 148) ⟨75, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨75, by decide⟩ 21 (transLenTr ⟨75, by decide⟩ 21 hp)) T120_75
      hfix120_75 hinj120_75 hcardT120_75
      (fun i => conj_mem_of_fixedPoints _ _ (T120_75 i) (hfix120_75 i) _)
      ⟨120, by decide⟩ ⟨75, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨75, by decide⟩ 21 hp) Q2.T120_75_2 Q2.hfix120_75_2 Q2.hinj120_75_2
      Q2.hcardT120_75_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_75_2 i) (Q2.hfix120_75_2 i) _)
      ?_).symm
  rw [show colData1 (⟨120, by decide⟩ : Fin 148)
        ((colE1 ⟨75, by decide⟩ 21 (transLenTr ⟨75, by decide⟩ 21 hp) : ↥(reps ⟨75, by decide⟩)) : Coordinate 1)
        T120_75 = colFn colCertDiv_120_75_21.D1 (m := 5) from colCertDiv_120_75_21.bind1,
    show colData2 (⟨120, by decide⟩ : Fin 148)
        ((colE2 ⟨75, by decide⟩ 21 hp : ↥(Q2.reps ⟨75, by decide⟩)) : Coordinate 2)
        Q2.T120_75_2 = colFn colCertDiv_120_75_21.D2 (m := 5) from colCertDiv_120_75_21.bind2]
  rw [alnId_120 j hj]
  exact fastcode_of_div ⟨120, by decide⟩ _ _ _
    ((alnId_120 j hj) ▸ Q2.listedAt (⟨120, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨120, by decide⟩ : Fin 148) hj hq).1) colCertDiv_120_75_21_match


theorem leaf_120_75_22 (hp : 22 < (Q2.transData.getD 75 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨75, by decide⟩ : Fin 148)) (colE2 ⟨75, by decide⟩ 22 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨75, by decide⟩ : Fin 148))
        (colE1 ⟨75, by decide⟩ 22 (transLenTr ⟨75, by decide⟩ 22 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨120, by decide⟩ : Fin 148) ⟨75, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨75, by decide⟩ 22 (transLenTr ⟨75, by decide⟩ 22 hp)) T120_75
      hfix120_75 hinj120_75 hcardT120_75
      (fun i => conj_mem_of_fixedPoints _ _ (T120_75 i) (hfix120_75 i) _)
      ⟨120, by decide⟩ ⟨75, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨75, by decide⟩ 22 hp) Q2.T120_75_2 Q2.hfix120_75_2 Q2.hinj120_75_2
      Q2.hcardT120_75_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_75_2 i) (Q2.hfix120_75_2 i) _)
      ?_).symm
  rw [show colData1 (⟨120, by decide⟩ : Fin 148)
        ((colE1 ⟨75, by decide⟩ 22 (transLenTr ⟨75, by decide⟩ 22 hp) : ↥(reps ⟨75, by decide⟩)) : Coordinate 1)
        T120_75 = colFn colCertDiv_120_75_22.D1 (m := 5) from colCertDiv_120_75_22.bind1,
    show colData2 (⟨120, by decide⟩ : Fin 148)
        ((colE2 ⟨75, by decide⟩ 22 hp : ↥(Q2.reps ⟨75, by decide⟩)) : Coordinate 2)
        Q2.T120_75_2 = colFn colCertDiv_120_75_22.D2 (m := 5) from colCertDiv_120_75_22.bind2]
  rw [alnId_120 j hj]
  exact fastcode_of_div ⟨120, by decide⟩ _ _ _
    ((alnId_120 j hj) ▸ Q2.listedAt (⟨120, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨120, by decide⟩ : Fin 148) hj hq).1) colCertDiv_120_75_22_match


theorem leaf_120_75_23 (hp : 23 < (Q2.transData.getD 75 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨75, by decide⟩ : Fin 148)) (colE2 ⟨75, by decide⟩ 23 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨75, by decide⟩ : Fin 148))
        (colE1 ⟨75, by decide⟩ 23 (transLenTr ⟨75, by decide⟩ 23 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨120, by decide⟩ : Fin 148) ⟨75, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨75, by decide⟩ 23 (transLenTr ⟨75, by decide⟩ 23 hp)) T120_75
      hfix120_75 hinj120_75 hcardT120_75
      (fun i => conj_mem_of_fixedPoints _ _ (T120_75 i) (hfix120_75 i) _)
      ⟨120, by decide⟩ ⟨75, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨75, by decide⟩ 23 hp) Q2.T120_75_2 Q2.hfix120_75_2 Q2.hinj120_75_2
      Q2.hcardT120_75_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_75_2 i) (Q2.hfix120_75_2 i) _)
      ?_).symm
  rw [show colData1 (⟨120, by decide⟩ : Fin 148)
        ((colE1 ⟨75, by decide⟩ 23 (transLenTr ⟨75, by decide⟩ 23 hp) : ↥(reps ⟨75, by decide⟩)) : Coordinate 1)
        T120_75 = colFn colCertDiv_120_75_23.D1 (m := 5) from colCertDiv_120_75_23.bind1,
    show colData2 (⟨120, by decide⟩ : Fin 148)
        ((colE2 ⟨75, by decide⟩ 23 hp : ↥(Q2.reps ⟨75, by decide⟩)) : Coordinate 2)
        Q2.T120_75_2 = colFn colCertDiv_120_75_23.D2 (m := 5) from colCertDiv_120_75_23.bind2]
  rw [alnId_120 j hj]
  exact fastcode_of_div ⟨120, by decide⟩ _ _ _
    ((alnId_120 j hj) ▸ Q2.listedAt (⟨120, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨120, by decide⟩ : Fin 148) hj hq).1) colCertDiv_120_75_23_match


theorem leaf_120_75_24 (hp : 24 < (Q2.transData.getD 75 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨75, by decide⟩ : Fin 148)) (colE2 ⟨75, by decide⟩ 24 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨75, by decide⟩ : Fin 148))
        (colE1 ⟨75, by decide⟩ 24 (transLenTr ⟨75, by decide⟩ 24 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨120, by decide⟩ : Fin 148) ⟨75, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨75, by decide⟩ 24 (transLenTr ⟨75, by decide⟩ 24 hp)) T120_75
      hfix120_75 hinj120_75 hcardT120_75
      (fun i => conj_mem_of_fixedPoints _ _ (T120_75 i) (hfix120_75 i) _)
      ⟨120, by decide⟩ ⟨75, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨75, by decide⟩ 24 hp) Q2.T120_75_2 Q2.hfix120_75_2 Q2.hinj120_75_2
      Q2.hcardT120_75_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_75_2 i) (Q2.hfix120_75_2 i) _)
      ?_).symm
  rw [show colData1 (⟨120, by decide⟩ : Fin 148)
        ((colE1 ⟨75, by decide⟩ 24 (transLenTr ⟨75, by decide⟩ 24 hp) : ↥(reps ⟨75, by decide⟩)) : Coordinate 1)
        T120_75 = colFn colCertDiv_120_75_24.D1 (m := 5) from colCertDiv_120_75_24.bind1,
    show colData2 (⟨120, by decide⟩ : Fin 148)
        ((colE2 ⟨75, by decide⟩ 24 hp : ↥(Q2.reps ⟨75, by decide⟩)) : Coordinate 2)
        Q2.T120_75_2 = colFn colCertDiv_120_75_24.D2 (m := 5) from colCertDiv_120_75_24.bind2]
  rw [alnId_120 j hj]
  exact fastcode_of_div ⟨120, by decide⟩ _ _ _
    ((alnId_120 j hj) ▸ Q2.listedAt (⟨120, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨120, by decide⟩ : Fin 148) hj hq).1) colCertDiv_120_75_24_match


theorem leaf_120_76_0 (hp : 0 < (Q2.transData.getD 76 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨76, by decide⟩ : Fin 148)) (colE2 ⟨76, by decide⟩ 0 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨76, by decide⟩ : Fin 148))
        (colE1 ⟨76, by decide⟩ 0 (transLenTr ⟨76, by decide⟩ 0 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨76, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨76, by decide⟩ 0 (transLenTr ⟨76, by decide⟩ 0 hp)) T120_76
      hfix120_76 hinj120_76 hcardT120_76
      (fun i => conj_mem_of_fixedPoints _ _ (T120_76 i) (hfix120_76 i) _)
      ⟨120, by decide⟩ ⟨76, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨76, by decide⟩ 0 hp) Q2.T120_76_2 Q2.hfix120_76_2 Q2.hinj120_76_2
      Q2.hcardT120_76_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_76_2 i) (Q2.hfix120_76_2 i) _)
      colCert_120_76_0.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_76_1 (hp : 1 < (Q2.transData.getD 76 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨76, by decide⟩ : Fin 148)) (colE2 ⟨76, by decide⟩ 1 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨76, by decide⟩ : Fin 148))
        (colE1 ⟨76, by decide⟩ 1 (transLenTr ⟨76, by decide⟩ 1 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨76, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨76, by decide⟩ 1 (transLenTr ⟨76, by decide⟩ 1 hp)) T120_76
      hfix120_76 hinj120_76 hcardT120_76
      (fun i => conj_mem_of_fixedPoints _ _ (T120_76 i) (hfix120_76 i) _)
      ⟨120, by decide⟩ ⟨76, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨76, by decide⟩ 1 hp) Q2.T120_76_2 Q2.hfix120_76_2 Q2.hinj120_76_2
      Q2.hcardT120_76_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_76_2 i) (Q2.hfix120_76_2 i) _)
      colCert_120_76_1.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_76_2 (hp : 2 < (Q2.transData.getD 76 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨76, by decide⟩ : Fin 148)) (colE2 ⟨76, by decide⟩ 2 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨76, by decide⟩ : Fin 148))
        (colE1 ⟨76, by decide⟩ 2 (transLenTr ⟨76, by decide⟩ 2 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨76, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨76, by decide⟩ 2 (transLenTr ⟨76, by decide⟩ 2 hp)) T120_76
      hfix120_76 hinj120_76 hcardT120_76
      (fun i => conj_mem_of_fixedPoints _ _ (T120_76 i) (hfix120_76 i) _)
      ⟨120, by decide⟩ ⟨76, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨76, by decide⟩ 2 hp) Q2.T120_76_2 Q2.hfix120_76_2 Q2.hinj120_76_2
      Q2.hcardT120_76_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_76_2 i) (Q2.hfix120_76_2 i) _)
      colCert_120_76_2.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_76_3 (hp : 3 < (Q2.transData.getD 76 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨76, by decide⟩ : Fin 148)) (colE2 ⟨76, by decide⟩ 3 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨76, by decide⟩ : Fin 148))
        (colE1 ⟨76, by decide⟩ 3 (transLenTr ⟨76, by decide⟩ 3 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨76, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨76, by decide⟩ 3 (transLenTr ⟨76, by decide⟩ 3 hp)) T120_76
      hfix120_76 hinj120_76 hcardT120_76
      (fun i => conj_mem_of_fixedPoints _ _ (T120_76 i) (hfix120_76 i) _)
      ⟨120, by decide⟩ ⟨76, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨76, by decide⟩ 3 hp) Q2.T120_76_2 Q2.hfix120_76_2 Q2.hinj120_76_2
      Q2.hcardT120_76_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_76_2 i) (Q2.hfix120_76_2 i) _)
      colCert_120_76_3.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_76_4 (hp : 4 < (Q2.transData.getD 76 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨76, by decide⟩ : Fin 148)) (colE2 ⟨76, by decide⟩ 4 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨76, by decide⟩ : Fin 148))
        (colE1 ⟨76, by decide⟩ 4 (transLenTr ⟨76, by decide⟩ 4 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨76, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨76, by decide⟩ 4 (transLenTr ⟨76, by decide⟩ 4 hp)) T120_76
      hfix120_76 hinj120_76 hcardT120_76
      (fun i => conj_mem_of_fixedPoints _ _ (T120_76 i) (hfix120_76 i) _)
      ⟨120, by decide⟩ ⟨76, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨76, by decide⟩ 4 hp) Q2.T120_76_2 Q2.hfix120_76_2 Q2.hinj120_76_2
      Q2.hcardT120_76_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_76_2 i) (Q2.hfix120_76_2 i) _)
      colCert_120_76_4.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_76_5 (hp : 5 < (Q2.transData.getD 76 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨76, by decide⟩ : Fin 148)) (colE2 ⟨76, by decide⟩ 5 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨76, by decide⟩ : Fin 148))
        (colE1 ⟨76, by decide⟩ 5 (transLenTr ⟨76, by decide⟩ 5 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨76, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨76, by decide⟩ 5 (transLenTr ⟨76, by decide⟩ 5 hp)) T120_76
      hfix120_76 hinj120_76 hcardT120_76
      (fun i => conj_mem_of_fixedPoints _ _ (T120_76 i) (hfix120_76 i) _)
      ⟨120, by decide⟩ ⟨76, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨76, by decide⟩ 5 hp) Q2.T120_76_2 Q2.hfix120_76_2 Q2.hinj120_76_2
      Q2.hcardT120_76_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_76_2 i) (Q2.hfix120_76_2 i) _)
      colCert_120_76_5.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_76_6 (hp : 6 < (Q2.transData.getD 76 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨76, by decide⟩ : Fin 148)) (colE2 ⟨76, by decide⟩ 6 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨76, by decide⟩ : Fin 148))
        (colE1 ⟨76, by decide⟩ 6 (transLenTr ⟨76, by decide⟩ 6 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨76, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨76, by decide⟩ 6 (transLenTr ⟨76, by decide⟩ 6 hp)) T120_76
      hfix120_76 hinj120_76 hcardT120_76
      (fun i => conj_mem_of_fixedPoints _ _ (T120_76 i) (hfix120_76 i) _)
      ⟨120, by decide⟩ ⟨76, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨76, by decide⟩ 6 hp) Q2.T120_76_2 Q2.hfix120_76_2 Q2.hinj120_76_2
      Q2.hcardT120_76_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_76_2 i) (Q2.hfix120_76_2 i) _)
      colCert_120_76_6.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_76_7 (hp : 7 < (Q2.transData.getD 76 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨76, by decide⟩ : Fin 148)) (colE2 ⟨76, by decide⟩ 7 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨76, by decide⟩ : Fin 148))
        (colE1 ⟨76, by decide⟩ 7 (transLenTr ⟨76, by decide⟩ 7 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨76, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨76, by decide⟩ 7 (transLenTr ⟨76, by decide⟩ 7 hp)) T120_76
      hfix120_76 hinj120_76 hcardT120_76
      (fun i => conj_mem_of_fixedPoints _ _ (T120_76 i) (hfix120_76 i) _)
      ⟨120, by decide⟩ ⟨76, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨76, by decide⟩ 7 hp) Q2.T120_76_2 Q2.hfix120_76_2 Q2.hinj120_76_2
      Q2.hcardT120_76_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_76_2 i) (Q2.hfix120_76_2 i) _)
      colCert_120_76_7.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_76_8 (hp : 8 < (Q2.transData.getD 76 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨76, by decide⟩ : Fin 148)) (colE2 ⟨76, by decide⟩ 8 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨76, by decide⟩ : Fin 148))
        (colE1 ⟨76, by decide⟩ 8 (transLenTr ⟨76, by decide⟩ 8 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨76, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨76, by decide⟩ 8 (transLenTr ⟨76, by decide⟩ 8 hp)) T120_76
      hfix120_76 hinj120_76 hcardT120_76
      (fun i => conj_mem_of_fixedPoints _ _ (T120_76 i) (hfix120_76 i) _)
      ⟨120, by decide⟩ ⟨76, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨76, by decide⟩ 8 hp) Q2.T120_76_2 Q2.hfix120_76_2 Q2.hinj120_76_2
      Q2.hcardT120_76_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_76_2 i) (Q2.hfix120_76_2 i) _)
      colCert_120_76_8.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_76_9 (hp : 9 < (Q2.transData.getD 76 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨76, by decide⟩ : Fin 148)) (colE2 ⟨76, by decide⟩ 9 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨76, by decide⟩ : Fin 148))
        (colE1 ⟨76, by decide⟩ 9 (transLenTr ⟨76, by decide⟩ 9 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨76, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨76, by decide⟩ 9 (transLenTr ⟨76, by decide⟩ 9 hp)) T120_76
      hfix120_76 hinj120_76 hcardT120_76
      (fun i => conj_mem_of_fixedPoints _ _ (T120_76 i) (hfix120_76 i) _)
      ⟨120, by decide⟩ ⟨76, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨76, by decide⟩ 9 hp) Q2.T120_76_2 Q2.hfix120_76_2 Q2.hinj120_76_2
      Q2.hcardT120_76_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_76_2 i) (Q2.hfix120_76_2 i) _)
      colCert_120_76_9.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_76_10 (hp : 10 < (Q2.transData.getD 76 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨76, by decide⟩ : Fin 148)) (colE2 ⟨76, by decide⟩ 10 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨76, by decide⟩ : Fin 148))
        (colE1 ⟨76, by decide⟩ 10 (transLenTr ⟨76, by decide⟩ 10 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨76, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨76, by decide⟩ 10 (transLenTr ⟨76, by decide⟩ 10 hp)) T120_76
      hfix120_76 hinj120_76 hcardT120_76
      (fun i => conj_mem_of_fixedPoints _ _ (T120_76 i) (hfix120_76 i) _)
      ⟨120, by decide⟩ ⟨76, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨76, by decide⟩ 10 hp) Q2.T120_76_2 Q2.hfix120_76_2 Q2.hinj120_76_2
      Q2.hcardT120_76_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_76_2 i) (Q2.hfix120_76_2 i) _)
      colCert_120_76_10.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_76_11 (hp : 11 < (Q2.transData.getD 76 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨76, by decide⟩ : Fin 148)) (colE2 ⟨76, by decide⟩ 11 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨76, by decide⟩ : Fin 148))
        (colE1 ⟨76, by decide⟩ 11 (transLenTr ⟨76, by decide⟩ 11 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨76, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨76, by decide⟩ 11 (transLenTr ⟨76, by decide⟩ 11 hp)) T120_76
      hfix120_76 hinj120_76 hcardT120_76
      (fun i => conj_mem_of_fixedPoints _ _ (T120_76 i) (hfix120_76 i) _)
      ⟨120, by decide⟩ ⟨76, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨76, by decide⟩ 11 hp) Q2.T120_76_2 Q2.hfix120_76_2 Q2.hinj120_76_2
      Q2.hcardT120_76_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_76_2 i) (Q2.hfix120_76_2 i) _)
      colCert_120_76_11.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_76_12 (hp : 12 < (Q2.transData.getD 76 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨76, by decide⟩ : Fin 148)) (colE2 ⟨76, by decide⟩ 12 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨76, by decide⟩ : Fin 148))
        (colE1 ⟨76, by decide⟩ 12 (transLenTr ⟨76, by decide⟩ 12 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨76, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨76, by decide⟩ 12 (transLenTr ⟨76, by decide⟩ 12 hp)) T120_76
      hfix120_76 hinj120_76 hcardT120_76
      (fun i => conj_mem_of_fixedPoints _ _ (T120_76 i) (hfix120_76 i) _)
      ⟨120, by decide⟩ ⟨76, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨76, by decide⟩ 12 hp) Q2.T120_76_2 Q2.hfix120_76_2 Q2.hinj120_76_2
      Q2.hcardT120_76_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_76_2 i) (Q2.hfix120_76_2 i) _)
      colCert_120_76_12.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_76_13 (hp : 13 < (Q2.transData.getD 76 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨76, by decide⟩ : Fin 148)) (colE2 ⟨76, by decide⟩ 13 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨76, by decide⟩ : Fin 148))
        (colE1 ⟨76, by decide⟩ 13 (transLenTr ⟨76, by decide⟩ 13 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨76, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨76, by decide⟩ 13 (transLenTr ⟨76, by decide⟩ 13 hp)) T120_76
      hfix120_76 hinj120_76 hcardT120_76
      (fun i => conj_mem_of_fixedPoints _ _ (T120_76 i) (hfix120_76 i) _)
      ⟨120, by decide⟩ ⟨76, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨76, by decide⟩ 13 hp) Q2.T120_76_2 Q2.hfix120_76_2 Q2.hinj120_76_2
      Q2.hcardT120_76_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_76_2 i) (Q2.hfix120_76_2 i) _)
      colCert_120_76_13.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_76_14 (hp : 14 < (Q2.transData.getD 76 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨76, by decide⟩ : Fin 148)) (colE2 ⟨76, by decide⟩ 14 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨76, by decide⟩ : Fin 148))
        (colE1 ⟨76, by decide⟩ 14 (transLenTr ⟨76, by decide⟩ 14 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨76, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨76, by decide⟩ 14 (transLenTr ⟨76, by decide⟩ 14 hp)) T120_76
      hfix120_76 hinj120_76 hcardT120_76
      (fun i => conj_mem_of_fixedPoints _ _ (T120_76 i) (hfix120_76 i) _)
      ⟨120, by decide⟩ ⟨76, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨76, by decide⟩ 14 hp) Q2.T120_76_2 Q2.hfix120_76_2 Q2.hinj120_76_2
      Q2.hcardT120_76_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_76_2 i) (Q2.hfix120_76_2 i) _)
      colCert_120_76_14.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_76_15 (hp : 15 < (Q2.transData.getD 76 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨76, by decide⟩ : Fin 148)) (colE2 ⟨76, by decide⟩ 15 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨76, by decide⟩ : Fin 148))
        (colE1 ⟨76, by decide⟩ 15 (transLenTr ⟨76, by decide⟩ 15 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨76, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨76, by decide⟩ 15 (transLenTr ⟨76, by decide⟩ 15 hp)) T120_76
      hfix120_76 hinj120_76 hcardT120_76
      (fun i => conj_mem_of_fixedPoints _ _ (T120_76 i) (hfix120_76 i) _)
      ⟨120, by decide⟩ ⟨76, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨76, by decide⟩ 15 hp) Q2.T120_76_2 Q2.hfix120_76_2 Q2.hinj120_76_2
      Q2.hcardT120_76_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_76_2 i) (Q2.hfix120_76_2 i) _)
      colCert_120_76_15.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_76_16 (hp : 16 < (Q2.transData.getD 76 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨76, by decide⟩ : Fin 148)) (colE2 ⟨76, by decide⟩ 16 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨76, by decide⟩ : Fin 148))
        (colE1 ⟨76, by decide⟩ 16 (transLenTr ⟨76, by decide⟩ 16 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨76, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨76, by decide⟩ 16 (transLenTr ⟨76, by decide⟩ 16 hp)) T120_76
      hfix120_76 hinj120_76 hcardT120_76
      (fun i => conj_mem_of_fixedPoints _ _ (T120_76 i) (hfix120_76 i) _)
      ⟨120, by decide⟩ ⟨76, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨76, by decide⟩ 16 hp) Q2.T120_76_2 Q2.hfix120_76_2 Q2.hinj120_76_2
      Q2.hcardT120_76_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_76_2 i) (Q2.hfix120_76_2 i) _)
      colCert_120_76_16.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_76_17 (hp : 17 < (Q2.transData.getD 76 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨76, by decide⟩ : Fin 148)) (colE2 ⟨76, by decide⟩ 17 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨76, by decide⟩ : Fin 148))
        (colE1 ⟨76, by decide⟩ 17 (transLenTr ⟨76, by decide⟩ 17 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨76, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨76, by decide⟩ 17 (transLenTr ⟨76, by decide⟩ 17 hp)) T120_76
      hfix120_76 hinj120_76 hcardT120_76
      (fun i => conj_mem_of_fixedPoints _ _ (T120_76 i) (hfix120_76 i) _)
      ⟨120, by decide⟩ ⟨76, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨76, by decide⟩ 17 hp) Q2.T120_76_2 Q2.hfix120_76_2 Q2.hinj120_76_2
      Q2.hcardT120_76_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_76_2 i) (Q2.hfix120_76_2 i) _)
      colCert_120_76_17.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_76_18 (hp : 18 < (Q2.transData.getD 76 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨76, by decide⟩ : Fin 148)) (colE2 ⟨76, by decide⟩ 18 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨76, by decide⟩ : Fin 148))
        (colE1 ⟨76, by decide⟩ 18 (transLenTr ⟨76, by decide⟩ 18 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨76, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨76, by decide⟩ 18 (transLenTr ⟨76, by decide⟩ 18 hp)) T120_76
      hfix120_76 hinj120_76 hcardT120_76
      (fun i => conj_mem_of_fixedPoints _ _ (T120_76 i) (hfix120_76 i) _)
      ⟨120, by decide⟩ ⟨76, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨76, by decide⟩ 18 hp) Q2.T120_76_2 Q2.hfix120_76_2 Q2.hinj120_76_2
      Q2.hcardT120_76_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_76_2 i) (Q2.hfix120_76_2 i) _)
      colCert_120_76_18.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_76_19 (hp : 19 < (Q2.transData.getD 76 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨76, by decide⟩ : Fin 148)) (colE2 ⟨76, by decide⟩ 19 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨76, by decide⟩ : Fin 148))
        (colE1 ⟨76, by decide⟩ 19 (transLenTr ⟨76, by decide⟩ 19 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨76, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨76, by decide⟩ 19 (transLenTr ⟨76, by decide⟩ 19 hp)) T120_76
      hfix120_76 hinj120_76 hcardT120_76
      (fun i => conj_mem_of_fixedPoints _ _ (T120_76 i) (hfix120_76 i) _)
      ⟨120, by decide⟩ ⟨76, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨76, by decide⟩ 19 hp) Q2.T120_76_2 Q2.hfix120_76_2 Q2.hinj120_76_2
      Q2.hcardT120_76_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_76_2 i) (Q2.hfix120_76_2 i) _)
      colCert_120_76_19.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_76_20 (hp : 20 < (Q2.transData.getD 76 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨76, by decide⟩ : Fin 148)) (colE2 ⟨76, by decide⟩ 20 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨76, by decide⟩ : Fin 148))
        (colE1 ⟨76, by decide⟩ 20 (transLenTr ⟨76, by decide⟩ 20 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨76, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨76, by decide⟩ 20 (transLenTr ⟨76, by decide⟩ 20 hp)) T120_76
      hfix120_76 hinj120_76 hcardT120_76
      (fun i => conj_mem_of_fixedPoints _ _ (T120_76 i) (hfix120_76 i) _)
      ⟨120, by decide⟩ ⟨76, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨76, by decide⟩ 20 hp) Q2.T120_76_2 Q2.hfix120_76_2 Q2.hinj120_76_2
      Q2.hcardT120_76_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_76_2 i) (Q2.hfix120_76_2 i) _)
      colCert_120_76_20.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_76_21 (hp : 21 < (Q2.transData.getD 76 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨76, by decide⟩ : Fin 148)) (colE2 ⟨76, by decide⟩ 21 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨76, by decide⟩ : Fin 148))
        (colE1 ⟨76, by decide⟩ 21 (transLenTr ⟨76, by decide⟩ 21 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨76, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨76, by decide⟩ 21 (transLenTr ⟨76, by decide⟩ 21 hp)) T120_76
      hfix120_76 hinj120_76 hcardT120_76
      (fun i => conj_mem_of_fixedPoints _ _ (T120_76 i) (hfix120_76 i) _)
      ⟨120, by decide⟩ ⟨76, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨76, by decide⟩ 21 hp) Q2.T120_76_2 Q2.hfix120_76_2 Q2.hinj120_76_2
      Q2.hcardT120_76_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_76_2 i) (Q2.hfix120_76_2 i) _)
      colCert_120_76_21.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_76_22 (hp : 22 < (Q2.transData.getD 76 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨76, by decide⟩ : Fin 148)) (colE2 ⟨76, by decide⟩ 22 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨76, by decide⟩ : Fin 148))
        (colE1 ⟨76, by decide⟩ 22 (transLenTr ⟨76, by decide⟩ 22 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨76, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨76, by decide⟩ 22 (transLenTr ⟨76, by decide⟩ 22 hp)) T120_76
      hfix120_76 hinj120_76 hcardT120_76
      (fun i => conj_mem_of_fixedPoints _ _ (T120_76 i) (hfix120_76 i) _)
      ⟨120, by decide⟩ ⟨76, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨76, by decide⟩ 22 hp) Q2.T120_76_2 Q2.hfix120_76_2 Q2.hinj120_76_2
      Q2.hcardT120_76_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_76_2 i) (Q2.hfix120_76_2 i) _)
      colCert_120_76_22.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_76_23 (hp : 23 < (Q2.transData.getD 76 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨76, by decide⟩ : Fin 148)) (colE2 ⟨76, by decide⟩ 23 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨76, by decide⟩ : Fin 148))
        (colE1 ⟨76, by decide⟩ 23 (transLenTr ⟨76, by decide⟩ 23 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨76, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨76, by decide⟩ 23 (transLenTr ⟨76, by decide⟩ 23 hp)) T120_76
      hfix120_76 hinj120_76 hcardT120_76
      (fun i => conj_mem_of_fixedPoints _ _ (T120_76 i) (hfix120_76 i) _)
      ⟨120, by decide⟩ ⟨76, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨76, by decide⟩ 23 hp) Q2.T120_76_2 Q2.hfix120_76_2 Q2.hinj120_76_2
      Q2.hcardT120_76_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_76_2 i) (Q2.hfix120_76_2 i) _)
      colCert_120_76_23.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_76_24 (hp : 24 < (Q2.transData.getD 76 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨76, by decide⟩ : Fin 148)) (colE2 ⟨76, by decide⟩ 24 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨76, by decide⟩ : Fin 148))
        (colE1 ⟨76, by decide⟩ 24 (transLenTr ⟨76, by decide⟩ 24 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨76, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨76, by decide⟩ 24 (transLenTr ⟨76, by decide⟩ 24 hp)) T120_76
      hfix120_76 hinj120_76 hcardT120_76
      (fun i => conj_mem_of_fixedPoints _ _ (T120_76 i) (hfix120_76 i) _)
      ⟨120, by decide⟩ ⟨76, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨76, by decide⟩ 24 hp) Q2.T120_76_2 Q2.hfix120_76_2 Q2.hinj120_76_2
      Q2.hcardT120_76_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_76_2 i) (Q2.hfix120_76_2 i) _)
      colCert_120_76_24.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_76_25 (hp : 25 < (Q2.transData.getD 76 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨76, by decide⟩ : Fin 148)) (colE2 ⟨76, by decide⟩ 25 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨76, by decide⟩ : Fin 148))
        (colE1 ⟨76, by decide⟩ 25 (transLenTr ⟨76, by decide⟩ 25 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨120, by decide⟩ : Fin 148) ⟨76, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨76, by decide⟩ 25 (transLenTr ⟨76, by decide⟩ 25 hp)) T120_76
      hfix120_76 hinj120_76 hcardT120_76
      (fun i => conj_mem_of_fixedPoints _ _ (T120_76 i) (hfix120_76 i) _)
      ⟨120, by decide⟩ ⟨76, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨76, by decide⟩ 25 hp) Q2.T120_76_2 Q2.hfix120_76_2 Q2.hinj120_76_2
      Q2.hcardT120_76_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_76_2 i) (Q2.hfix120_76_2 i) _)
      ?_).symm
  rw [show colData1 (⟨120, by decide⟩ : Fin 148)
        ((colE1 ⟨76, by decide⟩ 25 (transLenTr ⟨76, by decide⟩ 25 hp) : ↥(reps ⟨76, by decide⟩)) : Coordinate 1)
        T120_76 = colFn colCertDiv_120_76_25.D1 (m := 5) from colCertDiv_120_76_25.bind1,
    show colData2 (⟨120, by decide⟩ : Fin 148)
        ((colE2 ⟨76, by decide⟩ 25 hp : ↥(Q2.reps ⟨76, by decide⟩)) : Coordinate 2)
        Q2.T120_76_2 = colFn colCertDiv_120_76_25.D2 (m := 5) from colCertDiv_120_76_25.bind2]
  rw [alnId_120 j hj]
  exact fastcode_of_div ⟨120, by decide⟩ _ _ _
    ((alnId_120 j hj) ▸ Q2.listedAt (⟨120, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨120, by decide⟩ : Fin 148) hj hq).1) colCertDiv_120_76_25_match


theorem leaf_120_76_30 (hp : 30 < (Q2.transData.getD 76 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨76, by decide⟩ : Fin 148)) (colE2 ⟨76, by decide⟩ 30 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨76, by decide⟩ : Fin 148))
        (colE1 ⟨76, by decide⟩ 30 (transLenTr ⟨76, by decide⟩ 30 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨120, by decide⟩ : Fin 148) ⟨76, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨76, by decide⟩ 30 (transLenTr ⟨76, by decide⟩ 30 hp)) T120_76
      hfix120_76 hinj120_76 hcardT120_76
      (fun i => conj_mem_of_fixedPoints _ _ (T120_76 i) (hfix120_76 i) _)
      ⟨120, by decide⟩ ⟨76, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨76, by decide⟩ 30 hp) Q2.T120_76_2 Q2.hfix120_76_2 Q2.hinj120_76_2
      Q2.hcardT120_76_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_76_2 i) (Q2.hfix120_76_2 i) _)
      ?_).symm
  rw [show colData1 (⟨120, by decide⟩ : Fin 148)
        ((colE1 ⟨76, by decide⟩ 30 (transLenTr ⟨76, by decide⟩ 30 hp) : ↥(reps ⟨76, by decide⟩)) : Coordinate 1)
        T120_76 = colFn colCertDiv_120_76_30.D1 (m := 5) from colCertDiv_120_76_30.bind1,
    show colData2 (⟨120, by decide⟩ : Fin 148)
        ((colE2 ⟨76, by decide⟩ 30 hp : ↥(Q2.reps ⟨76, by decide⟩)) : Coordinate 2)
        Q2.T120_76_2 = colFn colCertDiv_120_76_30.D2 (m := 5) from colCertDiv_120_76_30.bind2]
  rw [alnId_120 j hj]
  exact fastcode_of_div ⟨120, by decide⟩ _ _ _
    ((alnId_120 j hj) ▸ Q2.listedAt (⟨120, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨120, by decide⟩ : Fin 148) hj hq).1) colCertDiv_120_76_30_match


theorem leaf_120_76_35 (hp : 35 < (Q2.transData.getD 76 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨76, by decide⟩ : Fin 148)) (colE2 ⟨76, by decide⟩ 35 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨76, by decide⟩ : Fin 148))
        (colE1 ⟨76, by decide⟩ 35 (transLenTr ⟨76, by decide⟩ 35 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨120, by decide⟩ : Fin 148) ⟨76, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨76, by decide⟩ 35 (transLenTr ⟨76, by decide⟩ 35 hp)) T120_76
      hfix120_76 hinj120_76 hcardT120_76
      (fun i => conj_mem_of_fixedPoints _ _ (T120_76 i) (hfix120_76 i) _)
      ⟨120, by decide⟩ ⟨76, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨76, by decide⟩ 35 hp) Q2.T120_76_2 Q2.hfix120_76_2 Q2.hinj120_76_2
      Q2.hcardT120_76_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_76_2 i) (Q2.hfix120_76_2 i) _)
      ?_).symm
  rw [show colData1 (⟨120, by decide⟩ : Fin 148)
        ((colE1 ⟨76, by decide⟩ 35 (transLenTr ⟨76, by decide⟩ 35 hp) : ↥(reps ⟨76, by decide⟩)) : Coordinate 1)
        T120_76 = colFn colCertDiv_120_76_35.D1 (m := 5) from colCertDiv_120_76_35.bind1,
    show colData2 (⟨120, by decide⟩ : Fin 148)
        ((colE2 ⟨76, by decide⟩ 35 hp : ↥(Q2.reps ⟨76, by decide⟩)) : Coordinate 2)
        Q2.T120_76_2 = colFn colCertDiv_120_76_35.D2 (m := 5) from colCertDiv_120_76_35.bind2]
  rw [alnId_120 j hj]
  exact fastcode_of_div ⟨120, by decide⟩ _ _ _
    ((alnId_120 j hj) ▸ Q2.listedAt (⟨120, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨120, by decide⟩ : Fin 148) hj hq).1) colCertDiv_120_76_35_match


theorem leaf_120_76_40 (hp : 40 < (Q2.transData.getD 76 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨76, by decide⟩ : Fin 148)) (colE2 ⟨76, by decide⟩ 40 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨76, by decide⟩ : Fin 148))
        (colE1 ⟨76, by decide⟩ 40 (transLenTr ⟨76, by decide⟩ 40 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨120, by decide⟩ : Fin 148) ⟨76, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨76, by decide⟩ 40 (transLenTr ⟨76, by decide⟩ 40 hp)) T120_76
      hfix120_76 hinj120_76 hcardT120_76
      (fun i => conj_mem_of_fixedPoints _ _ (T120_76 i) (hfix120_76 i) _)
      ⟨120, by decide⟩ ⟨76, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨76, by decide⟩ 40 hp) Q2.T120_76_2 Q2.hfix120_76_2 Q2.hinj120_76_2
      Q2.hcardT120_76_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_76_2 i) (Q2.hfix120_76_2 i) _)
      ?_).symm
  rw [show colData1 (⟨120, by decide⟩ : Fin 148)
        ((colE1 ⟨76, by decide⟩ 40 (transLenTr ⟨76, by decide⟩ 40 hp) : ↥(reps ⟨76, by decide⟩)) : Coordinate 1)
        T120_76 = colFn colCertDiv_120_76_40.D1 (m := 5) from colCertDiv_120_76_40.bind1,
    show colData2 (⟨120, by decide⟩ : Fin 148)
        ((colE2 ⟨76, by decide⟩ 40 hp : ↥(Q2.reps ⟨76, by decide⟩)) : Coordinate 2)
        Q2.T120_76_2 = colFn colCertDiv_120_76_40.D2 (m := 5) from colCertDiv_120_76_40.bind2]
  rw [alnId_120 j hj]
  exact fastcode_of_div ⟨120, by decide⟩ _ _ _
    ((alnId_120 j hj) ▸ Q2.listedAt (⟨120, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨120, by decide⟩ : Fin 148) hj hq).1) colCertDiv_120_76_40_match


theorem leaf_120_76_45 (hp : 45 < (Q2.transData.getD 76 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨76, by decide⟩ : Fin 148)) (colE2 ⟨76, by decide⟩ 45 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨76, by decide⟩ : Fin 148))
        (colE1 ⟨76, by decide⟩ 45 (transLenTr ⟨76, by decide⟩ 45 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨120, by decide⟩ : Fin 148) ⟨76, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨76, by decide⟩ 45 (transLenTr ⟨76, by decide⟩ 45 hp)) T120_76
      hfix120_76 hinj120_76 hcardT120_76
      (fun i => conj_mem_of_fixedPoints _ _ (T120_76 i) (hfix120_76 i) _)
      ⟨120, by decide⟩ ⟨76, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨76, by decide⟩ 45 hp) Q2.T120_76_2 Q2.hfix120_76_2 Q2.hinj120_76_2
      Q2.hcardT120_76_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_76_2 i) (Q2.hfix120_76_2 i) _)
      ?_).symm
  rw [show colData1 (⟨120, by decide⟩ : Fin 148)
        ((colE1 ⟨76, by decide⟩ 45 (transLenTr ⟨76, by decide⟩ 45 hp) : ↥(reps ⟨76, by decide⟩)) : Coordinate 1)
        T120_76 = colFn colCertDiv_120_76_45.D1 (m := 5) from colCertDiv_120_76_45.bind1,
    show colData2 (⟨120, by decide⟩ : Fin 148)
        ((colE2 ⟨76, by decide⟩ 45 hp : ↥(Q2.reps ⟨76, by decide⟩)) : Coordinate 2)
        Q2.T120_76_2 = colFn colCertDiv_120_76_45.D2 (m := 5) from colCertDiv_120_76_45.bind2]
  rw [alnId_120 j hj]
  exact fastcode_of_div ⟨120, by decide⟩ _ _ _
    ((alnId_120 j hj) ▸ Q2.listedAt (⟨120, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨120, by decide⟩ : Fin 148) hj hq).1) colCertDiv_120_76_45_match


theorem leaf_120_76_50 (hp : 50 < (Q2.transData.getD 76 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨76, by decide⟩ : Fin 148)) (colE2 ⟨76, by decide⟩ 50 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨76, by decide⟩ : Fin 148))
        (colE1 ⟨76, by decide⟩ 50 (transLenTr ⟨76, by decide⟩ 50 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨120, by decide⟩ : Fin 148) ⟨76, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨76, by decide⟩ 50 (transLenTr ⟨76, by decide⟩ 50 hp)) T120_76
      hfix120_76 hinj120_76 hcardT120_76
      (fun i => conj_mem_of_fixedPoints _ _ (T120_76 i) (hfix120_76 i) _)
      ⟨120, by decide⟩ ⟨76, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨76, by decide⟩ 50 hp) Q2.T120_76_2 Q2.hfix120_76_2 Q2.hinj120_76_2
      Q2.hcardT120_76_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_76_2 i) (Q2.hfix120_76_2 i) _)
      ?_).symm
  rw [show colData1 (⟨120, by decide⟩ : Fin 148)
        ((colE1 ⟨76, by decide⟩ 50 (transLenTr ⟨76, by decide⟩ 50 hp) : ↥(reps ⟨76, by decide⟩)) : Coordinate 1)
        T120_76 = colFn colCertDiv_120_76_50.D1 (m := 5) from colCertDiv_120_76_50.bind1,
    show colData2 (⟨120, by decide⟩ : Fin 148)
        ((colE2 ⟨76, by decide⟩ 50 hp : ↥(Q2.reps ⟨76, by decide⟩)) : Coordinate 2)
        Q2.T120_76_2 = colFn colCertDiv_120_76_50.D2 (m := 5) from colCertDiv_120_76_50.bind2]
  rw [alnId_120 j hj]
  exact fastcode_of_div ⟨120, by decide⟩ _ _ _
    ((alnId_120 j hj) ▸ Q2.listedAt (⟨120, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨120, by decide⟩ : Fin 148) hj hq).1) colCertDiv_120_76_50_match


theorem leaf_120_76_55 (hp : 55 < (Q2.transData.getD 76 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨76, by decide⟩ : Fin 148)) (colE2 ⟨76, by decide⟩ 55 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨76, by decide⟩ : Fin 148))
        (colE1 ⟨76, by decide⟩ 55 (transLenTr ⟨76, by decide⟩ 55 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨120, by decide⟩ : Fin 148) ⟨76, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨76, by decide⟩ 55 (transLenTr ⟨76, by decide⟩ 55 hp)) T120_76
      hfix120_76 hinj120_76 hcardT120_76
      (fun i => conj_mem_of_fixedPoints _ _ (T120_76 i) (hfix120_76 i) _)
      ⟨120, by decide⟩ ⟨76, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨76, by decide⟩ 55 hp) Q2.T120_76_2 Q2.hfix120_76_2 Q2.hinj120_76_2
      Q2.hcardT120_76_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_76_2 i) (Q2.hfix120_76_2 i) _)
      ?_).symm
  rw [show colData1 (⟨120, by decide⟩ : Fin 148)
        ((colE1 ⟨76, by decide⟩ 55 (transLenTr ⟨76, by decide⟩ 55 hp) : ↥(reps ⟨76, by decide⟩)) : Coordinate 1)
        T120_76 = colFn colCertDiv_120_76_55.D1 (m := 5) from colCertDiv_120_76_55.bind1,
    show colData2 (⟨120, by decide⟩ : Fin 148)
        ((colE2 ⟨76, by decide⟩ 55 hp : ↥(Q2.reps ⟨76, by decide⟩)) : Coordinate 2)
        Q2.T120_76_2 = colFn colCertDiv_120_76_55.D2 (m := 5) from colCertDiv_120_76_55.bind2]
  rw [alnId_120 j hj]
  exact fastcode_of_div ⟨120, by decide⟩ _ _ _
    ((alnId_120 j hj) ▸ Q2.listedAt (⟨120, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨120, by decide⟩ : Fin 148) hj hq).1) colCertDiv_120_76_55_match


theorem leaf_120_76_60 (hp : 60 < (Q2.transData.getD 76 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨76, by decide⟩ : Fin 148)) (colE2 ⟨76, by decide⟩ 60 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨76, by decide⟩ : Fin 148))
        (colE1 ⟨76, by decide⟩ 60 (transLenTr ⟨76, by decide⟩ 60 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨120, by decide⟩ : Fin 148) ⟨76, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨76, by decide⟩ 60 (transLenTr ⟨76, by decide⟩ 60 hp)) T120_76
      hfix120_76 hinj120_76 hcardT120_76
      (fun i => conj_mem_of_fixedPoints _ _ (T120_76 i) (hfix120_76 i) _)
      ⟨120, by decide⟩ ⟨76, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨76, by decide⟩ 60 hp) Q2.T120_76_2 Q2.hfix120_76_2 Q2.hinj120_76_2
      Q2.hcardT120_76_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_76_2 i) (Q2.hfix120_76_2 i) _)
      ?_).symm
  rw [show colData1 (⟨120, by decide⟩ : Fin 148)
        ((colE1 ⟨76, by decide⟩ 60 (transLenTr ⟨76, by decide⟩ 60 hp) : ↥(reps ⟨76, by decide⟩)) : Coordinate 1)
        T120_76 = colFn colCertDiv_120_76_60.D1 (m := 5) from colCertDiv_120_76_60.bind1,
    show colData2 (⟨120, by decide⟩ : Fin 148)
        ((colE2 ⟨76, by decide⟩ 60 hp : ↥(Q2.reps ⟨76, by decide⟩)) : Coordinate 2)
        Q2.T120_76_2 = colFn colCertDiv_120_76_60.D2 (m := 5) from colCertDiv_120_76_60.bind2]
  rw [alnId_120 j hj]
  exact fastcode_of_div ⟨120, by decide⟩ _ _ _
    ((alnId_120 j hj) ▸ Q2.listedAt (⟨120, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨120, by decide⟩ : Fin 148) hj hq).1) colCertDiv_120_76_60_match


theorem leaf_120_76_65 (hp : 65 < (Q2.transData.getD 76 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨76, by decide⟩ : Fin 148)) (colE2 ⟨76, by decide⟩ 65 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨76, by decide⟩ : Fin 148))
        (colE1 ⟨76, by decide⟩ 65 (transLenTr ⟨76, by decide⟩ 65 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨120, by decide⟩ : Fin 148) ⟨76, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨76, by decide⟩ 65 (transLenTr ⟨76, by decide⟩ 65 hp)) T120_76
      hfix120_76 hinj120_76 hcardT120_76
      (fun i => conj_mem_of_fixedPoints _ _ (T120_76 i) (hfix120_76 i) _)
      ⟨120, by decide⟩ ⟨76, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨76, by decide⟩ 65 hp) Q2.T120_76_2 Q2.hfix120_76_2 Q2.hinj120_76_2
      Q2.hcardT120_76_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_76_2 i) (Q2.hfix120_76_2 i) _)
      ?_).symm
  rw [show colData1 (⟨120, by decide⟩ : Fin 148)
        ((colE1 ⟨76, by decide⟩ 65 (transLenTr ⟨76, by decide⟩ 65 hp) : ↥(reps ⟨76, by decide⟩)) : Coordinate 1)
        T120_76 = colFn colCertDiv_120_76_65.D1 (m := 5) from colCertDiv_120_76_65.bind1,
    show colData2 (⟨120, by decide⟩ : Fin 148)
        ((colE2 ⟨76, by decide⟩ 65 hp : ↥(Q2.reps ⟨76, by decide⟩)) : Coordinate 2)
        Q2.T120_76_2 = colFn colCertDiv_120_76_65.D2 (m := 5) from colCertDiv_120_76_65.bind2]
  rw [alnId_120 j hj]
  exact fastcode_of_div ⟨120, by decide⟩ _ _ _
    ((alnId_120 j hj) ▸ Q2.listedAt (⟨120, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨120, by decide⟩ : Fin 148) hj hq).1) colCertDiv_120_76_65_match


theorem leaf_120_76_70 (hp : 70 < (Q2.transData.getD 76 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨76, by decide⟩ : Fin 148)) (colE2 ⟨76, by decide⟩ 70 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨76, by decide⟩ : Fin 148))
        (colE1 ⟨76, by decide⟩ 70 (transLenTr ⟨76, by decide⟩ 70 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨120, by decide⟩ : Fin 148) ⟨76, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨76, by decide⟩ 70 (transLenTr ⟨76, by decide⟩ 70 hp)) T120_76
      hfix120_76 hinj120_76 hcardT120_76
      (fun i => conj_mem_of_fixedPoints _ _ (T120_76 i) (hfix120_76 i) _)
      ⟨120, by decide⟩ ⟨76, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨76, by decide⟩ 70 hp) Q2.T120_76_2 Q2.hfix120_76_2 Q2.hinj120_76_2
      Q2.hcardT120_76_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_76_2 i) (Q2.hfix120_76_2 i) _)
      ?_).symm
  rw [show colData1 (⟨120, by decide⟩ : Fin 148)
        ((colE1 ⟨76, by decide⟩ 70 (transLenTr ⟨76, by decide⟩ 70 hp) : ↥(reps ⟨76, by decide⟩)) : Coordinate 1)
        T120_76 = colFn colCertDiv_120_76_70.D1 (m := 5) from colCertDiv_120_76_70.bind1,
    show colData2 (⟨120, by decide⟩ : Fin 148)
        ((colE2 ⟨76, by decide⟩ 70 hp : ↥(Q2.reps ⟨76, by decide⟩)) : Coordinate 2)
        Q2.T120_76_2 = colFn colCertDiv_120_76_70.D2 (m := 5) from colCertDiv_120_76_70.bind2]
  rw [alnId_120 j hj]
  exact fastcode_of_div ⟨120, by decide⟩ _ _ _
    ((alnId_120 j hj) ▸ Q2.listedAt (⟨120, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨120, by decide⟩ : Fin 148) hj hq).1) colCertDiv_120_76_70_match


theorem leaf_120_76_75 (hp : 75 < (Q2.transData.getD 76 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨76, by decide⟩ : Fin 148)) (colE2 ⟨76, by decide⟩ 75 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨76, by decide⟩ : Fin 148))
        (colE1 ⟨76, by decide⟩ 75 (transLenTr ⟨76, by decide⟩ 75 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨120, by decide⟩ : Fin 148) ⟨76, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨76, by decide⟩ 75 (transLenTr ⟨76, by decide⟩ 75 hp)) T120_76
      hfix120_76 hinj120_76 hcardT120_76
      (fun i => conj_mem_of_fixedPoints _ _ (T120_76 i) (hfix120_76 i) _)
      ⟨120, by decide⟩ ⟨76, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨76, by decide⟩ 75 hp) Q2.T120_76_2 Q2.hfix120_76_2 Q2.hinj120_76_2
      Q2.hcardT120_76_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_76_2 i) (Q2.hfix120_76_2 i) _)
      ?_).symm
  rw [show colData1 (⟨120, by decide⟩ : Fin 148)
        ((colE1 ⟨76, by decide⟩ 75 (transLenTr ⟨76, by decide⟩ 75 hp) : ↥(reps ⟨76, by decide⟩)) : Coordinate 1)
        T120_76 = colFn colCertDiv_120_76_75.D1 (m := 5) from colCertDiv_120_76_75.bind1,
    show colData2 (⟨120, by decide⟩ : Fin 148)
        ((colE2 ⟨76, by decide⟩ 75 hp : ↥(Q2.reps ⟨76, by decide⟩)) : Coordinate 2)
        Q2.T120_76_2 = colFn colCertDiv_120_76_75.D2 (m := 5) from colCertDiv_120_76_75.bind2]
  rw [alnId_120 j hj]
  exact fastcode_of_div ⟨120, by decide⟩ _ _ _
    ((alnId_120 j hj) ▸ Q2.listedAt (⟨120, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨120, by decide⟩ : Fin 148) hj hq).1) colCertDiv_120_76_75_match


theorem leaf_120_76_80 (hp : 80 < (Q2.transData.getD 76 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨76, by decide⟩ : Fin 148)) (colE2 ⟨76, by decide⟩ 80 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨76, by decide⟩ : Fin 148))
        (colE1 ⟨76, by decide⟩ 80 (transLenTr ⟨76, by decide⟩ 80 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨120, by decide⟩ : Fin 148) ⟨76, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨76, by decide⟩ 80 (transLenTr ⟨76, by decide⟩ 80 hp)) T120_76
      hfix120_76 hinj120_76 hcardT120_76
      (fun i => conj_mem_of_fixedPoints _ _ (T120_76 i) (hfix120_76 i) _)
      ⟨120, by decide⟩ ⟨76, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨76, by decide⟩ 80 hp) Q2.T120_76_2 Q2.hfix120_76_2 Q2.hinj120_76_2
      Q2.hcardT120_76_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_76_2 i) (Q2.hfix120_76_2 i) _)
      ?_).symm
  rw [show colData1 (⟨120, by decide⟩ : Fin 148)
        ((colE1 ⟨76, by decide⟩ 80 (transLenTr ⟨76, by decide⟩ 80 hp) : ↥(reps ⟨76, by decide⟩)) : Coordinate 1)
        T120_76 = colFn colCertDiv_120_76_80.D1 (m := 5) from colCertDiv_120_76_80.bind1,
    show colData2 (⟨120, by decide⟩ : Fin 148)
        ((colE2 ⟨76, by decide⟩ 80 hp : ↥(Q2.reps ⟨76, by decide⟩)) : Coordinate 2)
        Q2.T120_76_2 = colFn colCertDiv_120_76_80.D2 (m := 5) from colCertDiv_120_76_80.bind2]
  rw [alnId_120 j hj]
  exact fastcode_of_div ⟨120, by decide⟩ _ _ _
    ((alnId_120 j hj) ▸ Q2.listedAt (⟨120, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨120, by decide⟩ : Fin 148) hj hq).1) colCertDiv_120_76_80_match


theorem leaf_120_76_85 (hp : 85 < (Q2.transData.getD 76 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨76, by decide⟩ : Fin 148)) (colE2 ⟨76, by decide⟩ 85 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨76, by decide⟩ : Fin 148))
        (colE1 ⟨76, by decide⟩ 85 (transLenTr ⟨76, by decide⟩ 85 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨120, by decide⟩ : Fin 148) ⟨76, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨76, by decide⟩ 85 (transLenTr ⟨76, by decide⟩ 85 hp)) T120_76
      hfix120_76 hinj120_76 hcardT120_76
      (fun i => conj_mem_of_fixedPoints _ _ (T120_76 i) (hfix120_76 i) _)
      ⟨120, by decide⟩ ⟨76, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨76, by decide⟩ 85 hp) Q2.T120_76_2 Q2.hfix120_76_2 Q2.hinj120_76_2
      Q2.hcardT120_76_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_76_2 i) (Q2.hfix120_76_2 i) _)
      ?_).symm
  rw [show colData1 (⟨120, by decide⟩ : Fin 148)
        ((colE1 ⟨76, by decide⟩ 85 (transLenTr ⟨76, by decide⟩ 85 hp) : ↥(reps ⟨76, by decide⟩)) : Coordinate 1)
        T120_76 = colFn colCertDiv_120_76_85.D1 (m := 5) from colCertDiv_120_76_85.bind1,
    show colData2 (⟨120, by decide⟩ : Fin 148)
        ((colE2 ⟨76, by decide⟩ 85 hp : ↥(Q2.reps ⟨76, by decide⟩)) : Coordinate 2)
        Q2.T120_76_2 = colFn colCertDiv_120_76_85.D2 (m := 5) from colCertDiv_120_76_85.bind2]
  rw [alnId_120 j hj]
  exact fastcode_of_div ⟨120, by decide⟩ _ _ _
    ((alnId_120 j hj) ▸ Q2.listedAt (⟨120, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨120, by decide⟩ : Fin 148) hj hq).1) colCertDiv_120_76_85_match


theorem leaf_120_76_90 (hp : 90 < (Q2.transData.getD 76 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨76, by decide⟩ : Fin 148)) (colE2 ⟨76, by decide⟩ 90 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨76, by decide⟩ : Fin 148))
        (colE1 ⟨76, by decide⟩ 90 (transLenTr ⟨76, by decide⟩ 90 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨120, by decide⟩ : Fin 148) ⟨76, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨76, by decide⟩ 90 (transLenTr ⟨76, by decide⟩ 90 hp)) T120_76
      hfix120_76 hinj120_76 hcardT120_76
      (fun i => conj_mem_of_fixedPoints _ _ (T120_76 i) (hfix120_76 i) _)
      ⟨120, by decide⟩ ⟨76, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨76, by decide⟩ 90 hp) Q2.T120_76_2 Q2.hfix120_76_2 Q2.hinj120_76_2
      Q2.hcardT120_76_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_76_2 i) (Q2.hfix120_76_2 i) _)
      ?_).symm
  rw [show colData1 (⟨120, by decide⟩ : Fin 148)
        ((colE1 ⟨76, by decide⟩ 90 (transLenTr ⟨76, by decide⟩ 90 hp) : ↥(reps ⟨76, by decide⟩)) : Coordinate 1)
        T120_76 = colFn colCertDiv_120_76_90.D1 (m := 5) from colCertDiv_120_76_90.bind1,
    show colData2 (⟨120, by decide⟩ : Fin 148)
        ((colE2 ⟨76, by decide⟩ 90 hp : ↥(Q2.reps ⟨76, by decide⟩)) : Coordinate 2)
        Q2.T120_76_2 = colFn colCertDiv_120_76_90.D2 (m := 5) from colCertDiv_120_76_90.bind2]
  rw [alnId_120 j hj]
  exact fastcode_of_div ⟨120, by decide⟩ _ _ _
    ((alnId_120 j hj) ▸ Q2.listedAt (⟨120, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨120, by decide⟩ : Fin 148) hj hq).1) colCertDiv_120_76_90_match


theorem leaf_120_76_95 (hp : 95 < (Q2.transData.getD 76 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨76, by decide⟩ : Fin 148)) (colE2 ⟨76, by decide⟩ 95 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨76, by decide⟩ : Fin 148))
        (colE1 ⟨76, by decide⟩ 95 (transLenTr ⟨76, by decide⟩ 95 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨120, by decide⟩ : Fin 148) ⟨76, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨76, by decide⟩ 95 (transLenTr ⟨76, by decide⟩ 95 hp)) T120_76
      hfix120_76 hinj120_76 hcardT120_76
      (fun i => conj_mem_of_fixedPoints _ _ (T120_76 i) (hfix120_76 i) _)
      ⟨120, by decide⟩ ⟨76, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨76, by decide⟩ 95 hp) Q2.T120_76_2 Q2.hfix120_76_2 Q2.hinj120_76_2
      Q2.hcardT120_76_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_76_2 i) (Q2.hfix120_76_2 i) _)
      ?_).symm
  rw [show colData1 (⟨120, by decide⟩ : Fin 148)
        ((colE1 ⟨76, by decide⟩ 95 (transLenTr ⟨76, by decide⟩ 95 hp) : ↥(reps ⟨76, by decide⟩)) : Coordinate 1)
        T120_76 = colFn colCertDiv_120_76_95.D1 (m := 5) from colCertDiv_120_76_95.bind1,
    show colData2 (⟨120, by decide⟩ : Fin 148)
        ((colE2 ⟨76, by decide⟩ 95 hp : ↥(Q2.reps ⟨76, by decide⟩)) : Coordinate 2)
        Q2.T120_76_2 = colFn colCertDiv_120_76_95.D2 (m := 5) from colCertDiv_120_76_95.bind2]
  rw [alnId_120 j hj]
  exact fastcode_of_div ⟨120, by decide⟩ _ _ _
    ((alnId_120 j hj) ▸ Q2.listedAt (⟨120, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨120, by decide⟩ : Fin 148) hj hq).1) colCertDiv_120_76_95_match


theorem leaf_120_76_100 (hp : 100 < (Q2.transData.getD 76 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨76, by decide⟩ : Fin 148)) (colE2 ⟨76, by decide⟩ 100 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨76, by decide⟩ : Fin 148))
        (colE1 ⟨76, by decide⟩ 100 (transLenTr ⟨76, by decide⟩ 100 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨120, by decide⟩ : Fin 148) ⟨76, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨76, by decide⟩ 100 (transLenTr ⟨76, by decide⟩ 100 hp)) T120_76
      hfix120_76 hinj120_76 hcardT120_76
      (fun i => conj_mem_of_fixedPoints _ _ (T120_76 i) (hfix120_76 i) _)
      ⟨120, by decide⟩ ⟨76, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨76, by decide⟩ 100 hp) Q2.T120_76_2 Q2.hfix120_76_2 Q2.hinj120_76_2
      Q2.hcardT120_76_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_76_2 i) (Q2.hfix120_76_2 i) _)
      ?_).symm
  rw [show colData1 (⟨120, by decide⟩ : Fin 148)
        ((colE1 ⟨76, by decide⟩ 100 (transLenTr ⟨76, by decide⟩ 100 hp) : ↥(reps ⟨76, by decide⟩)) : Coordinate 1)
        T120_76 = colFn colCertDiv_120_76_100.D1 (m := 5) from colCertDiv_120_76_100.bind1,
    show colData2 (⟨120, by decide⟩ : Fin 148)
        ((colE2 ⟨76, by decide⟩ 100 hp : ↥(Q2.reps ⟨76, by decide⟩)) : Coordinate 2)
        Q2.T120_76_2 = colFn colCertDiv_120_76_100.D2 (m := 5) from colCertDiv_120_76_100.bind2]
  rw [alnId_120 j hj]
  exact fastcode_of_div ⟨120, by decide⟩ _ _ _
    ((alnId_120 j hj) ▸ Q2.listedAt (⟨120, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨120, by decide⟩ : Fin 148) hj hq).1) colCertDiv_120_76_100_match


theorem leaf_120_76_105 (hp : 105 < (Q2.transData.getD 76 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨76, by decide⟩ : Fin 148)) (colE2 ⟨76, by decide⟩ 105 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨76, by decide⟩ : Fin 148))
        (colE1 ⟨76, by decide⟩ 105 (transLenTr ⟨76, by decide⟩ 105 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨120, by decide⟩ : Fin 148) ⟨76, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨76, by decide⟩ 105 (transLenTr ⟨76, by decide⟩ 105 hp)) T120_76
      hfix120_76 hinj120_76 hcardT120_76
      (fun i => conj_mem_of_fixedPoints _ _ (T120_76 i) (hfix120_76 i) _)
      ⟨120, by decide⟩ ⟨76, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨76, by decide⟩ 105 hp) Q2.T120_76_2 Q2.hfix120_76_2 Q2.hinj120_76_2
      Q2.hcardT120_76_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_76_2 i) (Q2.hfix120_76_2 i) _)
      ?_).symm
  rw [show colData1 (⟨120, by decide⟩ : Fin 148)
        ((colE1 ⟨76, by decide⟩ 105 (transLenTr ⟨76, by decide⟩ 105 hp) : ↥(reps ⟨76, by decide⟩)) : Coordinate 1)
        T120_76 = colFn colCertDiv_120_76_105.D1 (m := 5) from colCertDiv_120_76_105.bind1,
    show colData2 (⟨120, by decide⟩ : Fin 148)
        ((colE2 ⟨76, by decide⟩ 105 hp : ↥(Q2.reps ⟨76, by decide⟩)) : Coordinate 2)
        Q2.T120_76_2 = colFn colCertDiv_120_76_105.D2 (m := 5) from colCertDiv_120_76_105.bind2]
  rw [alnId_120 j hj]
  exact fastcode_of_div ⟨120, by decide⟩ _ _ _
    ((alnId_120 j hj) ▸ Q2.listedAt (⟨120, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨120, by decide⟩ : Fin 148) hj hq).1) colCertDiv_120_76_105_match


theorem leaf_120_76_110 (hp : 110 < (Q2.transData.getD 76 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨76, by decide⟩ : Fin 148)) (colE2 ⟨76, by decide⟩ 110 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨76, by decide⟩ : Fin 148))
        (colE1 ⟨76, by decide⟩ 110 (transLenTr ⟨76, by decide⟩ 110 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨120, by decide⟩ : Fin 148) ⟨76, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨76, by decide⟩ 110 (transLenTr ⟨76, by decide⟩ 110 hp)) T120_76
      hfix120_76 hinj120_76 hcardT120_76
      (fun i => conj_mem_of_fixedPoints _ _ (T120_76 i) (hfix120_76 i) _)
      ⟨120, by decide⟩ ⟨76, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨76, by decide⟩ 110 hp) Q2.T120_76_2 Q2.hfix120_76_2 Q2.hinj120_76_2
      Q2.hcardT120_76_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_76_2 i) (Q2.hfix120_76_2 i) _)
      ?_).symm
  rw [show colData1 (⟨120, by decide⟩ : Fin 148)
        ((colE1 ⟨76, by decide⟩ 110 (transLenTr ⟨76, by decide⟩ 110 hp) : ↥(reps ⟨76, by decide⟩)) : Coordinate 1)
        T120_76 = colFn colCertDiv_120_76_110.D1 (m := 5) from colCertDiv_120_76_110.bind1,
    show colData2 (⟨120, by decide⟩ : Fin 148)
        ((colE2 ⟨76, by decide⟩ 110 hp : ↥(Q2.reps ⟨76, by decide⟩)) : Coordinate 2)
        Q2.T120_76_2 = colFn colCertDiv_120_76_110.D2 (m := 5) from colCertDiv_120_76_110.bind2]
  rw [alnId_120 j hj]
  exact fastcode_of_div ⟨120, by decide⟩ _ _ _
    ((alnId_120 j hj) ▸ Q2.listedAt (⟨120, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨120, by decide⟩ : Fin 148) hj hq).1) colCertDiv_120_76_110_match


theorem leaf_120_76_115 (hp : 115 < (Q2.transData.getD 76 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨76, by decide⟩ : Fin 148)) (colE2 ⟨76, by decide⟩ 115 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨76, by decide⟩ : Fin 148))
        (colE1 ⟨76, by decide⟩ 115 (transLenTr ⟨76, by decide⟩ 115 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨120, by decide⟩ : Fin 148) ⟨76, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨76, by decide⟩ 115 (transLenTr ⟨76, by decide⟩ 115 hp)) T120_76
      hfix120_76 hinj120_76 hcardT120_76
      (fun i => conj_mem_of_fixedPoints _ _ (T120_76 i) (hfix120_76 i) _)
      ⟨120, by decide⟩ ⟨76, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨76, by decide⟩ 115 hp) Q2.T120_76_2 Q2.hfix120_76_2 Q2.hinj120_76_2
      Q2.hcardT120_76_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_76_2 i) (Q2.hfix120_76_2 i) _)
      ?_).symm
  rw [show colData1 (⟨120, by decide⟩ : Fin 148)
        ((colE1 ⟨76, by decide⟩ 115 (transLenTr ⟨76, by decide⟩ 115 hp) : ↥(reps ⟨76, by decide⟩)) : Coordinate 1)
        T120_76 = colFn colCertDiv_120_76_115.D1 (m := 5) from colCertDiv_120_76_115.bind1,
    show colData2 (⟨120, by decide⟩ : Fin 148)
        ((colE2 ⟨76, by decide⟩ 115 hp : ↥(Q2.reps ⟨76, by decide⟩)) : Coordinate 2)
        Q2.T120_76_2 = colFn colCertDiv_120_76_115.D2 (m := 5) from colCertDiv_120_76_115.bind2]
  rw [alnId_120 j hj]
  exact fastcode_of_div ⟨120, by decide⟩ _ _ _
    ((alnId_120 j hj) ▸ Q2.listedAt (⟨120, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨120, by decide⟩ : Fin 148) hj hq).1) colCertDiv_120_76_115_match


theorem leaf_120_76_120 (hp : 120 < (Q2.transData.getD 76 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨76, by decide⟩ : Fin 148)) (colE2 ⟨76, by decide⟩ 120 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨76, by decide⟩ : Fin 148))
        (colE1 ⟨76, by decide⟩ 120 (transLenTr ⟨76, by decide⟩ 120 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨120, by decide⟩ : Fin 148) ⟨76, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨76, by decide⟩ 120 (transLenTr ⟨76, by decide⟩ 120 hp)) T120_76
      hfix120_76 hinj120_76 hcardT120_76
      (fun i => conj_mem_of_fixedPoints _ _ (T120_76 i) (hfix120_76 i) _)
      ⟨120, by decide⟩ ⟨76, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨76, by decide⟩ 120 hp) Q2.T120_76_2 Q2.hfix120_76_2 Q2.hinj120_76_2
      Q2.hcardT120_76_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_76_2 i) (Q2.hfix120_76_2 i) _)
      ?_).symm
  rw [show colData1 (⟨120, by decide⟩ : Fin 148)
        ((colE1 ⟨76, by decide⟩ 120 (transLenTr ⟨76, by decide⟩ 120 hp) : ↥(reps ⟨76, by decide⟩)) : Coordinate 1)
        T120_76 = colFn colCertDiv_120_76_120.D1 (m := 5) from colCertDiv_120_76_120.bind1,
    show colData2 (⟨120, by decide⟩ : Fin 148)
        ((colE2 ⟨76, by decide⟩ 120 hp : ↥(Q2.reps ⟨76, by decide⟩)) : Coordinate 2)
        Q2.T120_76_2 = colFn colCertDiv_120_76_120.D2 (m := 5) from colCertDiv_120_76_120.bind2]
  rw [alnId_120 j hj]
  exact fastcode_of_div ⟨120, by decide⟩ _ _ _
    ((alnId_120 j hj) ▸ Q2.listedAt (⟨120, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨120, by decide⟩ : Fin 148) hj hq).1) colCertDiv_120_76_120_match


theorem leaf_120_77_0 (hp : 0 < (Q2.transData.getD 77 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨77, by decide⟩ : Fin 148)) (colE2 ⟨77, by decide⟩ 0 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨77, by decide⟩ : Fin 148))
        (colE1 ⟨77, by decide⟩ 0 (transLenTr ⟨77, by decide⟩ 0 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨77, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨77, by decide⟩ 0 (transLenTr ⟨77, by decide⟩ 0 hp)) T120_77
      hfix120_77 hinj120_77 hcardT120_77
      (fun i => conj_mem_of_fixedPoints _ _ (T120_77 i) (hfix120_77 i) _)
      ⟨120, by decide⟩ ⟨77, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨77, by decide⟩ 0 hp) Q2.T120_77_2 Q2.hfix120_77_2 Q2.hinj120_77_2
      Q2.hcardT120_77_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_77_2 i) (Q2.hfix120_77_2 i) _)
      colCert_120_77_0.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_77_1 (hp : 1 < (Q2.transData.getD 77 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨77, by decide⟩ : Fin 148)) (colE2 ⟨77, by decide⟩ 1 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨77, by decide⟩ : Fin 148))
        (colE1 ⟨77, by decide⟩ 1 (transLenTr ⟨77, by decide⟩ 1 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨77, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨77, by decide⟩ 1 (transLenTr ⟨77, by decide⟩ 1 hp)) T120_77
      hfix120_77 hinj120_77 hcardT120_77
      (fun i => conj_mem_of_fixedPoints _ _ (T120_77 i) (hfix120_77 i) _)
      ⟨120, by decide⟩ ⟨77, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨77, by decide⟩ 1 hp) Q2.T120_77_2 Q2.hfix120_77_2 Q2.hinj120_77_2
      Q2.hcardT120_77_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_77_2 i) (Q2.hfix120_77_2 i) _)
      colCert_120_77_1.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_77_2 (hp : 2 < (Q2.transData.getD 77 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨77, by decide⟩ : Fin 148)) (colE2 ⟨77, by decide⟩ 2 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨77, by decide⟩ : Fin 148))
        (colE1 ⟨77, by decide⟩ 2 (transLenTr ⟨77, by decide⟩ 2 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨77, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨77, by decide⟩ 2 (transLenTr ⟨77, by decide⟩ 2 hp)) T120_77
      hfix120_77 hinj120_77 hcardT120_77
      (fun i => conj_mem_of_fixedPoints _ _ (T120_77 i) (hfix120_77 i) _)
      ⟨120, by decide⟩ ⟨77, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨77, by decide⟩ 2 hp) Q2.T120_77_2 Q2.hfix120_77_2 Q2.hinj120_77_2
      Q2.hcardT120_77_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_77_2 i) (Q2.hfix120_77_2 i) _)
      colCert_120_77_2.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_77_3 (hp : 3 < (Q2.transData.getD 77 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨77, by decide⟩ : Fin 148)) (colE2 ⟨77, by decide⟩ 3 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨77, by decide⟩ : Fin 148))
        (colE1 ⟨77, by decide⟩ 3 (transLenTr ⟨77, by decide⟩ 3 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨77, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨77, by decide⟩ 3 (transLenTr ⟨77, by decide⟩ 3 hp)) T120_77
      hfix120_77 hinj120_77 hcardT120_77
      (fun i => conj_mem_of_fixedPoints _ _ (T120_77 i) (hfix120_77 i) _)
      ⟨120, by decide⟩ ⟨77, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨77, by decide⟩ 3 hp) Q2.T120_77_2 Q2.hfix120_77_2 Q2.hinj120_77_2
      Q2.hcardT120_77_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_77_2 i) (Q2.hfix120_77_2 i) _)
      colCert_120_77_3.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_77_4 (hp : 4 < (Q2.transData.getD 77 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨77, by decide⟩ : Fin 148)) (colE2 ⟨77, by decide⟩ 4 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨77, by decide⟩ : Fin 148))
        (colE1 ⟨77, by decide⟩ 4 (transLenTr ⟨77, by decide⟩ 4 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨77, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨77, by decide⟩ 4 (transLenTr ⟨77, by decide⟩ 4 hp)) T120_77
      hfix120_77 hinj120_77 hcardT120_77
      (fun i => conj_mem_of_fixedPoints _ _ (T120_77 i) (hfix120_77 i) _)
      ⟨120, by decide⟩ ⟨77, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨77, by decide⟩ 4 hp) Q2.T120_77_2 Q2.hfix120_77_2 Q2.hinj120_77_2
      Q2.hcardT120_77_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_77_2 i) (Q2.hfix120_77_2 i) _)
      colCert_120_77_4.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_77_5 (hp : 5 < (Q2.transData.getD 77 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨77, by decide⟩ : Fin 148)) (colE2 ⟨77, by decide⟩ 5 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨77, by decide⟩ : Fin 148))
        (colE1 ⟨77, by decide⟩ 5 (transLenTr ⟨77, by decide⟩ 5 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨120, by decide⟩ : Fin 148) ⟨77, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨77, by decide⟩ 5 (transLenTr ⟨77, by decide⟩ 5 hp)) T120_77
      hfix120_77 hinj120_77 hcardT120_77
      (fun i => conj_mem_of_fixedPoints _ _ (T120_77 i) (hfix120_77 i) _)
      ⟨120, by decide⟩ ⟨77, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨77, by decide⟩ 5 hp) Q2.T120_77_2 Q2.hfix120_77_2 Q2.hinj120_77_2
      Q2.hcardT120_77_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_77_2 i) (Q2.hfix120_77_2 i) _)
      ?_).symm
  rw [show colData1 (⟨120, by decide⟩ : Fin 148)
        ((colE1 ⟨77, by decide⟩ 5 (transLenTr ⟨77, by decide⟩ 5 hp) : ↥(reps ⟨77, by decide⟩)) : Coordinate 1)
        T120_77 = colFn colCertDiv_120_77_5.D1 (m := 5) from colCertDiv_120_77_5.bind1,
    show colData2 (⟨120, by decide⟩ : Fin 148)
        ((colE2 ⟨77, by decide⟩ 5 hp : ↥(Q2.reps ⟨77, by decide⟩)) : Coordinate 2)
        Q2.T120_77_2 = colFn colCertDiv_120_77_5.D2 (m := 5) from colCertDiv_120_77_5.bind2]
  rw [alnId_120 j hj]
  exact fastcode_of_div ⟨120, by decide⟩ _ _ _
    ((alnId_120 j hj) ▸ Q2.listedAt (⟨120, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨120, by decide⟩ : Fin 148) hj hq).1) colCertDiv_120_77_5_match


theorem leaf_120_77_6 (hp : 6 < (Q2.transData.getD 77 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨77, by decide⟩ : Fin 148)) (colE2 ⟨77, by decide⟩ 6 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨77, by decide⟩ : Fin 148))
        (colE1 ⟨77, by decide⟩ 6 (transLenTr ⟨77, by decide⟩ 6 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨120, by decide⟩ : Fin 148) ⟨77, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨77, by decide⟩ 6 (transLenTr ⟨77, by decide⟩ 6 hp)) T120_77
      hfix120_77 hinj120_77 hcardT120_77
      (fun i => conj_mem_of_fixedPoints _ _ (T120_77 i) (hfix120_77 i) _)
      ⟨120, by decide⟩ ⟨77, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨77, by decide⟩ 6 hp) Q2.T120_77_2 Q2.hfix120_77_2 Q2.hinj120_77_2
      Q2.hcardT120_77_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_77_2 i) (Q2.hfix120_77_2 i) _)
      ?_).symm
  rw [show colData1 (⟨120, by decide⟩ : Fin 148)
        ((colE1 ⟨77, by decide⟩ 6 (transLenTr ⟨77, by decide⟩ 6 hp) : ↥(reps ⟨77, by decide⟩)) : Coordinate 1)
        T120_77 = colFn colCertDiv_120_77_6.D1 (m := 5) from colCertDiv_120_77_6.bind1,
    show colData2 (⟨120, by decide⟩ : Fin 148)
        ((colE2 ⟨77, by decide⟩ 6 hp : ↥(Q2.reps ⟨77, by decide⟩)) : Coordinate 2)
        Q2.T120_77_2 = colFn colCertDiv_120_77_6.D2 (m := 5) from colCertDiv_120_77_6.bind2]
  rw [alnId_120 j hj]
  exact fastcode_of_div ⟨120, by decide⟩ _ _ _
    ((alnId_120 j hj) ▸ Q2.listedAt (⟨120, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨120, by decide⟩ : Fin 148) hj hq).1) colCertDiv_120_77_6_match


theorem leaf_120_77_7 (hp : 7 < (Q2.transData.getD 77 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨77, by decide⟩ : Fin 148)) (colE2 ⟨77, by decide⟩ 7 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨77, by decide⟩ : Fin 148))
        (colE1 ⟨77, by decide⟩ 7 (transLenTr ⟨77, by decide⟩ 7 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨120, by decide⟩ : Fin 148) ⟨77, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨77, by decide⟩ 7 (transLenTr ⟨77, by decide⟩ 7 hp)) T120_77
      hfix120_77 hinj120_77 hcardT120_77
      (fun i => conj_mem_of_fixedPoints _ _ (T120_77 i) (hfix120_77 i) _)
      ⟨120, by decide⟩ ⟨77, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨77, by decide⟩ 7 hp) Q2.T120_77_2 Q2.hfix120_77_2 Q2.hinj120_77_2
      Q2.hcardT120_77_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_77_2 i) (Q2.hfix120_77_2 i) _)
      ?_).symm
  rw [show colData1 (⟨120, by decide⟩ : Fin 148)
        ((colE1 ⟨77, by decide⟩ 7 (transLenTr ⟨77, by decide⟩ 7 hp) : ↥(reps ⟨77, by decide⟩)) : Coordinate 1)
        T120_77 = colFn colCertDiv_120_77_7.D1 (m := 5) from colCertDiv_120_77_7.bind1,
    show colData2 (⟨120, by decide⟩ : Fin 148)
        ((colE2 ⟨77, by decide⟩ 7 hp : ↥(Q2.reps ⟨77, by decide⟩)) : Coordinate 2)
        Q2.T120_77_2 = colFn colCertDiv_120_77_7.D2 (m := 5) from colCertDiv_120_77_7.bind2]
  rw [alnId_120 j hj]
  exact fastcode_of_div ⟨120, by decide⟩ _ _ _
    ((alnId_120 j hj) ▸ Q2.listedAt (⟨120, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨120, by decide⟩ : Fin 148) hj hq).1) colCertDiv_120_77_7_match


theorem leaf_120_77_8 (hp : 8 < (Q2.transData.getD 77 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨77, by decide⟩ : Fin 148)) (colE2 ⟨77, by decide⟩ 8 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨77, by decide⟩ : Fin 148))
        (colE1 ⟨77, by decide⟩ 8 (transLenTr ⟨77, by decide⟩ 8 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨120, by decide⟩ : Fin 148) ⟨77, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨77, by decide⟩ 8 (transLenTr ⟨77, by decide⟩ 8 hp)) T120_77
      hfix120_77 hinj120_77 hcardT120_77
      (fun i => conj_mem_of_fixedPoints _ _ (T120_77 i) (hfix120_77 i) _)
      ⟨120, by decide⟩ ⟨77, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨77, by decide⟩ 8 hp) Q2.T120_77_2 Q2.hfix120_77_2 Q2.hinj120_77_2
      Q2.hcardT120_77_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_77_2 i) (Q2.hfix120_77_2 i) _)
      ?_).symm
  rw [show colData1 (⟨120, by decide⟩ : Fin 148)
        ((colE1 ⟨77, by decide⟩ 8 (transLenTr ⟨77, by decide⟩ 8 hp) : ↥(reps ⟨77, by decide⟩)) : Coordinate 1)
        T120_77 = colFn colCertDiv_120_77_8.D1 (m := 5) from colCertDiv_120_77_8.bind1,
    show colData2 (⟨120, by decide⟩ : Fin 148)
        ((colE2 ⟨77, by decide⟩ 8 hp : ↥(Q2.reps ⟨77, by decide⟩)) : Coordinate 2)
        Q2.T120_77_2 = colFn colCertDiv_120_77_8.D2 (m := 5) from colCertDiv_120_77_8.bind2]
  rw [alnId_120 j hj]
  exact fastcode_of_div ⟨120, by decide⟩ _ _ _
    ((alnId_120 j hj) ▸ Q2.listedAt (⟨120, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨120, by decide⟩ : Fin 148) hj hq).1) colCertDiv_120_77_8_match


theorem leaf_120_77_9 (hp : 9 < (Q2.transData.getD 77 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨77, by decide⟩ : Fin 148)) (colE2 ⟨77, by decide⟩ 9 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨77, by decide⟩ : Fin 148))
        (colE1 ⟨77, by decide⟩ 9 (transLenTr ⟨77, by decide⟩ 9 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨120, by decide⟩ : Fin 148) ⟨77, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨77, by decide⟩ 9 (transLenTr ⟨77, by decide⟩ 9 hp)) T120_77
      hfix120_77 hinj120_77 hcardT120_77
      (fun i => conj_mem_of_fixedPoints _ _ (T120_77 i) (hfix120_77 i) _)
      ⟨120, by decide⟩ ⟨77, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨77, by decide⟩ 9 hp) Q2.T120_77_2 Q2.hfix120_77_2 Q2.hinj120_77_2
      Q2.hcardT120_77_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_77_2 i) (Q2.hfix120_77_2 i) _)
      ?_).symm
  rw [show colData1 (⟨120, by decide⟩ : Fin 148)
        ((colE1 ⟨77, by decide⟩ 9 (transLenTr ⟨77, by decide⟩ 9 hp) : ↥(reps ⟨77, by decide⟩)) : Coordinate 1)
        T120_77 = colFn colCertDiv_120_77_9.D1 (m := 5) from colCertDiv_120_77_9.bind1,
    show colData2 (⟨120, by decide⟩ : Fin 148)
        ((colE2 ⟨77, by decide⟩ 9 hp : ↥(Q2.reps ⟨77, by decide⟩)) : Coordinate 2)
        Q2.T120_77_2 = colFn colCertDiv_120_77_9.D2 (m := 5) from colCertDiv_120_77_9.bind2]
  rw [alnId_120 j hj]
  exact fastcode_of_div ⟨120, by decide⟩ _ _ _
    ((alnId_120 j hj) ▸ Q2.listedAt (⟨120, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨120, by decide⟩ : Fin 148) hj hq).1) colCertDiv_120_77_9_match


theorem leaf_120_77_10 (hp : 10 < (Q2.transData.getD 77 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨77, by decide⟩ : Fin 148)) (colE2 ⟨77, by decide⟩ 10 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨77, by decide⟩ : Fin 148))
        (colE1 ⟨77, by decide⟩ 10 (transLenTr ⟨77, by decide⟩ 10 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨120, by decide⟩ : Fin 148) ⟨77, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨77, by decide⟩ 10 (transLenTr ⟨77, by decide⟩ 10 hp)) T120_77
      hfix120_77 hinj120_77 hcardT120_77
      (fun i => conj_mem_of_fixedPoints _ _ (T120_77 i) (hfix120_77 i) _)
      ⟨120, by decide⟩ ⟨77, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨77, by decide⟩ 10 hp) Q2.T120_77_2 Q2.hfix120_77_2 Q2.hinj120_77_2
      Q2.hcardT120_77_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_77_2 i) (Q2.hfix120_77_2 i) _)
      ?_).symm
  rw [show colData1 (⟨120, by decide⟩ : Fin 148)
        ((colE1 ⟨77, by decide⟩ 10 (transLenTr ⟨77, by decide⟩ 10 hp) : ↥(reps ⟨77, by decide⟩)) : Coordinate 1)
        T120_77 = colFn colCertDiv_120_77_10.D1 (m := 5) from colCertDiv_120_77_10.bind1,
    show colData2 (⟨120, by decide⟩ : Fin 148)
        ((colE2 ⟨77, by decide⟩ 10 hp : ↥(Q2.reps ⟨77, by decide⟩)) : Coordinate 2)
        Q2.T120_77_2 = colFn colCertDiv_120_77_10.D2 (m := 5) from colCertDiv_120_77_10.bind2]
  rw [alnId_120 j hj]
  exact fastcode_of_div ⟨120, by decide⟩ _ _ _
    ((alnId_120 j hj) ▸ Q2.listedAt (⟨120, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨120, by decide⟩ : Fin 148) hj hq).1) colCertDiv_120_77_10_match


theorem leaf_120_77_11 (hp : 11 < (Q2.transData.getD 77 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨77, by decide⟩ : Fin 148)) (colE2 ⟨77, by decide⟩ 11 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨77, by decide⟩ : Fin 148))
        (colE1 ⟨77, by decide⟩ 11 (transLenTr ⟨77, by decide⟩ 11 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨120, by decide⟩ : Fin 148) ⟨77, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨77, by decide⟩ 11 (transLenTr ⟨77, by decide⟩ 11 hp)) T120_77
      hfix120_77 hinj120_77 hcardT120_77
      (fun i => conj_mem_of_fixedPoints _ _ (T120_77 i) (hfix120_77 i) _)
      ⟨120, by decide⟩ ⟨77, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨77, by decide⟩ 11 hp) Q2.T120_77_2 Q2.hfix120_77_2 Q2.hinj120_77_2
      Q2.hcardT120_77_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_77_2 i) (Q2.hfix120_77_2 i) _)
      ?_).symm
  rw [show colData1 (⟨120, by decide⟩ : Fin 148)
        ((colE1 ⟨77, by decide⟩ 11 (transLenTr ⟨77, by decide⟩ 11 hp) : ↥(reps ⟨77, by decide⟩)) : Coordinate 1)
        T120_77 = colFn colCertDiv_120_77_11.D1 (m := 5) from colCertDiv_120_77_11.bind1,
    show colData2 (⟨120, by decide⟩ : Fin 148)
        ((colE2 ⟨77, by decide⟩ 11 hp : ↥(Q2.reps ⟨77, by decide⟩)) : Coordinate 2)
        Q2.T120_77_2 = colFn colCertDiv_120_77_11.D2 (m := 5) from colCertDiv_120_77_11.bind2]
  rw [alnId_120 j hj]
  exact fastcode_of_div ⟨120, by decide⟩ _ _ _
    ((alnId_120 j hj) ▸ Q2.listedAt (⟨120, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨120, by decide⟩ : Fin 148) hj hq).1) colCertDiv_120_77_11_match


theorem leaf_120_77_12 (hp : 12 < (Q2.transData.getD 77 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨77, by decide⟩ : Fin 148)) (colE2 ⟨77, by decide⟩ 12 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨77, by decide⟩ : Fin 148))
        (colE1 ⟨77, by decide⟩ 12 (transLenTr ⟨77, by decide⟩ 12 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨120, by decide⟩ : Fin 148) ⟨77, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨77, by decide⟩ 12 (transLenTr ⟨77, by decide⟩ 12 hp)) T120_77
      hfix120_77 hinj120_77 hcardT120_77
      (fun i => conj_mem_of_fixedPoints _ _ (T120_77 i) (hfix120_77 i) _)
      ⟨120, by decide⟩ ⟨77, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨77, by decide⟩ 12 hp) Q2.T120_77_2 Q2.hfix120_77_2 Q2.hinj120_77_2
      Q2.hcardT120_77_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_77_2 i) (Q2.hfix120_77_2 i) _)
      ?_).symm
  rw [show colData1 (⟨120, by decide⟩ : Fin 148)
        ((colE1 ⟨77, by decide⟩ 12 (transLenTr ⟨77, by decide⟩ 12 hp) : ↥(reps ⟨77, by decide⟩)) : Coordinate 1)
        T120_77 = colFn colCertDiv_120_77_12.D1 (m := 5) from colCertDiv_120_77_12.bind1,
    show colData2 (⟨120, by decide⟩ : Fin 148)
        ((colE2 ⟨77, by decide⟩ 12 hp : ↥(Q2.reps ⟨77, by decide⟩)) : Coordinate 2)
        Q2.T120_77_2 = colFn colCertDiv_120_77_12.D2 (m := 5) from colCertDiv_120_77_12.bind2]
  rw [alnId_120 j hj]
  exact fastcode_of_div ⟨120, by decide⟩ _ _ _
    ((alnId_120 j hj) ▸ Q2.listedAt (⟨120, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨120, by decide⟩ : Fin 148) hj hq).1) colCertDiv_120_77_12_match


theorem leaf_120_77_13 (hp : 13 < (Q2.transData.getD 77 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨77, by decide⟩ : Fin 148)) (colE2 ⟨77, by decide⟩ 13 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨77, by decide⟩ : Fin 148))
        (colE1 ⟨77, by decide⟩ 13 (transLenTr ⟨77, by decide⟩ 13 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨120, by decide⟩ : Fin 148) ⟨77, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨77, by decide⟩ 13 (transLenTr ⟨77, by decide⟩ 13 hp)) T120_77
      hfix120_77 hinj120_77 hcardT120_77
      (fun i => conj_mem_of_fixedPoints _ _ (T120_77 i) (hfix120_77 i) _)
      ⟨120, by decide⟩ ⟨77, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨77, by decide⟩ 13 hp) Q2.T120_77_2 Q2.hfix120_77_2 Q2.hinj120_77_2
      Q2.hcardT120_77_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_77_2 i) (Q2.hfix120_77_2 i) _)
      ?_).symm
  rw [show colData1 (⟨120, by decide⟩ : Fin 148)
        ((colE1 ⟨77, by decide⟩ 13 (transLenTr ⟨77, by decide⟩ 13 hp) : ↥(reps ⟨77, by decide⟩)) : Coordinate 1)
        T120_77 = colFn colCertDiv_120_77_13.D1 (m := 5) from colCertDiv_120_77_13.bind1,
    show colData2 (⟨120, by decide⟩ : Fin 148)
        ((colE2 ⟨77, by decide⟩ 13 hp : ↥(Q2.reps ⟨77, by decide⟩)) : Coordinate 2)
        Q2.T120_77_2 = colFn colCertDiv_120_77_13.D2 (m := 5) from colCertDiv_120_77_13.bind2]
  rw [alnId_120 j hj]
  exact fastcode_of_div ⟨120, by decide⟩ _ _ _
    ((alnId_120 j hj) ▸ Q2.listedAt (⟨120, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨120, by decide⟩ : Fin 148) hj hq).1) colCertDiv_120_77_13_match


theorem leaf_120_77_14 (hp : 14 < (Q2.transData.getD 77 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨77, by decide⟩ : Fin 148)) (colE2 ⟨77, by decide⟩ 14 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨77, by decide⟩ : Fin 148))
        (colE1 ⟨77, by decide⟩ 14 (transLenTr ⟨77, by decide⟩ 14 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨120, by decide⟩ : Fin 148) ⟨77, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨77, by decide⟩ 14 (transLenTr ⟨77, by decide⟩ 14 hp)) T120_77
      hfix120_77 hinj120_77 hcardT120_77
      (fun i => conj_mem_of_fixedPoints _ _ (T120_77 i) (hfix120_77 i) _)
      ⟨120, by decide⟩ ⟨77, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨77, by decide⟩ 14 hp) Q2.T120_77_2 Q2.hfix120_77_2 Q2.hinj120_77_2
      Q2.hcardT120_77_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_77_2 i) (Q2.hfix120_77_2 i) _)
      ?_).symm
  rw [show colData1 (⟨120, by decide⟩ : Fin 148)
        ((colE1 ⟨77, by decide⟩ 14 (transLenTr ⟨77, by decide⟩ 14 hp) : ↥(reps ⟨77, by decide⟩)) : Coordinate 1)
        T120_77 = colFn colCertDiv_120_77_14.D1 (m := 5) from colCertDiv_120_77_14.bind1,
    show colData2 (⟨120, by decide⟩ : Fin 148)
        ((colE2 ⟨77, by decide⟩ 14 hp : ↥(Q2.reps ⟨77, by decide⟩)) : Coordinate 2)
        Q2.T120_77_2 = colFn colCertDiv_120_77_14.D2 (m := 5) from colCertDiv_120_77_14.bind2]
  rw [alnId_120 j hj]
  exact fastcode_of_div ⟨120, by decide⟩ _ _ _
    ((alnId_120 j hj) ▸ Q2.listedAt (⟨120, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨120, by decide⟩ : Fin 148) hj hq).1) colCertDiv_120_77_14_match


theorem leaf_120_77_15 (hp : 15 < (Q2.transData.getD 77 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨77, by decide⟩ : Fin 148)) (colE2 ⟨77, by decide⟩ 15 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨77, by decide⟩ : Fin 148))
        (colE1 ⟨77, by decide⟩ 15 (transLenTr ⟨77, by decide⟩ 15 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨120, by decide⟩ : Fin 148) ⟨77, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨77, by decide⟩ 15 (transLenTr ⟨77, by decide⟩ 15 hp)) T120_77
      hfix120_77 hinj120_77 hcardT120_77
      (fun i => conj_mem_of_fixedPoints _ _ (T120_77 i) (hfix120_77 i) _)
      ⟨120, by decide⟩ ⟨77, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨77, by decide⟩ 15 hp) Q2.T120_77_2 Q2.hfix120_77_2 Q2.hinj120_77_2
      Q2.hcardT120_77_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_77_2 i) (Q2.hfix120_77_2 i) _)
      ?_).symm
  rw [show colData1 (⟨120, by decide⟩ : Fin 148)
        ((colE1 ⟨77, by decide⟩ 15 (transLenTr ⟨77, by decide⟩ 15 hp) : ↥(reps ⟨77, by decide⟩)) : Coordinate 1)
        T120_77 = colFn colCertDiv_120_77_15.D1 (m := 5) from colCertDiv_120_77_15.bind1,
    show colData2 (⟨120, by decide⟩ : Fin 148)
        ((colE2 ⟨77, by decide⟩ 15 hp : ↥(Q2.reps ⟨77, by decide⟩)) : Coordinate 2)
        Q2.T120_77_2 = colFn colCertDiv_120_77_15.D2 (m := 5) from colCertDiv_120_77_15.bind2]
  rw [alnId_120 j hj]
  exact fastcode_of_div ⟨120, by decide⟩ _ _ _
    ((alnId_120 j hj) ▸ Q2.listedAt (⟨120, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨120, by decide⟩ : Fin 148) hj hq).1) colCertDiv_120_77_15_match


theorem leaf_120_77_16 (hp : 16 < (Q2.transData.getD 77 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨77, by decide⟩ : Fin 148)) (colE2 ⟨77, by decide⟩ 16 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨77, by decide⟩ : Fin 148))
        (colE1 ⟨77, by decide⟩ 16 (transLenTr ⟨77, by decide⟩ 16 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨120, by decide⟩ : Fin 148) ⟨77, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨77, by decide⟩ 16 (transLenTr ⟨77, by decide⟩ 16 hp)) T120_77
      hfix120_77 hinj120_77 hcardT120_77
      (fun i => conj_mem_of_fixedPoints _ _ (T120_77 i) (hfix120_77 i) _)
      ⟨120, by decide⟩ ⟨77, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨77, by decide⟩ 16 hp) Q2.T120_77_2 Q2.hfix120_77_2 Q2.hinj120_77_2
      Q2.hcardT120_77_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_77_2 i) (Q2.hfix120_77_2 i) _)
      ?_).symm
  rw [show colData1 (⟨120, by decide⟩ : Fin 148)
        ((colE1 ⟨77, by decide⟩ 16 (transLenTr ⟨77, by decide⟩ 16 hp) : ↥(reps ⟨77, by decide⟩)) : Coordinate 1)
        T120_77 = colFn colCertDiv_120_77_16.D1 (m := 5) from colCertDiv_120_77_16.bind1,
    show colData2 (⟨120, by decide⟩ : Fin 148)
        ((colE2 ⟨77, by decide⟩ 16 hp : ↥(Q2.reps ⟨77, by decide⟩)) : Coordinate 2)
        Q2.T120_77_2 = colFn colCertDiv_120_77_16.D2 (m := 5) from colCertDiv_120_77_16.bind2]
  rw [alnId_120 j hj]
  exact fastcode_of_div ⟨120, by decide⟩ _ _ _
    ((alnId_120 j hj) ▸ Q2.listedAt (⟨120, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨120, by decide⟩ : Fin 148) hj hq).1) colCertDiv_120_77_16_match


theorem leaf_120_77_17 (hp : 17 < (Q2.transData.getD 77 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨77, by decide⟩ : Fin 148)) (colE2 ⟨77, by decide⟩ 17 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨77, by decide⟩ : Fin 148))
        (colE1 ⟨77, by decide⟩ 17 (transLenTr ⟨77, by decide⟩ 17 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨120, by decide⟩ : Fin 148) ⟨77, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨77, by decide⟩ 17 (transLenTr ⟨77, by decide⟩ 17 hp)) T120_77
      hfix120_77 hinj120_77 hcardT120_77
      (fun i => conj_mem_of_fixedPoints _ _ (T120_77 i) (hfix120_77 i) _)
      ⟨120, by decide⟩ ⟨77, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨77, by decide⟩ 17 hp) Q2.T120_77_2 Q2.hfix120_77_2 Q2.hinj120_77_2
      Q2.hcardT120_77_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_77_2 i) (Q2.hfix120_77_2 i) _)
      ?_).symm
  rw [show colData1 (⟨120, by decide⟩ : Fin 148)
        ((colE1 ⟨77, by decide⟩ 17 (transLenTr ⟨77, by decide⟩ 17 hp) : ↥(reps ⟨77, by decide⟩)) : Coordinate 1)
        T120_77 = colFn colCertDiv_120_77_17.D1 (m := 5) from colCertDiv_120_77_17.bind1,
    show colData2 (⟨120, by decide⟩ : Fin 148)
        ((colE2 ⟨77, by decide⟩ 17 hp : ↥(Q2.reps ⟨77, by decide⟩)) : Coordinate 2)
        Q2.T120_77_2 = colFn colCertDiv_120_77_17.D2 (m := 5) from colCertDiv_120_77_17.bind2]
  rw [alnId_120 j hj]
  exact fastcode_of_div ⟨120, by decide⟩ _ _ _
    ((alnId_120 j hj) ▸ Q2.listedAt (⟨120, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨120, by decide⟩ : Fin 148) hj hq).1) colCertDiv_120_77_17_match


theorem leaf_120_77_18 (hp : 18 < (Q2.transData.getD 77 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨77, by decide⟩ : Fin 148)) (colE2 ⟨77, by decide⟩ 18 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨77, by decide⟩ : Fin 148))
        (colE1 ⟨77, by decide⟩ 18 (transLenTr ⟨77, by decide⟩ 18 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨120, by decide⟩ : Fin 148) ⟨77, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨77, by decide⟩ 18 (transLenTr ⟨77, by decide⟩ 18 hp)) T120_77
      hfix120_77 hinj120_77 hcardT120_77
      (fun i => conj_mem_of_fixedPoints _ _ (T120_77 i) (hfix120_77 i) _)
      ⟨120, by decide⟩ ⟨77, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨77, by decide⟩ 18 hp) Q2.T120_77_2 Q2.hfix120_77_2 Q2.hinj120_77_2
      Q2.hcardT120_77_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_77_2 i) (Q2.hfix120_77_2 i) _)
      ?_).symm
  rw [show colData1 (⟨120, by decide⟩ : Fin 148)
        ((colE1 ⟨77, by decide⟩ 18 (transLenTr ⟨77, by decide⟩ 18 hp) : ↥(reps ⟨77, by decide⟩)) : Coordinate 1)
        T120_77 = colFn colCertDiv_120_77_18.D1 (m := 5) from colCertDiv_120_77_18.bind1,
    show colData2 (⟨120, by decide⟩ : Fin 148)
        ((colE2 ⟨77, by decide⟩ 18 hp : ↥(Q2.reps ⟨77, by decide⟩)) : Coordinate 2)
        Q2.T120_77_2 = colFn colCertDiv_120_77_18.D2 (m := 5) from colCertDiv_120_77_18.bind2]
  rw [alnId_120 j hj]
  exact fastcode_of_div ⟨120, by decide⟩ _ _ _
    ((alnId_120 j hj) ▸ Q2.listedAt (⟨120, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨120, by decide⟩ : Fin 148) hj hq).1) colCertDiv_120_77_18_match


theorem leaf_120_77_19 (hp : 19 < (Q2.transData.getD 77 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨77, by decide⟩ : Fin 148)) (colE2 ⟨77, by decide⟩ 19 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨77, by decide⟩ : Fin 148))
        (colE1 ⟨77, by decide⟩ 19 (transLenTr ⟨77, by decide⟩ 19 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨120, by decide⟩ : Fin 148) ⟨77, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨77, by decide⟩ 19 (transLenTr ⟨77, by decide⟩ 19 hp)) T120_77
      hfix120_77 hinj120_77 hcardT120_77
      (fun i => conj_mem_of_fixedPoints _ _ (T120_77 i) (hfix120_77 i) _)
      ⟨120, by decide⟩ ⟨77, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨77, by decide⟩ 19 hp) Q2.T120_77_2 Q2.hfix120_77_2 Q2.hinj120_77_2
      Q2.hcardT120_77_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_77_2 i) (Q2.hfix120_77_2 i) _)
      ?_).symm
  rw [show colData1 (⟨120, by decide⟩ : Fin 148)
        ((colE1 ⟨77, by decide⟩ 19 (transLenTr ⟨77, by decide⟩ 19 hp) : ↥(reps ⟨77, by decide⟩)) : Coordinate 1)
        T120_77 = colFn colCertDiv_120_77_19.D1 (m := 5) from colCertDiv_120_77_19.bind1,
    show colData2 (⟨120, by decide⟩ : Fin 148)
        ((colE2 ⟨77, by decide⟩ 19 hp : ↥(Q2.reps ⟨77, by decide⟩)) : Coordinate 2)
        Q2.T120_77_2 = colFn colCertDiv_120_77_19.D2 (m := 5) from colCertDiv_120_77_19.bind2]
  rw [alnId_120 j hj]
  exact fastcode_of_div ⟨120, by decide⟩ _ _ _
    ((alnId_120 j hj) ▸ Q2.listedAt (⟨120, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨120, by decide⟩ : Fin 148) hj hq).1) colCertDiv_120_77_19_match


theorem leaf_120_77_20 (hp : 20 < (Q2.transData.getD 77 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨77, by decide⟩ : Fin 148)) (colE2 ⟨77, by decide⟩ 20 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨77, by decide⟩ : Fin 148))
        (colE1 ⟨77, by decide⟩ 20 (transLenTr ⟨77, by decide⟩ 20 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨120, by decide⟩ : Fin 148) ⟨77, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨77, by decide⟩ 20 (transLenTr ⟨77, by decide⟩ 20 hp)) T120_77
      hfix120_77 hinj120_77 hcardT120_77
      (fun i => conj_mem_of_fixedPoints _ _ (T120_77 i) (hfix120_77 i) _)
      ⟨120, by decide⟩ ⟨77, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨77, by decide⟩ 20 hp) Q2.T120_77_2 Q2.hfix120_77_2 Q2.hinj120_77_2
      Q2.hcardT120_77_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_77_2 i) (Q2.hfix120_77_2 i) _)
      ?_).symm
  rw [show colData1 (⟨120, by decide⟩ : Fin 148)
        ((colE1 ⟨77, by decide⟩ 20 (transLenTr ⟨77, by decide⟩ 20 hp) : ↥(reps ⟨77, by decide⟩)) : Coordinate 1)
        T120_77 = colFn colCertDiv_120_77_20.D1 (m := 5) from colCertDiv_120_77_20.bind1,
    show colData2 (⟨120, by decide⟩ : Fin 148)
        ((colE2 ⟨77, by decide⟩ 20 hp : ↥(Q2.reps ⟨77, by decide⟩)) : Coordinate 2)
        Q2.T120_77_2 = colFn colCertDiv_120_77_20.D2 (m := 5) from colCertDiv_120_77_20.bind2]
  rw [alnId_120 j hj]
  exact fastcode_of_div ⟨120, by decide⟩ _ _ _
    ((alnId_120 j hj) ▸ Q2.listedAt (⟨120, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨120, by decide⟩ : Fin 148) hj hq).1) colCertDiv_120_77_20_match


theorem leaf_120_77_21 (hp : 21 < (Q2.transData.getD 77 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨77, by decide⟩ : Fin 148)) (colE2 ⟨77, by decide⟩ 21 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨77, by decide⟩ : Fin 148))
        (colE1 ⟨77, by decide⟩ 21 (transLenTr ⟨77, by decide⟩ 21 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨120, by decide⟩ : Fin 148) ⟨77, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨77, by decide⟩ 21 (transLenTr ⟨77, by decide⟩ 21 hp)) T120_77
      hfix120_77 hinj120_77 hcardT120_77
      (fun i => conj_mem_of_fixedPoints _ _ (T120_77 i) (hfix120_77 i) _)
      ⟨120, by decide⟩ ⟨77, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨77, by decide⟩ 21 hp) Q2.T120_77_2 Q2.hfix120_77_2 Q2.hinj120_77_2
      Q2.hcardT120_77_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_77_2 i) (Q2.hfix120_77_2 i) _)
      ?_).symm
  rw [show colData1 (⟨120, by decide⟩ : Fin 148)
        ((colE1 ⟨77, by decide⟩ 21 (transLenTr ⟨77, by decide⟩ 21 hp) : ↥(reps ⟨77, by decide⟩)) : Coordinate 1)
        T120_77 = colFn colCertDiv_120_77_21.D1 (m := 5) from colCertDiv_120_77_21.bind1,
    show colData2 (⟨120, by decide⟩ : Fin 148)
        ((colE2 ⟨77, by decide⟩ 21 hp : ↥(Q2.reps ⟨77, by decide⟩)) : Coordinate 2)
        Q2.T120_77_2 = colFn colCertDiv_120_77_21.D2 (m := 5) from colCertDiv_120_77_21.bind2]
  rw [alnId_120 j hj]
  exact fastcode_of_div ⟨120, by decide⟩ _ _ _
    ((alnId_120 j hj) ▸ Q2.listedAt (⟨120, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨120, by decide⟩ : Fin 148) hj hq).1) colCertDiv_120_77_21_match


theorem leaf_120_77_22 (hp : 22 < (Q2.transData.getD 77 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨77, by decide⟩ : Fin 148)) (colE2 ⟨77, by decide⟩ 22 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨77, by decide⟩ : Fin 148))
        (colE1 ⟨77, by decide⟩ 22 (transLenTr ⟨77, by decide⟩ 22 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨120, by decide⟩ : Fin 148) ⟨77, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨77, by decide⟩ 22 (transLenTr ⟨77, by decide⟩ 22 hp)) T120_77
      hfix120_77 hinj120_77 hcardT120_77
      (fun i => conj_mem_of_fixedPoints _ _ (T120_77 i) (hfix120_77 i) _)
      ⟨120, by decide⟩ ⟨77, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨77, by decide⟩ 22 hp) Q2.T120_77_2 Q2.hfix120_77_2 Q2.hinj120_77_2
      Q2.hcardT120_77_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_77_2 i) (Q2.hfix120_77_2 i) _)
      ?_).symm
  rw [show colData1 (⟨120, by decide⟩ : Fin 148)
        ((colE1 ⟨77, by decide⟩ 22 (transLenTr ⟨77, by decide⟩ 22 hp) : ↥(reps ⟨77, by decide⟩)) : Coordinate 1)
        T120_77 = colFn colCertDiv_120_77_22.D1 (m := 5) from colCertDiv_120_77_22.bind1,
    show colData2 (⟨120, by decide⟩ : Fin 148)
        ((colE2 ⟨77, by decide⟩ 22 hp : ↥(Q2.reps ⟨77, by decide⟩)) : Coordinate 2)
        Q2.T120_77_2 = colFn colCertDiv_120_77_22.D2 (m := 5) from colCertDiv_120_77_22.bind2]
  rw [alnId_120 j hj]
  exact fastcode_of_div ⟨120, by decide⟩ _ _ _
    ((alnId_120 j hj) ▸ Q2.listedAt (⟨120, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨120, by decide⟩ : Fin 148) hj hq).1) colCertDiv_120_77_22_match


theorem leaf_120_77_23 (hp : 23 < (Q2.transData.getD 77 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨77, by decide⟩ : Fin 148)) (colE2 ⟨77, by decide⟩ 23 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨77, by decide⟩ : Fin 148))
        (colE1 ⟨77, by decide⟩ 23 (transLenTr ⟨77, by decide⟩ 23 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨120, by decide⟩ : Fin 148) ⟨77, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨77, by decide⟩ 23 (transLenTr ⟨77, by decide⟩ 23 hp)) T120_77
      hfix120_77 hinj120_77 hcardT120_77
      (fun i => conj_mem_of_fixedPoints _ _ (T120_77 i) (hfix120_77 i) _)
      ⟨120, by decide⟩ ⟨77, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨77, by decide⟩ 23 hp) Q2.T120_77_2 Q2.hfix120_77_2 Q2.hinj120_77_2
      Q2.hcardT120_77_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_77_2 i) (Q2.hfix120_77_2 i) _)
      ?_).symm
  rw [show colData1 (⟨120, by decide⟩ : Fin 148)
        ((colE1 ⟨77, by decide⟩ 23 (transLenTr ⟨77, by decide⟩ 23 hp) : ↥(reps ⟨77, by decide⟩)) : Coordinate 1)
        T120_77 = colFn colCertDiv_120_77_23.D1 (m := 5) from colCertDiv_120_77_23.bind1,
    show colData2 (⟨120, by decide⟩ : Fin 148)
        ((colE2 ⟨77, by decide⟩ 23 hp : ↥(Q2.reps ⟨77, by decide⟩)) : Coordinate 2)
        Q2.T120_77_2 = colFn colCertDiv_120_77_23.D2 (m := 5) from colCertDiv_120_77_23.bind2]
  rw [alnId_120 j hj]
  exact fastcode_of_div ⟨120, by decide⟩ _ _ _
    ((alnId_120 j hj) ▸ Q2.listedAt (⟨120, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨120, by decide⟩ : Fin 148) hj hq).1) colCertDiv_120_77_23_match


theorem leaf_120_77_24 (hp : 24 < (Q2.transData.getD 77 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨77, by decide⟩ : Fin 148)) (colE2 ⟨77, by decide⟩ 24 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨77, by decide⟩ : Fin 148))
        (colE1 ⟨77, by decide⟩ 24 (transLenTr ⟨77, by decide⟩ 24 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨120, by decide⟩ : Fin 148) ⟨77, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨77, by decide⟩ 24 (transLenTr ⟨77, by decide⟩ 24 hp)) T120_77
      hfix120_77 hinj120_77 hcardT120_77
      (fun i => conj_mem_of_fixedPoints _ _ (T120_77 i) (hfix120_77 i) _)
      ⟨120, by decide⟩ ⟨77, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨77, by decide⟩ 24 hp) Q2.T120_77_2 Q2.hfix120_77_2 Q2.hinj120_77_2
      Q2.hcardT120_77_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_77_2 i) (Q2.hfix120_77_2 i) _)
      ?_).symm
  rw [show colData1 (⟨120, by decide⟩ : Fin 148)
        ((colE1 ⟨77, by decide⟩ 24 (transLenTr ⟨77, by decide⟩ 24 hp) : ↥(reps ⟨77, by decide⟩)) : Coordinate 1)
        T120_77 = colFn colCertDiv_120_77_24.D1 (m := 5) from colCertDiv_120_77_24.bind1,
    show colData2 (⟨120, by decide⟩ : Fin 148)
        ((colE2 ⟨77, by decide⟩ 24 hp : ↥(Q2.reps ⟨77, by decide⟩)) : Coordinate 2)
        Q2.T120_77_2 = colFn colCertDiv_120_77_24.D2 (m := 5) from colCertDiv_120_77_24.bind2]
  rw [alnId_120 j hj]
  exact fastcode_of_div ⟨120, by decide⟩ _ _ _
    ((alnId_120 j hj) ▸ Q2.listedAt (⟨120, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨120, by decide⟩ : Fin 148) hj hq).1) colCertDiv_120_77_24_match


theorem leaf_120_78_0 (hp : 0 < (Q2.transData.getD 78 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨78, by decide⟩ : Fin 148)) (colE2 ⟨78, by decide⟩ 0 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨78, by decide⟩ : Fin 148))
        (colE1 ⟨78, by decide⟩ 0 (transLenTr ⟨78, by decide⟩ 0 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨78, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨78, by decide⟩ 0 (transLenTr ⟨78, by decide⟩ 0 hp)) T120_78
      hfix120_78 hinj120_78 hcardT120_78
      (fun i => conj_mem_of_fixedPoints _ _ (T120_78 i) (hfix120_78 i) _)
      ⟨120, by decide⟩ ⟨78, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨78, by decide⟩ 0 hp) Q2.T120_78_2 Q2.hfix120_78_2 Q2.hinj120_78_2
      Q2.hcardT120_78_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_78_2 i) (Q2.hfix120_78_2 i) _)
      colCert_120_78_0.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_78_1 (hp : 1 < (Q2.transData.getD 78 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨78, by decide⟩ : Fin 148)) (colE2 ⟨78, by decide⟩ 1 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨78, by decide⟩ : Fin 148))
        (colE1 ⟨78, by decide⟩ 1 (transLenTr ⟨78, by decide⟩ 1 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨78, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨78, by decide⟩ 1 (transLenTr ⟨78, by decide⟩ 1 hp)) T120_78
      hfix120_78 hinj120_78 hcardT120_78
      (fun i => conj_mem_of_fixedPoints _ _ (T120_78 i) (hfix120_78 i) _)
      ⟨120, by decide⟩ ⟨78, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨78, by decide⟩ 1 hp) Q2.T120_78_2 Q2.hfix120_78_2 Q2.hinj120_78_2
      Q2.hcardT120_78_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_78_2 i) (Q2.hfix120_78_2 i) _)
      colCert_120_78_1.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_78_2 (hp : 2 < (Q2.transData.getD 78 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨78, by decide⟩ : Fin 148)) (colE2 ⟨78, by decide⟩ 2 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨78, by decide⟩ : Fin 148))
        (colE1 ⟨78, by decide⟩ 2 (transLenTr ⟨78, by decide⟩ 2 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨78, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨78, by decide⟩ 2 (transLenTr ⟨78, by decide⟩ 2 hp)) T120_78
      hfix120_78 hinj120_78 hcardT120_78
      (fun i => conj_mem_of_fixedPoints _ _ (T120_78 i) (hfix120_78 i) _)
      ⟨120, by decide⟩ ⟨78, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨78, by decide⟩ 2 hp) Q2.T120_78_2 Q2.hfix120_78_2 Q2.hinj120_78_2
      Q2.hcardT120_78_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_78_2 i) (Q2.hfix120_78_2 i) _)
      colCert_120_78_2.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_78_3 (hp : 3 < (Q2.transData.getD 78 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨78, by decide⟩ : Fin 148)) (colE2 ⟨78, by decide⟩ 3 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨78, by decide⟩ : Fin 148))
        (colE1 ⟨78, by decide⟩ 3 (transLenTr ⟨78, by decide⟩ 3 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨78, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨78, by decide⟩ 3 (transLenTr ⟨78, by decide⟩ 3 hp)) T120_78
      hfix120_78 hinj120_78 hcardT120_78
      (fun i => conj_mem_of_fixedPoints _ _ (T120_78 i) (hfix120_78 i) _)
      ⟨120, by decide⟩ ⟨78, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨78, by decide⟩ 3 hp) Q2.T120_78_2 Q2.hfix120_78_2 Q2.hinj120_78_2
      Q2.hcardT120_78_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_78_2 i) (Q2.hfix120_78_2 i) _)
      colCert_120_78_3.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_78_4 (hp : 4 < (Q2.transData.getD 78 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨78, by decide⟩ : Fin 148)) (colE2 ⟨78, by decide⟩ 4 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨78, by decide⟩ : Fin 148))
        (colE1 ⟨78, by decide⟩ 4 (transLenTr ⟨78, by decide⟩ 4 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨78, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨78, by decide⟩ 4 (transLenTr ⟨78, by decide⟩ 4 hp)) T120_78
      hfix120_78 hinj120_78 hcardT120_78
      (fun i => conj_mem_of_fixedPoints _ _ (T120_78 i) (hfix120_78 i) _)
      ⟨120, by decide⟩ ⟨78, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨78, by decide⟩ 4 hp) Q2.T120_78_2 Q2.hfix120_78_2 Q2.hinj120_78_2
      Q2.hcardT120_78_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_78_2 i) (Q2.hfix120_78_2 i) _)
      colCert_120_78_4.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_78_5 (hp : 5 < (Q2.transData.getD 78 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨78, by decide⟩ : Fin 148)) (colE2 ⟨78, by decide⟩ 5 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨78, by decide⟩ : Fin 148))
        (colE1 ⟨78, by decide⟩ 5 (transLenTr ⟨78, by decide⟩ 5 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨120, by decide⟩ : Fin 148) ⟨78, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨78, by decide⟩ 5 (transLenTr ⟨78, by decide⟩ 5 hp)) T120_78
      hfix120_78 hinj120_78 hcardT120_78
      (fun i => conj_mem_of_fixedPoints _ _ (T120_78 i) (hfix120_78 i) _)
      ⟨120, by decide⟩ ⟨78, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨78, by decide⟩ 5 hp) Q2.T120_78_2 Q2.hfix120_78_2 Q2.hinj120_78_2
      Q2.hcardT120_78_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_78_2 i) (Q2.hfix120_78_2 i) _)
      ?_).symm
  rw [show colData1 (⟨120, by decide⟩ : Fin 148)
        ((colE1 ⟨78, by decide⟩ 5 (transLenTr ⟨78, by decide⟩ 5 hp) : ↥(reps ⟨78, by decide⟩)) : Coordinate 1)
        T120_78 = colFn colCertDiv_120_78_5.D1 (m := 5) from colCertDiv_120_78_5.bind1,
    show colData2 (⟨120, by decide⟩ : Fin 148)
        ((colE2 ⟨78, by decide⟩ 5 hp : ↥(Q2.reps ⟨78, by decide⟩)) : Coordinate 2)
        Q2.T120_78_2 = colFn colCertDiv_120_78_5.D2 (m := 5) from colCertDiv_120_78_5.bind2]
  rw [alnId_120 j hj]
  exact fastcode_of_div ⟨120, by decide⟩ _ _ _
    ((alnId_120 j hj) ▸ Q2.listedAt (⟨120, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨120, by decide⟩ : Fin 148) hj hq).1) colCertDiv_120_78_5_match


theorem leaf_120_78_6 (hp : 6 < (Q2.transData.getD 78 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨78, by decide⟩ : Fin 148)) (colE2 ⟨78, by decide⟩ 6 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨78, by decide⟩ : Fin 148))
        (colE1 ⟨78, by decide⟩ 6 (transLenTr ⟨78, by decide⟩ 6 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨120, by decide⟩ : Fin 148) ⟨78, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨78, by decide⟩ 6 (transLenTr ⟨78, by decide⟩ 6 hp)) T120_78
      hfix120_78 hinj120_78 hcardT120_78
      (fun i => conj_mem_of_fixedPoints _ _ (T120_78 i) (hfix120_78 i) _)
      ⟨120, by decide⟩ ⟨78, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨78, by decide⟩ 6 hp) Q2.T120_78_2 Q2.hfix120_78_2 Q2.hinj120_78_2
      Q2.hcardT120_78_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_78_2 i) (Q2.hfix120_78_2 i) _)
      ?_).symm
  rw [show colData1 (⟨120, by decide⟩ : Fin 148)
        ((colE1 ⟨78, by decide⟩ 6 (transLenTr ⟨78, by decide⟩ 6 hp) : ↥(reps ⟨78, by decide⟩)) : Coordinate 1)
        T120_78 = colFn colCertDiv_120_78_6.D1 (m := 5) from colCertDiv_120_78_6.bind1,
    show colData2 (⟨120, by decide⟩ : Fin 148)
        ((colE2 ⟨78, by decide⟩ 6 hp : ↥(Q2.reps ⟨78, by decide⟩)) : Coordinate 2)
        Q2.T120_78_2 = colFn colCertDiv_120_78_6.D2 (m := 5) from colCertDiv_120_78_6.bind2]
  rw [alnId_120 j hj]
  exact fastcode_of_div ⟨120, by decide⟩ _ _ _
    ((alnId_120 j hj) ▸ Q2.listedAt (⟨120, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨120, by decide⟩ : Fin 148) hj hq).1) colCertDiv_120_78_6_match


theorem leaf_120_78_7 (hp : 7 < (Q2.transData.getD 78 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨78, by decide⟩ : Fin 148)) (colE2 ⟨78, by decide⟩ 7 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨78, by decide⟩ : Fin 148))
        (colE1 ⟨78, by decide⟩ 7 (transLenTr ⟨78, by decide⟩ 7 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨120, by decide⟩ : Fin 148) ⟨78, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨78, by decide⟩ 7 (transLenTr ⟨78, by decide⟩ 7 hp)) T120_78
      hfix120_78 hinj120_78 hcardT120_78
      (fun i => conj_mem_of_fixedPoints _ _ (T120_78 i) (hfix120_78 i) _)
      ⟨120, by decide⟩ ⟨78, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨78, by decide⟩ 7 hp) Q2.T120_78_2 Q2.hfix120_78_2 Q2.hinj120_78_2
      Q2.hcardT120_78_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_78_2 i) (Q2.hfix120_78_2 i) _)
      ?_).symm
  rw [show colData1 (⟨120, by decide⟩ : Fin 148)
        ((colE1 ⟨78, by decide⟩ 7 (transLenTr ⟨78, by decide⟩ 7 hp) : ↥(reps ⟨78, by decide⟩)) : Coordinate 1)
        T120_78 = colFn colCertDiv_120_78_7.D1 (m := 5) from colCertDiv_120_78_7.bind1,
    show colData2 (⟨120, by decide⟩ : Fin 148)
        ((colE2 ⟨78, by decide⟩ 7 hp : ↥(Q2.reps ⟨78, by decide⟩)) : Coordinate 2)
        Q2.T120_78_2 = colFn colCertDiv_120_78_7.D2 (m := 5) from colCertDiv_120_78_7.bind2]
  rw [alnId_120 j hj]
  exact fastcode_of_div ⟨120, by decide⟩ _ _ _
    ((alnId_120 j hj) ▸ Q2.listedAt (⟨120, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨120, by decide⟩ : Fin 148) hj hq).1) colCertDiv_120_78_7_match


theorem leaf_120_78_8 (hp : 8 < (Q2.transData.getD 78 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨78, by decide⟩ : Fin 148)) (colE2 ⟨78, by decide⟩ 8 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨78, by decide⟩ : Fin 148))
        (colE1 ⟨78, by decide⟩ 8 (transLenTr ⟨78, by decide⟩ 8 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨120, by decide⟩ : Fin 148) ⟨78, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨78, by decide⟩ 8 (transLenTr ⟨78, by decide⟩ 8 hp)) T120_78
      hfix120_78 hinj120_78 hcardT120_78
      (fun i => conj_mem_of_fixedPoints _ _ (T120_78 i) (hfix120_78 i) _)
      ⟨120, by decide⟩ ⟨78, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨78, by decide⟩ 8 hp) Q2.T120_78_2 Q2.hfix120_78_2 Q2.hinj120_78_2
      Q2.hcardT120_78_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_78_2 i) (Q2.hfix120_78_2 i) _)
      ?_).symm
  rw [show colData1 (⟨120, by decide⟩ : Fin 148)
        ((colE1 ⟨78, by decide⟩ 8 (transLenTr ⟨78, by decide⟩ 8 hp) : ↥(reps ⟨78, by decide⟩)) : Coordinate 1)
        T120_78 = colFn colCertDiv_120_78_8.D1 (m := 5) from colCertDiv_120_78_8.bind1,
    show colData2 (⟨120, by decide⟩ : Fin 148)
        ((colE2 ⟨78, by decide⟩ 8 hp : ↥(Q2.reps ⟨78, by decide⟩)) : Coordinate 2)
        Q2.T120_78_2 = colFn colCertDiv_120_78_8.D2 (m := 5) from colCertDiv_120_78_8.bind2]
  rw [alnId_120 j hj]
  exact fastcode_of_div ⟨120, by decide⟩ _ _ _
    ((alnId_120 j hj) ▸ Q2.listedAt (⟨120, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨120, by decide⟩ : Fin 148) hj hq).1) colCertDiv_120_78_8_match


theorem leaf_120_78_9 (hp : 9 < (Q2.transData.getD 78 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨78, by decide⟩ : Fin 148)) (colE2 ⟨78, by decide⟩ 9 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨78, by decide⟩ : Fin 148))
        (colE1 ⟨78, by decide⟩ 9 (transLenTr ⟨78, by decide⟩ 9 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨120, by decide⟩ : Fin 148) ⟨78, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨78, by decide⟩ 9 (transLenTr ⟨78, by decide⟩ 9 hp)) T120_78
      hfix120_78 hinj120_78 hcardT120_78
      (fun i => conj_mem_of_fixedPoints _ _ (T120_78 i) (hfix120_78 i) _)
      ⟨120, by decide⟩ ⟨78, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨78, by decide⟩ 9 hp) Q2.T120_78_2 Q2.hfix120_78_2 Q2.hinj120_78_2
      Q2.hcardT120_78_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_78_2 i) (Q2.hfix120_78_2 i) _)
      ?_).symm
  rw [show colData1 (⟨120, by decide⟩ : Fin 148)
        ((colE1 ⟨78, by decide⟩ 9 (transLenTr ⟨78, by decide⟩ 9 hp) : ↥(reps ⟨78, by decide⟩)) : Coordinate 1)
        T120_78 = colFn colCertDiv_120_78_9.D1 (m := 5) from colCertDiv_120_78_9.bind1,
    show colData2 (⟨120, by decide⟩ : Fin 148)
        ((colE2 ⟨78, by decide⟩ 9 hp : ↥(Q2.reps ⟨78, by decide⟩)) : Coordinate 2)
        Q2.T120_78_2 = colFn colCertDiv_120_78_9.D2 (m := 5) from colCertDiv_120_78_9.bind2]
  rw [alnId_120 j hj]
  exact fastcode_of_div ⟨120, by decide⟩ _ _ _
    ((alnId_120 j hj) ▸ Q2.listedAt (⟨120, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨120, by decide⟩ : Fin 148) hj hq).1) colCertDiv_120_78_9_match


theorem leaf_120_78_10 (hp : 10 < (Q2.transData.getD 78 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨78, by decide⟩ : Fin 148)) (colE2 ⟨78, by decide⟩ 10 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨78, by decide⟩ : Fin 148))
        (colE1 ⟨78, by decide⟩ 10 (transLenTr ⟨78, by decide⟩ 10 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨120, by decide⟩ : Fin 148) ⟨78, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨78, by decide⟩ 10 (transLenTr ⟨78, by decide⟩ 10 hp)) T120_78
      hfix120_78 hinj120_78 hcardT120_78
      (fun i => conj_mem_of_fixedPoints _ _ (T120_78 i) (hfix120_78 i) _)
      ⟨120, by decide⟩ ⟨78, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨78, by decide⟩ 10 hp) Q2.T120_78_2 Q2.hfix120_78_2 Q2.hinj120_78_2
      Q2.hcardT120_78_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_78_2 i) (Q2.hfix120_78_2 i) _)
      ?_).symm
  rw [show colData1 (⟨120, by decide⟩ : Fin 148)
        ((colE1 ⟨78, by decide⟩ 10 (transLenTr ⟨78, by decide⟩ 10 hp) : ↥(reps ⟨78, by decide⟩)) : Coordinate 1)
        T120_78 = colFn colCertDiv_120_78_10.D1 (m := 5) from colCertDiv_120_78_10.bind1,
    show colData2 (⟨120, by decide⟩ : Fin 148)
        ((colE2 ⟨78, by decide⟩ 10 hp : ↥(Q2.reps ⟨78, by decide⟩)) : Coordinate 2)
        Q2.T120_78_2 = colFn colCertDiv_120_78_10.D2 (m := 5) from colCertDiv_120_78_10.bind2]
  rw [alnId_120 j hj]
  exact fastcode_of_div ⟨120, by decide⟩ _ _ _
    ((alnId_120 j hj) ▸ Q2.listedAt (⟨120, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨120, by decide⟩ : Fin 148) hj hq).1) colCertDiv_120_78_10_match


theorem leaf_120_78_11 (hp : 11 < (Q2.transData.getD 78 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨78, by decide⟩ : Fin 148)) (colE2 ⟨78, by decide⟩ 11 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨78, by decide⟩ : Fin 148))
        (colE1 ⟨78, by decide⟩ 11 (transLenTr ⟨78, by decide⟩ 11 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨120, by decide⟩ : Fin 148) ⟨78, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨78, by decide⟩ 11 (transLenTr ⟨78, by decide⟩ 11 hp)) T120_78
      hfix120_78 hinj120_78 hcardT120_78
      (fun i => conj_mem_of_fixedPoints _ _ (T120_78 i) (hfix120_78 i) _)
      ⟨120, by decide⟩ ⟨78, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨78, by decide⟩ 11 hp) Q2.T120_78_2 Q2.hfix120_78_2 Q2.hinj120_78_2
      Q2.hcardT120_78_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_78_2 i) (Q2.hfix120_78_2 i) _)
      ?_).symm
  rw [show colData1 (⟨120, by decide⟩ : Fin 148)
        ((colE1 ⟨78, by decide⟩ 11 (transLenTr ⟨78, by decide⟩ 11 hp) : ↥(reps ⟨78, by decide⟩)) : Coordinate 1)
        T120_78 = colFn colCertDiv_120_78_11.D1 (m := 5) from colCertDiv_120_78_11.bind1,
    show colData2 (⟨120, by decide⟩ : Fin 148)
        ((colE2 ⟨78, by decide⟩ 11 hp : ↥(Q2.reps ⟨78, by decide⟩)) : Coordinate 2)
        Q2.T120_78_2 = colFn colCertDiv_120_78_11.D2 (m := 5) from colCertDiv_120_78_11.bind2]
  rw [alnId_120 j hj]
  exact fastcode_of_div ⟨120, by decide⟩ _ _ _
    ((alnId_120 j hj) ▸ Q2.listedAt (⟨120, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨120, by decide⟩ : Fin 148) hj hq).1) colCertDiv_120_78_11_match


theorem leaf_120_78_12 (hp : 12 < (Q2.transData.getD 78 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨78, by decide⟩ : Fin 148)) (colE2 ⟨78, by decide⟩ 12 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨78, by decide⟩ : Fin 148))
        (colE1 ⟨78, by decide⟩ 12 (transLenTr ⟨78, by decide⟩ 12 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨120, by decide⟩ : Fin 148) ⟨78, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨78, by decide⟩ 12 (transLenTr ⟨78, by decide⟩ 12 hp)) T120_78
      hfix120_78 hinj120_78 hcardT120_78
      (fun i => conj_mem_of_fixedPoints _ _ (T120_78 i) (hfix120_78 i) _)
      ⟨120, by decide⟩ ⟨78, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨78, by decide⟩ 12 hp) Q2.T120_78_2 Q2.hfix120_78_2 Q2.hinj120_78_2
      Q2.hcardT120_78_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_78_2 i) (Q2.hfix120_78_2 i) _)
      ?_).symm
  rw [show colData1 (⟨120, by decide⟩ : Fin 148)
        ((colE1 ⟨78, by decide⟩ 12 (transLenTr ⟨78, by decide⟩ 12 hp) : ↥(reps ⟨78, by decide⟩)) : Coordinate 1)
        T120_78 = colFn colCertDiv_120_78_12.D1 (m := 5) from colCertDiv_120_78_12.bind1,
    show colData2 (⟨120, by decide⟩ : Fin 148)
        ((colE2 ⟨78, by decide⟩ 12 hp : ↥(Q2.reps ⟨78, by decide⟩)) : Coordinate 2)
        Q2.T120_78_2 = colFn colCertDiv_120_78_12.D2 (m := 5) from colCertDiv_120_78_12.bind2]
  rw [alnId_120 j hj]
  exact fastcode_of_div ⟨120, by decide⟩ _ _ _
    ((alnId_120 j hj) ▸ Q2.listedAt (⟨120, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨120, by decide⟩ : Fin 148) hj hq).1) colCertDiv_120_78_12_match


theorem leaf_120_78_13 (hp : 13 < (Q2.transData.getD 78 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨78, by decide⟩ : Fin 148)) (colE2 ⟨78, by decide⟩ 13 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨78, by decide⟩ : Fin 148))
        (colE1 ⟨78, by decide⟩ 13 (transLenTr ⟨78, by decide⟩ 13 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨120, by decide⟩ : Fin 148) ⟨78, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨78, by decide⟩ 13 (transLenTr ⟨78, by decide⟩ 13 hp)) T120_78
      hfix120_78 hinj120_78 hcardT120_78
      (fun i => conj_mem_of_fixedPoints _ _ (T120_78 i) (hfix120_78 i) _)
      ⟨120, by decide⟩ ⟨78, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨78, by decide⟩ 13 hp) Q2.T120_78_2 Q2.hfix120_78_2 Q2.hinj120_78_2
      Q2.hcardT120_78_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_78_2 i) (Q2.hfix120_78_2 i) _)
      ?_).symm
  rw [show colData1 (⟨120, by decide⟩ : Fin 148)
        ((colE1 ⟨78, by decide⟩ 13 (transLenTr ⟨78, by decide⟩ 13 hp) : ↥(reps ⟨78, by decide⟩)) : Coordinate 1)
        T120_78 = colFn colCertDiv_120_78_13.D1 (m := 5) from colCertDiv_120_78_13.bind1,
    show colData2 (⟨120, by decide⟩ : Fin 148)
        ((colE2 ⟨78, by decide⟩ 13 hp : ↥(Q2.reps ⟨78, by decide⟩)) : Coordinate 2)
        Q2.T120_78_2 = colFn colCertDiv_120_78_13.D2 (m := 5) from colCertDiv_120_78_13.bind2]
  rw [alnId_120 j hj]
  exact fastcode_of_div ⟨120, by decide⟩ _ _ _
    ((alnId_120 j hj) ▸ Q2.listedAt (⟨120, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨120, by decide⟩ : Fin 148) hj hq).1) colCertDiv_120_78_13_match


theorem leaf_120_78_14 (hp : 14 < (Q2.transData.getD 78 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨78, by decide⟩ : Fin 148)) (colE2 ⟨78, by decide⟩ 14 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨78, by decide⟩ : Fin 148))
        (colE1 ⟨78, by decide⟩ 14 (transLenTr ⟨78, by decide⟩ 14 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨120, by decide⟩ : Fin 148) ⟨78, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨78, by decide⟩ 14 (transLenTr ⟨78, by decide⟩ 14 hp)) T120_78
      hfix120_78 hinj120_78 hcardT120_78
      (fun i => conj_mem_of_fixedPoints _ _ (T120_78 i) (hfix120_78 i) _)
      ⟨120, by decide⟩ ⟨78, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨78, by decide⟩ 14 hp) Q2.T120_78_2 Q2.hfix120_78_2 Q2.hinj120_78_2
      Q2.hcardT120_78_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_78_2 i) (Q2.hfix120_78_2 i) _)
      ?_).symm
  rw [show colData1 (⟨120, by decide⟩ : Fin 148)
        ((colE1 ⟨78, by decide⟩ 14 (transLenTr ⟨78, by decide⟩ 14 hp) : ↥(reps ⟨78, by decide⟩)) : Coordinate 1)
        T120_78 = colFn colCertDiv_120_78_14.D1 (m := 5) from colCertDiv_120_78_14.bind1,
    show colData2 (⟨120, by decide⟩ : Fin 148)
        ((colE2 ⟨78, by decide⟩ 14 hp : ↥(Q2.reps ⟨78, by decide⟩)) : Coordinate 2)
        Q2.T120_78_2 = colFn colCertDiv_120_78_14.D2 (m := 5) from colCertDiv_120_78_14.bind2]
  rw [alnId_120 j hj]
  exact fastcode_of_div ⟨120, by decide⟩ _ _ _
    ((alnId_120 j hj) ▸ Q2.listedAt (⟨120, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨120, by decide⟩ : Fin 148) hj hq).1) colCertDiv_120_78_14_match


theorem leaf_120_78_15 (hp : 15 < (Q2.transData.getD 78 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨78, by decide⟩ : Fin 148)) (colE2 ⟨78, by decide⟩ 15 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨78, by decide⟩ : Fin 148))
        (colE1 ⟨78, by decide⟩ 15 (transLenTr ⟨78, by decide⟩ 15 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨120, by decide⟩ : Fin 148) ⟨78, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨78, by decide⟩ 15 (transLenTr ⟨78, by decide⟩ 15 hp)) T120_78
      hfix120_78 hinj120_78 hcardT120_78
      (fun i => conj_mem_of_fixedPoints _ _ (T120_78 i) (hfix120_78 i) _)
      ⟨120, by decide⟩ ⟨78, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨78, by decide⟩ 15 hp) Q2.T120_78_2 Q2.hfix120_78_2 Q2.hinj120_78_2
      Q2.hcardT120_78_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_78_2 i) (Q2.hfix120_78_2 i) _)
      ?_).symm
  rw [show colData1 (⟨120, by decide⟩ : Fin 148)
        ((colE1 ⟨78, by decide⟩ 15 (transLenTr ⟨78, by decide⟩ 15 hp) : ↥(reps ⟨78, by decide⟩)) : Coordinate 1)
        T120_78 = colFn colCertDiv_120_78_15.D1 (m := 5) from colCertDiv_120_78_15.bind1,
    show colData2 (⟨120, by decide⟩ : Fin 148)
        ((colE2 ⟨78, by decide⟩ 15 hp : ↥(Q2.reps ⟨78, by decide⟩)) : Coordinate 2)
        Q2.T120_78_2 = colFn colCertDiv_120_78_15.D2 (m := 5) from colCertDiv_120_78_15.bind2]
  rw [alnId_120 j hj]
  exact fastcode_of_div ⟨120, by decide⟩ _ _ _
    ((alnId_120 j hj) ▸ Q2.listedAt (⟨120, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨120, by decide⟩ : Fin 148) hj hq).1) colCertDiv_120_78_15_match


theorem leaf_120_78_16 (hp : 16 < (Q2.transData.getD 78 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨78, by decide⟩ : Fin 148)) (colE2 ⟨78, by decide⟩ 16 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨78, by decide⟩ : Fin 148))
        (colE1 ⟨78, by decide⟩ 16 (transLenTr ⟨78, by decide⟩ 16 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨120, by decide⟩ : Fin 148) ⟨78, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨78, by decide⟩ 16 (transLenTr ⟨78, by decide⟩ 16 hp)) T120_78
      hfix120_78 hinj120_78 hcardT120_78
      (fun i => conj_mem_of_fixedPoints _ _ (T120_78 i) (hfix120_78 i) _)
      ⟨120, by decide⟩ ⟨78, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨78, by decide⟩ 16 hp) Q2.T120_78_2 Q2.hfix120_78_2 Q2.hinj120_78_2
      Q2.hcardT120_78_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_78_2 i) (Q2.hfix120_78_2 i) _)
      ?_).symm
  rw [show colData1 (⟨120, by decide⟩ : Fin 148)
        ((colE1 ⟨78, by decide⟩ 16 (transLenTr ⟨78, by decide⟩ 16 hp) : ↥(reps ⟨78, by decide⟩)) : Coordinate 1)
        T120_78 = colFn colCertDiv_120_78_16.D1 (m := 5) from colCertDiv_120_78_16.bind1,
    show colData2 (⟨120, by decide⟩ : Fin 148)
        ((colE2 ⟨78, by decide⟩ 16 hp : ↥(Q2.reps ⟨78, by decide⟩)) : Coordinate 2)
        Q2.T120_78_2 = colFn colCertDiv_120_78_16.D2 (m := 5) from colCertDiv_120_78_16.bind2]
  rw [alnId_120 j hj]
  exact fastcode_of_div ⟨120, by decide⟩ _ _ _
    ((alnId_120 j hj) ▸ Q2.listedAt (⟨120, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨120, by decide⟩ : Fin 148) hj hq).1) colCertDiv_120_78_16_match


theorem leaf_120_78_17 (hp : 17 < (Q2.transData.getD 78 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨78, by decide⟩ : Fin 148)) (colE2 ⟨78, by decide⟩ 17 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨78, by decide⟩ : Fin 148))
        (colE1 ⟨78, by decide⟩ 17 (transLenTr ⟨78, by decide⟩ 17 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨120, by decide⟩ : Fin 148) ⟨78, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨78, by decide⟩ 17 (transLenTr ⟨78, by decide⟩ 17 hp)) T120_78
      hfix120_78 hinj120_78 hcardT120_78
      (fun i => conj_mem_of_fixedPoints _ _ (T120_78 i) (hfix120_78 i) _)
      ⟨120, by decide⟩ ⟨78, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨78, by decide⟩ 17 hp) Q2.T120_78_2 Q2.hfix120_78_2 Q2.hinj120_78_2
      Q2.hcardT120_78_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_78_2 i) (Q2.hfix120_78_2 i) _)
      ?_).symm
  rw [show colData1 (⟨120, by decide⟩ : Fin 148)
        ((colE1 ⟨78, by decide⟩ 17 (transLenTr ⟨78, by decide⟩ 17 hp) : ↥(reps ⟨78, by decide⟩)) : Coordinate 1)
        T120_78 = colFn colCertDiv_120_78_17.D1 (m := 5) from colCertDiv_120_78_17.bind1,
    show colData2 (⟨120, by decide⟩ : Fin 148)
        ((colE2 ⟨78, by decide⟩ 17 hp : ↥(Q2.reps ⟨78, by decide⟩)) : Coordinate 2)
        Q2.T120_78_2 = colFn colCertDiv_120_78_17.D2 (m := 5) from colCertDiv_120_78_17.bind2]
  rw [alnId_120 j hj]
  exact fastcode_of_div ⟨120, by decide⟩ _ _ _
    ((alnId_120 j hj) ▸ Q2.listedAt (⟨120, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨120, by decide⟩ : Fin 148) hj hq).1) colCertDiv_120_78_17_match


theorem leaf_120_78_18 (hp : 18 < (Q2.transData.getD 78 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨78, by decide⟩ : Fin 148)) (colE2 ⟨78, by decide⟩ 18 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨78, by decide⟩ : Fin 148))
        (colE1 ⟨78, by decide⟩ 18 (transLenTr ⟨78, by decide⟩ 18 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨120, by decide⟩ : Fin 148) ⟨78, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨78, by decide⟩ 18 (transLenTr ⟨78, by decide⟩ 18 hp)) T120_78
      hfix120_78 hinj120_78 hcardT120_78
      (fun i => conj_mem_of_fixedPoints _ _ (T120_78 i) (hfix120_78 i) _)
      ⟨120, by decide⟩ ⟨78, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨78, by decide⟩ 18 hp) Q2.T120_78_2 Q2.hfix120_78_2 Q2.hinj120_78_2
      Q2.hcardT120_78_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_78_2 i) (Q2.hfix120_78_2 i) _)
      ?_).symm
  rw [show colData1 (⟨120, by decide⟩ : Fin 148)
        ((colE1 ⟨78, by decide⟩ 18 (transLenTr ⟨78, by decide⟩ 18 hp) : ↥(reps ⟨78, by decide⟩)) : Coordinate 1)
        T120_78 = colFn colCertDiv_120_78_18.D1 (m := 5) from colCertDiv_120_78_18.bind1,
    show colData2 (⟨120, by decide⟩ : Fin 148)
        ((colE2 ⟨78, by decide⟩ 18 hp : ↥(Q2.reps ⟨78, by decide⟩)) : Coordinate 2)
        Q2.T120_78_2 = colFn colCertDiv_120_78_18.D2 (m := 5) from colCertDiv_120_78_18.bind2]
  rw [alnId_120 j hj]
  exact fastcode_of_div ⟨120, by decide⟩ _ _ _
    ((alnId_120 j hj) ▸ Q2.listedAt (⟨120, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨120, by decide⟩ : Fin 148) hj hq).1) colCertDiv_120_78_18_match


theorem leaf_120_78_19 (hp : 19 < (Q2.transData.getD 78 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨78, by decide⟩ : Fin 148)) (colE2 ⟨78, by decide⟩ 19 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨78, by decide⟩ : Fin 148))
        (colE1 ⟨78, by decide⟩ 19 (transLenTr ⟨78, by decide⟩ 19 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨120, by decide⟩ : Fin 148) ⟨78, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨78, by decide⟩ 19 (transLenTr ⟨78, by decide⟩ 19 hp)) T120_78
      hfix120_78 hinj120_78 hcardT120_78
      (fun i => conj_mem_of_fixedPoints _ _ (T120_78 i) (hfix120_78 i) _)
      ⟨120, by decide⟩ ⟨78, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨78, by decide⟩ 19 hp) Q2.T120_78_2 Q2.hfix120_78_2 Q2.hinj120_78_2
      Q2.hcardT120_78_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_78_2 i) (Q2.hfix120_78_2 i) _)
      ?_).symm
  rw [show colData1 (⟨120, by decide⟩ : Fin 148)
        ((colE1 ⟨78, by decide⟩ 19 (transLenTr ⟨78, by decide⟩ 19 hp) : ↥(reps ⟨78, by decide⟩)) : Coordinate 1)
        T120_78 = colFn colCertDiv_120_78_19.D1 (m := 5) from colCertDiv_120_78_19.bind1,
    show colData2 (⟨120, by decide⟩ : Fin 148)
        ((colE2 ⟨78, by decide⟩ 19 hp : ↥(Q2.reps ⟨78, by decide⟩)) : Coordinate 2)
        Q2.T120_78_2 = colFn colCertDiv_120_78_19.D2 (m := 5) from colCertDiv_120_78_19.bind2]
  rw [alnId_120 j hj]
  exact fastcode_of_div ⟨120, by decide⟩ _ _ _
    ((alnId_120 j hj) ▸ Q2.listedAt (⟨120, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨120, by decide⟩ : Fin 148) hj hq).1) colCertDiv_120_78_19_match


theorem leaf_120_78_20 (hp : 20 < (Q2.transData.getD 78 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨78, by decide⟩ : Fin 148)) (colE2 ⟨78, by decide⟩ 20 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨78, by decide⟩ : Fin 148))
        (colE1 ⟨78, by decide⟩ 20 (transLenTr ⟨78, by decide⟩ 20 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨120, by decide⟩ : Fin 148) ⟨78, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨78, by decide⟩ 20 (transLenTr ⟨78, by decide⟩ 20 hp)) T120_78
      hfix120_78 hinj120_78 hcardT120_78
      (fun i => conj_mem_of_fixedPoints _ _ (T120_78 i) (hfix120_78 i) _)
      ⟨120, by decide⟩ ⟨78, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨78, by decide⟩ 20 hp) Q2.T120_78_2 Q2.hfix120_78_2 Q2.hinj120_78_2
      Q2.hcardT120_78_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_78_2 i) (Q2.hfix120_78_2 i) _)
      ?_).symm
  rw [show colData1 (⟨120, by decide⟩ : Fin 148)
        ((colE1 ⟨78, by decide⟩ 20 (transLenTr ⟨78, by decide⟩ 20 hp) : ↥(reps ⟨78, by decide⟩)) : Coordinate 1)
        T120_78 = colFn colCertDiv_120_78_20.D1 (m := 5) from colCertDiv_120_78_20.bind1,
    show colData2 (⟨120, by decide⟩ : Fin 148)
        ((colE2 ⟨78, by decide⟩ 20 hp : ↥(Q2.reps ⟨78, by decide⟩)) : Coordinate 2)
        Q2.T120_78_2 = colFn colCertDiv_120_78_20.D2 (m := 5) from colCertDiv_120_78_20.bind2]
  rw [alnId_120 j hj]
  exact fastcode_of_div ⟨120, by decide⟩ _ _ _
    ((alnId_120 j hj) ▸ Q2.listedAt (⟨120, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨120, by decide⟩ : Fin 148) hj hq).1) colCertDiv_120_78_20_match


theorem leaf_120_78_21 (hp : 21 < (Q2.transData.getD 78 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨78, by decide⟩ : Fin 148)) (colE2 ⟨78, by decide⟩ 21 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨78, by decide⟩ : Fin 148))
        (colE1 ⟨78, by decide⟩ 21 (transLenTr ⟨78, by decide⟩ 21 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨120, by decide⟩ : Fin 148) ⟨78, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨78, by decide⟩ 21 (transLenTr ⟨78, by decide⟩ 21 hp)) T120_78
      hfix120_78 hinj120_78 hcardT120_78
      (fun i => conj_mem_of_fixedPoints _ _ (T120_78 i) (hfix120_78 i) _)
      ⟨120, by decide⟩ ⟨78, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨78, by decide⟩ 21 hp) Q2.T120_78_2 Q2.hfix120_78_2 Q2.hinj120_78_2
      Q2.hcardT120_78_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_78_2 i) (Q2.hfix120_78_2 i) _)
      ?_).symm
  rw [show colData1 (⟨120, by decide⟩ : Fin 148)
        ((colE1 ⟨78, by decide⟩ 21 (transLenTr ⟨78, by decide⟩ 21 hp) : ↥(reps ⟨78, by decide⟩)) : Coordinate 1)
        T120_78 = colFn colCertDiv_120_78_21.D1 (m := 5) from colCertDiv_120_78_21.bind1,
    show colData2 (⟨120, by decide⟩ : Fin 148)
        ((colE2 ⟨78, by decide⟩ 21 hp : ↥(Q2.reps ⟨78, by decide⟩)) : Coordinate 2)
        Q2.T120_78_2 = colFn colCertDiv_120_78_21.D2 (m := 5) from colCertDiv_120_78_21.bind2]
  rw [alnId_120 j hj]
  exact fastcode_of_div ⟨120, by decide⟩ _ _ _
    ((alnId_120 j hj) ▸ Q2.listedAt (⟨120, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨120, by decide⟩ : Fin 148) hj hq).1) colCertDiv_120_78_21_match


theorem leaf_120_78_22 (hp : 22 < (Q2.transData.getD 78 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨78, by decide⟩ : Fin 148)) (colE2 ⟨78, by decide⟩ 22 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨78, by decide⟩ : Fin 148))
        (colE1 ⟨78, by decide⟩ 22 (transLenTr ⟨78, by decide⟩ 22 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨120, by decide⟩ : Fin 148) ⟨78, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨78, by decide⟩ 22 (transLenTr ⟨78, by decide⟩ 22 hp)) T120_78
      hfix120_78 hinj120_78 hcardT120_78
      (fun i => conj_mem_of_fixedPoints _ _ (T120_78 i) (hfix120_78 i) _)
      ⟨120, by decide⟩ ⟨78, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨78, by decide⟩ 22 hp) Q2.T120_78_2 Q2.hfix120_78_2 Q2.hinj120_78_2
      Q2.hcardT120_78_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_78_2 i) (Q2.hfix120_78_2 i) _)
      ?_).symm
  rw [show colData1 (⟨120, by decide⟩ : Fin 148)
        ((colE1 ⟨78, by decide⟩ 22 (transLenTr ⟨78, by decide⟩ 22 hp) : ↥(reps ⟨78, by decide⟩)) : Coordinate 1)
        T120_78 = colFn colCertDiv_120_78_22.D1 (m := 5) from colCertDiv_120_78_22.bind1,
    show colData2 (⟨120, by decide⟩ : Fin 148)
        ((colE2 ⟨78, by decide⟩ 22 hp : ↥(Q2.reps ⟨78, by decide⟩)) : Coordinate 2)
        Q2.T120_78_2 = colFn colCertDiv_120_78_22.D2 (m := 5) from colCertDiv_120_78_22.bind2]
  rw [alnId_120 j hj]
  exact fastcode_of_div ⟨120, by decide⟩ _ _ _
    ((alnId_120 j hj) ▸ Q2.listedAt (⟨120, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨120, by decide⟩ : Fin 148) hj hq).1) colCertDiv_120_78_22_match


theorem leaf_120_78_23 (hp : 23 < (Q2.transData.getD 78 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨78, by decide⟩ : Fin 148)) (colE2 ⟨78, by decide⟩ 23 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨78, by decide⟩ : Fin 148))
        (colE1 ⟨78, by decide⟩ 23 (transLenTr ⟨78, by decide⟩ 23 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨120, by decide⟩ : Fin 148) ⟨78, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨78, by decide⟩ 23 (transLenTr ⟨78, by decide⟩ 23 hp)) T120_78
      hfix120_78 hinj120_78 hcardT120_78
      (fun i => conj_mem_of_fixedPoints _ _ (T120_78 i) (hfix120_78 i) _)
      ⟨120, by decide⟩ ⟨78, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨78, by decide⟩ 23 hp) Q2.T120_78_2 Q2.hfix120_78_2 Q2.hinj120_78_2
      Q2.hcardT120_78_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_78_2 i) (Q2.hfix120_78_2 i) _)
      ?_).symm
  rw [show colData1 (⟨120, by decide⟩ : Fin 148)
        ((colE1 ⟨78, by decide⟩ 23 (transLenTr ⟨78, by decide⟩ 23 hp) : ↥(reps ⟨78, by decide⟩)) : Coordinate 1)
        T120_78 = colFn colCertDiv_120_78_23.D1 (m := 5) from colCertDiv_120_78_23.bind1,
    show colData2 (⟨120, by decide⟩ : Fin 148)
        ((colE2 ⟨78, by decide⟩ 23 hp : ↥(Q2.reps ⟨78, by decide⟩)) : Coordinate 2)
        Q2.T120_78_2 = colFn colCertDiv_120_78_23.D2 (m := 5) from colCertDiv_120_78_23.bind2]
  rw [alnId_120 j hj]
  exact fastcode_of_div ⟨120, by decide⟩ _ _ _
    ((alnId_120 j hj) ▸ Q2.listedAt (⟨120, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨120, by decide⟩ : Fin 148) hj hq).1) colCertDiv_120_78_23_match


theorem leaf_120_78_24 (hp : 24 < (Q2.transData.getD 78 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨78, by decide⟩ : Fin 148)) (colE2 ⟨78, by decide⟩ 24 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨78, by decide⟩ : Fin 148))
        (colE1 ⟨78, by decide⟩ 24 (transLenTr ⟨78, by decide⟩ 24 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨120, by decide⟩ : Fin 148) ⟨78, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨78, by decide⟩ 24 (transLenTr ⟨78, by decide⟩ 24 hp)) T120_78
      hfix120_78 hinj120_78 hcardT120_78
      (fun i => conj_mem_of_fixedPoints _ _ (T120_78 i) (hfix120_78 i) _)
      ⟨120, by decide⟩ ⟨78, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨78, by decide⟩ 24 hp) Q2.T120_78_2 Q2.hfix120_78_2 Q2.hinj120_78_2
      Q2.hcardT120_78_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_78_2 i) (Q2.hfix120_78_2 i) _)
      ?_).symm
  rw [show colData1 (⟨120, by decide⟩ : Fin 148)
        ((colE1 ⟨78, by decide⟩ 24 (transLenTr ⟨78, by decide⟩ 24 hp) : ↥(reps ⟨78, by decide⟩)) : Coordinate 1)
        T120_78 = colFn colCertDiv_120_78_24.D1 (m := 5) from colCertDiv_120_78_24.bind1,
    show colData2 (⟨120, by decide⟩ : Fin 148)
        ((colE2 ⟨78, by decide⟩ 24 hp : ↥(Q2.reps ⟨78, by decide⟩)) : Coordinate 2)
        Q2.T120_78_2 = colFn colCertDiv_120_78_24.D2 (m := 5) from colCertDiv_120_78_24.bind2]
  rw [alnId_120 j hj]
  exact fastcode_of_div ⟨120, by decide⟩ _ _ _
    ((alnId_120 j hj) ▸ Q2.listedAt (⟨120, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨120, by decide⟩ : Fin 148) hj hq).1) colCertDiv_120_78_24_match


theorem leaf_120_79_0 (hp : 0 < (Q2.transData.getD 79 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨79, by decide⟩ : Fin 148)) (colE2 ⟨79, by decide⟩ 0 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨79, by decide⟩ : Fin 148))
        (colE1 ⟨79, by decide⟩ 0 (transLenTr ⟨79, by decide⟩ 0 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨79, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨79, by decide⟩ 0 (transLenTr ⟨79, by decide⟩ 0 hp)) T120_79
      hfix120_79 hinj120_79 hcardT120_79
      (fun i => conj_mem_of_fixedPoints _ _ (T120_79 i) (hfix120_79 i) _)
      ⟨120, by decide⟩ ⟨79, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨79, by decide⟩ 0 hp) Q2.T120_79_2 Q2.hfix120_79_2 Q2.hinj120_79_2
      Q2.hcardT120_79_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_79_2 i) (Q2.hfix120_79_2 i) _)
      colCert_120_79_0.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_79_1 (hp : 1 < (Q2.transData.getD 79 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨79, by decide⟩ : Fin 148)) (colE2 ⟨79, by decide⟩ 1 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨79, by decide⟩ : Fin 148))
        (colE1 ⟨79, by decide⟩ 1 (transLenTr ⟨79, by decide⟩ 1 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨79, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨79, by decide⟩ 1 (transLenTr ⟨79, by decide⟩ 1 hp)) T120_79
      hfix120_79 hinj120_79 hcardT120_79
      (fun i => conj_mem_of_fixedPoints _ _ (T120_79 i) (hfix120_79 i) _)
      ⟨120, by decide⟩ ⟨79, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨79, by decide⟩ 1 hp) Q2.T120_79_2 Q2.hfix120_79_2 Q2.hinj120_79_2
      Q2.hcardT120_79_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_79_2 i) (Q2.hfix120_79_2 i) _)
      colCert_120_79_1.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_79_2 (hp : 2 < (Q2.transData.getD 79 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨79, by decide⟩ : Fin 148)) (colE2 ⟨79, by decide⟩ 2 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨79, by decide⟩ : Fin 148))
        (colE1 ⟨79, by decide⟩ 2 (transLenTr ⟨79, by decide⟩ 2 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨79, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨79, by decide⟩ 2 (transLenTr ⟨79, by decide⟩ 2 hp)) T120_79
      hfix120_79 hinj120_79 hcardT120_79
      (fun i => conj_mem_of_fixedPoints _ _ (T120_79 i) (hfix120_79 i) _)
      ⟨120, by decide⟩ ⟨79, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨79, by decide⟩ 2 hp) Q2.T120_79_2 Q2.hfix120_79_2 Q2.hinj120_79_2
      Q2.hcardT120_79_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_79_2 i) (Q2.hfix120_79_2 i) _)
      colCert_120_79_2.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_79_3 (hp : 3 < (Q2.transData.getD 79 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨79, by decide⟩ : Fin 148)) (colE2 ⟨79, by decide⟩ 3 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨79, by decide⟩ : Fin 148))
        (colE1 ⟨79, by decide⟩ 3 (transLenTr ⟨79, by decide⟩ 3 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨79, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨79, by decide⟩ 3 (transLenTr ⟨79, by decide⟩ 3 hp)) T120_79
      hfix120_79 hinj120_79 hcardT120_79
      (fun i => conj_mem_of_fixedPoints _ _ (T120_79 i) (hfix120_79 i) _)
      ⟨120, by decide⟩ ⟨79, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨79, by decide⟩ 3 hp) Q2.T120_79_2 Q2.hfix120_79_2 Q2.hinj120_79_2
      Q2.hcardT120_79_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_79_2 i) (Q2.hfix120_79_2 i) _)
      colCert_120_79_3.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_79_4 (hp : 4 < (Q2.transData.getD 79 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨79, by decide⟩ : Fin 148)) (colE2 ⟨79, by decide⟩ 4 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨79, by decide⟩ : Fin 148))
        (colE1 ⟨79, by decide⟩ 4 (transLenTr ⟨79, by decide⟩ 4 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨79, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨79, by decide⟩ 4 (transLenTr ⟨79, by decide⟩ 4 hp)) T120_79
      hfix120_79 hinj120_79 hcardT120_79
      (fun i => conj_mem_of_fixedPoints _ _ (T120_79 i) (hfix120_79 i) _)
      ⟨120, by decide⟩ ⟨79, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨79, by decide⟩ 4 hp) Q2.T120_79_2 Q2.hfix120_79_2 Q2.hinj120_79_2
      Q2.hcardT120_79_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_79_2 i) (Q2.hfix120_79_2 i) _)
      colCert_120_79_4.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_79_5 (hp : 5 < (Q2.transData.getD 79 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨79, by decide⟩ : Fin 148)) (colE2 ⟨79, by decide⟩ 5 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨79, by decide⟩ : Fin 148))
        (colE1 ⟨79, by decide⟩ 5 (transLenTr ⟨79, by decide⟩ 5 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨79, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨79, by decide⟩ 5 (transLenTr ⟨79, by decide⟩ 5 hp)) T120_79
      hfix120_79 hinj120_79 hcardT120_79
      (fun i => conj_mem_of_fixedPoints _ _ (T120_79 i) (hfix120_79 i) _)
      ⟨120, by decide⟩ ⟨79, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨79, by decide⟩ 5 hp) Q2.T120_79_2 Q2.hfix120_79_2 Q2.hinj120_79_2
      Q2.hcardT120_79_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_79_2 i) (Q2.hfix120_79_2 i) _)
      colCert_120_79_5.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_79_6 (hp : 6 < (Q2.transData.getD 79 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨79, by decide⟩ : Fin 148)) (colE2 ⟨79, by decide⟩ 6 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨79, by decide⟩ : Fin 148))
        (colE1 ⟨79, by decide⟩ 6 (transLenTr ⟨79, by decide⟩ 6 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨79, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨79, by decide⟩ 6 (transLenTr ⟨79, by decide⟩ 6 hp)) T120_79
      hfix120_79 hinj120_79 hcardT120_79
      (fun i => conj_mem_of_fixedPoints _ _ (T120_79 i) (hfix120_79 i) _)
      ⟨120, by decide⟩ ⟨79, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨79, by decide⟩ 6 hp) Q2.T120_79_2 Q2.hfix120_79_2 Q2.hinj120_79_2
      Q2.hcardT120_79_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_79_2 i) (Q2.hfix120_79_2 i) _)
      colCert_120_79_6.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_79_7 (hp : 7 < (Q2.transData.getD 79 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨79, by decide⟩ : Fin 148)) (colE2 ⟨79, by decide⟩ 7 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨79, by decide⟩ : Fin 148))
        (colE1 ⟨79, by decide⟩ 7 (transLenTr ⟨79, by decide⟩ 7 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨79, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨79, by decide⟩ 7 (transLenTr ⟨79, by decide⟩ 7 hp)) T120_79
      hfix120_79 hinj120_79 hcardT120_79
      (fun i => conj_mem_of_fixedPoints _ _ (T120_79 i) (hfix120_79 i) _)
      ⟨120, by decide⟩ ⟨79, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨79, by decide⟩ 7 hp) Q2.T120_79_2 Q2.hfix120_79_2 Q2.hinj120_79_2
      Q2.hcardT120_79_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_79_2 i) (Q2.hfix120_79_2 i) _)
      colCert_120_79_7.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_79_8 (hp : 8 < (Q2.transData.getD 79 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨79, by decide⟩ : Fin 148)) (colE2 ⟨79, by decide⟩ 8 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨79, by decide⟩ : Fin 148))
        (colE1 ⟨79, by decide⟩ 8 (transLenTr ⟨79, by decide⟩ 8 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨79, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨79, by decide⟩ 8 (transLenTr ⟨79, by decide⟩ 8 hp)) T120_79
      hfix120_79 hinj120_79 hcardT120_79
      (fun i => conj_mem_of_fixedPoints _ _ (T120_79 i) (hfix120_79 i) _)
      ⟨120, by decide⟩ ⟨79, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨79, by decide⟩ 8 hp) Q2.T120_79_2 Q2.hfix120_79_2 Q2.hinj120_79_2
      Q2.hcardT120_79_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_79_2 i) (Q2.hfix120_79_2 i) _)
      colCert_120_79_8.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_79_9 (hp : 9 < (Q2.transData.getD 79 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨79, by decide⟩ : Fin 148)) (colE2 ⟨79, by decide⟩ 9 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨79, by decide⟩ : Fin 148))
        (colE1 ⟨79, by decide⟩ 9 (transLenTr ⟨79, by decide⟩ 9 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨79, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨79, by decide⟩ 9 (transLenTr ⟨79, by decide⟩ 9 hp)) T120_79
      hfix120_79 hinj120_79 hcardT120_79
      (fun i => conj_mem_of_fixedPoints _ _ (T120_79 i) (hfix120_79 i) _)
      ⟨120, by decide⟩ ⟨79, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨79, by decide⟩ 9 hp) Q2.T120_79_2 Q2.hfix120_79_2 Q2.hinj120_79_2
      Q2.hcardT120_79_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_79_2 i) (Q2.hfix120_79_2 i) _)
      colCert_120_79_9.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_79_10 (hp : 10 < (Q2.transData.getD 79 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨79, by decide⟩ : Fin 148)) (colE2 ⟨79, by decide⟩ 10 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨79, by decide⟩ : Fin 148))
        (colE1 ⟨79, by decide⟩ 10 (transLenTr ⟨79, by decide⟩ 10 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨79, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨79, by decide⟩ 10 (transLenTr ⟨79, by decide⟩ 10 hp)) T120_79
      hfix120_79 hinj120_79 hcardT120_79
      (fun i => conj_mem_of_fixedPoints _ _ (T120_79 i) (hfix120_79 i) _)
      ⟨120, by decide⟩ ⟨79, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨79, by decide⟩ 10 hp) Q2.T120_79_2 Q2.hfix120_79_2 Q2.hinj120_79_2
      Q2.hcardT120_79_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_79_2 i) (Q2.hfix120_79_2 i) _)
      colCert_120_79_10.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_79_11 (hp : 11 < (Q2.transData.getD 79 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨79, by decide⟩ : Fin 148)) (colE2 ⟨79, by decide⟩ 11 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨79, by decide⟩ : Fin 148))
        (colE1 ⟨79, by decide⟩ 11 (transLenTr ⟨79, by decide⟩ 11 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨79, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨79, by decide⟩ 11 (transLenTr ⟨79, by decide⟩ 11 hp)) T120_79
      hfix120_79 hinj120_79 hcardT120_79
      (fun i => conj_mem_of_fixedPoints _ _ (T120_79 i) (hfix120_79 i) _)
      ⟨120, by decide⟩ ⟨79, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨79, by decide⟩ 11 hp) Q2.T120_79_2 Q2.hfix120_79_2 Q2.hinj120_79_2
      Q2.hcardT120_79_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_79_2 i) (Q2.hfix120_79_2 i) _)
      colCert_120_79_11.hD ?_).symm
  rw [alnId_120 j hj]


end LeanDring.P5Presentation
