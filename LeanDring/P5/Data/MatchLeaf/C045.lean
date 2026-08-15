/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Data.ColCdd.C020
import LeanDring.P5.Data.ColRestCheap.C094
import LeanDring.P5.Data.ColRestCheap.C095
import LeanDring.P5.Data.ColRestCheap.C096
import LeanDring.P5.Data.ColRestCheap.C097
import LeanDring.P5.Data.ColRestCheap.C098
import LeanDring.P5.Data.ColTau.C002
import LeanDring.P5.Data.EntryK.C040
import LeanDring.P5.Data.EntryK.C041
import LeanDring.P5.Certificate.RingIsomorphism.MatchCore
import LeanDring.P5.Data.SpeciesDiv.C030
import LeanDring.P5.Certificate.SpeciesTable.Twin2.SpeciesTau.Chunk03

/-! # Stage-5 leaves, chunk 44 (auto-emitted).  -/

namespace LeanDring.P5Presentation

open MulAction Finset LeanDring.DRing LeanDring.MonGSet

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.style.longLine false

theorem leaf_141_85_24 (hp : 24 < (Q2.transData.getD 85 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨85, by decide⟩ : Fin 148)) (colE2 ⟨85, by decide⟩ 24 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨85, by decide⟩ : Fin 148))
        (colE1 ⟨85, by decide⟩ 24 (transLenTr ⟨85, by decide⟩ 24 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨85, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨85, by decide⟩ 24 (transLenTr ⟨85, by decide⟩ 24 hp)) T141_85
      hfix141_85 hinj141_85 hcardT141_85
      (fun i => conj_mem_of_fixedPoints _ _ (T141_85 i) (hfix141_85 i) _)
      ⟨141, by decide⟩ ⟨85, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨85, by decide⟩ 24 hp) Q2.T141_85_2 Q2.hfix141_85_2 Q2.hinj141_85_2
      Q2.hcardT141_85_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_85_2 i) (Q2.hfix141_85_2 i) _)
      colCert_141_85_24.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_85_25 (hp : 25 < (Q2.transData.getD 85 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨85, by decide⟩ : Fin 148)) (colE2 ⟨85, by decide⟩ 25 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨85, by decide⟩ : Fin 148))
        (colE1 ⟨85, by decide⟩ 25 (transLenTr ⟨85, by decide⟩ 25 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨85, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨85, by decide⟩ 25 (transLenTr ⟨85, by decide⟩ 25 hp)) T141_85
      hfix141_85 hinj141_85 hcardT141_85
      (fun i => conj_mem_of_fixedPoints _ _ (T141_85 i) (hfix141_85 i) _)
      ⟨141, by decide⟩ ⟨85, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨85, by decide⟩ 25 hp) Q2.T141_85_2 Q2.hfix141_85_2 Q2.hinj141_85_2
      Q2.hcardT141_85_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_85_2 i) (Q2.hfix141_85_2 i) _)
      colCert_141_85_25.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_85_30 (hp : 30 < (Q2.transData.getD 85 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨85, by decide⟩ : Fin 148)) (colE2 ⟨85, by decide⟩ 30 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨85, by decide⟩ : Fin 148))
        (colE1 ⟨85, by decide⟩ 30 (transLenTr ⟨85, by decide⟩ 30 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨85, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨85, by decide⟩ 30 (transLenTr ⟨85, by decide⟩ 30 hp)) T141_85
      hfix141_85 hinj141_85 hcardT141_85
      (fun i => conj_mem_of_fixedPoints _ _ (T141_85 i) (hfix141_85 i) _)
      ⟨141, by decide⟩ ⟨85, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨85, by decide⟩ 30 hp) Q2.T141_85_2 Q2.hfix141_85_2 Q2.hinj141_85_2
      Q2.hcardT141_85_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_85_2 i) (Q2.hfix141_85_2 i) _)
      colCert_141_85_30.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_85_35 (hp : 35 < (Q2.transData.getD 85 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨85, by decide⟩ : Fin 148)) (colE2 ⟨85, by decide⟩ 35 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨85, by decide⟩ : Fin 148))
        (colE1 ⟨85, by decide⟩ 35 (transLenTr ⟨85, by decide⟩ 35 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨85, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨85, by decide⟩ 35 (transLenTr ⟨85, by decide⟩ 35 hp)) T141_85
      hfix141_85 hinj141_85 hcardT141_85
      (fun i => conj_mem_of_fixedPoints _ _ (T141_85 i) (hfix141_85 i) _)
      ⟨141, by decide⟩ ⟨85, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨85, by decide⟩ 35 hp) Q2.T141_85_2 Q2.hfix141_85_2 Q2.hinj141_85_2
      Q2.hcardT141_85_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_85_2 i) (Q2.hfix141_85_2 i) _)
      colCert_141_85_35.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_85_40 (hp : 40 < (Q2.transData.getD 85 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨85, by decide⟩ : Fin 148)) (colE2 ⟨85, by decide⟩ 40 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨85, by decide⟩ : Fin 148))
        (colE1 ⟨85, by decide⟩ 40 (transLenTr ⟨85, by decide⟩ 40 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨85, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨85, by decide⟩ 40 (transLenTr ⟨85, by decide⟩ 40 hp)) T141_85
      hfix141_85 hinj141_85 hcardT141_85
      (fun i => conj_mem_of_fixedPoints _ _ (T141_85 i) (hfix141_85 i) _)
      ⟨141, by decide⟩ ⟨85, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨85, by decide⟩ 40 hp) Q2.T141_85_2 Q2.hfix141_85_2 Q2.hinj141_85_2
      Q2.hcardT141_85_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_85_2 i) (Q2.hfix141_85_2 i) _)
      colCert_141_85_40.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_85_45 (hp : 45 < (Q2.transData.getD 85 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨85, by decide⟩ : Fin 148)) (colE2 ⟨85, by decide⟩ 45 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨85, by decide⟩ : Fin 148))
        (colE1 ⟨85, by decide⟩ 45 (transLenTr ⟨85, by decide⟩ 45 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨85, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨85, by decide⟩ 45 (transLenTr ⟨85, by decide⟩ 45 hp)) T141_85
      hfix141_85 hinj141_85 hcardT141_85
      (fun i => conj_mem_of_fixedPoints _ _ (T141_85 i) (hfix141_85 i) _)
      ⟨141, by decide⟩ ⟨85, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨85, by decide⟩ 45 hp) Q2.T141_85_2 Q2.hfix141_85_2 Q2.hinj141_85_2
      Q2.hcardT141_85_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_85_2 i) (Q2.hfix141_85_2 i) _)
      colCert_141_85_45.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_85_50 (hp : 50 < (Q2.transData.getD 85 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨85, by decide⟩ : Fin 148)) (colE2 ⟨85, by decide⟩ 50 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨85, by decide⟩ : Fin 148))
        (colE1 ⟨85, by decide⟩ 50 (transLenTr ⟨85, by decide⟩ 50 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨141, by decide⟩ : Fin 148) ⟨85, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨85, by decide⟩ 50 (transLenTr ⟨85, by decide⟩ 50 hp)) T141_85
      hfix141_85 hinj141_85 hcardT141_85
      (fun i => conj_mem_of_fixedPoints _ _ (T141_85 i) (hfix141_85 i) _)
      ⟨141, by decide⟩ ⟨85, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨85, by decide⟩ 50 hp) Q2.T141_85_2 Q2.hfix141_85_2 Q2.hinj141_85_2
      Q2.hcardT141_85_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_85_2 i) (Q2.hfix141_85_2 i) _)
      ?_).symm
  rw [show colData1 (⟨141, by decide⟩ : Fin 148)
        ((colE1 ⟨85, by decide⟩ 50 (transLenTr ⟨85, by decide⟩ 50 hp) : ↥(reps ⟨85, by decide⟩)) : Coordinate 1)
        T141_85 = colFn colCertDiv_141_85_50.D1 (m := 5) from colCertDiv_141_85_50.bind1,
    show colData2 (⟨141, by decide⟩ : Fin 148)
        ((colE2 ⟨85, by decide⟩ 50 hp : ↥(Q2.reps ⟨85, by decide⟩)) : Coordinate 2)
        Q2.T141_85_2 = colFn colCertDiv_141_85_50.D2 (m := 5) from colCertDiv_141_85_50.bind2]
  rw [alnId_141 j hj]
  exact fastcode_of_tau ⟨141, by decide⟩ _ _ _
    ((alnId_141 j hj) ▸ Q2.listedAt (⟨141, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨141, by decide⟩ : Fin 148) hj hq).1) colCertDiv_141_85_50_tau_match


theorem leaf_141_85_55 (hp : 55 < (Q2.transData.getD 85 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨85, by decide⟩ : Fin 148)) (colE2 ⟨85, by decide⟩ 55 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨85, by decide⟩ : Fin 148))
        (colE1 ⟨85, by decide⟩ 55 (transLenTr ⟨85, by decide⟩ 55 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨141, by decide⟩ : Fin 148) ⟨85, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨85, by decide⟩ 55 (transLenTr ⟨85, by decide⟩ 55 hp)) T141_85
      hfix141_85 hinj141_85 hcardT141_85
      (fun i => conj_mem_of_fixedPoints _ _ (T141_85 i) (hfix141_85 i) _)
      ⟨141, by decide⟩ ⟨85, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨85, by decide⟩ 55 hp) Q2.T141_85_2 Q2.hfix141_85_2 Q2.hinj141_85_2
      Q2.hcardT141_85_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_85_2 i) (Q2.hfix141_85_2 i) _)
      ?_).symm
  rw [show colData1 (⟨141, by decide⟩ : Fin 148)
        ((colE1 ⟨85, by decide⟩ 55 (transLenTr ⟨85, by decide⟩ 55 hp) : ↥(reps ⟨85, by decide⟩)) : Coordinate 1)
        T141_85 = colFn colCertDiv_141_85_55.D1 (m := 5) from colCertDiv_141_85_55.bind1,
    show colData2 (⟨141, by decide⟩ : Fin 148)
        ((colE2 ⟨85, by decide⟩ 55 hp : ↥(Q2.reps ⟨85, by decide⟩)) : Coordinate 2)
        Q2.T141_85_2 = colFn colCertDiv_141_85_55.D2 (m := 5) from colCertDiv_141_85_55.bind2]
  rw [alnId_141 j hj]
  exact fastcode_of_tau ⟨141, by decide⟩ _ _ _
    ((alnId_141 j hj) ▸ Q2.listedAt (⟨141, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨141, by decide⟩ : Fin 148) hj hq).1) colCertDiv_141_85_55_tau_match


theorem leaf_141_85_60 (hp : 60 < (Q2.transData.getD 85 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨85, by decide⟩ : Fin 148)) (colE2 ⟨85, by decide⟩ 60 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨85, by decide⟩ : Fin 148))
        (colE1 ⟨85, by decide⟩ 60 (transLenTr ⟨85, by decide⟩ 60 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨141, by decide⟩ : Fin 148) ⟨85, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨85, by decide⟩ 60 (transLenTr ⟨85, by decide⟩ 60 hp)) T141_85
      hfix141_85 hinj141_85 hcardT141_85
      (fun i => conj_mem_of_fixedPoints _ _ (T141_85 i) (hfix141_85 i) _)
      ⟨141, by decide⟩ ⟨85, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨85, by decide⟩ 60 hp) Q2.T141_85_2 Q2.hfix141_85_2 Q2.hinj141_85_2
      Q2.hcardT141_85_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_85_2 i) (Q2.hfix141_85_2 i) _)
      ?_).symm
  rw [show colData1 (⟨141, by decide⟩ : Fin 148)
        ((colE1 ⟨85, by decide⟩ 60 (transLenTr ⟨85, by decide⟩ 60 hp) : ↥(reps ⟨85, by decide⟩)) : Coordinate 1)
        T141_85 = colFn colCertDiv_141_85_60.D1 (m := 5) from colCertDiv_141_85_60.bind1,
    show colData2 (⟨141, by decide⟩ : Fin 148)
        ((colE2 ⟨85, by decide⟩ 60 hp : ↥(Q2.reps ⟨85, by decide⟩)) : Coordinate 2)
        Q2.T141_85_2 = colFn colCertDiv_141_85_60.D2 (m := 5) from colCertDiv_141_85_60.bind2]
  rw [alnId_141 j hj]
  exact fastcode_of_tau ⟨141, by decide⟩ _ _ _
    ((alnId_141 j hj) ▸ Q2.listedAt (⟨141, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨141, by decide⟩ : Fin 148) hj hq).1) colCertDiv_141_85_60_tau_match


theorem leaf_141_85_65 (hp : 65 < (Q2.transData.getD 85 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨85, by decide⟩ : Fin 148)) (colE2 ⟨85, by decide⟩ 65 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨85, by decide⟩ : Fin 148))
        (colE1 ⟨85, by decide⟩ 65 (transLenTr ⟨85, by decide⟩ 65 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨141, by decide⟩ : Fin 148) ⟨85, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨85, by decide⟩ 65 (transLenTr ⟨85, by decide⟩ 65 hp)) T141_85
      hfix141_85 hinj141_85 hcardT141_85
      (fun i => conj_mem_of_fixedPoints _ _ (T141_85 i) (hfix141_85 i) _)
      ⟨141, by decide⟩ ⟨85, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨85, by decide⟩ 65 hp) Q2.T141_85_2 Q2.hfix141_85_2 Q2.hinj141_85_2
      Q2.hcardT141_85_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_85_2 i) (Q2.hfix141_85_2 i) _)
      ?_).symm
  rw [show colData1 (⟨141, by decide⟩ : Fin 148)
        ((colE1 ⟨85, by decide⟩ 65 (transLenTr ⟨85, by decide⟩ 65 hp) : ↥(reps ⟨85, by decide⟩)) : Coordinate 1)
        T141_85 = colFn colCertDiv_141_85_65.D1 (m := 5) from colCertDiv_141_85_65.bind1,
    show colData2 (⟨141, by decide⟩ : Fin 148)
        ((colE2 ⟨85, by decide⟩ 65 hp : ↥(Q2.reps ⟨85, by decide⟩)) : Coordinate 2)
        Q2.T141_85_2 = colFn colCertDiv_141_85_65.D2 (m := 5) from colCertDiv_141_85_65.bind2]
  rw [alnId_141 j hj]
  exact fastcode_of_tau ⟨141, by decide⟩ _ _ _
    ((alnId_141 j hj) ▸ Q2.listedAt (⟨141, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨141, by decide⟩ : Fin 148) hj hq).1) colCertDiv_141_85_65_tau_match


theorem leaf_141_85_70 (hp : 70 < (Q2.transData.getD 85 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨85, by decide⟩ : Fin 148)) (colE2 ⟨85, by decide⟩ 70 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨85, by decide⟩ : Fin 148))
        (colE1 ⟨85, by decide⟩ 70 (transLenTr ⟨85, by decide⟩ 70 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨141, by decide⟩ : Fin 148) ⟨85, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨85, by decide⟩ 70 (transLenTr ⟨85, by decide⟩ 70 hp)) T141_85
      hfix141_85 hinj141_85 hcardT141_85
      (fun i => conj_mem_of_fixedPoints _ _ (T141_85 i) (hfix141_85 i) _)
      ⟨141, by decide⟩ ⟨85, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨85, by decide⟩ 70 hp) Q2.T141_85_2 Q2.hfix141_85_2 Q2.hinj141_85_2
      Q2.hcardT141_85_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_85_2 i) (Q2.hfix141_85_2 i) _)
      ?_).symm
  rw [show colData1 (⟨141, by decide⟩ : Fin 148)
        ((colE1 ⟨85, by decide⟩ 70 (transLenTr ⟨85, by decide⟩ 70 hp) : ↥(reps ⟨85, by decide⟩)) : Coordinate 1)
        T141_85 = colFn colCertDiv_141_85_70.D1 (m := 5) from colCertDiv_141_85_70.bind1,
    show colData2 (⟨141, by decide⟩ : Fin 148)
        ((colE2 ⟨85, by decide⟩ 70 hp : ↥(Q2.reps ⟨85, by decide⟩)) : Coordinate 2)
        Q2.T141_85_2 = colFn colCertDiv_141_85_70.D2 (m := 5) from colCertDiv_141_85_70.bind2]
  rw [alnId_141 j hj]
  exact fastcode_of_tau ⟨141, by decide⟩ _ _ _
    ((alnId_141 j hj) ▸ Q2.listedAt (⟨141, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨141, by decide⟩ : Fin 148) hj hq).1) colCertDiv_141_85_70_tau_match


theorem leaf_141_85_75 (hp : 75 < (Q2.transData.getD 85 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨85, by decide⟩ : Fin 148)) (colE2 ⟨85, by decide⟩ 75 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨85, by decide⟩ : Fin 148))
        (colE1 ⟨85, by decide⟩ 75 (transLenTr ⟨85, by decide⟩ 75 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨141, by decide⟩ : Fin 148) ⟨85, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨85, by decide⟩ 75 (transLenTr ⟨85, by decide⟩ 75 hp)) T141_85
      hfix141_85 hinj141_85 hcardT141_85
      (fun i => conj_mem_of_fixedPoints _ _ (T141_85 i) (hfix141_85 i) _)
      ⟨141, by decide⟩ ⟨85, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨85, by decide⟩ 75 hp) Q2.T141_85_2 Q2.hfix141_85_2 Q2.hinj141_85_2
      Q2.hcardT141_85_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_85_2 i) (Q2.hfix141_85_2 i) _)
      ?_).symm
  rw [show colData1 (⟨141, by decide⟩ : Fin 148)
        ((colE1 ⟨85, by decide⟩ 75 (transLenTr ⟨85, by decide⟩ 75 hp) : ↥(reps ⟨85, by decide⟩)) : Coordinate 1)
        T141_85 = colFn colCertDiv_141_85_75.D1 (m := 5) from colCertDiv_141_85_75.bind1,
    show colData2 (⟨141, by decide⟩ : Fin 148)
        ((colE2 ⟨85, by decide⟩ 75 hp : ↥(Q2.reps ⟨85, by decide⟩)) : Coordinate 2)
        Q2.T141_85_2 = colFn colCertDiv_141_85_75.D2 (m := 5) from colCertDiv_141_85_75.bind2]
  rw [alnId_141 j hj]
  exact fastcode_of_tau ⟨141, by decide⟩ _ _ _
    ((alnId_141 j hj) ▸ Q2.listedAt (⟨141, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨141, by decide⟩ : Fin 148) hj hq).1) colCertDiv_141_85_75_tau_match


theorem leaf_141_85_80 (hp : 80 < (Q2.transData.getD 85 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨85, by decide⟩ : Fin 148)) (colE2 ⟨85, by decide⟩ 80 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨85, by decide⟩ : Fin 148))
        (colE1 ⟨85, by decide⟩ 80 (transLenTr ⟨85, by decide⟩ 80 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨141, by decide⟩ : Fin 148) ⟨85, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨85, by decide⟩ 80 (transLenTr ⟨85, by decide⟩ 80 hp)) T141_85
      hfix141_85 hinj141_85 hcardT141_85
      (fun i => conj_mem_of_fixedPoints _ _ (T141_85 i) (hfix141_85 i) _)
      ⟨141, by decide⟩ ⟨85, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨85, by decide⟩ 80 hp) Q2.T141_85_2 Q2.hfix141_85_2 Q2.hinj141_85_2
      Q2.hcardT141_85_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_85_2 i) (Q2.hfix141_85_2 i) _)
      ?_).symm
  rw [show colData1 (⟨141, by decide⟩ : Fin 148)
        ((colE1 ⟨85, by decide⟩ 80 (transLenTr ⟨85, by decide⟩ 80 hp) : ↥(reps ⟨85, by decide⟩)) : Coordinate 1)
        T141_85 = colFn colCertDiv_141_85_80.D1 (m := 5) from colCertDiv_141_85_80.bind1,
    show colData2 (⟨141, by decide⟩ : Fin 148)
        ((colE2 ⟨85, by decide⟩ 80 hp : ↥(Q2.reps ⟨85, by decide⟩)) : Coordinate 2)
        Q2.T141_85_2 = colFn colCertDiv_141_85_80.D2 (m := 5) from colCertDiv_141_85_80.bind2]
  rw [alnId_141 j hj]
  exact fastcode_of_tau ⟨141, by decide⟩ _ _ _
    ((alnId_141 j hj) ▸ Q2.listedAt (⟨141, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨141, by decide⟩ : Fin 148) hj hq).1) colCertDiv_141_85_80_tau_match


theorem leaf_141_85_85 (hp : 85 < (Q2.transData.getD 85 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨85, by decide⟩ : Fin 148)) (colE2 ⟨85, by decide⟩ 85 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨85, by decide⟩ : Fin 148))
        (colE1 ⟨85, by decide⟩ 85 (transLenTr ⟨85, by decide⟩ 85 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨141, by decide⟩ : Fin 148) ⟨85, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨85, by decide⟩ 85 (transLenTr ⟨85, by decide⟩ 85 hp)) T141_85
      hfix141_85 hinj141_85 hcardT141_85
      (fun i => conj_mem_of_fixedPoints _ _ (T141_85 i) (hfix141_85 i) _)
      ⟨141, by decide⟩ ⟨85, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨85, by decide⟩ 85 hp) Q2.T141_85_2 Q2.hfix141_85_2 Q2.hinj141_85_2
      Q2.hcardT141_85_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_85_2 i) (Q2.hfix141_85_2 i) _)
      ?_).symm
  rw [show colData1 (⟨141, by decide⟩ : Fin 148)
        ((colE1 ⟨85, by decide⟩ 85 (transLenTr ⟨85, by decide⟩ 85 hp) : ↥(reps ⟨85, by decide⟩)) : Coordinate 1)
        T141_85 = colFn colCertDiv_141_85_85.D1 (m := 5) from colCertDiv_141_85_85.bind1,
    show colData2 (⟨141, by decide⟩ : Fin 148)
        ((colE2 ⟨85, by decide⟩ 85 hp : ↥(Q2.reps ⟨85, by decide⟩)) : Coordinate 2)
        Q2.T141_85_2 = colFn colCertDiv_141_85_85.D2 (m := 5) from colCertDiv_141_85_85.bind2]
  rw [alnId_141 j hj]
  exact fastcode_of_tau ⟨141, by decide⟩ _ _ _
    ((alnId_141 j hj) ▸ Q2.listedAt (⟨141, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨141, by decide⟩ : Fin 148) hj hq).1) colCertDiv_141_85_85_tau_match


theorem leaf_141_85_90 (hp : 90 < (Q2.transData.getD 85 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨85, by decide⟩ : Fin 148)) (colE2 ⟨85, by decide⟩ 90 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨85, by decide⟩ : Fin 148))
        (colE1 ⟨85, by decide⟩ 90 (transLenTr ⟨85, by decide⟩ 90 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨141, by decide⟩ : Fin 148) ⟨85, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨85, by decide⟩ 90 (transLenTr ⟨85, by decide⟩ 90 hp)) T141_85
      hfix141_85 hinj141_85 hcardT141_85
      (fun i => conj_mem_of_fixedPoints _ _ (T141_85 i) (hfix141_85 i) _)
      ⟨141, by decide⟩ ⟨85, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨85, by decide⟩ 90 hp) Q2.T141_85_2 Q2.hfix141_85_2 Q2.hinj141_85_2
      Q2.hcardT141_85_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_85_2 i) (Q2.hfix141_85_2 i) _)
      ?_).symm
  rw [show colData1 (⟨141, by decide⟩ : Fin 148)
        ((colE1 ⟨85, by decide⟩ 90 (transLenTr ⟨85, by decide⟩ 90 hp) : ↥(reps ⟨85, by decide⟩)) : Coordinate 1)
        T141_85 = colFn colCertDiv_141_85_90.D1 (m := 5) from colCertDiv_141_85_90.bind1,
    show colData2 (⟨141, by decide⟩ : Fin 148)
        ((colE2 ⟨85, by decide⟩ 90 hp : ↥(Q2.reps ⟨85, by decide⟩)) : Coordinate 2)
        Q2.T141_85_2 = colFn colCertDiv_141_85_90.D2 (m := 5) from colCertDiv_141_85_90.bind2]
  rw [alnId_141 j hj]
  exact fastcode_of_tau ⟨141, by decide⟩ _ _ _
    ((alnId_141 j hj) ▸ Q2.listedAt (⟨141, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨141, by decide⟩ : Fin 148) hj hq).1) colCertDiv_141_85_90_tau_match


theorem leaf_141_85_95 (hp : 95 < (Q2.transData.getD 85 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨85, by decide⟩ : Fin 148)) (colE2 ⟨85, by decide⟩ 95 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨85, by decide⟩ : Fin 148))
        (colE1 ⟨85, by decide⟩ 95 (transLenTr ⟨85, by decide⟩ 95 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨141, by decide⟩ : Fin 148) ⟨85, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨85, by decide⟩ 95 (transLenTr ⟨85, by decide⟩ 95 hp)) T141_85
      hfix141_85 hinj141_85 hcardT141_85
      (fun i => conj_mem_of_fixedPoints _ _ (T141_85 i) (hfix141_85 i) _)
      ⟨141, by decide⟩ ⟨85, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨85, by decide⟩ 95 hp) Q2.T141_85_2 Q2.hfix141_85_2 Q2.hinj141_85_2
      Q2.hcardT141_85_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_85_2 i) (Q2.hfix141_85_2 i) _)
      ?_).symm
  rw [show colData1 (⟨141, by decide⟩ : Fin 148)
        ((colE1 ⟨85, by decide⟩ 95 (transLenTr ⟨85, by decide⟩ 95 hp) : ↥(reps ⟨85, by decide⟩)) : Coordinate 1)
        T141_85 = colFn colCertDiv_141_85_95.D1 (m := 5) from colCertDiv_141_85_95.bind1,
    show colData2 (⟨141, by decide⟩ : Fin 148)
        ((colE2 ⟨85, by decide⟩ 95 hp : ↥(Q2.reps ⟨85, by decide⟩)) : Coordinate 2)
        Q2.T141_85_2 = colFn colCertDiv_141_85_95.D2 (m := 5) from colCertDiv_141_85_95.bind2]
  rw [alnId_141 j hj]
  exact fastcode_of_tau ⟨141, by decide⟩ _ _ _
    ((alnId_141 j hj) ▸ Q2.listedAt (⟨141, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨141, by decide⟩ : Fin 148) hj hq).1) colCertDiv_141_85_95_tau_match


theorem leaf_141_85_100 (hp : 100 < (Q2.transData.getD 85 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨85, by decide⟩ : Fin 148)) (colE2 ⟨85, by decide⟩ 100 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨85, by decide⟩ : Fin 148))
        (colE1 ⟨85, by decide⟩ 100 (transLenTr ⟨85, by decide⟩ 100 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨141, by decide⟩ : Fin 148) ⟨85, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨85, by decide⟩ 100 (transLenTr ⟨85, by decide⟩ 100 hp)) T141_85
      hfix141_85 hinj141_85 hcardT141_85
      (fun i => conj_mem_of_fixedPoints _ _ (T141_85 i) (hfix141_85 i) _)
      ⟨141, by decide⟩ ⟨85, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨85, by decide⟩ 100 hp) Q2.T141_85_2 Q2.hfix141_85_2 Q2.hinj141_85_2
      Q2.hcardT141_85_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_85_2 i) (Q2.hfix141_85_2 i) _)
      ?_).symm
  rw [show colData1 (⟨141, by decide⟩ : Fin 148)
        ((colE1 ⟨85, by decide⟩ 100 (transLenTr ⟨85, by decide⟩ 100 hp) : ↥(reps ⟨85, by decide⟩)) : Coordinate 1)
        T141_85 = colFn colCertDiv_141_85_100.D1 (m := 5) from colCertDiv_141_85_100.bind1,
    show colData2 (⟨141, by decide⟩ : Fin 148)
        ((colE2 ⟨85, by decide⟩ 100 hp : ↥(Q2.reps ⟨85, by decide⟩)) : Coordinate 2)
        Q2.T141_85_2 = colFn colCertDiv_141_85_100.D2 (m := 5) from colCertDiv_141_85_100.bind2]
  rw [alnId_141 j hj]
  exact fastcode_of_tau ⟨141, by decide⟩ _ _ _
    ((alnId_141 j hj) ▸ Q2.listedAt (⟨141, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨141, by decide⟩ : Fin 148) hj hq).1) colCertDiv_141_85_100_tau_match


theorem leaf_141_85_105 (hp : 105 < (Q2.transData.getD 85 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨85, by decide⟩ : Fin 148)) (colE2 ⟨85, by decide⟩ 105 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨85, by decide⟩ : Fin 148))
        (colE1 ⟨85, by decide⟩ 105 (transLenTr ⟨85, by decide⟩ 105 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨141, by decide⟩ : Fin 148) ⟨85, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨85, by decide⟩ 105 (transLenTr ⟨85, by decide⟩ 105 hp)) T141_85
      hfix141_85 hinj141_85 hcardT141_85
      (fun i => conj_mem_of_fixedPoints _ _ (T141_85 i) (hfix141_85 i) _)
      ⟨141, by decide⟩ ⟨85, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨85, by decide⟩ 105 hp) Q2.T141_85_2 Q2.hfix141_85_2 Q2.hinj141_85_2
      Q2.hcardT141_85_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_85_2 i) (Q2.hfix141_85_2 i) _)
      ?_).symm
  rw [show colData1 (⟨141, by decide⟩ : Fin 148)
        ((colE1 ⟨85, by decide⟩ 105 (transLenTr ⟨85, by decide⟩ 105 hp) : ↥(reps ⟨85, by decide⟩)) : Coordinate 1)
        T141_85 = colFn colCertDiv_141_85_105.D1 (m := 5) from colCertDiv_141_85_105.bind1,
    show colData2 (⟨141, by decide⟩ : Fin 148)
        ((colE2 ⟨85, by decide⟩ 105 hp : ↥(Q2.reps ⟨85, by decide⟩)) : Coordinate 2)
        Q2.T141_85_2 = colFn colCertDiv_141_85_105.D2 (m := 5) from colCertDiv_141_85_105.bind2]
  rw [alnId_141 j hj]
  exact fastcode_of_tau ⟨141, by decide⟩ _ _ _
    ((alnId_141 j hj) ▸ Q2.listedAt (⟨141, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨141, by decide⟩ : Fin 148) hj hq).1) colCertDiv_141_85_105_tau_match


theorem leaf_141_85_110 (hp : 110 < (Q2.transData.getD 85 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨85, by decide⟩ : Fin 148)) (colE2 ⟨85, by decide⟩ 110 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨85, by decide⟩ : Fin 148))
        (colE1 ⟨85, by decide⟩ 110 (transLenTr ⟨85, by decide⟩ 110 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨141, by decide⟩ : Fin 148) ⟨85, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨85, by decide⟩ 110 (transLenTr ⟨85, by decide⟩ 110 hp)) T141_85
      hfix141_85 hinj141_85 hcardT141_85
      (fun i => conj_mem_of_fixedPoints _ _ (T141_85 i) (hfix141_85 i) _)
      ⟨141, by decide⟩ ⟨85, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨85, by decide⟩ 110 hp) Q2.T141_85_2 Q2.hfix141_85_2 Q2.hinj141_85_2
      Q2.hcardT141_85_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_85_2 i) (Q2.hfix141_85_2 i) _)
      ?_).symm
  rw [show colData1 (⟨141, by decide⟩ : Fin 148)
        ((colE1 ⟨85, by decide⟩ 110 (transLenTr ⟨85, by decide⟩ 110 hp) : ↥(reps ⟨85, by decide⟩)) : Coordinate 1)
        T141_85 = colFn colCertDiv_141_85_110.D1 (m := 5) from colCertDiv_141_85_110.bind1,
    show colData2 (⟨141, by decide⟩ : Fin 148)
        ((colE2 ⟨85, by decide⟩ 110 hp : ↥(Q2.reps ⟨85, by decide⟩)) : Coordinate 2)
        Q2.T141_85_2 = colFn colCertDiv_141_85_110.D2 (m := 5) from colCertDiv_141_85_110.bind2]
  rw [alnId_141 j hj]
  exact fastcode_of_tau ⟨141, by decide⟩ _ _ _
    ((alnId_141 j hj) ▸ Q2.listedAt (⟨141, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨141, by decide⟩ : Fin 148) hj hq).1) colCertDiv_141_85_110_tau_match


theorem leaf_141_85_115 (hp : 115 < (Q2.transData.getD 85 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨85, by decide⟩ : Fin 148)) (colE2 ⟨85, by decide⟩ 115 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨85, by decide⟩ : Fin 148))
        (colE1 ⟨85, by decide⟩ 115 (transLenTr ⟨85, by decide⟩ 115 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨141, by decide⟩ : Fin 148) ⟨85, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨85, by decide⟩ 115 (transLenTr ⟨85, by decide⟩ 115 hp)) T141_85
      hfix141_85 hinj141_85 hcardT141_85
      (fun i => conj_mem_of_fixedPoints _ _ (T141_85 i) (hfix141_85 i) _)
      ⟨141, by decide⟩ ⟨85, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨85, by decide⟩ 115 hp) Q2.T141_85_2 Q2.hfix141_85_2 Q2.hinj141_85_2
      Q2.hcardT141_85_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_85_2 i) (Q2.hfix141_85_2 i) _)
      ?_).symm
  rw [show colData1 (⟨141, by decide⟩ : Fin 148)
        ((colE1 ⟨85, by decide⟩ 115 (transLenTr ⟨85, by decide⟩ 115 hp) : ↥(reps ⟨85, by decide⟩)) : Coordinate 1)
        T141_85 = colFn colCertDiv_141_85_115.D1 (m := 5) from colCertDiv_141_85_115.bind1,
    show colData2 (⟨141, by decide⟩ : Fin 148)
        ((colE2 ⟨85, by decide⟩ 115 hp : ↥(Q2.reps ⟨85, by decide⟩)) : Coordinate 2)
        Q2.T141_85_2 = colFn colCertDiv_141_85_115.D2 (m := 5) from colCertDiv_141_85_115.bind2]
  rw [alnId_141 j hj]
  exact fastcode_of_tau ⟨141, by decide⟩ _ _ _
    ((alnId_141 j hj) ▸ Q2.listedAt (⟨141, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨141, by decide⟩ : Fin 148) hj hq).1) colCertDiv_141_85_115_tau_match


theorem leaf_141_85_120 (hp : 120 < (Q2.transData.getD 85 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨85, by decide⟩ : Fin 148)) (colE2 ⟨85, by decide⟩ 120 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨85, by decide⟩ : Fin 148))
        (colE1 ⟨85, by decide⟩ 120 (transLenTr ⟨85, by decide⟩ 120 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨141, by decide⟩ : Fin 148) ⟨85, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨85, by decide⟩ 120 (transLenTr ⟨85, by decide⟩ 120 hp)) T141_85
      hfix141_85 hinj141_85 hcardT141_85
      (fun i => conj_mem_of_fixedPoints _ _ (T141_85 i) (hfix141_85 i) _)
      ⟨141, by decide⟩ ⟨85, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨85, by decide⟩ 120 hp) Q2.T141_85_2 Q2.hfix141_85_2 Q2.hinj141_85_2
      Q2.hcardT141_85_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_85_2 i) (Q2.hfix141_85_2 i) _)
      ?_).symm
  rw [show colData1 (⟨141, by decide⟩ : Fin 148)
        ((colE1 ⟨85, by decide⟩ 120 (transLenTr ⟨85, by decide⟩ 120 hp) : ↥(reps ⟨85, by decide⟩)) : Coordinate 1)
        T141_85 = colFn colCertDiv_141_85_120.D1 (m := 5) from colCertDiv_141_85_120.bind1,
    show colData2 (⟨141, by decide⟩ : Fin 148)
        ((colE2 ⟨85, by decide⟩ 120 hp : ↥(Q2.reps ⟨85, by decide⟩)) : Coordinate 2)
        Q2.T141_85_2 = colFn colCertDiv_141_85_120.D2 (m := 5) from colCertDiv_141_85_120.bind2]
  rw [alnId_141 j hj]
  exact fastcode_of_tau ⟨141, by decide⟩ _ _ _
    ((alnId_141 j hj) ▸ Q2.listedAt (⟨141, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨141, by decide⟩ : Fin 148) hj hq).1) colCertDiv_141_85_120_tau_match


theorem leaf_141_86_0 (hp : 0 < (Q2.transData.getD 86 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨86, by decide⟩ : Fin 148)) (colE2 ⟨86, by decide⟩ 0 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨86, by decide⟩ : Fin 148))
        (colE1 ⟨86, by decide⟩ 0 (transLenTr ⟨86, by decide⟩ 0 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨141, by decide⟩ : Fin 148) ⟨86, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨86, by decide⟩ 0 (transLenTr ⟨86, by decide⟩ 0 hp)) T141_86
      hfix141_86 hinj141_86 hcardT141_86
      (fun i => conj_mem_of_fixedPoints _ _ (T141_86 i) (hfix141_86 i) _)
      ⟨141, by decide⟩ ⟨86, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨86, by decide⟩ 0 hp) Q2.T141_86_2 Q2.hfix141_86_2 Q2.hinj141_86_2
      Q2.hcardT141_86_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_86_2 i) (Q2.hfix141_86_2 i) _)
      ?_).symm
  rw [show colData1 (⟨141, by decide⟩ : Fin 148)
        ((colE1 ⟨86, by decide⟩ 0 (transLenTr ⟨86, by decide⟩ 0 hp) : ↥(reps ⟨86, by decide⟩)) : Coordinate 1)
        T141_86 = colFn colCertDiv_141_86_0.D1 (m := 5) from colCertDiv_141_86_0.bind1,
    show colData2 (⟨141, by decide⟩ : Fin 148)
        ((colE2 ⟨86, by decide⟩ 0 hp : ↥(Q2.reps ⟨86, by decide⟩)) : Coordinate 2)
        Q2.T141_86_2 = colFn colCertDiv_141_86_0.D2 (m := 5) from colCertDiv_141_86_0.bind2]
  rw [alnId_141 j hj]
  exact fastcode_of_tau ⟨141, by decide⟩ _ _ _
    ((alnId_141 j hj) ▸ Q2.listedAt (⟨141, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨141, by decide⟩ : Fin 148) hj hq).1) colCertDiv_141_86_0_tau_match


theorem leaf_141_86_1 (hp : 1 < (Q2.transData.getD 86 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨86, by decide⟩ : Fin 148)) (colE2 ⟨86, by decide⟩ 1 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨86, by decide⟩ : Fin 148))
        (colE1 ⟨86, by decide⟩ 1 (transLenTr ⟨86, by decide⟩ 1 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨141, by decide⟩ : Fin 148) ⟨86, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨86, by decide⟩ 1 (transLenTr ⟨86, by decide⟩ 1 hp)) T141_86
      hfix141_86 hinj141_86 hcardT141_86
      (fun i => conj_mem_of_fixedPoints _ _ (T141_86 i) (hfix141_86 i) _)
      ⟨141, by decide⟩ ⟨86, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨86, by decide⟩ 1 hp) Q2.T141_86_2 Q2.hfix141_86_2 Q2.hinj141_86_2
      Q2.hcardT141_86_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_86_2 i) (Q2.hfix141_86_2 i) _)
      ?_).symm
  rw [show colData1 (⟨141, by decide⟩ : Fin 148)
        ((colE1 ⟨86, by decide⟩ 1 (transLenTr ⟨86, by decide⟩ 1 hp) : ↥(reps ⟨86, by decide⟩)) : Coordinate 1)
        T141_86 = colFn colCertDiv_141_86_1.D1 (m := 5) from colCertDiv_141_86_1.bind1,
    show colData2 (⟨141, by decide⟩ : Fin 148)
        ((colE2 ⟨86, by decide⟩ 1 hp : ↥(Q2.reps ⟨86, by decide⟩)) : Coordinate 2)
        Q2.T141_86_2 = colFn colCertDiv_141_86_1.D2 (m := 5) from colCertDiv_141_86_1.bind2]
  rw [alnId_141 j hj]
  exact fastcode_of_tau ⟨141, by decide⟩ _ _ _
    ((alnId_141 j hj) ▸ Q2.listedAt (⟨141, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨141, by decide⟩ : Fin 148) hj hq).1) colCertDiv_141_86_1_tau_match


theorem leaf_141_86_2 (hp : 2 < (Q2.transData.getD 86 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨86, by decide⟩ : Fin 148)) (colE2 ⟨86, by decide⟩ 2 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨86, by decide⟩ : Fin 148))
        (colE1 ⟨86, by decide⟩ 2 (transLenTr ⟨86, by decide⟩ 2 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨141, by decide⟩ : Fin 148) ⟨86, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨86, by decide⟩ 2 (transLenTr ⟨86, by decide⟩ 2 hp)) T141_86
      hfix141_86 hinj141_86 hcardT141_86
      (fun i => conj_mem_of_fixedPoints _ _ (T141_86 i) (hfix141_86 i) _)
      ⟨141, by decide⟩ ⟨86, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨86, by decide⟩ 2 hp) Q2.T141_86_2 Q2.hfix141_86_2 Q2.hinj141_86_2
      Q2.hcardT141_86_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_86_2 i) (Q2.hfix141_86_2 i) _)
      ?_).symm
  rw [show colData1 (⟨141, by decide⟩ : Fin 148)
        ((colE1 ⟨86, by decide⟩ 2 (transLenTr ⟨86, by decide⟩ 2 hp) : ↥(reps ⟨86, by decide⟩)) : Coordinate 1)
        T141_86 = colFn colCertDiv_141_86_2.D1 (m := 5) from colCertDiv_141_86_2.bind1,
    show colData2 (⟨141, by decide⟩ : Fin 148)
        ((colE2 ⟨86, by decide⟩ 2 hp : ↥(Q2.reps ⟨86, by decide⟩)) : Coordinate 2)
        Q2.T141_86_2 = colFn colCertDiv_141_86_2.D2 (m := 5) from colCertDiv_141_86_2.bind2]
  rw [alnId_141 j hj]
  exact fastcode_of_tau ⟨141, by decide⟩ _ _ _
    ((alnId_141 j hj) ▸ Q2.listedAt (⟨141, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨141, by decide⟩ : Fin 148) hj hq).1) colCertDiv_141_86_2_tau_match


theorem leaf_141_86_3 (hp : 3 < (Q2.transData.getD 86 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨86, by decide⟩ : Fin 148)) (colE2 ⟨86, by decide⟩ 3 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨86, by decide⟩ : Fin 148))
        (colE1 ⟨86, by decide⟩ 3 (transLenTr ⟨86, by decide⟩ 3 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨141, by decide⟩ : Fin 148) ⟨86, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨86, by decide⟩ 3 (transLenTr ⟨86, by decide⟩ 3 hp)) T141_86
      hfix141_86 hinj141_86 hcardT141_86
      (fun i => conj_mem_of_fixedPoints _ _ (T141_86 i) (hfix141_86 i) _)
      ⟨141, by decide⟩ ⟨86, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨86, by decide⟩ 3 hp) Q2.T141_86_2 Q2.hfix141_86_2 Q2.hinj141_86_2
      Q2.hcardT141_86_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_86_2 i) (Q2.hfix141_86_2 i) _)
      ?_).symm
  rw [show colData1 (⟨141, by decide⟩ : Fin 148)
        ((colE1 ⟨86, by decide⟩ 3 (transLenTr ⟨86, by decide⟩ 3 hp) : ↥(reps ⟨86, by decide⟩)) : Coordinate 1)
        T141_86 = colFn colCertDiv_141_86_3.D1 (m := 5) from colCertDiv_141_86_3.bind1,
    show colData2 (⟨141, by decide⟩ : Fin 148)
        ((colE2 ⟨86, by decide⟩ 3 hp : ↥(Q2.reps ⟨86, by decide⟩)) : Coordinate 2)
        Q2.T141_86_2 = colFn colCertDiv_141_86_3.D2 (m := 5) from colCertDiv_141_86_3.bind2]
  rw [alnId_141 j hj]
  exact fastcode_of_tau ⟨141, by decide⟩ _ _ _
    ((alnId_141 j hj) ▸ Q2.listedAt (⟨141, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨141, by decide⟩ : Fin 148) hj hq).1) colCertDiv_141_86_3_tau_match


theorem leaf_141_86_4 (hp : 4 < (Q2.transData.getD 86 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨86, by decide⟩ : Fin 148)) (colE2 ⟨86, by decide⟩ 4 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨86, by decide⟩ : Fin 148))
        (colE1 ⟨86, by decide⟩ 4 (transLenTr ⟨86, by decide⟩ 4 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨141, by decide⟩ : Fin 148) ⟨86, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨86, by decide⟩ 4 (transLenTr ⟨86, by decide⟩ 4 hp)) T141_86
      hfix141_86 hinj141_86 hcardT141_86
      (fun i => conj_mem_of_fixedPoints _ _ (T141_86 i) (hfix141_86 i) _)
      ⟨141, by decide⟩ ⟨86, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨86, by decide⟩ 4 hp) Q2.T141_86_2 Q2.hfix141_86_2 Q2.hinj141_86_2
      Q2.hcardT141_86_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_86_2 i) (Q2.hfix141_86_2 i) _)
      ?_).symm
  rw [show colData1 (⟨141, by decide⟩ : Fin 148)
        ((colE1 ⟨86, by decide⟩ 4 (transLenTr ⟨86, by decide⟩ 4 hp) : ↥(reps ⟨86, by decide⟩)) : Coordinate 1)
        T141_86 = colFn colCertDiv_141_86_4.D1 (m := 5) from colCertDiv_141_86_4.bind1,
    show colData2 (⟨141, by decide⟩ : Fin 148)
        ((colE2 ⟨86, by decide⟩ 4 hp : ↥(Q2.reps ⟨86, by decide⟩)) : Coordinate 2)
        Q2.T141_86_2 = colFn colCertDiv_141_86_4.D2 (m := 5) from colCertDiv_141_86_4.bind2]
  rw [alnId_141 j hj]
  exact fastcode_of_tau ⟨141, by decide⟩ _ _ _
    ((alnId_141 j hj) ▸ Q2.listedAt (⟨141, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨141, by decide⟩ : Fin 148) hj hq).1) colCertDiv_141_86_4_tau_match


theorem leaf_141_86_5 (hp : 5 < (Q2.transData.getD 86 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨86, by decide⟩ : Fin 148)) (colE2 ⟨86, by decide⟩ 5 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨86, by decide⟩ : Fin 148))
        (colE1 ⟨86, by decide⟩ 5 (transLenTr ⟨86, by decide⟩ 5 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨86, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨86, by decide⟩ 5 (transLenTr ⟨86, by decide⟩ 5 hp)) T141_86
      hfix141_86 hinj141_86 hcardT141_86
      (fun i => conj_mem_of_fixedPoints _ _ (T141_86 i) (hfix141_86 i) _)
      ⟨141, by decide⟩ ⟨86, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨86, by decide⟩ 5 hp) Q2.T141_86_2 Q2.hfix141_86_2 Q2.hinj141_86_2
      Q2.hcardT141_86_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_86_2 i) (Q2.hfix141_86_2 i) _)
      colCert_141_86_5.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_86_6 (hp : 6 < (Q2.transData.getD 86 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨86, by decide⟩ : Fin 148)) (colE2 ⟨86, by decide⟩ 6 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨86, by decide⟩ : Fin 148))
        (colE1 ⟨86, by decide⟩ 6 (transLenTr ⟨86, by decide⟩ 6 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨86, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨86, by decide⟩ 6 (transLenTr ⟨86, by decide⟩ 6 hp)) T141_86
      hfix141_86 hinj141_86 hcardT141_86
      (fun i => conj_mem_of_fixedPoints _ _ (T141_86 i) (hfix141_86 i) _)
      ⟨141, by decide⟩ ⟨86, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨86, by decide⟩ 6 hp) Q2.T141_86_2 Q2.hfix141_86_2 Q2.hinj141_86_2
      Q2.hcardT141_86_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_86_2 i) (Q2.hfix141_86_2 i) _)
      colCert_141_86_6.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_86_7 (hp : 7 < (Q2.transData.getD 86 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨86, by decide⟩ : Fin 148)) (colE2 ⟨86, by decide⟩ 7 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨86, by decide⟩ : Fin 148))
        (colE1 ⟨86, by decide⟩ 7 (transLenTr ⟨86, by decide⟩ 7 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨86, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨86, by decide⟩ 7 (transLenTr ⟨86, by decide⟩ 7 hp)) T141_86
      hfix141_86 hinj141_86 hcardT141_86
      (fun i => conj_mem_of_fixedPoints _ _ (T141_86 i) (hfix141_86 i) _)
      ⟨141, by decide⟩ ⟨86, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨86, by decide⟩ 7 hp) Q2.T141_86_2 Q2.hfix141_86_2 Q2.hinj141_86_2
      Q2.hcardT141_86_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_86_2 i) (Q2.hfix141_86_2 i) _)
      colCert_141_86_7.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_86_8 (hp : 8 < (Q2.transData.getD 86 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨86, by decide⟩ : Fin 148)) (colE2 ⟨86, by decide⟩ 8 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨86, by decide⟩ : Fin 148))
        (colE1 ⟨86, by decide⟩ 8 (transLenTr ⟨86, by decide⟩ 8 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨86, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨86, by decide⟩ 8 (transLenTr ⟨86, by decide⟩ 8 hp)) T141_86
      hfix141_86 hinj141_86 hcardT141_86
      (fun i => conj_mem_of_fixedPoints _ _ (T141_86 i) (hfix141_86 i) _)
      ⟨141, by decide⟩ ⟨86, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨86, by decide⟩ 8 hp) Q2.T141_86_2 Q2.hfix141_86_2 Q2.hinj141_86_2
      Q2.hcardT141_86_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_86_2 i) (Q2.hfix141_86_2 i) _)
      colCert_141_86_8.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_86_9 (hp : 9 < (Q2.transData.getD 86 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨86, by decide⟩ : Fin 148)) (colE2 ⟨86, by decide⟩ 9 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨86, by decide⟩ : Fin 148))
        (colE1 ⟨86, by decide⟩ 9 (transLenTr ⟨86, by decide⟩ 9 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨86, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨86, by decide⟩ 9 (transLenTr ⟨86, by decide⟩ 9 hp)) T141_86
      hfix141_86 hinj141_86 hcardT141_86
      (fun i => conj_mem_of_fixedPoints _ _ (T141_86 i) (hfix141_86 i) _)
      ⟨141, by decide⟩ ⟨86, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨86, by decide⟩ 9 hp) Q2.T141_86_2 Q2.hfix141_86_2 Q2.hinj141_86_2
      Q2.hcardT141_86_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_86_2 i) (Q2.hfix141_86_2 i) _)
      colCert_141_86_9.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_86_10 (hp : 10 < (Q2.transData.getD 86 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨86, by decide⟩ : Fin 148)) (colE2 ⟨86, by decide⟩ 10 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨86, by decide⟩ : Fin 148))
        (colE1 ⟨86, by decide⟩ 10 (transLenTr ⟨86, by decide⟩ 10 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨86, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨86, by decide⟩ 10 (transLenTr ⟨86, by decide⟩ 10 hp)) T141_86
      hfix141_86 hinj141_86 hcardT141_86
      (fun i => conj_mem_of_fixedPoints _ _ (T141_86 i) (hfix141_86 i) _)
      ⟨141, by decide⟩ ⟨86, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨86, by decide⟩ 10 hp) Q2.T141_86_2 Q2.hfix141_86_2 Q2.hinj141_86_2
      Q2.hcardT141_86_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_86_2 i) (Q2.hfix141_86_2 i) _)
      colCert_141_86_10.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_86_11 (hp : 11 < (Q2.transData.getD 86 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨86, by decide⟩ : Fin 148)) (colE2 ⟨86, by decide⟩ 11 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨86, by decide⟩ : Fin 148))
        (colE1 ⟨86, by decide⟩ 11 (transLenTr ⟨86, by decide⟩ 11 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨86, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨86, by decide⟩ 11 (transLenTr ⟨86, by decide⟩ 11 hp)) T141_86
      hfix141_86 hinj141_86 hcardT141_86
      (fun i => conj_mem_of_fixedPoints _ _ (T141_86 i) (hfix141_86 i) _)
      ⟨141, by decide⟩ ⟨86, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨86, by decide⟩ 11 hp) Q2.T141_86_2 Q2.hfix141_86_2 Q2.hinj141_86_2
      Q2.hcardT141_86_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_86_2 i) (Q2.hfix141_86_2 i) _)
      colCert_141_86_11.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_86_12 (hp : 12 < (Q2.transData.getD 86 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨86, by decide⟩ : Fin 148)) (colE2 ⟨86, by decide⟩ 12 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨86, by decide⟩ : Fin 148))
        (colE1 ⟨86, by decide⟩ 12 (transLenTr ⟨86, by decide⟩ 12 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨86, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨86, by decide⟩ 12 (transLenTr ⟨86, by decide⟩ 12 hp)) T141_86
      hfix141_86 hinj141_86 hcardT141_86
      (fun i => conj_mem_of_fixedPoints _ _ (T141_86 i) (hfix141_86 i) _)
      ⟨141, by decide⟩ ⟨86, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨86, by decide⟩ 12 hp) Q2.T141_86_2 Q2.hfix141_86_2 Q2.hinj141_86_2
      Q2.hcardT141_86_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_86_2 i) (Q2.hfix141_86_2 i) _)
      colCert_141_86_12.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_86_13 (hp : 13 < (Q2.transData.getD 86 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨86, by decide⟩ : Fin 148)) (colE2 ⟨86, by decide⟩ 13 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨86, by decide⟩ : Fin 148))
        (colE1 ⟨86, by decide⟩ 13 (transLenTr ⟨86, by decide⟩ 13 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨86, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨86, by decide⟩ 13 (transLenTr ⟨86, by decide⟩ 13 hp)) T141_86
      hfix141_86 hinj141_86 hcardT141_86
      (fun i => conj_mem_of_fixedPoints _ _ (T141_86 i) (hfix141_86 i) _)
      ⟨141, by decide⟩ ⟨86, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨86, by decide⟩ 13 hp) Q2.T141_86_2 Q2.hfix141_86_2 Q2.hinj141_86_2
      Q2.hcardT141_86_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_86_2 i) (Q2.hfix141_86_2 i) _)
      colCert_141_86_13.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_86_14 (hp : 14 < (Q2.transData.getD 86 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨86, by decide⟩ : Fin 148)) (colE2 ⟨86, by decide⟩ 14 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨86, by decide⟩ : Fin 148))
        (colE1 ⟨86, by decide⟩ 14 (transLenTr ⟨86, by decide⟩ 14 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨86, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨86, by decide⟩ 14 (transLenTr ⟨86, by decide⟩ 14 hp)) T141_86
      hfix141_86 hinj141_86 hcardT141_86
      (fun i => conj_mem_of_fixedPoints _ _ (T141_86 i) (hfix141_86 i) _)
      ⟨141, by decide⟩ ⟨86, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨86, by decide⟩ 14 hp) Q2.T141_86_2 Q2.hfix141_86_2 Q2.hinj141_86_2
      Q2.hcardT141_86_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_86_2 i) (Q2.hfix141_86_2 i) _)
      colCert_141_86_14.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_86_15 (hp : 15 < (Q2.transData.getD 86 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨86, by decide⟩ : Fin 148)) (colE2 ⟨86, by decide⟩ 15 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨86, by decide⟩ : Fin 148))
        (colE1 ⟨86, by decide⟩ 15 (transLenTr ⟨86, by decide⟩ 15 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨86, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨86, by decide⟩ 15 (transLenTr ⟨86, by decide⟩ 15 hp)) T141_86
      hfix141_86 hinj141_86 hcardT141_86
      (fun i => conj_mem_of_fixedPoints _ _ (T141_86 i) (hfix141_86 i) _)
      ⟨141, by decide⟩ ⟨86, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨86, by decide⟩ 15 hp) Q2.T141_86_2 Q2.hfix141_86_2 Q2.hinj141_86_2
      Q2.hcardT141_86_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_86_2 i) (Q2.hfix141_86_2 i) _)
      colCert_141_86_15.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_86_16 (hp : 16 < (Q2.transData.getD 86 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨86, by decide⟩ : Fin 148)) (colE2 ⟨86, by decide⟩ 16 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨86, by decide⟩ : Fin 148))
        (colE1 ⟨86, by decide⟩ 16 (transLenTr ⟨86, by decide⟩ 16 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨86, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨86, by decide⟩ 16 (transLenTr ⟨86, by decide⟩ 16 hp)) T141_86
      hfix141_86 hinj141_86 hcardT141_86
      (fun i => conj_mem_of_fixedPoints _ _ (T141_86 i) (hfix141_86 i) _)
      ⟨141, by decide⟩ ⟨86, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨86, by decide⟩ 16 hp) Q2.T141_86_2 Q2.hfix141_86_2 Q2.hinj141_86_2
      Q2.hcardT141_86_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_86_2 i) (Q2.hfix141_86_2 i) _)
      colCert_141_86_16.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_86_17 (hp : 17 < (Q2.transData.getD 86 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨86, by decide⟩ : Fin 148)) (colE2 ⟨86, by decide⟩ 17 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨86, by decide⟩ : Fin 148))
        (colE1 ⟨86, by decide⟩ 17 (transLenTr ⟨86, by decide⟩ 17 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨86, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨86, by decide⟩ 17 (transLenTr ⟨86, by decide⟩ 17 hp)) T141_86
      hfix141_86 hinj141_86 hcardT141_86
      (fun i => conj_mem_of_fixedPoints _ _ (T141_86 i) (hfix141_86 i) _)
      ⟨141, by decide⟩ ⟨86, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨86, by decide⟩ 17 hp) Q2.T141_86_2 Q2.hfix141_86_2 Q2.hinj141_86_2
      Q2.hcardT141_86_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_86_2 i) (Q2.hfix141_86_2 i) _)
      colCert_141_86_17.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_86_18 (hp : 18 < (Q2.transData.getD 86 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨86, by decide⟩ : Fin 148)) (colE2 ⟨86, by decide⟩ 18 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨86, by decide⟩ : Fin 148))
        (colE1 ⟨86, by decide⟩ 18 (transLenTr ⟨86, by decide⟩ 18 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨86, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨86, by decide⟩ 18 (transLenTr ⟨86, by decide⟩ 18 hp)) T141_86
      hfix141_86 hinj141_86 hcardT141_86
      (fun i => conj_mem_of_fixedPoints _ _ (T141_86 i) (hfix141_86 i) _)
      ⟨141, by decide⟩ ⟨86, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨86, by decide⟩ 18 hp) Q2.T141_86_2 Q2.hfix141_86_2 Q2.hinj141_86_2
      Q2.hcardT141_86_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_86_2 i) (Q2.hfix141_86_2 i) _)
      colCert_141_86_18.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_86_19 (hp : 19 < (Q2.transData.getD 86 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨86, by decide⟩ : Fin 148)) (colE2 ⟨86, by decide⟩ 19 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨86, by decide⟩ : Fin 148))
        (colE1 ⟨86, by decide⟩ 19 (transLenTr ⟨86, by decide⟩ 19 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨86, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨86, by decide⟩ 19 (transLenTr ⟨86, by decide⟩ 19 hp)) T141_86
      hfix141_86 hinj141_86 hcardT141_86
      (fun i => conj_mem_of_fixedPoints _ _ (T141_86 i) (hfix141_86 i) _)
      ⟨141, by decide⟩ ⟨86, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨86, by decide⟩ 19 hp) Q2.T141_86_2 Q2.hfix141_86_2 Q2.hinj141_86_2
      Q2.hcardT141_86_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_86_2 i) (Q2.hfix141_86_2 i) _)
      colCert_141_86_19.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_86_20 (hp : 20 < (Q2.transData.getD 86 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨86, by decide⟩ : Fin 148)) (colE2 ⟨86, by decide⟩ 20 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨86, by decide⟩ : Fin 148))
        (colE1 ⟨86, by decide⟩ 20 (transLenTr ⟨86, by decide⟩ 20 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨86, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨86, by decide⟩ 20 (transLenTr ⟨86, by decide⟩ 20 hp)) T141_86
      hfix141_86 hinj141_86 hcardT141_86
      (fun i => conj_mem_of_fixedPoints _ _ (T141_86 i) (hfix141_86 i) _)
      ⟨141, by decide⟩ ⟨86, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨86, by decide⟩ 20 hp) Q2.T141_86_2 Q2.hfix141_86_2 Q2.hinj141_86_2
      Q2.hcardT141_86_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_86_2 i) (Q2.hfix141_86_2 i) _)
      colCert_141_86_20.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_86_21 (hp : 21 < (Q2.transData.getD 86 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨86, by decide⟩ : Fin 148)) (colE2 ⟨86, by decide⟩ 21 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨86, by decide⟩ : Fin 148))
        (colE1 ⟨86, by decide⟩ 21 (transLenTr ⟨86, by decide⟩ 21 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨86, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨86, by decide⟩ 21 (transLenTr ⟨86, by decide⟩ 21 hp)) T141_86
      hfix141_86 hinj141_86 hcardT141_86
      (fun i => conj_mem_of_fixedPoints _ _ (T141_86 i) (hfix141_86 i) _)
      ⟨141, by decide⟩ ⟨86, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨86, by decide⟩ 21 hp) Q2.T141_86_2 Q2.hfix141_86_2 Q2.hinj141_86_2
      Q2.hcardT141_86_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_86_2 i) (Q2.hfix141_86_2 i) _)
      colCert_141_86_21.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_86_22 (hp : 22 < (Q2.transData.getD 86 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨86, by decide⟩ : Fin 148)) (colE2 ⟨86, by decide⟩ 22 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨86, by decide⟩ : Fin 148))
        (colE1 ⟨86, by decide⟩ 22 (transLenTr ⟨86, by decide⟩ 22 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨86, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨86, by decide⟩ 22 (transLenTr ⟨86, by decide⟩ 22 hp)) T141_86
      hfix141_86 hinj141_86 hcardT141_86
      (fun i => conj_mem_of_fixedPoints _ _ (T141_86 i) (hfix141_86 i) _)
      ⟨141, by decide⟩ ⟨86, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨86, by decide⟩ 22 hp) Q2.T141_86_2 Q2.hfix141_86_2 Q2.hinj141_86_2
      Q2.hcardT141_86_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_86_2 i) (Q2.hfix141_86_2 i) _)
      colCert_141_86_22.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_86_23 (hp : 23 < (Q2.transData.getD 86 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨86, by decide⟩ : Fin 148)) (colE2 ⟨86, by decide⟩ 23 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨86, by decide⟩ : Fin 148))
        (colE1 ⟨86, by decide⟩ 23 (transLenTr ⟨86, by decide⟩ 23 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨86, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨86, by decide⟩ 23 (transLenTr ⟨86, by decide⟩ 23 hp)) T141_86
      hfix141_86 hinj141_86 hcardT141_86
      (fun i => conj_mem_of_fixedPoints _ _ (T141_86 i) (hfix141_86 i) _)
      ⟨141, by decide⟩ ⟨86, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨86, by decide⟩ 23 hp) Q2.T141_86_2 Q2.hfix141_86_2 Q2.hinj141_86_2
      Q2.hcardT141_86_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_86_2 i) (Q2.hfix141_86_2 i) _)
      colCert_141_86_23.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_86_24 (hp : 24 < (Q2.transData.getD 86 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨86, by decide⟩ : Fin 148)) (colE2 ⟨86, by decide⟩ 24 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨86, by decide⟩ : Fin 148))
        (colE1 ⟨86, by decide⟩ 24 (transLenTr ⟨86, by decide⟩ 24 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨86, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨86, by decide⟩ 24 (transLenTr ⟨86, by decide⟩ 24 hp)) T141_86
      hfix141_86 hinj141_86 hcardT141_86
      (fun i => conj_mem_of_fixedPoints _ _ (T141_86 i) (hfix141_86 i) _)
      ⟨141, by decide⟩ ⟨86, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨86, by decide⟩ 24 hp) Q2.T141_86_2 Q2.hfix141_86_2 Q2.hinj141_86_2
      Q2.hcardT141_86_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_86_2 i) (Q2.hfix141_86_2 i) _)
      colCert_141_86_24.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_87_0 (hp : 0 < (Q2.transData.getD 87 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨87, by decide⟩ : Fin 148)) (colE2 ⟨87, by decide⟩ 0 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨87, by decide⟩ : Fin 148))
        (colE1 ⟨87, by decide⟩ 0 (transLenTr ⟨87, by decide⟩ 0 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨87, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨87, by decide⟩ 0 (transLenTr ⟨87, by decide⟩ 0 hp)) T141_87
      hfix141_87 hinj141_87 hcardT141_87
      (fun i => conj_mem_of_fixedPoints _ _ (T141_87 i) (hfix141_87 i) _)
      ⟨141, by decide⟩ ⟨87, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨87, by decide⟩ 0 hp) Q2.T141_87_2 Q2.hfix141_87_2 Q2.hinj141_87_2
      Q2.hcardT141_87_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_87_2 i) (Q2.hfix141_87_2 i) _)
      colCert_141_87_0.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_87_1 (hp : 1 < (Q2.transData.getD 87 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨87, by decide⟩ : Fin 148)) (colE2 ⟨87, by decide⟩ 1 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨87, by decide⟩ : Fin 148))
        (colE1 ⟨87, by decide⟩ 1 (transLenTr ⟨87, by decide⟩ 1 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨87, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨87, by decide⟩ 1 (transLenTr ⟨87, by decide⟩ 1 hp)) T141_87
      hfix141_87 hinj141_87 hcardT141_87
      (fun i => conj_mem_of_fixedPoints _ _ (T141_87 i) (hfix141_87 i) _)
      ⟨141, by decide⟩ ⟨87, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨87, by decide⟩ 1 hp) Q2.T141_87_2 Q2.hfix141_87_2 Q2.hinj141_87_2
      Q2.hcardT141_87_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_87_2 i) (Q2.hfix141_87_2 i) _)
      colCert_141_87_1.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_87_2 (hp : 2 < (Q2.transData.getD 87 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨87, by decide⟩ : Fin 148)) (colE2 ⟨87, by decide⟩ 2 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨87, by decide⟩ : Fin 148))
        (colE1 ⟨87, by decide⟩ 2 (transLenTr ⟨87, by decide⟩ 2 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨87, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨87, by decide⟩ 2 (transLenTr ⟨87, by decide⟩ 2 hp)) T141_87
      hfix141_87 hinj141_87 hcardT141_87
      (fun i => conj_mem_of_fixedPoints _ _ (T141_87 i) (hfix141_87 i) _)
      ⟨141, by decide⟩ ⟨87, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨87, by decide⟩ 2 hp) Q2.T141_87_2 Q2.hfix141_87_2 Q2.hinj141_87_2
      Q2.hcardT141_87_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_87_2 i) (Q2.hfix141_87_2 i) _)
      colCert_141_87_2.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_87_3 (hp : 3 < (Q2.transData.getD 87 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨87, by decide⟩ : Fin 148)) (colE2 ⟨87, by decide⟩ 3 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨87, by decide⟩ : Fin 148))
        (colE1 ⟨87, by decide⟩ 3 (transLenTr ⟨87, by decide⟩ 3 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨87, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨87, by decide⟩ 3 (transLenTr ⟨87, by decide⟩ 3 hp)) T141_87
      hfix141_87 hinj141_87 hcardT141_87
      (fun i => conj_mem_of_fixedPoints _ _ (T141_87 i) (hfix141_87 i) _)
      ⟨141, by decide⟩ ⟨87, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨87, by decide⟩ 3 hp) Q2.T141_87_2 Q2.hfix141_87_2 Q2.hinj141_87_2
      Q2.hcardT141_87_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_87_2 i) (Q2.hfix141_87_2 i) _)
      colCert_141_87_3.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_87_4 (hp : 4 < (Q2.transData.getD 87 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨87, by decide⟩ : Fin 148)) (colE2 ⟨87, by decide⟩ 4 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨87, by decide⟩ : Fin 148))
        (colE1 ⟨87, by decide⟩ 4 (transLenTr ⟨87, by decide⟩ 4 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨87, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨87, by decide⟩ 4 (transLenTr ⟨87, by decide⟩ 4 hp)) T141_87
      hfix141_87 hinj141_87 hcardT141_87
      (fun i => conj_mem_of_fixedPoints _ _ (T141_87 i) (hfix141_87 i) _)
      ⟨141, by decide⟩ ⟨87, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨87, by decide⟩ 4 hp) Q2.T141_87_2 Q2.hfix141_87_2 Q2.hinj141_87_2
      Q2.hcardT141_87_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_87_2 i) (Q2.hfix141_87_2 i) _)
      colCert_141_87_4.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_87_5 (hp : 5 < (Q2.transData.getD 87 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨87, by decide⟩ : Fin 148)) (colE2 ⟨87, by decide⟩ 5 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨87, by decide⟩ : Fin 148))
        (colE1 ⟨87, by decide⟩ 5 (transLenTr ⟨87, by decide⟩ 5 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨87, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨87, by decide⟩ 5 (transLenTr ⟨87, by decide⟩ 5 hp)) T141_87
      hfix141_87 hinj141_87 hcardT141_87
      (fun i => conj_mem_of_fixedPoints _ _ (T141_87 i) (hfix141_87 i) _)
      ⟨141, by decide⟩ ⟨87, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨87, by decide⟩ 5 hp) Q2.T141_87_2 Q2.hfix141_87_2 Q2.hinj141_87_2
      Q2.hcardT141_87_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_87_2 i) (Q2.hfix141_87_2 i) _)
      colCert_141_87_5.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_87_6 (hp : 6 < (Q2.transData.getD 87 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨87, by decide⟩ : Fin 148)) (colE2 ⟨87, by decide⟩ 6 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨87, by decide⟩ : Fin 148))
        (colE1 ⟨87, by decide⟩ 6 (transLenTr ⟨87, by decide⟩ 6 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨87, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨87, by decide⟩ 6 (transLenTr ⟨87, by decide⟩ 6 hp)) T141_87
      hfix141_87 hinj141_87 hcardT141_87
      (fun i => conj_mem_of_fixedPoints _ _ (T141_87 i) (hfix141_87 i) _)
      ⟨141, by decide⟩ ⟨87, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨87, by decide⟩ 6 hp) Q2.T141_87_2 Q2.hfix141_87_2 Q2.hinj141_87_2
      Q2.hcardT141_87_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_87_2 i) (Q2.hfix141_87_2 i) _)
      colCert_141_87_6.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_87_7 (hp : 7 < (Q2.transData.getD 87 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨87, by decide⟩ : Fin 148)) (colE2 ⟨87, by decide⟩ 7 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨87, by decide⟩ : Fin 148))
        (colE1 ⟨87, by decide⟩ 7 (transLenTr ⟨87, by decide⟩ 7 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨87, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨87, by decide⟩ 7 (transLenTr ⟨87, by decide⟩ 7 hp)) T141_87
      hfix141_87 hinj141_87 hcardT141_87
      (fun i => conj_mem_of_fixedPoints _ _ (T141_87 i) (hfix141_87 i) _)
      ⟨141, by decide⟩ ⟨87, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨87, by decide⟩ 7 hp) Q2.T141_87_2 Q2.hfix141_87_2 Q2.hinj141_87_2
      Q2.hcardT141_87_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_87_2 i) (Q2.hfix141_87_2 i) _)
      colCert_141_87_7.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_87_8 (hp : 8 < (Q2.transData.getD 87 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨87, by decide⟩ : Fin 148)) (colE2 ⟨87, by decide⟩ 8 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨87, by decide⟩ : Fin 148))
        (colE1 ⟨87, by decide⟩ 8 (transLenTr ⟨87, by decide⟩ 8 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨87, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨87, by decide⟩ 8 (transLenTr ⟨87, by decide⟩ 8 hp)) T141_87
      hfix141_87 hinj141_87 hcardT141_87
      (fun i => conj_mem_of_fixedPoints _ _ (T141_87 i) (hfix141_87 i) _)
      ⟨141, by decide⟩ ⟨87, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨87, by decide⟩ 8 hp) Q2.T141_87_2 Q2.hfix141_87_2 Q2.hinj141_87_2
      Q2.hcardT141_87_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_87_2 i) (Q2.hfix141_87_2 i) _)
      colCert_141_87_8.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_87_9 (hp : 9 < (Q2.transData.getD 87 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨87, by decide⟩ : Fin 148)) (colE2 ⟨87, by decide⟩ 9 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨87, by decide⟩ : Fin 148))
        (colE1 ⟨87, by decide⟩ 9 (transLenTr ⟨87, by decide⟩ 9 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨87, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨87, by decide⟩ 9 (transLenTr ⟨87, by decide⟩ 9 hp)) T141_87
      hfix141_87 hinj141_87 hcardT141_87
      (fun i => conj_mem_of_fixedPoints _ _ (T141_87 i) (hfix141_87 i) _)
      ⟨141, by decide⟩ ⟨87, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨87, by decide⟩ 9 hp) Q2.T141_87_2 Q2.hfix141_87_2 Q2.hinj141_87_2
      Q2.hcardT141_87_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_87_2 i) (Q2.hfix141_87_2 i) _)
      colCert_141_87_9.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_87_10 (hp : 10 < (Q2.transData.getD 87 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨87, by decide⟩ : Fin 148)) (colE2 ⟨87, by decide⟩ 10 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨87, by decide⟩ : Fin 148))
        (colE1 ⟨87, by decide⟩ 10 (transLenTr ⟨87, by decide⟩ 10 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨87, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨87, by decide⟩ 10 (transLenTr ⟨87, by decide⟩ 10 hp)) T141_87
      hfix141_87 hinj141_87 hcardT141_87
      (fun i => conj_mem_of_fixedPoints _ _ (T141_87 i) (hfix141_87 i) _)
      ⟨141, by decide⟩ ⟨87, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨87, by decide⟩ 10 hp) Q2.T141_87_2 Q2.hfix141_87_2 Q2.hinj141_87_2
      Q2.hcardT141_87_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_87_2 i) (Q2.hfix141_87_2 i) _)
      colCert_141_87_10.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_87_11 (hp : 11 < (Q2.transData.getD 87 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨87, by decide⟩ : Fin 148)) (colE2 ⟨87, by decide⟩ 11 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨87, by decide⟩ : Fin 148))
        (colE1 ⟨87, by decide⟩ 11 (transLenTr ⟨87, by decide⟩ 11 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨87, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨87, by decide⟩ 11 (transLenTr ⟨87, by decide⟩ 11 hp)) T141_87
      hfix141_87 hinj141_87 hcardT141_87
      (fun i => conj_mem_of_fixedPoints _ _ (T141_87 i) (hfix141_87 i) _)
      ⟨141, by decide⟩ ⟨87, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨87, by decide⟩ 11 hp) Q2.T141_87_2 Q2.hfix141_87_2 Q2.hinj141_87_2
      Q2.hcardT141_87_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_87_2 i) (Q2.hfix141_87_2 i) _)
      colCert_141_87_11.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_87_12 (hp : 12 < (Q2.transData.getD 87 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨87, by decide⟩ : Fin 148)) (colE2 ⟨87, by decide⟩ 12 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨87, by decide⟩ : Fin 148))
        (colE1 ⟨87, by decide⟩ 12 (transLenTr ⟨87, by decide⟩ 12 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨87, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨87, by decide⟩ 12 (transLenTr ⟨87, by decide⟩ 12 hp)) T141_87
      hfix141_87 hinj141_87 hcardT141_87
      (fun i => conj_mem_of_fixedPoints _ _ (T141_87 i) (hfix141_87 i) _)
      ⟨141, by decide⟩ ⟨87, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨87, by decide⟩ 12 hp) Q2.T141_87_2 Q2.hfix141_87_2 Q2.hinj141_87_2
      Q2.hcardT141_87_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_87_2 i) (Q2.hfix141_87_2 i) _)
      colCert_141_87_12.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_87_13 (hp : 13 < (Q2.transData.getD 87 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨87, by decide⟩ : Fin 148)) (colE2 ⟨87, by decide⟩ 13 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨87, by decide⟩ : Fin 148))
        (colE1 ⟨87, by decide⟩ 13 (transLenTr ⟨87, by decide⟩ 13 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨87, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨87, by decide⟩ 13 (transLenTr ⟨87, by decide⟩ 13 hp)) T141_87
      hfix141_87 hinj141_87 hcardT141_87
      (fun i => conj_mem_of_fixedPoints _ _ (T141_87 i) (hfix141_87 i) _)
      ⟨141, by decide⟩ ⟨87, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨87, by decide⟩ 13 hp) Q2.T141_87_2 Q2.hfix141_87_2 Q2.hinj141_87_2
      Q2.hcardT141_87_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_87_2 i) (Q2.hfix141_87_2 i) _)
      colCert_141_87_13.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_87_14 (hp : 14 < (Q2.transData.getD 87 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨87, by decide⟩ : Fin 148)) (colE2 ⟨87, by decide⟩ 14 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨87, by decide⟩ : Fin 148))
        (colE1 ⟨87, by decide⟩ 14 (transLenTr ⟨87, by decide⟩ 14 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨87, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨87, by decide⟩ 14 (transLenTr ⟨87, by decide⟩ 14 hp)) T141_87
      hfix141_87 hinj141_87 hcardT141_87
      (fun i => conj_mem_of_fixedPoints _ _ (T141_87 i) (hfix141_87 i) _)
      ⟨141, by decide⟩ ⟨87, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨87, by decide⟩ 14 hp) Q2.T141_87_2 Q2.hfix141_87_2 Q2.hinj141_87_2
      Q2.hcardT141_87_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_87_2 i) (Q2.hfix141_87_2 i) _)
      colCert_141_87_14.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_87_15 (hp : 15 < (Q2.transData.getD 87 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨87, by decide⟩ : Fin 148)) (colE2 ⟨87, by decide⟩ 15 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨87, by decide⟩ : Fin 148))
        (colE1 ⟨87, by decide⟩ 15 (transLenTr ⟨87, by decide⟩ 15 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨87, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨87, by decide⟩ 15 (transLenTr ⟨87, by decide⟩ 15 hp)) T141_87
      hfix141_87 hinj141_87 hcardT141_87
      (fun i => conj_mem_of_fixedPoints _ _ (T141_87 i) (hfix141_87 i) _)
      ⟨141, by decide⟩ ⟨87, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨87, by decide⟩ 15 hp) Q2.T141_87_2 Q2.hfix141_87_2 Q2.hinj141_87_2
      Q2.hcardT141_87_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_87_2 i) (Q2.hfix141_87_2 i) _)
      colCert_141_87_15.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_87_16 (hp : 16 < (Q2.transData.getD 87 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨87, by decide⟩ : Fin 148)) (colE2 ⟨87, by decide⟩ 16 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨87, by decide⟩ : Fin 148))
        (colE1 ⟨87, by decide⟩ 16 (transLenTr ⟨87, by decide⟩ 16 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨87, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨87, by decide⟩ 16 (transLenTr ⟨87, by decide⟩ 16 hp)) T141_87
      hfix141_87 hinj141_87 hcardT141_87
      (fun i => conj_mem_of_fixedPoints _ _ (T141_87 i) (hfix141_87 i) _)
      ⟨141, by decide⟩ ⟨87, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨87, by decide⟩ 16 hp) Q2.T141_87_2 Q2.hfix141_87_2 Q2.hinj141_87_2
      Q2.hcardT141_87_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_87_2 i) (Q2.hfix141_87_2 i) _)
      colCert_141_87_16.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_87_17 (hp : 17 < (Q2.transData.getD 87 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨87, by decide⟩ : Fin 148)) (colE2 ⟨87, by decide⟩ 17 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨87, by decide⟩ : Fin 148))
        (colE1 ⟨87, by decide⟩ 17 (transLenTr ⟨87, by decide⟩ 17 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨87, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨87, by decide⟩ 17 (transLenTr ⟨87, by decide⟩ 17 hp)) T141_87
      hfix141_87 hinj141_87 hcardT141_87
      (fun i => conj_mem_of_fixedPoints _ _ (T141_87 i) (hfix141_87 i) _)
      ⟨141, by decide⟩ ⟨87, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨87, by decide⟩ 17 hp) Q2.T141_87_2 Q2.hfix141_87_2 Q2.hinj141_87_2
      Q2.hcardT141_87_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_87_2 i) (Q2.hfix141_87_2 i) _)
      colCert_141_87_17.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_87_18 (hp : 18 < (Q2.transData.getD 87 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨87, by decide⟩ : Fin 148)) (colE2 ⟨87, by decide⟩ 18 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨87, by decide⟩ : Fin 148))
        (colE1 ⟨87, by decide⟩ 18 (transLenTr ⟨87, by decide⟩ 18 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨87, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨87, by decide⟩ 18 (transLenTr ⟨87, by decide⟩ 18 hp)) T141_87
      hfix141_87 hinj141_87 hcardT141_87
      (fun i => conj_mem_of_fixedPoints _ _ (T141_87 i) (hfix141_87 i) _)
      ⟨141, by decide⟩ ⟨87, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨87, by decide⟩ 18 hp) Q2.T141_87_2 Q2.hfix141_87_2 Q2.hinj141_87_2
      Q2.hcardT141_87_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_87_2 i) (Q2.hfix141_87_2 i) _)
      colCert_141_87_18.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_87_19 (hp : 19 < (Q2.transData.getD 87 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨87, by decide⟩ : Fin 148)) (colE2 ⟨87, by decide⟩ 19 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨87, by decide⟩ : Fin 148))
        (colE1 ⟨87, by decide⟩ 19 (transLenTr ⟨87, by decide⟩ 19 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨87, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨87, by decide⟩ 19 (transLenTr ⟨87, by decide⟩ 19 hp)) T141_87
      hfix141_87 hinj141_87 hcardT141_87
      (fun i => conj_mem_of_fixedPoints _ _ (T141_87 i) (hfix141_87 i) _)
      ⟨141, by decide⟩ ⟨87, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨87, by decide⟩ 19 hp) Q2.T141_87_2 Q2.hfix141_87_2 Q2.hinj141_87_2
      Q2.hcardT141_87_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_87_2 i) (Q2.hfix141_87_2 i) _)
      colCert_141_87_19.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_87_20 (hp : 20 < (Q2.transData.getD 87 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨87, by decide⟩ : Fin 148)) (colE2 ⟨87, by decide⟩ 20 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨87, by decide⟩ : Fin 148))
        (colE1 ⟨87, by decide⟩ 20 (transLenTr ⟨87, by decide⟩ 20 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨87, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨87, by decide⟩ 20 (transLenTr ⟨87, by decide⟩ 20 hp)) T141_87
      hfix141_87 hinj141_87 hcardT141_87
      (fun i => conj_mem_of_fixedPoints _ _ (T141_87 i) (hfix141_87 i) _)
      ⟨141, by decide⟩ ⟨87, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨87, by decide⟩ 20 hp) Q2.T141_87_2 Q2.hfix141_87_2 Q2.hinj141_87_2
      Q2.hcardT141_87_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_87_2 i) (Q2.hfix141_87_2 i) _)
      colCert_141_87_20.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_87_21 (hp : 21 < (Q2.transData.getD 87 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨87, by decide⟩ : Fin 148)) (colE2 ⟨87, by decide⟩ 21 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨87, by decide⟩ : Fin 148))
        (colE1 ⟨87, by decide⟩ 21 (transLenTr ⟨87, by decide⟩ 21 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨87, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨87, by decide⟩ 21 (transLenTr ⟨87, by decide⟩ 21 hp)) T141_87
      hfix141_87 hinj141_87 hcardT141_87
      (fun i => conj_mem_of_fixedPoints _ _ (T141_87 i) (hfix141_87 i) _)
      ⟨141, by decide⟩ ⟨87, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨87, by decide⟩ 21 hp) Q2.T141_87_2 Q2.hfix141_87_2 Q2.hinj141_87_2
      Q2.hcardT141_87_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_87_2 i) (Q2.hfix141_87_2 i) _)
      colCert_141_87_21.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_87_22 (hp : 22 < (Q2.transData.getD 87 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨87, by decide⟩ : Fin 148)) (colE2 ⟨87, by decide⟩ 22 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨87, by decide⟩ : Fin 148))
        (colE1 ⟨87, by decide⟩ 22 (transLenTr ⟨87, by decide⟩ 22 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨87, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨87, by decide⟩ 22 (transLenTr ⟨87, by decide⟩ 22 hp)) T141_87
      hfix141_87 hinj141_87 hcardT141_87
      (fun i => conj_mem_of_fixedPoints _ _ (T141_87 i) (hfix141_87 i) _)
      ⟨141, by decide⟩ ⟨87, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨87, by decide⟩ 22 hp) Q2.T141_87_2 Q2.hfix141_87_2 Q2.hinj141_87_2
      Q2.hcardT141_87_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_87_2 i) (Q2.hfix141_87_2 i) _)
      colCert_141_87_22.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_87_23 (hp : 23 < (Q2.transData.getD 87 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨87, by decide⟩ : Fin 148)) (colE2 ⟨87, by decide⟩ 23 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨87, by decide⟩ : Fin 148))
        (colE1 ⟨87, by decide⟩ 23 (transLenTr ⟨87, by decide⟩ 23 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨87, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨87, by decide⟩ 23 (transLenTr ⟨87, by decide⟩ 23 hp)) T141_87
      hfix141_87 hinj141_87 hcardT141_87
      (fun i => conj_mem_of_fixedPoints _ _ (T141_87 i) (hfix141_87 i) _)
      ⟨141, by decide⟩ ⟨87, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨87, by decide⟩ 23 hp) Q2.T141_87_2 Q2.hfix141_87_2 Q2.hinj141_87_2
      Q2.hcardT141_87_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_87_2 i) (Q2.hfix141_87_2 i) _)
      colCert_141_87_23.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_87_24 (hp : 24 < (Q2.transData.getD 87 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨87, by decide⟩ : Fin 148)) (colE2 ⟨87, by decide⟩ 24 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨87, by decide⟩ : Fin 148))
        (colE1 ⟨87, by decide⟩ 24 (transLenTr ⟨87, by decide⟩ 24 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨87, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨87, by decide⟩ 24 (transLenTr ⟨87, by decide⟩ 24 hp)) T141_87
      hfix141_87 hinj141_87 hcardT141_87
      (fun i => conj_mem_of_fixedPoints _ _ (T141_87 i) (hfix141_87 i) _)
      ⟨141, by decide⟩ ⟨87, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨87, by decide⟩ 24 hp) Q2.T141_87_2 Q2.hfix141_87_2 Q2.hinj141_87_2
      Q2.hcardT141_87_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_87_2 i) (Q2.hfix141_87_2 i) _)
      colCert_141_87_24.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_88_0 (hp : 0 < (Q2.transData.getD 88 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨88, by decide⟩ : Fin 148)) (colE2 ⟨88, by decide⟩ 0 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨88, by decide⟩ : Fin 148))
        (colE1 ⟨88, by decide⟩ 0 (transLenTr ⟨88, by decide⟩ 0 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨88, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨88, by decide⟩ 0 (transLenTr ⟨88, by decide⟩ 0 hp)) T141_88
      hfix141_88 hinj141_88 hcardT141_88
      (fun i => conj_mem_of_fixedPoints _ _ (T141_88 i) (hfix141_88 i) _)
      ⟨141, by decide⟩ ⟨88, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨88, by decide⟩ 0 hp) Q2.T141_88_2 Q2.hfix141_88_2 Q2.hinj141_88_2
      Q2.hcardT141_88_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_88_2 i) (Q2.hfix141_88_2 i) _)
      colCert_141_88_0.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_88_1 (hp : 1 < (Q2.transData.getD 88 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨88, by decide⟩ : Fin 148)) (colE2 ⟨88, by decide⟩ 1 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨88, by decide⟩ : Fin 148))
        (colE1 ⟨88, by decide⟩ 1 (transLenTr ⟨88, by decide⟩ 1 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨88, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨88, by decide⟩ 1 (transLenTr ⟨88, by decide⟩ 1 hp)) T141_88
      hfix141_88 hinj141_88 hcardT141_88
      (fun i => conj_mem_of_fixedPoints _ _ (T141_88 i) (hfix141_88 i) _)
      ⟨141, by decide⟩ ⟨88, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨88, by decide⟩ 1 hp) Q2.T141_88_2 Q2.hfix141_88_2 Q2.hinj141_88_2
      Q2.hcardT141_88_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_88_2 i) (Q2.hfix141_88_2 i) _)
      colCert_141_88_1.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_88_2 (hp : 2 < (Q2.transData.getD 88 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨88, by decide⟩ : Fin 148)) (colE2 ⟨88, by decide⟩ 2 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨88, by decide⟩ : Fin 148))
        (colE1 ⟨88, by decide⟩ 2 (transLenTr ⟨88, by decide⟩ 2 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨88, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨88, by decide⟩ 2 (transLenTr ⟨88, by decide⟩ 2 hp)) T141_88
      hfix141_88 hinj141_88 hcardT141_88
      (fun i => conj_mem_of_fixedPoints _ _ (T141_88 i) (hfix141_88 i) _)
      ⟨141, by decide⟩ ⟨88, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨88, by decide⟩ 2 hp) Q2.T141_88_2 Q2.hfix141_88_2 Q2.hinj141_88_2
      Q2.hcardT141_88_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_88_2 i) (Q2.hfix141_88_2 i) _)
      colCert_141_88_2.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_88_3 (hp : 3 < (Q2.transData.getD 88 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨88, by decide⟩ : Fin 148)) (colE2 ⟨88, by decide⟩ 3 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨88, by decide⟩ : Fin 148))
        (colE1 ⟨88, by decide⟩ 3 (transLenTr ⟨88, by decide⟩ 3 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨88, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨88, by decide⟩ 3 (transLenTr ⟨88, by decide⟩ 3 hp)) T141_88
      hfix141_88 hinj141_88 hcardT141_88
      (fun i => conj_mem_of_fixedPoints _ _ (T141_88 i) (hfix141_88 i) _)
      ⟨141, by decide⟩ ⟨88, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨88, by decide⟩ 3 hp) Q2.T141_88_2 Q2.hfix141_88_2 Q2.hinj141_88_2
      Q2.hcardT141_88_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_88_2 i) (Q2.hfix141_88_2 i) _)
      colCert_141_88_3.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_88_4 (hp : 4 < (Q2.transData.getD 88 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨88, by decide⟩ : Fin 148)) (colE2 ⟨88, by decide⟩ 4 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨88, by decide⟩ : Fin 148))
        (colE1 ⟨88, by decide⟩ 4 (transLenTr ⟨88, by decide⟩ 4 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨88, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨88, by decide⟩ 4 (transLenTr ⟨88, by decide⟩ 4 hp)) T141_88
      hfix141_88 hinj141_88 hcardT141_88
      (fun i => conj_mem_of_fixedPoints _ _ (T141_88 i) (hfix141_88 i) _)
      ⟨141, by decide⟩ ⟨88, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨88, by decide⟩ 4 hp) Q2.T141_88_2 Q2.hfix141_88_2 Q2.hinj141_88_2
      Q2.hcardT141_88_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_88_2 i) (Q2.hfix141_88_2 i) _)
      colCert_141_88_4.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_88_5 (hp : 5 < (Q2.transData.getD 88 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨88, by decide⟩ : Fin 148)) (colE2 ⟨88, by decide⟩ 5 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨88, by decide⟩ : Fin 148))
        (colE1 ⟨88, by decide⟩ 5 (transLenTr ⟨88, by decide⟩ 5 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨88, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨88, by decide⟩ 5 (transLenTr ⟨88, by decide⟩ 5 hp)) T141_88
      hfix141_88 hinj141_88 hcardT141_88
      (fun i => conj_mem_of_fixedPoints _ _ (T141_88 i) (hfix141_88 i) _)
      ⟨141, by decide⟩ ⟨88, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨88, by decide⟩ 5 hp) Q2.T141_88_2 Q2.hfix141_88_2 Q2.hinj141_88_2
      Q2.hcardT141_88_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_88_2 i) (Q2.hfix141_88_2 i) _)
      colCert_141_88_5.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_88_6 (hp : 6 < (Q2.transData.getD 88 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨88, by decide⟩ : Fin 148)) (colE2 ⟨88, by decide⟩ 6 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨88, by decide⟩ : Fin 148))
        (colE1 ⟨88, by decide⟩ 6 (transLenTr ⟨88, by decide⟩ 6 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨88, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨88, by decide⟩ 6 (transLenTr ⟨88, by decide⟩ 6 hp)) T141_88
      hfix141_88 hinj141_88 hcardT141_88
      (fun i => conj_mem_of_fixedPoints _ _ (T141_88 i) (hfix141_88 i) _)
      ⟨141, by decide⟩ ⟨88, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨88, by decide⟩ 6 hp) Q2.T141_88_2 Q2.hfix141_88_2 Q2.hinj141_88_2
      Q2.hcardT141_88_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_88_2 i) (Q2.hfix141_88_2 i) _)
      colCert_141_88_6.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_88_7 (hp : 7 < (Q2.transData.getD 88 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨88, by decide⟩ : Fin 148)) (colE2 ⟨88, by decide⟩ 7 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨88, by decide⟩ : Fin 148))
        (colE1 ⟨88, by decide⟩ 7 (transLenTr ⟨88, by decide⟩ 7 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨88, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨88, by decide⟩ 7 (transLenTr ⟨88, by decide⟩ 7 hp)) T141_88
      hfix141_88 hinj141_88 hcardT141_88
      (fun i => conj_mem_of_fixedPoints _ _ (T141_88 i) (hfix141_88 i) _)
      ⟨141, by decide⟩ ⟨88, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨88, by decide⟩ 7 hp) Q2.T141_88_2 Q2.hfix141_88_2 Q2.hinj141_88_2
      Q2.hcardT141_88_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_88_2 i) (Q2.hfix141_88_2 i) _)
      colCert_141_88_7.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_88_8 (hp : 8 < (Q2.transData.getD 88 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨88, by decide⟩ : Fin 148)) (colE2 ⟨88, by decide⟩ 8 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨88, by decide⟩ : Fin 148))
        (colE1 ⟨88, by decide⟩ 8 (transLenTr ⟨88, by decide⟩ 8 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨88, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨88, by decide⟩ 8 (transLenTr ⟨88, by decide⟩ 8 hp)) T141_88
      hfix141_88 hinj141_88 hcardT141_88
      (fun i => conj_mem_of_fixedPoints _ _ (T141_88 i) (hfix141_88 i) _)
      ⟨141, by decide⟩ ⟨88, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨88, by decide⟩ 8 hp) Q2.T141_88_2 Q2.hfix141_88_2 Q2.hinj141_88_2
      Q2.hcardT141_88_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_88_2 i) (Q2.hfix141_88_2 i) _)
      colCert_141_88_8.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_88_9 (hp : 9 < (Q2.transData.getD 88 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨88, by decide⟩ : Fin 148)) (colE2 ⟨88, by decide⟩ 9 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨88, by decide⟩ : Fin 148))
        (colE1 ⟨88, by decide⟩ 9 (transLenTr ⟨88, by decide⟩ 9 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨88, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨88, by decide⟩ 9 (transLenTr ⟨88, by decide⟩ 9 hp)) T141_88
      hfix141_88 hinj141_88 hcardT141_88
      (fun i => conj_mem_of_fixedPoints _ _ (T141_88 i) (hfix141_88 i) _)
      ⟨141, by decide⟩ ⟨88, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨88, by decide⟩ 9 hp) Q2.T141_88_2 Q2.hfix141_88_2 Q2.hinj141_88_2
      Q2.hcardT141_88_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_88_2 i) (Q2.hfix141_88_2 i) _)
      colCert_141_88_9.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_88_10 (hp : 10 < (Q2.transData.getD 88 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨88, by decide⟩ : Fin 148)) (colE2 ⟨88, by decide⟩ 10 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨88, by decide⟩ : Fin 148))
        (colE1 ⟨88, by decide⟩ 10 (transLenTr ⟨88, by decide⟩ 10 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨88, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨88, by decide⟩ 10 (transLenTr ⟨88, by decide⟩ 10 hp)) T141_88
      hfix141_88 hinj141_88 hcardT141_88
      (fun i => conj_mem_of_fixedPoints _ _ (T141_88 i) (hfix141_88 i) _)
      ⟨141, by decide⟩ ⟨88, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨88, by decide⟩ 10 hp) Q2.T141_88_2 Q2.hfix141_88_2 Q2.hinj141_88_2
      Q2.hcardT141_88_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_88_2 i) (Q2.hfix141_88_2 i) _)
      colCert_141_88_10.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_88_11 (hp : 11 < (Q2.transData.getD 88 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨88, by decide⟩ : Fin 148)) (colE2 ⟨88, by decide⟩ 11 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨88, by decide⟩ : Fin 148))
        (colE1 ⟨88, by decide⟩ 11 (transLenTr ⟨88, by decide⟩ 11 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨88, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨88, by decide⟩ 11 (transLenTr ⟨88, by decide⟩ 11 hp)) T141_88
      hfix141_88 hinj141_88 hcardT141_88
      (fun i => conj_mem_of_fixedPoints _ _ (T141_88 i) (hfix141_88 i) _)
      ⟨141, by decide⟩ ⟨88, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨88, by decide⟩ 11 hp) Q2.T141_88_2 Q2.hfix141_88_2 Q2.hinj141_88_2
      Q2.hcardT141_88_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_88_2 i) (Q2.hfix141_88_2 i) _)
      colCert_141_88_11.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_88_12 (hp : 12 < (Q2.transData.getD 88 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨88, by decide⟩ : Fin 148)) (colE2 ⟨88, by decide⟩ 12 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨88, by decide⟩ : Fin 148))
        (colE1 ⟨88, by decide⟩ 12 (transLenTr ⟨88, by decide⟩ 12 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨88, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨88, by decide⟩ 12 (transLenTr ⟨88, by decide⟩ 12 hp)) T141_88
      hfix141_88 hinj141_88 hcardT141_88
      (fun i => conj_mem_of_fixedPoints _ _ (T141_88 i) (hfix141_88 i) _)
      ⟨141, by decide⟩ ⟨88, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨88, by decide⟩ 12 hp) Q2.T141_88_2 Q2.hfix141_88_2 Q2.hinj141_88_2
      Q2.hcardT141_88_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_88_2 i) (Q2.hfix141_88_2 i) _)
      colCert_141_88_12.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_88_13 (hp : 13 < (Q2.transData.getD 88 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨88, by decide⟩ : Fin 148)) (colE2 ⟨88, by decide⟩ 13 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨88, by decide⟩ : Fin 148))
        (colE1 ⟨88, by decide⟩ 13 (transLenTr ⟨88, by decide⟩ 13 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨88, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨88, by decide⟩ 13 (transLenTr ⟨88, by decide⟩ 13 hp)) T141_88
      hfix141_88 hinj141_88 hcardT141_88
      (fun i => conj_mem_of_fixedPoints _ _ (T141_88 i) (hfix141_88 i) _)
      ⟨141, by decide⟩ ⟨88, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨88, by decide⟩ 13 hp) Q2.T141_88_2 Q2.hfix141_88_2 Q2.hinj141_88_2
      Q2.hcardT141_88_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_88_2 i) (Q2.hfix141_88_2 i) _)
      colCert_141_88_13.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_88_14 (hp : 14 < (Q2.transData.getD 88 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨88, by decide⟩ : Fin 148)) (colE2 ⟨88, by decide⟩ 14 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨88, by decide⟩ : Fin 148))
        (colE1 ⟨88, by decide⟩ 14 (transLenTr ⟨88, by decide⟩ 14 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨88, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨88, by decide⟩ 14 (transLenTr ⟨88, by decide⟩ 14 hp)) T141_88
      hfix141_88 hinj141_88 hcardT141_88
      (fun i => conj_mem_of_fixedPoints _ _ (T141_88 i) (hfix141_88 i) _)
      ⟨141, by decide⟩ ⟨88, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨88, by decide⟩ 14 hp) Q2.T141_88_2 Q2.hfix141_88_2 Q2.hinj141_88_2
      Q2.hcardT141_88_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_88_2 i) (Q2.hfix141_88_2 i) _)
      colCert_141_88_14.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_88_15 (hp : 15 < (Q2.transData.getD 88 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨88, by decide⟩ : Fin 148)) (colE2 ⟨88, by decide⟩ 15 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨88, by decide⟩ : Fin 148))
        (colE1 ⟨88, by decide⟩ 15 (transLenTr ⟨88, by decide⟩ 15 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨88, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨88, by decide⟩ 15 (transLenTr ⟨88, by decide⟩ 15 hp)) T141_88
      hfix141_88 hinj141_88 hcardT141_88
      (fun i => conj_mem_of_fixedPoints _ _ (T141_88 i) (hfix141_88 i) _)
      ⟨141, by decide⟩ ⟨88, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨88, by decide⟩ 15 hp) Q2.T141_88_2 Q2.hfix141_88_2 Q2.hinj141_88_2
      Q2.hcardT141_88_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_88_2 i) (Q2.hfix141_88_2 i) _)
      colCert_141_88_15.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_88_16 (hp : 16 < (Q2.transData.getD 88 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨88, by decide⟩ : Fin 148)) (colE2 ⟨88, by decide⟩ 16 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨88, by decide⟩ : Fin 148))
        (colE1 ⟨88, by decide⟩ 16 (transLenTr ⟨88, by decide⟩ 16 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨88, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨88, by decide⟩ 16 (transLenTr ⟨88, by decide⟩ 16 hp)) T141_88
      hfix141_88 hinj141_88 hcardT141_88
      (fun i => conj_mem_of_fixedPoints _ _ (T141_88 i) (hfix141_88 i) _)
      ⟨141, by decide⟩ ⟨88, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨88, by decide⟩ 16 hp) Q2.T141_88_2 Q2.hfix141_88_2 Q2.hinj141_88_2
      Q2.hcardT141_88_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_88_2 i) (Q2.hfix141_88_2 i) _)
      colCert_141_88_16.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_88_17 (hp : 17 < (Q2.transData.getD 88 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨88, by decide⟩ : Fin 148)) (colE2 ⟨88, by decide⟩ 17 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨88, by decide⟩ : Fin 148))
        (colE1 ⟨88, by decide⟩ 17 (transLenTr ⟨88, by decide⟩ 17 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨88, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨88, by decide⟩ 17 (transLenTr ⟨88, by decide⟩ 17 hp)) T141_88
      hfix141_88 hinj141_88 hcardT141_88
      (fun i => conj_mem_of_fixedPoints _ _ (T141_88 i) (hfix141_88 i) _)
      ⟨141, by decide⟩ ⟨88, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨88, by decide⟩ 17 hp) Q2.T141_88_2 Q2.hfix141_88_2 Q2.hinj141_88_2
      Q2.hcardT141_88_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_88_2 i) (Q2.hfix141_88_2 i) _)
      colCert_141_88_17.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_88_18 (hp : 18 < (Q2.transData.getD 88 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨88, by decide⟩ : Fin 148)) (colE2 ⟨88, by decide⟩ 18 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨88, by decide⟩ : Fin 148))
        (colE1 ⟨88, by decide⟩ 18 (transLenTr ⟨88, by decide⟩ 18 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨88, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨88, by decide⟩ 18 (transLenTr ⟨88, by decide⟩ 18 hp)) T141_88
      hfix141_88 hinj141_88 hcardT141_88
      (fun i => conj_mem_of_fixedPoints _ _ (T141_88 i) (hfix141_88 i) _)
      ⟨141, by decide⟩ ⟨88, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨88, by decide⟩ 18 hp) Q2.T141_88_2 Q2.hfix141_88_2 Q2.hinj141_88_2
      Q2.hcardT141_88_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_88_2 i) (Q2.hfix141_88_2 i) _)
      colCert_141_88_18.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_88_19 (hp : 19 < (Q2.transData.getD 88 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨88, by decide⟩ : Fin 148)) (colE2 ⟨88, by decide⟩ 19 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨88, by decide⟩ : Fin 148))
        (colE1 ⟨88, by decide⟩ 19 (transLenTr ⟨88, by decide⟩ 19 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨88, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨88, by decide⟩ 19 (transLenTr ⟨88, by decide⟩ 19 hp)) T141_88
      hfix141_88 hinj141_88 hcardT141_88
      (fun i => conj_mem_of_fixedPoints _ _ (T141_88 i) (hfix141_88 i) _)
      ⟨141, by decide⟩ ⟨88, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨88, by decide⟩ 19 hp) Q2.T141_88_2 Q2.hfix141_88_2 Q2.hinj141_88_2
      Q2.hcardT141_88_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_88_2 i) (Q2.hfix141_88_2 i) _)
      colCert_141_88_19.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_88_20 (hp : 20 < (Q2.transData.getD 88 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨88, by decide⟩ : Fin 148)) (colE2 ⟨88, by decide⟩ 20 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨88, by decide⟩ : Fin 148))
        (colE1 ⟨88, by decide⟩ 20 (transLenTr ⟨88, by decide⟩ 20 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨88, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨88, by decide⟩ 20 (transLenTr ⟨88, by decide⟩ 20 hp)) T141_88
      hfix141_88 hinj141_88 hcardT141_88
      (fun i => conj_mem_of_fixedPoints _ _ (T141_88 i) (hfix141_88 i) _)
      ⟨141, by decide⟩ ⟨88, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨88, by decide⟩ 20 hp) Q2.T141_88_2 Q2.hfix141_88_2 Q2.hinj141_88_2
      Q2.hcardT141_88_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_88_2 i) (Q2.hfix141_88_2 i) _)
      colCert_141_88_20.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_88_21 (hp : 21 < (Q2.transData.getD 88 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨88, by decide⟩ : Fin 148)) (colE2 ⟨88, by decide⟩ 21 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨88, by decide⟩ : Fin 148))
        (colE1 ⟨88, by decide⟩ 21 (transLenTr ⟨88, by decide⟩ 21 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨88, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨88, by decide⟩ 21 (transLenTr ⟨88, by decide⟩ 21 hp)) T141_88
      hfix141_88 hinj141_88 hcardT141_88
      (fun i => conj_mem_of_fixedPoints _ _ (T141_88 i) (hfix141_88 i) _)
      ⟨141, by decide⟩ ⟨88, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨88, by decide⟩ 21 hp) Q2.T141_88_2 Q2.hfix141_88_2 Q2.hinj141_88_2
      Q2.hcardT141_88_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_88_2 i) (Q2.hfix141_88_2 i) _)
      colCert_141_88_21.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_88_22 (hp : 22 < (Q2.transData.getD 88 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨88, by decide⟩ : Fin 148)) (colE2 ⟨88, by decide⟩ 22 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨88, by decide⟩ : Fin 148))
        (colE1 ⟨88, by decide⟩ 22 (transLenTr ⟨88, by decide⟩ 22 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨88, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨88, by decide⟩ 22 (transLenTr ⟨88, by decide⟩ 22 hp)) T141_88
      hfix141_88 hinj141_88 hcardT141_88
      (fun i => conj_mem_of_fixedPoints _ _ (T141_88 i) (hfix141_88 i) _)
      ⟨141, by decide⟩ ⟨88, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨88, by decide⟩ 22 hp) Q2.T141_88_2 Q2.hfix141_88_2 Q2.hinj141_88_2
      Q2.hcardT141_88_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_88_2 i) (Q2.hfix141_88_2 i) _)
      colCert_141_88_22.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_88_23 (hp : 23 < (Q2.transData.getD 88 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨88, by decide⟩ : Fin 148)) (colE2 ⟨88, by decide⟩ 23 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨88, by decide⟩ : Fin 148))
        (colE1 ⟨88, by decide⟩ 23 (transLenTr ⟨88, by decide⟩ 23 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨88, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨88, by decide⟩ 23 (transLenTr ⟨88, by decide⟩ 23 hp)) T141_88
      hfix141_88 hinj141_88 hcardT141_88
      (fun i => conj_mem_of_fixedPoints _ _ (T141_88 i) (hfix141_88 i) _)
      ⟨141, by decide⟩ ⟨88, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨88, by decide⟩ 23 hp) Q2.T141_88_2 Q2.hfix141_88_2 Q2.hinj141_88_2
      Q2.hcardT141_88_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_88_2 i) (Q2.hfix141_88_2 i) _)
      colCert_141_88_23.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_88_24 (hp : 24 < (Q2.transData.getD 88 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨88, by decide⟩ : Fin 148)) (colE2 ⟨88, by decide⟩ 24 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨88, by decide⟩ : Fin 148))
        (colE1 ⟨88, by decide⟩ 24 (transLenTr ⟨88, by decide⟩ 24 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨88, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨88, by decide⟩ 24 (transLenTr ⟨88, by decide⟩ 24 hp)) T141_88
      hfix141_88 hinj141_88 hcardT141_88
      (fun i => conj_mem_of_fixedPoints _ _ (T141_88 i) (hfix141_88 i) _)
      ⟨141, by decide⟩ ⟨88, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨88, by decide⟩ 24 hp) Q2.T141_88_2 Q2.hfix141_88_2 Q2.hinj141_88_2
      Q2.hcardT141_88_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_88_2 i) (Q2.hfix141_88_2 i) _)
      colCert_141_88_24.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_89_0 (hp : 0 < (Q2.transData.getD 89 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨89, by decide⟩ : Fin 148)) (colE2 ⟨89, by decide⟩ 0 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨89, by decide⟩ : Fin 148))
        (colE1 ⟨89, by decide⟩ 0 (transLenTr ⟨89, by decide⟩ 0 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨89, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨89, by decide⟩ 0 (transLenTr ⟨89, by decide⟩ 0 hp)) T141_89
      hfix141_89 hinj141_89 hcardT141_89
      (fun i => conj_mem_of_fixedPoints _ _ (T141_89 i) (hfix141_89 i) _)
      ⟨141, by decide⟩ ⟨89, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨89, by decide⟩ 0 hp) Q2.T141_89_2 Q2.hfix141_89_2 Q2.hinj141_89_2
      Q2.hcardT141_89_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_89_2 i) (Q2.hfix141_89_2 i) _)
      colCert_141_89_0.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_89_1 (hp : 1 < (Q2.transData.getD 89 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨89, by decide⟩ : Fin 148)) (colE2 ⟨89, by decide⟩ 1 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨89, by decide⟩ : Fin 148))
        (colE1 ⟨89, by decide⟩ 1 (transLenTr ⟨89, by decide⟩ 1 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨89, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨89, by decide⟩ 1 (transLenTr ⟨89, by decide⟩ 1 hp)) T141_89
      hfix141_89 hinj141_89 hcardT141_89
      (fun i => conj_mem_of_fixedPoints _ _ (T141_89 i) (hfix141_89 i) _)
      ⟨141, by decide⟩ ⟨89, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨89, by decide⟩ 1 hp) Q2.T141_89_2 Q2.hfix141_89_2 Q2.hinj141_89_2
      Q2.hcardT141_89_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_89_2 i) (Q2.hfix141_89_2 i) _)
      colCert_141_89_1.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_89_2 (hp : 2 < (Q2.transData.getD 89 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨89, by decide⟩ : Fin 148)) (colE2 ⟨89, by decide⟩ 2 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨89, by decide⟩ : Fin 148))
        (colE1 ⟨89, by decide⟩ 2 (transLenTr ⟨89, by decide⟩ 2 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨89, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨89, by decide⟩ 2 (transLenTr ⟨89, by decide⟩ 2 hp)) T141_89
      hfix141_89 hinj141_89 hcardT141_89
      (fun i => conj_mem_of_fixedPoints _ _ (T141_89 i) (hfix141_89 i) _)
      ⟨141, by decide⟩ ⟨89, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨89, by decide⟩ 2 hp) Q2.T141_89_2 Q2.hfix141_89_2 Q2.hinj141_89_2
      Q2.hcardT141_89_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_89_2 i) (Q2.hfix141_89_2 i) _)
      colCert_141_89_2.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_89_3 (hp : 3 < (Q2.transData.getD 89 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨89, by decide⟩ : Fin 148)) (colE2 ⟨89, by decide⟩ 3 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨89, by decide⟩ : Fin 148))
        (colE1 ⟨89, by decide⟩ 3 (transLenTr ⟨89, by decide⟩ 3 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨89, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨89, by decide⟩ 3 (transLenTr ⟨89, by decide⟩ 3 hp)) T141_89
      hfix141_89 hinj141_89 hcardT141_89
      (fun i => conj_mem_of_fixedPoints _ _ (T141_89 i) (hfix141_89 i) _)
      ⟨141, by decide⟩ ⟨89, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨89, by decide⟩ 3 hp) Q2.T141_89_2 Q2.hfix141_89_2 Q2.hinj141_89_2
      Q2.hcardT141_89_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_89_2 i) (Q2.hfix141_89_2 i) _)
      colCert_141_89_3.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_89_4 (hp : 4 < (Q2.transData.getD 89 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨89, by decide⟩ : Fin 148)) (colE2 ⟨89, by decide⟩ 4 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨89, by decide⟩ : Fin 148))
        (colE1 ⟨89, by decide⟩ 4 (transLenTr ⟨89, by decide⟩ 4 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨89, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨89, by decide⟩ 4 (transLenTr ⟨89, by decide⟩ 4 hp)) T141_89
      hfix141_89 hinj141_89 hcardT141_89
      (fun i => conj_mem_of_fixedPoints _ _ (T141_89 i) (hfix141_89 i) _)
      ⟨141, by decide⟩ ⟨89, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨89, by decide⟩ 4 hp) Q2.T141_89_2 Q2.hfix141_89_2 Q2.hinj141_89_2
      Q2.hcardT141_89_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_89_2 i) (Q2.hfix141_89_2 i) _)
      colCert_141_89_4.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_89_5 (hp : 5 < (Q2.transData.getD 89 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨89, by decide⟩ : Fin 148)) (colE2 ⟨89, by decide⟩ 5 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨89, by decide⟩ : Fin 148))
        (colE1 ⟨89, by decide⟩ 5 (transLenTr ⟨89, by decide⟩ 5 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨89, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨89, by decide⟩ 5 (transLenTr ⟨89, by decide⟩ 5 hp)) T141_89
      hfix141_89 hinj141_89 hcardT141_89
      (fun i => conj_mem_of_fixedPoints _ _ (T141_89 i) (hfix141_89 i) _)
      ⟨141, by decide⟩ ⟨89, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨89, by decide⟩ 5 hp) Q2.T141_89_2 Q2.hfix141_89_2 Q2.hinj141_89_2
      Q2.hcardT141_89_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_89_2 i) (Q2.hfix141_89_2 i) _)
      colCert_141_89_5.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_89_6 (hp : 6 < (Q2.transData.getD 89 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨89, by decide⟩ : Fin 148)) (colE2 ⟨89, by decide⟩ 6 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨89, by decide⟩ : Fin 148))
        (colE1 ⟨89, by decide⟩ 6 (transLenTr ⟨89, by decide⟩ 6 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨89, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨89, by decide⟩ 6 (transLenTr ⟨89, by decide⟩ 6 hp)) T141_89
      hfix141_89 hinj141_89 hcardT141_89
      (fun i => conj_mem_of_fixedPoints _ _ (T141_89 i) (hfix141_89 i) _)
      ⟨141, by decide⟩ ⟨89, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨89, by decide⟩ 6 hp) Q2.T141_89_2 Q2.hfix141_89_2 Q2.hinj141_89_2
      Q2.hcardT141_89_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_89_2 i) (Q2.hfix141_89_2 i) _)
      colCert_141_89_6.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_89_7 (hp : 7 < (Q2.transData.getD 89 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨89, by decide⟩ : Fin 148)) (colE2 ⟨89, by decide⟩ 7 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨89, by decide⟩ : Fin 148))
        (colE1 ⟨89, by decide⟩ 7 (transLenTr ⟨89, by decide⟩ 7 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨89, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨89, by decide⟩ 7 (transLenTr ⟨89, by decide⟩ 7 hp)) T141_89
      hfix141_89 hinj141_89 hcardT141_89
      (fun i => conj_mem_of_fixedPoints _ _ (T141_89 i) (hfix141_89 i) _)
      ⟨141, by decide⟩ ⟨89, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨89, by decide⟩ 7 hp) Q2.T141_89_2 Q2.hfix141_89_2 Q2.hinj141_89_2
      Q2.hcardT141_89_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_89_2 i) (Q2.hfix141_89_2 i) _)
      colCert_141_89_7.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_89_8 (hp : 8 < (Q2.transData.getD 89 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨89, by decide⟩ : Fin 148)) (colE2 ⟨89, by decide⟩ 8 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨89, by decide⟩ : Fin 148))
        (colE1 ⟨89, by decide⟩ 8 (transLenTr ⟨89, by decide⟩ 8 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨89, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨89, by decide⟩ 8 (transLenTr ⟨89, by decide⟩ 8 hp)) T141_89
      hfix141_89 hinj141_89 hcardT141_89
      (fun i => conj_mem_of_fixedPoints _ _ (T141_89 i) (hfix141_89 i) _)
      ⟨141, by decide⟩ ⟨89, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨89, by decide⟩ 8 hp) Q2.T141_89_2 Q2.hfix141_89_2 Q2.hinj141_89_2
      Q2.hcardT141_89_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_89_2 i) (Q2.hfix141_89_2 i) _)
      colCert_141_89_8.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_89_9 (hp : 9 < (Q2.transData.getD 89 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨89, by decide⟩ : Fin 148)) (colE2 ⟨89, by decide⟩ 9 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨89, by decide⟩ : Fin 148))
        (colE1 ⟨89, by decide⟩ 9 (transLenTr ⟨89, by decide⟩ 9 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨89, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨89, by decide⟩ 9 (transLenTr ⟨89, by decide⟩ 9 hp)) T141_89
      hfix141_89 hinj141_89 hcardT141_89
      (fun i => conj_mem_of_fixedPoints _ _ (T141_89 i) (hfix141_89 i) _)
      ⟨141, by decide⟩ ⟨89, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨89, by decide⟩ 9 hp) Q2.T141_89_2 Q2.hfix141_89_2 Q2.hinj141_89_2
      Q2.hcardT141_89_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_89_2 i) (Q2.hfix141_89_2 i) _)
      colCert_141_89_9.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_89_10 (hp : 10 < (Q2.transData.getD 89 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨89, by decide⟩ : Fin 148)) (colE2 ⟨89, by decide⟩ 10 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨89, by decide⟩ : Fin 148))
        (colE1 ⟨89, by decide⟩ 10 (transLenTr ⟨89, by decide⟩ 10 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨89, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨89, by decide⟩ 10 (transLenTr ⟨89, by decide⟩ 10 hp)) T141_89
      hfix141_89 hinj141_89 hcardT141_89
      (fun i => conj_mem_of_fixedPoints _ _ (T141_89 i) (hfix141_89 i) _)
      ⟨141, by decide⟩ ⟨89, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨89, by decide⟩ 10 hp) Q2.T141_89_2 Q2.hfix141_89_2 Q2.hinj141_89_2
      Q2.hcardT141_89_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_89_2 i) (Q2.hfix141_89_2 i) _)
      colCert_141_89_10.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_89_11 (hp : 11 < (Q2.transData.getD 89 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨89, by decide⟩ : Fin 148)) (colE2 ⟨89, by decide⟩ 11 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨89, by decide⟩ : Fin 148))
        (colE1 ⟨89, by decide⟩ 11 (transLenTr ⟨89, by decide⟩ 11 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨89, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨89, by decide⟩ 11 (transLenTr ⟨89, by decide⟩ 11 hp)) T141_89
      hfix141_89 hinj141_89 hcardT141_89
      (fun i => conj_mem_of_fixedPoints _ _ (T141_89 i) (hfix141_89 i) _)
      ⟨141, by decide⟩ ⟨89, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨89, by decide⟩ 11 hp) Q2.T141_89_2 Q2.hfix141_89_2 Q2.hinj141_89_2
      Q2.hcardT141_89_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_89_2 i) (Q2.hfix141_89_2 i) _)
      colCert_141_89_11.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_89_12 (hp : 12 < (Q2.transData.getD 89 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨89, by decide⟩ : Fin 148)) (colE2 ⟨89, by decide⟩ 12 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨89, by decide⟩ : Fin 148))
        (colE1 ⟨89, by decide⟩ 12 (transLenTr ⟨89, by decide⟩ 12 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨89, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨89, by decide⟩ 12 (transLenTr ⟨89, by decide⟩ 12 hp)) T141_89
      hfix141_89 hinj141_89 hcardT141_89
      (fun i => conj_mem_of_fixedPoints _ _ (T141_89 i) (hfix141_89 i) _)
      ⟨141, by decide⟩ ⟨89, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨89, by decide⟩ 12 hp) Q2.T141_89_2 Q2.hfix141_89_2 Q2.hinj141_89_2
      Q2.hcardT141_89_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_89_2 i) (Q2.hfix141_89_2 i) _)
      colCert_141_89_12.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_89_13 (hp : 13 < (Q2.transData.getD 89 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨89, by decide⟩ : Fin 148)) (colE2 ⟨89, by decide⟩ 13 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨89, by decide⟩ : Fin 148))
        (colE1 ⟨89, by decide⟩ 13 (transLenTr ⟨89, by decide⟩ 13 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨89, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨89, by decide⟩ 13 (transLenTr ⟨89, by decide⟩ 13 hp)) T141_89
      hfix141_89 hinj141_89 hcardT141_89
      (fun i => conj_mem_of_fixedPoints _ _ (T141_89 i) (hfix141_89 i) _)
      ⟨141, by decide⟩ ⟨89, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨89, by decide⟩ 13 hp) Q2.T141_89_2 Q2.hfix141_89_2 Q2.hinj141_89_2
      Q2.hcardT141_89_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_89_2 i) (Q2.hfix141_89_2 i) _)
      colCert_141_89_13.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_89_14 (hp : 14 < (Q2.transData.getD 89 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨89, by decide⟩ : Fin 148)) (colE2 ⟨89, by decide⟩ 14 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨89, by decide⟩ : Fin 148))
        (colE1 ⟨89, by decide⟩ 14 (transLenTr ⟨89, by decide⟩ 14 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨89, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨89, by decide⟩ 14 (transLenTr ⟨89, by decide⟩ 14 hp)) T141_89
      hfix141_89 hinj141_89 hcardT141_89
      (fun i => conj_mem_of_fixedPoints _ _ (T141_89 i) (hfix141_89 i) _)
      ⟨141, by decide⟩ ⟨89, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨89, by decide⟩ 14 hp) Q2.T141_89_2 Q2.hfix141_89_2 Q2.hinj141_89_2
      Q2.hcardT141_89_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_89_2 i) (Q2.hfix141_89_2 i) _)
      colCert_141_89_14.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_89_15 (hp : 15 < (Q2.transData.getD 89 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨89, by decide⟩ : Fin 148)) (colE2 ⟨89, by decide⟩ 15 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨89, by decide⟩ : Fin 148))
        (colE1 ⟨89, by decide⟩ 15 (transLenTr ⟨89, by decide⟩ 15 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨89, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨89, by decide⟩ 15 (transLenTr ⟨89, by decide⟩ 15 hp)) T141_89
      hfix141_89 hinj141_89 hcardT141_89
      (fun i => conj_mem_of_fixedPoints _ _ (T141_89 i) (hfix141_89 i) _)
      ⟨141, by decide⟩ ⟨89, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨89, by decide⟩ 15 hp) Q2.T141_89_2 Q2.hfix141_89_2 Q2.hinj141_89_2
      Q2.hcardT141_89_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_89_2 i) (Q2.hfix141_89_2 i) _)
      colCert_141_89_15.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_89_16 (hp : 16 < (Q2.transData.getD 89 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨89, by decide⟩ : Fin 148)) (colE2 ⟨89, by decide⟩ 16 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨89, by decide⟩ : Fin 148))
        (colE1 ⟨89, by decide⟩ 16 (transLenTr ⟨89, by decide⟩ 16 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨89, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨89, by decide⟩ 16 (transLenTr ⟨89, by decide⟩ 16 hp)) T141_89
      hfix141_89 hinj141_89 hcardT141_89
      (fun i => conj_mem_of_fixedPoints _ _ (T141_89 i) (hfix141_89 i) _)
      ⟨141, by decide⟩ ⟨89, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨89, by decide⟩ 16 hp) Q2.T141_89_2 Q2.hfix141_89_2 Q2.hinj141_89_2
      Q2.hcardT141_89_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_89_2 i) (Q2.hfix141_89_2 i) _)
      colCert_141_89_16.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_89_17 (hp : 17 < (Q2.transData.getD 89 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨89, by decide⟩ : Fin 148)) (colE2 ⟨89, by decide⟩ 17 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨89, by decide⟩ : Fin 148))
        (colE1 ⟨89, by decide⟩ 17 (transLenTr ⟨89, by decide⟩ 17 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨89, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨89, by decide⟩ 17 (transLenTr ⟨89, by decide⟩ 17 hp)) T141_89
      hfix141_89 hinj141_89 hcardT141_89
      (fun i => conj_mem_of_fixedPoints _ _ (T141_89 i) (hfix141_89 i) _)
      ⟨141, by decide⟩ ⟨89, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨89, by decide⟩ 17 hp) Q2.T141_89_2 Q2.hfix141_89_2 Q2.hinj141_89_2
      Q2.hcardT141_89_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_89_2 i) (Q2.hfix141_89_2 i) _)
      colCert_141_89_17.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_89_18 (hp : 18 < (Q2.transData.getD 89 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨89, by decide⟩ : Fin 148)) (colE2 ⟨89, by decide⟩ 18 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨89, by decide⟩ : Fin 148))
        (colE1 ⟨89, by decide⟩ 18 (transLenTr ⟨89, by decide⟩ 18 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨89, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨89, by decide⟩ 18 (transLenTr ⟨89, by decide⟩ 18 hp)) T141_89
      hfix141_89 hinj141_89 hcardT141_89
      (fun i => conj_mem_of_fixedPoints _ _ (T141_89 i) (hfix141_89 i) _)
      ⟨141, by decide⟩ ⟨89, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨89, by decide⟩ 18 hp) Q2.T141_89_2 Q2.hfix141_89_2 Q2.hinj141_89_2
      Q2.hcardT141_89_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_89_2 i) (Q2.hfix141_89_2 i) _)
      colCert_141_89_18.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_89_19 (hp : 19 < (Q2.transData.getD 89 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨89, by decide⟩ : Fin 148)) (colE2 ⟨89, by decide⟩ 19 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨89, by decide⟩ : Fin 148))
        (colE1 ⟨89, by decide⟩ 19 (transLenTr ⟨89, by decide⟩ 19 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨89, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨89, by decide⟩ 19 (transLenTr ⟨89, by decide⟩ 19 hp)) T141_89
      hfix141_89 hinj141_89 hcardT141_89
      (fun i => conj_mem_of_fixedPoints _ _ (T141_89 i) (hfix141_89 i) _)
      ⟨141, by decide⟩ ⟨89, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨89, by decide⟩ 19 hp) Q2.T141_89_2 Q2.hfix141_89_2 Q2.hinj141_89_2
      Q2.hcardT141_89_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_89_2 i) (Q2.hfix141_89_2 i) _)
      colCert_141_89_19.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_89_20 (hp : 20 < (Q2.transData.getD 89 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨89, by decide⟩ : Fin 148)) (colE2 ⟨89, by decide⟩ 20 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨89, by decide⟩ : Fin 148))
        (colE1 ⟨89, by decide⟩ 20 (transLenTr ⟨89, by decide⟩ 20 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨89, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨89, by decide⟩ 20 (transLenTr ⟨89, by decide⟩ 20 hp)) T141_89
      hfix141_89 hinj141_89 hcardT141_89
      (fun i => conj_mem_of_fixedPoints _ _ (T141_89 i) (hfix141_89 i) _)
      ⟨141, by decide⟩ ⟨89, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨89, by decide⟩ 20 hp) Q2.T141_89_2 Q2.hfix141_89_2 Q2.hinj141_89_2
      Q2.hcardT141_89_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_89_2 i) (Q2.hfix141_89_2 i) _)
      colCert_141_89_20.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_89_21 (hp : 21 < (Q2.transData.getD 89 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨89, by decide⟩ : Fin 148)) (colE2 ⟨89, by decide⟩ 21 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨89, by decide⟩ : Fin 148))
        (colE1 ⟨89, by decide⟩ 21 (transLenTr ⟨89, by decide⟩ 21 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨89, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨89, by decide⟩ 21 (transLenTr ⟨89, by decide⟩ 21 hp)) T141_89
      hfix141_89 hinj141_89 hcardT141_89
      (fun i => conj_mem_of_fixedPoints _ _ (T141_89 i) (hfix141_89 i) _)
      ⟨141, by decide⟩ ⟨89, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨89, by decide⟩ 21 hp) Q2.T141_89_2 Q2.hfix141_89_2 Q2.hinj141_89_2
      Q2.hcardT141_89_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_89_2 i) (Q2.hfix141_89_2 i) _)
      colCert_141_89_21.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_89_22 (hp : 22 < (Q2.transData.getD 89 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨89, by decide⟩ : Fin 148)) (colE2 ⟨89, by decide⟩ 22 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨89, by decide⟩ : Fin 148))
        (colE1 ⟨89, by decide⟩ 22 (transLenTr ⟨89, by decide⟩ 22 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨89, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨89, by decide⟩ 22 (transLenTr ⟨89, by decide⟩ 22 hp)) T141_89
      hfix141_89 hinj141_89 hcardT141_89
      (fun i => conj_mem_of_fixedPoints _ _ (T141_89 i) (hfix141_89 i) _)
      ⟨141, by decide⟩ ⟨89, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨89, by decide⟩ 22 hp) Q2.T141_89_2 Q2.hfix141_89_2 Q2.hinj141_89_2
      Q2.hcardT141_89_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_89_2 i) (Q2.hfix141_89_2 i) _)
      colCert_141_89_22.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_89_23 (hp : 23 < (Q2.transData.getD 89 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨89, by decide⟩ : Fin 148)) (colE2 ⟨89, by decide⟩ 23 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨89, by decide⟩ : Fin 148))
        (colE1 ⟨89, by decide⟩ 23 (transLenTr ⟨89, by decide⟩ 23 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨89, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨89, by decide⟩ 23 (transLenTr ⟨89, by decide⟩ 23 hp)) T141_89
      hfix141_89 hinj141_89 hcardT141_89
      (fun i => conj_mem_of_fixedPoints _ _ (T141_89 i) (hfix141_89 i) _)
      ⟨141, by decide⟩ ⟨89, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨89, by decide⟩ 23 hp) Q2.T141_89_2 Q2.hfix141_89_2 Q2.hinj141_89_2
      Q2.hcardT141_89_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_89_2 i) (Q2.hfix141_89_2 i) _)
      colCert_141_89_23.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_89_24 (hp : 24 < (Q2.transData.getD 89 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨89, by decide⟩ : Fin 148)) (colE2 ⟨89, by decide⟩ 24 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨89, by decide⟩ : Fin 148))
        (colE1 ⟨89, by decide⟩ 24 (transLenTr ⟨89, by decide⟩ 24 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨89, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨89, by decide⟩ 24 (transLenTr ⟨89, by decide⟩ 24 hp)) T141_89
      hfix141_89 hinj141_89 hcardT141_89
      (fun i => conj_mem_of_fixedPoints _ _ (T141_89 i) (hfix141_89 i) _)
      ⟨141, by decide⟩ ⟨89, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨89, by decide⟩ 24 hp) Q2.T141_89_2 Q2.hfix141_89_2 Q2.hinj141_89_2
      Q2.hcardT141_89_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_89_2 i) (Q2.hfix141_89_2 i) _)
      colCert_141_89_24.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_115_0 (hp : 0 < (Q2.transData.getD 115 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨115, by decide⟩ : Fin 148)) (colE2 ⟨115, by decide⟩ 0 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨115, by decide⟩ : Fin 148))
        (colE1 ⟨115, by decide⟩ 0 (transLenTr ⟨115, by decide⟩ 0 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨115, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨115, by decide⟩ 0 (transLenTr ⟨115, by decide⟩ 0 hp)) T141_115
      hfix141_115 hinj141_115 hcardT141_115
      (fun i => conj_mem_of_fixedPoints _ _ (T141_115 i) (hfix141_115 i) _)
      ⟨141, by decide⟩ ⟨115, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨115, by decide⟩ 0 hp) Q2.T141_115_2 Q2.hfix141_115_2 Q2.hinj141_115_2
      Q2.hcardT141_115_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_115_2 i) (Q2.hfix141_115_2 i) _)
      colCert_141_115_0.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_115_1 (hp : 1 < (Q2.transData.getD 115 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨115, by decide⟩ : Fin 148)) (colE2 ⟨115, by decide⟩ 1 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨115, by decide⟩ : Fin 148))
        (colE1 ⟨115, by decide⟩ 1 (transLenTr ⟨115, by decide⟩ 1 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨115, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨115, by decide⟩ 1 (transLenTr ⟨115, by decide⟩ 1 hp)) T141_115
      hfix141_115 hinj141_115 hcardT141_115
      (fun i => conj_mem_of_fixedPoints _ _ (T141_115 i) (hfix141_115 i) _)
      ⟨141, by decide⟩ ⟨115, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨115, by decide⟩ 1 hp) Q2.T141_115_2 Q2.hfix141_115_2 Q2.hinj141_115_2
      Q2.hcardT141_115_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_115_2 i) (Q2.hfix141_115_2 i) _)
      colCert_141_115_1.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_115_2 (hp : 2 < (Q2.transData.getD 115 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨115, by decide⟩ : Fin 148)) (colE2 ⟨115, by decide⟩ 2 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨115, by decide⟩ : Fin 148))
        (colE1 ⟨115, by decide⟩ 2 (transLenTr ⟨115, by decide⟩ 2 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨115, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨115, by decide⟩ 2 (transLenTr ⟨115, by decide⟩ 2 hp)) T141_115
      hfix141_115 hinj141_115 hcardT141_115
      (fun i => conj_mem_of_fixedPoints _ _ (T141_115 i) (hfix141_115 i) _)
      ⟨141, by decide⟩ ⟨115, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨115, by decide⟩ 2 hp) Q2.T141_115_2 Q2.hfix141_115_2 Q2.hinj141_115_2
      Q2.hcardT141_115_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_115_2 i) (Q2.hfix141_115_2 i) _)
      colCert_141_115_2.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_115_3 (hp : 3 < (Q2.transData.getD 115 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨115, by decide⟩ : Fin 148)) (colE2 ⟨115, by decide⟩ 3 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨115, by decide⟩ : Fin 148))
        (colE1 ⟨115, by decide⟩ 3 (transLenTr ⟨115, by decide⟩ 3 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨115, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨115, by decide⟩ 3 (transLenTr ⟨115, by decide⟩ 3 hp)) T141_115
      hfix141_115 hinj141_115 hcardT141_115
      (fun i => conj_mem_of_fixedPoints _ _ (T141_115 i) (hfix141_115 i) _)
      ⟨141, by decide⟩ ⟨115, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨115, by decide⟩ 3 hp) Q2.T141_115_2 Q2.hfix141_115_2 Q2.hinj141_115_2
      Q2.hcardT141_115_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_115_2 i) (Q2.hfix141_115_2 i) _)
      colCert_141_115_3.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_115_4 (hp : 4 < (Q2.transData.getD 115 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨115, by decide⟩ : Fin 148)) (colE2 ⟨115, by decide⟩ 4 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨115, by decide⟩ : Fin 148))
        (colE1 ⟨115, by decide⟩ 4 (transLenTr ⟨115, by decide⟩ 4 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨115, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨115, by decide⟩ 4 (transLenTr ⟨115, by decide⟩ 4 hp)) T141_115
      hfix141_115 hinj141_115 hcardT141_115
      (fun i => conj_mem_of_fixedPoints _ _ (T141_115 i) (hfix141_115 i) _)
      ⟨141, by decide⟩ ⟨115, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨115, by decide⟩ 4 hp) Q2.T141_115_2 Q2.hfix141_115_2 Q2.hinj141_115_2
      Q2.hcardT141_115_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_115_2 i) (Q2.hfix141_115_2 i) _)
      colCert_141_115_4.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_115_5 (hp : 5 < (Q2.transData.getD 115 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨115, by decide⟩ : Fin 148)) (colE2 ⟨115, by decide⟩ 5 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨115, by decide⟩ : Fin 148))
        (colE1 ⟨115, by decide⟩ 5 (transLenTr ⟨115, by decide⟩ 5 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨115, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨115, by decide⟩ 5 (transLenTr ⟨115, by decide⟩ 5 hp)) T141_115
      hfix141_115 hinj141_115 hcardT141_115
      (fun i => conj_mem_of_fixedPoints _ _ (T141_115 i) (hfix141_115 i) _)
      ⟨141, by decide⟩ ⟨115, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨115, by decide⟩ 5 hp) Q2.T141_115_2 Q2.hfix141_115_2 Q2.hinj141_115_2
      Q2.hcardT141_115_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_115_2 i) (Q2.hfix141_115_2 i) _)
      colCert_141_115_5.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_115_10 (hp : 10 < (Q2.transData.getD 115 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨115, by decide⟩ : Fin 148)) (colE2 ⟨115, by decide⟩ 10 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨115, by decide⟩ : Fin 148))
        (colE1 ⟨115, by decide⟩ 10 (transLenTr ⟨115, by decide⟩ 10 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨115, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨115, by decide⟩ 10 (transLenTr ⟨115, by decide⟩ 10 hp)) T141_115
      hfix141_115 hinj141_115 hcardT141_115
      (fun i => conj_mem_of_fixedPoints _ _ (T141_115 i) (hfix141_115 i) _)
      ⟨141, by decide⟩ ⟨115, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨115, by decide⟩ 10 hp) Q2.T141_115_2 Q2.hfix141_115_2 Q2.hinj141_115_2
      Q2.hcardT141_115_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_115_2 i) (Q2.hfix141_115_2 i) _)
      colCert_141_115_10.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_115_15 (hp : 15 < (Q2.transData.getD 115 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨115, by decide⟩ : Fin 148)) (colE2 ⟨115, by decide⟩ 15 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨115, by decide⟩ : Fin 148))
        (colE1 ⟨115, by decide⟩ 15 (transLenTr ⟨115, by decide⟩ 15 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨115, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨115, by decide⟩ 15 (transLenTr ⟨115, by decide⟩ 15 hp)) T141_115
      hfix141_115 hinj141_115 hcardT141_115
      (fun i => conj_mem_of_fixedPoints _ _ (T141_115 i) (hfix141_115 i) _)
      ⟨141, by decide⟩ ⟨115, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨115, by decide⟩ 15 hp) Q2.T141_115_2 Q2.hfix141_115_2 Q2.hinj141_115_2
      Q2.hcardT141_115_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_115_2 i) (Q2.hfix141_115_2 i) _)
      colCert_141_115_15.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_115_20 (hp : 20 < (Q2.transData.getD 115 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨115, by decide⟩ : Fin 148)) (colE2 ⟨115, by decide⟩ 20 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨115, by decide⟩ : Fin 148))
        (colE1 ⟨115, by decide⟩ 20 (transLenTr ⟨115, by decide⟩ 20 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨115, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨115, by decide⟩ 20 (transLenTr ⟨115, by decide⟩ 20 hp)) T141_115
      hfix141_115 hinj141_115 hcardT141_115
      (fun i => conj_mem_of_fixedPoints _ _ (T141_115 i) (hfix141_115 i) _)
      ⟨141, by decide⟩ ⟨115, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨115, by decide⟩ 20 hp) Q2.T141_115_2 Q2.hfix141_115_2 Q2.hinj141_115_2
      Q2.hcardT141_115_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_115_2 i) (Q2.hfix141_115_2 i) _)
      colCert_141_115_20.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_141_0 (hp : 0 < (Q2.transData.getD 141 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨141, by decide⟩ : Fin 148)) (colE2 ⟨141, by decide⟩ 0 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨141, by decide⟩ : Fin 148))
        (colE1 ⟨141, by decide⟩ 0 (transLenTr ⟨141, by decide⟩ 0 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨141, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨141, by decide⟩ 0 (transLenTr ⟨141, by decide⟩ 0 hp)) T141_141
      hfix141_141 hinj141_141 hcardT141_141
      (fun i => conj_mem_of_fixedPoints _ _ (T141_141 i) (hfix141_141 i) _)
      ⟨141, by decide⟩ ⟨141, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨141, by decide⟩ 0 hp) Q2.T141_141_2 Q2.hfix141_141_2 Q2.hinj141_141_2
      Q2.hcardT141_141_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_141_2 i) (Q2.hfix141_141_2 i) _)
      colCert_141_141_0.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_141_1 (hp : 1 < (Q2.transData.getD 141 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨141, by decide⟩ : Fin 148)) (colE2 ⟨141, by decide⟩ 1 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨141, by decide⟩ : Fin 148))
        (colE1 ⟨141, by decide⟩ 1 (transLenTr ⟨141, by decide⟩ 1 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨141, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨141, by decide⟩ 1 (transLenTr ⟨141, by decide⟩ 1 hp)) T141_141
      hfix141_141 hinj141_141 hcardT141_141
      (fun i => conj_mem_of_fixedPoints _ _ (T141_141 i) (hfix141_141 i) _)
      ⟨141, by decide⟩ ⟨141, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨141, by decide⟩ 1 hp) Q2.T141_141_2 Q2.hfix141_141_2 Q2.hinj141_141_2
      Q2.hcardT141_141_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_141_2 i) (Q2.hfix141_141_2 i) _)
      colCert_141_141_1.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_141_2 (hp : 2 < (Q2.transData.getD 141 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨141, by decide⟩ : Fin 148)) (colE2 ⟨141, by decide⟩ 2 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨141, by decide⟩ : Fin 148))
        (colE1 ⟨141, by decide⟩ 2 (transLenTr ⟨141, by decide⟩ 2 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨141, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨141, by decide⟩ 2 (transLenTr ⟨141, by decide⟩ 2 hp)) T141_141
      hfix141_141 hinj141_141 hcardT141_141
      (fun i => conj_mem_of_fixedPoints _ _ (T141_141 i) (hfix141_141 i) _)
      ⟨141, by decide⟩ ⟨141, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨141, by decide⟩ 2 hp) Q2.T141_141_2 Q2.hfix141_141_2 Q2.hinj141_141_2
      Q2.hcardT141_141_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_141_2 i) (Q2.hfix141_141_2 i) _)
      colCert_141_141_2.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_141_3 (hp : 3 < (Q2.transData.getD 141 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨141, by decide⟩ : Fin 148)) (colE2 ⟨141, by decide⟩ 3 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨141, by decide⟩ : Fin 148))
        (colE1 ⟨141, by decide⟩ 3 (transLenTr ⟨141, by decide⟩ 3 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨141, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨141, by decide⟩ 3 (transLenTr ⟨141, by decide⟩ 3 hp)) T141_141
      hfix141_141 hinj141_141 hcardT141_141
      (fun i => conj_mem_of_fixedPoints _ _ (T141_141 i) (hfix141_141 i) _)
      ⟨141, by decide⟩ ⟨141, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨141, by decide⟩ 3 hp) Q2.T141_141_2 Q2.hfix141_141_2 Q2.hinj141_141_2
      Q2.hcardT141_141_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_141_2 i) (Q2.hfix141_141_2 i) _)
      colCert_141_141_3.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_141_4 (hp : 4 < (Q2.transData.getD 141 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨141, by decide⟩ : Fin 148)) (colE2 ⟨141, by decide⟩ 4 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨141, by decide⟩ : Fin 148))
        (colE1 ⟨141, by decide⟩ 4 (transLenTr ⟨141, by decide⟩ 4 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨141, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨141, by decide⟩ 4 (transLenTr ⟨141, by decide⟩ 4 hp)) T141_141
      hfix141_141 hinj141_141 hcardT141_141
      (fun i => conj_mem_of_fixedPoints _ _ (T141_141 i) (hfix141_141 i) _)
      ⟨141, by decide⟩ ⟨141, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨141, by decide⟩ 4 hp) Q2.T141_141_2 Q2.hfix141_141_2 Q2.hinj141_141_2
      Q2.hcardT141_141_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_141_2 i) (Q2.hfix141_141_2 i) _)
      colCert_141_141_4.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_141_5 (hp : 5 < (Q2.transData.getD 141 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨141, by decide⟩ : Fin 148)) (colE2 ⟨141, by decide⟩ 5 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨141, by decide⟩ : Fin 148))
        (colE1 ⟨141, by decide⟩ 5 (transLenTr ⟨141, by decide⟩ 5 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨141, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨141, by decide⟩ 5 (transLenTr ⟨141, by decide⟩ 5 hp)) T141_141
      hfix141_141 hinj141_141 hcardT141_141
      (fun i => conj_mem_of_fixedPoints _ _ (T141_141 i) (hfix141_141 i) _)
      ⟨141, by decide⟩ ⟨141, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨141, by decide⟩ 5 hp) Q2.T141_141_2 Q2.hfix141_141_2 Q2.hinj141_141_2
      Q2.hcardT141_141_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_141_2 i) (Q2.hfix141_141_2 i) _)
      colCert_141_141_5.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_141_6 (hp : 6 < (Q2.transData.getD 141 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨141, by decide⟩ : Fin 148)) (colE2 ⟨141, by decide⟩ 6 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨141, by decide⟩ : Fin 148))
        (colE1 ⟨141, by decide⟩ 6 (transLenTr ⟨141, by decide⟩ 6 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨141, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨141, by decide⟩ 6 (transLenTr ⟨141, by decide⟩ 6 hp)) T141_141
      hfix141_141 hinj141_141 hcardT141_141
      (fun i => conj_mem_of_fixedPoints _ _ (T141_141 i) (hfix141_141 i) _)
      ⟨141, by decide⟩ ⟨141, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨141, by decide⟩ 6 hp) Q2.T141_141_2 Q2.hfix141_141_2 Q2.hinj141_141_2
      Q2.hcardT141_141_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_141_2 i) (Q2.hfix141_141_2 i) _)
      colCert_141_141_6.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_141_7 (hp : 7 < (Q2.transData.getD 141 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨141, by decide⟩ : Fin 148)) (colE2 ⟨141, by decide⟩ 7 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨141, by decide⟩ : Fin 148))
        (colE1 ⟨141, by decide⟩ 7 (transLenTr ⟨141, by decide⟩ 7 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨141, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨141, by decide⟩ 7 (transLenTr ⟨141, by decide⟩ 7 hp)) T141_141
      hfix141_141 hinj141_141 hcardT141_141
      (fun i => conj_mem_of_fixedPoints _ _ (T141_141 i) (hfix141_141 i) _)
      ⟨141, by decide⟩ ⟨141, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨141, by decide⟩ 7 hp) Q2.T141_141_2 Q2.hfix141_141_2 Q2.hinj141_141_2
      Q2.hcardT141_141_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_141_2 i) (Q2.hfix141_141_2 i) _)
      colCert_141_141_7.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_141_8 (hp : 8 < (Q2.transData.getD 141 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨141, by decide⟩ : Fin 148)) (colE2 ⟨141, by decide⟩ 8 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨141, by decide⟩ : Fin 148))
        (colE1 ⟨141, by decide⟩ 8 (transLenTr ⟨141, by decide⟩ 8 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨141, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨141, by decide⟩ 8 (transLenTr ⟨141, by decide⟩ 8 hp)) T141_141
      hfix141_141 hinj141_141 hcardT141_141
      (fun i => conj_mem_of_fixedPoints _ _ (T141_141 i) (hfix141_141 i) _)
      ⟨141, by decide⟩ ⟨141, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨141, by decide⟩ 8 hp) Q2.T141_141_2 Q2.hfix141_141_2 Q2.hinj141_141_2
      Q2.hcardT141_141_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_141_2 i) (Q2.hfix141_141_2 i) _)
      colCert_141_141_8.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_141_9 (hp : 9 < (Q2.transData.getD 141 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨141, by decide⟩ : Fin 148)) (colE2 ⟨141, by decide⟩ 9 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨141, by decide⟩ : Fin 148))
        (colE1 ⟨141, by decide⟩ 9 (transLenTr ⟨141, by decide⟩ 9 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨141, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨141, by decide⟩ 9 (transLenTr ⟨141, by decide⟩ 9 hp)) T141_141
      hfix141_141 hinj141_141 hcardT141_141
      (fun i => conj_mem_of_fixedPoints _ _ (T141_141 i) (hfix141_141 i) _)
      ⟨141, by decide⟩ ⟨141, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨141, by decide⟩ 9 hp) Q2.T141_141_2 Q2.hfix141_141_2 Q2.hinj141_141_2
      Q2.hcardT141_141_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_141_2 i) (Q2.hfix141_141_2 i) _)
      colCert_141_141_9.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_141_10 (hp : 10 < (Q2.transData.getD 141 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨141, by decide⟩ : Fin 148)) (colE2 ⟨141, by decide⟩ 10 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨141, by decide⟩ : Fin 148))
        (colE1 ⟨141, by decide⟩ 10 (transLenTr ⟨141, by decide⟩ 10 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨141, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨141, by decide⟩ 10 (transLenTr ⟨141, by decide⟩ 10 hp)) T141_141
      hfix141_141 hinj141_141 hcardT141_141
      (fun i => conj_mem_of_fixedPoints _ _ (T141_141 i) (hfix141_141 i) _)
      ⟨141, by decide⟩ ⟨141, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨141, by decide⟩ 10 hp) Q2.T141_141_2 Q2.hfix141_141_2 Q2.hinj141_141_2
      Q2.hcardT141_141_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_141_2 i) (Q2.hfix141_141_2 i) _)
      colCert_141_141_10.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_141_11 (hp : 11 < (Q2.transData.getD 141 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨141, by decide⟩ : Fin 148)) (colE2 ⟨141, by decide⟩ 11 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨141, by decide⟩ : Fin 148))
        (colE1 ⟨141, by decide⟩ 11 (transLenTr ⟨141, by decide⟩ 11 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨141, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨141, by decide⟩ 11 (transLenTr ⟨141, by decide⟩ 11 hp)) T141_141
      hfix141_141 hinj141_141 hcardT141_141
      (fun i => conj_mem_of_fixedPoints _ _ (T141_141 i) (hfix141_141 i) _)
      ⟨141, by decide⟩ ⟨141, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨141, by decide⟩ 11 hp) Q2.T141_141_2 Q2.hfix141_141_2 Q2.hinj141_141_2
      Q2.hcardT141_141_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_141_2 i) (Q2.hfix141_141_2 i) _)
      colCert_141_141_11.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_141_12 (hp : 12 < (Q2.transData.getD 141 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨141, by decide⟩ : Fin 148)) (colE2 ⟨141, by decide⟩ 12 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨141, by decide⟩ : Fin 148))
        (colE1 ⟨141, by decide⟩ 12 (transLenTr ⟨141, by decide⟩ 12 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨141, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨141, by decide⟩ 12 (transLenTr ⟨141, by decide⟩ 12 hp)) T141_141
      hfix141_141 hinj141_141 hcardT141_141
      (fun i => conj_mem_of_fixedPoints _ _ (T141_141 i) (hfix141_141 i) _)
      ⟨141, by decide⟩ ⟨141, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨141, by decide⟩ 12 hp) Q2.T141_141_2 Q2.hfix141_141_2 Q2.hinj141_141_2
      Q2.hcardT141_141_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_141_2 i) (Q2.hfix141_141_2 i) _)
      colCert_141_141_12.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_141_13 (hp : 13 < (Q2.transData.getD 141 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨141, by decide⟩ : Fin 148)) (colE2 ⟨141, by decide⟩ 13 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨141, by decide⟩ : Fin 148))
        (colE1 ⟨141, by decide⟩ 13 (transLenTr ⟨141, by decide⟩ 13 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨141, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨141, by decide⟩ 13 (transLenTr ⟨141, by decide⟩ 13 hp)) T141_141
      hfix141_141 hinj141_141 hcardT141_141
      (fun i => conj_mem_of_fixedPoints _ _ (T141_141 i) (hfix141_141 i) _)
      ⟨141, by decide⟩ ⟨141, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨141, by decide⟩ 13 hp) Q2.T141_141_2 Q2.hfix141_141_2 Q2.hinj141_141_2
      Q2.hcardT141_141_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_141_2 i) (Q2.hfix141_141_2 i) _)
      colCert_141_141_13.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_141_14 (hp : 14 < (Q2.transData.getD 141 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨141, by decide⟩ : Fin 148)) (colE2 ⟨141, by decide⟩ 14 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨141, by decide⟩ : Fin 148))
        (colE1 ⟨141, by decide⟩ 14 (transLenTr ⟨141, by decide⟩ 14 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨141, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨141, by decide⟩ 14 (transLenTr ⟨141, by decide⟩ 14 hp)) T141_141
      hfix141_141 hinj141_141 hcardT141_141
      (fun i => conj_mem_of_fixedPoints _ _ (T141_141 i) (hfix141_141 i) _)
      ⟨141, by decide⟩ ⟨141, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨141, by decide⟩ 14 hp) Q2.T141_141_2 Q2.hfix141_141_2 Q2.hinj141_141_2
      Q2.hcardT141_141_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_141_2 i) (Q2.hfix141_141_2 i) _)
      colCert_141_141_14.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_141_15 (hp : 15 < (Q2.transData.getD 141 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨141, by decide⟩ : Fin 148)) (colE2 ⟨141, by decide⟩ 15 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨141, by decide⟩ : Fin 148))
        (colE1 ⟨141, by decide⟩ 15 (transLenTr ⟨141, by decide⟩ 15 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨141, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨141, by decide⟩ 15 (transLenTr ⟨141, by decide⟩ 15 hp)) T141_141
      hfix141_141 hinj141_141 hcardT141_141
      (fun i => conj_mem_of_fixedPoints _ _ (T141_141 i) (hfix141_141 i) _)
      ⟨141, by decide⟩ ⟨141, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨141, by decide⟩ 15 hp) Q2.T141_141_2 Q2.hfix141_141_2 Q2.hinj141_141_2
      Q2.hcardT141_141_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_141_2 i) (Q2.hfix141_141_2 i) _)
      colCert_141_141_15.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_141_16 (hp : 16 < (Q2.transData.getD 141 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨141, by decide⟩ : Fin 148)) (colE2 ⟨141, by decide⟩ 16 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨141, by decide⟩ : Fin 148))
        (colE1 ⟨141, by decide⟩ 16 (transLenTr ⟨141, by decide⟩ 16 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨141, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨141, by decide⟩ 16 (transLenTr ⟨141, by decide⟩ 16 hp)) T141_141
      hfix141_141 hinj141_141 hcardT141_141
      (fun i => conj_mem_of_fixedPoints _ _ (T141_141 i) (hfix141_141 i) _)
      ⟨141, by decide⟩ ⟨141, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨141, by decide⟩ 16 hp) Q2.T141_141_2 Q2.hfix141_141_2 Q2.hinj141_141_2
      Q2.hcardT141_141_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_141_2 i) (Q2.hfix141_141_2 i) _)
      colCert_141_141_16.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_141_17 (hp : 17 < (Q2.transData.getD 141 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨141, by decide⟩ : Fin 148)) (colE2 ⟨141, by decide⟩ 17 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨141, by decide⟩ : Fin 148))
        (colE1 ⟨141, by decide⟩ 17 (transLenTr ⟨141, by decide⟩ 17 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨141, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨141, by decide⟩ 17 (transLenTr ⟨141, by decide⟩ 17 hp)) T141_141
      hfix141_141 hinj141_141 hcardT141_141
      (fun i => conj_mem_of_fixedPoints _ _ (T141_141 i) (hfix141_141 i) _)
      ⟨141, by decide⟩ ⟨141, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨141, by decide⟩ 17 hp) Q2.T141_141_2 Q2.hfix141_141_2 Q2.hinj141_141_2
      Q2.hcardT141_141_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_141_2 i) (Q2.hfix141_141_2 i) _)
      colCert_141_141_17.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_141_18 (hp : 18 < (Q2.transData.getD 141 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨141, by decide⟩ : Fin 148)) (colE2 ⟨141, by decide⟩ 18 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨141, by decide⟩ : Fin 148))
        (colE1 ⟨141, by decide⟩ 18 (transLenTr ⟨141, by decide⟩ 18 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨141, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨141, by decide⟩ 18 (transLenTr ⟨141, by decide⟩ 18 hp)) T141_141
      hfix141_141 hinj141_141 hcardT141_141
      (fun i => conj_mem_of_fixedPoints _ _ (T141_141 i) (hfix141_141 i) _)
      ⟨141, by decide⟩ ⟨141, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨141, by decide⟩ 18 hp) Q2.T141_141_2 Q2.hfix141_141_2 Q2.hinj141_141_2
      Q2.hcardT141_141_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_141_2 i) (Q2.hfix141_141_2 i) _)
      colCert_141_141_18.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_141_19 (hp : 19 < (Q2.transData.getD 141 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨141, by decide⟩ : Fin 148)) (colE2 ⟨141, by decide⟩ 19 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨141, by decide⟩ : Fin 148))
        (colE1 ⟨141, by decide⟩ 19 (transLenTr ⟨141, by decide⟩ 19 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨141, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨141, by decide⟩ 19 (transLenTr ⟨141, by decide⟩ 19 hp)) T141_141
      hfix141_141 hinj141_141 hcardT141_141
      (fun i => conj_mem_of_fixedPoints _ _ (T141_141 i) (hfix141_141 i) _)
      ⟨141, by decide⟩ ⟨141, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨141, by decide⟩ 19 hp) Q2.T141_141_2 Q2.hfix141_141_2 Q2.hinj141_141_2
      Q2.hcardT141_141_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_141_2 i) (Q2.hfix141_141_2 i) _)
      colCert_141_141_19.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_141_20 (hp : 20 < (Q2.transData.getD 141 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨141, by decide⟩ : Fin 148)) (colE2 ⟨141, by decide⟩ 20 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨141, by decide⟩ : Fin 148))
        (colE1 ⟨141, by decide⟩ 20 (transLenTr ⟨141, by decide⟩ 20 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨141, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨141, by decide⟩ 20 (transLenTr ⟨141, by decide⟩ 20 hp)) T141_141
      hfix141_141 hinj141_141 hcardT141_141
      (fun i => conj_mem_of_fixedPoints _ _ (T141_141 i) (hfix141_141 i) _)
      ⟨141, by decide⟩ ⟨141, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨141, by decide⟩ 20 hp) Q2.T141_141_2 Q2.hfix141_141_2 Q2.hinj141_141_2
      Q2.hcardT141_141_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_141_2 i) (Q2.hfix141_141_2 i) _)
      colCert_141_141_20.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_141_21 (hp : 21 < (Q2.transData.getD 141 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨141, by decide⟩ : Fin 148)) (colE2 ⟨141, by decide⟩ 21 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨141, by decide⟩ : Fin 148))
        (colE1 ⟨141, by decide⟩ 21 (transLenTr ⟨141, by decide⟩ 21 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨141, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨141, by decide⟩ 21 (transLenTr ⟨141, by decide⟩ 21 hp)) T141_141
      hfix141_141 hinj141_141 hcardT141_141
      (fun i => conj_mem_of_fixedPoints _ _ (T141_141 i) (hfix141_141 i) _)
      ⟨141, by decide⟩ ⟨141, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨141, by decide⟩ 21 hp) Q2.T141_141_2 Q2.hfix141_141_2 Q2.hinj141_141_2
      Q2.hcardT141_141_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_141_2 i) (Q2.hfix141_141_2 i) _)
      colCert_141_141_21.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_141_22 (hp : 22 < (Q2.transData.getD 141 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨141, by decide⟩ : Fin 148)) (colE2 ⟨141, by decide⟩ 22 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨141, by decide⟩ : Fin 148))
        (colE1 ⟨141, by decide⟩ 22 (transLenTr ⟨141, by decide⟩ 22 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨141, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨141, by decide⟩ 22 (transLenTr ⟨141, by decide⟩ 22 hp)) T141_141
      hfix141_141 hinj141_141 hcardT141_141
      (fun i => conj_mem_of_fixedPoints _ _ (T141_141 i) (hfix141_141 i) _)
      ⟨141, by decide⟩ ⟨141, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨141, by decide⟩ 22 hp) Q2.T141_141_2 Q2.hfix141_141_2 Q2.hinj141_141_2
      Q2.hcardT141_141_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_141_2 i) (Q2.hfix141_141_2 i) _)
      colCert_141_141_22.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_141_23 (hp : 23 < (Q2.transData.getD 141 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨141, by decide⟩ : Fin 148)) (colE2 ⟨141, by decide⟩ 23 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨141, by decide⟩ : Fin 148))
        (colE1 ⟨141, by decide⟩ 23 (transLenTr ⟨141, by decide⟩ 23 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨141, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨141, by decide⟩ 23 (transLenTr ⟨141, by decide⟩ 23 hp)) T141_141
      hfix141_141 hinj141_141 hcardT141_141
      (fun i => conj_mem_of_fixedPoints _ _ (T141_141 i) (hfix141_141 i) _)
      ⟨141, by decide⟩ ⟨141, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨141, by decide⟩ 23 hp) Q2.T141_141_2 Q2.hfix141_141_2 Q2.hinj141_141_2
      Q2.hcardT141_141_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_141_2 i) (Q2.hfix141_141_2 i) _)
      colCert_141_141_23.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_141_24 (hp : 24 < (Q2.transData.getD 141 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨141, by decide⟩ : Fin 148)) (colE2 ⟨141, by decide⟩ 24 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨141, by decide⟩ : Fin 148))
        (colE1 ⟨141, by decide⟩ 24 (transLenTr ⟨141, by decide⟩ 24 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨141, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨141, by decide⟩ 24 (transLenTr ⟨141, by decide⟩ 24 hp)) T141_141
      hfix141_141 hinj141_141 hcardT141_141
      (fun i => conj_mem_of_fixedPoints _ _ (T141_141 i) (hfix141_141 i) _)
      ⟨141, by decide⟩ ⟨141, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨141, by decide⟩ 24 hp) Q2.T141_141_2 Q2.hfix141_141_2 Q2.hinj141_141_2
      Q2.hcardT141_141_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_141_2 i) (Q2.hfix141_141_2 i) _)
      colCert_141_141_24.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_141_25 (hp : 25 < (Q2.transData.getD 141 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨141, by decide⟩ : Fin 148)) (colE2 ⟨141, by decide⟩ 25 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨141, by decide⟩ : Fin 148))
        (colE1 ⟨141, by decide⟩ 25 (transLenTr ⟨141, by decide⟩ 25 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨141, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨141, by decide⟩ 25 (transLenTr ⟨141, by decide⟩ 25 hp)) T141_141
      hfix141_141 hinj141_141 hcardT141_141
      (fun i => conj_mem_of_fixedPoints _ _ (T141_141 i) (hfix141_141 i) _)
      ⟨141, by decide⟩ ⟨141, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨141, by decide⟩ 25 hp) Q2.T141_141_2 Q2.hfix141_141_2 Q2.hinj141_141_2
      Q2.hcardT141_141_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_141_2 i) (Q2.hfix141_141_2 i) _)
      colCert_141_141_25.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_141_30 (hp : 30 < (Q2.transData.getD 141 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨141, by decide⟩ : Fin 148)) (colE2 ⟨141, by decide⟩ 30 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨141, by decide⟩ : Fin 148))
        (colE1 ⟨141, by decide⟩ 30 (transLenTr ⟨141, by decide⟩ 30 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨141, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨141, by decide⟩ 30 (transLenTr ⟨141, by decide⟩ 30 hp)) T141_141
      hfix141_141 hinj141_141 hcardT141_141
      (fun i => conj_mem_of_fixedPoints _ _ (T141_141 i) (hfix141_141 i) _)
      ⟨141, by decide⟩ ⟨141, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨141, by decide⟩ 30 hp) Q2.T141_141_2 Q2.hfix141_141_2 Q2.hinj141_141_2
      Q2.hcardT141_141_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_141_2 i) (Q2.hfix141_141_2 i) _)
      colCert_141_141_30.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_141_35 (hp : 35 < (Q2.transData.getD 141 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨141, by decide⟩ : Fin 148)) (colE2 ⟨141, by decide⟩ 35 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨141, by decide⟩ : Fin 148))
        (colE1 ⟨141, by decide⟩ 35 (transLenTr ⟨141, by decide⟩ 35 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨141, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨141, by decide⟩ 35 (transLenTr ⟨141, by decide⟩ 35 hp)) T141_141
      hfix141_141 hinj141_141 hcardT141_141
      (fun i => conj_mem_of_fixedPoints _ _ (T141_141 i) (hfix141_141 i) _)
      ⟨141, by decide⟩ ⟨141, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨141, by decide⟩ 35 hp) Q2.T141_141_2 Q2.hfix141_141_2 Q2.hinj141_141_2
      Q2.hcardT141_141_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_141_2 i) (Q2.hfix141_141_2 i) _)
      colCert_141_141_35.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_141_40 (hp : 40 < (Q2.transData.getD 141 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨141, by decide⟩ : Fin 148)) (colE2 ⟨141, by decide⟩ 40 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨141, by decide⟩ : Fin 148))
        (colE1 ⟨141, by decide⟩ 40 (transLenTr ⟨141, by decide⟩ 40 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨141, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨141, by decide⟩ 40 (transLenTr ⟨141, by decide⟩ 40 hp)) T141_141
      hfix141_141 hinj141_141 hcardT141_141
      (fun i => conj_mem_of_fixedPoints _ _ (T141_141 i) (hfix141_141 i) _)
      ⟨141, by decide⟩ ⟨141, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨141, by decide⟩ 40 hp) Q2.T141_141_2 Q2.hfix141_141_2 Q2.hinj141_141_2
      Q2.hcardT141_141_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_141_2 i) (Q2.hfix141_141_2 i) _)
      colCert_141_141_40.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_141_45 (hp : 45 < (Q2.transData.getD 141 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨141, by decide⟩ : Fin 148)) (colE2 ⟨141, by decide⟩ 45 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨141, by decide⟩ : Fin 148))
        (colE1 ⟨141, by decide⟩ 45 (transLenTr ⟨141, by decide⟩ 45 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨141, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨141, by decide⟩ 45 (transLenTr ⟨141, by decide⟩ 45 hp)) T141_141
      hfix141_141 hinj141_141 hcardT141_141
      (fun i => conj_mem_of_fixedPoints _ _ (T141_141 i) (hfix141_141 i) _)
      ⟨141, by decide⟩ ⟨141, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨141, by decide⟩ 45 hp) Q2.T141_141_2 Q2.hfix141_141_2 Q2.hinj141_141_2
      Q2.hcardT141_141_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_141_2 i) (Q2.hfix141_141_2 i) _)
      colCert_141_141_45.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_141_50 (hp : 50 < (Q2.transData.getD 141 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨141, by decide⟩ : Fin 148)) (colE2 ⟨141, by decide⟩ 50 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨141, by decide⟩ : Fin 148))
        (colE1 ⟨141, by decide⟩ 50 (transLenTr ⟨141, by decide⟩ 50 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨141, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨141, by decide⟩ 50 (transLenTr ⟨141, by decide⟩ 50 hp)) T141_141
      hfix141_141 hinj141_141 hcardT141_141
      (fun i => conj_mem_of_fixedPoints _ _ (T141_141 i) (hfix141_141 i) _)
      ⟨141, by decide⟩ ⟨141, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨141, by decide⟩ 50 hp) Q2.T141_141_2 Q2.hfix141_141_2 Q2.hinj141_141_2
      Q2.hcardT141_141_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_141_2 i) (Q2.hfix141_141_2 i) _)
      colCert_141_141_50.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_141_55 (hp : 55 < (Q2.transData.getD 141 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨141, by decide⟩ : Fin 148)) (colE2 ⟨141, by decide⟩ 55 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨141, by decide⟩ : Fin 148))
        (colE1 ⟨141, by decide⟩ 55 (transLenTr ⟨141, by decide⟩ 55 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨141, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨141, by decide⟩ 55 (transLenTr ⟨141, by decide⟩ 55 hp)) T141_141
      hfix141_141 hinj141_141 hcardT141_141
      (fun i => conj_mem_of_fixedPoints _ _ (T141_141 i) (hfix141_141 i) _)
      ⟨141, by decide⟩ ⟨141, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨141, by decide⟩ 55 hp) Q2.T141_141_2 Q2.hfix141_141_2 Q2.hinj141_141_2
      Q2.hcardT141_141_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_141_2 i) (Q2.hfix141_141_2 i) _)
      colCert_141_141_55.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_141_60 (hp : 60 < (Q2.transData.getD 141 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨141, by decide⟩ : Fin 148)) (colE2 ⟨141, by decide⟩ 60 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨141, by decide⟩ : Fin 148))
        (colE1 ⟨141, by decide⟩ 60 (transLenTr ⟨141, by decide⟩ 60 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨141, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨141, by decide⟩ 60 (transLenTr ⟨141, by decide⟩ 60 hp)) T141_141
      hfix141_141 hinj141_141 hcardT141_141
      (fun i => conj_mem_of_fixedPoints _ _ (T141_141 i) (hfix141_141 i) _)
      ⟨141, by decide⟩ ⟨141, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨141, by decide⟩ 60 hp) Q2.T141_141_2 Q2.hfix141_141_2 Q2.hinj141_141_2
      Q2.hcardT141_141_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_141_2 i) (Q2.hfix141_141_2 i) _)
      colCert_141_141_60.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_141_65 (hp : 65 < (Q2.transData.getD 141 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨141, by decide⟩ : Fin 148)) (colE2 ⟨141, by decide⟩ 65 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨141, by decide⟩ : Fin 148))
        (colE1 ⟨141, by decide⟩ 65 (transLenTr ⟨141, by decide⟩ 65 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨141, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨141, by decide⟩ 65 (transLenTr ⟨141, by decide⟩ 65 hp)) T141_141
      hfix141_141 hinj141_141 hcardT141_141
      (fun i => conj_mem_of_fixedPoints _ _ (T141_141 i) (hfix141_141 i) _)
      ⟨141, by decide⟩ ⟨141, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨141, by decide⟩ 65 hp) Q2.T141_141_2 Q2.hfix141_141_2 Q2.hinj141_141_2
      Q2.hcardT141_141_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_141_2 i) (Q2.hfix141_141_2 i) _)
      colCert_141_141_65.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_141_70 (hp : 70 < (Q2.transData.getD 141 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨141, by decide⟩ : Fin 148)) (colE2 ⟨141, by decide⟩ 70 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨141, by decide⟩ : Fin 148))
        (colE1 ⟨141, by decide⟩ 70 (transLenTr ⟨141, by decide⟩ 70 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨141, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨141, by decide⟩ 70 (transLenTr ⟨141, by decide⟩ 70 hp)) T141_141
      hfix141_141 hinj141_141 hcardT141_141
      (fun i => conj_mem_of_fixedPoints _ _ (T141_141 i) (hfix141_141 i) _)
      ⟨141, by decide⟩ ⟨141, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨141, by decide⟩ 70 hp) Q2.T141_141_2 Q2.hfix141_141_2 Q2.hinj141_141_2
      Q2.hcardT141_141_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_141_2 i) (Q2.hfix141_141_2 i) _)
      colCert_141_141_70.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_141_75 (hp : 75 < (Q2.transData.getD 141 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨141, by decide⟩ : Fin 148)) (colE2 ⟨141, by decide⟩ 75 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨141, by decide⟩ : Fin 148))
        (colE1 ⟨141, by decide⟩ 75 (transLenTr ⟨141, by decide⟩ 75 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨141, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨141, by decide⟩ 75 (transLenTr ⟨141, by decide⟩ 75 hp)) T141_141
      hfix141_141 hinj141_141 hcardT141_141
      (fun i => conj_mem_of_fixedPoints _ _ (T141_141 i) (hfix141_141 i) _)
      ⟨141, by decide⟩ ⟨141, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨141, by decide⟩ 75 hp) Q2.T141_141_2 Q2.hfix141_141_2 Q2.hinj141_141_2
      Q2.hcardT141_141_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_141_2 i) (Q2.hfix141_141_2 i) _)
      colCert_141_141_75.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_141_80 (hp : 80 < (Q2.transData.getD 141 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨141, by decide⟩ : Fin 148)) (colE2 ⟨141, by decide⟩ 80 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨141, by decide⟩ : Fin 148))
        (colE1 ⟨141, by decide⟩ 80 (transLenTr ⟨141, by decide⟩ 80 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨141, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨141, by decide⟩ 80 (transLenTr ⟨141, by decide⟩ 80 hp)) T141_141
      hfix141_141 hinj141_141 hcardT141_141
      (fun i => conj_mem_of_fixedPoints _ _ (T141_141 i) (hfix141_141 i) _)
      ⟨141, by decide⟩ ⟨141, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨141, by decide⟩ 80 hp) Q2.T141_141_2 Q2.hfix141_141_2 Q2.hinj141_141_2
      Q2.hcardT141_141_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_141_2 i) (Q2.hfix141_141_2 i) _)
      colCert_141_141_80.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_141_85 (hp : 85 < (Q2.transData.getD 141 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨141, by decide⟩ : Fin 148)) (colE2 ⟨141, by decide⟩ 85 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨141, by decide⟩ : Fin 148))
        (colE1 ⟨141, by decide⟩ 85 (transLenTr ⟨141, by decide⟩ 85 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨141, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨141, by decide⟩ 85 (transLenTr ⟨141, by decide⟩ 85 hp)) T141_141
      hfix141_141 hinj141_141 hcardT141_141
      (fun i => conj_mem_of_fixedPoints _ _ (T141_141 i) (hfix141_141 i) _)
      ⟨141, by decide⟩ ⟨141, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨141, by decide⟩ 85 hp) Q2.T141_141_2 Q2.hfix141_141_2 Q2.hinj141_141_2
      Q2.hcardT141_141_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_141_2 i) (Q2.hfix141_141_2 i) _)
      colCert_141_141_85.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_141_90 (hp : 90 < (Q2.transData.getD 141 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨141, by decide⟩ : Fin 148)) (colE2 ⟨141, by decide⟩ 90 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨141, by decide⟩ : Fin 148))
        (colE1 ⟨141, by decide⟩ 90 (transLenTr ⟨141, by decide⟩ 90 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨141, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨141, by decide⟩ 90 (transLenTr ⟨141, by decide⟩ 90 hp)) T141_141
      hfix141_141 hinj141_141 hcardT141_141
      (fun i => conj_mem_of_fixedPoints _ _ (T141_141 i) (hfix141_141 i) _)
      ⟨141, by decide⟩ ⟨141, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨141, by decide⟩ 90 hp) Q2.T141_141_2 Q2.hfix141_141_2 Q2.hinj141_141_2
      Q2.hcardT141_141_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_141_2 i) (Q2.hfix141_141_2 i) _)
      colCert_141_141_90.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_141_95 (hp : 95 < (Q2.transData.getD 141 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨141, by decide⟩ : Fin 148)) (colE2 ⟨141, by decide⟩ 95 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨141, by decide⟩ : Fin 148))
        (colE1 ⟨141, by decide⟩ 95 (transLenTr ⟨141, by decide⟩ 95 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨141, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨141, by decide⟩ 95 (transLenTr ⟨141, by decide⟩ 95 hp)) T141_141
      hfix141_141 hinj141_141 hcardT141_141
      (fun i => conj_mem_of_fixedPoints _ _ (T141_141 i) (hfix141_141 i) _)
      ⟨141, by decide⟩ ⟨141, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨141, by decide⟩ 95 hp) Q2.T141_141_2 Q2.hfix141_141_2 Q2.hinj141_141_2
      Q2.hcardT141_141_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_141_2 i) (Q2.hfix141_141_2 i) _)
      colCert_141_141_95.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_141_100 (hp : 100 < (Q2.transData.getD 141 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨141, by decide⟩ : Fin 148)) (colE2 ⟨141, by decide⟩ 100 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨141, by decide⟩ : Fin 148))
        (colE1 ⟨141, by decide⟩ 100 (transLenTr ⟨141, by decide⟩ 100 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨141, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨141, by decide⟩ 100 (transLenTr ⟨141, by decide⟩ 100 hp)) T141_141
      hfix141_141 hinj141_141 hcardT141_141
      (fun i => conj_mem_of_fixedPoints _ _ (T141_141 i) (hfix141_141 i) _)
      ⟨141, by decide⟩ ⟨141, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨141, by decide⟩ 100 hp) Q2.T141_141_2 Q2.hfix141_141_2 Q2.hinj141_141_2
      Q2.hcardT141_141_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_141_2 i) (Q2.hfix141_141_2 i) _)
      colCert_141_141_100.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_141_105 (hp : 105 < (Q2.transData.getD 141 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨141, by decide⟩ : Fin 148)) (colE2 ⟨141, by decide⟩ 105 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨141, by decide⟩ : Fin 148))
        (colE1 ⟨141, by decide⟩ 105 (transLenTr ⟨141, by decide⟩ 105 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨141, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨141, by decide⟩ 105 (transLenTr ⟨141, by decide⟩ 105 hp)) T141_141
      hfix141_141 hinj141_141 hcardT141_141
      (fun i => conj_mem_of_fixedPoints _ _ (T141_141 i) (hfix141_141 i) _)
      ⟨141, by decide⟩ ⟨141, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨141, by decide⟩ 105 hp) Q2.T141_141_2 Q2.hfix141_141_2 Q2.hinj141_141_2
      Q2.hcardT141_141_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_141_2 i) (Q2.hfix141_141_2 i) _)
      colCert_141_141_105.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_141_110 (hp : 110 < (Q2.transData.getD 141 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨141, by decide⟩ : Fin 148)) (colE2 ⟨141, by decide⟩ 110 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨141, by decide⟩ : Fin 148))
        (colE1 ⟨141, by decide⟩ 110 (transLenTr ⟨141, by decide⟩ 110 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨141, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨141, by decide⟩ 110 (transLenTr ⟨141, by decide⟩ 110 hp)) T141_141
      hfix141_141 hinj141_141 hcardT141_141
      (fun i => conj_mem_of_fixedPoints _ _ (T141_141 i) (hfix141_141 i) _)
      ⟨141, by decide⟩ ⟨141, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨141, by decide⟩ 110 hp) Q2.T141_141_2 Q2.hfix141_141_2 Q2.hinj141_141_2
      Q2.hcardT141_141_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_141_2 i) (Q2.hfix141_141_2 i) _)
      colCert_141_141_110.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_141_115 (hp : 115 < (Q2.transData.getD 141 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨141, by decide⟩ : Fin 148)) (colE2 ⟨141, by decide⟩ 115 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨141, by decide⟩ : Fin 148))
        (colE1 ⟨141, by decide⟩ 115 (transLenTr ⟨141, by decide⟩ 115 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨141, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨141, by decide⟩ 115 (transLenTr ⟨141, by decide⟩ 115 hp)) T141_141
      hfix141_141 hinj141_141 hcardT141_141
      (fun i => conj_mem_of_fixedPoints _ _ (T141_141 i) (hfix141_141 i) _)
      ⟨141, by decide⟩ ⟨141, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨141, by decide⟩ 115 hp) Q2.T141_141_2 Q2.hfix141_141_2 Q2.hinj141_141_2
      Q2.hcardT141_141_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_141_2 i) (Q2.hfix141_141_2 i) _)
      colCert_141_141_115.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_141_120 (hp : 120 < (Q2.transData.getD 141 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨141, by decide⟩ : Fin 148)) (colE2 ⟨141, by decide⟩ 120 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨141, by decide⟩ : Fin 148))
        (colE1 ⟨141, by decide⟩ 120 (transLenTr ⟨141, by decide⟩ 120 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨141, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨141, by decide⟩ 120 (transLenTr ⟨141, by decide⟩ 120 hp)) T141_141
      hfix141_141 hinj141_141 hcardT141_141
      (fun i => conj_mem_of_fixedPoints _ _ (T141_141 i) (hfix141_141 i) _)
      ⟨141, by decide⟩ ⟨141, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨141, by decide⟩ 120 hp) Q2.T141_141_2 Q2.hfix141_141_2 Q2.hinj141_141_2
      Q2.hcardT141_141_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_141_2 i) (Q2.hfix141_141_2 i) _)
      colCert_141_141_120.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_142_10_0 (hp : 0 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 142 []).length)
    (hq : (normIsRep.getD 142 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 0 hp)
        (rowE2 (⟨142, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 0 (transLenTr ⟨10, by decide⟩ 0 hp))
        (rowE1 (⟨142, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨142, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨142, by decide⟩ (listedAt ⟨142, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 0 (transLenTr ⟨10, by decide⟩ 0 hp)) T142_10
      hfix142_10 hinj142_10 hcardT142_10
      (fun i => conj_mem_of_fixedPoints _ _ (T142_10 i) (hfix142_10 i) _)
      ⟨142, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨142, by decide⟩ (Q2.listedAt ⟨142, by decide⟩
        (alnCheck_rep ⟨142, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 0 hp) Q2.T142_10_2 Q2.hfix142_10_2 Q2.hinj142_10_2
      Q2.hcardT142_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T142_10_2 i) (Q2.hfix142_10_2 i) _)
      colCert_142_10_0.hD ?_).symm
  rw [alnId_142 j hj]


theorem leaf_142_10_1 (hp : 1 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 142 []).length)
    (hq : (normIsRep.getD 142 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 1 hp)
        (rowE2 (⟨142, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 1 (transLenTr ⟨10, by decide⟩ 1 hp))
        (rowE1 (⟨142, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨142, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨142, by decide⟩ (listedAt ⟨142, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 1 (transLenTr ⟨10, by decide⟩ 1 hp)) T142_10
      hfix142_10 hinj142_10 hcardT142_10
      (fun i => conj_mem_of_fixedPoints _ _ (T142_10 i) (hfix142_10 i) _)
      ⟨142, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨142, by decide⟩ (Q2.listedAt ⟨142, by decide⟩
        (alnCheck_rep ⟨142, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 1 hp) Q2.T142_10_2 Q2.hfix142_10_2 Q2.hinj142_10_2
      Q2.hcardT142_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T142_10_2 i) (Q2.hfix142_10_2 i) _)
      colCert_142_10_1.hD ?_).symm
  rw [alnId_142 j hj]


theorem leaf_142_10_2 (hp : 2 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 142 []).length)
    (hq : (normIsRep.getD 142 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 2 hp)
        (rowE2 (⟨142, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 2 (transLenTr ⟨10, by decide⟩ 2 hp))
        (rowE1 (⟨142, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨142, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨142, by decide⟩ (listedAt ⟨142, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 2 (transLenTr ⟨10, by decide⟩ 2 hp)) T142_10
      hfix142_10 hinj142_10 hcardT142_10
      (fun i => conj_mem_of_fixedPoints _ _ (T142_10 i) (hfix142_10 i) _)
      ⟨142, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨142, by decide⟩ (Q2.listedAt ⟨142, by decide⟩
        (alnCheck_rep ⟨142, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 2 hp) Q2.T142_10_2 Q2.hfix142_10_2 Q2.hinj142_10_2
      Q2.hcardT142_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T142_10_2 i) (Q2.hfix142_10_2 i) _)
      colCert_142_10_2.hD ?_).symm
  rw [alnId_142 j hj]


theorem leaf_142_10_3 (hp : 3 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 142 []).length)
    (hq : (normIsRep.getD 142 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 3 hp)
        (rowE2 (⟨142, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 3 (transLenTr ⟨10, by decide⟩ 3 hp))
        (rowE1 (⟨142, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨142, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨142, by decide⟩ (listedAt ⟨142, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 3 (transLenTr ⟨10, by decide⟩ 3 hp)) T142_10
      hfix142_10 hinj142_10 hcardT142_10
      (fun i => conj_mem_of_fixedPoints _ _ (T142_10 i) (hfix142_10 i) _)
      ⟨142, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨142, by decide⟩ (Q2.listedAt ⟨142, by decide⟩
        (alnCheck_rep ⟨142, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 3 hp) Q2.T142_10_2 Q2.hfix142_10_2 Q2.hinj142_10_2
      Q2.hcardT142_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T142_10_2 i) (Q2.hfix142_10_2 i) _)
      colCert_142_10_3.hD ?_).symm
  rw [alnId_142 j hj]


theorem leaf_142_10_4 (hp : 4 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 142 []).length)
    (hq : (normIsRep.getD 142 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 4 hp)
        (rowE2 (⟨142, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 4 (transLenTr ⟨10, by decide⟩ 4 hp))
        (rowE1 (⟨142, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨142, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨142, by decide⟩ (listedAt ⟨142, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 4 (transLenTr ⟨10, by decide⟩ 4 hp)) T142_10
      hfix142_10 hinj142_10 hcardT142_10
      (fun i => conj_mem_of_fixedPoints _ _ (T142_10 i) (hfix142_10 i) _)
      ⟨142, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨142, by decide⟩ (Q2.listedAt ⟨142, by decide⟩
        (alnCheck_rep ⟨142, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 4 hp) Q2.T142_10_2 Q2.hfix142_10_2 Q2.hinj142_10_2
      Q2.hcardT142_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T142_10_2 i) (Q2.hfix142_10_2 i) _)
      colCert_142_10_4.hD ?_).symm
  rw [alnId_142 j hj]


theorem leaf_142_11_0 (hp : 0 < (Q2.transData.getD 11 []).length)
    (j : Nat) (hj : j < (repChars.getD 142 []).length)
    (hq : (normIsRep.getD 142 []).getD j false = true) :
    species (Q2.reps (⟨11, by decide⟩ : Fin 148)) (colE2 ⟨11, by decide⟩ 0 hp)
        (rowE2 (⟨142, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨11, by decide⟩ : Fin 148))
        (colE1 ⟨11, by decide⟩ 0 (transLenTr ⟨11, by decide⟩ 0 hp))
        (rowE1 (⟨142, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨142, by decide⟩ : Fin 148) ⟨11, by decide⟩ _
      (validAt ⟨142, by decide⟩ (listedAt ⟨142, by decide⟩ hj))
      (colE1 ⟨11, by decide⟩ 0 (transLenTr ⟨11, by decide⟩ 0 hp)) T142_11
      hfix142_11 hinj142_11 hcardT142_11
      (fun i => conj_mem_of_fixedPoints _ _ (T142_11 i) (hfix142_11 i) _)
      ⟨142, by decide⟩ ⟨11, by decide⟩ _
      (Q2.validAt ⟨142, by decide⟩ (Q2.listedAt ⟨142, by decide⟩
        (alnCheck_rep ⟨142, by decide⟩ hj hq).1))
      (colE2 ⟨11, by decide⟩ 0 hp) Q2.T142_11_2 Q2.hfix142_11_2 Q2.hinj142_11_2
      Q2.hcardT142_11_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T142_11_2 i) (Q2.hfix142_11_2 i) _)
      colCert_142_11_0.hD ?_).symm
  rw [alnId_142 j hj]


theorem leaf_142_11_1 (hp : 1 < (Q2.transData.getD 11 []).length)
    (j : Nat) (hj : j < (repChars.getD 142 []).length)
    (hq : (normIsRep.getD 142 []).getD j false = true) :
    species (Q2.reps (⟨11, by decide⟩ : Fin 148)) (colE2 ⟨11, by decide⟩ 1 hp)
        (rowE2 (⟨142, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨11, by decide⟩ : Fin 148))
        (colE1 ⟨11, by decide⟩ 1 (transLenTr ⟨11, by decide⟩ 1 hp))
        (rowE1 (⟨142, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨142, by decide⟩ : Fin 148) ⟨11, by decide⟩ _
      (validAt ⟨142, by decide⟩ (listedAt ⟨142, by decide⟩ hj))
      (colE1 ⟨11, by decide⟩ 1 (transLenTr ⟨11, by decide⟩ 1 hp)) T142_11
      hfix142_11 hinj142_11 hcardT142_11
      (fun i => conj_mem_of_fixedPoints _ _ (T142_11 i) (hfix142_11 i) _)
      ⟨142, by decide⟩ ⟨11, by decide⟩ _
      (Q2.validAt ⟨142, by decide⟩ (Q2.listedAt ⟨142, by decide⟩
        (alnCheck_rep ⟨142, by decide⟩ hj hq).1))
      (colE2 ⟨11, by decide⟩ 1 hp) Q2.T142_11_2 Q2.hfix142_11_2 Q2.hinj142_11_2
      Q2.hcardT142_11_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T142_11_2 i) (Q2.hfix142_11_2 i) _)
      colCert_142_11_1.hD ?_).symm
  rw [alnId_142 j hj]


theorem leaf_142_11_2 (hp : 2 < (Q2.transData.getD 11 []).length)
    (j : Nat) (hj : j < (repChars.getD 142 []).length)
    (hq : (normIsRep.getD 142 []).getD j false = true) :
    species (Q2.reps (⟨11, by decide⟩ : Fin 148)) (colE2 ⟨11, by decide⟩ 2 hp)
        (rowE2 (⟨142, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨11, by decide⟩ : Fin 148))
        (colE1 ⟨11, by decide⟩ 2 (transLenTr ⟨11, by decide⟩ 2 hp))
        (rowE1 (⟨142, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨142, by decide⟩ : Fin 148) ⟨11, by decide⟩ _
      (validAt ⟨142, by decide⟩ (listedAt ⟨142, by decide⟩ hj))
      (colE1 ⟨11, by decide⟩ 2 (transLenTr ⟨11, by decide⟩ 2 hp)) T142_11
      hfix142_11 hinj142_11 hcardT142_11
      (fun i => conj_mem_of_fixedPoints _ _ (T142_11 i) (hfix142_11 i) _)
      ⟨142, by decide⟩ ⟨11, by decide⟩ _
      (Q2.validAt ⟨142, by decide⟩ (Q2.listedAt ⟨142, by decide⟩
        (alnCheck_rep ⟨142, by decide⟩ hj hq).1))
      (colE2 ⟨11, by decide⟩ 2 hp) Q2.T142_11_2 Q2.hfix142_11_2 Q2.hinj142_11_2
      Q2.hcardT142_11_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T142_11_2 i) (Q2.hfix142_11_2 i) _)
      colCert_142_11_2.hD ?_).symm
  rw [alnId_142 j hj]


theorem leaf_142_11_3 (hp : 3 < (Q2.transData.getD 11 []).length)
    (j : Nat) (hj : j < (repChars.getD 142 []).length)
    (hq : (normIsRep.getD 142 []).getD j false = true) :
    species (Q2.reps (⟨11, by decide⟩ : Fin 148)) (colE2 ⟨11, by decide⟩ 3 hp)
        (rowE2 (⟨142, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨11, by decide⟩ : Fin 148))
        (colE1 ⟨11, by decide⟩ 3 (transLenTr ⟨11, by decide⟩ 3 hp))
        (rowE1 (⟨142, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨142, by decide⟩ : Fin 148) ⟨11, by decide⟩ _
      (validAt ⟨142, by decide⟩ (listedAt ⟨142, by decide⟩ hj))
      (colE1 ⟨11, by decide⟩ 3 (transLenTr ⟨11, by decide⟩ 3 hp)) T142_11
      hfix142_11 hinj142_11 hcardT142_11
      (fun i => conj_mem_of_fixedPoints _ _ (T142_11 i) (hfix142_11 i) _)
      ⟨142, by decide⟩ ⟨11, by decide⟩ _
      (Q2.validAt ⟨142, by decide⟩ (Q2.listedAt ⟨142, by decide⟩
        (alnCheck_rep ⟨142, by decide⟩ hj hq).1))
      (colE2 ⟨11, by decide⟩ 3 hp) Q2.T142_11_2 Q2.hfix142_11_2 Q2.hinj142_11_2
      Q2.hcardT142_11_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T142_11_2 i) (Q2.hfix142_11_2 i) _)
      colCert_142_11_3.hD ?_).symm
  rw [alnId_142 j hj]


theorem leaf_142_11_4 (hp : 4 < (Q2.transData.getD 11 []).length)
    (j : Nat) (hj : j < (repChars.getD 142 []).length)
    (hq : (normIsRep.getD 142 []).getD j false = true) :
    species (Q2.reps (⟨11, by decide⟩ : Fin 148)) (colE2 ⟨11, by decide⟩ 4 hp)
        (rowE2 (⟨142, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨11, by decide⟩ : Fin 148))
        (colE1 ⟨11, by decide⟩ 4 (transLenTr ⟨11, by decide⟩ 4 hp))
        (rowE1 (⟨142, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨142, by decide⟩ : Fin 148) ⟨11, by decide⟩ _
      (validAt ⟨142, by decide⟩ (listedAt ⟨142, by decide⟩ hj))
      (colE1 ⟨11, by decide⟩ 4 (transLenTr ⟨11, by decide⟩ 4 hp)) T142_11
      hfix142_11 hinj142_11 hcardT142_11
      (fun i => conj_mem_of_fixedPoints _ _ (T142_11 i) (hfix142_11 i) _)
      ⟨142, by decide⟩ ⟨11, by decide⟩ _
      (Q2.validAt ⟨142, by decide⟩ (Q2.listedAt ⟨142, by decide⟩
        (alnCheck_rep ⟨142, by decide⟩ hj hq).1))
      (colE2 ⟨11, by decide⟩ 4 hp) Q2.T142_11_2 Q2.hfix142_11_2 Q2.hinj142_11_2
      Q2.hcardT142_11_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T142_11_2 i) (Q2.hfix142_11_2 i) _)
      colCert_142_11_4.hD ?_).symm
  rw [alnId_142 j hj]


theorem leaf_142_12_0 (hp : 0 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 142 []).length)
    (hq : (normIsRep.getD 142 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 0 hp)
        (rowE2 (⟨142, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp))
        (rowE1 (⟨142, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨142, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨142, by decide⟩ (listedAt ⟨142, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp)) T142_12
      hfix142_12 hinj142_12 hcardT142_12
      (fun i => conj_mem_of_fixedPoints _ _ (T142_12 i) (hfix142_12 i) _)
      ⟨142, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨142, by decide⟩ (Q2.listedAt ⟨142, by decide⟩
        (alnCheck_rep ⟨142, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 0 hp) Q2.T142_12_2 Q2.hfix142_12_2 Q2.hinj142_12_2
      Q2.hcardT142_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T142_12_2 i) (Q2.hfix142_12_2 i) _)
      colCert_142_12_0.hD ?_).symm
  rw [alnId_142 j hj]


theorem leaf_142_12_1 (hp : 1 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 142 []).length)
    (hq : (normIsRep.getD 142 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 1 hp)
        (rowE2 (⟨142, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp))
        (rowE1 (⟨142, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨142, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨142, by decide⟩ (listedAt ⟨142, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp)) T142_12
      hfix142_12 hinj142_12 hcardT142_12
      (fun i => conj_mem_of_fixedPoints _ _ (T142_12 i) (hfix142_12 i) _)
      ⟨142, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨142, by decide⟩ (Q2.listedAt ⟨142, by decide⟩
        (alnCheck_rep ⟨142, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 1 hp) Q2.T142_12_2 Q2.hfix142_12_2 Q2.hinj142_12_2
      Q2.hcardT142_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T142_12_2 i) (Q2.hfix142_12_2 i) _)
      colCert_142_12_1.hD ?_).symm
  rw [alnId_142 j hj]


theorem leaf_142_12_2 (hp : 2 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 142 []).length)
    (hq : (normIsRep.getD 142 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 2 hp)
        (rowE2 (⟨142, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp))
        (rowE1 (⟨142, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨142, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨142, by decide⟩ (listedAt ⟨142, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp)) T142_12
      hfix142_12 hinj142_12 hcardT142_12
      (fun i => conj_mem_of_fixedPoints _ _ (T142_12 i) (hfix142_12 i) _)
      ⟨142, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨142, by decide⟩ (Q2.listedAt ⟨142, by decide⟩
        (alnCheck_rep ⟨142, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 2 hp) Q2.T142_12_2 Q2.hfix142_12_2 Q2.hinj142_12_2
      Q2.hcardT142_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T142_12_2 i) (Q2.hfix142_12_2 i) _)
      colCert_142_12_2.hD ?_).symm
  rw [alnId_142 j hj]


theorem leaf_142_12_3 (hp : 3 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 142 []).length)
    (hq : (normIsRep.getD 142 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 3 hp)
        (rowE2 (⟨142, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp))
        (rowE1 (⟨142, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨142, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨142, by decide⟩ (listedAt ⟨142, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp)) T142_12
      hfix142_12 hinj142_12 hcardT142_12
      (fun i => conj_mem_of_fixedPoints _ _ (T142_12 i) (hfix142_12 i) _)
      ⟨142, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨142, by decide⟩ (Q2.listedAt ⟨142, by decide⟩
        (alnCheck_rep ⟨142, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 3 hp) Q2.T142_12_2 Q2.hfix142_12_2 Q2.hinj142_12_2
      Q2.hcardT142_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T142_12_2 i) (Q2.hfix142_12_2 i) _)
      colCert_142_12_3.hD ?_).symm
  rw [alnId_142 j hj]


theorem leaf_142_12_4 (hp : 4 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 142 []).length)
    (hq : (normIsRep.getD 142 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 4 hp)
        (rowE2 (⟨142, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp))
        (rowE1 (⟨142, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨142, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨142, by decide⟩ (listedAt ⟨142, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp)) T142_12
      hfix142_12 hinj142_12 hcardT142_12
      (fun i => conj_mem_of_fixedPoints _ _ (T142_12 i) (hfix142_12 i) _)
      ⟨142, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨142, by decide⟩ (Q2.listedAt ⟨142, by decide⟩
        (alnCheck_rep ⟨142, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 4 hp) Q2.T142_12_2 Q2.hfix142_12_2 Q2.hinj142_12_2
      Q2.hcardT142_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T142_12_2 i) (Q2.hfix142_12_2 i) _)
      colCert_142_12_4.hD ?_).symm
  rw [alnId_142 j hj]


theorem leaf_142_28_0 (hp : 0 < (Q2.transData.getD 28 []).length)
    (j : Nat) (hj : j < (repChars.getD 142 []).length)
    (hq : (normIsRep.getD 142 []).getD j false = true) :
    species (Q2.reps (⟨28, by decide⟩ : Fin 148)) (colE2 ⟨28, by decide⟩ 0 hp)
        (rowE2 (⟨142, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨28, by decide⟩ : Fin 148))
        (colE1 ⟨28, by decide⟩ 0 (transLenTr ⟨28, by decide⟩ 0 hp))
        (rowE1 (⟨142, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨142, by decide⟩ : Fin 148) ⟨28, by decide⟩ _
      (validAt ⟨142, by decide⟩ (listedAt ⟨142, by decide⟩ hj))
      (colE1 ⟨28, by decide⟩ 0 (transLenTr ⟨28, by decide⟩ 0 hp)) T142_28
      hfix142_28 hinj142_28 hcardT142_28
      (fun i => conj_mem_of_fixedPoints _ _ (T142_28 i) (hfix142_28 i) _)
      ⟨142, by decide⟩ ⟨28, by decide⟩ _
      (Q2.validAt ⟨142, by decide⟩ (Q2.listedAt ⟨142, by decide⟩
        (alnCheck_rep ⟨142, by decide⟩ hj hq).1))
      (colE2 ⟨28, by decide⟩ 0 hp) Q2.T142_28_2 Q2.hfix142_28_2 Q2.hinj142_28_2
      Q2.hcardT142_28_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T142_28_2 i) (Q2.hfix142_28_2 i) _)
      colCert_142_28_0.hD ?_).symm
  rw [alnId_142 j hj]


theorem leaf_142_28_1 (hp : 1 < (Q2.transData.getD 28 []).length)
    (j : Nat) (hj : j < (repChars.getD 142 []).length)
    (hq : (normIsRep.getD 142 []).getD j false = true) :
    species (Q2.reps (⟨28, by decide⟩ : Fin 148)) (colE2 ⟨28, by decide⟩ 1 hp)
        (rowE2 (⟨142, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨28, by decide⟩ : Fin 148))
        (colE1 ⟨28, by decide⟩ 1 (transLenTr ⟨28, by decide⟩ 1 hp))
        (rowE1 (⟨142, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨142, by decide⟩ : Fin 148) ⟨28, by decide⟩ _
      (validAt ⟨142, by decide⟩ (listedAt ⟨142, by decide⟩ hj))
      (colE1 ⟨28, by decide⟩ 1 (transLenTr ⟨28, by decide⟩ 1 hp)) T142_28
      hfix142_28 hinj142_28 hcardT142_28
      (fun i => conj_mem_of_fixedPoints _ _ (T142_28 i) (hfix142_28 i) _)
      ⟨142, by decide⟩ ⟨28, by decide⟩ _
      (Q2.validAt ⟨142, by decide⟩ (Q2.listedAt ⟨142, by decide⟩
        (alnCheck_rep ⟨142, by decide⟩ hj hq).1))
      (colE2 ⟨28, by decide⟩ 1 hp) Q2.T142_28_2 Q2.hfix142_28_2 Q2.hinj142_28_2
      Q2.hcardT142_28_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T142_28_2 i) (Q2.hfix142_28_2 i) _)
      colCert_142_28_1.hD ?_).symm
  rw [alnId_142 j hj]


theorem leaf_142_28_2 (hp : 2 < (Q2.transData.getD 28 []).length)
    (j : Nat) (hj : j < (repChars.getD 142 []).length)
    (hq : (normIsRep.getD 142 []).getD j false = true) :
    species (Q2.reps (⟨28, by decide⟩ : Fin 148)) (colE2 ⟨28, by decide⟩ 2 hp)
        (rowE2 (⟨142, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨28, by decide⟩ : Fin 148))
        (colE1 ⟨28, by decide⟩ 2 (transLenTr ⟨28, by decide⟩ 2 hp))
        (rowE1 (⟨142, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨142, by decide⟩ : Fin 148) ⟨28, by decide⟩ _
      (validAt ⟨142, by decide⟩ (listedAt ⟨142, by decide⟩ hj))
      (colE1 ⟨28, by decide⟩ 2 (transLenTr ⟨28, by decide⟩ 2 hp)) T142_28
      hfix142_28 hinj142_28 hcardT142_28
      (fun i => conj_mem_of_fixedPoints _ _ (T142_28 i) (hfix142_28 i) _)
      ⟨142, by decide⟩ ⟨28, by decide⟩ _
      (Q2.validAt ⟨142, by decide⟩ (Q2.listedAt ⟨142, by decide⟩
        (alnCheck_rep ⟨142, by decide⟩ hj hq).1))
      (colE2 ⟨28, by decide⟩ 2 hp) Q2.T142_28_2 Q2.hfix142_28_2 Q2.hinj142_28_2
      Q2.hcardT142_28_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T142_28_2 i) (Q2.hfix142_28_2 i) _)
      colCert_142_28_2.hD ?_).symm
  rw [alnId_142 j hj]


theorem leaf_142_28_3 (hp : 3 < (Q2.transData.getD 28 []).length)
    (j : Nat) (hj : j < (repChars.getD 142 []).length)
    (hq : (normIsRep.getD 142 []).getD j false = true) :
    species (Q2.reps (⟨28, by decide⟩ : Fin 148)) (colE2 ⟨28, by decide⟩ 3 hp)
        (rowE2 (⟨142, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨28, by decide⟩ : Fin 148))
        (colE1 ⟨28, by decide⟩ 3 (transLenTr ⟨28, by decide⟩ 3 hp))
        (rowE1 (⟨142, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨142, by decide⟩ : Fin 148) ⟨28, by decide⟩ _
      (validAt ⟨142, by decide⟩ (listedAt ⟨142, by decide⟩ hj))
      (colE1 ⟨28, by decide⟩ 3 (transLenTr ⟨28, by decide⟩ 3 hp)) T142_28
      hfix142_28 hinj142_28 hcardT142_28
      (fun i => conj_mem_of_fixedPoints _ _ (T142_28 i) (hfix142_28 i) _)
      ⟨142, by decide⟩ ⟨28, by decide⟩ _
      (Q2.validAt ⟨142, by decide⟩ (Q2.listedAt ⟨142, by decide⟩
        (alnCheck_rep ⟨142, by decide⟩ hj hq).1))
      (colE2 ⟨28, by decide⟩ 3 hp) Q2.T142_28_2 Q2.hfix142_28_2 Q2.hinj142_28_2
      Q2.hcardT142_28_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T142_28_2 i) (Q2.hfix142_28_2 i) _)
      colCert_142_28_3.hD ?_).symm
  rw [alnId_142 j hj]


theorem leaf_142_28_4 (hp : 4 < (Q2.transData.getD 28 []).length)
    (j : Nat) (hj : j < (repChars.getD 142 []).length)
    (hq : (normIsRep.getD 142 []).getD j false = true) :
    species (Q2.reps (⟨28, by decide⟩ : Fin 148)) (colE2 ⟨28, by decide⟩ 4 hp)
        (rowE2 (⟨142, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨28, by decide⟩ : Fin 148))
        (colE1 ⟨28, by decide⟩ 4 (transLenTr ⟨28, by decide⟩ 4 hp))
        (rowE1 (⟨142, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨142, by decide⟩ : Fin 148) ⟨28, by decide⟩ _
      (validAt ⟨142, by decide⟩ (listedAt ⟨142, by decide⟩ hj))
      (colE1 ⟨28, by decide⟩ 4 (transLenTr ⟨28, by decide⟩ 4 hp)) T142_28
      hfix142_28 hinj142_28 hcardT142_28
      (fun i => conj_mem_of_fixedPoints _ _ (T142_28 i) (hfix142_28 i) _)
      ⟨142, by decide⟩ ⟨28, by decide⟩ _
      (Q2.validAt ⟨142, by decide⟩ (Q2.listedAt ⟨142, by decide⟩
        (alnCheck_rep ⟨142, by decide⟩ hj hq).1))
      (colE2 ⟨28, by decide⟩ 4 hp) Q2.T142_28_2 Q2.hfix142_28_2 Q2.hinj142_28_2
      Q2.hcardT142_28_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T142_28_2 i) (Q2.hfix142_28_2 i) _)
      colCert_142_28_4.hD ?_).symm
  rw [alnId_142 j hj]


theorem leaf_142_28_5 (hp : 5 < (Q2.transData.getD 28 []).length)
    (j : Nat) (hj : j < (repChars.getD 142 []).length)
    (hq : (normIsRep.getD 142 []).getD j false = true) :
    species (Q2.reps (⟨28, by decide⟩ : Fin 148)) (colE2 ⟨28, by decide⟩ 5 hp)
        (rowE2 (⟨142, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨28, by decide⟩ : Fin 148))
        (colE1 ⟨28, by decide⟩ 5 (transLenTr ⟨28, by decide⟩ 5 hp))
        (rowE1 (⟨142, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨142, by decide⟩ : Fin 148) ⟨28, by decide⟩ _
      (validAt ⟨142, by decide⟩ (listedAt ⟨142, by decide⟩ hj))
      (colE1 ⟨28, by decide⟩ 5 (transLenTr ⟨28, by decide⟩ 5 hp)) T142_28
      hfix142_28 hinj142_28 hcardT142_28
      (fun i => conj_mem_of_fixedPoints _ _ (T142_28 i) (hfix142_28 i) _)
      ⟨142, by decide⟩ ⟨28, by decide⟩ _
      (Q2.validAt ⟨142, by decide⟩ (Q2.listedAt ⟨142, by decide⟩
        (alnCheck_rep ⟨142, by decide⟩ hj hq).1))
      (colE2 ⟨28, by decide⟩ 5 hp) Q2.T142_28_2 Q2.hfix142_28_2 Q2.hinj142_28_2
      Q2.hcardT142_28_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T142_28_2 i) (Q2.hfix142_28_2 i) _)
      colCert_142_28_5.hD ?_).symm
  rw [alnId_142 j hj]


theorem leaf_142_28_10 (hp : 10 < (Q2.transData.getD 28 []).length)
    (j : Nat) (hj : j < (repChars.getD 142 []).length)
    (hq : (normIsRep.getD 142 []).getD j false = true) :
    species (Q2.reps (⟨28, by decide⟩ : Fin 148)) (colE2 ⟨28, by decide⟩ 10 hp)
        (rowE2 (⟨142, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨28, by decide⟩ : Fin 148))
        (colE1 ⟨28, by decide⟩ 10 (transLenTr ⟨28, by decide⟩ 10 hp))
        (rowE1 (⟨142, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨142, by decide⟩ : Fin 148) ⟨28, by decide⟩ _
      (validAt ⟨142, by decide⟩ (listedAt ⟨142, by decide⟩ hj))
      (colE1 ⟨28, by decide⟩ 10 (transLenTr ⟨28, by decide⟩ 10 hp)) T142_28
      hfix142_28 hinj142_28 hcardT142_28
      (fun i => conj_mem_of_fixedPoints _ _ (T142_28 i) (hfix142_28 i) _)
      ⟨142, by decide⟩ ⟨28, by decide⟩ _
      (Q2.validAt ⟨142, by decide⟩ (Q2.listedAt ⟨142, by decide⟩
        (alnCheck_rep ⟨142, by decide⟩ hj hq).1))
      (colE2 ⟨28, by decide⟩ 10 hp) Q2.T142_28_2 Q2.hfix142_28_2 Q2.hinj142_28_2
      Q2.hcardT142_28_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T142_28_2 i) (Q2.hfix142_28_2 i) _)
      colCert_142_28_10.hD ?_).symm
  rw [alnId_142 j hj]


theorem leaf_142_28_15 (hp : 15 < (Q2.transData.getD 28 []).length)
    (j : Nat) (hj : j < (repChars.getD 142 []).length)
    (hq : (normIsRep.getD 142 []).getD j false = true) :
    species (Q2.reps (⟨28, by decide⟩ : Fin 148)) (colE2 ⟨28, by decide⟩ 15 hp)
        (rowE2 (⟨142, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨28, by decide⟩ : Fin 148))
        (colE1 ⟨28, by decide⟩ 15 (transLenTr ⟨28, by decide⟩ 15 hp))
        (rowE1 (⟨142, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨142, by decide⟩ : Fin 148) ⟨28, by decide⟩ _
      (validAt ⟨142, by decide⟩ (listedAt ⟨142, by decide⟩ hj))
      (colE1 ⟨28, by decide⟩ 15 (transLenTr ⟨28, by decide⟩ 15 hp)) T142_28
      hfix142_28 hinj142_28 hcardT142_28
      (fun i => conj_mem_of_fixedPoints _ _ (T142_28 i) (hfix142_28 i) _)
      ⟨142, by decide⟩ ⟨28, by decide⟩ _
      (Q2.validAt ⟨142, by decide⟩ (Q2.listedAt ⟨142, by decide⟩
        (alnCheck_rep ⟨142, by decide⟩ hj hq).1))
      (colE2 ⟨28, by decide⟩ 15 hp) Q2.T142_28_2 Q2.hfix142_28_2 Q2.hinj142_28_2
      Q2.hcardT142_28_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T142_28_2 i) (Q2.hfix142_28_2 i) _)
      colCert_142_28_15.hD ?_).symm
  rw [alnId_142 j hj]


theorem leaf_142_28_20 (hp : 20 < (Q2.transData.getD 28 []).length)
    (j : Nat) (hj : j < (repChars.getD 142 []).length)
    (hq : (normIsRep.getD 142 []).getD j false = true) :
    species (Q2.reps (⟨28, by decide⟩ : Fin 148)) (colE2 ⟨28, by decide⟩ 20 hp)
        (rowE2 (⟨142, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨28, by decide⟩ : Fin 148))
        (colE1 ⟨28, by decide⟩ 20 (transLenTr ⟨28, by decide⟩ 20 hp))
        (rowE1 (⟨142, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨142, by decide⟩ : Fin 148) ⟨28, by decide⟩ _
      (validAt ⟨142, by decide⟩ (listedAt ⟨142, by decide⟩ hj))
      (colE1 ⟨28, by decide⟩ 20 (transLenTr ⟨28, by decide⟩ 20 hp)) T142_28
      hfix142_28 hinj142_28 hcardT142_28
      (fun i => conj_mem_of_fixedPoints _ _ (T142_28 i) (hfix142_28 i) _)
      ⟨142, by decide⟩ ⟨28, by decide⟩ _
      (Q2.validAt ⟨142, by decide⟩ (Q2.listedAt ⟨142, by decide⟩
        (alnCheck_rep ⟨142, by decide⟩ hj hq).1))
      (colE2 ⟨28, by decide⟩ 20 hp) Q2.T142_28_2 Q2.hfix142_28_2 Q2.hinj142_28_2
      Q2.hcardT142_28_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T142_28_2 i) (Q2.hfix142_28_2 i) _)
      colCert_142_28_20.hD ?_).symm
  rw [alnId_142 j hj]


theorem leaf_142_29_0 (hp : 0 < (Q2.transData.getD 29 []).length)
    (j : Nat) (hj : j < (repChars.getD 142 []).length)
    (hq : (normIsRep.getD 142 []).getD j false = true) :
    species (Q2.reps (⟨29, by decide⟩ : Fin 148)) (colE2 ⟨29, by decide⟩ 0 hp)
        (rowE2 (⟨142, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨29, by decide⟩ : Fin 148))
        (colE1 ⟨29, by decide⟩ 0 (transLenTr ⟨29, by decide⟩ 0 hp))
        (rowE1 (⟨142, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨142, by decide⟩ : Fin 148) ⟨29, by decide⟩ _
      (validAt ⟨142, by decide⟩ (listedAt ⟨142, by decide⟩ hj))
      (colE1 ⟨29, by decide⟩ 0 (transLenTr ⟨29, by decide⟩ 0 hp)) T142_29
      hfix142_29 hinj142_29 hcardT142_29
      (fun i => conj_mem_of_fixedPoints _ _ (T142_29 i) (hfix142_29 i) _)
      ⟨142, by decide⟩ ⟨29, by decide⟩ _
      (Q2.validAt ⟨142, by decide⟩ (Q2.listedAt ⟨142, by decide⟩
        (alnCheck_rep ⟨142, by decide⟩ hj hq).1))
      (colE2 ⟨29, by decide⟩ 0 hp) Q2.T142_29_2 Q2.hfix142_29_2 Q2.hinj142_29_2
      Q2.hcardT142_29_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T142_29_2 i) (Q2.hfix142_29_2 i) _)
      colCert_142_29_0.hD ?_).symm
  rw [alnId_142 j hj]


theorem leaf_142_29_1 (hp : 1 < (Q2.transData.getD 29 []).length)
    (j : Nat) (hj : j < (repChars.getD 142 []).length)
    (hq : (normIsRep.getD 142 []).getD j false = true) :
    species (Q2.reps (⟨29, by decide⟩ : Fin 148)) (colE2 ⟨29, by decide⟩ 1 hp)
        (rowE2 (⟨142, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨29, by decide⟩ : Fin 148))
        (colE1 ⟨29, by decide⟩ 1 (transLenTr ⟨29, by decide⟩ 1 hp))
        (rowE1 (⟨142, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨142, by decide⟩ : Fin 148) ⟨29, by decide⟩ _
      (validAt ⟨142, by decide⟩ (listedAt ⟨142, by decide⟩ hj))
      (colE1 ⟨29, by decide⟩ 1 (transLenTr ⟨29, by decide⟩ 1 hp)) T142_29
      hfix142_29 hinj142_29 hcardT142_29
      (fun i => conj_mem_of_fixedPoints _ _ (T142_29 i) (hfix142_29 i) _)
      ⟨142, by decide⟩ ⟨29, by decide⟩ _
      (Q2.validAt ⟨142, by decide⟩ (Q2.listedAt ⟨142, by decide⟩
        (alnCheck_rep ⟨142, by decide⟩ hj hq).1))
      (colE2 ⟨29, by decide⟩ 1 hp) Q2.T142_29_2 Q2.hfix142_29_2 Q2.hinj142_29_2
      Q2.hcardT142_29_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T142_29_2 i) (Q2.hfix142_29_2 i) _)
      colCert_142_29_1.hD ?_).symm
  rw [alnId_142 j hj]


theorem leaf_142_29_2 (hp : 2 < (Q2.transData.getD 29 []).length)
    (j : Nat) (hj : j < (repChars.getD 142 []).length)
    (hq : (normIsRep.getD 142 []).getD j false = true) :
    species (Q2.reps (⟨29, by decide⟩ : Fin 148)) (colE2 ⟨29, by decide⟩ 2 hp)
        (rowE2 (⟨142, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨29, by decide⟩ : Fin 148))
        (colE1 ⟨29, by decide⟩ 2 (transLenTr ⟨29, by decide⟩ 2 hp))
        (rowE1 (⟨142, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨142, by decide⟩ : Fin 148) ⟨29, by decide⟩ _
      (validAt ⟨142, by decide⟩ (listedAt ⟨142, by decide⟩ hj))
      (colE1 ⟨29, by decide⟩ 2 (transLenTr ⟨29, by decide⟩ 2 hp)) T142_29
      hfix142_29 hinj142_29 hcardT142_29
      (fun i => conj_mem_of_fixedPoints _ _ (T142_29 i) (hfix142_29 i) _)
      ⟨142, by decide⟩ ⟨29, by decide⟩ _
      (Q2.validAt ⟨142, by decide⟩ (Q2.listedAt ⟨142, by decide⟩
        (alnCheck_rep ⟨142, by decide⟩ hj hq).1))
      (colE2 ⟨29, by decide⟩ 2 hp) Q2.T142_29_2 Q2.hfix142_29_2 Q2.hinj142_29_2
      Q2.hcardT142_29_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T142_29_2 i) (Q2.hfix142_29_2 i) _)
      colCert_142_29_2.hD ?_).symm
  rw [alnId_142 j hj]


theorem leaf_142_29_3 (hp : 3 < (Q2.transData.getD 29 []).length)
    (j : Nat) (hj : j < (repChars.getD 142 []).length)
    (hq : (normIsRep.getD 142 []).getD j false = true) :
    species (Q2.reps (⟨29, by decide⟩ : Fin 148)) (colE2 ⟨29, by decide⟩ 3 hp)
        (rowE2 (⟨142, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨29, by decide⟩ : Fin 148))
        (colE1 ⟨29, by decide⟩ 3 (transLenTr ⟨29, by decide⟩ 3 hp))
        (rowE1 (⟨142, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨142, by decide⟩ : Fin 148) ⟨29, by decide⟩ _
      (validAt ⟨142, by decide⟩ (listedAt ⟨142, by decide⟩ hj))
      (colE1 ⟨29, by decide⟩ 3 (transLenTr ⟨29, by decide⟩ 3 hp)) T142_29
      hfix142_29 hinj142_29 hcardT142_29
      (fun i => conj_mem_of_fixedPoints _ _ (T142_29 i) (hfix142_29 i) _)
      ⟨142, by decide⟩ ⟨29, by decide⟩ _
      (Q2.validAt ⟨142, by decide⟩ (Q2.listedAt ⟨142, by decide⟩
        (alnCheck_rep ⟨142, by decide⟩ hj hq).1))
      (colE2 ⟨29, by decide⟩ 3 hp) Q2.T142_29_2 Q2.hfix142_29_2 Q2.hinj142_29_2
      Q2.hcardT142_29_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T142_29_2 i) (Q2.hfix142_29_2 i) _)
      colCert_142_29_3.hD ?_).symm
  rw [alnId_142 j hj]


theorem leaf_142_29_4 (hp : 4 < (Q2.transData.getD 29 []).length)
    (j : Nat) (hj : j < (repChars.getD 142 []).length)
    (hq : (normIsRep.getD 142 []).getD j false = true) :
    species (Q2.reps (⟨29, by decide⟩ : Fin 148)) (colE2 ⟨29, by decide⟩ 4 hp)
        (rowE2 (⟨142, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨29, by decide⟩ : Fin 148))
        (colE1 ⟨29, by decide⟩ 4 (transLenTr ⟨29, by decide⟩ 4 hp))
        (rowE1 (⟨142, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨142, by decide⟩ : Fin 148) ⟨29, by decide⟩ _
      (validAt ⟨142, by decide⟩ (listedAt ⟨142, by decide⟩ hj))
      (colE1 ⟨29, by decide⟩ 4 (transLenTr ⟨29, by decide⟩ 4 hp)) T142_29
      hfix142_29 hinj142_29 hcardT142_29
      (fun i => conj_mem_of_fixedPoints _ _ (T142_29 i) (hfix142_29 i) _)
      ⟨142, by decide⟩ ⟨29, by decide⟩ _
      (Q2.validAt ⟨142, by decide⟩ (Q2.listedAt ⟨142, by decide⟩
        (alnCheck_rep ⟨142, by decide⟩ hj hq).1))
      (colE2 ⟨29, by decide⟩ 4 hp) Q2.T142_29_2 Q2.hfix142_29_2 Q2.hinj142_29_2
      Q2.hcardT142_29_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T142_29_2 i) (Q2.hfix142_29_2 i) _)
      colCert_142_29_4.hD ?_).symm
  rw [alnId_142 j hj]


theorem leaf_142_29_5 (hp : 5 < (Q2.transData.getD 29 []).length)
    (j : Nat) (hj : j < (repChars.getD 142 []).length)
    (hq : (normIsRep.getD 142 []).getD j false = true) :
    species (Q2.reps (⟨29, by decide⟩ : Fin 148)) (colE2 ⟨29, by decide⟩ 5 hp)
        (rowE2 (⟨142, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨29, by decide⟩ : Fin 148))
        (colE1 ⟨29, by decide⟩ 5 (transLenTr ⟨29, by decide⟩ 5 hp))
        (rowE1 (⟨142, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨142, by decide⟩ : Fin 148) ⟨29, by decide⟩ _
      (validAt ⟨142, by decide⟩ (listedAt ⟨142, by decide⟩ hj))
      (colE1 ⟨29, by decide⟩ 5 (transLenTr ⟨29, by decide⟩ 5 hp)) T142_29
      hfix142_29 hinj142_29 hcardT142_29
      (fun i => conj_mem_of_fixedPoints _ _ (T142_29 i) (hfix142_29 i) _)
      ⟨142, by decide⟩ ⟨29, by decide⟩ _
      (Q2.validAt ⟨142, by decide⟩ (Q2.listedAt ⟨142, by decide⟩
        (alnCheck_rep ⟨142, by decide⟩ hj hq).1))
      (colE2 ⟨29, by decide⟩ 5 hp) Q2.T142_29_2 Q2.hfix142_29_2 Q2.hinj142_29_2
      Q2.hcardT142_29_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T142_29_2 i) (Q2.hfix142_29_2 i) _)
      ?_).symm
  rw [show colData1 (⟨142, by decide⟩ : Fin 148)
        ((colE1 ⟨29, by decide⟩ 5 (transLenTr ⟨29, by decide⟩ 5 hp) : ↥(reps ⟨29, by decide⟩)) : Coordinate 1)
        T142_29 = colFn colCertDiv_142_29_5.D1 (m := 5) from colCertDiv_142_29_5.bind1,
    show colData2 (⟨142, by decide⟩ : Fin 148)
        ((colE2 ⟨29, by decide⟩ 5 hp : ↥(Q2.reps ⟨29, by decide⟩)) : Coordinate 2)
        Q2.T142_29_2 = colFn colCertDiv_142_29_5.D2 (m := 5) from colCertDiv_142_29_5.bind2]
  rw [alnId_142 j hj]
  exact fastcode_of_div ⟨142, by decide⟩ _ _ _
    ((alnId_142 j hj) ▸ Q2.listedAt (⟨142, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨142, by decide⟩ : Fin 148) hj hq).1) colCertDiv_142_29_5_match


theorem leaf_142_29_10 (hp : 10 < (Q2.transData.getD 29 []).length)
    (j : Nat) (hj : j < (repChars.getD 142 []).length)
    (hq : (normIsRep.getD 142 []).getD j false = true) :
    species (Q2.reps (⟨29, by decide⟩ : Fin 148)) (colE2 ⟨29, by decide⟩ 10 hp)
        (rowE2 (⟨142, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨29, by decide⟩ : Fin 148))
        (colE1 ⟨29, by decide⟩ 10 (transLenTr ⟨29, by decide⟩ 10 hp))
        (rowE1 (⟨142, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨142, by decide⟩ : Fin 148) ⟨29, by decide⟩ _
      (validAt ⟨142, by decide⟩ (listedAt ⟨142, by decide⟩ hj))
      (colE1 ⟨29, by decide⟩ 10 (transLenTr ⟨29, by decide⟩ 10 hp)) T142_29
      hfix142_29 hinj142_29 hcardT142_29
      (fun i => conj_mem_of_fixedPoints _ _ (T142_29 i) (hfix142_29 i) _)
      ⟨142, by decide⟩ ⟨29, by decide⟩ _
      (Q2.validAt ⟨142, by decide⟩ (Q2.listedAt ⟨142, by decide⟩
        (alnCheck_rep ⟨142, by decide⟩ hj hq).1))
      (colE2 ⟨29, by decide⟩ 10 hp) Q2.T142_29_2 Q2.hfix142_29_2 Q2.hinj142_29_2
      Q2.hcardT142_29_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T142_29_2 i) (Q2.hfix142_29_2 i) _)
      ?_).symm
  rw [show colData1 (⟨142, by decide⟩ : Fin 148)
        ((colE1 ⟨29, by decide⟩ 10 (transLenTr ⟨29, by decide⟩ 10 hp) : ↥(reps ⟨29, by decide⟩)) : Coordinate 1)
        T142_29 = colFn colCertDiv_142_29_10.D1 (m := 5) from colCertDiv_142_29_10.bind1,
    show colData2 (⟨142, by decide⟩ : Fin 148)
        ((colE2 ⟨29, by decide⟩ 10 hp : ↥(Q2.reps ⟨29, by decide⟩)) : Coordinate 2)
        Q2.T142_29_2 = colFn colCertDiv_142_29_10.D2 (m := 5) from colCertDiv_142_29_10.bind2]
  rw [alnId_142 j hj]
  exact fastcode_of_div ⟨142, by decide⟩ _ _ _
    ((alnId_142 j hj) ▸ Q2.listedAt (⟨142, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨142, by decide⟩ : Fin 148) hj hq).1) colCertDiv_142_29_10_match


theorem leaf_142_29_15 (hp : 15 < (Q2.transData.getD 29 []).length)
    (j : Nat) (hj : j < (repChars.getD 142 []).length)
    (hq : (normIsRep.getD 142 []).getD j false = true) :
    species (Q2.reps (⟨29, by decide⟩ : Fin 148)) (colE2 ⟨29, by decide⟩ 15 hp)
        (rowE2 (⟨142, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨29, by decide⟩ : Fin 148))
        (colE1 ⟨29, by decide⟩ 15 (transLenTr ⟨29, by decide⟩ 15 hp))
        (rowE1 (⟨142, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨142, by decide⟩ : Fin 148) ⟨29, by decide⟩ _
      (validAt ⟨142, by decide⟩ (listedAt ⟨142, by decide⟩ hj))
      (colE1 ⟨29, by decide⟩ 15 (transLenTr ⟨29, by decide⟩ 15 hp)) T142_29
      hfix142_29 hinj142_29 hcardT142_29
      (fun i => conj_mem_of_fixedPoints _ _ (T142_29 i) (hfix142_29 i) _)
      ⟨142, by decide⟩ ⟨29, by decide⟩ _
      (Q2.validAt ⟨142, by decide⟩ (Q2.listedAt ⟨142, by decide⟩
        (alnCheck_rep ⟨142, by decide⟩ hj hq).1))
      (colE2 ⟨29, by decide⟩ 15 hp) Q2.T142_29_2 Q2.hfix142_29_2 Q2.hinj142_29_2
      Q2.hcardT142_29_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T142_29_2 i) (Q2.hfix142_29_2 i) _)
      ?_).symm
  rw [show colData1 (⟨142, by decide⟩ : Fin 148)
        ((colE1 ⟨29, by decide⟩ 15 (transLenTr ⟨29, by decide⟩ 15 hp) : ↥(reps ⟨29, by decide⟩)) : Coordinate 1)
        T142_29 = colFn colCertDiv_142_29_15.D1 (m := 5) from colCertDiv_142_29_15.bind1,
    show colData2 (⟨142, by decide⟩ : Fin 148)
        ((colE2 ⟨29, by decide⟩ 15 hp : ↥(Q2.reps ⟨29, by decide⟩)) : Coordinate 2)
        Q2.T142_29_2 = colFn colCertDiv_142_29_15.D2 (m := 5) from colCertDiv_142_29_15.bind2]
  rw [alnId_142 j hj]
  exact fastcode_of_div ⟨142, by decide⟩ _ _ _
    ((alnId_142 j hj) ▸ Q2.listedAt (⟨142, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨142, by decide⟩ : Fin 148) hj hq).1) colCertDiv_142_29_15_match


theorem leaf_142_29_20 (hp : 20 < (Q2.transData.getD 29 []).length)
    (j : Nat) (hj : j < (repChars.getD 142 []).length)
    (hq : (normIsRep.getD 142 []).getD j false = true) :
    species (Q2.reps (⟨29, by decide⟩ : Fin 148)) (colE2 ⟨29, by decide⟩ 20 hp)
        (rowE2 (⟨142, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨29, by decide⟩ : Fin 148))
        (colE1 ⟨29, by decide⟩ 20 (transLenTr ⟨29, by decide⟩ 20 hp))
        (rowE1 (⟨142, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨142, by decide⟩ : Fin 148) ⟨29, by decide⟩ _
      (validAt ⟨142, by decide⟩ (listedAt ⟨142, by decide⟩ hj))
      (colE1 ⟨29, by decide⟩ 20 (transLenTr ⟨29, by decide⟩ 20 hp)) T142_29
      hfix142_29 hinj142_29 hcardT142_29
      (fun i => conj_mem_of_fixedPoints _ _ (T142_29 i) (hfix142_29 i) _)
      ⟨142, by decide⟩ ⟨29, by decide⟩ _
      (Q2.validAt ⟨142, by decide⟩ (Q2.listedAt ⟨142, by decide⟩
        (alnCheck_rep ⟨142, by decide⟩ hj hq).1))
      (colE2 ⟨29, by decide⟩ 20 hp) Q2.T142_29_2 Q2.hfix142_29_2 Q2.hinj142_29_2
      Q2.hcardT142_29_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T142_29_2 i) (Q2.hfix142_29_2 i) _)
      colCert_142_29_20.hD ?_).symm
  rw [alnId_142 j hj]


theorem leaf_142_30_0 (hp : 0 < (Q2.transData.getD 30 []).length)
    (j : Nat) (hj : j < (repChars.getD 142 []).length)
    (hq : (normIsRep.getD 142 []).getD j false = true) :
    species (Q2.reps (⟨30, by decide⟩ : Fin 148)) (colE2 ⟨30, by decide⟩ 0 hp)
        (rowE2 (⟨142, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨30, by decide⟩ : Fin 148))
        (colE1 ⟨30, by decide⟩ 0 (transLenTr ⟨30, by decide⟩ 0 hp))
        (rowE1 (⟨142, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨142, by decide⟩ : Fin 148) ⟨30, by decide⟩ _
      (validAt ⟨142, by decide⟩ (listedAt ⟨142, by decide⟩ hj))
      (colE1 ⟨30, by decide⟩ 0 (transLenTr ⟨30, by decide⟩ 0 hp)) T142_30
      hfix142_30 hinj142_30 hcardT142_30
      (fun i => conj_mem_of_fixedPoints _ _ (T142_30 i) (hfix142_30 i) _)
      ⟨142, by decide⟩ ⟨30, by decide⟩ _
      (Q2.validAt ⟨142, by decide⟩ (Q2.listedAt ⟨142, by decide⟩
        (alnCheck_rep ⟨142, by decide⟩ hj hq).1))
      (colE2 ⟨30, by decide⟩ 0 hp) Q2.T142_30_2 Q2.hfix142_30_2 Q2.hinj142_30_2
      Q2.hcardT142_30_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T142_30_2 i) (Q2.hfix142_30_2 i) _)
      colCert_142_30_0.hD ?_).symm
  rw [alnId_142 j hj]


theorem leaf_142_30_1 (hp : 1 < (Q2.transData.getD 30 []).length)
    (j : Nat) (hj : j < (repChars.getD 142 []).length)
    (hq : (normIsRep.getD 142 []).getD j false = true) :
    species (Q2.reps (⟨30, by decide⟩ : Fin 148)) (colE2 ⟨30, by decide⟩ 1 hp)
        (rowE2 (⟨142, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨30, by decide⟩ : Fin 148))
        (colE1 ⟨30, by decide⟩ 1 (transLenTr ⟨30, by decide⟩ 1 hp))
        (rowE1 (⟨142, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨142, by decide⟩ : Fin 148) ⟨30, by decide⟩ _
      (validAt ⟨142, by decide⟩ (listedAt ⟨142, by decide⟩ hj))
      (colE1 ⟨30, by decide⟩ 1 (transLenTr ⟨30, by decide⟩ 1 hp)) T142_30
      hfix142_30 hinj142_30 hcardT142_30
      (fun i => conj_mem_of_fixedPoints _ _ (T142_30 i) (hfix142_30 i) _)
      ⟨142, by decide⟩ ⟨30, by decide⟩ _
      (Q2.validAt ⟨142, by decide⟩ (Q2.listedAt ⟨142, by decide⟩
        (alnCheck_rep ⟨142, by decide⟩ hj hq).1))
      (colE2 ⟨30, by decide⟩ 1 hp) Q2.T142_30_2 Q2.hfix142_30_2 Q2.hinj142_30_2
      Q2.hcardT142_30_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T142_30_2 i) (Q2.hfix142_30_2 i) _)
      colCert_142_30_1.hD ?_).symm
  rw [alnId_142 j hj]


theorem leaf_142_30_2 (hp : 2 < (Q2.transData.getD 30 []).length)
    (j : Nat) (hj : j < (repChars.getD 142 []).length)
    (hq : (normIsRep.getD 142 []).getD j false = true) :
    species (Q2.reps (⟨30, by decide⟩ : Fin 148)) (colE2 ⟨30, by decide⟩ 2 hp)
        (rowE2 (⟨142, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨30, by decide⟩ : Fin 148))
        (colE1 ⟨30, by decide⟩ 2 (transLenTr ⟨30, by decide⟩ 2 hp))
        (rowE1 (⟨142, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨142, by decide⟩ : Fin 148) ⟨30, by decide⟩ _
      (validAt ⟨142, by decide⟩ (listedAt ⟨142, by decide⟩ hj))
      (colE1 ⟨30, by decide⟩ 2 (transLenTr ⟨30, by decide⟩ 2 hp)) T142_30
      hfix142_30 hinj142_30 hcardT142_30
      (fun i => conj_mem_of_fixedPoints _ _ (T142_30 i) (hfix142_30 i) _)
      ⟨142, by decide⟩ ⟨30, by decide⟩ _
      (Q2.validAt ⟨142, by decide⟩ (Q2.listedAt ⟨142, by decide⟩
        (alnCheck_rep ⟨142, by decide⟩ hj hq).1))
      (colE2 ⟨30, by decide⟩ 2 hp) Q2.T142_30_2 Q2.hfix142_30_2 Q2.hinj142_30_2
      Q2.hcardT142_30_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T142_30_2 i) (Q2.hfix142_30_2 i) _)
      colCert_142_30_2.hD ?_).symm
  rw [alnId_142 j hj]


theorem leaf_142_30_3 (hp : 3 < (Q2.transData.getD 30 []).length)
    (j : Nat) (hj : j < (repChars.getD 142 []).length)
    (hq : (normIsRep.getD 142 []).getD j false = true) :
    species (Q2.reps (⟨30, by decide⟩ : Fin 148)) (colE2 ⟨30, by decide⟩ 3 hp)
        (rowE2 (⟨142, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨30, by decide⟩ : Fin 148))
        (colE1 ⟨30, by decide⟩ 3 (transLenTr ⟨30, by decide⟩ 3 hp))
        (rowE1 (⟨142, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨142, by decide⟩ : Fin 148) ⟨30, by decide⟩ _
      (validAt ⟨142, by decide⟩ (listedAt ⟨142, by decide⟩ hj))
      (colE1 ⟨30, by decide⟩ 3 (transLenTr ⟨30, by decide⟩ 3 hp)) T142_30
      hfix142_30 hinj142_30 hcardT142_30
      (fun i => conj_mem_of_fixedPoints _ _ (T142_30 i) (hfix142_30 i) _)
      ⟨142, by decide⟩ ⟨30, by decide⟩ _
      (Q2.validAt ⟨142, by decide⟩ (Q2.listedAt ⟨142, by decide⟩
        (alnCheck_rep ⟨142, by decide⟩ hj hq).1))
      (colE2 ⟨30, by decide⟩ 3 hp) Q2.T142_30_2 Q2.hfix142_30_2 Q2.hinj142_30_2
      Q2.hcardT142_30_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T142_30_2 i) (Q2.hfix142_30_2 i) _)
      colCert_142_30_3.hD ?_).symm
  rw [alnId_142 j hj]


theorem leaf_142_30_4 (hp : 4 < (Q2.transData.getD 30 []).length)
    (j : Nat) (hj : j < (repChars.getD 142 []).length)
    (hq : (normIsRep.getD 142 []).getD j false = true) :
    species (Q2.reps (⟨30, by decide⟩ : Fin 148)) (colE2 ⟨30, by decide⟩ 4 hp)
        (rowE2 (⟨142, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨30, by decide⟩ : Fin 148))
        (colE1 ⟨30, by decide⟩ 4 (transLenTr ⟨30, by decide⟩ 4 hp))
        (rowE1 (⟨142, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨142, by decide⟩ : Fin 148) ⟨30, by decide⟩ _
      (validAt ⟨142, by decide⟩ (listedAt ⟨142, by decide⟩ hj))
      (colE1 ⟨30, by decide⟩ 4 (transLenTr ⟨30, by decide⟩ 4 hp)) T142_30
      hfix142_30 hinj142_30 hcardT142_30
      (fun i => conj_mem_of_fixedPoints _ _ (T142_30 i) (hfix142_30 i) _)
      ⟨142, by decide⟩ ⟨30, by decide⟩ _
      (Q2.validAt ⟨142, by decide⟩ (Q2.listedAt ⟨142, by decide⟩
        (alnCheck_rep ⟨142, by decide⟩ hj hq).1))
      (colE2 ⟨30, by decide⟩ 4 hp) Q2.T142_30_2 Q2.hfix142_30_2 Q2.hinj142_30_2
      Q2.hcardT142_30_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T142_30_2 i) (Q2.hfix142_30_2 i) _)
      colCert_142_30_4.hD ?_).symm
  rw [alnId_142 j hj]


theorem leaf_142_30_5 (hp : 5 < (Q2.transData.getD 30 []).length)
    (j : Nat) (hj : j < (repChars.getD 142 []).length)
    (hq : (normIsRep.getD 142 []).getD j false = true) :
    species (Q2.reps (⟨30, by decide⟩ : Fin 148)) (colE2 ⟨30, by decide⟩ 5 hp)
        (rowE2 (⟨142, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨30, by decide⟩ : Fin 148))
        (colE1 ⟨30, by decide⟩ 5 (transLenTr ⟨30, by decide⟩ 5 hp))
        (rowE1 (⟨142, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨142, by decide⟩ : Fin 148) ⟨30, by decide⟩ _
      (validAt ⟨142, by decide⟩ (listedAt ⟨142, by decide⟩ hj))
      (colE1 ⟨30, by decide⟩ 5 (transLenTr ⟨30, by decide⟩ 5 hp)) T142_30
      hfix142_30 hinj142_30 hcardT142_30
      (fun i => conj_mem_of_fixedPoints _ _ (T142_30 i) (hfix142_30 i) _)
      ⟨142, by decide⟩ ⟨30, by decide⟩ _
      (Q2.validAt ⟨142, by decide⟩ (Q2.listedAt ⟨142, by decide⟩
        (alnCheck_rep ⟨142, by decide⟩ hj hq).1))
      (colE2 ⟨30, by decide⟩ 5 hp) Q2.T142_30_2 Q2.hfix142_30_2 Q2.hinj142_30_2
      Q2.hcardT142_30_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T142_30_2 i) (Q2.hfix142_30_2 i) _)
      ?_).symm
  rw [show colData1 (⟨142, by decide⟩ : Fin 148)
        ((colE1 ⟨30, by decide⟩ 5 (transLenTr ⟨30, by decide⟩ 5 hp) : ↥(reps ⟨30, by decide⟩)) : Coordinate 1)
        T142_30 = colFn colCertDiv_142_30_5.D1 (m := 5) from colCertDiv_142_30_5.bind1,
    show colData2 (⟨142, by decide⟩ : Fin 148)
        ((colE2 ⟨30, by decide⟩ 5 hp : ↥(Q2.reps ⟨30, by decide⟩)) : Coordinate 2)
        Q2.T142_30_2 = colFn colCertDiv_142_30_5.D2 (m := 5) from colCertDiv_142_30_5.bind2]
  rw [alnId_142 j hj]
  exact fastcode_of_div ⟨142, by decide⟩ _ _ _
    ((alnId_142 j hj) ▸ Q2.listedAt (⟨142, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨142, by decide⟩ : Fin 148) hj hq).1) colCertDiv_142_30_5_match


theorem leaf_142_30_10 (hp : 10 < (Q2.transData.getD 30 []).length)
    (j : Nat) (hj : j < (repChars.getD 142 []).length)
    (hq : (normIsRep.getD 142 []).getD j false = true) :
    species (Q2.reps (⟨30, by decide⟩ : Fin 148)) (colE2 ⟨30, by decide⟩ 10 hp)
        (rowE2 (⟨142, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨30, by decide⟩ : Fin 148))
        (colE1 ⟨30, by decide⟩ 10 (transLenTr ⟨30, by decide⟩ 10 hp))
        (rowE1 (⟨142, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨142, by decide⟩ : Fin 148) ⟨30, by decide⟩ _
      (validAt ⟨142, by decide⟩ (listedAt ⟨142, by decide⟩ hj))
      (colE1 ⟨30, by decide⟩ 10 (transLenTr ⟨30, by decide⟩ 10 hp)) T142_30
      hfix142_30 hinj142_30 hcardT142_30
      (fun i => conj_mem_of_fixedPoints _ _ (T142_30 i) (hfix142_30 i) _)
      ⟨142, by decide⟩ ⟨30, by decide⟩ _
      (Q2.validAt ⟨142, by decide⟩ (Q2.listedAt ⟨142, by decide⟩
        (alnCheck_rep ⟨142, by decide⟩ hj hq).1))
      (colE2 ⟨30, by decide⟩ 10 hp) Q2.T142_30_2 Q2.hfix142_30_2 Q2.hinj142_30_2
      Q2.hcardT142_30_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T142_30_2 i) (Q2.hfix142_30_2 i) _)
      ?_).symm
  rw [show colData1 (⟨142, by decide⟩ : Fin 148)
        ((colE1 ⟨30, by decide⟩ 10 (transLenTr ⟨30, by decide⟩ 10 hp) : ↥(reps ⟨30, by decide⟩)) : Coordinate 1)
        T142_30 = colFn colCertDiv_142_30_10.D1 (m := 5) from colCertDiv_142_30_10.bind1,
    show colData2 (⟨142, by decide⟩ : Fin 148)
        ((colE2 ⟨30, by decide⟩ 10 hp : ↥(Q2.reps ⟨30, by decide⟩)) : Coordinate 2)
        Q2.T142_30_2 = colFn colCertDiv_142_30_10.D2 (m := 5) from colCertDiv_142_30_10.bind2]
  rw [alnId_142 j hj]
  exact fastcode_of_div ⟨142, by decide⟩ _ _ _
    ((alnId_142 j hj) ▸ Q2.listedAt (⟨142, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨142, by decide⟩ : Fin 148) hj hq).1) colCertDiv_142_30_10_match


theorem leaf_142_30_15 (hp : 15 < (Q2.transData.getD 30 []).length)
    (j : Nat) (hj : j < (repChars.getD 142 []).length)
    (hq : (normIsRep.getD 142 []).getD j false = true) :
    species (Q2.reps (⟨30, by decide⟩ : Fin 148)) (colE2 ⟨30, by decide⟩ 15 hp)
        (rowE2 (⟨142, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨30, by decide⟩ : Fin 148))
        (colE1 ⟨30, by decide⟩ 15 (transLenTr ⟨30, by decide⟩ 15 hp))
        (rowE1 (⟨142, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨142, by decide⟩ : Fin 148) ⟨30, by decide⟩ _
      (validAt ⟨142, by decide⟩ (listedAt ⟨142, by decide⟩ hj))
      (colE1 ⟨30, by decide⟩ 15 (transLenTr ⟨30, by decide⟩ 15 hp)) T142_30
      hfix142_30 hinj142_30 hcardT142_30
      (fun i => conj_mem_of_fixedPoints _ _ (T142_30 i) (hfix142_30 i) _)
      ⟨142, by decide⟩ ⟨30, by decide⟩ _
      (Q2.validAt ⟨142, by decide⟩ (Q2.listedAt ⟨142, by decide⟩
        (alnCheck_rep ⟨142, by decide⟩ hj hq).1))
      (colE2 ⟨30, by decide⟩ 15 hp) Q2.T142_30_2 Q2.hfix142_30_2 Q2.hinj142_30_2
      Q2.hcardT142_30_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T142_30_2 i) (Q2.hfix142_30_2 i) _)
      ?_).symm
  rw [show colData1 (⟨142, by decide⟩ : Fin 148)
        ((colE1 ⟨30, by decide⟩ 15 (transLenTr ⟨30, by decide⟩ 15 hp) : ↥(reps ⟨30, by decide⟩)) : Coordinate 1)
        T142_30 = colFn colCertDiv_142_30_15.D1 (m := 5) from colCertDiv_142_30_15.bind1,
    show colData2 (⟨142, by decide⟩ : Fin 148)
        ((colE2 ⟨30, by decide⟩ 15 hp : ↥(Q2.reps ⟨30, by decide⟩)) : Coordinate 2)
        Q2.T142_30_2 = colFn colCertDiv_142_30_15.D2 (m := 5) from colCertDiv_142_30_15.bind2]
  rw [alnId_142 j hj]
  exact fastcode_of_div ⟨142, by decide⟩ _ _ _
    ((alnId_142 j hj) ▸ Q2.listedAt (⟨142, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨142, by decide⟩ : Fin 148) hj hq).1) colCertDiv_142_30_15_match


theorem leaf_142_30_20 (hp : 20 < (Q2.transData.getD 30 []).length)
    (j : Nat) (hj : j < (repChars.getD 142 []).length)
    (hq : (normIsRep.getD 142 []).getD j false = true) :
    species (Q2.reps (⟨30, by decide⟩ : Fin 148)) (colE2 ⟨30, by decide⟩ 20 hp)
        (rowE2 (⟨142, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨30, by decide⟩ : Fin 148))
        (colE1 ⟨30, by decide⟩ 20 (transLenTr ⟨30, by decide⟩ 20 hp))
        (rowE1 (⟨142, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨142, by decide⟩ : Fin 148) ⟨30, by decide⟩ _
      (validAt ⟨142, by decide⟩ (listedAt ⟨142, by decide⟩ hj))
      (colE1 ⟨30, by decide⟩ 20 (transLenTr ⟨30, by decide⟩ 20 hp)) T142_30
      hfix142_30 hinj142_30 hcardT142_30
      (fun i => conj_mem_of_fixedPoints _ _ (T142_30 i) (hfix142_30 i) _)
      ⟨142, by decide⟩ ⟨30, by decide⟩ _
      (Q2.validAt ⟨142, by decide⟩ (Q2.listedAt ⟨142, by decide⟩
        (alnCheck_rep ⟨142, by decide⟩ hj hq).1))
      (colE2 ⟨30, by decide⟩ 20 hp) Q2.T142_30_2 Q2.hfix142_30_2 Q2.hinj142_30_2
      Q2.hcardT142_30_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T142_30_2 i) (Q2.hfix142_30_2 i) _)
      colCert_142_30_20.hD ?_).symm
  rw [alnId_142 j hj]


theorem leaf_142_31_0 (hp : 0 < (Q2.transData.getD 31 []).length)
    (j : Nat) (hj : j < (repChars.getD 142 []).length)
    (hq : (normIsRep.getD 142 []).getD j false = true) :
    species (Q2.reps (⟨31, by decide⟩ : Fin 148)) (colE2 ⟨31, by decide⟩ 0 hp)
        (rowE2 (⟨142, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨31, by decide⟩ : Fin 148))
        (colE1 ⟨31, by decide⟩ 0 (transLenTr ⟨31, by decide⟩ 0 hp))
        (rowE1 (⟨142, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨142, by decide⟩ : Fin 148) ⟨31, by decide⟩ _
      (validAt ⟨142, by decide⟩ (listedAt ⟨142, by decide⟩ hj))
      (colE1 ⟨31, by decide⟩ 0 (transLenTr ⟨31, by decide⟩ 0 hp)) T142_31
      hfix142_31 hinj142_31 hcardT142_31
      (fun i => conj_mem_of_fixedPoints _ _ (T142_31 i) (hfix142_31 i) _)
      ⟨142, by decide⟩ ⟨31, by decide⟩ _
      (Q2.validAt ⟨142, by decide⟩ (Q2.listedAt ⟨142, by decide⟩
        (alnCheck_rep ⟨142, by decide⟩ hj hq).1))
      (colE2 ⟨31, by decide⟩ 0 hp) Q2.T142_31_2 Q2.hfix142_31_2 Q2.hinj142_31_2
      Q2.hcardT142_31_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T142_31_2 i) (Q2.hfix142_31_2 i) _)
      colCert_142_31_0.hD ?_).symm
  rw [alnId_142 j hj]


theorem leaf_142_31_1 (hp : 1 < (Q2.transData.getD 31 []).length)
    (j : Nat) (hj : j < (repChars.getD 142 []).length)
    (hq : (normIsRep.getD 142 []).getD j false = true) :
    species (Q2.reps (⟨31, by decide⟩ : Fin 148)) (colE2 ⟨31, by decide⟩ 1 hp)
        (rowE2 (⟨142, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨31, by decide⟩ : Fin 148))
        (colE1 ⟨31, by decide⟩ 1 (transLenTr ⟨31, by decide⟩ 1 hp))
        (rowE1 (⟨142, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨142, by decide⟩ : Fin 148) ⟨31, by decide⟩ _
      (validAt ⟨142, by decide⟩ (listedAt ⟨142, by decide⟩ hj))
      (colE1 ⟨31, by decide⟩ 1 (transLenTr ⟨31, by decide⟩ 1 hp)) T142_31
      hfix142_31 hinj142_31 hcardT142_31
      (fun i => conj_mem_of_fixedPoints _ _ (T142_31 i) (hfix142_31 i) _)
      ⟨142, by decide⟩ ⟨31, by decide⟩ _
      (Q2.validAt ⟨142, by decide⟩ (Q2.listedAt ⟨142, by decide⟩
        (alnCheck_rep ⟨142, by decide⟩ hj hq).1))
      (colE2 ⟨31, by decide⟩ 1 hp) Q2.T142_31_2 Q2.hfix142_31_2 Q2.hinj142_31_2
      Q2.hcardT142_31_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T142_31_2 i) (Q2.hfix142_31_2 i) _)
      colCert_142_31_1.hD ?_).symm
  rw [alnId_142 j hj]


theorem leaf_142_31_2 (hp : 2 < (Q2.transData.getD 31 []).length)
    (j : Nat) (hj : j < (repChars.getD 142 []).length)
    (hq : (normIsRep.getD 142 []).getD j false = true) :
    species (Q2.reps (⟨31, by decide⟩ : Fin 148)) (colE2 ⟨31, by decide⟩ 2 hp)
        (rowE2 (⟨142, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨31, by decide⟩ : Fin 148))
        (colE1 ⟨31, by decide⟩ 2 (transLenTr ⟨31, by decide⟩ 2 hp))
        (rowE1 (⟨142, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨142, by decide⟩ : Fin 148) ⟨31, by decide⟩ _
      (validAt ⟨142, by decide⟩ (listedAt ⟨142, by decide⟩ hj))
      (colE1 ⟨31, by decide⟩ 2 (transLenTr ⟨31, by decide⟩ 2 hp)) T142_31
      hfix142_31 hinj142_31 hcardT142_31
      (fun i => conj_mem_of_fixedPoints _ _ (T142_31 i) (hfix142_31 i) _)
      ⟨142, by decide⟩ ⟨31, by decide⟩ _
      (Q2.validAt ⟨142, by decide⟩ (Q2.listedAt ⟨142, by decide⟩
        (alnCheck_rep ⟨142, by decide⟩ hj hq).1))
      (colE2 ⟨31, by decide⟩ 2 hp) Q2.T142_31_2 Q2.hfix142_31_2 Q2.hinj142_31_2
      Q2.hcardT142_31_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T142_31_2 i) (Q2.hfix142_31_2 i) _)
      colCert_142_31_2.hD ?_).symm
  rw [alnId_142 j hj]


theorem leaf_142_31_3 (hp : 3 < (Q2.transData.getD 31 []).length)
    (j : Nat) (hj : j < (repChars.getD 142 []).length)
    (hq : (normIsRep.getD 142 []).getD j false = true) :
    species (Q2.reps (⟨31, by decide⟩ : Fin 148)) (colE2 ⟨31, by decide⟩ 3 hp)
        (rowE2 (⟨142, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨31, by decide⟩ : Fin 148))
        (colE1 ⟨31, by decide⟩ 3 (transLenTr ⟨31, by decide⟩ 3 hp))
        (rowE1 (⟨142, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨142, by decide⟩ : Fin 148) ⟨31, by decide⟩ _
      (validAt ⟨142, by decide⟩ (listedAt ⟨142, by decide⟩ hj))
      (colE1 ⟨31, by decide⟩ 3 (transLenTr ⟨31, by decide⟩ 3 hp)) T142_31
      hfix142_31 hinj142_31 hcardT142_31
      (fun i => conj_mem_of_fixedPoints _ _ (T142_31 i) (hfix142_31 i) _)
      ⟨142, by decide⟩ ⟨31, by decide⟩ _
      (Q2.validAt ⟨142, by decide⟩ (Q2.listedAt ⟨142, by decide⟩
        (alnCheck_rep ⟨142, by decide⟩ hj hq).1))
      (colE2 ⟨31, by decide⟩ 3 hp) Q2.T142_31_2 Q2.hfix142_31_2 Q2.hinj142_31_2
      Q2.hcardT142_31_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T142_31_2 i) (Q2.hfix142_31_2 i) _)
      colCert_142_31_3.hD ?_).symm
  rw [alnId_142 j hj]


theorem leaf_142_31_4 (hp : 4 < (Q2.transData.getD 31 []).length)
    (j : Nat) (hj : j < (repChars.getD 142 []).length)
    (hq : (normIsRep.getD 142 []).getD j false = true) :
    species (Q2.reps (⟨31, by decide⟩ : Fin 148)) (colE2 ⟨31, by decide⟩ 4 hp)
        (rowE2 (⟨142, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨31, by decide⟩ : Fin 148))
        (colE1 ⟨31, by decide⟩ 4 (transLenTr ⟨31, by decide⟩ 4 hp))
        (rowE1 (⟨142, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨142, by decide⟩ : Fin 148) ⟨31, by decide⟩ _
      (validAt ⟨142, by decide⟩ (listedAt ⟨142, by decide⟩ hj))
      (colE1 ⟨31, by decide⟩ 4 (transLenTr ⟨31, by decide⟩ 4 hp)) T142_31
      hfix142_31 hinj142_31 hcardT142_31
      (fun i => conj_mem_of_fixedPoints _ _ (T142_31 i) (hfix142_31 i) _)
      ⟨142, by decide⟩ ⟨31, by decide⟩ _
      (Q2.validAt ⟨142, by decide⟩ (Q2.listedAt ⟨142, by decide⟩
        (alnCheck_rep ⟨142, by decide⟩ hj hq).1))
      (colE2 ⟨31, by decide⟩ 4 hp) Q2.T142_31_2 Q2.hfix142_31_2 Q2.hinj142_31_2
      Q2.hcardT142_31_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T142_31_2 i) (Q2.hfix142_31_2 i) _)
      colCert_142_31_4.hD ?_).symm
  rw [alnId_142 j hj]


theorem leaf_142_31_5 (hp : 5 < (Q2.transData.getD 31 []).length)
    (j : Nat) (hj : j < (repChars.getD 142 []).length)
    (hq : (normIsRep.getD 142 []).getD j false = true) :
    species (Q2.reps (⟨31, by decide⟩ : Fin 148)) (colE2 ⟨31, by decide⟩ 5 hp)
        (rowE2 (⟨142, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨31, by decide⟩ : Fin 148))
        (colE1 ⟨31, by decide⟩ 5 (transLenTr ⟨31, by decide⟩ 5 hp))
        (rowE1 (⟨142, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨142, by decide⟩ : Fin 148) ⟨31, by decide⟩ _
      (validAt ⟨142, by decide⟩ (listedAt ⟨142, by decide⟩ hj))
      (colE1 ⟨31, by decide⟩ 5 (transLenTr ⟨31, by decide⟩ 5 hp)) T142_31
      hfix142_31 hinj142_31 hcardT142_31
      (fun i => conj_mem_of_fixedPoints _ _ (T142_31 i) (hfix142_31 i) _)
      ⟨142, by decide⟩ ⟨31, by decide⟩ _
      (Q2.validAt ⟨142, by decide⟩ (Q2.listedAt ⟨142, by decide⟩
        (alnCheck_rep ⟨142, by decide⟩ hj hq).1))
      (colE2 ⟨31, by decide⟩ 5 hp) Q2.T142_31_2 Q2.hfix142_31_2 Q2.hinj142_31_2
      Q2.hcardT142_31_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T142_31_2 i) (Q2.hfix142_31_2 i) _)
      ?_).symm
  rw [show colData1 (⟨142, by decide⟩ : Fin 148)
        ((colE1 ⟨31, by decide⟩ 5 (transLenTr ⟨31, by decide⟩ 5 hp) : ↥(reps ⟨31, by decide⟩)) : Coordinate 1)
        T142_31 = colFn colCertDiv_142_31_5.D1 (m := 5) from colCertDiv_142_31_5.bind1,
    show colData2 (⟨142, by decide⟩ : Fin 148)
        ((colE2 ⟨31, by decide⟩ 5 hp : ↥(Q2.reps ⟨31, by decide⟩)) : Coordinate 2)
        Q2.T142_31_2 = colFn colCertDiv_142_31_5.D2 (m := 5) from colCertDiv_142_31_5.bind2]
  rw [alnId_142 j hj]
  exact fastcode_of_div ⟨142, by decide⟩ _ _ _
    ((alnId_142 j hj) ▸ Q2.listedAt (⟨142, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨142, by decide⟩ : Fin 148) hj hq).1) colCertDiv_142_31_5_match


theorem leaf_142_31_10 (hp : 10 < (Q2.transData.getD 31 []).length)
    (j : Nat) (hj : j < (repChars.getD 142 []).length)
    (hq : (normIsRep.getD 142 []).getD j false = true) :
    species (Q2.reps (⟨31, by decide⟩ : Fin 148)) (colE2 ⟨31, by decide⟩ 10 hp)
        (rowE2 (⟨142, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨31, by decide⟩ : Fin 148))
        (colE1 ⟨31, by decide⟩ 10 (transLenTr ⟨31, by decide⟩ 10 hp))
        (rowE1 (⟨142, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨142, by decide⟩ : Fin 148) ⟨31, by decide⟩ _
      (validAt ⟨142, by decide⟩ (listedAt ⟨142, by decide⟩ hj))
      (colE1 ⟨31, by decide⟩ 10 (transLenTr ⟨31, by decide⟩ 10 hp)) T142_31
      hfix142_31 hinj142_31 hcardT142_31
      (fun i => conj_mem_of_fixedPoints _ _ (T142_31 i) (hfix142_31 i) _)
      ⟨142, by decide⟩ ⟨31, by decide⟩ _
      (Q2.validAt ⟨142, by decide⟩ (Q2.listedAt ⟨142, by decide⟩
        (alnCheck_rep ⟨142, by decide⟩ hj hq).1))
      (colE2 ⟨31, by decide⟩ 10 hp) Q2.T142_31_2 Q2.hfix142_31_2 Q2.hinj142_31_2
      Q2.hcardT142_31_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T142_31_2 i) (Q2.hfix142_31_2 i) _)
      colCert_142_31_10.hD ?_).symm
  rw [alnId_142 j hj]


theorem leaf_142_31_15 (hp : 15 < (Q2.transData.getD 31 []).length)
    (j : Nat) (hj : j < (repChars.getD 142 []).length)
    (hq : (normIsRep.getD 142 []).getD j false = true) :
    species (Q2.reps (⟨31, by decide⟩ : Fin 148)) (colE2 ⟨31, by decide⟩ 15 hp)
        (rowE2 (⟨142, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨31, by decide⟩ : Fin 148))
        (colE1 ⟨31, by decide⟩ 15 (transLenTr ⟨31, by decide⟩ 15 hp))
        (rowE1 (⟨142, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨142, by decide⟩ : Fin 148) ⟨31, by decide⟩ _
      (validAt ⟨142, by decide⟩ (listedAt ⟨142, by decide⟩ hj))
      (colE1 ⟨31, by decide⟩ 15 (transLenTr ⟨31, by decide⟩ 15 hp)) T142_31
      hfix142_31 hinj142_31 hcardT142_31
      (fun i => conj_mem_of_fixedPoints _ _ (T142_31 i) (hfix142_31 i) _)
      ⟨142, by decide⟩ ⟨31, by decide⟩ _
      (Q2.validAt ⟨142, by decide⟩ (Q2.listedAt ⟨142, by decide⟩
        (alnCheck_rep ⟨142, by decide⟩ hj hq).1))
      (colE2 ⟨31, by decide⟩ 15 hp) Q2.T142_31_2 Q2.hfix142_31_2 Q2.hinj142_31_2
      Q2.hcardT142_31_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T142_31_2 i) (Q2.hfix142_31_2 i) _)
      ?_).symm
  rw [show colData1 (⟨142, by decide⟩ : Fin 148)
        ((colE1 ⟨31, by decide⟩ 15 (transLenTr ⟨31, by decide⟩ 15 hp) : ↥(reps ⟨31, by decide⟩)) : Coordinate 1)
        T142_31 = colFn colCertDiv_142_31_15.D1 (m := 5) from colCertDiv_142_31_15.bind1,
    show colData2 (⟨142, by decide⟩ : Fin 148)
        ((colE2 ⟨31, by decide⟩ 15 hp : ↥(Q2.reps ⟨31, by decide⟩)) : Coordinate 2)
        Q2.T142_31_2 = colFn colCertDiv_142_31_15.D2 (m := 5) from colCertDiv_142_31_15.bind2]
  rw [alnId_142 j hj]
  exact fastcode_of_div ⟨142, by decide⟩ _ _ _
    ((alnId_142 j hj) ▸ Q2.listedAt (⟨142, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨142, by decide⟩ : Fin 148) hj hq).1) colCertDiv_142_31_15_match


theorem leaf_142_31_20 (hp : 20 < (Q2.transData.getD 31 []).length)
    (j : Nat) (hj : j < (repChars.getD 142 []).length)
    (hq : (normIsRep.getD 142 []).getD j false = true) :
    species (Q2.reps (⟨31, by decide⟩ : Fin 148)) (colE2 ⟨31, by decide⟩ 20 hp)
        (rowE2 (⟨142, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨31, by decide⟩ : Fin 148))
        (colE1 ⟨31, by decide⟩ 20 (transLenTr ⟨31, by decide⟩ 20 hp))
        (rowE1 (⟨142, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨142, by decide⟩ : Fin 148) ⟨31, by decide⟩ _
      (validAt ⟨142, by decide⟩ (listedAt ⟨142, by decide⟩ hj))
      (colE1 ⟨31, by decide⟩ 20 (transLenTr ⟨31, by decide⟩ 20 hp)) T142_31
      hfix142_31 hinj142_31 hcardT142_31
      (fun i => conj_mem_of_fixedPoints _ _ (T142_31 i) (hfix142_31 i) _)
      ⟨142, by decide⟩ ⟨31, by decide⟩ _
      (Q2.validAt ⟨142, by decide⟩ (Q2.listedAt ⟨142, by decide⟩
        (alnCheck_rep ⟨142, by decide⟩ hj hq).1))
      (colE2 ⟨31, by decide⟩ 20 hp) Q2.T142_31_2 Q2.hfix142_31_2 Q2.hinj142_31_2
      Q2.hcardT142_31_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T142_31_2 i) (Q2.hfix142_31_2 i) _)
      colCert_142_31_20.hD ?_).symm
  rw [alnId_142 j hj]


theorem leaf_142_32_0 (hp : 0 < (Q2.transData.getD 32 []).length)
    (j : Nat) (hj : j < (repChars.getD 142 []).length)
    (hq : (normIsRep.getD 142 []).getD j false = true) :
    species (Q2.reps (⟨32, by decide⟩ : Fin 148)) (colE2 ⟨32, by decide⟩ 0 hp)
        (rowE2 (⟨142, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨32, by decide⟩ : Fin 148))
        (colE1 ⟨32, by decide⟩ 0 (transLenTr ⟨32, by decide⟩ 0 hp))
        (rowE1 (⟨142, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨142, by decide⟩ : Fin 148) ⟨32, by decide⟩ _
      (validAt ⟨142, by decide⟩ (listedAt ⟨142, by decide⟩ hj))
      (colE1 ⟨32, by decide⟩ 0 (transLenTr ⟨32, by decide⟩ 0 hp)) T142_32
      hfix142_32 hinj142_32 hcardT142_32
      (fun i => conj_mem_of_fixedPoints _ _ (T142_32 i) (hfix142_32 i) _)
      ⟨142, by decide⟩ ⟨32, by decide⟩ _
      (Q2.validAt ⟨142, by decide⟩ (Q2.listedAt ⟨142, by decide⟩
        (alnCheck_rep ⟨142, by decide⟩ hj hq).1))
      (colE2 ⟨32, by decide⟩ 0 hp) Q2.T142_32_2 Q2.hfix142_32_2 Q2.hinj142_32_2
      Q2.hcardT142_32_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T142_32_2 i) (Q2.hfix142_32_2 i) _)
      colCert_142_32_0.hD ?_).symm
  rw [alnId_142 j hj]


theorem leaf_142_32_1 (hp : 1 < (Q2.transData.getD 32 []).length)
    (j : Nat) (hj : j < (repChars.getD 142 []).length)
    (hq : (normIsRep.getD 142 []).getD j false = true) :
    species (Q2.reps (⟨32, by decide⟩ : Fin 148)) (colE2 ⟨32, by decide⟩ 1 hp)
        (rowE2 (⟨142, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨32, by decide⟩ : Fin 148))
        (colE1 ⟨32, by decide⟩ 1 (transLenTr ⟨32, by decide⟩ 1 hp))
        (rowE1 (⟨142, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨142, by decide⟩ : Fin 148) ⟨32, by decide⟩ _
      (validAt ⟨142, by decide⟩ (listedAt ⟨142, by decide⟩ hj))
      (colE1 ⟨32, by decide⟩ 1 (transLenTr ⟨32, by decide⟩ 1 hp)) T142_32
      hfix142_32 hinj142_32 hcardT142_32
      (fun i => conj_mem_of_fixedPoints _ _ (T142_32 i) (hfix142_32 i) _)
      ⟨142, by decide⟩ ⟨32, by decide⟩ _
      (Q2.validAt ⟨142, by decide⟩ (Q2.listedAt ⟨142, by decide⟩
        (alnCheck_rep ⟨142, by decide⟩ hj hq).1))
      (colE2 ⟨32, by decide⟩ 1 hp) Q2.T142_32_2 Q2.hfix142_32_2 Q2.hinj142_32_2
      Q2.hcardT142_32_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T142_32_2 i) (Q2.hfix142_32_2 i) _)
      colCert_142_32_1.hD ?_).symm
  rw [alnId_142 j hj]


theorem leaf_142_32_2 (hp : 2 < (Q2.transData.getD 32 []).length)
    (j : Nat) (hj : j < (repChars.getD 142 []).length)
    (hq : (normIsRep.getD 142 []).getD j false = true) :
    species (Q2.reps (⟨32, by decide⟩ : Fin 148)) (colE2 ⟨32, by decide⟩ 2 hp)
        (rowE2 (⟨142, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨32, by decide⟩ : Fin 148))
        (colE1 ⟨32, by decide⟩ 2 (transLenTr ⟨32, by decide⟩ 2 hp))
        (rowE1 (⟨142, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨142, by decide⟩ : Fin 148) ⟨32, by decide⟩ _
      (validAt ⟨142, by decide⟩ (listedAt ⟨142, by decide⟩ hj))
      (colE1 ⟨32, by decide⟩ 2 (transLenTr ⟨32, by decide⟩ 2 hp)) T142_32
      hfix142_32 hinj142_32 hcardT142_32
      (fun i => conj_mem_of_fixedPoints _ _ (T142_32 i) (hfix142_32 i) _)
      ⟨142, by decide⟩ ⟨32, by decide⟩ _
      (Q2.validAt ⟨142, by decide⟩ (Q2.listedAt ⟨142, by decide⟩
        (alnCheck_rep ⟨142, by decide⟩ hj hq).1))
      (colE2 ⟨32, by decide⟩ 2 hp) Q2.T142_32_2 Q2.hfix142_32_2 Q2.hinj142_32_2
      Q2.hcardT142_32_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T142_32_2 i) (Q2.hfix142_32_2 i) _)
      colCert_142_32_2.hD ?_).symm
  rw [alnId_142 j hj]


theorem leaf_142_32_3 (hp : 3 < (Q2.transData.getD 32 []).length)
    (j : Nat) (hj : j < (repChars.getD 142 []).length)
    (hq : (normIsRep.getD 142 []).getD j false = true) :
    species (Q2.reps (⟨32, by decide⟩ : Fin 148)) (colE2 ⟨32, by decide⟩ 3 hp)
        (rowE2 (⟨142, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨32, by decide⟩ : Fin 148))
        (colE1 ⟨32, by decide⟩ 3 (transLenTr ⟨32, by decide⟩ 3 hp))
        (rowE1 (⟨142, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨142, by decide⟩ : Fin 148) ⟨32, by decide⟩ _
      (validAt ⟨142, by decide⟩ (listedAt ⟨142, by decide⟩ hj))
      (colE1 ⟨32, by decide⟩ 3 (transLenTr ⟨32, by decide⟩ 3 hp)) T142_32
      hfix142_32 hinj142_32 hcardT142_32
      (fun i => conj_mem_of_fixedPoints _ _ (T142_32 i) (hfix142_32 i) _)
      ⟨142, by decide⟩ ⟨32, by decide⟩ _
      (Q2.validAt ⟨142, by decide⟩ (Q2.listedAt ⟨142, by decide⟩
        (alnCheck_rep ⟨142, by decide⟩ hj hq).1))
      (colE2 ⟨32, by decide⟩ 3 hp) Q2.T142_32_2 Q2.hfix142_32_2 Q2.hinj142_32_2
      Q2.hcardT142_32_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T142_32_2 i) (Q2.hfix142_32_2 i) _)
      colCert_142_32_3.hD ?_).symm
  rw [alnId_142 j hj]


theorem leaf_142_32_4 (hp : 4 < (Q2.transData.getD 32 []).length)
    (j : Nat) (hj : j < (repChars.getD 142 []).length)
    (hq : (normIsRep.getD 142 []).getD j false = true) :
    species (Q2.reps (⟨32, by decide⟩ : Fin 148)) (colE2 ⟨32, by decide⟩ 4 hp)
        (rowE2 (⟨142, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨32, by decide⟩ : Fin 148))
        (colE1 ⟨32, by decide⟩ 4 (transLenTr ⟨32, by decide⟩ 4 hp))
        (rowE1 (⟨142, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨142, by decide⟩ : Fin 148) ⟨32, by decide⟩ _
      (validAt ⟨142, by decide⟩ (listedAt ⟨142, by decide⟩ hj))
      (colE1 ⟨32, by decide⟩ 4 (transLenTr ⟨32, by decide⟩ 4 hp)) T142_32
      hfix142_32 hinj142_32 hcardT142_32
      (fun i => conj_mem_of_fixedPoints _ _ (T142_32 i) (hfix142_32 i) _)
      ⟨142, by decide⟩ ⟨32, by decide⟩ _
      (Q2.validAt ⟨142, by decide⟩ (Q2.listedAt ⟨142, by decide⟩
        (alnCheck_rep ⟨142, by decide⟩ hj hq).1))
      (colE2 ⟨32, by decide⟩ 4 hp) Q2.T142_32_2 Q2.hfix142_32_2 Q2.hinj142_32_2
      Q2.hcardT142_32_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T142_32_2 i) (Q2.hfix142_32_2 i) _)
      colCert_142_32_4.hD ?_).symm
  rw [alnId_142 j hj]


theorem leaf_142_32_5 (hp : 5 < (Q2.transData.getD 32 []).length)
    (j : Nat) (hj : j < (repChars.getD 142 []).length)
    (hq : (normIsRep.getD 142 []).getD j false = true) :
    species (Q2.reps (⟨32, by decide⟩ : Fin 148)) (colE2 ⟨32, by decide⟩ 5 hp)
        (rowE2 (⟨142, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨32, by decide⟩ : Fin 148))
        (colE1 ⟨32, by decide⟩ 5 (transLenTr ⟨32, by decide⟩ 5 hp))
        (rowE1 (⟨142, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨142, by decide⟩ : Fin 148) ⟨32, by decide⟩ _
      (validAt ⟨142, by decide⟩ (listedAt ⟨142, by decide⟩ hj))
      (colE1 ⟨32, by decide⟩ 5 (transLenTr ⟨32, by decide⟩ 5 hp)) T142_32
      hfix142_32 hinj142_32 hcardT142_32
      (fun i => conj_mem_of_fixedPoints _ _ (T142_32 i) (hfix142_32 i) _)
      ⟨142, by decide⟩ ⟨32, by decide⟩ _
      (Q2.validAt ⟨142, by decide⟩ (Q2.listedAt ⟨142, by decide⟩
        (alnCheck_rep ⟨142, by decide⟩ hj hq).1))
      (colE2 ⟨32, by decide⟩ 5 hp) Q2.T142_32_2 Q2.hfix142_32_2 Q2.hinj142_32_2
      Q2.hcardT142_32_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T142_32_2 i) (Q2.hfix142_32_2 i) _)
      colCert_142_32_5.hD ?_).symm
  rw [alnId_142 j hj]


theorem leaf_142_32_10 (hp : 10 < (Q2.transData.getD 32 []).length)
    (j : Nat) (hj : j < (repChars.getD 142 []).length)
    (hq : (normIsRep.getD 142 []).getD j false = true) :
    species (Q2.reps (⟨32, by decide⟩ : Fin 148)) (colE2 ⟨32, by decide⟩ 10 hp)
        (rowE2 (⟨142, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨32, by decide⟩ : Fin 148))
        (colE1 ⟨32, by decide⟩ 10 (transLenTr ⟨32, by decide⟩ 10 hp))
        (rowE1 (⟨142, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨142, by decide⟩ : Fin 148) ⟨32, by decide⟩ _
      (validAt ⟨142, by decide⟩ (listedAt ⟨142, by decide⟩ hj))
      (colE1 ⟨32, by decide⟩ 10 (transLenTr ⟨32, by decide⟩ 10 hp)) T142_32
      hfix142_32 hinj142_32 hcardT142_32
      (fun i => conj_mem_of_fixedPoints _ _ (T142_32 i) (hfix142_32 i) _)
      ⟨142, by decide⟩ ⟨32, by decide⟩ _
      (Q2.validAt ⟨142, by decide⟩ (Q2.listedAt ⟨142, by decide⟩
        (alnCheck_rep ⟨142, by decide⟩ hj hq).1))
      (colE2 ⟨32, by decide⟩ 10 hp) Q2.T142_32_2 Q2.hfix142_32_2 Q2.hinj142_32_2
      Q2.hcardT142_32_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T142_32_2 i) (Q2.hfix142_32_2 i) _)
      colCert_142_32_10.hD ?_).symm
  rw [alnId_142 j hj]


theorem leaf_142_32_15 (hp : 15 < (Q2.transData.getD 32 []).length)
    (j : Nat) (hj : j < (repChars.getD 142 []).length)
    (hq : (normIsRep.getD 142 []).getD j false = true) :
    species (Q2.reps (⟨32, by decide⟩ : Fin 148)) (colE2 ⟨32, by decide⟩ 15 hp)
        (rowE2 (⟨142, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨32, by decide⟩ : Fin 148))
        (colE1 ⟨32, by decide⟩ 15 (transLenTr ⟨32, by decide⟩ 15 hp))
        (rowE1 (⟨142, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨142, by decide⟩ : Fin 148) ⟨32, by decide⟩ _
      (validAt ⟨142, by decide⟩ (listedAt ⟨142, by decide⟩ hj))
      (colE1 ⟨32, by decide⟩ 15 (transLenTr ⟨32, by decide⟩ 15 hp)) T142_32
      hfix142_32 hinj142_32 hcardT142_32
      (fun i => conj_mem_of_fixedPoints _ _ (T142_32 i) (hfix142_32 i) _)
      ⟨142, by decide⟩ ⟨32, by decide⟩ _
      (Q2.validAt ⟨142, by decide⟩ (Q2.listedAt ⟨142, by decide⟩
        (alnCheck_rep ⟨142, by decide⟩ hj hq).1))
      (colE2 ⟨32, by decide⟩ 15 hp) Q2.T142_32_2 Q2.hfix142_32_2 Q2.hinj142_32_2
      Q2.hcardT142_32_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T142_32_2 i) (Q2.hfix142_32_2 i) _)
      colCert_142_32_15.hD ?_).symm
  rw [alnId_142 j hj]


theorem leaf_142_32_20 (hp : 20 < (Q2.transData.getD 32 []).length)
    (j : Nat) (hj : j < (repChars.getD 142 []).length)
    (hq : (normIsRep.getD 142 []).getD j false = true) :
    species (Q2.reps (⟨32, by decide⟩ : Fin 148)) (colE2 ⟨32, by decide⟩ 20 hp)
        (rowE2 (⟨142, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨32, by decide⟩ : Fin 148))
        (colE1 ⟨32, by decide⟩ 20 (transLenTr ⟨32, by decide⟩ 20 hp))
        (rowE1 (⟨142, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨142, by decide⟩ : Fin 148) ⟨32, by decide⟩ _
      (validAt ⟨142, by decide⟩ (listedAt ⟨142, by decide⟩ hj))
      (colE1 ⟨32, by decide⟩ 20 (transLenTr ⟨32, by decide⟩ 20 hp)) T142_32
      hfix142_32 hinj142_32 hcardT142_32
      (fun i => conj_mem_of_fixedPoints _ _ (T142_32 i) (hfix142_32 i) _)
      ⟨142, by decide⟩ ⟨32, by decide⟩ _
      (Q2.validAt ⟨142, by decide⟩ (Q2.listedAt ⟨142, by decide⟩
        (alnCheck_rep ⟨142, by decide⟩ hj hq).1))
      (colE2 ⟨32, by decide⟩ 20 hp) Q2.T142_32_2 Q2.hfix142_32_2 Q2.hinj142_32_2
      Q2.hcardT142_32_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T142_32_2 i) (Q2.hfix142_32_2 i) _)
      colCert_142_32_20.hD ?_).symm
  rw [alnId_142 j hj]


theorem leaf_142_53_0 (hp : 0 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 142 []).length)
    (hq : (normIsRep.getD 142 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 0 hp)
        (rowE2 (⟨142, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 0 (transLenTr ⟨53, by decide⟩ 0 hp))
        (rowE1 (⟨142, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨142, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨142, by decide⟩ (listedAt ⟨142, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 0 (transLenTr ⟨53, by decide⟩ 0 hp)) T142_53
      hfix142_53 hinj142_53 hcardT142_53
      (fun i => conj_mem_of_fixedPoints _ _ (T142_53 i) (hfix142_53 i) _)
      ⟨142, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨142, by decide⟩ (Q2.listedAt ⟨142, by decide⟩
        (alnCheck_rep ⟨142, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 0 hp) Q2.T142_53_2 Q2.hfix142_53_2 Q2.hinj142_53_2
      Q2.hcardT142_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T142_53_2 i) (Q2.hfix142_53_2 i) _)
      colCert_142_53_0.hD ?_).symm
  rw [alnId_142 j hj]


theorem leaf_142_53_1 (hp : 1 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 142 []).length)
    (hq : (normIsRep.getD 142 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 1 hp)
        (rowE2 (⟨142, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 1 (transLenTr ⟨53, by decide⟩ 1 hp))
        (rowE1 (⟨142, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨142, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨142, by decide⟩ (listedAt ⟨142, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 1 (transLenTr ⟨53, by decide⟩ 1 hp)) T142_53
      hfix142_53 hinj142_53 hcardT142_53
      (fun i => conj_mem_of_fixedPoints _ _ (T142_53 i) (hfix142_53 i) _)
      ⟨142, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨142, by decide⟩ (Q2.listedAt ⟨142, by decide⟩
        (alnCheck_rep ⟨142, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 1 hp) Q2.T142_53_2 Q2.hfix142_53_2 Q2.hinj142_53_2
      Q2.hcardT142_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T142_53_2 i) (Q2.hfix142_53_2 i) _)
      colCert_142_53_1.hD ?_).symm
  rw [alnId_142 j hj]


theorem leaf_142_53_2 (hp : 2 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 142 []).length)
    (hq : (normIsRep.getD 142 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 2 hp)
        (rowE2 (⟨142, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 2 (transLenTr ⟨53, by decide⟩ 2 hp))
        (rowE1 (⟨142, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨142, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨142, by decide⟩ (listedAt ⟨142, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 2 (transLenTr ⟨53, by decide⟩ 2 hp)) T142_53
      hfix142_53 hinj142_53 hcardT142_53
      (fun i => conj_mem_of_fixedPoints _ _ (T142_53 i) (hfix142_53 i) _)
      ⟨142, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨142, by decide⟩ (Q2.listedAt ⟨142, by decide⟩
        (alnCheck_rep ⟨142, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 2 hp) Q2.T142_53_2 Q2.hfix142_53_2 Q2.hinj142_53_2
      Q2.hcardT142_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T142_53_2 i) (Q2.hfix142_53_2 i) _)
      colCert_142_53_2.hD ?_).symm
  rw [alnId_142 j hj]


theorem leaf_142_53_3 (hp : 3 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 142 []).length)
    (hq : (normIsRep.getD 142 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 3 hp)
        (rowE2 (⟨142, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 3 (transLenTr ⟨53, by decide⟩ 3 hp))
        (rowE1 (⟨142, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨142, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨142, by decide⟩ (listedAt ⟨142, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 3 (transLenTr ⟨53, by decide⟩ 3 hp)) T142_53
      hfix142_53 hinj142_53 hcardT142_53
      (fun i => conj_mem_of_fixedPoints _ _ (T142_53 i) (hfix142_53 i) _)
      ⟨142, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨142, by decide⟩ (Q2.listedAt ⟨142, by decide⟩
        (alnCheck_rep ⟨142, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 3 hp) Q2.T142_53_2 Q2.hfix142_53_2 Q2.hinj142_53_2
      Q2.hcardT142_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T142_53_2 i) (Q2.hfix142_53_2 i) _)
      colCert_142_53_3.hD ?_).symm
  rw [alnId_142 j hj]


theorem leaf_142_53_4 (hp : 4 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 142 []).length)
    (hq : (normIsRep.getD 142 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 4 hp)
        (rowE2 (⟨142, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 4 (transLenTr ⟨53, by decide⟩ 4 hp))
        (rowE1 (⟨142, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨142, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨142, by decide⟩ (listedAt ⟨142, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 4 (transLenTr ⟨53, by decide⟩ 4 hp)) T142_53
      hfix142_53 hinj142_53 hcardT142_53
      (fun i => conj_mem_of_fixedPoints _ _ (T142_53 i) (hfix142_53 i) _)
      ⟨142, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨142, by decide⟩ (Q2.listedAt ⟨142, by decide⟩
        (alnCheck_rep ⟨142, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 4 hp) Q2.T142_53_2 Q2.hfix142_53_2 Q2.hinj142_53_2
      Q2.hcardT142_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T142_53_2 i) (Q2.hfix142_53_2 i) _)
      colCert_142_53_4.hD ?_).symm
  rw [alnId_142 j hj]


theorem leaf_142_53_5 (hp : 5 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 142 []).length)
    (hq : (normIsRep.getD 142 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 5 hp)
        (rowE2 (⟨142, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 5 (transLenTr ⟨53, by decide⟩ 5 hp))
        (rowE1 (⟨142, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨142, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨142, by decide⟩ (listedAt ⟨142, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 5 (transLenTr ⟨53, by decide⟩ 5 hp)) T142_53
      hfix142_53 hinj142_53 hcardT142_53
      (fun i => conj_mem_of_fixedPoints _ _ (T142_53 i) (hfix142_53 i) _)
      ⟨142, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨142, by decide⟩ (Q2.listedAt ⟨142, by decide⟩
        (alnCheck_rep ⟨142, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 5 hp) Q2.T142_53_2 Q2.hfix142_53_2 Q2.hinj142_53_2
      Q2.hcardT142_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T142_53_2 i) (Q2.hfix142_53_2 i) _)
      colCert_142_53_5.hD ?_).symm
  rw [alnId_142 j hj]


theorem leaf_142_53_10 (hp : 10 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 142 []).length)
    (hq : (normIsRep.getD 142 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 10 hp)
        (rowE2 (⟨142, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 10 (transLenTr ⟨53, by decide⟩ 10 hp))
        (rowE1 (⟨142, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨142, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨142, by decide⟩ (listedAt ⟨142, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 10 (transLenTr ⟨53, by decide⟩ 10 hp)) T142_53
      hfix142_53 hinj142_53 hcardT142_53
      (fun i => conj_mem_of_fixedPoints _ _ (T142_53 i) (hfix142_53 i) _)
      ⟨142, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨142, by decide⟩ (Q2.listedAt ⟨142, by decide⟩
        (alnCheck_rep ⟨142, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 10 hp) Q2.T142_53_2 Q2.hfix142_53_2 Q2.hinj142_53_2
      Q2.hcardT142_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T142_53_2 i) (Q2.hfix142_53_2 i) _)
      colCert_142_53_10.hD ?_).symm
  rw [alnId_142 j hj]


theorem leaf_142_53_15 (hp : 15 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 142 []).length)
    (hq : (normIsRep.getD 142 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 15 hp)
        (rowE2 (⟨142, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 15 (transLenTr ⟨53, by decide⟩ 15 hp))
        (rowE1 (⟨142, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨142, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨142, by decide⟩ (listedAt ⟨142, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 15 (transLenTr ⟨53, by decide⟩ 15 hp)) T142_53
      hfix142_53 hinj142_53 hcardT142_53
      (fun i => conj_mem_of_fixedPoints _ _ (T142_53 i) (hfix142_53 i) _)
      ⟨142, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨142, by decide⟩ (Q2.listedAt ⟨142, by decide⟩
        (alnCheck_rep ⟨142, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 15 hp) Q2.T142_53_2 Q2.hfix142_53_2 Q2.hinj142_53_2
      Q2.hcardT142_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T142_53_2 i) (Q2.hfix142_53_2 i) _)
      colCert_142_53_15.hD ?_).symm
  rw [alnId_142 j hj]


theorem leaf_142_53_20 (hp : 20 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 142 []).length)
    (hq : (normIsRep.getD 142 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 20 hp)
        (rowE2 (⟨142, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 20 (transLenTr ⟨53, by decide⟩ 20 hp))
        (rowE1 (⟨142, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨142, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨142, by decide⟩ (listedAt ⟨142, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 20 (transLenTr ⟨53, by decide⟩ 20 hp)) T142_53
      hfix142_53 hinj142_53 hcardT142_53
      (fun i => conj_mem_of_fixedPoints _ _ (T142_53 i) (hfix142_53 i) _)
      ⟨142, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨142, by decide⟩ (Q2.listedAt ⟨142, by decide⟩
        (alnCheck_rep ⟨142, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 20 hp) Q2.T142_53_2 Q2.hfix142_53_2 Q2.hinj142_53_2
      Q2.hcardT142_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T142_53_2 i) (Q2.hfix142_53_2 i) _)
      colCert_142_53_20.hD ?_).symm
  rw [alnId_142 j hj]


theorem leaf_142_54_0 (hp : 0 < (Q2.transData.getD 54 []).length)
    (j : Nat) (hj : j < (repChars.getD 142 []).length)
    (hq : (normIsRep.getD 142 []).getD j false = true) :
    species (Q2.reps (⟨54, by decide⟩ : Fin 148)) (colE2 ⟨54, by decide⟩ 0 hp)
        (rowE2 (⟨142, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨54, by decide⟩ : Fin 148))
        (colE1 ⟨54, by decide⟩ 0 (transLenTr ⟨54, by decide⟩ 0 hp))
        (rowE1 (⟨142, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨142, by decide⟩ : Fin 148) ⟨54, by decide⟩ _
      (validAt ⟨142, by decide⟩ (listedAt ⟨142, by decide⟩ hj))
      (colE1 ⟨54, by decide⟩ 0 (transLenTr ⟨54, by decide⟩ 0 hp)) T142_54
      hfix142_54 hinj142_54 hcardT142_54
      (fun i => conj_mem_of_fixedPoints _ _ (T142_54 i) (hfix142_54 i) _)
      ⟨142, by decide⟩ ⟨54, by decide⟩ _
      (Q2.validAt ⟨142, by decide⟩ (Q2.listedAt ⟨142, by decide⟩
        (alnCheck_rep ⟨142, by decide⟩ hj hq).1))
      (colE2 ⟨54, by decide⟩ 0 hp) Q2.T142_54_2 Q2.hfix142_54_2 Q2.hinj142_54_2
      Q2.hcardT142_54_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T142_54_2 i) (Q2.hfix142_54_2 i) _)
      colCert_142_54_0.hD ?_).symm
  rw [alnId_142 j hj]


theorem leaf_142_54_1 (hp : 1 < (Q2.transData.getD 54 []).length)
    (j : Nat) (hj : j < (repChars.getD 142 []).length)
    (hq : (normIsRep.getD 142 []).getD j false = true) :
    species (Q2.reps (⟨54, by decide⟩ : Fin 148)) (colE2 ⟨54, by decide⟩ 1 hp)
        (rowE2 (⟨142, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨54, by decide⟩ : Fin 148))
        (colE1 ⟨54, by decide⟩ 1 (transLenTr ⟨54, by decide⟩ 1 hp))
        (rowE1 (⟨142, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨142, by decide⟩ : Fin 148) ⟨54, by decide⟩ _
      (validAt ⟨142, by decide⟩ (listedAt ⟨142, by decide⟩ hj))
      (colE1 ⟨54, by decide⟩ 1 (transLenTr ⟨54, by decide⟩ 1 hp)) T142_54
      hfix142_54 hinj142_54 hcardT142_54
      (fun i => conj_mem_of_fixedPoints _ _ (T142_54 i) (hfix142_54 i) _)
      ⟨142, by decide⟩ ⟨54, by decide⟩ _
      (Q2.validAt ⟨142, by decide⟩ (Q2.listedAt ⟨142, by decide⟩
        (alnCheck_rep ⟨142, by decide⟩ hj hq).1))
      (colE2 ⟨54, by decide⟩ 1 hp) Q2.T142_54_2 Q2.hfix142_54_2 Q2.hinj142_54_2
      Q2.hcardT142_54_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T142_54_2 i) (Q2.hfix142_54_2 i) _)
      colCert_142_54_1.hD ?_).symm
  rw [alnId_142 j hj]


theorem leaf_142_54_2 (hp : 2 < (Q2.transData.getD 54 []).length)
    (j : Nat) (hj : j < (repChars.getD 142 []).length)
    (hq : (normIsRep.getD 142 []).getD j false = true) :
    species (Q2.reps (⟨54, by decide⟩ : Fin 148)) (colE2 ⟨54, by decide⟩ 2 hp)
        (rowE2 (⟨142, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨54, by decide⟩ : Fin 148))
        (colE1 ⟨54, by decide⟩ 2 (transLenTr ⟨54, by decide⟩ 2 hp))
        (rowE1 (⟨142, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨142, by decide⟩ : Fin 148) ⟨54, by decide⟩ _
      (validAt ⟨142, by decide⟩ (listedAt ⟨142, by decide⟩ hj))
      (colE1 ⟨54, by decide⟩ 2 (transLenTr ⟨54, by decide⟩ 2 hp)) T142_54
      hfix142_54 hinj142_54 hcardT142_54
      (fun i => conj_mem_of_fixedPoints _ _ (T142_54 i) (hfix142_54 i) _)
      ⟨142, by decide⟩ ⟨54, by decide⟩ _
      (Q2.validAt ⟨142, by decide⟩ (Q2.listedAt ⟨142, by decide⟩
        (alnCheck_rep ⟨142, by decide⟩ hj hq).1))
      (colE2 ⟨54, by decide⟩ 2 hp) Q2.T142_54_2 Q2.hfix142_54_2 Q2.hinj142_54_2
      Q2.hcardT142_54_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T142_54_2 i) (Q2.hfix142_54_2 i) _)
      colCert_142_54_2.hD ?_).symm
  rw [alnId_142 j hj]


theorem leaf_142_54_3 (hp : 3 < (Q2.transData.getD 54 []).length)
    (j : Nat) (hj : j < (repChars.getD 142 []).length)
    (hq : (normIsRep.getD 142 []).getD j false = true) :
    species (Q2.reps (⟨54, by decide⟩ : Fin 148)) (colE2 ⟨54, by decide⟩ 3 hp)
        (rowE2 (⟨142, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨54, by decide⟩ : Fin 148))
        (colE1 ⟨54, by decide⟩ 3 (transLenTr ⟨54, by decide⟩ 3 hp))
        (rowE1 (⟨142, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨142, by decide⟩ : Fin 148) ⟨54, by decide⟩ _
      (validAt ⟨142, by decide⟩ (listedAt ⟨142, by decide⟩ hj))
      (colE1 ⟨54, by decide⟩ 3 (transLenTr ⟨54, by decide⟩ 3 hp)) T142_54
      hfix142_54 hinj142_54 hcardT142_54
      (fun i => conj_mem_of_fixedPoints _ _ (T142_54 i) (hfix142_54 i) _)
      ⟨142, by decide⟩ ⟨54, by decide⟩ _
      (Q2.validAt ⟨142, by decide⟩ (Q2.listedAt ⟨142, by decide⟩
        (alnCheck_rep ⟨142, by decide⟩ hj hq).1))
      (colE2 ⟨54, by decide⟩ 3 hp) Q2.T142_54_2 Q2.hfix142_54_2 Q2.hinj142_54_2
      Q2.hcardT142_54_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T142_54_2 i) (Q2.hfix142_54_2 i) _)
      colCert_142_54_3.hD ?_).symm
  rw [alnId_142 j hj]


theorem leaf_142_54_4 (hp : 4 < (Q2.transData.getD 54 []).length)
    (j : Nat) (hj : j < (repChars.getD 142 []).length)
    (hq : (normIsRep.getD 142 []).getD j false = true) :
    species (Q2.reps (⟨54, by decide⟩ : Fin 148)) (colE2 ⟨54, by decide⟩ 4 hp)
        (rowE2 (⟨142, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨54, by decide⟩ : Fin 148))
        (colE1 ⟨54, by decide⟩ 4 (transLenTr ⟨54, by decide⟩ 4 hp))
        (rowE1 (⟨142, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨142, by decide⟩ : Fin 148) ⟨54, by decide⟩ _
      (validAt ⟨142, by decide⟩ (listedAt ⟨142, by decide⟩ hj))
      (colE1 ⟨54, by decide⟩ 4 (transLenTr ⟨54, by decide⟩ 4 hp)) T142_54
      hfix142_54 hinj142_54 hcardT142_54
      (fun i => conj_mem_of_fixedPoints _ _ (T142_54 i) (hfix142_54 i) _)
      ⟨142, by decide⟩ ⟨54, by decide⟩ _
      (Q2.validAt ⟨142, by decide⟩ (Q2.listedAt ⟨142, by decide⟩
        (alnCheck_rep ⟨142, by decide⟩ hj hq).1))
      (colE2 ⟨54, by decide⟩ 4 hp) Q2.T142_54_2 Q2.hfix142_54_2 Q2.hinj142_54_2
      Q2.hcardT142_54_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T142_54_2 i) (Q2.hfix142_54_2 i) _)
      colCert_142_54_4.hD ?_).symm
  rw [alnId_142 j hj]


theorem leaf_142_54_5 (hp : 5 < (Q2.transData.getD 54 []).length)
    (j : Nat) (hj : j < (repChars.getD 142 []).length)
    (hq : (normIsRep.getD 142 []).getD j false = true) :
    species (Q2.reps (⟨54, by decide⟩ : Fin 148)) (colE2 ⟨54, by decide⟩ 5 hp)
        (rowE2 (⟨142, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨54, by decide⟩ : Fin 148))
        (colE1 ⟨54, by decide⟩ 5 (transLenTr ⟨54, by decide⟩ 5 hp))
        (rowE1 (⟨142, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨142, by decide⟩ : Fin 148) ⟨54, by decide⟩ _
      (validAt ⟨142, by decide⟩ (listedAt ⟨142, by decide⟩ hj))
      (colE1 ⟨54, by decide⟩ 5 (transLenTr ⟨54, by decide⟩ 5 hp)) T142_54
      hfix142_54 hinj142_54 hcardT142_54
      (fun i => conj_mem_of_fixedPoints _ _ (T142_54 i) (hfix142_54 i) _)
      ⟨142, by decide⟩ ⟨54, by decide⟩ _
      (Q2.validAt ⟨142, by decide⟩ (Q2.listedAt ⟨142, by decide⟩
        (alnCheck_rep ⟨142, by decide⟩ hj hq).1))
      (colE2 ⟨54, by decide⟩ 5 hp) Q2.T142_54_2 Q2.hfix142_54_2 Q2.hinj142_54_2
      Q2.hcardT142_54_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T142_54_2 i) (Q2.hfix142_54_2 i) _)
      colCert_142_54_5.hD ?_).symm
  rw [alnId_142 j hj]


end LeanDring.P5Presentation
