/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Data.ColCdd.C003
import LeanDring.P5.Data.ColCdd.C004
import LeanDring.P5.Data.ColRestCheap.C032
import LeanDring.P5.Data.ColRestCheap.C033
import LeanDring.P5.Data.ColRestCheap.C034
import LeanDring.P5.Data.ColRestCheap.C035
import LeanDring.P5.Data.ColTau.C001
import LeanDring.P5.Data.EntryK.C027
import LeanDring.P5.Certificate.RingIsomorphism.MatchCore
import LeanDring.P5.Data.SpeciesDiv.C033
import LeanDring.P5.Data.SpeciesDiv.C039
import LeanDring.P5.Data.SpeciesDiv.C040
import LeanDring.P5.Data.SpeciesDiv.C041
import LeanDring.P5.Certificate.SpeciesTable.Twin2.SpeciesTau.Chunk02

/-! # Stage-5 leaves, chunk 25 (auto-emitted).  -/

namespace LeanDring.P5Presentation

open MulAction Finset LeanDring.DRing LeanDring.MonGSet

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.style.longLine false

theorem leaf_118_45_5 (hp : 5 < (Q2.transData.getD 45 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨45, by decide⟩ : Fin 148)) (colE2 ⟨45, by decide⟩ 5 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨45, by decide⟩ : Fin 148))
        (colE1 ⟨45, by decide⟩ 5 (transLenTr ⟨45, by decide⟩ 5 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨118, by decide⟩ : Fin 148) ⟨45, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨45, by decide⟩ 5 (transLenTr ⟨45, by decide⟩ 5 hp)) T118_45
      hfix118_45 hinj118_45 hcardT118_45
      (fun i => conj_mem_of_fixedPoints _ _ (T118_45 i) (hfix118_45 i) _)
      ⟨118, by decide⟩ ⟨45, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨45, by decide⟩ 5 hp) Q2.T118_45_2 Q2.hfix118_45_2 Q2.hinj118_45_2
      Q2.hcardT118_45_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_45_2 i) (Q2.hfix118_45_2 i) _)
      ?_).symm
  rw [show colData1 (⟨118, by decide⟩ : Fin 148)
        ((colE1 ⟨45, by decide⟩ 5 (transLenTr ⟨45, by decide⟩ 5 hp) : ↥(reps ⟨45, by decide⟩)) : Coordinate 1)
        T118_45 = colFn colCertDiv_118_45_5.D1 (m := 5) from colCertDiv_118_45_5.bind1,
    show colData2 (⟨118, by decide⟩ : Fin 148)
        ((colE2 ⟨45, by decide⟩ 5 hp : ↥(Q2.reps ⟨45, by decide⟩)) : Coordinate 2)
        Q2.T118_45_2 = colFn colCertDiv_118_45_5.D2 (m := 5) from colCertDiv_118_45_5.bind2]
  rw [alnId_118 j hj]
  exact fastcode_of_div ⟨118, by decide⟩ _ _ _
    ((alnId_118 j hj) ▸ Q2.listedAt (⟨118, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨118, by decide⟩ : Fin 148) hj hq).1) colCertDiv_118_45_5_match


theorem leaf_118_45_10 (hp : 10 < (Q2.transData.getD 45 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨45, by decide⟩ : Fin 148)) (colE2 ⟨45, by decide⟩ 10 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨45, by decide⟩ : Fin 148))
        (colE1 ⟨45, by decide⟩ 10 (transLenTr ⟨45, by decide⟩ 10 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨118, by decide⟩ : Fin 148) ⟨45, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨45, by decide⟩ 10 (transLenTr ⟨45, by decide⟩ 10 hp)) T118_45
      hfix118_45 hinj118_45 hcardT118_45
      (fun i => conj_mem_of_fixedPoints _ _ (T118_45 i) (hfix118_45 i) _)
      ⟨118, by decide⟩ ⟨45, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨45, by decide⟩ 10 hp) Q2.T118_45_2 Q2.hfix118_45_2 Q2.hinj118_45_2
      Q2.hcardT118_45_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_45_2 i) (Q2.hfix118_45_2 i) _)
      ?_).symm
  rw [show colData1 (⟨118, by decide⟩ : Fin 148)
        ((colE1 ⟨45, by decide⟩ 10 (transLenTr ⟨45, by decide⟩ 10 hp) : ↥(reps ⟨45, by decide⟩)) : Coordinate 1)
        T118_45 = colFn colCertDiv_118_45_10.D1 (m := 5) from colCertDiv_118_45_10.bind1,
    show colData2 (⟨118, by decide⟩ : Fin 148)
        ((colE2 ⟨45, by decide⟩ 10 hp : ↥(Q2.reps ⟨45, by decide⟩)) : Coordinate 2)
        Q2.T118_45_2 = colFn colCertDiv_118_45_10.D2 (m := 5) from colCertDiv_118_45_10.bind2]
  rw [alnId_118 j hj]
  exact fastcode_of_div ⟨118, by decide⟩ _ _ _
    ((alnId_118 j hj) ▸ Q2.listedAt (⟨118, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨118, by decide⟩ : Fin 148) hj hq).1) colCertDiv_118_45_10_match


theorem leaf_118_45_15 (hp : 15 < (Q2.transData.getD 45 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨45, by decide⟩ : Fin 148)) (colE2 ⟨45, by decide⟩ 15 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨45, by decide⟩ : Fin 148))
        (colE1 ⟨45, by decide⟩ 15 (transLenTr ⟨45, by decide⟩ 15 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨118, by decide⟩ : Fin 148) ⟨45, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨45, by decide⟩ 15 (transLenTr ⟨45, by decide⟩ 15 hp)) T118_45
      hfix118_45 hinj118_45 hcardT118_45
      (fun i => conj_mem_of_fixedPoints _ _ (T118_45 i) (hfix118_45 i) _)
      ⟨118, by decide⟩ ⟨45, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨45, by decide⟩ 15 hp) Q2.T118_45_2 Q2.hfix118_45_2 Q2.hinj118_45_2
      Q2.hcardT118_45_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_45_2 i) (Q2.hfix118_45_2 i) _)
      ?_).symm
  rw [show colData1 (⟨118, by decide⟩ : Fin 148)
        ((colE1 ⟨45, by decide⟩ 15 (transLenTr ⟨45, by decide⟩ 15 hp) : ↥(reps ⟨45, by decide⟩)) : Coordinate 1)
        T118_45 = colFn colCertDiv_118_45_15.D1 (m := 5) from colCertDiv_118_45_15.bind1,
    show colData2 (⟨118, by decide⟩ : Fin 148)
        ((colE2 ⟨45, by decide⟩ 15 hp : ↥(Q2.reps ⟨45, by decide⟩)) : Coordinate 2)
        Q2.T118_45_2 = colFn colCertDiv_118_45_15.D2 (m := 5) from colCertDiv_118_45_15.bind2]
  rw [alnId_118 j hj]
  exact fastcode_of_div ⟨118, by decide⟩ _ _ _
    ((alnId_118 j hj) ▸ Q2.listedAt (⟨118, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨118, by decide⟩ : Fin 148) hj hq).1) colCertDiv_118_45_15_match


theorem leaf_118_45_20 (hp : 20 < (Q2.transData.getD 45 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨45, by decide⟩ : Fin 148)) (colE2 ⟨45, by decide⟩ 20 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨45, by decide⟩ : Fin 148))
        (colE1 ⟨45, by decide⟩ 20 (transLenTr ⟨45, by decide⟩ 20 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨118, by decide⟩ : Fin 148) ⟨45, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨45, by decide⟩ 20 (transLenTr ⟨45, by decide⟩ 20 hp)) T118_45
      hfix118_45 hinj118_45 hcardT118_45
      (fun i => conj_mem_of_fixedPoints _ _ (T118_45 i) (hfix118_45 i) _)
      ⟨118, by decide⟩ ⟨45, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨45, by decide⟩ 20 hp) Q2.T118_45_2 Q2.hfix118_45_2 Q2.hinj118_45_2
      Q2.hcardT118_45_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_45_2 i) (Q2.hfix118_45_2 i) _)
      ?_).symm
  rw [show colData1 (⟨118, by decide⟩ : Fin 148)
        ((colE1 ⟨45, by decide⟩ 20 (transLenTr ⟨45, by decide⟩ 20 hp) : ↥(reps ⟨45, by decide⟩)) : Coordinate 1)
        T118_45 = colFn colCertDiv_118_45_20.D1 (m := 5) from colCertDiv_118_45_20.bind1,
    show colData2 (⟨118, by decide⟩ : Fin 148)
        ((colE2 ⟨45, by decide⟩ 20 hp : ↥(Q2.reps ⟨45, by decide⟩)) : Coordinate 2)
        Q2.T118_45_2 = colFn colCertDiv_118_45_20.D2 (m := 5) from colCertDiv_118_45_20.bind2]
  rw [alnId_118 j hj]
  exact fastcode_of_div ⟨118, by decide⟩ _ _ _
    ((alnId_118 j hj) ▸ Q2.listedAt (⟨118, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨118, by decide⟩ : Fin 148) hj hq).1) colCertDiv_118_45_20_match


theorem leaf_118_50_0 (hp : 0 < (Q2.transData.getD 50 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨50, by decide⟩ : Fin 148)) (colE2 ⟨50, by decide⟩ 0 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨50, by decide⟩ : Fin 148))
        (colE1 ⟨50, by decide⟩ 0 (transLenTr ⟨50, by decide⟩ 0 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨50, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨50, by decide⟩ 0 (transLenTr ⟨50, by decide⟩ 0 hp)) T118_50
      hfix118_50 hinj118_50 hcardT118_50
      (fun i => conj_mem_of_fixedPoints _ _ (T118_50 i) (hfix118_50 i) _)
      ⟨118, by decide⟩ ⟨50, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨50, by decide⟩ 0 hp) Q2.T118_50_2 Q2.hfix118_50_2 Q2.hinj118_50_2
      Q2.hcardT118_50_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_50_2 i) (Q2.hfix118_50_2 i) _)
      colCert_118_50_0.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_50_1 (hp : 1 < (Q2.transData.getD 50 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨50, by decide⟩ : Fin 148)) (colE2 ⟨50, by decide⟩ 1 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨50, by decide⟩ : Fin 148))
        (colE1 ⟨50, by decide⟩ 1 (transLenTr ⟨50, by decide⟩ 1 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨50, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨50, by decide⟩ 1 (transLenTr ⟨50, by decide⟩ 1 hp)) T118_50
      hfix118_50 hinj118_50 hcardT118_50
      (fun i => conj_mem_of_fixedPoints _ _ (T118_50 i) (hfix118_50 i) _)
      ⟨118, by decide⟩ ⟨50, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨50, by decide⟩ 1 hp) Q2.T118_50_2 Q2.hfix118_50_2 Q2.hinj118_50_2
      Q2.hcardT118_50_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_50_2 i) (Q2.hfix118_50_2 i) _)
      colCert_118_50_1.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_50_2 (hp : 2 < (Q2.transData.getD 50 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨50, by decide⟩ : Fin 148)) (colE2 ⟨50, by decide⟩ 2 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨50, by decide⟩ : Fin 148))
        (colE1 ⟨50, by decide⟩ 2 (transLenTr ⟨50, by decide⟩ 2 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨50, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨50, by decide⟩ 2 (transLenTr ⟨50, by decide⟩ 2 hp)) T118_50
      hfix118_50 hinj118_50 hcardT118_50
      (fun i => conj_mem_of_fixedPoints _ _ (T118_50 i) (hfix118_50 i) _)
      ⟨118, by decide⟩ ⟨50, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨50, by decide⟩ 2 hp) Q2.T118_50_2 Q2.hfix118_50_2 Q2.hinj118_50_2
      Q2.hcardT118_50_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_50_2 i) (Q2.hfix118_50_2 i) _)
      colCert_118_50_2.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_50_3 (hp : 3 < (Q2.transData.getD 50 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨50, by decide⟩ : Fin 148)) (colE2 ⟨50, by decide⟩ 3 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨50, by decide⟩ : Fin 148))
        (colE1 ⟨50, by decide⟩ 3 (transLenTr ⟨50, by decide⟩ 3 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨50, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨50, by decide⟩ 3 (transLenTr ⟨50, by decide⟩ 3 hp)) T118_50
      hfix118_50 hinj118_50 hcardT118_50
      (fun i => conj_mem_of_fixedPoints _ _ (T118_50 i) (hfix118_50 i) _)
      ⟨118, by decide⟩ ⟨50, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨50, by decide⟩ 3 hp) Q2.T118_50_2 Q2.hfix118_50_2 Q2.hinj118_50_2
      Q2.hcardT118_50_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_50_2 i) (Q2.hfix118_50_2 i) _)
      colCert_118_50_3.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_50_4 (hp : 4 < (Q2.transData.getD 50 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨50, by decide⟩ : Fin 148)) (colE2 ⟨50, by decide⟩ 4 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨50, by decide⟩ : Fin 148))
        (colE1 ⟨50, by decide⟩ 4 (transLenTr ⟨50, by decide⟩ 4 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨50, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨50, by decide⟩ 4 (transLenTr ⟨50, by decide⟩ 4 hp)) T118_50
      hfix118_50 hinj118_50 hcardT118_50
      (fun i => conj_mem_of_fixedPoints _ _ (T118_50 i) (hfix118_50 i) _)
      ⟨118, by decide⟩ ⟨50, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨50, by decide⟩ 4 hp) Q2.T118_50_2 Q2.hfix118_50_2 Q2.hinj118_50_2
      Q2.hcardT118_50_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_50_2 i) (Q2.hfix118_50_2 i) _)
      colCert_118_50_4.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_50_5 (hp : 5 < (Q2.transData.getD 50 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨50, by decide⟩ : Fin 148)) (colE2 ⟨50, by decide⟩ 5 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨50, by decide⟩ : Fin 148))
        (colE1 ⟨50, by decide⟩ 5 (transLenTr ⟨50, by decide⟩ 5 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨118, by decide⟩ : Fin 148) ⟨50, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨50, by decide⟩ 5 (transLenTr ⟨50, by decide⟩ 5 hp)) T118_50
      hfix118_50 hinj118_50 hcardT118_50
      (fun i => conj_mem_of_fixedPoints _ _ (T118_50 i) (hfix118_50 i) _)
      ⟨118, by decide⟩ ⟨50, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨50, by decide⟩ 5 hp) Q2.T118_50_2 Q2.hfix118_50_2 Q2.hinj118_50_2
      Q2.hcardT118_50_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_50_2 i) (Q2.hfix118_50_2 i) _)
      ?_).symm
  rw [show colData1 (⟨118, by decide⟩ : Fin 148)
        ((colE1 ⟨50, by decide⟩ 5 (transLenTr ⟨50, by decide⟩ 5 hp) : ↥(reps ⟨50, by decide⟩)) : Coordinate 1)
        T118_50 = colFn colCertDiv_118_50_5.D1 (m := 5) from colCertDiv_118_50_5.bind1,
    show colData2 (⟨118, by decide⟩ : Fin 148)
        ((colE2 ⟨50, by decide⟩ 5 hp : ↥(Q2.reps ⟨50, by decide⟩)) : Coordinate 2)
        Q2.T118_50_2 = colFn colCertDiv_118_50_5.D2 (m := 5) from colCertDiv_118_50_5.bind2]
  rw [alnId_118 j hj]
  exact fastcode_of_div ⟨118, by decide⟩ _ _ _
    ((alnId_118 j hj) ▸ Q2.listedAt (⟨118, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨118, by decide⟩ : Fin 148) hj hq).1) colCertDiv_118_50_5_match


theorem leaf_118_50_10 (hp : 10 < (Q2.transData.getD 50 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨50, by decide⟩ : Fin 148)) (colE2 ⟨50, by decide⟩ 10 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨50, by decide⟩ : Fin 148))
        (colE1 ⟨50, by decide⟩ 10 (transLenTr ⟨50, by decide⟩ 10 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨118, by decide⟩ : Fin 148) ⟨50, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨50, by decide⟩ 10 (transLenTr ⟨50, by decide⟩ 10 hp)) T118_50
      hfix118_50 hinj118_50 hcardT118_50
      (fun i => conj_mem_of_fixedPoints _ _ (T118_50 i) (hfix118_50 i) _)
      ⟨118, by decide⟩ ⟨50, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨50, by decide⟩ 10 hp) Q2.T118_50_2 Q2.hfix118_50_2 Q2.hinj118_50_2
      Q2.hcardT118_50_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_50_2 i) (Q2.hfix118_50_2 i) _)
      ?_).symm
  rw [show colData1 (⟨118, by decide⟩ : Fin 148)
        ((colE1 ⟨50, by decide⟩ 10 (transLenTr ⟨50, by decide⟩ 10 hp) : ↥(reps ⟨50, by decide⟩)) : Coordinate 1)
        T118_50 = colFn colCertDiv_118_50_10.D1 (m := 5) from colCertDiv_118_50_10.bind1,
    show colData2 (⟨118, by decide⟩ : Fin 148)
        ((colE2 ⟨50, by decide⟩ 10 hp : ↥(Q2.reps ⟨50, by decide⟩)) : Coordinate 2)
        Q2.T118_50_2 = colFn colCertDiv_118_50_10.D2 (m := 5) from colCertDiv_118_50_10.bind2]
  rw [alnId_118 j hj]
  exact fastcode_of_div ⟨118, by decide⟩ _ _ _
    ((alnId_118 j hj) ▸ Q2.listedAt (⟨118, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨118, by decide⟩ : Fin 148) hj hq).1) colCertDiv_118_50_10_match


theorem leaf_118_50_15 (hp : 15 < (Q2.transData.getD 50 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨50, by decide⟩ : Fin 148)) (colE2 ⟨50, by decide⟩ 15 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨50, by decide⟩ : Fin 148))
        (colE1 ⟨50, by decide⟩ 15 (transLenTr ⟨50, by decide⟩ 15 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨118, by decide⟩ : Fin 148) ⟨50, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨50, by decide⟩ 15 (transLenTr ⟨50, by decide⟩ 15 hp)) T118_50
      hfix118_50 hinj118_50 hcardT118_50
      (fun i => conj_mem_of_fixedPoints _ _ (T118_50 i) (hfix118_50 i) _)
      ⟨118, by decide⟩ ⟨50, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨50, by decide⟩ 15 hp) Q2.T118_50_2 Q2.hfix118_50_2 Q2.hinj118_50_2
      Q2.hcardT118_50_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_50_2 i) (Q2.hfix118_50_2 i) _)
      ?_).symm
  rw [show colData1 (⟨118, by decide⟩ : Fin 148)
        ((colE1 ⟨50, by decide⟩ 15 (transLenTr ⟨50, by decide⟩ 15 hp) : ↥(reps ⟨50, by decide⟩)) : Coordinate 1)
        T118_50 = colFn colCertDiv_118_50_15.D1 (m := 5) from colCertDiv_118_50_15.bind1,
    show colData2 (⟨118, by decide⟩ : Fin 148)
        ((colE2 ⟨50, by decide⟩ 15 hp : ↥(Q2.reps ⟨50, by decide⟩)) : Coordinate 2)
        Q2.T118_50_2 = colFn colCertDiv_118_50_15.D2 (m := 5) from colCertDiv_118_50_15.bind2]
  rw [alnId_118 j hj]
  exact fastcode_of_div ⟨118, by decide⟩ _ _ _
    ((alnId_118 j hj) ▸ Q2.listedAt (⟨118, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨118, by decide⟩ : Fin 148) hj hq).1) colCertDiv_118_50_15_match


theorem leaf_118_50_20 (hp : 20 < (Q2.transData.getD 50 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨50, by decide⟩ : Fin 148)) (colE2 ⟨50, by decide⟩ 20 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨50, by decide⟩ : Fin 148))
        (colE1 ⟨50, by decide⟩ 20 (transLenTr ⟨50, by decide⟩ 20 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨118, by decide⟩ : Fin 148) ⟨50, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨50, by decide⟩ 20 (transLenTr ⟨50, by decide⟩ 20 hp)) T118_50
      hfix118_50 hinj118_50 hcardT118_50
      (fun i => conj_mem_of_fixedPoints _ _ (T118_50 i) (hfix118_50 i) _)
      ⟨118, by decide⟩ ⟨50, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨50, by decide⟩ 20 hp) Q2.T118_50_2 Q2.hfix118_50_2 Q2.hinj118_50_2
      Q2.hcardT118_50_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_50_2 i) (Q2.hfix118_50_2 i) _)
      ?_).symm
  rw [show colData1 (⟨118, by decide⟩ : Fin 148)
        ((colE1 ⟨50, by decide⟩ 20 (transLenTr ⟨50, by decide⟩ 20 hp) : ↥(reps ⟨50, by decide⟩)) : Coordinate 1)
        T118_50 = colFn colCertDiv_118_50_20.D1 (m := 5) from colCertDiv_118_50_20.bind1,
    show colData2 (⟨118, by decide⟩ : Fin 148)
        ((colE2 ⟨50, by decide⟩ 20 hp : ↥(Q2.reps ⟨50, by decide⟩)) : Coordinate 2)
        Q2.T118_50_2 = colFn colCertDiv_118_50_20.D2 (m := 5) from colCertDiv_118_50_20.bind2]
  rw [alnId_118 j hj]
  exact fastcode_of_div ⟨118, by decide⟩ _ _ _
    ((alnId_118 j hj) ▸ Q2.listedAt (⟨118, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨118, by decide⟩ : Fin 148) hj hq).1) colCertDiv_118_50_20_match


theorem leaf_118_53_0 (hp : 0 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 0 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 0 (transLenTr ⟨53, by decide⟩ 0 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 0 (transLenTr ⟨53, by decide⟩ 0 hp)) T118_53
      hfix118_53 hinj118_53 hcardT118_53
      (fun i => conj_mem_of_fixedPoints _ _ (T118_53 i) (hfix118_53 i) _)
      ⟨118, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 0 hp) Q2.T118_53_2 Q2.hfix118_53_2 Q2.hinj118_53_2
      Q2.hcardT118_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_53_2 i) (Q2.hfix118_53_2 i) _)
      colCert_118_53_0.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_53_1 (hp : 1 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 1 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 1 (transLenTr ⟨53, by decide⟩ 1 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 1 (transLenTr ⟨53, by decide⟩ 1 hp)) T118_53
      hfix118_53 hinj118_53 hcardT118_53
      (fun i => conj_mem_of_fixedPoints _ _ (T118_53 i) (hfix118_53 i) _)
      ⟨118, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 1 hp) Q2.T118_53_2 Q2.hfix118_53_2 Q2.hinj118_53_2
      Q2.hcardT118_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_53_2 i) (Q2.hfix118_53_2 i) _)
      colCert_118_53_1.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_53_2 (hp : 2 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 2 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 2 (transLenTr ⟨53, by decide⟩ 2 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 2 (transLenTr ⟨53, by decide⟩ 2 hp)) T118_53
      hfix118_53 hinj118_53 hcardT118_53
      (fun i => conj_mem_of_fixedPoints _ _ (T118_53 i) (hfix118_53 i) _)
      ⟨118, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 2 hp) Q2.T118_53_2 Q2.hfix118_53_2 Q2.hinj118_53_2
      Q2.hcardT118_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_53_2 i) (Q2.hfix118_53_2 i) _)
      colCert_118_53_2.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_53_3 (hp : 3 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 3 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 3 (transLenTr ⟨53, by decide⟩ 3 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 3 (transLenTr ⟨53, by decide⟩ 3 hp)) T118_53
      hfix118_53 hinj118_53 hcardT118_53
      (fun i => conj_mem_of_fixedPoints _ _ (T118_53 i) (hfix118_53 i) _)
      ⟨118, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 3 hp) Q2.T118_53_2 Q2.hfix118_53_2 Q2.hinj118_53_2
      Q2.hcardT118_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_53_2 i) (Q2.hfix118_53_2 i) _)
      colCert_118_53_3.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_53_4 (hp : 4 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 4 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 4 (transLenTr ⟨53, by decide⟩ 4 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 4 (transLenTr ⟨53, by decide⟩ 4 hp)) T118_53
      hfix118_53 hinj118_53 hcardT118_53
      (fun i => conj_mem_of_fixedPoints _ _ (T118_53 i) (hfix118_53 i) _)
      ⟨118, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 4 hp) Q2.T118_53_2 Q2.hfix118_53_2 Q2.hinj118_53_2
      Q2.hcardT118_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_53_2 i) (Q2.hfix118_53_2 i) _)
      colCert_118_53_4.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_53_5 (hp : 5 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 5 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 5 (transLenTr ⟨53, by decide⟩ 5 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 5 (transLenTr ⟨53, by decide⟩ 5 hp)) T118_53
      hfix118_53 hinj118_53 hcardT118_53
      (fun i => conj_mem_of_fixedPoints _ _ (T118_53 i) (hfix118_53 i) _)
      ⟨118, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 5 hp) Q2.T118_53_2 Q2.hfix118_53_2 Q2.hinj118_53_2
      Q2.hcardT118_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_53_2 i) (Q2.hfix118_53_2 i) _)
      colCert_118_53_5.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_53_10 (hp : 10 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 10 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 10 (transLenTr ⟨53, by decide⟩ 10 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 10 (transLenTr ⟨53, by decide⟩ 10 hp)) T118_53
      hfix118_53 hinj118_53 hcardT118_53
      (fun i => conj_mem_of_fixedPoints _ _ (T118_53 i) (hfix118_53 i) _)
      ⟨118, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 10 hp) Q2.T118_53_2 Q2.hfix118_53_2 Q2.hinj118_53_2
      Q2.hcardT118_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_53_2 i) (Q2.hfix118_53_2 i) _)
      colCert_118_53_10.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_53_15 (hp : 15 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 15 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 15 (transLenTr ⟨53, by decide⟩ 15 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 15 (transLenTr ⟨53, by decide⟩ 15 hp)) T118_53
      hfix118_53 hinj118_53 hcardT118_53
      (fun i => conj_mem_of_fixedPoints _ _ (T118_53 i) (hfix118_53 i) _)
      ⟨118, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 15 hp) Q2.T118_53_2 Q2.hfix118_53_2 Q2.hinj118_53_2
      Q2.hcardT118_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_53_2 i) (Q2.hfix118_53_2 i) _)
      colCert_118_53_15.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_53_20 (hp : 20 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 20 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 20 (transLenTr ⟨53, by decide⟩ 20 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 20 (transLenTr ⟨53, by decide⟩ 20 hp)) T118_53
      hfix118_53 hinj118_53 hcardT118_53
      (fun i => conj_mem_of_fixedPoints _ _ (T118_53 i) (hfix118_53 i) _)
      ⟨118, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 20 hp) Q2.T118_53_2 Q2.hfix118_53_2 Q2.hinj118_53_2
      Q2.hcardT118_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_53_2 i) (Q2.hfix118_53_2 i) _)
      colCert_118_53_20.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_65_0 (hp : 0 < (Q2.transData.getD 65 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨65, by decide⟩ : Fin 148)) (colE2 ⟨65, by decide⟩ 0 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨65, by decide⟩ : Fin 148))
        (colE1 ⟨65, by decide⟩ 0 (transLenTr ⟨65, by decide⟩ 0 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨65, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨65, by decide⟩ 0 (transLenTr ⟨65, by decide⟩ 0 hp)) T118_65
      hfix118_65 hinj118_65 hcardT118_65
      (fun i => conj_mem_of_fixedPoints _ _ (T118_65 i) (hfix118_65 i) _)
      ⟨118, by decide⟩ ⟨65, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨65, by decide⟩ 0 hp) Q2.T118_65_2 Q2.hfix118_65_2 Q2.hinj118_65_2
      Q2.hcardT118_65_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_65_2 i) (Q2.hfix118_65_2 i) _)
      colCert_118_65_0.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_65_1 (hp : 1 < (Q2.transData.getD 65 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨65, by decide⟩ : Fin 148)) (colE2 ⟨65, by decide⟩ 1 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨65, by decide⟩ : Fin 148))
        (colE1 ⟨65, by decide⟩ 1 (transLenTr ⟨65, by decide⟩ 1 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨65, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨65, by decide⟩ 1 (transLenTr ⟨65, by decide⟩ 1 hp)) T118_65
      hfix118_65 hinj118_65 hcardT118_65
      (fun i => conj_mem_of_fixedPoints _ _ (T118_65 i) (hfix118_65 i) _)
      ⟨118, by decide⟩ ⟨65, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨65, by decide⟩ 1 hp) Q2.T118_65_2 Q2.hfix118_65_2 Q2.hinj118_65_2
      Q2.hcardT118_65_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_65_2 i) (Q2.hfix118_65_2 i) _)
      colCert_118_65_1.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_65_2 (hp : 2 < (Q2.transData.getD 65 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨65, by decide⟩ : Fin 148)) (colE2 ⟨65, by decide⟩ 2 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨65, by decide⟩ : Fin 148))
        (colE1 ⟨65, by decide⟩ 2 (transLenTr ⟨65, by decide⟩ 2 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨65, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨65, by decide⟩ 2 (transLenTr ⟨65, by decide⟩ 2 hp)) T118_65
      hfix118_65 hinj118_65 hcardT118_65
      (fun i => conj_mem_of_fixedPoints _ _ (T118_65 i) (hfix118_65 i) _)
      ⟨118, by decide⟩ ⟨65, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨65, by decide⟩ 2 hp) Q2.T118_65_2 Q2.hfix118_65_2 Q2.hinj118_65_2
      Q2.hcardT118_65_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_65_2 i) (Q2.hfix118_65_2 i) _)
      colCert_118_65_2.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_65_3 (hp : 3 < (Q2.transData.getD 65 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨65, by decide⟩ : Fin 148)) (colE2 ⟨65, by decide⟩ 3 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨65, by decide⟩ : Fin 148))
        (colE1 ⟨65, by decide⟩ 3 (transLenTr ⟨65, by decide⟩ 3 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨65, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨65, by decide⟩ 3 (transLenTr ⟨65, by decide⟩ 3 hp)) T118_65
      hfix118_65 hinj118_65 hcardT118_65
      (fun i => conj_mem_of_fixedPoints _ _ (T118_65 i) (hfix118_65 i) _)
      ⟨118, by decide⟩ ⟨65, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨65, by decide⟩ 3 hp) Q2.T118_65_2 Q2.hfix118_65_2 Q2.hinj118_65_2
      Q2.hcardT118_65_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_65_2 i) (Q2.hfix118_65_2 i) _)
      colCert_118_65_3.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_65_4 (hp : 4 < (Q2.transData.getD 65 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨65, by decide⟩ : Fin 148)) (colE2 ⟨65, by decide⟩ 4 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨65, by decide⟩ : Fin 148))
        (colE1 ⟨65, by decide⟩ 4 (transLenTr ⟨65, by decide⟩ 4 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨65, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨65, by decide⟩ 4 (transLenTr ⟨65, by decide⟩ 4 hp)) T118_65
      hfix118_65 hinj118_65 hcardT118_65
      (fun i => conj_mem_of_fixedPoints _ _ (T118_65 i) (hfix118_65 i) _)
      ⟨118, by decide⟩ ⟨65, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨65, by decide⟩ 4 hp) Q2.T118_65_2 Q2.hfix118_65_2 Q2.hinj118_65_2
      Q2.hcardT118_65_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_65_2 i) (Q2.hfix118_65_2 i) _)
      colCert_118_65_4.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_65_5 (hp : 5 < (Q2.transData.getD 65 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨65, by decide⟩ : Fin 148)) (colE2 ⟨65, by decide⟩ 5 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨65, by decide⟩ : Fin 148))
        (colE1 ⟨65, by decide⟩ 5 (transLenTr ⟨65, by decide⟩ 5 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨118, by decide⟩ : Fin 148) ⟨65, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨65, by decide⟩ 5 (transLenTr ⟨65, by decide⟩ 5 hp)) T118_65
      hfix118_65 hinj118_65 hcardT118_65
      (fun i => conj_mem_of_fixedPoints _ _ (T118_65 i) (hfix118_65 i) _)
      ⟨118, by decide⟩ ⟨65, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨65, by decide⟩ 5 hp) Q2.T118_65_2 Q2.hfix118_65_2 Q2.hinj118_65_2
      Q2.hcardT118_65_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_65_2 i) (Q2.hfix118_65_2 i) _)
      ?_).symm
  rw [show colData1 (⟨118, by decide⟩ : Fin 148)
        ((colE1 ⟨65, by decide⟩ 5 (transLenTr ⟨65, by decide⟩ 5 hp) : ↥(reps ⟨65, by decide⟩)) : Coordinate 1)
        T118_65 = colFn colCertDiv_118_65_5.D1 (m := 5) from colCertDiv_118_65_5.bind1,
    show colData2 (⟨118, by decide⟩ : Fin 148)
        ((colE2 ⟨65, by decide⟩ 5 hp : ↥(Q2.reps ⟨65, by decide⟩)) : Coordinate 2)
        Q2.T118_65_2 = colFn colCertDiv_118_65_5.D2 (m := 5) from colCertDiv_118_65_5.bind2]
  rw [alnId_118 j hj]
  exact fastcode_of_div ⟨118, by decide⟩ _ _ _
    ((alnId_118 j hj) ▸ Q2.listedAt (⟨118, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨118, by decide⟩ : Fin 148) hj hq).1) colCertDiv_118_65_5_match


theorem leaf_118_65_6 (hp : 6 < (Q2.transData.getD 65 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨65, by decide⟩ : Fin 148)) (colE2 ⟨65, by decide⟩ 6 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨65, by decide⟩ : Fin 148))
        (colE1 ⟨65, by decide⟩ 6 (transLenTr ⟨65, by decide⟩ 6 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨118, by decide⟩ : Fin 148) ⟨65, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨65, by decide⟩ 6 (transLenTr ⟨65, by decide⟩ 6 hp)) T118_65
      hfix118_65 hinj118_65 hcardT118_65
      (fun i => conj_mem_of_fixedPoints _ _ (T118_65 i) (hfix118_65 i) _)
      ⟨118, by decide⟩ ⟨65, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨65, by decide⟩ 6 hp) Q2.T118_65_2 Q2.hfix118_65_2 Q2.hinj118_65_2
      Q2.hcardT118_65_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_65_2 i) (Q2.hfix118_65_2 i) _)
      ?_).symm
  rw [show colData1 (⟨118, by decide⟩ : Fin 148)
        ((colE1 ⟨65, by decide⟩ 6 (transLenTr ⟨65, by decide⟩ 6 hp) : ↥(reps ⟨65, by decide⟩)) : Coordinate 1)
        T118_65 = colFn colCertDiv_118_65_6.D1 (m := 5) from colCertDiv_118_65_6.bind1,
    show colData2 (⟨118, by decide⟩ : Fin 148)
        ((colE2 ⟨65, by decide⟩ 6 hp : ↥(Q2.reps ⟨65, by decide⟩)) : Coordinate 2)
        Q2.T118_65_2 = colFn colCertDiv_118_65_6.D2 (m := 5) from colCertDiv_118_65_6.bind2]
  rw [alnId_118 j hj]
  exact fastcode_of_div ⟨118, by decide⟩ _ _ _
    ((alnId_118 j hj) ▸ Q2.listedAt (⟨118, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨118, by decide⟩ : Fin 148) hj hq).1) colCertDiv_118_65_6_match


theorem leaf_118_65_7 (hp : 7 < (Q2.transData.getD 65 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨65, by decide⟩ : Fin 148)) (colE2 ⟨65, by decide⟩ 7 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨65, by decide⟩ : Fin 148))
        (colE1 ⟨65, by decide⟩ 7 (transLenTr ⟨65, by decide⟩ 7 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨118, by decide⟩ : Fin 148) ⟨65, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨65, by decide⟩ 7 (transLenTr ⟨65, by decide⟩ 7 hp)) T118_65
      hfix118_65 hinj118_65 hcardT118_65
      (fun i => conj_mem_of_fixedPoints _ _ (T118_65 i) (hfix118_65 i) _)
      ⟨118, by decide⟩ ⟨65, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨65, by decide⟩ 7 hp) Q2.T118_65_2 Q2.hfix118_65_2 Q2.hinj118_65_2
      Q2.hcardT118_65_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_65_2 i) (Q2.hfix118_65_2 i) _)
      ?_).symm
  rw [show colData1 (⟨118, by decide⟩ : Fin 148)
        ((colE1 ⟨65, by decide⟩ 7 (transLenTr ⟨65, by decide⟩ 7 hp) : ↥(reps ⟨65, by decide⟩)) : Coordinate 1)
        T118_65 = colFn colCertDiv_118_65_7.D1 (m := 5) from colCertDiv_118_65_7.bind1,
    show colData2 (⟨118, by decide⟩ : Fin 148)
        ((colE2 ⟨65, by decide⟩ 7 hp : ↥(Q2.reps ⟨65, by decide⟩)) : Coordinate 2)
        Q2.T118_65_2 = colFn colCertDiv_118_65_7.D2 (m := 5) from colCertDiv_118_65_7.bind2]
  rw [alnId_118 j hj]
  exact fastcode_of_div ⟨118, by decide⟩ _ _ _
    ((alnId_118 j hj) ▸ Q2.listedAt (⟨118, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨118, by decide⟩ : Fin 148) hj hq).1) colCertDiv_118_65_7_match


theorem leaf_118_65_8 (hp : 8 < (Q2.transData.getD 65 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨65, by decide⟩ : Fin 148)) (colE2 ⟨65, by decide⟩ 8 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨65, by decide⟩ : Fin 148))
        (colE1 ⟨65, by decide⟩ 8 (transLenTr ⟨65, by decide⟩ 8 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨118, by decide⟩ : Fin 148) ⟨65, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨65, by decide⟩ 8 (transLenTr ⟨65, by decide⟩ 8 hp)) T118_65
      hfix118_65 hinj118_65 hcardT118_65
      (fun i => conj_mem_of_fixedPoints _ _ (T118_65 i) (hfix118_65 i) _)
      ⟨118, by decide⟩ ⟨65, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨65, by decide⟩ 8 hp) Q2.T118_65_2 Q2.hfix118_65_2 Q2.hinj118_65_2
      Q2.hcardT118_65_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_65_2 i) (Q2.hfix118_65_2 i) _)
      ?_).symm
  rw [show colData1 (⟨118, by decide⟩ : Fin 148)
        ((colE1 ⟨65, by decide⟩ 8 (transLenTr ⟨65, by decide⟩ 8 hp) : ↥(reps ⟨65, by decide⟩)) : Coordinate 1)
        T118_65 = colFn colCertDiv_118_65_8.D1 (m := 5) from colCertDiv_118_65_8.bind1,
    show colData2 (⟨118, by decide⟩ : Fin 148)
        ((colE2 ⟨65, by decide⟩ 8 hp : ↥(Q2.reps ⟨65, by decide⟩)) : Coordinate 2)
        Q2.T118_65_2 = colFn colCertDiv_118_65_8.D2 (m := 5) from colCertDiv_118_65_8.bind2]
  rw [alnId_118 j hj]
  exact fastcode_of_div ⟨118, by decide⟩ _ _ _
    ((alnId_118 j hj) ▸ Q2.listedAt (⟨118, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨118, by decide⟩ : Fin 148) hj hq).1) colCertDiv_118_65_8_match


theorem leaf_118_65_9 (hp : 9 < (Q2.transData.getD 65 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨65, by decide⟩ : Fin 148)) (colE2 ⟨65, by decide⟩ 9 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨65, by decide⟩ : Fin 148))
        (colE1 ⟨65, by decide⟩ 9 (transLenTr ⟨65, by decide⟩ 9 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨118, by decide⟩ : Fin 148) ⟨65, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨65, by decide⟩ 9 (transLenTr ⟨65, by decide⟩ 9 hp)) T118_65
      hfix118_65 hinj118_65 hcardT118_65
      (fun i => conj_mem_of_fixedPoints _ _ (T118_65 i) (hfix118_65 i) _)
      ⟨118, by decide⟩ ⟨65, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨65, by decide⟩ 9 hp) Q2.T118_65_2 Q2.hfix118_65_2 Q2.hinj118_65_2
      Q2.hcardT118_65_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_65_2 i) (Q2.hfix118_65_2 i) _)
      ?_).symm
  rw [show colData1 (⟨118, by decide⟩ : Fin 148)
        ((colE1 ⟨65, by decide⟩ 9 (transLenTr ⟨65, by decide⟩ 9 hp) : ↥(reps ⟨65, by decide⟩)) : Coordinate 1)
        T118_65 = colFn colCertDiv_118_65_9.D1 (m := 5) from colCertDiv_118_65_9.bind1,
    show colData2 (⟨118, by decide⟩ : Fin 148)
        ((colE2 ⟨65, by decide⟩ 9 hp : ↥(Q2.reps ⟨65, by decide⟩)) : Coordinate 2)
        Q2.T118_65_2 = colFn colCertDiv_118_65_9.D2 (m := 5) from colCertDiv_118_65_9.bind2]
  rw [alnId_118 j hj]
  exact fastcode_of_div ⟨118, by decide⟩ _ _ _
    ((alnId_118 j hj) ▸ Q2.listedAt (⟨118, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨118, by decide⟩ : Fin 148) hj hq).1) colCertDiv_118_65_9_match


theorem leaf_118_65_10 (hp : 10 < (Q2.transData.getD 65 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨65, by decide⟩ : Fin 148)) (colE2 ⟨65, by decide⟩ 10 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨65, by decide⟩ : Fin 148))
        (colE1 ⟨65, by decide⟩ 10 (transLenTr ⟨65, by decide⟩ 10 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨118, by decide⟩ : Fin 148) ⟨65, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨65, by decide⟩ 10 (transLenTr ⟨65, by decide⟩ 10 hp)) T118_65
      hfix118_65 hinj118_65 hcardT118_65
      (fun i => conj_mem_of_fixedPoints _ _ (T118_65 i) (hfix118_65 i) _)
      ⟨118, by decide⟩ ⟨65, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨65, by decide⟩ 10 hp) Q2.T118_65_2 Q2.hfix118_65_2 Q2.hinj118_65_2
      Q2.hcardT118_65_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_65_2 i) (Q2.hfix118_65_2 i) _)
      ?_).symm
  rw [show colData1 (⟨118, by decide⟩ : Fin 148)
        ((colE1 ⟨65, by decide⟩ 10 (transLenTr ⟨65, by decide⟩ 10 hp) : ↥(reps ⟨65, by decide⟩)) : Coordinate 1)
        T118_65 = colFn colCertDiv_118_65_10.D1 (m := 5) from colCertDiv_118_65_10.bind1,
    show colData2 (⟨118, by decide⟩ : Fin 148)
        ((colE2 ⟨65, by decide⟩ 10 hp : ↥(Q2.reps ⟨65, by decide⟩)) : Coordinate 2)
        Q2.T118_65_2 = colFn colCertDiv_118_65_10.D2 (m := 5) from colCertDiv_118_65_10.bind2]
  rw [alnId_118 j hj]
  exact fastcode_of_div ⟨118, by decide⟩ _ _ _
    ((alnId_118 j hj) ▸ Q2.listedAt (⟨118, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨118, by decide⟩ : Fin 148) hj hq).1) colCertDiv_118_65_10_match


theorem leaf_118_65_11 (hp : 11 < (Q2.transData.getD 65 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨65, by decide⟩ : Fin 148)) (colE2 ⟨65, by decide⟩ 11 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨65, by decide⟩ : Fin 148))
        (colE1 ⟨65, by decide⟩ 11 (transLenTr ⟨65, by decide⟩ 11 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨118, by decide⟩ : Fin 148) ⟨65, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨65, by decide⟩ 11 (transLenTr ⟨65, by decide⟩ 11 hp)) T118_65
      hfix118_65 hinj118_65 hcardT118_65
      (fun i => conj_mem_of_fixedPoints _ _ (T118_65 i) (hfix118_65 i) _)
      ⟨118, by decide⟩ ⟨65, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨65, by decide⟩ 11 hp) Q2.T118_65_2 Q2.hfix118_65_2 Q2.hinj118_65_2
      Q2.hcardT118_65_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_65_2 i) (Q2.hfix118_65_2 i) _)
      ?_).symm
  rw [show colData1 (⟨118, by decide⟩ : Fin 148)
        ((colE1 ⟨65, by decide⟩ 11 (transLenTr ⟨65, by decide⟩ 11 hp) : ↥(reps ⟨65, by decide⟩)) : Coordinate 1)
        T118_65 = colFn colCertDiv_118_65_11.D1 (m := 5) from colCertDiv_118_65_11.bind1,
    show colData2 (⟨118, by decide⟩ : Fin 148)
        ((colE2 ⟨65, by decide⟩ 11 hp : ↥(Q2.reps ⟨65, by decide⟩)) : Coordinate 2)
        Q2.T118_65_2 = colFn colCertDiv_118_65_11.D2 (m := 5) from colCertDiv_118_65_11.bind2]
  rw [alnId_118 j hj]
  exact fastcode_of_div ⟨118, by decide⟩ _ _ _
    ((alnId_118 j hj) ▸ Q2.listedAt (⟨118, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨118, by decide⟩ : Fin 148) hj hq).1) colCertDiv_118_65_11_match


theorem leaf_118_65_12 (hp : 12 < (Q2.transData.getD 65 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨65, by decide⟩ : Fin 148)) (colE2 ⟨65, by decide⟩ 12 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨65, by decide⟩ : Fin 148))
        (colE1 ⟨65, by decide⟩ 12 (transLenTr ⟨65, by decide⟩ 12 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨118, by decide⟩ : Fin 148) ⟨65, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨65, by decide⟩ 12 (transLenTr ⟨65, by decide⟩ 12 hp)) T118_65
      hfix118_65 hinj118_65 hcardT118_65
      (fun i => conj_mem_of_fixedPoints _ _ (T118_65 i) (hfix118_65 i) _)
      ⟨118, by decide⟩ ⟨65, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨65, by decide⟩ 12 hp) Q2.T118_65_2 Q2.hfix118_65_2 Q2.hinj118_65_2
      Q2.hcardT118_65_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_65_2 i) (Q2.hfix118_65_2 i) _)
      ?_).symm
  rw [show colData1 (⟨118, by decide⟩ : Fin 148)
        ((colE1 ⟨65, by decide⟩ 12 (transLenTr ⟨65, by decide⟩ 12 hp) : ↥(reps ⟨65, by decide⟩)) : Coordinate 1)
        T118_65 = colFn colCertDiv_118_65_12.D1 (m := 5) from colCertDiv_118_65_12.bind1,
    show colData2 (⟨118, by decide⟩ : Fin 148)
        ((colE2 ⟨65, by decide⟩ 12 hp : ↥(Q2.reps ⟨65, by decide⟩)) : Coordinate 2)
        Q2.T118_65_2 = colFn colCertDiv_118_65_12.D2 (m := 5) from colCertDiv_118_65_12.bind2]
  rw [alnId_118 j hj]
  exact fastcode_of_div ⟨118, by decide⟩ _ _ _
    ((alnId_118 j hj) ▸ Q2.listedAt (⟨118, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨118, by decide⟩ : Fin 148) hj hq).1) colCertDiv_118_65_12_match


theorem leaf_118_65_13 (hp : 13 < (Q2.transData.getD 65 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨65, by decide⟩ : Fin 148)) (colE2 ⟨65, by decide⟩ 13 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨65, by decide⟩ : Fin 148))
        (colE1 ⟨65, by decide⟩ 13 (transLenTr ⟨65, by decide⟩ 13 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨118, by decide⟩ : Fin 148) ⟨65, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨65, by decide⟩ 13 (transLenTr ⟨65, by decide⟩ 13 hp)) T118_65
      hfix118_65 hinj118_65 hcardT118_65
      (fun i => conj_mem_of_fixedPoints _ _ (T118_65 i) (hfix118_65 i) _)
      ⟨118, by decide⟩ ⟨65, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨65, by decide⟩ 13 hp) Q2.T118_65_2 Q2.hfix118_65_2 Q2.hinj118_65_2
      Q2.hcardT118_65_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_65_2 i) (Q2.hfix118_65_2 i) _)
      ?_).symm
  rw [show colData1 (⟨118, by decide⟩ : Fin 148)
        ((colE1 ⟨65, by decide⟩ 13 (transLenTr ⟨65, by decide⟩ 13 hp) : ↥(reps ⟨65, by decide⟩)) : Coordinate 1)
        T118_65 = colFn colCertDiv_118_65_13.D1 (m := 5) from colCertDiv_118_65_13.bind1,
    show colData2 (⟨118, by decide⟩ : Fin 148)
        ((colE2 ⟨65, by decide⟩ 13 hp : ↥(Q2.reps ⟨65, by decide⟩)) : Coordinate 2)
        Q2.T118_65_2 = colFn colCertDiv_118_65_13.D2 (m := 5) from colCertDiv_118_65_13.bind2]
  rw [alnId_118 j hj]
  exact fastcode_of_div ⟨118, by decide⟩ _ _ _
    ((alnId_118 j hj) ▸ Q2.listedAt (⟨118, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨118, by decide⟩ : Fin 148) hj hq).1) colCertDiv_118_65_13_match


theorem leaf_118_65_14 (hp : 14 < (Q2.transData.getD 65 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨65, by decide⟩ : Fin 148)) (colE2 ⟨65, by decide⟩ 14 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨65, by decide⟩ : Fin 148))
        (colE1 ⟨65, by decide⟩ 14 (transLenTr ⟨65, by decide⟩ 14 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨118, by decide⟩ : Fin 148) ⟨65, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨65, by decide⟩ 14 (transLenTr ⟨65, by decide⟩ 14 hp)) T118_65
      hfix118_65 hinj118_65 hcardT118_65
      (fun i => conj_mem_of_fixedPoints _ _ (T118_65 i) (hfix118_65 i) _)
      ⟨118, by decide⟩ ⟨65, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨65, by decide⟩ 14 hp) Q2.T118_65_2 Q2.hfix118_65_2 Q2.hinj118_65_2
      Q2.hcardT118_65_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_65_2 i) (Q2.hfix118_65_2 i) _)
      ?_).symm
  rw [show colData1 (⟨118, by decide⟩ : Fin 148)
        ((colE1 ⟨65, by decide⟩ 14 (transLenTr ⟨65, by decide⟩ 14 hp) : ↥(reps ⟨65, by decide⟩)) : Coordinate 1)
        T118_65 = colFn colCertDiv_118_65_14.D1 (m := 5) from colCertDiv_118_65_14.bind1,
    show colData2 (⟨118, by decide⟩ : Fin 148)
        ((colE2 ⟨65, by decide⟩ 14 hp : ↥(Q2.reps ⟨65, by decide⟩)) : Coordinate 2)
        Q2.T118_65_2 = colFn colCertDiv_118_65_14.D2 (m := 5) from colCertDiv_118_65_14.bind2]
  rw [alnId_118 j hj]
  exact fastcode_of_div ⟨118, by decide⟩ _ _ _
    ((alnId_118 j hj) ▸ Q2.listedAt (⟨118, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨118, by decide⟩ : Fin 148) hj hq).1) colCertDiv_118_65_14_match


theorem leaf_118_65_15 (hp : 15 < (Q2.transData.getD 65 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨65, by decide⟩ : Fin 148)) (colE2 ⟨65, by decide⟩ 15 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨65, by decide⟩ : Fin 148))
        (colE1 ⟨65, by decide⟩ 15 (transLenTr ⟨65, by decide⟩ 15 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨118, by decide⟩ : Fin 148) ⟨65, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨65, by decide⟩ 15 (transLenTr ⟨65, by decide⟩ 15 hp)) T118_65
      hfix118_65 hinj118_65 hcardT118_65
      (fun i => conj_mem_of_fixedPoints _ _ (T118_65 i) (hfix118_65 i) _)
      ⟨118, by decide⟩ ⟨65, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨65, by decide⟩ 15 hp) Q2.T118_65_2 Q2.hfix118_65_2 Q2.hinj118_65_2
      Q2.hcardT118_65_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_65_2 i) (Q2.hfix118_65_2 i) _)
      ?_).symm
  rw [show colData1 (⟨118, by decide⟩ : Fin 148)
        ((colE1 ⟨65, by decide⟩ 15 (transLenTr ⟨65, by decide⟩ 15 hp) : ↥(reps ⟨65, by decide⟩)) : Coordinate 1)
        T118_65 = colFn colCertDiv_118_65_15.D1 (m := 5) from colCertDiv_118_65_15.bind1,
    show colData2 (⟨118, by decide⟩ : Fin 148)
        ((colE2 ⟨65, by decide⟩ 15 hp : ↥(Q2.reps ⟨65, by decide⟩)) : Coordinate 2)
        Q2.T118_65_2 = colFn colCertDiv_118_65_15.D2 (m := 5) from colCertDiv_118_65_15.bind2]
  rw [alnId_118 j hj]
  exact fastcode_of_div ⟨118, by decide⟩ _ _ _
    ((alnId_118 j hj) ▸ Q2.listedAt (⟨118, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨118, by decide⟩ : Fin 148) hj hq).1) colCertDiv_118_65_15_match


theorem leaf_118_65_16 (hp : 16 < (Q2.transData.getD 65 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨65, by decide⟩ : Fin 148)) (colE2 ⟨65, by decide⟩ 16 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨65, by decide⟩ : Fin 148))
        (colE1 ⟨65, by decide⟩ 16 (transLenTr ⟨65, by decide⟩ 16 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨118, by decide⟩ : Fin 148) ⟨65, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨65, by decide⟩ 16 (transLenTr ⟨65, by decide⟩ 16 hp)) T118_65
      hfix118_65 hinj118_65 hcardT118_65
      (fun i => conj_mem_of_fixedPoints _ _ (T118_65 i) (hfix118_65 i) _)
      ⟨118, by decide⟩ ⟨65, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨65, by decide⟩ 16 hp) Q2.T118_65_2 Q2.hfix118_65_2 Q2.hinj118_65_2
      Q2.hcardT118_65_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_65_2 i) (Q2.hfix118_65_2 i) _)
      ?_).symm
  rw [show colData1 (⟨118, by decide⟩ : Fin 148)
        ((colE1 ⟨65, by decide⟩ 16 (transLenTr ⟨65, by decide⟩ 16 hp) : ↥(reps ⟨65, by decide⟩)) : Coordinate 1)
        T118_65 = colFn colCertDiv_118_65_16.D1 (m := 5) from colCertDiv_118_65_16.bind1,
    show colData2 (⟨118, by decide⟩ : Fin 148)
        ((colE2 ⟨65, by decide⟩ 16 hp : ↥(Q2.reps ⟨65, by decide⟩)) : Coordinate 2)
        Q2.T118_65_2 = colFn colCertDiv_118_65_16.D2 (m := 5) from colCertDiv_118_65_16.bind2]
  rw [alnId_118 j hj]
  exact fastcode_of_div ⟨118, by decide⟩ _ _ _
    ((alnId_118 j hj) ▸ Q2.listedAt (⟨118, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨118, by decide⟩ : Fin 148) hj hq).1) colCertDiv_118_65_16_match


theorem leaf_118_65_17 (hp : 17 < (Q2.transData.getD 65 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨65, by decide⟩ : Fin 148)) (colE2 ⟨65, by decide⟩ 17 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨65, by decide⟩ : Fin 148))
        (colE1 ⟨65, by decide⟩ 17 (transLenTr ⟨65, by decide⟩ 17 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨118, by decide⟩ : Fin 148) ⟨65, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨65, by decide⟩ 17 (transLenTr ⟨65, by decide⟩ 17 hp)) T118_65
      hfix118_65 hinj118_65 hcardT118_65
      (fun i => conj_mem_of_fixedPoints _ _ (T118_65 i) (hfix118_65 i) _)
      ⟨118, by decide⟩ ⟨65, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨65, by decide⟩ 17 hp) Q2.T118_65_2 Q2.hfix118_65_2 Q2.hinj118_65_2
      Q2.hcardT118_65_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_65_2 i) (Q2.hfix118_65_2 i) _)
      ?_).symm
  rw [show colData1 (⟨118, by decide⟩ : Fin 148)
        ((colE1 ⟨65, by decide⟩ 17 (transLenTr ⟨65, by decide⟩ 17 hp) : ↥(reps ⟨65, by decide⟩)) : Coordinate 1)
        T118_65 = colFn colCertDiv_118_65_17.D1 (m := 5) from colCertDiv_118_65_17.bind1,
    show colData2 (⟨118, by decide⟩ : Fin 148)
        ((colE2 ⟨65, by decide⟩ 17 hp : ↥(Q2.reps ⟨65, by decide⟩)) : Coordinate 2)
        Q2.T118_65_2 = colFn colCertDiv_118_65_17.D2 (m := 5) from colCertDiv_118_65_17.bind2]
  rw [alnId_118 j hj]
  exact fastcode_of_div ⟨118, by decide⟩ _ _ _
    ((alnId_118 j hj) ▸ Q2.listedAt (⟨118, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨118, by decide⟩ : Fin 148) hj hq).1) colCertDiv_118_65_17_match


theorem leaf_118_65_18 (hp : 18 < (Q2.transData.getD 65 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨65, by decide⟩ : Fin 148)) (colE2 ⟨65, by decide⟩ 18 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨65, by decide⟩ : Fin 148))
        (colE1 ⟨65, by decide⟩ 18 (transLenTr ⟨65, by decide⟩ 18 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨118, by decide⟩ : Fin 148) ⟨65, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨65, by decide⟩ 18 (transLenTr ⟨65, by decide⟩ 18 hp)) T118_65
      hfix118_65 hinj118_65 hcardT118_65
      (fun i => conj_mem_of_fixedPoints _ _ (T118_65 i) (hfix118_65 i) _)
      ⟨118, by decide⟩ ⟨65, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨65, by decide⟩ 18 hp) Q2.T118_65_2 Q2.hfix118_65_2 Q2.hinj118_65_2
      Q2.hcardT118_65_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_65_2 i) (Q2.hfix118_65_2 i) _)
      ?_).symm
  rw [show colData1 (⟨118, by decide⟩ : Fin 148)
        ((colE1 ⟨65, by decide⟩ 18 (transLenTr ⟨65, by decide⟩ 18 hp) : ↥(reps ⟨65, by decide⟩)) : Coordinate 1)
        T118_65 = colFn colCertDiv_118_65_18.D1 (m := 5) from colCertDiv_118_65_18.bind1,
    show colData2 (⟨118, by decide⟩ : Fin 148)
        ((colE2 ⟨65, by decide⟩ 18 hp : ↥(Q2.reps ⟨65, by decide⟩)) : Coordinate 2)
        Q2.T118_65_2 = colFn colCertDiv_118_65_18.D2 (m := 5) from colCertDiv_118_65_18.bind2]
  rw [alnId_118 j hj]
  exact fastcode_of_div ⟨118, by decide⟩ _ _ _
    ((alnId_118 j hj) ▸ Q2.listedAt (⟨118, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨118, by decide⟩ : Fin 148) hj hq).1) colCertDiv_118_65_18_match


theorem leaf_118_65_19 (hp : 19 < (Q2.transData.getD 65 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨65, by decide⟩ : Fin 148)) (colE2 ⟨65, by decide⟩ 19 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨65, by decide⟩ : Fin 148))
        (colE1 ⟨65, by decide⟩ 19 (transLenTr ⟨65, by decide⟩ 19 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨118, by decide⟩ : Fin 148) ⟨65, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨65, by decide⟩ 19 (transLenTr ⟨65, by decide⟩ 19 hp)) T118_65
      hfix118_65 hinj118_65 hcardT118_65
      (fun i => conj_mem_of_fixedPoints _ _ (T118_65 i) (hfix118_65 i) _)
      ⟨118, by decide⟩ ⟨65, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨65, by decide⟩ 19 hp) Q2.T118_65_2 Q2.hfix118_65_2 Q2.hinj118_65_2
      Q2.hcardT118_65_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_65_2 i) (Q2.hfix118_65_2 i) _)
      ?_).symm
  rw [show colData1 (⟨118, by decide⟩ : Fin 148)
        ((colE1 ⟨65, by decide⟩ 19 (transLenTr ⟨65, by decide⟩ 19 hp) : ↥(reps ⟨65, by decide⟩)) : Coordinate 1)
        T118_65 = colFn colCertDiv_118_65_19.D1 (m := 5) from colCertDiv_118_65_19.bind1,
    show colData2 (⟨118, by decide⟩ : Fin 148)
        ((colE2 ⟨65, by decide⟩ 19 hp : ↥(Q2.reps ⟨65, by decide⟩)) : Coordinate 2)
        Q2.T118_65_2 = colFn colCertDiv_118_65_19.D2 (m := 5) from colCertDiv_118_65_19.bind2]
  rw [alnId_118 j hj]
  exact fastcode_of_div ⟨118, by decide⟩ _ _ _
    ((alnId_118 j hj) ▸ Q2.listedAt (⟨118, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨118, by decide⟩ : Fin 148) hj hq).1) colCertDiv_118_65_19_match


theorem leaf_118_65_20 (hp : 20 < (Q2.transData.getD 65 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨65, by decide⟩ : Fin 148)) (colE2 ⟨65, by decide⟩ 20 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨65, by decide⟩ : Fin 148))
        (colE1 ⟨65, by decide⟩ 20 (transLenTr ⟨65, by decide⟩ 20 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨118, by decide⟩ : Fin 148) ⟨65, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨65, by decide⟩ 20 (transLenTr ⟨65, by decide⟩ 20 hp)) T118_65
      hfix118_65 hinj118_65 hcardT118_65
      (fun i => conj_mem_of_fixedPoints _ _ (T118_65 i) (hfix118_65 i) _)
      ⟨118, by decide⟩ ⟨65, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨65, by decide⟩ 20 hp) Q2.T118_65_2 Q2.hfix118_65_2 Q2.hinj118_65_2
      Q2.hcardT118_65_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_65_2 i) (Q2.hfix118_65_2 i) _)
      ?_).symm
  rw [show colData1 (⟨118, by decide⟩ : Fin 148)
        ((colE1 ⟨65, by decide⟩ 20 (transLenTr ⟨65, by decide⟩ 20 hp) : ↥(reps ⟨65, by decide⟩)) : Coordinate 1)
        T118_65 = colFn colCertDiv_118_65_20.D1 (m := 5) from colCertDiv_118_65_20.bind1,
    show colData2 (⟨118, by decide⟩ : Fin 148)
        ((colE2 ⟨65, by decide⟩ 20 hp : ↥(Q2.reps ⟨65, by decide⟩)) : Coordinate 2)
        Q2.T118_65_2 = colFn colCertDiv_118_65_20.D2 (m := 5) from colCertDiv_118_65_20.bind2]
  rw [alnId_118 j hj]
  exact fastcode_of_div ⟨118, by decide⟩ _ _ _
    ((alnId_118 j hj) ▸ Q2.listedAt (⟨118, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨118, by decide⟩ : Fin 148) hj hq).1) colCertDiv_118_65_20_match


theorem leaf_118_65_21 (hp : 21 < (Q2.transData.getD 65 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨65, by decide⟩ : Fin 148)) (colE2 ⟨65, by decide⟩ 21 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨65, by decide⟩ : Fin 148))
        (colE1 ⟨65, by decide⟩ 21 (transLenTr ⟨65, by decide⟩ 21 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨118, by decide⟩ : Fin 148) ⟨65, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨65, by decide⟩ 21 (transLenTr ⟨65, by decide⟩ 21 hp)) T118_65
      hfix118_65 hinj118_65 hcardT118_65
      (fun i => conj_mem_of_fixedPoints _ _ (T118_65 i) (hfix118_65 i) _)
      ⟨118, by decide⟩ ⟨65, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨65, by decide⟩ 21 hp) Q2.T118_65_2 Q2.hfix118_65_2 Q2.hinj118_65_2
      Q2.hcardT118_65_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_65_2 i) (Q2.hfix118_65_2 i) _)
      ?_).symm
  rw [show colData1 (⟨118, by decide⟩ : Fin 148)
        ((colE1 ⟨65, by decide⟩ 21 (transLenTr ⟨65, by decide⟩ 21 hp) : ↥(reps ⟨65, by decide⟩)) : Coordinate 1)
        T118_65 = colFn colCertDiv_118_65_21.D1 (m := 5) from colCertDiv_118_65_21.bind1,
    show colData2 (⟨118, by decide⟩ : Fin 148)
        ((colE2 ⟨65, by decide⟩ 21 hp : ↥(Q2.reps ⟨65, by decide⟩)) : Coordinate 2)
        Q2.T118_65_2 = colFn colCertDiv_118_65_21.D2 (m := 5) from colCertDiv_118_65_21.bind2]
  rw [alnId_118 j hj]
  exact fastcode_of_div ⟨118, by decide⟩ _ _ _
    ((alnId_118 j hj) ▸ Q2.listedAt (⟨118, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨118, by decide⟩ : Fin 148) hj hq).1) colCertDiv_118_65_21_match


theorem leaf_118_65_22 (hp : 22 < (Q2.transData.getD 65 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨65, by decide⟩ : Fin 148)) (colE2 ⟨65, by decide⟩ 22 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨65, by decide⟩ : Fin 148))
        (colE1 ⟨65, by decide⟩ 22 (transLenTr ⟨65, by decide⟩ 22 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨118, by decide⟩ : Fin 148) ⟨65, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨65, by decide⟩ 22 (transLenTr ⟨65, by decide⟩ 22 hp)) T118_65
      hfix118_65 hinj118_65 hcardT118_65
      (fun i => conj_mem_of_fixedPoints _ _ (T118_65 i) (hfix118_65 i) _)
      ⟨118, by decide⟩ ⟨65, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨65, by decide⟩ 22 hp) Q2.T118_65_2 Q2.hfix118_65_2 Q2.hinj118_65_2
      Q2.hcardT118_65_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_65_2 i) (Q2.hfix118_65_2 i) _)
      ?_).symm
  rw [show colData1 (⟨118, by decide⟩ : Fin 148)
        ((colE1 ⟨65, by decide⟩ 22 (transLenTr ⟨65, by decide⟩ 22 hp) : ↥(reps ⟨65, by decide⟩)) : Coordinate 1)
        T118_65 = colFn colCertDiv_118_65_22.D1 (m := 5) from colCertDiv_118_65_22.bind1,
    show colData2 (⟨118, by decide⟩ : Fin 148)
        ((colE2 ⟨65, by decide⟩ 22 hp : ↥(Q2.reps ⟨65, by decide⟩)) : Coordinate 2)
        Q2.T118_65_2 = colFn colCertDiv_118_65_22.D2 (m := 5) from colCertDiv_118_65_22.bind2]
  rw [alnId_118 j hj]
  exact fastcode_of_div ⟨118, by decide⟩ _ _ _
    ((alnId_118 j hj) ▸ Q2.listedAt (⟨118, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨118, by decide⟩ : Fin 148) hj hq).1) colCertDiv_118_65_22_match


theorem leaf_118_65_23 (hp : 23 < (Q2.transData.getD 65 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨65, by decide⟩ : Fin 148)) (colE2 ⟨65, by decide⟩ 23 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨65, by decide⟩ : Fin 148))
        (colE1 ⟨65, by decide⟩ 23 (transLenTr ⟨65, by decide⟩ 23 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨118, by decide⟩ : Fin 148) ⟨65, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨65, by decide⟩ 23 (transLenTr ⟨65, by decide⟩ 23 hp)) T118_65
      hfix118_65 hinj118_65 hcardT118_65
      (fun i => conj_mem_of_fixedPoints _ _ (T118_65 i) (hfix118_65 i) _)
      ⟨118, by decide⟩ ⟨65, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨65, by decide⟩ 23 hp) Q2.T118_65_2 Q2.hfix118_65_2 Q2.hinj118_65_2
      Q2.hcardT118_65_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_65_2 i) (Q2.hfix118_65_2 i) _)
      ?_).symm
  rw [show colData1 (⟨118, by decide⟩ : Fin 148)
        ((colE1 ⟨65, by decide⟩ 23 (transLenTr ⟨65, by decide⟩ 23 hp) : ↥(reps ⟨65, by decide⟩)) : Coordinate 1)
        T118_65 = colFn colCertDiv_118_65_23.D1 (m := 5) from colCertDiv_118_65_23.bind1,
    show colData2 (⟨118, by decide⟩ : Fin 148)
        ((colE2 ⟨65, by decide⟩ 23 hp : ↥(Q2.reps ⟨65, by decide⟩)) : Coordinate 2)
        Q2.T118_65_2 = colFn colCertDiv_118_65_23.D2 (m := 5) from colCertDiv_118_65_23.bind2]
  rw [alnId_118 j hj]
  exact fastcode_of_div ⟨118, by decide⟩ _ _ _
    ((alnId_118 j hj) ▸ Q2.listedAt (⟨118, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨118, by decide⟩ : Fin 148) hj hq).1) colCertDiv_118_65_23_match


theorem leaf_118_65_24 (hp : 24 < (Q2.transData.getD 65 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨65, by decide⟩ : Fin 148)) (colE2 ⟨65, by decide⟩ 24 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨65, by decide⟩ : Fin 148))
        (colE1 ⟨65, by decide⟩ 24 (transLenTr ⟨65, by decide⟩ 24 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨118, by decide⟩ : Fin 148) ⟨65, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨65, by decide⟩ 24 (transLenTr ⟨65, by decide⟩ 24 hp)) T118_65
      hfix118_65 hinj118_65 hcardT118_65
      (fun i => conj_mem_of_fixedPoints _ _ (T118_65 i) (hfix118_65 i) _)
      ⟨118, by decide⟩ ⟨65, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨65, by decide⟩ 24 hp) Q2.T118_65_2 Q2.hfix118_65_2 Q2.hinj118_65_2
      Q2.hcardT118_65_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_65_2 i) (Q2.hfix118_65_2 i) _)
      ?_).symm
  rw [show colData1 (⟨118, by decide⟩ : Fin 148)
        ((colE1 ⟨65, by decide⟩ 24 (transLenTr ⟨65, by decide⟩ 24 hp) : ↥(reps ⟨65, by decide⟩)) : Coordinate 1)
        T118_65 = colFn colCertDiv_118_65_24.D1 (m := 5) from colCertDiv_118_65_24.bind1,
    show colData2 (⟨118, by decide⟩ : Fin 148)
        ((colE2 ⟨65, by decide⟩ 24 hp : ↥(Q2.reps ⟨65, by decide⟩)) : Coordinate 2)
        Q2.T118_65_2 = colFn colCertDiv_118_65_24.D2 (m := 5) from colCertDiv_118_65_24.bind2]
  rw [alnId_118 j hj]
  exact fastcode_of_div ⟨118, by decide⟩ _ _ _
    ((alnId_118 j hj) ▸ Q2.listedAt (⟨118, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨118, by decide⟩ : Fin 148) hj hq).1) colCertDiv_118_65_24_match


theorem leaf_118_66_0 (hp : 0 < (Q2.transData.getD 66 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨66, by decide⟩ : Fin 148)) (colE2 ⟨66, by decide⟩ 0 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨66, by decide⟩ : Fin 148))
        (colE1 ⟨66, by decide⟩ 0 (transLenTr ⟨66, by decide⟩ 0 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨66, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨66, by decide⟩ 0 (transLenTr ⟨66, by decide⟩ 0 hp)) T118_66
      hfix118_66 hinj118_66 hcardT118_66
      (fun i => conj_mem_of_fixedPoints _ _ (T118_66 i) (hfix118_66 i) _)
      ⟨118, by decide⟩ ⟨66, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨66, by decide⟩ 0 hp) Q2.T118_66_2 Q2.hfix118_66_2 Q2.hinj118_66_2
      Q2.hcardT118_66_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_66_2 i) (Q2.hfix118_66_2 i) _)
      colCert_118_66_0.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_66_1 (hp : 1 < (Q2.transData.getD 66 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨66, by decide⟩ : Fin 148)) (colE2 ⟨66, by decide⟩ 1 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨66, by decide⟩ : Fin 148))
        (colE1 ⟨66, by decide⟩ 1 (transLenTr ⟨66, by decide⟩ 1 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨66, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨66, by decide⟩ 1 (transLenTr ⟨66, by decide⟩ 1 hp)) T118_66
      hfix118_66 hinj118_66 hcardT118_66
      (fun i => conj_mem_of_fixedPoints _ _ (T118_66 i) (hfix118_66 i) _)
      ⟨118, by decide⟩ ⟨66, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨66, by decide⟩ 1 hp) Q2.T118_66_2 Q2.hfix118_66_2 Q2.hinj118_66_2
      Q2.hcardT118_66_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_66_2 i) (Q2.hfix118_66_2 i) _)
      colCert_118_66_1.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_66_2 (hp : 2 < (Q2.transData.getD 66 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨66, by decide⟩ : Fin 148)) (colE2 ⟨66, by decide⟩ 2 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨66, by decide⟩ : Fin 148))
        (colE1 ⟨66, by decide⟩ 2 (transLenTr ⟨66, by decide⟩ 2 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨66, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨66, by decide⟩ 2 (transLenTr ⟨66, by decide⟩ 2 hp)) T118_66
      hfix118_66 hinj118_66 hcardT118_66
      (fun i => conj_mem_of_fixedPoints _ _ (T118_66 i) (hfix118_66 i) _)
      ⟨118, by decide⟩ ⟨66, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨66, by decide⟩ 2 hp) Q2.T118_66_2 Q2.hfix118_66_2 Q2.hinj118_66_2
      Q2.hcardT118_66_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_66_2 i) (Q2.hfix118_66_2 i) _)
      colCert_118_66_2.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_66_3 (hp : 3 < (Q2.transData.getD 66 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨66, by decide⟩ : Fin 148)) (colE2 ⟨66, by decide⟩ 3 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨66, by decide⟩ : Fin 148))
        (colE1 ⟨66, by decide⟩ 3 (transLenTr ⟨66, by decide⟩ 3 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨66, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨66, by decide⟩ 3 (transLenTr ⟨66, by decide⟩ 3 hp)) T118_66
      hfix118_66 hinj118_66 hcardT118_66
      (fun i => conj_mem_of_fixedPoints _ _ (T118_66 i) (hfix118_66 i) _)
      ⟨118, by decide⟩ ⟨66, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨66, by decide⟩ 3 hp) Q2.T118_66_2 Q2.hfix118_66_2 Q2.hinj118_66_2
      Q2.hcardT118_66_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_66_2 i) (Q2.hfix118_66_2 i) _)
      colCert_118_66_3.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_66_4 (hp : 4 < (Q2.transData.getD 66 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨66, by decide⟩ : Fin 148)) (colE2 ⟨66, by decide⟩ 4 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨66, by decide⟩ : Fin 148))
        (colE1 ⟨66, by decide⟩ 4 (transLenTr ⟨66, by decide⟩ 4 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨66, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨66, by decide⟩ 4 (transLenTr ⟨66, by decide⟩ 4 hp)) T118_66
      hfix118_66 hinj118_66 hcardT118_66
      (fun i => conj_mem_of_fixedPoints _ _ (T118_66 i) (hfix118_66 i) _)
      ⟨118, by decide⟩ ⟨66, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨66, by decide⟩ 4 hp) Q2.T118_66_2 Q2.hfix118_66_2 Q2.hinj118_66_2
      Q2.hcardT118_66_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_66_2 i) (Q2.hfix118_66_2 i) _)
      colCert_118_66_4.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_66_5 (hp : 5 < (Q2.transData.getD 66 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨66, by decide⟩ : Fin 148)) (colE2 ⟨66, by decide⟩ 5 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨66, by decide⟩ : Fin 148))
        (colE1 ⟨66, by decide⟩ 5 (transLenTr ⟨66, by decide⟩ 5 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨118, by decide⟩ : Fin 148) ⟨66, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨66, by decide⟩ 5 (transLenTr ⟨66, by decide⟩ 5 hp)) T118_66
      hfix118_66 hinj118_66 hcardT118_66
      (fun i => conj_mem_of_fixedPoints _ _ (T118_66 i) (hfix118_66 i) _)
      ⟨118, by decide⟩ ⟨66, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨66, by decide⟩ 5 hp) Q2.T118_66_2 Q2.hfix118_66_2 Q2.hinj118_66_2
      Q2.hcardT118_66_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_66_2 i) (Q2.hfix118_66_2 i) _)
      ?_).symm
  rw [show colData1 (⟨118, by decide⟩ : Fin 148)
        ((colE1 ⟨66, by decide⟩ 5 (transLenTr ⟨66, by decide⟩ 5 hp) : ↥(reps ⟨66, by decide⟩)) : Coordinate 1)
        T118_66 = colFn colCertDiv_118_66_5.D1 (m := 5) from colCertDiv_118_66_5.bind1,
    show colData2 (⟨118, by decide⟩ : Fin 148)
        ((colE2 ⟨66, by decide⟩ 5 hp : ↥(Q2.reps ⟨66, by decide⟩)) : Coordinate 2)
        Q2.T118_66_2 = colFn colCertDiv_118_66_5.D2 (m := 5) from colCertDiv_118_66_5.bind2]
  rw [alnId_118 j hj]
  exact fastcode_of_div ⟨118, by decide⟩ _ _ _
    ((alnId_118 j hj) ▸ Q2.listedAt (⟨118, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨118, by decide⟩ : Fin 148) hj hq).1) colCertDiv_118_66_5_match


theorem leaf_118_66_6 (hp : 6 < (Q2.transData.getD 66 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨66, by decide⟩ : Fin 148)) (colE2 ⟨66, by decide⟩ 6 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨66, by decide⟩ : Fin 148))
        (colE1 ⟨66, by decide⟩ 6 (transLenTr ⟨66, by decide⟩ 6 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨118, by decide⟩ : Fin 148) ⟨66, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨66, by decide⟩ 6 (transLenTr ⟨66, by decide⟩ 6 hp)) T118_66
      hfix118_66 hinj118_66 hcardT118_66
      (fun i => conj_mem_of_fixedPoints _ _ (T118_66 i) (hfix118_66 i) _)
      ⟨118, by decide⟩ ⟨66, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨66, by decide⟩ 6 hp) Q2.T118_66_2 Q2.hfix118_66_2 Q2.hinj118_66_2
      Q2.hcardT118_66_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_66_2 i) (Q2.hfix118_66_2 i) _)
      ?_).symm
  rw [show colData1 (⟨118, by decide⟩ : Fin 148)
        ((colE1 ⟨66, by decide⟩ 6 (transLenTr ⟨66, by decide⟩ 6 hp) : ↥(reps ⟨66, by decide⟩)) : Coordinate 1)
        T118_66 = colFn colCertDiv_118_66_6.D1 (m := 5) from colCertDiv_118_66_6.bind1,
    show colData2 (⟨118, by decide⟩ : Fin 148)
        ((colE2 ⟨66, by decide⟩ 6 hp : ↥(Q2.reps ⟨66, by decide⟩)) : Coordinate 2)
        Q2.T118_66_2 = colFn colCertDiv_118_66_6.D2 (m := 5) from colCertDiv_118_66_6.bind2]
  rw [alnId_118 j hj]
  exact fastcode_of_div ⟨118, by decide⟩ _ _ _
    ((alnId_118 j hj) ▸ Q2.listedAt (⟨118, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨118, by decide⟩ : Fin 148) hj hq).1) colCertDiv_118_66_6_match


theorem leaf_118_66_7 (hp : 7 < (Q2.transData.getD 66 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨66, by decide⟩ : Fin 148)) (colE2 ⟨66, by decide⟩ 7 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨66, by decide⟩ : Fin 148))
        (colE1 ⟨66, by decide⟩ 7 (transLenTr ⟨66, by decide⟩ 7 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨118, by decide⟩ : Fin 148) ⟨66, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨66, by decide⟩ 7 (transLenTr ⟨66, by decide⟩ 7 hp)) T118_66
      hfix118_66 hinj118_66 hcardT118_66
      (fun i => conj_mem_of_fixedPoints _ _ (T118_66 i) (hfix118_66 i) _)
      ⟨118, by decide⟩ ⟨66, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨66, by decide⟩ 7 hp) Q2.T118_66_2 Q2.hfix118_66_2 Q2.hinj118_66_2
      Q2.hcardT118_66_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_66_2 i) (Q2.hfix118_66_2 i) _)
      ?_).symm
  rw [show colData1 (⟨118, by decide⟩ : Fin 148)
        ((colE1 ⟨66, by decide⟩ 7 (transLenTr ⟨66, by decide⟩ 7 hp) : ↥(reps ⟨66, by decide⟩)) : Coordinate 1)
        T118_66 = colFn colCertDiv_118_66_7.D1 (m := 5) from colCertDiv_118_66_7.bind1,
    show colData2 (⟨118, by decide⟩ : Fin 148)
        ((colE2 ⟨66, by decide⟩ 7 hp : ↥(Q2.reps ⟨66, by decide⟩)) : Coordinate 2)
        Q2.T118_66_2 = colFn colCertDiv_118_66_7.D2 (m := 5) from colCertDiv_118_66_7.bind2]
  rw [alnId_118 j hj]
  exact fastcode_of_div ⟨118, by decide⟩ _ _ _
    ((alnId_118 j hj) ▸ Q2.listedAt (⟨118, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨118, by decide⟩ : Fin 148) hj hq).1) colCertDiv_118_66_7_match


theorem leaf_118_66_8 (hp : 8 < (Q2.transData.getD 66 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨66, by decide⟩ : Fin 148)) (colE2 ⟨66, by decide⟩ 8 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨66, by decide⟩ : Fin 148))
        (colE1 ⟨66, by decide⟩ 8 (transLenTr ⟨66, by decide⟩ 8 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨118, by decide⟩ : Fin 148) ⟨66, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨66, by decide⟩ 8 (transLenTr ⟨66, by decide⟩ 8 hp)) T118_66
      hfix118_66 hinj118_66 hcardT118_66
      (fun i => conj_mem_of_fixedPoints _ _ (T118_66 i) (hfix118_66 i) _)
      ⟨118, by decide⟩ ⟨66, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨66, by decide⟩ 8 hp) Q2.T118_66_2 Q2.hfix118_66_2 Q2.hinj118_66_2
      Q2.hcardT118_66_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_66_2 i) (Q2.hfix118_66_2 i) _)
      ?_).symm
  rw [show colData1 (⟨118, by decide⟩ : Fin 148)
        ((colE1 ⟨66, by decide⟩ 8 (transLenTr ⟨66, by decide⟩ 8 hp) : ↥(reps ⟨66, by decide⟩)) : Coordinate 1)
        T118_66 = colFn colCertDiv_118_66_8.D1 (m := 5) from colCertDiv_118_66_8.bind1,
    show colData2 (⟨118, by decide⟩ : Fin 148)
        ((colE2 ⟨66, by decide⟩ 8 hp : ↥(Q2.reps ⟨66, by decide⟩)) : Coordinate 2)
        Q2.T118_66_2 = colFn colCertDiv_118_66_8.D2 (m := 5) from colCertDiv_118_66_8.bind2]
  rw [alnId_118 j hj]
  exact fastcode_of_div ⟨118, by decide⟩ _ _ _
    ((alnId_118 j hj) ▸ Q2.listedAt (⟨118, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨118, by decide⟩ : Fin 148) hj hq).1) colCertDiv_118_66_8_match


theorem leaf_118_66_9 (hp : 9 < (Q2.transData.getD 66 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨66, by decide⟩ : Fin 148)) (colE2 ⟨66, by decide⟩ 9 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨66, by decide⟩ : Fin 148))
        (colE1 ⟨66, by decide⟩ 9 (transLenTr ⟨66, by decide⟩ 9 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨118, by decide⟩ : Fin 148) ⟨66, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨66, by decide⟩ 9 (transLenTr ⟨66, by decide⟩ 9 hp)) T118_66
      hfix118_66 hinj118_66 hcardT118_66
      (fun i => conj_mem_of_fixedPoints _ _ (T118_66 i) (hfix118_66 i) _)
      ⟨118, by decide⟩ ⟨66, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨66, by decide⟩ 9 hp) Q2.T118_66_2 Q2.hfix118_66_2 Q2.hinj118_66_2
      Q2.hcardT118_66_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_66_2 i) (Q2.hfix118_66_2 i) _)
      ?_).symm
  rw [show colData1 (⟨118, by decide⟩ : Fin 148)
        ((colE1 ⟨66, by decide⟩ 9 (transLenTr ⟨66, by decide⟩ 9 hp) : ↥(reps ⟨66, by decide⟩)) : Coordinate 1)
        T118_66 = colFn colCertDiv_118_66_9.D1 (m := 5) from colCertDiv_118_66_9.bind1,
    show colData2 (⟨118, by decide⟩ : Fin 148)
        ((colE2 ⟨66, by decide⟩ 9 hp : ↥(Q2.reps ⟨66, by decide⟩)) : Coordinate 2)
        Q2.T118_66_2 = colFn colCertDiv_118_66_9.D2 (m := 5) from colCertDiv_118_66_9.bind2]
  rw [alnId_118 j hj]
  exact fastcode_of_div ⟨118, by decide⟩ _ _ _
    ((alnId_118 j hj) ▸ Q2.listedAt (⟨118, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨118, by decide⟩ : Fin 148) hj hq).1) colCertDiv_118_66_9_match


theorem leaf_118_66_10 (hp : 10 < (Q2.transData.getD 66 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨66, by decide⟩ : Fin 148)) (colE2 ⟨66, by decide⟩ 10 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨66, by decide⟩ : Fin 148))
        (colE1 ⟨66, by decide⟩ 10 (transLenTr ⟨66, by decide⟩ 10 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨118, by decide⟩ : Fin 148) ⟨66, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨66, by decide⟩ 10 (transLenTr ⟨66, by decide⟩ 10 hp)) T118_66
      hfix118_66 hinj118_66 hcardT118_66
      (fun i => conj_mem_of_fixedPoints _ _ (T118_66 i) (hfix118_66 i) _)
      ⟨118, by decide⟩ ⟨66, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨66, by decide⟩ 10 hp) Q2.T118_66_2 Q2.hfix118_66_2 Q2.hinj118_66_2
      Q2.hcardT118_66_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_66_2 i) (Q2.hfix118_66_2 i) _)
      ?_).symm
  rw [show colData1 (⟨118, by decide⟩ : Fin 148)
        ((colE1 ⟨66, by decide⟩ 10 (transLenTr ⟨66, by decide⟩ 10 hp) : ↥(reps ⟨66, by decide⟩)) : Coordinate 1)
        T118_66 = colFn colCertDiv_118_66_10.D1 (m := 5) from colCertDiv_118_66_10.bind1,
    show colData2 (⟨118, by decide⟩ : Fin 148)
        ((colE2 ⟨66, by decide⟩ 10 hp : ↥(Q2.reps ⟨66, by decide⟩)) : Coordinate 2)
        Q2.T118_66_2 = colFn colCertDiv_118_66_10.D2 (m := 5) from colCertDiv_118_66_10.bind2]
  rw [alnId_118 j hj]
  exact fastcode_of_div ⟨118, by decide⟩ _ _ _
    ((alnId_118 j hj) ▸ Q2.listedAt (⟨118, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨118, by decide⟩ : Fin 148) hj hq).1) colCertDiv_118_66_10_match


theorem leaf_118_66_11 (hp : 11 < (Q2.transData.getD 66 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨66, by decide⟩ : Fin 148)) (colE2 ⟨66, by decide⟩ 11 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨66, by decide⟩ : Fin 148))
        (colE1 ⟨66, by decide⟩ 11 (transLenTr ⟨66, by decide⟩ 11 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨118, by decide⟩ : Fin 148) ⟨66, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨66, by decide⟩ 11 (transLenTr ⟨66, by decide⟩ 11 hp)) T118_66
      hfix118_66 hinj118_66 hcardT118_66
      (fun i => conj_mem_of_fixedPoints _ _ (T118_66 i) (hfix118_66 i) _)
      ⟨118, by decide⟩ ⟨66, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨66, by decide⟩ 11 hp) Q2.T118_66_2 Q2.hfix118_66_2 Q2.hinj118_66_2
      Q2.hcardT118_66_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_66_2 i) (Q2.hfix118_66_2 i) _)
      ?_).symm
  rw [show colData1 (⟨118, by decide⟩ : Fin 148)
        ((colE1 ⟨66, by decide⟩ 11 (transLenTr ⟨66, by decide⟩ 11 hp) : ↥(reps ⟨66, by decide⟩)) : Coordinate 1)
        T118_66 = colFn colCertDiv_118_66_11.D1 (m := 5) from colCertDiv_118_66_11.bind1,
    show colData2 (⟨118, by decide⟩ : Fin 148)
        ((colE2 ⟨66, by decide⟩ 11 hp : ↥(Q2.reps ⟨66, by decide⟩)) : Coordinate 2)
        Q2.T118_66_2 = colFn colCertDiv_118_66_11.D2 (m := 5) from colCertDiv_118_66_11.bind2]
  rw [alnId_118 j hj]
  exact fastcode_of_div ⟨118, by decide⟩ _ _ _
    ((alnId_118 j hj) ▸ Q2.listedAt (⟨118, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨118, by decide⟩ : Fin 148) hj hq).1) colCertDiv_118_66_11_match


theorem leaf_118_66_12 (hp : 12 < (Q2.transData.getD 66 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨66, by decide⟩ : Fin 148)) (colE2 ⟨66, by decide⟩ 12 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨66, by decide⟩ : Fin 148))
        (colE1 ⟨66, by decide⟩ 12 (transLenTr ⟨66, by decide⟩ 12 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨118, by decide⟩ : Fin 148) ⟨66, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨66, by decide⟩ 12 (transLenTr ⟨66, by decide⟩ 12 hp)) T118_66
      hfix118_66 hinj118_66 hcardT118_66
      (fun i => conj_mem_of_fixedPoints _ _ (T118_66 i) (hfix118_66 i) _)
      ⟨118, by decide⟩ ⟨66, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨66, by decide⟩ 12 hp) Q2.T118_66_2 Q2.hfix118_66_2 Q2.hinj118_66_2
      Q2.hcardT118_66_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_66_2 i) (Q2.hfix118_66_2 i) _)
      ?_).symm
  rw [show colData1 (⟨118, by decide⟩ : Fin 148)
        ((colE1 ⟨66, by decide⟩ 12 (transLenTr ⟨66, by decide⟩ 12 hp) : ↥(reps ⟨66, by decide⟩)) : Coordinate 1)
        T118_66 = colFn colCertDiv_118_66_12.D1 (m := 5) from colCertDiv_118_66_12.bind1,
    show colData2 (⟨118, by decide⟩ : Fin 148)
        ((colE2 ⟨66, by decide⟩ 12 hp : ↥(Q2.reps ⟨66, by decide⟩)) : Coordinate 2)
        Q2.T118_66_2 = colFn colCertDiv_118_66_12.D2 (m := 5) from colCertDiv_118_66_12.bind2]
  rw [alnId_118 j hj]
  exact fastcode_of_div ⟨118, by decide⟩ _ _ _
    ((alnId_118 j hj) ▸ Q2.listedAt (⟨118, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨118, by decide⟩ : Fin 148) hj hq).1) colCertDiv_118_66_12_match


theorem leaf_118_66_13 (hp : 13 < (Q2.transData.getD 66 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨66, by decide⟩ : Fin 148)) (colE2 ⟨66, by decide⟩ 13 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨66, by decide⟩ : Fin 148))
        (colE1 ⟨66, by decide⟩ 13 (transLenTr ⟨66, by decide⟩ 13 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨118, by decide⟩ : Fin 148) ⟨66, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨66, by decide⟩ 13 (transLenTr ⟨66, by decide⟩ 13 hp)) T118_66
      hfix118_66 hinj118_66 hcardT118_66
      (fun i => conj_mem_of_fixedPoints _ _ (T118_66 i) (hfix118_66 i) _)
      ⟨118, by decide⟩ ⟨66, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨66, by decide⟩ 13 hp) Q2.T118_66_2 Q2.hfix118_66_2 Q2.hinj118_66_2
      Q2.hcardT118_66_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_66_2 i) (Q2.hfix118_66_2 i) _)
      ?_).symm
  rw [show colData1 (⟨118, by decide⟩ : Fin 148)
        ((colE1 ⟨66, by decide⟩ 13 (transLenTr ⟨66, by decide⟩ 13 hp) : ↥(reps ⟨66, by decide⟩)) : Coordinate 1)
        T118_66 = colFn colCertDiv_118_66_13.D1 (m := 5) from colCertDiv_118_66_13.bind1,
    show colData2 (⟨118, by decide⟩ : Fin 148)
        ((colE2 ⟨66, by decide⟩ 13 hp : ↥(Q2.reps ⟨66, by decide⟩)) : Coordinate 2)
        Q2.T118_66_2 = colFn colCertDiv_118_66_13.D2 (m := 5) from colCertDiv_118_66_13.bind2]
  rw [alnId_118 j hj]
  exact fastcode_of_div ⟨118, by decide⟩ _ _ _
    ((alnId_118 j hj) ▸ Q2.listedAt (⟨118, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨118, by decide⟩ : Fin 148) hj hq).1) colCertDiv_118_66_13_match


theorem leaf_118_66_14 (hp : 14 < (Q2.transData.getD 66 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨66, by decide⟩ : Fin 148)) (colE2 ⟨66, by decide⟩ 14 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨66, by decide⟩ : Fin 148))
        (colE1 ⟨66, by decide⟩ 14 (transLenTr ⟨66, by decide⟩ 14 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨118, by decide⟩ : Fin 148) ⟨66, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨66, by decide⟩ 14 (transLenTr ⟨66, by decide⟩ 14 hp)) T118_66
      hfix118_66 hinj118_66 hcardT118_66
      (fun i => conj_mem_of_fixedPoints _ _ (T118_66 i) (hfix118_66 i) _)
      ⟨118, by decide⟩ ⟨66, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨66, by decide⟩ 14 hp) Q2.T118_66_2 Q2.hfix118_66_2 Q2.hinj118_66_2
      Q2.hcardT118_66_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_66_2 i) (Q2.hfix118_66_2 i) _)
      ?_).symm
  rw [show colData1 (⟨118, by decide⟩ : Fin 148)
        ((colE1 ⟨66, by decide⟩ 14 (transLenTr ⟨66, by decide⟩ 14 hp) : ↥(reps ⟨66, by decide⟩)) : Coordinate 1)
        T118_66 = colFn colCertDiv_118_66_14.D1 (m := 5) from colCertDiv_118_66_14.bind1,
    show colData2 (⟨118, by decide⟩ : Fin 148)
        ((colE2 ⟨66, by decide⟩ 14 hp : ↥(Q2.reps ⟨66, by decide⟩)) : Coordinate 2)
        Q2.T118_66_2 = colFn colCertDiv_118_66_14.D2 (m := 5) from colCertDiv_118_66_14.bind2]
  rw [alnId_118 j hj]
  exact fastcode_of_div ⟨118, by decide⟩ _ _ _
    ((alnId_118 j hj) ▸ Q2.listedAt (⟨118, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨118, by decide⟩ : Fin 148) hj hq).1) colCertDiv_118_66_14_match


theorem leaf_118_66_15 (hp : 15 < (Q2.transData.getD 66 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨66, by decide⟩ : Fin 148)) (colE2 ⟨66, by decide⟩ 15 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨66, by decide⟩ : Fin 148))
        (colE1 ⟨66, by decide⟩ 15 (transLenTr ⟨66, by decide⟩ 15 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨118, by decide⟩ : Fin 148) ⟨66, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨66, by decide⟩ 15 (transLenTr ⟨66, by decide⟩ 15 hp)) T118_66
      hfix118_66 hinj118_66 hcardT118_66
      (fun i => conj_mem_of_fixedPoints _ _ (T118_66 i) (hfix118_66 i) _)
      ⟨118, by decide⟩ ⟨66, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨66, by decide⟩ 15 hp) Q2.T118_66_2 Q2.hfix118_66_2 Q2.hinj118_66_2
      Q2.hcardT118_66_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_66_2 i) (Q2.hfix118_66_2 i) _)
      ?_).symm
  rw [show colData1 (⟨118, by decide⟩ : Fin 148)
        ((colE1 ⟨66, by decide⟩ 15 (transLenTr ⟨66, by decide⟩ 15 hp) : ↥(reps ⟨66, by decide⟩)) : Coordinate 1)
        T118_66 = colFn colCertDiv_118_66_15.D1 (m := 5) from colCertDiv_118_66_15.bind1,
    show colData2 (⟨118, by decide⟩ : Fin 148)
        ((colE2 ⟨66, by decide⟩ 15 hp : ↥(Q2.reps ⟨66, by decide⟩)) : Coordinate 2)
        Q2.T118_66_2 = colFn colCertDiv_118_66_15.D2 (m := 5) from colCertDiv_118_66_15.bind2]
  rw [alnId_118 j hj]
  exact fastcode_of_div ⟨118, by decide⟩ _ _ _
    ((alnId_118 j hj) ▸ Q2.listedAt (⟨118, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨118, by decide⟩ : Fin 148) hj hq).1) colCertDiv_118_66_15_match


theorem leaf_118_66_16 (hp : 16 < (Q2.transData.getD 66 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨66, by decide⟩ : Fin 148)) (colE2 ⟨66, by decide⟩ 16 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨66, by decide⟩ : Fin 148))
        (colE1 ⟨66, by decide⟩ 16 (transLenTr ⟨66, by decide⟩ 16 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨118, by decide⟩ : Fin 148) ⟨66, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨66, by decide⟩ 16 (transLenTr ⟨66, by decide⟩ 16 hp)) T118_66
      hfix118_66 hinj118_66 hcardT118_66
      (fun i => conj_mem_of_fixedPoints _ _ (T118_66 i) (hfix118_66 i) _)
      ⟨118, by decide⟩ ⟨66, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨66, by decide⟩ 16 hp) Q2.T118_66_2 Q2.hfix118_66_2 Q2.hinj118_66_2
      Q2.hcardT118_66_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_66_2 i) (Q2.hfix118_66_2 i) _)
      ?_).symm
  rw [show colData1 (⟨118, by decide⟩ : Fin 148)
        ((colE1 ⟨66, by decide⟩ 16 (transLenTr ⟨66, by decide⟩ 16 hp) : ↥(reps ⟨66, by decide⟩)) : Coordinate 1)
        T118_66 = colFn colCertDiv_118_66_16.D1 (m := 5) from colCertDiv_118_66_16.bind1,
    show colData2 (⟨118, by decide⟩ : Fin 148)
        ((colE2 ⟨66, by decide⟩ 16 hp : ↥(Q2.reps ⟨66, by decide⟩)) : Coordinate 2)
        Q2.T118_66_2 = colFn colCertDiv_118_66_16.D2 (m := 5) from colCertDiv_118_66_16.bind2]
  rw [alnId_118 j hj]
  exact fastcode_of_div ⟨118, by decide⟩ _ _ _
    ((alnId_118 j hj) ▸ Q2.listedAt (⟨118, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨118, by decide⟩ : Fin 148) hj hq).1) colCertDiv_118_66_16_match


theorem leaf_118_66_17 (hp : 17 < (Q2.transData.getD 66 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨66, by decide⟩ : Fin 148)) (colE2 ⟨66, by decide⟩ 17 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨66, by decide⟩ : Fin 148))
        (colE1 ⟨66, by decide⟩ 17 (transLenTr ⟨66, by decide⟩ 17 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨118, by decide⟩ : Fin 148) ⟨66, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨66, by decide⟩ 17 (transLenTr ⟨66, by decide⟩ 17 hp)) T118_66
      hfix118_66 hinj118_66 hcardT118_66
      (fun i => conj_mem_of_fixedPoints _ _ (T118_66 i) (hfix118_66 i) _)
      ⟨118, by decide⟩ ⟨66, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨66, by decide⟩ 17 hp) Q2.T118_66_2 Q2.hfix118_66_2 Q2.hinj118_66_2
      Q2.hcardT118_66_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_66_2 i) (Q2.hfix118_66_2 i) _)
      ?_).symm
  rw [show colData1 (⟨118, by decide⟩ : Fin 148)
        ((colE1 ⟨66, by decide⟩ 17 (transLenTr ⟨66, by decide⟩ 17 hp) : ↥(reps ⟨66, by decide⟩)) : Coordinate 1)
        T118_66 = colFn colCertDiv_118_66_17.D1 (m := 5) from colCertDiv_118_66_17.bind1,
    show colData2 (⟨118, by decide⟩ : Fin 148)
        ((colE2 ⟨66, by decide⟩ 17 hp : ↥(Q2.reps ⟨66, by decide⟩)) : Coordinate 2)
        Q2.T118_66_2 = colFn colCertDiv_118_66_17.D2 (m := 5) from colCertDiv_118_66_17.bind2]
  rw [alnId_118 j hj]
  exact fastcode_of_div ⟨118, by decide⟩ _ _ _
    ((alnId_118 j hj) ▸ Q2.listedAt (⟨118, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨118, by decide⟩ : Fin 148) hj hq).1) colCertDiv_118_66_17_match


theorem leaf_118_66_18 (hp : 18 < (Q2.transData.getD 66 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨66, by decide⟩ : Fin 148)) (colE2 ⟨66, by decide⟩ 18 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨66, by decide⟩ : Fin 148))
        (colE1 ⟨66, by decide⟩ 18 (transLenTr ⟨66, by decide⟩ 18 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨118, by decide⟩ : Fin 148) ⟨66, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨66, by decide⟩ 18 (transLenTr ⟨66, by decide⟩ 18 hp)) T118_66
      hfix118_66 hinj118_66 hcardT118_66
      (fun i => conj_mem_of_fixedPoints _ _ (T118_66 i) (hfix118_66 i) _)
      ⟨118, by decide⟩ ⟨66, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨66, by decide⟩ 18 hp) Q2.T118_66_2 Q2.hfix118_66_2 Q2.hinj118_66_2
      Q2.hcardT118_66_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_66_2 i) (Q2.hfix118_66_2 i) _)
      ?_).symm
  rw [show colData1 (⟨118, by decide⟩ : Fin 148)
        ((colE1 ⟨66, by decide⟩ 18 (transLenTr ⟨66, by decide⟩ 18 hp) : ↥(reps ⟨66, by decide⟩)) : Coordinate 1)
        T118_66 = colFn colCertDiv_118_66_18.D1 (m := 5) from colCertDiv_118_66_18.bind1,
    show colData2 (⟨118, by decide⟩ : Fin 148)
        ((colE2 ⟨66, by decide⟩ 18 hp : ↥(Q2.reps ⟨66, by decide⟩)) : Coordinate 2)
        Q2.T118_66_2 = colFn colCertDiv_118_66_18.D2 (m := 5) from colCertDiv_118_66_18.bind2]
  rw [alnId_118 j hj]
  exact fastcode_of_div ⟨118, by decide⟩ _ _ _
    ((alnId_118 j hj) ▸ Q2.listedAt (⟨118, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨118, by decide⟩ : Fin 148) hj hq).1) colCertDiv_118_66_18_match


theorem leaf_118_66_19 (hp : 19 < (Q2.transData.getD 66 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨66, by decide⟩ : Fin 148)) (colE2 ⟨66, by decide⟩ 19 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨66, by decide⟩ : Fin 148))
        (colE1 ⟨66, by decide⟩ 19 (transLenTr ⟨66, by decide⟩ 19 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨118, by decide⟩ : Fin 148) ⟨66, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨66, by decide⟩ 19 (transLenTr ⟨66, by decide⟩ 19 hp)) T118_66
      hfix118_66 hinj118_66 hcardT118_66
      (fun i => conj_mem_of_fixedPoints _ _ (T118_66 i) (hfix118_66 i) _)
      ⟨118, by decide⟩ ⟨66, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨66, by decide⟩ 19 hp) Q2.T118_66_2 Q2.hfix118_66_2 Q2.hinj118_66_2
      Q2.hcardT118_66_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_66_2 i) (Q2.hfix118_66_2 i) _)
      ?_).symm
  rw [show colData1 (⟨118, by decide⟩ : Fin 148)
        ((colE1 ⟨66, by decide⟩ 19 (transLenTr ⟨66, by decide⟩ 19 hp) : ↥(reps ⟨66, by decide⟩)) : Coordinate 1)
        T118_66 = colFn colCertDiv_118_66_19.D1 (m := 5) from colCertDiv_118_66_19.bind1,
    show colData2 (⟨118, by decide⟩ : Fin 148)
        ((colE2 ⟨66, by decide⟩ 19 hp : ↥(Q2.reps ⟨66, by decide⟩)) : Coordinate 2)
        Q2.T118_66_2 = colFn colCertDiv_118_66_19.D2 (m := 5) from colCertDiv_118_66_19.bind2]
  rw [alnId_118 j hj]
  exact fastcode_of_div ⟨118, by decide⟩ _ _ _
    ((alnId_118 j hj) ▸ Q2.listedAt (⟨118, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨118, by decide⟩ : Fin 148) hj hq).1) colCertDiv_118_66_19_match


theorem leaf_118_66_20 (hp : 20 < (Q2.transData.getD 66 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨66, by decide⟩ : Fin 148)) (colE2 ⟨66, by decide⟩ 20 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨66, by decide⟩ : Fin 148))
        (colE1 ⟨66, by decide⟩ 20 (transLenTr ⟨66, by decide⟩ 20 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨118, by decide⟩ : Fin 148) ⟨66, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨66, by decide⟩ 20 (transLenTr ⟨66, by decide⟩ 20 hp)) T118_66
      hfix118_66 hinj118_66 hcardT118_66
      (fun i => conj_mem_of_fixedPoints _ _ (T118_66 i) (hfix118_66 i) _)
      ⟨118, by decide⟩ ⟨66, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨66, by decide⟩ 20 hp) Q2.T118_66_2 Q2.hfix118_66_2 Q2.hinj118_66_2
      Q2.hcardT118_66_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_66_2 i) (Q2.hfix118_66_2 i) _)
      ?_).symm
  rw [show colData1 (⟨118, by decide⟩ : Fin 148)
        ((colE1 ⟨66, by decide⟩ 20 (transLenTr ⟨66, by decide⟩ 20 hp) : ↥(reps ⟨66, by decide⟩)) : Coordinate 1)
        T118_66 = colFn colCertDiv_118_66_20.D1 (m := 5) from colCertDiv_118_66_20.bind1,
    show colData2 (⟨118, by decide⟩ : Fin 148)
        ((colE2 ⟨66, by decide⟩ 20 hp : ↥(Q2.reps ⟨66, by decide⟩)) : Coordinate 2)
        Q2.T118_66_2 = colFn colCertDiv_118_66_20.D2 (m := 5) from colCertDiv_118_66_20.bind2]
  rw [alnId_118 j hj]
  exact fastcode_of_div ⟨118, by decide⟩ _ _ _
    ((alnId_118 j hj) ▸ Q2.listedAt (⟨118, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨118, by decide⟩ : Fin 148) hj hq).1) colCertDiv_118_66_20_match


theorem leaf_118_66_21 (hp : 21 < (Q2.transData.getD 66 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨66, by decide⟩ : Fin 148)) (colE2 ⟨66, by decide⟩ 21 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨66, by decide⟩ : Fin 148))
        (colE1 ⟨66, by decide⟩ 21 (transLenTr ⟨66, by decide⟩ 21 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨118, by decide⟩ : Fin 148) ⟨66, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨66, by decide⟩ 21 (transLenTr ⟨66, by decide⟩ 21 hp)) T118_66
      hfix118_66 hinj118_66 hcardT118_66
      (fun i => conj_mem_of_fixedPoints _ _ (T118_66 i) (hfix118_66 i) _)
      ⟨118, by decide⟩ ⟨66, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨66, by decide⟩ 21 hp) Q2.T118_66_2 Q2.hfix118_66_2 Q2.hinj118_66_2
      Q2.hcardT118_66_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_66_2 i) (Q2.hfix118_66_2 i) _)
      ?_).symm
  rw [show colData1 (⟨118, by decide⟩ : Fin 148)
        ((colE1 ⟨66, by decide⟩ 21 (transLenTr ⟨66, by decide⟩ 21 hp) : ↥(reps ⟨66, by decide⟩)) : Coordinate 1)
        T118_66 = colFn colCertDiv_118_66_21.D1 (m := 5) from colCertDiv_118_66_21.bind1,
    show colData2 (⟨118, by decide⟩ : Fin 148)
        ((colE2 ⟨66, by decide⟩ 21 hp : ↥(Q2.reps ⟨66, by decide⟩)) : Coordinate 2)
        Q2.T118_66_2 = colFn colCertDiv_118_66_21.D2 (m := 5) from colCertDiv_118_66_21.bind2]
  rw [alnId_118 j hj]
  exact fastcode_of_div ⟨118, by decide⟩ _ _ _
    ((alnId_118 j hj) ▸ Q2.listedAt (⟨118, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨118, by decide⟩ : Fin 148) hj hq).1) colCertDiv_118_66_21_match


theorem leaf_118_66_22 (hp : 22 < (Q2.transData.getD 66 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨66, by decide⟩ : Fin 148)) (colE2 ⟨66, by decide⟩ 22 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨66, by decide⟩ : Fin 148))
        (colE1 ⟨66, by decide⟩ 22 (transLenTr ⟨66, by decide⟩ 22 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨118, by decide⟩ : Fin 148) ⟨66, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨66, by decide⟩ 22 (transLenTr ⟨66, by decide⟩ 22 hp)) T118_66
      hfix118_66 hinj118_66 hcardT118_66
      (fun i => conj_mem_of_fixedPoints _ _ (T118_66 i) (hfix118_66 i) _)
      ⟨118, by decide⟩ ⟨66, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨66, by decide⟩ 22 hp) Q2.T118_66_2 Q2.hfix118_66_2 Q2.hinj118_66_2
      Q2.hcardT118_66_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_66_2 i) (Q2.hfix118_66_2 i) _)
      ?_).symm
  rw [show colData1 (⟨118, by decide⟩ : Fin 148)
        ((colE1 ⟨66, by decide⟩ 22 (transLenTr ⟨66, by decide⟩ 22 hp) : ↥(reps ⟨66, by decide⟩)) : Coordinate 1)
        T118_66 = colFn colCertDiv_118_66_22.D1 (m := 5) from colCertDiv_118_66_22.bind1,
    show colData2 (⟨118, by decide⟩ : Fin 148)
        ((colE2 ⟨66, by decide⟩ 22 hp : ↥(Q2.reps ⟨66, by decide⟩)) : Coordinate 2)
        Q2.T118_66_2 = colFn colCertDiv_118_66_22.D2 (m := 5) from colCertDiv_118_66_22.bind2]
  rw [alnId_118 j hj]
  exact fastcode_of_div ⟨118, by decide⟩ _ _ _
    ((alnId_118 j hj) ▸ Q2.listedAt (⟨118, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨118, by decide⟩ : Fin 148) hj hq).1) colCertDiv_118_66_22_match


theorem leaf_118_66_23 (hp : 23 < (Q2.transData.getD 66 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨66, by decide⟩ : Fin 148)) (colE2 ⟨66, by decide⟩ 23 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨66, by decide⟩ : Fin 148))
        (colE1 ⟨66, by decide⟩ 23 (transLenTr ⟨66, by decide⟩ 23 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨118, by decide⟩ : Fin 148) ⟨66, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨66, by decide⟩ 23 (transLenTr ⟨66, by decide⟩ 23 hp)) T118_66
      hfix118_66 hinj118_66 hcardT118_66
      (fun i => conj_mem_of_fixedPoints _ _ (T118_66 i) (hfix118_66 i) _)
      ⟨118, by decide⟩ ⟨66, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨66, by decide⟩ 23 hp) Q2.T118_66_2 Q2.hfix118_66_2 Q2.hinj118_66_2
      Q2.hcardT118_66_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_66_2 i) (Q2.hfix118_66_2 i) _)
      ?_).symm
  rw [show colData1 (⟨118, by decide⟩ : Fin 148)
        ((colE1 ⟨66, by decide⟩ 23 (transLenTr ⟨66, by decide⟩ 23 hp) : ↥(reps ⟨66, by decide⟩)) : Coordinate 1)
        T118_66 = colFn colCertDiv_118_66_23.D1 (m := 5) from colCertDiv_118_66_23.bind1,
    show colData2 (⟨118, by decide⟩ : Fin 148)
        ((colE2 ⟨66, by decide⟩ 23 hp : ↥(Q2.reps ⟨66, by decide⟩)) : Coordinate 2)
        Q2.T118_66_2 = colFn colCertDiv_118_66_23.D2 (m := 5) from colCertDiv_118_66_23.bind2]
  rw [alnId_118 j hj]
  exact fastcode_of_div ⟨118, by decide⟩ _ _ _
    ((alnId_118 j hj) ▸ Q2.listedAt (⟨118, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨118, by decide⟩ : Fin 148) hj hq).1) colCertDiv_118_66_23_match


theorem leaf_118_66_24 (hp : 24 < (Q2.transData.getD 66 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨66, by decide⟩ : Fin 148)) (colE2 ⟨66, by decide⟩ 24 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨66, by decide⟩ : Fin 148))
        (colE1 ⟨66, by decide⟩ 24 (transLenTr ⟨66, by decide⟩ 24 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨118, by decide⟩ : Fin 148) ⟨66, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨66, by decide⟩ 24 (transLenTr ⟨66, by decide⟩ 24 hp)) T118_66
      hfix118_66 hinj118_66 hcardT118_66
      (fun i => conj_mem_of_fixedPoints _ _ (T118_66 i) (hfix118_66 i) _)
      ⟨118, by decide⟩ ⟨66, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨66, by decide⟩ 24 hp) Q2.T118_66_2 Q2.hfix118_66_2 Q2.hinj118_66_2
      Q2.hcardT118_66_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_66_2 i) (Q2.hfix118_66_2 i) _)
      ?_).symm
  rw [show colData1 (⟨118, by decide⟩ : Fin 148)
        ((colE1 ⟨66, by decide⟩ 24 (transLenTr ⟨66, by decide⟩ 24 hp) : ↥(reps ⟨66, by decide⟩)) : Coordinate 1)
        T118_66 = colFn colCertDiv_118_66_24.D1 (m := 5) from colCertDiv_118_66_24.bind1,
    show colData2 (⟨118, by decide⟩ : Fin 148)
        ((colE2 ⟨66, by decide⟩ 24 hp : ↥(Q2.reps ⟨66, by decide⟩)) : Coordinate 2)
        Q2.T118_66_2 = colFn colCertDiv_118_66_24.D2 (m := 5) from colCertDiv_118_66_24.bind2]
  rw [alnId_118 j hj]
  exact fastcode_of_div ⟨118, by decide⟩ _ _ _
    ((alnId_118 j hj) ▸ Q2.listedAt (⟨118, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨118, by decide⟩ : Fin 148) hj hq).1) colCertDiv_118_66_24_match


theorem leaf_118_67_0 (hp : 0 < (Q2.transData.getD 67 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨67, by decide⟩ : Fin 148)) (colE2 ⟨67, by decide⟩ 0 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨67, by decide⟩ : Fin 148))
        (colE1 ⟨67, by decide⟩ 0 (transLenTr ⟨67, by decide⟩ 0 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨67, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨67, by decide⟩ 0 (transLenTr ⟨67, by decide⟩ 0 hp)) T118_67
      hfix118_67 hinj118_67 hcardT118_67
      (fun i => conj_mem_of_fixedPoints _ _ (T118_67 i) (hfix118_67 i) _)
      ⟨118, by decide⟩ ⟨67, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨67, by decide⟩ 0 hp) Q2.T118_67_2 Q2.hfix118_67_2 Q2.hinj118_67_2
      Q2.hcardT118_67_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_67_2 i) (Q2.hfix118_67_2 i) _)
      colCert_118_67_0.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_67_1 (hp : 1 < (Q2.transData.getD 67 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨67, by decide⟩ : Fin 148)) (colE2 ⟨67, by decide⟩ 1 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨67, by decide⟩ : Fin 148))
        (colE1 ⟨67, by decide⟩ 1 (transLenTr ⟨67, by decide⟩ 1 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨67, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨67, by decide⟩ 1 (transLenTr ⟨67, by decide⟩ 1 hp)) T118_67
      hfix118_67 hinj118_67 hcardT118_67
      (fun i => conj_mem_of_fixedPoints _ _ (T118_67 i) (hfix118_67 i) _)
      ⟨118, by decide⟩ ⟨67, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨67, by decide⟩ 1 hp) Q2.T118_67_2 Q2.hfix118_67_2 Q2.hinj118_67_2
      Q2.hcardT118_67_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_67_2 i) (Q2.hfix118_67_2 i) _)
      colCert_118_67_1.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_67_2 (hp : 2 < (Q2.transData.getD 67 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨67, by decide⟩ : Fin 148)) (colE2 ⟨67, by decide⟩ 2 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨67, by decide⟩ : Fin 148))
        (colE1 ⟨67, by decide⟩ 2 (transLenTr ⟨67, by decide⟩ 2 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨67, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨67, by decide⟩ 2 (transLenTr ⟨67, by decide⟩ 2 hp)) T118_67
      hfix118_67 hinj118_67 hcardT118_67
      (fun i => conj_mem_of_fixedPoints _ _ (T118_67 i) (hfix118_67 i) _)
      ⟨118, by decide⟩ ⟨67, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨67, by decide⟩ 2 hp) Q2.T118_67_2 Q2.hfix118_67_2 Q2.hinj118_67_2
      Q2.hcardT118_67_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_67_2 i) (Q2.hfix118_67_2 i) _)
      colCert_118_67_2.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_67_3 (hp : 3 < (Q2.transData.getD 67 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨67, by decide⟩ : Fin 148)) (colE2 ⟨67, by decide⟩ 3 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨67, by decide⟩ : Fin 148))
        (colE1 ⟨67, by decide⟩ 3 (transLenTr ⟨67, by decide⟩ 3 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨67, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨67, by decide⟩ 3 (transLenTr ⟨67, by decide⟩ 3 hp)) T118_67
      hfix118_67 hinj118_67 hcardT118_67
      (fun i => conj_mem_of_fixedPoints _ _ (T118_67 i) (hfix118_67 i) _)
      ⟨118, by decide⟩ ⟨67, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨67, by decide⟩ 3 hp) Q2.T118_67_2 Q2.hfix118_67_2 Q2.hinj118_67_2
      Q2.hcardT118_67_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_67_2 i) (Q2.hfix118_67_2 i) _)
      colCert_118_67_3.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_67_4 (hp : 4 < (Q2.transData.getD 67 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨67, by decide⟩ : Fin 148)) (colE2 ⟨67, by decide⟩ 4 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨67, by decide⟩ : Fin 148))
        (colE1 ⟨67, by decide⟩ 4 (transLenTr ⟨67, by decide⟩ 4 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨67, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨67, by decide⟩ 4 (transLenTr ⟨67, by decide⟩ 4 hp)) T118_67
      hfix118_67 hinj118_67 hcardT118_67
      (fun i => conj_mem_of_fixedPoints _ _ (T118_67 i) (hfix118_67 i) _)
      ⟨118, by decide⟩ ⟨67, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨67, by decide⟩ 4 hp) Q2.T118_67_2 Q2.hfix118_67_2 Q2.hinj118_67_2
      Q2.hcardT118_67_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_67_2 i) (Q2.hfix118_67_2 i) _)
      colCert_118_67_4.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_67_5 (hp : 5 < (Q2.transData.getD 67 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨67, by decide⟩ : Fin 148)) (colE2 ⟨67, by decide⟩ 5 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨67, by decide⟩ : Fin 148))
        (colE1 ⟨67, by decide⟩ 5 (transLenTr ⟨67, by decide⟩ 5 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨67, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨67, by decide⟩ 5 (transLenTr ⟨67, by decide⟩ 5 hp)) T118_67
      hfix118_67 hinj118_67 hcardT118_67
      (fun i => conj_mem_of_fixedPoints _ _ (T118_67 i) (hfix118_67 i) _)
      ⟨118, by decide⟩ ⟨67, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨67, by decide⟩ 5 hp) Q2.T118_67_2 Q2.hfix118_67_2 Q2.hinj118_67_2
      Q2.hcardT118_67_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_67_2 i) (Q2.hfix118_67_2 i) _)
      colCert_118_67_5.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_67_6 (hp : 6 < (Q2.transData.getD 67 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨67, by decide⟩ : Fin 148)) (colE2 ⟨67, by decide⟩ 6 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨67, by decide⟩ : Fin 148))
        (colE1 ⟨67, by decide⟩ 6 (transLenTr ⟨67, by decide⟩ 6 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨67, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨67, by decide⟩ 6 (transLenTr ⟨67, by decide⟩ 6 hp)) T118_67
      hfix118_67 hinj118_67 hcardT118_67
      (fun i => conj_mem_of_fixedPoints _ _ (T118_67 i) (hfix118_67 i) _)
      ⟨118, by decide⟩ ⟨67, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨67, by decide⟩ 6 hp) Q2.T118_67_2 Q2.hfix118_67_2 Q2.hinj118_67_2
      Q2.hcardT118_67_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_67_2 i) (Q2.hfix118_67_2 i) _)
      colCert_118_67_6.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_67_7 (hp : 7 < (Q2.transData.getD 67 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨67, by decide⟩ : Fin 148)) (colE2 ⟨67, by decide⟩ 7 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨67, by decide⟩ : Fin 148))
        (colE1 ⟨67, by decide⟩ 7 (transLenTr ⟨67, by decide⟩ 7 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨67, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨67, by decide⟩ 7 (transLenTr ⟨67, by decide⟩ 7 hp)) T118_67
      hfix118_67 hinj118_67 hcardT118_67
      (fun i => conj_mem_of_fixedPoints _ _ (T118_67 i) (hfix118_67 i) _)
      ⟨118, by decide⟩ ⟨67, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨67, by decide⟩ 7 hp) Q2.T118_67_2 Q2.hfix118_67_2 Q2.hinj118_67_2
      Q2.hcardT118_67_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_67_2 i) (Q2.hfix118_67_2 i) _)
      colCert_118_67_7.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_67_8 (hp : 8 < (Q2.transData.getD 67 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨67, by decide⟩ : Fin 148)) (colE2 ⟨67, by decide⟩ 8 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨67, by decide⟩ : Fin 148))
        (colE1 ⟨67, by decide⟩ 8 (transLenTr ⟨67, by decide⟩ 8 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨67, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨67, by decide⟩ 8 (transLenTr ⟨67, by decide⟩ 8 hp)) T118_67
      hfix118_67 hinj118_67 hcardT118_67
      (fun i => conj_mem_of_fixedPoints _ _ (T118_67 i) (hfix118_67 i) _)
      ⟨118, by decide⟩ ⟨67, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨67, by decide⟩ 8 hp) Q2.T118_67_2 Q2.hfix118_67_2 Q2.hinj118_67_2
      Q2.hcardT118_67_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_67_2 i) (Q2.hfix118_67_2 i) _)
      colCert_118_67_8.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_67_9 (hp : 9 < (Q2.transData.getD 67 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨67, by decide⟩ : Fin 148)) (colE2 ⟨67, by decide⟩ 9 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨67, by decide⟩ : Fin 148))
        (colE1 ⟨67, by decide⟩ 9 (transLenTr ⟨67, by decide⟩ 9 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨67, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨67, by decide⟩ 9 (transLenTr ⟨67, by decide⟩ 9 hp)) T118_67
      hfix118_67 hinj118_67 hcardT118_67
      (fun i => conj_mem_of_fixedPoints _ _ (T118_67 i) (hfix118_67 i) _)
      ⟨118, by decide⟩ ⟨67, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨67, by decide⟩ 9 hp) Q2.T118_67_2 Q2.hfix118_67_2 Q2.hinj118_67_2
      Q2.hcardT118_67_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_67_2 i) (Q2.hfix118_67_2 i) _)
      colCert_118_67_9.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_67_10 (hp : 10 < (Q2.transData.getD 67 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨67, by decide⟩ : Fin 148)) (colE2 ⟨67, by decide⟩ 10 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨67, by decide⟩ : Fin 148))
        (colE1 ⟨67, by decide⟩ 10 (transLenTr ⟨67, by decide⟩ 10 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨67, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨67, by decide⟩ 10 (transLenTr ⟨67, by decide⟩ 10 hp)) T118_67
      hfix118_67 hinj118_67 hcardT118_67
      (fun i => conj_mem_of_fixedPoints _ _ (T118_67 i) (hfix118_67 i) _)
      ⟨118, by decide⟩ ⟨67, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨67, by decide⟩ 10 hp) Q2.T118_67_2 Q2.hfix118_67_2 Q2.hinj118_67_2
      Q2.hcardT118_67_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_67_2 i) (Q2.hfix118_67_2 i) _)
      colCert_118_67_10.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_67_11 (hp : 11 < (Q2.transData.getD 67 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨67, by decide⟩ : Fin 148)) (colE2 ⟨67, by decide⟩ 11 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨67, by decide⟩ : Fin 148))
        (colE1 ⟨67, by decide⟩ 11 (transLenTr ⟨67, by decide⟩ 11 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨67, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨67, by decide⟩ 11 (transLenTr ⟨67, by decide⟩ 11 hp)) T118_67
      hfix118_67 hinj118_67 hcardT118_67
      (fun i => conj_mem_of_fixedPoints _ _ (T118_67 i) (hfix118_67 i) _)
      ⟨118, by decide⟩ ⟨67, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨67, by decide⟩ 11 hp) Q2.T118_67_2 Q2.hfix118_67_2 Q2.hinj118_67_2
      Q2.hcardT118_67_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_67_2 i) (Q2.hfix118_67_2 i) _)
      colCert_118_67_11.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_67_12 (hp : 12 < (Q2.transData.getD 67 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨67, by decide⟩ : Fin 148)) (colE2 ⟨67, by decide⟩ 12 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨67, by decide⟩ : Fin 148))
        (colE1 ⟨67, by decide⟩ 12 (transLenTr ⟨67, by decide⟩ 12 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨67, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨67, by decide⟩ 12 (transLenTr ⟨67, by decide⟩ 12 hp)) T118_67
      hfix118_67 hinj118_67 hcardT118_67
      (fun i => conj_mem_of_fixedPoints _ _ (T118_67 i) (hfix118_67 i) _)
      ⟨118, by decide⟩ ⟨67, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨67, by decide⟩ 12 hp) Q2.T118_67_2 Q2.hfix118_67_2 Q2.hinj118_67_2
      Q2.hcardT118_67_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_67_2 i) (Q2.hfix118_67_2 i) _)
      colCert_118_67_12.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_67_13 (hp : 13 < (Q2.transData.getD 67 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨67, by decide⟩ : Fin 148)) (colE2 ⟨67, by decide⟩ 13 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨67, by decide⟩ : Fin 148))
        (colE1 ⟨67, by decide⟩ 13 (transLenTr ⟨67, by decide⟩ 13 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨67, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨67, by decide⟩ 13 (transLenTr ⟨67, by decide⟩ 13 hp)) T118_67
      hfix118_67 hinj118_67 hcardT118_67
      (fun i => conj_mem_of_fixedPoints _ _ (T118_67 i) (hfix118_67 i) _)
      ⟨118, by decide⟩ ⟨67, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨67, by decide⟩ 13 hp) Q2.T118_67_2 Q2.hfix118_67_2 Q2.hinj118_67_2
      Q2.hcardT118_67_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_67_2 i) (Q2.hfix118_67_2 i) _)
      colCert_118_67_13.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_67_14 (hp : 14 < (Q2.transData.getD 67 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨67, by decide⟩ : Fin 148)) (colE2 ⟨67, by decide⟩ 14 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨67, by decide⟩ : Fin 148))
        (colE1 ⟨67, by decide⟩ 14 (transLenTr ⟨67, by decide⟩ 14 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨67, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨67, by decide⟩ 14 (transLenTr ⟨67, by decide⟩ 14 hp)) T118_67
      hfix118_67 hinj118_67 hcardT118_67
      (fun i => conj_mem_of_fixedPoints _ _ (T118_67 i) (hfix118_67 i) _)
      ⟨118, by decide⟩ ⟨67, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨67, by decide⟩ 14 hp) Q2.T118_67_2 Q2.hfix118_67_2 Q2.hinj118_67_2
      Q2.hcardT118_67_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_67_2 i) (Q2.hfix118_67_2 i) _)
      colCert_118_67_14.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_67_15 (hp : 15 < (Q2.transData.getD 67 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨67, by decide⟩ : Fin 148)) (colE2 ⟨67, by decide⟩ 15 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨67, by decide⟩ : Fin 148))
        (colE1 ⟨67, by decide⟩ 15 (transLenTr ⟨67, by decide⟩ 15 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨67, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨67, by decide⟩ 15 (transLenTr ⟨67, by decide⟩ 15 hp)) T118_67
      hfix118_67 hinj118_67 hcardT118_67
      (fun i => conj_mem_of_fixedPoints _ _ (T118_67 i) (hfix118_67 i) _)
      ⟨118, by decide⟩ ⟨67, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨67, by decide⟩ 15 hp) Q2.T118_67_2 Q2.hfix118_67_2 Q2.hinj118_67_2
      Q2.hcardT118_67_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_67_2 i) (Q2.hfix118_67_2 i) _)
      colCert_118_67_15.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_67_16 (hp : 16 < (Q2.transData.getD 67 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨67, by decide⟩ : Fin 148)) (colE2 ⟨67, by decide⟩ 16 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨67, by decide⟩ : Fin 148))
        (colE1 ⟨67, by decide⟩ 16 (transLenTr ⟨67, by decide⟩ 16 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨67, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨67, by decide⟩ 16 (transLenTr ⟨67, by decide⟩ 16 hp)) T118_67
      hfix118_67 hinj118_67 hcardT118_67
      (fun i => conj_mem_of_fixedPoints _ _ (T118_67 i) (hfix118_67 i) _)
      ⟨118, by decide⟩ ⟨67, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨67, by decide⟩ 16 hp) Q2.T118_67_2 Q2.hfix118_67_2 Q2.hinj118_67_2
      Q2.hcardT118_67_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_67_2 i) (Q2.hfix118_67_2 i) _)
      colCert_118_67_16.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_67_17 (hp : 17 < (Q2.transData.getD 67 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨67, by decide⟩ : Fin 148)) (colE2 ⟨67, by decide⟩ 17 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨67, by decide⟩ : Fin 148))
        (colE1 ⟨67, by decide⟩ 17 (transLenTr ⟨67, by decide⟩ 17 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨67, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨67, by decide⟩ 17 (transLenTr ⟨67, by decide⟩ 17 hp)) T118_67
      hfix118_67 hinj118_67 hcardT118_67
      (fun i => conj_mem_of_fixedPoints _ _ (T118_67 i) (hfix118_67 i) _)
      ⟨118, by decide⟩ ⟨67, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨67, by decide⟩ 17 hp) Q2.T118_67_2 Q2.hfix118_67_2 Q2.hinj118_67_2
      Q2.hcardT118_67_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_67_2 i) (Q2.hfix118_67_2 i) _)
      colCert_118_67_17.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_67_18 (hp : 18 < (Q2.transData.getD 67 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨67, by decide⟩ : Fin 148)) (colE2 ⟨67, by decide⟩ 18 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨67, by decide⟩ : Fin 148))
        (colE1 ⟨67, by decide⟩ 18 (transLenTr ⟨67, by decide⟩ 18 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨67, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨67, by decide⟩ 18 (transLenTr ⟨67, by decide⟩ 18 hp)) T118_67
      hfix118_67 hinj118_67 hcardT118_67
      (fun i => conj_mem_of_fixedPoints _ _ (T118_67 i) (hfix118_67 i) _)
      ⟨118, by decide⟩ ⟨67, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨67, by decide⟩ 18 hp) Q2.T118_67_2 Q2.hfix118_67_2 Q2.hinj118_67_2
      Q2.hcardT118_67_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_67_2 i) (Q2.hfix118_67_2 i) _)
      colCert_118_67_18.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_67_19 (hp : 19 < (Q2.transData.getD 67 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨67, by decide⟩ : Fin 148)) (colE2 ⟨67, by decide⟩ 19 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨67, by decide⟩ : Fin 148))
        (colE1 ⟨67, by decide⟩ 19 (transLenTr ⟨67, by decide⟩ 19 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨67, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨67, by decide⟩ 19 (transLenTr ⟨67, by decide⟩ 19 hp)) T118_67
      hfix118_67 hinj118_67 hcardT118_67
      (fun i => conj_mem_of_fixedPoints _ _ (T118_67 i) (hfix118_67 i) _)
      ⟨118, by decide⟩ ⟨67, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨67, by decide⟩ 19 hp) Q2.T118_67_2 Q2.hfix118_67_2 Q2.hinj118_67_2
      Q2.hcardT118_67_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_67_2 i) (Q2.hfix118_67_2 i) _)
      colCert_118_67_19.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_67_20 (hp : 20 < (Q2.transData.getD 67 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨67, by decide⟩ : Fin 148)) (colE2 ⟨67, by decide⟩ 20 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨67, by decide⟩ : Fin 148))
        (colE1 ⟨67, by decide⟩ 20 (transLenTr ⟨67, by decide⟩ 20 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨67, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨67, by decide⟩ 20 (transLenTr ⟨67, by decide⟩ 20 hp)) T118_67
      hfix118_67 hinj118_67 hcardT118_67
      (fun i => conj_mem_of_fixedPoints _ _ (T118_67 i) (hfix118_67 i) _)
      ⟨118, by decide⟩ ⟨67, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨67, by decide⟩ 20 hp) Q2.T118_67_2 Q2.hfix118_67_2 Q2.hinj118_67_2
      Q2.hcardT118_67_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_67_2 i) (Q2.hfix118_67_2 i) _)
      colCert_118_67_20.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_67_21 (hp : 21 < (Q2.transData.getD 67 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨67, by decide⟩ : Fin 148)) (colE2 ⟨67, by decide⟩ 21 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨67, by decide⟩ : Fin 148))
        (colE1 ⟨67, by decide⟩ 21 (transLenTr ⟨67, by decide⟩ 21 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨67, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨67, by decide⟩ 21 (transLenTr ⟨67, by decide⟩ 21 hp)) T118_67
      hfix118_67 hinj118_67 hcardT118_67
      (fun i => conj_mem_of_fixedPoints _ _ (T118_67 i) (hfix118_67 i) _)
      ⟨118, by decide⟩ ⟨67, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨67, by decide⟩ 21 hp) Q2.T118_67_2 Q2.hfix118_67_2 Q2.hinj118_67_2
      Q2.hcardT118_67_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_67_2 i) (Q2.hfix118_67_2 i) _)
      colCert_118_67_21.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_67_22 (hp : 22 < (Q2.transData.getD 67 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨67, by decide⟩ : Fin 148)) (colE2 ⟨67, by decide⟩ 22 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨67, by decide⟩ : Fin 148))
        (colE1 ⟨67, by decide⟩ 22 (transLenTr ⟨67, by decide⟩ 22 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨67, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨67, by decide⟩ 22 (transLenTr ⟨67, by decide⟩ 22 hp)) T118_67
      hfix118_67 hinj118_67 hcardT118_67
      (fun i => conj_mem_of_fixedPoints _ _ (T118_67 i) (hfix118_67 i) _)
      ⟨118, by decide⟩ ⟨67, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨67, by decide⟩ 22 hp) Q2.T118_67_2 Q2.hfix118_67_2 Q2.hinj118_67_2
      Q2.hcardT118_67_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_67_2 i) (Q2.hfix118_67_2 i) _)
      colCert_118_67_22.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_67_23 (hp : 23 < (Q2.transData.getD 67 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨67, by decide⟩ : Fin 148)) (colE2 ⟨67, by decide⟩ 23 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨67, by decide⟩ : Fin 148))
        (colE1 ⟨67, by decide⟩ 23 (transLenTr ⟨67, by decide⟩ 23 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨67, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨67, by decide⟩ 23 (transLenTr ⟨67, by decide⟩ 23 hp)) T118_67
      hfix118_67 hinj118_67 hcardT118_67
      (fun i => conj_mem_of_fixedPoints _ _ (T118_67 i) (hfix118_67 i) _)
      ⟨118, by decide⟩ ⟨67, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨67, by decide⟩ 23 hp) Q2.T118_67_2 Q2.hfix118_67_2 Q2.hinj118_67_2
      Q2.hcardT118_67_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_67_2 i) (Q2.hfix118_67_2 i) _)
      colCert_118_67_23.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_67_24 (hp : 24 < (Q2.transData.getD 67 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨67, by decide⟩ : Fin 148)) (colE2 ⟨67, by decide⟩ 24 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨67, by decide⟩ : Fin 148))
        (colE1 ⟨67, by decide⟩ 24 (transLenTr ⟨67, by decide⟩ 24 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨67, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨67, by decide⟩ 24 (transLenTr ⟨67, by decide⟩ 24 hp)) T118_67
      hfix118_67 hinj118_67 hcardT118_67
      (fun i => conj_mem_of_fixedPoints _ _ (T118_67 i) (hfix118_67 i) _)
      ⟨118, by decide⟩ ⟨67, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨67, by decide⟩ 24 hp) Q2.T118_67_2 Q2.hfix118_67_2 Q2.hinj118_67_2
      Q2.hcardT118_67_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_67_2 i) (Q2.hfix118_67_2 i) _)
      colCert_118_67_24.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_67_25 (hp : 25 < (Q2.transData.getD 67 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨67, by decide⟩ : Fin 148)) (colE2 ⟨67, by decide⟩ 25 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨67, by decide⟩ : Fin 148))
        (colE1 ⟨67, by decide⟩ 25 (transLenTr ⟨67, by decide⟩ 25 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨67, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨67, by decide⟩ 25 (transLenTr ⟨67, by decide⟩ 25 hp)) T118_67
      hfix118_67 hinj118_67 hcardT118_67
      (fun i => conj_mem_of_fixedPoints _ _ (T118_67 i) (hfix118_67 i) _)
      ⟨118, by decide⟩ ⟨67, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨67, by decide⟩ 25 hp) Q2.T118_67_2 Q2.hfix118_67_2 Q2.hinj118_67_2
      Q2.hcardT118_67_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_67_2 i) (Q2.hfix118_67_2 i) _)
      colCert_118_67_25.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_67_30 (hp : 30 < (Q2.transData.getD 67 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨67, by decide⟩ : Fin 148)) (colE2 ⟨67, by decide⟩ 30 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨67, by decide⟩ : Fin 148))
        (colE1 ⟨67, by decide⟩ 30 (transLenTr ⟨67, by decide⟩ 30 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨67, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨67, by decide⟩ 30 (transLenTr ⟨67, by decide⟩ 30 hp)) T118_67
      hfix118_67 hinj118_67 hcardT118_67
      (fun i => conj_mem_of_fixedPoints _ _ (T118_67 i) (hfix118_67 i) _)
      ⟨118, by decide⟩ ⟨67, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨67, by decide⟩ 30 hp) Q2.T118_67_2 Q2.hfix118_67_2 Q2.hinj118_67_2
      Q2.hcardT118_67_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_67_2 i) (Q2.hfix118_67_2 i) _)
      colCert_118_67_30.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_67_35 (hp : 35 < (Q2.transData.getD 67 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨67, by decide⟩ : Fin 148)) (colE2 ⟨67, by decide⟩ 35 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨67, by decide⟩ : Fin 148))
        (colE1 ⟨67, by decide⟩ 35 (transLenTr ⟨67, by decide⟩ 35 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨67, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨67, by decide⟩ 35 (transLenTr ⟨67, by decide⟩ 35 hp)) T118_67
      hfix118_67 hinj118_67 hcardT118_67
      (fun i => conj_mem_of_fixedPoints _ _ (T118_67 i) (hfix118_67 i) _)
      ⟨118, by decide⟩ ⟨67, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨67, by decide⟩ 35 hp) Q2.T118_67_2 Q2.hfix118_67_2 Q2.hinj118_67_2
      Q2.hcardT118_67_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_67_2 i) (Q2.hfix118_67_2 i) _)
      colCert_118_67_35.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_67_40 (hp : 40 < (Q2.transData.getD 67 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨67, by decide⟩ : Fin 148)) (colE2 ⟨67, by decide⟩ 40 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨67, by decide⟩ : Fin 148))
        (colE1 ⟨67, by decide⟩ 40 (transLenTr ⟨67, by decide⟩ 40 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨67, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨67, by decide⟩ 40 (transLenTr ⟨67, by decide⟩ 40 hp)) T118_67
      hfix118_67 hinj118_67 hcardT118_67
      (fun i => conj_mem_of_fixedPoints _ _ (T118_67 i) (hfix118_67 i) _)
      ⟨118, by decide⟩ ⟨67, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨67, by decide⟩ 40 hp) Q2.T118_67_2 Q2.hfix118_67_2 Q2.hinj118_67_2
      Q2.hcardT118_67_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_67_2 i) (Q2.hfix118_67_2 i) _)
      colCert_118_67_40.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_67_45 (hp : 45 < (Q2.transData.getD 67 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨67, by decide⟩ : Fin 148)) (colE2 ⟨67, by decide⟩ 45 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨67, by decide⟩ : Fin 148))
        (colE1 ⟨67, by decide⟩ 45 (transLenTr ⟨67, by decide⟩ 45 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨67, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨67, by decide⟩ 45 (transLenTr ⟨67, by decide⟩ 45 hp)) T118_67
      hfix118_67 hinj118_67 hcardT118_67
      (fun i => conj_mem_of_fixedPoints _ _ (T118_67 i) (hfix118_67 i) _)
      ⟨118, by decide⟩ ⟨67, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨67, by decide⟩ 45 hp) Q2.T118_67_2 Q2.hfix118_67_2 Q2.hinj118_67_2
      Q2.hcardT118_67_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_67_2 i) (Q2.hfix118_67_2 i) _)
      colCert_118_67_45.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_67_50 (hp : 50 < (Q2.transData.getD 67 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨67, by decide⟩ : Fin 148)) (colE2 ⟨67, by decide⟩ 50 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨67, by decide⟩ : Fin 148))
        (colE1 ⟨67, by decide⟩ 50 (transLenTr ⟨67, by decide⟩ 50 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨67, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨67, by decide⟩ 50 (transLenTr ⟨67, by decide⟩ 50 hp)) T118_67
      hfix118_67 hinj118_67 hcardT118_67
      (fun i => conj_mem_of_fixedPoints _ _ (T118_67 i) (hfix118_67 i) _)
      ⟨118, by decide⟩ ⟨67, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨67, by decide⟩ 50 hp) Q2.T118_67_2 Q2.hfix118_67_2 Q2.hinj118_67_2
      Q2.hcardT118_67_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_67_2 i) (Q2.hfix118_67_2 i) _)
      colCert_118_67_50.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_67_55 (hp : 55 < (Q2.transData.getD 67 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨67, by decide⟩ : Fin 148)) (colE2 ⟨67, by decide⟩ 55 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨67, by decide⟩ : Fin 148))
        (colE1 ⟨67, by decide⟩ 55 (transLenTr ⟨67, by decide⟩ 55 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨67, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨67, by decide⟩ 55 (transLenTr ⟨67, by decide⟩ 55 hp)) T118_67
      hfix118_67 hinj118_67 hcardT118_67
      (fun i => conj_mem_of_fixedPoints _ _ (T118_67 i) (hfix118_67 i) _)
      ⟨118, by decide⟩ ⟨67, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨67, by decide⟩ 55 hp) Q2.T118_67_2 Q2.hfix118_67_2 Q2.hinj118_67_2
      Q2.hcardT118_67_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_67_2 i) (Q2.hfix118_67_2 i) _)
      colCert_118_67_55.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_67_60 (hp : 60 < (Q2.transData.getD 67 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨67, by decide⟩ : Fin 148)) (colE2 ⟨67, by decide⟩ 60 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨67, by decide⟩ : Fin 148))
        (colE1 ⟨67, by decide⟩ 60 (transLenTr ⟨67, by decide⟩ 60 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨67, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨67, by decide⟩ 60 (transLenTr ⟨67, by decide⟩ 60 hp)) T118_67
      hfix118_67 hinj118_67 hcardT118_67
      (fun i => conj_mem_of_fixedPoints _ _ (T118_67 i) (hfix118_67 i) _)
      ⟨118, by decide⟩ ⟨67, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨67, by decide⟩ 60 hp) Q2.T118_67_2 Q2.hfix118_67_2 Q2.hinj118_67_2
      Q2.hcardT118_67_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_67_2 i) (Q2.hfix118_67_2 i) _)
      colCert_118_67_60.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_67_65 (hp : 65 < (Q2.transData.getD 67 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨67, by decide⟩ : Fin 148)) (colE2 ⟨67, by decide⟩ 65 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨67, by decide⟩ : Fin 148))
        (colE1 ⟨67, by decide⟩ 65 (transLenTr ⟨67, by decide⟩ 65 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨67, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨67, by decide⟩ 65 (transLenTr ⟨67, by decide⟩ 65 hp)) T118_67
      hfix118_67 hinj118_67 hcardT118_67
      (fun i => conj_mem_of_fixedPoints _ _ (T118_67 i) (hfix118_67 i) _)
      ⟨118, by decide⟩ ⟨67, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨67, by decide⟩ 65 hp) Q2.T118_67_2 Q2.hfix118_67_2 Q2.hinj118_67_2
      Q2.hcardT118_67_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_67_2 i) (Q2.hfix118_67_2 i) _)
      colCert_118_67_65.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_67_70 (hp : 70 < (Q2.transData.getD 67 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨67, by decide⟩ : Fin 148)) (colE2 ⟨67, by decide⟩ 70 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨67, by decide⟩ : Fin 148))
        (colE1 ⟨67, by decide⟩ 70 (transLenTr ⟨67, by decide⟩ 70 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨67, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨67, by decide⟩ 70 (transLenTr ⟨67, by decide⟩ 70 hp)) T118_67
      hfix118_67 hinj118_67 hcardT118_67
      (fun i => conj_mem_of_fixedPoints _ _ (T118_67 i) (hfix118_67 i) _)
      ⟨118, by decide⟩ ⟨67, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨67, by decide⟩ 70 hp) Q2.T118_67_2 Q2.hfix118_67_2 Q2.hinj118_67_2
      Q2.hcardT118_67_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_67_2 i) (Q2.hfix118_67_2 i) _)
      colCert_118_67_70.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_67_75 (hp : 75 < (Q2.transData.getD 67 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨67, by decide⟩ : Fin 148)) (colE2 ⟨67, by decide⟩ 75 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨67, by decide⟩ : Fin 148))
        (colE1 ⟨67, by decide⟩ 75 (transLenTr ⟨67, by decide⟩ 75 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨67, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨67, by decide⟩ 75 (transLenTr ⟨67, by decide⟩ 75 hp)) T118_67
      hfix118_67 hinj118_67 hcardT118_67
      (fun i => conj_mem_of_fixedPoints _ _ (T118_67 i) (hfix118_67 i) _)
      ⟨118, by decide⟩ ⟨67, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨67, by decide⟩ 75 hp) Q2.T118_67_2 Q2.hfix118_67_2 Q2.hinj118_67_2
      Q2.hcardT118_67_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_67_2 i) (Q2.hfix118_67_2 i) _)
      colCert_118_67_75.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_67_80 (hp : 80 < (Q2.transData.getD 67 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨67, by decide⟩ : Fin 148)) (colE2 ⟨67, by decide⟩ 80 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨67, by decide⟩ : Fin 148))
        (colE1 ⟨67, by decide⟩ 80 (transLenTr ⟨67, by decide⟩ 80 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨67, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨67, by decide⟩ 80 (transLenTr ⟨67, by decide⟩ 80 hp)) T118_67
      hfix118_67 hinj118_67 hcardT118_67
      (fun i => conj_mem_of_fixedPoints _ _ (T118_67 i) (hfix118_67 i) _)
      ⟨118, by decide⟩ ⟨67, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨67, by decide⟩ 80 hp) Q2.T118_67_2 Q2.hfix118_67_2 Q2.hinj118_67_2
      Q2.hcardT118_67_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_67_2 i) (Q2.hfix118_67_2 i) _)
      colCert_118_67_80.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_67_85 (hp : 85 < (Q2.transData.getD 67 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨67, by decide⟩ : Fin 148)) (colE2 ⟨67, by decide⟩ 85 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨67, by decide⟩ : Fin 148))
        (colE1 ⟨67, by decide⟩ 85 (transLenTr ⟨67, by decide⟩ 85 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨67, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨67, by decide⟩ 85 (transLenTr ⟨67, by decide⟩ 85 hp)) T118_67
      hfix118_67 hinj118_67 hcardT118_67
      (fun i => conj_mem_of_fixedPoints _ _ (T118_67 i) (hfix118_67 i) _)
      ⟨118, by decide⟩ ⟨67, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨67, by decide⟩ 85 hp) Q2.T118_67_2 Q2.hfix118_67_2 Q2.hinj118_67_2
      Q2.hcardT118_67_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_67_2 i) (Q2.hfix118_67_2 i) _)
      colCert_118_67_85.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_67_90 (hp : 90 < (Q2.transData.getD 67 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨67, by decide⟩ : Fin 148)) (colE2 ⟨67, by decide⟩ 90 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨67, by decide⟩ : Fin 148))
        (colE1 ⟨67, by decide⟩ 90 (transLenTr ⟨67, by decide⟩ 90 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨67, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨67, by decide⟩ 90 (transLenTr ⟨67, by decide⟩ 90 hp)) T118_67
      hfix118_67 hinj118_67 hcardT118_67
      (fun i => conj_mem_of_fixedPoints _ _ (T118_67 i) (hfix118_67 i) _)
      ⟨118, by decide⟩ ⟨67, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨67, by decide⟩ 90 hp) Q2.T118_67_2 Q2.hfix118_67_2 Q2.hinj118_67_2
      Q2.hcardT118_67_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_67_2 i) (Q2.hfix118_67_2 i) _)
      colCert_118_67_90.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_67_95 (hp : 95 < (Q2.transData.getD 67 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨67, by decide⟩ : Fin 148)) (colE2 ⟨67, by decide⟩ 95 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨67, by decide⟩ : Fin 148))
        (colE1 ⟨67, by decide⟩ 95 (transLenTr ⟨67, by decide⟩ 95 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨67, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨67, by decide⟩ 95 (transLenTr ⟨67, by decide⟩ 95 hp)) T118_67
      hfix118_67 hinj118_67 hcardT118_67
      (fun i => conj_mem_of_fixedPoints _ _ (T118_67 i) (hfix118_67 i) _)
      ⟨118, by decide⟩ ⟨67, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨67, by decide⟩ 95 hp) Q2.T118_67_2 Q2.hfix118_67_2 Q2.hinj118_67_2
      Q2.hcardT118_67_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_67_2 i) (Q2.hfix118_67_2 i) _)
      colCert_118_67_95.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_67_100 (hp : 100 < (Q2.transData.getD 67 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨67, by decide⟩ : Fin 148)) (colE2 ⟨67, by decide⟩ 100 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨67, by decide⟩ : Fin 148))
        (colE1 ⟨67, by decide⟩ 100 (transLenTr ⟨67, by decide⟩ 100 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨67, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨67, by decide⟩ 100 (transLenTr ⟨67, by decide⟩ 100 hp)) T118_67
      hfix118_67 hinj118_67 hcardT118_67
      (fun i => conj_mem_of_fixedPoints _ _ (T118_67 i) (hfix118_67 i) _)
      ⟨118, by decide⟩ ⟨67, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨67, by decide⟩ 100 hp) Q2.T118_67_2 Q2.hfix118_67_2 Q2.hinj118_67_2
      Q2.hcardT118_67_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_67_2 i) (Q2.hfix118_67_2 i) _)
      colCert_118_67_100.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_67_105 (hp : 105 < (Q2.transData.getD 67 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨67, by decide⟩ : Fin 148)) (colE2 ⟨67, by decide⟩ 105 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨67, by decide⟩ : Fin 148))
        (colE1 ⟨67, by decide⟩ 105 (transLenTr ⟨67, by decide⟩ 105 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨67, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨67, by decide⟩ 105 (transLenTr ⟨67, by decide⟩ 105 hp)) T118_67
      hfix118_67 hinj118_67 hcardT118_67
      (fun i => conj_mem_of_fixedPoints _ _ (T118_67 i) (hfix118_67 i) _)
      ⟨118, by decide⟩ ⟨67, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨67, by decide⟩ 105 hp) Q2.T118_67_2 Q2.hfix118_67_2 Q2.hinj118_67_2
      Q2.hcardT118_67_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_67_2 i) (Q2.hfix118_67_2 i) _)
      colCert_118_67_105.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_67_110 (hp : 110 < (Q2.transData.getD 67 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨67, by decide⟩ : Fin 148)) (colE2 ⟨67, by decide⟩ 110 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨67, by decide⟩ : Fin 148))
        (colE1 ⟨67, by decide⟩ 110 (transLenTr ⟨67, by decide⟩ 110 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨67, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨67, by decide⟩ 110 (transLenTr ⟨67, by decide⟩ 110 hp)) T118_67
      hfix118_67 hinj118_67 hcardT118_67
      (fun i => conj_mem_of_fixedPoints _ _ (T118_67 i) (hfix118_67 i) _)
      ⟨118, by decide⟩ ⟨67, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨67, by decide⟩ 110 hp) Q2.T118_67_2 Q2.hfix118_67_2 Q2.hinj118_67_2
      Q2.hcardT118_67_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_67_2 i) (Q2.hfix118_67_2 i) _)
      colCert_118_67_110.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_67_115 (hp : 115 < (Q2.transData.getD 67 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨67, by decide⟩ : Fin 148)) (colE2 ⟨67, by decide⟩ 115 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨67, by decide⟩ : Fin 148))
        (colE1 ⟨67, by decide⟩ 115 (transLenTr ⟨67, by decide⟩ 115 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨67, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨67, by decide⟩ 115 (transLenTr ⟨67, by decide⟩ 115 hp)) T118_67
      hfix118_67 hinj118_67 hcardT118_67
      (fun i => conj_mem_of_fixedPoints _ _ (T118_67 i) (hfix118_67 i) _)
      ⟨118, by decide⟩ ⟨67, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨67, by decide⟩ 115 hp) Q2.T118_67_2 Q2.hfix118_67_2 Q2.hinj118_67_2
      Q2.hcardT118_67_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_67_2 i) (Q2.hfix118_67_2 i) _)
      colCert_118_67_115.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_67_120 (hp : 120 < (Q2.transData.getD 67 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨67, by decide⟩ : Fin 148)) (colE2 ⟨67, by decide⟩ 120 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨67, by decide⟩ : Fin 148))
        (colE1 ⟨67, by decide⟩ 120 (transLenTr ⟨67, by decide⟩ 120 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨67, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨67, by decide⟩ 120 (transLenTr ⟨67, by decide⟩ 120 hp)) T118_67
      hfix118_67 hinj118_67 hcardT118_67
      (fun i => conj_mem_of_fixedPoints _ _ (T118_67 i) (hfix118_67 i) _)
      ⟨118, by decide⟩ ⟨67, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨67, by decide⟩ 120 hp) Q2.T118_67_2 Q2.hfix118_67_2 Q2.hinj118_67_2
      Q2.hcardT118_67_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_67_2 i) (Q2.hfix118_67_2 i) _)
      colCert_118_67_120.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_68_0 (hp : 0 < (Q2.transData.getD 68 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨68, by decide⟩ : Fin 148)) (colE2 ⟨68, by decide⟩ 0 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨68, by decide⟩ : Fin 148))
        (colE1 ⟨68, by decide⟩ 0 (transLenTr ⟨68, by decide⟩ 0 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨68, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨68, by decide⟩ 0 (transLenTr ⟨68, by decide⟩ 0 hp)) T118_68
      hfix118_68 hinj118_68 hcardT118_68
      (fun i => conj_mem_of_fixedPoints _ _ (T118_68 i) (hfix118_68 i) _)
      ⟨118, by decide⟩ ⟨68, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨68, by decide⟩ 0 hp) Q2.T118_68_2 Q2.hfix118_68_2 Q2.hinj118_68_2
      Q2.hcardT118_68_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_68_2 i) (Q2.hfix118_68_2 i) _)
      colCert_118_68_0.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_68_1 (hp : 1 < (Q2.transData.getD 68 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨68, by decide⟩ : Fin 148)) (colE2 ⟨68, by decide⟩ 1 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨68, by decide⟩ : Fin 148))
        (colE1 ⟨68, by decide⟩ 1 (transLenTr ⟨68, by decide⟩ 1 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨68, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨68, by decide⟩ 1 (transLenTr ⟨68, by decide⟩ 1 hp)) T118_68
      hfix118_68 hinj118_68 hcardT118_68
      (fun i => conj_mem_of_fixedPoints _ _ (T118_68 i) (hfix118_68 i) _)
      ⟨118, by decide⟩ ⟨68, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨68, by decide⟩ 1 hp) Q2.T118_68_2 Q2.hfix118_68_2 Q2.hinj118_68_2
      Q2.hcardT118_68_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_68_2 i) (Q2.hfix118_68_2 i) _)
      colCert_118_68_1.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_68_2 (hp : 2 < (Q2.transData.getD 68 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨68, by decide⟩ : Fin 148)) (colE2 ⟨68, by decide⟩ 2 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨68, by decide⟩ : Fin 148))
        (colE1 ⟨68, by decide⟩ 2 (transLenTr ⟨68, by decide⟩ 2 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨68, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨68, by decide⟩ 2 (transLenTr ⟨68, by decide⟩ 2 hp)) T118_68
      hfix118_68 hinj118_68 hcardT118_68
      (fun i => conj_mem_of_fixedPoints _ _ (T118_68 i) (hfix118_68 i) _)
      ⟨118, by decide⟩ ⟨68, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨68, by decide⟩ 2 hp) Q2.T118_68_2 Q2.hfix118_68_2 Q2.hinj118_68_2
      Q2.hcardT118_68_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_68_2 i) (Q2.hfix118_68_2 i) _)
      colCert_118_68_2.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_68_3 (hp : 3 < (Q2.transData.getD 68 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨68, by decide⟩ : Fin 148)) (colE2 ⟨68, by decide⟩ 3 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨68, by decide⟩ : Fin 148))
        (colE1 ⟨68, by decide⟩ 3 (transLenTr ⟨68, by decide⟩ 3 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨68, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨68, by decide⟩ 3 (transLenTr ⟨68, by decide⟩ 3 hp)) T118_68
      hfix118_68 hinj118_68 hcardT118_68
      (fun i => conj_mem_of_fixedPoints _ _ (T118_68 i) (hfix118_68 i) _)
      ⟨118, by decide⟩ ⟨68, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨68, by decide⟩ 3 hp) Q2.T118_68_2 Q2.hfix118_68_2 Q2.hinj118_68_2
      Q2.hcardT118_68_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_68_2 i) (Q2.hfix118_68_2 i) _)
      colCert_118_68_3.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_68_4 (hp : 4 < (Q2.transData.getD 68 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨68, by decide⟩ : Fin 148)) (colE2 ⟨68, by decide⟩ 4 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨68, by decide⟩ : Fin 148))
        (colE1 ⟨68, by decide⟩ 4 (transLenTr ⟨68, by decide⟩ 4 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨68, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨68, by decide⟩ 4 (transLenTr ⟨68, by decide⟩ 4 hp)) T118_68
      hfix118_68 hinj118_68 hcardT118_68
      (fun i => conj_mem_of_fixedPoints _ _ (T118_68 i) (hfix118_68 i) _)
      ⟨118, by decide⟩ ⟨68, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨68, by decide⟩ 4 hp) Q2.T118_68_2 Q2.hfix118_68_2 Q2.hinj118_68_2
      Q2.hcardT118_68_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_68_2 i) (Q2.hfix118_68_2 i) _)
      colCert_118_68_4.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_68_5 (hp : 5 < (Q2.transData.getD 68 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨68, by decide⟩ : Fin 148)) (colE2 ⟨68, by decide⟩ 5 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨68, by decide⟩ : Fin 148))
        (colE1 ⟨68, by decide⟩ 5 (transLenTr ⟨68, by decide⟩ 5 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨118, by decide⟩ : Fin 148) ⟨68, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨68, by decide⟩ 5 (transLenTr ⟨68, by decide⟩ 5 hp)) T118_68
      hfix118_68 hinj118_68 hcardT118_68
      (fun i => conj_mem_of_fixedPoints _ _ (T118_68 i) (hfix118_68 i) _)
      ⟨118, by decide⟩ ⟨68, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨68, by decide⟩ 5 hp) Q2.T118_68_2 Q2.hfix118_68_2 Q2.hinj118_68_2
      Q2.hcardT118_68_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_68_2 i) (Q2.hfix118_68_2 i) _)
      ?_).symm
  rw [show colData1 (⟨118, by decide⟩ : Fin 148)
        ((colE1 ⟨68, by decide⟩ 5 (transLenTr ⟨68, by decide⟩ 5 hp) : ↥(reps ⟨68, by decide⟩)) : Coordinate 1)
        T118_68 = colFn colCertDiv_118_68_5.D1 (m := 5) from colCertDiv_118_68_5.bind1,
    show colData2 (⟨118, by decide⟩ : Fin 148)
        ((colE2 ⟨68, by decide⟩ 5 hp : ↥(Q2.reps ⟨68, by decide⟩)) : Coordinate 2)
        Q2.T118_68_2 = colFn colCertDiv_118_68_5.D2 (m := 5) from colCertDiv_118_68_5.bind2]
  rw [alnId_118 j hj]
  exact fastcode_of_div ⟨118, by decide⟩ _ _ _
    ((alnId_118 j hj) ▸ Q2.listedAt (⟨118, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨118, by decide⟩ : Fin 148) hj hq).1) colCertDiv_118_68_5_match


theorem leaf_118_68_6 (hp : 6 < (Q2.transData.getD 68 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨68, by decide⟩ : Fin 148)) (colE2 ⟨68, by decide⟩ 6 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨68, by decide⟩ : Fin 148))
        (colE1 ⟨68, by decide⟩ 6 (transLenTr ⟨68, by decide⟩ 6 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨118, by decide⟩ : Fin 148) ⟨68, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨68, by decide⟩ 6 (transLenTr ⟨68, by decide⟩ 6 hp)) T118_68
      hfix118_68 hinj118_68 hcardT118_68
      (fun i => conj_mem_of_fixedPoints _ _ (T118_68 i) (hfix118_68 i) _)
      ⟨118, by decide⟩ ⟨68, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨68, by decide⟩ 6 hp) Q2.T118_68_2 Q2.hfix118_68_2 Q2.hinj118_68_2
      Q2.hcardT118_68_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_68_2 i) (Q2.hfix118_68_2 i) _)
      ?_).symm
  rw [show colData1 (⟨118, by decide⟩ : Fin 148)
        ((colE1 ⟨68, by decide⟩ 6 (transLenTr ⟨68, by decide⟩ 6 hp) : ↥(reps ⟨68, by decide⟩)) : Coordinate 1)
        T118_68 = colFn colCertDiv_118_68_6.D1 (m := 5) from colCertDiv_118_68_6.bind1,
    show colData2 (⟨118, by decide⟩ : Fin 148)
        ((colE2 ⟨68, by decide⟩ 6 hp : ↥(Q2.reps ⟨68, by decide⟩)) : Coordinate 2)
        Q2.T118_68_2 = colFn colCertDiv_118_68_6.D2 (m := 5) from colCertDiv_118_68_6.bind2]
  rw [alnId_118 j hj]
  exact fastcode_of_div ⟨118, by decide⟩ _ _ _
    ((alnId_118 j hj) ▸ Q2.listedAt (⟨118, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨118, by decide⟩ : Fin 148) hj hq).1) colCertDiv_118_68_6_match


theorem leaf_118_68_7 (hp : 7 < (Q2.transData.getD 68 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨68, by decide⟩ : Fin 148)) (colE2 ⟨68, by decide⟩ 7 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨68, by decide⟩ : Fin 148))
        (colE1 ⟨68, by decide⟩ 7 (transLenTr ⟨68, by decide⟩ 7 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨118, by decide⟩ : Fin 148) ⟨68, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨68, by decide⟩ 7 (transLenTr ⟨68, by decide⟩ 7 hp)) T118_68
      hfix118_68 hinj118_68 hcardT118_68
      (fun i => conj_mem_of_fixedPoints _ _ (T118_68 i) (hfix118_68 i) _)
      ⟨118, by decide⟩ ⟨68, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨68, by decide⟩ 7 hp) Q2.T118_68_2 Q2.hfix118_68_2 Q2.hinj118_68_2
      Q2.hcardT118_68_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_68_2 i) (Q2.hfix118_68_2 i) _)
      ?_).symm
  rw [show colData1 (⟨118, by decide⟩ : Fin 148)
        ((colE1 ⟨68, by decide⟩ 7 (transLenTr ⟨68, by decide⟩ 7 hp) : ↥(reps ⟨68, by decide⟩)) : Coordinate 1)
        T118_68 = colFn colCertDiv_118_68_7.D1 (m := 5) from colCertDiv_118_68_7.bind1,
    show colData2 (⟨118, by decide⟩ : Fin 148)
        ((colE2 ⟨68, by decide⟩ 7 hp : ↥(Q2.reps ⟨68, by decide⟩)) : Coordinate 2)
        Q2.T118_68_2 = colFn colCertDiv_118_68_7.D2 (m := 5) from colCertDiv_118_68_7.bind2]
  rw [alnId_118 j hj]
  exact fastcode_of_div ⟨118, by decide⟩ _ _ _
    ((alnId_118 j hj) ▸ Q2.listedAt (⟨118, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨118, by decide⟩ : Fin 148) hj hq).1) colCertDiv_118_68_7_match


theorem leaf_118_68_8 (hp : 8 < (Q2.transData.getD 68 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨68, by decide⟩ : Fin 148)) (colE2 ⟨68, by decide⟩ 8 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨68, by decide⟩ : Fin 148))
        (colE1 ⟨68, by decide⟩ 8 (transLenTr ⟨68, by decide⟩ 8 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨118, by decide⟩ : Fin 148) ⟨68, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨68, by decide⟩ 8 (transLenTr ⟨68, by decide⟩ 8 hp)) T118_68
      hfix118_68 hinj118_68 hcardT118_68
      (fun i => conj_mem_of_fixedPoints _ _ (T118_68 i) (hfix118_68 i) _)
      ⟨118, by decide⟩ ⟨68, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨68, by decide⟩ 8 hp) Q2.T118_68_2 Q2.hfix118_68_2 Q2.hinj118_68_2
      Q2.hcardT118_68_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_68_2 i) (Q2.hfix118_68_2 i) _)
      ?_).symm
  rw [show colData1 (⟨118, by decide⟩ : Fin 148)
        ((colE1 ⟨68, by decide⟩ 8 (transLenTr ⟨68, by decide⟩ 8 hp) : ↥(reps ⟨68, by decide⟩)) : Coordinate 1)
        T118_68 = colFn colCertDiv_118_68_8.D1 (m := 5) from colCertDiv_118_68_8.bind1,
    show colData2 (⟨118, by decide⟩ : Fin 148)
        ((colE2 ⟨68, by decide⟩ 8 hp : ↥(Q2.reps ⟨68, by decide⟩)) : Coordinate 2)
        Q2.T118_68_2 = colFn colCertDiv_118_68_8.D2 (m := 5) from colCertDiv_118_68_8.bind2]
  rw [alnId_118 j hj]
  exact fastcode_of_div ⟨118, by decide⟩ _ _ _
    ((alnId_118 j hj) ▸ Q2.listedAt (⟨118, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨118, by decide⟩ : Fin 148) hj hq).1) colCertDiv_118_68_8_match


theorem leaf_118_68_9 (hp : 9 < (Q2.transData.getD 68 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨68, by decide⟩ : Fin 148)) (colE2 ⟨68, by decide⟩ 9 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨68, by decide⟩ : Fin 148))
        (colE1 ⟨68, by decide⟩ 9 (transLenTr ⟨68, by decide⟩ 9 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨118, by decide⟩ : Fin 148) ⟨68, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨68, by decide⟩ 9 (transLenTr ⟨68, by decide⟩ 9 hp)) T118_68
      hfix118_68 hinj118_68 hcardT118_68
      (fun i => conj_mem_of_fixedPoints _ _ (T118_68 i) (hfix118_68 i) _)
      ⟨118, by decide⟩ ⟨68, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨68, by decide⟩ 9 hp) Q2.T118_68_2 Q2.hfix118_68_2 Q2.hinj118_68_2
      Q2.hcardT118_68_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_68_2 i) (Q2.hfix118_68_2 i) _)
      ?_).symm
  rw [show colData1 (⟨118, by decide⟩ : Fin 148)
        ((colE1 ⟨68, by decide⟩ 9 (transLenTr ⟨68, by decide⟩ 9 hp) : ↥(reps ⟨68, by decide⟩)) : Coordinate 1)
        T118_68 = colFn colCertDiv_118_68_9.D1 (m := 5) from colCertDiv_118_68_9.bind1,
    show colData2 (⟨118, by decide⟩ : Fin 148)
        ((colE2 ⟨68, by decide⟩ 9 hp : ↥(Q2.reps ⟨68, by decide⟩)) : Coordinate 2)
        Q2.T118_68_2 = colFn colCertDiv_118_68_9.D2 (m := 5) from colCertDiv_118_68_9.bind2]
  rw [alnId_118 j hj]
  exact fastcode_of_div ⟨118, by decide⟩ _ _ _
    ((alnId_118 j hj) ▸ Q2.listedAt (⟨118, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨118, by decide⟩ : Fin 148) hj hq).1) colCertDiv_118_68_9_match


theorem leaf_118_68_10 (hp : 10 < (Q2.transData.getD 68 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨68, by decide⟩ : Fin 148)) (colE2 ⟨68, by decide⟩ 10 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨68, by decide⟩ : Fin 148))
        (colE1 ⟨68, by decide⟩ 10 (transLenTr ⟨68, by decide⟩ 10 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨118, by decide⟩ : Fin 148) ⟨68, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨68, by decide⟩ 10 (transLenTr ⟨68, by decide⟩ 10 hp)) T118_68
      hfix118_68 hinj118_68 hcardT118_68
      (fun i => conj_mem_of_fixedPoints _ _ (T118_68 i) (hfix118_68 i) _)
      ⟨118, by decide⟩ ⟨68, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨68, by decide⟩ 10 hp) Q2.T118_68_2 Q2.hfix118_68_2 Q2.hinj118_68_2
      Q2.hcardT118_68_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_68_2 i) (Q2.hfix118_68_2 i) _)
      ?_).symm
  rw [show colData1 (⟨118, by decide⟩ : Fin 148)
        ((colE1 ⟨68, by decide⟩ 10 (transLenTr ⟨68, by decide⟩ 10 hp) : ↥(reps ⟨68, by decide⟩)) : Coordinate 1)
        T118_68 = colFn colCertDiv_118_68_10.D1 (m := 5) from colCertDiv_118_68_10.bind1,
    show colData2 (⟨118, by decide⟩ : Fin 148)
        ((colE2 ⟨68, by decide⟩ 10 hp : ↥(Q2.reps ⟨68, by decide⟩)) : Coordinate 2)
        Q2.T118_68_2 = colFn colCertDiv_118_68_10.D2 (m := 5) from colCertDiv_118_68_10.bind2]
  rw [alnId_118 j hj]
  exact fastcode_of_div ⟨118, by decide⟩ _ _ _
    ((alnId_118 j hj) ▸ Q2.listedAt (⟨118, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨118, by decide⟩ : Fin 148) hj hq).1) colCertDiv_118_68_10_match


theorem leaf_118_68_11 (hp : 11 < (Q2.transData.getD 68 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨68, by decide⟩ : Fin 148)) (colE2 ⟨68, by decide⟩ 11 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨68, by decide⟩ : Fin 148))
        (colE1 ⟨68, by decide⟩ 11 (transLenTr ⟨68, by decide⟩ 11 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨118, by decide⟩ : Fin 148) ⟨68, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨68, by decide⟩ 11 (transLenTr ⟨68, by decide⟩ 11 hp)) T118_68
      hfix118_68 hinj118_68 hcardT118_68
      (fun i => conj_mem_of_fixedPoints _ _ (T118_68 i) (hfix118_68 i) _)
      ⟨118, by decide⟩ ⟨68, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨68, by decide⟩ 11 hp) Q2.T118_68_2 Q2.hfix118_68_2 Q2.hinj118_68_2
      Q2.hcardT118_68_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_68_2 i) (Q2.hfix118_68_2 i) _)
      ?_).symm
  rw [show colData1 (⟨118, by decide⟩ : Fin 148)
        ((colE1 ⟨68, by decide⟩ 11 (transLenTr ⟨68, by decide⟩ 11 hp) : ↥(reps ⟨68, by decide⟩)) : Coordinate 1)
        T118_68 = colFn colCertDiv_118_68_11.D1 (m := 5) from colCertDiv_118_68_11.bind1,
    show colData2 (⟨118, by decide⟩ : Fin 148)
        ((colE2 ⟨68, by decide⟩ 11 hp : ↥(Q2.reps ⟨68, by decide⟩)) : Coordinate 2)
        Q2.T118_68_2 = colFn colCertDiv_118_68_11.D2 (m := 5) from colCertDiv_118_68_11.bind2]
  rw [alnId_118 j hj]
  exact fastcode_of_div ⟨118, by decide⟩ _ _ _
    ((alnId_118 j hj) ▸ Q2.listedAt (⟨118, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨118, by decide⟩ : Fin 148) hj hq).1) colCertDiv_118_68_11_match


theorem leaf_118_68_12 (hp : 12 < (Q2.transData.getD 68 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨68, by decide⟩ : Fin 148)) (colE2 ⟨68, by decide⟩ 12 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨68, by decide⟩ : Fin 148))
        (colE1 ⟨68, by decide⟩ 12 (transLenTr ⟨68, by decide⟩ 12 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨118, by decide⟩ : Fin 148) ⟨68, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨68, by decide⟩ 12 (transLenTr ⟨68, by decide⟩ 12 hp)) T118_68
      hfix118_68 hinj118_68 hcardT118_68
      (fun i => conj_mem_of_fixedPoints _ _ (T118_68 i) (hfix118_68 i) _)
      ⟨118, by decide⟩ ⟨68, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨68, by decide⟩ 12 hp) Q2.T118_68_2 Q2.hfix118_68_2 Q2.hinj118_68_2
      Q2.hcardT118_68_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_68_2 i) (Q2.hfix118_68_2 i) _)
      ?_).symm
  rw [show colData1 (⟨118, by decide⟩ : Fin 148)
        ((colE1 ⟨68, by decide⟩ 12 (transLenTr ⟨68, by decide⟩ 12 hp) : ↥(reps ⟨68, by decide⟩)) : Coordinate 1)
        T118_68 = colFn colCertDiv_118_68_12.D1 (m := 5) from colCertDiv_118_68_12.bind1,
    show colData2 (⟨118, by decide⟩ : Fin 148)
        ((colE2 ⟨68, by decide⟩ 12 hp : ↥(Q2.reps ⟨68, by decide⟩)) : Coordinate 2)
        Q2.T118_68_2 = colFn colCertDiv_118_68_12.D2 (m := 5) from colCertDiv_118_68_12.bind2]
  rw [alnId_118 j hj]
  exact fastcode_of_div ⟨118, by decide⟩ _ _ _
    ((alnId_118 j hj) ▸ Q2.listedAt (⟨118, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨118, by decide⟩ : Fin 148) hj hq).1) colCertDiv_118_68_12_match


theorem leaf_118_68_13 (hp : 13 < (Q2.transData.getD 68 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨68, by decide⟩ : Fin 148)) (colE2 ⟨68, by decide⟩ 13 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨68, by decide⟩ : Fin 148))
        (colE1 ⟨68, by decide⟩ 13 (transLenTr ⟨68, by decide⟩ 13 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨118, by decide⟩ : Fin 148) ⟨68, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨68, by decide⟩ 13 (transLenTr ⟨68, by decide⟩ 13 hp)) T118_68
      hfix118_68 hinj118_68 hcardT118_68
      (fun i => conj_mem_of_fixedPoints _ _ (T118_68 i) (hfix118_68 i) _)
      ⟨118, by decide⟩ ⟨68, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨68, by decide⟩ 13 hp) Q2.T118_68_2 Q2.hfix118_68_2 Q2.hinj118_68_2
      Q2.hcardT118_68_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_68_2 i) (Q2.hfix118_68_2 i) _)
      ?_).symm
  rw [show colData1 (⟨118, by decide⟩ : Fin 148)
        ((colE1 ⟨68, by decide⟩ 13 (transLenTr ⟨68, by decide⟩ 13 hp) : ↥(reps ⟨68, by decide⟩)) : Coordinate 1)
        T118_68 = colFn colCertDiv_118_68_13.D1 (m := 5) from colCertDiv_118_68_13.bind1,
    show colData2 (⟨118, by decide⟩ : Fin 148)
        ((colE2 ⟨68, by decide⟩ 13 hp : ↥(Q2.reps ⟨68, by decide⟩)) : Coordinate 2)
        Q2.T118_68_2 = colFn colCertDiv_118_68_13.D2 (m := 5) from colCertDiv_118_68_13.bind2]
  rw [alnId_118 j hj]
  exact fastcode_of_div ⟨118, by decide⟩ _ _ _
    ((alnId_118 j hj) ▸ Q2.listedAt (⟨118, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨118, by decide⟩ : Fin 148) hj hq).1) colCertDiv_118_68_13_match


theorem leaf_118_68_14 (hp : 14 < (Q2.transData.getD 68 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨68, by decide⟩ : Fin 148)) (colE2 ⟨68, by decide⟩ 14 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨68, by decide⟩ : Fin 148))
        (colE1 ⟨68, by decide⟩ 14 (transLenTr ⟨68, by decide⟩ 14 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨118, by decide⟩ : Fin 148) ⟨68, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨68, by decide⟩ 14 (transLenTr ⟨68, by decide⟩ 14 hp)) T118_68
      hfix118_68 hinj118_68 hcardT118_68
      (fun i => conj_mem_of_fixedPoints _ _ (T118_68 i) (hfix118_68 i) _)
      ⟨118, by decide⟩ ⟨68, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨68, by decide⟩ 14 hp) Q2.T118_68_2 Q2.hfix118_68_2 Q2.hinj118_68_2
      Q2.hcardT118_68_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_68_2 i) (Q2.hfix118_68_2 i) _)
      ?_).symm
  rw [show colData1 (⟨118, by decide⟩ : Fin 148)
        ((colE1 ⟨68, by decide⟩ 14 (transLenTr ⟨68, by decide⟩ 14 hp) : ↥(reps ⟨68, by decide⟩)) : Coordinate 1)
        T118_68 = colFn colCertDiv_118_68_14.D1 (m := 5) from colCertDiv_118_68_14.bind1,
    show colData2 (⟨118, by decide⟩ : Fin 148)
        ((colE2 ⟨68, by decide⟩ 14 hp : ↥(Q2.reps ⟨68, by decide⟩)) : Coordinate 2)
        Q2.T118_68_2 = colFn colCertDiv_118_68_14.D2 (m := 5) from colCertDiv_118_68_14.bind2]
  rw [alnId_118 j hj]
  exact fastcode_of_div ⟨118, by decide⟩ _ _ _
    ((alnId_118 j hj) ▸ Q2.listedAt (⟨118, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨118, by decide⟩ : Fin 148) hj hq).1) colCertDiv_118_68_14_match


theorem leaf_118_68_15 (hp : 15 < (Q2.transData.getD 68 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨68, by decide⟩ : Fin 148)) (colE2 ⟨68, by decide⟩ 15 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨68, by decide⟩ : Fin 148))
        (colE1 ⟨68, by decide⟩ 15 (transLenTr ⟨68, by decide⟩ 15 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨118, by decide⟩ : Fin 148) ⟨68, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨68, by decide⟩ 15 (transLenTr ⟨68, by decide⟩ 15 hp)) T118_68
      hfix118_68 hinj118_68 hcardT118_68
      (fun i => conj_mem_of_fixedPoints _ _ (T118_68 i) (hfix118_68 i) _)
      ⟨118, by decide⟩ ⟨68, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨68, by decide⟩ 15 hp) Q2.T118_68_2 Q2.hfix118_68_2 Q2.hinj118_68_2
      Q2.hcardT118_68_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_68_2 i) (Q2.hfix118_68_2 i) _)
      ?_).symm
  rw [show colData1 (⟨118, by decide⟩ : Fin 148)
        ((colE1 ⟨68, by decide⟩ 15 (transLenTr ⟨68, by decide⟩ 15 hp) : ↥(reps ⟨68, by decide⟩)) : Coordinate 1)
        T118_68 = colFn colCertDiv_118_68_15.D1 (m := 5) from colCertDiv_118_68_15.bind1,
    show colData2 (⟨118, by decide⟩ : Fin 148)
        ((colE2 ⟨68, by decide⟩ 15 hp : ↥(Q2.reps ⟨68, by decide⟩)) : Coordinate 2)
        Q2.T118_68_2 = colFn colCertDiv_118_68_15.D2 (m := 5) from colCertDiv_118_68_15.bind2]
  rw [alnId_118 j hj]
  exact fastcode_of_div ⟨118, by decide⟩ _ _ _
    ((alnId_118 j hj) ▸ Q2.listedAt (⟨118, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨118, by decide⟩ : Fin 148) hj hq).1) colCertDiv_118_68_15_match


theorem leaf_118_68_16 (hp : 16 < (Q2.transData.getD 68 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨68, by decide⟩ : Fin 148)) (colE2 ⟨68, by decide⟩ 16 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨68, by decide⟩ : Fin 148))
        (colE1 ⟨68, by decide⟩ 16 (transLenTr ⟨68, by decide⟩ 16 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨118, by decide⟩ : Fin 148) ⟨68, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨68, by decide⟩ 16 (transLenTr ⟨68, by decide⟩ 16 hp)) T118_68
      hfix118_68 hinj118_68 hcardT118_68
      (fun i => conj_mem_of_fixedPoints _ _ (T118_68 i) (hfix118_68 i) _)
      ⟨118, by decide⟩ ⟨68, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨68, by decide⟩ 16 hp) Q2.T118_68_2 Q2.hfix118_68_2 Q2.hinj118_68_2
      Q2.hcardT118_68_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_68_2 i) (Q2.hfix118_68_2 i) _)
      ?_).symm
  rw [show colData1 (⟨118, by decide⟩ : Fin 148)
        ((colE1 ⟨68, by decide⟩ 16 (transLenTr ⟨68, by decide⟩ 16 hp) : ↥(reps ⟨68, by decide⟩)) : Coordinate 1)
        T118_68 = colFn colCertDiv_118_68_16.D1 (m := 5) from colCertDiv_118_68_16.bind1,
    show colData2 (⟨118, by decide⟩ : Fin 148)
        ((colE2 ⟨68, by decide⟩ 16 hp : ↥(Q2.reps ⟨68, by decide⟩)) : Coordinate 2)
        Q2.T118_68_2 = colFn colCertDiv_118_68_16.D2 (m := 5) from colCertDiv_118_68_16.bind2]
  rw [alnId_118 j hj]
  exact fastcode_of_div ⟨118, by decide⟩ _ _ _
    ((alnId_118 j hj) ▸ Q2.listedAt (⟨118, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨118, by decide⟩ : Fin 148) hj hq).1) colCertDiv_118_68_16_match


theorem leaf_118_68_17 (hp : 17 < (Q2.transData.getD 68 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨68, by decide⟩ : Fin 148)) (colE2 ⟨68, by decide⟩ 17 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨68, by decide⟩ : Fin 148))
        (colE1 ⟨68, by decide⟩ 17 (transLenTr ⟨68, by decide⟩ 17 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨118, by decide⟩ : Fin 148) ⟨68, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨68, by decide⟩ 17 (transLenTr ⟨68, by decide⟩ 17 hp)) T118_68
      hfix118_68 hinj118_68 hcardT118_68
      (fun i => conj_mem_of_fixedPoints _ _ (T118_68 i) (hfix118_68 i) _)
      ⟨118, by decide⟩ ⟨68, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨68, by decide⟩ 17 hp) Q2.T118_68_2 Q2.hfix118_68_2 Q2.hinj118_68_2
      Q2.hcardT118_68_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_68_2 i) (Q2.hfix118_68_2 i) _)
      ?_).symm
  rw [show colData1 (⟨118, by decide⟩ : Fin 148)
        ((colE1 ⟨68, by decide⟩ 17 (transLenTr ⟨68, by decide⟩ 17 hp) : ↥(reps ⟨68, by decide⟩)) : Coordinate 1)
        T118_68 = colFn colCertDiv_118_68_17.D1 (m := 5) from colCertDiv_118_68_17.bind1,
    show colData2 (⟨118, by decide⟩ : Fin 148)
        ((colE2 ⟨68, by decide⟩ 17 hp : ↥(Q2.reps ⟨68, by decide⟩)) : Coordinate 2)
        Q2.T118_68_2 = colFn colCertDiv_118_68_17.D2 (m := 5) from colCertDiv_118_68_17.bind2]
  rw [alnId_118 j hj]
  exact fastcode_of_div ⟨118, by decide⟩ _ _ _
    ((alnId_118 j hj) ▸ Q2.listedAt (⟨118, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨118, by decide⟩ : Fin 148) hj hq).1) colCertDiv_118_68_17_match


theorem leaf_118_68_18 (hp : 18 < (Q2.transData.getD 68 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨68, by decide⟩ : Fin 148)) (colE2 ⟨68, by decide⟩ 18 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨68, by decide⟩ : Fin 148))
        (colE1 ⟨68, by decide⟩ 18 (transLenTr ⟨68, by decide⟩ 18 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨118, by decide⟩ : Fin 148) ⟨68, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨68, by decide⟩ 18 (transLenTr ⟨68, by decide⟩ 18 hp)) T118_68
      hfix118_68 hinj118_68 hcardT118_68
      (fun i => conj_mem_of_fixedPoints _ _ (T118_68 i) (hfix118_68 i) _)
      ⟨118, by decide⟩ ⟨68, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨68, by decide⟩ 18 hp) Q2.T118_68_2 Q2.hfix118_68_2 Q2.hinj118_68_2
      Q2.hcardT118_68_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_68_2 i) (Q2.hfix118_68_2 i) _)
      ?_).symm
  rw [show colData1 (⟨118, by decide⟩ : Fin 148)
        ((colE1 ⟨68, by decide⟩ 18 (transLenTr ⟨68, by decide⟩ 18 hp) : ↥(reps ⟨68, by decide⟩)) : Coordinate 1)
        T118_68 = colFn colCertDiv_118_68_18.D1 (m := 5) from colCertDiv_118_68_18.bind1,
    show colData2 (⟨118, by decide⟩ : Fin 148)
        ((colE2 ⟨68, by decide⟩ 18 hp : ↥(Q2.reps ⟨68, by decide⟩)) : Coordinate 2)
        Q2.T118_68_2 = colFn colCertDiv_118_68_18.D2 (m := 5) from colCertDiv_118_68_18.bind2]
  rw [alnId_118 j hj]
  exact fastcode_of_div ⟨118, by decide⟩ _ _ _
    ((alnId_118 j hj) ▸ Q2.listedAt (⟨118, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨118, by decide⟩ : Fin 148) hj hq).1) colCertDiv_118_68_18_match


theorem leaf_118_68_19 (hp : 19 < (Q2.transData.getD 68 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨68, by decide⟩ : Fin 148)) (colE2 ⟨68, by decide⟩ 19 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨68, by decide⟩ : Fin 148))
        (colE1 ⟨68, by decide⟩ 19 (transLenTr ⟨68, by decide⟩ 19 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨118, by decide⟩ : Fin 148) ⟨68, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨68, by decide⟩ 19 (transLenTr ⟨68, by decide⟩ 19 hp)) T118_68
      hfix118_68 hinj118_68 hcardT118_68
      (fun i => conj_mem_of_fixedPoints _ _ (T118_68 i) (hfix118_68 i) _)
      ⟨118, by decide⟩ ⟨68, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨68, by decide⟩ 19 hp) Q2.T118_68_2 Q2.hfix118_68_2 Q2.hinj118_68_2
      Q2.hcardT118_68_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_68_2 i) (Q2.hfix118_68_2 i) _)
      ?_).symm
  rw [show colData1 (⟨118, by decide⟩ : Fin 148)
        ((colE1 ⟨68, by decide⟩ 19 (transLenTr ⟨68, by decide⟩ 19 hp) : ↥(reps ⟨68, by decide⟩)) : Coordinate 1)
        T118_68 = colFn colCertDiv_118_68_19.D1 (m := 5) from colCertDiv_118_68_19.bind1,
    show colData2 (⟨118, by decide⟩ : Fin 148)
        ((colE2 ⟨68, by decide⟩ 19 hp : ↥(Q2.reps ⟨68, by decide⟩)) : Coordinate 2)
        Q2.T118_68_2 = colFn colCertDiv_118_68_19.D2 (m := 5) from colCertDiv_118_68_19.bind2]
  rw [alnId_118 j hj]
  exact fastcode_of_tau ⟨118, by decide⟩ _ _ _
    ((alnId_118 j hj) ▸ Q2.listedAt (⟨118, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨118, by decide⟩ : Fin 148) hj hq).1) colCertDiv_118_68_19_tau_match


theorem leaf_118_68_20 (hp : 20 < (Q2.transData.getD 68 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨68, by decide⟩ : Fin 148)) (colE2 ⟨68, by decide⟩ 20 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨68, by decide⟩ : Fin 148))
        (colE1 ⟨68, by decide⟩ 20 (transLenTr ⟨68, by decide⟩ 20 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨118, by decide⟩ : Fin 148) ⟨68, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨68, by decide⟩ 20 (transLenTr ⟨68, by decide⟩ 20 hp)) T118_68
      hfix118_68 hinj118_68 hcardT118_68
      (fun i => conj_mem_of_fixedPoints _ _ (T118_68 i) (hfix118_68 i) _)
      ⟨118, by decide⟩ ⟨68, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨68, by decide⟩ 20 hp) Q2.T118_68_2 Q2.hfix118_68_2 Q2.hinj118_68_2
      Q2.hcardT118_68_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_68_2 i) (Q2.hfix118_68_2 i) _)
      ?_).symm
  rw [show colData1 (⟨118, by decide⟩ : Fin 148)
        ((colE1 ⟨68, by decide⟩ 20 (transLenTr ⟨68, by decide⟩ 20 hp) : ↥(reps ⟨68, by decide⟩)) : Coordinate 1)
        T118_68 = colFn colCertDiv_118_68_20.D1 (m := 5) from colCertDiv_118_68_20.bind1,
    show colData2 (⟨118, by decide⟩ : Fin 148)
        ((colE2 ⟨68, by decide⟩ 20 hp : ↥(Q2.reps ⟨68, by decide⟩)) : Coordinate 2)
        Q2.T118_68_2 = colFn colCertDiv_118_68_20.D2 (m := 5) from colCertDiv_118_68_20.bind2]
  rw [alnId_118 j hj]
  exact fastcode_of_tau ⟨118, by decide⟩ _ _ _
    ((alnId_118 j hj) ▸ Q2.listedAt (⟨118, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨118, by decide⟩ : Fin 148) hj hq).1) colCertDiv_118_68_20_tau_match


theorem leaf_118_68_21 (hp : 21 < (Q2.transData.getD 68 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨68, by decide⟩ : Fin 148)) (colE2 ⟨68, by decide⟩ 21 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨68, by decide⟩ : Fin 148))
        (colE1 ⟨68, by decide⟩ 21 (transLenTr ⟨68, by decide⟩ 21 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨118, by decide⟩ : Fin 148) ⟨68, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨68, by decide⟩ 21 (transLenTr ⟨68, by decide⟩ 21 hp)) T118_68
      hfix118_68 hinj118_68 hcardT118_68
      (fun i => conj_mem_of_fixedPoints _ _ (T118_68 i) (hfix118_68 i) _)
      ⟨118, by decide⟩ ⟨68, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨68, by decide⟩ 21 hp) Q2.T118_68_2 Q2.hfix118_68_2 Q2.hinj118_68_2
      Q2.hcardT118_68_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_68_2 i) (Q2.hfix118_68_2 i) _)
      ?_).symm
  rw [show colData1 (⟨118, by decide⟩ : Fin 148)
        ((colE1 ⟨68, by decide⟩ 21 (transLenTr ⟨68, by decide⟩ 21 hp) : ↥(reps ⟨68, by decide⟩)) : Coordinate 1)
        T118_68 = colFn colCertDiv_118_68_21.D1 (m := 5) from colCertDiv_118_68_21.bind1,
    show colData2 (⟨118, by decide⟩ : Fin 148)
        ((colE2 ⟨68, by decide⟩ 21 hp : ↥(Q2.reps ⟨68, by decide⟩)) : Coordinate 2)
        Q2.T118_68_2 = colFn colCertDiv_118_68_21.D2 (m := 5) from colCertDiv_118_68_21.bind2]
  rw [alnId_118 j hj]
  exact fastcode_of_tau ⟨118, by decide⟩ _ _ _
    ((alnId_118 j hj) ▸ Q2.listedAt (⟨118, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨118, by decide⟩ : Fin 148) hj hq).1) colCertDiv_118_68_21_tau_match


theorem leaf_118_68_22 (hp : 22 < (Q2.transData.getD 68 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨68, by decide⟩ : Fin 148)) (colE2 ⟨68, by decide⟩ 22 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨68, by decide⟩ : Fin 148))
        (colE1 ⟨68, by decide⟩ 22 (transLenTr ⟨68, by decide⟩ 22 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨118, by decide⟩ : Fin 148) ⟨68, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨68, by decide⟩ 22 (transLenTr ⟨68, by decide⟩ 22 hp)) T118_68
      hfix118_68 hinj118_68 hcardT118_68
      (fun i => conj_mem_of_fixedPoints _ _ (T118_68 i) (hfix118_68 i) _)
      ⟨118, by decide⟩ ⟨68, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨68, by decide⟩ 22 hp) Q2.T118_68_2 Q2.hfix118_68_2 Q2.hinj118_68_2
      Q2.hcardT118_68_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_68_2 i) (Q2.hfix118_68_2 i) _)
      ?_).symm
  rw [show colData1 (⟨118, by decide⟩ : Fin 148)
        ((colE1 ⟨68, by decide⟩ 22 (transLenTr ⟨68, by decide⟩ 22 hp) : ↥(reps ⟨68, by decide⟩)) : Coordinate 1)
        T118_68 = colFn colCertDiv_118_68_22.D1 (m := 5) from colCertDiv_118_68_22.bind1,
    show colData2 (⟨118, by decide⟩ : Fin 148)
        ((colE2 ⟨68, by decide⟩ 22 hp : ↥(Q2.reps ⟨68, by decide⟩)) : Coordinate 2)
        Q2.T118_68_2 = colFn colCertDiv_118_68_22.D2 (m := 5) from colCertDiv_118_68_22.bind2]
  rw [alnId_118 j hj]
  exact fastcode_of_tau ⟨118, by decide⟩ _ _ _
    ((alnId_118 j hj) ▸ Q2.listedAt (⟨118, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨118, by decide⟩ : Fin 148) hj hq).1) colCertDiv_118_68_22_tau_match


theorem leaf_118_68_23 (hp : 23 < (Q2.transData.getD 68 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨68, by decide⟩ : Fin 148)) (colE2 ⟨68, by decide⟩ 23 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨68, by decide⟩ : Fin 148))
        (colE1 ⟨68, by decide⟩ 23 (transLenTr ⟨68, by decide⟩ 23 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨118, by decide⟩ : Fin 148) ⟨68, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨68, by decide⟩ 23 (transLenTr ⟨68, by decide⟩ 23 hp)) T118_68
      hfix118_68 hinj118_68 hcardT118_68
      (fun i => conj_mem_of_fixedPoints _ _ (T118_68 i) (hfix118_68 i) _)
      ⟨118, by decide⟩ ⟨68, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨68, by decide⟩ 23 hp) Q2.T118_68_2 Q2.hfix118_68_2 Q2.hinj118_68_2
      Q2.hcardT118_68_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_68_2 i) (Q2.hfix118_68_2 i) _)
      ?_).symm
  rw [show colData1 (⟨118, by decide⟩ : Fin 148)
        ((colE1 ⟨68, by decide⟩ 23 (transLenTr ⟨68, by decide⟩ 23 hp) : ↥(reps ⟨68, by decide⟩)) : Coordinate 1)
        T118_68 = colFn colCertDiv_118_68_23.D1 (m := 5) from colCertDiv_118_68_23.bind1,
    show colData2 (⟨118, by decide⟩ : Fin 148)
        ((colE2 ⟨68, by decide⟩ 23 hp : ↥(Q2.reps ⟨68, by decide⟩)) : Coordinate 2)
        Q2.T118_68_2 = colFn colCertDiv_118_68_23.D2 (m := 5) from colCertDiv_118_68_23.bind2]
  rw [alnId_118 j hj]
  exact fastcode_of_div ⟨118, by decide⟩ _ _ _
    ((alnId_118 j hj) ▸ Q2.listedAt (⟨118, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨118, by decide⟩ : Fin 148) hj hq).1) colCertDiv_118_68_23_match


theorem leaf_118_68_24 (hp : 24 < (Q2.transData.getD 68 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨68, by decide⟩ : Fin 148)) (colE2 ⟨68, by decide⟩ 24 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨68, by decide⟩ : Fin 148))
        (colE1 ⟨68, by decide⟩ 24 (transLenTr ⟨68, by decide⟩ 24 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨118, by decide⟩ : Fin 148) ⟨68, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨68, by decide⟩ 24 (transLenTr ⟨68, by decide⟩ 24 hp)) T118_68
      hfix118_68 hinj118_68 hcardT118_68
      (fun i => conj_mem_of_fixedPoints _ _ (T118_68 i) (hfix118_68 i) _)
      ⟨118, by decide⟩ ⟨68, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨68, by decide⟩ 24 hp) Q2.T118_68_2 Q2.hfix118_68_2 Q2.hinj118_68_2
      Q2.hcardT118_68_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_68_2 i) (Q2.hfix118_68_2 i) _)
      ?_).symm
  rw [show colData1 (⟨118, by decide⟩ : Fin 148)
        ((colE1 ⟨68, by decide⟩ 24 (transLenTr ⟨68, by decide⟩ 24 hp) : ↥(reps ⟨68, by decide⟩)) : Coordinate 1)
        T118_68 = colFn colCertDiv_118_68_24.D1 (m := 5) from colCertDiv_118_68_24.bind1,
    show colData2 (⟨118, by decide⟩ : Fin 148)
        ((colE2 ⟨68, by decide⟩ 24 hp : ↥(Q2.reps ⟨68, by decide⟩)) : Coordinate 2)
        Q2.T118_68_2 = colFn colCertDiv_118_68_24.D2 (m := 5) from colCertDiv_118_68_24.bind2]
  rw [alnId_118 j hj]
  exact fastcode_of_div ⟨118, by decide⟩ _ _ _
    ((alnId_118 j hj) ▸ Q2.listedAt (⟨118, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨118, by decide⟩ : Fin 148) hj hq).1) colCertDiv_118_68_24_match


theorem leaf_118_69_0 (hp : 0 < (Q2.transData.getD 69 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨69, by decide⟩ : Fin 148)) (colE2 ⟨69, by decide⟩ 0 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨69, by decide⟩ : Fin 148))
        (colE1 ⟨69, by decide⟩ 0 (transLenTr ⟨69, by decide⟩ 0 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨69, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨69, by decide⟩ 0 (transLenTr ⟨69, by decide⟩ 0 hp)) T118_69
      hfix118_69 hinj118_69 hcardT118_69
      (fun i => conj_mem_of_fixedPoints _ _ (T118_69 i) (hfix118_69 i) _)
      ⟨118, by decide⟩ ⟨69, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨69, by decide⟩ 0 hp) Q2.T118_69_2 Q2.hfix118_69_2 Q2.hinj118_69_2
      Q2.hcardT118_69_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_69_2 i) (Q2.hfix118_69_2 i) _)
      colCert_118_69_0.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_69_1 (hp : 1 < (Q2.transData.getD 69 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨69, by decide⟩ : Fin 148)) (colE2 ⟨69, by decide⟩ 1 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨69, by decide⟩ : Fin 148))
        (colE1 ⟨69, by decide⟩ 1 (transLenTr ⟨69, by decide⟩ 1 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨69, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨69, by decide⟩ 1 (transLenTr ⟨69, by decide⟩ 1 hp)) T118_69
      hfix118_69 hinj118_69 hcardT118_69
      (fun i => conj_mem_of_fixedPoints _ _ (T118_69 i) (hfix118_69 i) _)
      ⟨118, by decide⟩ ⟨69, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨69, by decide⟩ 1 hp) Q2.T118_69_2 Q2.hfix118_69_2 Q2.hinj118_69_2
      Q2.hcardT118_69_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_69_2 i) (Q2.hfix118_69_2 i) _)
      colCert_118_69_1.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_69_2 (hp : 2 < (Q2.transData.getD 69 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨69, by decide⟩ : Fin 148)) (colE2 ⟨69, by decide⟩ 2 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨69, by decide⟩ : Fin 148))
        (colE1 ⟨69, by decide⟩ 2 (transLenTr ⟨69, by decide⟩ 2 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨69, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨69, by decide⟩ 2 (transLenTr ⟨69, by decide⟩ 2 hp)) T118_69
      hfix118_69 hinj118_69 hcardT118_69
      (fun i => conj_mem_of_fixedPoints _ _ (T118_69 i) (hfix118_69 i) _)
      ⟨118, by decide⟩ ⟨69, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨69, by decide⟩ 2 hp) Q2.T118_69_2 Q2.hfix118_69_2 Q2.hinj118_69_2
      Q2.hcardT118_69_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_69_2 i) (Q2.hfix118_69_2 i) _)
      colCert_118_69_2.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_69_3 (hp : 3 < (Q2.transData.getD 69 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨69, by decide⟩ : Fin 148)) (colE2 ⟨69, by decide⟩ 3 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨69, by decide⟩ : Fin 148))
        (colE1 ⟨69, by decide⟩ 3 (transLenTr ⟨69, by decide⟩ 3 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨69, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨69, by decide⟩ 3 (transLenTr ⟨69, by decide⟩ 3 hp)) T118_69
      hfix118_69 hinj118_69 hcardT118_69
      (fun i => conj_mem_of_fixedPoints _ _ (T118_69 i) (hfix118_69 i) _)
      ⟨118, by decide⟩ ⟨69, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨69, by decide⟩ 3 hp) Q2.T118_69_2 Q2.hfix118_69_2 Q2.hinj118_69_2
      Q2.hcardT118_69_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_69_2 i) (Q2.hfix118_69_2 i) _)
      colCert_118_69_3.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_69_4 (hp : 4 < (Q2.transData.getD 69 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨69, by decide⟩ : Fin 148)) (colE2 ⟨69, by decide⟩ 4 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨69, by decide⟩ : Fin 148))
        (colE1 ⟨69, by decide⟩ 4 (transLenTr ⟨69, by decide⟩ 4 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨69, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨69, by decide⟩ 4 (transLenTr ⟨69, by decide⟩ 4 hp)) T118_69
      hfix118_69 hinj118_69 hcardT118_69
      (fun i => conj_mem_of_fixedPoints _ _ (T118_69 i) (hfix118_69 i) _)
      ⟨118, by decide⟩ ⟨69, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨69, by decide⟩ 4 hp) Q2.T118_69_2 Q2.hfix118_69_2 Q2.hinj118_69_2
      Q2.hcardT118_69_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_69_2 i) (Q2.hfix118_69_2 i) _)
      colCert_118_69_4.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_69_5 (hp : 5 < (Q2.transData.getD 69 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨69, by decide⟩ : Fin 148)) (colE2 ⟨69, by decide⟩ 5 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨69, by decide⟩ : Fin 148))
        (colE1 ⟨69, by decide⟩ 5 (transLenTr ⟨69, by decide⟩ 5 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨69, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨69, by decide⟩ 5 (transLenTr ⟨69, by decide⟩ 5 hp)) T118_69
      hfix118_69 hinj118_69 hcardT118_69
      (fun i => conj_mem_of_fixedPoints _ _ (T118_69 i) (hfix118_69 i) _)
      ⟨118, by decide⟩ ⟨69, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨69, by decide⟩ 5 hp) Q2.T118_69_2 Q2.hfix118_69_2 Q2.hinj118_69_2
      Q2.hcardT118_69_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_69_2 i) (Q2.hfix118_69_2 i) _)
      colCert_118_69_5.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_69_6 (hp : 6 < (Q2.transData.getD 69 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨69, by decide⟩ : Fin 148)) (colE2 ⟨69, by decide⟩ 6 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨69, by decide⟩ : Fin 148))
        (colE1 ⟨69, by decide⟩ 6 (transLenTr ⟨69, by decide⟩ 6 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨69, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨69, by decide⟩ 6 (transLenTr ⟨69, by decide⟩ 6 hp)) T118_69
      hfix118_69 hinj118_69 hcardT118_69
      (fun i => conj_mem_of_fixedPoints _ _ (T118_69 i) (hfix118_69 i) _)
      ⟨118, by decide⟩ ⟨69, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨69, by decide⟩ 6 hp) Q2.T118_69_2 Q2.hfix118_69_2 Q2.hinj118_69_2
      Q2.hcardT118_69_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_69_2 i) (Q2.hfix118_69_2 i) _)
      colCert_118_69_6.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_69_7 (hp : 7 < (Q2.transData.getD 69 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨69, by decide⟩ : Fin 148)) (colE2 ⟨69, by decide⟩ 7 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨69, by decide⟩ : Fin 148))
        (colE1 ⟨69, by decide⟩ 7 (transLenTr ⟨69, by decide⟩ 7 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨69, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨69, by decide⟩ 7 (transLenTr ⟨69, by decide⟩ 7 hp)) T118_69
      hfix118_69 hinj118_69 hcardT118_69
      (fun i => conj_mem_of_fixedPoints _ _ (T118_69 i) (hfix118_69 i) _)
      ⟨118, by decide⟩ ⟨69, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨69, by decide⟩ 7 hp) Q2.T118_69_2 Q2.hfix118_69_2 Q2.hinj118_69_2
      Q2.hcardT118_69_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_69_2 i) (Q2.hfix118_69_2 i) _)
      colCert_118_69_7.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_69_8 (hp : 8 < (Q2.transData.getD 69 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨69, by decide⟩ : Fin 148)) (colE2 ⟨69, by decide⟩ 8 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨69, by decide⟩ : Fin 148))
        (colE1 ⟨69, by decide⟩ 8 (transLenTr ⟨69, by decide⟩ 8 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨69, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨69, by decide⟩ 8 (transLenTr ⟨69, by decide⟩ 8 hp)) T118_69
      hfix118_69 hinj118_69 hcardT118_69
      (fun i => conj_mem_of_fixedPoints _ _ (T118_69 i) (hfix118_69 i) _)
      ⟨118, by decide⟩ ⟨69, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨69, by decide⟩ 8 hp) Q2.T118_69_2 Q2.hfix118_69_2 Q2.hinj118_69_2
      Q2.hcardT118_69_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_69_2 i) (Q2.hfix118_69_2 i) _)
      colCert_118_69_8.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_69_9 (hp : 9 < (Q2.transData.getD 69 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨69, by decide⟩ : Fin 148)) (colE2 ⟨69, by decide⟩ 9 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨69, by decide⟩ : Fin 148))
        (colE1 ⟨69, by decide⟩ 9 (transLenTr ⟨69, by decide⟩ 9 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨69, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨69, by decide⟩ 9 (transLenTr ⟨69, by decide⟩ 9 hp)) T118_69
      hfix118_69 hinj118_69 hcardT118_69
      (fun i => conj_mem_of_fixedPoints _ _ (T118_69 i) (hfix118_69 i) _)
      ⟨118, by decide⟩ ⟨69, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨69, by decide⟩ 9 hp) Q2.T118_69_2 Q2.hfix118_69_2 Q2.hinj118_69_2
      Q2.hcardT118_69_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_69_2 i) (Q2.hfix118_69_2 i) _)
      colCert_118_69_9.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_69_10 (hp : 10 < (Q2.transData.getD 69 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨69, by decide⟩ : Fin 148)) (colE2 ⟨69, by decide⟩ 10 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨69, by decide⟩ : Fin 148))
        (colE1 ⟨69, by decide⟩ 10 (transLenTr ⟨69, by decide⟩ 10 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨69, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨69, by decide⟩ 10 (transLenTr ⟨69, by decide⟩ 10 hp)) T118_69
      hfix118_69 hinj118_69 hcardT118_69
      (fun i => conj_mem_of_fixedPoints _ _ (T118_69 i) (hfix118_69 i) _)
      ⟨118, by decide⟩ ⟨69, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨69, by decide⟩ 10 hp) Q2.T118_69_2 Q2.hfix118_69_2 Q2.hinj118_69_2
      Q2.hcardT118_69_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_69_2 i) (Q2.hfix118_69_2 i) _)
      colCert_118_69_10.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_69_11 (hp : 11 < (Q2.transData.getD 69 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨69, by decide⟩ : Fin 148)) (colE2 ⟨69, by decide⟩ 11 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨69, by decide⟩ : Fin 148))
        (colE1 ⟨69, by decide⟩ 11 (transLenTr ⟨69, by decide⟩ 11 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨69, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨69, by decide⟩ 11 (transLenTr ⟨69, by decide⟩ 11 hp)) T118_69
      hfix118_69 hinj118_69 hcardT118_69
      (fun i => conj_mem_of_fixedPoints _ _ (T118_69 i) (hfix118_69 i) _)
      ⟨118, by decide⟩ ⟨69, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨69, by decide⟩ 11 hp) Q2.T118_69_2 Q2.hfix118_69_2 Q2.hinj118_69_2
      Q2.hcardT118_69_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_69_2 i) (Q2.hfix118_69_2 i) _)
      colCert_118_69_11.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_69_12 (hp : 12 < (Q2.transData.getD 69 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨69, by decide⟩ : Fin 148)) (colE2 ⟨69, by decide⟩ 12 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨69, by decide⟩ : Fin 148))
        (colE1 ⟨69, by decide⟩ 12 (transLenTr ⟨69, by decide⟩ 12 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨69, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨69, by decide⟩ 12 (transLenTr ⟨69, by decide⟩ 12 hp)) T118_69
      hfix118_69 hinj118_69 hcardT118_69
      (fun i => conj_mem_of_fixedPoints _ _ (T118_69 i) (hfix118_69 i) _)
      ⟨118, by decide⟩ ⟨69, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨69, by decide⟩ 12 hp) Q2.T118_69_2 Q2.hfix118_69_2 Q2.hinj118_69_2
      Q2.hcardT118_69_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_69_2 i) (Q2.hfix118_69_2 i) _)
      colCert_118_69_12.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_69_13 (hp : 13 < (Q2.transData.getD 69 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨69, by decide⟩ : Fin 148)) (colE2 ⟨69, by decide⟩ 13 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨69, by decide⟩ : Fin 148))
        (colE1 ⟨69, by decide⟩ 13 (transLenTr ⟨69, by decide⟩ 13 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨69, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨69, by decide⟩ 13 (transLenTr ⟨69, by decide⟩ 13 hp)) T118_69
      hfix118_69 hinj118_69 hcardT118_69
      (fun i => conj_mem_of_fixedPoints _ _ (T118_69 i) (hfix118_69 i) _)
      ⟨118, by decide⟩ ⟨69, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨69, by decide⟩ 13 hp) Q2.T118_69_2 Q2.hfix118_69_2 Q2.hinj118_69_2
      Q2.hcardT118_69_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_69_2 i) (Q2.hfix118_69_2 i) _)
      colCert_118_69_13.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_69_14 (hp : 14 < (Q2.transData.getD 69 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨69, by decide⟩ : Fin 148)) (colE2 ⟨69, by decide⟩ 14 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨69, by decide⟩ : Fin 148))
        (colE1 ⟨69, by decide⟩ 14 (transLenTr ⟨69, by decide⟩ 14 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨69, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨69, by decide⟩ 14 (transLenTr ⟨69, by decide⟩ 14 hp)) T118_69
      hfix118_69 hinj118_69 hcardT118_69
      (fun i => conj_mem_of_fixedPoints _ _ (T118_69 i) (hfix118_69 i) _)
      ⟨118, by decide⟩ ⟨69, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨69, by decide⟩ 14 hp) Q2.T118_69_2 Q2.hfix118_69_2 Q2.hinj118_69_2
      Q2.hcardT118_69_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_69_2 i) (Q2.hfix118_69_2 i) _)
      colCert_118_69_14.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_69_15 (hp : 15 < (Q2.transData.getD 69 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨69, by decide⟩ : Fin 148)) (colE2 ⟨69, by decide⟩ 15 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨69, by decide⟩ : Fin 148))
        (colE1 ⟨69, by decide⟩ 15 (transLenTr ⟨69, by decide⟩ 15 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨69, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨69, by decide⟩ 15 (transLenTr ⟨69, by decide⟩ 15 hp)) T118_69
      hfix118_69 hinj118_69 hcardT118_69
      (fun i => conj_mem_of_fixedPoints _ _ (T118_69 i) (hfix118_69 i) _)
      ⟨118, by decide⟩ ⟨69, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨69, by decide⟩ 15 hp) Q2.T118_69_2 Q2.hfix118_69_2 Q2.hinj118_69_2
      Q2.hcardT118_69_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_69_2 i) (Q2.hfix118_69_2 i) _)
      colCert_118_69_15.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_69_16 (hp : 16 < (Q2.transData.getD 69 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨69, by decide⟩ : Fin 148)) (colE2 ⟨69, by decide⟩ 16 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨69, by decide⟩ : Fin 148))
        (colE1 ⟨69, by decide⟩ 16 (transLenTr ⟨69, by decide⟩ 16 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨69, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨69, by decide⟩ 16 (transLenTr ⟨69, by decide⟩ 16 hp)) T118_69
      hfix118_69 hinj118_69 hcardT118_69
      (fun i => conj_mem_of_fixedPoints _ _ (T118_69 i) (hfix118_69 i) _)
      ⟨118, by decide⟩ ⟨69, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨69, by decide⟩ 16 hp) Q2.T118_69_2 Q2.hfix118_69_2 Q2.hinj118_69_2
      Q2.hcardT118_69_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_69_2 i) (Q2.hfix118_69_2 i) _)
      colCert_118_69_16.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_69_17 (hp : 17 < (Q2.transData.getD 69 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨69, by decide⟩ : Fin 148)) (colE2 ⟨69, by decide⟩ 17 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨69, by decide⟩ : Fin 148))
        (colE1 ⟨69, by decide⟩ 17 (transLenTr ⟨69, by decide⟩ 17 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨69, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨69, by decide⟩ 17 (transLenTr ⟨69, by decide⟩ 17 hp)) T118_69
      hfix118_69 hinj118_69 hcardT118_69
      (fun i => conj_mem_of_fixedPoints _ _ (T118_69 i) (hfix118_69 i) _)
      ⟨118, by decide⟩ ⟨69, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨69, by decide⟩ 17 hp) Q2.T118_69_2 Q2.hfix118_69_2 Q2.hinj118_69_2
      Q2.hcardT118_69_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_69_2 i) (Q2.hfix118_69_2 i) _)
      colCert_118_69_17.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_69_18 (hp : 18 < (Q2.transData.getD 69 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨69, by decide⟩ : Fin 148)) (colE2 ⟨69, by decide⟩ 18 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨69, by decide⟩ : Fin 148))
        (colE1 ⟨69, by decide⟩ 18 (transLenTr ⟨69, by decide⟩ 18 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨69, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨69, by decide⟩ 18 (transLenTr ⟨69, by decide⟩ 18 hp)) T118_69
      hfix118_69 hinj118_69 hcardT118_69
      (fun i => conj_mem_of_fixedPoints _ _ (T118_69 i) (hfix118_69 i) _)
      ⟨118, by decide⟩ ⟨69, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨69, by decide⟩ 18 hp) Q2.T118_69_2 Q2.hfix118_69_2 Q2.hinj118_69_2
      Q2.hcardT118_69_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_69_2 i) (Q2.hfix118_69_2 i) _)
      colCert_118_69_18.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_69_19 (hp : 19 < (Q2.transData.getD 69 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨69, by decide⟩ : Fin 148)) (colE2 ⟨69, by decide⟩ 19 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨69, by decide⟩ : Fin 148))
        (colE1 ⟨69, by decide⟩ 19 (transLenTr ⟨69, by decide⟩ 19 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨69, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨69, by decide⟩ 19 (transLenTr ⟨69, by decide⟩ 19 hp)) T118_69
      hfix118_69 hinj118_69 hcardT118_69
      (fun i => conj_mem_of_fixedPoints _ _ (T118_69 i) (hfix118_69 i) _)
      ⟨118, by decide⟩ ⟨69, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨69, by decide⟩ 19 hp) Q2.T118_69_2 Q2.hfix118_69_2 Q2.hinj118_69_2
      Q2.hcardT118_69_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_69_2 i) (Q2.hfix118_69_2 i) _)
      colCert_118_69_19.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_69_20 (hp : 20 < (Q2.transData.getD 69 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨69, by decide⟩ : Fin 148)) (colE2 ⟨69, by decide⟩ 20 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨69, by decide⟩ : Fin 148))
        (colE1 ⟨69, by decide⟩ 20 (transLenTr ⟨69, by decide⟩ 20 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨69, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨69, by decide⟩ 20 (transLenTr ⟨69, by decide⟩ 20 hp)) T118_69
      hfix118_69 hinj118_69 hcardT118_69
      (fun i => conj_mem_of_fixedPoints _ _ (T118_69 i) (hfix118_69 i) _)
      ⟨118, by decide⟩ ⟨69, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨69, by decide⟩ 20 hp) Q2.T118_69_2 Q2.hfix118_69_2 Q2.hinj118_69_2
      Q2.hcardT118_69_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_69_2 i) (Q2.hfix118_69_2 i) _)
      colCert_118_69_20.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_69_21 (hp : 21 < (Q2.transData.getD 69 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨69, by decide⟩ : Fin 148)) (colE2 ⟨69, by decide⟩ 21 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨69, by decide⟩ : Fin 148))
        (colE1 ⟨69, by decide⟩ 21 (transLenTr ⟨69, by decide⟩ 21 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨69, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨69, by decide⟩ 21 (transLenTr ⟨69, by decide⟩ 21 hp)) T118_69
      hfix118_69 hinj118_69 hcardT118_69
      (fun i => conj_mem_of_fixedPoints _ _ (T118_69 i) (hfix118_69 i) _)
      ⟨118, by decide⟩ ⟨69, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨69, by decide⟩ 21 hp) Q2.T118_69_2 Q2.hfix118_69_2 Q2.hinj118_69_2
      Q2.hcardT118_69_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_69_2 i) (Q2.hfix118_69_2 i) _)
      colCert_118_69_21.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_69_22 (hp : 22 < (Q2.transData.getD 69 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨69, by decide⟩ : Fin 148)) (colE2 ⟨69, by decide⟩ 22 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨69, by decide⟩ : Fin 148))
        (colE1 ⟨69, by decide⟩ 22 (transLenTr ⟨69, by decide⟩ 22 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨69, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨69, by decide⟩ 22 (transLenTr ⟨69, by decide⟩ 22 hp)) T118_69
      hfix118_69 hinj118_69 hcardT118_69
      (fun i => conj_mem_of_fixedPoints _ _ (T118_69 i) (hfix118_69 i) _)
      ⟨118, by decide⟩ ⟨69, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨69, by decide⟩ 22 hp) Q2.T118_69_2 Q2.hfix118_69_2 Q2.hinj118_69_2
      Q2.hcardT118_69_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_69_2 i) (Q2.hfix118_69_2 i) _)
      colCert_118_69_22.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_69_23 (hp : 23 < (Q2.transData.getD 69 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨69, by decide⟩ : Fin 148)) (colE2 ⟨69, by decide⟩ 23 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨69, by decide⟩ : Fin 148))
        (colE1 ⟨69, by decide⟩ 23 (transLenTr ⟨69, by decide⟩ 23 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨69, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨69, by decide⟩ 23 (transLenTr ⟨69, by decide⟩ 23 hp)) T118_69
      hfix118_69 hinj118_69 hcardT118_69
      (fun i => conj_mem_of_fixedPoints _ _ (T118_69 i) (hfix118_69 i) _)
      ⟨118, by decide⟩ ⟨69, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨69, by decide⟩ 23 hp) Q2.T118_69_2 Q2.hfix118_69_2 Q2.hinj118_69_2
      Q2.hcardT118_69_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_69_2 i) (Q2.hfix118_69_2 i) _)
      colCert_118_69_23.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_69_24 (hp : 24 < (Q2.transData.getD 69 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨69, by decide⟩ : Fin 148)) (colE2 ⟨69, by decide⟩ 24 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨69, by decide⟩ : Fin 148))
        (colE1 ⟨69, by decide⟩ 24 (transLenTr ⟨69, by decide⟩ 24 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨69, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨69, by decide⟩ 24 (transLenTr ⟨69, by decide⟩ 24 hp)) T118_69
      hfix118_69 hinj118_69 hcardT118_69
      (fun i => conj_mem_of_fixedPoints _ _ (T118_69 i) (hfix118_69 i) _)
      ⟨118, by decide⟩ ⟨69, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨69, by decide⟩ 24 hp) Q2.T118_69_2 Q2.hfix118_69_2 Q2.hinj118_69_2
      Q2.hcardT118_69_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_69_2 i) (Q2.hfix118_69_2 i) _)
      colCert_118_69_24.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_80_0 (hp : 0 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 0 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 0 (transLenTr ⟨80, by decide⟩ 0 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 0 (transLenTr ⟨80, by decide⟩ 0 hp)) T118_80
      hfix118_80 hinj118_80 hcardT118_80
      (fun i => conj_mem_of_fixedPoints _ _ (T118_80 i) (hfix118_80 i) _)
      ⟨118, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 0 hp) Q2.T118_80_2 Q2.hfix118_80_2 Q2.hinj118_80_2
      Q2.hcardT118_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_80_2 i) (Q2.hfix118_80_2 i) _)
      colCert_118_80_0.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_80_1 (hp : 1 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 1 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 1 (transLenTr ⟨80, by decide⟩ 1 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 1 (transLenTr ⟨80, by decide⟩ 1 hp)) T118_80
      hfix118_80 hinj118_80 hcardT118_80
      (fun i => conj_mem_of_fixedPoints _ _ (T118_80 i) (hfix118_80 i) _)
      ⟨118, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 1 hp) Q2.T118_80_2 Q2.hfix118_80_2 Q2.hinj118_80_2
      Q2.hcardT118_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_80_2 i) (Q2.hfix118_80_2 i) _)
      colCert_118_80_1.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_80_2 (hp : 2 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 2 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 2 (transLenTr ⟨80, by decide⟩ 2 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 2 (transLenTr ⟨80, by decide⟩ 2 hp)) T118_80
      hfix118_80 hinj118_80 hcardT118_80
      (fun i => conj_mem_of_fixedPoints _ _ (T118_80 i) (hfix118_80 i) _)
      ⟨118, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 2 hp) Q2.T118_80_2 Q2.hfix118_80_2 Q2.hinj118_80_2
      Q2.hcardT118_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_80_2 i) (Q2.hfix118_80_2 i) _)
      colCert_118_80_2.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_80_3 (hp : 3 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 3 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 3 (transLenTr ⟨80, by decide⟩ 3 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 3 (transLenTr ⟨80, by decide⟩ 3 hp)) T118_80
      hfix118_80 hinj118_80 hcardT118_80
      (fun i => conj_mem_of_fixedPoints _ _ (T118_80 i) (hfix118_80 i) _)
      ⟨118, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 3 hp) Q2.T118_80_2 Q2.hfix118_80_2 Q2.hinj118_80_2
      Q2.hcardT118_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_80_2 i) (Q2.hfix118_80_2 i) _)
      colCert_118_80_3.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_80_4 (hp : 4 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 4 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 4 (transLenTr ⟨80, by decide⟩ 4 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 4 (transLenTr ⟨80, by decide⟩ 4 hp)) T118_80
      hfix118_80 hinj118_80 hcardT118_80
      (fun i => conj_mem_of_fixedPoints _ _ (T118_80 i) (hfix118_80 i) _)
      ⟨118, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 4 hp) Q2.T118_80_2 Q2.hfix118_80_2 Q2.hinj118_80_2
      Q2.hcardT118_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_80_2 i) (Q2.hfix118_80_2 i) _)
      colCert_118_80_4.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_80_5 (hp : 5 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 5 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 5 (transLenTr ⟨80, by decide⟩ 5 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 5 (transLenTr ⟨80, by decide⟩ 5 hp)) T118_80
      hfix118_80 hinj118_80 hcardT118_80
      (fun i => conj_mem_of_fixedPoints _ _ (T118_80 i) (hfix118_80 i) _)
      ⟨118, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 5 hp) Q2.T118_80_2 Q2.hfix118_80_2 Q2.hinj118_80_2
      Q2.hcardT118_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_80_2 i) (Q2.hfix118_80_2 i) _)
      colCert_118_80_5.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_80_10 (hp : 10 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 10 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 10 (transLenTr ⟨80, by decide⟩ 10 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 10 (transLenTr ⟨80, by decide⟩ 10 hp)) T118_80
      hfix118_80 hinj118_80 hcardT118_80
      (fun i => conj_mem_of_fixedPoints _ _ (T118_80 i) (hfix118_80 i) _)
      ⟨118, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 10 hp) Q2.T118_80_2 Q2.hfix118_80_2 Q2.hinj118_80_2
      Q2.hcardT118_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_80_2 i) (Q2.hfix118_80_2 i) _)
      colCert_118_80_10.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_80_15 (hp : 15 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 15 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 15 (transLenTr ⟨80, by decide⟩ 15 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 15 (transLenTr ⟨80, by decide⟩ 15 hp)) T118_80
      hfix118_80 hinj118_80 hcardT118_80
      (fun i => conj_mem_of_fixedPoints _ _ (T118_80 i) (hfix118_80 i) _)
      ⟨118, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 15 hp) Q2.T118_80_2 Q2.hfix118_80_2 Q2.hinj118_80_2
      Q2.hcardT118_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_80_2 i) (Q2.hfix118_80_2 i) _)
      colCert_118_80_15.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_80_20 (hp : 20 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 20 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 20 (transLenTr ⟨80, by decide⟩ 20 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 20 (transLenTr ⟨80, by decide⟩ 20 hp)) T118_80
      hfix118_80 hinj118_80 hcardT118_80
      (fun i => conj_mem_of_fixedPoints _ _ (T118_80 i) (hfix118_80 i) _)
      ⟨118, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 20 hp) Q2.T118_80_2 Q2.hfix118_80_2 Q2.hinj118_80_2
      Q2.hcardT118_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_80_2 i) (Q2.hfix118_80_2 i) _)
      colCert_118_80_20.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_80_25 (hp : 25 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 25 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 25 (transLenTr ⟨80, by decide⟩ 25 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 25 (transLenTr ⟨80, by decide⟩ 25 hp)) T118_80
      hfix118_80 hinj118_80 hcardT118_80
      (fun i => conj_mem_of_fixedPoints _ _ (T118_80 i) (hfix118_80 i) _)
      ⟨118, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 25 hp) Q2.T118_80_2 Q2.hfix118_80_2 Q2.hinj118_80_2
      Q2.hcardT118_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_80_2 i) (Q2.hfix118_80_2 i) _)
      colCert_118_80_25.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_80_30 (hp : 30 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 30 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 30 (transLenTr ⟨80, by decide⟩ 30 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 30 (transLenTr ⟨80, by decide⟩ 30 hp)) T118_80
      hfix118_80 hinj118_80 hcardT118_80
      (fun i => conj_mem_of_fixedPoints _ _ (T118_80 i) (hfix118_80 i) _)
      ⟨118, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 30 hp) Q2.T118_80_2 Q2.hfix118_80_2 Q2.hinj118_80_2
      Q2.hcardT118_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_80_2 i) (Q2.hfix118_80_2 i) _)
      colCert_118_80_30.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_80_35 (hp : 35 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 35 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 35 (transLenTr ⟨80, by decide⟩ 35 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 35 (transLenTr ⟨80, by decide⟩ 35 hp)) T118_80
      hfix118_80 hinj118_80 hcardT118_80
      (fun i => conj_mem_of_fixedPoints _ _ (T118_80 i) (hfix118_80 i) _)
      ⟨118, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 35 hp) Q2.T118_80_2 Q2.hfix118_80_2 Q2.hinj118_80_2
      Q2.hcardT118_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_80_2 i) (Q2.hfix118_80_2 i) _)
      colCert_118_80_35.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_80_40 (hp : 40 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 40 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 40 (transLenTr ⟨80, by decide⟩ 40 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 40 (transLenTr ⟨80, by decide⟩ 40 hp)) T118_80
      hfix118_80 hinj118_80 hcardT118_80
      (fun i => conj_mem_of_fixedPoints _ _ (T118_80 i) (hfix118_80 i) _)
      ⟨118, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 40 hp) Q2.T118_80_2 Q2.hfix118_80_2 Q2.hinj118_80_2
      Q2.hcardT118_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_80_2 i) (Q2.hfix118_80_2 i) _)
      colCert_118_80_40.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_80_45 (hp : 45 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 45 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 45 (transLenTr ⟨80, by decide⟩ 45 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 45 (transLenTr ⟨80, by decide⟩ 45 hp)) T118_80
      hfix118_80 hinj118_80 hcardT118_80
      (fun i => conj_mem_of_fixedPoints _ _ (T118_80 i) (hfix118_80 i) _)
      ⟨118, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 45 hp) Q2.T118_80_2 Q2.hfix118_80_2 Q2.hinj118_80_2
      Q2.hcardT118_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_80_2 i) (Q2.hfix118_80_2 i) _)
      colCert_118_80_45.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_80_50 (hp : 50 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 50 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 50 (transLenTr ⟨80, by decide⟩ 50 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 50 (transLenTr ⟨80, by decide⟩ 50 hp)) T118_80
      hfix118_80 hinj118_80 hcardT118_80
      (fun i => conj_mem_of_fixedPoints _ _ (T118_80 i) (hfix118_80 i) _)
      ⟨118, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 50 hp) Q2.T118_80_2 Q2.hfix118_80_2 Q2.hinj118_80_2
      Q2.hcardT118_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_80_2 i) (Q2.hfix118_80_2 i) _)
      colCert_118_80_50.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_80_55 (hp : 55 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 55 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 55 (transLenTr ⟨80, by decide⟩ 55 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 55 (transLenTr ⟨80, by decide⟩ 55 hp)) T118_80
      hfix118_80 hinj118_80 hcardT118_80
      (fun i => conj_mem_of_fixedPoints _ _ (T118_80 i) (hfix118_80 i) _)
      ⟨118, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 55 hp) Q2.T118_80_2 Q2.hfix118_80_2 Q2.hinj118_80_2
      Q2.hcardT118_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_80_2 i) (Q2.hfix118_80_2 i) _)
      colCert_118_80_55.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_80_60 (hp : 60 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 60 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 60 (transLenTr ⟨80, by decide⟩ 60 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 60 (transLenTr ⟨80, by decide⟩ 60 hp)) T118_80
      hfix118_80 hinj118_80 hcardT118_80
      (fun i => conj_mem_of_fixedPoints _ _ (T118_80 i) (hfix118_80 i) _)
      ⟨118, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 60 hp) Q2.T118_80_2 Q2.hfix118_80_2 Q2.hinj118_80_2
      Q2.hcardT118_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_80_2 i) (Q2.hfix118_80_2 i) _)
      colCert_118_80_60.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_80_65 (hp : 65 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 65 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 65 (transLenTr ⟨80, by decide⟩ 65 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 65 (transLenTr ⟨80, by decide⟩ 65 hp)) T118_80
      hfix118_80 hinj118_80 hcardT118_80
      (fun i => conj_mem_of_fixedPoints _ _ (T118_80 i) (hfix118_80 i) _)
      ⟨118, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 65 hp) Q2.T118_80_2 Q2.hfix118_80_2 Q2.hinj118_80_2
      Q2.hcardT118_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_80_2 i) (Q2.hfix118_80_2 i) _)
      colCert_118_80_65.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_80_70 (hp : 70 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 70 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 70 (transLenTr ⟨80, by decide⟩ 70 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 70 (transLenTr ⟨80, by decide⟩ 70 hp)) T118_80
      hfix118_80 hinj118_80 hcardT118_80
      (fun i => conj_mem_of_fixedPoints _ _ (T118_80 i) (hfix118_80 i) _)
      ⟨118, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 70 hp) Q2.T118_80_2 Q2.hfix118_80_2 Q2.hinj118_80_2
      Q2.hcardT118_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_80_2 i) (Q2.hfix118_80_2 i) _)
      colCert_118_80_70.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_80_75 (hp : 75 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 75 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 75 (transLenTr ⟨80, by decide⟩ 75 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 75 (transLenTr ⟨80, by decide⟩ 75 hp)) T118_80
      hfix118_80 hinj118_80 hcardT118_80
      (fun i => conj_mem_of_fixedPoints _ _ (T118_80 i) (hfix118_80 i) _)
      ⟨118, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 75 hp) Q2.T118_80_2 Q2.hfix118_80_2 Q2.hinj118_80_2
      Q2.hcardT118_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_80_2 i) (Q2.hfix118_80_2 i) _)
      colCert_118_80_75.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_80_80 (hp : 80 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 80 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 80 (transLenTr ⟨80, by decide⟩ 80 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 80 (transLenTr ⟨80, by decide⟩ 80 hp)) T118_80
      hfix118_80 hinj118_80 hcardT118_80
      (fun i => conj_mem_of_fixedPoints _ _ (T118_80 i) (hfix118_80 i) _)
      ⟨118, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 80 hp) Q2.T118_80_2 Q2.hfix118_80_2 Q2.hinj118_80_2
      Q2.hcardT118_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_80_2 i) (Q2.hfix118_80_2 i) _)
      colCert_118_80_80.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_80_85 (hp : 85 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 85 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 85 (transLenTr ⟨80, by decide⟩ 85 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 85 (transLenTr ⟨80, by decide⟩ 85 hp)) T118_80
      hfix118_80 hinj118_80 hcardT118_80
      (fun i => conj_mem_of_fixedPoints _ _ (T118_80 i) (hfix118_80 i) _)
      ⟨118, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 85 hp) Q2.T118_80_2 Q2.hfix118_80_2 Q2.hinj118_80_2
      Q2.hcardT118_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_80_2 i) (Q2.hfix118_80_2 i) _)
      colCert_118_80_85.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_80_90 (hp : 90 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 90 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 90 (transLenTr ⟨80, by decide⟩ 90 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 90 (transLenTr ⟨80, by decide⟩ 90 hp)) T118_80
      hfix118_80 hinj118_80 hcardT118_80
      (fun i => conj_mem_of_fixedPoints _ _ (T118_80 i) (hfix118_80 i) _)
      ⟨118, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 90 hp) Q2.T118_80_2 Q2.hfix118_80_2 Q2.hinj118_80_2
      Q2.hcardT118_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_80_2 i) (Q2.hfix118_80_2 i) _)
      colCert_118_80_90.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_80_95 (hp : 95 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 95 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 95 (transLenTr ⟨80, by decide⟩ 95 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 95 (transLenTr ⟨80, by decide⟩ 95 hp)) T118_80
      hfix118_80 hinj118_80 hcardT118_80
      (fun i => conj_mem_of_fixedPoints _ _ (T118_80 i) (hfix118_80 i) _)
      ⟨118, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 95 hp) Q2.T118_80_2 Q2.hfix118_80_2 Q2.hinj118_80_2
      Q2.hcardT118_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_80_2 i) (Q2.hfix118_80_2 i) _)
      colCert_118_80_95.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_80_100 (hp : 100 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 100 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 100 (transLenTr ⟨80, by decide⟩ 100 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 100 (transLenTr ⟨80, by decide⟩ 100 hp)) T118_80
      hfix118_80 hinj118_80 hcardT118_80
      (fun i => conj_mem_of_fixedPoints _ _ (T118_80 i) (hfix118_80 i) _)
      ⟨118, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 100 hp) Q2.T118_80_2 Q2.hfix118_80_2 Q2.hinj118_80_2
      Q2.hcardT118_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_80_2 i) (Q2.hfix118_80_2 i) _)
      colCert_118_80_100.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_80_105 (hp : 105 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 105 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 105 (transLenTr ⟨80, by decide⟩ 105 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 105 (transLenTr ⟨80, by decide⟩ 105 hp)) T118_80
      hfix118_80 hinj118_80 hcardT118_80
      (fun i => conj_mem_of_fixedPoints _ _ (T118_80 i) (hfix118_80 i) _)
      ⟨118, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 105 hp) Q2.T118_80_2 Q2.hfix118_80_2 Q2.hinj118_80_2
      Q2.hcardT118_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_80_2 i) (Q2.hfix118_80_2 i) _)
      colCert_118_80_105.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_80_110 (hp : 110 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 110 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 110 (transLenTr ⟨80, by decide⟩ 110 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 110 (transLenTr ⟨80, by decide⟩ 110 hp)) T118_80
      hfix118_80 hinj118_80 hcardT118_80
      (fun i => conj_mem_of_fixedPoints _ _ (T118_80 i) (hfix118_80 i) _)
      ⟨118, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 110 hp) Q2.T118_80_2 Q2.hfix118_80_2 Q2.hinj118_80_2
      Q2.hcardT118_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_80_2 i) (Q2.hfix118_80_2 i) _)
      colCert_118_80_110.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_80_115 (hp : 115 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 115 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 115 (transLenTr ⟨80, by decide⟩ 115 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 115 (transLenTr ⟨80, by decide⟩ 115 hp)) T118_80
      hfix118_80 hinj118_80 hcardT118_80
      (fun i => conj_mem_of_fixedPoints _ _ (T118_80 i) (hfix118_80 i) _)
      ⟨118, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 115 hp) Q2.T118_80_2 Q2.hfix118_80_2 Q2.hinj118_80_2
      Q2.hcardT118_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_80_2 i) (Q2.hfix118_80_2 i) _)
      colCert_118_80_115.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_80_120 (hp : 120 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 120 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 120 (transLenTr ⟨80, by decide⟩ 120 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 120 (transLenTr ⟨80, by decide⟩ 120 hp)) T118_80
      hfix118_80 hinj118_80 hcardT118_80
      (fun i => conj_mem_of_fixedPoints _ _ (T118_80 i) (hfix118_80 i) _)
      ⟨118, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 120 hp) Q2.T118_80_2 Q2.hfix118_80_2 Q2.hinj118_80_2
      Q2.hcardT118_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_80_2 i) (Q2.hfix118_80_2 i) _)
      colCert_118_80_120.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_92_0 (hp : 0 < (Q2.transData.getD 92 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨92, by decide⟩ : Fin 148)) (colE2 ⟨92, by decide⟩ 0 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨92, by decide⟩ : Fin 148))
        (colE1 ⟨92, by decide⟩ 0 (transLenTr ⟨92, by decide⟩ 0 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨92, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨92, by decide⟩ 0 (transLenTr ⟨92, by decide⟩ 0 hp)) T118_92
      hfix118_92 hinj118_92 hcardT118_92
      (fun i => conj_mem_of_fixedPoints _ _ (T118_92 i) (hfix118_92 i) _)
      ⟨118, by decide⟩ ⟨92, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨92, by decide⟩ 0 hp) Q2.T118_92_2 Q2.hfix118_92_2 Q2.hinj118_92_2
      Q2.hcardT118_92_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_92_2 i) (Q2.hfix118_92_2 i) _)
      colCert_118_92_0.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_92_1 (hp : 1 < (Q2.transData.getD 92 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨92, by decide⟩ : Fin 148)) (colE2 ⟨92, by decide⟩ 1 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨92, by decide⟩ : Fin 148))
        (colE1 ⟨92, by decide⟩ 1 (transLenTr ⟨92, by decide⟩ 1 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨92, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨92, by decide⟩ 1 (transLenTr ⟨92, by decide⟩ 1 hp)) T118_92
      hfix118_92 hinj118_92 hcardT118_92
      (fun i => conj_mem_of_fixedPoints _ _ (T118_92 i) (hfix118_92 i) _)
      ⟨118, by decide⟩ ⟨92, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨92, by decide⟩ 1 hp) Q2.T118_92_2 Q2.hfix118_92_2 Q2.hinj118_92_2
      Q2.hcardT118_92_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_92_2 i) (Q2.hfix118_92_2 i) _)
      colCert_118_92_1.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_92_2 (hp : 2 < (Q2.transData.getD 92 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨92, by decide⟩ : Fin 148)) (colE2 ⟨92, by decide⟩ 2 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨92, by decide⟩ : Fin 148))
        (colE1 ⟨92, by decide⟩ 2 (transLenTr ⟨92, by decide⟩ 2 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨92, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨92, by decide⟩ 2 (transLenTr ⟨92, by decide⟩ 2 hp)) T118_92
      hfix118_92 hinj118_92 hcardT118_92
      (fun i => conj_mem_of_fixedPoints _ _ (T118_92 i) (hfix118_92 i) _)
      ⟨118, by decide⟩ ⟨92, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨92, by decide⟩ 2 hp) Q2.T118_92_2 Q2.hfix118_92_2 Q2.hinj118_92_2
      Q2.hcardT118_92_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_92_2 i) (Q2.hfix118_92_2 i) _)
      colCert_118_92_2.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_92_3 (hp : 3 < (Q2.transData.getD 92 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨92, by decide⟩ : Fin 148)) (colE2 ⟨92, by decide⟩ 3 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨92, by decide⟩ : Fin 148))
        (colE1 ⟨92, by decide⟩ 3 (transLenTr ⟨92, by decide⟩ 3 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨92, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨92, by decide⟩ 3 (transLenTr ⟨92, by decide⟩ 3 hp)) T118_92
      hfix118_92 hinj118_92 hcardT118_92
      (fun i => conj_mem_of_fixedPoints _ _ (T118_92 i) (hfix118_92 i) _)
      ⟨118, by decide⟩ ⟨92, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨92, by decide⟩ 3 hp) Q2.T118_92_2 Q2.hfix118_92_2 Q2.hinj118_92_2
      Q2.hcardT118_92_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_92_2 i) (Q2.hfix118_92_2 i) _)
      colCert_118_92_3.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_92_4 (hp : 4 < (Q2.transData.getD 92 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨92, by decide⟩ : Fin 148)) (colE2 ⟨92, by decide⟩ 4 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨92, by decide⟩ : Fin 148))
        (colE1 ⟨92, by decide⟩ 4 (transLenTr ⟨92, by decide⟩ 4 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨92, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨92, by decide⟩ 4 (transLenTr ⟨92, by decide⟩ 4 hp)) T118_92
      hfix118_92 hinj118_92 hcardT118_92
      (fun i => conj_mem_of_fixedPoints _ _ (T118_92 i) (hfix118_92 i) _)
      ⟨118, by decide⟩ ⟨92, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨92, by decide⟩ 4 hp) Q2.T118_92_2 Q2.hfix118_92_2 Q2.hinj118_92_2
      Q2.hcardT118_92_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_92_2 i) (Q2.hfix118_92_2 i) _)
      colCert_118_92_4.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_92_5 (hp : 5 < (Q2.transData.getD 92 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨92, by decide⟩ : Fin 148)) (colE2 ⟨92, by decide⟩ 5 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨92, by decide⟩ : Fin 148))
        (colE1 ⟨92, by decide⟩ 5 (transLenTr ⟨92, by decide⟩ 5 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨92, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨92, by decide⟩ 5 (transLenTr ⟨92, by decide⟩ 5 hp)) T118_92
      hfix118_92 hinj118_92 hcardT118_92
      (fun i => conj_mem_of_fixedPoints _ _ (T118_92 i) (hfix118_92 i) _)
      ⟨118, by decide⟩ ⟨92, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨92, by decide⟩ 5 hp) Q2.T118_92_2 Q2.hfix118_92_2 Q2.hinj118_92_2
      Q2.hcardT118_92_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_92_2 i) (Q2.hfix118_92_2 i) _)
      colCert_118_92_5.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_92_10 (hp : 10 < (Q2.transData.getD 92 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨92, by decide⟩ : Fin 148)) (colE2 ⟨92, by decide⟩ 10 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨92, by decide⟩ : Fin 148))
        (colE1 ⟨92, by decide⟩ 10 (transLenTr ⟨92, by decide⟩ 10 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨92, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨92, by decide⟩ 10 (transLenTr ⟨92, by decide⟩ 10 hp)) T118_92
      hfix118_92 hinj118_92 hcardT118_92
      (fun i => conj_mem_of_fixedPoints _ _ (T118_92 i) (hfix118_92 i) _)
      ⟨118, by decide⟩ ⟨92, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨92, by decide⟩ 10 hp) Q2.T118_92_2 Q2.hfix118_92_2 Q2.hinj118_92_2
      Q2.hcardT118_92_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_92_2 i) (Q2.hfix118_92_2 i) _)
      colCert_118_92_10.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_92_15 (hp : 15 < (Q2.transData.getD 92 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨92, by decide⟩ : Fin 148)) (colE2 ⟨92, by decide⟩ 15 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨92, by decide⟩ : Fin 148))
        (colE1 ⟨92, by decide⟩ 15 (transLenTr ⟨92, by decide⟩ 15 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨92, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨92, by decide⟩ 15 (transLenTr ⟨92, by decide⟩ 15 hp)) T118_92
      hfix118_92 hinj118_92 hcardT118_92
      (fun i => conj_mem_of_fixedPoints _ _ (T118_92 i) (hfix118_92 i) _)
      ⟨118, by decide⟩ ⟨92, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨92, by decide⟩ 15 hp) Q2.T118_92_2 Q2.hfix118_92_2 Q2.hinj118_92_2
      Q2.hcardT118_92_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_92_2 i) (Q2.hfix118_92_2 i) _)
      colCert_118_92_15.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_92_20 (hp : 20 < (Q2.transData.getD 92 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨92, by decide⟩ : Fin 148)) (colE2 ⟨92, by decide⟩ 20 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨92, by decide⟩ : Fin 148))
        (colE1 ⟨92, by decide⟩ 20 (transLenTr ⟨92, by decide⟩ 20 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨92, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨92, by decide⟩ 20 (transLenTr ⟨92, by decide⟩ 20 hp)) T118_92
      hfix118_92 hinj118_92 hcardT118_92
      (fun i => conj_mem_of_fixedPoints _ _ (T118_92 i) (hfix118_92 i) _)
      ⟨118, by decide⟩ ⟨92, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨92, by decide⟩ 20 hp) Q2.T118_92_2 Q2.hfix118_92_2 Q2.hinj118_92_2
      Q2.hcardT118_92_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_92_2 i) (Q2.hfix118_92_2 i) _)
      colCert_118_92_20.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_97_0 (hp : 0 < (Q2.transData.getD 97 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨97, by decide⟩ : Fin 148)) (colE2 ⟨97, by decide⟩ 0 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨97, by decide⟩ : Fin 148))
        (colE1 ⟨97, by decide⟩ 0 (transLenTr ⟨97, by decide⟩ 0 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨97, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨97, by decide⟩ 0 (transLenTr ⟨97, by decide⟩ 0 hp)) T118_97
      hfix118_97 hinj118_97 hcardT118_97
      (fun i => conj_mem_of_fixedPoints _ _ (T118_97 i) (hfix118_97 i) _)
      ⟨118, by decide⟩ ⟨97, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨97, by decide⟩ 0 hp) Q2.T118_97_2 Q2.hfix118_97_2 Q2.hinj118_97_2
      Q2.hcardT118_97_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_97_2 i) (Q2.hfix118_97_2 i) _)
      colCert_118_97_0.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_97_1 (hp : 1 < (Q2.transData.getD 97 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨97, by decide⟩ : Fin 148)) (colE2 ⟨97, by decide⟩ 1 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨97, by decide⟩ : Fin 148))
        (colE1 ⟨97, by decide⟩ 1 (transLenTr ⟨97, by decide⟩ 1 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨97, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨97, by decide⟩ 1 (transLenTr ⟨97, by decide⟩ 1 hp)) T118_97
      hfix118_97 hinj118_97 hcardT118_97
      (fun i => conj_mem_of_fixedPoints _ _ (T118_97 i) (hfix118_97 i) _)
      ⟨118, by decide⟩ ⟨97, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨97, by decide⟩ 1 hp) Q2.T118_97_2 Q2.hfix118_97_2 Q2.hinj118_97_2
      Q2.hcardT118_97_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_97_2 i) (Q2.hfix118_97_2 i) _)
      colCert_118_97_1.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_97_2 (hp : 2 < (Q2.transData.getD 97 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨97, by decide⟩ : Fin 148)) (colE2 ⟨97, by decide⟩ 2 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨97, by decide⟩ : Fin 148))
        (colE1 ⟨97, by decide⟩ 2 (transLenTr ⟨97, by decide⟩ 2 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨97, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨97, by decide⟩ 2 (transLenTr ⟨97, by decide⟩ 2 hp)) T118_97
      hfix118_97 hinj118_97 hcardT118_97
      (fun i => conj_mem_of_fixedPoints _ _ (T118_97 i) (hfix118_97 i) _)
      ⟨118, by decide⟩ ⟨97, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨97, by decide⟩ 2 hp) Q2.T118_97_2 Q2.hfix118_97_2 Q2.hinj118_97_2
      Q2.hcardT118_97_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_97_2 i) (Q2.hfix118_97_2 i) _)
      colCert_118_97_2.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_97_3 (hp : 3 < (Q2.transData.getD 97 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨97, by decide⟩ : Fin 148)) (colE2 ⟨97, by decide⟩ 3 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨97, by decide⟩ : Fin 148))
        (colE1 ⟨97, by decide⟩ 3 (transLenTr ⟨97, by decide⟩ 3 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨97, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨97, by decide⟩ 3 (transLenTr ⟨97, by decide⟩ 3 hp)) T118_97
      hfix118_97 hinj118_97 hcardT118_97
      (fun i => conj_mem_of_fixedPoints _ _ (T118_97 i) (hfix118_97 i) _)
      ⟨118, by decide⟩ ⟨97, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨97, by decide⟩ 3 hp) Q2.T118_97_2 Q2.hfix118_97_2 Q2.hinj118_97_2
      Q2.hcardT118_97_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_97_2 i) (Q2.hfix118_97_2 i) _)
      colCert_118_97_3.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_97_4 (hp : 4 < (Q2.transData.getD 97 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨97, by decide⟩ : Fin 148)) (colE2 ⟨97, by decide⟩ 4 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨97, by decide⟩ : Fin 148))
        (colE1 ⟨97, by decide⟩ 4 (transLenTr ⟨97, by decide⟩ 4 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨97, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨97, by decide⟩ 4 (transLenTr ⟨97, by decide⟩ 4 hp)) T118_97
      hfix118_97 hinj118_97 hcardT118_97
      (fun i => conj_mem_of_fixedPoints _ _ (T118_97 i) (hfix118_97 i) _)
      ⟨118, by decide⟩ ⟨97, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨97, by decide⟩ 4 hp) Q2.T118_97_2 Q2.hfix118_97_2 Q2.hinj118_97_2
      Q2.hcardT118_97_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_97_2 i) (Q2.hfix118_97_2 i) _)
      colCert_118_97_4.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_97_5 (hp : 5 < (Q2.transData.getD 97 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨97, by decide⟩ : Fin 148)) (colE2 ⟨97, by decide⟩ 5 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨97, by decide⟩ : Fin 148))
        (colE1 ⟨97, by decide⟩ 5 (transLenTr ⟨97, by decide⟩ 5 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨97, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨97, by decide⟩ 5 (transLenTr ⟨97, by decide⟩ 5 hp)) T118_97
      hfix118_97 hinj118_97 hcardT118_97
      (fun i => conj_mem_of_fixedPoints _ _ (T118_97 i) (hfix118_97 i) _)
      ⟨118, by decide⟩ ⟨97, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨97, by decide⟩ 5 hp) Q2.T118_97_2 Q2.hfix118_97_2 Q2.hinj118_97_2
      Q2.hcardT118_97_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_97_2 i) (Q2.hfix118_97_2 i) _)
      colCert_118_97_5.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_97_10 (hp : 10 < (Q2.transData.getD 97 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨97, by decide⟩ : Fin 148)) (colE2 ⟨97, by decide⟩ 10 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨97, by decide⟩ : Fin 148))
        (colE1 ⟨97, by decide⟩ 10 (transLenTr ⟨97, by decide⟩ 10 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨97, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨97, by decide⟩ 10 (transLenTr ⟨97, by decide⟩ 10 hp)) T118_97
      hfix118_97 hinj118_97 hcardT118_97
      (fun i => conj_mem_of_fixedPoints _ _ (T118_97 i) (hfix118_97 i) _)
      ⟨118, by decide⟩ ⟨97, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨97, by decide⟩ 10 hp) Q2.T118_97_2 Q2.hfix118_97_2 Q2.hinj118_97_2
      Q2.hcardT118_97_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_97_2 i) (Q2.hfix118_97_2 i) _)
      colCert_118_97_10.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_97_15 (hp : 15 < (Q2.transData.getD 97 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨97, by decide⟩ : Fin 148)) (colE2 ⟨97, by decide⟩ 15 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨97, by decide⟩ : Fin 148))
        (colE1 ⟨97, by decide⟩ 15 (transLenTr ⟨97, by decide⟩ 15 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨97, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨97, by decide⟩ 15 (transLenTr ⟨97, by decide⟩ 15 hp)) T118_97
      hfix118_97 hinj118_97 hcardT118_97
      (fun i => conj_mem_of_fixedPoints _ _ (T118_97 i) (hfix118_97 i) _)
      ⟨118, by decide⟩ ⟨97, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨97, by decide⟩ 15 hp) Q2.T118_97_2 Q2.hfix118_97_2 Q2.hinj118_97_2
      Q2.hcardT118_97_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_97_2 i) (Q2.hfix118_97_2 i) _)
      colCert_118_97_15.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_97_20 (hp : 20 < (Q2.transData.getD 97 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨97, by decide⟩ : Fin 148)) (colE2 ⟨97, by decide⟩ 20 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨97, by decide⟩ : Fin 148))
        (colE1 ⟨97, by decide⟩ 20 (transLenTr ⟨97, by decide⟩ 20 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨97, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨97, by decide⟩ 20 (transLenTr ⟨97, by decide⟩ 20 hp)) T118_97
      hfix118_97 hinj118_97 hcardT118_97
      (fun i => conj_mem_of_fixedPoints _ _ (T118_97 i) (hfix118_97 i) _)
      ⟨118, by decide⟩ ⟨97, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨97, by decide⟩ 20 hp) Q2.T118_97_2 Q2.hfix118_97_2 Q2.hinj118_97_2
      Q2.hcardT118_97_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_97_2 i) (Q2.hfix118_97_2 i) _)
      colCert_118_97_20.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_102_0 (hp : 0 < (Q2.transData.getD 102 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨102, by decide⟩ : Fin 148)) (colE2 ⟨102, by decide⟩ 0 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨102, by decide⟩ : Fin 148))
        (colE1 ⟨102, by decide⟩ 0 (transLenTr ⟨102, by decide⟩ 0 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨102, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨102, by decide⟩ 0 (transLenTr ⟨102, by decide⟩ 0 hp)) T118_102
      hfix118_102 hinj118_102 hcardT118_102
      (fun i => conj_mem_of_fixedPoints _ _ (T118_102 i) (hfix118_102 i) _)
      ⟨118, by decide⟩ ⟨102, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨102, by decide⟩ 0 hp) Q2.T118_102_2 Q2.hfix118_102_2 Q2.hinj118_102_2
      Q2.hcardT118_102_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_102_2 i) (Q2.hfix118_102_2 i) _)
      colCert_118_102_0.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_102_1 (hp : 1 < (Q2.transData.getD 102 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨102, by decide⟩ : Fin 148)) (colE2 ⟨102, by decide⟩ 1 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨102, by decide⟩ : Fin 148))
        (colE1 ⟨102, by decide⟩ 1 (transLenTr ⟨102, by decide⟩ 1 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨102, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨102, by decide⟩ 1 (transLenTr ⟨102, by decide⟩ 1 hp)) T118_102
      hfix118_102 hinj118_102 hcardT118_102
      (fun i => conj_mem_of_fixedPoints _ _ (T118_102 i) (hfix118_102 i) _)
      ⟨118, by decide⟩ ⟨102, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨102, by decide⟩ 1 hp) Q2.T118_102_2 Q2.hfix118_102_2 Q2.hinj118_102_2
      Q2.hcardT118_102_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_102_2 i) (Q2.hfix118_102_2 i) _)
      colCert_118_102_1.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_102_2 (hp : 2 < (Q2.transData.getD 102 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨102, by decide⟩ : Fin 148)) (colE2 ⟨102, by decide⟩ 2 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨102, by decide⟩ : Fin 148))
        (colE1 ⟨102, by decide⟩ 2 (transLenTr ⟨102, by decide⟩ 2 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨102, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨102, by decide⟩ 2 (transLenTr ⟨102, by decide⟩ 2 hp)) T118_102
      hfix118_102 hinj118_102 hcardT118_102
      (fun i => conj_mem_of_fixedPoints _ _ (T118_102 i) (hfix118_102 i) _)
      ⟨118, by decide⟩ ⟨102, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨102, by decide⟩ 2 hp) Q2.T118_102_2 Q2.hfix118_102_2 Q2.hinj118_102_2
      Q2.hcardT118_102_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_102_2 i) (Q2.hfix118_102_2 i) _)
      colCert_118_102_2.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_102_3 (hp : 3 < (Q2.transData.getD 102 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨102, by decide⟩ : Fin 148)) (colE2 ⟨102, by decide⟩ 3 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨102, by decide⟩ : Fin 148))
        (colE1 ⟨102, by decide⟩ 3 (transLenTr ⟨102, by decide⟩ 3 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨102, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨102, by decide⟩ 3 (transLenTr ⟨102, by decide⟩ 3 hp)) T118_102
      hfix118_102 hinj118_102 hcardT118_102
      (fun i => conj_mem_of_fixedPoints _ _ (T118_102 i) (hfix118_102 i) _)
      ⟨118, by decide⟩ ⟨102, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨102, by decide⟩ 3 hp) Q2.T118_102_2 Q2.hfix118_102_2 Q2.hinj118_102_2
      Q2.hcardT118_102_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_102_2 i) (Q2.hfix118_102_2 i) _)
      colCert_118_102_3.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_102_4 (hp : 4 < (Q2.transData.getD 102 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨102, by decide⟩ : Fin 148)) (colE2 ⟨102, by decide⟩ 4 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨102, by decide⟩ : Fin 148))
        (colE1 ⟨102, by decide⟩ 4 (transLenTr ⟨102, by decide⟩ 4 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨102, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨102, by decide⟩ 4 (transLenTr ⟨102, by decide⟩ 4 hp)) T118_102
      hfix118_102 hinj118_102 hcardT118_102
      (fun i => conj_mem_of_fixedPoints _ _ (T118_102 i) (hfix118_102 i) _)
      ⟨118, by decide⟩ ⟨102, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨102, by decide⟩ 4 hp) Q2.T118_102_2 Q2.hfix118_102_2 Q2.hinj118_102_2
      Q2.hcardT118_102_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_102_2 i) (Q2.hfix118_102_2 i) _)
      colCert_118_102_4.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_102_5 (hp : 5 < (Q2.transData.getD 102 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨102, by decide⟩ : Fin 148)) (colE2 ⟨102, by decide⟩ 5 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨102, by decide⟩ : Fin 148))
        (colE1 ⟨102, by decide⟩ 5 (transLenTr ⟨102, by decide⟩ 5 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨102, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨102, by decide⟩ 5 (transLenTr ⟨102, by decide⟩ 5 hp)) T118_102
      hfix118_102 hinj118_102 hcardT118_102
      (fun i => conj_mem_of_fixedPoints _ _ (T118_102 i) (hfix118_102 i) _)
      ⟨118, by decide⟩ ⟨102, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨102, by decide⟩ 5 hp) Q2.T118_102_2 Q2.hfix118_102_2 Q2.hinj118_102_2
      Q2.hcardT118_102_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_102_2 i) (Q2.hfix118_102_2 i) _)
      colCert_118_102_5.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_102_10 (hp : 10 < (Q2.transData.getD 102 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨102, by decide⟩ : Fin 148)) (colE2 ⟨102, by decide⟩ 10 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨102, by decide⟩ : Fin 148))
        (colE1 ⟨102, by decide⟩ 10 (transLenTr ⟨102, by decide⟩ 10 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨102, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨102, by decide⟩ 10 (transLenTr ⟨102, by decide⟩ 10 hp)) T118_102
      hfix118_102 hinj118_102 hcardT118_102
      (fun i => conj_mem_of_fixedPoints _ _ (T118_102 i) (hfix118_102 i) _)
      ⟨118, by decide⟩ ⟨102, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨102, by decide⟩ 10 hp) Q2.T118_102_2 Q2.hfix118_102_2 Q2.hinj118_102_2
      Q2.hcardT118_102_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_102_2 i) (Q2.hfix118_102_2 i) _)
      colCert_118_102_10.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_102_15 (hp : 15 < (Q2.transData.getD 102 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨102, by decide⟩ : Fin 148)) (colE2 ⟨102, by decide⟩ 15 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨102, by decide⟩ : Fin 148))
        (colE1 ⟨102, by decide⟩ 15 (transLenTr ⟨102, by decide⟩ 15 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨102, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨102, by decide⟩ 15 (transLenTr ⟨102, by decide⟩ 15 hp)) T118_102
      hfix118_102 hinj118_102 hcardT118_102
      (fun i => conj_mem_of_fixedPoints _ _ (T118_102 i) (hfix118_102 i) _)
      ⟨118, by decide⟩ ⟨102, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨102, by decide⟩ 15 hp) Q2.T118_102_2 Q2.hfix118_102_2 Q2.hinj118_102_2
      Q2.hcardT118_102_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_102_2 i) (Q2.hfix118_102_2 i) _)
      colCert_118_102_15.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_102_20 (hp : 20 < (Q2.transData.getD 102 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨102, by decide⟩ : Fin 148)) (colE2 ⟨102, by decide⟩ 20 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨102, by decide⟩ : Fin 148))
        (colE1 ⟨102, by decide⟩ 20 (transLenTr ⟨102, by decide⟩ 20 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨102, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨102, by decide⟩ 20 (transLenTr ⟨102, by decide⟩ 20 hp)) T118_102
      hfix118_102 hinj118_102 hcardT118_102
      (fun i => conj_mem_of_fixedPoints _ _ (T118_102 i) (hfix118_102 i) _)
      ⟨118, by decide⟩ ⟨102, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨102, by decide⟩ 20 hp) Q2.T118_102_2 Q2.hfix118_102_2 Q2.hinj118_102_2
      Q2.hcardT118_102_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_102_2 i) (Q2.hfix118_102_2 i) _)
      colCert_118_102_20.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_107_0 (hp : 0 < (Q2.transData.getD 107 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨107, by decide⟩ : Fin 148)) (colE2 ⟨107, by decide⟩ 0 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨107, by decide⟩ : Fin 148))
        (colE1 ⟨107, by decide⟩ 0 (transLenTr ⟨107, by decide⟩ 0 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨107, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨107, by decide⟩ 0 (transLenTr ⟨107, by decide⟩ 0 hp)) T118_107
      hfix118_107 hinj118_107 hcardT118_107
      (fun i => conj_mem_of_fixedPoints _ _ (T118_107 i) (hfix118_107 i) _)
      ⟨118, by decide⟩ ⟨107, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨107, by decide⟩ 0 hp) Q2.T118_107_2 Q2.hfix118_107_2 Q2.hinj118_107_2
      Q2.hcardT118_107_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_107_2 i) (Q2.hfix118_107_2 i) _)
      colCert_118_107_0.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_107_1 (hp : 1 < (Q2.transData.getD 107 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨107, by decide⟩ : Fin 148)) (colE2 ⟨107, by decide⟩ 1 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨107, by decide⟩ : Fin 148))
        (colE1 ⟨107, by decide⟩ 1 (transLenTr ⟨107, by decide⟩ 1 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨107, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨107, by decide⟩ 1 (transLenTr ⟨107, by decide⟩ 1 hp)) T118_107
      hfix118_107 hinj118_107 hcardT118_107
      (fun i => conj_mem_of_fixedPoints _ _ (T118_107 i) (hfix118_107 i) _)
      ⟨118, by decide⟩ ⟨107, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨107, by decide⟩ 1 hp) Q2.T118_107_2 Q2.hfix118_107_2 Q2.hinj118_107_2
      Q2.hcardT118_107_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_107_2 i) (Q2.hfix118_107_2 i) _)
      colCert_118_107_1.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_107_2 (hp : 2 < (Q2.transData.getD 107 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨107, by decide⟩ : Fin 148)) (colE2 ⟨107, by decide⟩ 2 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨107, by decide⟩ : Fin 148))
        (colE1 ⟨107, by decide⟩ 2 (transLenTr ⟨107, by decide⟩ 2 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨107, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨107, by decide⟩ 2 (transLenTr ⟨107, by decide⟩ 2 hp)) T118_107
      hfix118_107 hinj118_107 hcardT118_107
      (fun i => conj_mem_of_fixedPoints _ _ (T118_107 i) (hfix118_107 i) _)
      ⟨118, by decide⟩ ⟨107, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨107, by decide⟩ 2 hp) Q2.T118_107_2 Q2.hfix118_107_2 Q2.hinj118_107_2
      Q2.hcardT118_107_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_107_2 i) (Q2.hfix118_107_2 i) _)
      colCert_118_107_2.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_107_3 (hp : 3 < (Q2.transData.getD 107 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨107, by decide⟩ : Fin 148)) (colE2 ⟨107, by decide⟩ 3 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨107, by decide⟩ : Fin 148))
        (colE1 ⟨107, by decide⟩ 3 (transLenTr ⟨107, by decide⟩ 3 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨107, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨107, by decide⟩ 3 (transLenTr ⟨107, by decide⟩ 3 hp)) T118_107
      hfix118_107 hinj118_107 hcardT118_107
      (fun i => conj_mem_of_fixedPoints _ _ (T118_107 i) (hfix118_107 i) _)
      ⟨118, by decide⟩ ⟨107, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨107, by decide⟩ 3 hp) Q2.T118_107_2 Q2.hfix118_107_2 Q2.hinj118_107_2
      Q2.hcardT118_107_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_107_2 i) (Q2.hfix118_107_2 i) _)
      colCert_118_107_3.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_107_4 (hp : 4 < (Q2.transData.getD 107 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨107, by decide⟩ : Fin 148)) (colE2 ⟨107, by decide⟩ 4 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨107, by decide⟩ : Fin 148))
        (colE1 ⟨107, by decide⟩ 4 (transLenTr ⟨107, by decide⟩ 4 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨107, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨107, by decide⟩ 4 (transLenTr ⟨107, by decide⟩ 4 hp)) T118_107
      hfix118_107 hinj118_107 hcardT118_107
      (fun i => conj_mem_of_fixedPoints _ _ (T118_107 i) (hfix118_107 i) _)
      ⟨118, by decide⟩ ⟨107, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨107, by decide⟩ 4 hp) Q2.T118_107_2 Q2.hfix118_107_2 Q2.hinj118_107_2
      Q2.hcardT118_107_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_107_2 i) (Q2.hfix118_107_2 i) _)
      colCert_118_107_4.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_107_5 (hp : 5 < (Q2.transData.getD 107 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨107, by decide⟩ : Fin 148)) (colE2 ⟨107, by decide⟩ 5 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨107, by decide⟩ : Fin 148))
        (colE1 ⟨107, by decide⟩ 5 (transLenTr ⟨107, by decide⟩ 5 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨107, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨107, by decide⟩ 5 (transLenTr ⟨107, by decide⟩ 5 hp)) T118_107
      hfix118_107 hinj118_107 hcardT118_107
      (fun i => conj_mem_of_fixedPoints _ _ (T118_107 i) (hfix118_107 i) _)
      ⟨118, by decide⟩ ⟨107, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨107, by decide⟩ 5 hp) Q2.T118_107_2 Q2.hfix118_107_2 Q2.hinj118_107_2
      Q2.hcardT118_107_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_107_2 i) (Q2.hfix118_107_2 i) _)
      colCert_118_107_5.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_107_10 (hp : 10 < (Q2.transData.getD 107 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨107, by decide⟩ : Fin 148)) (colE2 ⟨107, by decide⟩ 10 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨107, by decide⟩ : Fin 148))
        (colE1 ⟨107, by decide⟩ 10 (transLenTr ⟨107, by decide⟩ 10 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨107, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨107, by decide⟩ 10 (transLenTr ⟨107, by decide⟩ 10 hp)) T118_107
      hfix118_107 hinj118_107 hcardT118_107
      (fun i => conj_mem_of_fixedPoints _ _ (T118_107 i) (hfix118_107 i) _)
      ⟨118, by decide⟩ ⟨107, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨107, by decide⟩ 10 hp) Q2.T118_107_2 Q2.hfix118_107_2 Q2.hinj118_107_2
      Q2.hcardT118_107_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_107_2 i) (Q2.hfix118_107_2 i) _)
      colCert_118_107_10.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_107_15 (hp : 15 < (Q2.transData.getD 107 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨107, by decide⟩ : Fin 148)) (colE2 ⟨107, by decide⟩ 15 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨107, by decide⟩ : Fin 148))
        (colE1 ⟨107, by decide⟩ 15 (transLenTr ⟨107, by decide⟩ 15 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨107, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨107, by decide⟩ 15 (transLenTr ⟨107, by decide⟩ 15 hp)) T118_107
      hfix118_107 hinj118_107 hcardT118_107
      (fun i => conj_mem_of_fixedPoints _ _ (T118_107 i) (hfix118_107 i) _)
      ⟨118, by decide⟩ ⟨107, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨107, by decide⟩ 15 hp) Q2.T118_107_2 Q2.hfix118_107_2 Q2.hinj118_107_2
      Q2.hcardT118_107_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_107_2 i) (Q2.hfix118_107_2 i) _)
      colCert_118_107_15.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_107_20 (hp : 20 < (Q2.transData.getD 107 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨107, by decide⟩ : Fin 148)) (colE2 ⟨107, by decide⟩ 20 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨107, by decide⟩ : Fin 148))
        (colE1 ⟨107, by decide⟩ 20 (transLenTr ⟨107, by decide⟩ 20 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨107, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨107, by decide⟩ 20 (transLenTr ⟨107, by decide⟩ 20 hp)) T118_107
      hfix118_107 hinj118_107 hcardT118_107
      (fun i => conj_mem_of_fixedPoints _ _ (T118_107 i) (hfix118_107 i) _)
      ⟨118, by decide⟩ ⟨107, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨107, by decide⟩ 20 hp) Q2.T118_107_2 Q2.hfix118_107_2 Q2.hinj118_107_2
      Q2.hcardT118_107_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_107_2 i) (Q2.hfix118_107_2 i) _)
      colCert_118_107_20.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_112_0 (hp : 0 < (Q2.transData.getD 112 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨112, by decide⟩ : Fin 148)) (colE2 ⟨112, by decide⟩ 0 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨112, by decide⟩ : Fin 148))
        (colE1 ⟨112, by decide⟩ 0 (transLenTr ⟨112, by decide⟩ 0 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨112, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨112, by decide⟩ 0 (transLenTr ⟨112, by decide⟩ 0 hp)) T118_112
      hfix118_112 hinj118_112 hcardT118_112
      (fun i => conj_mem_of_fixedPoints _ _ (T118_112 i) (hfix118_112 i) _)
      ⟨118, by decide⟩ ⟨112, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨112, by decide⟩ 0 hp) Q2.T118_112_2 Q2.hfix118_112_2 Q2.hinj118_112_2
      Q2.hcardT118_112_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_112_2 i) (Q2.hfix118_112_2 i) _)
      colCert_118_112_0.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_112_1 (hp : 1 < (Q2.transData.getD 112 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨112, by decide⟩ : Fin 148)) (colE2 ⟨112, by decide⟩ 1 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨112, by decide⟩ : Fin 148))
        (colE1 ⟨112, by decide⟩ 1 (transLenTr ⟨112, by decide⟩ 1 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨112, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨112, by decide⟩ 1 (transLenTr ⟨112, by decide⟩ 1 hp)) T118_112
      hfix118_112 hinj118_112 hcardT118_112
      (fun i => conj_mem_of_fixedPoints _ _ (T118_112 i) (hfix118_112 i) _)
      ⟨118, by decide⟩ ⟨112, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨112, by decide⟩ 1 hp) Q2.T118_112_2 Q2.hfix118_112_2 Q2.hinj118_112_2
      Q2.hcardT118_112_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_112_2 i) (Q2.hfix118_112_2 i) _)
      colCert_118_112_1.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_112_2 (hp : 2 < (Q2.transData.getD 112 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨112, by decide⟩ : Fin 148)) (colE2 ⟨112, by decide⟩ 2 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨112, by decide⟩ : Fin 148))
        (colE1 ⟨112, by decide⟩ 2 (transLenTr ⟨112, by decide⟩ 2 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨112, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨112, by decide⟩ 2 (transLenTr ⟨112, by decide⟩ 2 hp)) T118_112
      hfix118_112 hinj118_112 hcardT118_112
      (fun i => conj_mem_of_fixedPoints _ _ (T118_112 i) (hfix118_112 i) _)
      ⟨118, by decide⟩ ⟨112, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨112, by decide⟩ 2 hp) Q2.T118_112_2 Q2.hfix118_112_2 Q2.hinj118_112_2
      Q2.hcardT118_112_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_112_2 i) (Q2.hfix118_112_2 i) _)
      colCert_118_112_2.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_112_3 (hp : 3 < (Q2.transData.getD 112 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨112, by decide⟩ : Fin 148)) (colE2 ⟨112, by decide⟩ 3 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨112, by decide⟩ : Fin 148))
        (colE1 ⟨112, by decide⟩ 3 (transLenTr ⟨112, by decide⟩ 3 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨112, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨112, by decide⟩ 3 (transLenTr ⟨112, by decide⟩ 3 hp)) T118_112
      hfix118_112 hinj118_112 hcardT118_112
      (fun i => conj_mem_of_fixedPoints _ _ (T118_112 i) (hfix118_112 i) _)
      ⟨118, by decide⟩ ⟨112, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨112, by decide⟩ 3 hp) Q2.T118_112_2 Q2.hfix118_112_2 Q2.hinj118_112_2
      Q2.hcardT118_112_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_112_2 i) (Q2.hfix118_112_2 i) _)
      colCert_118_112_3.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_112_4 (hp : 4 < (Q2.transData.getD 112 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨112, by decide⟩ : Fin 148)) (colE2 ⟨112, by decide⟩ 4 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨112, by decide⟩ : Fin 148))
        (colE1 ⟨112, by decide⟩ 4 (transLenTr ⟨112, by decide⟩ 4 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨112, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨112, by decide⟩ 4 (transLenTr ⟨112, by decide⟩ 4 hp)) T118_112
      hfix118_112 hinj118_112 hcardT118_112
      (fun i => conj_mem_of_fixedPoints _ _ (T118_112 i) (hfix118_112 i) _)
      ⟨118, by decide⟩ ⟨112, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨112, by decide⟩ 4 hp) Q2.T118_112_2 Q2.hfix118_112_2 Q2.hinj118_112_2
      Q2.hcardT118_112_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_112_2 i) (Q2.hfix118_112_2 i) _)
      colCert_118_112_4.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_112_5 (hp : 5 < (Q2.transData.getD 112 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨112, by decide⟩ : Fin 148)) (colE2 ⟨112, by decide⟩ 5 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨112, by decide⟩ : Fin 148))
        (colE1 ⟨112, by decide⟩ 5 (transLenTr ⟨112, by decide⟩ 5 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨112, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨112, by decide⟩ 5 (transLenTr ⟨112, by decide⟩ 5 hp)) T118_112
      hfix118_112 hinj118_112 hcardT118_112
      (fun i => conj_mem_of_fixedPoints _ _ (T118_112 i) (hfix118_112 i) _)
      ⟨118, by decide⟩ ⟨112, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨112, by decide⟩ 5 hp) Q2.T118_112_2 Q2.hfix118_112_2 Q2.hinj118_112_2
      Q2.hcardT118_112_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_112_2 i) (Q2.hfix118_112_2 i) _)
      colCert_118_112_5.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_112_10 (hp : 10 < (Q2.transData.getD 112 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨112, by decide⟩ : Fin 148)) (colE2 ⟨112, by decide⟩ 10 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨112, by decide⟩ : Fin 148))
        (colE1 ⟨112, by decide⟩ 10 (transLenTr ⟨112, by decide⟩ 10 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨112, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨112, by decide⟩ 10 (transLenTr ⟨112, by decide⟩ 10 hp)) T118_112
      hfix118_112 hinj118_112 hcardT118_112
      (fun i => conj_mem_of_fixedPoints _ _ (T118_112 i) (hfix118_112 i) _)
      ⟨118, by decide⟩ ⟨112, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨112, by decide⟩ 10 hp) Q2.T118_112_2 Q2.hfix118_112_2 Q2.hinj118_112_2
      Q2.hcardT118_112_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_112_2 i) (Q2.hfix118_112_2 i) _)
      colCert_118_112_10.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_112_15 (hp : 15 < (Q2.transData.getD 112 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨112, by decide⟩ : Fin 148)) (colE2 ⟨112, by decide⟩ 15 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨112, by decide⟩ : Fin 148))
        (colE1 ⟨112, by decide⟩ 15 (transLenTr ⟨112, by decide⟩ 15 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨112, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨112, by decide⟩ 15 (transLenTr ⟨112, by decide⟩ 15 hp)) T118_112
      hfix118_112 hinj118_112 hcardT118_112
      (fun i => conj_mem_of_fixedPoints _ _ (T118_112 i) (hfix118_112 i) _)
      ⟨118, by decide⟩ ⟨112, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨112, by decide⟩ 15 hp) Q2.T118_112_2 Q2.hfix118_112_2 Q2.hinj118_112_2
      Q2.hcardT118_112_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_112_2 i) (Q2.hfix118_112_2 i) _)
      colCert_118_112_15.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_112_20 (hp : 20 < (Q2.transData.getD 112 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨112, by decide⟩ : Fin 148)) (colE2 ⟨112, by decide⟩ 20 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨112, by decide⟩ : Fin 148))
        (colE1 ⟨112, by decide⟩ 20 (transLenTr ⟨112, by decide⟩ 20 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨112, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨112, by decide⟩ 20 (transLenTr ⟨112, by decide⟩ 20 hp)) T118_112
      hfix118_112 hinj118_112 hcardT118_112
      (fun i => conj_mem_of_fixedPoints _ _ (T118_112 i) (hfix118_112 i) _)
      ⟨118, by decide⟩ ⟨112, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨112, by decide⟩ 20 hp) Q2.T118_112_2 Q2.hfix118_112_2 Q2.hinj118_112_2
      Q2.hcardT118_112_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_112_2 i) (Q2.hfix118_112_2 i) _)
      colCert_118_112_20.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_118_0 (hp : 0 < (Q2.transData.getD 118 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨118, by decide⟩ : Fin 148)) (colE2 ⟨118, by decide⟩ 0 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨118, by decide⟩ : Fin 148))
        (colE1 ⟨118, by decide⟩ 0 (transLenTr ⟨118, by decide⟩ 0 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨118, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨118, by decide⟩ 0 (transLenTr ⟨118, by decide⟩ 0 hp)) T118_118
      hfix118_118 hinj118_118 hcardT118_118
      (fun i => conj_mem_of_fixedPoints _ _ (T118_118 i) (hfix118_118 i) _)
      ⟨118, by decide⟩ ⟨118, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨118, by decide⟩ 0 hp) Q2.T118_118_2 Q2.hfix118_118_2 Q2.hinj118_118_2
      Q2.hcardT118_118_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_118_2 i) (Q2.hfix118_118_2 i) _)
      colCert_118_118_0.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_118_1 (hp : 1 < (Q2.transData.getD 118 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨118, by decide⟩ : Fin 148)) (colE2 ⟨118, by decide⟩ 1 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨118, by decide⟩ : Fin 148))
        (colE1 ⟨118, by decide⟩ 1 (transLenTr ⟨118, by decide⟩ 1 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨118, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨118, by decide⟩ 1 (transLenTr ⟨118, by decide⟩ 1 hp)) T118_118
      hfix118_118 hinj118_118 hcardT118_118
      (fun i => conj_mem_of_fixedPoints _ _ (T118_118 i) (hfix118_118 i) _)
      ⟨118, by decide⟩ ⟨118, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨118, by decide⟩ 1 hp) Q2.T118_118_2 Q2.hfix118_118_2 Q2.hinj118_118_2
      Q2.hcardT118_118_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_118_2 i) (Q2.hfix118_118_2 i) _)
      colCert_118_118_1.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_118_2 (hp : 2 < (Q2.transData.getD 118 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨118, by decide⟩ : Fin 148)) (colE2 ⟨118, by decide⟩ 2 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨118, by decide⟩ : Fin 148))
        (colE1 ⟨118, by decide⟩ 2 (transLenTr ⟨118, by decide⟩ 2 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨118, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨118, by decide⟩ 2 (transLenTr ⟨118, by decide⟩ 2 hp)) T118_118
      hfix118_118 hinj118_118 hcardT118_118
      (fun i => conj_mem_of_fixedPoints _ _ (T118_118 i) (hfix118_118 i) _)
      ⟨118, by decide⟩ ⟨118, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨118, by decide⟩ 2 hp) Q2.T118_118_2 Q2.hfix118_118_2 Q2.hinj118_118_2
      Q2.hcardT118_118_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_118_2 i) (Q2.hfix118_118_2 i) _)
      colCert_118_118_2.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_118_3 (hp : 3 < (Q2.transData.getD 118 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨118, by decide⟩ : Fin 148)) (colE2 ⟨118, by decide⟩ 3 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨118, by decide⟩ : Fin 148))
        (colE1 ⟨118, by decide⟩ 3 (transLenTr ⟨118, by decide⟩ 3 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨118, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨118, by decide⟩ 3 (transLenTr ⟨118, by decide⟩ 3 hp)) T118_118
      hfix118_118 hinj118_118 hcardT118_118
      (fun i => conj_mem_of_fixedPoints _ _ (T118_118 i) (hfix118_118 i) _)
      ⟨118, by decide⟩ ⟨118, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨118, by decide⟩ 3 hp) Q2.T118_118_2 Q2.hfix118_118_2 Q2.hinj118_118_2
      Q2.hcardT118_118_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_118_2 i) (Q2.hfix118_118_2 i) _)
      colCert_118_118_3.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_118_4 (hp : 4 < (Q2.transData.getD 118 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨118, by decide⟩ : Fin 148)) (colE2 ⟨118, by decide⟩ 4 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨118, by decide⟩ : Fin 148))
        (colE1 ⟨118, by decide⟩ 4 (transLenTr ⟨118, by decide⟩ 4 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨118, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨118, by decide⟩ 4 (transLenTr ⟨118, by decide⟩ 4 hp)) T118_118
      hfix118_118 hinj118_118 hcardT118_118
      (fun i => conj_mem_of_fixedPoints _ _ (T118_118 i) (hfix118_118 i) _)
      ⟨118, by decide⟩ ⟨118, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨118, by decide⟩ 4 hp) Q2.T118_118_2 Q2.hfix118_118_2 Q2.hinj118_118_2
      Q2.hcardT118_118_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_118_2 i) (Q2.hfix118_118_2 i) _)
      colCert_118_118_4.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_118_5 (hp : 5 < (Q2.transData.getD 118 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨118, by decide⟩ : Fin 148)) (colE2 ⟨118, by decide⟩ 5 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨118, by decide⟩ : Fin 148))
        (colE1 ⟨118, by decide⟩ 5 (transLenTr ⟨118, by decide⟩ 5 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨118, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨118, by decide⟩ 5 (transLenTr ⟨118, by decide⟩ 5 hp)) T118_118
      hfix118_118 hinj118_118 hcardT118_118
      (fun i => conj_mem_of_fixedPoints _ _ (T118_118 i) (hfix118_118 i) _)
      ⟨118, by decide⟩ ⟨118, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨118, by decide⟩ 5 hp) Q2.T118_118_2 Q2.hfix118_118_2 Q2.hinj118_118_2
      Q2.hcardT118_118_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_118_2 i) (Q2.hfix118_118_2 i) _)
      colCert_118_118_5.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_118_6 (hp : 6 < (Q2.transData.getD 118 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨118, by decide⟩ : Fin 148)) (colE2 ⟨118, by decide⟩ 6 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨118, by decide⟩ : Fin 148))
        (colE1 ⟨118, by decide⟩ 6 (transLenTr ⟨118, by decide⟩ 6 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨118, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨118, by decide⟩ 6 (transLenTr ⟨118, by decide⟩ 6 hp)) T118_118
      hfix118_118 hinj118_118 hcardT118_118
      (fun i => conj_mem_of_fixedPoints _ _ (T118_118 i) (hfix118_118 i) _)
      ⟨118, by decide⟩ ⟨118, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨118, by decide⟩ 6 hp) Q2.T118_118_2 Q2.hfix118_118_2 Q2.hinj118_118_2
      Q2.hcardT118_118_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_118_2 i) (Q2.hfix118_118_2 i) _)
      colCert_118_118_6.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_118_7 (hp : 7 < (Q2.transData.getD 118 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨118, by decide⟩ : Fin 148)) (colE2 ⟨118, by decide⟩ 7 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨118, by decide⟩ : Fin 148))
        (colE1 ⟨118, by decide⟩ 7 (transLenTr ⟨118, by decide⟩ 7 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨118, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨118, by decide⟩ 7 (transLenTr ⟨118, by decide⟩ 7 hp)) T118_118
      hfix118_118 hinj118_118 hcardT118_118
      (fun i => conj_mem_of_fixedPoints _ _ (T118_118 i) (hfix118_118 i) _)
      ⟨118, by decide⟩ ⟨118, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨118, by decide⟩ 7 hp) Q2.T118_118_2 Q2.hfix118_118_2 Q2.hinj118_118_2
      Q2.hcardT118_118_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_118_2 i) (Q2.hfix118_118_2 i) _)
      colCert_118_118_7.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_118_8 (hp : 8 < (Q2.transData.getD 118 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨118, by decide⟩ : Fin 148)) (colE2 ⟨118, by decide⟩ 8 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨118, by decide⟩ : Fin 148))
        (colE1 ⟨118, by decide⟩ 8 (transLenTr ⟨118, by decide⟩ 8 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨118, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨118, by decide⟩ 8 (transLenTr ⟨118, by decide⟩ 8 hp)) T118_118
      hfix118_118 hinj118_118 hcardT118_118
      (fun i => conj_mem_of_fixedPoints _ _ (T118_118 i) (hfix118_118 i) _)
      ⟨118, by decide⟩ ⟨118, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨118, by decide⟩ 8 hp) Q2.T118_118_2 Q2.hfix118_118_2 Q2.hinj118_118_2
      Q2.hcardT118_118_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_118_2 i) (Q2.hfix118_118_2 i) _)
      colCert_118_118_8.hD ?_).symm
  rw [alnId_118 j hj]


end LeanDring.P5Presentation
