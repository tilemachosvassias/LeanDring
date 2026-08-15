/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Data.ColCdd.C008
import LeanDring.P5.Data.ColCdd.C009
import LeanDring.P5.Data.ColRestCheap.C048
import LeanDring.P5.Data.ColRestCheap.C049
import LeanDring.P5.Data.ColRestCheap.C050
import LeanDring.P5.Data.ColRestCheap.C051
import LeanDring.P5.Data.EntryK.C029
import LeanDring.P5.Data.EntryK.C030
import LeanDring.P5.Certificate.RingIsomorphism.MatchCore
import LeanDring.P5.Data.SpeciesDiv.C063
import LeanDring.P5.Data.SpeciesDiv.C064
import LeanDring.P5.Data.SpeciesDiv.C065

/-! # Stage-5 leaves, chunk 30 (auto-emitted).  -/

namespace LeanDring.P5Presentation

open MulAction Finset LeanDring.DRing LeanDring.MonGSet

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.style.longLine false

theorem leaf_121_106_4 (hp : 4 < (Q2.transData.getD 106 []).length)
    (j : Nat) (hj : j < (repChars.getD 121 []).length)
    (hq : (normIsRep.getD 121 []).getD j false = true) :
    species (Q2.reps (⟨106, by decide⟩ : Fin 148)) (colE2 ⟨106, by decide⟩ 4 hp)
        (rowE2 (⟨121, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨106, by decide⟩ : Fin 148))
        (colE1 ⟨106, by decide⟩ 4 (transLenTr ⟨106, by decide⟩ 4 hp))
        (rowE1 (⟨121, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨121, by decide⟩ : Fin 148) ⟨106, by decide⟩ _
      (validAt ⟨121, by decide⟩ (listedAt ⟨121, by decide⟩ hj))
      (colE1 ⟨106, by decide⟩ 4 (transLenTr ⟨106, by decide⟩ 4 hp)) T121_106
      hfix121_106 hinj121_106 hcardT121_106
      (fun i => conj_mem_of_fixedPoints _ _ (T121_106 i) (hfix121_106 i) _)
      ⟨121, by decide⟩ ⟨106, by decide⟩ _
      (Q2.validAt ⟨121, by decide⟩ (Q2.listedAt ⟨121, by decide⟩
        (alnCheck_rep ⟨121, by decide⟩ hj hq).1))
      (colE2 ⟨106, by decide⟩ 4 hp) Q2.T121_106_2 Q2.hfix121_106_2 Q2.hinj121_106_2
      Q2.hcardT121_106_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T121_106_2 i) (Q2.hfix121_106_2 i) _)
      colCert_121_106_4.hD ?_).symm
  rw [alnId_121 j hj]


theorem leaf_121_106_5 (hp : 5 < (Q2.transData.getD 106 []).length)
    (j : Nat) (hj : j < (repChars.getD 121 []).length)
    (hq : (normIsRep.getD 121 []).getD j false = true) :
    species (Q2.reps (⟨106, by decide⟩ : Fin 148)) (colE2 ⟨106, by decide⟩ 5 hp)
        (rowE2 (⟨121, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨106, by decide⟩ : Fin 148))
        (colE1 ⟨106, by decide⟩ 5 (transLenTr ⟨106, by decide⟩ 5 hp))
        (rowE1 (⟨121, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨121, by decide⟩ : Fin 148) ⟨106, by decide⟩ _
      (validAt ⟨121, by decide⟩ (listedAt ⟨121, by decide⟩ hj))
      (colE1 ⟨106, by decide⟩ 5 (transLenTr ⟨106, by decide⟩ 5 hp)) T121_106
      hfix121_106 hinj121_106 hcardT121_106
      (fun i => conj_mem_of_fixedPoints _ _ (T121_106 i) (hfix121_106 i) _)
      ⟨121, by decide⟩ ⟨106, by decide⟩ _
      (Q2.validAt ⟨121, by decide⟩ (Q2.listedAt ⟨121, by decide⟩
        (alnCheck_rep ⟨121, by decide⟩ hj hq).1))
      (colE2 ⟨106, by decide⟩ 5 hp) Q2.T121_106_2 Q2.hfix121_106_2 Q2.hinj121_106_2
      Q2.hcardT121_106_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T121_106_2 i) (Q2.hfix121_106_2 i) _)
      colCert_121_106_5.hD ?_).symm
  rw [alnId_121 j hj]


theorem leaf_121_106_10 (hp : 10 < (Q2.transData.getD 106 []).length)
    (j : Nat) (hj : j < (repChars.getD 121 []).length)
    (hq : (normIsRep.getD 121 []).getD j false = true) :
    species (Q2.reps (⟨106, by decide⟩ : Fin 148)) (colE2 ⟨106, by decide⟩ 10 hp)
        (rowE2 (⟨121, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨106, by decide⟩ : Fin 148))
        (colE1 ⟨106, by decide⟩ 10 (transLenTr ⟨106, by decide⟩ 10 hp))
        (rowE1 (⟨121, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨121, by decide⟩ : Fin 148) ⟨106, by decide⟩ _
      (validAt ⟨121, by decide⟩ (listedAt ⟨121, by decide⟩ hj))
      (colE1 ⟨106, by decide⟩ 10 (transLenTr ⟨106, by decide⟩ 10 hp)) T121_106
      hfix121_106 hinj121_106 hcardT121_106
      (fun i => conj_mem_of_fixedPoints _ _ (T121_106 i) (hfix121_106 i) _)
      ⟨121, by decide⟩ ⟨106, by decide⟩ _
      (Q2.validAt ⟨121, by decide⟩ (Q2.listedAt ⟨121, by decide⟩
        (alnCheck_rep ⟨121, by decide⟩ hj hq).1))
      (colE2 ⟨106, by decide⟩ 10 hp) Q2.T121_106_2 Q2.hfix121_106_2 Q2.hinj121_106_2
      Q2.hcardT121_106_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T121_106_2 i) (Q2.hfix121_106_2 i) _)
      ?_).symm
  rw [show colData1 (⟨121, by decide⟩ : Fin 148)
        ((colE1 ⟨106, by decide⟩ 10 (transLenTr ⟨106, by decide⟩ 10 hp) : ↥(reps ⟨106, by decide⟩)) : Coordinate 1)
        T121_106 = colFn colCertDiv_121_106_10.D1 (m := 5) from colCertDiv_121_106_10.bind1,
    show colData2 (⟨121, by decide⟩ : Fin 148)
        ((colE2 ⟨106, by decide⟩ 10 hp : ↥(Q2.reps ⟨106, by decide⟩)) : Coordinate 2)
        Q2.T121_106_2 = colFn colCertDiv_121_106_10.D2 (m := 5) from colCertDiv_121_106_10.bind2]
  rw [alnId_121 j hj]
  exact fastcode_of_div ⟨121, by decide⟩ _ _ _
    ((alnId_121 j hj) ▸ Q2.listedAt (⟨121, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨121, by decide⟩ : Fin 148) hj hq).1) colCertDiv_121_106_10_match


theorem leaf_121_106_15 (hp : 15 < (Q2.transData.getD 106 []).length)
    (j : Nat) (hj : j < (repChars.getD 121 []).length)
    (hq : (normIsRep.getD 121 []).getD j false = true) :
    species (Q2.reps (⟨106, by decide⟩ : Fin 148)) (colE2 ⟨106, by decide⟩ 15 hp)
        (rowE2 (⟨121, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨106, by decide⟩ : Fin 148))
        (colE1 ⟨106, by decide⟩ 15 (transLenTr ⟨106, by decide⟩ 15 hp))
        (rowE1 (⟨121, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨121, by decide⟩ : Fin 148) ⟨106, by decide⟩ _
      (validAt ⟨121, by decide⟩ (listedAt ⟨121, by decide⟩ hj))
      (colE1 ⟨106, by decide⟩ 15 (transLenTr ⟨106, by decide⟩ 15 hp)) T121_106
      hfix121_106 hinj121_106 hcardT121_106
      (fun i => conj_mem_of_fixedPoints _ _ (T121_106 i) (hfix121_106 i) _)
      ⟨121, by decide⟩ ⟨106, by decide⟩ _
      (Q2.validAt ⟨121, by decide⟩ (Q2.listedAt ⟨121, by decide⟩
        (alnCheck_rep ⟨121, by decide⟩ hj hq).1))
      (colE2 ⟨106, by decide⟩ 15 hp) Q2.T121_106_2 Q2.hfix121_106_2 Q2.hinj121_106_2
      Q2.hcardT121_106_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T121_106_2 i) (Q2.hfix121_106_2 i) _)
      ?_).symm
  rw [show colData1 (⟨121, by decide⟩ : Fin 148)
        ((colE1 ⟨106, by decide⟩ 15 (transLenTr ⟨106, by decide⟩ 15 hp) : ↥(reps ⟨106, by decide⟩)) : Coordinate 1)
        T121_106 = colFn colCertDiv_121_106_15.D1 (m := 5) from colCertDiv_121_106_15.bind1,
    show colData2 (⟨121, by decide⟩ : Fin 148)
        ((colE2 ⟨106, by decide⟩ 15 hp : ↥(Q2.reps ⟨106, by decide⟩)) : Coordinate 2)
        Q2.T121_106_2 = colFn colCertDiv_121_106_15.D2 (m := 5) from colCertDiv_121_106_15.bind2]
  rw [alnId_121 j hj]
  exact fastcode_of_div ⟨121, by decide⟩ _ _ _
    ((alnId_121 j hj) ▸ Q2.listedAt (⟨121, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨121, by decide⟩ : Fin 148) hj hq).1) colCertDiv_121_106_15_match


theorem leaf_121_106_20 (hp : 20 < (Q2.transData.getD 106 []).length)
    (j : Nat) (hj : j < (repChars.getD 121 []).length)
    (hq : (normIsRep.getD 121 []).getD j false = true) :
    species (Q2.reps (⟨106, by decide⟩ : Fin 148)) (colE2 ⟨106, by decide⟩ 20 hp)
        (rowE2 (⟨121, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨106, by decide⟩ : Fin 148))
        (colE1 ⟨106, by decide⟩ 20 (transLenTr ⟨106, by decide⟩ 20 hp))
        (rowE1 (⟨121, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨121, by decide⟩ : Fin 148) ⟨106, by decide⟩ _
      (validAt ⟨121, by decide⟩ (listedAt ⟨121, by decide⟩ hj))
      (colE1 ⟨106, by decide⟩ 20 (transLenTr ⟨106, by decide⟩ 20 hp)) T121_106
      hfix121_106 hinj121_106 hcardT121_106
      (fun i => conj_mem_of_fixedPoints _ _ (T121_106 i) (hfix121_106 i) _)
      ⟨121, by decide⟩ ⟨106, by decide⟩ _
      (Q2.validAt ⟨121, by decide⟩ (Q2.listedAt ⟨121, by decide⟩
        (alnCheck_rep ⟨121, by decide⟩ hj hq).1))
      (colE2 ⟨106, by decide⟩ 20 hp) Q2.T121_106_2 Q2.hfix121_106_2 Q2.hinj121_106_2
      Q2.hcardT121_106_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T121_106_2 i) (Q2.hfix121_106_2 i) _)
      ?_).symm
  rw [show colData1 (⟨121, by decide⟩ : Fin 148)
        ((colE1 ⟨106, by decide⟩ 20 (transLenTr ⟨106, by decide⟩ 20 hp) : ↥(reps ⟨106, by decide⟩)) : Coordinate 1)
        T121_106 = colFn colCertDiv_121_106_20.D1 (m := 5) from colCertDiv_121_106_20.bind1,
    show colData2 (⟨121, by decide⟩ : Fin 148)
        ((colE2 ⟨106, by decide⟩ 20 hp : ↥(Q2.reps ⟨106, by decide⟩)) : Coordinate 2)
        Q2.T121_106_2 = colFn colCertDiv_121_106_20.D2 (m := 5) from colCertDiv_121_106_20.bind2]
  rw [alnId_121 j hj]
  exact fastcode_of_div ⟨121, by decide⟩ _ _ _
    ((alnId_121 j hj) ▸ Q2.listedAt (⟨121, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨121, by decide⟩ : Fin 148) hj hq).1) colCertDiv_121_106_20_match


theorem leaf_121_110_0 (hp : 0 < (Q2.transData.getD 110 []).length)
    (j : Nat) (hj : j < (repChars.getD 121 []).length)
    (hq : (normIsRep.getD 121 []).getD j false = true) :
    species (Q2.reps (⟨110, by decide⟩ : Fin 148)) (colE2 ⟨110, by decide⟩ 0 hp)
        (rowE2 (⟨121, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨110, by decide⟩ : Fin 148))
        (colE1 ⟨110, by decide⟩ 0 (transLenTr ⟨110, by decide⟩ 0 hp))
        (rowE1 (⟨121, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨121, by decide⟩ : Fin 148) ⟨110, by decide⟩ _
      (validAt ⟨121, by decide⟩ (listedAt ⟨121, by decide⟩ hj))
      (colE1 ⟨110, by decide⟩ 0 (transLenTr ⟨110, by decide⟩ 0 hp)) T121_110
      hfix121_110 hinj121_110 hcardT121_110
      (fun i => conj_mem_of_fixedPoints _ _ (T121_110 i) (hfix121_110 i) _)
      ⟨121, by decide⟩ ⟨110, by decide⟩ _
      (Q2.validAt ⟨121, by decide⟩ (Q2.listedAt ⟨121, by decide⟩
        (alnCheck_rep ⟨121, by decide⟩ hj hq).1))
      (colE2 ⟨110, by decide⟩ 0 hp) Q2.T121_110_2 Q2.hfix121_110_2 Q2.hinj121_110_2
      Q2.hcardT121_110_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T121_110_2 i) (Q2.hfix121_110_2 i) _)
      colCert_121_110_0.hD ?_).symm
  rw [alnId_121 j hj]


theorem leaf_121_110_1 (hp : 1 < (Q2.transData.getD 110 []).length)
    (j : Nat) (hj : j < (repChars.getD 121 []).length)
    (hq : (normIsRep.getD 121 []).getD j false = true) :
    species (Q2.reps (⟨110, by decide⟩ : Fin 148)) (colE2 ⟨110, by decide⟩ 1 hp)
        (rowE2 (⟨121, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨110, by decide⟩ : Fin 148))
        (colE1 ⟨110, by decide⟩ 1 (transLenTr ⟨110, by decide⟩ 1 hp))
        (rowE1 (⟨121, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨121, by decide⟩ : Fin 148) ⟨110, by decide⟩ _
      (validAt ⟨121, by decide⟩ (listedAt ⟨121, by decide⟩ hj))
      (colE1 ⟨110, by decide⟩ 1 (transLenTr ⟨110, by decide⟩ 1 hp)) T121_110
      hfix121_110 hinj121_110 hcardT121_110
      (fun i => conj_mem_of_fixedPoints _ _ (T121_110 i) (hfix121_110 i) _)
      ⟨121, by decide⟩ ⟨110, by decide⟩ _
      (Q2.validAt ⟨121, by decide⟩ (Q2.listedAt ⟨121, by decide⟩
        (alnCheck_rep ⟨121, by decide⟩ hj hq).1))
      (colE2 ⟨110, by decide⟩ 1 hp) Q2.T121_110_2 Q2.hfix121_110_2 Q2.hinj121_110_2
      Q2.hcardT121_110_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T121_110_2 i) (Q2.hfix121_110_2 i) _)
      colCert_121_110_1.hD ?_).symm
  rw [alnId_121 j hj]


theorem leaf_121_110_2 (hp : 2 < (Q2.transData.getD 110 []).length)
    (j : Nat) (hj : j < (repChars.getD 121 []).length)
    (hq : (normIsRep.getD 121 []).getD j false = true) :
    species (Q2.reps (⟨110, by decide⟩ : Fin 148)) (colE2 ⟨110, by decide⟩ 2 hp)
        (rowE2 (⟨121, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨110, by decide⟩ : Fin 148))
        (colE1 ⟨110, by decide⟩ 2 (transLenTr ⟨110, by decide⟩ 2 hp))
        (rowE1 (⟨121, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨121, by decide⟩ : Fin 148) ⟨110, by decide⟩ _
      (validAt ⟨121, by decide⟩ (listedAt ⟨121, by decide⟩ hj))
      (colE1 ⟨110, by decide⟩ 2 (transLenTr ⟨110, by decide⟩ 2 hp)) T121_110
      hfix121_110 hinj121_110 hcardT121_110
      (fun i => conj_mem_of_fixedPoints _ _ (T121_110 i) (hfix121_110 i) _)
      ⟨121, by decide⟩ ⟨110, by decide⟩ _
      (Q2.validAt ⟨121, by decide⟩ (Q2.listedAt ⟨121, by decide⟩
        (alnCheck_rep ⟨121, by decide⟩ hj hq).1))
      (colE2 ⟨110, by decide⟩ 2 hp) Q2.T121_110_2 Q2.hfix121_110_2 Q2.hinj121_110_2
      Q2.hcardT121_110_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T121_110_2 i) (Q2.hfix121_110_2 i) _)
      colCert_121_110_2.hD ?_).symm
  rw [alnId_121 j hj]


theorem leaf_121_110_3 (hp : 3 < (Q2.transData.getD 110 []).length)
    (j : Nat) (hj : j < (repChars.getD 121 []).length)
    (hq : (normIsRep.getD 121 []).getD j false = true) :
    species (Q2.reps (⟨110, by decide⟩ : Fin 148)) (colE2 ⟨110, by decide⟩ 3 hp)
        (rowE2 (⟨121, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨110, by decide⟩ : Fin 148))
        (colE1 ⟨110, by decide⟩ 3 (transLenTr ⟨110, by decide⟩ 3 hp))
        (rowE1 (⟨121, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨121, by decide⟩ : Fin 148) ⟨110, by decide⟩ _
      (validAt ⟨121, by decide⟩ (listedAt ⟨121, by decide⟩ hj))
      (colE1 ⟨110, by decide⟩ 3 (transLenTr ⟨110, by decide⟩ 3 hp)) T121_110
      hfix121_110 hinj121_110 hcardT121_110
      (fun i => conj_mem_of_fixedPoints _ _ (T121_110 i) (hfix121_110 i) _)
      ⟨121, by decide⟩ ⟨110, by decide⟩ _
      (Q2.validAt ⟨121, by decide⟩ (Q2.listedAt ⟨121, by decide⟩
        (alnCheck_rep ⟨121, by decide⟩ hj hq).1))
      (colE2 ⟨110, by decide⟩ 3 hp) Q2.T121_110_2 Q2.hfix121_110_2 Q2.hinj121_110_2
      Q2.hcardT121_110_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T121_110_2 i) (Q2.hfix121_110_2 i) _)
      colCert_121_110_3.hD ?_).symm
  rw [alnId_121 j hj]


theorem leaf_121_110_4 (hp : 4 < (Q2.transData.getD 110 []).length)
    (j : Nat) (hj : j < (repChars.getD 121 []).length)
    (hq : (normIsRep.getD 121 []).getD j false = true) :
    species (Q2.reps (⟨110, by decide⟩ : Fin 148)) (colE2 ⟨110, by decide⟩ 4 hp)
        (rowE2 (⟨121, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨110, by decide⟩ : Fin 148))
        (colE1 ⟨110, by decide⟩ 4 (transLenTr ⟨110, by decide⟩ 4 hp))
        (rowE1 (⟨121, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨121, by decide⟩ : Fin 148) ⟨110, by decide⟩ _
      (validAt ⟨121, by decide⟩ (listedAt ⟨121, by decide⟩ hj))
      (colE1 ⟨110, by decide⟩ 4 (transLenTr ⟨110, by decide⟩ 4 hp)) T121_110
      hfix121_110 hinj121_110 hcardT121_110
      (fun i => conj_mem_of_fixedPoints _ _ (T121_110 i) (hfix121_110 i) _)
      ⟨121, by decide⟩ ⟨110, by decide⟩ _
      (Q2.validAt ⟨121, by decide⟩ (Q2.listedAt ⟨121, by decide⟩
        (alnCheck_rep ⟨121, by decide⟩ hj hq).1))
      (colE2 ⟨110, by decide⟩ 4 hp) Q2.T121_110_2 Q2.hfix121_110_2 Q2.hinj121_110_2
      Q2.hcardT121_110_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T121_110_2 i) (Q2.hfix121_110_2 i) _)
      colCert_121_110_4.hD ?_).symm
  rw [alnId_121 j hj]


theorem leaf_121_110_5 (hp : 5 < (Q2.transData.getD 110 []).length)
    (j : Nat) (hj : j < (repChars.getD 121 []).length)
    (hq : (normIsRep.getD 121 []).getD j false = true) :
    species (Q2.reps (⟨110, by decide⟩ : Fin 148)) (colE2 ⟨110, by decide⟩ 5 hp)
        (rowE2 (⟨121, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨110, by decide⟩ : Fin 148))
        (colE1 ⟨110, by decide⟩ 5 (transLenTr ⟨110, by decide⟩ 5 hp))
        (rowE1 (⟨121, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨121, by decide⟩ : Fin 148) ⟨110, by decide⟩ _
      (validAt ⟨121, by decide⟩ (listedAt ⟨121, by decide⟩ hj))
      (colE1 ⟨110, by decide⟩ 5 (transLenTr ⟨110, by decide⟩ 5 hp)) T121_110
      hfix121_110 hinj121_110 hcardT121_110
      (fun i => conj_mem_of_fixedPoints _ _ (T121_110 i) (hfix121_110 i) _)
      ⟨121, by decide⟩ ⟨110, by decide⟩ _
      (Q2.validAt ⟨121, by decide⟩ (Q2.listedAt ⟨121, by decide⟩
        (alnCheck_rep ⟨121, by decide⟩ hj hq).1))
      (colE2 ⟨110, by decide⟩ 5 hp) Q2.T121_110_2 Q2.hfix121_110_2 Q2.hinj121_110_2
      Q2.hcardT121_110_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T121_110_2 i) (Q2.hfix121_110_2 i) _)
      colCert_121_110_5.hD ?_).symm
  rw [alnId_121 j hj]


theorem leaf_121_110_10 (hp : 10 < (Q2.transData.getD 110 []).length)
    (j : Nat) (hj : j < (repChars.getD 121 []).length)
    (hq : (normIsRep.getD 121 []).getD j false = true) :
    species (Q2.reps (⟨110, by decide⟩ : Fin 148)) (colE2 ⟨110, by decide⟩ 10 hp)
        (rowE2 (⟨121, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨110, by decide⟩ : Fin 148))
        (colE1 ⟨110, by decide⟩ 10 (transLenTr ⟨110, by decide⟩ 10 hp))
        (rowE1 (⟨121, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨121, by decide⟩ : Fin 148) ⟨110, by decide⟩ _
      (validAt ⟨121, by decide⟩ (listedAt ⟨121, by decide⟩ hj))
      (colE1 ⟨110, by decide⟩ 10 (transLenTr ⟨110, by decide⟩ 10 hp)) T121_110
      hfix121_110 hinj121_110 hcardT121_110
      (fun i => conj_mem_of_fixedPoints _ _ (T121_110 i) (hfix121_110 i) _)
      ⟨121, by decide⟩ ⟨110, by decide⟩ _
      (Q2.validAt ⟨121, by decide⟩ (Q2.listedAt ⟨121, by decide⟩
        (alnCheck_rep ⟨121, by decide⟩ hj hq).1))
      (colE2 ⟨110, by decide⟩ 10 hp) Q2.T121_110_2 Q2.hfix121_110_2 Q2.hinj121_110_2
      Q2.hcardT121_110_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T121_110_2 i) (Q2.hfix121_110_2 i) _)
      colCert_121_110_10.hD ?_).symm
  rw [alnId_121 j hj]


theorem leaf_121_110_15 (hp : 15 < (Q2.transData.getD 110 []).length)
    (j : Nat) (hj : j < (repChars.getD 121 []).length)
    (hq : (normIsRep.getD 121 []).getD j false = true) :
    species (Q2.reps (⟨110, by decide⟩ : Fin 148)) (colE2 ⟨110, by decide⟩ 15 hp)
        (rowE2 (⟨121, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨110, by decide⟩ : Fin 148))
        (colE1 ⟨110, by decide⟩ 15 (transLenTr ⟨110, by decide⟩ 15 hp))
        (rowE1 (⟨121, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨121, by decide⟩ : Fin 148) ⟨110, by decide⟩ _
      (validAt ⟨121, by decide⟩ (listedAt ⟨121, by decide⟩ hj))
      (colE1 ⟨110, by decide⟩ 15 (transLenTr ⟨110, by decide⟩ 15 hp)) T121_110
      hfix121_110 hinj121_110 hcardT121_110
      (fun i => conj_mem_of_fixedPoints _ _ (T121_110 i) (hfix121_110 i) _)
      ⟨121, by decide⟩ ⟨110, by decide⟩ _
      (Q2.validAt ⟨121, by decide⟩ (Q2.listedAt ⟨121, by decide⟩
        (alnCheck_rep ⟨121, by decide⟩ hj hq).1))
      (colE2 ⟨110, by decide⟩ 15 hp) Q2.T121_110_2 Q2.hfix121_110_2 Q2.hinj121_110_2
      Q2.hcardT121_110_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T121_110_2 i) (Q2.hfix121_110_2 i) _)
      colCert_121_110_15.hD ?_).symm
  rw [alnId_121 j hj]


theorem leaf_121_110_20 (hp : 20 < (Q2.transData.getD 110 []).length)
    (j : Nat) (hj : j < (repChars.getD 121 []).length)
    (hq : (normIsRep.getD 121 []).getD j false = true) :
    species (Q2.reps (⟨110, by decide⟩ : Fin 148)) (colE2 ⟨110, by decide⟩ 20 hp)
        (rowE2 (⟨121, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨110, by decide⟩ : Fin 148))
        (colE1 ⟨110, by decide⟩ 20 (transLenTr ⟨110, by decide⟩ 20 hp))
        (rowE1 (⟨121, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨121, by decide⟩ : Fin 148) ⟨110, by decide⟩ _
      (validAt ⟨121, by decide⟩ (listedAt ⟨121, by decide⟩ hj))
      (colE1 ⟨110, by decide⟩ 20 (transLenTr ⟨110, by decide⟩ 20 hp)) T121_110
      hfix121_110 hinj121_110 hcardT121_110
      (fun i => conj_mem_of_fixedPoints _ _ (T121_110 i) (hfix121_110 i) _)
      ⟨121, by decide⟩ ⟨110, by decide⟩ _
      (Q2.validAt ⟨121, by decide⟩ (Q2.listedAt ⟨121, by decide⟩
        (alnCheck_rep ⟨121, by decide⟩ hj hq).1))
      (colE2 ⟨110, by decide⟩ 20 hp) Q2.T121_110_2 Q2.hfix121_110_2 Q2.hinj121_110_2
      Q2.hcardT121_110_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T121_110_2 i) (Q2.hfix121_110_2 i) _)
      colCert_121_110_20.hD ?_).symm
  rw [alnId_121 j hj]


theorem leaf_121_110_25 (hp : 25 < (Q2.transData.getD 110 []).length)
    (j : Nat) (hj : j < (repChars.getD 121 []).length)
    (hq : (normIsRep.getD 121 []).getD j false = true) :
    species (Q2.reps (⟨110, by decide⟩ : Fin 148)) (colE2 ⟨110, by decide⟩ 25 hp)
        (rowE2 (⟨121, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨110, by decide⟩ : Fin 148))
        (colE1 ⟨110, by decide⟩ 25 (transLenTr ⟨110, by decide⟩ 25 hp))
        (rowE1 (⟨121, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨121, by decide⟩ : Fin 148) ⟨110, by decide⟩ _
      (validAt ⟨121, by decide⟩ (listedAt ⟨121, by decide⟩ hj))
      (colE1 ⟨110, by decide⟩ 25 (transLenTr ⟨110, by decide⟩ 25 hp)) T121_110
      hfix121_110 hinj121_110 hcardT121_110
      (fun i => conj_mem_of_fixedPoints _ _ (T121_110 i) (hfix121_110 i) _)
      ⟨121, by decide⟩ ⟨110, by decide⟩ _
      (Q2.validAt ⟨121, by decide⟩ (Q2.listedAt ⟨121, by decide⟩
        (alnCheck_rep ⟨121, by decide⟩ hj hq).1))
      (colE2 ⟨110, by decide⟩ 25 hp) Q2.T121_110_2 Q2.hfix121_110_2 Q2.hinj121_110_2
      Q2.hcardT121_110_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T121_110_2 i) (Q2.hfix121_110_2 i) _)
      colCert_121_110_25.hD ?_).symm
  rw [alnId_121 j hj]


theorem leaf_121_110_50 (hp : 50 < (Q2.transData.getD 110 []).length)
    (j : Nat) (hj : j < (repChars.getD 121 []).length)
    (hq : (normIsRep.getD 121 []).getD j false = true) :
    species (Q2.reps (⟨110, by decide⟩ : Fin 148)) (colE2 ⟨110, by decide⟩ 50 hp)
        (rowE2 (⟨121, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨110, by decide⟩ : Fin 148))
        (colE1 ⟨110, by decide⟩ 50 (transLenTr ⟨110, by decide⟩ 50 hp))
        (rowE1 (⟨121, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨121, by decide⟩ : Fin 148) ⟨110, by decide⟩ _
      (validAt ⟨121, by decide⟩ (listedAt ⟨121, by decide⟩ hj))
      (colE1 ⟨110, by decide⟩ 50 (transLenTr ⟨110, by decide⟩ 50 hp)) T121_110
      hfix121_110 hinj121_110 hcardT121_110
      (fun i => conj_mem_of_fixedPoints _ _ (T121_110 i) (hfix121_110 i) _)
      ⟨121, by decide⟩ ⟨110, by decide⟩ _
      (Q2.validAt ⟨121, by decide⟩ (Q2.listedAt ⟨121, by decide⟩
        (alnCheck_rep ⟨121, by decide⟩ hj hq).1))
      (colE2 ⟨110, by decide⟩ 50 hp) Q2.T121_110_2 Q2.hfix121_110_2 Q2.hinj121_110_2
      Q2.hcardT121_110_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T121_110_2 i) (Q2.hfix121_110_2 i) _)
      colCert_121_110_50.hD ?_).symm
  rw [alnId_121 j hj]


theorem leaf_121_110_75 (hp : 75 < (Q2.transData.getD 110 []).length)
    (j : Nat) (hj : j < (repChars.getD 121 []).length)
    (hq : (normIsRep.getD 121 []).getD j false = true) :
    species (Q2.reps (⟨110, by decide⟩ : Fin 148)) (colE2 ⟨110, by decide⟩ 75 hp)
        (rowE2 (⟨121, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨110, by decide⟩ : Fin 148))
        (colE1 ⟨110, by decide⟩ 75 (transLenTr ⟨110, by decide⟩ 75 hp))
        (rowE1 (⟨121, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨121, by decide⟩ : Fin 148) ⟨110, by decide⟩ _
      (validAt ⟨121, by decide⟩ (listedAt ⟨121, by decide⟩ hj))
      (colE1 ⟨110, by decide⟩ 75 (transLenTr ⟨110, by decide⟩ 75 hp)) T121_110
      hfix121_110 hinj121_110 hcardT121_110
      (fun i => conj_mem_of_fixedPoints _ _ (T121_110 i) (hfix121_110 i) _)
      ⟨121, by decide⟩ ⟨110, by decide⟩ _
      (Q2.validAt ⟨121, by decide⟩ (Q2.listedAt ⟨121, by decide⟩
        (alnCheck_rep ⟨121, by decide⟩ hj hq).1))
      (colE2 ⟨110, by decide⟩ 75 hp) Q2.T121_110_2 Q2.hfix121_110_2 Q2.hinj121_110_2
      Q2.hcardT121_110_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T121_110_2 i) (Q2.hfix121_110_2 i) _)
      colCert_121_110_75.hD ?_).symm
  rw [alnId_121 j hj]


theorem leaf_121_110_100 (hp : 100 < (Q2.transData.getD 110 []).length)
    (j : Nat) (hj : j < (repChars.getD 121 []).length)
    (hq : (normIsRep.getD 121 []).getD j false = true) :
    species (Q2.reps (⟨110, by decide⟩ : Fin 148)) (colE2 ⟨110, by decide⟩ 100 hp)
        (rowE2 (⟨121, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨110, by decide⟩ : Fin 148))
        (colE1 ⟨110, by decide⟩ 100 (transLenTr ⟨110, by decide⟩ 100 hp))
        (rowE1 (⟨121, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨121, by decide⟩ : Fin 148) ⟨110, by decide⟩ _
      (validAt ⟨121, by decide⟩ (listedAt ⟨121, by decide⟩ hj))
      (colE1 ⟨110, by decide⟩ 100 (transLenTr ⟨110, by decide⟩ 100 hp)) T121_110
      hfix121_110 hinj121_110 hcardT121_110
      (fun i => conj_mem_of_fixedPoints _ _ (T121_110 i) (hfix121_110 i) _)
      ⟨121, by decide⟩ ⟨110, by decide⟩ _
      (Q2.validAt ⟨121, by decide⟩ (Q2.listedAt ⟨121, by decide⟩
        (alnCheck_rep ⟨121, by decide⟩ hj hq).1))
      (colE2 ⟨110, by decide⟩ 100 hp) Q2.T121_110_2 Q2.hfix121_110_2 Q2.hinj121_110_2
      Q2.hcardT121_110_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T121_110_2 i) (Q2.hfix121_110_2 i) _)
      colCert_121_110_100.hD ?_).symm
  rw [alnId_121 j hj]


theorem leaf_121_121_0 (hp : 0 < (Q2.transData.getD 121 []).length)
    (j : Nat) (hj : j < (repChars.getD 121 []).length)
    (hq : (normIsRep.getD 121 []).getD j false = true) :
    species (Q2.reps (⟨121, by decide⟩ : Fin 148)) (colE2 ⟨121, by decide⟩ 0 hp)
        (rowE2 (⟨121, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨121, by decide⟩ : Fin 148))
        (colE1 ⟨121, by decide⟩ 0 (transLenTr ⟨121, by decide⟩ 0 hp))
        (rowE1 (⟨121, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨121, by decide⟩ : Fin 148) ⟨121, by decide⟩ _
      (validAt ⟨121, by decide⟩ (listedAt ⟨121, by decide⟩ hj))
      (colE1 ⟨121, by decide⟩ 0 (transLenTr ⟨121, by decide⟩ 0 hp)) T121_121
      hfix121_121 hinj121_121 hcardT121_121
      (fun i => conj_mem_of_fixedPoints _ _ (T121_121 i) (hfix121_121 i) _)
      ⟨121, by decide⟩ ⟨121, by decide⟩ _
      (Q2.validAt ⟨121, by decide⟩ (Q2.listedAt ⟨121, by decide⟩
        (alnCheck_rep ⟨121, by decide⟩ hj hq).1))
      (colE2 ⟨121, by decide⟩ 0 hp) Q2.T121_121_2 Q2.hfix121_121_2 Q2.hinj121_121_2
      Q2.hcardT121_121_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T121_121_2 i) (Q2.hfix121_121_2 i) _)
      colCert_121_121_0.hD ?_).symm
  rw [alnId_121 j hj]


theorem leaf_121_121_1 (hp : 1 < (Q2.transData.getD 121 []).length)
    (j : Nat) (hj : j < (repChars.getD 121 []).length)
    (hq : (normIsRep.getD 121 []).getD j false = true) :
    species (Q2.reps (⟨121, by decide⟩ : Fin 148)) (colE2 ⟨121, by decide⟩ 1 hp)
        (rowE2 (⟨121, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨121, by decide⟩ : Fin 148))
        (colE1 ⟨121, by decide⟩ 1 (transLenTr ⟨121, by decide⟩ 1 hp))
        (rowE1 (⟨121, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨121, by decide⟩ : Fin 148) ⟨121, by decide⟩ _
      (validAt ⟨121, by decide⟩ (listedAt ⟨121, by decide⟩ hj))
      (colE1 ⟨121, by decide⟩ 1 (transLenTr ⟨121, by decide⟩ 1 hp)) T121_121
      hfix121_121 hinj121_121 hcardT121_121
      (fun i => conj_mem_of_fixedPoints _ _ (T121_121 i) (hfix121_121 i) _)
      ⟨121, by decide⟩ ⟨121, by decide⟩ _
      (Q2.validAt ⟨121, by decide⟩ (Q2.listedAt ⟨121, by decide⟩
        (alnCheck_rep ⟨121, by decide⟩ hj hq).1))
      (colE2 ⟨121, by decide⟩ 1 hp) Q2.T121_121_2 Q2.hfix121_121_2 Q2.hinj121_121_2
      Q2.hcardT121_121_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T121_121_2 i) (Q2.hfix121_121_2 i) _)
      colCert_121_121_1.hD ?_).symm
  rw [alnId_121 j hj]


theorem leaf_121_121_2 (hp : 2 < (Q2.transData.getD 121 []).length)
    (j : Nat) (hj : j < (repChars.getD 121 []).length)
    (hq : (normIsRep.getD 121 []).getD j false = true) :
    species (Q2.reps (⟨121, by decide⟩ : Fin 148)) (colE2 ⟨121, by decide⟩ 2 hp)
        (rowE2 (⟨121, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨121, by decide⟩ : Fin 148))
        (colE1 ⟨121, by decide⟩ 2 (transLenTr ⟨121, by decide⟩ 2 hp))
        (rowE1 (⟨121, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨121, by decide⟩ : Fin 148) ⟨121, by decide⟩ _
      (validAt ⟨121, by decide⟩ (listedAt ⟨121, by decide⟩ hj))
      (colE1 ⟨121, by decide⟩ 2 (transLenTr ⟨121, by decide⟩ 2 hp)) T121_121
      hfix121_121 hinj121_121 hcardT121_121
      (fun i => conj_mem_of_fixedPoints _ _ (T121_121 i) (hfix121_121 i) _)
      ⟨121, by decide⟩ ⟨121, by decide⟩ _
      (Q2.validAt ⟨121, by decide⟩ (Q2.listedAt ⟨121, by decide⟩
        (alnCheck_rep ⟨121, by decide⟩ hj hq).1))
      (colE2 ⟨121, by decide⟩ 2 hp) Q2.T121_121_2 Q2.hfix121_121_2 Q2.hinj121_121_2
      Q2.hcardT121_121_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T121_121_2 i) (Q2.hfix121_121_2 i) _)
      colCert_121_121_2.hD ?_).symm
  rw [alnId_121 j hj]


theorem leaf_121_121_3 (hp : 3 < (Q2.transData.getD 121 []).length)
    (j : Nat) (hj : j < (repChars.getD 121 []).length)
    (hq : (normIsRep.getD 121 []).getD j false = true) :
    species (Q2.reps (⟨121, by decide⟩ : Fin 148)) (colE2 ⟨121, by decide⟩ 3 hp)
        (rowE2 (⟨121, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨121, by decide⟩ : Fin 148))
        (colE1 ⟨121, by decide⟩ 3 (transLenTr ⟨121, by decide⟩ 3 hp))
        (rowE1 (⟨121, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨121, by decide⟩ : Fin 148) ⟨121, by decide⟩ _
      (validAt ⟨121, by decide⟩ (listedAt ⟨121, by decide⟩ hj))
      (colE1 ⟨121, by decide⟩ 3 (transLenTr ⟨121, by decide⟩ 3 hp)) T121_121
      hfix121_121 hinj121_121 hcardT121_121
      (fun i => conj_mem_of_fixedPoints _ _ (T121_121 i) (hfix121_121 i) _)
      ⟨121, by decide⟩ ⟨121, by decide⟩ _
      (Q2.validAt ⟨121, by decide⟩ (Q2.listedAt ⟨121, by decide⟩
        (alnCheck_rep ⟨121, by decide⟩ hj hq).1))
      (colE2 ⟨121, by decide⟩ 3 hp) Q2.T121_121_2 Q2.hfix121_121_2 Q2.hinj121_121_2
      Q2.hcardT121_121_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T121_121_2 i) (Q2.hfix121_121_2 i) _)
      colCert_121_121_3.hD ?_).symm
  rw [alnId_121 j hj]


theorem leaf_121_121_4 (hp : 4 < (Q2.transData.getD 121 []).length)
    (j : Nat) (hj : j < (repChars.getD 121 []).length)
    (hq : (normIsRep.getD 121 []).getD j false = true) :
    species (Q2.reps (⟨121, by decide⟩ : Fin 148)) (colE2 ⟨121, by decide⟩ 4 hp)
        (rowE2 (⟨121, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨121, by decide⟩ : Fin 148))
        (colE1 ⟨121, by decide⟩ 4 (transLenTr ⟨121, by decide⟩ 4 hp))
        (rowE1 (⟨121, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨121, by decide⟩ : Fin 148) ⟨121, by decide⟩ _
      (validAt ⟨121, by decide⟩ (listedAt ⟨121, by decide⟩ hj))
      (colE1 ⟨121, by decide⟩ 4 (transLenTr ⟨121, by decide⟩ 4 hp)) T121_121
      hfix121_121 hinj121_121 hcardT121_121
      (fun i => conj_mem_of_fixedPoints _ _ (T121_121 i) (hfix121_121 i) _)
      ⟨121, by decide⟩ ⟨121, by decide⟩ _
      (Q2.validAt ⟨121, by decide⟩ (Q2.listedAt ⟨121, by decide⟩
        (alnCheck_rep ⟨121, by decide⟩ hj hq).1))
      (colE2 ⟨121, by decide⟩ 4 hp) Q2.T121_121_2 Q2.hfix121_121_2 Q2.hinj121_121_2
      Q2.hcardT121_121_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T121_121_2 i) (Q2.hfix121_121_2 i) _)
      colCert_121_121_4.hD ?_).symm
  rw [alnId_121 j hj]


theorem leaf_121_121_5 (hp : 5 < (Q2.transData.getD 121 []).length)
    (j : Nat) (hj : j < (repChars.getD 121 []).length)
    (hq : (normIsRep.getD 121 []).getD j false = true) :
    species (Q2.reps (⟨121, by decide⟩ : Fin 148)) (colE2 ⟨121, by decide⟩ 5 hp)
        (rowE2 (⟨121, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨121, by decide⟩ : Fin 148))
        (colE1 ⟨121, by decide⟩ 5 (transLenTr ⟨121, by decide⟩ 5 hp))
        (rowE1 (⟨121, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨121, by decide⟩ : Fin 148) ⟨121, by decide⟩ _
      (validAt ⟨121, by decide⟩ (listedAt ⟨121, by decide⟩ hj))
      (colE1 ⟨121, by decide⟩ 5 (transLenTr ⟨121, by decide⟩ 5 hp)) T121_121
      hfix121_121 hinj121_121 hcardT121_121
      (fun i => conj_mem_of_fixedPoints _ _ (T121_121 i) (hfix121_121 i) _)
      ⟨121, by decide⟩ ⟨121, by decide⟩ _
      (Q2.validAt ⟨121, by decide⟩ (Q2.listedAt ⟨121, by decide⟩
        (alnCheck_rep ⟨121, by decide⟩ hj hq).1))
      (colE2 ⟨121, by decide⟩ 5 hp) Q2.T121_121_2 Q2.hfix121_121_2 Q2.hinj121_121_2
      Q2.hcardT121_121_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T121_121_2 i) (Q2.hfix121_121_2 i) _)
      colCert_121_121_5.hD ?_).symm
  rw [alnId_121 j hj]


theorem leaf_121_121_6 (hp : 6 < (Q2.transData.getD 121 []).length)
    (j : Nat) (hj : j < (repChars.getD 121 []).length)
    (hq : (normIsRep.getD 121 []).getD j false = true) :
    species (Q2.reps (⟨121, by decide⟩ : Fin 148)) (colE2 ⟨121, by decide⟩ 6 hp)
        (rowE2 (⟨121, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨121, by decide⟩ : Fin 148))
        (colE1 ⟨121, by decide⟩ 6 (transLenTr ⟨121, by decide⟩ 6 hp))
        (rowE1 (⟨121, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨121, by decide⟩ : Fin 148) ⟨121, by decide⟩ _
      (validAt ⟨121, by decide⟩ (listedAt ⟨121, by decide⟩ hj))
      (colE1 ⟨121, by decide⟩ 6 (transLenTr ⟨121, by decide⟩ 6 hp)) T121_121
      hfix121_121 hinj121_121 hcardT121_121
      (fun i => conj_mem_of_fixedPoints _ _ (T121_121 i) (hfix121_121 i) _)
      ⟨121, by decide⟩ ⟨121, by decide⟩ _
      (Q2.validAt ⟨121, by decide⟩ (Q2.listedAt ⟨121, by decide⟩
        (alnCheck_rep ⟨121, by decide⟩ hj hq).1))
      (colE2 ⟨121, by decide⟩ 6 hp) Q2.T121_121_2 Q2.hfix121_121_2 Q2.hinj121_121_2
      Q2.hcardT121_121_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T121_121_2 i) (Q2.hfix121_121_2 i) _)
      colCert_121_121_6.hD ?_).symm
  rw [alnId_121 j hj]


theorem leaf_121_121_7 (hp : 7 < (Q2.transData.getD 121 []).length)
    (j : Nat) (hj : j < (repChars.getD 121 []).length)
    (hq : (normIsRep.getD 121 []).getD j false = true) :
    species (Q2.reps (⟨121, by decide⟩ : Fin 148)) (colE2 ⟨121, by decide⟩ 7 hp)
        (rowE2 (⟨121, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨121, by decide⟩ : Fin 148))
        (colE1 ⟨121, by decide⟩ 7 (transLenTr ⟨121, by decide⟩ 7 hp))
        (rowE1 (⟨121, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨121, by decide⟩ : Fin 148) ⟨121, by decide⟩ _
      (validAt ⟨121, by decide⟩ (listedAt ⟨121, by decide⟩ hj))
      (colE1 ⟨121, by decide⟩ 7 (transLenTr ⟨121, by decide⟩ 7 hp)) T121_121
      hfix121_121 hinj121_121 hcardT121_121
      (fun i => conj_mem_of_fixedPoints _ _ (T121_121 i) (hfix121_121 i) _)
      ⟨121, by decide⟩ ⟨121, by decide⟩ _
      (Q2.validAt ⟨121, by decide⟩ (Q2.listedAt ⟨121, by decide⟩
        (alnCheck_rep ⟨121, by decide⟩ hj hq).1))
      (colE2 ⟨121, by decide⟩ 7 hp) Q2.T121_121_2 Q2.hfix121_121_2 Q2.hinj121_121_2
      Q2.hcardT121_121_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T121_121_2 i) (Q2.hfix121_121_2 i) _)
      colCert_121_121_7.hD ?_).symm
  rw [alnId_121 j hj]


theorem leaf_121_121_8 (hp : 8 < (Q2.transData.getD 121 []).length)
    (j : Nat) (hj : j < (repChars.getD 121 []).length)
    (hq : (normIsRep.getD 121 []).getD j false = true) :
    species (Q2.reps (⟨121, by decide⟩ : Fin 148)) (colE2 ⟨121, by decide⟩ 8 hp)
        (rowE2 (⟨121, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨121, by decide⟩ : Fin 148))
        (colE1 ⟨121, by decide⟩ 8 (transLenTr ⟨121, by decide⟩ 8 hp))
        (rowE1 (⟨121, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨121, by decide⟩ : Fin 148) ⟨121, by decide⟩ _
      (validAt ⟨121, by decide⟩ (listedAt ⟨121, by decide⟩ hj))
      (colE1 ⟨121, by decide⟩ 8 (transLenTr ⟨121, by decide⟩ 8 hp)) T121_121
      hfix121_121 hinj121_121 hcardT121_121
      (fun i => conj_mem_of_fixedPoints _ _ (T121_121 i) (hfix121_121 i) _)
      ⟨121, by decide⟩ ⟨121, by decide⟩ _
      (Q2.validAt ⟨121, by decide⟩ (Q2.listedAt ⟨121, by decide⟩
        (alnCheck_rep ⟨121, by decide⟩ hj hq).1))
      (colE2 ⟨121, by decide⟩ 8 hp) Q2.T121_121_2 Q2.hfix121_121_2 Q2.hinj121_121_2
      Q2.hcardT121_121_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T121_121_2 i) (Q2.hfix121_121_2 i) _)
      colCert_121_121_8.hD ?_).symm
  rw [alnId_121 j hj]


theorem leaf_121_121_9 (hp : 9 < (Q2.transData.getD 121 []).length)
    (j : Nat) (hj : j < (repChars.getD 121 []).length)
    (hq : (normIsRep.getD 121 []).getD j false = true) :
    species (Q2.reps (⟨121, by decide⟩ : Fin 148)) (colE2 ⟨121, by decide⟩ 9 hp)
        (rowE2 (⟨121, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨121, by decide⟩ : Fin 148))
        (colE1 ⟨121, by decide⟩ 9 (transLenTr ⟨121, by decide⟩ 9 hp))
        (rowE1 (⟨121, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨121, by decide⟩ : Fin 148) ⟨121, by decide⟩ _
      (validAt ⟨121, by decide⟩ (listedAt ⟨121, by decide⟩ hj))
      (colE1 ⟨121, by decide⟩ 9 (transLenTr ⟨121, by decide⟩ 9 hp)) T121_121
      hfix121_121 hinj121_121 hcardT121_121
      (fun i => conj_mem_of_fixedPoints _ _ (T121_121 i) (hfix121_121 i) _)
      ⟨121, by decide⟩ ⟨121, by decide⟩ _
      (Q2.validAt ⟨121, by decide⟩ (Q2.listedAt ⟨121, by decide⟩
        (alnCheck_rep ⟨121, by decide⟩ hj hq).1))
      (colE2 ⟨121, by decide⟩ 9 hp) Q2.T121_121_2 Q2.hfix121_121_2 Q2.hinj121_121_2
      Q2.hcardT121_121_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T121_121_2 i) (Q2.hfix121_121_2 i) _)
      colCert_121_121_9.hD ?_).symm
  rw [alnId_121 j hj]


theorem leaf_121_121_10 (hp : 10 < (Q2.transData.getD 121 []).length)
    (j : Nat) (hj : j < (repChars.getD 121 []).length)
    (hq : (normIsRep.getD 121 []).getD j false = true) :
    species (Q2.reps (⟨121, by decide⟩ : Fin 148)) (colE2 ⟨121, by decide⟩ 10 hp)
        (rowE2 (⟨121, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨121, by decide⟩ : Fin 148))
        (colE1 ⟨121, by decide⟩ 10 (transLenTr ⟨121, by decide⟩ 10 hp))
        (rowE1 (⟨121, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨121, by decide⟩ : Fin 148) ⟨121, by decide⟩ _
      (validAt ⟨121, by decide⟩ (listedAt ⟨121, by decide⟩ hj))
      (colE1 ⟨121, by decide⟩ 10 (transLenTr ⟨121, by decide⟩ 10 hp)) T121_121
      hfix121_121 hinj121_121 hcardT121_121
      (fun i => conj_mem_of_fixedPoints _ _ (T121_121 i) (hfix121_121 i) _)
      ⟨121, by decide⟩ ⟨121, by decide⟩ _
      (Q2.validAt ⟨121, by decide⟩ (Q2.listedAt ⟨121, by decide⟩
        (alnCheck_rep ⟨121, by decide⟩ hj hq).1))
      (colE2 ⟨121, by decide⟩ 10 hp) Q2.T121_121_2 Q2.hfix121_121_2 Q2.hinj121_121_2
      Q2.hcardT121_121_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T121_121_2 i) (Q2.hfix121_121_2 i) _)
      colCert_121_121_10.hD ?_).symm
  rw [alnId_121 j hj]


theorem leaf_121_121_11 (hp : 11 < (Q2.transData.getD 121 []).length)
    (j : Nat) (hj : j < (repChars.getD 121 []).length)
    (hq : (normIsRep.getD 121 []).getD j false = true) :
    species (Q2.reps (⟨121, by decide⟩ : Fin 148)) (colE2 ⟨121, by decide⟩ 11 hp)
        (rowE2 (⟨121, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨121, by decide⟩ : Fin 148))
        (colE1 ⟨121, by decide⟩ 11 (transLenTr ⟨121, by decide⟩ 11 hp))
        (rowE1 (⟨121, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨121, by decide⟩ : Fin 148) ⟨121, by decide⟩ _
      (validAt ⟨121, by decide⟩ (listedAt ⟨121, by decide⟩ hj))
      (colE1 ⟨121, by decide⟩ 11 (transLenTr ⟨121, by decide⟩ 11 hp)) T121_121
      hfix121_121 hinj121_121 hcardT121_121
      (fun i => conj_mem_of_fixedPoints _ _ (T121_121 i) (hfix121_121 i) _)
      ⟨121, by decide⟩ ⟨121, by decide⟩ _
      (Q2.validAt ⟨121, by decide⟩ (Q2.listedAt ⟨121, by decide⟩
        (alnCheck_rep ⟨121, by decide⟩ hj hq).1))
      (colE2 ⟨121, by decide⟩ 11 hp) Q2.T121_121_2 Q2.hfix121_121_2 Q2.hinj121_121_2
      Q2.hcardT121_121_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T121_121_2 i) (Q2.hfix121_121_2 i) _)
      colCert_121_121_11.hD ?_).symm
  rw [alnId_121 j hj]


theorem leaf_121_121_12 (hp : 12 < (Q2.transData.getD 121 []).length)
    (j : Nat) (hj : j < (repChars.getD 121 []).length)
    (hq : (normIsRep.getD 121 []).getD j false = true) :
    species (Q2.reps (⟨121, by decide⟩ : Fin 148)) (colE2 ⟨121, by decide⟩ 12 hp)
        (rowE2 (⟨121, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨121, by decide⟩ : Fin 148))
        (colE1 ⟨121, by decide⟩ 12 (transLenTr ⟨121, by decide⟩ 12 hp))
        (rowE1 (⟨121, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨121, by decide⟩ : Fin 148) ⟨121, by decide⟩ _
      (validAt ⟨121, by decide⟩ (listedAt ⟨121, by decide⟩ hj))
      (colE1 ⟨121, by decide⟩ 12 (transLenTr ⟨121, by decide⟩ 12 hp)) T121_121
      hfix121_121 hinj121_121 hcardT121_121
      (fun i => conj_mem_of_fixedPoints _ _ (T121_121 i) (hfix121_121 i) _)
      ⟨121, by decide⟩ ⟨121, by decide⟩ _
      (Q2.validAt ⟨121, by decide⟩ (Q2.listedAt ⟨121, by decide⟩
        (alnCheck_rep ⟨121, by decide⟩ hj hq).1))
      (colE2 ⟨121, by decide⟩ 12 hp) Q2.T121_121_2 Q2.hfix121_121_2 Q2.hinj121_121_2
      Q2.hcardT121_121_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T121_121_2 i) (Q2.hfix121_121_2 i) _)
      colCert_121_121_12.hD ?_).symm
  rw [alnId_121 j hj]


theorem leaf_121_121_13 (hp : 13 < (Q2.transData.getD 121 []).length)
    (j : Nat) (hj : j < (repChars.getD 121 []).length)
    (hq : (normIsRep.getD 121 []).getD j false = true) :
    species (Q2.reps (⟨121, by decide⟩ : Fin 148)) (colE2 ⟨121, by decide⟩ 13 hp)
        (rowE2 (⟨121, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨121, by decide⟩ : Fin 148))
        (colE1 ⟨121, by decide⟩ 13 (transLenTr ⟨121, by decide⟩ 13 hp))
        (rowE1 (⟨121, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨121, by decide⟩ : Fin 148) ⟨121, by decide⟩ _
      (validAt ⟨121, by decide⟩ (listedAt ⟨121, by decide⟩ hj))
      (colE1 ⟨121, by decide⟩ 13 (transLenTr ⟨121, by decide⟩ 13 hp)) T121_121
      hfix121_121 hinj121_121 hcardT121_121
      (fun i => conj_mem_of_fixedPoints _ _ (T121_121 i) (hfix121_121 i) _)
      ⟨121, by decide⟩ ⟨121, by decide⟩ _
      (Q2.validAt ⟨121, by decide⟩ (Q2.listedAt ⟨121, by decide⟩
        (alnCheck_rep ⟨121, by decide⟩ hj hq).1))
      (colE2 ⟨121, by decide⟩ 13 hp) Q2.T121_121_2 Q2.hfix121_121_2 Q2.hinj121_121_2
      Q2.hcardT121_121_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T121_121_2 i) (Q2.hfix121_121_2 i) _)
      colCert_121_121_13.hD ?_).symm
  rw [alnId_121 j hj]


theorem leaf_121_121_14 (hp : 14 < (Q2.transData.getD 121 []).length)
    (j : Nat) (hj : j < (repChars.getD 121 []).length)
    (hq : (normIsRep.getD 121 []).getD j false = true) :
    species (Q2.reps (⟨121, by decide⟩ : Fin 148)) (colE2 ⟨121, by decide⟩ 14 hp)
        (rowE2 (⟨121, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨121, by decide⟩ : Fin 148))
        (colE1 ⟨121, by decide⟩ 14 (transLenTr ⟨121, by decide⟩ 14 hp))
        (rowE1 (⟨121, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨121, by decide⟩ : Fin 148) ⟨121, by decide⟩ _
      (validAt ⟨121, by decide⟩ (listedAt ⟨121, by decide⟩ hj))
      (colE1 ⟨121, by decide⟩ 14 (transLenTr ⟨121, by decide⟩ 14 hp)) T121_121
      hfix121_121 hinj121_121 hcardT121_121
      (fun i => conj_mem_of_fixedPoints _ _ (T121_121 i) (hfix121_121 i) _)
      ⟨121, by decide⟩ ⟨121, by decide⟩ _
      (Q2.validAt ⟨121, by decide⟩ (Q2.listedAt ⟨121, by decide⟩
        (alnCheck_rep ⟨121, by decide⟩ hj hq).1))
      (colE2 ⟨121, by decide⟩ 14 hp) Q2.T121_121_2 Q2.hfix121_121_2 Q2.hinj121_121_2
      Q2.hcardT121_121_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T121_121_2 i) (Q2.hfix121_121_2 i) _)
      colCert_121_121_14.hD ?_).symm
  rw [alnId_121 j hj]


theorem leaf_121_121_15 (hp : 15 < (Q2.transData.getD 121 []).length)
    (j : Nat) (hj : j < (repChars.getD 121 []).length)
    (hq : (normIsRep.getD 121 []).getD j false = true) :
    species (Q2.reps (⟨121, by decide⟩ : Fin 148)) (colE2 ⟨121, by decide⟩ 15 hp)
        (rowE2 (⟨121, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨121, by decide⟩ : Fin 148))
        (colE1 ⟨121, by decide⟩ 15 (transLenTr ⟨121, by decide⟩ 15 hp))
        (rowE1 (⟨121, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨121, by decide⟩ : Fin 148) ⟨121, by decide⟩ _
      (validAt ⟨121, by decide⟩ (listedAt ⟨121, by decide⟩ hj))
      (colE1 ⟨121, by decide⟩ 15 (transLenTr ⟨121, by decide⟩ 15 hp)) T121_121
      hfix121_121 hinj121_121 hcardT121_121
      (fun i => conj_mem_of_fixedPoints _ _ (T121_121 i) (hfix121_121 i) _)
      ⟨121, by decide⟩ ⟨121, by decide⟩ _
      (Q2.validAt ⟨121, by decide⟩ (Q2.listedAt ⟨121, by decide⟩
        (alnCheck_rep ⟨121, by decide⟩ hj hq).1))
      (colE2 ⟨121, by decide⟩ 15 hp) Q2.T121_121_2 Q2.hfix121_121_2 Q2.hinj121_121_2
      Q2.hcardT121_121_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T121_121_2 i) (Q2.hfix121_121_2 i) _)
      colCert_121_121_15.hD ?_).symm
  rw [alnId_121 j hj]


theorem leaf_121_121_16 (hp : 16 < (Q2.transData.getD 121 []).length)
    (j : Nat) (hj : j < (repChars.getD 121 []).length)
    (hq : (normIsRep.getD 121 []).getD j false = true) :
    species (Q2.reps (⟨121, by decide⟩ : Fin 148)) (colE2 ⟨121, by decide⟩ 16 hp)
        (rowE2 (⟨121, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨121, by decide⟩ : Fin 148))
        (colE1 ⟨121, by decide⟩ 16 (transLenTr ⟨121, by decide⟩ 16 hp))
        (rowE1 (⟨121, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨121, by decide⟩ : Fin 148) ⟨121, by decide⟩ _
      (validAt ⟨121, by decide⟩ (listedAt ⟨121, by decide⟩ hj))
      (colE1 ⟨121, by decide⟩ 16 (transLenTr ⟨121, by decide⟩ 16 hp)) T121_121
      hfix121_121 hinj121_121 hcardT121_121
      (fun i => conj_mem_of_fixedPoints _ _ (T121_121 i) (hfix121_121 i) _)
      ⟨121, by decide⟩ ⟨121, by decide⟩ _
      (Q2.validAt ⟨121, by decide⟩ (Q2.listedAt ⟨121, by decide⟩
        (alnCheck_rep ⟨121, by decide⟩ hj hq).1))
      (colE2 ⟨121, by decide⟩ 16 hp) Q2.T121_121_2 Q2.hfix121_121_2 Q2.hinj121_121_2
      Q2.hcardT121_121_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T121_121_2 i) (Q2.hfix121_121_2 i) _)
      colCert_121_121_16.hD ?_).symm
  rw [alnId_121 j hj]


theorem leaf_121_121_17 (hp : 17 < (Q2.transData.getD 121 []).length)
    (j : Nat) (hj : j < (repChars.getD 121 []).length)
    (hq : (normIsRep.getD 121 []).getD j false = true) :
    species (Q2.reps (⟨121, by decide⟩ : Fin 148)) (colE2 ⟨121, by decide⟩ 17 hp)
        (rowE2 (⟨121, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨121, by decide⟩ : Fin 148))
        (colE1 ⟨121, by decide⟩ 17 (transLenTr ⟨121, by decide⟩ 17 hp))
        (rowE1 (⟨121, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨121, by decide⟩ : Fin 148) ⟨121, by decide⟩ _
      (validAt ⟨121, by decide⟩ (listedAt ⟨121, by decide⟩ hj))
      (colE1 ⟨121, by decide⟩ 17 (transLenTr ⟨121, by decide⟩ 17 hp)) T121_121
      hfix121_121 hinj121_121 hcardT121_121
      (fun i => conj_mem_of_fixedPoints _ _ (T121_121 i) (hfix121_121 i) _)
      ⟨121, by decide⟩ ⟨121, by decide⟩ _
      (Q2.validAt ⟨121, by decide⟩ (Q2.listedAt ⟨121, by decide⟩
        (alnCheck_rep ⟨121, by decide⟩ hj hq).1))
      (colE2 ⟨121, by decide⟩ 17 hp) Q2.T121_121_2 Q2.hfix121_121_2 Q2.hinj121_121_2
      Q2.hcardT121_121_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T121_121_2 i) (Q2.hfix121_121_2 i) _)
      colCert_121_121_17.hD ?_).symm
  rw [alnId_121 j hj]


theorem leaf_121_121_18 (hp : 18 < (Q2.transData.getD 121 []).length)
    (j : Nat) (hj : j < (repChars.getD 121 []).length)
    (hq : (normIsRep.getD 121 []).getD j false = true) :
    species (Q2.reps (⟨121, by decide⟩ : Fin 148)) (colE2 ⟨121, by decide⟩ 18 hp)
        (rowE2 (⟨121, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨121, by decide⟩ : Fin 148))
        (colE1 ⟨121, by decide⟩ 18 (transLenTr ⟨121, by decide⟩ 18 hp))
        (rowE1 (⟨121, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨121, by decide⟩ : Fin 148) ⟨121, by decide⟩ _
      (validAt ⟨121, by decide⟩ (listedAt ⟨121, by decide⟩ hj))
      (colE1 ⟨121, by decide⟩ 18 (transLenTr ⟨121, by decide⟩ 18 hp)) T121_121
      hfix121_121 hinj121_121 hcardT121_121
      (fun i => conj_mem_of_fixedPoints _ _ (T121_121 i) (hfix121_121 i) _)
      ⟨121, by decide⟩ ⟨121, by decide⟩ _
      (Q2.validAt ⟨121, by decide⟩ (Q2.listedAt ⟨121, by decide⟩
        (alnCheck_rep ⟨121, by decide⟩ hj hq).1))
      (colE2 ⟨121, by decide⟩ 18 hp) Q2.T121_121_2 Q2.hfix121_121_2 Q2.hinj121_121_2
      Q2.hcardT121_121_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T121_121_2 i) (Q2.hfix121_121_2 i) _)
      colCert_121_121_18.hD ?_).symm
  rw [alnId_121 j hj]


theorem leaf_121_121_19 (hp : 19 < (Q2.transData.getD 121 []).length)
    (j : Nat) (hj : j < (repChars.getD 121 []).length)
    (hq : (normIsRep.getD 121 []).getD j false = true) :
    species (Q2.reps (⟨121, by decide⟩ : Fin 148)) (colE2 ⟨121, by decide⟩ 19 hp)
        (rowE2 (⟨121, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨121, by decide⟩ : Fin 148))
        (colE1 ⟨121, by decide⟩ 19 (transLenTr ⟨121, by decide⟩ 19 hp))
        (rowE1 (⟨121, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨121, by decide⟩ : Fin 148) ⟨121, by decide⟩ _
      (validAt ⟨121, by decide⟩ (listedAt ⟨121, by decide⟩ hj))
      (colE1 ⟨121, by decide⟩ 19 (transLenTr ⟨121, by decide⟩ 19 hp)) T121_121
      hfix121_121 hinj121_121 hcardT121_121
      (fun i => conj_mem_of_fixedPoints _ _ (T121_121 i) (hfix121_121 i) _)
      ⟨121, by decide⟩ ⟨121, by decide⟩ _
      (Q2.validAt ⟨121, by decide⟩ (Q2.listedAt ⟨121, by decide⟩
        (alnCheck_rep ⟨121, by decide⟩ hj hq).1))
      (colE2 ⟨121, by decide⟩ 19 hp) Q2.T121_121_2 Q2.hfix121_121_2 Q2.hinj121_121_2
      Q2.hcardT121_121_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T121_121_2 i) (Q2.hfix121_121_2 i) _)
      colCert_121_121_19.hD ?_).symm
  rw [alnId_121 j hj]


theorem leaf_121_121_20 (hp : 20 < (Q2.transData.getD 121 []).length)
    (j : Nat) (hj : j < (repChars.getD 121 []).length)
    (hq : (normIsRep.getD 121 []).getD j false = true) :
    species (Q2.reps (⟨121, by decide⟩ : Fin 148)) (colE2 ⟨121, by decide⟩ 20 hp)
        (rowE2 (⟨121, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨121, by decide⟩ : Fin 148))
        (colE1 ⟨121, by decide⟩ 20 (transLenTr ⟨121, by decide⟩ 20 hp))
        (rowE1 (⟨121, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨121, by decide⟩ : Fin 148) ⟨121, by decide⟩ _
      (validAt ⟨121, by decide⟩ (listedAt ⟨121, by decide⟩ hj))
      (colE1 ⟨121, by decide⟩ 20 (transLenTr ⟨121, by decide⟩ 20 hp)) T121_121
      hfix121_121 hinj121_121 hcardT121_121
      (fun i => conj_mem_of_fixedPoints _ _ (T121_121 i) (hfix121_121 i) _)
      ⟨121, by decide⟩ ⟨121, by decide⟩ _
      (Q2.validAt ⟨121, by decide⟩ (Q2.listedAt ⟨121, by decide⟩
        (alnCheck_rep ⟨121, by decide⟩ hj hq).1))
      (colE2 ⟨121, by decide⟩ 20 hp) Q2.T121_121_2 Q2.hfix121_121_2 Q2.hinj121_121_2
      Q2.hcardT121_121_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T121_121_2 i) (Q2.hfix121_121_2 i) _)
      colCert_121_121_20.hD ?_).symm
  rw [alnId_121 j hj]


theorem leaf_121_121_21 (hp : 21 < (Q2.transData.getD 121 []).length)
    (j : Nat) (hj : j < (repChars.getD 121 []).length)
    (hq : (normIsRep.getD 121 []).getD j false = true) :
    species (Q2.reps (⟨121, by decide⟩ : Fin 148)) (colE2 ⟨121, by decide⟩ 21 hp)
        (rowE2 (⟨121, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨121, by decide⟩ : Fin 148))
        (colE1 ⟨121, by decide⟩ 21 (transLenTr ⟨121, by decide⟩ 21 hp))
        (rowE1 (⟨121, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨121, by decide⟩ : Fin 148) ⟨121, by decide⟩ _
      (validAt ⟨121, by decide⟩ (listedAt ⟨121, by decide⟩ hj))
      (colE1 ⟨121, by decide⟩ 21 (transLenTr ⟨121, by decide⟩ 21 hp)) T121_121
      hfix121_121 hinj121_121 hcardT121_121
      (fun i => conj_mem_of_fixedPoints _ _ (T121_121 i) (hfix121_121 i) _)
      ⟨121, by decide⟩ ⟨121, by decide⟩ _
      (Q2.validAt ⟨121, by decide⟩ (Q2.listedAt ⟨121, by decide⟩
        (alnCheck_rep ⟨121, by decide⟩ hj hq).1))
      (colE2 ⟨121, by decide⟩ 21 hp) Q2.T121_121_2 Q2.hfix121_121_2 Q2.hinj121_121_2
      Q2.hcardT121_121_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T121_121_2 i) (Q2.hfix121_121_2 i) _)
      colCert_121_121_21.hD ?_).symm
  rw [alnId_121 j hj]


theorem leaf_121_121_22 (hp : 22 < (Q2.transData.getD 121 []).length)
    (j : Nat) (hj : j < (repChars.getD 121 []).length)
    (hq : (normIsRep.getD 121 []).getD j false = true) :
    species (Q2.reps (⟨121, by decide⟩ : Fin 148)) (colE2 ⟨121, by decide⟩ 22 hp)
        (rowE2 (⟨121, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨121, by decide⟩ : Fin 148))
        (colE1 ⟨121, by decide⟩ 22 (transLenTr ⟨121, by decide⟩ 22 hp))
        (rowE1 (⟨121, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨121, by decide⟩ : Fin 148) ⟨121, by decide⟩ _
      (validAt ⟨121, by decide⟩ (listedAt ⟨121, by decide⟩ hj))
      (colE1 ⟨121, by decide⟩ 22 (transLenTr ⟨121, by decide⟩ 22 hp)) T121_121
      hfix121_121 hinj121_121 hcardT121_121
      (fun i => conj_mem_of_fixedPoints _ _ (T121_121 i) (hfix121_121 i) _)
      ⟨121, by decide⟩ ⟨121, by decide⟩ _
      (Q2.validAt ⟨121, by decide⟩ (Q2.listedAt ⟨121, by decide⟩
        (alnCheck_rep ⟨121, by decide⟩ hj hq).1))
      (colE2 ⟨121, by decide⟩ 22 hp) Q2.T121_121_2 Q2.hfix121_121_2 Q2.hinj121_121_2
      Q2.hcardT121_121_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T121_121_2 i) (Q2.hfix121_121_2 i) _)
      colCert_121_121_22.hD ?_).symm
  rw [alnId_121 j hj]


theorem leaf_121_121_23 (hp : 23 < (Q2.transData.getD 121 []).length)
    (j : Nat) (hj : j < (repChars.getD 121 []).length)
    (hq : (normIsRep.getD 121 []).getD j false = true) :
    species (Q2.reps (⟨121, by decide⟩ : Fin 148)) (colE2 ⟨121, by decide⟩ 23 hp)
        (rowE2 (⟨121, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨121, by decide⟩ : Fin 148))
        (colE1 ⟨121, by decide⟩ 23 (transLenTr ⟨121, by decide⟩ 23 hp))
        (rowE1 (⟨121, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨121, by decide⟩ : Fin 148) ⟨121, by decide⟩ _
      (validAt ⟨121, by decide⟩ (listedAt ⟨121, by decide⟩ hj))
      (colE1 ⟨121, by decide⟩ 23 (transLenTr ⟨121, by decide⟩ 23 hp)) T121_121
      hfix121_121 hinj121_121 hcardT121_121
      (fun i => conj_mem_of_fixedPoints _ _ (T121_121 i) (hfix121_121 i) _)
      ⟨121, by decide⟩ ⟨121, by decide⟩ _
      (Q2.validAt ⟨121, by decide⟩ (Q2.listedAt ⟨121, by decide⟩
        (alnCheck_rep ⟨121, by decide⟩ hj hq).1))
      (colE2 ⟨121, by decide⟩ 23 hp) Q2.T121_121_2 Q2.hfix121_121_2 Q2.hinj121_121_2
      Q2.hcardT121_121_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T121_121_2 i) (Q2.hfix121_121_2 i) _)
      colCert_121_121_23.hD ?_).symm
  rw [alnId_121 j hj]


theorem leaf_121_121_24 (hp : 24 < (Q2.transData.getD 121 []).length)
    (j : Nat) (hj : j < (repChars.getD 121 []).length)
    (hq : (normIsRep.getD 121 []).getD j false = true) :
    species (Q2.reps (⟨121, by decide⟩ : Fin 148)) (colE2 ⟨121, by decide⟩ 24 hp)
        (rowE2 (⟨121, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨121, by decide⟩ : Fin 148))
        (colE1 ⟨121, by decide⟩ 24 (transLenTr ⟨121, by decide⟩ 24 hp))
        (rowE1 (⟨121, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨121, by decide⟩ : Fin 148) ⟨121, by decide⟩ _
      (validAt ⟨121, by decide⟩ (listedAt ⟨121, by decide⟩ hj))
      (colE1 ⟨121, by decide⟩ 24 (transLenTr ⟨121, by decide⟩ 24 hp)) T121_121
      hfix121_121 hinj121_121 hcardT121_121
      (fun i => conj_mem_of_fixedPoints _ _ (T121_121 i) (hfix121_121 i) _)
      ⟨121, by decide⟩ ⟨121, by decide⟩ _
      (Q2.validAt ⟨121, by decide⟩ (Q2.listedAt ⟨121, by decide⟩
        (alnCheck_rep ⟨121, by decide⟩ hj hq).1))
      (colE2 ⟨121, by decide⟩ 24 hp) Q2.T121_121_2 Q2.hfix121_121_2 Q2.hinj121_121_2
      Q2.hcardT121_121_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T121_121_2 i) (Q2.hfix121_121_2 i) _)
      colCert_121_121_24.hD ?_).symm
  rw [alnId_121 j hj]


theorem leaf_122_2_0 (hp : 0 < (Q2.transData.getD 2 []).length)
    (j : Nat) (hj : j < (repChars.getD 122 []).length)
    (hq : (normIsRep.getD 122 []).getD j false = true) :
    species (Q2.reps (⟨2, by decide⟩ : Fin 148)) (colE2 ⟨2, by decide⟩ 0 hp)
        (rowE2 (⟨122, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨2, by decide⟩ : Fin 148))
        (colE1 ⟨2, by decide⟩ 0 (transLenTr ⟨2, by decide⟩ 0 hp))
        (rowE1 (⟨122, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨122, by decide⟩ : Fin 148) ⟨2, by decide⟩ _
      (validAt ⟨122, by decide⟩ (listedAt ⟨122, by decide⟩ hj))
      (colE1 ⟨2, by decide⟩ 0 (transLenTr ⟨2, by decide⟩ 0 hp)) T122_2
      hfix122_2 hinj122_2 hcardT122_2
      (fun i => conj_mem_of_fixedPoints _ _ (T122_2 i) (hfix122_2 i) _)
      ⟨122, by decide⟩ ⟨2, by decide⟩ _
      (Q2.validAt ⟨122, by decide⟩ (Q2.listedAt ⟨122, by decide⟩
        (alnCheck_rep ⟨122, by decide⟩ hj hq).1))
      (colE2 ⟨2, by decide⟩ 0 hp) Q2.T122_2_2 Q2.hfix122_2_2 Q2.hinj122_2_2
      Q2.hcardT122_2_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T122_2_2 i) (Q2.hfix122_2_2 i) _)
      colCert_122_2_0.hD ?_).symm
  rw [alnId_122 j hj]


theorem leaf_122_2_1 (hp : 1 < (Q2.transData.getD 2 []).length)
    (j : Nat) (hj : j < (repChars.getD 122 []).length)
    (hq : (normIsRep.getD 122 []).getD j false = true) :
    species (Q2.reps (⟨2, by decide⟩ : Fin 148)) (colE2 ⟨2, by decide⟩ 1 hp)
        (rowE2 (⟨122, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨2, by decide⟩ : Fin 148))
        (colE1 ⟨2, by decide⟩ 1 (transLenTr ⟨2, by decide⟩ 1 hp))
        (rowE1 (⟨122, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨122, by decide⟩ : Fin 148) ⟨2, by decide⟩ _
      (validAt ⟨122, by decide⟩ (listedAt ⟨122, by decide⟩ hj))
      (colE1 ⟨2, by decide⟩ 1 (transLenTr ⟨2, by decide⟩ 1 hp)) T122_2
      hfix122_2 hinj122_2 hcardT122_2
      (fun i => conj_mem_of_fixedPoints _ _ (T122_2 i) (hfix122_2 i) _)
      ⟨122, by decide⟩ ⟨2, by decide⟩ _
      (Q2.validAt ⟨122, by decide⟩ (Q2.listedAt ⟨122, by decide⟩
        (alnCheck_rep ⟨122, by decide⟩ hj hq).1))
      (colE2 ⟨2, by decide⟩ 1 hp) Q2.T122_2_2 Q2.hfix122_2_2 Q2.hinj122_2_2
      Q2.hcardT122_2_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T122_2_2 i) (Q2.hfix122_2_2 i) _)
      ?_).symm
  rw [show colData1 (⟨122, by decide⟩ : Fin 148)
        ((colE1 ⟨2, by decide⟩ 1 (transLenTr ⟨2, by decide⟩ 1 hp) : ↥(reps ⟨2, by decide⟩)) : Coordinate 1)
        T122_2 = colFn colCertDiv_122_2_1.D1 (m := 5) from colCertDiv_122_2_1.bind1,
    show colData2 (⟨122, by decide⟩ : Fin 148)
        ((colE2 ⟨2, by decide⟩ 1 hp : ↥(Q2.reps ⟨2, by decide⟩)) : Coordinate 2)
        Q2.T122_2_2 = colFn colCertDiv_122_2_1.D2 (m := 5) from colCertDiv_122_2_1.bind2]
  rw [alnId_122 j hj]
  exact fastcode_of_div ⟨122, by decide⟩ _ _ _
    ((alnId_122 j hj) ▸ Q2.listedAt (⟨122, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨122, by decide⟩ : Fin 148) hj hq).1) colCertDiv_122_2_1_match


theorem leaf_122_2_2 (hp : 2 < (Q2.transData.getD 2 []).length)
    (j : Nat) (hj : j < (repChars.getD 122 []).length)
    (hq : (normIsRep.getD 122 []).getD j false = true) :
    species (Q2.reps (⟨2, by decide⟩ : Fin 148)) (colE2 ⟨2, by decide⟩ 2 hp)
        (rowE2 (⟨122, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨2, by decide⟩ : Fin 148))
        (colE1 ⟨2, by decide⟩ 2 (transLenTr ⟨2, by decide⟩ 2 hp))
        (rowE1 (⟨122, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨122, by decide⟩ : Fin 148) ⟨2, by decide⟩ _
      (validAt ⟨122, by decide⟩ (listedAt ⟨122, by decide⟩ hj))
      (colE1 ⟨2, by decide⟩ 2 (transLenTr ⟨2, by decide⟩ 2 hp)) T122_2
      hfix122_2 hinj122_2 hcardT122_2
      (fun i => conj_mem_of_fixedPoints _ _ (T122_2 i) (hfix122_2 i) _)
      ⟨122, by decide⟩ ⟨2, by decide⟩ _
      (Q2.validAt ⟨122, by decide⟩ (Q2.listedAt ⟨122, by decide⟩
        (alnCheck_rep ⟨122, by decide⟩ hj hq).1))
      (colE2 ⟨2, by decide⟩ 2 hp) Q2.T122_2_2 Q2.hfix122_2_2 Q2.hinj122_2_2
      Q2.hcardT122_2_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T122_2_2 i) (Q2.hfix122_2_2 i) _)
      ?_).symm
  rw [show colData1 (⟨122, by decide⟩ : Fin 148)
        ((colE1 ⟨2, by decide⟩ 2 (transLenTr ⟨2, by decide⟩ 2 hp) : ↥(reps ⟨2, by decide⟩)) : Coordinate 1)
        T122_2 = colFn colCertDiv_122_2_2.D1 (m := 5) from colCertDiv_122_2_2.bind1,
    show colData2 (⟨122, by decide⟩ : Fin 148)
        ((colE2 ⟨2, by decide⟩ 2 hp : ↥(Q2.reps ⟨2, by decide⟩)) : Coordinate 2)
        Q2.T122_2_2 = colFn colCertDiv_122_2_2.D2 (m := 5) from colCertDiv_122_2_2.bind2]
  rw [alnId_122 j hj]
  exact fastcode_of_div ⟨122, by decide⟩ _ _ _
    ((alnId_122 j hj) ▸ Q2.listedAt (⟨122, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨122, by decide⟩ : Fin 148) hj hq).1) colCertDiv_122_2_2_match


theorem leaf_122_2_3 (hp : 3 < (Q2.transData.getD 2 []).length)
    (j : Nat) (hj : j < (repChars.getD 122 []).length)
    (hq : (normIsRep.getD 122 []).getD j false = true) :
    species (Q2.reps (⟨2, by decide⟩ : Fin 148)) (colE2 ⟨2, by decide⟩ 3 hp)
        (rowE2 (⟨122, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨2, by decide⟩ : Fin 148))
        (colE1 ⟨2, by decide⟩ 3 (transLenTr ⟨2, by decide⟩ 3 hp))
        (rowE1 (⟨122, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨122, by decide⟩ : Fin 148) ⟨2, by decide⟩ _
      (validAt ⟨122, by decide⟩ (listedAt ⟨122, by decide⟩ hj))
      (colE1 ⟨2, by decide⟩ 3 (transLenTr ⟨2, by decide⟩ 3 hp)) T122_2
      hfix122_2 hinj122_2 hcardT122_2
      (fun i => conj_mem_of_fixedPoints _ _ (T122_2 i) (hfix122_2 i) _)
      ⟨122, by decide⟩ ⟨2, by decide⟩ _
      (Q2.validAt ⟨122, by decide⟩ (Q2.listedAt ⟨122, by decide⟩
        (alnCheck_rep ⟨122, by decide⟩ hj hq).1))
      (colE2 ⟨2, by decide⟩ 3 hp) Q2.T122_2_2 Q2.hfix122_2_2 Q2.hinj122_2_2
      Q2.hcardT122_2_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T122_2_2 i) (Q2.hfix122_2_2 i) _)
      ?_).symm
  rw [show colData1 (⟨122, by decide⟩ : Fin 148)
        ((colE1 ⟨2, by decide⟩ 3 (transLenTr ⟨2, by decide⟩ 3 hp) : ↥(reps ⟨2, by decide⟩)) : Coordinate 1)
        T122_2 = colFn colCertDiv_122_2_3.D1 (m := 5) from colCertDiv_122_2_3.bind1,
    show colData2 (⟨122, by decide⟩ : Fin 148)
        ((colE2 ⟨2, by decide⟩ 3 hp : ↥(Q2.reps ⟨2, by decide⟩)) : Coordinate 2)
        Q2.T122_2_2 = colFn colCertDiv_122_2_3.D2 (m := 5) from colCertDiv_122_2_3.bind2]
  rw [alnId_122 j hj]
  exact fastcode_of_div ⟨122, by decide⟩ _ _ _
    ((alnId_122 j hj) ▸ Q2.listedAt (⟨122, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨122, by decide⟩ : Fin 148) hj hq).1) colCertDiv_122_2_3_match


theorem leaf_122_2_4 (hp : 4 < (Q2.transData.getD 2 []).length)
    (j : Nat) (hj : j < (repChars.getD 122 []).length)
    (hq : (normIsRep.getD 122 []).getD j false = true) :
    species (Q2.reps (⟨2, by decide⟩ : Fin 148)) (colE2 ⟨2, by decide⟩ 4 hp)
        (rowE2 (⟨122, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨2, by decide⟩ : Fin 148))
        (colE1 ⟨2, by decide⟩ 4 (transLenTr ⟨2, by decide⟩ 4 hp))
        (rowE1 (⟨122, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨122, by decide⟩ : Fin 148) ⟨2, by decide⟩ _
      (validAt ⟨122, by decide⟩ (listedAt ⟨122, by decide⟩ hj))
      (colE1 ⟨2, by decide⟩ 4 (transLenTr ⟨2, by decide⟩ 4 hp)) T122_2
      hfix122_2 hinj122_2 hcardT122_2
      (fun i => conj_mem_of_fixedPoints _ _ (T122_2 i) (hfix122_2 i) _)
      ⟨122, by decide⟩ ⟨2, by decide⟩ _
      (Q2.validAt ⟨122, by decide⟩ (Q2.listedAt ⟨122, by decide⟩
        (alnCheck_rep ⟨122, by decide⟩ hj hq).1))
      (colE2 ⟨2, by decide⟩ 4 hp) Q2.T122_2_2 Q2.hfix122_2_2 Q2.hinj122_2_2
      Q2.hcardT122_2_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T122_2_2 i) (Q2.hfix122_2_2 i) _)
      ?_).symm
  rw [show colData1 (⟨122, by decide⟩ : Fin 148)
        ((colE1 ⟨2, by decide⟩ 4 (transLenTr ⟨2, by decide⟩ 4 hp) : ↥(reps ⟨2, by decide⟩)) : Coordinate 1)
        T122_2 = colFn colCertDiv_122_2_4.D1 (m := 5) from colCertDiv_122_2_4.bind1,
    show colData2 (⟨122, by decide⟩ : Fin 148)
        ((colE2 ⟨2, by decide⟩ 4 hp : ↥(Q2.reps ⟨2, by decide⟩)) : Coordinate 2)
        Q2.T122_2_2 = colFn colCertDiv_122_2_4.D2 (m := 5) from colCertDiv_122_2_4.bind2]
  rw [alnId_122 j hj]
  exact fastcode_of_div ⟨122, by decide⟩ _ _ _
    ((alnId_122 j hj) ▸ Q2.listedAt (⟨122, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨122, by decide⟩ : Fin 148) hj hq).1) colCertDiv_122_2_4_match


theorem leaf_122_10_0 (hp : 0 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 122 []).length)
    (hq : (normIsRep.getD 122 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 0 hp)
        (rowE2 (⟨122, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 0 (transLenTr ⟨10, by decide⟩ 0 hp))
        (rowE1 (⟨122, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨122, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨122, by decide⟩ (listedAt ⟨122, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 0 (transLenTr ⟨10, by decide⟩ 0 hp)) T122_10
      hfix122_10 hinj122_10 hcardT122_10
      (fun i => conj_mem_of_fixedPoints _ _ (T122_10 i) (hfix122_10 i) _)
      ⟨122, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨122, by decide⟩ (Q2.listedAt ⟨122, by decide⟩
        (alnCheck_rep ⟨122, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 0 hp) Q2.T122_10_2 Q2.hfix122_10_2 Q2.hinj122_10_2
      Q2.hcardT122_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T122_10_2 i) (Q2.hfix122_10_2 i) _)
      colCert_122_10_0.hD ?_).symm
  rw [alnId_122 j hj]


theorem leaf_122_10_1 (hp : 1 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 122 []).length)
    (hq : (normIsRep.getD 122 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 1 hp)
        (rowE2 (⟨122, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 1 (transLenTr ⟨10, by decide⟩ 1 hp))
        (rowE1 (⟨122, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨122, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨122, by decide⟩ (listedAt ⟨122, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 1 (transLenTr ⟨10, by decide⟩ 1 hp)) T122_10
      hfix122_10 hinj122_10 hcardT122_10
      (fun i => conj_mem_of_fixedPoints _ _ (T122_10 i) (hfix122_10 i) _)
      ⟨122, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨122, by decide⟩ (Q2.listedAt ⟨122, by decide⟩
        (alnCheck_rep ⟨122, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 1 hp) Q2.T122_10_2 Q2.hfix122_10_2 Q2.hinj122_10_2
      Q2.hcardT122_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T122_10_2 i) (Q2.hfix122_10_2 i) _)
      colCert_122_10_1.hD ?_).symm
  rw [alnId_122 j hj]


theorem leaf_122_10_2 (hp : 2 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 122 []).length)
    (hq : (normIsRep.getD 122 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 2 hp)
        (rowE2 (⟨122, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 2 (transLenTr ⟨10, by decide⟩ 2 hp))
        (rowE1 (⟨122, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨122, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨122, by decide⟩ (listedAt ⟨122, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 2 (transLenTr ⟨10, by decide⟩ 2 hp)) T122_10
      hfix122_10 hinj122_10 hcardT122_10
      (fun i => conj_mem_of_fixedPoints _ _ (T122_10 i) (hfix122_10 i) _)
      ⟨122, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨122, by decide⟩ (Q2.listedAt ⟨122, by decide⟩
        (alnCheck_rep ⟨122, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 2 hp) Q2.T122_10_2 Q2.hfix122_10_2 Q2.hinj122_10_2
      Q2.hcardT122_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T122_10_2 i) (Q2.hfix122_10_2 i) _)
      colCert_122_10_2.hD ?_).symm
  rw [alnId_122 j hj]


theorem leaf_122_10_3 (hp : 3 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 122 []).length)
    (hq : (normIsRep.getD 122 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 3 hp)
        (rowE2 (⟨122, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 3 (transLenTr ⟨10, by decide⟩ 3 hp))
        (rowE1 (⟨122, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨122, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨122, by decide⟩ (listedAt ⟨122, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 3 (transLenTr ⟨10, by decide⟩ 3 hp)) T122_10
      hfix122_10 hinj122_10 hcardT122_10
      (fun i => conj_mem_of_fixedPoints _ _ (T122_10 i) (hfix122_10 i) _)
      ⟨122, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨122, by decide⟩ (Q2.listedAt ⟨122, by decide⟩
        (alnCheck_rep ⟨122, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 3 hp) Q2.T122_10_2 Q2.hfix122_10_2 Q2.hinj122_10_2
      Q2.hcardT122_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T122_10_2 i) (Q2.hfix122_10_2 i) _)
      colCert_122_10_3.hD ?_).symm
  rw [alnId_122 j hj]


theorem leaf_122_10_4 (hp : 4 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 122 []).length)
    (hq : (normIsRep.getD 122 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 4 hp)
        (rowE2 (⟨122, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 4 (transLenTr ⟨10, by decide⟩ 4 hp))
        (rowE1 (⟨122, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨122, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨122, by decide⟩ (listedAt ⟨122, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 4 (transLenTr ⟨10, by decide⟩ 4 hp)) T122_10
      hfix122_10 hinj122_10 hcardT122_10
      (fun i => conj_mem_of_fixedPoints _ _ (T122_10 i) (hfix122_10 i) _)
      ⟨122, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨122, by decide⟩ (Q2.listedAt ⟨122, by decide⟩
        (alnCheck_rep ⟨122, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 4 hp) Q2.T122_10_2 Q2.hfix122_10_2 Q2.hinj122_10_2
      Q2.hcardT122_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T122_10_2 i) (Q2.hfix122_10_2 i) _)
      colCert_122_10_4.hD ?_).symm
  rw [alnId_122 j hj]


theorem leaf_122_12_0 (hp : 0 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 122 []).length)
    (hq : (normIsRep.getD 122 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 0 hp)
        (rowE2 (⟨122, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp))
        (rowE1 (⟨122, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨122, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨122, by decide⟩ (listedAt ⟨122, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp)) T122_12
      hfix122_12 hinj122_12 hcardT122_12
      (fun i => conj_mem_of_fixedPoints _ _ (T122_12 i) (hfix122_12 i) _)
      ⟨122, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨122, by decide⟩ (Q2.listedAt ⟨122, by decide⟩
        (alnCheck_rep ⟨122, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 0 hp) Q2.T122_12_2 Q2.hfix122_12_2 Q2.hinj122_12_2
      Q2.hcardT122_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T122_12_2 i) (Q2.hfix122_12_2 i) _)
      colCert_122_12_0.hD ?_).symm
  rw [alnId_122 j hj]


theorem leaf_122_12_1 (hp : 1 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 122 []).length)
    (hq : (normIsRep.getD 122 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 1 hp)
        (rowE2 (⟨122, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp))
        (rowE1 (⟨122, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨122, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨122, by decide⟩ (listedAt ⟨122, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp)) T122_12
      hfix122_12 hinj122_12 hcardT122_12
      (fun i => conj_mem_of_fixedPoints _ _ (T122_12 i) (hfix122_12 i) _)
      ⟨122, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨122, by decide⟩ (Q2.listedAt ⟨122, by decide⟩
        (alnCheck_rep ⟨122, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 1 hp) Q2.T122_12_2 Q2.hfix122_12_2 Q2.hinj122_12_2
      Q2.hcardT122_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T122_12_2 i) (Q2.hfix122_12_2 i) _)
      colCert_122_12_1.hD ?_).symm
  rw [alnId_122 j hj]


theorem leaf_122_12_2 (hp : 2 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 122 []).length)
    (hq : (normIsRep.getD 122 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 2 hp)
        (rowE2 (⟨122, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp))
        (rowE1 (⟨122, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨122, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨122, by decide⟩ (listedAt ⟨122, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp)) T122_12
      hfix122_12 hinj122_12 hcardT122_12
      (fun i => conj_mem_of_fixedPoints _ _ (T122_12 i) (hfix122_12 i) _)
      ⟨122, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨122, by decide⟩ (Q2.listedAt ⟨122, by decide⟩
        (alnCheck_rep ⟨122, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 2 hp) Q2.T122_12_2 Q2.hfix122_12_2 Q2.hinj122_12_2
      Q2.hcardT122_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T122_12_2 i) (Q2.hfix122_12_2 i) _)
      colCert_122_12_2.hD ?_).symm
  rw [alnId_122 j hj]


theorem leaf_122_12_3 (hp : 3 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 122 []).length)
    (hq : (normIsRep.getD 122 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 3 hp)
        (rowE2 (⟨122, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp))
        (rowE1 (⟨122, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨122, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨122, by decide⟩ (listedAt ⟨122, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp)) T122_12
      hfix122_12 hinj122_12 hcardT122_12
      (fun i => conj_mem_of_fixedPoints _ _ (T122_12 i) (hfix122_12 i) _)
      ⟨122, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨122, by decide⟩ (Q2.listedAt ⟨122, by decide⟩
        (alnCheck_rep ⟨122, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 3 hp) Q2.T122_12_2 Q2.hfix122_12_2 Q2.hinj122_12_2
      Q2.hcardT122_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T122_12_2 i) (Q2.hfix122_12_2 i) _)
      colCert_122_12_3.hD ?_).symm
  rw [alnId_122 j hj]


theorem leaf_122_12_4 (hp : 4 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 122 []).length)
    (hq : (normIsRep.getD 122 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 4 hp)
        (rowE2 (⟨122, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp))
        (rowE1 (⟨122, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨122, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨122, by decide⟩ (listedAt ⟨122, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp)) T122_12
      hfix122_12 hinj122_12 hcardT122_12
      (fun i => conj_mem_of_fixedPoints _ _ (T122_12 i) (hfix122_12 i) _)
      ⟨122, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨122, by decide⟩ (Q2.listedAt ⟨122, by decide⟩
        (alnCheck_rep ⟨122, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 4 hp) Q2.T122_12_2 Q2.hfix122_12_2 Q2.hinj122_12_2
      Q2.hcardT122_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T122_12_2 i) (Q2.hfix122_12_2 i) _)
      colCert_122_12_4.hD ?_).symm
  rw [alnId_122 j hj]


theorem leaf_122_20_0 (hp : 0 < (Q2.transData.getD 20 []).length)
    (j : Nat) (hj : j < (repChars.getD 122 []).length)
    (hq : (normIsRep.getD 122 []).getD j false = true) :
    species (Q2.reps (⟨20, by decide⟩ : Fin 148)) (colE2 ⟨20, by decide⟩ 0 hp)
        (rowE2 (⟨122, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨20, by decide⟩ : Fin 148))
        (colE1 ⟨20, by decide⟩ 0 (transLenTr ⟨20, by decide⟩ 0 hp))
        (rowE1 (⟨122, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨122, by decide⟩ : Fin 148) ⟨20, by decide⟩ _
      (validAt ⟨122, by decide⟩ (listedAt ⟨122, by decide⟩ hj))
      (colE1 ⟨20, by decide⟩ 0 (transLenTr ⟨20, by decide⟩ 0 hp)) T122_20
      hfix122_20 hinj122_20 hcardT122_20
      (fun i => conj_mem_of_fixedPoints _ _ (T122_20 i) (hfix122_20 i) _)
      ⟨122, by decide⟩ ⟨20, by decide⟩ _
      (Q2.validAt ⟨122, by decide⟩ (Q2.listedAt ⟨122, by decide⟩
        (alnCheck_rep ⟨122, by decide⟩ hj hq).1))
      (colE2 ⟨20, by decide⟩ 0 hp) Q2.T122_20_2 Q2.hfix122_20_2 Q2.hinj122_20_2
      Q2.hcardT122_20_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T122_20_2 i) (Q2.hfix122_20_2 i) _)
      colCert_122_20_0.hD ?_).symm
  rw [alnId_122 j hj]


theorem leaf_122_20_1 (hp : 1 < (Q2.transData.getD 20 []).length)
    (j : Nat) (hj : j < (repChars.getD 122 []).length)
    (hq : (normIsRep.getD 122 []).getD j false = true) :
    species (Q2.reps (⟨20, by decide⟩ : Fin 148)) (colE2 ⟨20, by decide⟩ 1 hp)
        (rowE2 (⟨122, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨20, by decide⟩ : Fin 148))
        (colE1 ⟨20, by decide⟩ 1 (transLenTr ⟨20, by decide⟩ 1 hp))
        (rowE1 (⟨122, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨122, by decide⟩ : Fin 148) ⟨20, by decide⟩ _
      (validAt ⟨122, by decide⟩ (listedAt ⟨122, by decide⟩ hj))
      (colE1 ⟨20, by decide⟩ 1 (transLenTr ⟨20, by decide⟩ 1 hp)) T122_20
      hfix122_20 hinj122_20 hcardT122_20
      (fun i => conj_mem_of_fixedPoints _ _ (T122_20 i) (hfix122_20 i) _)
      ⟨122, by decide⟩ ⟨20, by decide⟩ _
      (Q2.validAt ⟨122, by decide⟩ (Q2.listedAt ⟨122, by decide⟩
        (alnCheck_rep ⟨122, by decide⟩ hj hq).1))
      (colE2 ⟨20, by decide⟩ 1 hp) Q2.T122_20_2 Q2.hfix122_20_2 Q2.hinj122_20_2
      Q2.hcardT122_20_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T122_20_2 i) (Q2.hfix122_20_2 i) _)
      colCert_122_20_1.hD ?_).symm
  rw [alnId_122 j hj]


theorem leaf_122_20_2 (hp : 2 < (Q2.transData.getD 20 []).length)
    (j : Nat) (hj : j < (repChars.getD 122 []).length)
    (hq : (normIsRep.getD 122 []).getD j false = true) :
    species (Q2.reps (⟨20, by decide⟩ : Fin 148)) (colE2 ⟨20, by decide⟩ 2 hp)
        (rowE2 (⟨122, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨20, by decide⟩ : Fin 148))
        (colE1 ⟨20, by decide⟩ 2 (transLenTr ⟨20, by decide⟩ 2 hp))
        (rowE1 (⟨122, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨122, by decide⟩ : Fin 148) ⟨20, by decide⟩ _
      (validAt ⟨122, by decide⟩ (listedAt ⟨122, by decide⟩ hj))
      (colE1 ⟨20, by decide⟩ 2 (transLenTr ⟨20, by decide⟩ 2 hp)) T122_20
      hfix122_20 hinj122_20 hcardT122_20
      (fun i => conj_mem_of_fixedPoints _ _ (T122_20 i) (hfix122_20 i) _)
      ⟨122, by decide⟩ ⟨20, by decide⟩ _
      (Q2.validAt ⟨122, by decide⟩ (Q2.listedAt ⟨122, by decide⟩
        (alnCheck_rep ⟨122, by decide⟩ hj hq).1))
      (colE2 ⟨20, by decide⟩ 2 hp) Q2.T122_20_2 Q2.hfix122_20_2 Q2.hinj122_20_2
      Q2.hcardT122_20_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T122_20_2 i) (Q2.hfix122_20_2 i) _)
      colCert_122_20_2.hD ?_).symm
  rw [alnId_122 j hj]


theorem leaf_122_20_3 (hp : 3 < (Q2.transData.getD 20 []).length)
    (j : Nat) (hj : j < (repChars.getD 122 []).length)
    (hq : (normIsRep.getD 122 []).getD j false = true) :
    species (Q2.reps (⟨20, by decide⟩ : Fin 148)) (colE2 ⟨20, by decide⟩ 3 hp)
        (rowE2 (⟨122, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨20, by decide⟩ : Fin 148))
        (colE1 ⟨20, by decide⟩ 3 (transLenTr ⟨20, by decide⟩ 3 hp))
        (rowE1 (⟨122, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨122, by decide⟩ : Fin 148) ⟨20, by decide⟩ _
      (validAt ⟨122, by decide⟩ (listedAt ⟨122, by decide⟩ hj))
      (colE1 ⟨20, by decide⟩ 3 (transLenTr ⟨20, by decide⟩ 3 hp)) T122_20
      hfix122_20 hinj122_20 hcardT122_20
      (fun i => conj_mem_of_fixedPoints _ _ (T122_20 i) (hfix122_20 i) _)
      ⟨122, by decide⟩ ⟨20, by decide⟩ _
      (Q2.validAt ⟨122, by decide⟩ (Q2.listedAt ⟨122, by decide⟩
        (alnCheck_rep ⟨122, by decide⟩ hj hq).1))
      (colE2 ⟨20, by decide⟩ 3 hp) Q2.T122_20_2 Q2.hfix122_20_2 Q2.hinj122_20_2
      Q2.hcardT122_20_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T122_20_2 i) (Q2.hfix122_20_2 i) _)
      colCert_122_20_3.hD ?_).symm
  rw [alnId_122 j hj]


theorem leaf_122_20_4 (hp : 4 < (Q2.transData.getD 20 []).length)
    (j : Nat) (hj : j < (repChars.getD 122 []).length)
    (hq : (normIsRep.getD 122 []).getD j false = true) :
    species (Q2.reps (⟨20, by decide⟩ : Fin 148)) (colE2 ⟨20, by decide⟩ 4 hp)
        (rowE2 (⟨122, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨20, by decide⟩ : Fin 148))
        (colE1 ⟨20, by decide⟩ 4 (transLenTr ⟨20, by decide⟩ 4 hp))
        (rowE1 (⟨122, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨122, by decide⟩ : Fin 148) ⟨20, by decide⟩ _
      (validAt ⟨122, by decide⟩ (listedAt ⟨122, by decide⟩ hj))
      (colE1 ⟨20, by decide⟩ 4 (transLenTr ⟨20, by decide⟩ 4 hp)) T122_20
      hfix122_20 hinj122_20 hcardT122_20
      (fun i => conj_mem_of_fixedPoints _ _ (T122_20 i) (hfix122_20 i) _)
      ⟨122, by decide⟩ ⟨20, by decide⟩ _
      (Q2.validAt ⟨122, by decide⟩ (Q2.listedAt ⟨122, by decide⟩
        (alnCheck_rep ⟨122, by decide⟩ hj hq).1))
      (colE2 ⟨20, by decide⟩ 4 hp) Q2.T122_20_2 Q2.hfix122_20_2 Q2.hinj122_20_2
      Q2.hcardT122_20_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T122_20_2 i) (Q2.hfix122_20_2 i) _)
      colCert_122_20_4.hD ?_).symm
  rw [alnId_122 j hj]


theorem leaf_122_20_5 (hp : 5 < (Q2.transData.getD 20 []).length)
    (j : Nat) (hj : j < (repChars.getD 122 []).length)
    (hq : (normIsRep.getD 122 []).getD j false = true) :
    species (Q2.reps (⟨20, by decide⟩ : Fin 148)) (colE2 ⟨20, by decide⟩ 5 hp)
        (rowE2 (⟨122, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨20, by decide⟩ : Fin 148))
        (colE1 ⟨20, by decide⟩ 5 (transLenTr ⟨20, by decide⟩ 5 hp))
        (rowE1 (⟨122, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨122, by decide⟩ : Fin 148) ⟨20, by decide⟩ _
      (validAt ⟨122, by decide⟩ (listedAt ⟨122, by decide⟩ hj))
      (colE1 ⟨20, by decide⟩ 5 (transLenTr ⟨20, by decide⟩ 5 hp)) T122_20
      hfix122_20 hinj122_20 hcardT122_20
      (fun i => conj_mem_of_fixedPoints _ _ (T122_20 i) (hfix122_20 i) _)
      ⟨122, by decide⟩ ⟨20, by decide⟩ _
      (Q2.validAt ⟨122, by decide⟩ (Q2.listedAt ⟨122, by decide⟩
        (alnCheck_rep ⟨122, by decide⟩ hj hq).1))
      (colE2 ⟨20, by decide⟩ 5 hp) Q2.T122_20_2 Q2.hfix122_20_2 Q2.hinj122_20_2
      Q2.hcardT122_20_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T122_20_2 i) (Q2.hfix122_20_2 i) _)
      ?_).symm
  rw [show colData1 (⟨122, by decide⟩ : Fin 148)
        ((colE1 ⟨20, by decide⟩ 5 (transLenTr ⟨20, by decide⟩ 5 hp) : ↥(reps ⟨20, by decide⟩)) : Coordinate 1)
        T122_20 = colFn colCertDiv_122_20_5.D1 (m := 5) from colCertDiv_122_20_5.bind1,
    show colData2 (⟨122, by decide⟩ : Fin 148)
        ((colE2 ⟨20, by decide⟩ 5 hp : ↥(Q2.reps ⟨20, by decide⟩)) : Coordinate 2)
        Q2.T122_20_2 = colFn colCertDiv_122_20_5.D2 (m := 5) from colCertDiv_122_20_5.bind2]
  rw [alnId_122 j hj]
  exact fastcode_of_div ⟨122, by decide⟩ _ _ _
    ((alnId_122 j hj) ▸ Q2.listedAt (⟨122, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨122, by decide⟩ : Fin 148) hj hq).1) colCertDiv_122_20_5_match


theorem leaf_122_20_10 (hp : 10 < (Q2.transData.getD 20 []).length)
    (j : Nat) (hj : j < (repChars.getD 122 []).length)
    (hq : (normIsRep.getD 122 []).getD j false = true) :
    species (Q2.reps (⟨20, by decide⟩ : Fin 148)) (colE2 ⟨20, by decide⟩ 10 hp)
        (rowE2 (⟨122, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨20, by decide⟩ : Fin 148))
        (colE1 ⟨20, by decide⟩ 10 (transLenTr ⟨20, by decide⟩ 10 hp))
        (rowE1 (⟨122, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨122, by decide⟩ : Fin 148) ⟨20, by decide⟩ _
      (validAt ⟨122, by decide⟩ (listedAt ⟨122, by decide⟩ hj))
      (colE1 ⟨20, by decide⟩ 10 (transLenTr ⟨20, by decide⟩ 10 hp)) T122_20
      hfix122_20 hinj122_20 hcardT122_20
      (fun i => conj_mem_of_fixedPoints _ _ (T122_20 i) (hfix122_20 i) _)
      ⟨122, by decide⟩ ⟨20, by decide⟩ _
      (Q2.validAt ⟨122, by decide⟩ (Q2.listedAt ⟨122, by decide⟩
        (alnCheck_rep ⟨122, by decide⟩ hj hq).1))
      (colE2 ⟨20, by decide⟩ 10 hp) Q2.T122_20_2 Q2.hfix122_20_2 Q2.hinj122_20_2
      Q2.hcardT122_20_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T122_20_2 i) (Q2.hfix122_20_2 i) _)
      ?_).symm
  rw [show colData1 (⟨122, by decide⟩ : Fin 148)
        ((colE1 ⟨20, by decide⟩ 10 (transLenTr ⟨20, by decide⟩ 10 hp) : ↥(reps ⟨20, by decide⟩)) : Coordinate 1)
        T122_20 = colFn colCertDiv_122_20_10.D1 (m := 5) from colCertDiv_122_20_10.bind1,
    show colData2 (⟨122, by decide⟩ : Fin 148)
        ((colE2 ⟨20, by decide⟩ 10 hp : ↥(Q2.reps ⟨20, by decide⟩)) : Coordinate 2)
        Q2.T122_20_2 = colFn colCertDiv_122_20_10.D2 (m := 5) from colCertDiv_122_20_10.bind2]
  rw [alnId_122 j hj]
  exact fastcode_of_div ⟨122, by decide⟩ _ _ _
    ((alnId_122 j hj) ▸ Q2.listedAt (⟨122, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨122, by decide⟩ : Fin 148) hj hq).1) colCertDiv_122_20_10_match


theorem leaf_122_20_15 (hp : 15 < (Q2.transData.getD 20 []).length)
    (j : Nat) (hj : j < (repChars.getD 122 []).length)
    (hq : (normIsRep.getD 122 []).getD j false = true) :
    species (Q2.reps (⟨20, by decide⟩ : Fin 148)) (colE2 ⟨20, by decide⟩ 15 hp)
        (rowE2 (⟨122, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨20, by decide⟩ : Fin 148))
        (colE1 ⟨20, by decide⟩ 15 (transLenTr ⟨20, by decide⟩ 15 hp))
        (rowE1 (⟨122, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨122, by decide⟩ : Fin 148) ⟨20, by decide⟩ _
      (validAt ⟨122, by decide⟩ (listedAt ⟨122, by decide⟩ hj))
      (colE1 ⟨20, by decide⟩ 15 (transLenTr ⟨20, by decide⟩ 15 hp)) T122_20
      hfix122_20 hinj122_20 hcardT122_20
      (fun i => conj_mem_of_fixedPoints _ _ (T122_20 i) (hfix122_20 i) _)
      ⟨122, by decide⟩ ⟨20, by decide⟩ _
      (Q2.validAt ⟨122, by decide⟩ (Q2.listedAt ⟨122, by decide⟩
        (alnCheck_rep ⟨122, by decide⟩ hj hq).1))
      (colE2 ⟨20, by decide⟩ 15 hp) Q2.T122_20_2 Q2.hfix122_20_2 Q2.hinj122_20_2
      Q2.hcardT122_20_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T122_20_2 i) (Q2.hfix122_20_2 i) _)
      ?_).symm
  rw [show colData1 (⟨122, by decide⟩ : Fin 148)
        ((colE1 ⟨20, by decide⟩ 15 (transLenTr ⟨20, by decide⟩ 15 hp) : ↥(reps ⟨20, by decide⟩)) : Coordinate 1)
        T122_20 = colFn colCertDiv_122_20_15.D1 (m := 5) from colCertDiv_122_20_15.bind1,
    show colData2 (⟨122, by decide⟩ : Fin 148)
        ((colE2 ⟨20, by decide⟩ 15 hp : ↥(Q2.reps ⟨20, by decide⟩)) : Coordinate 2)
        Q2.T122_20_2 = colFn colCertDiv_122_20_15.D2 (m := 5) from colCertDiv_122_20_15.bind2]
  rw [alnId_122 j hj]
  exact fastcode_of_div ⟨122, by decide⟩ _ _ _
    ((alnId_122 j hj) ▸ Q2.listedAt (⟨122, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨122, by decide⟩ : Fin 148) hj hq).1) colCertDiv_122_20_15_match


theorem leaf_122_20_20 (hp : 20 < (Q2.transData.getD 20 []).length)
    (j : Nat) (hj : j < (repChars.getD 122 []).length)
    (hq : (normIsRep.getD 122 []).getD j false = true) :
    species (Q2.reps (⟨20, by decide⟩ : Fin 148)) (colE2 ⟨20, by decide⟩ 20 hp)
        (rowE2 (⟨122, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨20, by decide⟩ : Fin 148))
        (colE1 ⟨20, by decide⟩ 20 (transLenTr ⟨20, by decide⟩ 20 hp))
        (rowE1 (⟨122, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨122, by decide⟩ : Fin 148) ⟨20, by decide⟩ _
      (validAt ⟨122, by decide⟩ (listedAt ⟨122, by decide⟩ hj))
      (colE1 ⟨20, by decide⟩ 20 (transLenTr ⟨20, by decide⟩ 20 hp)) T122_20
      hfix122_20 hinj122_20 hcardT122_20
      (fun i => conj_mem_of_fixedPoints _ _ (T122_20 i) (hfix122_20 i) _)
      ⟨122, by decide⟩ ⟨20, by decide⟩ _
      (Q2.validAt ⟨122, by decide⟩ (Q2.listedAt ⟨122, by decide⟩
        (alnCheck_rep ⟨122, by decide⟩ hj hq).1))
      (colE2 ⟨20, by decide⟩ 20 hp) Q2.T122_20_2 Q2.hfix122_20_2 Q2.hinj122_20_2
      Q2.hcardT122_20_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T122_20_2 i) (Q2.hfix122_20_2 i) _)
      ?_).symm
  rw [show colData1 (⟨122, by decide⟩ : Fin 148)
        ((colE1 ⟨20, by decide⟩ 20 (transLenTr ⟨20, by decide⟩ 20 hp) : ↥(reps ⟨20, by decide⟩)) : Coordinate 1)
        T122_20 = colFn colCertDiv_122_20_20.D1 (m := 5) from colCertDiv_122_20_20.bind1,
    show colData2 (⟨122, by decide⟩ : Fin 148)
        ((colE2 ⟨20, by decide⟩ 20 hp : ↥(Q2.reps ⟨20, by decide⟩)) : Coordinate 2)
        Q2.T122_20_2 = colFn colCertDiv_122_20_20.D2 (m := 5) from colCertDiv_122_20_20.bind2]
  rw [alnId_122 j hj]
  exact fastcode_of_div ⟨122, by decide⟩ _ _ _
    ((alnId_122 j hj) ▸ Q2.listedAt (⟨122, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨122, by decide⟩ : Fin 148) hj hq).1) colCertDiv_122_20_20_match


theorem leaf_122_28_0 (hp : 0 < (Q2.transData.getD 28 []).length)
    (j : Nat) (hj : j < (repChars.getD 122 []).length)
    (hq : (normIsRep.getD 122 []).getD j false = true) :
    species (Q2.reps (⟨28, by decide⟩ : Fin 148)) (colE2 ⟨28, by decide⟩ 0 hp)
        (rowE2 (⟨122, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨28, by decide⟩ : Fin 148))
        (colE1 ⟨28, by decide⟩ 0 (transLenTr ⟨28, by decide⟩ 0 hp))
        (rowE1 (⟨122, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨122, by decide⟩ : Fin 148) ⟨28, by decide⟩ _
      (validAt ⟨122, by decide⟩ (listedAt ⟨122, by decide⟩ hj))
      (colE1 ⟨28, by decide⟩ 0 (transLenTr ⟨28, by decide⟩ 0 hp)) T122_28
      hfix122_28 hinj122_28 hcardT122_28
      (fun i => conj_mem_of_fixedPoints _ _ (T122_28 i) (hfix122_28 i) _)
      ⟨122, by decide⟩ ⟨28, by decide⟩ _
      (Q2.validAt ⟨122, by decide⟩ (Q2.listedAt ⟨122, by decide⟩
        (alnCheck_rep ⟨122, by decide⟩ hj hq).1))
      (colE2 ⟨28, by decide⟩ 0 hp) Q2.T122_28_2 Q2.hfix122_28_2 Q2.hinj122_28_2
      Q2.hcardT122_28_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T122_28_2 i) (Q2.hfix122_28_2 i) _)
      colCert_122_28_0.hD ?_).symm
  rw [alnId_122 j hj]


theorem leaf_122_28_1 (hp : 1 < (Q2.transData.getD 28 []).length)
    (j : Nat) (hj : j < (repChars.getD 122 []).length)
    (hq : (normIsRep.getD 122 []).getD j false = true) :
    species (Q2.reps (⟨28, by decide⟩ : Fin 148)) (colE2 ⟨28, by decide⟩ 1 hp)
        (rowE2 (⟨122, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨28, by decide⟩ : Fin 148))
        (colE1 ⟨28, by decide⟩ 1 (transLenTr ⟨28, by decide⟩ 1 hp))
        (rowE1 (⟨122, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨122, by decide⟩ : Fin 148) ⟨28, by decide⟩ _
      (validAt ⟨122, by decide⟩ (listedAt ⟨122, by decide⟩ hj))
      (colE1 ⟨28, by decide⟩ 1 (transLenTr ⟨28, by decide⟩ 1 hp)) T122_28
      hfix122_28 hinj122_28 hcardT122_28
      (fun i => conj_mem_of_fixedPoints _ _ (T122_28 i) (hfix122_28 i) _)
      ⟨122, by decide⟩ ⟨28, by decide⟩ _
      (Q2.validAt ⟨122, by decide⟩ (Q2.listedAt ⟨122, by decide⟩
        (alnCheck_rep ⟨122, by decide⟩ hj hq).1))
      (colE2 ⟨28, by decide⟩ 1 hp) Q2.T122_28_2 Q2.hfix122_28_2 Q2.hinj122_28_2
      Q2.hcardT122_28_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T122_28_2 i) (Q2.hfix122_28_2 i) _)
      colCert_122_28_1.hD ?_).symm
  rw [alnId_122 j hj]


theorem leaf_122_28_2 (hp : 2 < (Q2.transData.getD 28 []).length)
    (j : Nat) (hj : j < (repChars.getD 122 []).length)
    (hq : (normIsRep.getD 122 []).getD j false = true) :
    species (Q2.reps (⟨28, by decide⟩ : Fin 148)) (colE2 ⟨28, by decide⟩ 2 hp)
        (rowE2 (⟨122, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨28, by decide⟩ : Fin 148))
        (colE1 ⟨28, by decide⟩ 2 (transLenTr ⟨28, by decide⟩ 2 hp))
        (rowE1 (⟨122, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨122, by decide⟩ : Fin 148) ⟨28, by decide⟩ _
      (validAt ⟨122, by decide⟩ (listedAt ⟨122, by decide⟩ hj))
      (colE1 ⟨28, by decide⟩ 2 (transLenTr ⟨28, by decide⟩ 2 hp)) T122_28
      hfix122_28 hinj122_28 hcardT122_28
      (fun i => conj_mem_of_fixedPoints _ _ (T122_28 i) (hfix122_28 i) _)
      ⟨122, by decide⟩ ⟨28, by decide⟩ _
      (Q2.validAt ⟨122, by decide⟩ (Q2.listedAt ⟨122, by decide⟩
        (alnCheck_rep ⟨122, by decide⟩ hj hq).1))
      (colE2 ⟨28, by decide⟩ 2 hp) Q2.T122_28_2 Q2.hfix122_28_2 Q2.hinj122_28_2
      Q2.hcardT122_28_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T122_28_2 i) (Q2.hfix122_28_2 i) _)
      colCert_122_28_2.hD ?_).symm
  rw [alnId_122 j hj]


theorem leaf_122_28_3 (hp : 3 < (Q2.transData.getD 28 []).length)
    (j : Nat) (hj : j < (repChars.getD 122 []).length)
    (hq : (normIsRep.getD 122 []).getD j false = true) :
    species (Q2.reps (⟨28, by decide⟩ : Fin 148)) (colE2 ⟨28, by decide⟩ 3 hp)
        (rowE2 (⟨122, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨28, by decide⟩ : Fin 148))
        (colE1 ⟨28, by decide⟩ 3 (transLenTr ⟨28, by decide⟩ 3 hp))
        (rowE1 (⟨122, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨122, by decide⟩ : Fin 148) ⟨28, by decide⟩ _
      (validAt ⟨122, by decide⟩ (listedAt ⟨122, by decide⟩ hj))
      (colE1 ⟨28, by decide⟩ 3 (transLenTr ⟨28, by decide⟩ 3 hp)) T122_28
      hfix122_28 hinj122_28 hcardT122_28
      (fun i => conj_mem_of_fixedPoints _ _ (T122_28 i) (hfix122_28 i) _)
      ⟨122, by decide⟩ ⟨28, by decide⟩ _
      (Q2.validAt ⟨122, by decide⟩ (Q2.listedAt ⟨122, by decide⟩
        (alnCheck_rep ⟨122, by decide⟩ hj hq).1))
      (colE2 ⟨28, by decide⟩ 3 hp) Q2.T122_28_2 Q2.hfix122_28_2 Q2.hinj122_28_2
      Q2.hcardT122_28_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T122_28_2 i) (Q2.hfix122_28_2 i) _)
      colCert_122_28_3.hD ?_).symm
  rw [alnId_122 j hj]


theorem leaf_122_28_4 (hp : 4 < (Q2.transData.getD 28 []).length)
    (j : Nat) (hj : j < (repChars.getD 122 []).length)
    (hq : (normIsRep.getD 122 []).getD j false = true) :
    species (Q2.reps (⟨28, by decide⟩ : Fin 148)) (colE2 ⟨28, by decide⟩ 4 hp)
        (rowE2 (⟨122, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨28, by decide⟩ : Fin 148))
        (colE1 ⟨28, by decide⟩ 4 (transLenTr ⟨28, by decide⟩ 4 hp))
        (rowE1 (⟨122, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨122, by decide⟩ : Fin 148) ⟨28, by decide⟩ _
      (validAt ⟨122, by decide⟩ (listedAt ⟨122, by decide⟩ hj))
      (colE1 ⟨28, by decide⟩ 4 (transLenTr ⟨28, by decide⟩ 4 hp)) T122_28
      hfix122_28 hinj122_28 hcardT122_28
      (fun i => conj_mem_of_fixedPoints _ _ (T122_28 i) (hfix122_28 i) _)
      ⟨122, by decide⟩ ⟨28, by decide⟩ _
      (Q2.validAt ⟨122, by decide⟩ (Q2.listedAt ⟨122, by decide⟩
        (alnCheck_rep ⟨122, by decide⟩ hj hq).1))
      (colE2 ⟨28, by decide⟩ 4 hp) Q2.T122_28_2 Q2.hfix122_28_2 Q2.hinj122_28_2
      Q2.hcardT122_28_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T122_28_2 i) (Q2.hfix122_28_2 i) _)
      colCert_122_28_4.hD ?_).symm
  rw [alnId_122 j hj]


theorem leaf_122_28_5 (hp : 5 < (Q2.transData.getD 28 []).length)
    (j : Nat) (hj : j < (repChars.getD 122 []).length)
    (hq : (normIsRep.getD 122 []).getD j false = true) :
    species (Q2.reps (⟨28, by decide⟩ : Fin 148)) (colE2 ⟨28, by decide⟩ 5 hp)
        (rowE2 (⟨122, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨28, by decide⟩ : Fin 148))
        (colE1 ⟨28, by decide⟩ 5 (transLenTr ⟨28, by decide⟩ 5 hp))
        (rowE1 (⟨122, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨122, by decide⟩ : Fin 148) ⟨28, by decide⟩ _
      (validAt ⟨122, by decide⟩ (listedAt ⟨122, by decide⟩ hj))
      (colE1 ⟨28, by decide⟩ 5 (transLenTr ⟨28, by decide⟩ 5 hp)) T122_28
      hfix122_28 hinj122_28 hcardT122_28
      (fun i => conj_mem_of_fixedPoints _ _ (T122_28 i) (hfix122_28 i) _)
      ⟨122, by decide⟩ ⟨28, by decide⟩ _
      (Q2.validAt ⟨122, by decide⟩ (Q2.listedAt ⟨122, by decide⟩
        (alnCheck_rep ⟨122, by decide⟩ hj hq).1))
      (colE2 ⟨28, by decide⟩ 5 hp) Q2.T122_28_2 Q2.hfix122_28_2 Q2.hinj122_28_2
      Q2.hcardT122_28_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T122_28_2 i) (Q2.hfix122_28_2 i) _)
      colCert_122_28_5.hD ?_).symm
  rw [alnId_122 j hj]


theorem leaf_122_28_10 (hp : 10 < (Q2.transData.getD 28 []).length)
    (j : Nat) (hj : j < (repChars.getD 122 []).length)
    (hq : (normIsRep.getD 122 []).getD j false = true) :
    species (Q2.reps (⟨28, by decide⟩ : Fin 148)) (colE2 ⟨28, by decide⟩ 10 hp)
        (rowE2 (⟨122, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨28, by decide⟩ : Fin 148))
        (colE1 ⟨28, by decide⟩ 10 (transLenTr ⟨28, by decide⟩ 10 hp))
        (rowE1 (⟨122, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨122, by decide⟩ : Fin 148) ⟨28, by decide⟩ _
      (validAt ⟨122, by decide⟩ (listedAt ⟨122, by decide⟩ hj))
      (colE1 ⟨28, by decide⟩ 10 (transLenTr ⟨28, by decide⟩ 10 hp)) T122_28
      hfix122_28 hinj122_28 hcardT122_28
      (fun i => conj_mem_of_fixedPoints _ _ (T122_28 i) (hfix122_28 i) _)
      ⟨122, by decide⟩ ⟨28, by decide⟩ _
      (Q2.validAt ⟨122, by decide⟩ (Q2.listedAt ⟨122, by decide⟩
        (alnCheck_rep ⟨122, by decide⟩ hj hq).1))
      (colE2 ⟨28, by decide⟩ 10 hp) Q2.T122_28_2 Q2.hfix122_28_2 Q2.hinj122_28_2
      Q2.hcardT122_28_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T122_28_2 i) (Q2.hfix122_28_2 i) _)
      colCert_122_28_10.hD ?_).symm
  rw [alnId_122 j hj]


theorem leaf_122_28_15 (hp : 15 < (Q2.transData.getD 28 []).length)
    (j : Nat) (hj : j < (repChars.getD 122 []).length)
    (hq : (normIsRep.getD 122 []).getD j false = true) :
    species (Q2.reps (⟨28, by decide⟩ : Fin 148)) (colE2 ⟨28, by decide⟩ 15 hp)
        (rowE2 (⟨122, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨28, by decide⟩ : Fin 148))
        (colE1 ⟨28, by decide⟩ 15 (transLenTr ⟨28, by decide⟩ 15 hp))
        (rowE1 (⟨122, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨122, by decide⟩ : Fin 148) ⟨28, by decide⟩ _
      (validAt ⟨122, by decide⟩ (listedAt ⟨122, by decide⟩ hj))
      (colE1 ⟨28, by decide⟩ 15 (transLenTr ⟨28, by decide⟩ 15 hp)) T122_28
      hfix122_28 hinj122_28 hcardT122_28
      (fun i => conj_mem_of_fixedPoints _ _ (T122_28 i) (hfix122_28 i) _)
      ⟨122, by decide⟩ ⟨28, by decide⟩ _
      (Q2.validAt ⟨122, by decide⟩ (Q2.listedAt ⟨122, by decide⟩
        (alnCheck_rep ⟨122, by decide⟩ hj hq).1))
      (colE2 ⟨28, by decide⟩ 15 hp) Q2.T122_28_2 Q2.hfix122_28_2 Q2.hinj122_28_2
      Q2.hcardT122_28_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T122_28_2 i) (Q2.hfix122_28_2 i) _)
      colCert_122_28_15.hD ?_).symm
  rw [alnId_122 j hj]


theorem leaf_122_28_20 (hp : 20 < (Q2.transData.getD 28 []).length)
    (j : Nat) (hj : j < (repChars.getD 122 []).length)
    (hq : (normIsRep.getD 122 []).getD j false = true) :
    species (Q2.reps (⟨28, by decide⟩ : Fin 148)) (colE2 ⟨28, by decide⟩ 20 hp)
        (rowE2 (⟨122, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨28, by decide⟩ : Fin 148))
        (colE1 ⟨28, by decide⟩ 20 (transLenTr ⟨28, by decide⟩ 20 hp))
        (rowE1 (⟨122, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨122, by decide⟩ : Fin 148) ⟨28, by decide⟩ _
      (validAt ⟨122, by decide⟩ (listedAt ⟨122, by decide⟩ hj))
      (colE1 ⟨28, by decide⟩ 20 (transLenTr ⟨28, by decide⟩ 20 hp)) T122_28
      hfix122_28 hinj122_28 hcardT122_28
      (fun i => conj_mem_of_fixedPoints _ _ (T122_28 i) (hfix122_28 i) _)
      ⟨122, by decide⟩ ⟨28, by decide⟩ _
      (Q2.validAt ⟨122, by decide⟩ (Q2.listedAt ⟨122, by decide⟩
        (alnCheck_rep ⟨122, by decide⟩ hj hq).1))
      (colE2 ⟨28, by decide⟩ 20 hp) Q2.T122_28_2 Q2.hfix122_28_2 Q2.hinj122_28_2
      Q2.hcardT122_28_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T122_28_2 i) (Q2.hfix122_28_2 i) _)
      colCert_122_28_20.hD ?_).symm
  rw [alnId_122 j hj]


theorem leaf_122_36_0 (hp : 0 < (Q2.transData.getD 36 []).length)
    (j : Nat) (hj : j < (repChars.getD 122 []).length)
    (hq : (normIsRep.getD 122 []).getD j false = true) :
    species (Q2.reps (⟨36, by decide⟩ : Fin 148)) (colE2 ⟨36, by decide⟩ 0 hp)
        (rowE2 (⟨122, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨36, by decide⟩ : Fin 148))
        (colE1 ⟨36, by decide⟩ 0 (transLenTr ⟨36, by decide⟩ 0 hp))
        (rowE1 (⟨122, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨122, by decide⟩ : Fin 148) ⟨36, by decide⟩ _
      (validAt ⟨122, by decide⟩ (listedAt ⟨122, by decide⟩ hj))
      (colE1 ⟨36, by decide⟩ 0 (transLenTr ⟨36, by decide⟩ 0 hp)) T122_36
      hfix122_36 hinj122_36 hcardT122_36
      (fun i => conj_mem_of_fixedPoints _ _ (T122_36 i) (hfix122_36 i) _)
      ⟨122, by decide⟩ ⟨36, by decide⟩ _
      (Q2.validAt ⟨122, by decide⟩ (Q2.listedAt ⟨122, by decide⟩
        (alnCheck_rep ⟨122, by decide⟩ hj hq).1))
      (colE2 ⟨36, by decide⟩ 0 hp) Q2.T122_36_2 Q2.hfix122_36_2 Q2.hinj122_36_2
      Q2.hcardT122_36_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T122_36_2 i) (Q2.hfix122_36_2 i) _)
      colCert_122_36_0.hD ?_).symm
  rw [alnId_122 j hj]


theorem leaf_122_36_1 (hp : 1 < (Q2.transData.getD 36 []).length)
    (j : Nat) (hj : j < (repChars.getD 122 []).length)
    (hq : (normIsRep.getD 122 []).getD j false = true) :
    species (Q2.reps (⟨36, by decide⟩ : Fin 148)) (colE2 ⟨36, by decide⟩ 1 hp)
        (rowE2 (⟨122, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨36, by decide⟩ : Fin 148))
        (colE1 ⟨36, by decide⟩ 1 (transLenTr ⟨36, by decide⟩ 1 hp))
        (rowE1 (⟨122, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨122, by decide⟩ : Fin 148) ⟨36, by decide⟩ _
      (validAt ⟨122, by decide⟩ (listedAt ⟨122, by decide⟩ hj))
      (colE1 ⟨36, by decide⟩ 1 (transLenTr ⟨36, by decide⟩ 1 hp)) T122_36
      hfix122_36 hinj122_36 hcardT122_36
      (fun i => conj_mem_of_fixedPoints _ _ (T122_36 i) (hfix122_36 i) _)
      ⟨122, by decide⟩ ⟨36, by decide⟩ _
      (Q2.validAt ⟨122, by decide⟩ (Q2.listedAt ⟨122, by decide⟩
        (alnCheck_rep ⟨122, by decide⟩ hj hq).1))
      (colE2 ⟨36, by decide⟩ 1 hp) Q2.T122_36_2 Q2.hfix122_36_2 Q2.hinj122_36_2
      Q2.hcardT122_36_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T122_36_2 i) (Q2.hfix122_36_2 i) _)
      colCert_122_36_1.hD ?_).symm
  rw [alnId_122 j hj]


theorem leaf_122_36_2 (hp : 2 < (Q2.transData.getD 36 []).length)
    (j : Nat) (hj : j < (repChars.getD 122 []).length)
    (hq : (normIsRep.getD 122 []).getD j false = true) :
    species (Q2.reps (⟨36, by decide⟩ : Fin 148)) (colE2 ⟨36, by decide⟩ 2 hp)
        (rowE2 (⟨122, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨36, by decide⟩ : Fin 148))
        (colE1 ⟨36, by decide⟩ 2 (transLenTr ⟨36, by decide⟩ 2 hp))
        (rowE1 (⟨122, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨122, by decide⟩ : Fin 148) ⟨36, by decide⟩ _
      (validAt ⟨122, by decide⟩ (listedAt ⟨122, by decide⟩ hj))
      (colE1 ⟨36, by decide⟩ 2 (transLenTr ⟨36, by decide⟩ 2 hp)) T122_36
      hfix122_36 hinj122_36 hcardT122_36
      (fun i => conj_mem_of_fixedPoints _ _ (T122_36 i) (hfix122_36 i) _)
      ⟨122, by decide⟩ ⟨36, by decide⟩ _
      (Q2.validAt ⟨122, by decide⟩ (Q2.listedAt ⟨122, by decide⟩
        (alnCheck_rep ⟨122, by decide⟩ hj hq).1))
      (colE2 ⟨36, by decide⟩ 2 hp) Q2.T122_36_2 Q2.hfix122_36_2 Q2.hinj122_36_2
      Q2.hcardT122_36_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T122_36_2 i) (Q2.hfix122_36_2 i) _)
      colCert_122_36_2.hD ?_).symm
  rw [alnId_122 j hj]


theorem leaf_122_36_3 (hp : 3 < (Q2.transData.getD 36 []).length)
    (j : Nat) (hj : j < (repChars.getD 122 []).length)
    (hq : (normIsRep.getD 122 []).getD j false = true) :
    species (Q2.reps (⟨36, by decide⟩ : Fin 148)) (colE2 ⟨36, by decide⟩ 3 hp)
        (rowE2 (⟨122, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨36, by decide⟩ : Fin 148))
        (colE1 ⟨36, by decide⟩ 3 (transLenTr ⟨36, by decide⟩ 3 hp))
        (rowE1 (⟨122, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨122, by decide⟩ : Fin 148) ⟨36, by decide⟩ _
      (validAt ⟨122, by decide⟩ (listedAt ⟨122, by decide⟩ hj))
      (colE1 ⟨36, by decide⟩ 3 (transLenTr ⟨36, by decide⟩ 3 hp)) T122_36
      hfix122_36 hinj122_36 hcardT122_36
      (fun i => conj_mem_of_fixedPoints _ _ (T122_36 i) (hfix122_36 i) _)
      ⟨122, by decide⟩ ⟨36, by decide⟩ _
      (Q2.validAt ⟨122, by decide⟩ (Q2.listedAt ⟨122, by decide⟩
        (alnCheck_rep ⟨122, by decide⟩ hj hq).1))
      (colE2 ⟨36, by decide⟩ 3 hp) Q2.T122_36_2 Q2.hfix122_36_2 Q2.hinj122_36_2
      Q2.hcardT122_36_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T122_36_2 i) (Q2.hfix122_36_2 i) _)
      colCert_122_36_3.hD ?_).symm
  rw [alnId_122 j hj]


theorem leaf_122_36_4 (hp : 4 < (Q2.transData.getD 36 []).length)
    (j : Nat) (hj : j < (repChars.getD 122 []).length)
    (hq : (normIsRep.getD 122 []).getD j false = true) :
    species (Q2.reps (⟨36, by decide⟩ : Fin 148)) (colE2 ⟨36, by decide⟩ 4 hp)
        (rowE2 (⟨122, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨36, by decide⟩ : Fin 148))
        (colE1 ⟨36, by decide⟩ 4 (transLenTr ⟨36, by decide⟩ 4 hp))
        (rowE1 (⟨122, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨122, by decide⟩ : Fin 148) ⟨36, by decide⟩ _
      (validAt ⟨122, by decide⟩ (listedAt ⟨122, by decide⟩ hj))
      (colE1 ⟨36, by decide⟩ 4 (transLenTr ⟨36, by decide⟩ 4 hp)) T122_36
      hfix122_36 hinj122_36 hcardT122_36
      (fun i => conj_mem_of_fixedPoints _ _ (T122_36 i) (hfix122_36 i) _)
      ⟨122, by decide⟩ ⟨36, by decide⟩ _
      (Q2.validAt ⟨122, by decide⟩ (Q2.listedAt ⟨122, by decide⟩
        (alnCheck_rep ⟨122, by decide⟩ hj hq).1))
      (colE2 ⟨36, by decide⟩ 4 hp) Q2.T122_36_2 Q2.hfix122_36_2 Q2.hinj122_36_2
      Q2.hcardT122_36_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T122_36_2 i) (Q2.hfix122_36_2 i) _)
      colCert_122_36_4.hD ?_).symm
  rw [alnId_122 j hj]


theorem leaf_122_36_5 (hp : 5 < (Q2.transData.getD 36 []).length)
    (j : Nat) (hj : j < (repChars.getD 122 []).length)
    (hq : (normIsRep.getD 122 []).getD j false = true) :
    species (Q2.reps (⟨36, by decide⟩ : Fin 148)) (colE2 ⟨36, by decide⟩ 5 hp)
        (rowE2 (⟨122, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨36, by decide⟩ : Fin 148))
        (colE1 ⟨36, by decide⟩ 5 (transLenTr ⟨36, by decide⟩ 5 hp))
        (rowE1 (⟨122, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨122, by decide⟩ : Fin 148) ⟨36, by decide⟩ _
      (validAt ⟨122, by decide⟩ (listedAt ⟨122, by decide⟩ hj))
      (colE1 ⟨36, by decide⟩ 5 (transLenTr ⟨36, by decide⟩ 5 hp)) T122_36
      hfix122_36 hinj122_36 hcardT122_36
      (fun i => conj_mem_of_fixedPoints _ _ (T122_36 i) (hfix122_36 i) _)
      ⟨122, by decide⟩ ⟨36, by decide⟩ _
      (Q2.validAt ⟨122, by decide⟩ (Q2.listedAt ⟨122, by decide⟩
        (alnCheck_rep ⟨122, by decide⟩ hj hq).1))
      (colE2 ⟨36, by decide⟩ 5 hp) Q2.T122_36_2 Q2.hfix122_36_2 Q2.hinj122_36_2
      Q2.hcardT122_36_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T122_36_2 i) (Q2.hfix122_36_2 i) _)
      ?_).symm
  rw [show colData1 (⟨122, by decide⟩ : Fin 148)
        ((colE1 ⟨36, by decide⟩ 5 (transLenTr ⟨36, by decide⟩ 5 hp) : ↥(reps ⟨36, by decide⟩)) : Coordinate 1)
        T122_36 = colFn colCertDiv_122_36_5.D1 (m := 5) from colCertDiv_122_36_5.bind1,
    show colData2 (⟨122, by decide⟩ : Fin 148)
        ((colE2 ⟨36, by decide⟩ 5 hp : ↥(Q2.reps ⟨36, by decide⟩)) : Coordinate 2)
        Q2.T122_36_2 = colFn colCertDiv_122_36_5.D2 (m := 5) from colCertDiv_122_36_5.bind2]
  rw [alnId_122 j hj]
  exact fastcode_of_div ⟨122, by decide⟩ _ _ _
    ((alnId_122 j hj) ▸ Q2.listedAt (⟨122, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨122, by decide⟩ : Fin 148) hj hq).1) colCertDiv_122_36_5_match


theorem leaf_122_36_10 (hp : 10 < (Q2.transData.getD 36 []).length)
    (j : Nat) (hj : j < (repChars.getD 122 []).length)
    (hq : (normIsRep.getD 122 []).getD j false = true) :
    species (Q2.reps (⟨36, by decide⟩ : Fin 148)) (colE2 ⟨36, by decide⟩ 10 hp)
        (rowE2 (⟨122, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨36, by decide⟩ : Fin 148))
        (colE1 ⟨36, by decide⟩ 10 (transLenTr ⟨36, by decide⟩ 10 hp))
        (rowE1 (⟨122, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨122, by decide⟩ : Fin 148) ⟨36, by decide⟩ _
      (validAt ⟨122, by decide⟩ (listedAt ⟨122, by decide⟩ hj))
      (colE1 ⟨36, by decide⟩ 10 (transLenTr ⟨36, by decide⟩ 10 hp)) T122_36
      hfix122_36 hinj122_36 hcardT122_36
      (fun i => conj_mem_of_fixedPoints _ _ (T122_36 i) (hfix122_36 i) _)
      ⟨122, by decide⟩ ⟨36, by decide⟩ _
      (Q2.validAt ⟨122, by decide⟩ (Q2.listedAt ⟨122, by decide⟩
        (alnCheck_rep ⟨122, by decide⟩ hj hq).1))
      (colE2 ⟨36, by decide⟩ 10 hp) Q2.T122_36_2 Q2.hfix122_36_2 Q2.hinj122_36_2
      Q2.hcardT122_36_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T122_36_2 i) (Q2.hfix122_36_2 i) _)
      ?_).symm
  rw [show colData1 (⟨122, by decide⟩ : Fin 148)
        ((colE1 ⟨36, by decide⟩ 10 (transLenTr ⟨36, by decide⟩ 10 hp) : ↥(reps ⟨36, by decide⟩)) : Coordinate 1)
        T122_36 = colFn colCertDiv_122_36_10.D1 (m := 5) from colCertDiv_122_36_10.bind1,
    show colData2 (⟨122, by decide⟩ : Fin 148)
        ((colE2 ⟨36, by decide⟩ 10 hp : ↥(Q2.reps ⟨36, by decide⟩)) : Coordinate 2)
        Q2.T122_36_2 = colFn colCertDiv_122_36_10.D2 (m := 5) from colCertDiv_122_36_10.bind2]
  rw [alnId_122 j hj]
  exact fastcode_of_div ⟨122, by decide⟩ _ _ _
    ((alnId_122 j hj) ▸ Q2.listedAt (⟨122, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨122, by decide⟩ : Fin 148) hj hq).1) colCertDiv_122_36_10_match


theorem leaf_122_36_15 (hp : 15 < (Q2.transData.getD 36 []).length)
    (j : Nat) (hj : j < (repChars.getD 122 []).length)
    (hq : (normIsRep.getD 122 []).getD j false = true) :
    species (Q2.reps (⟨36, by decide⟩ : Fin 148)) (colE2 ⟨36, by decide⟩ 15 hp)
        (rowE2 (⟨122, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨36, by decide⟩ : Fin 148))
        (colE1 ⟨36, by decide⟩ 15 (transLenTr ⟨36, by decide⟩ 15 hp))
        (rowE1 (⟨122, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨122, by decide⟩ : Fin 148) ⟨36, by decide⟩ _
      (validAt ⟨122, by decide⟩ (listedAt ⟨122, by decide⟩ hj))
      (colE1 ⟨36, by decide⟩ 15 (transLenTr ⟨36, by decide⟩ 15 hp)) T122_36
      hfix122_36 hinj122_36 hcardT122_36
      (fun i => conj_mem_of_fixedPoints _ _ (T122_36 i) (hfix122_36 i) _)
      ⟨122, by decide⟩ ⟨36, by decide⟩ _
      (Q2.validAt ⟨122, by decide⟩ (Q2.listedAt ⟨122, by decide⟩
        (alnCheck_rep ⟨122, by decide⟩ hj hq).1))
      (colE2 ⟨36, by decide⟩ 15 hp) Q2.T122_36_2 Q2.hfix122_36_2 Q2.hinj122_36_2
      Q2.hcardT122_36_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T122_36_2 i) (Q2.hfix122_36_2 i) _)
      ?_).symm
  rw [show colData1 (⟨122, by decide⟩ : Fin 148)
        ((colE1 ⟨36, by decide⟩ 15 (transLenTr ⟨36, by decide⟩ 15 hp) : ↥(reps ⟨36, by decide⟩)) : Coordinate 1)
        T122_36 = colFn colCertDiv_122_36_15.D1 (m := 5) from colCertDiv_122_36_15.bind1,
    show colData2 (⟨122, by decide⟩ : Fin 148)
        ((colE2 ⟨36, by decide⟩ 15 hp : ↥(Q2.reps ⟨36, by decide⟩)) : Coordinate 2)
        Q2.T122_36_2 = colFn colCertDiv_122_36_15.D2 (m := 5) from colCertDiv_122_36_15.bind2]
  rw [alnId_122 j hj]
  exact fastcode_of_div ⟨122, by decide⟩ _ _ _
    ((alnId_122 j hj) ▸ Q2.listedAt (⟨122, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨122, by decide⟩ : Fin 148) hj hq).1) colCertDiv_122_36_15_match


theorem leaf_122_36_20 (hp : 20 < (Q2.transData.getD 36 []).length)
    (j : Nat) (hj : j < (repChars.getD 122 []).length)
    (hq : (normIsRep.getD 122 []).getD j false = true) :
    species (Q2.reps (⟨36, by decide⟩ : Fin 148)) (colE2 ⟨36, by decide⟩ 20 hp)
        (rowE2 (⟨122, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨36, by decide⟩ : Fin 148))
        (colE1 ⟨36, by decide⟩ 20 (transLenTr ⟨36, by decide⟩ 20 hp))
        (rowE1 (⟨122, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨122, by decide⟩ : Fin 148) ⟨36, by decide⟩ _
      (validAt ⟨122, by decide⟩ (listedAt ⟨122, by decide⟩ hj))
      (colE1 ⟨36, by decide⟩ 20 (transLenTr ⟨36, by decide⟩ 20 hp)) T122_36
      hfix122_36 hinj122_36 hcardT122_36
      (fun i => conj_mem_of_fixedPoints _ _ (T122_36 i) (hfix122_36 i) _)
      ⟨122, by decide⟩ ⟨36, by decide⟩ _
      (Q2.validAt ⟨122, by decide⟩ (Q2.listedAt ⟨122, by decide⟩
        (alnCheck_rep ⟨122, by decide⟩ hj hq).1))
      (colE2 ⟨36, by decide⟩ 20 hp) Q2.T122_36_2 Q2.hfix122_36_2 Q2.hinj122_36_2
      Q2.hcardT122_36_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T122_36_2 i) (Q2.hfix122_36_2 i) _)
      ?_).symm
  rw [show colData1 (⟨122, by decide⟩ : Fin 148)
        ((colE1 ⟨36, by decide⟩ 20 (transLenTr ⟨36, by decide⟩ 20 hp) : ↥(reps ⟨36, by decide⟩)) : Coordinate 1)
        T122_36 = colFn colCertDiv_122_36_20.D1 (m := 5) from colCertDiv_122_36_20.bind1,
    show colData2 (⟨122, by decide⟩ : Fin 148)
        ((colE2 ⟨36, by decide⟩ 20 hp : ↥(Q2.reps ⟨36, by decide⟩)) : Coordinate 2)
        Q2.T122_36_2 = colFn colCertDiv_122_36_20.D2 (m := 5) from colCertDiv_122_36_20.bind2]
  rw [alnId_122 j hj]
  exact fastcode_of_div ⟨122, by decide⟩ _ _ _
    ((alnId_122 j hj) ▸ Q2.listedAt (⟨122, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨122, by decide⟩ : Fin 148) hj hq).1) colCertDiv_122_36_20_match


theorem leaf_122_42_0 (hp : 0 < (Q2.transData.getD 42 []).length)
    (j : Nat) (hj : j < (repChars.getD 122 []).length)
    (hq : (normIsRep.getD 122 []).getD j false = true) :
    species (Q2.reps (⟨42, by decide⟩ : Fin 148)) (colE2 ⟨42, by decide⟩ 0 hp)
        (rowE2 (⟨122, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨42, by decide⟩ : Fin 148))
        (colE1 ⟨42, by decide⟩ 0 (transLenTr ⟨42, by decide⟩ 0 hp))
        (rowE1 (⟨122, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨122, by decide⟩ : Fin 148) ⟨42, by decide⟩ _
      (validAt ⟨122, by decide⟩ (listedAt ⟨122, by decide⟩ hj))
      (colE1 ⟨42, by decide⟩ 0 (transLenTr ⟨42, by decide⟩ 0 hp)) T122_42
      hfix122_42 hinj122_42 hcardT122_42
      (fun i => conj_mem_of_fixedPoints _ _ (T122_42 i) (hfix122_42 i) _)
      ⟨122, by decide⟩ ⟨42, by decide⟩ _
      (Q2.validAt ⟨122, by decide⟩ (Q2.listedAt ⟨122, by decide⟩
        (alnCheck_rep ⟨122, by decide⟩ hj hq).1))
      (colE2 ⟨42, by decide⟩ 0 hp) Q2.T122_42_2 Q2.hfix122_42_2 Q2.hinj122_42_2
      Q2.hcardT122_42_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T122_42_2 i) (Q2.hfix122_42_2 i) _)
      colCert_122_42_0.hD ?_).symm
  rw [alnId_122 j hj]


theorem leaf_122_42_1 (hp : 1 < (Q2.transData.getD 42 []).length)
    (j : Nat) (hj : j < (repChars.getD 122 []).length)
    (hq : (normIsRep.getD 122 []).getD j false = true) :
    species (Q2.reps (⟨42, by decide⟩ : Fin 148)) (colE2 ⟨42, by decide⟩ 1 hp)
        (rowE2 (⟨122, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨42, by decide⟩ : Fin 148))
        (colE1 ⟨42, by decide⟩ 1 (transLenTr ⟨42, by decide⟩ 1 hp))
        (rowE1 (⟨122, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨122, by decide⟩ : Fin 148) ⟨42, by decide⟩ _
      (validAt ⟨122, by decide⟩ (listedAt ⟨122, by decide⟩ hj))
      (colE1 ⟨42, by decide⟩ 1 (transLenTr ⟨42, by decide⟩ 1 hp)) T122_42
      hfix122_42 hinj122_42 hcardT122_42
      (fun i => conj_mem_of_fixedPoints _ _ (T122_42 i) (hfix122_42 i) _)
      ⟨122, by decide⟩ ⟨42, by decide⟩ _
      (Q2.validAt ⟨122, by decide⟩ (Q2.listedAt ⟨122, by decide⟩
        (alnCheck_rep ⟨122, by decide⟩ hj hq).1))
      (colE2 ⟨42, by decide⟩ 1 hp) Q2.T122_42_2 Q2.hfix122_42_2 Q2.hinj122_42_2
      Q2.hcardT122_42_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T122_42_2 i) (Q2.hfix122_42_2 i) _)
      colCert_122_42_1.hD ?_).symm
  rw [alnId_122 j hj]


theorem leaf_122_42_2 (hp : 2 < (Q2.transData.getD 42 []).length)
    (j : Nat) (hj : j < (repChars.getD 122 []).length)
    (hq : (normIsRep.getD 122 []).getD j false = true) :
    species (Q2.reps (⟨42, by decide⟩ : Fin 148)) (colE2 ⟨42, by decide⟩ 2 hp)
        (rowE2 (⟨122, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨42, by decide⟩ : Fin 148))
        (colE1 ⟨42, by decide⟩ 2 (transLenTr ⟨42, by decide⟩ 2 hp))
        (rowE1 (⟨122, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨122, by decide⟩ : Fin 148) ⟨42, by decide⟩ _
      (validAt ⟨122, by decide⟩ (listedAt ⟨122, by decide⟩ hj))
      (colE1 ⟨42, by decide⟩ 2 (transLenTr ⟨42, by decide⟩ 2 hp)) T122_42
      hfix122_42 hinj122_42 hcardT122_42
      (fun i => conj_mem_of_fixedPoints _ _ (T122_42 i) (hfix122_42 i) _)
      ⟨122, by decide⟩ ⟨42, by decide⟩ _
      (Q2.validAt ⟨122, by decide⟩ (Q2.listedAt ⟨122, by decide⟩
        (alnCheck_rep ⟨122, by decide⟩ hj hq).1))
      (colE2 ⟨42, by decide⟩ 2 hp) Q2.T122_42_2 Q2.hfix122_42_2 Q2.hinj122_42_2
      Q2.hcardT122_42_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T122_42_2 i) (Q2.hfix122_42_2 i) _)
      colCert_122_42_2.hD ?_).symm
  rw [alnId_122 j hj]


theorem leaf_122_42_3 (hp : 3 < (Q2.transData.getD 42 []).length)
    (j : Nat) (hj : j < (repChars.getD 122 []).length)
    (hq : (normIsRep.getD 122 []).getD j false = true) :
    species (Q2.reps (⟨42, by decide⟩ : Fin 148)) (colE2 ⟨42, by decide⟩ 3 hp)
        (rowE2 (⟨122, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨42, by decide⟩ : Fin 148))
        (colE1 ⟨42, by decide⟩ 3 (transLenTr ⟨42, by decide⟩ 3 hp))
        (rowE1 (⟨122, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨122, by decide⟩ : Fin 148) ⟨42, by decide⟩ _
      (validAt ⟨122, by decide⟩ (listedAt ⟨122, by decide⟩ hj))
      (colE1 ⟨42, by decide⟩ 3 (transLenTr ⟨42, by decide⟩ 3 hp)) T122_42
      hfix122_42 hinj122_42 hcardT122_42
      (fun i => conj_mem_of_fixedPoints _ _ (T122_42 i) (hfix122_42 i) _)
      ⟨122, by decide⟩ ⟨42, by decide⟩ _
      (Q2.validAt ⟨122, by decide⟩ (Q2.listedAt ⟨122, by decide⟩
        (alnCheck_rep ⟨122, by decide⟩ hj hq).1))
      (colE2 ⟨42, by decide⟩ 3 hp) Q2.T122_42_2 Q2.hfix122_42_2 Q2.hinj122_42_2
      Q2.hcardT122_42_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T122_42_2 i) (Q2.hfix122_42_2 i) _)
      colCert_122_42_3.hD ?_).symm
  rw [alnId_122 j hj]


theorem leaf_122_42_4 (hp : 4 < (Q2.transData.getD 42 []).length)
    (j : Nat) (hj : j < (repChars.getD 122 []).length)
    (hq : (normIsRep.getD 122 []).getD j false = true) :
    species (Q2.reps (⟨42, by decide⟩ : Fin 148)) (colE2 ⟨42, by decide⟩ 4 hp)
        (rowE2 (⟨122, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨42, by decide⟩ : Fin 148))
        (colE1 ⟨42, by decide⟩ 4 (transLenTr ⟨42, by decide⟩ 4 hp))
        (rowE1 (⟨122, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨122, by decide⟩ : Fin 148) ⟨42, by decide⟩ _
      (validAt ⟨122, by decide⟩ (listedAt ⟨122, by decide⟩ hj))
      (colE1 ⟨42, by decide⟩ 4 (transLenTr ⟨42, by decide⟩ 4 hp)) T122_42
      hfix122_42 hinj122_42 hcardT122_42
      (fun i => conj_mem_of_fixedPoints _ _ (T122_42 i) (hfix122_42 i) _)
      ⟨122, by decide⟩ ⟨42, by decide⟩ _
      (Q2.validAt ⟨122, by decide⟩ (Q2.listedAt ⟨122, by decide⟩
        (alnCheck_rep ⟨122, by decide⟩ hj hq).1))
      (colE2 ⟨42, by decide⟩ 4 hp) Q2.T122_42_2 Q2.hfix122_42_2 Q2.hinj122_42_2
      Q2.hcardT122_42_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T122_42_2 i) (Q2.hfix122_42_2 i) _)
      colCert_122_42_4.hD ?_).symm
  rw [alnId_122 j hj]


theorem leaf_122_42_5 (hp : 5 < (Q2.transData.getD 42 []).length)
    (j : Nat) (hj : j < (repChars.getD 122 []).length)
    (hq : (normIsRep.getD 122 []).getD j false = true) :
    species (Q2.reps (⟨42, by decide⟩ : Fin 148)) (colE2 ⟨42, by decide⟩ 5 hp)
        (rowE2 (⟨122, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨42, by decide⟩ : Fin 148))
        (colE1 ⟨42, by decide⟩ 5 (transLenTr ⟨42, by decide⟩ 5 hp))
        (rowE1 (⟨122, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨122, by decide⟩ : Fin 148) ⟨42, by decide⟩ _
      (validAt ⟨122, by decide⟩ (listedAt ⟨122, by decide⟩ hj))
      (colE1 ⟨42, by decide⟩ 5 (transLenTr ⟨42, by decide⟩ 5 hp)) T122_42
      hfix122_42 hinj122_42 hcardT122_42
      (fun i => conj_mem_of_fixedPoints _ _ (T122_42 i) (hfix122_42 i) _)
      ⟨122, by decide⟩ ⟨42, by decide⟩ _
      (Q2.validAt ⟨122, by decide⟩ (Q2.listedAt ⟨122, by decide⟩
        (alnCheck_rep ⟨122, by decide⟩ hj hq).1))
      (colE2 ⟨42, by decide⟩ 5 hp) Q2.T122_42_2 Q2.hfix122_42_2 Q2.hinj122_42_2
      Q2.hcardT122_42_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T122_42_2 i) (Q2.hfix122_42_2 i) _)
      ?_).symm
  rw [show colData1 (⟨122, by decide⟩ : Fin 148)
        ((colE1 ⟨42, by decide⟩ 5 (transLenTr ⟨42, by decide⟩ 5 hp) : ↥(reps ⟨42, by decide⟩)) : Coordinate 1)
        T122_42 = colFn colCertDiv_122_42_5.D1 (m := 5) from colCertDiv_122_42_5.bind1,
    show colData2 (⟨122, by decide⟩ : Fin 148)
        ((colE2 ⟨42, by decide⟩ 5 hp : ↥(Q2.reps ⟨42, by decide⟩)) : Coordinate 2)
        Q2.T122_42_2 = colFn colCertDiv_122_42_5.D2 (m := 5) from colCertDiv_122_42_5.bind2]
  rw [alnId_122 j hj]
  exact fastcode_of_div ⟨122, by decide⟩ _ _ _
    ((alnId_122 j hj) ▸ Q2.listedAt (⟨122, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨122, by decide⟩ : Fin 148) hj hq).1) colCertDiv_122_42_5_match


theorem leaf_122_42_10 (hp : 10 < (Q2.transData.getD 42 []).length)
    (j : Nat) (hj : j < (repChars.getD 122 []).length)
    (hq : (normIsRep.getD 122 []).getD j false = true) :
    species (Q2.reps (⟨42, by decide⟩ : Fin 148)) (colE2 ⟨42, by decide⟩ 10 hp)
        (rowE2 (⟨122, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨42, by decide⟩ : Fin 148))
        (colE1 ⟨42, by decide⟩ 10 (transLenTr ⟨42, by decide⟩ 10 hp))
        (rowE1 (⟨122, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨122, by decide⟩ : Fin 148) ⟨42, by decide⟩ _
      (validAt ⟨122, by decide⟩ (listedAt ⟨122, by decide⟩ hj))
      (colE1 ⟨42, by decide⟩ 10 (transLenTr ⟨42, by decide⟩ 10 hp)) T122_42
      hfix122_42 hinj122_42 hcardT122_42
      (fun i => conj_mem_of_fixedPoints _ _ (T122_42 i) (hfix122_42 i) _)
      ⟨122, by decide⟩ ⟨42, by decide⟩ _
      (Q2.validAt ⟨122, by decide⟩ (Q2.listedAt ⟨122, by decide⟩
        (alnCheck_rep ⟨122, by decide⟩ hj hq).1))
      (colE2 ⟨42, by decide⟩ 10 hp) Q2.T122_42_2 Q2.hfix122_42_2 Q2.hinj122_42_2
      Q2.hcardT122_42_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T122_42_2 i) (Q2.hfix122_42_2 i) _)
      ?_).symm
  rw [show colData1 (⟨122, by decide⟩ : Fin 148)
        ((colE1 ⟨42, by decide⟩ 10 (transLenTr ⟨42, by decide⟩ 10 hp) : ↥(reps ⟨42, by decide⟩)) : Coordinate 1)
        T122_42 = colFn colCertDiv_122_42_10.D1 (m := 5) from colCertDiv_122_42_10.bind1,
    show colData2 (⟨122, by decide⟩ : Fin 148)
        ((colE2 ⟨42, by decide⟩ 10 hp : ↥(Q2.reps ⟨42, by decide⟩)) : Coordinate 2)
        Q2.T122_42_2 = colFn colCertDiv_122_42_10.D2 (m := 5) from colCertDiv_122_42_10.bind2]
  rw [alnId_122 j hj]
  exact fastcode_of_div ⟨122, by decide⟩ _ _ _
    ((alnId_122 j hj) ▸ Q2.listedAt (⟨122, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨122, by decide⟩ : Fin 148) hj hq).1) colCertDiv_122_42_10_match


theorem leaf_122_42_15 (hp : 15 < (Q2.transData.getD 42 []).length)
    (j : Nat) (hj : j < (repChars.getD 122 []).length)
    (hq : (normIsRep.getD 122 []).getD j false = true) :
    species (Q2.reps (⟨42, by decide⟩ : Fin 148)) (colE2 ⟨42, by decide⟩ 15 hp)
        (rowE2 (⟨122, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨42, by decide⟩ : Fin 148))
        (colE1 ⟨42, by decide⟩ 15 (transLenTr ⟨42, by decide⟩ 15 hp))
        (rowE1 (⟨122, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨122, by decide⟩ : Fin 148) ⟨42, by decide⟩ _
      (validAt ⟨122, by decide⟩ (listedAt ⟨122, by decide⟩ hj))
      (colE1 ⟨42, by decide⟩ 15 (transLenTr ⟨42, by decide⟩ 15 hp)) T122_42
      hfix122_42 hinj122_42 hcardT122_42
      (fun i => conj_mem_of_fixedPoints _ _ (T122_42 i) (hfix122_42 i) _)
      ⟨122, by decide⟩ ⟨42, by decide⟩ _
      (Q2.validAt ⟨122, by decide⟩ (Q2.listedAt ⟨122, by decide⟩
        (alnCheck_rep ⟨122, by decide⟩ hj hq).1))
      (colE2 ⟨42, by decide⟩ 15 hp) Q2.T122_42_2 Q2.hfix122_42_2 Q2.hinj122_42_2
      Q2.hcardT122_42_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T122_42_2 i) (Q2.hfix122_42_2 i) _)
      ?_).symm
  rw [show colData1 (⟨122, by decide⟩ : Fin 148)
        ((colE1 ⟨42, by decide⟩ 15 (transLenTr ⟨42, by decide⟩ 15 hp) : ↥(reps ⟨42, by decide⟩)) : Coordinate 1)
        T122_42 = colFn colCertDiv_122_42_15.D1 (m := 5) from colCertDiv_122_42_15.bind1,
    show colData2 (⟨122, by decide⟩ : Fin 148)
        ((colE2 ⟨42, by decide⟩ 15 hp : ↥(Q2.reps ⟨42, by decide⟩)) : Coordinate 2)
        Q2.T122_42_2 = colFn colCertDiv_122_42_15.D2 (m := 5) from colCertDiv_122_42_15.bind2]
  rw [alnId_122 j hj]
  exact fastcode_of_div ⟨122, by decide⟩ _ _ _
    ((alnId_122 j hj) ▸ Q2.listedAt (⟨122, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨122, by decide⟩ : Fin 148) hj hq).1) colCertDiv_122_42_15_match


theorem leaf_122_42_20 (hp : 20 < (Q2.transData.getD 42 []).length)
    (j : Nat) (hj : j < (repChars.getD 122 []).length)
    (hq : (normIsRep.getD 122 []).getD j false = true) :
    species (Q2.reps (⟨42, by decide⟩ : Fin 148)) (colE2 ⟨42, by decide⟩ 20 hp)
        (rowE2 (⟨122, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨42, by decide⟩ : Fin 148))
        (colE1 ⟨42, by decide⟩ 20 (transLenTr ⟨42, by decide⟩ 20 hp))
        (rowE1 (⟨122, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨122, by decide⟩ : Fin 148) ⟨42, by decide⟩ _
      (validAt ⟨122, by decide⟩ (listedAt ⟨122, by decide⟩ hj))
      (colE1 ⟨42, by decide⟩ 20 (transLenTr ⟨42, by decide⟩ 20 hp)) T122_42
      hfix122_42 hinj122_42 hcardT122_42
      (fun i => conj_mem_of_fixedPoints _ _ (T122_42 i) (hfix122_42 i) _)
      ⟨122, by decide⟩ ⟨42, by decide⟩ _
      (Q2.validAt ⟨122, by decide⟩ (Q2.listedAt ⟨122, by decide⟩
        (alnCheck_rep ⟨122, by decide⟩ hj hq).1))
      (colE2 ⟨42, by decide⟩ 20 hp) Q2.T122_42_2 Q2.hfix122_42_2 Q2.hinj122_42_2
      Q2.hcardT122_42_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T122_42_2 i) (Q2.hfix122_42_2 i) _)
      ?_).symm
  rw [show colData1 (⟨122, by decide⟩ : Fin 148)
        ((colE1 ⟨42, by decide⟩ 20 (transLenTr ⟨42, by decide⟩ 20 hp) : ↥(reps ⟨42, by decide⟩)) : Coordinate 1)
        T122_42 = colFn colCertDiv_122_42_20.D1 (m := 5) from colCertDiv_122_42_20.bind1,
    show colData2 (⟨122, by decide⟩ : Fin 148)
        ((colE2 ⟨42, by decide⟩ 20 hp : ↥(Q2.reps ⟨42, by decide⟩)) : Coordinate 2)
        Q2.T122_42_2 = colFn colCertDiv_122_42_20.D2 (m := 5) from colCertDiv_122_42_20.bind2]
  rw [alnId_122 j hj]
  exact fastcode_of_div ⟨122, by decide⟩ _ _ _
    ((alnId_122 j hj) ▸ Q2.listedAt (⟨122, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨122, by decide⟩ : Fin 148) hj hq).1) colCertDiv_122_42_20_match


theorem leaf_122_45_0 (hp : 0 < (Q2.transData.getD 45 []).length)
    (j : Nat) (hj : j < (repChars.getD 122 []).length)
    (hq : (normIsRep.getD 122 []).getD j false = true) :
    species (Q2.reps (⟨45, by decide⟩ : Fin 148)) (colE2 ⟨45, by decide⟩ 0 hp)
        (rowE2 (⟨122, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨45, by decide⟩ : Fin 148))
        (colE1 ⟨45, by decide⟩ 0 (transLenTr ⟨45, by decide⟩ 0 hp))
        (rowE1 (⟨122, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨122, by decide⟩ : Fin 148) ⟨45, by decide⟩ _
      (validAt ⟨122, by decide⟩ (listedAt ⟨122, by decide⟩ hj))
      (colE1 ⟨45, by decide⟩ 0 (transLenTr ⟨45, by decide⟩ 0 hp)) T122_45
      hfix122_45 hinj122_45 hcardT122_45
      (fun i => conj_mem_of_fixedPoints _ _ (T122_45 i) (hfix122_45 i) _)
      ⟨122, by decide⟩ ⟨45, by decide⟩ _
      (Q2.validAt ⟨122, by decide⟩ (Q2.listedAt ⟨122, by decide⟩
        (alnCheck_rep ⟨122, by decide⟩ hj hq).1))
      (colE2 ⟨45, by decide⟩ 0 hp) Q2.T122_45_2 Q2.hfix122_45_2 Q2.hinj122_45_2
      Q2.hcardT122_45_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T122_45_2 i) (Q2.hfix122_45_2 i) _)
      colCert_122_45_0.hD ?_).symm
  rw [alnId_122 j hj]


theorem leaf_122_45_1 (hp : 1 < (Q2.transData.getD 45 []).length)
    (j : Nat) (hj : j < (repChars.getD 122 []).length)
    (hq : (normIsRep.getD 122 []).getD j false = true) :
    species (Q2.reps (⟨45, by decide⟩ : Fin 148)) (colE2 ⟨45, by decide⟩ 1 hp)
        (rowE2 (⟨122, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨45, by decide⟩ : Fin 148))
        (colE1 ⟨45, by decide⟩ 1 (transLenTr ⟨45, by decide⟩ 1 hp))
        (rowE1 (⟨122, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨122, by decide⟩ : Fin 148) ⟨45, by decide⟩ _
      (validAt ⟨122, by decide⟩ (listedAt ⟨122, by decide⟩ hj))
      (colE1 ⟨45, by decide⟩ 1 (transLenTr ⟨45, by decide⟩ 1 hp)) T122_45
      hfix122_45 hinj122_45 hcardT122_45
      (fun i => conj_mem_of_fixedPoints _ _ (T122_45 i) (hfix122_45 i) _)
      ⟨122, by decide⟩ ⟨45, by decide⟩ _
      (Q2.validAt ⟨122, by decide⟩ (Q2.listedAt ⟨122, by decide⟩
        (alnCheck_rep ⟨122, by decide⟩ hj hq).1))
      (colE2 ⟨45, by decide⟩ 1 hp) Q2.T122_45_2 Q2.hfix122_45_2 Q2.hinj122_45_2
      Q2.hcardT122_45_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T122_45_2 i) (Q2.hfix122_45_2 i) _)
      colCert_122_45_1.hD ?_).symm
  rw [alnId_122 j hj]


theorem leaf_122_45_2 (hp : 2 < (Q2.transData.getD 45 []).length)
    (j : Nat) (hj : j < (repChars.getD 122 []).length)
    (hq : (normIsRep.getD 122 []).getD j false = true) :
    species (Q2.reps (⟨45, by decide⟩ : Fin 148)) (colE2 ⟨45, by decide⟩ 2 hp)
        (rowE2 (⟨122, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨45, by decide⟩ : Fin 148))
        (colE1 ⟨45, by decide⟩ 2 (transLenTr ⟨45, by decide⟩ 2 hp))
        (rowE1 (⟨122, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨122, by decide⟩ : Fin 148) ⟨45, by decide⟩ _
      (validAt ⟨122, by decide⟩ (listedAt ⟨122, by decide⟩ hj))
      (colE1 ⟨45, by decide⟩ 2 (transLenTr ⟨45, by decide⟩ 2 hp)) T122_45
      hfix122_45 hinj122_45 hcardT122_45
      (fun i => conj_mem_of_fixedPoints _ _ (T122_45 i) (hfix122_45 i) _)
      ⟨122, by decide⟩ ⟨45, by decide⟩ _
      (Q2.validAt ⟨122, by decide⟩ (Q2.listedAt ⟨122, by decide⟩
        (alnCheck_rep ⟨122, by decide⟩ hj hq).1))
      (colE2 ⟨45, by decide⟩ 2 hp) Q2.T122_45_2 Q2.hfix122_45_2 Q2.hinj122_45_2
      Q2.hcardT122_45_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T122_45_2 i) (Q2.hfix122_45_2 i) _)
      colCert_122_45_2.hD ?_).symm
  rw [alnId_122 j hj]


theorem leaf_122_45_3 (hp : 3 < (Q2.transData.getD 45 []).length)
    (j : Nat) (hj : j < (repChars.getD 122 []).length)
    (hq : (normIsRep.getD 122 []).getD j false = true) :
    species (Q2.reps (⟨45, by decide⟩ : Fin 148)) (colE2 ⟨45, by decide⟩ 3 hp)
        (rowE2 (⟨122, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨45, by decide⟩ : Fin 148))
        (colE1 ⟨45, by decide⟩ 3 (transLenTr ⟨45, by decide⟩ 3 hp))
        (rowE1 (⟨122, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨122, by decide⟩ : Fin 148) ⟨45, by decide⟩ _
      (validAt ⟨122, by decide⟩ (listedAt ⟨122, by decide⟩ hj))
      (colE1 ⟨45, by decide⟩ 3 (transLenTr ⟨45, by decide⟩ 3 hp)) T122_45
      hfix122_45 hinj122_45 hcardT122_45
      (fun i => conj_mem_of_fixedPoints _ _ (T122_45 i) (hfix122_45 i) _)
      ⟨122, by decide⟩ ⟨45, by decide⟩ _
      (Q2.validAt ⟨122, by decide⟩ (Q2.listedAt ⟨122, by decide⟩
        (alnCheck_rep ⟨122, by decide⟩ hj hq).1))
      (colE2 ⟨45, by decide⟩ 3 hp) Q2.T122_45_2 Q2.hfix122_45_2 Q2.hinj122_45_2
      Q2.hcardT122_45_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T122_45_2 i) (Q2.hfix122_45_2 i) _)
      colCert_122_45_3.hD ?_).symm
  rw [alnId_122 j hj]


theorem leaf_122_45_4 (hp : 4 < (Q2.transData.getD 45 []).length)
    (j : Nat) (hj : j < (repChars.getD 122 []).length)
    (hq : (normIsRep.getD 122 []).getD j false = true) :
    species (Q2.reps (⟨45, by decide⟩ : Fin 148)) (colE2 ⟨45, by decide⟩ 4 hp)
        (rowE2 (⟨122, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨45, by decide⟩ : Fin 148))
        (colE1 ⟨45, by decide⟩ 4 (transLenTr ⟨45, by decide⟩ 4 hp))
        (rowE1 (⟨122, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨122, by decide⟩ : Fin 148) ⟨45, by decide⟩ _
      (validAt ⟨122, by decide⟩ (listedAt ⟨122, by decide⟩ hj))
      (colE1 ⟨45, by decide⟩ 4 (transLenTr ⟨45, by decide⟩ 4 hp)) T122_45
      hfix122_45 hinj122_45 hcardT122_45
      (fun i => conj_mem_of_fixedPoints _ _ (T122_45 i) (hfix122_45 i) _)
      ⟨122, by decide⟩ ⟨45, by decide⟩ _
      (Q2.validAt ⟨122, by decide⟩ (Q2.listedAt ⟨122, by decide⟩
        (alnCheck_rep ⟨122, by decide⟩ hj hq).1))
      (colE2 ⟨45, by decide⟩ 4 hp) Q2.T122_45_2 Q2.hfix122_45_2 Q2.hinj122_45_2
      Q2.hcardT122_45_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T122_45_2 i) (Q2.hfix122_45_2 i) _)
      colCert_122_45_4.hD ?_).symm
  rw [alnId_122 j hj]


theorem leaf_122_45_5 (hp : 5 < (Q2.transData.getD 45 []).length)
    (j : Nat) (hj : j < (repChars.getD 122 []).length)
    (hq : (normIsRep.getD 122 []).getD j false = true) :
    species (Q2.reps (⟨45, by decide⟩ : Fin 148)) (colE2 ⟨45, by decide⟩ 5 hp)
        (rowE2 (⟨122, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨45, by decide⟩ : Fin 148))
        (colE1 ⟨45, by decide⟩ 5 (transLenTr ⟨45, by decide⟩ 5 hp))
        (rowE1 (⟨122, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨122, by decide⟩ : Fin 148) ⟨45, by decide⟩ _
      (validAt ⟨122, by decide⟩ (listedAt ⟨122, by decide⟩ hj))
      (colE1 ⟨45, by decide⟩ 5 (transLenTr ⟨45, by decide⟩ 5 hp)) T122_45
      hfix122_45 hinj122_45 hcardT122_45
      (fun i => conj_mem_of_fixedPoints _ _ (T122_45 i) (hfix122_45 i) _)
      ⟨122, by decide⟩ ⟨45, by decide⟩ _
      (Q2.validAt ⟨122, by decide⟩ (Q2.listedAt ⟨122, by decide⟩
        (alnCheck_rep ⟨122, by decide⟩ hj hq).1))
      (colE2 ⟨45, by decide⟩ 5 hp) Q2.T122_45_2 Q2.hfix122_45_2 Q2.hinj122_45_2
      Q2.hcardT122_45_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T122_45_2 i) (Q2.hfix122_45_2 i) _)
      ?_).symm
  rw [show colData1 (⟨122, by decide⟩ : Fin 148)
        ((colE1 ⟨45, by decide⟩ 5 (transLenTr ⟨45, by decide⟩ 5 hp) : ↥(reps ⟨45, by decide⟩)) : Coordinate 1)
        T122_45 = colFn colCertDiv_122_45_5.D1 (m := 5) from colCertDiv_122_45_5.bind1,
    show colData2 (⟨122, by decide⟩ : Fin 148)
        ((colE2 ⟨45, by decide⟩ 5 hp : ↥(Q2.reps ⟨45, by decide⟩)) : Coordinate 2)
        Q2.T122_45_2 = colFn colCertDiv_122_45_5.D2 (m := 5) from colCertDiv_122_45_5.bind2]
  rw [alnId_122 j hj]
  exact fastcode_of_div ⟨122, by decide⟩ _ _ _
    ((alnId_122 j hj) ▸ Q2.listedAt (⟨122, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨122, by decide⟩ : Fin 148) hj hq).1) colCertDiv_122_45_5_match


theorem leaf_122_45_10 (hp : 10 < (Q2.transData.getD 45 []).length)
    (j : Nat) (hj : j < (repChars.getD 122 []).length)
    (hq : (normIsRep.getD 122 []).getD j false = true) :
    species (Q2.reps (⟨45, by decide⟩ : Fin 148)) (colE2 ⟨45, by decide⟩ 10 hp)
        (rowE2 (⟨122, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨45, by decide⟩ : Fin 148))
        (colE1 ⟨45, by decide⟩ 10 (transLenTr ⟨45, by decide⟩ 10 hp))
        (rowE1 (⟨122, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨122, by decide⟩ : Fin 148) ⟨45, by decide⟩ _
      (validAt ⟨122, by decide⟩ (listedAt ⟨122, by decide⟩ hj))
      (colE1 ⟨45, by decide⟩ 10 (transLenTr ⟨45, by decide⟩ 10 hp)) T122_45
      hfix122_45 hinj122_45 hcardT122_45
      (fun i => conj_mem_of_fixedPoints _ _ (T122_45 i) (hfix122_45 i) _)
      ⟨122, by decide⟩ ⟨45, by decide⟩ _
      (Q2.validAt ⟨122, by decide⟩ (Q2.listedAt ⟨122, by decide⟩
        (alnCheck_rep ⟨122, by decide⟩ hj hq).1))
      (colE2 ⟨45, by decide⟩ 10 hp) Q2.T122_45_2 Q2.hfix122_45_2 Q2.hinj122_45_2
      Q2.hcardT122_45_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T122_45_2 i) (Q2.hfix122_45_2 i) _)
      ?_).symm
  rw [show colData1 (⟨122, by decide⟩ : Fin 148)
        ((colE1 ⟨45, by decide⟩ 10 (transLenTr ⟨45, by decide⟩ 10 hp) : ↥(reps ⟨45, by decide⟩)) : Coordinate 1)
        T122_45 = colFn colCertDiv_122_45_10.D1 (m := 5) from colCertDiv_122_45_10.bind1,
    show colData2 (⟨122, by decide⟩ : Fin 148)
        ((colE2 ⟨45, by decide⟩ 10 hp : ↥(Q2.reps ⟨45, by decide⟩)) : Coordinate 2)
        Q2.T122_45_2 = colFn colCertDiv_122_45_10.D2 (m := 5) from colCertDiv_122_45_10.bind2]
  rw [alnId_122 j hj]
  exact fastcode_of_div ⟨122, by decide⟩ _ _ _
    ((alnId_122 j hj) ▸ Q2.listedAt (⟨122, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨122, by decide⟩ : Fin 148) hj hq).1) colCertDiv_122_45_10_match


theorem leaf_122_45_15 (hp : 15 < (Q2.transData.getD 45 []).length)
    (j : Nat) (hj : j < (repChars.getD 122 []).length)
    (hq : (normIsRep.getD 122 []).getD j false = true) :
    species (Q2.reps (⟨45, by decide⟩ : Fin 148)) (colE2 ⟨45, by decide⟩ 15 hp)
        (rowE2 (⟨122, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨45, by decide⟩ : Fin 148))
        (colE1 ⟨45, by decide⟩ 15 (transLenTr ⟨45, by decide⟩ 15 hp))
        (rowE1 (⟨122, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨122, by decide⟩ : Fin 148) ⟨45, by decide⟩ _
      (validAt ⟨122, by decide⟩ (listedAt ⟨122, by decide⟩ hj))
      (colE1 ⟨45, by decide⟩ 15 (transLenTr ⟨45, by decide⟩ 15 hp)) T122_45
      hfix122_45 hinj122_45 hcardT122_45
      (fun i => conj_mem_of_fixedPoints _ _ (T122_45 i) (hfix122_45 i) _)
      ⟨122, by decide⟩ ⟨45, by decide⟩ _
      (Q2.validAt ⟨122, by decide⟩ (Q2.listedAt ⟨122, by decide⟩
        (alnCheck_rep ⟨122, by decide⟩ hj hq).1))
      (colE2 ⟨45, by decide⟩ 15 hp) Q2.T122_45_2 Q2.hfix122_45_2 Q2.hinj122_45_2
      Q2.hcardT122_45_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T122_45_2 i) (Q2.hfix122_45_2 i) _)
      colCert_122_45_15.hD ?_).symm
  rw [alnId_122 j hj]


theorem leaf_122_45_20 (hp : 20 < (Q2.transData.getD 45 []).length)
    (j : Nat) (hj : j < (repChars.getD 122 []).length)
    (hq : (normIsRep.getD 122 []).getD j false = true) :
    species (Q2.reps (⟨45, by decide⟩ : Fin 148)) (colE2 ⟨45, by decide⟩ 20 hp)
        (rowE2 (⟨122, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨45, by decide⟩ : Fin 148))
        (colE1 ⟨45, by decide⟩ 20 (transLenTr ⟨45, by decide⟩ 20 hp))
        (rowE1 (⟨122, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨122, by decide⟩ : Fin 148) ⟨45, by decide⟩ _
      (validAt ⟨122, by decide⟩ (listedAt ⟨122, by decide⟩ hj))
      (colE1 ⟨45, by decide⟩ 20 (transLenTr ⟨45, by decide⟩ 20 hp)) T122_45
      hfix122_45 hinj122_45 hcardT122_45
      (fun i => conj_mem_of_fixedPoints _ _ (T122_45 i) (hfix122_45 i) _)
      ⟨122, by decide⟩ ⟨45, by decide⟩ _
      (Q2.validAt ⟨122, by decide⟩ (Q2.listedAt ⟨122, by decide⟩
        (alnCheck_rep ⟨122, by decide⟩ hj hq).1))
      (colE2 ⟨45, by decide⟩ 20 hp) Q2.T122_45_2 Q2.hfix122_45_2 Q2.hinj122_45_2
      Q2.hcardT122_45_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T122_45_2 i) (Q2.hfix122_45_2 i) _)
      ?_).symm
  rw [show colData1 (⟨122, by decide⟩ : Fin 148)
        ((colE1 ⟨45, by decide⟩ 20 (transLenTr ⟨45, by decide⟩ 20 hp) : ↥(reps ⟨45, by decide⟩)) : Coordinate 1)
        T122_45 = colFn colCertDiv_122_45_20.D1 (m := 5) from colCertDiv_122_45_20.bind1,
    show colData2 (⟨122, by decide⟩ : Fin 148)
        ((colE2 ⟨45, by decide⟩ 20 hp : ↥(Q2.reps ⟨45, by decide⟩)) : Coordinate 2)
        Q2.T122_45_2 = colFn colCertDiv_122_45_20.D2 (m := 5) from colCertDiv_122_45_20.bind2]
  rw [alnId_122 j hj]
  exact fastcode_of_div ⟨122, by decide⟩ _ _ _
    ((alnId_122 j hj) ▸ Q2.listedAt (⟨122, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨122, by decide⟩ : Fin 148) hj hq).1) colCertDiv_122_45_20_match


theorem leaf_122_49_0 (hp : 0 < (Q2.transData.getD 49 []).length)
    (j : Nat) (hj : j < (repChars.getD 122 []).length)
    (hq : (normIsRep.getD 122 []).getD j false = true) :
    species (Q2.reps (⟨49, by decide⟩ : Fin 148)) (colE2 ⟨49, by decide⟩ 0 hp)
        (rowE2 (⟨122, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨49, by decide⟩ : Fin 148))
        (colE1 ⟨49, by decide⟩ 0 (transLenTr ⟨49, by decide⟩ 0 hp))
        (rowE1 (⟨122, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨122, by decide⟩ : Fin 148) ⟨49, by decide⟩ _
      (validAt ⟨122, by decide⟩ (listedAt ⟨122, by decide⟩ hj))
      (colE1 ⟨49, by decide⟩ 0 (transLenTr ⟨49, by decide⟩ 0 hp)) T122_49
      hfix122_49 hinj122_49 hcardT122_49
      (fun i => conj_mem_of_fixedPoints _ _ (T122_49 i) (hfix122_49 i) _)
      ⟨122, by decide⟩ ⟨49, by decide⟩ _
      (Q2.validAt ⟨122, by decide⟩ (Q2.listedAt ⟨122, by decide⟩
        (alnCheck_rep ⟨122, by decide⟩ hj hq).1))
      (colE2 ⟨49, by decide⟩ 0 hp) Q2.T122_49_2 Q2.hfix122_49_2 Q2.hinj122_49_2
      Q2.hcardT122_49_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T122_49_2 i) (Q2.hfix122_49_2 i) _)
      colCert_122_49_0.hD ?_).symm
  rw [alnId_122 j hj]


theorem leaf_122_49_1 (hp : 1 < (Q2.transData.getD 49 []).length)
    (j : Nat) (hj : j < (repChars.getD 122 []).length)
    (hq : (normIsRep.getD 122 []).getD j false = true) :
    species (Q2.reps (⟨49, by decide⟩ : Fin 148)) (colE2 ⟨49, by decide⟩ 1 hp)
        (rowE2 (⟨122, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨49, by decide⟩ : Fin 148))
        (colE1 ⟨49, by decide⟩ 1 (transLenTr ⟨49, by decide⟩ 1 hp))
        (rowE1 (⟨122, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨122, by decide⟩ : Fin 148) ⟨49, by decide⟩ _
      (validAt ⟨122, by decide⟩ (listedAt ⟨122, by decide⟩ hj))
      (colE1 ⟨49, by decide⟩ 1 (transLenTr ⟨49, by decide⟩ 1 hp)) T122_49
      hfix122_49 hinj122_49 hcardT122_49
      (fun i => conj_mem_of_fixedPoints _ _ (T122_49 i) (hfix122_49 i) _)
      ⟨122, by decide⟩ ⟨49, by decide⟩ _
      (Q2.validAt ⟨122, by decide⟩ (Q2.listedAt ⟨122, by decide⟩
        (alnCheck_rep ⟨122, by decide⟩ hj hq).1))
      (colE2 ⟨49, by decide⟩ 1 hp) Q2.T122_49_2 Q2.hfix122_49_2 Q2.hinj122_49_2
      Q2.hcardT122_49_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T122_49_2 i) (Q2.hfix122_49_2 i) _)
      colCert_122_49_1.hD ?_).symm
  rw [alnId_122 j hj]


theorem leaf_122_49_2 (hp : 2 < (Q2.transData.getD 49 []).length)
    (j : Nat) (hj : j < (repChars.getD 122 []).length)
    (hq : (normIsRep.getD 122 []).getD j false = true) :
    species (Q2.reps (⟨49, by decide⟩ : Fin 148)) (colE2 ⟨49, by decide⟩ 2 hp)
        (rowE2 (⟨122, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨49, by decide⟩ : Fin 148))
        (colE1 ⟨49, by decide⟩ 2 (transLenTr ⟨49, by decide⟩ 2 hp))
        (rowE1 (⟨122, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨122, by decide⟩ : Fin 148) ⟨49, by decide⟩ _
      (validAt ⟨122, by decide⟩ (listedAt ⟨122, by decide⟩ hj))
      (colE1 ⟨49, by decide⟩ 2 (transLenTr ⟨49, by decide⟩ 2 hp)) T122_49
      hfix122_49 hinj122_49 hcardT122_49
      (fun i => conj_mem_of_fixedPoints _ _ (T122_49 i) (hfix122_49 i) _)
      ⟨122, by decide⟩ ⟨49, by decide⟩ _
      (Q2.validAt ⟨122, by decide⟩ (Q2.listedAt ⟨122, by decide⟩
        (alnCheck_rep ⟨122, by decide⟩ hj hq).1))
      (colE2 ⟨49, by decide⟩ 2 hp) Q2.T122_49_2 Q2.hfix122_49_2 Q2.hinj122_49_2
      Q2.hcardT122_49_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T122_49_2 i) (Q2.hfix122_49_2 i) _)
      colCert_122_49_2.hD ?_).symm
  rw [alnId_122 j hj]


theorem leaf_122_49_3 (hp : 3 < (Q2.transData.getD 49 []).length)
    (j : Nat) (hj : j < (repChars.getD 122 []).length)
    (hq : (normIsRep.getD 122 []).getD j false = true) :
    species (Q2.reps (⟨49, by decide⟩ : Fin 148)) (colE2 ⟨49, by decide⟩ 3 hp)
        (rowE2 (⟨122, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨49, by decide⟩ : Fin 148))
        (colE1 ⟨49, by decide⟩ 3 (transLenTr ⟨49, by decide⟩ 3 hp))
        (rowE1 (⟨122, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨122, by decide⟩ : Fin 148) ⟨49, by decide⟩ _
      (validAt ⟨122, by decide⟩ (listedAt ⟨122, by decide⟩ hj))
      (colE1 ⟨49, by decide⟩ 3 (transLenTr ⟨49, by decide⟩ 3 hp)) T122_49
      hfix122_49 hinj122_49 hcardT122_49
      (fun i => conj_mem_of_fixedPoints _ _ (T122_49 i) (hfix122_49 i) _)
      ⟨122, by decide⟩ ⟨49, by decide⟩ _
      (Q2.validAt ⟨122, by decide⟩ (Q2.listedAt ⟨122, by decide⟩
        (alnCheck_rep ⟨122, by decide⟩ hj hq).1))
      (colE2 ⟨49, by decide⟩ 3 hp) Q2.T122_49_2 Q2.hfix122_49_2 Q2.hinj122_49_2
      Q2.hcardT122_49_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T122_49_2 i) (Q2.hfix122_49_2 i) _)
      colCert_122_49_3.hD ?_).symm
  rw [alnId_122 j hj]


theorem leaf_122_49_4 (hp : 4 < (Q2.transData.getD 49 []).length)
    (j : Nat) (hj : j < (repChars.getD 122 []).length)
    (hq : (normIsRep.getD 122 []).getD j false = true) :
    species (Q2.reps (⟨49, by decide⟩ : Fin 148)) (colE2 ⟨49, by decide⟩ 4 hp)
        (rowE2 (⟨122, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨49, by decide⟩ : Fin 148))
        (colE1 ⟨49, by decide⟩ 4 (transLenTr ⟨49, by decide⟩ 4 hp))
        (rowE1 (⟨122, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨122, by decide⟩ : Fin 148) ⟨49, by decide⟩ _
      (validAt ⟨122, by decide⟩ (listedAt ⟨122, by decide⟩ hj))
      (colE1 ⟨49, by decide⟩ 4 (transLenTr ⟨49, by decide⟩ 4 hp)) T122_49
      hfix122_49 hinj122_49 hcardT122_49
      (fun i => conj_mem_of_fixedPoints _ _ (T122_49 i) (hfix122_49 i) _)
      ⟨122, by decide⟩ ⟨49, by decide⟩ _
      (Q2.validAt ⟨122, by decide⟩ (Q2.listedAt ⟨122, by decide⟩
        (alnCheck_rep ⟨122, by decide⟩ hj hq).1))
      (colE2 ⟨49, by decide⟩ 4 hp) Q2.T122_49_2 Q2.hfix122_49_2 Q2.hinj122_49_2
      Q2.hcardT122_49_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T122_49_2 i) (Q2.hfix122_49_2 i) _)
      colCert_122_49_4.hD ?_).symm
  rw [alnId_122 j hj]


theorem leaf_122_49_5 (hp : 5 < (Q2.transData.getD 49 []).length)
    (j : Nat) (hj : j < (repChars.getD 122 []).length)
    (hq : (normIsRep.getD 122 []).getD j false = true) :
    species (Q2.reps (⟨49, by decide⟩ : Fin 148)) (colE2 ⟨49, by decide⟩ 5 hp)
        (rowE2 (⟨122, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨49, by decide⟩ : Fin 148))
        (colE1 ⟨49, by decide⟩ 5 (transLenTr ⟨49, by decide⟩ 5 hp))
        (rowE1 (⟨122, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨122, by decide⟩ : Fin 148) ⟨49, by decide⟩ _
      (validAt ⟨122, by decide⟩ (listedAt ⟨122, by decide⟩ hj))
      (colE1 ⟨49, by decide⟩ 5 (transLenTr ⟨49, by decide⟩ 5 hp)) T122_49
      hfix122_49 hinj122_49 hcardT122_49
      (fun i => conj_mem_of_fixedPoints _ _ (T122_49 i) (hfix122_49 i) _)
      ⟨122, by decide⟩ ⟨49, by decide⟩ _
      (Q2.validAt ⟨122, by decide⟩ (Q2.listedAt ⟨122, by decide⟩
        (alnCheck_rep ⟨122, by decide⟩ hj hq).1))
      (colE2 ⟨49, by decide⟩ 5 hp) Q2.T122_49_2 Q2.hfix122_49_2 Q2.hinj122_49_2
      Q2.hcardT122_49_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T122_49_2 i) (Q2.hfix122_49_2 i) _)
      colCert_122_49_5.hD ?_).symm
  rw [alnId_122 j hj]


theorem leaf_122_49_10 (hp : 10 < (Q2.transData.getD 49 []).length)
    (j : Nat) (hj : j < (repChars.getD 122 []).length)
    (hq : (normIsRep.getD 122 []).getD j false = true) :
    species (Q2.reps (⟨49, by decide⟩ : Fin 148)) (colE2 ⟨49, by decide⟩ 10 hp)
        (rowE2 (⟨122, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨49, by decide⟩ : Fin 148))
        (colE1 ⟨49, by decide⟩ 10 (transLenTr ⟨49, by decide⟩ 10 hp))
        (rowE1 (⟨122, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨122, by decide⟩ : Fin 148) ⟨49, by decide⟩ _
      (validAt ⟨122, by decide⟩ (listedAt ⟨122, by decide⟩ hj))
      (colE1 ⟨49, by decide⟩ 10 (transLenTr ⟨49, by decide⟩ 10 hp)) T122_49
      hfix122_49 hinj122_49 hcardT122_49
      (fun i => conj_mem_of_fixedPoints _ _ (T122_49 i) (hfix122_49 i) _)
      ⟨122, by decide⟩ ⟨49, by decide⟩ _
      (Q2.validAt ⟨122, by decide⟩ (Q2.listedAt ⟨122, by decide⟩
        (alnCheck_rep ⟨122, by decide⟩ hj hq).1))
      (colE2 ⟨49, by decide⟩ 10 hp) Q2.T122_49_2 Q2.hfix122_49_2 Q2.hinj122_49_2
      Q2.hcardT122_49_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T122_49_2 i) (Q2.hfix122_49_2 i) _)
      ?_).symm
  rw [show colData1 (⟨122, by decide⟩ : Fin 148)
        ((colE1 ⟨49, by decide⟩ 10 (transLenTr ⟨49, by decide⟩ 10 hp) : ↥(reps ⟨49, by decide⟩)) : Coordinate 1)
        T122_49 = colFn colCertDiv_122_49_10.D1 (m := 5) from colCertDiv_122_49_10.bind1,
    show colData2 (⟨122, by decide⟩ : Fin 148)
        ((colE2 ⟨49, by decide⟩ 10 hp : ↥(Q2.reps ⟨49, by decide⟩)) : Coordinate 2)
        Q2.T122_49_2 = colFn colCertDiv_122_49_10.D2 (m := 5) from colCertDiv_122_49_10.bind2]
  rw [alnId_122 j hj]
  exact fastcode_of_div ⟨122, by decide⟩ _ _ _
    ((alnId_122 j hj) ▸ Q2.listedAt (⟨122, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨122, by decide⟩ : Fin 148) hj hq).1) colCertDiv_122_49_10_match


theorem leaf_122_49_15 (hp : 15 < (Q2.transData.getD 49 []).length)
    (j : Nat) (hj : j < (repChars.getD 122 []).length)
    (hq : (normIsRep.getD 122 []).getD j false = true) :
    species (Q2.reps (⟨49, by decide⟩ : Fin 148)) (colE2 ⟨49, by decide⟩ 15 hp)
        (rowE2 (⟨122, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨49, by decide⟩ : Fin 148))
        (colE1 ⟨49, by decide⟩ 15 (transLenTr ⟨49, by decide⟩ 15 hp))
        (rowE1 (⟨122, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨122, by decide⟩ : Fin 148) ⟨49, by decide⟩ _
      (validAt ⟨122, by decide⟩ (listedAt ⟨122, by decide⟩ hj))
      (colE1 ⟨49, by decide⟩ 15 (transLenTr ⟨49, by decide⟩ 15 hp)) T122_49
      hfix122_49 hinj122_49 hcardT122_49
      (fun i => conj_mem_of_fixedPoints _ _ (T122_49 i) (hfix122_49 i) _)
      ⟨122, by decide⟩ ⟨49, by decide⟩ _
      (Q2.validAt ⟨122, by decide⟩ (Q2.listedAt ⟨122, by decide⟩
        (alnCheck_rep ⟨122, by decide⟩ hj hq).1))
      (colE2 ⟨49, by decide⟩ 15 hp) Q2.T122_49_2 Q2.hfix122_49_2 Q2.hinj122_49_2
      Q2.hcardT122_49_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T122_49_2 i) (Q2.hfix122_49_2 i) _)
      ?_).symm
  rw [show colData1 (⟨122, by decide⟩ : Fin 148)
        ((colE1 ⟨49, by decide⟩ 15 (transLenTr ⟨49, by decide⟩ 15 hp) : ↥(reps ⟨49, by decide⟩)) : Coordinate 1)
        T122_49 = colFn colCertDiv_122_49_15.D1 (m := 5) from colCertDiv_122_49_15.bind1,
    show colData2 (⟨122, by decide⟩ : Fin 148)
        ((colE2 ⟨49, by decide⟩ 15 hp : ↥(Q2.reps ⟨49, by decide⟩)) : Coordinate 2)
        Q2.T122_49_2 = colFn colCertDiv_122_49_15.D2 (m := 5) from colCertDiv_122_49_15.bind2]
  rw [alnId_122 j hj]
  exact fastcode_of_div ⟨122, by decide⟩ _ _ _
    ((alnId_122 j hj) ▸ Q2.listedAt (⟨122, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨122, by decide⟩ : Fin 148) hj hq).1) colCertDiv_122_49_15_match


theorem leaf_122_49_20 (hp : 20 < (Q2.transData.getD 49 []).length)
    (j : Nat) (hj : j < (repChars.getD 122 []).length)
    (hq : (normIsRep.getD 122 []).getD j false = true) :
    species (Q2.reps (⟨49, by decide⟩ : Fin 148)) (colE2 ⟨49, by decide⟩ 20 hp)
        (rowE2 (⟨122, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨49, by decide⟩ : Fin 148))
        (colE1 ⟨49, by decide⟩ 20 (transLenTr ⟨49, by decide⟩ 20 hp))
        (rowE1 (⟨122, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨122, by decide⟩ : Fin 148) ⟨49, by decide⟩ _
      (validAt ⟨122, by decide⟩ (listedAt ⟨122, by decide⟩ hj))
      (colE1 ⟨49, by decide⟩ 20 (transLenTr ⟨49, by decide⟩ 20 hp)) T122_49
      hfix122_49 hinj122_49 hcardT122_49
      (fun i => conj_mem_of_fixedPoints _ _ (T122_49 i) (hfix122_49 i) _)
      ⟨122, by decide⟩ ⟨49, by decide⟩ _
      (Q2.validAt ⟨122, by decide⟩ (Q2.listedAt ⟨122, by decide⟩
        (alnCheck_rep ⟨122, by decide⟩ hj hq).1))
      (colE2 ⟨49, by decide⟩ 20 hp) Q2.T122_49_2 Q2.hfix122_49_2 Q2.hinj122_49_2
      Q2.hcardT122_49_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T122_49_2 i) (Q2.hfix122_49_2 i) _)
      ?_).symm
  rw [show colData1 (⟨122, by decide⟩ : Fin 148)
        ((colE1 ⟨49, by decide⟩ 20 (transLenTr ⟨49, by decide⟩ 20 hp) : ↥(reps ⟨49, by decide⟩)) : Coordinate 1)
        T122_49 = colFn colCertDiv_122_49_20.D1 (m := 5) from colCertDiv_122_49_20.bind1,
    show colData2 (⟨122, by decide⟩ : Fin 148)
        ((colE2 ⟨49, by decide⟩ 20 hp : ↥(Q2.reps ⟨49, by decide⟩)) : Coordinate 2)
        Q2.T122_49_2 = colFn colCertDiv_122_49_20.D2 (m := 5) from colCertDiv_122_49_20.bind2]
  rw [alnId_122 j hj]
  exact fastcode_of_div ⟨122, by decide⟩ _ _ _
    ((alnId_122 j hj) ▸ Q2.listedAt (⟨122, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨122, by decide⟩ : Fin 148) hj hq).1) colCertDiv_122_49_20_match


theorem leaf_122_53_0 (hp : 0 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 122 []).length)
    (hq : (normIsRep.getD 122 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 0 hp)
        (rowE2 (⟨122, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 0 (transLenTr ⟨53, by decide⟩ 0 hp))
        (rowE1 (⟨122, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨122, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨122, by decide⟩ (listedAt ⟨122, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 0 (transLenTr ⟨53, by decide⟩ 0 hp)) T122_53
      hfix122_53 hinj122_53 hcardT122_53
      (fun i => conj_mem_of_fixedPoints _ _ (T122_53 i) (hfix122_53 i) _)
      ⟨122, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨122, by decide⟩ (Q2.listedAt ⟨122, by decide⟩
        (alnCheck_rep ⟨122, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 0 hp) Q2.T122_53_2 Q2.hfix122_53_2 Q2.hinj122_53_2
      Q2.hcardT122_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T122_53_2 i) (Q2.hfix122_53_2 i) _)
      colCert_122_53_0.hD ?_).symm
  rw [alnId_122 j hj]


theorem leaf_122_53_1 (hp : 1 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 122 []).length)
    (hq : (normIsRep.getD 122 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 1 hp)
        (rowE2 (⟨122, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 1 (transLenTr ⟨53, by decide⟩ 1 hp))
        (rowE1 (⟨122, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨122, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨122, by decide⟩ (listedAt ⟨122, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 1 (transLenTr ⟨53, by decide⟩ 1 hp)) T122_53
      hfix122_53 hinj122_53 hcardT122_53
      (fun i => conj_mem_of_fixedPoints _ _ (T122_53 i) (hfix122_53 i) _)
      ⟨122, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨122, by decide⟩ (Q2.listedAt ⟨122, by decide⟩
        (alnCheck_rep ⟨122, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 1 hp) Q2.T122_53_2 Q2.hfix122_53_2 Q2.hinj122_53_2
      Q2.hcardT122_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T122_53_2 i) (Q2.hfix122_53_2 i) _)
      colCert_122_53_1.hD ?_).symm
  rw [alnId_122 j hj]


theorem leaf_122_53_2 (hp : 2 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 122 []).length)
    (hq : (normIsRep.getD 122 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 2 hp)
        (rowE2 (⟨122, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 2 (transLenTr ⟨53, by decide⟩ 2 hp))
        (rowE1 (⟨122, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨122, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨122, by decide⟩ (listedAt ⟨122, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 2 (transLenTr ⟨53, by decide⟩ 2 hp)) T122_53
      hfix122_53 hinj122_53 hcardT122_53
      (fun i => conj_mem_of_fixedPoints _ _ (T122_53 i) (hfix122_53 i) _)
      ⟨122, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨122, by decide⟩ (Q2.listedAt ⟨122, by decide⟩
        (alnCheck_rep ⟨122, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 2 hp) Q2.T122_53_2 Q2.hfix122_53_2 Q2.hinj122_53_2
      Q2.hcardT122_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T122_53_2 i) (Q2.hfix122_53_2 i) _)
      colCert_122_53_2.hD ?_).symm
  rw [alnId_122 j hj]


theorem leaf_122_53_3 (hp : 3 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 122 []).length)
    (hq : (normIsRep.getD 122 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 3 hp)
        (rowE2 (⟨122, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 3 (transLenTr ⟨53, by decide⟩ 3 hp))
        (rowE1 (⟨122, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨122, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨122, by decide⟩ (listedAt ⟨122, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 3 (transLenTr ⟨53, by decide⟩ 3 hp)) T122_53
      hfix122_53 hinj122_53 hcardT122_53
      (fun i => conj_mem_of_fixedPoints _ _ (T122_53 i) (hfix122_53 i) _)
      ⟨122, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨122, by decide⟩ (Q2.listedAt ⟨122, by decide⟩
        (alnCheck_rep ⟨122, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 3 hp) Q2.T122_53_2 Q2.hfix122_53_2 Q2.hinj122_53_2
      Q2.hcardT122_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T122_53_2 i) (Q2.hfix122_53_2 i) _)
      colCert_122_53_3.hD ?_).symm
  rw [alnId_122 j hj]


theorem leaf_122_53_4 (hp : 4 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 122 []).length)
    (hq : (normIsRep.getD 122 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 4 hp)
        (rowE2 (⟨122, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 4 (transLenTr ⟨53, by decide⟩ 4 hp))
        (rowE1 (⟨122, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨122, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨122, by decide⟩ (listedAt ⟨122, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 4 (transLenTr ⟨53, by decide⟩ 4 hp)) T122_53
      hfix122_53 hinj122_53 hcardT122_53
      (fun i => conj_mem_of_fixedPoints _ _ (T122_53 i) (hfix122_53 i) _)
      ⟨122, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨122, by decide⟩ (Q2.listedAt ⟨122, by decide⟩
        (alnCheck_rep ⟨122, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 4 hp) Q2.T122_53_2 Q2.hfix122_53_2 Q2.hinj122_53_2
      Q2.hcardT122_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T122_53_2 i) (Q2.hfix122_53_2 i) _)
      colCert_122_53_4.hD ?_).symm
  rw [alnId_122 j hj]


theorem leaf_122_53_5 (hp : 5 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 122 []).length)
    (hq : (normIsRep.getD 122 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 5 hp)
        (rowE2 (⟨122, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 5 (transLenTr ⟨53, by decide⟩ 5 hp))
        (rowE1 (⟨122, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨122, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨122, by decide⟩ (listedAt ⟨122, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 5 (transLenTr ⟨53, by decide⟩ 5 hp)) T122_53
      hfix122_53 hinj122_53 hcardT122_53
      (fun i => conj_mem_of_fixedPoints _ _ (T122_53 i) (hfix122_53 i) _)
      ⟨122, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨122, by decide⟩ (Q2.listedAt ⟨122, by decide⟩
        (alnCheck_rep ⟨122, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 5 hp) Q2.T122_53_2 Q2.hfix122_53_2 Q2.hinj122_53_2
      Q2.hcardT122_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T122_53_2 i) (Q2.hfix122_53_2 i) _)
      colCert_122_53_5.hD ?_).symm
  rw [alnId_122 j hj]


theorem leaf_122_53_10 (hp : 10 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 122 []).length)
    (hq : (normIsRep.getD 122 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 10 hp)
        (rowE2 (⟨122, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 10 (transLenTr ⟨53, by decide⟩ 10 hp))
        (rowE1 (⟨122, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨122, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨122, by decide⟩ (listedAt ⟨122, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 10 (transLenTr ⟨53, by decide⟩ 10 hp)) T122_53
      hfix122_53 hinj122_53 hcardT122_53
      (fun i => conj_mem_of_fixedPoints _ _ (T122_53 i) (hfix122_53 i) _)
      ⟨122, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨122, by decide⟩ (Q2.listedAt ⟨122, by decide⟩
        (alnCheck_rep ⟨122, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 10 hp) Q2.T122_53_2 Q2.hfix122_53_2 Q2.hinj122_53_2
      Q2.hcardT122_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T122_53_2 i) (Q2.hfix122_53_2 i) _)
      colCert_122_53_10.hD ?_).symm
  rw [alnId_122 j hj]


theorem leaf_122_53_15 (hp : 15 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 122 []).length)
    (hq : (normIsRep.getD 122 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 15 hp)
        (rowE2 (⟨122, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 15 (transLenTr ⟨53, by decide⟩ 15 hp))
        (rowE1 (⟨122, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨122, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨122, by decide⟩ (listedAt ⟨122, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 15 (transLenTr ⟨53, by decide⟩ 15 hp)) T122_53
      hfix122_53 hinj122_53 hcardT122_53
      (fun i => conj_mem_of_fixedPoints _ _ (T122_53 i) (hfix122_53 i) _)
      ⟨122, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨122, by decide⟩ (Q2.listedAt ⟨122, by decide⟩
        (alnCheck_rep ⟨122, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 15 hp) Q2.T122_53_2 Q2.hfix122_53_2 Q2.hinj122_53_2
      Q2.hcardT122_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T122_53_2 i) (Q2.hfix122_53_2 i) _)
      colCert_122_53_15.hD ?_).symm
  rw [alnId_122 j hj]


theorem leaf_122_53_20 (hp : 20 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 122 []).length)
    (hq : (normIsRep.getD 122 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 20 hp)
        (rowE2 (⟨122, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 20 (transLenTr ⟨53, by decide⟩ 20 hp))
        (rowE1 (⟨122, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨122, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨122, by decide⟩ (listedAt ⟨122, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 20 (transLenTr ⟨53, by decide⟩ 20 hp)) T122_53
      hfix122_53 hinj122_53 hcardT122_53
      (fun i => conj_mem_of_fixedPoints _ _ (T122_53 i) (hfix122_53 i) _)
      ⟨122, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨122, by decide⟩ (Q2.listedAt ⟨122, by decide⟩
        (alnCheck_rep ⟨122, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 20 hp) Q2.T122_53_2 Q2.hfix122_53_2 Q2.hinj122_53_2
      Q2.hcardT122_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T122_53_2 i) (Q2.hfix122_53_2 i) _)
      colCert_122_53_20.hD ?_).symm
  rw [alnId_122 j hj]


theorem leaf_122_81_0 (hp : 0 < (Q2.transData.getD 81 []).length)
    (j : Nat) (hj : j < (repChars.getD 122 []).length)
    (hq : (normIsRep.getD 122 []).getD j false = true) :
    species (Q2.reps (⟨81, by decide⟩ : Fin 148)) (colE2 ⟨81, by decide⟩ 0 hp)
        (rowE2 (⟨122, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨81, by decide⟩ : Fin 148))
        (colE1 ⟨81, by decide⟩ 0 (transLenTr ⟨81, by decide⟩ 0 hp))
        (rowE1 (⟨122, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨122, by decide⟩ : Fin 148) ⟨81, by decide⟩ _
      (validAt ⟨122, by decide⟩ (listedAt ⟨122, by decide⟩ hj))
      (colE1 ⟨81, by decide⟩ 0 (transLenTr ⟨81, by decide⟩ 0 hp)) T122_81
      hfix122_81 hinj122_81 hcardT122_81
      (fun i => conj_mem_of_fixedPoints _ _ (T122_81 i) (hfix122_81 i) _)
      ⟨122, by decide⟩ ⟨81, by decide⟩ _
      (Q2.validAt ⟨122, by decide⟩ (Q2.listedAt ⟨122, by decide⟩
        (alnCheck_rep ⟨122, by decide⟩ hj hq).1))
      (colE2 ⟨81, by decide⟩ 0 hp) Q2.T122_81_2 Q2.hfix122_81_2 Q2.hinj122_81_2
      Q2.hcardT122_81_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T122_81_2 i) (Q2.hfix122_81_2 i) _)
      colCert_122_81_0.hD ?_).symm
  rw [alnId_122 j hj]


theorem leaf_122_81_1 (hp : 1 < (Q2.transData.getD 81 []).length)
    (j : Nat) (hj : j < (repChars.getD 122 []).length)
    (hq : (normIsRep.getD 122 []).getD j false = true) :
    species (Q2.reps (⟨81, by decide⟩ : Fin 148)) (colE2 ⟨81, by decide⟩ 1 hp)
        (rowE2 (⟨122, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨81, by decide⟩ : Fin 148))
        (colE1 ⟨81, by decide⟩ 1 (transLenTr ⟨81, by decide⟩ 1 hp))
        (rowE1 (⟨122, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨122, by decide⟩ : Fin 148) ⟨81, by decide⟩ _
      (validAt ⟨122, by decide⟩ (listedAt ⟨122, by decide⟩ hj))
      (colE1 ⟨81, by decide⟩ 1 (transLenTr ⟨81, by decide⟩ 1 hp)) T122_81
      hfix122_81 hinj122_81 hcardT122_81
      (fun i => conj_mem_of_fixedPoints _ _ (T122_81 i) (hfix122_81 i) _)
      ⟨122, by decide⟩ ⟨81, by decide⟩ _
      (Q2.validAt ⟨122, by decide⟩ (Q2.listedAt ⟨122, by decide⟩
        (alnCheck_rep ⟨122, by decide⟩ hj hq).1))
      (colE2 ⟨81, by decide⟩ 1 hp) Q2.T122_81_2 Q2.hfix122_81_2 Q2.hinj122_81_2
      Q2.hcardT122_81_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T122_81_2 i) (Q2.hfix122_81_2 i) _)
      colCert_122_81_1.hD ?_).symm
  rw [alnId_122 j hj]


theorem leaf_122_81_2 (hp : 2 < (Q2.transData.getD 81 []).length)
    (j : Nat) (hj : j < (repChars.getD 122 []).length)
    (hq : (normIsRep.getD 122 []).getD j false = true) :
    species (Q2.reps (⟨81, by decide⟩ : Fin 148)) (colE2 ⟨81, by decide⟩ 2 hp)
        (rowE2 (⟨122, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨81, by decide⟩ : Fin 148))
        (colE1 ⟨81, by decide⟩ 2 (transLenTr ⟨81, by decide⟩ 2 hp))
        (rowE1 (⟨122, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨122, by decide⟩ : Fin 148) ⟨81, by decide⟩ _
      (validAt ⟨122, by decide⟩ (listedAt ⟨122, by decide⟩ hj))
      (colE1 ⟨81, by decide⟩ 2 (transLenTr ⟨81, by decide⟩ 2 hp)) T122_81
      hfix122_81 hinj122_81 hcardT122_81
      (fun i => conj_mem_of_fixedPoints _ _ (T122_81 i) (hfix122_81 i) _)
      ⟨122, by decide⟩ ⟨81, by decide⟩ _
      (Q2.validAt ⟨122, by decide⟩ (Q2.listedAt ⟨122, by decide⟩
        (alnCheck_rep ⟨122, by decide⟩ hj hq).1))
      (colE2 ⟨81, by decide⟩ 2 hp) Q2.T122_81_2 Q2.hfix122_81_2 Q2.hinj122_81_2
      Q2.hcardT122_81_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T122_81_2 i) (Q2.hfix122_81_2 i) _)
      colCert_122_81_2.hD ?_).symm
  rw [alnId_122 j hj]


theorem leaf_122_81_3 (hp : 3 < (Q2.transData.getD 81 []).length)
    (j : Nat) (hj : j < (repChars.getD 122 []).length)
    (hq : (normIsRep.getD 122 []).getD j false = true) :
    species (Q2.reps (⟨81, by decide⟩ : Fin 148)) (colE2 ⟨81, by decide⟩ 3 hp)
        (rowE2 (⟨122, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨81, by decide⟩ : Fin 148))
        (colE1 ⟨81, by decide⟩ 3 (transLenTr ⟨81, by decide⟩ 3 hp))
        (rowE1 (⟨122, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨122, by decide⟩ : Fin 148) ⟨81, by decide⟩ _
      (validAt ⟨122, by decide⟩ (listedAt ⟨122, by decide⟩ hj))
      (colE1 ⟨81, by decide⟩ 3 (transLenTr ⟨81, by decide⟩ 3 hp)) T122_81
      hfix122_81 hinj122_81 hcardT122_81
      (fun i => conj_mem_of_fixedPoints _ _ (T122_81 i) (hfix122_81 i) _)
      ⟨122, by decide⟩ ⟨81, by decide⟩ _
      (Q2.validAt ⟨122, by decide⟩ (Q2.listedAt ⟨122, by decide⟩
        (alnCheck_rep ⟨122, by decide⟩ hj hq).1))
      (colE2 ⟨81, by decide⟩ 3 hp) Q2.T122_81_2 Q2.hfix122_81_2 Q2.hinj122_81_2
      Q2.hcardT122_81_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T122_81_2 i) (Q2.hfix122_81_2 i) _)
      colCert_122_81_3.hD ?_).symm
  rw [alnId_122 j hj]


theorem leaf_122_81_4 (hp : 4 < (Q2.transData.getD 81 []).length)
    (j : Nat) (hj : j < (repChars.getD 122 []).length)
    (hq : (normIsRep.getD 122 []).getD j false = true) :
    species (Q2.reps (⟨81, by decide⟩ : Fin 148)) (colE2 ⟨81, by decide⟩ 4 hp)
        (rowE2 (⟨122, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨81, by decide⟩ : Fin 148))
        (colE1 ⟨81, by decide⟩ 4 (transLenTr ⟨81, by decide⟩ 4 hp))
        (rowE1 (⟨122, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨122, by decide⟩ : Fin 148) ⟨81, by decide⟩ _
      (validAt ⟨122, by decide⟩ (listedAt ⟨122, by decide⟩ hj))
      (colE1 ⟨81, by decide⟩ 4 (transLenTr ⟨81, by decide⟩ 4 hp)) T122_81
      hfix122_81 hinj122_81 hcardT122_81
      (fun i => conj_mem_of_fixedPoints _ _ (T122_81 i) (hfix122_81 i) _)
      ⟨122, by decide⟩ ⟨81, by decide⟩ _
      (Q2.validAt ⟨122, by decide⟩ (Q2.listedAt ⟨122, by decide⟩
        (alnCheck_rep ⟨122, by decide⟩ hj hq).1))
      (colE2 ⟨81, by decide⟩ 4 hp) Q2.T122_81_2 Q2.hfix122_81_2 Q2.hinj122_81_2
      Q2.hcardT122_81_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T122_81_2 i) (Q2.hfix122_81_2 i) _)
      colCert_122_81_4.hD ?_).symm
  rw [alnId_122 j hj]


theorem leaf_122_81_5 (hp : 5 < (Q2.transData.getD 81 []).length)
    (j : Nat) (hj : j < (repChars.getD 122 []).length)
    (hq : (normIsRep.getD 122 []).getD j false = true) :
    species (Q2.reps (⟨81, by decide⟩ : Fin 148)) (colE2 ⟨81, by decide⟩ 5 hp)
        (rowE2 (⟨122, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨81, by decide⟩ : Fin 148))
        (colE1 ⟨81, by decide⟩ 5 (transLenTr ⟨81, by decide⟩ 5 hp))
        (rowE1 (⟨122, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨122, by decide⟩ : Fin 148) ⟨81, by decide⟩ _
      (validAt ⟨122, by decide⟩ (listedAt ⟨122, by decide⟩ hj))
      (colE1 ⟨81, by decide⟩ 5 (transLenTr ⟨81, by decide⟩ 5 hp)) T122_81
      hfix122_81 hinj122_81 hcardT122_81
      (fun i => conj_mem_of_fixedPoints _ _ (T122_81 i) (hfix122_81 i) _)
      ⟨122, by decide⟩ ⟨81, by decide⟩ _
      (Q2.validAt ⟨122, by decide⟩ (Q2.listedAt ⟨122, by decide⟩
        (alnCheck_rep ⟨122, by decide⟩ hj hq).1))
      (colE2 ⟨81, by decide⟩ 5 hp) Q2.T122_81_2 Q2.hfix122_81_2 Q2.hinj122_81_2
      Q2.hcardT122_81_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T122_81_2 i) (Q2.hfix122_81_2 i) _)
      ?_).symm
  rw [show colData1 (⟨122, by decide⟩ : Fin 148)
        ((colE1 ⟨81, by decide⟩ 5 (transLenTr ⟨81, by decide⟩ 5 hp) : ↥(reps ⟨81, by decide⟩)) : Coordinate 1)
        T122_81 = colFn colCertDiv_122_81_5.D1 (m := 5) from colCertDiv_122_81_5.bind1,
    show colData2 (⟨122, by decide⟩ : Fin 148)
        ((colE2 ⟨81, by decide⟩ 5 hp : ↥(Q2.reps ⟨81, by decide⟩)) : Coordinate 2)
        Q2.T122_81_2 = colFn colCertDiv_122_81_5.D2 (m := 5) from colCertDiv_122_81_5.bind2]
  rw [alnId_122 j hj]
  exact fastcode_of_div ⟨122, by decide⟩ _ _ _
    ((alnId_122 j hj) ▸ Q2.listedAt (⟨122, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨122, by decide⟩ : Fin 148) hj hq).1) colCertDiv_122_81_5_match


theorem leaf_122_81_10 (hp : 10 < (Q2.transData.getD 81 []).length)
    (j : Nat) (hj : j < (repChars.getD 122 []).length)
    (hq : (normIsRep.getD 122 []).getD j false = true) :
    species (Q2.reps (⟨81, by decide⟩ : Fin 148)) (colE2 ⟨81, by decide⟩ 10 hp)
        (rowE2 (⟨122, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨81, by decide⟩ : Fin 148))
        (colE1 ⟨81, by decide⟩ 10 (transLenTr ⟨81, by decide⟩ 10 hp))
        (rowE1 (⟨122, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨122, by decide⟩ : Fin 148) ⟨81, by decide⟩ _
      (validAt ⟨122, by decide⟩ (listedAt ⟨122, by decide⟩ hj))
      (colE1 ⟨81, by decide⟩ 10 (transLenTr ⟨81, by decide⟩ 10 hp)) T122_81
      hfix122_81 hinj122_81 hcardT122_81
      (fun i => conj_mem_of_fixedPoints _ _ (T122_81 i) (hfix122_81 i) _)
      ⟨122, by decide⟩ ⟨81, by decide⟩ _
      (Q2.validAt ⟨122, by decide⟩ (Q2.listedAt ⟨122, by decide⟩
        (alnCheck_rep ⟨122, by decide⟩ hj hq).1))
      (colE2 ⟨81, by decide⟩ 10 hp) Q2.T122_81_2 Q2.hfix122_81_2 Q2.hinj122_81_2
      Q2.hcardT122_81_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T122_81_2 i) (Q2.hfix122_81_2 i) _)
      ?_).symm
  rw [show colData1 (⟨122, by decide⟩ : Fin 148)
        ((colE1 ⟨81, by decide⟩ 10 (transLenTr ⟨81, by decide⟩ 10 hp) : ↥(reps ⟨81, by decide⟩)) : Coordinate 1)
        T122_81 = colFn colCertDiv_122_81_10.D1 (m := 5) from colCertDiv_122_81_10.bind1,
    show colData2 (⟨122, by decide⟩ : Fin 148)
        ((colE2 ⟨81, by decide⟩ 10 hp : ↥(Q2.reps ⟨81, by decide⟩)) : Coordinate 2)
        Q2.T122_81_2 = colFn colCertDiv_122_81_10.D2 (m := 5) from colCertDiv_122_81_10.bind2]
  rw [alnId_122 j hj]
  exact fastcode_of_div ⟨122, by decide⟩ _ _ _
    ((alnId_122 j hj) ▸ Q2.listedAt (⟨122, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨122, by decide⟩ : Fin 148) hj hq).1) colCertDiv_122_81_10_match


theorem leaf_122_81_15 (hp : 15 < (Q2.transData.getD 81 []).length)
    (j : Nat) (hj : j < (repChars.getD 122 []).length)
    (hq : (normIsRep.getD 122 []).getD j false = true) :
    species (Q2.reps (⟨81, by decide⟩ : Fin 148)) (colE2 ⟨81, by decide⟩ 15 hp)
        (rowE2 (⟨122, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨81, by decide⟩ : Fin 148))
        (colE1 ⟨81, by decide⟩ 15 (transLenTr ⟨81, by decide⟩ 15 hp))
        (rowE1 (⟨122, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨122, by decide⟩ : Fin 148) ⟨81, by decide⟩ _
      (validAt ⟨122, by decide⟩ (listedAt ⟨122, by decide⟩ hj))
      (colE1 ⟨81, by decide⟩ 15 (transLenTr ⟨81, by decide⟩ 15 hp)) T122_81
      hfix122_81 hinj122_81 hcardT122_81
      (fun i => conj_mem_of_fixedPoints _ _ (T122_81 i) (hfix122_81 i) _)
      ⟨122, by decide⟩ ⟨81, by decide⟩ _
      (Q2.validAt ⟨122, by decide⟩ (Q2.listedAt ⟨122, by decide⟩
        (alnCheck_rep ⟨122, by decide⟩ hj hq).1))
      (colE2 ⟨81, by decide⟩ 15 hp) Q2.T122_81_2 Q2.hfix122_81_2 Q2.hinj122_81_2
      Q2.hcardT122_81_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T122_81_2 i) (Q2.hfix122_81_2 i) _)
      ?_).symm
  rw [show colData1 (⟨122, by decide⟩ : Fin 148)
        ((colE1 ⟨81, by decide⟩ 15 (transLenTr ⟨81, by decide⟩ 15 hp) : ↥(reps ⟨81, by decide⟩)) : Coordinate 1)
        T122_81 = colFn colCertDiv_122_81_15.D1 (m := 5) from colCertDiv_122_81_15.bind1,
    show colData2 (⟨122, by decide⟩ : Fin 148)
        ((colE2 ⟨81, by decide⟩ 15 hp : ↥(Q2.reps ⟨81, by decide⟩)) : Coordinate 2)
        Q2.T122_81_2 = colFn colCertDiv_122_81_15.D2 (m := 5) from colCertDiv_122_81_15.bind2]
  rw [alnId_122 j hj]
  exact fastcode_of_div ⟨122, by decide⟩ _ _ _
    ((alnId_122 j hj) ▸ Q2.listedAt (⟨122, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨122, by decide⟩ : Fin 148) hj hq).1) colCertDiv_122_81_15_match


theorem leaf_122_81_20 (hp : 20 < (Q2.transData.getD 81 []).length)
    (j : Nat) (hj : j < (repChars.getD 122 []).length)
    (hq : (normIsRep.getD 122 []).getD j false = true) :
    species (Q2.reps (⟨81, by decide⟩ : Fin 148)) (colE2 ⟨81, by decide⟩ 20 hp)
        (rowE2 (⟨122, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨81, by decide⟩ : Fin 148))
        (colE1 ⟨81, by decide⟩ 20 (transLenTr ⟨81, by decide⟩ 20 hp))
        (rowE1 (⟨122, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨122, by decide⟩ : Fin 148) ⟨81, by decide⟩ _
      (validAt ⟨122, by decide⟩ (listedAt ⟨122, by decide⟩ hj))
      (colE1 ⟨81, by decide⟩ 20 (transLenTr ⟨81, by decide⟩ 20 hp)) T122_81
      hfix122_81 hinj122_81 hcardT122_81
      (fun i => conj_mem_of_fixedPoints _ _ (T122_81 i) (hfix122_81 i) _)
      ⟨122, by decide⟩ ⟨81, by decide⟩ _
      (Q2.validAt ⟨122, by decide⟩ (Q2.listedAt ⟨122, by decide⟩
        (alnCheck_rep ⟨122, by decide⟩ hj hq).1))
      (colE2 ⟨81, by decide⟩ 20 hp) Q2.T122_81_2 Q2.hfix122_81_2 Q2.hinj122_81_2
      Q2.hcardT122_81_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T122_81_2 i) (Q2.hfix122_81_2 i) _)
      ?_).symm
  rw [show colData1 (⟨122, by decide⟩ : Fin 148)
        ((colE1 ⟨81, by decide⟩ 20 (transLenTr ⟨81, by decide⟩ 20 hp) : ↥(reps ⟨81, by decide⟩)) : Coordinate 1)
        T122_81 = colFn colCertDiv_122_81_20.D1 (m := 5) from colCertDiv_122_81_20.bind1,
    show colData2 (⟨122, by decide⟩ : Fin 148)
        ((colE2 ⟨81, by decide⟩ 20 hp : ↥(Q2.reps ⟨81, by decide⟩)) : Coordinate 2)
        Q2.T122_81_2 = colFn colCertDiv_122_81_20.D2 (m := 5) from colCertDiv_122_81_20.bind2]
  rw [alnId_122 j hj]
  exact fastcode_of_div ⟨122, by decide⟩ _ _ _
    ((alnId_122 j hj) ▸ Q2.listedAt (⟨122, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨122, by decide⟩ : Fin 148) hj hq).1) colCertDiv_122_81_20_match


theorem leaf_122_90_0 (hp : 0 < (Q2.transData.getD 90 []).length)
    (j : Nat) (hj : j < (repChars.getD 122 []).length)
    (hq : (normIsRep.getD 122 []).getD j false = true) :
    species (Q2.reps (⟨90, by decide⟩ : Fin 148)) (colE2 ⟨90, by decide⟩ 0 hp)
        (rowE2 (⟨122, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨90, by decide⟩ : Fin 148))
        (colE1 ⟨90, by decide⟩ 0 (transLenTr ⟨90, by decide⟩ 0 hp))
        (rowE1 (⟨122, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨122, by decide⟩ : Fin 148) ⟨90, by decide⟩ _
      (validAt ⟨122, by decide⟩ (listedAt ⟨122, by decide⟩ hj))
      (colE1 ⟨90, by decide⟩ 0 (transLenTr ⟨90, by decide⟩ 0 hp)) T122_90
      hfix122_90 hinj122_90 hcardT122_90
      (fun i => conj_mem_of_fixedPoints _ _ (T122_90 i) (hfix122_90 i) _)
      ⟨122, by decide⟩ ⟨90, by decide⟩ _
      (Q2.validAt ⟨122, by decide⟩ (Q2.listedAt ⟨122, by decide⟩
        (alnCheck_rep ⟨122, by decide⟩ hj hq).1))
      (colE2 ⟨90, by decide⟩ 0 hp) Q2.T122_90_2 Q2.hfix122_90_2 Q2.hinj122_90_2
      Q2.hcardT122_90_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T122_90_2 i) (Q2.hfix122_90_2 i) _)
      colCert_122_90_0.hD ?_).symm
  rw [alnId_122 j hj]


theorem leaf_122_90_1 (hp : 1 < (Q2.transData.getD 90 []).length)
    (j : Nat) (hj : j < (repChars.getD 122 []).length)
    (hq : (normIsRep.getD 122 []).getD j false = true) :
    species (Q2.reps (⟨90, by decide⟩ : Fin 148)) (colE2 ⟨90, by decide⟩ 1 hp)
        (rowE2 (⟨122, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨90, by decide⟩ : Fin 148))
        (colE1 ⟨90, by decide⟩ 1 (transLenTr ⟨90, by decide⟩ 1 hp))
        (rowE1 (⟨122, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨122, by decide⟩ : Fin 148) ⟨90, by decide⟩ _
      (validAt ⟨122, by decide⟩ (listedAt ⟨122, by decide⟩ hj))
      (colE1 ⟨90, by decide⟩ 1 (transLenTr ⟨90, by decide⟩ 1 hp)) T122_90
      hfix122_90 hinj122_90 hcardT122_90
      (fun i => conj_mem_of_fixedPoints _ _ (T122_90 i) (hfix122_90 i) _)
      ⟨122, by decide⟩ ⟨90, by decide⟩ _
      (Q2.validAt ⟨122, by decide⟩ (Q2.listedAt ⟨122, by decide⟩
        (alnCheck_rep ⟨122, by decide⟩ hj hq).1))
      (colE2 ⟨90, by decide⟩ 1 hp) Q2.T122_90_2 Q2.hfix122_90_2 Q2.hinj122_90_2
      Q2.hcardT122_90_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T122_90_2 i) (Q2.hfix122_90_2 i) _)
      colCert_122_90_1.hD ?_).symm
  rw [alnId_122 j hj]


theorem leaf_122_90_2 (hp : 2 < (Q2.transData.getD 90 []).length)
    (j : Nat) (hj : j < (repChars.getD 122 []).length)
    (hq : (normIsRep.getD 122 []).getD j false = true) :
    species (Q2.reps (⟨90, by decide⟩ : Fin 148)) (colE2 ⟨90, by decide⟩ 2 hp)
        (rowE2 (⟨122, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨90, by decide⟩ : Fin 148))
        (colE1 ⟨90, by decide⟩ 2 (transLenTr ⟨90, by decide⟩ 2 hp))
        (rowE1 (⟨122, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨122, by decide⟩ : Fin 148) ⟨90, by decide⟩ _
      (validAt ⟨122, by decide⟩ (listedAt ⟨122, by decide⟩ hj))
      (colE1 ⟨90, by decide⟩ 2 (transLenTr ⟨90, by decide⟩ 2 hp)) T122_90
      hfix122_90 hinj122_90 hcardT122_90
      (fun i => conj_mem_of_fixedPoints _ _ (T122_90 i) (hfix122_90 i) _)
      ⟨122, by decide⟩ ⟨90, by decide⟩ _
      (Q2.validAt ⟨122, by decide⟩ (Q2.listedAt ⟨122, by decide⟩
        (alnCheck_rep ⟨122, by decide⟩ hj hq).1))
      (colE2 ⟨90, by decide⟩ 2 hp) Q2.T122_90_2 Q2.hfix122_90_2 Q2.hinj122_90_2
      Q2.hcardT122_90_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T122_90_2 i) (Q2.hfix122_90_2 i) _)
      colCert_122_90_2.hD ?_).symm
  rw [alnId_122 j hj]


theorem leaf_122_90_3 (hp : 3 < (Q2.transData.getD 90 []).length)
    (j : Nat) (hj : j < (repChars.getD 122 []).length)
    (hq : (normIsRep.getD 122 []).getD j false = true) :
    species (Q2.reps (⟨90, by decide⟩ : Fin 148)) (colE2 ⟨90, by decide⟩ 3 hp)
        (rowE2 (⟨122, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨90, by decide⟩ : Fin 148))
        (colE1 ⟨90, by decide⟩ 3 (transLenTr ⟨90, by decide⟩ 3 hp))
        (rowE1 (⟨122, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨122, by decide⟩ : Fin 148) ⟨90, by decide⟩ _
      (validAt ⟨122, by decide⟩ (listedAt ⟨122, by decide⟩ hj))
      (colE1 ⟨90, by decide⟩ 3 (transLenTr ⟨90, by decide⟩ 3 hp)) T122_90
      hfix122_90 hinj122_90 hcardT122_90
      (fun i => conj_mem_of_fixedPoints _ _ (T122_90 i) (hfix122_90 i) _)
      ⟨122, by decide⟩ ⟨90, by decide⟩ _
      (Q2.validAt ⟨122, by decide⟩ (Q2.listedAt ⟨122, by decide⟩
        (alnCheck_rep ⟨122, by decide⟩ hj hq).1))
      (colE2 ⟨90, by decide⟩ 3 hp) Q2.T122_90_2 Q2.hfix122_90_2 Q2.hinj122_90_2
      Q2.hcardT122_90_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T122_90_2 i) (Q2.hfix122_90_2 i) _)
      colCert_122_90_3.hD ?_).symm
  rw [alnId_122 j hj]


theorem leaf_122_90_4 (hp : 4 < (Q2.transData.getD 90 []).length)
    (j : Nat) (hj : j < (repChars.getD 122 []).length)
    (hq : (normIsRep.getD 122 []).getD j false = true) :
    species (Q2.reps (⟨90, by decide⟩ : Fin 148)) (colE2 ⟨90, by decide⟩ 4 hp)
        (rowE2 (⟨122, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨90, by decide⟩ : Fin 148))
        (colE1 ⟨90, by decide⟩ 4 (transLenTr ⟨90, by decide⟩ 4 hp))
        (rowE1 (⟨122, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨122, by decide⟩ : Fin 148) ⟨90, by decide⟩ _
      (validAt ⟨122, by decide⟩ (listedAt ⟨122, by decide⟩ hj))
      (colE1 ⟨90, by decide⟩ 4 (transLenTr ⟨90, by decide⟩ 4 hp)) T122_90
      hfix122_90 hinj122_90 hcardT122_90
      (fun i => conj_mem_of_fixedPoints _ _ (T122_90 i) (hfix122_90 i) _)
      ⟨122, by decide⟩ ⟨90, by decide⟩ _
      (Q2.validAt ⟨122, by decide⟩ (Q2.listedAt ⟨122, by decide⟩
        (alnCheck_rep ⟨122, by decide⟩ hj hq).1))
      (colE2 ⟨90, by decide⟩ 4 hp) Q2.T122_90_2 Q2.hfix122_90_2 Q2.hinj122_90_2
      Q2.hcardT122_90_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T122_90_2 i) (Q2.hfix122_90_2 i) _)
      colCert_122_90_4.hD ?_).symm
  rw [alnId_122 j hj]


theorem leaf_122_90_5 (hp : 5 < (Q2.transData.getD 90 []).length)
    (j : Nat) (hj : j < (repChars.getD 122 []).length)
    (hq : (normIsRep.getD 122 []).getD j false = true) :
    species (Q2.reps (⟨90, by decide⟩ : Fin 148)) (colE2 ⟨90, by decide⟩ 5 hp)
        (rowE2 (⟨122, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨90, by decide⟩ : Fin 148))
        (colE1 ⟨90, by decide⟩ 5 (transLenTr ⟨90, by decide⟩ 5 hp))
        (rowE1 (⟨122, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨122, by decide⟩ : Fin 148) ⟨90, by decide⟩ _
      (validAt ⟨122, by decide⟩ (listedAt ⟨122, by decide⟩ hj))
      (colE1 ⟨90, by decide⟩ 5 (transLenTr ⟨90, by decide⟩ 5 hp)) T122_90
      hfix122_90 hinj122_90 hcardT122_90
      (fun i => conj_mem_of_fixedPoints _ _ (T122_90 i) (hfix122_90 i) _)
      ⟨122, by decide⟩ ⟨90, by decide⟩ _
      (Q2.validAt ⟨122, by decide⟩ (Q2.listedAt ⟨122, by decide⟩
        (alnCheck_rep ⟨122, by decide⟩ hj hq).1))
      (colE2 ⟨90, by decide⟩ 5 hp) Q2.T122_90_2 Q2.hfix122_90_2 Q2.hinj122_90_2
      Q2.hcardT122_90_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T122_90_2 i) (Q2.hfix122_90_2 i) _)
      colCert_122_90_5.hD ?_).symm
  rw [alnId_122 j hj]


theorem leaf_122_90_10 (hp : 10 < (Q2.transData.getD 90 []).length)
    (j : Nat) (hj : j < (repChars.getD 122 []).length)
    (hq : (normIsRep.getD 122 []).getD j false = true) :
    species (Q2.reps (⟨90, by decide⟩ : Fin 148)) (colE2 ⟨90, by decide⟩ 10 hp)
        (rowE2 (⟨122, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨90, by decide⟩ : Fin 148))
        (colE1 ⟨90, by decide⟩ 10 (transLenTr ⟨90, by decide⟩ 10 hp))
        (rowE1 (⟨122, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨122, by decide⟩ : Fin 148) ⟨90, by decide⟩ _
      (validAt ⟨122, by decide⟩ (listedAt ⟨122, by decide⟩ hj))
      (colE1 ⟨90, by decide⟩ 10 (transLenTr ⟨90, by decide⟩ 10 hp)) T122_90
      hfix122_90 hinj122_90 hcardT122_90
      (fun i => conj_mem_of_fixedPoints _ _ (T122_90 i) (hfix122_90 i) _)
      ⟨122, by decide⟩ ⟨90, by decide⟩ _
      (Q2.validAt ⟨122, by decide⟩ (Q2.listedAt ⟨122, by decide⟩
        (alnCheck_rep ⟨122, by decide⟩ hj hq).1))
      (colE2 ⟨90, by decide⟩ 10 hp) Q2.T122_90_2 Q2.hfix122_90_2 Q2.hinj122_90_2
      Q2.hcardT122_90_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T122_90_2 i) (Q2.hfix122_90_2 i) _)
      colCert_122_90_10.hD ?_).symm
  rw [alnId_122 j hj]


theorem leaf_122_90_15 (hp : 15 < (Q2.transData.getD 90 []).length)
    (j : Nat) (hj : j < (repChars.getD 122 []).length)
    (hq : (normIsRep.getD 122 []).getD j false = true) :
    species (Q2.reps (⟨90, by decide⟩ : Fin 148)) (colE2 ⟨90, by decide⟩ 15 hp)
        (rowE2 (⟨122, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨90, by decide⟩ : Fin 148))
        (colE1 ⟨90, by decide⟩ 15 (transLenTr ⟨90, by decide⟩ 15 hp))
        (rowE1 (⟨122, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨122, by decide⟩ : Fin 148) ⟨90, by decide⟩ _
      (validAt ⟨122, by decide⟩ (listedAt ⟨122, by decide⟩ hj))
      (colE1 ⟨90, by decide⟩ 15 (transLenTr ⟨90, by decide⟩ 15 hp)) T122_90
      hfix122_90 hinj122_90 hcardT122_90
      (fun i => conj_mem_of_fixedPoints _ _ (T122_90 i) (hfix122_90 i) _)
      ⟨122, by decide⟩ ⟨90, by decide⟩ _
      (Q2.validAt ⟨122, by decide⟩ (Q2.listedAt ⟨122, by decide⟩
        (alnCheck_rep ⟨122, by decide⟩ hj hq).1))
      (colE2 ⟨90, by decide⟩ 15 hp) Q2.T122_90_2 Q2.hfix122_90_2 Q2.hinj122_90_2
      Q2.hcardT122_90_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T122_90_2 i) (Q2.hfix122_90_2 i) _)
      colCert_122_90_15.hD ?_).symm
  rw [alnId_122 j hj]


theorem leaf_122_90_20 (hp : 20 < (Q2.transData.getD 90 []).length)
    (j : Nat) (hj : j < (repChars.getD 122 []).length)
    (hq : (normIsRep.getD 122 []).getD j false = true) :
    species (Q2.reps (⟨90, by decide⟩ : Fin 148)) (colE2 ⟨90, by decide⟩ 20 hp)
        (rowE2 (⟨122, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨90, by decide⟩ : Fin 148))
        (colE1 ⟨90, by decide⟩ 20 (transLenTr ⟨90, by decide⟩ 20 hp))
        (rowE1 (⟨122, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨122, by decide⟩ : Fin 148) ⟨90, by decide⟩ _
      (validAt ⟨122, by decide⟩ (listedAt ⟨122, by decide⟩ hj))
      (colE1 ⟨90, by decide⟩ 20 (transLenTr ⟨90, by decide⟩ 20 hp)) T122_90
      hfix122_90 hinj122_90 hcardT122_90
      (fun i => conj_mem_of_fixedPoints _ _ (T122_90 i) (hfix122_90 i) _)
      ⟨122, by decide⟩ ⟨90, by decide⟩ _
      (Q2.validAt ⟨122, by decide⟩ (Q2.listedAt ⟨122, by decide⟩
        (alnCheck_rep ⟨122, by decide⟩ hj hq).1))
      (colE2 ⟨90, by decide⟩ 20 hp) Q2.T122_90_2 Q2.hfix122_90_2 Q2.hinj122_90_2
      Q2.hcardT122_90_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T122_90_2 i) (Q2.hfix122_90_2 i) _)
      colCert_122_90_20.hD ?_).symm
  rw [alnId_122 j hj]


theorem leaf_122_90_25 (hp : 25 < (Q2.transData.getD 90 []).length)
    (j : Nat) (hj : j < (repChars.getD 122 []).length)
    (hq : (normIsRep.getD 122 []).getD j false = true) :
    species (Q2.reps (⟨90, by decide⟩ : Fin 148)) (colE2 ⟨90, by decide⟩ 25 hp)
        (rowE2 (⟨122, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨90, by decide⟩ : Fin 148))
        (colE1 ⟨90, by decide⟩ 25 (transLenTr ⟨90, by decide⟩ 25 hp))
        (rowE1 (⟨122, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨122, by decide⟩ : Fin 148) ⟨90, by decide⟩ _
      (validAt ⟨122, by decide⟩ (listedAt ⟨122, by decide⟩ hj))
      (colE1 ⟨90, by decide⟩ 25 (transLenTr ⟨90, by decide⟩ 25 hp)) T122_90
      hfix122_90 hinj122_90 hcardT122_90
      (fun i => conj_mem_of_fixedPoints _ _ (T122_90 i) (hfix122_90 i) _)
      ⟨122, by decide⟩ ⟨90, by decide⟩ _
      (Q2.validAt ⟨122, by decide⟩ (Q2.listedAt ⟨122, by decide⟩
        (alnCheck_rep ⟨122, by decide⟩ hj hq).1))
      (colE2 ⟨90, by decide⟩ 25 hp) Q2.T122_90_2 Q2.hfix122_90_2 Q2.hinj122_90_2
      Q2.hcardT122_90_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T122_90_2 i) (Q2.hfix122_90_2 i) _)
      ?_).symm
  rw [show colData1 (⟨122, by decide⟩ : Fin 148)
        ((colE1 ⟨90, by decide⟩ 25 (transLenTr ⟨90, by decide⟩ 25 hp) : ↥(reps ⟨90, by decide⟩)) : Coordinate 1)
        T122_90 = colFn colCertDiv_122_90_25.D1 (m := 5) from colCertDiv_122_90_25.bind1,
    show colData2 (⟨122, by decide⟩ : Fin 148)
        ((colE2 ⟨90, by decide⟩ 25 hp : ↥(Q2.reps ⟨90, by decide⟩)) : Coordinate 2)
        Q2.T122_90_2 = colFn colCertDiv_122_90_25.D2 (m := 5) from colCertDiv_122_90_25.bind2]
  rw [alnId_122 j hj]
  exact fastcode_of_div ⟨122, by decide⟩ _ _ _
    ((alnId_122 j hj) ▸ Q2.listedAt (⟨122, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨122, by decide⟩ : Fin 148) hj hq).1) colCertDiv_122_90_25_match


theorem leaf_122_90_50 (hp : 50 < (Q2.transData.getD 90 []).length)
    (j : Nat) (hj : j < (repChars.getD 122 []).length)
    (hq : (normIsRep.getD 122 []).getD j false = true) :
    species (Q2.reps (⟨90, by decide⟩ : Fin 148)) (colE2 ⟨90, by decide⟩ 50 hp)
        (rowE2 (⟨122, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨90, by decide⟩ : Fin 148))
        (colE1 ⟨90, by decide⟩ 50 (transLenTr ⟨90, by decide⟩ 50 hp))
        (rowE1 (⟨122, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨122, by decide⟩ : Fin 148) ⟨90, by decide⟩ _
      (validAt ⟨122, by decide⟩ (listedAt ⟨122, by decide⟩ hj))
      (colE1 ⟨90, by decide⟩ 50 (transLenTr ⟨90, by decide⟩ 50 hp)) T122_90
      hfix122_90 hinj122_90 hcardT122_90
      (fun i => conj_mem_of_fixedPoints _ _ (T122_90 i) (hfix122_90 i) _)
      ⟨122, by decide⟩ ⟨90, by decide⟩ _
      (Q2.validAt ⟨122, by decide⟩ (Q2.listedAt ⟨122, by decide⟩
        (alnCheck_rep ⟨122, by decide⟩ hj hq).1))
      (colE2 ⟨90, by decide⟩ 50 hp) Q2.T122_90_2 Q2.hfix122_90_2 Q2.hinj122_90_2
      Q2.hcardT122_90_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T122_90_2 i) (Q2.hfix122_90_2 i) _)
      ?_).symm
  rw [show colData1 (⟨122, by decide⟩ : Fin 148)
        ((colE1 ⟨90, by decide⟩ 50 (transLenTr ⟨90, by decide⟩ 50 hp) : ↥(reps ⟨90, by decide⟩)) : Coordinate 1)
        T122_90 = colFn colCertDiv_122_90_50.D1 (m := 5) from colCertDiv_122_90_50.bind1,
    show colData2 (⟨122, by decide⟩ : Fin 148)
        ((colE2 ⟨90, by decide⟩ 50 hp : ↥(Q2.reps ⟨90, by decide⟩)) : Coordinate 2)
        Q2.T122_90_2 = colFn colCertDiv_122_90_50.D2 (m := 5) from colCertDiv_122_90_50.bind2]
  rw [alnId_122 j hj]
  exact fastcode_of_div ⟨122, by decide⟩ _ _ _
    ((alnId_122 j hj) ▸ Q2.listedAt (⟨122, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨122, by decide⟩ : Fin 148) hj hq).1) colCertDiv_122_90_50_match


theorem leaf_122_90_75 (hp : 75 < (Q2.transData.getD 90 []).length)
    (j : Nat) (hj : j < (repChars.getD 122 []).length)
    (hq : (normIsRep.getD 122 []).getD j false = true) :
    species (Q2.reps (⟨90, by decide⟩ : Fin 148)) (colE2 ⟨90, by decide⟩ 75 hp)
        (rowE2 (⟨122, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨90, by decide⟩ : Fin 148))
        (colE1 ⟨90, by decide⟩ 75 (transLenTr ⟨90, by decide⟩ 75 hp))
        (rowE1 (⟨122, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨122, by decide⟩ : Fin 148) ⟨90, by decide⟩ _
      (validAt ⟨122, by decide⟩ (listedAt ⟨122, by decide⟩ hj))
      (colE1 ⟨90, by decide⟩ 75 (transLenTr ⟨90, by decide⟩ 75 hp)) T122_90
      hfix122_90 hinj122_90 hcardT122_90
      (fun i => conj_mem_of_fixedPoints _ _ (T122_90 i) (hfix122_90 i) _)
      ⟨122, by decide⟩ ⟨90, by decide⟩ _
      (Q2.validAt ⟨122, by decide⟩ (Q2.listedAt ⟨122, by decide⟩
        (alnCheck_rep ⟨122, by decide⟩ hj hq).1))
      (colE2 ⟨90, by decide⟩ 75 hp) Q2.T122_90_2 Q2.hfix122_90_2 Q2.hinj122_90_2
      Q2.hcardT122_90_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T122_90_2 i) (Q2.hfix122_90_2 i) _)
      ?_).symm
  rw [show colData1 (⟨122, by decide⟩ : Fin 148)
        ((colE1 ⟨90, by decide⟩ 75 (transLenTr ⟨90, by decide⟩ 75 hp) : ↥(reps ⟨90, by decide⟩)) : Coordinate 1)
        T122_90 = colFn colCertDiv_122_90_75.D1 (m := 5) from colCertDiv_122_90_75.bind1,
    show colData2 (⟨122, by decide⟩ : Fin 148)
        ((colE2 ⟨90, by decide⟩ 75 hp : ↥(Q2.reps ⟨90, by decide⟩)) : Coordinate 2)
        Q2.T122_90_2 = colFn colCertDiv_122_90_75.D2 (m := 5) from colCertDiv_122_90_75.bind2]
  rw [alnId_122 j hj]
  exact fastcode_of_div ⟨122, by decide⟩ _ _ _
    ((alnId_122 j hj) ▸ Q2.listedAt (⟨122, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨122, by decide⟩ : Fin 148) hj hq).1) colCertDiv_122_90_75_match


theorem leaf_122_90_100 (hp : 100 < (Q2.transData.getD 90 []).length)
    (j : Nat) (hj : j < (repChars.getD 122 []).length)
    (hq : (normIsRep.getD 122 []).getD j false = true) :
    species (Q2.reps (⟨90, by decide⟩ : Fin 148)) (colE2 ⟨90, by decide⟩ 100 hp)
        (rowE2 (⟨122, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨90, by decide⟩ : Fin 148))
        (colE1 ⟨90, by decide⟩ 100 (transLenTr ⟨90, by decide⟩ 100 hp))
        (rowE1 (⟨122, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨122, by decide⟩ : Fin 148) ⟨90, by decide⟩ _
      (validAt ⟨122, by decide⟩ (listedAt ⟨122, by decide⟩ hj))
      (colE1 ⟨90, by decide⟩ 100 (transLenTr ⟨90, by decide⟩ 100 hp)) T122_90
      hfix122_90 hinj122_90 hcardT122_90
      (fun i => conj_mem_of_fixedPoints _ _ (T122_90 i) (hfix122_90 i) _)
      ⟨122, by decide⟩ ⟨90, by decide⟩ _
      (Q2.validAt ⟨122, by decide⟩ (Q2.listedAt ⟨122, by decide⟩
        (alnCheck_rep ⟨122, by decide⟩ hj hq).1))
      (colE2 ⟨90, by decide⟩ 100 hp) Q2.T122_90_2 Q2.hfix122_90_2 Q2.hinj122_90_2
      Q2.hcardT122_90_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T122_90_2 i) (Q2.hfix122_90_2 i) _)
      ?_).symm
  rw [show colData1 (⟨122, by decide⟩ : Fin 148)
        ((colE1 ⟨90, by decide⟩ 100 (transLenTr ⟨90, by decide⟩ 100 hp) : ↥(reps ⟨90, by decide⟩)) : Coordinate 1)
        T122_90 = colFn colCertDiv_122_90_100.D1 (m := 5) from colCertDiv_122_90_100.bind1,
    show colData2 (⟨122, by decide⟩ : Fin 148)
        ((colE2 ⟨90, by decide⟩ 100 hp : ↥(Q2.reps ⟨90, by decide⟩)) : Coordinate 2)
        Q2.T122_90_2 = colFn colCertDiv_122_90_100.D2 (m := 5) from colCertDiv_122_90_100.bind2]
  rw [alnId_122 j hj]
  exact fastcode_of_div ⟨122, by decide⟩ _ _ _
    ((alnId_122 j hj) ▸ Q2.listedAt (⟨122, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨122, by decide⟩ : Fin 148) hj hq).1) colCertDiv_122_90_100_match


theorem leaf_122_98_0 (hp : 0 < (Q2.transData.getD 98 []).length)
    (j : Nat) (hj : j < (repChars.getD 122 []).length)
    (hq : (normIsRep.getD 122 []).getD j false = true) :
    species (Q2.reps (⟨98, by decide⟩ : Fin 148)) (colE2 ⟨98, by decide⟩ 0 hp)
        (rowE2 (⟨122, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨98, by decide⟩ : Fin 148))
        (colE1 ⟨98, by decide⟩ 0 (transLenTr ⟨98, by decide⟩ 0 hp))
        (rowE1 (⟨122, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨122, by decide⟩ : Fin 148) ⟨98, by decide⟩ _
      (validAt ⟨122, by decide⟩ (listedAt ⟨122, by decide⟩ hj))
      (colE1 ⟨98, by decide⟩ 0 (transLenTr ⟨98, by decide⟩ 0 hp)) T122_98
      hfix122_98 hinj122_98 hcardT122_98
      (fun i => conj_mem_of_fixedPoints _ _ (T122_98 i) (hfix122_98 i) _)
      ⟨122, by decide⟩ ⟨98, by decide⟩ _
      (Q2.validAt ⟨122, by decide⟩ (Q2.listedAt ⟨122, by decide⟩
        (alnCheck_rep ⟨122, by decide⟩ hj hq).1))
      (colE2 ⟨98, by decide⟩ 0 hp) Q2.T122_98_2 Q2.hfix122_98_2 Q2.hinj122_98_2
      Q2.hcardT122_98_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T122_98_2 i) (Q2.hfix122_98_2 i) _)
      colCert_122_98_0.hD ?_).symm
  rw [alnId_122 j hj]


theorem leaf_122_98_1 (hp : 1 < (Q2.transData.getD 98 []).length)
    (j : Nat) (hj : j < (repChars.getD 122 []).length)
    (hq : (normIsRep.getD 122 []).getD j false = true) :
    species (Q2.reps (⟨98, by decide⟩ : Fin 148)) (colE2 ⟨98, by decide⟩ 1 hp)
        (rowE2 (⟨122, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨98, by decide⟩ : Fin 148))
        (colE1 ⟨98, by decide⟩ 1 (transLenTr ⟨98, by decide⟩ 1 hp))
        (rowE1 (⟨122, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨122, by decide⟩ : Fin 148) ⟨98, by decide⟩ _
      (validAt ⟨122, by decide⟩ (listedAt ⟨122, by decide⟩ hj))
      (colE1 ⟨98, by decide⟩ 1 (transLenTr ⟨98, by decide⟩ 1 hp)) T122_98
      hfix122_98 hinj122_98 hcardT122_98
      (fun i => conj_mem_of_fixedPoints _ _ (T122_98 i) (hfix122_98 i) _)
      ⟨122, by decide⟩ ⟨98, by decide⟩ _
      (Q2.validAt ⟨122, by decide⟩ (Q2.listedAt ⟨122, by decide⟩
        (alnCheck_rep ⟨122, by decide⟩ hj hq).1))
      (colE2 ⟨98, by decide⟩ 1 hp) Q2.T122_98_2 Q2.hfix122_98_2 Q2.hinj122_98_2
      Q2.hcardT122_98_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T122_98_2 i) (Q2.hfix122_98_2 i) _)
      colCert_122_98_1.hD ?_).symm
  rw [alnId_122 j hj]


theorem leaf_122_98_2 (hp : 2 < (Q2.transData.getD 98 []).length)
    (j : Nat) (hj : j < (repChars.getD 122 []).length)
    (hq : (normIsRep.getD 122 []).getD j false = true) :
    species (Q2.reps (⟨98, by decide⟩ : Fin 148)) (colE2 ⟨98, by decide⟩ 2 hp)
        (rowE2 (⟨122, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨98, by decide⟩ : Fin 148))
        (colE1 ⟨98, by decide⟩ 2 (transLenTr ⟨98, by decide⟩ 2 hp))
        (rowE1 (⟨122, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨122, by decide⟩ : Fin 148) ⟨98, by decide⟩ _
      (validAt ⟨122, by decide⟩ (listedAt ⟨122, by decide⟩ hj))
      (colE1 ⟨98, by decide⟩ 2 (transLenTr ⟨98, by decide⟩ 2 hp)) T122_98
      hfix122_98 hinj122_98 hcardT122_98
      (fun i => conj_mem_of_fixedPoints _ _ (T122_98 i) (hfix122_98 i) _)
      ⟨122, by decide⟩ ⟨98, by decide⟩ _
      (Q2.validAt ⟨122, by decide⟩ (Q2.listedAt ⟨122, by decide⟩
        (alnCheck_rep ⟨122, by decide⟩ hj hq).1))
      (colE2 ⟨98, by decide⟩ 2 hp) Q2.T122_98_2 Q2.hfix122_98_2 Q2.hinj122_98_2
      Q2.hcardT122_98_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T122_98_2 i) (Q2.hfix122_98_2 i) _)
      colCert_122_98_2.hD ?_).symm
  rw [alnId_122 j hj]


theorem leaf_122_98_3 (hp : 3 < (Q2.transData.getD 98 []).length)
    (j : Nat) (hj : j < (repChars.getD 122 []).length)
    (hq : (normIsRep.getD 122 []).getD j false = true) :
    species (Q2.reps (⟨98, by decide⟩ : Fin 148)) (colE2 ⟨98, by decide⟩ 3 hp)
        (rowE2 (⟨122, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨98, by decide⟩ : Fin 148))
        (colE1 ⟨98, by decide⟩ 3 (transLenTr ⟨98, by decide⟩ 3 hp))
        (rowE1 (⟨122, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨122, by decide⟩ : Fin 148) ⟨98, by decide⟩ _
      (validAt ⟨122, by decide⟩ (listedAt ⟨122, by decide⟩ hj))
      (colE1 ⟨98, by decide⟩ 3 (transLenTr ⟨98, by decide⟩ 3 hp)) T122_98
      hfix122_98 hinj122_98 hcardT122_98
      (fun i => conj_mem_of_fixedPoints _ _ (T122_98 i) (hfix122_98 i) _)
      ⟨122, by decide⟩ ⟨98, by decide⟩ _
      (Q2.validAt ⟨122, by decide⟩ (Q2.listedAt ⟨122, by decide⟩
        (alnCheck_rep ⟨122, by decide⟩ hj hq).1))
      (colE2 ⟨98, by decide⟩ 3 hp) Q2.T122_98_2 Q2.hfix122_98_2 Q2.hinj122_98_2
      Q2.hcardT122_98_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T122_98_2 i) (Q2.hfix122_98_2 i) _)
      colCert_122_98_3.hD ?_).symm
  rw [alnId_122 j hj]


theorem leaf_122_98_4 (hp : 4 < (Q2.transData.getD 98 []).length)
    (j : Nat) (hj : j < (repChars.getD 122 []).length)
    (hq : (normIsRep.getD 122 []).getD j false = true) :
    species (Q2.reps (⟨98, by decide⟩ : Fin 148)) (colE2 ⟨98, by decide⟩ 4 hp)
        (rowE2 (⟨122, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨98, by decide⟩ : Fin 148))
        (colE1 ⟨98, by decide⟩ 4 (transLenTr ⟨98, by decide⟩ 4 hp))
        (rowE1 (⟨122, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨122, by decide⟩ : Fin 148) ⟨98, by decide⟩ _
      (validAt ⟨122, by decide⟩ (listedAt ⟨122, by decide⟩ hj))
      (colE1 ⟨98, by decide⟩ 4 (transLenTr ⟨98, by decide⟩ 4 hp)) T122_98
      hfix122_98 hinj122_98 hcardT122_98
      (fun i => conj_mem_of_fixedPoints _ _ (T122_98 i) (hfix122_98 i) _)
      ⟨122, by decide⟩ ⟨98, by decide⟩ _
      (Q2.validAt ⟨122, by decide⟩ (Q2.listedAt ⟨122, by decide⟩
        (alnCheck_rep ⟨122, by decide⟩ hj hq).1))
      (colE2 ⟨98, by decide⟩ 4 hp) Q2.T122_98_2 Q2.hfix122_98_2 Q2.hinj122_98_2
      Q2.hcardT122_98_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T122_98_2 i) (Q2.hfix122_98_2 i) _)
      colCert_122_98_4.hD ?_).symm
  rw [alnId_122 j hj]


theorem leaf_122_98_5 (hp : 5 < (Q2.transData.getD 98 []).length)
    (j : Nat) (hj : j < (repChars.getD 122 []).length)
    (hq : (normIsRep.getD 122 []).getD j false = true) :
    species (Q2.reps (⟨98, by decide⟩ : Fin 148)) (colE2 ⟨98, by decide⟩ 5 hp)
        (rowE2 (⟨122, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨98, by decide⟩ : Fin 148))
        (colE1 ⟨98, by decide⟩ 5 (transLenTr ⟨98, by decide⟩ 5 hp))
        (rowE1 (⟨122, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨122, by decide⟩ : Fin 148) ⟨98, by decide⟩ _
      (validAt ⟨122, by decide⟩ (listedAt ⟨122, by decide⟩ hj))
      (colE1 ⟨98, by decide⟩ 5 (transLenTr ⟨98, by decide⟩ 5 hp)) T122_98
      hfix122_98 hinj122_98 hcardT122_98
      (fun i => conj_mem_of_fixedPoints _ _ (T122_98 i) (hfix122_98 i) _)
      ⟨122, by decide⟩ ⟨98, by decide⟩ _
      (Q2.validAt ⟨122, by decide⟩ (Q2.listedAt ⟨122, by decide⟩
        (alnCheck_rep ⟨122, by decide⟩ hj hq).1))
      (colE2 ⟨98, by decide⟩ 5 hp) Q2.T122_98_2 Q2.hfix122_98_2 Q2.hinj122_98_2
      Q2.hcardT122_98_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T122_98_2 i) (Q2.hfix122_98_2 i) _)
      ?_).symm
  rw [show colData1 (⟨122, by decide⟩ : Fin 148)
        ((colE1 ⟨98, by decide⟩ 5 (transLenTr ⟨98, by decide⟩ 5 hp) : ↥(reps ⟨98, by decide⟩)) : Coordinate 1)
        T122_98 = colFn colCertDiv_122_98_5.D1 (m := 5) from colCertDiv_122_98_5.bind1,
    show colData2 (⟨122, by decide⟩ : Fin 148)
        ((colE2 ⟨98, by decide⟩ 5 hp : ↥(Q2.reps ⟨98, by decide⟩)) : Coordinate 2)
        Q2.T122_98_2 = colFn colCertDiv_122_98_5.D2 (m := 5) from colCertDiv_122_98_5.bind2]
  rw [alnId_122 j hj]
  exact fastcode_of_div ⟨122, by decide⟩ _ _ _
    ((alnId_122 j hj) ▸ Q2.listedAt (⟨122, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨122, by decide⟩ : Fin 148) hj hq).1) colCertDiv_122_98_5_match


theorem leaf_122_98_10 (hp : 10 < (Q2.transData.getD 98 []).length)
    (j : Nat) (hj : j < (repChars.getD 122 []).length)
    (hq : (normIsRep.getD 122 []).getD j false = true) :
    species (Q2.reps (⟨98, by decide⟩ : Fin 148)) (colE2 ⟨98, by decide⟩ 10 hp)
        (rowE2 (⟨122, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨98, by decide⟩ : Fin 148))
        (colE1 ⟨98, by decide⟩ 10 (transLenTr ⟨98, by decide⟩ 10 hp))
        (rowE1 (⟨122, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨122, by decide⟩ : Fin 148) ⟨98, by decide⟩ _
      (validAt ⟨122, by decide⟩ (listedAt ⟨122, by decide⟩ hj))
      (colE1 ⟨98, by decide⟩ 10 (transLenTr ⟨98, by decide⟩ 10 hp)) T122_98
      hfix122_98 hinj122_98 hcardT122_98
      (fun i => conj_mem_of_fixedPoints _ _ (T122_98 i) (hfix122_98 i) _)
      ⟨122, by decide⟩ ⟨98, by decide⟩ _
      (Q2.validAt ⟨122, by decide⟩ (Q2.listedAt ⟨122, by decide⟩
        (alnCheck_rep ⟨122, by decide⟩ hj hq).1))
      (colE2 ⟨98, by decide⟩ 10 hp) Q2.T122_98_2 Q2.hfix122_98_2 Q2.hinj122_98_2
      Q2.hcardT122_98_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T122_98_2 i) (Q2.hfix122_98_2 i) _)
      ?_).symm
  rw [show colData1 (⟨122, by decide⟩ : Fin 148)
        ((colE1 ⟨98, by decide⟩ 10 (transLenTr ⟨98, by decide⟩ 10 hp) : ↥(reps ⟨98, by decide⟩)) : Coordinate 1)
        T122_98 = colFn colCertDiv_122_98_10.D1 (m := 5) from colCertDiv_122_98_10.bind1,
    show colData2 (⟨122, by decide⟩ : Fin 148)
        ((colE2 ⟨98, by decide⟩ 10 hp : ↥(Q2.reps ⟨98, by decide⟩)) : Coordinate 2)
        Q2.T122_98_2 = colFn colCertDiv_122_98_10.D2 (m := 5) from colCertDiv_122_98_10.bind2]
  rw [alnId_122 j hj]
  exact fastcode_of_div ⟨122, by decide⟩ _ _ _
    ((alnId_122 j hj) ▸ Q2.listedAt (⟨122, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨122, by decide⟩ : Fin 148) hj hq).1) colCertDiv_122_98_10_match


theorem leaf_122_98_15 (hp : 15 < (Q2.transData.getD 98 []).length)
    (j : Nat) (hj : j < (repChars.getD 122 []).length)
    (hq : (normIsRep.getD 122 []).getD j false = true) :
    species (Q2.reps (⟨98, by decide⟩ : Fin 148)) (colE2 ⟨98, by decide⟩ 15 hp)
        (rowE2 (⟨122, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨98, by decide⟩ : Fin 148))
        (colE1 ⟨98, by decide⟩ 15 (transLenTr ⟨98, by decide⟩ 15 hp))
        (rowE1 (⟨122, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨122, by decide⟩ : Fin 148) ⟨98, by decide⟩ _
      (validAt ⟨122, by decide⟩ (listedAt ⟨122, by decide⟩ hj))
      (colE1 ⟨98, by decide⟩ 15 (transLenTr ⟨98, by decide⟩ 15 hp)) T122_98
      hfix122_98 hinj122_98 hcardT122_98
      (fun i => conj_mem_of_fixedPoints _ _ (T122_98 i) (hfix122_98 i) _)
      ⟨122, by decide⟩ ⟨98, by decide⟩ _
      (Q2.validAt ⟨122, by decide⟩ (Q2.listedAt ⟨122, by decide⟩
        (alnCheck_rep ⟨122, by decide⟩ hj hq).1))
      (colE2 ⟨98, by decide⟩ 15 hp) Q2.T122_98_2 Q2.hfix122_98_2 Q2.hinj122_98_2
      Q2.hcardT122_98_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T122_98_2 i) (Q2.hfix122_98_2 i) _)
      colCert_122_98_15.hD ?_).symm
  rw [alnId_122 j hj]


theorem leaf_122_98_20 (hp : 20 < (Q2.transData.getD 98 []).length)
    (j : Nat) (hj : j < (repChars.getD 122 []).length)
    (hq : (normIsRep.getD 122 []).getD j false = true) :
    species (Q2.reps (⟨98, by decide⟩ : Fin 148)) (colE2 ⟨98, by decide⟩ 20 hp)
        (rowE2 (⟨122, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨98, by decide⟩ : Fin 148))
        (colE1 ⟨98, by decide⟩ 20 (transLenTr ⟨98, by decide⟩ 20 hp))
        (rowE1 (⟨122, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨122, by decide⟩ : Fin 148) ⟨98, by decide⟩ _
      (validAt ⟨122, by decide⟩ (listedAt ⟨122, by decide⟩ hj))
      (colE1 ⟨98, by decide⟩ 20 (transLenTr ⟨98, by decide⟩ 20 hp)) T122_98
      hfix122_98 hinj122_98 hcardT122_98
      (fun i => conj_mem_of_fixedPoints _ _ (T122_98 i) (hfix122_98 i) _)
      ⟨122, by decide⟩ ⟨98, by decide⟩ _
      (Q2.validAt ⟨122, by decide⟩ (Q2.listedAt ⟨122, by decide⟩
        (alnCheck_rep ⟨122, by decide⟩ hj hq).1))
      (colE2 ⟨98, by decide⟩ 20 hp) Q2.T122_98_2 Q2.hfix122_98_2 Q2.hinj122_98_2
      Q2.hcardT122_98_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T122_98_2 i) (Q2.hfix122_98_2 i) _)
      ?_).symm
  rw [show colData1 (⟨122, by decide⟩ : Fin 148)
        ((colE1 ⟨98, by decide⟩ 20 (transLenTr ⟨98, by decide⟩ 20 hp) : ↥(reps ⟨98, by decide⟩)) : Coordinate 1)
        T122_98 = colFn colCertDiv_122_98_20.D1 (m := 5) from colCertDiv_122_98_20.bind1,
    show colData2 (⟨122, by decide⟩ : Fin 148)
        ((colE2 ⟨98, by decide⟩ 20 hp : ↥(Q2.reps ⟨98, by decide⟩)) : Coordinate 2)
        Q2.T122_98_2 = colFn colCertDiv_122_98_20.D2 (m := 5) from colCertDiv_122_98_20.bind2]
  rw [alnId_122 j hj]
  exact fastcode_of_div ⟨122, by decide⟩ _ _ _
    ((alnId_122 j hj) ▸ Q2.listedAt (⟨122, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨122, by decide⟩ : Fin 148) hj hq).1) colCertDiv_122_98_20_match


theorem leaf_122_104_0 (hp : 0 < (Q2.transData.getD 104 []).length)
    (j : Nat) (hj : j < (repChars.getD 122 []).length)
    (hq : (normIsRep.getD 122 []).getD j false = true) :
    species (Q2.reps (⟨104, by decide⟩ : Fin 148)) (colE2 ⟨104, by decide⟩ 0 hp)
        (rowE2 (⟨122, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨104, by decide⟩ : Fin 148))
        (colE1 ⟨104, by decide⟩ 0 (transLenTr ⟨104, by decide⟩ 0 hp))
        (rowE1 (⟨122, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨122, by decide⟩ : Fin 148) ⟨104, by decide⟩ _
      (validAt ⟨122, by decide⟩ (listedAt ⟨122, by decide⟩ hj))
      (colE1 ⟨104, by decide⟩ 0 (transLenTr ⟨104, by decide⟩ 0 hp)) T122_104
      hfix122_104 hinj122_104 hcardT122_104
      (fun i => conj_mem_of_fixedPoints _ _ (T122_104 i) (hfix122_104 i) _)
      ⟨122, by decide⟩ ⟨104, by decide⟩ _
      (Q2.validAt ⟨122, by decide⟩ (Q2.listedAt ⟨122, by decide⟩
        (alnCheck_rep ⟨122, by decide⟩ hj hq).1))
      (colE2 ⟨104, by decide⟩ 0 hp) Q2.T122_104_2 Q2.hfix122_104_2 Q2.hinj122_104_2
      Q2.hcardT122_104_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T122_104_2 i) (Q2.hfix122_104_2 i) _)
      colCert_122_104_0.hD ?_).symm
  rw [alnId_122 j hj]


theorem leaf_122_104_1 (hp : 1 < (Q2.transData.getD 104 []).length)
    (j : Nat) (hj : j < (repChars.getD 122 []).length)
    (hq : (normIsRep.getD 122 []).getD j false = true) :
    species (Q2.reps (⟨104, by decide⟩ : Fin 148)) (colE2 ⟨104, by decide⟩ 1 hp)
        (rowE2 (⟨122, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨104, by decide⟩ : Fin 148))
        (colE1 ⟨104, by decide⟩ 1 (transLenTr ⟨104, by decide⟩ 1 hp))
        (rowE1 (⟨122, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨122, by decide⟩ : Fin 148) ⟨104, by decide⟩ _
      (validAt ⟨122, by decide⟩ (listedAt ⟨122, by decide⟩ hj))
      (colE1 ⟨104, by decide⟩ 1 (transLenTr ⟨104, by decide⟩ 1 hp)) T122_104
      hfix122_104 hinj122_104 hcardT122_104
      (fun i => conj_mem_of_fixedPoints _ _ (T122_104 i) (hfix122_104 i) _)
      ⟨122, by decide⟩ ⟨104, by decide⟩ _
      (Q2.validAt ⟨122, by decide⟩ (Q2.listedAt ⟨122, by decide⟩
        (alnCheck_rep ⟨122, by decide⟩ hj hq).1))
      (colE2 ⟨104, by decide⟩ 1 hp) Q2.T122_104_2 Q2.hfix122_104_2 Q2.hinj122_104_2
      Q2.hcardT122_104_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T122_104_2 i) (Q2.hfix122_104_2 i) _)
      colCert_122_104_1.hD ?_).symm
  rw [alnId_122 j hj]


theorem leaf_122_104_2 (hp : 2 < (Q2.transData.getD 104 []).length)
    (j : Nat) (hj : j < (repChars.getD 122 []).length)
    (hq : (normIsRep.getD 122 []).getD j false = true) :
    species (Q2.reps (⟨104, by decide⟩ : Fin 148)) (colE2 ⟨104, by decide⟩ 2 hp)
        (rowE2 (⟨122, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨104, by decide⟩ : Fin 148))
        (colE1 ⟨104, by decide⟩ 2 (transLenTr ⟨104, by decide⟩ 2 hp))
        (rowE1 (⟨122, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨122, by decide⟩ : Fin 148) ⟨104, by decide⟩ _
      (validAt ⟨122, by decide⟩ (listedAt ⟨122, by decide⟩ hj))
      (colE1 ⟨104, by decide⟩ 2 (transLenTr ⟨104, by decide⟩ 2 hp)) T122_104
      hfix122_104 hinj122_104 hcardT122_104
      (fun i => conj_mem_of_fixedPoints _ _ (T122_104 i) (hfix122_104 i) _)
      ⟨122, by decide⟩ ⟨104, by decide⟩ _
      (Q2.validAt ⟨122, by decide⟩ (Q2.listedAt ⟨122, by decide⟩
        (alnCheck_rep ⟨122, by decide⟩ hj hq).1))
      (colE2 ⟨104, by decide⟩ 2 hp) Q2.T122_104_2 Q2.hfix122_104_2 Q2.hinj122_104_2
      Q2.hcardT122_104_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T122_104_2 i) (Q2.hfix122_104_2 i) _)
      colCert_122_104_2.hD ?_).symm
  rw [alnId_122 j hj]


theorem leaf_122_104_3 (hp : 3 < (Q2.transData.getD 104 []).length)
    (j : Nat) (hj : j < (repChars.getD 122 []).length)
    (hq : (normIsRep.getD 122 []).getD j false = true) :
    species (Q2.reps (⟨104, by decide⟩ : Fin 148)) (colE2 ⟨104, by decide⟩ 3 hp)
        (rowE2 (⟨122, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨104, by decide⟩ : Fin 148))
        (colE1 ⟨104, by decide⟩ 3 (transLenTr ⟨104, by decide⟩ 3 hp))
        (rowE1 (⟨122, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨122, by decide⟩ : Fin 148) ⟨104, by decide⟩ _
      (validAt ⟨122, by decide⟩ (listedAt ⟨122, by decide⟩ hj))
      (colE1 ⟨104, by decide⟩ 3 (transLenTr ⟨104, by decide⟩ 3 hp)) T122_104
      hfix122_104 hinj122_104 hcardT122_104
      (fun i => conj_mem_of_fixedPoints _ _ (T122_104 i) (hfix122_104 i) _)
      ⟨122, by decide⟩ ⟨104, by decide⟩ _
      (Q2.validAt ⟨122, by decide⟩ (Q2.listedAt ⟨122, by decide⟩
        (alnCheck_rep ⟨122, by decide⟩ hj hq).1))
      (colE2 ⟨104, by decide⟩ 3 hp) Q2.T122_104_2 Q2.hfix122_104_2 Q2.hinj122_104_2
      Q2.hcardT122_104_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T122_104_2 i) (Q2.hfix122_104_2 i) _)
      colCert_122_104_3.hD ?_).symm
  rw [alnId_122 j hj]


theorem leaf_122_104_4 (hp : 4 < (Q2.transData.getD 104 []).length)
    (j : Nat) (hj : j < (repChars.getD 122 []).length)
    (hq : (normIsRep.getD 122 []).getD j false = true) :
    species (Q2.reps (⟨104, by decide⟩ : Fin 148)) (colE2 ⟨104, by decide⟩ 4 hp)
        (rowE2 (⟨122, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨104, by decide⟩ : Fin 148))
        (colE1 ⟨104, by decide⟩ 4 (transLenTr ⟨104, by decide⟩ 4 hp))
        (rowE1 (⟨122, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨122, by decide⟩ : Fin 148) ⟨104, by decide⟩ _
      (validAt ⟨122, by decide⟩ (listedAt ⟨122, by decide⟩ hj))
      (colE1 ⟨104, by decide⟩ 4 (transLenTr ⟨104, by decide⟩ 4 hp)) T122_104
      hfix122_104 hinj122_104 hcardT122_104
      (fun i => conj_mem_of_fixedPoints _ _ (T122_104 i) (hfix122_104 i) _)
      ⟨122, by decide⟩ ⟨104, by decide⟩ _
      (Q2.validAt ⟨122, by decide⟩ (Q2.listedAt ⟨122, by decide⟩
        (alnCheck_rep ⟨122, by decide⟩ hj hq).1))
      (colE2 ⟨104, by decide⟩ 4 hp) Q2.T122_104_2 Q2.hfix122_104_2 Q2.hinj122_104_2
      Q2.hcardT122_104_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T122_104_2 i) (Q2.hfix122_104_2 i) _)
      colCert_122_104_4.hD ?_).symm
  rw [alnId_122 j hj]


theorem leaf_122_104_5 (hp : 5 < (Q2.transData.getD 104 []).length)
    (j : Nat) (hj : j < (repChars.getD 122 []).length)
    (hq : (normIsRep.getD 122 []).getD j false = true) :
    species (Q2.reps (⟨104, by decide⟩ : Fin 148)) (colE2 ⟨104, by decide⟩ 5 hp)
        (rowE2 (⟨122, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨104, by decide⟩ : Fin 148))
        (colE1 ⟨104, by decide⟩ 5 (transLenTr ⟨104, by decide⟩ 5 hp))
        (rowE1 (⟨122, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨122, by decide⟩ : Fin 148) ⟨104, by decide⟩ _
      (validAt ⟨122, by decide⟩ (listedAt ⟨122, by decide⟩ hj))
      (colE1 ⟨104, by decide⟩ 5 (transLenTr ⟨104, by decide⟩ 5 hp)) T122_104
      hfix122_104 hinj122_104 hcardT122_104
      (fun i => conj_mem_of_fixedPoints _ _ (T122_104 i) (hfix122_104 i) _)
      ⟨122, by decide⟩ ⟨104, by decide⟩ _
      (Q2.validAt ⟨122, by decide⟩ (Q2.listedAt ⟨122, by decide⟩
        (alnCheck_rep ⟨122, by decide⟩ hj hq).1))
      (colE2 ⟨104, by decide⟩ 5 hp) Q2.T122_104_2 Q2.hfix122_104_2 Q2.hinj122_104_2
      Q2.hcardT122_104_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T122_104_2 i) (Q2.hfix122_104_2 i) _)
      ?_).symm
  rw [show colData1 (⟨122, by decide⟩ : Fin 148)
        ((colE1 ⟨104, by decide⟩ 5 (transLenTr ⟨104, by decide⟩ 5 hp) : ↥(reps ⟨104, by decide⟩)) : Coordinate 1)
        T122_104 = colFn colCertDiv_122_104_5.D1 (m := 5) from colCertDiv_122_104_5.bind1,
    show colData2 (⟨122, by decide⟩ : Fin 148)
        ((colE2 ⟨104, by decide⟩ 5 hp : ↥(Q2.reps ⟨104, by decide⟩)) : Coordinate 2)
        Q2.T122_104_2 = colFn colCertDiv_122_104_5.D2 (m := 5) from colCertDiv_122_104_5.bind2]
  rw [alnId_122 j hj]
  exact fastcode_of_div ⟨122, by decide⟩ _ _ _
    ((alnId_122 j hj) ▸ Q2.listedAt (⟨122, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨122, by decide⟩ : Fin 148) hj hq).1) colCertDiv_122_104_5_match


theorem leaf_122_104_10 (hp : 10 < (Q2.transData.getD 104 []).length)
    (j : Nat) (hj : j < (repChars.getD 122 []).length)
    (hq : (normIsRep.getD 122 []).getD j false = true) :
    species (Q2.reps (⟨104, by decide⟩ : Fin 148)) (colE2 ⟨104, by decide⟩ 10 hp)
        (rowE2 (⟨122, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨104, by decide⟩ : Fin 148))
        (colE1 ⟨104, by decide⟩ 10 (transLenTr ⟨104, by decide⟩ 10 hp))
        (rowE1 (⟨122, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨122, by decide⟩ : Fin 148) ⟨104, by decide⟩ _
      (validAt ⟨122, by decide⟩ (listedAt ⟨122, by decide⟩ hj))
      (colE1 ⟨104, by decide⟩ 10 (transLenTr ⟨104, by decide⟩ 10 hp)) T122_104
      hfix122_104 hinj122_104 hcardT122_104
      (fun i => conj_mem_of_fixedPoints _ _ (T122_104 i) (hfix122_104 i) _)
      ⟨122, by decide⟩ ⟨104, by decide⟩ _
      (Q2.validAt ⟨122, by decide⟩ (Q2.listedAt ⟨122, by decide⟩
        (alnCheck_rep ⟨122, by decide⟩ hj hq).1))
      (colE2 ⟨104, by decide⟩ 10 hp) Q2.T122_104_2 Q2.hfix122_104_2 Q2.hinj122_104_2
      Q2.hcardT122_104_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T122_104_2 i) (Q2.hfix122_104_2 i) _)
      ?_).symm
  rw [show colData1 (⟨122, by decide⟩ : Fin 148)
        ((colE1 ⟨104, by decide⟩ 10 (transLenTr ⟨104, by decide⟩ 10 hp) : ↥(reps ⟨104, by decide⟩)) : Coordinate 1)
        T122_104 = colFn colCertDiv_122_104_10.D1 (m := 5) from colCertDiv_122_104_10.bind1,
    show colData2 (⟨122, by decide⟩ : Fin 148)
        ((colE2 ⟨104, by decide⟩ 10 hp : ↥(Q2.reps ⟨104, by decide⟩)) : Coordinate 2)
        Q2.T122_104_2 = colFn colCertDiv_122_104_10.D2 (m := 5) from colCertDiv_122_104_10.bind2]
  rw [alnId_122 j hj]
  exact fastcode_of_div ⟨122, by decide⟩ _ _ _
    ((alnId_122 j hj) ▸ Q2.listedAt (⟨122, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨122, by decide⟩ : Fin 148) hj hq).1) colCertDiv_122_104_10_match


theorem leaf_122_104_15 (hp : 15 < (Q2.transData.getD 104 []).length)
    (j : Nat) (hj : j < (repChars.getD 122 []).length)
    (hq : (normIsRep.getD 122 []).getD j false = true) :
    species (Q2.reps (⟨104, by decide⟩ : Fin 148)) (colE2 ⟨104, by decide⟩ 15 hp)
        (rowE2 (⟨122, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨104, by decide⟩ : Fin 148))
        (colE1 ⟨104, by decide⟩ 15 (transLenTr ⟨104, by decide⟩ 15 hp))
        (rowE1 (⟨122, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨122, by decide⟩ : Fin 148) ⟨104, by decide⟩ _
      (validAt ⟨122, by decide⟩ (listedAt ⟨122, by decide⟩ hj))
      (colE1 ⟨104, by decide⟩ 15 (transLenTr ⟨104, by decide⟩ 15 hp)) T122_104
      hfix122_104 hinj122_104 hcardT122_104
      (fun i => conj_mem_of_fixedPoints _ _ (T122_104 i) (hfix122_104 i) _)
      ⟨122, by decide⟩ ⟨104, by decide⟩ _
      (Q2.validAt ⟨122, by decide⟩ (Q2.listedAt ⟨122, by decide⟩
        (alnCheck_rep ⟨122, by decide⟩ hj hq).1))
      (colE2 ⟨104, by decide⟩ 15 hp) Q2.T122_104_2 Q2.hfix122_104_2 Q2.hinj122_104_2
      Q2.hcardT122_104_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T122_104_2 i) (Q2.hfix122_104_2 i) _)
      ?_).symm
  rw [show colData1 (⟨122, by decide⟩ : Fin 148)
        ((colE1 ⟨104, by decide⟩ 15 (transLenTr ⟨104, by decide⟩ 15 hp) : ↥(reps ⟨104, by decide⟩)) : Coordinate 1)
        T122_104 = colFn colCertDiv_122_104_15.D1 (m := 5) from colCertDiv_122_104_15.bind1,
    show colData2 (⟨122, by decide⟩ : Fin 148)
        ((colE2 ⟨104, by decide⟩ 15 hp : ↥(Q2.reps ⟨104, by decide⟩)) : Coordinate 2)
        Q2.T122_104_2 = colFn colCertDiv_122_104_15.D2 (m := 5) from colCertDiv_122_104_15.bind2]
  rw [alnId_122 j hj]
  exact fastcode_of_div ⟨122, by decide⟩ _ _ _
    ((alnId_122 j hj) ▸ Q2.listedAt (⟨122, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨122, by decide⟩ : Fin 148) hj hq).1) colCertDiv_122_104_15_match


theorem leaf_122_104_20 (hp : 20 < (Q2.transData.getD 104 []).length)
    (j : Nat) (hj : j < (repChars.getD 122 []).length)
    (hq : (normIsRep.getD 122 []).getD j false = true) :
    species (Q2.reps (⟨104, by decide⟩ : Fin 148)) (colE2 ⟨104, by decide⟩ 20 hp)
        (rowE2 (⟨122, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨104, by decide⟩ : Fin 148))
        (colE1 ⟨104, by decide⟩ 20 (transLenTr ⟨104, by decide⟩ 20 hp))
        (rowE1 (⟨122, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨122, by decide⟩ : Fin 148) ⟨104, by decide⟩ _
      (validAt ⟨122, by decide⟩ (listedAt ⟨122, by decide⟩ hj))
      (colE1 ⟨104, by decide⟩ 20 (transLenTr ⟨104, by decide⟩ 20 hp)) T122_104
      hfix122_104 hinj122_104 hcardT122_104
      (fun i => conj_mem_of_fixedPoints _ _ (T122_104 i) (hfix122_104 i) _)
      ⟨122, by decide⟩ ⟨104, by decide⟩ _
      (Q2.validAt ⟨122, by decide⟩ (Q2.listedAt ⟨122, by decide⟩
        (alnCheck_rep ⟨122, by decide⟩ hj hq).1))
      (colE2 ⟨104, by decide⟩ 20 hp) Q2.T122_104_2 Q2.hfix122_104_2 Q2.hinj122_104_2
      Q2.hcardT122_104_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T122_104_2 i) (Q2.hfix122_104_2 i) _)
      ?_).symm
  rw [show colData1 (⟨122, by decide⟩ : Fin 148)
        ((colE1 ⟨104, by decide⟩ 20 (transLenTr ⟨104, by decide⟩ 20 hp) : ↥(reps ⟨104, by decide⟩)) : Coordinate 1)
        T122_104 = colFn colCertDiv_122_104_20.D1 (m := 5) from colCertDiv_122_104_20.bind1,
    show colData2 (⟨122, by decide⟩ : Fin 148)
        ((colE2 ⟨104, by decide⟩ 20 hp : ↥(Q2.reps ⟨104, by decide⟩)) : Coordinate 2)
        Q2.T122_104_2 = colFn colCertDiv_122_104_20.D2 (m := 5) from colCertDiv_122_104_20.bind2]
  rw [alnId_122 j hj]
  exact fastcode_of_div ⟨122, by decide⟩ _ _ _
    ((alnId_122 j hj) ▸ Q2.listedAt (⟨122, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨122, by decide⟩ : Fin 148) hj hq).1) colCertDiv_122_104_20_match


theorem leaf_122_107_0 (hp : 0 < (Q2.transData.getD 107 []).length)
    (j : Nat) (hj : j < (repChars.getD 122 []).length)
    (hq : (normIsRep.getD 122 []).getD j false = true) :
    species (Q2.reps (⟨107, by decide⟩ : Fin 148)) (colE2 ⟨107, by decide⟩ 0 hp)
        (rowE2 (⟨122, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨107, by decide⟩ : Fin 148))
        (colE1 ⟨107, by decide⟩ 0 (transLenTr ⟨107, by decide⟩ 0 hp))
        (rowE1 (⟨122, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨122, by decide⟩ : Fin 148) ⟨107, by decide⟩ _
      (validAt ⟨122, by decide⟩ (listedAt ⟨122, by decide⟩ hj))
      (colE1 ⟨107, by decide⟩ 0 (transLenTr ⟨107, by decide⟩ 0 hp)) T122_107
      hfix122_107 hinj122_107 hcardT122_107
      (fun i => conj_mem_of_fixedPoints _ _ (T122_107 i) (hfix122_107 i) _)
      ⟨122, by decide⟩ ⟨107, by decide⟩ _
      (Q2.validAt ⟨122, by decide⟩ (Q2.listedAt ⟨122, by decide⟩
        (alnCheck_rep ⟨122, by decide⟩ hj hq).1))
      (colE2 ⟨107, by decide⟩ 0 hp) Q2.T122_107_2 Q2.hfix122_107_2 Q2.hinj122_107_2
      Q2.hcardT122_107_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T122_107_2 i) (Q2.hfix122_107_2 i) _)
      colCert_122_107_0.hD ?_).symm
  rw [alnId_122 j hj]


theorem leaf_122_107_1 (hp : 1 < (Q2.transData.getD 107 []).length)
    (j : Nat) (hj : j < (repChars.getD 122 []).length)
    (hq : (normIsRep.getD 122 []).getD j false = true) :
    species (Q2.reps (⟨107, by decide⟩ : Fin 148)) (colE2 ⟨107, by decide⟩ 1 hp)
        (rowE2 (⟨122, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨107, by decide⟩ : Fin 148))
        (colE1 ⟨107, by decide⟩ 1 (transLenTr ⟨107, by decide⟩ 1 hp))
        (rowE1 (⟨122, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨122, by decide⟩ : Fin 148) ⟨107, by decide⟩ _
      (validAt ⟨122, by decide⟩ (listedAt ⟨122, by decide⟩ hj))
      (colE1 ⟨107, by decide⟩ 1 (transLenTr ⟨107, by decide⟩ 1 hp)) T122_107
      hfix122_107 hinj122_107 hcardT122_107
      (fun i => conj_mem_of_fixedPoints _ _ (T122_107 i) (hfix122_107 i) _)
      ⟨122, by decide⟩ ⟨107, by decide⟩ _
      (Q2.validAt ⟨122, by decide⟩ (Q2.listedAt ⟨122, by decide⟩
        (alnCheck_rep ⟨122, by decide⟩ hj hq).1))
      (colE2 ⟨107, by decide⟩ 1 hp) Q2.T122_107_2 Q2.hfix122_107_2 Q2.hinj122_107_2
      Q2.hcardT122_107_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T122_107_2 i) (Q2.hfix122_107_2 i) _)
      colCert_122_107_1.hD ?_).symm
  rw [alnId_122 j hj]


theorem leaf_122_107_2 (hp : 2 < (Q2.transData.getD 107 []).length)
    (j : Nat) (hj : j < (repChars.getD 122 []).length)
    (hq : (normIsRep.getD 122 []).getD j false = true) :
    species (Q2.reps (⟨107, by decide⟩ : Fin 148)) (colE2 ⟨107, by decide⟩ 2 hp)
        (rowE2 (⟨122, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨107, by decide⟩ : Fin 148))
        (colE1 ⟨107, by decide⟩ 2 (transLenTr ⟨107, by decide⟩ 2 hp))
        (rowE1 (⟨122, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨122, by decide⟩ : Fin 148) ⟨107, by decide⟩ _
      (validAt ⟨122, by decide⟩ (listedAt ⟨122, by decide⟩ hj))
      (colE1 ⟨107, by decide⟩ 2 (transLenTr ⟨107, by decide⟩ 2 hp)) T122_107
      hfix122_107 hinj122_107 hcardT122_107
      (fun i => conj_mem_of_fixedPoints _ _ (T122_107 i) (hfix122_107 i) _)
      ⟨122, by decide⟩ ⟨107, by decide⟩ _
      (Q2.validAt ⟨122, by decide⟩ (Q2.listedAt ⟨122, by decide⟩
        (alnCheck_rep ⟨122, by decide⟩ hj hq).1))
      (colE2 ⟨107, by decide⟩ 2 hp) Q2.T122_107_2 Q2.hfix122_107_2 Q2.hinj122_107_2
      Q2.hcardT122_107_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T122_107_2 i) (Q2.hfix122_107_2 i) _)
      colCert_122_107_2.hD ?_).symm
  rw [alnId_122 j hj]


theorem leaf_122_107_3 (hp : 3 < (Q2.transData.getD 107 []).length)
    (j : Nat) (hj : j < (repChars.getD 122 []).length)
    (hq : (normIsRep.getD 122 []).getD j false = true) :
    species (Q2.reps (⟨107, by decide⟩ : Fin 148)) (colE2 ⟨107, by decide⟩ 3 hp)
        (rowE2 (⟨122, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨107, by decide⟩ : Fin 148))
        (colE1 ⟨107, by decide⟩ 3 (transLenTr ⟨107, by decide⟩ 3 hp))
        (rowE1 (⟨122, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨122, by decide⟩ : Fin 148) ⟨107, by decide⟩ _
      (validAt ⟨122, by decide⟩ (listedAt ⟨122, by decide⟩ hj))
      (colE1 ⟨107, by decide⟩ 3 (transLenTr ⟨107, by decide⟩ 3 hp)) T122_107
      hfix122_107 hinj122_107 hcardT122_107
      (fun i => conj_mem_of_fixedPoints _ _ (T122_107 i) (hfix122_107 i) _)
      ⟨122, by decide⟩ ⟨107, by decide⟩ _
      (Q2.validAt ⟨122, by decide⟩ (Q2.listedAt ⟨122, by decide⟩
        (alnCheck_rep ⟨122, by decide⟩ hj hq).1))
      (colE2 ⟨107, by decide⟩ 3 hp) Q2.T122_107_2 Q2.hfix122_107_2 Q2.hinj122_107_2
      Q2.hcardT122_107_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T122_107_2 i) (Q2.hfix122_107_2 i) _)
      colCert_122_107_3.hD ?_).symm
  rw [alnId_122 j hj]


theorem leaf_122_107_4 (hp : 4 < (Q2.transData.getD 107 []).length)
    (j : Nat) (hj : j < (repChars.getD 122 []).length)
    (hq : (normIsRep.getD 122 []).getD j false = true) :
    species (Q2.reps (⟨107, by decide⟩ : Fin 148)) (colE2 ⟨107, by decide⟩ 4 hp)
        (rowE2 (⟨122, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨107, by decide⟩ : Fin 148))
        (colE1 ⟨107, by decide⟩ 4 (transLenTr ⟨107, by decide⟩ 4 hp))
        (rowE1 (⟨122, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨122, by decide⟩ : Fin 148) ⟨107, by decide⟩ _
      (validAt ⟨122, by decide⟩ (listedAt ⟨122, by decide⟩ hj))
      (colE1 ⟨107, by decide⟩ 4 (transLenTr ⟨107, by decide⟩ 4 hp)) T122_107
      hfix122_107 hinj122_107 hcardT122_107
      (fun i => conj_mem_of_fixedPoints _ _ (T122_107 i) (hfix122_107 i) _)
      ⟨122, by decide⟩ ⟨107, by decide⟩ _
      (Q2.validAt ⟨122, by decide⟩ (Q2.listedAt ⟨122, by decide⟩
        (alnCheck_rep ⟨122, by decide⟩ hj hq).1))
      (colE2 ⟨107, by decide⟩ 4 hp) Q2.T122_107_2 Q2.hfix122_107_2 Q2.hinj122_107_2
      Q2.hcardT122_107_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T122_107_2 i) (Q2.hfix122_107_2 i) _)
      colCert_122_107_4.hD ?_).symm
  rw [alnId_122 j hj]


theorem leaf_122_107_5 (hp : 5 < (Q2.transData.getD 107 []).length)
    (j : Nat) (hj : j < (repChars.getD 122 []).length)
    (hq : (normIsRep.getD 122 []).getD j false = true) :
    species (Q2.reps (⟨107, by decide⟩ : Fin 148)) (colE2 ⟨107, by decide⟩ 5 hp)
        (rowE2 (⟨122, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨107, by decide⟩ : Fin 148))
        (colE1 ⟨107, by decide⟩ 5 (transLenTr ⟨107, by decide⟩ 5 hp))
        (rowE1 (⟨122, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨122, by decide⟩ : Fin 148) ⟨107, by decide⟩ _
      (validAt ⟨122, by decide⟩ (listedAt ⟨122, by decide⟩ hj))
      (colE1 ⟨107, by decide⟩ 5 (transLenTr ⟨107, by decide⟩ 5 hp)) T122_107
      hfix122_107 hinj122_107 hcardT122_107
      (fun i => conj_mem_of_fixedPoints _ _ (T122_107 i) (hfix122_107 i) _)
      ⟨122, by decide⟩ ⟨107, by decide⟩ _
      (Q2.validAt ⟨122, by decide⟩ (Q2.listedAt ⟨122, by decide⟩
        (alnCheck_rep ⟨122, by decide⟩ hj hq).1))
      (colE2 ⟨107, by decide⟩ 5 hp) Q2.T122_107_2 Q2.hfix122_107_2 Q2.hinj122_107_2
      Q2.hcardT122_107_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T122_107_2 i) (Q2.hfix122_107_2 i) _)
      ?_).symm
  rw [show colData1 (⟨122, by decide⟩ : Fin 148)
        ((colE1 ⟨107, by decide⟩ 5 (transLenTr ⟨107, by decide⟩ 5 hp) : ↥(reps ⟨107, by decide⟩)) : Coordinate 1)
        T122_107 = colFn colCertDiv_122_107_5.D1 (m := 5) from colCertDiv_122_107_5.bind1,
    show colData2 (⟨122, by decide⟩ : Fin 148)
        ((colE2 ⟨107, by decide⟩ 5 hp : ↥(Q2.reps ⟨107, by decide⟩)) : Coordinate 2)
        Q2.T122_107_2 = colFn colCertDiv_122_107_5.D2 (m := 5) from colCertDiv_122_107_5.bind2]
  rw [alnId_122 j hj]
  exact fastcode_of_div ⟨122, by decide⟩ _ _ _
    ((alnId_122 j hj) ▸ Q2.listedAt (⟨122, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨122, by decide⟩ : Fin 148) hj hq).1) colCertDiv_122_107_5_match


theorem leaf_122_107_10 (hp : 10 < (Q2.transData.getD 107 []).length)
    (j : Nat) (hj : j < (repChars.getD 122 []).length)
    (hq : (normIsRep.getD 122 []).getD j false = true) :
    species (Q2.reps (⟨107, by decide⟩ : Fin 148)) (colE2 ⟨107, by decide⟩ 10 hp)
        (rowE2 (⟨122, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨107, by decide⟩ : Fin 148))
        (colE1 ⟨107, by decide⟩ 10 (transLenTr ⟨107, by decide⟩ 10 hp))
        (rowE1 (⟨122, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨122, by decide⟩ : Fin 148) ⟨107, by decide⟩ _
      (validAt ⟨122, by decide⟩ (listedAt ⟨122, by decide⟩ hj))
      (colE1 ⟨107, by decide⟩ 10 (transLenTr ⟨107, by decide⟩ 10 hp)) T122_107
      hfix122_107 hinj122_107 hcardT122_107
      (fun i => conj_mem_of_fixedPoints _ _ (T122_107 i) (hfix122_107 i) _)
      ⟨122, by decide⟩ ⟨107, by decide⟩ _
      (Q2.validAt ⟨122, by decide⟩ (Q2.listedAt ⟨122, by decide⟩
        (alnCheck_rep ⟨122, by decide⟩ hj hq).1))
      (colE2 ⟨107, by decide⟩ 10 hp) Q2.T122_107_2 Q2.hfix122_107_2 Q2.hinj122_107_2
      Q2.hcardT122_107_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T122_107_2 i) (Q2.hfix122_107_2 i) _)
      ?_).symm
  rw [show colData1 (⟨122, by decide⟩ : Fin 148)
        ((colE1 ⟨107, by decide⟩ 10 (transLenTr ⟨107, by decide⟩ 10 hp) : ↥(reps ⟨107, by decide⟩)) : Coordinate 1)
        T122_107 = colFn colCertDiv_122_107_10.D1 (m := 5) from colCertDiv_122_107_10.bind1,
    show colData2 (⟨122, by decide⟩ : Fin 148)
        ((colE2 ⟨107, by decide⟩ 10 hp : ↥(Q2.reps ⟨107, by decide⟩)) : Coordinate 2)
        Q2.T122_107_2 = colFn colCertDiv_122_107_10.D2 (m := 5) from colCertDiv_122_107_10.bind2]
  rw [alnId_122 j hj]
  exact fastcode_of_div ⟨122, by decide⟩ _ _ _
    ((alnId_122 j hj) ▸ Q2.listedAt (⟨122, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨122, by decide⟩ : Fin 148) hj hq).1) colCertDiv_122_107_10_match


theorem leaf_122_107_15 (hp : 15 < (Q2.transData.getD 107 []).length)
    (j : Nat) (hj : j < (repChars.getD 122 []).length)
    (hq : (normIsRep.getD 122 []).getD j false = true) :
    species (Q2.reps (⟨107, by decide⟩ : Fin 148)) (colE2 ⟨107, by decide⟩ 15 hp)
        (rowE2 (⟨122, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨107, by decide⟩ : Fin 148))
        (colE1 ⟨107, by decide⟩ 15 (transLenTr ⟨107, by decide⟩ 15 hp))
        (rowE1 (⟨122, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨122, by decide⟩ : Fin 148) ⟨107, by decide⟩ _
      (validAt ⟨122, by decide⟩ (listedAt ⟨122, by decide⟩ hj))
      (colE1 ⟨107, by decide⟩ 15 (transLenTr ⟨107, by decide⟩ 15 hp)) T122_107
      hfix122_107 hinj122_107 hcardT122_107
      (fun i => conj_mem_of_fixedPoints _ _ (T122_107 i) (hfix122_107 i) _)
      ⟨122, by decide⟩ ⟨107, by decide⟩ _
      (Q2.validAt ⟨122, by decide⟩ (Q2.listedAt ⟨122, by decide⟩
        (alnCheck_rep ⟨122, by decide⟩ hj hq).1))
      (colE2 ⟨107, by decide⟩ 15 hp) Q2.T122_107_2 Q2.hfix122_107_2 Q2.hinj122_107_2
      Q2.hcardT122_107_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T122_107_2 i) (Q2.hfix122_107_2 i) _)
      ?_).symm
  rw [show colData1 (⟨122, by decide⟩ : Fin 148)
        ((colE1 ⟨107, by decide⟩ 15 (transLenTr ⟨107, by decide⟩ 15 hp) : ↥(reps ⟨107, by decide⟩)) : Coordinate 1)
        T122_107 = colFn colCertDiv_122_107_15.D1 (m := 5) from colCertDiv_122_107_15.bind1,
    show colData2 (⟨122, by decide⟩ : Fin 148)
        ((colE2 ⟨107, by decide⟩ 15 hp : ↥(Q2.reps ⟨107, by decide⟩)) : Coordinate 2)
        Q2.T122_107_2 = colFn colCertDiv_122_107_15.D2 (m := 5) from colCertDiv_122_107_15.bind2]
  rw [alnId_122 j hj]
  exact fastcode_of_div ⟨122, by decide⟩ _ _ _
    ((alnId_122 j hj) ▸ Q2.listedAt (⟨122, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨122, by decide⟩ : Fin 148) hj hq).1) colCertDiv_122_107_15_match


theorem leaf_122_107_20 (hp : 20 < (Q2.transData.getD 107 []).length)
    (j : Nat) (hj : j < (repChars.getD 122 []).length)
    (hq : (normIsRep.getD 122 []).getD j false = true) :
    species (Q2.reps (⟨107, by decide⟩ : Fin 148)) (colE2 ⟨107, by decide⟩ 20 hp)
        (rowE2 (⟨122, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨107, by decide⟩ : Fin 148))
        (colE1 ⟨107, by decide⟩ 20 (transLenTr ⟨107, by decide⟩ 20 hp))
        (rowE1 (⟨122, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨122, by decide⟩ : Fin 148) ⟨107, by decide⟩ _
      (validAt ⟨122, by decide⟩ (listedAt ⟨122, by decide⟩ hj))
      (colE1 ⟨107, by decide⟩ 20 (transLenTr ⟨107, by decide⟩ 20 hp)) T122_107
      hfix122_107 hinj122_107 hcardT122_107
      (fun i => conj_mem_of_fixedPoints _ _ (T122_107 i) (hfix122_107 i) _)
      ⟨122, by decide⟩ ⟨107, by decide⟩ _
      (Q2.validAt ⟨122, by decide⟩ (Q2.listedAt ⟨122, by decide⟩
        (alnCheck_rep ⟨122, by decide⟩ hj hq).1))
      (colE2 ⟨107, by decide⟩ 20 hp) Q2.T122_107_2 Q2.hfix122_107_2 Q2.hinj122_107_2
      Q2.hcardT122_107_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T122_107_2 i) (Q2.hfix122_107_2 i) _)
      colCert_122_107_20.hD ?_).symm
  rw [alnId_122 j hj]


theorem leaf_122_111_0 (hp : 0 < (Q2.transData.getD 111 []).length)
    (j : Nat) (hj : j < (repChars.getD 122 []).length)
    (hq : (normIsRep.getD 122 []).getD j false = true) :
    species (Q2.reps (⟨111, by decide⟩ : Fin 148)) (colE2 ⟨111, by decide⟩ 0 hp)
        (rowE2 (⟨122, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨111, by decide⟩ : Fin 148))
        (colE1 ⟨111, by decide⟩ 0 (transLenTr ⟨111, by decide⟩ 0 hp))
        (rowE1 (⟨122, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨122, by decide⟩ : Fin 148) ⟨111, by decide⟩ _
      (validAt ⟨122, by decide⟩ (listedAt ⟨122, by decide⟩ hj))
      (colE1 ⟨111, by decide⟩ 0 (transLenTr ⟨111, by decide⟩ 0 hp)) T122_111
      hfix122_111 hinj122_111 hcardT122_111
      (fun i => conj_mem_of_fixedPoints _ _ (T122_111 i) (hfix122_111 i) _)
      ⟨122, by decide⟩ ⟨111, by decide⟩ _
      (Q2.validAt ⟨122, by decide⟩ (Q2.listedAt ⟨122, by decide⟩
        (alnCheck_rep ⟨122, by decide⟩ hj hq).1))
      (colE2 ⟨111, by decide⟩ 0 hp) Q2.T122_111_2 Q2.hfix122_111_2 Q2.hinj122_111_2
      Q2.hcardT122_111_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T122_111_2 i) (Q2.hfix122_111_2 i) _)
      colCert_122_111_0.hD ?_).symm
  rw [alnId_122 j hj]


theorem leaf_122_111_1 (hp : 1 < (Q2.transData.getD 111 []).length)
    (j : Nat) (hj : j < (repChars.getD 122 []).length)
    (hq : (normIsRep.getD 122 []).getD j false = true) :
    species (Q2.reps (⟨111, by decide⟩ : Fin 148)) (colE2 ⟨111, by decide⟩ 1 hp)
        (rowE2 (⟨122, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨111, by decide⟩ : Fin 148))
        (colE1 ⟨111, by decide⟩ 1 (transLenTr ⟨111, by decide⟩ 1 hp))
        (rowE1 (⟨122, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨122, by decide⟩ : Fin 148) ⟨111, by decide⟩ _
      (validAt ⟨122, by decide⟩ (listedAt ⟨122, by decide⟩ hj))
      (colE1 ⟨111, by decide⟩ 1 (transLenTr ⟨111, by decide⟩ 1 hp)) T122_111
      hfix122_111 hinj122_111 hcardT122_111
      (fun i => conj_mem_of_fixedPoints _ _ (T122_111 i) (hfix122_111 i) _)
      ⟨122, by decide⟩ ⟨111, by decide⟩ _
      (Q2.validAt ⟨122, by decide⟩ (Q2.listedAt ⟨122, by decide⟩
        (alnCheck_rep ⟨122, by decide⟩ hj hq).1))
      (colE2 ⟨111, by decide⟩ 1 hp) Q2.T122_111_2 Q2.hfix122_111_2 Q2.hinj122_111_2
      Q2.hcardT122_111_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T122_111_2 i) (Q2.hfix122_111_2 i) _)
      colCert_122_111_1.hD ?_).symm
  rw [alnId_122 j hj]


theorem leaf_122_111_2 (hp : 2 < (Q2.transData.getD 111 []).length)
    (j : Nat) (hj : j < (repChars.getD 122 []).length)
    (hq : (normIsRep.getD 122 []).getD j false = true) :
    species (Q2.reps (⟨111, by decide⟩ : Fin 148)) (colE2 ⟨111, by decide⟩ 2 hp)
        (rowE2 (⟨122, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨111, by decide⟩ : Fin 148))
        (colE1 ⟨111, by decide⟩ 2 (transLenTr ⟨111, by decide⟩ 2 hp))
        (rowE1 (⟨122, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨122, by decide⟩ : Fin 148) ⟨111, by decide⟩ _
      (validAt ⟨122, by decide⟩ (listedAt ⟨122, by decide⟩ hj))
      (colE1 ⟨111, by decide⟩ 2 (transLenTr ⟨111, by decide⟩ 2 hp)) T122_111
      hfix122_111 hinj122_111 hcardT122_111
      (fun i => conj_mem_of_fixedPoints _ _ (T122_111 i) (hfix122_111 i) _)
      ⟨122, by decide⟩ ⟨111, by decide⟩ _
      (Q2.validAt ⟨122, by decide⟩ (Q2.listedAt ⟨122, by decide⟩
        (alnCheck_rep ⟨122, by decide⟩ hj hq).1))
      (colE2 ⟨111, by decide⟩ 2 hp) Q2.T122_111_2 Q2.hfix122_111_2 Q2.hinj122_111_2
      Q2.hcardT122_111_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T122_111_2 i) (Q2.hfix122_111_2 i) _)
      colCert_122_111_2.hD ?_).symm
  rw [alnId_122 j hj]


theorem leaf_122_111_3 (hp : 3 < (Q2.transData.getD 111 []).length)
    (j : Nat) (hj : j < (repChars.getD 122 []).length)
    (hq : (normIsRep.getD 122 []).getD j false = true) :
    species (Q2.reps (⟨111, by decide⟩ : Fin 148)) (colE2 ⟨111, by decide⟩ 3 hp)
        (rowE2 (⟨122, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨111, by decide⟩ : Fin 148))
        (colE1 ⟨111, by decide⟩ 3 (transLenTr ⟨111, by decide⟩ 3 hp))
        (rowE1 (⟨122, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨122, by decide⟩ : Fin 148) ⟨111, by decide⟩ _
      (validAt ⟨122, by decide⟩ (listedAt ⟨122, by decide⟩ hj))
      (colE1 ⟨111, by decide⟩ 3 (transLenTr ⟨111, by decide⟩ 3 hp)) T122_111
      hfix122_111 hinj122_111 hcardT122_111
      (fun i => conj_mem_of_fixedPoints _ _ (T122_111 i) (hfix122_111 i) _)
      ⟨122, by decide⟩ ⟨111, by decide⟩ _
      (Q2.validAt ⟨122, by decide⟩ (Q2.listedAt ⟨122, by decide⟩
        (alnCheck_rep ⟨122, by decide⟩ hj hq).1))
      (colE2 ⟨111, by decide⟩ 3 hp) Q2.T122_111_2 Q2.hfix122_111_2 Q2.hinj122_111_2
      Q2.hcardT122_111_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T122_111_2 i) (Q2.hfix122_111_2 i) _)
      colCert_122_111_3.hD ?_).symm
  rw [alnId_122 j hj]


theorem leaf_122_111_4 (hp : 4 < (Q2.transData.getD 111 []).length)
    (j : Nat) (hj : j < (repChars.getD 122 []).length)
    (hq : (normIsRep.getD 122 []).getD j false = true) :
    species (Q2.reps (⟨111, by decide⟩ : Fin 148)) (colE2 ⟨111, by decide⟩ 4 hp)
        (rowE2 (⟨122, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨111, by decide⟩ : Fin 148))
        (colE1 ⟨111, by decide⟩ 4 (transLenTr ⟨111, by decide⟩ 4 hp))
        (rowE1 (⟨122, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨122, by decide⟩ : Fin 148) ⟨111, by decide⟩ _
      (validAt ⟨122, by decide⟩ (listedAt ⟨122, by decide⟩ hj))
      (colE1 ⟨111, by decide⟩ 4 (transLenTr ⟨111, by decide⟩ 4 hp)) T122_111
      hfix122_111 hinj122_111 hcardT122_111
      (fun i => conj_mem_of_fixedPoints _ _ (T122_111 i) (hfix122_111 i) _)
      ⟨122, by decide⟩ ⟨111, by decide⟩ _
      (Q2.validAt ⟨122, by decide⟩ (Q2.listedAt ⟨122, by decide⟩
        (alnCheck_rep ⟨122, by decide⟩ hj hq).1))
      (colE2 ⟨111, by decide⟩ 4 hp) Q2.T122_111_2 Q2.hfix122_111_2 Q2.hinj122_111_2
      Q2.hcardT122_111_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T122_111_2 i) (Q2.hfix122_111_2 i) _)
      colCert_122_111_4.hD ?_).symm
  rw [alnId_122 j hj]


theorem leaf_122_111_5 (hp : 5 < (Q2.transData.getD 111 []).length)
    (j : Nat) (hj : j < (repChars.getD 122 []).length)
    (hq : (normIsRep.getD 122 []).getD j false = true) :
    species (Q2.reps (⟨111, by decide⟩ : Fin 148)) (colE2 ⟨111, by decide⟩ 5 hp)
        (rowE2 (⟨122, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨111, by decide⟩ : Fin 148))
        (colE1 ⟨111, by decide⟩ 5 (transLenTr ⟨111, by decide⟩ 5 hp))
        (rowE1 (⟨122, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨122, by decide⟩ : Fin 148) ⟨111, by decide⟩ _
      (validAt ⟨122, by decide⟩ (listedAt ⟨122, by decide⟩ hj))
      (colE1 ⟨111, by decide⟩ 5 (transLenTr ⟨111, by decide⟩ 5 hp)) T122_111
      hfix122_111 hinj122_111 hcardT122_111
      (fun i => conj_mem_of_fixedPoints _ _ (T122_111 i) (hfix122_111 i) _)
      ⟨122, by decide⟩ ⟨111, by decide⟩ _
      (Q2.validAt ⟨122, by decide⟩ (Q2.listedAt ⟨122, by decide⟩
        (alnCheck_rep ⟨122, by decide⟩ hj hq).1))
      (colE2 ⟨111, by decide⟩ 5 hp) Q2.T122_111_2 Q2.hfix122_111_2 Q2.hinj122_111_2
      Q2.hcardT122_111_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T122_111_2 i) (Q2.hfix122_111_2 i) _)
      colCert_122_111_5.hD ?_).symm
  rw [alnId_122 j hj]


theorem leaf_122_111_10 (hp : 10 < (Q2.transData.getD 111 []).length)
    (j : Nat) (hj : j < (repChars.getD 122 []).length)
    (hq : (normIsRep.getD 122 []).getD j false = true) :
    species (Q2.reps (⟨111, by decide⟩ : Fin 148)) (colE2 ⟨111, by decide⟩ 10 hp)
        (rowE2 (⟨122, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨111, by decide⟩ : Fin 148))
        (colE1 ⟨111, by decide⟩ 10 (transLenTr ⟨111, by decide⟩ 10 hp))
        (rowE1 (⟨122, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨122, by decide⟩ : Fin 148) ⟨111, by decide⟩ _
      (validAt ⟨122, by decide⟩ (listedAt ⟨122, by decide⟩ hj))
      (colE1 ⟨111, by decide⟩ 10 (transLenTr ⟨111, by decide⟩ 10 hp)) T122_111
      hfix122_111 hinj122_111 hcardT122_111
      (fun i => conj_mem_of_fixedPoints _ _ (T122_111 i) (hfix122_111 i) _)
      ⟨122, by decide⟩ ⟨111, by decide⟩ _
      (Q2.validAt ⟨122, by decide⟩ (Q2.listedAt ⟨122, by decide⟩
        (alnCheck_rep ⟨122, by decide⟩ hj hq).1))
      (colE2 ⟨111, by decide⟩ 10 hp) Q2.T122_111_2 Q2.hfix122_111_2 Q2.hinj122_111_2
      Q2.hcardT122_111_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T122_111_2 i) (Q2.hfix122_111_2 i) _)
      ?_).symm
  rw [show colData1 (⟨122, by decide⟩ : Fin 148)
        ((colE1 ⟨111, by decide⟩ 10 (transLenTr ⟨111, by decide⟩ 10 hp) : ↥(reps ⟨111, by decide⟩)) : Coordinate 1)
        T122_111 = colFn colCertDiv_122_111_10.D1 (m := 5) from colCertDiv_122_111_10.bind1,
    show colData2 (⟨122, by decide⟩ : Fin 148)
        ((colE2 ⟨111, by decide⟩ 10 hp : ↥(Q2.reps ⟨111, by decide⟩)) : Coordinate 2)
        Q2.T122_111_2 = colFn colCertDiv_122_111_10.D2 (m := 5) from colCertDiv_122_111_10.bind2]
  rw [alnId_122 j hj]
  exact fastcode_of_div ⟨122, by decide⟩ _ _ _
    ((alnId_122 j hj) ▸ Q2.listedAt (⟨122, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨122, by decide⟩ : Fin 148) hj hq).1) colCertDiv_122_111_10_match


theorem leaf_122_111_15 (hp : 15 < (Q2.transData.getD 111 []).length)
    (j : Nat) (hj : j < (repChars.getD 122 []).length)
    (hq : (normIsRep.getD 122 []).getD j false = true) :
    species (Q2.reps (⟨111, by decide⟩ : Fin 148)) (colE2 ⟨111, by decide⟩ 15 hp)
        (rowE2 (⟨122, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨111, by decide⟩ : Fin 148))
        (colE1 ⟨111, by decide⟩ 15 (transLenTr ⟨111, by decide⟩ 15 hp))
        (rowE1 (⟨122, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨122, by decide⟩ : Fin 148) ⟨111, by decide⟩ _
      (validAt ⟨122, by decide⟩ (listedAt ⟨122, by decide⟩ hj))
      (colE1 ⟨111, by decide⟩ 15 (transLenTr ⟨111, by decide⟩ 15 hp)) T122_111
      hfix122_111 hinj122_111 hcardT122_111
      (fun i => conj_mem_of_fixedPoints _ _ (T122_111 i) (hfix122_111 i) _)
      ⟨122, by decide⟩ ⟨111, by decide⟩ _
      (Q2.validAt ⟨122, by decide⟩ (Q2.listedAt ⟨122, by decide⟩
        (alnCheck_rep ⟨122, by decide⟩ hj hq).1))
      (colE2 ⟨111, by decide⟩ 15 hp) Q2.T122_111_2 Q2.hfix122_111_2 Q2.hinj122_111_2
      Q2.hcardT122_111_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T122_111_2 i) (Q2.hfix122_111_2 i) _)
      ?_).symm
  rw [show colData1 (⟨122, by decide⟩ : Fin 148)
        ((colE1 ⟨111, by decide⟩ 15 (transLenTr ⟨111, by decide⟩ 15 hp) : ↥(reps ⟨111, by decide⟩)) : Coordinate 1)
        T122_111 = colFn colCertDiv_122_111_15.D1 (m := 5) from colCertDiv_122_111_15.bind1,
    show colData2 (⟨122, by decide⟩ : Fin 148)
        ((colE2 ⟨111, by decide⟩ 15 hp : ↥(Q2.reps ⟨111, by decide⟩)) : Coordinate 2)
        Q2.T122_111_2 = colFn colCertDiv_122_111_15.D2 (m := 5) from colCertDiv_122_111_15.bind2]
  rw [alnId_122 j hj]
  exact fastcode_of_div ⟨122, by decide⟩ _ _ _
    ((alnId_122 j hj) ▸ Q2.listedAt (⟨122, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨122, by decide⟩ : Fin 148) hj hq).1) colCertDiv_122_111_15_match


theorem leaf_122_111_20 (hp : 20 < (Q2.transData.getD 111 []).length)
    (j : Nat) (hj : j < (repChars.getD 122 []).length)
    (hq : (normIsRep.getD 122 []).getD j false = true) :
    species (Q2.reps (⟨111, by decide⟩ : Fin 148)) (colE2 ⟨111, by decide⟩ 20 hp)
        (rowE2 (⟨122, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨111, by decide⟩ : Fin 148))
        (colE1 ⟨111, by decide⟩ 20 (transLenTr ⟨111, by decide⟩ 20 hp))
        (rowE1 (⟨122, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨122, by decide⟩ : Fin 148) ⟨111, by decide⟩ _
      (validAt ⟨122, by decide⟩ (listedAt ⟨122, by decide⟩ hj))
      (colE1 ⟨111, by decide⟩ 20 (transLenTr ⟨111, by decide⟩ 20 hp)) T122_111
      hfix122_111 hinj122_111 hcardT122_111
      (fun i => conj_mem_of_fixedPoints _ _ (T122_111 i) (hfix122_111 i) _)
      ⟨122, by decide⟩ ⟨111, by decide⟩ _
      (Q2.validAt ⟨122, by decide⟩ (Q2.listedAt ⟨122, by decide⟩
        (alnCheck_rep ⟨122, by decide⟩ hj hq).1))
      (colE2 ⟨111, by decide⟩ 20 hp) Q2.T122_111_2 Q2.hfix122_111_2 Q2.hinj122_111_2
      Q2.hcardT122_111_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T122_111_2 i) (Q2.hfix122_111_2 i) _)
      ?_).symm
  rw [show colData1 (⟨122, by decide⟩ : Fin 148)
        ((colE1 ⟨111, by decide⟩ 20 (transLenTr ⟨111, by decide⟩ 20 hp) : ↥(reps ⟨111, by decide⟩)) : Coordinate 1)
        T122_111 = colFn colCertDiv_122_111_20.D1 (m := 5) from colCertDiv_122_111_20.bind1,
    show colData2 (⟨122, by decide⟩ : Fin 148)
        ((colE2 ⟨111, by decide⟩ 20 hp : ↥(Q2.reps ⟨111, by decide⟩)) : Coordinate 2)
        Q2.T122_111_2 = colFn colCertDiv_122_111_20.D2 (m := 5) from colCertDiv_122_111_20.bind2]
  rw [alnId_122 j hj]
  exact fastcode_of_div ⟨122, by decide⟩ _ _ _
    ((alnId_122 j hj) ▸ Q2.listedAt (⟨122, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨122, by decide⟩ : Fin 148) hj hq).1) colCertDiv_122_111_20_match


theorem leaf_122_122_0 (hp : 0 < (Q2.transData.getD 122 []).length)
    (j : Nat) (hj : j < (repChars.getD 122 []).length)
    (hq : (normIsRep.getD 122 []).getD j false = true) :
    species (Q2.reps (⟨122, by decide⟩ : Fin 148)) (colE2 ⟨122, by decide⟩ 0 hp)
        (rowE2 (⟨122, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨122, by decide⟩ : Fin 148))
        (colE1 ⟨122, by decide⟩ 0 (transLenTr ⟨122, by decide⟩ 0 hp))
        (rowE1 (⟨122, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨122, by decide⟩ : Fin 148) ⟨122, by decide⟩ _
      (validAt ⟨122, by decide⟩ (listedAt ⟨122, by decide⟩ hj))
      (colE1 ⟨122, by decide⟩ 0 (transLenTr ⟨122, by decide⟩ 0 hp)) T122_122
      hfix122_122 hinj122_122 hcardT122_122
      (fun i => conj_mem_of_fixedPoints _ _ (T122_122 i) (hfix122_122 i) _)
      ⟨122, by decide⟩ ⟨122, by decide⟩ _
      (Q2.validAt ⟨122, by decide⟩ (Q2.listedAt ⟨122, by decide⟩
        (alnCheck_rep ⟨122, by decide⟩ hj hq).1))
      (colE2 ⟨122, by decide⟩ 0 hp) Q2.T122_122_2 Q2.hfix122_122_2 Q2.hinj122_122_2
      Q2.hcardT122_122_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T122_122_2 i) (Q2.hfix122_122_2 i) _)
      colCert_122_122_0.hD ?_).symm
  rw [alnId_122 j hj]


theorem leaf_122_122_1 (hp : 1 < (Q2.transData.getD 122 []).length)
    (j : Nat) (hj : j < (repChars.getD 122 []).length)
    (hq : (normIsRep.getD 122 []).getD j false = true) :
    species (Q2.reps (⟨122, by decide⟩ : Fin 148)) (colE2 ⟨122, by decide⟩ 1 hp)
        (rowE2 (⟨122, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨122, by decide⟩ : Fin 148))
        (colE1 ⟨122, by decide⟩ 1 (transLenTr ⟨122, by decide⟩ 1 hp))
        (rowE1 (⟨122, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨122, by decide⟩ : Fin 148) ⟨122, by decide⟩ _
      (validAt ⟨122, by decide⟩ (listedAt ⟨122, by decide⟩ hj))
      (colE1 ⟨122, by decide⟩ 1 (transLenTr ⟨122, by decide⟩ 1 hp)) T122_122
      hfix122_122 hinj122_122 hcardT122_122
      (fun i => conj_mem_of_fixedPoints _ _ (T122_122 i) (hfix122_122 i) _)
      ⟨122, by decide⟩ ⟨122, by decide⟩ _
      (Q2.validAt ⟨122, by decide⟩ (Q2.listedAt ⟨122, by decide⟩
        (alnCheck_rep ⟨122, by decide⟩ hj hq).1))
      (colE2 ⟨122, by decide⟩ 1 hp) Q2.T122_122_2 Q2.hfix122_122_2 Q2.hinj122_122_2
      Q2.hcardT122_122_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T122_122_2 i) (Q2.hfix122_122_2 i) _)
      colCert_122_122_1.hD ?_).symm
  rw [alnId_122 j hj]


theorem leaf_122_122_2 (hp : 2 < (Q2.transData.getD 122 []).length)
    (j : Nat) (hj : j < (repChars.getD 122 []).length)
    (hq : (normIsRep.getD 122 []).getD j false = true) :
    species (Q2.reps (⟨122, by decide⟩ : Fin 148)) (colE2 ⟨122, by decide⟩ 2 hp)
        (rowE2 (⟨122, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨122, by decide⟩ : Fin 148))
        (colE1 ⟨122, by decide⟩ 2 (transLenTr ⟨122, by decide⟩ 2 hp))
        (rowE1 (⟨122, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨122, by decide⟩ : Fin 148) ⟨122, by decide⟩ _
      (validAt ⟨122, by decide⟩ (listedAt ⟨122, by decide⟩ hj))
      (colE1 ⟨122, by decide⟩ 2 (transLenTr ⟨122, by decide⟩ 2 hp)) T122_122
      hfix122_122 hinj122_122 hcardT122_122
      (fun i => conj_mem_of_fixedPoints _ _ (T122_122 i) (hfix122_122 i) _)
      ⟨122, by decide⟩ ⟨122, by decide⟩ _
      (Q2.validAt ⟨122, by decide⟩ (Q2.listedAt ⟨122, by decide⟩
        (alnCheck_rep ⟨122, by decide⟩ hj hq).1))
      (colE2 ⟨122, by decide⟩ 2 hp) Q2.T122_122_2 Q2.hfix122_122_2 Q2.hinj122_122_2
      Q2.hcardT122_122_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T122_122_2 i) (Q2.hfix122_122_2 i) _)
      colCert_122_122_2.hD ?_).symm
  rw [alnId_122 j hj]


theorem leaf_122_122_3 (hp : 3 < (Q2.transData.getD 122 []).length)
    (j : Nat) (hj : j < (repChars.getD 122 []).length)
    (hq : (normIsRep.getD 122 []).getD j false = true) :
    species (Q2.reps (⟨122, by decide⟩ : Fin 148)) (colE2 ⟨122, by decide⟩ 3 hp)
        (rowE2 (⟨122, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨122, by decide⟩ : Fin 148))
        (colE1 ⟨122, by decide⟩ 3 (transLenTr ⟨122, by decide⟩ 3 hp))
        (rowE1 (⟨122, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨122, by decide⟩ : Fin 148) ⟨122, by decide⟩ _
      (validAt ⟨122, by decide⟩ (listedAt ⟨122, by decide⟩ hj))
      (colE1 ⟨122, by decide⟩ 3 (transLenTr ⟨122, by decide⟩ 3 hp)) T122_122
      hfix122_122 hinj122_122 hcardT122_122
      (fun i => conj_mem_of_fixedPoints _ _ (T122_122 i) (hfix122_122 i) _)
      ⟨122, by decide⟩ ⟨122, by decide⟩ _
      (Q2.validAt ⟨122, by decide⟩ (Q2.listedAt ⟨122, by decide⟩
        (alnCheck_rep ⟨122, by decide⟩ hj hq).1))
      (colE2 ⟨122, by decide⟩ 3 hp) Q2.T122_122_2 Q2.hfix122_122_2 Q2.hinj122_122_2
      Q2.hcardT122_122_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T122_122_2 i) (Q2.hfix122_122_2 i) _)
      colCert_122_122_3.hD ?_).symm
  rw [alnId_122 j hj]


theorem leaf_122_122_4 (hp : 4 < (Q2.transData.getD 122 []).length)
    (j : Nat) (hj : j < (repChars.getD 122 []).length)
    (hq : (normIsRep.getD 122 []).getD j false = true) :
    species (Q2.reps (⟨122, by decide⟩ : Fin 148)) (colE2 ⟨122, by decide⟩ 4 hp)
        (rowE2 (⟨122, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨122, by decide⟩ : Fin 148))
        (colE1 ⟨122, by decide⟩ 4 (transLenTr ⟨122, by decide⟩ 4 hp))
        (rowE1 (⟨122, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨122, by decide⟩ : Fin 148) ⟨122, by decide⟩ _
      (validAt ⟨122, by decide⟩ (listedAt ⟨122, by decide⟩ hj))
      (colE1 ⟨122, by decide⟩ 4 (transLenTr ⟨122, by decide⟩ 4 hp)) T122_122
      hfix122_122 hinj122_122 hcardT122_122
      (fun i => conj_mem_of_fixedPoints _ _ (T122_122 i) (hfix122_122 i) _)
      ⟨122, by decide⟩ ⟨122, by decide⟩ _
      (Q2.validAt ⟨122, by decide⟩ (Q2.listedAt ⟨122, by decide⟩
        (alnCheck_rep ⟨122, by decide⟩ hj hq).1))
      (colE2 ⟨122, by decide⟩ 4 hp) Q2.T122_122_2 Q2.hfix122_122_2 Q2.hinj122_122_2
      Q2.hcardT122_122_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T122_122_2 i) (Q2.hfix122_122_2 i) _)
      colCert_122_122_4.hD ?_).symm
  rw [alnId_122 j hj]


theorem leaf_122_122_5 (hp : 5 < (Q2.transData.getD 122 []).length)
    (j : Nat) (hj : j < (repChars.getD 122 []).length)
    (hq : (normIsRep.getD 122 []).getD j false = true) :
    species (Q2.reps (⟨122, by decide⟩ : Fin 148)) (colE2 ⟨122, by decide⟩ 5 hp)
        (rowE2 (⟨122, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨122, by decide⟩ : Fin 148))
        (colE1 ⟨122, by decide⟩ 5 (transLenTr ⟨122, by decide⟩ 5 hp))
        (rowE1 (⟨122, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨122, by decide⟩ : Fin 148) ⟨122, by decide⟩ _
      (validAt ⟨122, by decide⟩ (listedAt ⟨122, by decide⟩ hj))
      (colE1 ⟨122, by decide⟩ 5 (transLenTr ⟨122, by decide⟩ 5 hp)) T122_122
      hfix122_122 hinj122_122 hcardT122_122
      (fun i => conj_mem_of_fixedPoints _ _ (T122_122 i) (hfix122_122 i) _)
      ⟨122, by decide⟩ ⟨122, by decide⟩ _
      (Q2.validAt ⟨122, by decide⟩ (Q2.listedAt ⟨122, by decide⟩
        (alnCheck_rep ⟨122, by decide⟩ hj hq).1))
      (colE2 ⟨122, by decide⟩ 5 hp) Q2.T122_122_2 Q2.hfix122_122_2 Q2.hinj122_122_2
      Q2.hcardT122_122_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T122_122_2 i) (Q2.hfix122_122_2 i) _)
      colCert_122_122_5.hD ?_).symm
  rw [alnId_122 j hj]


theorem leaf_122_122_6 (hp : 6 < (Q2.transData.getD 122 []).length)
    (j : Nat) (hj : j < (repChars.getD 122 []).length)
    (hq : (normIsRep.getD 122 []).getD j false = true) :
    species (Q2.reps (⟨122, by decide⟩ : Fin 148)) (colE2 ⟨122, by decide⟩ 6 hp)
        (rowE2 (⟨122, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨122, by decide⟩ : Fin 148))
        (colE1 ⟨122, by decide⟩ 6 (transLenTr ⟨122, by decide⟩ 6 hp))
        (rowE1 (⟨122, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨122, by decide⟩ : Fin 148) ⟨122, by decide⟩ _
      (validAt ⟨122, by decide⟩ (listedAt ⟨122, by decide⟩ hj))
      (colE1 ⟨122, by decide⟩ 6 (transLenTr ⟨122, by decide⟩ 6 hp)) T122_122
      hfix122_122 hinj122_122 hcardT122_122
      (fun i => conj_mem_of_fixedPoints _ _ (T122_122 i) (hfix122_122 i) _)
      ⟨122, by decide⟩ ⟨122, by decide⟩ _
      (Q2.validAt ⟨122, by decide⟩ (Q2.listedAt ⟨122, by decide⟩
        (alnCheck_rep ⟨122, by decide⟩ hj hq).1))
      (colE2 ⟨122, by decide⟩ 6 hp) Q2.T122_122_2 Q2.hfix122_122_2 Q2.hinj122_122_2
      Q2.hcardT122_122_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T122_122_2 i) (Q2.hfix122_122_2 i) _)
      colCert_122_122_6.hD ?_).symm
  rw [alnId_122 j hj]


theorem leaf_122_122_7 (hp : 7 < (Q2.transData.getD 122 []).length)
    (j : Nat) (hj : j < (repChars.getD 122 []).length)
    (hq : (normIsRep.getD 122 []).getD j false = true) :
    species (Q2.reps (⟨122, by decide⟩ : Fin 148)) (colE2 ⟨122, by decide⟩ 7 hp)
        (rowE2 (⟨122, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨122, by decide⟩ : Fin 148))
        (colE1 ⟨122, by decide⟩ 7 (transLenTr ⟨122, by decide⟩ 7 hp))
        (rowE1 (⟨122, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨122, by decide⟩ : Fin 148) ⟨122, by decide⟩ _
      (validAt ⟨122, by decide⟩ (listedAt ⟨122, by decide⟩ hj))
      (colE1 ⟨122, by decide⟩ 7 (transLenTr ⟨122, by decide⟩ 7 hp)) T122_122
      hfix122_122 hinj122_122 hcardT122_122
      (fun i => conj_mem_of_fixedPoints _ _ (T122_122 i) (hfix122_122 i) _)
      ⟨122, by decide⟩ ⟨122, by decide⟩ _
      (Q2.validAt ⟨122, by decide⟩ (Q2.listedAt ⟨122, by decide⟩
        (alnCheck_rep ⟨122, by decide⟩ hj hq).1))
      (colE2 ⟨122, by decide⟩ 7 hp) Q2.T122_122_2 Q2.hfix122_122_2 Q2.hinj122_122_2
      Q2.hcardT122_122_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T122_122_2 i) (Q2.hfix122_122_2 i) _)
      colCert_122_122_7.hD ?_).symm
  rw [alnId_122 j hj]


theorem leaf_122_122_8 (hp : 8 < (Q2.transData.getD 122 []).length)
    (j : Nat) (hj : j < (repChars.getD 122 []).length)
    (hq : (normIsRep.getD 122 []).getD j false = true) :
    species (Q2.reps (⟨122, by decide⟩ : Fin 148)) (colE2 ⟨122, by decide⟩ 8 hp)
        (rowE2 (⟨122, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨122, by decide⟩ : Fin 148))
        (colE1 ⟨122, by decide⟩ 8 (transLenTr ⟨122, by decide⟩ 8 hp))
        (rowE1 (⟨122, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨122, by decide⟩ : Fin 148) ⟨122, by decide⟩ _
      (validAt ⟨122, by decide⟩ (listedAt ⟨122, by decide⟩ hj))
      (colE1 ⟨122, by decide⟩ 8 (transLenTr ⟨122, by decide⟩ 8 hp)) T122_122
      hfix122_122 hinj122_122 hcardT122_122
      (fun i => conj_mem_of_fixedPoints _ _ (T122_122 i) (hfix122_122 i) _)
      ⟨122, by decide⟩ ⟨122, by decide⟩ _
      (Q2.validAt ⟨122, by decide⟩ (Q2.listedAt ⟨122, by decide⟩
        (alnCheck_rep ⟨122, by decide⟩ hj hq).1))
      (colE2 ⟨122, by decide⟩ 8 hp) Q2.T122_122_2 Q2.hfix122_122_2 Q2.hinj122_122_2
      Q2.hcardT122_122_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T122_122_2 i) (Q2.hfix122_122_2 i) _)
      colCert_122_122_8.hD ?_).symm
  rw [alnId_122 j hj]


theorem leaf_122_122_9 (hp : 9 < (Q2.transData.getD 122 []).length)
    (j : Nat) (hj : j < (repChars.getD 122 []).length)
    (hq : (normIsRep.getD 122 []).getD j false = true) :
    species (Q2.reps (⟨122, by decide⟩ : Fin 148)) (colE2 ⟨122, by decide⟩ 9 hp)
        (rowE2 (⟨122, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨122, by decide⟩ : Fin 148))
        (colE1 ⟨122, by decide⟩ 9 (transLenTr ⟨122, by decide⟩ 9 hp))
        (rowE1 (⟨122, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨122, by decide⟩ : Fin 148) ⟨122, by decide⟩ _
      (validAt ⟨122, by decide⟩ (listedAt ⟨122, by decide⟩ hj))
      (colE1 ⟨122, by decide⟩ 9 (transLenTr ⟨122, by decide⟩ 9 hp)) T122_122
      hfix122_122 hinj122_122 hcardT122_122
      (fun i => conj_mem_of_fixedPoints _ _ (T122_122 i) (hfix122_122 i) _)
      ⟨122, by decide⟩ ⟨122, by decide⟩ _
      (Q2.validAt ⟨122, by decide⟩ (Q2.listedAt ⟨122, by decide⟩
        (alnCheck_rep ⟨122, by decide⟩ hj hq).1))
      (colE2 ⟨122, by decide⟩ 9 hp) Q2.T122_122_2 Q2.hfix122_122_2 Q2.hinj122_122_2
      Q2.hcardT122_122_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T122_122_2 i) (Q2.hfix122_122_2 i) _)
      colCert_122_122_9.hD ?_).symm
  rw [alnId_122 j hj]


theorem leaf_122_122_10 (hp : 10 < (Q2.transData.getD 122 []).length)
    (j : Nat) (hj : j < (repChars.getD 122 []).length)
    (hq : (normIsRep.getD 122 []).getD j false = true) :
    species (Q2.reps (⟨122, by decide⟩ : Fin 148)) (colE2 ⟨122, by decide⟩ 10 hp)
        (rowE2 (⟨122, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨122, by decide⟩ : Fin 148))
        (colE1 ⟨122, by decide⟩ 10 (transLenTr ⟨122, by decide⟩ 10 hp))
        (rowE1 (⟨122, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨122, by decide⟩ : Fin 148) ⟨122, by decide⟩ _
      (validAt ⟨122, by decide⟩ (listedAt ⟨122, by decide⟩ hj))
      (colE1 ⟨122, by decide⟩ 10 (transLenTr ⟨122, by decide⟩ 10 hp)) T122_122
      hfix122_122 hinj122_122 hcardT122_122
      (fun i => conj_mem_of_fixedPoints _ _ (T122_122 i) (hfix122_122 i) _)
      ⟨122, by decide⟩ ⟨122, by decide⟩ _
      (Q2.validAt ⟨122, by decide⟩ (Q2.listedAt ⟨122, by decide⟩
        (alnCheck_rep ⟨122, by decide⟩ hj hq).1))
      (colE2 ⟨122, by decide⟩ 10 hp) Q2.T122_122_2 Q2.hfix122_122_2 Q2.hinj122_122_2
      Q2.hcardT122_122_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T122_122_2 i) (Q2.hfix122_122_2 i) _)
      colCert_122_122_10.hD ?_).symm
  rw [alnId_122 j hj]


theorem leaf_122_122_11 (hp : 11 < (Q2.transData.getD 122 []).length)
    (j : Nat) (hj : j < (repChars.getD 122 []).length)
    (hq : (normIsRep.getD 122 []).getD j false = true) :
    species (Q2.reps (⟨122, by decide⟩ : Fin 148)) (colE2 ⟨122, by decide⟩ 11 hp)
        (rowE2 (⟨122, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨122, by decide⟩ : Fin 148))
        (colE1 ⟨122, by decide⟩ 11 (transLenTr ⟨122, by decide⟩ 11 hp))
        (rowE1 (⟨122, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨122, by decide⟩ : Fin 148) ⟨122, by decide⟩ _
      (validAt ⟨122, by decide⟩ (listedAt ⟨122, by decide⟩ hj))
      (colE1 ⟨122, by decide⟩ 11 (transLenTr ⟨122, by decide⟩ 11 hp)) T122_122
      hfix122_122 hinj122_122 hcardT122_122
      (fun i => conj_mem_of_fixedPoints _ _ (T122_122 i) (hfix122_122 i) _)
      ⟨122, by decide⟩ ⟨122, by decide⟩ _
      (Q2.validAt ⟨122, by decide⟩ (Q2.listedAt ⟨122, by decide⟩
        (alnCheck_rep ⟨122, by decide⟩ hj hq).1))
      (colE2 ⟨122, by decide⟩ 11 hp) Q2.T122_122_2 Q2.hfix122_122_2 Q2.hinj122_122_2
      Q2.hcardT122_122_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T122_122_2 i) (Q2.hfix122_122_2 i) _)
      colCert_122_122_11.hD ?_).symm
  rw [alnId_122 j hj]


theorem leaf_122_122_12 (hp : 12 < (Q2.transData.getD 122 []).length)
    (j : Nat) (hj : j < (repChars.getD 122 []).length)
    (hq : (normIsRep.getD 122 []).getD j false = true) :
    species (Q2.reps (⟨122, by decide⟩ : Fin 148)) (colE2 ⟨122, by decide⟩ 12 hp)
        (rowE2 (⟨122, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨122, by decide⟩ : Fin 148))
        (colE1 ⟨122, by decide⟩ 12 (transLenTr ⟨122, by decide⟩ 12 hp))
        (rowE1 (⟨122, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨122, by decide⟩ : Fin 148) ⟨122, by decide⟩ _
      (validAt ⟨122, by decide⟩ (listedAt ⟨122, by decide⟩ hj))
      (colE1 ⟨122, by decide⟩ 12 (transLenTr ⟨122, by decide⟩ 12 hp)) T122_122
      hfix122_122 hinj122_122 hcardT122_122
      (fun i => conj_mem_of_fixedPoints _ _ (T122_122 i) (hfix122_122 i) _)
      ⟨122, by decide⟩ ⟨122, by decide⟩ _
      (Q2.validAt ⟨122, by decide⟩ (Q2.listedAt ⟨122, by decide⟩
        (alnCheck_rep ⟨122, by decide⟩ hj hq).1))
      (colE2 ⟨122, by decide⟩ 12 hp) Q2.T122_122_2 Q2.hfix122_122_2 Q2.hinj122_122_2
      Q2.hcardT122_122_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T122_122_2 i) (Q2.hfix122_122_2 i) _)
      colCert_122_122_12.hD ?_).symm
  rw [alnId_122 j hj]


theorem leaf_122_122_13 (hp : 13 < (Q2.transData.getD 122 []).length)
    (j : Nat) (hj : j < (repChars.getD 122 []).length)
    (hq : (normIsRep.getD 122 []).getD j false = true) :
    species (Q2.reps (⟨122, by decide⟩ : Fin 148)) (colE2 ⟨122, by decide⟩ 13 hp)
        (rowE2 (⟨122, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨122, by decide⟩ : Fin 148))
        (colE1 ⟨122, by decide⟩ 13 (transLenTr ⟨122, by decide⟩ 13 hp))
        (rowE1 (⟨122, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨122, by decide⟩ : Fin 148) ⟨122, by decide⟩ _
      (validAt ⟨122, by decide⟩ (listedAt ⟨122, by decide⟩ hj))
      (colE1 ⟨122, by decide⟩ 13 (transLenTr ⟨122, by decide⟩ 13 hp)) T122_122
      hfix122_122 hinj122_122 hcardT122_122
      (fun i => conj_mem_of_fixedPoints _ _ (T122_122 i) (hfix122_122 i) _)
      ⟨122, by decide⟩ ⟨122, by decide⟩ _
      (Q2.validAt ⟨122, by decide⟩ (Q2.listedAt ⟨122, by decide⟩
        (alnCheck_rep ⟨122, by decide⟩ hj hq).1))
      (colE2 ⟨122, by decide⟩ 13 hp) Q2.T122_122_2 Q2.hfix122_122_2 Q2.hinj122_122_2
      Q2.hcardT122_122_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T122_122_2 i) (Q2.hfix122_122_2 i) _)
      colCert_122_122_13.hD ?_).symm
  rw [alnId_122 j hj]


theorem leaf_122_122_14 (hp : 14 < (Q2.transData.getD 122 []).length)
    (j : Nat) (hj : j < (repChars.getD 122 []).length)
    (hq : (normIsRep.getD 122 []).getD j false = true) :
    species (Q2.reps (⟨122, by decide⟩ : Fin 148)) (colE2 ⟨122, by decide⟩ 14 hp)
        (rowE2 (⟨122, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨122, by decide⟩ : Fin 148))
        (colE1 ⟨122, by decide⟩ 14 (transLenTr ⟨122, by decide⟩ 14 hp))
        (rowE1 (⟨122, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨122, by decide⟩ : Fin 148) ⟨122, by decide⟩ _
      (validAt ⟨122, by decide⟩ (listedAt ⟨122, by decide⟩ hj))
      (colE1 ⟨122, by decide⟩ 14 (transLenTr ⟨122, by decide⟩ 14 hp)) T122_122
      hfix122_122 hinj122_122 hcardT122_122
      (fun i => conj_mem_of_fixedPoints _ _ (T122_122 i) (hfix122_122 i) _)
      ⟨122, by decide⟩ ⟨122, by decide⟩ _
      (Q2.validAt ⟨122, by decide⟩ (Q2.listedAt ⟨122, by decide⟩
        (alnCheck_rep ⟨122, by decide⟩ hj hq).1))
      (colE2 ⟨122, by decide⟩ 14 hp) Q2.T122_122_2 Q2.hfix122_122_2 Q2.hinj122_122_2
      Q2.hcardT122_122_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T122_122_2 i) (Q2.hfix122_122_2 i) _)
      colCert_122_122_14.hD ?_).symm
  rw [alnId_122 j hj]


theorem leaf_122_122_15 (hp : 15 < (Q2.transData.getD 122 []).length)
    (j : Nat) (hj : j < (repChars.getD 122 []).length)
    (hq : (normIsRep.getD 122 []).getD j false = true) :
    species (Q2.reps (⟨122, by decide⟩ : Fin 148)) (colE2 ⟨122, by decide⟩ 15 hp)
        (rowE2 (⟨122, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨122, by decide⟩ : Fin 148))
        (colE1 ⟨122, by decide⟩ 15 (transLenTr ⟨122, by decide⟩ 15 hp))
        (rowE1 (⟨122, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨122, by decide⟩ : Fin 148) ⟨122, by decide⟩ _
      (validAt ⟨122, by decide⟩ (listedAt ⟨122, by decide⟩ hj))
      (colE1 ⟨122, by decide⟩ 15 (transLenTr ⟨122, by decide⟩ 15 hp)) T122_122
      hfix122_122 hinj122_122 hcardT122_122
      (fun i => conj_mem_of_fixedPoints _ _ (T122_122 i) (hfix122_122 i) _)
      ⟨122, by decide⟩ ⟨122, by decide⟩ _
      (Q2.validAt ⟨122, by decide⟩ (Q2.listedAt ⟨122, by decide⟩
        (alnCheck_rep ⟨122, by decide⟩ hj hq).1))
      (colE2 ⟨122, by decide⟩ 15 hp) Q2.T122_122_2 Q2.hfix122_122_2 Q2.hinj122_122_2
      Q2.hcardT122_122_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T122_122_2 i) (Q2.hfix122_122_2 i) _)
      colCert_122_122_15.hD ?_).symm
  rw [alnId_122 j hj]


theorem leaf_122_122_16 (hp : 16 < (Q2.transData.getD 122 []).length)
    (j : Nat) (hj : j < (repChars.getD 122 []).length)
    (hq : (normIsRep.getD 122 []).getD j false = true) :
    species (Q2.reps (⟨122, by decide⟩ : Fin 148)) (colE2 ⟨122, by decide⟩ 16 hp)
        (rowE2 (⟨122, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨122, by decide⟩ : Fin 148))
        (colE1 ⟨122, by decide⟩ 16 (transLenTr ⟨122, by decide⟩ 16 hp))
        (rowE1 (⟨122, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨122, by decide⟩ : Fin 148) ⟨122, by decide⟩ _
      (validAt ⟨122, by decide⟩ (listedAt ⟨122, by decide⟩ hj))
      (colE1 ⟨122, by decide⟩ 16 (transLenTr ⟨122, by decide⟩ 16 hp)) T122_122
      hfix122_122 hinj122_122 hcardT122_122
      (fun i => conj_mem_of_fixedPoints _ _ (T122_122 i) (hfix122_122 i) _)
      ⟨122, by decide⟩ ⟨122, by decide⟩ _
      (Q2.validAt ⟨122, by decide⟩ (Q2.listedAt ⟨122, by decide⟩
        (alnCheck_rep ⟨122, by decide⟩ hj hq).1))
      (colE2 ⟨122, by decide⟩ 16 hp) Q2.T122_122_2 Q2.hfix122_122_2 Q2.hinj122_122_2
      Q2.hcardT122_122_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T122_122_2 i) (Q2.hfix122_122_2 i) _)
      colCert_122_122_16.hD ?_).symm
  rw [alnId_122 j hj]


theorem leaf_122_122_17 (hp : 17 < (Q2.transData.getD 122 []).length)
    (j : Nat) (hj : j < (repChars.getD 122 []).length)
    (hq : (normIsRep.getD 122 []).getD j false = true) :
    species (Q2.reps (⟨122, by decide⟩ : Fin 148)) (colE2 ⟨122, by decide⟩ 17 hp)
        (rowE2 (⟨122, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨122, by decide⟩ : Fin 148))
        (colE1 ⟨122, by decide⟩ 17 (transLenTr ⟨122, by decide⟩ 17 hp))
        (rowE1 (⟨122, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨122, by decide⟩ : Fin 148) ⟨122, by decide⟩ _
      (validAt ⟨122, by decide⟩ (listedAt ⟨122, by decide⟩ hj))
      (colE1 ⟨122, by decide⟩ 17 (transLenTr ⟨122, by decide⟩ 17 hp)) T122_122
      hfix122_122 hinj122_122 hcardT122_122
      (fun i => conj_mem_of_fixedPoints _ _ (T122_122 i) (hfix122_122 i) _)
      ⟨122, by decide⟩ ⟨122, by decide⟩ _
      (Q2.validAt ⟨122, by decide⟩ (Q2.listedAt ⟨122, by decide⟩
        (alnCheck_rep ⟨122, by decide⟩ hj hq).1))
      (colE2 ⟨122, by decide⟩ 17 hp) Q2.T122_122_2 Q2.hfix122_122_2 Q2.hinj122_122_2
      Q2.hcardT122_122_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T122_122_2 i) (Q2.hfix122_122_2 i) _)
      colCert_122_122_17.hD ?_).symm
  rw [alnId_122 j hj]


theorem leaf_122_122_18 (hp : 18 < (Q2.transData.getD 122 []).length)
    (j : Nat) (hj : j < (repChars.getD 122 []).length)
    (hq : (normIsRep.getD 122 []).getD j false = true) :
    species (Q2.reps (⟨122, by decide⟩ : Fin 148)) (colE2 ⟨122, by decide⟩ 18 hp)
        (rowE2 (⟨122, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨122, by decide⟩ : Fin 148))
        (colE1 ⟨122, by decide⟩ 18 (transLenTr ⟨122, by decide⟩ 18 hp))
        (rowE1 (⟨122, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨122, by decide⟩ : Fin 148) ⟨122, by decide⟩ _
      (validAt ⟨122, by decide⟩ (listedAt ⟨122, by decide⟩ hj))
      (colE1 ⟨122, by decide⟩ 18 (transLenTr ⟨122, by decide⟩ 18 hp)) T122_122
      hfix122_122 hinj122_122 hcardT122_122
      (fun i => conj_mem_of_fixedPoints _ _ (T122_122 i) (hfix122_122 i) _)
      ⟨122, by decide⟩ ⟨122, by decide⟩ _
      (Q2.validAt ⟨122, by decide⟩ (Q2.listedAt ⟨122, by decide⟩
        (alnCheck_rep ⟨122, by decide⟩ hj hq).1))
      (colE2 ⟨122, by decide⟩ 18 hp) Q2.T122_122_2 Q2.hfix122_122_2 Q2.hinj122_122_2
      Q2.hcardT122_122_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T122_122_2 i) (Q2.hfix122_122_2 i) _)
      colCert_122_122_18.hD ?_).symm
  rw [alnId_122 j hj]


theorem leaf_122_122_19 (hp : 19 < (Q2.transData.getD 122 []).length)
    (j : Nat) (hj : j < (repChars.getD 122 []).length)
    (hq : (normIsRep.getD 122 []).getD j false = true) :
    species (Q2.reps (⟨122, by decide⟩ : Fin 148)) (colE2 ⟨122, by decide⟩ 19 hp)
        (rowE2 (⟨122, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨122, by decide⟩ : Fin 148))
        (colE1 ⟨122, by decide⟩ 19 (transLenTr ⟨122, by decide⟩ 19 hp))
        (rowE1 (⟨122, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨122, by decide⟩ : Fin 148) ⟨122, by decide⟩ _
      (validAt ⟨122, by decide⟩ (listedAt ⟨122, by decide⟩ hj))
      (colE1 ⟨122, by decide⟩ 19 (transLenTr ⟨122, by decide⟩ 19 hp)) T122_122
      hfix122_122 hinj122_122 hcardT122_122
      (fun i => conj_mem_of_fixedPoints _ _ (T122_122 i) (hfix122_122 i) _)
      ⟨122, by decide⟩ ⟨122, by decide⟩ _
      (Q2.validAt ⟨122, by decide⟩ (Q2.listedAt ⟨122, by decide⟩
        (alnCheck_rep ⟨122, by decide⟩ hj hq).1))
      (colE2 ⟨122, by decide⟩ 19 hp) Q2.T122_122_2 Q2.hfix122_122_2 Q2.hinj122_122_2
      Q2.hcardT122_122_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T122_122_2 i) (Q2.hfix122_122_2 i) _)
      colCert_122_122_19.hD ?_).symm
  rw [alnId_122 j hj]


theorem leaf_122_122_20 (hp : 20 < (Q2.transData.getD 122 []).length)
    (j : Nat) (hj : j < (repChars.getD 122 []).length)
    (hq : (normIsRep.getD 122 []).getD j false = true) :
    species (Q2.reps (⟨122, by decide⟩ : Fin 148)) (colE2 ⟨122, by decide⟩ 20 hp)
        (rowE2 (⟨122, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨122, by decide⟩ : Fin 148))
        (colE1 ⟨122, by decide⟩ 20 (transLenTr ⟨122, by decide⟩ 20 hp))
        (rowE1 (⟨122, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨122, by decide⟩ : Fin 148) ⟨122, by decide⟩ _
      (validAt ⟨122, by decide⟩ (listedAt ⟨122, by decide⟩ hj))
      (colE1 ⟨122, by decide⟩ 20 (transLenTr ⟨122, by decide⟩ 20 hp)) T122_122
      hfix122_122 hinj122_122 hcardT122_122
      (fun i => conj_mem_of_fixedPoints _ _ (T122_122 i) (hfix122_122 i) _)
      ⟨122, by decide⟩ ⟨122, by decide⟩ _
      (Q2.validAt ⟨122, by decide⟩ (Q2.listedAt ⟨122, by decide⟩
        (alnCheck_rep ⟨122, by decide⟩ hj hq).1))
      (colE2 ⟨122, by decide⟩ 20 hp) Q2.T122_122_2 Q2.hfix122_122_2 Q2.hinj122_122_2
      Q2.hcardT122_122_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T122_122_2 i) (Q2.hfix122_122_2 i) _)
      colCert_122_122_20.hD ?_).symm
  rw [alnId_122 j hj]


theorem leaf_122_122_21 (hp : 21 < (Q2.transData.getD 122 []).length)
    (j : Nat) (hj : j < (repChars.getD 122 []).length)
    (hq : (normIsRep.getD 122 []).getD j false = true) :
    species (Q2.reps (⟨122, by decide⟩ : Fin 148)) (colE2 ⟨122, by decide⟩ 21 hp)
        (rowE2 (⟨122, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨122, by decide⟩ : Fin 148))
        (colE1 ⟨122, by decide⟩ 21 (transLenTr ⟨122, by decide⟩ 21 hp))
        (rowE1 (⟨122, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨122, by decide⟩ : Fin 148) ⟨122, by decide⟩ _
      (validAt ⟨122, by decide⟩ (listedAt ⟨122, by decide⟩ hj))
      (colE1 ⟨122, by decide⟩ 21 (transLenTr ⟨122, by decide⟩ 21 hp)) T122_122
      hfix122_122 hinj122_122 hcardT122_122
      (fun i => conj_mem_of_fixedPoints _ _ (T122_122 i) (hfix122_122 i) _)
      ⟨122, by decide⟩ ⟨122, by decide⟩ _
      (Q2.validAt ⟨122, by decide⟩ (Q2.listedAt ⟨122, by decide⟩
        (alnCheck_rep ⟨122, by decide⟩ hj hq).1))
      (colE2 ⟨122, by decide⟩ 21 hp) Q2.T122_122_2 Q2.hfix122_122_2 Q2.hinj122_122_2
      Q2.hcardT122_122_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T122_122_2 i) (Q2.hfix122_122_2 i) _)
      colCert_122_122_21.hD ?_).symm
  rw [alnId_122 j hj]


theorem leaf_122_122_22 (hp : 22 < (Q2.transData.getD 122 []).length)
    (j : Nat) (hj : j < (repChars.getD 122 []).length)
    (hq : (normIsRep.getD 122 []).getD j false = true) :
    species (Q2.reps (⟨122, by decide⟩ : Fin 148)) (colE2 ⟨122, by decide⟩ 22 hp)
        (rowE2 (⟨122, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨122, by decide⟩ : Fin 148))
        (colE1 ⟨122, by decide⟩ 22 (transLenTr ⟨122, by decide⟩ 22 hp))
        (rowE1 (⟨122, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨122, by decide⟩ : Fin 148) ⟨122, by decide⟩ _
      (validAt ⟨122, by decide⟩ (listedAt ⟨122, by decide⟩ hj))
      (colE1 ⟨122, by decide⟩ 22 (transLenTr ⟨122, by decide⟩ 22 hp)) T122_122
      hfix122_122 hinj122_122 hcardT122_122
      (fun i => conj_mem_of_fixedPoints _ _ (T122_122 i) (hfix122_122 i) _)
      ⟨122, by decide⟩ ⟨122, by decide⟩ _
      (Q2.validAt ⟨122, by decide⟩ (Q2.listedAt ⟨122, by decide⟩
        (alnCheck_rep ⟨122, by decide⟩ hj hq).1))
      (colE2 ⟨122, by decide⟩ 22 hp) Q2.T122_122_2 Q2.hfix122_122_2 Q2.hinj122_122_2
      Q2.hcardT122_122_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T122_122_2 i) (Q2.hfix122_122_2 i) _)
      colCert_122_122_22.hD ?_).symm
  rw [alnId_122 j hj]


theorem leaf_122_122_23 (hp : 23 < (Q2.transData.getD 122 []).length)
    (j : Nat) (hj : j < (repChars.getD 122 []).length)
    (hq : (normIsRep.getD 122 []).getD j false = true) :
    species (Q2.reps (⟨122, by decide⟩ : Fin 148)) (colE2 ⟨122, by decide⟩ 23 hp)
        (rowE2 (⟨122, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨122, by decide⟩ : Fin 148))
        (colE1 ⟨122, by decide⟩ 23 (transLenTr ⟨122, by decide⟩ 23 hp))
        (rowE1 (⟨122, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨122, by decide⟩ : Fin 148) ⟨122, by decide⟩ _
      (validAt ⟨122, by decide⟩ (listedAt ⟨122, by decide⟩ hj))
      (colE1 ⟨122, by decide⟩ 23 (transLenTr ⟨122, by decide⟩ 23 hp)) T122_122
      hfix122_122 hinj122_122 hcardT122_122
      (fun i => conj_mem_of_fixedPoints _ _ (T122_122 i) (hfix122_122 i) _)
      ⟨122, by decide⟩ ⟨122, by decide⟩ _
      (Q2.validAt ⟨122, by decide⟩ (Q2.listedAt ⟨122, by decide⟩
        (alnCheck_rep ⟨122, by decide⟩ hj hq).1))
      (colE2 ⟨122, by decide⟩ 23 hp) Q2.T122_122_2 Q2.hfix122_122_2 Q2.hinj122_122_2
      Q2.hcardT122_122_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T122_122_2 i) (Q2.hfix122_122_2 i) _)
      colCert_122_122_23.hD ?_).symm
  rw [alnId_122 j hj]


theorem leaf_122_122_24 (hp : 24 < (Q2.transData.getD 122 []).length)
    (j : Nat) (hj : j < (repChars.getD 122 []).length)
    (hq : (normIsRep.getD 122 []).getD j false = true) :
    species (Q2.reps (⟨122, by decide⟩ : Fin 148)) (colE2 ⟨122, by decide⟩ 24 hp)
        (rowE2 (⟨122, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨122, by decide⟩ : Fin 148))
        (colE1 ⟨122, by decide⟩ 24 (transLenTr ⟨122, by decide⟩ 24 hp))
        (rowE1 (⟨122, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨122, by decide⟩ : Fin 148) ⟨122, by decide⟩ _
      (validAt ⟨122, by decide⟩ (listedAt ⟨122, by decide⟩ hj))
      (colE1 ⟨122, by decide⟩ 24 (transLenTr ⟨122, by decide⟩ 24 hp)) T122_122
      hfix122_122 hinj122_122 hcardT122_122
      (fun i => conj_mem_of_fixedPoints _ _ (T122_122 i) (hfix122_122 i) _)
      ⟨122, by decide⟩ ⟨122, by decide⟩ _
      (Q2.validAt ⟨122, by decide⟩ (Q2.listedAt ⟨122, by decide⟩
        (alnCheck_rep ⟨122, by decide⟩ hj hq).1))
      (colE2 ⟨122, by decide⟩ 24 hp) Q2.T122_122_2 Q2.hfix122_122_2 Q2.hinj122_122_2
      Q2.hcardT122_122_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T122_122_2 i) (Q2.hfix122_122_2 i) _)
      colCert_122_122_24.hD ?_).symm
  rw [alnId_122 j hj]


theorem leaf_123_2_0 (hp : 0 < (Q2.transData.getD 2 []).length)
    (j : Nat) (hj : j < (repChars.getD 123 []).length)
    (hq : (normIsRep.getD 123 []).getD j false = true) :
    species (Q2.reps (⟨2, by decide⟩ : Fin 148)) (colE2 ⟨2, by decide⟩ 0 hp)
        (rowE2 (⟨123, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨2, by decide⟩ : Fin 148))
        (colE1 ⟨2, by decide⟩ 0 (transLenTr ⟨2, by decide⟩ 0 hp))
        (rowE1 (⟨123, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨123, by decide⟩ : Fin 148) ⟨2, by decide⟩ _
      (validAt ⟨123, by decide⟩ (listedAt ⟨123, by decide⟩ hj))
      (colE1 ⟨2, by decide⟩ 0 (transLenTr ⟨2, by decide⟩ 0 hp)) T123_2
      hfix123_2 hinj123_2 hcardT123_2
      (fun i => conj_mem_of_fixedPoints _ _ (T123_2 i) (hfix123_2 i) _)
      ⟨123, by decide⟩ ⟨2, by decide⟩ _
      (Q2.validAt ⟨123, by decide⟩ (Q2.listedAt ⟨123, by decide⟩
        (alnCheck_rep ⟨123, by decide⟩ hj hq).1))
      (colE2 ⟨2, by decide⟩ 0 hp) Q2.T123_2_2 Q2.hfix123_2_2 Q2.hinj123_2_2
      Q2.hcardT123_2_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T123_2_2 i) (Q2.hfix123_2_2 i) _)
      colCert_123_2_0.hD ?_).symm
  rw [alnId_123 j hj]


theorem leaf_123_2_1 (hp : 1 < (Q2.transData.getD 2 []).length)
    (j : Nat) (hj : j < (repChars.getD 123 []).length)
    (hq : (normIsRep.getD 123 []).getD j false = true) :
    species (Q2.reps (⟨2, by decide⟩ : Fin 148)) (colE2 ⟨2, by decide⟩ 1 hp)
        (rowE2 (⟨123, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨2, by decide⟩ : Fin 148))
        (colE1 ⟨2, by decide⟩ 1 (transLenTr ⟨2, by decide⟩ 1 hp))
        (rowE1 (⟨123, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨123, by decide⟩ : Fin 148) ⟨2, by decide⟩ _
      (validAt ⟨123, by decide⟩ (listedAt ⟨123, by decide⟩ hj))
      (colE1 ⟨2, by decide⟩ 1 (transLenTr ⟨2, by decide⟩ 1 hp)) T123_2
      hfix123_2 hinj123_2 hcardT123_2
      (fun i => conj_mem_of_fixedPoints _ _ (T123_2 i) (hfix123_2 i) _)
      ⟨123, by decide⟩ ⟨2, by decide⟩ _
      (Q2.validAt ⟨123, by decide⟩ (Q2.listedAt ⟨123, by decide⟩
        (alnCheck_rep ⟨123, by decide⟩ hj hq).1))
      (colE2 ⟨2, by decide⟩ 1 hp) Q2.T123_2_2 Q2.hfix123_2_2 Q2.hinj123_2_2
      Q2.hcardT123_2_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T123_2_2 i) (Q2.hfix123_2_2 i) _)
      ?_).symm
  rw [show colData1 (⟨123, by decide⟩ : Fin 148)
        ((colE1 ⟨2, by decide⟩ 1 (transLenTr ⟨2, by decide⟩ 1 hp) : ↥(reps ⟨2, by decide⟩)) : Coordinate 1)
        T123_2 = colFn colCertDiv_123_2_1.D1 (m := 5) from colCertDiv_123_2_1.bind1,
    show colData2 (⟨123, by decide⟩ : Fin 148)
        ((colE2 ⟨2, by decide⟩ 1 hp : ↥(Q2.reps ⟨2, by decide⟩)) : Coordinate 2)
        Q2.T123_2_2 = colFn colCertDiv_123_2_1.D2 (m := 5) from colCertDiv_123_2_1.bind2]
  rw [alnId_123 j hj]
  exact fastcode_of_div ⟨123, by decide⟩ _ _ _
    ((alnId_123 j hj) ▸ Q2.listedAt (⟨123, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨123, by decide⟩ : Fin 148) hj hq).1) colCertDiv_123_2_1_match


theorem leaf_123_2_2 (hp : 2 < (Q2.transData.getD 2 []).length)
    (j : Nat) (hj : j < (repChars.getD 123 []).length)
    (hq : (normIsRep.getD 123 []).getD j false = true) :
    species (Q2.reps (⟨2, by decide⟩ : Fin 148)) (colE2 ⟨2, by decide⟩ 2 hp)
        (rowE2 (⟨123, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨2, by decide⟩ : Fin 148))
        (colE1 ⟨2, by decide⟩ 2 (transLenTr ⟨2, by decide⟩ 2 hp))
        (rowE1 (⟨123, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨123, by decide⟩ : Fin 148) ⟨2, by decide⟩ _
      (validAt ⟨123, by decide⟩ (listedAt ⟨123, by decide⟩ hj))
      (colE1 ⟨2, by decide⟩ 2 (transLenTr ⟨2, by decide⟩ 2 hp)) T123_2
      hfix123_2 hinj123_2 hcardT123_2
      (fun i => conj_mem_of_fixedPoints _ _ (T123_2 i) (hfix123_2 i) _)
      ⟨123, by decide⟩ ⟨2, by decide⟩ _
      (Q2.validAt ⟨123, by decide⟩ (Q2.listedAt ⟨123, by decide⟩
        (alnCheck_rep ⟨123, by decide⟩ hj hq).1))
      (colE2 ⟨2, by decide⟩ 2 hp) Q2.T123_2_2 Q2.hfix123_2_2 Q2.hinj123_2_2
      Q2.hcardT123_2_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T123_2_2 i) (Q2.hfix123_2_2 i) _)
      ?_).symm
  rw [show colData1 (⟨123, by decide⟩ : Fin 148)
        ((colE1 ⟨2, by decide⟩ 2 (transLenTr ⟨2, by decide⟩ 2 hp) : ↥(reps ⟨2, by decide⟩)) : Coordinate 1)
        T123_2 = colFn colCertDiv_123_2_2.D1 (m := 5) from colCertDiv_123_2_2.bind1,
    show colData2 (⟨123, by decide⟩ : Fin 148)
        ((colE2 ⟨2, by decide⟩ 2 hp : ↥(Q2.reps ⟨2, by decide⟩)) : Coordinate 2)
        Q2.T123_2_2 = colFn colCertDiv_123_2_2.D2 (m := 5) from colCertDiv_123_2_2.bind2]
  rw [alnId_123 j hj]
  exact fastcode_of_div ⟨123, by decide⟩ _ _ _
    ((alnId_123 j hj) ▸ Q2.listedAt (⟨123, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨123, by decide⟩ : Fin 148) hj hq).1) colCertDiv_123_2_2_match


theorem leaf_123_2_3 (hp : 3 < (Q2.transData.getD 2 []).length)
    (j : Nat) (hj : j < (repChars.getD 123 []).length)
    (hq : (normIsRep.getD 123 []).getD j false = true) :
    species (Q2.reps (⟨2, by decide⟩ : Fin 148)) (colE2 ⟨2, by decide⟩ 3 hp)
        (rowE2 (⟨123, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨2, by decide⟩ : Fin 148))
        (colE1 ⟨2, by decide⟩ 3 (transLenTr ⟨2, by decide⟩ 3 hp))
        (rowE1 (⟨123, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨123, by decide⟩ : Fin 148) ⟨2, by decide⟩ _
      (validAt ⟨123, by decide⟩ (listedAt ⟨123, by decide⟩ hj))
      (colE1 ⟨2, by decide⟩ 3 (transLenTr ⟨2, by decide⟩ 3 hp)) T123_2
      hfix123_2 hinj123_2 hcardT123_2
      (fun i => conj_mem_of_fixedPoints _ _ (T123_2 i) (hfix123_2 i) _)
      ⟨123, by decide⟩ ⟨2, by decide⟩ _
      (Q2.validAt ⟨123, by decide⟩ (Q2.listedAt ⟨123, by decide⟩
        (alnCheck_rep ⟨123, by decide⟩ hj hq).1))
      (colE2 ⟨2, by decide⟩ 3 hp) Q2.T123_2_2 Q2.hfix123_2_2 Q2.hinj123_2_2
      Q2.hcardT123_2_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T123_2_2 i) (Q2.hfix123_2_2 i) _)
      ?_).symm
  rw [show colData1 (⟨123, by decide⟩ : Fin 148)
        ((colE1 ⟨2, by decide⟩ 3 (transLenTr ⟨2, by decide⟩ 3 hp) : ↥(reps ⟨2, by decide⟩)) : Coordinate 1)
        T123_2 = colFn colCertDiv_123_2_3.D1 (m := 5) from colCertDiv_123_2_3.bind1,
    show colData2 (⟨123, by decide⟩ : Fin 148)
        ((colE2 ⟨2, by decide⟩ 3 hp : ↥(Q2.reps ⟨2, by decide⟩)) : Coordinate 2)
        Q2.T123_2_2 = colFn colCertDiv_123_2_3.D2 (m := 5) from colCertDiv_123_2_3.bind2]
  rw [alnId_123 j hj]
  exact fastcode_of_div ⟨123, by decide⟩ _ _ _
    ((alnId_123 j hj) ▸ Q2.listedAt (⟨123, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨123, by decide⟩ : Fin 148) hj hq).1) colCertDiv_123_2_3_match


theorem leaf_123_2_4 (hp : 4 < (Q2.transData.getD 2 []).length)
    (j : Nat) (hj : j < (repChars.getD 123 []).length)
    (hq : (normIsRep.getD 123 []).getD j false = true) :
    species (Q2.reps (⟨2, by decide⟩ : Fin 148)) (colE2 ⟨2, by decide⟩ 4 hp)
        (rowE2 (⟨123, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨2, by decide⟩ : Fin 148))
        (colE1 ⟨2, by decide⟩ 4 (transLenTr ⟨2, by decide⟩ 4 hp))
        (rowE1 (⟨123, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨123, by decide⟩ : Fin 148) ⟨2, by decide⟩ _
      (validAt ⟨123, by decide⟩ (listedAt ⟨123, by decide⟩ hj))
      (colE1 ⟨2, by decide⟩ 4 (transLenTr ⟨2, by decide⟩ 4 hp)) T123_2
      hfix123_2 hinj123_2 hcardT123_2
      (fun i => conj_mem_of_fixedPoints _ _ (T123_2 i) (hfix123_2 i) _)
      ⟨123, by decide⟩ ⟨2, by decide⟩ _
      (Q2.validAt ⟨123, by decide⟩ (Q2.listedAt ⟨123, by decide⟩
        (alnCheck_rep ⟨123, by decide⟩ hj hq).1))
      (colE2 ⟨2, by decide⟩ 4 hp) Q2.T123_2_2 Q2.hfix123_2_2 Q2.hinj123_2_2
      Q2.hcardT123_2_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T123_2_2 i) (Q2.hfix123_2_2 i) _)
      ?_).symm
  rw [show colData1 (⟨123, by decide⟩ : Fin 148)
        ((colE1 ⟨2, by decide⟩ 4 (transLenTr ⟨2, by decide⟩ 4 hp) : ↥(reps ⟨2, by decide⟩)) : Coordinate 1)
        T123_2 = colFn colCertDiv_123_2_4.D1 (m := 5) from colCertDiv_123_2_4.bind1,
    show colData2 (⟨123, by decide⟩ : Fin 148)
        ((colE2 ⟨2, by decide⟩ 4 hp : ↥(Q2.reps ⟨2, by decide⟩)) : Coordinate 2)
        Q2.T123_2_2 = colFn colCertDiv_123_2_4.D2 (m := 5) from colCertDiv_123_2_4.bind2]
  rw [alnId_123 j hj]
  exact fastcode_of_div ⟨123, by decide⟩ _ _ _
    ((alnId_123 j hj) ▸ Q2.listedAt (⟨123, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨123, by decide⟩ : Fin 148) hj hq).1) colCertDiv_123_2_4_match


theorem leaf_123_10_0 (hp : 0 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 123 []).length)
    (hq : (normIsRep.getD 123 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 0 hp)
        (rowE2 (⟨123, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 0 (transLenTr ⟨10, by decide⟩ 0 hp))
        (rowE1 (⟨123, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨123, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨123, by decide⟩ (listedAt ⟨123, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 0 (transLenTr ⟨10, by decide⟩ 0 hp)) T123_10
      hfix123_10 hinj123_10 hcardT123_10
      (fun i => conj_mem_of_fixedPoints _ _ (T123_10 i) (hfix123_10 i) _)
      ⟨123, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨123, by decide⟩ (Q2.listedAt ⟨123, by decide⟩
        (alnCheck_rep ⟨123, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 0 hp) Q2.T123_10_2 Q2.hfix123_10_2 Q2.hinj123_10_2
      Q2.hcardT123_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T123_10_2 i) (Q2.hfix123_10_2 i) _)
      colCert_123_10_0.hD ?_).symm
  rw [alnId_123 j hj]


theorem leaf_123_10_1 (hp : 1 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 123 []).length)
    (hq : (normIsRep.getD 123 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 1 hp)
        (rowE2 (⟨123, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 1 (transLenTr ⟨10, by decide⟩ 1 hp))
        (rowE1 (⟨123, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨123, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨123, by decide⟩ (listedAt ⟨123, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 1 (transLenTr ⟨10, by decide⟩ 1 hp)) T123_10
      hfix123_10 hinj123_10 hcardT123_10
      (fun i => conj_mem_of_fixedPoints _ _ (T123_10 i) (hfix123_10 i) _)
      ⟨123, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨123, by decide⟩ (Q2.listedAt ⟨123, by decide⟩
        (alnCheck_rep ⟨123, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 1 hp) Q2.T123_10_2 Q2.hfix123_10_2 Q2.hinj123_10_2
      Q2.hcardT123_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T123_10_2 i) (Q2.hfix123_10_2 i) _)
      colCert_123_10_1.hD ?_).symm
  rw [alnId_123 j hj]


theorem leaf_123_10_2 (hp : 2 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 123 []).length)
    (hq : (normIsRep.getD 123 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 2 hp)
        (rowE2 (⟨123, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 2 (transLenTr ⟨10, by decide⟩ 2 hp))
        (rowE1 (⟨123, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨123, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨123, by decide⟩ (listedAt ⟨123, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 2 (transLenTr ⟨10, by decide⟩ 2 hp)) T123_10
      hfix123_10 hinj123_10 hcardT123_10
      (fun i => conj_mem_of_fixedPoints _ _ (T123_10 i) (hfix123_10 i) _)
      ⟨123, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨123, by decide⟩ (Q2.listedAt ⟨123, by decide⟩
        (alnCheck_rep ⟨123, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 2 hp) Q2.T123_10_2 Q2.hfix123_10_2 Q2.hinj123_10_2
      Q2.hcardT123_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T123_10_2 i) (Q2.hfix123_10_2 i) _)
      colCert_123_10_2.hD ?_).symm
  rw [alnId_123 j hj]


theorem leaf_123_10_3 (hp : 3 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 123 []).length)
    (hq : (normIsRep.getD 123 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 3 hp)
        (rowE2 (⟨123, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 3 (transLenTr ⟨10, by decide⟩ 3 hp))
        (rowE1 (⟨123, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨123, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨123, by decide⟩ (listedAt ⟨123, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 3 (transLenTr ⟨10, by decide⟩ 3 hp)) T123_10
      hfix123_10 hinj123_10 hcardT123_10
      (fun i => conj_mem_of_fixedPoints _ _ (T123_10 i) (hfix123_10 i) _)
      ⟨123, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨123, by decide⟩ (Q2.listedAt ⟨123, by decide⟩
        (alnCheck_rep ⟨123, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 3 hp) Q2.T123_10_2 Q2.hfix123_10_2 Q2.hinj123_10_2
      Q2.hcardT123_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T123_10_2 i) (Q2.hfix123_10_2 i) _)
      colCert_123_10_3.hD ?_).symm
  rw [alnId_123 j hj]


theorem leaf_123_10_4 (hp : 4 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 123 []).length)
    (hq : (normIsRep.getD 123 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 4 hp)
        (rowE2 (⟨123, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 4 (transLenTr ⟨10, by decide⟩ 4 hp))
        (rowE1 (⟨123, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨123, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨123, by decide⟩ (listedAt ⟨123, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 4 (transLenTr ⟨10, by decide⟩ 4 hp)) T123_10
      hfix123_10 hinj123_10 hcardT123_10
      (fun i => conj_mem_of_fixedPoints _ _ (T123_10 i) (hfix123_10 i) _)
      ⟨123, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨123, by decide⟩ (Q2.listedAt ⟨123, by decide⟩
        (alnCheck_rep ⟨123, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 4 hp) Q2.T123_10_2 Q2.hfix123_10_2 Q2.hinj123_10_2
      Q2.hcardT123_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T123_10_2 i) (Q2.hfix123_10_2 i) _)
      colCert_123_10_4.hD ?_).symm
  rw [alnId_123 j hj]


theorem leaf_123_12_0 (hp : 0 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 123 []).length)
    (hq : (normIsRep.getD 123 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 0 hp)
        (rowE2 (⟨123, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp))
        (rowE1 (⟨123, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨123, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨123, by decide⟩ (listedAt ⟨123, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp)) T123_12
      hfix123_12 hinj123_12 hcardT123_12
      (fun i => conj_mem_of_fixedPoints _ _ (T123_12 i) (hfix123_12 i) _)
      ⟨123, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨123, by decide⟩ (Q2.listedAt ⟨123, by decide⟩
        (alnCheck_rep ⟨123, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 0 hp) Q2.T123_12_2 Q2.hfix123_12_2 Q2.hinj123_12_2
      Q2.hcardT123_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T123_12_2 i) (Q2.hfix123_12_2 i) _)
      colCert_123_12_0.hD ?_).symm
  rw [alnId_123 j hj]


theorem leaf_123_12_1 (hp : 1 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 123 []).length)
    (hq : (normIsRep.getD 123 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 1 hp)
        (rowE2 (⟨123, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp))
        (rowE1 (⟨123, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨123, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨123, by decide⟩ (listedAt ⟨123, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp)) T123_12
      hfix123_12 hinj123_12 hcardT123_12
      (fun i => conj_mem_of_fixedPoints _ _ (T123_12 i) (hfix123_12 i) _)
      ⟨123, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨123, by decide⟩ (Q2.listedAt ⟨123, by decide⟩
        (alnCheck_rep ⟨123, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 1 hp) Q2.T123_12_2 Q2.hfix123_12_2 Q2.hinj123_12_2
      Q2.hcardT123_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T123_12_2 i) (Q2.hfix123_12_2 i) _)
      colCert_123_12_1.hD ?_).symm
  rw [alnId_123 j hj]


theorem leaf_123_12_2 (hp : 2 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 123 []).length)
    (hq : (normIsRep.getD 123 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 2 hp)
        (rowE2 (⟨123, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp))
        (rowE1 (⟨123, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨123, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨123, by decide⟩ (listedAt ⟨123, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp)) T123_12
      hfix123_12 hinj123_12 hcardT123_12
      (fun i => conj_mem_of_fixedPoints _ _ (T123_12 i) (hfix123_12 i) _)
      ⟨123, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨123, by decide⟩ (Q2.listedAt ⟨123, by decide⟩
        (alnCheck_rep ⟨123, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 2 hp) Q2.T123_12_2 Q2.hfix123_12_2 Q2.hinj123_12_2
      Q2.hcardT123_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T123_12_2 i) (Q2.hfix123_12_2 i) _)
      colCert_123_12_2.hD ?_).symm
  rw [alnId_123 j hj]


theorem leaf_123_12_3 (hp : 3 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 123 []).length)
    (hq : (normIsRep.getD 123 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 3 hp)
        (rowE2 (⟨123, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp))
        (rowE1 (⟨123, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨123, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨123, by decide⟩ (listedAt ⟨123, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp)) T123_12
      hfix123_12 hinj123_12 hcardT123_12
      (fun i => conj_mem_of_fixedPoints _ _ (T123_12 i) (hfix123_12 i) _)
      ⟨123, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨123, by decide⟩ (Q2.listedAt ⟨123, by decide⟩
        (alnCheck_rep ⟨123, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 3 hp) Q2.T123_12_2 Q2.hfix123_12_2 Q2.hinj123_12_2
      Q2.hcardT123_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T123_12_2 i) (Q2.hfix123_12_2 i) _)
      colCert_123_12_3.hD ?_).symm
  rw [alnId_123 j hj]


theorem leaf_123_12_4 (hp : 4 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 123 []).length)
    (hq : (normIsRep.getD 123 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 4 hp)
        (rowE2 (⟨123, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp))
        (rowE1 (⟨123, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨123, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨123, by decide⟩ (listedAt ⟨123, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp)) T123_12
      hfix123_12 hinj123_12 hcardT123_12
      (fun i => conj_mem_of_fixedPoints _ _ (T123_12 i) (hfix123_12 i) _)
      ⟨123, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨123, by decide⟩ (Q2.listedAt ⟨123, by decide⟩
        (alnCheck_rep ⟨123, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 4 hp) Q2.T123_12_2 Q2.hfix123_12_2 Q2.hinj123_12_2
      Q2.hcardT123_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T123_12_2 i) (Q2.hfix123_12_2 i) _)
      colCert_123_12_4.hD ?_).symm
  rw [alnId_123 j hj]


theorem leaf_123_20_0 (hp : 0 < (Q2.transData.getD 20 []).length)
    (j : Nat) (hj : j < (repChars.getD 123 []).length)
    (hq : (normIsRep.getD 123 []).getD j false = true) :
    species (Q2.reps (⟨20, by decide⟩ : Fin 148)) (colE2 ⟨20, by decide⟩ 0 hp)
        (rowE2 (⟨123, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨20, by decide⟩ : Fin 148))
        (colE1 ⟨20, by decide⟩ 0 (transLenTr ⟨20, by decide⟩ 0 hp))
        (rowE1 (⟨123, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨123, by decide⟩ : Fin 148) ⟨20, by decide⟩ _
      (validAt ⟨123, by decide⟩ (listedAt ⟨123, by decide⟩ hj))
      (colE1 ⟨20, by decide⟩ 0 (transLenTr ⟨20, by decide⟩ 0 hp)) T123_20
      hfix123_20 hinj123_20 hcardT123_20
      (fun i => conj_mem_of_fixedPoints _ _ (T123_20 i) (hfix123_20 i) _)
      ⟨123, by decide⟩ ⟨20, by decide⟩ _
      (Q2.validAt ⟨123, by decide⟩ (Q2.listedAt ⟨123, by decide⟩
        (alnCheck_rep ⟨123, by decide⟩ hj hq).1))
      (colE2 ⟨20, by decide⟩ 0 hp) Q2.T123_20_2 Q2.hfix123_20_2 Q2.hinj123_20_2
      Q2.hcardT123_20_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T123_20_2 i) (Q2.hfix123_20_2 i) _)
      colCert_123_20_0.hD ?_).symm
  rw [alnId_123 j hj]


theorem leaf_123_20_1 (hp : 1 < (Q2.transData.getD 20 []).length)
    (j : Nat) (hj : j < (repChars.getD 123 []).length)
    (hq : (normIsRep.getD 123 []).getD j false = true) :
    species (Q2.reps (⟨20, by decide⟩ : Fin 148)) (colE2 ⟨20, by decide⟩ 1 hp)
        (rowE2 (⟨123, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨20, by decide⟩ : Fin 148))
        (colE1 ⟨20, by decide⟩ 1 (transLenTr ⟨20, by decide⟩ 1 hp))
        (rowE1 (⟨123, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨123, by decide⟩ : Fin 148) ⟨20, by decide⟩ _
      (validAt ⟨123, by decide⟩ (listedAt ⟨123, by decide⟩ hj))
      (colE1 ⟨20, by decide⟩ 1 (transLenTr ⟨20, by decide⟩ 1 hp)) T123_20
      hfix123_20 hinj123_20 hcardT123_20
      (fun i => conj_mem_of_fixedPoints _ _ (T123_20 i) (hfix123_20 i) _)
      ⟨123, by decide⟩ ⟨20, by decide⟩ _
      (Q2.validAt ⟨123, by decide⟩ (Q2.listedAt ⟨123, by decide⟩
        (alnCheck_rep ⟨123, by decide⟩ hj hq).1))
      (colE2 ⟨20, by decide⟩ 1 hp) Q2.T123_20_2 Q2.hfix123_20_2 Q2.hinj123_20_2
      Q2.hcardT123_20_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T123_20_2 i) (Q2.hfix123_20_2 i) _)
      colCert_123_20_1.hD ?_).symm
  rw [alnId_123 j hj]


theorem leaf_123_20_2 (hp : 2 < (Q2.transData.getD 20 []).length)
    (j : Nat) (hj : j < (repChars.getD 123 []).length)
    (hq : (normIsRep.getD 123 []).getD j false = true) :
    species (Q2.reps (⟨20, by decide⟩ : Fin 148)) (colE2 ⟨20, by decide⟩ 2 hp)
        (rowE2 (⟨123, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨20, by decide⟩ : Fin 148))
        (colE1 ⟨20, by decide⟩ 2 (transLenTr ⟨20, by decide⟩ 2 hp))
        (rowE1 (⟨123, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨123, by decide⟩ : Fin 148) ⟨20, by decide⟩ _
      (validAt ⟨123, by decide⟩ (listedAt ⟨123, by decide⟩ hj))
      (colE1 ⟨20, by decide⟩ 2 (transLenTr ⟨20, by decide⟩ 2 hp)) T123_20
      hfix123_20 hinj123_20 hcardT123_20
      (fun i => conj_mem_of_fixedPoints _ _ (T123_20 i) (hfix123_20 i) _)
      ⟨123, by decide⟩ ⟨20, by decide⟩ _
      (Q2.validAt ⟨123, by decide⟩ (Q2.listedAt ⟨123, by decide⟩
        (alnCheck_rep ⟨123, by decide⟩ hj hq).1))
      (colE2 ⟨20, by decide⟩ 2 hp) Q2.T123_20_2 Q2.hfix123_20_2 Q2.hinj123_20_2
      Q2.hcardT123_20_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T123_20_2 i) (Q2.hfix123_20_2 i) _)
      colCert_123_20_2.hD ?_).symm
  rw [alnId_123 j hj]


theorem leaf_123_20_3 (hp : 3 < (Q2.transData.getD 20 []).length)
    (j : Nat) (hj : j < (repChars.getD 123 []).length)
    (hq : (normIsRep.getD 123 []).getD j false = true) :
    species (Q2.reps (⟨20, by decide⟩ : Fin 148)) (colE2 ⟨20, by decide⟩ 3 hp)
        (rowE2 (⟨123, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨20, by decide⟩ : Fin 148))
        (colE1 ⟨20, by decide⟩ 3 (transLenTr ⟨20, by decide⟩ 3 hp))
        (rowE1 (⟨123, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨123, by decide⟩ : Fin 148) ⟨20, by decide⟩ _
      (validAt ⟨123, by decide⟩ (listedAt ⟨123, by decide⟩ hj))
      (colE1 ⟨20, by decide⟩ 3 (transLenTr ⟨20, by decide⟩ 3 hp)) T123_20
      hfix123_20 hinj123_20 hcardT123_20
      (fun i => conj_mem_of_fixedPoints _ _ (T123_20 i) (hfix123_20 i) _)
      ⟨123, by decide⟩ ⟨20, by decide⟩ _
      (Q2.validAt ⟨123, by decide⟩ (Q2.listedAt ⟨123, by decide⟩
        (alnCheck_rep ⟨123, by decide⟩ hj hq).1))
      (colE2 ⟨20, by decide⟩ 3 hp) Q2.T123_20_2 Q2.hfix123_20_2 Q2.hinj123_20_2
      Q2.hcardT123_20_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T123_20_2 i) (Q2.hfix123_20_2 i) _)
      colCert_123_20_3.hD ?_).symm
  rw [alnId_123 j hj]


theorem leaf_123_20_4 (hp : 4 < (Q2.transData.getD 20 []).length)
    (j : Nat) (hj : j < (repChars.getD 123 []).length)
    (hq : (normIsRep.getD 123 []).getD j false = true) :
    species (Q2.reps (⟨20, by decide⟩ : Fin 148)) (colE2 ⟨20, by decide⟩ 4 hp)
        (rowE2 (⟨123, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨20, by decide⟩ : Fin 148))
        (colE1 ⟨20, by decide⟩ 4 (transLenTr ⟨20, by decide⟩ 4 hp))
        (rowE1 (⟨123, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨123, by decide⟩ : Fin 148) ⟨20, by decide⟩ _
      (validAt ⟨123, by decide⟩ (listedAt ⟨123, by decide⟩ hj))
      (colE1 ⟨20, by decide⟩ 4 (transLenTr ⟨20, by decide⟩ 4 hp)) T123_20
      hfix123_20 hinj123_20 hcardT123_20
      (fun i => conj_mem_of_fixedPoints _ _ (T123_20 i) (hfix123_20 i) _)
      ⟨123, by decide⟩ ⟨20, by decide⟩ _
      (Q2.validAt ⟨123, by decide⟩ (Q2.listedAt ⟨123, by decide⟩
        (alnCheck_rep ⟨123, by decide⟩ hj hq).1))
      (colE2 ⟨20, by decide⟩ 4 hp) Q2.T123_20_2 Q2.hfix123_20_2 Q2.hinj123_20_2
      Q2.hcardT123_20_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T123_20_2 i) (Q2.hfix123_20_2 i) _)
      colCert_123_20_4.hD ?_).symm
  rw [alnId_123 j hj]


theorem leaf_123_20_5 (hp : 5 < (Q2.transData.getD 20 []).length)
    (j : Nat) (hj : j < (repChars.getD 123 []).length)
    (hq : (normIsRep.getD 123 []).getD j false = true) :
    species (Q2.reps (⟨20, by decide⟩ : Fin 148)) (colE2 ⟨20, by decide⟩ 5 hp)
        (rowE2 (⟨123, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨20, by decide⟩ : Fin 148))
        (colE1 ⟨20, by decide⟩ 5 (transLenTr ⟨20, by decide⟩ 5 hp))
        (rowE1 (⟨123, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨123, by decide⟩ : Fin 148) ⟨20, by decide⟩ _
      (validAt ⟨123, by decide⟩ (listedAt ⟨123, by decide⟩ hj))
      (colE1 ⟨20, by decide⟩ 5 (transLenTr ⟨20, by decide⟩ 5 hp)) T123_20
      hfix123_20 hinj123_20 hcardT123_20
      (fun i => conj_mem_of_fixedPoints _ _ (T123_20 i) (hfix123_20 i) _)
      ⟨123, by decide⟩ ⟨20, by decide⟩ _
      (Q2.validAt ⟨123, by decide⟩ (Q2.listedAt ⟨123, by decide⟩
        (alnCheck_rep ⟨123, by decide⟩ hj hq).1))
      (colE2 ⟨20, by decide⟩ 5 hp) Q2.T123_20_2 Q2.hfix123_20_2 Q2.hinj123_20_2
      Q2.hcardT123_20_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T123_20_2 i) (Q2.hfix123_20_2 i) _)
      ?_).symm
  rw [show colData1 (⟨123, by decide⟩ : Fin 148)
        ((colE1 ⟨20, by decide⟩ 5 (transLenTr ⟨20, by decide⟩ 5 hp) : ↥(reps ⟨20, by decide⟩)) : Coordinate 1)
        T123_20 = colFn colCertDiv_123_20_5.D1 (m := 5) from colCertDiv_123_20_5.bind1,
    show colData2 (⟨123, by decide⟩ : Fin 148)
        ((colE2 ⟨20, by decide⟩ 5 hp : ↥(Q2.reps ⟨20, by decide⟩)) : Coordinate 2)
        Q2.T123_20_2 = colFn colCertDiv_123_20_5.D2 (m := 5) from colCertDiv_123_20_5.bind2]
  rw [alnId_123 j hj]
  exact fastcode_of_div ⟨123, by decide⟩ _ _ _
    ((alnId_123 j hj) ▸ Q2.listedAt (⟨123, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨123, by decide⟩ : Fin 148) hj hq).1) colCertDiv_123_20_5_match


theorem leaf_123_20_10 (hp : 10 < (Q2.transData.getD 20 []).length)
    (j : Nat) (hj : j < (repChars.getD 123 []).length)
    (hq : (normIsRep.getD 123 []).getD j false = true) :
    species (Q2.reps (⟨20, by decide⟩ : Fin 148)) (colE2 ⟨20, by decide⟩ 10 hp)
        (rowE2 (⟨123, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨20, by decide⟩ : Fin 148))
        (colE1 ⟨20, by decide⟩ 10 (transLenTr ⟨20, by decide⟩ 10 hp))
        (rowE1 (⟨123, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨123, by decide⟩ : Fin 148) ⟨20, by decide⟩ _
      (validAt ⟨123, by decide⟩ (listedAt ⟨123, by decide⟩ hj))
      (colE1 ⟨20, by decide⟩ 10 (transLenTr ⟨20, by decide⟩ 10 hp)) T123_20
      hfix123_20 hinj123_20 hcardT123_20
      (fun i => conj_mem_of_fixedPoints _ _ (T123_20 i) (hfix123_20 i) _)
      ⟨123, by decide⟩ ⟨20, by decide⟩ _
      (Q2.validAt ⟨123, by decide⟩ (Q2.listedAt ⟨123, by decide⟩
        (alnCheck_rep ⟨123, by decide⟩ hj hq).1))
      (colE2 ⟨20, by decide⟩ 10 hp) Q2.T123_20_2 Q2.hfix123_20_2 Q2.hinj123_20_2
      Q2.hcardT123_20_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T123_20_2 i) (Q2.hfix123_20_2 i) _)
      ?_).symm
  rw [show colData1 (⟨123, by decide⟩ : Fin 148)
        ((colE1 ⟨20, by decide⟩ 10 (transLenTr ⟨20, by decide⟩ 10 hp) : ↥(reps ⟨20, by decide⟩)) : Coordinate 1)
        T123_20 = colFn colCertDiv_123_20_10.D1 (m := 5) from colCertDiv_123_20_10.bind1,
    show colData2 (⟨123, by decide⟩ : Fin 148)
        ((colE2 ⟨20, by decide⟩ 10 hp : ↥(Q2.reps ⟨20, by decide⟩)) : Coordinate 2)
        Q2.T123_20_2 = colFn colCertDiv_123_20_10.D2 (m := 5) from colCertDiv_123_20_10.bind2]
  rw [alnId_123 j hj]
  exact fastcode_of_div ⟨123, by decide⟩ _ _ _
    ((alnId_123 j hj) ▸ Q2.listedAt (⟨123, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨123, by decide⟩ : Fin 148) hj hq).1) colCertDiv_123_20_10_match


theorem leaf_123_20_15 (hp : 15 < (Q2.transData.getD 20 []).length)
    (j : Nat) (hj : j < (repChars.getD 123 []).length)
    (hq : (normIsRep.getD 123 []).getD j false = true) :
    species (Q2.reps (⟨20, by decide⟩ : Fin 148)) (colE2 ⟨20, by decide⟩ 15 hp)
        (rowE2 (⟨123, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨20, by decide⟩ : Fin 148))
        (colE1 ⟨20, by decide⟩ 15 (transLenTr ⟨20, by decide⟩ 15 hp))
        (rowE1 (⟨123, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨123, by decide⟩ : Fin 148) ⟨20, by decide⟩ _
      (validAt ⟨123, by decide⟩ (listedAt ⟨123, by decide⟩ hj))
      (colE1 ⟨20, by decide⟩ 15 (transLenTr ⟨20, by decide⟩ 15 hp)) T123_20
      hfix123_20 hinj123_20 hcardT123_20
      (fun i => conj_mem_of_fixedPoints _ _ (T123_20 i) (hfix123_20 i) _)
      ⟨123, by decide⟩ ⟨20, by decide⟩ _
      (Q2.validAt ⟨123, by decide⟩ (Q2.listedAt ⟨123, by decide⟩
        (alnCheck_rep ⟨123, by decide⟩ hj hq).1))
      (colE2 ⟨20, by decide⟩ 15 hp) Q2.T123_20_2 Q2.hfix123_20_2 Q2.hinj123_20_2
      Q2.hcardT123_20_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T123_20_2 i) (Q2.hfix123_20_2 i) _)
      ?_).symm
  rw [show colData1 (⟨123, by decide⟩ : Fin 148)
        ((colE1 ⟨20, by decide⟩ 15 (transLenTr ⟨20, by decide⟩ 15 hp) : ↥(reps ⟨20, by decide⟩)) : Coordinate 1)
        T123_20 = colFn colCertDiv_123_20_15.D1 (m := 5) from colCertDiv_123_20_15.bind1,
    show colData2 (⟨123, by decide⟩ : Fin 148)
        ((colE2 ⟨20, by decide⟩ 15 hp : ↥(Q2.reps ⟨20, by decide⟩)) : Coordinate 2)
        Q2.T123_20_2 = colFn colCertDiv_123_20_15.D2 (m := 5) from colCertDiv_123_20_15.bind2]
  rw [alnId_123 j hj]
  exact fastcode_of_div ⟨123, by decide⟩ _ _ _
    ((alnId_123 j hj) ▸ Q2.listedAt (⟨123, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨123, by decide⟩ : Fin 148) hj hq).1) colCertDiv_123_20_15_match


theorem leaf_123_20_20 (hp : 20 < (Q2.transData.getD 20 []).length)
    (j : Nat) (hj : j < (repChars.getD 123 []).length)
    (hq : (normIsRep.getD 123 []).getD j false = true) :
    species (Q2.reps (⟨20, by decide⟩ : Fin 148)) (colE2 ⟨20, by decide⟩ 20 hp)
        (rowE2 (⟨123, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨20, by decide⟩ : Fin 148))
        (colE1 ⟨20, by decide⟩ 20 (transLenTr ⟨20, by decide⟩ 20 hp))
        (rowE1 (⟨123, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨123, by decide⟩ : Fin 148) ⟨20, by decide⟩ _
      (validAt ⟨123, by decide⟩ (listedAt ⟨123, by decide⟩ hj))
      (colE1 ⟨20, by decide⟩ 20 (transLenTr ⟨20, by decide⟩ 20 hp)) T123_20
      hfix123_20 hinj123_20 hcardT123_20
      (fun i => conj_mem_of_fixedPoints _ _ (T123_20 i) (hfix123_20 i) _)
      ⟨123, by decide⟩ ⟨20, by decide⟩ _
      (Q2.validAt ⟨123, by decide⟩ (Q2.listedAt ⟨123, by decide⟩
        (alnCheck_rep ⟨123, by decide⟩ hj hq).1))
      (colE2 ⟨20, by decide⟩ 20 hp) Q2.T123_20_2 Q2.hfix123_20_2 Q2.hinj123_20_2
      Q2.hcardT123_20_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T123_20_2 i) (Q2.hfix123_20_2 i) _)
      ?_).symm
  rw [show colData1 (⟨123, by decide⟩ : Fin 148)
        ((colE1 ⟨20, by decide⟩ 20 (transLenTr ⟨20, by decide⟩ 20 hp) : ↥(reps ⟨20, by decide⟩)) : Coordinate 1)
        T123_20 = colFn colCertDiv_123_20_20.D1 (m := 5) from colCertDiv_123_20_20.bind1,
    show colData2 (⟨123, by decide⟩ : Fin 148)
        ((colE2 ⟨20, by decide⟩ 20 hp : ↥(Q2.reps ⟨20, by decide⟩)) : Coordinate 2)
        Q2.T123_20_2 = colFn colCertDiv_123_20_20.D2 (m := 5) from colCertDiv_123_20_20.bind2]
  rw [alnId_123 j hj]
  exact fastcode_of_div ⟨123, by decide⟩ _ _ _
    ((alnId_123 j hj) ▸ Q2.listedAt (⟨123, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨123, by decide⟩ : Fin 148) hj hq).1) colCertDiv_123_20_20_match


theorem leaf_123_29_0 (hp : 0 < (Q2.transData.getD 29 []).length)
    (j : Nat) (hj : j < (repChars.getD 123 []).length)
    (hq : (normIsRep.getD 123 []).getD j false = true) :
    species (Q2.reps (⟨29, by decide⟩ : Fin 148)) (colE2 ⟨29, by decide⟩ 0 hp)
        (rowE2 (⟨123, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨29, by decide⟩ : Fin 148))
        (colE1 ⟨29, by decide⟩ 0 (transLenTr ⟨29, by decide⟩ 0 hp))
        (rowE1 (⟨123, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨123, by decide⟩ : Fin 148) ⟨29, by decide⟩ _
      (validAt ⟨123, by decide⟩ (listedAt ⟨123, by decide⟩ hj))
      (colE1 ⟨29, by decide⟩ 0 (transLenTr ⟨29, by decide⟩ 0 hp)) T123_29
      hfix123_29 hinj123_29 hcardT123_29
      (fun i => conj_mem_of_fixedPoints _ _ (T123_29 i) (hfix123_29 i) _)
      ⟨123, by decide⟩ ⟨29, by decide⟩ _
      (Q2.validAt ⟨123, by decide⟩ (Q2.listedAt ⟨123, by decide⟩
        (alnCheck_rep ⟨123, by decide⟩ hj hq).1))
      (colE2 ⟨29, by decide⟩ 0 hp) Q2.T123_29_2 Q2.hfix123_29_2 Q2.hinj123_29_2
      Q2.hcardT123_29_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T123_29_2 i) (Q2.hfix123_29_2 i) _)
      colCert_123_29_0.hD ?_).symm
  rw [alnId_123 j hj]


theorem leaf_123_29_1 (hp : 1 < (Q2.transData.getD 29 []).length)
    (j : Nat) (hj : j < (repChars.getD 123 []).length)
    (hq : (normIsRep.getD 123 []).getD j false = true) :
    species (Q2.reps (⟨29, by decide⟩ : Fin 148)) (colE2 ⟨29, by decide⟩ 1 hp)
        (rowE2 (⟨123, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨29, by decide⟩ : Fin 148))
        (colE1 ⟨29, by decide⟩ 1 (transLenTr ⟨29, by decide⟩ 1 hp))
        (rowE1 (⟨123, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨123, by decide⟩ : Fin 148) ⟨29, by decide⟩ _
      (validAt ⟨123, by decide⟩ (listedAt ⟨123, by decide⟩ hj))
      (colE1 ⟨29, by decide⟩ 1 (transLenTr ⟨29, by decide⟩ 1 hp)) T123_29
      hfix123_29 hinj123_29 hcardT123_29
      (fun i => conj_mem_of_fixedPoints _ _ (T123_29 i) (hfix123_29 i) _)
      ⟨123, by decide⟩ ⟨29, by decide⟩ _
      (Q2.validAt ⟨123, by decide⟩ (Q2.listedAt ⟨123, by decide⟩
        (alnCheck_rep ⟨123, by decide⟩ hj hq).1))
      (colE2 ⟨29, by decide⟩ 1 hp) Q2.T123_29_2 Q2.hfix123_29_2 Q2.hinj123_29_2
      Q2.hcardT123_29_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T123_29_2 i) (Q2.hfix123_29_2 i) _)
      colCert_123_29_1.hD ?_).symm
  rw [alnId_123 j hj]


theorem leaf_123_29_2 (hp : 2 < (Q2.transData.getD 29 []).length)
    (j : Nat) (hj : j < (repChars.getD 123 []).length)
    (hq : (normIsRep.getD 123 []).getD j false = true) :
    species (Q2.reps (⟨29, by decide⟩ : Fin 148)) (colE2 ⟨29, by decide⟩ 2 hp)
        (rowE2 (⟨123, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨29, by decide⟩ : Fin 148))
        (colE1 ⟨29, by decide⟩ 2 (transLenTr ⟨29, by decide⟩ 2 hp))
        (rowE1 (⟨123, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨123, by decide⟩ : Fin 148) ⟨29, by decide⟩ _
      (validAt ⟨123, by decide⟩ (listedAt ⟨123, by decide⟩ hj))
      (colE1 ⟨29, by decide⟩ 2 (transLenTr ⟨29, by decide⟩ 2 hp)) T123_29
      hfix123_29 hinj123_29 hcardT123_29
      (fun i => conj_mem_of_fixedPoints _ _ (T123_29 i) (hfix123_29 i) _)
      ⟨123, by decide⟩ ⟨29, by decide⟩ _
      (Q2.validAt ⟨123, by decide⟩ (Q2.listedAt ⟨123, by decide⟩
        (alnCheck_rep ⟨123, by decide⟩ hj hq).1))
      (colE2 ⟨29, by decide⟩ 2 hp) Q2.T123_29_2 Q2.hfix123_29_2 Q2.hinj123_29_2
      Q2.hcardT123_29_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T123_29_2 i) (Q2.hfix123_29_2 i) _)
      colCert_123_29_2.hD ?_).symm
  rw [alnId_123 j hj]


theorem leaf_123_29_3 (hp : 3 < (Q2.transData.getD 29 []).length)
    (j : Nat) (hj : j < (repChars.getD 123 []).length)
    (hq : (normIsRep.getD 123 []).getD j false = true) :
    species (Q2.reps (⟨29, by decide⟩ : Fin 148)) (colE2 ⟨29, by decide⟩ 3 hp)
        (rowE2 (⟨123, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨29, by decide⟩ : Fin 148))
        (colE1 ⟨29, by decide⟩ 3 (transLenTr ⟨29, by decide⟩ 3 hp))
        (rowE1 (⟨123, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨123, by decide⟩ : Fin 148) ⟨29, by decide⟩ _
      (validAt ⟨123, by decide⟩ (listedAt ⟨123, by decide⟩ hj))
      (colE1 ⟨29, by decide⟩ 3 (transLenTr ⟨29, by decide⟩ 3 hp)) T123_29
      hfix123_29 hinj123_29 hcardT123_29
      (fun i => conj_mem_of_fixedPoints _ _ (T123_29 i) (hfix123_29 i) _)
      ⟨123, by decide⟩ ⟨29, by decide⟩ _
      (Q2.validAt ⟨123, by decide⟩ (Q2.listedAt ⟨123, by decide⟩
        (alnCheck_rep ⟨123, by decide⟩ hj hq).1))
      (colE2 ⟨29, by decide⟩ 3 hp) Q2.T123_29_2 Q2.hfix123_29_2 Q2.hinj123_29_2
      Q2.hcardT123_29_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T123_29_2 i) (Q2.hfix123_29_2 i) _)
      colCert_123_29_3.hD ?_).symm
  rw [alnId_123 j hj]


theorem leaf_123_29_4 (hp : 4 < (Q2.transData.getD 29 []).length)
    (j : Nat) (hj : j < (repChars.getD 123 []).length)
    (hq : (normIsRep.getD 123 []).getD j false = true) :
    species (Q2.reps (⟨29, by decide⟩ : Fin 148)) (colE2 ⟨29, by decide⟩ 4 hp)
        (rowE2 (⟨123, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨29, by decide⟩ : Fin 148))
        (colE1 ⟨29, by decide⟩ 4 (transLenTr ⟨29, by decide⟩ 4 hp))
        (rowE1 (⟨123, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨123, by decide⟩ : Fin 148) ⟨29, by decide⟩ _
      (validAt ⟨123, by decide⟩ (listedAt ⟨123, by decide⟩ hj))
      (colE1 ⟨29, by decide⟩ 4 (transLenTr ⟨29, by decide⟩ 4 hp)) T123_29
      hfix123_29 hinj123_29 hcardT123_29
      (fun i => conj_mem_of_fixedPoints _ _ (T123_29 i) (hfix123_29 i) _)
      ⟨123, by decide⟩ ⟨29, by decide⟩ _
      (Q2.validAt ⟨123, by decide⟩ (Q2.listedAt ⟨123, by decide⟩
        (alnCheck_rep ⟨123, by decide⟩ hj hq).1))
      (colE2 ⟨29, by decide⟩ 4 hp) Q2.T123_29_2 Q2.hfix123_29_2 Q2.hinj123_29_2
      Q2.hcardT123_29_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T123_29_2 i) (Q2.hfix123_29_2 i) _)
      colCert_123_29_4.hD ?_).symm
  rw [alnId_123 j hj]


theorem leaf_123_29_5 (hp : 5 < (Q2.transData.getD 29 []).length)
    (j : Nat) (hj : j < (repChars.getD 123 []).length)
    (hq : (normIsRep.getD 123 []).getD j false = true) :
    species (Q2.reps (⟨29, by decide⟩ : Fin 148)) (colE2 ⟨29, by decide⟩ 5 hp)
        (rowE2 (⟨123, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨29, by decide⟩ : Fin 148))
        (colE1 ⟨29, by decide⟩ 5 (transLenTr ⟨29, by decide⟩ 5 hp))
        (rowE1 (⟨123, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨123, by decide⟩ : Fin 148) ⟨29, by decide⟩ _
      (validAt ⟨123, by decide⟩ (listedAt ⟨123, by decide⟩ hj))
      (colE1 ⟨29, by decide⟩ 5 (transLenTr ⟨29, by decide⟩ 5 hp)) T123_29
      hfix123_29 hinj123_29 hcardT123_29
      (fun i => conj_mem_of_fixedPoints _ _ (T123_29 i) (hfix123_29 i) _)
      ⟨123, by decide⟩ ⟨29, by decide⟩ _
      (Q2.validAt ⟨123, by decide⟩ (Q2.listedAt ⟨123, by decide⟩
        (alnCheck_rep ⟨123, by decide⟩ hj hq).1))
      (colE2 ⟨29, by decide⟩ 5 hp) Q2.T123_29_2 Q2.hfix123_29_2 Q2.hinj123_29_2
      Q2.hcardT123_29_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T123_29_2 i) (Q2.hfix123_29_2 i) _)
      ?_).symm
  rw [show colData1 (⟨123, by decide⟩ : Fin 148)
        ((colE1 ⟨29, by decide⟩ 5 (transLenTr ⟨29, by decide⟩ 5 hp) : ↥(reps ⟨29, by decide⟩)) : Coordinate 1)
        T123_29 = colFn colCertDiv_123_29_5.D1 (m := 5) from colCertDiv_123_29_5.bind1,
    show colData2 (⟨123, by decide⟩ : Fin 148)
        ((colE2 ⟨29, by decide⟩ 5 hp : ↥(Q2.reps ⟨29, by decide⟩)) : Coordinate 2)
        Q2.T123_29_2 = colFn colCertDiv_123_29_5.D2 (m := 5) from colCertDiv_123_29_5.bind2]
  rw [alnId_123 j hj]
  exact fastcode_of_div ⟨123, by decide⟩ _ _ _
    ((alnId_123 j hj) ▸ Q2.listedAt (⟨123, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨123, by decide⟩ : Fin 148) hj hq).1) colCertDiv_123_29_5_match


theorem leaf_123_29_10 (hp : 10 < (Q2.transData.getD 29 []).length)
    (j : Nat) (hj : j < (repChars.getD 123 []).length)
    (hq : (normIsRep.getD 123 []).getD j false = true) :
    species (Q2.reps (⟨29, by decide⟩ : Fin 148)) (colE2 ⟨29, by decide⟩ 10 hp)
        (rowE2 (⟨123, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨29, by decide⟩ : Fin 148))
        (colE1 ⟨29, by decide⟩ 10 (transLenTr ⟨29, by decide⟩ 10 hp))
        (rowE1 (⟨123, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨123, by decide⟩ : Fin 148) ⟨29, by decide⟩ _
      (validAt ⟨123, by decide⟩ (listedAt ⟨123, by decide⟩ hj))
      (colE1 ⟨29, by decide⟩ 10 (transLenTr ⟨29, by decide⟩ 10 hp)) T123_29
      hfix123_29 hinj123_29 hcardT123_29
      (fun i => conj_mem_of_fixedPoints _ _ (T123_29 i) (hfix123_29 i) _)
      ⟨123, by decide⟩ ⟨29, by decide⟩ _
      (Q2.validAt ⟨123, by decide⟩ (Q2.listedAt ⟨123, by decide⟩
        (alnCheck_rep ⟨123, by decide⟩ hj hq).1))
      (colE2 ⟨29, by decide⟩ 10 hp) Q2.T123_29_2 Q2.hfix123_29_2 Q2.hinj123_29_2
      Q2.hcardT123_29_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T123_29_2 i) (Q2.hfix123_29_2 i) _)
      ?_).symm
  rw [show colData1 (⟨123, by decide⟩ : Fin 148)
        ((colE1 ⟨29, by decide⟩ 10 (transLenTr ⟨29, by decide⟩ 10 hp) : ↥(reps ⟨29, by decide⟩)) : Coordinate 1)
        T123_29 = colFn colCertDiv_123_29_10.D1 (m := 5) from colCertDiv_123_29_10.bind1,
    show colData2 (⟨123, by decide⟩ : Fin 148)
        ((colE2 ⟨29, by decide⟩ 10 hp : ↥(Q2.reps ⟨29, by decide⟩)) : Coordinate 2)
        Q2.T123_29_2 = colFn colCertDiv_123_29_10.D2 (m := 5) from colCertDiv_123_29_10.bind2]
  rw [alnId_123 j hj]
  exact fastcode_of_div ⟨123, by decide⟩ _ _ _
    ((alnId_123 j hj) ▸ Q2.listedAt (⟨123, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨123, by decide⟩ : Fin 148) hj hq).1) colCertDiv_123_29_10_match


theorem leaf_123_29_15 (hp : 15 < (Q2.transData.getD 29 []).length)
    (j : Nat) (hj : j < (repChars.getD 123 []).length)
    (hq : (normIsRep.getD 123 []).getD j false = true) :
    species (Q2.reps (⟨29, by decide⟩ : Fin 148)) (colE2 ⟨29, by decide⟩ 15 hp)
        (rowE2 (⟨123, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨29, by decide⟩ : Fin 148))
        (colE1 ⟨29, by decide⟩ 15 (transLenTr ⟨29, by decide⟩ 15 hp))
        (rowE1 (⟨123, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨123, by decide⟩ : Fin 148) ⟨29, by decide⟩ _
      (validAt ⟨123, by decide⟩ (listedAt ⟨123, by decide⟩ hj))
      (colE1 ⟨29, by decide⟩ 15 (transLenTr ⟨29, by decide⟩ 15 hp)) T123_29
      hfix123_29 hinj123_29 hcardT123_29
      (fun i => conj_mem_of_fixedPoints _ _ (T123_29 i) (hfix123_29 i) _)
      ⟨123, by decide⟩ ⟨29, by decide⟩ _
      (Q2.validAt ⟨123, by decide⟩ (Q2.listedAt ⟨123, by decide⟩
        (alnCheck_rep ⟨123, by decide⟩ hj hq).1))
      (colE2 ⟨29, by decide⟩ 15 hp) Q2.T123_29_2 Q2.hfix123_29_2 Q2.hinj123_29_2
      Q2.hcardT123_29_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T123_29_2 i) (Q2.hfix123_29_2 i) _)
      ?_).symm
  rw [show colData1 (⟨123, by decide⟩ : Fin 148)
        ((colE1 ⟨29, by decide⟩ 15 (transLenTr ⟨29, by decide⟩ 15 hp) : ↥(reps ⟨29, by decide⟩)) : Coordinate 1)
        T123_29 = colFn colCertDiv_123_29_15.D1 (m := 5) from colCertDiv_123_29_15.bind1,
    show colData2 (⟨123, by decide⟩ : Fin 148)
        ((colE2 ⟨29, by decide⟩ 15 hp : ↥(Q2.reps ⟨29, by decide⟩)) : Coordinate 2)
        Q2.T123_29_2 = colFn colCertDiv_123_29_15.D2 (m := 5) from colCertDiv_123_29_15.bind2]
  rw [alnId_123 j hj]
  exact fastcode_of_div ⟨123, by decide⟩ _ _ _
    ((alnId_123 j hj) ▸ Q2.listedAt (⟨123, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨123, by decide⟩ : Fin 148) hj hq).1) colCertDiv_123_29_15_match


theorem leaf_123_29_20 (hp : 20 < (Q2.transData.getD 29 []).length)
    (j : Nat) (hj : j < (repChars.getD 123 []).length)
    (hq : (normIsRep.getD 123 []).getD j false = true) :
    species (Q2.reps (⟨29, by decide⟩ : Fin 148)) (colE2 ⟨29, by decide⟩ 20 hp)
        (rowE2 (⟨123, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨29, by decide⟩ : Fin 148))
        (colE1 ⟨29, by decide⟩ 20 (transLenTr ⟨29, by decide⟩ 20 hp))
        (rowE1 (⟨123, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨123, by decide⟩ : Fin 148) ⟨29, by decide⟩ _
      (validAt ⟨123, by decide⟩ (listedAt ⟨123, by decide⟩ hj))
      (colE1 ⟨29, by decide⟩ 20 (transLenTr ⟨29, by decide⟩ 20 hp)) T123_29
      hfix123_29 hinj123_29 hcardT123_29
      (fun i => conj_mem_of_fixedPoints _ _ (T123_29 i) (hfix123_29 i) _)
      ⟨123, by decide⟩ ⟨29, by decide⟩ _
      (Q2.validAt ⟨123, by decide⟩ (Q2.listedAt ⟨123, by decide⟩
        (alnCheck_rep ⟨123, by decide⟩ hj hq).1))
      (colE2 ⟨29, by decide⟩ 20 hp) Q2.T123_29_2 Q2.hfix123_29_2 Q2.hinj123_29_2
      Q2.hcardT123_29_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T123_29_2 i) (Q2.hfix123_29_2 i) _)
      colCert_123_29_20.hD ?_).symm
  rw [alnId_123 j hj]


theorem leaf_123_37_0 (hp : 0 < (Q2.transData.getD 37 []).length)
    (j : Nat) (hj : j < (repChars.getD 123 []).length)
    (hq : (normIsRep.getD 123 []).getD j false = true) :
    species (Q2.reps (⟨37, by decide⟩ : Fin 148)) (colE2 ⟨37, by decide⟩ 0 hp)
        (rowE2 (⟨123, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨37, by decide⟩ : Fin 148))
        (colE1 ⟨37, by decide⟩ 0 (transLenTr ⟨37, by decide⟩ 0 hp))
        (rowE1 (⟨123, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨123, by decide⟩ : Fin 148) ⟨37, by decide⟩ _
      (validAt ⟨123, by decide⟩ (listedAt ⟨123, by decide⟩ hj))
      (colE1 ⟨37, by decide⟩ 0 (transLenTr ⟨37, by decide⟩ 0 hp)) T123_37
      hfix123_37 hinj123_37 hcardT123_37
      (fun i => conj_mem_of_fixedPoints _ _ (T123_37 i) (hfix123_37 i) _)
      ⟨123, by decide⟩ ⟨37, by decide⟩ _
      (Q2.validAt ⟨123, by decide⟩ (Q2.listedAt ⟨123, by decide⟩
        (alnCheck_rep ⟨123, by decide⟩ hj hq).1))
      (colE2 ⟨37, by decide⟩ 0 hp) Q2.T123_37_2 Q2.hfix123_37_2 Q2.hinj123_37_2
      Q2.hcardT123_37_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T123_37_2 i) (Q2.hfix123_37_2 i) _)
      colCert_123_37_0.hD ?_).symm
  rw [alnId_123 j hj]


theorem leaf_123_37_1 (hp : 1 < (Q2.transData.getD 37 []).length)
    (j : Nat) (hj : j < (repChars.getD 123 []).length)
    (hq : (normIsRep.getD 123 []).getD j false = true) :
    species (Q2.reps (⟨37, by decide⟩ : Fin 148)) (colE2 ⟨37, by decide⟩ 1 hp)
        (rowE2 (⟨123, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨37, by decide⟩ : Fin 148))
        (colE1 ⟨37, by decide⟩ 1 (transLenTr ⟨37, by decide⟩ 1 hp))
        (rowE1 (⟨123, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨123, by decide⟩ : Fin 148) ⟨37, by decide⟩ _
      (validAt ⟨123, by decide⟩ (listedAt ⟨123, by decide⟩ hj))
      (colE1 ⟨37, by decide⟩ 1 (transLenTr ⟨37, by decide⟩ 1 hp)) T123_37
      hfix123_37 hinj123_37 hcardT123_37
      (fun i => conj_mem_of_fixedPoints _ _ (T123_37 i) (hfix123_37 i) _)
      ⟨123, by decide⟩ ⟨37, by decide⟩ _
      (Q2.validAt ⟨123, by decide⟩ (Q2.listedAt ⟨123, by decide⟩
        (alnCheck_rep ⟨123, by decide⟩ hj hq).1))
      (colE2 ⟨37, by decide⟩ 1 hp) Q2.T123_37_2 Q2.hfix123_37_2 Q2.hinj123_37_2
      Q2.hcardT123_37_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T123_37_2 i) (Q2.hfix123_37_2 i) _)
      colCert_123_37_1.hD ?_).symm
  rw [alnId_123 j hj]


theorem leaf_123_37_2 (hp : 2 < (Q2.transData.getD 37 []).length)
    (j : Nat) (hj : j < (repChars.getD 123 []).length)
    (hq : (normIsRep.getD 123 []).getD j false = true) :
    species (Q2.reps (⟨37, by decide⟩ : Fin 148)) (colE2 ⟨37, by decide⟩ 2 hp)
        (rowE2 (⟨123, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨37, by decide⟩ : Fin 148))
        (colE1 ⟨37, by decide⟩ 2 (transLenTr ⟨37, by decide⟩ 2 hp))
        (rowE1 (⟨123, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨123, by decide⟩ : Fin 148) ⟨37, by decide⟩ _
      (validAt ⟨123, by decide⟩ (listedAt ⟨123, by decide⟩ hj))
      (colE1 ⟨37, by decide⟩ 2 (transLenTr ⟨37, by decide⟩ 2 hp)) T123_37
      hfix123_37 hinj123_37 hcardT123_37
      (fun i => conj_mem_of_fixedPoints _ _ (T123_37 i) (hfix123_37 i) _)
      ⟨123, by decide⟩ ⟨37, by decide⟩ _
      (Q2.validAt ⟨123, by decide⟩ (Q2.listedAt ⟨123, by decide⟩
        (alnCheck_rep ⟨123, by decide⟩ hj hq).1))
      (colE2 ⟨37, by decide⟩ 2 hp) Q2.T123_37_2 Q2.hfix123_37_2 Q2.hinj123_37_2
      Q2.hcardT123_37_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T123_37_2 i) (Q2.hfix123_37_2 i) _)
      colCert_123_37_2.hD ?_).symm
  rw [alnId_123 j hj]


theorem leaf_123_37_3 (hp : 3 < (Q2.transData.getD 37 []).length)
    (j : Nat) (hj : j < (repChars.getD 123 []).length)
    (hq : (normIsRep.getD 123 []).getD j false = true) :
    species (Q2.reps (⟨37, by decide⟩ : Fin 148)) (colE2 ⟨37, by decide⟩ 3 hp)
        (rowE2 (⟨123, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨37, by decide⟩ : Fin 148))
        (colE1 ⟨37, by decide⟩ 3 (transLenTr ⟨37, by decide⟩ 3 hp))
        (rowE1 (⟨123, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨123, by decide⟩ : Fin 148) ⟨37, by decide⟩ _
      (validAt ⟨123, by decide⟩ (listedAt ⟨123, by decide⟩ hj))
      (colE1 ⟨37, by decide⟩ 3 (transLenTr ⟨37, by decide⟩ 3 hp)) T123_37
      hfix123_37 hinj123_37 hcardT123_37
      (fun i => conj_mem_of_fixedPoints _ _ (T123_37 i) (hfix123_37 i) _)
      ⟨123, by decide⟩ ⟨37, by decide⟩ _
      (Q2.validAt ⟨123, by decide⟩ (Q2.listedAt ⟨123, by decide⟩
        (alnCheck_rep ⟨123, by decide⟩ hj hq).1))
      (colE2 ⟨37, by decide⟩ 3 hp) Q2.T123_37_2 Q2.hfix123_37_2 Q2.hinj123_37_2
      Q2.hcardT123_37_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T123_37_2 i) (Q2.hfix123_37_2 i) _)
      colCert_123_37_3.hD ?_).symm
  rw [alnId_123 j hj]


theorem leaf_123_37_4 (hp : 4 < (Q2.transData.getD 37 []).length)
    (j : Nat) (hj : j < (repChars.getD 123 []).length)
    (hq : (normIsRep.getD 123 []).getD j false = true) :
    species (Q2.reps (⟨37, by decide⟩ : Fin 148)) (colE2 ⟨37, by decide⟩ 4 hp)
        (rowE2 (⟨123, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨37, by decide⟩ : Fin 148))
        (colE1 ⟨37, by decide⟩ 4 (transLenTr ⟨37, by decide⟩ 4 hp))
        (rowE1 (⟨123, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨123, by decide⟩ : Fin 148) ⟨37, by decide⟩ _
      (validAt ⟨123, by decide⟩ (listedAt ⟨123, by decide⟩ hj))
      (colE1 ⟨37, by decide⟩ 4 (transLenTr ⟨37, by decide⟩ 4 hp)) T123_37
      hfix123_37 hinj123_37 hcardT123_37
      (fun i => conj_mem_of_fixedPoints _ _ (T123_37 i) (hfix123_37 i) _)
      ⟨123, by decide⟩ ⟨37, by decide⟩ _
      (Q2.validAt ⟨123, by decide⟩ (Q2.listedAt ⟨123, by decide⟩
        (alnCheck_rep ⟨123, by decide⟩ hj hq).1))
      (colE2 ⟨37, by decide⟩ 4 hp) Q2.T123_37_2 Q2.hfix123_37_2 Q2.hinj123_37_2
      Q2.hcardT123_37_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T123_37_2 i) (Q2.hfix123_37_2 i) _)
      colCert_123_37_4.hD ?_).symm
  rw [alnId_123 j hj]


theorem leaf_123_37_5 (hp : 5 < (Q2.transData.getD 37 []).length)
    (j : Nat) (hj : j < (repChars.getD 123 []).length)
    (hq : (normIsRep.getD 123 []).getD j false = true) :
    species (Q2.reps (⟨37, by decide⟩ : Fin 148)) (colE2 ⟨37, by decide⟩ 5 hp)
        (rowE2 (⟨123, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨37, by decide⟩ : Fin 148))
        (colE1 ⟨37, by decide⟩ 5 (transLenTr ⟨37, by decide⟩ 5 hp))
        (rowE1 (⟨123, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨123, by decide⟩ : Fin 148) ⟨37, by decide⟩ _
      (validAt ⟨123, by decide⟩ (listedAt ⟨123, by decide⟩ hj))
      (colE1 ⟨37, by decide⟩ 5 (transLenTr ⟨37, by decide⟩ 5 hp)) T123_37
      hfix123_37 hinj123_37 hcardT123_37
      (fun i => conj_mem_of_fixedPoints _ _ (T123_37 i) (hfix123_37 i) _)
      ⟨123, by decide⟩ ⟨37, by decide⟩ _
      (Q2.validAt ⟨123, by decide⟩ (Q2.listedAt ⟨123, by decide⟩
        (alnCheck_rep ⟨123, by decide⟩ hj hq).1))
      (colE2 ⟨37, by decide⟩ 5 hp) Q2.T123_37_2 Q2.hfix123_37_2 Q2.hinj123_37_2
      Q2.hcardT123_37_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T123_37_2 i) (Q2.hfix123_37_2 i) _)
      ?_).symm
  rw [show colData1 (⟨123, by decide⟩ : Fin 148)
        ((colE1 ⟨37, by decide⟩ 5 (transLenTr ⟨37, by decide⟩ 5 hp) : ↥(reps ⟨37, by decide⟩)) : Coordinate 1)
        T123_37 = colFn colCertDiv_123_37_5.D1 (m := 5) from colCertDiv_123_37_5.bind1,
    show colData2 (⟨123, by decide⟩ : Fin 148)
        ((colE2 ⟨37, by decide⟩ 5 hp : ↥(Q2.reps ⟨37, by decide⟩)) : Coordinate 2)
        Q2.T123_37_2 = colFn colCertDiv_123_37_5.D2 (m := 5) from colCertDiv_123_37_5.bind2]
  rw [alnId_123 j hj]
  exact fastcode_of_div ⟨123, by decide⟩ _ _ _
    ((alnId_123 j hj) ▸ Q2.listedAt (⟨123, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨123, by decide⟩ : Fin 148) hj hq).1) colCertDiv_123_37_5_match


theorem leaf_123_37_10 (hp : 10 < (Q2.transData.getD 37 []).length)
    (j : Nat) (hj : j < (repChars.getD 123 []).length)
    (hq : (normIsRep.getD 123 []).getD j false = true) :
    species (Q2.reps (⟨37, by decide⟩ : Fin 148)) (colE2 ⟨37, by decide⟩ 10 hp)
        (rowE2 (⟨123, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨37, by decide⟩ : Fin 148))
        (colE1 ⟨37, by decide⟩ 10 (transLenTr ⟨37, by decide⟩ 10 hp))
        (rowE1 (⟨123, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨123, by decide⟩ : Fin 148) ⟨37, by decide⟩ _
      (validAt ⟨123, by decide⟩ (listedAt ⟨123, by decide⟩ hj))
      (colE1 ⟨37, by decide⟩ 10 (transLenTr ⟨37, by decide⟩ 10 hp)) T123_37
      hfix123_37 hinj123_37 hcardT123_37
      (fun i => conj_mem_of_fixedPoints _ _ (T123_37 i) (hfix123_37 i) _)
      ⟨123, by decide⟩ ⟨37, by decide⟩ _
      (Q2.validAt ⟨123, by decide⟩ (Q2.listedAt ⟨123, by decide⟩
        (alnCheck_rep ⟨123, by decide⟩ hj hq).1))
      (colE2 ⟨37, by decide⟩ 10 hp) Q2.T123_37_2 Q2.hfix123_37_2 Q2.hinj123_37_2
      Q2.hcardT123_37_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T123_37_2 i) (Q2.hfix123_37_2 i) _)
      ?_).symm
  rw [show colData1 (⟨123, by decide⟩ : Fin 148)
        ((colE1 ⟨37, by decide⟩ 10 (transLenTr ⟨37, by decide⟩ 10 hp) : ↥(reps ⟨37, by decide⟩)) : Coordinate 1)
        T123_37 = colFn colCertDiv_123_37_10.D1 (m := 5) from colCertDiv_123_37_10.bind1,
    show colData2 (⟨123, by decide⟩ : Fin 148)
        ((colE2 ⟨37, by decide⟩ 10 hp : ↥(Q2.reps ⟨37, by decide⟩)) : Coordinate 2)
        Q2.T123_37_2 = colFn colCertDiv_123_37_10.D2 (m := 5) from colCertDiv_123_37_10.bind2]
  rw [alnId_123 j hj]
  exact fastcode_of_div ⟨123, by decide⟩ _ _ _
    ((alnId_123 j hj) ▸ Q2.listedAt (⟨123, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨123, by decide⟩ : Fin 148) hj hq).1) colCertDiv_123_37_10_match


theorem leaf_123_37_15 (hp : 15 < (Q2.transData.getD 37 []).length)
    (j : Nat) (hj : j < (repChars.getD 123 []).length)
    (hq : (normIsRep.getD 123 []).getD j false = true) :
    species (Q2.reps (⟨37, by decide⟩ : Fin 148)) (colE2 ⟨37, by decide⟩ 15 hp)
        (rowE2 (⟨123, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨37, by decide⟩ : Fin 148))
        (colE1 ⟨37, by decide⟩ 15 (transLenTr ⟨37, by decide⟩ 15 hp))
        (rowE1 (⟨123, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨123, by decide⟩ : Fin 148) ⟨37, by decide⟩ _
      (validAt ⟨123, by decide⟩ (listedAt ⟨123, by decide⟩ hj))
      (colE1 ⟨37, by decide⟩ 15 (transLenTr ⟨37, by decide⟩ 15 hp)) T123_37
      hfix123_37 hinj123_37 hcardT123_37
      (fun i => conj_mem_of_fixedPoints _ _ (T123_37 i) (hfix123_37 i) _)
      ⟨123, by decide⟩ ⟨37, by decide⟩ _
      (Q2.validAt ⟨123, by decide⟩ (Q2.listedAt ⟨123, by decide⟩
        (alnCheck_rep ⟨123, by decide⟩ hj hq).1))
      (colE2 ⟨37, by decide⟩ 15 hp) Q2.T123_37_2 Q2.hfix123_37_2 Q2.hinj123_37_2
      Q2.hcardT123_37_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T123_37_2 i) (Q2.hfix123_37_2 i) _)
      ?_).symm
  rw [show colData1 (⟨123, by decide⟩ : Fin 148)
        ((colE1 ⟨37, by decide⟩ 15 (transLenTr ⟨37, by decide⟩ 15 hp) : ↥(reps ⟨37, by decide⟩)) : Coordinate 1)
        T123_37 = colFn colCertDiv_123_37_15.D1 (m := 5) from colCertDiv_123_37_15.bind1,
    show colData2 (⟨123, by decide⟩ : Fin 148)
        ((colE2 ⟨37, by decide⟩ 15 hp : ↥(Q2.reps ⟨37, by decide⟩)) : Coordinate 2)
        Q2.T123_37_2 = colFn colCertDiv_123_37_15.D2 (m := 5) from colCertDiv_123_37_15.bind2]
  rw [alnId_123 j hj]
  exact fastcode_of_div ⟨123, by decide⟩ _ _ _
    ((alnId_123 j hj) ▸ Q2.listedAt (⟨123, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨123, by decide⟩ : Fin 148) hj hq).1) colCertDiv_123_37_15_match


theorem leaf_123_37_20 (hp : 20 < (Q2.transData.getD 37 []).length)
    (j : Nat) (hj : j < (repChars.getD 123 []).length)
    (hq : (normIsRep.getD 123 []).getD j false = true) :
    species (Q2.reps (⟨37, by decide⟩ : Fin 148)) (colE2 ⟨37, by decide⟩ 20 hp)
        (rowE2 (⟨123, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨37, by decide⟩ : Fin 148))
        (colE1 ⟨37, by decide⟩ 20 (transLenTr ⟨37, by decide⟩ 20 hp))
        (rowE1 (⟨123, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨123, by decide⟩ : Fin 148) ⟨37, by decide⟩ _
      (validAt ⟨123, by decide⟩ (listedAt ⟨123, by decide⟩ hj))
      (colE1 ⟨37, by decide⟩ 20 (transLenTr ⟨37, by decide⟩ 20 hp)) T123_37
      hfix123_37 hinj123_37 hcardT123_37
      (fun i => conj_mem_of_fixedPoints _ _ (T123_37 i) (hfix123_37 i) _)
      ⟨123, by decide⟩ ⟨37, by decide⟩ _
      (Q2.validAt ⟨123, by decide⟩ (Q2.listedAt ⟨123, by decide⟩
        (alnCheck_rep ⟨123, by decide⟩ hj hq).1))
      (colE2 ⟨37, by decide⟩ 20 hp) Q2.T123_37_2 Q2.hfix123_37_2 Q2.hinj123_37_2
      Q2.hcardT123_37_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T123_37_2 i) (Q2.hfix123_37_2 i) _)
      ?_).symm
  rw [show colData1 (⟨123, by decide⟩ : Fin 148)
        ((colE1 ⟨37, by decide⟩ 20 (transLenTr ⟨37, by decide⟩ 20 hp) : ↥(reps ⟨37, by decide⟩)) : Coordinate 1)
        T123_37 = colFn colCertDiv_123_37_20.D1 (m := 5) from colCertDiv_123_37_20.bind1,
    show colData2 (⟨123, by decide⟩ : Fin 148)
        ((colE2 ⟨37, by decide⟩ 20 hp : ↥(Q2.reps ⟨37, by decide⟩)) : Coordinate 2)
        Q2.T123_37_2 = colFn colCertDiv_123_37_20.D2 (m := 5) from colCertDiv_123_37_20.bind2]
  rw [alnId_123 j hj]
  exact fastcode_of_div ⟨123, by decide⟩ _ _ _
    ((alnId_123 j hj) ▸ Q2.listedAt (⟨123, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨123, by decide⟩ : Fin 148) hj hq).1) colCertDiv_123_37_20_match


theorem leaf_123_38_0 (hp : 0 < (Q2.transData.getD 38 []).length)
    (j : Nat) (hj : j < (repChars.getD 123 []).length)
    (hq : (normIsRep.getD 123 []).getD j false = true) :
    species (Q2.reps (⟨38, by decide⟩ : Fin 148)) (colE2 ⟨38, by decide⟩ 0 hp)
        (rowE2 (⟨123, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨38, by decide⟩ : Fin 148))
        (colE1 ⟨38, by decide⟩ 0 (transLenTr ⟨38, by decide⟩ 0 hp))
        (rowE1 (⟨123, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨123, by decide⟩ : Fin 148) ⟨38, by decide⟩ _
      (validAt ⟨123, by decide⟩ (listedAt ⟨123, by decide⟩ hj))
      (colE1 ⟨38, by decide⟩ 0 (transLenTr ⟨38, by decide⟩ 0 hp)) T123_38
      hfix123_38 hinj123_38 hcardT123_38
      (fun i => conj_mem_of_fixedPoints _ _ (T123_38 i) (hfix123_38 i) _)
      ⟨123, by decide⟩ ⟨38, by decide⟩ _
      (Q2.validAt ⟨123, by decide⟩ (Q2.listedAt ⟨123, by decide⟩
        (alnCheck_rep ⟨123, by decide⟩ hj hq).1))
      (colE2 ⟨38, by decide⟩ 0 hp) Q2.T123_38_2 Q2.hfix123_38_2 Q2.hinj123_38_2
      Q2.hcardT123_38_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T123_38_2 i) (Q2.hfix123_38_2 i) _)
      colCert_123_38_0.hD ?_).symm
  rw [alnId_123 j hj]


theorem leaf_123_38_1 (hp : 1 < (Q2.transData.getD 38 []).length)
    (j : Nat) (hj : j < (repChars.getD 123 []).length)
    (hq : (normIsRep.getD 123 []).getD j false = true) :
    species (Q2.reps (⟨38, by decide⟩ : Fin 148)) (colE2 ⟨38, by decide⟩ 1 hp)
        (rowE2 (⟨123, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨38, by decide⟩ : Fin 148))
        (colE1 ⟨38, by decide⟩ 1 (transLenTr ⟨38, by decide⟩ 1 hp))
        (rowE1 (⟨123, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨123, by decide⟩ : Fin 148) ⟨38, by decide⟩ _
      (validAt ⟨123, by decide⟩ (listedAt ⟨123, by decide⟩ hj))
      (colE1 ⟨38, by decide⟩ 1 (transLenTr ⟨38, by decide⟩ 1 hp)) T123_38
      hfix123_38 hinj123_38 hcardT123_38
      (fun i => conj_mem_of_fixedPoints _ _ (T123_38 i) (hfix123_38 i) _)
      ⟨123, by decide⟩ ⟨38, by decide⟩ _
      (Q2.validAt ⟨123, by decide⟩ (Q2.listedAt ⟨123, by decide⟩
        (alnCheck_rep ⟨123, by decide⟩ hj hq).1))
      (colE2 ⟨38, by decide⟩ 1 hp) Q2.T123_38_2 Q2.hfix123_38_2 Q2.hinj123_38_2
      Q2.hcardT123_38_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T123_38_2 i) (Q2.hfix123_38_2 i) _)
      colCert_123_38_1.hD ?_).symm
  rw [alnId_123 j hj]


theorem leaf_123_38_2 (hp : 2 < (Q2.transData.getD 38 []).length)
    (j : Nat) (hj : j < (repChars.getD 123 []).length)
    (hq : (normIsRep.getD 123 []).getD j false = true) :
    species (Q2.reps (⟨38, by decide⟩ : Fin 148)) (colE2 ⟨38, by decide⟩ 2 hp)
        (rowE2 (⟨123, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨38, by decide⟩ : Fin 148))
        (colE1 ⟨38, by decide⟩ 2 (transLenTr ⟨38, by decide⟩ 2 hp))
        (rowE1 (⟨123, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨123, by decide⟩ : Fin 148) ⟨38, by decide⟩ _
      (validAt ⟨123, by decide⟩ (listedAt ⟨123, by decide⟩ hj))
      (colE1 ⟨38, by decide⟩ 2 (transLenTr ⟨38, by decide⟩ 2 hp)) T123_38
      hfix123_38 hinj123_38 hcardT123_38
      (fun i => conj_mem_of_fixedPoints _ _ (T123_38 i) (hfix123_38 i) _)
      ⟨123, by decide⟩ ⟨38, by decide⟩ _
      (Q2.validAt ⟨123, by decide⟩ (Q2.listedAt ⟨123, by decide⟩
        (alnCheck_rep ⟨123, by decide⟩ hj hq).1))
      (colE2 ⟨38, by decide⟩ 2 hp) Q2.T123_38_2 Q2.hfix123_38_2 Q2.hinj123_38_2
      Q2.hcardT123_38_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T123_38_2 i) (Q2.hfix123_38_2 i) _)
      colCert_123_38_2.hD ?_).symm
  rw [alnId_123 j hj]


theorem leaf_123_38_3 (hp : 3 < (Q2.transData.getD 38 []).length)
    (j : Nat) (hj : j < (repChars.getD 123 []).length)
    (hq : (normIsRep.getD 123 []).getD j false = true) :
    species (Q2.reps (⟨38, by decide⟩ : Fin 148)) (colE2 ⟨38, by decide⟩ 3 hp)
        (rowE2 (⟨123, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨38, by decide⟩ : Fin 148))
        (colE1 ⟨38, by decide⟩ 3 (transLenTr ⟨38, by decide⟩ 3 hp))
        (rowE1 (⟨123, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨123, by decide⟩ : Fin 148) ⟨38, by decide⟩ _
      (validAt ⟨123, by decide⟩ (listedAt ⟨123, by decide⟩ hj))
      (colE1 ⟨38, by decide⟩ 3 (transLenTr ⟨38, by decide⟩ 3 hp)) T123_38
      hfix123_38 hinj123_38 hcardT123_38
      (fun i => conj_mem_of_fixedPoints _ _ (T123_38 i) (hfix123_38 i) _)
      ⟨123, by decide⟩ ⟨38, by decide⟩ _
      (Q2.validAt ⟨123, by decide⟩ (Q2.listedAt ⟨123, by decide⟩
        (alnCheck_rep ⟨123, by decide⟩ hj hq).1))
      (colE2 ⟨38, by decide⟩ 3 hp) Q2.T123_38_2 Q2.hfix123_38_2 Q2.hinj123_38_2
      Q2.hcardT123_38_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T123_38_2 i) (Q2.hfix123_38_2 i) _)
      colCert_123_38_3.hD ?_).symm
  rw [alnId_123 j hj]


end LeanDring.P5Presentation
