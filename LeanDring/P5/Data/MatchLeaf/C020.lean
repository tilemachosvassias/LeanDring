/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Data.ColCdd.C001
import LeanDring.P5.Data.ColRestCheap.C011
import LeanDring.P5.Data.ColRestCheap.C012
import LeanDring.P5.Data.ColRestCheap.C013
import LeanDring.P5.Data.ColRestCheap.C009
import LeanDring.P5.Data.ColRestCheap.C010
import LeanDring.P5.Data.EntryK.C023
import LeanDring.P5.Data.EntryK.C024
import LeanDring.P5.Certificate.RingIsomorphism.MatchCore
import LeanDring.P5.Data.SpeciesAlign.C024
import LeanDring.P5.Data.SpeciesAlign.C025
import LeanDring.P5.Data.SpeciesDiv.C001
import LeanDring.P5.Data.SpeciesDiv.C002
import LeanDring.P5.Data.SpeciesDiv.C003
import LeanDring.P5.Data.SpeciesDiv.C004

/-! # Stage-5 leaves, chunk 19 (auto-emitted).  -/

namespace LeanDring.P5Presentation

open MulAction Finset LeanDring.DRing LeanDring.MonGSet

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.style.longLine false

theorem leaf_102_40_4 (hp : 4 < (Q2.transData.getD 40 []).length)
    (j : Nat) (hj : j < (repChars.getD 102 []).length)
    (hq : (normIsRep.getD 102 []).getD j false = true) :
    species (Q2.reps (⟨40, by decide⟩ : Fin 148)) (colE2 ⟨40, by decide⟩ 4 hp)
        (rowE2 (⟨102, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨40, by decide⟩ : Fin 148))
        (colE1 ⟨40, by decide⟩ 4 (transLenTr ⟨40, by decide⟩ 4 hp))
        (rowE1 (⟨102, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨102, by decide⟩ : Fin 148) ⟨40, by decide⟩ _
      (validAt ⟨102, by decide⟩ (listedAt ⟨102, by decide⟩ hj))
      (colE1 ⟨40, by decide⟩ 4 (transLenTr ⟨40, by decide⟩ 4 hp)) T102_40
      hfix102_40 hinj102_40 hcardT102_40
      (fun i => conj_mem_of_fixedPoints _ _ (T102_40 i) (hfix102_40 i) _)
      ⟨102, by decide⟩ ⟨40, by decide⟩ _
      (Q2.validAt ⟨102, by decide⟩ (Q2.listedAt ⟨102, by decide⟩
        (alnCheck_rep ⟨102, by decide⟩ hj hq).1))
      (colE2 ⟨40, by decide⟩ 4 hp) Q2.T102_40_2 Q2.hfix102_40_2 Q2.hinj102_40_2
      Q2.hcardT102_40_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T102_40_2 i) (Q2.hfix102_40_2 i) _)
      colCert_102_40_4.hD ?_).symm
  rw [alnId_102 j hj]


theorem leaf_102_40_5 (hp : 5 < (Q2.transData.getD 40 []).length)
    (j : Nat) (hj : j < (repChars.getD 102 []).length)
    (hq : (normIsRep.getD 102 []).getD j false = true) :
    species (Q2.reps (⟨40, by decide⟩ : Fin 148)) (colE2 ⟨40, by decide⟩ 5 hp)
        (rowE2 (⟨102, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨40, by decide⟩ : Fin 148))
        (colE1 ⟨40, by decide⟩ 5 (transLenTr ⟨40, by decide⟩ 5 hp))
        (rowE1 (⟨102, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨102, by decide⟩ : Fin 148) ⟨40, by decide⟩ _
      (validAt ⟨102, by decide⟩ (listedAt ⟨102, by decide⟩ hj))
      (colE1 ⟨40, by decide⟩ 5 (transLenTr ⟨40, by decide⟩ 5 hp)) T102_40
      hfix102_40 hinj102_40 hcardT102_40
      (fun i => conj_mem_of_fixedPoints _ _ (T102_40 i) (hfix102_40 i) _)
      ⟨102, by decide⟩ ⟨40, by decide⟩ _
      (Q2.validAt ⟨102, by decide⟩ (Q2.listedAt ⟨102, by decide⟩
        (alnCheck_rep ⟨102, by decide⟩ hj hq).1))
      (colE2 ⟨40, by decide⟩ 5 hp) Q2.T102_40_2 Q2.hfix102_40_2 Q2.hinj102_40_2
      Q2.hcardT102_40_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T102_40_2 i) (Q2.hfix102_40_2 i) _)
      ?_).symm
  rw [show colData1 (⟨102, by decide⟩ : Fin 148)
        ((colE1 ⟨40, by decide⟩ 5 (transLenTr ⟨40, by decide⟩ 5 hp) : ↥(reps ⟨40, by decide⟩)) : Coordinate 1)
        T102_40 = colFn colCertDiv_102_40_5.D1 (m := 25) from colCertDiv_102_40_5.bind1,
    show colData2 (⟨102, by decide⟩ : Fin 148)
        ((colE2 ⟨40, by decide⟩ 5 hp : ↥(Q2.reps ⟨40, by decide⟩)) : Coordinate 2)
        Q2.T102_40_2 = colFn colCertDiv_102_40_5.D2 (m := 25) from colCertDiv_102_40_5.bind2]
  rw [alnId_102 j hj]
  exact fastcode_of_div ⟨102, by decide⟩ _ _ _
    ((alnId_102 j hj) ▸ Q2.listedAt (⟨102, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨102, by decide⟩ : Fin 148) hj hq).1) colCertDiv_102_40_5_match


theorem leaf_102_40_10 (hp : 10 < (Q2.transData.getD 40 []).length)
    (j : Nat) (hj : j < (repChars.getD 102 []).length)
    (hq : (normIsRep.getD 102 []).getD j false = true) :
    species (Q2.reps (⟨40, by decide⟩ : Fin 148)) (colE2 ⟨40, by decide⟩ 10 hp)
        (rowE2 (⟨102, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨40, by decide⟩ : Fin 148))
        (colE1 ⟨40, by decide⟩ 10 (transLenTr ⟨40, by decide⟩ 10 hp))
        (rowE1 (⟨102, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨102, by decide⟩ : Fin 148) ⟨40, by decide⟩ _
      (validAt ⟨102, by decide⟩ (listedAt ⟨102, by decide⟩ hj))
      (colE1 ⟨40, by decide⟩ 10 (transLenTr ⟨40, by decide⟩ 10 hp)) T102_40
      hfix102_40 hinj102_40 hcardT102_40
      (fun i => conj_mem_of_fixedPoints _ _ (T102_40 i) (hfix102_40 i) _)
      ⟨102, by decide⟩ ⟨40, by decide⟩ _
      (Q2.validAt ⟨102, by decide⟩ (Q2.listedAt ⟨102, by decide⟩
        (alnCheck_rep ⟨102, by decide⟩ hj hq).1))
      (colE2 ⟨40, by decide⟩ 10 hp) Q2.T102_40_2 Q2.hfix102_40_2 Q2.hinj102_40_2
      Q2.hcardT102_40_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T102_40_2 i) (Q2.hfix102_40_2 i) _)
      ?_).symm
  rw [show colData1 (⟨102, by decide⟩ : Fin 148)
        ((colE1 ⟨40, by decide⟩ 10 (transLenTr ⟨40, by decide⟩ 10 hp) : ↥(reps ⟨40, by decide⟩)) : Coordinate 1)
        T102_40 = colFn colCertDiv_102_40_10.D1 (m := 25) from colCertDiv_102_40_10.bind1,
    show colData2 (⟨102, by decide⟩ : Fin 148)
        ((colE2 ⟨40, by decide⟩ 10 hp : ↥(Q2.reps ⟨40, by decide⟩)) : Coordinate 2)
        Q2.T102_40_2 = colFn colCertDiv_102_40_10.D2 (m := 25) from colCertDiv_102_40_10.bind2]
  rw [alnId_102 j hj]
  exact fastcode_of_div ⟨102, by decide⟩ _ _ _
    ((alnId_102 j hj) ▸ Q2.listedAt (⟨102, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨102, by decide⟩ : Fin 148) hj hq).1) colCertDiv_102_40_10_match


theorem leaf_102_40_15 (hp : 15 < (Q2.transData.getD 40 []).length)
    (j : Nat) (hj : j < (repChars.getD 102 []).length)
    (hq : (normIsRep.getD 102 []).getD j false = true) :
    species (Q2.reps (⟨40, by decide⟩ : Fin 148)) (colE2 ⟨40, by decide⟩ 15 hp)
        (rowE2 (⟨102, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨40, by decide⟩ : Fin 148))
        (colE1 ⟨40, by decide⟩ 15 (transLenTr ⟨40, by decide⟩ 15 hp))
        (rowE1 (⟨102, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨102, by decide⟩ : Fin 148) ⟨40, by decide⟩ _
      (validAt ⟨102, by decide⟩ (listedAt ⟨102, by decide⟩ hj))
      (colE1 ⟨40, by decide⟩ 15 (transLenTr ⟨40, by decide⟩ 15 hp)) T102_40
      hfix102_40 hinj102_40 hcardT102_40
      (fun i => conj_mem_of_fixedPoints _ _ (T102_40 i) (hfix102_40 i) _)
      ⟨102, by decide⟩ ⟨40, by decide⟩ _
      (Q2.validAt ⟨102, by decide⟩ (Q2.listedAt ⟨102, by decide⟩
        (alnCheck_rep ⟨102, by decide⟩ hj hq).1))
      (colE2 ⟨40, by decide⟩ 15 hp) Q2.T102_40_2 Q2.hfix102_40_2 Q2.hinj102_40_2
      Q2.hcardT102_40_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T102_40_2 i) (Q2.hfix102_40_2 i) _)
      ?_).symm
  rw [show colData1 (⟨102, by decide⟩ : Fin 148)
        ((colE1 ⟨40, by decide⟩ 15 (transLenTr ⟨40, by decide⟩ 15 hp) : ↥(reps ⟨40, by decide⟩)) : Coordinate 1)
        T102_40 = colFn colCertDiv_102_40_15.D1 (m := 25) from colCertDiv_102_40_15.bind1,
    show colData2 (⟨102, by decide⟩ : Fin 148)
        ((colE2 ⟨40, by decide⟩ 15 hp : ↥(Q2.reps ⟨40, by decide⟩)) : Coordinate 2)
        Q2.T102_40_2 = colFn colCertDiv_102_40_15.D2 (m := 25) from colCertDiv_102_40_15.bind2]
  rw [alnId_102 j hj]
  exact fastcode_of_div ⟨102, by decide⟩ _ _ _
    ((alnId_102 j hj) ▸ Q2.listedAt (⟨102, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨102, by decide⟩ : Fin 148) hj hq).1) colCertDiv_102_40_15_match


theorem leaf_102_40_20 (hp : 20 < (Q2.transData.getD 40 []).length)
    (j : Nat) (hj : j < (repChars.getD 102 []).length)
    (hq : (normIsRep.getD 102 []).getD j false = true) :
    species (Q2.reps (⟨40, by decide⟩ : Fin 148)) (colE2 ⟨40, by decide⟩ 20 hp)
        (rowE2 (⟨102, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨40, by decide⟩ : Fin 148))
        (colE1 ⟨40, by decide⟩ 20 (transLenTr ⟨40, by decide⟩ 20 hp))
        (rowE1 (⟨102, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨102, by decide⟩ : Fin 148) ⟨40, by decide⟩ _
      (validAt ⟨102, by decide⟩ (listedAt ⟨102, by decide⟩ hj))
      (colE1 ⟨40, by decide⟩ 20 (transLenTr ⟨40, by decide⟩ 20 hp)) T102_40
      hfix102_40 hinj102_40 hcardT102_40
      (fun i => conj_mem_of_fixedPoints _ _ (T102_40 i) (hfix102_40 i) _)
      ⟨102, by decide⟩ ⟨40, by decide⟩ _
      (Q2.validAt ⟨102, by decide⟩ (Q2.listedAt ⟨102, by decide⟩
        (alnCheck_rep ⟨102, by decide⟩ hj hq).1))
      (colE2 ⟨40, by decide⟩ 20 hp) Q2.T102_40_2 Q2.hfix102_40_2 Q2.hinj102_40_2
      Q2.hcardT102_40_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T102_40_2 i) (Q2.hfix102_40_2 i) _)
      ?_).symm
  rw [show colData1 (⟨102, by decide⟩ : Fin 148)
        ((colE1 ⟨40, by decide⟩ 20 (transLenTr ⟨40, by decide⟩ 20 hp) : ↥(reps ⟨40, by decide⟩)) : Coordinate 1)
        T102_40 = colFn colCertDiv_102_40_20.D1 (m := 25) from colCertDiv_102_40_20.bind1,
    show colData2 (⟨102, by decide⟩ : Fin 148)
        ((colE2 ⟨40, by decide⟩ 20 hp : ↥(Q2.reps ⟨40, by decide⟩)) : Coordinate 2)
        Q2.T102_40_2 = colFn colCertDiv_102_40_20.D2 (m := 25) from colCertDiv_102_40_20.bind2]
  rw [alnId_102 j hj]
  exact fastcode_of_div ⟨102, by decide⟩ _ _ _
    ((alnId_102 j hj) ▸ Q2.listedAt (⟨102, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨102, by decide⟩ : Fin 148) hj hq).1) colCertDiv_102_40_20_match


theorem leaf_102_53_0 (hp : 0 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 102 []).length)
    (hq : (normIsRep.getD 102 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 0 hp)
        (rowE2 (⟨102, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 0 (transLenTr ⟨53, by decide⟩ 0 hp))
        (rowE1 (⟨102, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨102, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨102, by decide⟩ (listedAt ⟨102, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 0 (transLenTr ⟨53, by decide⟩ 0 hp)) T102_53
      hfix102_53 hinj102_53 hcardT102_53
      (fun i => conj_mem_of_fixedPoints _ _ (T102_53 i) (hfix102_53 i) _)
      ⟨102, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨102, by decide⟩ (Q2.listedAt ⟨102, by decide⟩
        (alnCheck_rep ⟨102, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 0 hp) Q2.T102_53_2 Q2.hfix102_53_2 Q2.hinj102_53_2
      Q2.hcardT102_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T102_53_2 i) (Q2.hfix102_53_2 i) _)
      colCert_102_53_0.hD ?_).symm
  rw [alnId_102 j hj]


theorem leaf_102_53_1 (hp : 1 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 102 []).length)
    (hq : (normIsRep.getD 102 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 1 hp)
        (rowE2 (⟨102, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 1 (transLenTr ⟨53, by decide⟩ 1 hp))
        (rowE1 (⟨102, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨102, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨102, by decide⟩ (listedAt ⟨102, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 1 (transLenTr ⟨53, by decide⟩ 1 hp)) T102_53
      hfix102_53 hinj102_53 hcardT102_53
      (fun i => conj_mem_of_fixedPoints _ _ (T102_53 i) (hfix102_53 i) _)
      ⟨102, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨102, by decide⟩ (Q2.listedAt ⟨102, by decide⟩
        (alnCheck_rep ⟨102, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 1 hp) Q2.T102_53_2 Q2.hfix102_53_2 Q2.hinj102_53_2
      Q2.hcardT102_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T102_53_2 i) (Q2.hfix102_53_2 i) _)
      colCert_102_53_1.hD ?_).symm
  rw [alnId_102 j hj]


theorem leaf_102_53_2 (hp : 2 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 102 []).length)
    (hq : (normIsRep.getD 102 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 2 hp)
        (rowE2 (⟨102, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 2 (transLenTr ⟨53, by decide⟩ 2 hp))
        (rowE1 (⟨102, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨102, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨102, by decide⟩ (listedAt ⟨102, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 2 (transLenTr ⟨53, by decide⟩ 2 hp)) T102_53
      hfix102_53 hinj102_53 hcardT102_53
      (fun i => conj_mem_of_fixedPoints _ _ (T102_53 i) (hfix102_53 i) _)
      ⟨102, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨102, by decide⟩ (Q2.listedAt ⟨102, by decide⟩
        (alnCheck_rep ⟨102, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 2 hp) Q2.T102_53_2 Q2.hfix102_53_2 Q2.hinj102_53_2
      Q2.hcardT102_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T102_53_2 i) (Q2.hfix102_53_2 i) _)
      colCert_102_53_2.hD ?_).symm
  rw [alnId_102 j hj]


theorem leaf_102_53_3 (hp : 3 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 102 []).length)
    (hq : (normIsRep.getD 102 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 3 hp)
        (rowE2 (⟨102, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 3 (transLenTr ⟨53, by decide⟩ 3 hp))
        (rowE1 (⟨102, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨102, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨102, by decide⟩ (listedAt ⟨102, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 3 (transLenTr ⟨53, by decide⟩ 3 hp)) T102_53
      hfix102_53 hinj102_53 hcardT102_53
      (fun i => conj_mem_of_fixedPoints _ _ (T102_53 i) (hfix102_53 i) _)
      ⟨102, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨102, by decide⟩ (Q2.listedAt ⟨102, by decide⟩
        (alnCheck_rep ⟨102, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 3 hp) Q2.T102_53_2 Q2.hfix102_53_2 Q2.hinj102_53_2
      Q2.hcardT102_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T102_53_2 i) (Q2.hfix102_53_2 i) _)
      colCert_102_53_3.hD ?_).symm
  rw [alnId_102 j hj]


theorem leaf_102_53_4 (hp : 4 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 102 []).length)
    (hq : (normIsRep.getD 102 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 4 hp)
        (rowE2 (⟨102, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 4 (transLenTr ⟨53, by decide⟩ 4 hp))
        (rowE1 (⟨102, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨102, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨102, by decide⟩ (listedAt ⟨102, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 4 (transLenTr ⟨53, by decide⟩ 4 hp)) T102_53
      hfix102_53 hinj102_53 hcardT102_53
      (fun i => conj_mem_of_fixedPoints _ _ (T102_53 i) (hfix102_53 i) _)
      ⟨102, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨102, by decide⟩ (Q2.listedAt ⟨102, by decide⟩
        (alnCheck_rep ⟨102, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 4 hp) Q2.T102_53_2 Q2.hfix102_53_2 Q2.hinj102_53_2
      Q2.hcardT102_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T102_53_2 i) (Q2.hfix102_53_2 i) _)
      colCert_102_53_4.hD ?_).symm
  rw [alnId_102 j hj]


theorem leaf_102_53_5 (hp : 5 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 102 []).length)
    (hq : (normIsRep.getD 102 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 5 hp)
        (rowE2 (⟨102, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 5 (transLenTr ⟨53, by decide⟩ 5 hp))
        (rowE1 (⟨102, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨102, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨102, by decide⟩ (listedAt ⟨102, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 5 (transLenTr ⟨53, by decide⟩ 5 hp)) T102_53
      hfix102_53 hinj102_53 hcardT102_53
      (fun i => conj_mem_of_fixedPoints _ _ (T102_53 i) (hfix102_53 i) _)
      ⟨102, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨102, by decide⟩ (Q2.listedAt ⟨102, by decide⟩
        (alnCheck_rep ⟨102, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 5 hp) Q2.T102_53_2 Q2.hfix102_53_2 Q2.hinj102_53_2
      Q2.hcardT102_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T102_53_2 i) (Q2.hfix102_53_2 i) _)
      colCert_102_53_5.hD ?_).symm
  rw [alnId_102 j hj]


theorem leaf_102_53_10 (hp : 10 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 102 []).length)
    (hq : (normIsRep.getD 102 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 10 hp)
        (rowE2 (⟨102, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 10 (transLenTr ⟨53, by decide⟩ 10 hp))
        (rowE1 (⟨102, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨102, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨102, by decide⟩ (listedAt ⟨102, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 10 (transLenTr ⟨53, by decide⟩ 10 hp)) T102_53
      hfix102_53 hinj102_53 hcardT102_53
      (fun i => conj_mem_of_fixedPoints _ _ (T102_53 i) (hfix102_53 i) _)
      ⟨102, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨102, by decide⟩ (Q2.listedAt ⟨102, by decide⟩
        (alnCheck_rep ⟨102, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 10 hp) Q2.T102_53_2 Q2.hfix102_53_2 Q2.hinj102_53_2
      Q2.hcardT102_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T102_53_2 i) (Q2.hfix102_53_2 i) _)
      colCert_102_53_10.hD ?_).symm
  rw [alnId_102 j hj]


theorem leaf_102_53_15 (hp : 15 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 102 []).length)
    (hq : (normIsRep.getD 102 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 15 hp)
        (rowE2 (⟨102, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 15 (transLenTr ⟨53, by decide⟩ 15 hp))
        (rowE1 (⟨102, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨102, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨102, by decide⟩ (listedAt ⟨102, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 15 (transLenTr ⟨53, by decide⟩ 15 hp)) T102_53
      hfix102_53 hinj102_53 hcardT102_53
      (fun i => conj_mem_of_fixedPoints _ _ (T102_53 i) (hfix102_53 i) _)
      ⟨102, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨102, by decide⟩ (Q2.listedAt ⟨102, by decide⟩
        (alnCheck_rep ⟨102, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 15 hp) Q2.T102_53_2 Q2.hfix102_53_2 Q2.hinj102_53_2
      Q2.hcardT102_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T102_53_2 i) (Q2.hfix102_53_2 i) _)
      colCert_102_53_15.hD ?_).symm
  rw [alnId_102 j hj]


theorem leaf_102_53_20 (hp : 20 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 102 []).length)
    (hq : (normIsRep.getD 102 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 20 hp)
        (rowE2 (⟨102, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 20 (transLenTr ⟨53, by decide⟩ 20 hp))
        (rowE1 (⟨102, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨102, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨102, by decide⟩ (listedAt ⟨102, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 20 (transLenTr ⟨53, by decide⟩ 20 hp)) T102_53
      hfix102_53 hinj102_53 hcardT102_53
      (fun i => conj_mem_of_fixedPoints _ _ (T102_53 i) (hfix102_53 i) _)
      ⟨102, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨102, by decide⟩ (Q2.listedAt ⟨102, by decide⟩
        (alnCheck_rep ⟨102, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 20 hp) Q2.T102_53_2 Q2.hfix102_53_2 Q2.hinj102_53_2
      Q2.hcardT102_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T102_53_2 i) (Q2.hfix102_53_2 i) _)
      colCert_102_53_20.hD ?_).symm
  rw [alnId_102 j hj]


theorem leaf_102_102_0 (hp : 0 < (Q2.transData.getD 102 []).length)
    (j : Nat) (hj : j < (repChars.getD 102 []).length)
    (hq : (normIsRep.getD 102 []).getD j false = true) :
    species (Q2.reps (⟨102, by decide⟩ : Fin 148)) (colE2 ⟨102, by decide⟩ 0 hp)
        (rowE2 (⟨102, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨102, by decide⟩ : Fin 148))
        (colE1 ⟨102, by decide⟩ 0 (transLenTr ⟨102, by decide⟩ 0 hp))
        (rowE1 (⟨102, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨102, by decide⟩ : Fin 148) ⟨102, by decide⟩ _
      (validAt ⟨102, by decide⟩ (listedAt ⟨102, by decide⟩ hj))
      (colE1 ⟨102, by decide⟩ 0 (transLenTr ⟨102, by decide⟩ 0 hp)) T102_102
      hfix102_102 hinj102_102 hcardT102_102
      (fun i => conj_mem_of_fixedPoints _ _ (T102_102 i) (hfix102_102 i) _)
      ⟨102, by decide⟩ ⟨102, by decide⟩ _
      (Q2.validAt ⟨102, by decide⟩ (Q2.listedAt ⟨102, by decide⟩
        (alnCheck_rep ⟨102, by decide⟩ hj hq).1))
      (colE2 ⟨102, by decide⟩ 0 hp) Q2.T102_102_2 Q2.hfix102_102_2 Q2.hinj102_102_2
      Q2.hcardT102_102_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T102_102_2 i) (Q2.hfix102_102_2 i) _)
      colCert_102_102_0.hD ?_).symm
  rw [alnId_102 j hj]


theorem leaf_102_102_1 (hp : 1 < (Q2.transData.getD 102 []).length)
    (j : Nat) (hj : j < (repChars.getD 102 []).length)
    (hq : (normIsRep.getD 102 []).getD j false = true) :
    species (Q2.reps (⟨102, by decide⟩ : Fin 148)) (colE2 ⟨102, by decide⟩ 1 hp)
        (rowE2 (⟨102, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨102, by decide⟩ : Fin 148))
        (colE1 ⟨102, by decide⟩ 1 (transLenTr ⟨102, by decide⟩ 1 hp))
        (rowE1 (⟨102, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨102, by decide⟩ : Fin 148) ⟨102, by decide⟩ _
      (validAt ⟨102, by decide⟩ (listedAt ⟨102, by decide⟩ hj))
      (colE1 ⟨102, by decide⟩ 1 (transLenTr ⟨102, by decide⟩ 1 hp)) T102_102
      hfix102_102 hinj102_102 hcardT102_102
      (fun i => conj_mem_of_fixedPoints _ _ (T102_102 i) (hfix102_102 i) _)
      ⟨102, by decide⟩ ⟨102, by decide⟩ _
      (Q2.validAt ⟨102, by decide⟩ (Q2.listedAt ⟨102, by decide⟩
        (alnCheck_rep ⟨102, by decide⟩ hj hq).1))
      (colE2 ⟨102, by decide⟩ 1 hp) Q2.T102_102_2 Q2.hfix102_102_2 Q2.hinj102_102_2
      Q2.hcardT102_102_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T102_102_2 i) (Q2.hfix102_102_2 i) _)
      colCert_102_102_1.hD ?_).symm
  rw [alnId_102 j hj]


theorem leaf_102_102_2 (hp : 2 < (Q2.transData.getD 102 []).length)
    (j : Nat) (hj : j < (repChars.getD 102 []).length)
    (hq : (normIsRep.getD 102 []).getD j false = true) :
    species (Q2.reps (⟨102, by decide⟩ : Fin 148)) (colE2 ⟨102, by decide⟩ 2 hp)
        (rowE2 (⟨102, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨102, by decide⟩ : Fin 148))
        (colE1 ⟨102, by decide⟩ 2 (transLenTr ⟨102, by decide⟩ 2 hp))
        (rowE1 (⟨102, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨102, by decide⟩ : Fin 148) ⟨102, by decide⟩ _
      (validAt ⟨102, by decide⟩ (listedAt ⟨102, by decide⟩ hj))
      (colE1 ⟨102, by decide⟩ 2 (transLenTr ⟨102, by decide⟩ 2 hp)) T102_102
      hfix102_102 hinj102_102 hcardT102_102
      (fun i => conj_mem_of_fixedPoints _ _ (T102_102 i) (hfix102_102 i) _)
      ⟨102, by decide⟩ ⟨102, by decide⟩ _
      (Q2.validAt ⟨102, by decide⟩ (Q2.listedAt ⟨102, by decide⟩
        (alnCheck_rep ⟨102, by decide⟩ hj hq).1))
      (colE2 ⟨102, by decide⟩ 2 hp) Q2.T102_102_2 Q2.hfix102_102_2 Q2.hinj102_102_2
      Q2.hcardT102_102_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T102_102_2 i) (Q2.hfix102_102_2 i) _)
      colCert_102_102_2.hD ?_).symm
  rw [alnId_102 j hj]


theorem leaf_102_102_3 (hp : 3 < (Q2.transData.getD 102 []).length)
    (j : Nat) (hj : j < (repChars.getD 102 []).length)
    (hq : (normIsRep.getD 102 []).getD j false = true) :
    species (Q2.reps (⟨102, by decide⟩ : Fin 148)) (colE2 ⟨102, by decide⟩ 3 hp)
        (rowE2 (⟨102, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨102, by decide⟩ : Fin 148))
        (colE1 ⟨102, by decide⟩ 3 (transLenTr ⟨102, by decide⟩ 3 hp))
        (rowE1 (⟨102, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨102, by decide⟩ : Fin 148) ⟨102, by decide⟩ _
      (validAt ⟨102, by decide⟩ (listedAt ⟨102, by decide⟩ hj))
      (colE1 ⟨102, by decide⟩ 3 (transLenTr ⟨102, by decide⟩ 3 hp)) T102_102
      hfix102_102 hinj102_102 hcardT102_102
      (fun i => conj_mem_of_fixedPoints _ _ (T102_102 i) (hfix102_102 i) _)
      ⟨102, by decide⟩ ⟨102, by decide⟩ _
      (Q2.validAt ⟨102, by decide⟩ (Q2.listedAt ⟨102, by decide⟩
        (alnCheck_rep ⟨102, by decide⟩ hj hq).1))
      (colE2 ⟨102, by decide⟩ 3 hp) Q2.T102_102_2 Q2.hfix102_102_2 Q2.hinj102_102_2
      Q2.hcardT102_102_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T102_102_2 i) (Q2.hfix102_102_2 i) _)
      colCert_102_102_3.hD ?_).symm
  rw [alnId_102 j hj]


theorem leaf_102_102_4 (hp : 4 < (Q2.transData.getD 102 []).length)
    (j : Nat) (hj : j < (repChars.getD 102 []).length)
    (hq : (normIsRep.getD 102 []).getD j false = true) :
    species (Q2.reps (⟨102, by decide⟩ : Fin 148)) (colE2 ⟨102, by decide⟩ 4 hp)
        (rowE2 (⟨102, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨102, by decide⟩ : Fin 148))
        (colE1 ⟨102, by decide⟩ 4 (transLenTr ⟨102, by decide⟩ 4 hp))
        (rowE1 (⟨102, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨102, by decide⟩ : Fin 148) ⟨102, by decide⟩ _
      (validAt ⟨102, by decide⟩ (listedAt ⟨102, by decide⟩ hj))
      (colE1 ⟨102, by decide⟩ 4 (transLenTr ⟨102, by decide⟩ 4 hp)) T102_102
      hfix102_102 hinj102_102 hcardT102_102
      (fun i => conj_mem_of_fixedPoints _ _ (T102_102 i) (hfix102_102 i) _)
      ⟨102, by decide⟩ ⟨102, by decide⟩ _
      (Q2.validAt ⟨102, by decide⟩ (Q2.listedAt ⟨102, by decide⟩
        (alnCheck_rep ⟨102, by decide⟩ hj hq).1))
      (colE2 ⟨102, by decide⟩ 4 hp) Q2.T102_102_2 Q2.hfix102_102_2 Q2.hinj102_102_2
      Q2.hcardT102_102_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T102_102_2 i) (Q2.hfix102_102_2 i) _)
      colCert_102_102_4.hD ?_).symm
  rw [alnId_102 j hj]


theorem leaf_102_102_5 (hp : 5 < (Q2.transData.getD 102 []).length)
    (j : Nat) (hj : j < (repChars.getD 102 []).length)
    (hq : (normIsRep.getD 102 []).getD j false = true) :
    species (Q2.reps (⟨102, by decide⟩ : Fin 148)) (colE2 ⟨102, by decide⟩ 5 hp)
        (rowE2 (⟨102, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨102, by decide⟩ : Fin 148))
        (colE1 ⟨102, by decide⟩ 5 (transLenTr ⟨102, by decide⟩ 5 hp))
        (rowE1 (⟨102, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨102, by decide⟩ : Fin 148) ⟨102, by decide⟩ _
      (validAt ⟨102, by decide⟩ (listedAt ⟨102, by decide⟩ hj))
      (colE1 ⟨102, by decide⟩ 5 (transLenTr ⟨102, by decide⟩ 5 hp)) T102_102
      hfix102_102 hinj102_102 hcardT102_102
      (fun i => conj_mem_of_fixedPoints _ _ (T102_102 i) (hfix102_102 i) _)
      ⟨102, by decide⟩ ⟨102, by decide⟩ _
      (Q2.validAt ⟨102, by decide⟩ (Q2.listedAt ⟨102, by decide⟩
        (alnCheck_rep ⟨102, by decide⟩ hj hq).1))
      (colE2 ⟨102, by decide⟩ 5 hp) Q2.T102_102_2 Q2.hfix102_102_2 Q2.hinj102_102_2
      Q2.hcardT102_102_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T102_102_2 i) (Q2.hfix102_102_2 i) _)
      colCert_102_102_5.hD ?_).symm
  rw [alnId_102 j hj]


theorem leaf_102_102_10 (hp : 10 < (Q2.transData.getD 102 []).length)
    (j : Nat) (hj : j < (repChars.getD 102 []).length)
    (hq : (normIsRep.getD 102 []).getD j false = true) :
    species (Q2.reps (⟨102, by decide⟩ : Fin 148)) (colE2 ⟨102, by decide⟩ 10 hp)
        (rowE2 (⟨102, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨102, by decide⟩ : Fin 148))
        (colE1 ⟨102, by decide⟩ 10 (transLenTr ⟨102, by decide⟩ 10 hp))
        (rowE1 (⟨102, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨102, by decide⟩ : Fin 148) ⟨102, by decide⟩ _
      (validAt ⟨102, by decide⟩ (listedAt ⟨102, by decide⟩ hj))
      (colE1 ⟨102, by decide⟩ 10 (transLenTr ⟨102, by decide⟩ 10 hp)) T102_102
      hfix102_102 hinj102_102 hcardT102_102
      (fun i => conj_mem_of_fixedPoints _ _ (T102_102 i) (hfix102_102 i) _)
      ⟨102, by decide⟩ ⟨102, by decide⟩ _
      (Q2.validAt ⟨102, by decide⟩ (Q2.listedAt ⟨102, by decide⟩
        (alnCheck_rep ⟨102, by decide⟩ hj hq).1))
      (colE2 ⟨102, by decide⟩ 10 hp) Q2.T102_102_2 Q2.hfix102_102_2 Q2.hinj102_102_2
      Q2.hcardT102_102_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T102_102_2 i) (Q2.hfix102_102_2 i) _)
      colCert_102_102_10.hD ?_).symm
  rw [alnId_102 j hj]


theorem leaf_102_102_15 (hp : 15 < (Q2.transData.getD 102 []).length)
    (j : Nat) (hj : j < (repChars.getD 102 []).length)
    (hq : (normIsRep.getD 102 []).getD j false = true) :
    species (Q2.reps (⟨102, by decide⟩ : Fin 148)) (colE2 ⟨102, by decide⟩ 15 hp)
        (rowE2 (⟨102, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨102, by decide⟩ : Fin 148))
        (colE1 ⟨102, by decide⟩ 15 (transLenTr ⟨102, by decide⟩ 15 hp))
        (rowE1 (⟨102, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨102, by decide⟩ : Fin 148) ⟨102, by decide⟩ _
      (validAt ⟨102, by decide⟩ (listedAt ⟨102, by decide⟩ hj))
      (colE1 ⟨102, by decide⟩ 15 (transLenTr ⟨102, by decide⟩ 15 hp)) T102_102
      hfix102_102 hinj102_102 hcardT102_102
      (fun i => conj_mem_of_fixedPoints _ _ (T102_102 i) (hfix102_102 i) _)
      ⟨102, by decide⟩ ⟨102, by decide⟩ _
      (Q2.validAt ⟨102, by decide⟩ (Q2.listedAt ⟨102, by decide⟩
        (alnCheck_rep ⟨102, by decide⟩ hj hq).1))
      (colE2 ⟨102, by decide⟩ 15 hp) Q2.T102_102_2 Q2.hfix102_102_2 Q2.hinj102_102_2
      Q2.hcardT102_102_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T102_102_2 i) (Q2.hfix102_102_2 i) _)
      colCert_102_102_15.hD ?_).symm
  rw [alnId_102 j hj]


theorem leaf_102_102_20 (hp : 20 < (Q2.transData.getD 102 []).length)
    (j : Nat) (hj : j < (repChars.getD 102 []).length)
    (hq : (normIsRep.getD 102 []).getD j false = true) :
    species (Q2.reps (⟨102, by decide⟩ : Fin 148)) (colE2 ⟨102, by decide⟩ 20 hp)
        (rowE2 (⟨102, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨102, by decide⟩ : Fin 148))
        (colE1 ⟨102, by decide⟩ 20 (transLenTr ⟨102, by decide⟩ 20 hp))
        (rowE1 (⟨102, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨102, by decide⟩ : Fin 148) ⟨102, by decide⟩ _
      (validAt ⟨102, by decide⟩ (listedAt ⟨102, by decide⟩ hj))
      (colE1 ⟨102, by decide⟩ 20 (transLenTr ⟨102, by decide⟩ 20 hp)) T102_102
      hfix102_102 hinj102_102 hcardT102_102
      (fun i => conj_mem_of_fixedPoints _ _ (T102_102 i) (hfix102_102 i) _)
      ⟨102, by decide⟩ ⟨102, by decide⟩ _
      (Q2.validAt ⟨102, by decide⟩ (Q2.listedAt ⟨102, by decide⟩
        (alnCheck_rep ⟨102, by decide⟩ hj hq).1))
      (colE2 ⟨102, by decide⟩ 20 hp) Q2.T102_102_2 Q2.hfix102_102_2 Q2.hinj102_102_2
      Q2.hcardT102_102_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T102_102_2 i) (Q2.hfix102_102_2 i) _)
      colCert_102_102_20.hD ?_).symm
  rw [alnId_102 j hj]


theorem leaf_103_10_0 (hp : 0 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 103 []).length)
    (hq : (normIsRep.getD 103 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 0 hp)
        (rowE2 (⟨103, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 0 (transLenTr ⟨10, by decide⟩ 0 hp))
        (rowE1 (⟨103, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨103, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨103, by decide⟩ (listedAt ⟨103, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 0 (transLenTr ⟨10, by decide⟩ 0 hp)) T103_10
      hfix103_10 hinj103_10 hcardT103_10
      (fun i => conj_mem_of_fixedPoints _ _ (T103_10 i) (hfix103_10 i) _)
      ⟨103, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨103, by decide⟩ (Q2.listedAt ⟨103, by decide⟩
        (alnCheck_rep ⟨103, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 0 hp) Q2.T103_10_2 Q2.hfix103_10_2 Q2.hinj103_10_2
      Q2.hcardT103_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T103_10_2 i) (Q2.hfix103_10_2 i) _)
      colCert_103_10_0.hD ?_).symm
  rw [alnId_103 j hj]


theorem leaf_103_10_1 (hp : 1 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 103 []).length)
    (hq : (normIsRep.getD 103 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 1 hp)
        (rowE2 (⟨103, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 1 (transLenTr ⟨10, by decide⟩ 1 hp))
        (rowE1 (⟨103, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨103, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨103, by decide⟩ (listedAt ⟨103, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 1 (transLenTr ⟨10, by decide⟩ 1 hp)) T103_10
      hfix103_10 hinj103_10 hcardT103_10
      (fun i => conj_mem_of_fixedPoints _ _ (T103_10 i) (hfix103_10 i) _)
      ⟨103, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨103, by decide⟩ (Q2.listedAt ⟨103, by decide⟩
        (alnCheck_rep ⟨103, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 1 hp) Q2.T103_10_2 Q2.hfix103_10_2 Q2.hinj103_10_2
      Q2.hcardT103_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T103_10_2 i) (Q2.hfix103_10_2 i) _)
      colCert_103_10_1.hD ?_).symm
  rw [alnId_103 j hj]


theorem leaf_103_10_2 (hp : 2 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 103 []).length)
    (hq : (normIsRep.getD 103 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 2 hp)
        (rowE2 (⟨103, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 2 (transLenTr ⟨10, by decide⟩ 2 hp))
        (rowE1 (⟨103, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨103, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨103, by decide⟩ (listedAt ⟨103, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 2 (transLenTr ⟨10, by decide⟩ 2 hp)) T103_10
      hfix103_10 hinj103_10 hcardT103_10
      (fun i => conj_mem_of_fixedPoints _ _ (T103_10 i) (hfix103_10 i) _)
      ⟨103, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨103, by decide⟩ (Q2.listedAt ⟨103, by decide⟩
        (alnCheck_rep ⟨103, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 2 hp) Q2.T103_10_2 Q2.hfix103_10_2 Q2.hinj103_10_2
      Q2.hcardT103_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T103_10_2 i) (Q2.hfix103_10_2 i) _)
      colCert_103_10_2.hD ?_).symm
  rw [alnId_103 j hj]


theorem leaf_103_10_3 (hp : 3 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 103 []).length)
    (hq : (normIsRep.getD 103 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 3 hp)
        (rowE2 (⟨103, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 3 (transLenTr ⟨10, by decide⟩ 3 hp))
        (rowE1 (⟨103, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨103, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨103, by decide⟩ (listedAt ⟨103, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 3 (transLenTr ⟨10, by decide⟩ 3 hp)) T103_10
      hfix103_10 hinj103_10 hcardT103_10
      (fun i => conj_mem_of_fixedPoints _ _ (T103_10 i) (hfix103_10 i) _)
      ⟨103, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨103, by decide⟩ (Q2.listedAt ⟨103, by decide⟩
        (alnCheck_rep ⟨103, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 3 hp) Q2.T103_10_2 Q2.hfix103_10_2 Q2.hinj103_10_2
      Q2.hcardT103_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T103_10_2 i) (Q2.hfix103_10_2 i) _)
      colCert_103_10_3.hD ?_).symm
  rw [alnId_103 j hj]


theorem leaf_103_10_4 (hp : 4 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 103 []).length)
    (hq : (normIsRep.getD 103 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 4 hp)
        (rowE2 (⟨103, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 4 (transLenTr ⟨10, by decide⟩ 4 hp))
        (rowE1 (⟨103, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨103, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨103, by decide⟩ (listedAt ⟨103, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 4 (transLenTr ⟨10, by decide⟩ 4 hp)) T103_10
      hfix103_10 hinj103_10 hcardT103_10
      (fun i => conj_mem_of_fixedPoints _ _ (T103_10 i) (hfix103_10 i) _)
      ⟨103, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨103, by decide⟩ (Q2.listedAt ⟨103, by decide⟩
        (alnCheck_rep ⟨103, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 4 hp) Q2.T103_10_2 Q2.hfix103_10_2 Q2.hinj103_10_2
      Q2.hcardT103_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T103_10_2 i) (Q2.hfix103_10_2 i) _)
      colCert_103_10_4.hD ?_).symm
  rw [alnId_103 j hj]


theorem leaf_103_12_0 (hp : 0 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 103 []).length)
    (hq : (normIsRep.getD 103 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 0 hp)
        (rowE2 (⟨103, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp))
        (rowE1 (⟨103, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨103, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨103, by decide⟩ (listedAt ⟨103, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp)) T103_12
      hfix103_12 hinj103_12 hcardT103_12
      (fun i => conj_mem_of_fixedPoints _ _ (T103_12 i) (hfix103_12 i) _)
      ⟨103, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨103, by decide⟩ (Q2.listedAt ⟨103, by decide⟩
        (alnCheck_rep ⟨103, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 0 hp) Q2.T103_12_2 Q2.hfix103_12_2 Q2.hinj103_12_2
      Q2.hcardT103_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T103_12_2 i) (Q2.hfix103_12_2 i) _)
      colCert_103_12_0.hD ?_).symm
  rw [alnId_103 j hj]


theorem leaf_103_12_1 (hp : 1 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 103 []).length)
    (hq : (normIsRep.getD 103 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 1 hp)
        (rowE2 (⟨103, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp))
        (rowE1 (⟨103, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨103, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨103, by decide⟩ (listedAt ⟨103, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp)) T103_12
      hfix103_12 hinj103_12 hcardT103_12
      (fun i => conj_mem_of_fixedPoints _ _ (T103_12 i) (hfix103_12 i) _)
      ⟨103, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨103, by decide⟩ (Q2.listedAt ⟨103, by decide⟩
        (alnCheck_rep ⟨103, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 1 hp) Q2.T103_12_2 Q2.hfix103_12_2 Q2.hinj103_12_2
      Q2.hcardT103_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T103_12_2 i) (Q2.hfix103_12_2 i) _)
      colCert_103_12_1.hD ?_).symm
  rw [alnId_103 j hj]


theorem leaf_103_12_2 (hp : 2 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 103 []).length)
    (hq : (normIsRep.getD 103 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 2 hp)
        (rowE2 (⟨103, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp))
        (rowE1 (⟨103, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨103, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨103, by decide⟩ (listedAt ⟨103, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp)) T103_12
      hfix103_12 hinj103_12 hcardT103_12
      (fun i => conj_mem_of_fixedPoints _ _ (T103_12 i) (hfix103_12 i) _)
      ⟨103, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨103, by decide⟩ (Q2.listedAt ⟨103, by decide⟩
        (alnCheck_rep ⟨103, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 2 hp) Q2.T103_12_2 Q2.hfix103_12_2 Q2.hinj103_12_2
      Q2.hcardT103_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T103_12_2 i) (Q2.hfix103_12_2 i) _)
      colCert_103_12_2.hD ?_).symm
  rw [alnId_103 j hj]


theorem leaf_103_12_3 (hp : 3 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 103 []).length)
    (hq : (normIsRep.getD 103 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 3 hp)
        (rowE2 (⟨103, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp))
        (rowE1 (⟨103, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨103, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨103, by decide⟩ (listedAt ⟨103, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp)) T103_12
      hfix103_12 hinj103_12 hcardT103_12
      (fun i => conj_mem_of_fixedPoints _ _ (T103_12 i) (hfix103_12 i) _)
      ⟨103, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨103, by decide⟩ (Q2.listedAt ⟨103, by decide⟩
        (alnCheck_rep ⟨103, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 3 hp) Q2.T103_12_2 Q2.hfix103_12_2 Q2.hinj103_12_2
      Q2.hcardT103_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T103_12_2 i) (Q2.hfix103_12_2 i) _)
      colCert_103_12_3.hD ?_).symm
  rw [alnId_103 j hj]


theorem leaf_103_12_4 (hp : 4 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 103 []).length)
    (hq : (normIsRep.getD 103 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 4 hp)
        (rowE2 (⟨103, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp))
        (rowE1 (⟨103, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨103, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨103, by decide⟩ (listedAt ⟨103, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp)) T103_12
      hfix103_12 hinj103_12 hcardT103_12
      (fun i => conj_mem_of_fixedPoints _ _ (T103_12 i) (hfix103_12 i) _)
      ⟨103, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨103, by decide⟩ (Q2.listedAt ⟨103, by decide⟩
        (alnCheck_rep ⟨103, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 4 hp) Q2.T103_12_2 Q2.hfix103_12_2 Q2.hinj103_12_2
      Q2.hcardT103_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T103_12_2 i) (Q2.hfix103_12_2 i) _)
      colCert_103_12_4.hD ?_).symm
  rw [alnId_103 j hj]


theorem leaf_103_41_0 (hp : 0 < (Q2.transData.getD 41 []).length)
    (j : Nat) (hj : j < (repChars.getD 103 []).length)
    (hq : (normIsRep.getD 103 []).getD j false = true) :
    species (Q2.reps (⟨41, by decide⟩ : Fin 148)) (colE2 ⟨41, by decide⟩ 0 hp)
        (rowE2 (⟨103, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨41, by decide⟩ : Fin 148))
        (colE1 ⟨41, by decide⟩ 0 (transLenTr ⟨41, by decide⟩ 0 hp))
        (rowE1 (⟨103, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨103, by decide⟩ : Fin 148) ⟨41, by decide⟩ _
      (validAt ⟨103, by decide⟩ (listedAt ⟨103, by decide⟩ hj))
      (colE1 ⟨41, by decide⟩ 0 (transLenTr ⟨41, by decide⟩ 0 hp)) T103_41
      hfix103_41 hinj103_41 hcardT103_41
      (fun i => conj_mem_of_fixedPoints _ _ (T103_41 i) (hfix103_41 i) _)
      ⟨103, by decide⟩ ⟨41, by decide⟩ _
      (Q2.validAt ⟨103, by decide⟩ (Q2.listedAt ⟨103, by decide⟩
        (alnCheck_rep ⟨103, by decide⟩ hj hq).1))
      (colE2 ⟨41, by decide⟩ 0 hp) Q2.T103_41_2 Q2.hfix103_41_2 Q2.hinj103_41_2
      Q2.hcardT103_41_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T103_41_2 i) (Q2.hfix103_41_2 i) _)
      colCert_103_41_0.hD ?_).symm
  rw [alnId_103 j hj]


theorem leaf_103_41_1 (hp : 1 < (Q2.transData.getD 41 []).length)
    (j : Nat) (hj : j < (repChars.getD 103 []).length)
    (hq : (normIsRep.getD 103 []).getD j false = true) :
    species (Q2.reps (⟨41, by decide⟩ : Fin 148)) (colE2 ⟨41, by decide⟩ 1 hp)
        (rowE2 (⟨103, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨41, by decide⟩ : Fin 148))
        (colE1 ⟨41, by decide⟩ 1 (transLenTr ⟨41, by decide⟩ 1 hp))
        (rowE1 (⟨103, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨103, by decide⟩ : Fin 148) ⟨41, by decide⟩ _
      (validAt ⟨103, by decide⟩ (listedAt ⟨103, by decide⟩ hj))
      (colE1 ⟨41, by decide⟩ 1 (transLenTr ⟨41, by decide⟩ 1 hp)) T103_41
      hfix103_41 hinj103_41 hcardT103_41
      (fun i => conj_mem_of_fixedPoints _ _ (T103_41 i) (hfix103_41 i) _)
      ⟨103, by decide⟩ ⟨41, by decide⟩ _
      (Q2.validAt ⟨103, by decide⟩ (Q2.listedAt ⟨103, by decide⟩
        (alnCheck_rep ⟨103, by decide⟩ hj hq).1))
      (colE2 ⟨41, by decide⟩ 1 hp) Q2.T103_41_2 Q2.hfix103_41_2 Q2.hinj103_41_2
      Q2.hcardT103_41_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T103_41_2 i) (Q2.hfix103_41_2 i) _)
      colCert_103_41_1.hD ?_).symm
  rw [alnId_103 j hj]


theorem leaf_103_41_2 (hp : 2 < (Q2.transData.getD 41 []).length)
    (j : Nat) (hj : j < (repChars.getD 103 []).length)
    (hq : (normIsRep.getD 103 []).getD j false = true) :
    species (Q2.reps (⟨41, by decide⟩ : Fin 148)) (colE2 ⟨41, by decide⟩ 2 hp)
        (rowE2 (⟨103, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨41, by decide⟩ : Fin 148))
        (colE1 ⟨41, by decide⟩ 2 (transLenTr ⟨41, by decide⟩ 2 hp))
        (rowE1 (⟨103, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨103, by decide⟩ : Fin 148) ⟨41, by decide⟩ _
      (validAt ⟨103, by decide⟩ (listedAt ⟨103, by decide⟩ hj))
      (colE1 ⟨41, by decide⟩ 2 (transLenTr ⟨41, by decide⟩ 2 hp)) T103_41
      hfix103_41 hinj103_41 hcardT103_41
      (fun i => conj_mem_of_fixedPoints _ _ (T103_41 i) (hfix103_41 i) _)
      ⟨103, by decide⟩ ⟨41, by decide⟩ _
      (Q2.validAt ⟨103, by decide⟩ (Q2.listedAt ⟨103, by decide⟩
        (alnCheck_rep ⟨103, by decide⟩ hj hq).1))
      (colE2 ⟨41, by decide⟩ 2 hp) Q2.T103_41_2 Q2.hfix103_41_2 Q2.hinj103_41_2
      Q2.hcardT103_41_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T103_41_2 i) (Q2.hfix103_41_2 i) _)
      colCert_103_41_2.hD ?_).symm
  rw [alnId_103 j hj]


theorem leaf_103_41_3 (hp : 3 < (Q2.transData.getD 41 []).length)
    (j : Nat) (hj : j < (repChars.getD 103 []).length)
    (hq : (normIsRep.getD 103 []).getD j false = true) :
    species (Q2.reps (⟨41, by decide⟩ : Fin 148)) (colE2 ⟨41, by decide⟩ 3 hp)
        (rowE2 (⟨103, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨41, by decide⟩ : Fin 148))
        (colE1 ⟨41, by decide⟩ 3 (transLenTr ⟨41, by decide⟩ 3 hp))
        (rowE1 (⟨103, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨103, by decide⟩ : Fin 148) ⟨41, by decide⟩ _
      (validAt ⟨103, by decide⟩ (listedAt ⟨103, by decide⟩ hj))
      (colE1 ⟨41, by decide⟩ 3 (transLenTr ⟨41, by decide⟩ 3 hp)) T103_41
      hfix103_41 hinj103_41 hcardT103_41
      (fun i => conj_mem_of_fixedPoints _ _ (T103_41 i) (hfix103_41 i) _)
      ⟨103, by decide⟩ ⟨41, by decide⟩ _
      (Q2.validAt ⟨103, by decide⟩ (Q2.listedAt ⟨103, by decide⟩
        (alnCheck_rep ⟨103, by decide⟩ hj hq).1))
      (colE2 ⟨41, by decide⟩ 3 hp) Q2.T103_41_2 Q2.hfix103_41_2 Q2.hinj103_41_2
      Q2.hcardT103_41_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T103_41_2 i) (Q2.hfix103_41_2 i) _)
      colCert_103_41_3.hD ?_).symm
  rw [alnId_103 j hj]


theorem leaf_103_41_4 (hp : 4 < (Q2.transData.getD 41 []).length)
    (j : Nat) (hj : j < (repChars.getD 103 []).length)
    (hq : (normIsRep.getD 103 []).getD j false = true) :
    species (Q2.reps (⟨41, by decide⟩ : Fin 148)) (colE2 ⟨41, by decide⟩ 4 hp)
        (rowE2 (⟨103, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨41, by decide⟩ : Fin 148))
        (colE1 ⟨41, by decide⟩ 4 (transLenTr ⟨41, by decide⟩ 4 hp))
        (rowE1 (⟨103, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨103, by decide⟩ : Fin 148) ⟨41, by decide⟩ _
      (validAt ⟨103, by decide⟩ (listedAt ⟨103, by decide⟩ hj))
      (colE1 ⟨41, by decide⟩ 4 (transLenTr ⟨41, by decide⟩ 4 hp)) T103_41
      hfix103_41 hinj103_41 hcardT103_41
      (fun i => conj_mem_of_fixedPoints _ _ (T103_41 i) (hfix103_41 i) _)
      ⟨103, by decide⟩ ⟨41, by decide⟩ _
      (Q2.validAt ⟨103, by decide⟩ (Q2.listedAt ⟨103, by decide⟩
        (alnCheck_rep ⟨103, by decide⟩ hj hq).1))
      (colE2 ⟨41, by decide⟩ 4 hp) Q2.T103_41_2 Q2.hfix103_41_2 Q2.hinj103_41_2
      Q2.hcardT103_41_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T103_41_2 i) (Q2.hfix103_41_2 i) _)
      colCert_103_41_4.hD ?_).symm
  rw [alnId_103 j hj]


theorem leaf_103_41_5 (hp : 5 < (Q2.transData.getD 41 []).length)
    (j : Nat) (hj : j < (repChars.getD 103 []).length)
    (hq : (normIsRep.getD 103 []).getD j false = true) :
    species (Q2.reps (⟨41, by decide⟩ : Fin 148)) (colE2 ⟨41, by decide⟩ 5 hp)
        (rowE2 (⟨103, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨41, by decide⟩ : Fin 148))
        (colE1 ⟨41, by decide⟩ 5 (transLenTr ⟨41, by decide⟩ 5 hp))
        (rowE1 (⟨103, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨103, by decide⟩ : Fin 148) ⟨41, by decide⟩ _
      (validAt ⟨103, by decide⟩ (listedAt ⟨103, by decide⟩ hj))
      (colE1 ⟨41, by decide⟩ 5 (transLenTr ⟨41, by decide⟩ 5 hp)) T103_41
      hfix103_41 hinj103_41 hcardT103_41
      (fun i => conj_mem_of_fixedPoints _ _ (T103_41 i) (hfix103_41 i) _)
      ⟨103, by decide⟩ ⟨41, by decide⟩ _
      (Q2.validAt ⟨103, by decide⟩ (Q2.listedAt ⟨103, by decide⟩
        (alnCheck_rep ⟨103, by decide⟩ hj hq).1))
      (colE2 ⟨41, by decide⟩ 5 hp) Q2.T103_41_2 Q2.hfix103_41_2 Q2.hinj103_41_2
      Q2.hcardT103_41_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T103_41_2 i) (Q2.hfix103_41_2 i) _)
      ?_).symm
  rw [show colData1 (⟨103, by decide⟩ : Fin 148)
        ((colE1 ⟨41, by decide⟩ 5 (transLenTr ⟨41, by decide⟩ 5 hp) : ↥(reps ⟨41, by decide⟩)) : Coordinate 1)
        T103_41 = colFn colCertDiv_103_41_5.D1 (m := 25) from colCertDiv_103_41_5.bind1,
    show colData2 (⟨103, by decide⟩ : Fin 148)
        ((colE2 ⟨41, by decide⟩ 5 hp : ↥(Q2.reps ⟨41, by decide⟩)) : Coordinate 2)
        Q2.T103_41_2 = colFn colCertDiv_103_41_5.D2 (m := 25) from colCertDiv_103_41_5.bind2]
  rw [alnId_103 j hj]
  exact fastcode_of_div ⟨103, by decide⟩ _ _ _
    ((alnId_103 j hj) ▸ Q2.listedAt (⟨103, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨103, by decide⟩ : Fin 148) hj hq).1) colCertDiv_103_41_5_match


theorem leaf_103_41_10 (hp : 10 < (Q2.transData.getD 41 []).length)
    (j : Nat) (hj : j < (repChars.getD 103 []).length)
    (hq : (normIsRep.getD 103 []).getD j false = true) :
    species (Q2.reps (⟨41, by decide⟩ : Fin 148)) (colE2 ⟨41, by decide⟩ 10 hp)
        (rowE2 (⟨103, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨41, by decide⟩ : Fin 148))
        (colE1 ⟨41, by decide⟩ 10 (transLenTr ⟨41, by decide⟩ 10 hp))
        (rowE1 (⟨103, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨103, by decide⟩ : Fin 148) ⟨41, by decide⟩ _
      (validAt ⟨103, by decide⟩ (listedAt ⟨103, by decide⟩ hj))
      (colE1 ⟨41, by decide⟩ 10 (transLenTr ⟨41, by decide⟩ 10 hp)) T103_41
      hfix103_41 hinj103_41 hcardT103_41
      (fun i => conj_mem_of_fixedPoints _ _ (T103_41 i) (hfix103_41 i) _)
      ⟨103, by decide⟩ ⟨41, by decide⟩ _
      (Q2.validAt ⟨103, by decide⟩ (Q2.listedAt ⟨103, by decide⟩
        (alnCheck_rep ⟨103, by decide⟩ hj hq).1))
      (colE2 ⟨41, by decide⟩ 10 hp) Q2.T103_41_2 Q2.hfix103_41_2 Q2.hinj103_41_2
      Q2.hcardT103_41_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T103_41_2 i) (Q2.hfix103_41_2 i) _)
      ?_).symm
  rw [show colData1 (⟨103, by decide⟩ : Fin 148)
        ((colE1 ⟨41, by decide⟩ 10 (transLenTr ⟨41, by decide⟩ 10 hp) : ↥(reps ⟨41, by decide⟩)) : Coordinate 1)
        T103_41 = colFn colCertDiv_103_41_10.D1 (m := 25) from colCertDiv_103_41_10.bind1,
    show colData2 (⟨103, by decide⟩ : Fin 148)
        ((colE2 ⟨41, by decide⟩ 10 hp : ↥(Q2.reps ⟨41, by decide⟩)) : Coordinate 2)
        Q2.T103_41_2 = colFn colCertDiv_103_41_10.D2 (m := 25) from colCertDiv_103_41_10.bind2]
  rw [alnId_103 j hj]
  exact fastcode_of_div ⟨103, by decide⟩ _ _ _
    ((alnId_103 j hj) ▸ Q2.listedAt (⟨103, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨103, by decide⟩ : Fin 148) hj hq).1) colCertDiv_103_41_10_match


theorem leaf_103_41_15 (hp : 15 < (Q2.transData.getD 41 []).length)
    (j : Nat) (hj : j < (repChars.getD 103 []).length)
    (hq : (normIsRep.getD 103 []).getD j false = true) :
    species (Q2.reps (⟨41, by decide⟩ : Fin 148)) (colE2 ⟨41, by decide⟩ 15 hp)
        (rowE2 (⟨103, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨41, by decide⟩ : Fin 148))
        (colE1 ⟨41, by decide⟩ 15 (transLenTr ⟨41, by decide⟩ 15 hp))
        (rowE1 (⟨103, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨103, by decide⟩ : Fin 148) ⟨41, by decide⟩ _
      (validAt ⟨103, by decide⟩ (listedAt ⟨103, by decide⟩ hj))
      (colE1 ⟨41, by decide⟩ 15 (transLenTr ⟨41, by decide⟩ 15 hp)) T103_41
      hfix103_41 hinj103_41 hcardT103_41
      (fun i => conj_mem_of_fixedPoints _ _ (T103_41 i) (hfix103_41 i) _)
      ⟨103, by decide⟩ ⟨41, by decide⟩ _
      (Q2.validAt ⟨103, by decide⟩ (Q2.listedAt ⟨103, by decide⟩
        (alnCheck_rep ⟨103, by decide⟩ hj hq).1))
      (colE2 ⟨41, by decide⟩ 15 hp) Q2.T103_41_2 Q2.hfix103_41_2 Q2.hinj103_41_2
      Q2.hcardT103_41_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T103_41_2 i) (Q2.hfix103_41_2 i) _)
      ?_).symm
  rw [show colData1 (⟨103, by decide⟩ : Fin 148)
        ((colE1 ⟨41, by decide⟩ 15 (transLenTr ⟨41, by decide⟩ 15 hp) : ↥(reps ⟨41, by decide⟩)) : Coordinate 1)
        T103_41 = colFn colCertDiv_103_41_15.D1 (m := 25) from colCertDiv_103_41_15.bind1,
    show colData2 (⟨103, by decide⟩ : Fin 148)
        ((colE2 ⟨41, by decide⟩ 15 hp : ↥(Q2.reps ⟨41, by decide⟩)) : Coordinate 2)
        Q2.T103_41_2 = colFn colCertDiv_103_41_15.D2 (m := 25) from colCertDiv_103_41_15.bind2]
  rw [alnId_103 j hj]
  exact fastcode_of_div ⟨103, by decide⟩ _ _ _
    ((alnId_103 j hj) ▸ Q2.listedAt (⟨103, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨103, by decide⟩ : Fin 148) hj hq).1) colCertDiv_103_41_15_match


theorem leaf_103_41_20 (hp : 20 < (Q2.transData.getD 41 []).length)
    (j : Nat) (hj : j < (repChars.getD 103 []).length)
    (hq : (normIsRep.getD 103 []).getD j false = true) :
    species (Q2.reps (⟨41, by decide⟩ : Fin 148)) (colE2 ⟨41, by decide⟩ 20 hp)
        (rowE2 (⟨103, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨41, by decide⟩ : Fin 148))
        (colE1 ⟨41, by decide⟩ 20 (transLenTr ⟨41, by decide⟩ 20 hp))
        (rowE1 (⟨103, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨103, by decide⟩ : Fin 148) ⟨41, by decide⟩ _
      (validAt ⟨103, by decide⟩ (listedAt ⟨103, by decide⟩ hj))
      (colE1 ⟨41, by decide⟩ 20 (transLenTr ⟨41, by decide⟩ 20 hp)) T103_41
      hfix103_41 hinj103_41 hcardT103_41
      (fun i => conj_mem_of_fixedPoints _ _ (T103_41 i) (hfix103_41 i) _)
      ⟨103, by decide⟩ ⟨41, by decide⟩ _
      (Q2.validAt ⟨103, by decide⟩ (Q2.listedAt ⟨103, by decide⟩
        (alnCheck_rep ⟨103, by decide⟩ hj hq).1))
      (colE2 ⟨41, by decide⟩ 20 hp) Q2.T103_41_2 Q2.hfix103_41_2 Q2.hinj103_41_2
      Q2.hcardT103_41_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T103_41_2 i) (Q2.hfix103_41_2 i) _)
      ?_).symm
  rw [show colData1 (⟨103, by decide⟩ : Fin 148)
        ((colE1 ⟨41, by decide⟩ 20 (transLenTr ⟨41, by decide⟩ 20 hp) : ↥(reps ⟨41, by decide⟩)) : Coordinate 1)
        T103_41 = colFn colCertDiv_103_41_20.D1 (m := 25) from colCertDiv_103_41_20.bind1,
    show colData2 (⟨103, by decide⟩ : Fin 148)
        ((colE2 ⟨41, by decide⟩ 20 hp : ↥(Q2.reps ⟨41, by decide⟩)) : Coordinate 2)
        Q2.T103_41_2 = colFn colCertDiv_103_41_20.D2 (m := 25) from colCertDiv_103_41_20.bind2]
  rw [alnId_103 j hj]
  exact fastcode_of_div ⟨103, by decide⟩ _ _ _
    ((alnId_103 j hj) ▸ Q2.listedAt (⟨103, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨103, by decide⟩ : Fin 148) hj hq).1) colCertDiv_103_41_20_match


theorem leaf_103_53_0 (hp : 0 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 103 []).length)
    (hq : (normIsRep.getD 103 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 0 hp)
        (rowE2 (⟨103, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 0 (transLenTr ⟨53, by decide⟩ 0 hp))
        (rowE1 (⟨103, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨103, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨103, by decide⟩ (listedAt ⟨103, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 0 (transLenTr ⟨53, by decide⟩ 0 hp)) T103_53
      hfix103_53 hinj103_53 hcardT103_53
      (fun i => conj_mem_of_fixedPoints _ _ (T103_53 i) (hfix103_53 i) _)
      ⟨103, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨103, by decide⟩ (Q2.listedAt ⟨103, by decide⟩
        (alnCheck_rep ⟨103, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 0 hp) Q2.T103_53_2 Q2.hfix103_53_2 Q2.hinj103_53_2
      Q2.hcardT103_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T103_53_2 i) (Q2.hfix103_53_2 i) _)
      colCert_103_53_0.hD ?_).symm
  rw [alnId_103 j hj]


theorem leaf_103_53_1 (hp : 1 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 103 []).length)
    (hq : (normIsRep.getD 103 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 1 hp)
        (rowE2 (⟨103, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 1 (transLenTr ⟨53, by decide⟩ 1 hp))
        (rowE1 (⟨103, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨103, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨103, by decide⟩ (listedAt ⟨103, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 1 (transLenTr ⟨53, by decide⟩ 1 hp)) T103_53
      hfix103_53 hinj103_53 hcardT103_53
      (fun i => conj_mem_of_fixedPoints _ _ (T103_53 i) (hfix103_53 i) _)
      ⟨103, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨103, by decide⟩ (Q2.listedAt ⟨103, by decide⟩
        (alnCheck_rep ⟨103, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 1 hp) Q2.T103_53_2 Q2.hfix103_53_2 Q2.hinj103_53_2
      Q2.hcardT103_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T103_53_2 i) (Q2.hfix103_53_2 i) _)
      colCert_103_53_1.hD ?_).symm
  rw [alnId_103 j hj]


theorem leaf_103_53_2 (hp : 2 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 103 []).length)
    (hq : (normIsRep.getD 103 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 2 hp)
        (rowE2 (⟨103, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 2 (transLenTr ⟨53, by decide⟩ 2 hp))
        (rowE1 (⟨103, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨103, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨103, by decide⟩ (listedAt ⟨103, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 2 (transLenTr ⟨53, by decide⟩ 2 hp)) T103_53
      hfix103_53 hinj103_53 hcardT103_53
      (fun i => conj_mem_of_fixedPoints _ _ (T103_53 i) (hfix103_53 i) _)
      ⟨103, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨103, by decide⟩ (Q2.listedAt ⟨103, by decide⟩
        (alnCheck_rep ⟨103, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 2 hp) Q2.T103_53_2 Q2.hfix103_53_2 Q2.hinj103_53_2
      Q2.hcardT103_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T103_53_2 i) (Q2.hfix103_53_2 i) _)
      colCert_103_53_2.hD ?_).symm
  rw [alnId_103 j hj]


theorem leaf_103_53_3 (hp : 3 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 103 []).length)
    (hq : (normIsRep.getD 103 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 3 hp)
        (rowE2 (⟨103, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 3 (transLenTr ⟨53, by decide⟩ 3 hp))
        (rowE1 (⟨103, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨103, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨103, by decide⟩ (listedAt ⟨103, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 3 (transLenTr ⟨53, by decide⟩ 3 hp)) T103_53
      hfix103_53 hinj103_53 hcardT103_53
      (fun i => conj_mem_of_fixedPoints _ _ (T103_53 i) (hfix103_53 i) _)
      ⟨103, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨103, by decide⟩ (Q2.listedAt ⟨103, by decide⟩
        (alnCheck_rep ⟨103, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 3 hp) Q2.T103_53_2 Q2.hfix103_53_2 Q2.hinj103_53_2
      Q2.hcardT103_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T103_53_2 i) (Q2.hfix103_53_2 i) _)
      colCert_103_53_3.hD ?_).symm
  rw [alnId_103 j hj]


theorem leaf_103_53_4 (hp : 4 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 103 []).length)
    (hq : (normIsRep.getD 103 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 4 hp)
        (rowE2 (⟨103, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 4 (transLenTr ⟨53, by decide⟩ 4 hp))
        (rowE1 (⟨103, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨103, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨103, by decide⟩ (listedAt ⟨103, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 4 (transLenTr ⟨53, by decide⟩ 4 hp)) T103_53
      hfix103_53 hinj103_53 hcardT103_53
      (fun i => conj_mem_of_fixedPoints _ _ (T103_53 i) (hfix103_53 i) _)
      ⟨103, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨103, by decide⟩ (Q2.listedAt ⟨103, by decide⟩
        (alnCheck_rep ⟨103, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 4 hp) Q2.T103_53_2 Q2.hfix103_53_2 Q2.hinj103_53_2
      Q2.hcardT103_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T103_53_2 i) (Q2.hfix103_53_2 i) _)
      colCert_103_53_4.hD ?_).symm
  rw [alnId_103 j hj]


theorem leaf_103_53_5 (hp : 5 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 103 []).length)
    (hq : (normIsRep.getD 103 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 5 hp)
        (rowE2 (⟨103, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 5 (transLenTr ⟨53, by decide⟩ 5 hp))
        (rowE1 (⟨103, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨103, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨103, by decide⟩ (listedAt ⟨103, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 5 (transLenTr ⟨53, by decide⟩ 5 hp)) T103_53
      hfix103_53 hinj103_53 hcardT103_53
      (fun i => conj_mem_of_fixedPoints _ _ (T103_53 i) (hfix103_53 i) _)
      ⟨103, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨103, by decide⟩ (Q2.listedAt ⟨103, by decide⟩
        (alnCheck_rep ⟨103, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 5 hp) Q2.T103_53_2 Q2.hfix103_53_2 Q2.hinj103_53_2
      Q2.hcardT103_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T103_53_2 i) (Q2.hfix103_53_2 i) _)
      colCert_103_53_5.hD ?_).symm
  rw [alnId_103 j hj]


theorem leaf_103_53_10 (hp : 10 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 103 []).length)
    (hq : (normIsRep.getD 103 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 10 hp)
        (rowE2 (⟨103, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 10 (transLenTr ⟨53, by decide⟩ 10 hp))
        (rowE1 (⟨103, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨103, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨103, by decide⟩ (listedAt ⟨103, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 10 (transLenTr ⟨53, by decide⟩ 10 hp)) T103_53
      hfix103_53 hinj103_53 hcardT103_53
      (fun i => conj_mem_of_fixedPoints _ _ (T103_53 i) (hfix103_53 i) _)
      ⟨103, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨103, by decide⟩ (Q2.listedAt ⟨103, by decide⟩
        (alnCheck_rep ⟨103, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 10 hp) Q2.T103_53_2 Q2.hfix103_53_2 Q2.hinj103_53_2
      Q2.hcardT103_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T103_53_2 i) (Q2.hfix103_53_2 i) _)
      colCert_103_53_10.hD ?_).symm
  rw [alnId_103 j hj]


theorem leaf_103_53_15 (hp : 15 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 103 []).length)
    (hq : (normIsRep.getD 103 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 15 hp)
        (rowE2 (⟨103, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 15 (transLenTr ⟨53, by decide⟩ 15 hp))
        (rowE1 (⟨103, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨103, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨103, by decide⟩ (listedAt ⟨103, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 15 (transLenTr ⟨53, by decide⟩ 15 hp)) T103_53
      hfix103_53 hinj103_53 hcardT103_53
      (fun i => conj_mem_of_fixedPoints _ _ (T103_53 i) (hfix103_53 i) _)
      ⟨103, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨103, by decide⟩ (Q2.listedAt ⟨103, by decide⟩
        (alnCheck_rep ⟨103, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 15 hp) Q2.T103_53_2 Q2.hfix103_53_2 Q2.hinj103_53_2
      Q2.hcardT103_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T103_53_2 i) (Q2.hfix103_53_2 i) _)
      colCert_103_53_15.hD ?_).symm
  rw [alnId_103 j hj]


theorem leaf_103_53_20 (hp : 20 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 103 []).length)
    (hq : (normIsRep.getD 103 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 20 hp)
        (rowE2 (⟨103, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 20 (transLenTr ⟨53, by decide⟩ 20 hp))
        (rowE1 (⟨103, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨103, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨103, by decide⟩ (listedAt ⟨103, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 20 (transLenTr ⟨53, by decide⟩ 20 hp)) T103_53
      hfix103_53 hinj103_53 hcardT103_53
      (fun i => conj_mem_of_fixedPoints _ _ (T103_53 i) (hfix103_53 i) _)
      ⟨103, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨103, by decide⟩ (Q2.listedAt ⟨103, by decide⟩
        (alnCheck_rep ⟨103, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 20 hp) Q2.T103_53_2 Q2.hfix103_53_2 Q2.hinj103_53_2
      Q2.hcardT103_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T103_53_2 i) (Q2.hfix103_53_2 i) _)
      colCert_103_53_20.hD ?_).symm
  rw [alnId_103 j hj]


theorem leaf_103_103_0 (hp : 0 < (Q2.transData.getD 103 []).length)
    (j : Nat) (hj : j < (repChars.getD 103 []).length)
    (hq : (normIsRep.getD 103 []).getD j false = true) :
    species (Q2.reps (⟨103, by decide⟩ : Fin 148)) (colE2 ⟨103, by decide⟩ 0 hp)
        (rowE2 (⟨103, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨103, by decide⟩ : Fin 148))
        (colE1 ⟨103, by decide⟩ 0 (transLenTr ⟨103, by decide⟩ 0 hp))
        (rowE1 (⟨103, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨103, by decide⟩ : Fin 148) ⟨103, by decide⟩ _
      (validAt ⟨103, by decide⟩ (listedAt ⟨103, by decide⟩ hj))
      (colE1 ⟨103, by decide⟩ 0 (transLenTr ⟨103, by decide⟩ 0 hp)) T103_103
      hfix103_103 hinj103_103 hcardT103_103
      (fun i => conj_mem_of_fixedPoints _ _ (T103_103 i) (hfix103_103 i) _)
      ⟨103, by decide⟩ ⟨103, by decide⟩ _
      (Q2.validAt ⟨103, by decide⟩ (Q2.listedAt ⟨103, by decide⟩
        (alnCheck_rep ⟨103, by decide⟩ hj hq).1))
      (colE2 ⟨103, by decide⟩ 0 hp) Q2.T103_103_2 Q2.hfix103_103_2 Q2.hinj103_103_2
      Q2.hcardT103_103_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T103_103_2 i) (Q2.hfix103_103_2 i) _)
      colCert_103_103_0.hD ?_).symm
  rw [alnId_103 j hj]


theorem leaf_103_103_1 (hp : 1 < (Q2.transData.getD 103 []).length)
    (j : Nat) (hj : j < (repChars.getD 103 []).length)
    (hq : (normIsRep.getD 103 []).getD j false = true) :
    species (Q2.reps (⟨103, by decide⟩ : Fin 148)) (colE2 ⟨103, by decide⟩ 1 hp)
        (rowE2 (⟨103, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨103, by decide⟩ : Fin 148))
        (colE1 ⟨103, by decide⟩ 1 (transLenTr ⟨103, by decide⟩ 1 hp))
        (rowE1 (⟨103, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨103, by decide⟩ : Fin 148) ⟨103, by decide⟩ _
      (validAt ⟨103, by decide⟩ (listedAt ⟨103, by decide⟩ hj))
      (colE1 ⟨103, by decide⟩ 1 (transLenTr ⟨103, by decide⟩ 1 hp)) T103_103
      hfix103_103 hinj103_103 hcardT103_103
      (fun i => conj_mem_of_fixedPoints _ _ (T103_103 i) (hfix103_103 i) _)
      ⟨103, by decide⟩ ⟨103, by decide⟩ _
      (Q2.validAt ⟨103, by decide⟩ (Q2.listedAt ⟨103, by decide⟩
        (alnCheck_rep ⟨103, by decide⟩ hj hq).1))
      (colE2 ⟨103, by decide⟩ 1 hp) Q2.T103_103_2 Q2.hfix103_103_2 Q2.hinj103_103_2
      Q2.hcardT103_103_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T103_103_2 i) (Q2.hfix103_103_2 i) _)
      colCert_103_103_1.hD ?_).symm
  rw [alnId_103 j hj]


theorem leaf_103_103_2 (hp : 2 < (Q2.transData.getD 103 []).length)
    (j : Nat) (hj : j < (repChars.getD 103 []).length)
    (hq : (normIsRep.getD 103 []).getD j false = true) :
    species (Q2.reps (⟨103, by decide⟩ : Fin 148)) (colE2 ⟨103, by decide⟩ 2 hp)
        (rowE2 (⟨103, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨103, by decide⟩ : Fin 148))
        (colE1 ⟨103, by decide⟩ 2 (transLenTr ⟨103, by decide⟩ 2 hp))
        (rowE1 (⟨103, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨103, by decide⟩ : Fin 148) ⟨103, by decide⟩ _
      (validAt ⟨103, by decide⟩ (listedAt ⟨103, by decide⟩ hj))
      (colE1 ⟨103, by decide⟩ 2 (transLenTr ⟨103, by decide⟩ 2 hp)) T103_103
      hfix103_103 hinj103_103 hcardT103_103
      (fun i => conj_mem_of_fixedPoints _ _ (T103_103 i) (hfix103_103 i) _)
      ⟨103, by decide⟩ ⟨103, by decide⟩ _
      (Q2.validAt ⟨103, by decide⟩ (Q2.listedAt ⟨103, by decide⟩
        (alnCheck_rep ⟨103, by decide⟩ hj hq).1))
      (colE2 ⟨103, by decide⟩ 2 hp) Q2.T103_103_2 Q2.hfix103_103_2 Q2.hinj103_103_2
      Q2.hcardT103_103_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T103_103_2 i) (Q2.hfix103_103_2 i) _)
      colCert_103_103_2.hD ?_).symm
  rw [alnId_103 j hj]


theorem leaf_103_103_3 (hp : 3 < (Q2.transData.getD 103 []).length)
    (j : Nat) (hj : j < (repChars.getD 103 []).length)
    (hq : (normIsRep.getD 103 []).getD j false = true) :
    species (Q2.reps (⟨103, by decide⟩ : Fin 148)) (colE2 ⟨103, by decide⟩ 3 hp)
        (rowE2 (⟨103, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨103, by decide⟩ : Fin 148))
        (colE1 ⟨103, by decide⟩ 3 (transLenTr ⟨103, by decide⟩ 3 hp))
        (rowE1 (⟨103, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨103, by decide⟩ : Fin 148) ⟨103, by decide⟩ _
      (validAt ⟨103, by decide⟩ (listedAt ⟨103, by decide⟩ hj))
      (colE1 ⟨103, by decide⟩ 3 (transLenTr ⟨103, by decide⟩ 3 hp)) T103_103
      hfix103_103 hinj103_103 hcardT103_103
      (fun i => conj_mem_of_fixedPoints _ _ (T103_103 i) (hfix103_103 i) _)
      ⟨103, by decide⟩ ⟨103, by decide⟩ _
      (Q2.validAt ⟨103, by decide⟩ (Q2.listedAt ⟨103, by decide⟩
        (alnCheck_rep ⟨103, by decide⟩ hj hq).1))
      (colE2 ⟨103, by decide⟩ 3 hp) Q2.T103_103_2 Q2.hfix103_103_2 Q2.hinj103_103_2
      Q2.hcardT103_103_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T103_103_2 i) (Q2.hfix103_103_2 i) _)
      colCert_103_103_3.hD ?_).symm
  rw [alnId_103 j hj]


theorem leaf_103_103_4 (hp : 4 < (Q2.transData.getD 103 []).length)
    (j : Nat) (hj : j < (repChars.getD 103 []).length)
    (hq : (normIsRep.getD 103 []).getD j false = true) :
    species (Q2.reps (⟨103, by decide⟩ : Fin 148)) (colE2 ⟨103, by decide⟩ 4 hp)
        (rowE2 (⟨103, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨103, by decide⟩ : Fin 148))
        (colE1 ⟨103, by decide⟩ 4 (transLenTr ⟨103, by decide⟩ 4 hp))
        (rowE1 (⟨103, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨103, by decide⟩ : Fin 148) ⟨103, by decide⟩ _
      (validAt ⟨103, by decide⟩ (listedAt ⟨103, by decide⟩ hj))
      (colE1 ⟨103, by decide⟩ 4 (transLenTr ⟨103, by decide⟩ 4 hp)) T103_103
      hfix103_103 hinj103_103 hcardT103_103
      (fun i => conj_mem_of_fixedPoints _ _ (T103_103 i) (hfix103_103 i) _)
      ⟨103, by decide⟩ ⟨103, by decide⟩ _
      (Q2.validAt ⟨103, by decide⟩ (Q2.listedAt ⟨103, by decide⟩
        (alnCheck_rep ⟨103, by decide⟩ hj hq).1))
      (colE2 ⟨103, by decide⟩ 4 hp) Q2.T103_103_2 Q2.hfix103_103_2 Q2.hinj103_103_2
      Q2.hcardT103_103_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T103_103_2 i) (Q2.hfix103_103_2 i) _)
      colCert_103_103_4.hD ?_).symm
  rw [alnId_103 j hj]


theorem leaf_103_103_5 (hp : 5 < (Q2.transData.getD 103 []).length)
    (j : Nat) (hj : j < (repChars.getD 103 []).length)
    (hq : (normIsRep.getD 103 []).getD j false = true) :
    species (Q2.reps (⟨103, by decide⟩ : Fin 148)) (colE2 ⟨103, by decide⟩ 5 hp)
        (rowE2 (⟨103, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨103, by decide⟩ : Fin 148))
        (colE1 ⟨103, by decide⟩ 5 (transLenTr ⟨103, by decide⟩ 5 hp))
        (rowE1 (⟨103, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨103, by decide⟩ : Fin 148) ⟨103, by decide⟩ _
      (validAt ⟨103, by decide⟩ (listedAt ⟨103, by decide⟩ hj))
      (colE1 ⟨103, by decide⟩ 5 (transLenTr ⟨103, by decide⟩ 5 hp)) T103_103
      hfix103_103 hinj103_103 hcardT103_103
      (fun i => conj_mem_of_fixedPoints _ _ (T103_103 i) (hfix103_103 i) _)
      ⟨103, by decide⟩ ⟨103, by decide⟩ _
      (Q2.validAt ⟨103, by decide⟩ (Q2.listedAt ⟨103, by decide⟩
        (alnCheck_rep ⟨103, by decide⟩ hj hq).1))
      (colE2 ⟨103, by decide⟩ 5 hp) Q2.T103_103_2 Q2.hfix103_103_2 Q2.hinj103_103_2
      Q2.hcardT103_103_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T103_103_2 i) (Q2.hfix103_103_2 i) _)
      colCert_103_103_5.hD ?_).symm
  rw [alnId_103 j hj]


theorem leaf_103_103_10 (hp : 10 < (Q2.transData.getD 103 []).length)
    (j : Nat) (hj : j < (repChars.getD 103 []).length)
    (hq : (normIsRep.getD 103 []).getD j false = true) :
    species (Q2.reps (⟨103, by decide⟩ : Fin 148)) (colE2 ⟨103, by decide⟩ 10 hp)
        (rowE2 (⟨103, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨103, by decide⟩ : Fin 148))
        (colE1 ⟨103, by decide⟩ 10 (transLenTr ⟨103, by decide⟩ 10 hp))
        (rowE1 (⟨103, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨103, by decide⟩ : Fin 148) ⟨103, by decide⟩ _
      (validAt ⟨103, by decide⟩ (listedAt ⟨103, by decide⟩ hj))
      (colE1 ⟨103, by decide⟩ 10 (transLenTr ⟨103, by decide⟩ 10 hp)) T103_103
      hfix103_103 hinj103_103 hcardT103_103
      (fun i => conj_mem_of_fixedPoints _ _ (T103_103 i) (hfix103_103 i) _)
      ⟨103, by decide⟩ ⟨103, by decide⟩ _
      (Q2.validAt ⟨103, by decide⟩ (Q2.listedAt ⟨103, by decide⟩
        (alnCheck_rep ⟨103, by decide⟩ hj hq).1))
      (colE2 ⟨103, by decide⟩ 10 hp) Q2.T103_103_2 Q2.hfix103_103_2 Q2.hinj103_103_2
      Q2.hcardT103_103_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T103_103_2 i) (Q2.hfix103_103_2 i) _)
      colCert_103_103_10.hD ?_).symm
  rw [alnId_103 j hj]


theorem leaf_103_103_15 (hp : 15 < (Q2.transData.getD 103 []).length)
    (j : Nat) (hj : j < (repChars.getD 103 []).length)
    (hq : (normIsRep.getD 103 []).getD j false = true) :
    species (Q2.reps (⟨103, by decide⟩ : Fin 148)) (colE2 ⟨103, by decide⟩ 15 hp)
        (rowE2 (⟨103, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨103, by decide⟩ : Fin 148))
        (colE1 ⟨103, by decide⟩ 15 (transLenTr ⟨103, by decide⟩ 15 hp))
        (rowE1 (⟨103, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨103, by decide⟩ : Fin 148) ⟨103, by decide⟩ _
      (validAt ⟨103, by decide⟩ (listedAt ⟨103, by decide⟩ hj))
      (colE1 ⟨103, by decide⟩ 15 (transLenTr ⟨103, by decide⟩ 15 hp)) T103_103
      hfix103_103 hinj103_103 hcardT103_103
      (fun i => conj_mem_of_fixedPoints _ _ (T103_103 i) (hfix103_103 i) _)
      ⟨103, by decide⟩ ⟨103, by decide⟩ _
      (Q2.validAt ⟨103, by decide⟩ (Q2.listedAt ⟨103, by decide⟩
        (alnCheck_rep ⟨103, by decide⟩ hj hq).1))
      (colE2 ⟨103, by decide⟩ 15 hp) Q2.T103_103_2 Q2.hfix103_103_2 Q2.hinj103_103_2
      Q2.hcardT103_103_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T103_103_2 i) (Q2.hfix103_103_2 i) _)
      colCert_103_103_15.hD ?_).symm
  rw [alnId_103 j hj]


theorem leaf_103_103_20 (hp : 20 < (Q2.transData.getD 103 []).length)
    (j : Nat) (hj : j < (repChars.getD 103 []).length)
    (hq : (normIsRep.getD 103 []).getD j false = true) :
    species (Q2.reps (⟨103, by decide⟩ : Fin 148)) (colE2 ⟨103, by decide⟩ 20 hp)
        (rowE2 (⟨103, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨103, by decide⟩ : Fin 148))
        (colE1 ⟨103, by decide⟩ 20 (transLenTr ⟨103, by decide⟩ 20 hp))
        (rowE1 (⟨103, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨103, by decide⟩ : Fin 148) ⟨103, by decide⟩ _
      (validAt ⟨103, by decide⟩ (listedAt ⟨103, by decide⟩ hj))
      (colE1 ⟨103, by decide⟩ 20 (transLenTr ⟨103, by decide⟩ 20 hp)) T103_103
      hfix103_103 hinj103_103 hcardT103_103
      (fun i => conj_mem_of_fixedPoints _ _ (T103_103 i) (hfix103_103 i) _)
      ⟨103, by decide⟩ ⟨103, by decide⟩ _
      (Q2.validAt ⟨103, by decide⟩ (Q2.listedAt ⟨103, by decide⟩
        (alnCheck_rep ⟨103, by decide⟩ hj hq).1))
      (colE2 ⟨103, by decide⟩ 20 hp) Q2.T103_103_2 Q2.hfix103_103_2 Q2.hinj103_103_2
      Q2.hcardT103_103_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T103_103_2 i) (Q2.hfix103_103_2 i) _)
      colCert_103_103_20.hD ?_).symm
  rw [alnId_103 j hj]


theorem leaf_104_10_0 (hp : 0 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 104 []).length)
    (hq : (normIsRep.getD 104 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 0 hp)
        (rowE2 (⟨104, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 0 (transLenTr ⟨10, by decide⟩ 0 hp))
        (rowE1 (⟨104, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨104, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨104, by decide⟩ (listedAt ⟨104, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 0 (transLenTr ⟨10, by decide⟩ 0 hp)) T104_10
      hfix104_10 hinj104_10 hcardT104_10
      (fun i => conj_mem_of_fixedPoints _ _ (T104_10 i) (hfix104_10 i) _)
      ⟨104, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨104, by decide⟩ (Q2.listedAt ⟨104, by decide⟩
        (alnCheck_rep ⟨104, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 0 hp) Q2.T104_10_2 Q2.hfix104_10_2 Q2.hinj104_10_2
      Q2.hcardT104_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T104_10_2 i) (Q2.hfix104_10_2 i) _)
      colCert_104_10_0.hD ?_).symm
  rw [alnId_104 j hj]


theorem leaf_104_10_1 (hp : 1 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 104 []).length)
    (hq : (normIsRep.getD 104 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 1 hp)
        (rowE2 (⟨104, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 1 (transLenTr ⟨10, by decide⟩ 1 hp))
        (rowE1 (⟨104, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨104, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨104, by decide⟩ (listedAt ⟨104, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 1 (transLenTr ⟨10, by decide⟩ 1 hp)) T104_10
      hfix104_10 hinj104_10 hcardT104_10
      (fun i => conj_mem_of_fixedPoints _ _ (T104_10 i) (hfix104_10 i) _)
      ⟨104, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨104, by decide⟩ (Q2.listedAt ⟨104, by decide⟩
        (alnCheck_rep ⟨104, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 1 hp) Q2.T104_10_2 Q2.hfix104_10_2 Q2.hinj104_10_2
      Q2.hcardT104_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T104_10_2 i) (Q2.hfix104_10_2 i) _)
      colCert_104_10_1.hD ?_).symm
  rw [alnId_104 j hj]


theorem leaf_104_10_2 (hp : 2 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 104 []).length)
    (hq : (normIsRep.getD 104 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 2 hp)
        (rowE2 (⟨104, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 2 (transLenTr ⟨10, by decide⟩ 2 hp))
        (rowE1 (⟨104, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨104, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨104, by decide⟩ (listedAt ⟨104, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 2 (transLenTr ⟨10, by decide⟩ 2 hp)) T104_10
      hfix104_10 hinj104_10 hcardT104_10
      (fun i => conj_mem_of_fixedPoints _ _ (T104_10 i) (hfix104_10 i) _)
      ⟨104, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨104, by decide⟩ (Q2.listedAt ⟨104, by decide⟩
        (alnCheck_rep ⟨104, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 2 hp) Q2.T104_10_2 Q2.hfix104_10_2 Q2.hinj104_10_2
      Q2.hcardT104_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T104_10_2 i) (Q2.hfix104_10_2 i) _)
      colCert_104_10_2.hD ?_).symm
  rw [alnId_104 j hj]


theorem leaf_104_10_3 (hp : 3 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 104 []).length)
    (hq : (normIsRep.getD 104 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 3 hp)
        (rowE2 (⟨104, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 3 (transLenTr ⟨10, by decide⟩ 3 hp))
        (rowE1 (⟨104, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨104, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨104, by decide⟩ (listedAt ⟨104, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 3 (transLenTr ⟨10, by decide⟩ 3 hp)) T104_10
      hfix104_10 hinj104_10 hcardT104_10
      (fun i => conj_mem_of_fixedPoints _ _ (T104_10 i) (hfix104_10 i) _)
      ⟨104, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨104, by decide⟩ (Q2.listedAt ⟨104, by decide⟩
        (alnCheck_rep ⟨104, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 3 hp) Q2.T104_10_2 Q2.hfix104_10_2 Q2.hinj104_10_2
      Q2.hcardT104_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T104_10_2 i) (Q2.hfix104_10_2 i) _)
      colCert_104_10_3.hD ?_).symm
  rw [alnId_104 j hj]


theorem leaf_104_10_4 (hp : 4 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 104 []).length)
    (hq : (normIsRep.getD 104 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 4 hp)
        (rowE2 (⟨104, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 4 (transLenTr ⟨10, by decide⟩ 4 hp))
        (rowE1 (⟨104, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨104, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨104, by decide⟩ (listedAt ⟨104, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 4 (transLenTr ⟨10, by decide⟩ 4 hp)) T104_10
      hfix104_10 hinj104_10 hcardT104_10
      (fun i => conj_mem_of_fixedPoints _ _ (T104_10 i) (hfix104_10 i) _)
      ⟨104, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨104, by decide⟩ (Q2.listedAt ⟨104, by decide⟩
        (alnCheck_rep ⟨104, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 4 hp) Q2.T104_10_2 Q2.hfix104_10_2 Q2.hinj104_10_2
      Q2.hcardT104_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T104_10_2 i) (Q2.hfix104_10_2 i) _)
      colCert_104_10_4.hD ?_).symm
  rw [alnId_104 j hj]


theorem leaf_104_12_0 (hp : 0 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 104 []).length)
    (hq : (normIsRep.getD 104 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 0 hp)
        (rowE2 (⟨104, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp))
        (rowE1 (⟨104, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨104, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨104, by decide⟩ (listedAt ⟨104, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp)) T104_12
      hfix104_12 hinj104_12 hcardT104_12
      (fun i => conj_mem_of_fixedPoints _ _ (T104_12 i) (hfix104_12 i) _)
      ⟨104, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨104, by decide⟩ (Q2.listedAt ⟨104, by decide⟩
        (alnCheck_rep ⟨104, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 0 hp) Q2.T104_12_2 Q2.hfix104_12_2 Q2.hinj104_12_2
      Q2.hcardT104_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T104_12_2 i) (Q2.hfix104_12_2 i) _)
      colCert_104_12_0.hD ?_).symm
  rw [alnId_104 j hj]


theorem leaf_104_12_1 (hp : 1 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 104 []).length)
    (hq : (normIsRep.getD 104 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 1 hp)
        (rowE2 (⟨104, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp))
        (rowE1 (⟨104, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨104, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨104, by decide⟩ (listedAt ⟨104, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp)) T104_12
      hfix104_12 hinj104_12 hcardT104_12
      (fun i => conj_mem_of_fixedPoints _ _ (T104_12 i) (hfix104_12 i) _)
      ⟨104, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨104, by decide⟩ (Q2.listedAt ⟨104, by decide⟩
        (alnCheck_rep ⟨104, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 1 hp) Q2.T104_12_2 Q2.hfix104_12_2 Q2.hinj104_12_2
      Q2.hcardT104_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T104_12_2 i) (Q2.hfix104_12_2 i) _)
      colCert_104_12_1.hD ?_).symm
  rw [alnId_104 j hj]


theorem leaf_104_12_2 (hp : 2 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 104 []).length)
    (hq : (normIsRep.getD 104 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 2 hp)
        (rowE2 (⟨104, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp))
        (rowE1 (⟨104, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨104, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨104, by decide⟩ (listedAt ⟨104, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp)) T104_12
      hfix104_12 hinj104_12 hcardT104_12
      (fun i => conj_mem_of_fixedPoints _ _ (T104_12 i) (hfix104_12 i) _)
      ⟨104, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨104, by decide⟩ (Q2.listedAt ⟨104, by decide⟩
        (alnCheck_rep ⟨104, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 2 hp) Q2.T104_12_2 Q2.hfix104_12_2 Q2.hinj104_12_2
      Q2.hcardT104_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T104_12_2 i) (Q2.hfix104_12_2 i) _)
      colCert_104_12_2.hD ?_).symm
  rw [alnId_104 j hj]


theorem leaf_104_12_3 (hp : 3 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 104 []).length)
    (hq : (normIsRep.getD 104 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 3 hp)
        (rowE2 (⟨104, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp))
        (rowE1 (⟨104, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨104, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨104, by decide⟩ (listedAt ⟨104, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp)) T104_12
      hfix104_12 hinj104_12 hcardT104_12
      (fun i => conj_mem_of_fixedPoints _ _ (T104_12 i) (hfix104_12 i) _)
      ⟨104, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨104, by decide⟩ (Q2.listedAt ⟨104, by decide⟩
        (alnCheck_rep ⟨104, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 3 hp) Q2.T104_12_2 Q2.hfix104_12_2 Q2.hinj104_12_2
      Q2.hcardT104_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T104_12_2 i) (Q2.hfix104_12_2 i) _)
      colCert_104_12_3.hD ?_).symm
  rw [alnId_104 j hj]


theorem leaf_104_12_4 (hp : 4 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 104 []).length)
    (hq : (normIsRep.getD 104 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 4 hp)
        (rowE2 (⟨104, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp))
        (rowE1 (⟨104, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨104, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨104, by decide⟩ (listedAt ⟨104, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp)) T104_12
      hfix104_12 hinj104_12 hcardT104_12
      (fun i => conj_mem_of_fixedPoints _ _ (T104_12 i) (hfix104_12 i) _)
      ⟨104, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨104, by decide⟩ (Q2.listedAt ⟨104, by decide⟩
        (alnCheck_rep ⟨104, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 4 hp) Q2.T104_12_2 Q2.hfix104_12_2 Q2.hinj104_12_2
      Q2.hcardT104_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T104_12_2 i) (Q2.hfix104_12_2 i) _)
      colCert_104_12_4.hD ?_).symm
  rw [alnId_104 j hj]


theorem leaf_104_42_0 (hp : 0 < (Q2.transData.getD 42 []).length)
    (j : Nat) (hj : j < (repChars.getD 104 []).length)
    (hq : (normIsRep.getD 104 []).getD j false = true) :
    species (Q2.reps (⟨42, by decide⟩ : Fin 148)) (colE2 ⟨42, by decide⟩ 0 hp)
        (rowE2 (⟨104, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨42, by decide⟩ : Fin 148))
        (colE1 ⟨42, by decide⟩ 0 (transLenTr ⟨42, by decide⟩ 0 hp))
        (rowE1 (⟨104, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨104, by decide⟩ : Fin 148) ⟨42, by decide⟩ _
      (validAt ⟨104, by decide⟩ (listedAt ⟨104, by decide⟩ hj))
      (colE1 ⟨42, by decide⟩ 0 (transLenTr ⟨42, by decide⟩ 0 hp)) T104_42
      hfix104_42 hinj104_42 hcardT104_42
      (fun i => conj_mem_of_fixedPoints _ _ (T104_42 i) (hfix104_42 i) _)
      ⟨104, by decide⟩ ⟨42, by decide⟩ _
      (Q2.validAt ⟨104, by decide⟩ (Q2.listedAt ⟨104, by decide⟩
        (alnCheck_rep ⟨104, by decide⟩ hj hq).1))
      (colE2 ⟨42, by decide⟩ 0 hp) Q2.T104_42_2 Q2.hfix104_42_2 Q2.hinj104_42_2
      Q2.hcardT104_42_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T104_42_2 i) (Q2.hfix104_42_2 i) _)
      colCert_104_42_0.hD ?_).symm
  rw [alnId_104 j hj]


theorem leaf_104_42_1 (hp : 1 < (Q2.transData.getD 42 []).length)
    (j : Nat) (hj : j < (repChars.getD 104 []).length)
    (hq : (normIsRep.getD 104 []).getD j false = true) :
    species (Q2.reps (⟨42, by decide⟩ : Fin 148)) (colE2 ⟨42, by decide⟩ 1 hp)
        (rowE2 (⟨104, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨42, by decide⟩ : Fin 148))
        (colE1 ⟨42, by decide⟩ 1 (transLenTr ⟨42, by decide⟩ 1 hp))
        (rowE1 (⟨104, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨104, by decide⟩ : Fin 148) ⟨42, by decide⟩ _
      (validAt ⟨104, by decide⟩ (listedAt ⟨104, by decide⟩ hj))
      (colE1 ⟨42, by decide⟩ 1 (transLenTr ⟨42, by decide⟩ 1 hp)) T104_42
      hfix104_42 hinj104_42 hcardT104_42
      (fun i => conj_mem_of_fixedPoints _ _ (T104_42 i) (hfix104_42 i) _)
      ⟨104, by decide⟩ ⟨42, by decide⟩ _
      (Q2.validAt ⟨104, by decide⟩ (Q2.listedAt ⟨104, by decide⟩
        (alnCheck_rep ⟨104, by decide⟩ hj hq).1))
      (colE2 ⟨42, by decide⟩ 1 hp) Q2.T104_42_2 Q2.hfix104_42_2 Q2.hinj104_42_2
      Q2.hcardT104_42_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T104_42_2 i) (Q2.hfix104_42_2 i) _)
      colCert_104_42_1.hD ?_).symm
  rw [alnId_104 j hj]


theorem leaf_104_42_2 (hp : 2 < (Q2.transData.getD 42 []).length)
    (j : Nat) (hj : j < (repChars.getD 104 []).length)
    (hq : (normIsRep.getD 104 []).getD j false = true) :
    species (Q2.reps (⟨42, by decide⟩ : Fin 148)) (colE2 ⟨42, by decide⟩ 2 hp)
        (rowE2 (⟨104, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨42, by decide⟩ : Fin 148))
        (colE1 ⟨42, by decide⟩ 2 (transLenTr ⟨42, by decide⟩ 2 hp))
        (rowE1 (⟨104, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨104, by decide⟩ : Fin 148) ⟨42, by decide⟩ _
      (validAt ⟨104, by decide⟩ (listedAt ⟨104, by decide⟩ hj))
      (colE1 ⟨42, by decide⟩ 2 (transLenTr ⟨42, by decide⟩ 2 hp)) T104_42
      hfix104_42 hinj104_42 hcardT104_42
      (fun i => conj_mem_of_fixedPoints _ _ (T104_42 i) (hfix104_42 i) _)
      ⟨104, by decide⟩ ⟨42, by decide⟩ _
      (Q2.validAt ⟨104, by decide⟩ (Q2.listedAt ⟨104, by decide⟩
        (alnCheck_rep ⟨104, by decide⟩ hj hq).1))
      (colE2 ⟨42, by decide⟩ 2 hp) Q2.T104_42_2 Q2.hfix104_42_2 Q2.hinj104_42_2
      Q2.hcardT104_42_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T104_42_2 i) (Q2.hfix104_42_2 i) _)
      colCert_104_42_2.hD ?_).symm
  rw [alnId_104 j hj]


theorem leaf_104_42_3 (hp : 3 < (Q2.transData.getD 42 []).length)
    (j : Nat) (hj : j < (repChars.getD 104 []).length)
    (hq : (normIsRep.getD 104 []).getD j false = true) :
    species (Q2.reps (⟨42, by decide⟩ : Fin 148)) (colE2 ⟨42, by decide⟩ 3 hp)
        (rowE2 (⟨104, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨42, by decide⟩ : Fin 148))
        (colE1 ⟨42, by decide⟩ 3 (transLenTr ⟨42, by decide⟩ 3 hp))
        (rowE1 (⟨104, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨104, by decide⟩ : Fin 148) ⟨42, by decide⟩ _
      (validAt ⟨104, by decide⟩ (listedAt ⟨104, by decide⟩ hj))
      (colE1 ⟨42, by decide⟩ 3 (transLenTr ⟨42, by decide⟩ 3 hp)) T104_42
      hfix104_42 hinj104_42 hcardT104_42
      (fun i => conj_mem_of_fixedPoints _ _ (T104_42 i) (hfix104_42 i) _)
      ⟨104, by decide⟩ ⟨42, by decide⟩ _
      (Q2.validAt ⟨104, by decide⟩ (Q2.listedAt ⟨104, by decide⟩
        (alnCheck_rep ⟨104, by decide⟩ hj hq).1))
      (colE2 ⟨42, by decide⟩ 3 hp) Q2.T104_42_2 Q2.hfix104_42_2 Q2.hinj104_42_2
      Q2.hcardT104_42_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T104_42_2 i) (Q2.hfix104_42_2 i) _)
      colCert_104_42_3.hD ?_).symm
  rw [alnId_104 j hj]


theorem leaf_104_42_4 (hp : 4 < (Q2.transData.getD 42 []).length)
    (j : Nat) (hj : j < (repChars.getD 104 []).length)
    (hq : (normIsRep.getD 104 []).getD j false = true) :
    species (Q2.reps (⟨42, by decide⟩ : Fin 148)) (colE2 ⟨42, by decide⟩ 4 hp)
        (rowE2 (⟨104, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨42, by decide⟩ : Fin 148))
        (colE1 ⟨42, by decide⟩ 4 (transLenTr ⟨42, by decide⟩ 4 hp))
        (rowE1 (⟨104, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨104, by decide⟩ : Fin 148) ⟨42, by decide⟩ _
      (validAt ⟨104, by decide⟩ (listedAt ⟨104, by decide⟩ hj))
      (colE1 ⟨42, by decide⟩ 4 (transLenTr ⟨42, by decide⟩ 4 hp)) T104_42
      hfix104_42 hinj104_42 hcardT104_42
      (fun i => conj_mem_of_fixedPoints _ _ (T104_42 i) (hfix104_42 i) _)
      ⟨104, by decide⟩ ⟨42, by decide⟩ _
      (Q2.validAt ⟨104, by decide⟩ (Q2.listedAt ⟨104, by decide⟩
        (alnCheck_rep ⟨104, by decide⟩ hj hq).1))
      (colE2 ⟨42, by decide⟩ 4 hp) Q2.T104_42_2 Q2.hfix104_42_2 Q2.hinj104_42_2
      Q2.hcardT104_42_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T104_42_2 i) (Q2.hfix104_42_2 i) _)
      colCert_104_42_4.hD ?_).symm
  rw [alnId_104 j hj]


theorem leaf_104_42_5 (hp : 5 < (Q2.transData.getD 42 []).length)
    (j : Nat) (hj : j < (repChars.getD 104 []).length)
    (hq : (normIsRep.getD 104 []).getD j false = true) :
    species (Q2.reps (⟨42, by decide⟩ : Fin 148)) (colE2 ⟨42, by decide⟩ 5 hp)
        (rowE2 (⟨104, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨42, by decide⟩ : Fin 148))
        (colE1 ⟨42, by decide⟩ 5 (transLenTr ⟨42, by decide⟩ 5 hp))
        (rowE1 (⟨104, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨104, by decide⟩ : Fin 148) ⟨42, by decide⟩ _
      (validAt ⟨104, by decide⟩ (listedAt ⟨104, by decide⟩ hj))
      (colE1 ⟨42, by decide⟩ 5 (transLenTr ⟨42, by decide⟩ 5 hp)) T104_42
      hfix104_42 hinj104_42 hcardT104_42
      (fun i => conj_mem_of_fixedPoints _ _ (T104_42 i) (hfix104_42 i) _)
      ⟨104, by decide⟩ ⟨42, by decide⟩ _
      (Q2.validAt ⟨104, by decide⟩ (Q2.listedAt ⟨104, by decide⟩
        (alnCheck_rep ⟨104, by decide⟩ hj hq).1))
      (colE2 ⟨42, by decide⟩ 5 hp) Q2.T104_42_2 Q2.hfix104_42_2 Q2.hinj104_42_2
      Q2.hcardT104_42_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T104_42_2 i) (Q2.hfix104_42_2 i) _)
      ?_).symm
  rw [show colData1 (⟨104, by decide⟩ : Fin 148)
        ((colE1 ⟨42, by decide⟩ 5 (transLenTr ⟨42, by decide⟩ 5 hp) : ↥(reps ⟨42, by decide⟩)) : Coordinate 1)
        T104_42 = colFn colCertDiv_104_42_5.D1 (m := 25) from colCertDiv_104_42_5.bind1,
    show colData2 (⟨104, by decide⟩ : Fin 148)
        ((colE2 ⟨42, by decide⟩ 5 hp : ↥(Q2.reps ⟨42, by decide⟩)) : Coordinate 2)
        Q2.T104_42_2 = colFn colCertDiv_104_42_5.D2 (m := 25) from colCertDiv_104_42_5.bind2]
  rw [alnId_104 j hj]
  exact fastcode_of_div ⟨104, by decide⟩ _ _ _
    ((alnId_104 j hj) ▸ Q2.listedAt (⟨104, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨104, by decide⟩ : Fin 148) hj hq).1) colCertDiv_104_42_5_match


theorem leaf_104_42_10 (hp : 10 < (Q2.transData.getD 42 []).length)
    (j : Nat) (hj : j < (repChars.getD 104 []).length)
    (hq : (normIsRep.getD 104 []).getD j false = true) :
    species (Q2.reps (⟨42, by decide⟩ : Fin 148)) (colE2 ⟨42, by decide⟩ 10 hp)
        (rowE2 (⟨104, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨42, by decide⟩ : Fin 148))
        (colE1 ⟨42, by decide⟩ 10 (transLenTr ⟨42, by decide⟩ 10 hp))
        (rowE1 (⟨104, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨104, by decide⟩ : Fin 148) ⟨42, by decide⟩ _
      (validAt ⟨104, by decide⟩ (listedAt ⟨104, by decide⟩ hj))
      (colE1 ⟨42, by decide⟩ 10 (transLenTr ⟨42, by decide⟩ 10 hp)) T104_42
      hfix104_42 hinj104_42 hcardT104_42
      (fun i => conj_mem_of_fixedPoints _ _ (T104_42 i) (hfix104_42 i) _)
      ⟨104, by decide⟩ ⟨42, by decide⟩ _
      (Q2.validAt ⟨104, by decide⟩ (Q2.listedAt ⟨104, by decide⟩
        (alnCheck_rep ⟨104, by decide⟩ hj hq).1))
      (colE2 ⟨42, by decide⟩ 10 hp) Q2.T104_42_2 Q2.hfix104_42_2 Q2.hinj104_42_2
      Q2.hcardT104_42_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T104_42_2 i) (Q2.hfix104_42_2 i) _)
      ?_).symm
  rw [show colData1 (⟨104, by decide⟩ : Fin 148)
        ((colE1 ⟨42, by decide⟩ 10 (transLenTr ⟨42, by decide⟩ 10 hp) : ↥(reps ⟨42, by decide⟩)) : Coordinate 1)
        T104_42 = colFn colCertDiv_104_42_10.D1 (m := 25) from colCertDiv_104_42_10.bind1,
    show colData2 (⟨104, by decide⟩ : Fin 148)
        ((colE2 ⟨42, by decide⟩ 10 hp : ↥(Q2.reps ⟨42, by decide⟩)) : Coordinate 2)
        Q2.T104_42_2 = colFn colCertDiv_104_42_10.D2 (m := 25) from colCertDiv_104_42_10.bind2]
  rw [alnId_104 j hj]
  exact fastcode_of_div ⟨104, by decide⟩ _ _ _
    ((alnId_104 j hj) ▸ Q2.listedAt (⟨104, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨104, by decide⟩ : Fin 148) hj hq).1) colCertDiv_104_42_10_match


theorem leaf_104_42_15 (hp : 15 < (Q2.transData.getD 42 []).length)
    (j : Nat) (hj : j < (repChars.getD 104 []).length)
    (hq : (normIsRep.getD 104 []).getD j false = true) :
    species (Q2.reps (⟨42, by decide⟩ : Fin 148)) (colE2 ⟨42, by decide⟩ 15 hp)
        (rowE2 (⟨104, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨42, by decide⟩ : Fin 148))
        (colE1 ⟨42, by decide⟩ 15 (transLenTr ⟨42, by decide⟩ 15 hp))
        (rowE1 (⟨104, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨104, by decide⟩ : Fin 148) ⟨42, by decide⟩ _
      (validAt ⟨104, by decide⟩ (listedAt ⟨104, by decide⟩ hj))
      (colE1 ⟨42, by decide⟩ 15 (transLenTr ⟨42, by decide⟩ 15 hp)) T104_42
      hfix104_42 hinj104_42 hcardT104_42
      (fun i => conj_mem_of_fixedPoints _ _ (T104_42 i) (hfix104_42 i) _)
      ⟨104, by decide⟩ ⟨42, by decide⟩ _
      (Q2.validAt ⟨104, by decide⟩ (Q2.listedAt ⟨104, by decide⟩
        (alnCheck_rep ⟨104, by decide⟩ hj hq).1))
      (colE2 ⟨42, by decide⟩ 15 hp) Q2.T104_42_2 Q2.hfix104_42_2 Q2.hinj104_42_2
      Q2.hcardT104_42_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T104_42_2 i) (Q2.hfix104_42_2 i) _)
      ?_).symm
  rw [show colData1 (⟨104, by decide⟩ : Fin 148)
        ((colE1 ⟨42, by decide⟩ 15 (transLenTr ⟨42, by decide⟩ 15 hp) : ↥(reps ⟨42, by decide⟩)) : Coordinate 1)
        T104_42 = colFn colCertDiv_104_42_15.D1 (m := 25) from colCertDiv_104_42_15.bind1,
    show colData2 (⟨104, by decide⟩ : Fin 148)
        ((colE2 ⟨42, by decide⟩ 15 hp : ↥(Q2.reps ⟨42, by decide⟩)) : Coordinate 2)
        Q2.T104_42_2 = colFn colCertDiv_104_42_15.D2 (m := 25) from colCertDiv_104_42_15.bind2]
  rw [alnId_104 j hj]
  exact fastcode_of_div ⟨104, by decide⟩ _ _ _
    ((alnId_104 j hj) ▸ Q2.listedAt (⟨104, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨104, by decide⟩ : Fin 148) hj hq).1) colCertDiv_104_42_15_match


theorem leaf_104_42_20 (hp : 20 < (Q2.transData.getD 42 []).length)
    (j : Nat) (hj : j < (repChars.getD 104 []).length)
    (hq : (normIsRep.getD 104 []).getD j false = true) :
    species (Q2.reps (⟨42, by decide⟩ : Fin 148)) (colE2 ⟨42, by decide⟩ 20 hp)
        (rowE2 (⟨104, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨42, by decide⟩ : Fin 148))
        (colE1 ⟨42, by decide⟩ 20 (transLenTr ⟨42, by decide⟩ 20 hp))
        (rowE1 (⟨104, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨104, by decide⟩ : Fin 148) ⟨42, by decide⟩ _
      (validAt ⟨104, by decide⟩ (listedAt ⟨104, by decide⟩ hj))
      (colE1 ⟨42, by decide⟩ 20 (transLenTr ⟨42, by decide⟩ 20 hp)) T104_42
      hfix104_42 hinj104_42 hcardT104_42
      (fun i => conj_mem_of_fixedPoints _ _ (T104_42 i) (hfix104_42 i) _)
      ⟨104, by decide⟩ ⟨42, by decide⟩ _
      (Q2.validAt ⟨104, by decide⟩ (Q2.listedAt ⟨104, by decide⟩
        (alnCheck_rep ⟨104, by decide⟩ hj hq).1))
      (colE2 ⟨42, by decide⟩ 20 hp) Q2.T104_42_2 Q2.hfix104_42_2 Q2.hinj104_42_2
      Q2.hcardT104_42_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T104_42_2 i) (Q2.hfix104_42_2 i) _)
      ?_).symm
  rw [show colData1 (⟨104, by decide⟩ : Fin 148)
        ((colE1 ⟨42, by decide⟩ 20 (transLenTr ⟨42, by decide⟩ 20 hp) : ↥(reps ⟨42, by decide⟩)) : Coordinate 1)
        T104_42 = colFn colCertDiv_104_42_20.D1 (m := 25) from colCertDiv_104_42_20.bind1,
    show colData2 (⟨104, by decide⟩ : Fin 148)
        ((colE2 ⟨42, by decide⟩ 20 hp : ↥(Q2.reps ⟨42, by decide⟩)) : Coordinate 2)
        Q2.T104_42_2 = colFn colCertDiv_104_42_20.D2 (m := 25) from colCertDiv_104_42_20.bind2]
  rw [alnId_104 j hj]
  exact fastcode_of_div ⟨104, by decide⟩ _ _ _
    ((alnId_104 j hj) ▸ Q2.listedAt (⟨104, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨104, by decide⟩ : Fin 148) hj hq).1) colCertDiv_104_42_20_match


theorem leaf_104_53_0 (hp : 0 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 104 []).length)
    (hq : (normIsRep.getD 104 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 0 hp)
        (rowE2 (⟨104, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 0 (transLenTr ⟨53, by decide⟩ 0 hp))
        (rowE1 (⟨104, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨104, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨104, by decide⟩ (listedAt ⟨104, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 0 (transLenTr ⟨53, by decide⟩ 0 hp)) T104_53
      hfix104_53 hinj104_53 hcardT104_53
      (fun i => conj_mem_of_fixedPoints _ _ (T104_53 i) (hfix104_53 i) _)
      ⟨104, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨104, by decide⟩ (Q2.listedAt ⟨104, by decide⟩
        (alnCheck_rep ⟨104, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 0 hp) Q2.T104_53_2 Q2.hfix104_53_2 Q2.hinj104_53_2
      Q2.hcardT104_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T104_53_2 i) (Q2.hfix104_53_2 i) _)
      colCert_104_53_0.hD ?_).symm
  rw [alnId_104 j hj]


theorem leaf_104_53_1 (hp : 1 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 104 []).length)
    (hq : (normIsRep.getD 104 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 1 hp)
        (rowE2 (⟨104, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 1 (transLenTr ⟨53, by decide⟩ 1 hp))
        (rowE1 (⟨104, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨104, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨104, by decide⟩ (listedAt ⟨104, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 1 (transLenTr ⟨53, by decide⟩ 1 hp)) T104_53
      hfix104_53 hinj104_53 hcardT104_53
      (fun i => conj_mem_of_fixedPoints _ _ (T104_53 i) (hfix104_53 i) _)
      ⟨104, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨104, by decide⟩ (Q2.listedAt ⟨104, by decide⟩
        (alnCheck_rep ⟨104, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 1 hp) Q2.T104_53_2 Q2.hfix104_53_2 Q2.hinj104_53_2
      Q2.hcardT104_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T104_53_2 i) (Q2.hfix104_53_2 i) _)
      colCert_104_53_1.hD ?_).symm
  rw [alnId_104 j hj]


theorem leaf_104_53_2 (hp : 2 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 104 []).length)
    (hq : (normIsRep.getD 104 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 2 hp)
        (rowE2 (⟨104, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 2 (transLenTr ⟨53, by decide⟩ 2 hp))
        (rowE1 (⟨104, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨104, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨104, by decide⟩ (listedAt ⟨104, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 2 (transLenTr ⟨53, by decide⟩ 2 hp)) T104_53
      hfix104_53 hinj104_53 hcardT104_53
      (fun i => conj_mem_of_fixedPoints _ _ (T104_53 i) (hfix104_53 i) _)
      ⟨104, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨104, by decide⟩ (Q2.listedAt ⟨104, by decide⟩
        (alnCheck_rep ⟨104, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 2 hp) Q2.T104_53_2 Q2.hfix104_53_2 Q2.hinj104_53_2
      Q2.hcardT104_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T104_53_2 i) (Q2.hfix104_53_2 i) _)
      colCert_104_53_2.hD ?_).symm
  rw [alnId_104 j hj]


theorem leaf_104_53_3 (hp : 3 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 104 []).length)
    (hq : (normIsRep.getD 104 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 3 hp)
        (rowE2 (⟨104, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 3 (transLenTr ⟨53, by decide⟩ 3 hp))
        (rowE1 (⟨104, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨104, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨104, by decide⟩ (listedAt ⟨104, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 3 (transLenTr ⟨53, by decide⟩ 3 hp)) T104_53
      hfix104_53 hinj104_53 hcardT104_53
      (fun i => conj_mem_of_fixedPoints _ _ (T104_53 i) (hfix104_53 i) _)
      ⟨104, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨104, by decide⟩ (Q2.listedAt ⟨104, by decide⟩
        (alnCheck_rep ⟨104, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 3 hp) Q2.T104_53_2 Q2.hfix104_53_2 Q2.hinj104_53_2
      Q2.hcardT104_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T104_53_2 i) (Q2.hfix104_53_2 i) _)
      colCert_104_53_3.hD ?_).symm
  rw [alnId_104 j hj]


theorem leaf_104_53_4 (hp : 4 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 104 []).length)
    (hq : (normIsRep.getD 104 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 4 hp)
        (rowE2 (⟨104, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 4 (transLenTr ⟨53, by decide⟩ 4 hp))
        (rowE1 (⟨104, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨104, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨104, by decide⟩ (listedAt ⟨104, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 4 (transLenTr ⟨53, by decide⟩ 4 hp)) T104_53
      hfix104_53 hinj104_53 hcardT104_53
      (fun i => conj_mem_of_fixedPoints _ _ (T104_53 i) (hfix104_53 i) _)
      ⟨104, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨104, by decide⟩ (Q2.listedAt ⟨104, by decide⟩
        (alnCheck_rep ⟨104, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 4 hp) Q2.T104_53_2 Q2.hfix104_53_2 Q2.hinj104_53_2
      Q2.hcardT104_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T104_53_2 i) (Q2.hfix104_53_2 i) _)
      colCert_104_53_4.hD ?_).symm
  rw [alnId_104 j hj]


theorem leaf_104_53_5 (hp : 5 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 104 []).length)
    (hq : (normIsRep.getD 104 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 5 hp)
        (rowE2 (⟨104, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 5 (transLenTr ⟨53, by decide⟩ 5 hp))
        (rowE1 (⟨104, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨104, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨104, by decide⟩ (listedAt ⟨104, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 5 (transLenTr ⟨53, by decide⟩ 5 hp)) T104_53
      hfix104_53 hinj104_53 hcardT104_53
      (fun i => conj_mem_of_fixedPoints _ _ (T104_53 i) (hfix104_53 i) _)
      ⟨104, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨104, by decide⟩ (Q2.listedAt ⟨104, by decide⟩
        (alnCheck_rep ⟨104, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 5 hp) Q2.T104_53_2 Q2.hfix104_53_2 Q2.hinj104_53_2
      Q2.hcardT104_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T104_53_2 i) (Q2.hfix104_53_2 i) _)
      colCert_104_53_5.hD ?_).symm
  rw [alnId_104 j hj]


theorem leaf_104_53_10 (hp : 10 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 104 []).length)
    (hq : (normIsRep.getD 104 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 10 hp)
        (rowE2 (⟨104, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 10 (transLenTr ⟨53, by decide⟩ 10 hp))
        (rowE1 (⟨104, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨104, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨104, by decide⟩ (listedAt ⟨104, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 10 (transLenTr ⟨53, by decide⟩ 10 hp)) T104_53
      hfix104_53 hinj104_53 hcardT104_53
      (fun i => conj_mem_of_fixedPoints _ _ (T104_53 i) (hfix104_53 i) _)
      ⟨104, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨104, by decide⟩ (Q2.listedAt ⟨104, by decide⟩
        (alnCheck_rep ⟨104, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 10 hp) Q2.T104_53_2 Q2.hfix104_53_2 Q2.hinj104_53_2
      Q2.hcardT104_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T104_53_2 i) (Q2.hfix104_53_2 i) _)
      colCert_104_53_10.hD ?_).symm
  rw [alnId_104 j hj]


theorem leaf_104_53_15 (hp : 15 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 104 []).length)
    (hq : (normIsRep.getD 104 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 15 hp)
        (rowE2 (⟨104, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 15 (transLenTr ⟨53, by decide⟩ 15 hp))
        (rowE1 (⟨104, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨104, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨104, by decide⟩ (listedAt ⟨104, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 15 (transLenTr ⟨53, by decide⟩ 15 hp)) T104_53
      hfix104_53 hinj104_53 hcardT104_53
      (fun i => conj_mem_of_fixedPoints _ _ (T104_53 i) (hfix104_53 i) _)
      ⟨104, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨104, by decide⟩ (Q2.listedAt ⟨104, by decide⟩
        (alnCheck_rep ⟨104, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 15 hp) Q2.T104_53_2 Q2.hfix104_53_2 Q2.hinj104_53_2
      Q2.hcardT104_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T104_53_2 i) (Q2.hfix104_53_2 i) _)
      colCert_104_53_15.hD ?_).symm
  rw [alnId_104 j hj]


theorem leaf_104_53_20 (hp : 20 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 104 []).length)
    (hq : (normIsRep.getD 104 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 20 hp)
        (rowE2 (⟨104, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 20 (transLenTr ⟨53, by decide⟩ 20 hp))
        (rowE1 (⟨104, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨104, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨104, by decide⟩ (listedAt ⟨104, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 20 (transLenTr ⟨53, by decide⟩ 20 hp)) T104_53
      hfix104_53 hinj104_53 hcardT104_53
      (fun i => conj_mem_of_fixedPoints _ _ (T104_53 i) (hfix104_53 i) _)
      ⟨104, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨104, by decide⟩ (Q2.listedAt ⟨104, by decide⟩
        (alnCheck_rep ⟨104, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 20 hp) Q2.T104_53_2 Q2.hfix104_53_2 Q2.hinj104_53_2
      Q2.hcardT104_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T104_53_2 i) (Q2.hfix104_53_2 i) _)
      colCert_104_53_20.hD ?_).symm
  rw [alnId_104 j hj]


theorem leaf_104_104_0 (hp : 0 < (Q2.transData.getD 104 []).length)
    (j : Nat) (hj : j < (repChars.getD 104 []).length)
    (hq : (normIsRep.getD 104 []).getD j false = true) :
    species (Q2.reps (⟨104, by decide⟩ : Fin 148)) (colE2 ⟨104, by decide⟩ 0 hp)
        (rowE2 (⟨104, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨104, by decide⟩ : Fin 148))
        (colE1 ⟨104, by decide⟩ 0 (transLenTr ⟨104, by decide⟩ 0 hp))
        (rowE1 (⟨104, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨104, by decide⟩ : Fin 148) ⟨104, by decide⟩ _
      (validAt ⟨104, by decide⟩ (listedAt ⟨104, by decide⟩ hj))
      (colE1 ⟨104, by decide⟩ 0 (transLenTr ⟨104, by decide⟩ 0 hp)) T104_104
      hfix104_104 hinj104_104 hcardT104_104
      (fun i => conj_mem_of_fixedPoints _ _ (T104_104 i) (hfix104_104 i) _)
      ⟨104, by decide⟩ ⟨104, by decide⟩ _
      (Q2.validAt ⟨104, by decide⟩ (Q2.listedAt ⟨104, by decide⟩
        (alnCheck_rep ⟨104, by decide⟩ hj hq).1))
      (colE2 ⟨104, by decide⟩ 0 hp) Q2.T104_104_2 Q2.hfix104_104_2 Q2.hinj104_104_2
      Q2.hcardT104_104_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T104_104_2 i) (Q2.hfix104_104_2 i) _)
      colCert_104_104_0.hD ?_).symm
  rw [alnId_104 j hj]


theorem leaf_104_104_1 (hp : 1 < (Q2.transData.getD 104 []).length)
    (j : Nat) (hj : j < (repChars.getD 104 []).length)
    (hq : (normIsRep.getD 104 []).getD j false = true) :
    species (Q2.reps (⟨104, by decide⟩ : Fin 148)) (colE2 ⟨104, by decide⟩ 1 hp)
        (rowE2 (⟨104, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨104, by decide⟩ : Fin 148))
        (colE1 ⟨104, by decide⟩ 1 (transLenTr ⟨104, by decide⟩ 1 hp))
        (rowE1 (⟨104, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨104, by decide⟩ : Fin 148) ⟨104, by decide⟩ _
      (validAt ⟨104, by decide⟩ (listedAt ⟨104, by decide⟩ hj))
      (colE1 ⟨104, by decide⟩ 1 (transLenTr ⟨104, by decide⟩ 1 hp)) T104_104
      hfix104_104 hinj104_104 hcardT104_104
      (fun i => conj_mem_of_fixedPoints _ _ (T104_104 i) (hfix104_104 i) _)
      ⟨104, by decide⟩ ⟨104, by decide⟩ _
      (Q2.validAt ⟨104, by decide⟩ (Q2.listedAt ⟨104, by decide⟩
        (alnCheck_rep ⟨104, by decide⟩ hj hq).1))
      (colE2 ⟨104, by decide⟩ 1 hp) Q2.T104_104_2 Q2.hfix104_104_2 Q2.hinj104_104_2
      Q2.hcardT104_104_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T104_104_2 i) (Q2.hfix104_104_2 i) _)
      colCert_104_104_1.hD ?_).symm
  rw [alnId_104 j hj]


theorem leaf_104_104_2 (hp : 2 < (Q2.transData.getD 104 []).length)
    (j : Nat) (hj : j < (repChars.getD 104 []).length)
    (hq : (normIsRep.getD 104 []).getD j false = true) :
    species (Q2.reps (⟨104, by decide⟩ : Fin 148)) (colE2 ⟨104, by decide⟩ 2 hp)
        (rowE2 (⟨104, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨104, by decide⟩ : Fin 148))
        (colE1 ⟨104, by decide⟩ 2 (transLenTr ⟨104, by decide⟩ 2 hp))
        (rowE1 (⟨104, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨104, by decide⟩ : Fin 148) ⟨104, by decide⟩ _
      (validAt ⟨104, by decide⟩ (listedAt ⟨104, by decide⟩ hj))
      (colE1 ⟨104, by decide⟩ 2 (transLenTr ⟨104, by decide⟩ 2 hp)) T104_104
      hfix104_104 hinj104_104 hcardT104_104
      (fun i => conj_mem_of_fixedPoints _ _ (T104_104 i) (hfix104_104 i) _)
      ⟨104, by decide⟩ ⟨104, by decide⟩ _
      (Q2.validAt ⟨104, by decide⟩ (Q2.listedAt ⟨104, by decide⟩
        (alnCheck_rep ⟨104, by decide⟩ hj hq).1))
      (colE2 ⟨104, by decide⟩ 2 hp) Q2.T104_104_2 Q2.hfix104_104_2 Q2.hinj104_104_2
      Q2.hcardT104_104_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T104_104_2 i) (Q2.hfix104_104_2 i) _)
      colCert_104_104_2.hD ?_).symm
  rw [alnId_104 j hj]


theorem leaf_104_104_3 (hp : 3 < (Q2.transData.getD 104 []).length)
    (j : Nat) (hj : j < (repChars.getD 104 []).length)
    (hq : (normIsRep.getD 104 []).getD j false = true) :
    species (Q2.reps (⟨104, by decide⟩ : Fin 148)) (colE2 ⟨104, by decide⟩ 3 hp)
        (rowE2 (⟨104, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨104, by decide⟩ : Fin 148))
        (colE1 ⟨104, by decide⟩ 3 (transLenTr ⟨104, by decide⟩ 3 hp))
        (rowE1 (⟨104, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨104, by decide⟩ : Fin 148) ⟨104, by decide⟩ _
      (validAt ⟨104, by decide⟩ (listedAt ⟨104, by decide⟩ hj))
      (colE1 ⟨104, by decide⟩ 3 (transLenTr ⟨104, by decide⟩ 3 hp)) T104_104
      hfix104_104 hinj104_104 hcardT104_104
      (fun i => conj_mem_of_fixedPoints _ _ (T104_104 i) (hfix104_104 i) _)
      ⟨104, by decide⟩ ⟨104, by decide⟩ _
      (Q2.validAt ⟨104, by decide⟩ (Q2.listedAt ⟨104, by decide⟩
        (alnCheck_rep ⟨104, by decide⟩ hj hq).1))
      (colE2 ⟨104, by decide⟩ 3 hp) Q2.T104_104_2 Q2.hfix104_104_2 Q2.hinj104_104_2
      Q2.hcardT104_104_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T104_104_2 i) (Q2.hfix104_104_2 i) _)
      colCert_104_104_3.hD ?_).symm
  rw [alnId_104 j hj]


theorem leaf_104_104_4 (hp : 4 < (Q2.transData.getD 104 []).length)
    (j : Nat) (hj : j < (repChars.getD 104 []).length)
    (hq : (normIsRep.getD 104 []).getD j false = true) :
    species (Q2.reps (⟨104, by decide⟩ : Fin 148)) (colE2 ⟨104, by decide⟩ 4 hp)
        (rowE2 (⟨104, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨104, by decide⟩ : Fin 148))
        (colE1 ⟨104, by decide⟩ 4 (transLenTr ⟨104, by decide⟩ 4 hp))
        (rowE1 (⟨104, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨104, by decide⟩ : Fin 148) ⟨104, by decide⟩ _
      (validAt ⟨104, by decide⟩ (listedAt ⟨104, by decide⟩ hj))
      (colE1 ⟨104, by decide⟩ 4 (transLenTr ⟨104, by decide⟩ 4 hp)) T104_104
      hfix104_104 hinj104_104 hcardT104_104
      (fun i => conj_mem_of_fixedPoints _ _ (T104_104 i) (hfix104_104 i) _)
      ⟨104, by decide⟩ ⟨104, by decide⟩ _
      (Q2.validAt ⟨104, by decide⟩ (Q2.listedAt ⟨104, by decide⟩
        (alnCheck_rep ⟨104, by decide⟩ hj hq).1))
      (colE2 ⟨104, by decide⟩ 4 hp) Q2.T104_104_2 Q2.hfix104_104_2 Q2.hinj104_104_2
      Q2.hcardT104_104_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T104_104_2 i) (Q2.hfix104_104_2 i) _)
      colCert_104_104_4.hD ?_).symm
  rw [alnId_104 j hj]


theorem leaf_104_104_5 (hp : 5 < (Q2.transData.getD 104 []).length)
    (j : Nat) (hj : j < (repChars.getD 104 []).length)
    (hq : (normIsRep.getD 104 []).getD j false = true) :
    species (Q2.reps (⟨104, by decide⟩ : Fin 148)) (colE2 ⟨104, by decide⟩ 5 hp)
        (rowE2 (⟨104, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨104, by decide⟩ : Fin 148))
        (colE1 ⟨104, by decide⟩ 5 (transLenTr ⟨104, by decide⟩ 5 hp))
        (rowE1 (⟨104, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨104, by decide⟩ : Fin 148) ⟨104, by decide⟩ _
      (validAt ⟨104, by decide⟩ (listedAt ⟨104, by decide⟩ hj))
      (colE1 ⟨104, by decide⟩ 5 (transLenTr ⟨104, by decide⟩ 5 hp)) T104_104
      hfix104_104 hinj104_104 hcardT104_104
      (fun i => conj_mem_of_fixedPoints _ _ (T104_104 i) (hfix104_104 i) _)
      ⟨104, by decide⟩ ⟨104, by decide⟩ _
      (Q2.validAt ⟨104, by decide⟩ (Q2.listedAt ⟨104, by decide⟩
        (alnCheck_rep ⟨104, by decide⟩ hj hq).1))
      (colE2 ⟨104, by decide⟩ 5 hp) Q2.T104_104_2 Q2.hfix104_104_2 Q2.hinj104_104_2
      Q2.hcardT104_104_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T104_104_2 i) (Q2.hfix104_104_2 i) _)
      colCert_104_104_5.hD ?_).symm
  rw [alnId_104 j hj]


theorem leaf_104_104_10 (hp : 10 < (Q2.transData.getD 104 []).length)
    (j : Nat) (hj : j < (repChars.getD 104 []).length)
    (hq : (normIsRep.getD 104 []).getD j false = true) :
    species (Q2.reps (⟨104, by decide⟩ : Fin 148)) (colE2 ⟨104, by decide⟩ 10 hp)
        (rowE2 (⟨104, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨104, by decide⟩ : Fin 148))
        (colE1 ⟨104, by decide⟩ 10 (transLenTr ⟨104, by decide⟩ 10 hp))
        (rowE1 (⟨104, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨104, by decide⟩ : Fin 148) ⟨104, by decide⟩ _
      (validAt ⟨104, by decide⟩ (listedAt ⟨104, by decide⟩ hj))
      (colE1 ⟨104, by decide⟩ 10 (transLenTr ⟨104, by decide⟩ 10 hp)) T104_104
      hfix104_104 hinj104_104 hcardT104_104
      (fun i => conj_mem_of_fixedPoints _ _ (T104_104 i) (hfix104_104 i) _)
      ⟨104, by decide⟩ ⟨104, by decide⟩ _
      (Q2.validAt ⟨104, by decide⟩ (Q2.listedAt ⟨104, by decide⟩
        (alnCheck_rep ⟨104, by decide⟩ hj hq).1))
      (colE2 ⟨104, by decide⟩ 10 hp) Q2.T104_104_2 Q2.hfix104_104_2 Q2.hinj104_104_2
      Q2.hcardT104_104_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T104_104_2 i) (Q2.hfix104_104_2 i) _)
      colCert_104_104_10.hD ?_).symm
  rw [alnId_104 j hj]


theorem leaf_104_104_15 (hp : 15 < (Q2.transData.getD 104 []).length)
    (j : Nat) (hj : j < (repChars.getD 104 []).length)
    (hq : (normIsRep.getD 104 []).getD j false = true) :
    species (Q2.reps (⟨104, by decide⟩ : Fin 148)) (colE2 ⟨104, by decide⟩ 15 hp)
        (rowE2 (⟨104, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨104, by decide⟩ : Fin 148))
        (colE1 ⟨104, by decide⟩ 15 (transLenTr ⟨104, by decide⟩ 15 hp))
        (rowE1 (⟨104, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨104, by decide⟩ : Fin 148) ⟨104, by decide⟩ _
      (validAt ⟨104, by decide⟩ (listedAt ⟨104, by decide⟩ hj))
      (colE1 ⟨104, by decide⟩ 15 (transLenTr ⟨104, by decide⟩ 15 hp)) T104_104
      hfix104_104 hinj104_104 hcardT104_104
      (fun i => conj_mem_of_fixedPoints _ _ (T104_104 i) (hfix104_104 i) _)
      ⟨104, by decide⟩ ⟨104, by decide⟩ _
      (Q2.validAt ⟨104, by decide⟩ (Q2.listedAt ⟨104, by decide⟩
        (alnCheck_rep ⟨104, by decide⟩ hj hq).1))
      (colE2 ⟨104, by decide⟩ 15 hp) Q2.T104_104_2 Q2.hfix104_104_2 Q2.hinj104_104_2
      Q2.hcardT104_104_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T104_104_2 i) (Q2.hfix104_104_2 i) _)
      colCert_104_104_15.hD ?_).symm
  rw [alnId_104 j hj]


theorem leaf_104_104_20 (hp : 20 < (Q2.transData.getD 104 []).length)
    (j : Nat) (hj : j < (repChars.getD 104 []).length)
    (hq : (normIsRep.getD 104 []).getD j false = true) :
    species (Q2.reps (⟨104, by decide⟩ : Fin 148)) (colE2 ⟨104, by decide⟩ 20 hp)
        (rowE2 (⟨104, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨104, by decide⟩ : Fin 148))
        (colE1 ⟨104, by decide⟩ 20 (transLenTr ⟨104, by decide⟩ 20 hp))
        (rowE1 (⟨104, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨104, by decide⟩ : Fin 148) ⟨104, by decide⟩ _
      (validAt ⟨104, by decide⟩ (listedAt ⟨104, by decide⟩ hj))
      (colE1 ⟨104, by decide⟩ 20 (transLenTr ⟨104, by decide⟩ 20 hp)) T104_104
      hfix104_104 hinj104_104 hcardT104_104
      (fun i => conj_mem_of_fixedPoints _ _ (T104_104 i) (hfix104_104 i) _)
      ⟨104, by decide⟩ ⟨104, by decide⟩ _
      (Q2.validAt ⟨104, by decide⟩ (Q2.listedAt ⟨104, by decide⟩
        (alnCheck_rep ⟨104, by decide⟩ hj hq).1))
      (colE2 ⟨104, by decide⟩ 20 hp) Q2.T104_104_2 Q2.hfix104_104_2 Q2.hinj104_104_2
      Q2.hcardT104_104_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T104_104_2 i) (Q2.hfix104_104_2 i) _)
      colCert_104_104_20.hD ?_).symm
  rw [alnId_104 j hj]


theorem leaf_105_10_0 (hp : 0 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 105 []).length)
    (hq : (normIsRep.getD 105 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 0 hp)
        (rowE2 (⟨105, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 0 (transLenTr ⟨10, by decide⟩ 0 hp))
        (rowE1 (⟨105, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨105, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨105, by decide⟩ (listedAt ⟨105, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 0 (transLenTr ⟨10, by decide⟩ 0 hp)) T105_10
      hfix105_10 hinj105_10 hcardT105_10
      (fun i => conj_mem_of_fixedPoints _ _ (T105_10 i) (hfix105_10 i) _)
      ⟨105, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨105, by decide⟩ (Q2.listedAt ⟨105, by decide⟩
        (alnCheck_rep ⟨105, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 0 hp) Q2.T105_10_2 Q2.hfix105_10_2 Q2.hinj105_10_2
      Q2.hcardT105_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T105_10_2 i) (Q2.hfix105_10_2 i) _)
      ?_).symm
  rw [show colData1 (⟨105, by decide⟩ : Fin 148)
        ((colE1 ⟨10, by decide⟩ 0 (transLenTr ⟨10, by decide⟩ 0 hp) : ↥(reps ⟨10, by decide⟩)) : Coordinate 1)
        T105_10 = colFn colCert_105_10_0.D (m := 25) from colCert_105_10_0.bind1,
    show colData2 (⟨105, by decide⟩ : Fin 148)
        ((colE2 ⟨10, by decide⟩ 0 hp : ↥(Q2.reps ⟨10, by decide⟩)) : Coordinate 2)
        Q2.T105_10_2 = colFn colCert_105_10_0.D (m := 25) from colCert_105_10_0.bind2]
  exact alnAll_105_10_0 j hj hq

theorem leaf_105_10_1 (hp : 1 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 105 []).length)
    (hq : (normIsRep.getD 105 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 1 hp)
        (rowE2 (⟨105, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 1 (transLenTr ⟨10, by decide⟩ 1 hp))
        (rowE1 (⟨105, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨105, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨105, by decide⟩ (listedAt ⟨105, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 1 (transLenTr ⟨10, by decide⟩ 1 hp)) T105_10
      hfix105_10 hinj105_10 hcardT105_10
      (fun i => conj_mem_of_fixedPoints _ _ (T105_10 i) (hfix105_10 i) _)
      ⟨105, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨105, by decide⟩ (Q2.listedAt ⟨105, by decide⟩
        (alnCheck_rep ⟨105, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 1 hp) Q2.T105_10_2 Q2.hfix105_10_2 Q2.hinj105_10_2
      Q2.hcardT105_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T105_10_2 i) (Q2.hfix105_10_2 i) _)
      ?_).symm
  rw [show colData1 (⟨105, by decide⟩ : Fin 148)
        ((colE1 ⟨10, by decide⟩ 1 (transLenTr ⟨10, by decide⟩ 1 hp) : ↥(reps ⟨10, by decide⟩)) : Coordinate 1)
        T105_10 = colFn colCert_105_10_1.D (m := 25) from colCert_105_10_1.bind1,
    show colData2 (⟨105, by decide⟩ : Fin 148)
        ((colE2 ⟨10, by decide⟩ 1 hp : ↥(Q2.reps ⟨10, by decide⟩)) : Coordinate 2)
        Q2.T105_10_2 = colFn colCert_105_10_1.D (m := 25) from colCert_105_10_1.bind2]
  exact alnAll_105_10_1 j hj hq

theorem leaf_105_10_2 (hp : 2 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 105 []).length)
    (hq : (normIsRep.getD 105 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 2 hp)
        (rowE2 (⟨105, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 2 (transLenTr ⟨10, by decide⟩ 2 hp))
        (rowE1 (⟨105, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨105, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨105, by decide⟩ (listedAt ⟨105, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 2 (transLenTr ⟨10, by decide⟩ 2 hp)) T105_10
      hfix105_10 hinj105_10 hcardT105_10
      (fun i => conj_mem_of_fixedPoints _ _ (T105_10 i) (hfix105_10 i) _)
      ⟨105, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨105, by decide⟩ (Q2.listedAt ⟨105, by decide⟩
        (alnCheck_rep ⟨105, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 2 hp) Q2.T105_10_2 Q2.hfix105_10_2 Q2.hinj105_10_2
      Q2.hcardT105_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T105_10_2 i) (Q2.hfix105_10_2 i) _)
      ?_).symm
  rw [show colData1 (⟨105, by decide⟩ : Fin 148)
        ((colE1 ⟨10, by decide⟩ 2 (transLenTr ⟨10, by decide⟩ 2 hp) : ↥(reps ⟨10, by decide⟩)) : Coordinate 1)
        T105_10 = colFn colCert_105_10_2.D (m := 25) from colCert_105_10_2.bind1,
    show colData2 (⟨105, by decide⟩ : Fin 148)
        ((colE2 ⟨10, by decide⟩ 2 hp : ↥(Q2.reps ⟨10, by decide⟩)) : Coordinate 2)
        Q2.T105_10_2 = colFn colCert_105_10_2.D (m := 25) from colCert_105_10_2.bind2]
  exact alnAll_105_10_2 j hj hq

theorem leaf_105_10_3 (hp : 3 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 105 []).length)
    (hq : (normIsRep.getD 105 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 3 hp)
        (rowE2 (⟨105, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 3 (transLenTr ⟨10, by decide⟩ 3 hp))
        (rowE1 (⟨105, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨105, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨105, by decide⟩ (listedAt ⟨105, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 3 (transLenTr ⟨10, by decide⟩ 3 hp)) T105_10
      hfix105_10 hinj105_10 hcardT105_10
      (fun i => conj_mem_of_fixedPoints _ _ (T105_10 i) (hfix105_10 i) _)
      ⟨105, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨105, by decide⟩ (Q2.listedAt ⟨105, by decide⟩
        (alnCheck_rep ⟨105, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 3 hp) Q2.T105_10_2 Q2.hfix105_10_2 Q2.hinj105_10_2
      Q2.hcardT105_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T105_10_2 i) (Q2.hfix105_10_2 i) _)
      ?_).symm
  rw [show colData1 (⟨105, by decide⟩ : Fin 148)
        ((colE1 ⟨10, by decide⟩ 3 (transLenTr ⟨10, by decide⟩ 3 hp) : ↥(reps ⟨10, by decide⟩)) : Coordinate 1)
        T105_10 = colFn colCert_105_10_3.D (m := 25) from colCert_105_10_3.bind1,
    show colData2 (⟨105, by decide⟩ : Fin 148)
        ((colE2 ⟨10, by decide⟩ 3 hp : ↥(Q2.reps ⟨10, by decide⟩)) : Coordinate 2)
        Q2.T105_10_2 = colFn colCert_105_10_3.D (m := 25) from colCert_105_10_3.bind2]
  exact alnAll_105_10_3 j hj hq

theorem leaf_105_10_4 (hp : 4 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 105 []).length)
    (hq : (normIsRep.getD 105 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 4 hp)
        (rowE2 (⟨105, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 4 (transLenTr ⟨10, by decide⟩ 4 hp))
        (rowE1 (⟨105, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨105, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨105, by decide⟩ (listedAt ⟨105, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 4 (transLenTr ⟨10, by decide⟩ 4 hp)) T105_10
      hfix105_10 hinj105_10 hcardT105_10
      (fun i => conj_mem_of_fixedPoints _ _ (T105_10 i) (hfix105_10 i) _)
      ⟨105, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨105, by decide⟩ (Q2.listedAt ⟨105, by decide⟩
        (alnCheck_rep ⟨105, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 4 hp) Q2.T105_10_2 Q2.hfix105_10_2 Q2.hinj105_10_2
      Q2.hcardT105_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T105_10_2 i) (Q2.hfix105_10_2 i) _)
      ?_).symm
  rw [show colData1 (⟨105, by decide⟩ : Fin 148)
        ((colE1 ⟨10, by decide⟩ 4 (transLenTr ⟨10, by decide⟩ 4 hp) : ↥(reps ⟨10, by decide⟩)) : Coordinate 1)
        T105_10 = colFn colCert_105_10_4.D (m := 25) from colCert_105_10_4.bind1,
    show colData2 (⟨105, by decide⟩ : Fin 148)
        ((colE2 ⟨10, by decide⟩ 4 hp : ↥(Q2.reps ⟨10, by decide⟩)) : Coordinate 2)
        Q2.T105_10_2 = colFn colCert_105_10_4.D (m := 25) from colCert_105_10_4.bind2]
  exact alnAll_105_10_4 j hj hq

theorem leaf_105_12_0 (hp : 0 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 105 []).length)
    (hq : (normIsRep.getD 105 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 0 hp)
        (rowE2 (⟨105, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp))
        (rowE1 (⟨105, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨105, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨105, by decide⟩ (listedAt ⟨105, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp)) T105_12
      hfix105_12 hinj105_12 hcardT105_12
      (fun i => conj_mem_of_fixedPoints _ _ (T105_12 i) (hfix105_12 i) _)
      ⟨105, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨105, by decide⟩ (Q2.listedAt ⟨105, by decide⟩
        (alnCheck_rep ⟨105, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 0 hp) Q2.T105_12_2 Q2.hfix105_12_2 Q2.hinj105_12_2
      Q2.hcardT105_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T105_12_2 i) (Q2.hfix105_12_2 i) _)
      ?_).symm
  rw [show colData1 (⟨105, by decide⟩ : Fin 148)
        ((colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp) : ↥(reps ⟨12, by decide⟩)) : Coordinate 1)
        T105_12 = colFn colCert_105_12_0.D (m := 25) from colCert_105_12_0.bind1,
    show colData2 (⟨105, by decide⟩ : Fin 148)
        ((colE2 ⟨12, by decide⟩ 0 hp : ↥(Q2.reps ⟨12, by decide⟩)) : Coordinate 2)
        Q2.T105_12_2 = colFn colCert_105_12_0.D (m := 25) from colCert_105_12_0.bind2]
  exact alnAll_105_12_0 j hj hq

theorem leaf_105_12_1 (hp : 1 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 105 []).length)
    (hq : (normIsRep.getD 105 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 1 hp)
        (rowE2 (⟨105, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp))
        (rowE1 (⟨105, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨105, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨105, by decide⟩ (listedAt ⟨105, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp)) T105_12
      hfix105_12 hinj105_12 hcardT105_12
      (fun i => conj_mem_of_fixedPoints _ _ (T105_12 i) (hfix105_12 i) _)
      ⟨105, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨105, by decide⟩ (Q2.listedAt ⟨105, by decide⟩
        (alnCheck_rep ⟨105, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 1 hp) Q2.T105_12_2 Q2.hfix105_12_2 Q2.hinj105_12_2
      Q2.hcardT105_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T105_12_2 i) (Q2.hfix105_12_2 i) _)
      ?_).symm
  rw [show colData1 (⟨105, by decide⟩ : Fin 148)
        ((colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp) : ↥(reps ⟨12, by decide⟩)) : Coordinate 1)
        T105_12 = colFn colCert_105_12_1.D (m := 25) from colCert_105_12_1.bind1,
    show colData2 (⟨105, by decide⟩ : Fin 148)
        ((colE2 ⟨12, by decide⟩ 1 hp : ↥(Q2.reps ⟨12, by decide⟩)) : Coordinate 2)
        Q2.T105_12_2 = colFn colCert_105_12_1.D (m := 25) from colCert_105_12_1.bind2]
  exact alnAll_105_12_1 j hj hq

theorem leaf_105_12_2 (hp : 2 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 105 []).length)
    (hq : (normIsRep.getD 105 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 2 hp)
        (rowE2 (⟨105, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp))
        (rowE1 (⟨105, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨105, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨105, by decide⟩ (listedAt ⟨105, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp)) T105_12
      hfix105_12 hinj105_12 hcardT105_12
      (fun i => conj_mem_of_fixedPoints _ _ (T105_12 i) (hfix105_12 i) _)
      ⟨105, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨105, by decide⟩ (Q2.listedAt ⟨105, by decide⟩
        (alnCheck_rep ⟨105, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 2 hp) Q2.T105_12_2 Q2.hfix105_12_2 Q2.hinj105_12_2
      Q2.hcardT105_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T105_12_2 i) (Q2.hfix105_12_2 i) _)
      ?_).symm
  rw [show colData1 (⟨105, by decide⟩ : Fin 148)
        ((colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp) : ↥(reps ⟨12, by decide⟩)) : Coordinate 1)
        T105_12 = colFn colCert_105_12_2.D (m := 25) from colCert_105_12_2.bind1,
    show colData2 (⟨105, by decide⟩ : Fin 148)
        ((colE2 ⟨12, by decide⟩ 2 hp : ↥(Q2.reps ⟨12, by decide⟩)) : Coordinate 2)
        Q2.T105_12_2 = colFn colCert_105_12_2.D (m := 25) from colCert_105_12_2.bind2]
  exact alnAll_105_12_2 j hj hq

theorem leaf_105_12_3 (hp : 3 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 105 []).length)
    (hq : (normIsRep.getD 105 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 3 hp)
        (rowE2 (⟨105, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp))
        (rowE1 (⟨105, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨105, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨105, by decide⟩ (listedAt ⟨105, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp)) T105_12
      hfix105_12 hinj105_12 hcardT105_12
      (fun i => conj_mem_of_fixedPoints _ _ (T105_12 i) (hfix105_12 i) _)
      ⟨105, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨105, by decide⟩ (Q2.listedAt ⟨105, by decide⟩
        (alnCheck_rep ⟨105, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 3 hp) Q2.T105_12_2 Q2.hfix105_12_2 Q2.hinj105_12_2
      Q2.hcardT105_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T105_12_2 i) (Q2.hfix105_12_2 i) _)
      ?_).symm
  rw [show colData1 (⟨105, by decide⟩ : Fin 148)
        ((colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp) : ↥(reps ⟨12, by decide⟩)) : Coordinate 1)
        T105_12 = colFn colCert_105_12_3.D (m := 25) from colCert_105_12_3.bind1,
    show colData2 (⟨105, by decide⟩ : Fin 148)
        ((colE2 ⟨12, by decide⟩ 3 hp : ↥(Q2.reps ⟨12, by decide⟩)) : Coordinate 2)
        Q2.T105_12_2 = colFn colCert_105_12_3.D (m := 25) from colCert_105_12_3.bind2]
  exact alnAll_105_12_3 j hj hq

theorem leaf_105_12_4 (hp : 4 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 105 []).length)
    (hq : (normIsRep.getD 105 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 4 hp)
        (rowE2 (⟨105, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp))
        (rowE1 (⟨105, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨105, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨105, by decide⟩ (listedAt ⟨105, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp)) T105_12
      hfix105_12 hinj105_12 hcardT105_12
      (fun i => conj_mem_of_fixedPoints _ _ (T105_12 i) (hfix105_12 i) _)
      ⟨105, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨105, by decide⟩ (Q2.listedAt ⟨105, by decide⟩
        (alnCheck_rep ⟨105, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 4 hp) Q2.T105_12_2 Q2.hfix105_12_2 Q2.hinj105_12_2
      Q2.hcardT105_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T105_12_2 i) (Q2.hfix105_12_2 i) _)
      ?_).symm
  rw [show colData1 (⟨105, by decide⟩ : Fin 148)
        ((colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp) : ↥(reps ⟨12, by decide⟩)) : Coordinate 1)
        T105_12 = colFn colCert_105_12_4.D (m := 25) from colCert_105_12_4.bind1,
    show colData2 (⟨105, by decide⟩ : Fin 148)
        ((colE2 ⟨12, by decide⟩ 4 hp : ↥(Q2.reps ⟨12, by decide⟩)) : Coordinate 2)
        Q2.T105_12_2 = colFn colCert_105_12_4.D (m := 25) from colCert_105_12_4.bind2]
  exact alnAll_105_12_4 j hj hq

theorem leaf_105_43_0 (hp : 0 < (Q2.transData.getD 43 []).length)
    (j : Nat) (hj : j < (repChars.getD 105 []).length)
    (hq : (normIsRep.getD 105 []).getD j false = true) :
    species (Q2.reps (⟨43, by decide⟩ : Fin 148)) (colE2 ⟨43, by decide⟩ 0 hp)
        (rowE2 (⟨105, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨43, by decide⟩ : Fin 148))
        (colE1 ⟨43, by decide⟩ 0 (transLenTr ⟨43, by decide⟩ 0 hp))
        (rowE1 (⟨105, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨105, by decide⟩ : Fin 148) ⟨43, by decide⟩ _
      (validAt ⟨105, by decide⟩ (listedAt ⟨105, by decide⟩ hj))
      (colE1 ⟨43, by decide⟩ 0 (transLenTr ⟨43, by decide⟩ 0 hp)) T105_43
      hfix105_43 hinj105_43 hcardT105_43
      (fun i => conj_mem_of_fixedPoints _ _ (T105_43 i) (hfix105_43 i) _)
      ⟨105, by decide⟩ ⟨43, by decide⟩ _
      (Q2.validAt ⟨105, by decide⟩ (Q2.listedAt ⟨105, by decide⟩
        (alnCheck_rep ⟨105, by decide⟩ hj hq).1))
      (colE2 ⟨43, by decide⟩ 0 hp) Q2.T105_43_2 Q2.hfix105_43_2 Q2.hinj105_43_2
      Q2.hcardT105_43_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T105_43_2 i) (Q2.hfix105_43_2 i) _)
      ?_).symm
  rw [show colData1 (⟨105, by decide⟩ : Fin 148)
        ((colE1 ⟨43, by decide⟩ 0 (transLenTr ⟨43, by decide⟩ 0 hp) : ↥(reps ⟨43, by decide⟩)) : Coordinate 1)
        T105_43 = colFn colCert_105_43_0.D (m := 25) from colCert_105_43_0.bind1,
    show colData2 (⟨105, by decide⟩ : Fin 148)
        ((colE2 ⟨43, by decide⟩ 0 hp : ↥(Q2.reps ⟨43, by decide⟩)) : Coordinate 2)
        Q2.T105_43_2 = colFn colCert_105_43_0.D (m := 25) from colCert_105_43_0.bind2]
  exact alnAll_105_43_0 j hj hq

theorem leaf_105_43_1 (hp : 1 < (Q2.transData.getD 43 []).length)
    (j : Nat) (hj : j < (repChars.getD 105 []).length)
    (hq : (normIsRep.getD 105 []).getD j false = true) :
    species (Q2.reps (⟨43, by decide⟩ : Fin 148)) (colE2 ⟨43, by decide⟩ 1 hp)
        (rowE2 (⟨105, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨43, by decide⟩ : Fin 148))
        (colE1 ⟨43, by decide⟩ 1 (transLenTr ⟨43, by decide⟩ 1 hp))
        (rowE1 (⟨105, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨105, by decide⟩ : Fin 148) ⟨43, by decide⟩ _
      (validAt ⟨105, by decide⟩ (listedAt ⟨105, by decide⟩ hj))
      (colE1 ⟨43, by decide⟩ 1 (transLenTr ⟨43, by decide⟩ 1 hp)) T105_43
      hfix105_43 hinj105_43 hcardT105_43
      (fun i => conj_mem_of_fixedPoints _ _ (T105_43 i) (hfix105_43 i) _)
      ⟨105, by decide⟩ ⟨43, by decide⟩ _
      (Q2.validAt ⟨105, by decide⟩ (Q2.listedAt ⟨105, by decide⟩
        (alnCheck_rep ⟨105, by decide⟩ hj hq).1))
      (colE2 ⟨43, by decide⟩ 1 hp) Q2.T105_43_2 Q2.hfix105_43_2 Q2.hinj105_43_2
      Q2.hcardT105_43_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T105_43_2 i) (Q2.hfix105_43_2 i) _)
      ?_).symm
  rw [show colData1 (⟨105, by decide⟩ : Fin 148)
        ((colE1 ⟨43, by decide⟩ 1 (transLenTr ⟨43, by decide⟩ 1 hp) : ↥(reps ⟨43, by decide⟩)) : Coordinate 1)
        T105_43 = colFn colCert_105_43_1.D (m := 25) from colCert_105_43_1.bind1,
    show colData2 (⟨105, by decide⟩ : Fin 148)
        ((colE2 ⟨43, by decide⟩ 1 hp : ↥(Q2.reps ⟨43, by decide⟩)) : Coordinate 2)
        Q2.T105_43_2 = colFn colCert_105_43_1.D (m := 25) from colCert_105_43_1.bind2]
  exact alnAll_105_43_1 j hj hq

theorem leaf_105_43_2 (hp : 2 < (Q2.transData.getD 43 []).length)
    (j : Nat) (hj : j < (repChars.getD 105 []).length)
    (hq : (normIsRep.getD 105 []).getD j false = true) :
    species (Q2.reps (⟨43, by decide⟩ : Fin 148)) (colE2 ⟨43, by decide⟩ 2 hp)
        (rowE2 (⟨105, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨43, by decide⟩ : Fin 148))
        (colE1 ⟨43, by decide⟩ 2 (transLenTr ⟨43, by decide⟩ 2 hp))
        (rowE1 (⟨105, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨105, by decide⟩ : Fin 148) ⟨43, by decide⟩ _
      (validAt ⟨105, by decide⟩ (listedAt ⟨105, by decide⟩ hj))
      (colE1 ⟨43, by decide⟩ 2 (transLenTr ⟨43, by decide⟩ 2 hp)) T105_43
      hfix105_43 hinj105_43 hcardT105_43
      (fun i => conj_mem_of_fixedPoints _ _ (T105_43 i) (hfix105_43 i) _)
      ⟨105, by decide⟩ ⟨43, by decide⟩ _
      (Q2.validAt ⟨105, by decide⟩ (Q2.listedAt ⟨105, by decide⟩
        (alnCheck_rep ⟨105, by decide⟩ hj hq).1))
      (colE2 ⟨43, by decide⟩ 2 hp) Q2.T105_43_2 Q2.hfix105_43_2 Q2.hinj105_43_2
      Q2.hcardT105_43_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T105_43_2 i) (Q2.hfix105_43_2 i) _)
      ?_).symm
  rw [show colData1 (⟨105, by decide⟩ : Fin 148)
        ((colE1 ⟨43, by decide⟩ 2 (transLenTr ⟨43, by decide⟩ 2 hp) : ↥(reps ⟨43, by decide⟩)) : Coordinate 1)
        T105_43 = colFn colCert_105_43_2.D (m := 25) from colCert_105_43_2.bind1,
    show colData2 (⟨105, by decide⟩ : Fin 148)
        ((colE2 ⟨43, by decide⟩ 2 hp : ↥(Q2.reps ⟨43, by decide⟩)) : Coordinate 2)
        Q2.T105_43_2 = colFn colCert_105_43_2.D (m := 25) from colCert_105_43_2.bind2]
  exact alnAll_105_43_2 j hj hq

theorem leaf_105_43_3 (hp : 3 < (Q2.transData.getD 43 []).length)
    (j : Nat) (hj : j < (repChars.getD 105 []).length)
    (hq : (normIsRep.getD 105 []).getD j false = true) :
    species (Q2.reps (⟨43, by decide⟩ : Fin 148)) (colE2 ⟨43, by decide⟩ 3 hp)
        (rowE2 (⟨105, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨43, by decide⟩ : Fin 148))
        (colE1 ⟨43, by decide⟩ 3 (transLenTr ⟨43, by decide⟩ 3 hp))
        (rowE1 (⟨105, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨105, by decide⟩ : Fin 148) ⟨43, by decide⟩ _
      (validAt ⟨105, by decide⟩ (listedAt ⟨105, by decide⟩ hj))
      (colE1 ⟨43, by decide⟩ 3 (transLenTr ⟨43, by decide⟩ 3 hp)) T105_43
      hfix105_43 hinj105_43 hcardT105_43
      (fun i => conj_mem_of_fixedPoints _ _ (T105_43 i) (hfix105_43 i) _)
      ⟨105, by decide⟩ ⟨43, by decide⟩ _
      (Q2.validAt ⟨105, by decide⟩ (Q2.listedAt ⟨105, by decide⟩
        (alnCheck_rep ⟨105, by decide⟩ hj hq).1))
      (colE2 ⟨43, by decide⟩ 3 hp) Q2.T105_43_2 Q2.hfix105_43_2 Q2.hinj105_43_2
      Q2.hcardT105_43_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T105_43_2 i) (Q2.hfix105_43_2 i) _)
      ?_).symm
  rw [show colData1 (⟨105, by decide⟩ : Fin 148)
        ((colE1 ⟨43, by decide⟩ 3 (transLenTr ⟨43, by decide⟩ 3 hp) : ↥(reps ⟨43, by decide⟩)) : Coordinate 1)
        T105_43 = colFn colCert_105_43_3.D (m := 25) from colCert_105_43_3.bind1,
    show colData2 (⟨105, by decide⟩ : Fin 148)
        ((colE2 ⟨43, by decide⟩ 3 hp : ↥(Q2.reps ⟨43, by decide⟩)) : Coordinate 2)
        Q2.T105_43_2 = colFn colCert_105_43_3.D (m := 25) from colCert_105_43_3.bind2]
  exact alnAll_105_43_3 j hj hq

theorem leaf_105_43_4 (hp : 4 < (Q2.transData.getD 43 []).length)
    (j : Nat) (hj : j < (repChars.getD 105 []).length)
    (hq : (normIsRep.getD 105 []).getD j false = true) :
    species (Q2.reps (⟨43, by decide⟩ : Fin 148)) (colE2 ⟨43, by decide⟩ 4 hp)
        (rowE2 (⟨105, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨43, by decide⟩ : Fin 148))
        (colE1 ⟨43, by decide⟩ 4 (transLenTr ⟨43, by decide⟩ 4 hp))
        (rowE1 (⟨105, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨105, by decide⟩ : Fin 148) ⟨43, by decide⟩ _
      (validAt ⟨105, by decide⟩ (listedAt ⟨105, by decide⟩ hj))
      (colE1 ⟨43, by decide⟩ 4 (transLenTr ⟨43, by decide⟩ 4 hp)) T105_43
      hfix105_43 hinj105_43 hcardT105_43
      (fun i => conj_mem_of_fixedPoints _ _ (T105_43 i) (hfix105_43 i) _)
      ⟨105, by decide⟩ ⟨43, by decide⟩ _
      (Q2.validAt ⟨105, by decide⟩ (Q2.listedAt ⟨105, by decide⟩
        (alnCheck_rep ⟨105, by decide⟩ hj hq).1))
      (colE2 ⟨43, by decide⟩ 4 hp) Q2.T105_43_2 Q2.hfix105_43_2 Q2.hinj105_43_2
      Q2.hcardT105_43_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T105_43_2 i) (Q2.hfix105_43_2 i) _)
      ?_).symm
  rw [show colData1 (⟨105, by decide⟩ : Fin 148)
        ((colE1 ⟨43, by decide⟩ 4 (transLenTr ⟨43, by decide⟩ 4 hp) : ↥(reps ⟨43, by decide⟩)) : Coordinate 1)
        T105_43 = colFn colCert_105_43_4.D (m := 25) from colCert_105_43_4.bind1,
    show colData2 (⟨105, by decide⟩ : Fin 148)
        ((colE2 ⟨43, by decide⟩ 4 hp : ↥(Q2.reps ⟨43, by decide⟩)) : Coordinate 2)
        Q2.T105_43_2 = colFn colCert_105_43_4.D (m := 25) from colCert_105_43_4.bind2]
  exact alnAll_105_43_4 j hj hq

theorem leaf_105_43_5 (hp : 5 < (Q2.transData.getD 43 []).length)
    (j : Nat) (hj : j < (repChars.getD 105 []).length)
    (hq : (normIsRep.getD 105 []).getD j false = true) :
    species (Q2.reps (⟨43, by decide⟩ : Fin 148)) (colE2 ⟨43, by decide⟩ 5 hp)
        (rowE2 (⟨105, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨43, by decide⟩ : Fin 148))
        (colE1 ⟨43, by decide⟩ 5 (transLenTr ⟨43, by decide⟩ 5 hp))
        (rowE1 (⟨105, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨105, by decide⟩ : Fin 148) ⟨43, by decide⟩ _
      (validAt ⟨105, by decide⟩ (listedAt ⟨105, by decide⟩ hj))
      (colE1 ⟨43, by decide⟩ 5 (transLenTr ⟨43, by decide⟩ 5 hp)) T105_43
      hfix105_43 hinj105_43 hcardT105_43
      (fun i => conj_mem_of_fixedPoints _ _ (T105_43 i) (hfix105_43 i) _)
      ⟨105, by decide⟩ ⟨43, by decide⟩ _
      (Q2.validAt ⟨105, by decide⟩ (Q2.listedAt ⟨105, by decide⟩
        (alnCheck_rep ⟨105, by decide⟩ hj hq).1))
      (colE2 ⟨43, by decide⟩ 5 hp) Q2.T105_43_2 Q2.hfix105_43_2 Q2.hinj105_43_2
      Q2.hcardT105_43_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T105_43_2 i) (Q2.hfix105_43_2 i) _)
      ?_).symm
  rw [show colData1 (⟨105, by decide⟩ : Fin 148)
        ((colE1 ⟨43, by decide⟩ 5 (transLenTr ⟨43, by decide⟩ 5 hp) : ↥(reps ⟨43, by decide⟩)) : Coordinate 1)
        T105_43 = colFn colCertDiv_105_43_5.D1 (m := 25) from colCertDiv_105_43_5.bind1,
    show colData2 (⟨105, by decide⟩ : Fin 148)
        ((colE2 ⟨43, by decide⟩ 5 hp : ↥(Q2.reps ⟨43, by decide⟩)) : Coordinate 2)
        Q2.T105_43_2 = colFn colCertDiv_105_43_5.D2 (m := 25) from colCertDiv_105_43_5.bind2]
  exact alnAll_105_43_5 j hj hq

theorem leaf_105_43_10 (hp : 10 < (Q2.transData.getD 43 []).length)
    (j : Nat) (hj : j < (repChars.getD 105 []).length)
    (hq : (normIsRep.getD 105 []).getD j false = true) :
    species (Q2.reps (⟨43, by decide⟩ : Fin 148)) (colE2 ⟨43, by decide⟩ 10 hp)
        (rowE2 (⟨105, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨43, by decide⟩ : Fin 148))
        (colE1 ⟨43, by decide⟩ 10 (transLenTr ⟨43, by decide⟩ 10 hp))
        (rowE1 (⟨105, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨105, by decide⟩ : Fin 148) ⟨43, by decide⟩ _
      (validAt ⟨105, by decide⟩ (listedAt ⟨105, by decide⟩ hj))
      (colE1 ⟨43, by decide⟩ 10 (transLenTr ⟨43, by decide⟩ 10 hp)) T105_43
      hfix105_43 hinj105_43 hcardT105_43
      (fun i => conj_mem_of_fixedPoints _ _ (T105_43 i) (hfix105_43 i) _)
      ⟨105, by decide⟩ ⟨43, by decide⟩ _
      (Q2.validAt ⟨105, by decide⟩ (Q2.listedAt ⟨105, by decide⟩
        (alnCheck_rep ⟨105, by decide⟩ hj hq).1))
      (colE2 ⟨43, by decide⟩ 10 hp) Q2.T105_43_2 Q2.hfix105_43_2 Q2.hinj105_43_2
      Q2.hcardT105_43_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T105_43_2 i) (Q2.hfix105_43_2 i) _)
      ?_).symm
  rw [show colData1 (⟨105, by decide⟩ : Fin 148)
        ((colE1 ⟨43, by decide⟩ 10 (transLenTr ⟨43, by decide⟩ 10 hp) : ↥(reps ⟨43, by decide⟩)) : Coordinate 1)
        T105_43 = colFn colCertDiv_105_43_10.D1 (m := 25) from colCertDiv_105_43_10.bind1,
    show colData2 (⟨105, by decide⟩ : Fin 148)
        ((colE2 ⟨43, by decide⟩ 10 hp : ↥(Q2.reps ⟨43, by decide⟩)) : Coordinate 2)
        Q2.T105_43_2 = colFn colCertDiv_105_43_10.D2 (m := 25) from colCertDiv_105_43_10.bind2]
  exact alnAll_105_43_10 j hj hq

theorem leaf_105_43_15 (hp : 15 < (Q2.transData.getD 43 []).length)
    (j : Nat) (hj : j < (repChars.getD 105 []).length)
    (hq : (normIsRep.getD 105 []).getD j false = true) :
    species (Q2.reps (⟨43, by decide⟩ : Fin 148)) (colE2 ⟨43, by decide⟩ 15 hp)
        (rowE2 (⟨105, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨43, by decide⟩ : Fin 148))
        (colE1 ⟨43, by decide⟩ 15 (transLenTr ⟨43, by decide⟩ 15 hp))
        (rowE1 (⟨105, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨105, by decide⟩ : Fin 148) ⟨43, by decide⟩ _
      (validAt ⟨105, by decide⟩ (listedAt ⟨105, by decide⟩ hj))
      (colE1 ⟨43, by decide⟩ 15 (transLenTr ⟨43, by decide⟩ 15 hp)) T105_43
      hfix105_43 hinj105_43 hcardT105_43
      (fun i => conj_mem_of_fixedPoints _ _ (T105_43 i) (hfix105_43 i) _)
      ⟨105, by decide⟩ ⟨43, by decide⟩ _
      (Q2.validAt ⟨105, by decide⟩ (Q2.listedAt ⟨105, by decide⟩
        (alnCheck_rep ⟨105, by decide⟩ hj hq).1))
      (colE2 ⟨43, by decide⟩ 15 hp) Q2.T105_43_2 Q2.hfix105_43_2 Q2.hinj105_43_2
      Q2.hcardT105_43_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T105_43_2 i) (Q2.hfix105_43_2 i) _)
      ?_).symm
  rw [show colData1 (⟨105, by decide⟩ : Fin 148)
        ((colE1 ⟨43, by decide⟩ 15 (transLenTr ⟨43, by decide⟩ 15 hp) : ↥(reps ⟨43, by decide⟩)) : Coordinate 1)
        T105_43 = colFn colCertDiv_105_43_15.D1 (m := 25) from colCertDiv_105_43_15.bind1,
    show colData2 (⟨105, by decide⟩ : Fin 148)
        ((colE2 ⟨43, by decide⟩ 15 hp : ↥(Q2.reps ⟨43, by decide⟩)) : Coordinate 2)
        Q2.T105_43_2 = colFn colCertDiv_105_43_15.D2 (m := 25) from colCertDiv_105_43_15.bind2]
  exact alnAll_105_43_15 j hj hq

theorem leaf_105_43_20 (hp : 20 < (Q2.transData.getD 43 []).length)
    (j : Nat) (hj : j < (repChars.getD 105 []).length)
    (hq : (normIsRep.getD 105 []).getD j false = true) :
    species (Q2.reps (⟨43, by decide⟩ : Fin 148)) (colE2 ⟨43, by decide⟩ 20 hp)
        (rowE2 (⟨105, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨43, by decide⟩ : Fin 148))
        (colE1 ⟨43, by decide⟩ 20 (transLenTr ⟨43, by decide⟩ 20 hp))
        (rowE1 (⟨105, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨105, by decide⟩ : Fin 148) ⟨43, by decide⟩ _
      (validAt ⟨105, by decide⟩ (listedAt ⟨105, by decide⟩ hj))
      (colE1 ⟨43, by decide⟩ 20 (transLenTr ⟨43, by decide⟩ 20 hp)) T105_43
      hfix105_43 hinj105_43 hcardT105_43
      (fun i => conj_mem_of_fixedPoints _ _ (T105_43 i) (hfix105_43 i) _)
      ⟨105, by decide⟩ ⟨43, by decide⟩ _
      (Q2.validAt ⟨105, by decide⟩ (Q2.listedAt ⟨105, by decide⟩
        (alnCheck_rep ⟨105, by decide⟩ hj hq).1))
      (colE2 ⟨43, by decide⟩ 20 hp) Q2.T105_43_2 Q2.hfix105_43_2 Q2.hinj105_43_2
      Q2.hcardT105_43_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T105_43_2 i) (Q2.hfix105_43_2 i) _)
      ?_).symm
  rw [show colData1 (⟨105, by decide⟩ : Fin 148)
        ((colE1 ⟨43, by decide⟩ 20 (transLenTr ⟨43, by decide⟩ 20 hp) : ↥(reps ⟨43, by decide⟩)) : Coordinate 1)
        T105_43 = colFn colCertDiv_105_43_20.D1 (m := 25) from colCertDiv_105_43_20.bind1,
    show colData2 (⟨105, by decide⟩ : Fin 148)
        ((colE2 ⟨43, by decide⟩ 20 hp : ↥(Q2.reps ⟨43, by decide⟩)) : Coordinate 2)
        Q2.T105_43_2 = colFn colCertDiv_105_43_20.D2 (m := 25) from colCertDiv_105_43_20.bind2]
  exact alnAll_105_43_20 j hj hq

theorem leaf_105_53_0 (hp : 0 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 105 []).length)
    (hq : (normIsRep.getD 105 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 0 hp)
        (rowE2 (⟨105, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 0 (transLenTr ⟨53, by decide⟩ 0 hp))
        (rowE1 (⟨105, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨105, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨105, by decide⟩ (listedAt ⟨105, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 0 (transLenTr ⟨53, by decide⟩ 0 hp)) T105_53
      hfix105_53 hinj105_53 hcardT105_53
      (fun i => conj_mem_of_fixedPoints _ _ (T105_53 i) (hfix105_53 i) _)
      ⟨105, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨105, by decide⟩ (Q2.listedAt ⟨105, by decide⟩
        (alnCheck_rep ⟨105, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 0 hp) Q2.T105_53_2 Q2.hfix105_53_2 Q2.hinj105_53_2
      Q2.hcardT105_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T105_53_2 i) (Q2.hfix105_53_2 i) _)
      ?_).symm
  rw [show colData1 (⟨105, by decide⟩ : Fin 148)
        ((colE1 ⟨53, by decide⟩ 0 (transLenTr ⟨53, by decide⟩ 0 hp) : ↥(reps ⟨53, by decide⟩)) : Coordinate 1)
        T105_53 = colFn colCert_105_53_0.D (m := 25) from colCert_105_53_0.bind1,
    show colData2 (⟨105, by decide⟩ : Fin 148)
        ((colE2 ⟨53, by decide⟩ 0 hp : ↥(Q2.reps ⟨53, by decide⟩)) : Coordinate 2)
        Q2.T105_53_2 = colFn colCert_105_53_0.D (m := 25) from colCert_105_53_0.bind2]
  exact alnAll_105_53_0 j hj hq

theorem leaf_105_53_1 (hp : 1 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 105 []).length)
    (hq : (normIsRep.getD 105 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 1 hp)
        (rowE2 (⟨105, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 1 (transLenTr ⟨53, by decide⟩ 1 hp))
        (rowE1 (⟨105, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨105, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨105, by decide⟩ (listedAt ⟨105, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 1 (transLenTr ⟨53, by decide⟩ 1 hp)) T105_53
      hfix105_53 hinj105_53 hcardT105_53
      (fun i => conj_mem_of_fixedPoints _ _ (T105_53 i) (hfix105_53 i) _)
      ⟨105, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨105, by decide⟩ (Q2.listedAt ⟨105, by decide⟩
        (alnCheck_rep ⟨105, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 1 hp) Q2.T105_53_2 Q2.hfix105_53_2 Q2.hinj105_53_2
      Q2.hcardT105_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T105_53_2 i) (Q2.hfix105_53_2 i) _)
      ?_).symm
  rw [show colData1 (⟨105, by decide⟩ : Fin 148)
        ((colE1 ⟨53, by decide⟩ 1 (transLenTr ⟨53, by decide⟩ 1 hp) : ↥(reps ⟨53, by decide⟩)) : Coordinate 1)
        T105_53 = colFn colCert_105_53_1.D (m := 25) from colCert_105_53_1.bind1,
    show colData2 (⟨105, by decide⟩ : Fin 148)
        ((colE2 ⟨53, by decide⟩ 1 hp : ↥(Q2.reps ⟨53, by decide⟩)) : Coordinate 2)
        Q2.T105_53_2 = colFn colCert_105_53_1.D (m := 25) from colCert_105_53_1.bind2]
  exact alnAll_105_53_1 j hj hq

theorem leaf_105_53_2 (hp : 2 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 105 []).length)
    (hq : (normIsRep.getD 105 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 2 hp)
        (rowE2 (⟨105, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 2 (transLenTr ⟨53, by decide⟩ 2 hp))
        (rowE1 (⟨105, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨105, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨105, by decide⟩ (listedAt ⟨105, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 2 (transLenTr ⟨53, by decide⟩ 2 hp)) T105_53
      hfix105_53 hinj105_53 hcardT105_53
      (fun i => conj_mem_of_fixedPoints _ _ (T105_53 i) (hfix105_53 i) _)
      ⟨105, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨105, by decide⟩ (Q2.listedAt ⟨105, by decide⟩
        (alnCheck_rep ⟨105, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 2 hp) Q2.T105_53_2 Q2.hfix105_53_2 Q2.hinj105_53_2
      Q2.hcardT105_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T105_53_2 i) (Q2.hfix105_53_2 i) _)
      ?_).symm
  rw [show colData1 (⟨105, by decide⟩ : Fin 148)
        ((colE1 ⟨53, by decide⟩ 2 (transLenTr ⟨53, by decide⟩ 2 hp) : ↥(reps ⟨53, by decide⟩)) : Coordinate 1)
        T105_53 = colFn colCert_105_53_2.D (m := 25) from colCert_105_53_2.bind1,
    show colData2 (⟨105, by decide⟩ : Fin 148)
        ((colE2 ⟨53, by decide⟩ 2 hp : ↥(Q2.reps ⟨53, by decide⟩)) : Coordinate 2)
        Q2.T105_53_2 = colFn colCert_105_53_2.D (m := 25) from colCert_105_53_2.bind2]
  exact alnAll_105_53_2 j hj hq

theorem leaf_105_53_3 (hp : 3 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 105 []).length)
    (hq : (normIsRep.getD 105 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 3 hp)
        (rowE2 (⟨105, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 3 (transLenTr ⟨53, by decide⟩ 3 hp))
        (rowE1 (⟨105, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨105, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨105, by decide⟩ (listedAt ⟨105, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 3 (transLenTr ⟨53, by decide⟩ 3 hp)) T105_53
      hfix105_53 hinj105_53 hcardT105_53
      (fun i => conj_mem_of_fixedPoints _ _ (T105_53 i) (hfix105_53 i) _)
      ⟨105, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨105, by decide⟩ (Q2.listedAt ⟨105, by decide⟩
        (alnCheck_rep ⟨105, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 3 hp) Q2.T105_53_2 Q2.hfix105_53_2 Q2.hinj105_53_2
      Q2.hcardT105_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T105_53_2 i) (Q2.hfix105_53_2 i) _)
      ?_).symm
  rw [show colData1 (⟨105, by decide⟩ : Fin 148)
        ((colE1 ⟨53, by decide⟩ 3 (transLenTr ⟨53, by decide⟩ 3 hp) : ↥(reps ⟨53, by decide⟩)) : Coordinate 1)
        T105_53 = colFn colCert_105_53_3.D (m := 25) from colCert_105_53_3.bind1,
    show colData2 (⟨105, by decide⟩ : Fin 148)
        ((colE2 ⟨53, by decide⟩ 3 hp : ↥(Q2.reps ⟨53, by decide⟩)) : Coordinate 2)
        Q2.T105_53_2 = colFn colCert_105_53_3.D (m := 25) from colCert_105_53_3.bind2]
  exact alnAll_105_53_3 j hj hq

theorem leaf_105_53_4 (hp : 4 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 105 []).length)
    (hq : (normIsRep.getD 105 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 4 hp)
        (rowE2 (⟨105, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 4 (transLenTr ⟨53, by decide⟩ 4 hp))
        (rowE1 (⟨105, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨105, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨105, by decide⟩ (listedAt ⟨105, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 4 (transLenTr ⟨53, by decide⟩ 4 hp)) T105_53
      hfix105_53 hinj105_53 hcardT105_53
      (fun i => conj_mem_of_fixedPoints _ _ (T105_53 i) (hfix105_53 i) _)
      ⟨105, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨105, by decide⟩ (Q2.listedAt ⟨105, by decide⟩
        (alnCheck_rep ⟨105, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 4 hp) Q2.T105_53_2 Q2.hfix105_53_2 Q2.hinj105_53_2
      Q2.hcardT105_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T105_53_2 i) (Q2.hfix105_53_2 i) _)
      ?_).symm
  rw [show colData1 (⟨105, by decide⟩ : Fin 148)
        ((colE1 ⟨53, by decide⟩ 4 (transLenTr ⟨53, by decide⟩ 4 hp) : ↥(reps ⟨53, by decide⟩)) : Coordinate 1)
        T105_53 = colFn colCert_105_53_4.D (m := 25) from colCert_105_53_4.bind1,
    show colData2 (⟨105, by decide⟩ : Fin 148)
        ((colE2 ⟨53, by decide⟩ 4 hp : ↥(Q2.reps ⟨53, by decide⟩)) : Coordinate 2)
        Q2.T105_53_2 = colFn colCert_105_53_4.D (m := 25) from colCert_105_53_4.bind2]
  exact alnAll_105_53_4 j hj hq

theorem leaf_105_53_5 (hp : 5 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 105 []).length)
    (hq : (normIsRep.getD 105 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 5 hp)
        (rowE2 (⟨105, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 5 (transLenTr ⟨53, by decide⟩ 5 hp))
        (rowE1 (⟨105, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨105, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨105, by decide⟩ (listedAt ⟨105, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 5 (transLenTr ⟨53, by decide⟩ 5 hp)) T105_53
      hfix105_53 hinj105_53 hcardT105_53
      (fun i => conj_mem_of_fixedPoints _ _ (T105_53 i) (hfix105_53 i) _)
      ⟨105, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨105, by decide⟩ (Q2.listedAt ⟨105, by decide⟩
        (alnCheck_rep ⟨105, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 5 hp) Q2.T105_53_2 Q2.hfix105_53_2 Q2.hinj105_53_2
      Q2.hcardT105_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T105_53_2 i) (Q2.hfix105_53_2 i) _)
      ?_).symm
  rw [show colData1 (⟨105, by decide⟩ : Fin 148)
        ((colE1 ⟨53, by decide⟩ 5 (transLenTr ⟨53, by decide⟩ 5 hp) : ↥(reps ⟨53, by decide⟩)) : Coordinate 1)
        T105_53 = colFn colCert_105_53_5.D (m := 25) from colCert_105_53_5.bind1,
    show colData2 (⟨105, by decide⟩ : Fin 148)
        ((colE2 ⟨53, by decide⟩ 5 hp : ↥(Q2.reps ⟨53, by decide⟩)) : Coordinate 2)
        Q2.T105_53_2 = colFn colCert_105_53_5.D (m := 25) from colCert_105_53_5.bind2]
  exact alnAll_105_53_5 j hj hq

theorem leaf_105_53_10 (hp : 10 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 105 []).length)
    (hq : (normIsRep.getD 105 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 10 hp)
        (rowE2 (⟨105, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 10 (transLenTr ⟨53, by decide⟩ 10 hp))
        (rowE1 (⟨105, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨105, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨105, by decide⟩ (listedAt ⟨105, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 10 (transLenTr ⟨53, by decide⟩ 10 hp)) T105_53
      hfix105_53 hinj105_53 hcardT105_53
      (fun i => conj_mem_of_fixedPoints _ _ (T105_53 i) (hfix105_53 i) _)
      ⟨105, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨105, by decide⟩ (Q2.listedAt ⟨105, by decide⟩
        (alnCheck_rep ⟨105, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 10 hp) Q2.T105_53_2 Q2.hfix105_53_2 Q2.hinj105_53_2
      Q2.hcardT105_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T105_53_2 i) (Q2.hfix105_53_2 i) _)
      ?_).symm
  rw [show colData1 (⟨105, by decide⟩ : Fin 148)
        ((colE1 ⟨53, by decide⟩ 10 (transLenTr ⟨53, by decide⟩ 10 hp) : ↥(reps ⟨53, by decide⟩)) : Coordinate 1)
        T105_53 = colFn colCert_105_53_10.D (m := 25) from colCert_105_53_10.bind1,
    show colData2 (⟨105, by decide⟩ : Fin 148)
        ((colE2 ⟨53, by decide⟩ 10 hp : ↥(Q2.reps ⟨53, by decide⟩)) : Coordinate 2)
        Q2.T105_53_2 = colFn colCert_105_53_10.D (m := 25) from colCert_105_53_10.bind2]
  exact alnAll_105_53_10 j hj hq

theorem leaf_105_53_15 (hp : 15 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 105 []).length)
    (hq : (normIsRep.getD 105 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 15 hp)
        (rowE2 (⟨105, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 15 (transLenTr ⟨53, by decide⟩ 15 hp))
        (rowE1 (⟨105, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨105, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨105, by decide⟩ (listedAt ⟨105, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 15 (transLenTr ⟨53, by decide⟩ 15 hp)) T105_53
      hfix105_53 hinj105_53 hcardT105_53
      (fun i => conj_mem_of_fixedPoints _ _ (T105_53 i) (hfix105_53 i) _)
      ⟨105, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨105, by decide⟩ (Q2.listedAt ⟨105, by decide⟩
        (alnCheck_rep ⟨105, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 15 hp) Q2.T105_53_2 Q2.hfix105_53_2 Q2.hinj105_53_2
      Q2.hcardT105_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T105_53_2 i) (Q2.hfix105_53_2 i) _)
      ?_).symm
  rw [show colData1 (⟨105, by decide⟩ : Fin 148)
        ((colE1 ⟨53, by decide⟩ 15 (transLenTr ⟨53, by decide⟩ 15 hp) : ↥(reps ⟨53, by decide⟩)) : Coordinate 1)
        T105_53 = colFn colCert_105_53_15.D (m := 25) from colCert_105_53_15.bind1,
    show colData2 (⟨105, by decide⟩ : Fin 148)
        ((colE2 ⟨53, by decide⟩ 15 hp : ↥(Q2.reps ⟨53, by decide⟩)) : Coordinate 2)
        Q2.T105_53_2 = colFn colCert_105_53_15.D (m := 25) from colCert_105_53_15.bind2]
  exact alnAll_105_53_15 j hj hq

theorem leaf_105_53_20 (hp : 20 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 105 []).length)
    (hq : (normIsRep.getD 105 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 20 hp)
        (rowE2 (⟨105, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 20 (transLenTr ⟨53, by decide⟩ 20 hp))
        (rowE1 (⟨105, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨105, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨105, by decide⟩ (listedAt ⟨105, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 20 (transLenTr ⟨53, by decide⟩ 20 hp)) T105_53
      hfix105_53 hinj105_53 hcardT105_53
      (fun i => conj_mem_of_fixedPoints _ _ (T105_53 i) (hfix105_53 i) _)
      ⟨105, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨105, by decide⟩ (Q2.listedAt ⟨105, by decide⟩
        (alnCheck_rep ⟨105, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 20 hp) Q2.T105_53_2 Q2.hfix105_53_2 Q2.hinj105_53_2
      Q2.hcardT105_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T105_53_2 i) (Q2.hfix105_53_2 i) _)
      ?_).symm
  rw [show colData1 (⟨105, by decide⟩ : Fin 148)
        ((colE1 ⟨53, by decide⟩ 20 (transLenTr ⟨53, by decide⟩ 20 hp) : ↥(reps ⟨53, by decide⟩)) : Coordinate 1)
        T105_53 = colFn colCert_105_53_20.D (m := 25) from colCert_105_53_20.bind1,
    show colData2 (⟨105, by decide⟩ : Fin 148)
        ((colE2 ⟨53, by decide⟩ 20 hp : ↥(Q2.reps ⟨53, by decide⟩)) : Coordinate 2)
        Q2.T105_53_2 = colFn colCert_105_53_20.D (m := 25) from colCert_105_53_20.bind2]
  exact alnAll_105_53_20 j hj hq

theorem leaf_105_105_0 (hp : 0 < (Q2.transData.getD 105 []).length)
    (j : Nat) (hj : j < (repChars.getD 105 []).length)
    (hq : (normIsRep.getD 105 []).getD j false = true) :
    species (Q2.reps (⟨105, by decide⟩ : Fin 148)) (colE2 ⟨105, by decide⟩ 0 hp)
        (rowE2 (⟨105, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨105, by decide⟩ : Fin 148))
        (colE1 ⟨105, by decide⟩ 0 (transLenTr ⟨105, by decide⟩ 0 hp))
        (rowE1 (⟨105, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨105, by decide⟩ : Fin 148) ⟨105, by decide⟩ _
      (validAt ⟨105, by decide⟩ (listedAt ⟨105, by decide⟩ hj))
      (colE1 ⟨105, by decide⟩ 0 (transLenTr ⟨105, by decide⟩ 0 hp)) T105_105
      hfix105_105 hinj105_105 hcardT105_105
      (fun i => conj_mem_of_fixedPoints _ _ (T105_105 i) (hfix105_105 i) _)
      ⟨105, by decide⟩ ⟨105, by decide⟩ _
      (Q2.validAt ⟨105, by decide⟩ (Q2.listedAt ⟨105, by decide⟩
        (alnCheck_rep ⟨105, by decide⟩ hj hq).1))
      (colE2 ⟨105, by decide⟩ 0 hp) Q2.T105_105_2 Q2.hfix105_105_2 Q2.hinj105_105_2
      Q2.hcardT105_105_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T105_105_2 i) (Q2.hfix105_105_2 i) _)
      ?_).symm
  rw [show colData1 (⟨105, by decide⟩ : Fin 148)
        ((colE1 ⟨105, by decide⟩ 0 (transLenTr ⟨105, by decide⟩ 0 hp) : ↥(reps ⟨105, by decide⟩)) : Coordinate 1)
        T105_105 = colFn colCert_105_105_0.D (m := 25) from colCert_105_105_0.bind1,
    show colData2 (⟨105, by decide⟩ : Fin 148)
        ((colE2 ⟨105, by decide⟩ 0 hp : ↥(Q2.reps ⟨105, by decide⟩)) : Coordinate 2)
        Q2.T105_105_2 = colFn colCert_105_105_0.D (m := 25) from colCert_105_105_0.bind2]
  exact alnAll_105_105_0 j hj hq

theorem leaf_105_105_1 (hp : 1 < (Q2.transData.getD 105 []).length)
    (j : Nat) (hj : j < (repChars.getD 105 []).length)
    (hq : (normIsRep.getD 105 []).getD j false = true) :
    species (Q2.reps (⟨105, by decide⟩ : Fin 148)) (colE2 ⟨105, by decide⟩ 1 hp)
        (rowE2 (⟨105, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨105, by decide⟩ : Fin 148))
        (colE1 ⟨105, by decide⟩ 1 (transLenTr ⟨105, by decide⟩ 1 hp))
        (rowE1 (⟨105, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨105, by decide⟩ : Fin 148) ⟨105, by decide⟩ _
      (validAt ⟨105, by decide⟩ (listedAt ⟨105, by decide⟩ hj))
      (colE1 ⟨105, by decide⟩ 1 (transLenTr ⟨105, by decide⟩ 1 hp)) T105_105
      hfix105_105 hinj105_105 hcardT105_105
      (fun i => conj_mem_of_fixedPoints _ _ (T105_105 i) (hfix105_105 i) _)
      ⟨105, by decide⟩ ⟨105, by decide⟩ _
      (Q2.validAt ⟨105, by decide⟩ (Q2.listedAt ⟨105, by decide⟩
        (alnCheck_rep ⟨105, by decide⟩ hj hq).1))
      (colE2 ⟨105, by decide⟩ 1 hp) Q2.T105_105_2 Q2.hfix105_105_2 Q2.hinj105_105_2
      Q2.hcardT105_105_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T105_105_2 i) (Q2.hfix105_105_2 i) _)
      ?_).symm
  rw [show colData1 (⟨105, by decide⟩ : Fin 148)
        ((colE1 ⟨105, by decide⟩ 1 (transLenTr ⟨105, by decide⟩ 1 hp) : ↥(reps ⟨105, by decide⟩)) : Coordinate 1)
        T105_105 = colFn colCert_105_105_1.D (m := 25) from colCert_105_105_1.bind1,
    show colData2 (⟨105, by decide⟩ : Fin 148)
        ((colE2 ⟨105, by decide⟩ 1 hp : ↥(Q2.reps ⟨105, by decide⟩)) : Coordinate 2)
        Q2.T105_105_2 = colFn colCert_105_105_1.D (m := 25) from colCert_105_105_1.bind2]
  exact alnAll_105_105_1 j hj hq

theorem leaf_105_105_2 (hp : 2 < (Q2.transData.getD 105 []).length)
    (j : Nat) (hj : j < (repChars.getD 105 []).length)
    (hq : (normIsRep.getD 105 []).getD j false = true) :
    species (Q2.reps (⟨105, by decide⟩ : Fin 148)) (colE2 ⟨105, by decide⟩ 2 hp)
        (rowE2 (⟨105, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨105, by decide⟩ : Fin 148))
        (colE1 ⟨105, by decide⟩ 2 (transLenTr ⟨105, by decide⟩ 2 hp))
        (rowE1 (⟨105, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨105, by decide⟩ : Fin 148) ⟨105, by decide⟩ _
      (validAt ⟨105, by decide⟩ (listedAt ⟨105, by decide⟩ hj))
      (colE1 ⟨105, by decide⟩ 2 (transLenTr ⟨105, by decide⟩ 2 hp)) T105_105
      hfix105_105 hinj105_105 hcardT105_105
      (fun i => conj_mem_of_fixedPoints _ _ (T105_105 i) (hfix105_105 i) _)
      ⟨105, by decide⟩ ⟨105, by decide⟩ _
      (Q2.validAt ⟨105, by decide⟩ (Q2.listedAt ⟨105, by decide⟩
        (alnCheck_rep ⟨105, by decide⟩ hj hq).1))
      (colE2 ⟨105, by decide⟩ 2 hp) Q2.T105_105_2 Q2.hfix105_105_2 Q2.hinj105_105_2
      Q2.hcardT105_105_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T105_105_2 i) (Q2.hfix105_105_2 i) _)
      ?_).symm
  rw [show colData1 (⟨105, by decide⟩ : Fin 148)
        ((colE1 ⟨105, by decide⟩ 2 (transLenTr ⟨105, by decide⟩ 2 hp) : ↥(reps ⟨105, by decide⟩)) : Coordinate 1)
        T105_105 = colFn colCert_105_105_2.D (m := 25) from colCert_105_105_2.bind1,
    show colData2 (⟨105, by decide⟩ : Fin 148)
        ((colE2 ⟨105, by decide⟩ 2 hp : ↥(Q2.reps ⟨105, by decide⟩)) : Coordinate 2)
        Q2.T105_105_2 = colFn colCert_105_105_2.D (m := 25) from colCert_105_105_2.bind2]
  exact alnAll_105_105_2 j hj hq

theorem leaf_105_105_3 (hp : 3 < (Q2.transData.getD 105 []).length)
    (j : Nat) (hj : j < (repChars.getD 105 []).length)
    (hq : (normIsRep.getD 105 []).getD j false = true) :
    species (Q2.reps (⟨105, by decide⟩ : Fin 148)) (colE2 ⟨105, by decide⟩ 3 hp)
        (rowE2 (⟨105, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨105, by decide⟩ : Fin 148))
        (colE1 ⟨105, by decide⟩ 3 (transLenTr ⟨105, by decide⟩ 3 hp))
        (rowE1 (⟨105, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨105, by decide⟩ : Fin 148) ⟨105, by decide⟩ _
      (validAt ⟨105, by decide⟩ (listedAt ⟨105, by decide⟩ hj))
      (colE1 ⟨105, by decide⟩ 3 (transLenTr ⟨105, by decide⟩ 3 hp)) T105_105
      hfix105_105 hinj105_105 hcardT105_105
      (fun i => conj_mem_of_fixedPoints _ _ (T105_105 i) (hfix105_105 i) _)
      ⟨105, by decide⟩ ⟨105, by decide⟩ _
      (Q2.validAt ⟨105, by decide⟩ (Q2.listedAt ⟨105, by decide⟩
        (alnCheck_rep ⟨105, by decide⟩ hj hq).1))
      (colE2 ⟨105, by decide⟩ 3 hp) Q2.T105_105_2 Q2.hfix105_105_2 Q2.hinj105_105_2
      Q2.hcardT105_105_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T105_105_2 i) (Q2.hfix105_105_2 i) _)
      ?_).symm
  rw [show colData1 (⟨105, by decide⟩ : Fin 148)
        ((colE1 ⟨105, by decide⟩ 3 (transLenTr ⟨105, by decide⟩ 3 hp) : ↥(reps ⟨105, by decide⟩)) : Coordinate 1)
        T105_105 = colFn colCert_105_105_3.D (m := 25) from colCert_105_105_3.bind1,
    show colData2 (⟨105, by decide⟩ : Fin 148)
        ((colE2 ⟨105, by decide⟩ 3 hp : ↥(Q2.reps ⟨105, by decide⟩)) : Coordinate 2)
        Q2.T105_105_2 = colFn colCert_105_105_3.D (m := 25) from colCert_105_105_3.bind2]
  exact alnAll_105_105_3 j hj hq

theorem leaf_105_105_4 (hp : 4 < (Q2.transData.getD 105 []).length)
    (j : Nat) (hj : j < (repChars.getD 105 []).length)
    (hq : (normIsRep.getD 105 []).getD j false = true) :
    species (Q2.reps (⟨105, by decide⟩ : Fin 148)) (colE2 ⟨105, by decide⟩ 4 hp)
        (rowE2 (⟨105, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨105, by decide⟩ : Fin 148))
        (colE1 ⟨105, by decide⟩ 4 (transLenTr ⟨105, by decide⟩ 4 hp))
        (rowE1 (⟨105, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨105, by decide⟩ : Fin 148) ⟨105, by decide⟩ _
      (validAt ⟨105, by decide⟩ (listedAt ⟨105, by decide⟩ hj))
      (colE1 ⟨105, by decide⟩ 4 (transLenTr ⟨105, by decide⟩ 4 hp)) T105_105
      hfix105_105 hinj105_105 hcardT105_105
      (fun i => conj_mem_of_fixedPoints _ _ (T105_105 i) (hfix105_105 i) _)
      ⟨105, by decide⟩ ⟨105, by decide⟩ _
      (Q2.validAt ⟨105, by decide⟩ (Q2.listedAt ⟨105, by decide⟩
        (alnCheck_rep ⟨105, by decide⟩ hj hq).1))
      (colE2 ⟨105, by decide⟩ 4 hp) Q2.T105_105_2 Q2.hfix105_105_2 Q2.hinj105_105_2
      Q2.hcardT105_105_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T105_105_2 i) (Q2.hfix105_105_2 i) _)
      ?_).symm
  rw [show colData1 (⟨105, by decide⟩ : Fin 148)
        ((colE1 ⟨105, by decide⟩ 4 (transLenTr ⟨105, by decide⟩ 4 hp) : ↥(reps ⟨105, by decide⟩)) : Coordinate 1)
        T105_105 = colFn colCert_105_105_4.D (m := 25) from colCert_105_105_4.bind1,
    show colData2 (⟨105, by decide⟩ : Fin 148)
        ((colE2 ⟨105, by decide⟩ 4 hp : ↥(Q2.reps ⟨105, by decide⟩)) : Coordinate 2)
        Q2.T105_105_2 = colFn colCert_105_105_4.D (m := 25) from colCert_105_105_4.bind2]
  exact alnAll_105_105_4 j hj hq

theorem leaf_105_105_5 (hp : 5 < (Q2.transData.getD 105 []).length)
    (j : Nat) (hj : j < (repChars.getD 105 []).length)
    (hq : (normIsRep.getD 105 []).getD j false = true) :
    species (Q2.reps (⟨105, by decide⟩ : Fin 148)) (colE2 ⟨105, by decide⟩ 5 hp)
        (rowE2 (⟨105, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨105, by decide⟩ : Fin 148))
        (colE1 ⟨105, by decide⟩ 5 (transLenTr ⟨105, by decide⟩ 5 hp))
        (rowE1 (⟨105, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨105, by decide⟩ : Fin 148) ⟨105, by decide⟩ _
      (validAt ⟨105, by decide⟩ (listedAt ⟨105, by decide⟩ hj))
      (colE1 ⟨105, by decide⟩ 5 (transLenTr ⟨105, by decide⟩ 5 hp)) T105_105
      hfix105_105 hinj105_105 hcardT105_105
      (fun i => conj_mem_of_fixedPoints _ _ (T105_105 i) (hfix105_105 i) _)
      ⟨105, by decide⟩ ⟨105, by decide⟩ _
      (Q2.validAt ⟨105, by decide⟩ (Q2.listedAt ⟨105, by decide⟩
        (alnCheck_rep ⟨105, by decide⟩ hj hq).1))
      (colE2 ⟨105, by decide⟩ 5 hp) Q2.T105_105_2 Q2.hfix105_105_2 Q2.hinj105_105_2
      Q2.hcardT105_105_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T105_105_2 i) (Q2.hfix105_105_2 i) _)
      ?_).symm
  rw [show colData1 (⟨105, by decide⟩ : Fin 148)
        ((colE1 ⟨105, by decide⟩ 5 (transLenTr ⟨105, by decide⟩ 5 hp) : ↥(reps ⟨105, by decide⟩)) : Coordinate 1)
        T105_105 = colFn colCert_105_105_5.D (m := 25) from colCert_105_105_5.bind1,
    show colData2 (⟨105, by decide⟩ : Fin 148)
        ((colE2 ⟨105, by decide⟩ 5 hp : ↥(Q2.reps ⟨105, by decide⟩)) : Coordinate 2)
        Q2.T105_105_2 = colFn colCert_105_105_5.D (m := 25) from colCert_105_105_5.bind2]
  exact alnAll_105_105_5 j hj hq

theorem leaf_105_105_10 (hp : 10 < (Q2.transData.getD 105 []).length)
    (j : Nat) (hj : j < (repChars.getD 105 []).length)
    (hq : (normIsRep.getD 105 []).getD j false = true) :
    species (Q2.reps (⟨105, by decide⟩ : Fin 148)) (colE2 ⟨105, by decide⟩ 10 hp)
        (rowE2 (⟨105, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨105, by decide⟩ : Fin 148))
        (colE1 ⟨105, by decide⟩ 10 (transLenTr ⟨105, by decide⟩ 10 hp))
        (rowE1 (⟨105, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨105, by decide⟩ : Fin 148) ⟨105, by decide⟩ _
      (validAt ⟨105, by decide⟩ (listedAt ⟨105, by decide⟩ hj))
      (colE1 ⟨105, by decide⟩ 10 (transLenTr ⟨105, by decide⟩ 10 hp)) T105_105
      hfix105_105 hinj105_105 hcardT105_105
      (fun i => conj_mem_of_fixedPoints _ _ (T105_105 i) (hfix105_105 i) _)
      ⟨105, by decide⟩ ⟨105, by decide⟩ _
      (Q2.validAt ⟨105, by decide⟩ (Q2.listedAt ⟨105, by decide⟩
        (alnCheck_rep ⟨105, by decide⟩ hj hq).1))
      (colE2 ⟨105, by decide⟩ 10 hp) Q2.T105_105_2 Q2.hfix105_105_2 Q2.hinj105_105_2
      Q2.hcardT105_105_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T105_105_2 i) (Q2.hfix105_105_2 i) _)
      ?_).symm
  rw [show colData1 (⟨105, by decide⟩ : Fin 148)
        ((colE1 ⟨105, by decide⟩ 10 (transLenTr ⟨105, by decide⟩ 10 hp) : ↥(reps ⟨105, by decide⟩)) : Coordinate 1)
        T105_105 = colFn colCert_105_105_10.D (m := 25) from colCert_105_105_10.bind1,
    show colData2 (⟨105, by decide⟩ : Fin 148)
        ((colE2 ⟨105, by decide⟩ 10 hp : ↥(Q2.reps ⟨105, by decide⟩)) : Coordinate 2)
        Q2.T105_105_2 = colFn colCert_105_105_10.D (m := 25) from colCert_105_105_10.bind2]
  exact alnAll_105_105_10 j hj hq

theorem leaf_105_105_15 (hp : 15 < (Q2.transData.getD 105 []).length)
    (j : Nat) (hj : j < (repChars.getD 105 []).length)
    (hq : (normIsRep.getD 105 []).getD j false = true) :
    species (Q2.reps (⟨105, by decide⟩ : Fin 148)) (colE2 ⟨105, by decide⟩ 15 hp)
        (rowE2 (⟨105, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨105, by decide⟩ : Fin 148))
        (colE1 ⟨105, by decide⟩ 15 (transLenTr ⟨105, by decide⟩ 15 hp))
        (rowE1 (⟨105, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨105, by decide⟩ : Fin 148) ⟨105, by decide⟩ _
      (validAt ⟨105, by decide⟩ (listedAt ⟨105, by decide⟩ hj))
      (colE1 ⟨105, by decide⟩ 15 (transLenTr ⟨105, by decide⟩ 15 hp)) T105_105
      hfix105_105 hinj105_105 hcardT105_105
      (fun i => conj_mem_of_fixedPoints _ _ (T105_105 i) (hfix105_105 i) _)
      ⟨105, by decide⟩ ⟨105, by decide⟩ _
      (Q2.validAt ⟨105, by decide⟩ (Q2.listedAt ⟨105, by decide⟩
        (alnCheck_rep ⟨105, by decide⟩ hj hq).1))
      (colE2 ⟨105, by decide⟩ 15 hp) Q2.T105_105_2 Q2.hfix105_105_2 Q2.hinj105_105_2
      Q2.hcardT105_105_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T105_105_2 i) (Q2.hfix105_105_2 i) _)
      ?_).symm
  rw [show colData1 (⟨105, by decide⟩ : Fin 148)
        ((colE1 ⟨105, by decide⟩ 15 (transLenTr ⟨105, by decide⟩ 15 hp) : ↥(reps ⟨105, by decide⟩)) : Coordinate 1)
        T105_105 = colFn colCert_105_105_15.D (m := 25) from colCert_105_105_15.bind1,
    show colData2 (⟨105, by decide⟩ : Fin 148)
        ((colE2 ⟨105, by decide⟩ 15 hp : ↥(Q2.reps ⟨105, by decide⟩)) : Coordinate 2)
        Q2.T105_105_2 = colFn colCert_105_105_15.D (m := 25) from colCert_105_105_15.bind2]
  exact alnAll_105_105_15 j hj hq

theorem leaf_105_105_20 (hp : 20 < (Q2.transData.getD 105 []).length)
    (j : Nat) (hj : j < (repChars.getD 105 []).length)
    (hq : (normIsRep.getD 105 []).getD j false = true) :
    species (Q2.reps (⟨105, by decide⟩ : Fin 148)) (colE2 ⟨105, by decide⟩ 20 hp)
        (rowE2 (⟨105, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨105, by decide⟩ : Fin 148))
        (colE1 ⟨105, by decide⟩ 20 (transLenTr ⟨105, by decide⟩ 20 hp))
        (rowE1 (⟨105, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨105, by decide⟩ : Fin 148) ⟨105, by decide⟩ _
      (validAt ⟨105, by decide⟩ (listedAt ⟨105, by decide⟩ hj))
      (colE1 ⟨105, by decide⟩ 20 (transLenTr ⟨105, by decide⟩ 20 hp)) T105_105
      hfix105_105 hinj105_105 hcardT105_105
      (fun i => conj_mem_of_fixedPoints _ _ (T105_105 i) (hfix105_105 i) _)
      ⟨105, by decide⟩ ⟨105, by decide⟩ _
      (Q2.validAt ⟨105, by decide⟩ (Q2.listedAt ⟨105, by decide⟩
        (alnCheck_rep ⟨105, by decide⟩ hj hq).1))
      (colE2 ⟨105, by decide⟩ 20 hp) Q2.T105_105_2 Q2.hfix105_105_2 Q2.hinj105_105_2
      Q2.hcardT105_105_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T105_105_2 i) (Q2.hfix105_105_2 i) _)
      ?_).symm
  rw [show colData1 (⟨105, by decide⟩ : Fin 148)
        ((colE1 ⟨105, by decide⟩ 20 (transLenTr ⟨105, by decide⟩ 20 hp) : ↥(reps ⟨105, by decide⟩)) : Coordinate 1)
        T105_105 = colFn colCert_105_105_20.D (m := 25) from colCert_105_105_20.bind1,
    show colData2 (⟨105, by decide⟩ : Fin 148)
        ((colE2 ⟨105, by decide⟩ 20 hp : ↥(Q2.reps ⟨105, by decide⟩)) : Coordinate 2)
        Q2.T105_105_2 = colFn colCert_105_105_20.D (m := 25) from colCert_105_105_20.bind2]
  exact alnAll_105_105_20 j hj hq

theorem leaf_105_105_25 (hp : 25 < (Q2.transData.getD 105 []).length)
    (j : Nat) (hj : j < (repChars.getD 105 []).length)
    (hq : (normIsRep.getD 105 []).getD j false = true) :
    species (Q2.reps (⟨105, by decide⟩ : Fin 148)) (colE2 ⟨105, by decide⟩ 25 hp)
        (rowE2 (⟨105, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨105, by decide⟩ : Fin 148))
        (colE1 ⟨105, by decide⟩ 25 (transLenTr ⟨105, by decide⟩ 25 hp))
        (rowE1 (⟨105, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨105, by decide⟩ : Fin 148) ⟨105, by decide⟩ _
      (validAt ⟨105, by decide⟩ (listedAt ⟨105, by decide⟩ hj))
      (colE1 ⟨105, by decide⟩ 25 (transLenTr ⟨105, by decide⟩ 25 hp)) T105_105
      hfix105_105 hinj105_105 hcardT105_105
      (fun i => conj_mem_of_fixedPoints _ _ (T105_105 i) (hfix105_105 i) _)
      ⟨105, by decide⟩ ⟨105, by decide⟩ _
      (Q2.validAt ⟨105, by decide⟩ (Q2.listedAt ⟨105, by decide⟩
        (alnCheck_rep ⟨105, by decide⟩ hj hq).1))
      (colE2 ⟨105, by decide⟩ 25 hp) Q2.T105_105_2 Q2.hfix105_105_2 Q2.hinj105_105_2
      Q2.hcardT105_105_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T105_105_2 i) (Q2.hfix105_105_2 i) _)
      ?_).symm
  rw [show colData1 (⟨105, by decide⟩ : Fin 148)
        ((colE1 ⟨105, by decide⟩ 25 (transLenTr ⟨105, by decide⟩ 25 hp) : ↥(reps ⟨105, by decide⟩)) : Coordinate 1)
        T105_105 = colFn colCert_105_105_25.D (m := 25) from colCert_105_105_25.bind1,
    show colData2 (⟨105, by decide⟩ : Fin 148)
        ((colE2 ⟨105, by decide⟩ 25 hp : ↥(Q2.reps ⟨105, by decide⟩)) : Coordinate 2)
        Q2.T105_105_2 = colFn colCert_105_105_25.D (m := 25) from colCert_105_105_25.bind2]
  exact alnAll_105_105_25 j hj hq

theorem leaf_105_105_50 (hp : 50 < (Q2.transData.getD 105 []).length)
    (j : Nat) (hj : j < (repChars.getD 105 []).length)
    (hq : (normIsRep.getD 105 []).getD j false = true) :
    species (Q2.reps (⟨105, by decide⟩ : Fin 148)) (colE2 ⟨105, by decide⟩ 50 hp)
        (rowE2 (⟨105, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨105, by decide⟩ : Fin 148))
        (colE1 ⟨105, by decide⟩ 50 (transLenTr ⟨105, by decide⟩ 50 hp))
        (rowE1 (⟨105, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨105, by decide⟩ : Fin 148) ⟨105, by decide⟩ _
      (validAt ⟨105, by decide⟩ (listedAt ⟨105, by decide⟩ hj))
      (colE1 ⟨105, by decide⟩ 50 (transLenTr ⟨105, by decide⟩ 50 hp)) T105_105
      hfix105_105 hinj105_105 hcardT105_105
      (fun i => conj_mem_of_fixedPoints _ _ (T105_105 i) (hfix105_105 i) _)
      ⟨105, by decide⟩ ⟨105, by decide⟩ _
      (Q2.validAt ⟨105, by decide⟩ (Q2.listedAt ⟨105, by decide⟩
        (alnCheck_rep ⟨105, by decide⟩ hj hq).1))
      (colE2 ⟨105, by decide⟩ 50 hp) Q2.T105_105_2 Q2.hfix105_105_2 Q2.hinj105_105_2
      Q2.hcardT105_105_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T105_105_2 i) (Q2.hfix105_105_2 i) _)
      ?_).symm
  rw [show colData1 (⟨105, by decide⟩ : Fin 148)
        ((colE1 ⟨105, by decide⟩ 50 (transLenTr ⟨105, by decide⟩ 50 hp) : ↥(reps ⟨105, by decide⟩)) : Coordinate 1)
        T105_105 = colFn colCert_105_105_50.D (m := 25) from colCert_105_105_50.bind1,
    show colData2 (⟨105, by decide⟩ : Fin 148)
        ((colE2 ⟨105, by decide⟩ 50 hp : ↥(Q2.reps ⟨105, by decide⟩)) : Coordinate 2)
        Q2.T105_105_2 = colFn colCert_105_105_50.D (m := 25) from colCert_105_105_50.bind2]
  exact alnAll_105_105_50 j hj hq

theorem leaf_105_105_75 (hp : 75 < (Q2.transData.getD 105 []).length)
    (j : Nat) (hj : j < (repChars.getD 105 []).length)
    (hq : (normIsRep.getD 105 []).getD j false = true) :
    species (Q2.reps (⟨105, by decide⟩ : Fin 148)) (colE2 ⟨105, by decide⟩ 75 hp)
        (rowE2 (⟨105, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨105, by decide⟩ : Fin 148))
        (colE1 ⟨105, by decide⟩ 75 (transLenTr ⟨105, by decide⟩ 75 hp))
        (rowE1 (⟨105, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨105, by decide⟩ : Fin 148) ⟨105, by decide⟩ _
      (validAt ⟨105, by decide⟩ (listedAt ⟨105, by decide⟩ hj))
      (colE1 ⟨105, by decide⟩ 75 (transLenTr ⟨105, by decide⟩ 75 hp)) T105_105
      hfix105_105 hinj105_105 hcardT105_105
      (fun i => conj_mem_of_fixedPoints _ _ (T105_105 i) (hfix105_105 i) _)
      ⟨105, by decide⟩ ⟨105, by decide⟩ _
      (Q2.validAt ⟨105, by decide⟩ (Q2.listedAt ⟨105, by decide⟩
        (alnCheck_rep ⟨105, by decide⟩ hj hq).1))
      (colE2 ⟨105, by decide⟩ 75 hp) Q2.T105_105_2 Q2.hfix105_105_2 Q2.hinj105_105_2
      Q2.hcardT105_105_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T105_105_2 i) (Q2.hfix105_105_2 i) _)
      ?_).symm
  rw [show colData1 (⟨105, by decide⟩ : Fin 148)
        ((colE1 ⟨105, by decide⟩ 75 (transLenTr ⟨105, by decide⟩ 75 hp) : ↥(reps ⟨105, by decide⟩)) : Coordinate 1)
        T105_105 = colFn colCert_105_105_75.D (m := 25) from colCert_105_105_75.bind1,
    show colData2 (⟨105, by decide⟩ : Fin 148)
        ((colE2 ⟨105, by decide⟩ 75 hp : ↥(Q2.reps ⟨105, by decide⟩)) : Coordinate 2)
        Q2.T105_105_2 = colFn colCert_105_105_75.D (m := 25) from colCert_105_105_75.bind2]
  exact alnAll_105_105_75 j hj hq

theorem leaf_105_105_100 (hp : 100 < (Q2.transData.getD 105 []).length)
    (j : Nat) (hj : j < (repChars.getD 105 []).length)
    (hq : (normIsRep.getD 105 []).getD j false = true) :
    species (Q2.reps (⟨105, by decide⟩ : Fin 148)) (colE2 ⟨105, by decide⟩ 100 hp)
        (rowE2 (⟨105, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨105, by decide⟩ : Fin 148))
        (colE1 ⟨105, by decide⟩ 100 (transLenTr ⟨105, by decide⟩ 100 hp))
        (rowE1 (⟨105, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨105, by decide⟩ : Fin 148) ⟨105, by decide⟩ _
      (validAt ⟨105, by decide⟩ (listedAt ⟨105, by decide⟩ hj))
      (colE1 ⟨105, by decide⟩ 100 (transLenTr ⟨105, by decide⟩ 100 hp)) T105_105
      hfix105_105 hinj105_105 hcardT105_105
      (fun i => conj_mem_of_fixedPoints _ _ (T105_105 i) (hfix105_105 i) _)
      ⟨105, by decide⟩ ⟨105, by decide⟩ _
      (Q2.validAt ⟨105, by decide⟩ (Q2.listedAt ⟨105, by decide⟩
        (alnCheck_rep ⟨105, by decide⟩ hj hq).1))
      (colE2 ⟨105, by decide⟩ 100 hp) Q2.T105_105_2 Q2.hfix105_105_2 Q2.hinj105_105_2
      Q2.hcardT105_105_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T105_105_2 i) (Q2.hfix105_105_2 i) _)
      ?_).symm
  rw [show colData1 (⟨105, by decide⟩ : Fin 148)
        ((colE1 ⟨105, by decide⟩ 100 (transLenTr ⟨105, by decide⟩ 100 hp) : ↥(reps ⟨105, by decide⟩)) : Coordinate 1)
        T105_105 = colFn colCert_105_105_100.D (m := 25) from colCert_105_105_100.bind1,
    show colData2 (⟨105, by decide⟩ : Fin 148)
        ((colE2 ⟨105, by decide⟩ 100 hp : ↥(Q2.reps ⟨105, by decide⟩)) : Coordinate 2)
        Q2.T105_105_2 = colFn colCert_105_105_100.D (m := 25) from colCert_105_105_100.bind2]
  exact alnAll_105_105_100 j hj hq

theorem leaf_106_10_0 (hp : 0 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 106 []).length)
    (hq : (normIsRep.getD 106 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 0 hp)
        (rowE2 (⟨106, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 0 (transLenTr ⟨10, by decide⟩ 0 hp))
        (rowE1 (⟨106, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨106, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨106, by decide⟩ (listedAt ⟨106, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 0 (transLenTr ⟨10, by decide⟩ 0 hp)) T106_10
      hfix106_10 hinj106_10 hcardT106_10
      (fun i => conj_mem_of_fixedPoints _ _ (T106_10 i) (hfix106_10 i) _)
      ⟨106, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨106, by decide⟩ (Q2.listedAt ⟨106, by decide⟩
        (alnCheck_rep ⟨106, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 0 hp) Q2.T106_10_2 Q2.hfix106_10_2 Q2.hinj106_10_2
      Q2.hcardT106_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T106_10_2 i) (Q2.hfix106_10_2 i) _)
      colCert_106_10_0.hD ?_).symm
  rw [alnId_106 j hj]


theorem leaf_106_10_1 (hp : 1 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 106 []).length)
    (hq : (normIsRep.getD 106 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 1 hp)
        (rowE2 (⟨106, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 1 (transLenTr ⟨10, by decide⟩ 1 hp))
        (rowE1 (⟨106, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨106, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨106, by decide⟩ (listedAt ⟨106, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 1 (transLenTr ⟨10, by decide⟩ 1 hp)) T106_10
      hfix106_10 hinj106_10 hcardT106_10
      (fun i => conj_mem_of_fixedPoints _ _ (T106_10 i) (hfix106_10 i) _)
      ⟨106, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨106, by decide⟩ (Q2.listedAt ⟨106, by decide⟩
        (alnCheck_rep ⟨106, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 1 hp) Q2.T106_10_2 Q2.hfix106_10_2 Q2.hinj106_10_2
      Q2.hcardT106_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T106_10_2 i) (Q2.hfix106_10_2 i) _)
      colCert_106_10_1.hD ?_).symm
  rw [alnId_106 j hj]


theorem leaf_106_10_2 (hp : 2 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 106 []).length)
    (hq : (normIsRep.getD 106 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 2 hp)
        (rowE2 (⟨106, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 2 (transLenTr ⟨10, by decide⟩ 2 hp))
        (rowE1 (⟨106, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨106, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨106, by decide⟩ (listedAt ⟨106, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 2 (transLenTr ⟨10, by decide⟩ 2 hp)) T106_10
      hfix106_10 hinj106_10 hcardT106_10
      (fun i => conj_mem_of_fixedPoints _ _ (T106_10 i) (hfix106_10 i) _)
      ⟨106, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨106, by decide⟩ (Q2.listedAt ⟨106, by decide⟩
        (alnCheck_rep ⟨106, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 2 hp) Q2.T106_10_2 Q2.hfix106_10_2 Q2.hinj106_10_2
      Q2.hcardT106_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T106_10_2 i) (Q2.hfix106_10_2 i) _)
      colCert_106_10_2.hD ?_).symm
  rw [alnId_106 j hj]


theorem leaf_106_10_3 (hp : 3 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 106 []).length)
    (hq : (normIsRep.getD 106 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 3 hp)
        (rowE2 (⟨106, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 3 (transLenTr ⟨10, by decide⟩ 3 hp))
        (rowE1 (⟨106, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨106, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨106, by decide⟩ (listedAt ⟨106, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 3 (transLenTr ⟨10, by decide⟩ 3 hp)) T106_10
      hfix106_10 hinj106_10 hcardT106_10
      (fun i => conj_mem_of_fixedPoints _ _ (T106_10 i) (hfix106_10 i) _)
      ⟨106, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨106, by decide⟩ (Q2.listedAt ⟨106, by decide⟩
        (alnCheck_rep ⟨106, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 3 hp) Q2.T106_10_2 Q2.hfix106_10_2 Q2.hinj106_10_2
      Q2.hcardT106_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T106_10_2 i) (Q2.hfix106_10_2 i) _)
      colCert_106_10_3.hD ?_).symm
  rw [alnId_106 j hj]


theorem leaf_106_10_4 (hp : 4 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 106 []).length)
    (hq : (normIsRep.getD 106 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 4 hp)
        (rowE2 (⟨106, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 4 (transLenTr ⟨10, by decide⟩ 4 hp))
        (rowE1 (⟨106, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨106, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨106, by decide⟩ (listedAt ⟨106, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 4 (transLenTr ⟨10, by decide⟩ 4 hp)) T106_10
      hfix106_10 hinj106_10 hcardT106_10
      (fun i => conj_mem_of_fixedPoints _ _ (T106_10 i) (hfix106_10 i) _)
      ⟨106, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨106, by decide⟩ (Q2.listedAt ⟨106, by decide⟩
        (alnCheck_rep ⟨106, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 4 hp) Q2.T106_10_2 Q2.hfix106_10_2 Q2.hinj106_10_2
      Q2.hcardT106_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T106_10_2 i) (Q2.hfix106_10_2 i) _)
      colCert_106_10_4.hD ?_).symm
  rw [alnId_106 j hj]


theorem leaf_106_12_0 (hp : 0 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 106 []).length)
    (hq : (normIsRep.getD 106 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 0 hp)
        (rowE2 (⟨106, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp))
        (rowE1 (⟨106, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨106, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨106, by decide⟩ (listedAt ⟨106, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp)) T106_12
      hfix106_12 hinj106_12 hcardT106_12
      (fun i => conj_mem_of_fixedPoints _ _ (T106_12 i) (hfix106_12 i) _)
      ⟨106, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨106, by decide⟩ (Q2.listedAt ⟨106, by decide⟩
        (alnCheck_rep ⟨106, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 0 hp) Q2.T106_12_2 Q2.hfix106_12_2 Q2.hinj106_12_2
      Q2.hcardT106_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T106_12_2 i) (Q2.hfix106_12_2 i) _)
      colCert_106_12_0.hD ?_).symm
  rw [alnId_106 j hj]


theorem leaf_106_12_1 (hp : 1 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 106 []).length)
    (hq : (normIsRep.getD 106 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 1 hp)
        (rowE2 (⟨106, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp))
        (rowE1 (⟨106, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨106, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨106, by decide⟩ (listedAt ⟨106, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp)) T106_12
      hfix106_12 hinj106_12 hcardT106_12
      (fun i => conj_mem_of_fixedPoints _ _ (T106_12 i) (hfix106_12 i) _)
      ⟨106, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨106, by decide⟩ (Q2.listedAt ⟨106, by decide⟩
        (alnCheck_rep ⟨106, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 1 hp) Q2.T106_12_2 Q2.hfix106_12_2 Q2.hinj106_12_2
      Q2.hcardT106_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T106_12_2 i) (Q2.hfix106_12_2 i) _)
      colCert_106_12_1.hD ?_).symm
  rw [alnId_106 j hj]


theorem leaf_106_12_2 (hp : 2 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 106 []).length)
    (hq : (normIsRep.getD 106 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 2 hp)
        (rowE2 (⟨106, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp))
        (rowE1 (⟨106, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨106, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨106, by decide⟩ (listedAt ⟨106, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp)) T106_12
      hfix106_12 hinj106_12 hcardT106_12
      (fun i => conj_mem_of_fixedPoints _ _ (T106_12 i) (hfix106_12 i) _)
      ⟨106, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨106, by decide⟩ (Q2.listedAt ⟨106, by decide⟩
        (alnCheck_rep ⟨106, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 2 hp) Q2.T106_12_2 Q2.hfix106_12_2 Q2.hinj106_12_2
      Q2.hcardT106_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T106_12_2 i) (Q2.hfix106_12_2 i) _)
      colCert_106_12_2.hD ?_).symm
  rw [alnId_106 j hj]


theorem leaf_106_12_3 (hp : 3 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 106 []).length)
    (hq : (normIsRep.getD 106 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 3 hp)
        (rowE2 (⟨106, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp))
        (rowE1 (⟨106, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨106, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨106, by decide⟩ (listedAt ⟨106, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp)) T106_12
      hfix106_12 hinj106_12 hcardT106_12
      (fun i => conj_mem_of_fixedPoints _ _ (T106_12 i) (hfix106_12 i) _)
      ⟨106, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨106, by decide⟩ (Q2.listedAt ⟨106, by decide⟩
        (alnCheck_rep ⟨106, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 3 hp) Q2.T106_12_2 Q2.hfix106_12_2 Q2.hinj106_12_2
      Q2.hcardT106_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T106_12_2 i) (Q2.hfix106_12_2 i) _)
      colCert_106_12_3.hD ?_).symm
  rw [alnId_106 j hj]


theorem leaf_106_12_4 (hp : 4 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 106 []).length)
    (hq : (normIsRep.getD 106 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 4 hp)
        (rowE2 (⟨106, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp))
        (rowE1 (⟨106, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨106, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨106, by decide⟩ (listedAt ⟨106, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp)) T106_12
      hfix106_12 hinj106_12 hcardT106_12
      (fun i => conj_mem_of_fixedPoints _ _ (T106_12 i) (hfix106_12 i) _)
      ⟨106, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨106, by decide⟩ (Q2.listedAt ⟨106, by decide⟩
        (alnCheck_rep ⟨106, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 4 hp) Q2.T106_12_2 Q2.hfix106_12_2 Q2.hinj106_12_2
      Q2.hcardT106_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T106_12_2 i) (Q2.hfix106_12_2 i) _)
      colCert_106_12_4.hD ?_).symm
  rw [alnId_106 j hj]


theorem leaf_106_44_0 (hp : 0 < (Q2.transData.getD 44 []).length)
    (j : Nat) (hj : j < (repChars.getD 106 []).length)
    (hq : (normIsRep.getD 106 []).getD j false = true) :
    species (Q2.reps (⟨44, by decide⟩ : Fin 148)) (colE2 ⟨44, by decide⟩ 0 hp)
        (rowE2 (⟨106, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨44, by decide⟩ : Fin 148))
        (colE1 ⟨44, by decide⟩ 0 (transLenTr ⟨44, by decide⟩ 0 hp))
        (rowE1 (⟨106, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨106, by decide⟩ : Fin 148) ⟨44, by decide⟩ _
      (validAt ⟨106, by decide⟩ (listedAt ⟨106, by decide⟩ hj))
      (colE1 ⟨44, by decide⟩ 0 (transLenTr ⟨44, by decide⟩ 0 hp)) T106_44
      hfix106_44 hinj106_44 hcardT106_44
      (fun i => conj_mem_of_fixedPoints _ _ (T106_44 i) (hfix106_44 i) _)
      ⟨106, by decide⟩ ⟨44, by decide⟩ _
      (Q2.validAt ⟨106, by decide⟩ (Q2.listedAt ⟨106, by decide⟩
        (alnCheck_rep ⟨106, by decide⟩ hj hq).1))
      (colE2 ⟨44, by decide⟩ 0 hp) Q2.T106_44_2 Q2.hfix106_44_2 Q2.hinj106_44_2
      Q2.hcardT106_44_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T106_44_2 i) (Q2.hfix106_44_2 i) _)
      colCert_106_44_0.hD ?_).symm
  rw [alnId_106 j hj]


theorem leaf_106_44_1 (hp : 1 < (Q2.transData.getD 44 []).length)
    (j : Nat) (hj : j < (repChars.getD 106 []).length)
    (hq : (normIsRep.getD 106 []).getD j false = true) :
    species (Q2.reps (⟨44, by decide⟩ : Fin 148)) (colE2 ⟨44, by decide⟩ 1 hp)
        (rowE2 (⟨106, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨44, by decide⟩ : Fin 148))
        (colE1 ⟨44, by decide⟩ 1 (transLenTr ⟨44, by decide⟩ 1 hp))
        (rowE1 (⟨106, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨106, by decide⟩ : Fin 148) ⟨44, by decide⟩ _
      (validAt ⟨106, by decide⟩ (listedAt ⟨106, by decide⟩ hj))
      (colE1 ⟨44, by decide⟩ 1 (transLenTr ⟨44, by decide⟩ 1 hp)) T106_44
      hfix106_44 hinj106_44 hcardT106_44
      (fun i => conj_mem_of_fixedPoints _ _ (T106_44 i) (hfix106_44 i) _)
      ⟨106, by decide⟩ ⟨44, by decide⟩ _
      (Q2.validAt ⟨106, by decide⟩ (Q2.listedAt ⟨106, by decide⟩
        (alnCheck_rep ⟨106, by decide⟩ hj hq).1))
      (colE2 ⟨44, by decide⟩ 1 hp) Q2.T106_44_2 Q2.hfix106_44_2 Q2.hinj106_44_2
      Q2.hcardT106_44_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T106_44_2 i) (Q2.hfix106_44_2 i) _)
      colCert_106_44_1.hD ?_).symm
  rw [alnId_106 j hj]


theorem leaf_106_44_2 (hp : 2 < (Q2.transData.getD 44 []).length)
    (j : Nat) (hj : j < (repChars.getD 106 []).length)
    (hq : (normIsRep.getD 106 []).getD j false = true) :
    species (Q2.reps (⟨44, by decide⟩ : Fin 148)) (colE2 ⟨44, by decide⟩ 2 hp)
        (rowE2 (⟨106, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨44, by decide⟩ : Fin 148))
        (colE1 ⟨44, by decide⟩ 2 (transLenTr ⟨44, by decide⟩ 2 hp))
        (rowE1 (⟨106, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨106, by decide⟩ : Fin 148) ⟨44, by decide⟩ _
      (validAt ⟨106, by decide⟩ (listedAt ⟨106, by decide⟩ hj))
      (colE1 ⟨44, by decide⟩ 2 (transLenTr ⟨44, by decide⟩ 2 hp)) T106_44
      hfix106_44 hinj106_44 hcardT106_44
      (fun i => conj_mem_of_fixedPoints _ _ (T106_44 i) (hfix106_44 i) _)
      ⟨106, by decide⟩ ⟨44, by decide⟩ _
      (Q2.validAt ⟨106, by decide⟩ (Q2.listedAt ⟨106, by decide⟩
        (alnCheck_rep ⟨106, by decide⟩ hj hq).1))
      (colE2 ⟨44, by decide⟩ 2 hp) Q2.T106_44_2 Q2.hfix106_44_2 Q2.hinj106_44_2
      Q2.hcardT106_44_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T106_44_2 i) (Q2.hfix106_44_2 i) _)
      colCert_106_44_2.hD ?_).symm
  rw [alnId_106 j hj]


theorem leaf_106_44_3 (hp : 3 < (Q2.transData.getD 44 []).length)
    (j : Nat) (hj : j < (repChars.getD 106 []).length)
    (hq : (normIsRep.getD 106 []).getD j false = true) :
    species (Q2.reps (⟨44, by decide⟩ : Fin 148)) (colE2 ⟨44, by decide⟩ 3 hp)
        (rowE2 (⟨106, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨44, by decide⟩ : Fin 148))
        (colE1 ⟨44, by decide⟩ 3 (transLenTr ⟨44, by decide⟩ 3 hp))
        (rowE1 (⟨106, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨106, by decide⟩ : Fin 148) ⟨44, by decide⟩ _
      (validAt ⟨106, by decide⟩ (listedAt ⟨106, by decide⟩ hj))
      (colE1 ⟨44, by decide⟩ 3 (transLenTr ⟨44, by decide⟩ 3 hp)) T106_44
      hfix106_44 hinj106_44 hcardT106_44
      (fun i => conj_mem_of_fixedPoints _ _ (T106_44 i) (hfix106_44 i) _)
      ⟨106, by decide⟩ ⟨44, by decide⟩ _
      (Q2.validAt ⟨106, by decide⟩ (Q2.listedAt ⟨106, by decide⟩
        (alnCheck_rep ⟨106, by decide⟩ hj hq).1))
      (colE2 ⟨44, by decide⟩ 3 hp) Q2.T106_44_2 Q2.hfix106_44_2 Q2.hinj106_44_2
      Q2.hcardT106_44_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T106_44_2 i) (Q2.hfix106_44_2 i) _)
      colCert_106_44_3.hD ?_).symm
  rw [alnId_106 j hj]


theorem leaf_106_44_4 (hp : 4 < (Q2.transData.getD 44 []).length)
    (j : Nat) (hj : j < (repChars.getD 106 []).length)
    (hq : (normIsRep.getD 106 []).getD j false = true) :
    species (Q2.reps (⟨44, by decide⟩ : Fin 148)) (colE2 ⟨44, by decide⟩ 4 hp)
        (rowE2 (⟨106, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨44, by decide⟩ : Fin 148))
        (colE1 ⟨44, by decide⟩ 4 (transLenTr ⟨44, by decide⟩ 4 hp))
        (rowE1 (⟨106, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨106, by decide⟩ : Fin 148) ⟨44, by decide⟩ _
      (validAt ⟨106, by decide⟩ (listedAt ⟨106, by decide⟩ hj))
      (colE1 ⟨44, by decide⟩ 4 (transLenTr ⟨44, by decide⟩ 4 hp)) T106_44
      hfix106_44 hinj106_44 hcardT106_44
      (fun i => conj_mem_of_fixedPoints _ _ (T106_44 i) (hfix106_44 i) _)
      ⟨106, by decide⟩ ⟨44, by decide⟩ _
      (Q2.validAt ⟨106, by decide⟩ (Q2.listedAt ⟨106, by decide⟩
        (alnCheck_rep ⟨106, by decide⟩ hj hq).1))
      (colE2 ⟨44, by decide⟩ 4 hp) Q2.T106_44_2 Q2.hfix106_44_2 Q2.hinj106_44_2
      Q2.hcardT106_44_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T106_44_2 i) (Q2.hfix106_44_2 i) _)
      colCert_106_44_4.hD ?_).symm
  rw [alnId_106 j hj]


theorem leaf_106_44_5 (hp : 5 < (Q2.transData.getD 44 []).length)
    (j : Nat) (hj : j < (repChars.getD 106 []).length)
    (hq : (normIsRep.getD 106 []).getD j false = true) :
    species (Q2.reps (⟨44, by decide⟩ : Fin 148)) (colE2 ⟨44, by decide⟩ 5 hp)
        (rowE2 (⟨106, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨44, by decide⟩ : Fin 148))
        (colE1 ⟨44, by decide⟩ 5 (transLenTr ⟨44, by decide⟩ 5 hp))
        (rowE1 (⟨106, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨106, by decide⟩ : Fin 148) ⟨44, by decide⟩ _
      (validAt ⟨106, by decide⟩ (listedAt ⟨106, by decide⟩ hj))
      (colE1 ⟨44, by decide⟩ 5 (transLenTr ⟨44, by decide⟩ 5 hp)) T106_44
      hfix106_44 hinj106_44 hcardT106_44
      (fun i => conj_mem_of_fixedPoints _ _ (T106_44 i) (hfix106_44 i) _)
      ⟨106, by decide⟩ ⟨44, by decide⟩ _
      (Q2.validAt ⟨106, by decide⟩ (Q2.listedAt ⟨106, by decide⟩
        (alnCheck_rep ⟨106, by decide⟩ hj hq).1))
      (colE2 ⟨44, by decide⟩ 5 hp) Q2.T106_44_2 Q2.hfix106_44_2 Q2.hinj106_44_2
      Q2.hcardT106_44_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T106_44_2 i) (Q2.hfix106_44_2 i) _)
      colCert_106_44_5.hD ?_).symm
  rw [alnId_106 j hj]


theorem leaf_106_44_10 (hp : 10 < (Q2.transData.getD 44 []).length)
    (j : Nat) (hj : j < (repChars.getD 106 []).length)
    (hq : (normIsRep.getD 106 []).getD j false = true) :
    species (Q2.reps (⟨44, by decide⟩ : Fin 148)) (colE2 ⟨44, by decide⟩ 10 hp)
        (rowE2 (⟨106, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨44, by decide⟩ : Fin 148))
        (colE1 ⟨44, by decide⟩ 10 (transLenTr ⟨44, by decide⟩ 10 hp))
        (rowE1 (⟨106, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨106, by decide⟩ : Fin 148) ⟨44, by decide⟩ _
      (validAt ⟨106, by decide⟩ (listedAt ⟨106, by decide⟩ hj))
      (colE1 ⟨44, by decide⟩ 10 (transLenTr ⟨44, by decide⟩ 10 hp)) T106_44
      hfix106_44 hinj106_44 hcardT106_44
      (fun i => conj_mem_of_fixedPoints _ _ (T106_44 i) (hfix106_44 i) _)
      ⟨106, by decide⟩ ⟨44, by decide⟩ _
      (Q2.validAt ⟨106, by decide⟩ (Q2.listedAt ⟨106, by decide⟩
        (alnCheck_rep ⟨106, by decide⟩ hj hq).1))
      (colE2 ⟨44, by decide⟩ 10 hp) Q2.T106_44_2 Q2.hfix106_44_2 Q2.hinj106_44_2
      Q2.hcardT106_44_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T106_44_2 i) (Q2.hfix106_44_2 i) _)
      colCert_106_44_10.hD ?_).symm
  rw [alnId_106 j hj]


theorem leaf_106_44_15 (hp : 15 < (Q2.transData.getD 44 []).length)
    (j : Nat) (hj : j < (repChars.getD 106 []).length)
    (hq : (normIsRep.getD 106 []).getD j false = true) :
    species (Q2.reps (⟨44, by decide⟩ : Fin 148)) (colE2 ⟨44, by decide⟩ 15 hp)
        (rowE2 (⟨106, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨44, by decide⟩ : Fin 148))
        (colE1 ⟨44, by decide⟩ 15 (transLenTr ⟨44, by decide⟩ 15 hp))
        (rowE1 (⟨106, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨106, by decide⟩ : Fin 148) ⟨44, by decide⟩ _
      (validAt ⟨106, by decide⟩ (listedAt ⟨106, by decide⟩ hj))
      (colE1 ⟨44, by decide⟩ 15 (transLenTr ⟨44, by decide⟩ 15 hp)) T106_44
      hfix106_44 hinj106_44 hcardT106_44
      (fun i => conj_mem_of_fixedPoints _ _ (T106_44 i) (hfix106_44 i) _)
      ⟨106, by decide⟩ ⟨44, by decide⟩ _
      (Q2.validAt ⟨106, by decide⟩ (Q2.listedAt ⟨106, by decide⟩
        (alnCheck_rep ⟨106, by decide⟩ hj hq).1))
      (colE2 ⟨44, by decide⟩ 15 hp) Q2.T106_44_2 Q2.hfix106_44_2 Q2.hinj106_44_2
      Q2.hcardT106_44_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T106_44_2 i) (Q2.hfix106_44_2 i) _)
      colCert_106_44_15.hD ?_).symm
  rw [alnId_106 j hj]


theorem leaf_106_44_20 (hp : 20 < (Q2.transData.getD 44 []).length)
    (j : Nat) (hj : j < (repChars.getD 106 []).length)
    (hq : (normIsRep.getD 106 []).getD j false = true) :
    species (Q2.reps (⟨44, by decide⟩ : Fin 148)) (colE2 ⟨44, by decide⟩ 20 hp)
        (rowE2 (⟨106, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨44, by decide⟩ : Fin 148))
        (colE1 ⟨44, by decide⟩ 20 (transLenTr ⟨44, by decide⟩ 20 hp))
        (rowE1 (⟨106, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨106, by decide⟩ : Fin 148) ⟨44, by decide⟩ _
      (validAt ⟨106, by decide⟩ (listedAt ⟨106, by decide⟩ hj))
      (colE1 ⟨44, by decide⟩ 20 (transLenTr ⟨44, by decide⟩ 20 hp)) T106_44
      hfix106_44 hinj106_44 hcardT106_44
      (fun i => conj_mem_of_fixedPoints _ _ (T106_44 i) (hfix106_44 i) _)
      ⟨106, by decide⟩ ⟨44, by decide⟩ _
      (Q2.validAt ⟨106, by decide⟩ (Q2.listedAt ⟨106, by decide⟩
        (alnCheck_rep ⟨106, by decide⟩ hj hq).1))
      (colE2 ⟨44, by decide⟩ 20 hp) Q2.T106_44_2 Q2.hfix106_44_2 Q2.hinj106_44_2
      Q2.hcardT106_44_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T106_44_2 i) (Q2.hfix106_44_2 i) _)
      colCert_106_44_20.hD ?_).symm
  rw [alnId_106 j hj]


theorem leaf_106_53_0 (hp : 0 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 106 []).length)
    (hq : (normIsRep.getD 106 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 0 hp)
        (rowE2 (⟨106, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 0 (transLenTr ⟨53, by decide⟩ 0 hp))
        (rowE1 (⟨106, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨106, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨106, by decide⟩ (listedAt ⟨106, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 0 (transLenTr ⟨53, by decide⟩ 0 hp)) T106_53
      hfix106_53 hinj106_53 hcardT106_53
      (fun i => conj_mem_of_fixedPoints _ _ (T106_53 i) (hfix106_53 i) _)
      ⟨106, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨106, by decide⟩ (Q2.listedAt ⟨106, by decide⟩
        (alnCheck_rep ⟨106, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 0 hp) Q2.T106_53_2 Q2.hfix106_53_2 Q2.hinj106_53_2
      Q2.hcardT106_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T106_53_2 i) (Q2.hfix106_53_2 i) _)
      colCert_106_53_0.hD ?_).symm
  rw [alnId_106 j hj]


theorem leaf_106_53_1 (hp : 1 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 106 []).length)
    (hq : (normIsRep.getD 106 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 1 hp)
        (rowE2 (⟨106, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 1 (transLenTr ⟨53, by decide⟩ 1 hp))
        (rowE1 (⟨106, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨106, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨106, by decide⟩ (listedAt ⟨106, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 1 (transLenTr ⟨53, by decide⟩ 1 hp)) T106_53
      hfix106_53 hinj106_53 hcardT106_53
      (fun i => conj_mem_of_fixedPoints _ _ (T106_53 i) (hfix106_53 i) _)
      ⟨106, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨106, by decide⟩ (Q2.listedAt ⟨106, by decide⟩
        (alnCheck_rep ⟨106, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 1 hp) Q2.T106_53_2 Q2.hfix106_53_2 Q2.hinj106_53_2
      Q2.hcardT106_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T106_53_2 i) (Q2.hfix106_53_2 i) _)
      colCert_106_53_1.hD ?_).symm
  rw [alnId_106 j hj]


theorem leaf_106_53_2 (hp : 2 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 106 []).length)
    (hq : (normIsRep.getD 106 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 2 hp)
        (rowE2 (⟨106, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 2 (transLenTr ⟨53, by decide⟩ 2 hp))
        (rowE1 (⟨106, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨106, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨106, by decide⟩ (listedAt ⟨106, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 2 (transLenTr ⟨53, by decide⟩ 2 hp)) T106_53
      hfix106_53 hinj106_53 hcardT106_53
      (fun i => conj_mem_of_fixedPoints _ _ (T106_53 i) (hfix106_53 i) _)
      ⟨106, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨106, by decide⟩ (Q2.listedAt ⟨106, by decide⟩
        (alnCheck_rep ⟨106, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 2 hp) Q2.T106_53_2 Q2.hfix106_53_2 Q2.hinj106_53_2
      Q2.hcardT106_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T106_53_2 i) (Q2.hfix106_53_2 i) _)
      colCert_106_53_2.hD ?_).symm
  rw [alnId_106 j hj]


theorem leaf_106_53_3 (hp : 3 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 106 []).length)
    (hq : (normIsRep.getD 106 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 3 hp)
        (rowE2 (⟨106, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 3 (transLenTr ⟨53, by decide⟩ 3 hp))
        (rowE1 (⟨106, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨106, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨106, by decide⟩ (listedAt ⟨106, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 3 (transLenTr ⟨53, by decide⟩ 3 hp)) T106_53
      hfix106_53 hinj106_53 hcardT106_53
      (fun i => conj_mem_of_fixedPoints _ _ (T106_53 i) (hfix106_53 i) _)
      ⟨106, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨106, by decide⟩ (Q2.listedAt ⟨106, by decide⟩
        (alnCheck_rep ⟨106, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 3 hp) Q2.T106_53_2 Q2.hfix106_53_2 Q2.hinj106_53_2
      Q2.hcardT106_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T106_53_2 i) (Q2.hfix106_53_2 i) _)
      colCert_106_53_3.hD ?_).symm
  rw [alnId_106 j hj]


theorem leaf_106_53_4 (hp : 4 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 106 []).length)
    (hq : (normIsRep.getD 106 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 4 hp)
        (rowE2 (⟨106, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 4 (transLenTr ⟨53, by decide⟩ 4 hp))
        (rowE1 (⟨106, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨106, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨106, by decide⟩ (listedAt ⟨106, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 4 (transLenTr ⟨53, by decide⟩ 4 hp)) T106_53
      hfix106_53 hinj106_53 hcardT106_53
      (fun i => conj_mem_of_fixedPoints _ _ (T106_53 i) (hfix106_53 i) _)
      ⟨106, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨106, by decide⟩ (Q2.listedAt ⟨106, by decide⟩
        (alnCheck_rep ⟨106, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 4 hp) Q2.T106_53_2 Q2.hfix106_53_2 Q2.hinj106_53_2
      Q2.hcardT106_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T106_53_2 i) (Q2.hfix106_53_2 i) _)
      colCert_106_53_4.hD ?_).symm
  rw [alnId_106 j hj]


theorem leaf_106_53_5 (hp : 5 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 106 []).length)
    (hq : (normIsRep.getD 106 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 5 hp)
        (rowE2 (⟨106, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 5 (transLenTr ⟨53, by decide⟩ 5 hp))
        (rowE1 (⟨106, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨106, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨106, by decide⟩ (listedAt ⟨106, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 5 (transLenTr ⟨53, by decide⟩ 5 hp)) T106_53
      hfix106_53 hinj106_53 hcardT106_53
      (fun i => conj_mem_of_fixedPoints _ _ (T106_53 i) (hfix106_53 i) _)
      ⟨106, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨106, by decide⟩ (Q2.listedAt ⟨106, by decide⟩
        (alnCheck_rep ⟨106, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 5 hp) Q2.T106_53_2 Q2.hfix106_53_2 Q2.hinj106_53_2
      Q2.hcardT106_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T106_53_2 i) (Q2.hfix106_53_2 i) _)
      colCert_106_53_5.hD ?_).symm
  rw [alnId_106 j hj]


theorem leaf_106_53_10 (hp : 10 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 106 []).length)
    (hq : (normIsRep.getD 106 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 10 hp)
        (rowE2 (⟨106, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 10 (transLenTr ⟨53, by decide⟩ 10 hp))
        (rowE1 (⟨106, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨106, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨106, by decide⟩ (listedAt ⟨106, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 10 (transLenTr ⟨53, by decide⟩ 10 hp)) T106_53
      hfix106_53 hinj106_53 hcardT106_53
      (fun i => conj_mem_of_fixedPoints _ _ (T106_53 i) (hfix106_53 i) _)
      ⟨106, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨106, by decide⟩ (Q2.listedAt ⟨106, by decide⟩
        (alnCheck_rep ⟨106, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 10 hp) Q2.T106_53_2 Q2.hfix106_53_2 Q2.hinj106_53_2
      Q2.hcardT106_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T106_53_2 i) (Q2.hfix106_53_2 i) _)
      colCert_106_53_10.hD ?_).symm
  rw [alnId_106 j hj]


theorem leaf_106_53_15 (hp : 15 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 106 []).length)
    (hq : (normIsRep.getD 106 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 15 hp)
        (rowE2 (⟨106, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 15 (transLenTr ⟨53, by decide⟩ 15 hp))
        (rowE1 (⟨106, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨106, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨106, by decide⟩ (listedAt ⟨106, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 15 (transLenTr ⟨53, by decide⟩ 15 hp)) T106_53
      hfix106_53 hinj106_53 hcardT106_53
      (fun i => conj_mem_of_fixedPoints _ _ (T106_53 i) (hfix106_53 i) _)
      ⟨106, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨106, by decide⟩ (Q2.listedAt ⟨106, by decide⟩
        (alnCheck_rep ⟨106, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 15 hp) Q2.T106_53_2 Q2.hfix106_53_2 Q2.hinj106_53_2
      Q2.hcardT106_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T106_53_2 i) (Q2.hfix106_53_2 i) _)
      colCert_106_53_15.hD ?_).symm
  rw [alnId_106 j hj]


theorem leaf_106_53_20 (hp : 20 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 106 []).length)
    (hq : (normIsRep.getD 106 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 20 hp)
        (rowE2 (⟨106, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 20 (transLenTr ⟨53, by decide⟩ 20 hp))
        (rowE1 (⟨106, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨106, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨106, by decide⟩ (listedAt ⟨106, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 20 (transLenTr ⟨53, by decide⟩ 20 hp)) T106_53
      hfix106_53 hinj106_53 hcardT106_53
      (fun i => conj_mem_of_fixedPoints _ _ (T106_53 i) (hfix106_53 i) _)
      ⟨106, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨106, by decide⟩ (Q2.listedAt ⟨106, by decide⟩
        (alnCheck_rep ⟨106, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 20 hp) Q2.T106_53_2 Q2.hfix106_53_2 Q2.hinj106_53_2
      Q2.hcardT106_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T106_53_2 i) (Q2.hfix106_53_2 i) _)
      colCert_106_53_20.hD ?_).symm
  rw [alnId_106 j hj]


theorem leaf_106_106_0 (hp : 0 < (Q2.transData.getD 106 []).length)
    (j : Nat) (hj : j < (repChars.getD 106 []).length)
    (hq : (normIsRep.getD 106 []).getD j false = true) :
    species (Q2.reps (⟨106, by decide⟩ : Fin 148)) (colE2 ⟨106, by decide⟩ 0 hp)
        (rowE2 (⟨106, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨106, by decide⟩ : Fin 148))
        (colE1 ⟨106, by decide⟩ 0 (transLenTr ⟨106, by decide⟩ 0 hp))
        (rowE1 (⟨106, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨106, by decide⟩ : Fin 148) ⟨106, by decide⟩ _
      (validAt ⟨106, by decide⟩ (listedAt ⟨106, by decide⟩ hj))
      (colE1 ⟨106, by decide⟩ 0 (transLenTr ⟨106, by decide⟩ 0 hp)) T106_106
      hfix106_106 hinj106_106 hcardT106_106
      (fun i => conj_mem_of_fixedPoints _ _ (T106_106 i) (hfix106_106 i) _)
      ⟨106, by decide⟩ ⟨106, by decide⟩ _
      (Q2.validAt ⟨106, by decide⟩ (Q2.listedAt ⟨106, by decide⟩
        (alnCheck_rep ⟨106, by decide⟩ hj hq).1))
      (colE2 ⟨106, by decide⟩ 0 hp) Q2.T106_106_2 Q2.hfix106_106_2 Q2.hinj106_106_2
      Q2.hcardT106_106_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T106_106_2 i) (Q2.hfix106_106_2 i) _)
      colCert_106_106_0.hD ?_).symm
  rw [alnId_106 j hj]


theorem leaf_106_106_1 (hp : 1 < (Q2.transData.getD 106 []).length)
    (j : Nat) (hj : j < (repChars.getD 106 []).length)
    (hq : (normIsRep.getD 106 []).getD j false = true) :
    species (Q2.reps (⟨106, by decide⟩ : Fin 148)) (colE2 ⟨106, by decide⟩ 1 hp)
        (rowE2 (⟨106, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨106, by decide⟩ : Fin 148))
        (colE1 ⟨106, by decide⟩ 1 (transLenTr ⟨106, by decide⟩ 1 hp))
        (rowE1 (⟨106, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨106, by decide⟩ : Fin 148) ⟨106, by decide⟩ _
      (validAt ⟨106, by decide⟩ (listedAt ⟨106, by decide⟩ hj))
      (colE1 ⟨106, by decide⟩ 1 (transLenTr ⟨106, by decide⟩ 1 hp)) T106_106
      hfix106_106 hinj106_106 hcardT106_106
      (fun i => conj_mem_of_fixedPoints _ _ (T106_106 i) (hfix106_106 i) _)
      ⟨106, by decide⟩ ⟨106, by decide⟩ _
      (Q2.validAt ⟨106, by decide⟩ (Q2.listedAt ⟨106, by decide⟩
        (alnCheck_rep ⟨106, by decide⟩ hj hq).1))
      (colE2 ⟨106, by decide⟩ 1 hp) Q2.T106_106_2 Q2.hfix106_106_2 Q2.hinj106_106_2
      Q2.hcardT106_106_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T106_106_2 i) (Q2.hfix106_106_2 i) _)
      colCert_106_106_1.hD ?_).symm
  rw [alnId_106 j hj]


theorem leaf_106_106_2 (hp : 2 < (Q2.transData.getD 106 []).length)
    (j : Nat) (hj : j < (repChars.getD 106 []).length)
    (hq : (normIsRep.getD 106 []).getD j false = true) :
    species (Q2.reps (⟨106, by decide⟩ : Fin 148)) (colE2 ⟨106, by decide⟩ 2 hp)
        (rowE2 (⟨106, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨106, by decide⟩ : Fin 148))
        (colE1 ⟨106, by decide⟩ 2 (transLenTr ⟨106, by decide⟩ 2 hp))
        (rowE1 (⟨106, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨106, by decide⟩ : Fin 148) ⟨106, by decide⟩ _
      (validAt ⟨106, by decide⟩ (listedAt ⟨106, by decide⟩ hj))
      (colE1 ⟨106, by decide⟩ 2 (transLenTr ⟨106, by decide⟩ 2 hp)) T106_106
      hfix106_106 hinj106_106 hcardT106_106
      (fun i => conj_mem_of_fixedPoints _ _ (T106_106 i) (hfix106_106 i) _)
      ⟨106, by decide⟩ ⟨106, by decide⟩ _
      (Q2.validAt ⟨106, by decide⟩ (Q2.listedAt ⟨106, by decide⟩
        (alnCheck_rep ⟨106, by decide⟩ hj hq).1))
      (colE2 ⟨106, by decide⟩ 2 hp) Q2.T106_106_2 Q2.hfix106_106_2 Q2.hinj106_106_2
      Q2.hcardT106_106_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T106_106_2 i) (Q2.hfix106_106_2 i) _)
      colCert_106_106_2.hD ?_).symm
  rw [alnId_106 j hj]


theorem leaf_106_106_3 (hp : 3 < (Q2.transData.getD 106 []).length)
    (j : Nat) (hj : j < (repChars.getD 106 []).length)
    (hq : (normIsRep.getD 106 []).getD j false = true) :
    species (Q2.reps (⟨106, by decide⟩ : Fin 148)) (colE2 ⟨106, by decide⟩ 3 hp)
        (rowE2 (⟨106, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨106, by decide⟩ : Fin 148))
        (colE1 ⟨106, by decide⟩ 3 (transLenTr ⟨106, by decide⟩ 3 hp))
        (rowE1 (⟨106, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨106, by decide⟩ : Fin 148) ⟨106, by decide⟩ _
      (validAt ⟨106, by decide⟩ (listedAt ⟨106, by decide⟩ hj))
      (colE1 ⟨106, by decide⟩ 3 (transLenTr ⟨106, by decide⟩ 3 hp)) T106_106
      hfix106_106 hinj106_106 hcardT106_106
      (fun i => conj_mem_of_fixedPoints _ _ (T106_106 i) (hfix106_106 i) _)
      ⟨106, by decide⟩ ⟨106, by decide⟩ _
      (Q2.validAt ⟨106, by decide⟩ (Q2.listedAt ⟨106, by decide⟩
        (alnCheck_rep ⟨106, by decide⟩ hj hq).1))
      (colE2 ⟨106, by decide⟩ 3 hp) Q2.T106_106_2 Q2.hfix106_106_2 Q2.hinj106_106_2
      Q2.hcardT106_106_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T106_106_2 i) (Q2.hfix106_106_2 i) _)
      colCert_106_106_3.hD ?_).symm
  rw [alnId_106 j hj]


theorem leaf_106_106_4 (hp : 4 < (Q2.transData.getD 106 []).length)
    (j : Nat) (hj : j < (repChars.getD 106 []).length)
    (hq : (normIsRep.getD 106 []).getD j false = true) :
    species (Q2.reps (⟨106, by decide⟩ : Fin 148)) (colE2 ⟨106, by decide⟩ 4 hp)
        (rowE2 (⟨106, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨106, by decide⟩ : Fin 148))
        (colE1 ⟨106, by decide⟩ 4 (transLenTr ⟨106, by decide⟩ 4 hp))
        (rowE1 (⟨106, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨106, by decide⟩ : Fin 148) ⟨106, by decide⟩ _
      (validAt ⟨106, by decide⟩ (listedAt ⟨106, by decide⟩ hj))
      (colE1 ⟨106, by decide⟩ 4 (transLenTr ⟨106, by decide⟩ 4 hp)) T106_106
      hfix106_106 hinj106_106 hcardT106_106
      (fun i => conj_mem_of_fixedPoints _ _ (T106_106 i) (hfix106_106 i) _)
      ⟨106, by decide⟩ ⟨106, by decide⟩ _
      (Q2.validAt ⟨106, by decide⟩ (Q2.listedAt ⟨106, by decide⟩
        (alnCheck_rep ⟨106, by decide⟩ hj hq).1))
      (colE2 ⟨106, by decide⟩ 4 hp) Q2.T106_106_2 Q2.hfix106_106_2 Q2.hinj106_106_2
      Q2.hcardT106_106_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T106_106_2 i) (Q2.hfix106_106_2 i) _)
      colCert_106_106_4.hD ?_).symm
  rw [alnId_106 j hj]


theorem leaf_106_106_5 (hp : 5 < (Q2.transData.getD 106 []).length)
    (j : Nat) (hj : j < (repChars.getD 106 []).length)
    (hq : (normIsRep.getD 106 []).getD j false = true) :
    species (Q2.reps (⟨106, by decide⟩ : Fin 148)) (colE2 ⟨106, by decide⟩ 5 hp)
        (rowE2 (⟨106, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨106, by decide⟩ : Fin 148))
        (colE1 ⟨106, by decide⟩ 5 (transLenTr ⟨106, by decide⟩ 5 hp))
        (rowE1 (⟨106, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨106, by decide⟩ : Fin 148) ⟨106, by decide⟩ _
      (validAt ⟨106, by decide⟩ (listedAt ⟨106, by decide⟩ hj))
      (colE1 ⟨106, by decide⟩ 5 (transLenTr ⟨106, by decide⟩ 5 hp)) T106_106
      hfix106_106 hinj106_106 hcardT106_106
      (fun i => conj_mem_of_fixedPoints _ _ (T106_106 i) (hfix106_106 i) _)
      ⟨106, by decide⟩ ⟨106, by decide⟩ _
      (Q2.validAt ⟨106, by decide⟩ (Q2.listedAt ⟨106, by decide⟩
        (alnCheck_rep ⟨106, by decide⟩ hj hq).1))
      (colE2 ⟨106, by decide⟩ 5 hp) Q2.T106_106_2 Q2.hfix106_106_2 Q2.hinj106_106_2
      Q2.hcardT106_106_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T106_106_2 i) (Q2.hfix106_106_2 i) _)
      colCert_106_106_5.hD ?_).symm
  rw [alnId_106 j hj]


theorem leaf_106_106_10 (hp : 10 < (Q2.transData.getD 106 []).length)
    (j : Nat) (hj : j < (repChars.getD 106 []).length)
    (hq : (normIsRep.getD 106 []).getD j false = true) :
    species (Q2.reps (⟨106, by decide⟩ : Fin 148)) (colE2 ⟨106, by decide⟩ 10 hp)
        (rowE2 (⟨106, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨106, by decide⟩ : Fin 148))
        (colE1 ⟨106, by decide⟩ 10 (transLenTr ⟨106, by decide⟩ 10 hp))
        (rowE1 (⟨106, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨106, by decide⟩ : Fin 148) ⟨106, by decide⟩ _
      (validAt ⟨106, by decide⟩ (listedAt ⟨106, by decide⟩ hj))
      (colE1 ⟨106, by decide⟩ 10 (transLenTr ⟨106, by decide⟩ 10 hp)) T106_106
      hfix106_106 hinj106_106 hcardT106_106
      (fun i => conj_mem_of_fixedPoints _ _ (T106_106 i) (hfix106_106 i) _)
      ⟨106, by decide⟩ ⟨106, by decide⟩ _
      (Q2.validAt ⟨106, by decide⟩ (Q2.listedAt ⟨106, by decide⟩
        (alnCheck_rep ⟨106, by decide⟩ hj hq).1))
      (colE2 ⟨106, by decide⟩ 10 hp) Q2.T106_106_2 Q2.hfix106_106_2 Q2.hinj106_106_2
      Q2.hcardT106_106_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T106_106_2 i) (Q2.hfix106_106_2 i) _)
      colCert_106_106_10.hD ?_).symm
  rw [alnId_106 j hj]


theorem leaf_106_106_15 (hp : 15 < (Q2.transData.getD 106 []).length)
    (j : Nat) (hj : j < (repChars.getD 106 []).length)
    (hq : (normIsRep.getD 106 []).getD j false = true) :
    species (Q2.reps (⟨106, by decide⟩ : Fin 148)) (colE2 ⟨106, by decide⟩ 15 hp)
        (rowE2 (⟨106, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨106, by decide⟩ : Fin 148))
        (colE1 ⟨106, by decide⟩ 15 (transLenTr ⟨106, by decide⟩ 15 hp))
        (rowE1 (⟨106, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨106, by decide⟩ : Fin 148) ⟨106, by decide⟩ _
      (validAt ⟨106, by decide⟩ (listedAt ⟨106, by decide⟩ hj))
      (colE1 ⟨106, by decide⟩ 15 (transLenTr ⟨106, by decide⟩ 15 hp)) T106_106
      hfix106_106 hinj106_106 hcardT106_106
      (fun i => conj_mem_of_fixedPoints _ _ (T106_106 i) (hfix106_106 i) _)
      ⟨106, by decide⟩ ⟨106, by decide⟩ _
      (Q2.validAt ⟨106, by decide⟩ (Q2.listedAt ⟨106, by decide⟩
        (alnCheck_rep ⟨106, by decide⟩ hj hq).1))
      (colE2 ⟨106, by decide⟩ 15 hp) Q2.T106_106_2 Q2.hfix106_106_2 Q2.hinj106_106_2
      Q2.hcardT106_106_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T106_106_2 i) (Q2.hfix106_106_2 i) _)
      colCert_106_106_15.hD ?_).symm
  rw [alnId_106 j hj]


theorem leaf_106_106_20 (hp : 20 < (Q2.transData.getD 106 []).length)
    (j : Nat) (hj : j < (repChars.getD 106 []).length)
    (hq : (normIsRep.getD 106 []).getD j false = true) :
    species (Q2.reps (⟨106, by decide⟩ : Fin 148)) (colE2 ⟨106, by decide⟩ 20 hp)
        (rowE2 (⟨106, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨106, by decide⟩ : Fin 148))
        (colE1 ⟨106, by decide⟩ 20 (transLenTr ⟨106, by decide⟩ 20 hp))
        (rowE1 (⟨106, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨106, by decide⟩ : Fin 148) ⟨106, by decide⟩ _
      (validAt ⟨106, by decide⟩ (listedAt ⟨106, by decide⟩ hj))
      (colE1 ⟨106, by decide⟩ 20 (transLenTr ⟨106, by decide⟩ 20 hp)) T106_106
      hfix106_106 hinj106_106 hcardT106_106
      (fun i => conj_mem_of_fixedPoints _ _ (T106_106 i) (hfix106_106 i) _)
      ⟨106, by decide⟩ ⟨106, by decide⟩ _
      (Q2.validAt ⟨106, by decide⟩ (Q2.listedAt ⟨106, by decide⟩
        (alnCheck_rep ⟨106, by decide⟩ hj hq).1))
      (colE2 ⟨106, by decide⟩ 20 hp) Q2.T106_106_2 Q2.hfix106_106_2 Q2.hinj106_106_2
      Q2.hcardT106_106_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T106_106_2 i) (Q2.hfix106_106_2 i) _)
      colCert_106_106_20.hD ?_).symm
  rw [alnId_106 j hj]


theorem leaf_107_10_0 (hp : 0 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 107 []).length)
    (hq : (normIsRep.getD 107 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 0 hp)
        (rowE2 (⟨107, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 0 (transLenTr ⟨10, by decide⟩ 0 hp))
        (rowE1 (⟨107, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨107, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨107, by decide⟩ (listedAt ⟨107, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 0 (transLenTr ⟨10, by decide⟩ 0 hp)) T107_10
      hfix107_10 hinj107_10 hcardT107_10
      (fun i => conj_mem_of_fixedPoints _ _ (T107_10 i) (hfix107_10 i) _)
      ⟨107, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨107, by decide⟩ (Q2.listedAt ⟨107, by decide⟩
        (alnCheck_rep ⟨107, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 0 hp) Q2.T107_10_2 Q2.hfix107_10_2 Q2.hinj107_10_2
      Q2.hcardT107_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T107_10_2 i) (Q2.hfix107_10_2 i) _)
      colCert_107_10_0.hD ?_).symm
  rw [alnId_107 j hj]


theorem leaf_107_10_1 (hp : 1 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 107 []).length)
    (hq : (normIsRep.getD 107 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 1 hp)
        (rowE2 (⟨107, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 1 (transLenTr ⟨10, by decide⟩ 1 hp))
        (rowE1 (⟨107, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨107, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨107, by decide⟩ (listedAt ⟨107, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 1 (transLenTr ⟨10, by decide⟩ 1 hp)) T107_10
      hfix107_10 hinj107_10 hcardT107_10
      (fun i => conj_mem_of_fixedPoints _ _ (T107_10 i) (hfix107_10 i) _)
      ⟨107, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨107, by decide⟩ (Q2.listedAt ⟨107, by decide⟩
        (alnCheck_rep ⟨107, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 1 hp) Q2.T107_10_2 Q2.hfix107_10_2 Q2.hinj107_10_2
      Q2.hcardT107_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T107_10_2 i) (Q2.hfix107_10_2 i) _)
      colCert_107_10_1.hD ?_).symm
  rw [alnId_107 j hj]


theorem leaf_107_10_2 (hp : 2 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 107 []).length)
    (hq : (normIsRep.getD 107 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 2 hp)
        (rowE2 (⟨107, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 2 (transLenTr ⟨10, by decide⟩ 2 hp))
        (rowE1 (⟨107, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨107, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨107, by decide⟩ (listedAt ⟨107, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 2 (transLenTr ⟨10, by decide⟩ 2 hp)) T107_10
      hfix107_10 hinj107_10 hcardT107_10
      (fun i => conj_mem_of_fixedPoints _ _ (T107_10 i) (hfix107_10 i) _)
      ⟨107, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨107, by decide⟩ (Q2.listedAt ⟨107, by decide⟩
        (alnCheck_rep ⟨107, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 2 hp) Q2.T107_10_2 Q2.hfix107_10_2 Q2.hinj107_10_2
      Q2.hcardT107_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T107_10_2 i) (Q2.hfix107_10_2 i) _)
      colCert_107_10_2.hD ?_).symm
  rw [alnId_107 j hj]


theorem leaf_107_10_3 (hp : 3 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 107 []).length)
    (hq : (normIsRep.getD 107 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 3 hp)
        (rowE2 (⟨107, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 3 (transLenTr ⟨10, by decide⟩ 3 hp))
        (rowE1 (⟨107, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨107, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨107, by decide⟩ (listedAt ⟨107, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 3 (transLenTr ⟨10, by decide⟩ 3 hp)) T107_10
      hfix107_10 hinj107_10 hcardT107_10
      (fun i => conj_mem_of_fixedPoints _ _ (T107_10 i) (hfix107_10 i) _)
      ⟨107, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨107, by decide⟩ (Q2.listedAt ⟨107, by decide⟩
        (alnCheck_rep ⟨107, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 3 hp) Q2.T107_10_2 Q2.hfix107_10_2 Q2.hinj107_10_2
      Q2.hcardT107_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T107_10_2 i) (Q2.hfix107_10_2 i) _)
      colCert_107_10_3.hD ?_).symm
  rw [alnId_107 j hj]


theorem leaf_107_10_4 (hp : 4 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 107 []).length)
    (hq : (normIsRep.getD 107 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 4 hp)
        (rowE2 (⟨107, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 4 (transLenTr ⟨10, by decide⟩ 4 hp))
        (rowE1 (⟨107, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨107, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨107, by decide⟩ (listedAt ⟨107, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 4 (transLenTr ⟨10, by decide⟩ 4 hp)) T107_10
      hfix107_10 hinj107_10 hcardT107_10
      (fun i => conj_mem_of_fixedPoints _ _ (T107_10 i) (hfix107_10 i) _)
      ⟨107, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨107, by decide⟩ (Q2.listedAt ⟨107, by decide⟩
        (alnCheck_rep ⟨107, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 4 hp) Q2.T107_10_2 Q2.hfix107_10_2 Q2.hinj107_10_2
      Q2.hcardT107_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T107_10_2 i) (Q2.hfix107_10_2 i) _)
      colCert_107_10_4.hD ?_).symm
  rw [alnId_107 j hj]


theorem leaf_107_12_0 (hp : 0 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 107 []).length)
    (hq : (normIsRep.getD 107 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 0 hp)
        (rowE2 (⟨107, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp))
        (rowE1 (⟨107, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨107, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨107, by decide⟩ (listedAt ⟨107, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp)) T107_12
      hfix107_12 hinj107_12 hcardT107_12
      (fun i => conj_mem_of_fixedPoints _ _ (T107_12 i) (hfix107_12 i) _)
      ⟨107, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨107, by decide⟩ (Q2.listedAt ⟨107, by decide⟩
        (alnCheck_rep ⟨107, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 0 hp) Q2.T107_12_2 Q2.hfix107_12_2 Q2.hinj107_12_2
      Q2.hcardT107_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T107_12_2 i) (Q2.hfix107_12_2 i) _)
      colCert_107_12_0.hD ?_).symm
  rw [alnId_107 j hj]


theorem leaf_107_12_1 (hp : 1 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 107 []).length)
    (hq : (normIsRep.getD 107 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 1 hp)
        (rowE2 (⟨107, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp))
        (rowE1 (⟨107, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨107, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨107, by decide⟩ (listedAt ⟨107, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp)) T107_12
      hfix107_12 hinj107_12 hcardT107_12
      (fun i => conj_mem_of_fixedPoints _ _ (T107_12 i) (hfix107_12 i) _)
      ⟨107, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨107, by decide⟩ (Q2.listedAt ⟨107, by decide⟩
        (alnCheck_rep ⟨107, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 1 hp) Q2.T107_12_2 Q2.hfix107_12_2 Q2.hinj107_12_2
      Q2.hcardT107_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T107_12_2 i) (Q2.hfix107_12_2 i) _)
      colCert_107_12_1.hD ?_).symm
  rw [alnId_107 j hj]


theorem leaf_107_12_2 (hp : 2 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 107 []).length)
    (hq : (normIsRep.getD 107 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 2 hp)
        (rowE2 (⟨107, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp))
        (rowE1 (⟨107, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨107, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨107, by decide⟩ (listedAt ⟨107, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp)) T107_12
      hfix107_12 hinj107_12 hcardT107_12
      (fun i => conj_mem_of_fixedPoints _ _ (T107_12 i) (hfix107_12 i) _)
      ⟨107, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨107, by decide⟩ (Q2.listedAt ⟨107, by decide⟩
        (alnCheck_rep ⟨107, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 2 hp) Q2.T107_12_2 Q2.hfix107_12_2 Q2.hinj107_12_2
      Q2.hcardT107_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T107_12_2 i) (Q2.hfix107_12_2 i) _)
      colCert_107_12_2.hD ?_).symm
  rw [alnId_107 j hj]


theorem leaf_107_12_3 (hp : 3 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 107 []).length)
    (hq : (normIsRep.getD 107 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 3 hp)
        (rowE2 (⟨107, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp))
        (rowE1 (⟨107, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨107, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨107, by decide⟩ (listedAt ⟨107, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp)) T107_12
      hfix107_12 hinj107_12 hcardT107_12
      (fun i => conj_mem_of_fixedPoints _ _ (T107_12 i) (hfix107_12 i) _)
      ⟨107, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨107, by decide⟩ (Q2.listedAt ⟨107, by decide⟩
        (alnCheck_rep ⟨107, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 3 hp) Q2.T107_12_2 Q2.hfix107_12_2 Q2.hinj107_12_2
      Q2.hcardT107_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T107_12_2 i) (Q2.hfix107_12_2 i) _)
      colCert_107_12_3.hD ?_).symm
  rw [alnId_107 j hj]


theorem leaf_107_12_4 (hp : 4 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 107 []).length)
    (hq : (normIsRep.getD 107 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 4 hp)
        (rowE2 (⟨107, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp))
        (rowE1 (⟨107, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨107, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨107, by decide⟩ (listedAt ⟨107, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp)) T107_12
      hfix107_12 hinj107_12 hcardT107_12
      (fun i => conj_mem_of_fixedPoints _ _ (T107_12 i) (hfix107_12 i) _)
      ⟨107, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨107, by decide⟩ (Q2.listedAt ⟨107, by decide⟩
        (alnCheck_rep ⟨107, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 4 hp) Q2.T107_12_2 Q2.hfix107_12_2 Q2.hinj107_12_2
      Q2.hcardT107_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T107_12_2 i) (Q2.hfix107_12_2 i) _)
      colCert_107_12_4.hD ?_).symm
  rw [alnId_107 j hj]


theorem leaf_107_45_0 (hp : 0 < (Q2.transData.getD 45 []).length)
    (j : Nat) (hj : j < (repChars.getD 107 []).length)
    (hq : (normIsRep.getD 107 []).getD j false = true) :
    species (Q2.reps (⟨45, by decide⟩ : Fin 148)) (colE2 ⟨45, by decide⟩ 0 hp)
        (rowE2 (⟨107, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨45, by decide⟩ : Fin 148))
        (colE1 ⟨45, by decide⟩ 0 (transLenTr ⟨45, by decide⟩ 0 hp))
        (rowE1 (⟨107, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨107, by decide⟩ : Fin 148) ⟨45, by decide⟩ _
      (validAt ⟨107, by decide⟩ (listedAt ⟨107, by decide⟩ hj))
      (colE1 ⟨45, by decide⟩ 0 (transLenTr ⟨45, by decide⟩ 0 hp)) T107_45
      hfix107_45 hinj107_45 hcardT107_45
      (fun i => conj_mem_of_fixedPoints _ _ (T107_45 i) (hfix107_45 i) _)
      ⟨107, by decide⟩ ⟨45, by decide⟩ _
      (Q2.validAt ⟨107, by decide⟩ (Q2.listedAt ⟨107, by decide⟩
        (alnCheck_rep ⟨107, by decide⟩ hj hq).1))
      (colE2 ⟨45, by decide⟩ 0 hp) Q2.T107_45_2 Q2.hfix107_45_2 Q2.hinj107_45_2
      Q2.hcardT107_45_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T107_45_2 i) (Q2.hfix107_45_2 i) _)
      colCert_107_45_0.hD ?_).symm
  rw [alnId_107 j hj]


theorem leaf_107_45_1 (hp : 1 < (Q2.transData.getD 45 []).length)
    (j : Nat) (hj : j < (repChars.getD 107 []).length)
    (hq : (normIsRep.getD 107 []).getD j false = true) :
    species (Q2.reps (⟨45, by decide⟩ : Fin 148)) (colE2 ⟨45, by decide⟩ 1 hp)
        (rowE2 (⟨107, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨45, by decide⟩ : Fin 148))
        (colE1 ⟨45, by decide⟩ 1 (transLenTr ⟨45, by decide⟩ 1 hp))
        (rowE1 (⟨107, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨107, by decide⟩ : Fin 148) ⟨45, by decide⟩ _
      (validAt ⟨107, by decide⟩ (listedAt ⟨107, by decide⟩ hj))
      (colE1 ⟨45, by decide⟩ 1 (transLenTr ⟨45, by decide⟩ 1 hp)) T107_45
      hfix107_45 hinj107_45 hcardT107_45
      (fun i => conj_mem_of_fixedPoints _ _ (T107_45 i) (hfix107_45 i) _)
      ⟨107, by decide⟩ ⟨45, by decide⟩ _
      (Q2.validAt ⟨107, by decide⟩ (Q2.listedAt ⟨107, by decide⟩
        (alnCheck_rep ⟨107, by decide⟩ hj hq).1))
      (colE2 ⟨45, by decide⟩ 1 hp) Q2.T107_45_2 Q2.hfix107_45_2 Q2.hinj107_45_2
      Q2.hcardT107_45_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T107_45_2 i) (Q2.hfix107_45_2 i) _)
      colCert_107_45_1.hD ?_).symm
  rw [alnId_107 j hj]


theorem leaf_107_45_2 (hp : 2 < (Q2.transData.getD 45 []).length)
    (j : Nat) (hj : j < (repChars.getD 107 []).length)
    (hq : (normIsRep.getD 107 []).getD j false = true) :
    species (Q2.reps (⟨45, by decide⟩ : Fin 148)) (colE2 ⟨45, by decide⟩ 2 hp)
        (rowE2 (⟨107, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨45, by decide⟩ : Fin 148))
        (colE1 ⟨45, by decide⟩ 2 (transLenTr ⟨45, by decide⟩ 2 hp))
        (rowE1 (⟨107, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨107, by decide⟩ : Fin 148) ⟨45, by decide⟩ _
      (validAt ⟨107, by decide⟩ (listedAt ⟨107, by decide⟩ hj))
      (colE1 ⟨45, by decide⟩ 2 (transLenTr ⟨45, by decide⟩ 2 hp)) T107_45
      hfix107_45 hinj107_45 hcardT107_45
      (fun i => conj_mem_of_fixedPoints _ _ (T107_45 i) (hfix107_45 i) _)
      ⟨107, by decide⟩ ⟨45, by decide⟩ _
      (Q2.validAt ⟨107, by decide⟩ (Q2.listedAt ⟨107, by decide⟩
        (alnCheck_rep ⟨107, by decide⟩ hj hq).1))
      (colE2 ⟨45, by decide⟩ 2 hp) Q2.T107_45_2 Q2.hfix107_45_2 Q2.hinj107_45_2
      Q2.hcardT107_45_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T107_45_2 i) (Q2.hfix107_45_2 i) _)
      colCert_107_45_2.hD ?_).symm
  rw [alnId_107 j hj]


theorem leaf_107_45_3 (hp : 3 < (Q2.transData.getD 45 []).length)
    (j : Nat) (hj : j < (repChars.getD 107 []).length)
    (hq : (normIsRep.getD 107 []).getD j false = true) :
    species (Q2.reps (⟨45, by decide⟩ : Fin 148)) (colE2 ⟨45, by decide⟩ 3 hp)
        (rowE2 (⟨107, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨45, by decide⟩ : Fin 148))
        (colE1 ⟨45, by decide⟩ 3 (transLenTr ⟨45, by decide⟩ 3 hp))
        (rowE1 (⟨107, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨107, by decide⟩ : Fin 148) ⟨45, by decide⟩ _
      (validAt ⟨107, by decide⟩ (listedAt ⟨107, by decide⟩ hj))
      (colE1 ⟨45, by decide⟩ 3 (transLenTr ⟨45, by decide⟩ 3 hp)) T107_45
      hfix107_45 hinj107_45 hcardT107_45
      (fun i => conj_mem_of_fixedPoints _ _ (T107_45 i) (hfix107_45 i) _)
      ⟨107, by decide⟩ ⟨45, by decide⟩ _
      (Q2.validAt ⟨107, by decide⟩ (Q2.listedAt ⟨107, by decide⟩
        (alnCheck_rep ⟨107, by decide⟩ hj hq).1))
      (colE2 ⟨45, by decide⟩ 3 hp) Q2.T107_45_2 Q2.hfix107_45_2 Q2.hinj107_45_2
      Q2.hcardT107_45_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T107_45_2 i) (Q2.hfix107_45_2 i) _)
      colCert_107_45_3.hD ?_).symm
  rw [alnId_107 j hj]


theorem leaf_107_45_4 (hp : 4 < (Q2.transData.getD 45 []).length)
    (j : Nat) (hj : j < (repChars.getD 107 []).length)
    (hq : (normIsRep.getD 107 []).getD j false = true) :
    species (Q2.reps (⟨45, by decide⟩ : Fin 148)) (colE2 ⟨45, by decide⟩ 4 hp)
        (rowE2 (⟨107, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨45, by decide⟩ : Fin 148))
        (colE1 ⟨45, by decide⟩ 4 (transLenTr ⟨45, by decide⟩ 4 hp))
        (rowE1 (⟨107, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨107, by decide⟩ : Fin 148) ⟨45, by decide⟩ _
      (validAt ⟨107, by decide⟩ (listedAt ⟨107, by decide⟩ hj))
      (colE1 ⟨45, by decide⟩ 4 (transLenTr ⟨45, by decide⟩ 4 hp)) T107_45
      hfix107_45 hinj107_45 hcardT107_45
      (fun i => conj_mem_of_fixedPoints _ _ (T107_45 i) (hfix107_45 i) _)
      ⟨107, by decide⟩ ⟨45, by decide⟩ _
      (Q2.validAt ⟨107, by decide⟩ (Q2.listedAt ⟨107, by decide⟩
        (alnCheck_rep ⟨107, by decide⟩ hj hq).1))
      (colE2 ⟨45, by decide⟩ 4 hp) Q2.T107_45_2 Q2.hfix107_45_2 Q2.hinj107_45_2
      Q2.hcardT107_45_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T107_45_2 i) (Q2.hfix107_45_2 i) _)
      colCert_107_45_4.hD ?_).symm
  rw [alnId_107 j hj]


theorem leaf_107_45_5 (hp : 5 < (Q2.transData.getD 45 []).length)
    (j : Nat) (hj : j < (repChars.getD 107 []).length)
    (hq : (normIsRep.getD 107 []).getD j false = true) :
    species (Q2.reps (⟨45, by decide⟩ : Fin 148)) (colE2 ⟨45, by decide⟩ 5 hp)
        (rowE2 (⟨107, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨45, by decide⟩ : Fin 148))
        (colE1 ⟨45, by decide⟩ 5 (transLenTr ⟨45, by decide⟩ 5 hp))
        (rowE1 (⟨107, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨107, by decide⟩ : Fin 148) ⟨45, by decide⟩ _
      (validAt ⟨107, by decide⟩ (listedAt ⟨107, by decide⟩ hj))
      (colE1 ⟨45, by decide⟩ 5 (transLenTr ⟨45, by decide⟩ 5 hp)) T107_45
      hfix107_45 hinj107_45 hcardT107_45
      (fun i => conj_mem_of_fixedPoints _ _ (T107_45 i) (hfix107_45 i) _)
      ⟨107, by decide⟩ ⟨45, by decide⟩ _
      (Q2.validAt ⟨107, by decide⟩ (Q2.listedAt ⟨107, by decide⟩
        (alnCheck_rep ⟨107, by decide⟩ hj hq).1))
      (colE2 ⟨45, by decide⟩ 5 hp) Q2.T107_45_2 Q2.hfix107_45_2 Q2.hinj107_45_2
      Q2.hcardT107_45_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T107_45_2 i) (Q2.hfix107_45_2 i) _)
      ?_).symm
  rw [show colData1 (⟨107, by decide⟩ : Fin 148)
        ((colE1 ⟨45, by decide⟩ 5 (transLenTr ⟨45, by decide⟩ 5 hp) : ↥(reps ⟨45, by decide⟩)) : Coordinate 1)
        T107_45 = colFn colCertDiv_107_45_5.D1 (m := 25) from colCertDiv_107_45_5.bind1,
    show colData2 (⟨107, by decide⟩ : Fin 148)
        ((colE2 ⟨45, by decide⟩ 5 hp : ↥(Q2.reps ⟨45, by decide⟩)) : Coordinate 2)
        Q2.T107_45_2 = colFn colCertDiv_107_45_5.D2 (m := 25) from colCertDiv_107_45_5.bind2]
  rw [alnId_107 j hj]
  exact fastcode_of_div ⟨107, by decide⟩ _ _ _
    ((alnId_107 j hj) ▸ Q2.listedAt (⟨107, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨107, by decide⟩ : Fin 148) hj hq).1) colCertDiv_107_45_5_match


theorem leaf_107_45_10 (hp : 10 < (Q2.transData.getD 45 []).length)
    (j : Nat) (hj : j < (repChars.getD 107 []).length)
    (hq : (normIsRep.getD 107 []).getD j false = true) :
    species (Q2.reps (⟨45, by decide⟩ : Fin 148)) (colE2 ⟨45, by decide⟩ 10 hp)
        (rowE2 (⟨107, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨45, by decide⟩ : Fin 148))
        (colE1 ⟨45, by decide⟩ 10 (transLenTr ⟨45, by decide⟩ 10 hp))
        (rowE1 (⟨107, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨107, by decide⟩ : Fin 148) ⟨45, by decide⟩ _
      (validAt ⟨107, by decide⟩ (listedAt ⟨107, by decide⟩ hj))
      (colE1 ⟨45, by decide⟩ 10 (transLenTr ⟨45, by decide⟩ 10 hp)) T107_45
      hfix107_45 hinj107_45 hcardT107_45
      (fun i => conj_mem_of_fixedPoints _ _ (T107_45 i) (hfix107_45 i) _)
      ⟨107, by decide⟩ ⟨45, by decide⟩ _
      (Q2.validAt ⟨107, by decide⟩ (Q2.listedAt ⟨107, by decide⟩
        (alnCheck_rep ⟨107, by decide⟩ hj hq).1))
      (colE2 ⟨45, by decide⟩ 10 hp) Q2.T107_45_2 Q2.hfix107_45_2 Q2.hinj107_45_2
      Q2.hcardT107_45_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T107_45_2 i) (Q2.hfix107_45_2 i) _)
      ?_).symm
  rw [show colData1 (⟨107, by decide⟩ : Fin 148)
        ((colE1 ⟨45, by decide⟩ 10 (transLenTr ⟨45, by decide⟩ 10 hp) : ↥(reps ⟨45, by decide⟩)) : Coordinate 1)
        T107_45 = colFn colCertDiv_107_45_10.D1 (m := 25) from colCertDiv_107_45_10.bind1,
    show colData2 (⟨107, by decide⟩ : Fin 148)
        ((colE2 ⟨45, by decide⟩ 10 hp : ↥(Q2.reps ⟨45, by decide⟩)) : Coordinate 2)
        Q2.T107_45_2 = colFn colCertDiv_107_45_10.D2 (m := 25) from colCertDiv_107_45_10.bind2]
  rw [alnId_107 j hj]
  exact fastcode_of_div ⟨107, by decide⟩ _ _ _
    ((alnId_107 j hj) ▸ Q2.listedAt (⟨107, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨107, by decide⟩ : Fin 148) hj hq).1) colCertDiv_107_45_10_match


theorem leaf_107_45_15 (hp : 15 < (Q2.transData.getD 45 []).length)
    (j : Nat) (hj : j < (repChars.getD 107 []).length)
    (hq : (normIsRep.getD 107 []).getD j false = true) :
    species (Q2.reps (⟨45, by decide⟩ : Fin 148)) (colE2 ⟨45, by decide⟩ 15 hp)
        (rowE2 (⟨107, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨45, by decide⟩ : Fin 148))
        (colE1 ⟨45, by decide⟩ 15 (transLenTr ⟨45, by decide⟩ 15 hp))
        (rowE1 (⟨107, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨107, by decide⟩ : Fin 148) ⟨45, by decide⟩ _
      (validAt ⟨107, by decide⟩ (listedAt ⟨107, by decide⟩ hj))
      (colE1 ⟨45, by decide⟩ 15 (transLenTr ⟨45, by decide⟩ 15 hp)) T107_45
      hfix107_45 hinj107_45 hcardT107_45
      (fun i => conj_mem_of_fixedPoints _ _ (T107_45 i) (hfix107_45 i) _)
      ⟨107, by decide⟩ ⟨45, by decide⟩ _
      (Q2.validAt ⟨107, by decide⟩ (Q2.listedAt ⟨107, by decide⟩
        (alnCheck_rep ⟨107, by decide⟩ hj hq).1))
      (colE2 ⟨45, by decide⟩ 15 hp) Q2.T107_45_2 Q2.hfix107_45_2 Q2.hinj107_45_2
      Q2.hcardT107_45_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T107_45_2 i) (Q2.hfix107_45_2 i) _)
      ?_).symm
  rw [show colData1 (⟨107, by decide⟩ : Fin 148)
        ((colE1 ⟨45, by decide⟩ 15 (transLenTr ⟨45, by decide⟩ 15 hp) : ↥(reps ⟨45, by decide⟩)) : Coordinate 1)
        T107_45 = colFn colCertDiv_107_45_15.D1 (m := 25) from colCertDiv_107_45_15.bind1,
    show colData2 (⟨107, by decide⟩ : Fin 148)
        ((colE2 ⟨45, by decide⟩ 15 hp : ↥(Q2.reps ⟨45, by decide⟩)) : Coordinate 2)
        Q2.T107_45_2 = colFn colCertDiv_107_45_15.D2 (m := 25) from colCertDiv_107_45_15.bind2]
  rw [alnId_107 j hj]
  exact fastcode_of_div ⟨107, by decide⟩ _ _ _
    ((alnId_107 j hj) ▸ Q2.listedAt (⟨107, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨107, by decide⟩ : Fin 148) hj hq).1) colCertDiv_107_45_15_match


theorem leaf_107_45_20 (hp : 20 < (Q2.transData.getD 45 []).length)
    (j : Nat) (hj : j < (repChars.getD 107 []).length)
    (hq : (normIsRep.getD 107 []).getD j false = true) :
    species (Q2.reps (⟨45, by decide⟩ : Fin 148)) (colE2 ⟨45, by decide⟩ 20 hp)
        (rowE2 (⟨107, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨45, by decide⟩ : Fin 148))
        (colE1 ⟨45, by decide⟩ 20 (transLenTr ⟨45, by decide⟩ 20 hp))
        (rowE1 (⟨107, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨107, by decide⟩ : Fin 148) ⟨45, by decide⟩ _
      (validAt ⟨107, by decide⟩ (listedAt ⟨107, by decide⟩ hj))
      (colE1 ⟨45, by decide⟩ 20 (transLenTr ⟨45, by decide⟩ 20 hp)) T107_45
      hfix107_45 hinj107_45 hcardT107_45
      (fun i => conj_mem_of_fixedPoints _ _ (T107_45 i) (hfix107_45 i) _)
      ⟨107, by decide⟩ ⟨45, by decide⟩ _
      (Q2.validAt ⟨107, by decide⟩ (Q2.listedAt ⟨107, by decide⟩
        (alnCheck_rep ⟨107, by decide⟩ hj hq).1))
      (colE2 ⟨45, by decide⟩ 20 hp) Q2.T107_45_2 Q2.hfix107_45_2 Q2.hinj107_45_2
      Q2.hcardT107_45_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T107_45_2 i) (Q2.hfix107_45_2 i) _)
      ?_).symm
  rw [show colData1 (⟨107, by decide⟩ : Fin 148)
        ((colE1 ⟨45, by decide⟩ 20 (transLenTr ⟨45, by decide⟩ 20 hp) : ↥(reps ⟨45, by decide⟩)) : Coordinate 1)
        T107_45 = colFn colCertDiv_107_45_20.D1 (m := 25) from colCertDiv_107_45_20.bind1,
    show colData2 (⟨107, by decide⟩ : Fin 148)
        ((colE2 ⟨45, by decide⟩ 20 hp : ↥(Q2.reps ⟨45, by decide⟩)) : Coordinate 2)
        Q2.T107_45_2 = colFn colCertDiv_107_45_20.D2 (m := 25) from colCertDiv_107_45_20.bind2]
  rw [alnId_107 j hj]
  exact fastcode_of_div ⟨107, by decide⟩ _ _ _
    ((alnId_107 j hj) ▸ Q2.listedAt (⟨107, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨107, by decide⟩ : Fin 148) hj hq).1) colCertDiv_107_45_20_match


theorem leaf_107_53_0 (hp : 0 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 107 []).length)
    (hq : (normIsRep.getD 107 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 0 hp)
        (rowE2 (⟨107, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 0 (transLenTr ⟨53, by decide⟩ 0 hp))
        (rowE1 (⟨107, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨107, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨107, by decide⟩ (listedAt ⟨107, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 0 (transLenTr ⟨53, by decide⟩ 0 hp)) T107_53
      hfix107_53 hinj107_53 hcardT107_53
      (fun i => conj_mem_of_fixedPoints _ _ (T107_53 i) (hfix107_53 i) _)
      ⟨107, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨107, by decide⟩ (Q2.listedAt ⟨107, by decide⟩
        (alnCheck_rep ⟨107, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 0 hp) Q2.T107_53_2 Q2.hfix107_53_2 Q2.hinj107_53_2
      Q2.hcardT107_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T107_53_2 i) (Q2.hfix107_53_2 i) _)
      colCert_107_53_0.hD ?_).symm
  rw [alnId_107 j hj]


theorem leaf_107_53_1 (hp : 1 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 107 []).length)
    (hq : (normIsRep.getD 107 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 1 hp)
        (rowE2 (⟨107, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 1 (transLenTr ⟨53, by decide⟩ 1 hp))
        (rowE1 (⟨107, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨107, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨107, by decide⟩ (listedAt ⟨107, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 1 (transLenTr ⟨53, by decide⟩ 1 hp)) T107_53
      hfix107_53 hinj107_53 hcardT107_53
      (fun i => conj_mem_of_fixedPoints _ _ (T107_53 i) (hfix107_53 i) _)
      ⟨107, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨107, by decide⟩ (Q2.listedAt ⟨107, by decide⟩
        (alnCheck_rep ⟨107, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 1 hp) Q2.T107_53_2 Q2.hfix107_53_2 Q2.hinj107_53_2
      Q2.hcardT107_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T107_53_2 i) (Q2.hfix107_53_2 i) _)
      colCert_107_53_1.hD ?_).symm
  rw [alnId_107 j hj]


theorem leaf_107_53_2 (hp : 2 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 107 []).length)
    (hq : (normIsRep.getD 107 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 2 hp)
        (rowE2 (⟨107, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 2 (transLenTr ⟨53, by decide⟩ 2 hp))
        (rowE1 (⟨107, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨107, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨107, by decide⟩ (listedAt ⟨107, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 2 (transLenTr ⟨53, by decide⟩ 2 hp)) T107_53
      hfix107_53 hinj107_53 hcardT107_53
      (fun i => conj_mem_of_fixedPoints _ _ (T107_53 i) (hfix107_53 i) _)
      ⟨107, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨107, by decide⟩ (Q2.listedAt ⟨107, by decide⟩
        (alnCheck_rep ⟨107, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 2 hp) Q2.T107_53_2 Q2.hfix107_53_2 Q2.hinj107_53_2
      Q2.hcardT107_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T107_53_2 i) (Q2.hfix107_53_2 i) _)
      colCert_107_53_2.hD ?_).symm
  rw [alnId_107 j hj]


theorem leaf_107_53_3 (hp : 3 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 107 []).length)
    (hq : (normIsRep.getD 107 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 3 hp)
        (rowE2 (⟨107, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 3 (transLenTr ⟨53, by decide⟩ 3 hp))
        (rowE1 (⟨107, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨107, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨107, by decide⟩ (listedAt ⟨107, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 3 (transLenTr ⟨53, by decide⟩ 3 hp)) T107_53
      hfix107_53 hinj107_53 hcardT107_53
      (fun i => conj_mem_of_fixedPoints _ _ (T107_53 i) (hfix107_53 i) _)
      ⟨107, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨107, by decide⟩ (Q2.listedAt ⟨107, by decide⟩
        (alnCheck_rep ⟨107, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 3 hp) Q2.T107_53_2 Q2.hfix107_53_2 Q2.hinj107_53_2
      Q2.hcardT107_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T107_53_2 i) (Q2.hfix107_53_2 i) _)
      colCert_107_53_3.hD ?_).symm
  rw [alnId_107 j hj]


theorem leaf_107_53_4 (hp : 4 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 107 []).length)
    (hq : (normIsRep.getD 107 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 4 hp)
        (rowE2 (⟨107, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 4 (transLenTr ⟨53, by decide⟩ 4 hp))
        (rowE1 (⟨107, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨107, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨107, by decide⟩ (listedAt ⟨107, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 4 (transLenTr ⟨53, by decide⟩ 4 hp)) T107_53
      hfix107_53 hinj107_53 hcardT107_53
      (fun i => conj_mem_of_fixedPoints _ _ (T107_53 i) (hfix107_53 i) _)
      ⟨107, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨107, by decide⟩ (Q2.listedAt ⟨107, by decide⟩
        (alnCheck_rep ⟨107, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 4 hp) Q2.T107_53_2 Q2.hfix107_53_2 Q2.hinj107_53_2
      Q2.hcardT107_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T107_53_2 i) (Q2.hfix107_53_2 i) _)
      colCert_107_53_4.hD ?_).symm
  rw [alnId_107 j hj]


theorem leaf_107_53_5 (hp : 5 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 107 []).length)
    (hq : (normIsRep.getD 107 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 5 hp)
        (rowE2 (⟨107, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 5 (transLenTr ⟨53, by decide⟩ 5 hp))
        (rowE1 (⟨107, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨107, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨107, by decide⟩ (listedAt ⟨107, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 5 (transLenTr ⟨53, by decide⟩ 5 hp)) T107_53
      hfix107_53 hinj107_53 hcardT107_53
      (fun i => conj_mem_of_fixedPoints _ _ (T107_53 i) (hfix107_53 i) _)
      ⟨107, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨107, by decide⟩ (Q2.listedAt ⟨107, by decide⟩
        (alnCheck_rep ⟨107, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 5 hp) Q2.T107_53_2 Q2.hfix107_53_2 Q2.hinj107_53_2
      Q2.hcardT107_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T107_53_2 i) (Q2.hfix107_53_2 i) _)
      colCert_107_53_5.hD ?_).symm
  rw [alnId_107 j hj]


theorem leaf_107_53_10 (hp : 10 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 107 []).length)
    (hq : (normIsRep.getD 107 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 10 hp)
        (rowE2 (⟨107, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 10 (transLenTr ⟨53, by decide⟩ 10 hp))
        (rowE1 (⟨107, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨107, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨107, by decide⟩ (listedAt ⟨107, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 10 (transLenTr ⟨53, by decide⟩ 10 hp)) T107_53
      hfix107_53 hinj107_53 hcardT107_53
      (fun i => conj_mem_of_fixedPoints _ _ (T107_53 i) (hfix107_53 i) _)
      ⟨107, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨107, by decide⟩ (Q2.listedAt ⟨107, by decide⟩
        (alnCheck_rep ⟨107, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 10 hp) Q2.T107_53_2 Q2.hfix107_53_2 Q2.hinj107_53_2
      Q2.hcardT107_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T107_53_2 i) (Q2.hfix107_53_2 i) _)
      colCert_107_53_10.hD ?_).symm
  rw [alnId_107 j hj]


theorem leaf_107_53_15 (hp : 15 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 107 []).length)
    (hq : (normIsRep.getD 107 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 15 hp)
        (rowE2 (⟨107, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 15 (transLenTr ⟨53, by decide⟩ 15 hp))
        (rowE1 (⟨107, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨107, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨107, by decide⟩ (listedAt ⟨107, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 15 (transLenTr ⟨53, by decide⟩ 15 hp)) T107_53
      hfix107_53 hinj107_53 hcardT107_53
      (fun i => conj_mem_of_fixedPoints _ _ (T107_53 i) (hfix107_53 i) _)
      ⟨107, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨107, by decide⟩ (Q2.listedAt ⟨107, by decide⟩
        (alnCheck_rep ⟨107, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 15 hp) Q2.T107_53_2 Q2.hfix107_53_2 Q2.hinj107_53_2
      Q2.hcardT107_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T107_53_2 i) (Q2.hfix107_53_2 i) _)
      colCert_107_53_15.hD ?_).symm
  rw [alnId_107 j hj]


theorem leaf_107_53_20 (hp : 20 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 107 []).length)
    (hq : (normIsRep.getD 107 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 20 hp)
        (rowE2 (⟨107, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 20 (transLenTr ⟨53, by decide⟩ 20 hp))
        (rowE1 (⟨107, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨107, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨107, by decide⟩ (listedAt ⟨107, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 20 (transLenTr ⟨53, by decide⟩ 20 hp)) T107_53
      hfix107_53 hinj107_53 hcardT107_53
      (fun i => conj_mem_of_fixedPoints _ _ (T107_53 i) (hfix107_53 i) _)
      ⟨107, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨107, by decide⟩ (Q2.listedAt ⟨107, by decide⟩
        (alnCheck_rep ⟨107, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 20 hp) Q2.T107_53_2 Q2.hfix107_53_2 Q2.hinj107_53_2
      Q2.hcardT107_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T107_53_2 i) (Q2.hfix107_53_2 i) _)
      colCert_107_53_20.hD ?_).symm
  rw [alnId_107 j hj]


theorem leaf_107_107_0 (hp : 0 < (Q2.transData.getD 107 []).length)
    (j : Nat) (hj : j < (repChars.getD 107 []).length)
    (hq : (normIsRep.getD 107 []).getD j false = true) :
    species (Q2.reps (⟨107, by decide⟩ : Fin 148)) (colE2 ⟨107, by decide⟩ 0 hp)
        (rowE2 (⟨107, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨107, by decide⟩ : Fin 148))
        (colE1 ⟨107, by decide⟩ 0 (transLenTr ⟨107, by decide⟩ 0 hp))
        (rowE1 (⟨107, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨107, by decide⟩ : Fin 148) ⟨107, by decide⟩ _
      (validAt ⟨107, by decide⟩ (listedAt ⟨107, by decide⟩ hj))
      (colE1 ⟨107, by decide⟩ 0 (transLenTr ⟨107, by decide⟩ 0 hp)) T107_107
      hfix107_107 hinj107_107 hcardT107_107
      (fun i => conj_mem_of_fixedPoints _ _ (T107_107 i) (hfix107_107 i) _)
      ⟨107, by decide⟩ ⟨107, by decide⟩ _
      (Q2.validAt ⟨107, by decide⟩ (Q2.listedAt ⟨107, by decide⟩
        (alnCheck_rep ⟨107, by decide⟩ hj hq).1))
      (colE2 ⟨107, by decide⟩ 0 hp) Q2.T107_107_2 Q2.hfix107_107_2 Q2.hinj107_107_2
      Q2.hcardT107_107_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T107_107_2 i) (Q2.hfix107_107_2 i) _)
      colCert_107_107_0.hD ?_).symm
  rw [alnId_107 j hj]


theorem leaf_107_107_1 (hp : 1 < (Q2.transData.getD 107 []).length)
    (j : Nat) (hj : j < (repChars.getD 107 []).length)
    (hq : (normIsRep.getD 107 []).getD j false = true) :
    species (Q2.reps (⟨107, by decide⟩ : Fin 148)) (colE2 ⟨107, by decide⟩ 1 hp)
        (rowE2 (⟨107, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨107, by decide⟩ : Fin 148))
        (colE1 ⟨107, by decide⟩ 1 (transLenTr ⟨107, by decide⟩ 1 hp))
        (rowE1 (⟨107, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨107, by decide⟩ : Fin 148) ⟨107, by decide⟩ _
      (validAt ⟨107, by decide⟩ (listedAt ⟨107, by decide⟩ hj))
      (colE1 ⟨107, by decide⟩ 1 (transLenTr ⟨107, by decide⟩ 1 hp)) T107_107
      hfix107_107 hinj107_107 hcardT107_107
      (fun i => conj_mem_of_fixedPoints _ _ (T107_107 i) (hfix107_107 i) _)
      ⟨107, by decide⟩ ⟨107, by decide⟩ _
      (Q2.validAt ⟨107, by decide⟩ (Q2.listedAt ⟨107, by decide⟩
        (alnCheck_rep ⟨107, by decide⟩ hj hq).1))
      (colE2 ⟨107, by decide⟩ 1 hp) Q2.T107_107_2 Q2.hfix107_107_2 Q2.hinj107_107_2
      Q2.hcardT107_107_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T107_107_2 i) (Q2.hfix107_107_2 i) _)
      colCert_107_107_1.hD ?_).symm
  rw [alnId_107 j hj]


theorem leaf_107_107_2 (hp : 2 < (Q2.transData.getD 107 []).length)
    (j : Nat) (hj : j < (repChars.getD 107 []).length)
    (hq : (normIsRep.getD 107 []).getD j false = true) :
    species (Q2.reps (⟨107, by decide⟩ : Fin 148)) (colE2 ⟨107, by decide⟩ 2 hp)
        (rowE2 (⟨107, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨107, by decide⟩ : Fin 148))
        (colE1 ⟨107, by decide⟩ 2 (transLenTr ⟨107, by decide⟩ 2 hp))
        (rowE1 (⟨107, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨107, by decide⟩ : Fin 148) ⟨107, by decide⟩ _
      (validAt ⟨107, by decide⟩ (listedAt ⟨107, by decide⟩ hj))
      (colE1 ⟨107, by decide⟩ 2 (transLenTr ⟨107, by decide⟩ 2 hp)) T107_107
      hfix107_107 hinj107_107 hcardT107_107
      (fun i => conj_mem_of_fixedPoints _ _ (T107_107 i) (hfix107_107 i) _)
      ⟨107, by decide⟩ ⟨107, by decide⟩ _
      (Q2.validAt ⟨107, by decide⟩ (Q2.listedAt ⟨107, by decide⟩
        (alnCheck_rep ⟨107, by decide⟩ hj hq).1))
      (colE2 ⟨107, by decide⟩ 2 hp) Q2.T107_107_2 Q2.hfix107_107_2 Q2.hinj107_107_2
      Q2.hcardT107_107_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T107_107_2 i) (Q2.hfix107_107_2 i) _)
      colCert_107_107_2.hD ?_).symm
  rw [alnId_107 j hj]


theorem leaf_107_107_3 (hp : 3 < (Q2.transData.getD 107 []).length)
    (j : Nat) (hj : j < (repChars.getD 107 []).length)
    (hq : (normIsRep.getD 107 []).getD j false = true) :
    species (Q2.reps (⟨107, by decide⟩ : Fin 148)) (colE2 ⟨107, by decide⟩ 3 hp)
        (rowE2 (⟨107, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨107, by decide⟩ : Fin 148))
        (colE1 ⟨107, by decide⟩ 3 (transLenTr ⟨107, by decide⟩ 3 hp))
        (rowE1 (⟨107, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨107, by decide⟩ : Fin 148) ⟨107, by decide⟩ _
      (validAt ⟨107, by decide⟩ (listedAt ⟨107, by decide⟩ hj))
      (colE1 ⟨107, by decide⟩ 3 (transLenTr ⟨107, by decide⟩ 3 hp)) T107_107
      hfix107_107 hinj107_107 hcardT107_107
      (fun i => conj_mem_of_fixedPoints _ _ (T107_107 i) (hfix107_107 i) _)
      ⟨107, by decide⟩ ⟨107, by decide⟩ _
      (Q2.validAt ⟨107, by decide⟩ (Q2.listedAt ⟨107, by decide⟩
        (alnCheck_rep ⟨107, by decide⟩ hj hq).1))
      (colE2 ⟨107, by decide⟩ 3 hp) Q2.T107_107_2 Q2.hfix107_107_2 Q2.hinj107_107_2
      Q2.hcardT107_107_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T107_107_2 i) (Q2.hfix107_107_2 i) _)
      colCert_107_107_3.hD ?_).symm
  rw [alnId_107 j hj]


theorem leaf_107_107_4 (hp : 4 < (Q2.transData.getD 107 []).length)
    (j : Nat) (hj : j < (repChars.getD 107 []).length)
    (hq : (normIsRep.getD 107 []).getD j false = true) :
    species (Q2.reps (⟨107, by decide⟩ : Fin 148)) (colE2 ⟨107, by decide⟩ 4 hp)
        (rowE2 (⟨107, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨107, by decide⟩ : Fin 148))
        (colE1 ⟨107, by decide⟩ 4 (transLenTr ⟨107, by decide⟩ 4 hp))
        (rowE1 (⟨107, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨107, by decide⟩ : Fin 148) ⟨107, by decide⟩ _
      (validAt ⟨107, by decide⟩ (listedAt ⟨107, by decide⟩ hj))
      (colE1 ⟨107, by decide⟩ 4 (transLenTr ⟨107, by decide⟩ 4 hp)) T107_107
      hfix107_107 hinj107_107 hcardT107_107
      (fun i => conj_mem_of_fixedPoints _ _ (T107_107 i) (hfix107_107 i) _)
      ⟨107, by decide⟩ ⟨107, by decide⟩ _
      (Q2.validAt ⟨107, by decide⟩ (Q2.listedAt ⟨107, by decide⟩
        (alnCheck_rep ⟨107, by decide⟩ hj hq).1))
      (colE2 ⟨107, by decide⟩ 4 hp) Q2.T107_107_2 Q2.hfix107_107_2 Q2.hinj107_107_2
      Q2.hcardT107_107_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T107_107_2 i) (Q2.hfix107_107_2 i) _)
      colCert_107_107_4.hD ?_).symm
  rw [alnId_107 j hj]


theorem leaf_107_107_5 (hp : 5 < (Q2.transData.getD 107 []).length)
    (j : Nat) (hj : j < (repChars.getD 107 []).length)
    (hq : (normIsRep.getD 107 []).getD j false = true) :
    species (Q2.reps (⟨107, by decide⟩ : Fin 148)) (colE2 ⟨107, by decide⟩ 5 hp)
        (rowE2 (⟨107, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨107, by decide⟩ : Fin 148))
        (colE1 ⟨107, by decide⟩ 5 (transLenTr ⟨107, by decide⟩ 5 hp))
        (rowE1 (⟨107, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨107, by decide⟩ : Fin 148) ⟨107, by decide⟩ _
      (validAt ⟨107, by decide⟩ (listedAt ⟨107, by decide⟩ hj))
      (colE1 ⟨107, by decide⟩ 5 (transLenTr ⟨107, by decide⟩ 5 hp)) T107_107
      hfix107_107 hinj107_107 hcardT107_107
      (fun i => conj_mem_of_fixedPoints _ _ (T107_107 i) (hfix107_107 i) _)
      ⟨107, by decide⟩ ⟨107, by decide⟩ _
      (Q2.validAt ⟨107, by decide⟩ (Q2.listedAt ⟨107, by decide⟩
        (alnCheck_rep ⟨107, by decide⟩ hj hq).1))
      (colE2 ⟨107, by decide⟩ 5 hp) Q2.T107_107_2 Q2.hfix107_107_2 Q2.hinj107_107_2
      Q2.hcardT107_107_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T107_107_2 i) (Q2.hfix107_107_2 i) _)
      colCert_107_107_5.hD ?_).symm
  rw [alnId_107 j hj]


theorem leaf_107_107_10 (hp : 10 < (Q2.transData.getD 107 []).length)
    (j : Nat) (hj : j < (repChars.getD 107 []).length)
    (hq : (normIsRep.getD 107 []).getD j false = true) :
    species (Q2.reps (⟨107, by decide⟩ : Fin 148)) (colE2 ⟨107, by decide⟩ 10 hp)
        (rowE2 (⟨107, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨107, by decide⟩ : Fin 148))
        (colE1 ⟨107, by decide⟩ 10 (transLenTr ⟨107, by decide⟩ 10 hp))
        (rowE1 (⟨107, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨107, by decide⟩ : Fin 148) ⟨107, by decide⟩ _
      (validAt ⟨107, by decide⟩ (listedAt ⟨107, by decide⟩ hj))
      (colE1 ⟨107, by decide⟩ 10 (transLenTr ⟨107, by decide⟩ 10 hp)) T107_107
      hfix107_107 hinj107_107 hcardT107_107
      (fun i => conj_mem_of_fixedPoints _ _ (T107_107 i) (hfix107_107 i) _)
      ⟨107, by decide⟩ ⟨107, by decide⟩ _
      (Q2.validAt ⟨107, by decide⟩ (Q2.listedAt ⟨107, by decide⟩
        (alnCheck_rep ⟨107, by decide⟩ hj hq).1))
      (colE2 ⟨107, by decide⟩ 10 hp) Q2.T107_107_2 Q2.hfix107_107_2 Q2.hinj107_107_2
      Q2.hcardT107_107_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T107_107_2 i) (Q2.hfix107_107_2 i) _)
      colCert_107_107_10.hD ?_).symm
  rw [alnId_107 j hj]


theorem leaf_107_107_15 (hp : 15 < (Q2.transData.getD 107 []).length)
    (j : Nat) (hj : j < (repChars.getD 107 []).length)
    (hq : (normIsRep.getD 107 []).getD j false = true) :
    species (Q2.reps (⟨107, by decide⟩ : Fin 148)) (colE2 ⟨107, by decide⟩ 15 hp)
        (rowE2 (⟨107, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨107, by decide⟩ : Fin 148))
        (colE1 ⟨107, by decide⟩ 15 (transLenTr ⟨107, by decide⟩ 15 hp))
        (rowE1 (⟨107, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨107, by decide⟩ : Fin 148) ⟨107, by decide⟩ _
      (validAt ⟨107, by decide⟩ (listedAt ⟨107, by decide⟩ hj))
      (colE1 ⟨107, by decide⟩ 15 (transLenTr ⟨107, by decide⟩ 15 hp)) T107_107
      hfix107_107 hinj107_107 hcardT107_107
      (fun i => conj_mem_of_fixedPoints _ _ (T107_107 i) (hfix107_107 i) _)
      ⟨107, by decide⟩ ⟨107, by decide⟩ _
      (Q2.validAt ⟨107, by decide⟩ (Q2.listedAt ⟨107, by decide⟩
        (alnCheck_rep ⟨107, by decide⟩ hj hq).1))
      (colE2 ⟨107, by decide⟩ 15 hp) Q2.T107_107_2 Q2.hfix107_107_2 Q2.hinj107_107_2
      Q2.hcardT107_107_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T107_107_2 i) (Q2.hfix107_107_2 i) _)
      colCert_107_107_15.hD ?_).symm
  rw [alnId_107 j hj]


theorem leaf_107_107_20 (hp : 20 < (Q2.transData.getD 107 []).length)
    (j : Nat) (hj : j < (repChars.getD 107 []).length)
    (hq : (normIsRep.getD 107 []).getD j false = true) :
    species (Q2.reps (⟨107, by decide⟩ : Fin 148)) (colE2 ⟨107, by decide⟩ 20 hp)
        (rowE2 (⟨107, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨107, by decide⟩ : Fin 148))
        (colE1 ⟨107, by decide⟩ 20 (transLenTr ⟨107, by decide⟩ 20 hp))
        (rowE1 (⟨107, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨107, by decide⟩ : Fin 148) ⟨107, by decide⟩ _
      (validAt ⟨107, by decide⟩ (listedAt ⟨107, by decide⟩ hj))
      (colE1 ⟨107, by decide⟩ 20 (transLenTr ⟨107, by decide⟩ 20 hp)) T107_107
      hfix107_107 hinj107_107 hcardT107_107
      (fun i => conj_mem_of_fixedPoints _ _ (T107_107 i) (hfix107_107 i) _)
      ⟨107, by decide⟩ ⟨107, by decide⟩ _
      (Q2.validAt ⟨107, by decide⟩ (Q2.listedAt ⟨107, by decide⟩
        (alnCheck_rep ⟨107, by decide⟩ hj hq).1))
      (colE2 ⟨107, by decide⟩ 20 hp) Q2.T107_107_2 Q2.hfix107_107_2 Q2.hinj107_107_2
      Q2.hcardT107_107_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T107_107_2 i) (Q2.hfix107_107_2 i) _)
      colCert_107_107_20.hD ?_).symm
  rw [alnId_107 j hj]


theorem leaf_108_10_0 (hp : 0 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 108 []).length)
    (hq : (normIsRep.getD 108 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 0 hp)
        (rowE2 (⟨108, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 0 (transLenTr ⟨10, by decide⟩ 0 hp))
        (rowE1 (⟨108, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨108, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨108, by decide⟩ (listedAt ⟨108, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 0 (transLenTr ⟨10, by decide⟩ 0 hp)) T108_10
      hfix108_10 hinj108_10 hcardT108_10
      (fun i => conj_mem_of_fixedPoints _ _ (T108_10 i) (hfix108_10 i) _)
      ⟨108, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨108, by decide⟩ (Q2.listedAt ⟨108, by decide⟩
        (alnCheck_rep ⟨108, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 0 hp) Q2.T108_10_2 Q2.hfix108_10_2 Q2.hinj108_10_2
      Q2.hcardT108_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T108_10_2 i) (Q2.hfix108_10_2 i) _)
      colCert_108_10_0.hD ?_).symm
  rw [alnId_108 j hj]


theorem leaf_108_10_1 (hp : 1 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 108 []).length)
    (hq : (normIsRep.getD 108 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 1 hp)
        (rowE2 (⟨108, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 1 (transLenTr ⟨10, by decide⟩ 1 hp))
        (rowE1 (⟨108, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨108, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨108, by decide⟩ (listedAt ⟨108, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 1 (transLenTr ⟨10, by decide⟩ 1 hp)) T108_10
      hfix108_10 hinj108_10 hcardT108_10
      (fun i => conj_mem_of_fixedPoints _ _ (T108_10 i) (hfix108_10 i) _)
      ⟨108, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨108, by decide⟩ (Q2.listedAt ⟨108, by decide⟩
        (alnCheck_rep ⟨108, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 1 hp) Q2.T108_10_2 Q2.hfix108_10_2 Q2.hinj108_10_2
      Q2.hcardT108_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T108_10_2 i) (Q2.hfix108_10_2 i) _)
      colCert_108_10_1.hD ?_).symm
  rw [alnId_108 j hj]


theorem leaf_108_10_2 (hp : 2 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 108 []).length)
    (hq : (normIsRep.getD 108 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 2 hp)
        (rowE2 (⟨108, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 2 (transLenTr ⟨10, by decide⟩ 2 hp))
        (rowE1 (⟨108, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨108, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨108, by decide⟩ (listedAt ⟨108, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 2 (transLenTr ⟨10, by decide⟩ 2 hp)) T108_10
      hfix108_10 hinj108_10 hcardT108_10
      (fun i => conj_mem_of_fixedPoints _ _ (T108_10 i) (hfix108_10 i) _)
      ⟨108, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨108, by decide⟩ (Q2.listedAt ⟨108, by decide⟩
        (alnCheck_rep ⟨108, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 2 hp) Q2.T108_10_2 Q2.hfix108_10_2 Q2.hinj108_10_2
      Q2.hcardT108_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T108_10_2 i) (Q2.hfix108_10_2 i) _)
      colCert_108_10_2.hD ?_).symm
  rw [alnId_108 j hj]


theorem leaf_108_10_3 (hp : 3 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 108 []).length)
    (hq : (normIsRep.getD 108 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 3 hp)
        (rowE2 (⟨108, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 3 (transLenTr ⟨10, by decide⟩ 3 hp))
        (rowE1 (⟨108, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨108, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨108, by decide⟩ (listedAt ⟨108, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 3 (transLenTr ⟨10, by decide⟩ 3 hp)) T108_10
      hfix108_10 hinj108_10 hcardT108_10
      (fun i => conj_mem_of_fixedPoints _ _ (T108_10 i) (hfix108_10 i) _)
      ⟨108, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨108, by decide⟩ (Q2.listedAt ⟨108, by decide⟩
        (alnCheck_rep ⟨108, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 3 hp) Q2.T108_10_2 Q2.hfix108_10_2 Q2.hinj108_10_2
      Q2.hcardT108_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T108_10_2 i) (Q2.hfix108_10_2 i) _)
      colCert_108_10_3.hD ?_).symm
  rw [alnId_108 j hj]


theorem leaf_108_10_4 (hp : 4 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 108 []).length)
    (hq : (normIsRep.getD 108 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 4 hp)
        (rowE2 (⟨108, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 4 (transLenTr ⟨10, by decide⟩ 4 hp))
        (rowE1 (⟨108, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨108, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨108, by decide⟩ (listedAt ⟨108, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 4 (transLenTr ⟨10, by decide⟩ 4 hp)) T108_10
      hfix108_10 hinj108_10 hcardT108_10
      (fun i => conj_mem_of_fixedPoints _ _ (T108_10 i) (hfix108_10 i) _)
      ⟨108, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨108, by decide⟩ (Q2.listedAt ⟨108, by decide⟩
        (alnCheck_rep ⟨108, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 4 hp) Q2.T108_10_2 Q2.hfix108_10_2 Q2.hinj108_10_2
      Q2.hcardT108_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T108_10_2 i) (Q2.hfix108_10_2 i) _)
      colCert_108_10_4.hD ?_).symm
  rw [alnId_108 j hj]


theorem leaf_108_12_0 (hp : 0 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 108 []).length)
    (hq : (normIsRep.getD 108 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 0 hp)
        (rowE2 (⟨108, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp))
        (rowE1 (⟨108, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨108, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨108, by decide⟩ (listedAt ⟨108, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp)) T108_12
      hfix108_12 hinj108_12 hcardT108_12
      (fun i => conj_mem_of_fixedPoints _ _ (T108_12 i) (hfix108_12 i) _)
      ⟨108, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨108, by decide⟩ (Q2.listedAt ⟨108, by decide⟩
        (alnCheck_rep ⟨108, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 0 hp) Q2.T108_12_2 Q2.hfix108_12_2 Q2.hinj108_12_2
      Q2.hcardT108_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T108_12_2 i) (Q2.hfix108_12_2 i) _)
      colCert_108_12_0.hD ?_).symm
  rw [alnId_108 j hj]


theorem leaf_108_12_1 (hp : 1 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 108 []).length)
    (hq : (normIsRep.getD 108 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 1 hp)
        (rowE2 (⟨108, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp))
        (rowE1 (⟨108, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨108, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨108, by decide⟩ (listedAt ⟨108, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp)) T108_12
      hfix108_12 hinj108_12 hcardT108_12
      (fun i => conj_mem_of_fixedPoints _ _ (T108_12 i) (hfix108_12 i) _)
      ⟨108, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨108, by decide⟩ (Q2.listedAt ⟨108, by decide⟩
        (alnCheck_rep ⟨108, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 1 hp) Q2.T108_12_2 Q2.hfix108_12_2 Q2.hinj108_12_2
      Q2.hcardT108_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T108_12_2 i) (Q2.hfix108_12_2 i) _)
      colCert_108_12_1.hD ?_).symm
  rw [alnId_108 j hj]


theorem leaf_108_12_2 (hp : 2 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 108 []).length)
    (hq : (normIsRep.getD 108 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 2 hp)
        (rowE2 (⟨108, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp))
        (rowE1 (⟨108, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨108, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨108, by decide⟩ (listedAt ⟨108, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp)) T108_12
      hfix108_12 hinj108_12 hcardT108_12
      (fun i => conj_mem_of_fixedPoints _ _ (T108_12 i) (hfix108_12 i) _)
      ⟨108, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨108, by decide⟩ (Q2.listedAt ⟨108, by decide⟩
        (alnCheck_rep ⟨108, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 2 hp) Q2.T108_12_2 Q2.hfix108_12_2 Q2.hinj108_12_2
      Q2.hcardT108_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T108_12_2 i) (Q2.hfix108_12_2 i) _)
      colCert_108_12_2.hD ?_).symm
  rw [alnId_108 j hj]


theorem leaf_108_12_3 (hp : 3 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 108 []).length)
    (hq : (normIsRep.getD 108 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 3 hp)
        (rowE2 (⟨108, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp))
        (rowE1 (⟨108, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨108, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨108, by decide⟩ (listedAt ⟨108, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp)) T108_12
      hfix108_12 hinj108_12 hcardT108_12
      (fun i => conj_mem_of_fixedPoints _ _ (T108_12 i) (hfix108_12 i) _)
      ⟨108, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨108, by decide⟩ (Q2.listedAt ⟨108, by decide⟩
        (alnCheck_rep ⟨108, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 3 hp) Q2.T108_12_2 Q2.hfix108_12_2 Q2.hinj108_12_2
      Q2.hcardT108_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T108_12_2 i) (Q2.hfix108_12_2 i) _)
      colCert_108_12_3.hD ?_).symm
  rw [alnId_108 j hj]


theorem leaf_108_12_4 (hp : 4 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 108 []).length)
    (hq : (normIsRep.getD 108 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 4 hp)
        (rowE2 (⟨108, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp))
        (rowE1 (⟨108, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨108, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨108, by decide⟩ (listedAt ⟨108, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp)) T108_12
      hfix108_12 hinj108_12 hcardT108_12
      (fun i => conj_mem_of_fixedPoints _ _ (T108_12 i) (hfix108_12 i) _)
      ⟨108, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨108, by decide⟩ (Q2.listedAt ⟨108, by decide⟩
        (alnCheck_rep ⟨108, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 4 hp) Q2.T108_12_2 Q2.hfix108_12_2 Q2.hinj108_12_2
      Q2.hcardT108_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T108_12_2 i) (Q2.hfix108_12_2 i) _)
      colCert_108_12_4.hD ?_).symm
  rw [alnId_108 j hj]


theorem leaf_108_46_0 (hp : 0 < (Q2.transData.getD 46 []).length)
    (j : Nat) (hj : j < (repChars.getD 108 []).length)
    (hq : (normIsRep.getD 108 []).getD j false = true) :
    species (Q2.reps (⟨46, by decide⟩ : Fin 148)) (colE2 ⟨46, by decide⟩ 0 hp)
        (rowE2 (⟨108, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨46, by decide⟩ : Fin 148))
        (colE1 ⟨46, by decide⟩ 0 (transLenTr ⟨46, by decide⟩ 0 hp))
        (rowE1 (⟨108, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨108, by decide⟩ : Fin 148) ⟨46, by decide⟩ _
      (validAt ⟨108, by decide⟩ (listedAt ⟨108, by decide⟩ hj))
      (colE1 ⟨46, by decide⟩ 0 (transLenTr ⟨46, by decide⟩ 0 hp)) T108_46
      hfix108_46 hinj108_46 hcardT108_46
      (fun i => conj_mem_of_fixedPoints _ _ (T108_46 i) (hfix108_46 i) _)
      ⟨108, by decide⟩ ⟨46, by decide⟩ _
      (Q2.validAt ⟨108, by decide⟩ (Q2.listedAt ⟨108, by decide⟩
        (alnCheck_rep ⟨108, by decide⟩ hj hq).1))
      (colE2 ⟨46, by decide⟩ 0 hp) Q2.T108_46_2 Q2.hfix108_46_2 Q2.hinj108_46_2
      Q2.hcardT108_46_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T108_46_2 i) (Q2.hfix108_46_2 i) _)
      colCert_108_46_0.hD ?_).symm
  rw [alnId_108 j hj]


theorem leaf_108_46_1 (hp : 1 < (Q2.transData.getD 46 []).length)
    (j : Nat) (hj : j < (repChars.getD 108 []).length)
    (hq : (normIsRep.getD 108 []).getD j false = true) :
    species (Q2.reps (⟨46, by decide⟩ : Fin 148)) (colE2 ⟨46, by decide⟩ 1 hp)
        (rowE2 (⟨108, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨46, by decide⟩ : Fin 148))
        (colE1 ⟨46, by decide⟩ 1 (transLenTr ⟨46, by decide⟩ 1 hp))
        (rowE1 (⟨108, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨108, by decide⟩ : Fin 148) ⟨46, by decide⟩ _
      (validAt ⟨108, by decide⟩ (listedAt ⟨108, by decide⟩ hj))
      (colE1 ⟨46, by decide⟩ 1 (transLenTr ⟨46, by decide⟩ 1 hp)) T108_46
      hfix108_46 hinj108_46 hcardT108_46
      (fun i => conj_mem_of_fixedPoints _ _ (T108_46 i) (hfix108_46 i) _)
      ⟨108, by decide⟩ ⟨46, by decide⟩ _
      (Q2.validAt ⟨108, by decide⟩ (Q2.listedAt ⟨108, by decide⟩
        (alnCheck_rep ⟨108, by decide⟩ hj hq).1))
      (colE2 ⟨46, by decide⟩ 1 hp) Q2.T108_46_2 Q2.hfix108_46_2 Q2.hinj108_46_2
      Q2.hcardT108_46_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T108_46_2 i) (Q2.hfix108_46_2 i) _)
      colCert_108_46_1.hD ?_).symm
  rw [alnId_108 j hj]


theorem leaf_108_46_2 (hp : 2 < (Q2.transData.getD 46 []).length)
    (j : Nat) (hj : j < (repChars.getD 108 []).length)
    (hq : (normIsRep.getD 108 []).getD j false = true) :
    species (Q2.reps (⟨46, by decide⟩ : Fin 148)) (colE2 ⟨46, by decide⟩ 2 hp)
        (rowE2 (⟨108, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨46, by decide⟩ : Fin 148))
        (colE1 ⟨46, by decide⟩ 2 (transLenTr ⟨46, by decide⟩ 2 hp))
        (rowE1 (⟨108, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨108, by decide⟩ : Fin 148) ⟨46, by decide⟩ _
      (validAt ⟨108, by decide⟩ (listedAt ⟨108, by decide⟩ hj))
      (colE1 ⟨46, by decide⟩ 2 (transLenTr ⟨46, by decide⟩ 2 hp)) T108_46
      hfix108_46 hinj108_46 hcardT108_46
      (fun i => conj_mem_of_fixedPoints _ _ (T108_46 i) (hfix108_46 i) _)
      ⟨108, by decide⟩ ⟨46, by decide⟩ _
      (Q2.validAt ⟨108, by decide⟩ (Q2.listedAt ⟨108, by decide⟩
        (alnCheck_rep ⟨108, by decide⟩ hj hq).1))
      (colE2 ⟨46, by decide⟩ 2 hp) Q2.T108_46_2 Q2.hfix108_46_2 Q2.hinj108_46_2
      Q2.hcardT108_46_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T108_46_2 i) (Q2.hfix108_46_2 i) _)
      colCert_108_46_2.hD ?_).symm
  rw [alnId_108 j hj]


theorem leaf_108_46_3 (hp : 3 < (Q2.transData.getD 46 []).length)
    (j : Nat) (hj : j < (repChars.getD 108 []).length)
    (hq : (normIsRep.getD 108 []).getD j false = true) :
    species (Q2.reps (⟨46, by decide⟩ : Fin 148)) (colE2 ⟨46, by decide⟩ 3 hp)
        (rowE2 (⟨108, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨46, by decide⟩ : Fin 148))
        (colE1 ⟨46, by decide⟩ 3 (transLenTr ⟨46, by decide⟩ 3 hp))
        (rowE1 (⟨108, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨108, by decide⟩ : Fin 148) ⟨46, by decide⟩ _
      (validAt ⟨108, by decide⟩ (listedAt ⟨108, by decide⟩ hj))
      (colE1 ⟨46, by decide⟩ 3 (transLenTr ⟨46, by decide⟩ 3 hp)) T108_46
      hfix108_46 hinj108_46 hcardT108_46
      (fun i => conj_mem_of_fixedPoints _ _ (T108_46 i) (hfix108_46 i) _)
      ⟨108, by decide⟩ ⟨46, by decide⟩ _
      (Q2.validAt ⟨108, by decide⟩ (Q2.listedAt ⟨108, by decide⟩
        (alnCheck_rep ⟨108, by decide⟩ hj hq).1))
      (colE2 ⟨46, by decide⟩ 3 hp) Q2.T108_46_2 Q2.hfix108_46_2 Q2.hinj108_46_2
      Q2.hcardT108_46_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T108_46_2 i) (Q2.hfix108_46_2 i) _)
      colCert_108_46_3.hD ?_).symm
  rw [alnId_108 j hj]


theorem leaf_108_46_4 (hp : 4 < (Q2.transData.getD 46 []).length)
    (j : Nat) (hj : j < (repChars.getD 108 []).length)
    (hq : (normIsRep.getD 108 []).getD j false = true) :
    species (Q2.reps (⟨46, by decide⟩ : Fin 148)) (colE2 ⟨46, by decide⟩ 4 hp)
        (rowE2 (⟨108, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨46, by decide⟩ : Fin 148))
        (colE1 ⟨46, by decide⟩ 4 (transLenTr ⟨46, by decide⟩ 4 hp))
        (rowE1 (⟨108, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨108, by decide⟩ : Fin 148) ⟨46, by decide⟩ _
      (validAt ⟨108, by decide⟩ (listedAt ⟨108, by decide⟩ hj))
      (colE1 ⟨46, by decide⟩ 4 (transLenTr ⟨46, by decide⟩ 4 hp)) T108_46
      hfix108_46 hinj108_46 hcardT108_46
      (fun i => conj_mem_of_fixedPoints _ _ (T108_46 i) (hfix108_46 i) _)
      ⟨108, by decide⟩ ⟨46, by decide⟩ _
      (Q2.validAt ⟨108, by decide⟩ (Q2.listedAt ⟨108, by decide⟩
        (alnCheck_rep ⟨108, by decide⟩ hj hq).1))
      (colE2 ⟨46, by decide⟩ 4 hp) Q2.T108_46_2 Q2.hfix108_46_2 Q2.hinj108_46_2
      Q2.hcardT108_46_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T108_46_2 i) (Q2.hfix108_46_2 i) _)
      colCert_108_46_4.hD ?_).symm
  rw [alnId_108 j hj]


theorem leaf_108_46_5 (hp : 5 < (Q2.transData.getD 46 []).length)
    (j : Nat) (hj : j < (repChars.getD 108 []).length)
    (hq : (normIsRep.getD 108 []).getD j false = true) :
    species (Q2.reps (⟨46, by decide⟩ : Fin 148)) (colE2 ⟨46, by decide⟩ 5 hp)
        (rowE2 (⟨108, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨46, by decide⟩ : Fin 148))
        (colE1 ⟨46, by decide⟩ 5 (transLenTr ⟨46, by decide⟩ 5 hp))
        (rowE1 (⟨108, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨108, by decide⟩ : Fin 148) ⟨46, by decide⟩ _
      (validAt ⟨108, by decide⟩ (listedAt ⟨108, by decide⟩ hj))
      (colE1 ⟨46, by decide⟩ 5 (transLenTr ⟨46, by decide⟩ 5 hp)) T108_46
      hfix108_46 hinj108_46 hcardT108_46
      (fun i => conj_mem_of_fixedPoints _ _ (T108_46 i) (hfix108_46 i) _)
      ⟨108, by decide⟩ ⟨46, by decide⟩ _
      (Q2.validAt ⟨108, by decide⟩ (Q2.listedAt ⟨108, by decide⟩
        (alnCheck_rep ⟨108, by decide⟩ hj hq).1))
      (colE2 ⟨46, by decide⟩ 5 hp) Q2.T108_46_2 Q2.hfix108_46_2 Q2.hinj108_46_2
      Q2.hcardT108_46_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T108_46_2 i) (Q2.hfix108_46_2 i) _)
      ?_).symm
  rw [show colData1 (⟨108, by decide⟩ : Fin 148)
        ((colE1 ⟨46, by decide⟩ 5 (transLenTr ⟨46, by decide⟩ 5 hp) : ↥(reps ⟨46, by decide⟩)) : Coordinate 1)
        T108_46 = colFn colCertDiv_108_46_5.D1 (m := 25) from colCertDiv_108_46_5.bind1,
    show colData2 (⟨108, by decide⟩ : Fin 148)
        ((colE2 ⟨46, by decide⟩ 5 hp : ↥(Q2.reps ⟨46, by decide⟩)) : Coordinate 2)
        Q2.T108_46_2 = colFn colCertDiv_108_46_5.D2 (m := 25) from colCertDiv_108_46_5.bind2]
  rw [alnId_108 j hj]
  exact fastcode_of_div ⟨108, by decide⟩ _ _ _
    ((alnId_108 j hj) ▸ Q2.listedAt (⟨108, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨108, by decide⟩ : Fin 148) hj hq).1) colCertDiv_108_46_5_match


theorem leaf_108_46_10 (hp : 10 < (Q2.transData.getD 46 []).length)
    (j : Nat) (hj : j < (repChars.getD 108 []).length)
    (hq : (normIsRep.getD 108 []).getD j false = true) :
    species (Q2.reps (⟨46, by decide⟩ : Fin 148)) (colE2 ⟨46, by decide⟩ 10 hp)
        (rowE2 (⟨108, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨46, by decide⟩ : Fin 148))
        (colE1 ⟨46, by decide⟩ 10 (transLenTr ⟨46, by decide⟩ 10 hp))
        (rowE1 (⟨108, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨108, by decide⟩ : Fin 148) ⟨46, by decide⟩ _
      (validAt ⟨108, by decide⟩ (listedAt ⟨108, by decide⟩ hj))
      (colE1 ⟨46, by decide⟩ 10 (transLenTr ⟨46, by decide⟩ 10 hp)) T108_46
      hfix108_46 hinj108_46 hcardT108_46
      (fun i => conj_mem_of_fixedPoints _ _ (T108_46 i) (hfix108_46 i) _)
      ⟨108, by decide⟩ ⟨46, by decide⟩ _
      (Q2.validAt ⟨108, by decide⟩ (Q2.listedAt ⟨108, by decide⟩
        (alnCheck_rep ⟨108, by decide⟩ hj hq).1))
      (colE2 ⟨46, by decide⟩ 10 hp) Q2.T108_46_2 Q2.hfix108_46_2 Q2.hinj108_46_2
      Q2.hcardT108_46_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T108_46_2 i) (Q2.hfix108_46_2 i) _)
      ?_).symm
  rw [show colData1 (⟨108, by decide⟩ : Fin 148)
        ((colE1 ⟨46, by decide⟩ 10 (transLenTr ⟨46, by decide⟩ 10 hp) : ↥(reps ⟨46, by decide⟩)) : Coordinate 1)
        T108_46 = colFn colCertDiv_108_46_10.D1 (m := 25) from colCertDiv_108_46_10.bind1,
    show colData2 (⟨108, by decide⟩ : Fin 148)
        ((colE2 ⟨46, by decide⟩ 10 hp : ↥(Q2.reps ⟨46, by decide⟩)) : Coordinate 2)
        Q2.T108_46_2 = colFn colCertDiv_108_46_10.D2 (m := 25) from colCertDiv_108_46_10.bind2]
  rw [alnId_108 j hj]
  exact fastcode_of_div ⟨108, by decide⟩ _ _ _
    ((alnId_108 j hj) ▸ Q2.listedAt (⟨108, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨108, by decide⟩ : Fin 148) hj hq).1) colCertDiv_108_46_10_match


theorem leaf_108_46_15 (hp : 15 < (Q2.transData.getD 46 []).length)
    (j : Nat) (hj : j < (repChars.getD 108 []).length)
    (hq : (normIsRep.getD 108 []).getD j false = true) :
    species (Q2.reps (⟨46, by decide⟩ : Fin 148)) (colE2 ⟨46, by decide⟩ 15 hp)
        (rowE2 (⟨108, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨46, by decide⟩ : Fin 148))
        (colE1 ⟨46, by decide⟩ 15 (transLenTr ⟨46, by decide⟩ 15 hp))
        (rowE1 (⟨108, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨108, by decide⟩ : Fin 148) ⟨46, by decide⟩ _
      (validAt ⟨108, by decide⟩ (listedAt ⟨108, by decide⟩ hj))
      (colE1 ⟨46, by decide⟩ 15 (transLenTr ⟨46, by decide⟩ 15 hp)) T108_46
      hfix108_46 hinj108_46 hcardT108_46
      (fun i => conj_mem_of_fixedPoints _ _ (T108_46 i) (hfix108_46 i) _)
      ⟨108, by decide⟩ ⟨46, by decide⟩ _
      (Q2.validAt ⟨108, by decide⟩ (Q2.listedAt ⟨108, by decide⟩
        (alnCheck_rep ⟨108, by decide⟩ hj hq).1))
      (colE2 ⟨46, by decide⟩ 15 hp) Q2.T108_46_2 Q2.hfix108_46_2 Q2.hinj108_46_2
      Q2.hcardT108_46_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T108_46_2 i) (Q2.hfix108_46_2 i) _)
      ?_).symm
  rw [show colData1 (⟨108, by decide⟩ : Fin 148)
        ((colE1 ⟨46, by decide⟩ 15 (transLenTr ⟨46, by decide⟩ 15 hp) : ↥(reps ⟨46, by decide⟩)) : Coordinate 1)
        T108_46 = colFn colCertDiv_108_46_15.D1 (m := 25) from colCertDiv_108_46_15.bind1,
    show colData2 (⟨108, by decide⟩ : Fin 148)
        ((colE2 ⟨46, by decide⟩ 15 hp : ↥(Q2.reps ⟨46, by decide⟩)) : Coordinate 2)
        Q2.T108_46_2 = colFn colCertDiv_108_46_15.D2 (m := 25) from colCertDiv_108_46_15.bind2]
  rw [alnId_108 j hj]
  exact fastcode_of_div ⟨108, by decide⟩ _ _ _
    ((alnId_108 j hj) ▸ Q2.listedAt (⟨108, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨108, by decide⟩ : Fin 148) hj hq).1) colCertDiv_108_46_15_match


theorem leaf_108_46_20 (hp : 20 < (Q2.transData.getD 46 []).length)
    (j : Nat) (hj : j < (repChars.getD 108 []).length)
    (hq : (normIsRep.getD 108 []).getD j false = true) :
    species (Q2.reps (⟨46, by decide⟩ : Fin 148)) (colE2 ⟨46, by decide⟩ 20 hp)
        (rowE2 (⟨108, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨46, by decide⟩ : Fin 148))
        (colE1 ⟨46, by decide⟩ 20 (transLenTr ⟨46, by decide⟩ 20 hp))
        (rowE1 (⟨108, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨108, by decide⟩ : Fin 148) ⟨46, by decide⟩ _
      (validAt ⟨108, by decide⟩ (listedAt ⟨108, by decide⟩ hj))
      (colE1 ⟨46, by decide⟩ 20 (transLenTr ⟨46, by decide⟩ 20 hp)) T108_46
      hfix108_46 hinj108_46 hcardT108_46
      (fun i => conj_mem_of_fixedPoints _ _ (T108_46 i) (hfix108_46 i) _)
      ⟨108, by decide⟩ ⟨46, by decide⟩ _
      (Q2.validAt ⟨108, by decide⟩ (Q2.listedAt ⟨108, by decide⟩
        (alnCheck_rep ⟨108, by decide⟩ hj hq).1))
      (colE2 ⟨46, by decide⟩ 20 hp) Q2.T108_46_2 Q2.hfix108_46_2 Q2.hinj108_46_2
      Q2.hcardT108_46_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T108_46_2 i) (Q2.hfix108_46_2 i) _)
      ?_).symm
  rw [show colData1 (⟨108, by decide⟩ : Fin 148)
        ((colE1 ⟨46, by decide⟩ 20 (transLenTr ⟨46, by decide⟩ 20 hp) : ↥(reps ⟨46, by decide⟩)) : Coordinate 1)
        T108_46 = colFn colCertDiv_108_46_20.D1 (m := 25) from colCertDiv_108_46_20.bind1,
    show colData2 (⟨108, by decide⟩ : Fin 148)
        ((colE2 ⟨46, by decide⟩ 20 hp : ↥(Q2.reps ⟨46, by decide⟩)) : Coordinate 2)
        Q2.T108_46_2 = colFn colCertDiv_108_46_20.D2 (m := 25) from colCertDiv_108_46_20.bind2]
  rw [alnId_108 j hj]
  exact fastcode_of_div ⟨108, by decide⟩ _ _ _
    ((alnId_108 j hj) ▸ Q2.listedAt (⟨108, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨108, by decide⟩ : Fin 148) hj hq).1) colCertDiv_108_46_20_match


theorem leaf_108_53_0 (hp : 0 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 108 []).length)
    (hq : (normIsRep.getD 108 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 0 hp)
        (rowE2 (⟨108, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 0 (transLenTr ⟨53, by decide⟩ 0 hp))
        (rowE1 (⟨108, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨108, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨108, by decide⟩ (listedAt ⟨108, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 0 (transLenTr ⟨53, by decide⟩ 0 hp)) T108_53
      hfix108_53 hinj108_53 hcardT108_53
      (fun i => conj_mem_of_fixedPoints _ _ (T108_53 i) (hfix108_53 i) _)
      ⟨108, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨108, by decide⟩ (Q2.listedAt ⟨108, by decide⟩
        (alnCheck_rep ⟨108, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 0 hp) Q2.T108_53_2 Q2.hfix108_53_2 Q2.hinj108_53_2
      Q2.hcardT108_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T108_53_2 i) (Q2.hfix108_53_2 i) _)
      colCert_108_53_0.hD ?_).symm
  rw [alnId_108 j hj]


theorem leaf_108_53_1 (hp : 1 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 108 []).length)
    (hq : (normIsRep.getD 108 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 1 hp)
        (rowE2 (⟨108, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 1 (transLenTr ⟨53, by decide⟩ 1 hp))
        (rowE1 (⟨108, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨108, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨108, by decide⟩ (listedAt ⟨108, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 1 (transLenTr ⟨53, by decide⟩ 1 hp)) T108_53
      hfix108_53 hinj108_53 hcardT108_53
      (fun i => conj_mem_of_fixedPoints _ _ (T108_53 i) (hfix108_53 i) _)
      ⟨108, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨108, by decide⟩ (Q2.listedAt ⟨108, by decide⟩
        (alnCheck_rep ⟨108, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 1 hp) Q2.T108_53_2 Q2.hfix108_53_2 Q2.hinj108_53_2
      Q2.hcardT108_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T108_53_2 i) (Q2.hfix108_53_2 i) _)
      colCert_108_53_1.hD ?_).symm
  rw [alnId_108 j hj]


theorem leaf_108_53_2 (hp : 2 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 108 []).length)
    (hq : (normIsRep.getD 108 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 2 hp)
        (rowE2 (⟨108, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 2 (transLenTr ⟨53, by decide⟩ 2 hp))
        (rowE1 (⟨108, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨108, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨108, by decide⟩ (listedAt ⟨108, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 2 (transLenTr ⟨53, by decide⟩ 2 hp)) T108_53
      hfix108_53 hinj108_53 hcardT108_53
      (fun i => conj_mem_of_fixedPoints _ _ (T108_53 i) (hfix108_53 i) _)
      ⟨108, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨108, by decide⟩ (Q2.listedAt ⟨108, by decide⟩
        (alnCheck_rep ⟨108, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 2 hp) Q2.T108_53_2 Q2.hfix108_53_2 Q2.hinj108_53_2
      Q2.hcardT108_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T108_53_2 i) (Q2.hfix108_53_2 i) _)
      colCert_108_53_2.hD ?_).symm
  rw [alnId_108 j hj]


theorem leaf_108_53_3 (hp : 3 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 108 []).length)
    (hq : (normIsRep.getD 108 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 3 hp)
        (rowE2 (⟨108, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 3 (transLenTr ⟨53, by decide⟩ 3 hp))
        (rowE1 (⟨108, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨108, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨108, by decide⟩ (listedAt ⟨108, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 3 (transLenTr ⟨53, by decide⟩ 3 hp)) T108_53
      hfix108_53 hinj108_53 hcardT108_53
      (fun i => conj_mem_of_fixedPoints _ _ (T108_53 i) (hfix108_53 i) _)
      ⟨108, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨108, by decide⟩ (Q2.listedAt ⟨108, by decide⟩
        (alnCheck_rep ⟨108, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 3 hp) Q2.T108_53_2 Q2.hfix108_53_2 Q2.hinj108_53_2
      Q2.hcardT108_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T108_53_2 i) (Q2.hfix108_53_2 i) _)
      colCert_108_53_3.hD ?_).symm
  rw [alnId_108 j hj]


theorem leaf_108_53_4 (hp : 4 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 108 []).length)
    (hq : (normIsRep.getD 108 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 4 hp)
        (rowE2 (⟨108, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 4 (transLenTr ⟨53, by decide⟩ 4 hp))
        (rowE1 (⟨108, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨108, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨108, by decide⟩ (listedAt ⟨108, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 4 (transLenTr ⟨53, by decide⟩ 4 hp)) T108_53
      hfix108_53 hinj108_53 hcardT108_53
      (fun i => conj_mem_of_fixedPoints _ _ (T108_53 i) (hfix108_53 i) _)
      ⟨108, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨108, by decide⟩ (Q2.listedAt ⟨108, by decide⟩
        (alnCheck_rep ⟨108, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 4 hp) Q2.T108_53_2 Q2.hfix108_53_2 Q2.hinj108_53_2
      Q2.hcardT108_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T108_53_2 i) (Q2.hfix108_53_2 i) _)
      colCert_108_53_4.hD ?_).symm
  rw [alnId_108 j hj]


theorem leaf_108_53_5 (hp : 5 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 108 []).length)
    (hq : (normIsRep.getD 108 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 5 hp)
        (rowE2 (⟨108, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 5 (transLenTr ⟨53, by decide⟩ 5 hp))
        (rowE1 (⟨108, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨108, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨108, by decide⟩ (listedAt ⟨108, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 5 (transLenTr ⟨53, by decide⟩ 5 hp)) T108_53
      hfix108_53 hinj108_53 hcardT108_53
      (fun i => conj_mem_of_fixedPoints _ _ (T108_53 i) (hfix108_53 i) _)
      ⟨108, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨108, by decide⟩ (Q2.listedAt ⟨108, by decide⟩
        (alnCheck_rep ⟨108, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 5 hp) Q2.T108_53_2 Q2.hfix108_53_2 Q2.hinj108_53_2
      Q2.hcardT108_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T108_53_2 i) (Q2.hfix108_53_2 i) _)
      colCert_108_53_5.hD ?_).symm
  rw [alnId_108 j hj]


theorem leaf_108_53_10 (hp : 10 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 108 []).length)
    (hq : (normIsRep.getD 108 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 10 hp)
        (rowE2 (⟨108, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 10 (transLenTr ⟨53, by decide⟩ 10 hp))
        (rowE1 (⟨108, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨108, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨108, by decide⟩ (listedAt ⟨108, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 10 (transLenTr ⟨53, by decide⟩ 10 hp)) T108_53
      hfix108_53 hinj108_53 hcardT108_53
      (fun i => conj_mem_of_fixedPoints _ _ (T108_53 i) (hfix108_53 i) _)
      ⟨108, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨108, by decide⟩ (Q2.listedAt ⟨108, by decide⟩
        (alnCheck_rep ⟨108, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 10 hp) Q2.T108_53_2 Q2.hfix108_53_2 Q2.hinj108_53_2
      Q2.hcardT108_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T108_53_2 i) (Q2.hfix108_53_2 i) _)
      colCert_108_53_10.hD ?_).symm
  rw [alnId_108 j hj]


theorem leaf_108_53_15 (hp : 15 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 108 []).length)
    (hq : (normIsRep.getD 108 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 15 hp)
        (rowE2 (⟨108, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 15 (transLenTr ⟨53, by decide⟩ 15 hp))
        (rowE1 (⟨108, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨108, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨108, by decide⟩ (listedAt ⟨108, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 15 (transLenTr ⟨53, by decide⟩ 15 hp)) T108_53
      hfix108_53 hinj108_53 hcardT108_53
      (fun i => conj_mem_of_fixedPoints _ _ (T108_53 i) (hfix108_53 i) _)
      ⟨108, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨108, by decide⟩ (Q2.listedAt ⟨108, by decide⟩
        (alnCheck_rep ⟨108, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 15 hp) Q2.T108_53_2 Q2.hfix108_53_2 Q2.hinj108_53_2
      Q2.hcardT108_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T108_53_2 i) (Q2.hfix108_53_2 i) _)
      colCert_108_53_15.hD ?_).symm
  rw [alnId_108 j hj]


theorem leaf_108_53_20 (hp : 20 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 108 []).length)
    (hq : (normIsRep.getD 108 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 20 hp)
        (rowE2 (⟨108, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 20 (transLenTr ⟨53, by decide⟩ 20 hp))
        (rowE1 (⟨108, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨108, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨108, by decide⟩ (listedAt ⟨108, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 20 (transLenTr ⟨53, by decide⟩ 20 hp)) T108_53
      hfix108_53 hinj108_53 hcardT108_53
      (fun i => conj_mem_of_fixedPoints _ _ (T108_53 i) (hfix108_53 i) _)
      ⟨108, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨108, by decide⟩ (Q2.listedAt ⟨108, by decide⟩
        (alnCheck_rep ⟨108, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 20 hp) Q2.T108_53_2 Q2.hfix108_53_2 Q2.hinj108_53_2
      Q2.hcardT108_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T108_53_2 i) (Q2.hfix108_53_2 i) _)
      colCert_108_53_20.hD ?_).symm
  rw [alnId_108 j hj]


theorem leaf_108_108_0 (hp : 0 < (Q2.transData.getD 108 []).length)
    (j : Nat) (hj : j < (repChars.getD 108 []).length)
    (hq : (normIsRep.getD 108 []).getD j false = true) :
    species (Q2.reps (⟨108, by decide⟩ : Fin 148)) (colE2 ⟨108, by decide⟩ 0 hp)
        (rowE2 (⟨108, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨108, by decide⟩ : Fin 148))
        (colE1 ⟨108, by decide⟩ 0 (transLenTr ⟨108, by decide⟩ 0 hp))
        (rowE1 (⟨108, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨108, by decide⟩ : Fin 148) ⟨108, by decide⟩ _
      (validAt ⟨108, by decide⟩ (listedAt ⟨108, by decide⟩ hj))
      (colE1 ⟨108, by decide⟩ 0 (transLenTr ⟨108, by decide⟩ 0 hp)) T108_108
      hfix108_108 hinj108_108 hcardT108_108
      (fun i => conj_mem_of_fixedPoints _ _ (T108_108 i) (hfix108_108 i) _)
      ⟨108, by decide⟩ ⟨108, by decide⟩ _
      (Q2.validAt ⟨108, by decide⟩ (Q2.listedAt ⟨108, by decide⟩
        (alnCheck_rep ⟨108, by decide⟩ hj hq).1))
      (colE2 ⟨108, by decide⟩ 0 hp) Q2.T108_108_2 Q2.hfix108_108_2 Q2.hinj108_108_2
      Q2.hcardT108_108_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T108_108_2 i) (Q2.hfix108_108_2 i) _)
      colCert_108_108_0.hD ?_).symm
  rw [alnId_108 j hj]


theorem leaf_108_108_1 (hp : 1 < (Q2.transData.getD 108 []).length)
    (j : Nat) (hj : j < (repChars.getD 108 []).length)
    (hq : (normIsRep.getD 108 []).getD j false = true) :
    species (Q2.reps (⟨108, by decide⟩ : Fin 148)) (colE2 ⟨108, by decide⟩ 1 hp)
        (rowE2 (⟨108, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨108, by decide⟩ : Fin 148))
        (colE1 ⟨108, by decide⟩ 1 (transLenTr ⟨108, by decide⟩ 1 hp))
        (rowE1 (⟨108, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨108, by decide⟩ : Fin 148) ⟨108, by decide⟩ _
      (validAt ⟨108, by decide⟩ (listedAt ⟨108, by decide⟩ hj))
      (colE1 ⟨108, by decide⟩ 1 (transLenTr ⟨108, by decide⟩ 1 hp)) T108_108
      hfix108_108 hinj108_108 hcardT108_108
      (fun i => conj_mem_of_fixedPoints _ _ (T108_108 i) (hfix108_108 i) _)
      ⟨108, by decide⟩ ⟨108, by decide⟩ _
      (Q2.validAt ⟨108, by decide⟩ (Q2.listedAt ⟨108, by decide⟩
        (alnCheck_rep ⟨108, by decide⟩ hj hq).1))
      (colE2 ⟨108, by decide⟩ 1 hp) Q2.T108_108_2 Q2.hfix108_108_2 Q2.hinj108_108_2
      Q2.hcardT108_108_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T108_108_2 i) (Q2.hfix108_108_2 i) _)
      colCert_108_108_1.hD ?_).symm
  rw [alnId_108 j hj]


theorem leaf_108_108_2 (hp : 2 < (Q2.transData.getD 108 []).length)
    (j : Nat) (hj : j < (repChars.getD 108 []).length)
    (hq : (normIsRep.getD 108 []).getD j false = true) :
    species (Q2.reps (⟨108, by decide⟩ : Fin 148)) (colE2 ⟨108, by decide⟩ 2 hp)
        (rowE2 (⟨108, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨108, by decide⟩ : Fin 148))
        (colE1 ⟨108, by decide⟩ 2 (transLenTr ⟨108, by decide⟩ 2 hp))
        (rowE1 (⟨108, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨108, by decide⟩ : Fin 148) ⟨108, by decide⟩ _
      (validAt ⟨108, by decide⟩ (listedAt ⟨108, by decide⟩ hj))
      (colE1 ⟨108, by decide⟩ 2 (transLenTr ⟨108, by decide⟩ 2 hp)) T108_108
      hfix108_108 hinj108_108 hcardT108_108
      (fun i => conj_mem_of_fixedPoints _ _ (T108_108 i) (hfix108_108 i) _)
      ⟨108, by decide⟩ ⟨108, by decide⟩ _
      (Q2.validAt ⟨108, by decide⟩ (Q2.listedAt ⟨108, by decide⟩
        (alnCheck_rep ⟨108, by decide⟩ hj hq).1))
      (colE2 ⟨108, by decide⟩ 2 hp) Q2.T108_108_2 Q2.hfix108_108_2 Q2.hinj108_108_2
      Q2.hcardT108_108_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T108_108_2 i) (Q2.hfix108_108_2 i) _)
      colCert_108_108_2.hD ?_).symm
  rw [alnId_108 j hj]


theorem leaf_108_108_3 (hp : 3 < (Q2.transData.getD 108 []).length)
    (j : Nat) (hj : j < (repChars.getD 108 []).length)
    (hq : (normIsRep.getD 108 []).getD j false = true) :
    species (Q2.reps (⟨108, by decide⟩ : Fin 148)) (colE2 ⟨108, by decide⟩ 3 hp)
        (rowE2 (⟨108, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨108, by decide⟩ : Fin 148))
        (colE1 ⟨108, by decide⟩ 3 (transLenTr ⟨108, by decide⟩ 3 hp))
        (rowE1 (⟨108, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨108, by decide⟩ : Fin 148) ⟨108, by decide⟩ _
      (validAt ⟨108, by decide⟩ (listedAt ⟨108, by decide⟩ hj))
      (colE1 ⟨108, by decide⟩ 3 (transLenTr ⟨108, by decide⟩ 3 hp)) T108_108
      hfix108_108 hinj108_108 hcardT108_108
      (fun i => conj_mem_of_fixedPoints _ _ (T108_108 i) (hfix108_108 i) _)
      ⟨108, by decide⟩ ⟨108, by decide⟩ _
      (Q2.validAt ⟨108, by decide⟩ (Q2.listedAt ⟨108, by decide⟩
        (alnCheck_rep ⟨108, by decide⟩ hj hq).1))
      (colE2 ⟨108, by decide⟩ 3 hp) Q2.T108_108_2 Q2.hfix108_108_2 Q2.hinj108_108_2
      Q2.hcardT108_108_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T108_108_2 i) (Q2.hfix108_108_2 i) _)
      colCert_108_108_3.hD ?_).symm
  rw [alnId_108 j hj]


theorem leaf_108_108_4 (hp : 4 < (Q2.transData.getD 108 []).length)
    (j : Nat) (hj : j < (repChars.getD 108 []).length)
    (hq : (normIsRep.getD 108 []).getD j false = true) :
    species (Q2.reps (⟨108, by decide⟩ : Fin 148)) (colE2 ⟨108, by decide⟩ 4 hp)
        (rowE2 (⟨108, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨108, by decide⟩ : Fin 148))
        (colE1 ⟨108, by decide⟩ 4 (transLenTr ⟨108, by decide⟩ 4 hp))
        (rowE1 (⟨108, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨108, by decide⟩ : Fin 148) ⟨108, by decide⟩ _
      (validAt ⟨108, by decide⟩ (listedAt ⟨108, by decide⟩ hj))
      (colE1 ⟨108, by decide⟩ 4 (transLenTr ⟨108, by decide⟩ 4 hp)) T108_108
      hfix108_108 hinj108_108 hcardT108_108
      (fun i => conj_mem_of_fixedPoints _ _ (T108_108 i) (hfix108_108 i) _)
      ⟨108, by decide⟩ ⟨108, by decide⟩ _
      (Q2.validAt ⟨108, by decide⟩ (Q2.listedAt ⟨108, by decide⟩
        (alnCheck_rep ⟨108, by decide⟩ hj hq).1))
      (colE2 ⟨108, by decide⟩ 4 hp) Q2.T108_108_2 Q2.hfix108_108_2 Q2.hinj108_108_2
      Q2.hcardT108_108_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T108_108_2 i) (Q2.hfix108_108_2 i) _)
      colCert_108_108_4.hD ?_).symm
  rw [alnId_108 j hj]


theorem leaf_108_108_5 (hp : 5 < (Q2.transData.getD 108 []).length)
    (j : Nat) (hj : j < (repChars.getD 108 []).length)
    (hq : (normIsRep.getD 108 []).getD j false = true) :
    species (Q2.reps (⟨108, by decide⟩ : Fin 148)) (colE2 ⟨108, by decide⟩ 5 hp)
        (rowE2 (⟨108, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨108, by decide⟩ : Fin 148))
        (colE1 ⟨108, by decide⟩ 5 (transLenTr ⟨108, by decide⟩ 5 hp))
        (rowE1 (⟨108, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨108, by decide⟩ : Fin 148) ⟨108, by decide⟩ _
      (validAt ⟨108, by decide⟩ (listedAt ⟨108, by decide⟩ hj))
      (colE1 ⟨108, by decide⟩ 5 (transLenTr ⟨108, by decide⟩ 5 hp)) T108_108
      hfix108_108 hinj108_108 hcardT108_108
      (fun i => conj_mem_of_fixedPoints _ _ (T108_108 i) (hfix108_108 i) _)
      ⟨108, by decide⟩ ⟨108, by decide⟩ _
      (Q2.validAt ⟨108, by decide⟩ (Q2.listedAt ⟨108, by decide⟩
        (alnCheck_rep ⟨108, by decide⟩ hj hq).1))
      (colE2 ⟨108, by decide⟩ 5 hp) Q2.T108_108_2 Q2.hfix108_108_2 Q2.hinj108_108_2
      Q2.hcardT108_108_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T108_108_2 i) (Q2.hfix108_108_2 i) _)
      colCert_108_108_5.hD ?_).symm
  rw [alnId_108 j hj]


theorem leaf_108_108_10 (hp : 10 < (Q2.transData.getD 108 []).length)
    (j : Nat) (hj : j < (repChars.getD 108 []).length)
    (hq : (normIsRep.getD 108 []).getD j false = true) :
    species (Q2.reps (⟨108, by decide⟩ : Fin 148)) (colE2 ⟨108, by decide⟩ 10 hp)
        (rowE2 (⟨108, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨108, by decide⟩ : Fin 148))
        (colE1 ⟨108, by decide⟩ 10 (transLenTr ⟨108, by decide⟩ 10 hp))
        (rowE1 (⟨108, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨108, by decide⟩ : Fin 148) ⟨108, by decide⟩ _
      (validAt ⟨108, by decide⟩ (listedAt ⟨108, by decide⟩ hj))
      (colE1 ⟨108, by decide⟩ 10 (transLenTr ⟨108, by decide⟩ 10 hp)) T108_108
      hfix108_108 hinj108_108 hcardT108_108
      (fun i => conj_mem_of_fixedPoints _ _ (T108_108 i) (hfix108_108 i) _)
      ⟨108, by decide⟩ ⟨108, by decide⟩ _
      (Q2.validAt ⟨108, by decide⟩ (Q2.listedAt ⟨108, by decide⟩
        (alnCheck_rep ⟨108, by decide⟩ hj hq).1))
      (colE2 ⟨108, by decide⟩ 10 hp) Q2.T108_108_2 Q2.hfix108_108_2 Q2.hinj108_108_2
      Q2.hcardT108_108_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T108_108_2 i) (Q2.hfix108_108_2 i) _)
      colCert_108_108_10.hD ?_).symm
  rw [alnId_108 j hj]


theorem leaf_108_108_15 (hp : 15 < (Q2.transData.getD 108 []).length)
    (j : Nat) (hj : j < (repChars.getD 108 []).length)
    (hq : (normIsRep.getD 108 []).getD j false = true) :
    species (Q2.reps (⟨108, by decide⟩ : Fin 148)) (colE2 ⟨108, by decide⟩ 15 hp)
        (rowE2 (⟨108, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨108, by decide⟩ : Fin 148))
        (colE1 ⟨108, by decide⟩ 15 (transLenTr ⟨108, by decide⟩ 15 hp))
        (rowE1 (⟨108, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨108, by decide⟩ : Fin 148) ⟨108, by decide⟩ _
      (validAt ⟨108, by decide⟩ (listedAt ⟨108, by decide⟩ hj))
      (colE1 ⟨108, by decide⟩ 15 (transLenTr ⟨108, by decide⟩ 15 hp)) T108_108
      hfix108_108 hinj108_108 hcardT108_108
      (fun i => conj_mem_of_fixedPoints _ _ (T108_108 i) (hfix108_108 i) _)
      ⟨108, by decide⟩ ⟨108, by decide⟩ _
      (Q2.validAt ⟨108, by decide⟩ (Q2.listedAt ⟨108, by decide⟩
        (alnCheck_rep ⟨108, by decide⟩ hj hq).1))
      (colE2 ⟨108, by decide⟩ 15 hp) Q2.T108_108_2 Q2.hfix108_108_2 Q2.hinj108_108_2
      Q2.hcardT108_108_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T108_108_2 i) (Q2.hfix108_108_2 i) _)
      colCert_108_108_15.hD ?_).symm
  rw [alnId_108 j hj]


theorem leaf_108_108_20 (hp : 20 < (Q2.transData.getD 108 []).length)
    (j : Nat) (hj : j < (repChars.getD 108 []).length)
    (hq : (normIsRep.getD 108 []).getD j false = true) :
    species (Q2.reps (⟨108, by decide⟩ : Fin 148)) (colE2 ⟨108, by decide⟩ 20 hp)
        (rowE2 (⟨108, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨108, by decide⟩ : Fin 148))
        (colE1 ⟨108, by decide⟩ 20 (transLenTr ⟨108, by decide⟩ 20 hp))
        (rowE1 (⟨108, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨108, by decide⟩ : Fin 148) ⟨108, by decide⟩ _
      (validAt ⟨108, by decide⟩ (listedAt ⟨108, by decide⟩ hj))
      (colE1 ⟨108, by decide⟩ 20 (transLenTr ⟨108, by decide⟩ 20 hp)) T108_108
      hfix108_108 hinj108_108 hcardT108_108
      (fun i => conj_mem_of_fixedPoints _ _ (T108_108 i) (hfix108_108 i) _)
      ⟨108, by decide⟩ ⟨108, by decide⟩ _
      (Q2.validAt ⟨108, by decide⟩ (Q2.listedAt ⟨108, by decide⟩
        (alnCheck_rep ⟨108, by decide⟩ hj hq).1))
      (colE2 ⟨108, by decide⟩ 20 hp) Q2.T108_108_2 Q2.hfix108_108_2 Q2.hinj108_108_2
      Q2.hcardT108_108_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T108_108_2 i) (Q2.hfix108_108_2 i) _)
      colCert_108_108_20.hD ?_).symm
  rw [alnId_108 j hj]


theorem leaf_109_10_0 (hp : 0 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 109 []).length)
    (hq : (normIsRep.getD 109 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 0 hp)
        (rowE2 (⟨109, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 0 (transLenTr ⟨10, by decide⟩ 0 hp))
        (rowE1 (⟨109, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨109, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨109, by decide⟩ (listedAt ⟨109, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 0 (transLenTr ⟨10, by decide⟩ 0 hp)) T109_10
      hfix109_10 hinj109_10 hcardT109_10
      (fun i => conj_mem_of_fixedPoints _ _ (T109_10 i) (hfix109_10 i) _)
      ⟨109, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨109, by decide⟩ (Q2.listedAt ⟨109, by decide⟩
        (alnCheck_rep ⟨109, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 0 hp) Q2.T109_10_2 Q2.hfix109_10_2 Q2.hinj109_10_2
      Q2.hcardT109_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T109_10_2 i) (Q2.hfix109_10_2 i) _)
      colCert_109_10_0.hD ?_).symm
  rw [alnId_109 j hj]


end LeanDring.P5Presentation
