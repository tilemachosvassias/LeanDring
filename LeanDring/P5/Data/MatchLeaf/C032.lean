/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Data.ColCdd.C009
import LeanDring.P5.Data.ColCdd.C010
import LeanDring.P5.Data.ColRestCheap.C051
import LeanDring.P5.Data.ColRestCheap.C052
import LeanDring.P5.Data.ColRestCheap.C053
import LeanDring.P5.Data.ColRestCheap.C054
import LeanDring.P5.Data.EntryK.C030
import LeanDring.P5.Data.EntryK.C031
import LeanDring.P5.Certificate.RingIsomorphism.MatchCore
import LeanDring.P5.Data.SpeciesDiv.C065
import LeanDring.P5.Data.SpeciesDiv.C066
import LeanDring.P5.Data.SpeciesDiv.C067
import LeanDring.P5.Data.SpeciesDiv.C068

/-! # Stage-5 leaves, chunk 31 (auto-emitted).  -/

namespace LeanDring.P5Presentation

open MulAction Finset LeanDring.DRing LeanDring.MonGSet

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.style.longLine false

theorem leaf_123_38_4 (hp : 4 < (Q2.transData.getD 38 []).length)
    (j : Nat) (hj : j < (repChars.getD 123 []).length)
    (hq : (normIsRep.getD 123 []).getD j false = true) :
    species (Q2.reps (⟨38, by decide⟩ : Fin 148)) (colE2 ⟨38, by decide⟩ 4 hp)
        (rowE2 (⟨123, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨38, by decide⟩ : Fin 148))
        (colE1 ⟨38, by decide⟩ 4 (transLenTr ⟨38, by decide⟩ 4 hp))
        (rowE1 (⟨123, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨123, by decide⟩ : Fin 148) ⟨38, by decide⟩ _
      (validAt ⟨123, by decide⟩ (listedAt ⟨123, by decide⟩ hj))
      (colE1 ⟨38, by decide⟩ 4 (transLenTr ⟨38, by decide⟩ 4 hp)) T123_38
      hfix123_38 hinj123_38 hcardT123_38
      (fun i => conj_mem_of_fixedPoints _ _ (T123_38 i) (hfix123_38 i) _)
      ⟨123, by decide⟩ ⟨38, by decide⟩ _
      (Q2.validAt ⟨123, by decide⟩ (Q2.listedAt ⟨123, by decide⟩
        (alnCheck_rep ⟨123, by decide⟩ hj hq).1))
      (colE2 ⟨38, by decide⟩ 4 hp) Q2.T123_38_2 Q2.hfix123_38_2 Q2.hinj123_38_2
      Q2.hcardT123_38_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T123_38_2 i) (Q2.hfix123_38_2 i) _)
      colCert_123_38_4.hD ?_).symm
  rw [alnId_123 j hj]


theorem leaf_123_38_5 (hp : 5 < (Q2.transData.getD 38 []).length)
    (j : Nat) (hj : j < (repChars.getD 123 []).length)
    (hq : (normIsRep.getD 123 []).getD j false = true) :
    species (Q2.reps (⟨38, by decide⟩ : Fin 148)) (colE2 ⟨38, by decide⟩ 5 hp)
        (rowE2 (⟨123, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨38, by decide⟩ : Fin 148))
        (colE1 ⟨38, by decide⟩ 5 (transLenTr ⟨38, by decide⟩ 5 hp))
        (rowE1 (⟨123, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨123, by decide⟩ : Fin 148) ⟨38, by decide⟩ _
      (validAt ⟨123, by decide⟩ (listedAt ⟨123, by decide⟩ hj))
      (colE1 ⟨38, by decide⟩ 5 (transLenTr ⟨38, by decide⟩ 5 hp)) T123_38
      hfix123_38 hinj123_38 hcardT123_38
      (fun i => conj_mem_of_fixedPoints _ _ (T123_38 i) (hfix123_38 i) _)
      ⟨123, by decide⟩ ⟨38, by decide⟩ _
      (Q2.validAt ⟨123, by decide⟩ (Q2.listedAt ⟨123, by decide⟩
        (alnCheck_rep ⟨123, by decide⟩ hj hq).1))
      (colE2 ⟨38, by decide⟩ 5 hp) Q2.T123_38_2 Q2.hfix123_38_2 Q2.hinj123_38_2
      Q2.hcardT123_38_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T123_38_2 i) (Q2.hfix123_38_2 i) _)
      ?_).symm
  rw [show colData1 (⟨123, by decide⟩ : Fin 148)
        ((colE1 ⟨38, by decide⟩ 5 (transLenTr ⟨38, by decide⟩ 5 hp) : ↥(reps ⟨38, by decide⟩)) : Coordinate 1)
        T123_38 = colFn colCertDiv_123_38_5.D1 (m := 5) from colCertDiv_123_38_5.bind1,
    show colData2 (⟨123, by decide⟩ : Fin 148)
        ((colE2 ⟨38, by decide⟩ 5 hp : ↥(Q2.reps ⟨38, by decide⟩)) : Coordinate 2)
        Q2.T123_38_2 = colFn colCertDiv_123_38_5.D2 (m := 5) from colCertDiv_123_38_5.bind2]
  rw [alnId_123 j hj]
  exact fastcode_of_div ⟨123, by decide⟩ _ _ _
    ((alnId_123 j hj) ▸ Q2.listedAt (⟨123, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨123, by decide⟩ : Fin 148) hj hq).1) colCertDiv_123_38_5_match


theorem leaf_123_38_10 (hp : 10 < (Q2.transData.getD 38 []).length)
    (j : Nat) (hj : j < (repChars.getD 123 []).length)
    (hq : (normIsRep.getD 123 []).getD j false = true) :
    species (Q2.reps (⟨38, by decide⟩ : Fin 148)) (colE2 ⟨38, by decide⟩ 10 hp)
        (rowE2 (⟨123, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨38, by decide⟩ : Fin 148))
        (colE1 ⟨38, by decide⟩ 10 (transLenTr ⟨38, by decide⟩ 10 hp))
        (rowE1 (⟨123, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨123, by decide⟩ : Fin 148) ⟨38, by decide⟩ _
      (validAt ⟨123, by decide⟩ (listedAt ⟨123, by decide⟩ hj))
      (colE1 ⟨38, by decide⟩ 10 (transLenTr ⟨38, by decide⟩ 10 hp)) T123_38
      hfix123_38 hinj123_38 hcardT123_38
      (fun i => conj_mem_of_fixedPoints _ _ (T123_38 i) (hfix123_38 i) _)
      ⟨123, by decide⟩ ⟨38, by decide⟩ _
      (Q2.validAt ⟨123, by decide⟩ (Q2.listedAt ⟨123, by decide⟩
        (alnCheck_rep ⟨123, by decide⟩ hj hq).1))
      (colE2 ⟨38, by decide⟩ 10 hp) Q2.T123_38_2 Q2.hfix123_38_2 Q2.hinj123_38_2
      Q2.hcardT123_38_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T123_38_2 i) (Q2.hfix123_38_2 i) _)
      ?_).symm
  rw [show colData1 (⟨123, by decide⟩ : Fin 148)
        ((colE1 ⟨38, by decide⟩ 10 (transLenTr ⟨38, by decide⟩ 10 hp) : ↥(reps ⟨38, by decide⟩)) : Coordinate 1)
        T123_38 = colFn colCertDiv_123_38_10.D1 (m := 5) from colCertDiv_123_38_10.bind1,
    show colData2 (⟨123, by decide⟩ : Fin 148)
        ((colE2 ⟨38, by decide⟩ 10 hp : ↥(Q2.reps ⟨38, by decide⟩)) : Coordinate 2)
        Q2.T123_38_2 = colFn colCertDiv_123_38_10.D2 (m := 5) from colCertDiv_123_38_10.bind2]
  rw [alnId_123 j hj]
  exact fastcode_of_div ⟨123, by decide⟩ _ _ _
    ((alnId_123 j hj) ▸ Q2.listedAt (⟨123, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨123, by decide⟩ : Fin 148) hj hq).1) colCertDiv_123_38_10_match


theorem leaf_123_38_15 (hp : 15 < (Q2.transData.getD 38 []).length)
    (j : Nat) (hj : j < (repChars.getD 123 []).length)
    (hq : (normIsRep.getD 123 []).getD j false = true) :
    species (Q2.reps (⟨38, by decide⟩ : Fin 148)) (colE2 ⟨38, by decide⟩ 15 hp)
        (rowE2 (⟨123, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨38, by decide⟩ : Fin 148))
        (colE1 ⟨38, by decide⟩ 15 (transLenTr ⟨38, by decide⟩ 15 hp))
        (rowE1 (⟨123, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨123, by decide⟩ : Fin 148) ⟨38, by decide⟩ _
      (validAt ⟨123, by decide⟩ (listedAt ⟨123, by decide⟩ hj))
      (colE1 ⟨38, by decide⟩ 15 (transLenTr ⟨38, by decide⟩ 15 hp)) T123_38
      hfix123_38 hinj123_38 hcardT123_38
      (fun i => conj_mem_of_fixedPoints _ _ (T123_38 i) (hfix123_38 i) _)
      ⟨123, by decide⟩ ⟨38, by decide⟩ _
      (Q2.validAt ⟨123, by decide⟩ (Q2.listedAt ⟨123, by decide⟩
        (alnCheck_rep ⟨123, by decide⟩ hj hq).1))
      (colE2 ⟨38, by decide⟩ 15 hp) Q2.T123_38_2 Q2.hfix123_38_2 Q2.hinj123_38_2
      Q2.hcardT123_38_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T123_38_2 i) (Q2.hfix123_38_2 i) _)
      ?_).symm
  rw [show colData1 (⟨123, by decide⟩ : Fin 148)
        ((colE1 ⟨38, by decide⟩ 15 (transLenTr ⟨38, by decide⟩ 15 hp) : ↥(reps ⟨38, by decide⟩)) : Coordinate 1)
        T123_38 = colFn colCertDiv_123_38_15.D1 (m := 5) from colCertDiv_123_38_15.bind1,
    show colData2 (⟨123, by decide⟩ : Fin 148)
        ((colE2 ⟨38, by decide⟩ 15 hp : ↥(Q2.reps ⟨38, by decide⟩)) : Coordinate 2)
        Q2.T123_38_2 = colFn colCertDiv_123_38_15.D2 (m := 5) from colCertDiv_123_38_15.bind2]
  rw [alnId_123 j hj]
  exact fastcode_of_div ⟨123, by decide⟩ _ _ _
    ((alnId_123 j hj) ▸ Q2.listedAt (⟨123, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨123, by decide⟩ : Fin 148) hj hq).1) colCertDiv_123_38_15_match


theorem leaf_123_38_20 (hp : 20 < (Q2.transData.getD 38 []).length)
    (j : Nat) (hj : j < (repChars.getD 123 []).length)
    (hq : (normIsRep.getD 123 []).getD j false = true) :
    species (Q2.reps (⟨38, by decide⟩ : Fin 148)) (colE2 ⟨38, by decide⟩ 20 hp)
        (rowE2 (⟨123, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨38, by decide⟩ : Fin 148))
        (colE1 ⟨38, by decide⟩ 20 (transLenTr ⟨38, by decide⟩ 20 hp))
        (rowE1 (⟨123, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨123, by decide⟩ : Fin 148) ⟨38, by decide⟩ _
      (validAt ⟨123, by decide⟩ (listedAt ⟨123, by decide⟩ hj))
      (colE1 ⟨38, by decide⟩ 20 (transLenTr ⟨38, by decide⟩ 20 hp)) T123_38
      hfix123_38 hinj123_38 hcardT123_38
      (fun i => conj_mem_of_fixedPoints _ _ (T123_38 i) (hfix123_38 i) _)
      ⟨123, by decide⟩ ⟨38, by decide⟩ _
      (Q2.validAt ⟨123, by decide⟩ (Q2.listedAt ⟨123, by decide⟩
        (alnCheck_rep ⟨123, by decide⟩ hj hq).1))
      (colE2 ⟨38, by decide⟩ 20 hp) Q2.T123_38_2 Q2.hfix123_38_2 Q2.hinj123_38_2
      Q2.hcardT123_38_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T123_38_2 i) (Q2.hfix123_38_2 i) _)
      ?_).symm
  rw [show colData1 (⟨123, by decide⟩ : Fin 148)
        ((colE1 ⟨38, by decide⟩ 20 (transLenTr ⟨38, by decide⟩ 20 hp) : ↥(reps ⟨38, by decide⟩)) : Coordinate 1)
        T123_38 = colFn colCertDiv_123_38_20.D1 (m := 5) from colCertDiv_123_38_20.bind1,
    show colData2 (⟨123, by decide⟩ : Fin 148)
        ((colE2 ⟨38, by decide⟩ 20 hp : ↥(Q2.reps ⟨38, by decide⟩)) : Coordinate 2)
        Q2.T123_38_2 = colFn colCertDiv_123_38_20.D2 (m := 5) from colCertDiv_123_38_20.bind2]
  rw [alnId_123 j hj]
  exact fastcode_of_div ⟨123, by decide⟩ _ _ _
    ((alnId_123 j hj) ▸ Q2.listedAt (⟨123, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨123, by decide⟩ : Fin 148) hj hq).1) colCertDiv_123_38_20_match


theorem leaf_123_46_0 (hp : 0 < (Q2.transData.getD 46 []).length)
    (j : Nat) (hj : j < (repChars.getD 123 []).length)
    (hq : (normIsRep.getD 123 []).getD j false = true) :
    species (Q2.reps (⟨46, by decide⟩ : Fin 148)) (colE2 ⟨46, by decide⟩ 0 hp)
        (rowE2 (⟨123, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨46, by decide⟩ : Fin 148))
        (colE1 ⟨46, by decide⟩ 0 (transLenTr ⟨46, by decide⟩ 0 hp))
        (rowE1 (⟨123, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨123, by decide⟩ : Fin 148) ⟨46, by decide⟩ _
      (validAt ⟨123, by decide⟩ (listedAt ⟨123, by decide⟩ hj))
      (colE1 ⟨46, by decide⟩ 0 (transLenTr ⟨46, by decide⟩ 0 hp)) T123_46
      hfix123_46 hinj123_46 hcardT123_46
      (fun i => conj_mem_of_fixedPoints _ _ (T123_46 i) (hfix123_46 i) _)
      ⟨123, by decide⟩ ⟨46, by decide⟩ _
      (Q2.validAt ⟨123, by decide⟩ (Q2.listedAt ⟨123, by decide⟩
        (alnCheck_rep ⟨123, by decide⟩ hj hq).1))
      (colE2 ⟨46, by decide⟩ 0 hp) Q2.T123_46_2 Q2.hfix123_46_2 Q2.hinj123_46_2
      Q2.hcardT123_46_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T123_46_2 i) (Q2.hfix123_46_2 i) _)
      colCert_123_46_0.hD ?_).symm
  rw [alnId_123 j hj]


theorem leaf_123_46_1 (hp : 1 < (Q2.transData.getD 46 []).length)
    (j : Nat) (hj : j < (repChars.getD 123 []).length)
    (hq : (normIsRep.getD 123 []).getD j false = true) :
    species (Q2.reps (⟨46, by decide⟩ : Fin 148)) (colE2 ⟨46, by decide⟩ 1 hp)
        (rowE2 (⟨123, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨46, by decide⟩ : Fin 148))
        (colE1 ⟨46, by decide⟩ 1 (transLenTr ⟨46, by decide⟩ 1 hp))
        (rowE1 (⟨123, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨123, by decide⟩ : Fin 148) ⟨46, by decide⟩ _
      (validAt ⟨123, by decide⟩ (listedAt ⟨123, by decide⟩ hj))
      (colE1 ⟨46, by decide⟩ 1 (transLenTr ⟨46, by decide⟩ 1 hp)) T123_46
      hfix123_46 hinj123_46 hcardT123_46
      (fun i => conj_mem_of_fixedPoints _ _ (T123_46 i) (hfix123_46 i) _)
      ⟨123, by decide⟩ ⟨46, by decide⟩ _
      (Q2.validAt ⟨123, by decide⟩ (Q2.listedAt ⟨123, by decide⟩
        (alnCheck_rep ⟨123, by decide⟩ hj hq).1))
      (colE2 ⟨46, by decide⟩ 1 hp) Q2.T123_46_2 Q2.hfix123_46_2 Q2.hinj123_46_2
      Q2.hcardT123_46_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T123_46_2 i) (Q2.hfix123_46_2 i) _)
      colCert_123_46_1.hD ?_).symm
  rw [alnId_123 j hj]


theorem leaf_123_46_2 (hp : 2 < (Q2.transData.getD 46 []).length)
    (j : Nat) (hj : j < (repChars.getD 123 []).length)
    (hq : (normIsRep.getD 123 []).getD j false = true) :
    species (Q2.reps (⟨46, by decide⟩ : Fin 148)) (colE2 ⟨46, by decide⟩ 2 hp)
        (rowE2 (⟨123, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨46, by decide⟩ : Fin 148))
        (colE1 ⟨46, by decide⟩ 2 (transLenTr ⟨46, by decide⟩ 2 hp))
        (rowE1 (⟨123, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨123, by decide⟩ : Fin 148) ⟨46, by decide⟩ _
      (validAt ⟨123, by decide⟩ (listedAt ⟨123, by decide⟩ hj))
      (colE1 ⟨46, by decide⟩ 2 (transLenTr ⟨46, by decide⟩ 2 hp)) T123_46
      hfix123_46 hinj123_46 hcardT123_46
      (fun i => conj_mem_of_fixedPoints _ _ (T123_46 i) (hfix123_46 i) _)
      ⟨123, by decide⟩ ⟨46, by decide⟩ _
      (Q2.validAt ⟨123, by decide⟩ (Q2.listedAt ⟨123, by decide⟩
        (alnCheck_rep ⟨123, by decide⟩ hj hq).1))
      (colE2 ⟨46, by decide⟩ 2 hp) Q2.T123_46_2 Q2.hfix123_46_2 Q2.hinj123_46_2
      Q2.hcardT123_46_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T123_46_2 i) (Q2.hfix123_46_2 i) _)
      colCert_123_46_2.hD ?_).symm
  rw [alnId_123 j hj]


theorem leaf_123_46_3 (hp : 3 < (Q2.transData.getD 46 []).length)
    (j : Nat) (hj : j < (repChars.getD 123 []).length)
    (hq : (normIsRep.getD 123 []).getD j false = true) :
    species (Q2.reps (⟨46, by decide⟩ : Fin 148)) (colE2 ⟨46, by decide⟩ 3 hp)
        (rowE2 (⟨123, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨46, by decide⟩ : Fin 148))
        (colE1 ⟨46, by decide⟩ 3 (transLenTr ⟨46, by decide⟩ 3 hp))
        (rowE1 (⟨123, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨123, by decide⟩ : Fin 148) ⟨46, by decide⟩ _
      (validAt ⟨123, by decide⟩ (listedAt ⟨123, by decide⟩ hj))
      (colE1 ⟨46, by decide⟩ 3 (transLenTr ⟨46, by decide⟩ 3 hp)) T123_46
      hfix123_46 hinj123_46 hcardT123_46
      (fun i => conj_mem_of_fixedPoints _ _ (T123_46 i) (hfix123_46 i) _)
      ⟨123, by decide⟩ ⟨46, by decide⟩ _
      (Q2.validAt ⟨123, by decide⟩ (Q2.listedAt ⟨123, by decide⟩
        (alnCheck_rep ⟨123, by decide⟩ hj hq).1))
      (colE2 ⟨46, by decide⟩ 3 hp) Q2.T123_46_2 Q2.hfix123_46_2 Q2.hinj123_46_2
      Q2.hcardT123_46_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T123_46_2 i) (Q2.hfix123_46_2 i) _)
      colCert_123_46_3.hD ?_).symm
  rw [alnId_123 j hj]


theorem leaf_123_46_4 (hp : 4 < (Q2.transData.getD 46 []).length)
    (j : Nat) (hj : j < (repChars.getD 123 []).length)
    (hq : (normIsRep.getD 123 []).getD j false = true) :
    species (Q2.reps (⟨46, by decide⟩ : Fin 148)) (colE2 ⟨46, by decide⟩ 4 hp)
        (rowE2 (⟨123, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨46, by decide⟩ : Fin 148))
        (colE1 ⟨46, by decide⟩ 4 (transLenTr ⟨46, by decide⟩ 4 hp))
        (rowE1 (⟨123, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨123, by decide⟩ : Fin 148) ⟨46, by decide⟩ _
      (validAt ⟨123, by decide⟩ (listedAt ⟨123, by decide⟩ hj))
      (colE1 ⟨46, by decide⟩ 4 (transLenTr ⟨46, by decide⟩ 4 hp)) T123_46
      hfix123_46 hinj123_46 hcardT123_46
      (fun i => conj_mem_of_fixedPoints _ _ (T123_46 i) (hfix123_46 i) _)
      ⟨123, by decide⟩ ⟨46, by decide⟩ _
      (Q2.validAt ⟨123, by decide⟩ (Q2.listedAt ⟨123, by decide⟩
        (alnCheck_rep ⟨123, by decide⟩ hj hq).1))
      (colE2 ⟨46, by decide⟩ 4 hp) Q2.T123_46_2 Q2.hfix123_46_2 Q2.hinj123_46_2
      Q2.hcardT123_46_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T123_46_2 i) (Q2.hfix123_46_2 i) _)
      colCert_123_46_4.hD ?_).symm
  rw [alnId_123 j hj]


theorem leaf_123_46_5 (hp : 5 < (Q2.transData.getD 46 []).length)
    (j : Nat) (hj : j < (repChars.getD 123 []).length)
    (hq : (normIsRep.getD 123 []).getD j false = true) :
    species (Q2.reps (⟨46, by decide⟩ : Fin 148)) (colE2 ⟨46, by decide⟩ 5 hp)
        (rowE2 (⟨123, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨46, by decide⟩ : Fin 148))
        (colE1 ⟨46, by decide⟩ 5 (transLenTr ⟨46, by decide⟩ 5 hp))
        (rowE1 (⟨123, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨123, by decide⟩ : Fin 148) ⟨46, by decide⟩ _
      (validAt ⟨123, by decide⟩ (listedAt ⟨123, by decide⟩ hj))
      (colE1 ⟨46, by decide⟩ 5 (transLenTr ⟨46, by decide⟩ 5 hp)) T123_46
      hfix123_46 hinj123_46 hcardT123_46
      (fun i => conj_mem_of_fixedPoints _ _ (T123_46 i) (hfix123_46 i) _)
      ⟨123, by decide⟩ ⟨46, by decide⟩ _
      (Q2.validAt ⟨123, by decide⟩ (Q2.listedAt ⟨123, by decide⟩
        (alnCheck_rep ⟨123, by decide⟩ hj hq).1))
      (colE2 ⟨46, by decide⟩ 5 hp) Q2.T123_46_2 Q2.hfix123_46_2 Q2.hinj123_46_2
      Q2.hcardT123_46_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T123_46_2 i) (Q2.hfix123_46_2 i) _)
      colCert_123_46_5.hD ?_).symm
  rw [alnId_123 j hj]


theorem leaf_123_46_10 (hp : 10 < (Q2.transData.getD 46 []).length)
    (j : Nat) (hj : j < (repChars.getD 123 []).length)
    (hq : (normIsRep.getD 123 []).getD j false = true) :
    species (Q2.reps (⟨46, by decide⟩ : Fin 148)) (colE2 ⟨46, by decide⟩ 10 hp)
        (rowE2 (⟨123, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨46, by decide⟩ : Fin 148))
        (colE1 ⟨46, by decide⟩ 10 (transLenTr ⟨46, by decide⟩ 10 hp))
        (rowE1 (⟨123, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨123, by decide⟩ : Fin 148) ⟨46, by decide⟩ _
      (validAt ⟨123, by decide⟩ (listedAt ⟨123, by decide⟩ hj))
      (colE1 ⟨46, by decide⟩ 10 (transLenTr ⟨46, by decide⟩ 10 hp)) T123_46
      hfix123_46 hinj123_46 hcardT123_46
      (fun i => conj_mem_of_fixedPoints _ _ (T123_46 i) (hfix123_46 i) _)
      ⟨123, by decide⟩ ⟨46, by decide⟩ _
      (Q2.validAt ⟨123, by decide⟩ (Q2.listedAt ⟨123, by decide⟩
        (alnCheck_rep ⟨123, by decide⟩ hj hq).1))
      (colE2 ⟨46, by decide⟩ 10 hp) Q2.T123_46_2 Q2.hfix123_46_2 Q2.hinj123_46_2
      Q2.hcardT123_46_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T123_46_2 i) (Q2.hfix123_46_2 i) _)
      ?_).symm
  rw [show colData1 (⟨123, by decide⟩ : Fin 148)
        ((colE1 ⟨46, by decide⟩ 10 (transLenTr ⟨46, by decide⟩ 10 hp) : ↥(reps ⟨46, by decide⟩)) : Coordinate 1)
        T123_46 = colFn colCertDiv_123_46_10.D1 (m := 5) from colCertDiv_123_46_10.bind1,
    show colData2 (⟨123, by decide⟩ : Fin 148)
        ((colE2 ⟨46, by decide⟩ 10 hp : ↥(Q2.reps ⟨46, by decide⟩)) : Coordinate 2)
        Q2.T123_46_2 = colFn colCertDiv_123_46_10.D2 (m := 5) from colCertDiv_123_46_10.bind2]
  rw [alnId_123 j hj]
  exact fastcode_of_div ⟨123, by decide⟩ _ _ _
    ((alnId_123 j hj) ▸ Q2.listedAt (⟨123, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨123, by decide⟩ : Fin 148) hj hq).1) colCertDiv_123_46_10_match


theorem leaf_123_46_15 (hp : 15 < (Q2.transData.getD 46 []).length)
    (j : Nat) (hj : j < (repChars.getD 123 []).length)
    (hq : (normIsRep.getD 123 []).getD j false = true) :
    species (Q2.reps (⟨46, by decide⟩ : Fin 148)) (colE2 ⟨46, by decide⟩ 15 hp)
        (rowE2 (⟨123, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨46, by decide⟩ : Fin 148))
        (colE1 ⟨46, by decide⟩ 15 (transLenTr ⟨46, by decide⟩ 15 hp))
        (rowE1 (⟨123, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨123, by decide⟩ : Fin 148) ⟨46, by decide⟩ _
      (validAt ⟨123, by decide⟩ (listedAt ⟨123, by decide⟩ hj))
      (colE1 ⟨46, by decide⟩ 15 (transLenTr ⟨46, by decide⟩ 15 hp)) T123_46
      hfix123_46 hinj123_46 hcardT123_46
      (fun i => conj_mem_of_fixedPoints _ _ (T123_46 i) (hfix123_46 i) _)
      ⟨123, by decide⟩ ⟨46, by decide⟩ _
      (Q2.validAt ⟨123, by decide⟩ (Q2.listedAt ⟨123, by decide⟩
        (alnCheck_rep ⟨123, by decide⟩ hj hq).1))
      (colE2 ⟨46, by decide⟩ 15 hp) Q2.T123_46_2 Q2.hfix123_46_2 Q2.hinj123_46_2
      Q2.hcardT123_46_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T123_46_2 i) (Q2.hfix123_46_2 i) _)
      ?_).symm
  rw [show colData1 (⟨123, by decide⟩ : Fin 148)
        ((colE1 ⟨46, by decide⟩ 15 (transLenTr ⟨46, by decide⟩ 15 hp) : ↥(reps ⟨46, by decide⟩)) : Coordinate 1)
        T123_46 = colFn colCertDiv_123_46_15.D1 (m := 5) from colCertDiv_123_46_15.bind1,
    show colData2 (⟨123, by decide⟩ : Fin 148)
        ((colE2 ⟨46, by decide⟩ 15 hp : ↥(Q2.reps ⟨46, by decide⟩)) : Coordinate 2)
        Q2.T123_46_2 = colFn colCertDiv_123_46_15.D2 (m := 5) from colCertDiv_123_46_15.bind2]
  rw [alnId_123 j hj]
  exact fastcode_of_div ⟨123, by decide⟩ _ _ _
    ((alnId_123 j hj) ▸ Q2.listedAt (⟨123, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨123, by decide⟩ : Fin 148) hj hq).1) colCertDiv_123_46_15_match


theorem leaf_123_46_20 (hp : 20 < (Q2.transData.getD 46 []).length)
    (j : Nat) (hj : j < (repChars.getD 123 []).length)
    (hq : (normIsRep.getD 123 []).getD j false = true) :
    species (Q2.reps (⟨46, by decide⟩ : Fin 148)) (colE2 ⟨46, by decide⟩ 20 hp)
        (rowE2 (⟨123, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨46, by decide⟩ : Fin 148))
        (colE1 ⟨46, by decide⟩ 20 (transLenTr ⟨46, by decide⟩ 20 hp))
        (rowE1 (⟨123, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨123, by decide⟩ : Fin 148) ⟨46, by decide⟩ _
      (validAt ⟨123, by decide⟩ (listedAt ⟨123, by decide⟩ hj))
      (colE1 ⟨46, by decide⟩ 20 (transLenTr ⟨46, by decide⟩ 20 hp)) T123_46
      hfix123_46 hinj123_46 hcardT123_46
      (fun i => conj_mem_of_fixedPoints _ _ (T123_46 i) (hfix123_46 i) _)
      ⟨123, by decide⟩ ⟨46, by decide⟩ _
      (Q2.validAt ⟨123, by decide⟩ (Q2.listedAt ⟨123, by decide⟩
        (alnCheck_rep ⟨123, by decide⟩ hj hq).1))
      (colE2 ⟨46, by decide⟩ 20 hp) Q2.T123_46_2 Q2.hfix123_46_2 Q2.hinj123_46_2
      Q2.hcardT123_46_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T123_46_2 i) (Q2.hfix123_46_2 i) _)
      ?_).symm
  rw [show colData1 (⟨123, by decide⟩ : Fin 148)
        ((colE1 ⟨46, by decide⟩ 20 (transLenTr ⟨46, by decide⟩ 20 hp) : ↥(reps ⟨46, by decide⟩)) : Coordinate 1)
        T123_46 = colFn colCertDiv_123_46_20.D1 (m := 5) from colCertDiv_123_46_20.bind1,
    show colData2 (⟨123, by decide⟩ : Fin 148)
        ((colE2 ⟨46, by decide⟩ 20 hp : ↥(Q2.reps ⟨46, by decide⟩)) : Coordinate 2)
        Q2.T123_46_2 = colFn colCertDiv_123_46_20.D2 (m := 5) from colCertDiv_123_46_20.bind2]
  rw [alnId_123 j hj]
  exact fastcode_of_div ⟨123, by decide⟩ _ _ _
    ((alnId_123 j hj) ▸ Q2.listedAt (⟨123, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨123, by decide⟩ : Fin 148) hj hq).1) colCertDiv_123_46_20_match


theorem leaf_123_50_0 (hp : 0 < (Q2.transData.getD 50 []).length)
    (j : Nat) (hj : j < (repChars.getD 123 []).length)
    (hq : (normIsRep.getD 123 []).getD j false = true) :
    species (Q2.reps (⟨50, by decide⟩ : Fin 148)) (colE2 ⟨50, by decide⟩ 0 hp)
        (rowE2 (⟨123, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨50, by decide⟩ : Fin 148))
        (colE1 ⟨50, by decide⟩ 0 (transLenTr ⟨50, by decide⟩ 0 hp))
        (rowE1 (⟨123, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨123, by decide⟩ : Fin 148) ⟨50, by decide⟩ _
      (validAt ⟨123, by decide⟩ (listedAt ⟨123, by decide⟩ hj))
      (colE1 ⟨50, by decide⟩ 0 (transLenTr ⟨50, by decide⟩ 0 hp)) T123_50
      hfix123_50 hinj123_50 hcardT123_50
      (fun i => conj_mem_of_fixedPoints _ _ (T123_50 i) (hfix123_50 i) _)
      ⟨123, by decide⟩ ⟨50, by decide⟩ _
      (Q2.validAt ⟨123, by decide⟩ (Q2.listedAt ⟨123, by decide⟩
        (alnCheck_rep ⟨123, by decide⟩ hj hq).1))
      (colE2 ⟨50, by decide⟩ 0 hp) Q2.T123_50_2 Q2.hfix123_50_2 Q2.hinj123_50_2
      Q2.hcardT123_50_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T123_50_2 i) (Q2.hfix123_50_2 i) _)
      colCert_123_50_0.hD ?_).symm
  rw [alnId_123 j hj]


theorem leaf_123_50_1 (hp : 1 < (Q2.transData.getD 50 []).length)
    (j : Nat) (hj : j < (repChars.getD 123 []).length)
    (hq : (normIsRep.getD 123 []).getD j false = true) :
    species (Q2.reps (⟨50, by decide⟩ : Fin 148)) (colE2 ⟨50, by decide⟩ 1 hp)
        (rowE2 (⟨123, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨50, by decide⟩ : Fin 148))
        (colE1 ⟨50, by decide⟩ 1 (transLenTr ⟨50, by decide⟩ 1 hp))
        (rowE1 (⟨123, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨123, by decide⟩ : Fin 148) ⟨50, by decide⟩ _
      (validAt ⟨123, by decide⟩ (listedAt ⟨123, by decide⟩ hj))
      (colE1 ⟨50, by decide⟩ 1 (transLenTr ⟨50, by decide⟩ 1 hp)) T123_50
      hfix123_50 hinj123_50 hcardT123_50
      (fun i => conj_mem_of_fixedPoints _ _ (T123_50 i) (hfix123_50 i) _)
      ⟨123, by decide⟩ ⟨50, by decide⟩ _
      (Q2.validAt ⟨123, by decide⟩ (Q2.listedAt ⟨123, by decide⟩
        (alnCheck_rep ⟨123, by decide⟩ hj hq).1))
      (colE2 ⟨50, by decide⟩ 1 hp) Q2.T123_50_2 Q2.hfix123_50_2 Q2.hinj123_50_2
      Q2.hcardT123_50_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T123_50_2 i) (Q2.hfix123_50_2 i) _)
      colCert_123_50_1.hD ?_).symm
  rw [alnId_123 j hj]


theorem leaf_123_50_2 (hp : 2 < (Q2.transData.getD 50 []).length)
    (j : Nat) (hj : j < (repChars.getD 123 []).length)
    (hq : (normIsRep.getD 123 []).getD j false = true) :
    species (Q2.reps (⟨50, by decide⟩ : Fin 148)) (colE2 ⟨50, by decide⟩ 2 hp)
        (rowE2 (⟨123, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨50, by decide⟩ : Fin 148))
        (colE1 ⟨50, by decide⟩ 2 (transLenTr ⟨50, by decide⟩ 2 hp))
        (rowE1 (⟨123, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨123, by decide⟩ : Fin 148) ⟨50, by decide⟩ _
      (validAt ⟨123, by decide⟩ (listedAt ⟨123, by decide⟩ hj))
      (colE1 ⟨50, by decide⟩ 2 (transLenTr ⟨50, by decide⟩ 2 hp)) T123_50
      hfix123_50 hinj123_50 hcardT123_50
      (fun i => conj_mem_of_fixedPoints _ _ (T123_50 i) (hfix123_50 i) _)
      ⟨123, by decide⟩ ⟨50, by decide⟩ _
      (Q2.validAt ⟨123, by decide⟩ (Q2.listedAt ⟨123, by decide⟩
        (alnCheck_rep ⟨123, by decide⟩ hj hq).1))
      (colE2 ⟨50, by decide⟩ 2 hp) Q2.T123_50_2 Q2.hfix123_50_2 Q2.hinj123_50_2
      Q2.hcardT123_50_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T123_50_2 i) (Q2.hfix123_50_2 i) _)
      colCert_123_50_2.hD ?_).symm
  rw [alnId_123 j hj]


theorem leaf_123_50_3 (hp : 3 < (Q2.transData.getD 50 []).length)
    (j : Nat) (hj : j < (repChars.getD 123 []).length)
    (hq : (normIsRep.getD 123 []).getD j false = true) :
    species (Q2.reps (⟨50, by decide⟩ : Fin 148)) (colE2 ⟨50, by decide⟩ 3 hp)
        (rowE2 (⟨123, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨50, by decide⟩ : Fin 148))
        (colE1 ⟨50, by decide⟩ 3 (transLenTr ⟨50, by decide⟩ 3 hp))
        (rowE1 (⟨123, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨123, by decide⟩ : Fin 148) ⟨50, by decide⟩ _
      (validAt ⟨123, by decide⟩ (listedAt ⟨123, by decide⟩ hj))
      (colE1 ⟨50, by decide⟩ 3 (transLenTr ⟨50, by decide⟩ 3 hp)) T123_50
      hfix123_50 hinj123_50 hcardT123_50
      (fun i => conj_mem_of_fixedPoints _ _ (T123_50 i) (hfix123_50 i) _)
      ⟨123, by decide⟩ ⟨50, by decide⟩ _
      (Q2.validAt ⟨123, by decide⟩ (Q2.listedAt ⟨123, by decide⟩
        (alnCheck_rep ⟨123, by decide⟩ hj hq).1))
      (colE2 ⟨50, by decide⟩ 3 hp) Q2.T123_50_2 Q2.hfix123_50_2 Q2.hinj123_50_2
      Q2.hcardT123_50_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T123_50_2 i) (Q2.hfix123_50_2 i) _)
      colCert_123_50_3.hD ?_).symm
  rw [alnId_123 j hj]


theorem leaf_123_50_4 (hp : 4 < (Q2.transData.getD 50 []).length)
    (j : Nat) (hj : j < (repChars.getD 123 []).length)
    (hq : (normIsRep.getD 123 []).getD j false = true) :
    species (Q2.reps (⟨50, by decide⟩ : Fin 148)) (colE2 ⟨50, by decide⟩ 4 hp)
        (rowE2 (⟨123, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨50, by decide⟩ : Fin 148))
        (colE1 ⟨50, by decide⟩ 4 (transLenTr ⟨50, by decide⟩ 4 hp))
        (rowE1 (⟨123, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨123, by decide⟩ : Fin 148) ⟨50, by decide⟩ _
      (validAt ⟨123, by decide⟩ (listedAt ⟨123, by decide⟩ hj))
      (colE1 ⟨50, by decide⟩ 4 (transLenTr ⟨50, by decide⟩ 4 hp)) T123_50
      hfix123_50 hinj123_50 hcardT123_50
      (fun i => conj_mem_of_fixedPoints _ _ (T123_50 i) (hfix123_50 i) _)
      ⟨123, by decide⟩ ⟨50, by decide⟩ _
      (Q2.validAt ⟨123, by decide⟩ (Q2.listedAt ⟨123, by decide⟩
        (alnCheck_rep ⟨123, by decide⟩ hj hq).1))
      (colE2 ⟨50, by decide⟩ 4 hp) Q2.T123_50_2 Q2.hfix123_50_2 Q2.hinj123_50_2
      Q2.hcardT123_50_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T123_50_2 i) (Q2.hfix123_50_2 i) _)
      colCert_123_50_4.hD ?_).symm
  rw [alnId_123 j hj]


theorem leaf_123_50_5 (hp : 5 < (Q2.transData.getD 50 []).length)
    (j : Nat) (hj : j < (repChars.getD 123 []).length)
    (hq : (normIsRep.getD 123 []).getD j false = true) :
    species (Q2.reps (⟨50, by decide⟩ : Fin 148)) (colE2 ⟨50, by decide⟩ 5 hp)
        (rowE2 (⟨123, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨50, by decide⟩ : Fin 148))
        (colE1 ⟨50, by decide⟩ 5 (transLenTr ⟨50, by decide⟩ 5 hp))
        (rowE1 (⟨123, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨123, by decide⟩ : Fin 148) ⟨50, by decide⟩ _
      (validAt ⟨123, by decide⟩ (listedAt ⟨123, by decide⟩ hj))
      (colE1 ⟨50, by decide⟩ 5 (transLenTr ⟨50, by decide⟩ 5 hp)) T123_50
      hfix123_50 hinj123_50 hcardT123_50
      (fun i => conj_mem_of_fixedPoints _ _ (T123_50 i) (hfix123_50 i) _)
      ⟨123, by decide⟩ ⟨50, by decide⟩ _
      (Q2.validAt ⟨123, by decide⟩ (Q2.listedAt ⟨123, by decide⟩
        (alnCheck_rep ⟨123, by decide⟩ hj hq).1))
      (colE2 ⟨50, by decide⟩ 5 hp) Q2.T123_50_2 Q2.hfix123_50_2 Q2.hinj123_50_2
      Q2.hcardT123_50_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T123_50_2 i) (Q2.hfix123_50_2 i) _)
      ?_).symm
  rw [show colData1 (⟨123, by decide⟩ : Fin 148)
        ((colE1 ⟨50, by decide⟩ 5 (transLenTr ⟨50, by decide⟩ 5 hp) : ↥(reps ⟨50, by decide⟩)) : Coordinate 1)
        T123_50 = colFn colCertDiv_123_50_5.D1 (m := 5) from colCertDiv_123_50_5.bind1,
    show colData2 (⟨123, by decide⟩ : Fin 148)
        ((colE2 ⟨50, by decide⟩ 5 hp : ↥(Q2.reps ⟨50, by decide⟩)) : Coordinate 2)
        Q2.T123_50_2 = colFn colCertDiv_123_50_5.D2 (m := 5) from colCertDiv_123_50_5.bind2]
  rw [alnId_123 j hj]
  exact fastcode_of_div ⟨123, by decide⟩ _ _ _
    ((alnId_123 j hj) ▸ Q2.listedAt (⟨123, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨123, by decide⟩ : Fin 148) hj hq).1) colCertDiv_123_50_5_match


theorem leaf_123_50_10 (hp : 10 < (Q2.transData.getD 50 []).length)
    (j : Nat) (hj : j < (repChars.getD 123 []).length)
    (hq : (normIsRep.getD 123 []).getD j false = true) :
    species (Q2.reps (⟨50, by decide⟩ : Fin 148)) (colE2 ⟨50, by decide⟩ 10 hp)
        (rowE2 (⟨123, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨50, by decide⟩ : Fin 148))
        (colE1 ⟨50, by decide⟩ 10 (transLenTr ⟨50, by decide⟩ 10 hp))
        (rowE1 (⟨123, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨123, by decide⟩ : Fin 148) ⟨50, by decide⟩ _
      (validAt ⟨123, by decide⟩ (listedAt ⟨123, by decide⟩ hj))
      (colE1 ⟨50, by decide⟩ 10 (transLenTr ⟨50, by decide⟩ 10 hp)) T123_50
      hfix123_50 hinj123_50 hcardT123_50
      (fun i => conj_mem_of_fixedPoints _ _ (T123_50 i) (hfix123_50 i) _)
      ⟨123, by decide⟩ ⟨50, by decide⟩ _
      (Q2.validAt ⟨123, by decide⟩ (Q2.listedAt ⟨123, by decide⟩
        (alnCheck_rep ⟨123, by decide⟩ hj hq).1))
      (colE2 ⟨50, by decide⟩ 10 hp) Q2.T123_50_2 Q2.hfix123_50_2 Q2.hinj123_50_2
      Q2.hcardT123_50_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T123_50_2 i) (Q2.hfix123_50_2 i) _)
      ?_).symm
  rw [show colData1 (⟨123, by decide⟩ : Fin 148)
        ((colE1 ⟨50, by decide⟩ 10 (transLenTr ⟨50, by decide⟩ 10 hp) : ↥(reps ⟨50, by decide⟩)) : Coordinate 1)
        T123_50 = colFn colCertDiv_123_50_10.D1 (m := 5) from colCertDiv_123_50_10.bind1,
    show colData2 (⟨123, by decide⟩ : Fin 148)
        ((colE2 ⟨50, by decide⟩ 10 hp : ↥(Q2.reps ⟨50, by decide⟩)) : Coordinate 2)
        Q2.T123_50_2 = colFn colCertDiv_123_50_10.D2 (m := 5) from colCertDiv_123_50_10.bind2]
  rw [alnId_123 j hj]
  exact fastcode_of_div ⟨123, by decide⟩ _ _ _
    ((alnId_123 j hj) ▸ Q2.listedAt (⟨123, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨123, by decide⟩ : Fin 148) hj hq).1) colCertDiv_123_50_10_match


theorem leaf_123_50_15 (hp : 15 < (Q2.transData.getD 50 []).length)
    (j : Nat) (hj : j < (repChars.getD 123 []).length)
    (hq : (normIsRep.getD 123 []).getD j false = true) :
    species (Q2.reps (⟨50, by decide⟩ : Fin 148)) (colE2 ⟨50, by decide⟩ 15 hp)
        (rowE2 (⟨123, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨50, by decide⟩ : Fin 148))
        (colE1 ⟨50, by decide⟩ 15 (transLenTr ⟨50, by decide⟩ 15 hp))
        (rowE1 (⟨123, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨123, by decide⟩ : Fin 148) ⟨50, by decide⟩ _
      (validAt ⟨123, by decide⟩ (listedAt ⟨123, by decide⟩ hj))
      (colE1 ⟨50, by decide⟩ 15 (transLenTr ⟨50, by decide⟩ 15 hp)) T123_50
      hfix123_50 hinj123_50 hcardT123_50
      (fun i => conj_mem_of_fixedPoints _ _ (T123_50 i) (hfix123_50 i) _)
      ⟨123, by decide⟩ ⟨50, by decide⟩ _
      (Q2.validAt ⟨123, by decide⟩ (Q2.listedAt ⟨123, by decide⟩
        (alnCheck_rep ⟨123, by decide⟩ hj hq).1))
      (colE2 ⟨50, by decide⟩ 15 hp) Q2.T123_50_2 Q2.hfix123_50_2 Q2.hinj123_50_2
      Q2.hcardT123_50_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T123_50_2 i) (Q2.hfix123_50_2 i) _)
      ?_).symm
  rw [show colData1 (⟨123, by decide⟩ : Fin 148)
        ((colE1 ⟨50, by decide⟩ 15 (transLenTr ⟨50, by decide⟩ 15 hp) : ↥(reps ⟨50, by decide⟩)) : Coordinate 1)
        T123_50 = colFn colCertDiv_123_50_15.D1 (m := 5) from colCertDiv_123_50_15.bind1,
    show colData2 (⟨123, by decide⟩ : Fin 148)
        ((colE2 ⟨50, by decide⟩ 15 hp : ↥(Q2.reps ⟨50, by decide⟩)) : Coordinate 2)
        Q2.T123_50_2 = colFn colCertDiv_123_50_15.D2 (m := 5) from colCertDiv_123_50_15.bind2]
  rw [alnId_123 j hj]
  exact fastcode_of_div ⟨123, by decide⟩ _ _ _
    ((alnId_123 j hj) ▸ Q2.listedAt (⟨123, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨123, by decide⟩ : Fin 148) hj hq).1) colCertDiv_123_50_15_match


theorem leaf_123_50_20 (hp : 20 < (Q2.transData.getD 50 []).length)
    (j : Nat) (hj : j < (repChars.getD 123 []).length)
    (hq : (normIsRep.getD 123 []).getD j false = true) :
    species (Q2.reps (⟨50, by decide⟩ : Fin 148)) (colE2 ⟨50, by decide⟩ 20 hp)
        (rowE2 (⟨123, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨50, by decide⟩ : Fin 148))
        (colE1 ⟨50, by decide⟩ 20 (transLenTr ⟨50, by decide⟩ 20 hp))
        (rowE1 (⟨123, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨123, by decide⟩ : Fin 148) ⟨50, by decide⟩ _
      (validAt ⟨123, by decide⟩ (listedAt ⟨123, by decide⟩ hj))
      (colE1 ⟨50, by decide⟩ 20 (transLenTr ⟨50, by decide⟩ 20 hp)) T123_50
      hfix123_50 hinj123_50 hcardT123_50
      (fun i => conj_mem_of_fixedPoints _ _ (T123_50 i) (hfix123_50 i) _)
      ⟨123, by decide⟩ ⟨50, by decide⟩ _
      (Q2.validAt ⟨123, by decide⟩ (Q2.listedAt ⟨123, by decide⟩
        (alnCheck_rep ⟨123, by decide⟩ hj hq).1))
      (colE2 ⟨50, by decide⟩ 20 hp) Q2.T123_50_2 Q2.hfix123_50_2 Q2.hinj123_50_2
      Q2.hcardT123_50_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T123_50_2 i) (Q2.hfix123_50_2 i) _)
      ?_).symm
  rw [show colData1 (⟨123, by decide⟩ : Fin 148)
        ((colE1 ⟨50, by decide⟩ 20 (transLenTr ⟨50, by decide⟩ 20 hp) : ↥(reps ⟨50, by decide⟩)) : Coordinate 1)
        T123_50 = colFn colCertDiv_123_50_20.D1 (m := 5) from colCertDiv_123_50_20.bind1,
    show colData2 (⟨123, by decide⟩ : Fin 148)
        ((colE2 ⟨50, by decide⟩ 20 hp : ↥(Q2.reps ⟨50, by decide⟩)) : Coordinate 2)
        Q2.T123_50_2 = colFn colCertDiv_123_50_20.D2 (m := 5) from colCertDiv_123_50_20.bind2]
  rw [alnId_123 j hj]
  exact fastcode_of_div ⟨123, by decide⟩ _ _ _
    ((alnId_123 j hj) ▸ Q2.listedAt (⟨123, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨123, by decide⟩ : Fin 148) hj hq).1) colCertDiv_123_50_20_match


theorem leaf_123_53_0 (hp : 0 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 123 []).length)
    (hq : (normIsRep.getD 123 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 0 hp)
        (rowE2 (⟨123, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 0 (transLenTr ⟨53, by decide⟩ 0 hp))
        (rowE1 (⟨123, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨123, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨123, by decide⟩ (listedAt ⟨123, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 0 (transLenTr ⟨53, by decide⟩ 0 hp)) T123_53
      hfix123_53 hinj123_53 hcardT123_53
      (fun i => conj_mem_of_fixedPoints _ _ (T123_53 i) (hfix123_53 i) _)
      ⟨123, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨123, by decide⟩ (Q2.listedAt ⟨123, by decide⟩
        (alnCheck_rep ⟨123, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 0 hp) Q2.T123_53_2 Q2.hfix123_53_2 Q2.hinj123_53_2
      Q2.hcardT123_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T123_53_2 i) (Q2.hfix123_53_2 i) _)
      colCert_123_53_0.hD ?_).symm
  rw [alnId_123 j hj]


theorem leaf_123_53_1 (hp : 1 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 123 []).length)
    (hq : (normIsRep.getD 123 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 1 hp)
        (rowE2 (⟨123, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 1 (transLenTr ⟨53, by decide⟩ 1 hp))
        (rowE1 (⟨123, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨123, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨123, by decide⟩ (listedAt ⟨123, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 1 (transLenTr ⟨53, by decide⟩ 1 hp)) T123_53
      hfix123_53 hinj123_53 hcardT123_53
      (fun i => conj_mem_of_fixedPoints _ _ (T123_53 i) (hfix123_53 i) _)
      ⟨123, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨123, by decide⟩ (Q2.listedAt ⟨123, by decide⟩
        (alnCheck_rep ⟨123, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 1 hp) Q2.T123_53_2 Q2.hfix123_53_2 Q2.hinj123_53_2
      Q2.hcardT123_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T123_53_2 i) (Q2.hfix123_53_2 i) _)
      colCert_123_53_1.hD ?_).symm
  rw [alnId_123 j hj]


theorem leaf_123_53_2 (hp : 2 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 123 []).length)
    (hq : (normIsRep.getD 123 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 2 hp)
        (rowE2 (⟨123, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 2 (transLenTr ⟨53, by decide⟩ 2 hp))
        (rowE1 (⟨123, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨123, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨123, by decide⟩ (listedAt ⟨123, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 2 (transLenTr ⟨53, by decide⟩ 2 hp)) T123_53
      hfix123_53 hinj123_53 hcardT123_53
      (fun i => conj_mem_of_fixedPoints _ _ (T123_53 i) (hfix123_53 i) _)
      ⟨123, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨123, by decide⟩ (Q2.listedAt ⟨123, by decide⟩
        (alnCheck_rep ⟨123, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 2 hp) Q2.T123_53_2 Q2.hfix123_53_2 Q2.hinj123_53_2
      Q2.hcardT123_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T123_53_2 i) (Q2.hfix123_53_2 i) _)
      colCert_123_53_2.hD ?_).symm
  rw [alnId_123 j hj]


theorem leaf_123_53_3 (hp : 3 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 123 []).length)
    (hq : (normIsRep.getD 123 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 3 hp)
        (rowE2 (⟨123, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 3 (transLenTr ⟨53, by decide⟩ 3 hp))
        (rowE1 (⟨123, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨123, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨123, by decide⟩ (listedAt ⟨123, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 3 (transLenTr ⟨53, by decide⟩ 3 hp)) T123_53
      hfix123_53 hinj123_53 hcardT123_53
      (fun i => conj_mem_of_fixedPoints _ _ (T123_53 i) (hfix123_53 i) _)
      ⟨123, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨123, by decide⟩ (Q2.listedAt ⟨123, by decide⟩
        (alnCheck_rep ⟨123, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 3 hp) Q2.T123_53_2 Q2.hfix123_53_2 Q2.hinj123_53_2
      Q2.hcardT123_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T123_53_2 i) (Q2.hfix123_53_2 i) _)
      colCert_123_53_3.hD ?_).symm
  rw [alnId_123 j hj]


theorem leaf_123_53_4 (hp : 4 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 123 []).length)
    (hq : (normIsRep.getD 123 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 4 hp)
        (rowE2 (⟨123, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 4 (transLenTr ⟨53, by decide⟩ 4 hp))
        (rowE1 (⟨123, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨123, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨123, by decide⟩ (listedAt ⟨123, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 4 (transLenTr ⟨53, by decide⟩ 4 hp)) T123_53
      hfix123_53 hinj123_53 hcardT123_53
      (fun i => conj_mem_of_fixedPoints _ _ (T123_53 i) (hfix123_53 i) _)
      ⟨123, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨123, by decide⟩ (Q2.listedAt ⟨123, by decide⟩
        (alnCheck_rep ⟨123, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 4 hp) Q2.T123_53_2 Q2.hfix123_53_2 Q2.hinj123_53_2
      Q2.hcardT123_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T123_53_2 i) (Q2.hfix123_53_2 i) _)
      colCert_123_53_4.hD ?_).symm
  rw [alnId_123 j hj]


theorem leaf_123_53_5 (hp : 5 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 123 []).length)
    (hq : (normIsRep.getD 123 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 5 hp)
        (rowE2 (⟨123, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 5 (transLenTr ⟨53, by decide⟩ 5 hp))
        (rowE1 (⟨123, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨123, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨123, by decide⟩ (listedAt ⟨123, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 5 (transLenTr ⟨53, by decide⟩ 5 hp)) T123_53
      hfix123_53 hinj123_53 hcardT123_53
      (fun i => conj_mem_of_fixedPoints _ _ (T123_53 i) (hfix123_53 i) _)
      ⟨123, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨123, by decide⟩ (Q2.listedAt ⟨123, by decide⟩
        (alnCheck_rep ⟨123, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 5 hp) Q2.T123_53_2 Q2.hfix123_53_2 Q2.hinj123_53_2
      Q2.hcardT123_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T123_53_2 i) (Q2.hfix123_53_2 i) _)
      colCert_123_53_5.hD ?_).symm
  rw [alnId_123 j hj]


theorem leaf_123_53_10 (hp : 10 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 123 []).length)
    (hq : (normIsRep.getD 123 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 10 hp)
        (rowE2 (⟨123, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 10 (transLenTr ⟨53, by decide⟩ 10 hp))
        (rowE1 (⟨123, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨123, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨123, by decide⟩ (listedAt ⟨123, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 10 (transLenTr ⟨53, by decide⟩ 10 hp)) T123_53
      hfix123_53 hinj123_53 hcardT123_53
      (fun i => conj_mem_of_fixedPoints _ _ (T123_53 i) (hfix123_53 i) _)
      ⟨123, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨123, by decide⟩ (Q2.listedAt ⟨123, by decide⟩
        (alnCheck_rep ⟨123, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 10 hp) Q2.T123_53_2 Q2.hfix123_53_2 Q2.hinj123_53_2
      Q2.hcardT123_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T123_53_2 i) (Q2.hfix123_53_2 i) _)
      colCert_123_53_10.hD ?_).symm
  rw [alnId_123 j hj]


theorem leaf_123_53_15 (hp : 15 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 123 []).length)
    (hq : (normIsRep.getD 123 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 15 hp)
        (rowE2 (⟨123, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 15 (transLenTr ⟨53, by decide⟩ 15 hp))
        (rowE1 (⟨123, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨123, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨123, by decide⟩ (listedAt ⟨123, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 15 (transLenTr ⟨53, by decide⟩ 15 hp)) T123_53
      hfix123_53 hinj123_53 hcardT123_53
      (fun i => conj_mem_of_fixedPoints _ _ (T123_53 i) (hfix123_53 i) _)
      ⟨123, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨123, by decide⟩ (Q2.listedAt ⟨123, by decide⟩
        (alnCheck_rep ⟨123, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 15 hp) Q2.T123_53_2 Q2.hfix123_53_2 Q2.hinj123_53_2
      Q2.hcardT123_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T123_53_2 i) (Q2.hfix123_53_2 i) _)
      colCert_123_53_15.hD ?_).symm
  rw [alnId_123 j hj]


theorem leaf_123_53_20 (hp : 20 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 123 []).length)
    (hq : (normIsRep.getD 123 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 20 hp)
        (rowE2 (⟨123, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 20 (transLenTr ⟨53, by decide⟩ 20 hp))
        (rowE1 (⟨123, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨123, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨123, by decide⟩ (listedAt ⟨123, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 20 (transLenTr ⟨53, by decide⟩ 20 hp)) T123_53
      hfix123_53 hinj123_53 hcardT123_53
      (fun i => conj_mem_of_fixedPoints _ _ (T123_53 i) (hfix123_53 i) _)
      ⟨123, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨123, by decide⟩ (Q2.listedAt ⟨123, by decide⟩
        (alnCheck_rep ⟨123, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 20 hp) Q2.T123_53_2 Q2.hfix123_53_2 Q2.hinj123_53_2
      Q2.hcardT123_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T123_53_2 i) (Q2.hfix123_53_2 i) _)
      colCert_123_53_20.hD ?_).symm
  rw [alnId_123 j hj]


theorem leaf_123_81_0 (hp : 0 < (Q2.transData.getD 81 []).length)
    (j : Nat) (hj : j < (repChars.getD 123 []).length)
    (hq : (normIsRep.getD 123 []).getD j false = true) :
    species (Q2.reps (⟨81, by decide⟩ : Fin 148)) (colE2 ⟨81, by decide⟩ 0 hp)
        (rowE2 (⟨123, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨81, by decide⟩ : Fin 148))
        (colE1 ⟨81, by decide⟩ 0 (transLenTr ⟨81, by decide⟩ 0 hp))
        (rowE1 (⟨123, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨123, by decide⟩ : Fin 148) ⟨81, by decide⟩ _
      (validAt ⟨123, by decide⟩ (listedAt ⟨123, by decide⟩ hj))
      (colE1 ⟨81, by decide⟩ 0 (transLenTr ⟨81, by decide⟩ 0 hp)) T123_81
      hfix123_81 hinj123_81 hcardT123_81
      (fun i => conj_mem_of_fixedPoints _ _ (T123_81 i) (hfix123_81 i) _)
      ⟨123, by decide⟩ ⟨81, by decide⟩ _
      (Q2.validAt ⟨123, by decide⟩ (Q2.listedAt ⟨123, by decide⟩
        (alnCheck_rep ⟨123, by decide⟩ hj hq).1))
      (colE2 ⟨81, by decide⟩ 0 hp) Q2.T123_81_2 Q2.hfix123_81_2 Q2.hinj123_81_2
      Q2.hcardT123_81_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T123_81_2 i) (Q2.hfix123_81_2 i) _)
      colCert_123_81_0.hD ?_).symm
  rw [alnId_123 j hj]


theorem leaf_123_81_1 (hp : 1 < (Q2.transData.getD 81 []).length)
    (j : Nat) (hj : j < (repChars.getD 123 []).length)
    (hq : (normIsRep.getD 123 []).getD j false = true) :
    species (Q2.reps (⟨81, by decide⟩ : Fin 148)) (colE2 ⟨81, by decide⟩ 1 hp)
        (rowE2 (⟨123, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨81, by decide⟩ : Fin 148))
        (colE1 ⟨81, by decide⟩ 1 (transLenTr ⟨81, by decide⟩ 1 hp))
        (rowE1 (⟨123, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨123, by decide⟩ : Fin 148) ⟨81, by decide⟩ _
      (validAt ⟨123, by decide⟩ (listedAt ⟨123, by decide⟩ hj))
      (colE1 ⟨81, by decide⟩ 1 (transLenTr ⟨81, by decide⟩ 1 hp)) T123_81
      hfix123_81 hinj123_81 hcardT123_81
      (fun i => conj_mem_of_fixedPoints _ _ (T123_81 i) (hfix123_81 i) _)
      ⟨123, by decide⟩ ⟨81, by decide⟩ _
      (Q2.validAt ⟨123, by decide⟩ (Q2.listedAt ⟨123, by decide⟩
        (alnCheck_rep ⟨123, by decide⟩ hj hq).1))
      (colE2 ⟨81, by decide⟩ 1 hp) Q2.T123_81_2 Q2.hfix123_81_2 Q2.hinj123_81_2
      Q2.hcardT123_81_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T123_81_2 i) (Q2.hfix123_81_2 i) _)
      colCert_123_81_1.hD ?_).symm
  rw [alnId_123 j hj]


theorem leaf_123_81_2 (hp : 2 < (Q2.transData.getD 81 []).length)
    (j : Nat) (hj : j < (repChars.getD 123 []).length)
    (hq : (normIsRep.getD 123 []).getD j false = true) :
    species (Q2.reps (⟨81, by decide⟩ : Fin 148)) (colE2 ⟨81, by decide⟩ 2 hp)
        (rowE2 (⟨123, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨81, by decide⟩ : Fin 148))
        (colE1 ⟨81, by decide⟩ 2 (transLenTr ⟨81, by decide⟩ 2 hp))
        (rowE1 (⟨123, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨123, by decide⟩ : Fin 148) ⟨81, by decide⟩ _
      (validAt ⟨123, by decide⟩ (listedAt ⟨123, by decide⟩ hj))
      (colE1 ⟨81, by decide⟩ 2 (transLenTr ⟨81, by decide⟩ 2 hp)) T123_81
      hfix123_81 hinj123_81 hcardT123_81
      (fun i => conj_mem_of_fixedPoints _ _ (T123_81 i) (hfix123_81 i) _)
      ⟨123, by decide⟩ ⟨81, by decide⟩ _
      (Q2.validAt ⟨123, by decide⟩ (Q2.listedAt ⟨123, by decide⟩
        (alnCheck_rep ⟨123, by decide⟩ hj hq).1))
      (colE2 ⟨81, by decide⟩ 2 hp) Q2.T123_81_2 Q2.hfix123_81_2 Q2.hinj123_81_2
      Q2.hcardT123_81_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T123_81_2 i) (Q2.hfix123_81_2 i) _)
      colCert_123_81_2.hD ?_).symm
  rw [alnId_123 j hj]


theorem leaf_123_81_3 (hp : 3 < (Q2.transData.getD 81 []).length)
    (j : Nat) (hj : j < (repChars.getD 123 []).length)
    (hq : (normIsRep.getD 123 []).getD j false = true) :
    species (Q2.reps (⟨81, by decide⟩ : Fin 148)) (colE2 ⟨81, by decide⟩ 3 hp)
        (rowE2 (⟨123, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨81, by decide⟩ : Fin 148))
        (colE1 ⟨81, by decide⟩ 3 (transLenTr ⟨81, by decide⟩ 3 hp))
        (rowE1 (⟨123, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨123, by decide⟩ : Fin 148) ⟨81, by decide⟩ _
      (validAt ⟨123, by decide⟩ (listedAt ⟨123, by decide⟩ hj))
      (colE1 ⟨81, by decide⟩ 3 (transLenTr ⟨81, by decide⟩ 3 hp)) T123_81
      hfix123_81 hinj123_81 hcardT123_81
      (fun i => conj_mem_of_fixedPoints _ _ (T123_81 i) (hfix123_81 i) _)
      ⟨123, by decide⟩ ⟨81, by decide⟩ _
      (Q2.validAt ⟨123, by decide⟩ (Q2.listedAt ⟨123, by decide⟩
        (alnCheck_rep ⟨123, by decide⟩ hj hq).1))
      (colE2 ⟨81, by decide⟩ 3 hp) Q2.T123_81_2 Q2.hfix123_81_2 Q2.hinj123_81_2
      Q2.hcardT123_81_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T123_81_2 i) (Q2.hfix123_81_2 i) _)
      colCert_123_81_3.hD ?_).symm
  rw [alnId_123 j hj]


theorem leaf_123_81_4 (hp : 4 < (Q2.transData.getD 81 []).length)
    (j : Nat) (hj : j < (repChars.getD 123 []).length)
    (hq : (normIsRep.getD 123 []).getD j false = true) :
    species (Q2.reps (⟨81, by decide⟩ : Fin 148)) (colE2 ⟨81, by decide⟩ 4 hp)
        (rowE2 (⟨123, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨81, by decide⟩ : Fin 148))
        (colE1 ⟨81, by decide⟩ 4 (transLenTr ⟨81, by decide⟩ 4 hp))
        (rowE1 (⟨123, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨123, by decide⟩ : Fin 148) ⟨81, by decide⟩ _
      (validAt ⟨123, by decide⟩ (listedAt ⟨123, by decide⟩ hj))
      (colE1 ⟨81, by decide⟩ 4 (transLenTr ⟨81, by decide⟩ 4 hp)) T123_81
      hfix123_81 hinj123_81 hcardT123_81
      (fun i => conj_mem_of_fixedPoints _ _ (T123_81 i) (hfix123_81 i) _)
      ⟨123, by decide⟩ ⟨81, by decide⟩ _
      (Q2.validAt ⟨123, by decide⟩ (Q2.listedAt ⟨123, by decide⟩
        (alnCheck_rep ⟨123, by decide⟩ hj hq).1))
      (colE2 ⟨81, by decide⟩ 4 hp) Q2.T123_81_2 Q2.hfix123_81_2 Q2.hinj123_81_2
      Q2.hcardT123_81_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T123_81_2 i) (Q2.hfix123_81_2 i) _)
      colCert_123_81_4.hD ?_).symm
  rw [alnId_123 j hj]


theorem leaf_123_81_5 (hp : 5 < (Q2.transData.getD 81 []).length)
    (j : Nat) (hj : j < (repChars.getD 123 []).length)
    (hq : (normIsRep.getD 123 []).getD j false = true) :
    species (Q2.reps (⟨81, by decide⟩ : Fin 148)) (colE2 ⟨81, by decide⟩ 5 hp)
        (rowE2 (⟨123, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨81, by decide⟩ : Fin 148))
        (colE1 ⟨81, by decide⟩ 5 (transLenTr ⟨81, by decide⟩ 5 hp))
        (rowE1 (⟨123, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨123, by decide⟩ : Fin 148) ⟨81, by decide⟩ _
      (validAt ⟨123, by decide⟩ (listedAt ⟨123, by decide⟩ hj))
      (colE1 ⟨81, by decide⟩ 5 (transLenTr ⟨81, by decide⟩ 5 hp)) T123_81
      hfix123_81 hinj123_81 hcardT123_81
      (fun i => conj_mem_of_fixedPoints _ _ (T123_81 i) (hfix123_81 i) _)
      ⟨123, by decide⟩ ⟨81, by decide⟩ _
      (Q2.validAt ⟨123, by decide⟩ (Q2.listedAt ⟨123, by decide⟩
        (alnCheck_rep ⟨123, by decide⟩ hj hq).1))
      (colE2 ⟨81, by decide⟩ 5 hp) Q2.T123_81_2 Q2.hfix123_81_2 Q2.hinj123_81_2
      Q2.hcardT123_81_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T123_81_2 i) (Q2.hfix123_81_2 i) _)
      ?_).symm
  rw [show colData1 (⟨123, by decide⟩ : Fin 148)
        ((colE1 ⟨81, by decide⟩ 5 (transLenTr ⟨81, by decide⟩ 5 hp) : ↥(reps ⟨81, by decide⟩)) : Coordinate 1)
        T123_81 = colFn colCertDiv_123_81_5.D1 (m := 5) from colCertDiv_123_81_5.bind1,
    show colData2 (⟨123, by decide⟩ : Fin 148)
        ((colE2 ⟨81, by decide⟩ 5 hp : ↥(Q2.reps ⟨81, by decide⟩)) : Coordinate 2)
        Q2.T123_81_2 = colFn colCertDiv_123_81_5.D2 (m := 5) from colCertDiv_123_81_5.bind2]
  rw [alnId_123 j hj]
  exact fastcode_of_div ⟨123, by decide⟩ _ _ _
    ((alnId_123 j hj) ▸ Q2.listedAt (⟨123, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨123, by decide⟩ : Fin 148) hj hq).1) colCertDiv_123_81_5_match


theorem leaf_123_81_10 (hp : 10 < (Q2.transData.getD 81 []).length)
    (j : Nat) (hj : j < (repChars.getD 123 []).length)
    (hq : (normIsRep.getD 123 []).getD j false = true) :
    species (Q2.reps (⟨81, by decide⟩ : Fin 148)) (colE2 ⟨81, by decide⟩ 10 hp)
        (rowE2 (⟨123, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨81, by decide⟩ : Fin 148))
        (colE1 ⟨81, by decide⟩ 10 (transLenTr ⟨81, by decide⟩ 10 hp))
        (rowE1 (⟨123, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨123, by decide⟩ : Fin 148) ⟨81, by decide⟩ _
      (validAt ⟨123, by decide⟩ (listedAt ⟨123, by decide⟩ hj))
      (colE1 ⟨81, by decide⟩ 10 (transLenTr ⟨81, by decide⟩ 10 hp)) T123_81
      hfix123_81 hinj123_81 hcardT123_81
      (fun i => conj_mem_of_fixedPoints _ _ (T123_81 i) (hfix123_81 i) _)
      ⟨123, by decide⟩ ⟨81, by decide⟩ _
      (Q2.validAt ⟨123, by decide⟩ (Q2.listedAt ⟨123, by decide⟩
        (alnCheck_rep ⟨123, by decide⟩ hj hq).1))
      (colE2 ⟨81, by decide⟩ 10 hp) Q2.T123_81_2 Q2.hfix123_81_2 Q2.hinj123_81_2
      Q2.hcardT123_81_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T123_81_2 i) (Q2.hfix123_81_2 i) _)
      ?_).symm
  rw [show colData1 (⟨123, by decide⟩ : Fin 148)
        ((colE1 ⟨81, by decide⟩ 10 (transLenTr ⟨81, by decide⟩ 10 hp) : ↥(reps ⟨81, by decide⟩)) : Coordinate 1)
        T123_81 = colFn colCertDiv_123_81_10.D1 (m := 5) from colCertDiv_123_81_10.bind1,
    show colData2 (⟨123, by decide⟩ : Fin 148)
        ((colE2 ⟨81, by decide⟩ 10 hp : ↥(Q2.reps ⟨81, by decide⟩)) : Coordinate 2)
        Q2.T123_81_2 = colFn colCertDiv_123_81_10.D2 (m := 5) from colCertDiv_123_81_10.bind2]
  rw [alnId_123 j hj]
  exact fastcode_of_div ⟨123, by decide⟩ _ _ _
    ((alnId_123 j hj) ▸ Q2.listedAt (⟨123, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨123, by decide⟩ : Fin 148) hj hq).1) colCertDiv_123_81_10_match


theorem leaf_123_81_15 (hp : 15 < (Q2.transData.getD 81 []).length)
    (j : Nat) (hj : j < (repChars.getD 123 []).length)
    (hq : (normIsRep.getD 123 []).getD j false = true) :
    species (Q2.reps (⟨81, by decide⟩ : Fin 148)) (colE2 ⟨81, by decide⟩ 15 hp)
        (rowE2 (⟨123, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨81, by decide⟩ : Fin 148))
        (colE1 ⟨81, by decide⟩ 15 (transLenTr ⟨81, by decide⟩ 15 hp))
        (rowE1 (⟨123, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨123, by decide⟩ : Fin 148) ⟨81, by decide⟩ _
      (validAt ⟨123, by decide⟩ (listedAt ⟨123, by decide⟩ hj))
      (colE1 ⟨81, by decide⟩ 15 (transLenTr ⟨81, by decide⟩ 15 hp)) T123_81
      hfix123_81 hinj123_81 hcardT123_81
      (fun i => conj_mem_of_fixedPoints _ _ (T123_81 i) (hfix123_81 i) _)
      ⟨123, by decide⟩ ⟨81, by decide⟩ _
      (Q2.validAt ⟨123, by decide⟩ (Q2.listedAt ⟨123, by decide⟩
        (alnCheck_rep ⟨123, by decide⟩ hj hq).1))
      (colE2 ⟨81, by decide⟩ 15 hp) Q2.T123_81_2 Q2.hfix123_81_2 Q2.hinj123_81_2
      Q2.hcardT123_81_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T123_81_2 i) (Q2.hfix123_81_2 i) _)
      ?_).symm
  rw [show colData1 (⟨123, by decide⟩ : Fin 148)
        ((colE1 ⟨81, by decide⟩ 15 (transLenTr ⟨81, by decide⟩ 15 hp) : ↥(reps ⟨81, by decide⟩)) : Coordinate 1)
        T123_81 = colFn colCertDiv_123_81_15.D1 (m := 5) from colCertDiv_123_81_15.bind1,
    show colData2 (⟨123, by decide⟩ : Fin 148)
        ((colE2 ⟨81, by decide⟩ 15 hp : ↥(Q2.reps ⟨81, by decide⟩)) : Coordinate 2)
        Q2.T123_81_2 = colFn colCertDiv_123_81_15.D2 (m := 5) from colCertDiv_123_81_15.bind2]
  rw [alnId_123 j hj]
  exact fastcode_of_div ⟨123, by decide⟩ _ _ _
    ((alnId_123 j hj) ▸ Q2.listedAt (⟨123, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨123, by decide⟩ : Fin 148) hj hq).1) colCertDiv_123_81_15_match


theorem leaf_123_81_20 (hp : 20 < (Q2.transData.getD 81 []).length)
    (j : Nat) (hj : j < (repChars.getD 123 []).length)
    (hq : (normIsRep.getD 123 []).getD j false = true) :
    species (Q2.reps (⟨81, by decide⟩ : Fin 148)) (colE2 ⟨81, by decide⟩ 20 hp)
        (rowE2 (⟨123, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨81, by decide⟩ : Fin 148))
        (colE1 ⟨81, by decide⟩ 20 (transLenTr ⟨81, by decide⟩ 20 hp))
        (rowE1 (⟨123, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨123, by decide⟩ : Fin 148) ⟨81, by decide⟩ _
      (validAt ⟨123, by decide⟩ (listedAt ⟨123, by decide⟩ hj))
      (colE1 ⟨81, by decide⟩ 20 (transLenTr ⟨81, by decide⟩ 20 hp)) T123_81
      hfix123_81 hinj123_81 hcardT123_81
      (fun i => conj_mem_of_fixedPoints _ _ (T123_81 i) (hfix123_81 i) _)
      ⟨123, by decide⟩ ⟨81, by decide⟩ _
      (Q2.validAt ⟨123, by decide⟩ (Q2.listedAt ⟨123, by decide⟩
        (alnCheck_rep ⟨123, by decide⟩ hj hq).1))
      (colE2 ⟨81, by decide⟩ 20 hp) Q2.T123_81_2 Q2.hfix123_81_2 Q2.hinj123_81_2
      Q2.hcardT123_81_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T123_81_2 i) (Q2.hfix123_81_2 i) _)
      ?_).symm
  rw [show colData1 (⟨123, by decide⟩ : Fin 148)
        ((colE1 ⟨81, by decide⟩ 20 (transLenTr ⟨81, by decide⟩ 20 hp) : ↥(reps ⟨81, by decide⟩)) : Coordinate 1)
        T123_81 = colFn colCertDiv_123_81_20.D1 (m := 5) from colCertDiv_123_81_20.bind1,
    show colData2 (⟨123, by decide⟩ : Fin 148)
        ((colE2 ⟨81, by decide⟩ 20 hp : ↥(Q2.reps ⟨81, by decide⟩)) : Coordinate 2)
        Q2.T123_81_2 = colFn colCertDiv_123_81_20.D2 (m := 5) from colCertDiv_123_81_20.bind2]
  rw [alnId_123 j hj]
  exact fastcode_of_div ⟨123, by decide⟩ _ _ _
    ((alnId_123 j hj) ▸ Q2.listedAt (⟨123, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨123, by decide⟩ : Fin 148) hj hq).1) colCertDiv_123_81_20_match


theorem leaf_123_91_0 (hp : 0 < (Q2.transData.getD 91 []).length)
    (j : Nat) (hj : j < (repChars.getD 123 []).length)
    (hq : (normIsRep.getD 123 []).getD j false = true) :
    species (Q2.reps (⟨91, by decide⟩ : Fin 148)) (colE2 ⟨91, by decide⟩ 0 hp)
        (rowE2 (⟨123, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨91, by decide⟩ : Fin 148))
        (colE1 ⟨91, by decide⟩ 0 (transLenTr ⟨91, by decide⟩ 0 hp))
        (rowE1 (⟨123, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨123, by decide⟩ : Fin 148) ⟨91, by decide⟩ _
      (validAt ⟨123, by decide⟩ (listedAt ⟨123, by decide⟩ hj))
      (colE1 ⟨91, by decide⟩ 0 (transLenTr ⟨91, by decide⟩ 0 hp)) T123_91
      hfix123_91 hinj123_91 hcardT123_91
      (fun i => conj_mem_of_fixedPoints _ _ (T123_91 i) (hfix123_91 i) _)
      ⟨123, by decide⟩ ⟨91, by decide⟩ _
      (Q2.validAt ⟨123, by decide⟩ (Q2.listedAt ⟨123, by decide⟩
        (alnCheck_rep ⟨123, by decide⟩ hj hq).1))
      (colE2 ⟨91, by decide⟩ 0 hp) Q2.T123_91_2 Q2.hfix123_91_2 Q2.hinj123_91_2
      Q2.hcardT123_91_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T123_91_2 i) (Q2.hfix123_91_2 i) _)
      colCert_123_91_0.hD ?_).symm
  rw [alnId_123 j hj]


theorem leaf_123_91_1 (hp : 1 < (Q2.transData.getD 91 []).length)
    (j : Nat) (hj : j < (repChars.getD 123 []).length)
    (hq : (normIsRep.getD 123 []).getD j false = true) :
    species (Q2.reps (⟨91, by decide⟩ : Fin 148)) (colE2 ⟨91, by decide⟩ 1 hp)
        (rowE2 (⟨123, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨91, by decide⟩ : Fin 148))
        (colE1 ⟨91, by decide⟩ 1 (transLenTr ⟨91, by decide⟩ 1 hp))
        (rowE1 (⟨123, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨123, by decide⟩ : Fin 148) ⟨91, by decide⟩ _
      (validAt ⟨123, by decide⟩ (listedAt ⟨123, by decide⟩ hj))
      (colE1 ⟨91, by decide⟩ 1 (transLenTr ⟨91, by decide⟩ 1 hp)) T123_91
      hfix123_91 hinj123_91 hcardT123_91
      (fun i => conj_mem_of_fixedPoints _ _ (T123_91 i) (hfix123_91 i) _)
      ⟨123, by decide⟩ ⟨91, by decide⟩ _
      (Q2.validAt ⟨123, by decide⟩ (Q2.listedAt ⟨123, by decide⟩
        (alnCheck_rep ⟨123, by decide⟩ hj hq).1))
      (colE2 ⟨91, by decide⟩ 1 hp) Q2.T123_91_2 Q2.hfix123_91_2 Q2.hinj123_91_2
      Q2.hcardT123_91_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T123_91_2 i) (Q2.hfix123_91_2 i) _)
      colCert_123_91_1.hD ?_).symm
  rw [alnId_123 j hj]


theorem leaf_123_91_2 (hp : 2 < (Q2.transData.getD 91 []).length)
    (j : Nat) (hj : j < (repChars.getD 123 []).length)
    (hq : (normIsRep.getD 123 []).getD j false = true) :
    species (Q2.reps (⟨91, by decide⟩ : Fin 148)) (colE2 ⟨91, by decide⟩ 2 hp)
        (rowE2 (⟨123, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨91, by decide⟩ : Fin 148))
        (colE1 ⟨91, by decide⟩ 2 (transLenTr ⟨91, by decide⟩ 2 hp))
        (rowE1 (⟨123, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨123, by decide⟩ : Fin 148) ⟨91, by decide⟩ _
      (validAt ⟨123, by decide⟩ (listedAt ⟨123, by decide⟩ hj))
      (colE1 ⟨91, by decide⟩ 2 (transLenTr ⟨91, by decide⟩ 2 hp)) T123_91
      hfix123_91 hinj123_91 hcardT123_91
      (fun i => conj_mem_of_fixedPoints _ _ (T123_91 i) (hfix123_91 i) _)
      ⟨123, by decide⟩ ⟨91, by decide⟩ _
      (Q2.validAt ⟨123, by decide⟩ (Q2.listedAt ⟨123, by decide⟩
        (alnCheck_rep ⟨123, by decide⟩ hj hq).1))
      (colE2 ⟨91, by decide⟩ 2 hp) Q2.T123_91_2 Q2.hfix123_91_2 Q2.hinj123_91_2
      Q2.hcardT123_91_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T123_91_2 i) (Q2.hfix123_91_2 i) _)
      colCert_123_91_2.hD ?_).symm
  rw [alnId_123 j hj]


theorem leaf_123_91_3 (hp : 3 < (Q2.transData.getD 91 []).length)
    (j : Nat) (hj : j < (repChars.getD 123 []).length)
    (hq : (normIsRep.getD 123 []).getD j false = true) :
    species (Q2.reps (⟨91, by decide⟩ : Fin 148)) (colE2 ⟨91, by decide⟩ 3 hp)
        (rowE2 (⟨123, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨91, by decide⟩ : Fin 148))
        (colE1 ⟨91, by decide⟩ 3 (transLenTr ⟨91, by decide⟩ 3 hp))
        (rowE1 (⟨123, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨123, by decide⟩ : Fin 148) ⟨91, by decide⟩ _
      (validAt ⟨123, by decide⟩ (listedAt ⟨123, by decide⟩ hj))
      (colE1 ⟨91, by decide⟩ 3 (transLenTr ⟨91, by decide⟩ 3 hp)) T123_91
      hfix123_91 hinj123_91 hcardT123_91
      (fun i => conj_mem_of_fixedPoints _ _ (T123_91 i) (hfix123_91 i) _)
      ⟨123, by decide⟩ ⟨91, by decide⟩ _
      (Q2.validAt ⟨123, by decide⟩ (Q2.listedAt ⟨123, by decide⟩
        (alnCheck_rep ⟨123, by decide⟩ hj hq).1))
      (colE2 ⟨91, by decide⟩ 3 hp) Q2.T123_91_2 Q2.hfix123_91_2 Q2.hinj123_91_2
      Q2.hcardT123_91_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T123_91_2 i) (Q2.hfix123_91_2 i) _)
      colCert_123_91_3.hD ?_).symm
  rw [alnId_123 j hj]


theorem leaf_123_91_4 (hp : 4 < (Q2.transData.getD 91 []).length)
    (j : Nat) (hj : j < (repChars.getD 123 []).length)
    (hq : (normIsRep.getD 123 []).getD j false = true) :
    species (Q2.reps (⟨91, by decide⟩ : Fin 148)) (colE2 ⟨91, by decide⟩ 4 hp)
        (rowE2 (⟨123, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨91, by decide⟩ : Fin 148))
        (colE1 ⟨91, by decide⟩ 4 (transLenTr ⟨91, by decide⟩ 4 hp))
        (rowE1 (⟨123, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨123, by decide⟩ : Fin 148) ⟨91, by decide⟩ _
      (validAt ⟨123, by decide⟩ (listedAt ⟨123, by decide⟩ hj))
      (colE1 ⟨91, by decide⟩ 4 (transLenTr ⟨91, by decide⟩ 4 hp)) T123_91
      hfix123_91 hinj123_91 hcardT123_91
      (fun i => conj_mem_of_fixedPoints _ _ (T123_91 i) (hfix123_91 i) _)
      ⟨123, by decide⟩ ⟨91, by decide⟩ _
      (Q2.validAt ⟨123, by decide⟩ (Q2.listedAt ⟨123, by decide⟩
        (alnCheck_rep ⟨123, by decide⟩ hj hq).1))
      (colE2 ⟨91, by decide⟩ 4 hp) Q2.T123_91_2 Q2.hfix123_91_2 Q2.hinj123_91_2
      Q2.hcardT123_91_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T123_91_2 i) (Q2.hfix123_91_2 i) _)
      colCert_123_91_4.hD ?_).symm
  rw [alnId_123 j hj]


theorem leaf_123_91_5 (hp : 5 < (Q2.transData.getD 91 []).length)
    (j : Nat) (hj : j < (repChars.getD 123 []).length)
    (hq : (normIsRep.getD 123 []).getD j false = true) :
    species (Q2.reps (⟨91, by decide⟩ : Fin 148)) (colE2 ⟨91, by decide⟩ 5 hp)
        (rowE2 (⟨123, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨91, by decide⟩ : Fin 148))
        (colE1 ⟨91, by decide⟩ 5 (transLenTr ⟨91, by decide⟩ 5 hp))
        (rowE1 (⟨123, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨123, by decide⟩ : Fin 148) ⟨91, by decide⟩ _
      (validAt ⟨123, by decide⟩ (listedAt ⟨123, by decide⟩ hj))
      (colE1 ⟨91, by decide⟩ 5 (transLenTr ⟨91, by decide⟩ 5 hp)) T123_91
      hfix123_91 hinj123_91 hcardT123_91
      (fun i => conj_mem_of_fixedPoints _ _ (T123_91 i) (hfix123_91 i) _)
      ⟨123, by decide⟩ ⟨91, by decide⟩ _
      (Q2.validAt ⟨123, by decide⟩ (Q2.listedAt ⟨123, by decide⟩
        (alnCheck_rep ⟨123, by decide⟩ hj hq).1))
      (colE2 ⟨91, by decide⟩ 5 hp) Q2.T123_91_2 Q2.hfix123_91_2 Q2.hinj123_91_2
      Q2.hcardT123_91_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T123_91_2 i) (Q2.hfix123_91_2 i) _)
      ?_).symm
  rw [show colData1 (⟨123, by decide⟩ : Fin 148)
        ((colE1 ⟨91, by decide⟩ 5 (transLenTr ⟨91, by decide⟩ 5 hp) : ↥(reps ⟨91, by decide⟩)) : Coordinate 1)
        T123_91 = colFn colCertDiv_123_91_5.D1 (m := 5) from colCertDiv_123_91_5.bind1,
    show colData2 (⟨123, by decide⟩ : Fin 148)
        ((colE2 ⟨91, by decide⟩ 5 hp : ↥(Q2.reps ⟨91, by decide⟩)) : Coordinate 2)
        Q2.T123_91_2 = colFn colCertDiv_123_91_5.D2 (m := 5) from colCertDiv_123_91_5.bind2]
  rw [alnId_123 j hj]
  exact fastcode_of_div ⟨123, by decide⟩ _ _ _
    ((alnId_123 j hj) ▸ Q2.listedAt (⟨123, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨123, by decide⟩ : Fin 148) hj hq).1) colCertDiv_123_91_5_match


theorem leaf_123_91_10 (hp : 10 < (Q2.transData.getD 91 []).length)
    (j : Nat) (hj : j < (repChars.getD 123 []).length)
    (hq : (normIsRep.getD 123 []).getD j false = true) :
    species (Q2.reps (⟨91, by decide⟩ : Fin 148)) (colE2 ⟨91, by decide⟩ 10 hp)
        (rowE2 (⟨123, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨91, by decide⟩ : Fin 148))
        (colE1 ⟨91, by decide⟩ 10 (transLenTr ⟨91, by decide⟩ 10 hp))
        (rowE1 (⟨123, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨123, by decide⟩ : Fin 148) ⟨91, by decide⟩ _
      (validAt ⟨123, by decide⟩ (listedAt ⟨123, by decide⟩ hj))
      (colE1 ⟨91, by decide⟩ 10 (transLenTr ⟨91, by decide⟩ 10 hp)) T123_91
      hfix123_91 hinj123_91 hcardT123_91
      (fun i => conj_mem_of_fixedPoints _ _ (T123_91 i) (hfix123_91 i) _)
      ⟨123, by decide⟩ ⟨91, by decide⟩ _
      (Q2.validAt ⟨123, by decide⟩ (Q2.listedAt ⟨123, by decide⟩
        (alnCheck_rep ⟨123, by decide⟩ hj hq).1))
      (colE2 ⟨91, by decide⟩ 10 hp) Q2.T123_91_2 Q2.hfix123_91_2 Q2.hinj123_91_2
      Q2.hcardT123_91_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T123_91_2 i) (Q2.hfix123_91_2 i) _)
      ?_).symm
  rw [show colData1 (⟨123, by decide⟩ : Fin 148)
        ((colE1 ⟨91, by decide⟩ 10 (transLenTr ⟨91, by decide⟩ 10 hp) : ↥(reps ⟨91, by decide⟩)) : Coordinate 1)
        T123_91 = colFn colCertDiv_123_91_10.D1 (m := 5) from colCertDiv_123_91_10.bind1,
    show colData2 (⟨123, by decide⟩ : Fin 148)
        ((colE2 ⟨91, by decide⟩ 10 hp : ↥(Q2.reps ⟨91, by decide⟩)) : Coordinate 2)
        Q2.T123_91_2 = colFn colCertDiv_123_91_10.D2 (m := 5) from colCertDiv_123_91_10.bind2]
  rw [alnId_123 j hj]
  exact fastcode_of_div ⟨123, by decide⟩ _ _ _
    ((alnId_123 j hj) ▸ Q2.listedAt (⟨123, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨123, by decide⟩ : Fin 148) hj hq).1) colCertDiv_123_91_10_match


theorem leaf_123_91_15 (hp : 15 < (Q2.transData.getD 91 []).length)
    (j : Nat) (hj : j < (repChars.getD 123 []).length)
    (hq : (normIsRep.getD 123 []).getD j false = true) :
    species (Q2.reps (⟨91, by decide⟩ : Fin 148)) (colE2 ⟨91, by decide⟩ 15 hp)
        (rowE2 (⟨123, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨91, by decide⟩ : Fin 148))
        (colE1 ⟨91, by decide⟩ 15 (transLenTr ⟨91, by decide⟩ 15 hp))
        (rowE1 (⟨123, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨123, by decide⟩ : Fin 148) ⟨91, by decide⟩ _
      (validAt ⟨123, by decide⟩ (listedAt ⟨123, by decide⟩ hj))
      (colE1 ⟨91, by decide⟩ 15 (transLenTr ⟨91, by decide⟩ 15 hp)) T123_91
      hfix123_91 hinj123_91 hcardT123_91
      (fun i => conj_mem_of_fixedPoints _ _ (T123_91 i) (hfix123_91 i) _)
      ⟨123, by decide⟩ ⟨91, by decide⟩ _
      (Q2.validAt ⟨123, by decide⟩ (Q2.listedAt ⟨123, by decide⟩
        (alnCheck_rep ⟨123, by decide⟩ hj hq).1))
      (colE2 ⟨91, by decide⟩ 15 hp) Q2.T123_91_2 Q2.hfix123_91_2 Q2.hinj123_91_2
      Q2.hcardT123_91_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T123_91_2 i) (Q2.hfix123_91_2 i) _)
      ?_).symm
  rw [show colData1 (⟨123, by decide⟩ : Fin 148)
        ((colE1 ⟨91, by decide⟩ 15 (transLenTr ⟨91, by decide⟩ 15 hp) : ↥(reps ⟨91, by decide⟩)) : Coordinate 1)
        T123_91 = colFn colCertDiv_123_91_15.D1 (m := 5) from colCertDiv_123_91_15.bind1,
    show colData2 (⟨123, by decide⟩ : Fin 148)
        ((colE2 ⟨91, by decide⟩ 15 hp : ↥(Q2.reps ⟨91, by decide⟩)) : Coordinate 2)
        Q2.T123_91_2 = colFn colCertDiv_123_91_15.D2 (m := 5) from colCertDiv_123_91_15.bind2]
  rw [alnId_123 j hj]
  exact fastcode_of_div ⟨123, by decide⟩ _ _ _
    ((alnId_123 j hj) ▸ Q2.listedAt (⟨123, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨123, by decide⟩ : Fin 148) hj hq).1) colCertDiv_123_91_15_match


theorem leaf_123_91_20 (hp : 20 < (Q2.transData.getD 91 []).length)
    (j : Nat) (hj : j < (repChars.getD 123 []).length)
    (hq : (normIsRep.getD 123 []).getD j false = true) :
    species (Q2.reps (⟨91, by decide⟩ : Fin 148)) (colE2 ⟨91, by decide⟩ 20 hp)
        (rowE2 (⟨123, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨91, by decide⟩ : Fin 148))
        (colE1 ⟨91, by decide⟩ 20 (transLenTr ⟨91, by decide⟩ 20 hp))
        (rowE1 (⟨123, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨123, by decide⟩ : Fin 148) ⟨91, by decide⟩ _
      (validAt ⟨123, by decide⟩ (listedAt ⟨123, by decide⟩ hj))
      (colE1 ⟨91, by decide⟩ 20 (transLenTr ⟨91, by decide⟩ 20 hp)) T123_91
      hfix123_91 hinj123_91 hcardT123_91
      (fun i => conj_mem_of_fixedPoints _ _ (T123_91 i) (hfix123_91 i) _)
      ⟨123, by decide⟩ ⟨91, by decide⟩ _
      (Q2.validAt ⟨123, by decide⟩ (Q2.listedAt ⟨123, by decide⟩
        (alnCheck_rep ⟨123, by decide⟩ hj hq).1))
      (colE2 ⟨91, by decide⟩ 20 hp) Q2.T123_91_2 Q2.hfix123_91_2 Q2.hinj123_91_2
      Q2.hcardT123_91_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T123_91_2 i) (Q2.hfix123_91_2 i) _)
      colCert_123_91_20.hD ?_).symm
  rw [alnId_123 j hj]


theorem leaf_123_99_0 (hp : 0 < (Q2.transData.getD 99 []).length)
    (j : Nat) (hj : j < (repChars.getD 123 []).length)
    (hq : (normIsRep.getD 123 []).getD j false = true) :
    species (Q2.reps (⟨99, by decide⟩ : Fin 148)) (colE2 ⟨99, by decide⟩ 0 hp)
        (rowE2 (⟨123, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨99, by decide⟩ : Fin 148))
        (colE1 ⟨99, by decide⟩ 0 (transLenTr ⟨99, by decide⟩ 0 hp))
        (rowE1 (⟨123, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨123, by decide⟩ : Fin 148) ⟨99, by decide⟩ _
      (validAt ⟨123, by decide⟩ (listedAt ⟨123, by decide⟩ hj))
      (colE1 ⟨99, by decide⟩ 0 (transLenTr ⟨99, by decide⟩ 0 hp)) T123_99
      hfix123_99 hinj123_99 hcardT123_99
      (fun i => conj_mem_of_fixedPoints _ _ (T123_99 i) (hfix123_99 i) _)
      ⟨123, by decide⟩ ⟨99, by decide⟩ _
      (Q2.validAt ⟨123, by decide⟩ (Q2.listedAt ⟨123, by decide⟩
        (alnCheck_rep ⟨123, by decide⟩ hj hq).1))
      (colE2 ⟨99, by decide⟩ 0 hp) Q2.T123_99_2 Q2.hfix123_99_2 Q2.hinj123_99_2
      Q2.hcardT123_99_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T123_99_2 i) (Q2.hfix123_99_2 i) _)
      colCert_123_99_0.hD ?_).symm
  rw [alnId_123 j hj]


theorem leaf_123_99_1 (hp : 1 < (Q2.transData.getD 99 []).length)
    (j : Nat) (hj : j < (repChars.getD 123 []).length)
    (hq : (normIsRep.getD 123 []).getD j false = true) :
    species (Q2.reps (⟨99, by decide⟩ : Fin 148)) (colE2 ⟨99, by decide⟩ 1 hp)
        (rowE2 (⟨123, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨99, by decide⟩ : Fin 148))
        (colE1 ⟨99, by decide⟩ 1 (transLenTr ⟨99, by decide⟩ 1 hp))
        (rowE1 (⟨123, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨123, by decide⟩ : Fin 148) ⟨99, by decide⟩ _
      (validAt ⟨123, by decide⟩ (listedAt ⟨123, by decide⟩ hj))
      (colE1 ⟨99, by decide⟩ 1 (transLenTr ⟨99, by decide⟩ 1 hp)) T123_99
      hfix123_99 hinj123_99 hcardT123_99
      (fun i => conj_mem_of_fixedPoints _ _ (T123_99 i) (hfix123_99 i) _)
      ⟨123, by decide⟩ ⟨99, by decide⟩ _
      (Q2.validAt ⟨123, by decide⟩ (Q2.listedAt ⟨123, by decide⟩
        (alnCheck_rep ⟨123, by decide⟩ hj hq).1))
      (colE2 ⟨99, by decide⟩ 1 hp) Q2.T123_99_2 Q2.hfix123_99_2 Q2.hinj123_99_2
      Q2.hcardT123_99_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T123_99_2 i) (Q2.hfix123_99_2 i) _)
      colCert_123_99_1.hD ?_).symm
  rw [alnId_123 j hj]


theorem leaf_123_99_2 (hp : 2 < (Q2.transData.getD 99 []).length)
    (j : Nat) (hj : j < (repChars.getD 123 []).length)
    (hq : (normIsRep.getD 123 []).getD j false = true) :
    species (Q2.reps (⟨99, by decide⟩ : Fin 148)) (colE2 ⟨99, by decide⟩ 2 hp)
        (rowE2 (⟨123, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨99, by decide⟩ : Fin 148))
        (colE1 ⟨99, by decide⟩ 2 (transLenTr ⟨99, by decide⟩ 2 hp))
        (rowE1 (⟨123, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨123, by decide⟩ : Fin 148) ⟨99, by decide⟩ _
      (validAt ⟨123, by decide⟩ (listedAt ⟨123, by decide⟩ hj))
      (colE1 ⟨99, by decide⟩ 2 (transLenTr ⟨99, by decide⟩ 2 hp)) T123_99
      hfix123_99 hinj123_99 hcardT123_99
      (fun i => conj_mem_of_fixedPoints _ _ (T123_99 i) (hfix123_99 i) _)
      ⟨123, by decide⟩ ⟨99, by decide⟩ _
      (Q2.validAt ⟨123, by decide⟩ (Q2.listedAt ⟨123, by decide⟩
        (alnCheck_rep ⟨123, by decide⟩ hj hq).1))
      (colE2 ⟨99, by decide⟩ 2 hp) Q2.T123_99_2 Q2.hfix123_99_2 Q2.hinj123_99_2
      Q2.hcardT123_99_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T123_99_2 i) (Q2.hfix123_99_2 i) _)
      colCert_123_99_2.hD ?_).symm
  rw [alnId_123 j hj]


theorem leaf_123_99_3 (hp : 3 < (Q2.transData.getD 99 []).length)
    (j : Nat) (hj : j < (repChars.getD 123 []).length)
    (hq : (normIsRep.getD 123 []).getD j false = true) :
    species (Q2.reps (⟨99, by decide⟩ : Fin 148)) (colE2 ⟨99, by decide⟩ 3 hp)
        (rowE2 (⟨123, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨99, by decide⟩ : Fin 148))
        (colE1 ⟨99, by decide⟩ 3 (transLenTr ⟨99, by decide⟩ 3 hp))
        (rowE1 (⟨123, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨123, by decide⟩ : Fin 148) ⟨99, by decide⟩ _
      (validAt ⟨123, by decide⟩ (listedAt ⟨123, by decide⟩ hj))
      (colE1 ⟨99, by decide⟩ 3 (transLenTr ⟨99, by decide⟩ 3 hp)) T123_99
      hfix123_99 hinj123_99 hcardT123_99
      (fun i => conj_mem_of_fixedPoints _ _ (T123_99 i) (hfix123_99 i) _)
      ⟨123, by decide⟩ ⟨99, by decide⟩ _
      (Q2.validAt ⟨123, by decide⟩ (Q2.listedAt ⟨123, by decide⟩
        (alnCheck_rep ⟨123, by decide⟩ hj hq).1))
      (colE2 ⟨99, by decide⟩ 3 hp) Q2.T123_99_2 Q2.hfix123_99_2 Q2.hinj123_99_2
      Q2.hcardT123_99_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T123_99_2 i) (Q2.hfix123_99_2 i) _)
      colCert_123_99_3.hD ?_).symm
  rw [alnId_123 j hj]


theorem leaf_123_99_4 (hp : 4 < (Q2.transData.getD 99 []).length)
    (j : Nat) (hj : j < (repChars.getD 123 []).length)
    (hq : (normIsRep.getD 123 []).getD j false = true) :
    species (Q2.reps (⟨99, by decide⟩ : Fin 148)) (colE2 ⟨99, by decide⟩ 4 hp)
        (rowE2 (⟨123, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨99, by decide⟩ : Fin 148))
        (colE1 ⟨99, by decide⟩ 4 (transLenTr ⟨99, by decide⟩ 4 hp))
        (rowE1 (⟨123, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨123, by decide⟩ : Fin 148) ⟨99, by decide⟩ _
      (validAt ⟨123, by decide⟩ (listedAt ⟨123, by decide⟩ hj))
      (colE1 ⟨99, by decide⟩ 4 (transLenTr ⟨99, by decide⟩ 4 hp)) T123_99
      hfix123_99 hinj123_99 hcardT123_99
      (fun i => conj_mem_of_fixedPoints _ _ (T123_99 i) (hfix123_99 i) _)
      ⟨123, by decide⟩ ⟨99, by decide⟩ _
      (Q2.validAt ⟨123, by decide⟩ (Q2.listedAt ⟨123, by decide⟩
        (alnCheck_rep ⟨123, by decide⟩ hj hq).1))
      (colE2 ⟨99, by decide⟩ 4 hp) Q2.T123_99_2 Q2.hfix123_99_2 Q2.hinj123_99_2
      Q2.hcardT123_99_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T123_99_2 i) (Q2.hfix123_99_2 i) _)
      colCert_123_99_4.hD ?_).symm
  rw [alnId_123 j hj]


theorem leaf_123_99_5 (hp : 5 < (Q2.transData.getD 99 []).length)
    (j : Nat) (hj : j < (repChars.getD 123 []).length)
    (hq : (normIsRep.getD 123 []).getD j false = true) :
    species (Q2.reps (⟨99, by decide⟩ : Fin 148)) (colE2 ⟨99, by decide⟩ 5 hp)
        (rowE2 (⟨123, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨99, by decide⟩ : Fin 148))
        (colE1 ⟨99, by decide⟩ 5 (transLenTr ⟨99, by decide⟩ 5 hp))
        (rowE1 (⟨123, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨123, by decide⟩ : Fin 148) ⟨99, by decide⟩ _
      (validAt ⟨123, by decide⟩ (listedAt ⟨123, by decide⟩ hj))
      (colE1 ⟨99, by decide⟩ 5 (transLenTr ⟨99, by decide⟩ 5 hp)) T123_99
      hfix123_99 hinj123_99 hcardT123_99
      (fun i => conj_mem_of_fixedPoints _ _ (T123_99 i) (hfix123_99 i) _)
      ⟨123, by decide⟩ ⟨99, by decide⟩ _
      (Q2.validAt ⟨123, by decide⟩ (Q2.listedAt ⟨123, by decide⟩
        (alnCheck_rep ⟨123, by decide⟩ hj hq).1))
      (colE2 ⟨99, by decide⟩ 5 hp) Q2.T123_99_2 Q2.hfix123_99_2 Q2.hinj123_99_2
      Q2.hcardT123_99_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T123_99_2 i) (Q2.hfix123_99_2 i) _)
      ?_).symm
  rw [show colData1 (⟨123, by decide⟩ : Fin 148)
        ((colE1 ⟨99, by decide⟩ 5 (transLenTr ⟨99, by decide⟩ 5 hp) : ↥(reps ⟨99, by decide⟩)) : Coordinate 1)
        T123_99 = colFn colCertDiv_123_99_5.D1 (m := 5) from colCertDiv_123_99_5.bind1,
    show colData2 (⟨123, by decide⟩ : Fin 148)
        ((colE2 ⟨99, by decide⟩ 5 hp : ↥(Q2.reps ⟨99, by decide⟩)) : Coordinate 2)
        Q2.T123_99_2 = colFn colCertDiv_123_99_5.D2 (m := 5) from colCertDiv_123_99_5.bind2]
  rw [alnId_123 j hj]
  exact fastcode_of_div ⟨123, by decide⟩ _ _ _
    ((alnId_123 j hj) ▸ Q2.listedAt (⟨123, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨123, by decide⟩ : Fin 148) hj hq).1) colCertDiv_123_99_5_match


theorem leaf_123_99_10 (hp : 10 < (Q2.transData.getD 99 []).length)
    (j : Nat) (hj : j < (repChars.getD 123 []).length)
    (hq : (normIsRep.getD 123 []).getD j false = true) :
    species (Q2.reps (⟨99, by decide⟩ : Fin 148)) (colE2 ⟨99, by decide⟩ 10 hp)
        (rowE2 (⟨123, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨99, by decide⟩ : Fin 148))
        (colE1 ⟨99, by decide⟩ 10 (transLenTr ⟨99, by decide⟩ 10 hp))
        (rowE1 (⟨123, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨123, by decide⟩ : Fin 148) ⟨99, by decide⟩ _
      (validAt ⟨123, by decide⟩ (listedAt ⟨123, by decide⟩ hj))
      (colE1 ⟨99, by decide⟩ 10 (transLenTr ⟨99, by decide⟩ 10 hp)) T123_99
      hfix123_99 hinj123_99 hcardT123_99
      (fun i => conj_mem_of_fixedPoints _ _ (T123_99 i) (hfix123_99 i) _)
      ⟨123, by decide⟩ ⟨99, by decide⟩ _
      (Q2.validAt ⟨123, by decide⟩ (Q2.listedAt ⟨123, by decide⟩
        (alnCheck_rep ⟨123, by decide⟩ hj hq).1))
      (colE2 ⟨99, by decide⟩ 10 hp) Q2.T123_99_2 Q2.hfix123_99_2 Q2.hinj123_99_2
      Q2.hcardT123_99_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T123_99_2 i) (Q2.hfix123_99_2 i) _)
      ?_).symm
  rw [show colData1 (⟨123, by decide⟩ : Fin 148)
        ((colE1 ⟨99, by decide⟩ 10 (transLenTr ⟨99, by decide⟩ 10 hp) : ↥(reps ⟨99, by decide⟩)) : Coordinate 1)
        T123_99 = colFn colCertDiv_123_99_10.D1 (m := 5) from colCertDiv_123_99_10.bind1,
    show colData2 (⟨123, by decide⟩ : Fin 148)
        ((colE2 ⟨99, by decide⟩ 10 hp : ↥(Q2.reps ⟨99, by decide⟩)) : Coordinate 2)
        Q2.T123_99_2 = colFn colCertDiv_123_99_10.D2 (m := 5) from colCertDiv_123_99_10.bind2]
  rw [alnId_123 j hj]
  exact fastcode_of_div ⟨123, by decide⟩ _ _ _
    ((alnId_123 j hj) ▸ Q2.listedAt (⟨123, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨123, by decide⟩ : Fin 148) hj hq).1) colCertDiv_123_99_10_match


theorem leaf_123_99_15 (hp : 15 < (Q2.transData.getD 99 []).length)
    (j : Nat) (hj : j < (repChars.getD 123 []).length)
    (hq : (normIsRep.getD 123 []).getD j false = true) :
    species (Q2.reps (⟨99, by decide⟩ : Fin 148)) (colE2 ⟨99, by decide⟩ 15 hp)
        (rowE2 (⟨123, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨99, by decide⟩ : Fin 148))
        (colE1 ⟨99, by decide⟩ 15 (transLenTr ⟨99, by decide⟩ 15 hp))
        (rowE1 (⟨123, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨123, by decide⟩ : Fin 148) ⟨99, by decide⟩ _
      (validAt ⟨123, by decide⟩ (listedAt ⟨123, by decide⟩ hj))
      (colE1 ⟨99, by decide⟩ 15 (transLenTr ⟨99, by decide⟩ 15 hp)) T123_99
      hfix123_99 hinj123_99 hcardT123_99
      (fun i => conj_mem_of_fixedPoints _ _ (T123_99 i) (hfix123_99 i) _)
      ⟨123, by decide⟩ ⟨99, by decide⟩ _
      (Q2.validAt ⟨123, by decide⟩ (Q2.listedAt ⟨123, by decide⟩
        (alnCheck_rep ⟨123, by decide⟩ hj hq).1))
      (colE2 ⟨99, by decide⟩ 15 hp) Q2.T123_99_2 Q2.hfix123_99_2 Q2.hinj123_99_2
      Q2.hcardT123_99_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T123_99_2 i) (Q2.hfix123_99_2 i) _)
      ?_).symm
  rw [show colData1 (⟨123, by decide⟩ : Fin 148)
        ((colE1 ⟨99, by decide⟩ 15 (transLenTr ⟨99, by decide⟩ 15 hp) : ↥(reps ⟨99, by decide⟩)) : Coordinate 1)
        T123_99 = colFn colCertDiv_123_99_15.D1 (m := 5) from colCertDiv_123_99_15.bind1,
    show colData2 (⟨123, by decide⟩ : Fin 148)
        ((colE2 ⟨99, by decide⟩ 15 hp : ↥(Q2.reps ⟨99, by decide⟩)) : Coordinate 2)
        Q2.T123_99_2 = colFn colCertDiv_123_99_15.D2 (m := 5) from colCertDiv_123_99_15.bind2]
  rw [alnId_123 j hj]
  exact fastcode_of_div ⟨123, by decide⟩ _ _ _
    ((alnId_123 j hj) ▸ Q2.listedAt (⟨123, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨123, by decide⟩ : Fin 148) hj hq).1) colCertDiv_123_99_15_match


theorem leaf_123_99_20 (hp : 20 < (Q2.transData.getD 99 []).length)
    (j : Nat) (hj : j < (repChars.getD 123 []).length)
    (hq : (normIsRep.getD 123 []).getD j false = true) :
    species (Q2.reps (⟨99, by decide⟩ : Fin 148)) (colE2 ⟨99, by decide⟩ 20 hp)
        (rowE2 (⟨123, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨99, by decide⟩ : Fin 148))
        (colE1 ⟨99, by decide⟩ 20 (transLenTr ⟨99, by decide⟩ 20 hp))
        (rowE1 (⟨123, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨123, by decide⟩ : Fin 148) ⟨99, by decide⟩ _
      (validAt ⟨123, by decide⟩ (listedAt ⟨123, by decide⟩ hj))
      (colE1 ⟨99, by decide⟩ 20 (transLenTr ⟨99, by decide⟩ 20 hp)) T123_99
      hfix123_99 hinj123_99 hcardT123_99
      (fun i => conj_mem_of_fixedPoints _ _ (T123_99 i) (hfix123_99 i) _)
      ⟨123, by decide⟩ ⟨99, by decide⟩ _
      (Q2.validAt ⟨123, by decide⟩ (Q2.listedAt ⟨123, by decide⟩
        (alnCheck_rep ⟨123, by decide⟩ hj hq).1))
      (colE2 ⟨99, by decide⟩ 20 hp) Q2.T123_99_2 Q2.hfix123_99_2 Q2.hinj123_99_2
      Q2.hcardT123_99_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T123_99_2 i) (Q2.hfix123_99_2 i) _)
      ?_).symm
  rw [show colData1 (⟨123, by decide⟩ : Fin 148)
        ((colE1 ⟨99, by decide⟩ 20 (transLenTr ⟨99, by decide⟩ 20 hp) : ↥(reps ⟨99, by decide⟩)) : Coordinate 1)
        T123_99 = colFn colCertDiv_123_99_20.D1 (m := 5) from colCertDiv_123_99_20.bind1,
    show colData2 (⟨123, by decide⟩ : Fin 148)
        ((colE2 ⟨99, by decide⟩ 20 hp : ↥(Q2.reps ⟨99, by decide⟩)) : Coordinate 2)
        Q2.T123_99_2 = colFn colCertDiv_123_99_20.D2 (m := 5) from colCertDiv_123_99_20.bind2]
  rw [alnId_123 j hj]
  exact fastcode_of_div ⟨123, by decide⟩ _ _ _
    ((alnId_123 j hj) ▸ Q2.listedAt (⟨123, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨123, by decide⟩ : Fin 148) hj hq).1) colCertDiv_123_99_20_match


theorem leaf_123_100_0 (hp : 0 < (Q2.transData.getD 100 []).length)
    (j : Nat) (hj : j < (repChars.getD 123 []).length)
    (hq : (normIsRep.getD 123 []).getD j false = true) :
    species (Q2.reps (⟨100, by decide⟩ : Fin 148)) (colE2 ⟨100, by decide⟩ 0 hp)
        (rowE2 (⟨123, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨100, by decide⟩ : Fin 148))
        (colE1 ⟨100, by decide⟩ 0 (transLenTr ⟨100, by decide⟩ 0 hp))
        (rowE1 (⟨123, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨123, by decide⟩ : Fin 148) ⟨100, by decide⟩ _
      (validAt ⟨123, by decide⟩ (listedAt ⟨123, by decide⟩ hj))
      (colE1 ⟨100, by decide⟩ 0 (transLenTr ⟨100, by decide⟩ 0 hp)) T123_100
      hfix123_100 hinj123_100 hcardT123_100
      (fun i => conj_mem_of_fixedPoints _ _ (T123_100 i) (hfix123_100 i) _)
      ⟨123, by decide⟩ ⟨100, by decide⟩ _
      (Q2.validAt ⟨123, by decide⟩ (Q2.listedAt ⟨123, by decide⟩
        (alnCheck_rep ⟨123, by decide⟩ hj hq).1))
      (colE2 ⟨100, by decide⟩ 0 hp) Q2.T123_100_2 Q2.hfix123_100_2 Q2.hinj123_100_2
      Q2.hcardT123_100_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T123_100_2 i) (Q2.hfix123_100_2 i) _)
      colCert_123_100_0.hD ?_).symm
  rw [alnId_123 j hj]


theorem leaf_123_100_1 (hp : 1 < (Q2.transData.getD 100 []).length)
    (j : Nat) (hj : j < (repChars.getD 123 []).length)
    (hq : (normIsRep.getD 123 []).getD j false = true) :
    species (Q2.reps (⟨100, by decide⟩ : Fin 148)) (colE2 ⟨100, by decide⟩ 1 hp)
        (rowE2 (⟨123, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨100, by decide⟩ : Fin 148))
        (colE1 ⟨100, by decide⟩ 1 (transLenTr ⟨100, by decide⟩ 1 hp))
        (rowE1 (⟨123, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨123, by decide⟩ : Fin 148) ⟨100, by decide⟩ _
      (validAt ⟨123, by decide⟩ (listedAt ⟨123, by decide⟩ hj))
      (colE1 ⟨100, by decide⟩ 1 (transLenTr ⟨100, by decide⟩ 1 hp)) T123_100
      hfix123_100 hinj123_100 hcardT123_100
      (fun i => conj_mem_of_fixedPoints _ _ (T123_100 i) (hfix123_100 i) _)
      ⟨123, by decide⟩ ⟨100, by decide⟩ _
      (Q2.validAt ⟨123, by decide⟩ (Q2.listedAt ⟨123, by decide⟩
        (alnCheck_rep ⟨123, by decide⟩ hj hq).1))
      (colE2 ⟨100, by decide⟩ 1 hp) Q2.T123_100_2 Q2.hfix123_100_2 Q2.hinj123_100_2
      Q2.hcardT123_100_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T123_100_2 i) (Q2.hfix123_100_2 i) _)
      colCert_123_100_1.hD ?_).symm
  rw [alnId_123 j hj]


theorem leaf_123_100_2 (hp : 2 < (Q2.transData.getD 100 []).length)
    (j : Nat) (hj : j < (repChars.getD 123 []).length)
    (hq : (normIsRep.getD 123 []).getD j false = true) :
    species (Q2.reps (⟨100, by decide⟩ : Fin 148)) (colE2 ⟨100, by decide⟩ 2 hp)
        (rowE2 (⟨123, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨100, by decide⟩ : Fin 148))
        (colE1 ⟨100, by decide⟩ 2 (transLenTr ⟨100, by decide⟩ 2 hp))
        (rowE1 (⟨123, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨123, by decide⟩ : Fin 148) ⟨100, by decide⟩ _
      (validAt ⟨123, by decide⟩ (listedAt ⟨123, by decide⟩ hj))
      (colE1 ⟨100, by decide⟩ 2 (transLenTr ⟨100, by decide⟩ 2 hp)) T123_100
      hfix123_100 hinj123_100 hcardT123_100
      (fun i => conj_mem_of_fixedPoints _ _ (T123_100 i) (hfix123_100 i) _)
      ⟨123, by decide⟩ ⟨100, by decide⟩ _
      (Q2.validAt ⟨123, by decide⟩ (Q2.listedAt ⟨123, by decide⟩
        (alnCheck_rep ⟨123, by decide⟩ hj hq).1))
      (colE2 ⟨100, by decide⟩ 2 hp) Q2.T123_100_2 Q2.hfix123_100_2 Q2.hinj123_100_2
      Q2.hcardT123_100_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T123_100_2 i) (Q2.hfix123_100_2 i) _)
      colCert_123_100_2.hD ?_).symm
  rw [alnId_123 j hj]


theorem leaf_123_100_3 (hp : 3 < (Q2.transData.getD 100 []).length)
    (j : Nat) (hj : j < (repChars.getD 123 []).length)
    (hq : (normIsRep.getD 123 []).getD j false = true) :
    species (Q2.reps (⟨100, by decide⟩ : Fin 148)) (colE2 ⟨100, by decide⟩ 3 hp)
        (rowE2 (⟨123, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨100, by decide⟩ : Fin 148))
        (colE1 ⟨100, by decide⟩ 3 (transLenTr ⟨100, by decide⟩ 3 hp))
        (rowE1 (⟨123, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨123, by decide⟩ : Fin 148) ⟨100, by decide⟩ _
      (validAt ⟨123, by decide⟩ (listedAt ⟨123, by decide⟩ hj))
      (colE1 ⟨100, by decide⟩ 3 (transLenTr ⟨100, by decide⟩ 3 hp)) T123_100
      hfix123_100 hinj123_100 hcardT123_100
      (fun i => conj_mem_of_fixedPoints _ _ (T123_100 i) (hfix123_100 i) _)
      ⟨123, by decide⟩ ⟨100, by decide⟩ _
      (Q2.validAt ⟨123, by decide⟩ (Q2.listedAt ⟨123, by decide⟩
        (alnCheck_rep ⟨123, by decide⟩ hj hq).1))
      (colE2 ⟨100, by decide⟩ 3 hp) Q2.T123_100_2 Q2.hfix123_100_2 Q2.hinj123_100_2
      Q2.hcardT123_100_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T123_100_2 i) (Q2.hfix123_100_2 i) _)
      colCert_123_100_3.hD ?_).symm
  rw [alnId_123 j hj]


theorem leaf_123_100_4 (hp : 4 < (Q2.transData.getD 100 []).length)
    (j : Nat) (hj : j < (repChars.getD 123 []).length)
    (hq : (normIsRep.getD 123 []).getD j false = true) :
    species (Q2.reps (⟨100, by decide⟩ : Fin 148)) (colE2 ⟨100, by decide⟩ 4 hp)
        (rowE2 (⟨123, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨100, by decide⟩ : Fin 148))
        (colE1 ⟨100, by decide⟩ 4 (transLenTr ⟨100, by decide⟩ 4 hp))
        (rowE1 (⟨123, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨123, by decide⟩ : Fin 148) ⟨100, by decide⟩ _
      (validAt ⟨123, by decide⟩ (listedAt ⟨123, by decide⟩ hj))
      (colE1 ⟨100, by decide⟩ 4 (transLenTr ⟨100, by decide⟩ 4 hp)) T123_100
      hfix123_100 hinj123_100 hcardT123_100
      (fun i => conj_mem_of_fixedPoints _ _ (T123_100 i) (hfix123_100 i) _)
      ⟨123, by decide⟩ ⟨100, by decide⟩ _
      (Q2.validAt ⟨123, by decide⟩ (Q2.listedAt ⟨123, by decide⟩
        (alnCheck_rep ⟨123, by decide⟩ hj hq).1))
      (colE2 ⟨100, by decide⟩ 4 hp) Q2.T123_100_2 Q2.hfix123_100_2 Q2.hinj123_100_2
      Q2.hcardT123_100_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T123_100_2 i) (Q2.hfix123_100_2 i) _)
      colCert_123_100_4.hD ?_).symm
  rw [alnId_123 j hj]


theorem leaf_123_100_5 (hp : 5 < (Q2.transData.getD 100 []).length)
    (j : Nat) (hj : j < (repChars.getD 123 []).length)
    (hq : (normIsRep.getD 123 []).getD j false = true) :
    species (Q2.reps (⟨100, by decide⟩ : Fin 148)) (colE2 ⟨100, by decide⟩ 5 hp)
        (rowE2 (⟨123, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨100, by decide⟩ : Fin 148))
        (colE1 ⟨100, by decide⟩ 5 (transLenTr ⟨100, by decide⟩ 5 hp))
        (rowE1 (⟨123, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨123, by decide⟩ : Fin 148) ⟨100, by decide⟩ _
      (validAt ⟨123, by decide⟩ (listedAt ⟨123, by decide⟩ hj))
      (colE1 ⟨100, by decide⟩ 5 (transLenTr ⟨100, by decide⟩ 5 hp)) T123_100
      hfix123_100 hinj123_100 hcardT123_100
      (fun i => conj_mem_of_fixedPoints _ _ (T123_100 i) (hfix123_100 i) _)
      ⟨123, by decide⟩ ⟨100, by decide⟩ _
      (Q2.validAt ⟨123, by decide⟩ (Q2.listedAt ⟨123, by decide⟩
        (alnCheck_rep ⟨123, by decide⟩ hj hq).1))
      (colE2 ⟨100, by decide⟩ 5 hp) Q2.T123_100_2 Q2.hfix123_100_2 Q2.hinj123_100_2
      Q2.hcardT123_100_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T123_100_2 i) (Q2.hfix123_100_2 i) _)
      colCert_123_100_5.hD ?_).symm
  rw [alnId_123 j hj]


theorem leaf_123_100_10 (hp : 10 < (Q2.transData.getD 100 []).length)
    (j : Nat) (hj : j < (repChars.getD 123 []).length)
    (hq : (normIsRep.getD 123 []).getD j false = true) :
    species (Q2.reps (⟨100, by decide⟩ : Fin 148)) (colE2 ⟨100, by decide⟩ 10 hp)
        (rowE2 (⟨123, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨100, by decide⟩ : Fin 148))
        (colE1 ⟨100, by decide⟩ 10 (transLenTr ⟨100, by decide⟩ 10 hp))
        (rowE1 (⟨123, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨123, by decide⟩ : Fin 148) ⟨100, by decide⟩ _
      (validAt ⟨123, by decide⟩ (listedAt ⟨123, by decide⟩ hj))
      (colE1 ⟨100, by decide⟩ 10 (transLenTr ⟨100, by decide⟩ 10 hp)) T123_100
      hfix123_100 hinj123_100 hcardT123_100
      (fun i => conj_mem_of_fixedPoints _ _ (T123_100 i) (hfix123_100 i) _)
      ⟨123, by decide⟩ ⟨100, by decide⟩ _
      (Q2.validAt ⟨123, by decide⟩ (Q2.listedAt ⟨123, by decide⟩
        (alnCheck_rep ⟨123, by decide⟩ hj hq).1))
      (colE2 ⟨100, by decide⟩ 10 hp) Q2.T123_100_2 Q2.hfix123_100_2 Q2.hinj123_100_2
      Q2.hcardT123_100_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T123_100_2 i) (Q2.hfix123_100_2 i) _)
      colCert_123_100_10.hD ?_).symm
  rw [alnId_123 j hj]


theorem leaf_123_100_15 (hp : 15 < (Q2.transData.getD 100 []).length)
    (j : Nat) (hj : j < (repChars.getD 123 []).length)
    (hq : (normIsRep.getD 123 []).getD j false = true) :
    species (Q2.reps (⟨100, by decide⟩ : Fin 148)) (colE2 ⟨100, by decide⟩ 15 hp)
        (rowE2 (⟨123, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨100, by decide⟩ : Fin 148))
        (colE1 ⟨100, by decide⟩ 15 (transLenTr ⟨100, by decide⟩ 15 hp))
        (rowE1 (⟨123, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨123, by decide⟩ : Fin 148) ⟨100, by decide⟩ _
      (validAt ⟨123, by decide⟩ (listedAt ⟨123, by decide⟩ hj))
      (colE1 ⟨100, by decide⟩ 15 (transLenTr ⟨100, by decide⟩ 15 hp)) T123_100
      hfix123_100 hinj123_100 hcardT123_100
      (fun i => conj_mem_of_fixedPoints _ _ (T123_100 i) (hfix123_100 i) _)
      ⟨123, by decide⟩ ⟨100, by decide⟩ _
      (Q2.validAt ⟨123, by decide⟩ (Q2.listedAt ⟨123, by decide⟩
        (alnCheck_rep ⟨123, by decide⟩ hj hq).1))
      (colE2 ⟨100, by decide⟩ 15 hp) Q2.T123_100_2 Q2.hfix123_100_2 Q2.hinj123_100_2
      Q2.hcardT123_100_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T123_100_2 i) (Q2.hfix123_100_2 i) _)
      colCert_123_100_15.hD ?_).symm
  rw [alnId_123 j hj]


theorem leaf_123_100_20 (hp : 20 < (Q2.transData.getD 100 []).length)
    (j : Nat) (hj : j < (repChars.getD 123 []).length)
    (hq : (normIsRep.getD 123 []).getD j false = true) :
    species (Q2.reps (⟨100, by decide⟩ : Fin 148)) (colE2 ⟨100, by decide⟩ 20 hp)
        (rowE2 (⟨123, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨100, by decide⟩ : Fin 148))
        (colE1 ⟨100, by decide⟩ 20 (transLenTr ⟨100, by decide⟩ 20 hp))
        (rowE1 (⟨123, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨123, by decide⟩ : Fin 148) ⟨100, by decide⟩ _
      (validAt ⟨123, by decide⟩ (listedAt ⟨123, by decide⟩ hj))
      (colE1 ⟨100, by decide⟩ 20 (transLenTr ⟨100, by decide⟩ 20 hp)) T123_100
      hfix123_100 hinj123_100 hcardT123_100
      (fun i => conj_mem_of_fixedPoints _ _ (T123_100 i) (hfix123_100 i) _)
      ⟨123, by decide⟩ ⟨100, by decide⟩ _
      (Q2.validAt ⟨123, by decide⟩ (Q2.listedAt ⟨123, by decide⟩
        (alnCheck_rep ⟨123, by decide⟩ hj hq).1))
      (colE2 ⟨100, by decide⟩ 20 hp) Q2.T123_100_2 Q2.hfix123_100_2 Q2.hinj123_100_2
      Q2.hcardT123_100_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T123_100_2 i) (Q2.hfix123_100_2 i) _)
      colCert_123_100_20.hD ?_).symm
  rw [alnId_123 j hj]


theorem leaf_123_100_25 (hp : 25 < (Q2.transData.getD 100 []).length)
    (j : Nat) (hj : j < (repChars.getD 123 []).length)
    (hq : (normIsRep.getD 123 []).getD j false = true) :
    species (Q2.reps (⟨100, by decide⟩ : Fin 148)) (colE2 ⟨100, by decide⟩ 25 hp)
        (rowE2 (⟨123, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨100, by decide⟩ : Fin 148))
        (colE1 ⟨100, by decide⟩ 25 (transLenTr ⟨100, by decide⟩ 25 hp))
        (rowE1 (⟨123, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨123, by decide⟩ : Fin 148) ⟨100, by decide⟩ _
      (validAt ⟨123, by decide⟩ (listedAt ⟨123, by decide⟩ hj))
      (colE1 ⟨100, by decide⟩ 25 (transLenTr ⟨100, by decide⟩ 25 hp)) T123_100
      hfix123_100 hinj123_100 hcardT123_100
      (fun i => conj_mem_of_fixedPoints _ _ (T123_100 i) (hfix123_100 i) _)
      ⟨123, by decide⟩ ⟨100, by decide⟩ _
      (Q2.validAt ⟨123, by decide⟩ (Q2.listedAt ⟨123, by decide⟩
        (alnCheck_rep ⟨123, by decide⟩ hj hq).1))
      (colE2 ⟨100, by decide⟩ 25 hp) Q2.T123_100_2 Q2.hfix123_100_2 Q2.hinj123_100_2
      Q2.hcardT123_100_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T123_100_2 i) (Q2.hfix123_100_2 i) _)
      ?_).symm
  rw [show colData1 (⟨123, by decide⟩ : Fin 148)
        ((colE1 ⟨100, by decide⟩ 25 (transLenTr ⟨100, by decide⟩ 25 hp) : ↥(reps ⟨100, by decide⟩)) : Coordinate 1)
        T123_100 = colFn colCertDiv_123_100_25.D1 (m := 5) from colCertDiv_123_100_25.bind1,
    show colData2 (⟨123, by decide⟩ : Fin 148)
        ((colE2 ⟨100, by decide⟩ 25 hp : ↥(Q2.reps ⟨100, by decide⟩)) : Coordinate 2)
        Q2.T123_100_2 = colFn colCertDiv_123_100_25.D2 (m := 5) from colCertDiv_123_100_25.bind2]
  rw [alnId_123 j hj]
  exact fastcode_of_div ⟨123, by decide⟩ _ _ _
    ((alnId_123 j hj) ▸ Q2.listedAt (⟨123, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨123, by decide⟩ : Fin 148) hj hq).1) colCertDiv_123_100_25_match


theorem leaf_123_100_50 (hp : 50 < (Q2.transData.getD 100 []).length)
    (j : Nat) (hj : j < (repChars.getD 123 []).length)
    (hq : (normIsRep.getD 123 []).getD j false = true) :
    species (Q2.reps (⟨100, by decide⟩ : Fin 148)) (colE2 ⟨100, by decide⟩ 50 hp)
        (rowE2 (⟨123, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨100, by decide⟩ : Fin 148))
        (colE1 ⟨100, by decide⟩ 50 (transLenTr ⟨100, by decide⟩ 50 hp))
        (rowE1 (⟨123, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨123, by decide⟩ : Fin 148) ⟨100, by decide⟩ _
      (validAt ⟨123, by decide⟩ (listedAt ⟨123, by decide⟩ hj))
      (colE1 ⟨100, by decide⟩ 50 (transLenTr ⟨100, by decide⟩ 50 hp)) T123_100
      hfix123_100 hinj123_100 hcardT123_100
      (fun i => conj_mem_of_fixedPoints _ _ (T123_100 i) (hfix123_100 i) _)
      ⟨123, by decide⟩ ⟨100, by decide⟩ _
      (Q2.validAt ⟨123, by decide⟩ (Q2.listedAt ⟨123, by decide⟩
        (alnCheck_rep ⟨123, by decide⟩ hj hq).1))
      (colE2 ⟨100, by decide⟩ 50 hp) Q2.T123_100_2 Q2.hfix123_100_2 Q2.hinj123_100_2
      Q2.hcardT123_100_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T123_100_2 i) (Q2.hfix123_100_2 i) _)
      ?_).symm
  rw [show colData1 (⟨123, by decide⟩ : Fin 148)
        ((colE1 ⟨100, by decide⟩ 50 (transLenTr ⟨100, by decide⟩ 50 hp) : ↥(reps ⟨100, by decide⟩)) : Coordinate 1)
        T123_100 = colFn colCertDiv_123_100_50.D1 (m := 5) from colCertDiv_123_100_50.bind1,
    show colData2 (⟨123, by decide⟩ : Fin 148)
        ((colE2 ⟨100, by decide⟩ 50 hp : ↥(Q2.reps ⟨100, by decide⟩)) : Coordinate 2)
        Q2.T123_100_2 = colFn colCertDiv_123_100_50.D2 (m := 5) from colCertDiv_123_100_50.bind2]
  rw [alnId_123 j hj]
  exact fastcode_of_div ⟨123, by decide⟩ _ _ _
    ((alnId_123 j hj) ▸ Q2.listedAt (⟨123, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨123, by decide⟩ : Fin 148) hj hq).1) colCertDiv_123_100_50_match


theorem leaf_123_100_75 (hp : 75 < (Q2.transData.getD 100 []).length)
    (j : Nat) (hj : j < (repChars.getD 123 []).length)
    (hq : (normIsRep.getD 123 []).getD j false = true) :
    species (Q2.reps (⟨100, by decide⟩ : Fin 148)) (colE2 ⟨100, by decide⟩ 75 hp)
        (rowE2 (⟨123, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨100, by decide⟩ : Fin 148))
        (colE1 ⟨100, by decide⟩ 75 (transLenTr ⟨100, by decide⟩ 75 hp))
        (rowE1 (⟨123, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨123, by decide⟩ : Fin 148) ⟨100, by decide⟩ _
      (validAt ⟨123, by decide⟩ (listedAt ⟨123, by decide⟩ hj))
      (colE1 ⟨100, by decide⟩ 75 (transLenTr ⟨100, by decide⟩ 75 hp)) T123_100
      hfix123_100 hinj123_100 hcardT123_100
      (fun i => conj_mem_of_fixedPoints _ _ (T123_100 i) (hfix123_100 i) _)
      ⟨123, by decide⟩ ⟨100, by decide⟩ _
      (Q2.validAt ⟨123, by decide⟩ (Q2.listedAt ⟨123, by decide⟩
        (alnCheck_rep ⟨123, by decide⟩ hj hq).1))
      (colE2 ⟨100, by decide⟩ 75 hp) Q2.T123_100_2 Q2.hfix123_100_2 Q2.hinj123_100_2
      Q2.hcardT123_100_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T123_100_2 i) (Q2.hfix123_100_2 i) _)
      ?_).symm
  rw [show colData1 (⟨123, by decide⟩ : Fin 148)
        ((colE1 ⟨100, by decide⟩ 75 (transLenTr ⟨100, by decide⟩ 75 hp) : ↥(reps ⟨100, by decide⟩)) : Coordinate 1)
        T123_100 = colFn colCertDiv_123_100_75.D1 (m := 5) from colCertDiv_123_100_75.bind1,
    show colData2 (⟨123, by decide⟩ : Fin 148)
        ((colE2 ⟨100, by decide⟩ 75 hp : ↥(Q2.reps ⟨100, by decide⟩)) : Coordinate 2)
        Q2.T123_100_2 = colFn colCertDiv_123_100_75.D2 (m := 5) from colCertDiv_123_100_75.bind2]
  rw [alnId_123 j hj]
  exact fastcode_of_div ⟨123, by decide⟩ _ _ _
    ((alnId_123 j hj) ▸ Q2.listedAt (⟨123, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨123, by decide⟩ : Fin 148) hj hq).1) colCertDiv_123_100_75_match


theorem leaf_123_100_100 (hp : 100 < (Q2.transData.getD 100 []).length)
    (j : Nat) (hj : j < (repChars.getD 123 []).length)
    (hq : (normIsRep.getD 123 []).getD j false = true) :
    species (Q2.reps (⟨100, by decide⟩ : Fin 148)) (colE2 ⟨100, by decide⟩ 100 hp)
        (rowE2 (⟨123, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨100, by decide⟩ : Fin 148))
        (colE1 ⟨100, by decide⟩ 100 (transLenTr ⟨100, by decide⟩ 100 hp))
        (rowE1 (⟨123, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨123, by decide⟩ : Fin 148) ⟨100, by decide⟩ _
      (validAt ⟨123, by decide⟩ (listedAt ⟨123, by decide⟩ hj))
      (colE1 ⟨100, by decide⟩ 100 (transLenTr ⟨100, by decide⟩ 100 hp)) T123_100
      hfix123_100 hinj123_100 hcardT123_100
      (fun i => conj_mem_of_fixedPoints _ _ (T123_100 i) (hfix123_100 i) _)
      ⟨123, by decide⟩ ⟨100, by decide⟩ _
      (Q2.validAt ⟨123, by decide⟩ (Q2.listedAt ⟨123, by decide⟩
        (alnCheck_rep ⟨123, by decide⟩ hj hq).1))
      (colE2 ⟨100, by decide⟩ 100 hp) Q2.T123_100_2 Q2.hfix123_100_2 Q2.hinj123_100_2
      Q2.hcardT123_100_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T123_100_2 i) (Q2.hfix123_100_2 i) _)
      ?_).symm
  rw [show colData1 (⟨123, by decide⟩ : Fin 148)
        ((colE1 ⟨100, by decide⟩ 100 (transLenTr ⟨100, by decide⟩ 100 hp) : ↥(reps ⟨100, by decide⟩)) : Coordinate 1)
        T123_100 = colFn colCertDiv_123_100_100.D1 (m := 5) from colCertDiv_123_100_100.bind1,
    show colData2 (⟨123, by decide⟩ : Fin 148)
        ((colE2 ⟨100, by decide⟩ 100 hp : ↥(Q2.reps ⟨100, by decide⟩)) : Coordinate 2)
        Q2.T123_100_2 = colFn colCertDiv_123_100_100.D2 (m := 5) from colCertDiv_123_100_100.bind2]
  rw [alnId_123 j hj]
  exact fastcode_of_div ⟨123, by decide⟩ _ _ _
    ((alnId_123 j hj) ▸ Q2.listedAt (⟨123, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨123, by decide⟩ : Fin 148) hj hq).1) colCertDiv_123_100_100_match


theorem leaf_123_108_0 (hp : 0 < (Q2.transData.getD 108 []).length)
    (j : Nat) (hj : j < (repChars.getD 123 []).length)
    (hq : (normIsRep.getD 123 []).getD j false = true) :
    species (Q2.reps (⟨108, by decide⟩ : Fin 148)) (colE2 ⟨108, by decide⟩ 0 hp)
        (rowE2 (⟨123, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨108, by decide⟩ : Fin 148))
        (colE1 ⟨108, by decide⟩ 0 (transLenTr ⟨108, by decide⟩ 0 hp))
        (rowE1 (⟨123, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨123, by decide⟩ : Fin 148) ⟨108, by decide⟩ _
      (validAt ⟨123, by decide⟩ (listedAt ⟨123, by decide⟩ hj))
      (colE1 ⟨108, by decide⟩ 0 (transLenTr ⟨108, by decide⟩ 0 hp)) T123_108
      hfix123_108 hinj123_108 hcardT123_108
      (fun i => conj_mem_of_fixedPoints _ _ (T123_108 i) (hfix123_108 i) _)
      ⟨123, by decide⟩ ⟨108, by decide⟩ _
      (Q2.validAt ⟨123, by decide⟩ (Q2.listedAt ⟨123, by decide⟩
        (alnCheck_rep ⟨123, by decide⟩ hj hq).1))
      (colE2 ⟨108, by decide⟩ 0 hp) Q2.T123_108_2 Q2.hfix123_108_2 Q2.hinj123_108_2
      Q2.hcardT123_108_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T123_108_2 i) (Q2.hfix123_108_2 i) _)
      colCert_123_108_0.hD ?_).symm
  rw [alnId_123 j hj]


theorem leaf_123_108_1 (hp : 1 < (Q2.transData.getD 108 []).length)
    (j : Nat) (hj : j < (repChars.getD 123 []).length)
    (hq : (normIsRep.getD 123 []).getD j false = true) :
    species (Q2.reps (⟨108, by decide⟩ : Fin 148)) (colE2 ⟨108, by decide⟩ 1 hp)
        (rowE2 (⟨123, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨108, by decide⟩ : Fin 148))
        (colE1 ⟨108, by decide⟩ 1 (transLenTr ⟨108, by decide⟩ 1 hp))
        (rowE1 (⟨123, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨123, by decide⟩ : Fin 148) ⟨108, by decide⟩ _
      (validAt ⟨123, by decide⟩ (listedAt ⟨123, by decide⟩ hj))
      (colE1 ⟨108, by decide⟩ 1 (transLenTr ⟨108, by decide⟩ 1 hp)) T123_108
      hfix123_108 hinj123_108 hcardT123_108
      (fun i => conj_mem_of_fixedPoints _ _ (T123_108 i) (hfix123_108 i) _)
      ⟨123, by decide⟩ ⟨108, by decide⟩ _
      (Q2.validAt ⟨123, by decide⟩ (Q2.listedAt ⟨123, by decide⟩
        (alnCheck_rep ⟨123, by decide⟩ hj hq).1))
      (colE2 ⟨108, by decide⟩ 1 hp) Q2.T123_108_2 Q2.hfix123_108_2 Q2.hinj123_108_2
      Q2.hcardT123_108_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T123_108_2 i) (Q2.hfix123_108_2 i) _)
      colCert_123_108_1.hD ?_).symm
  rw [alnId_123 j hj]


theorem leaf_123_108_2 (hp : 2 < (Q2.transData.getD 108 []).length)
    (j : Nat) (hj : j < (repChars.getD 123 []).length)
    (hq : (normIsRep.getD 123 []).getD j false = true) :
    species (Q2.reps (⟨108, by decide⟩ : Fin 148)) (colE2 ⟨108, by decide⟩ 2 hp)
        (rowE2 (⟨123, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨108, by decide⟩ : Fin 148))
        (colE1 ⟨108, by decide⟩ 2 (transLenTr ⟨108, by decide⟩ 2 hp))
        (rowE1 (⟨123, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨123, by decide⟩ : Fin 148) ⟨108, by decide⟩ _
      (validAt ⟨123, by decide⟩ (listedAt ⟨123, by decide⟩ hj))
      (colE1 ⟨108, by decide⟩ 2 (transLenTr ⟨108, by decide⟩ 2 hp)) T123_108
      hfix123_108 hinj123_108 hcardT123_108
      (fun i => conj_mem_of_fixedPoints _ _ (T123_108 i) (hfix123_108 i) _)
      ⟨123, by decide⟩ ⟨108, by decide⟩ _
      (Q2.validAt ⟨123, by decide⟩ (Q2.listedAt ⟨123, by decide⟩
        (alnCheck_rep ⟨123, by decide⟩ hj hq).1))
      (colE2 ⟨108, by decide⟩ 2 hp) Q2.T123_108_2 Q2.hfix123_108_2 Q2.hinj123_108_2
      Q2.hcardT123_108_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T123_108_2 i) (Q2.hfix123_108_2 i) _)
      colCert_123_108_2.hD ?_).symm
  rw [alnId_123 j hj]


theorem leaf_123_108_3 (hp : 3 < (Q2.transData.getD 108 []).length)
    (j : Nat) (hj : j < (repChars.getD 123 []).length)
    (hq : (normIsRep.getD 123 []).getD j false = true) :
    species (Q2.reps (⟨108, by decide⟩ : Fin 148)) (colE2 ⟨108, by decide⟩ 3 hp)
        (rowE2 (⟨123, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨108, by decide⟩ : Fin 148))
        (colE1 ⟨108, by decide⟩ 3 (transLenTr ⟨108, by decide⟩ 3 hp))
        (rowE1 (⟨123, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨123, by decide⟩ : Fin 148) ⟨108, by decide⟩ _
      (validAt ⟨123, by decide⟩ (listedAt ⟨123, by decide⟩ hj))
      (colE1 ⟨108, by decide⟩ 3 (transLenTr ⟨108, by decide⟩ 3 hp)) T123_108
      hfix123_108 hinj123_108 hcardT123_108
      (fun i => conj_mem_of_fixedPoints _ _ (T123_108 i) (hfix123_108 i) _)
      ⟨123, by decide⟩ ⟨108, by decide⟩ _
      (Q2.validAt ⟨123, by decide⟩ (Q2.listedAt ⟨123, by decide⟩
        (alnCheck_rep ⟨123, by decide⟩ hj hq).1))
      (colE2 ⟨108, by decide⟩ 3 hp) Q2.T123_108_2 Q2.hfix123_108_2 Q2.hinj123_108_2
      Q2.hcardT123_108_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T123_108_2 i) (Q2.hfix123_108_2 i) _)
      colCert_123_108_3.hD ?_).symm
  rw [alnId_123 j hj]


theorem leaf_123_108_4 (hp : 4 < (Q2.transData.getD 108 []).length)
    (j : Nat) (hj : j < (repChars.getD 123 []).length)
    (hq : (normIsRep.getD 123 []).getD j false = true) :
    species (Q2.reps (⟨108, by decide⟩ : Fin 148)) (colE2 ⟨108, by decide⟩ 4 hp)
        (rowE2 (⟨123, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨108, by decide⟩ : Fin 148))
        (colE1 ⟨108, by decide⟩ 4 (transLenTr ⟨108, by decide⟩ 4 hp))
        (rowE1 (⟨123, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨123, by decide⟩ : Fin 148) ⟨108, by decide⟩ _
      (validAt ⟨123, by decide⟩ (listedAt ⟨123, by decide⟩ hj))
      (colE1 ⟨108, by decide⟩ 4 (transLenTr ⟨108, by decide⟩ 4 hp)) T123_108
      hfix123_108 hinj123_108 hcardT123_108
      (fun i => conj_mem_of_fixedPoints _ _ (T123_108 i) (hfix123_108 i) _)
      ⟨123, by decide⟩ ⟨108, by decide⟩ _
      (Q2.validAt ⟨123, by decide⟩ (Q2.listedAt ⟨123, by decide⟩
        (alnCheck_rep ⟨123, by decide⟩ hj hq).1))
      (colE2 ⟨108, by decide⟩ 4 hp) Q2.T123_108_2 Q2.hfix123_108_2 Q2.hinj123_108_2
      Q2.hcardT123_108_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T123_108_2 i) (Q2.hfix123_108_2 i) _)
      colCert_123_108_4.hD ?_).symm
  rw [alnId_123 j hj]


theorem leaf_123_108_5 (hp : 5 < (Q2.transData.getD 108 []).length)
    (j : Nat) (hj : j < (repChars.getD 123 []).length)
    (hq : (normIsRep.getD 123 []).getD j false = true) :
    species (Q2.reps (⟨108, by decide⟩ : Fin 148)) (colE2 ⟨108, by decide⟩ 5 hp)
        (rowE2 (⟨123, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨108, by decide⟩ : Fin 148))
        (colE1 ⟨108, by decide⟩ 5 (transLenTr ⟨108, by decide⟩ 5 hp))
        (rowE1 (⟨123, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨123, by decide⟩ : Fin 148) ⟨108, by decide⟩ _
      (validAt ⟨123, by decide⟩ (listedAt ⟨123, by decide⟩ hj))
      (colE1 ⟨108, by decide⟩ 5 (transLenTr ⟨108, by decide⟩ 5 hp)) T123_108
      hfix123_108 hinj123_108 hcardT123_108
      (fun i => conj_mem_of_fixedPoints _ _ (T123_108 i) (hfix123_108 i) _)
      ⟨123, by decide⟩ ⟨108, by decide⟩ _
      (Q2.validAt ⟨123, by decide⟩ (Q2.listedAt ⟨123, by decide⟩
        (alnCheck_rep ⟨123, by decide⟩ hj hq).1))
      (colE2 ⟨108, by decide⟩ 5 hp) Q2.T123_108_2 Q2.hfix123_108_2 Q2.hinj123_108_2
      Q2.hcardT123_108_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T123_108_2 i) (Q2.hfix123_108_2 i) _)
      ?_).symm
  rw [show colData1 (⟨123, by decide⟩ : Fin 148)
        ((colE1 ⟨108, by decide⟩ 5 (transLenTr ⟨108, by decide⟩ 5 hp) : ↥(reps ⟨108, by decide⟩)) : Coordinate 1)
        T123_108 = colFn colCertDiv_123_108_5.D1 (m := 5) from colCertDiv_123_108_5.bind1,
    show colData2 (⟨123, by decide⟩ : Fin 148)
        ((colE2 ⟨108, by decide⟩ 5 hp : ↥(Q2.reps ⟨108, by decide⟩)) : Coordinate 2)
        Q2.T123_108_2 = colFn colCertDiv_123_108_5.D2 (m := 5) from colCertDiv_123_108_5.bind2]
  rw [alnId_123 j hj]
  exact fastcode_of_div ⟨123, by decide⟩ _ _ _
    ((alnId_123 j hj) ▸ Q2.listedAt (⟨123, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨123, by decide⟩ : Fin 148) hj hq).1) colCertDiv_123_108_5_match


theorem leaf_123_108_10 (hp : 10 < (Q2.transData.getD 108 []).length)
    (j : Nat) (hj : j < (repChars.getD 123 []).length)
    (hq : (normIsRep.getD 123 []).getD j false = true) :
    species (Q2.reps (⟨108, by decide⟩ : Fin 148)) (colE2 ⟨108, by decide⟩ 10 hp)
        (rowE2 (⟨123, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨108, by decide⟩ : Fin 148))
        (colE1 ⟨108, by decide⟩ 10 (transLenTr ⟨108, by decide⟩ 10 hp))
        (rowE1 (⟨123, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨123, by decide⟩ : Fin 148) ⟨108, by decide⟩ _
      (validAt ⟨123, by decide⟩ (listedAt ⟨123, by decide⟩ hj))
      (colE1 ⟨108, by decide⟩ 10 (transLenTr ⟨108, by decide⟩ 10 hp)) T123_108
      hfix123_108 hinj123_108 hcardT123_108
      (fun i => conj_mem_of_fixedPoints _ _ (T123_108 i) (hfix123_108 i) _)
      ⟨123, by decide⟩ ⟨108, by decide⟩ _
      (Q2.validAt ⟨123, by decide⟩ (Q2.listedAt ⟨123, by decide⟩
        (alnCheck_rep ⟨123, by decide⟩ hj hq).1))
      (colE2 ⟨108, by decide⟩ 10 hp) Q2.T123_108_2 Q2.hfix123_108_2 Q2.hinj123_108_2
      Q2.hcardT123_108_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T123_108_2 i) (Q2.hfix123_108_2 i) _)
      ?_).symm
  rw [show colData1 (⟨123, by decide⟩ : Fin 148)
        ((colE1 ⟨108, by decide⟩ 10 (transLenTr ⟨108, by decide⟩ 10 hp) : ↥(reps ⟨108, by decide⟩)) : Coordinate 1)
        T123_108 = colFn colCertDiv_123_108_10.D1 (m := 5) from colCertDiv_123_108_10.bind1,
    show colData2 (⟨123, by decide⟩ : Fin 148)
        ((colE2 ⟨108, by decide⟩ 10 hp : ↥(Q2.reps ⟨108, by decide⟩)) : Coordinate 2)
        Q2.T123_108_2 = colFn colCertDiv_123_108_10.D2 (m := 5) from colCertDiv_123_108_10.bind2]
  rw [alnId_123 j hj]
  exact fastcode_of_div ⟨123, by decide⟩ _ _ _
    ((alnId_123 j hj) ▸ Q2.listedAt (⟨123, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨123, by decide⟩ : Fin 148) hj hq).1) colCertDiv_123_108_10_match


theorem leaf_123_108_15 (hp : 15 < (Q2.transData.getD 108 []).length)
    (j : Nat) (hj : j < (repChars.getD 123 []).length)
    (hq : (normIsRep.getD 123 []).getD j false = true) :
    species (Q2.reps (⟨108, by decide⟩ : Fin 148)) (colE2 ⟨108, by decide⟩ 15 hp)
        (rowE2 (⟨123, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨108, by decide⟩ : Fin 148))
        (colE1 ⟨108, by decide⟩ 15 (transLenTr ⟨108, by decide⟩ 15 hp))
        (rowE1 (⟨123, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨123, by decide⟩ : Fin 148) ⟨108, by decide⟩ _
      (validAt ⟨123, by decide⟩ (listedAt ⟨123, by decide⟩ hj))
      (colE1 ⟨108, by decide⟩ 15 (transLenTr ⟨108, by decide⟩ 15 hp)) T123_108
      hfix123_108 hinj123_108 hcardT123_108
      (fun i => conj_mem_of_fixedPoints _ _ (T123_108 i) (hfix123_108 i) _)
      ⟨123, by decide⟩ ⟨108, by decide⟩ _
      (Q2.validAt ⟨123, by decide⟩ (Q2.listedAt ⟨123, by decide⟩
        (alnCheck_rep ⟨123, by decide⟩ hj hq).1))
      (colE2 ⟨108, by decide⟩ 15 hp) Q2.T123_108_2 Q2.hfix123_108_2 Q2.hinj123_108_2
      Q2.hcardT123_108_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T123_108_2 i) (Q2.hfix123_108_2 i) _)
      ?_).symm
  rw [show colData1 (⟨123, by decide⟩ : Fin 148)
        ((colE1 ⟨108, by decide⟩ 15 (transLenTr ⟨108, by decide⟩ 15 hp) : ↥(reps ⟨108, by decide⟩)) : Coordinate 1)
        T123_108 = colFn colCertDiv_123_108_15.D1 (m := 5) from colCertDiv_123_108_15.bind1,
    show colData2 (⟨123, by decide⟩ : Fin 148)
        ((colE2 ⟨108, by decide⟩ 15 hp : ↥(Q2.reps ⟨108, by decide⟩)) : Coordinate 2)
        Q2.T123_108_2 = colFn colCertDiv_123_108_15.D2 (m := 5) from colCertDiv_123_108_15.bind2]
  rw [alnId_123 j hj]
  exact fastcode_of_div ⟨123, by decide⟩ _ _ _
    ((alnId_123 j hj) ▸ Q2.listedAt (⟨123, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨123, by decide⟩ : Fin 148) hj hq).1) colCertDiv_123_108_15_match


theorem leaf_123_108_20 (hp : 20 < (Q2.transData.getD 108 []).length)
    (j : Nat) (hj : j < (repChars.getD 123 []).length)
    (hq : (normIsRep.getD 123 []).getD j false = true) :
    species (Q2.reps (⟨108, by decide⟩ : Fin 148)) (colE2 ⟨108, by decide⟩ 20 hp)
        (rowE2 (⟨123, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨108, by decide⟩ : Fin 148))
        (colE1 ⟨108, by decide⟩ 20 (transLenTr ⟨108, by decide⟩ 20 hp))
        (rowE1 (⟨123, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨123, by decide⟩ : Fin 148) ⟨108, by decide⟩ _
      (validAt ⟨123, by decide⟩ (listedAt ⟨123, by decide⟩ hj))
      (colE1 ⟨108, by decide⟩ 20 (transLenTr ⟨108, by decide⟩ 20 hp)) T123_108
      hfix123_108 hinj123_108 hcardT123_108
      (fun i => conj_mem_of_fixedPoints _ _ (T123_108 i) (hfix123_108 i) _)
      ⟨123, by decide⟩ ⟨108, by decide⟩ _
      (Q2.validAt ⟨123, by decide⟩ (Q2.listedAt ⟨123, by decide⟩
        (alnCheck_rep ⟨123, by decide⟩ hj hq).1))
      (colE2 ⟨108, by decide⟩ 20 hp) Q2.T123_108_2 Q2.hfix123_108_2 Q2.hinj123_108_2
      Q2.hcardT123_108_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T123_108_2 i) (Q2.hfix123_108_2 i) _)
      ?_).symm
  rw [show colData1 (⟨123, by decide⟩ : Fin 148)
        ((colE1 ⟨108, by decide⟩ 20 (transLenTr ⟨108, by decide⟩ 20 hp) : ↥(reps ⟨108, by decide⟩)) : Coordinate 1)
        T123_108 = colFn colCertDiv_123_108_20.D1 (m := 5) from colCertDiv_123_108_20.bind1,
    show colData2 (⟨123, by decide⟩ : Fin 148)
        ((colE2 ⟨108, by decide⟩ 20 hp : ↥(Q2.reps ⟨108, by decide⟩)) : Coordinate 2)
        Q2.T123_108_2 = colFn colCertDiv_123_108_20.D2 (m := 5) from colCertDiv_123_108_20.bind2]
  rw [alnId_123 j hj]
  exact fastcode_of_div ⟨123, by decide⟩ _ _ _
    ((alnId_123 j hj) ▸ Q2.listedAt (⟨123, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨123, by decide⟩ : Fin 148) hj hq).1) colCertDiv_123_108_20_match


theorem leaf_123_112_0 (hp : 0 < (Q2.transData.getD 112 []).length)
    (j : Nat) (hj : j < (repChars.getD 123 []).length)
    (hq : (normIsRep.getD 123 []).getD j false = true) :
    species (Q2.reps (⟨112, by decide⟩ : Fin 148)) (colE2 ⟨112, by decide⟩ 0 hp)
        (rowE2 (⟨123, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨112, by decide⟩ : Fin 148))
        (colE1 ⟨112, by decide⟩ 0 (transLenTr ⟨112, by decide⟩ 0 hp))
        (rowE1 (⟨123, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨123, by decide⟩ : Fin 148) ⟨112, by decide⟩ _
      (validAt ⟨123, by decide⟩ (listedAt ⟨123, by decide⟩ hj))
      (colE1 ⟨112, by decide⟩ 0 (transLenTr ⟨112, by decide⟩ 0 hp)) T123_112
      hfix123_112 hinj123_112 hcardT123_112
      (fun i => conj_mem_of_fixedPoints _ _ (T123_112 i) (hfix123_112 i) _)
      ⟨123, by decide⟩ ⟨112, by decide⟩ _
      (Q2.validAt ⟨123, by decide⟩ (Q2.listedAt ⟨123, by decide⟩
        (alnCheck_rep ⟨123, by decide⟩ hj hq).1))
      (colE2 ⟨112, by decide⟩ 0 hp) Q2.T123_112_2 Q2.hfix123_112_2 Q2.hinj123_112_2
      Q2.hcardT123_112_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T123_112_2 i) (Q2.hfix123_112_2 i) _)
      colCert_123_112_0.hD ?_).symm
  rw [alnId_123 j hj]


theorem leaf_123_112_1 (hp : 1 < (Q2.transData.getD 112 []).length)
    (j : Nat) (hj : j < (repChars.getD 123 []).length)
    (hq : (normIsRep.getD 123 []).getD j false = true) :
    species (Q2.reps (⟨112, by decide⟩ : Fin 148)) (colE2 ⟨112, by decide⟩ 1 hp)
        (rowE2 (⟨123, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨112, by decide⟩ : Fin 148))
        (colE1 ⟨112, by decide⟩ 1 (transLenTr ⟨112, by decide⟩ 1 hp))
        (rowE1 (⟨123, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨123, by decide⟩ : Fin 148) ⟨112, by decide⟩ _
      (validAt ⟨123, by decide⟩ (listedAt ⟨123, by decide⟩ hj))
      (colE1 ⟨112, by decide⟩ 1 (transLenTr ⟨112, by decide⟩ 1 hp)) T123_112
      hfix123_112 hinj123_112 hcardT123_112
      (fun i => conj_mem_of_fixedPoints _ _ (T123_112 i) (hfix123_112 i) _)
      ⟨123, by decide⟩ ⟨112, by decide⟩ _
      (Q2.validAt ⟨123, by decide⟩ (Q2.listedAt ⟨123, by decide⟩
        (alnCheck_rep ⟨123, by decide⟩ hj hq).1))
      (colE2 ⟨112, by decide⟩ 1 hp) Q2.T123_112_2 Q2.hfix123_112_2 Q2.hinj123_112_2
      Q2.hcardT123_112_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T123_112_2 i) (Q2.hfix123_112_2 i) _)
      colCert_123_112_1.hD ?_).symm
  rw [alnId_123 j hj]


theorem leaf_123_112_2 (hp : 2 < (Q2.transData.getD 112 []).length)
    (j : Nat) (hj : j < (repChars.getD 123 []).length)
    (hq : (normIsRep.getD 123 []).getD j false = true) :
    species (Q2.reps (⟨112, by decide⟩ : Fin 148)) (colE2 ⟨112, by decide⟩ 2 hp)
        (rowE2 (⟨123, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨112, by decide⟩ : Fin 148))
        (colE1 ⟨112, by decide⟩ 2 (transLenTr ⟨112, by decide⟩ 2 hp))
        (rowE1 (⟨123, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨123, by decide⟩ : Fin 148) ⟨112, by decide⟩ _
      (validAt ⟨123, by decide⟩ (listedAt ⟨123, by decide⟩ hj))
      (colE1 ⟨112, by decide⟩ 2 (transLenTr ⟨112, by decide⟩ 2 hp)) T123_112
      hfix123_112 hinj123_112 hcardT123_112
      (fun i => conj_mem_of_fixedPoints _ _ (T123_112 i) (hfix123_112 i) _)
      ⟨123, by decide⟩ ⟨112, by decide⟩ _
      (Q2.validAt ⟨123, by decide⟩ (Q2.listedAt ⟨123, by decide⟩
        (alnCheck_rep ⟨123, by decide⟩ hj hq).1))
      (colE2 ⟨112, by decide⟩ 2 hp) Q2.T123_112_2 Q2.hfix123_112_2 Q2.hinj123_112_2
      Q2.hcardT123_112_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T123_112_2 i) (Q2.hfix123_112_2 i) _)
      colCert_123_112_2.hD ?_).symm
  rw [alnId_123 j hj]


theorem leaf_123_112_3 (hp : 3 < (Q2.transData.getD 112 []).length)
    (j : Nat) (hj : j < (repChars.getD 123 []).length)
    (hq : (normIsRep.getD 123 []).getD j false = true) :
    species (Q2.reps (⟨112, by decide⟩ : Fin 148)) (colE2 ⟨112, by decide⟩ 3 hp)
        (rowE2 (⟨123, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨112, by decide⟩ : Fin 148))
        (colE1 ⟨112, by decide⟩ 3 (transLenTr ⟨112, by decide⟩ 3 hp))
        (rowE1 (⟨123, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨123, by decide⟩ : Fin 148) ⟨112, by decide⟩ _
      (validAt ⟨123, by decide⟩ (listedAt ⟨123, by decide⟩ hj))
      (colE1 ⟨112, by decide⟩ 3 (transLenTr ⟨112, by decide⟩ 3 hp)) T123_112
      hfix123_112 hinj123_112 hcardT123_112
      (fun i => conj_mem_of_fixedPoints _ _ (T123_112 i) (hfix123_112 i) _)
      ⟨123, by decide⟩ ⟨112, by decide⟩ _
      (Q2.validAt ⟨123, by decide⟩ (Q2.listedAt ⟨123, by decide⟩
        (alnCheck_rep ⟨123, by decide⟩ hj hq).1))
      (colE2 ⟨112, by decide⟩ 3 hp) Q2.T123_112_2 Q2.hfix123_112_2 Q2.hinj123_112_2
      Q2.hcardT123_112_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T123_112_2 i) (Q2.hfix123_112_2 i) _)
      colCert_123_112_3.hD ?_).symm
  rw [alnId_123 j hj]


theorem leaf_123_112_4 (hp : 4 < (Q2.transData.getD 112 []).length)
    (j : Nat) (hj : j < (repChars.getD 123 []).length)
    (hq : (normIsRep.getD 123 []).getD j false = true) :
    species (Q2.reps (⟨112, by decide⟩ : Fin 148)) (colE2 ⟨112, by decide⟩ 4 hp)
        (rowE2 (⟨123, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨112, by decide⟩ : Fin 148))
        (colE1 ⟨112, by decide⟩ 4 (transLenTr ⟨112, by decide⟩ 4 hp))
        (rowE1 (⟨123, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨123, by decide⟩ : Fin 148) ⟨112, by decide⟩ _
      (validAt ⟨123, by decide⟩ (listedAt ⟨123, by decide⟩ hj))
      (colE1 ⟨112, by decide⟩ 4 (transLenTr ⟨112, by decide⟩ 4 hp)) T123_112
      hfix123_112 hinj123_112 hcardT123_112
      (fun i => conj_mem_of_fixedPoints _ _ (T123_112 i) (hfix123_112 i) _)
      ⟨123, by decide⟩ ⟨112, by decide⟩ _
      (Q2.validAt ⟨123, by decide⟩ (Q2.listedAt ⟨123, by decide⟩
        (alnCheck_rep ⟨123, by decide⟩ hj hq).1))
      (colE2 ⟨112, by decide⟩ 4 hp) Q2.T123_112_2 Q2.hfix123_112_2 Q2.hinj123_112_2
      Q2.hcardT123_112_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T123_112_2 i) (Q2.hfix123_112_2 i) _)
      colCert_123_112_4.hD ?_).symm
  rw [alnId_123 j hj]


theorem leaf_123_112_5 (hp : 5 < (Q2.transData.getD 112 []).length)
    (j : Nat) (hj : j < (repChars.getD 123 []).length)
    (hq : (normIsRep.getD 123 []).getD j false = true) :
    species (Q2.reps (⟨112, by decide⟩ : Fin 148)) (colE2 ⟨112, by decide⟩ 5 hp)
        (rowE2 (⟨123, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨112, by decide⟩ : Fin 148))
        (colE1 ⟨112, by decide⟩ 5 (transLenTr ⟨112, by decide⟩ 5 hp))
        (rowE1 (⟨123, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨123, by decide⟩ : Fin 148) ⟨112, by decide⟩ _
      (validAt ⟨123, by decide⟩ (listedAt ⟨123, by decide⟩ hj))
      (colE1 ⟨112, by decide⟩ 5 (transLenTr ⟨112, by decide⟩ 5 hp)) T123_112
      hfix123_112 hinj123_112 hcardT123_112
      (fun i => conj_mem_of_fixedPoints _ _ (T123_112 i) (hfix123_112 i) _)
      ⟨123, by decide⟩ ⟨112, by decide⟩ _
      (Q2.validAt ⟨123, by decide⟩ (Q2.listedAt ⟨123, by decide⟩
        (alnCheck_rep ⟨123, by decide⟩ hj hq).1))
      (colE2 ⟨112, by decide⟩ 5 hp) Q2.T123_112_2 Q2.hfix123_112_2 Q2.hinj123_112_2
      Q2.hcardT123_112_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T123_112_2 i) (Q2.hfix123_112_2 i) _)
      colCert_123_112_5.hD ?_).symm
  rw [alnId_123 j hj]


theorem leaf_123_112_10 (hp : 10 < (Q2.transData.getD 112 []).length)
    (j : Nat) (hj : j < (repChars.getD 123 []).length)
    (hq : (normIsRep.getD 123 []).getD j false = true) :
    species (Q2.reps (⟨112, by decide⟩ : Fin 148)) (colE2 ⟨112, by decide⟩ 10 hp)
        (rowE2 (⟨123, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨112, by decide⟩ : Fin 148))
        (colE1 ⟨112, by decide⟩ 10 (transLenTr ⟨112, by decide⟩ 10 hp))
        (rowE1 (⟨123, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨123, by decide⟩ : Fin 148) ⟨112, by decide⟩ _
      (validAt ⟨123, by decide⟩ (listedAt ⟨123, by decide⟩ hj))
      (colE1 ⟨112, by decide⟩ 10 (transLenTr ⟨112, by decide⟩ 10 hp)) T123_112
      hfix123_112 hinj123_112 hcardT123_112
      (fun i => conj_mem_of_fixedPoints _ _ (T123_112 i) (hfix123_112 i) _)
      ⟨123, by decide⟩ ⟨112, by decide⟩ _
      (Q2.validAt ⟨123, by decide⟩ (Q2.listedAt ⟨123, by decide⟩
        (alnCheck_rep ⟨123, by decide⟩ hj hq).1))
      (colE2 ⟨112, by decide⟩ 10 hp) Q2.T123_112_2 Q2.hfix123_112_2 Q2.hinj123_112_2
      Q2.hcardT123_112_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T123_112_2 i) (Q2.hfix123_112_2 i) _)
      colCert_123_112_10.hD ?_).symm
  rw [alnId_123 j hj]


theorem leaf_123_112_15 (hp : 15 < (Q2.transData.getD 112 []).length)
    (j : Nat) (hj : j < (repChars.getD 123 []).length)
    (hq : (normIsRep.getD 123 []).getD j false = true) :
    species (Q2.reps (⟨112, by decide⟩ : Fin 148)) (colE2 ⟨112, by decide⟩ 15 hp)
        (rowE2 (⟨123, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨112, by decide⟩ : Fin 148))
        (colE1 ⟨112, by decide⟩ 15 (transLenTr ⟨112, by decide⟩ 15 hp))
        (rowE1 (⟨123, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨123, by decide⟩ : Fin 148) ⟨112, by decide⟩ _
      (validAt ⟨123, by decide⟩ (listedAt ⟨123, by decide⟩ hj))
      (colE1 ⟨112, by decide⟩ 15 (transLenTr ⟨112, by decide⟩ 15 hp)) T123_112
      hfix123_112 hinj123_112 hcardT123_112
      (fun i => conj_mem_of_fixedPoints _ _ (T123_112 i) (hfix123_112 i) _)
      ⟨123, by decide⟩ ⟨112, by decide⟩ _
      (Q2.validAt ⟨123, by decide⟩ (Q2.listedAt ⟨123, by decide⟩
        (alnCheck_rep ⟨123, by decide⟩ hj hq).1))
      (colE2 ⟨112, by decide⟩ 15 hp) Q2.T123_112_2 Q2.hfix123_112_2 Q2.hinj123_112_2
      Q2.hcardT123_112_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T123_112_2 i) (Q2.hfix123_112_2 i) _)
      ?_).symm
  rw [show colData1 (⟨123, by decide⟩ : Fin 148)
        ((colE1 ⟨112, by decide⟩ 15 (transLenTr ⟨112, by decide⟩ 15 hp) : ↥(reps ⟨112, by decide⟩)) : Coordinate 1)
        T123_112 = colFn colCertDiv_123_112_15.D1 (m := 5) from colCertDiv_123_112_15.bind1,
    show colData2 (⟨123, by decide⟩ : Fin 148)
        ((colE2 ⟨112, by decide⟩ 15 hp : ↥(Q2.reps ⟨112, by decide⟩)) : Coordinate 2)
        Q2.T123_112_2 = colFn colCertDiv_123_112_15.D2 (m := 5) from colCertDiv_123_112_15.bind2]
  rw [alnId_123 j hj]
  exact fastcode_of_div ⟨123, by decide⟩ _ _ _
    ((alnId_123 j hj) ▸ Q2.listedAt (⟨123, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨123, by decide⟩ : Fin 148) hj hq).1) colCertDiv_123_112_15_match


theorem leaf_123_112_20 (hp : 20 < (Q2.transData.getD 112 []).length)
    (j : Nat) (hj : j < (repChars.getD 123 []).length)
    (hq : (normIsRep.getD 123 []).getD j false = true) :
    species (Q2.reps (⟨112, by decide⟩ : Fin 148)) (colE2 ⟨112, by decide⟩ 20 hp)
        (rowE2 (⟨123, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨112, by decide⟩ : Fin 148))
        (colE1 ⟨112, by decide⟩ 20 (transLenTr ⟨112, by decide⟩ 20 hp))
        (rowE1 (⟨123, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨123, by decide⟩ : Fin 148) ⟨112, by decide⟩ _
      (validAt ⟨123, by decide⟩ (listedAt ⟨123, by decide⟩ hj))
      (colE1 ⟨112, by decide⟩ 20 (transLenTr ⟨112, by decide⟩ 20 hp)) T123_112
      hfix123_112 hinj123_112 hcardT123_112
      (fun i => conj_mem_of_fixedPoints _ _ (T123_112 i) (hfix123_112 i) _)
      ⟨123, by decide⟩ ⟨112, by decide⟩ _
      (Q2.validAt ⟨123, by decide⟩ (Q2.listedAt ⟨123, by decide⟩
        (alnCheck_rep ⟨123, by decide⟩ hj hq).1))
      (colE2 ⟨112, by decide⟩ 20 hp) Q2.T123_112_2 Q2.hfix123_112_2 Q2.hinj123_112_2
      Q2.hcardT123_112_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T123_112_2 i) (Q2.hfix123_112_2 i) _)
      ?_).symm
  rw [show colData1 (⟨123, by decide⟩ : Fin 148)
        ((colE1 ⟨112, by decide⟩ 20 (transLenTr ⟨112, by decide⟩ 20 hp) : ↥(reps ⟨112, by decide⟩)) : Coordinate 1)
        T123_112 = colFn colCertDiv_123_112_20.D1 (m := 5) from colCertDiv_123_112_20.bind1,
    show colData2 (⟨123, by decide⟩ : Fin 148)
        ((colE2 ⟨112, by decide⟩ 20 hp : ↥(Q2.reps ⟨112, by decide⟩)) : Coordinate 2)
        Q2.T123_112_2 = colFn colCertDiv_123_112_20.D2 (m := 5) from colCertDiv_123_112_20.bind2]
  rw [alnId_123 j hj]
  exact fastcode_of_div ⟨123, by decide⟩ _ _ _
    ((alnId_123 j hj) ▸ Q2.listedAt (⟨123, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨123, by decide⟩ : Fin 148) hj hq).1) colCertDiv_123_112_20_match


theorem leaf_123_123_0 (hp : 0 < (Q2.transData.getD 123 []).length)
    (j : Nat) (hj : j < (repChars.getD 123 []).length)
    (hq : (normIsRep.getD 123 []).getD j false = true) :
    species (Q2.reps (⟨123, by decide⟩ : Fin 148)) (colE2 ⟨123, by decide⟩ 0 hp)
        (rowE2 (⟨123, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨123, by decide⟩ : Fin 148))
        (colE1 ⟨123, by decide⟩ 0 (transLenTr ⟨123, by decide⟩ 0 hp))
        (rowE1 (⟨123, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨123, by decide⟩ : Fin 148) ⟨123, by decide⟩ _
      (validAt ⟨123, by decide⟩ (listedAt ⟨123, by decide⟩ hj))
      (colE1 ⟨123, by decide⟩ 0 (transLenTr ⟨123, by decide⟩ 0 hp)) T123_123
      hfix123_123 hinj123_123 hcardT123_123
      (fun i => conj_mem_of_fixedPoints _ _ (T123_123 i) (hfix123_123 i) _)
      ⟨123, by decide⟩ ⟨123, by decide⟩ _
      (Q2.validAt ⟨123, by decide⟩ (Q2.listedAt ⟨123, by decide⟩
        (alnCheck_rep ⟨123, by decide⟩ hj hq).1))
      (colE2 ⟨123, by decide⟩ 0 hp) Q2.T123_123_2 Q2.hfix123_123_2 Q2.hinj123_123_2
      Q2.hcardT123_123_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T123_123_2 i) (Q2.hfix123_123_2 i) _)
      colCert_123_123_0.hD ?_).symm
  rw [alnId_123 j hj]


theorem leaf_123_123_1 (hp : 1 < (Q2.transData.getD 123 []).length)
    (j : Nat) (hj : j < (repChars.getD 123 []).length)
    (hq : (normIsRep.getD 123 []).getD j false = true) :
    species (Q2.reps (⟨123, by decide⟩ : Fin 148)) (colE2 ⟨123, by decide⟩ 1 hp)
        (rowE2 (⟨123, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨123, by decide⟩ : Fin 148))
        (colE1 ⟨123, by decide⟩ 1 (transLenTr ⟨123, by decide⟩ 1 hp))
        (rowE1 (⟨123, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨123, by decide⟩ : Fin 148) ⟨123, by decide⟩ _
      (validAt ⟨123, by decide⟩ (listedAt ⟨123, by decide⟩ hj))
      (colE1 ⟨123, by decide⟩ 1 (transLenTr ⟨123, by decide⟩ 1 hp)) T123_123
      hfix123_123 hinj123_123 hcardT123_123
      (fun i => conj_mem_of_fixedPoints _ _ (T123_123 i) (hfix123_123 i) _)
      ⟨123, by decide⟩ ⟨123, by decide⟩ _
      (Q2.validAt ⟨123, by decide⟩ (Q2.listedAt ⟨123, by decide⟩
        (alnCheck_rep ⟨123, by decide⟩ hj hq).1))
      (colE2 ⟨123, by decide⟩ 1 hp) Q2.T123_123_2 Q2.hfix123_123_2 Q2.hinj123_123_2
      Q2.hcardT123_123_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T123_123_2 i) (Q2.hfix123_123_2 i) _)
      colCert_123_123_1.hD ?_).symm
  rw [alnId_123 j hj]


theorem leaf_123_123_2 (hp : 2 < (Q2.transData.getD 123 []).length)
    (j : Nat) (hj : j < (repChars.getD 123 []).length)
    (hq : (normIsRep.getD 123 []).getD j false = true) :
    species (Q2.reps (⟨123, by decide⟩ : Fin 148)) (colE2 ⟨123, by decide⟩ 2 hp)
        (rowE2 (⟨123, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨123, by decide⟩ : Fin 148))
        (colE1 ⟨123, by decide⟩ 2 (transLenTr ⟨123, by decide⟩ 2 hp))
        (rowE1 (⟨123, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨123, by decide⟩ : Fin 148) ⟨123, by decide⟩ _
      (validAt ⟨123, by decide⟩ (listedAt ⟨123, by decide⟩ hj))
      (colE1 ⟨123, by decide⟩ 2 (transLenTr ⟨123, by decide⟩ 2 hp)) T123_123
      hfix123_123 hinj123_123 hcardT123_123
      (fun i => conj_mem_of_fixedPoints _ _ (T123_123 i) (hfix123_123 i) _)
      ⟨123, by decide⟩ ⟨123, by decide⟩ _
      (Q2.validAt ⟨123, by decide⟩ (Q2.listedAt ⟨123, by decide⟩
        (alnCheck_rep ⟨123, by decide⟩ hj hq).1))
      (colE2 ⟨123, by decide⟩ 2 hp) Q2.T123_123_2 Q2.hfix123_123_2 Q2.hinj123_123_2
      Q2.hcardT123_123_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T123_123_2 i) (Q2.hfix123_123_2 i) _)
      colCert_123_123_2.hD ?_).symm
  rw [alnId_123 j hj]


theorem leaf_123_123_3 (hp : 3 < (Q2.transData.getD 123 []).length)
    (j : Nat) (hj : j < (repChars.getD 123 []).length)
    (hq : (normIsRep.getD 123 []).getD j false = true) :
    species (Q2.reps (⟨123, by decide⟩ : Fin 148)) (colE2 ⟨123, by decide⟩ 3 hp)
        (rowE2 (⟨123, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨123, by decide⟩ : Fin 148))
        (colE1 ⟨123, by decide⟩ 3 (transLenTr ⟨123, by decide⟩ 3 hp))
        (rowE1 (⟨123, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨123, by decide⟩ : Fin 148) ⟨123, by decide⟩ _
      (validAt ⟨123, by decide⟩ (listedAt ⟨123, by decide⟩ hj))
      (colE1 ⟨123, by decide⟩ 3 (transLenTr ⟨123, by decide⟩ 3 hp)) T123_123
      hfix123_123 hinj123_123 hcardT123_123
      (fun i => conj_mem_of_fixedPoints _ _ (T123_123 i) (hfix123_123 i) _)
      ⟨123, by decide⟩ ⟨123, by decide⟩ _
      (Q2.validAt ⟨123, by decide⟩ (Q2.listedAt ⟨123, by decide⟩
        (alnCheck_rep ⟨123, by decide⟩ hj hq).1))
      (colE2 ⟨123, by decide⟩ 3 hp) Q2.T123_123_2 Q2.hfix123_123_2 Q2.hinj123_123_2
      Q2.hcardT123_123_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T123_123_2 i) (Q2.hfix123_123_2 i) _)
      colCert_123_123_3.hD ?_).symm
  rw [alnId_123 j hj]


theorem leaf_123_123_4 (hp : 4 < (Q2.transData.getD 123 []).length)
    (j : Nat) (hj : j < (repChars.getD 123 []).length)
    (hq : (normIsRep.getD 123 []).getD j false = true) :
    species (Q2.reps (⟨123, by decide⟩ : Fin 148)) (colE2 ⟨123, by decide⟩ 4 hp)
        (rowE2 (⟨123, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨123, by decide⟩ : Fin 148))
        (colE1 ⟨123, by decide⟩ 4 (transLenTr ⟨123, by decide⟩ 4 hp))
        (rowE1 (⟨123, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨123, by decide⟩ : Fin 148) ⟨123, by decide⟩ _
      (validAt ⟨123, by decide⟩ (listedAt ⟨123, by decide⟩ hj))
      (colE1 ⟨123, by decide⟩ 4 (transLenTr ⟨123, by decide⟩ 4 hp)) T123_123
      hfix123_123 hinj123_123 hcardT123_123
      (fun i => conj_mem_of_fixedPoints _ _ (T123_123 i) (hfix123_123 i) _)
      ⟨123, by decide⟩ ⟨123, by decide⟩ _
      (Q2.validAt ⟨123, by decide⟩ (Q2.listedAt ⟨123, by decide⟩
        (alnCheck_rep ⟨123, by decide⟩ hj hq).1))
      (colE2 ⟨123, by decide⟩ 4 hp) Q2.T123_123_2 Q2.hfix123_123_2 Q2.hinj123_123_2
      Q2.hcardT123_123_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T123_123_2 i) (Q2.hfix123_123_2 i) _)
      colCert_123_123_4.hD ?_).symm
  rw [alnId_123 j hj]


theorem leaf_123_123_5 (hp : 5 < (Q2.transData.getD 123 []).length)
    (j : Nat) (hj : j < (repChars.getD 123 []).length)
    (hq : (normIsRep.getD 123 []).getD j false = true) :
    species (Q2.reps (⟨123, by decide⟩ : Fin 148)) (colE2 ⟨123, by decide⟩ 5 hp)
        (rowE2 (⟨123, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨123, by decide⟩ : Fin 148))
        (colE1 ⟨123, by decide⟩ 5 (transLenTr ⟨123, by decide⟩ 5 hp))
        (rowE1 (⟨123, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨123, by decide⟩ : Fin 148) ⟨123, by decide⟩ _
      (validAt ⟨123, by decide⟩ (listedAt ⟨123, by decide⟩ hj))
      (colE1 ⟨123, by decide⟩ 5 (transLenTr ⟨123, by decide⟩ 5 hp)) T123_123
      hfix123_123 hinj123_123 hcardT123_123
      (fun i => conj_mem_of_fixedPoints _ _ (T123_123 i) (hfix123_123 i) _)
      ⟨123, by decide⟩ ⟨123, by decide⟩ _
      (Q2.validAt ⟨123, by decide⟩ (Q2.listedAt ⟨123, by decide⟩
        (alnCheck_rep ⟨123, by decide⟩ hj hq).1))
      (colE2 ⟨123, by decide⟩ 5 hp) Q2.T123_123_2 Q2.hfix123_123_2 Q2.hinj123_123_2
      Q2.hcardT123_123_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T123_123_2 i) (Q2.hfix123_123_2 i) _)
      colCert_123_123_5.hD ?_).symm
  rw [alnId_123 j hj]


theorem leaf_123_123_6 (hp : 6 < (Q2.transData.getD 123 []).length)
    (j : Nat) (hj : j < (repChars.getD 123 []).length)
    (hq : (normIsRep.getD 123 []).getD j false = true) :
    species (Q2.reps (⟨123, by decide⟩ : Fin 148)) (colE2 ⟨123, by decide⟩ 6 hp)
        (rowE2 (⟨123, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨123, by decide⟩ : Fin 148))
        (colE1 ⟨123, by decide⟩ 6 (transLenTr ⟨123, by decide⟩ 6 hp))
        (rowE1 (⟨123, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨123, by decide⟩ : Fin 148) ⟨123, by decide⟩ _
      (validAt ⟨123, by decide⟩ (listedAt ⟨123, by decide⟩ hj))
      (colE1 ⟨123, by decide⟩ 6 (transLenTr ⟨123, by decide⟩ 6 hp)) T123_123
      hfix123_123 hinj123_123 hcardT123_123
      (fun i => conj_mem_of_fixedPoints _ _ (T123_123 i) (hfix123_123 i) _)
      ⟨123, by decide⟩ ⟨123, by decide⟩ _
      (Q2.validAt ⟨123, by decide⟩ (Q2.listedAt ⟨123, by decide⟩
        (alnCheck_rep ⟨123, by decide⟩ hj hq).1))
      (colE2 ⟨123, by decide⟩ 6 hp) Q2.T123_123_2 Q2.hfix123_123_2 Q2.hinj123_123_2
      Q2.hcardT123_123_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T123_123_2 i) (Q2.hfix123_123_2 i) _)
      colCert_123_123_6.hD ?_).symm
  rw [alnId_123 j hj]


theorem leaf_123_123_7 (hp : 7 < (Q2.transData.getD 123 []).length)
    (j : Nat) (hj : j < (repChars.getD 123 []).length)
    (hq : (normIsRep.getD 123 []).getD j false = true) :
    species (Q2.reps (⟨123, by decide⟩ : Fin 148)) (colE2 ⟨123, by decide⟩ 7 hp)
        (rowE2 (⟨123, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨123, by decide⟩ : Fin 148))
        (colE1 ⟨123, by decide⟩ 7 (transLenTr ⟨123, by decide⟩ 7 hp))
        (rowE1 (⟨123, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨123, by decide⟩ : Fin 148) ⟨123, by decide⟩ _
      (validAt ⟨123, by decide⟩ (listedAt ⟨123, by decide⟩ hj))
      (colE1 ⟨123, by decide⟩ 7 (transLenTr ⟨123, by decide⟩ 7 hp)) T123_123
      hfix123_123 hinj123_123 hcardT123_123
      (fun i => conj_mem_of_fixedPoints _ _ (T123_123 i) (hfix123_123 i) _)
      ⟨123, by decide⟩ ⟨123, by decide⟩ _
      (Q2.validAt ⟨123, by decide⟩ (Q2.listedAt ⟨123, by decide⟩
        (alnCheck_rep ⟨123, by decide⟩ hj hq).1))
      (colE2 ⟨123, by decide⟩ 7 hp) Q2.T123_123_2 Q2.hfix123_123_2 Q2.hinj123_123_2
      Q2.hcardT123_123_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T123_123_2 i) (Q2.hfix123_123_2 i) _)
      colCert_123_123_7.hD ?_).symm
  rw [alnId_123 j hj]


theorem leaf_123_123_8 (hp : 8 < (Q2.transData.getD 123 []).length)
    (j : Nat) (hj : j < (repChars.getD 123 []).length)
    (hq : (normIsRep.getD 123 []).getD j false = true) :
    species (Q2.reps (⟨123, by decide⟩ : Fin 148)) (colE2 ⟨123, by decide⟩ 8 hp)
        (rowE2 (⟨123, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨123, by decide⟩ : Fin 148))
        (colE1 ⟨123, by decide⟩ 8 (transLenTr ⟨123, by decide⟩ 8 hp))
        (rowE1 (⟨123, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨123, by decide⟩ : Fin 148) ⟨123, by decide⟩ _
      (validAt ⟨123, by decide⟩ (listedAt ⟨123, by decide⟩ hj))
      (colE1 ⟨123, by decide⟩ 8 (transLenTr ⟨123, by decide⟩ 8 hp)) T123_123
      hfix123_123 hinj123_123 hcardT123_123
      (fun i => conj_mem_of_fixedPoints _ _ (T123_123 i) (hfix123_123 i) _)
      ⟨123, by decide⟩ ⟨123, by decide⟩ _
      (Q2.validAt ⟨123, by decide⟩ (Q2.listedAt ⟨123, by decide⟩
        (alnCheck_rep ⟨123, by decide⟩ hj hq).1))
      (colE2 ⟨123, by decide⟩ 8 hp) Q2.T123_123_2 Q2.hfix123_123_2 Q2.hinj123_123_2
      Q2.hcardT123_123_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T123_123_2 i) (Q2.hfix123_123_2 i) _)
      colCert_123_123_8.hD ?_).symm
  rw [alnId_123 j hj]


theorem leaf_123_123_9 (hp : 9 < (Q2.transData.getD 123 []).length)
    (j : Nat) (hj : j < (repChars.getD 123 []).length)
    (hq : (normIsRep.getD 123 []).getD j false = true) :
    species (Q2.reps (⟨123, by decide⟩ : Fin 148)) (colE2 ⟨123, by decide⟩ 9 hp)
        (rowE2 (⟨123, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨123, by decide⟩ : Fin 148))
        (colE1 ⟨123, by decide⟩ 9 (transLenTr ⟨123, by decide⟩ 9 hp))
        (rowE1 (⟨123, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨123, by decide⟩ : Fin 148) ⟨123, by decide⟩ _
      (validAt ⟨123, by decide⟩ (listedAt ⟨123, by decide⟩ hj))
      (colE1 ⟨123, by decide⟩ 9 (transLenTr ⟨123, by decide⟩ 9 hp)) T123_123
      hfix123_123 hinj123_123 hcardT123_123
      (fun i => conj_mem_of_fixedPoints _ _ (T123_123 i) (hfix123_123 i) _)
      ⟨123, by decide⟩ ⟨123, by decide⟩ _
      (Q2.validAt ⟨123, by decide⟩ (Q2.listedAt ⟨123, by decide⟩
        (alnCheck_rep ⟨123, by decide⟩ hj hq).1))
      (colE2 ⟨123, by decide⟩ 9 hp) Q2.T123_123_2 Q2.hfix123_123_2 Q2.hinj123_123_2
      Q2.hcardT123_123_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T123_123_2 i) (Q2.hfix123_123_2 i) _)
      colCert_123_123_9.hD ?_).symm
  rw [alnId_123 j hj]


theorem leaf_123_123_10 (hp : 10 < (Q2.transData.getD 123 []).length)
    (j : Nat) (hj : j < (repChars.getD 123 []).length)
    (hq : (normIsRep.getD 123 []).getD j false = true) :
    species (Q2.reps (⟨123, by decide⟩ : Fin 148)) (colE2 ⟨123, by decide⟩ 10 hp)
        (rowE2 (⟨123, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨123, by decide⟩ : Fin 148))
        (colE1 ⟨123, by decide⟩ 10 (transLenTr ⟨123, by decide⟩ 10 hp))
        (rowE1 (⟨123, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨123, by decide⟩ : Fin 148) ⟨123, by decide⟩ _
      (validAt ⟨123, by decide⟩ (listedAt ⟨123, by decide⟩ hj))
      (colE1 ⟨123, by decide⟩ 10 (transLenTr ⟨123, by decide⟩ 10 hp)) T123_123
      hfix123_123 hinj123_123 hcardT123_123
      (fun i => conj_mem_of_fixedPoints _ _ (T123_123 i) (hfix123_123 i) _)
      ⟨123, by decide⟩ ⟨123, by decide⟩ _
      (Q2.validAt ⟨123, by decide⟩ (Q2.listedAt ⟨123, by decide⟩
        (alnCheck_rep ⟨123, by decide⟩ hj hq).1))
      (colE2 ⟨123, by decide⟩ 10 hp) Q2.T123_123_2 Q2.hfix123_123_2 Q2.hinj123_123_2
      Q2.hcardT123_123_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T123_123_2 i) (Q2.hfix123_123_2 i) _)
      colCert_123_123_10.hD ?_).symm
  rw [alnId_123 j hj]


theorem leaf_123_123_11 (hp : 11 < (Q2.transData.getD 123 []).length)
    (j : Nat) (hj : j < (repChars.getD 123 []).length)
    (hq : (normIsRep.getD 123 []).getD j false = true) :
    species (Q2.reps (⟨123, by decide⟩ : Fin 148)) (colE2 ⟨123, by decide⟩ 11 hp)
        (rowE2 (⟨123, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨123, by decide⟩ : Fin 148))
        (colE1 ⟨123, by decide⟩ 11 (transLenTr ⟨123, by decide⟩ 11 hp))
        (rowE1 (⟨123, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨123, by decide⟩ : Fin 148) ⟨123, by decide⟩ _
      (validAt ⟨123, by decide⟩ (listedAt ⟨123, by decide⟩ hj))
      (colE1 ⟨123, by decide⟩ 11 (transLenTr ⟨123, by decide⟩ 11 hp)) T123_123
      hfix123_123 hinj123_123 hcardT123_123
      (fun i => conj_mem_of_fixedPoints _ _ (T123_123 i) (hfix123_123 i) _)
      ⟨123, by decide⟩ ⟨123, by decide⟩ _
      (Q2.validAt ⟨123, by decide⟩ (Q2.listedAt ⟨123, by decide⟩
        (alnCheck_rep ⟨123, by decide⟩ hj hq).1))
      (colE2 ⟨123, by decide⟩ 11 hp) Q2.T123_123_2 Q2.hfix123_123_2 Q2.hinj123_123_2
      Q2.hcardT123_123_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T123_123_2 i) (Q2.hfix123_123_2 i) _)
      colCert_123_123_11.hD ?_).symm
  rw [alnId_123 j hj]


theorem leaf_123_123_12 (hp : 12 < (Q2.transData.getD 123 []).length)
    (j : Nat) (hj : j < (repChars.getD 123 []).length)
    (hq : (normIsRep.getD 123 []).getD j false = true) :
    species (Q2.reps (⟨123, by decide⟩ : Fin 148)) (colE2 ⟨123, by decide⟩ 12 hp)
        (rowE2 (⟨123, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨123, by decide⟩ : Fin 148))
        (colE1 ⟨123, by decide⟩ 12 (transLenTr ⟨123, by decide⟩ 12 hp))
        (rowE1 (⟨123, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨123, by decide⟩ : Fin 148) ⟨123, by decide⟩ _
      (validAt ⟨123, by decide⟩ (listedAt ⟨123, by decide⟩ hj))
      (colE1 ⟨123, by decide⟩ 12 (transLenTr ⟨123, by decide⟩ 12 hp)) T123_123
      hfix123_123 hinj123_123 hcardT123_123
      (fun i => conj_mem_of_fixedPoints _ _ (T123_123 i) (hfix123_123 i) _)
      ⟨123, by decide⟩ ⟨123, by decide⟩ _
      (Q2.validAt ⟨123, by decide⟩ (Q2.listedAt ⟨123, by decide⟩
        (alnCheck_rep ⟨123, by decide⟩ hj hq).1))
      (colE2 ⟨123, by decide⟩ 12 hp) Q2.T123_123_2 Q2.hfix123_123_2 Q2.hinj123_123_2
      Q2.hcardT123_123_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T123_123_2 i) (Q2.hfix123_123_2 i) _)
      colCert_123_123_12.hD ?_).symm
  rw [alnId_123 j hj]


theorem leaf_123_123_13 (hp : 13 < (Q2.transData.getD 123 []).length)
    (j : Nat) (hj : j < (repChars.getD 123 []).length)
    (hq : (normIsRep.getD 123 []).getD j false = true) :
    species (Q2.reps (⟨123, by decide⟩ : Fin 148)) (colE2 ⟨123, by decide⟩ 13 hp)
        (rowE2 (⟨123, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨123, by decide⟩ : Fin 148))
        (colE1 ⟨123, by decide⟩ 13 (transLenTr ⟨123, by decide⟩ 13 hp))
        (rowE1 (⟨123, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨123, by decide⟩ : Fin 148) ⟨123, by decide⟩ _
      (validAt ⟨123, by decide⟩ (listedAt ⟨123, by decide⟩ hj))
      (colE1 ⟨123, by decide⟩ 13 (transLenTr ⟨123, by decide⟩ 13 hp)) T123_123
      hfix123_123 hinj123_123 hcardT123_123
      (fun i => conj_mem_of_fixedPoints _ _ (T123_123 i) (hfix123_123 i) _)
      ⟨123, by decide⟩ ⟨123, by decide⟩ _
      (Q2.validAt ⟨123, by decide⟩ (Q2.listedAt ⟨123, by decide⟩
        (alnCheck_rep ⟨123, by decide⟩ hj hq).1))
      (colE2 ⟨123, by decide⟩ 13 hp) Q2.T123_123_2 Q2.hfix123_123_2 Q2.hinj123_123_2
      Q2.hcardT123_123_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T123_123_2 i) (Q2.hfix123_123_2 i) _)
      colCert_123_123_13.hD ?_).symm
  rw [alnId_123 j hj]


theorem leaf_123_123_14 (hp : 14 < (Q2.transData.getD 123 []).length)
    (j : Nat) (hj : j < (repChars.getD 123 []).length)
    (hq : (normIsRep.getD 123 []).getD j false = true) :
    species (Q2.reps (⟨123, by decide⟩ : Fin 148)) (colE2 ⟨123, by decide⟩ 14 hp)
        (rowE2 (⟨123, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨123, by decide⟩ : Fin 148))
        (colE1 ⟨123, by decide⟩ 14 (transLenTr ⟨123, by decide⟩ 14 hp))
        (rowE1 (⟨123, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨123, by decide⟩ : Fin 148) ⟨123, by decide⟩ _
      (validAt ⟨123, by decide⟩ (listedAt ⟨123, by decide⟩ hj))
      (colE1 ⟨123, by decide⟩ 14 (transLenTr ⟨123, by decide⟩ 14 hp)) T123_123
      hfix123_123 hinj123_123 hcardT123_123
      (fun i => conj_mem_of_fixedPoints _ _ (T123_123 i) (hfix123_123 i) _)
      ⟨123, by decide⟩ ⟨123, by decide⟩ _
      (Q2.validAt ⟨123, by decide⟩ (Q2.listedAt ⟨123, by decide⟩
        (alnCheck_rep ⟨123, by decide⟩ hj hq).1))
      (colE2 ⟨123, by decide⟩ 14 hp) Q2.T123_123_2 Q2.hfix123_123_2 Q2.hinj123_123_2
      Q2.hcardT123_123_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T123_123_2 i) (Q2.hfix123_123_2 i) _)
      colCert_123_123_14.hD ?_).symm
  rw [alnId_123 j hj]


theorem leaf_123_123_15 (hp : 15 < (Q2.transData.getD 123 []).length)
    (j : Nat) (hj : j < (repChars.getD 123 []).length)
    (hq : (normIsRep.getD 123 []).getD j false = true) :
    species (Q2.reps (⟨123, by decide⟩ : Fin 148)) (colE2 ⟨123, by decide⟩ 15 hp)
        (rowE2 (⟨123, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨123, by decide⟩ : Fin 148))
        (colE1 ⟨123, by decide⟩ 15 (transLenTr ⟨123, by decide⟩ 15 hp))
        (rowE1 (⟨123, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨123, by decide⟩ : Fin 148) ⟨123, by decide⟩ _
      (validAt ⟨123, by decide⟩ (listedAt ⟨123, by decide⟩ hj))
      (colE1 ⟨123, by decide⟩ 15 (transLenTr ⟨123, by decide⟩ 15 hp)) T123_123
      hfix123_123 hinj123_123 hcardT123_123
      (fun i => conj_mem_of_fixedPoints _ _ (T123_123 i) (hfix123_123 i) _)
      ⟨123, by decide⟩ ⟨123, by decide⟩ _
      (Q2.validAt ⟨123, by decide⟩ (Q2.listedAt ⟨123, by decide⟩
        (alnCheck_rep ⟨123, by decide⟩ hj hq).1))
      (colE2 ⟨123, by decide⟩ 15 hp) Q2.T123_123_2 Q2.hfix123_123_2 Q2.hinj123_123_2
      Q2.hcardT123_123_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T123_123_2 i) (Q2.hfix123_123_2 i) _)
      colCert_123_123_15.hD ?_).symm
  rw [alnId_123 j hj]


theorem leaf_123_123_16 (hp : 16 < (Q2.transData.getD 123 []).length)
    (j : Nat) (hj : j < (repChars.getD 123 []).length)
    (hq : (normIsRep.getD 123 []).getD j false = true) :
    species (Q2.reps (⟨123, by decide⟩ : Fin 148)) (colE2 ⟨123, by decide⟩ 16 hp)
        (rowE2 (⟨123, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨123, by decide⟩ : Fin 148))
        (colE1 ⟨123, by decide⟩ 16 (transLenTr ⟨123, by decide⟩ 16 hp))
        (rowE1 (⟨123, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨123, by decide⟩ : Fin 148) ⟨123, by decide⟩ _
      (validAt ⟨123, by decide⟩ (listedAt ⟨123, by decide⟩ hj))
      (colE1 ⟨123, by decide⟩ 16 (transLenTr ⟨123, by decide⟩ 16 hp)) T123_123
      hfix123_123 hinj123_123 hcardT123_123
      (fun i => conj_mem_of_fixedPoints _ _ (T123_123 i) (hfix123_123 i) _)
      ⟨123, by decide⟩ ⟨123, by decide⟩ _
      (Q2.validAt ⟨123, by decide⟩ (Q2.listedAt ⟨123, by decide⟩
        (alnCheck_rep ⟨123, by decide⟩ hj hq).1))
      (colE2 ⟨123, by decide⟩ 16 hp) Q2.T123_123_2 Q2.hfix123_123_2 Q2.hinj123_123_2
      Q2.hcardT123_123_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T123_123_2 i) (Q2.hfix123_123_2 i) _)
      colCert_123_123_16.hD ?_).symm
  rw [alnId_123 j hj]


theorem leaf_123_123_17 (hp : 17 < (Q2.transData.getD 123 []).length)
    (j : Nat) (hj : j < (repChars.getD 123 []).length)
    (hq : (normIsRep.getD 123 []).getD j false = true) :
    species (Q2.reps (⟨123, by decide⟩ : Fin 148)) (colE2 ⟨123, by decide⟩ 17 hp)
        (rowE2 (⟨123, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨123, by decide⟩ : Fin 148))
        (colE1 ⟨123, by decide⟩ 17 (transLenTr ⟨123, by decide⟩ 17 hp))
        (rowE1 (⟨123, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨123, by decide⟩ : Fin 148) ⟨123, by decide⟩ _
      (validAt ⟨123, by decide⟩ (listedAt ⟨123, by decide⟩ hj))
      (colE1 ⟨123, by decide⟩ 17 (transLenTr ⟨123, by decide⟩ 17 hp)) T123_123
      hfix123_123 hinj123_123 hcardT123_123
      (fun i => conj_mem_of_fixedPoints _ _ (T123_123 i) (hfix123_123 i) _)
      ⟨123, by decide⟩ ⟨123, by decide⟩ _
      (Q2.validAt ⟨123, by decide⟩ (Q2.listedAt ⟨123, by decide⟩
        (alnCheck_rep ⟨123, by decide⟩ hj hq).1))
      (colE2 ⟨123, by decide⟩ 17 hp) Q2.T123_123_2 Q2.hfix123_123_2 Q2.hinj123_123_2
      Q2.hcardT123_123_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T123_123_2 i) (Q2.hfix123_123_2 i) _)
      colCert_123_123_17.hD ?_).symm
  rw [alnId_123 j hj]


theorem leaf_123_123_18 (hp : 18 < (Q2.transData.getD 123 []).length)
    (j : Nat) (hj : j < (repChars.getD 123 []).length)
    (hq : (normIsRep.getD 123 []).getD j false = true) :
    species (Q2.reps (⟨123, by decide⟩ : Fin 148)) (colE2 ⟨123, by decide⟩ 18 hp)
        (rowE2 (⟨123, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨123, by decide⟩ : Fin 148))
        (colE1 ⟨123, by decide⟩ 18 (transLenTr ⟨123, by decide⟩ 18 hp))
        (rowE1 (⟨123, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨123, by decide⟩ : Fin 148) ⟨123, by decide⟩ _
      (validAt ⟨123, by decide⟩ (listedAt ⟨123, by decide⟩ hj))
      (colE1 ⟨123, by decide⟩ 18 (transLenTr ⟨123, by decide⟩ 18 hp)) T123_123
      hfix123_123 hinj123_123 hcardT123_123
      (fun i => conj_mem_of_fixedPoints _ _ (T123_123 i) (hfix123_123 i) _)
      ⟨123, by decide⟩ ⟨123, by decide⟩ _
      (Q2.validAt ⟨123, by decide⟩ (Q2.listedAt ⟨123, by decide⟩
        (alnCheck_rep ⟨123, by decide⟩ hj hq).1))
      (colE2 ⟨123, by decide⟩ 18 hp) Q2.T123_123_2 Q2.hfix123_123_2 Q2.hinj123_123_2
      Q2.hcardT123_123_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T123_123_2 i) (Q2.hfix123_123_2 i) _)
      colCert_123_123_18.hD ?_).symm
  rw [alnId_123 j hj]


theorem leaf_123_123_19 (hp : 19 < (Q2.transData.getD 123 []).length)
    (j : Nat) (hj : j < (repChars.getD 123 []).length)
    (hq : (normIsRep.getD 123 []).getD j false = true) :
    species (Q2.reps (⟨123, by decide⟩ : Fin 148)) (colE2 ⟨123, by decide⟩ 19 hp)
        (rowE2 (⟨123, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨123, by decide⟩ : Fin 148))
        (colE1 ⟨123, by decide⟩ 19 (transLenTr ⟨123, by decide⟩ 19 hp))
        (rowE1 (⟨123, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨123, by decide⟩ : Fin 148) ⟨123, by decide⟩ _
      (validAt ⟨123, by decide⟩ (listedAt ⟨123, by decide⟩ hj))
      (colE1 ⟨123, by decide⟩ 19 (transLenTr ⟨123, by decide⟩ 19 hp)) T123_123
      hfix123_123 hinj123_123 hcardT123_123
      (fun i => conj_mem_of_fixedPoints _ _ (T123_123 i) (hfix123_123 i) _)
      ⟨123, by decide⟩ ⟨123, by decide⟩ _
      (Q2.validAt ⟨123, by decide⟩ (Q2.listedAt ⟨123, by decide⟩
        (alnCheck_rep ⟨123, by decide⟩ hj hq).1))
      (colE2 ⟨123, by decide⟩ 19 hp) Q2.T123_123_2 Q2.hfix123_123_2 Q2.hinj123_123_2
      Q2.hcardT123_123_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T123_123_2 i) (Q2.hfix123_123_2 i) _)
      colCert_123_123_19.hD ?_).symm
  rw [alnId_123 j hj]


theorem leaf_123_123_20 (hp : 20 < (Q2.transData.getD 123 []).length)
    (j : Nat) (hj : j < (repChars.getD 123 []).length)
    (hq : (normIsRep.getD 123 []).getD j false = true) :
    species (Q2.reps (⟨123, by decide⟩ : Fin 148)) (colE2 ⟨123, by decide⟩ 20 hp)
        (rowE2 (⟨123, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨123, by decide⟩ : Fin 148))
        (colE1 ⟨123, by decide⟩ 20 (transLenTr ⟨123, by decide⟩ 20 hp))
        (rowE1 (⟨123, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨123, by decide⟩ : Fin 148) ⟨123, by decide⟩ _
      (validAt ⟨123, by decide⟩ (listedAt ⟨123, by decide⟩ hj))
      (colE1 ⟨123, by decide⟩ 20 (transLenTr ⟨123, by decide⟩ 20 hp)) T123_123
      hfix123_123 hinj123_123 hcardT123_123
      (fun i => conj_mem_of_fixedPoints _ _ (T123_123 i) (hfix123_123 i) _)
      ⟨123, by decide⟩ ⟨123, by decide⟩ _
      (Q2.validAt ⟨123, by decide⟩ (Q2.listedAt ⟨123, by decide⟩
        (alnCheck_rep ⟨123, by decide⟩ hj hq).1))
      (colE2 ⟨123, by decide⟩ 20 hp) Q2.T123_123_2 Q2.hfix123_123_2 Q2.hinj123_123_2
      Q2.hcardT123_123_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T123_123_2 i) (Q2.hfix123_123_2 i) _)
      colCert_123_123_20.hD ?_).symm
  rw [alnId_123 j hj]


theorem leaf_123_123_21 (hp : 21 < (Q2.transData.getD 123 []).length)
    (j : Nat) (hj : j < (repChars.getD 123 []).length)
    (hq : (normIsRep.getD 123 []).getD j false = true) :
    species (Q2.reps (⟨123, by decide⟩ : Fin 148)) (colE2 ⟨123, by decide⟩ 21 hp)
        (rowE2 (⟨123, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨123, by decide⟩ : Fin 148))
        (colE1 ⟨123, by decide⟩ 21 (transLenTr ⟨123, by decide⟩ 21 hp))
        (rowE1 (⟨123, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨123, by decide⟩ : Fin 148) ⟨123, by decide⟩ _
      (validAt ⟨123, by decide⟩ (listedAt ⟨123, by decide⟩ hj))
      (colE1 ⟨123, by decide⟩ 21 (transLenTr ⟨123, by decide⟩ 21 hp)) T123_123
      hfix123_123 hinj123_123 hcardT123_123
      (fun i => conj_mem_of_fixedPoints _ _ (T123_123 i) (hfix123_123 i) _)
      ⟨123, by decide⟩ ⟨123, by decide⟩ _
      (Q2.validAt ⟨123, by decide⟩ (Q2.listedAt ⟨123, by decide⟩
        (alnCheck_rep ⟨123, by decide⟩ hj hq).1))
      (colE2 ⟨123, by decide⟩ 21 hp) Q2.T123_123_2 Q2.hfix123_123_2 Q2.hinj123_123_2
      Q2.hcardT123_123_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T123_123_2 i) (Q2.hfix123_123_2 i) _)
      colCert_123_123_21.hD ?_).symm
  rw [alnId_123 j hj]


theorem leaf_123_123_22 (hp : 22 < (Q2.transData.getD 123 []).length)
    (j : Nat) (hj : j < (repChars.getD 123 []).length)
    (hq : (normIsRep.getD 123 []).getD j false = true) :
    species (Q2.reps (⟨123, by decide⟩ : Fin 148)) (colE2 ⟨123, by decide⟩ 22 hp)
        (rowE2 (⟨123, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨123, by decide⟩ : Fin 148))
        (colE1 ⟨123, by decide⟩ 22 (transLenTr ⟨123, by decide⟩ 22 hp))
        (rowE1 (⟨123, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨123, by decide⟩ : Fin 148) ⟨123, by decide⟩ _
      (validAt ⟨123, by decide⟩ (listedAt ⟨123, by decide⟩ hj))
      (colE1 ⟨123, by decide⟩ 22 (transLenTr ⟨123, by decide⟩ 22 hp)) T123_123
      hfix123_123 hinj123_123 hcardT123_123
      (fun i => conj_mem_of_fixedPoints _ _ (T123_123 i) (hfix123_123 i) _)
      ⟨123, by decide⟩ ⟨123, by decide⟩ _
      (Q2.validAt ⟨123, by decide⟩ (Q2.listedAt ⟨123, by decide⟩
        (alnCheck_rep ⟨123, by decide⟩ hj hq).1))
      (colE2 ⟨123, by decide⟩ 22 hp) Q2.T123_123_2 Q2.hfix123_123_2 Q2.hinj123_123_2
      Q2.hcardT123_123_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T123_123_2 i) (Q2.hfix123_123_2 i) _)
      colCert_123_123_22.hD ?_).symm
  rw [alnId_123 j hj]


theorem leaf_123_123_23 (hp : 23 < (Q2.transData.getD 123 []).length)
    (j : Nat) (hj : j < (repChars.getD 123 []).length)
    (hq : (normIsRep.getD 123 []).getD j false = true) :
    species (Q2.reps (⟨123, by decide⟩ : Fin 148)) (colE2 ⟨123, by decide⟩ 23 hp)
        (rowE2 (⟨123, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨123, by decide⟩ : Fin 148))
        (colE1 ⟨123, by decide⟩ 23 (transLenTr ⟨123, by decide⟩ 23 hp))
        (rowE1 (⟨123, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨123, by decide⟩ : Fin 148) ⟨123, by decide⟩ _
      (validAt ⟨123, by decide⟩ (listedAt ⟨123, by decide⟩ hj))
      (colE1 ⟨123, by decide⟩ 23 (transLenTr ⟨123, by decide⟩ 23 hp)) T123_123
      hfix123_123 hinj123_123 hcardT123_123
      (fun i => conj_mem_of_fixedPoints _ _ (T123_123 i) (hfix123_123 i) _)
      ⟨123, by decide⟩ ⟨123, by decide⟩ _
      (Q2.validAt ⟨123, by decide⟩ (Q2.listedAt ⟨123, by decide⟩
        (alnCheck_rep ⟨123, by decide⟩ hj hq).1))
      (colE2 ⟨123, by decide⟩ 23 hp) Q2.T123_123_2 Q2.hfix123_123_2 Q2.hinj123_123_2
      Q2.hcardT123_123_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T123_123_2 i) (Q2.hfix123_123_2 i) _)
      colCert_123_123_23.hD ?_).symm
  rw [alnId_123 j hj]


theorem leaf_123_123_24 (hp : 24 < (Q2.transData.getD 123 []).length)
    (j : Nat) (hj : j < (repChars.getD 123 []).length)
    (hq : (normIsRep.getD 123 []).getD j false = true) :
    species (Q2.reps (⟨123, by decide⟩ : Fin 148)) (colE2 ⟨123, by decide⟩ 24 hp)
        (rowE2 (⟨123, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨123, by decide⟩ : Fin 148))
        (colE1 ⟨123, by decide⟩ 24 (transLenTr ⟨123, by decide⟩ 24 hp))
        (rowE1 (⟨123, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨123, by decide⟩ : Fin 148) ⟨123, by decide⟩ _
      (validAt ⟨123, by decide⟩ (listedAt ⟨123, by decide⟩ hj))
      (colE1 ⟨123, by decide⟩ 24 (transLenTr ⟨123, by decide⟩ 24 hp)) T123_123
      hfix123_123 hinj123_123 hcardT123_123
      (fun i => conj_mem_of_fixedPoints _ _ (T123_123 i) (hfix123_123 i) _)
      ⟨123, by decide⟩ ⟨123, by decide⟩ _
      (Q2.validAt ⟨123, by decide⟩ (Q2.listedAt ⟨123, by decide⟩
        (alnCheck_rep ⟨123, by decide⟩ hj hq).1))
      (colE2 ⟨123, by decide⟩ 24 hp) Q2.T123_123_2 Q2.hfix123_123_2 Q2.hinj123_123_2
      Q2.hcardT123_123_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T123_123_2 i) (Q2.hfix123_123_2 i) _)
      colCert_123_123_24.hD ?_).symm
  rw [alnId_123 j hj]


theorem leaf_124_2_0 (hp : 0 < (Q2.transData.getD 2 []).length)
    (j : Nat) (hj : j < (repChars.getD 124 []).length)
    (hq : (normIsRep.getD 124 []).getD j false = true) :
    species (Q2.reps (⟨2, by decide⟩ : Fin 148)) (colE2 ⟨2, by decide⟩ 0 hp)
        (rowE2 (⟨124, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨2, by decide⟩ : Fin 148))
        (colE1 ⟨2, by decide⟩ 0 (transLenTr ⟨2, by decide⟩ 0 hp))
        (rowE1 (⟨124, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨124, by decide⟩ : Fin 148) ⟨2, by decide⟩ _
      (validAt ⟨124, by decide⟩ (listedAt ⟨124, by decide⟩ hj))
      (colE1 ⟨2, by decide⟩ 0 (transLenTr ⟨2, by decide⟩ 0 hp)) T124_2
      hfix124_2 hinj124_2 hcardT124_2
      (fun i => conj_mem_of_fixedPoints _ _ (T124_2 i) (hfix124_2 i) _)
      ⟨124, by decide⟩ ⟨2, by decide⟩ _
      (Q2.validAt ⟨124, by decide⟩ (Q2.listedAt ⟨124, by decide⟩
        (alnCheck_rep ⟨124, by decide⟩ hj hq).1))
      (colE2 ⟨2, by decide⟩ 0 hp) Q2.T124_2_2 Q2.hfix124_2_2 Q2.hinj124_2_2
      Q2.hcardT124_2_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T124_2_2 i) (Q2.hfix124_2_2 i) _)
      colCert_124_2_0.hD ?_).symm
  rw [alnId_124 j hj]


theorem leaf_124_2_1 (hp : 1 < (Q2.transData.getD 2 []).length)
    (j : Nat) (hj : j < (repChars.getD 124 []).length)
    (hq : (normIsRep.getD 124 []).getD j false = true) :
    species (Q2.reps (⟨2, by decide⟩ : Fin 148)) (colE2 ⟨2, by decide⟩ 1 hp)
        (rowE2 (⟨124, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨2, by decide⟩ : Fin 148))
        (colE1 ⟨2, by decide⟩ 1 (transLenTr ⟨2, by decide⟩ 1 hp))
        (rowE1 (⟨124, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨124, by decide⟩ : Fin 148) ⟨2, by decide⟩ _
      (validAt ⟨124, by decide⟩ (listedAt ⟨124, by decide⟩ hj))
      (colE1 ⟨2, by decide⟩ 1 (transLenTr ⟨2, by decide⟩ 1 hp)) T124_2
      hfix124_2 hinj124_2 hcardT124_2
      (fun i => conj_mem_of_fixedPoints _ _ (T124_2 i) (hfix124_2 i) _)
      ⟨124, by decide⟩ ⟨2, by decide⟩ _
      (Q2.validAt ⟨124, by decide⟩ (Q2.listedAt ⟨124, by decide⟩
        (alnCheck_rep ⟨124, by decide⟩ hj hq).1))
      (colE2 ⟨2, by decide⟩ 1 hp) Q2.T124_2_2 Q2.hfix124_2_2 Q2.hinj124_2_2
      Q2.hcardT124_2_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T124_2_2 i) (Q2.hfix124_2_2 i) _)
      ?_).symm
  rw [show colData1 (⟨124, by decide⟩ : Fin 148)
        ((colE1 ⟨2, by decide⟩ 1 (transLenTr ⟨2, by decide⟩ 1 hp) : ↥(reps ⟨2, by decide⟩)) : Coordinate 1)
        T124_2 = colFn colCertDiv_124_2_1.D1 (m := 5) from colCertDiv_124_2_1.bind1,
    show colData2 (⟨124, by decide⟩ : Fin 148)
        ((colE2 ⟨2, by decide⟩ 1 hp : ↥(Q2.reps ⟨2, by decide⟩)) : Coordinate 2)
        Q2.T124_2_2 = colFn colCertDiv_124_2_1.D2 (m := 5) from colCertDiv_124_2_1.bind2]
  rw [alnId_124 j hj]
  exact fastcode_of_div ⟨124, by decide⟩ _ _ _
    ((alnId_124 j hj) ▸ Q2.listedAt (⟨124, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨124, by decide⟩ : Fin 148) hj hq).1) colCertDiv_124_2_1_match


theorem leaf_124_2_2 (hp : 2 < (Q2.transData.getD 2 []).length)
    (j : Nat) (hj : j < (repChars.getD 124 []).length)
    (hq : (normIsRep.getD 124 []).getD j false = true) :
    species (Q2.reps (⟨2, by decide⟩ : Fin 148)) (colE2 ⟨2, by decide⟩ 2 hp)
        (rowE2 (⟨124, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨2, by decide⟩ : Fin 148))
        (colE1 ⟨2, by decide⟩ 2 (transLenTr ⟨2, by decide⟩ 2 hp))
        (rowE1 (⟨124, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨124, by decide⟩ : Fin 148) ⟨2, by decide⟩ _
      (validAt ⟨124, by decide⟩ (listedAt ⟨124, by decide⟩ hj))
      (colE1 ⟨2, by decide⟩ 2 (transLenTr ⟨2, by decide⟩ 2 hp)) T124_2
      hfix124_2 hinj124_2 hcardT124_2
      (fun i => conj_mem_of_fixedPoints _ _ (T124_2 i) (hfix124_2 i) _)
      ⟨124, by decide⟩ ⟨2, by decide⟩ _
      (Q2.validAt ⟨124, by decide⟩ (Q2.listedAt ⟨124, by decide⟩
        (alnCheck_rep ⟨124, by decide⟩ hj hq).1))
      (colE2 ⟨2, by decide⟩ 2 hp) Q2.T124_2_2 Q2.hfix124_2_2 Q2.hinj124_2_2
      Q2.hcardT124_2_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T124_2_2 i) (Q2.hfix124_2_2 i) _)
      ?_).symm
  rw [show colData1 (⟨124, by decide⟩ : Fin 148)
        ((colE1 ⟨2, by decide⟩ 2 (transLenTr ⟨2, by decide⟩ 2 hp) : ↥(reps ⟨2, by decide⟩)) : Coordinate 1)
        T124_2 = colFn colCertDiv_124_2_2.D1 (m := 5) from colCertDiv_124_2_2.bind1,
    show colData2 (⟨124, by decide⟩ : Fin 148)
        ((colE2 ⟨2, by decide⟩ 2 hp : ↥(Q2.reps ⟨2, by decide⟩)) : Coordinate 2)
        Q2.T124_2_2 = colFn colCertDiv_124_2_2.D2 (m := 5) from colCertDiv_124_2_2.bind2]
  rw [alnId_124 j hj]
  exact fastcode_of_div ⟨124, by decide⟩ _ _ _
    ((alnId_124 j hj) ▸ Q2.listedAt (⟨124, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨124, by decide⟩ : Fin 148) hj hq).1) colCertDiv_124_2_2_match


theorem leaf_124_2_3 (hp : 3 < (Q2.transData.getD 2 []).length)
    (j : Nat) (hj : j < (repChars.getD 124 []).length)
    (hq : (normIsRep.getD 124 []).getD j false = true) :
    species (Q2.reps (⟨2, by decide⟩ : Fin 148)) (colE2 ⟨2, by decide⟩ 3 hp)
        (rowE2 (⟨124, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨2, by decide⟩ : Fin 148))
        (colE1 ⟨2, by decide⟩ 3 (transLenTr ⟨2, by decide⟩ 3 hp))
        (rowE1 (⟨124, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨124, by decide⟩ : Fin 148) ⟨2, by decide⟩ _
      (validAt ⟨124, by decide⟩ (listedAt ⟨124, by decide⟩ hj))
      (colE1 ⟨2, by decide⟩ 3 (transLenTr ⟨2, by decide⟩ 3 hp)) T124_2
      hfix124_2 hinj124_2 hcardT124_2
      (fun i => conj_mem_of_fixedPoints _ _ (T124_2 i) (hfix124_2 i) _)
      ⟨124, by decide⟩ ⟨2, by decide⟩ _
      (Q2.validAt ⟨124, by decide⟩ (Q2.listedAt ⟨124, by decide⟩
        (alnCheck_rep ⟨124, by decide⟩ hj hq).1))
      (colE2 ⟨2, by decide⟩ 3 hp) Q2.T124_2_2 Q2.hfix124_2_2 Q2.hinj124_2_2
      Q2.hcardT124_2_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T124_2_2 i) (Q2.hfix124_2_2 i) _)
      ?_).symm
  rw [show colData1 (⟨124, by decide⟩ : Fin 148)
        ((colE1 ⟨2, by decide⟩ 3 (transLenTr ⟨2, by decide⟩ 3 hp) : ↥(reps ⟨2, by decide⟩)) : Coordinate 1)
        T124_2 = colFn colCertDiv_124_2_3.D1 (m := 5) from colCertDiv_124_2_3.bind1,
    show colData2 (⟨124, by decide⟩ : Fin 148)
        ((colE2 ⟨2, by decide⟩ 3 hp : ↥(Q2.reps ⟨2, by decide⟩)) : Coordinate 2)
        Q2.T124_2_2 = colFn colCertDiv_124_2_3.D2 (m := 5) from colCertDiv_124_2_3.bind2]
  rw [alnId_124 j hj]
  exact fastcode_of_div ⟨124, by decide⟩ _ _ _
    ((alnId_124 j hj) ▸ Q2.listedAt (⟨124, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨124, by decide⟩ : Fin 148) hj hq).1) colCertDiv_124_2_3_match


theorem leaf_124_2_4 (hp : 4 < (Q2.transData.getD 2 []).length)
    (j : Nat) (hj : j < (repChars.getD 124 []).length)
    (hq : (normIsRep.getD 124 []).getD j false = true) :
    species (Q2.reps (⟨2, by decide⟩ : Fin 148)) (colE2 ⟨2, by decide⟩ 4 hp)
        (rowE2 (⟨124, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨2, by decide⟩ : Fin 148))
        (colE1 ⟨2, by decide⟩ 4 (transLenTr ⟨2, by decide⟩ 4 hp))
        (rowE1 (⟨124, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨124, by decide⟩ : Fin 148) ⟨2, by decide⟩ _
      (validAt ⟨124, by decide⟩ (listedAt ⟨124, by decide⟩ hj))
      (colE1 ⟨2, by decide⟩ 4 (transLenTr ⟨2, by decide⟩ 4 hp)) T124_2
      hfix124_2 hinj124_2 hcardT124_2
      (fun i => conj_mem_of_fixedPoints _ _ (T124_2 i) (hfix124_2 i) _)
      ⟨124, by decide⟩ ⟨2, by decide⟩ _
      (Q2.validAt ⟨124, by decide⟩ (Q2.listedAt ⟨124, by decide⟩
        (alnCheck_rep ⟨124, by decide⟩ hj hq).1))
      (colE2 ⟨2, by decide⟩ 4 hp) Q2.T124_2_2 Q2.hfix124_2_2 Q2.hinj124_2_2
      Q2.hcardT124_2_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T124_2_2 i) (Q2.hfix124_2_2 i) _)
      ?_).symm
  rw [show colData1 (⟨124, by decide⟩ : Fin 148)
        ((colE1 ⟨2, by decide⟩ 4 (transLenTr ⟨2, by decide⟩ 4 hp) : ↥(reps ⟨2, by decide⟩)) : Coordinate 1)
        T124_2 = colFn colCertDiv_124_2_4.D1 (m := 5) from colCertDiv_124_2_4.bind1,
    show colData2 (⟨124, by decide⟩ : Fin 148)
        ((colE2 ⟨2, by decide⟩ 4 hp : ↥(Q2.reps ⟨2, by decide⟩)) : Coordinate 2)
        Q2.T124_2_2 = colFn colCertDiv_124_2_4.D2 (m := 5) from colCertDiv_124_2_4.bind2]
  rw [alnId_124 j hj]
  exact fastcode_of_div ⟨124, by decide⟩ _ _ _
    ((alnId_124 j hj) ▸ Q2.listedAt (⟨124, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨124, by decide⟩ : Fin 148) hj hq).1) colCertDiv_124_2_4_match


theorem leaf_124_10_0 (hp : 0 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 124 []).length)
    (hq : (normIsRep.getD 124 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 0 hp)
        (rowE2 (⟨124, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 0 (transLenTr ⟨10, by decide⟩ 0 hp))
        (rowE1 (⟨124, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨124, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨124, by decide⟩ (listedAt ⟨124, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 0 (transLenTr ⟨10, by decide⟩ 0 hp)) T124_10
      hfix124_10 hinj124_10 hcardT124_10
      (fun i => conj_mem_of_fixedPoints _ _ (T124_10 i) (hfix124_10 i) _)
      ⟨124, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨124, by decide⟩ (Q2.listedAt ⟨124, by decide⟩
        (alnCheck_rep ⟨124, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 0 hp) Q2.T124_10_2 Q2.hfix124_10_2 Q2.hinj124_10_2
      Q2.hcardT124_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T124_10_2 i) (Q2.hfix124_10_2 i) _)
      colCert_124_10_0.hD ?_).symm
  rw [alnId_124 j hj]


theorem leaf_124_10_1 (hp : 1 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 124 []).length)
    (hq : (normIsRep.getD 124 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 1 hp)
        (rowE2 (⟨124, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 1 (transLenTr ⟨10, by decide⟩ 1 hp))
        (rowE1 (⟨124, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨124, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨124, by decide⟩ (listedAt ⟨124, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 1 (transLenTr ⟨10, by decide⟩ 1 hp)) T124_10
      hfix124_10 hinj124_10 hcardT124_10
      (fun i => conj_mem_of_fixedPoints _ _ (T124_10 i) (hfix124_10 i) _)
      ⟨124, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨124, by decide⟩ (Q2.listedAt ⟨124, by decide⟩
        (alnCheck_rep ⟨124, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 1 hp) Q2.T124_10_2 Q2.hfix124_10_2 Q2.hinj124_10_2
      Q2.hcardT124_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T124_10_2 i) (Q2.hfix124_10_2 i) _)
      colCert_124_10_1.hD ?_).symm
  rw [alnId_124 j hj]


theorem leaf_124_10_2 (hp : 2 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 124 []).length)
    (hq : (normIsRep.getD 124 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 2 hp)
        (rowE2 (⟨124, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 2 (transLenTr ⟨10, by decide⟩ 2 hp))
        (rowE1 (⟨124, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨124, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨124, by decide⟩ (listedAt ⟨124, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 2 (transLenTr ⟨10, by decide⟩ 2 hp)) T124_10
      hfix124_10 hinj124_10 hcardT124_10
      (fun i => conj_mem_of_fixedPoints _ _ (T124_10 i) (hfix124_10 i) _)
      ⟨124, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨124, by decide⟩ (Q2.listedAt ⟨124, by decide⟩
        (alnCheck_rep ⟨124, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 2 hp) Q2.T124_10_2 Q2.hfix124_10_2 Q2.hinj124_10_2
      Q2.hcardT124_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T124_10_2 i) (Q2.hfix124_10_2 i) _)
      colCert_124_10_2.hD ?_).symm
  rw [alnId_124 j hj]


theorem leaf_124_10_3 (hp : 3 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 124 []).length)
    (hq : (normIsRep.getD 124 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 3 hp)
        (rowE2 (⟨124, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 3 (transLenTr ⟨10, by decide⟩ 3 hp))
        (rowE1 (⟨124, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨124, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨124, by decide⟩ (listedAt ⟨124, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 3 (transLenTr ⟨10, by decide⟩ 3 hp)) T124_10
      hfix124_10 hinj124_10 hcardT124_10
      (fun i => conj_mem_of_fixedPoints _ _ (T124_10 i) (hfix124_10 i) _)
      ⟨124, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨124, by decide⟩ (Q2.listedAt ⟨124, by decide⟩
        (alnCheck_rep ⟨124, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 3 hp) Q2.T124_10_2 Q2.hfix124_10_2 Q2.hinj124_10_2
      Q2.hcardT124_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T124_10_2 i) (Q2.hfix124_10_2 i) _)
      colCert_124_10_3.hD ?_).symm
  rw [alnId_124 j hj]


theorem leaf_124_10_4 (hp : 4 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 124 []).length)
    (hq : (normIsRep.getD 124 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 4 hp)
        (rowE2 (⟨124, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 4 (transLenTr ⟨10, by decide⟩ 4 hp))
        (rowE1 (⟨124, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨124, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨124, by decide⟩ (listedAt ⟨124, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 4 (transLenTr ⟨10, by decide⟩ 4 hp)) T124_10
      hfix124_10 hinj124_10 hcardT124_10
      (fun i => conj_mem_of_fixedPoints _ _ (T124_10 i) (hfix124_10 i) _)
      ⟨124, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨124, by decide⟩ (Q2.listedAt ⟨124, by decide⟩
        (alnCheck_rep ⟨124, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 4 hp) Q2.T124_10_2 Q2.hfix124_10_2 Q2.hinj124_10_2
      Q2.hcardT124_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T124_10_2 i) (Q2.hfix124_10_2 i) _)
      colCert_124_10_4.hD ?_).symm
  rw [alnId_124 j hj]


theorem leaf_124_12_0 (hp : 0 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 124 []).length)
    (hq : (normIsRep.getD 124 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 0 hp)
        (rowE2 (⟨124, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp))
        (rowE1 (⟨124, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨124, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨124, by decide⟩ (listedAt ⟨124, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp)) T124_12
      hfix124_12 hinj124_12 hcardT124_12
      (fun i => conj_mem_of_fixedPoints _ _ (T124_12 i) (hfix124_12 i) _)
      ⟨124, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨124, by decide⟩ (Q2.listedAt ⟨124, by decide⟩
        (alnCheck_rep ⟨124, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 0 hp) Q2.T124_12_2 Q2.hfix124_12_2 Q2.hinj124_12_2
      Q2.hcardT124_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T124_12_2 i) (Q2.hfix124_12_2 i) _)
      colCert_124_12_0.hD ?_).symm
  rw [alnId_124 j hj]


theorem leaf_124_12_1 (hp : 1 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 124 []).length)
    (hq : (normIsRep.getD 124 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 1 hp)
        (rowE2 (⟨124, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp))
        (rowE1 (⟨124, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨124, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨124, by decide⟩ (listedAt ⟨124, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp)) T124_12
      hfix124_12 hinj124_12 hcardT124_12
      (fun i => conj_mem_of_fixedPoints _ _ (T124_12 i) (hfix124_12 i) _)
      ⟨124, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨124, by decide⟩ (Q2.listedAt ⟨124, by decide⟩
        (alnCheck_rep ⟨124, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 1 hp) Q2.T124_12_2 Q2.hfix124_12_2 Q2.hinj124_12_2
      Q2.hcardT124_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T124_12_2 i) (Q2.hfix124_12_2 i) _)
      colCert_124_12_1.hD ?_).symm
  rw [alnId_124 j hj]


theorem leaf_124_12_2 (hp : 2 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 124 []).length)
    (hq : (normIsRep.getD 124 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 2 hp)
        (rowE2 (⟨124, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp))
        (rowE1 (⟨124, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨124, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨124, by decide⟩ (listedAt ⟨124, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp)) T124_12
      hfix124_12 hinj124_12 hcardT124_12
      (fun i => conj_mem_of_fixedPoints _ _ (T124_12 i) (hfix124_12 i) _)
      ⟨124, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨124, by decide⟩ (Q2.listedAt ⟨124, by decide⟩
        (alnCheck_rep ⟨124, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 2 hp) Q2.T124_12_2 Q2.hfix124_12_2 Q2.hinj124_12_2
      Q2.hcardT124_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T124_12_2 i) (Q2.hfix124_12_2 i) _)
      colCert_124_12_2.hD ?_).symm
  rw [alnId_124 j hj]


theorem leaf_124_12_3 (hp : 3 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 124 []).length)
    (hq : (normIsRep.getD 124 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 3 hp)
        (rowE2 (⟨124, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp))
        (rowE1 (⟨124, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨124, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨124, by decide⟩ (listedAt ⟨124, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp)) T124_12
      hfix124_12 hinj124_12 hcardT124_12
      (fun i => conj_mem_of_fixedPoints _ _ (T124_12 i) (hfix124_12 i) _)
      ⟨124, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨124, by decide⟩ (Q2.listedAt ⟨124, by decide⟩
        (alnCheck_rep ⟨124, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 3 hp) Q2.T124_12_2 Q2.hfix124_12_2 Q2.hinj124_12_2
      Q2.hcardT124_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T124_12_2 i) (Q2.hfix124_12_2 i) _)
      colCert_124_12_3.hD ?_).symm
  rw [alnId_124 j hj]


theorem leaf_124_12_4 (hp : 4 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 124 []).length)
    (hq : (normIsRep.getD 124 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 4 hp)
        (rowE2 (⟨124, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp))
        (rowE1 (⟨124, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨124, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨124, by decide⟩ (listedAt ⟨124, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp)) T124_12
      hfix124_12 hinj124_12 hcardT124_12
      (fun i => conj_mem_of_fixedPoints _ _ (T124_12 i) (hfix124_12 i) _)
      ⟨124, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨124, by decide⟩ (Q2.listedAt ⟨124, by decide⟩
        (alnCheck_rep ⟨124, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 4 hp) Q2.T124_12_2 Q2.hfix124_12_2 Q2.hinj124_12_2
      Q2.hcardT124_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T124_12_2 i) (Q2.hfix124_12_2 i) _)
      colCert_124_12_4.hD ?_).symm
  rw [alnId_124 j hj]


theorem leaf_124_20_0 (hp : 0 < (Q2.transData.getD 20 []).length)
    (j : Nat) (hj : j < (repChars.getD 124 []).length)
    (hq : (normIsRep.getD 124 []).getD j false = true) :
    species (Q2.reps (⟨20, by decide⟩ : Fin 148)) (colE2 ⟨20, by decide⟩ 0 hp)
        (rowE2 (⟨124, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨20, by decide⟩ : Fin 148))
        (colE1 ⟨20, by decide⟩ 0 (transLenTr ⟨20, by decide⟩ 0 hp))
        (rowE1 (⟨124, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨124, by decide⟩ : Fin 148) ⟨20, by decide⟩ _
      (validAt ⟨124, by decide⟩ (listedAt ⟨124, by decide⟩ hj))
      (colE1 ⟨20, by decide⟩ 0 (transLenTr ⟨20, by decide⟩ 0 hp)) T124_20
      hfix124_20 hinj124_20 hcardT124_20
      (fun i => conj_mem_of_fixedPoints _ _ (T124_20 i) (hfix124_20 i) _)
      ⟨124, by decide⟩ ⟨20, by decide⟩ _
      (Q2.validAt ⟨124, by decide⟩ (Q2.listedAt ⟨124, by decide⟩
        (alnCheck_rep ⟨124, by decide⟩ hj hq).1))
      (colE2 ⟨20, by decide⟩ 0 hp) Q2.T124_20_2 Q2.hfix124_20_2 Q2.hinj124_20_2
      Q2.hcardT124_20_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T124_20_2 i) (Q2.hfix124_20_2 i) _)
      colCert_124_20_0.hD ?_).symm
  rw [alnId_124 j hj]


theorem leaf_124_20_1 (hp : 1 < (Q2.transData.getD 20 []).length)
    (j : Nat) (hj : j < (repChars.getD 124 []).length)
    (hq : (normIsRep.getD 124 []).getD j false = true) :
    species (Q2.reps (⟨20, by decide⟩ : Fin 148)) (colE2 ⟨20, by decide⟩ 1 hp)
        (rowE2 (⟨124, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨20, by decide⟩ : Fin 148))
        (colE1 ⟨20, by decide⟩ 1 (transLenTr ⟨20, by decide⟩ 1 hp))
        (rowE1 (⟨124, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨124, by decide⟩ : Fin 148) ⟨20, by decide⟩ _
      (validAt ⟨124, by decide⟩ (listedAt ⟨124, by decide⟩ hj))
      (colE1 ⟨20, by decide⟩ 1 (transLenTr ⟨20, by decide⟩ 1 hp)) T124_20
      hfix124_20 hinj124_20 hcardT124_20
      (fun i => conj_mem_of_fixedPoints _ _ (T124_20 i) (hfix124_20 i) _)
      ⟨124, by decide⟩ ⟨20, by decide⟩ _
      (Q2.validAt ⟨124, by decide⟩ (Q2.listedAt ⟨124, by decide⟩
        (alnCheck_rep ⟨124, by decide⟩ hj hq).1))
      (colE2 ⟨20, by decide⟩ 1 hp) Q2.T124_20_2 Q2.hfix124_20_2 Q2.hinj124_20_2
      Q2.hcardT124_20_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T124_20_2 i) (Q2.hfix124_20_2 i) _)
      colCert_124_20_1.hD ?_).symm
  rw [alnId_124 j hj]


theorem leaf_124_20_2 (hp : 2 < (Q2.transData.getD 20 []).length)
    (j : Nat) (hj : j < (repChars.getD 124 []).length)
    (hq : (normIsRep.getD 124 []).getD j false = true) :
    species (Q2.reps (⟨20, by decide⟩ : Fin 148)) (colE2 ⟨20, by decide⟩ 2 hp)
        (rowE2 (⟨124, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨20, by decide⟩ : Fin 148))
        (colE1 ⟨20, by decide⟩ 2 (transLenTr ⟨20, by decide⟩ 2 hp))
        (rowE1 (⟨124, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨124, by decide⟩ : Fin 148) ⟨20, by decide⟩ _
      (validAt ⟨124, by decide⟩ (listedAt ⟨124, by decide⟩ hj))
      (colE1 ⟨20, by decide⟩ 2 (transLenTr ⟨20, by decide⟩ 2 hp)) T124_20
      hfix124_20 hinj124_20 hcardT124_20
      (fun i => conj_mem_of_fixedPoints _ _ (T124_20 i) (hfix124_20 i) _)
      ⟨124, by decide⟩ ⟨20, by decide⟩ _
      (Q2.validAt ⟨124, by decide⟩ (Q2.listedAt ⟨124, by decide⟩
        (alnCheck_rep ⟨124, by decide⟩ hj hq).1))
      (colE2 ⟨20, by decide⟩ 2 hp) Q2.T124_20_2 Q2.hfix124_20_2 Q2.hinj124_20_2
      Q2.hcardT124_20_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T124_20_2 i) (Q2.hfix124_20_2 i) _)
      colCert_124_20_2.hD ?_).symm
  rw [alnId_124 j hj]


theorem leaf_124_20_3 (hp : 3 < (Q2.transData.getD 20 []).length)
    (j : Nat) (hj : j < (repChars.getD 124 []).length)
    (hq : (normIsRep.getD 124 []).getD j false = true) :
    species (Q2.reps (⟨20, by decide⟩ : Fin 148)) (colE2 ⟨20, by decide⟩ 3 hp)
        (rowE2 (⟨124, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨20, by decide⟩ : Fin 148))
        (colE1 ⟨20, by decide⟩ 3 (transLenTr ⟨20, by decide⟩ 3 hp))
        (rowE1 (⟨124, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨124, by decide⟩ : Fin 148) ⟨20, by decide⟩ _
      (validAt ⟨124, by decide⟩ (listedAt ⟨124, by decide⟩ hj))
      (colE1 ⟨20, by decide⟩ 3 (transLenTr ⟨20, by decide⟩ 3 hp)) T124_20
      hfix124_20 hinj124_20 hcardT124_20
      (fun i => conj_mem_of_fixedPoints _ _ (T124_20 i) (hfix124_20 i) _)
      ⟨124, by decide⟩ ⟨20, by decide⟩ _
      (Q2.validAt ⟨124, by decide⟩ (Q2.listedAt ⟨124, by decide⟩
        (alnCheck_rep ⟨124, by decide⟩ hj hq).1))
      (colE2 ⟨20, by decide⟩ 3 hp) Q2.T124_20_2 Q2.hfix124_20_2 Q2.hinj124_20_2
      Q2.hcardT124_20_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T124_20_2 i) (Q2.hfix124_20_2 i) _)
      colCert_124_20_3.hD ?_).symm
  rw [alnId_124 j hj]


theorem leaf_124_20_4 (hp : 4 < (Q2.transData.getD 20 []).length)
    (j : Nat) (hj : j < (repChars.getD 124 []).length)
    (hq : (normIsRep.getD 124 []).getD j false = true) :
    species (Q2.reps (⟨20, by decide⟩ : Fin 148)) (colE2 ⟨20, by decide⟩ 4 hp)
        (rowE2 (⟨124, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨20, by decide⟩ : Fin 148))
        (colE1 ⟨20, by decide⟩ 4 (transLenTr ⟨20, by decide⟩ 4 hp))
        (rowE1 (⟨124, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨124, by decide⟩ : Fin 148) ⟨20, by decide⟩ _
      (validAt ⟨124, by decide⟩ (listedAt ⟨124, by decide⟩ hj))
      (colE1 ⟨20, by decide⟩ 4 (transLenTr ⟨20, by decide⟩ 4 hp)) T124_20
      hfix124_20 hinj124_20 hcardT124_20
      (fun i => conj_mem_of_fixedPoints _ _ (T124_20 i) (hfix124_20 i) _)
      ⟨124, by decide⟩ ⟨20, by decide⟩ _
      (Q2.validAt ⟨124, by decide⟩ (Q2.listedAt ⟨124, by decide⟩
        (alnCheck_rep ⟨124, by decide⟩ hj hq).1))
      (colE2 ⟨20, by decide⟩ 4 hp) Q2.T124_20_2 Q2.hfix124_20_2 Q2.hinj124_20_2
      Q2.hcardT124_20_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T124_20_2 i) (Q2.hfix124_20_2 i) _)
      colCert_124_20_4.hD ?_).symm
  rw [alnId_124 j hj]


theorem leaf_124_20_5 (hp : 5 < (Q2.transData.getD 20 []).length)
    (j : Nat) (hj : j < (repChars.getD 124 []).length)
    (hq : (normIsRep.getD 124 []).getD j false = true) :
    species (Q2.reps (⟨20, by decide⟩ : Fin 148)) (colE2 ⟨20, by decide⟩ 5 hp)
        (rowE2 (⟨124, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨20, by decide⟩ : Fin 148))
        (colE1 ⟨20, by decide⟩ 5 (transLenTr ⟨20, by decide⟩ 5 hp))
        (rowE1 (⟨124, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨124, by decide⟩ : Fin 148) ⟨20, by decide⟩ _
      (validAt ⟨124, by decide⟩ (listedAt ⟨124, by decide⟩ hj))
      (colE1 ⟨20, by decide⟩ 5 (transLenTr ⟨20, by decide⟩ 5 hp)) T124_20
      hfix124_20 hinj124_20 hcardT124_20
      (fun i => conj_mem_of_fixedPoints _ _ (T124_20 i) (hfix124_20 i) _)
      ⟨124, by decide⟩ ⟨20, by decide⟩ _
      (Q2.validAt ⟨124, by decide⟩ (Q2.listedAt ⟨124, by decide⟩
        (alnCheck_rep ⟨124, by decide⟩ hj hq).1))
      (colE2 ⟨20, by decide⟩ 5 hp) Q2.T124_20_2 Q2.hfix124_20_2 Q2.hinj124_20_2
      Q2.hcardT124_20_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T124_20_2 i) (Q2.hfix124_20_2 i) _)
      ?_).symm
  rw [show colData1 (⟨124, by decide⟩ : Fin 148)
        ((colE1 ⟨20, by decide⟩ 5 (transLenTr ⟨20, by decide⟩ 5 hp) : ↥(reps ⟨20, by decide⟩)) : Coordinate 1)
        T124_20 = colFn colCertDiv_124_20_5.D1 (m := 5) from colCertDiv_124_20_5.bind1,
    show colData2 (⟨124, by decide⟩ : Fin 148)
        ((colE2 ⟨20, by decide⟩ 5 hp : ↥(Q2.reps ⟨20, by decide⟩)) : Coordinate 2)
        Q2.T124_20_2 = colFn colCertDiv_124_20_5.D2 (m := 5) from colCertDiv_124_20_5.bind2]
  rw [alnId_124 j hj]
  exact fastcode_of_div ⟨124, by decide⟩ _ _ _
    ((alnId_124 j hj) ▸ Q2.listedAt (⟨124, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨124, by decide⟩ : Fin 148) hj hq).1) colCertDiv_124_20_5_match


theorem leaf_124_20_10 (hp : 10 < (Q2.transData.getD 20 []).length)
    (j : Nat) (hj : j < (repChars.getD 124 []).length)
    (hq : (normIsRep.getD 124 []).getD j false = true) :
    species (Q2.reps (⟨20, by decide⟩ : Fin 148)) (colE2 ⟨20, by decide⟩ 10 hp)
        (rowE2 (⟨124, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨20, by decide⟩ : Fin 148))
        (colE1 ⟨20, by decide⟩ 10 (transLenTr ⟨20, by decide⟩ 10 hp))
        (rowE1 (⟨124, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨124, by decide⟩ : Fin 148) ⟨20, by decide⟩ _
      (validAt ⟨124, by decide⟩ (listedAt ⟨124, by decide⟩ hj))
      (colE1 ⟨20, by decide⟩ 10 (transLenTr ⟨20, by decide⟩ 10 hp)) T124_20
      hfix124_20 hinj124_20 hcardT124_20
      (fun i => conj_mem_of_fixedPoints _ _ (T124_20 i) (hfix124_20 i) _)
      ⟨124, by decide⟩ ⟨20, by decide⟩ _
      (Q2.validAt ⟨124, by decide⟩ (Q2.listedAt ⟨124, by decide⟩
        (alnCheck_rep ⟨124, by decide⟩ hj hq).1))
      (colE2 ⟨20, by decide⟩ 10 hp) Q2.T124_20_2 Q2.hfix124_20_2 Q2.hinj124_20_2
      Q2.hcardT124_20_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T124_20_2 i) (Q2.hfix124_20_2 i) _)
      ?_).symm
  rw [show colData1 (⟨124, by decide⟩ : Fin 148)
        ((colE1 ⟨20, by decide⟩ 10 (transLenTr ⟨20, by decide⟩ 10 hp) : ↥(reps ⟨20, by decide⟩)) : Coordinate 1)
        T124_20 = colFn colCertDiv_124_20_10.D1 (m := 5) from colCertDiv_124_20_10.bind1,
    show colData2 (⟨124, by decide⟩ : Fin 148)
        ((colE2 ⟨20, by decide⟩ 10 hp : ↥(Q2.reps ⟨20, by decide⟩)) : Coordinate 2)
        Q2.T124_20_2 = colFn colCertDiv_124_20_10.D2 (m := 5) from colCertDiv_124_20_10.bind2]
  rw [alnId_124 j hj]
  exact fastcode_of_div ⟨124, by decide⟩ _ _ _
    ((alnId_124 j hj) ▸ Q2.listedAt (⟨124, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨124, by decide⟩ : Fin 148) hj hq).1) colCertDiv_124_20_10_match


theorem leaf_124_20_15 (hp : 15 < (Q2.transData.getD 20 []).length)
    (j : Nat) (hj : j < (repChars.getD 124 []).length)
    (hq : (normIsRep.getD 124 []).getD j false = true) :
    species (Q2.reps (⟨20, by decide⟩ : Fin 148)) (colE2 ⟨20, by decide⟩ 15 hp)
        (rowE2 (⟨124, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨20, by decide⟩ : Fin 148))
        (colE1 ⟨20, by decide⟩ 15 (transLenTr ⟨20, by decide⟩ 15 hp))
        (rowE1 (⟨124, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨124, by decide⟩ : Fin 148) ⟨20, by decide⟩ _
      (validAt ⟨124, by decide⟩ (listedAt ⟨124, by decide⟩ hj))
      (colE1 ⟨20, by decide⟩ 15 (transLenTr ⟨20, by decide⟩ 15 hp)) T124_20
      hfix124_20 hinj124_20 hcardT124_20
      (fun i => conj_mem_of_fixedPoints _ _ (T124_20 i) (hfix124_20 i) _)
      ⟨124, by decide⟩ ⟨20, by decide⟩ _
      (Q2.validAt ⟨124, by decide⟩ (Q2.listedAt ⟨124, by decide⟩
        (alnCheck_rep ⟨124, by decide⟩ hj hq).1))
      (colE2 ⟨20, by decide⟩ 15 hp) Q2.T124_20_2 Q2.hfix124_20_2 Q2.hinj124_20_2
      Q2.hcardT124_20_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T124_20_2 i) (Q2.hfix124_20_2 i) _)
      ?_).symm
  rw [show colData1 (⟨124, by decide⟩ : Fin 148)
        ((colE1 ⟨20, by decide⟩ 15 (transLenTr ⟨20, by decide⟩ 15 hp) : ↥(reps ⟨20, by decide⟩)) : Coordinate 1)
        T124_20 = colFn colCertDiv_124_20_15.D1 (m := 5) from colCertDiv_124_20_15.bind1,
    show colData2 (⟨124, by decide⟩ : Fin 148)
        ((colE2 ⟨20, by decide⟩ 15 hp : ↥(Q2.reps ⟨20, by decide⟩)) : Coordinate 2)
        Q2.T124_20_2 = colFn colCertDiv_124_20_15.D2 (m := 5) from colCertDiv_124_20_15.bind2]
  rw [alnId_124 j hj]
  exact fastcode_of_div ⟨124, by decide⟩ _ _ _
    ((alnId_124 j hj) ▸ Q2.listedAt (⟨124, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨124, by decide⟩ : Fin 148) hj hq).1) colCertDiv_124_20_15_match


theorem leaf_124_20_20 (hp : 20 < (Q2.transData.getD 20 []).length)
    (j : Nat) (hj : j < (repChars.getD 124 []).length)
    (hq : (normIsRep.getD 124 []).getD j false = true) :
    species (Q2.reps (⟨20, by decide⟩ : Fin 148)) (colE2 ⟨20, by decide⟩ 20 hp)
        (rowE2 (⟨124, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨20, by decide⟩ : Fin 148))
        (colE1 ⟨20, by decide⟩ 20 (transLenTr ⟨20, by decide⟩ 20 hp))
        (rowE1 (⟨124, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨124, by decide⟩ : Fin 148) ⟨20, by decide⟩ _
      (validAt ⟨124, by decide⟩ (listedAt ⟨124, by decide⟩ hj))
      (colE1 ⟨20, by decide⟩ 20 (transLenTr ⟨20, by decide⟩ 20 hp)) T124_20
      hfix124_20 hinj124_20 hcardT124_20
      (fun i => conj_mem_of_fixedPoints _ _ (T124_20 i) (hfix124_20 i) _)
      ⟨124, by decide⟩ ⟨20, by decide⟩ _
      (Q2.validAt ⟨124, by decide⟩ (Q2.listedAt ⟨124, by decide⟩
        (alnCheck_rep ⟨124, by decide⟩ hj hq).1))
      (colE2 ⟨20, by decide⟩ 20 hp) Q2.T124_20_2 Q2.hfix124_20_2 Q2.hinj124_20_2
      Q2.hcardT124_20_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T124_20_2 i) (Q2.hfix124_20_2 i) _)
      ?_).symm
  rw [show colData1 (⟨124, by decide⟩ : Fin 148)
        ((colE1 ⟨20, by decide⟩ 20 (transLenTr ⟨20, by decide⟩ 20 hp) : ↥(reps ⟨20, by decide⟩)) : Coordinate 1)
        T124_20 = colFn colCertDiv_124_20_20.D1 (m := 5) from colCertDiv_124_20_20.bind1,
    show colData2 (⟨124, by decide⟩ : Fin 148)
        ((colE2 ⟨20, by decide⟩ 20 hp : ↥(Q2.reps ⟨20, by decide⟩)) : Coordinate 2)
        Q2.T124_20_2 = colFn colCertDiv_124_20_20.D2 (m := 5) from colCertDiv_124_20_20.bind2]
  rw [alnId_124 j hj]
  exact fastcode_of_div ⟨124, by decide⟩ _ _ _
    ((alnId_124 j hj) ▸ Q2.listedAt (⟨124, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨124, by decide⟩ : Fin 148) hj hq).1) colCertDiv_124_20_20_match


theorem leaf_124_30_0 (hp : 0 < (Q2.transData.getD 30 []).length)
    (j : Nat) (hj : j < (repChars.getD 124 []).length)
    (hq : (normIsRep.getD 124 []).getD j false = true) :
    species (Q2.reps (⟨30, by decide⟩ : Fin 148)) (colE2 ⟨30, by decide⟩ 0 hp)
        (rowE2 (⟨124, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨30, by decide⟩ : Fin 148))
        (colE1 ⟨30, by decide⟩ 0 (transLenTr ⟨30, by decide⟩ 0 hp))
        (rowE1 (⟨124, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨124, by decide⟩ : Fin 148) ⟨30, by decide⟩ _
      (validAt ⟨124, by decide⟩ (listedAt ⟨124, by decide⟩ hj))
      (colE1 ⟨30, by decide⟩ 0 (transLenTr ⟨30, by decide⟩ 0 hp)) T124_30
      hfix124_30 hinj124_30 hcardT124_30
      (fun i => conj_mem_of_fixedPoints _ _ (T124_30 i) (hfix124_30 i) _)
      ⟨124, by decide⟩ ⟨30, by decide⟩ _
      (Q2.validAt ⟨124, by decide⟩ (Q2.listedAt ⟨124, by decide⟩
        (alnCheck_rep ⟨124, by decide⟩ hj hq).1))
      (colE2 ⟨30, by decide⟩ 0 hp) Q2.T124_30_2 Q2.hfix124_30_2 Q2.hinj124_30_2
      Q2.hcardT124_30_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T124_30_2 i) (Q2.hfix124_30_2 i) _)
      colCert_124_30_0.hD ?_).symm
  rw [alnId_124 j hj]


theorem leaf_124_30_1 (hp : 1 < (Q2.transData.getD 30 []).length)
    (j : Nat) (hj : j < (repChars.getD 124 []).length)
    (hq : (normIsRep.getD 124 []).getD j false = true) :
    species (Q2.reps (⟨30, by decide⟩ : Fin 148)) (colE2 ⟨30, by decide⟩ 1 hp)
        (rowE2 (⟨124, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨30, by decide⟩ : Fin 148))
        (colE1 ⟨30, by decide⟩ 1 (transLenTr ⟨30, by decide⟩ 1 hp))
        (rowE1 (⟨124, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨124, by decide⟩ : Fin 148) ⟨30, by decide⟩ _
      (validAt ⟨124, by decide⟩ (listedAt ⟨124, by decide⟩ hj))
      (colE1 ⟨30, by decide⟩ 1 (transLenTr ⟨30, by decide⟩ 1 hp)) T124_30
      hfix124_30 hinj124_30 hcardT124_30
      (fun i => conj_mem_of_fixedPoints _ _ (T124_30 i) (hfix124_30 i) _)
      ⟨124, by decide⟩ ⟨30, by decide⟩ _
      (Q2.validAt ⟨124, by decide⟩ (Q2.listedAt ⟨124, by decide⟩
        (alnCheck_rep ⟨124, by decide⟩ hj hq).1))
      (colE2 ⟨30, by decide⟩ 1 hp) Q2.T124_30_2 Q2.hfix124_30_2 Q2.hinj124_30_2
      Q2.hcardT124_30_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T124_30_2 i) (Q2.hfix124_30_2 i) _)
      colCert_124_30_1.hD ?_).symm
  rw [alnId_124 j hj]


theorem leaf_124_30_2 (hp : 2 < (Q2.transData.getD 30 []).length)
    (j : Nat) (hj : j < (repChars.getD 124 []).length)
    (hq : (normIsRep.getD 124 []).getD j false = true) :
    species (Q2.reps (⟨30, by decide⟩ : Fin 148)) (colE2 ⟨30, by decide⟩ 2 hp)
        (rowE2 (⟨124, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨30, by decide⟩ : Fin 148))
        (colE1 ⟨30, by decide⟩ 2 (transLenTr ⟨30, by decide⟩ 2 hp))
        (rowE1 (⟨124, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨124, by decide⟩ : Fin 148) ⟨30, by decide⟩ _
      (validAt ⟨124, by decide⟩ (listedAt ⟨124, by decide⟩ hj))
      (colE1 ⟨30, by decide⟩ 2 (transLenTr ⟨30, by decide⟩ 2 hp)) T124_30
      hfix124_30 hinj124_30 hcardT124_30
      (fun i => conj_mem_of_fixedPoints _ _ (T124_30 i) (hfix124_30 i) _)
      ⟨124, by decide⟩ ⟨30, by decide⟩ _
      (Q2.validAt ⟨124, by decide⟩ (Q2.listedAt ⟨124, by decide⟩
        (alnCheck_rep ⟨124, by decide⟩ hj hq).1))
      (colE2 ⟨30, by decide⟩ 2 hp) Q2.T124_30_2 Q2.hfix124_30_2 Q2.hinj124_30_2
      Q2.hcardT124_30_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T124_30_2 i) (Q2.hfix124_30_2 i) _)
      colCert_124_30_2.hD ?_).symm
  rw [alnId_124 j hj]


theorem leaf_124_30_3 (hp : 3 < (Q2.transData.getD 30 []).length)
    (j : Nat) (hj : j < (repChars.getD 124 []).length)
    (hq : (normIsRep.getD 124 []).getD j false = true) :
    species (Q2.reps (⟨30, by decide⟩ : Fin 148)) (colE2 ⟨30, by decide⟩ 3 hp)
        (rowE2 (⟨124, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨30, by decide⟩ : Fin 148))
        (colE1 ⟨30, by decide⟩ 3 (transLenTr ⟨30, by decide⟩ 3 hp))
        (rowE1 (⟨124, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨124, by decide⟩ : Fin 148) ⟨30, by decide⟩ _
      (validAt ⟨124, by decide⟩ (listedAt ⟨124, by decide⟩ hj))
      (colE1 ⟨30, by decide⟩ 3 (transLenTr ⟨30, by decide⟩ 3 hp)) T124_30
      hfix124_30 hinj124_30 hcardT124_30
      (fun i => conj_mem_of_fixedPoints _ _ (T124_30 i) (hfix124_30 i) _)
      ⟨124, by decide⟩ ⟨30, by decide⟩ _
      (Q2.validAt ⟨124, by decide⟩ (Q2.listedAt ⟨124, by decide⟩
        (alnCheck_rep ⟨124, by decide⟩ hj hq).1))
      (colE2 ⟨30, by decide⟩ 3 hp) Q2.T124_30_2 Q2.hfix124_30_2 Q2.hinj124_30_2
      Q2.hcardT124_30_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T124_30_2 i) (Q2.hfix124_30_2 i) _)
      colCert_124_30_3.hD ?_).symm
  rw [alnId_124 j hj]


theorem leaf_124_30_4 (hp : 4 < (Q2.transData.getD 30 []).length)
    (j : Nat) (hj : j < (repChars.getD 124 []).length)
    (hq : (normIsRep.getD 124 []).getD j false = true) :
    species (Q2.reps (⟨30, by decide⟩ : Fin 148)) (colE2 ⟨30, by decide⟩ 4 hp)
        (rowE2 (⟨124, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨30, by decide⟩ : Fin 148))
        (colE1 ⟨30, by decide⟩ 4 (transLenTr ⟨30, by decide⟩ 4 hp))
        (rowE1 (⟨124, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨124, by decide⟩ : Fin 148) ⟨30, by decide⟩ _
      (validAt ⟨124, by decide⟩ (listedAt ⟨124, by decide⟩ hj))
      (colE1 ⟨30, by decide⟩ 4 (transLenTr ⟨30, by decide⟩ 4 hp)) T124_30
      hfix124_30 hinj124_30 hcardT124_30
      (fun i => conj_mem_of_fixedPoints _ _ (T124_30 i) (hfix124_30 i) _)
      ⟨124, by decide⟩ ⟨30, by decide⟩ _
      (Q2.validAt ⟨124, by decide⟩ (Q2.listedAt ⟨124, by decide⟩
        (alnCheck_rep ⟨124, by decide⟩ hj hq).1))
      (colE2 ⟨30, by decide⟩ 4 hp) Q2.T124_30_2 Q2.hfix124_30_2 Q2.hinj124_30_2
      Q2.hcardT124_30_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T124_30_2 i) (Q2.hfix124_30_2 i) _)
      colCert_124_30_4.hD ?_).symm
  rw [alnId_124 j hj]


theorem leaf_124_30_5 (hp : 5 < (Q2.transData.getD 30 []).length)
    (j : Nat) (hj : j < (repChars.getD 124 []).length)
    (hq : (normIsRep.getD 124 []).getD j false = true) :
    species (Q2.reps (⟨30, by decide⟩ : Fin 148)) (colE2 ⟨30, by decide⟩ 5 hp)
        (rowE2 (⟨124, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨30, by decide⟩ : Fin 148))
        (colE1 ⟨30, by decide⟩ 5 (transLenTr ⟨30, by decide⟩ 5 hp))
        (rowE1 (⟨124, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨124, by decide⟩ : Fin 148) ⟨30, by decide⟩ _
      (validAt ⟨124, by decide⟩ (listedAt ⟨124, by decide⟩ hj))
      (colE1 ⟨30, by decide⟩ 5 (transLenTr ⟨30, by decide⟩ 5 hp)) T124_30
      hfix124_30 hinj124_30 hcardT124_30
      (fun i => conj_mem_of_fixedPoints _ _ (T124_30 i) (hfix124_30 i) _)
      ⟨124, by decide⟩ ⟨30, by decide⟩ _
      (Q2.validAt ⟨124, by decide⟩ (Q2.listedAt ⟨124, by decide⟩
        (alnCheck_rep ⟨124, by decide⟩ hj hq).1))
      (colE2 ⟨30, by decide⟩ 5 hp) Q2.T124_30_2 Q2.hfix124_30_2 Q2.hinj124_30_2
      Q2.hcardT124_30_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T124_30_2 i) (Q2.hfix124_30_2 i) _)
      ?_).symm
  rw [show colData1 (⟨124, by decide⟩ : Fin 148)
        ((colE1 ⟨30, by decide⟩ 5 (transLenTr ⟨30, by decide⟩ 5 hp) : ↥(reps ⟨30, by decide⟩)) : Coordinate 1)
        T124_30 = colFn colCertDiv_124_30_5.D1 (m := 5) from colCertDiv_124_30_5.bind1,
    show colData2 (⟨124, by decide⟩ : Fin 148)
        ((colE2 ⟨30, by decide⟩ 5 hp : ↥(Q2.reps ⟨30, by decide⟩)) : Coordinate 2)
        Q2.T124_30_2 = colFn colCertDiv_124_30_5.D2 (m := 5) from colCertDiv_124_30_5.bind2]
  rw [alnId_124 j hj]
  exact fastcode_of_div ⟨124, by decide⟩ _ _ _
    ((alnId_124 j hj) ▸ Q2.listedAt (⟨124, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨124, by decide⟩ : Fin 148) hj hq).1) colCertDiv_124_30_5_match


theorem leaf_124_30_10 (hp : 10 < (Q2.transData.getD 30 []).length)
    (j : Nat) (hj : j < (repChars.getD 124 []).length)
    (hq : (normIsRep.getD 124 []).getD j false = true) :
    species (Q2.reps (⟨30, by decide⟩ : Fin 148)) (colE2 ⟨30, by decide⟩ 10 hp)
        (rowE2 (⟨124, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨30, by decide⟩ : Fin 148))
        (colE1 ⟨30, by decide⟩ 10 (transLenTr ⟨30, by decide⟩ 10 hp))
        (rowE1 (⟨124, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨124, by decide⟩ : Fin 148) ⟨30, by decide⟩ _
      (validAt ⟨124, by decide⟩ (listedAt ⟨124, by decide⟩ hj))
      (colE1 ⟨30, by decide⟩ 10 (transLenTr ⟨30, by decide⟩ 10 hp)) T124_30
      hfix124_30 hinj124_30 hcardT124_30
      (fun i => conj_mem_of_fixedPoints _ _ (T124_30 i) (hfix124_30 i) _)
      ⟨124, by decide⟩ ⟨30, by decide⟩ _
      (Q2.validAt ⟨124, by decide⟩ (Q2.listedAt ⟨124, by decide⟩
        (alnCheck_rep ⟨124, by decide⟩ hj hq).1))
      (colE2 ⟨30, by decide⟩ 10 hp) Q2.T124_30_2 Q2.hfix124_30_2 Q2.hinj124_30_2
      Q2.hcardT124_30_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T124_30_2 i) (Q2.hfix124_30_2 i) _)
      ?_).symm
  rw [show colData1 (⟨124, by decide⟩ : Fin 148)
        ((colE1 ⟨30, by decide⟩ 10 (transLenTr ⟨30, by decide⟩ 10 hp) : ↥(reps ⟨30, by decide⟩)) : Coordinate 1)
        T124_30 = colFn colCertDiv_124_30_10.D1 (m := 5) from colCertDiv_124_30_10.bind1,
    show colData2 (⟨124, by decide⟩ : Fin 148)
        ((colE2 ⟨30, by decide⟩ 10 hp : ↥(Q2.reps ⟨30, by decide⟩)) : Coordinate 2)
        Q2.T124_30_2 = colFn colCertDiv_124_30_10.D2 (m := 5) from colCertDiv_124_30_10.bind2]
  rw [alnId_124 j hj]
  exact fastcode_of_div ⟨124, by decide⟩ _ _ _
    ((alnId_124 j hj) ▸ Q2.listedAt (⟨124, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨124, by decide⟩ : Fin 148) hj hq).1) colCertDiv_124_30_10_match


theorem leaf_124_30_15 (hp : 15 < (Q2.transData.getD 30 []).length)
    (j : Nat) (hj : j < (repChars.getD 124 []).length)
    (hq : (normIsRep.getD 124 []).getD j false = true) :
    species (Q2.reps (⟨30, by decide⟩ : Fin 148)) (colE2 ⟨30, by decide⟩ 15 hp)
        (rowE2 (⟨124, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨30, by decide⟩ : Fin 148))
        (colE1 ⟨30, by decide⟩ 15 (transLenTr ⟨30, by decide⟩ 15 hp))
        (rowE1 (⟨124, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨124, by decide⟩ : Fin 148) ⟨30, by decide⟩ _
      (validAt ⟨124, by decide⟩ (listedAt ⟨124, by decide⟩ hj))
      (colE1 ⟨30, by decide⟩ 15 (transLenTr ⟨30, by decide⟩ 15 hp)) T124_30
      hfix124_30 hinj124_30 hcardT124_30
      (fun i => conj_mem_of_fixedPoints _ _ (T124_30 i) (hfix124_30 i) _)
      ⟨124, by decide⟩ ⟨30, by decide⟩ _
      (Q2.validAt ⟨124, by decide⟩ (Q2.listedAt ⟨124, by decide⟩
        (alnCheck_rep ⟨124, by decide⟩ hj hq).1))
      (colE2 ⟨30, by decide⟩ 15 hp) Q2.T124_30_2 Q2.hfix124_30_2 Q2.hinj124_30_2
      Q2.hcardT124_30_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T124_30_2 i) (Q2.hfix124_30_2 i) _)
      colCert_124_30_15.hD ?_).symm
  rw [alnId_124 j hj]


theorem leaf_124_30_20 (hp : 20 < (Q2.transData.getD 30 []).length)
    (j : Nat) (hj : j < (repChars.getD 124 []).length)
    (hq : (normIsRep.getD 124 []).getD j false = true) :
    species (Q2.reps (⟨30, by decide⟩ : Fin 148)) (colE2 ⟨30, by decide⟩ 20 hp)
        (rowE2 (⟨124, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨30, by decide⟩ : Fin 148))
        (colE1 ⟨30, by decide⟩ 20 (transLenTr ⟨30, by decide⟩ 20 hp))
        (rowE1 (⟨124, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨124, by decide⟩ : Fin 148) ⟨30, by decide⟩ _
      (validAt ⟨124, by decide⟩ (listedAt ⟨124, by decide⟩ hj))
      (colE1 ⟨30, by decide⟩ 20 (transLenTr ⟨30, by decide⟩ 20 hp)) T124_30
      hfix124_30 hinj124_30 hcardT124_30
      (fun i => conj_mem_of_fixedPoints _ _ (T124_30 i) (hfix124_30 i) _)
      ⟨124, by decide⟩ ⟨30, by decide⟩ _
      (Q2.validAt ⟨124, by decide⟩ (Q2.listedAt ⟨124, by decide⟩
        (alnCheck_rep ⟨124, by decide⟩ hj hq).1))
      (colE2 ⟨30, by decide⟩ 20 hp) Q2.T124_30_2 Q2.hfix124_30_2 Q2.hinj124_30_2
      Q2.hcardT124_30_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T124_30_2 i) (Q2.hfix124_30_2 i) _)
      ?_).symm
  rw [show colData1 (⟨124, by decide⟩ : Fin 148)
        ((colE1 ⟨30, by decide⟩ 20 (transLenTr ⟨30, by decide⟩ 20 hp) : ↥(reps ⟨30, by decide⟩)) : Coordinate 1)
        T124_30 = colFn colCertDiv_124_30_20.D1 (m := 5) from colCertDiv_124_30_20.bind1,
    show colData2 (⟨124, by decide⟩ : Fin 148)
        ((colE2 ⟨30, by decide⟩ 20 hp : ↥(Q2.reps ⟨30, by decide⟩)) : Coordinate 2)
        Q2.T124_30_2 = colFn colCertDiv_124_30_20.D2 (m := 5) from colCertDiv_124_30_20.bind2]
  rw [alnId_124 j hj]
  exact fastcode_of_div ⟨124, by decide⟩ _ _ _
    ((alnId_124 j hj) ▸ Q2.listedAt (⟨124, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨124, by decide⟩ : Fin 148) hj hq).1) colCertDiv_124_30_20_match


theorem leaf_124_33_0 (hp : 0 < (Q2.transData.getD 33 []).length)
    (j : Nat) (hj : j < (repChars.getD 124 []).length)
    (hq : (normIsRep.getD 124 []).getD j false = true) :
    species (Q2.reps (⟨33, by decide⟩ : Fin 148)) (colE2 ⟨33, by decide⟩ 0 hp)
        (rowE2 (⟨124, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨33, by decide⟩ : Fin 148))
        (colE1 ⟨33, by decide⟩ 0 (transLenTr ⟨33, by decide⟩ 0 hp))
        (rowE1 (⟨124, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨124, by decide⟩ : Fin 148) ⟨33, by decide⟩ _
      (validAt ⟨124, by decide⟩ (listedAt ⟨124, by decide⟩ hj))
      (colE1 ⟨33, by decide⟩ 0 (transLenTr ⟨33, by decide⟩ 0 hp)) T124_33
      hfix124_33 hinj124_33 hcardT124_33
      (fun i => conj_mem_of_fixedPoints _ _ (T124_33 i) (hfix124_33 i) _)
      ⟨124, by decide⟩ ⟨33, by decide⟩ _
      (Q2.validAt ⟨124, by decide⟩ (Q2.listedAt ⟨124, by decide⟩
        (alnCheck_rep ⟨124, by decide⟩ hj hq).1))
      (colE2 ⟨33, by decide⟩ 0 hp) Q2.T124_33_2 Q2.hfix124_33_2 Q2.hinj124_33_2
      Q2.hcardT124_33_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T124_33_2 i) (Q2.hfix124_33_2 i) _)
      colCert_124_33_0.hD ?_).symm
  rw [alnId_124 j hj]


theorem leaf_124_33_1 (hp : 1 < (Q2.transData.getD 33 []).length)
    (j : Nat) (hj : j < (repChars.getD 124 []).length)
    (hq : (normIsRep.getD 124 []).getD j false = true) :
    species (Q2.reps (⟨33, by decide⟩ : Fin 148)) (colE2 ⟨33, by decide⟩ 1 hp)
        (rowE2 (⟨124, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨33, by decide⟩ : Fin 148))
        (colE1 ⟨33, by decide⟩ 1 (transLenTr ⟨33, by decide⟩ 1 hp))
        (rowE1 (⟨124, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨124, by decide⟩ : Fin 148) ⟨33, by decide⟩ _
      (validAt ⟨124, by decide⟩ (listedAt ⟨124, by decide⟩ hj))
      (colE1 ⟨33, by decide⟩ 1 (transLenTr ⟨33, by decide⟩ 1 hp)) T124_33
      hfix124_33 hinj124_33 hcardT124_33
      (fun i => conj_mem_of_fixedPoints _ _ (T124_33 i) (hfix124_33 i) _)
      ⟨124, by decide⟩ ⟨33, by decide⟩ _
      (Q2.validAt ⟨124, by decide⟩ (Q2.listedAt ⟨124, by decide⟩
        (alnCheck_rep ⟨124, by decide⟩ hj hq).1))
      (colE2 ⟨33, by decide⟩ 1 hp) Q2.T124_33_2 Q2.hfix124_33_2 Q2.hinj124_33_2
      Q2.hcardT124_33_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T124_33_2 i) (Q2.hfix124_33_2 i) _)
      colCert_124_33_1.hD ?_).symm
  rw [alnId_124 j hj]


theorem leaf_124_33_2 (hp : 2 < (Q2.transData.getD 33 []).length)
    (j : Nat) (hj : j < (repChars.getD 124 []).length)
    (hq : (normIsRep.getD 124 []).getD j false = true) :
    species (Q2.reps (⟨33, by decide⟩ : Fin 148)) (colE2 ⟨33, by decide⟩ 2 hp)
        (rowE2 (⟨124, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨33, by decide⟩ : Fin 148))
        (colE1 ⟨33, by decide⟩ 2 (transLenTr ⟨33, by decide⟩ 2 hp))
        (rowE1 (⟨124, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨124, by decide⟩ : Fin 148) ⟨33, by decide⟩ _
      (validAt ⟨124, by decide⟩ (listedAt ⟨124, by decide⟩ hj))
      (colE1 ⟨33, by decide⟩ 2 (transLenTr ⟨33, by decide⟩ 2 hp)) T124_33
      hfix124_33 hinj124_33 hcardT124_33
      (fun i => conj_mem_of_fixedPoints _ _ (T124_33 i) (hfix124_33 i) _)
      ⟨124, by decide⟩ ⟨33, by decide⟩ _
      (Q2.validAt ⟨124, by decide⟩ (Q2.listedAt ⟨124, by decide⟩
        (alnCheck_rep ⟨124, by decide⟩ hj hq).1))
      (colE2 ⟨33, by decide⟩ 2 hp) Q2.T124_33_2 Q2.hfix124_33_2 Q2.hinj124_33_2
      Q2.hcardT124_33_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T124_33_2 i) (Q2.hfix124_33_2 i) _)
      colCert_124_33_2.hD ?_).symm
  rw [alnId_124 j hj]


theorem leaf_124_33_3 (hp : 3 < (Q2.transData.getD 33 []).length)
    (j : Nat) (hj : j < (repChars.getD 124 []).length)
    (hq : (normIsRep.getD 124 []).getD j false = true) :
    species (Q2.reps (⟨33, by decide⟩ : Fin 148)) (colE2 ⟨33, by decide⟩ 3 hp)
        (rowE2 (⟨124, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨33, by decide⟩ : Fin 148))
        (colE1 ⟨33, by decide⟩ 3 (transLenTr ⟨33, by decide⟩ 3 hp))
        (rowE1 (⟨124, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨124, by decide⟩ : Fin 148) ⟨33, by decide⟩ _
      (validAt ⟨124, by decide⟩ (listedAt ⟨124, by decide⟩ hj))
      (colE1 ⟨33, by decide⟩ 3 (transLenTr ⟨33, by decide⟩ 3 hp)) T124_33
      hfix124_33 hinj124_33 hcardT124_33
      (fun i => conj_mem_of_fixedPoints _ _ (T124_33 i) (hfix124_33 i) _)
      ⟨124, by decide⟩ ⟨33, by decide⟩ _
      (Q2.validAt ⟨124, by decide⟩ (Q2.listedAt ⟨124, by decide⟩
        (alnCheck_rep ⟨124, by decide⟩ hj hq).1))
      (colE2 ⟨33, by decide⟩ 3 hp) Q2.T124_33_2 Q2.hfix124_33_2 Q2.hinj124_33_2
      Q2.hcardT124_33_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T124_33_2 i) (Q2.hfix124_33_2 i) _)
      colCert_124_33_3.hD ?_).symm
  rw [alnId_124 j hj]


theorem leaf_124_33_4 (hp : 4 < (Q2.transData.getD 33 []).length)
    (j : Nat) (hj : j < (repChars.getD 124 []).length)
    (hq : (normIsRep.getD 124 []).getD j false = true) :
    species (Q2.reps (⟨33, by decide⟩ : Fin 148)) (colE2 ⟨33, by decide⟩ 4 hp)
        (rowE2 (⟨124, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨33, by decide⟩ : Fin 148))
        (colE1 ⟨33, by decide⟩ 4 (transLenTr ⟨33, by decide⟩ 4 hp))
        (rowE1 (⟨124, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨124, by decide⟩ : Fin 148) ⟨33, by decide⟩ _
      (validAt ⟨124, by decide⟩ (listedAt ⟨124, by decide⟩ hj))
      (colE1 ⟨33, by decide⟩ 4 (transLenTr ⟨33, by decide⟩ 4 hp)) T124_33
      hfix124_33 hinj124_33 hcardT124_33
      (fun i => conj_mem_of_fixedPoints _ _ (T124_33 i) (hfix124_33 i) _)
      ⟨124, by decide⟩ ⟨33, by decide⟩ _
      (Q2.validAt ⟨124, by decide⟩ (Q2.listedAt ⟨124, by decide⟩
        (alnCheck_rep ⟨124, by decide⟩ hj hq).1))
      (colE2 ⟨33, by decide⟩ 4 hp) Q2.T124_33_2 Q2.hfix124_33_2 Q2.hinj124_33_2
      Q2.hcardT124_33_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T124_33_2 i) (Q2.hfix124_33_2 i) _)
      colCert_124_33_4.hD ?_).symm
  rw [alnId_124 j hj]


theorem leaf_124_33_5 (hp : 5 < (Q2.transData.getD 33 []).length)
    (j : Nat) (hj : j < (repChars.getD 124 []).length)
    (hq : (normIsRep.getD 124 []).getD j false = true) :
    species (Q2.reps (⟨33, by decide⟩ : Fin 148)) (colE2 ⟨33, by decide⟩ 5 hp)
        (rowE2 (⟨124, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨33, by decide⟩ : Fin 148))
        (colE1 ⟨33, by decide⟩ 5 (transLenTr ⟨33, by decide⟩ 5 hp))
        (rowE1 (⟨124, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨124, by decide⟩ : Fin 148) ⟨33, by decide⟩ _
      (validAt ⟨124, by decide⟩ (listedAt ⟨124, by decide⟩ hj))
      (colE1 ⟨33, by decide⟩ 5 (transLenTr ⟨33, by decide⟩ 5 hp)) T124_33
      hfix124_33 hinj124_33 hcardT124_33
      (fun i => conj_mem_of_fixedPoints _ _ (T124_33 i) (hfix124_33 i) _)
      ⟨124, by decide⟩ ⟨33, by decide⟩ _
      (Q2.validAt ⟨124, by decide⟩ (Q2.listedAt ⟨124, by decide⟩
        (alnCheck_rep ⟨124, by decide⟩ hj hq).1))
      (colE2 ⟨33, by decide⟩ 5 hp) Q2.T124_33_2 Q2.hfix124_33_2 Q2.hinj124_33_2
      Q2.hcardT124_33_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T124_33_2 i) (Q2.hfix124_33_2 i) _)
      ?_).symm
  rw [show colData1 (⟨124, by decide⟩ : Fin 148)
        ((colE1 ⟨33, by decide⟩ 5 (transLenTr ⟨33, by decide⟩ 5 hp) : ↥(reps ⟨33, by decide⟩)) : Coordinate 1)
        T124_33 = colFn colCertDiv_124_33_5.D1 (m := 5) from colCertDiv_124_33_5.bind1,
    show colData2 (⟨124, by decide⟩ : Fin 148)
        ((colE2 ⟨33, by decide⟩ 5 hp : ↥(Q2.reps ⟨33, by decide⟩)) : Coordinate 2)
        Q2.T124_33_2 = colFn colCertDiv_124_33_5.D2 (m := 5) from colCertDiv_124_33_5.bind2]
  rw [alnId_124 j hj]
  exact fastcode_of_div ⟨124, by decide⟩ _ _ _
    ((alnId_124 j hj) ▸ Q2.listedAt (⟨124, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨124, by decide⟩ : Fin 148) hj hq).1) colCertDiv_124_33_5_match


theorem leaf_124_33_10 (hp : 10 < (Q2.transData.getD 33 []).length)
    (j : Nat) (hj : j < (repChars.getD 124 []).length)
    (hq : (normIsRep.getD 124 []).getD j false = true) :
    species (Q2.reps (⟨33, by decide⟩ : Fin 148)) (colE2 ⟨33, by decide⟩ 10 hp)
        (rowE2 (⟨124, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨33, by decide⟩ : Fin 148))
        (colE1 ⟨33, by decide⟩ 10 (transLenTr ⟨33, by decide⟩ 10 hp))
        (rowE1 (⟨124, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨124, by decide⟩ : Fin 148) ⟨33, by decide⟩ _
      (validAt ⟨124, by decide⟩ (listedAt ⟨124, by decide⟩ hj))
      (colE1 ⟨33, by decide⟩ 10 (transLenTr ⟨33, by decide⟩ 10 hp)) T124_33
      hfix124_33 hinj124_33 hcardT124_33
      (fun i => conj_mem_of_fixedPoints _ _ (T124_33 i) (hfix124_33 i) _)
      ⟨124, by decide⟩ ⟨33, by decide⟩ _
      (Q2.validAt ⟨124, by decide⟩ (Q2.listedAt ⟨124, by decide⟩
        (alnCheck_rep ⟨124, by decide⟩ hj hq).1))
      (colE2 ⟨33, by decide⟩ 10 hp) Q2.T124_33_2 Q2.hfix124_33_2 Q2.hinj124_33_2
      Q2.hcardT124_33_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T124_33_2 i) (Q2.hfix124_33_2 i) _)
      ?_).symm
  rw [show colData1 (⟨124, by decide⟩ : Fin 148)
        ((colE1 ⟨33, by decide⟩ 10 (transLenTr ⟨33, by decide⟩ 10 hp) : ↥(reps ⟨33, by decide⟩)) : Coordinate 1)
        T124_33 = colFn colCertDiv_124_33_10.D1 (m := 5) from colCertDiv_124_33_10.bind1,
    show colData2 (⟨124, by decide⟩ : Fin 148)
        ((colE2 ⟨33, by decide⟩ 10 hp : ↥(Q2.reps ⟨33, by decide⟩)) : Coordinate 2)
        Q2.T124_33_2 = colFn colCertDiv_124_33_10.D2 (m := 5) from colCertDiv_124_33_10.bind2]
  rw [alnId_124 j hj]
  exact fastcode_of_div ⟨124, by decide⟩ _ _ _
    ((alnId_124 j hj) ▸ Q2.listedAt (⟨124, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨124, by decide⟩ : Fin 148) hj hq).1) colCertDiv_124_33_10_match


theorem leaf_124_33_15 (hp : 15 < (Q2.transData.getD 33 []).length)
    (j : Nat) (hj : j < (repChars.getD 124 []).length)
    (hq : (normIsRep.getD 124 []).getD j false = true) :
    species (Q2.reps (⟨33, by decide⟩ : Fin 148)) (colE2 ⟨33, by decide⟩ 15 hp)
        (rowE2 (⟨124, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨33, by decide⟩ : Fin 148))
        (colE1 ⟨33, by decide⟩ 15 (transLenTr ⟨33, by decide⟩ 15 hp))
        (rowE1 (⟨124, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨124, by decide⟩ : Fin 148) ⟨33, by decide⟩ _
      (validAt ⟨124, by decide⟩ (listedAt ⟨124, by decide⟩ hj))
      (colE1 ⟨33, by decide⟩ 15 (transLenTr ⟨33, by decide⟩ 15 hp)) T124_33
      hfix124_33 hinj124_33 hcardT124_33
      (fun i => conj_mem_of_fixedPoints _ _ (T124_33 i) (hfix124_33 i) _)
      ⟨124, by decide⟩ ⟨33, by decide⟩ _
      (Q2.validAt ⟨124, by decide⟩ (Q2.listedAt ⟨124, by decide⟩
        (alnCheck_rep ⟨124, by decide⟩ hj hq).1))
      (colE2 ⟨33, by decide⟩ 15 hp) Q2.T124_33_2 Q2.hfix124_33_2 Q2.hinj124_33_2
      Q2.hcardT124_33_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T124_33_2 i) (Q2.hfix124_33_2 i) _)
      ?_).symm
  rw [show colData1 (⟨124, by decide⟩ : Fin 148)
        ((colE1 ⟨33, by decide⟩ 15 (transLenTr ⟨33, by decide⟩ 15 hp) : ↥(reps ⟨33, by decide⟩)) : Coordinate 1)
        T124_33 = colFn colCertDiv_124_33_15.D1 (m := 5) from colCertDiv_124_33_15.bind1,
    show colData2 (⟨124, by decide⟩ : Fin 148)
        ((colE2 ⟨33, by decide⟩ 15 hp : ↥(Q2.reps ⟨33, by decide⟩)) : Coordinate 2)
        Q2.T124_33_2 = colFn colCertDiv_124_33_15.D2 (m := 5) from colCertDiv_124_33_15.bind2]
  rw [alnId_124 j hj]
  exact fastcode_of_div ⟨124, by decide⟩ _ _ _
    ((alnId_124 j hj) ▸ Q2.listedAt (⟨124, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨124, by decide⟩ : Fin 148) hj hq).1) colCertDiv_124_33_15_match


theorem leaf_124_33_20 (hp : 20 < (Q2.transData.getD 33 []).length)
    (j : Nat) (hj : j < (repChars.getD 124 []).length)
    (hq : (normIsRep.getD 124 []).getD j false = true) :
    species (Q2.reps (⟨33, by decide⟩ : Fin 148)) (colE2 ⟨33, by decide⟩ 20 hp)
        (rowE2 (⟨124, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨33, by decide⟩ : Fin 148))
        (colE1 ⟨33, by decide⟩ 20 (transLenTr ⟨33, by decide⟩ 20 hp))
        (rowE1 (⟨124, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨124, by decide⟩ : Fin 148) ⟨33, by decide⟩ _
      (validAt ⟨124, by decide⟩ (listedAt ⟨124, by decide⟩ hj))
      (colE1 ⟨33, by decide⟩ 20 (transLenTr ⟨33, by decide⟩ 20 hp)) T124_33
      hfix124_33 hinj124_33 hcardT124_33
      (fun i => conj_mem_of_fixedPoints _ _ (T124_33 i) (hfix124_33 i) _)
      ⟨124, by decide⟩ ⟨33, by decide⟩ _
      (Q2.validAt ⟨124, by decide⟩ (Q2.listedAt ⟨124, by decide⟩
        (alnCheck_rep ⟨124, by decide⟩ hj hq).1))
      (colE2 ⟨33, by decide⟩ 20 hp) Q2.T124_33_2 Q2.hfix124_33_2 Q2.hinj124_33_2
      Q2.hcardT124_33_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T124_33_2 i) (Q2.hfix124_33_2 i) _)
      ?_).symm
  rw [show colData1 (⟨124, by decide⟩ : Fin 148)
        ((colE1 ⟨33, by decide⟩ 20 (transLenTr ⟨33, by decide⟩ 20 hp) : ↥(reps ⟨33, by decide⟩)) : Coordinate 1)
        T124_33 = colFn colCertDiv_124_33_20.D1 (m := 5) from colCertDiv_124_33_20.bind1,
    show colData2 (⟨124, by decide⟩ : Fin 148)
        ((colE2 ⟨33, by decide⟩ 20 hp : ↥(Q2.reps ⟨33, by decide⟩)) : Coordinate 2)
        Q2.T124_33_2 = colFn colCertDiv_124_33_20.D2 (m := 5) from colCertDiv_124_33_20.bind2]
  rw [alnId_124 j hj]
  exact fastcode_of_div ⟨124, by decide⟩ _ _ _
    ((alnId_124 j hj) ▸ Q2.listedAt (⟨124, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨124, by decide⟩ : Fin 148) hj hq).1) colCertDiv_124_33_20_match


theorem leaf_124_39_0 (hp : 0 < (Q2.transData.getD 39 []).length)
    (j : Nat) (hj : j < (repChars.getD 124 []).length)
    (hq : (normIsRep.getD 124 []).getD j false = true) :
    species (Q2.reps (⟨39, by decide⟩ : Fin 148)) (colE2 ⟨39, by decide⟩ 0 hp)
        (rowE2 (⟨124, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨39, by decide⟩ : Fin 148))
        (colE1 ⟨39, by decide⟩ 0 (transLenTr ⟨39, by decide⟩ 0 hp))
        (rowE1 (⟨124, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨124, by decide⟩ : Fin 148) ⟨39, by decide⟩ _
      (validAt ⟨124, by decide⟩ (listedAt ⟨124, by decide⟩ hj))
      (colE1 ⟨39, by decide⟩ 0 (transLenTr ⟨39, by decide⟩ 0 hp)) T124_39
      hfix124_39 hinj124_39 hcardT124_39
      (fun i => conj_mem_of_fixedPoints _ _ (T124_39 i) (hfix124_39 i) _)
      ⟨124, by decide⟩ ⟨39, by decide⟩ _
      (Q2.validAt ⟨124, by decide⟩ (Q2.listedAt ⟨124, by decide⟩
        (alnCheck_rep ⟨124, by decide⟩ hj hq).1))
      (colE2 ⟨39, by decide⟩ 0 hp) Q2.T124_39_2 Q2.hfix124_39_2 Q2.hinj124_39_2
      Q2.hcardT124_39_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T124_39_2 i) (Q2.hfix124_39_2 i) _)
      colCert_124_39_0.hD ?_).symm
  rw [alnId_124 j hj]


theorem leaf_124_39_1 (hp : 1 < (Q2.transData.getD 39 []).length)
    (j : Nat) (hj : j < (repChars.getD 124 []).length)
    (hq : (normIsRep.getD 124 []).getD j false = true) :
    species (Q2.reps (⟨39, by decide⟩ : Fin 148)) (colE2 ⟨39, by decide⟩ 1 hp)
        (rowE2 (⟨124, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨39, by decide⟩ : Fin 148))
        (colE1 ⟨39, by decide⟩ 1 (transLenTr ⟨39, by decide⟩ 1 hp))
        (rowE1 (⟨124, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨124, by decide⟩ : Fin 148) ⟨39, by decide⟩ _
      (validAt ⟨124, by decide⟩ (listedAt ⟨124, by decide⟩ hj))
      (colE1 ⟨39, by decide⟩ 1 (transLenTr ⟨39, by decide⟩ 1 hp)) T124_39
      hfix124_39 hinj124_39 hcardT124_39
      (fun i => conj_mem_of_fixedPoints _ _ (T124_39 i) (hfix124_39 i) _)
      ⟨124, by decide⟩ ⟨39, by decide⟩ _
      (Q2.validAt ⟨124, by decide⟩ (Q2.listedAt ⟨124, by decide⟩
        (alnCheck_rep ⟨124, by decide⟩ hj hq).1))
      (colE2 ⟨39, by decide⟩ 1 hp) Q2.T124_39_2 Q2.hfix124_39_2 Q2.hinj124_39_2
      Q2.hcardT124_39_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T124_39_2 i) (Q2.hfix124_39_2 i) _)
      colCert_124_39_1.hD ?_).symm
  rw [alnId_124 j hj]


theorem leaf_124_39_2 (hp : 2 < (Q2.transData.getD 39 []).length)
    (j : Nat) (hj : j < (repChars.getD 124 []).length)
    (hq : (normIsRep.getD 124 []).getD j false = true) :
    species (Q2.reps (⟨39, by decide⟩ : Fin 148)) (colE2 ⟨39, by decide⟩ 2 hp)
        (rowE2 (⟨124, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨39, by decide⟩ : Fin 148))
        (colE1 ⟨39, by decide⟩ 2 (transLenTr ⟨39, by decide⟩ 2 hp))
        (rowE1 (⟨124, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨124, by decide⟩ : Fin 148) ⟨39, by decide⟩ _
      (validAt ⟨124, by decide⟩ (listedAt ⟨124, by decide⟩ hj))
      (colE1 ⟨39, by decide⟩ 2 (transLenTr ⟨39, by decide⟩ 2 hp)) T124_39
      hfix124_39 hinj124_39 hcardT124_39
      (fun i => conj_mem_of_fixedPoints _ _ (T124_39 i) (hfix124_39 i) _)
      ⟨124, by decide⟩ ⟨39, by decide⟩ _
      (Q2.validAt ⟨124, by decide⟩ (Q2.listedAt ⟨124, by decide⟩
        (alnCheck_rep ⟨124, by decide⟩ hj hq).1))
      (colE2 ⟨39, by decide⟩ 2 hp) Q2.T124_39_2 Q2.hfix124_39_2 Q2.hinj124_39_2
      Q2.hcardT124_39_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T124_39_2 i) (Q2.hfix124_39_2 i) _)
      colCert_124_39_2.hD ?_).symm
  rw [alnId_124 j hj]


theorem leaf_124_39_3 (hp : 3 < (Q2.transData.getD 39 []).length)
    (j : Nat) (hj : j < (repChars.getD 124 []).length)
    (hq : (normIsRep.getD 124 []).getD j false = true) :
    species (Q2.reps (⟨39, by decide⟩ : Fin 148)) (colE2 ⟨39, by decide⟩ 3 hp)
        (rowE2 (⟨124, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨39, by decide⟩ : Fin 148))
        (colE1 ⟨39, by decide⟩ 3 (transLenTr ⟨39, by decide⟩ 3 hp))
        (rowE1 (⟨124, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨124, by decide⟩ : Fin 148) ⟨39, by decide⟩ _
      (validAt ⟨124, by decide⟩ (listedAt ⟨124, by decide⟩ hj))
      (colE1 ⟨39, by decide⟩ 3 (transLenTr ⟨39, by decide⟩ 3 hp)) T124_39
      hfix124_39 hinj124_39 hcardT124_39
      (fun i => conj_mem_of_fixedPoints _ _ (T124_39 i) (hfix124_39 i) _)
      ⟨124, by decide⟩ ⟨39, by decide⟩ _
      (Q2.validAt ⟨124, by decide⟩ (Q2.listedAt ⟨124, by decide⟩
        (alnCheck_rep ⟨124, by decide⟩ hj hq).1))
      (colE2 ⟨39, by decide⟩ 3 hp) Q2.T124_39_2 Q2.hfix124_39_2 Q2.hinj124_39_2
      Q2.hcardT124_39_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T124_39_2 i) (Q2.hfix124_39_2 i) _)
      colCert_124_39_3.hD ?_).symm
  rw [alnId_124 j hj]


theorem leaf_124_39_4 (hp : 4 < (Q2.transData.getD 39 []).length)
    (j : Nat) (hj : j < (repChars.getD 124 []).length)
    (hq : (normIsRep.getD 124 []).getD j false = true) :
    species (Q2.reps (⟨39, by decide⟩ : Fin 148)) (colE2 ⟨39, by decide⟩ 4 hp)
        (rowE2 (⟨124, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨39, by decide⟩ : Fin 148))
        (colE1 ⟨39, by decide⟩ 4 (transLenTr ⟨39, by decide⟩ 4 hp))
        (rowE1 (⟨124, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨124, by decide⟩ : Fin 148) ⟨39, by decide⟩ _
      (validAt ⟨124, by decide⟩ (listedAt ⟨124, by decide⟩ hj))
      (colE1 ⟨39, by decide⟩ 4 (transLenTr ⟨39, by decide⟩ 4 hp)) T124_39
      hfix124_39 hinj124_39 hcardT124_39
      (fun i => conj_mem_of_fixedPoints _ _ (T124_39 i) (hfix124_39 i) _)
      ⟨124, by decide⟩ ⟨39, by decide⟩ _
      (Q2.validAt ⟨124, by decide⟩ (Q2.listedAt ⟨124, by decide⟩
        (alnCheck_rep ⟨124, by decide⟩ hj hq).1))
      (colE2 ⟨39, by decide⟩ 4 hp) Q2.T124_39_2 Q2.hfix124_39_2 Q2.hinj124_39_2
      Q2.hcardT124_39_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T124_39_2 i) (Q2.hfix124_39_2 i) _)
      colCert_124_39_4.hD ?_).symm
  rw [alnId_124 j hj]


theorem leaf_124_39_5 (hp : 5 < (Q2.transData.getD 39 []).length)
    (j : Nat) (hj : j < (repChars.getD 124 []).length)
    (hq : (normIsRep.getD 124 []).getD j false = true) :
    species (Q2.reps (⟨39, by decide⟩ : Fin 148)) (colE2 ⟨39, by decide⟩ 5 hp)
        (rowE2 (⟨124, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨39, by decide⟩ : Fin 148))
        (colE1 ⟨39, by decide⟩ 5 (transLenTr ⟨39, by decide⟩ 5 hp))
        (rowE1 (⟨124, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨124, by decide⟩ : Fin 148) ⟨39, by decide⟩ _
      (validAt ⟨124, by decide⟩ (listedAt ⟨124, by decide⟩ hj))
      (colE1 ⟨39, by decide⟩ 5 (transLenTr ⟨39, by decide⟩ 5 hp)) T124_39
      hfix124_39 hinj124_39 hcardT124_39
      (fun i => conj_mem_of_fixedPoints _ _ (T124_39 i) (hfix124_39 i) _)
      ⟨124, by decide⟩ ⟨39, by decide⟩ _
      (Q2.validAt ⟨124, by decide⟩ (Q2.listedAt ⟨124, by decide⟩
        (alnCheck_rep ⟨124, by decide⟩ hj hq).1))
      (colE2 ⟨39, by decide⟩ 5 hp) Q2.T124_39_2 Q2.hfix124_39_2 Q2.hinj124_39_2
      Q2.hcardT124_39_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T124_39_2 i) (Q2.hfix124_39_2 i) _)
      ?_).symm
  rw [show colData1 (⟨124, by decide⟩ : Fin 148)
        ((colE1 ⟨39, by decide⟩ 5 (transLenTr ⟨39, by decide⟩ 5 hp) : ↥(reps ⟨39, by decide⟩)) : Coordinate 1)
        T124_39 = colFn colCertDiv_124_39_5.D1 (m := 5) from colCertDiv_124_39_5.bind1,
    show colData2 (⟨124, by decide⟩ : Fin 148)
        ((colE2 ⟨39, by decide⟩ 5 hp : ↥(Q2.reps ⟨39, by decide⟩)) : Coordinate 2)
        Q2.T124_39_2 = colFn colCertDiv_124_39_5.D2 (m := 5) from colCertDiv_124_39_5.bind2]
  rw [alnId_124 j hj]
  exact fastcode_of_div ⟨124, by decide⟩ _ _ _
    ((alnId_124 j hj) ▸ Q2.listedAt (⟨124, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨124, by decide⟩ : Fin 148) hj hq).1) colCertDiv_124_39_5_match


theorem leaf_124_39_10 (hp : 10 < (Q2.transData.getD 39 []).length)
    (j : Nat) (hj : j < (repChars.getD 124 []).length)
    (hq : (normIsRep.getD 124 []).getD j false = true) :
    species (Q2.reps (⟨39, by decide⟩ : Fin 148)) (colE2 ⟨39, by decide⟩ 10 hp)
        (rowE2 (⟨124, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨39, by decide⟩ : Fin 148))
        (colE1 ⟨39, by decide⟩ 10 (transLenTr ⟨39, by decide⟩ 10 hp))
        (rowE1 (⟨124, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨124, by decide⟩ : Fin 148) ⟨39, by decide⟩ _
      (validAt ⟨124, by decide⟩ (listedAt ⟨124, by decide⟩ hj))
      (colE1 ⟨39, by decide⟩ 10 (transLenTr ⟨39, by decide⟩ 10 hp)) T124_39
      hfix124_39 hinj124_39 hcardT124_39
      (fun i => conj_mem_of_fixedPoints _ _ (T124_39 i) (hfix124_39 i) _)
      ⟨124, by decide⟩ ⟨39, by decide⟩ _
      (Q2.validAt ⟨124, by decide⟩ (Q2.listedAt ⟨124, by decide⟩
        (alnCheck_rep ⟨124, by decide⟩ hj hq).1))
      (colE2 ⟨39, by decide⟩ 10 hp) Q2.T124_39_2 Q2.hfix124_39_2 Q2.hinj124_39_2
      Q2.hcardT124_39_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T124_39_2 i) (Q2.hfix124_39_2 i) _)
      ?_).symm
  rw [show colData1 (⟨124, by decide⟩ : Fin 148)
        ((colE1 ⟨39, by decide⟩ 10 (transLenTr ⟨39, by decide⟩ 10 hp) : ↥(reps ⟨39, by decide⟩)) : Coordinate 1)
        T124_39 = colFn colCertDiv_124_39_10.D1 (m := 5) from colCertDiv_124_39_10.bind1,
    show colData2 (⟨124, by decide⟩ : Fin 148)
        ((colE2 ⟨39, by decide⟩ 10 hp : ↥(Q2.reps ⟨39, by decide⟩)) : Coordinate 2)
        Q2.T124_39_2 = colFn colCertDiv_124_39_10.D2 (m := 5) from colCertDiv_124_39_10.bind2]
  rw [alnId_124 j hj]
  exact fastcode_of_div ⟨124, by decide⟩ _ _ _
    ((alnId_124 j hj) ▸ Q2.listedAt (⟨124, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨124, by decide⟩ : Fin 148) hj hq).1) colCertDiv_124_39_10_match


theorem leaf_124_39_15 (hp : 15 < (Q2.transData.getD 39 []).length)
    (j : Nat) (hj : j < (repChars.getD 124 []).length)
    (hq : (normIsRep.getD 124 []).getD j false = true) :
    species (Q2.reps (⟨39, by decide⟩ : Fin 148)) (colE2 ⟨39, by decide⟩ 15 hp)
        (rowE2 (⟨124, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨39, by decide⟩ : Fin 148))
        (colE1 ⟨39, by decide⟩ 15 (transLenTr ⟨39, by decide⟩ 15 hp))
        (rowE1 (⟨124, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨124, by decide⟩ : Fin 148) ⟨39, by decide⟩ _
      (validAt ⟨124, by decide⟩ (listedAt ⟨124, by decide⟩ hj))
      (colE1 ⟨39, by decide⟩ 15 (transLenTr ⟨39, by decide⟩ 15 hp)) T124_39
      hfix124_39 hinj124_39 hcardT124_39
      (fun i => conj_mem_of_fixedPoints _ _ (T124_39 i) (hfix124_39 i) _)
      ⟨124, by decide⟩ ⟨39, by decide⟩ _
      (Q2.validAt ⟨124, by decide⟩ (Q2.listedAt ⟨124, by decide⟩
        (alnCheck_rep ⟨124, by decide⟩ hj hq).1))
      (colE2 ⟨39, by decide⟩ 15 hp) Q2.T124_39_2 Q2.hfix124_39_2 Q2.hinj124_39_2
      Q2.hcardT124_39_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T124_39_2 i) (Q2.hfix124_39_2 i) _)
      ?_).symm
  rw [show colData1 (⟨124, by decide⟩ : Fin 148)
        ((colE1 ⟨39, by decide⟩ 15 (transLenTr ⟨39, by decide⟩ 15 hp) : ↥(reps ⟨39, by decide⟩)) : Coordinate 1)
        T124_39 = colFn colCertDiv_124_39_15.D1 (m := 5) from colCertDiv_124_39_15.bind1,
    show colData2 (⟨124, by decide⟩ : Fin 148)
        ((colE2 ⟨39, by decide⟩ 15 hp : ↥(Q2.reps ⟨39, by decide⟩)) : Coordinate 2)
        Q2.T124_39_2 = colFn colCertDiv_124_39_15.D2 (m := 5) from colCertDiv_124_39_15.bind2]
  rw [alnId_124 j hj]
  exact fastcode_of_div ⟨124, by decide⟩ _ _ _
    ((alnId_124 j hj) ▸ Q2.listedAt (⟨124, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨124, by decide⟩ : Fin 148) hj hq).1) colCertDiv_124_39_15_match


theorem leaf_124_39_20 (hp : 20 < (Q2.transData.getD 39 []).length)
    (j : Nat) (hj : j < (repChars.getD 124 []).length)
    (hq : (normIsRep.getD 124 []).getD j false = true) :
    species (Q2.reps (⟨39, by decide⟩ : Fin 148)) (colE2 ⟨39, by decide⟩ 20 hp)
        (rowE2 (⟨124, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨39, by decide⟩ : Fin 148))
        (colE1 ⟨39, by decide⟩ 20 (transLenTr ⟨39, by decide⟩ 20 hp))
        (rowE1 (⟨124, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨124, by decide⟩ : Fin 148) ⟨39, by decide⟩ _
      (validAt ⟨124, by decide⟩ (listedAt ⟨124, by decide⟩ hj))
      (colE1 ⟨39, by decide⟩ 20 (transLenTr ⟨39, by decide⟩ 20 hp)) T124_39
      hfix124_39 hinj124_39 hcardT124_39
      (fun i => conj_mem_of_fixedPoints _ _ (T124_39 i) (hfix124_39 i) _)
      ⟨124, by decide⟩ ⟨39, by decide⟩ _
      (Q2.validAt ⟨124, by decide⟩ (Q2.listedAt ⟨124, by decide⟩
        (alnCheck_rep ⟨124, by decide⟩ hj hq).1))
      (colE2 ⟨39, by decide⟩ 20 hp) Q2.T124_39_2 Q2.hfix124_39_2 Q2.hinj124_39_2
      Q2.hcardT124_39_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T124_39_2 i) (Q2.hfix124_39_2 i) _)
      ?_).symm
  rw [show colData1 (⟨124, by decide⟩ : Fin 148)
        ((colE1 ⟨39, by decide⟩ 20 (transLenTr ⟨39, by decide⟩ 20 hp) : ↥(reps ⟨39, by decide⟩)) : Coordinate 1)
        T124_39 = colFn colCertDiv_124_39_20.D1 (m := 5) from colCertDiv_124_39_20.bind1,
    show colData2 (⟨124, by decide⟩ : Fin 148)
        ((colE2 ⟨39, by decide⟩ 20 hp : ↥(Q2.reps ⟨39, by decide⟩)) : Coordinate 2)
        Q2.T124_39_2 = colFn colCertDiv_124_39_20.D2 (m := 5) from colCertDiv_124_39_20.bind2]
  rw [alnId_124 j hj]
  exact fastcode_of_div ⟨124, by decide⟩ _ _ _
    ((alnId_124 j hj) ▸ Q2.listedAt (⟨124, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨124, by decide⟩ : Fin 148) hj hq).1) colCertDiv_124_39_20_match


theorem leaf_124_47_0 (hp : 0 < (Q2.transData.getD 47 []).length)
    (j : Nat) (hj : j < (repChars.getD 124 []).length)
    (hq : (normIsRep.getD 124 []).getD j false = true) :
    species (Q2.reps (⟨47, by decide⟩ : Fin 148)) (colE2 ⟨47, by decide⟩ 0 hp)
        (rowE2 (⟨124, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨47, by decide⟩ : Fin 148))
        (colE1 ⟨47, by decide⟩ 0 (transLenTr ⟨47, by decide⟩ 0 hp))
        (rowE1 (⟨124, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨124, by decide⟩ : Fin 148) ⟨47, by decide⟩ _
      (validAt ⟨124, by decide⟩ (listedAt ⟨124, by decide⟩ hj))
      (colE1 ⟨47, by decide⟩ 0 (transLenTr ⟨47, by decide⟩ 0 hp)) T124_47
      hfix124_47 hinj124_47 hcardT124_47
      (fun i => conj_mem_of_fixedPoints _ _ (T124_47 i) (hfix124_47 i) _)
      ⟨124, by decide⟩ ⟨47, by decide⟩ _
      (Q2.validAt ⟨124, by decide⟩ (Q2.listedAt ⟨124, by decide⟩
        (alnCheck_rep ⟨124, by decide⟩ hj hq).1))
      (colE2 ⟨47, by decide⟩ 0 hp) Q2.T124_47_2 Q2.hfix124_47_2 Q2.hinj124_47_2
      Q2.hcardT124_47_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T124_47_2 i) (Q2.hfix124_47_2 i) _)
      colCert_124_47_0.hD ?_).symm
  rw [alnId_124 j hj]


theorem leaf_124_47_1 (hp : 1 < (Q2.transData.getD 47 []).length)
    (j : Nat) (hj : j < (repChars.getD 124 []).length)
    (hq : (normIsRep.getD 124 []).getD j false = true) :
    species (Q2.reps (⟨47, by decide⟩ : Fin 148)) (colE2 ⟨47, by decide⟩ 1 hp)
        (rowE2 (⟨124, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨47, by decide⟩ : Fin 148))
        (colE1 ⟨47, by decide⟩ 1 (transLenTr ⟨47, by decide⟩ 1 hp))
        (rowE1 (⟨124, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨124, by decide⟩ : Fin 148) ⟨47, by decide⟩ _
      (validAt ⟨124, by decide⟩ (listedAt ⟨124, by decide⟩ hj))
      (colE1 ⟨47, by decide⟩ 1 (transLenTr ⟨47, by decide⟩ 1 hp)) T124_47
      hfix124_47 hinj124_47 hcardT124_47
      (fun i => conj_mem_of_fixedPoints _ _ (T124_47 i) (hfix124_47 i) _)
      ⟨124, by decide⟩ ⟨47, by decide⟩ _
      (Q2.validAt ⟨124, by decide⟩ (Q2.listedAt ⟨124, by decide⟩
        (alnCheck_rep ⟨124, by decide⟩ hj hq).1))
      (colE2 ⟨47, by decide⟩ 1 hp) Q2.T124_47_2 Q2.hfix124_47_2 Q2.hinj124_47_2
      Q2.hcardT124_47_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T124_47_2 i) (Q2.hfix124_47_2 i) _)
      colCert_124_47_1.hD ?_).symm
  rw [alnId_124 j hj]


theorem leaf_124_47_2 (hp : 2 < (Q2.transData.getD 47 []).length)
    (j : Nat) (hj : j < (repChars.getD 124 []).length)
    (hq : (normIsRep.getD 124 []).getD j false = true) :
    species (Q2.reps (⟨47, by decide⟩ : Fin 148)) (colE2 ⟨47, by decide⟩ 2 hp)
        (rowE2 (⟨124, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨47, by decide⟩ : Fin 148))
        (colE1 ⟨47, by decide⟩ 2 (transLenTr ⟨47, by decide⟩ 2 hp))
        (rowE1 (⟨124, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨124, by decide⟩ : Fin 148) ⟨47, by decide⟩ _
      (validAt ⟨124, by decide⟩ (listedAt ⟨124, by decide⟩ hj))
      (colE1 ⟨47, by decide⟩ 2 (transLenTr ⟨47, by decide⟩ 2 hp)) T124_47
      hfix124_47 hinj124_47 hcardT124_47
      (fun i => conj_mem_of_fixedPoints _ _ (T124_47 i) (hfix124_47 i) _)
      ⟨124, by decide⟩ ⟨47, by decide⟩ _
      (Q2.validAt ⟨124, by decide⟩ (Q2.listedAt ⟨124, by decide⟩
        (alnCheck_rep ⟨124, by decide⟩ hj hq).1))
      (colE2 ⟨47, by decide⟩ 2 hp) Q2.T124_47_2 Q2.hfix124_47_2 Q2.hinj124_47_2
      Q2.hcardT124_47_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T124_47_2 i) (Q2.hfix124_47_2 i) _)
      colCert_124_47_2.hD ?_).symm
  rw [alnId_124 j hj]


theorem leaf_124_47_3 (hp : 3 < (Q2.transData.getD 47 []).length)
    (j : Nat) (hj : j < (repChars.getD 124 []).length)
    (hq : (normIsRep.getD 124 []).getD j false = true) :
    species (Q2.reps (⟨47, by decide⟩ : Fin 148)) (colE2 ⟨47, by decide⟩ 3 hp)
        (rowE2 (⟨124, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨47, by decide⟩ : Fin 148))
        (colE1 ⟨47, by decide⟩ 3 (transLenTr ⟨47, by decide⟩ 3 hp))
        (rowE1 (⟨124, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨124, by decide⟩ : Fin 148) ⟨47, by decide⟩ _
      (validAt ⟨124, by decide⟩ (listedAt ⟨124, by decide⟩ hj))
      (colE1 ⟨47, by decide⟩ 3 (transLenTr ⟨47, by decide⟩ 3 hp)) T124_47
      hfix124_47 hinj124_47 hcardT124_47
      (fun i => conj_mem_of_fixedPoints _ _ (T124_47 i) (hfix124_47 i) _)
      ⟨124, by decide⟩ ⟨47, by decide⟩ _
      (Q2.validAt ⟨124, by decide⟩ (Q2.listedAt ⟨124, by decide⟩
        (alnCheck_rep ⟨124, by decide⟩ hj hq).1))
      (colE2 ⟨47, by decide⟩ 3 hp) Q2.T124_47_2 Q2.hfix124_47_2 Q2.hinj124_47_2
      Q2.hcardT124_47_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T124_47_2 i) (Q2.hfix124_47_2 i) _)
      colCert_124_47_3.hD ?_).symm
  rw [alnId_124 j hj]


theorem leaf_124_47_4 (hp : 4 < (Q2.transData.getD 47 []).length)
    (j : Nat) (hj : j < (repChars.getD 124 []).length)
    (hq : (normIsRep.getD 124 []).getD j false = true) :
    species (Q2.reps (⟨47, by decide⟩ : Fin 148)) (colE2 ⟨47, by decide⟩ 4 hp)
        (rowE2 (⟨124, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨47, by decide⟩ : Fin 148))
        (colE1 ⟨47, by decide⟩ 4 (transLenTr ⟨47, by decide⟩ 4 hp))
        (rowE1 (⟨124, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨124, by decide⟩ : Fin 148) ⟨47, by decide⟩ _
      (validAt ⟨124, by decide⟩ (listedAt ⟨124, by decide⟩ hj))
      (colE1 ⟨47, by decide⟩ 4 (transLenTr ⟨47, by decide⟩ 4 hp)) T124_47
      hfix124_47 hinj124_47 hcardT124_47
      (fun i => conj_mem_of_fixedPoints _ _ (T124_47 i) (hfix124_47 i) _)
      ⟨124, by decide⟩ ⟨47, by decide⟩ _
      (Q2.validAt ⟨124, by decide⟩ (Q2.listedAt ⟨124, by decide⟩
        (alnCheck_rep ⟨124, by decide⟩ hj hq).1))
      (colE2 ⟨47, by decide⟩ 4 hp) Q2.T124_47_2 Q2.hfix124_47_2 Q2.hinj124_47_2
      Q2.hcardT124_47_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T124_47_2 i) (Q2.hfix124_47_2 i) _)
      colCert_124_47_4.hD ?_).symm
  rw [alnId_124 j hj]


theorem leaf_124_47_5 (hp : 5 < (Q2.transData.getD 47 []).length)
    (j : Nat) (hj : j < (repChars.getD 124 []).length)
    (hq : (normIsRep.getD 124 []).getD j false = true) :
    species (Q2.reps (⟨47, by decide⟩ : Fin 148)) (colE2 ⟨47, by decide⟩ 5 hp)
        (rowE2 (⟨124, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨47, by decide⟩ : Fin 148))
        (colE1 ⟨47, by decide⟩ 5 (transLenTr ⟨47, by decide⟩ 5 hp))
        (rowE1 (⟨124, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨124, by decide⟩ : Fin 148) ⟨47, by decide⟩ _
      (validAt ⟨124, by decide⟩ (listedAt ⟨124, by decide⟩ hj))
      (colE1 ⟨47, by decide⟩ 5 (transLenTr ⟨47, by decide⟩ 5 hp)) T124_47
      hfix124_47 hinj124_47 hcardT124_47
      (fun i => conj_mem_of_fixedPoints _ _ (T124_47 i) (hfix124_47 i) _)
      ⟨124, by decide⟩ ⟨47, by decide⟩ _
      (Q2.validAt ⟨124, by decide⟩ (Q2.listedAt ⟨124, by decide⟩
        (alnCheck_rep ⟨124, by decide⟩ hj hq).1))
      (colE2 ⟨47, by decide⟩ 5 hp) Q2.T124_47_2 Q2.hfix124_47_2 Q2.hinj124_47_2
      Q2.hcardT124_47_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T124_47_2 i) (Q2.hfix124_47_2 i) _)
      colCert_124_47_5.hD ?_).symm
  rw [alnId_124 j hj]


theorem leaf_124_47_10 (hp : 10 < (Q2.transData.getD 47 []).length)
    (j : Nat) (hj : j < (repChars.getD 124 []).length)
    (hq : (normIsRep.getD 124 []).getD j false = true) :
    species (Q2.reps (⟨47, by decide⟩ : Fin 148)) (colE2 ⟨47, by decide⟩ 10 hp)
        (rowE2 (⟨124, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨47, by decide⟩ : Fin 148))
        (colE1 ⟨47, by decide⟩ 10 (transLenTr ⟨47, by decide⟩ 10 hp))
        (rowE1 (⟨124, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨124, by decide⟩ : Fin 148) ⟨47, by decide⟩ _
      (validAt ⟨124, by decide⟩ (listedAt ⟨124, by decide⟩ hj))
      (colE1 ⟨47, by decide⟩ 10 (transLenTr ⟨47, by decide⟩ 10 hp)) T124_47
      hfix124_47 hinj124_47 hcardT124_47
      (fun i => conj_mem_of_fixedPoints _ _ (T124_47 i) (hfix124_47 i) _)
      ⟨124, by decide⟩ ⟨47, by decide⟩ _
      (Q2.validAt ⟨124, by decide⟩ (Q2.listedAt ⟨124, by decide⟩
        (alnCheck_rep ⟨124, by decide⟩ hj hq).1))
      (colE2 ⟨47, by decide⟩ 10 hp) Q2.T124_47_2 Q2.hfix124_47_2 Q2.hinj124_47_2
      Q2.hcardT124_47_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T124_47_2 i) (Q2.hfix124_47_2 i) _)
      colCert_124_47_10.hD ?_).symm
  rw [alnId_124 j hj]


theorem leaf_124_47_15 (hp : 15 < (Q2.transData.getD 47 []).length)
    (j : Nat) (hj : j < (repChars.getD 124 []).length)
    (hq : (normIsRep.getD 124 []).getD j false = true) :
    species (Q2.reps (⟨47, by decide⟩ : Fin 148)) (colE2 ⟨47, by decide⟩ 15 hp)
        (rowE2 (⟨124, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨47, by decide⟩ : Fin 148))
        (colE1 ⟨47, by decide⟩ 15 (transLenTr ⟨47, by decide⟩ 15 hp))
        (rowE1 (⟨124, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨124, by decide⟩ : Fin 148) ⟨47, by decide⟩ _
      (validAt ⟨124, by decide⟩ (listedAt ⟨124, by decide⟩ hj))
      (colE1 ⟨47, by decide⟩ 15 (transLenTr ⟨47, by decide⟩ 15 hp)) T124_47
      hfix124_47 hinj124_47 hcardT124_47
      (fun i => conj_mem_of_fixedPoints _ _ (T124_47 i) (hfix124_47 i) _)
      ⟨124, by decide⟩ ⟨47, by decide⟩ _
      (Q2.validAt ⟨124, by decide⟩ (Q2.listedAt ⟨124, by decide⟩
        (alnCheck_rep ⟨124, by decide⟩ hj hq).1))
      (colE2 ⟨47, by decide⟩ 15 hp) Q2.T124_47_2 Q2.hfix124_47_2 Q2.hinj124_47_2
      Q2.hcardT124_47_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T124_47_2 i) (Q2.hfix124_47_2 i) _)
      colCert_124_47_15.hD ?_).symm
  rw [alnId_124 j hj]


theorem leaf_124_47_20 (hp : 20 < (Q2.transData.getD 47 []).length)
    (j : Nat) (hj : j < (repChars.getD 124 []).length)
    (hq : (normIsRep.getD 124 []).getD j false = true) :
    species (Q2.reps (⟨47, by decide⟩ : Fin 148)) (colE2 ⟨47, by decide⟩ 20 hp)
        (rowE2 (⟨124, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨47, by decide⟩ : Fin 148))
        (colE1 ⟨47, by decide⟩ 20 (transLenTr ⟨47, by decide⟩ 20 hp))
        (rowE1 (⟨124, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨124, by decide⟩ : Fin 148) ⟨47, by decide⟩ _
      (validAt ⟨124, by decide⟩ (listedAt ⟨124, by decide⟩ hj))
      (colE1 ⟨47, by decide⟩ 20 (transLenTr ⟨47, by decide⟩ 20 hp)) T124_47
      hfix124_47 hinj124_47 hcardT124_47
      (fun i => conj_mem_of_fixedPoints _ _ (T124_47 i) (hfix124_47 i) _)
      ⟨124, by decide⟩ ⟨47, by decide⟩ _
      (Q2.validAt ⟨124, by decide⟩ (Q2.listedAt ⟨124, by decide⟩
        (alnCheck_rep ⟨124, by decide⟩ hj hq).1))
      (colE2 ⟨47, by decide⟩ 20 hp) Q2.T124_47_2 Q2.hfix124_47_2 Q2.hinj124_47_2
      Q2.hcardT124_47_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T124_47_2 i) (Q2.hfix124_47_2 i) _)
      colCert_124_47_20.hD ?_).symm
  rw [alnId_124 j hj]


theorem leaf_124_51_0 (hp : 0 < (Q2.transData.getD 51 []).length)
    (j : Nat) (hj : j < (repChars.getD 124 []).length)
    (hq : (normIsRep.getD 124 []).getD j false = true) :
    species (Q2.reps (⟨51, by decide⟩ : Fin 148)) (colE2 ⟨51, by decide⟩ 0 hp)
        (rowE2 (⟨124, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨51, by decide⟩ : Fin 148))
        (colE1 ⟨51, by decide⟩ 0 (transLenTr ⟨51, by decide⟩ 0 hp))
        (rowE1 (⟨124, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨124, by decide⟩ : Fin 148) ⟨51, by decide⟩ _
      (validAt ⟨124, by decide⟩ (listedAt ⟨124, by decide⟩ hj))
      (colE1 ⟨51, by decide⟩ 0 (transLenTr ⟨51, by decide⟩ 0 hp)) T124_51
      hfix124_51 hinj124_51 hcardT124_51
      (fun i => conj_mem_of_fixedPoints _ _ (T124_51 i) (hfix124_51 i) _)
      ⟨124, by decide⟩ ⟨51, by decide⟩ _
      (Q2.validAt ⟨124, by decide⟩ (Q2.listedAt ⟨124, by decide⟩
        (alnCheck_rep ⟨124, by decide⟩ hj hq).1))
      (colE2 ⟨51, by decide⟩ 0 hp) Q2.T124_51_2 Q2.hfix124_51_2 Q2.hinj124_51_2
      Q2.hcardT124_51_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T124_51_2 i) (Q2.hfix124_51_2 i) _)
      colCert_124_51_0.hD ?_).symm
  rw [alnId_124 j hj]


theorem leaf_124_51_1 (hp : 1 < (Q2.transData.getD 51 []).length)
    (j : Nat) (hj : j < (repChars.getD 124 []).length)
    (hq : (normIsRep.getD 124 []).getD j false = true) :
    species (Q2.reps (⟨51, by decide⟩ : Fin 148)) (colE2 ⟨51, by decide⟩ 1 hp)
        (rowE2 (⟨124, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨51, by decide⟩ : Fin 148))
        (colE1 ⟨51, by decide⟩ 1 (transLenTr ⟨51, by decide⟩ 1 hp))
        (rowE1 (⟨124, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨124, by decide⟩ : Fin 148) ⟨51, by decide⟩ _
      (validAt ⟨124, by decide⟩ (listedAt ⟨124, by decide⟩ hj))
      (colE1 ⟨51, by decide⟩ 1 (transLenTr ⟨51, by decide⟩ 1 hp)) T124_51
      hfix124_51 hinj124_51 hcardT124_51
      (fun i => conj_mem_of_fixedPoints _ _ (T124_51 i) (hfix124_51 i) _)
      ⟨124, by decide⟩ ⟨51, by decide⟩ _
      (Q2.validAt ⟨124, by decide⟩ (Q2.listedAt ⟨124, by decide⟩
        (alnCheck_rep ⟨124, by decide⟩ hj hq).1))
      (colE2 ⟨51, by decide⟩ 1 hp) Q2.T124_51_2 Q2.hfix124_51_2 Q2.hinj124_51_2
      Q2.hcardT124_51_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T124_51_2 i) (Q2.hfix124_51_2 i) _)
      colCert_124_51_1.hD ?_).symm
  rw [alnId_124 j hj]


theorem leaf_124_51_2 (hp : 2 < (Q2.transData.getD 51 []).length)
    (j : Nat) (hj : j < (repChars.getD 124 []).length)
    (hq : (normIsRep.getD 124 []).getD j false = true) :
    species (Q2.reps (⟨51, by decide⟩ : Fin 148)) (colE2 ⟨51, by decide⟩ 2 hp)
        (rowE2 (⟨124, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨51, by decide⟩ : Fin 148))
        (colE1 ⟨51, by decide⟩ 2 (transLenTr ⟨51, by decide⟩ 2 hp))
        (rowE1 (⟨124, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨124, by decide⟩ : Fin 148) ⟨51, by decide⟩ _
      (validAt ⟨124, by decide⟩ (listedAt ⟨124, by decide⟩ hj))
      (colE1 ⟨51, by decide⟩ 2 (transLenTr ⟨51, by decide⟩ 2 hp)) T124_51
      hfix124_51 hinj124_51 hcardT124_51
      (fun i => conj_mem_of_fixedPoints _ _ (T124_51 i) (hfix124_51 i) _)
      ⟨124, by decide⟩ ⟨51, by decide⟩ _
      (Q2.validAt ⟨124, by decide⟩ (Q2.listedAt ⟨124, by decide⟩
        (alnCheck_rep ⟨124, by decide⟩ hj hq).1))
      (colE2 ⟨51, by decide⟩ 2 hp) Q2.T124_51_2 Q2.hfix124_51_2 Q2.hinj124_51_2
      Q2.hcardT124_51_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T124_51_2 i) (Q2.hfix124_51_2 i) _)
      colCert_124_51_2.hD ?_).symm
  rw [alnId_124 j hj]


theorem leaf_124_51_3 (hp : 3 < (Q2.transData.getD 51 []).length)
    (j : Nat) (hj : j < (repChars.getD 124 []).length)
    (hq : (normIsRep.getD 124 []).getD j false = true) :
    species (Q2.reps (⟨51, by decide⟩ : Fin 148)) (colE2 ⟨51, by decide⟩ 3 hp)
        (rowE2 (⟨124, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨51, by decide⟩ : Fin 148))
        (colE1 ⟨51, by decide⟩ 3 (transLenTr ⟨51, by decide⟩ 3 hp))
        (rowE1 (⟨124, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨124, by decide⟩ : Fin 148) ⟨51, by decide⟩ _
      (validAt ⟨124, by decide⟩ (listedAt ⟨124, by decide⟩ hj))
      (colE1 ⟨51, by decide⟩ 3 (transLenTr ⟨51, by decide⟩ 3 hp)) T124_51
      hfix124_51 hinj124_51 hcardT124_51
      (fun i => conj_mem_of_fixedPoints _ _ (T124_51 i) (hfix124_51 i) _)
      ⟨124, by decide⟩ ⟨51, by decide⟩ _
      (Q2.validAt ⟨124, by decide⟩ (Q2.listedAt ⟨124, by decide⟩
        (alnCheck_rep ⟨124, by decide⟩ hj hq).1))
      (colE2 ⟨51, by decide⟩ 3 hp) Q2.T124_51_2 Q2.hfix124_51_2 Q2.hinj124_51_2
      Q2.hcardT124_51_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T124_51_2 i) (Q2.hfix124_51_2 i) _)
      colCert_124_51_3.hD ?_).symm
  rw [alnId_124 j hj]


theorem leaf_124_51_4 (hp : 4 < (Q2.transData.getD 51 []).length)
    (j : Nat) (hj : j < (repChars.getD 124 []).length)
    (hq : (normIsRep.getD 124 []).getD j false = true) :
    species (Q2.reps (⟨51, by decide⟩ : Fin 148)) (colE2 ⟨51, by decide⟩ 4 hp)
        (rowE2 (⟨124, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨51, by decide⟩ : Fin 148))
        (colE1 ⟨51, by decide⟩ 4 (transLenTr ⟨51, by decide⟩ 4 hp))
        (rowE1 (⟨124, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨124, by decide⟩ : Fin 148) ⟨51, by decide⟩ _
      (validAt ⟨124, by decide⟩ (listedAt ⟨124, by decide⟩ hj))
      (colE1 ⟨51, by decide⟩ 4 (transLenTr ⟨51, by decide⟩ 4 hp)) T124_51
      hfix124_51 hinj124_51 hcardT124_51
      (fun i => conj_mem_of_fixedPoints _ _ (T124_51 i) (hfix124_51 i) _)
      ⟨124, by decide⟩ ⟨51, by decide⟩ _
      (Q2.validAt ⟨124, by decide⟩ (Q2.listedAt ⟨124, by decide⟩
        (alnCheck_rep ⟨124, by decide⟩ hj hq).1))
      (colE2 ⟨51, by decide⟩ 4 hp) Q2.T124_51_2 Q2.hfix124_51_2 Q2.hinj124_51_2
      Q2.hcardT124_51_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T124_51_2 i) (Q2.hfix124_51_2 i) _)
      colCert_124_51_4.hD ?_).symm
  rw [alnId_124 j hj]


theorem leaf_124_51_5 (hp : 5 < (Q2.transData.getD 51 []).length)
    (j : Nat) (hj : j < (repChars.getD 124 []).length)
    (hq : (normIsRep.getD 124 []).getD j false = true) :
    species (Q2.reps (⟨51, by decide⟩ : Fin 148)) (colE2 ⟨51, by decide⟩ 5 hp)
        (rowE2 (⟨124, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨51, by decide⟩ : Fin 148))
        (colE1 ⟨51, by decide⟩ 5 (transLenTr ⟨51, by decide⟩ 5 hp))
        (rowE1 (⟨124, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨124, by decide⟩ : Fin 148) ⟨51, by decide⟩ _
      (validAt ⟨124, by decide⟩ (listedAt ⟨124, by decide⟩ hj))
      (colE1 ⟨51, by decide⟩ 5 (transLenTr ⟨51, by decide⟩ 5 hp)) T124_51
      hfix124_51 hinj124_51 hcardT124_51
      (fun i => conj_mem_of_fixedPoints _ _ (T124_51 i) (hfix124_51 i) _)
      ⟨124, by decide⟩ ⟨51, by decide⟩ _
      (Q2.validAt ⟨124, by decide⟩ (Q2.listedAt ⟨124, by decide⟩
        (alnCheck_rep ⟨124, by decide⟩ hj hq).1))
      (colE2 ⟨51, by decide⟩ 5 hp) Q2.T124_51_2 Q2.hfix124_51_2 Q2.hinj124_51_2
      Q2.hcardT124_51_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T124_51_2 i) (Q2.hfix124_51_2 i) _)
      ?_).symm
  rw [show colData1 (⟨124, by decide⟩ : Fin 148)
        ((colE1 ⟨51, by decide⟩ 5 (transLenTr ⟨51, by decide⟩ 5 hp) : ↥(reps ⟨51, by decide⟩)) : Coordinate 1)
        T124_51 = colFn colCertDiv_124_51_5.D1 (m := 5) from colCertDiv_124_51_5.bind1,
    show colData2 (⟨124, by decide⟩ : Fin 148)
        ((colE2 ⟨51, by decide⟩ 5 hp : ↥(Q2.reps ⟨51, by decide⟩)) : Coordinate 2)
        Q2.T124_51_2 = colFn colCertDiv_124_51_5.D2 (m := 5) from colCertDiv_124_51_5.bind2]
  rw [alnId_124 j hj]
  exact fastcode_of_div ⟨124, by decide⟩ _ _ _
    ((alnId_124 j hj) ▸ Q2.listedAt (⟨124, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨124, by decide⟩ : Fin 148) hj hq).1) colCertDiv_124_51_5_match


theorem leaf_124_51_10 (hp : 10 < (Q2.transData.getD 51 []).length)
    (j : Nat) (hj : j < (repChars.getD 124 []).length)
    (hq : (normIsRep.getD 124 []).getD j false = true) :
    species (Q2.reps (⟨51, by decide⟩ : Fin 148)) (colE2 ⟨51, by decide⟩ 10 hp)
        (rowE2 (⟨124, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨51, by decide⟩ : Fin 148))
        (colE1 ⟨51, by decide⟩ 10 (transLenTr ⟨51, by decide⟩ 10 hp))
        (rowE1 (⟨124, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨124, by decide⟩ : Fin 148) ⟨51, by decide⟩ _
      (validAt ⟨124, by decide⟩ (listedAt ⟨124, by decide⟩ hj))
      (colE1 ⟨51, by decide⟩ 10 (transLenTr ⟨51, by decide⟩ 10 hp)) T124_51
      hfix124_51 hinj124_51 hcardT124_51
      (fun i => conj_mem_of_fixedPoints _ _ (T124_51 i) (hfix124_51 i) _)
      ⟨124, by decide⟩ ⟨51, by decide⟩ _
      (Q2.validAt ⟨124, by decide⟩ (Q2.listedAt ⟨124, by decide⟩
        (alnCheck_rep ⟨124, by decide⟩ hj hq).1))
      (colE2 ⟨51, by decide⟩ 10 hp) Q2.T124_51_2 Q2.hfix124_51_2 Q2.hinj124_51_2
      Q2.hcardT124_51_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T124_51_2 i) (Q2.hfix124_51_2 i) _)
      ?_).symm
  rw [show colData1 (⟨124, by decide⟩ : Fin 148)
        ((colE1 ⟨51, by decide⟩ 10 (transLenTr ⟨51, by decide⟩ 10 hp) : ↥(reps ⟨51, by decide⟩)) : Coordinate 1)
        T124_51 = colFn colCertDiv_124_51_10.D1 (m := 5) from colCertDiv_124_51_10.bind1,
    show colData2 (⟨124, by decide⟩ : Fin 148)
        ((colE2 ⟨51, by decide⟩ 10 hp : ↥(Q2.reps ⟨51, by decide⟩)) : Coordinate 2)
        Q2.T124_51_2 = colFn colCertDiv_124_51_10.D2 (m := 5) from colCertDiv_124_51_10.bind2]
  rw [alnId_124 j hj]
  exact fastcode_of_div ⟨124, by decide⟩ _ _ _
    ((alnId_124 j hj) ▸ Q2.listedAt (⟨124, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨124, by decide⟩ : Fin 148) hj hq).1) colCertDiv_124_51_10_match


theorem leaf_124_51_15 (hp : 15 < (Q2.transData.getD 51 []).length)
    (j : Nat) (hj : j < (repChars.getD 124 []).length)
    (hq : (normIsRep.getD 124 []).getD j false = true) :
    species (Q2.reps (⟨51, by decide⟩ : Fin 148)) (colE2 ⟨51, by decide⟩ 15 hp)
        (rowE2 (⟨124, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨51, by decide⟩ : Fin 148))
        (colE1 ⟨51, by decide⟩ 15 (transLenTr ⟨51, by decide⟩ 15 hp))
        (rowE1 (⟨124, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨124, by decide⟩ : Fin 148) ⟨51, by decide⟩ _
      (validAt ⟨124, by decide⟩ (listedAt ⟨124, by decide⟩ hj))
      (colE1 ⟨51, by decide⟩ 15 (transLenTr ⟨51, by decide⟩ 15 hp)) T124_51
      hfix124_51 hinj124_51 hcardT124_51
      (fun i => conj_mem_of_fixedPoints _ _ (T124_51 i) (hfix124_51 i) _)
      ⟨124, by decide⟩ ⟨51, by decide⟩ _
      (Q2.validAt ⟨124, by decide⟩ (Q2.listedAt ⟨124, by decide⟩
        (alnCheck_rep ⟨124, by decide⟩ hj hq).1))
      (colE2 ⟨51, by decide⟩ 15 hp) Q2.T124_51_2 Q2.hfix124_51_2 Q2.hinj124_51_2
      Q2.hcardT124_51_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T124_51_2 i) (Q2.hfix124_51_2 i) _)
      ?_).symm
  rw [show colData1 (⟨124, by decide⟩ : Fin 148)
        ((colE1 ⟨51, by decide⟩ 15 (transLenTr ⟨51, by decide⟩ 15 hp) : ↥(reps ⟨51, by decide⟩)) : Coordinate 1)
        T124_51 = colFn colCertDiv_124_51_15.D1 (m := 5) from colCertDiv_124_51_15.bind1,
    show colData2 (⟨124, by decide⟩ : Fin 148)
        ((colE2 ⟨51, by decide⟩ 15 hp : ↥(Q2.reps ⟨51, by decide⟩)) : Coordinate 2)
        Q2.T124_51_2 = colFn colCertDiv_124_51_15.D2 (m := 5) from colCertDiv_124_51_15.bind2]
  rw [alnId_124 j hj]
  exact fastcode_of_div ⟨124, by decide⟩ _ _ _
    ((alnId_124 j hj) ▸ Q2.listedAt (⟨124, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨124, by decide⟩ : Fin 148) hj hq).1) colCertDiv_124_51_15_match


theorem leaf_124_51_20 (hp : 20 < (Q2.transData.getD 51 []).length)
    (j : Nat) (hj : j < (repChars.getD 124 []).length)
    (hq : (normIsRep.getD 124 []).getD j false = true) :
    species (Q2.reps (⟨51, by decide⟩ : Fin 148)) (colE2 ⟨51, by decide⟩ 20 hp)
        (rowE2 (⟨124, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨51, by decide⟩ : Fin 148))
        (colE1 ⟨51, by decide⟩ 20 (transLenTr ⟨51, by decide⟩ 20 hp))
        (rowE1 (⟨124, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨124, by decide⟩ : Fin 148) ⟨51, by decide⟩ _
      (validAt ⟨124, by decide⟩ (listedAt ⟨124, by decide⟩ hj))
      (colE1 ⟨51, by decide⟩ 20 (transLenTr ⟨51, by decide⟩ 20 hp)) T124_51
      hfix124_51 hinj124_51 hcardT124_51
      (fun i => conj_mem_of_fixedPoints _ _ (T124_51 i) (hfix124_51 i) _)
      ⟨124, by decide⟩ ⟨51, by decide⟩ _
      (Q2.validAt ⟨124, by decide⟩ (Q2.listedAt ⟨124, by decide⟩
        (alnCheck_rep ⟨124, by decide⟩ hj hq).1))
      (colE2 ⟨51, by decide⟩ 20 hp) Q2.T124_51_2 Q2.hfix124_51_2 Q2.hinj124_51_2
      Q2.hcardT124_51_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T124_51_2 i) (Q2.hfix124_51_2 i) _)
      ?_).symm
  rw [show colData1 (⟨124, by decide⟩ : Fin 148)
        ((colE1 ⟨51, by decide⟩ 20 (transLenTr ⟨51, by decide⟩ 20 hp) : ↥(reps ⟨51, by decide⟩)) : Coordinate 1)
        T124_51 = colFn colCertDiv_124_51_20.D1 (m := 5) from colCertDiv_124_51_20.bind1,
    show colData2 (⟨124, by decide⟩ : Fin 148)
        ((colE2 ⟨51, by decide⟩ 20 hp : ↥(Q2.reps ⟨51, by decide⟩)) : Coordinate 2)
        Q2.T124_51_2 = colFn colCertDiv_124_51_20.D2 (m := 5) from colCertDiv_124_51_20.bind2]
  rw [alnId_124 j hj]
  exact fastcode_of_div ⟨124, by decide⟩ _ _ _
    ((alnId_124 j hj) ▸ Q2.listedAt (⟨124, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨124, by decide⟩ : Fin 148) hj hq).1) colCertDiv_124_51_20_match


theorem leaf_124_53_0 (hp : 0 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 124 []).length)
    (hq : (normIsRep.getD 124 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 0 hp)
        (rowE2 (⟨124, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 0 (transLenTr ⟨53, by decide⟩ 0 hp))
        (rowE1 (⟨124, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨124, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨124, by decide⟩ (listedAt ⟨124, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 0 (transLenTr ⟨53, by decide⟩ 0 hp)) T124_53
      hfix124_53 hinj124_53 hcardT124_53
      (fun i => conj_mem_of_fixedPoints _ _ (T124_53 i) (hfix124_53 i) _)
      ⟨124, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨124, by decide⟩ (Q2.listedAt ⟨124, by decide⟩
        (alnCheck_rep ⟨124, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 0 hp) Q2.T124_53_2 Q2.hfix124_53_2 Q2.hinj124_53_2
      Q2.hcardT124_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T124_53_2 i) (Q2.hfix124_53_2 i) _)
      colCert_124_53_0.hD ?_).symm
  rw [alnId_124 j hj]


theorem leaf_124_53_1 (hp : 1 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 124 []).length)
    (hq : (normIsRep.getD 124 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 1 hp)
        (rowE2 (⟨124, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 1 (transLenTr ⟨53, by decide⟩ 1 hp))
        (rowE1 (⟨124, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨124, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨124, by decide⟩ (listedAt ⟨124, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 1 (transLenTr ⟨53, by decide⟩ 1 hp)) T124_53
      hfix124_53 hinj124_53 hcardT124_53
      (fun i => conj_mem_of_fixedPoints _ _ (T124_53 i) (hfix124_53 i) _)
      ⟨124, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨124, by decide⟩ (Q2.listedAt ⟨124, by decide⟩
        (alnCheck_rep ⟨124, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 1 hp) Q2.T124_53_2 Q2.hfix124_53_2 Q2.hinj124_53_2
      Q2.hcardT124_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T124_53_2 i) (Q2.hfix124_53_2 i) _)
      colCert_124_53_1.hD ?_).symm
  rw [alnId_124 j hj]


theorem leaf_124_53_2 (hp : 2 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 124 []).length)
    (hq : (normIsRep.getD 124 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 2 hp)
        (rowE2 (⟨124, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 2 (transLenTr ⟨53, by decide⟩ 2 hp))
        (rowE1 (⟨124, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨124, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨124, by decide⟩ (listedAt ⟨124, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 2 (transLenTr ⟨53, by decide⟩ 2 hp)) T124_53
      hfix124_53 hinj124_53 hcardT124_53
      (fun i => conj_mem_of_fixedPoints _ _ (T124_53 i) (hfix124_53 i) _)
      ⟨124, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨124, by decide⟩ (Q2.listedAt ⟨124, by decide⟩
        (alnCheck_rep ⟨124, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 2 hp) Q2.T124_53_2 Q2.hfix124_53_2 Q2.hinj124_53_2
      Q2.hcardT124_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T124_53_2 i) (Q2.hfix124_53_2 i) _)
      colCert_124_53_2.hD ?_).symm
  rw [alnId_124 j hj]


theorem leaf_124_53_3 (hp : 3 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 124 []).length)
    (hq : (normIsRep.getD 124 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 3 hp)
        (rowE2 (⟨124, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 3 (transLenTr ⟨53, by decide⟩ 3 hp))
        (rowE1 (⟨124, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨124, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨124, by decide⟩ (listedAt ⟨124, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 3 (transLenTr ⟨53, by decide⟩ 3 hp)) T124_53
      hfix124_53 hinj124_53 hcardT124_53
      (fun i => conj_mem_of_fixedPoints _ _ (T124_53 i) (hfix124_53 i) _)
      ⟨124, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨124, by decide⟩ (Q2.listedAt ⟨124, by decide⟩
        (alnCheck_rep ⟨124, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 3 hp) Q2.T124_53_2 Q2.hfix124_53_2 Q2.hinj124_53_2
      Q2.hcardT124_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T124_53_2 i) (Q2.hfix124_53_2 i) _)
      colCert_124_53_3.hD ?_).symm
  rw [alnId_124 j hj]


theorem leaf_124_53_4 (hp : 4 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 124 []).length)
    (hq : (normIsRep.getD 124 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 4 hp)
        (rowE2 (⟨124, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 4 (transLenTr ⟨53, by decide⟩ 4 hp))
        (rowE1 (⟨124, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨124, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨124, by decide⟩ (listedAt ⟨124, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 4 (transLenTr ⟨53, by decide⟩ 4 hp)) T124_53
      hfix124_53 hinj124_53 hcardT124_53
      (fun i => conj_mem_of_fixedPoints _ _ (T124_53 i) (hfix124_53 i) _)
      ⟨124, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨124, by decide⟩ (Q2.listedAt ⟨124, by decide⟩
        (alnCheck_rep ⟨124, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 4 hp) Q2.T124_53_2 Q2.hfix124_53_2 Q2.hinj124_53_2
      Q2.hcardT124_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T124_53_2 i) (Q2.hfix124_53_2 i) _)
      colCert_124_53_4.hD ?_).symm
  rw [alnId_124 j hj]


theorem leaf_124_53_5 (hp : 5 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 124 []).length)
    (hq : (normIsRep.getD 124 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 5 hp)
        (rowE2 (⟨124, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 5 (transLenTr ⟨53, by decide⟩ 5 hp))
        (rowE1 (⟨124, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨124, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨124, by decide⟩ (listedAt ⟨124, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 5 (transLenTr ⟨53, by decide⟩ 5 hp)) T124_53
      hfix124_53 hinj124_53 hcardT124_53
      (fun i => conj_mem_of_fixedPoints _ _ (T124_53 i) (hfix124_53 i) _)
      ⟨124, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨124, by decide⟩ (Q2.listedAt ⟨124, by decide⟩
        (alnCheck_rep ⟨124, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 5 hp) Q2.T124_53_2 Q2.hfix124_53_2 Q2.hinj124_53_2
      Q2.hcardT124_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T124_53_2 i) (Q2.hfix124_53_2 i) _)
      colCert_124_53_5.hD ?_).symm
  rw [alnId_124 j hj]


theorem leaf_124_53_10 (hp : 10 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 124 []).length)
    (hq : (normIsRep.getD 124 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 10 hp)
        (rowE2 (⟨124, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 10 (transLenTr ⟨53, by decide⟩ 10 hp))
        (rowE1 (⟨124, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨124, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨124, by decide⟩ (listedAt ⟨124, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 10 (transLenTr ⟨53, by decide⟩ 10 hp)) T124_53
      hfix124_53 hinj124_53 hcardT124_53
      (fun i => conj_mem_of_fixedPoints _ _ (T124_53 i) (hfix124_53 i) _)
      ⟨124, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨124, by decide⟩ (Q2.listedAt ⟨124, by decide⟩
        (alnCheck_rep ⟨124, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 10 hp) Q2.T124_53_2 Q2.hfix124_53_2 Q2.hinj124_53_2
      Q2.hcardT124_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T124_53_2 i) (Q2.hfix124_53_2 i) _)
      colCert_124_53_10.hD ?_).symm
  rw [alnId_124 j hj]


theorem leaf_124_53_15 (hp : 15 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 124 []).length)
    (hq : (normIsRep.getD 124 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 15 hp)
        (rowE2 (⟨124, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 15 (transLenTr ⟨53, by decide⟩ 15 hp))
        (rowE1 (⟨124, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨124, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨124, by decide⟩ (listedAt ⟨124, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 15 (transLenTr ⟨53, by decide⟩ 15 hp)) T124_53
      hfix124_53 hinj124_53 hcardT124_53
      (fun i => conj_mem_of_fixedPoints _ _ (T124_53 i) (hfix124_53 i) _)
      ⟨124, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨124, by decide⟩ (Q2.listedAt ⟨124, by decide⟩
        (alnCheck_rep ⟨124, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 15 hp) Q2.T124_53_2 Q2.hfix124_53_2 Q2.hinj124_53_2
      Q2.hcardT124_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T124_53_2 i) (Q2.hfix124_53_2 i) _)
      colCert_124_53_15.hD ?_).symm
  rw [alnId_124 j hj]


theorem leaf_124_53_20 (hp : 20 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 124 []).length)
    (hq : (normIsRep.getD 124 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 20 hp)
        (rowE2 (⟨124, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 20 (transLenTr ⟨53, by decide⟩ 20 hp))
        (rowE1 (⟨124, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨124, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨124, by decide⟩ (listedAt ⟨124, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 20 (transLenTr ⟨53, by decide⟩ 20 hp)) T124_53
      hfix124_53 hinj124_53 hcardT124_53
      (fun i => conj_mem_of_fixedPoints _ _ (T124_53 i) (hfix124_53 i) _)
      ⟨124, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨124, by decide⟩ (Q2.listedAt ⟨124, by decide⟩
        (alnCheck_rep ⟨124, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 20 hp) Q2.T124_53_2 Q2.hfix124_53_2 Q2.hinj124_53_2
      Q2.hcardT124_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T124_53_2 i) (Q2.hfix124_53_2 i) _)
      colCert_124_53_20.hD ?_).symm
  rw [alnId_124 j hj]


theorem leaf_124_81_0 (hp : 0 < (Q2.transData.getD 81 []).length)
    (j : Nat) (hj : j < (repChars.getD 124 []).length)
    (hq : (normIsRep.getD 124 []).getD j false = true) :
    species (Q2.reps (⟨81, by decide⟩ : Fin 148)) (colE2 ⟨81, by decide⟩ 0 hp)
        (rowE2 (⟨124, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨81, by decide⟩ : Fin 148))
        (colE1 ⟨81, by decide⟩ 0 (transLenTr ⟨81, by decide⟩ 0 hp))
        (rowE1 (⟨124, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨124, by decide⟩ : Fin 148) ⟨81, by decide⟩ _
      (validAt ⟨124, by decide⟩ (listedAt ⟨124, by decide⟩ hj))
      (colE1 ⟨81, by decide⟩ 0 (transLenTr ⟨81, by decide⟩ 0 hp)) T124_81
      hfix124_81 hinj124_81 hcardT124_81
      (fun i => conj_mem_of_fixedPoints _ _ (T124_81 i) (hfix124_81 i) _)
      ⟨124, by decide⟩ ⟨81, by decide⟩ _
      (Q2.validAt ⟨124, by decide⟩ (Q2.listedAt ⟨124, by decide⟩
        (alnCheck_rep ⟨124, by decide⟩ hj hq).1))
      (colE2 ⟨81, by decide⟩ 0 hp) Q2.T124_81_2 Q2.hfix124_81_2 Q2.hinj124_81_2
      Q2.hcardT124_81_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T124_81_2 i) (Q2.hfix124_81_2 i) _)
      colCert_124_81_0.hD ?_).symm
  rw [alnId_124 j hj]


theorem leaf_124_81_1 (hp : 1 < (Q2.transData.getD 81 []).length)
    (j : Nat) (hj : j < (repChars.getD 124 []).length)
    (hq : (normIsRep.getD 124 []).getD j false = true) :
    species (Q2.reps (⟨81, by decide⟩ : Fin 148)) (colE2 ⟨81, by decide⟩ 1 hp)
        (rowE2 (⟨124, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨81, by decide⟩ : Fin 148))
        (colE1 ⟨81, by decide⟩ 1 (transLenTr ⟨81, by decide⟩ 1 hp))
        (rowE1 (⟨124, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨124, by decide⟩ : Fin 148) ⟨81, by decide⟩ _
      (validAt ⟨124, by decide⟩ (listedAt ⟨124, by decide⟩ hj))
      (colE1 ⟨81, by decide⟩ 1 (transLenTr ⟨81, by decide⟩ 1 hp)) T124_81
      hfix124_81 hinj124_81 hcardT124_81
      (fun i => conj_mem_of_fixedPoints _ _ (T124_81 i) (hfix124_81 i) _)
      ⟨124, by decide⟩ ⟨81, by decide⟩ _
      (Q2.validAt ⟨124, by decide⟩ (Q2.listedAt ⟨124, by decide⟩
        (alnCheck_rep ⟨124, by decide⟩ hj hq).1))
      (colE2 ⟨81, by decide⟩ 1 hp) Q2.T124_81_2 Q2.hfix124_81_2 Q2.hinj124_81_2
      Q2.hcardT124_81_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T124_81_2 i) (Q2.hfix124_81_2 i) _)
      colCert_124_81_1.hD ?_).symm
  rw [alnId_124 j hj]


theorem leaf_124_81_2 (hp : 2 < (Q2.transData.getD 81 []).length)
    (j : Nat) (hj : j < (repChars.getD 124 []).length)
    (hq : (normIsRep.getD 124 []).getD j false = true) :
    species (Q2.reps (⟨81, by decide⟩ : Fin 148)) (colE2 ⟨81, by decide⟩ 2 hp)
        (rowE2 (⟨124, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨81, by decide⟩ : Fin 148))
        (colE1 ⟨81, by decide⟩ 2 (transLenTr ⟨81, by decide⟩ 2 hp))
        (rowE1 (⟨124, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨124, by decide⟩ : Fin 148) ⟨81, by decide⟩ _
      (validAt ⟨124, by decide⟩ (listedAt ⟨124, by decide⟩ hj))
      (colE1 ⟨81, by decide⟩ 2 (transLenTr ⟨81, by decide⟩ 2 hp)) T124_81
      hfix124_81 hinj124_81 hcardT124_81
      (fun i => conj_mem_of_fixedPoints _ _ (T124_81 i) (hfix124_81 i) _)
      ⟨124, by decide⟩ ⟨81, by decide⟩ _
      (Q2.validAt ⟨124, by decide⟩ (Q2.listedAt ⟨124, by decide⟩
        (alnCheck_rep ⟨124, by decide⟩ hj hq).1))
      (colE2 ⟨81, by decide⟩ 2 hp) Q2.T124_81_2 Q2.hfix124_81_2 Q2.hinj124_81_2
      Q2.hcardT124_81_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T124_81_2 i) (Q2.hfix124_81_2 i) _)
      colCert_124_81_2.hD ?_).symm
  rw [alnId_124 j hj]


theorem leaf_124_81_3 (hp : 3 < (Q2.transData.getD 81 []).length)
    (j : Nat) (hj : j < (repChars.getD 124 []).length)
    (hq : (normIsRep.getD 124 []).getD j false = true) :
    species (Q2.reps (⟨81, by decide⟩ : Fin 148)) (colE2 ⟨81, by decide⟩ 3 hp)
        (rowE2 (⟨124, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨81, by decide⟩ : Fin 148))
        (colE1 ⟨81, by decide⟩ 3 (transLenTr ⟨81, by decide⟩ 3 hp))
        (rowE1 (⟨124, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨124, by decide⟩ : Fin 148) ⟨81, by decide⟩ _
      (validAt ⟨124, by decide⟩ (listedAt ⟨124, by decide⟩ hj))
      (colE1 ⟨81, by decide⟩ 3 (transLenTr ⟨81, by decide⟩ 3 hp)) T124_81
      hfix124_81 hinj124_81 hcardT124_81
      (fun i => conj_mem_of_fixedPoints _ _ (T124_81 i) (hfix124_81 i) _)
      ⟨124, by decide⟩ ⟨81, by decide⟩ _
      (Q2.validAt ⟨124, by decide⟩ (Q2.listedAt ⟨124, by decide⟩
        (alnCheck_rep ⟨124, by decide⟩ hj hq).1))
      (colE2 ⟨81, by decide⟩ 3 hp) Q2.T124_81_2 Q2.hfix124_81_2 Q2.hinj124_81_2
      Q2.hcardT124_81_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T124_81_2 i) (Q2.hfix124_81_2 i) _)
      colCert_124_81_3.hD ?_).symm
  rw [alnId_124 j hj]


theorem leaf_124_81_4 (hp : 4 < (Q2.transData.getD 81 []).length)
    (j : Nat) (hj : j < (repChars.getD 124 []).length)
    (hq : (normIsRep.getD 124 []).getD j false = true) :
    species (Q2.reps (⟨81, by decide⟩ : Fin 148)) (colE2 ⟨81, by decide⟩ 4 hp)
        (rowE2 (⟨124, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨81, by decide⟩ : Fin 148))
        (colE1 ⟨81, by decide⟩ 4 (transLenTr ⟨81, by decide⟩ 4 hp))
        (rowE1 (⟨124, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨124, by decide⟩ : Fin 148) ⟨81, by decide⟩ _
      (validAt ⟨124, by decide⟩ (listedAt ⟨124, by decide⟩ hj))
      (colE1 ⟨81, by decide⟩ 4 (transLenTr ⟨81, by decide⟩ 4 hp)) T124_81
      hfix124_81 hinj124_81 hcardT124_81
      (fun i => conj_mem_of_fixedPoints _ _ (T124_81 i) (hfix124_81 i) _)
      ⟨124, by decide⟩ ⟨81, by decide⟩ _
      (Q2.validAt ⟨124, by decide⟩ (Q2.listedAt ⟨124, by decide⟩
        (alnCheck_rep ⟨124, by decide⟩ hj hq).1))
      (colE2 ⟨81, by decide⟩ 4 hp) Q2.T124_81_2 Q2.hfix124_81_2 Q2.hinj124_81_2
      Q2.hcardT124_81_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T124_81_2 i) (Q2.hfix124_81_2 i) _)
      colCert_124_81_4.hD ?_).symm
  rw [alnId_124 j hj]


theorem leaf_124_81_5 (hp : 5 < (Q2.transData.getD 81 []).length)
    (j : Nat) (hj : j < (repChars.getD 124 []).length)
    (hq : (normIsRep.getD 124 []).getD j false = true) :
    species (Q2.reps (⟨81, by decide⟩ : Fin 148)) (colE2 ⟨81, by decide⟩ 5 hp)
        (rowE2 (⟨124, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨81, by decide⟩ : Fin 148))
        (colE1 ⟨81, by decide⟩ 5 (transLenTr ⟨81, by decide⟩ 5 hp))
        (rowE1 (⟨124, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨124, by decide⟩ : Fin 148) ⟨81, by decide⟩ _
      (validAt ⟨124, by decide⟩ (listedAt ⟨124, by decide⟩ hj))
      (colE1 ⟨81, by decide⟩ 5 (transLenTr ⟨81, by decide⟩ 5 hp)) T124_81
      hfix124_81 hinj124_81 hcardT124_81
      (fun i => conj_mem_of_fixedPoints _ _ (T124_81 i) (hfix124_81 i) _)
      ⟨124, by decide⟩ ⟨81, by decide⟩ _
      (Q2.validAt ⟨124, by decide⟩ (Q2.listedAt ⟨124, by decide⟩
        (alnCheck_rep ⟨124, by decide⟩ hj hq).1))
      (colE2 ⟨81, by decide⟩ 5 hp) Q2.T124_81_2 Q2.hfix124_81_2 Q2.hinj124_81_2
      Q2.hcardT124_81_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T124_81_2 i) (Q2.hfix124_81_2 i) _)
      ?_).symm
  rw [show colData1 (⟨124, by decide⟩ : Fin 148)
        ((colE1 ⟨81, by decide⟩ 5 (transLenTr ⟨81, by decide⟩ 5 hp) : ↥(reps ⟨81, by decide⟩)) : Coordinate 1)
        T124_81 = colFn colCertDiv_124_81_5.D1 (m := 5) from colCertDiv_124_81_5.bind1,
    show colData2 (⟨124, by decide⟩ : Fin 148)
        ((colE2 ⟨81, by decide⟩ 5 hp : ↥(Q2.reps ⟨81, by decide⟩)) : Coordinate 2)
        Q2.T124_81_2 = colFn colCertDiv_124_81_5.D2 (m := 5) from colCertDiv_124_81_5.bind2]
  rw [alnId_124 j hj]
  exact fastcode_of_div ⟨124, by decide⟩ _ _ _
    ((alnId_124 j hj) ▸ Q2.listedAt (⟨124, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨124, by decide⟩ : Fin 148) hj hq).1) colCertDiv_124_81_5_match


theorem leaf_124_81_10 (hp : 10 < (Q2.transData.getD 81 []).length)
    (j : Nat) (hj : j < (repChars.getD 124 []).length)
    (hq : (normIsRep.getD 124 []).getD j false = true) :
    species (Q2.reps (⟨81, by decide⟩ : Fin 148)) (colE2 ⟨81, by decide⟩ 10 hp)
        (rowE2 (⟨124, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨81, by decide⟩ : Fin 148))
        (colE1 ⟨81, by decide⟩ 10 (transLenTr ⟨81, by decide⟩ 10 hp))
        (rowE1 (⟨124, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨124, by decide⟩ : Fin 148) ⟨81, by decide⟩ _
      (validAt ⟨124, by decide⟩ (listedAt ⟨124, by decide⟩ hj))
      (colE1 ⟨81, by decide⟩ 10 (transLenTr ⟨81, by decide⟩ 10 hp)) T124_81
      hfix124_81 hinj124_81 hcardT124_81
      (fun i => conj_mem_of_fixedPoints _ _ (T124_81 i) (hfix124_81 i) _)
      ⟨124, by decide⟩ ⟨81, by decide⟩ _
      (Q2.validAt ⟨124, by decide⟩ (Q2.listedAt ⟨124, by decide⟩
        (alnCheck_rep ⟨124, by decide⟩ hj hq).1))
      (colE2 ⟨81, by decide⟩ 10 hp) Q2.T124_81_2 Q2.hfix124_81_2 Q2.hinj124_81_2
      Q2.hcardT124_81_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T124_81_2 i) (Q2.hfix124_81_2 i) _)
      ?_).symm
  rw [show colData1 (⟨124, by decide⟩ : Fin 148)
        ((colE1 ⟨81, by decide⟩ 10 (transLenTr ⟨81, by decide⟩ 10 hp) : ↥(reps ⟨81, by decide⟩)) : Coordinate 1)
        T124_81 = colFn colCertDiv_124_81_10.D1 (m := 5) from colCertDiv_124_81_10.bind1,
    show colData2 (⟨124, by decide⟩ : Fin 148)
        ((colE2 ⟨81, by decide⟩ 10 hp : ↥(Q2.reps ⟨81, by decide⟩)) : Coordinate 2)
        Q2.T124_81_2 = colFn colCertDiv_124_81_10.D2 (m := 5) from colCertDiv_124_81_10.bind2]
  rw [alnId_124 j hj]
  exact fastcode_of_div ⟨124, by decide⟩ _ _ _
    ((alnId_124 j hj) ▸ Q2.listedAt (⟨124, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨124, by decide⟩ : Fin 148) hj hq).1) colCertDiv_124_81_10_match


theorem leaf_124_81_15 (hp : 15 < (Q2.transData.getD 81 []).length)
    (j : Nat) (hj : j < (repChars.getD 124 []).length)
    (hq : (normIsRep.getD 124 []).getD j false = true) :
    species (Q2.reps (⟨81, by decide⟩ : Fin 148)) (colE2 ⟨81, by decide⟩ 15 hp)
        (rowE2 (⟨124, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨81, by decide⟩ : Fin 148))
        (colE1 ⟨81, by decide⟩ 15 (transLenTr ⟨81, by decide⟩ 15 hp))
        (rowE1 (⟨124, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨124, by decide⟩ : Fin 148) ⟨81, by decide⟩ _
      (validAt ⟨124, by decide⟩ (listedAt ⟨124, by decide⟩ hj))
      (colE1 ⟨81, by decide⟩ 15 (transLenTr ⟨81, by decide⟩ 15 hp)) T124_81
      hfix124_81 hinj124_81 hcardT124_81
      (fun i => conj_mem_of_fixedPoints _ _ (T124_81 i) (hfix124_81 i) _)
      ⟨124, by decide⟩ ⟨81, by decide⟩ _
      (Q2.validAt ⟨124, by decide⟩ (Q2.listedAt ⟨124, by decide⟩
        (alnCheck_rep ⟨124, by decide⟩ hj hq).1))
      (colE2 ⟨81, by decide⟩ 15 hp) Q2.T124_81_2 Q2.hfix124_81_2 Q2.hinj124_81_2
      Q2.hcardT124_81_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T124_81_2 i) (Q2.hfix124_81_2 i) _)
      ?_).symm
  rw [show colData1 (⟨124, by decide⟩ : Fin 148)
        ((colE1 ⟨81, by decide⟩ 15 (transLenTr ⟨81, by decide⟩ 15 hp) : ↥(reps ⟨81, by decide⟩)) : Coordinate 1)
        T124_81 = colFn colCertDiv_124_81_15.D1 (m := 5) from colCertDiv_124_81_15.bind1,
    show colData2 (⟨124, by decide⟩ : Fin 148)
        ((colE2 ⟨81, by decide⟩ 15 hp : ↥(Q2.reps ⟨81, by decide⟩)) : Coordinate 2)
        Q2.T124_81_2 = colFn colCertDiv_124_81_15.D2 (m := 5) from colCertDiv_124_81_15.bind2]
  rw [alnId_124 j hj]
  exact fastcode_of_div ⟨124, by decide⟩ _ _ _
    ((alnId_124 j hj) ▸ Q2.listedAt (⟨124, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨124, by decide⟩ : Fin 148) hj hq).1) colCertDiv_124_81_15_match


theorem leaf_124_81_20 (hp : 20 < (Q2.transData.getD 81 []).length)
    (j : Nat) (hj : j < (repChars.getD 124 []).length)
    (hq : (normIsRep.getD 124 []).getD j false = true) :
    species (Q2.reps (⟨81, by decide⟩ : Fin 148)) (colE2 ⟨81, by decide⟩ 20 hp)
        (rowE2 (⟨124, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨81, by decide⟩ : Fin 148))
        (colE1 ⟨81, by decide⟩ 20 (transLenTr ⟨81, by decide⟩ 20 hp))
        (rowE1 (⟨124, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨124, by decide⟩ : Fin 148) ⟨81, by decide⟩ _
      (validAt ⟨124, by decide⟩ (listedAt ⟨124, by decide⟩ hj))
      (colE1 ⟨81, by decide⟩ 20 (transLenTr ⟨81, by decide⟩ 20 hp)) T124_81
      hfix124_81 hinj124_81 hcardT124_81
      (fun i => conj_mem_of_fixedPoints _ _ (T124_81 i) (hfix124_81 i) _)
      ⟨124, by decide⟩ ⟨81, by decide⟩ _
      (Q2.validAt ⟨124, by decide⟩ (Q2.listedAt ⟨124, by decide⟩
        (alnCheck_rep ⟨124, by decide⟩ hj hq).1))
      (colE2 ⟨81, by decide⟩ 20 hp) Q2.T124_81_2 Q2.hfix124_81_2 Q2.hinj124_81_2
      Q2.hcardT124_81_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T124_81_2 i) (Q2.hfix124_81_2 i) _)
      ?_).symm
  rw [show colData1 (⟨124, by decide⟩ : Fin 148)
        ((colE1 ⟨81, by decide⟩ 20 (transLenTr ⟨81, by decide⟩ 20 hp) : ↥(reps ⟨81, by decide⟩)) : Coordinate 1)
        T124_81 = colFn colCertDiv_124_81_20.D1 (m := 5) from colCertDiv_124_81_20.bind1,
    show colData2 (⟨124, by decide⟩ : Fin 148)
        ((colE2 ⟨81, by decide⟩ 20 hp : ↥(Q2.reps ⟨81, by decide⟩)) : Coordinate 2)
        Q2.T124_81_2 = colFn colCertDiv_124_81_20.D2 (m := 5) from colCertDiv_124_81_20.bind2]
  rw [alnId_124 j hj]
  exact fastcode_of_div ⟨124, by decide⟩ _ _ _
    ((alnId_124 j hj) ▸ Q2.listedAt (⟨124, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨124, by decide⟩ : Fin 148) hj hq).1) colCertDiv_124_81_20_match


theorem leaf_124_92_0 (hp : 0 < (Q2.transData.getD 92 []).length)
    (j : Nat) (hj : j < (repChars.getD 124 []).length)
    (hq : (normIsRep.getD 124 []).getD j false = true) :
    species (Q2.reps (⟨92, by decide⟩ : Fin 148)) (colE2 ⟨92, by decide⟩ 0 hp)
        (rowE2 (⟨124, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨92, by decide⟩ : Fin 148))
        (colE1 ⟨92, by decide⟩ 0 (transLenTr ⟨92, by decide⟩ 0 hp))
        (rowE1 (⟨124, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨124, by decide⟩ : Fin 148) ⟨92, by decide⟩ _
      (validAt ⟨124, by decide⟩ (listedAt ⟨124, by decide⟩ hj))
      (colE1 ⟨92, by decide⟩ 0 (transLenTr ⟨92, by decide⟩ 0 hp)) T124_92
      hfix124_92 hinj124_92 hcardT124_92
      (fun i => conj_mem_of_fixedPoints _ _ (T124_92 i) (hfix124_92 i) _)
      ⟨124, by decide⟩ ⟨92, by decide⟩ _
      (Q2.validAt ⟨124, by decide⟩ (Q2.listedAt ⟨124, by decide⟩
        (alnCheck_rep ⟨124, by decide⟩ hj hq).1))
      (colE2 ⟨92, by decide⟩ 0 hp) Q2.T124_92_2 Q2.hfix124_92_2 Q2.hinj124_92_2
      Q2.hcardT124_92_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T124_92_2 i) (Q2.hfix124_92_2 i) _)
      colCert_124_92_0.hD ?_).symm
  rw [alnId_124 j hj]


theorem leaf_124_92_1 (hp : 1 < (Q2.transData.getD 92 []).length)
    (j : Nat) (hj : j < (repChars.getD 124 []).length)
    (hq : (normIsRep.getD 124 []).getD j false = true) :
    species (Q2.reps (⟨92, by decide⟩ : Fin 148)) (colE2 ⟨92, by decide⟩ 1 hp)
        (rowE2 (⟨124, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨92, by decide⟩ : Fin 148))
        (colE1 ⟨92, by decide⟩ 1 (transLenTr ⟨92, by decide⟩ 1 hp))
        (rowE1 (⟨124, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨124, by decide⟩ : Fin 148) ⟨92, by decide⟩ _
      (validAt ⟨124, by decide⟩ (listedAt ⟨124, by decide⟩ hj))
      (colE1 ⟨92, by decide⟩ 1 (transLenTr ⟨92, by decide⟩ 1 hp)) T124_92
      hfix124_92 hinj124_92 hcardT124_92
      (fun i => conj_mem_of_fixedPoints _ _ (T124_92 i) (hfix124_92 i) _)
      ⟨124, by decide⟩ ⟨92, by decide⟩ _
      (Q2.validAt ⟨124, by decide⟩ (Q2.listedAt ⟨124, by decide⟩
        (alnCheck_rep ⟨124, by decide⟩ hj hq).1))
      (colE2 ⟨92, by decide⟩ 1 hp) Q2.T124_92_2 Q2.hfix124_92_2 Q2.hinj124_92_2
      Q2.hcardT124_92_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T124_92_2 i) (Q2.hfix124_92_2 i) _)
      colCert_124_92_1.hD ?_).symm
  rw [alnId_124 j hj]


theorem leaf_124_92_2 (hp : 2 < (Q2.transData.getD 92 []).length)
    (j : Nat) (hj : j < (repChars.getD 124 []).length)
    (hq : (normIsRep.getD 124 []).getD j false = true) :
    species (Q2.reps (⟨92, by decide⟩ : Fin 148)) (colE2 ⟨92, by decide⟩ 2 hp)
        (rowE2 (⟨124, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨92, by decide⟩ : Fin 148))
        (colE1 ⟨92, by decide⟩ 2 (transLenTr ⟨92, by decide⟩ 2 hp))
        (rowE1 (⟨124, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨124, by decide⟩ : Fin 148) ⟨92, by decide⟩ _
      (validAt ⟨124, by decide⟩ (listedAt ⟨124, by decide⟩ hj))
      (colE1 ⟨92, by decide⟩ 2 (transLenTr ⟨92, by decide⟩ 2 hp)) T124_92
      hfix124_92 hinj124_92 hcardT124_92
      (fun i => conj_mem_of_fixedPoints _ _ (T124_92 i) (hfix124_92 i) _)
      ⟨124, by decide⟩ ⟨92, by decide⟩ _
      (Q2.validAt ⟨124, by decide⟩ (Q2.listedAt ⟨124, by decide⟩
        (alnCheck_rep ⟨124, by decide⟩ hj hq).1))
      (colE2 ⟨92, by decide⟩ 2 hp) Q2.T124_92_2 Q2.hfix124_92_2 Q2.hinj124_92_2
      Q2.hcardT124_92_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T124_92_2 i) (Q2.hfix124_92_2 i) _)
      colCert_124_92_2.hD ?_).symm
  rw [alnId_124 j hj]


theorem leaf_124_92_3 (hp : 3 < (Q2.transData.getD 92 []).length)
    (j : Nat) (hj : j < (repChars.getD 124 []).length)
    (hq : (normIsRep.getD 124 []).getD j false = true) :
    species (Q2.reps (⟨92, by decide⟩ : Fin 148)) (colE2 ⟨92, by decide⟩ 3 hp)
        (rowE2 (⟨124, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨92, by decide⟩ : Fin 148))
        (colE1 ⟨92, by decide⟩ 3 (transLenTr ⟨92, by decide⟩ 3 hp))
        (rowE1 (⟨124, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨124, by decide⟩ : Fin 148) ⟨92, by decide⟩ _
      (validAt ⟨124, by decide⟩ (listedAt ⟨124, by decide⟩ hj))
      (colE1 ⟨92, by decide⟩ 3 (transLenTr ⟨92, by decide⟩ 3 hp)) T124_92
      hfix124_92 hinj124_92 hcardT124_92
      (fun i => conj_mem_of_fixedPoints _ _ (T124_92 i) (hfix124_92 i) _)
      ⟨124, by decide⟩ ⟨92, by decide⟩ _
      (Q2.validAt ⟨124, by decide⟩ (Q2.listedAt ⟨124, by decide⟩
        (alnCheck_rep ⟨124, by decide⟩ hj hq).1))
      (colE2 ⟨92, by decide⟩ 3 hp) Q2.T124_92_2 Q2.hfix124_92_2 Q2.hinj124_92_2
      Q2.hcardT124_92_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T124_92_2 i) (Q2.hfix124_92_2 i) _)
      colCert_124_92_3.hD ?_).symm
  rw [alnId_124 j hj]


theorem leaf_124_92_4 (hp : 4 < (Q2.transData.getD 92 []).length)
    (j : Nat) (hj : j < (repChars.getD 124 []).length)
    (hq : (normIsRep.getD 124 []).getD j false = true) :
    species (Q2.reps (⟨92, by decide⟩ : Fin 148)) (colE2 ⟨92, by decide⟩ 4 hp)
        (rowE2 (⟨124, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨92, by decide⟩ : Fin 148))
        (colE1 ⟨92, by decide⟩ 4 (transLenTr ⟨92, by decide⟩ 4 hp))
        (rowE1 (⟨124, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨124, by decide⟩ : Fin 148) ⟨92, by decide⟩ _
      (validAt ⟨124, by decide⟩ (listedAt ⟨124, by decide⟩ hj))
      (colE1 ⟨92, by decide⟩ 4 (transLenTr ⟨92, by decide⟩ 4 hp)) T124_92
      hfix124_92 hinj124_92 hcardT124_92
      (fun i => conj_mem_of_fixedPoints _ _ (T124_92 i) (hfix124_92 i) _)
      ⟨124, by decide⟩ ⟨92, by decide⟩ _
      (Q2.validAt ⟨124, by decide⟩ (Q2.listedAt ⟨124, by decide⟩
        (alnCheck_rep ⟨124, by decide⟩ hj hq).1))
      (colE2 ⟨92, by decide⟩ 4 hp) Q2.T124_92_2 Q2.hfix124_92_2 Q2.hinj124_92_2
      Q2.hcardT124_92_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T124_92_2 i) (Q2.hfix124_92_2 i) _)
      colCert_124_92_4.hD ?_).symm
  rw [alnId_124 j hj]


theorem leaf_124_92_5 (hp : 5 < (Q2.transData.getD 92 []).length)
    (j : Nat) (hj : j < (repChars.getD 124 []).length)
    (hq : (normIsRep.getD 124 []).getD j false = true) :
    species (Q2.reps (⟨92, by decide⟩ : Fin 148)) (colE2 ⟨92, by decide⟩ 5 hp)
        (rowE2 (⟨124, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨92, by decide⟩ : Fin 148))
        (colE1 ⟨92, by decide⟩ 5 (transLenTr ⟨92, by decide⟩ 5 hp))
        (rowE1 (⟨124, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨124, by decide⟩ : Fin 148) ⟨92, by decide⟩ _
      (validAt ⟨124, by decide⟩ (listedAt ⟨124, by decide⟩ hj))
      (colE1 ⟨92, by decide⟩ 5 (transLenTr ⟨92, by decide⟩ 5 hp)) T124_92
      hfix124_92 hinj124_92 hcardT124_92
      (fun i => conj_mem_of_fixedPoints _ _ (T124_92 i) (hfix124_92 i) _)
      ⟨124, by decide⟩ ⟨92, by decide⟩ _
      (Q2.validAt ⟨124, by decide⟩ (Q2.listedAt ⟨124, by decide⟩
        (alnCheck_rep ⟨124, by decide⟩ hj hq).1))
      (colE2 ⟨92, by decide⟩ 5 hp) Q2.T124_92_2 Q2.hfix124_92_2 Q2.hinj124_92_2
      Q2.hcardT124_92_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T124_92_2 i) (Q2.hfix124_92_2 i) _)
      ?_).symm
  rw [show colData1 (⟨124, by decide⟩ : Fin 148)
        ((colE1 ⟨92, by decide⟩ 5 (transLenTr ⟨92, by decide⟩ 5 hp) : ↥(reps ⟨92, by decide⟩)) : Coordinate 1)
        T124_92 = colFn colCertDiv_124_92_5.D1 (m := 5) from colCertDiv_124_92_5.bind1,
    show colData2 (⟨124, by decide⟩ : Fin 148)
        ((colE2 ⟨92, by decide⟩ 5 hp : ↥(Q2.reps ⟨92, by decide⟩)) : Coordinate 2)
        Q2.T124_92_2 = colFn colCertDiv_124_92_5.D2 (m := 5) from colCertDiv_124_92_5.bind2]
  rw [alnId_124 j hj]
  exact fastcode_of_div ⟨124, by decide⟩ _ _ _
    ((alnId_124 j hj) ▸ Q2.listedAt (⟨124, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨124, by decide⟩ : Fin 148) hj hq).1) colCertDiv_124_92_5_match


theorem leaf_124_92_10 (hp : 10 < (Q2.transData.getD 92 []).length)
    (j : Nat) (hj : j < (repChars.getD 124 []).length)
    (hq : (normIsRep.getD 124 []).getD j false = true) :
    species (Q2.reps (⟨92, by decide⟩ : Fin 148)) (colE2 ⟨92, by decide⟩ 10 hp)
        (rowE2 (⟨124, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨92, by decide⟩ : Fin 148))
        (colE1 ⟨92, by decide⟩ 10 (transLenTr ⟨92, by decide⟩ 10 hp))
        (rowE1 (⟨124, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨124, by decide⟩ : Fin 148) ⟨92, by decide⟩ _
      (validAt ⟨124, by decide⟩ (listedAt ⟨124, by decide⟩ hj))
      (colE1 ⟨92, by decide⟩ 10 (transLenTr ⟨92, by decide⟩ 10 hp)) T124_92
      hfix124_92 hinj124_92 hcardT124_92
      (fun i => conj_mem_of_fixedPoints _ _ (T124_92 i) (hfix124_92 i) _)
      ⟨124, by decide⟩ ⟨92, by decide⟩ _
      (Q2.validAt ⟨124, by decide⟩ (Q2.listedAt ⟨124, by decide⟩
        (alnCheck_rep ⟨124, by decide⟩ hj hq).1))
      (colE2 ⟨92, by decide⟩ 10 hp) Q2.T124_92_2 Q2.hfix124_92_2 Q2.hinj124_92_2
      Q2.hcardT124_92_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T124_92_2 i) (Q2.hfix124_92_2 i) _)
      ?_).symm
  rw [show colData1 (⟨124, by decide⟩ : Fin 148)
        ((colE1 ⟨92, by decide⟩ 10 (transLenTr ⟨92, by decide⟩ 10 hp) : ↥(reps ⟨92, by decide⟩)) : Coordinate 1)
        T124_92 = colFn colCertDiv_124_92_10.D1 (m := 5) from colCertDiv_124_92_10.bind1,
    show colData2 (⟨124, by decide⟩ : Fin 148)
        ((colE2 ⟨92, by decide⟩ 10 hp : ↥(Q2.reps ⟨92, by decide⟩)) : Coordinate 2)
        Q2.T124_92_2 = colFn colCertDiv_124_92_10.D2 (m := 5) from colCertDiv_124_92_10.bind2]
  rw [alnId_124 j hj]
  exact fastcode_of_div ⟨124, by decide⟩ _ _ _
    ((alnId_124 j hj) ▸ Q2.listedAt (⟨124, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨124, by decide⟩ : Fin 148) hj hq).1) colCertDiv_124_92_10_match


theorem leaf_124_92_15 (hp : 15 < (Q2.transData.getD 92 []).length)
    (j : Nat) (hj : j < (repChars.getD 124 []).length)
    (hq : (normIsRep.getD 124 []).getD j false = true) :
    species (Q2.reps (⟨92, by decide⟩ : Fin 148)) (colE2 ⟨92, by decide⟩ 15 hp)
        (rowE2 (⟨124, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨92, by decide⟩ : Fin 148))
        (colE1 ⟨92, by decide⟩ 15 (transLenTr ⟨92, by decide⟩ 15 hp))
        (rowE1 (⟨124, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨124, by decide⟩ : Fin 148) ⟨92, by decide⟩ _
      (validAt ⟨124, by decide⟩ (listedAt ⟨124, by decide⟩ hj))
      (colE1 ⟨92, by decide⟩ 15 (transLenTr ⟨92, by decide⟩ 15 hp)) T124_92
      hfix124_92 hinj124_92 hcardT124_92
      (fun i => conj_mem_of_fixedPoints _ _ (T124_92 i) (hfix124_92 i) _)
      ⟨124, by decide⟩ ⟨92, by decide⟩ _
      (Q2.validAt ⟨124, by decide⟩ (Q2.listedAt ⟨124, by decide⟩
        (alnCheck_rep ⟨124, by decide⟩ hj hq).1))
      (colE2 ⟨92, by decide⟩ 15 hp) Q2.T124_92_2 Q2.hfix124_92_2 Q2.hinj124_92_2
      Q2.hcardT124_92_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T124_92_2 i) (Q2.hfix124_92_2 i) _)
      ?_).symm
  rw [show colData1 (⟨124, by decide⟩ : Fin 148)
        ((colE1 ⟨92, by decide⟩ 15 (transLenTr ⟨92, by decide⟩ 15 hp) : ↥(reps ⟨92, by decide⟩)) : Coordinate 1)
        T124_92 = colFn colCertDiv_124_92_15.D1 (m := 5) from colCertDiv_124_92_15.bind1,
    show colData2 (⟨124, by decide⟩ : Fin 148)
        ((colE2 ⟨92, by decide⟩ 15 hp : ↥(Q2.reps ⟨92, by decide⟩)) : Coordinate 2)
        Q2.T124_92_2 = colFn colCertDiv_124_92_15.D2 (m := 5) from colCertDiv_124_92_15.bind2]
  rw [alnId_124 j hj]
  exact fastcode_of_div ⟨124, by decide⟩ _ _ _
    ((alnId_124 j hj) ▸ Q2.listedAt (⟨124, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨124, by decide⟩ : Fin 148) hj hq).1) colCertDiv_124_92_15_match


theorem leaf_124_92_20 (hp : 20 < (Q2.transData.getD 92 []).length)
    (j : Nat) (hj : j < (repChars.getD 124 []).length)
    (hq : (normIsRep.getD 124 []).getD j false = true) :
    species (Q2.reps (⟨92, by decide⟩ : Fin 148)) (colE2 ⟨92, by decide⟩ 20 hp)
        (rowE2 (⟨124, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨92, by decide⟩ : Fin 148))
        (colE1 ⟨92, by decide⟩ 20 (transLenTr ⟨92, by decide⟩ 20 hp))
        (rowE1 (⟨124, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨124, by decide⟩ : Fin 148) ⟨92, by decide⟩ _
      (validAt ⟨124, by decide⟩ (listedAt ⟨124, by decide⟩ hj))
      (colE1 ⟨92, by decide⟩ 20 (transLenTr ⟨92, by decide⟩ 20 hp)) T124_92
      hfix124_92 hinj124_92 hcardT124_92
      (fun i => conj_mem_of_fixedPoints _ _ (T124_92 i) (hfix124_92 i) _)
      ⟨124, by decide⟩ ⟨92, by decide⟩ _
      (Q2.validAt ⟨124, by decide⟩ (Q2.listedAt ⟨124, by decide⟩
        (alnCheck_rep ⟨124, by decide⟩ hj hq).1))
      (colE2 ⟨92, by decide⟩ 20 hp) Q2.T124_92_2 Q2.hfix124_92_2 Q2.hinj124_92_2
      Q2.hcardT124_92_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T124_92_2 i) (Q2.hfix124_92_2 i) _)
      colCert_124_92_20.hD ?_).symm
  rw [alnId_124 j hj]


theorem leaf_124_95_0 (hp : 0 < (Q2.transData.getD 95 []).length)
    (j : Nat) (hj : j < (repChars.getD 124 []).length)
    (hq : (normIsRep.getD 124 []).getD j false = true) :
    species (Q2.reps (⟨95, by decide⟩ : Fin 148)) (colE2 ⟨95, by decide⟩ 0 hp)
        (rowE2 (⟨124, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨95, by decide⟩ : Fin 148))
        (colE1 ⟨95, by decide⟩ 0 (transLenTr ⟨95, by decide⟩ 0 hp))
        (rowE1 (⟨124, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨124, by decide⟩ : Fin 148) ⟨95, by decide⟩ _
      (validAt ⟨124, by decide⟩ (listedAt ⟨124, by decide⟩ hj))
      (colE1 ⟨95, by decide⟩ 0 (transLenTr ⟨95, by decide⟩ 0 hp)) T124_95
      hfix124_95 hinj124_95 hcardT124_95
      (fun i => conj_mem_of_fixedPoints _ _ (T124_95 i) (hfix124_95 i) _)
      ⟨124, by decide⟩ ⟨95, by decide⟩ _
      (Q2.validAt ⟨124, by decide⟩ (Q2.listedAt ⟨124, by decide⟩
        (alnCheck_rep ⟨124, by decide⟩ hj hq).1))
      (colE2 ⟨95, by decide⟩ 0 hp) Q2.T124_95_2 Q2.hfix124_95_2 Q2.hinj124_95_2
      Q2.hcardT124_95_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T124_95_2 i) (Q2.hfix124_95_2 i) _)
      colCert_124_95_0.hD ?_).symm
  rw [alnId_124 j hj]


theorem leaf_124_95_1 (hp : 1 < (Q2.transData.getD 95 []).length)
    (j : Nat) (hj : j < (repChars.getD 124 []).length)
    (hq : (normIsRep.getD 124 []).getD j false = true) :
    species (Q2.reps (⟨95, by decide⟩ : Fin 148)) (colE2 ⟨95, by decide⟩ 1 hp)
        (rowE2 (⟨124, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨95, by decide⟩ : Fin 148))
        (colE1 ⟨95, by decide⟩ 1 (transLenTr ⟨95, by decide⟩ 1 hp))
        (rowE1 (⟨124, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨124, by decide⟩ : Fin 148) ⟨95, by decide⟩ _
      (validAt ⟨124, by decide⟩ (listedAt ⟨124, by decide⟩ hj))
      (colE1 ⟨95, by decide⟩ 1 (transLenTr ⟨95, by decide⟩ 1 hp)) T124_95
      hfix124_95 hinj124_95 hcardT124_95
      (fun i => conj_mem_of_fixedPoints _ _ (T124_95 i) (hfix124_95 i) _)
      ⟨124, by decide⟩ ⟨95, by decide⟩ _
      (Q2.validAt ⟨124, by decide⟩ (Q2.listedAt ⟨124, by decide⟩
        (alnCheck_rep ⟨124, by decide⟩ hj hq).1))
      (colE2 ⟨95, by decide⟩ 1 hp) Q2.T124_95_2 Q2.hfix124_95_2 Q2.hinj124_95_2
      Q2.hcardT124_95_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T124_95_2 i) (Q2.hfix124_95_2 i) _)
      colCert_124_95_1.hD ?_).symm
  rw [alnId_124 j hj]


theorem leaf_124_95_2 (hp : 2 < (Q2.transData.getD 95 []).length)
    (j : Nat) (hj : j < (repChars.getD 124 []).length)
    (hq : (normIsRep.getD 124 []).getD j false = true) :
    species (Q2.reps (⟨95, by decide⟩ : Fin 148)) (colE2 ⟨95, by decide⟩ 2 hp)
        (rowE2 (⟨124, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨95, by decide⟩ : Fin 148))
        (colE1 ⟨95, by decide⟩ 2 (transLenTr ⟨95, by decide⟩ 2 hp))
        (rowE1 (⟨124, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨124, by decide⟩ : Fin 148) ⟨95, by decide⟩ _
      (validAt ⟨124, by decide⟩ (listedAt ⟨124, by decide⟩ hj))
      (colE1 ⟨95, by decide⟩ 2 (transLenTr ⟨95, by decide⟩ 2 hp)) T124_95
      hfix124_95 hinj124_95 hcardT124_95
      (fun i => conj_mem_of_fixedPoints _ _ (T124_95 i) (hfix124_95 i) _)
      ⟨124, by decide⟩ ⟨95, by decide⟩ _
      (Q2.validAt ⟨124, by decide⟩ (Q2.listedAt ⟨124, by decide⟩
        (alnCheck_rep ⟨124, by decide⟩ hj hq).1))
      (colE2 ⟨95, by decide⟩ 2 hp) Q2.T124_95_2 Q2.hfix124_95_2 Q2.hinj124_95_2
      Q2.hcardT124_95_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T124_95_2 i) (Q2.hfix124_95_2 i) _)
      colCert_124_95_2.hD ?_).symm
  rw [alnId_124 j hj]


theorem leaf_124_95_3 (hp : 3 < (Q2.transData.getD 95 []).length)
    (j : Nat) (hj : j < (repChars.getD 124 []).length)
    (hq : (normIsRep.getD 124 []).getD j false = true) :
    species (Q2.reps (⟨95, by decide⟩ : Fin 148)) (colE2 ⟨95, by decide⟩ 3 hp)
        (rowE2 (⟨124, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨95, by decide⟩ : Fin 148))
        (colE1 ⟨95, by decide⟩ 3 (transLenTr ⟨95, by decide⟩ 3 hp))
        (rowE1 (⟨124, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨124, by decide⟩ : Fin 148) ⟨95, by decide⟩ _
      (validAt ⟨124, by decide⟩ (listedAt ⟨124, by decide⟩ hj))
      (colE1 ⟨95, by decide⟩ 3 (transLenTr ⟨95, by decide⟩ 3 hp)) T124_95
      hfix124_95 hinj124_95 hcardT124_95
      (fun i => conj_mem_of_fixedPoints _ _ (T124_95 i) (hfix124_95 i) _)
      ⟨124, by decide⟩ ⟨95, by decide⟩ _
      (Q2.validAt ⟨124, by decide⟩ (Q2.listedAt ⟨124, by decide⟩
        (alnCheck_rep ⟨124, by decide⟩ hj hq).1))
      (colE2 ⟨95, by decide⟩ 3 hp) Q2.T124_95_2 Q2.hfix124_95_2 Q2.hinj124_95_2
      Q2.hcardT124_95_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T124_95_2 i) (Q2.hfix124_95_2 i) _)
      colCert_124_95_3.hD ?_).symm
  rw [alnId_124 j hj]


theorem leaf_124_95_4 (hp : 4 < (Q2.transData.getD 95 []).length)
    (j : Nat) (hj : j < (repChars.getD 124 []).length)
    (hq : (normIsRep.getD 124 []).getD j false = true) :
    species (Q2.reps (⟨95, by decide⟩ : Fin 148)) (colE2 ⟨95, by decide⟩ 4 hp)
        (rowE2 (⟨124, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨95, by decide⟩ : Fin 148))
        (colE1 ⟨95, by decide⟩ 4 (transLenTr ⟨95, by decide⟩ 4 hp))
        (rowE1 (⟨124, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨124, by decide⟩ : Fin 148) ⟨95, by decide⟩ _
      (validAt ⟨124, by decide⟩ (listedAt ⟨124, by decide⟩ hj))
      (colE1 ⟨95, by decide⟩ 4 (transLenTr ⟨95, by decide⟩ 4 hp)) T124_95
      hfix124_95 hinj124_95 hcardT124_95
      (fun i => conj_mem_of_fixedPoints _ _ (T124_95 i) (hfix124_95 i) _)
      ⟨124, by decide⟩ ⟨95, by decide⟩ _
      (Q2.validAt ⟨124, by decide⟩ (Q2.listedAt ⟨124, by decide⟩
        (alnCheck_rep ⟨124, by decide⟩ hj hq).1))
      (colE2 ⟨95, by decide⟩ 4 hp) Q2.T124_95_2 Q2.hfix124_95_2 Q2.hinj124_95_2
      Q2.hcardT124_95_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T124_95_2 i) (Q2.hfix124_95_2 i) _)
      colCert_124_95_4.hD ?_).symm
  rw [alnId_124 j hj]


theorem leaf_124_95_5 (hp : 5 < (Q2.transData.getD 95 []).length)
    (j : Nat) (hj : j < (repChars.getD 124 []).length)
    (hq : (normIsRep.getD 124 []).getD j false = true) :
    species (Q2.reps (⟨95, by decide⟩ : Fin 148)) (colE2 ⟨95, by decide⟩ 5 hp)
        (rowE2 (⟨124, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨95, by decide⟩ : Fin 148))
        (colE1 ⟨95, by decide⟩ 5 (transLenTr ⟨95, by decide⟩ 5 hp))
        (rowE1 (⟨124, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨124, by decide⟩ : Fin 148) ⟨95, by decide⟩ _
      (validAt ⟨124, by decide⟩ (listedAt ⟨124, by decide⟩ hj))
      (colE1 ⟨95, by decide⟩ 5 (transLenTr ⟨95, by decide⟩ 5 hp)) T124_95
      hfix124_95 hinj124_95 hcardT124_95
      (fun i => conj_mem_of_fixedPoints _ _ (T124_95 i) (hfix124_95 i) _)
      ⟨124, by decide⟩ ⟨95, by decide⟩ _
      (Q2.validAt ⟨124, by decide⟩ (Q2.listedAt ⟨124, by decide⟩
        (alnCheck_rep ⟨124, by decide⟩ hj hq).1))
      (colE2 ⟨95, by decide⟩ 5 hp) Q2.T124_95_2 Q2.hfix124_95_2 Q2.hinj124_95_2
      Q2.hcardT124_95_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T124_95_2 i) (Q2.hfix124_95_2 i) _)
      colCert_124_95_5.hD ?_).symm
  rw [alnId_124 j hj]


theorem leaf_124_95_10 (hp : 10 < (Q2.transData.getD 95 []).length)
    (j : Nat) (hj : j < (repChars.getD 124 []).length)
    (hq : (normIsRep.getD 124 []).getD j false = true) :
    species (Q2.reps (⟨95, by decide⟩ : Fin 148)) (colE2 ⟨95, by decide⟩ 10 hp)
        (rowE2 (⟨124, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨95, by decide⟩ : Fin 148))
        (colE1 ⟨95, by decide⟩ 10 (transLenTr ⟨95, by decide⟩ 10 hp))
        (rowE1 (⟨124, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨124, by decide⟩ : Fin 148) ⟨95, by decide⟩ _
      (validAt ⟨124, by decide⟩ (listedAt ⟨124, by decide⟩ hj))
      (colE1 ⟨95, by decide⟩ 10 (transLenTr ⟨95, by decide⟩ 10 hp)) T124_95
      hfix124_95 hinj124_95 hcardT124_95
      (fun i => conj_mem_of_fixedPoints _ _ (T124_95 i) (hfix124_95 i) _)
      ⟨124, by decide⟩ ⟨95, by decide⟩ _
      (Q2.validAt ⟨124, by decide⟩ (Q2.listedAt ⟨124, by decide⟩
        (alnCheck_rep ⟨124, by decide⟩ hj hq).1))
      (colE2 ⟨95, by decide⟩ 10 hp) Q2.T124_95_2 Q2.hfix124_95_2 Q2.hinj124_95_2
      Q2.hcardT124_95_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T124_95_2 i) (Q2.hfix124_95_2 i) _)
      colCert_124_95_10.hD ?_).symm
  rw [alnId_124 j hj]


theorem leaf_124_95_15 (hp : 15 < (Q2.transData.getD 95 []).length)
    (j : Nat) (hj : j < (repChars.getD 124 []).length)
    (hq : (normIsRep.getD 124 []).getD j false = true) :
    species (Q2.reps (⟨95, by decide⟩ : Fin 148)) (colE2 ⟨95, by decide⟩ 15 hp)
        (rowE2 (⟨124, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨95, by decide⟩ : Fin 148))
        (colE1 ⟨95, by decide⟩ 15 (transLenTr ⟨95, by decide⟩ 15 hp))
        (rowE1 (⟨124, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨124, by decide⟩ : Fin 148) ⟨95, by decide⟩ _
      (validAt ⟨124, by decide⟩ (listedAt ⟨124, by decide⟩ hj))
      (colE1 ⟨95, by decide⟩ 15 (transLenTr ⟨95, by decide⟩ 15 hp)) T124_95
      hfix124_95 hinj124_95 hcardT124_95
      (fun i => conj_mem_of_fixedPoints _ _ (T124_95 i) (hfix124_95 i) _)
      ⟨124, by decide⟩ ⟨95, by decide⟩ _
      (Q2.validAt ⟨124, by decide⟩ (Q2.listedAt ⟨124, by decide⟩
        (alnCheck_rep ⟨124, by decide⟩ hj hq).1))
      (colE2 ⟨95, by decide⟩ 15 hp) Q2.T124_95_2 Q2.hfix124_95_2 Q2.hinj124_95_2
      Q2.hcardT124_95_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T124_95_2 i) (Q2.hfix124_95_2 i) _)
      colCert_124_95_15.hD ?_).symm
  rw [alnId_124 j hj]


theorem leaf_124_95_20 (hp : 20 < (Q2.transData.getD 95 []).length)
    (j : Nat) (hj : j < (repChars.getD 124 []).length)
    (hq : (normIsRep.getD 124 []).getD j false = true) :
    species (Q2.reps (⟨95, by decide⟩ : Fin 148)) (colE2 ⟨95, by decide⟩ 20 hp)
        (rowE2 (⟨124, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨95, by decide⟩ : Fin 148))
        (colE1 ⟨95, by decide⟩ 20 (transLenTr ⟨95, by decide⟩ 20 hp))
        (rowE1 (⟨124, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨124, by decide⟩ : Fin 148) ⟨95, by decide⟩ _
      (validAt ⟨124, by decide⟩ (listedAt ⟨124, by decide⟩ hj))
      (colE1 ⟨95, by decide⟩ 20 (transLenTr ⟨95, by decide⟩ 20 hp)) T124_95
      hfix124_95 hinj124_95 hcardT124_95
      (fun i => conj_mem_of_fixedPoints _ _ (T124_95 i) (hfix124_95 i) _)
      ⟨124, by decide⟩ ⟨95, by decide⟩ _
      (Q2.validAt ⟨124, by decide⟩ (Q2.listedAt ⟨124, by decide⟩
        (alnCheck_rep ⟨124, by decide⟩ hj hq).1))
      (colE2 ⟨95, by decide⟩ 20 hp) Q2.T124_95_2 Q2.hfix124_95_2 Q2.hinj124_95_2
      Q2.hcardT124_95_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T124_95_2 i) (Q2.hfix124_95_2 i) _)
      colCert_124_95_20.hD ?_).symm
  rw [alnId_124 j hj]


theorem leaf_124_95_25 (hp : 25 < (Q2.transData.getD 95 []).length)
    (j : Nat) (hj : j < (repChars.getD 124 []).length)
    (hq : (normIsRep.getD 124 []).getD j false = true) :
    species (Q2.reps (⟨95, by decide⟩ : Fin 148)) (colE2 ⟨95, by decide⟩ 25 hp)
        (rowE2 (⟨124, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨95, by decide⟩ : Fin 148))
        (colE1 ⟨95, by decide⟩ 25 (transLenTr ⟨95, by decide⟩ 25 hp))
        (rowE1 (⟨124, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨124, by decide⟩ : Fin 148) ⟨95, by decide⟩ _
      (validAt ⟨124, by decide⟩ (listedAt ⟨124, by decide⟩ hj))
      (colE1 ⟨95, by decide⟩ 25 (transLenTr ⟨95, by decide⟩ 25 hp)) T124_95
      hfix124_95 hinj124_95 hcardT124_95
      (fun i => conj_mem_of_fixedPoints _ _ (T124_95 i) (hfix124_95 i) _)
      ⟨124, by decide⟩ ⟨95, by decide⟩ _
      (Q2.validAt ⟨124, by decide⟩ (Q2.listedAt ⟨124, by decide⟩
        (alnCheck_rep ⟨124, by decide⟩ hj hq).1))
      (colE2 ⟨95, by decide⟩ 25 hp) Q2.T124_95_2 Q2.hfix124_95_2 Q2.hinj124_95_2
      Q2.hcardT124_95_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T124_95_2 i) (Q2.hfix124_95_2 i) _)
      ?_).symm
  rw [show colData1 (⟨124, by decide⟩ : Fin 148)
        ((colE1 ⟨95, by decide⟩ 25 (transLenTr ⟨95, by decide⟩ 25 hp) : ↥(reps ⟨95, by decide⟩)) : Coordinate 1)
        T124_95 = colFn colCertDiv_124_95_25.D1 (m := 5) from colCertDiv_124_95_25.bind1,
    show colData2 (⟨124, by decide⟩ : Fin 148)
        ((colE2 ⟨95, by decide⟩ 25 hp : ↥(Q2.reps ⟨95, by decide⟩)) : Coordinate 2)
        Q2.T124_95_2 = colFn colCertDiv_124_95_25.D2 (m := 5) from colCertDiv_124_95_25.bind2]
  rw [alnId_124 j hj]
  exact fastcode_of_div ⟨124, by decide⟩ _ _ _
    ((alnId_124 j hj) ▸ Q2.listedAt (⟨124, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨124, by decide⟩ : Fin 148) hj hq).1) colCertDiv_124_95_25_match


theorem leaf_124_95_50 (hp : 50 < (Q2.transData.getD 95 []).length)
    (j : Nat) (hj : j < (repChars.getD 124 []).length)
    (hq : (normIsRep.getD 124 []).getD j false = true) :
    species (Q2.reps (⟨95, by decide⟩ : Fin 148)) (colE2 ⟨95, by decide⟩ 50 hp)
        (rowE2 (⟨124, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨95, by decide⟩ : Fin 148))
        (colE1 ⟨95, by decide⟩ 50 (transLenTr ⟨95, by decide⟩ 50 hp))
        (rowE1 (⟨124, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨124, by decide⟩ : Fin 148) ⟨95, by decide⟩ _
      (validAt ⟨124, by decide⟩ (listedAt ⟨124, by decide⟩ hj))
      (colE1 ⟨95, by decide⟩ 50 (transLenTr ⟨95, by decide⟩ 50 hp)) T124_95
      hfix124_95 hinj124_95 hcardT124_95
      (fun i => conj_mem_of_fixedPoints _ _ (T124_95 i) (hfix124_95 i) _)
      ⟨124, by decide⟩ ⟨95, by decide⟩ _
      (Q2.validAt ⟨124, by decide⟩ (Q2.listedAt ⟨124, by decide⟩
        (alnCheck_rep ⟨124, by decide⟩ hj hq).1))
      (colE2 ⟨95, by decide⟩ 50 hp) Q2.T124_95_2 Q2.hfix124_95_2 Q2.hinj124_95_2
      Q2.hcardT124_95_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T124_95_2 i) (Q2.hfix124_95_2 i) _)
      ?_).symm
  rw [show colData1 (⟨124, by decide⟩ : Fin 148)
        ((colE1 ⟨95, by decide⟩ 50 (transLenTr ⟨95, by decide⟩ 50 hp) : ↥(reps ⟨95, by decide⟩)) : Coordinate 1)
        T124_95 = colFn colCertDiv_124_95_50.D1 (m := 5) from colCertDiv_124_95_50.bind1,
    show colData2 (⟨124, by decide⟩ : Fin 148)
        ((colE2 ⟨95, by decide⟩ 50 hp : ↥(Q2.reps ⟨95, by decide⟩)) : Coordinate 2)
        Q2.T124_95_2 = colFn colCertDiv_124_95_50.D2 (m := 5) from colCertDiv_124_95_50.bind2]
  rw [alnId_124 j hj]
  exact fastcode_of_div ⟨124, by decide⟩ _ _ _
    ((alnId_124 j hj) ▸ Q2.listedAt (⟨124, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨124, by decide⟩ : Fin 148) hj hq).1) colCertDiv_124_95_50_match


theorem leaf_124_95_75 (hp : 75 < (Q2.transData.getD 95 []).length)
    (j : Nat) (hj : j < (repChars.getD 124 []).length)
    (hq : (normIsRep.getD 124 []).getD j false = true) :
    species (Q2.reps (⟨95, by decide⟩ : Fin 148)) (colE2 ⟨95, by decide⟩ 75 hp)
        (rowE2 (⟨124, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨95, by decide⟩ : Fin 148))
        (colE1 ⟨95, by decide⟩ 75 (transLenTr ⟨95, by decide⟩ 75 hp))
        (rowE1 (⟨124, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨124, by decide⟩ : Fin 148) ⟨95, by decide⟩ _
      (validAt ⟨124, by decide⟩ (listedAt ⟨124, by decide⟩ hj))
      (colE1 ⟨95, by decide⟩ 75 (transLenTr ⟨95, by decide⟩ 75 hp)) T124_95
      hfix124_95 hinj124_95 hcardT124_95
      (fun i => conj_mem_of_fixedPoints _ _ (T124_95 i) (hfix124_95 i) _)
      ⟨124, by decide⟩ ⟨95, by decide⟩ _
      (Q2.validAt ⟨124, by decide⟩ (Q2.listedAt ⟨124, by decide⟩
        (alnCheck_rep ⟨124, by decide⟩ hj hq).1))
      (colE2 ⟨95, by decide⟩ 75 hp) Q2.T124_95_2 Q2.hfix124_95_2 Q2.hinj124_95_2
      Q2.hcardT124_95_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T124_95_2 i) (Q2.hfix124_95_2 i) _)
      ?_).symm
  rw [show colData1 (⟨124, by decide⟩ : Fin 148)
        ((colE1 ⟨95, by decide⟩ 75 (transLenTr ⟨95, by decide⟩ 75 hp) : ↥(reps ⟨95, by decide⟩)) : Coordinate 1)
        T124_95 = colFn colCertDiv_124_95_75.D1 (m := 5) from colCertDiv_124_95_75.bind1,
    show colData2 (⟨124, by decide⟩ : Fin 148)
        ((colE2 ⟨95, by decide⟩ 75 hp : ↥(Q2.reps ⟨95, by decide⟩)) : Coordinate 2)
        Q2.T124_95_2 = colFn colCertDiv_124_95_75.D2 (m := 5) from colCertDiv_124_95_75.bind2]
  rw [alnId_124 j hj]
  exact fastcode_of_div ⟨124, by decide⟩ _ _ _
    ((alnId_124 j hj) ▸ Q2.listedAt (⟨124, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨124, by decide⟩ : Fin 148) hj hq).1) colCertDiv_124_95_75_match


theorem leaf_124_95_100 (hp : 100 < (Q2.transData.getD 95 []).length)
    (j : Nat) (hj : j < (repChars.getD 124 []).length)
    (hq : (normIsRep.getD 124 []).getD j false = true) :
    species (Q2.reps (⟨95, by decide⟩ : Fin 148)) (colE2 ⟨95, by decide⟩ 100 hp)
        (rowE2 (⟨124, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨95, by decide⟩ : Fin 148))
        (colE1 ⟨95, by decide⟩ 100 (transLenTr ⟨95, by decide⟩ 100 hp))
        (rowE1 (⟨124, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨124, by decide⟩ : Fin 148) ⟨95, by decide⟩ _
      (validAt ⟨124, by decide⟩ (listedAt ⟨124, by decide⟩ hj))
      (colE1 ⟨95, by decide⟩ 100 (transLenTr ⟨95, by decide⟩ 100 hp)) T124_95
      hfix124_95 hinj124_95 hcardT124_95
      (fun i => conj_mem_of_fixedPoints _ _ (T124_95 i) (hfix124_95 i) _)
      ⟨124, by decide⟩ ⟨95, by decide⟩ _
      (Q2.validAt ⟨124, by decide⟩ (Q2.listedAt ⟨124, by decide⟩
        (alnCheck_rep ⟨124, by decide⟩ hj hq).1))
      (colE2 ⟨95, by decide⟩ 100 hp) Q2.T124_95_2 Q2.hfix124_95_2 Q2.hinj124_95_2
      Q2.hcardT124_95_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T124_95_2 i) (Q2.hfix124_95_2 i) _)
      ?_).symm
  rw [show colData1 (⟨124, by decide⟩ : Fin 148)
        ((colE1 ⟨95, by decide⟩ 100 (transLenTr ⟨95, by decide⟩ 100 hp) : ↥(reps ⟨95, by decide⟩)) : Coordinate 1)
        T124_95 = colFn colCertDiv_124_95_100.D1 (m := 5) from colCertDiv_124_95_100.bind1,
    show colData2 (⟨124, by decide⟩ : Fin 148)
        ((colE2 ⟨95, by decide⟩ 100 hp : ↥(Q2.reps ⟨95, by decide⟩)) : Coordinate 2)
        Q2.T124_95_2 = colFn colCertDiv_124_95_100.D2 (m := 5) from colCertDiv_124_95_100.bind2]
  rw [alnId_124 j hj]
  exact fastcode_of_div ⟨124, by decide⟩ _ _ _
    ((alnId_124 j hj) ▸ Q2.listedAt (⟨124, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨124, by decide⟩ : Fin 148) hj hq).1) colCertDiv_124_95_100_match


theorem leaf_124_101_0 (hp : 0 < (Q2.transData.getD 101 []).length)
    (j : Nat) (hj : j < (repChars.getD 124 []).length)
    (hq : (normIsRep.getD 124 []).getD j false = true) :
    species (Q2.reps (⟨101, by decide⟩ : Fin 148)) (colE2 ⟨101, by decide⟩ 0 hp)
        (rowE2 (⟨124, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨101, by decide⟩ : Fin 148))
        (colE1 ⟨101, by decide⟩ 0 (transLenTr ⟨101, by decide⟩ 0 hp))
        (rowE1 (⟨124, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨124, by decide⟩ : Fin 148) ⟨101, by decide⟩ _
      (validAt ⟨124, by decide⟩ (listedAt ⟨124, by decide⟩ hj))
      (colE1 ⟨101, by decide⟩ 0 (transLenTr ⟨101, by decide⟩ 0 hp)) T124_101
      hfix124_101 hinj124_101 hcardT124_101
      (fun i => conj_mem_of_fixedPoints _ _ (T124_101 i) (hfix124_101 i) _)
      ⟨124, by decide⟩ ⟨101, by decide⟩ _
      (Q2.validAt ⟨124, by decide⟩ (Q2.listedAt ⟨124, by decide⟩
        (alnCheck_rep ⟨124, by decide⟩ hj hq).1))
      (colE2 ⟨101, by decide⟩ 0 hp) Q2.T124_101_2 Q2.hfix124_101_2 Q2.hinj124_101_2
      Q2.hcardT124_101_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T124_101_2 i) (Q2.hfix124_101_2 i) _)
      colCert_124_101_0.hD ?_).symm
  rw [alnId_124 j hj]


theorem leaf_124_101_1 (hp : 1 < (Q2.transData.getD 101 []).length)
    (j : Nat) (hj : j < (repChars.getD 124 []).length)
    (hq : (normIsRep.getD 124 []).getD j false = true) :
    species (Q2.reps (⟨101, by decide⟩ : Fin 148)) (colE2 ⟨101, by decide⟩ 1 hp)
        (rowE2 (⟨124, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨101, by decide⟩ : Fin 148))
        (colE1 ⟨101, by decide⟩ 1 (transLenTr ⟨101, by decide⟩ 1 hp))
        (rowE1 (⟨124, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨124, by decide⟩ : Fin 148) ⟨101, by decide⟩ _
      (validAt ⟨124, by decide⟩ (listedAt ⟨124, by decide⟩ hj))
      (colE1 ⟨101, by decide⟩ 1 (transLenTr ⟨101, by decide⟩ 1 hp)) T124_101
      hfix124_101 hinj124_101 hcardT124_101
      (fun i => conj_mem_of_fixedPoints _ _ (T124_101 i) (hfix124_101 i) _)
      ⟨124, by decide⟩ ⟨101, by decide⟩ _
      (Q2.validAt ⟨124, by decide⟩ (Q2.listedAt ⟨124, by decide⟩
        (alnCheck_rep ⟨124, by decide⟩ hj hq).1))
      (colE2 ⟨101, by decide⟩ 1 hp) Q2.T124_101_2 Q2.hfix124_101_2 Q2.hinj124_101_2
      Q2.hcardT124_101_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T124_101_2 i) (Q2.hfix124_101_2 i) _)
      colCert_124_101_1.hD ?_).symm
  rw [alnId_124 j hj]


theorem leaf_124_101_2 (hp : 2 < (Q2.transData.getD 101 []).length)
    (j : Nat) (hj : j < (repChars.getD 124 []).length)
    (hq : (normIsRep.getD 124 []).getD j false = true) :
    species (Q2.reps (⟨101, by decide⟩ : Fin 148)) (colE2 ⟨101, by decide⟩ 2 hp)
        (rowE2 (⟨124, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨101, by decide⟩ : Fin 148))
        (colE1 ⟨101, by decide⟩ 2 (transLenTr ⟨101, by decide⟩ 2 hp))
        (rowE1 (⟨124, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨124, by decide⟩ : Fin 148) ⟨101, by decide⟩ _
      (validAt ⟨124, by decide⟩ (listedAt ⟨124, by decide⟩ hj))
      (colE1 ⟨101, by decide⟩ 2 (transLenTr ⟨101, by decide⟩ 2 hp)) T124_101
      hfix124_101 hinj124_101 hcardT124_101
      (fun i => conj_mem_of_fixedPoints _ _ (T124_101 i) (hfix124_101 i) _)
      ⟨124, by decide⟩ ⟨101, by decide⟩ _
      (Q2.validAt ⟨124, by decide⟩ (Q2.listedAt ⟨124, by decide⟩
        (alnCheck_rep ⟨124, by decide⟩ hj hq).1))
      (colE2 ⟨101, by decide⟩ 2 hp) Q2.T124_101_2 Q2.hfix124_101_2 Q2.hinj124_101_2
      Q2.hcardT124_101_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T124_101_2 i) (Q2.hfix124_101_2 i) _)
      colCert_124_101_2.hD ?_).symm
  rw [alnId_124 j hj]


theorem leaf_124_101_3 (hp : 3 < (Q2.transData.getD 101 []).length)
    (j : Nat) (hj : j < (repChars.getD 124 []).length)
    (hq : (normIsRep.getD 124 []).getD j false = true) :
    species (Q2.reps (⟨101, by decide⟩ : Fin 148)) (colE2 ⟨101, by decide⟩ 3 hp)
        (rowE2 (⟨124, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨101, by decide⟩ : Fin 148))
        (colE1 ⟨101, by decide⟩ 3 (transLenTr ⟨101, by decide⟩ 3 hp))
        (rowE1 (⟨124, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨124, by decide⟩ : Fin 148) ⟨101, by decide⟩ _
      (validAt ⟨124, by decide⟩ (listedAt ⟨124, by decide⟩ hj))
      (colE1 ⟨101, by decide⟩ 3 (transLenTr ⟨101, by decide⟩ 3 hp)) T124_101
      hfix124_101 hinj124_101 hcardT124_101
      (fun i => conj_mem_of_fixedPoints _ _ (T124_101 i) (hfix124_101 i) _)
      ⟨124, by decide⟩ ⟨101, by decide⟩ _
      (Q2.validAt ⟨124, by decide⟩ (Q2.listedAt ⟨124, by decide⟩
        (alnCheck_rep ⟨124, by decide⟩ hj hq).1))
      (colE2 ⟨101, by decide⟩ 3 hp) Q2.T124_101_2 Q2.hfix124_101_2 Q2.hinj124_101_2
      Q2.hcardT124_101_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T124_101_2 i) (Q2.hfix124_101_2 i) _)
      colCert_124_101_3.hD ?_).symm
  rw [alnId_124 j hj]


theorem leaf_124_101_4 (hp : 4 < (Q2.transData.getD 101 []).length)
    (j : Nat) (hj : j < (repChars.getD 124 []).length)
    (hq : (normIsRep.getD 124 []).getD j false = true) :
    species (Q2.reps (⟨101, by decide⟩ : Fin 148)) (colE2 ⟨101, by decide⟩ 4 hp)
        (rowE2 (⟨124, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨101, by decide⟩ : Fin 148))
        (colE1 ⟨101, by decide⟩ 4 (transLenTr ⟨101, by decide⟩ 4 hp))
        (rowE1 (⟨124, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨124, by decide⟩ : Fin 148) ⟨101, by decide⟩ _
      (validAt ⟨124, by decide⟩ (listedAt ⟨124, by decide⟩ hj))
      (colE1 ⟨101, by decide⟩ 4 (transLenTr ⟨101, by decide⟩ 4 hp)) T124_101
      hfix124_101 hinj124_101 hcardT124_101
      (fun i => conj_mem_of_fixedPoints _ _ (T124_101 i) (hfix124_101 i) _)
      ⟨124, by decide⟩ ⟨101, by decide⟩ _
      (Q2.validAt ⟨124, by decide⟩ (Q2.listedAt ⟨124, by decide⟩
        (alnCheck_rep ⟨124, by decide⟩ hj hq).1))
      (colE2 ⟨101, by decide⟩ 4 hp) Q2.T124_101_2 Q2.hfix124_101_2 Q2.hinj124_101_2
      Q2.hcardT124_101_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T124_101_2 i) (Q2.hfix124_101_2 i) _)
      colCert_124_101_4.hD ?_).symm
  rw [alnId_124 j hj]


theorem leaf_124_101_5 (hp : 5 < (Q2.transData.getD 101 []).length)
    (j : Nat) (hj : j < (repChars.getD 124 []).length)
    (hq : (normIsRep.getD 124 []).getD j false = true) :
    species (Q2.reps (⟨101, by decide⟩ : Fin 148)) (colE2 ⟨101, by decide⟩ 5 hp)
        (rowE2 (⟨124, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨101, by decide⟩ : Fin 148))
        (colE1 ⟨101, by decide⟩ 5 (transLenTr ⟨101, by decide⟩ 5 hp))
        (rowE1 (⟨124, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨124, by decide⟩ : Fin 148) ⟨101, by decide⟩ _
      (validAt ⟨124, by decide⟩ (listedAt ⟨124, by decide⟩ hj))
      (colE1 ⟨101, by decide⟩ 5 (transLenTr ⟨101, by decide⟩ 5 hp)) T124_101
      hfix124_101 hinj124_101 hcardT124_101
      (fun i => conj_mem_of_fixedPoints _ _ (T124_101 i) (hfix124_101 i) _)
      ⟨124, by decide⟩ ⟨101, by decide⟩ _
      (Q2.validAt ⟨124, by decide⟩ (Q2.listedAt ⟨124, by decide⟩
        (alnCheck_rep ⟨124, by decide⟩ hj hq).1))
      (colE2 ⟨101, by decide⟩ 5 hp) Q2.T124_101_2 Q2.hfix124_101_2 Q2.hinj124_101_2
      Q2.hcardT124_101_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T124_101_2 i) (Q2.hfix124_101_2 i) _)
      ?_).symm
  rw [show colData1 (⟨124, by decide⟩ : Fin 148)
        ((colE1 ⟨101, by decide⟩ 5 (transLenTr ⟨101, by decide⟩ 5 hp) : ↥(reps ⟨101, by decide⟩)) : Coordinate 1)
        T124_101 = colFn colCertDiv_124_101_5.D1 (m := 5) from colCertDiv_124_101_5.bind1,
    show colData2 (⟨124, by decide⟩ : Fin 148)
        ((colE2 ⟨101, by decide⟩ 5 hp : ↥(Q2.reps ⟨101, by decide⟩)) : Coordinate 2)
        Q2.T124_101_2 = colFn colCertDiv_124_101_5.D2 (m := 5) from colCertDiv_124_101_5.bind2]
  rw [alnId_124 j hj]
  exact fastcode_of_div ⟨124, by decide⟩ _ _ _
    ((alnId_124 j hj) ▸ Q2.listedAt (⟨124, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨124, by decide⟩ : Fin 148) hj hq).1) colCertDiv_124_101_5_match


theorem leaf_124_101_10 (hp : 10 < (Q2.transData.getD 101 []).length)
    (j : Nat) (hj : j < (repChars.getD 124 []).length)
    (hq : (normIsRep.getD 124 []).getD j false = true) :
    species (Q2.reps (⟨101, by decide⟩ : Fin 148)) (colE2 ⟨101, by decide⟩ 10 hp)
        (rowE2 (⟨124, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨101, by decide⟩ : Fin 148))
        (colE1 ⟨101, by decide⟩ 10 (transLenTr ⟨101, by decide⟩ 10 hp))
        (rowE1 (⟨124, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨124, by decide⟩ : Fin 148) ⟨101, by decide⟩ _
      (validAt ⟨124, by decide⟩ (listedAt ⟨124, by decide⟩ hj))
      (colE1 ⟨101, by decide⟩ 10 (transLenTr ⟨101, by decide⟩ 10 hp)) T124_101
      hfix124_101 hinj124_101 hcardT124_101
      (fun i => conj_mem_of_fixedPoints _ _ (T124_101 i) (hfix124_101 i) _)
      ⟨124, by decide⟩ ⟨101, by decide⟩ _
      (Q2.validAt ⟨124, by decide⟩ (Q2.listedAt ⟨124, by decide⟩
        (alnCheck_rep ⟨124, by decide⟩ hj hq).1))
      (colE2 ⟨101, by decide⟩ 10 hp) Q2.T124_101_2 Q2.hfix124_101_2 Q2.hinj124_101_2
      Q2.hcardT124_101_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T124_101_2 i) (Q2.hfix124_101_2 i) _)
      ?_).symm
  rw [show colData1 (⟨124, by decide⟩ : Fin 148)
        ((colE1 ⟨101, by decide⟩ 10 (transLenTr ⟨101, by decide⟩ 10 hp) : ↥(reps ⟨101, by decide⟩)) : Coordinate 1)
        T124_101 = colFn colCertDiv_124_101_10.D1 (m := 5) from colCertDiv_124_101_10.bind1,
    show colData2 (⟨124, by decide⟩ : Fin 148)
        ((colE2 ⟨101, by decide⟩ 10 hp : ↥(Q2.reps ⟨101, by decide⟩)) : Coordinate 2)
        Q2.T124_101_2 = colFn colCertDiv_124_101_10.D2 (m := 5) from colCertDiv_124_101_10.bind2]
  rw [alnId_124 j hj]
  exact fastcode_of_div ⟨124, by decide⟩ _ _ _
    ((alnId_124 j hj) ▸ Q2.listedAt (⟨124, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨124, by decide⟩ : Fin 148) hj hq).1) colCertDiv_124_101_10_match


theorem leaf_124_101_15 (hp : 15 < (Q2.transData.getD 101 []).length)
    (j : Nat) (hj : j < (repChars.getD 124 []).length)
    (hq : (normIsRep.getD 124 []).getD j false = true) :
    species (Q2.reps (⟨101, by decide⟩ : Fin 148)) (colE2 ⟨101, by decide⟩ 15 hp)
        (rowE2 (⟨124, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨101, by decide⟩ : Fin 148))
        (colE1 ⟨101, by decide⟩ 15 (transLenTr ⟨101, by decide⟩ 15 hp))
        (rowE1 (⟨124, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨124, by decide⟩ : Fin 148) ⟨101, by decide⟩ _
      (validAt ⟨124, by decide⟩ (listedAt ⟨124, by decide⟩ hj))
      (colE1 ⟨101, by decide⟩ 15 (transLenTr ⟨101, by decide⟩ 15 hp)) T124_101
      hfix124_101 hinj124_101 hcardT124_101
      (fun i => conj_mem_of_fixedPoints _ _ (T124_101 i) (hfix124_101 i) _)
      ⟨124, by decide⟩ ⟨101, by decide⟩ _
      (Q2.validAt ⟨124, by decide⟩ (Q2.listedAt ⟨124, by decide⟩
        (alnCheck_rep ⟨124, by decide⟩ hj hq).1))
      (colE2 ⟨101, by decide⟩ 15 hp) Q2.T124_101_2 Q2.hfix124_101_2 Q2.hinj124_101_2
      Q2.hcardT124_101_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T124_101_2 i) (Q2.hfix124_101_2 i) _)
      ?_).symm
  rw [show colData1 (⟨124, by decide⟩ : Fin 148)
        ((colE1 ⟨101, by decide⟩ 15 (transLenTr ⟨101, by decide⟩ 15 hp) : ↥(reps ⟨101, by decide⟩)) : Coordinate 1)
        T124_101 = colFn colCertDiv_124_101_15.D1 (m := 5) from colCertDiv_124_101_15.bind1,
    show colData2 (⟨124, by decide⟩ : Fin 148)
        ((colE2 ⟨101, by decide⟩ 15 hp : ↥(Q2.reps ⟨101, by decide⟩)) : Coordinate 2)
        Q2.T124_101_2 = colFn colCertDiv_124_101_15.D2 (m := 5) from colCertDiv_124_101_15.bind2]
  rw [alnId_124 j hj]
  exact fastcode_of_div ⟨124, by decide⟩ _ _ _
    ((alnId_124 j hj) ▸ Q2.listedAt (⟨124, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨124, by decide⟩ : Fin 148) hj hq).1) colCertDiv_124_101_15_match


theorem leaf_124_101_20 (hp : 20 < (Q2.transData.getD 101 []).length)
    (j : Nat) (hj : j < (repChars.getD 124 []).length)
    (hq : (normIsRep.getD 124 []).getD j false = true) :
    species (Q2.reps (⟨101, by decide⟩ : Fin 148)) (colE2 ⟨101, by decide⟩ 20 hp)
        (rowE2 (⟨124, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨101, by decide⟩ : Fin 148))
        (colE1 ⟨101, by decide⟩ 20 (transLenTr ⟨101, by decide⟩ 20 hp))
        (rowE1 (⟨124, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨124, by decide⟩ : Fin 148) ⟨101, by decide⟩ _
      (validAt ⟨124, by decide⟩ (listedAt ⟨124, by decide⟩ hj))
      (colE1 ⟨101, by decide⟩ 20 (transLenTr ⟨101, by decide⟩ 20 hp)) T124_101
      hfix124_101 hinj124_101 hcardT124_101
      (fun i => conj_mem_of_fixedPoints _ _ (T124_101 i) (hfix124_101 i) _)
      ⟨124, by decide⟩ ⟨101, by decide⟩ _
      (Q2.validAt ⟨124, by decide⟩ (Q2.listedAt ⟨124, by decide⟩
        (alnCheck_rep ⟨124, by decide⟩ hj hq).1))
      (colE2 ⟨101, by decide⟩ 20 hp) Q2.T124_101_2 Q2.hfix124_101_2 Q2.hinj124_101_2
      Q2.hcardT124_101_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T124_101_2 i) (Q2.hfix124_101_2 i) _)
      ?_).symm
  rw [show colData1 (⟨124, by decide⟩ : Fin 148)
        ((colE1 ⟨101, by decide⟩ 20 (transLenTr ⟨101, by decide⟩ 20 hp) : ↥(reps ⟨101, by decide⟩)) : Coordinate 1)
        T124_101 = colFn colCertDiv_124_101_20.D1 (m := 5) from colCertDiv_124_101_20.bind1,
    show colData2 (⟨124, by decide⟩ : Fin 148)
        ((colE2 ⟨101, by decide⟩ 20 hp : ↥(Q2.reps ⟨101, by decide⟩)) : Coordinate 2)
        Q2.T124_101_2 = colFn colCertDiv_124_101_20.D2 (m := 5) from colCertDiv_124_101_20.bind2]
  rw [alnId_124 j hj]
  exact fastcode_of_div ⟨124, by decide⟩ _ _ _
    ((alnId_124 j hj) ▸ Q2.listedAt (⟨124, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨124, by decide⟩ : Fin 148) hj hq).1) colCertDiv_124_101_20_match


theorem leaf_124_109_0 (hp : 0 < (Q2.transData.getD 109 []).length)
    (j : Nat) (hj : j < (repChars.getD 124 []).length)
    (hq : (normIsRep.getD 124 []).getD j false = true) :
    species (Q2.reps (⟨109, by decide⟩ : Fin 148)) (colE2 ⟨109, by decide⟩ 0 hp)
        (rowE2 (⟨124, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨109, by decide⟩ : Fin 148))
        (colE1 ⟨109, by decide⟩ 0 (transLenTr ⟨109, by decide⟩ 0 hp))
        (rowE1 (⟨124, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨124, by decide⟩ : Fin 148) ⟨109, by decide⟩ _
      (validAt ⟨124, by decide⟩ (listedAt ⟨124, by decide⟩ hj))
      (colE1 ⟨109, by decide⟩ 0 (transLenTr ⟨109, by decide⟩ 0 hp)) T124_109
      hfix124_109 hinj124_109 hcardT124_109
      (fun i => conj_mem_of_fixedPoints _ _ (T124_109 i) (hfix124_109 i) _)
      ⟨124, by decide⟩ ⟨109, by decide⟩ _
      (Q2.validAt ⟨124, by decide⟩ (Q2.listedAt ⟨124, by decide⟩
        (alnCheck_rep ⟨124, by decide⟩ hj hq).1))
      (colE2 ⟨109, by decide⟩ 0 hp) Q2.T124_109_2 Q2.hfix124_109_2 Q2.hinj124_109_2
      Q2.hcardT124_109_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T124_109_2 i) (Q2.hfix124_109_2 i) _)
      colCert_124_109_0.hD ?_).symm
  rw [alnId_124 j hj]


theorem leaf_124_109_1 (hp : 1 < (Q2.transData.getD 109 []).length)
    (j : Nat) (hj : j < (repChars.getD 124 []).length)
    (hq : (normIsRep.getD 124 []).getD j false = true) :
    species (Q2.reps (⟨109, by decide⟩ : Fin 148)) (colE2 ⟨109, by decide⟩ 1 hp)
        (rowE2 (⟨124, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨109, by decide⟩ : Fin 148))
        (colE1 ⟨109, by decide⟩ 1 (transLenTr ⟨109, by decide⟩ 1 hp))
        (rowE1 (⟨124, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨124, by decide⟩ : Fin 148) ⟨109, by decide⟩ _
      (validAt ⟨124, by decide⟩ (listedAt ⟨124, by decide⟩ hj))
      (colE1 ⟨109, by decide⟩ 1 (transLenTr ⟨109, by decide⟩ 1 hp)) T124_109
      hfix124_109 hinj124_109 hcardT124_109
      (fun i => conj_mem_of_fixedPoints _ _ (T124_109 i) (hfix124_109 i) _)
      ⟨124, by decide⟩ ⟨109, by decide⟩ _
      (Q2.validAt ⟨124, by decide⟩ (Q2.listedAt ⟨124, by decide⟩
        (alnCheck_rep ⟨124, by decide⟩ hj hq).1))
      (colE2 ⟨109, by decide⟩ 1 hp) Q2.T124_109_2 Q2.hfix124_109_2 Q2.hinj124_109_2
      Q2.hcardT124_109_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T124_109_2 i) (Q2.hfix124_109_2 i) _)
      colCert_124_109_1.hD ?_).symm
  rw [alnId_124 j hj]


theorem leaf_124_109_2 (hp : 2 < (Q2.transData.getD 109 []).length)
    (j : Nat) (hj : j < (repChars.getD 124 []).length)
    (hq : (normIsRep.getD 124 []).getD j false = true) :
    species (Q2.reps (⟨109, by decide⟩ : Fin 148)) (colE2 ⟨109, by decide⟩ 2 hp)
        (rowE2 (⟨124, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨109, by decide⟩ : Fin 148))
        (colE1 ⟨109, by decide⟩ 2 (transLenTr ⟨109, by decide⟩ 2 hp))
        (rowE1 (⟨124, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨124, by decide⟩ : Fin 148) ⟨109, by decide⟩ _
      (validAt ⟨124, by decide⟩ (listedAt ⟨124, by decide⟩ hj))
      (colE1 ⟨109, by decide⟩ 2 (transLenTr ⟨109, by decide⟩ 2 hp)) T124_109
      hfix124_109 hinj124_109 hcardT124_109
      (fun i => conj_mem_of_fixedPoints _ _ (T124_109 i) (hfix124_109 i) _)
      ⟨124, by decide⟩ ⟨109, by decide⟩ _
      (Q2.validAt ⟨124, by decide⟩ (Q2.listedAt ⟨124, by decide⟩
        (alnCheck_rep ⟨124, by decide⟩ hj hq).1))
      (colE2 ⟨109, by decide⟩ 2 hp) Q2.T124_109_2 Q2.hfix124_109_2 Q2.hinj124_109_2
      Q2.hcardT124_109_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T124_109_2 i) (Q2.hfix124_109_2 i) _)
      colCert_124_109_2.hD ?_).symm
  rw [alnId_124 j hj]


theorem leaf_124_109_3 (hp : 3 < (Q2.transData.getD 109 []).length)
    (j : Nat) (hj : j < (repChars.getD 124 []).length)
    (hq : (normIsRep.getD 124 []).getD j false = true) :
    species (Q2.reps (⟨109, by decide⟩ : Fin 148)) (colE2 ⟨109, by decide⟩ 3 hp)
        (rowE2 (⟨124, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨109, by decide⟩ : Fin 148))
        (colE1 ⟨109, by decide⟩ 3 (transLenTr ⟨109, by decide⟩ 3 hp))
        (rowE1 (⟨124, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨124, by decide⟩ : Fin 148) ⟨109, by decide⟩ _
      (validAt ⟨124, by decide⟩ (listedAt ⟨124, by decide⟩ hj))
      (colE1 ⟨109, by decide⟩ 3 (transLenTr ⟨109, by decide⟩ 3 hp)) T124_109
      hfix124_109 hinj124_109 hcardT124_109
      (fun i => conj_mem_of_fixedPoints _ _ (T124_109 i) (hfix124_109 i) _)
      ⟨124, by decide⟩ ⟨109, by decide⟩ _
      (Q2.validAt ⟨124, by decide⟩ (Q2.listedAt ⟨124, by decide⟩
        (alnCheck_rep ⟨124, by decide⟩ hj hq).1))
      (colE2 ⟨109, by decide⟩ 3 hp) Q2.T124_109_2 Q2.hfix124_109_2 Q2.hinj124_109_2
      Q2.hcardT124_109_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T124_109_2 i) (Q2.hfix124_109_2 i) _)
      colCert_124_109_3.hD ?_).symm
  rw [alnId_124 j hj]


theorem leaf_124_109_4 (hp : 4 < (Q2.transData.getD 109 []).length)
    (j : Nat) (hj : j < (repChars.getD 124 []).length)
    (hq : (normIsRep.getD 124 []).getD j false = true) :
    species (Q2.reps (⟨109, by decide⟩ : Fin 148)) (colE2 ⟨109, by decide⟩ 4 hp)
        (rowE2 (⟨124, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨109, by decide⟩ : Fin 148))
        (colE1 ⟨109, by decide⟩ 4 (transLenTr ⟨109, by decide⟩ 4 hp))
        (rowE1 (⟨124, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨124, by decide⟩ : Fin 148) ⟨109, by decide⟩ _
      (validAt ⟨124, by decide⟩ (listedAt ⟨124, by decide⟩ hj))
      (colE1 ⟨109, by decide⟩ 4 (transLenTr ⟨109, by decide⟩ 4 hp)) T124_109
      hfix124_109 hinj124_109 hcardT124_109
      (fun i => conj_mem_of_fixedPoints _ _ (T124_109 i) (hfix124_109 i) _)
      ⟨124, by decide⟩ ⟨109, by decide⟩ _
      (Q2.validAt ⟨124, by decide⟩ (Q2.listedAt ⟨124, by decide⟩
        (alnCheck_rep ⟨124, by decide⟩ hj hq).1))
      (colE2 ⟨109, by decide⟩ 4 hp) Q2.T124_109_2 Q2.hfix124_109_2 Q2.hinj124_109_2
      Q2.hcardT124_109_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T124_109_2 i) (Q2.hfix124_109_2 i) _)
      colCert_124_109_4.hD ?_).symm
  rw [alnId_124 j hj]


theorem leaf_124_109_5 (hp : 5 < (Q2.transData.getD 109 []).length)
    (j : Nat) (hj : j < (repChars.getD 124 []).length)
    (hq : (normIsRep.getD 124 []).getD j false = true) :
    species (Q2.reps (⟨109, by decide⟩ : Fin 148)) (colE2 ⟨109, by decide⟩ 5 hp)
        (rowE2 (⟨124, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨109, by decide⟩ : Fin 148))
        (colE1 ⟨109, by decide⟩ 5 (transLenTr ⟨109, by decide⟩ 5 hp))
        (rowE1 (⟨124, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨124, by decide⟩ : Fin 148) ⟨109, by decide⟩ _
      (validAt ⟨124, by decide⟩ (listedAt ⟨124, by decide⟩ hj))
      (colE1 ⟨109, by decide⟩ 5 (transLenTr ⟨109, by decide⟩ 5 hp)) T124_109
      hfix124_109 hinj124_109 hcardT124_109
      (fun i => conj_mem_of_fixedPoints _ _ (T124_109 i) (hfix124_109 i) _)
      ⟨124, by decide⟩ ⟨109, by decide⟩ _
      (Q2.validAt ⟨124, by decide⟩ (Q2.listedAt ⟨124, by decide⟩
        (alnCheck_rep ⟨124, by decide⟩ hj hq).1))
      (colE2 ⟨109, by decide⟩ 5 hp) Q2.T124_109_2 Q2.hfix124_109_2 Q2.hinj124_109_2
      Q2.hcardT124_109_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T124_109_2 i) (Q2.hfix124_109_2 i) _)
      ?_).symm
  rw [show colData1 (⟨124, by decide⟩ : Fin 148)
        ((colE1 ⟨109, by decide⟩ 5 (transLenTr ⟨109, by decide⟩ 5 hp) : ↥(reps ⟨109, by decide⟩)) : Coordinate 1)
        T124_109 = colFn colCertDiv_124_109_5.D1 (m := 5) from colCertDiv_124_109_5.bind1,
    show colData2 (⟨124, by decide⟩ : Fin 148)
        ((colE2 ⟨109, by decide⟩ 5 hp : ↥(Q2.reps ⟨109, by decide⟩)) : Coordinate 2)
        Q2.T124_109_2 = colFn colCertDiv_124_109_5.D2 (m := 5) from colCertDiv_124_109_5.bind2]
  rw [alnId_124 j hj]
  exact fastcode_of_div ⟨124, by decide⟩ _ _ _
    ((alnId_124 j hj) ▸ Q2.listedAt (⟨124, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨124, by decide⟩ : Fin 148) hj hq).1) colCertDiv_124_109_5_match


theorem leaf_124_109_10 (hp : 10 < (Q2.transData.getD 109 []).length)
    (j : Nat) (hj : j < (repChars.getD 124 []).length)
    (hq : (normIsRep.getD 124 []).getD j false = true) :
    species (Q2.reps (⟨109, by decide⟩ : Fin 148)) (colE2 ⟨109, by decide⟩ 10 hp)
        (rowE2 (⟨124, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨109, by decide⟩ : Fin 148))
        (colE1 ⟨109, by decide⟩ 10 (transLenTr ⟨109, by decide⟩ 10 hp))
        (rowE1 (⟨124, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨124, by decide⟩ : Fin 148) ⟨109, by decide⟩ _
      (validAt ⟨124, by decide⟩ (listedAt ⟨124, by decide⟩ hj))
      (colE1 ⟨109, by decide⟩ 10 (transLenTr ⟨109, by decide⟩ 10 hp)) T124_109
      hfix124_109 hinj124_109 hcardT124_109
      (fun i => conj_mem_of_fixedPoints _ _ (T124_109 i) (hfix124_109 i) _)
      ⟨124, by decide⟩ ⟨109, by decide⟩ _
      (Q2.validAt ⟨124, by decide⟩ (Q2.listedAt ⟨124, by decide⟩
        (alnCheck_rep ⟨124, by decide⟩ hj hq).1))
      (colE2 ⟨109, by decide⟩ 10 hp) Q2.T124_109_2 Q2.hfix124_109_2 Q2.hinj124_109_2
      Q2.hcardT124_109_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T124_109_2 i) (Q2.hfix124_109_2 i) _)
      ?_).symm
  rw [show colData1 (⟨124, by decide⟩ : Fin 148)
        ((colE1 ⟨109, by decide⟩ 10 (transLenTr ⟨109, by decide⟩ 10 hp) : ↥(reps ⟨109, by decide⟩)) : Coordinate 1)
        T124_109 = colFn colCertDiv_124_109_10.D1 (m := 5) from colCertDiv_124_109_10.bind1,
    show colData2 (⟨124, by decide⟩ : Fin 148)
        ((colE2 ⟨109, by decide⟩ 10 hp : ↥(Q2.reps ⟨109, by decide⟩)) : Coordinate 2)
        Q2.T124_109_2 = colFn colCertDiv_124_109_10.D2 (m := 5) from colCertDiv_124_109_10.bind2]
  rw [alnId_124 j hj]
  exact fastcode_of_div ⟨124, by decide⟩ _ _ _
    ((alnId_124 j hj) ▸ Q2.listedAt (⟨124, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨124, by decide⟩ : Fin 148) hj hq).1) colCertDiv_124_109_10_match


theorem leaf_124_109_15 (hp : 15 < (Q2.transData.getD 109 []).length)
    (j : Nat) (hj : j < (repChars.getD 124 []).length)
    (hq : (normIsRep.getD 124 []).getD j false = true) :
    species (Q2.reps (⟨109, by decide⟩ : Fin 148)) (colE2 ⟨109, by decide⟩ 15 hp)
        (rowE2 (⟨124, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨109, by decide⟩ : Fin 148))
        (colE1 ⟨109, by decide⟩ 15 (transLenTr ⟨109, by decide⟩ 15 hp))
        (rowE1 (⟨124, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨124, by decide⟩ : Fin 148) ⟨109, by decide⟩ _
      (validAt ⟨124, by decide⟩ (listedAt ⟨124, by decide⟩ hj))
      (colE1 ⟨109, by decide⟩ 15 (transLenTr ⟨109, by decide⟩ 15 hp)) T124_109
      hfix124_109 hinj124_109 hcardT124_109
      (fun i => conj_mem_of_fixedPoints _ _ (T124_109 i) (hfix124_109 i) _)
      ⟨124, by decide⟩ ⟨109, by decide⟩ _
      (Q2.validAt ⟨124, by decide⟩ (Q2.listedAt ⟨124, by decide⟩
        (alnCheck_rep ⟨124, by decide⟩ hj hq).1))
      (colE2 ⟨109, by decide⟩ 15 hp) Q2.T124_109_2 Q2.hfix124_109_2 Q2.hinj124_109_2
      Q2.hcardT124_109_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T124_109_2 i) (Q2.hfix124_109_2 i) _)
      ?_).symm
  rw [show colData1 (⟨124, by decide⟩ : Fin 148)
        ((colE1 ⟨109, by decide⟩ 15 (transLenTr ⟨109, by decide⟩ 15 hp) : ↥(reps ⟨109, by decide⟩)) : Coordinate 1)
        T124_109 = colFn colCertDiv_124_109_15.D1 (m := 5) from colCertDiv_124_109_15.bind1,
    show colData2 (⟨124, by decide⟩ : Fin 148)
        ((colE2 ⟨109, by decide⟩ 15 hp : ↥(Q2.reps ⟨109, by decide⟩)) : Coordinate 2)
        Q2.T124_109_2 = colFn colCertDiv_124_109_15.D2 (m := 5) from colCertDiv_124_109_15.bind2]
  rw [alnId_124 j hj]
  exact fastcode_of_div ⟨124, by decide⟩ _ _ _
    ((alnId_124 j hj) ▸ Q2.listedAt (⟨124, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨124, by decide⟩ : Fin 148) hj hq).1) colCertDiv_124_109_15_match


theorem leaf_124_109_20 (hp : 20 < (Q2.transData.getD 109 []).length)
    (j : Nat) (hj : j < (repChars.getD 124 []).length)
    (hq : (normIsRep.getD 124 []).getD j false = true) :
    species (Q2.reps (⟨109, by decide⟩ : Fin 148)) (colE2 ⟨109, by decide⟩ 20 hp)
        (rowE2 (⟨124, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨109, by decide⟩ : Fin 148))
        (colE1 ⟨109, by decide⟩ 20 (transLenTr ⟨109, by decide⟩ 20 hp))
        (rowE1 (⟨124, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨124, by decide⟩ : Fin 148) ⟨109, by decide⟩ _
      (validAt ⟨124, by decide⟩ (listedAt ⟨124, by decide⟩ hj))
      (colE1 ⟨109, by decide⟩ 20 (transLenTr ⟨109, by decide⟩ 20 hp)) T124_109
      hfix124_109 hinj124_109 hcardT124_109
      (fun i => conj_mem_of_fixedPoints _ _ (T124_109 i) (hfix124_109 i) _)
      ⟨124, by decide⟩ ⟨109, by decide⟩ _
      (Q2.validAt ⟨124, by decide⟩ (Q2.listedAt ⟨124, by decide⟩
        (alnCheck_rep ⟨124, by decide⟩ hj hq).1))
      (colE2 ⟨109, by decide⟩ 20 hp) Q2.T124_109_2 Q2.hfix124_109_2 Q2.hinj124_109_2
      Q2.hcardT124_109_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T124_109_2 i) (Q2.hfix124_109_2 i) _)
      ?_).symm
  rw [show colData1 (⟨124, by decide⟩ : Fin 148)
        ((colE1 ⟨109, by decide⟩ 20 (transLenTr ⟨109, by decide⟩ 20 hp) : ↥(reps ⟨109, by decide⟩)) : Coordinate 1)
        T124_109 = colFn colCertDiv_124_109_20.D1 (m := 5) from colCertDiv_124_109_20.bind1,
    show colData2 (⟨124, by decide⟩ : Fin 148)
        ((colE2 ⟨109, by decide⟩ 20 hp : ↥(Q2.reps ⟨109, by decide⟩)) : Coordinate 2)
        Q2.T124_109_2 = colFn colCertDiv_124_109_20.D2 (m := 5) from colCertDiv_124_109_20.bind2]
  rw [alnId_124 j hj]
  exact fastcode_of_div ⟨124, by decide⟩ _ _ _
    ((alnId_124 j hj) ▸ Q2.listedAt (⟨124, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨124, by decide⟩ : Fin 148) hj hq).1) colCertDiv_124_109_20_match


theorem leaf_124_113_0 (hp : 0 < (Q2.transData.getD 113 []).length)
    (j : Nat) (hj : j < (repChars.getD 124 []).length)
    (hq : (normIsRep.getD 124 []).getD j false = true) :
    species (Q2.reps (⟨113, by decide⟩ : Fin 148)) (colE2 ⟨113, by decide⟩ 0 hp)
        (rowE2 (⟨124, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨113, by decide⟩ : Fin 148))
        (colE1 ⟨113, by decide⟩ 0 (transLenTr ⟨113, by decide⟩ 0 hp))
        (rowE1 (⟨124, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨124, by decide⟩ : Fin 148) ⟨113, by decide⟩ _
      (validAt ⟨124, by decide⟩ (listedAt ⟨124, by decide⟩ hj))
      (colE1 ⟨113, by decide⟩ 0 (transLenTr ⟨113, by decide⟩ 0 hp)) T124_113
      hfix124_113 hinj124_113 hcardT124_113
      (fun i => conj_mem_of_fixedPoints _ _ (T124_113 i) (hfix124_113 i) _)
      ⟨124, by decide⟩ ⟨113, by decide⟩ _
      (Q2.validAt ⟨124, by decide⟩ (Q2.listedAt ⟨124, by decide⟩
        (alnCheck_rep ⟨124, by decide⟩ hj hq).1))
      (colE2 ⟨113, by decide⟩ 0 hp) Q2.T124_113_2 Q2.hfix124_113_2 Q2.hinj124_113_2
      Q2.hcardT124_113_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T124_113_2 i) (Q2.hfix124_113_2 i) _)
      colCert_124_113_0.hD ?_).symm
  rw [alnId_124 j hj]


theorem leaf_124_113_1 (hp : 1 < (Q2.transData.getD 113 []).length)
    (j : Nat) (hj : j < (repChars.getD 124 []).length)
    (hq : (normIsRep.getD 124 []).getD j false = true) :
    species (Q2.reps (⟨113, by decide⟩ : Fin 148)) (colE2 ⟨113, by decide⟩ 1 hp)
        (rowE2 (⟨124, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨113, by decide⟩ : Fin 148))
        (colE1 ⟨113, by decide⟩ 1 (transLenTr ⟨113, by decide⟩ 1 hp))
        (rowE1 (⟨124, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨124, by decide⟩ : Fin 148) ⟨113, by decide⟩ _
      (validAt ⟨124, by decide⟩ (listedAt ⟨124, by decide⟩ hj))
      (colE1 ⟨113, by decide⟩ 1 (transLenTr ⟨113, by decide⟩ 1 hp)) T124_113
      hfix124_113 hinj124_113 hcardT124_113
      (fun i => conj_mem_of_fixedPoints _ _ (T124_113 i) (hfix124_113 i) _)
      ⟨124, by decide⟩ ⟨113, by decide⟩ _
      (Q2.validAt ⟨124, by decide⟩ (Q2.listedAt ⟨124, by decide⟩
        (alnCheck_rep ⟨124, by decide⟩ hj hq).1))
      (colE2 ⟨113, by decide⟩ 1 hp) Q2.T124_113_2 Q2.hfix124_113_2 Q2.hinj124_113_2
      Q2.hcardT124_113_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T124_113_2 i) (Q2.hfix124_113_2 i) _)
      colCert_124_113_1.hD ?_).symm
  rw [alnId_124 j hj]


theorem leaf_124_113_2 (hp : 2 < (Q2.transData.getD 113 []).length)
    (j : Nat) (hj : j < (repChars.getD 124 []).length)
    (hq : (normIsRep.getD 124 []).getD j false = true) :
    species (Q2.reps (⟨113, by decide⟩ : Fin 148)) (colE2 ⟨113, by decide⟩ 2 hp)
        (rowE2 (⟨124, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨113, by decide⟩ : Fin 148))
        (colE1 ⟨113, by decide⟩ 2 (transLenTr ⟨113, by decide⟩ 2 hp))
        (rowE1 (⟨124, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨124, by decide⟩ : Fin 148) ⟨113, by decide⟩ _
      (validAt ⟨124, by decide⟩ (listedAt ⟨124, by decide⟩ hj))
      (colE1 ⟨113, by decide⟩ 2 (transLenTr ⟨113, by decide⟩ 2 hp)) T124_113
      hfix124_113 hinj124_113 hcardT124_113
      (fun i => conj_mem_of_fixedPoints _ _ (T124_113 i) (hfix124_113 i) _)
      ⟨124, by decide⟩ ⟨113, by decide⟩ _
      (Q2.validAt ⟨124, by decide⟩ (Q2.listedAt ⟨124, by decide⟩
        (alnCheck_rep ⟨124, by decide⟩ hj hq).1))
      (colE2 ⟨113, by decide⟩ 2 hp) Q2.T124_113_2 Q2.hfix124_113_2 Q2.hinj124_113_2
      Q2.hcardT124_113_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T124_113_2 i) (Q2.hfix124_113_2 i) _)
      colCert_124_113_2.hD ?_).symm
  rw [alnId_124 j hj]


theorem leaf_124_113_3 (hp : 3 < (Q2.transData.getD 113 []).length)
    (j : Nat) (hj : j < (repChars.getD 124 []).length)
    (hq : (normIsRep.getD 124 []).getD j false = true) :
    species (Q2.reps (⟨113, by decide⟩ : Fin 148)) (colE2 ⟨113, by decide⟩ 3 hp)
        (rowE2 (⟨124, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨113, by decide⟩ : Fin 148))
        (colE1 ⟨113, by decide⟩ 3 (transLenTr ⟨113, by decide⟩ 3 hp))
        (rowE1 (⟨124, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨124, by decide⟩ : Fin 148) ⟨113, by decide⟩ _
      (validAt ⟨124, by decide⟩ (listedAt ⟨124, by decide⟩ hj))
      (colE1 ⟨113, by decide⟩ 3 (transLenTr ⟨113, by decide⟩ 3 hp)) T124_113
      hfix124_113 hinj124_113 hcardT124_113
      (fun i => conj_mem_of_fixedPoints _ _ (T124_113 i) (hfix124_113 i) _)
      ⟨124, by decide⟩ ⟨113, by decide⟩ _
      (Q2.validAt ⟨124, by decide⟩ (Q2.listedAt ⟨124, by decide⟩
        (alnCheck_rep ⟨124, by decide⟩ hj hq).1))
      (colE2 ⟨113, by decide⟩ 3 hp) Q2.T124_113_2 Q2.hfix124_113_2 Q2.hinj124_113_2
      Q2.hcardT124_113_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T124_113_2 i) (Q2.hfix124_113_2 i) _)
      colCert_124_113_3.hD ?_).symm
  rw [alnId_124 j hj]


theorem leaf_124_113_4 (hp : 4 < (Q2.transData.getD 113 []).length)
    (j : Nat) (hj : j < (repChars.getD 124 []).length)
    (hq : (normIsRep.getD 124 []).getD j false = true) :
    species (Q2.reps (⟨113, by decide⟩ : Fin 148)) (colE2 ⟨113, by decide⟩ 4 hp)
        (rowE2 (⟨124, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨113, by decide⟩ : Fin 148))
        (colE1 ⟨113, by decide⟩ 4 (transLenTr ⟨113, by decide⟩ 4 hp))
        (rowE1 (⟨124, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨124, by decide⟩ : Fin 148) ⟨113, by decide⟩ _
      (validAt ⟨124, by decide⟩ (listedAt ⟨124, by decide⟩ hj))
      (colE1 ⟨113, by decide⟩ 4 (transLenTr ⟨113, by decide⟩ 4 hp)) T124_113
      hfix124_113 hinj124_113 hcardT124_113
      (fun i => conj_mem_of_fixedPoints _ _ (T124_113 i) (hfix124_113 i) _)
      ⟨124, by decide⟩ ⟨113, by decide⟩ _
      (Q2.validAt ⟨124, by decide⟩ (Q2.listedAt ⟨124, by decide⟩
        (alnCheck_rep ⟨124, by decide⟩ hj hq).1))
      (colE2 ⟨113, by decide⟩ 4 hp) Q2.T124_113_2 Q2.hfix124_113_2 Q2.hinj124_113_2
      Q2.hcardT124_113_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T124_113_2 i) (Q2.hfix124_113_2 i) _)
      colCert_124_113_4.hD ?_).symm
  rw [alnId_124 j hj]


theorem leaf_124_113_5 (hp : 5 < (Q2.transData.getD 113 []).length)
    (j : Nat) (hj : j < (repChars.getD 124 []).length)
    (hq : (normIsRep.getD 124 []).getD j false = true) :
    species (Q2.reps (⟨113, by decide⟩ : Fin 148)) (colE2 ⟨113, by decide⟩ 5 hp)
        (rowE2 (⟨124, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨113, by decide⟩ : Fin 148))
        (colE1 ⟨113, by decide⟩ 5 (transLenTr ⟨113, by decide⟩ 5 hp))
        (rowE1 (⟨124, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨124, by decide⟩ : Fin 148) ⟨113, by decide⟩ _
      (validAt ⟨124, by decide⟩ (listedAt ⟨124, by decide⟩ hj))
      (colE1 ⟨113, by decide⟩ 5 (transLenTr ⟨113, by decide⟩ 5 hp)) T124_113
      hfix124_113 hinj124_113 hcardT124_113
      (fun i => conj_mem_of_fixedPoints _ _ (T124_113 i) (hfix124_113 i) _)
      ⟨124, by decide⟩ ⟨113, by decide⟩ _
      (Q2.validAt ⟨124, by decide⟩ (Q2.listedAt ⟨124, by decide⟩
        (alnCheck_rep ⟨124, by decide⟩ hj hq).1))
      (colE2 ⟨113, by decide⟩ 5 hp) Q2.T124_113_2 Q2.hfix124_113_2 Q2.hinj124_113_2
      Q2.hcardT124_113_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T124_113_2 i) (Q2.hfix124_113_2 i) _)
      colCert_124_113_5.hD ?_).symm
  rw [alnId_124 j hj]


theorem leaf_124_113_10 (hp : 10 < (Q2.transData.getD 113 []).length)
    (j : Nat) (hj : j < (repChars.getD 124 []).length)
    (hq : (normIsRep.getD 124 []).getD j false = true) :
    species (Q2.reps (⟨113, by decide⟩ : Fin 148)) (colE2 ⟨113, by decide⟩ 10 hp)
        (rowE2 (⟨124, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨113, by decide⟩ : Fin 148))
        (colE1 ⟨113, by decide⟩ 10 (transLenTr ⟨113, by decide⟩ 10 hp))
        (rowE1 (⟨124, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨124, by decide⟩ : Fin 148) ⟨113, by decide⟩ _
      (validAt ⟨124, by decide⟩ (listedAt ⟨124, by decide⟩ hj))
      (colE1 ⟨113, by decide⟩ 10 (transLenTr ⟨113, by decide⟩ 10 hp)) T124_113
      hfix124_113 hinj124_113 hcardT124_113
      (fun i => conj_mem_of_fixedPoints _ _ (T124_113 i) (hfix124_113 i) _)
      ⟨124, by decide⟩ ⟨113, by decide⟩ _
      (Q2.validAt ⟨124, by decide⟩ (Q2.listedAt ⟨124, by decide⟩
        (alnCheck_rep ⟨124, by decide⟩ hj hq).1))
      (colE2 ⟨113, by decide⟩ 10 hp) Q2.T124_113_2 Q2.hfix124_113_2 Q2.hinj124_113_2
      Q2.hcardT124_113_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T124_113_2 i) (Q2.hfix124_113_2 i) _)
      ?_).symm
  rw [show colData1 (⟨124, by decide⟩ : Fin 148)
        ((colE1 ⟨113, by decide⟩ 10 (transLenTr ⟨113, by decide⟩ 10 hp) : ↥(reps ⟨113, by decide⟩)) : Coordinate 1)
        T124_113 = colFn colCertDiv_124_113_10.D1 (m := 5) from colCertDiv_124_113_10.bind1,
    show colData2 (⟨124, by decide⟩ : Fin 148)
        ((colE2 ⟨113, by decide⟩ 10 hp : ↥(Q2.reps ⟨113, by decide⟩)) : Coordinate 2)
        Q2.T124_113_2 = colFn colCertDiv_124_113_10.D2 (m := 5) from colCertDiv_124_113_10.bind2]
  rw [alnId_124 j hj]
  exact fastcode_of_div ⟨124, by decide⟩ _ _ _
    ((alnId_124 j hj) ▸ Q2.listedAt (⟨124, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨124, by decide⟩ : Fin 148) hj hq).1) colCertDiv_124_113_10_match


theorem leaf_124_113_15 (hp : 15 < (Q2.transData.getD 113 []).length)
    (j : Nat) (hj : j < (repChars.getD 124 []).length)
    (hq : (normIsRep.getD 124 []).getD j false = true) :
    species (Q2.reps (⟨113, by decide⟩ : Fin 148)) (colE2 ⟨113, by decide⟩ 15 hp)
        (rowE2 (⟨124, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨113, by decide⟩ : Fin 148))
        (colE1 ⟨113, by decide⟩ 15 (transLenTr ⟨113, by decide⟩ 15 hp))
        (rowE1 (⟨124, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨124, by decide⟩ : Fin 148) ⟨113, by decide⟩ _
      (validAt ⟨124, by decide⟩ (listedAt ⟨124, by decide⟩ hj))
      (colE1 ⟨113, by decide⟩ 15 (transLenTr ⟨113, by decide⟩ 15 hp)) T124_113
      hfix124_113 hinj124_113 hcardT124_113
      (fun i => conj_mem_of_fixedPoints _ _ (T124_113 i) (hfix124_113 i) _)
      ⟨124, by decide⟩ ⟨113, by decide⟩ _
      (Q2.validAt ⟨124, by decide⟩ (Q2.listedAt ⟨124, by decide⟩
        (alnCheck_rep ⟨124, by decide⟩ hj hq).1))
      (colE2 ⟨113, by decide⟩ 15 hp) Q2.T124_113_2 Q2.hfix124_113_2 Q2.hinj124_113_2
      Q2.hcardT124_113_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T124_113_2 i) (Q2.hfix124_113_2 i) _)
      ?_).symm
  rw [show colData1 (⟨124, by decide⟩ : Fin 148)
        ((colE1 ⟨113, by decide⟩ 15 (transLenTr ⟨113, by decide⟩ 15 hp) : ↥(reps ⟨113, by decide⟩)) : Coordinate 1)
        T124_113 = colFn colCertDiv_124_113_15.D1 (m := 5) from colCertDiv_124_113_15.bind1,
    show colData2 (⟨124, by decide⟩ : Fin 148)
        ((colE2 ⟨113, by decide⟩ 15 hp : ↥(Q2.reps ⟨113, by decide⟩)) : Coordinate 2)
        Q2.T124_113_2 = colFn colCertDiv_124_113_15.D2 (m := 5) from colCertDiv_124_113_15.bind2]
  rw [alnId_124 j hj]
  exact fastcode_of_div ⟨124, by decide⟩ _ _ _
    ((alnId_124 j hj) ▸ Q2.listedAt (⟨124, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨124, by decide⟩ : Fin 148) hj hq).1) colCertDiv_124_113_15_match


end LeanDring.P5Presentation
