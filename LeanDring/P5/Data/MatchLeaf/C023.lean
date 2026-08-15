/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Data.ColCdd.C003
import LeanDring.P5.Data.ColRestCheap.C020
import LeanDring.P5.Data.ColRestCheap.C021
import LeanDring.P5.Data.ColRestCheap.C022
import LeanDring.P5.Data.ColRestCheap.C023
import LeanDring.P5.Data.ColRestCheap.C024
import LeanDring.P5.Data.ColTau.C001
import LeanDring.P5.Data.EntryK.C025
import LeanDring.P5.Data.EntryK.C026
import LeanDring.P5.Certificate.RingIsomorphism.MatchCore
import LeanDring.P5.Data.SpeciesDiv.C031
import LeanDring.P5.Data.SpeciesDiv.C032
import LeanDring.P5.Certificate.SpeciesTable.Twin2.SpeciesTau.Chunk02

/-! # Stage-5 leaves, chunk 22 (auto-emitted).  -/

namespace LeanDring.P5Presentation

open MulAction Finset LeanDring.DRing LeanDring.MonGSet

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.style.longLine false

theorem leaf_116_57_24 (hp : 24 < (Q2.transData.getD 57 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨57, by decide⟩ : Fin 148)) (colE2 ⟨57, by decide⟩ 24 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨57, by decide⟩ : Fin 148))
        (colE1 ⟨57, by decide⟩ 24 (transLenTr ⟨57, by decide⟩ 24 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨116, by decide⟩ : Fin 148) ⟨57, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨57, by decide⟩ 24 (transLenTr ⟨57, by decide⟩ 24 hp)) T116_57
      hfix116_57 hinj116_57 hcardT116_57
      (fun i => conj_mem_of_fixedPoints _ _ (T116_57 i) (hfix116_57 i) _)
      ⟨116, by decide⟩ ⟨57, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨57, by decide⟩ 24 hp) Q2.T116_57_2 Q2.hfix116_57_2 Q2.hinj116_57_2
      Q2.hcardT116_57_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_57_2 i) (Q2.hfix116_57_2 i) _)
      ?_).symm
  rw [show colData1 (⟨116, by decide⟩ : Fin 148)
        ((colE1 ⟨57, by decide⟩ 24 (transLenTr ⟨57, by decide⟩ 24 hp) : ↥(reps ⟨57, by decide⟩)) : Coordinate 1)
        T116_57 = colFn colCertDiv_116_57_24.D1 (m := 5) from colCertDiv_116_57_24.bind1,
    show colData2 (⟨116, by decide⟩ : Fin 148)
        ((colE2 ⟨57, by decide⟩ 24 hp : ↥(Q2.reps ⟨57, by decide⟩)) : Coordinate 2)
        Q2.T116_57_2 = colFn colCertDiv_116_57_24.D2 (m := 5) from colCertDiv_116_57_24.bind2]
  rw [alnId_116 j hj]
  exact fastcode_of_div ⟨116, by decide⟩ _ _ _
    ((alnId_116 j hj) ▸ Q2.listedAt (⟨116, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨116, by decide⟩ : Fin 148) hj hq).1) colCertDiv_116_57_24_match


theorem leaf_116_58_0 (hp : 0 < (Q2.transData.getD 58 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨58, by decide⟩ : Fin 148)) (colE2 ⟨58, by decide⟩ 0 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨58, by decide⟩ : Fin 148))
        (colE1 ⟨58, by decide⟩ 0 (transLenTr ⟨58, by decide⟩ 0 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨58, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨58, by decide⟩ 0 (transLenTr ⟨58, by decide⟩ 0 hp)) T116_58
      hfix116_58 hinj116_58 hcardT116_58
      (fun i => conj_mem_of_fixedPoints _ _ (T116_58 i) (hfix116_58 i) _)
      ⟨116, by decide⟩ ⟨58, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨58, by decide⟩ 0 hp) Q2.T116_58_2 Q2.hfix116_58_2 Q2.hinj116_58_2
      Q2.hcardT116_58_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_58_2 i) (Q2.hfix116_58_2 i) _)
      colCert_116_58_0.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_58_1 (hp : 1 < (Q2.transData.getD 58 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨58, by decide⟩ : Fin 148)) (colE2 ⟨58, by decide⟩ 1 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨58, by decide⟩ : Fin 148))
        (colE1 ⟨58, by decide⟩ 1 (transLenTr ⟨58, by decide⟩ 1 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨58, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨58, by decide⟩ 1 (transLenTr ⟨58, by decide⟩ 1 hp)) T116_58
      hfix116_58 hinj116_58 hcardT116_58
      (fun i => conj_mem_of_fixedPoints _ _ (T116_58 i) (hfix116_58 i) _)
      ⟨116, by decide⟩ ⟨58, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨58, by decide⟩ 1 hp) Q2.T116_58_2 Q2.hfix116_58_2 Q2.hinj116_58_2
      Q2.hcardT116_58_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_58_2 i) (Q2.hfix116_58_2 i) _)
      colCert_116_58_1.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_58_2 (hp : 2 < (Q2.transData.getD 58 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨58, by decide⟩ : Fin 148)) (colE2 ⟨58, by decide⟩ 2 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨58, by decide⟩ : Fin 148))
        (colE1 ⟨58, by decide⟩ 2 (transLenTr ⟨58, by decide⟩ 2 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨58, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨58, by decide⟩ 2 (transLenTr ⟨58, by decide⟩ 2 hp)) T116_58
      hfix116_58 hinj116_58 hcardT116_58
      (fun i => conj_mem_of_fixedPoints _ _ (T116_58 i) (hfix116_58 i) _)
      ⟨116, by decide⟩ ⟨58, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨58, by decide⟩ 2 hp) Q2.T116_58_2 Q2.hfix116_58_2 Q2.hinj116_58_2
      Q2.hcardT116_58_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_58_2 i) (Q2.hfix116_58_2 i) _)
      colCert_116_58_2.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_58_3 (hp : 3 < (Q2.transData.getD 58 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨58, by decide⟩ : Fin 148)) (colE2 ⟨58, by decide⟩ 3 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨58, by decide⟩ : Fin 148))
        (colE1 ⟨58, by decide⟩ 3 (transLenTr ⟨58, by decide⟩ 3 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨58, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨58, by decide⟩ 3 (transLenTr ⟨58, by decide⟩ 3 hp)) T116_58
      hfix116_58 hinj116_58 hcardT116_58
      (fun i => conj_mem_of_fixedPoints _ _ (T116_58 i) (hfix116_58 i) _)
      ⟨116, by decide⟩ ⟨58, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨58, by decide⟩ 3 hp) Q2.T116_58_2 Q2.hfix116_58_2 Q2.hinj116_58_2
      Q2.hcardT116_58_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_58_2 i) (Q2.hfix116_58_2 i) _)
      colCert_116_58_3.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_58_4 (hp : 4 < (Q2.transData.getD 58 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨58, by decide⟩ : Fin 148)) (colE2 ⟨58, by decide⟩ 4 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨58, by decide⟩ : Fin 148))
        (colE1 ⟨58, by decide⟩ 4 (transLenTr ⟨58, by decide⟩ 4 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨58, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨58, by decide⟩ 4 (transLenTr ⟨58, by decide⟩ 4 hp)) T116_58
      hfix116_58 hinj116_58 hcardT116_58
      (fun i => conj_mem_of_fixedPoints _ _ (T116_58 i) (hfix116_58 i) _)
      ⟨116, by decide⟩ ⟨58, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨58, by decide⟩ 4 hp) Q2.T116_58_2 Q2.hfix116_58_2 Q2.hinj116_58_2
      Q2.hcardT116_58_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_58_2 i) (Q2.hfix116_58_2 i) _)
      colCert_116_58_4.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_58_5 (hp : 5 < (Q2.transData.getD 58 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨58, by decide⟩ : Fin 148)) (colE2 ⟨58, by decide⟩ 5 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨58, by decide⟩ : Fin 148))
        (colE1 ⟨58, by decide⟩ 5 (transLenTr ⟨58, by decide⟩ 5 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨116, by decide⟩ : Fin 148) ⟨58, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨58, by decide⟩ 5 (transLenTr ⟨58, by decide⟩ 5 hp)) T116_58
      hfix116_58 hinj116_58 hcardT116_58
      (fun i => conj_mem_of_fixedPoints _ _ (T116_58 i) (hfix116_58 i) _)
      ⟨116, by decide⟩ ⟨58, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨58, by decide⟩ 5 hp) Q2.T116_58_2 Q2.hfix116_58_2 Q2.hinj116_58_2
      Q2.hcardT116_58_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_58_2 i) (Q2.hfix116_58_2 i) _)
      ?_).symm
  rw [show colData1 (⟨116, by decide⟩ : Fin 148)
        ((colE1 ⟨58, by decide⟩ 5 (transLenTr ⟨58, by decide⟩ 5 hp) : ↥(reps ⟨58, by decide⟩)) : Coordinate 1)
        T116_58 = colFn colCertDiv_116_58_5.D1 (m := 5) from colCertDiv_116_58_5.bind1,
    show colData2 (⟨116, by decide⟩ : Fin 148)
        ((colE2 ⟨58, by decide⟩ 5 hp : ↥(Q2.reps ⟨58, by decide⟩)) : Coordinate 2)
        Q2.T116_58_2 = colFn colCertDiv_116_58_5.D2 (m := 5) from colCertDiv_116_58_5.bind2]
  rw [alnId_116 j hj]
  exact fastcode_of_div ⟨116, by decide⟩ _ _ _
    ((alnId_116 j hj) ▸ Q2.listedAt (⟨116, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨116, by decide⟩ : Fin 148) hj hq).1) colCertDiv_116_58_5_match


theorem leaf_116_58_6 (hp : 6 < (Q2.transData.getD 58 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨58, by decide⟩ : Fin 148)) (colE2 ⟨58, by decide⟩ 6 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨58, by decide⟩ : Fin 148))
        (colE1 ⟨58, by decide⟩ 6 (transLenTr ⟨58, by decide⟩ 6 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨116, by decide⟩ : Fin 148) ⟨58, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨58, by decide⟩ 6 (transLenTr ⟨58, by decide⟩ 6 hp)) T116_58
      hfix116_58 hinj116_58 hcardT116_58
      (fun i => conj_mem_of_fixedPoints _ _ (T116_58 i) (hfix116_58 i) _)
      ⟨116, by decide⟩ ⟨58, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨58, by decide⟩ 6 hp) Q2.T116_58_2 Q2.hfix116_58_2 Q2.hinj116_58_2
      Q2.hcardT116_58_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_58_2 i) (Q2.hfix116_58_2 i) _)
      ?_).symm
  rw [show colData1 (⟨116, by decide⟩ : Fin 148)
        ((colE1 ⟨58, by decide⟩ 6 (transLenTr ⟨58, by decide⟩ 6 hp) : ↥(reps ⟨58, by decide⟩)) : Coordinate 1)
        T116_58 = colFn colCertDiv_116_58_6.D1 (m := 5) from colCertDiv_116_58_6.bind1,
    show colData2 (⟨116, by decide⟩ : Fin 148)
        ((colE2 ⟨58, by decide⟩ 6 hp : ↥(Q2.reps ⟨58, by decide⟩)) : Coordinate 2)
        Q2.T116_58_2 = colFn colCertDiv_116_58_6.D2 (m := 5) from colCertDiv_116_58_6.bind2]
  rw [alnId_116 j hj]
  exact fastcode_of_div ⟨116, by decide⟩ _ _ _
    ((alnId_116 j hj) ▸ Q2.listedAt (⟨116, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨116, by decide⟩ : Fin 148) hj hq).1) colCertDiv_116_58_6_match


theorem leaf_116_58_7 (hp : 7 < (Q2.transData.getD 58 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨58, by decide⟩ : Fin 148)) (colE2 ⟨58, by decide⟩ 7 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨58, by decide⟩ : Fin 148))
        (colE1 ⟨58, by decide⟩ 7 (transLenTr ⟨58, by decide⟩ 7 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨116, by decide⟩ : Fin 148) ⟨58, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨58, by decide⟩ 7 (transLenTr ⟨58, by decide⟩ 7 hp)) T116_58
      hfix116_58 hinj116_58 hcardT116_58
      (fun i => conj_mem_of_fixedPoints _ _ (T116_58 i) (hfix116_58 i) _)
      ⟨116, by decide⟩ ⟨58, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨58, by decide⟩ 7 hp) Q2.T116_58_2 Q2.hfix116_58_2 Q2.hinj116_58_2
      Q2.hcardT116_58_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_58_2 i) (Q2.hfix116_58_2 i) _)
      ?_).symm
  rw [show colData1 (⟨116, by decide⟩ : Fin 148)
        ((colE1 ⟨58, by decide⟩ 7 (transLenTr ⟨58, by decide⟩ 7 hp) : ↥(reps ⟨58, by decide⟩)) : Coordinate 1)
        T116_58 = colFn colCertDiv_116_58_7.D1 (m := 5) from colCertDiv_116_58_7.bind1,
    show colData2 (⟨116, by decide⟩ : Fin 148)
        ((colE2 ⟨58, by decide⟩ 7 hp : ↥(Q2.reps ⟨58, by decide⟩)) : Coordinate 2)
        Q2.T116_58_2 = colFn colCertDiv_116_58_7.D2 (m := 5) from colCertDiv_116_58_7.bind2]
  rw [alnId_116 j hj]
  exact fastcode_of_div ⟨116, by decide⟩ _ _ _
    ((alnId_116 j hj) ▸ Q2.listedAt (⟨116, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨116, by decide⟩ : Fin 148) hj hq).1) colCertDiv_116_58_7_match


theorem leaf_116_58_8 (hp : 8 < (Q2.transData.getD 58 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨58, by decide⟩ : Fin 148)) (colE2 ⟨58, by decide⟩ 8 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨58, by decide⟩ : Fin 148))
        (colE1 ⟨58, by decide⟩ 8 (transLenTr ⟨58, by decide⟩ 8 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨116, by decide⟩ : Fin 148) ⟨58, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨58, by decide⟩ 8 (transLenTr ⟨58, by decide⟩ 8 hp)) T116_58
      hfix116_58 hinj116_58 hcardT116_58
      (fun i => conj_mem_of_fixedPoints _ _ (T116_58 i) (hfix116_58 i) _)
      ⟨116, by decide⟩ ⟨58, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨58, by decide⟩ 8 hp) Q2.T116_58_2 Q2.hfix116_58_2 Q2.hinj116_58_2
      Q2.hcardT116_58_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_58_2 i) (Q2.hfix116_58_2 i) _)
      ?_).symm
  rw [show colData1 (⟨116, by decide⟩ : Fin 148)
        ((colE1 ⟨58, by decide⟩ 8 (transLenTr ⟨58, by decide⟩ 8 hp) : ↥(reps ⟨58, by decide⟩)) : Coordinate 1)
        T116_58 = colFn colCertDiv_116_58_8.D1 (m := 5) from colCertDiv_116_58_8.bind1,
    show colData2 (⟨116, by decide⟩ : Fin 148)
        ((colE2 ⟨58, by decide⟩ 8 hp : ↥(Q2.reps ⟨58, by decide⟩)) : Coordinate 2)
        Q2.T116_58_2 = colFn colCertDiv_116_58_8.D2 (m := 5) from colCertDiv_116_58_8.bind2]
  rw [alnId_116 j hj]
  exact fastcode_of_div ⟨116, by decide⟩ _ _ _
    ((alnId_116 j hj) ▸ Q2.listedAt (⟨116, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨116, by decide⟩ : Fin 148) hj hq).1) colCertDiv_116_58_8_match


theorem leaf_116_58_9 (hp : 9 < (Q2.transData.getD 58 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨58, by decide⟩ : Fin 148)) (colE2 ⟨58, by decide⟩ 9 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨58, by decide⟩ : Fin 148))
        (colE1 ⟨58, by decide⟩ 9 (transLenTr ⟨58, by decide⟩ 9 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨116, by decide⟩ : Fin 148) ⟨58, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨58, by decide⟩ 9 (transLenTr ⟨58, by decide⟩ 9 hp)) T116_58
      hfix116_58 hinj116_58 hcardT116_58
      (fun i => conj_mem_of_fixedPoints _ _ (T116_58 i) (hfix116_58 i) _)
      ⟨116, by decide⟩ ⟨58, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨58, by decide⟩ 9 hp) Q2.T116_58_2 Q2.hfix116_58_2 Q2.hinj116_58_2
      Q2.hcardT116_58_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_58_2 i) (Q2.hfix116_58_2 i) _)
      ?_).symm
  rw [show colData1 (⟨116, by decide⟩ : Fin 148)
        ((colE1 ⟨58, by decide⟩ 9 (transLenTr ⟨58, by decide⟩ 9 hp) : ↥(reps ⟨58, by decide⟩)) : Coordinate 1)
        T116_58 = colFn colCertDiv_116_58_9.D1 (m := 5) from colCertDiv_116_58_9.bind1,
    show colData2 (⟨116, by decide⟩ : Fin 148)
        ((colE2 ⟨58, by decide⟩ 9 hp : ↥(Q2.reps ⟨58, by decide⟩)) : Coordinate 2)
        Q2.T116_58_2 = colFn colCertDiv_116_58_9.D2 (m := 5) from colCertDiv_116_58_9.bind2]
  rw [alnId_116 j hj]
  exact fastcode_of_div ⟨116, by decide⟩ _ _ _
    ((alnId_116 j hj) ▸ Q2.listedAt (⟨116, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨116, by decide⟩ : Fin 148) hj hq).1) colCertDiv_116_58_9_match


theorem leaf_116_58_10 (hp : 10 < (Q2.transData.getD 58 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨58, by decide⟩ : Fin 148)) (colE2 ⟨58, by decide⟩ 10 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨58, by decide⟩ : Fin 148))
        (colE1 ⟨58, by decide⟩ 10 (transLenTr ⟨58, by decide⟩ 10 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨116, by decide⟩ : Fin 148) ⟨58, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨58, by decide⟩ 10 (transLenTr ⟨58, by decide⟩ 10 hp)) T116_58
      hfix116_58 hinj116_58 hcardT116_58
      (fun i => conj_mem_of_fixedPoints _ _ (T116_58 i) (hfix116_58 i) _)
      ⟨116, by decide⟩ ⟨58, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨58, by decide⟩ 10 hp) Q2.T116_58_2 Q2.hfix116_58_2 Q2.hinj116_58_2
      Q2.hcardT116_58_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_58_2 i) (Q2.hfix116_58_2 i) _)
      ?_).symm
  rw [show colData1 (⟨116, by decide⟩ : Fin 148)
        ((colE1 ⟨58, by decide⟩ 10 (transLenTr ⟨58, by decide⟩ 10 hp) : ↥(reps ⟨58, by decide⟩)) : Coordinate 1)
        T116_58 = colFn colCertDiv_116_58_10.D1 (m := 5) from colCertDiv_116_58_10.bind1,
    show colData2 (⟨116, by decide⟩ : Fin 148)
        ((colE2 ⟨58, by decide⟩ 10 hp : ↥(Q2.reps ⟨58, by decide⟩)) : Coordinate 2)
        Q2.T116_58_2 = colFn colCertDiv_116_58_10.D2 (m := 5) from colCertDiv_116_58_10.bind2]
  rw [alnId_116 j hj]
  exact fastcode_of_div ⟨116, by decide⟩ _ _ _
    ((alnId_116 j hj) ▸ Q2.listedAt (⟨116, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨116, by decide⟩ : Fin 148) hj hq).1) colCertDiv_116_58_10_match


theorem leaf_116_58_11 (hp : 11 < (Q2.transData.getD 58 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨58, by decide⟩ : Fin 148)) (colE2 ⟨58, by decide⟩ 11 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨58, by decide⟩ : Fin 148))
        (colE1 ⟨58, by decide⟩ 11 (transLenTr ⟨58, by decide⟩ 11 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨116, by decide⟩ : Fin 148) ⟨58, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨58, by decide⟩ 11 (transLenTr ⟨58, by decide⟩ 11 hp)) T116_58
      hfix116_58 hinj116_58 hcardT116_58
      (fun i => conj_mem_of_fixedPoints _ _ (T116_58 i) (hfix116_58 i) _)
      ⟨116, by decide⟩ ⟨58, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨58, by decide⟩ 11 hp) Q2.T116_58_2 Q2.hfix116_58_2 Q2.hinj116_58_2
      Q2.hcardT116_58_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_58_2 i) (Q2.hfix116_58_2 i) _)
      ?_).symm
  rw [show colData1 (⟨116, by decide⟩ : Fin 148)
        ((colE1 ⟨58, by decide⟩ 11 (transLenTr ⟨58, by decide⟩ 11 hp) : ↥(reps ⟨58, by decide⟩)) : Coordinate 1)
        T116_58 = colFn colCertDiv_116_58_11.D1 (m := 5) from colCertDiv_116_58_11.bind1,
    show colData2 (⟨116, by decide⟩ : Fin 148)
        ((colE2 ⟨58, by decide⟩ 11 hp : ↥(Q2.reps ⟨58, by decide⟩)) : Coordinate 2)
        Q2.T116_58_2 = colFn colCertDiv_116_58_11.D2 (m := 5) from colCertDiv_116_58_11.bind2]
  rw [alnId_116 j hj]
  exact fastcode_of_div ⟨116, by decide⟩ _ _ _
    ((alnId_116 j hj) ▸ Q2.listedAt (⟨116, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨116, by decide⟩ : Fin 148) hj hq).1) colCertDiv_116_58_11_match


theorem leaf_116_58_12 (hp : 12 < (Q2.transData.getD 58 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨58, by decide⟩ : Fin 148)) (colE2 ⟨58, by decide⟩ 12 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨58, by decide⟩ : Fin 148))
        (colE1 ⟨58, by decide⟩ 12 (transLenTr ⟨58, by decide⟩ 12 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨116, by decide⟩ : Fin 148) ⟨58, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨58, by decide⟩ 12 (transLenTr ⟨58, by decide⟩ 12 hp)) T116_58
      hfix116_58 hinj116_58 hcardT116_58
      (fun i => conj_mem_of_fixedPoints _ _ (T116_58 i) (hfix116_58 i) _)
      ⟨116, by decide⟩ ⟨58, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨58, by decide⟩ 12 hp) Q2.T116_58_2 Q2.hfix116_58_2 Q2.hinj116_58_2
      Q2.hcardT116_58_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_58_2 i) (Q2.hfix116_58_2 i) _)
      ?_).symm
  rw [show colData1 (⟨116, by decide⟩ : Fin 148)
        ((colE1 ⟨58, by decide⟩ 12 (transLenTr ⟨58, by decide⟩ 12 hp) : ↥(reps ⟨58, by decide⟩)) : Coordinate 1)
        T116_58 = colFn colCertDiv_116_58_12.D1 (m := 5) from colCertDiv_116_58_12.bind1,
    show colData2 (⟨116, by decide⟩ : Fin 148)
        ((colE2 ⟨58, by decide⟩ 12 hp : ↥(Q2.reps ⟨58, by decide⟩)) : Coordinate 2)
        Q2.T116_58_2 = colFn colCertDiv_116_58_12.D2 (m := 5) from colCertDiv_116_58_12.bind2]
  rw [alnId_116 j hj]
  exact fastcode_of_div ⟨116, by decide⟩ _ _ _
    ((alnId_116 j hj) ▸ Q2.listedAt (⟨116, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨116, by decide⟩ : Fin 148) hj hq).1) colCertDiv_116_58_12_match


theorem leaf_116_58_13 (hp : 13 < (Q2.transData.getD 58 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨58, by decide⟩ : Fin 148)) (colE2 ⟨58, by decide⟩ 13 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨58, by decide⟩ : Fin 148))
        (colE1 ⟨58, by decide⟩ 13 (transLenTr ⟨58, by decide⟩ 13 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨116, by decide⟩ : Fin 148) ⟨58, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨58, by decide⟩ 13 (transLenTr ⟨58, by decide⟩ 13 hp)) T116_58
      hfix116_58 hinj116_58 hcardT116_58
      (fun i => conj_mem_of_fixedPoints _ _ (T116_58 i) (hfix116_58 i) _)
      ⟨116, by decide⟩ ⟨58, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨58, by decide⟩ 13 hp) Q2.T116_58_2 Q2.hfix116_58_2 Q2.hinj116_58_2
      Q2.hcardT116_58_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_58_2 i) (Q2.hfix116_58_2 i) _)
      ?_).symm
  rw [show colData1 (⟨116, by decide⟩ : Fin 148)
        ((colE1 ⟨58, by decide⟩ 13 (transLenTr ⟨58, by decide⟩ 13 hp) : ↥(reps ⟨58, by decide⟩)) : Coordinate 1)
        T116_58 = colFn colCertDiv_116_58_13.D1 (m := 5) from colCertDiv_116_58_13.bind1,
    show colData2 (⟨116, by decide⟩ : Fin 148)
        ((colE2 ⟨58, by decide⟩ 13 hp : ↥(Q2.reps ⟨58, by decide⟩)) : Coordinate 2)
        Q2.T116_58_2 = colFn colCertDiv_116_58_13.D2 (m := 5) from colCertDiv_116_58_13.bind2]
  rw [alnId_116 j hj]
  exact fastcode_of_div ⟨116, by decide⟩ _ _ _
    ((alnId_116 j hj) ▸ Q2.listedAt (⟨116, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨116, by decide⟩ : Fin 148) hj hq).1) colCertDiv_116_58_13_match


theorem leaf_116_58_14 (hp : 14 < (Q2.transData.getD 58 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨58, by decide⟩ : Fin 148)) (colE2 ⟨58, by decide⟩ 14 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨58, by decide⟩ : Fin 148))
        (colE1 ⟨58, by decide⟩ 14 (transLenTr ⟨58, by decide⟩ 14 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨116, by decide⟩ : Fin 148) ⟨58, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨58, by decide⟩ 14 (transLenTr ⟨58, by decide⟩ 14 hp)) T116_58
      hfix116_58 hinj116_58 hcardT116_58
      (fun i => conj_mem_of_fixedPoints _ _ (T116_58 i) (hfix116_58 i) _)
      ⟨116, by decide⟩ ⟨58, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨58, by decide⟩ 14 hp) Q2.T116_58_2 Q2.hfix116_58_2 Q2.hinj116_58_2
      Q2.hcardT116_58_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_58_2 i) (Q2.hfix116_58_2 i) _)
      ?_).symm
  rw [show colData1 (⟨116, by decide⟩ : Fin 148)
        ((colE1 ⟨58, by decide⟩ 14 (transLenTr ⟨58, by decide⟩ 14 hp) : ↥(reps ⟨58, by decide⟩)) : Coordinate 1)
        T116_58 = colFn colCertDiv_116_58_14.D1 (m := 5) from colCertDiv_116_58_14.bind1,
    show colData2 (⟨116, by decide⟩ : Fin 148)
        ((colE2 ⟨58, by decide⟩ 14 hp : ↥(Q2.reps ⟨58, by decide⟩)) : Coordinate 2)
        Q2.T116_58_2 = colFn colCertDiv_116_58_14.D2 (m := 5) from colCertDiv_116_58_14.bind2]
  rw [alnId_116 j hj]
  exact fastcode_of_div ⟨116, by decide⟩ _ _ _
    ((alnId_116 j hj) ▸ Q2.listedAt (⟨116, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨116, by decide⟩ : Fin 148) hj hq).1) colCertDiv_116_58_14_match


theorem leaf_116_58_15 (hp : 15 < (Q2.transData.getD 58 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨58, by decide⟩ : Fin 148)) (colE2 ⟨58, by decide⟩ 15 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨58, by decide⟩ : Fin 148))
        (colE1 ⟨58, by decide⟩ 15 (transLenTr ⟨58, by decide⟩ 15 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨116, by decide⟩ : Fin 148) ⟨58, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨58, by decide⟩ 15 (transLenTr ⟨58, by decide⟩ 15 hp)) T116_58
      hfix116_58 hinj116_58 hcardT116_58
      (fun i => conj_mem_of_fixedPoints _ _ (T116_58 i) (hfix116_58 i) _)
      ⟨116, by decide⟩ ⟨58, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨58, by decide⟩ 15 hp) Q2.T116_58_2 Q2.hfix116_58_2 Q2.hinj116_58_2
      Q2.hcardT116_58_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_58_2 i) (Q2.hfix116_58_2 i) _)
      ?_).symm
  rw [show colData1 (⟨116, by decide⟩ : Fin 148)
        ((colE1 ⟨58, by decide⟩ 15 (transLenTr ⟨58, by decide⟩ 15 hp) : ↥(reps ⟨58, by decide⟩)) : Coordinate 1)
        T116_58 = colFn colCertDiv_116_58_15.D1 (m := 5) from colCertDiv_116_58_15.bind1,
    show colData2 (⟨116, by decide⟩ : Fin 148)
        ((colE2 ⟨58, by decide⟩ 15 hp : ↥(Q2.reps ⟨58, by decide⟩)) : Coordinate 2)
        Q2.T116_58_2 = colFn colCertDiv_116_58_15.D2 (m := 5) from colCertDiv_116_58_15.bind2]
  rw [alnId_116 j hj]
  exact fastcode_of_div ⟨116, by decide⟩ _ _ _
    ((alnId_116 j hj) ▸ Q2.listedAt (⟨116, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨116, by decide⟩ : Fin 148) hj hq).1) colCertDiv_116_58_15_match


theorem leaf_116_58_16 (hp : 16 < (Q2.transData.getD 58 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨58, by decide⟩ : Fin 148)) (colE2 ⟨58, by decide⟩ 16 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨58, by decide⟩ : Fin 148))
        (colE1 ⟨58, by decide⟩ 16 (transLenTr ⟨58, by decide⟩ 16 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨116, by decide⟩ : Fin 148) ⟨58, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨58, by decide⟩ 16 (transLenTr ⟨58, by decide⟩ 16 hp)) T116_58
      hfix116_58 hinj116_58 hcardT116_58
      (fun i => conj_mem_of_fixedPoints _ _ (T116_58 i) (hfix116_58 i) _)
      ⟨116, by decide⟩ ⟨58, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨58, by decide⟩ 16 hp) Q2.T116_58_2 Q2.hfix116_58_2 Q2.hinj116_58_2
      Q2.hcardT116_58_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_58_2 i) (Q2.hfix116_58_2 i) _)
      ?_).symm
  rw [show colData1 (⟨116, by decide⟩ : Fin 148)
        ((colE1 ⟨58, by decide⟩ 16 (transLenTr ⟨58, by decide⟩ 16 hp) : ↥(reps ⟨58, by decide⟩)) : Coordinate 1)
        T116_58 = colFn colCertDiv_116_58_16.D1 (m := 5) from colCertDiv_116_58_16.bind1,
    show colData2 (⟨116, by decide⟩ : Fin 148)
        ((colE2 ⟨58, by decide⟩ 16 hp : ↥(Q2.reps ⟨58, by decide⟩)) : Coordinate 2)
        Q2.T116_58_2 = colFn colCertDiv_116_58_16.D2 (m := 5) from colCertDiv_116_58_16.bind2]
  rw [alnId_116 j hj]
  exact fastcode_of_div ⟨116, by decide⟩ _ _ _
    ((alnId_116 j hj) ▸ Q2.listedAt (⟨116, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨116, by decide⟩ : Fin 148) hj hq).1) colCertDiv_116_58_16_match


theorem leaf_116_58_17 (hp : 17 < (Q2.transData.getD 58 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨58, by decide⟩ : Fin 148)) (colE2 ⟨58, by decide⟩ 17 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨58, by decide⟩ : Fin 148))
        (colE1 ⟨58, by decide⟩ 17 (transLenTr ⟨58, by decide⟩ 17 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨116, by decide⟩ : Fin 148) ⟨58, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨58, by decide⟩ 17 (transLenTr ⟨58, by decide⟩ 17 hp)) T116_58
      hfix116_58 hinj116_58 hcardT116_58
      (fun i => conj_mem_of_fixedPoints _ _ (T116_58 i) (hfix116_58 i) _)
      ⟨116, by decide⟩ ⟨58, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨58, by decide⟩ 17 hp) Q2.T116_58_2 Q2.hfix116_58_2 Q2.hinj116_58_2
      Q2.hcardT116_58_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_58_2 i) (Q2.hfix116_58_2 i) _)
      ?_).symm
  rw [show colData1 (⟨116, by decide⟩ : Fin 148)
        ((colE1 ⟨58, by decide⟩ 17 (transLenTr ⟨58, by decide⟩ 17 hp) : ↥(reps ⟨58, by decide⟩)) : Coordinate 1)
        T116_58 = colFn colCertDiv_116_58_17.D1 (m := 5) from colCertDiv_116_58_17.bind1,
    show colData2 (⟨116, by decide⟩ : Fin 148)
        ((colE2 ⟨58, by decide⟩ 17 hp : ↥(Q2.reps ⟨58, by decide⟩)) : Coordinate 2)
        Q2.T116_58_2 = colFn colCertDiv_116_58_17.D2 (m := 5) from colCertDiv_116_58_17.bind2]
  rw [alnId_116 j hj]
  exact fastcode_of_div ⟨116, by decide⟩ _ _ _
    ((alnId_116 j hj) ▸ Q2.listedAt (⟨116, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨116, by decide⟩ : Fin 148) hj hq).1) colCertDiv_116_58_17_match


theorem leaf_116_58_18 (hp : 18 < (Q2.transData.getD 58 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨58, by decide⟩ : Fin 148)) (colE2 ⟨58, by decide⟩ 18 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨58, by decide⟩ : Fin 148))
        (colE1 ⟨58, by decide⟩ 18 (transLenTr ⟨58, by decide⟩ 18 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨116, by decide⟩ : Fin 148) ⟨58, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨58, by decide⟩ 18 (transLenTr ⟨58, by decide⟩ 18 hp)) T116_58
      hfix116_58 hinj116_58 hcardT116_58
      (fun i => conj_mem_of_fixedPoints _ _ (T116_58 i) (hfix116_58 i) _)
      ⟨116, by decide⟩ ⟨58, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨58, by decide⟩ 18 hp) Q2.T116_58_2 Q2.hfix116_58_2 Q2.hinj116_58_2
      Q2.hcardT116_58_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_58_2 i) (Q2.hfix116_58_2 i) _)
      ?_).symm
  rw [show colData1 (⟨116, by decide⟩ : Fin 148)
        ((colE1 ⟨58, by decide⟩ 18 (transLenTr ⟨58, by decide⟩ 18 hp) : ↥(reps ⟨58, by decide⟩)) : Coordinate 1)
        T116_58 = colFn colCertDiv_116_58_18.D1 (m := 5) from colCertDiv_116_58_18.bind1,
    show colData2 (⟨116, by decide⟩ : Fin 148)
        ((colE2 ⟨58, by decide⟩ 18 hp : ↥(Q2.reps ⟨58, by decide⟩)) : Coordinate 2)
        Q2.T116_58_2 = colFn colCertDiv_116_58_18.D2 (m := 5) from colCertDiv_116_58_18.bind2]
  rw [alnId_116 j hj]
  exact fastcode_of_div ⟨116, by decide⟩ _ _ _
    ((alnId_116 j hj) ▸ Q2.listedAt (⟨116, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨116, by decide⟩ : Fin 148) hj hq).1) colCertDiv_116_58_18_match


theorem leaf_116_58_19 (hp : 19 < (Q2.transData.getD 58 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨58, by decide⟩ : Fin 148)) (colE2 ⟨58, by decide⟩ 19 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨58, by decide⟩ : Fin 148))
        (colE1 ⟨58, by decide⟩ 19 (transLenTr ⟨58, by decide⟩ 19 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨116, by decide⟩ : Fin 148) ⟨58, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨58, by decide⟩ 19 (transLenTr ⟨58, by decide⟩ 19 hp)) T116_58
      hfix116_58 hinj116_58 hcardT116_58
      (fun i => conj_mem_of_fixedPoints _ _ (T116_58 i) (hfix116_58 i) _)
      ⟨116, by decide⟩ ⟨58, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨58, by decide⟩ 19 hp) Q2.T116_58_2 Q2.hfix116_58_2 Q2.hinj116_58_2
      Q2.hcardT116_58_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_58_2 i) (Q2.hfix116_58_2 i) _)
      ?_).symm
  rw [show colData1 (⟨116, by decide⟩ : Fin 148)
        ((colE1 ⟨58, by decide⟩ 19 (transLenTr ⟨58, by decide⟩ 19 hp) : ↥(reps ⟨58, by decide⟩)) : Coordinate 1)
        T116_58 = colFn colCertDiv_116_58_19.D1 (m := 5) from colCertDiv_116_58_19.bind1,
    show colData2 (⟨116, by decide⟩ : Fin 148)
        ((colE2 ⟨58, by decide⟩ 19 hp : ↥(Q2.reps ⟨58, by decide⟩)) : Coordinate 2)
        Q2.T116_58_2 = colFn colCertDiv_116_58_19.D2 (m := 5) from colCertDiv_116_58_19.bind2]
  rw [alnId_116 j hj]
  exact fastcode_of_div ⟨116, by decide⟩ _ _ _
    ((alnId_116 j hj) ▸ Q2.listedAt (⟨116, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨116, by decide⟩ : Fin 148) hj hq).1) colCertDiv_116_58_19_match


theorem leaf_116_58_20 (hp : 20 < (Q2.transData.getD 58 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨58, by decide⟩ : Fin 148)) (colE2 ⟨58, by decide⟩ 20 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨58, by decide⟩ : Fin 148))
        (colE1 ⟨58, by decide⟩ 20 (transLenTr ⟨58, by decide⟩ 20 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨116, by decide⟩ : Fin 148) ⟨58, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨58, by decide⟩ 20 (transLenTr ⟨58, by decide⟩ 20 hp)) T116_58
      hfix116_58 hinj116_58 hcardT116_58
      (fun i => conj_mem_of_fixedPoints _ _ (T116_58 i) (hfix116_58 i) _)
      ⟨116, by decide⟩ ⟨58, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨58, by decide⟩ 20 hp) Q2.T116_58_2 Q2.hfix116_58_2 Q2.hinj116_58_2
      Q2.hcardT116_58_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_58_2 i) (Q2.hfix116_58_2 i) _)
      ?_).symm
  rw [show colData1 (⟨116, by decide⟩ : Fin 148)
        ((colE1 ⟨58, by decide⟩ 20 (transLenTr ⟨58, by decide⟩ 20 hp) : ↥(reps ⟨58, by decide⟩)) : Coordinate 1)
        T116_58 = colFn colCertDiv_116_58_20.D1 (m := 5) from colCertDiv_116_58_20.bind1,
    show colData2 (⟨116, by decide⟩ : Fin 148)
        ((colE2 ⟨58, by decide⟩ 20 hp : ↥(Q2.reps ⟨58, by decide⟩)) : Coordinate 2)
        Q2.T116_58_2 = colFn colCertDiv_116_58_20.D2 (m := 5) from colCertDiv_116_58_20.bind2]
  rw [alnId_116 j hj]
  exact fastcode_of_div ⟨116, by decide⟩ _ _ _
    ((alnId_116 j hj) ▸ Q2.listedAt (⟨116, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨116, by decide⟩ : Fin 148) hj hq).1) colCertDiv_116_58_20_match


theorem leaf_116_58_21 (hp : 21 < (Q2.transData.getD 58 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨58, by decide⟩ : Fin 148)) (colE2 ⟨58, by decide⟩ 21 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨58, by decide⟩ : Fin 148))
        (colE1 ⟨58, by decide⟩ 21 (transLenTr ⟨58, by decide⟩ 21 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨116, by decide⟩ : Fin 148) ⟨58, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨58, by decide⟩ 21 (transLenTr ⟨58, by decide⟩ 21 hp)) T116_58
      hfix116_58 hinj116_58 hcardT116_58
      (fun i => conj_mem_of_fixedPoints _ _ (T116_58 i) (hfix116_58 i) _)
      ⟨116, by decide⟩ ⟨58, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨58, by decide⟩ 21 hp) Q2.T116_58_2 Q2.hfix116_58_2 Q2.hinj116_58_2
      Q2.hcardT116_58_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_58_2 i) (Q2.hfix116_58_2 i) _)
      ?_).symm
  rw [show colData1 (⟨116, by decide⟩ : Fin 148)
        ((colE1 ⟨58, by decide⟩ 21 (transLenTr ⟨58, by decide⟩ 21 hp) : ↥(reps ⟨58, by decide⟩)) : Coordinate 1)
        T116_58 = colFn colCertDiv_116_58_21.D1 (m := 5) from colCertDiv_116_58_21.bind1,
    show colData2 (⟨116, by decide⟩ : Fin 148)
        ((colE2 ⟨58, by decide⟩ 21 hp : ↥(Q2.reps ⟨58, by decide⟩)) : Coordinate 2)
        Q2.T116_58_2 = colFn colCertDiv_116_58_21.D2 (m := 5) from colCertDiv_116_58_21.bind2]
  rw [alnId_116 j hj]
  exact fastcode_of_div ⟨116, by decide⟩ _ _ _
    ((alnId_116 j hj) ▸ Q2.listedAt (⟨116, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨116, by decide⟩ : Fin 148) hj hq).1) colCertDiv_116_58_21_match


theorem leaf_116_58_22 (hp : 22 < (Q2.transData.getD 58 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨58, by decide⟩ : Fin 148)) (colE2 ⟨58, by decide⟩ 22 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨58, by decide⟩ : Fin 148))
        (colE1 ⟨58, by decide⟩ 22 (transLenTr ⟨58, by decide⟩ 22 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨116, by decide⟩ : Fin 148) ⟨58, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨58, by decide⟩ 22 (transLenTr ⟨58, by decide⟩ 22 hp)) T116_58
      hfix116_58 hinj116_58 hcardT116_58
      (fun i => conj_mem_of_fixedPoints _ _ (T116_58 i) (hfix116_58 i) _)
      ⟨116, by decide⟩ ⟨58, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨58, by decide⟩ 22 hp) Q2.T116_58_2 Q2.hfix116_58_2 Q2.hinj116_58_2
      Q2.hcardT116_58_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_58_2 i) (Q2.hfix116_58_2 i) _)
      ?_).symm
  rw [show colData1 (⟨116, by decide⟩ : Fin 148)
        ((colE1 ⟨58, by decide⟩ 22 (transLenTr ⟨58, by decide⟩ 22 hp) : ↥(reps ⟨58, by decide⟩)) : Coordinate 1)
        T116_58 = colFn colCertDiv_116_58_22.D1 (m := 5) from colCertDiv_116_58_22.bind1,
    show colData2 (⟨116, by decide⟩ : Fin 148)
        ((colE2 ⟨58, by decide⟩ 22 hp : ↥(Q2.reps ⟨58, by decide⟩)) : Coordinate 2)
        Q2.T116_58_2 = colFn colCertDiv_116_58_22.D2 (m := 5) from colCertDiv_116_58_22.bind2]
  rw [alnId_116 j hj]
  exact fastcode_of_div ⟨116, by decide⟩ _ _ _
    ((alnId_116 j hj) ▸ Q2.listedAt (⟨116, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨116, by decide⟩ : Fin 148) hj hq).1) colCertDiv_116_58_22_match


theorem leaf_116_58_23 (hp : 23 < (Q2.transData.getD 58 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨58, by decide⟩ : Fin 148)) (colE2 ⟨58, by decide⟩ 23 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨58, by decide⟩ : Fin 148))
        (colE1 ⟨58, by decide⟩ 23 (transLenTr ⟨58, by decide⟩ 23 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨116, by decide⟩ : Fin 148) ⟨58, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨58, by decide⟩ 23 (transLenTr ⟨58, by decide⟩ 23 hp)) T116_58
      hfix116_58 hinj116_58 hcardT116_58
      (fun i => conj_mem_of_fixedPoints _ _ (T116_58 i) (hfix116_58 i) _)
      ⟨116, by decide⟩ ⟨58, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨58, by decide⟩ 23 hp) Q2.T116_58_2 Q2.hfix116_58_2 Q2.hinj116_58_2
      Q2.hcardT116_58_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_58_2 i) (Q2.hfix116_58_2 i) _)
      ?_).symm
  rw [show colData1 (⟨116, by decide⟩ : Fin 148)
        ((colE1 ⟨58, by decide⟩ 23 (transLenTr ⟨58, by decide⟩ 23 hp) : ↥(reps ⟨58, by decide⟩)) : Coordinate 1)
        T116_58 = colFn colCertDiv_116_58_23.D1 (m := 5) from colCertDiv_116_58_23.bind1,
    show colData2 (⟨116, by decide⟩ : Fin 148)
        ((colE2 ⟨58, by decide⟩ 23 hp : ↥(Q2.reps ⟨58, by decide⟩)) : Coordinate 2)
        Q2.T116_58_2 = colFn colCertDiv_116_58_23.D2 (m := 5) from colCertDiv_116_58_23.bind2]
  rw [alnId_116 j hj]
  exact fastcode_of_div ⟨116, by decide⟩ _ _ _
    ((alnId_116 j hj) ▸ Q2.listedAt (⟨116, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨116, by decide⟩ : Fin 148) hj hq).1) colCertDiv_116_58_23_match


theorem leaf_116_58_24 (hp : 24 < (Q2.transData.getD 58 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨58, by decide⟩ : Fin 148)) (colE2 ⟨58, by decide⟩ 24 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨58, by decide⟩ : Fin 148))
        (colE1 ⟨58, by decide⟩ 24 (transLenTr ⟨58, by decide⟩ 24 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨116, by decide⟩ : Fin 148) ⟨58, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨58, by decide⟩ 24 (transLenTr ⟨58, by decide⟩ 24 hp)) T116_58
      hfix116_58 hinj116_58 hcardT116_58
      (fun i => conj_mem_of_fixedPoints _ _ (T116_58 i) (hfix116_58 i) _)
      ⟨116, by decide⟩ ⟨58, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨58, by decide⟩ 24 hp) Q2.T116_58_2 Q2.hfix116_58_2 Q2.hinj116_58_2
      Q2.hcardT116_58_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_58_2 i) (Q2.hfix116_58_2 i) _)
      ?_).symm
  rw [show colData1 (⟨116, by decide⟩ : Fin 148)
        ((colE1 ⟨58, by decide⟩ 24 (transLenTr ⟨58, by decide⟩ 24 hp) : ↥(reps ⟨58, by decide⟩)) : Coordinate 1)
        T116_58 = colFn colCertDiv_116_58_24.D1 (m := 5) from colCertDiv_116_58_24.bind1,
    show colData2 (⟨116, by decide⟩ : Fin 148)
        ((colE2 ⟨58, by decide⟩ 24 hp : ↥(Q2.reps ⟨58, by decide⟩)) : Coordinate 2)
        Q2.T116_58_2 = colFn colCertDiv_116_58_24.D2 (m := 5) from colCertDiv_116_58_24.bind2]
  rw [alnId_116 j hj]
  exact fastcode_of_div ⟨116, by decide⟩ _ _ _
    ((alnId_116 j hj) ▸ Q2.listedAt (⟨116, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨116, by decide⟩ : Fin 148) hj hq).1) colCertDiv_116_58_24_match


theorem leaf_116_59_0 (hp : 0 < (Q2.transData.getD 59 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨59, by decide⟩ : Fin 148)) (colE2 ⟨59, by decide⟩ 0 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨59, by decide⟩ : Fin 148))
        (colE1 ⟨59, by decide⟩ 0 (transLenTr ⟨59, by decide⟩ 0 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨59, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨59, by decide⟩ 0 (transLenTr ⟨59, by decide⟩ 0 hp)) T116_59
      hfix116_59 hinj116_59 hcardT116_59
      (fun i => conj_mem_of_fixedPoints _ _ (T116_59 i) (hfix116_59 i) _)
      ⟨116, by decide⟩ ⟨59, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨59, by decide⟩ 0 hp) Q2.T116_59_2 Q2.hfix116_59_2 Q2.hinj116_59_2
      Q2.hcardT116_59_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_59_2 i) (Q2.hfix116_59_2 i) _)
      colCert_116_59_0.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_59_1 (hp : 1 < (Q2.transData.getD 59 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨59, by decide⟩ : Fin 148)) (colE2 ⟨59, by decide⟩ 1 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨59, by decide⟩ : Fin 148))
        (colE1 ⟨59, by decide⟩ 1 (transLenTr ⟨59, by decide⟩ 1 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨59, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨59, by decide⟩ 1 (transLenTr ⟨59, by decide⟩ 1 hp)) T116_59
      hfix116_59 hinj116_59 hcardT116_59
      (fun i => conj_mem_of_fixedPoints _ _ (T116_59 i) (hfix116_59 i) _)
      ⟨116, by decide⟩ ⟨59, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨59, by decide⟩ 1 hp) Q2.T116_59_2 Q2.hfix116_59_2 Q2.hinj116_59_2
      Q2.hcardT116_59_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_59_2 i) (Q2.hfix116_59_2 i) _)
      colCert_116_59_1.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_59_2 (hp : 2 < (Q2.transData.getD 59 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨59, by decide⟩ : Fin 148)) (colE2 ⟨59, by decide⟩ 2 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨59, by decide⟩ : Fin 148))
        (colE1 ⟨59, by decide⟩ 2 (transLenTr ⟨59, by decide⟩ 2 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨59, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨59, by decide⟩ 2 (transLenTr ⟨59, by decide⟩ 2 hp)) T116_59
      hfix116_59 hinj116_59 hcardT116_59
      (fun i => conj_mem_of_fixedPoints _ _ (T116_59 i) (hfix116_59 i) _)
      ⟨116, by decide⟩ ⟨59, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨59, by decide⟩ 2 hp) Q2.T116_59_2 Q2.hfix116_59_2 Q2.hinj116_59_2
      Q2.hcardT116_59_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_59_2 i) (Q2.hfix116_59_2 i) _)
      colCert_116_59_2.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_59_3 (hp : 3 < (Q2.transData.getD 59 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨59, by decide⟩ : Fin 148)) (colE2 ⟨59, by decide⟩ 3 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨59, by decide⟩ : Fin 148))
        (colE1 ⟨59, by decide⟩ 3 (transLenTr ⟨59, by decide⟩ 3 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨59, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨59, by decide⟩ 3 (transLenTr ⟨59, by decide⟩ 3 hp)) T116_59
      hfix116_59 hinj116_59 hcardT116_59
      (fun i => conj_mem_of_fixedPoints _ _ (T116_59 i) (hfix116_59 i) _)
      ⟨116, by decide⟩ ⟨59, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨59, by decide⟩ 3 hp) Q2.T116_59_2 Q2.hfix116_59_2 Q2.hinj116_59_2
      Q2.hcardT116_59_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_59_2 i) (Q2.hfix116_59_2 i) _)
      colCert_116_59_3.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_59_4 (hp : 4 < (Q2.transData.getD 59 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨59, by decide⟩ : Fin 148)) (colE2 ⟨59, by decide⟩ 4 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨59, by decide⟩ : Fin 148))
        (colE1 ⟨59, by decide⟩ 4 (transLenTr ⟨59, by decide⟩ 4 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨59, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨59, by decide⟩ 4 (transLenTr ⟨59, by decide⟩ 4 hp)) T116_59
      hfix116_59 hinj116_59 hcardT116_59
      (fun i => conj_mem_of_fixedPoints _ _ (T116_59 i) (hfix116_59 i) _)
      ⟨116, by decide⟩ ⟨59, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨59, by decide⟩ 4 hp) Q2.T116_59_2 Q2.hfix116_59_2 Q2.hinj116_59_2
      Q2.hcardT116_59_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_59_2 i) (Q2.hfix116_59_2 i) _)
      colCert_116_59_4.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_59_5 (hp : 5 < (Q2.transData.getD 59 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨59, by decide⟩ : Fin 148)) (colE2 ⟨59, by decide⟩ 5 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨59, by decide⟩ : Fin 148))
        (colE1 ⟨59, by decide⟩ 5 (transLenTr ⟨59, by decide⟩ 5 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨59, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨59, by decide⟩ 5 (transLenTr ⟨59, by decide⟩ 5 hp)) T116_59
      hfix116_59 hinj116_59 hcardT116_59
      (fun i => conj_mem_of_fixedPoints _ _ (T116_59 i) (hfix116_59 i) _)
      ⟨116, by decide⟩ ⟨59, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨59, by decide⟩ 5 hp) Q2.T116_59_2 Q2.hfix116_59_2 Q2.hinj116_59_2
      Q2.hcardT116_59_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_59_2 i) (Q2.hfix116_59_2 i) _)
      colCert_116_59_5.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_59_6 (hp : 6 < (Q2.transData.getD 59 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨59, by decide⟩ : Fin 148)) (colE2 ⟨59, by decide⟩ 6 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨59, by decide⟩ : Fin 148))
        (colE1 ⟨59, by decide⟩ 6 (transLenTr ⟨59, by decide⟩ 6 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨59, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨59, by decide⟩ 6 (transLenTr ⟨59, by decide⟩ 6 hp)) T116_59
      hfix116_59 hinj116_59 hcardT116_59
      (fun i => conj_mem_of_fixedPoints _ _ (T116_59 i) (hfix116_59 i) _)
      ⟨116, by decide⟩ ⟨59, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨59, by decide⟩ 6 hp) Q2.T116_59_2 Q2.hfix116_59_2 Q2.hinj116_59_2
      Q2.hcardT116_59_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_59_2 i) (Q2.hfix116_59_2 i) _)
      colCert_116_59_6.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_59_7 (hp : 7 < (Q2.transData.getD 59 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨59, by decide⟩ : Fin 148)) (colE2 ⟨59, by decide⟩ 7 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨59, by decide⟩ : Fin 148))
        (colE1 ⟨59, by decide⟩ 7 (transLenTr ⟨59, by decide⟩ 7 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨59, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨59, by decide⟩ 7 (transLenTr ⟨59, by decide⟩ 7 hp)) T116_59
      hfix116_59 hinj116_59 hcardT116_59
      (fun i => conj_mem_of_fixedPoints _ _ (T116_59 i) (hfix116_59 i) _)
      ⟨116, by decide⟩ ⟨59, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨59, by decide⟩ 7 hp) Q2.T116_59_2 Q2.hfix116_59_2 Q2.hinj116_59_2
      Q2.hcardT116_59_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_59_2 i) (Q2.hfix116_59_2 i) _)
      colCert_116_59_7.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_59_8 (hp : 8 < (Q2.transData.getD 59 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨59, by decide⟩ : Fin 148)) (colE2 ⟨59, by decide⟩ 8 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨59, by decide⟩ : Fin 148))
        (colE1 ⟨59, by decide⟩ 8 (transLenTr ⟨59, by decide⟩ 8 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨59, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨59, by decide⟩ 8 (transLenTr ⟨59, by decide⟩ 8 hp)) T116_59
      hfix116_59 hinj116_59 hcardT116_59
      (fun i => conj_mem_of_fixedPoints _ _ (T116_59 i) (hfix116_59 i) _)
      ⟨116, by decide⟩ ⟨59, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨59, by decide⟩ 8 hp) Q2.T116_59_2 Q2.hfix116_59_2 Q2.hinj116_59_2
      Q2.hcardT116_59_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_59_2 i) (Q2.hfix116_59_2 i) _)
      colCert_116_59_8.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_59_9 (hp : 9 < (Q2.transData.getD 59 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨59, by decide⟩ : Fin 148)) (colE2 ⟨59, by decide⟩ 9 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨59, by decide⟩ : Fin 148))
        (colE1 ⟨59, by decide⟩ 9 (transLenTr ⟨59, by decide⟩ 9 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨59, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨59, by decide⟩ 9 (transLenTr ⟨59, by decide⟩ 9 hp)) T116_59
      hfix116_59 hinj116_59 hcardT116_59
      (fun i => conj_mem_of_fixedPoints _ _ (T116_59 i) (hfix116_59 i) _)
      ⟨116, by decide⟩ ⟨59, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨59, by decide⟩ 9 hp) Q2.T116_59_2 Q2.hfix116_59_2 Q2.hinj116_59_2
      Q2.hcardT116_59_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_59_2 i) (Q2.hfix116_59_2 i) _)
      colCert_116_59_9.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_59_10 (hp : 10 < (Q2.transData.getD 59 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨59, by decide⟩ : Fin 148)) (colE2 ⟨59, by decide⟩ 10 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨59, by decide⟩ : Fin 148))
        (colE1 ⟨59, by decide⟩ 10 (transLenTr ⟨59, by decide⟩ 10 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨59, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨59, by decide⟩ 10 (transLenTr ⟨59, by decide⟩ 10 hp)) T116_59
      hfix116_59 hinj116_59 hcardT116_59
      (fun i => conj_mem_of_fixedPoints _ _ (T116_59 i) (hfix116_59 i) _)
      ⟨116, by decide⟩ ⟨59, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨59, by decide⟩ 10 hp) Q2.T116_59_2 Q2.hfix116_59_2 Q2.hinj116_59_2
      Q2.hcardT116_59_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_59_2 i) (Q2.hfix116_59_2 i) _)
      colCert_116_59_10.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_59_11 (hp : 11 < (Q2.transData.getD 59 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨59, by decide⟩ : Fin 148)) (colE2 ⟨59, by decide⟩ 11 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨59, by decide⟩ : Fin 148))
        (colE1 ⟨59, by decide⟩ 11 (transLenTr ⟨59, by decide⟩ 11 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨59, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨59, by decide⟩ 11 (transLenTr ⟨59, by decide⟩ 11 hp)) T116_59
      hfix116_59 hinj116_59 hcardT116_59
      (fun i => conj_mem_of_fixedPoints _ _ (T116_59 i) (hfix116_59 i) _)
      ⟨116, by decide⟩ ⟨59, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨59, by decide⟩ 11 hp) Q2.T116_59_2 Q2.hfix116_59_2 Q2.hinj116_59_2
      Q2.hcardT116_59_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_59_2 i) (Q2.hfix116_59_2 i) _)
      colCert_116_59_11.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_59_12 (hp : 12 < (Q2.transData.getD 59 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨59, by decide⟩ : Fin 148)) (colE2 ⟨59, by decide⟩ 12 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨59, by decide⟩ : Fin 148))
        (colE1 ⟨59, by decide⟩ 12 (transLenTr ⟨59, by decide⟩ 12 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨59, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨59, by decide⟩ 12 (transLenTr ⟨59, by decide⟩ 12 hp)) T116_59
      hfix116_59 hinj116_59 hcardT116_59
      (fun i => conj_mem_of_fixedPoints _ _ (T116_59 i) (hfix116_59 i) _)
      ⟨116, by decide⟩ ⟨59, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨59, by decide⟩ 12 hp) Q2.T116_59_2 Q2.hfix116_59_2 Q2.hinj116_59_2
      Q2.hcardT116_59_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_59_2 i) (Q2.hfix116_59_2 i) _)
      colCert_116_59_12.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_59_13 (hp : 13 < (Q2.transData.getD 59 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨59, by decide⟩ : Fin 148)) (colE2 ⟨59, by decide⟩ 13 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨59, by decide⟩ : Fin 148))
        (colE1 ⟨59, by decide⟩ 13 (transLenTr ⟨59, by decide⟩ 13 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨59, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨59, by decide⟩ 13 (transLenTr ⟨59, by decide⟩ 13 hp)) T116_59
      hfix116_59 hinj116_59 hcardT116_59
      (fun i => conj_mem_of_fixedPoints _ _ (T116_59 i) (hfix116_59 i) _)
      ⟨116, by decide⟩ ⟨59, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨59, by decide⟩ 13 hp) Q2.T116_59_2 Q2.hfix116_59_2 Q2.hinj116_59_2
      Q2.hcardT116_59_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_59_2 i) (Q2.hfix116_59_2 i) _)
      colCert_116_59_13.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_59_14 (hp : 14 < (Q2.transData.getD 59 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨59, by decide⟩ : Fin 148)) (colE2 ⟨59, by decide⟩ 14 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨59, by decide⟩ : Fin 148))
        (colE1 ⟨59, by decide⟩ 14 (transLenTr ⟨59, by decide⟩ 14 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨59, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨59, by decide⟩ 14 (transLenTr ⟨59, by decide⟩ 14 hp)) T116_59
      hfix116_59 hinj116_59 hcardT116_59
      (fun i => conj_mem_of_fixedPoints _ _ (T116_59 i) (hfix116_59 i) _)
      ⟨116, by decide⟩ ⟨59, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨59, by decide⟩ 14 hp) Q2.T116_59_2 Q2.hfix116_59_2 Q2.hinj116_59_2
      Q2.hcardT116_59_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_59_2 i) (Q2.hfix116_59_2 i) _)
      colCert_116_59_14.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_59_15 (hp : 15 < (Q2.transData.getD 59 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨59, by decide⟩ : Fin 148)) (colE2 ⟨59, by decide⟩ 15 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨59, by decide⟩ : Fin 148))
        (colE1 ⟨59, by decide⟩ 15 (transLenTr ⟨59, by decide⟩ 15 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨59, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨59, by decide⟩ 15 (transLenTr ⟨59, by decide⟩ 15 hp)) T116_59
      hfix116_59 hinj116_59 hcardT116_59
      (fun i => conj_mem_of_fixedPoints _ _ (T116_59 i) (hfix116_59 i) _)
      ⟨116, by decide⟩ ⟨59, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨59, by decide⟩ 15 hp) Q2.T116_59_2 Q2.hfix116_59_2 Q2.hinj116_59_2
      Q2.hcardT116_59_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_59_2 i) (Q2.hfix116_59_2 i) _)
      colCert_116_59_15.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_59_16 (hp : 16 < (Q2.transData.getD 59 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨59, by decide⟩ : Fin 148)) (colE2 ⟨59, by decide⟩ 16 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨59, by decide⟩ : Fin 148))
        (colE1 ⟨59, by decide⟩ 16 (transLenTr ⟨59, by decide⟩ 16 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨59, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨59, by decide⟩ 16 (transLenTr ⟨59, by decide⟩ 16 hp)) T116_59
      hfix116_59 hinj116_59 hcardT116_59
      (fun i => conj_mem_of_fixedPoints _ _ (T116_59 i) (hfix116_59 i) _)
      ⟨116, by decide⟩ ⟨59, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨59, by decide⟩ 16 hp) Q2.T116_59_2 Q2.hfix116_59_2 Q2.hinj116_59_2
      Q2.hcardT116_59_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_59_2 i) (Q2.hfix116_59_2 i) _)
      colCert_116_59_16.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_59_17 (hp : 17 < (Q2.transData.getD 59 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨59, by decide⟩ : Fin 148)) (colE2 ⟨59, by decide⟩ 17 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨59, by decide⟩ : Fin 148))
        (colE1 ⟨59, by decide⟩ 17 (transLenTr ⟨59, by decide⟩ 17 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨59, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨59, by decide⟩ 17 (transLenTr ⟨59, by decide⟩ 17 hp)) T116_59
      hfix116_59 hinj116_59 hcardT116_59
      (fun i => conj_mem_of_fixedPoints _ _ (T116_59 i) (hfix116_59 i) _)
      ⟨116, by decide⟩ ⟨59, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨59, by decide⟩ 17 hp) Q2.T116_59_2 Q2.hfix116_59_2 Q2.hinj116_59_2
      Q2.hcardT116_59_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_59_2 i) (Q2.hfix116_59_2 i) _)
      colCert_116_59_17.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_59_18 (hp : 18 < (Q2.transData.getD 59 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨59, by decide⟩ : Fin 148)) (colE2 ⟨59, by decide⟩ 18 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨59, by decide⟩ : Fin 148))
        (colE1 ⟨59, by decide⟩ 18 (transLenTr ⟨59, by decide⟩ 18 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨59, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨59, by decide⟩ 18 (transLenTr ⟨59, by decide⟩ 18 hp)) T116_59
      hfix116_59 hinj116_59 hcardT116_59
      (fun i => conj_mem_of_fixedPoints _ _ (T116_59 i) (hfix116_59 i) _)
      ⟨116, by decide⟩ ⟨59, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨59, by decide⟩ 18 hp) Q2.T116_59_2 Q2.hfix116_59_2 Q2.hinj116_59_2
      Q2.hcardT116_59_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_59_2 i) (Q2.hfix116_59_2 i) _)
      colCert_116_59_18.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_59_19 (hp : 19 < (Q2.transData.getD 59 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨59, by decide⟩ : Fin 148)) (colE2 ⟨59, by decide⟩ 19 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨59, by decide⟩ : Fin 148))
        (colE1 ⟨59, by decide⟩ 19 (transLenTr ⟨59, by decide⟩ 19 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨59, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨59, by decide⟩ 19 (transLenTr ⟨59, by decide⟩ 19 hp)) T116_59
      hfix116_59 hinj116_59 hcardT116_59
      (fun i => conj_mem_of_fixedPoints _ _ (T116_59 i) (hfix116_59 i) _)
      ⟨116, by decide⟩ ⟨59, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨59, by decide⟩ 19 hp) Q2.T116_59_2 Q2.hfix116_59_2 Q2.hinj116_59_2
      Q2.hcardT116_59_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_59_2 i) (Q2.hfix116_59_2 i) _)
      colCert_116_59_19.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_59_20 (hp : 20 < (Q2.transData.getD 59 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨59, by decide⟩ : Fin 148)) (colE2 ⟨59, by decide⟩ 20 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨59, by decide⟩ : Fin 148))
        (colE1 ⟨59, by decide⟩ 20 (transLenTr ⟨59, by decide⟩ 20 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨59, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨59, by decide⟩ 20 (transLenTr ⟨59, by decide⟩ 20 hp)) T116_59
      hfix116_59 hinj116_59 hcardT116_59
      (fun i => conj_mem_of_fixedPoints _ _ (T116_59 i) (hfix116_59 i) _)
      ⟨116, by decide⟩ ⟨59, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨59, by decide⟩ 20 hp) Q2.T116_59_2 Q2.hfix116_59_2 Q2.hinj116_59_2
      Q2.hcardT116_59_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_59_2 i) (Q2.hfix116_59_2 i) _)
      colCert_116_59_20.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_59_21 (hp : 21 < (Q2.transData.getD 59 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨59, by decide⟩ : Fin 148)) (colE2 ⟨59, by decide⟩ 21 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨59, by decide⟩ : Fin 148))
        (colE1 ⟨59, by decide⟩ 21 (transLenTr ⟨59, by decide⟩ 21 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨59, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨59, by decide⟩ 21 (transLenTr ⟨59, by decide⟩ 21 hp)) T116_59
      hfix116_59 hinj116_59 hcardT116_59
      (fun i => conj_mem_of_fixedPoints _ _ (T116_59 i) (hfix116_59 i) _)
      ⟨116, by decide⟩ ⟨59, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨59, by decide⟩ 21 hp) Q2.T116_59_2 Q2.hfix116_59_2 Q2.hinj116_59_2
      Q2.hcardT116_59_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_59_2 i) (Q2.hfix116_59_2 i) _)
      colCert_116_59_21.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_59_22 (hp : 22 < (Q2.transData.getD 59 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨59, by decide⟩ : Fin 148)) (colE2 ⟨59, by decide⟩ 22 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨59, by decide⟩ : Fin 148))
        (colE1 ⟨59, by decide⟩ 22 (transLenTr ⟨59, by decide⟩ 22 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨59, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨59, by decide⟩ 22 (transLenTr ⟨59, by decide⟩ 22 hp)) T116_59
      hfix116_59 hinj116_59 hcardT116_59
      (fun i => conj_mem_of_fixedPoints _ _ (T116_59 i) (hfix116_59 i) _)
      ⟨116, by decide⟩ ⟨59, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨59, by decide⟩ 22 hp) Q2.T116_59_2 Q2.hfix116_59_2 Q2.hinj116_59_2
      Q2.hcardT116_59_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_59_2 i) (Q2.hfix116_59_2 i) _)
      colCert_116_59_22.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_59_23 (hp : 23 < (Q2.transData.getD 59 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨59, by decide⟩ : Fin 148)) (colE2 ⟨59, by decide⟩ 23 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨59, by decide⟩ : Fin 148))
        (colE1 ⟨59, by decide⟩ 23 (transLenTr ⟨59, by decide⟩ 23 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨59, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨59, by decide⟩ 23 (transLenTr ⟨59, by decide⟩ 23 hp)) T116_59
      hfix116_59 hinj116_59 hcardT116_59
      (fun i => conj_mem_of_fixedPoints _ _ (T116_59 i) (hfix116_59 i) _)
      ⟨116, by decide⟩ ⟨59, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨59, by decide⟩ 23 hp) Q2.T116_59_2 Q2.hfix116_59_2 Q2.hinj116_59_2
      Q2.hcardT116_59_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_59_2 i) (Q2.hfix116_59_2 i) _)
      colCert_116_59_23.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_59_24 (hp : 24 < (Q2.transData.getD 59 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨59, by decide⟩ : Fin 148)) (colE2 ⟨59, by decide⟩ 24 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨59, by decide⟩ : Fin 148))
        (colE1 ⟨59, by decide⟩ 24 (transLenTr ⟨59, by decide⟩ 24 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨59, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨59, by decide⟩ 24 (transLenTr ⟨59, by decide⟩ 24 hp)) T116_59
      hfix116_59 hinj116_59 hcardT116_59
      (fun i => conj_mem_of_fixedPoints _ _ (T116_59 i) (hfix116_59 i) _)
      ⟨116, by decide⟩ ⟨59, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨59, by decide⟩ 24 hp) Q2.T116_59_2 Q2.hfix116_59_2 Q2.hinj116_59_2
      Q2.hcardT116_59_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_59_2 i) (Q2.hfix116_59_2 i) _)
      colCert_116_59_24.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_80_0 (hp : 0 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 0 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 0 (transLenTr ⟨80, by decide⟩ 0 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 0 (transLenTr ⟨80, by decide⟩ 0 hp)) T116_80
      hfix116_80 hinj116_80 hcardT116_80
      (fun i => conj_mem_of_fixedPoints _ _ (T116_80 i) (hfix116_80 i) _)
      ⟨116, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 0 hp) Q2.T116_80_2 Q2.hfix116_80_2 Q2.hinj116_80_2
      Q2.hcardT116_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_80_2 i) (Q2.hfix116_80_2 i) _)
      colCert_116_80_0.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_80_1 (hp : 1 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 1 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 1 (transLenTr ⟨80, by decide⟩ 1 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 1 (transLenTr ⟨80, by decide⟩ 1 hp)) T116_80
      hfix116_80 hinj116_80 hcardT116_80
      (fun i => conj_mem_of_fixedPoints _ _ (T116_80 i) (hfix116_80 i) _)
      ⟨116, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 1 hp) Q2.T116_80_2 Q2.hfix116_80_2 Q2.hinj116_80_2
      Q2.hcardT116_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_80_2 i) (Q2.hfix116_80_2 i) _)
      colCert_116_80_1.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_80_2 (hp : 2 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 2 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 2 (transLenTr ⟨80, by decide⟩ 2 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 2 (transLenTr ⟨80, by decide⟩ 2 hp)) T116_80
      hfix116_80 hinj116_80 hcardT116_80
      (fun i => conj_mem_of_fixedPoints _ _ (T116_80 i) (hfix116_80 i) _)
      ⟨116, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 2 hp) Q2.T116_80_2 Q2.hfix116_80_2 Q2.hinj116_80_2
      Q2.hcardT116_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_80_2 i) (Q2.hfix116_80_2 i) _)
      colCert_116_80_2.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_80_3 (hp : 3 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 3 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 3 (transLenTr ⟨80, by decide⟩ 3 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 3 (transLenTr ⟨80, by decide⟩ 3 hp)) T116_80
      hfix116_80 hinj116_80 hcardT116_80
      (fun i => conj_mem_of_fixedPoints _ _ (T116_80 i) (hfix116_80 i) _)
      ⟨116, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 3 hp) Q2.T116_80_2 Q2.hfix116_80_2 Q2.hinj116_80_2
      Q2.hcardT116_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_80_2 i) (Q2.hfix116_80_2 i) _)
      colCert_116_80_3.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_80_4 (hp : 4 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 4 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 4 (transLenTr ⟨80, by decide⟩ 4 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 4 (transLenTr ⟨80, by decide⟩ 4 hp)) T116_80
      hfix116_80 hinj116_80 hcardT116_80
      (fun i => conj_mem_of_fixedPoints _ _ (T116_80 i) (hfix116_80 i) _)
      ⟨116, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 4 hp) Q2.T116_80_2 Q2.hfix116_80_2 Q2.hinj116_80_2
      Q2.hcardT116_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_80_2 i) (Q2.hfix116_80_2 i) _)
      colCert_116_80_4.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_80_5 (hp : 5 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 5 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 5 (transLenTr ⟨80, by decide⟩ 5 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 5 (transLenTr ⟨80, by decide⟩ 5 hp)) T116_80
      hfix116_80 hinj116_80 hcardT116_80
      (fun i => conj_mem_of_fixedPoints _ _ (T116_80 i) (hfix116_80 i) _)
      ⟨116, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 5 hp) Q2.T116_80_2 Q2.hfix116_80_2 Q2.hinj116_80_2
      Q2.hcardT116_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_80_2 i) (Q2.hfix116_80_2 i) _)
      colCert_116_80_5.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_80_10 (hp : 10 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 10 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 10 (transLenTr ⟨80, by decide⟩ 10 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 10 (transLenTr ⟨80, by decide⟩ 10 hp)) T116_80
      hfix116_80 hinj116_80 hcardT116_80
      (fun i => conj_mem_of_fixedPoints _ _ (T116_80 i) (hfix116_80 i) _)
      ⟨116, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 10 hp) Q2.T116_80_2 Q2.hfix116_80_2 Q2.hinj116_80_2
      Q2.hcardT116_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_80_2 i) (Q2.hfix116_80_2 i) _)
      colCert_116_80_10.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_80_15 (hp : 15 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 15 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 15 (transLenTr ⟨80, by decide⟩ 15 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 15 (transLenTr ⟨80, by decide⟩ 15 hp)) T116_80
      hfix116_80 hinj116_80 hcardT116_80
      (fun i => conj_mem_of_fixedPoints _ _ (T116_80 i) (hfix116_80 i) _)
      ⟨116, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 15 hp) Q2.T116_80_2 Q2.hfix116_80_2 Q2.hinj116_80_2
      Q2.hcardT116_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_80_2 i) (Q2.hfix116_80_2 i) _)
      colCert_116_80_15.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_80_20 (hp : 20 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 20 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 20 (transLenTr ⟨80, by decide⟩ 20 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 20 (transLenTr ⟨80, by decide⟩ 20 hp)) T116_80
      hfix116_80 hinj116_80 hcardT116_80
      (fun i => conj_mem_of_fixedPoints _ _ (T116_80 i) (hfix116_80 i) _)
      ⟨116, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 20 hp) Q2.T116_80_2 Q2.hfix116_80_2 Q2.hinj116_80_2
      Q2.hcardT116_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_80_2 i) (Q2.hfix116_80_2 i) _)
      colCert_116_80_20.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_80_25 (hp : 25 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 25 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 25 (transLenTr ⟨80, by decide⟩ 25 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 25 (transLenTr ⟨80, by decide⟩ 25 hp)) T116_80
      hfix116_80 hinj116_80 hcardT116_80
      (fun i => conj_mem_of_fixedPoints _ _ (T116_80 i) (hfix116_80 i) _)
      ⟨116, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 25 hp) Q2.T116_80_2 Q2.hfix116_80_2 Q2.hinj116_80_2
      Q2.hcardT116_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_80_2 i) (Q2.hfix116_80_2 i) _)
      colCert_116_80_25.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_80_30 (hp : 30 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 30 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 30 (transLenTr ⟨80, by decide⟩ 30 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 30 (transLenTr ⟨80, by decide⟩ 30 hp)) T116_80
      hfix116_80 hinj116_80 hcardT116_80
      (fun i => conj_mem_of_fixedPoints _ _ (T116_80 i) (hfix116_80 i) _)
      ⟨116, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 30 hp) Q2.T116_80_2 Q2.hfix116_80_2 Q2.hinj116_80_2
      Q2.hcardT116_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_80_2 i) (Q2.hfix116_80_2 i) _)
      colCert_116_80_30.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_80_35 (hp : 35 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 35 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 35 (transLenTr ⟨80, by decide⟩ 35 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 35 (transLenTr ⟨80, by decide⟩ 35 hp)) T116_80
      hfix116_80 hinj116_80 hcardT116_80
      (fun i => conj_mem_of_fixedPoints _ _ (T116_80 i) (hfix116_80 i) _)
      ⟨116, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 35 hp) Q2.T116_80_2 Q2.hfix116_80_2 Q2.hinj116_80_2
      Q2.hcardT116_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_80_2 i) (Q2.hfix116_80_2 i) _)
      colCert_116_80_35.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_80_40 (hp : 40 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 40 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 40 (transLenTr ⟨80, by decide⟩ 40 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 40 (transLenTr ⟨80, by decide⟩ 40 hp)) T116_80
      hfix116_80 hinj116_80 hcardT116_80
      (fun i => conj_mem_of_fixedPoints _ _ (T116_80 i) (hfix116_80 i) _)
      ⟨116, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 40 hp) Q2.T116_80_2 Q2.hfix116_80_2 Q2.hinj116_80_2
      Q2.hcardT116_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_80_2 i) (Q2.hfix116_80_2 i) _)
      colCert_116_80_40.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_80_45 (hp : 45 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 45 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 45 (transLenTr ⟨80, by decide⟩ 45 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 45 (transLenTr ⟨80, by decide⟩ 45 hp)) T116_80
      hfix116_80 hinj116_80 hcardT116_80
      (fun i => conj_mem_of_fixedPoints _ _ (T116_80 i) (hfix116_80 i) _)
      ⟨116, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 45 hp) Q2.T116_80_2 Q2.hfix116_80_2 Q2.hinj116_80_2
      Q2.hcardT116_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_80_2 i) (Q2.hfix116_80_2 i) _)
      colCert_116_80_45.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_80_50 (hp : 50 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 50 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 50 (transLenTr ⟨80, by decide⟩ 50 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 50 (transLenTr ⟨80, by decide⟩ 50 hp)) T116_80
      hfix116_80 hinj116_80 hcardT116_80
      (fun i => conj_mem_of_fixedPoints _ _ (T116_80 i) (hfix116_80 i) _)
      ⟨116, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 50 hp) Q2.T116_80_2 Q2.hfix116_80_2 Q2.hinj116_80_2
      Q2.hcardT116_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_80_2 i) (Q2.hfix116_80_2 i) _)
      colCert_116_80_50.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_80_55 (hp : 55 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 55 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 55 (transLenTr ⟨80, by decide⟩ 55 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 55 (transLenTr ⟨80, by decide⟩ 55 hp)) T116_80
      hfix116_80 hinj116_80 hcardT116_80
      (fun i => conj_mem_of_fixedPoints _ _ (T116_80 i) (hfix116_80 i) _)
      ⟨116, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 55 hp) Q2.T116_80_2 Q2.hfix116_80_2 Q2.hinj116_80_2
      Q2.hcardT116_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_80_2 i) (Q2.hfix116_80_2 i) _)
      colCert_116_80_55.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_80_60 (hp : 60 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 60 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 60 (transLenTr ⟨80, by decide⟩ 60 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 60 (transLenTr ⟨80, by decide⟩ 60 hp)) T116_80
      hfix116_80 hinj116_80 hcardT116_80
      (fun i => conj_mem_of_fixedPoints _ _ (T116_80 i) (hfix116_80 i) _)
      ⟨116, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 60 hp) Q2.T116_80_2 Q2.hfix116_80_2 Q2.hinj116_80_2
      Q2.hcardT116_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_80_2 i) (Q2.hfix116_80_2 i) _)
      colCert_116_80_60.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_80_65 (hp : 65 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 65 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 65 (transLenTr ⟨80, by decide⟩ 65 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 65 (transLenTr ⟨80, by decide⟩ 65 hp)) T116_80
      hfix116_80 hinj116_80 hcardT116_80
      (fun i => conj_mem_of_fixedPoints _ _ (T116_80 i) (hfix116_80 i) _)
      ⟨116, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 65 hp) Q2.T116_80_2 Q2.hfix116_80_2 Q2.hinj116_80_2
      Q2.hcardT116_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_80_2 i) (Q2.hfix116_80_2 i) _)
      colCert_116_80_65.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_80_70 (hp : 70 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 70 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 70 (transLenTr ⟨80, by decide⟩ 70 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 70 (transLenTr ⟨80, by decide⟩ 70 hp)) T116_80
      hfix116_80 hinj116_80 hcardT116_80
      (fun i => conj_mem_of_fixedPoints _ _ (T116_80 i) (hfix116_80 i) _)
      ⟨116, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 70 hp) Q2.T116_80_2 Q2.hfix116_80_2 Q2.hinj116_80_2
      Q2.hcardT116_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_80_2 i) (Q2.hfix116_80_2 i) _)
      colCert_116_80_70.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_80_75 (hp : 75 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 75 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 75 (transLenTr ⟨80, by decide⟩ 75 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 75 (transLenTr ⟨80, by decide⟩ 75 hp)) T116_80
      hfix116_80 hinj116_80 hcardT116_80
      (fun i => conj_mem_of_fixedPoints _ _ (T116_80 i) (hfix116_80 i) _)
      ⟨116, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 75 hp) Q2.T116_80_2 Q2.hfix116_80_2 Q2.hinj116_80_2
      Q2.hcardT116_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_80_2 i) (Q2.hfix116_80_2 i) _)
      colCert_116_80_75.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_80_80 (hp : 80 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 80 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 80 (transLenTr ⟨80, by decide⟩ 80 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 80 (transLenTr ⟨80, by decide⟩ 80 hp)) T116_80
      hfix116_80 hinj116_80 hcardT116_80
      (fun i => conj_mem_of_fixedPoints _ _ (T116_80 i) (hfix116_80 i) _)
      ⟨116, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 80 hp) Q2.T116_80_2 Q2.hfix116_80_2 Q2.hinj116_80_2
      Q2.hcardT116_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_80_2 i) (Q2.hfix116_80_2 i) _)
      colCert_116_80_80.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_80_85 (hp : 85 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 85 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 85 (transLenTr ⟨80, by decide⟩ 85 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 85 (transLenTr ⟨80, by decide⟩ 85 hp)) T116_80
      hfix116_80 hinj116_80 hcardT116_80
      (fun i => conj_mem_of_fixedPoints _ _ (T116_80 i) (hfix116_80 i) _)
      ⟨116, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 85 hp) Q2.T116_80_2 Q2.hfix116_80_2 Q2.hinj116_80_2
      Q2.hcardT116_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_80_2 i) (Q2.hfix116_80_2 i) _)
      colCert_116_80_85.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_80_90 (hp : 90 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 90 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 90 (transLenTr ⟨80, by decide⟩ 90 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 90 (transLenTr ⟨80, by decide⟩ 90 hp)) T116_80
      hfix116_80 hinj116_80 hcardT116_80
      (fun i => conj_mem_of_fixedPoints _ _ (T116_80 i) (hfix116_80 i) _)
      ⟨116, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 90 hp) Q2.T116_80_2 Q2.hfix116_80_2 Q2.hinj116_80_2
      Q2.hcardT116_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_80_2 i) (Q2.hfix116_80_2 i) _)
      colCert_116_80_90.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_80_95 (hp : 95 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 95 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 95 (transLenTr ⟨80, by decide⟩ 95 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 95 (transLenTr ⟨80, by decide⟩ 95 hp)) T116_80
      hfix116_80 hinj116_80 hcardT116_80
      (fun i => conj_mem_of_fixedPoints _ _ (T116_80 i) (hfix116_80 i) _)
      ⟨116, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 95 hp) Q2.T116_80_2 Q2.hfix116_80_2 Q2.hinj116_80_2
      Q2.hcardT116_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_80_2 i) (Q2.hfix116_80_2 i) _)
      colCert_116_80_95.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_80_100 (hp : 100 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 100 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 100 (transLenTr ⟨80, by decide⟩ 100 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 100 (transLenTr ⟨80, by decide⟩ 100 hp)) T116_80
      hfix116_80 hinj116_80 hcardT116_80
      (fun i => conj_mem_of_fixedPoints _ _ (T116_80 i) (hfix116_80 i) _)
      ⟨116, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 100 hp) Q2.T116_80_2 Q2.hfix116_80_2 Q2.hinj116_80_2
      Q2.hcardT116_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_80_2 i) (Q2.hfix116_80_2 i) _)
      colCert_116_80_100.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_80_105 (hp : 105 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 105 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 105 (transLenTr ⟨80, by decide⟩ 105 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 105 (transLenTr ⟨80, by decide⟩ 105 hp)) T116_80
      hfix116_80 hinj116_80 hcardT116_80
      (fun i => conj_mem_of_fixedPoints _ _ (T116_80 i) (hfix116_80 i) _)
      ⟨116, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 105 hp) Q2.T116_80_2 Q2.hfix116_80_2 Q2.hinj116_80_2
      Q2.hcardT116_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_80_2 i) (Q2.hfix116_80_2 i) _)
      colCert_116_80_105.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_80_110 (hp : 110 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 110 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 110 (transLenTr ⟨80, by decide⟩ 110 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 110 (transLenTr ⟨80, by decide⟩ 110 hp)) T116_80
      hfix116_80 hinj116_80 hcardT116_80
      (fun i => conj_mem_of_fixedPoints _ _ (T116_80 i) (hfix116_80 i) _)
      ⟨116, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 110 hp) Q2.T116_80_2 Q2.hfix116_80_2 Q2.hinj116_80_2
      Q2.hcardT116_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_80_2 i) (Q2.hfix116_80_2 i) _)
      colCert_116_80_110.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_80_115 (hp : 115 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 115 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 115 (transLenTr ⟨80, by decide⟩ 115 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 115 (transLenTr ⟨80, by decide⟩ 115 hp)) T116_80
      hfix116_80 hinj116_80 hcardT116_80
      (fun i => conj_mem_of_fixedPoints _ _ (T116_80 i) (hfix116_80 i) _)
      ⟨116, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 115 hp) Q2.T116_80_2 Q2.hfix116_80_2 Q2.hinj116_80_2
      Q2.hcardT116_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_80_2 i) (Q2.hfix116_80_2 i) _)
      colCert_116_80_115.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_80_120 (hp : 120 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 120 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 120 (transLenTr ⟨80, by decide⟩ 120 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 120 (transLenTr ⟨80, by decide⟩ 120 hp)) T116_80
      hfix116_80 hinj116_80 hcardT116_80
      (fun i => conj_mem_of_fixedPoints _ _ (T116_80 i) (hfix116_80 i) _)
      ⟨116, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 120 hp) Q2.T116_80_2 Q2.hfix116_80_2 Q2.hinj116_80_2
      Q2.hcardT116_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_80_2 i) (Q2.hfix116_80_2 i) _)
      colCert_116_80_120.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_90_0 (hp : 0 < (Q2.transData.getD 90 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨90, by decide⟩ : Fin 148)) (colE2 ⟨90, by decide⟩ 0 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨90, by decide⟩ : Fin 148))
        (colE1 ⟨90, by decide⟩ 0 (transLenTr ⟨90, by decide⟩ 0 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨90, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨90, by decide⟩ 0 (transLenTr ⟨90, by decide⟩ 0 hp)) T116_90
      hfix116_90 hinj116_90 hcardT116_90
      (fun i => conj_mem_of_fixedPoints _ _ (T116_90 i) (hfix116_90 i) _)
      ⟨116, by decide⟩ ⟨90, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨90, by decide⟩ 0 hp) Q2.T116_90_2 Q2.hfix116_90_2 Q2.hinj116_90_2
      Q2.hcardT116_90_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_90_2 i) (Q2.hfix116_90_2 i) _)
      colCert_116_90_0.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_90_1 (hp : 1 < (Q2.transData.getD 90 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨90, by decide⟩ : Fin 148)) (colE2 ⟨90, by decide⟩ 1 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨90, by decide⟩ : Fin 148))
        (colE1 ⟨90, by decide⟩ 1 (transLenTr ⟨90, by decide⟩ 1 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨90, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨90, by decide⟩ 1 (transLenTr ⟨90, by decide⟩ 1 hp)) T116_90
      hfix116_90 hinj116_90 hcardT116_90
      (fun i => conj_mem_of_fixedPoints _ _ (T116_90 i) (hfix116_90 i) _)
      ⟨116, by decide⟩ ⟨90, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨90, by decide⟩ 1 hp) Q2.T116_90_2 Q2.hfix116_90_2 Q2.hinj116_90_2
      Q2.hcardT116_90_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_90_2 i) (Q2.hfix116_90_2 i) _)
      colCert_116_90_1.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_90_2 (hp : 2 < (Q2.transData.getD 90 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨90, by decide⟩ : Fin 148)) (colE2 ⟨90, by decide⟩ 2 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨90, by decide⟩ : Fin 148))
        (colE1 ⟨90, by decide⟩ 2 (transLenTr ⟨90, by decide⟩ 2 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨90, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨90, by decide⟩ 2 (transLenTr ⟨90, by decide⟩ 2 hp)) T116_90
      hfix116_90 hinj116_90 hcardT116_90
      (fun i => conj_mem_of_fixedPoints _ _ (T116_90 i) (hfix116_90 i) _)
      ⟨116, by decide⟩ ⟨90, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨90, by decide⟩ 2 hp) Q2.T116_90_2 Q2.hfix116_90_2 Q2.hinj116_90_2
      Q2.hcardT116_90_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_90_2 i) (Q2.hfix116_90_2 i) _)
      colCert_116_90_2.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_90_3 (hp : 3 < (Q2.transData.getD 90 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨90, by decide⟩ : Fin 148)) (colE2 ⟨90, by decide⟩ 3 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨90, by decide⟩ : Fin 148))
        (colE1 ⟨90, by decide⟩ 3 (transLenTr ⟨90, by decide⟩ 3 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨90, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨90, by decide⟩ 3 (transLenTr ⟨90, by decide⟩ 3 hp)) T116_90
      hfix116_90 hinj116_90 hcardT116_90
      (fun i => conj_mem_of_fixedPoints _ _ (T116_90 i) (hfix116_90 i) _)
      ⟨116, by decide⟩ ⟨90, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨90, by decide⟩ 3 hp) Q2.T116_90_2 Q2.hfix116_90_2 Q2.hinj116_90_2
      Q2.hcardT116_90_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_90_2 i) (Q2.hfix116_90_2 i) _)
      colCert_116_90_3.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_90_4 (hp : 4 < (Q2.transData.getD 90 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨90, by decide⟩ : Fin 148)) (colE2 ⟨90, by decide⟩ 4 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨90, by decide⟩ : Fin 148))
        (colE1 ⟨90, by decide⟩ 4 (transLenTr ⟨90, by decide⟩ 4 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨90, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨90, by decide⟩ 4 (transLenTr ⟨90, by decide⟩ 4 hp)) T116_90
      hfix116_90 hinj116_90 hcardT116_90
      (fun i => conj_mem_of_fixedPoints _ _ (T116_90 i) (hfix116_90 i) _)
      ⟨116, by decide⟩ ⟨90, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨90, by decide⟩ 4 hp) Q2.T116_90_2 Q2.hfix116_90_2 Q2.hinj116_90_2
      Q2.hcardT116_90_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_90_2 i) (Q2.hfix116_90_2 i) _)
      colCert_116_90_4.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_90_5 (hp : 5 < (Q2.transData.getD 90 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨90, by decide⟩ : Fin 148)) (colE2 ⟨90, by decide⟩ 5 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨90, by decide⟩ : Fin 148))
        (colE1 ⟨90, by decide⟩ 5 (transLenTr ⟨90, by decide⟩ 5 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨90, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨90, by decide⟩ 5 (transLenTr ⟨90, by decide⟩ 5 hp)) T116_90
      hfix116_90 hinj116_90 hcardT116_90
      (fun i => conj_mem_of_fixedPoints _ _ (T116_90 i) (hfix116_90 i) _)
      ⟨116, by decide⟩ ⟨90, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨90, by decide⟩ 5 hp) Q2.T116_90_2 Q2.hfix116_90_2 Q2.hinj116_90_2
      Q2.hcardT116_90_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_90_2 i) (Q2.hfix116_90_2 i) _)
      colCert_116_90_5.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_90_10 (hp : 10 < (Q2.transData.getD 90 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨90, by decide⟩ : Fin 148)) (colE2 ⟨90, by decide⟩ 10 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨90, by decide⟩ : Fin 148))
        (colE1 ⟨90, by decide⟩ 10 (transLenTr ⟨90, by decide⟩ 10 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨90, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨90, by decide⟩ 10 (transLenTr ⟨90, by decide⟩ 10 hp)) T116_90
      hfix116_90 hinj116_90 hcardT116_90
      (fun i => conj_mem_of_fixedPoints _ _ (T116_90 i) (hfix116_90 i) _)
      ⟨116, by decide⟩ ⟨90, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨90, by decide⟩ 10 hp) Q2.T116_90_2 Q2.hfix116_90_2 Q2.hinj116_90_2
      Q2.hcardT116_90_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_90_2 i) (Q2.hfix116_90_2 i) _)
      colCert_116_90_10.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_90_15 (hp : 15 < (Q2.transData.getD 90 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨90, by decide⟩ : Fin 148)) (colE2 ⟨90, by decide⟩ 15 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨90, by decide⟩ : Fin 148))
        (colE1 ⟨90, by decide⟩ 15 (transLenTr ⟨90, by decide⟩ 15 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨90, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨90, by decide⟩ 15 (transLenTr ⟨90, by decide⟩ 15 hp)) T116_90
      hfix116_90 hinj116_90 hcardT116_90
      (fun i => conj_mem_of_fixedPoints _ _ (T116_90 i) (hfix116_90 i) _)
      ⟨116, by decide⟩ ⟨90, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨90, by decide⟩ 15 hp) Q2.T116_90_2 Q2.hfix116_90_2 Q2.hinj116_90_2
      Q2.hcardT116_90_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_90_2 i) (Q2.hfix116_90_2 i) _)
      colCert_116_90_15.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_90_20 (hp : 20 < (Q2.transData.getD 90 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨90, by decide⟩ : Fin 148)) (colE2 ⟨90, by decide⟩ 20 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨90, by decide⟩ : Fin 148))
        (colE1 ⟨90, by decide⟩ 20 (transLenTr ⟨90, by decide⟩ 20 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨90, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨90, by decide⟩ 20 (transLenTr ⟨90, by decide⟩ 20 hp)) T116_90
      hfix116_90 hinj116_90 hcardT116_90
      (fun i => conj_mem_of_fixedPoints _ _ (T116_90 i) (hfix116_90 i) _)
      ⟨116, by decide⟩ ⟨90, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨90, by decide⟩ 20 hp) Q2.T116_90_2 Q2.hfix116_90_2 Q2.hinj116_90_2
      Q2.hcardT116_90_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_90_2 i) (Q2.hfix116_90_2 i) _)
      colCert_116_90_20.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_90_25 (hp : 25 < (Q2.transData.getD 90 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨90, by decide⟩ : Fin 148)) (colE2 ⟨90, by decide⟩ 25 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨90, by decide⟩ : Fin 148))
        (colE1 ⟨90, by decide⟩ 25 (transLenTr ⟨90, by decide⟩ 25 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨90, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨90, by decide⟩ 25 (transLenTr ⟨90, by decide⟩ 25 hp)) T116_90
      hfix116_90 hinj116_90 hcardT116_90
      (fun i => conj_mem_of_fixedPoints _ _ (T116_90 i) (hfix116_90 i) _)
      ⟨116, by decide⟩ ⟨90, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨90, by decide⟩ 25 hp) Q2.T116_90_2 Q2.hfix116_90_2 Q2.hinj116_90_2
      Q2.hcardT116_90_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_90_2 i) (Q2.hfix116_90_2 i) _)
      colCert_116_90_25.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_90_50 (hp : 50 < (Q2.transData.getD 90 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨90, by decide⟩ : Fin 148)) (colE2 ⟨90, by decide⟩ 50 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨90, by decide⟩ : Fin 148))
        (colE1 ⟨90, by decide⟩ 50 (transLenTr ⟨90, by decide⟩ 50 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨90, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨90, by decide⟩ 50 (transLenTr ⟨90, by decide⟩ 50 hp)) T116_90
      hfix116_90 hinj116_90 hcardT116_90
      (fun i => conj_mem_of_fixedPoints _ _ (T116_90 i) (hfix116_90 i) _)
      ⟨116, by decide⟩ ⟨90, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨90, by decide⟩ 50 hp) Q2.T116_90_2 Q2.hfix116_90_2 Q2.hinj116_90_2
      Q2.hcardT116_90_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_90_2 i) (Q2.hfix116_90_2 i) _)
      colCert_116_90_50.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_90_75 (hp : 75 < (Q2.transData.getD 90 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨90, by decide⟩ : Fin 148)) (colE2 ⟨90, by decide⟩ 75 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨90, by decide⟩ : Fin 148))
        (colE1 ⟨90, by decide⟩ 75 (transLenTr ⟨90, by decide⟩ 75 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨90, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨90, by decide⟩ 75 (transLenTr ⟨90, by decide⟩ 75 hp)) T116_90
      hfix116_90 hinj116_90 hcardT116_90
      (fun i => conj_mem_of_fixedPoints _ _ (T116_90 i) (hfix116_90 i) _)
      ⟨116, by decide⟩ ⟨90, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨90, by decide⟩ 75 hp) Q2.T116_90_2 Q2.hfix116_90_2 Q2.hinj116_90_2
      Q2.hcardT116_90_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_90_2 i) (Q2.hfix116_90_2 i) _)
      colCert_116_90_75.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_90_100 (hp : 100 < (Q2.transData.getD 90 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨90, by decide⟩ : Fin 148)) (colE2 ⟨90, by decide⟩ 100 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨90, by decide⟩ : Fin 148))
        (colE1 ⟨90, by decide⟩ 100 (transLenTr ⟨90, by decide⟩ 100 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨90, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨90, by decide⟩ 100 (transLenTr ⟨90, by decide⟩ 100 hp)) T116_90
      hfix116_90 hinj116_90 hcardT116_90
      (fun i => conj_mem_of_fixedPoints _ _ (T116_90 i) (hfix116_90 i) _)
      ⟨116, by decide⟩ ⟨90, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨90, by decide⟩ 100 hp) Q2.T116_90_2 Q2.hfix116_90_2 Q2.hinj116_90_2
      Q2.hcardT116_90_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_90_2 i) (Q2.hfix116_90_2 i) _)
      colCert_116_90_100.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_95_0 (hp : 0 < (Q2.transData.getD 95 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨95, by decide⟩ : Fin 148)) (colE2 ⟨95, by decide⟩ 0 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨95, by decide⟩ : Fin 148))
        (colE1 ⟨95, by decide⟩ 0 (transLenTr ⟨95, by decide⟩ 0 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨95, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨95, by decide⟩ 0 (transLenTr ⟨95, by decide⟩ 0 hp)) T116_95
      hfix116_95 hinj116_95 hcardT116_95
      (fun i => conj_mem_of_fixedPoints _ _ (T116_95 i) (hfix116_95 i) _)
      ⟨116, by decide⟩ ⟨95, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨95, by decide⟩ 0 hp) Q2.T116_95_2 Q2.hfix116_95_2 Q2.hinj116_95_2
      Q2.hcardT116_95_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_95_2 i) (Q2.hfix116_95_2 i) _)
      colCert_116_95_0.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_95_1 (hp : 1 < (Q2.transData.getD 95 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨95, by decide⟩ : Fin 148)) (colE2 ⟨95, by decide⟩ 1 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨95, by decide⟩ : Fin 148))
        (colE1 ⟨95, by decide⟩ 1 (transLenTr ⟨95, by decide⟩ 1 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨95, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨95, by decide⟩ 1 (transLenTr ⟨95, by decide⟩ 1 hp)) T116_95
      hfix116_95 hinj116_95 hcardT116_95
      (fun i => conj_mem_of_fixedPoints _ _ (T116_95 i) (hfix116_95 i) _)
      ⟨116, by decide⟩ ⟨95, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨95, by decide⟩ 1 hp) Q2.T116_95_2 Q2.hfix116_95_2 Q2.hinj116_95_2
      Q2.hcardT116_95_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_95_2 i) (Q2.hfix116_95_2 i) _)
      colCert_116_95_1.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_95_2 (hp : 2 < (Q2.transData.getD 95 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨95, by decide⟩ : Fin 148)) (colE2 ⟨95, by decide⟩ 2 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨95, by decide⟩ : Fin 148))
        (colE1 ⟨95, by decide⟩ 2 (transLenTr ⟨95, by decide⟩ 2 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨95, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨95, by decide⟩ 2 (transLenTr ⟨95, by decide⟩ 2 hp)) T116_95
      hfix116_95 hinj116_95 hcardT116_95
      (fun i => conj_mem_of_fixedPoints _ _ (T116_95 i) (hfix116_95 i) _)
      ⟨116, by decide⟩ ⟨95, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨95, by decide⟩ 2 hp) Q2.T116_95_2 Q2.hfix116_95_2 Q2.hinj116_95_2
      Q2.hcardT116_95_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_95_2 i) (Q2.hfix116_95_2 i) _)
      colCert_116_95_2.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_95_3 (hp : 3 < (Q2.transData.getD 95 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨95, by decide⟩ : Fin 148)) (colE2 ⟨95, by decide⟩ 3 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨95, by decide⟩ : Fin 148))
        (colE1 ⟨95, by decide⟩ 3 (transLenTr ⟨95, by decide⟩ 3 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨95, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨95, by decide⟩ 3 (transLenTr ⟨95, by decide⟩ 3 hp)) T116_95
      hfix116_95 hinj116_95 hcardT116_95
      (fun i => conj_mem_of_fixedPoints _ _ (T116_95 i) (hfix116_95 i) _)
      ⟨116, by decide⟩ ⟨95, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨95, by decide⟩ 3 hp) Q2.T116_95_2 Q2.hfix116_95_2 Q2.hinj116_95_2
      Q2.hcardT116_95_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_95_2 i) (Q2.hfix116_95_2 i) _)
      colCert_116_95_3.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_95_4 (hp : 4 < (Q2.transData.getD 95 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨95, by decide⟩ : Fin 148)) (colE2 ⟨95, by decide⟩ 4 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨95, by decide⟩ : Fin 148))
        (colE1 ⟨95, by decide⟩ 4 (transLenTr ⟨95, by decide⟩ 4 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨95, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨95, by decide⟩ 4 (transLenTr ⟨95, by decide⟩ 4 hp)) T116_95
      hfix116_95 hinj116_95 hcardT116_95
      (fun i => conj_mem_of_fixedPoints _ _ (T116_95 i) (hfix116_95 i) _)
      ⟨116, by decide⟩ ⟨95, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨95, by decide⟩ 4 hp) Q2.T116_95_2 Q2.hfix116_95_2 Q2.hinj116_95_2
      Q2.hcardT116_95_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_95_2 i) (Q2.hfix116_95_2 i) _)
      colCert_116_95_4.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_95_5 (hp : 5 < (Q2.transData.getD 95 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨95, by decide⟩ : Fin 148)) (colE2 ⟨95, by decide⟩ 5 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨95, by decide⟩ : Fin 148))
        (colE1 ⟨95, by decide⟩ 5 (transLenTr ⟨95, by decide⟩ 5 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨95, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨95, by decide⟩ 5 (transLenTr ⟨95, by decide⟩ 5 hp)) T116_95
      hfix116_95 hinj116_95 hcardT116_95
      (fun i => conj_mem_of_fixedPoints _ _ (T116_95 i) (hfix116_95 i) _)
      ⟨116, by decide⟩ ⟨95, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨95, by decide⟩ 5 hp) Q2.T116_95_2 Q2.hfix116_95_2 Q2.hinj116_95_2
      Q2.hcardT116_95_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_95_2 i) (Q2.hfix116_95_2 i) _)
      colCert_116_95_5.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_95_10 (hp : 10 < (Q2.transData.getD 95 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨95, by decide⟩ : Fin 148)) (colE2 ⟨95, by decide⟩ 10 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨95, by decide⟩ : Fin 148))
        (colE1 ⟨95, by decide⟩ 10 (transLenTr ⟨95, by decide⟩ 10 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨95, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨95, by decide⟩ 10 (transLenTr ⟨95, by decide⟩ 10 hp)) T116_95
      hfix116_95 hinj116_95 hcardT116_95
      (fun i => conj_mem_of_fixedPoints _ _ (T116_95 i) (hfix116_95 i) _)
      ⟨116, by decide⟩ ⟨95, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨95, by decide⟩ 10 hp) Q2.T116_95_2 Q2.hfix116_95_2 Q2.hinj116_95_2
      Q2.hcardT116_95_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_95_2 i) (Q2.hfix116_95_2 i) _)
      colCert_116_95_10.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_95_15 (hp : 15 < (Q2.transData.getD 95 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨95, by decide⟩ : Fin 148)) (colE2 ⟨95, by decide⟩ 15 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨95, by decide⟩ : Fin 148))
        (colE1 ⟨95, by decide⟩ 15 (transLenTr ⟨95, by decide⟩ 15 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨95, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨95, by decide⟩ 15 (transLenTr ⟨95, by decide⟩ 15 hp)) T116_95
      hfix116_95 hinj116_95 hcardT116_95
      (fun i => conj_mem_of_fixedPoints _ _ (T116_95 i) (hfix116_95 i) _)
      ⟨116, by decide⟩ ⟨95, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨95, by decide⟩ 15 hp) Q2.T116_95_2 Q2.hfix116_95_2 Q2.hinj116_95_2
      Q2.hcardT116_95_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_95_2 i) (Q2.hfix116_95_2 i) _)
      colCert_116_95_15.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_95_20 (hp : 20 < (Q2.transData.getD 95 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨95, by decide⟩ : Fin 148)) (colE2 ⟨95, by decide⟩ 20 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨95, by decide⟩ : Fin 148))
        (colE1 ⟨95, by decide⟩ 20 (transLenTr ⟨95, by decide⟩ 20 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨95, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨95, by decide⟩ 20 (transLenTr ⟨95, by decide⟩ 20 hp)) T116_95
      hfix116_95 hinj116_95 hcardT116_95
      (fun i => conj_mem_of_fixedPoints _ _ (T116_95 i) (hfix116_95 i) _)
      ⟨116, by decide⟩ ⟨95, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨95, by decide⟩ 20 hp) Q2.T116_95_2 Q2.hfix116_95_2 Q2.hinj116_95_2
      Q2.hcardT116_95_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_95_2 i) (Q2.hfix116_95_2 i) _)
      colCert_116_95_20.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_95_25 (hp : 25 < (Q2.transData.getD 95 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨95, by decide⟩ : Fin 148)) (colE2 ⟨95, by decide⟩ 25 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨95, by decide⟩ : Fin 148))
        (colE1 ⟨95, by decide⟩ 25 (transLenTr ⟨95, by decide⟩ 25 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨95, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨95, by decide⟩ 25 (transLenTr ⟨95, by decide⟩ 25 hp)) T116_95
      hfix116_95 hinj116_95 hcardT116_95
      (fun i => conj_mem_of_fixedPoints _ _ (T116_95 i) (hfix116_95 i) _)
      ⟨116, by decide⟩ ⟨95, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨95, by decide⟩ 25 hp) Q2.T116_95_2 Q2.hfix116_95_2 Q2.hinj116_95_2
      Q2.hcardT116_95_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_95_2 i) (Q2.hfix116_95_2 i) _)
      colCert_116_95_25.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_95_50 (hp : 50 < (Q2.transData.getD 95 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨95, by decide⟩ : Fin 148)) (colE2 ⟨95, by decide⟩ 50 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨95, by decide⟩ : Fin 148))
        (colE1 ⟨95, by decide⟩ 50 (transLenTr ⟨95, by decide⟩ 50 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨95, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨95, by decide⟩ 50 (transLenTr ⟨95, by decide⟩ 50 hp)) T116_95
      hfix116_95 hinj116_95 hcardT116_95
      (fun i => conj_mem_of_fixedPoints _ _ (T116_95 i) (hfix116_95 i) _)
      ⟨116, by decide⟩ ⟨95, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨95, by decide⟩ 50 hp) Q2.T116_95_2 Q2.hfix116_95_2 Q2.hinj116_95_2
      Q2.hcardT116_95_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_95_2 i) (Q2.hfix116_95_2 i) _)
      colCert_116_95_50.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_95_75 (hp : 75 < (Q2.transData.getD 95 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨95, by decide⟩ : Fin 148)) (colE2 ⟨95, by decide⟩ 75 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨95, by decide⟩ : Fin 148))
        (colE1 ⟨95, by decide⟩ 75 (transLenTr ⟨95, by decide⟩ 75 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨95, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨95, by decide⟩ 75 (transLenTr ⟨95, by decide⟩ 75 hp)) T116_95
      hfix116_95 hinj116_95 hcardT116_95
      (fun i => conj_mem_of_fixedPoints _ _ (T116_95 i) (hfix116_95 i) _)
      ⟨116, by decide⟩ ⟨95, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨95, by decide⟩ 75 hp) Q2.T116_95_2 Q2.hfix116_95_2 Q2.hinj116_95_2
      Q2.hcardT116_95_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_95_2 i) (Q2.hfix116_95_2 i) _)
      colCert_116_95_75.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_95_100 (hp : 100 < (Q2.transData.getD 95 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨95, by decide⟩ : Fin 148)) (colE2 ⟨95, by decide⟩ 100 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨95, by decide⟩ : Fin 148))
        (colE1 ⟨95, by decide⟩ 100 (transLenTr ⟨95, by decide⟩ 100 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨95, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨95, by decide⟩ 100 (transLenTr ⟨95, by decide⟩ 100 hp)) T116_95
      hfix116_95 hinj116_95 hcardT116_95
      (fun i => conj_mem_of_fixedPoints _ _ (T116_95 i) (hfix116_95 i) _)
      ⟨116, by decide⟩ ⟨95, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨95, by decide⟩ 100 hp) Q2.T116_95_2 Q2.hfix116_95_2 Q2.hinj116_95_2
      Q2.hcardT116_95_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_95_2 i) (Q2.hfix116_95_2 i) _)
      colCert_116_95_100.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_100_0 (hp : 0 < (Q2.transData.getD 100 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨100, by decide⟩ : Fin 148)) (colE2 ⟨100, by decide⟩ 0 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨100, by decide⟩ : Fin 148))
        (colE1 ⟨100, by decide⟩ 0 (transLenTr ⟨100, by decide⟩ 0 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨100, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨100, by decide⟩ 0 (transLenTr ⟨100, by decide⟩ 0 hp)) T116_100
      hfix116_100 hinj116_100 hcardT116_100
      (fun i => conj_mem_of_fixedPoints _ _ (T116_100 i) (hfix116_100 i) _)
      ⟨116, by decide⟩ ⟨100, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨100, by decide⟩ 0 hp) Q2.T116_100_2 Q2.hfix116_100_2 Q2.hinj116_100_2
      Q2.hcardT116_100_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_100_2 i) (Q2.hfix116_100_2 i) _)
      colCert_116_100_0.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_100_1 (hp : 1 < (Q2.transData.getD 100 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨100, by decide⟩ : Fin 148)) (colE2 ⟨100, by decide⟩ 1 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨100, by decide⟩ : Fin 148))
        (colE1 ⟨100, by decide⟩ 1 (transLenTr ⟨100, by decide⟩ 1 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨100, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨100, by decide⟩ 1 (transLenTr ⟨100, by decide⟩ 1 hp)) T116_100
      hfix116_100 hinj116_100 hcardT116_100
      (fun i => conj_mem_of_fixedPoints _ _ (T116_100 i) (hfix116_100 i) _)
      ⟨116, by decide⟩ ⟨100, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨100, by decide⟩ 1 hp) Q2.T116_100_2 Q2.hfix116_100_2 Q2.hinj116_100_2
      Q2.hcardT116_100_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_100_2 i) (Q2.hfix116_100_2 i) _)
      colCert_116_100_1.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_100_2 (hp : 2 < (Q2.transData.getD 100 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨100, by decide⟩ : Fin 148)) (colE2 ⟨100, by decide⟩ 2 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨100, by decide⟩ : Fin 148))
        (colE1 ⟨100, by decide⟩ 2 (transLenTr ⟨100, by decide⟩ 2 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨100, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨100, by decide⟩ 2 (transLenTr ⟨100, by decide⟩ 2 hp)) T116_100
      hfix116_100 hinj116_100 hcardT116_100
      (fun i => conj_mem_of_fixedPoints _ _ (T116_100 i) (hfix116_100 i) _)
      ⟨116, by decide⟩ ⟨100, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨100, by decide⟩ 2 hp) Q2.T116_100_2 Q2.hfix116_100_2 Q2.hinj116_100_2
      Q2.hcardT116_100_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_100_2 i) (Q2.hfix116_100_2 i) _)
      colCert_116_100_2.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_100_3 (hp : 3 < (Q2.transData.getD 100 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨100, by decide⟩ : Fin 148)) (colE2 ⟨100, by decide⟩ 3 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨100, by decide⟩ : Fin 148))
        (colE1 ⟨100, by decide⟩ 3 (transLenTr ⟨100, by decide⟩ 3 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨100, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨100, by decide⟩ 3 (transLenTr ⟨100, by decide⟩ 3 hp)) T116_100
      hfix116_100 hinj116_100 hcardT116_100
      (fun i => conj_mem_of_fixedPoints _ _ (T116_100 i) (hfix116_100 i) _)
      ⟨116, by decide⟩ ⟨100, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨100, by decide⟩ 3 hp) Q2.T116_100_2 Q2.hfix116_100_2 Q2.hinj116_100_2
      Q2.hcardT116_100_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_100_2 i) (Q2.hfix116_100_2 i) _)
      colCert_116_100_3.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_100_4 (hp : 4 < (Q2.transData.getD 100 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨100, by decide⟩ : Fin 148)) (colE2 ⟨100, by decide⟩ 4 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨100, by decide⟩ : Fin 148))
        (colE1 ⟨100, by decide⟩ 4 (transLenTr ⟨100, by decide⟩ 4 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨100, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨100, by decide⟩ 4 (transLenTr ⟨100, by decide⟩ 4 hp)) T116_100
      hfix116_100 hinj116_100 hcardT116_100
      (fun i => conj_mem_of_fixedPoints _ _ (T116_100 i) (hfix116_100 i) _)
      ⟨116, by decide⟩ ⟨100, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨100, by decide⟩ 4 hp) Q2.T116_100_2 Q2.hfix116_100_2 Q2.hinj116_100_2
      Q2.hcardT116_100_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_100_2 i) (Q2.hfix116_100_2 i) _)
      colCert_116_100_4.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_100_5 (hp : 5 < (Q2.transData.getD 100 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨100, by decide⟩ : Fin 148)) (colE2 ⟨100, by decide⟩ 5 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨100, by decide⟩ : Fin 148))
        (colE1 ⟨100, by decide⟩ 5 (transLenTr ⟨100, by decide⟩ 5 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨100, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨100, by decide⟩ 5 (transLenTr ⟨100, by decide⟩ 5 hp)) T116_100
      hfix116_100 hinj116_100 hcardT116_100
      (fun i => conj_mem_of_fixedPoints _ _ (T116_100 i) (hfix116_100 i) _)
      ⟨116, by decide⟩ ⟨100, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨100, by decide⟩ 5 hp) Q2.T116_100_2 Q2.hfix116_100_2 Q2.hinj116_100_2
      Q2.hcardT116_100_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_100_2 i) (Q2.hfix116_100_2 i) _)
      colCert_116_100_5.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_100_10 (hp : 10 < (Q2.transData.getD 100 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨100, by decide⟩ : Fin 148)) (colE2 ⟨100, by decide⟩ 10 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨100, by decide⟩ : Fin 148))
        (colE1 ⟨100, by decide⟩ 10 (transLenTr ⟨100, by decide⟩ 10 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨100, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨100, by decide⟩ 10 (transLenTr ⟨100, by decide⟩ 10 hp)) T116_100
      hfix116_100 hinj116_100 hcardT116_100
      (fun i => conj_mem_of_fixedPoints _ _ (T116_100 i) (hfix116_100 i) _)
      ⟨116, by decide⟩ ⟨100, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨100, by decide⟩ 10 hp) Q2.T116_100_2 Q2.hfix116_100_2 Q2.hinj116_100_2
      Q2.hcardT116_100_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_100_2 i) (Q2.hfix116_100_2 i) _)
      colCert_116_100_10.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_100_15 (hp : 15 < (Q2.transData.getD 100 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨100, by decide⟩ : Fin 148)) (colE2 ⟨100, by decide⟩ 15 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨100, by decide⟩ : Fin 148))
        (colE1 ⟨100, by decide⟩ 15 (transLenTr ⟨100, by decide⟩ 15 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨100, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨100, by decide⟩ 15 (transLenTr ⟨100, by decide⟩ 15 hp)) T116_100
      hfix116_100 hinj116_100 hcardT116_100
      (fun i => conj_mem_of_fixedPoints _ _ (T116_100 i) (hfix116_100 i) _)
      ⟨116, by decide⟩ ⟨100, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨100, by decide⟩ 15 hp) Q2.T116_100_2 Q2.hfix116_100_2 Q2.hinj116_100_2
      Q2.hcardT116_100_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_100_2 i) (Q2.hfix116_100_2 i) _)
      colCert_116_100_15.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_100_20 (hp : 20 < (Q2.transData.getD 100 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨100, by decide⟩ : Fin 148)) (colE2 ⟨100, by decide⟩ 20 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨100, by decide⟩ : Fin 148))
        (colE1 ⟨100, by decide⟩ 20 (transLenTr ⟨100, by decide⟩ 20 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨100, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨100, by decide⟩ 20 (transLenTr ⟨100, by decide⟩ 20 hp)) T116_100
      hfix116_100 hinj116_100 hcardT116_100
      (fun i => conj_mem_of_fixedPoints _ _ (T116_100 i) (hfix116_100 i) _)
      ⟨116, by decide⟩ ⟨100, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨100, by decide⟩ 20 hp) Q2.T116_100_2 Q2.hfix116_100_2 Q2.hinj116_100_2
      Q2.hcardT116_100_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_100_2 i) (Q2.hfix116_100_2 i) _)
      colCert_116_100_20.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_100_25 (hp : 25 < (Q2.transData.getD 100 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨100, by decide⟩ : Fin 148)) (colE2 ⟨100, by decide⟩ 25 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨100, by decide⟩ : Fin 148))
        (colE1 ⟨100, by decide⟩ 25 (transLenTr ⟨100, by decide⟩ 25 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨100, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨100, by decide⟩ 25 (transLenTr ⟨100, by decide⟩ 25 hp)) T116_100
      hfix116_100 hinj116_100 hcardT116_100
      (fun i => conj_mem_of_fixedPoints _ _ (T116_100 i) (hfix116_100 i) _)
      ⟨116, by decide⟩ ⟨100, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨100, by decide⟩ 25 hp) Q2.T116_100_2 Q2.hfix116_100_2 Q2.hinj116_100_2
      Q2.hcardT116_100_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_100_2 i) (Q2.hfix116_100_2 i) _)
      colCert_116_100_25.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_100_50 (hp : 50 < (Q2.transData.getD 100 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨100, by decide⟩ : Fin 148)) (colE2 ⟨100, by decide⟩ 50 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨100, by decide⟩ : Fin 148))
        (colE1 ⟨100, by decide⟩ 50 (transLenTr ⟨100, by decide⟩ 50 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨100, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨100, by decide⟩ 50 (transLenTr ⟨100, by decide⟩ 50 hp)) T116_100
      hfix116_100 hinj116_100 hcardT116_100
      (fun i => conj_mem_of_fixedPoints _ _ (T116_100 i) (hfix116_100 i) _)
      ⟨116, by decide⟩ ⟨100, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨100, by decide⟩ 50 hp) Q2.T116_100_2 Q2.hfix116_100_2 Q2.hinj116_100_2
      Q2.hcardT116_100_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_100_2 i) (Q2.hfix116_100_2 i) _)
      colCert_116_100_50.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_100_75 (hp : 75 < (Q2.transData.getD 100 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨100, by decide⟩ : Fin 148)) (colE2 ⟨100, by decide⟩ 75 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨100, by decide⟩ : Fin 148))
        (colE1 ⟨100, by decide⟩ 75 (transLenTr ⟨100, by decide⟩ 75 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨100, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨100, by decide⟩ 75 (transLenTr ⟨100, by decide⟩ 75 hp)) T116_100
      hfix116_100 hinj116_100 hcardT116_100
      (fun i => conj_mem_of_fixedPoints _ _ (T116_100 i) (hfix116_100 i) _)
      ⟨116, by decide⟩ ⟨100, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨100, by decide⟩ 75 hp) Q2.T116_100_2 Q2.hfix116_100_2 Q2.hinj116_100_2
      Q2.hcardT116_100_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_100_2 i) (Q2.hfix116_100_2 i) _)
      colCert_116_100_75.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_100_100 (hp : 100 < (Q2.transData.getD 100 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨100, by decide⟩ : Fin 148)) (colE2 ⟨100, by decide⟩ 100 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨100, by decide⟩ : Fin 148))
        (colE1 ⟨100, by decide⟩ 100 (transLenTr ⟨100, by decide⟩ 100 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨100, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨100, by decide⟩ 100 (transLenTr ⟨100, by decide⟩ 100 hp)) T116_100
      hfix116_100 hinj116_100 hcardT116_100
      (fun i => conj_mem_of_fixedPoints _ _ (T116_100 i) (hfix116_100 i) _)
      ⟨116, by decide⟩ ⟨100, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨100, by decide⟩ 100 hp) Q2.T116_100_2 Q2.hfix116_100_2 Q2.hinj116_100_2
      Q2.hcardT116_100_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_100_2 i) (Q2.hfix116_100_2 i) _)
      colCert_116_100_100.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_105_0 (hp : 0 < (Q2.transData.getD 105 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨105, by decide⟩ : Fin 148)) (colE2 ⟨105, by decide⟩ 0 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨105, by decide⟩ : Fin 148))
        (colE1 ⟨105, by decide⟩ 0 (transLenTr ⟨105, by decide⟩ 0 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨105, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨105, by decide⟩ 0 (transLenTr ⟨105, by decide⟩ 0 hp)) T116_105
      hfix116_105 hinj116_105 hcardT116_105
      (fun i => conj_mem_of_fixedPoints _ _ (T116_105 i) (hfix116_105 i) _)
      ⟨116, by decide⟩ ⟨105, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨105, by decide⟩ 0 hp) Q2.T116_105_2 Q2.hfix116_105_2 Q2.hinj116_105_2
      Q2.hcardT116_105_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_105_2 i) (Q2.hfix116_105_2 i) _)
      colCert_116_105_0.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_105_1 (hp : 1 < (Q2.transData.getD 105 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨105, by decide⟩ : Fin 148)) (colE2 ⟨105, by decide⟩ 1 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨105, by decide⟩ : Fin 148))
        (colE1 ⟨105, by decide⟩ 1 (transLenTr ⟨105, by decide⟩ 1 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨105, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨105, by decide⟩ 1 (transLenTr ⟨105, by decide⟩ 1 hp)) T116_105
      hfix116_105 hinj116_105 hcardT116_105
      (fun i => conj_mem_of_fixedPoints _ _ (T116_105 i) (hfix116_105 i) _)
      ⟨116, by decide⟩ ⟨105, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨105, by decide⟩ 1 hp) Q2.T116_105_2 Q2.hfix116_105_2 Q2.hinj116_105_2
      Q2.hcardT116_105_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_105_2 i) (Q2.hfix116_105_2 i) _)
      colCert_116_105_1.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_105_2 (hp : 2 < (Q2.transData.getD 105 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨105, by decide⟩ : Fin 148)) (colE2 ⟨105, by decide⟩ 2 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨105, by decide⟩ : Fin 148))
        (colE1 ⟨105, by decide⟩ 2 (transLenTr ⟨105, by decide⟩ 2 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨105, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨105, by decide⟩ 2 (transLenTr ⟨105, by decide⟩ 2 hp)) T116_105
      hfix116_105 hinj116_105 hcardT116_105
      (fun i => conj_mem_of_fixedPoints _ _ (T116_105 i) (hfix116_105 i) _)
      ⟨116, by decide⟩ ⟨105, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨105, by decide⟩ 2 hp) Q2.T116_105_2 Q2.hfix116_105_2 Q2.hinj116_105_2
      Q2.hcardT116_105_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_105_2 i) (Q2.hfix116_105_2 i) _)
      colCert_116_105_2.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_105_3 (hp : 3 < (Q2.transData.getD 105 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨105, by decide⟩ : Fin 148)) (colE2 ⟨105, by decide⟩ 3 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨105, by decide⟩ : Fin 148))
        (colE1 ⟨105, by decide⟩ 3 (transLenTr ⟨105, by decide⟩ 3 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨105, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨105, by decide⟩ 3 (transLenTr ⟨105, by decide⟩ 3 hp)) T116_105
      hfix116_105 hinj116_105 hcardT116_105
      (fun i => conj_mem_of_fixedPoints _ _ (T116_105 i) (hfix116_105 i) _)
      ⟨116, by decide⟩ ⟨105, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨105, by decide⟩ 3 hp) Q2.T116_105_2 Q2.hfix116_105_2 Q2.hinj116_105_2
      Q2.hcardT116_105_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_105_2 i) (Q2.hfix116_105_2 i) _)
      colCert_116_105_3.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_105_4 (hp : 4 < (Q2.transData.getD 105 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨105, by decide⟩ : Fin 148)) (colE2 ⟨105, by decide⟩ 4 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨105, by decide⟩ : Fin 148))
        (colE1 ⟨105, by decide⟩ 4 (transLenTr ⟨105, by decide⟩ 4 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨105, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨105, by decide⟩ 4 (transLenTr ⟨105, by decide⟩ 4 hp)) T116_105
      hfix116_105 hinj116_105 hcardT116_105
      (fun i => conj_mem_of_fixedPoints _ _ (T116_105 i) (hfix116_105 i) _)
      ⟨116, by decide⟩ ⟨105, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨105, by decide⟩ 4 hp) Q2.T116_105_2 Q2.hfix116_105_2 Q2.hinj116_105_2
      Q2.hcardT116_105_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_105_2 i) (Q2.hfix116_105_2 i) _)
      colCert_116_105_4.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_105_5 (hp : 5 < (Q2.transData.getD 105 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨105, by decide⟩ : Fin 148)) (colE2 ⟨105, by decide⟩ 5 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨105, by decide⟩ : Fin 148))
        (colE1 ⟨105, by decide⟩ 5 (transLenTr ⟨105, by decide⟩ 5 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨105, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨105, by decide⟩ 5 (transLenTr ⟨105, by decide⟩ 5 hp)) T116_105
      hfix116_105 hinj116_105 hcardT116_105
      (fun i => conj_mem_of_fixedPoints _ _ (T116_105 i) (hfix116_105 i) _)
      ⟨116, by decide⟩ ⟨105, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨105, by decide⟩ 5 hp) Q2.T116_105_2 Q2.hfix116_105_2 Q2.hinj116_105_2
      Q2.hcardT116_105_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_105_2 i) (Q2.hfix116_105_2 i) _)
      colCert_116_105_5.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_105_10 (hp : 10 < (Q2.transData.getD 105 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨105, by decide⟩ : Fin 148)) (colE2 ⟨105, by decide⟩ 10 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨105, by decide⟩ : Fin 148))
        (colE1 ⟨105, by decide⟩ 10 (transLenTr ⟨105, by decide⟩ 10 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨105, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨105, by decide⟩ 10 (transLenTr ⟨105, by decide⟩ 10 hp)) T116_105
      hfix116_105 hinj116_105 hcardT116_105
      (fun i => conj_mem_of_fixedPoints _ _ (T116_105 i) (hfix116_105 i) _)
      ⟨116, by decide⟩ ⟨105, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨105, by decide⟩ 10 hp) Q2.T116_105_2 Q2.hfix116_105_2 Q2.hinj116_105_2
      Q2.hcardT116_105_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_105_2 i) (Q2.hfix116_105_2 i) _)
      colCert_116_105_10.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_105_15 (hp : 15 < (Q2.transData.getD 105 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨105, by decide⟩ : Fin 148)) (colE2 ⟨105, by decide⟩ 15 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨105, by decide⟩ : Fin 148))
        (colE1 ⟨105, by decide⟩ 15 (transLenTr ⟨105, by decide⟩ 15 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨105, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨105, by decide⟩ 15 (transLenTr ⟨105, by decide⟩ 15 hp)) T116_105
      hfix116_105 hinj116_105 hcardT116_105
      (fun i => conj_mem_of_fixedPoints _ _ (T116_105 i) (hfix116_105 i) _)
      ⟨116, by decide⟩ ⟨105, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨105, by decide⟩ 15 hp) Q2.T116_105_2 Q2.hfix116_105_2 Q2.hinj116_105_2
      Q2.hcardT116_105_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_105_2 i) (Q2.hfix116_105_2 i) _)
      colCert_116_105_15.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_105_20 (hp : 20 < (Q2.transData.getD 105 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨105, by decide⟩ : Fin 148)) (colE2 ⟨105, by decide⟩ 20 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨105, by decide⟩ : Fin 148))
        (colE1 ⟨105, by decide⟩ 20 (transLenTr ⟨105, by decide⟩ 20 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨105, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨105, by decide⟩ 20 (transLenTr ⟨105, by decide⟩ 20 hp)) T116_105
      hfix116_105 hinj116_105 hcardT116_105
      (fun i => conj_mem_of_fixedPoints _ _ (T116_105 i) (hfix116_105 i) _)
      ⟨116, by decide⟩ ⟨105, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨105, by decide⟩ 20 hp) Q2.T116_105_2 Q2.hfix116_105_2 Q2.hinj116_105_2
      Q2.hcardT116_105_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_105_2 i) (Q2.hfix116_105_2 i) _)
      colCert_116_105_20.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_105_25 (hp : 25 < (Q2.transData.getD 105 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨105, by decide⟩ : Fin 148)) (colE2 ⟨105, by decide⟩ 25 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨105, by decide⟩ : Fin 148))
        (colE1 ⟨105, by decide⟩ 25 (transLenTr ⟨105, by decide⟩ 25 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨105, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨105, by decide⟩ 25 (transLenTr ⟨105, by decide⟩ 25 hp)) T116_105
      hfix116_105 hinj116_105 hcardT116_105
      (fun i => conj_mem_of_fixedPoints _ _ (T116_105 i) (hfix116_105 i) _)
      ⟨116, by decide⟩ ⟨105, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨105, by decide⟩ 25 hp) Q2.T116_105_2 Q2.hfix116_105_2 Q2.hinj116_105_2
      Q2.hcardT116_105_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_105_2 i) (Q2.hfix116_105_2 i) _)
      colCert_116_105_25.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_105_50 (hp : 50 < (Q2.transData.getD 105 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨105, by decide⟩ : Fin 148)) (colE2 ⟨105, by decide⟩ 50 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨105, by decide⟩ : Fin 148))
        (colE1 ⟨105, by decide⟩ 50 (transLenTr ⟨105, by decide⟩ 50 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨105, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨105, by decide⟩ 50 (transLenTr ⟨105, by decide⟩ 50 hp)) T116_105
      hfix116_105 hinj116_105 hcardT116_105
      (fun i => conj_mem_of_fixedPoints _ _ (T116_105 i) (hfix116_105 i) _)
      ⟨116, by decide⟩ ⟨105, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨105, by decide⟩ 50 hp) Q2.T116_105_2 Q2.hfix116_105_2 Q2.hinj116_105_2
      Q2.hcardT116_105_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_105_2 i) (Q2.hfix116_105_2 i) _)
      colCert_116_105_50.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_105_75 (hp : 75 < (Q2.transData.getD 105 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨105, by decide⟩ : Fin 148)) (colE2 ⟨105, by decide⟩ 75 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨105, by decide⟩ : Fin 148))
        (colE1 ⟨105, by decide⟩ 75 (transLenTr ⟨105, by decide⟩ 75 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨105, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨105, by decide⟩ 75 (transLenTr ⟨105, by decide⟩ 75 hp)) T116_105
      hfix116_105 hinj116_105 hcardT116_105
      (fun i => conj_mem_of_fixedPoints _ _ (T116_105 i) (hfix116_105 i) _)
      ⟨116, by decide⟩ ⟨105, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨105, by decide⟩ 75 hp) Q2.T116_105_2 Q2.hfix116_105_2 Q2.hinj116_105_2
      Q2.hcardT116_105_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_105_2 i) (Q2.hfix116_105_2 i) _)
      colCert_116_105_75.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_105_100 (hp : 100 < (Q2.transData.getD 105 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨105, by decide⟩ : Fin 148)) (colE2 ⟨105, by decide⟩ 100 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨105, by decide⟩ : Fin 148))
        (colE1 ⟨105, by decide⟩ 100 (transLenTr ⟨105, by decide⟩ 100 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨105, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨105, by decide⟩ 100 (transLenTr ⟨105, by decide⟩ 100 hp)) T116_105
      hfix116_105 hinj116_105 hcardT116_105
      (fun i => conj_mem_of_fixedPoints _ _ (T116_105 i) (hfix116_105 i) _)
      ⟨116, by decide⟩ ⟨105, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨105, by decide⟩ 100 hp) Q2.T116_105_2 Q2.hfix116_105_2 Q2.hinj116_105_2
      Q2.hcardT116_105_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_105_2 i) (Q2.hfix116_105_2 i) _)
      colCert_116_105_100.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_110_0 (hp : 0 < (Q2.transData.getD 110 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨110, by decide⟩ : Fin 148)) (colE2 ⟨110, by decide⟩ 0 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨110, by decide⟩ : Fin 148))
        (colE1 ⟨110, by decide⟩ 0 (transLenTr ⟨110, by decide⟩ 0 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨110, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨110, by decide⟩ 0 (transLenTr ⟨110, by decide⟩ 0 hp)) T116_110
      hfix116_110 hinj116_110 hcardT116_110
      (fun i => conj_mem_of_fixedPoints _ _ (T116_110 i) (hfix116_110 i) _)
      ⟨116, by decide⟩ ⟨110, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨110, by decide⟩ 0 hp) Q2.T116_110_2 Q2.hfix116_110_2 Q2.hinj116_110_2
      Q2.hcardT116_110_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_110_2 i) (Q2.hfix116_110_2 i) _)
      colCert_116_110_0.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_110_1 (hp : 1 < (Q2.transData.getD 110 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨110, by decide⟩ : Fin 148)) (colE2 ⟨110, by decide⟩ 1 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨110, by decide⟩ : Fin 148))
        (colE1 ⟨110, by decide⟩ 1 (transLenTr ⟨110, by decide⟩ 1 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨110, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨110, by decide⟩ 1 (transLenTr ⟨110, by decide⟩ 1 hp)) T116_110
      hfix116_110 hinj116_110 hcardT116_110
      (fun i => conj_mem_of_fixedPoints _ _ (T116_110 i) (hfix116_110 i) _)
      ⟨116, by decide⟩ ⟨110, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨110, by decide⟩ 1 hp) Q2.T116_110_2 Q2.hfix116_110_2 Q2.hinj116_110_2
      Q2.hcardT116_110_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_110_2 i) (Q2.hfix116_110_2 i) _)
      colCert_116_110_1.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_110_2 (hp : 2 < (Q2.transData.getD 110 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨110, by decide⟩ : Fin 148)) (colE2 ⟨110, by decide⟩ 2 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨110, by decide⟩ : Fin 148))
        (colE1 ⟨110, by decide⟩ 2 (transLenTr ⟨110, by decide⟩ 2 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨110, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨110, by decide⟩ 2 (transLenTr ⟨110, by decide⟩ 2 hp)) T116_110
      hfix116_110 hinj116_110 hcardT116_110
      (fun i => conj_mem_of_fixedPoints _ _ (T116_110 i) (hfix116_110 i) _)
      ⟨116, by decide⟩ ⟨110, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨110, by decide⟩ 2 hp) Q2.T116_110_2 Q2.hfix116_110_2 Q2.hinj116_110_2
      Q2.hcardT116_110_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_110_2 i) (Q2.hfix116_110_2 i) _)
      colCert_116_110_2.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_110_3 (hp : 3 < (Q2.transData.getD 110 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨110, by decide⟩ : Fin 148)) (colE2 ⟨110, by decide⟩ 3 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨110, by decide⟩ : Fin 148))
        (colE1 ⟨110, by decide⟩ 3 (transLenTr ⟨110, by decide⟩ 3 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨110, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨110, by decide⟩ 3 (transLenTr ⟨110, by decide⟩ 3 hp)) T116_110
      hfix116_110 hinj116_110 hcardT116_110
      (fun i => conj_mem_of_fixedPoints _ _ (T116_110 i) (hfix116_110 i) _)
      ⟨116, by decide⟩ ⟨110, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨110, by decide⟩ 3 hp) Q2.T116_110_2 Q2.hfix116_110_2 Q2.hinj116_110_2
      Q2.hcardT116_110_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_110_2 i) (Q2.hfix116_110_2 i) _)
      colCert_116_110_3.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_110_4 (hp : 4 < (Q2.transData.getD 110 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨110, by decide⟩ : Fin 148)) (colE2 ⟨110, by decide⟩ 4 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨110, by decide⟩ : Fin 148))
        (colE1 ⟨110, by decide⟩ 4 (transLenTr ⟨110, by decide⟩ 4 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨110, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨110, by decide⟩ 4 (transLenTr ⟨110, by decide⟩ 4 hp)) T116_110
      hfix116_110 hinj116_110 hcardT116_110
      (fun i => conj_mem_of_fixedPoints _ _ (T116_110 i) (hfix116_110 i) _)
      ⟨116, by decide⟩ ⟨110, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨110, by decide⟩ 4 hp) Q2.T116_110_2 Q2.hfix116_110_2 Q2.hinj116_110_2
      Q2.hcardT116_110_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_110_2 i) (Q2.hfix116_110_2 i) _)
      colCert_116_110_4.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_110_5 (hp : 5 < (Q2.transData.getD 110 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨110, by decide⟩ : Fin 148)) (colE2 ⟨110, by decide⟩ 5 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨110, by decide⟩ : Fin 148))
        (colE1 ⟨110, by decide⟩ 5 (transLenTr ⟨110, by decide⟩ 5 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨110, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨110, by decide⟩ 5 (transLenTr ⟨110, by decide⟩ 5 hp)) T116_110
      hfix116_110 hinj116_110 hcardT116_110
      (fun i => conj_mem_of_fixedPoints _ _ (T116_110 i) (hfix116_110 i) _)
      ⟨116, by decide⟩ ⟨110, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨110, by decide⟩ 5 hp) Q2.T116_110_2 Q2.hfix116_110_2 Q2.hinj116_110_2
      Q2.hcardT116_110_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_110_2 i) (Q2.hfix116_110_2 i) _)
      colCert_116_110_5.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_110_10 (hp : 10 < (Q2.transData.getD 110 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨110, by decide⟩ : Fin 148)) (colE2 ⟨110, by decide⟩ 10 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨110, by decide⟩ : Fin 148))
        (colE1 ⟨110, by decide⟩ 10 (transLenTr ⟨110, by decide⟩ 10 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨110, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨110, by decide⟩ 10 (transLenTr ⟨110, by decide⟩ 10 hp)) T116_110
      hfix116_110 hinj116_110 hcardT116_110
      (fun i => conj_mem_of_fixedPoints _ _ (T116_110 i) (hfix116_110 i) _)
      ⟨116, by decide⟩ ⟨110, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨110, by decide⟩ 10 hp) Q2.T116_110_2 Q2.hfix116_110_2 Q2.hinj116_110_2
      Q2.hcardT116_110_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_110_2 i) (Q2.hfix116_110_2 i) _)
      colCert_116_110_10.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_110_15 (hp : 15 < (Q2.transData.getD 110 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨110, by decide⟩ : Fin 148)) (colE2 ⟨110, by decide⟩ 15 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨110, by decide⟩ : Fin 148))
        (colE1 ⟨110, by decide⟩ 15 (transLenTr ⟨110, by decide⟩ 15 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨110, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨110, by decide⟩ 15 (transLenTr ⟨110, by decide⟩ 15 hp)) T116_110
      hfix116_110 hinj116_110 hcardT116_110
      (fun i => conj_mem_of_fixedPoints _ _ (T116_110 i) (hfix116_110 i) _)
      ⟨116, by decide⟩ ⟨110, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨110, by decide⟩ 15 hp) Q2.T116_110_2 Q2.hfix116_110_2 Q2.hinj116_110_2
      Q2.hcardT116_110_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_110_2 i) (Q2.hfix116_110_2 i) _)
      colCert_116_110_15.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_110_20 (hp : 20 < (Q2.transData.getD 110 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨110, by decide⟩ : Fin 148)) (colE2 ⟨110, by decide⟩ 20 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨110, by decide⟩ : Fin 148))
        (colE1 ⟨110, by decide⟩ 20 (transLenTr ⟨110, by decide⟩ 20 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨110, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨110, by decide⟩ 20 (transLenTr ⟨110, by decide⟩ 20 hp)) T116_110
      hfix116_110 hinj116_110 hcardT116_110
      (fun i => conj_mem_of_fixedPoints _ _ (T116_110 i) (hfix116_110 i) _)
      ⟨116, by decide⟩ ⟨110, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨110, by decide⟩ 20 hp) Q2.T116_110_2 Q2.hfix116_110_2 Q2.hinj116_110_2
      Q2.hcardT116_110_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_110_2 i) (Q2.hfix116_110_2 i) _)
      colCert_116_110_20.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_110_25 (hp : 25 < (Q2.transData.getD 110 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨110, by decide⟩ : Fin 148)) (colE2 ⟨110, by decide⟩ 25 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨110, by decide⟩ : Fin 148))
        (colE1 ⟨110, by decide⟩ 25 (transLenTr ⟨110, by decide⟩ 25 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨110, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨110, by decide⟩ 25 (transLenTr ⟨110, by decide⟩ 25 hp)) T116_110
      hfix116_110 hinj116_110 hcardT116_110
      (fun i => conj_mem_of_fixedPoints _ _ (T116_110 i) (hfix116_110 i) _)
      ⟨116, by decide⟩ ⟨110, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨110, by decide⟩ 25 hp) Q2.T116_110_2 Q2.hfix116_110_2 Q2.hinj116_110_2
      Q2.hcardT116_110_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_110_2 i) (Q2.hfix116_110_2 i) _)
      colCert_116_110_25.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_110_50 (hp : 50 < (Q2.transData.getD 110 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨110, by decide⟩ : Fin 148)) (colE2 ⟨110, by decide⟩ 50 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨110, by decide⟩ : Fin 148))
        (colE1 ⟨110, by decide⟩ 50 (transLenTr ⟨110, by decide⟩ 50 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨110, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨110, by decide⟩ 50 (transLenTr ⟨110, by decide⟩ 50 hp)) T116_110
      hfix116_110 hinj116_110 hcardT116_110
      (fun i => conj_mem_of_fixedPoints _ _ (T116_110 i) (hfix116_110 i) _)
      ⟨116, by decide⟩ ⟨110, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨110, by decide⟩ 50 hp) Q2.T116_110_2 Q2.hfix116_110_2 Q2.hinj116_110_2
      Q2.hcardT116_110_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_110_2 i) (Q2.hfix116_110_2 i) _)
      colCert_116_110_50.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_110_75 (hp : 75 < (Q2.transData.getD 110 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨110, by decide⟩ : Fin 148)) (colE2 ⟨110, by decide⟩ 75 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨110, by decide⟩ : Fin 148))
        (colE1 ⟨110, by decide⟩ 75 (transLenTr ⟨110, by decide⟩ 75 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨110, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨110, by decide⟩ 75 (transLenTr ⟨110, by decide⟩ 75 hp)) T116_110
      hfix116_110 hinj116_110 hcardT116_110
      (fun i => conj_mem_of_fixedPoints _ _ (T116_110 i) (hfix116_110 i) _)
      ⟨116, by decide⟩ ⟨110, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨110, by decide⟩ 75 hp) Q2.T116_110_2 Q2.hfix116_110_2 Q2.hinj116_110_2
      Q2.hcardT116_110_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_110_2 i) (Q2.hfix116_110_2 i) _)
      colCert_116_110_75.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_110_100 (hp : 100 < (Q2.transData.getD 110 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨110, by decide⟩ : Fin 148)) (colE2 ⟨110, by decide⟩ 100 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨110, by decide⟩ : Fin 148))
        (colE1 ⟨110, by decide⟩ 100 (transLenTr ⟨110, by decide⟩ 100 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨110, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨110, by decide⟩ 100 (transLenTr ⟨110, by decide⟩ 100 hp)) T116_110
      hfix116_110 hinj116_110 hcardT116_110
      (fun i => conj_mem_of_fixedPoints _ _ (T116_110 i) (hfix116_110 i) _)
      ⟨116, by decide⟩ ⟨110, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨110, by decide⟩ 100 hp) Q2.T116_110_2 Q2.hfix116_110_2 Q2.hinj116_110_2
      Q2.hcardT116_110_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_110_2 i) (Q2.hfix116_110_2 i) _)
      colCert_116_110_100.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_116_0 (hp : 0 < (Q2.transData.getD 116 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨116, by decide⟩ : Fin 148)) (colE2 ⟨116, by decide⟩ 0 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨116, by decide⟩ : Fin 148))
        (colE1 ⟨116, by decide⟩ 0 (transLenTr ⟨116, by decide⟩ 0 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨116, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨116, by decide⟩ 0 (transLenTr ⟨116, by decide⟩ 0 hp)) T116_116
      hfix116_116 hinj116_116 hcardT116_116
      (fun i => conj_mem_of_fixedPoints _ _ (T116_116 i) (hfix116_116 i) _)
      ⟨116, by decide⟩ ⟨116, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨116, by decide⟩ 0 hp) Q2.T116_116_2 Q2.hfix116_116_2 Q2.hinj116_116_2
      Q2.hcardT116_116_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_116_2 i) (Q2.hfix116_116_2 i) _)
      colCert_116_116_0.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_116_1 (hp : 1 < (Q2.transData.getD 116 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨116, by decide⟩ : Fin 148)) (colE2 ⟨116, by decide⟩ 1 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨116, by decide⟩ : Fin 148))
        (colE1 ⟨116, by decide⟩ 1 (transLenTr ⟨116, by decide⟩ 1 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨116, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨116, by decide⟩ 1 (transLenTr ⟨116, by decide⟩ 1 hp)) T116_116
      hfix116_116 hinj116_116 hcardT116_116
      (fun i => conj_mem_of_fixedPoints _ _ (T116_116 i) (hfix116_116 i) _)
      ⟨116, by decide⟩ ⟨116, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨116, by decide⟩ 1 hp) Q2.T116_116_2 Q2.hfix116_116_2 Q2.hinj116_116_2
      Q2.hcardT116_116_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_116_2 i) (Q2.hfix116_116_2 i) _)
      colCert_116_116_1.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_116_2 (hp : 2 < (Q2.transData.getD 116 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨116, by decide⟩ : Fin 148)) (colE2 ⟨116, by decide⟩ 2 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨116, by decide⟩ : Fin 148))
        (colE1 ⟨116, by decide⟩ 2 (transLenTr ⟨116, by decide⟩ 2 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨116, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨116, by decide⟩ 2 (transLenTr ⟨116, by decide⟩ 2 hp)) T116_116
      hfix116_116 hinj116_116 hcardT116_116
      (fun i => conj_mem_of_fixedPoints _ _ (T116_116 i) (hfix116_116 i) _)
      ⟨116, by decide⟩ ⟨116, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨116, by decide⟩ 2 hp) Q2.T116_116_2 Q2.hfix116_116_2 Q2.hinj116_116_2
      Q2.hcardT116_116_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_116_2 i) (Q2.hfix116_116_2 i) _)
      colCert_116_116_2.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_116_3 (hp : 3 < (Q2.transData.getD 116 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨116, by decide⟩ : Fin 148)) (colE2 ⟨116, by decide⟩ 3 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨116, by decide⟩ : Fin 148))
        (colE1 ⟨116, by decide⟩ 3 (transLenTr ⟨116, by decide⟩ 3 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨116, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨116, by decide⟩ 3 (transLenTr ⟨116, by decide⟩ 3 hp)) T116_116
      hfix116_116 hinj116_116 hcardT116_116
      (fun i => conj_mem_of_fixedPoints _ _ (T116_116 i) (hfix116_116 i) _)
      ⟨116, by decide⟩ ⟨116, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨116, by decide⟩ 3 hp) Q2.T116_116_2 Q2.hfix116_116_2 Q2.hinj116_116_2
      Q2.hcardT116_116_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_116_2 i) (Q2.hfix116_116_2 i) _)
      colCert_116_116_3.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_116_4 (hp : 4 < (Q2.transData.getD 116 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨116, by decide⟩ : Fin 148)) (colE2 ⟨116, by decide⟩ 4 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨116, by decide⟩ : Fin 148))
        (colE1 ⟨116, by decide⟩ 4 (transLenTr ⟨116, by decide⟩ 4 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨116, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨116, by decide⟩ 4 (transLenTr ⟨116, by decide⟩ 4 hp)) T116_116
      hfix116_116 hinj116_116 hcardT116_116
      (fun i => conj_mem_of_fixedPoints _ _ (T116_116 i) (hfix116_116 i) _)
      ⟨116, by decide⟩ ⟨116, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨116, by decide⟩ 4 hp) Q2.T116_116_2 Q2.hfix116_116_2 Q2.hinj116_116_2
      Q2.hcardT116_116_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_116_2 i) (Q2.hfix116_116_2 i) _)
      colCert_116_116_4.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_116_5 (hp : 5 < (Q2.transData.getD 116 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨116, by decide⟩ : Fin 148)) (colE2 ⟨116, by decide⟩ 5 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨116, by decide⟩ : Fin 148))
        (colE1 ⟨116, by decide⟩ 5 (transLenTr ⟨116, by decide⟩ 5 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨116, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨116, by decide⟩ 5 (transLenTr ⟨116, by decide⟩ 5 hp)) T116_116
      hfix116_116 hinj116_116 hcardT116_116
      (fun i => conj_mem_of_fixedPoints _ _ (T116_116 i) (hfix116_116 i) _)
      ⟨116, by decide⟩ ⟨116, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨116, by decide⟩ 5 hp) Q2.T116_116_2 Q2.hfix116_116_2 Q2.hinj116_116_2
      Q2.hcardT116_116_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_116_2 i) (Q2.hfix116_116_2 i) _)
      colCert_116_116_5.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_116_6 (hp : 6 < (Q2.transData.getD 116 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨116, by decide⟩ : Fin 148)) (colE2 ⟨116, by decide⟩ 6 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨116, by decide⟩ : Fin 148))
        (colE1 ⟨116, by decide⟩ 6 (transLenTr ⟨116, by decide⟩ 6 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨116, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨116, by decide⟩ 6 (transLenTr ⟨116, by decide⟩ 6 hp)) T116_116
      hfix116_116 hinj116_116 hcardT116_116
      (fun i => conj_mem_of_fixedPoints _ _ (T116_116 i) (hfix116_116 i) _)
      ⟨116, by decide⟩ ⟨116, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨116, by decide⟩ 6 hp) Q2.T116_116_2 Q2.hfix116_116_2 Q2.hinj116_116_2
      Q2.hcardT116_116_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_116_2 i) (Q2.hfix116_116_2 i) _)
      colCert_116_116_6.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_116_7 (hp : 7 < (Q2.transData.getD 116 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨116, by decide⟩ : Fin 148)) (colE2 ⟨116, by decide⟩ 7 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨116, by decide⟩ : Fin 148))
        (colE1 ⟨116, by decide⟩ 7 (transLenTr ⟨116, by decide⟩ 7 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨116, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨116, by decide⟩ 7 (transLenTr ⟨116, by decide⟩ 7 hp)) T116_116
      hfix116_116 hinj116_116 hcardT116_116
      (fun i => conj_mem_of_fixedPoints _ _ (T116_116 i) (hfix116_116 i) _)
      ⟨116, by decide⟩ ⟨116, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨116, by decide⟩ 7 hp) Q2.T116_116_2 Q2.hfix116_116_2 Q2.hinj116_116_2
      Q2.hcardT116_116_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_116_2 i) (Q2.hfix116_116_2 i) _)
      colCert_116_116_7.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_116_8 (hp : 8 < (Q2.transData.getD 116 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨116, by decide⟩ : Fin 148)) (colE2 ⟨116, by decide⟩ 8 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨116, by decide⟩ : Fin 148))
        (colE1 ⟨116, by decide⟩ 8 (transLenTr ⟨116, by decide⟩ 8 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨116, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨116, by decide⟩ 8 (transLenTr ⟨116, by decide⟩ 8 hp)) T116_116
      hfix116_116 hinj116_116 hcardT116_116
      (fun i => conj_mem_of_fixedPoints _ _ (T116_116 i) (hfix116_116 i) _)
      ⟨116, by decide⟩ ⟨116, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨116, by decide⟩ 8 hp) Q2.T116_116_2 Q2.hfix116_116_2 Q2.hinj116_116_2
      Q2.hcardT116_116_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_116_2 i) (Q2.hfix116_116_2 i) _)
      colCert_116_116_8.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_116_9 (hp : 9 < (Q2.transData.getD 116 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨116, by decide⟩ : Fin 148)) (colE2 ⟨116, by decide⟩ 9 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨116, by decide⟩ : Fin 148))
        (colE1 ⟨116, by decide⟩ 9 (transLenTr ⟨116, by decide⟩ 9 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨116, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨116, by decide⟩ 9 (transLenTr ⟨116, by decide⟩ 9 hp)) T116_116
      hfix116_116 hinj116_116 hcardT116_116
      (fun i => conj_mem_of_fixedPoints _ _ (T116_116 i) (hfix116_116 i) _)
      ⟨116, by decide⟩ ⟨116, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨116, by decide⟩ 9 hp) Q2.T116_116_2 Q2.hfix116_116_2 Q2.hinj116_116_2
      Q2.hcardT116_116_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_116_2 i) (Q2.hfix116_116_2 i) _)
      colCert_116_116_9.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_116_10 (hp : 10 < (Q2.transData.getD 116 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨116, by decide⟩ : Fin 148)) (colE2 ⟨116, by decide⟩ 10 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨116, by decide⟩ : Fin 148))
        (colE1 ⟨116, by decide⟩ 10 (transLenTr ⟨116, by decide⟩ 10 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨116, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨116, by decide⟩ 10 (transLenTr ⟨116, by decide⟩ 10 hp)) T116_116
      hfix116_116 hinj116_116 hcardT116_116
      (fun i => conj_mem_of_fixedPoints _ _ (T116_116 i) (hfix116_116 i) _)
      ⟨116, by decide⟩ ⟨116, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨116, by decide⟩ 10 hp) Q2.T116_116_2 Q2.hfix116_116_2 Q2.hinj116_116_2
      Q2.hcardT116_116_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_116_2 i) (Q2.hfix116_116_2 i) _)
      colCert_116_116_10.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_116_11 (hp : 11 < (Q2.transData.getD 116 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨116, by decide⟩ : Fin 148)) (colE2 ⟨116, by decide⟩ 11 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨116, by decide⟩ : Fin 148))
        (colE1 ⟨116, by decide⟩ 11 (transLenTr ⟨116, by decide⟩ 11 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨116, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨116, by decide⟩ 11 (transLenTr ⟨116, by decide⟩ 11 hp)) T116_116
      hfix116_116 hinj116_116 hcardT116_116
      (fun i => conj_mem_of_fixedPoints _ _ (T116_116 i) (hfix116_116 i) _)
      ⟨116, by decide⟩ ⟨116, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨116, by decide⟩ 11 hp) Q2.T116_116_2 Q2.hfix116_116_2 Q2.hinj116_116_2
      Q2.hcardT116_116_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_116_2 i) (Q2.hfix116_116_2 i) _)
      colCert_116_116_11.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_116_12 (hp : 12 < (Q2.transData.getD 116 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨116, by decide⟩ : Fin 148)) (colE2 ⟨116, by decide⟩ 12 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨116, by decide⟩ : Fin 148))
        (colE1 ⟨116, by decide⟩ 12 (transLenTr ⟨116, by decide⟩ 12 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨116, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨116, by decide⟩ 12 (transLenTr ⟨116, by decide⟩ 12 hp)) T116_116
      hfix116_116 hinj116_116 hcardT116_116
      (fun i => conj_mem_of_fixedPoints _ _ (T116_116 i) (hfix116_116 i) _)
      ⟨116, by decide⟩ ⟨116, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨116, by decide⟩ 12 hp) Q2.T116_116_2 Q2.hfix116_116_2 Q2.hinj116_116_2
      Q2.hcardT116_116_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_116_2 i) (Q2.hfix116_116_2 i) _)
      colCert_116_116_12.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_116_13 (hp : 13 < (Q2.transData.getD 116 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨116, by decide⟩ : Fin 148)) (colE2 ⟨116, by decide⟩ 13 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨116, by decide⟩ : Fin 148))
        (colE1 ⟨116, by decide⟩ 13 (transLenTr ⟨116, by decide⟩ 13 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨116, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨116, by decide⟩ 13 (transLenTr ⟨116, by decide⟩ 13 hp)) T116_116
      hfix116_116 hinj116_116 hcardT116_116
      (fun i => conj_mem_of_fixedPoints _ _ (T116_116 i) (hfix116_116 i) _)
      ⟨116, by decide⟩ ⟨116, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨116, by decide⟩ 13 hp) Q2.T116_116_2 Q2.hfix116_116_2 Q2.hinj116_116_2
      Q2.hcardT116_116_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_116_2 i) (Q2.hfix116_116_2 i) _)
      colCert_116_116_13.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_116_14 (hp : 14 < (Q2.transData.getD 116 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨116, by decide⟩ : Fin 148)) (colE2 ⟨116, by decide⟩ 14 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨116, by decide⟩ : Fin 148))
        (colE1 ⟨116, by decide⟩ 14 (transLenTr ⟨116, by decide⟩ 14 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨116, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨116, by decide⟩ 14 (transLenTr ⟨116, by decide⟩ 14 hp)) T116_116
      hfix116_116 hinj116_116 hcardT116_116
      (fun i => conj_mem_of_fixedPoints _ _ (T116_116 i) (hfix116_116 i) _)
      ⟨116, by decide⟩ ⟨116, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨116, by decide⟩ 14 hp) Q2.T116_116_2 Q2.hfix116_116_2 Q2.hinj116_116_2
      Q2.hcardT116_116_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_116_2 i) (Q2.hfix116_116_2 i) _)
      colCert_116_116_14.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_116_15 (hp : 15 < (Q2.transData.getD 116 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨116, by decide⟩ : Fin 148)) (colE2 ⟨116, by decide⟩ 15 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨116, by decide⟩ : Fin 148))
        (colE1 ⟨116, by decide⟩ 15 (transLenTr ⟨116, by decide⟩ 15 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨116, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨116, by decide⟩ 15 (transLenTr ⟨116, by decide⟩ 15 hp)) T116_116
      hfix116_116 hinj116_116 hcardT116_116
      (fun i => conj_mem_of_fixedPoints _ _ (T116_116 i) (hfix116_116 i) _)
      ⟨116, by decide⟩ ⟨116, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨116, by decide⟩ 15 hp) Q2.T116_116_2 Q2.hfix116_116_2 Q2.hinj116_116_2
      Q2.hcardT116_116_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_116_2 i) (Q2.hfix116_116_2 i) _)
      colCert_116_116_15.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_116_16 (hp : 16 < (Q2.transData.getD 116 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨116, by decide⟩ : Fin 148)) (colE2 ⟨116, by decide⟩ 16 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨116, by decide⟩ : Fin 148))
        (colE1 ⟨116, by decide⟩ 16 (transLenTr ⟨116, by decide⟩ 16 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨116, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨116, by decide⟩ 16 (transLenTr ⟨116, by decide⟩ 16 hp)) T116_116
      hfix116_116 hinj116_116 hcardT116_116
      (fun i => conj_mem_of_fixedPoints _ _ (T116_116 i) (hfix116_116 i) _)
      ⟨116, by decide⟩ ⟨116, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨116, by decide⟩ 16 hp) Q2.T116_116_2 Q2.hfix116_116_2 Q2.hinj116_116_2
      Q2.hcardT116_116_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_116_2 i) (Q2.hfix116_116_2 i) _)
      colCert_116_116_16.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_116_17 (hp : 17 < (Q2.transData.getD 116 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨116, by decide⟩ : Fin 148)) (colE2 ⟨116, by decide⟩ 17 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨116, by decide⟩ : Fin 148))
        (colE1 ⟨116, by decide⟩ 17 (transLenTr ⟨116, by decide⟩ 17 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨116, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨116, by decide⟩ 17 (transLenTr ⟨116, by decide⟩ 17 hp)) T116_116
      hfix116_116 hinj116_116 hcardT116_116
      (fun i => conj_mem_of_fixedPoints _ _ (T116_116 i) (hfix116_116 i) _)
      ⟨116, by decide⟩ ⟨116, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨116, by decide⟩ 17 hp) Q2.T116_116_2 Q2.hfix116_116_2 Q2.hinj116_116_2
      Q2.hcardT116_116_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_116_2 i) (Q2.hfix116_116_2 i) _)
      colCert_116_116_17.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_116_18 (hp : 18 < (Q2.transData.getD 116 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨116, by decide⟩ : Fin 148)) (colE2 ⟨116, by decide⟩ 18 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨116, by decide⟩ : Fin 148))
        (colE1 ⟨116, by decide⟩ 18 (transLenTr ⟨116, by decide⟩ 18 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨116, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨116, by decide⟩ 18 (transLenTr ⟨116, by decide⟩ 18 hp)) T116_116
      hfix116_116 hinj116_116 hcardT116_116
      (fun i => conj_mem_of_fixedPoints _ _ (T116_116 i) (hfix116_116 i) _)
      ⟨116, by decide⟩ ⟨116, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨116, by decide⟩ 18 hp) Q2.T116_116_2 Q2.hfix116_116_2 Q2.hinj116_116_2
      Q2.hcardT116_116_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_116_2 i) (Q2.hfix116_116_2 i) _)
      colCert_116_116_18.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_116_19 (hp : 19 < (Q2.transData.getD 116 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨116, by decide⟩ : Fin 148)) (colE2 ⟨116, by decide⟩ 19 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨116, by decide⟩ : Fin 148))
        (colE1 ⟨116, by decide⟩ 19 (transLenTr ⟨116, by decide⟩ 19 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨116, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨116, by decide⟩ 19 (transLenTr ⟨116, by decide⟩ 19 hp)) T116_116
      hfix116_116 hinj116_116 hcardT116_116
      (fun i => conj_mem_of_fixedPoints _ _ (T116_116 i) (hfix116_116 i) _)
      ⟨116, by decide⟩ ⟨116, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨116, by decide⟩ 19 hp) Q2.T116_116_2 Q2.hfix116_116_2 Q2.hinj116_116_2
      Q2.hcardT116_116_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_116_2 i) (Q2.hfix116_116_2 i) _)
      colCert_116_116_19.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_116_20 (hp : 20 < (Q2.transData.getD 116 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨116, by decide⟩ : Fin 148)) (colE2 ⟨116, by decide⟩ 20 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨116, by decide⟩ : Fin 148))
        (colE1 ⟨116, by decide⟩ 20 (transLenTr ⟨116, by decide⟩ 20 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨116, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨116, by decide⟩ 20 (transLenTr ⟨116, by decide⟩ 20 hp)) T116_116
      hfix116_116 hinj116_116 hcardT116_116
      (fun i => conj_mem_of_fixedPoints _ _ (T116_116 i) (hfix116_116 i) _)
      ⟨116, by decide⟩ ⟨116, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨116, by decide⟩ 20 hp) Q2.T116_116_2 Q2.hfix116_116_2 Q2.hinj116_116_2
      Q2.hcardT116_116_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_116_2 i) (Q2.hfix116_116_2 i) _)
      colCert_116_116_20.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_116_21 (hp : 21 < (Q2.transData.getD 116 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨116, by decide⟩ : Fin 148)) (colE2 ⟨116, by decide⟩ 21 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨116, by decide⟩ : Fin 148))
        (colE1 ⟨116, by decide⟩ 21 (transLenTr ⟨116, by decide⟩ 21 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨116, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨116, by decide⟩ 21 (transLenTr ⟨116, by decide⟩ 21 hp)) T116_116
      hfix116_116 hinj116_116 hcardT116_116
      (fun i => conj_mem_of_fixedPoints _ _ (T116_116 i) (hfix116_116 i) _)
      ⟨116, by decide⟩ ⟨116, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨116, by decide⟩ 21 hp) Q2.T116_116_2 Q2.hfix116_116_2 Q2.hinj116_116_2
      Q2.hcardT116_116_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_116_2 i) (Q2.hfix116_116_2 i) _)
      colCert_116_116_21.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_116_22 (hp : 22 < (Q2.transData.getD 116 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨116, by decide⟩ : Fin 148)) (colE2 ⟨116, by decide⟩ 22 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨116, by decide⟩ : Fin 148))
        (colE1 ⟨116, by decide⟩ 22 (transLenTr ⟨116, by decide⟩ 22 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨116, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨116, by decide⟩ 22 (transLenTr ⟨116, by decide⟩ 22 hp)) T116_116
      hfix116_116 hinj116_116 hcardT116_116
      (fun i => conj_mem_of_fixedPoints _ _ (T116_116 i) (hfix116_116 i) _)
      ⟨116, by decide⟩ ⟨116, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨116, by decide⟩ 22 hp) Q2.T116_116_2 Q2.hfix116_116_2 Q2.hinj116_116_2
      Q2.hcardT116_116_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_116_2 i) (Q2.hfix116_116_2 i) _)
      colCert_116_116_22.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_116_23 (hp : 23 < (Q2.transData.getD 116 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨116, by decide⟩ : Fin 148)) (colE2 ⟨116, by decide⟩ 23 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨116, by decide⟩ : Fin 148))
        (colE1 ⟨116, by decide⟩ 23 (transLenTr ⟨116, by decide⟩ 23 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨116, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨116, by decide⟩ 23 (transLenTr ⟨116, by decide⟩ 23 hp)) T116_116
      hfix116_116 hinj116_116 hcardT116_116
      (fun i => conj_mem_of_fixedPoints _ _ (T116_116 i) (hfix116_116 i) _)
      ⟨116, by decide⟩ ⟨116, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨116, by decide⟩ 23 hp) Q2.T116_116_2 Q2.hfix116_116_2 Q2.hinj116_116_2
      Q2.hcardT116_116_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_116_2 i) (Q2.hfix116_116_2 i) _)
      colCert_116_116_23.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_116_24 (hp : 24 < (Q2.transData.getD 116 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨116, by decide⟩ : Fin 148)) (colE2 ⟨116, by decide⟩ 24 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨116, by decide⟩ : Fin 148))
        (colE1 ⟨116, by decide⟩ 24 (transLenTr ⟨116, by decide⟩ 24 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨116, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨116, by decide⟩ 24 (transLenTr ⟨116, by decide⟩ 24 hp)) T116_116
      hfix116_116 hinj116_116 hcardT116_116
      (fun i => conj_mem_of_fixedPoints _ _ (T116_116 i) (hfix116_116 i) _)
      ⟨116, by decide⟩ ⟨116, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨116, by decide⟩ 24 hp) Q2.T116_116_2 Q2.hfix116_116_2 Q2.hinj116_116_2
      Q2.hcardT116_116_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_116_2 i) (Q2.hfix116_116_2 i) _)
      colCert_116_116_24.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_116_25 (hp : 25 < (Q2.transData.getD 116 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨116, by decide⟩ : Fin 148)) (colE2 ⟨116, by decide⟩ 25 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨116, by decide⟩ : Fin 148))
        (colE1 ⟨116, by decide⟩ 25 (transLenTr ⟨116, by decide⟩ 25 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨116, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨116, by decide⟩ 25 (transLenTr ⟨116, by decide⟩ 25 hp)) T116_116
      hfix116_116 hinj116_116 hcardT116_116
      (fun i => conj_mem_of_fixedPoints _ _ (T116_116 i) (hfix116_116 i) _)
      ⟨116, by decide⟩ ⟨116, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨116, by decide⟩ 25 hp) Q2.T116_116_2 Q2.hfix116_116_2 Q2.hinj116_116_2
      Q2.hcardT116_116_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_116_2 i) (Q2.hfix116_116_2 i) _)
      colCert_116_116_25.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_116_30 (hp : 30 < (Q2.transData.getD 116 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨116, by decide⟩ : Fin 148)) (colE2 ⟨116, by decide⟩ 30 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨116, by decide⟩ : Fin 148))
        (colE1 ⟨116, by decide⟩ 30 (transLenTr ⟨116, by decide⟩ 30 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨116, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨116, by decide⟩ 30 (transLenTr ⟨116, by decide⟩ 30 hp)) T116_116
      hfix116_116 hinj116_116 hcardT116_116
      (fun i => conj_mem_of_fixedPoints _ _ (T116_116 i) (hfix116_116 i) _)
      ⟨116, by decide⟩ ⟨116, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨116, by decide⟩ 30 hp) Q2.T116_116_2 Q2.hfix116_116_2 Q2.hinj116_116_2
      Q2.hcardT116_116_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_116_2 i) (Q2.hfix116_116_2 i) _)
      colCert_116_116_30.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_116_35 (hp : 35 < (Q2.transData.getD 116 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨116, by decide⟩ : Fin 148)) (colE2 ⟨116, by decide⟩ 35 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨116, by decide⟩ : Fin 148))
        (colE1 ⟨116, by decide⟩ 35 (transLenTr ⟨116, by decide⟩ 35 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨116, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨116, by decide⟩ 35 (transLenTr ⟨116, by decide⟩ 35 hp)) T116_116
      hfix116_116 hinj116_116 hcardT116_116
      (fun i => conj_mem_of_fixedPoints _ _ (T116_116 i) (hfix116_116 i) _)
      ⟨116, by decide⟩ ⟨116, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨116, by decide⟩ 35 hp) Q2.T116_116_2 Q2.hfix116_116_2 Q2.hinj116_116_2
      Q2.hcardT116_116_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_116_2 i) (Q2.hfix116_116_2 i) _)
      colCert_116_116_35.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_116_40 (hp : 40 < (Q2.transData.getD 116 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨116, by decide⟩ : Fin 148)) (colE2 ⟨116, by decide⟩ 40 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨116, by decide⟩ : Fin 148))
        (colE1 ⟨116, by decide⟩ 40 (transLenTr ⟨116, by decide⟩ 40 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨116, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨116, by decide⟩ 40 (transLenTr ⟨116, by decide⟩ 40 hp)) T116_116
      hfix116_116 hinj116_116 hcardT116_116
      (fun i => conj_mem_of_fixedPoints _ _ (T116_116 i) (hfix116_116 i) _)
      ⟨116, by decide⟩ ⟨116, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨116, by decide⟩ 40 hp) Q2.T116_116_2 Q2.hfix116_116_2 Q2.hinj116_116_2
      Q2.hcardT116_116_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_116_2 i) (Q2.hfix116_116_2 i) _)
      colCert_116_116_40.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_116_45 (hp : 45 < (Q2.transData.getD 116 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨116, by decide⟩ : Fin 148)) (colE2 ⟨116, by decide⟩ 45 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨116, by decide⟩ : Fin 148))
        (colE1 ⟨116, by decide⟩ 45 (transLenTr ⟨116, by decide⟩ 45 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨116, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨116, by decide⟩ 45 (transLenTr ⟨116, by decide⟩ 45 hp)) T116_116
      hfix116_116 hinj116_116 hcardT116_116
      (fun i => conj_mem_of_fixedPoints _ _ (T116_116 i) (hfix116_116 i) _)
      ⟨116, by decide⟩ ⟨116, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨116, by decide⟩ 45 hp) Q2.T116_116_2 Q2.hfix116_116_2 Q2.hinj116_116_2
      Q2.hcardT116_116_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_116_2 i) (Q2.hfix116_116_2 i) _)
      colCert_116_116_45.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_116_50 (hp : 50 < (Q2.transData.getD 116 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨116, by decide⟩ : Fin 148)) (colE2 ⟨116, by decide⟩ 50 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨116, by decide⟩ : Fin 148))
        (colE1 ⟨116, by decide⟩ 50 (transLenTr ⟨116, by decide⟩ 50 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨116, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨116, by decide⟩ 50 (transLenTr ⟨116, by decide⟩ 50 hp)) T116_116
      hfix116_116 hinj116_116 hcardT116_116
      (fun i => conj_mem_of_fixedPoints _ _ (T116_116 i) (hfix116_116 i) _)
      ⟨116, by decide⟩ ⟨116, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨116, by decide⟩ 50 hp) Q2.T116_116_2 Q2.hfix116_116_2 Q2.hinj116_116_2
      Q2.hcardT116_116_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_116_2 i) (Q2.hfix116_116_2 i) _)
      colCert_116_116_50.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_116_55 (hp : 55 < (Q2.transData.getD 116 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨116, by decide⟩ : Fin 148)) (colE2 ⟨116, by decide⟩ 55 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨116, by decide⟩ : Fin 148))
        (colE1 ⟨116, by decide⟩ 55 (transLenTr ⟨116, by decide⟩ 55 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨116, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨116, by decide⟩ 55 (transLenTr ⟨116, by decide⟩ 55 hp)) T116_116
      hfix116_116 hinj116_116 hcardT116_116
      (fun i => conj_mem_of_fixedPoints _ _ (T116_116 i) (hfix116_116 i) _)
      ⟨116, by decide⟩ ⟨116, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨116, by decide⟩ 55 hp) Q2.T116_116_2 Q2.hfix116_116_2 Q2.hinj116_116_2
      Q2.hcardT116_116_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_116_2 i) (Q2.hfix116_116_2 i) _)
      colCert_116_116_55.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_116_60 (hp : 60 < (Q2.transData.getD 116 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨116, by decide⟩ : Fin 148)) (colE2 ⟨116, by decide⟩ 60 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨116, by decide⟩ : Fin 148))
        (colE1 ⟨116, by decide⟩ 60 (transLenTr ⟨116, by decide⟩ 60 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨116, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨116, by decide⟩ 60 (transLenTr ⟨116, by decide⟩ 60 hp)) T116_116
      hfix116_116 hinj116_116 hcardT116_116
      (fun i => conj_mem_of_fixedPoints _ _ (T116_116 i) (hfix116_116 i) _)
      ⟨116, by decide⟩ ⟨116, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨116, by decide⟩ 60 hp) Q2.T116_116_2 Q2.hfix116_116_2 Q2.hinj116_116_2
      Q2.hcardT116_116_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_116_2 i) (Q2.hfix116_116_2 i) _)
      colCert_116_116_60.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_116_65 (hp : 65 < (Q2.transData.getD 116 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨116, by decide⟩ : Fin 148)) (colE2 ⟨116, by decide⟩ 65 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨116, by decide⟩ : Fin 148))
        (colE1 ⟨116, by decide⟩ 65 (transLenTr ⟨116, by decide⟩ 65 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨116, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨116, by decide⟩ 65 (transLenTr ⟨116, by decide⟩ 65 hp)) T116_116
      hfix116_116 hinj116_116 hcardT116_116
      (fun i => conj_mem_of_fixedPoints _ _ (T116_116 i) (hfix116_116 i) _)
      ⟨116, by decide⟩ ⟨116, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨116, by decide⟩ 65 hp) Q2.T116_116_2 Q2.hfix116_116_2 Q2.hinj116_116_2
      Q2.hcardT116_116_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_116_2 i) (Q2.hfix116_116_2 i) _)
      colCert_116_116_65.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_116_70 (hp : 70 < (Q2.transData.getD 116 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨116, by decide⟩ : Fin 148)) (colE2 ⟨116, by decide⟩ 70 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨116, by decide⟩ : Fin 148))
        (colE1 ⟨116, by decide⟩ 70 (transLenTr ⟨116, by decide⟩ 70 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨116, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨116, by decide⟩ 70 (transLenTr ⟨116, by decide⟩ 70 hp)) T116_116
      hfix116_116 hinj116_116 hcardT116_116
      (fun i => conj_mem_of_fixedPoints _ _ (T116_116 i) (hfix116_116 i) _)
      ⟨116, by decide⟩ ⟨116, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨116, by decide⟩ 70 hp) Q2.T116_116_2 Q2.hfix116_116_2 Q2.hinj116_116_2
      Q2.hcardT116_116_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_116_2 i) (Q2.hfix116_116_2 i) _)
      colCert_116_116_70.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_116_75 (hp : 75 < (Q2.transData.getD 116 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨116, by decide⟩ : Fin 148)) (colE2 ⟨116, by decide⟩ 75 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨116, by decide⟩ : Fin 148))
        (colE1 ⟨116, by decide⟩ 75 (transLenTr ⟨116, by decide⟩ 75 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨116, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨116, by decide⟩ 75 (transLenTr ⟨116, by decide⟩ 75 hp)) T116_116
      hfix116_116 hinj116_116 hcardT116_116
      (fun i => conj_mem_of_fixedPoints _ _ (T116_116 i) (hfix116_116 i) _)
      ⟨116, by decide⟩ ⟨116, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨116, by decide⟩ 75 hp) Q2.T116_116_2 Q2.hfix116_116_2 Q2.hinj116_116_2
      Q2.hcardT116_116_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_116_2 i) (Q2.hfix116_116_2 i) _)
      colCert_116_116_75.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_116_80 (hp : 80 < (Q2.transData.getD 116 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨116, by decide⟩ : Fin 148)) (colE2 ⟨116, by decide⟩ 80 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨116, by decide⟩ : Fin 148))
        (colE1 ⟨116, by decide⟩ 80 (transLenTr ⟨116, by decide⟩ 80 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨116, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨116, by decide⟩ 80 (transLenTr ⟨116, by decide⟩ 80 hp)) T116_116
      hfix116_116 hinj116_116 hcardT116_116
      (fun i => conj_mem_of_fixedPoints _ _ (T116_116 i) (hfix116_116 i) _)
      ⟨116, by decide⟩ ⟨116, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨116, by decide⟩ 80 hp) Q2.T116_116_2 Q2.hfix116_116_2 Q2.hinj116_116_2
      Q2.hcardT116_116_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_116_2 i) (Q2.hfix116_116_2 i) _)
      colCert_116_116_80.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_116_85 (hp : 85 < (Q2.transData.getD 116 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨116, by decide⟩ : Fin 148)) (colE2 ⟨116, by decide⟩ 85 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨116, by decide⟩ : Fin 148))
        (colE1 ⟨116, by decide⟩ 85 (transLenTr ⟨116, by decide⟩ 85 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨116, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨116, by decide⟩ 85 (transLenTr ⟨116, by decide⟩ 85 hp)) T116_116
      hfix116_116 hinj116_116 hcardT116_116
      (fun i => conj_mem_of_fixedPoints _ _ (T116_116 i) (hfix116_116 i) _)
      ⟨116, by decide⟩ ⟨116, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨116, by decide⟩ 85 hp) Q2.T116_116_2 Q2.hfix116_116_2 Q2.hinj116_116_2
      Q2.hcardT116_116_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_116_2 i) (Q2.hfix116_116_2 i) _)
      colCert_116_116_85.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_116_90 (hp : 90 < (Q2.transData.getD 116 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨116, by decide⟩ : Fin 148)) (colE2 ⟨116, by decide⟩ 90 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨116, by decide⟩ : Fin 148))
        (colE1 ⟨116, by decide⟩ 90 (transLenTr ⟨116, by decide⟩ 90 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨116, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨116, by decide⟩ 90 (transLenTr ⟨116, by decide⟩ 90 hp)) T116_116
      hfix116_116 hinj116_116 hcardT116_116
      (fun i => conj_mem_of_fixedPoints _ _ (T116_116 i) (hfix116_116 i) _)
      ⟨116, by decide⟩ ⟨116, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨116, by decide⟩ 90 hp) Q2.T116_116_2 Q2.hfix116_116_2 Q2.hinj116_116_2
      Q2.hcardT116_116_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_116_2 i) (Q2.hfix116_116_2 i) _)
      colCert_116_116_90.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_116_95 (hp : 95 < (Q2.transData.getD 116 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨116, by decide⟩ : Fin 148)) (colE2 ⟨116, by decide⟩ 95 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨116, by decide⟩ : Fin 148))
        (colE1 ⟨116, by decide⟩ 95 (transLenTr ⟨116, by decide⟩ 95 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨116, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨116, by decide⟩ 95 (transLenTr ⟨116, by decide⟩ 95 hp)) T116_116
      hfix116_116 hinj116_116 hcardT116_116
      (fun i => conj_mem_of_fixedPoints _ _ (T116_116 i) (hfix116_116 i) _)
      ⟨116, by decide⟩ ⟨116, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨116, by decide⟩ 95 hp) Q2.T116_116_2 Q2.hfix116_116_2 Q2.hinj116_116_2
      Q2.hcardT116_116_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_116_2 i) (Q2.hfix116_116_2 i) _)
      colCert_116_116_95.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_116_100 (hp : 100 < (Q2.transData.getD 116 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨116, by decide⟩ : Fin 148)) (colE2 ⟨116, by decide⟩ 100 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨116, by decide⟩ : Fin 148))
        (colE1 ⟨116, by decide⟩ 100 (transLenTr ⟨116, by decide⟩ 100 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨116, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨116, by decide⟩ 100 (transLenTr ⟨116, by decide⟩ 100 hp)) T116_116
      hfix116_116 hinj116_116 hcardT116_116
      (fun i => conj_mem_of_fixedPoints _ _ (T116_116 i) (hfix116_116 i) _)
      ⟨116, by decide⟩ ⟨116, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨116, by decide⟩ 100 hp) Q2.T116_116_2 Q2.hfix116_116_2 Q2.hinj116_116_2
      Q2.hcardT116_116_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_116_2 i) (Q2.hfix116_116_2 i) _)
      colCert_116_116_100.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_116_105 (hp : 105 < (Q2.transData.getD 116 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨116, by decide⟩ : Fin 148)) (colE2 ⟨116, by decide⟩ 105 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨116, by decide⟩ : Fin 148))
        (colE1 ⟨116, by decide⟩ 105 (transLenTr ⟨116, by decide⟩ 105 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨116, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨116, by decide⟩ 105 (transLenTr ⟨116, by decide⟩ 105 hp)) T116_116
      hfix116_116 hinj116_116 hcardT116_116
      (fun i => conj_mem_of_fixedPoints _ _ (T116_116 i) (hfix116_116 i) _)
      ⟨116, by decide⟩ ⟨116, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨116, by decide⟩ 105 hp) Q2.T116_116_2 Q2.hfix116_116_2 Q2.hinj116_116_2
      Q2.hcardT116_116_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_116_2 i) (Q2.hfix116_116_2 i) _)
      colCert_116_116_105.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_116_110 (hp : 110 < (Q2.transData.getD 116 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨116, by decide⟩ : Fin 148)) (colE2 ⟨116, by decide⟩ 110 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨116, by decide⟩ : Fin 148))
        (colE1 ⟨116, by decide⟩ 110 (transLenTr ⟨116, by decide⟩ 110 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨116, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨116, by decide⟩ 110 (transLenTr ⟨116, by decide⟩ 110 hp)) T116_116
      hfix116_116 hinj116_116 hcardT116_116
      (fun i => conj_mem_of_fixedPoints _ _ (T116_116 i) (hfix116_116 i) _)
      ⟨116, by decide⟩ ⟨116, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨116, by decide⟩ 110 hp) Q2.T116_116_2 Q2.hfix116_116_2 Q2.hinj116_116_2
      Q2.hcardT116_116_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_116_2 i) (Q2.hfix116_116_2 i) _)
      colCert_116_116_110.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_116_115 (hp : 115 < (Q2.transData.getD 116 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨116, by decide⟩ : Fin 148)) (colE2 ⟨116, by decide⟩ 115 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨116, by decide⟩ : Fin 148))
        (colE1 ⟨116, by decide⟩ 115 (transLenTr ⟨116, by decide⟩ 115 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨116, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨116, by decide⟩ 115 (transLenTr ⟨116, by decide⟩ 115 hp)) T116_116
      hfix116_116 hinj116_116 hcardT116_116
      (fun i => conj_mem_of_fixedPoints _ _ (T116_116 i) (hfix116_116 i) _)
      ⟨116, by decide⟩ ⟨116, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨116, by decide⟩ 115 hp) Q2.T116_116_2 Q2.hfix116_116_2 Q2.hinj116_116_2
      Q2.hcardT116_116_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_116_2 i) (Q2.hfix116_116_2 i) _)
      colCert_116_116_115.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_116_120 (hp : 120 < (Q2.transData.getD 116 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨116, by decide⟩ : Fin 148)) (colE2 ⟨116, by decide⟩ 120 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨116, by decide⟩ : Fin 148))
        (colE1 ⟨116, by decide⟩ 120 (transLenTr ⟨116, by decide⟩ 120 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨116, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨116, by decide⟩ 120 (transLenTr ⟨116, by decide⟩ 120 hp)) T116_116
      hfix116_116 hinj116_116 hcardT116_116
      (fun i => conj_mem_of_fixedPoints _ _ (T116_116 i) (hfix116_116 i) _)
      ⟨116, by decide⟩ ⟨116, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨116, by decide⟩ 120 hp) Q2.T116_116_2 Q2.hfix116_116_2 Q2.hinj116_116_2
      Q2.hcardT116_116_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_116_2 i) (Q2.hfix116_116_2 i) _)
      colCert_116_116_120.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_117_1_0 (hp : 0 < (Q2.transData.getD 1 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨1, by decide⟩ : Fin 148)) (colE2 ⟨1, by decide⟩ 0 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨1, by decide⟩ : Fin 148))
        (colE1 ⟨1, by decide⟩ 0 (transLenTr ⟨1, by decide⟩ 0 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨1, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨1, by decide⟩ 0 (transLenTr ⟨1, by decide⟩ 0 hp)) T117_1
      hfix117_1 hinj117_1 hcardT117_1
      (fun i => conj_mem_of_fixedPoints _ _ (T117_1 i) (hfix117_1 i) _)
      ⟨117, by decide⟩ ⟨1, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨1, by decide⟩ 0 hp) Q2.T117_1_2 Q2.hfix117_1_2 Q2.hinj117_1_2
      Q2.hcardT117_1_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_1_2 i) (Q2.hfix117_1_2 i) _)
      colCert_117_1_0.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_1_1 (hp : 1 < (Q2.transData.getD 1 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨1, by decide⟩ : Fin 148)) (colE2 ⟨1, by decide⟩ 1 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨1, by decide⟩ : Fin 148))
        (colE1 ⟨1, by decide⟩ 1 (transLenTr ⟨1, by decide⟩ 1 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨1, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨1, by decide⟩ 1 (transLenTr ⟨1, by decide⟩ 1 hp)) T117_1
      hfix117_1 hinj117_1 hcardT117_1
      (fun i => conj_mem_of_fixedPoints _ _ (T117_1 i) (hfix117_1 i) _)
      ⟨117, by decide⟩ ⟨1, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨1, by decide⟩ 1 hp) Q2.T117_1_2 Q2.hfix117_1_2 Q2.hinj117_1_2
      Q2.hcardT117_1_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_1_2 i) (Q2.hfix117_1_2 i) _)
      colCert_117_1_1.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_1_2 (hp : 2 < (Q2.transData.getD 1 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨1, by decide⟩ : Fin 148)) (colE2 ⟨1, by decide⟩ 2 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨1, by decide⟩ : Fin 148))
        (colE1 ⟨1, by decide⟩ 2 (transLenTr ⟨1, by decide⟩ 2 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨1, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨1, by decide⟩ 2 (transLenTr ⟨1, by decide⟩ 2 hp)) T117_1
      hfix117_1 hinj117_1 hcardT117_1
      (fun i => conj_mem_of_fixedPoints _ _ (T117_1 i) (hfix117_1 i) _)
      ⟨117, by decide⟩ ⟨1, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨1, by decide⟩ 2 hp) Q2.T117_1_2 Q2.hfix117_1_2 Q2.hinj117_1_2
      Q2.hcardT117_1_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_1_2 i) (Q2.hfix117_1_2 i) _)
      colCert_117_1_2.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_1_3 (hp : 3 < (Q2.transData.getD 1 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨1, by decide⟩ : Fin 148)) (colE2 ⟨1, by decide⟩ 3 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨1, by decide⟩ : Fin 148))
        (colE1 ⟨1, by decide⟩ 3 (transLenTr ⟨1, by decide⟩ 3 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨1, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨1, by decide⟩ 3 (transLenTr ⟨1, by decide⟩ 3 hp)) T117_1
      hfix117_1 hinj117_1 hcardT117_1
      (fun i => conj_mem_of_fixedPoints _ _ (T117_1 i) (hfix117_1 i) _)
      ⟨117, by decide⟩ ⟨1, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨1, by decide⟩ 3 hp) Q2.T117_1_2 Q2.hfix117_1_2 Q2.hinj117_1_2
      Q2.hcardT117_1_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_1_2 i) (Q2.hfix117_1_2 i) _)
      colCert_117_1_3.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_1_4 (hp : 4 < (Q2.transData.getD 1 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨1, by decide⟩ : Fin 148)) (colE2 ⟨1, by decide⟩ 4 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨1, by decide⟩ : Fin 148))
        (colE1 ⟨1, by decide⟩ 4 (transLenTr ⟨1, by decide⟩ 4 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨1, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨1, by decide⟩ 4 (transLenTr ⟨1, by decide⟩ 4 hp)) T117_1
      hfix117_1 hinj117_1 hcardT117_1
      (fun i => conj_mem_of_fixedPoints _ _ (T117_1 i) (hfix117_1 i) _)
      ⟨117, by decide⟩ ⟨1, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨1, by decide⟩ 4 hp) Q2.T117_1_2 Q2.hfix117_1_2 Q2.hinj117_1_2
      Q2.hcardT117_1_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_1_2 i) (Q2.hfix117_1_2 i) _)
      colCert_117_1_4.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_6_0 (hp : 0 < (Q2.transData.getD 6 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨6, by decide⟩ : Fin 148)) (colE2 ⟨6, by decide⟩ 0 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨6, by decide⟩ : Fin 148))
        (colE1 ⟨6, by decide⟩ 0 (transLenTr ⟨6, by decide⟩ 0 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨6, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨6, by decide⟩ 0 (transLenTr ⟨6, by decide⟩ 0 hp)) T117_6
      hfix117_6 hinj117_6 hcardT117_6
      (fun i => conj_mem_of_fixedPoints _ _ (T117_6 i) (hfix117_6 i) _)
      ⟨117, by decide⟩ ⟨6, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨6, by decide⟩ 0 hp) Q2.T117_6_2 Q2.hfix117_6_2 Q2.hinj117_6_2
      Q2.hcardT117_6_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_6_2 i) (Q2.hfix117_6_2 i) _)
      colCert_117_6_0.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_6_1 (hp : 1 < (Q2.transData.getD 6 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨6, by decide⟩ : Fin 148)) (colE2 ⟨6, by decide⟩ 1 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨6, by decide⟩ : Fin 148))
        (colE1 ⟨6, by decide⟩ 1 (transLenTr ⟨6, by decide⟩ 1 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨6, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨6, by decide⟩ 1 (transLenTr ⟨6, by decide⟩ 1 hp)) T117_6
      hfix117_6 hinj117_6 hcardT117_6
      (fun i => conj_mem_of_fixedPoints _ _ (T117_6 i) (hfix117_6 i) _)
      ⟨117, by decide⟩ ⟨6, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨6, by decide⟩ 1 hp) Q2.T117_6_2 Q2.hfix117_6_2 Q2.hinj117_6_2
      Q2.hcardT117_6_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_6_2 i) (Q2.hfix117_6_2 i) _)
      colCert_117_6_1.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_6_2 (hp : 2 < (Q2.transData.getD 6 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨6, by decide⟩ : Fin 148)) (colE2 ⟨6, by decide⟩ 2 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨6, by decide⟩ : Fin 148))
        (colE1 ⟨6, by decide⟩ 2 (transLenTr ⟨6, by decide⟩ 2 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨6, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨6, by decide⟩ 2 (transLenTr ⟨6, by decide⟩ 2 hp)) T117_6
      hfix117_6 hinj117_6 hcardT117_6
      (fun i => conj_mem_of_fixedPoints _ _ (T117_6 i) (hfix117_6 i) _)
      ⟨117, by decide⟩ ⟨6, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨6, by decide⟩ 2 hp) Q2.T117_6_2 Q2.hfix117_6_2 Q2.hinj117_6_2
      Q2.hcardT117_6_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_6_2 i) (Q2.hfix117_6_2 i) _)
      colCert_117_6_2.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_6_3 (hp : 3 < (Q2.transData.getD 6 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨6, by decide⟩ : Fin 148)) (colE2 ⟨6, by decide⟩ 3 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨6, by decide⟩ : Fin 148))
        (colE1 ⟨6, by decide⟩ 3 (transLenTr ⟨6, by decide⟩ 3 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨6, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨6, by decide⟩ 3 (transLenTr ⟨6, by decide⟩ 3 hp)) T117_6
      hfix117_6 hinj117_6 hcardT117_6
      (fun i => conj_mem_of_fixedPoints _ _ (T117_6 i) (hfix117_6 i) _)
      ⟨117, by decide⟩ ⟨6, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨6, by decide⟩ 3 hp) Q2.T117_6_2 Q2.hfix117_6_2 Q2.hinj117_6_2
      Q2.hcardT117_6_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_6_2 i) (Q2.hfix117_6_2 i) _)
      colCert_117_6_3.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_6_4 (hp : 4 < (Q2.transData.getD 6 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨6, by decide⟩ : Fin 148)) (colE2 ⟨6, by decide⟩ 4 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨6, by decide⟩ : Fin 148))
        (colE1 ⟨6, by decide⟩ 4 (transLenTr ⟨6, by decide⟩ 4 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨6, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨6, by decide⟩ 4 (transLenTr ⟨6, by decide⟩ 4 hp)) T117_6
      hfix117_6 hinj117_6 hcardT117_6
      (fun i => conj_mem_of_fixedPoints _ _ (T117_6 i) (hfix117_6 i) _)
      ⟨117, by decide⟩ ⟨6, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨6, by decide⟩ 4 hp) Q2.T117_6_2 Q2.hfix117_6_2 Q2.hinj117_6_2
      Q2.hcardT117_6_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_6_2 i) (Q2.hfix117_6_2 i) _)
      colCert_117_6_4.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_7_0 (hp : 0 < (Q2.transData.getD 7 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨7, by decide⟩ : Fin 148)) (colE2 ⟨7, by decide⟩ 0 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨7, by decide⟩ : Fin 148))
        (colE1 ⟨7, by decide⟩ 0 (transLenTr ⟨7, by decide⟩ 0 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨7, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨7, by decide⟩ 0 (transLenTr ⟨7, by decide⟩ 0 hp)) T117_7
      hfix117_7 hinj117_7 hcardT117_7
      (fun i => conj_mem_of_fixedPoints _ _ (T117_7 i) (hfix117_7 i) _)
      ⟨117, by decide⟩ ⟨7, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨7, by decide⟩ 0 hp) Q2.T117_7_2 Q2.hfix117_7_2 Q2.hinj117_7_2
      Q2.hcardT117_7_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_7_2 i) (Q2.hfix117_7_2 i) _)
      colCert_117_7_0.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_7_1 (hp : 1 < (Q2.transData.getD 7 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨7, by decide⟩ : Fin 148)) (colE2 ⟨7, by decide⟩ 1 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨7, by decide⟩ : Fin 148))
        (colE1 ⟨7, by decide⟩ 1 (transLenTr ⟨7, by decide⟩ 1 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨7, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨7, by decide⟩ 1 (transLenTr ⟨7, by decide⟩ 1 hp)) T117_7
      hfix117_7 hinj117_7 hcardT117_7
      (fun i => conj_mem_of_fixedPoints _ _ (T117_7 i) (hfix117_7 i) _)
      ⟨117, by decide⟩ ⟨7, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨7, by decide⟩ 1 hp) Q2.T117_7_2 Q2.hfix117_7_2 Q2.hinj117_7_2
      Q2.hcardT117_7_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_7_2 i) (Q2.hfix117_7_2 i) _)
      colCert_117_7_1.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_7_2 (hp : 2 < (Q2.transData.getD 7 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨7, by decide⟩ : Fin 148)) (colE2 ⟨7, by decide⟩ 2 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨7, by decide⟩ : Fin 148))
        (colE1 ⟨7, by decide⟩ 2 (transLenTr ⟨7, by decide⟩ 2 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨7, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨7, by decide⟩ 2 (transLenTr ⟨7, by decide⟩ 2 hp)) T117_7
      hfix117_7 hinj117_7 hcardT117_7
      (fun i => conj_mem_of_fixedPoints _ _ (T117_7 i) (hfix117_7 i) _)
      ⟨117, by decide⟩ ⟨7, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨7, by decide⟩ 2 hp) Q2.T117_7_2 Q2.hfix117_7_2 Q2.hinj117_7_2
      Q2.hcardT117_7_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_7_2 i) (Q2.hfix117_7_2 i) _)
      colCert_117_7_2.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_7_3 (hp : 3 < (Q2.transData.getD 7 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨7, by decide⟩ : Fin 148)) (colE2 ⟨7, by decide⟩ 3 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨7, by decide⟩ : Fin 148))
        (colE1 ⟨7, by decide⟩ 3 (transLenTr ⟨7, by decide⟩ 3 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨7, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨7, by decide⟩ 3 (transLenTr ⟨7, by decide⟩ 3 hp)) T117_7
      hfix117_7 hinj117_7 hcardT117_7
      (fun i => conj_mem_of_fixedPoints _ _ (T117_7 i) (hfix117_7 i) _)
      ⟨117, by decide⟩ ⟨7, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨7, by decide⟩ 3 hp) Q2.T117_7_2 Q2.hfix117_7_2 Q2.hinj117_7_2
      Q2.hcardT117_7_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_7_2 i) (Q2.hfix117_7_2 i) _)
      colCert_117_7_3.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_7_4 (hp : 4 < (Q2.transData.getD 7 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨7, by decide⟩ : Fin 148)) (colE2 ⟨7, by decide⟩ 4 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨7, by decide⟩ : Fin 148))
        (colE1 ⟨7, by decide⟩ 4 (transLenTr ⟨7, by decide⟩ 4 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨7, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨7, by decide⟩ 4 (transLenTr ⟨7, by decide⟩ 4 hp)) T117_7
      hfix117_7 hinj117_7 hcardT117_7
      (fun i => conj_mem_of_fixedPoints _ _ (T117_7 i) (hfix117_7 i) _)
      ⟨117, by decide⟩ ⟨7, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨7, by decide⟩ 4 hp) Q2.T117_7_2 Q2.hfix117_7_2 Q2.hinj117_7_2
      Q2.hcardT117_7_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_7_2 i) (Q2.hfix117_7_2 i) _)
      colCert_117_7_4.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_8_0 (hp : 0 < (Q2.transData.getD 8 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨8, by decide⟩ : Fin 148)) (colE2 ⟨8, by decide⟩ 0 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨8, by decide⟩ : Fin 148))
        (colE1 ⟨8, by decide⟩ 0 (transLenTr ⟨8, by decide⟩ 0 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨8, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨8, by decide⟩ 0 (transLenTr ⟨8, by decide⟩ 0 hp)) T117_8
      hfix117_8 hinj117_8 hcardT117_8
      (fun i => conj_mem_of_fixedPoints _ _ (T117_8 i) (hfix117_8 i) _)
      ⟨117, by decide⟩ ⟨8, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨8, by decide⟩ 0 hp) Q2.T117_8_2 Q2.hfix117_8_2 Q2.hinj117_8_2
      Q2.hcardT117_8_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_8_2 i) (Q2.hfix117_8_2 i) _)
      colCert_117_8_0.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_8_1 (hp : 1 < (Q2.transData.getD 8 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨8, by decide⟩ : Fin 148)) (colE2 ⟨8, by decide⟩ 1 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨8, by decide⟩ : Fin 148))
        (colE1 ⟨8, by decide⟩ 1 (transLenTr ⟨8, by decide⟩ 1 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨8, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨8, by decide⟩ 1 (transLenTr ⟨8, by decide⟩ 1 hp)) T117_8
      hfix117_8 hinj117_8 hcardT117_8
      (fun i => conj_mem_of_fixedPoints _ _ (T117_8 i) (hfix117_8 i) _)
      ⟨117, by decide⟩ ⟨8, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨8, by decide⟩ 1 hp) Q2.T117_8_2 Q2.hfix117_8_2 Q2.hinj117_8_2
      Q2.hcardT117_8_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_8_2 i) (Q2.hfix117_8_2 i) _)
      colCert_117_8_1.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_8_2 (hp : 2 < (Q2.transData.getD 8 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨8, by decide⟩ : Fin 148)) (colE2 ⟨8, by decide⟩ 2 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨8, by decide⟩ : Fin 148))
        (colE1 ⟨8, by decide⟩ 2 (transLenTr ⟨8, by decide⟩ 2 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨8, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨8, by decide⟩ 2 (transLenTr ⟨8, by decide⟩ 2 hp)) T117_8
      hfix117_8 hinj117_8 hcardT117_8
      (fun i => conj_mem_of_fixedPoints _ _ (T117_8 i) (hfix117_8 i) _)
      ⟨117, by decide⟩ ⟨8, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨8, by decide⟩ 2 hp) Q2.T117_8_2 Q2.hfix117_8_2 Q2.hinj117_8_2
      Q2.hcardT117_8_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_8_2 i) (Q2.hfix117_8_2 i) _)
      colCert_117_8_2.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_8_3 (hp : 3 < (Q2.transData.getD 8 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨8, by decide⟩ : Fin 148)) (colE2 ⟨8, by decide⟩ 3 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨8, by decide⟩ : Fin 148))
        (colE1 ⟨8, by decide⟩ 3 (transLenTr ⟨8, by decide⟩ 3 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨8, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨8, by decide⟩ 3 (transLenTr ⟨8, by decide⟩ 3 hp)) T117_8
      hfix117_8 hinj117_8 hcardT117_8
      (fun i => conj_mem_of_fixedPoints _ _ (T117_8 i) (hfix117_8 i) _)
      ⟨117, by decide⟩ ⟨8, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨8, by decide⟩ 3 hp) Q2.T117_8_2 Q2.hfix117_8_2 Q2.hinj117_8_2
      Q2.hcardT117_8_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_8_2 i) (Q2.hfix117_8_2 i) _)
      colCert_117_8_3.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_8_4 (hp : 4 < (Q2.transData.getD 8 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨8, by decide⟩ : Fin 148)) (colE2 ⟨8, by decide⟩ 4 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨8, by decide⟩ : Fin 148))
        (colE1 ⟨8, by decide⟩ 4 (transLenTr ⟨8, by decide⟩ 4 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨8, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨8, by decide⟩ 4 (transLenTr ⟨8, by decide⟩ 4 hp)) T117_8
      hfix117_8 hinj117_8 hcardT117_8
      (fun i => conj_mem_of_fixedPoints _ _ (T117_8 i) (hfix117_8 i) _)
      ⟨117, by decide⟩ ⟨8, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨8, by decide⟩ 4 hp) Q2.T117_8_2 Q2.hfix117_8_2 Q2.hinj117_8_2
      Q2.hcardT117_8_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_8_2 i) (Q2.hfix117_8_2 i) _)
      colCert_117_8_4.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_9_0 (hp : 0 < (Q2.transData.getD 9 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨9, by decide⟩ : Fin 148)) (colE2 ⟨9, by decide⟩ 0 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨9, by decide⟩ : Fin 148))
        (colE1 ⟨9, by decide⟩ 0 (transLenTr ⟨9, by decide⟩ 0 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨9, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨9, by decide⟩ 0 (transLenTr ⟨9, by decide⟩ 0 hp)) T117_9
      hfix117_9 hinj117_9 hcardT117_9
      (fun i => conj_mem_of_fixedPoints _ _ (T117_9 i) (hfix117_9 i) _)
      ⟨117, by decide⟩ ⟨9, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨9, by decide⟩ 0 hp) Q2.T117_9_2 Q2.hfix117_9_2 Q2.hinj117_9_2
      Q2.hcardT117_9_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_9_2 i) (Q2.hfix117_9_2 i) _)
      colCert_117_9_0.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_9_1 (hp : 1 < (Q2.transData.getD 9 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨9, by decide⟩ : Fin 148)) (colE2 ⟨9, by decide⟩ 1 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨9, by decide⟩ : Fin 148))
        (colE1 ⟨9, by decide⟩ 1 (transLenTr ⟨9, by decide⟩ 1 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨9, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨9, by decide⟩ 1 (transLenTr ⟨9, by decide⟩ 1 hp)) T117_9
      hfix117_9 hinj117_9 hcardT117_9
      (fun i => conj_mem_of_fixedPoints _ _ (T117_9 i) (hfix117_9 i) _)
      ⟨117, by decide⟩ ⟨9, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨9, by decide⟩ 1 hp) Q2.T117_9_2 Q2.hfix117_9_2 Q2.hinj117_9_2
      Q2.hcardT117_9_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_9_2 i) (Q2.hfix117_9_2 i) _)
      colCert_117_9_1.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_9_2 (hp : 2 < (Q2.transData.getD 9 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨9, by decide⟩ : Fin 148)) (colE2 ⟨9, by decide⟩ 2 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨9, by decide⟩ : Fin 148))
        (colE1 ⟨9, by decide⟩ 2 (transLenTr ⟨9, by decide⟩ 2 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨9, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨9, by decide⟩ 2 (transLenTr ⟨9, by decide⟩ 2 hp)) T117_9
      hfix117_9 hinj117_9 hcardT117_9
      (fun i => conj_mem_of_fixedPoints _ _ (T117_9 i) (hfix117_9 i) _)
      ⟨117, by decide⟩ ⟨9, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨9, by decide⟩ 2 hp) Q2.T117_9_2 Q2.hfix117_9_2 Q2.hinj117_9_2
      Q2.hcardT117_9_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_9_2 i) (Q2.hfix117_9_2 i) _)
      colCert_117_9_2.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_9_3 (hp : 3 < (Q2.transData.getD 9 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨9, by decide⟩ : Fin 148)) (colE2 ⟨9, by decide⟩ 3 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨9, by decide⟩ : Fin 148))
        (colE1 ⟨9, by decide⟩ 3 (transLenTr ⟨9, by decide⟩ 3 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨9, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨9, by decide⟩ 3 (transLenTr ⟨9, by decide⟩ 3 hp)) T117_9
      hfix117_9 hinj117_9 hcardT117_9
      (fun i => conj_mem_of_fixedPoints _ _ (T117_9 i) (hfix117_9 i) _)
      ⟨117, by decide⟩ ⟨9, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨9, by decide⟩ 3 hp) Q2.T117_9_2 Q2.hfix117_9_2 Q2.hinj117_9_2
      Q2.hcardT117_9_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_9_2 i) (Q2.hfix117_9_2 i) _)
      colCert_117_9_3.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_9_4 (hp : 4 < (Q2.transData.getD 9 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨9, by decide⟩ : Fin 148)) (colE2 ⟨9, by decide⟩ 4 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨9, by decide⟩ : Fin 148))
        (colE1 ⟨9, by decide⟩ 4 (transLenTr ⟨9, by decide⟩ 4 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨9, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨9, by decide⟩ 4 (transLenTr ⟨9, by decide⟩ 4 hp)) T117_9
      hfix117_9 hinj117_9 hcardT117_9
      (fun i => conj_mem_of_fixedPoints _ _ (T117_9 i) (hfix117_9 i) _)
      ⟨117, by decide⟩ ⟨9, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨9, by decide⟩ 4 hp) Q2.T117_9_2 Q2.hfix117_9_2 Q2.hinj117_9_2
      Q2.hcardT117_9_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_9_2 i) (Q2.hfix117_9_2 i) _)
      colCert_117_9_4.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_10_0 (hp : 0 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 0 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 0 (transLenTr ⟨10, by decide⟩ 0 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 0 (transLenTr ⟨10, by decide⟩ 0 hp)) T117_10
      hfix117_10 hinj117_10 hcardT117_10
      (fun i => conj_mem_of_fixedPoints _ _ (T117_10 i) (hfix117_10 i) _)
      ⟨117, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 0 hp) Q2.T117_10_2 Q2.hfix117_10_2 Q2.hinj117_10_2
      Q2.hcardT117_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_10_2 i) (Q2.hfix117_10_2 i) _)
      colCert_117_10_0.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_10_1 (hp : 1 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 1 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 1 (transLenTr ⟨10, by decide⟩ 1 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 1 (transLenTr ⟨10, by decide⟩ 1 hp)) T117_10
      hfix117_10 hinj117_10 hcardT117_10
      (fun i => conj_mem_of_fixedPoints _ _ (T117_10 i) (hfix117_10 i) _)
      ⟨117, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 1 hp) Q2.T117_10_2 Q2.hfix117_10_2 Q2.hinj117_10_2
      Q2.hcardT117_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_10_2 i) (Q2.hfix117_10_2 i) _)
      colCert_117_10_1.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_10_2 (hp : 2 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 2 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 2 (transLenTr ⟨10, by decide⟩ 2 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 2 (transLenTr ⟨10, by decide⟩ 2 hp)) T117_10
      hfix117_10 hinj117_10 hcardT117_10
      (fun i => conj_mem_of_fixedPoints _ _ (T117_10 i) (hfix117_10 i) _)
      ⟨117, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 2 hp) Q2.T117_10_2 Q2.hfix117_10_2 Q2.hinj117_10_2
      Q2.hcardT117_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_10_2 i) (Q2.hfix117_10_2 i) _)
      colCert_117_10_2.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_10_3 (hp : 3 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 3 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 3 (transLenTr ⟨10, by decide⟩ 3 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 3 (transLenTr ⟨10, by decide⟩ 3 hp)) T117_10
      hfix117_10 hinj117_10 hcardT117_10
      (fun i => conj_mem_of_fixedPoints _ _ (T117_10 i) (hfix117_10 i) _)
      ⟨117, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 3 hp) Q2.T117_10_2 Q2.hfix117_10_2 Q2.hinj117_10_2
      Q2.hcardT117_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_10_2 i) (Q2.hfix117_10_2 i) _)
      colCert_117_10_3.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_10_4 (hp : 4 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 4 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 4 (transLenTr ⟨10, by decide⟩ 4 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 4 (transLenTr ⟨10, by decide⟩ 4 hp)) T117_10
      hfix117_10 hinj117_10 hcardT117_10
      (fun i => conj_mem_of_fixedPoints _ _ (T117_10 i) (hfix117_10 i) _)
      ⟨117, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 4 hp) Q2.T117_10_2 Q2.hfix117_10_2 Q2.hinj117_10_2
      Q2.hcardT117_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_10_2 i) (Q2.hfix117_10_2 i) _)
      colCert_117_10_4.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_12_0 (hp : 0 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 0 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp)) T117_12
      hfix117_12 hinj117_12 hcardT117_12
      (fun i => conj_mem_of_fixedPoints _ _ (T117_12 i) (hfix117_12 i) _)
      ⟨117, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 0 hp) Q2.T117_12_2 Q2.hfix117_12_2 Q2.hinj117_12_2
      Q2.hcardT117_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_12_2 i) (Q2.hfix117_12_2 i) _)
      colCert_117_12_0.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_12_1 (hp : 1 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 1 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp)) T117_12
      hfix117_12 hinj117_12 hcardT117_12
      (fun i => conj_mem_of_fixedPoints _ _ (T117_12 i) (hfix117_12 i) _)
      ⟨117, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 1 hp) Q2.T117_12_2 Q2.hfix117_12_2 Q2.hinj117_12_2
      Q2.hcardT117_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_12_2 i) (Q2.hfix117_12_2 i) _)
      colCert_117_12_1.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_12_2 (hp : 2 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 2 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp)) T117_12
      hfix117_12 hinj117_12 hcardT117_12
      (fun i => conj_mem_of_fixedPoints _ _ (T117_12 i) (hfix117_12 i) _)
      ⟨117, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 2 hp) Q2.T117_12_2 Q2.hfix117_12_2 Q2.hinj117_12_2
      Q2.hcardT117_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_12_2 i) (Q2.hfix117_12_2 i) _)
      colCert_117_12_2.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_12_3 (hp : 3 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 3 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp)) T117_12
      hfix117_12 hinj117_12 hcardT117_12
      (fun i => conj_mem_of_fixedPoints _ _ (T117_12 i) (hfix117_12 i) _)
      ⟨117, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 3 hp) Q2.T117_12_2 Q2.hfix117_12_2 Q2.hinj117_12_2
      Q2.hcardT117_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_12_2 i) (Q2.hfix117_12_2 i) _)
      colCert_117_12_3.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_12_4 (hp : 4 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 4 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp)) T117_12
      hfix117_12 hinj117_12 hcardT117_12
      (fun i => conj_mem_of_fixedPoints _ _ (T117_12 i) (hfix117_12 i) _)
      ⟨117, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 4 hp) Q2.T117_12_2 Q2.hfix117_12_2 Q2.hinj117_12_2
      Q2.hcardT117_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_12_2 i) (Q2.hfix117_12_2 i) _)
      colCert_117_12_4.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_13_0 (hp : 0 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 0 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 0 (transLenTr ⟨13, by decide⟩ 0 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 0 (transLenTr ⟨13, by decide⟩ 0 hp)) T117_13
      hfix117_13 hinj117_13 hcardT117_13
      (fun i => conj_mem_of_fixedPoints _ _ (T117_13 i) (hfix117_13 i) _)
      ⟨117, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 0 hp) Q2.T117_13_2 Q2.hfix117_13_2 Q2.hinj117_13_2
      Q2.hcardT117_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_13_2 i) (Q2.hfix117_13_2 i) _)
      colCert_117_13_0.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_13_1 (hp : 1 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 1 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 1 (transLenTr ⟨13, by decide⟩ 1 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 1 (transLenTr ⟨13, by decide⟩ 1 hp)) T117_13
      hfix117_13 hinj117_13 hcardT117_13
      (fun i => conj_mem_of_fixedPoints _ _ (T117_13 i) (hfix117_13 i) _)
      ⟨117, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 1 hp) Q2.T117_13_2 Q2.hfix117_13_2 Q2.hinj117_13_2
      Q2.hcardT117_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_13_2 i) (Q2.hfix117_13_2 i) _)
      colCert_117_13_1.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_13_2 (hp : 2 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 2 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 2 (transLenTr ⟨13, by decide⟩ 2 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 2 (transLenTr ⟨13, by decide⟩ 2 hp)) T117_13
      hfix117_13 hinj117_13 hcardT117_13
      (fun i => conj_mem_of_fixedPoints _ _ (T117_13 i) (hfix117_13 i) _)
      ⟨117, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 2 hp) Q2.T117_13_2 Q2.hfix117_13_2 Q2.hinj117_13_2
      Q2.hcardT117_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_13_2 i) (Q2.hfix117_13_2 i) _)
      colCert_117_13_2.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_13_3 (hp : 3 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 3 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 3 (transLenTr ⟨13, by decide⟩ 3 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 3 (transLenTr ⟨13, by decide⟩ 3 hp)) T117_13
      hfix117_13 hinj117_13 hcardT117_13
      (fun i => conj_mem_of_fixedPoints _ _ (T117_13 i) (hfix117_13 i) _)
      ⟨117, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 3 hp) Q2.T117_13_2 Q2.hfix117_13_2 Q2.hinj117_13_2
      Q2.hcardT117_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_13_2 i) (Q2.hfix117_13_2 i) _)
      colCert_117_13_3.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_13_4 (hp : 4 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 4 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 4 (transLenTr ⟨13, by decide⟩ 4 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 4 (transLenTr ⟨13, by decide⟩ 4 hp)) T117_13
      hfix117_13 hinj117_13 hcardT117_13
      (fun i => conj_mem_of_fixedPoints _ _ (T117_13 i) (hfix117_13 i) _)
      ⟨117, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 4 hp) Q2.T117_13_2 Q2.hfix117_13_2 Q2.hinj117_13_2
      Q2.hcardT117_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_13_2 i) (Q2.hfix117_13_2 i) _)
      colCert_117_13_4.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_13_5 (hp : 5 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 5 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 5 (transLenTr ⟨13, by decide⟩ 5 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨117, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 5 (transLenTr ⟨13, by decide⟩ 5 hp)) T117_13
      hfix117_13 hinj117_13 hcardT117_13
      (fun i => conj_mem_of_fixedPoints _ _ (T117_13 i) (hfix117_13 i) _)
      ⟨117, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 5 hp) Q2.T117_13_2 Q2.hfix117_13_2 Q2.hinj117_13_2
      Q2.hcardT117_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_13_2 i) (Q2.hfix117_13_2 i) _)
      ?_).symm
  rw [show colData1 (⟨117, by decide⟩ : Fin 148)
        ((colE1 ⟨13, by decide⟩ 5 (transLenTr ⟨13, by decide⟩ 5 hp) : ↥(reps ⟨13, by decide⟩)) : Coordinate 1)
        T117_13 = colFn colCertDiv_117_13_5.D1 (m := 5) from colCertDiv_117_13_5.bind1,
    show colData2 (⟨117, by decide⟩ : Fin 148)
        ((colE2 ⟨13, by decide⟩ 5 hp : ↥(Q2.reps ⟨13, by decide⟩)) : Coordinate 2)
        Q2.T117_13_2 = colFn colCertDiv_117_13_5.D2 (m := 5) from colCertDiv_117_13_5.bind2]
  rw [alnId_117 j hj]
  exact fastcode_of_tau ⟨117, by decide⟩ _ _ _
    ((alnId_117 j hj) ▸ Q2.listedAt (⟨117, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨117, by decide⟩ : Fin 148) hj hq).1) colCertDiv_117_13_5_tau_match


theorem leaf_117_13_6 (hp : 6 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 6 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 6 (transLenTr ⟨13, by decide⟩ 6 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨117, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 6 (transLenTr ⟨13, by decide⟩ 6 hp)) T117_13
      hfix117_13 hinj117_13 hcardT117_13
      (fun i => conj_mem_of_fixedPoints _ _ (T117_13 i) (hfix117_13 i) _)
      ⟨117, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 6 hp) Q2.T117_13_2 Q2.hfix117_13_2 Q2.hinj117_13_2
      Q2.hcardT117_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_13_2 i) (Q2.hfix117_13_2 i) _)
      ?_).symm
  rw [show colData1 (⟨117, by decide⟩ : Fin 148)
        ((colE1 ⟨13, by decide⟩ 6 (transLenTr ⟨13, by decide⟩ 6 hp) : ↥(reps ⟨13, by decide⟩)) : Coordinate 1)
        T117_13 = colFn colCertDiv_117_13_6.D1 (m := 5) from colCertDiv_117_13_6.bind1,
    show colData2 (⟨117, by decide⟩ : Fin 148)
        ((colE2 ⟨13, by decide⟩ 6 hp : ↥(Q2.reps ⟨13, by decide⟩)) : Coordinate 2)
        Q2.T117_13_2 = colFn colCertDiv_117_13_6.D2 (m := 5) from colCertDiv_117_13_6.bind2]
  rw [alnId_117 j hj]
  exact fastcode_of_tau ⟨117, by decide⟩ _ _ _
    ((alnId_117 j hj) ▸ Q2.listedAt (⟨117, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨117, by decide⟩ : Fin 148) hj hq).1) colCertDiv_117_13_6_tau_match


theorem leaf_117_13_7 (hp : 7 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 7 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 7 (transLenTr ⟨13, by decide⟩ 7 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨117, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 7 (transLenTr ⟨13, by decide⟩ 7 hp)) T117_13
      hfix117_13 hinj117_13 hcardT117_13
      (fun i => conj_mem_of_fixedPoints _ _ (T117_13 i) (hfix117_13 i) _)
      ⟨117, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 7 hp) Q2.T117_13_2 Q2.hfix117_13_2 Q2.hinj117_13_2
      Q2.hcardT117_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_13_2 i) (Q2.hfix117_13_2 i) _)
      ?_).symm
  rw [show colData1 (⟨117, by decide⟩ : Fin 148)
        ((colE1 ⟨13, by decide⟩ 7 (transLenTr ⟨13, by decide⟩ 7 hp) : ↥(reps ⟨13, by decide⟩)) : Coordinate 1)
        T117_13 = colFn colCertDiv_117_13_7.D1 (m := 5) from colCertDiv_117_13_7.bind1,
    show colData2 (⟨117, by decide⟩ : Fin 148)
        ((colE2 ⟨13, by decide⟩ 7 hp : ↥(Q2.reps ⟨13, by decide⟩)) : Coordinate 2)
        Q2.T117_13_2 = colFn colCertDiv_117_13_7.D2 (m := 5) from colCertDiv_117_13_7.bind2]
  rw [alnId_117 j hj]
  exact fastcode_of_tau ⟨117, by decide⟩ _ _ _
    ((alnId_117 j hj) ▸ Q2.listedAt (⟨117, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨117, by decide⟩ : Fin 148) hj hq).1) colCertDiv_117_13_7_tau_match


theorem leaf_117_13_8 (hp : 8 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 8 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 8 (transLenTr ⟨13, by decide⟩ 8 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨117, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 8 (transLenTr ⟨13, by decide⟩ 8 hp)) T117_13
      hfix117_13 hinj117_13 hcardT117_13
      (fun i => conj_mem_of_fixedPoints _ _ (T117_13 i) (hfix117_13 i) _)
      ⟨117, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 8 hp) Q2.T117_13_2 Q2.hfix117_13_2 Q2.hinj117_13_2
      Q2.hcardT117_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_13_2 i) (Q2.hfix117_13_2 i) _)
      ?_).symm
  rw [show colData1 (⟨117, by decide⟩ : Fin 148)
        ((colE1 ⟨13, by decide⟩ 8 (transLenTr ⟨13, by decide⟩ 8 hp) : ↥(reps ⟨13, by decide⟩)) : Coordinate 1)
        T117_13 = colFn colCertDiv_117_13_8.D1 (m := 5) from colCertDiv_117_13_8.bind1,
    show colData2 (⟨117, by decide⟩ : Fin 148)
        ((colE2 ⟨13, by decide⟩ 8 hp : ↥(Q2.reps ⟨13, by decide⟩)) : Coordinate 2)
        Q2.T117_13_2 = colFn colCertDiv_117_13_8.D2 (m := 5) from colCertDiv_117_13_8.bind2]
  rw [alnId_117 j hj]
  exact fastcode_of_tau ⟨117, by decide⟩ _ _ _
    ((alnId_117 j hj) ▸ Q2.listedAt (⟨117, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨117, by decide⟩ : Fin 148) hj hq).1) colCertDiv_117_13_8_tau_match


theorem leaf_117_13_9 (hp : 9 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 9 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 9 (transLenTr ⟨13, by decide⟩ 9 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 9 (transLenTr ⟨13, by decide⟩ 9 hp)) T117_13
      hfix117_13 hinj117_13 hcardT117_13
      (fun i => conj_mem_of_fixedPoints _ _ (T117_13 i) (hfix117_13 i) _)
      ⟨117, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 9 hp) Q2.T117_13_2 Q2.hfix117_13_2 Q2.hinj117_13_2
      Q2.hcardT117_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_13_2 i) (Q2.hfix117_13_2 i) _)
      colCert_117_13_9.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_13_10 (hp : 10 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 10 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 10 (transLenTr ⟨13, by decide⟩ 10 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 10 (transLenTr ⟨13, by decide⟩ 10 hp)) T117_13
      hfix117_13 hinj117_13 hcardT117_13
      (fun i => conj_mem_of_fixedPoints _ _ (T117_13 i) (hfix117_13 i) _)
      ⟨117, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 10 hp) Q2.T117_13_2 Q2.hfix117_13_2 Q2.hinj117_13_2
      Q2.hcardT117_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_13_2 i) (Q2.hfix117_13_2 i) _)
      colCert_117_13_10.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_13_11 (hp : 11 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 11 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 11 (transLenTr ⟨13, by decide⟩ 11 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 11 (transLenTr ⟨13, by decide⟩ 11 hp)) T117_13
      hfix117_13 hinj117_13 hcardT117_13
      (fun i => conj_mem_of_fixedPoints _ _ (T117_13 i) (hfix117_13 i) _)
      ⟨117, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 11 hp) Q2.T117_13_2 Q2.hfix117_13_2 Q2.hinj117_13_2
      Q2.hcardT117_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_13_2 i) (Q2.hfix117_13_2 i) _)
      colCert_117_13_11.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_13_12 (hp : 12 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 12 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 12 (transLenTr ⟨13, by decide⟩ 12 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 12 (transLenTr ⟨13, by decide⟩ 12 hp)) T117_13
      hfix117_13 hinj117_13 hcardT117_13
      (fun i => conj_mem_of_fixedPoints _ _ (T117_13 i) (hfix117_13 i) _)
      ⟨117, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 12 hp) Q2.T117_13_2 Q2.hfix117_13_2 Q2.hinj117_13_2
      Q2.hcardT117_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_13_2 i) (Q2.hfix117_13_2 i) _)
      colCert_117_13_12.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_13_13 (hp : 13 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 13 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 13 (transLenTr ⟨13, by decide⟩ 13 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 13 (transLenTr ⟨13, by decide⟩ 13 hp)) T117_13
      hfix117_13 hinj117_13 hcardT117_13
      (fun i => conj_mem_of_fixedPoints _ _ (T117_13 i) (hfix117_13 i) _)
      ⟨117, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 13 hp) Q2.T117_13_2 Q2.hfix117_13_2 Q2.hinj117_13_2
      Q2.hcardT117_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_13_2 i) (Q2.hfix117_13_2 i) _)
      colCert_117_13_13.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_13_14 (hp : 14 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 14 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 14 (transLenTr ⟨13, by decide⟩ 14 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 14 (transLenTr ⟨13, by decide⟩ 14 hp)) T117_13
      hfix117_13 hinj117_13 hcardT117_13
      (fun i => conj_mem_of_fixedPoints _ _ (T117_13 i) (hfix117_13 i) _)
      ⟨117, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 14 hp) Q2.T117_13_2 Q2.hfix117_13_2 Q2.hinj117_13_2
      Q2.hcardT117_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_13_2 i) (Q2.hfix117_13_2 i) _)
      colCert_117_13_14.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_13_15 (hp : 15 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 15 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 15 (transLenTr ⟨13, by decide⟩ 15 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 15 (transLenTr ⟨13, by decide⟩ 15 hp)) T117_13
      hfix117_13 hinj117_13 hcardT117_13
      (fun i => conj_mem_of_fixedPoints _ _ (T117_13 i) (hfix117_13 i) _)
      ⟨117, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 15 hp) Q2.T117_13_2 Q2.hfix117_13_2 Q2.hinj117_13_2
      Q2.hcardT117_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_13_2 i) (Q2.hfix117_13_2 i) _)
      colCert_117_13_15.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_13_16 (hp : 16 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 16 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 16 (transLenTr ⟨13, by decide⟩ 16 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 16 (transLenTr ⟨13, by decide⟩ 16 hp)) T117_13
      hfix117_13 hinj117_13 hcardT117_13
      (fun i => conj_mem_of_fixedPoints _ _ (T117_13 i) (hfix117_13 i) _)
      ⟨117, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 16 hp) Q2.T117_13_2 Q2.hfix117_13_2 Q2.hinj117_13_2
      Q2.hcardT117_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_13_2 i) (Q2.hfix117_13_2 i) _)
      colCert_117_13_16.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_13_17 (hp : 17 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 17 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 17 (transLenTr ⟨13, by decide⟩ 17 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 17 (transLenTr ⟨13, by decide⟩ 17 hp)) T117_13
      hfix117_13 hinj117_13 hcardT117_13
      (fun i => conj_mem_of_fixedPoints _ _ (T117_13 i) (hfix117_13 i) _)
      ⟨117, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 17 hp) Q2.T117_13_2 Q2.hfix117_13_2 Q2.hinj117_13_2
      Q2.hcardT117_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_13_2 i) (Q2.hfix117_13_2 i) _)
      colCert_117_13_17.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_13_18 (hp : 18 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 18 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 18 (transLenTr ⟨13, by decide⟩ 18 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 18 (transLenTr ⟨13, by decide⟩ 18 hp)) T117_13
      hfix117_13 hinj117_13 hcardT117_13
      (fun i => conj_mem_of_fixedPoints _ _ (T117_13 i) (hfix117_13 i) _)
      ⟨117, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 18 hp) Q2.T117_13_2 Q2.hfix117_13_2 Q2.hinj117_13_2
      Q2.hcardT117_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_13_2 i) (Q2.hfix117_13_2 i) _)
      colCert_117_13_18.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_13_19 (hp : 19 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 19 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 19 (transLenTr ⟨13, by decide⟩ 19 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 19 (transLenTr ⟨13, by decide⟩ 19 hp)) T117_13
      hfix117_13 hinj117_13 hcardT117_13
      (fun i => conj_mem_of_fixedPoints _ _ (T117_13 i) (hfix117_13 i) _)
      ⟨117, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 19 hp) Q2.T117_13_2 Q2.hfix117_13_2 Q2.hinj117_13_2
      Q2.hcardT117_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_13_2 i) (Q2.hfix117_13_2 i) _)
      colCert_117_13_19.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_13_20 (hp : 20 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 20 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 20 (transLenTr ⟨13, by decide⟩ 20 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 20 (transLenTr ⟨13, by decide⟩ 20 hp)) T117_13
      hfix117_13 hinj117_13 hcardT117_13
      (fun i => conj_mem_of_fixedPoints _ _ (T117_13 i) (hfix117_13 i) _)
      ⟨117, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 20 hp) Q2.T117_13_2 Q2.hfix117_13_2 Q2.hinj117_13_2
      Q2.hcardT117_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_13_2 i) (Q2.hfix117_13_2 i) _)
      colCert_117_13_20.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_13_21 (hp : 21 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 21 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 21 (transLenTr ⟨13, by decide⟩ 21 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 21 (transLenTr ⟨13, by decide⟩ 21 hp)) T117_13
      hfix117_13 hinj117_13 hcardT117_13
      (fun i => conj_mem_of_fixedPoints _ _ (T117_13 i) (hfix117_13 i) _)
      ⟨117, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 21 hp) Q2.T117_13_2 Q2.hfix117_13_2 Q2.hinj117_13_2
      Q2.hcardT117_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_13_2 i) (Q2.hfix117_13_2 i) _)
      colCert_117_13_21.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_13_22 (hp : 22 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 22 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 22 (transLenTr ⟨13, by decide⟩ 22 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 22 (transLenTr ⟨13, by decide⟩ 22 hp)) T117_13
      hfix117_13 hinj117_13 hcardT117_13
      (fun i => conj_mem_of_fixedPoints _ _ (T117_13 i) (hfix117_13 i) _)
      ⟨117, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 22 hp) Q2.T117_13_2 Q2.hfix117_13_2 Q2.hinj117_13_2
      Q2.hcardT117_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_13_2 i) (Q2.hfix117_13_2 i) _)
      colCert_117_13_22.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_13_23 (hp : 23 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 23 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 23 (transLenTr ⟨13, by decide⟩ 23 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 23 (transLenTr ⟨13, by decide⟩ 23 hp)) T117_13
      hfix117_13 hinj117_13 hcardT117_13
      (fun i => conj_mem_of_fixedPoints _ _ (T117_13 i) (hfix117_13 i) _)
      ⟨117, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 23 hp) Q2.T117_13_2 Q2.hfix117_13_2 Q2.hinj117_13_2
      Q2.hcardT117_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_13_2 i) (Q2.hfix117_13_2 i) _)
      colCert_117_13_23.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_13_24 (hp : 24 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 24 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 24 (transLenTr ⟨13, by decide⟩ 24 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 24 (transLenTr ⟨13, by decide⟩ 24 hp)) T117_13
      hfix117_13 hinj117_13 hcardT117_13
      (fun i => conj_mem_of_fixedPoints _ _ (T117_13 i) (hfix117_13 i) _)
      ⟨117, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 24 hp) Q2.T117_13_2 Q2.hfix117_13_2 Q2.hinj117_13_2
      Q2.hcardT117_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_13_2 i) (Q2.hfix117_13_2 i) _)
      colCert_117_13_24.hD ?_).symm
  rw [alnId_117 j hj]


end LeanDring.P5Presentation
