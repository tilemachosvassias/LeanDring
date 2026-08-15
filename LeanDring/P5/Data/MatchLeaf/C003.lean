/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Data.ColRestCheap.C005
import LeanDring.P5.Data.ColRestCheap.C006
import LeanDring.P5.Data.ColRestCheap.C007
import LeanDring.P5.Data.ColRestHeavy.C011
import LeanDring.P5.Data.ColRestHeavy.C012
import LeanDring.P5.Data.ColRestHeavy.C013
import LeanDring.P5.Data.ColRestHeavy.C014
import LeanDring.P5.Data.ColRestHeavy.C015
import LeanDring.P5.Data.ColRestHeavy.C016
import LeanDring.P5.Data.ColRestHeavy.C017
import LeanDring.P5.Data.ColRestHeavy.C018
import LeanDring.P5.Data.ColRestHeavy.C019
import LeanDring.P5.Data.ColRestHeavy.C020
import LeanDring.P5.Data.ColRestHeavy.C021
import LeanDring.P5.Data.ColRestHeavy.C022
import LeanDring.P5.Data.ColRestHeavy.C023
import LeanDring.P5.Data.ColRestHeavy.C024
import LeanDring.P5.Data.ColRestHeavy.C025
import LeanDring.P5.Data.ColRestHeavy.C026
import LeanDring.P5.Data.ColRestHeavy.C027
import LeanDring.P5.Data.ColRestHeavy.C008
import LeanDring.P5.Data.ColRestHeavy.C009
import LeanDring.P5.Data.ColRestHeavy.C010
import LeanDring.P5.Data.EntryA.C012
import LeanDring.P5.Data.EntryA.C013
import LeanDring.P5.Data.EntryA.C014
import LeanDring.P5.Data.EntryA.C015
import LeanDring.P5.Data.EntryA.C016
import LeanDring.P5.Data.EntryA.C017
import LeanDring.P5.Data.EntryA.C018
import LeanDring.P5.Data.EntryA.C019
import LeanDring.P5.Data.EntryA.C020
import LeanDring.P5.Data.EntryA.C021
import LeanDring.P5.Data.EntryA.C022
import LeanDring.P5.Data.EntryA.C023
import LeanDring.P5.Data.EntryA.C024
import LeanDring.P5.Data.EntryA.C025
import LeanDring.P5.Data.EntryA.C026
import LeanDring.P5.Data.EntryA.C027
import LeanDring.P5.Data.EntryA.C028
import LeanDring.P5.Data.EntryA.C029
import LeanDring.P5.Certificate.RingIsomorphism.MatchCore
import LeanDring.P5.Data.SpeciesAlign.C001
import LeanDring.P5.Data.SpeciesAlign.C002
import LeanDring.P5.Data.SpeciesAlign.C003
import LeanDring.P5.Data.SpeciesAlign.C004
import LeanDring.P5.Data.SpeciesAlign.C005
import LeanDring.P5.Data.SpeciesAlign.C006

/-! # Stage-5 leaves, chunk 2 (auto-emitted).  -/

namespace LeanDring.P5Presentation

open MulAction Finset LeanDring.DRing LeanDring.MonGSet

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.style.longLine false

theorem leaf_24_24_5 (hp : 5 < (Q2.transData.getD 24 []).length)
    (j : Nat) (hj : j < (repChars.getD 24 []).length)
    (hq : (normIsRep.getD 24 []).getD j false = true) :
    species (Q2.reps (⟨24, by decide⟩ : Fin 148)) (colE2 ⟨24, by decide⟩ 5 hp)
        (rowE2 (⟨24, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨24, by decide⟩ : Fin 148))
        (colE1 ⟨24, by decide⟩ 5 (transLenTr ⟨24, by decide⟩ 5 hp))
        (rowE1 (⟨24, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨24, by decide⟩ : Fin 148) ⟨24, by decide⟩ _
      (validAt ⟨24, by decide⟩ (listedAt ⟨24, by decide⟩ hj))
      (colE1 ⟨24, by decide⟩ 5 (transLenTr ⟨24, by decide⟩ 5 hp)) T24_24
      hfix24_24 hinj24_24 hcardT24_24
      (fun i => conj_mem_of_fixedPoints _ _ (T24_24 i) (hfix24_24 i) _)
      ⟨24, by decide⟩ ⟨24, by decide⟩ _
      (Q2.validAt ⟨24, by decide⟩ (Q2.listedAt ⟨24, by decide⟩
        (alnCheck_rep ⟨24, by decide⟩ hj hq).1))
      (colE2 ⟨24, by decide⟩ 5 hp) Q2.T24_24_2 Q2.hfix24_24_2 Q2.hinj24_24_2
      Q2.hcardT24_24_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T24_24_2 i) (Q2.hfix24_24_2 i) _)
      colCert_24_24_5.hD ?_).symm
  rw [alnId_24 j hj]


theorem leaf_24_24_10 (hp : 10 < (Q2.transData.getD 24 []).length)
    (j : Nat) (hj : j < (repChars.getD 24 []).length)
    (hq : (normIsRep.getD 24 []).getD j false = true) :
    species (Q2.reps (⟨24, by decide⟩ : Fin 148)) (colE2 ⟨24, by decide⟩ 10 hp)
        (rowE2 (⟨24, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨24, by decide⟩ : Fin 148))
        (colE1 ⟨24, by decide⟩ 10 (transLenTr ⟨24, by decide⟩ 10 hp))
        (rowE1 (⟨24, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨24, by decide⟩ : Fin 148) ⟨24, by decide⟩ _
      (validAt ⟨24, by decide⟩ (listedAt ⟨24, by decide⟩ hj))
      (colE1 ⟨24, by decide⟩ 10 (transLenTr ⟨24, by decide⟩ 10 hp)) T24_24
      hfix24_24 hinj24_24 hcardT24_24
      (fun i => conj_mem_of_fixedPoints _ _ (T24_24 i) (hfix24_24 i) _)
      ⟨24, by decide⟩ ⟨24, by decide⟩ _
      (Q2.validAt ⟨24, by decide⟩ (Q2.listedAt ⟨24, by decide⟩
        (alnCheck_rep ⟨24, by decide⟩ hj hq).1))
      (colE2 ⟨24, by decide⟩ 10 hp) Q2.T24_24_2 Q2.hfix24_24_2 Q2.hinj24_24_2
      Q2.hcardT24_24_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T24_24_2 i) (Q2.hfix24_24_2 i) _)
      colCert_24_24_10.hD ?_).symm
  rw [alnId_24 j hj]


theorem leaf_24_24_15 (hp : 15 < (Q2.transData.getD 24 []).length)
    (j : Nat) (hj : j < (repChars.getD 24 []).length)
    (hq : (normIsRep.getD 24 []).getD j false = true) :
    species (Q2.reps (⟨24, by decide⟩ : Fin 148)) (colE2 ⟨24, by decide⟩ 15 hp)
        (rowE2 (⟨24, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨24, by decide⟩ : Fin 148))
        (colE1 ⟨24, by decide⟩ 15 (transLenTr ⟨24, by decide⟩ 15 hp))
        (rowE1 (⟨24, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨24, by decide⟩ : Fin 148) ⟨24, by decide⟩ _
      (validAt ⟨24, by decide⟩ (listedAt ⟨24, by decide⟩ hj))
      (colE1 ⟨24, by decide⟩ 15 (transLenTr ⟨24, by decide⟩ 15 hp)) T24_24
      hfix24_24 hinj24_24 hcardT24_24
      (fun i => conj_mem_of_fixedPoints _ _ (T24_24 i) (hfix24_24 i) _)
      ⟨24, by decide⟩ ⟨24, by decide⟩ _
      (Q2.validAt ⟨24, by decide⟩ (Q2.listedAt ⟨24, by decide⟩
        (alnCheck_rep ⟨24, by decide⟩ hj hq).1))
      (colE2 ⟨24, by decide⟩ 15 hp) Q2.T24_24_2 Q2.hfix24_24_2 Q2.hinj24_24_2
      Q2.hcardT24_24_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T24_24_2 i) (Q2.hfix24_24_2 i) _)
      colCert_24_24_15.hD ?_).symm
  rw [alnId_24 j hj]


theorem leaf_24_24_20 (hp : 20 < (Q2.transData.getD 24 []).length)
    (j : Nat) (hj : j < (repChars.getD 24 []).length)
    (hq : (normIsRep.getD 24 []).getD j false = true) :
    species (Q2.reps (⟨24, by decide⟩ : Fin 148)) (colE2 ⟨24, by decide⟩ 20 hp)
        (rowE2 (⟨24, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨24, by decide⟩ : Fin 148))
        (colE1 ⟨24, by decide⟩ 20 (transLenTr ⟨24, by decide⟩ 20 hp))
        (rowE1 (⟨24, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨24, by decide⟩ : Fin 148) ⟨24, by decide⟩ _
      (validAt ⟨24, by decide⟩ (listedAt ⟨24, by decide⟩ hj))
      (colE1 ⟨24, by decide⟩ 20 (transLenTr ⟨24, by decide⟩ 20 hp)) T24_24
      hfix24_24 hinj24_24 hcardT24_24
      (fun i => conj_mem_of_fixedPoints _ _ (T24_24 i) (hfix24_24 i) _)
      ⟨24, by decide⟩ ⟨24, by decide⟩ _
      (Q2.validAt ⟨24, by decide⟩ (Q2.listedAt ⟨24, by decide⟩
        (alnCheck_rep ⟨24, by decide⟩ hj hq).1))
      (colE2 ⟨24, by decide⟩ 20 hp) Q2.T24_24_2 Q2.hfix24_24_2 Q2.hinj24_24_2
      Q2.hcardT24_24_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T24_24_2 i) (Q2.hfix24_24_2 i) _)
      colCert_24_24_20.hD ?_).symm
  rw [alnId_24 j hj]


theorem leaf_25_7_0 (hp : 0 < (Q2.transData.getD 7 []).length)
    (j : Nat) (hj : j < (repChars.getD 25 []).length)
    (hq : (normIsRep.getD 25 []).getD j false = true) :
    species (Q2.reps (⟨7, by decide⟩ : Fin 148)) (colE2 ⟨7, by decide⟩ 0 hp)
        (rowE2 (⟨25, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨7, by decide⟩ : Fin 148))
        (colE1 ⟨7, by decide⟩ 0 (transLenTr ⟨7, by decide⟩ 0 hp))
        (rowE1 (⟨25, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨25, by decide⟩ : Fin 148) ⟨7, by decide⟩ _
      (validAt ⟨25, by decide⟩ (listedAt ⟨25, by decide⟩ hj))
      (colE1 ⟨7, by decide⟩ 0 (transLenTr ⟨7, by decide⟩ 0 hp)) T25_7
      hfix25_7 hinj25_7 hcardT25_7
      (fun i => conj_mem_of_fixedPoints _ _ (T25_7 i) (hfix25_7 i) _)
      ⟨25, by decide⟩ ⟨7, by decide⟩ _
      (Q2.validAt ⟨25, by decide⟩ (Q2.listedAt ⟨25, by decide⟩
        (alnCheck_rep ⟨25, by decide⟩ hj hq).1))
      (colE2 ⟨7, by decide⟩ 0 hp) Q2.T25_7_2 Q2.hfix25_7_2 Q2.hinj25_7_2
      Q2.hcardT25_7_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T25_7_2 i) (Q2.hfix25_7_2 i) _)
      colCert_25_7_0.hD ?_).symm
  rw [alnId_25 j hj]


theorem leaf_25_7_1 (hp : 1 < (Q2.transData.getD 7 []).length)
    (j : Nat) (hj : j < (repChars.getD 25 []).length)
    (hq : (normIsRep.getD 25 []).getD j false = true) :
    species (Q2.reps (⟨7, by decide⟩ : Fin 148)) (colE2 ⟨7, by decide⟩ 1 hp)
        (rowE2 (⟨25, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨7, by decide⟩ : Fin 148))
        (colE1 ⟨7, by decide⟩ 1 (transLenTr ⟨7, by decide⟩ 1 hp))
        (rowE1 (⟨25, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨25, by decide⟩ : Fin 148) ⟨7, by decide⟩ _
      (validAt ⟨25, by decide⟩ (listedAt ⟨25, by decide⟩ hj))
      (colE1 ⟨7, by decide⟩ 1 (transLenTr ⟨7, by decide⟩ 1 hp)) T25_7
      hfix25_7 hinj25_7 hcardT25_7
      (fun i => conj_mem_of_fixedPoints _ _ (T25_7 i) (hfix25_7 i) _)
      ⟨25, by decide⟩ ⟨7, by decide⟩ _
      (Q2.validAt ⟨25, by decide⟩ (Q2.listedAt ⟨25, by decide⟩
        (alnCheck_rep ⟨25, by decide⟩ hj hq).1))
      (colE2 ⟨7, by decide⟩ 1 hp) Q2.T25_7_2 Q2.hfix25_7_2 Q2.hinj25_7_2
      Q2.hcardT25_7_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T25_7_2 i) (Q2.hfix25_7_2 i) _)
      colCert_25_7_1.hD ?_).symm
  rw [alnId_25 j hj]


theorem leaf_25_7_2 (hp : 2 < (Q2.transData.getD 7 []).length)
    (j : Nat) (hj : j < (repChars.getD 25 []).length)
    (hq : (normIsRep.getD 25 []).getD j false = true) :
    species (Q2.reps (⟨7, by decide⟩ : Fin 148)) (colE2 ⟨7, by decide⟩ 2 hp)
        (rowE2 (⟨25, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨7, by decide⟩ : Fin 148))
        (colE1 ⟨7, by decide⟩ 2 (transLenTr ⟨7, by decide⟩ 2 hp))
        (rowE1 (⟨25, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨25, by decide⟩ : Fin 148) ⟨7, by decide⟩ _
      (validAt ⟨25, by decide⟩ (listedAt ⟨25, by decide⟩ hj))
      (colE1 ⟨7, by decide⟩ 2 (transLenTr ⟨7, by decide⟩ 2 hp)) T25_7
      hfix25_7 hinj25_7 hcardT25_7
      (fun i => conj_mem_of_fixedPoints _ _ (T25_7 i) (hfix25_7 i) _)
      ⟨25, by decide⟩ ⟨7, by decide⟩ _
      (Q2.validAt ⟨25, by decide⟩ (Q2.listedAt ⟨25, by decide⟩
        (alnCheck_rep ⟨25, by decide⟩ hj hq).1))
      (colE2 ⟨7, by decide⟩ 2 hp) Q2.T25_7_2 Q2.hfix25_7_2 Q2.hinj25_7_2
      Q2.hcardT25_7_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T25_7_2 i) (Q2.hfix25_7_2 i) _)
      colCert_25_7_2.hD ?_).symm
  rw [alnId_25 j hj]


theorem leaf_25_7_3 (hp : 3 < (Q2.transData.getD 7 []).length)
    (j : Nat) (hj : j < (repChars.getD 25 []).length)
    (hq : (normIsRep.getD 25 []).getD j false = true) :
    species (Q2.reps (⟨7, by decide⟩ : Fin 148)) (colE2 ⟨7, by decide⟩ 3 hp)
        (rowE2 (⟨25, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨7, by decide⟩ : Fin 148))
        (colE1 ⟨7, by decide⟩ 3 (transLenTr ⟨7, by decide⟩ 3 hp))
        (rowE1 (⟨25, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨25, by decide⟩ : Fin 148) ⟨7, by decide⟩ _
      (validAt ⟨25, by decide⟩ (listedAt ⟨25, by decide⟩ hj))
      (colE1 ⟨7, by decide⟩ 3 (transLenTr ⟨7, by decide⟩ 3 hp)) T25_7
      hfix25_7 hinj25_7 hcardT25_7
      (fun i => conj_mem_of_fixedPoints _ _ (T25_7 i) (hfix25_7 i) _)
      ⟨25, by decide⟩ ⟨7, by decide⟩ _
      (Q2.validAt ⟨25, by decide⟩ (Q2.listedAt ⟨25, by decide⟩
        (alnCheck_rep ⟨25, by decide⟩ hj hq).1))
      (colE2 ⟨7, by decide⟩ 3 hp) Q2.T25_7_2 Q2.hfix25_7_2 Q2.hinj25_7_2
      Q2.hcardT25_7_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T25_7_2 i) (Q2.hfix25_7_2 i) _)
      colCert_25_7_3.hD ?_).symm
  rw [alnId_25 j hj]


theorem leaf_25_7_4 (hp : 4 < (Q2.transData.getD 7 []).length)
    (j : Nat) (hj : j < (repChars.getD 25 []).length)
    (hq : (normIsRep.getD 25 []).getD j false = true) :
    species (Q2.reps (⟨7, by decide⟩ : Fin 148)) (colE2 ⟨7, by decide⟩ 4 hp)
        (rowE2 (⟨25, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨7, by decide⟩ : Fin 148))
        (colE1 ⟨7, by decide⟩ 4 (transLenTr ⟨7, by decide⟩ 4 hp))
        (rowE1 (⟨25, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨25, by decide⟩ : Fin 148) ⟨7, by decide⟩ _
      (validAt ⟨25, by decide⟩ (listedAt ⟨25, by decide⟩ hj))
      (colE1 ⟨7, by decide⟩ 4 (transLenTr ⟨7, by decide⟩ 4 hp)) T25_7
      hfix25_7 hinj25_7 hcardT25_7
      (fun i => conj_mem_of_fixedPoints _ _ (T25_7 i) (hfix25_7 i) _)
      ⟨25, by decide⟩ ⟨7, by decide⟩ _
      (Q2.validAt ⟨25, by decide⟩ (Q2.listedAt ⟨25, by decide⟩
        (alnCheck_rep ⟨25, by decide⟩ hj hq).1))
      (colE2 ⟨7, by decide⟩ 4 hp) Q2.T25_7_2 Q2.hfix25_7_2 Q2.hinj25_7_2
      Q2.hcardT25_7_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T25_7_2 i) (Q2.hfix25_7_2 i) _)
      colCert_25_7_4.hD ?_).symm
  rw [alnId_25 j hj]


theorem leaf_25_12_0 (hp : 0 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 25 []).length)
    (hq : (normIsRep.getD 25 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 0 hp)
        (rowE2 (⟨25, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp))
        (rowE1 (⟨25, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨25, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨25, by decide⟩ (listedAt ⟨25, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp)) T25_12
      hfix25_12 hinj25_12 hcardT25_12
      (fun i => conj_mem_of_fixedPoints _ _ (T25_12 i) (hfix25_12 i) _)
      ⟨25, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨25, by decide⟩ (Q2.listedAt ⟨25, by decide⟩
        (alnCheck_rep ⟨25, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 0 hp) Q2.T25_12_2 Q2.hfix25_12_2 Q2.hinj25_12_2
      Q2.hcardT25_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T25_12_2 i) (Q2.hfix25_12_2 i) _)
      colCert_25_12_0.hD ?_).symm
  rw [alnId_25 j hj]


theorem leaf_25_12_1 (hp : 1 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 25 []).length)
    (hq : (normIsRep.getD 25 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 1 hp)
        (rowE2 (⟨25, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp))
        (rowE1 (⟨25, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨25, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨25, by decide⟩ (listedAt ⟨25, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp)) T25_12
      hfix25_12 hinj25_12 hcardT25_12
      (fun i => conj_mem_of_fixedPoints _ _ (T25_12 i) (hfix25_12 i) _)
      ⟨25, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨25, by decide⟩ (Q2.listedAt ⟨25, by decide⟩
        (alnCheck_rep ⟨25, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 1 hp) Q2.T25_12_2 Q2.hfix25_12_2 Q2.hinj25_12_2
      Q2.hcardT25_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T25_12_2 i) (Q2.hfix25_12_2 i) _)
      colCert_25_12_1.hD ?_).symm
  rw [alnId_25 j hj]


theorem leaf_25_12_2 (hp : 2 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 25 []).length)
    (hq : (normIsRep.getD 25 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 2 hp)
        (rowE2 (⟨25, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp))
        (rowE1 (⟨25, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨25, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨25, by decide⟩ (listedAt ⟨25, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp)) T25_12
      hfix25_12 hinj25_12 hcardT25_12
      (fun i => conj_mem_of_fixedPoints _ _ (T25_12 i) (hfix25_12 i) _)
      ⟨25, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨25, by decide⟩ (Q2.listedAt ⟨25, by decide⟩
        (alnCheck_rep ⟨25, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 2 hp) Q2.T25_12_2 Q2.hfix25_12_2 Q2.hinj25_12_2
      Q2.hcardT25_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T25_12_2 i) (Q2.hfix25_12_2 i) _)
      colCert_25_12_2.hD ?_).symm
  rw [alnId_25 j hj]


theorem leaf_25_12_3 (hp : 3 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 25 []).length)
    (hq : (normIsRep.getD 25 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 3 hp)
        (rowE2 (⟨25, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp))
        (rowE1 (⟨25, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨25, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨25, by decide⟩ (listedAt ⟨25, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp)) T25_12
      hfix25_12 hinj25_12 hcardT25_12
      (fun i => conj_mem_of_fixedPoints _ _ (T25_12 i) (hfix25_12 i) _)
      ⟨25, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨25, by decide⟩ (Q2.listedAt ⟨25, by decide⟩
        (alnCheck_rep ⟨25, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 3 hp) Q2.T25_12_2 Q2.hfix25_12_2 Q2.hinj25_12_2
      Q2.hcardT25_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T25_12_2 i) (Q2.hfix25_12_2 i) _)
      colCert_25_12_3.hD ?_).symm
  rw [alnId_25 j hj]


theorem leaf_25_12_4 (hp : 4 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 25 []).length)
    (hq : (normIsRep.getD 25 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 4 hp)
        (rowE2 (⟨25, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp))
        (rowE1 (⟨25, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨25, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨25, by decide⟩ (listedAt ⟨25, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp)) T25_12
      hfix25_12 hinj25_12 hcardT25_12
      (fun i => conj_mem_of_fixedPoints _ _ (T25_12 i) (hfix25_12 i) _)
      ⟨25, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨25, by decide⟩ (Q2.listedAt ⟨25, by decide⟩
        (alnCheck_rep ⟨25, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 4 hp) Q2.T25_12_2 Q2.hfix25_12_2 Q2.hinj25_12_2
      Q2.hcardT25_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T25_12_2 i) (Q2.hfix25_12_2 i) _)
      colCert_25_12_4.hD ?_).symm
  rw [alnId_25 j hj]


theorem leaf_25_25_0 (hp : 0 < (Q2.transData.getD 25 []).length)
    (j : Nat) (hj : j < (repChars.getD 25 []).length)
    (hq : (normIsRep.getD 25 []).getD j false = true) :
    species (Q2.reps (⟨25, by decide⟩ : Fin 148)) (colE2 ⟨25, by decide⟩ 0 hp)
        (rowE2 (⟨25, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨25, by decide⟩ : Fin 148))
        (colE1 ⟨25, by decide⟩ 0 (transLenTr ⟨25, by decide⟩ 0 hp))
        (rowE1 (⟨25, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨25, by decide⟩ : Fin 148) ⟨25, by decide⟩ _
      (validAt ⟨25, by decide⟩ (listedAt ⟨25, by decide⟩ hj))
      (colE1 ⟨25, by decide⟩ 0 (transLenTr ⟨25, by decide⟩ 0 hp)) T25_25
      hfix25_25 hinj25_25 hcardT25_25
      (fun i => conj_mem_of_fixedPoints _ _ (T25_25 i) (hfix25_25 i) _)
      ⟨25, by decide⟩ ⟨25, by decide⟩ _
      (Q2.validAt ⟨25, by decide⟩ (Q2.listedAt ⟨25, by decide⟩
        (alnCheck_rep ⟨25, by decide⟩ hj hq).1))
      (colE2 ⟨25, by decide⟩ 0 hp) Q2.T25_25_2 Q2.hfix25_25_2 Q2.hinj25_25_2
      Q2.hcardT25_25_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T25_25_2 i) (Q2.hfix25_25_2 i) _)
      colCert_25_25_0.hD ?_).symm
  rw [alnId_25 j hj]


theorem leaf_25_25_1 (hp : 1 < (Q2.transData.getD 25 []).length)
    (j : Nat) (hj : j < (repChars.getD 25 []).length)
    (hq : (normIsRep.getD 25 []).getD j false = true) :
    species (Q2.reps (⟨25, by decide⟩ : Fin 148)) (colE2 ⟨25, by decide⟩ 1 hp)
        (rowE2 (⟨25, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨25, by decide⟩ : Fin 148))
        (colE1 ⟨25, by decide⟩ 1 (transLenTr ⟨25, by decide⟩ 1 hp))
        (rowE1 (⟨25, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨25, by decide⟩ : Fin 148) ⟨25, by decide⟩ _
      (validAt ⟨25, by decide⟩ (listedAt ⟨25, by decide⟩ hj))
      (colE1 ⟨25, by decide⟩ 1 (transLenTr ⟨25, by decide⟩ 1 hp)) T25_25
      hfix25_25 hinj25_25 hcardT25_25
      (fun i => conj_mem_of_fixedPoints _ _ (T25_25 i) (hfix25_25 i) _)
      ⟨25, by decide⟩ ⟨25, by decide⟩ _
      (Q2.validAt ⟨25, by decide⟩ (Q2.listedAt ⟨25, by decide⟩
        (alnCheck_rep ⟨25, by decide⟩ hj hq).1))
      (colE2 ⟨25, by decide⟩ 1 hp) Q2.T25_25_2 Q2.hfix25_25_2 Q2.hinj25_25_2
      Q2.hcardT25_25_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T25_25_2 i) (Q2.hfix25_25_2 i) _)
      colCert_25_25_1.hD ?_).symm
  rw [alnId_25 j hj]


theorem leaf_25_25_2 (hp : 2 < (Q2.transData.getD 25 []).length)
    (j : Nat) (hj : j < (repChars.getD 25 []).length)
    (hq : (normIsRep.getD 25 []).getD j false = true) :
    species (Q2.reps (⟨25, by decide⟩ : Fin 148)) (colE2 ⟨25, by decide⟩ 2 hp)
        (rowE2 (⟨25, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨25, by decide⟩ : Fin 148))
        (colE1 ⟨25, by decide⟩ 2 (transLenTr ⟨25, by decide⟩ 2 hp))
        (rowE1 (⟨25, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨25, by decide⟩ : Fin 148) ⟨25, by decide⟩ _
      (validAt ⟨25, by decide⟩ (listedAt ⟨25, by decide⟩ hj))
      (colE1 ⟨25, by decide⟩ 2 (transLenTr ⟨25, by decide⟩ 2 hp)) T25_25
      hfix25_25 hinj25_25 hcardT25_25
      (fun i => conj_mem_of_fixedPoints _ _ (T25_25 i) (hfix25_25 i) _)
      ⟨25, by decide⟩ ⟨25, by decide⟩ _
      (Q2.validAt ⟨25, by decide⟩ (Q2.listedAt ⟨25, by decide⟩
        (alnCheck_rep ⟨25, by decide⟩ hj hq).1))
      (colE2 ⟨25, by decide⟩ 2 hp) Q2.T25_25_2 Q2.hfix25_25_2 Q2.hinj25_25_2
      Q2.hcardT25_25_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T25_25_2 i) (Q2.hfix25_25_2 i) _)
      colCert_25_25_2.hD ?_).symm
  rw [alnId_25 j hj]


theorem leaf_25_25_3 (hp : 3 < (Q2.transData.getD 25 []).length)
    (j : Nat) (hj : j < (repChars.getD 25 []).length)
    (hq : (normIsRep.getD 25 []).getD j false = true) :
    species (Q2.reps (⟨25, by decide⟩ : Fin 148)) (colE2 ⟨25, by decide⟩ 3 hp)
        (rowE2 (⟨25, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨25, by decide⟩ : Fin 148))
        (colE1 ⟨25, by decide⟩ 3 (transLenTr ⟨25, by decide⟩ 3 hp))
        (rowE1 (⟨25, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨25, by decide⟩ : Fin 148) ⟨25, by decide⟩ _
      (validAt ⟨25, by decide⟩ (listedAt ⟨25, by decide⟩ hj))
      (colE1 ⟨25, by decide⟩ 3 (transLenTr ⟨25, by decide⟩ 3 hp)) T25_25
      hfix25_25 hinj25_25 hcardT25_25
      (fun i => conj_mem_of_fixedPoints _ _ (T25_25 i) (hfix25_25 i) _)
      ⟨25, by decide⟩ ⟨25, by decide⟩ _
      (Q2.validAt ⟨25, by decide⟩ (Q2.listedAt ⟨25, by decide⟩
        (alnCheck_rep ⟨25, by decide⟩ hj hq).1))
      (colE2 ⟨25, by decide⟩ 3 hp) Q2.T25_25_2 Q2.hfix25_25_2 Q2.hinj25_25_2
      Q2.hcardT25_25_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T25_25_2 i) (Q2.hfix25_25_2 i) _)
      colCert_25_25_3.hD ?_).symm
  rw [alnId_25 j hj]


theorem leaf_25_25_4 (hp : 4 < (Q2.transData.getD 25 []).length)
    (j : Nat) (hj : j < (repChars.getD 25 []).length)
    (hq : (normIsRep.getD 25 []).getD j false = true) :
    species (Q2.reps (⟨25, by decide⟩ : Fin 148)) (colE2 ⟨25, by decide⟩ 4 hp)
        (rowE2 (⟨25, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨25, by decide⟩ : Fin 148))
        (colE1 ⟨25, by decide⟩ 4 (transLenTr ⟨25, by decide⟩ 4 hp))
        (rowE1 (⟨25, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨25, by decide⟩ : Fin 148) ⟨25, by decide⟩ _
      (validAt ⟨25, by decide⟩ (listedAt ⟨25, by decide⟩ hj))
      (colE1 ⟨25, by decide⟩ 4 (transLenTr ⟨25, by decide⟩ 4 hp)) T25_25
      hfix25_25 hinj25_25 hcardT25_25
      (fun i => conj_mem_of_fixedPoints _ _ (T25_25 i) (hfix25_25 i) _)
      ⟨25, by decide⟩ ⟨25, by decide⟩ _
      (Q2.validAt ⟨25, by decide⟩ (Q2.listedAt ⟨25, by decide⟩
        (alnCheck_rep ⟨25, by decide⟩ hj hq).1))
      (colE2 ⟨25, by decide⟩ 4 hp) Q2.T25_25_2 Q2.hfix25_25_2 Q2.hinj25_25_2
      Q2.hcardT25_25_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T25_25_2 i) (Q2.hfix25_25_2 i) _)
      colCert_25_25_4.hD ?_).symm
  rw [alnId_25 j hj]


theorem leaf_25_25_5 (hp : 5 < (Q2.transData.getD 25 []).length)
    (j : Nat) (hj : j < (repChars.getD 25 []).length)
    (hq : (normIsRep.getD 25 []).getD j false = true) :
    species (Q2.reps (⟨25, by decide⟩ : Fin 148)) (colE2 ⟨25, by decide⟩ 5 hp)
        (rowE2 (⟨25, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨25, by decide⟩ : Fin 148))
        (colE1 ⟨25, by decide⟩ 5 (transLenTr ⟨25, by decide⟩ 5 hp))
        (rowE1 (⟨25, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨25, by decide⟩ : Fin 148) ⟨25, by decide⟩ _
      (validAt ⟨25, by decide⟩ (listedAt ⟨25, by decide⟩ hj))
      (colE1 ⟨25, by decide⟩ 5 (transLenTr ⟨25, by decide⟩ 5 hp)) T25_25
      hfix25_25 hinj25_25 hcardT25_25
      (fun i => conj_mem_of_fixedPoints _ _ (T25_25 i) (hfix25_25 i) _)
      ⟨25, by decide⟩ ⟨25, by decide⟩ _
      (Q2.validAt ⟨25, by decide⟩ (Q2.listedAt ⟨25, by decide⟩
        (alnCheck_rep ⟨25, by decide⟩ hj hq).1))
      (colE2 ⟨25, by decide⟩ 5 hp) Q2.T25_25_2 Q2.hfix25_25_2 Q2.hinj25_25_2
      Q2.hcardT25_25_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T25_25_2 i) (Q2.hfix25_25_2 i) _)
      colCert_25_25_5.hD ?_).symm
  rw [alnId_25 j hj]


theorem leaf_25_25_10 (hp : 10 < (Q2.transData.getD 25 []).length)
    (j : Nat) (hj : j < (repChars.getD 25 []).length)
    (hq : (normIsRep.getD 25 []).getD j false = true) :
    species (Q2.reps (⟨25, by decide⟩ : Fin 148)) (colE2 ⟨25, by decide⟩ 10 hp)
        (rowE2 (⟨25, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨25, by decide⟩ : Fin 148))
        (colE1 ⟨25, by decide⟩ 10 (transLenTr ⟨25, by decide⟩ 10 hp))
        (rowE1 (⟨25, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨25, by decide⟩ : Fin 148) ⟨25, by decide⟩ _
      (validAt ⟨25, by decide⟩ (listedAt ⟨25, by decide⟩ hj))
      (colE1 ⟨25, by decide⟩ 10 (transLenTr ⟨25, by decide⟩ 10 hp)) T25_25
      hfix25_25 hinj25_25 hcardT25_25
      (fun i => conj_mem_of_fixedPoints _ _ (T25_25 i) (hfix25_25 i) _)
      ⟨25, by decide⟩ ⟨25, by decide⟩ _
      (Q2.validAt ⟨25, by decide⟩ (Q2.listedAt ⟨25, by decide⟩
        (alnCheck_rep ⟨25, by decide⟩ hj hq).1))
      (colE2 ⟨25, by decide⟩ 10 hp) Q2.T25_25_2 Q2.hfix25_25_2 Q2.hinj25_25_2
      Q2.hcardT25_25_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T25_25_2 i) (Q2.hfix25_25_2 i) _)
      colCert_25_25_10.hD ?_).symm
  rw [alnId_25 j hj]


theorem leaf_25_25_15 (hp : 15 < (Q2.transData.getD 25 []).length)
    (j : Nat) (hj : j < (repChars.getD 25 []).length)
    (hq : (normIsRep.getD 25 []).getD j false = true) :
    species (Q2.reps (⟨25, by decide⟩ : Fin 148)) (colE2 ⟨25, by decide⟩ 15 hp)
        (rowE2 (⟨25, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨25, by decide⟩ : Fin 148))
        (colE1 ⟨25, by decide⟩ 15 (transLenTr ⟨25, by decide⟩ 15 hp))
        (rowE1 (⟨25, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨25, by decide⟩ : Fin 148) ⟨25, by decide⟩ _
      (validAt ⟨25, by decide⟩ (listedAt ⟨25, by decide⟩ hj))
      (colE1 ⟨25, by decide⟩ 15 (transLenTr ⟨25, by decide⟩ 15 hp)) T25_25
      hfix25_25 hinj25_25 hcardT25_25
      (fun i => conj_mem_of_fixedPoints _ _ (T25_25 i) (hfix25_25 i) _)
      ⟨25, by decide⟩ ⟨25, by decide⟩ _
      (Q2.validAt ⟨25, by decide⟩ (Q2.listedAt ⟨25, by decide⟩
        (alnCheck_rep ⟨25, by decide⟩ hj hq).1))
      (colE2 ⟨25, by decide⟩ 15 hp) Q2.T25_25_2 Q2.hfix25_25_2 Q2.hinj25_25_2
      Q2.hcardT25_25_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T25_25_2 i) (Q2.hfix25_25_2 i) _)
      colCert_25_25_15.hD ?_).symm
  rw [alnId_25 j hj]


theorem leaf_25_25_20 (hp : 20 < (Q2.transData.getD 25 []).length)
    (j : Nat) (hj : j < (repChars.getD 25 []).length)
    (hq : (normIsRep.getD 25 []).getD j false = true) :
    species (Q2.reps (⟨25, by decide⟩ : Fin 148)) (colE2 ⟨25, by decide⟩ 20 hp)
        (rowE2 (⟨25, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨25, by decide⟩ : Fin 148))
        (colE1 ⟨25, by decide⟩ 20 (transLenTr ⟨25, by decide⟩ 20 hp))
        (rowE1 (⟨25, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨25, by decide⟩ : Fin 148) ⟨25, by decide⟩ _
      (validAt ⟨25, by decide⟩ (listedAt ⟨25, by decide⟩ hj))
      (colE1 ⟨25, by decide⟩ 20 (transLenTr ⟨25, by decide⟩ 20 hp)) T25_25
      hfix25_25 hinj25_25 hcardT25_25
      (fun i => conj_mem_of_fixedPoints _ _ (T25_25 i) (hfix25_25 i) _)
      ⟨25, by decide⟩ ⟨25, by decide⟩ _
      (Q2.validAt ⟨25, by decide⟩ (Q2.listedAt ⟨25, by decide⟩
        (alnCheck_rep ⟨25, by decide⟩ hj hq).1))
      (colE2 ⟨25, by decide⟩ 20 hp) Q2.T25_25_2 Q2.hfix25_25_2 Q2.hinj25_25_2
      Q2.hcardT25_25_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T25_25_2 i) (Q2.hfix25_25_2 i) _)
      colCert_25_25_20.hD ?_).symm
  rw [alnId_25 j hj]


theorem leaf_26_8_0 (hp : 0 < (Q2.transData.getD 8 []).length)
    (j : Nat) (hj : j < (repChars.getD 26 []).length)
    (hq : (normIsRep.getD 26 []).getD j false = true) :
    species (Q2.reps (⟨8, by decide⟩ : Fin 148)) (colE2 ⟨8, by decide⟩ 0 hp)
        (rowE2 (⟨26, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨8, by decide⟩ : Fin 148))
        (colE1 ⟨8, by decide⟩ 0 (transLenTr ⟨8, by decide⟩ 0 hp))
        (rowE1 (⟨26, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨26, by decide⟩ : Fin 148) ⟨8, by decide⟩ _
      (validAt ⟨26, by decide⟩ (listedAt ⟨26, by decide⟩ hj))
      (colE1 ⟨8, by decide⟩ 0 (transLenTr ⟨8, by decide⟩ 0 hp)) T26_8
      hfix26_8 hinj26_8 hcardT26_8
      (fun i => conj_mem_of_fixedPoints _ _ (T26_8 i) (hfix26_8 i) _)
      ⟨26, by decide⟩ ⟨8, by decide⟩ _
      (Q2.validAt ⟨26, by decide⟩ (Q2.listedAt ⟨26, by decide⟩
        (alnCheck_rep ⟨26, by decide⟩ hj hq).1))
      (colE2 ⟨8, by decide⟩ 0 hp) Q2.T26_8_2 Q2.hfix26_8_2 Q2.hinj26_8_2
      Q2.hcardT26_8_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T26_8_2 i) (Q2.hfix26_8_2 i) _)
      colCert_26_8_0.hD ?_).symm
  rw [alnId_26 j hj]


theorem leaf_26_8_1 (hp : 1 < (Q2.transData.getD 8 []).length)
    (j : Nat) (hj : j < (repChars.getD 26 []).length)
    (hq : (normIsRep.getD 26 []).getD j false = true) :
    species (Q2.reps (⟨8, by decide⟩ : Fin 148)) (colE2 ⟨8, by decide⟩ 1 hp)
        (rowE2 (⟨26, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨8, by decide⟩ : Fin 148))
        (colE1 ⟨8, by decide⟩ 1 (transLenTr ⟨8, by decide⟩ 1 hp))
        (rowE1 (⟨26, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨26, by decide⟩ : Fin 148) ⟨8, by decide⟩ _
      (validAt ⟨26, by decide⟩ (listedAt ⟨26, by decide⟩ hj))
      (colE1 ⟨8, by decide⟩ 1 (transLenTr ⟨8, by decide⟩ 1 hp)) T26_8
      hfix26_8 hinj26_8 hcardT26_8
      (fun i => conj_mem_of_fixedPoints _ _ (T26_8 i) (hfix26_8 i) _)
      ⟨26, by decide⟩ ⟨8, by decide⟩ _
      (Q2.validAt ⟨26, by decide⟩ (Q2.listedAt ⟨26, by decide⟩
        (alnCheck_rep ⟨26, by decide⟩ hj hq).1))
      (colE2 ⟨8, by decide⟩ 1 hp) Q2.T26_8_2 Q2.hfix26_8_2 Q2.hinj26_8_2
      Q2.hcardT26_8_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T26_8_2 i) (Q2.hfix26_8_2 i) _)
      colCert_26_8_1.hD ?_).symm
  rw [alnId_26 j hj]


theorem leaf_26_8_2 (hp : 2 < (Q2.transData.getD 8 []).length)
    (j : Nat) (hj : j < (repChars.getD 26 []).length)
    (hq : (normIsRep.getD 26 []).getD j false = true) :
    species (Q2.reps (⟨8, by decide⟩ : Fin 148)) (colE2 ⟨8, by decide⟩ 2 hp)
        (rowE2 (⟨26, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨8, by decide⟩ : Fin 148))
        (colE1 ⟨8, by decide⟩ 2 (transLenTr ⟨8, by decide⟩ 2 hp))
        (rowE1 (⟨26, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨26, by decide⟩ : Fin 148) ⟨8, by decide⟩ _
      (validAt ⟨26, by decide⟩ (listedAt ⟨26, by decide⟩ hj))
      (colE1 ⟨8, by decide⟩ 2 (transLenTr ⟨8, by decide⟩ 2 hp)) T26_8
      hfix26_8 hinj26_8 hcardT26_8
      (fun i => conj_mem_of_fixedPoints _ _ (T26_8 i) (hfix26_8 i) _)
      ⟨26, by decide⟩ ⟨8, by decide⟩ _
      (Q2.validAt ⟨26, by decide⟩ (Q2.listedAt ⟨26, by decide⟩
        (alnCheck_rep ⟨26, by decide⟩ hj hq).1))
      (colE2 ⟨8, by decide⟩ 2 hp) Q2.T26_8_2 Q2.hfix26_8_2 Q2.hinj26_8_2
      Q2.hcardT26_8_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T26_8_2 i) (Q2.hfix26_8_2 i) _)
      colCert_26_8_2.hD ?_).symm
  rw [alnId_26 j hj]


theorem leaf_26_8_3 (hp : 3 < (Q2.transData.getD 8 []).length)
    (j : Nat) (hj : j < (repChars.getD 26 []).length)
    (hq : (normIsRep.getD 26 []).getD j false = true) :
    species (Q2.reps (⟨8, by decide⟩ : Fin 148)) (colE2 ⟨8, by decide⟩ 3 hp)
        (rowE2 (⟨26, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨8, by decide⟩ : Fin 148))
        (colE1 ⟨8, by decide⟩ 3 (transLenTr ⟨8, by decide⟩ 3 hp))
        (rowE1 (⟨26, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨26, by decide⟩ : Fin 148) ⟨8, by decide⟩ _
      (validAt ⟨26, by decide⟩ (listedAt ⟨26, by decide⟩ hj))
      (colE1 ⟨8, by decide⟩ 3 (transLenTr ⟨8, by decide⟩ 3 hp)) T26_8
      hfix26_8 hinj26_8 hcardT26_8
      (fun i => conj_mem_of_fixedPoints _ _ (T26_8 i) (hfix26_8 i) _)
      ⟨26, by decide⟩ ⟨8, by decide⟩ _
      (Q2.validAt ⟨26, by decide⟩ (Q2.listedAt ⟨26, by decide⟩
        (alnCheck_rep ⟨26, by decide⟩ hj hq).1))
      (colE2 ⟨8, by decide⟩ 3 hp) Q2.T26_8_2 Q2.hfix26_8_2 Q2.hinj26_8_2
      Q2.hcardT26_8_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T26_8_2 i) (Q2.hfix26_8_2 i) _)
      colCert_26_8_3.hD ?_).symm
  rw [alnId_26 j hj]


theorem leaf_26_8_4 (hp : 4 < (Q2.transData.getD 8 []).length)
    (j : Nat) (hj : j < (repChars.getD 26 []).length)
    (hq : (normIsRep.getD 26 []).getD j false = true) :
    species (Q2.reps (⟨8, by decide⟩ : Fin 148)) (colE2 ⟨8, by decide⟩ 4 hp)
        (rowE2 (⟨26, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨8, by decide⟩ : Fin 148))
        (colE1 ⟨8, by decide⟩ 4 (transLenTr ⟨8, by decide⟩ 4 hp))
        (rowE1 (⟨26, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨26, by decide⟩ : Fin 148) ⟨8, by decide⟩ _
      (validAt ⟨26, by decide⟩ (listedAt ⟨26, by decide⟩ hj))
      (colE1 ⟨8, by decide⟩ 4 (transLenTr ⟨8, by decide⟩ 4 hp)) T26_8
      hfix26_8 hinj26_8 hcardT26_8
      (fun i => conj_mem_of_fixedPoints _ _ (T26_8 i) (hfix26_8 i) _)
      ⟨26, by decide⟩ ⟨8, by decide⟩ _
      (Q2.validAt ⟨26, by decide⟩ (Q2.listedAt ⟨26, by decide⟩
        (alnCheck_rep ⟨26, by decide⟩ hj hq).1))
      (colE2 ⟨8, by decide⟩ 4 hp) Q2.T26_8_2 Q2.hfix26_8_2 Q2.hinj26_8_2
      Q2.hcardT26_8_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T26_8_2 i) (Q2.hfix26_8_2 i) _)
      colCert_26_8_4.hD ?_).symm
  rw [alnId_26 j hj]


theorem leaf_26_12_0 (hp : 0 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 26 []).length)
    (hq : (normIsRep.getD 26 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 0 hp)
        (rowE2 (⟨26, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp))
        (rowE1 (⟨26, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨26, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨26, by decide⟩ (listedAt ⟨26, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp)) T26_12
      hfix26_12 hinj26_12 hcardT26_12
      (fun i => conj_mem_of_fixedPoints _ _ (T26_12 i) (hfix26_12 i) _)
      ⟨26, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨26, by decide⟩ (Q2.listedAt ⟨26, by decide⟩
        (alnCheck_rep ⟨26, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 0 hp) Q2.T26_12_2 Q2.hfix26_12_2 Q2.hinj26_12_2
      Q2.hcardT26_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T26_12_2 i) (Q2.hfix26_12_2 i) _)
      colCert_26_12_0.hD ?_).symm
  rw [alnId_26 j hj]


theorem leaf_26_12_1 (hp : 1 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 26 []).length)
    (hq : (normIsRep.getD 26 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 1 hp)
        (rowE2 (⟨26, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp))
        (rowE1 (⟨26, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨26, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨26, by decide⟩ (listedAt ⟨26, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp)) T26_12
      hfix26_12 hinj26_12 hcardT26_12
      (fun i => conj_mem_of_fixedPoints _ _ (T26_12 i) (hfix26_12 i) _)
      ⟨26, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨26, by decide⟩ (Q2.listedAt ⟨26, by decide⟩
        (alnCheck_rep ⟨26, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 1 hp) Q2.T26_12_2 Q2.hfix26_12_2 Q2.hinj26_12_2
      Q2.hcardT26_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T26_12_2 i) (Q2.hfix26_12_2 i) _)
      colCert_26_12_1.hD ?_).symm
  rw [alnId_26 j hj]


theorem leaf_26_12_2 (hp : 2 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 26 []).length)
    (hq : (normIsRep.getD 26 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 2 hp)
        (rowE2 (⟨26, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp))
        (rowE1 (⟨26, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨26, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨26, by decide⟩ (listedAt ⟨26, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp)) T26_12
      hfix26_12 hinj26_12 hcardT26_12
      (fun i => conj_mem_of_fixedPoints _ _ (T26_12 i) (hfix26_12 i) _)
      ⟨26, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨26, by decide⟩ (Q2.listedAt ⟨26, by decide⟩
        (alnCheck_rep ⟨26, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 2 hp) Q2.T26_12_2 Q2.hfix26_12_2 Q2.hinj26_12_2
      Q2.hcardT26_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T26_12_2 i) (Q2.hfix26_12_2 i) _)
      colCert_26_12_2.hD ?_).symm
  rw [alnId_26 j hj]


theorem leaf_26_12_3 (hp : 3 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 26 []).length)
    (hq : (normIsRep.getD 26 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 3 hp)
        (rowE2 (⟨26, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp))
        (rowE1 (⟨26, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨26, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨26, by decide⟩ (listedAt ⟨26, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp)) T26_12
      hfix26_12 hinj26_12 hcardT26_12
      (fun i => conj_mem_of_fixedPoints _ _ (T26_12 i) (hfix26_12 i) _)
      ⟨26, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨26, by decide⟩ (Q2.listedAt ⟨26, by decide⟩
        (alnCheck_rep ⟨26, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 3 hp) Q2.T26_12_2 Q2.hfix26_12_2 Q2.hinj26_12_2
      Q2.hcardT26_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T26_12_2 i) (Q2.hfix26_12_2 i) _)
      colCert_26_12_3.hD ?_).symm
  rw [alnId_26 j hj]


theorem leaf_26_12_4 (hp : 4 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 26 []).length)
    (hq : (normIsRep.getD 26 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 4 hp)
        (rowE2 (⟨26, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp))
        (rowE1 (⟨26, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨26, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨26, by decide⟩ (listedAt ⟨26, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp)) T26_12
      hfix26_12 hinj26_12 hcardT26_12
      (fun i => conj_mem_of_fixedPoints _ _ (T26_12 i) (hfix26_12 i) _)
      ⟨26, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨26, by decide⟩ (Q2.listedAt ⟨26, by decide⟩
        (alnCheck_rep ⟨26, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 4 hp) Q2.T26_12_2 Q2.hfix26_12_2 Q2.hinj26_12_2
      Q2.hcardT26_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T26_12_2 i) (Q2.hfix26_12_2 i) _)
      colCert_26_12_4.hD ?_).symm
  rw [alnId_26 j hj]


theorem leaf_26_26_0 (hp : 0 < (Q2.transData.getD 26 []).length)
    (j : Nat) (hj : j < (repChars.getD 26 []).length)
    (hq : (normIsRep.getD 26 []).getD j false = true) :
    species (Q2.reps (⟨26, by decide⟩ : Fin 148)) (colE2 ⟨26, by decide⟩ 0 hp)
        (rowE2 (⟨26, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨26, by decide⟩ : Fin 148))
        (colE1 ⟨26, by decide⟩ 0 (transLenTr ⟨26, by decide⟩ 0 hp))
        (rowE1 (⟨26, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨26, by decide⟩ : Fin 148) ⟨26, by decide⟩ _
      (validAt ⟨26, by decide⟩ (listedAt ⟨26, by decide⟩ hj))
      (colE1 ⟨26, by decide⟩ 0 (transLenTr ⟨26, by decide⟩ 0 hp)) T26_26
      hfix26_26 hinj26_26 hcardT26_26
      (fun i => conj_mem_of_fixedPoints _ _ (T26_26 i) (hfix26_26 i) _)
      ⟨26, by decide⟩ ⟨26, by decide⟩ _
      (Q2.validAt ⟨26, by decide⟩ (Q2.listedAt ⟨26, by decide⟩
        (alnCheck_rep ⟨26, by decide⟩ hj hq).1))
      (colE2 ⟨26, by decide⟩ 0 hp) Q2.T26_26_2 Q2.hfix26_26_2 Q2.hinj26_26_2
      Q2.hcardT26_26_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T26_26_2 i) (Q2.hfix26_26_2 i) _)
      colCert_26_26_0.hD ?_).symm
  rw [alnId_26 j hj]


theorem leaf_26_26_1 (hp : 1 < (Q2.transData.getD 26 []).length)
    (j : Nat) (hj : j < (repChars.getD 26 []).length)
    (hq : (normIsRep.getD 26 []).getD j false = true) :
    species (Q2.reps (⟨26, by decide⟩ : Fin 148)) (colE2 ⟨26, by decide⟩ 1 hp)
        (rowE2 (⟨26, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨26, by decide⟩ : Fin 148))
        (colE1 ⟨26, by decide⟩ 1 (transLenTr ⟨26, by decide⟩ 1 hp))
        (rowE1 (⟨26, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨26, by decide⟩ : Fin 148) ⟨26, by decide⟩ _
      (validAt ⟨26, by decide⟩ (listedAt ⟨26, by decide⟩ hj))
      (colE1 ⟨26, by decide⟩ 1 (transLenTr ⟨26, by decide⟩ 1 hp)) T26_26
      hfix26_26 hinj26_26 hcardT26_26
      (fun i => conj_mem_of_fixedPoints _ _ (T26_26 i) (hfix26_26 i) _)
      ⟨26, by decide⟩ ⟨26, by decide⟩ _
      (Q2.validAt ⟨26, by decide⟩ (Q2.listedAt ⟨26, by decide⟩
        (alnCheck_rep ⟨26, by decide⟩ hj hq).1))
      (colE2 ⟨26, by decide⟩ 1 hp) Q2.T26_26_2 Q2.hfix26_26_2 Q2.hinj26_26_2
      Q2.hcardT26_26_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T26_26_2 i) (Q2.hfix26_26_2 i) _)
      colCert_26_26_1.hD ?_).symm
  rw [alnId_26 j hj]


theorem leaf_26_26_2 (hp : 2 < (Q2.transData.getD 26 []).length)
    (j : Nat) (hj : j < (repChars.getD 26 []).length)
    (hq : (normIsRep.getD 26 []).getD j false = true) :
    species (Q2.reps (⟨26, by decide⟩ : Fin 148)) (colE2 ⟨26, by decide⟩ 2 hp)
        (rowE2 (⟨26, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨26, by decide⟩ : Fin 148))
        (colE1 ⟨26, by decide⟩ 2 (transLenTr ⟨26, by decide⟩ 2 hp))
        (rowE1 (⟨26, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨26, by decide⟩ : Fin 148) ⟨26, by decide⟩ _
      (validAt ⟨26, by decide⟩ (listedAt ⟨26, by decide⟩ hj))
      (colE1 ⟨26, by decide⟩ 2 (transLenTr ⟨26, by decide⟩ 2 hp)) T26_26
      hfix26_26 hinj26_26 hcardT26_26
      (fun i => conj_mem_of_fixedPoints _ _ (T26_26 i) (hfix26_26 i) _)
      ⟨26, by decide⟩ ⟨26, by decide⟩ _
      (Q2.validAt ⟨26, by decide⟩ (Q2.listedAt ⟨26, by decide⟩
        (alnCheck_rep ⟨26, by decide⟩ hj hq).1))
      (colE2 ⟨26, by decide⟩ 2 hp) Q2.T26_26_2 Q2.hfix26_26_2 Q2.hinj26_26_2
      Q2.hcardT26_26_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T26_26_2 i) (Q2.hfix26_26_2 i) _)
      colCert_26_26_2.hD ?_).symm
  rw [alnId_26 j hj]


theorem leaf_26_26_3 (hp : 3 < (Q2.transData.getD 26 []).length)
    (j : Nat) (hj : j < (repChars.getD 26 []).length)
    (hq : (normIsRep.getD 26 []).getD j false = true) :
    species (Q2.reps (⟨26, by decide⟩ : Fin 148)) (colE2 ⟨26, by decide⟩ 3 hp)
        (rowE2 (⟨26, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨26, by decide⟩ : Fin 148))
        (colE1 ⟨26, by decide⟩ 3 (transLenTr ⟨26, by decide⟩ 3 hp))
        (rowE1 (⟨26, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨26, by decide⟩ : Fin 148) ⟨26, by decide⟩ _
      (validAt ⟨26, by decide⟩ (listedAt ⟨26, by decide⟩ hj))
      (colE1 ⟨26, by decide⟩ 3 (transLenTr ⟨26, by decide⟩ 3 hp)) T26_26
      hfix26_26 hinj26_26 hcardT26_26
      (fun i => conj_mem_of_fixedPoints _ _ (T26_26 i) (hfix26_26 i) _)
      ⟨26, by decide⟩ ⟨26, by decide⟩ _
      (Q2.validAt ⟨26, by decide⟩ (Q2.listedAt ⟨26, by decide⟩
        (alnCheck_rep ⟨26, by decide⟩ hj hq).1))
      (colE2 ⟨26, by decide⟩ 3 hp) Q2.T26_26_2 Q2.hfix26_26_2 Q2.hinj26_26_2
      Q2.hcardT26_26_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T26_26_2 i) (Q2.hfix26_26_2 i) _)
      colCert_26_26_3.hD ?_).symm
  rw [alnId_26 j hj]


theorem leaf_26_26_4 (hp : 4 < (Q2.transData.getD 26 []).length)
    (j : Nat) (hj : j < (repChars.getD 26 []).length)
    (hq : (normIsRep.getD 26 []).getD j false = true) :
    species (Q2.reps (⟨26, by decide⟩ : Fin 148)) (colE2 ⟨26, by decide⟩ 4 hp)
        (rowE2 (⟨26, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨26, by decide⟩ : Fin 148))
        (colE1 ⟨26, by decide⟩ 4 (transLenTr ⟨26, by decide⟩ 4 hp))
        (rowE1 (⟨26, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨26, by decide⟩ : Fin 148) ⟨26, by decide⟩ _
      (validAt ⟨26, by decide⟩ (listedAt ⟨26, by decide⟩ hj))
      (colE1 ⟨26, by decide⟩ 4 (transLenTr ⟨26, by decide⟩ 4 hp)) T26_26
      hfix26_26 hinj26_26 hcardT26_26
      (fun i => conj_mem_of_fixedPoints _ _ (T26_26 i) (hfix26_26 i) _)
      ⟨26, by decide⟩ ⟨26, by decide⟩ _
      (Q2.validAt ⟨26, by decide⟩ (Q2.listedAt ⟨26, by decide⟩
        (alnCheck_rep ⟨26, by decide⟩ hj hq).1))
      (colE2 ⟨26, by decide⟩ 4 hp) Q2.T26_26_2 Q2.hfix26_26_2 Q2.hinj26_26_2
      Q2.hcardT26_26_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T26_26_2 i) (Q2.hfix26_26_2 i) _)
      colCert_26_26_4.hD ?_).symm
  rw [alnId_26 j hj]


theorem leaf_26_26_5 (hp : 5 < (Q2.transData.getD 26 []).length)
    (j : Nat) (hj : j < (repChars.getD 26 []).length)
    (hq : (normIsRep.getD 26 []).getD j false = true) :
    species (Q2.reps (⟨26, by decide⟩ : Fin 148)) (colE2 ⟨26, by decide⟩ 5 hp)
        (rowE2 (⟨26, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨26, by decide⟩ : Fin 148))
        (colE1 ⟨26, by decide⟩ 5 (transLenTr ⟨26, by decide⟩ 5 hp))
        (rowE1 (⟨26, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨26, by decide⟩ : Fin 148) ⟨26, by decide⟩ _
      (validAt ⟨26, by decide⟩ (listedAt ⟨26, by decide⟩ hj))
      (colE1 ⟨26, by decide⟩ 5 (transLenTr ⟨26, by decide⟩ 5 hp)) T26_26
      hfix26_26 hinj26_26 hcardT26_26
      (fun i => conj_mem_of_fixedPoints _ _ (T26_26 i) (hfix26_26 i) _)
      ⟨26, by decide⟩ ⟨26, by decide⟩ _
      (Q2.validAt ⟨26, by decide⟩ (Q2.listedAt ⟨26, by decide⟩
        (alnCheck_rep ⟨26, by decide⟩ hj hq).1))
      (colE2 ⟨26, by decide⟩ 5 hp) Q2.T26_26_2 Q2.hfix26_26_2 Q2.hinj26_26_2
      Q2.hcardT26_26_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T26_26_2 i) (Q2.hfix26_26_2 i) _)
      colCert_26_26_5.hD ?_).symm
  rw [alnId_26 j hj]


theorem leaf_26_26_10 (hp : 10 < (Q2.transData.getD 26 []).length)
    (j : Nat) (hj : j < (repChars.getD 26 []).length)
    (hq : (normIsRep.getD 26 []).getD j false = true) :
    species (Q2.reps (⟨26, by decide⟩ : Fin 148)) (colE2 ⟨26, by decide⟩ 10 hp)
        (rowE2 (⟨26, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨26, by decide⟩ : Fin 148))
        (colE1 ⟨26, by decide⟩ 10 (transLenTr ⟨26, by decide⟩ 10 hp))
        (rowE1 (⟨26, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨26, by decide⟩ : Fin 148) ⟨26, by decide⟩ _
      (validAt ⟨26, by decide⟩ (listedAt ⟨26, by decide⟩ hj))
      (colE1 ⟨26, by decide⟩ 10 (transLenTr ⟨26, by decide⟩ 10 hp)) T26_26
      hfix26_26 hinj26_26 hcardT26_26
      (fun i => conj_mem_of_fixedPoints _ _ (T26_26 i) (hfix26_26 i) _)
      ⟨26, by decide⟩ ⟨26, by decide⟩ _
      (Q2.validAt ⟨26, by decide⟩ (Q2.listedAt ⟨26, by decide⟩
        (alnCheck_rep ⟨26, by decide⟩ hj hq).1))
      (colE2 ⟨26, by decide⟩ 10 hp) Q2.T26_26_2 Q2.hfix26_26_2 Q2.hinj26_26_2
      Q2.hcardT26_26_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T26_26_2 i) (Q2.hfix26_26_2 i) _)
      colCert_26_26_10.hD ?_).symm
  rw [alnId_26 j hj]


theorem leaf_26_26_15 (hp : 15 < (Q2.transData.getD 26 []).length)
    (j : Nat) (hj : j < (repChars.getD 26 []).length)
    (hq : (normIsRep.getD 26 []).getD j false = true) :
    species (Q2.reps (⟨26, by decide⟩ : Fin 148)) (colE2 ⟨26, by decide⟩ 15 hp)
        (rowE2 (⟨26, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨26, by decide⟩ : Fin 148))
        (colE1 ⟨26, by decide⟩ 15 (transLenTr ⟨26, by decide⟩ 15 hp))
        (rowE1 (⟨26, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨26, by decide⟩ : Fin 148) ⟨26, by decide⟩ _
      (validAt ⟨26, by decide⟩ (listedAt ⟨26, by decide⟩ hj))
      (colE1 ⟨26, by decide⟩ 15 (transLenTr ⟨26, by decide⟩ 15 hp)) T26_26
      hfix26_26 hinj26_26 hcardT26_26
      (fun i => conj_mem_of_fixedPoints _ _ (T26_26 i) (hfix26_26 i) _)
      ⟨26, by decide⟩ ⟨26, by decide⟩ _
      (Q2.validAt ⟨26, by decide⟩ (Q2.listedAt ⟨26, by decide⟩
        (alnCheck_rep ⟨26, by decide⟩ hj hq).1))
      (colE2 ⟨26, by decide⟩ 15 hp) Q2.T26_26_2 Q2.hfix26_26_2 Q2.hinj26_26_2
      Q2.hcardT26_26_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T26_26_2 i) (Q2.hfix26_26_2 i) _)
      colCert_26_26_15.hD ?_).symm
  rw [alnId_26 j hj]


theorem leaf_26_26_20 (hp : 20 < (Q2.transData.getD 26 []).length)
    (j : Nat) (hj : j < (repChars.getD 26 []).length)
    (hq : (normIsRep.getD 26 []).getD j false = true) :
    species (Q2.reps (⟨26, by decide⟩ : Fin 148)) (colE2 ⟨26, by decide⟩ 20 hp)
        (rowE2 (⟨26, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨26, by decide⟩ : Fin 148))
        (colE1 ⟨26, by decide⟩ 20 (transLenTr ⟨26, by decide⟩ 20 hp))
        (rowE1 (⟨26, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨26, by decide⟩ : Fin 148) ⟨26, by decide⟩ _
      (validAt ⟨26, by decide⟩ (listedAt ⟨26, by decide⟩ hj))
      (colE1 ⟨26, by decide⟩ 20 (transLenTr ⟨26, by decide⟩ 20 hp)) T26_26
      hfix26_26 hinj26_26 hcardT26_26
      (fun i => conj_mem_of_fixedPoints _ _ (T26_26 i) (hfix26_26 i) _)
      ⟨26, by decide⟩ ⟨26, by decide⟩ _
      (Q2.validAt ⟨26, by decide⟩ (Q2.listedAt ⟨26, by decide⟩
        (alnCheck_rep ⟨26, by decide⟩ hj hq).1))
      (colE2 ⟨26, by decide⟩ 20 hp) Q2.T26_26_2 Q2.hfix26_26_2 Q2.hinj26_26_2
      Q2.hcardT26_26_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T26_26_2 i) (Q2.hfix26_26_2 i) _)
      colCert_26_26_20.hD ?_).symm
  rw [alnId_26 j hj]


theorem leaf_27_9_0 (hp : 0 < (Q2.transData.getD 9 []).length)
    (j : Nat) (hj : j < (repChars.getD 27 []).length)
    (hq : (normIsRep.getD 27 []).getD j false = true) :
    species (Q2.reps (⟨9, by decide⟩ : Fin 148)) (colE2 ⟨9, by decide⟩ 0 hp)
        (rowE2 (⟨27, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨9, by decide⟩ : Fin 148))
        (colE1 ⟨9, by decide⟩ 0 (transLenTr ⟨9, by decide⟩ 0 hp))
        (rowE1 (⟨27, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨27, by decide⟩ : Fin 148) ⟨9, by decide⟩ _
      (validAt ⟨27, by decide⟩ (listedAt ⟨27, by decide⟩ hj))
      (colE1 ⟨9, by decide⟩ 0 (transLenTr ⟨9, by decide⟩ 0 hp)) T27_9
      hfix27_9 hinj27_9 hcardT27_9
      (fun i => conj_mem_of_fixedPoints _ _ (T27_9 i) (hfix27_9 i) _)
      ⟨27, by decide⟩ ⟨9, by decide⟩ _
      (Q2.validAt ⟨27, by decide⟩ (Q2.listedAt ⟨27, by decide⟩
        (alnCheck_rep ⟨27, by decide⟩ hj hq).1))
      (colE2 ⟨9, by decide⟩ 0 hp) Q2.T27_9_2 Q2.hfix27_9_2 Q2.hinj27_9_2
      Q2.hcardT27_9_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T27_9_2 i) (Q2.hfix27_9_2 i) _)
      colCert_27_9_0.hD ?_).symm
  rw [alnId_27 j hj]


theorem leaf_27_9_1 (hp : 1 < (Q2.transData.getD 9 []).length)
    (j : Nat) (hj : j < (repChars.getD 27 []).length)
    (hq : (normIsRep.getD 27 []).getD j false = true) :
    species (Q2.reps (⟨9, by decide⟩ : Fin 148)) (colE2 ⟨9, by decide⟩ 1 hp)
        (rowE2 (⟨27, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨9, by decide⟩ : Fin 148))
        (colE1 ⟨9, by decide⟩ 1 (transLenTr ⟨9, by decide⟩ 1 hp))
        (rowE1 (⟨27, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨27, by decide⟩ : Fin 148) ⟨9, by decide⟩ _
      (validAt ⟨27, by decide⟩ (listedAt ⟨27, by decide⟩ hj))
      (colE1 ⟨9, by decide⟩ 1 (transLenTr ⟨9, by decide⟩ 1 hp)) T27_9
      hfix27_9 hinj27_9 hcardT27_9
      (fun i => conj_mem_of_fixedPoints _ _ (T27_9 i) (hfix27_9 i) _)
      ⟨27, by decide⟩ ⟨9, by decide⟩ _
      (Q2.validAt ⟨27, by decide⟩ (Q2.listedAt ⟨27, by decide⟩
        (alnCheck_rep ⟨27, by decide⟩ hj hq).1))
      (colE2 ⟨9, by decide⟩ 1 hp) Q2.T27_9_2 Q2.hfix27_9_2 Q2.hinj27_9_2
      Q2.hcardT27_9_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T27_9_2 i) (Q2.hfix27_9_2 i) _)
      colCert_27_9_1.hD ?_).symm
  rw [alnId_27 j hj]


theorem leaf_27_9_2 (hp : 2 < (Q2.transData.getD 9 []).length)
    (j : Nat) (hj : j < (repChars.getD 27 []).length)
    (hq : (normIsRep.getD 27 []).getD j false = true) :
    species (Q2.reps (⟨9, by decide⟩ : Fin 148)) (colE2 ⟨9, by decide⟩ 2 hp)
        (rowE2 (⟨27, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨9, by decide⟩ : Fin 148))
        (colE1 ⟨9, by decide⟩ 2 (transLenTr ⟨9, by decide⟩ 2 hp))
        (rowE1 (⟨27, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨27, by decide⟩ : Fin 148) ⟨9, by decide⟩ _
      (validAt ⟨27, by decide⟩ (listedAt ⟨27, by decide⟩ hj))
      (colE1 ⟨9, by decide⟩ 2 (transLenTr ⟨9, by decide⟩ 2 hp)) T27_9
      hfix27_9 hinj27_9 hcardT27_9
      (fun i => conj_mem_of_fixedPoints _ _ (T27_9 i) (hfix27_9 i) _)
      ⟨27, by decide⟩ ⟨9, by decide⟩ _
      (Q2.validAt ⟨27, by decide⟩ (Q2.listedAt ⟨27, by decide⟩
        (alnCheck_rep ⟨27, by decide⟩ hj hq).1))
      (colE2 ⟨9, by decide⟩ 2 hp) Q2.T27_9_2 Q2.hfix27_9_2 Q2.hinj27_9_2
      Q2.hcardT27_9_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T27_9_2 i) (Q2.hfix27_9_2 i) _)
      colCert_27_9_2.hD ?_).symm
  rw [alnId_27 j hj]


theorem leaf_27_9_3 (hp : 3 < (Q2.transData.getD 9 []).length)
    (j : Nat) (hj : j < (repChars.getD 27 []).length)
    (hq : (normIsRep.getD 27 []).getD j false = true) :
    species (Q2.reps (⟨9, by decide⟩ : Fin 148)) (colE2 ⟨9, by decide⟩ 3 hp)
        (rowE2 (⟨27, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨9, by decide⟩ : Fin 148))
        (colE1 ⟨9, by decide⟩ 3 (transLenTr ⟨9, by decide⟩ 3 hp))
        (rowE1 (⟨27, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨27, by decide⟩ : Fin 148) ⟨9, by decide⟩ _
      (validAt ⟨27, by decide⟩ (listedAt ⟨27, by decide⟩ hj))
      (colE1 ⟨9, by decide⟩ 3 (transLenTr ⟨9, by decide⟩ 3 hp)) T27_9
      hfix27_9 hinj27_9 hcardT27_9
      (fun i => conj_mem_of_fixedPoints _ _ (T27_9 i) (hfix27_9 i) _)
      ⟨27, by decide⟩ ⟨9, by decide⟩ _
      (Q2.validAt ⟨27, by decide⟩ (Q2.listedAt ⟨27, by decide⟩
        (alnCheck_rep ⟨27, by decide⟩ hj hq).1))
      (colE2 ⟨9, by decide⟩ 3 hp) Q2.T27_9_2 Q2.hfix27_9_2 Q2.hinj27_9_2
      Q2.hcardT27_9_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T27_9_2 i) (Q2.hfix27_9_2 i) _)
      colCert_27_9_3.hD ?_).symm
  rw [alnId_27 j hj]


theorem leaf_27_9_4 (hp : 4 < (Q2.transData.getD 9 []).length)
    (j : Nat) (hj : j < (repChars.getD 27 []).length)
    (hq : (normIsRep.getD 27 []).getD j false = true) :
    species (Q2.reps (⟨9, by decide⟩ : Fin 148)) (colE2 ⟨9, by decide⟩ 4 hp)
        (rowE2 (⟨27, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨9, by decide⟩ : Fin 148))
        (colE1 ⟨9, by decide⟩ 4 (transLenTr ⟨9, by decide⟩ 4 hp))
        (rowE1 (⟨27, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨27, by decide⟩ : Fin 148) ⟨9, by decide⟩ _
      (validAt ⟨27, by decide⟩ (listedAt ⟨27, by decide⟩ hj))
      (colE1 ⟨9, by decide⟩ 4 (transLenTr ⟨9, by decide⟩ 4 hp)) T27_9
      hfix27_9 hinj27_9 hcardT27_9
      (fun i => conj_mem_of_fixedPoints _ _ (T27_9 i) (hfix27_9 i) _)
      ⟨27, by decide⟩ ⟨9, by decide⟩ _
      (Q2.validAt ⟨27, by decide⟩ (Q2.listedAt ⟨27, by decide⟩
        (alnCheck_rep ⟨27, by decide⟩ hj hq).1))
      (colE2 ⟨9, by decide⟩ 4 hp) Q2.T27_9_2 Q2.hfix27_9_2 Q2.hinj27_9_2
      Q2.hcardT27_9_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T27_9_2 i) (Q2.hfix27_9_2 i) _)
      colCert_27_9_4.hD ?_).symm
  rw [alnId_27 j hj]


theorem leaf_27_12_0 (hp : 0 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 27 []).length)
    (hq : (normIsRep.getD 27 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 0 hp)
        (rowE2 (⟨27, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp))
        (rowE1 (⟨27, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨27, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨27, by decide⟩ (listedAt ⟨27, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp)) T27_12
      hfix27_12 hinj27_12 hcardT27_12
      (fun i => conj_mem_of_fixedPoints _ _ (T27_12 i) (hfix27_12 i) _)
      ⟨27, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨27, by decide⟩ (Q2.listedAt ⟨27, by decide⟩
        (alnCheck_rep ⟨27, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 0 hp) Q2.T27_12_2 Q2.hfix27_12_2 Q2.hinj27_12_2
      Q2.hcardT27_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T27_12_2 i) (Q2.hfix27_12_2 i) _)
      colCert_27_12_0.hD ?_).symm
  rw [alnId_27 j hj]


theorem leaf_27_12_1 (hp : 1 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 27 []).length)
    (hq : (normIsRep.getD 27 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 1 hp)
        (rowE2 (⟨27, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp))
        (rowE1 (⟨27, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨27, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨27, by decide⟩ (listedAt ⟨27, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp)) T27_12
      hfix27_12 hinj27_12 hcardT27_12
      (fun i => conj_mem_of_fixedPoints _ _ (T27_12 i) (hfix27_12 i) _)
      ⟨27, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨27, by decide⟩ (Q2.listedAt ⟨27, by decide⟩
        (alnCheck_rep ⟨27, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 1 hp) Q2.T27_12_2 Q2.hfix27_12_2 Q2.hinj27_12_2
      Q2.hcardT27_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T27_12_2 i) (Q2.hfix27_12_2 i) _)
      colCert_27_12_1.hD ?_).symm
  rw [alnId_27 j hj]


theorem leaf_27_12_2 (hp : 2 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 27 []).length)
    (hq : (normIsRep.getD 27 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 2 hp)
        (rowE2 (⟨27, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp))
        (rowE1 (⟨27, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨27, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨27, by decide⟩ (listedAt ⟨27, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp)) T27_12
      hfix27_12 hinj27_12 hcardT27_12
      (fun i => conj_mem_of_fixedPoints _ _ (T27_12 i) (hfix27_12 i) _)
      ⟨27, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨27, by decide⟩ (Q2.listedAt ⟨27, by decide⟩
        (alnCheck_rep ⟨27, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 2 hp) Q2.T27_12_2 Q2.hfix27_12_2 Q2.hinj27_12_2
      Q2.hcardT27_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T27_12_2 i) (Q2.hfix27_12_2 i) _)
      colCert_27_12_2.hD ?_).symm
  rw [alnId_27 j hj]


theorem leaf_27_12_3 (hp : 3 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 27 []).length)
    (hq : (normIsRep.getD 27 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 3 hp)
        (rowE2 (⟨27, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp))
        (rowE1 (⟨27, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨27, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨27, by decide⟩ (listedAt ⟨27, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp)) T27_12
      hfix27_12 hinj27_12 hcardT27_12
      (fun i => conj_mem_of_fixedPoints _ _ (T27_12 i) (hfix27_12 i) _)
      ⟨27, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨27, by decide⟩ (Q2.listedAt ⟨27, by decide⟩
        (alnCheck_rep ⟨27, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 3 hp) Q2.T27_12_2 Q2.hfix27_12_2 Q2.hinj27_12_2
      Q2.hcardT27_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T27_12_2 i) (Q2.hfix27_12_2 i) _)
      colCert_27_12_3.hD ?_).symm
  rw [alnId_27 j hj]


theorem leaf_27_12_4 (hp : 4 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 27 []).length)
    (hq : (normIsRep.getD 27 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 4 hp)
        (rowE2 (⟨27, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp))
        (rowE1 (⟨27, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨27, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨27, by decide⟩ (listedAt ⟨27, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp)) T27_12
      hfix27_12 hinj27_12 hcardT27_12
      (fun i => conj_mem_of_fixedPoints _ _ (T27_12 i) (hfix27_12 i) _)
      ⟨27, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨27, by decide⟩ (Q2.listedAt ⟨27, by decide⟩
        (alnCheck_rep ⟨27, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 4 hp) Q2.T27_12_2 Q2.hfix27_12_2 Q2.hinj27_12_2
      Q2.hcardT27_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T27_12_2 i) (Q2.hfix27_12_2 i) _)
      colCert_27_12_4.hD ?_).symm
  rw [alnId_27 j hj]


theorem leaf_27_27_0 (hp : 0 < (Q2.transData.getD 27 []).length)
    (j : Nat) (hj : j < (repChars.getD 27 []).length)
    (hq : (normIsRep.getD 27 []).getD j false = true) :
    species (Q2.reps (⟨27, by decide⟩ : Fin 148)) (colE2 ⟨27, by decide⟩ 0 hp)
        (rowE2 (⟨27, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨27, by decide⟩ : Fin 148))
        (colE1 ⟨27, by decide⟩ 0 (transLenTr ⟨27, by decide⟩ 0 hp))
        (rowE1 (⟨27, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨27, by decide⟩ : Fin 148) ⟨27, by decide⟩ _
      (validAt ⟨27, by decide⟩ (listedAt ⟨27, by decide⟩ hj))
      (colE1 ⟨27, by decide⟩ 0 (transLenTr ⟨27, by decide⟩ 0 hp)) T27_27
      hfix27_27 hinj27_27 hcardT27_27
      (fun i => conj_mem_of_fixedPoints _ _ (T27_27 i) (hfix27_27 i) _)
      ⟨27, by decide⟩ ⟨27, by decide⟩ _
      (Q2.validAt ⟨27, by decide⟩ (Q2.listedAt ⟨27, by decide⟩
        (alnCheck_rep ⟨27, by decide⟩ hj hq).1))
      (colE2 ⟨27, by decide⟩ 0 hp) Q2.T27_27_2 Q2.hfix27_27_2 Q2.hinj27_27_2
      Q2.hcardT27_27_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T27_27_2 i) (Q2.hfix27_27_2 i) _)
      colCert_27_27_0.hD ?_).symm
  rw [alnId_27 j hj]


theorem leaf_27_27_1 (hp : 1 < (Q2.transData.getD 27 []).length)
    (j : Nat) (hj : j < (repChars.getD 27 []).length)
    (hq : (normIsRep.getD 27 []).getD j false = true) :
    species (Q2.reps (⟨27, by decide⟩ : Fin 148)) (colE2 ⟨27, by decide⟩ 1 hp)
        (rowE2 (⟨27, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨27, by decide⟩ : Fin 148))
        (colE1 ⟨27, by decide⟩ 1 (transLenTr ⟨27, by decide⟩ 1 hp))
        (rowE1 (⟨27, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨27, by decide⟩ : Fin 148) ⟨27, by decide⟩ _
      (validAt ⟨27, by decide⟩ (listedAt ⟨27, by decide⟩ hj))
      (colE1 ⟨27, by decide⟩ 1 (transLenTr ⟨27, by decide⟩ 1 hp)) T27_27
      hfix27_27 hinj27_27 hcardT27_27
      (fun i => conj_mem_of_fixedPoints _ _ (T27_27 i) (hfix27_27 i) _)
      ⟨27, by decide⟩ ⟨27, by decide⟩ _
      (Q2.validAt ⟨27, by decide⟩ (Q2.listedAt ⟨27, by decide⟩
        (alnCheck_rep ⟨27, by decide⟩ hj hq).1))
      (colE2 ⟨27, by decide⟩ 1 hp) Q2.T27_27_2 Q2.hfix27_27_2 Q2.hinj27_27_2
      Q2.hcardT27_27_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T27_27_2 i) (Q2.hfix27_27_2 i) _)
      colCert_27_27_1.hD ?_).symm
  rw [alnId_27 j hj]


theorem leaf_27_27_2 (hp : 2 < (Q2.transData.getD 27 []).length)
    (j : Nat) (hj : j < (repChars.getD 27 []).length)
    (hq : (normIsRep.getD 27 []).getD j false = true) :
    species (Q2.reps (⟨27, by decide⟩ : Fin 148)) (colE2 ⟨27, by decide⟩ 2 hp)
        (rowE2 (⟨27, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨27, by decide⟩ : Fin 148))
        (colE1 ⟨27, by decide⟩ 2 (transLenTr ⟨27, by decide⟩ 2 hp))
        (rowE1 (⟨27, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨27, by decide⟩ : Fin 148) ⟨27, by decide⟩ _
      (validAt ⟨27, by decide⟩ (listedAt ⟨27, by decide⟩ hj))
      (colE1 ⟨27, by decide⟩ 2 (transLenTr ⟨27, by decide⟩ 2 hp)) T27_27
      hfix27_27 hinj27_27 hcardT27_27
      (fun i => conj_mem_of_fixedPoints _ _ (T27_27 i) (hfix27_27 i) _)
      ⟨27, by decide⟩ ⟨27, by decide⟩ _
      (Q2.validAt ⟨27, by decide⟩ (Q2.listedAt ⟨27, by decide⟩
        (alnCheck_rep ⟨27, by decide⟩ hj hq).1))
      (colE2 ⟨27, by decide⟩ 2 hp) Q2.T27_27_2 Q2.hfix27_27_2 Q2.hinj27_27_2
      Q2.hcardT27_27_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T27_27_2 i) (Q2.hfix27_27_2 i) _)
      colCert_27_27_2.hD ?_).symm
  rw [alnId_27 j hj]


theorem leaf_27_27_3 (hp : 3 < (Q2.transData.getD 27 []).length)
    (j : Nat) (hj : j < (repChars.getD 27 []).length)
    (hq : (normIsRep.getD 27 []).getD j false = true) :
    species (Q2.reps (⟨27, by decide⟩ : Fin 148)) (colE2 ⟨27, by decide⟩ 3 hp)
        (rowE2 (⟨27, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨27, by decide⟩ : Fin 148))
        (colE1 ⟨27, by decide⟩ 3 (transLenTr ⟨27, by decide⟩ 3 hp))
        (rowE1 (⟨27, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨27, by decide⟩ : Fin 148) ⟨27, by decide⟩ _
      (validAt ⟨27, by decide⟩ (listedAt ⟨27, by decide⟩ hj))
      (colE1 ⟨27, by decide⟩ 3 (transLenTr ⟨27, by decide⟩ 3 hp)) T27_27
      hfix27_27 hinj27_27 hcardT27_27
      (fun i => conj_mem_of_fixedPoints _ _ (T27_27 i) (hfix27_27 i) _)
      ⟨27, by decide⟩ ⟨27, by decide⟩ _
      (Q2.validAt ⟨27, by decide⟩ (Q2.listedAt ⟨27, by decide⟩
        (alnCheck_rep ⟨27, by decide⟩ hj hq).1))
      (colE2 ⟨27, by decide⟩ 3 hp) Q2.T27_27_2 Q2.hfix27_27_2 Q2.hinj27_27_2
      Q2.hcardT27_27_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T27_27_2 i) (Q2.hfix27_27_2 i) _)
      colCert_27_27_3.hD ?_).symm
  rw [alnId_27 j hj]


theorem leaf_27_27_4 (hp : 4 < (Q2.transData.getD 27 []).length)
    (j : Nat) (hj : j < (repChars.getD 27 []).length)
    (hq : (normIsRep.getD 27 []).getD j false = true) :
    species (Q2.reps (⟨27, by decide⟩ : Fin 148)) (colE2 ⟨27, by decide⟩ 4 hp)
        (rowE2 (⟨27, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨27, by decide⟩ : Fin 148))
        (colE1 ⟨27, by decide⟩ 4 (transLenTr ⟨27, by decide⟩ 4 hp))
        (rowE1 (⟨27, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨27, by decide⟩ : Fin 148) ⟨27, by decide⟩ _
      (validAt ⟨27, by decide⟩ (listedAt ⟨27, by decide⟩ hj))
      (colE1 ⟨27, by decide⟩ 4 (transLenTr ⟨27, by decide⟩ 4 hp)) T27_27
      hfix27_27 hinj27_27 hcardT27_27
      (fun i => conj_mem_of_fixedPoints _ _ (T27_27 i) (hfix27_27 i) _)
      ⟨27, by decide⟩ ⟨27, by decide⟩ _
      (Q2.validAt ⟨27, by decide⟩ (Q2.listedAt ⟨27, by decide⟩
        (alnCheck_rep ⟨27, by decide⟩ hj hq).1))
      (colE2 ⟨27, by decide⟩ 4 hp) Q2.T27_27_2 Q2.hfix27_27_2 Q2.hinj27_27_2
      Q2.hcardT27_27_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T27_27_2 i) (Q2.hfix27_27_2 i) _)
      colCert_27_27_4.hD ?_).symm
  rw [alnId_27 j hj]


theorem leaf_27_27_5 (hp : 5 < (Q2.transData.getD 27 []).length)
    (j : Nat) (hj : j < (repChars.getD 27 []).length)
    (hq : (normIsRep.getD 27 []).getD j false = true) :
    species (Q2.reps (⟨27, by decide⟩ : Fin 148)) (colE2 ⟨27, by decide⟩ 5 hp)
        (rowE2 (⟨27, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨27, by decide⟩ : Fin 148))
        (colE1 ⟨27, by decide⟩ 5 (transLenTr ⟨27, by decide⟩ 5 hp))
        (rowE1 (⟨27, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨27, by decide⟩ : Fin 148) ⟨27, by decide⟩ _
      (validAt ⟨27, by decide⟩ (listedAt ⟨27, by decide⟩ hj))
      (colE1 ⟨27, by decide⟩ 5 (transLenTr ⟨27, by decide⟩ 5 hp)) T27_27
      hfix27_27 hinj27_27 hcardT27_27
      (fun i => conj_mem_of_fixedPoints _ _ (T27_27 i) (hfix27_27 i) _)
      ⟨27, by decide⟩ ⟨27, by decide⟩ _
      (Q2.validAt ⟨27, by decide⟩ (Q2.listedAt ⟨27, by decide⟩
        (alnCheck_rep ⟨27, by decide⟩ hj hq).1))
      (colE2 ⟨27, by decide⟩ 5 hp) Q2.T27_27_2 Q2.hfix27_27_2 Q2.hinj27_27_2
      Q2.hcardT27_27_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T27_27_2 i) (Q2.hfix27_27_2 i) _)
      colCert_27_27_5.hD ?_).symm
  rw [alnId_27 j hj]


theorem leaf_27_27_10 (hp : 10 < (Q2.transData.getD 27 []).length)
    (j : Nat) (hj : j < (repChars.getD 27 []).length)
    (hq : (normIsRep.getD 27 []).getD j false = true) :
    species (Q2.reps (⟨27, by decide⟩ : Fin 148)) (colE2 ⟨27, by decide⟩ 10 hp)
        (rowE2 (⟨27, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨27, by decide⟩ : Fin 148))
        (colE1 ⟨27, by decide⟩ 10 (transLenTr ⟨27, by decide⟩ 10 hp))
        (rowE1 (⟨27, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨27, by decide⟩ : Fin 148) ⟨27, by decide⟩ _
      (validAt ⟨27, by decide⟩ (listedAt ⟨27, by decide⟩ hj))
      (colE1 ⟨27, by decide⟩ 10 (transLenTr ⟨27, by decide⟩ 10 hp)) T27_27
      hfix27_27 hinj27_27 hcardT27_27
      (fun i => conj_mem_of_fixedPoints _ _ (T27_27 i) (hfix27_27 i) _)
      ⟨27, by decide⟩ ⟨27, by decide⟩ _
      (Q2.validAt ⟨27, by decide⟩ (Q2.listedAt ⟨27, by decide⟩
        (alnCheck_rep ⟨27, by decide⟩ hj hq).1))
      (colE2 ⟨27, by decide⟩ 10 hp) Q2.T27_27_2 Q2.hfix27_27_2 Q2.hinj27_27_2
      Q2.hcardT27_27_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T27_27_2 i) (Q2.hfix27_27_2 i) _)
      colCert_27_27_10.hD ?_).symm
  rw [alnId_27 j hj]


theorem leaf_27_27_15 (hp : 15 < (Q2.transData.getD 27 []).length)
    (j : Nat) (hj : j < (repChars.getD 27 []).length)
    (hq : (normIsRep.getD 27 []).getD j false = true) :
    species (Q2.reps (⟨27, by decide⟩ : Fin 148)) (colE2 ⟨27, by decide⟩ 15 hp)
        (rowE2 (⟨27, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨27, by decide⟩ : Fin 148))
        (colE1 ⟨27, by decide⟩ 15 (transLenTr ⟨27, by decide⟩ 15 hp))
        (rowE1 (⟨27, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨27, by decide⟩ : Fin 148) ⟨27, by decide⟩ _
      (validAt ⟨27, by decide⟩ (listedAt ⟨27, by decide⟩ hj))
      (colE1 ⟨27, by decide⟩ 15 (transLenTr ⟨27, by decide⟩ 15 hp)) T27_27
      hfix27_27 hinj27_27 hcardT27_27
      (fun i => conj_mem_of_fixedPoints _ _ (T27_27 i) (hfix27_27 i) _)
      ⟨27, by decide⟩ ⟨27, by decide⟩ _
      (Q2.validAt ⟨27, by decide⟩ (Q2.listedAt ⟨27, by decide⟩
        (alnCheck_rep ⟨27, by decide⟩ hj hq).1))
      (colE2 ⟨27, by decide⟩ 15 hp) Q2.T27_27_2 Q2.hfix27_27_2 Q2.hinj27_27_2
      Q2.hcardT27_27_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T27_27_2 i) (Q2.hfix27_27_2 i) _)
      colCert_27_27_15.hD ?_).symm
  rw [alnId_27 j hj]


theorem leaf_27_27_20 (hp : 20 < (Q2.transData.getD 27 []).length)
    (j : Nat) (hj : j < (repChars.getD 27 []).length)
    (hq : (normIsRep.getD 27 []).getD j false = true) :
    species (Q2.reps (⟨27, by decide⟩ : Fin 148)) (colE2 ⟨27, by decide⟩ 20 hp)
        (rowE2 (⟨27, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨27, by decide⟩ : Fin 148))
        (colE1 ⟨27, by decide⟩ 20 (transLenTr ⟨27, by decide⟩ 20 hp))
        (rowE1 (⟨27, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨27, by decide⟩ : Fin 148) ⟨27, by decide⟩ _
      (validAt ⟨27, by decide⟩ (listedAt ⟨27, by decide⟩ hj))
      (colE1 ⟨27, by decide⟩ 20 (transLenTr ⟨27, by decide⟩ 20 hp)) T27_27
      hfix27_27 hinj27_27 hcardT27_27
      (fun i => conj_mem_of_fixedPoints _ _ (T27_27 i) (hfix27_27 i) _)
      ⟨27, by decide⟩ ⟨27, by decide⟩ _
      (Q2.validAt ⟨27, by decide⟩ (Q2.listedAt ⟨27, by decide⟩
        (alnCheck_rep ⟨27, by decide⟩ hj hq).1))
      (colE2 ⟨27, by decide⟩ 20 hp) Q2.T27_27_2 Q2.hfix27_27_2 Q2.hinj27_27_2
      Q2.hcardT27_27_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T27_27_2 i) (Q2.hfix27_27_2 i) _)
      colCert_27_27_20.hD ?_).symm
  rw [alnId_27 j hj]


theorem leaf_28_12_0 (hp : 0 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 28 []).length)
    (hq : (normIsRep.getD 28 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 0 hp)
        (rowE2 (⟨28, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp))
        (rowE1 (⟨28, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨28, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨28, by decide⟩ (listedAt ⟨28, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp)) T28_12
      hfix28_12 hinj28_12 hcardT28_12
      (fun i => conj_mem_of_fixedPoints _ _ (T28_12 i) (hfix28_12 i) _)
      ⟨28, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨28, by decide⟩ (Q2.listedAt ⟨28, by decide⟩
        (alnCheck_rep ⟨28, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 0 hp) Q2.T28_12_2 Q2.hfix28_12_2 Q2.hinj28_12_2
      Q2.hcardT28_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T28_12_2 i) (Q2.hfix28_12_2 i) _)
      ?_).symm
  rw [show colData1 (⟨28, by decide⟩ : Fin 148)
        ((colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp) : ↥(reps ⟨12, by decide⟩)) : Coordinate 1)
        T28_12 = colFn colCert_28_12_0.D (m := 125) from colCert_28_12_0.bind1,
    show colData2 (⟨28, by decide⟩ : Fin 148)
        ((colE2 ⟨12, by decide⟩ 0 hp : ↥(Q2.reps ⟨12, by decide⟩)) : Coordinate 2)
        Q2.T28_12_2 = colFn colCert_28_12_0.D (m := 125) from colCert_28_12_0.bind2]
  exact alnAll_28_12_0 j hj hq

theorem leaf_28_12_1 (hp : 1 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 28 []).length)
    (hq : (normIsRep.getD 28 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 1 hp)
        (rowE2 (⟨28, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp))
        (rowE1 (⟨28, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨28, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨28, by decide⟩ (listedAt ⟨28, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp)) T28_12
      hfix28_12 hinj28_12 hcardT28_12
      (fun i => conj_mem_of_fixedPoints _ _ (T28_12 i) (hfix28_12 i) _)
      ⟨28, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨28, by decide⟩ (Q2.listedAt ⟨28, by decide⟩
        (alnCheck_rep ⟨28, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 1 hp) Q2.T28_12_2 Q2.hfix28_12_2 Q2.hinj28_12_2
      Q2.hcardT28_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T28_12_2 i) (Q2.hfix28_12_2 i) _)
      ?_).symm
  rw [show colData1 (⟨28, by decide⟩ : Fin 148)
        ((colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp) : ↥(reps ⟨12, by decide⟩)) : Coordinate 1)
        T28_12 = colFn colCert_28_12_1.D (m := 125) from colCert_28_12_1.bind1,
    show colData2 (⟨28, by decide⟩ : Fin 148)
        ((colE2 ⟨12, by decide⟩ 1 hp : ↥(Q2.reps ⟨12, by decide⟩)) : Coordinate 2)
        Q2.T28_12_2 = colFn colCert_28_12_1.D (m := 125) from colCert_28_12_1.bind2]
  exact alnAll_28_12_1 j hj hq

theorem leaf_28_12_2 (hp : 2 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 28 []).length)
    (hq : (normIsRep.getD 28 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 2 hp)
        (rowE2 (⟨28, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp))
        (rowE1 (⟨28, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨28, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨28, by decide⟩ (listedAt ⟨28, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp)) T28_12
      hfix28_12 hinj28_12 hcardT28_12
      (fun i => conj_mem_of_fixedPoints _ _ (T28_12 i) (hfix28_12 i) _)
      ⟨28, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨28, by decide⟩ (Q2.listedAt ⟨28, by decide⟩
        (alnCheck_rep ⟨28, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 2 hp) Q2.T28_12_2 Q2.hfix28_12_2 Q2.hinj28_12_2
      Q2.hcardT28_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T28_12_2 i) (Q2.hfix28_12_2 i) _)
      ?_).symm
  rw [show colData1 (⟨28, by decide⟩ : Fin 148)
        ((colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp) : ↥(reps ⟨12, by decide⟩)) : Coordinate 1)
        T28_12 = colFn colCert_28_12_2.D (m := 125) from colCert_28_12_2.bind1,
    show colData2 (⟨28, by decide⟩ : Fin 148)
        ((colE2 ⟨12, by decide⟩ 2 hp : ↥(Q2.reps ⟨12, by decide⟩)) : Coordinate 2)
        Q2.T28_12_2 = colFn colCert_28_12_2.D (m := 125) from colCert_28_12_2.bind2]
  exact alnAll_28_12_2 j hj hq

theorem leaf_28_12_3 (hp : 3 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 28 []).length)
    (hq : (normIsRep.getD 28 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 3 hp)
        (rowE2 (⟨28, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp))
        (rowE1 (⟨28, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨28, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨28, by decide⟩ (listedAt ⟨28, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp)) T28_12
      hfix28_12 hinj28_12 hcardT28_12
      (fun i => conj_mem_of_fixedPoints _ _ (T28_12 i) (hfix28_12 i) _)
      ⟨28, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨28, by decide⟩ (Q2.listedAt ⟨28, by decide⟩
        (alnCheck_rep ⟨28, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 3 hp) Q2.T28_12_2 Q2.hfix28_12_2 Q2.hinj28_12_2
      Q2.hcardT28_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T28_12_2 i) (Q2.hfix28_12_2 i) _)
      ?_).symm
  rw [show colData1 (⟨28, by decide⟩ : Fin 148)
        ((colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp) : ↥(reps ⟨12, by decide⟩)) : Coordinate 1)
        T28_12 = colFn colCert_28_12_3.D (m := 125) from colCert_28_12_3.bind1,
    show colData2 (⟨28, by decide⟩ : Fin 148)
        ((colE2 ⟨12, by decide⟩ 3 hp : ↥(Q2.reps ⟨12, by decide⟩)) : Coordinate 2)
        Q2.T28_12_2 = colFn colCert_28_12_3.D (m := 125) from colCert_28_12_3.bind2]
  exact alnAll_28_12_3 j hj hq

theorem leaf_28_12_4 (hp : 4 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 28 []).length)
    (hq : (normIsRep.getD 28 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 4 hp)
        (rowE2 (⟨28, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp))
        (rowE1 (⟨28, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨28, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨28, by decide⟩ (listedAt ⟨28, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp)) T28_12
      hfix28_12 hinj28_12 hcardT28_12
      (fun i => conj_mem_of_fixedPoints _ _ (T28_12 i) (hfix28_12 i) _)
      ⟨28, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨28, by decide⟩ (Q2.listedAt ⟨28, by decide⟩
        (alnCheck_rep ⟨28, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 4 hp) Q2.T28_12_2 Q2.hfix28_12_2 Q2.hinj28_12_2
      Q2.hcardT28_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T28_12_2 i) (Q2.hfix28_12_2 i) _)
      ?_).symm
  rw [show colData1 (⟨28, by decide⟩ : Fin 148)
        ((colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp) : ↥(reps ⟨12, by decide⟩)) : Coordinate 1)
        T28_12 = colFn colCert_28_12_4.D (m := 125) from colCert_28_12_4.bind1,
    show colData2 (⟨28, by decide⟩ : Fin 148)
        ((colE2 ⟨12, by decide⟩ 4 hp : ↥(Q2.reps ⟨12, by decide⟩)) : Coordinate 2)
        Q2.T28_12_2 = colFn colCert_28_12_4.D (m := 125) from colCert_28_12_4.bind2]
  exact alnAll_28_12_4 j hj hq

theorem leaf_28_28_0 (hp : 0 < (Q2.transData.getD 28 []).length)
    (j : Nat) (hj : j < (repChars.getD 28 []).length)
    (hq : (normIsRep.getD 28 []).getD j false = true) :
    species (Q2.reps (⟨28, by decide⟩ : Fin 148)) (colE2 ⟨28, by decide⟩ 0 hp)
        (rowE2 (⟨28, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨28, by decide⟩ : Fin 148))
        (colE1 ⟨28, by decide⟩ 0 (transLenTr ⟨28, by decide⟩ 0 hp))
        (rowE1 (⟨28, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨28, by decide⟩ : Fin 148) ⟨28, by decide⟩ _
      (validAt ⟨28, by decide⟩ (listedAt ⟨28, by decide⟩ hj))
      (colE1 ⟨28, by decide⟩ 0 (transLenTr ⟨28, by decide⟩ 0 hp)) T28_28
      hfix28_28 hinj28_28 hcardT28_28
      (fun i => conj_mem_of_fixedPoints _ _ (T28_28 i) (hfix28_28 i) _)
      ⟨28, by decide⟩ ⟨28, by decide⟩ _
      (Q2.validAt ⟨28, by decide⟩ (Q2.listedAt ⟨28, by decide⟩
        (alnCheck_rep ⟨28, by decide⟩ hj hq).1))
      (colE2 ⟨28, by decide⟩ 0 hp) Q2.T28_28_2 Q2.hfix28_28_2 Q2.hinj28_28_2
      Q2.hcardT28_28_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T28_28_2 i) (Q2.hfix28_28_2 i) _)
      ?_).symm
  rw [show colData1 (⟨28, by decide⟩ : Fin 148)
        ((colE1 ⟨28, by decide⟩ 0 (transLenTr ⟨28, by decide⟩ 0 hp) : ↥(reps ⟨28, by decide⟩)) : Coordinate 1)
        T28_28 = colFn colCert_28_28_0.D (m := 25) from colCert_28_28_0.bind1,
    show colData2 (⟨28, by decide⟩ : Fin 148)
        ((colE2 ⟨28, by decide⟩ 0 hp : ↥(Q2.reps ⟨28, by decide⟩)) : Coordinate 2)
        Q2.T28_28_2 = colFn colCert_28_28_0.D (m := 25) from colCert_28_28_0.bind2]
  exact alnAll_28_28_0 j hj hq

theorem leaf_28_28_1 (hp : 1 < (Q2.transData.getD 28 []).length)
    (j : Nat) (hj : j < (repChars.getD 28 []).length)
    (hq : (normIsRep.getD 28 []).getD j false = true) :
    species (Q2.reps (⟨28, by decide⟩ : Fin 148)) (colE2 ⟨28, by decide⟩ 1 hp)
        (rowE2 (⟨28, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨28, by decide⟩ : Fin 148))
        (colE1 ⟨28, by decide⟩ 1 (transLenTr ⟨28, by decide⟩ 1 hp))
        (rowE1 (⟨28, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨28, by decide⟩ : Fin 148) ⟨28, by decide⟩ _
      (validAt ⟨28, by decide⟩ (listedAt ⟨28, by decide⟩ hj))
      (colE1 ⟨28, by decide⟩ 1 (transLenTr ⟨28, by decide⟩ 1 hp)) T28_28
      hfix28_28 hinj28_28 hcardT28_28
      (fun i => conj_mem_of_fixedPoints _ _ (T28_28 i) (hfix28_28 i) _)
      ⟨28, by decide⟩ ⟨28, by decide⟩ _
      (Q2.validAt ⟨28, by decide⟩ (Q2.listedAt ⟨28, by decide⟩
        (alnCheck_rep ⟨28, by decide⟩ hj hq).1))
      (colE2 ⟨28, by decide⟩ 1 hp) Q2.T28_28_2 Q2.hfix28_28_2 Q2.hinj28_28_2
      Q2.hcardT28_28_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T28_28_2 i) (Q2.hfix28_28_2 i) _)
      ?_).symm
  rw [show colData1 (⟨28, by decide⟩ : Fin 148)
        ((colE1 ⟨28, by decide⟩ 1 (transLenTr ⟨28, by decide⟩ 1 hp) : ↥(reps ⟨28, by decide⟩)) : Coordinate 1)
        T28_28 = colFn colCert_28_28_1.D (m := 25) from colCert_28_28_1.bind1,
    show colData2 (⟨28, by decide⟩ : Fin 148)
        ((colE2 ⟨28, by decide⟩ 1 hp : ↥(Q2.reps ⟨28, by decide⟩)) : Coordinate 2)
        Q2.T28_28_2 = colFn colCert_28_28_1.D (m := 25) from colCert_28_28_1.bind2]
  exact alnAll_28_28_1 j hj hq

theorem leaf_28_28_2 (hp : 2 < (Q2.transData.getD 28 []).length)
    (j : Nat) (hj : j < (repChars.getD 28 []).length)
    (hq : (normIsRep.getD 28 []).getD j false = true) :
    species (Q2.reps (⟨28, by decide⟩ : Fin 148)) (colE2 ⟨28, by decide⟩ 2 hp)
        (rowE2 (⟨28, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨28, by decide⟩ : Fin 148))
        (colE1 ⟨28, by decide⟩ 2 (transLenTr ⟨28, by decide⟩ 2 hp))
        (rowE1 (⟨28, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨28, by decide⟩ : Fin 148) ⟨28, by decide⟩ _
      (validAt ⟨28, by decide⟩ (listedAt ⟨28, by decide⟩ hj))
      (colE1 ⟨28, by decide⟩ 2 (transLenTr ⟨28, by decide⟩ 2 hp)) T28_28
      hfix28_28 hinj28_28 hcardT28_28
      (fun i => conj_mem_of_fixedPoints _ _ (T28_28 i) (hfix28_28 i) _)
      ⟨28, by decide⟩ ⟨28, by decide⟩ _
      (Q2.validAt ⟨28, by decide⟩ (Q2.listedAt ⟨28, by decide⟩
        (alnCheck_rep ⟨28, by decide⟩ hj hq).1))
      (colE2 ⟨28, by decide⟩ 2 hp) Q2.T28_28_2 Q2.hfix28_28_2 Q2.hinj28_28_2
      Q2.hcardT28_28_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T28_28_2 i) (Q2.hfix28_28_2 i) _)
      ?_).symm
  rw [show colData1 (⟨28, by decide⟩ : Fin 148)
        ((colE1 ⟨28, by decide⟩ 2 (transLenTr ⟨28, by decide⟩ 2 hp) : ↥(reps ⟨28, by decide⟩)) : Coordinate 1)
        T28_28 = colFn colCert_28_28_2.D (m := 25) from colCert_28_28_2.bind1,
    show colData2 (⟨28, by decide⟩ : Fin 148)
        ((colE2 ⟨28, by decide⟩ 2 hp : ↥(Q2.reps ⟨28, by decide⟩)) : Coordinate 2)
        Q2.T28_28_2 = colFn colCert_28_28_2.D (m := 25) from colCert_28_28_2.bind2]
  exact alnAll_28_28_2 j hj hq

theorem leaf_28_28_3 (hp : 3 < (Q2.transData.getD 28 []).length)
    (j : Nat) (hj : j < (repChars.getD 28 []).length)
    (hq : (normIsRep.getD 28 []).getD j false = true) :
    species (Q2.reps (⟨28, by decide⟩ : Fin 148)) (colE2 ⟨28, by decide⟩ 3 hp)
        (rowE2 (⟨28, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨28, by decide⟩ : Fin 148))
        (colE1 ⟨28, by decide⟩ 3 (transLenTr ⟨28, by decide⟩ 3 hp))
        (rowE1 (⟨28, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨28, by decide⟩ : Fin 148) ⟨28, by decide⟩ _
      (validAt ⟨28, by decide⟩ (listedAt ⟨28, by decide⟩ hj))
      (colE1 ⟨28, by decide⟩ 3 (transLenTr ⟨28, by decide⟩ 3 hp)) T28_28
      hfix28_28 hinj28_28 hcardT28_28
      (fun i => conj_mem_of_fixedPoints _ _ (T28_28 i) (hfix28_28 i) _)
      ⟨28, by decide⟩ ⟨28, by decide⟩ _
      (Q2.validAt ⟨28, by decide⟩ (Q2.listedAt ⟨28, by decide⟩
        (alnCheck_rep ⟨28, by decide⟩ hj hq).1))
      (colE2 ⟨28, by decide⟩ 3 hp) Q2.T28_28_2 Q2.hfix28_28_2 Q2.hinj28_28_2
      Q2.hcardT28_28_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T28_28_2 i) (Q2.hfix28_28_2 i) _)
      ?_).symm
  rw [show colData1 (⟨28, by decide⟩ : Fin 148)
        ((colE1 ⟨28, by decide⟩ 3 (transLenTr ⟨28, by decide⟩ 3 hp) : ↥(reps ⟨28, by decide⟩)) : Coordinate 1)
        T28_28 = colFn colCert_28_28_3.D (m := 25) from colCert_28_28_3.bind1,
    show colData2 (⟨28, by decide⟩ : Fin 148)
        ((colE2 ⟨28, by decide⟩ 3 hp : ↥(Q2.reps ⟨28, by decide⟩)) : Coordinate 2)
        Q2.T28_28_2 = colFn colCert_28_28_3.D (m := 25) from colCert_28_28_3.bind2]
  exact alnAll_28_28_3 j hj hq

theorem leaf_28_28_4 (hp : 4 < (Q2.transData.getD 28 []).length)
    (j : Nat) (hj : j < (repChars.getD 28 []).length)
    (hq : (normIsRep.getD 28 []).getD j false = true) :
    species (Q2.reps (⟨28, by decide⟩ : Fin 148)) (colE2 ⟨28, by decide⟩ 4 hp)
        (rowE2 (⟨28, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨28, by decide⟩ : Fin 148))
        (colE1 ⟨28, by decide⟩ 4 (transLenTr ⟨28, by decide⟩ 4 hp))
        (rowE1 (⟨28, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨28, by decide⟩ : Fin 148) ⟨28, by decide⟩ _
      (validAt ⟨28, by decide⟩ (listedAt ⟨28, by decide⟩ hj))
      (colE1 ⟨28, by decide⟩ 4 (transLenTr ⟨28, by decide⟩ 4 hp)) T28_28
      hfix28_28 hinj28_28 hcardT28_28
      (fun i => conj_mem_of_fixedPoints _ _ (T28_28 i) (hfix28_28 i) _)
      ⟨28, by decide⟩ ⟨28, by decide⟩ _
      (Q2.validAt ⟨28, by decide⟩ (Q2.listedAt ⟨28, by decide⟩
        (alnCheck_rep ⟨28, by decide⟩ hj hq).1))
      (colE2 ⟨28, by decide⟩ 4 hp) Q2.T28_28_2 Q2.hfix28_28_2 Q2.hinj28_28_2
      Q2.hcardT28_28_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T28_28_2 i) (Q2.hfix28_28_2 i) _)
      ?_).symm
  rw [show colData1 (⟨28, by decide⟩ : Fin 148)
        ((colE1 ⟨28, by decide⟩ 4 (transLenTr ⟨28, by decide⟩ 4 hp) : ↥(reps ⟨28, by decide⟩)) : Coordinate 1)
        T28_28 = colFn colCert_28_28_4.D (m := 25) from colCert_28_28_4.bind1,
    show colData2 (⟨28, by decide⟩ : Fin 148)
        ((colE2 ⟨28, by decide⟩ 4 hp : ↥(Q2.reps ⟨28, by decide⟩)) : Coordinate 2)
        Q2.T28_28_2 = colFn colCert_28_28_4.D (m := 25) from colCert_28_28_4.bind2]
  exact alnAll_28_28_4 j hj hq

theorem leaf_28_28_5 (hp : 5 < (Q2.transData.getD 28 []).length)
    (j : Nat) (hj : j < (repChars.getD 28 []).length)
    (hq : (normIsRep.getD 28 []).getD j false = true) :
    species (Q2.reps (⟨28, by decide⟩ : Fin 148)) (colE2 ⟨28, by decide⟩ 5 hp)
        (rowE2 (⟨28, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨28, by decide⟩ : Fin 148))
        (colE1 ⟨28, by decide⟩ 5 (transLenTr ⟨28, by decide⟩ 5 hp))
        (rowE1 (⟨28, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨28, by decide⟩ : Fin 148) ⟨28, by decide⟩ _
      (validAt ⟨28, by decide⟩ (listedAt ⟨28, by decide⟩ hj))
      (colE1 ⟨28, by decide⟩ 5 (transLenTr ⟨28, by decide⟩ 5 hp)) T28_28
      hfix28_28 hinj28_28 hcardT28_28
      (fun i => conj_mem_of_fixedPoints _ _ (T28_28 i) (hfix28_28 i) _)
      ⟨28, by decide⟩ ⟨28, by decide⟩ _
      (Q2.validAt ⟨28, by decide⟩ (Q2.listedAt ⟨28, by decide⟩
        (alnCheck_rep ⟨28, by decide⟩ hj hq).1))
      (colE2 ⟨28, by decide⟩ 5 hp) Q2.T28_28_2 Q2.hfix28_28_2 Q2.hinj28_28_2
      Q2.hcardT28_28_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T28_28_2 i) (Q2.hfix28_28_2 i) _)
      ?_).symm
  rw [show colData1 (⟨28, by decide⟩ : Fin 148)
        ((colE1 ⟨28, by decide⟩ 5 (transLenTr ⟨28, by decide⟩ 5 hp) : ↥(reps ⟨28, by decide⟩)) : Coordinate 1)
        T28_28 = colFn colCert_28_28_5.D (m := 25) from colCert_28_28_5.bind1,
    show colData2 (⟨28, by decide⟩ : Fin 148)
        ((colE2 ⟨28, by decide⟩ 5 hp : ↥(Q2.reps ⟨28, by decide⟩)) : Coordinate 2)
        Q2.T28_28_2 = colFn colCert_28_28_5.D (m := 25) from colCert_28_28_5.bind2]
  exact alnAll_28_28_5 j hj hq

theorem leaf_28_28_10 (hp : 10 < (Q2.transData.getD 28 []).length)
    (j : Nat) (hj : j < (repChars.getD 28 []).length)
    (hq : (normIsRep.getD 28 []).getD j false = true) :
    species (Q2.reps (⟨28, by decide⟩ : Fin 148)) (colE2 ⟨28, by decide⟩ 10 hp)
        (rowE2 (⟨28, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨28, by decide⟩ : Fin 148))
        (colE1 ⟨28, by decide⟩ 10 (transLenTr ⟨28, by decide⟩ 10 hp))
        (rowE1 (⟨28, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨28, by decide⟩ : Fin 148) ⟨28, by decide⟩ _
      (validAt ⟨28, by decide⟩ (listedAt ⟨28, by decide⟩ hj))
      (colE1 ⟨28, by decide⟩ 10 (transLenTr ⟨28, by decide⟩ 10 hp)) T28_28
      hfix28_28 hinj28_28 hcardT28_28
      (fun i => conj_mem_of_fixedPoints _ _ (T28_28 i) (hfix28_28 i) _)
      ⟨28, by decide⟩ ⟨28, by decide⟩ _
      (Q2.validAt ⟨28, by decide⟩ (Q2.listedAt ⟨28, by decide⟩
        (alnCheck_rep ⟨28, by decide⟩ hj hq).1))
      (colE2 ⟨28, by decide⟩ 10 hp) Q2.T28_28_2 Q2.hfix28_28_2 Q2.hinj28_28_2
      Q2.hcardT28_28_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T28_28_2 i) (Q2.hfix28_28_2 i) _)
      ?_).symm
  rw [show colData1 (⟨28, by decide⟩ : Fin 148)
        ((colE1 ⟨28, by decide⟩ 10 (transLenTr ⟨28, by decide⟩ 10 hp) : ↥(reps ⟨28, by decide⟩)) : Coordinate 1)
        T28_28 = colFn colCert_28_28_10.D (m := 25) from colCert_28_28_10.bind1,
    show colData2 (⟨28, by decide⟩ : Fin 148)
        ((colE2 ⟨28, by decide⟩ 10 hp : ↥(Q2.reps ⟨28, by decide⟩)) : Coordinate 2)
        Q2.T28_28_2 = colFn colCert_28_28_10.D (m := 25) from colCert_28_28_10.bind2]
  exact alnAll_28_28_10 j hj hq

theorem leaf_28_28_15 (hp : 15 < (Q2.transData.getD 28 []).length)
    (j : Nat) (hj : j < (repChars.getD 28 []).length)
    (hq : (normIsRep.getD 28 []).getD j false = true) :
    species (Q2.reps (⟨28, by decide⟩ : Fin 148)) (colE2 ⟨28, by decide⟩ 15 hp)
        (rowE2 (⟨28, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨28, by decide⟩ : Fin 148))
        (colE1 ⟨28, by decide⟩ 15 (transLenTr ⟨28, by decide⟩ 15 hp))
        (rowE1 (⟨28, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨28, by decide⟩ : Fin 148) ⟨28, by decide⟩ _
      (validAt ⟨28, by decide⟩ (listedAt ⟨28, by decide⟩ hj))
      (colE1 ⟨28, by decide⟩ 15 (transLenTr ⟨28, by decide⟩ 15 hp)) T28_28
      hfix28_28 hinj28_28 hcardT28_28
      (fun i => conj_mem_of_fixedPoints _ _ (T28_28 i) (hfix28_28 i) _)
      ⟨28, by decide⟩ ⟨28, by decide⟩ _
      (Q2.validAt ⟨28, by decide⟩ (Q2.listedAt ⟨28, by decide⟩
        (alnCheck_rep ⟨28, by decide⟩ hj hq).1))
      (colE2 ⟨28, by decide⟩ 15 hp) Q2.T28_28_2 Q2.hfix28_28_2 Q2.hinj28_28_2
      Q2.hcardT28_28_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T28_28_2 i) (Q2.hfix28_28_2 i) _)
      ?_).symm
  rw [show colData1 (⟨28, by decide⟩ : Fin 148)
        ((colE1 ⟨28, by decide⟩ 15 (transLenTr ⟨28, by decide⟩ 15 hp) : ↥(reps ⟨28, by decide⟩)) : Coordinate 1)
        T28_28 = colFn colCert_28_28_15.D (m := 25) from colCert_28_28_15.bind1,
    show colData2 (⟨28, by decide⟩ : Fin 148)
        ((colE2 ⟨28, by decide⟩ 15 hp : ↥(Q2.reps ⟨28, by decide⟩)) : Coordinate 2)
        Q2.T28_28_2 = colFn colCert_28_28_15.D (m := 25) from colCert_28_28_15.bind2]
  exact alnAll_28_28_15 j hj hq

theorem leaf_28_28_20 (hp : 20 < (Q2.transData.getD 28 []).length)
    (j : Nat) (hj : j < (repChars.getD 28 []).length)
    (hq : (normIsRep.getD 28 []).getD j false = true) :
    species (Q2.reps (⟨28, by decide⟩ : Fin 148)) (colE2 ⟨28, by decide⟩ 20 hp)
        (rowE2 (⟨28, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨28, by decide⟩ : Fin 148))
        (colE1 ⟨28, by decide⟩ 20 (transLenTr ⟨28, by decide⟩ 20 hp))
        (rowE1 (⟨28, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨28, by decide⟩ : Fin 148) ⟨28, by decide⟩ _
      (validAt ⟨28, by decide⟩ (listedAt ⟨28, by decide⟩ hj))
      (colE1 ⟨28, by decide⟩ 20 (transLenTr ⟨28, by decide⟩ 20 hp)) T28_28
      hfix28_28 hinj28_28 hcardT28_28
      (fun i => conj_mem_of_fixedPoints _ _ (T28_28 i) (hfix28_28 i) _)
      ⟨28, by decide⟩ ⟨28, by decide⟩ _
      (Q2.validAt ⟨28, by decide⟩ (Q2.listedAt ⟨28, by decide⟩
        (alnCheck_rep ⟨28, by decide⟩ hj hq).1))
      (colE2 ⟨28, by decide⟩ 20 hp) Q2.T28_28_2 Q2.hfix28_28_2 Q2.hinj28_28_2
      Q2.hcardT28_28_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T28_28_2 i) (Q2.hfix28_28_2 i) _)
      ?_).symm
  rw [show colData1 (⟨28, by decide⟩ : Fin 148)
        ((colE1 ⟨28, by decide⟩ 20 (transLenTr ⟨28, by decide⟩ 20 hp) : ↥(reps ⟨28, by decide⟩)) : Coordinate 1)
        T28_28 = colFn colCert_28_28_20.D (m := 25) from colCert_28_28_20.bind1,
    show colData2 (⟨28, by decide⟩ : Fin 148)
        ((colE2 ⟨28, by decide⟩ 20 hp : ↥(Q2.reps ⟨28, by decide⟩)) : Coordinate 2)
        Q2.T28_28_2 = colFn colCert_28_28_20.D (m := 25) from colCert_28_28_20.bind2]
  exact alnAll_28_28_20 j hj hq

theorem leaf_29_12_0 (hp : 0 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 29 []).length)
    (hq : (normIsRep.getD 29 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 0 hp)
        (rowE2 (⟨29, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp))
        (rowE1 (⟨29, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨29, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨29, by decide⟩ (listedAt ⟨29, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp)) T29_12
      hfix29_12 hinj29_12 hcardT29_12
      (fun i => conj_mem_of_fixedPoints _ _ (T29_12 i) (hfix29_12 i) _)
      ⟨29, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨29, by decide⟩ (Q2.listedAt ⟨29, by decide⟩
        (alnCheck_rep ⟨29, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 0 hp) Q2.T29_12_2 Q2.hfix29_12_2 Q2.hinj29_12_2
      Q2.hcardT29_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T29_12_2 i) (Q2.hfix29_12_2 i) _)
      ?_).symm
  rw [show colData1 (⟨29, by decide⟩ : Fin 148)
        ((colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp) : ↥(reps ⟨12, by decide⟩)) : Coordinate 1)
        T29_12 = colFn colCert_29_12_0.D (m := 125) from colCert_29_12_0.bind1,
    show colData2 (⟨29, by decide⟩ : Fin 148)
        ((colE2 ⟨12, by decide⟩ 0 hp : ↥(Q2.reps ⟨12, by decide⟩)) : Coordinate 2)
        Q2.T29_12_2 = colFn colCert_29_12_0.D (m := 125) from colCert_29_12_0.bind2]
  exact alnAll_29_12_0 j hj hq

theorem leaf_29_12_1 (hp : 1 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 29 []).length)
    (hq : (normIsRep.getD 29 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 1 hp)
        (rowE2 (⟨29, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp))
        (rowE1 (⟨29, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨29, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨29, by decide⟩ (listedAt ⟨29, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp)) T29_12
      hfix29_12 hinj29_12 hcardT29_12
      (fun i => conj_mem_of_fixedPoints _ _ (T29_12 i) (hfix29_12 i) _)
      ⟨29, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨29, by decide⟩ (Q2.listedAt ⟨29, by decide⟩
        (alnCheck_rep ⟨29, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 1 hp) Q2.T29_12_2 Q2.hfix29_12_2 Q2.hinj29_12_2
      Q2.hcardT29_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T29_12_2 i) (Q2.hfix29_12_2 i) _)
      ?_).symm
  rw [show colData1 (⟨29, by decide⟩ : Fin 148)
        ((colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp) : ↥(reps ⟨12, by decide⟩)) : Coordinate 1)
        T29_12 = colFn colCert_29_12_1.D (m := 125) from colCert_29_12_1.bind1,
    show colData2 (⟨29, by decide⟩ : Fin 148)
        ((colE2 ⟨12, by decide⟩ 1 hp : ↥(Q2.reps ⟨12, by decide⟩)) : Coordinate 2)
        Q2.T29_12_2 = colFn colCert_29_12_1.D (m := 125) from colCert_29_12_1.bind2]
  exact alnAll_29_12_1 j hj hq

theorem leaf_29_12_2 (hp : 2 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 29 []).length)
    (hq : (normIsRep.getD 29 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 2 hp)
        (rowE2 (⟨29, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp))
        (rowE1 (⟨29, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨29, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨29, by decide⟩ (listedAt ⟨29, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp)) T29_12
      hfix29_12 hinj29_12 hcardT29_12
      (fun i => conj_mem_of_fixedPoints _ _ (T29_12 i) (hfix29_12 i) _)
      ⟨29, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨29, by decide⟩ (Q2.listedAt ⟨29, by decide⟩
        (alnCheck_rep ⟨29, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 2 hp) Q2.T29_12_2 Q2.hfix29_12_2 Q2.hinj29_12_2
      Q2.hcardT29_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T29_12_2 i) (Q2.hfix29_12_2 i) _)
      ?_).symm
  rw [show colData1 (⟨29, by decide⟩ : Fin 148)
        ((colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp) : ↥(reps ⟨12, by decide⟩)) : Coordinate 1)
        T29_12 = colFn colCert_29_12_2.D (m := 125) from colCert_29_12_2.bind1,
    show colData2 (⟨29, by decide⟩ : Fin 148)
        ((colE2 ⟨12, by decide⟩ 2 hp : ↥(Q2.reps ⟨12, by decide⟩)) : Coordinate 2)
        Q2.T29_12_2 = colFn colCert_29_12_2.D (m := 125) from colCert_29_12_2.bind2]
  exact alnAll_29_12_2 j hj hq

theorem leaf_29_12_3 (hp : 3 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 29 []).length)
    (hq : (normIsRep.getD 29 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 3 hp)
        (rowE2 (⟨29, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp))
        (rowE1 (⟨29, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨29, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨29, by decide⟩ (listedAt ⟨29, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp)) T29_12
      hfix29_12 hinj29_12 hcardT29_12
      (fun i => conj_mem_of_fixedPoints _ _ (T29_12 i) (hfix29_12 i) _)
      ⟨29, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨29, by decide⟩ (Q2.listedAt ⟨29, by decide⟩
        (alnCheck_rep ⟨29, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 3 hp) Q2.T29_12_2 Q2.hfix29_12_2 Q2.hinj29_12_2
      Q2.hcardT29_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T29_12_2 i) (Q2.hfix29_12_2 i) _)
      ?_).symm
  rw [show colData1 (⟨29, by decide⟩ : Fin 148)
        ((colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp) : ↥(reps ⟨12, by decide⟩)) : Coordinate 1)
        T29_12 = colFn colCert_29_12_3.D (m := 125) from colCert_29_12_3.bind1,
    show colData2 (⟨29, by decide⟩ : Fin 148)
        ((colE2 ⟨12, by decide⟩ 3 hp : ↥(Q2.reps ⟨12, by decide⟩)) : Coordinate 2)
        Q2.T29_12_2 = colFn colCert_29_12_3.D (m := 125) from colCert_29_12_3.bind2]
  exact alnAll_29_12_3 j hj hq

theorem leaf_29_12_4 (hp : 4 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 29 []).length)
    (hq : (normIsRep.getD 29 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 4 hp)
        (rowE2 (⟨29, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp))
        (rowE1 (⟨29, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨29, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨29, by decide⟩ (listedAt ⟨29, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp)) T29_12
      hfix29_12 hinj29_12 hcardT29_12
      (fun i => conj_mem_of_fixedPoints _ _ (T29_12 i) (hfix29_12 i) _)
      ⟨29, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨29, by decide⟩ (Q2.listedAt ⟨29, by decide⟩
        (alnCheck_rep ⟨29, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 4 hp) Q2.T29_12_2 Q2.hfix29_12_2 Q2.hinj29_12_2
      Q2.hcardT29_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T29_12_2 i) (Q2.hfix29_12_2 i) _)
      ?_).symm
  rw [show colData1 (⟨29, by decide⟩ : Fin 148)
        ((colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp) : ↥(reps ⟨12, by decide⟩)) : Coordinate 1)
        T29_12 = colFn colCert_29_12_4.D (m := 125) from colCert_29_12_4.bind1,
    show colData2 (⟨29, by decide⟩ : Fin 148)
        ((colE2 ⟨12, by decide⟩ 4 hp : ↥(Q2.reps ⟨12, by decide⟩)) : Coordinate 2)
        Q2.T29_12_2 = colFn colCert_29_12_4.D (m := 125) from colCert_29_12_4.bind2]
  exact alnAll_29_12_4 j hj hq

theorem leaf_29_29_0 (hp : 0 < (Q2.transData.getD 29 []).length)
    (j : Nat) (hj : j < (repChars.getD 29 []).length)
    (hq : (normIsRep.getD 29 []).getD j false = true) :
    species (Q2.reps (⟨29, by decide⟩ : Fin 148)) (colE2 ⟨29, by decide⟩ 0 hp)
        (rowE2 (⟨29, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨29, by decide⟩ : Fin 148))
        (colE1 ⟨29, by decide⟩ 0 (transLenTr ⟨29, by decide⟩ 0 hp))
        (rowE1 (⟨29, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨29, by decide⟩ : Fin 148) ⟨29, by decide⟩ _
      (validAt ⟨29, by decide⟩ (listedAt ⟨29, by decide⟩ hj))
      (colE1 ⟨29, by decide⟩ 0 (transLenTr ⟨29, by decide⟩ 0 hp)) T29_29
      hfix29_29 hinj29_29 hcardT29_29
      (fun i => conj_mem_of_fixedPoints _ _ (T29_29 i) (hfix29_29 i) _)
      ⟨29, by decide⟩ ⟨29, by decide⟩ _
      (Q2.validAt ⟨29, by decide⟩ (Q2.listedAt ⟨29, by decide⟩
        (alnCheck_rep ⟨29, by decide⟩ hj hq).1))
      (colE2 ⟨29, by decide⟩ 0 hp) Q2.T29_29_2 Q2.hfix29_29_2 Q2.hinj29_29_2
      Q2.hcardT29_29_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T29_29_2 i) (Q2.hfix29_29_2 i) _)
      ?_).symm
  rw [show colData1 (⟨29, by decide⟩ : Fin 148)
        ((colE1 ⟨29, by decide⟩ 0 (transLenTr ⟨29, by decide⟩ 0 hp) : ↥(reps ⟨29, by decide⟩)) : Coordinate 1)
        T29_29 = colFn colCert_29_29_0.D (m := 25) from colCert_29_29_0.bind1,
    show colData2 (⟨29, by decide⟩ : Fin 148)
        ((colE2 ⟨29, by decide⟩ 0 hp : ↥(Q2.reps ⟨29, by decide⟩)) : Coordinate 2)
        Q2.T29_29_2 = colFn colCert_29_29_0.D (m := 25) from colCert_29_29_0.bind2]
  exact alnAll_29_29_0 j hj hq

theorem leaf_29_29_1 (hp : 1 < (Q2.transData.getD 29 []).length)
    (j : Nat) (hj : j < (repChars.getD 29 []).length)
    (hq : (normIsRep.getD 29 []).getD j false = true) :
    species (Q2.reps (⟨29, by decide⟩ : Fin 148)) (colE2 ⟨29, by decide⟩ 1 hp)
        (rowE2 (⟨29, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨29, by decide⟩ : Fin 148))
        (colE1 ⟨29, by decide⟩ 1 (transLenTr ⟨29, by decide⟩ 1 hp))
        (rowE1 (⟨29, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨29, by decide⟩ : Fin 148) ⟨29, by decide⟩ _
      (validAt ⟨29, by decide⟩ (listedAt ⟨29, by decide⟩ hj))
      (colE1 ⟨29, by decide⟩ 1 (transLenTr ⟨29, by decide⟩ 1 hp)) T29_29
      hfix29_29 hinj29_29 hcardT29_29
      (fun i => conj_mem_of_fixedPoints _ _ (T29_29 i) (hfix29_29 i) _)
      ⟨29, by decide⟩ ⟨29, by decide⟩ _
      (Q2.validAt ⟨29, by decide⟩ (Q2.listedAt ⟨29, by decide⟩
        (alnCheck_rep ⟨29, by decide⟩ hj hq).1))
      (colE2 ⟨29, by decide⟩ 1 hp) Q2.T29_29_2 Q2.hfix29_29_2 Q2.hinj29_29_2
      Q2.hcardT29_29_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T29_29_2 i) (Q2.hfix29_29_2 i) _)
      ?_).symm
  rw [show colData1 (⟨29, by decide⟩ : Fin 148)
        ((colE1 ⟨29, by decide⟩ 1 (transLenTr ⟨29, by decide⟩ 1 hp) : ↥(reps ⟨29, by decide⟩)) : Coordinate 1)
        T29_29 = colFn colCert_29_29_1.D (m := 25) from colCert_29_29_1.bind1,
    show colData2 (⟨29, by decide⟩ : Fin 148)
        ((colE2 ⟨29, by decide⟩ 1 hp : ↥(Q2.reps ⟨29, by decide⟩)) : Coordinate 2)
        Q2.T29_29_2 = colFn colCert_29_29_1.D (m := 25) from colCert_29_29_1.bind2]
  exact alnAll_29_29_1 j hj hq

theorem leaf_29_29_2 (hp : 2 < (Q2.transData.getD 29 []).length)
    (j : Nat) (hj : j < (repChars.getD 29 []).length)
    (hq : (normIsRep.getD 29 []).getD j false = true) :
    species (Q2.reps (⟨29, by decide⟩ : Fin 148)) (colE2 ⟨29, by decide⟩ 2 hp)
        (rowE2 (⟨29, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨29, by decide⟩ : Fin 148))
        (colE1 ⟨29, by decide⟩ 2 (transLenTr ⟨29, by decide⟩ 2 hp))
        (rowE1 (⟨29, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨29, by decide⟩ : Fin 148) ⟨29, by decide⟩ _
      (validAt ⟨29, by decide⟩ (listedAt ⟨29, by decide⟩ hj))
      (colE1 ⟨29, by decide⟩ 2 (transLenTr ⟨29, by decide⟩ 2 hp)) T29_29
      hfix29_29 hinj29_29 hcardT29_29
      (fun i => conj_mem_of_fixedPoints _ _ (T29_29 i) (hfix29_29 i) _)
      ⟨29, by decide⟩ ⟨29, by decide⟩ _
      (Q2.validAt ⟨29, by decide⟩ (Q2.listedAt ⟨29, by decide⟩
        (alnCheck_rep ⟨29, by decide⟩ hj hq).1))
      (colE2 ⟨29, by decide⟩ 2 hp) Q2.T29_29_2 Q2.hfix29_29_2 Q2.hinj29_29_2
      Q2.hcardT29_29_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T29_29_2 i) (Q2.hfix29_29_2 i) _)
      ?_).symm
  rw [show colData1 (⟨29, by decide⟩ : Fin 148)
        ((colE1 ⟨29, by decide⟩ 2 (transLenTr ⟨29, by decide⟩ 2 hp) : ↥(reps ⟨29, by decide⟩)) : Coordinate 1)
        T29_29 = colFn colCert_29_29_2.D (m := 25) from colCert_29_29_2.bind1,
    show colData2 (⟨29, by decide⟩ : Fin 148)
        ((colE2 ⟨29, by decide⟩ 2 hp : ↥(Q2.reps ⟨29, by decide⟩)) : Coordinate 2)
        Q2.T29_29_2 = colFn colCert_29_29_2.D (m := 25) from colCert_29_29_2.bind2]
  exact alnAll_29_29_2 j hj hq

theorem leaf_29_29_3 (hp : 3 < (Q2.transData.getD 29 []).length)
    (j : Nat) (hj : j < (repChars.getD 29 []).length)
    (hq : (normIsRep.getD 29 []).getD j false = true) :
    species (Q2.reps (⟨29, by decide⟩ : Fin 148)) (colE2 ⟨29, by decide⟩ 3 hp)
        (rowE2 (⟨29, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨29, by decide⟩ : Fin 148))
        (colE1 ⟨29, by decide⟩ 3 (transLenTr ⟨29, by decide⟩ 3 hp))
        (rowE1 (⟨29, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨29, by decide⟩ : Fin 148) ⟨29, by decide⟩ _
      (validAt ⟨29, by decide⟩ (listedAt ⟨29, by decide⟩ hj))
      (colE1 ⟨29, by decide⟩ 3 (transLenTr ⟨29, by decide⟩ 3 hp)) T29_29
      hfix29_29 hinj29_29 hcardT29_29
      (fun i => conj_mem_of_fixedPoints _ _ (T29_29 i) (hfix29_29 i) _)
      ⟨29, by decide⟩ ⟨29, by decide⟩ _
      (Q2.validAt ⟨29, by decide⟩ (Q2.listedAt ⟨29, by decide⟩
        (alnCheck_rep ⟨29, by decide⟩ hj hq).1))
      (colE2 ⟨29, by decide⟩ 3 hp) Q2.T29_29_2 Q2.hfix29_29_2 Q2.hinj29_29_2
      Q2.hcardT29_29_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T29_29_2 i) (Q2.hfix29_29_2 i) _)
      ?_).symm
  rw [show colData1 (⟨29, by decide⟩ : Fin 148)
        ((colE1 ⟨29, by decide⟩ 3 (transLenTr ⟨29, by decide⟩ 3 hp) : ↥(reps ⟨29, by decide⟩)) : Coordinate 1)
        T29_29 = colFn colCert_29_29_3.D (m := 25) from colCert_29_29_3.bind1,
    show colData2 (⟨29, by decide⟩ : Fin 148)
        ((colE2 ⟨29, by decide⟩ 3 hp : ↥(Q2.reps ⟨29, by decide⟩)) : Coordinate 2)
        Q2.T29_29_2 = colFn colCert_29_29_3.D (m := 25) from colCert_29_29_3.bind2]
  exact alnAll_29_29_3 j hj hq

theorem leaf_29_29_4 (hp : 4 < (Q2.transData.getD 29 []).length)
    (j : Nat) (hj : j < (repChars.getD 29 []).length)
    (hq : (normIsRep.getD 29 []).getD j false = true) :
    species (Q2.reps (⟨29, by decide⟩ : Fin 148)) (colE2 ⟨29, by decide⟩ 4 hp)
        (rowE2 (⟨29, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨29, by decide⟩ : Fin 148))
        (colE1 ⟨29, by decide⟩ 4 (transLenTr ⟨29, by decide⟩ 4 hp))
        (rowE1 (⟨29, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨29, by decide⟩ : Fin 148) ⟨29, by decide⟩ _
      (validAt ⟨29, by decide⟩ (listedAt ⟨29, by decide⟩ hj))
      (colE1 ⟨29, by decide⟩ 4 (transLenTr ⟨29, by decide⟩ 4 hp)) T29_29
      hfix29_29 hinj29_29 hcardT29_29
      (fun i => conj_mem_of_fixedPoints _ _ (T29_29 i) (hfix29_29 i) _)
      ⟨29, by decide⟩ ⟨29, by decide⟩ _
      (Q2.validAt ⟨29, by decide⟩ (Q2.listedAt ⟨29, by decide⟩
        (alnCheck_rep ⟨29, by decide⟩ hj hq).1))
      (colE2 ⟨29, by decide⟩ 4 hp) Q2.T29_29_2 Q2.hfix29_29_2 Q2.hinj29_29_2
      Q2.hcardT29_29_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T29_29_2 i) (Q2.hfix29_29_2 i) _)
      ?_).symm
  rw [show colData1 (⟨29, by decide⟩ : Fin 148)
        ((colE1 ⟨29, by decide⟩ 4 (transLenTr ⟨29, by decide⟩ 4 hp) : ↥(reps ⟨29, by decide⟩)) : Coordinate 1)
        T29_29 = colFn colCert_29_29_4.D (m := 25) from colCert_29_29_4.bind1,
    show colData2 (⟨29, by decide⟩ : Fin 148)
        ((colE2 ⟨29, by decide⟩ 4 hp : ↥(Q2.reps ⟨29, by decide⟩)) : Coordinate 2)
        Q2.T29_29_2 = colFn colCert_29_29_4.D (m := 25) from colCert_29_29_4.bind2]
  exact alnAll_29_29_4 j hj hq

theorem leaf_29_29_5 (hp : 5 < (Q2.transData.getD 29 []).length)
    (j : Nat) (hj : j < (repChars.getD 29 []).length)
    (hq : (normIsRep.getD 29 []).getD j false = true) :
    species (Q2.reps (⟨29, by decide⟩ : Fin 148)) (colE2 ⟨29, by decide⟩ 5 hp)
        (rowE2 (⟨29, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨29, by decide⟩ : Fin 148))
        (colE1 ⟨29, by decide⟩ 5 (transLenTr ⟨29, by decide⟩ 5 hp))
        (rowE1 (⟨29, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨29, by decide⟩ : Fin 148) ⟨29, by decide⟩ _
      (validAt ⟨29, by decide⟩ (listedAt ⟨29, by decide⟩ hj))
      (colE1 ⟨29, by decide⟩ 5 (transLenTr ⟨29, by decide⟩ 5 hp)) T29_29
      hfix29_29 hinj29_29 hcardT29_29
      (fun i => conj_mem_of_fixedPoints _ _ (T29_29 i) (hfix29_29 i) _)
      ⟨29, by decide⟩ ⟨29, by decide⟩ _
      (Q2.validAt ⟨29, by decide⟩ (Q2.listedAt ⟨29, by decide⟩
        (alnCheck_rep ⟨29, by decide⟩ hj hq).1))
      (colE2 ⟨29, by decide⟩ 5 hp) Q2.T29_29_2 Q2.hfix29_29_2 Q2.hinj29_29_2
      Q2.hcardT29_29_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T29_29_2 i) (Q2.hfix29_29_2 i) _)
      ?_).symm
  rw [show colData1 (⟨29, by decide⟩ : Fin 148)
        ((colE1 ⟨29, by decide⟩ 5 (transLenTr ⟨29, by decide⟩ 5 hp) : ↥(reps ⟨29, by decide⟩)) : Coordinate 1)
        T29_29 = colFn colCert_29_29_5.D (m := 25) from colCert_29_29_5.bind1,
    show colData2 (⟨29, by decide⟩ : Fin 148)
        ((colE2 ⟨29, by decide⟩ 5 hp : ↥(Q2.reps ⟨29, by decide⟩)) : Coordinate 2)
        Q2.T29_29_2 = colFn colCert_29_29_5.D (m := 25) from colCert_29_29_5.bind2]
  exact alnAll_29_29_5 j hj hq

theorem leaf_29_29_10 (hp : 10 < (Q2.transData.getD 29 []).length)
    (j : Nat) (hj : j < (repChars.getD 29 []).length)
    (hq : (normIsRep.getD 29 []).getD j false = true) :
    species (Q2.reps (⟨29, by decide⟩ : Fin 148)) (colE2 ⟨29, by decide⟩ 10 hp)
        (rowE2 (⟨29, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨29, by decide⟩ : Fin 148))
        (colE1 ⟨29, by decide⟩ 10 (transLenTr ⟨29, by decide⟩ 10 hp))
        (rowE1 (⟨29, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨29, by decide⟩ : Fin 148) ⟨29, by decide⟩ _
      (validAt ⟨29, by decide⟩ (listedAt ⟨29, by decide⟩ hj))
      (colE1 ⟨29, by decide⟩ 10 (transLenTr ⟨29, by decide⟩ 10 hp)) T29_29
      hfix29_29 hinj29_29 hcardT29_29
      (fun i => conj_mem_of_fixedPoints _ _ (T29_29 i) (hfix29_29 i) _)
      ⟨29, by decide⟩ ⟨29, by decide⟩ _
      (Q2.validAt ⟨29, by decide⟩ (Q2.listedAt ⟨29, by decide⟩
        (alnCheck_rep ⟨29, by decide⟩ hj hq).1))
      (colE2 ⟨29, by decide⟩ 10 hp) Q2.T29_29_2 Q2.hfix29_29_2 Q2.hinj29_29_2
      Q2.hcardT29_29_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T29_29_2 i) (Q2.hfix29_29_2 i) _)
      ?_).symm
  rw [show colData1 (⟨29, by decide⟩ : Fin 148)
        ((colE1 ⟨29, by decide⟩ 10 (transLenTr ⟨29, by decide⟩ 10 hp) : ↥(reps ⟨29, by decide⟩)) : Coordinate 1)
        T29_29 = colFn colCert_29_29_10.D (m := 25) from colCert_29_29_10.bind1,
    show colData2 (⟨29, by decide⟩ : Fin 148)
        ((colE2 ⟨29, by decide⟩ 10 hp : ↥(Q2.reps ⟨29, by decide⟩)) : Coordinate 2)
        Q2.T29_29_2 = colFn colCert_29_29_10.D (m := 25) from colCert_29_29_10.bind2]
  exact alnAll_29_29_10 j hj hq

theorem leaf_29_29_15 (hp : 15 < (Q2.transData.getD 29 []).length)
    (j : Nat) (hj : j < (repChars.getD 29 []).length)
    (hq : (normIsRep.getD 29 []).getD j false = true) :
    species (Q2.reps (⟨29, by decide⟩ : Fin 148)) (colE2 ⟨29, by decide⟩ 15 hp)
        (rowE2 (⟨29, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨29, by decide⟩ : Fin 148))
        (colE1 ⟨29, by decide⟩ 15 (transLenTr ⟨29, by decide⟩ 15 hp))
        (rowE1 (⟨29, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨29, by decide⟩ : Fin 148) ⟨29, by decide⟩ _
      (validAt ⟨29, by decide⟩ (listedAt ⟨29, by decide⟩ hj))
      (colE1 ⟨29, by decide⟩ 15 (transLenTr ⟨29, by decide⟩ 15 hp)) T29_29
      hfix29_29 hinj29_29 hcardT29_29
      (fun i => conj_mem_of_fixedPoints _ _ (T29_29 i) (hfix29_29 i) _)
      ⟨29, by decide⟩ ⟨29, by decide⟩ _
      (Q2.validAt ⟨29, by decide⟩ (Q2.listedAt ⟨29, by decide⟩
        (alnCheck_rep ⟨29, by decide⟩ hj hq).1))
      (colE2 ⟨29, by decide⟩ 15 hp) Q2.T29_29_2 Q2.hfix29_29_2 Q2.hinj29_29_2
      Q2.hcardT29_29_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T29_29_2 i) (Q2.hfix29_29_2 i) _)
      ?_).symm
  rw [show colData1 (⟨29, by decide⟩ : Fin 148)
        ((colE1 ⟨29, by decide⟩ 15 (transLenTr ⟨29, by decide⟩ 15 hp) : ↥(reps ⟨29, by decide⟩)) : Coordinate 1)
        T29_29 = colFn colCert_29_29_15.D (m := 25) from colCert_29_29_15.bind1,
    show colData2 (⟨29, by decide⟩ : Fin 148)
        ((colE2 ⟨29, by decide⟩ 15 hp : ↥(Q2.reps ⟨29, by decide⟩)) : Coordinate 2)
        Q2.T29_29_2 = colFn colCert_29_29_15.D (m := 25) from colCert_29_29_15.bind2]
  exact alnAll_29_29_15 j hj hq

theorem leaf_29_29_20 (hp : 20 < (Q2.transData.getD 29 []).length)
    (j : Nat) (hj : j < (repChars.getD 29 []).length)
    (hq : (normIsRep.getD 29 []).getD j false = true) :
    species (Q2.reps (⟨29, by decide⟩ : Fin 148)) (colE2 ⟨29, by decide⟩ 20 hp)
        (rowE2 (⟨29, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨29, by decide⟩ : Fin 148))
        (colE1 ⟨29, by decide⟩ 20 (transLenTr ⟨29, by decide⟩ 20 hp))
        (rowE1 (⟨29, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨29, by decide⟩ : Fin 148) ⟨29, by decide⟩ _
      (validAt ⟨29, by decide⟩ (listedAt ⟨29, by decide⟩ hj))
      (colE1 ⟨29, by decide⟩ 20 (transLenTr ⟨29, by decide⟩ 20 hp)) T29_29
      hfix29_29 hinj29_29 hcardT29_29
      (fun i => conj_mem_of_fixedPoints _ _ (T29_29 i) (hfix29_29 i) _)
      ⟨29, by decide⟩ ⟨29, by decide⟩ _
      (Q2.validAt ⟨29, by decide⟩ (Q2.listedAt ⟨29, by decide⟩
        (alnCheck_rep ⟨29, by decide⟩ hj hq).1))
      (colE2 ⟨29, by decide⟩ 20 hp) Q2.T29_29_2 Q2.hfix29_29_2 Q2.hinj29_29_2
      Q2.hcardT29_29_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T29_29_2 i) (Q2.hfix29_29_2 i) _)
      ?_).symm
  rw [show colData1 (⟨29, by decide⟩ : Fin 148)
        ((colE1 ⟨29, by decide⟩ 20 (transLenTr ⟨29, by decide⟩ 20 hp) : ↥(reps ⟨29, by decide⟩)) : Coordinate 1)
        T29_29 = colFn colCert_29_29_20.D (m := 25) from colCert_29_29_20.bind1,
    show colData2 (⟨29, by decide⟩ : Fin 148)
        ((colE2 ⟨29, by decide⟩ 20 hp : ↥(Q2.reps ⟨29, by decide⟩)) : Coordinate 2)
        Q2.T29_29_2 = colFn colCert_29_29_20.D (m := 25) from colCert_29_29_20.bind2]
  exact alnAll_29_29_20 j hj hq

theorem leaf_30_12_0 (hp : 0 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 30 []).length)
    (hq : (normIsRep.getD 30 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 0 hp)
        (rowE2 (⟨30, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp))
        (rowE1 (⟨30, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨30, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨30, by decide⟩ (listedAt ⟨30, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp)) T30_12
      hfix30_12 hinj30_12 hcardT30_12
      (fun i => conj_mem_of_fixedPoints _ _ (T30_12 i) (hfix30_12 i) _)
      ⟨30, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨30, by decide⟩ (Q2.listedAt ⟨30, by decide⟩
        (alnCheck_rep ⟨30, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 0 hp) Q2.T30_12_2 Q2.hfix30_12_2 Q2.hinj30_12_2
      Q2.hcardT30_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T30_12_2 i) (Q2.hfix30_12_2 i) _)
      ?_).symm
  rw [show colData1 (⟨30, by decide⟩ : Fin 148)
        ((colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp) : ↥(reps ⟨12, by decide⟩)) : Coordinate 1)
        T30_12 = colFn colCert_30_12_0.D (m := 125) from colCert_30_12_0.bind1,
    show colData2 (⟨30, by decide⟩ : Fin 148)
        ((colE2 ⟨12, by decide⟩ 0 hp : ↥(Q2.reps ⟨12, by decide⟩)) : Coordinate 2)
        Q2.T30_12_2 = colFn colCert_30_12_0.D (m := 125) from colCert_30_12_0.bind2]
  exact alnAll_30_12_0 j hj hq

theorem leaf_30_12_1 (hp : 1 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 30 []).length)
    (hq : (normIsRep.getD 30 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 1 hp)
        (rowE2 (⟨30, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp))
        (rowE1 (⟨30, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨30, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨30, by decide⟩ (listedAt ⟨30, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp)) T30_12
      hfix30_12 hinj30_12 hcardT30_12
      (fun i => conj_mem_of_fixedPoints _ _ (T30_12 i) (hfix30_12 i) _)
      ⟨30, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨30, by decide⟩ (Q2.listedAt ⟨30, by decide⟩
        (alnCheck_rep ⟨30, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 1 hp) Q2.T30_12_2 Q2.hfix30_12_2 Q2.hinj30_12_2
      Q2.hcardT30_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T30_12_2 i) (Q2.hfix30_12_2 i) _)
      ?_).symm
  rw [show colData1 (⟨30, by decide⟩ : Fin 148)
        ((colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp) : ↥(reps ⟨12, by decide⟩)) : Coordinate 1)
        T30_12 = colFn colCert_30_12_1.D (m := 125) from colCert_30_12_1.bind1,
    show colData2 (⟨30, by decide⟩ : Fin 148)
        ((colE2 ⟨12, by decide⟩ 1 hp : ↥(Q2.reps ⟨12, by decide⟩)) : Coordinate 2)
        Q2.T30_12_2 = colFn colCert_30_12_1.D (m := 125) from colCert_30_12_1.bind2]
  exact alnAll_30_12_1 j hj hq

theorem leaf_30_12_2 (hp : 2 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 30 []).length)
    (hq : (normIsRep.getD 30 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 2 hp)
        (rowE2 (⟨30, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp))
        (rowE1 (⟨30, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨30, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨30, by decide⟩ (listedAt ⟨30, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp)) T30_12
      hfix30_12 hinj30_12 hcardT30_12
      (fun i => conj_mem_of_fixedPoints _ _ (T30_12 i) (hfix30_12 i) _)
      ⟨30, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨30, by decide⟩ (Q2.listedAt ⟨30, by decide⟩
        (alnCheck_rep ⟨30, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 2 hp) Q2.T30_12_2 Q2.hfix30_12_2 Q2.hinj30_12_2
      Q2.hcardT30_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T30_12_2 i) (Q2.hfix30_12_2 i) _)
      ?_).symm
  rw [show colData1 (⟨30, by decide⟩ : Fin 148)
        ((colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp) : ↥(reps ⟨12, by decide⟩)) : Coordinate 1)
        T30_12 = colFn colCert_30_12_2.D (m := 125) from colCert_30_12_2.bind1,
    show colData2 (⟨30, by decide⟩ : Fin 148)
        ((colE2 ⟨12, by decide⟩ 2 hp : ↥(Q2.reps ⟨12, by decide⟩)) : Coordinate 2)
        Q2.T30_12_2 = colFn colCert_30_12_2.D (m := 125) from colCert_30_12_2.bind2]
  exact alnAll_30_12_2 j hj hq

theorem leaf_30_12_3 (hp : 3 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 30 []).length)
    (hq : (normIsRep.getD 30 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 3 hp)
        (rowE2 (⟨30, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp))
        (rowE1 (⟨30, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨30, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨30, by decide⟩ (listedAt ⟨30, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp)) T30_12
      hfix30_12 hinj30_12 hcardT30_12
      (fun i => conj_mem_of_fixedPoints _ _ (T30_12 i) (hfix30_12 i) _)
      ⟨30, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨30, by decide⟩ (Q2.listedAt ⟨30, by decide⟩
        (alnCheck_rep ⟨30, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 3 hp) Q2.T30_12_2 Q2.hfix30_12_2 Q2.hinj30_12_2
      Q2.hcardT30_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T30_12_2 i) (Q2.hfix30_12_2 i) _)
      ?_).symm
  rw [show colData1 (⟨30, by decide⟩ : Fin 148)
        ((colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp) : ↥(reps ⟨12, by decide⟩)) : Coordinate 1)
        T30_12 = colFn colCert_30_12_3.D (m := 125) from colCert_30_12_3.bind1,
    show colData2 (⟨30, by decide⟩ : Fin 148)
        ((colE2 ⟨12, by decide⟩ 3 hp : ↥(Q2.reps ⟨12, by decide⟩)) : Coordinate 2)
        Q2.T30_12_2 = colFn colCert_30_12_3.D (m := 125) from colCert_30_12_3.bind2]
  exact alnAll_30_12_3 j hj hq

theorem leaf_30_12_4 (hp : 4 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 30 []).length)
    (hq : (normIsRep.getD 30 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 4 hp)
        (rowE2 (⟨30, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp))
        (rowE1 (⟨30, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨30, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨30, by decide⟩ (listedAt ⟨30, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp)) T30_12
      hfix30_12 hinj30_12 hcardT30_12
      (fun i => conj_mem_of_fixedPoints _ _ (T30_12 i) (hfix30_12 i) _)
      ⟨30, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨30, by decide⟩ (Q2.listedAt ⟨30, by decide⟩
        (alnCheck_rep ⟨30, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 4 hp) Q2.T30_12_2 Q2.hfix30_12_2 Q2.hinj30_12_2
      Q2.hcardT30_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T30_12_2 i) (Q2.hfix30_12_2 i) _)
      ?_).symm
  rw [show colData1 (⟨30, by decide⟩ : Fin 148)
        ((colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp) : ↥(reps ⟨12, by decide⟩)) : Coordinate 1)
        T30_12 = colFn colCert_30_12_4.D (m := 125) from colCert_30_12_4.bind1,
    show colData2 (⟨30, by decide⟩ : Fin 148)
        ((colE2 ⟨12, by decide⟩ 4 hp : ↥(Q2.reps ⟨12, by decide⟩)) : Coordinate 2)
        Q2.T30_12_2 = colFn colCert_30_12_4.D (m := 125) from colCert_30_12_4.bind2]
  exact alnAll_30_12_4 j hj hq

theorem leaf_30_30_0 (hp : 0 < (Q2.transData.getD 30 []).length)
    (j : Nat) (hj : j < (repChars.getD 30 []).length)
    (hq : (normIsRep.getD 30 []).getD j false = true) :
    species (Q2.reps (⟨30, by decide⟩ : Fin 148)) (colE2 ⟨30, by decide⟩ 0 hp)
        (rowE2 (⟨30, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨30, by decide⟩ : Fin 148))
        (colE1 ⟨30, by decide⟩ 0 (transLenTr ⟨30, by decide⟩ 0 hp))
        (rowE1 (⟨30, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨30, by decide⟩ : Fin 148) ⟨30, by decide⟩ _
      (validAt ⟨30, by decide⟩ (listedAt ⟨30, by decide⟩ hj))
      (colE1 ⟨30, by decide⟩ 0 (transLenTr ⟨30, by decide⟩ 0 hp)) T30_30
      hfix30_30 hinj30_30 hcardT30_30
      (fun i => conj_mem_of_fixedPoints _ _ (T30_30 i) (hfix30_30 i) _)
      ⟨30, by decide⟩ ⟨30, by decide⟩ _
      (Q2.validAt ⟨30, by decide⟩ (Q2.listedAt ⟨30, by decide⟩
        (alnCheck_rep ⟨30, by decide⟩ hj hq).1))
      (colE2 ⟨30, by decide⟩ 0 hp) Q2.T30_30_2 Q2.hfix30_30_2 Q2.hinj30_30_2
      Q2.hcardT30_30_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T30_30_2 i) (Q2.hfix30_30_2 i) _)
      ?_).symm
  rw [show colData1 (⟨30, by decide⟩ : Fin 148)
        ((colE1 ⟨30, by decide⟩ 0 (transLenTr ⟨30, by decide⟩ 0 hp) : ↥(reps ⟨30, by decide⟩)) : Coordinate 1)
        T30_30 = colFn colCert_30_30_0.D (m := 25) from colCert_30_30_0.bind1,
    show colData2 (⟨30, by decide⟩ : Fin 148)
        ((colE2 ⟨30, by decide⟩ 0 hp : ↥(Q2.reps ⟨30, by decide⟩)) : Coordinate 2)
        Q2.T30_30_2 = colFn colCert_30_30_0.D (m := 25) from colCert_30_30_0.bind2]
  exact alnAll_30_30_0 j hj hq

theorem leaf_30_30_1 (hp : 1 < (Q2.transData.getD 30 []).length)
    (j : Nat) (hj : j < (repChars.getD 30 []).length)
    (hq : (normIsRep.getD 30 []).getD j false = true) :
    species (Q2.reps (⟨30, by decide⟩ : Fin 148)) (colE2 ⟨30, by decide⟩ 1 hp)
        (rowE2 (⟨30, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨30, by decide⟩ : Fin 148))
        (colE1 ⟨30, by decide⟩ 1 (transLenTr ⟨30, by decide⟩ 1 hp))
        (rowE1 (⟨30, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨30, by decide⟩ : Fin 148) ⟨30, by decide⟩ _
      (validAt ⟨30, by decide⟩ (listedAt ⟨30, by decide⟩ hj))
      (colE1 ⟨30, by decide⟩ 1 (transLenTr ⟨30, by decide⟩ 1 hp)) T30_30
      hfix30_30 hinj30_30 hcardT30_30
      (fun i => conj_mem_of_fixedPoints _ _ (T30_30 i) (hfix30_30 i) _)
      ⟨30, by decide⟩ ⟨30, by decide⟩ _
      (Q2.validAt ⟨30, by decide⟩ (Q2.listedAt ⟨30, by decide⟩
        (alnCheck_rep ⟨30, by decide⟩ hj hq).1))
      (colE2 ⟨30, by decide⟩ 1 hp) Q2.T30_30_2 Q2.hfix30_30_2 Q2.hinj30_30_2
      Q2.hcardT30_30_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T30_30_2 i) (Q2.hfix30_30_2 i) _)
      ?_).symm
  rw [show colData1 (⟨30, by decide⟩ : Fin 148)
        ((colE1 ⟨30, by decide⟩ 1 (transLenTr ⟨30, by decide⟩ 1 hp) : ↥(reps ⟨30, by decide⟩)) : Coordinate 1)
        T30_30 = colFn colCert_30_30_1.D (m := 25) from colCert_30_30_1.bind1,
    show colData2 (⟨30, by decide⟩ : Fin 148)
        ((colE2 ⟨30, by decide⟩ 1 hp : ↥(Q2.reps ⟨30, by decide⟩)) : Coordinate 2)
        Q2.T30_30_2 = colFn colCert_30_30_1.D (m := 25) from colCert_30_30_1.bind2]
  exact alnAll_30_30_1 j hj hq

theorem leaf_30_30_2 (hp : 2 < (Q2.transData.getD 30 []).length)
    (j : Nat) (hj : j < (repChars.getD 30 []).length)
    (hq : (normIsRep.getD 30 []).getD j false = true) :
    species (Q2.reps (⟨30, by decide⟩ : Fin 148)) (colE2 ⟨30, by decide⟩ 2 hp)
        (rowE2 (⟨30, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨30, by decide⟩ : Fin 148))
        (colE1 ⟨30, by decide⟩ 2 (transLenTr ⟨30, by decide⟩ 2 hp))
        (rowE1 (⟨30, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨30, by decide⟩ : Fin 148) ⟨30, by decide⟩ _
      (validAt ⟨30, by decide⟩ (listedAt ⟨30, by decide⟩ hj))
      (colE1 ⟨30, by decide⟩ 2 (transLenTr ⟨30, by decide⟩ 2 hp)) T30_30
      hfix30_30 hinj30_30 hcardT30_30
      (fun i => conj_mem_of_fixedPoints _ _ (T30_30 i) (hfix30_30 i) _)
      ⟨30, by decide⟩ ⟨30, by decide⟩ _
      (Q2.validAt ⟨30, by decide⟩ (Q2.listedAt ⟨30, by decide⟩
        (alnCheck_rep ⟨30, by decide⟩ hj hq).1))
      (colE2 ⟨30, by decide⟩ 2 hp) Q2.T30_30_2 Q2.hfix30_30_2 Q2.hinj30_30_2
      Q2.hcardT30_30_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T30_30_2 i) (Q2.hfix30_30_2 i) _)
      ?_).symm
  rw [show colData1 (⟨30, by decide⟩ : Fin 148)
        ((colE1 ⟨30, by decide⟩ 2 (transLenTr ⟨30, by decide⟩ 2 hp) : ↥(reps ⟨30, by decide⟩)) : Coordinate 1)
        T30_30 = colFn colCert_30_30_2.D (m := 25) from colCert_30_30_2.bind1,
    show colData2 (⟨30, by decide⟩ : Fin 148)
        ((colE2 ⟨30, by decide⟩ 2 hp : ↥(Q2.reps ⟨30, by decide⟩)) : Coordinate 2)
        Q2.T30_30_2 = colFn colCert_30_30_2.D (m := 25) from colCert_30_30_2.bind2]
  exact alnAll_30_30_2 j hj hq

theorem leaf_30_30_3 (hp : 3 < (Q2.transData.getD 30 []).length)
    (j : Nat) (hj : j < (repChars.getD 30 []).length)
    (hq : (normIsRep.getD 30 []).getD j false = true) :
    species (Q2.reps (⟨30, by decide⟩ : Fin 148)) (colE2 ⟨30, by decide⟩ 3 hp)
        (rowE2 (⟨30, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨30, by decide⟩ : Fin 148))
        (colE1 ⟨30, by decide⟩ 3 (transLenTr ⟨30, by decide⟩ 3 hp))
        (rowE1 (⟨30, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨30, by decide⟩ : Fin 148) ⟨30, by decide⟩ _
      (validAt ⟨30, by decide⟩ (listedAt ⟨30, by decide⟩ hj))
      (colE1 ⟨30, by decide⟩ 3 (transLenTr ⟨30, by decide⟩ 3 hp)) T30_30
      hfix30_30 hinj30_30 hcardT30_30
      (fun i => conj_mem_of_fixedPoints _ _ (T30_30 i) (hfix30_30 i) _)
      ⟨30, by decide⟩ ⟨30, by decide⟩ _
      (Q2.validAt ⟨30, by decide⟩ (Q2.listedAt ⟨30, by decide⟩
        (alnCheck_rep ⟨30, by decide⟩ hj hq).1))
      (colE2 ⟨30, by decide⟩ 3 hp) Q2.T30_30_2 Q2.hfix30_30_2 Q2.hinj30_30_2
      Q2.hcardT30_30_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T30_30_2 i) (Q2.hfix30_30_2 i) _)
      ?_).symm
  rw [show colData1 (⟨30, by decide⟩ : Fin 148)
        ((colE1 ⟨30, by decide⟩ 3 (transLenTr ⟨30, by decide⟩ 3 hp) : ↥(reps ⟨30, by decide⟩)) : Coordinate 1)
        T30_30 = colFn colCert_30_30_3.D (m := 25) from colCert_30_30_3.bind1,
    show colData2 (⟨30, by decide⟩ : Fin 148)
        ((colE2 ⟨30, by decide⟩ 3 hp : ↥(Q2.reps ⟨30, by decide⟩)) : Coordinate 2)
        Q2.T30_30_2 = colFn colCert_30_30_3.D (m := 25) from colCert_30_30_3.bind2]
  exact alnAll_30_30_3 j hj hq

theorem leaf_30_30_4 (hp : 4 < (Q2.transData.getD 30 []).length)
    (j : Nat) (hj : j < (repChars.getD 30 []).length)
    (hq : (normIsRep.getD 30 []).getD j false = true) :
    species (Q2.reps (⟨30, by decide⟩ : Fin 148)) (colE2 ⟨30, by decide⟩ 4 hp)
        (rowE2 (⟨30, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨30, by decide⟩ : Fin 148))
        (colE1 ⟨30, by decide⟩ 4 (transLenTr ⟨30, by decide⟩ 4 hp))
        (rowE1 (⟨30, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨30, by decide⟩ : Fin 148) ⟨30, by decide⟩ _
      (validAt ⟨30, by decide⟩ (listedAt ⟨30, by decide⟩ hj))
      (colE1 ⟨30, by decide⟩ 4 (transLenTr ⟨30, by decide⟩ 4 hp)) T30_30
      hfix30_30 hinj30_30 hcardT30_30
      (fun i => conj_mem_of_fixedPoints _ _ (T30_30 i) (hfix30_30 i) _)
      ⟨30, by decide⟩ ⟨30, by decide⟩ _
      (Q2.validAt ⟨30, by decide⟩ (Q2.listedAt ⟨30, by decide⟩
        (alnCheck_rep ⟨30, by decide⟩ hj hq).1))
      (colE2 ⟨30, by decide⟩ 4 hp) Q2.T30_30_2 Q2.hfix30_30_2 Q2.hinj30_30_2
      Q2.hcardT30_30_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T30_30_2 i) (Q2.hfix30_30_2 i) _)
      ?_).symm
  rw [show colData1 (⟨30, by decide⟩ : Fin 148)
        ((colE1 ⟨30, by decide⟩ 4 (transLenTr ⟨30, by decide⟩ 4 hp) : ↥(reps ⟨30, by decide⟩)) : Coordinate 1)
        T30_30 = colFn colCert_30_30_4.D (m := 25) from colCert_30_30_4.bind1,
    show colData2 (⟨30, by decide⟩ : Fin 148)
        ((colE2 ⟨30, by decide⟩ 4 hp : ↥(Q2.reps ⟨30, by decide⟩)) : Coordinate 2)
        Q2.T30_30_2 = colFn colCert_30_30_4.D (m := 25) from colCert_30_30_4.bind2]
  exact alnAll_30_30_4 j hj hq

theorem leaf_30_30_5 (hp : 5 < (Q2.transData.getD 30 []).length)
    (j : Nat) (hj : j < (repChars.getD 30 []).length)
    (hq : (normIsRep.getD 30 []).getD j false = true) :
    species (Q2.reps (⟨30, by decide⟩ : Fin 148)) (colE2 ⟨30, by decide⟩ 5 hp)
        (rowE2 (⟨30, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨30, by decide⟩ : Fin 148))
        (colE1 ⟨30, by decide⟩ 5 (transLenTr ⟨30, by decide⟩ 5 hp))
        (rowE1 (⟨30, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨30, by decide⟩ : Fin 148) ⟨30, by decide⟩ _
      (validAt ⟨30, by decide⟩ (listedAt ⟨30, by decide⟩ hj))
      (colE1 ⟨30, by decide⟩ 5 (transLenTr ⟨30, by decide⟩ 5 hp)) T30_30
      hfix30_30 hinj30_30 hcardT30_30
      (fun i => conj_mem_of_fixedPoints _ _ (T30_30 i) (hfix30_30 i) _)
      ⟨30, by decide⟩ ⟨30, by decide⟩ _
      (Q2.validAt ⟨30, by decide⟩ (Q2.listedAt ⟨30, by decide⟩
        (alnCheck_rep ⟨30, by decide⟩ hj hq).1))
      (colE2 ⟨30, by decide⟩ 5 hp) Q2.T30_30_2 Q2.hfix30_30_2 Q2.hinj30_30_2
      Q2.hcardT30_30_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T30_30_2 i) (Q2.hfix30_30_2 i) _)
      ?_).symm
  rw [show colData1 (⟨30, by decide⟩ : Fin 148)
        ((colE1 ⟨30, by decide⟩ 5 (transLenTr ⟨30, by decide⟩ 5 hp) : ↥(reps ⟨30, by decide⟩)) : Coordinate 1)
        T30_30 = colFn colCert_30_30_5.D (m := 25) from colCert_30_30_5.bind1,
    show colData2 (⟨30, by decide⟩ : Fin 148)
        ((colE2 ⟨30, by decide⟩ 5 hp : ↥(Q2.reps ⟨30, by decide⟩)) : Coordinate 2)
        Q2.T30_30_2 = colFn colCert_30_30_5.D (m := 25) from colCert_30_30_5.bind2]
  exact alnAll_30_30_5 j hj hq

theorem leaf_30_30_10 (hp : 10 < (Q2.transData.getD 30 []).length)
    (j : Nat) (hj : j < (repChars.getD 30 []).length)
    (hq : (normIsRep.getD 30 []).getD j false = true) :
    species (Q2.reps (⟨30, by decide⟩ : Fin 148)) (colE2 ⟨30, by decide⟩ 10 hp)
        (rowE2 (⟨30, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨30, by decide⟩ : Fin 148))
        (colE1 ⟨30, by decide⟩ 10 (transLenTr ⟨30, by decide⟩ 10 hp))
        (rowE1 (⟨30, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨30, by decide⟩ : Fin 148) ⟨30, by decide⟩ _
      (validAt ⟨30, by decide⟩ (listedAt ⟨30, by decide⟩ hj))
      (colE1 ⟨30, by decide⟩ 10 (transLenTr ⟨30, by decide⟩ 10 hp)) T30_30
      hfix30_30 hinj30_30 hcardT30_30
      (fun i => conj_mem_of_fixedPoints _ _ (T30_30 i) (hfix30_30 i) _)
      ⟨30, by decide⟩ ⟨30, by decide⟩ _
      (Q2.validAt ⟨30, by decide⟩ (Q2.listedAt ⟨30, by decide⟩
        (alnCheck_rep ⟨30, by decide⟩ hj hq).1))
      (colE2 ⟨30, by decide⟩ 10 hp) Q2.T30_30_2 Q2.hfix30_30_2 Q2.hinj30_30_2
      Q2.hcardT30_30_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T30_30_2 i) (Q2.hfix30_30_2 i) _)
      ?_).symm
  rw [show colData1 (⟨30, by decide⟩ : Fin 148)
        ((colE1 ⟨30, by decide⟩ 10 (transLenTr ⟨30, by decide⟩ 10 hp) : ↥(reps ⟨30, by decide⟩)) : Coordinate 1)
        T30_30 = colFn colCert_30_30_10.D (m := 25) from colCert_30_30_10.bind1,
    show colData2 (⟨30, by decide⟩ : Fin 148)
        ((colE2 ⟨30, by decide⟩ 10 hp : ↥(Q2.reps ⟨30, by decide⟩)) : Coordinate 2)
        Q2.T30_30_2 = colFn colCert_30_30_10.D (m := 25) from colCert_30_30_10.bind2]
  exact alnAll_30_30_10 j hj hq

theorem leaf_30_30_15 (hp : 15 < (Q2.transData.getD 30 []).length)
    (j : Nat) (hj : j < (repChars.getD 30 []).length)
    (hq : (normIsRep.getD 30 []).getD j false = true) :
    species (Q2.reps (⟨30, by decide⟩ : Fin 148)) (colE2 ⟨30, by decide⟩ 15 hp)
        (rowE2 (⟨30, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨30, by decide⟩ : Fin 148))
        (colE1 ⟨30, by decide⟩ 15 (transLenTr ⟨30, by decide⟩ 15 hp))
        (rowE1 (⟨30, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨30, by decide⟩ : Fin 148) ⟨30, by decide⟩ _
      (validAt ⟨30, by decide⟩ (listedAt ⟨30, by decide⟩ hj))
      (colE1 ⟨30, by decide⟩ 15 (transLenTr ⟨30, by decide⟩ 15 hp)) T30_30
      hfix30_30 hinj30_30 hcardT30_30
      (fun i => conj_mem_of_fixedPoints _ _ (T30_30 i) (hfix30_30 i) _)
      ⟨30, by decide⟩ ⟨30, by decide⟩ _
      (Q2.validAt ⟨30, by decide⟩ (Q2.listedAt ⟨30, by decide⟩
        (alnCheck_rep ⟨30, by decide⟩ hj hq).1))
      (colE2 ⟨30, by decide⟩ 15 hp) Q2.T30_30_2 Q2.hfix30_30_2 Q2.hinj30_30_2
      Q2.hcardT30_30_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T30_30_2 i) (Q2.hfix30_30_2 i) _)
      ?_).symm
  rw [show colData1 (⟨30, by decide⟩ : Fin 148)
        ((colE1 ⟨30, by decide⟩ 15 (transLenTr ⟨30, by decide⟩ 15 hp) : ↥(reps ⟨30, by decide⟩)) : Coordinate 1)
        T30_30 = colFn colCert_30_30_15.D (m := 25) from colCert_30_30_15.bind1,
    show colData2 (⟨30, by decide⟩ : Fin 148)
        ((colE2 ⟨30, by decide⟩ 15 hp : ↥(Q2.reps ⟨30, by decide⟩)) : Coordinate 2)
        Q2.T30_30_2 = colFn colCert_30_30_15.D (m := 25) from colCert_30_30_15.bind2]
  exact alnAll_30_30_15 j hj hq

theorem leaf_30_30_20 (hp : 20 < (Q2.transData.getD 30 []).length)
    (j : Nat) (hj : j < (repChars.getD 30 []).length)
    (hq : (normIsRep.getD 30 []).getD j false = true) :
    species (Q2.reps (⟨30, by decide⟩ : Fin 148)) (colE2 ⟨30, by decide⟩ 20 hp)
        (rowE2 (⟨30, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨30, by decide⟩ : Fin 148))
        (colE1 ⟨30, by decide⟩ 20 (transLenTr ⟨30, by decide⟩ 20 hp))
        (rowE1 (⟨30, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨30, by decide⟩ : Fin 148) ⟨30, by decide⟩ _
      (validAt ⟨30, by decide⟩ (listedAt ⟨30, by decide⟩ hj))
      (colE1 ⟨30, by decide⟩ 20 (transLenTr ⟨30, by decide⟩ 20 hp)) T30_30
      hfix30_30 hinj30_30 hcardT30_30
      (fun i => conj_mem_of_fixedPoints _ _ (T30_30 i) (hfix30_30 i) _)
      ⟨30, by decide⟩ ⟨30, by decide⟩ _
      (Q2.validAt ⟨30, by decide⟩ (Q2.listedAt ⟨30, by decide⟩
        (alnCheck_rep ⟨30, by decide⟩ hj hq).1))
      (colE2 ⟨30, by decide⟩ 20 hp) Q2.T30_30_2 Q2.hfix30_30_2 Q2.hinj30_30_2
      Q2.hcardT30_30_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T30_30_2 i) (Q2.hfix30_30_2 i) _)
      ?_).symm
  rw [show colData1 (⟨30, by decide⟩ : Fin 148)
        ((colE1 ⟨30, by decide⟩ 20 (transLenTr ⟨30, by decide⟩ 20 hp) : ↥(reps ⟨30, by decide⟩)) : Coordinate 1)
        T30_30 = colFn colCert_30_30_20.D (m := 25) from colCert_30_30_20.bind1,
    show colData2 (⟨30, by decide⟩ : Fin 148)
        ((colE2 ⟨30, by decide⟩ 20 hp : ↥(Q2.reps ⟨30, by decide⟩)) : Coordinate 2)
        Q2.T30_30_2 = colFn colCert_30_30_20.D (m := 25) from colCert_30_30_20.bind2]
  exact alnAll_30_30_20 j hj hq

theorem leaf_31_12_0 (hp : 0 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 31 []).length)
    (hq : (normIsRep.getD 31 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 0 hp)
        (rowE2 (⟨31, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp))
        (rowE1 (⟨31, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨31, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨31, by decide⟩ (listedAt ⟨31, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp)) T31_12
      hfix31_12 hinj31_12 hcardT31_12
      (fun i => conj_mem_of_fixedPoints _ _ (T31_12 i) (hfix31_12 i) _)
      ⟨31, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨31, by decide⟩ (Q2.listedAt ⟨31, by decide⟩
        (alnCheck_rep ⟨31, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 0 hp) Q2.T31_12_2 Q2.hfix31_12_2 Q2.hinj31_12_2
      Q2.hcardT31_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T31_12_2 i) (Q2.hfix31_12_2 i) _)
      ?_).symm
  rw [show colData1 (⟨31, by decide⟩ : Fin 148)
        ((colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp) : ↥(reps ⟨12, by decide⟩)) : Coordinate 1)
        T31_12 = colFn colCert_31_12_0.D (m := 125) from colCert_31_12_0.bind1,
    show colData2 (⟨31, by decide⟩ : Fin 148)
        ((colE2 ⟨12, by decide⟩ 0 hp : ↥(Q2.reps ⟨12, by decide⟩)) : Coordinate 2)
        Q2.T31_12_2 = colFn colCert_31_12_0.D (m := 125) from colCert_31_12_0.bind2]
  exact alnAll_31_12_0 j hj hq

theorem leaf_31_12_1 (hp : 1 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 31 []).length)
    (hq : (normIsRep.getD 31 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 1 hp)
        (rowE2 (⟨31, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp))
        (rowE1 (⟨31, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨31, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨31, by decide⟩ (listedAt ⟨31, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp)) T31_12
      hfix31_12 hinj31_12 hcardT31_12
      (fun i => conj_mem_of_fixedPoints _ _ (T31_12 i) (hfix31_12 i) _)
      ⟨31, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨31, by decide⟩ (Q2.listedAt ⟨31, by decide⟩
        (alnCheck_rep ⟨31, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 1 hp) Q2.T31_12_2 Q2.hfix31_12_2 Q2.hinj31_12_2
      Q2.hcardT31_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T31_12_2 i) (Q2.hfix31_12_2 i) _)
      ?_).symm
  rw [show colData1 (⟨31, by decide⟩ : Fin 148)
        ((colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp) : ↥(reps ⟨12, by decide⟩)) : Coordinate 1)
        T31_12 = colFn colCert_31_12_1.D (m := 125) from colCert_31_12_1.bind1,
    show colData2 (⟨31, by decide⟩ : Fin 148)
        ((colE2 ⟨12, by decide⟩ 1 hp : ↥(Q2.reps ⟨12, by decide⟩)) : Coordinate 2)
        Q2.T31_12_2 = colFn colCert_31_12_1.D (m := 125) from colCert_31_12_1.bind2]
  exact alnAll_31_12_1 j hj hq

theorem leaf_31_12_2 (hp : 2 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 31 []).length)
    (hq : (normIsRep.getD 31 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 2 hp)
        (rowE2 (⟨31, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp))
        (rowE1 (⟨31, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨31, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨31, by decide⟩ (listedAt ⟨31, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp)) T31_12
      hfix31_12 hinj31_12 hcardT31_12
      (fun i => conj_mem_of_fixedPoints _ _ (T31_12 i) (hfix31_12 i) _)
      ⟨31, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨31, by decide⟩ (Q2.listedAt ⟨31, by decide⟩
        (alnCheck_rep ⟨31, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 2 hp) Q2.T31_12_2 Q2.hfix31_12_2 Q2.hinj31_12_2
      Q2.hcardT31_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T31_12_2 i) (Q2.hfix31_12_2 i) _)
      ?_).symm
  rw [show colData1 (⟨31, by decide⟩ : Fin 148)
        ((colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp) : ↥(reps ⟨12, by decide⟩)) : Coordinate 1)
        T31_12 = colFn colCert_31_12_2.D (m := 125) from colCert_31_12_2.bind1,
    show colData2 (⟨31, by decide⟩ : Fin 148)
        ((colE2 ⟨12, by decide⟩ 2 hp : ↥(Q2.reps ⟨12, by decide⟩)) : Coordinate 2)
        Q2.T31_12_2 = colFn colCert_31_12_2.D (m := 125) from colCert_31_12_2.bind2]
  exact alnAll_31_12_2 j hj hq

theorem leaf_31_12_3 (hp : 3 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 31 []).length)
    (hq : (normIsRep.getD 31 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 3 hp)
        (rowE2 (⟨31, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp))
        (rowE1 (⟨31, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨31, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨31, by decide⟩ (listedAt ⟨31, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp)) T31_12
      hfix31_12 hinj31_12 hcardT31_12
      (fun i => conj_mem_of_fixedPoints _ _ (T31_12 i) (hfix31_12 i) _)
      ⟨31, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨31, by decide⟩ (Q2.listedAt ⟨31, by decide⟩
        (alnCheck_rep ⟨31, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 3 hp) Q2.T31_12_2 Q2.hfix31_12_2 Q2.hinj31_12_2
      Q2.hcardT31_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T31_12_2 i) (Q2.hfix31_12_2 i) _)
      ?_).symm
  rw [show colData1 (⟨31, by decide⟩ : Fin 148)
        ((colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp) : ↥(reps ⟨12, by decide⟩)) : Coordinate 1)
        T31_12 = colFn colCert_31_12_3.D (m := 125) from colCert_31_12_3.bind1,
    show colData2 (⟨31, by decide⟩ : Fin 148)
        ((colE2 ⟨12, by decide⟩ 3 hp : ↥(Q2.reps ⟨12, by decide⟩)) : Coordinate 2)
        Q2.T31_12_2 = colFn colCert_31_12_3.D (m := 125) from colCert_31_12_3.bind2]
  exact alnAll_31_12_3 j hj hq

theorem leaf_31_12_4 (hp : 4 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 31 []).length)
    (hq : (normIsRep.getD 31 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 4 hp)
        (rowE2 (⟨31, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp))
        (rowE1 (⟨31, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨31, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨31, by decide⟩ (listedAt ⟨31, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp)) T31_12
      hfix31_12 hinj31_12 hcardT31_12
      (fun i => conj_mem_of_fixedPoints _ _ (T31_12 i) (hfix31_12 i) _)
      ⟨31, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨31, by decide⟩ (Q2.listedAt ⟨31, by decide⟩
        (alnCheck_rep ⟨31, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 4 hp) Q2.T31_12_2 Q2.hfix31_12_2 Q2.hinj31_12_2
      Q2.hcardT31_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T31_12_2 i) (Q2.hfix31_12_2 i) _)
      ?_).symm
  rw [show colData1 (⟨31, by decide⟩ : Fin 148)
        ((colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp) : ↥(reps ⟨12, by decide⟩)) : Coordinate 1)
        T31_12 = colFn colCert_31_12_4.D (m := 125) from colCert_31_12_4.bind1,
    show colData2 (⟨31, by decide⟩ : Fin 148)
        ((colE2 ⟨12, by decide⟩ 4 hp : ↥(Q2.reps ⟨12, by decide⟩)) : Coordinate 2)
        Q2.T31_12_2 = colFn colCert_31_12_4.D (m := 125) from colCert_31_12_4.bind2]
  exact alnAll_31_12_4 j hj hq

theorem leaf_31_31_0 (hp : 0 < (Q2.transData.getD 31 []).length)
    (j : Nat) (hj : j < (repChars.getD 31 []).length)
    (hq : (normIsRep.getD 31 []).getD j false = true) :
    species (Q2.reps (⟨31, by decide⟩ : Fin 148)) (colE2 ⟨31, by decide⟩ 0 hp)
        (rowE2 (⟨31, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨31, by decide⟩ : Fin 148))
        (colE1 ⟨31, by decide⟩ 0 (transLenTr ⟨31, by decide⟩ 0 hp))
        (rowE1 (⟨31, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨31, by decide⟩ : Fin 148) ⟨31, by decide⟩ _
      (validAt ⟨31, by decide⟩ (listedAt ⟨31, by decide⟩ hj))
      (colE1 ⟨31, by decide⟩ 0 (transLenTr ⟨31, by decide⟩ 0 hp)) T31_31
      hfix31_31 hinj31_31 hcardT31_31
      (fun i => conj_mem_of_fixedPoints _ _ (T31_31 i) (hfix31_31 i) _)
      ⟨31, by decide⟩ ⟨31, by decide⟩ _
      (Q2.validAt ⟨31, by decide⟩ (Q2.listedAt ⟨31, by decide⟩
        (alnCheck_rep ⟨31, by decide⟩ hj hq).1))
      (colE2 ⟨31, by decide⟩ 0 hp) Q2.T31_31_2 Q2.hfix31_31_2 Q2.hinj31_31_2
      Q2.hcardT31_31_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T31_31_2 i) (Q2.hfix31_31_2 i) _)
      ?_).symm
  rw [show colData1 (⟨31, by decide⟩ : Fin 148)
        ((colE1 ⟨31, by decide⟩ 0 (transLenTr ⟨31, by decide⟩ 0 hp) : ↥(reps ⟨31, by decide⟩)) : Coordinate 1)
        T31_31 = colFn colCert_31_31_0.D (m := 25) from colCert_31_31_0.bind1,
    show colData2 (⟨31, by decide⟩ : Fin 148)
        ((colE2 ⟨31, by decide⟩ 0 hp : ↥(Q2.reps ⟨31, by decide⟩)) : Coordinate 2)
        Q2.T31_31_2 = colFn colCert_31_31_0.D (m := 25) from colCert_31_31_0.bind2]
  exact alnAll_31_31_0 j hj hq

theorem leaf_31_31_1 (hp : 1 < (Q2.transData.getD 31 []).length)
    (j : Nat) (hj : j < (repChars.getD 31 []).length)
    (hq : (normIsRep.getD 31 []).getD j false = true) :
    species (Q2.reps (⟨31, by decide⟩ : Fin 148)) (colE2 ⟨31, by decide⟩ 1 hp)
        (rowE2 (⟨31, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨31, by decide⟩ : Fin 148))
        (colE1 ⟨31, by decide⟩ 1 (transLenTr ⟨31, by decide⟩ 1 hp))
        (rowE1 (⟨31, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨31, by decide⟩ : Fin 148) ⟨31, by decide⟩ _
      (validAt ⟨31, by decide⟩ (listedAt ⟨31, by decide⟩ hj))
      (colE1 ⟨31, by decide⟩ 1 (transLenTr ⟨31, by decide⟩ 1 hp)) T31_31
      hfix31_31 hinj31_31 hcardT31_31
      (fun i => conj_mem_of_fixedPoints _ _ (T31_31 i) (hfix31_31 i) _)
      ⟨31, by decide⟩ ⟨31, by decide⟩ _
      (Q2.validAt ⟨31, by decide⟩ (Q2.listedAt ⟨31, by decide⟩
        (alnCheck_rep ⟨31, by decide⟩ hj hq).1))
      (colE2 ⟨31, by decide⟩ 1 hp) Q2.T31_31_2 Q2.hfix31_31_2 Q2.hinj31_31_2
      Q2.hcardT31_31_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T31_31_2 i) (Q2.hfix31_31_2 i) _)
      ?_).symm
  rw [show colData1 (⟨31, by decide⟩ : Fin 148)
        ((colE1 ⟨31, by decide⟩ 1 (transLenTr ⟨31, by decide⟩ 1 hp) : ↥(reps ⟨31, by decide⟩)) : Coordinate 1)
        T31_31 = colFn colCert_31_31_1.D (m := 25) from colCert_31_31_1.bind1,
    show colData2 (⟨31, by decide⟩ : Fin 148)
        ((colE2 ⟨31, by decide⟩ 1 hp : ↥(Q2.reps ⟨31, by decide⟩)) : Coordinate 2)
        Q2.T31_31_2 = colFn colCert_31_31_1.D (m := 25) from colCert_31_31_1.bind2]
  exact alnAll_31_31_1 j hj hq

theorem leaf_31_31_2 (hp : 2 < (Q2.transData.getD 31 []).length)
    (j : Nat) (hj : j < (repChars.getD 31 []).length)
    (hq : (normIsRep.getD 31 []).getD j false = true) :
    species (Q2.reps (⟨31, by decide⟩ : Fin 148)) (colE2 ⟨31, by decide⟩ 2 hp)
        (rowE2 (⟨31, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨31, by decide⟩ : Fin 148))
        (colE1 ⟨31, by decide⟩ 2 (transLenTr ⟨31, by decide⟩ 2 hp))
        (rowE1 (⟨31, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨31, by decide⟩ : Fin 148) ⟨31, by decide⟩ _
      (validAt ⟨31, by decide⟩ (listedAt ⟨31, by decide⟩ hj))
      (colE1 ⟨31, by decide⟩ 2 (transLenTr ⟨31, by decide⟩ 2 hp)) T31_31
      hfix31_31 hinj31_31 hcardT31_31
      (fun i => conj_mem_of_fixedPoints _ _ (T31_31 i) (hfix31_31 i) _)
      ⟨31, by decide⟩ ⟨31, by decide⟩ _
      (Q2.validAt ⟨31, by decide⟩ (Q2.listedAt ⟨31, by decide⟩
        (alnCheck_rep ⟨31, by decide⟩ hj hq).1))
      (colE2 ⟨31, by decide⟩ 2 hp) Q2.T31_31_2 Q2.hfix31_31_2 Q2.hinj31_31_2
      Q2.hcardT31_31_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T31_31_2 i) (Q2.hfix31_31_2 i) _)
      ?_).symm
  rw [show colData1 (⟨31, by decide⟩ : Fin 148)
        ((colE1 ⟨31, by decide⟩ 2 (transLenTr ⟨31, by decide⟩ 2 hp) : ↥(reps ⟨31, by decide⟩)) : Coordinate 1)
        T31_31 = colFn colCert_31_31_2.D (m := 25) from colCert_31_31_2.bind1,
    show colData2 (⟨31, by decide⟩ : Fin 148)
        ((colE2 ⟨31, by decide⟩ 2 hp : ↥(Q2.reps ⟨31, by decide⟩)) : Coordinate 2)
        Q2.T31_31_2 = colFn colCert_31_31_2.D (m := 25) from colCert_31_31_2.bind2]
  exact alnAll_31_31_2 j hj hq

theorem leaf_31_31_3 (hp : 3 < (Q2.transData.getD 31 []).length)
    (j : Nat) (hj : j < (repChars.getD 31 []).length)
    (hq : (normIsRep.getD 31 []).getD j false = true) :
    species (Q2.reps (⟨31, by decide⟩ : Fin 148)) (colE2 ⟨31, by decide⟩ 3 hp)
        (rowE2 (⟨31, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨31, by decide⟩ : Fin 148))
        (colE1 ⟨31, by decide⟩ 3 (transLenTr ⟨31, by decide⟩ 3 hp))
        (rowE1 (⟨31, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨31, by decide⟩ : Fin 148) ⟨31, by decide⟩ _
      (validAt ⟨31, by decide⟩ (listedAt ⟨31, by decide⟩ hj))
      (colE1 ⟨31, by decide⟩ 3 (transLenTr ⟨31, by decide⟩ 3 hp)) T31_31
      hfix31_31 hinj31_31 hcardT31_31
      (fun i => conj_mem_of_fixedPoints _ _ (T31_31 i) (hfix31_31 i) _)
      ⟨31, by decide⟩ ⟨31, by decide⟩ _
      (Q2.validAt ⟨31, by decide⟩ (Q2.listedAt ⟨31, by decide⟩
        (alnCheck_rep ⟨31, by decide⟩ hj hq).1))
      (colE2 ⟨31, by decide⟩ 3 hp) Q2.T31_31_2 Q2.hfix31_31_2 Q2.hinj31_31_2
      Q2.hcardT31_31_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T31_31_2 i) (Q2.hfix31_31_2 i) _)
      ?_).symm
  rw [show colData1 (⟨31, by decide⟩ : Fin 148)
        ((colE1 ⟨31, by decide⟩ 3 (transLenTr ⟨31, by decide⟩ 3 hp) : ↥(reps ⟨31, by decide⟩)) : Coordinate 1)
        T31_31 = colFn colCert_31_31_3.D (m := 25) from colCert_31_31_3.bind1,
    show colData2 (⟨31, by decide⟩ : Fin 148)
        ((colE2 ⟨31, by decide⟩ 3 hp : ↥(Q2.reps ⟨31, by decide⟩)) : Coordinate 2)
        Q2.T31_31_2 = colFn colCert_31_31_3.D (m := 25) from colCert_31_31_3.bind2]
  exact alnAll_31_31_3 j hj hq

theorem leaf_31_31_4 (hp : 4 < (Q2.transData.getD 31 []).length)
    (j : Nat) (hj : j < (repChars.getD 31 []).length)
    (hq : (normIsRep.getD 31 []).getD j false = true) :
    species (Q2.reps (⟨31, by decide⟩ : Fin 148)) (colE2 ⟨31, by decide⟩ 4 hp)
        (rowE2 (⟨31, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨31, by decide⟩ : Fin 148))
        (colE1 ⟨31, by decide⟩ 4 (transLenTr ⟨31, by decide⟩ 4 hp))
        (rowE1 (⟨31, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨31, by decide⟩ : Fin 148) ⟨31, by decide⟩ _
      (validAt ⟨31, by decide⟩ (listedAt ⟨31, by decide⟩ hj))
      (colE1 ⟨31, by decide⟩ 4 (transLenTr ⟨31, by decide⟩ 4 hp)) T31_31
      hfix31_31 hinj31_31 hcardT31_31
      (fun i => conj_mem_of_fixedPoints _ _ (T31_31 i) (hfix31_31 i) _)
      ⟨31, by decide⟩ ⟨31, by decide⟩ _
      (Q2.validAt ⟨31, by decide⟩ (Q2.listedAt ⟨31, by decide⟩
        (alnCheck_rep ⟨31, by decide⟩ hj hq).1))
      (colE2 ⟨31, by decide⟩ 4 hp) Q2.T31_31_2 Q2.hfix31_31_2 Q2.hinj31_31_2
      Q2.hcardT31_31_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T31_31_2 i) (Q2.hfix31_31_2 i) _)
      ?_).symm
  rw [show colData1 (⟨31, by decide⟩ : Fin 148)
        ((colE1 ⟨31, by decide⟩ 4 (transLenTr ⟨31, by decide⟩ 4 hp) : ↥(reps ⟨31, by decide⟩)) : Coordinate 1)
        T31_31 = colFn colCert_31_31_4.D (m := 25) from colCert_31_31_4.bind1,
    show colData2 (⟨31, by decide⟩ : Fin 148)
        ((colE2 ⟨31, by decide⟩ 4 hp : ↥(Q2.reps ⟨31, by decide⟩)) : Coordinate 2)
        Q2.T31_31_2 = colFn colCert_31_31_4.D (m := 25) from colCert_31_31_4.bind2]
  exact alnAll_31_31_4 j hj hq

theorem leaf_31_31_5 (hp : 5 < (Q2.transData.getD 31 []).length)
    (j : Nat) (hj : j < (repChars.getD 31 []).length)
    (hq : (normIsRep.getD 31 []).getD j false = true) :
    species (Q2.reps (⟨31, by decide⟩ : Fin 148)) (colE2 ⟨31, by decide⟩ 5 hp)
        (rowE2 (⟨31, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨31, by decide⟩ : Fin 148))
        (colE1 ⟨31, by decide⟩ 5 (transLenTr ⟨31, by decide⟩ 5 hp))
        (rowE1 (⟨31, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨31, by decide⟩ : Fin 148) ⟨31, by decide⟩ _
      (validAt ⟨31, by decide⟩ (listedAt ⟨31, by decide⟩ hj))
      (colE1 ⟨31, by decide⟩ 5 (transLenTr ⟨31, by decide⟩ 5 hp)) T31_31
      hfix31_31 hinj31_31 hcardT31_31
      (fun i => conj_mem_of_fixedPoints _ _ (T31_31 i) (hfix31_31 i) _)
      ⟨31, by decide⟩ ⟨31, by decide⟩ _
      (Q2.validAt ⟨31, by decide⟩ (Q2.listedAt ⟨31, by decide⟩
        (alnCheck_rep ⟨31, by decide⟩ hj hq).1))
      (colE2 ⟨31, by decide⟩ 5 hp) Q2.T31_31_2 Q2.hfix31_31_2 Q2.hinj31_31_2
      Q2.hcardT31_31_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T31_31_2 i) (Q2.hfix31_31_2 i) _)
      ?_).symm
  rw [show colData1 (⟨31, by decide⟩ : Fin 148)
        ((colE1 ⟨31, by decide⟩ 5 (transLenTr ⟨31, by decide⟩ 5 hp) : ↥(reps ⟨31, by decide⟩)) : Coordinate 1)
        T31_31 = colFn colCert_31_31_5.D (m := 25) from colCert_31_31_5.bind1,
    show colData2 (⟨31, by decide⟩ : Fin 148)
        ((colE2 ⟨31, by decide⟩ 5 hp : ↥(Q2.reps ⟨31, by decide⟩)) : Coordinate 2)
        Q2.T31_31_2 = colFn colCert_31_31_5.D (m := 25) from colCert_31_31_5.bind2]
  exact alnAll_31_31_5 j hj hq

theorem leaf_31_31_10 (hp : 10 < (Q2.transData.getD 31 []).length)
    (j : Nat) (hj : j < (repChars.getD 31 []).length)
    (hq : (normIsRep.getD 31 []).getD j false = true) :
    species (Q2.reps (⟨31, by decide⟩ : Fin 148)) (colE2 ⟨31, by decide⟩ 10 hp)
        (rowE2 (⟨31, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨31, by decide⟩ : Fin 148))
        (colE1 ⟨31, by decide⟩ 10 (transLenTr ⟨31, by decide⟩ 10 hp))
        (rowE1 (⟨31, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨31, by decide⟩ : Fin 148) ⟨31, by decide⟩ _
      (validAt ⟨31, by decide⟩ (listedAt ⟨31, by decide⟩ hj))
      (colE1 ⟨31, by decide⟩ 10 (transLenTr ⟨31, by decide⟩ 10 hp)) T31_31
      hfix31_31 hinj31_31 hcardT31_31
      (fun i => conj_mem_of_fixedPoints _ _ (T31_31 i) (hfix31_31 i) _)
      ⟨31, by decide⟩ ⟨31, by decide⟩ _
      (Q2.validAt ⟨31, by decide⟩ (Q2.listedAt ⟨31, by decide⟩
        (alnCheck_rep ⟨31, by decide⟩ hj hq).1))
      (colE2 ⟨31, by decide⟩ 10 hp) Q2.T31_31_2 Q2.hfix31_31_2 Q2.hinj31_31_2
      Q2.hcardT31_31_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T31_31_2 i) (Q2.hfix31_31_2 i) _)
      ?_).symm
  rw [show colData1 (⟨31, by decide⟩ : Fin 148)
        ((colE1 ⟨31, by decide⟩ 10 (transLenTr ⟨31, by decide⟩ 10 hp) : ↥(reps ⟨31, by decide⟩)) : Coordinate 1)
        T31_31 = colFn colCert_31_31_10.D (m := 25) from colCert_31_31_10.bind1,
    show colData2 (⟨31, by decide⟩ : Fin 148)
        ((colE2 ⟨31, by decide⟩ 10 hp : ↥(Q2.reps ⟨31, by decide⟩)) : Coordinate 2)
        Q2.T31_31_2 = colFn colCert_31_31_10.D (m := 25) from colCert_31_31_10.bind2]
  exact alnAll_31_31_10 j hj hq

theorem leaf_31_31_15 (hp : 15 < (Q2.transData.getD 31 []).length)
    (j : Nat) (hj : j < (repChars.getD 31 []).length)
    (hq : (normIsRep.getD 31 []).getD j false = true) :
    species (Q2.reps (⟨31, by decide⟩ : Fin 148)) (colE2 ⟨31, by decide⟩ 15 hp)
        (rowE2 (⟨31, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨31, by decide⟩ : Fin 148))
        (colE1 ⟨31, by decide⟩ 15 (transLenTr ⟨31, by decide⟩ 15 hp))
        (rowE1 (⟨31, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨31, by decide⟩ : Fin 148) ⟨31, by decide⟩ _
      (validAt ⟨31, by decide⟩ (listedAt ⟨31, by decide⟩ hj))
      (colE1 ⟨31, by decide⟩ 15 (transLenTr ⟨31, by decide⟩ 15 hp)) T31_31
      hfix31_31 hinj31_31 hcardT31_31
      (fun i => conj_mem_of_fixedPoints _ _ (T31_31 i) (hfix31_31 i) _)
      ⟨31, by decide⟩ ⟨31, by decide⟩ _
      (Q2.validAt ⟨31, by decide⟩ (Q2.listedAt ⟨31, by decide⟩
        (alnCheck_rep ⟨31, by decide⟩ hj hq).1))
      (colE2 ⟨31, by decide⟩ 15 hp) Q2.T31_31_2 Q2.hfix31_31_2 Q2.hinj31_31_2
      Q2.hcardT31_31_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T31_31_2 i) (Q2.hfix31_31_2 i) _)
      ?_).symm
  rw [show colData1 (⟨31, by decide⟩ : Fin 148)
        ((colE1 ⟨31, by decide⟩ 15 (transLenTr ⟨31, by decide⟩ 15 hp) : ↥(reps ⟨31, by decide⟩)) : Coordinate 1)
        T31_31 = colFn colCert_31_31_15.D (m := 25) from colCert_31_31_15.bind1,
    show colData2 (⟨31, by decide⟩ : Fin 148)
        ((colE2 ⟨31, by decide⟩ 15 hp : ↥(Q2.reps ⟨31, by decide⟩)) : Coordinate 2)
        Q2.T31_31_2 = colFn colCert_31_31_15.D (m := 25) from colCert_31_31_15.bind2]
  exact alnAll_31_31_15 j hj hq

theorem leaf_31_31_20 (hp : 20 < (Q2.transData.getD 31 []).length)
    (j : Nat) (hj : j < (repChars.getD 31 []).length)
    (hq : (normIsRep.getD 31 []).getD j false = true) :
    species (Q2.reps (⟨31, by decide⟩ : Fin 148)) (colE2 ⟨31, by decide⟩ 20 hp)
        (rowE2 (⟨31, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨31, by decide⟩ : Fin 148))
        (colE1 ⟨31, by decide⟩ 20 (transLenTr ⟨31, by decide⟩ 20 hp))
        (rowE1 (⟨31, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨31, by decide⟩ : Fin 148) ⟨31, by decide⟩ _
      (validAt ⟨31, by decide⟩ (listedAt ⟨31, by decide⟩ hj))
      (colE1 ⟨31, by decide⟩ 20 (transLenTr ⟨31, by decide⟩ 20 hp)) T31_31
      hfix31_31 hinj31_31 hcardT31_31
      (fun i => conj_mem_of_fixedPoints _ _ (T31_31 i) (hfix31_31 i) _)
      ⟨31, by decide⟩ ⟨31, by decide⟩ _
      (Q2.validAt ⟨31, by decide⟩ (Q2.listedAt ⟨31, by decide⟩
        (alnCheck_rep ⟨31, by decide⟩ hj hq).1))
      (colE2 ⟨31, by decide⟩ 20 hp) Q2.T31_31_2 Q2.hfix31_31_2 Q2.hinj31_31_2
      Q2.hcardT31_31_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T31_31_2 i) (Q2.hfix31_31_2 i) _)
      ?_).symm
  rw [show colData1 (⟨31, by decide⟩ : Fin 148)
        ((colE1 ⟨31, by decide⟩ 20 (transLenTr ⟨31, by decide⟩ 20 hp) : ↥(reps ⟨31, by decide⟩)) : Coordinate 1)
        T31_31 = colFn colCert_31_31_20.D (m := 25) from colCert_31_31_20.bind1,
    show colData2 (⟨31, by decide⟩ : Fin 148)
        ((colE2 ⟨31, by decide⟩ 20 hp : ↥(Q2.reps ⟨31, by decide⟩)) : Coordinate 2)
        Q2.T31_31_2 = colFn colCert_31_31_20.D (m := 25) from colCert_31_31_20.bind2]
  exact alnAll_31_31_20 j hj hq

theorem leaf_32_12_0 (hp : 0 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 32 []).length)
    (hq : (normIsRep.getD 32 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 0 hp)
        (rowE2 (⟨32, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp))
        (rowE1 (⟨32, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨32, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨32, by decide⟩ (listedAt ⟨32, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp)) T32_12
      hfix32_12 hinj32_12 hcardT32_12
      (fun i => conj_mem_of_fixedPoints _ _ (T32_12 i) (hfix32_12 i) _)
      ⟨32, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨32, by decide⟩ (Q2.listedAt ⟨32, by decide⟩
        (alnCheck_rep ⟨32, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 0 hp) Q2.T32_12_2 Q2.hfix32_12_2 Q2.hinj32_12_2
      Q2.hcardT32_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T32_12_2 i) (Q2.hfix32_12_2 i) _)
      ?_).symm
  rw [show colData1 (⟨32, by decide⟩ : Fin 148)
        ((colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp) : ↥(reps ⟨12, by decide⟩)) : Coordinate 1)
        T32_12 = colFn colCert_32_12_0.D (m := 125) from colCert_32_12_0.bind1,
    show colData2 (⟨32, by decide⟩ : Fin 148)
        ((colE2 ⟨12, by decide⟩ 0 hp : ↥(Q2.reps ⟨12, by decide⟩)) : Coordinate 2)
        Q2.T32_12_2 = colFn colCert_32_12_0.D (m := 125) from colCert_32_12_0.bind2]
  exact alnAll_32_12_0 j hj hq

theorem leaf_32_12_1 (hp : 1 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 32 []).length)
    (hq : (normIsRep.getD 32 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 1 hp)
        (rowE2 (⟨32, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp))
        (rowE1 (⟨32, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨32, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨32, by decide⟩ (listedAt ⟨32, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp)) T32_12
      hfix32_12 hinj32_12 hcardT32_12
      (fun i => conj_mem_of_fixedPoints _ _ (T32_12 i) (hfix32_12 i) _)
      ⟨32, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨32, by decide⟩ (Q2.listedAt ⟨32, by decide⟩
        (alnCheck_rep ⟨32, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 1 hp) Q2.T32_12_2 Q2.hfix32_12_2 Q2.hinj32_12_2
      Q2.hcardT32_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T32_12_2 i) (Q2.hfix32_12_2 i) _)
      ?_).symm
  rw [show colData1 (⟨32, by decide⟩ : Fin 148)
        ((colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp) : ↥(reps ⟨12, by decide⟩)) : Coordinate 1)
        T32_12 = colFn colCert_32_12_1.D (m := 125) from colCert_32_12_1.bind1,
    show colData2 (⟨32, by decide⟩ : Fin 148)
        ((colE2 ⟨12, by decide⟩ 1 hp : ↥(Q2.reps ⟨12, by decide⟩)) : Coordinate 2)
        Q2.T32_12_2 = colFn colCert_32_12_1.D (m := 125) from colCert_32_12_1.bind2]
  exact alnAll_32_12_1 j hj hq

theorem leaf_32_12_2 (hp : 2 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 32 []).length)
    (hq : (normIsRep.getD 32 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 2 hp)
        (rowE2 (⟨32, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp))
        (rowE1 (⟨32, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨32, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨32, by decide⟩ (listedAt ⟨32, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp)) T32_12
      hfix32_12 hinj32_12 hcardT32_12
      (fun i => conj_mem_of_fixedPoints _ _ (T32_12 i) (hfix32_12 i) _)
      ⟨32, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨32, by decide⟩ (Q2.listedAt ⟨32, by decide⟩
        (alnCheck_rep ⟨32, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 2 hp) Q2.T32_12_2 Q2.hfix32_12_2 Q2.hinj32_12_2
      Q2.hcardT32_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T32_12_2 i) (Q2.hfix32_12_2 i) _)
      ?_).symm
  rw [show colData1 (⟨32, by decide⟩ : Fin 148)
        ((colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp) : ↥(reps ⟨12, by decide⟩)) : Coordinate 1)
        T32_12 = colFn colCert_32_12_2.D (m := 125) from colCert_32_12_2.bind1,
    show colData2 (⟨32, by decide⟩ : Fin 148)
        ((colE2 ⟨12, by decide⟩ 2 hp : ↥(Q2.reps ⟨12, by decide⟩)) : Coordinate 2)
        Q2.T32_12_2 = colFn colCert_32_12_2.D (m := 125) from colCert_32_12_2.bind2]
  exact alnAll_32_12_2 j hj hq

theorem leaf_32_12_3 (hp : 3 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 32 []).length)
    (hq : (normIsRep.getD 32 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 3 hp)
        (rowE2 (⟨32, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp))
        (rowE1 (⟨32, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨32, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨32, by decide⟩ (listedAt ⟨32, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp)) T32_12
      hfix32_12 hinj32_12 hcardT32_12
      (fun i => conj_mem_of_fixedPoints _ _ (T32_12 i) (hfix32_12 i) _)
      ⟨32, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨32, by decide⟩ (Q2.listedAt ⟨32, by decide⟩
        (alnCheck_rep ⟨32, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 3 hp) Q2.T32_12_2 Q2.hfix32_12_2 Q2.hinj32_12_2
      Q2.hcardT32_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T32_12_2 i) (Q2.hfix32_12_2 i) _)
      ?_).symm
  rw [show colData1 (⟨32, by decide⟩ : Fin 148)
        ((colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp) : ↥(reps ⟨12, by decide⟩)) : Coordinate 1)
        T32_12 = colFn colCert_32_12_3.D (m := 125) from colCert_32_12_3.bind1,
    show colData2 (⟨32, by decide⟩ : Fin 148)
        ((colE2 ⟨12, by decide⟩ 3 hp : ↥(Q2.reps ⟨12, by decide⟩)) : Coordinate 2)
        Q2.T32_12_2 = colFn colCert_32_12_3.D (m := 125) from colCert_32_12_3.bind2]
  exact alnAll_32_12_3 j hj hq

theorem leaf_32_12_4 (hp : 4 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 32 []).length)
    (hq : (normIsRep.getD 32 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 4 hp)
        (rowE2 (⟨32, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp))
        (rowE1 (⟨32, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨32, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨32, by decide⟩ (listedAt ⟨32, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp)) T32_12
      hfix32_12 hinj32_12 hcardT32_12
      (fun i => conj_mem_of_fixedPoints _ _ (T32_12 i) (hfix32_12 i) _)
      ⟨32, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨32, by decide⟩ (Q2.listedAt ⟨32, by decide⟩
        (alnCheck_rep ⟨32, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 4 hp) Q2.T32_12_2 Q2.hfix32_12_2 Q2.hinj32_12_2
      Q2.hcardT32_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T32_12_2 i) (Q2.hfix32_12_2 i) _)
      ?_).symm
  rw [show colData1 (⟨32, by decide⟩ : Fin 148)
        ((colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp) : ↥(reps ⟨12, by decide⟩)) : Coordinate 1)
        T32_12 = colFn colCert_32_12_4.D (m := 125) from colCert_32_12_4.bind1,
    show colData2 (⟨32, by decide⟩ : Fin 148)
        ((colE2 ⟨12, by decide⟩ 4 hp : ↥(Q2.reps ⟨12, by decide⟩)) : Coordinate 2)
        Q2.T32_12_2 = colFn colCert_32_12_4.D (m := 125) from colCert_32_12_4.bind2]
  exact alnAll_32_12_4 j hj hq

theorem leaf_32_32_0 (hp : 0 < (Q2.transData.getD 32 []).length)
    (j : Nat) (hj : j < (repChars.getD 32 []).length)
    (hq : (normIsRep.getD 32 []).getD j false = true) :
    species (Q2.reps (⟨32, by decide⟩ : Fin 148)) (colE2 ⟨32, by decide⟩ 0 hp)
        (rowE2 (⟨32, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨32, by decide⟩ : Fin 148))
        (colE1 ⟨32, by decide⟩ 0 (transLenTr ⟨32, by decide⟩ 0 hp))
        (rowE1 (⟨32, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨32, by decide⟩ : Fin 148) ⟨32, by decide⟩ _
      (validAt ⟨32, by decide⟩ (listedAt ⟨32, by decide⟩ hj))
      (colE1 ⟨32, by decide⟩ 0 (transLenTr ⟨32, by decide⟩ 0 hp)) T32_32
      hfix32_32 hinj32_32 hcardT32_32
      (fun i => conj_mem_of_fixedPoints _ _ (T32_32 i) (hfix32_32 i) _)
      ⟨32, by decide⟩ ⟨32, by decide⟩ _
      (Q2.validAt ⟨32, by decide⟩ (Q2.listedAt ⟨32, by decide⟩
        (alnCheck_rep ⟨32, by decide⟩ hj hq).1))
      (colE2 ⟨32, by decide⟩ 0 hp) Q2.T32_32_2 Q2.hfix32_32_2 Q2.hinj32_32_2
      Q2.hcardT32_32_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T32_32_2 i) (Q2.hfix32_32_2 i) _)
      ?_).symm
  rw [show colData1 (⟨32, by decide⟩ : Fin 148)
        ((colE1 ⟨32, by decide⟩ 0 (transLenTr ⟨32, by decide⟩ 0 hp) : ↥(reps ⟨32, by decide⟩)) : Coordinate 1)
        T32_32 = colFn colCert_32_32_0.D (m := 25) from colCert_32_32_0.bind1,
    show colData2 (⟨32, by decide⟩ : Fin 148)
        ((colE2 ⟨32, by decide⟩ 0 hp : ↥(Q2.reps ⟨32, by decide⟩)) : Coordinate 2)
        Q2.T32_32_2 = colFn colCert_32_32_0.D (m := 25) from colCert_32_32_0.bind2]
  exact alnAll_32_32_0 j hj hq

theorem leaf_32_32_1 (hp : 1 < (Q2.transData.getD 32 []).length)
    (j : Nat) (hj : j < (repChars.getD 32 []).length)
    (hq : (normIsRep.getD 32 []).getD j false = true) :
    species (Q2.reps (⟨32, by decide⟩ : Fin 148)) (colE2 ⟨32, by decide⟩ 1 hp)
        (rowE2 (⟨32, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨32, by decide⟩ : Fin 148))
        (colE1 ⟨32, by decide⟩ 1 (transLenTr ⟨32, by decide⟩ 1 hp))
        (rowE1 (⟨32, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨32, by decide⟩ : Fin 148) ⟨32, by decide⟩ _
      (validAt ⟨32, by decide⟩ (listedAt ⟨32, by decide⟩ hj))
      (colE1 ⟨32, by decide⟩ 1 (transLenTr ⟨32, by decide⟩ 1 hp)) T32_32
      hfix32_32 hinj32_32 hcardT32_32
      (fun i => conj_mem_of_fixedPoints _ _ (T32_32 i) (hfix32_32 i) _)
      ⟨32, by decide⟩ ⟨32, by decide⟩ _
      (Q2.validAt ⟨32, by decide⟩ (Q2.listedAt ⟨32, by decide⟩
        (alnCheck_rep ⟨32, by decide⟩ hj hq).1))
      (colE2 ⟨32, by decide⟩ 1 hp) Q2.T32_32_2 Q2.hfix32_32_2 Q2.hinj32_32_2
      Q2.hcardT32_32_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T32_32_2 i) (Q2.hfix32_32_2 i) _)
      ?_).symm
  rw [show colData1 (⟨32, by decide⟩ : Fin 148)
        ((colE1 ⟨32, by decide⟩ 1 (transLenTr ⟨32, by decide⟩ 1 hp) : ↥(reps ⟨32, by decide⟩)) : Coordinate 1)
        T32_32 = colFn colCert_32_32_1.D (m := 25) from colCert_32_32_1.bind1,
    show colData2 (⟨32, by decide⟩ : Fin 148)
        ((colE2 ⟨32, by decide⟩ 1 hp : ↥(Q2.reps ⟨32, by decide⟩)) : Coordinate 2)
        Q2.T32_32_2 = colFn colCert_32_32_1.D (m := 25) from colCert_32_32_1.bind2]
  exact alnAll_32_32_1 j hj hq

theorem leaf_32_32_2 (hp : 2 < (Q2.transData.getD 32 []).length)
    (j : Nat) (hj : j < (repChars.getD 32 []).length)
    (hq : (normIsRep.getD 32 []).getD j false = true) :
    species (Q2.reps (⟨32, by decide⟩ : Fin 148)) (colE2 ⟨32, by decide⟩ 2 hp)
        (rowE2 (⟨32, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨32, by decide⟩ : Fin 148))
        (colE1 ⟨32, by decide⟩ 2 (transLenTr ⟨32, by decide⟩ 2 hp))
        (rowE1 (⟨32, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨32, by decide⟩ : Fin 148) ⟨32, by decide⟩ _
      (validAt ⟨32, by decide⟩ (listedAt ⟨32, by decide⟩ hj))
      (colE1 ⟨32, by decide⟩ 2 (transLenTr ⟨32, by decide⟩ 2 hp)) T32_32
      hfix32_32 hinj32_32 hcardT32_32
      (fun i => conj_mem_of_fixedPoints _ _ (T32_32 i) (hfix32_32 i) _)
      ⟨32, by decide⟩ ⟨32, by decide⟩ _
      (Q2.validAt ⟨32, by decide⟩ (Q2.listedAt ⟨32, by decide⟩
        (alnCheck_rep ⟨32, by decide⟩ hj hq).1))
      (colE2 ⟨32, by decide⟩ 2 hp) Q2.T32_32_2 Q2.hfix32_32_2 Q2.hinj32_32_2
      Q2.hcardT32_32_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T32_32_2 i) (Q2.hfix32_32_2 i) _)
      ?_).symm
  rw [show colData1 (⟨32, by decide⟩ : Fin 148)
        ((colE1 ⟨32, by decide⟩ 2 (transLenTr ⟨32, by decide⟩ 2 hp) : ↥(reps ⟨32, by decide⟩)) : Coordinate 1)
        T32_32 = colFn colCert_32_32_2.D (m := 25) from colCert_32_32_2.bind1,
    show colData2 (⟨32, by decide⟩ : Fin 148)
        ((colE2 ⟨32, by decide⟩ 2 hp : ↥(Q2.reps ⟨32, by decide⟩)) : Coordinate 2)
        Q2.T32_32_2 = colFn colCert_32_32_2.D (m := 25) from colCert_32_32_2.bind2]
  exact alnAll_32_32_2 j hj hq

theorem leaf_32_32_3 (hp : 3 < (Q2.transData.getD 32 []).length)
    (j : Nat) (hj : j < (repChars.getD 32 []).length)
    (hq : (normIsRep.getD 32 []).getD j false = true) :
    species (Q2.reps (⟨32, by decide⟩ : Fin 148)) (colE2 ⟨32, by decide⟩ 3 hp)
        (rowE2 (⟨32, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨32, by decide⟩ : Fin 148))
        (colE1 ⟨32, by decide⟩ 3 (transLenTr ⟨32, by decide⟩ 3 hp))
        (rowE1 (⟨32, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨32, by decide⟩ : Fin 148) ⟨32, by decide⟩ _
      (validAt ⟨32, by decide⟩ (listedAt ⟨32, by decide⟩ hj))
      (colE1 ⟨32, by decide⟩ 3 (transLenTr ⟨32, by decide⟩ 3 hp)) T32_32
      hfix32_32 hinj32_32 hcardT32_32
      (fun i => conj_mem_of_fixedPoints _ _ (T32_32 i) (hfix32_32 i) _)
      ⟨32, by decide⟩ ⟨32, by decide⟩ _
      (Q2.validAt ⟨32, by decide⟩ (Q2.listedAt ⟨32, by decide⟩
        (alnCheck_rep ⟨32, by decide⟩ hj hq).1))
      (colE2 ⟨32, by decide⟩ 3 hp) Q2.T32_32_2 Q2.hfix32_32_2 Q2.hinj32_32_2
      Q2.hcardT32_32_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T32_32_2 i) (Q2.hfix32_32_2 i) _)
      ?_).symm
  rw [show colData1 (⟨32, by decide⟩ : Fin 148)
        ((colE1 ⟨32, by decide⟩ 3 (transLenTr ⟨32, by decide⟩ 3 hp) : ↥(reps ⟨32, by decide⟩)) : Coordinate 1)
        T32_32 = colFn colCert_32_32_3.D (m := 25) from colCert_32_32_3.bind1,
    show colData2 (⟨32, by decide⟩ : Fin 148)
        ((colE2 ⟨32, by decide⟩ 3 hp : ↥(Q2.reps ⟨32, by decide⟩)) : Coordinate 2)
        Q2.T32_32_2 = colFn colCert_32_32_3.D (m := 25) from colCert_32_32_3.bind2]
  exact alnAll_32_32_3 j hj hq

theorem leaf_32_32_4 (hp : 4 < (Q2.transData.getD 32 []).length)
    (j : Nat) (hj : j < (repChars.getD 32 []).length)
    (hq : (normIsRep.getD 32 []).getD j false = true) :
    species (Q2.reps (⟨32, by decide⟩ : Fin 148)) (colE2 ⟨32, by decide⟩ 4 hp)
        (rowE2 (⟨32, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨32, by decide⟩ : Fin 148))
        (colE1 ⟨32, by decide⟩ 4 (transLenTr ⟨32, by decide⟩ 4 hp))
        (rowE1 (⟨32, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨32, by decide⟩ : Fin 148) ⟨32, by decide⟩ _
      (validAt ⟨32, by decide⟩ (listedAt ⟨32, by decide⟩ hj))
      (colE1 ⟨32, by decide⟩ 4 (transLenTr ⟨32, by decide⟩ 4 hp)) T32_32
      hfix32_32 hinj32_32 hcardT32_32
      (fun i => conj_mem_of_fixedPoints _ _ (T32_32 i) (hfix32_32 i) _)
      ⟨32, by decide⟩ ⟨32, by decide⟩ _
      (Q2.validAt ⟨32, by decide⟩ (Q2.listedAt ⟨32, by decide⟩
        (alnCheck_rep ⟨32, by decide⟩ hj hq).1))
      (colE2 ⟨32, by decide⟩ 4 hp) Q2.T32_32_2 Q2.hfix32_32_2 Q2.hinj32_32_2
      Q2.hcardT32_32_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T32_32_2 i) (Q2.hfix32_32_2 i) _)
      ?_).symm
  rw [show colData1 (⟨32, by decide⟩ : Fin 148)
        ((colE1 ⟨32, by decide⟩ 4 (transLenTr ⟨32, by decide⟩ 4 hp) : ↥(reps ⟨32, by decide⟩)) : Coordinate 1)
        T32_32 = colFn colCert_32_32_4.D (m := 25) from colCert_32_32_4.bind1,
    show colData2 (⟨32, by decide⟩ : Fin 148)
        ((colE2 ⟨32, by decide⟩ 4 hp : ↥(Q2.reps ⟨32, by decide⟩)) : Coordinate 2)
        Q2.T32_32_2 = colFn colCert_32_32_4.D (m := 25) from colCert_32_32_4.bind2]
  exact alnAll_32_32_4 j hj hq

theorem leaf_32_32_5 (hp : 5 < (Q2.transData.getD 32 []).length)
    (j : Nat) (hj : j < (repChars.getD 32 []).length)
    (hq : (normIsRep.getD 32 []).getD j false = true) :
    species (Q2.reps (⟨32, by decide⟩ : Fin 148)) (colE2 ⟨32, by decide⟩ 5 hp)
        (rowE2 (⟨32, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨32, by decide⟩ : Fin 148))
        (colE1 ⟨32, by decide⟩ 5 (transLenTr ⟨32, by decide⟩ 5 hp))
        (rowE1 (⟨32, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨32, by decide⟩ : Fin 148) ⟨32, by decide⟩ _
      (validAt ⟨32, by decide⟩ (listedAt ⟨32, by decide⟩ hj))
      (colE1 ⟨32, by decide⟩ 5 (transLenTr ⟨32, by decide⟩ 5 hp)) T32_32
      hfix32_32 hinj32_32 hcardT32_32
      (fun i => conj_mem_of_fixedPoints _ _ (T32_32 i) (hfix32_32 i) _)
      ⟨32, by decide⟩ ⟨32, by decide⟩ _
      (Q2.validAt ⟨32, by decide⟩ (Q2.listedAt ⟨32, by decide⟩
        (alnCheck_rep ⟨32, by decide⟩ hj hq).1))
      (colE2 ⟨32, by decide⟩ 5 hp) Q2.T32_32_2 Q2.hfix32_32_2 Q2.hinj32_32_2
      Q2.hcardT32_32_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T32_32_2 i) (Q2.hfix32_32_2 i) _)
      ?_).symm
  rw [show colData1 (⟨32, by decide⟩ : Fin 148)
        ((colE1 ⟨32, by decide⟩ 5 (transLenTr ⟨32, by decide⟩ 5 hp) : ↥(reps ⟨32, by decide⟩)) : Coordinate 1)
        T32_32 = colFn colCert_32_32_5.D (m := 25) from colCert_32_32_5.bind1,
    show colData2 (⟨32, by decide⟩ : Fin 148)
        ((colE2 ⟨32, by decide⟩ 5 hp : ↥(Q2.reps ⟨32, by decide⟩)) : Coordinate 2)
        Q2.T32_32_2 = colFn colCert_32_32_5.D (m := 25) from colCert_32_32_5.bind2]
  exact alnAll_32_32_5 j hj hq

theorem leaf_32_32_10 (hp : 10 < (Q2.transData.getD 32 []).length)
    (j : Nat) (hj : j < (repChars.getD 32 []).length)
    (hq : (normIsRep.getD 32 []).getD j false = true) :
    species (Q2.reps (⟨32, by decide⟩ : Fin 148)) (colE2 ⟨32, by decide⟩ 10 hp)
        (rowE2 (⟨32, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨32, by decide⟩ : Fin 148))
        (colE1 ⟨32, by decide⟩ 10 (transLenTr ⟨32, by decide⟩ 10 hp))
        (rowE1 (⟨32, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨32, by decide⟩ : Fin 148) ⟨32, by decide⟩ _
      (validAt ⟨32, by decide⟩ (listedAt ⟨32, by decide⟩ hj))
      (colE1 ⟨32, by decide⟩ 10 (transLenTr ⟨32, by decide⟩ 10 hp)) T32_32
      hfix32_32 hinj32_32 hcardT32_32
      (fun i => conj_mem_of_fixedPoints _ _ (T32_32 i) (hfix32_32 i) _)
      ⟨32, by decide⟩ ⟨32, by decide⟩ _
      (Q2.validAt ⟨32, by decide⟩ (Q2.listedAt ⟨32, by decide⟩
        (alnCheck_rep ⟨32, by decide⟩ hj hq).1))
      (colE2 ⟨32, by decide⟩ 10 hp) Q2.T32_32_2 Q2.hfix32_32_2 Q2.hinj32_32_2
      Q2.hcardT32_32_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T32_32_2 i) (Q2.hfix32_32_2 i) _)
      ?_).symm
  rw [show colData1 (⟨32, by decide⟩ : Fin 148)
        ((colE1 ⟨32, by decide⟩ 10 (transLenTr ⟨32, by decide⟩ 10 hp) : ↥(reps ⟨32, by decide⟩)) : Coordinate 1)
        T32_32 = colFn colCert_32_32_10.D (m := 25) from colCert_32_32_10.bind1,
    show colData2 (⟨32, by decide⟩ : Fin 148)
        ((colE2 ⟨32, by decide⟩ 10 hp : ↥(Q2.reps ⟨32, by decide⟩)) : Coordinate 2)
        Q2.T32_32_2 = colFn colCert_32_32_10.D (m := 25) from colCert_32_32_10.bind2]
  exact alnAll_32_32_10 j hj hq

theorem leaf_32_32_15 (hp : 15 < (Q2.transData.getD 32 []).length)
    (j : Nat) (hj : j < (repChars.getD 32 []).length)
    (hq : (normIsRep.getD 32 []).getD j false = true) :
    species (Q2.reps (⟨32, by decide⟩ : Fin 148)) (colE2 ⟨32, by decide⟩ 15 hp)
        (rowE2 (⟨32, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨32, by decide⟩ : Fin 148))
        (colE1 ⟨32, by decide⟩ 15 (transLenTr ⟨32, by decide⟩ 15 hp))
        (rowE1 (⟨32, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨32, by decide⟩ : Fin 148) ⟨32, by decide⟩ _
      (validAt ⟨32, by decide⟩ (listedAt ⟨32, by decide⟩ hj))
      (colE1 ⟨32, by decide⟩ 15 (transLenTr ⟨32, by decide⟩ 15 hp)) T32_32
      hfix32_32 hinj32_32 hcardT32_32
      (fun i => conj_mem_of_fixedPoints _ _ (T32_32 i) (hfix32_32 i) _)
      ⟨32, by decide⟩ ⟨32, by decide⟩ _
      (Q2.validAt ⟨32, by decide⟩ (Q2.listedAt ⟨32, by decide⟩
        (alnCheck_rep ⟨32, by decide⟩ hj hq).1))
      (colE2 ⟨32, by decide⟩ 15 hp) Q2.T32_32_2 Q2.hfix32_32_2 Q2.hinj32_32_2
      Q2.hcardT32_32_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T32_32_2 i) (Q2.hfix32_32_2 i) _)
      ?_).symm
  rw [show colData1 (⟨32, by decide⟩ : Fin 148)
        ((colE1 ⟨32, by decide⟩ 15 (transLenTr ⟨32, by decide⟩ 15 hp) : ↥(reps ⟨32, by decide⟩)) : Coordinate 1)
        T32_32 = colFn colCert_32_32_15.D (m := 25) from colCert_32_32_15.bind1,
    show colData2 (⟨32, by decide⟩ : Fin 148)
        ((colE2 ⟨32, by decide⟩ 15 hp : ↥(Q2.reps ⟨32, by decide⟩)) : Coordinate 2)
        Q2.T32_32_2 = colFn colCert_32_32_15.D (m := 25) from colCert_32_32_15.bind2]
  exact alnAll_32_32_15 j hj hq

theorem leaf_32_32_20 (hp : 20 < (Q2.transData.getD 32 []).length)
    (j : Nat) (hj : j < (repChars.getD 32 []).length)
    (hq : (normIsRep.getD 32 []).getD j false = true) :
    species (Q2.reps (⟨32, by decide⟩ : Fin 148)) (colE2 ⟨32, by decide⟩ 20 hp)
        (rowE2 (⟨32, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨32, by decide⟩ : Fin 148))
        (colE1 ⟨32, by decide⟩ 20 (transLenTr ⟨32, by decide⟩ 20 hp))
        (rowE1 (⟨32, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨32, by decide⟩ : Fin 148) ⟨32, by decide⟩ _
      (validAt ⟨32, by decide⟩ (listedAt ⟨32, by decide⟩ hj))
      (colE1 ⟨32, by decide⟩ 20 (transLenTr ⟨32, by decide⟩ 20 hp)) T32_32
      hfix32_32 hinj32_32 hcardT32_32
      (fun i => conj_mem_of_fixedPoints _ _ (T32_32 i) (hfix32_32 i) _)
      ⟨32, by decide⟩ ⟨32, by decide⟩ _
      (Q2.validAt ⟨32, by decide⟩ (Q2.listedAt ⟨32, by decide⟩
        (alnCheck_rep ⟨32, by decide⟩ hj hq).1))
      (colE2 ⟨32, by decide⟩ 20 hp) Q2.T32_32_2 Q2.hfix32_32_2 Q2.hinj32_32_2
      Q2.hcardT32_32_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T32_32_2 i) (Q2.hfix32_32_2 i) _)
      ?_).symm
  rw [show colData1 (⟨32, by decide⟩ : Fin 148)
        ((colE1 ⟨32, by decide⟩ 20 (transLenTr ⟨32, by decide⟩ 20 hp) : ↥(reps ⟨32, by decide⟩)) : Coordinate 1)
        T32_32 = colFn colCert_32_32_20.D (m := 25) from colCert_32_32_20.bind1,
    show colData2 (⟨32, by decide⟩ : Fin 148)
        ((colE2 ⟨32, by decide⟩ 20 hp : ↥(Q2.reps ⟨32, by decide⟩)) : Coordinate 2)
        Q2.T32_32_2 = colFn colCert_32_32_20.D (m := 25) from colCert_32_32_20.bind2]
  exact alnAll_32_32_20 j hj hq

theorem leaf_33_12_0 (hp : 0 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 33 []).length)
    (hq : (normIsRep.getD 33 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 0 hp)
        (rowE2 (⟨33, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp))
        (rowE1 (⟨33, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨33, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨33, by decide⟩ (listedAt ⟨33, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp)) T33_12
      hfix33_12 hinj33_12 hcardT33_12
      (fun i => conj_mem_of_fixedPoints _ _ (T33_12 i) (hfix33_12 i) _)
      ⟨33, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨33, by decide⟩ (Q2.listedAt ⟨33, by decide⟩
        (alnCheck_rep ⟨33, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 0 hp) Q2.T33_12_2 Q2.hfix33_12_2 Q2.hinj33_12_2
      Q2.hcardT33_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T33_12_2 i) (Q2.hfix33_12_2 i) _)
      ?_).symm
  rw [show colData1 (⟨33, by decide⟩ : Fin 148)
        ((colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp) : ↥(reps ⟨12, by decide⟩)) : Coordinate 1)
        T33_12 = colFn colCert_33_12_0.D (m := 125) from colCert_33_12_0.bind1,
    show colData2 (⟨33, by decide⟩ : Fin 148)
        ((colE2 ⟨12, by decide⟩ 0 hp : ↥(Q2.reps ⟨12, by decide⟩)) : Coordinate 2)
        Q2.T33_12_2 = colFn colCert_33_12_0.D (m := 125) from colCert_33_12_0.bind2]
  exact alnAll_33_12_0 j hj hq

theorem leaf_33_12_1 (hp : 1 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 33 []).length)
    (hq : (normIsRep.getD 33 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 1 hp)
        (rowE2 (⟨33, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp))
        (rowE1 (⟨33, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨33, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨33, by decide⟩ (listedAt ⟨33, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp)) T33_12
      hfix33_12 hinj33_12 hcardT33_12
      (fun i => conj_mem_of_fixedPoints _ _ (T33_12 i) (hfix33_12 i) _)
      ⟨33, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨33, by decide⟩ (Q2.listedAt ⟨33, by decide⟩
        (alnCheck_rep ⟨33, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 1 hp) Q2.T33_12_2 Q2.hfix33_12_2 Q2.hinj33_12_2
      Q2.hcardT33_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T33_12_2 i) (Q2.hfix33_12_2 i) _)
      ?_).symm
  rw [show colData1 (⟨33, by decide⟩ : Fin 148)
        ((colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp) : ↥(reps ⟨12, by decide⟩)) : Coordinate 1)
        T33_12 = colFn colCert_33_12_1.D (m := 125) from colCert_33_12_1.bind1,
    show colData2 (⟨33, by decide⟩ : Fin 148)
        ((colE2 ⟨12, by decide⟩ 1 hp : ↥(Q2.reps ⟨12, by decide⟩)) : Coordinate 2)
        Q2.T33_12_2 = colFn colCert_33_12_1.D (m := 125) from colCert_33_12_1.bind2]
  exact alnAll_33_12_1 j hj hq

theorem leaf_33_12_2 (hp : 2 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 33 []).length)
    (hq : (normIsRep.getD 33 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 2 hp)
        (rowE2 (⟨33, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp))
        (rowE1 (⟨33, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨33, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨33, by decide⟩ (listedAt ⟨33, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp)) T33_12
      hfix33_12 hinj33_12 hcardT33_12
      (fun i => conj_mem_of_fixedPoints _ _ (T33_12 i) (hfix33_12 i) _)
      ⟨33, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨33, by decide⟩ (Q2.listedAt ⟨33, by decide⟩
        (alnCheck_rep ⟨33, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 2 hp) Q2.T33_12_2 Q2.hfix33_12_2 Q2.hinj33_12_2
      Q2.hcardT33_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T33_12_2 i) (Q2.hfix33_12_2 i) _)
      ?_).symm
  rw [show colData1 (⟨33, by decide⟩ : Fin 148)
        ((colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp) : ↥(reps ⟨12, by decide⟩)) : Coordinate 1)
        T33_12 = colFn colCert_33_12_2.D (m := 125) from colCert_33_12_2.bind1,
    show colData2 (⟨33, by decide⟩ : Fin 148)
        ((colE2 ⟨12, by decide⟩ 2 hp : ↥(Q2.reps ⟨12, by decide⟩)) : Coordinate 2)
        Q2.T33_12_2 = colFn colCert_33_12_2.D (m := 125) from colCert_33_12_2.bind2]
  exact alnAll_33_12_2 j hj hq

theorem leaf_33_12_3 (hp : 3 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 33 []).length)
    (hq : (normIsRep.getD 33 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 3 hp)
        (rowE2 (⟨33, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp))
        (rowE1 (⟨33, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨33, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨33, by decide⟩ (listedAt ⟨33, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp)) T33_12
      hfix33_12 hinj33_12 hcardT33_12
      (fun i => conj_mem_of_fixedPoints _ _ (T33_12 i) (hfix33_12 i) _)
      ⟨33, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨33, by decide⟩ (Q2.listedAt ⟨33, by decide⟩
        (alnCheck_rep ⟨33, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 3 hp) Q2.T33_12_2 Q2.hfix33_12_2 Q2.hinj33_12_2
      Q2.hcardT33_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T33_12_2 i) (Q2.hfix33_12_2 i) _)
      ?_).symm
  rw [show colData1 (⟨33, by decide⟩ : Fin 148)
        ((colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp) : ↥(reps ⟨12, by decide⟩)) : Coordinate 1)
        T33_12 = colFn colCert_33_12_3.D (m := 125) from colCert_33_12_3.bind1,
    show colData2 (⟨33, by decide⟩ : Fin 148)
        ((colE2 ⟨12, by decide⟩ 3 hp : ↥(Q2.reps ⟨12, by decide⟩)) : Coordinate 2)
        Q2.T33_12_2 = colFn colCert_33_12_3.D (m := 125) from colCert_33_12_3.bind2]
  exact alnAll_33_12_3 j hj hq

theorem leaf_33_12_4 (hp : 4 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 33 []).length)
    (hq : (normIsRep.getD 33 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 4 hp)
        (rowE2 (⟨33, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp))
        (rowE1 (⟨33, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨33, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨33, by decide⟩ (listedAt ⟨33, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp)) T33_12
      hfix33_12 hinj33_12 hcardT33_12
      (fun i => conj_mem_of_fixedPoints _ _ (T33_12 i) (hfix33_12 i) _)
      ⟨33, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨33, by decide⟩ (Q2.listedAt ⟨33, by decide⟩
        (alnCheck_rep ⟨33, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 4 hp) Q2.T33_12_2 Q2.hfix33_12_2 Q2.hinj33_12_2
      Q2.hcardT33_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T33_12_2 i) (Q2.hfix33_12_2 i) _)
      ?_).symm
  rw [show colData1 (⟨33, by decide⟩ : Fin 148)
        ((colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp) : ↥(reps ⟨12, by decide⟩)) : Coordinate 1)
        T33_12 = colFn colCert_33_12_4.D (m := 125) from colCert_33_12_4.bind1,
    show colData2 (⟨33, by decide⟩ : Fin 148)
        ((colE2 ⟨12, by decide⟩ 4 hp : ↥(Q2.reps ⟨12, by decide⟩)) : Coordinate 2)
        Q2.T33_12_2 = colFn colCert_33_12_4.D (m := 125) from colCert_33_12_4.bind2]
  exact alnAll_33_12_4 j hj hq

theorem leaf_33_33_0 (hp : 0 < (Q2.transData.getD 33 []).length)
    (j : Nat) (hj : j < (repChars.getD 33 []).length)
    (hq : (normIsRep.getD 33 []).getD j false = true) :
    species (Q2.reps (⟨33, by decide⟩ : Fin 148)) (colE2 ⟨33, by decide⟩ 0 hp)
        (rowE2 (⟨33, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨33, by decide⟩ : Fin 148))
        (colE1 ⟨33, by decide⟩ 0 (transLenTr ⟨33, by decide⟩ 0 hp))
        (rowE1 (⟨33, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨33, by decide⟩ : Fin 148) ⟨33, by decide⟩ _
      (validAt ⟨33, by decide⟩ (listedAt ⟨33, by decide⟩ hj))
      (colE1 ⟨33, by decide⟩ 0 (transLenTr ⟨33, by decide⟩ 0 hp)) T33_33
      hfix33_33 hinj33_33 hcardT33_33
      (fun i => conj_mem_of_fixedPoints _ _ (T33_33 i) (hfix33_33 i) _)
      ⟨33, by decide⟩ ⟨33, by decide⟩ _
      (Q2.validAt ⟨33, by decide⟩ (Q2.listedAt ⟨33, by decide⟩
        (alnCheck_rep ⟨33, by decide⟩ hj hq).1))
      (colE2 ⟨33, by decide⟩ 0 hp) Q2.T33_33_2 Q2.hfix33_33_2 Q2.hinj33_33_2
      Q2.hcardT33_33_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T33_33_2 i) (Q2.hfix33_33_2 i) _)
      ?_).symm
  rw [show colData1 (⟨33, by decide⟩ : Fin 148)
        ((colE1 ⟨33, by decide⟩ 0 (transLenTr ⟨33, by decide⟩ 0 hp) : ↥(reps ⟨33, by decide⟩)) : Coordinate 1)
        T33_33 = colFn colCert_33_33_0.D (m := 25) from colCert_33_33_0.bind1,
    show colData2 (⟨33, by decide⟩ : Fin 148)
        ((colE2 ⟨33, by decide⟩ 0 hp : ↥(Q2.reps ⟨33, by decide⟩)) : Coordinate 2)
        Q2.T33_33_2 = colFn colCert_33_33_0.D (m := 25) from colCert_33_33_0.bind2]
  exact alnAll_33_33_0 j hj hq

theorem leaf_33_33_1 (hp : 1 < (Q2.transData.getD 33 []).length)
    (j : Nat) (hj : j < (repChars.getD 33 []).length)
    (hq : (normIsRep.getD 33 []).getD j false = true) :
    species (Q2.reps (⟨33, by decide⟩ : Fin 148)) (colE2 ⟨33, by decide⟩ 1 hp)
        (rowE2 (⟨33, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨33, by decide⟩ : Fin 148))
        (colE1 ⟨33, by decide⟩ 1 (transLenTr ⟨33, by decide⟩ 1 hp))
        (rowE1 (⟨33, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨33, by decide⟩ : Fin 148) ⟨33, by decide⟩ _
      (validAt ⟨33, by decide⟩ (listedAt ⟨33, by decide⟩ hj))
      (colE1 ⟨33, by decide⟩ 1 (transLenTr ⟨33, by decide⟩ 1 hp)) T33_33
      hfix33_33 hinj33_33 hcardT33_33
      (fun i => conj_mem_of_fixedPoints _ _ (T33_33 i) (hfix33_33 i) _)
      ⟨33, by decide⟩ ⟨33, by decide⟩ _
      (Q2.validAt ⟨33, by decide⟩ (Q2.listedAt ⟨33, by decide⟩
        (alnCheck_rep ⟨33, by decide⟩ hj hq).1))
      (colE2 ⟨33, by decide⟩ 1 hp) Q2.T33_33_2 Q2.hfix33_33_2 Q2.hinj33_33_2
      Q2.hcardT33_33_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T33_33_2 i) (Q2.hfix33_33_2 i) _)
      ?_).symm
  rw [show colData1 (⟨33, by decide⟩ : Fin 148)
        ((colE1 ⟨33, by decide⟩ 1 (transLenTr ⟨33, by decide⟩ 1 hp) : ↥(reps ⟨33, by decide⟩)) : Coordinate 1)
        T33_33 = colFn colCert_33_33_1.D (m := 25) from colCert_33_33_1.bind1,
    show colData2 (⟨33, by decide⟩ : Fin 148)
        ((colE2 ⟨33, by decide⟩ 1 hp : ↥(Q2.reps ⟨33, by decide⟩)) : Coordinate 2)
        Q2.T33_33_2 = colFn colCert_33_33_1.D (m := 25) from colCert_33_33_1.bind2]
  exact alnAll_33_33_1 j hj hq

theorem leaf_33_33_2 (hp : 2 < (Q2.transData.getD 33 []).length)
    (j : Nat) (hj : j < (repChars.getD 33 []).length)
    (hq : (normIsRep.getD 33 []).getD j false = true) :
    species (Q2.reps (⟨33, by decide⟩ : Fin 148)) (colE2 ⟨33, by decide⟩ 2 hp)
        (rowE2 (⟨33, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨33, by decide⟩ : Fin 148))
        (colE1 ⟨33, by decide⟩ 2 (transLenTr ⟨33, by decide⟩ 2 hp))
        (rowE1 (⟨33, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨33, by decide⟩ : Fin 148) ⟨33, by decide⟩ _
      (validAt ⟨33, by decide⟩ (listedAt ⟨33, by decide⟩ hj))
      (colE1 ⟨33, by decide⟩ 2 (transLenTr ⟨33, by decide⟩ 2 hp)) T33_33
      hfix33_33 hinj33_33 hcardT33_33
      (fun i => conj_mem_of_fixedPoints _ _ (T33_33 i) (hfix33_33 i) _)
      ⟨33, by decide⟩ ⟨33, by decide⟩ _
      (Q2.validAt ⟨33, by decide⟩ (Q2.listedAt ⟨33, by decide⟩
        (alnCheck_rep ⟨33, by decide⟩ hj hq).1))
      (colE2 ⟨33, by decide⟩ 2 hp) Q2.T33_33_2 Q2.hfix33_33_2 Q2.hinj33_33_2
      Q2.hcardT33_33_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T33_33_2 i) (Q2.hfix33_33_2 i) _)
      ?_).symm
  rw [show colData1 (⟨33, by decide⟩ : Fin 148)
        ((colE1 ⟨33, by decide⟩ 2 (transLenTr ⟨33, by decide⟩ 2 hp) : ↥(reps ⟨33, by decide⟩)) : Coordinate 1)
        T33_33 = colFn colCert_33_33_2.D (m := 25) from colCert_33_33_2.bind1,
    show colData2 (⟨33, by decide⟩ : Fin 148)
        ((colE2 ⟨33, by decide⟩ 2 hp : ↥(Q2.reps ⟨33, by decide⟩)) : Coordinate 2)
        Q2.T33_33_2 = colFn colCert_33_33_2.D (m := 25) from colCert_33_33_2.bind2]
  exact alnAll_33_33_2 j hj hq

theorem leaf_33_33_3 (hp : 3 < (Q2.transData.getD 33 []).length)
    (j : Nat) (hj : j < (repChars.getD 33 []).length)
    (hq : (normIsRep.getD 33 []).getD j false = true) :
    species (Q2.reps (⟨33, by decide⟩ : Fin 148)) (colE2 ⟨33, by decide⟩ 3 hp)
        (rowE2 (⟨33, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨33, by decide⟩ : Fin 148))
        (colE1 ⟨33, by decide⟩ 3 (transLenTr ⟨33, by decide⟩ 3 hp))
        (rowE1 (⟨33, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨33, by decide⟩ : Fin 148) ⟨33, by decide⟩ _
      (validAt ⟨33, by decide⟩ (listedAt ⟨33, by decide⟩ hj))
      (colE1 ⟨33, by decide⟩ 3 (transLenTr ⟨33, by decide⟩ 3 hp)) T33_33
      hfix33_33 hinj33_33 hcardT33_33
      (fun i => conj_mem_of_fixedPoints _ _ (T33_33 i) (hfix33_33 i) _)
      ⟨33, by decide⟩ ⟨33, by decide⟩ _
      (Q2.validAt ⟨33, by decide⟩ (Q2.listedAt ⟨33, by decide⟩
        (alnCheck_rep ⟨33, by decide⟩ hj hq).1))
      (colE2 ⟨33, by decide⟩ 3 hp) Q2.T33_33_2 Q2.hfix33_33_2 Q2.hinj33_33_2
      Q2.hcardT33_33_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T33_33_2 i) (Q2.hfix33_33_2 i) _)
      ?_).symm
  rw [show colData1 (⟨33, by decide⟩ : Fin 148)
        ((colE1 ⟨33, by decide⟩ 3 (transLenTr ⟨33, by decide⟩ 3 hp) : ↥(reps ⟨33, by decide⟩)) : Coordinate 1)
        T33_33 = colFn colCert_33_33_3.D (m := 25) from colCert_33_33_3.bind1,
    show colData2 (⟨33, by decide⟩ : Fin 148)
        ((colE2 ⟨33, by decide⟩ 3 hp : ↥(Q2.reps ⟨33, by decide⟩)) : Coordinate 2)
        Q2.T33_33_2 = colFn colCert_33_33_3.D (m := 25) from colCert_33_33_3.bind2]
  exact alnAll_33_33_3 j hj hq

theorem leaf_33_33_4 (hp : 4 < (Q2.transData.getD 33 []).length)
    (j : Nat) (hj : j < (repChars.getD 33 []).length)
    (hq : (normIsRep.getD 33 []).getD j false = true) :
    species (Q2.reps (⟨33, by decide⟩ : Fin 148)) (colE2 ⟨33, by decide⟩ 4 hp)
        (rowE2 (⟨33, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨33, by decide⟩ : Fin 148))
        (colE1 ⟨33, by decide⟩ 4 (transLenTr ⟨33, by decide⟩ 4 hp))
        (rowE1 (⟨33, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨33, by decide⟩ : Fin 148) ⟨33, by decide⟩ _
      (validAt ⟨33, by decide⟩ (listedAt ⟨33, by decide⟩ hj))
      (colE1 ⟨33, by decide⟩ 4 (transLenTr ⟨33, by decide⟩ 4 hp)) T33_33
      hfix33_33 hinj33_33 hcardT33_33
      (fun i => conj_mem_of_fixedPoints _ _ (T33_33 i) (hfix33_33 i) _)
      ⟨33, by decide⟩ ⟨33, by decide⟩ _
      (Q2.validAt ⟨33, by decide⟩ (Q2.listedAt ⟨33, by decide⟩
        (alnCheck_rep ⟨33, by decide⟩ hj hq).1))
      (colE2 ⟨33, by decide⟩ 4 hp) Q2.T33_33_2 Q2.hfix33_33_2 Q2.hinj33_33_2
      Q2.hcardT33_33_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T33_33_2 i) (Q2.hfix33_33_2 i) _)
      ?_).symm
  rw [show colData1 (⟨33, by decide⟩ : Fin 148)
        ((colE1 ⟨33, by decide⟩ 4 (transLenTr ⟨33, by decide⟩ 4 hp) : ↥(reps ⟨33, by decide⟩)) : Coordinate 1)
        T33_33 = colFn colCert_33_33_4.D (m := 25) from colCert_33_33_4.bind1,
    show colData2 (⟨33, by decide⟩ : Fin 148)
        ((colE2 ⟨33, by decide⟩ 4 hp : ↥(Q2.reps ⟨33, by decide⟩)) : Coordinate 2)
        Q2.T33_33_2 = colFn colCert_33_33_4.D (m := 25) from colCert_33_33_4.bind2]
  exact alnAll_33_33_4 j hj hq

theorem leaf_33_33_5 (hp : 5 < (Q2.transData.getD 33 []).length)
    (j : Nat) (hj : j < (repChars.getD 33 []).length)
    (hq : (normIsRep.getD 33 []).getD j false = true) :
    species (Q2.reps (⟨33, by decide⟩ : Fin 148)) (colE2 ⟨33, by decide⟩ 5 hp)
        (rowE2 (⟨33, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨33, by decide⟩ : Fin 148))
        (colE1 ⟨33, by decide⟩ 5 (transLenTr ⟨33, by decide⟩ 5 hp))
        (rowE1 (⟨33, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨33, by decide⟩ : Fin 148) ⟨33, by decide⟩ _
      (validAt ⟨33, by decide⟩ (listedAt ⟨33, by decide⟩ hj))
      (colE1 ⟨33, by decide⟩ 5 (transLenTr ⟨33, by decide⟩ 5 hp)) T33_33
      hfix33_33 hinj33_33 hcardT33_33
      (fun i => conj_mem_of_fixedPoints _ _ (T33_33 i) (hfix33_33 i) _)
      ⟨33, by decide⟩ ⟨33, by decide⟩ _
      (Q2.validAt ⟨33, by decide⟩ (Q2.listedAt ⟨33, by decide⟩
        (alnCheck_rep ⟨33, by decide⟩ hj hq).1))
      (colE2 ⟨33, by decide⟩ 5 hp) Q2.T33_33_2 Q2.hfix33_33_2 Q2.hinj33_33_2
      Q2.hcardT33_33_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T33_33_2 i) (Q2.hfix33_33_2 i) _)
      ?_).symm
  rw [show colData1 (⟨33, by decide⟩ : Fin 148)
        ((colE1 ⟨33, by decide⟩ 5 (transLenTr ⟨33, by decide⟩ 5 hp) : ↥(reps ⟨33, by decide⟩)) : Coordinate 1)
        T33_33 = colFn colCert_33_33_5.D (m := 25) from colCert_33_33_5.bind1,
    show colData2 (⟨33, by decide⟩ : Fin 148)
        ((colE2 ⟨33, by decide⟩ 5 hp : ↥(Q2.reps ⟨33, by decide⟩)) : Coordinate 2)
        Q2.T33_33_2 = colFn colCert_33_33_5.D (m := 25) from colCert_33_33_5.bind2]
  exact alnAll_33_33_5 j hj hq

theorem leaf_33_33_10 (hp : 10 < (Q2.transData.getD 33 []).length)
    (j : Nat) (hj : j < (repChars.getD 33 []).length)
    (hq : (normIsRep.getD 33 []).getD j false = true) :
    species (Q2.reps (⟨33, by decide⟩ : Fin 148)) (colE2 ⟨33, by decide⟩ 10 hp)
        (rowE2 (⟨33, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨33, by decide⟩ : Fin 148))
        (colE1 ⟨33, by decide⟩ 10 (transLenTr ⟨33, by decide⟩ 10 hp))
        (rowE1 (⟨33, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨33, by decide⟩ : Fin 148) ⟨33, by decide⟩ _
      (validAt ⟨33, by decide⟩ (listedAt ⟨33, by decide⟩ hj))
      (colE1 ⟨33, by decide⟩ 10 (transLenTr ⟨33, by decide⟩ 10 hp)) T33_33
      hfix33_33 hinj33_33 hcardT33_33
      (fun i => conj_mem_of_fixedPoints _ _ (T33_33 i) (hfix33_33 i) _)
      ⟨33, by decide⟩ ⟨33, by decide⟩ _
      (Q2.validAt ⟨33, by decide⟩ (Q2.listedAt ⟨33, by decide⟩
        (alnCheck_rep ⟨33, by decide⟩ hj hq).1))
      (colE2 ⟨33, by decide⟩ 10 hp) Q2.T33_33_2 Q2.hfix33_33_2 Q2.hinj33_33_2
      Q2.hcardT33_33_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T33_33_2 i) (Q2.hfix33_33_2 i) _)
      ?_).symm
  rw [show colData1 (⟨33, by decide⟩ : Fin 148)
        ((colE1 ⟨33, by decide⟩ 10 (transLenTr ⟨33, by decide⟩ 10 hp) : ↥(reps ⟨33, by decide⟩)) : Coordinate 1)
        T33_33 = colFn colCert_33_33_10.D (m := 25) from colCert_33_33_10.bind1,
    show colData2 (⟨33, by decide⟩ : Fin 148)
        ((colE2 ⟨33, by decide⟩ 10 hp : ↥(Q2.reps ⟨33, by decide⟩)) : Coordinate 2)
        Q2.T33_33_2 = colFn colCert_33_33_10.D (m := 25) from colCert_33_33_10.bind2]
  exact alnAll_33_33_10 j hj hq

theorem leaf_33_33_15 (hp : 15 < (Q2.transData.getD 33 []).length)
    (j : Nat) (hj : j < (repChars.getD 33 []).length)
    (hq : (normIsRep.getD 33 []).getD j false = true) :
    species (Q2.reps (⟨33, by decide⟩ : Fin 148)) (colE2 ⟨33, by decide⟩ 15 hp)
        (rowE2 (⟨33, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨33, by decide⟩ : Fin 148))
        (colE1 ⟨33, by decide⟩ 15 (transLenTr ⟨33, by decide⟩ 15 hp))
        (rowE1 (⟨33, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨33, by decide⟩ : Fin 148) ⟨33, by decide⟩ _
      (validAt ⟨33, by decide⟩ (listedAt ⟨33, by decide⟩ hj))
      (colE1 ⟨33, by decide⟩ 15 (transLenTr ⟨33, by decide⟩ 15 hp)) T33_33
      hfix33_33 hinj33_33 hcardT33_33
      (fun i => conj_mem_of_fixedPoints _ _ (T33_33 i) (hfix33_33 i) _)
      ⟨33, by decide⟩ ⟨33, by decide⟩ _
      (Q2.validAt ⟨33, by decide⟩ (Q2.listedAt ⟨33, by decide⟩
        (alnCheck_rep ⟨33, by decide⟩ hj hq).1))
      (colE2 ⟨33, by decide⟩ 15 hp) Q2.T33_33_2 Q2.hfix33_33_2 Q2.hinj33_33_2
      Q2.hcardT33_33_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T33_33_2 i) (Q2.hfix33_33_2 i) _)
      ?_).symm
  rw [show colData1 (⟨33, by decide⟩ : Fin 148)
        ((colE1 ⟨33, by decide⟩ 15 (transLenTr ⟨33, by decide⟩ 15 hp) : ↥(reps ⟨33, by decide⟩)) : Coordinate 1)
        T33_33 = colFn colCert_33_33_15.D (m := 25) from colCert_33_33_15.bind1,
    show colData2 (⟨33, by decide⟩ : Fin 148)
        ((colE2 ⟨33, by decide⟩ 15 hp : ↥(Q2.reps ⟨33, by decide⟩)) : Coordinate 2)
        Q2.T33_33_2 = colFn colCert_33_33_15.D (m := 25) from colCert_33_33_15.bind2]
  exact alnAll_33_33_15 j hj hq

theorem leaf_33_33_20 (hp : 20 < (Q2.transData.getD 33 []).length)
    (j : Nat) (hj : j < (repChars.getD 33 []).length)
    (hq : (normIsRep.getD 33 []).getD j false = true) :
    species (Q2.reps (⟨33, by decide⟩ : Fin 148)) (colE2 ⟨33, by decide⟩ 20 hp)
        (rowE2 (⟨33, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨33, by decide⟩ : Fin 148))
        (colE1 ⟨33, by decide⟩ 20 (transLenTr ⟨33, by decide⟩ 20 hp))
        (rowE1 (⟨33, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨33, by decide⟩ : Fin 148) ⟨33, by decide⟩ _
      (validAt ⟨33, by decide⟩ (listedAt ⟨33, by decide⟩ hj))
      (colE1 ⟨33, by decide⟩ 20 (transLenTr ⟨33, by decide⟩ 20 hp)) T33_33
      hfix33_33 hinj33_33 hcardT33_33
      (fun i => conj_mem_of_fixedPoints _ _ (T33_33 i) (hfix33_33 i) _)
      ⟨33, by decide⟩ ⟨33, by decide⟩ _
      (Q2.validAt ⟨33, by decide⟩ (Q2.listedAt ⟨33, by decide⟩
        (alnCheck_rep ⟨33, by decide⟩ hj hq).1))
      (colE2 ⟨33, by decide⟩ 20 hp) Q2.T33_33_2 Q2.hfix33_33_2 Q2.hinj33_33_2
      Q2.hcardT33_33_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T33_33_2 i) (Q2.hfix33_33_2 i) _)
      ?_).symm
  rw [show colData1 (⟨33, by decide⟩ : Fin 148)
        ((colE1 ⟨33, by decide⟩ 20 (transLenTr ⟨33, by decide⟩ 20 hp) : ↥(reps ⟨33, by decide⟩)) : Coordinate 1)
        T33_33 = colFn colCert_33_33_20.D (m := 25) from colCert_33_33_20.bind1,
    show colData2 (⟨33, by decide⟩ : Fin 148)
        ((colE2 ⟨33, by decide⟩ 20 hp : ↥(Q2.reps ⟨33, by decide⟩)) : Coordinate 2)
        Q2.T33_33_2 = colFn colCert_33_33_20.D (m := 25) from colCert_33_33_20.bind2]
  exact alnAll_33_33_20 j hj hq

theorem leaf_34_12_0 (hp : 0 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 34 []).length)
    (hq : (normIsRep.getD 34 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 0 hp)
        (rowE2 (⟨34, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp))
        (rowE1 (⟨34, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨34, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨34, by decide⟩ (listedAt ⟨34, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp)) T34_12
      hfix34_12 hinj34_12 hcardT34_12
      (fun i => conj_mem_of_fixedPoints _ _ (T34_12 i) (hfix34_12 i) _)
      ⟨34, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨34, by decide⟩ (Q2.listedAt ⟨34, by decide⟩
        (alnCheck_rep ⟨34, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 0 hp) Q2.T34_12_2 Q2.hfix34_12_2 Q2.hinj34_12_2
      Q2.hcardT34_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T34_12_2 i) (Q2.hfix34_12_2 i) _)
      ?_).symm
  rw [show colData1 (⟨34, by decide⟩ : Fin 148)
        ((colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp) : ↥(reps ⟨12, by decide⟩)) : Coordinate 1)
        T34_12 = colFn colCert_34_12_0.D (m := 125) from colCert_34_12_0.bind1,
    show colData2 (⟨34, by decide⟩ : Fin 148)
        ((colE2 ⟨12, by decide⟩ 0 hp : ↥(Q2.reps ⟨12, by decide⟩)) : Coordinate 2)
        Q2.T34_12_2 = colFn colCert_34_12_0.D (m := 125) from colCert_34_12_0.bind2]
  exact alnAll_34_12_0 j hj hq

theorem leaf_34_12_1 (hp : 1 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 34 []).length)
    (hq : (normIsRep.getD 34 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 1 hp)
        (rowE2 (⟨34, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp))
        (rowE1 (⟨34, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨34, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨34, by decide⟩ (listedAt ⟨34, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp)) T34_12
      hfix34_12 hinj34_12 hcardT34_12
      (fun i => conj_mem_of_fixedPoints _ _ (T34_12 i) (hfix34_12 i) _)
      ⟨34, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨34, by decide⟩ (Q2.listedAt ⟨34, by decide⟩
        (alnCheck_rep ⟨34, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 1 hp) Q2.T34_12_2 Q2.hfix34_12_2 Q2.hinj34_12_2
      Q2.hcardT34_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T34_12_2 i) (Q2.hfix34_12_2 i) _)
      ?_).symm
  rw [show colData1 (⟨34, by decide⟩ : Fin 148)
        ((colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp) : ↥(reps ⟨12, by decide⟩)) : Coordinate 1)
        T34_12 = colFn colCert_34_12_1.D (m := 125) from colCert_34_12_1.bind1,
    show colData2 (⟨34, by decide⟩ : Fin 148)
        ((colE2 ⟨12, by decide⟩ 1 hp : ↥(Q2.reps ⟨12, by decide⟩)) : Coordinate 2)
        Q2.T34_12_2 = colFn colCert_34_12_1.D (m := 125) from colCert_34_12_1.bind2]
  exact alnAll_34_12_1 j hj hq

theorem leaf_34_12_2 (hp : 2 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 34 []).length)
    (hq : (normIsRep.getD 34 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 2 hp)
        (rowE2 (⟨34, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp))
        (rowE1 (⟨34, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨34, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨34, by decide⟩ (listedAt ⟨34, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp)) T34_12
      hfix34_12 hinj34_12 hcardT34_12
      (fun i => conj_mem_of_fixedPoints _ _ (T34_12 i) (hfix34_12 i) _)
      ⟨34, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨34, by decide⟩ (Q2.listedAt ⟨34, by decide⟩
        (alnCheck_rep ⟨34, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 2 hp) Q2.T34_12_2 Q2.hfix34_12_2 Q2.hinj34_12_2
      Q2.hcardT34_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T34_12_2 i) (Q2.hfix34_12_2 i) _)
      ?_).symm
  rw [show colData1 (⟨34, by decide⟩ : Fin 148)
        ((colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp) : ↥(reps ⟨12, by decide⟩)) : Coordinate 1)
        T34_12 = colFn colCert_34_12_2.D (m := 125) from colCert_34_12_2.bind1,
    show colData2 (⟨34, by decide⟩ : Fin 148)
        ((colE2 ⟨12, by decide⟩ 2 hp : ↥(Q2.reps ⟨12, by decide⟩)) : Coordinate 2)
        Q2.T34_12_2 = colFn colCert_34_12_2.D (m := 125) from colCert_34_12_2.bind2]
  exact alnAll_34_12_2 j hj hq

theorem leaf_34_12_3 (hp : 3 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 34 []).length)
    (hq : (normIsRep.getD 34 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 3 hp)
        (rowE2 (⟨34, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp))
        (rowE1 (⟨34, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨34, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨34, by decide⟩ (listedAt ⟨34, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp)) T34_12
      hfix34_12 hinj34_12 hcardT34_12
      (fun i => conj_mem_of_fixedPoints _ _ (T34_12 i) (hfix34_12 i) _)
      ⟨34, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨34, by decide⟩ (Q2.listedAt ⟨34, by decide⟩
        (alnCheck_rep ⟨34, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 3 hp) Q2.T34_12_2 Q2.hfix34_12_2 Q2.hinj34_12_2
      Q2.hcardT34_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T34_12_2 i) (Q2.hfix34_12_2 i) _)
      ?_).symm
  rw [show colData1 (⟨34, by decide⟩ : Fin 148)
        ((colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp) : ↥(reps ⟨12, by decide⟩)) : Coordinate 1)
        T34_12 = colFn colCert_34_12_3.D (m := 125) from colCert_34_12_3.bind1,
    show colData2 (⟨34, by decide⟩ : Fin 148)
        ((colE2 ⟨12, by decide⟩ 3 hp : ↥(Q2.reps ⟨12, by decide⟩)) : Coordinate 2)
        Q2.T34_12_2 = colFn colCert_34_12_3.D (m := 125) from colCert_34_12_3.bind2]
  exact alnAll_34_12_3 j hj hq

theorem leaf_34_12_4 (hp : 4 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 34 []).length)
    (hq : (normIsRep.getD 34 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 4 hp)
        (rowE2 (⟨34, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp))
        (rowE1 (⟨34, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨34, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨34, by decide⟩ (listedAt ⟨34, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp)) T34_12
      hfix34_12 hinj34_12 hcardT34_12
      (fun i => conj_mem_of_fixedPoints _ _ (T34_12 i) (hfix34_12 i) _)
      ⟨34, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨34, by decide⟩ (Q2.listedAt ⟨34, by decide⟩
        (alnCheck_rep ⟨34, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 4 hp) Q2.T34_12_2 Q2.hfix34_12_2 Q2.hinj34_12_2
      Q2.hcardT34_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T34_12_2 i) (Q2.hfix34_12_2 i) _)
      ?_).symm
  rw [show colData1 (⟨34, by decide⟩ : Fin 148)
        ((colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp) : ↥(reps ⟨12, by decide⟩)) : Coordinate 1)
        T34_12 = colFn colCert_34_12_4.D (m := 125) from colCert_34_12_4.bind1,
    show colData2 (⟨34, by decide⟩ : Fin 148)
        ((colE2 ⟨12, by decide⟩ 4 hp : ↥(Q2.reps ⟨12, by decide⟩)) : Coordinate 2)
        Q2.T34_12_2 = colFn colCert_34_12_4.D (m := 125) from colCert_34_12_4.bind2]
  exact alnAll_34_12_4 j hj hq

theorem leaf_34_34_0 (hp : 0 < (Q2.transData.getD 34 []).length)
    (j : Nat) (hj : j < (repChars.getD 34 []).length)
    (hq : (normIsRep.getD 34 []).getD j false = true) :
    species (Q2.reps (⟨34, by decide⟩ : Fin 148)) (colE2 ⟨34, by decide⟩ 0 hp)
        (rowE2 (⟨34, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨34, by decide⟩ : Fin 148))
        (colE1 ⟨34, by decide⟩ 0 (transLenTr ⟨34, by decide⟩ 0 hp))
        (rowE1 (⟨34, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨34, by decide⟩ : Fin 148) ⟨34, by decide⟩ _
      (validAt ⟨34, by decide⟩ (listedAt ⟨34, by decide⟩ hj))
      (colE1 ⟨34, by decide⟩ 0 (transLenTr ⟨34, by decide⟩ 0 hp)) T34_34
      hfix34_34 hinj34_34 hcardT34_34
      (fun i => conj_mem_of_fixedPoints _ _ (T34_34 i) (hfix34_34 i) _)
      ⟨34, by decide⟩ ⟨34, by decide⟩ _
      (Q2.validAt ⟨34, by decide⟩ (Q2.listedAt ⟨34, by decide⟩
        (alnCheck_rep ⟨34, by decide⟩ hj hq).1))
      (colE2 ⟨34, by decide⟩ 0 hp) Q2.T34_34_2 Q2.hfix34_34_2 Q2.hinj34_34_2
      Q2.hcardT34_34_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T34_34_2 i) (Q2.hfix34_34_2 i) _)
      ?_).symm
  rw [show colData1 (⟨34, by decide⟩ : Fin 148)
        ((colE1 ⟨34, by decide⟩ 0 (transLenTr ⟨34, by decide⟩ 0 hp) : ↥(reps ⟨34, by decide⟩)) : Coordinate 1)
        T34_34 = colFn colCert_34_34_0.D (m := 25) from colCert_34_34_0.bind1,
    show colData2 (⟨34, by decide⟩ : Fin 148)
        ((colE2 ⟨34, by decide⟩ 0 hp : ↥(Q2.reps ⟨34, by decide⟩)) : Coordinate 2)
        Q2.T34_34_2 = colFn colCert_34_34_0.D (m := 25) from colCert_34_34_0.bind2]
  exact alnAll_34_34_0 j hj hq

theorem leaf_34_34_1 (hp : 1 < (Q2.transData.getD 34 []).length)
    (j : Nat) (hj : j < (repChars.getD 34 []).length)
    (hq : (normIsRep.getD 34 []).getD j false = true) :
    species (Q2.reps (⟨34, by decide⟩ : Fin 148)) (colE2 ⟨34, by decide⟩ 1 hp)
        (rowE2 (⟨34, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨34, by decide⟩ : Fin 148))
        (colE1 ⟨34, by decide⟩ 1 (transLenTr ⟨34, by decide⟩ 1 hp))
        (rowE1 (⟨34, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨34, by decide⟩ : Fin 148) ⟨34, by decide⟩ _
      (validAt ⟨34, by decide⟩ (listedAt ⟨34, by decide⟩ hj))
      (colE1 ⟨34, by decide⟩ 1 (transLenTr ⟨34, by decide⟩ 1 hp)) T34_34
      hfix34_34 hinj34_34 hcardT34_34
      (fun i => conj_mem_of_fixedPoints _ _ (T34_34 i) (hfix34_34 i) _)
      ⟨34, by decide⟩ ⟨34, by decide⟩ _
      (Q2.validAt ⟨34, by decide⟩ (Q2.listedAt ⟨34, by decide⟩
        (alnCheck_rep ⟨34, by decide⟩ hj hq).1))
      (colE2 ⟨34, by decide⟩ 1 hp) Q2.T34_34_2 Q2.hfix34_34_2 Q2.hinj34_34_2
      Q2.hcardT34_34_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T34_34_2 i) (Q2.hfix34_34_2 i) _)
      ?_).symm
  rw [show colData1 (⟨34, by decide⟩ : Fin 148)
        ((colE1 ⟨34, by decide⟩ 1 (transLenTr ⟨34, by decide⟩ 1 hp) : ↥(reps ⟨34, by decide⟩)) : Coordinate 1)
        T34_34 = colFn colCert_34_34_1.D (m := 25) from colCert_34_34_1.bind1,
    show colData2 (⟨34, by decide⟩ : Fin 148)
        ((colE2 ⟨34, by decide⟩ 1 hp : ↥(Q2.reps ⟨34, by decide⟩)) : Coordinate 2)
        Q2.T34_34_2 = colFn colCert_34_34_1.D (m := 25) from colCert_34_34_1.bind2]
  exact alnAll_34_34_1 j hj hq

theorem leaf_34_34_2 (hp : 2 < (Q2.transData.getD 34 []).length)
    (j : Nat) (hj : j < (repChars.getD 34 []).length)
    (hq : (normIsRep.getD 34 []).getD j false = true) :
    species (Q2.reps (⟨34, by decide⟩ : Fin 148)) (colE2 ⟨34, by decide⟩ 2 hp)
        (rowE2 (⟨34, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨34, by decide⟩ : Fin 148))
        (colE1 ⟨34, by decide⟩ 2 (transLenTr ⟨34, by decide⟩ 2 hp))
        (rowE1 (⟨34, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨34, by decide⟩ : Fin 148) ⟨34, by decide⟩ _
      (validAt ⟨34, by decide⟩ (listedAt ⟨34, by decide⟩ hj))
      (colE1 ⟨34, by decide⟩ 2 (transLenTr ⟨34, by decide⟩ 2 hp)) T34_34
      hfix34_34 hinj34_34 hcardT34_34
      (fun i => conj_mem_of_fixedPoints _ _ (T34_34 i) (hfix34_34 i) _)
      ⟨34, by decide⟩ ⟨34, by decide⟩ _
      (Q2.validAt ⟨34, by decide⟩ (Q2.listedAt ⟨34, by decide⟩
        (alnCheck_rep ⟨34, by decide⟩ hj hq).1))
      (colE2 ⟨34, by decide⟩ 2 hp) Q2.T34_34_2 Q2.hfix34_34_2 Q2.hinj34_34_2
      Q2.hcardT34_34_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T34_34_2 i) (Q2.hfix34_34_2 i) _)
      ?_).symm
  rw [show colData1 (⟨34, by decide⟩ : Fin 148)
        ((colE1 ⟨34, by decide⟩ 2 (transLenTr ⟨34, by decide⟩ 2 hp) : ↥(reps ⟨34, by decide⟩)) : Coordinate 1)
        T34_34 = colFn colCert_34_34_2.D (m := 25) from colCert_34_34_2.bind1,
    show colData2 (⟨34, by decide⟩ : Fin 148)
        ((colE2 ⟨34, by decide⟩ 2 hp : ↥(Q2.reps ⟨34, by decide⟩)) : Coordinate 2)
        Q2.T34_34_2 = colFn colCert_34_34_2.D (m := 25) from colCert_34_34_2.bind2]
  exact alnAll_34_34_2 j hj hq

theorem leaf_34_34_3 (hp : 3 < (Q2.transData.getD 34 []).length)
    (j : Nat) (hj : j < (repChars.getD 34 []).length)
    (hq : (normIsRep.getD 34 []).getD j false = true) :
    species (Q2.reps (⟨34, by decide⟩ : Fin 148)) (colE2 ⟨34, by decide⟩ 3 hp)
        (rowE2 (⟨34, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨34, by decide⟩ : Fin 148))
        (colE1 ⟨34, by decide⟩ 3 (transLenTr ⟨34, by decide⟩ 3 hp))
        (rowE1 (⟨34, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨34, by decide⟩ : Fin 148) ⟨34, by decide⟩ _
      (validAt ⟨34, by decide⟩ (listedAt ⟨34, by decide⟩ hj))
      (colE1 ⟨34, by decide⟩ 3 (transLenTr ⟨34, by decide⟩ 3 hp)) T34_34
      hfix34_34 hinj34_34 hcardT34_34
      (fun i => conj_mem_of_fixedPoints _ _ (T34_34 i) (hfix34_34 i) _)
      ⟨34, by decide⟩ ⟨34, by decide⟩ _
      (Q2.validAt ⟨34, by decide⟩ (Q2.listedAt ⟨34, by decide⟩
        (alnCheck_rep ⟨34, by decide⟩ hj hq).1))
      (colE2 ⟨34, by decide⟩ 3 hp) Q2.T34_34_2 Q2.hfix34_34_2 Q2.hinj34_34_2
      Q2.hcardT34_34_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T34_34_2 i) (Q2.hfix34_34_2 i) _)
      ?_).symm
  rw [show colData1 (⟨34, by decide⟩ : Fin 148)
        ((colE1 ⟨34, by decide⟩ 3 (transLenTr ⟨34, by decide⟩ 3 hp) : ↥(reps ⟨34, by decide⟩)) : Coordinate 1)
        T34_34 = colFn colCert_34_34_3.D (m := 25) from colCert_34_34_3.bind1,
    show colData2 (⟨34, by decide⟩ : Fin 148)
        ((colE2 ⟨34, by decide⟩ 3 hp : ↥(Q2.reps ⟨34, by decide⟩)) : Coordinate 2)
        Q2.T34_34_2 = colFn colCert_34_34_3.D (m := 25) from colCert_34_34_3.bind2]
  exact alnAll_34_34_3 j hj hq

theorem leaf_34_34_4 (hp : 4 < (Q2.transData.getD 34 []).length)
    (j : Nat) (hj : j < (repChars.getD 34 []).length)
    (hq : (normIsRep.getD 34 []).getD j false = true) :
    species (Q2.reps (⟨34, by decide⟩ : Fin 148)) (colE2 ⟨34, by decide⟩ 4 hp)
        (rowE2 (⟨34, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨34, by decide⟩ : Fin 148))
        (colE1 ⟨34, by decide⟩ 4 (transLenTr ⟨34, by decide⟩ 4 hp))
        (rowE1 (⟨34, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨34, by decide⟩ : Fin 148) ⟨34, by decide⟩ _
      (validAt ⟨34, by decide⟩ (listedAt ⟨34, by decide⟩ hj))
      (colE1 ⟨34, by decide⟩ 4 (transLenTr ⟨34, by decide⟩ 4 hp)) T34_34
      hfix34_34 hinj34_34 hcardT34_34
      (fun i => conj_mem_of_fixedPoints _ _ (T34_34 i) (hfix34_34 i) _)
      ⟨34, by decide⟩ ⟨34, by decide⟩ _
      (Q2.validAt ⟨34, by decide⟩ (Q2.listedAt ⟨34, by decide⟩
        (alnCheck_rep ⟨34, by decide⟩ hj hq).1))
      (colE2 ⟨34, by decide⟩ 4 hp) Q2.T34_34_2 Q2.hfix34_34_2 Q2.hinj34_34_2
      Q2.hcardT34_34_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T34_34_2 i) (Q2.hfix34_34_2 i) _)
      ?_).symm
  rw [show colData1 (⟨34, by decide⟩ : Fin 148)
        ((colE1 ⟨34, by decide⟩ 4 (transLenTr ⟨34, by decide⟩ 4 hp) : ↥(reps ⟨34, by decide⟩)) : Coordinate 1)
        T34_34 = colFn colCert_34_34_4.D (m := 25) from colCert_34_34_4.bind1,
    show colData2 (⟨34, by decide⟩ : Fin 148)
        ((colE2 ⟨34, by decide⟩ 4 hp : ↥(Q2.reps ⟨34, by decide⟩)) : Coordinate 2)
        Q2.T34_34_2 = colFn colCert_34_34_4.D (m := 25) from colCert_34_34_4.bind2]
  exact alnAll_34_34_4 j hj hq

theorem leaf_34_34_5 (hp : 5 < (Q2.transData.getD 34 []).length)
    (j : Nat) (hj : j < (repChars.getD 34 []).length)
    (hq : (normIsRep.getD 34 []).getD j false = true) :
    species (Q2.reps (⟨34, by decide⟩ : Fin 148)) (colE2 ⟨34, by decide⟩ 5 hp)
        (rowE2 (⟨34, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨34, by decide⟩ : Fin 148))
        (colE1 ⟨34, by decide⟩ 5 (transLenTr ⟨34, by decide⟩ 5 hp))
        (rowE1 (⟨34, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨34, by decide⟩ : Fin 148) ⟨34, by decide⟩ _
      (validAt ⟨34, by decide⟩ (listedAt ⟨34, by decide⟩ hj))
      (colE1 ⟨34, by decide⟩ 5 (transLenTr ⟨34, by decide⟩ 5 hp)) T34_34
      hfix34_34 hinj34_34 hcardT34_34
      (fun i => conj_mem_of_fixedPoints _ _ (T34_34 i) (hfix34_34 i) _)
      ⟨34, by decide⟩ ⟨34, by decide⟩ _
      (Q2.validAt ⟨34, by decide⟩ (Q2.listedAt ⟨34, by decide⟩
        (alnCheck_rep ⟨34, by decide⟩ hj hq).1))
      (colE2 ⟨34, by decide⟩ 5 hp) Q2.T34_34_2 Q2.hfix34_34_2 Q2.hinj34_34_2
      Q2.hcardT34_34_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T34_34_2 i) (Q2.hfix34_34_2 i) _)
      ?_).symm
  rw [show colData1 (⟨34, by decide⟩ : Fin 148)
        ((colE1 ⟨34, by decide⟩ 5 (transLenTr ⟨34, by decide⟩ 5 hp) : ↥(reps ⟨34, by decide⟩)) : Coordinate 1)
        T34_34 = colFn colCert_34_34_5.D (m := 25) from colCert_34_34_5.bind1,
    show colData2 (⟨34, by decide⟩ : Fin 148)
        ((colE2 ⟨34, by decide⟩ 5 hp : ↥(Q2.reps ⟨34, by decide⟩)) : Coordinate 2)
        Q2.T34_34_2 = colFn colCert_34_34_5.D (m := 25) from colCert_34_34_5.bind2]
  exact alnAll_34_34_5 j hj hq

theorem leaf_34_34_10 (hp : 10 < (Q2.transData.getD 34 []).length)
    (j : Nat) (hj : j < (repChars.getD 34 []).length)
    (hq : (normIsRep.getD 34 []).getD j false = true) :
    species (Q2.reps (⟨34, by decide⟩ : Fin 148)) (colE2 ⟨34, by decide⟩ 10 hp)
        (rowE2 (⟨34, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨34, by decide⟩ : Fin 148))
        (colE1 ⟨34, by decide⟩ 10 (transLenTr ⟨34, by decide⟩ 10 hp))
        (rowE1 (⟨34, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨34, by decide⟩ : Fin 148) ⟨34, by decide⟩ _
      (validAt ⟨34, by decide⟩ (listedAt ⟨34, by decide⟩ hj))
      (colE1 ⟨34, by decide⟩ 10 (transLenTr ⟨34, by decide⟩ 10 hp)) T34_34
      hfix34_34 hinj34_34 hcardT34_34
      (fun i => conj_mem_of_fixedPoints _ _ (T34_34 i) (hfix34_34 i) _)
      ⟨34, by decide⟩ ⟨34, by decide⟩ _
      (Q2.validAt ⟨34, by decide⟩ (Q2.listedAt ⟨34, by decide⟩
        (alnCheck_rep ⟨34, by decide⟩ hj hq).1))
      (colE2 ⟨34, by decide⟩ 10 hp) Q2.T34_34_2 Q2.hfix34_34_2 Q2.hinj34_34_2
      Q2.hcardT34_34_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T34_34_2 i) (Q2.hfix34_34_2 i) _)
      ?_).symm
  rw [show colData1 (⟨34, by decide⟩ : Fin 148)
        ((colE1 ⟨34, by decide⟩ 10 (transLenTr ⟨34, by decide⟩ 10 hp) : ↥(reps ⟨34, by decide⟩)) : Coordinate 1)
        T34_34 = colFn colCert_34_34_10.D (m := 25) from colCert_34_34_10.bind1,
    show colData2 (⟨34, by decide⟩ : Fin 148)
        ((colE2 ⟨34, by decide⟩ 10 hp : ↥(Q2.reps ⟨34, by decide⟩)) : Coordinate 2)
        Q2.T34_34_2 = colFn colCert_34_34_10.D (m := 25) from colCert_34_34_10.bind2]
  exact alnAll_34_34_10 j hj hq

theorem leaf_34_34_15 (hp : 15 < (Q2.transData.getD 34 []).length)
    (j : Nat) (hj : j < (repChars.getD 34 []).length)
    (hq : (normIsRep.getD 34 []).getD j false = true) :
    species (Q2.reps (⟨34, by decide⟩ : Fin 148)) (colE2 ⟨34, by decide⟩ 15 hp)
        (rowE2 (⟨34, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨34, by decide⟩ : Fin 148))
        (colE1 ⟨34, by decide⟩ 15 (transLenTr ⟨34, by decide⟩ 15 hp))
        (rowE1 (⟨34, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨34, by decide⟩ : Fin 148) ⟨34, by decide⟩ _
      (validAt ⟨34, by decide⟩ (listedAt ⟨34, by decide⟩ hj))
      (colE1 ⟨34, by decide⟩ 15 (transLenTr ⟨34, by decide⟩ 15 hp)) T34_34
      hfix34_34 hinj34_34 hcardT34_34
      (fun i => conj_mem_of_fixedPoints _ _ (T34_34 i) (hfix34_34 i) _)
      ⟨34, by decide⟩ ⟨34, by decide⟩ _
      (Q2.validAt ⟨34, by decide⟩ (Q2.listedAt ⟨34, by decide⟩
        (alnCheck_rep ⟨34, by decide⟩ hj hq).1))
      (colE2 ⟨34, by decide⟩ 15 hp) Q2.T34_34_2 Q2.hfix34_34_2 Q2.hinj34_34_2
      Q2.hcardT34_34_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T34_34_2 i) (Q2.hfix34_34_2 i) _)
      ?_).symm
  rw [show colData1 (⟨34, by decide⟩ : Fin 148)
        ((colE1 ⟨34, by decide⟩ 15 (transLenTr ⟨34, by decide⟩ 15 hp) : ↥(reps ⟨34, by decide⟩)) : Coordinate 1)
        T34_34 = colFn colCert_34_34_15.D (m := 25) from colCert_34_34_15.bind1,
    show colData2 (⟨34, by decide⟩ : Fin 148)
        ((colE2 ⟨34, by decide⟩ 15 hp : ↥(Q2.reps ⟨34, by decide⟩)) : Coordinate 2)
        Q2.T34_34_2 = colFn colCert_34_34_15.D (m := 25) from colCert_34_34_15.bind2]
  exact alnAll_34_34_15 j hj hq

theorem leaf_34_34_20 (hp : 20 < (Q2.transData.getD 34 []).length)
    (j : Nat) (hj : j < (repChars.getD 34 []).length)
    (hq : (normIsRep.getD 34 []).getD j false = true) :
    species (Q2.reps (⟨34, by decide⟩ : Fin 148)) (colE2 ⟨34, by decide⟩ 20 hp)
        (rowE2 (⟨34, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨34, by decide⟩ : Fin 148))
        (colE1 ⟨34, by decide⟩ 20 (transLenTr ⟨34, by decide⟩ 20 hp))
        (rowE1 (⟨34, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨34, by decide⟩ : Fin 148) ⟨34, by decide⟩ _
      (validAt ⟨34, by decide⟩ (listedAt ⟨34, by decide⟩ hj))
      (colE1 ⟨34, by decide⟩ 20 (transLenTr ⟨34, by decide⟩ 20 hp)) T34_34
      hfix34_34 hinj34_34 hcardT34_34
      (fun i => conj_mem_of_fixedPoints _ _ (T34_34 i) (hfix34_34 i) _)
      ⟨34, by decide⟩ ⟨34, by decide⟩ _
      (Q2.validAt ⟨34, by decide⟩ (Q2.listedAt ⟨34, by decide⟩
        (alnCheck_rep ⟨34, by decide⟩ hj hq).1))
      (colE2 ⟨34, by decide⟩ 20 hp) Q2.T34_34_2 Q2.hfix34_34_2 Q2.hinj34_34_2
      Q2.hcardT34_34_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T34_34_2 i) (Q2.hfix34_34_2 i) _)
      ?_).symm
  rw [show colData1 (⟨34, by decide⟩ : Fin 148)
        ((colE1 ⟨34, by decide⟩ 20 (transLenTr ⟨34, by decide⟩ 20 hp) : ↥(reps ⟨34, by decide⟩)) : Coordinate 1)
        T34_34 = colFn colCert_34_34_20.D (m := 25) from colCert_34_34_20.bind1,
    show colData2 (⟨34, by decide⟩ : Fin 148)
        ((colE2 ⟨34, by decide⟩ 20 hp : ↥(Q2.reps ⟨34, by decide⟩)) : Coordinate 2)
        Q2.T34_34_2 = colFn colCert_34_34_20.D (m := 25) from colCert_34_34_20.bind2]
  exact alnAll_34_34_20 j hj hq

theorem leaf_35_12_0 (hp : 0 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 35 []).length)
    (hq : (normIsRep.getD 35 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 0 hp)
        (rowE2 (⟨35, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp))
        (rowE1 (⟨35, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨35, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨35, by decide⟩ (listedAt ⟨35, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp)) T35_12
      hfix35_12 hinj35_12 hcardT35_12
      (fun i => conj_mem_of_fixedPoints _ _ (T35_12 i) (hfix35_12 i) _)
      ⟨35, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨35, by decide⟩ (Q2.listedAt ⟨35, by decide⟩
        (alnCheck_rep ⟨35, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 0 hp) Q2.T35_12_2 Q2.hfix35_12_2 Q2.hinj35_12_2
      Q2.hcardT35_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T35_12_2 i) (Q2.hfix35_12_2 i) _)
      ?_).symm
  rw [show colData1 (⟨35, by decide⟩ : Fin 148)
        ((colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp) : ↥(reps ⟨12, by decide⟩)) : Coordinate 1)
        T35_12 = colFn colCert_35_12_0.D (m := 125) from colCert_35_12_0.bind1,
    show colData2 (⟨35, by decide⟩ : Fin 148)
        ((colE2 ⟨12, by decide⟩ 0 hp : ↥(Q2.reps ⟨12, by decide⟩)) : Coordinate 2)
        Q2.T35_12_2 = colFn colCert_35_12_0.D (m := 125) from colCert_35_12_0.bind2]
  exact alnAll_35_12_0 j hj hq

theorem leaf_35_12_1 (hp : 1 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 35 []).length)
    (hq : (normIsRep.getD 35 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 1 hp)
        (rowE2 (⟨35, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp))
        (rowE1 (⟨35, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨35, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨35, by decide⟩ (listedAt ⟨35, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp)) T35_12
      hfix35_12 hinj35_12 hcardT35_12
      (fun i => conj_mem_of_fixedPoints _ _ (T35_12 i) (hfix35_12 i) _)
      ⟨35, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨35, by decide⟩ (Q2.listedAt ⟨35, by decide⟩
        (alnCheck_rep ⟨35, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 1 hp) Q2.T35_12_2 Q2.hfix35_12_2 Q2.hinj35_12_2
      Q2.hcardT35_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T35_12_2 i) (Q2.hfix35_12_2 i) _)
      ?_).symm
  rw [show colData1 (⟨35, by decide⟩ : Fin 148)
        ((colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp) : ↥(reps ⟨12, by decide⟩)) : Coordinate 1)
        T35_12 = colFn colCert_35_12_1.D (m := 125) from colCert_35_12_1.bind1,
    show colData2 (⟨35, by decide⟩ : Fin 148)
        ((colE2 ⟨12, by decide⟩ 1 hp : ↥(Q2.reps ⟨12, by decide⟩)) : Coordinate 2)
        Q2.T35_12_2 = colFn colCert_35_12_1.D (m := 125) from colCert_35_12_1.bind2]
  exact alnAll_35_12_1 j hj hq

theorem leaf_35_12_2 (hp : 2 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 35 []).length)
    (hq : (normIsRep.getD 35 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 2 hp)
        (rowE2 (⟨35, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp))
        (rowE1 (⟨35, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨35, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨35, by decide⟩ (listedAt ⟨35, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp)) T35_12
      hfix35_12 hinj35_12 hcardT35_12
      (fun i => conj_mem_of_fixedPoints _ _ (T35_12 i) (hfix35_12 i) _)
      ⟨35, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨35, by decide⟩ (Q2.listedAt ⟨35, by decide⟩
        (alnCheck_rep ⟨35, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 2 hp) Q2.T35_12_2 Q2.hfix35_12_2 Q2.hinj35_12_2
      Q2.hcardT35_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T35_12_2 i) (Q2.hfix35_12_2 i) _)
      ?_).symm
  rw [show colData1 (⟨35, by decide⟩ : Fin 148)
        ((colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp) : ↥(reps ⟨12, by decide⟩)) : Coordinate 1)
        T35_12 = colFn colCert_35_12_2.D (m := 125) from colCert_35_12_2.bind1,
    show colData2 (⟨35, by decide⟩ : Fin 148)
        ((colE2 ⟨12, by decide⟩ 2 hp : ↥(Q2.reps ⟨12, by decide⟩)) : Coordinate 2)
        Q2.T35_12_2 = colFn colCert_35_12_2.D (m := 125) from colCert_35_12_2.bind2]
  exact alnAll_35_12_2 j hj hq

theorem leaf_35_12_3 (hp : 3 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 35 []).length)
    (hq : (normIsRep.getD 35 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 3 hp)
        (rowE2 (⟨35, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp))
        (rowE1 (⟨35, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨35, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨35, by decide⟩ (listedAt ⟨35, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp)) T35_12
      hfix35_12 hinj35_12 hcardT35_12
      (fun i => conj_mem_of_fixedPoints _ _ (T35_12 i) (hfix35_12 i) _)
      ⟨35, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨35, by decide⟩ (Q2.listedAt ⟨35, by decide⟩
        (alnCheck_rep ⟨35, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 3 hp) Q2.T35_12_2 Q2.hfix35_12_2 Q2.hinj35_12_2
      Q2.hcardT35_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T35_12_2 i) (Q2.hfix35_12_2 i) _)
      ?_).symm
  rw [show colData1 (⟨35, by decide⟩ : Fin 148)
        ((colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp) : ↥(reps ⟨12, by decide⟩)) : Coordinate 1)
        T35_12 = colFn colCert_35_12_3.D (m := 125) from colCert_35_12_3.bind1,
    show colData2 (⟨35, by decide⟩ : Fin 148)
        ((colE2 ⟨12, by decide⟩ 3 hp : ↥(Q2.reps ⟨12, by decide⟩)) : Coordinate 2)
        Q2.T35_12_2 = colFn colCert_35_12_3.D (m := 125) from colCert_35_12_3.bind2]
  exact alnAll_35_12_3 j hj hq

theorem leaf_35_12_4 (hp : 4 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 35 []).length)
    (hq : (normIsRep.getD 35 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 4 hp)
        (rowE2 (⟨35, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp))
        (rowE1 (⟨35, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨35, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨35, by decide⟩ (listedAt ⟨35, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp)) T35_12
      hfix35_12 hinj35_12 hcardT35_12
      (fun i => conj_mem_of_fixedPoints _ _ (T35_12 i) (hfix35_12 i) _)
      ⟨35, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨35, by decide⟩ (Q2.listedAt ⟨35, by decide⟩
        (alnCheck_rep ⟨35, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 4 hp) Q2.T35_12_2 Q2.hfix35_12_2 Q2.hinj35_12_2
      Q2.hcardT35_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T35_12_2 i) (Q2.hfix35_12_2 i) _)
      ?_).symm
  rw [show colData1 (⟨35, by decide⟩ : Fin 148)
        ((colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp) : ↥(reps ⟨12, by decide⟩)) : Coordinate 1)
        T35_12 = colFn colCert_35_12_4.D (m := 125) from colCert_35_12_4.bind1,
    show colData2 (⟨35, by decide⟩ : Fin 148)
        ((colE2 ⟨12, by decide⟩ 4 hp : ↥(Q2.reps ⟨12, by decide⟩)) : Coordinate 2)
        Q2.T35_12_2 = colFn colCert_35_12_4.D (m := 125) from colCert_35_12_4.bind2]
  exact alnAll_35_12_4 j hj hq

theorem leaf_35_35_0 (hp : 0 < (Q2.transData.getD 35 []).length)
    (j : Nat) (hj : j < (repChars.getD 35 []).length)
    (hq : (normIsRep.getD 35 []).getD j false = true) :
    species (Q2.reps (⟨35, by decide⟩ : Fin 148)) (colE2 ⟨35, by decide⟩ 0 hp)
        (rowE2 (⟨35, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨35, by decide⟩ : Fin 148))
        (colE1 ⟨35, by decide⟩ 0 (transLenTr ⟨35, by decide⟩ 0 hp))
        (rowE1 (⟨35, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨35, by decide⟩ : Fin 148) ⟨35, by decide⟩ _
      (validAt ⟨35, by decide⟩ (listedAt ⟨35, by decide⟩ hj))
      (colE1 ⟨35, by decide⟩ 0 (transLenTr ⟨35, by decide⟩ 0 hp)) T35_35
      hfix35_35 hinj35_35 hcardT35_35
      (fun i => conj_mem_of_fixedPoints _ _ (T35_35 i) (hfix35_35 i) _)
      ⟨35, by decide⟩ ⟨35, by decide⟩ _
      (Q2.validAt ⟨35, by decide⟩ (Q2.listedAt ⟨35, by decide⟩
        (alnCheck_rep ⟨35, by decide⟩ hj hq).1))
      (colE2 ⟨35, by decide⟩ 0 hp) Q2.T35_35_2 Q2.hfix35_35_2 Q2.hinj35_35_2
      Q2.hcardT35_35_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T35_35_2 i) (Q2.hfix35_35_2 i) _)
      ?_).symm
  rw [show colData1 (⟨35, by decide⟩ : Fin 148)
        ((colE1 ⟨35, by decide⟩ 0 (transLenTr ⟨35, by decide⟩ 0 hp) : ↥(reps ⟨35, by decide⟩)) : Coordinate 1)
        T35_35 = colFn colCert_35_35_0.D (m := 25) from colCert_35_35_0.bind1,
    show colData2 (⟨35, by decide⟩ : Fin 148)
        ((colE2 ⟨35, by decide⟩ 0 hp : ↥(Q2.reps ⟨35, by decide⟩)) : Coordinate 2)
        Q2.T35_35_2 = colFn colCert_35_35_0.D (m := 25) from colCert_35_35_0.bind2]
  exact alnAll_35_35_0 j hj hq

theorem leaf_35_35_1 (hp : 1 < (Q2.transData.getD 35 []).length)
    (j : Nat) (hj : j < (repChars.getD 35 []).length)
    (hq : (normIsRep.getD 35 []).getD j false = true) :
    species (Q2.reps (⟨35, by decide⟩ : Fin 148)) (colE2 ⟨35, by decide⟩ 1 hp)
        (rowE2 (⟨35, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨35, by decide⟩ : Fin 148))
        (colE1 ⟨35, by decide⟩ 1 (transLenTr ⟨35, by decide⟩ 1 hp))
        (rowE1 (⟨35, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨35, by decide⟩ : Fin 148) ⟨35, by decide⟩ _
      (validAt ⟨35, by decide⟩ (listedAt ⟨35, by decide⟩ hj))
      (colE1 ⟨35, by decide⟩ 1 (transLenTr ⟨35, by decide⟩ 1 hp)) T35_35
      hfix35_35 hinj35_35 hcardT35_35
      (fun i => conj_mem_of_fixedPoints _ _ (T35_35 i) (hfix35_35 i) _)
      ⟨35, by decide⟩ ⟨35, by decide⟩ _
      (Q2.validAt ⟨35, by decide⟩ (Q2.listedAt ⟨35, by decide⟩
        (alnCheck_rep ⟨35, by decide⟩ hj hq).1))
      (colE2 ⟨35, by decide⟩ 1 hp) Q2.T35_35_2 Q2.hfix35_35_2 Q2.hinj35_35_2
      Q2.hcardT35_35_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T35_35_2 i) (Q2.hfix35_35_2 i) _)
      ?_).symm
  rw [show colData1 (⟨35, by decide⟩ : Fin 148)
        ((colE1 ⟨35, by decide⟩ 1 (transLenTr ⟨35, by decide⟩ 1 hp) : ↥(reps ⟨35, by decide⟩)) : Coordinate 1)
        T35_35 = colFn colCert_35_35_1.D (m := 25) from colCert_35_35_1.bind1,
    show colData2 (⟨35, by decide⟩ : Fin 148)
        ((colE2 ⟨35, by decide⟩ 1 hp : ↥(Q2.reps ⟨35, by decide⟩)) : Coordinate 2)
        Q2.T35_35_2 = colFn colCert_35_35_1.D (m := 25) from colCert_35_35_1.bind2]
  exact alnAll_35_35_1 j hj hq

theorem leaf_35_35_2 (hp : 2 < (Q2.transData.getD 35 []).length)
    (j : Nat) (hj : j < (repChars.getD 35 []).length)
    (hq : (normIsRep.getD 35 []).getD j false = true) :
    species (Q2.reps (⟨35, by decide⟩ : Fin 148)) (colE2 ⟨35, by decide⟩ 2 hp)
        (rowE2 (⟨35, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨35, by decide⟩ : Fin 148))
        (colE1 ⟨35, by decide⟩ 2 (transLenTr ⟨35, by decide⟩ 2 hp))
        (rowE1 (⟨35, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨35, by decide⟩ : Fin 148) ⟨35, by decide⟩ _
      (validAt ⟨35, by decide⟩ (listedAt ⟨35, by decide⟩ hj))
      (colE1 ⟨35, by decide⟩ 2 (transLenTr ⟨35, by decide⟩ 2 hp)) T35_35
      hfix35_35 hinj35_35 hcardT35_35
      (fun i => conj_mem_of_fixedPoints _ _ (T35_35 i) (hfix35_35 i) _)
      ⟨35, by decide⟩ ⟨35, by decide⟩ _
      (Q2.validAt ⟨35, by decide⟩ (Q2.listedAt ⟨35, by decide⟩
        (alnCheck_rep ⟨35, by decide⟩ hj hq).1))
      (colE2 ⟨35, by decide⟩ 2 hp) Q2.T35_35_2 Q2.hfix35_35_2 Q2.hinj35_35_2
      Q2.hcardT35_35_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T35_35_2 i) (Q2.hfix35_35_2 i) _)
      ?_).symm
  rw [show colData1 (⟨35, by decide⟩ : Fin 148)
        ((colE1 ⟨35, by decide⟩ 2 (transLenTr ⟨35, by decide⟩ 2 hp) : ↥(reps ⟨35, by decide⟩)) : Coordinate 1)
        T35_35 = colFn colCert_35_35_2.D (m := 25) from colCert_35_35_2.bind1,
    show colData2 (⟨35, by decide⟩ : Fin 148)
        ((colE2 ⟨35, by decide⟩ 2 hp : ↥(Q2.reps ⟨35, by decide⟩)) : Coordinate 2)
        Q2.T35_35_2 = colFn colCert_35_35_2.D (m := 25) from colCert_35_35_2.bind2]
  exact alnAll_35_35_2 j hj hq

theorem leaf_35_35_3 (hp : 3 < (Q2.transData.getD 35 []).length)
    (j : Nat) (hj : j < (repChars.getD 35 []).length)
    (hq : (normIsRep.getD 35 []).getD j false = true) :
    species (Q2.reps (⟨35, by decide⟩ : Fin 148)) (colE2 ⟨35, by decide⟩ 3 hp)
        (rowE2 (⟨35, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨35, by decide⟩ : Fin 148))
        (colE1 ⟨35, by decide⟩ 3 (transLenTr ⟨35, by decide⟩ 3 hp))
        (rowE1 (⟨35, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨35, by decide⟩ : Fin 148) ⟨35, by decide⟩ _
      (validAt ⟨35, by decide⟩ (listedAt ⟨35, by decide⟩ hj))
      (colE1 ⟨35, by decide⟩ 3 (transLenTr ⟨35, by decide⟩ 3 hp)) T35_35
      hfix35_35 hinj35_35 hcardT35_35
      (fun i => conj_mem_of_fixedPoints _ _ (T35_35 i) (hfix35_35 i) _)
      ⟨35, by decide⟩ ⟨35, by decide⟩ _
      (Q2.validAt ⟨35, by decide⟩ (Q2.listedAt ⟨35, by decide⟩
        (alnCheck_rep ⟨35, by decide⟩ hj hq).1))
      (colE2 ⟨35, by decide⟩ 3 hp) Q2.T35_35_2 Q2.hfix35_35_2 Q2.hinj35_35_2
      Q2.hcardT35_35_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T35_35_2 i) (Q2.hfix35_35_2 i) _)
      ?_).symm
  rw [show colData1 (⟨35, by decide⟩ : Fin 148)
        ((colE1 ⟨35, by decide⟩ 3 (transLenTr ⟨35, by decide⟩ 3 hp) : ↥(reps ⟨35, by decide⟩)) : Coordinate 1)
        T35_35 = colFn colCert_35_35_3.D (m := 25) from colCert_35_35_3.bind1,
    show colData2 (⟨35, by decide⟩ : Fin 148)
        ((colE2 ⟨35, by decide⟩ 3 hp : ↥(Q2.reps ⟨35, by decide⟩)) : Coordinate 2)
        Q2.T35_35_2 = colFn colCert_35_35_3.D (m := 25) from colCert_35_35_3.bind2]
  exact alnAll_35_35_3 j hj hq

theorem leaf_35_35_4 (hp : 4 < (Q2.transData.getD 35 []).length)
    (j : Nat) (hj : j < (repChars.getD 35 []).length)
    (hq : (normIsRep.getD 35 []).getD j false = true) :
    species (Q2.reps (⟨35, by decide⟩ : Fin 148)) (colE2 ⟨35, by decide⟩ 4 hp)
        (rowE2 (⟨35, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨35, by decide⟩ : Fin 148))
        (colE1 ⟨35, by decide⟩ 4 (transLenTr ⟨35, by decide⟩ 4 hp))
        (rowE1 (⟨35, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨35, by decide⟩ : Fin 148) ⟨35, by decide⟩ _
      (validAt ⟨35, by decide⟩ (listedAt ⟨35, by decide⟩ hj))
      (colE1 ⟨35, by decide⟩ 4 (transLenTr ⟨35, by decide⟩ 4 hp)) T35_35
      hfix35_35 hinj35_35 hcardT35_35
      (fun i => conj_mem_of_fixedPoints _ _ (T35_35 i) (hfix35_35 i) _)
      ⟨35, by decide⟩ ⟨35, by decide⟩ _
      (Q2.validAt ⟨35, by decide⟩ (Q2.listedAt ⟨35, by decide⟩
        (alnCheck_rep ⟨35, by decide⟩ hj hq).1))
      (colE2 ⟨35, by decide⟩ 4 hp) Q2.T35_35_2 Q2.hfix35_35_2 Q2.hinj35_35_2
      Q2.hcardT35_35_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T35_35_2 i) (Q2.hfix35_35_2 i) _)
      ?_).symm
  rw [show colData1 (⟨35, by decide⟩ : Fin 148)
        ((colE1 ⟨35, by decide⟩ 4 (transLenTr ⟨35, by decide⟩ 4 hp) : ↥(reps ⟨35, by decide⟩)) : Coordinate 1)
        T35_35 = colFn colCert_35_35_4.D (m := 25) from colCert_35_35_4.bind1,
    show colData2 (⟨35, by decide⟩ : Fin 148)
        ((colE2 ⟨35, by decide⟩ 4 hp : ↥(Q2.reps ⟨35, by decide⟩)) : Coordinate 2)
        Q2.T35_35_2 = colFn colCert_35_35_4.D (m := 25) from colCert_35_35_4.bind2]
  exact alnAll_35_35_4 j hj hq

theorem leaf_35_35_5 (hp : 5 < (Q2.transData.getD 35 []).length)
    (j : Nat) (hj : j < (repChars.getD 35 []).length)
    (hq : (normIsRep.getD 35 []).getD j false = true) :
    species (Q2.reps (⟨35, by decide⟩ : Fin 148)) (colE2 ⟨35, by decide⟩ 5 hp)
        (rowE2 (⟨35, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨35, by decide⟩ : Fin 148))
        (colE1 ⟨35, by decide⟩ 5 (transLenTr ⟨35, by decide⟩ 5 hp))
        (rowE1 (⟨35, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨35, by decide⟩ : Fin 148) ⟨35, by decide⟩ _
      (validAt ⟨35, by decide⟩ (listedAt ⟨35, by decide⟩ hj))
      (colE1 ⟨35, by decide⟩ 5 (transLenTr ⟨35, by decide⟩ 5 hp)) T35_35
      hfix35_35 hinj35_35 hcardT35_35
      (fun i => conj_mem_of_fixedPoints _ _ (T35_35 i) (hfix35_35 i) _)
      ⟨35, by decide⟩ ⟨35, by decide⟩ _
      (Q2.validAt ⟨35, by decide⟩ (Q2.listedAt ⟨35, by decide⟩
        (alnCheck_rep ⟨35, by decide⟩ hj hq).1))
      (colE2 ⟨35, by decide⟩ 5 hp) Q2.T35_35_2 Q2.hfix35_35_2 Q2.hinj35_35_2
      Q2.hcardT35_35_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T35_35_2 i) (Q2.hfix35_35_2 i) _)
      ?_).symm
  rw [show colData1 (⟨35, by decide⟩ : Fin 148)
        ((colE1 ⟨35, by decide⟩ 5 (transLenTr ⟨35, by decide⟩ 5 hp) : ↥(reps ⟨35, by decide⟩)) : Coordinate 1)
        T35_35 = colFn colCert_35_35_5.D (m := 25) from colCert_35_35_5.bind1,
    show colData2 (⟨35, by decide⟩ : Fin 148)
        ((colE2 ⟨35, by decide⟩ 5 hp : ↥(Q2.reps ⟨35, by decide⟩)) : Coordinate 2)
        Q2.T35_35_2 = colFn colCert_35_35_5.D (m := 25) from colCert_35_35_5.bind2]
  exact alnAll_35_35_5 j hj hq

theorem leaf_35_35_10 (hp : 10 < (Q2.transData.getD 35 []).length)
    (j : Nat) (hj : j < (repChars.getD 35 []).length)
    (hq : (normIsRep.getD 35 []).getD j false = true) :
    species (Q2.reps (⟨35, by decide⟩ : Fin 148)) (colE2 ⟨35, by decide⟩ 10 hp)
        (rowE2 (⟨35, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨35, by decide⟩ : Fin 148))
        (colE1 ⟨35, by decide⟩ 10 (transLenTr ⟨35, by decide⟩ 10 hp))
        (rowE1 (⟨35, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨35, by decide⟩ : Fin 148) ⟨35, by decide⟩ _
      (validAt ⟨35, by decide⟩ (listedAt ⟨35, by decide⟩ hj))
      (colE1 ⟨35, by decide⟩ 10 (transLenTr ⟨35, by decide⟩ 10 hp)) T35_35
      hfix35_35 hinj35_35 hcardT35_35
      (fun i => conj_mem_of_fixedPoints _ _ (T35_35 i) (hfix35_35 i) _)
      ⟨35, by decide⟩ ⟨35, by decide⟩ _
      (Q2.validAt ⟨35, by decide⟩ (Q2.listedAt ⟨35, by decide⟩
        (alnCheck_rep ⟨35, by decide⟩ hj hq).1))
      (colE2 ⟨35, by decide⟩ 10 hp) Q2.T35_35_2 Q2.hfix35_35_2 Q2.hinj35_35_2
      Q2.hcardT35_35_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T35_35_2 i) (Q2.hfix35_35_2 i) _)
      ?_).symm
  rw [show colData1 (⟨35, by decide⟩ : Fin 148)
        ((colE1 ⟨35, by decide⟩ 10 (transLenTr ⟨35, by decide⟩ 10 hp) : ↥(reps ⟨35, by decide⟩)) : Coordinate 1)
        T35_35 = colFn colCert_35_35_10.D (m := 25) from colCert_35_35_10.bind1,
    show colData2 (⟨35, by decide⟩ : Fin 148)
        ((colE2 ⟨35, by decide⟩ 10 hp : ↥(Q2.reps ⟨35, by decide⟩)) : Coordinate 2)
        Q2.T35_35_2 = colFn colCert_35_35_10.D (m := 25) from colCert_35_35_10.bind2]
  exact alnAll_35_35_10 j hj hq

theorem leaf_35_35_15 (hp : 15 < (Q2.transData.getD 35 []).length)
    (j : Nat) (hj : j < (repChars.getD 35 []).length)
    (hq : (normIsRep.getD 35 []).getD j false = true) :
    species (Q2.reps (⟨35, by decide⟩ : Fin 148)) (colE2 ⟨35, by decide⟩ 15 hp)
        (rowE2 (⟨35, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨35, by decide⟩ : Fin 148))
        (colE1 ⟨35, by decide⟩ 15 (transLenTr ⟨35, by decide⟩ 15 hp))
        (rowE1 (⟨35, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨35, by decide⟩ : Fin 148) ⟨35, by decide⟩ _
      (validAt ⟨35, by decide⟩ (listedAt ⟨35, by decide⟩ hj))
      (colE1 ⟨35, by decide⟩ 15 (transLenTr ⟨35, by decide⟩ 15 hp)) T35_35
      hfix35_35 hinj35_35 hcardT35_35
      (fun i => conj_mem_of_fixedPoints _ _ (T35_35 i) (hfix35_35 i) _)
      ⟨35, by decide⟩ ⟨35, by decide⟩ _
      (Q2.validAt ⟨35, by decide⟩ (Q2.listedAt ⟨35, by decide⟩
        (alnCheck_rep ⟨35, by decide⟩ hj hq).1))
      (colE2 ⟨35, by decide⟩ 15 hp) Q2.T35_35_2 Q2.hfix35_35_2 Q2.hinj35_35_2
      Q2.hcardT35_35_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T35_35_2 i) (Q2.hfix35_35_2 i) _)
      ?_).symm
  rw [show colData1 (⟨35, by decide⟩ : Fin 148)
        ((colE1 ⟨35, by decide⟩ 15 (transLenTr ⟨35, by decide⟩ 15 hp) : ↥(reps ⟨35, by decide⟩)) : Coordinate 1)
        T35_35 = colFn colCert_35_35_15.D (m := 25) from colCert_35_35_15.bind1,
    show colData2 (⟨35, by decide⟩ : Fin 148)
        ((colE2 ⟨35, by decide⟩ 15 hp : ↥(Q2.reps ⟨35, by decide⟩)) : Coordinate 2)
        Q2.T35_35_2 = colFn colCert_35_35_15.D (m := 25) from colCert_35_35_15.bind2]
  exact alnAll_35_35_15 j hj hq

theorem leaf_35_35_20 (hp : 20 < (Q2.transData.getD 35 []).length)
    (j : Nat) (hj : j < (repChars.getD 35 []).length)
    (hq : (normIsRep.getD 35 []).getD j false = true) :
    species (Q2.reps (⟨35, by decide⟩ : Fin 148)) (colE2 ⟨35, by decide⟩ 20 hp)
        (rowE2 (⟨35, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨35, by decide⟩ : Fin 148))
        (colE1 ⟨35, by decide⟩ 20 (transLenTr ⟨35, by decide⟩ 20 hp))
        (rowE1 (⟨35, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨35, by decide⟩ : Fin 148) ⟨35, by decide⟩ _
      (validAt ⟨35, by decide⟩ (listedAt ⟨35, by decide⟩ hj))
      (colE1 ⟨35, by decide⟩ 20 (transLenTr ⟨35, by decide⟩ 20 hp)) T35_35
      hfix35_35 hinj35_35 hcardT35_35
      (fun i => conj_mem_of_fixedPoints _ _ (T35_35 i) (hfix35_35 i) _)
      ⟨35, by decide⟩ ⟨35, by decide⟩ _
      (Q2.validAt ⟨35, by decide⟩ (Q2.listedAt ⟨35, by decide⟩
        (alnCheck_rep ⟨35, by decide⟩ hj hq).1))
      (colE2 ⟨35, by decide⟩ 20 hp) Q2.T35_35_2 Q2.hfix35_35_2 Q2.hinj35_35_2
      Q2.hcardT35_35_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T35_35_2 i) (Q2.hfix35_35_2 i) _)
      ?_).symm
  rw [show colData1 (⟨35, by decide⟩ : Fin 148)
        ((colE1 ⟨35, by decide⟩ 20 (transLenTr ⟨35, by decide⟩ 20 hp) : ↥(reps ⟨35, by decide⟩)) : Coordinate 1)
        T35_35 = colFn colCert_35_35_20.D (m := 25) from colCert_35_35_20.bind1,
    show colData2 (⟨35, by decide⟩ : Fin 148)
        ((colE2 ⟨35, by decide⟩ 20 hp : ↥(Q2.reps ⟨35, by decide⟩)) : Coordinate 2)
        Q2.T35_35_2 = colFn colCert_35_35_20.D (m := 25) from colCert_35_35_20.bind2]
  exact alnAll_35_35_20 j hj hq

theorem leaf_36_12_0 (hp : 0 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 36 []).length)
    (hq : (normIsRep.getD 36 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 0 hp)
        (rowE2 (⟨36, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp))
        (rowE1 (⟨36, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨36, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨36, by decide⟩ (listedAt ⟨36, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp)) T36_12
      hfix36_12 hinj36_12 hcardT36_12
      (fun i => conj_mem_of_fixedPoints _ _ (T36_12 i) (hfix36_12 i) _)
      ⟨36, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨36, by decide⟩ (Q2.listedAt ⟨36, by decide⟩
        (alnCheck_rep ⟨36, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 0 hp) Q2.T36_12_2 Q2.hfix36_12_2 Q2.hinj36_12_2
      Q2.hcardT36_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T36_12_2 i) (Q2.hfix36_12_2 i) _)
      ?_).symm
  rw [show colData1 (⟨36, by decide⟩ : Fin 148)
        ((colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp) : ↥(reps ⟨12, by decide⟩)) : Coordinate 1)
        T36_12 = colFn colCert_36_12_0.D (m := 125) from colCert_36_12_0.bind1,
    show colData2 (⟨36, by decide⟩ : Fin 148)
        ((colE2 ⟨12, by decide⟩ 0 hp : ↥(Q2.reps ⟨12, by decide⟩)) : Coordinate 2)
        Q2.T36_12_2 = colFn colCert_36_12_0.D (m := 125) from colCert_36_12_0.bind2]
  exact alnAll_36_12_0 j hj hq

theorem leaf_36_12_1 (hp : 1 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 36 []).length)
    (hq : (normIsRep.getD 36 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 1 hp)
        (rowE2 (⟨36, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp))
        (rowE1 (⟨36, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨36, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨36, by decide⟩ (listedAt ⟨36, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp)) T36_12
      hfix36_12 hinj36_12 hcardT36_12
      (fun i => conj_mem_of_fixedPoints _ _ (T36_12 i) (hfix36_12 i) _)
      ⟨36, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨36, by decide⟩ (Q2.listedAt ⟨36, by decide⟩
        (alnCheck_rep ⟨36, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 1 hp) Q2.T36_12_2 Q2.hfix36_12_2 Q2.hinj36_12_2
      Q2.hcardT36_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T36_12_2 i) (Q2.hfix36_12_2 i) _)
      ?_).symm
  rw [show colData1 (⟨36, by decide⟩ : Fin 148)
        ((colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp) : ↥(reps ⟨12, by decide⟩)) : Coordinate 1)
        T36_12 = colFn colCert_36_12_1.D (m := 125) from colCert_36_12_1.bind1,
    show colData2 (⟨36, by decide⟩ : Fin 148)
        ((colE2 ⟨12, by decide⟩ 1 hp : ↥(Q2.reps ⟨12, by decide⟩)) : Coordinate 2)
        Q2.T36_12_2 = colFn colCert_36_12_1.D (m := 125) from colCert_36_12_1.bind2]
  exact alnAll_36_12_1 j hj hq

theorem leaf_36_12_2 (hp : 2 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 36 []).length)
    (hq : (normIsRep.getD 36 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 2 hp)
        (rowE2 (⟨36, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp))
        (rowE1 (⟨36, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨36, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨36, by decide⟩ (listedAt ⟨36, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp)) T36_12
      hfix36_12 hinj36_12 hcardT36_12
      (fun i => conj_mem_of_fixedPoints _ _ (T36_12 i) (hfix36_12 i) _)
      ⟨36, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨36, by decide⟩ (Q2.listedAt ⟨36, by decide⟩
        (alnCheck_rep ⟨36, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 2 hp) Q2.T36_12_2 Q2.hfix36_12_2 Q2.hinj36_12_2
      Q2.hcardT36_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T36_12_2 i) (Q2.hfix36_12_2 i) _)
      ?_).symm
  rw [show colData1 (⟨36, by decide⟩ : Fin 148)
        ((colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp) : ↥(reps ⟨12, by decide⟩)) : Coordinate 1)
        T36_12 = colFn colCert_36_12_2.D (m := 125) from colCert_36_12_2.bind1,
    show colData2 (⟨36, by decide⟩ : Fin 148)
        ((colE2 ⟨12, by decide⟩ 2 hp : ↥(Q2.reps ⟨12, by decide⟩)) : Coordinate 2)
        Q2.T36_12_2 = colFn colCert_36_12_2.D (m := 125) from colCert_36_12_2.bind2]
  exact alnAll_36_12_2 j hj hq

theorem leaf_36_12_3 (hp : 3 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 36 []).length)
    (hq : (normIsRep.getD 36 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 3 hp)
        (rowE2 (⟨36, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp))
        (rowE1 (⟨36, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨36, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨36, by decide⟩ (listedAt ⟨36, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp)) T36_12
      hfix36_12 hinj36_12 hcardT36_12
      (fun i => conj_mem_of_fixedPoints _ _ (T36_12 i) (hfix36_12 i) _)
      ⟨36, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨36, by decide⟩ (Q2.listedAt ⟨36, by decide⟩
        (alnCheck_rep ⟨36, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 3 hp) Q2.T36_12_2 Q2.hfix36_12_2 Q2.hinj36_12_2
      Q2.hcardT36_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T36_12_2 i) (Q2.hfix36_12_2 i) _)
      ?_).symm
  rw [show colData1 (⟨36, by decide⟩ : Fin 148)
        ((colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp) : ↥(reps ⟨12, by decide⟩)) : Coordinate 1)
        T36_12 = colFn colCert_36_12_3.D (m := 125) from colCert_36_12_3.bind1,
    show colData2 (⟨36, by decide⟩ : Fin 148)
        ((colE2 ⟨12, by decide⟩ 3 hp : ↥(Q2.reps ⟨12, by decide⟩)) : Coordinate 2)
        Q2.T36_12_2 = colFn colCert_36_12_3.D (m := 125) from colCert_36_12_3.bind2]
  exact alnAll_36_12_3 j hj hq

theorem leaf_36_12_4 (hp : 4 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 36 []).length)
    (hq : (normIsRep.getD 36 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 4 hp)
        (rowE2 (⟨36, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp))
        (rowE1 (⟨36, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨36, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨36, by decide⟩ (listedAt ⟨36, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp)) T36_12
      hfix36_12 hinj36_12 hcardT36_12
      (fun i => conj_mem_of_fixedPoints _ _ (T36_12 i) (hfix36_12 i) _)
      ⟨36, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨36, by decide⟩ (Q2.listedAt ⟨36, by decide⟩
        (alnCheck_rep ⟨36, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 4 hp) Q2.T36_12_2 Q2.hfix36_12_2 Q2.hinj36_12_2
      Q2.hcardT36_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T36_12_2 i) (Q2.hfix36_12_2 i) _)
      ?_).symm
  rw [show colData1 (⟨36, by decide⟩ : Fin 148)
        ((colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp) : ↥(reps ⟨12, by decide⟩)) : Coordinate 1)
        T36_12 = colFn colCert_36_12_4.D (m := 125) from colCert_36_12_4.bind1,
    show colData2 (⟨36, by decide⟩ : Fin 148)
        ((colE2 ⟨12, by decide⟩ 4 hp : ↥(Q2.reps ⟨12, by decide⟩)) : Coordinate 2)
        Q2.T36_12_2 = colFn colCert_36_12_4.D (m := 125) from colCert_36_12_4.bind2]
  exact alnAll_36_12_4 j hj hq

theorem leaf_36_36_0 (hp : 0 < (Q2.transData.getD 36 []).length)
    (j : Nat) (hj : j < (repChars.getD 36 []).length)
    (hq : (normIsRep.getD 36 []).getD j false = true) :
    species (Q2.reps (⟨36, by decide⟩ : Fin 148)) (colE2 ⟨36, by decide⟩ 0 hp)
        (rowE2 (⟨36, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨36, by decide⟩ : Fin 148))
        (colE1 ⟨36, by decide⟩ 0 (transLenTr ⟨36, by decide⟩ 0 hp))
        (rowE1 (⟨36, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨36, by decide⟩ : Fin 148) ⟨36, by decide⟩ _
      (validAt ⟨36, by decide⟩ (listedAt ⟨36, by decide⟩ hj))
      (colE1 ⟨36, by decide⟩ 0 (transLenTr ⟨36, by decide⟩ 0 hp)) T36_36
      hfix36_36 hinj36_36 hcardT36_36
      (fun i => conj_mem_of_fixedPoints _ _ (T36_36 i) (hfix36_36 i) _)
      ⟨36, by decide⟩ ⟨36, by decide⟩ _
      (Q2.validAt ⟨36, by decide⟩ (Q2.listedAt ⟨36, by decide⟩
        (alnCheck_rep ⟨36, by decide⟩ hj hq).1))
      (colE2 ⟨36, by decide⟩ 0 hp) Q2.T36_36_2 Q2.hfix36_36_2 Q2.hinj36_36_2
      Q2.hcardT36_36_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T36_36_2 i) (Q2.hfix36_36_2 i) _)
      ?_).symm
  rw [show colData1 (⟨36, by decide⟩ : Fin 148)
        ((colE1 ⟨36, by decide⟩ 0 (transLenTr ⟨36, by decide⟩ 0 hp) : ↥(reps ⟨36, by decide⟩)) : Coordinate 1)
        T36_36 = colFn colCert_36_36_0.D (m := 25) from colCert_36_36_0.bind1,
    show colData2 (⟨36, by decide⟩ : Fin 148)
        ((colE2 ⟨36, by decide⟩ 0 hp : ↥(Q2.reps ⟨36, by decide⟩)) : Coordinate 2)
        Q2.T36_36_2 = colFn colCert_36_36_0.D (m := 25) from colCert_36_36_0.bind2]
  exact alnAll_36_36_0 j hj hq

theorem leaf_36_36_1 (hp : 1 < (Q2.transData.getD 36 []).length)
    (j : Nat) (hj : j < (repChars.getD 36 []).length)
    (hq : (normIsRep.getD 36 []).getD j false = true) :
    species (Q2.reps (⟨36, by decide⟩ : Fin 148)) (colE2 ⟨36, by decide⟩ 1 hp)
        (rowE2 (⟨36, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨36, by decide⟩ : Fin 148))
        (colE1 ⟨36, by decide⟩ 1 (transLenTr ⟨36, by decide⟩ 1 hp))
        (rowE1 (⟨36, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨36, by decide⟩ : Fin 148) ⟨36, by decide⟩ _
      (validAt ⟨36, by decide⟩ (listedAt ⟨36, by decide⟩ hj))
      (colE1 ⟨36, by decide⟩ 1 (transLenTr ⟨36, by decide⟩ 1 hp)) T36_36
      hfix36_36 hinj36_36 hcardT36_36
      (fun i => conj_mem_of_fixedPoints _ _ (T36_36 i) (hfix36_36 i) _)
      ⟨36, by decide⟩ ⟨36, by decide⟩ _
      (Q2.validAt ⟨36, by decide⟩ (Q2.listedAt ⟨36, by decide⟩
        (alnCheck_rep ⟨36, by decide⟩ hj hq).1))
      (colE2 ⟨36, by decide⟩ 1 hp) Q2.T36_36_2 Q2.hfix36_36_2 Q2.hinj36_36_2
      Q2.hcardT36_36_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T36_36_2 i) (Q2.hfix36_36_2 i) _)
      ?_).symm
  rw [show colData1 (⟨36, by decide⟩ : Fin 148)
        ((colE1 ⟨36, by decide⟩ 1 (transLenTr ⟨36, by decide⟩ 1 hp) : ↥(reps ⟨36, by decide⟩)) : Coordinate 1)
        T36_36 = colFn colCert_36_36_1.D (m := 25) from colCert_36_36_1.bind1,
    show colData2 (⟨36, by decide⟩ : Fin 148)
        ((colE2 ⟨36, by decide⟩ 1 hp : ↥(Q2.reps ⟨36, by decide⟩)) : Coordinate 2)
        Q2.T36_36_2 = colFn colCert_36_36_1.D (m := 25) from colCert_36_36_1.bind2]
  exact alnAll_36_36_1 j hj hq

theorem leaf_36_36_2 (hp : 2 < (Q2.transData.getD 36 []).length)
    (j : Nat) (hj : j < (repChars.getD 36 []).length)
    (hq : (normIsRep.getD 36 []).getD j false = true) :
    species (Q2.reps (⟨36, by decide⟩ : Fin 148)) (colE2 ⟨36, by decide⟩ 2 hp)
        (rowE2 (⟨36, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨36, by decide⟩ : Fin 148))
        (colE1 ⟨36, by decide⟩ 2 (transLenTr ⟨36, by decide⟩ 2 hp))
        (rowE1 (⟨36, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨36, by decide⟩ : Fin 148) ⟨36, by decide⟩ _
      (validAt ⟨36, by decide⟩ (listedAt ⟨36, by decide⟩ hj))
      (colE1 ⟨36, by decide⟩ 2 (transLenTr ⟨36, by decide⟩ 2 hp)) T36_36
      hfix36_36 hinj36_36 hcardT36_36
      (fun i => conj_mem_of_fixedPoints _ _ (T36_36 i) (hfix36_36 i) _)
      ⟨36, by decide⟩ ⟨36, by decide⟩ _
      (Q2.validAt ⟨36, by decide⟩ (Q2.listedAt ⟨36, by decide⟩
        (alnCheck_rep ⟨36, by decide⟩ hj hq).1))
      (colE2 ⟨36, by decide⟩ 2 hp) Q2.T36_36_2 Q2.hfix36_36_2 Q2.hinj36_36_2
      Q2.hcardT36_36_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T36_36_2 i) (Q2.hfix36_36_2 i) _)
      ?_).symm
  rw [show colData1 (⟨36, by decide⟩ : Fin 148)
        ((colE1 ⟨36, by decide⟩ 2 (transLenTr ⟨36, by decide⟩ 2 hp) : ↥(reps ⟨36, by decide⟩)) : Coordinate 1)
        T36_36 = colFn colCert_36_36_2.D (m := 25) from colCert_36_36_2.bind1,
    show colData2 (⟨36, by decide⟩ : Fin 148)
        ((colE2 ⟨36, by decide⟩ 2 hp : ↥(Q2.reps ⟨36, by decide⟩)) : Coordinate 2)
        Q2.T36_36_2 = colFn colCert_36_36_2.D (m := 25) from colCert_36_36_2.bind2]
  exact alnAll_36_36_2 j hj hq

theorem leaf_36_36_3 (hp : 3 < (Q2.transData.getD 36 []).length)
    (j : Nat) (hj : j < (repChars.getD 36 []).length)
    (hq : (normIsRep.getD 36 []).getD j false = true) :
    species (Q2.reps (⟨36, by decide⟩ : Fin 148)) (colE2 ⟨36, by decide⟩ 3 hp)
        (rowE2 (⟨36, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨36, by decide⟩ : Fin 148))
        (colE1 ⟨36, by decide⟩ 3 (transLenTr ⟨36, by decide⟩ 3 hp))
        (rowE1 (⟨36, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨36, by decide⟩ : Fin 148) ⟨36, by decide⟩ _
      (validAt ⟨36, by decide⟩ (listedAt ⟨36, by decide⟩ hj))
      (colE1 ⟨36, by decide⟩ 3 (transLenTr ⟨36, by decide⟩ 3 hp)) T36_36
      hfix36_36 hinj36_36 hcardT36_36
      (fun i => conj_mem_of_fixedPoints _ _ (T36_36 i) (hfix36_36 i) _)
      ⟨36, by decide⟩ ⟨36, by decide⟩ _
      (Q2.validAt ⟨36, by decide⟩ (Q2.listedAt ⟨36, by decide⟩
        (alnCheck_rep ⟨36, by decide⟩ hj hq).1))
      (colE2 ⟨36, by decide⟩ 3 hp) Q2.T36_36_2 Q2.hfix36_36_2 Q2.hinj36_36_2
      Q2.hcardT36_36_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T36_36_2 i) (Q2.hfix36_36_2 i) _)
      ?_).symm
  rw [show colData1 (⟨36, by decide⟩ : Fin 148)
        ((colE1 ⟨36, by decide⟩ 3 (transLenTr ⟨36, by decide⟩ 3 hp) : ↥(reps ⟨36, by decide⟩)) : Coordinate 1)
        T36_36 = colFn colCert_36_36_3.D (m := 25) from colCert_36_36_3.bind1,
    show colData2 (⟨36, by decide⟩ : Fin 148)
        ((colE2 ⟨36, by decide⟩ 3 hp : ↥(Q2.reps ⟨36, by decide⟩)) : Coordinate 2)
        Q2.T36_36_2 = colFn colCert_36_36_3.D (m := 25) from colCert_36_36_3.bind2]
  exact alnAll_36_36_3 j hj hq

theorem leaf_36_36_4 (hp : 4 < (Q2.transData.getD 36 []).length)
    (j : Nat) (hj : j < (repChars.getD 36 []).length)
    (hq : (normIsRep.getD 36 []).getD j false = true) :
    species (Q2.reps (⟨36, by decide⟩ : Fin 148)) (colE2 ⟨36, by decide⟩ 4 hp)
        (rowE2 (⟨36, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨36, by decide⟩ : Fin 148))
        (colE1 ⟨36, by decide⟩ 4 (transLenTr ⟨36, by decide⟩ 4 hp))
        (rowE1 (⟨36, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨36, by decide⟩ : Fin 148) ⟨36, by decide⟩ _
      (validAt ⟨36, by decide⟩ (listedAt ⟨36, by decide⟩ hj))
      (colE1 ⟨36, by decide⟩ 4 (transLenTr ⟨36, by decide⟩ 4 hp)) T36_36
      hfix36_36 hinj36_36 hcardT36_36
      (fun i => conj_mem_of_fixedPoints _ _ (T36_36 i) (hfix36_36 i) _)
      ⟨36, by decide⟩ ⟨36, by decide⟩ _
      (Q2.validAt ⟨36, by decide⟩ (Q2.listedAt ⟨36, by decide⟩
        (alnCheck_rep ⟨36, by decide⟩ hj hq).1))
      (colE2 ⟨36, by decide⟩ 4 hp) Q2.T36_36_2 Q2.hfix36_36_2 Q2.hinj36_36_2
      Q2.hcardT36_36_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T36_36_2 i) (Q2.hfix36_36_2 i) _)
      ?_).symm
  rw [show colData1 (⟨36, by decide⟩ : Fin 148)
        ((colE1 ⟨36, by decide⟩ 4 (transLenTr ⟨36, by decide⟩ 4 hp) : ↥(reps ⟨36, by decide⟩)) : Coordinate 1)
        T36_36 = colFn colCert_36_36_4.D (m := 25) from colCert_36_36_4.bind1,
    show colData2 (⟨36, by decide⟩ : Fin 148)
        ((colE2 ⟨36, by decide⟩ 4 hp : ↥(Q2.reps ⟨36, by decide⟩)) : Coordinate 2)
        Q2.T36_36_2 = colFn colCert_36_36_4.D (m := 25) from colCert_36_36_4.bind2]
  exact alnAll_36_36_4 j hj hq

theorem leaf_36_36_5 (hp : 5 < (Q2.transData.getD 36 []).length)
    (j : Nat) (hj : j < (repChars.getD 36 []).length)
    (hq : (normIsRep.getD 36 []).getD j false = true) :
    species (Q2.reps (⟨36, by decide⟩ : Fin 148)) (colE2 ⟨36, by decide⟩ 5 hp)
        (rowE2 (⟨36, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨36, by decide⟩ : Fin 148))
        (colE1 ⟨36, by decide⟩ 5 (transLenTr ⟨36, by decide⟩ 5 hp))
        (rowE1 (⟨36, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨36, by decide⟩ : Fin 148) ⟨36, by decide⟩ _
      (validAt ⟨36, by decide⟩ (listedAt ⟨36, by decide⟩ hj))
      (colE1 ⟨36, by decide⟩ 5 (transLenTr ⟨36, by decide⟩ 5 hp)) T36_36
      hfix36_36 hinj36_36 hcardT36_36
      (fun i => conj_mem_of_fixedPoints _ _ (T36_36 i) (hfix36_36 i) _)
      ⟨36, by decide⟩ ⟨36, by decide⟩ _
      (Q2.validAt ⟨36, by decide⟩ (Q2.listedAt ⟨36, by decide⟩
        (alnCheck_rep ⟨36, by decide⟩ hj hq).1))
      (colE2 ⟨36, by decide⟩ 5 hp) Q2.T36_36_2 Q2.hfix36_36_2 Q2.hinj36_36_2
      Q2.hcardT36_36_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T36_36_2 i) (Q2.hfix36_36_2 i) _)
      ?_).symm
  rw [show colData1 (⟨36, by decide⟩ : Fin 148)
        ((colE1 ⟨36, by decide⟩ 5 (transLenTr ⟨36, by decide⟩ 5 hp) : ↥(reps ⟨36, by decide⟩)) : Coordinate 1)
        T36_36 = colFn colCert_36_36_5.D (m := 25) from colCert_36_36_5.bind1,
    show colData2 (⟨36, by decide⟩ : Fin 148)
        ((colE2 ⟨36, by decide⟩ 5 hp : ↥(Q2.reps ⟨36, by decide⟩)) : Coordinate 2)
        Q2.T36_36_2 = colFn colCert_36_36_5.D (m := 25) from colCert_36_36_5.bind2]
  exact alnAll_36_36_5 j hj hq

theorem leaf_36_36_10 (hp : 10 < (Q2.transData.getD 36 []).length)
    (j : Nat) (hj : j < (repChars.getD 36 []).length)
    (hq : (normIsRep.getD 36 []).getD j false = true) :
    species (Q2.reps (⟨36, by decide⟩ : Fin 148)) (colE2 ⟨36, by decide⟩ 10 hp)
        (rowE2 (⟨36, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨36, by decide⟩ : Fin 148))
        (colE1 ⟨36, by decide⟩ 10 (transLenTr ⟨36, by decide⟩ 10 hp))
        (rowE1 (⟨36, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨36, by decide⟩ : Fin 148) ⟨36, by decide⟩ _
      (validAt ⟨36, by decide⟩ (listedAt ⟨36, by decide⟩ hj))
      (colE1 ⟨36, by decide⟩ 10 (transLenTr ⟨36, by decide⟩ 10 hp)) T36_36
      hfix36_36 hinj36_36 hcardT36_36
      (fun i => conj_mem_of_fixedPoints _ _ (T36_36 i) (hfix36_36 i) _)
      ⟨36, by decide⟩ ⟨36, by decide⟩ _
      (Q2.validAt ⟨36, by decide⟩ (Q2.listedAt ⟨36, by decide⟩
        (alnCheck_rep ⟨36, by decide⟩ hj hq).1))
      (colE2 ⟨36, by decide⟩ 10 hp) Q2.T36_36_2 Q2.hfix36_36_2 Q2.hinj36_36_2
      Q2.hcardT36_36_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T36_36_2 i) (Q2.hfix36_36_2 i) _)
      ?_).symm
  rw [show colData1 (⟨36, by decide⟩ : Fin 148)
        ((colE1 ⟨36, by decide⟩ 10 (transLenTr ⟨36, by decide⟩ 10 hp) : ↥(reps ⟨36, by decide⟩)) : Coordinate 1)
        T36_36 = colFn colCert_36_36_10.D (m := 25) from colCert_36_36_10.bind1,
    show colData2 (⟨36, by decide⟩ : Fin 148)
        ((colE2 ⟨36, by decide⟩ 10 hp : ↥(Q2.reps ⟨36, by decide⟩)) : Coordinate 2)
        Q2.T36_36_2 = colFn colCert_36_36_10.D (m := 25) from colCert_36_36_10.bind2]
  exact alnAll_36_36_10 j hj hq

theorem leaf_36_36_15 (hp : 15 < (Q2.transData.getD 36 []).length)
    (j : Nat) (hj : j < (repChars.getD 36 []).length)
    (hq : (normIsRep.getD 36 []).getD j false = true) :
    species (Q2.reps (⟨36, by decide⟩ : Fin 148)) (colE2 ⟨36, by decide⟩ 15 hp)
        (rowE2 (⟨36, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨36, by decide⟩ : Fin 148))
        (colE1 ⟨36, by decide⟩ 15 (transLenTr ⟨36, by decide⟩ 15 hp))
        (rowE1 (⟨36, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨36, by decide⟩ : Fin 148) ⟨36, by decide⟩ _
      (validAt ⟨36, by decide⟩ (listedAt ⟨36, by decide⟩ hj))
      (colE1 ⟨36, by decide⟩ 15 (transLenTr ⟨36, by decide⟩ 15 hp)) T36_36
      hfix36_36 hinj36_36 hcardT36_36
      (fun i => conj_mem_of_fixedPoints _ _ (T36_36 i) (hfix36_36 i) _)
      ⟨36, by decide⟩ ⟨36, by decide⟩ _
      (Q2.validAt ⟨36, by decide⟩ (Q2.listedAt ⟨36, by decide⟩
        (alnCheck_rep ⟨36, by decide⟩ hj hq).1))
      (colE2 ⟨36, by decide⟩ 15 hp) Q2.T36_36_2 Q2.hfix36_36_2 Q2.hinj36_36_2
      Q2.hcardT36_36_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T36_36_2 i) (Q2.hfix36_36_2 i) _)
      ?_).symm
  rw [show colData1 (⟨36, by decide⟩ : Fin 148)
        ((colE1 ⟨36, by decide⟩ 15 (transLenTr ⟨36, by decide⟩ 15 hp) : ↥(reps ⟨36, by decide⟩)) : Coordinate 1)
        T36_36 = colFn colCert_36_36_15.D (m := 25) from colCert_36_36_15.bind1,
    show colData2 (⟨36, by decide⟩ : Fin 148)
        ((colE2 ⟨36, by decide⟩ 15 hp : ↥(Q2.reps ⟨36, by decide⟩)) : Coordinate 2)
        Q2.T36_36_2 = colFn colCert_36_36_15.D (m := 25) from colCert_36_36_15.bind2]
  exact alnAll_36_36_15 j hj hq

theorem leaf_36_36_20 (hp : 20 < (Q2.transData.getD 36 []).length)
    (j : Nat) (hj : j < (repChars.getD 36 []).length)
    (hq : (normIsRep.getD 36 []).getD j false = true) :
    species (Q2.reps (⟨36, by decide⟩ : Fin 148)) (colE2 ⟨36, by decide⟩ 20 hp)
        (rowE2 (⟨36, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨36, by decide⟩ : Fin 148))
        (colE1 ⟨36, by decide⟩ 20 (transLenTr ⟨36, by decide⟩ 20 hp))
        (rowE1 (⟨36, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨36, by decide⟩ : Fin 148) ⟨36, by decide⟩ _
      (validAt ⟨36, by decide⟩ (listedAt ⟨36, by decide⟩ hj))
      (colE1 ⟨36, by decide⟩ 20 (transLenTr ⟨36, by decide⟩ 20 hp)) T36_36
      hfix36_36 hinj36_36 hcardT36_36
      (fun i => conj_mem_of_fixedPoints _ _ (T36_36 i) (hfix36_36 i) _)
      ⟨36, by decide⟩ ⟨36, by decide⟩ _
      (Q2.validAt ⟨36, by decide⟩ (Q2.listedAt ⟨36, by decide⟩
        (alnCheck_rep ⟨36, by decide⟩ hj hq).1))
      (colE2 ⟨36, by decide⟩ 20 hp) Q2.T36_36_2 Q2.hfix36_36_2 Q2.hinj36_36_2
      Q2.hcardT36_36_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T36_36_2 i) (Q2.hfix36_36_2 i) _)
      ?_).symm
  rw [show colData1 (⟨36, by decide⟩ : Fin 148)
        ((colE1 ⟨36, by decide⟩ 20 (transLenTr ⟨36, by decide⟩ 20 hp) : ↥(reps ⟨36, by decide⟩)) : Coordinate 1)
        T36_36 = colFn colCert_36_36_20.D (m := 25) from colCert_36_36_20.bind1,
    show colData2 (⟨36, by decide⟩ : Fin 148)
        ((colE2 ⟨36, by decide⟩ 20 hp : ↥(Q2.reps ⟨36, by decide⟩)) : Coordinate 2)
        Q2.T36_36_2 = colFn colCert_36_36_20.D (m := 25) from colCert_36_36_20.bind2]
  exact alnAll_36_36_20 j hj hq

theorem leaf_37_12_0 (hp : 0 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 37 []).length)
    (hq : (normIsRep.getD 37 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 0 hp)
        (rowE2 (⟨37, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp))
        (rowE1 (⟨37, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨37, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨37, by decide⟩ (listedAt ⟨37, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp)) T37_12
      hfix37_12 hinj37_12 hcardT37_12
      (fun i => conj_mem_of_fixedPoints _ _ (T37_12 i) (hfix37_12 i) _)
      ⟨37, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨37, by decide⟩ (Q2.listedAt ⟨37, by decide⟩
        (alnCheck_rep ⟨37, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 0 hp) Q2.T37_12_2 Q2.hfix37_12_2 Q2.hinj37_12_2
      Q2.hcardT37_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T37_12_2 i) (Q2.hfix37_12_2 i) _)
      ?_).symm
  rw [show colData1 (⟨37, by decide⟩ : Fin 148)
        ((colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp) : ↥(reps ⟨12, by decide⟩)) : Coordinate 1)
        T37_12 = colFn colCert_37_12_0.D (m := 125) from colCert_37_12_0.bind1,
    show colData2 (⟨37, by decide⟩ : Fin 148)
        ((colE2 ⟨12, by decide⟩ 0 hp : ↥(Q2.reps ⟨12, by decide⟩)) : Coordinate 2)
        Q2.T37_12_2 = colFn colCert_37_12_0.D (m := 125) from colCert_37_12_0.bind2]
  exact alnAll_37_12_0 j hj hq

theorem leaf_37_12_1 (hp : 1 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 37 []).length)
    (hq : (normIsRep.getD 37 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 1 hp)
        (rowE2 (⟨37, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp))
        (rowE1 (⟨37, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨37, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨37, by decide⟩ (listedAt ⟨37, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp)) T37_12
      hfix37_12 hinj37_12 hcardT37_12
      (fun i => conj_mem_of_fixedPoints _ _ (T37_12 i) (hfix37_12 i) _)
      ⟨37, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨37, by decide⟩ (Q2.listedAt ⟨37, by decide⟩
        (alnCheck_rep ⟨37, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 1 hp) Q2.T37_12_2 Q2.hfix37_12_2 Q2.hinj37_12_2
      Q2.hcardT37_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T37_12_2 i) (Q2.hfix37_12_2 i) _)
      ?_).symm
  rw [show colData1 (⟨37, by decide⟩ : Fin 148)
        ((colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp) : ↥(reps ⟨12, by decide⟩)) : Coordinate 1)
        T37_12 = colFn colCert_37_12_1.D (m := 125) from colCert_37_12_1.bind1,
    show colData2 (⟨37, by decide⟩ : Fin 148)
        ((colE2 ⟨12, by decide⟩ 1 hp : ↥(Q2.reps ⟨12, by decide⟩)) : Coordinate 2)
        Q2.T37_12_2 = colFn colCert_37_12_1.D (m := 125) from colCert_37_12_1.bind2]
  exact alnAll_37_12_1 j hj hq

theorem leaf_37_12_2 (hp : 2 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 37 []).length)
    (hq : (normIsRep.getD 37 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 2 hp)
        (rowE2 (⟨37, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp))
        (rowE1 (⟨37, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨37, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨37, by decide⟩ (listedAt ⟨37, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp)) T37_12
      hfix37_12 hinj37_12 hcardT37_12
      (fun i => conj_mem_of_fixedPoints _ _ (T37_12 i) (hfix37_12 i) _)
      ⟨37, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨37, by decide⟩ (Q2.listedAt ⟨37, by decide⟩
        (alnCheck_rep ⟨37, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 2 hp) Q2.T37_12_2 Q2.hfix37_12_2 Q2.hinj37_12_2
      Q2.hcardT37_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T37_12_2 i) (Q2.hfix37_12_2 i) _)
      ?_).symm
  rw [show colData1 (⟨37, by decide⟩ : Fin 148)
        ((colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp) : ↥(reps ⟨12, by decide⟩)) : Coordinate 1)
        T37_12 = colFn colCert_37_12_2.D (m := 125) from colCert_37_12_2.bind1,
    show colData2 (⟨37, by decide⟩ : Fin 148)
        ((colE2 ⟨12, by decide⟩ 2 hp : ↥(Q2.reps ⟨12, by decide⟩)) : Coordinate 2)
        Q2.T37_12_2 = colFn colCert_37_12_2.D (m := 125) from colCert_37_12_2.bind2]
  exact alnAll_37_12_2 j hj hq

theorem leaf_37_12_3 (hp : 3 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 37 []).length)
    (hq : (normIsRep.getD 37 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 3 hp)
        (rowE2 (⟨37, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp))
        (rowE1 (⟨37, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨37, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨37, by decide⟩ (listedAt ⟨37, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp)) T37_12
      hfix37_12 hinj37_12 hcardT37_12
      (fun i => conj_mem_of_fixedPoints _ _ (T37_12 i) (hfix37_12 i) _)
      ⟨37, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨37, by decide⟩ (Q2.listedAt ⟨37, by decide⟩
        (alnCheck_rep ⟨37, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 3 hp) Q2.T37_12_2 Q2.hfix37_12_2 Q2.hinj37_12_2
      Q2.hcardT37_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T37_12_2 i) (Q2.hfix37_12_2 i) _)
      ?_).symm
  rw [show colData1 (⟨37, by decide⟩ : Fin 148)
        ((colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp) : ↥(reps ⟨12, by decide⟩)) : Coordinate 1)
        T37_12 = colFn colCert_37_12_3.D (m := 125) from colCert_37_12_3.bind1,
    show colData2 (⟨37, by decide⟩ : Fin 148)
        ((colE2 ⟨12, by decide⟩ 3 hp : ↥(Q2.reps ⟨12, by decide⟩)) : Coordinate 2)
        Q2.T37_12_2 = colFn colCert_37_12_3.D (m := 125) from colCert_37_12_3.bind2]
  exact alnAll_37_12_3 j hj hq

theorem leaf_37_12_4 (hp : 4 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 37 []).length)
    (hq : (normIsRep.getD 37 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 4 hp)
        (rowE2 (⟨37, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp))
        (rowE1 (⟨37, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨37, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨37, by decide⟩ (listedAt ⟨37, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp)) T37_12
      hfix37_12 hinj37_12 hcardT37_12
      (fun i => conj_mem_of_fixedPoints _ _ (T37_12 i) (hfix37_12 i) _)
      ⟨37, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨37, by decide⟩ (Q2.listedAt ⟨37, by decide⟩
        (alnCheck_rep ⟨37, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 4 hp) Q2.T37_12_2 Q2.hfix37_12_2 Q2.hinj37_12_2
      Q2.hcardT37_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T37_12_2 i) (Q2.hfix37_12_2 i) _)
      ?_).symm
  rw [show colData1 (⟨37, by decide⟩ : Fin 148)
        ((colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp) : ↥(reps ⟨12, by decide⟩)) : Coordinate 1)
        T37_12 = colFn colCert_37_12_4.D (m := 125) from colCert_37_12_4.bind1,
    show colData2 (⟨37, by decide⟩ : Fin 148)
        ((colE2 ⟨12, by decide⟩ 4 hp : ↥(Q2.reps ⟨12, by decide⟩)) : Coordinate 2)
        Q2.T37_12_2 = colFn colCert_37_12_4.D (m := 125) from colCert_37_12_4.bind2]
  exact alnAll_37_12_4 j hj hq

theorem leaf_37_37_0 (hp : 0 < (Q2.transData.getD 37 []).length)
    (j : Nat) (hj : j < (repChars.getD 37 []).length)
    (hq : (normIsRep.getD 37 []).getD j false = true) :
    species (Q2.reps (⟨37, by decide⟩ : Fin 148)) (colE2 ⟨37, by decide⟩ 0 hp)
        (rowE2 (⟨37, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨37, by decide⟩ : Fin 148))
        (colE1 ⟨37, by decide⟩ 0 (transLenTr ⟨37, by decide⟩ 0 hp))
        (rowE1 (⟨37, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨37, by decide⟩ : Fin 148) ⟨37, by decide⟩ _
      (validAt ⟨37, by decide⟩ (listedAt ⟨37, by decide⟩ hj))
      (colE1 ⟨37, by decide⟩ 0 (transLenTr ⟨37, by decide⟩ 0 hp)) T37_37
      hfix37_37 hinj37_37 hcardT37_37
      (fun i => conj_mem_of_fixedPoints _ _ (T37_37 i) (hfix37_37 i) _)
      ⟨37, by decide⟩ ⟨37, by decide⟩ _
      (Q2.validAt ⟨37, by decide⟩ (Q2.listedAt ⟨37, by decide⟩
        (alnCheck_rep ⟨37, by decide⟩ hj hq).1))
      (colE2 ⟨37, by decide⟩ 0 hp) Q2.T37_37_2 Q2.hfix37_37_2 Q2.hinj37_37_2
      Q2.hcardT37_37_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T37_37_2 i) (Q2.hfix37_37_2 i) _)
      ?_).symm
  rw [show colData1 (⟨37, by decide⟩ : Fin 148)
        ((colE1 ⟨37, by decide⟩ 0 (transLenTr ⟨37, by decide⟩ 0 hp) : ↥(reps ⟨37, by decide⟩)) : Coordinate 1)
        T37_37 = colFn colCert_37_37_0.D (m := 25) from colCert_37_37_0.bind1,
    show colData2 (⟨37, by decide⟩ : Fin 148)
        ((colE2 ⟨37, by decide⟩ 0 hp : ↥(Q2.reps ⟨37, by decide⟩)) : Coordinate 2)
        Q2.T37_37_2 = colFn colCert_37_37_0.D (m := 25) from colCert_37_37_0.bind2]
  exact alnAll_37_37_0 j hj hq

theorem leaf_37_37_1 (hp : 1 < (Q2.transData.getD 37 []).length)
    (j : Nat) (hj : j < (repChars.getD 37 []).length)
    (hq : (normIsRep.getD 37 []).getD j false = true) :
    species (Q2.reps (⟨37, by decide⟩ : Fin 148)) (colE2 ⟨37, by decide⟩ 1 hp)
        (rowE2 (⟨37, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨37, by decide⟩ : Fin 148))
        (colE1 ⟨37, by decide⟩ 1 (transLenTr ⟨37, by decide⟩ 1 hp))
        (rowE1 (⟨37, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨37, by decide⟩ : Fin 148) ⟨37, by decide⟩ _
      (validAt ⟨37, by decide⟩ (listedAt ⟨37, by decide⟩ hj))
      (colE1 ⟨37, by decide⟩ 1 (transLenTr ⟨37, by decide⟩ 1 hp)) T37_37
      hfix37_37 hinj37_37 hcardT37_37
      (fun i => conj_mem_of_fixedPoints _ _ (T37_37 i) (hfix37_37 i) _)
      ⟨37, by decide⟩ ⟨37, by decide⟩ _
      (Q2.validAt ⟨37, by decide⟩ (Q2.listedAt ⟨37, by decide⟩
        (alnCheck_rep ⟨37, by decide⟩ hj hq).1))
      (colE2 ⟨37, by decide⟩ 1 hp) Q2.T37_37_2 Q2.hfix37_37_2 Q2.hinj37_37_2
      Q2.hcardT37_37_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T37_37_2 i) (Q2.hfix37_37_2 i) _)
      ?_).symm
  rw [show colData1 (⟨37, by decide⟩ : Fin 148)
        ((colE1 ⟨37, by decide⟩ 1 (transLenTr ⟨37, by decide⟩ 1 hp) : ↥(reps ⟨37, by decide⟩)) : Coordinate 1)
        T37_37 = colFn colCert_37_37_1.D (m := 25) from colCert_37_37_1.bind1,
    show colData2 (⟨37, by decide⟩ : Fin 148)
        ((colE2 ⟨37, by decide⟩ 1 hp : ↥(Q2.reps ⟨37, by decide⟩)) : Coordinate 2)
        Q2.T37_37_2 = colFn colCert_37_37_1.D (m := 25) from colCert_37_37_1.bind2]
  exact alnAll_37_37_1 j hj hq

theorem leaf_37_37_2 (hp : 2 < (Q2.transData.getD 37 []).length)
    (j : Nat) (hj : j < (repChars.getD 37 []).length)
    (hq : (normIsRep.getD 37 []).getD j false = true) :
    species (Q2.reps (⟨37, by decide⟩ : Fin 148)) (colE2 ⟨37, by decide⟩ 2 hp)
        (rowE2 (⟨37, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨37, by decide⟩ : Fin 148))
        (colE1 ⟨37, by decide⟩ 2 (transLenTr ⟨37, by decide⟩ 2 hp))
        (rowE1 (⟨37, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨37, by decide⟩ : Fin 148) ⟨37, by decide⟩ _
      (validAt ⟨37, by decide⟩ (listedAt ⟨37, by decide⟩ hj))
      (colE1 ⟨37, by decide⟩ 2 (transLenTr ⟨37, by decide⟩ 2 hp)) T37_37
      hfix37_37 hinj37_37 hcardT37_37
      (fun i => conj_mem_of_fixedPoints _ _ (T37_37 i) (hfix37_37 i) _)
      ⟨37, by decide⟩ ⟨37, by decide⟩ _
      (Q2.validAt ⟨37, by decide⟩ (Q2.listedAt ⟨37, by decide⟩
        (alnCheck_rep ⟨37, by decide⟩ hj hq).1))
      (colE2 ⟨37, by decide⟩ 2 hp) Q2.T37_37_2 Q2.hfix37_37_2 Q2.hinj37_37_2
      Q2.hcardT37_37_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T37_37_2 i) (Q2.hfix37_37_2 i) _)
      ?_).symm
  rw [show colData1 (⟨37, by decide⟩ : Fin 148)
        ((colE1 ⟨37, by decide⟩ 2 (transLenTr ⟨37, by decide⟩ 2 hp) : ↥(reps ⟨37, by decide⟩)) : Coordinate 1)
        T37_37 = colFn colCert_37_37_2.D (m := 25) from colCert_37_37_2.bind1,
    show colData2 (⟨37, by decide⟩ : Fin 148)
        ((colE2 ⟨37, by decide⟩ 2 hp : ↥(Q2.reps ⟨37, by decide⟩)) : Coordinate 2)
        Q2.T37_37_2 = colFn colCert_37_37_2.D (m := 25) from colCert_37_37_2.bind2]
  exact alnAll_37_37_2 j hj hq

theorem leaf_37_37_3 (hp : 3 < (Q2.transData.getD 37 []).length)
    (j : Nat) (hj : j < (repChars.getD 37 []).length)
    (hq : (normIsRep.getD 37 []).getD j false = true) :
    species (Q2.reps (⟨37, by decide⟩ : Fin 148)) (colE2 ⟨37, by decide⟩ 3 hp)
        (rowE2 (⟨37, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨37, by decide⟩ : Fin 148))
        (colE1 ⟨37, by decide⟩ 3 (transLenTr ⟨37, by decide⟩ 3 hp))
        (rowE1 (⟨37, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨37, by decide⟩ : Fin 148) ⟨37, by decide⟩ _
      (validAt ⟨37, by decide⟩ (listedAt ⟨37, by decide⟩ hj))
      (colE1 ⟨37, by decide⟩ 3 (transLenTr ⟨37, by decide⟩ 3 hp)) T37_37
      hfix37_37 hinj37_37 hcardT37_37
      (fun i => conj_mem_of_fixedPoints _ _ (T37_37 i) (hfix37_37 i) _)
      ⟨37, by decide⟩ ⟨37, by decide⟩ _
      (Q2.validAt ⟨37, by decide⟩ (Q2.listedAt ⟨37, by decide⟩
        (alnCheck_rep ⟨37, by decide⟩ hj hq).1))
      (colE2 ⟨37, by decide⟩ 3 hp) Q2.T37_37_2 Q2.hfix37_37_2 Q2.hinj37_37_2
      Q2.hcardT37_37_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T37_37_2 i) (Q2.hfix37_37_2 i) _)
      ?_).symm
  rw [show colData1 (⟨37, by decide⟩ : Fin 148)
        ((colE1 ⟨37, by decide⟩ 3 (transLenTr ⟨37, by decide⟩ 3 hp) : ↥(reps ⟨37, by decide⟩)) : Coordinate 1)
        T37_37 = colFn colCert_37_37_3.D (m := 25) from colCert_37_37_3.bind1,
    show colData2 (⟨37, by decide⟩ : Fin 148)
        ((colE2 ⟨37, by decide⟩ 3 hp : ↥(Q2.reps ⟨37, by decide⟩)) : Coordinate 2)
        Q2.T37_37_2 = colFn colCert_37_37_3.D (m := 25) from colCert_37_37_3.bind2]
  exact alnAll_37_37_3 j hj hq

theorem leaf_37_37_4 (hp : 4 < (Q2.transData.getD 37 []).length)
    (j : Nat) (hj : j < (repChars.getD 37 []).length)
    (hq : (normIsRep.getD 37 []).getD j false = true) :
    species (Q2.reps (⟨37, by decide⟩ : Fin 148)) (colE2 ⟨37, by decide⟩ 4 hp)
        (rowE2 (⟨37, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨37, by decide⟩ : Fin 148))
        (colE1 ⟨37, by decide⟩ 4 (transLenTr ⟨37, by decide⟩ 4 hp))
        (rowE1 (⟨37, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨37, by decide⟩ : Fin 148) ⟨37, by decide⟩ _
      (validAt ⟨37, by decide⟩ (listedAt ⟨37, by decide⟩ hj))
      (colE1 ⟨37, by decide⟩ 4 (transLenTr ⟨37, by decide⟩ 4 hp)) T37_37
      hfix37_37 hinj37_37 hcardT37_37
      (fun i => conj_mem_of_fixedPoints _ _ (T37_37 i) (hfix37_37 i) _)
      ⟨37, by decide⟩ ⟨37, by decide⟩ _
      (Q2.validAt ⟨37, by decide⟩ (Q2.listedAt ⟨37, by decide⟩
        (alnCheck_rep ⟨37, by decide⟩ hj hq).1))
      (colE2 ⟨37, by decide⟩ 4 hp) Q2.T37_37_2 Q2.hfix37_37_2 Q2.hinj37_37_2
      Q2.hcardT37_37_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T37_37_2 i) (Q2.hfix37_37_2 i) _)
      ?_).symm
  rw [show colData1 (⟨37, by decide⟩ : Fin 148)
        ((colE1 ⟨37, by decide⟩ 4 (transLenTr ⟨37, by decide⟩ 4 hp) : ↥(reps ⟨37, by decide⟩)) : Coordinate 1)
        T37_37 = colFn colCert_37_37_4.D (m := 25) from colCert_37_37_4.bind1,
    show colData2 (⟨37, by decide⟩ : Fin 148)
        ((colE2 ⟨37, by decide⟩ 4 hp : ↥(Q2.reps ⟨37, by decide⟩)) : Coordinate 2)
        Q2.T37_37_2 = colFn colCert_37_37_4.D (m := 25) from colCert_37_37_4.bind2]
  exact alnAll_37_37_4 j hj hq

theorem leaf_37_37_5 (hp : 5 < (Q2.transData.getD 37 []).length)
    (j : Nat) (hj : j < (repChars.getD 37 []).length)
    (hq : (normIsRep.getD 37 []).getD j false = true) :
    species (Q2.reps (⟨37, by decide⟩ : Fin 148)) (colE2 ⟨37, by decide⟩ 5 hp)
        (rowE2 (⟨37, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨37, by decide⟩ : Fin 148))
        (colE1 ⟨37, by decide⟩ 5 (transLenTr ⟨37, by decide⟩ 5 hp))
        (rowE1 (⟨37, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨37, by decide⟩ : Fin 148) ⟨37, by decide⟩ _
      (validAt ⟨37, by decide⟩ (listedAt ⟨37, by decide⟩ hj))
      (colE1 ⟨37, by decide⟩ 5 (transLenTr ⟨37, by decide⟩ 5 hp)) T37_37
      hfix37_37 hinj37_37 hcardT37_37
      (fun i => conj_mem_of_fixedPoints _ _ (T37_37 i) (hfix37_37 i) _)
      ⟨37, by decide⟩ ⟨37, by decide⟩ _
      (Q2.validAt ⟨37, by decide⟩ (Q2.listedAt ⟨37, by decide⟩
        (alnCheck_rep ⟨37, by decide⟩ hj hq).1))
      (colE2 ⟨37, by decide⟩ 5 hp) Q2.T37_37_2 Q2.hfix37_37_2 Q2.hinj37_37_2
      Q2.hcardT37_37_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T37_37_2 i) (Q2.hfix37_37_2 i) _)
      ?_).symm
  rw [show colData1 (⟨37, by decide⟩ : Fin 148)
        ((colE1 ⟨37, by decide⟩ 5 (transLenTr ⟨37, by decide⟩ 5 hp) : ↥(reps ⟨37, by decide⟩)) : Coordinate 1)
        T37_37 = colFn colCert_37_37_5.D (m := 25) from colCert_37_37_5.bind1,
    show colData2 (⟨37, by decide⟩ : Fin 148)
        ((colE2 ⟨37, by decide⟩ 5 hp : ↥(Q2.reps ⟨37, by decide⟩)) : Coordinate 2)
        Q2.T37_37_2 = colFn colCert_37_37_5.D (m := 25) from colCert_37_37_5.bind2]
  exact alnAll_37_37_5 j hj hq

theorem leaf_37_37_10 (hp : 10 < (Q2.transData.getD 37 []).length)
    (j : Nat) (hj : j < (repChars.getD 37 []).length)
    (hq : (normIsRep.getD 37 []).getD j false = true) :
    species (Q2.reps (⟨37, by decide⟩ : Fin 148)) (colE2 ⟨37, by decide⟩ 10 hp)
        (rowE2 (⟨37, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨37, by decide⟩ : Fin 148))
        (colE1 ⟨37, by decide⟩ 10 (transLenTr ⟨37, by decide⟩ 10 hp))
        (rowE1 (⟨37, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨37, by decide⟩ : Fin 148) ⟨37, by decide⟩ _
      (validAt ⟨37, by decide⟩ (listedAt ⟨37, by decide⟩ hj))
      (colE1 ⟨37, by decide⟩ 10 (transLenTr ⟨37, by decide⟩ 10 hp)) T37_37
      hfix37_37 hinj37_37 hcardT37_37
      (fun i => conj_mem_of_fixedPoints _ _ (T37_37 i) (hfix37_37 i) _)
      ⟨37, by decide⟩ ⟨37, by decide⟩ _
      (Q2.validAt ⟨37, by decide⟩ (Q2.listedAt ⟨37, by decide⟩
        (alnCheck_rep ⟨37, by decide⟩ hj hq).1))
      (colE2 ⟨37, by decide⟩ 10 hp) Q2.T37_37_2 Q2.hfix37_37_2 Q2.hinj37_37_2
      Q2.hcardT37_37_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T37_37_2 i) (Q2.hfix37_37_2 i) _)
      ?_).symm
  rw [show colData1 (⟨37, by decide⟩ : Fin 148)
        ((colE1 ⟨37, by decide⟩ 10 (transLenTr ⟨37, by decide⟩ 10 hp) : ↥(reps ⟨37, by decide⟩)) : Coordinate 1)
        T37_37 = colFn colCert_37_37_10.D (m := 25) from colCert_37_37_10.bind1,
    show colData2 (⟨37, by decide⟩ : Fin 148)
        ((colE2 ⟨37, by decide⟩ 10 hp : ↥(Q2.reps ⟨37, by decide⟩)) : Coordinate 2)
        Q2.T37_37_2 = colFn colCert_37_37_10.D (m := 25) from colCert_37_37_10.bind2]
  exact alnAll_37_37_10 j hj hq

theorem leaf_37_37_15 (hp : 15 < (Q2.transData.getD 37 []).length)
    (j : Nat) (hj : j < (repChars.getD 37 []).length)
    (hq : (normIsRep.getD 37 []).getD j false = true) :
    species (Q2.reps (⟨37, by decide⟩ : Fin 148)) (colE2 ⟨37, by decide⟩ 15 hp)
        (rowE2 (⟨37, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨37, by decide⟩ : Fin 148))
        (colE1 ⟨37, by decide⟩ 15 (transLenTr ⟨37, by decide⟩ 15 hp))
        (rowE1 (⟨37, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨37, by decide⟩ : Fin 148) ⟨37, by decide⟩ _
      (validAt ⟨37, by decide⟩ (listedAt ⟨37, by decide⟩ hj))
      (colE1 ⟨37, by decide⟩ 15 (transLenTr ⟨37, by decide⟩ 15 hp)) T37_37
      hfix37_37 hinj37_37 hcardT37_37
      (fun i => conj_mem_of_fixedPoints _ _ (T37_37 i) (hfix37_37 i) _)
      ⟨37, by decide⟩ ⟨37, by decide⟩ _
      (Q2.validAt ⟨37, by decide⟩ (Q2.listedAt ⟨37, by decide⟩
        (alnCheck_rep ⟨37, by decide⟩ hj hq).1))
      (colE2 ⟨37, by decide⟩ 15 hp) Q2.T37_37_2 Q2.hfix37_37_2 Q2.hinj37_37_2
      Q2.hcardT37_37_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T37_37_2 i) (Q2.hfix37_37_2 i) _)
      ?_).symm
  rw [show colData1 (⟨37, by decide⟩ : Fin 148)
        ((colE1 ⟨37, by decide⟩ 15 (transLenTr ⟨37, by decide⟩ 15 hp) : ↥(reps ⟨37, by decide⟩)) : Coordinate 1)
        T37_37 = colFn colCert_37_37_15.D (m := 25) from colCert_37_37_15.bind1,
    show colData2 (⟨37, by decide⟩ : Fin 148)
        ((colE2 ⟨37, by decide⟩ 15 hp : ↥(Q2.reps ⟨37, by decide⟩)) : Coordinate 2)
        Q2.T37_37_2 = colFn colCert_37_37_15.D (m := 25) from colCert_37_37_15.bind2]
  exact alnAll_37_37_15 j hj hq

theorem leaf_37_37_20 (hp : 20 < (Q2.transData.getD 37 []).length)
    (j : Nat) (hj : j < (repChars.getD 37 []).length)
    (hq : (normIsRep.getD 37 []).getD j false = true) :
    species (Q2.reps (⟨37, by decide⟩ : Fin 148)) (colE2 ⟨37, by decide⟩ 20 hp)
        (rowE2 (⟨37, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨37, by decide⟩ : Fin 148))
        (colE1 ⟨37, by decide⟩ 20 (transLenTr ⟨37, by decide⟩ 20 hp))
        (rowE1 (⟨37, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨37, by decide⟩ : Fin 148) ⟨37, by decide⟩ _
      (validAt ⟨37, by decide⟩ (listedAt ⟨37, by decide⟩ hj))
      (colE1 ⟨37, by decide⟩ 20 (transLenTr ⟨37, by decide⟩ 20 hp)) T37_37
      hfix37_37 hinj37_37 hcardT37_37
      (fun i => conj_mem_of_fixedPoints _ _ (T37_37 i) (hfix37_37 i) _)
      ⟨37, by decide⟩ ⟨37, by decide⟩ _
      (Q2.validAt ⟨37, by decide⟩ (Q2.listedAt ⟨37, by decide⟩
        (alnCheck_rep ⟨37, by decide⟩ hj hq).1))
      (colE2 ⟨37, by decide⟩ 20 hp) Q2.T37_37_2 Q2.hfix37_37_2 Q2.hinj37_37_2
      Q2.hcardT37_37_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T37_37_2 i) (Q2.hfix37_37_2 i) _)
      ?_).symm
  rw [show colData1 (⟨37, by decide⟩ : Fin 148)
        ((colE1 ⟨37, by decide⟩ 20 (transLenTr ⟨37, by decide⟩ 20 hp) : ↥(reps ⟨37, by decide⟩)) : Coordinate 1)
        T37_37 = colFn colCert_37_37_20.D (m := 25) from colCert_37_37_20.bind1,
    show colData2 (⟨37, by decide⟩ : Fin 148)
        ((colE2 ⟨37, by decide⟩ 20 hp : ↥(Q2.reps ⟨37, by decide⟩)) : Coordinate 2)
        Q2.T37_37_2 = colFn colCert_37_37_20.D (m := 25) from colCert_37_37_20.bind2]
  exact alnAll_37_37_20 j hj hq

theorem leaf_38_12_0 (hp : 0 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 38 []).length)
    (hq : (normIsRep.getD 38 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 0 hp)
        (rowE2 (⟨38, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp))
        (rowE1 (⟨38, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨38, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨38, by decide⟩ (listedAt ⟨38, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp)) T38_12
      hfix38_12 hinj38_12 hcardT38_12
      (fun i => conj_mem_of_fixedPoints _ _ (T38_12 i) (hfix38_12 i) _)
      ⟨38, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨38, by decide⟩ (Q2.listedAt ⟨38, by decide⟩
        (alnCheck_rep ⟨38, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 0 hp) Q2.T38_12_2 Q2.hfix38_12_2 Q2.hinj38_12_2
      Q2.hcardT38_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T38_12_2 i) (Q2.hfix38_12_2 i) _)
      ?_).symm
  rw [show colData1 (⟨38, by decide⟩ : Fin 148)
        ((colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp) : ↥(reps ⟨12, by decide⟩)) : Coordinate 1)
        T38_12 = colFn colCert_38_12_0.D (m := 125) from colCert_38_12_0.bind1,
    show colData2 (⟨38, by decide⟩ : Fin 148)
        ((colE2 ⟨12, by decide⟩ 0 hp : ↥(Q2.reps ⟨12, by decide⟩)) : Coordinate 2)
        Q2.T38_12_2 = colFn colCert_38_12_0.D (m := 125) from colCert_38_12_0.bind2]
  exact alnAll_38_12_0 j hj hq

theorem leaf_38_12_1 (hp : 1 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 38 []).length)
    (hq : (normIsRep.getD 38 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 1 hp)
        (rowE2 (⟨38, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp))
        (rowE1 (⟨38, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨38, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨38, by decide⟩ (listedAt ⟨38, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp)) T38_12
      hfix38_12 hinj38_12 hcardT38_12
      (fun i => conj_mem_of_fixedPoints _ _ (T38_12 i) (hfix38_12 i) _)
      ⟨38, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨38, by decide⟩ (Q2.listedAt ⟨38, by decide⟩
        (alnCheck_rep ⟨38, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 1 hp) Q2.T38_12_2 Q2.hfix38_12_2 Q2.hinj38_12_2
      Q2.hcardT38_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T38_12_2 i) (Q2.hfix38_12_2 i) _)
      ?_).symm
  rw [show colData1 (⟨38, by decide⟩ : Fin 148)
        ((colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp) : ↥(reps ⟨12, by decide⟩)) : Coordinate 1)
        T38_12 = colFn colCert_38_12_1.D (m := 125) from colCert_38_12_1.bind1,
    show colData2 (⟨38, by decide⟩ : Fin 148)
        ((colE2 ⟨12, by decide⟩ 1 hp : ↥(Q2.reps ⟨12, by decide⟩)) : Coordinate 2)
        Q2.T38_12_2 = colFn colCert_38_12_1.D (m := 125) from colCert_38_12_1.bind2]
  exact alnAll_38_12_1 j hj hq

theorem leaf_38_12_2 (hp : 2 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 38 []).length)
    (hq : (normIsRep.getD 38 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 2 hp)
        (rowE2 (⟨38, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp))
        (rowE1 (⟨38, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨38, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨38, by decide⟩ (listedAt ⟨38, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp)) T38_12
      hfix38_12 hinj38_12 hcardT38_12
      (fun i => conj_mem_of_fixedPoints _ _ (T38_12 i) (hfix38_12 i) _)
      ⟨38, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨38, by decide⟩ (Q2.listedAt ⟨38, by decide⟩
        (alnCheck_rep ⟨38, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 2 hp) Q2.T38_12_2 Q2.hfix38_12_2 Q2.hinj38_12_2
      Q2.hcardT38_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T38_12_2 i) (Q2.hfix38_12_2 i) _)
      ?_).symm
  rw [show colData1 (⟨38, by decide⟩ : Fin 148)
        ((colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp) : ↥(reps ⟨12, by decide⟩)) : Coordinate 1)
        T38_12 = colFn colCert_38_12_2.D (m := 125) from colCert_38_12_2.bind1,
    show colData2 (⟨38, by decide⟩ : Fin 148)
        ((colE2 ⟨12, by decide⟩ 2 hp : ↥(Q2.reps ⟨12, by decide⟩)) : Coordinate 2)
        Q2.T38_12_2 = colFn colCert_38_12_2.D (m := 125) from colCert_38_12_2.bind2]
  exact alnAll_38_12_2 j hj hq

theorem leaf_38_12_3 (hp : 3 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 38 []).length)
    (hq : (normIsRep.getD 38 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 3 hp)
        (rowE2 (⟨38, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp))
        (rowE1 (⟨38, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨38, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨38, by decide⟩ (listedAt ⟨38, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp)) T38_12
      hfix38_12 hinj38_12 hcardT38_12
      (fun i => conj_mem_of_fixedPoints _ _ (T38_12 i) (hfix38_12 i) _)
      ⟨38, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨38, by decide⟩ (Q2.listedAt ⟨38, by decide⟩
        (alnCheck_rep ⟨38, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 3 hp) Q2.T38_12_2 Q2.hfix38_12_2 Q2.hinj38_12_2
      Q2.hcardT38_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T38_12_2 i) (Q2.hfix38_12_2 i) _)
      ?_).symm
  rw [show colData1 (⟨38, by decide⟩ : Fin 148)
        ((colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp) : ↥(reps ⟨12, by decide⟩)) : Coordinate 1)
        T38_12 = colFn colCert_38_12_3.D (m := 125) from colCert_38_12_3.bind1,
    show colData2 (⟨38, by decide⟩ : Fin 148)
        ((colE2 ⟨12, by decide⟩ 3 hp : ↥(Q2.reps ⟨12, by decide⟩)) : Coordinate 2)
        Q2.T38_12_2 = colFn colCert_38_12_3.D (m := 125) from colCert_38_12_3.bind2]
  exact alnAll_38_12_3 j hj hq

theorem leaf_38_12_4 (hp : 4 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 38 []).length)
    (hq : (normIsRep.getD 38 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 4 hp)
        (rowE2 (⟨38, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp))
        (rowE1 (⟨38, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨38, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨38, by decide⟩ (listedAt ⟨38, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp)) T38_12
      hfix38_12 hinj38_12 hcardT38_12
      (fun i => conj_mem_of_fixedPoints _ _ (T38_12 i) (hfix38_12 i) _)
      ⟨38, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨38, by decide⟩ (Q2.listedAt ⟨38, by decide⟩
        (alnCheck_rep ⟨38, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 4 hp) Q2.T38_12_2 Q2.hfix38_12_2 Q2.hinj38_12_2
      Q2.hcardT38_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T38_12_2 i) (Q2.hfix38_12_2 i) _)
      ?_).symm
  rw [show colData1 (⟨38, by decide⟩ : Fin 148)
        ((colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp) : ↥(reps ⟨12, by decide⟩)) : Coordinate 1)
        T38_12 = colFn colCert_38_12_4.D (m := 125) from colCert_38_12_4.bind1,
    show colData2 (⟨38, by decide⟩ : Fin 148)
        ((colE2 ⟨12, by decide⟩ 4 hp : ↥(Q2.reps ⟨12, by decide⟩)) : Coordinate 2)
        Q2.T38_12_2 = colFn colCert_38_12_4.D (m := 125) from colCert_38_12_4.bind2]
  exact alnAll_38_12_4 j hj hq

theorem leaf_38_38_0 (hp : 0 < (Q2.transData.getD 38 []).length)
    (j : Nat) (hj : j < (repChars.getD 38 []).length)
    (hq : (normIsRep.getD 38 []).getD j false = true) :
    species (Q2.reps (⟨38, by decide⟩ : Fin 148)) (colE2 ⟨38, by decide⟩ 0 hp)
        (rowE2 (⟨38, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨38, by decide⟩ : Fin 148))
        (colE1 ⟨38, by decide⟩ 0 (transLenTr ⟨38, by decide⟩ 0 hp))
        (rowE1 (⟨38, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨38, by decide⟩ : Fin 148) ⟨38, by decide⟩ _
      (validAt ⟨38, by decide⟩ (listedAt ⟨38, by decide⟩ hj))
      (colE1 ⟨38, by decide⟩ 0 (transLenTr ⟨38, by decide⟩ 0 hp)) T38_38
      hfix38_38 hinj38_38 hcardT38_38
      (fun i => conj_mem_of_fixedPoints _ _ (T38_38 i) (hfix38_38 i) _)
      ⟨38, by decide⟩ ⟨38, by decide⟩ _
      (Q2.validAt ⟨38, by decide⟩ (Q2.listedAt ⟨38, by decide⟩
        (alnCheck_rep ⟨38, by decide⟩ hj hq).1))
      (colE2 ⟨38, by decide⟩ 0 hp) Q2.T38_38_2 Q2.hfix38_38_2 Q2.hinj38_38_2
      Q2.hcardT38_38_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T38_38_2 i) (Q2.hfix38_38_2 i) _)
      ?_).symm
  rw [show colData1 (⟨38, by decide⟩ : Fin 148)
        ((colE1 ⟨38, by decide⟩ 0 (transLenTr ⟨38, by decide⟩ 0 hp) : ↥(reps ⟨38, by decide⟩)) : Coordinate 1)
        T38_38 = colFn colCert_38_38_0.D (m := 25) from colCert_38_38_0.bind1,
    show colData2 (⟨38, by decide⟩ : Fin 148)
        ((colE2 ⟨38, by decide⟩ 0 hp : ↥(Q2.reps ⟨38, by decide⟩)) : Coordinate 2)
        Q2.T38_38_2 = colFn colCert_38_38_0.D (m := 25) from colCert_38_38_0.bind2]
  exact alnAll_38_38_0 j hj hq

theorem leaf_38_38_1 (hp : 1 < (Q2.transData.getD 38 []).length)
    (j : Nat) (hj : j < (repChars.getD 38 []).length)
    (hq : (normIsRep.getD 38 []).getD j false = true) :
    species (Q2.reps (⟨38, by decide⟩ : Fin 148)) (colE2 ⟨38, by decide⟩ 1 hp)
        (rowE2 (⟨38, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨38, by decide⟩ : Fin 148))
        (colE1 ⟨38, by decide⟩ 1 (transLenTr ⟨38, by decide⟩ 1 hp))
        (rowE1 (⟨38, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨38, by decide⟩ : Fin 148) ⟨38, by decide⟩ _
      (validAt ⟨38, by decide⟩ (listedAt ⟨38, by decide⟩ hj))
      (colE1 ⟨38, by decide⟩ 1 (transLenTr ⟨38, by decide⟩ 1 hp)) T38_38
      hfix38_38 hinj38_38 hcardT38_38
      (fun i => conj_mem_of_fixedPoints _ _ (T38_38 i) (hfix38_38 i) _)
      ⟨38, by decide⟩ ⟨38, by decide⟩ _
      (Q2.validAt ⟨38, by decide⟩ (Q2.listedAt ⟨38, by decide⟩
        (alnCheck_rep ⟨38, by decide⟩ hj hq).1))
      (colE2 ⟨38, by decide⟩ 1 hp) Q2.T38_38_2 Q2.hfix38_38_2 Q2.hinj38_38_2
      Q2.hcardT38_38_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T38_38_2 i) (Q2.hfix38_38_2 i) _)
      ?_).symm
  rw [show colData1 (⟨38, by decide⟩ : Fin 148)
        ((colE1 ⟨38, by decide⟩ 1 (transLenTr ⟨38, by decide⟩ 1 hp) : ↥(reps ⟨38, by decide⟩)) : Coordinate 1)
        T38_38 = colFn colCert_38_38_1.D (m := 25) from colCert_38_38_1.bind1,
    show colData2 (⟨38, by decide⟩ : Fin 148)
        ((colE2 ⟨38, by decide⟩ 1 hp : ↥(Q2.reps ⟨38, by decide⟩)) : Coordinate 2)
        Q2.T38_38_2 = colFn colCert_38_38_1.D (m := 25) from colCert_38_38_1.bind2]
  exact alnAll_38_38_1 j hj hq

theorem leaf_38_38_2 (hp : 2 < (Q2.transData.getD 38 []).length)
    (j : Nat) (hj : j < (repChars.getD 38 []).length)
    (hq : (normIsRep.getD 38 []).getD j false = true) :
    species (Q2.reps (⟨38, by decide⟩ : Fin 148)) (colE2 ⟨38, by decide⟩ 2 hp)
        (rowE2 (⟨38, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨38, by decide⟩ : Fin 148))
        (colE1 ⟨38, by decide⟩ 2 (transLenTr ⟨38, by decide⟩ 2 hp))
        (rowE1 (⟨38, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨38, by decide⟩ : Fin 148) ⟨38, by decide⟩ _
      (validAt ⟨38, by decide⟩ (listedAt ⟨38, by decide⟩ hj))
      (colE1 ⟨38, by decide⟩ 2 (transLenTr ⟨38, by decide⟩ 2 hp)) T38_38
      hfix38_38 hinj38_38 hcardT38_38
      (fun i => conj_mem_of_fixedPoints _ _ (T38_38 i) (hfix38_38 i) _)
      ⟨38, by decide⟩ ⟨38, by decide⟩ _
      (Q2.validAt ⟨38, by decide⟩ (Q2.listedAt ⟨38, by decide⟩
        (alnCheck_rep ⟨38, by decide⟩ hj hq).1))
      (colE2 ⟨38, by decide⟩ 2 hp) Q2.T38_38_2 Q2.hfix38_38_2 Q2.hinj38_38_2
      Q2.hcardT38_38_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T38_38_2 i) (Q2.hfix38_38_2 i) _)
      ?_).symm
  rw [show colData1 (⟨38, by decide⟩ : Fin 148)
        ((colE1 ⟨38, by decide⟩ 2 (transLenTr ⟨38, by decide⟩ 2 hp) : ↥(reps ⟨38, by decide⟩)) : Coordinate 1)
        T38_38 = colFn colCert_38_38_2.D (m := 25) from colCert_38_38_2.bind1,
    show colData2 (⟨38, by decide⟩ : Fin 148)
        ((colE2 ⟨38, by decide⟩ 2 hp : ↥(Q2.reps ⟨38, by decide⟩)) : Coordinate 2)
        Q2.T38_38_2 = colFn colCert_38_38_2.D (m := 25) from colCert_38_38_2.bind2]
  exact alnAll_38_38_2 j hj hq

theorem leaf_38_38_3 (hp : 3 < (Q2.transData.getD 38 []).length)
    (j : Nat) (hj : j < (repChars.getD 38 []).length)
    (hq : (normIsRep.getD 38 []).getD j false = true) :
    species (Q2.reps (⟨38, by decide⟩ : Fin 148)) (colE2 ⟨38, by decide⟩ 3 hp)
        (rowE2 (⟨38, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨38, by decide⟩ : Fin 148))
        (colE1 ⟨38, by decide⟩ 3 (transLenTr ⟨38, by decide⟩ 3 hp))
        (rowE1 (⟨38, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨38, by decide⟩ : Fin 148) ⟨38, by decide⟩ _
      (validAt ⟨38, by decide⟩ (listedAt ⟨38, by decide⟩ hj))
      (colE1 ⟨38, by decide⟩ 3 (transLenTr ⟨38, by decide⟩ 3 hp)) T38_38
      hfix38_38 hinj38_38 hcardT38_38
      (fun i => conj_mem_of_fixedPoints _ _ (T38_38 i) (hfix38_38 i) _)
      ⟨38, by decide⟩ ⟨38, by decide⟩ _
      (Q2.validAt ⟨38, by decide⟩ (Q2.listedAt ⟨38, by decide⟩
        (alnCheck_rep ⟨38, by decide⟩ hj hq).1))
      (colE2 ⟨38, by decide⟩ 3 hp) Q2.T38_38_2 Q2.hfix38_38_2 Q2.hinj38_38_2
      Q2.hcardT38_38_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T38_38_2 i) (Q2.hfix38_38_2 i) _)
      ?_).symm
  rw [show colData1 (⟨38, by decide⟩ : Fin 148)
        ((colE1 ⟨38, by decide⟩ 3 (transLenTr ⟨38, by decide⟩ 3 hp) : ↥(reps ⟨38, by decide⟩)) : Coordinate 1)
        T38_38 = colFn colCert_38_38_3.D (m := 25) from colCert_38_38_3.bind1,
    show colData2 (⟨38, by decide⟩ : Fin 148)
        ((colE2 ⟨38, by decide⟩ 3 hp : ↥(Q2.reps ⟨38, by decide⟩)) : Coordinate 2)
        Q2.T38_38_2 = colFn colCert_38_38_3.D (m := 25) from colCert_38_38_3.bind2]
  exact alnAll_38_38_3 j hj hq

theorem leaf_38_38_4 (hp : 4 < (Q2.transData.getD 38 []).length)
    (j : Nat) (hj : j < (repChars.getD 38 []).length)
    (hq : (normIsRep.getD 38 []).getD j false = true) :
    species (Q2.reps (⟨38, by decide⟩ : Fin 148)) (colE2 ⟨38, by decide⟩ 4 hp)
        (rowE2 (⟨38, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨38, by decide⟩ : Fin 148))
        (colE1 ⟨38, by decide⟩ 4 (transLenTr ⟨38, by decide⟩ 4 hp))
        (rowE1 (⟨38, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨38, by decide⟩ : Fin 148) ⟨38, by decide⟩ _
      (validAt ⟨38, by decide⟩ (listedAt ⟨38, by decide⟩ hj))
      (colE1 ⟨38, by decide⟩ 4 (transLenTr ⟨38, by decide⟩ 4 hp)) T38_38
      hfix38_38 hinj38_38 hcardT38_38
      (fun i => conj_mem_of_fixedPoints _ _ (T38_38 i) (hfix38_38 i) _)
      ⟨38, by decide⟩ ⟨38, by decide⟩ _
      (Q2.validAt ⟨38, by decide⟩ (Q2.listedAt ⟨38, by decide⟩
        (alnCheck_rep ⟨38, by decide⟩ hj hq).1))
      (colE2 ⟨38, by decide⟩ 4 hp) Q2.T38_38_2 Q2.hfix38_38_2 Q2.hinj38_38_2
      Q2.hcardT38_38_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T38_38_2 i) (Q2.hfix38_38_2 i) _)
      ?_).symm
  rw [show colData1 (⟨38, by decide⟩ : Fin 148)
        ((colE1 ⟨38, by decide⟩ 4 (transLenTr ⟨38, by decide⟩ 4 hp) : ↥(reps ⟨38, by decide⟩)) : Coordinate 1)
        T38_38 = colFn colCert_38_38_4.D (m := 25) from colCert_38_38_4.bind1,
    show colData2 (⟨38, by decide⟩ : Fin 148)
        ((colE2 ⟨38, by decide⟩ 4 hp : ↥(Q2.reps ⟨38, by decide⟩)) : Coordinate 2)
        Q2.T38_38_2 = colFn colCert_38_38_4.D (m := 25) from colCert_38_38_4.bind2]
  exact alnAll_38_38_4 j hj hq

theorem leaf_38_38_5 (hp : 5 < (Q2.transData.getD 38 []).length)
    (j : Nat) (hj : j < (repChars.getD 38 []).length)
    (hq : (normIsRep.getD 38 []).getD j false = true) :
    species (Q2.reps (⟨38, by decide⟩ : Fin 148)) (colE2 ⟨38, by decide⟩ 5 hp)
        (rowE2 (⟨38, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨38, by decide⟩ : Fin 148))
        (colE1 ⟨38, by decide⟩ 5 (transLenTr ⟨38, by decide⟩ 5 hp))
        (rowE1 (⟨38, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨38, by decide⟩ : Fin 148) ⟨38, by decide⟩ _
      (validAt ⟨38, by decide⟩ (listedAt ⟨38, by decide⟩ hj))
      (colE1 ⟨38, by decide⟩ 5 (transLenTr ⟨38, by decide⟩ 5 hp)) T38_38
      hfix38_38 hinj38_38 hcardT38_38
      (fun i => conj_mem_of_fixedPoints _ _ (T38_38 i) (hfix38_38 i) _)
      ⟨38, by decide⟩ ⟨38, by decide⟩ _
      (Q2.validAt ⟨38, by decide⟩ (Q2.listedAt ⟨38, by decide⟩
        (alnCheck_rep ⟨38, by decide⟩ hj hq).1))
      (colE2 ⟨38, by decide⟩ 5 hp) Q2.T38_38_2 Q2.hfix38_38_2 Q2.hinj38_38_2
      Q2.hcardT38_38_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T38_38_2 i) (Q2.hfix38_38_2 i) _)
      ?_).symm
  rw [show colData1 (⟨38, by decide⟩ : Fin 148)
        ((colE1 ⟨38, by decide⟩ 5 (transLenTr ⟨38, by decide⟩ 5 hp) : ↥(reps ⟨38, by decide⟩)) : Coordinate 1)
        T38_38 = colFn colCert_38_38_5.D (m := 25) from colCert_38_38_5.bind1,
    show colData2 (⟨38, by decide⟩ : Fin 148)
        ((colE2 ⟨38, by decide⟩ 5 hp : ↥(Q2.reps ⟨38, by decide⟩)) : Coordinate 2)
        Q2.T38_38_2 = colFn colCert_38_38_5.D (m := 25) from colCert_38_38_5.bind2]
  exact alnAll_38_38_5 j hj hq

theorem leaf_38_38_10 (hp : 10 < (Q2.transData.getD 38 []).length)
    (j : Nat) (hj : j < (repChars.getD 38 []).length)
    (hq : (normIsRep.getD 38 []).getD j false = true) :
    species (Q2.reps (⟨38, by decide⟩ : Fin 148)) (colE2 ⟨38, by decide⟩ 10 hp)
        (rowE2 (⟨38, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨38, by decide⟩ : Fin 148))
        (colE1 ⟨38, by decide⟩ 10 (transLenTr ⟨38, by decide⟩ 10 hp))
        (rowE1 (⟨38, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨38, by decide⟩ : Fin 148) ⟨38, by decide⟩ _
      (validAt ⟨38, by decide⟩ (listedAt ⟨38, by decide⟩ hj))
      (colE1 ⟨38, by decide⟩ 10 (transLenTr ⟨38, by decide⟩ 10 hp)) T38_38
      hfix38_38 hinj38_38 hcardT38_38
      (fun i => conj_mem_of_fixedPoints _ _ (T38_38 i) (hfix38_38 i) _)
      ⟨38, by decide⟩ ⟨38, by decide⟩ _
      (Q2.validAt ⟨38, by decide⟩ (Q2.listedAt ⟨38, by decide⟩
        (alnCheck_rep ⟨38, by decide⟩ hj hq).1))
      (colE2 ⟨38, by decide⟩ 10 hp) Q2.T38_38_2 Q2.hfix38_38_2 Q2.hinj38_38_2
      Q2.hcardT38_38_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T38_38_2 i) (Q2.hfix38_38_2 i) _)
      ?_).symm
  rw [show colData1 (⟨38, by decide⟩ : Fin 148)
        ((colE1 ⟨38, by decide⟩ 10 (transLenTr ⟨38, by decide⟩ 10 hp) : ↥(reps ⟨38, by decide⟩)) : Coordinate 1)
        T38_38 = colFn colCert_38_38_10.D (m := 25) from colCert_38_38_10.bind1,
    show colData2 (⟨38, by decide⟩ : Fin 148)
        ((colE2 ⟨38, by decide⟩ 10 hp : ↥(Q2.reps ⟨38, by decide⟩)) : Coordinate 2)
        Q2.T38_38_2 = colFn colCert_38_38_10.D (m := 25) from colCert_38_38_10.bind2]
  exact alnAll_38_38_10 j hj hq

theorem leaf_38_38_15 (hp : 15 < (Q2.transData.getD 38 []).length)
    (j : Nat) (hj : j < (repChars.getD 38 []).length)
    (hq : (normIsRep.getD 38 []).getD j false = true) :
    species (Q2.reps (⟨38, by decide⟩ : Fin 148)) (colE2 ⟨38, by decide⟩ 15 hp)
        (rowE2 (⟨38, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨38, by decide⟩ : Fin 148))
        (colE1 ⟨38, by decide⟩ 15 (transLenTr ⟨38, by decide⟩ 15 hp))
        (rowE1 (⟨38, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨38, by decide⟩ : Fin 148) ⟨38, by decide⟩ _
      (validAt ⟨38, by decide⟩ (listedAt ⟨38, by decide⟩ hj))
      (colE1 ⟨38, by decide⟩ 15 (transLenTr ⟨38, by decide⟩ 15 hp)) T38_38
      hfix38_38 hinj38_38 hcardT38_38
      (fun i => conj_mem_of_fixedPoints _ _ (T38_38 i) (hfix38_38 i) _)
      ⟨38, by decide⟩ ⟨38, by decide⟩ _
      (Q2.validAt ⟨38, by decide⟩ (Q2.listedAt ⟨38, by decide⟩
        (alnCheck_rep ⟨38, by decide⟩ hj hq).1))
      (colE2 ⟨38, by decide⟩ 15 hp) Q2.T38_38_2 Q2.hfix38_38_2 Q2.hinj38_38_2
      Q2.hcardT38_38_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T38_38_2 i) (Q2.hfix38_38_2 i) _)
      ?_).symm
  rw [show colData1 (⟨38, by decide⟩ : Fin 148)
        ((colE1 ⟨38, by decide⟩ 15 (transLenTr ⟨38, by decide⟩ 15 hp) : ↥(reps ⟨38, by decide⟩)) : Coordinate 1)
        T38_38 = colFn colCert_38_38_15.D (m := 25) from colCert_38_38_15.bind1,
    show colData2 (⟨38, by decide⟩ : Fin 148)
        ((colE2 ⟨38, by decide⟩ 15 hp : ↥(Q2.reps ⟨38, by decide⟩)) : Coordinate 2)
        Q2.T38_38_2 = colFn colCert_38_38_15.D (m := 25) from colCert_38_38_15.bind2]
  exact alnAll_38_38_15 j hj hq

theorem leaf_38_38_20 (hp : 20 < (Q2.transData.getD 38 []).length)
    (j : Nat) (hj : j < (repChars.getD 38 []).length)
    (hq : (normIsRep.getD 38 []).getD j false = true) :
    species (Q2.reps (⟨38, by decide⟩ : Fin 148)) (colE2 ⟨38, by decide⟩ 20 hp)
        (rowE2 (⟨38, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨38, by decide⟩ : Fin 148))
        (colE1 ⟨38, by decide⟩ 20 (transLenTr ⟨38, by decide⟩ 20 hp))
        (rowE1 (⟨38, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨38, by decide⟩ : Fin 148) ⟨38, by decide⟩ _
      (validAt ⟨38, by decide⟩ (listedAt ⟨38, by decide⟩ hj))
      (colE1 ⟨38, by decide⟩ 20 (transLenTr ⟨38, by decide⟩ 20 hp)) T38_38
      hfix38_38 hinj38_38 hcardT38_38
      (fun i => conj_mem_of_fixedPoints _ _ (T38_38 i) (hfix38_38 i) _)
      ⟨38, by decide⟩ ⟨38, by decide⟩ _
      (Q2.validAt ⟨38, by decide⟩ (Q2.listedAt ⟨38, by decide⟩
        (alnCheck_rep ⟨38, by decide⟩ hj hq).1))
      (colE2 ⟨38, by decide⟩ 20 hp) Q2.T38_38_2 Q2.hfix38_38_2 Q2.hinj38_38_2
      Q2.hcardT38_38_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T38_38_2 i) (Q2.hfix38_38_2 i) _)
      ?_).symm
  rw [show colData1 (⟨38, by decide⟩ : Fin 148)
        ((colE1 ⟨38, by decide⟩ 20 (transLenTr ⟨38, by decide⟩ 20 hp) : ↥(reps ⟨38, by decide⟩)) : Coordinate 1)
        T38_38 = colFn colCert_38_38_20.D (m := 25) from colCert_38_38_20.bind1,
    show colData2 (⟨38, by decide⟩ : Fin 148)
        ((colE2 ⟨38, by decide⟩ 20 hp : ↥(Q2.reps ⟨38, by decide⟩)) : Coordinate 2)
        Q2.T38_38_2 = colFn colCert_38_38_20.D (m := 25) from colCert_38_38_20.bind2]
  exact alnAll_38_38_20 j hj hq

theorem leaf_39_12_0 (hp : 0 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 39 []).length)
    (hq : (normIsRep.getD 39 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 0 hp)
        (rowE2 (⟨39, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp))
        (rowE1 (⟨39, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨39, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨39, by decide⟩ (listedAt ⟨39, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp)) T39_12
      hfix39_12 hinj39_12 hcardT39_12
      (fun i => conj_mem_of_fixedPoints _ _ (T39_12 i) (hfix39_12 i) _)
      ⟨39, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨39, by decide⟩ (Q2.listedAt ⟨39, by decide⟩
        (alnCheck_rep ⟨39, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 0 hp) Q2.T39_12_2 Q2.hfix39_12_2 Q2.hinj39_12_2
      Q2.hcardT39_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T39_12_2 i) (Q2.hfix39_12_2 i) _)
      ?_).symm
  rw [show colData1 (⟨39, by decide⟩ : Fin 148)
        ((colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp) : ↥(reps ⟨12, by decide⟩)) : Coordinate 1)
        T39_12 = colFn colCert_39_12_0.D (m := 125) from colCert_39_12_0.bind1,
    show colData2 (⟨39, by decide⟩ : Fin 148)
        ((colE2 ⟨12, by decide⟩ 0 hp : ↥(Q2.reps ⟨12, by decide⟩)) : Coordinate 2)
        Q2.T39_12_2 = colFn colCert_39_12_0.D (m := 125) from colCert_39_12_0.bind2]
  exact alnAll_39_12_0 j hj hq

theorem leaf_39_12_1 (hp : 1 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 39 []).length)
    (hq : (normIsRep.getD 39 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 1 hp)
        (rowE2 (⟨39, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp))
        (rowE1 (⟨39, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨39, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨39, by decide⟩ (listedAt ⟨39, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp)) T39_12
      hfix39_12 hinj39_12 hcardT39_12
      (fun i => conj_mem_of_fixedPoints _ _ (T39_12 i) (hfix39_12 i) _)
      ⟨39, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨39, by decide⟩ (Q2.listedAt ⟨39, by decide⟩
        (alnCheck_rep ⟨39, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 1 hp) Q2.T39_12_2 Q2.hfix39_12_2 Q2.hinj39_12_2
      Q2.hcardT39_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T39_12_2 i) (Q2.hfix39_12_2 i) _)
      ?_).symm
  rw [show colData1 (⟨39, by decide⟩ : Fin 148)
        ((colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp) : ↥(reps ⟨12, by decide⟩)) : Coordinate 1)
        T39_12 = colFn colCert_39_12_1.D (m := 125) from colCert_39_12_1.bind1,
    show colData2 (⟨39, by decide⟩ : Fin 148)
        ((colE2 ⟨12, by decide⟩ 1 hp : ↥(Q2.reps ⟨12, by decide⟩)) : Coordinate 2)
        Q2.T39_12_2 = colFn colCert_39_12_1.D (m := 125) from colCert_39_12_1.bind2]
  exact alnAll_39_12_1 j hj hq

theorem leaf_39_12_2 (hp : 2 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 39 []).length)
    (hq : (normIsRep.getD 39 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 2 hp)
        (rowE2 (⟨39, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp))
        (rowE1 (⟨39, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨39, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨39, by decide⟩ (listedAt ⟨39, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp)) T39_12
      hfix39_12 hinj39_12 hcardT39_12
      (fun i => conj_mem_of_fixedPoints _ _ (T39_12 i) (hfix39_12 i) _)
      ⟨39, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨39, by decide⟩ (Q2.listedAt ⟨39, by decide⟩
        (alnCheck_rep ⟨39, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 2 hp) Q2.T39_12_2 Q2.hfix39_12_2 Q2.hinj39_12_2
      Q2.hcardT39_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T39_12_2 i) (Q2.hfix39_12_2 i) _)
      ?_).symm
  rw [show colData1 (⟨39, by decide⟩ : Fin 148)
        ((colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp) : ↥(reps ⟨12, by decide⟩)) : Coordinate 1)
        T39_12 = colFn colCert_39_12_2.D (m := 125) from colCert_39_12_2.bind1,
    show colData2 (⟨39, by decide⟩ : Fin 148)
        ((colE2 ⟨12, by decide⟩ 2 hp : ↥(Q2.reps ⟨12, by decide⟩)) : Coordinate 2)
        Q2.T39_12_2 = colFn colCert_39_12_2.D (m := 125) from colCert_39_12_2.bind2]
  exact alnAll_39_12_2 j hj hq

theorem leaf_39_12_3 (hp : 3 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 39 []).length)
    (hq : (normIsRep.getD 39 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 3 hp)
        (rowE2 (⟨39, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp))
        (rowE1 (⟨39, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨39, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨39, by decide⟩ (listedAt ⟨39, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp)) T39_12
      hfix39_12 hinj39_12 hcardT39_12
      (fun i => conj_mem_of_fixedPoints _ _ (T39_12 i) (hfix39_12 i) _)
      ⟨39, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨39, by decide⟩ (Q2.listedAt ⟨39, by decide⟩
        (alnCheck_rep ⟨39, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 3 hp) Q2.T39_12_2 Q2.hfix39_12_2 Q2.hinj39_12_2
      Q2.hcardT39_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T39_12_2 i) (Q2.hfix39_12_2 i) _)
      ?_).symm
  rw [show colData1 (⟨39, by decide⟩ : Fin 148)
        ((colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp) : ↥(reps ⟨12, by decide⟩)) : Coordinate 1)
        T39_12 = colFn colCert_39_12_3.D (m := 125) from colCert_39_12_3.bind1,
    show colData2 (⟨39, by decide⟩ : Fin 148)
        ((colE2 ⟨12, by decide⟩ 3 hp : ↥(Q2.reps ⟨12, by decide⟩)) : Coordinate 2)
        Q2.T39_12_2 = colFn colCert_39_12_3.D (m := 125) from colCert_39_12_3.bind2]
  exact alnAll_39_12_3 j hj hq

theorem leaf_39_12_4 (hp : 4 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 39 []).length)
    (hq : (normIsRep.getD 39 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 4 hp)
        (rowE2 (⟨39, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp))
        (rowE1 (⟨39, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨39, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨39, by decide⟩ (listedAt ⟨39, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp)) T39_12
      hfix39_12 hinj39_12 hcardT39_12
      (fun i => conj_mem_of_fixedPoints _ _ (T39_12 i) (hfix39_12 i) _)
      ⟨39, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨39, by decide⟩ (Q2.listedAt ⟨39, by decide⟩
        (alnCheck_rep ⟨39, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 4 hp) Q2.T39_12_2 Q2.hfix39_12_2 Q2.hinj39_12_2
      Q2.hcardT39_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T39_12_2 i) (Q2.hfix39_12_2 i) _)
      ?_).symm
  rw [show colData1 (⟨39, by decide⟩ : Fin 148)
        ((colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp) : ↥(reps ⟨12, by decide⟩)) : Coordinate 1)
        T39_12 = colFn colCert_39_12_4.D (m := 125) from colCert_39_12_4.bind1,
    show colData2 (⟨39, by decide⟩ : Fin 148)
        ((colE2 ⟨12, by decide⟩ 4 hp : ↥(Q2.reps ⟨12, by decide⟩)) : Coordinate 2)
        Q2.T39_12_2 = colFn colCert_39_12_4.D (m := 125) from colCert_39_12_4.bind2]
  exact alnAll_39_12_4 j hj hq

theorem leaf_39_39_0 (hp : 0 < (Q2.transData.getD 39 []).length)
    (j : Nat) (hj : j < (repChars.getD 39 []).length)
    (hq : (normIsRep.getD 39 []).getD j false = true) :
    species (Q2.reps (⟨39, by decide⟩ : Fin 148)) (colE2 ⟨39, by decide⟩ 0 hp)
        (rowE2 (⟨39, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨39, by decide⟩ : Fin 148))
        (colE1 ⟨39, by decide⟩ 0 (transLenTr ⟨39, by decide⟩ 0 hp))
        (rowE1 (⟨39, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨39, by decide⟩ : Fin 148) ⟨39, by decide⟩ _
      (validAt ⟨39, by decide⟩ (listedAt ⟨39, by decide⟩ hj))
      (colE1 ⟨39, by decide⟩ 0 (transLenTr ⟨39, by decide⟩ 0 hp)) T39_39
      hfix39_39 hinj39_39 hcardT39_39
      (fun i => conj_mem_of_fixedPoints _ _ (T39_39 i) (hfix39_39 i) _)
      ⟨39, by decide⟩ ⟨39, by decide⟩ _
      (Q2.validAt ⟨39, by decide⟩ (Q2.listedAt ⟨39, by decide⟩
        (alnCheck_rep ⟨39, by decide⟩ hj hq).1))
      (colE2 ⟨39, by decide⟩ 0 hp) Q2.T39_39_2 Q2.hfix39_39_2 Q2.hinj39_39_2
      Q2.hcardT39_39_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T39_39_2 i) (Q2.hfix39_39_2 i) _)
      ?_).symm
  rw [show colData1 (⟨39, by decide⟩ : Fin 148)
        ((colE1 ⟨39, by decide⟩ 0 (transLenTr ⟨39, by decide⟩ 0 hp) : ↥(reps ⟨39, by decide⟩)) : Coordinate 1)
        T39_39 = colFn colCert_39_39_0.D (m := 25) from colCert_39_39_0.bind1,
    show colData2 (⟨39, by decide⟩ : Fin 148)
        ((colE2 ⟨39, by decide⟩ 0 hp : ↥(Q2.reps ⟨39, by decide⟩)) : Coordinate 2)
        Q2.T39_39_2 = colFn colCert_39_39_0.D (m := 25) from colCert_39_39_0.bind2]
  exact alnAll_39_39_0 j hj hq

theorem leaf_39_39_1 (hp : 1 < (Q2.transData.getD 39 []).length)
    (j : Nat) (hj : j < (repChars.getD 39 []).length)
    (hq : (normIsRep.getD 39 []).getD j false = true) :
    species (Q2.reps (⟨39, by decide⟩ : Fin 148)) (colE2 ⟨39, by decide⟩ 1 hp)
        (rowE2 (⟨39, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨39, by decide⟩ : Fin 148))
        (colE1 ⟨39, by decide⟩ 1 (transLenTr ⟨39, by decide⟩ 1 hp))
        (rowE1 (⟨39, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨39, by decide⟩ : Fin 148) ⟨39, by decide⟩ _
      (validAt ⟨39, by decide⟩ (listedAt ⟨39, by decide⟩ hj))
      (colE1 ⟨39, by decide⟩ 1 (transLenTr ⟨39, by decide⟩ 1 hp)) T39_39
      hfix39_39 hinj39_39 hcardT39_39
      (fun i => conj_mem_of_fixedPoints _ _ (T39_39 i) (hfix39_39 i) _)
      ⟨39, by decide⟩ ⟨39, by decide⟩ _
      (Q2.validAt ⟨39, by decide⟩ (Q2.listedAt ⟨39, by decide⟩
        (alnCheck_rep ⟨39, by decide⟩ hj hq).1))
      (colE2 ⟨39, by decide⟩ 1 hp) Q2.T39_39_2 Q2.hfix39_39_2 Q2.hinj39_39_2
      Q2.hcardT39_39_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T39_39_2 i) (Q2.hfix39_39_2 i) _)
      ?_).symm
  rw [show colData1 (⟨39, by decide⟩ : Fin 148)
        ((colE1 ⟨39, by decide⟩ 1 (transLenTr ⟨39, by decide⟩ 1 hp) : ↥(reps ⟨39, by decide⟩)) : Coordinate 1)
        T39_39 = colFn colCert_39_39_1.D (m := 25) from colCert_39_39_1.bind1,
    show colData2 (⟨39, by decide⟩ : Fin 148)
        ((colE2 ⟨39, by decide⟩ 1 hp : ↥(Q2.reps ⟨39, by decide⟩)) : Coordinate 2)
        Q2.T39_39_2 = colFn colCert_39_39_1.D (m := 25) from colCert_39_39_1.bind2]
  exact alnAll_39_39_1 j hj hq

theorem leaf_39_39_2 (hp : 2 < (Q2.transData.getD 39 []).length)
    (j : Nat) (hj : j < (repChars.getD 39 []).length)
    (hq : (normIsRep.getD 39 []).getD j false = true) :
    species (Q2.reps (⟨39, by decide⟩ : Fin 148)) (colE2 ⟨39, by decide⟩ 2 hp)
        (rowE2 (⟨39, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨39, by decide⟩ : Fin 148))
        (colE1 ⟨39, by decide⟩ 2 (transLenTr ⟨39, by decide⟩ 2 hp))
        (rowE1 (⟨39, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨39, by decide⟩ : Fin 148) ⟨39, by decide⟩ _
      (validAt ⟨39, by decide⟩ (listedAt ⟨39, by decide⟩ hj))
      (colE1 ⟨39, by decide⟩ 2 (transLenTr ⟨39, by decide⟩ 2 hp)) T39_39
      hfix39_39 hinj39_39 hcardT39_39
      (fun i => conj_mem_of_fixedPoints _ _ (T39_39 i) (hfix39_39 i) _)
      ⟨39, by decide⟩ ⟨39, by decide⟩ _
      (Q2.validAt ⟨39, by decide⟩ (Q2.listedAt ⟨39, by decide⟩
        (alnCheck_rep ⟨39, by decide⟩ hj hq).1))
      (colE2 ⟨39, by decide⟩ 2 hp) Q2.T39_39_2 Q2.hfix39_39_2 Q2.hinj39_39_2
      Q2.hcardT39_39_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T39_39_2 i) (Q2.hfix39_39_2 i) _)
      ?_).symm
  rw [show colData1 (⟨39, by decide⟩ : Fin 148)
        ((colE1 ⟨39, by decide⟩ 2 (transLenTr ⟨39, by decide⟩ 2 hp) : ↥(reps ⟨39, by decide⟩)) : Coordinate 1)
        T39_39 = colFn colCert_39_39_2.D (m := 25) from colCert_39_39_2.bind1,
    show colData2 (⟨39, by decide⟩ : Fin 148)
        ((colE2 ⟨39, by decide⟩ 2 hp : ↥(Q2.reps ⟨39, by decide⟩)) : Coordinate 2)
        Q2.T39_39_2 = colFn colCert_39_39_2.D (m := 25) from colCert_39_39_2.bind2]
  exact alnAll_39_39_2 j hj hq

theorem leaf_39_39_3 (hp : 3 < (Q2.transData.getD 39 []).length)
    (j : Nat) (hj : j < (repChars.getD 39 []).length)
    (hq : (normIsRep.getD 39 []).getD j false = true) :
    species (Q2.reps (⟨39, by decide⟩ : Fin 148)) (colE2 ⟨39, by decide⟩ 3 hp)
        (rowE2 (⟨39, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨39, by decide⟩ : Fin 148))
        (colE1 ⟨39, by decide⟩ 3 (transLenTr ⟨39, by decide⟩ 3 hp))
        (rowE1 (⟨39, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨39, by decide⟩ : Fin 148) ⟨39, by decide⟩ _
      (validAt ⟨39, by decide⟩ (listedAt ⟨39, by decide⟩ hj))
      (colE1 ⟨39, by decide⟩ 3 (transLenTr ⟨39, by decide⟩ 3 hp)) T39_39
      hfix39_39 hinj39_39 hcardT39_39
      (fun i => conj_mem_of_fixedPoints _ _ (T39_39 i) (hfix39_39 i) _)
      ⟨39, by decide⟩ ⟨39, by decide⟩ _
      (Q2.validAt ⟨39, by decide⟩ (Q2.listedAt ⟨39, by decide⟩
        (alnCheck_rep ⟨39, by decide⟩ hj hq).1))
      (colE2 ⟨39, by decide⟩ 3 hp) Q2.T39_39_2 Q2.hfix39_39_2 Q2.hinj39_39_2
      Q2.hcardT39_39_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T39_39_2 i) (Q2.hfix39_39_2 i) _)
      ?_).symm
  rw [show colData1 (⟨39, by decide⟩ : Fin 148)
        ((colE1 ⟨39, by decide⟩ 3 (transLenTr ⟨39, by decide⟩ 3 hp) : ↥(reps ⟨39, by decide⟩)) : Coordinate 1)
        T39_39 = colFn colCert_39_39_3.D (m := 25) from colCert_39_39_3.bind1,
    show colData2 (⟨39, by decide⟩ : Fin 148)
        ((colE2 ⟨39, by decide⟩ 3 hp : ↥(Q2.reps ⟨39, by decide⟩)) : Coordinate 2)
        Q2.T39_39_2 = colFn colCert_39_39_3.D (m := 25) from colCert_39_39_3.bind2]
  exact alnAll_39_39_3 j hj hq

theorem leaf_39_39_4 (hp : 4 < (Q2.transData.getD 39 []).length)
    (j : Nat) (hj : j < (repChars.getD 39 []).length)
    (hq : (normIsRep.getD 39 []).getD j false = true) :
    species (Q2.reps (⟨39, by decide⟩ : Fin 148)) (colE2 ⟨39, by decide⟩ 4 hp)
        (rowE2 (⟨39, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨39, by decide⟩ : Fin 148))
        (colE1 ⟨39, by decide⟩ 4 (transLenTr ⟨39, by decide⟩ 4 hp))
        (rowE1 (⟨39, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨39, by decide⟩ : Fin 148) ⟨39, by decide⟩ _
      (validAt ⟨39, by decide⟩ (listedAt ⟨39, by decide⟩ hj))
      (colE1 ⟨39, by decide⟩ 4 (transLenTr ⟨39, by decide⟩ 4 hp)) T39_39
      hfix39_39 hinj39_39 hcardT39_39
      (fun i => conj_mem_of_fixedPoints _ _ (T39_39 i) (hfix39_39 i) _)
      ⟨39, by decide⟩ ⟨39, by decide⟩ _
      (Q2.validAt ⟨39, by decide⟩ (Q2.listedAt ⟨39, by decide⟩
        (alnCheck_rep ⟨39, by decide⟩ hj hq).1))
      (colE2 ⟨39, by decide⟩ 4 hp) Q2.T39_39_2 Q2.hfix39_39_2 Q2.hinj39_39_2
      Q2.hcardT39_39_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T39_39_2 i) (Q2.hfix39_39_2 i) _)
      ?_).symm
  rw [show colData1 (⟨39, by decide⟩ : Fin 148)
        ((colE1 ⟨39, by decide⟩ 4 (transLenTr ⟨39, by decide⟩ 4 hp) : ↥(reps ⟨39, by decide⟩)) : Coordinate 1)
        T39_39 = colFn colCert_39_39_4.D (m := 25) from colCert_39_39_4.bind1,
    show colData2 (⟨39, by decide⟩ : Fin 148)
        ((colE2 ⟨39, by decide⟩ 4 hp : ↥(Q2.reps ⟨39, by decide⟩)) : Coordinate 2)
        Q2.T39_39_2 = colFn colCert_39_39_4.D (m := 25) from colCert_39_39_4.bind2]
  exact alnAll_39_39_4 j hj hq

theorem leaf_39_39_5 (hp : 5 < (Q2.transData.getD 39 []).length)
    (j : Nat) (hj : j < (repChars.getD 39 []).length)
    (hq : (normIsRep.getD 39 []).getD j false = true) :
    species (Q2.reps (⟨39, by decide⟩ : Fin 148)) (colE2 ⟨39, by decide⟩ 5 hp)
        (rowE2 (⟨39, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨39, by decide⟩ : Fin 148))
        (colE1 ⟨39, by decide⟩ 5 (transLenTr ⟨39, by decide⟩ 5 hp))
        (rowE1 (⟨39, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨39, by decide⟩ : Fin 148) ⟨39, by decide⟩ _
      (validAt ⟨39, by decide⟩ (listedAt ⟨39, by decide⟩ hj))
      (colE1 ⟨39, by decide⟩ 5 (transLenTr ⟨39, by decide⟩ 5 hp)) T39_39
      hfix39_39 hinj39_39 hcardT39_39
      (fun i => conj_mem_of_fixedPoints _ _ (T39_39 i) (hfix39_39 i) _)
      ⟨39, by decide⟩ ⟨39, by decide⟩ _
      (Q2.validAt ⟨39, by decide⟩ (Q2.listedAt ⟨39, by decide⟩
        (alnCheck_rep ⟨39, by decide⟩ hj hq).1))
      (colE2 ⟨39, by decide⟩ 5 hp) Q2.T39_39_2 Q2.hfix39_39_2 Q2.hinj39_39_2
      Q2.hcardT39_39_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T39_39_2 i) (Q2.hfix39_39_2 i) _)
      ?_).symm
  rw [show colData1 (⟨39, by decide⟩ : Fin 148)
        ((colE1 ⟨39, by decide⟩ 5 (transLenTr ⟨39, by decide⟩ 5 hp) : ↥(reps ⟨39, by decide⟩)) : Coordinate 1)
        T39_39 = colFn colCert_39_39_5.D (m := 25) from colCert_39_39_5.bind1,
    show colData2 (⟨39, by decide⟩ : Fin 148)
        ((colE2 ⟨39, by decide⟩ 5 hp : ↥(Q2.reps ⟨39, by decide⟩)) : Coordinate 2)
        Q2.T39_39_2 = colFn colCert_39_39_5.D (m := 25) from colCert_39_39_5.bind2]
  exact alnAll_39_39_5 j hj hq

theorem leaf_39_39_10 (hp : 10 < (Q2.transData.getD 39 []).length)
    (j : Nat) (hj : j < (repChars.getD 39 []).length)
    (hq : (normIsRep.getD 39 []).getD j false = true) :
    species (Q2.reps (⟨39, by decide⟩ : Fin 148)) (colE2 ⟨39, by decide⟩ 10 hp)
        (rowE2 (⟨39, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨39, by decide⟩ : Fin 148))
        (colE1 ⟨39, by decide⟩ 10 (transLenTr ⟨39, by decide⟩ 10 hp))
        (rowE1 (⟨39, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨39, by decide⟩ : Fin 148) ⟨39, by decide⟩ _
      (validAt ⟨39, by decide⟩ (listedAt ⟨39, by decide⟩ hj))
      (colE1 ⟨39, by decide⟩ 10 (transLenTr ⟨39, by decide⟩ 10 hp)) T39_39
      hfix39_39 hinj39_39 hcardT39_39
      (fun i => conj_mem_of_fixedPoints _ _ (T39_39 i) (hfix39_39 i) _)
      ⟨39, by decide⟩ ⟨39, by decide⟩ _
      (Q2.validAt ⟨39, by decide⟩ (Q2.listedAt ⟨39, by decide⟩
        (alnCheck_rep ⟨39, by decide⟩ hj hq).1))
      (colE2 ⟨39, by decide⟩ 10 hp) Q2.T39_39_2 Q2.hfix39_39_2 Q2.hinj39_39_2
      Q2.hcardT39_39_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T39_39_2 i) (Q2.hfix39_39_2 i) _)
      ?_).symm
  rw [show colData1 (⟨39, by decide⟩ : Fin 148)
        ((colE1 ⟨39, by decide⟩ 10 (transLenTr ⟨39, by decide⟩ 10 hp) : ↥(reps ⟨39, by decide⟩)) : Coordinate 1)
        T39_39 = colFn colCert_39_39_10.D (m := 25) from colCert_39_39_10.bind1,
    show colData2 (⟨39, by decide⟩ : Fin 148)
        ((colE2 ⟨39, by decide⟩ 10 hp : ↥(Q2.reps ⟨39, by decide⟩)) : Coordinate 2)
        Q2.T39_39_2 = colFn colCert_39_39_10.D (m := 25) from colCert_39_39_10.bind2]
  exact alnAll_39_39_10 j hj hq

theorem leaf_39_39_15 (hp : 15 < (Q2.transData.getD 39 []).length)
    (j : Nat) (hj : j < (repChars.getD 39 []).length)
    (hq : (normIsRep.getD 39 []).getD j false = true) :
    species (Q2.reps (⟨39, by decide⟩ : Fin 148)) (colE2 ⟨39, by decide⟩ 15 hp)
        (rowE2 (⟨39, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨39, by decide⟩ : Fin 148))
        (colE1 ⟨39, by decide⟩ 15 (transLenTr ⟨39, by decide⟩ 15 hp))
        (rowE1 (⟨39, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨39, by decide⟩ : Fin 148) ⟨39, by decide⟩ _
      (validAt ⟨39, by decide⟩ (listedAt ⟨39, by decide⟩ hj))
      (colE1 ⟨39, by decide⟩ 15 (transLenTr ⟨39, by decide⟩ 15 hp)) T39_39
      hfix39_39 hinj39_39 hcardT39_39
      (fun i => conj_mem_of_fixedPoints _ _ (T39_39 i) (hfix39_39 i) _)
      ⟨39, by decide⟩ ⟨39, by decide⟩ _
      (Q2.validAt ⟨39, by decide⟩ (Q2.listedAt ⟨39, by decide⟩
        (alnCheck_rep ⟨39, by decide⟩ hj hq).1))
      (colE2 ⟨39, by decide⟩ 15 hp) Q2.T39_39_2 Q2.hfix39_39_2 Q2.hinj39_39_2
      Q2.hcardT39_39_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T39_39_2 i) (Q2.hfix39_39_2 i) _)
      ?_).symm
  rw [show colData1 (⟨39, by decide⟩ : Fin 148)
        ((colE1 ⟨39, by decide⟩ 15 (transLenTr ⟨39, by decide⟩ 15 hp) : ↥(reps ⟨39, by decide⟩)) : Coordinate 1)
        T39_39 = colFn colCert_39_39_15.D (m := 25) from colCert_39_39_15.bind1,
    show colData2 (⟨39, by decide⟩ : Fin 148)
        ((colE2 ⟨39, by decide⟩ 15 hp : ↥(Q2.reps ⟨39, by decide⟩)) : Coordinate 2)
        Q2.T39_39_2 = colFn colCert_39_39_15.D (m := 25) from colCert_39_39_15.bind2]
  exact alnAll_39_39_15 j hj hq

theorem leaf_39_39_20 (hp : 20 < (Q2.transData.getD 39 []).length)
    (j : Nat) (hj : j < (repChars.getD 39 []).length)
    (hq : (normIsRep.getD 39 []).getD j false = true) :
    species (Q2.reps (⟨39, by decide⟩ : Fin 148)) (colE2 ⟨39, by decide⟩ 20 hp)
        (rowE2 (⟨39, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨39, by decide⟩ : Fin 148))
        (colE1 ⟨39, by decide⟩ 20 (transLenTr ⟨39, by decide⟩ 20 hp))
        (rowE1 (⟨39, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨39, by decide⟩ : Fin 148) ⟨39, by decide⟩ _
      (validAt ⟨39, by decide⟩ (listedAt ⟨39, by decide⟩ hj))
      (colE1 ⟨39, by decide⟩ 20 (transLenTr ⟨39, by decide⟩ 20 hp)) T39_39
      hfix39_39 hinj39_39 hcardT39_39
      (fun i => conj_mem_of_fixedPoints _ _ (T39_39 i) (hfix39_39 i) _)
      ⟨39, by decide⟩ ⟨39, by decide⟩ _
      (Q2.validAt ⟨39, by decide⟩ (Q2.listedAt ⟨39, by decide⟩
        (alnCheck_rep ⟨39, by decide⟩ hj hq).1))
      (colE2 ⟨39, by decide⟩ 20 hp) Q2.T39_39_2 Q2.hfix39_39_2 Q2.hinj39_39_2
      Q2.hcardT39_39_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T39_39_2 i) (Q2.hfix39_39_2 i) _)
      ?_).symm
  rw [show colData1 (⟨39, by decide⟩ : Fin 148)
        ((colE1 ⟨39, by decide⟩ 20 (transLenTr ⟨39, by decide⟩ 20 hp) : ↥(reps ⟨39, by decide⟩)) : Coordinate 1)
        T39_39 = colFn colCert_39_39_20.D (m := 25) from colCert_39_39_20.bind1,
    show colData2 (⟨39, by decide⟩ : Fin 148)
        ((colE2 ⟨39, by decide⟩ 20 hp : ↥(Q2.reps ⟨39, by decide⟩)) : Coordinate 2)
        Q2.T39_39_2 = colFn colCert_39_39_20.D (m := 25) from colCert_39_39_20.bind2]
  exact alnAll_39_39_20 j hj hq

theorem leaf_40_12_0 (hp : 0 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 40 []).length)
    (hq : (normIsRep.getD 40 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 0 hp)
        (rowE2 (⟨40, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp))
        (rowE1 (⟨40, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨40, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨40, by decide⟩ (listedAt ⟨40, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp)) T40_12
      hfix40_12 hinj40_12 hcardT40_12
      (fun i => conj_mem_of_fixedPoints _ _ (T40_12 i) (hfix40_12 i) _)
      ⟨40, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨40, by decide⟩ (Q2.listedAt ⟨40, by decide⟩
        (alnCheck_rep ⟨40, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 0 hp) Q2.T40_12_2 Q2.hfix40_12_2 Q2.hinj40_12_2
      Q2.hcardT40_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T40_12_2 i) (Q2.hfix40_12_2 i) _)
      ?_).symm
  rw [show colData1 (⟨40, by decide⟩ : Fin 148)
        ((colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp) : ↥(reps ⟨12, by decide⟩)) : Coordinate 1)
        T40_12 = colFn colCert_40_12_0.D (m := 125) from colCert_40_12_0.bind1,
    show colData2 (⟨40, by decide⟩ : Fin 148)
        ((colE2 ⟨12, by decide⟩ 0 hp : ↥(Q2.reps ⟨12, by decide⟩)) : Coordinate 2)
        Q2.T40_12_2 = colFn colCert_40_12_0.D (m := 125) from colCert_40_12_0.bind2]
  exact alnAll_40_12_0 j hj hq

theorem leaf_40_12_1 (hp : 1 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 40 []).length)
    (hq : (normIsRep.getD 40 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 1 hp)
        (rowE2 (⟨40, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp))
        (rowE1 (⟨40, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨40, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨40, by decide⟩ (listedAt ⟨40, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp)) T40_12
      hfix40_12 hinj40_12 hcardT40_12
      (fun i => conj_mem_of_fixedPoints _ _ (T40_12 i) (hfix40_12 i) _)
      ⟨40, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨40, by decide⟩ (Q2.listedAt ⟨40, by decide⟩
        (alnCheck_rep ⟨40, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 1 hp) Q2.T40_12_2 Q2.hfix40_12_2 Q2.hinj40_12_2
      Q2.hcardT40_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T40_12_2 i) (Q2.hfix40_12_2 i) _)
      ?_).symm
  rw [show colData1 (⟨40, by decide⟩ : Fin 148)
        ((colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp) : ↥(reps ⟨12, by decide⟩)) : Coordinate 1)
        T40_12 = colFn colCert_40_12_1.D (m := 125) from colCert_40_12_1.bind1,
    show colData2 (⟨40, by decide⟩ : Fin 148)
        ((colE2 ⟨12, by decide⟩ 1 hp : ↥(Q2.reps ⟨12, by decide⟩)) : Coordinate 2)
        Q2.T40_12_2 = colFn colCert_40_12_1.D (m := 125) from colCert_40_12_1.bind2]
  exact alnAll_40_12_1 j hj hq

theorem leaf_40_12_2 (hp : 2 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 40 []).length)
    (hq : (normIsRep.getD 40 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 2 hp)
        (rowE2 (⟨40, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp))
        (rowE1 (⟨40, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨40, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨40, by decide⟩ (listedAt ⟨40, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp)) T40_12
      hfix40_12 hinj40_12 hcardT40_12
      (fun i => conj_mem_of_fixedPoints _ _ (T40_12 i) (hfix40_12 i) _)
      ⟨40, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨40, by decide⟩ (Q2.listedAt ⟨40, by decide⟩
        (alnCheck_rep ⟨40, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 2 hp) Q2.T40_12_2 Q2.hfix40_12_2 Q2.hinj40_12_2
      Q2.hcardT40_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T40_12_2 i) (Q2.hfix40_12_2 i) _)
      ?_).symm
  rw [show colData1 (⟨40, by decide⟩ : Fin 148)
        ((colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp) : ↥(reps ⟨12, by decide⟩)) : Coordinate 1)
        T40_12 = colFn colCert_40_12_2.D (m := 125) from colCert_40_12_2.bind1,
    show colData2 (⟨40, by decide⟩ : Fin 148)
        ((colE2 ⟨12, by decide⟩ 2 hp : ↥(Q2.reps ⟨12, by decide⟩)) : Coordinate 2)
        Q2.T40_12_2 = colFn colCert_40_12_2.D (m := 125) from colCert_40_12_2.bind2]
  exact alnAll_40_12_2 j hj hq

theorem leaf_40_12_3 (hp : 3 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 40 []).length)
    (hq : (normIsRep.getD 40 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 3 hp)
        (rowE2 (⟨40, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp))
        (rowE1 (⟨40, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨40, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨40, by decide⟩ (listedAt ⟨40, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp)) T40_12
      hfix40_12 hinj40_12 hcardT40_12
      (fun i => conj_mem_of_fixedPoints _ _ (T40_12 i) (hfix40_12 i) _)
      ⟨40, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨40, by decide⟩ (Q2.listedAt ⟨40, by decide⟩
        (alnCheck_rep ⟨40, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 3 hp) Q2.T40_12_2 Q2.hfix40_12_2 Q2.hinj40_12_2
      Q2.hcardT40_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T40_12_2 i) (Q2.hfix40_12_2 i) _)
      ?_).symm
  rw [show colData1 (⟨40, by decide⟩ : Fin 148)
        ((colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp) : ↥(reps ⟨12, by decide⟩)) : Coordinate 1)
        T40_12 = colFn colCert_40_12_3.D (m := 125) from colCert_40_12_3.bind1,
    show colData2 (⟨40, by decide⟩ : Fin 148)
        ((colE2 ⟨12, by decide⟩ 3 hp : ↥(Q2.reps ⟨12, by decide⟩)) : Coordinate 2)
        Q2.T40_12_2 = colFn colCert_40_12_3.D (m := 125) from colCert_40_12_3.bind2]
  exact alnAll_40_12_3 j hj hq

theorem leaf_40_12_4 (hp : 4 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 40 []).length)
    (hq : (normIsRep.getD 40 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 4 hp)
        (rowE2 (⟨40, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp))
        (rowE1 (⟨40, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨40, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨40, by decide⟩ (listedAt ⟨40, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp)) T40_12
      hfix40_12 hinj40_12 hcardT40_12
      (fun i => conj_mem_of_fixedPoints _ _ (T40_12 i) (hfix40_12 i) _)
      ⟨40, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨40, by decide⟩ (Q2.listedAt ⟨40, by decide⟩
        (alnCheck_rep ⟨40, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 4 hp) Q2.T40_12_2 Q2.hfix40_12_2 Q2.hinj40_12_2
      Q2.hcardT40_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T40_12_2 i) (Q2.hfix40_12_2 i) _)
      ?_).symm
  rw [show colData1 (⟨40, by decide⟩ : Fin 148)
        ((colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp) : ↥(reps ⟨12, by decide⟩)) : Coordinate 1)
        T40_12 = colFn colCert_40_12_4.D (m := 125) from colCert_40_12_4.bind1,
    show colData2 (⟨40, by decide⟩ : Fin 148)
        ((colE2 ⟨12, by decide⟩ 4 hp : ↥(Q2.reps ⟨12, by decide⟩)) : Coordinate 2)
        Q2.T40_12_2 = colFn colCert_40_12_4.D (m := 125) from colCert_40_12_4.bind2]
  exact alnAll_40_12_4 j hj hq

theorem leaf_40_40_0 (hp : 0 < (Q2.transData.getD 40 []).length)
    (j : Nat) (hj : j < (repChars.getD 40 []).length)
    (hq : (normIsRep.getD 40 []).getD j false = true) :
    species (Q2.reps (⟨40, by decide⟩ : Fin 148)) (colE2 ⟨40, by decide⟩ 0 hp)
        (rowE2 (⟨40, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨40, by decide⟩ : Fin 148))
        (colE1 ⟨40, by decide⟩ 0 (transLenTr ⟨40, by decide⟩ 0 hp))
        (rowE1 (⟨40, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨40, by decide⟩ : Fin 148) ⟨40, by decide⟩ _
      (validAt ⟨40, by decide⟩ (listedAt ⟨40, by decide⟩ hj))
      (colE1 ⟨40, by decide⟩ 0 (transLenTr ⟨40, by decide⟩ 0 hp)) T40_40
      hfix40_40 hinj40_40 hcardT40_40
      (fun i => conj_mem_of_fixedPoints _ _ (T40_40 i) (hfix40_40 i) _)
      ⟨40, by decide⟩ ⟨40, by decide⟩ _
      (Q2.validAt ⟨40, by decide⟩ (Q2.listedAt ⟨40, by decide⟩
        (alnCheck_rep ⟨40, by decide⟩ hj hq).1))
      (colE2 ⟨40, by decide⟩ 0 hp) Q2.T40_40_2 Q2.hfix40_40_2 Q2.hinj40_40_2
      Q2.hcardT40_40_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T40_40_2 i) (Q2.hfix40_40_2 i) _)
      ?_).symm
  rw [show colData1 (⟨40, by decide⟩ : Fin 148)
        ((colE1 ⟨40, by decide⟩ 0 (transLenTr ⟨40, by decide⟩ 0 hp) : ↥(reps ⟨40, by decide⟩)) : Coordinate 1)
        T40_40 = colFn colCert_40_40_0.D (m := 25) from colCert_40_40_0.bind1,
    show colData2 (⟨40, by decide⟩ : Fin 148)
        ((colE2 ⟨40, by decide⟩ 0 hp : ↥(Q2.reps ⟨40, by decide⟩)) : Coordinate 2)
        Q2.T40_40_2 = colFn colCert_40_40_0.D (m := 25) from colCert_40_40_0.bind2]
  exact alnAll_40_40_0 j hj hq

theorem leaf_40_40_1 (hp : 1 < (Q2.transData.getD 40 []).length)
    (j : Nat) (hj : j < (repChars.getD 40 []).length)
    (hq : (normIsRep.getD 40 []).getD j false = true) :
    species (Q2.reps (⟨40, by decide⟩ : Fin 148)) (colE2 ⟨40, by decide⟩ 1 hp)
        (rowE2 (⟨40, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨40, by decide⟩ : Fin 148))
        (colE1 ⟨40, by decide⟩ 1 (transLenTr ⟨40, by decide⟩ 1 hp))
        (rowE1 (⟨40, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨40, by decide⟩ : Fin 148) ⟨40, by decide⟩ _
      (validAt ⟨40, by decide⟩ (listedAt ⟨40, by decide⟩ hj))
      (colE1 ⟨40, by decide⟩ 1 (transLenTr ⟨40, by decide⟩ 1 hp)) T40_40
      hfix40_40 hinj40_40 hcardT40_40
      (fun i => conj_mem_of_fixedPoints _ _ (T40_40 i) (hfix40_40 i) _)
      ⟨40, by decide⟩ ⟨40, by decide⟩ _
      (Q2.validAt ⟨40, by decide⟩ (Q2.listedAt ⟨40, by decide⟩
        (alnCheck_rep ⟨40, by decide⟩ hj hq).1))
      (colE2 ⟨40, by decide⟩ 1 hp) Q2.T40_40_2 Q2.hfix40_40_2 Q2.hinj40_40_2
      Q2.hcardT40_40_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T40_40_2 i) (Q2.hfix40_40_2 i) _)
      ?_).symm
  rw [show colData1 (⟨40, by decide⟩ : Fin 148)
        ((colE1 ⟨40, by decide⟩ 1 (transLenTr ⟨40, by decide⟩ 1 hp) : ↥(reps ⟨40, by decide⟩)) : Coordinate 1)
        T40_40 = colFn colCert_40_40_1.D (m := 25) from colCert_40_40_1.bind1,
    show colData2 (⟨40, by decide⟩ : Fin 148)
        ((colE2 ⟨40, by decide⟩ 1 hp : ↥(Q2.reps ⟨40, by decide⟩)) : Coordinate 2)
        Q2.T40_40_2 = colFn colCert_40_40_1.D (m := 25) from colCert_40_40_1.bind2]
  exact alnAll_40_40_1 j hj hq

theorem leaf_40_40_2 (hp : 2 < (Q2.transData.getD 40 []).length)
    (j : Nat) (hj : j < (repChars.getD 40 []).length)
    (hq : (normIsRep.getD 40 []).getD j false = true) :
    species (Q2.reps (⟨40, by decide⟩ : Fin 148)) (colE2 ⟨40, by decide⟩ 2 hp)
        (rowE2 (⟨40, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨40, by decide⟩ : Fin 148))
        (colE1 ⟨40, by decide⟩ 2 (transLenTr ⟨40, by decide⟩ 2 hp))
        (rowE1 (⟨40, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨40, by decide⟩ : Fin 148) ⟨40, by decide⟩ _
      (validAt ⟨40, by decide⟩ (listedAt ⟨40, by decide⟩ hj))
      (colE1 ⟨40, by decide⟩ 2 (transLenTr ⟨40, by decide⟩ 2 hp)) T40_40
      hfix40_40 hinj40_40 hcardT40_40
      (fun i => conj_mem_of_fixedPoints _ _ (T40_40 i) (hfix40_40 i) _)
      ⟨40, by decide⟩ ⟨40, by decide⟩ _
      (Q2.validAt ⟨40, by decide⟩ (Q2.listedAt ⟨40, by decide⟩
        (alnCheck_rep ⟨40, by decide⟩ hj hq).1))
      (colE2 ⟨40, by decide⟩ 2 hp) Q2.T40_40_2 Q2.hfix40_40_2 Q2.hinj40_40_2
      Q2.hcardT40_40_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T40_40_2 i) (Q2.hfix40_40_2 i) _)
      ?_).symm
  rw [show colData1 (⟨40, by decide⟩ : Fin 148)
        ((colE1 ⟨40, by decide⟩ 2 (transLenTr ⟨40, by decide⟩ 2 hp) : ↥(reps ⟨40, by decide⟩)) : Coordinate 1)
        T40_40 = colFn colCert_40_40_2.D (m := 25) from colCert_40_40_2.bind1,
    show colData2 (⟨40, by decide⟩ : Fin 148)
        ((colE2 ⟨40, by decide⟩ 2 hp : ↥(Q2.reps ⟨40, by decide⟩)) : Coordinate 2)
        Q2.T40_40_2 = colFn colCert_40_40_2.D (m := 25) from colCert_40_40_2.bind2]
  exact alnAll_40_40_2 j hj hq

theorem leaf_40_40_3 (hp : 3 < (Q2.transData.getD 40 []).length)
    (j : Nat) (hj : j < (repChars.getD 40 []).length)
    (hq : (normIsRep.getD 40 []).getD j false = true) :
    species (Q2.reps (⟨40, by decide⟩ : Fin 148)) (colE2 ⟨40, by decide⟩ 3 hp)
        (rowE2 (⟨40, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨40, by decide⟩ : Fin 148))
        (colE1 ⟨40, by decide⟩ 3 (transLenTr ⟨40, by decide⟩ 3 hp))
        (rowE1 (⟨40, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨40, by decide⟩ : Fin 148) ⟨40, by decide⟩ _
      (validAt ⟨40, by decide⟩ (listedAt ⟨40, by decide⟩ hj))
      (colE1 ⟨40, by decide⟩ 3 (transLenTr ⟨40, by decide⟩ 3 hp)) T40_40
      hfix40_40 hinj40_40 hcardT40_40
      (fun i => conj_mem_of_fixedPoints _ _ (T40_40 i) (hfix40_40 i) _)
      ⟨40, by decide⟩ ⟨40, by decide⟩ _
      (Q2.validAt ⟨40, by decide⟩ (Q2.listedAt ⟨40, by decide⟩
        (alnCheck_rep ⟨40, by decide⟩ hj hq).1))
      (colE2 ⟨40, by decide⟩ 3 hp) Q2.T40_40_2 Q2.hfix40_40_2 Q2.hinj40_40_2
      Q2.hcardT40_40_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T40_40_2 i) (Q2.hfix40_40_2 i) _)
      ?_).symm
  rw [show colData1 (⟨40, by decide⟩ : Fin 148)
        ((colE1 ⟨40, by decide⟩ 3 (transLenTr ⟨40, by decide⟩ 3 hp) : ↥(reps ⟨40, by decide⟩)) : Coordinate 1)
        T40_40 = colFn colCert_40_40_3.D (m := 25) from colCert_40_40_3.bind1,
    show colData2 (⟨40, by decide⟩ : Fin 148)
        ((colE2 ⟨40, by decide⟩ 3 hp : ↥(Q2.reps ⟨40, by decide⟩)) : Coordinate 2)
        Q2.T40_40_2 = colFn colCert_40_40_3.D (m := 25) from colCert_40_40_3.bind2]
  exact alnAll_40_40_3 j hj hq

theorem leaf_40_40_4 (hp : 4 < (Q2.transData.getD 40 []).length)
    (j : Nat) (hj : j < (repChars.getD 40 []).length)
    (hq : (normIsRep.getD 40 []).getD j false = true) :
    species (Q2.reps (⟨40, by decide⟩ : Fin 148)) (colE2 ⟨40, by decide⟩ 4 hp)
        (rowE2 (⟨40, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨40, by decide⟩ : Fin 148))
        (colE1 ⟨40, by decide⟩ 4 (transLenTr ⟨40, by decide⟩ 4 hp))
        (rowE1 (⟨40, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨40, by decide⟩ : Fin 148) ⟨40, by decide⟩ _
      (validAt ⟨40, by decide⟩ (listedAt ⟨40, by decide⟩ hj))
      (colE1 ⟨40, by decide⟩ 4 (transLenTr ⟨40, by decide⟩ 4 hp)) T40_40
      hfix40_40 hinj40_40 hcardT40_40
      (fun i => conj_mem_of_fixedPoints _ _ (T40_40 i) (hfix40_40 i) _)
      ⟨40, by decide⟩ ⟨40, by decide⟩ _
      (Q2.validAt ⟨40, by decide⟩ (Q2.listedAt ⟨40, by decide⟩
        (alnCheck_rep ⟨40, by decide⟩ hj hq).1))
      (colE2 ⟨40, by decide⟩ 4 hp) Q2.T40_40_2 Q2.hfix40_40_2 Q2.hinj40_40_2
      Q2.hcardT40_40_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T40_40_2 i) (Q2.hfix40_40_2 i) _)
      ?_).symm
  rw [show colData1 (⟨40, by decide⟩ : Fin 148)
        ((colE1 ⟨40, by decide⟩ 4 (transLenTr ⟨40, by decide⟩ 4 hp) : ↥(reps ⟨40, by decide⟩)) : Coordinate 1)
        T40_40 = colFn colCert_40_40_4.D (m := 25) from colCert_40_40_4.bind1,
    show colData2 (⟨40, by decide⟩ : Fin 148)
        ((colE2 ⟨40, by decide⟩ 4 hp : ↥(Q2.reps ⟨40, by decide⟩)) : Coordinate 2)
        Q2.T40_40_2 = colFn colCert_40_40_4.D (m := 25) from colCert_40_40_4.bind2]
  exact alnAll_40_40_4 j hj hq

theorem leaf_40_40_5 (hp : 5 < (Q2.transData.getD 40 []).length)
    (j : Nat) (hj : j < (repChars.getD 40 []).length)
    (hq : (normIsRep.getD 40 []).getD j false = true) :
    species (Q2.reps (⟨40, by decide⟩ : Fin 148)) (colE2 ⟨40, by decide⟩ 5 hp)
        (rowE2 (⟨40, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨40, by decide⟩ : Fin 148))
        (colE1 ⟨40, by decide⟩ 5 (transLenTr ⟨40, by decide⟩ 5 hp))
        (rowE1 (⟨40, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨40, by decide⟩ : Fin 148) ⟨40, by decide⟩ _
      (validAt ⟨40, by decide⟩ (listedAt ⟨40, by decide⟩ hj))
      (colE1 ⟨40, by decide⟩ 5 (transLenTr ⟨40, by decide⟩ 5 hp)) T40_40
      hfix40_40 hinj40_40 hcardT40_40
      (fun i => conj_mem_of_fixedPoints _ _ (T40_40 i) (hfix40_40 i) _)
      ⟨40, by decide⟩ ⟨40, by decide⟩ _
      (Q2.validAt ⟨40, by decide⟩ (Q2.listedAt ⟨40, by decide⟩
        (alnCheck_rep ⟨40, by decide⟩ hj hq).1))
      (colE2 ⟨40, by decide⟩ 5 hp) Q2.T40_40_2 Q2.hfix40_40_2 Q2.hinj40_40_2
      Q2.hcardT40_40_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T40_40_2 i) (Q2.hfix40_40_2 i) _)
      ?_).symm
  rw [show colData1 (⟨40, by decide⟩ : Fin 148)
        ((colE1 ⟨40, by decide⟩ 5 (transLenTr ⟨40, by decide⟩ 5 hp) : ↥(reps ⟨40, by decide⟩)) : Coordinate 1)
        T40_40 = colFn colCert_40_40_5.D (m := 25) from colCert_40_40_5.bind1,
    show colData2 (⟨40, by decide⟩ : Fin 148)
        ((colE2 ⟨40, by decide⟩ 5 hp : ↥(Q2.reps ⟨40, by decide⟩)) : Coordinate 2)
        Q2.T40_40_2 = colFn colCert_40_40_5.D (m := 25) from colCert_40_40_5.bind2]
  exact alnAll_40_40_5 j hj hq

theorem leaf_40_40_10 (hp : 10 < (Q2.transData.getD 40 []).length)
    (j : Nat) (hj : j < (repChars.getD 40 []).length)
    (hq : (normIsRep.getD 40 []).getD j false = true) :
    species (Q2.reps (⟨40, by decide⟩ : Fin 148)) (colE2 ⟨40, by decide⟩ 10 hp)
        (rowE2 (⟨40, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨40, by decide⟩ : Fin 148))
        (colE1 ⟨40, by decide⟩ 10 (transLenTr ⟨40, by decide⟩ 10 hp))
        (rowE1 (⟨40, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨40, by decide⟩ : Fin 148) ⟨40, by decide⟩ _
      (validAt ⟨40, by decide⟩ (listedAt ⟨40, by decide⟩ hj))
      (colE1 ⟨40, by decide⟩ 10 (transLenTr ⟨40, by decide⟩ 10 hp)) T40_40
      hfix40_40 hinj40_40 hcardT40_40
      (fun i => conj_mem_of_fixedPoints _ _ (T40_40 i) (hfix40_40 i) _)
      ⟨40, by decide⟩ ⟨40, by decide⟩ _
      (Q2.validAt ⟨40, by decide⟩ (Q2.listedAt ⟨40, by decide⟩
        (alnCheck_rep ⟨40, by decide⟩ hj hq).1))
      (colE2 ⟨40, by decide⟩ 10 hp) Q2.T40_40_2 Q2.hfix40_40_2 Q2.hinj40_40_2
      Q2.hcardT40_40_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T40_40_2 i) (Q2.hfix40_40_2 i) _)
      ?_).symm
  rw [show colData1 (⟨40, by decide⟩ : Fin 148)
        ((colE1 ⟨40, by decide⟩ 10 (transLenTr ⟨40, by decide⟩ 10 hp) : ↥(reps ⟨40, by decide⟩)) : Coordinate 1)
        T40_40 = colFn colCert_40_40_10.D (m := 25) from colCert_40_40_10.bind1,
    show colData2 (⟨40, by decide⟩ : Fin 148)
        ((colE2 ⟨40, by decide⟩ 10 hp : ↥(Q2.reps ⟨40, by decide⟩)) : Coordinate 2)
        Q2.T40_40_2 = colFn colCert_40_40_10.D (m := 25) from colCert_40_40_10.bind2]
  exact alnAll_40_40_10 j hj hq

theorem leaf_40_40_15 (hp : 15 < (Q2.transData.getD 40 []).length)
    (j : Nat) (hj : j < (repChars.getD 40 []).length)
    (hq : (normIsRep.getD 40 []).getD j false = true) :
    species (Q2.reps (⟨40, by decide⟩ : Fin 148)) (colE2 ⟨40, by decide⟩ 15 hp)
        (rowE2 (⟨40, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨40, by decide⟩ : Fin 148))
        (colE1 ⟨40, by decide⟩ 15 (transLenTr ⟨40, by decide⟩ 15 hp))
        (rowE1 (⟨40, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨40, by decide⟩ : Fin 148) ⟨40, by decide⟩ _
      (validAt ⟨40, by decide⟩ (listedAt ⟨40, by decide⟩ hj))
      (colE1 ⟨40, by decide⟩ 15 (transLenTr ⟨40, by decide⟩ 15 hp)) T40_40
      hfix40_40 hinj40_40 hcardT40_40
      (fun i => conj_mem_of_fixedPoints _ _ (T40_40 i) (hfix40_40 i) _)
      ⟨40, by decide⟩ ⟨40, by decide⟩ _
      (Q2.validAt ⟨40, by decide⟩ (Q2.listedAt ⟨40, by decide⟩
        (alnCheck_rep ⟨40, by decide⟩ hj hq).1))
      (colE2 ⟨40, by decide⟩ 15 hp) Q2.T40_40_2 Q2.hfix40_40_2 Q2.hinj40_40_2
      Q2.hcardT40_40_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T40_40_2 i) (Q2.hfix40_40_2 i) _)
      ?_).symm
  rw [show colData1 (⟨40, by decide⟩ : Fin 148)
        ((colE1 ⟨40, by decide⟩ 15 (transLenTr ⟨40, by decide⟩ 15 hp) : ↥(reps ⟨40, by decide⟩)) : Coordinate 1)
        T40_40 = colFn colCert_40_40_15.D (m := 25) from colCert_40_40_15.bind1,
    show colData2 (⟨40, by decide⟩ : Fin 148)
        ((colE2 ⟨40, by decide⟩ 15 hp : ↥(Q2.reps ⟨40, by decide⟩)) : Coordinate 2)
        Q2.T40_40_2 = colFn colCert_40_40_15.D (m := 25) from colCert_40_40_15.bind2]
  exact alnAll_40_40_15 j hj hq

theorem leaf_40_40_20 (hp : 20 < (Q2.transData.getD 40 []).length)
    (j : Nat) (hj : j < (repChars.getD 40 []).length)
    (hq : (normIsRep.getD 40 []).getD j false = true) :
    species (Q2.reps (⟨40, by decide⟩ : Fin 148)) (colE2 ⟨40, by decide⟩ 20 hp)
        (rowE2 (⟨40, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨40, by decide⟩ : Fin 148))
        (colE1 ⟨40, by decide⟩ 20 (transLenTr ⟨40, by decide⟩ 20 hp))
        (rowE1 (⟨40, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨40, by decide⟩ : Fin 148) ⟨40, by decide⟩ _
      (validAt ⟨40, by decide⟩ (listedAt ⟨40, by decide⟩ hj))
      (colE1 ⟨40, by decide⟩ 20 (transLenTr ⟨40, by decide⟩ 20 hp)) T40_40
      hfix40_40 hinj40_40 hcardT40_40
      (fun i => conj_mem_of_fixedPoints _ _ (T40_40 i) (hfix40_40 i) _)
      ⟨40, by decide⟩ ⟨40, by decide⟩ _
      (Q2.validAt ⟨40, by decide⟩ (Q2.listedAt ⟨40, by decide⟩
        (alnCheck_rep ⟨40, by decide⟩ hj hq).1))
      (colE2 ⟨40, by decide⟩ 20 hp) Q2.T40_40_2 Q2.hfix40_40_2 Q2.hinj40_40_2
      Q2.hcardT40_40_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T40_40_2 i) (Q2.hfix40_40_2 i) _)
      ?_).symm
  rw [show colData1 (⟨40, by decide⟩ : Fin 148)
        ((colE1 ⟨40, by decide⟩ 20 (transLenTr ⟨40, by decide⟩ 20 hp) : ↥(reps ⟨40, by decide⟩)) : Coordinate 1)
        T40_40 = colFn colCert_40_40_20.D (m := 25) from colCert_40_40_20.bind1,
    show colData2 (⟨40, by decide⟩ : Fin 148)
        ((colE2 ⟨40, by decide⟩ 20 hp : ↥(Q2.reps ⟨40, by decide⟩)) : Coordinate 2)
        Q2.T40_40_2 = colFn colCert_40_40_20.D (m := 25) from colCert_40_40_20.bind2]
  exact alnAll_40_40_20 j hj hq

theorem leaf_41_12_0 (hp : 0 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 41 []).length)
    (hq : (normIsRep.getD 41 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 0 hp)
        (rowE2 (⟨41, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp))
        (rowE1 (⟨41, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨41, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨41, by decide⟩ (listedAt ⟨41, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp)) T41_12
      hfix41_12 hinj41_12 hcardT41_12
      (fun i => conj_mem_of_fixedPoints _ _ (T41_12 i) (hfix41_12 i) _)
      ⟨41, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨41, by decide⟩ (Q2.listedAt ⟨41, by decide⟩
        (alnCheck_rep ⟨41, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 0 hp) Q2.T41_12_2 Q2.hfix41_12_2 Q2.hinj41_12_2
      Q2.hcardT41_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T41_12_2 i) (Q2.hfix41_12_2 i) _)
      ?_).symm
  rw [show colData1 (⟨41, by decide⟩ : Fin 148)
        ((colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp) : ↥(reps ⟨12, by decide⟩)) : Coordinate 1)
        T41_12 = colFn colCert_41_12_0.D (m := 125) from colCert_41_12_0.bind1,
    show colData2 (⟨41, by decide⟩ : Fin 148)
        ((colE2 ⟨12, by decide⟩ 0 hp : ↥(Q2.reps ⟨12, by decide⟩)) : Coordinate 2)
        Q2.T41_12_2 = colFn colCert_41_12_0.D (m := 125) from colCert_41_12_0.bind2]
  exact alnAll_41_12_0 j hj hq

theorem leaf_41_12_1 (hp : 1 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 41 []).length)
    (hq : (normIsRep.getD 41 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 1 hp)
        (rowE2 (⟨41, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp))
        (rowE1 (⟨41, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨41, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨41, by decide⟩ (listedAt ⟨41, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp)) T41_12
      hfix41_12 hinj41_12 hcardT41_12
      (fun i => conj_mem_of_fixedPoints _ _ (T41_12 i) (hfix41_12 i) _)
      ⟨41, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨41, by decide⟩ (Q2.listedAt ⟨41, by decide⟩
        (alnCheck_rep ⟨41, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 1 hp) Q2.T41_12_2 Q2.hfix41_12_2 Q2.hinj41_12_2
      Q2.hcardT41_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T41_12_2 i) (Q2.hfix41_12_2 i) _)
      ?_).symm
  rw [show colData1 (⟨41, by decide⟩ : Fin 148)
        ((colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp) : ↥(reps ⟨12, by decide⟩)) : Coordinate 1)
        T41_12 = colFn colCert_41_12_1.D (m := 125) from colCert_41_12_1.bind1,
    show colData2 (⟨41, by decide⟩ : Fin 148)
        ((colE2 ⟨12, by decide⟩ 1 hp : ↥(Q2.reps ⟨12, by decide⟩)) : Coordinate 2)
        Q2.T41_12_2 = colFn colCert_41_12_1.D (m := 125) from colCert_41_12_1.bind2]
  exact alnAll_41_12_1 j hj hq

theorem leaf_41_12_2 (hp : 2 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 41 []).length)
    (hq : (normIsRep.getD 41 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 2 hp)
        (rowE2 (⟨41, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp))
        (rowE1 (⟨41, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨41, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨41, by decide⟩ (listedAt ⟨41, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp)) T41_12
      hfix41_12 hinj41_12 hcardT41_12
      (fun i => conj_mem_of_fixedPoints _ _ (T41_12 i) (hfix41_12 i) _)
      ⟨41, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨41, by decide⟩ (Q2.listedAt ⟨41, by decide⟩
        (alnCheck_rep ⟨41, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 2 hp) Q2.T41_12_2 Q2.hfix41_12_2 Q2.hinj41_12_2
      Q2.hcardT41_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T41_12_2 i) (Q2.hfix41_12_2 i) _)
      ?_).symm
  rw [show colData1 (⟨41, by decide⟩ : Fin 148)
        ((colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp) : ↥(reps ⟨12, by decide⟩)) : Coordinate 1)
        T41_12 = colFn colCert_41_12_2.D (m := 125) from colCert_41_12_2.bind1,
    show colData2 (⟨41, by decide⟩ : Fin 148)
        ((colE2 ⟨12, by decide⟩ 2 hp : ↥(Q2.reps ⟨12, by decide⟩)) : Coordinate 2)
        Q2.T41_12_2 = colFn colCert_41_12_2.D (m := 125) from colCert_41_12_2.bind2]
  exact alnAll_41_12_2 j hj hq

theorem leaf_41_12_3 (hp : 3 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 41 []).length)
    (hq : (normIsRep.getD 41 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 3 hp)
        (rowE2 (⟨41, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp))
        (rowE1 (⟨41, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨41, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨41, by decide⟩ (listedAt ⟨41, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp)) T41_12
      hfix41_12 hinj41_12 hcardT41_12
      (fun i => conj_mem_of_fixedPoints _ _ (T41_12 i) (hfix41_12 i) _)
      ⟨41, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨41, by decide⟩ (Q2.listedAt ⟨41, by decide⟩
        (alnCheck_rep ⟨41, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 3 hp) Q2.T41_12_2 Q2.hfix41_12_2 Q2.hinj41_12_2
      Q2.hcardT41_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T41_12_2 i) (Q2.hfix41_12_2 i) _)
      ?_).symm
  rw [show colData1 (⟨41, by decide⟩ : Fin 148)
        ((colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp) : ↥(reps ⟨12, by decide⟩)) : Coordinate 1)
        T41_12 = colFn colCert_41_12_3.D (m := 125) from colCert_41_12_3.bind1,
    show colData2 (⟨41, by decide⟩ : Fin 148)
        ((colE2 ⟨12, by decide⟩ 3 hp : ↥(Q2.reps ⟨12, by decide⟩)) : Coordinate 2)
        Q2.T41_12_2 = colFn colCert_41_12_3.D (m := 125) from colCert_41_12_3.bind2]
  exact alnAll_41_12_3 j hj hq

theorem leaf_41_12_4 (hp : 4 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 41 []).length)
    (hq : (normIsRep.getD 41 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 4 hp)
        (rowE2 (⟨41, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp))
        (rowE1 (⟨41, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨41, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨41, by decide⟩ (listedAt ⟨41, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp)) T41_12
      hfix41_12 hinj41_12 hcardT41_12
      (fun i => conj_mem_of_fixedPoints _ _ (T41_12 i) (hfix41_12 i) _)
      ⟨41, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨41, by decide⟩ (Q2.listedAt ⟨41, by decide⟩
        (alnCheck_rep ⟨41, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 4 hp) Q2.T41_12_2 Q2.hfix41_12_2 Q2.hinj41_12_2
      Q2.hcardT41_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T41_12_2 i) (Q2.hfix41_12_2 i) _)
      ?_).symm
  rw [show colData1 (⟨41, by decide⟩ : Fin 148)
        ((colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp) : ↥(reps ⟨12, by decide⟩)) : Coordinate 1)
        T41_12 = colFn colCert_41_12_4.D (m := 125) from colCert_41_12_4.bind1,
    show colData2 (⟨41, by decide⟩ : Fin 148)
        ((colE2 ⟨12, by decide⟩ 4 hp : ↥(Q2.reps ⟨12, by decide⟩)) : Coordinate 2)
        Q2.T41_12_2 = colFn colCert_41_12_4.D (m := 125) from colCert_41_12_4.bind2]
  exact alnAll_41_12_4 j hj hq

theorem leaf_41_41_0 (hp : 0 < (Q2.transData.getD 41 []).length)
    (j : Nat) (hj : j < (repChars.getD 41 []).length)
    (hq : (normIsRep.getD 41 []).getD j false = true) :
    species (Q2.reps (⟨41, by decide⟩ : Fin 148)) (colE2 ⟨41, by decide⟩ 0 hp)
        (rowE2 (⟨41, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨41, by decide⟩ : Fin 148))
        (colE1 ⟨41, by decide⟩ 0 (transLenTr ⟨41, by decide⟩ 0 hp))
        (rowE1 (⟨41, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨41, by decide⟩ : Fin 148) ⟨41, by decide⟩ _
      (validAt ⟨41, by decide⟩ (listedAt ⟨41, by decide⟩ hj))
      (colE1 ⟨41, by decide⟩ 0 (transLenTr ⟨41, by decide⟩ 0 hp)) T41_41
      hfix41_41 hinj41_41 hcardT41_41
      (fun i => conj_mem_of_fixedPoints _ _ (T41_41 i) (hfix41_41 i) _)
      ⟨41, by decide⟩ ⟨41, by decide⟩ _
      (Q2.validAt ⟨41, by decide⟩ (Q2.listedAt ⟨41, by decide⟩
        (alnCheck_rep ⟨41, by decide⟩ hj hq).1))
      (colE2 ⟨41, by decide⟩ 0 hp) Q2.T41_41_2 Q2.hfix41_41_2 Q2.hinj41_41_2
      Q2.hcardT41_41_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T41_41_2 i) (Q2.hfix41_41_2 i) _)
      ?_).symm
  rw [show colData1 (⟨41, by decide⟩ : Fin 148)
        ((colE1 ⟨41, by decide⟩ 0 (transLenTr ⟨41, by decide⟩ 0 hp) : ↥(reps ⟨41, by decide⟩)) : Coordinate 1)
        T41_41 = colFn colCert_41_41_0.D (m := 25) from colCert_41_41_0.bind1,
    show colData2 (⟨41, by decide⟩ : Fin 148)
        ((colE2 ⟨41, by decide⟩ 0 hp : ↥(Q2.reps ⟨41, by decide⟩)) : Coordinate 2)
        Q2.T41_41_2 = colFn colCert_41_41_0.D (m := 25) from colCert_41_41_0.bind2]
  exact alnAll_41_41_0 j hj hq

theorem leaf_41_41_1 (hp : 1 < (Q2.transData.getD 41 []).length)
    (j : Nat) (hj : j < (repChars.getD 41 []).length)
    (hq : (normIsRep.getD 41 []).getD j false = true) :
    species (Q2.reps (⟨41, by decide⟩ : Fin 148)) (colE2 ⟨41, by decide⟩ 1 hp)
        (rowE2 (⟨41, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨41, by decide⟩ : Fin 148))
        (colE1 ⟨41, by decide⟩ 1 (transLenTr ⟨41, by decide⟩ 1 hp))
        (rowE1 (⟨41, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨41, by decide⟩ : Fin 148) ⟨41, by decide⟩ _
      (validAt ⟨41, by decide⟩ (listedAt ⟨41, by decide⟩ hj))
      (colE1 ⟨41, by decide⟩ 1 (transLenTr ⟨41, by decide⟩ 1 hp)) T41_41
      hfix41_41 hinj41_41 hcardT41_41
      (fun i => conj_mem_of_fixedPoints _ _ (T41_41 i) (hfix41_41 i) _)
      ⟨41, by decide⟩ ⟨41, by decide⟩ _
      (Q2.validAt ⟨41, by decide⟩ (Q2.listedAt ⟨41, by decide⟩
        (alnCheck_rep ⟨41, by decide⟩ hj hq).1))
      (colE2 ⟨41, by decide⟩ 1 hp) Q2.T41_41_2 Q2.hfix41_41_2 Q2.hinj41_41_2
      Q2.hcardT41_41_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T41_41_2 i) (Q2.hfix41_41_2 i) _)
      ?_).symm
  rw [show colData1 (⟨41, by decide⟩ : Fin 148)
        ((colE1 ⟨41, by decide⟩ 1 (transLenTr ⟨41, by decide⟩ 1 hp) : ↥(reps ⟨41, by decide⟩)) : Coordinate 1)
        T41_41 = colFn colCert_41_41_1.D (m := 25) from colCert_41_41_1.bind1,
    show colData2 (⟨41, by decide⟩ : Fin 148)
        ((colE2 ⟨41, by decide⟩ 1 hp : ↥(Q2.reps ⟨41, by decide⟩)) : Coordinate 2)
        Q2.T41_41_2 = colFn colCert_41_41_1.D (m := 25) from colCert_41_41_1.bind2]
  exact alnAll_41_41_1 j hj hq

end LeanDring.P5Presentation
