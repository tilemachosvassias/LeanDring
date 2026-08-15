/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Data.ColCdd.C041
import LeanDring.P5.Data.ColRestCheap.C194
import LeanDring.P5.Data.ColRestCheap.C195
import LeanDring.P5.Data.ColRestCheap.C196
import LeanDring.P5.Data.ColRestCheap.C197
import LeanDring.P5.Data.ColRestCheap.C009
import LeanDring.P5.Data.EntryK.C023
import LeanDring.P5.Data.EntryK.C022
import LeanDring.P5.Certificate.RingIsomorphism.MatchCore
import LeanDring.P5.Data.SpeciesAlign.C024
import LeanDring.P5.Data.SpeciesDiv.C056
import LeanDring.P5.Data.SpeciesDiv.C057
import LeanDring.P5.Data.SpeciesDiv.C058

/-! # Stage-5 leaves, chunk 18 (auto-emitted).  -/

namespace LeanDring.P5Presentation

open MulAction Finset LeanDring.DRing LeanDring.MonGSet

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.style.longLine false

theorem leaf_95_95_3 (hp : 3 < (Q2.transData.getD 95 []).length)
    (j : Nat) (hj : j < (repChars.getD 95 []).length)
    (hq : (normIsRep.getD 95 []).getD j false = true) :
    species (Q2.reps (⟨95, by decide⟩ : Fin 148)) (colE2 ⟨95, by decide⟩ 3 hp)
        (rowE2 (⟨95, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨95, by decide⟩ : Fin 148))
        (colE1 ⟨95, by decide⟩ 3 (transLenTr ⟨95, by decide⟩ 3 hp))
        (rowE1 (⟨95, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨95, by decide⟩ : Fin 148) ⟨95, by decide⟩ _
      (validAt ⟨95, by decide⟩ (listedAt ⟨95, by decide⟩ hj))
      (colE1 ⟨95, by decide⟩ 3 (transLenTr ⟨95, by decide⟩ 3 hp)) T95_95
      hfix95_95 hinj95_95 hcardT95_95
      (fun i => conj_mem_of_fixedPoints _ _ (T95_95 i) (hfix95_95 i) _)
      ⟨95, by decide⟩ ⟨95, by decide⟩ _
      (Q2.validAt ⟨95, by decide⟩ (Q2.listedAt ⟨95, by decide⟩
        (alnCheck_rep ⟨95, by decide⟩ hj hq).1))
      (colE2 ⟨95, by decide⟩ 3 hp) Q2.T95_95_2 Q2.hfix95_95_2 Q2.hinj95_95_2
      Q2.hcardT95_95_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T95_95_2 i) (Q2.hfix95_95_2 i) _)
      ?_).symm
  rw [show colData1 (⟨95, by decide⟩ : Fin 148)
        ((colE1 ⟨95, by decide⟩ 3 (transLenTr ⟨95, by decide⟩ 3 hp) : ↥(reps ⟨95, by decide⟩)) : Coordinate 1)
        T95_95 = colFn colCert_95_95_3.D (m := 25) from colCert_95_95_3.bind1,
    show colData2 (⟨95, by decide⟩ : Fin 148)
        ((colE2 ⟨95, by decide⟩ 3 hp : ↥(Q2.reps ⟨95, by decide⟩)) : Coordinate 2)
        Q2.T95_95_2 = colFn colCert_95_95_3.D (m := 25) from colCert_95_95_3.bind2]
  exact alnAll_95_95_3 j hj hq

theorem leaf_95_95_4 (hp : 4 < (Q2.transData.getD 95 []).length)
    (j : Nat) (hj : j < (repChars.getD 95 []).length)
    (hq : (normIsRep.getD 95 []).getD j false = true) :
    species (Q2.reps (⟨95, by decide⟩ : Fin 148)) (colE2 ⟨95, by decide⟩ 4 hp)
        (rowE2 (⟨95, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨95, by decide⟩ : Fin 148))
        (colE1 ⟨95, by decide⟩ 4 (transLenTr ⟨95, by decide⟩ 4 hp))
        (rowE1 (⟨95, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨95, by decide⟩ : Fin 148) ⟨95, by decide⟩ _
      (validAt ⟨95, by decide⟩ (listedAt ⟨95, by decide⟩ hj))
      (colE1 ⟨95, by decide⟩ 4 (transLenTr ⟨95, by decide⟩ 4 hp)) T95_95
      hfix95_95 hinj95_95 hcardT95_95
      (fun i => conj_mem_of_fixedPoints _ _ (T95_95 i) (hfix95_95 i) _)
      ⟨95, by decide⟩ ⟨95, by decide⟩ _
      (Q2.validAt ⟨95, by decide⟩ (Q2.listedAt ⟨95, by decide⟩
        (alnCheck_rep ⟨95, by decide⟩ hj hq).1))
      (colE2 ⟨95, by decide⟩ 4 hp) Q2.T95_95_2 Q2.hfix95_95_2 Q2.hinj95_95_2
      Q2.hcardT95_95_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T95_95_2 i) (Q2.hfix95_95_2 i) _)
      ?_).symm
  rw [show colData1 (⟨95, by decide⟩ : Fin 148)
        ((colE1 ⟨95, by decide⟩ 4 (transLenTr ⟨95, by decide⟩ 4 hp) : ↥(reps ⟨95, by decide⟩)) : Coordinate 1)
        T95_95 = colFn colCert_95_95_4.D (m := 25) from colCert_95_95_4.bind1,
    show colData2 (⟨95, by decide⟩ : Fin 148)
        ((colE2 ⟨95, by decide⟩ 4 hp : ↥(Q2.reps ⟨95, by decide⟩)) : Coordinate 2)
        Q2.T95_95_2 = colFn colCert_95_95_4.D (m := 25) from colCert_95_95_4.bind2]
  exact alnAll_95_95_4 j hj hq

theorem leaf_95_95_5 (hp : 5 < (Q2.transData.getD 95 []).length)
    (j : Nat) (hj : j < (repChars.getD 95 []).length)
    (hq : (normIsRep.getD 95 []).getD j false = true) :
    species (Q2.reps (⟨95, by decide⟩ : Fin 148)) (colE2 ⟨95, by decide⟩ 5 hp)
        (rowE2 (⟨95, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨95, by decide⟩ : Fin 148))
        (colE1 ⟨95, by decide⟩ 5 (transLenTr ⟨95, by decide⟩ 5 hp))
        (rowE1 (⟨95, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨95, by decide⟩ : Fin 148) ⟨95, by decide⟩ _
      (validAt ⟨95, by decide⟩ (listedAt ⟨95, by decide⟩ hj))
      (colE1 ⟨95, by decide⟩ 5 (transLenTr ⟨95, by decide⟩ 5 hp)) T95_95
      hfix95_95 hinj95_95 hcardT95_95
      (fun i => conj_mem_of_fixedPoints _ _ (T95_95 i) (hfix95_95 i) _)
      ⟨95, by decide⟩ ⟨95, by decide⟩ _
      (Q2.validAt ⟨95, by decide⟩ (Q2.listedAt ⟨95, by decide⟩
        (alnCheck_rep ⟨95, by decide⟩ hj hq).1))
      (colE2 ⟨95, by decide⟩ 5 hp) Q2.T95_95_2 Q2.hfix95_95_2 Q2.hinj95_95_2
      Q2.hcardT95_95_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T95_95_2 i) (Q2.hfix95_95_2 i) _)
      ?_).symm
  rw [show colData1 (⟨95, by decide⟩ : Fin 148)
        ((colE1 ⟨95, by decide⟩ 5 (transLenTr ⟨95, by decide⟩ 5 hp) : ↥(reps ⟨95, by decide⟩)) : Coordinate 1)
        T95_95 = colFn colCert_95_95_5.D (m := 25) from colCert_95_95_5.bind1,
    show colData2 (⟨95, by decide⟩ : Fin 148)
        ((colE2 ⟨95, by decide⟩ 5 hp : ↥(Q2.reps ⟨95, by decide⟩)) : Coordinate 2)
        Q2.T95_95_2 = colFn colCert_95_95_5.D (m := 25) from colCert_95_95_5.bind2]
  exact alnAll_95_95_5 j hj hq

theorem leaf_95_95_10 (hp : 10 < (Q2.transData.getD 95 []).length)
    (j : Nat) (hj : j < (repChars.getD 95 []).length)
    (hq : (normIsRep.getD 95 []).getD j false = true) :
    species (Q2.reps (⟨95, by decide⟩ : Fin 148)) (colE2 ⟨95, by decide⟩ 10 hp)
        (rowE2 (⟨95, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨95, by decide⟩ : Fin 148))
        (colE1 ⟨95, by decide⟩ 10 (transLenTr ⟨95, by decide⟩ 10 hp))
        (rowE1 (⟨95, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨95, by decide⟩ : Fin 148) ⟨95, by decide⟩ _
      (validAt ⟨95, by decide⟩ (listedAt ⟨95, by decide⟩ hj))
      (colE1 ⟨95, by decide⟩ 10 (transLenTr ⟨95, by decide⟩ 10 hp)) T95_95
      hfix95_95 hinj95_95 hcardT95_95
      (fun i => conj_mem_of_fixedPoints _ _ (T95_95 i) (hfix95_95 i) _)
      ⟨95, by decide⟩ ⟨95, by decide⟩ _
      (Q2.validAt ⟨95, by decide⟩ (Q2.listedAt ⟨95, by decide⟩
        (alnCheck_rep ⟨95, by decide⟩ hj hq).1))
      (colE2 ⟨95, by decide⟩ 10 hp) Q2.T95_95_2 Q2.hfix95_95_2 Q2.hinj95_95_2
      Q2.hcardT95_95_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T95_95_2 i) (Q2.hfix95_95_2 i) _)
      ?_).symm
  rw [show colData1 (⟨95, by decide⟩ : Fin 148)
        ((colE1 ⟨95, by decide⟩ 10 (transLenTr ⟨95, by decide⟩ 10 hp) : ↥(reps ⟨95, by decide⟩)) : Coordinate 1)
        T95_95 = colFn colCert_95_95_10.D (m := 25) from colCert_95_95_10.bind1,
    show colData2 (⟨95, by decide⟩ : Fin 148)
        ((colE2 ⟨95, by decide⟩ 10 hp : ↥(Q2.reps ⟨95, by decide⟩)) : Coordinate 2)
        Q2.T95_95_2 = colFn colCert_95_95_10.D (m := 25) from colCert_95_95_10.bind2]
  exact alnAll_95_95_10 j hj hq

theorem leaf_95_95_15 (hp : 15 < (Q2.transData.getD 95 []).length)
    (j : Nat) (hj : j < (repChars.getD 95 []).length)
    (hq : (normIsRep.getD 95 []).getD j false = true) :
    species (Q2.reps (⟨95, by decide⟩ : Fin 148)) (colE2 ⟨95, by decide⟩ 15 hp)
        (rowE2 (⟨95, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨95, by decide⟩ : Fin 148))
        (colE1 ⟨95, by decide⟩ 15 (transLenTr ⟨95, by decide⟩ 15 hp))
        (rowE1 (⟨95, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨95, by decide⟩ : Fin 148) ⟨95, by decide⟩ _
      (validAt ⟨95, by decide⟩ (listedAt ⟨95, by decide⟩ hj))
      (colE1 ⟨95, by decide⟩ 15 (transLenTr ⟨95, by decide⟩ 15 hp)) T95_95
      hfix95_95 hinj95_95 hcardT95_95
      (fun i => conj_mem_of_fixedPoints _ _ (T95_95 i) (hfix95_95 i) _)
      ⟨95, by decide⟩ ⟨95, by decide⟩ _
      (Q2.validAt ⟨95, by decide⟩ (Q2.listedAt ⟨95, by decide⟩
        (alnCheck_rep ⟨95, by decide⟩ hj hq).1))
      (colE2 ⟨95, by decide⟩ 15 hp) Q2.T95_95_2 Q2.hfix95_95_2 Q2.hinj95_95_2
      Q2.hcardT95_95_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T95_95_2 i) (Q2.hfix95_95_2 i) _)
      ?_).symm
  rw [show colData1 (⟨95, by decide⟩ : Fin 148)
        ((colE1 ⟨95, by decide⟩ 15 (transLenTr ⟨95, by decide⟩ 15 hp) : ↥(reps ⟨95, by decide⟩)) : Coordinate 1)
        T95_95 = colFn colCert_95_95_15.D (m := 25) from colCert_95_95_15.bind1,
    show colData2 (⟨95, by decide⟩ : Fin 148)
        ((colE2 ⟨95, by decide⟩ 15 hp : ↥(Q2.reps ⟨95, by decide⟩)) : Coordinate 2)
        Q2.T95_95_2 = colFn colCert_95_95_15.D (m := 25) from colCert_95_95_15.bind2]
  exact alnAll_95_95_15 j hj hq

theorem leaf_95_95_20 (hp : 20 < (Q2.transData.getD 95 []).length)
    (j : Nat) (hj : j < (repChars.getD 95 []).length)
    (hq : (normIsRep.getD 95 []).getD j false = true) :
    species (Q2.reps (⟨95, by decide⟩ : Fin 148)) (colE2 ⟨95, by decide⟩ 20 hp)
        (rowE2 (⟨95, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨95, by decide⟩ : Fin 148))
        (colE1 ⟨95, by decide⟩ 20 (transLenTr ⟨95, by decide⟩ 20 hp))
        (rowE1 (⟨95, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨95, by decide⟩ : Fin 148) ⟨95, by decide⟩ _
      (validAt ⟨95, by decide⟩ (listedAt ⟨95, by decide⟩ hj))
      (colE1 ⟨95, by decide⟩ 20 (transLenTr ⟨95, by decide⟩ 20 hp)) T95_95
      hfix95_95 hinj95_95 hcardT95_95
      (fun i => conj_mem_of_fixedPoints _ _ (T95_95 i) (hfix95_95 i) _)
      ⟨95, by decide⟩ ⟨95, by decide⟩ _
      (Q2.validAt ⟨95, by decide⟩ (Q2.listedAt ⟨95, by decide⟩
        (alnCheck_rep ⟨95, by decide⟩ hj hq).1))
      (colE2 ⟨95, by decide⟩ 20 hp) Q2.T95_95_2 Q2.hfix95_95_2 Q2.hinj95_95_2
      Q2.hcardT95_95_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T95_95_2 i) (Q2.hfix95_95_2 i) _)
      ?_).symm
  rw [show colData1 (⟨95, by decide⟩ : Fin 148)
        ((colE1 ⟨95, by decide⟩ 20 (transLenTr ⟨95, by decide⟩ 20 hp) : ↥(reps ⟨95, by decide⟩)) : Coordinate 1)
        T95_95 = colFn colCert_95_95_20.D (m := 25) from colCert_95_95_20.bind1,
    show colData2 (⟨95, by decide⟩ : Fin 148)
        ((colE2 ⟨95, by decide⟩ 20 hp : ↥(Q2.reps ⟨95, by decide⟩)) : Coordinate 2)
        Q2.T95_95_2 = colFn colCert_95_95_20.D (m := 25) from colCert_95_95_20.bind2]
  exact alnAll_95_95_20 j hj hq

theorem leaf_95_95_25 (hp : 25 < (Q2.transData.getD 95 []).length)
    (j : Nat) (hj : j < (repChars.getD 95 []).length)
    (hq : (normIsRep.getD 95 []).getD j false = true) :
    species (Q2.reps (⟨95, by decide⟩ : Fin 148)) (colE2 ⟨95, by decide⟩ 25 hp)
        (rowE2 (⟨95, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨95, by decide⟩ : Fin 148))
        (colE1 ⟨95, by decide⟩ 25 (transLenTr ⟨95, by decide⟩ 25 hp))
        (rowE1 (⟨95, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨95, by decide⟩ : Fin 148) ⟨95, by decide⟩ _
      (validAt ⟨95, by decide⟩ (listedAt ⟨95, by decide⟩ hj))
      (colE1 ⟨95, by decide⟩ 25 (transLenTr ⟨95, by decide⟩ 25 hp)) T95_95
      hfix95_95 hinj95_95 hcardT95_95
      (fun i => conj_mem_of_fixedPoints _ _ (T95_95 i) (hfix95_95 i) _)
      ⟨95, by decide⟩ ⟨95, by decide⟩ _
      (Q2.validAt ⟨95, by decide⟩ (Q2.listedAt ⟨95, by decide⟩
        (alnCheck_rep ⟨95, by decide⟩ hj hq).1))
      (colE2 ⟨95, by decide⟩ 25 hp) Q2.T95_95_2 Q2.hfix95_95_2 Q2.hinj95_95_2
      Q2.hcardT95_95_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T95_95_2 i) (Q2.hfix95_95_2 i) _)
      ?_).symm
  rw [show colData1 (⟨95, by decide⟩ : Fin 148)
        ((colE1 ⟨95, by decide⟩ 25 (transLenTr ⟨95, by decide⟩ 25 hp) : ↥(reps ⟨95, by decide⟩)) : Coordinate 1)
        T95_95 = colFn colCert_95_95_25.D (m := 25) from colCert_95_95_25.bind1,
    show colData2 (⟨95, by decide⟩ : Fin 148)
        ((colE2 ⟨95, by decide⟩ 25 hp : ↥(Q2.reps ⟨95, by decide⟩)) : Coordinate 2)
        Q2.T95_95_2 = colFn colCert_95_95_25.D (m := 25) from colCert_95_95_25.bind2]
  exact alnAll_95_95_25 j hj hq

theorem leaf_95_95_50 (hp : 50 < (Q2.transData.getD 95 []).length)
    (j : Nat) (hj : j < (repChars.getD 95 []).length)
    (hq : (normIsRep.getD 95 []).getD j false = true) :
    species (Q2.reps (⟨95, by decide⟩ : Fin 148)) (colE2 ⟨95, by decide⟩ 50 hp)
        (rowE2 (⟨95, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨95, by decide⟩ : Fin 148))
        (colE1 ⟨95, by decide⟩ 50 (transLenTr ⟨95, by decide⟩ 50 hp))
        (rowE1 (⟨95, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨95, by decide⟩ : Fin 148) ⟨95, by decide⟩ _
      (validAt ⟨95, by decide⟩ (listedAt ⟨95, by decide⟩ hj))
      (colE1 ⟨95, by decide⟩ 50 (transLenTr ⟨95, by decide⟩ 50 hp)) T95_95
      hfix95_95 hinj95_95 hcardT95_95
      (fun i => conj_mem_of_fixedPoints _ _ (T95_95 i) (hfix95_95 i) _)
      ⟨95, by decide⟩ ⟨95, by decide⟩ _
      (Q2.validAt ⟨95, by decide⟩ (Q2.listedAt ⟨95, by decide⟩
        (alnCheck_rep ⟨95, by decide⟩ hj hq).1))
      (colE2 ⟨95, by decide⟩ 50 hp) Q2.T95_95_2 Q2.hfix95_95_2 Q2.hinj95_95_2
      Q2.hcardT95_95_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T95_95_2 i) (Q2.hfix95_95_2 i) _)
      ?_).symm
  rw [show colData1 (⟨95, by decide⟩ : Fin 148)
        ((colE1 ⟨95, by decide⟩ 50 (transLenTr ⟨95, by decide⟩ 50 hp) : ↥(reps ⟨95, by decide⟩)) : Coordinate 1)
        T95_95 = colFn colCert_95_95_50.D (m := 25) from colCert_95_95_50.bind1,
    show colData2 (⟨95, by decide⟩ : Fin 148)
        ((colE2 ⟨95, by decide⟩ 50 hp : ↥(Q2.reps ⟨95, by decide⟩)) : Coordinate 2)
        Q2.T95_95_2 = colFn colCert_95_95_50.D (m := 25) from colCert_95_95_50.bind2]
  exact alnAll_95_95_50 j hj hq

theorem leaf_95_95_75 (hp : 75 < (Q2.transData.getD 95 []).length)
    (j : Nat) (hj : j < (repChars.getD 95 []).length)
    (hq : (normIsRep.getD 95 []).getD j false = true) :
    species (Q2.reps (⟨95, by decide⟩ : Fin 148)) (colE2 ⟨95, by decide⟩ 75 hp)
        (rowE2 (⟨95, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨95, by decide⟩ : Fin 148))
        (colE1 ⟨95, by decide⟩ 75 (transLenTr ⟨95, by decide⟩ 75 hp))
        (rowE1 (⟨95, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨95, by decide⟩ : Fin 148) ⟨95, by decide⟩ _
      (validAt ⟨95, by decide⟩ (listedAt ⟨95, by decide⟩ hj))
      (colE1 ⟨95, by decide⟩ 75 (transLenTr ⟨95, by decide⟩ 75 hp)) T95_95
      hfix95_95 hinj95_95 hcardT95_95
      (fun i => conj_mem_of_fixedPoints _ _ (T95_95 i) (hfix95_95 i) _)
      ⟨95, by decide⟩ ⟨95, by decide⟩ _
      (Q2.validAt ⟨95, by decide⟩ (Q2.listedAt ⟨95, by decide⟩
        (alnCheck_rep ⟨95, by decide⟩ hj hq).1))
      (colE2 ⟨95, by decide⟩ 75 hp) Q2.T95_95_2 Q2.hfix95_95_2 Q2.hinj95_95_2
      Q2.hcardT95_95_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T95_95_2 i) (Q2.hfix95_95_2 i) _)
      ?_).symm
  rw [show colData1 (⟨95, by decide⟩ : Fin 148)
        ((colE1 ⟨95, by decide⟩ 75 (transLenTr ⟨95, by decide⟩ 75 hp) : ↥(reps ⟨95, by decide⟩)) : Coordinate 1)
        T95_95 = colFn colCert_95_95_75.D (m := 25) from colCert_95_95_75.bind1,
    show colData2 (⟨95, by decide⟩ : Fin 148)
        ((colE2 ⟨95, by decide⟩ 75 hp : ↥(Q2.reps ⟨95, by decide⟩)) : Coordinate 2)
        Q2.T95_95_2 = colFn colCert_95_95_75.D (m := 25) from colCert_95_95_75.bind2]
  exact alnAll_95_95_75 j hj hq

theorem leaf_95_95_100 (hp : 100 < (Q2.transData.getD 95 []).length)
    (j : Nat) (hj : j < (repChars.getD 95 []).length)
    (hq : (normIsRep.getD 95 []).getD j false = true) :
    species (Q2.reps (⟨95, by decide⟩ : Fin 148)) (colE2 ⟨95, by decide⟩ 100 hp)
        (rowE2 (⟨95, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨95, by decide⟩ : Fin 148))
        (colE1 ⟨95, by decide⟩ 100 (transLenTr ⟨95, by decide⟩ 100 hp))
        (rowE1 (⟨95, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨95, by decide⟩ : Fin 148) ⟨95, by decide⟩ _
      (validAt ⟨95, by decide⟩ (listedAt ⟨95, by decide⟩ hj))
      (colE1 ⟨95, by decide⟩ 100 (transLenTr ⟨95, by decide⟩ 100 hp)) T95_95
      hfix95_95 hinj95_95 hcardT95_95
      (fun i => conj_mem_of_fixedPoints _ _ (T95_95 i) (hfix95_95 i) _)
      ⟨95, by decide⟩ ⟨95, by decide⟩ _
      (Q2.validAt ⟨95, by decide⟩ (Q2.listedAt ⟨95, by decide⟩
        (alnCheck_rep ⟨95, by decide⟩ hj hq).1))
      (colE2 ⟨95, by decide⟩ 100 hp) Q2.T95_95_2 Q2.hfix95_95_2 Q2.hinj95_95_2
      Q2.hcardT95_95_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T95_95_2 i) (Q2.hfix95_95_2 i) _)
      ?_).symm
  rw [show colData1 (⟨95, by decide⟩ : Fin 148)
        ((colE1 ⟨95, by decide⟩ 100 (transLenTr ⟨95, by decide⟩ 100 hp) : ↥(reps ⟨95, by decide⟩)) : Coordinate 1)
        T95_95 = colFn colCert_95_95_100.D (m := 25) from colCert_95_95_100.bind1,
    show colData2 (⟨95, by decide⟩ : Fin 148)
        ((colE2 ⟨95, by decide⟩ 100 hp : ↥(Q2.reps ⟨95, by decide⟩)) : Coordinate 2)
        Q2.T95_95_2 = colFn colCert_95_95_100.D (m := 25) from colCert_95_95_100.bind2]
  exact alnAll_95_95_100 j hj hq

theorem leaf_96_10_0 (hp : 0 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 96 []).length)
    (hq : (normIsRep.getD 96 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 0 hp)
        (rowE2 (⟨96, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 0 (transLenTr ⟨10, by decide⟩ 0 hp))
        (rowE1 (⟨96, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨96, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨96, by decide⟩ (listedAt ⟨96, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 0 (transLenTr ⟨10, by decide⟩ 0 hp)) T96_10
      hfix96_10 hinj96_10 hcardT96_10
      (fun i => conj_mem_of_fixedPoints _ _ (T96_10 i) (hfix96_10 i) _)
      ⟨96, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨96, by decide⟩ (Q2.listedAt ⟨96, by decide⟩
        (alnCheck_rep ⟨96, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 0 hp) Q2.T96_10_2 Q2.hfix96_10_2 Q2.hinj96_10_2
      Q2.hcardT96_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T96_10_2 i) (Q2.hfix96_10_2 i) _)
      colCert_96_10_0.hD ?_).symm
  rw [alnId_96 j hj]


theorem leaf_96_10_1 (hp : 1 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 96 []).length)
    (hq : (normIsRep.getD 96 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 1 hp)
        (rowE2 (⟨96, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 1 (transLenTr ⟨10, by decide⟩ 1 hp))
        (rowE1 (⟨96, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨96, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨96, by decide⟩ (listedAt ⟨96, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 1 (transLenTr ⟨10, by decide⟩ 1 hp)) T96_10
      hfix96_10 hinj96_10 hcardT96_10
      (fun i => conj_mem_of_fixedPoints _ _ (T96_10 i) (hfix96_10 i) _)
      ⟨96, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨96, by decide⟩ (Q2.listedAt ⟨96, by decide⟩
        (alnCheck_rep ⟨96, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 1 hp) Q2.T96_10_2 Q2.hfix96_10_2 Q2.hinj96_10_2
      Q2.hcardT96_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T96_10_2 i) (Q2.hfix96_10_2 i) _)
      colCert_96_10_1.hD ?_).symm
  rw [alnId_96 j hj]


theorem leaf_96_10_2 (hp : 2 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 96 []).length)
    (hq : (normIsRep.getD 96 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 2 hp)
        (rowE2 (⟨96, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 2 (transLenTr ⟨10, by decide⟩ 2 hp))
        (rowE1 (⟨96, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨96, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨96, by decide⟩ (listedAt ⟨96, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 2 (transLenTr ⟨10, by decide⟩ 2 hp)) T96_10
      hfix96_10 hinj96_10 hcardT96_10
      (fun i => conj_mem_of_fixedPoints _ _ (T96_10 i) (hfix96_10 i) _)
      ⟨96, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨96, by decide⟩ (Q2.listedAt ⟨96, by decide⟩
        (alnCheck_rep ⟨96, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 2 hp) Q2.T96_10_2 Q2.hfix96_10_2 Q2.hinj96_10_2
      Q2.hcardT96_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T96_10_2 i) (Q2.hfix96_10_2 i) _)
      colCert_96_10_2.hD ?_).symm
  rw [alnId_96 j hj]


theorem leaf_96_10_3 (hp : 3 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 96 []).length)
    (hq : (normIsRep.getD 96 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 3 hp)
        (rowE2 (⟨96, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 3 (transLenTr ⟨10, by decide⟩ 3 hp))
        (rowE1 (⟨96, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨96, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨96, by decide⟩ (listedAt ⟨96, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 3 (transLenTr ⟨10, by decide⟩ 3 hp)) T96_10
      hfix96_10 hinj96_10 hcardT96_10
      (fun i => conj_mem_of_fixedPoints _ _ (T96_10 i) (hfix96_10 i) _)
      ⟨96, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨96, by decide⟩ (Q2.listedAt ⟨96, by decide⟩
        (alnCheck_rep ⟨96, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 3 hp) Q2.T96_10_2 Q2.hfix96_10_2 Q2.hinj96_10_2
      Q2.hcardT96_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T96_10_2 i) (Q2.hfix96_10_2 i) _)
      colCert_96_10_3.hD ?_).symm
  rw [alnId_96 j hj]


theorem leaf_96_10_4 (hp : 4 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 96 []).length)
    (hq : (normIsRep.getD 96 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 4 hp)
        (rowE2 (⟨96, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 4 (transLenTr ⟨10, by decide⟩ 4 hp))
        (rowE1 (⟨96, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨96, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨96, by decide⟩ (listedAt ⟨96, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 4 (transLenTr ⟨10, by decide⟩ 4 hp)) T96_10
      hfix96_10 hinj96_10 hcardT96_10
      (fun i => conj_mem_of_fixedPoints _ _ (T96_10 i) (hfix96_10 i) _)
      ⟨96, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨96, by decide⟩ (Q2.listedAt ⟨96, by decide⟩
        (alnCheck_rep ⟨96, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 4 hp) Q2.T96_10_2 Q2.hfix96_10_2 Q2.hinj96_10_2
      Q2.hcardT96_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T96_10_2 i) (Q2.hfix96_10_2 i) _)
      colCert_96_10_4.hD ?_).symm
  rw [alnId_96 j hj]


theorem leaf_96_12_0 (hp : 0 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 96 []).length)
    (hq : (normIsRep.getD 96 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 0 hp)
        (rowE2 (⟨96, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp))
        (rowE1 (⟨96, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨96, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨96, by decide⟩ (listedAt ⟨96, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp)) T96_12
      hfix96_12 hinj96_12 hcardT96_12
      (fun i => conj_mem_of_fixedPoints _ _ (T96_12 i) (hfix96_12 i) _)
      ⟨96, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨96, by decide⟩ (Q2.listedAt ⟨96, by decide⟩
        (alnCheck_rep ⟨96, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 0 hp) Q2.T96_12_2 Q2.hfix96_12_2 Q2.hinj96_12_2
      Q2.hcardT96_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T96_12_2 i) (Q2.hfix96_12_2 i) _)
      colCert_96_12_0.hD ?_).symm
  rw [alnId_96 j hj]


theorem leaf_96_12_1 (hp : 1 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 96 []).length)
    (hq : (normIsRep.getD 96 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 1 hp)
        (rowE2 (⟨96, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp))
        (rowE1 (⟨96, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨96, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨96, by decide⟩ (listedAt ⟨96, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp)) T96_12
      hfix96_12 hinj96_12 hcardT96_12
      (fun i => conj_mem_of_fixedPoints _ _ (T96_12 i) (hfix96_12 i) _)
      ⟨96, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨96, by decide⟩ (Q2.listedAt ⟨96, by decide⟩
        (alnCheck_rep ⟨96, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 1 hp) Q2.T96_12_2 Q2.hfix96_12_2 Q2.hinj96_12_2
      Q2.hcardT96_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T96_12_2 i) (Q2.hfix96_12_2 i) _)
      colCert_96_12_1.hD ?_).symm
  rw [alnId_96 j hj]


theorem leaf_96_12_2 (hp : 2 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 96 []).length)
    (hq : (normIsRep.getD 96 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 2 hp)
        (rowE2 (⟨96, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp))
        (rowE1 (⟨96, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨96, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨96, by decide⟩ (listedAt ⟨96, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp)) T96_12
      hfix96_12 hinj96_12 hcardT96_12
      (fun i => conj_mem_of_fixedPoints _ _ (T96_12 i) (hfix96_12 i) _)
      ⟨96, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨96, by decide⟩ (Q2.listedAt ⟨96, by decide⟩
        (alnCheck_rep ⟨96, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 2 hp) Q2.T96_12_2 Q2.hfix96_12_2 Q2.hinj96_12_2
      Q2.hcardT96_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T96_12_2 i) (Q2.hfix96_12_2 i) _)
      colCert_96_12_2.hD ?_).symm
  rw [alnId_96 j hj]


theorem leaf_96_12_3 (hp : 3 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 96 []).length)
    (hq : (normIsRep.getD 96 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 3 hp)
        (rowE2 (⟨96, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp))
        (rowE1 (⟨96, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨96, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨96, by decide⟩ (listedAt ⟨96, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp)) T96_12
      hfix96_12 hinj96_12 hcardT96_12
      (fun i => conj_mem_of_fixedPoints _ _ (T96_12 i) (hfix96_12 i) _)
      ⟨96, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨96, by decide⟩ (Q2.listedAt ⟨96, by decide⟩
        (alnCheck_rep ⟨96, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 3 hp) Q2.T96_12_2 Q2.hfix96_12_2 Q2.hinj96_12_2
      Q2.hcardT96_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T96_12_2 i) (Q2.hfix96_12_2 i) _)
      colCert_96_12_3.hD ?_).symm
  rw [alnId_96 j hj]


theorem leaf_96_12_4 (hp : 4 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 96 []).length)
    (hq : (normIsRep.getD 96 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 4 hp)
        (rowE2 (⟨96, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp))
        (rowE1 (⟨96, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨96, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨96, by decide⟩ (listedAt ⟨96, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp)) T96_12
      hfix96_12 hinj96_12 hcardT96_12
      (fun i => conj_mem_of_fixedPoints _ _ (T96_12 i) (hfix96_12 i) _)
      ⟨96, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨96, by decide⟩ (Q2.listedAt ⟨96, by decide⟩
        (alnCheck_rep ⟨96, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 4 hp) Q2.T96_12_2 Q2.hfix96_12_2 Q2.hinj96_12_2
      Q2.hcardT96_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T96_12_2 i) (Q2.hfix96_12_2 i) _)
      colCert_96_12_4.hD ?_).symm
  rw [alnId_96 j hj]


theorem leaf_96_34_0 (hp : 0 < (Q2.transData.getD 34 []).length)
    (j : Nat) (hj : j < (repChars.getD 96 []).length)
    (hq : (normIsRep.getD 96 []).getD j false = true) :
    species (Q2.reps (⟨34, by decide⟩ : Fin 148)) (colE2 ⟨34, by decide⟩ 0 hp)
        (rowE2 (⟨96, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨34, by decide⟩ : Fin 148))
        (colE1 ⟨34, by decide⟩ 0 (transLenTr ⟨34, by decide⟩ 0 hp))
        (rowE1 (⟨96, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨96, by decide⟩ : Fin 148) ⟨34, by decide⟩ _
      (validAt ⟨96, by decide⟩ (listedAt ⟨96, by decide⟩ hj))
      (colE1 ⟨34, by decide⟩ 0 (transLenTr ⟨34, by decide⟩ 0 hp)) T96_34
      hfix96_34 hinj96_34 hcardT96_34
      (fun i => conj_mem_of_fixedPoints _ _ (T96_34 i) (hfix96_34 i) _)
      ⟨96, by decide⟩ ⟨34, by decide⟩ _
      (Q2.validAt ⟨96, by decide⟩ (Q2.listedAt ⟨96, by decide⟩
        (alnCheck_rep ⟨96, by decide⟩ hj hq).1))
      (colE2 ⟨34, by decide⟩ 0 hp) Q2.T96_34_2 Q2.hfix96_34_2 Q2.hinj96_34_2
      Q2.hcardT96_34_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T96_34_2 i) (Q2.hfix96_34_2 i) _)
      colCert_96_34_0.hD ?_).symm
  rw [alnId_96 j hj]


theorem leaf_96_34_1 (hp : 1 < (Q2.transData.getD 34 []).length)
    (j : Nat) (hj : j < (repChars.getD 96 []).length)
    (hq : (normIsRep.getD 96 []).getD j false = true) :
    species (Q2.reps (⟨34, by decide⟩ : Fin 148)) (colE2 ⟨34, by decide⟩ 1 hp)
        (rowE2 (⟨96, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨34, by decide⟩ : Fin 148))
        (colE1 ⟨34, by decide⟩ 1 (transLenTr ⟨34, by decide⟩ 1 hp))
        (rowE1 (⟨96, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨96, by decide⟩ : Fin 148) ⟨34, by decide⟩ _
      (validAt ⟨96, by decide⟩ (listedAt ⟨96, by decide⟩ hj))
      (colE1 ⟨34, by decide⟩ 1 (transLenTr ⟨34, by decide⟩ 1 hp)) T96_34
      hfix96_34 hinj96_34 hcardT96_34
      (fun i => conj_mem_of_fixedPoints _ _ (T96_34 i) (hfix96_34 i) _)
      ⟨96, by decide⟩ ⟨34, by decide⟩ _
      (Q2.validAt ⟨96, by decide⟩ (Q2.listedAt ⟨96, by decide⟩
        (alnCheck_rep ⟨96, by decide⟩ hj hq).1))
      (colE2 ⟨34, by decide⟩ 1 hp) Q2.T96_34_2 Q2.hfix96_34_2 Q2.hinj96_34_2
      Q2.hcardT96_34_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T96_34_2 i) (Q2.hfix96_34_2 i) _)
      colCert_96_34_1.hD ?_).symm
  rw [alnId_96 j hj]


theorem leaf_96_34_2 (hp : 2 < (Q2.transData.getD 34 []).length)
    (j : Nat) (hj : j < (repChars.getD 96 []).length)
    (hq : (normIsRep.getD 96 []).getD j false = true) :
    species (Q2.reps (⟨34, by decide⟩ : Fin 148)) (colE2 ⟨34, by decide⟩ 2 hp)
        (rowE2 (⟨96, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨34, by decide⟩ : Fin 148))
        (colE1 ⟨34, by decide⟩ 2 (transLenTr ⟨34, by decide⟩ 2 hp))
        (rowE1 (⟨96, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨96, by decide⟩ : Fin 148) ⟨34, by decide⟩ _
      (validAt ⟨96, by decide⟩ (listedAt ⟨96, by decide⟩ hj))
      (colE1 ⟨34, by decide⟩ 2 (transLenTr ⟨34, by decide⟩ 2 hp)) T96_34
      hfix96_34 hinj96_34 hcardT96_34
      (fun i => conj_mem_of_fixedPoints _ _ (T96_34 i) (hfix96_34 i) _)
      ⟨96, by decide⟩ ⟨34, by decide⟩ _
      (Q2.validAt ⟨96, by decide⟩ (Q2.listedAt ⟨96, by decide⟩
        (alnCheck_rep ⟨96, by decide⟩ hj hq).1))
      (colE2 ⟨34, by decide⟩ 2 hp) Q2.T96_34_2 Q2.hfix96_34_2 Q2.hinj96_34_2
      Q2.hcardT96_34_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T96_34_2 i) (Q2.hfix96_34_2 i) _)
      colCert_96_34_2.hD ?_).symm
  rw [alnId_96 j hj]


theorem leaf_96_34_3 (hp : 3 < (Q2.transData.getD 34 []).length)
    (j : Nat) (hj : j < (repChars.getD 96 []).length)
    (hq : (normIsRep.getD 96 []).getD j false = true) :
    species (Q2.reps (⟨34, by decide⟩ : Fin 148)) (colE2 ⟨34, by decide⟩ 3 hp)
        (rowE2 (⟨96, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨34, by decide⟩ : Fin 148))
        (colE1 ⟨34, by decide⟩ 3 (transLenTr ⟨34, by decide⟩ 3 hp))
        (rowE1 (⟨96, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨96, by decide⟩ : Fin 148) ⟨34, by decide⟩ _
      (validAt ⟨96, by decide⟩ (listedAt ⟨96, by decide⟩ hj))
      (colE1 ⟨34, by decide⟩ 3 (transLenTr ⟨34, by decide⟩ 3 hp)) T96_34
      hfix96_34 hinj96_34 hcardT96_34
      (fun i => conj_mem_of_fixedPoints _ _ (T96_34 i) (hfix96_34 i) _)
      ⟨96, by decide⟩ ⟨34, by decide⟩ _
      (Q2.validAt ⟨96, by decide⟩ (Q2.listedAt ⟨96, by decide⟩
        (alnCheck_rep ⟨96, by decide⟩ hj hq).1))
      (colE2 ⟨34, by decide⟩ 3 hp) Q2.T96_34_2 Q2.hfix96_34_2 Q2.hinj96_34_2
      Q2.hcardT96_34_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T96_34_2 i) (Q2.hfix96_34_2 i) _)
      colCert_96_34_3.hD ?_).symm
  rw [alnId_96 j hj]


theorem leaf_96_34_4 (hp : 4 < (Q2.transData.getD 34 []).length)
    (j : Nat) (hj : j < (repChars.getD 96 []).length)
    (hq : (normIsRep.getD 96 []).getD j false = true) :
    species (Q2.reps (⟨34, by decide⟩ : Fin 148)) (colE2 ⟨34, by decide⟩ 4 hp)
        (rowE2 (⟨96, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨34, by decide⟩ : Fin 148))
        (colE1 ⟨34, by decide⟩ 4 (transLenTr ⟨34, by decide⟩ 4 hp))
        (rowE1 (⟨96, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨96, by decide⟩ : Fin 148) ⟨34, by decide⟩ _
      (validAt ⟨96, by decide⟩ (listedAt ⟨96, by decide⟩ hj))
      (colE1 ⟨34, by decide⟩ 4 (transLenTr ⟨34, by decide⟩ 4 hp)) T96_34
      hfix96_34 hinj96_34 hcardT96_34
      (fun i => conj_mem_of_fixedPoints _ _ (T96_34 i) (hfix96_34 i) _)
      ⟨96, by decide⟩ ⟨34, by decide⟩ _
      (Q2.validAt ⟨96, by decide⟩ (Q2.listedAt ⟨96, by decide⟩
        (alnCheck_rep ⟨96, by decide⟩ hj hq).1))
      (colE2 ⟨34, by decide⟩ 4 hp) Q2.T96_34_2 Q2.hfix96_34_2 Q2.hinj96_34_2
      Q2.hcardT96_34_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T96_34_2 i) (Q2.hfix96_34_2 i) _)
      colCert_96_34_4.hD ?_).symm
  rw [alnId_96 j hj]


theorem leaf_96_34_5 (hp : 5 < (Q2.transData.getD 34 []).length)
    (j : Nat) (hj : j < (repChars.getD 96 []).length)
    (hq : (normIsRep.getD 96 []).getD j false = true) :
    species (Q2.reps (⟨34, by decide⟩ : Fin 148)) (colE2 ⟨34, by decide⟩ 5 hp)
        (rowE2 (⟨96, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨34, by decide⟩ : Fin 148))
        (colE1 ⟨34, by decide⟩ 5 (transLenTr ⟨34, by decide⟩ 5 hp))
        (rowE1 (⟨96, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨96, by decide⟩ : Fin 148) ⟨34, by decide⟩ _
      (validAt ⟨96, by decide⟩ (listedAt ⟨96, by decide⟩ hj))
      (colE1 ⟨34, by decide⟩ 5 (transLenTr ⟨34, by decide⟩ 5 hp)) T96_34
      hfix96_34 hinj96_34 hcardT96_34
      (fun i => conj_mem_of_fixedPoints _ _ (T96_34 i) (hfix96_34 i) _)
      ⟨96, by decide⟩ ⟨34, by decide⟩ _
      (Q2.validAt ⟨96, by decide⟩ (Q2.listedAt ⟨96, by decide⟩
        (alnCheck_rep ⟨96, by decide⟩ hj hq).1))
      (colE2 ⟨34, by decide⟩ 5 hp) Q2.T96_34_2 Q2.hfix96_34_2 Q2.hinj96_34_2
      Q2.hcardT96_34_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T96_34_2 i) (Q2.hfix96_34_2 i) _)
      colCert_96_34_5.hD ?_).symm
  rw [alnId_96 j hj]


theorem leaf_96_34_10 (hp : 10 < (Q2.transData.getD 34 []).length)
    (j : Nat) (hj : j < (repChars.getD 96 []).length)
    (hq : (normIsRep.getD 96 []).getD j false = true) :
    species (Q2.reps (⟨34, by decide⟩ : Fin 148)) (colE2 ⟨34, by decide⟩ 10 hp)
        (rowE2 (⟨96, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨34, by decide⟩ : Fin 148))
        (colE1 ⟨34, by decide⟩ 10 (transLenTr ⟨34, by decide⟩ 10 hp))
        (rowE1 (⟨96, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨96, by decide⟩ : Fin 148) ⟨34, by decide⟩ _
      (validAt ⟨96, by decide⟩ (listedAt ⟨96, by decide⟩ hj))
      (colE1 ⟨34, by decide⟩ 10 (transLenTr ⟨34, by decide⟩ 10 hp)) T96_34
      hfix96_34 hinj96_34 hcardT96_34
      (fun i => conj_mem_of_fixedPoints _ _ (T96_34 i) (hfix96_34 i) _)
      ⟨96, by decide⟩ ⟨34, by decide⟩ _
      (Q2.validAt ⟨96, by decide⟩ (Q2.listedAt ⟨96, by decide⟩
        (alnCheck_rep ⟨96, by decide⟩ hj hq).1))
      (colE2 ⟨34, by decide⟩ 10 hp) Q2.T96_34_2 Q2.hfix96_34_2 Q2.hinj96_34_2
      Q2.hcardT96_34_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T96_34_2 i) (Q2.hfix96_34_2 i) _)
      colCert_96_34_10.hD ?_).symm
  rw [alnId_96 j hj]


theorem leaf_96_34_15 (hp : 15 < (Q2.transData.getD 34 []).length)
    (j : Nat) (hj : j < (repChars.getD 96 []).length)
    (hq : (normIsRep.getD 96 []).getD j false = true) :
    species (Q2.reps (⟨34, by decide⟩ : Fin 148)) (colE2 ⟨34, by decide⟩ 15 hp)
        (rowE2 (⟨96, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨34, by decide⟩ : Fin 148))
        (colE1 ⟨34, by decide⟩ 15 (transLenTr ⟨34, by decide⟩ 15 hp))
        (rowE1 (⟨96, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨96, by decide⟩ : Fin 148) ⟨34, by decide⟩ _
      (validAt ⟨96, by decide⟩ (listedAt ⟨96, by decide⟩ hj))
      (colE1 ⟨34, by decide⟩ 15 (transLenTr ⟨34, by decide⟩ 15 hp)) T96_34
      hfix96_34 hinj96_34 hcardT96_34
      (fun i => conj_mem_of_fixedPoints _ _ (T96_34 i) (hfix96_34 i) _)
      ⟨96, by decide⟩ ⟨34, by decide⟩ _
      (Q2.validAt ⟨96, by decide⟩ (Q2.listedAt ⟨96, by decide⟩
        (alnCheck_rep ⟨96, by decide⟩ hj hq).1))
      (colE2 ⟨34, by decide⟩ 15 hp) Q2.T96_34_2 Q2.hfix96_34_2 Q2.hinj96_34_2
      Q2.hcardT96_34_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T96_34_2 i) (Q2.hfix96_34_2 i) _)
      colCert_96_34_15.hD ?_).symm
  rw [alnId_96 j hj]


theorem leaf_96_34_20 (hp : 20 < (Q2.transData.getD 34 []).length)
    (j : Nat) (hj : j < (repChars.getD 96 []).length)
    (hq : (normIsRep.getD 96 []).getD j false = true) :
    species (Q2.reps (⟨34, by decide⟩ : Fin 148)) (colE2 ⟨34, by decide⟩ 20 hp)
        (rowE2 (⟨96, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨34, by decide⟩ : Fin 148))
        (colE1 ⟨34, by decide⟩ 20 (transLenTr ⟨34, by decide⟩ 20 hp))
        (rowE1 (⟨96, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨96, by decide⟩ : Fin 148) ⟨34, by decide⟩ _
      (validAt ⟨96, by decide⟩ (listedAt ⟨96, by decide⟩ hj))
      (colE1 ⟨34, by decide⟩ 20 (transLenTr ⟨34, by decide⟩ 20 hp)) T96_34
      hfix96_34 hinj96_34 hcardT96_34
      (fun i => conj_mem_of_fixedPoints _ _ (T96_34 i) (hfix96_34 i) _)
      ⟨96, by decide⟩ ⟨34, by decide⟩ _
      (Q2.validAt ⟨96, by decide⟩ (Q2.listedAt ⟨96, by decide⟩
        (alnCheck_rep ⟨96, by decide⟩ hj hq).1))
      (colE2 ⟨34, by decide⟩ 20 hp) Q2.T96_34_2 Q2.hfix96_34_2 Q2.hinj96_34_2
      Q2.hcardT96_34_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T96_34_2 i) (Q2.hfix96_34_2 i) _)
      colCert_96_34_20.hD ?_).symm
  rw [alnId_96 j hj]


theorem leaf_96_53_0 (hp : 0 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 96 []).length)
    (hq : (normIsRep.getD 96 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 0 hp)
        (rowE2 (⟨96, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 0 (transLenTr ⟨53, by decide⟩ 0 hp))
        (rowE1 (⟨96, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨96, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨96, by decide⟩ (listedAt ⟨96, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 0 (transLenTr ⟨53, by decide⟩ 0 hp)) T96_53
      hfix96_53 hinj96_53 hcardT96_53
      (fun i => conj_mem_of_fixedPoints _ _ (T96_53 i) (hfix96_53 i) _)
      ⟨96, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨96, by decide⟩ (Q2.listedAt ⟨96, by decide⟩
        (alnCheck_rep ⟨96, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 0 hp) Q2.T96_53_2 Q2.hfix96_53_2 Q2.hinj96_53_2
      Q2.hcardT96_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T96_53_2 i) (Q2.hfix96_53_2 i) _)
      colCert_96_53_0.hD ?_).symm
  rw [alnId_96 j hj]


theorem leaf_96_53_1 (hp : 1 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 96 []).length)
    (hq : (normIsRep.getD 96 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 1 hp)
        (rowE2 (⟨96, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 1 (transLenTr ⟨53, by decide⟩ 1 hp))
        (rowE1 (⟨96, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨96, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨96, by decide⟩ (listedAt ⟨96, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 1 (transLenTr ⟨53, by decide⟩ 1 hp)) T96_53
      hfix96_53 hinj96_53 hcardT96_53
      (fun i => conj_mem_of_fixedPoints _ _ (T96_53 i) (hfix96_53 i) _)
      ⟨96, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨96, by decide⟩ (Q2.listedAt ⟨96, by decide⟩
        (alnCheck_rep ⟨96, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 1 hp) Q2.T96_53_2 Q2.hfix96_53_2 Q2.hinj96_53_2
      Q2.hcardT96_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T96_53_2 i) (Q2.hfix96_53_2 i) _)
      colCert_96_53_1.hD ?_).symm
  rw [alnId_96 j hj]


theorem leaf_96_53_2 (hp : 2 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 96 []).length)
    (hq : (normIsRep.getD 96 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 2 hp)
        (rowE2 (⟨96, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 2 (transLenTr ⟨53, by decide⟩ 2 hp))
        (rowE1 (⟨96, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨96, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨96, by decide⟩ (listedAt ⟨96, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 2 (transLenTr ⟨53, by decide⟩ 2 hp)) T96_53
      hfix96_53 hinj96_53 hcardT96_53
      (fun i => conj_mem_of_fixedPoints _ _ (T96_53 i) (hfix96_53 i) _)
      ⟨96, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨96, by decide⟩ (Q2.listedAt ⟨96, by decide⟩
        (alnCheck_rep ⟨96, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 2 hp) Q2.T96_53_2 Q2.hfix96_53_2 Q2.hinj96_53_2
      Q2.hcardT96_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T96_53_2 i) (Q2.hfix96_53_2 i) _)
      colCert_96_53_2.hD ?_).symm
  rw [alnId_96 j hj]


theorem leaf_96_53_3 (hp : 3 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 96 []).length)
    (hq : (normIsRep.getD 96 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 3 hp)
        (rowE2 (⟨96, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 3 (transLenTr ⟨53, by decide⟩ 3 hp))
        (rowE1 (⟨96, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨96, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨96, by decide⟩ (listedAt ⟨96, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 3 (transLenTr ⟨53, by decide⟩ 3 hp)) T96_53
      hfix96_53 hinj96_53 hcardT96_53
      (fun i => conj_mem_of_fixedPoints _ _ (T96_53 i) (hfix96_53 i) _)
      ⟨96, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨96, by decide⟩ (Q2.listedAt ⟨96, by decide⟩
        (alnCheck_rep ⟨96, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 3 hp) Q2.T96_53_2 Q2.hfix96_53_2 Q2.hinj96_53_2
      Q2.hcardT96_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T96_53_2 i) (Q2.hfix96_53_2 i) _)
      colCert_96_53_3.hD ?_).symm
  rw [alnId_96 j hj]


theorem leaf_96_53_4 (hp : 4 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 96 []).length)
    (hq : (normIsRep.getD 96 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 4 hp)
        (rowE2 (⟨96, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 4 (transLenTr ⟨53, by decide⟩ 4 hp))
        (rowE1 (⟨96, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨96, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨96, by decide⟩ (listedAt ⟨96, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 4 (transLenTr ⟨53, by decide⟩ 4 hp)) T96_53
      hfix96_53 hinj96_53 hcardT96_53
      (fun i => conj_mem_of_fixedPoints _ _ (T96_53 i) (hfix96_53 i) _)
      ⟨96, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨96, by decide⟩ (Q2.listedAt ⟨96, by decide⟩
        (alnCheck_rep ⟨96, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 4 hp) Q2.T96_53_2 Q2.hfix96_53_2 Q2.hinj96_53_2
      Q2.hcardT96_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T96_53_2 i) (Q2.hfix96_53_2 i) _)
      colCert_96_53_4.hD ?_).symm
  rw [alnId_96 j hj]


theorem leaf_96_53_5 (hp : 5 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 96 []).length)
    (hq : (normIsRep.getD 96 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 5 hp)
        (rowE2 (⟨96, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 5 (transLenTr ⟨53, by decide⟩ 5 hp))
        (rowE1 (⟨96, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨96, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨96, by decide⟩ (listedAt ⟨96, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 5 (transLenTr ⟨53, by decide⟩ 5 hp)) T96_53
      hfix96_53 hinj96_53 hcardT96_53
      (fun i => conj_mem_of_fixedPoints _ _ (T96_53 i) (hfix96_53 i) _)
      ⟨96, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨96, by decide⟩ (Q2.listedAt ⟨96, by decide⟩
        (alnCheck_rep ⟨96, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 5 hp) Q2.T96_53_2 Q2.hfix96_53_2 Q2.hinj96_53_2
      Q2.hcardT96_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T96_53_2 i) (Q2.hfix96_53_2 i) _)
      colCert_96_53_5.hD ?_).symm
  rw [alnId_96 j hj]


theorem leaf_96_53_10 (hp : 10 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 96 []).length)
    (hq : (normIsRep.getD 96 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 10 hp)
        (rowE2 (⟨96, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 10 (transLenTr ⟨53, by decide⟩ 10 hp))
        (rowE1 (⟨96, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨96, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨96, by decide⟩ (listedAt ⟨96, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 10 (transLenTr ⟨53, by decide⟩ 10 hp)) T96_53
      hfix96_53 hinj96_53 hcardT96_53
      (fun i => conj_mem_of_fixedPoints _ _ (T96_53 i) (hfix96_53 i) _)
      ⟨96, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨96, by decide⟩ (Q2.listedAt ⟨96, by decide⟩
        (alnCheck_rep ⟨96, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 10 hp) Q2.T96_53_2 Q2.hfix96_53_2 Q2.hinj96_53_2
      Q2.hcardT96_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T96_53_2 i) (Q2.hfix96_53_2 i) _)
      colCert_96_53_10.hD ?_).symm
  rw [alnId_96 j hj]


theorem leaf_96_53_15 (hp : 15 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 96 []).length)
    (hq : (normIsRep.getD 96 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 15 hp)
        (rowE2 (⟨96, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 15 (transLenTr ⟨53, by decide⟩ 15 hp))
        (rowE1 (⟨96, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨96, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨96, by decide⟩ (listedAt ⟨96, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 15 (transLenTr ⟨53, by decide⟩ 15 hp)) T96_53
      hfix96_53 hinj96_53 hcardT96_53
      (fun i => conj_mem_of_fixedPoints _ _ (T96_53 i) (hfix96_53 i) _)
      ⟨96, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨96, by decide⟩ (Q2.listedAt ⟨96, by decide⟩
        (alnCheck_rep ⟨96, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 15 hp) Q2.T96_53_2 Q2.hfix96_53_2 Q2.hinj96_53_2
      Q2.hcardT96_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T96_53_2 i) (Q2.hfix96_53_2 i) _)
      colCert_96_53_15.hD ?_).symm
  rw [alnId_96 j hj]


theorem leaf_96_53_20 (hp : 20 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 96 []).length)
    (hq : (normIsRep.getD 96 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 20 hp)
        (rowE2 (⟨96, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 20 (transLenTr ⟨53, by decide⟩ 20 hp))
        (rowE1 (⟨96, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨96, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨96, by decide⟩ (listedAt ⟨96, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 20 (transLenTr ⟨53, by decide⟩ 20 hp)) T96_53
      hfix96_53 hinj96_53 hcardT96_53
      (fun i => conj_mem_of_fixedPoints _ _ (T96_53 i) (hfix96_53 i) _)
      ⟨96, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨96, by decide⟩ (Q2.listedAt ⟨96, by decide⟩
        (alnCheck_rep ⟨96, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 20 hp) Q2.T96_53_2 Q2.hfix96_53_2 Q2.hinj96_53_2
      Q2.hcardT96_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T96_53_2 i) (Q2.hfix96_53_2 i) _)
      colCert_96_53_20.hD ?_).symm
  rw [alnId_96 j hj]


theorem leaf_96_96_0 (hp : 0 < (Q2.transData.getD 96 []).length)
    (j : Nat) (hj : j < (repChars.getD 96 []).length)
    (hq : (normIsRep.getD 96 []).getD j false = true) :
    species (Q2.reps (⟨96, by decide⟩ : Fin 148)) (colE2 ⟨96, by decide⟩ 0 hp)
        (rowE2 (⟨96, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨96, by decide⟩ : Fin 148))
        (colE1 ⟨96, by decide⟩ 0 (transLenTr ⟨96, by decide⟩ 0 hp))
        (rowE1 (⟨96, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨96, by decide⟩ : Fin 148) ⟨96, by decide⟩ _
      (validAt ⟨96, by decide⟩ (listedAt ⟨96, by decide⟩ hj))
      (colE1 ⟨96, by decide⟩ 0 (transLenTr ⟨96, by decide⟩ 0 hp)) T96_96
      hfix96_96 hinj96_96 hcardT96_96
      (fun i => conj_mem_of_fixedPoints _ _ (T96_96 i) (hfix96_96 i) _)
      ⟨96, by decide⟩ ⟨96, by decide⟩ _
      (Q2.validAt ⟨96, by decide⟩ (Q2.listedAt ⟨96, by decide⟩
        (alnCheck_rep ⟨96, by decide⟩ hj hq).1))
      (colE2 ⟨96, by decide⟩ 0 hp) Q2.T96_96_2 Q2.hfix96_96_2 Q2.hinj96_96_2
      Q2.hcardT96_96_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T96_96_2 i) (Q2.hfix96_96_2 i) _)
      colCert_96_96_0.hD ?_).symm
  rw [alnId_96 j hj]


theorem leaf_96_96_1 (hp : 1 < (Q2.transData.getD 96 []).length)
    (j : Nat) (hj : j < (repChars.getD 96 []).length)
    (hq : (normIsRep.getD 96 []).getD j false = true) :
    species (Q2.reps (⟨96, by decide⟩ : Fin 148)) (colE2 ⟨96, by decide⟩ 1 hp)
        (rowE2 (⟨96, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨96, by decide⟩ : Fin 148))
        (colE1 ⟨96, by decide⟩ 1 (transLenTr ⟨96, by decide⟩ 1 hp))
        (rowE1 (⟨96, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨96, by decide⟩ : Fin 148) ⟨96, by decide⟩ _
      (validAt ⟨96, by decide⟩ (listedAt ⟨96, by decide⟩ hj))
      (colE1 ⟨96, by decide⟩ 1 (transLenTr ⟨96, by decide⟩ 1 hp)) T96_96
      hfix96_96 hinj96_96 hcardT96_96
      (fun i => conj_mem_of_fixedPoints _ _ (T96_96 i) (hfix96_96 i) _)
      ⟨96, by decide⟩ ⟨96, by decide⟩ _
      (Q2.validAt ⟨96, by decide⟩ (Q2.listedAt ⟨96, by decide⟩
        (alnCheck_rep ⟨96, by decide⟩ hj hq).1))
      (colE2 ⟨96, by decide⟩ 1 hp) Q2.T96_96_2 Q2.hfix96_96_2 Q2.hinj96_96_2
      Q2.hcardT96_96_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T96_96_2 i) (Q2.hfix96_96_2 i) _)
      colCert_96_96_1.hD ?_).symm
  rw [alnId_96 j hj]


theorem leaf_96_96_2 (hp : 2 < (Q2.transData.getD 96 []).length)
    (j : Nat) (hj : j < (repChars.getD 96 []).length)
    (hq : (normIsRep.getD 96 []).getD j false = true) :
    species (Q2.reps (⟨96, by decide⟩ : Fin 148)) (colE2 ⟨96, by decide⟩ 2 hp)
        (rowE2 (⟨96, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨96, by decide⟩ : Fin 148))
        (colE1 ⟨96, by decide⟩ 2 (transLenTr ⟨96, by decide⟩ 2 hp))
        (rowE1 (⟨96, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨96, by decide⟩ : Fin 148) ⟨96, by decide⟩ _
      (validAt ⟨96, by decide⟩ (listedAt ⟨96, by decide⟩ hj))
      (colE1 ⟨96, by decide⟩ 2 (transLenTr ⟨96, by decide⟩ 2 hp)) T96_96
      hfix96_96 hinj96_96 hcardT96_96
      (fun i => conj_mem_of_fixedPoints _ _ (T96_96 i) (hfix96_96 i) _)
      ⟨96, by decide⟩ ⟨96, by decide⟩ _
      (Q2.validAt ⟨96, by decide⟩ (Q2.listedAt ⟨96, by decide⟩
        (alnCheck_rep ⟨96, by decide⟩ hj hq).1))
      (colE2 ⟨96, by decide⟩ 2 hp) Q2.T96_96_2 Q2.hfix96_96_2 Q2.hinj96_96_2
      Q2.hcardT96_96_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T96_96_2 i) (Q2.hfix96_96_2 i) _)
      colCert_96_96_2.hD ?_).symm
  rw [alnId_96 j hj]


theorem leaf_96_96_3 (hp : 3 < (Q2.transData.getD 96 []).length)
    (j : Nat) (hj : j < (repChars.getD 96 []).length)
    (hq : (normIsRep.getD 96 []).getD j false = true) :
    species (Q2.reps (⟨96, by decide⟩ : Fin 148)) (colE2 ⟨96, by decide⟩ 3 hp)
        (rowE2 (⟨96, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨96, by decide⟩ : Fin 148))
        (colE1 ⟨96, by decide⟩ 3 (transLenTr ⟨96, by decide⟩ 3 hp))
        (rowE1 (⟨96, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨96, by decide⟩ : Fin 148) ⟨96, by decide⟩ _
      (validAt ⟨96, by decide⟩ (listedAt ⟨96, by decide⟩ hj))
      (colE1 ⟨96, by decide⟩ 3 (transLenTr ⟨96, by decide⟩ 3 hp)) T96_96
      hfix96_96 hinj96_96 hcardT96_96
      (fun i => conj_mem_of_fixedPoints _ _ (T96_96 i) (hfix96_96 i) _)
      ⟨96, by decide⟩ ⟨96, by decide⟩ _
      (Q2.validAt ⟨96, by decide⟩ (Q2.listedAt ⟨96, by decide⟩
        (alnCheck_rep ⟨96, by decide⟩ hj hq).1))
      (colE2 ⟨96, by decide⟩ 3 hp) Q2.T96_96_2 Q2.hfix96_96_2 Q2.hinj96_96_2
      Q2.hcardT96_96_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T96_96_2 i) (Q2.hfix96_96_2 i) _)
      colCert_96_96_3.hD ?_).symm
  rw [alnId_96 j hj]


theorem leaf_96_96_4 (hp : 4 < (Q2.transData.getD 96 []).length)
    (j : Nat) (hj : j < (repChars.getD 96 []).length)
    (hq : (normIsRep.getD 96 []).getD j false = true) :
    species (Q2.reps (⟨96, by decide⟩ : Fin 148)) (colE2 ⟨96, by decide⟩ 4 hp)
        (rowE2 (⟨96, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨96, by decide⟩ : Fin 148))
        (colE1 ⟨96, by decide⟩ 4 (transLenTr ⟨96, by decide⟩ 4 hp))
        (rowE1 (⟨96, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨96, by decide⟩ : Fin 148) ⟨96, by decide⟩ _
      (validAt ⟨96, by decide⟩ (listedAt ⟨96, by decide⟩ hj))
      (colE1 ⟨96, by decide⟩ 4 (transLenTr ⟨96, by decide⟩ 4 hp)) T96_96
      hfix96_96 hinj96_96 hcardT96_96
      (fun i => conj_mem_of_fixedPoints _ _ (T96_96 i) (hfix96_96 i) _)
      ⟨96, by decide⟩ ⟨96, by decide⟩ _
      (Q2.validAt ⟨96, by decide⟩ (Q2.listedAt ⟨96, by decide⟩
        (alnCheck_rep ⟨96, by decide⟩ hj hq).1))
      (colE2 ⟨96, by decide⟩ 4 hp) Q2.T96_96_2 Q2.hfix96_96_2 Q2.hinj96_96_2
      Q2.hcardT96_96_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T96_96_2 i) (Q2.hfix96_96_2 i) _)
      colCert_96_96_4.hD ?_).symm
  rw [alnId_96 j hj]


theorem leaf_96_96_5 (hp : 5 < (Q2.transData.getD 96 []).length)
    (j : Nat) (hj : j < (repChars.getD 96 []).length)
    (hq : (normIsRep.getD 96 []).getD j false = true) :
    species (Q2.reps (⟨96, by decide⟩ : Fin 148)) (colE2 ⟨96, by decide⟩ 5 hp)
        (rowE2 (⟨96, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨96, by decide⟩ : Fin 148))
        (colE1 ⟨96, by decide⟩ 5 (transLenTr ⟨96, by decide⟩ 5 hp))
        (rowE1 (⟨96, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨96, by decide⟩ : Fin 148) ⟨96, by decide⟩ _
      (validAt ⟨96, by decide⟩ (listedAt ⟨96, by decide⟩ hj))
      (colE1 ⟨96, by decide⟩ 5 (transLenTr ⟨96, by decide⟩ 5 hp)) T96_96
      hfix96_96 hinj96_96 hcardT96_96
      (fun i => conj_mem_of_fixedPoints _ _ (T96_96 i) (hfix96_96 i) _)
      ⟨96, by decide⟩ ⟨96, by decide⟩ _
      (Q2.validAt ⟨96, by decide⟩ (Q2.listedAt ⟨96, by decide⟩
        (alnCheck_rep ⟨96, by decide⟩ hj hq).1))
      (colE2 ⟨96, by decide⟩ 5 hp) Q2.T96_96_2 Q2.hfix96_96_2 Q2.hinj96_96_2
      Q2.hcardT96_96_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T96_96_2 i) (Q2.hfix96_96_2 i) _)
      colCert_96_96_5.hD ?_).symm
  rw [alnId_96 j hj]


theorem leaf_96_96_10 (hp : 10 < (Q2.transData.getD 96 []).length)
    (j : Nat) (hj : j < (repChars.getD 96 []).length)
    (hq : (normIsRep.getD 96 []).getD j false = true) :
    species (Q2.reps (⟨96, by decide⟩ : Fin 148)) (colE2 ⟨96, by decide⟩ 10 hp)
        (rowE2 (⟨96, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨96, by decide⟩ : Fin 148))
        (colE1 ⟨96, by decide⟩ 10 (transLenTr ⟨96, by decide⟩ 10 hp))
        (rowE1 (⟨96, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨96, by decide⟩ : Fin 148) ⟨96, by decide⟩ _
      (validAt ⟨96, by decide⟩ (listedAt ⟨96, by decide⟩ hj))
      (colE1 ⟨96, by decide⟩ 10 (transLenTr ⟨96, by decide⟩ 10 hp)) T96_96
      hfix96_96 hinj96_96 hcardT96_96
      (fun i => conj_mem_of_fixedPoints _ _ (T96_96 i) (hfix96_96 i) _)
      ⟨96, by decide⟩ ⟨96, by decide⟩ _
      (Q2.validAt ⟨96, by decide⟩ (Q2.listedAt ⟨96, by decide⟩
        (alnCheck_rep ⟨96, by decide⟩ hj hq).1))
      (colE2 ⟨96, by decide⟩ 10 hp) Q2.T96_96_2 Q2.hfix96_96_2 Q2.hinj96_96_2
      Q2.hcardT96_96_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T96_96_2 i) (Q2.hfix96_96_2 i) _)
      colCert_96_96_10.hD ?_).symm
  rw [alnId_96 j hj]


theorem leaf_96_96_15 (hp : 15 < (Q2.transData.getD 96 []).length)
    (j : Nat) (hj : j < (repChars.getD 96 []).length)
    (hq : (normIsRep.getD 96 []).getD j false = true) :
    species (Q2.reps (⟨96, by decide⟩ : Fin 148)) (colE2 ⟨96, by decide⟩ 15 hp)
        (rowE2 (⟨96, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨96, by decide⟩ : Fin 148))
        (colE1 ⟨96, by decide⟩ 15 (transLenTr ⟨96, by decide⟩ 15 hp))
        (rowE1 (⟨96, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨96, by decide⟩ : Fin 148) ⟨96, by decide⟩ _
      (validAt ⟨96, by decide⟩ (listedAt ⟨96, by decide⟩ hj))
      (colE1 ⟨96, by decide⟩ 15 (transLenTr ⟨96, by decide⟩ 15 hp)) T96_96
      hfix96_96 hinj96_96 hcardT96_96
      (fun i => conj_mem_of_fixedPoints _ _ (T96_96 i) (hfix96_96 i) _)
      ⟨96, by decide⟩ ⟨96, by decide⟩ _
      (Q2.validAt ⟨96, by decide⟩ (Q2.listedAt ⟨96, by decide⟩
        (alnCheck_rep ⟨96, by decide⟩ hj hq).1))
      (colE2 ⟨96, by decide⟩ 15 hp) Q2.T96_96_2 Q2.hfix96_96_2 Q2.hinj96_96_2
      Q2.hcardT96_96_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T96_96_2 i) (Q2.hfix96_96_2 i) _)
      colCert_96_96_15.hD ?_).symm
  rw [alnId_96 j hj]


theorem leaf_96_96_20 (hp : 20 < (Q2.transData.getD 96 []).length)
    (j : Nat) (hj : j < (repChars.getD 96 []).length)
    (hq : (normIsRep.getD 96 []).getD j false = true) :
    species (Q2.reps (⟨96, by decide⟩ : Fin 148)) (colE2 ⟨96, by decide⟩ 20 hp)
        (rowE2 (⟨96, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨96, by decide⟩ : Fin 148))
        (colE1 ⟨96, by decide⟩ 20 (transLenTr ⟨96, by decide⟩ 20 hp))
        (rowE1 (⟨96, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨96, by decide⟩ : Fin 148) ⟨96, by decide⟩ _
      (validAt ⟨96, by decide⟩ (listedAt ⟨96, by decide⟩ hj))
      (colE1 ⟨96, by decide⟩ 20 (transLenTr ⟨96, by decide⟩ 20 hp)) T96_96
      hfix96_96 hinj96_96 hcardT96_96
      (fun i => conj_mem_of_fixedPoints _ _ (T96_96 i) (hfix96_96 i) _)
      ⟨96, by decide⟩ ⟨96, by decide⟩ _
      (Q2.validAt ⟨96, by decide⟩ (Q2.listedAt ⟨96, by decide⟩
        (alnCheck_rep ⟨96, by decide⟩ hj hq).1))
      (colE2 ⟨96, by decide⟩ 20 hp) Q2.T96_96_2 Q2.hfix96_96_2 Q2.hinj96_96_2
      Q2.hcardT96_96_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T96_96_2 i) (Q2.hfix96_96_2 i) _)
      colCert_96_96_20.hD ?_).symm
  rw [alnId_96 j hj]


theorem leaf_97_10_0 (hp : 0 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 97 []).length)
    (hq : (normIsRep.getD 97 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 0 hp)
        (rowE2 (⟨97, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 0 (transLenTr ⟨10, by decide⟩ 0 hp))
        (rowE1 (⟨97, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨97, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨97, by decide⟩ (listedAt ⟨97, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 0 (transLenTr ⟨10, by decide⟩ 0 hp)) T97_10
      hfix97_10 hinj97_10 hcardT97_10
      (fun i => conj_mem_of_fixedPoints _ _ (T97_10 i) (hfix97_10 i) _)
      ⟨97, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨97, by decide⟩ (Q2.listedAt ⟨97, by decide⟩
        (alnCheck_rep ⟨97, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 0 hp) Q2.T97_10_2 Q2.hfix97_10_2 Q2.hinj97_10_2
      Q2.hcardT97_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T97_10_2 i) (Q2.hfix97_10_2 i) _)
      colCert_97_10_0.hD ?_).symm
  rw [alnId_97 j hj]


theorem leaf_97_10_1 (hp : 1 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 97 []).length)
    (hq : (normIsRep.getD 97 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 1 hp)
        (rowE2 (⟨97, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 1 (transLenTr ⟨10, by decide⟩ 1 hp))
        (rowE1 (⟨97, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨97, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨97, by decide⟩ (listedAt ⟨97, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 1 (transLenTr ⟨10, by decide⟩ 1 hp)) T97_10
      hfix97_10 hinj97_10 hcardT97_10
      (fun i => conj_mem_of_fixedPoints _ _ (T97_10 i) (hfix97_10 i) _)
      ⟨97, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨97, by decide⟩ (Q2.listedAt ⟨97, by decide⟩
        (alnCheck_rep ⟨97, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 1 hp) Q2.T97_10_2 Q2.hfix97_10_2 Q2.hinj97_10_2
      Q2.hcardT97_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T97_10_2 i) (Q2.hfix97_10_2 i) _)
      colCert_97_10_1.hD ?_).symm
  rw [alnId_97 j hj]


theorem leaf_97_10_2 (hp : 2 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 97 []).length)
    (hq : (normIsRep.getD 97 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 2 hp)
        (rowE2 (⟨97, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 2 (transLenTr ⟨10, by decide⟩ 2 hp))
        (rowE1 (⟨97, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨97, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨97, by decide⟩ (listedAt ⟨97, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 2 (transLenTr ⟨10, by decide⟩ 2 hp)) T97_10
      hfix97_10 hinj97_10 hcardT97_10
      (fun i => conj_mem_of_fixedPoints _ _ (T97_10 i) (hfix97_10 i) _)
      ⟨97, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨97, by decide⟩ (Q2.listedAt ⟨97, by decide⟩
        (alnCheck_rep ⟨97, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 2 hp) Q2.T97_10_2 Q2.hfix97_10_2 Q2.hinj97_10_2
      Q2.hcardT97_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T97_10_2 i) (Q2.hfix97_10_2 i) _)
      colCert_97_10_2.hD ?_).symm
  rw [alnId_97 j hj]


theorem leaf_97_10_3 (hp : 3 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 97 []).length)
    (hq : (normIsRep.getD 97 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 3 hp)
        (rowE2 (⟨97, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 3 (transLenTr ⟨10, by decide⟩ 3 hp))
        (rowE1 (⟨97, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨97, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨97, by decide⟩ (listedAt ⟨97, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 3 (transLenTr ⟨10, by decide⟩ 3 hp)) T97_10
      hfix97_10 hinj97_10 hcardT97_10
      (fun i => conj_mem_of_fixedPoints _ _ (T97_10 i) (hfix97_10 i) _)
      ⟨97, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨97, by decide⟩ (Q2.listedAt ⟨97, by decide⟩
        (alnCheck_rep ⟨97, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 3 hp) Q2.T97_10_2 Q2.hfix97_10_2 Q2.hinj97_10_2
      Q2.hcardT97_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T97_10_2 i) (Q2.hfix97_10_2 i) _)
      colCert_97_10_3.hD ?_).symm
  rw [alnId_97 j hj]


theorem leaf_97_10_4 (hp : 4 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 97 []).length)
    (hq : (normIsRep.getD 97 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 4 hp)
        (rowE2 (⟨97, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 4 (transLenTr ⟨10, by decide⟩ 4 hp))
        (rowE1 (⟨97, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨97, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨97, by decide⟩ (listedAt ⟨97, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 4 (transLenTr ⟨10, by decide⟩ 4 hp)) T97_10
      hfix97_10 hinj97_10 hcardT97_10
      (fun i => conj_mem_of_fixedPoints _ _ (T97_10 i) (hfix97_10 i) _)
      ⟨97, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨97, by decide⟩ (Q2.listedAt ⟨97, by decide⟩
        (alnCheck_rep ⟨97, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 4 hp) Q2.T97_10_2 Q2.hfix97_10_2 Q2.hinj97_10_2
      Q2.hcardT97_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T97_10_2 i) (Q2.hfix97_10_2 i) _)
      colCert_97_10_4.hD ?_).symm
  rw [alnId_97 j hj]


theorem leaf_97_12_0 (hp : 0 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 97 []).length)
    (hq : (normIsRep.getD 97 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 0 hp)
        (rowE2 (⟨97, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp))
        (rowE1 (⟨97, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨97, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨97, by decide⟩ (listedAt ⟨97, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp)) T97_12
      hfix97_12 hinj97_12 hcardT97_12
      (fun i => conj_mem_of_fixedPoints _ _ (T97_12 i) (hfix97_12 i) _)
      ⟨97, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨97, by decide⟩ (Q2.listedAt ⟨97, by decide⟩
        (alnCheck_rep ⟨97, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 0 hp) Q2.T97_12_2 Q2.hfix97_12_2 Q2.hinj97_12_2
      Q2.hcardT97_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T97_12_2 i) (Q2.hfix97_12_2 i) _)
      colCert_97_12_0.hD ?_).symm
  rw [alnId_97 j hj]


theorem leaf_97_12_1 (hp : 1 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 97 []).length)
    (hq : (normIsRep.getD 97 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 1 hp)
        (rowE2 (⟨97, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp))
        (rowE1 (⟨97, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨97, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨97, by decide⟩ (listedAt ⟨97, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp)) T97_12
      hfix97_12 hinj97_12 hcardT97_12
      (fun i => conj_mem_of_fixedPoints _ _ (T97_12 i) (hfix97_12 i) _)
      ⟨97, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨97, by decide⟩ (Q2.listedAt ⟨97, by decide⟩
        (alnCheck_rep ⟨97, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 1 hp) Q2.T97_12_2 Q2.hfix97_12_2 Q2.hinj97_12_2
      Q2.hcardT97_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T97_12_2 i) (Q2.hfix97_12_2 i) _)
      colCert_97_12_1.hD ?_).symm
  rw [alnId_97 j hj]


theorem leaf_97_12_2 (hp : 2 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 97 []).length)
    (hq : (normIsRep.getD 97 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 2 hp)
        (rowE2 (⟨97, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp))
        (rowE1 (⟨97, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨97, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨97, by decide⟩ (listedAt ⟨97, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp)) T97_12
      hfix97_12 hinj97_12 hcardT97_12
      (fun i => conj_mem_of_fixedPoints _ _ (T97_12 i) (hfix97_12 i) _)
      ⟨97, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨97, by decide⟩ (Q2.listedAt ⟨97, by decide⟩
        (alnCheck_rep ⟨97, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 2 hp) Q2.T97_12_2 Q2.hfix97_12_2 Q2.hinj97_12_2
      Q2.hcardT97_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T97_12_2 i) (Q2.hfix97_12_2 i) _)
      colCert_97_12_2.hD ?_).symm
  rw [alnId_97 j hj]


theorem leaf_97_12_3 (hp : 3 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 97 []).length)
    (hq : (normIsRep.getD 97 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 3 hp)
        (rowE2 (⟨97, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp))
        (rowE1 (⟨97, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨97, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨97, by decide⟩ (listedAt ⟨97, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp)) T97_12
      hfix97_12 hinj97_12 hcardT97_12
      (fun i => conj_mem_of_fixedPoints _ _ (T97_12 i) (hfix97_12 i) _)
      ⟨97, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨97, by decide⟩ (Q2.listedAt ⟨97, by decide⟩
        (alnCheck_rep ⟨97, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 3 hp) Q2.T97_12_2 Q2.hfix97_12_2 Q2.hinj97_12_2
      Q2.hcardT97_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T97_12_2 i) (Q2.hfix97_12_2 i) _)
      colCert_97_12_3.hD ?_).symm
  rw [alnId_97 j hj]


theorem leaf_97_12_4 (hp : 4 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 97 []).length)
    (hq : (normIsRep.getD 97 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 4 hp)
        (rowE2 (⟨97, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp))
        (rowE1 (⟨97, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨97, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨97, by decide⟩ (listedAt ⟨97, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp)) T97_12
      hfix97_12 hinj97_12 hcardT97_12
      (fun i => conj_mem_of_fixedPoints _ _ (T97_12 i) (hfix97_12 i) _)
      ⟨97, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨97, by decide⟩ (Q2.listedAt ⟨97, by decide⟩
        (alnCheck_rep ⟨97, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 4 hp) Q2.T97_12_2 Q2.hfix97_12_2 Q2.hinj97_12_2
      Q2.hcardT97_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T97_12_2 i) (Q2.hfix97_12_2 i) _)
      colCert_97_12_4.hD ?_).symm
  rw [alnId_97 j hj]


theorem leaf_97_35_0 (hp : 0 < (Q2.transData.getD 35 []).length)
    (j : Nat) (hj : j < (repChars.getD 97 []).length)
    (hq : (normIsRep.getD 97 []).getD j false = true) :
    species (Q2.reps (⟨35, by decide⟩ : Fin 148)) (colE2 ⟨35, by decide⟩ 0 hp)
        (rowE2 (⟨97, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨35, by decide⟩ : Fin 148))
        (colE1 ⟨35, by decide⟩ 0 (transLenTr ⟨35, by decide⟩ 0 hp))
        (rowE1 (⟨97, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨97, by decide⟩ : Fin 148) ⟨35, by decide⟩ _
      (validAt ⟨97, by decide⟩ (listedAt ⟨97, by decide⟩ hj))
      (colE1 ⟨35, by decide⟩ 0 (transLenTr ⟨35, by decide⟩ 0 hp)) T97_35
      hfix97_35 hinj97_35 hcardT97_35
      (fun i => conj_mem_of_fixedPoints _ _ (T97_35 i) (hfix97_35 i) _)
      ⟨97, by decide⟩ ⟨35, by decide⟩ _
      (Q2.validAt ⟨97, by decide⟩ (Q2.listedAt ⟨97, by decide⟩
        (alnCheck_rep ⟨97, by decide⟩ hj hq).1))
      (colE2 ⟨35, by decide⟩ 0 hp) Q2.T97_35_2 Q2.hfix97_35_2 Q2.hinj97_35_2
      Q2.hcardT97_35_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T97_35_2 i) (Q2.hfix97_35_2 i) _)
      colCert_97_35_0.hD ?_).symm
  rw [alnId_97 j hj]


theorem leaf_97_35_1 (hp : 1 < (Q2.transData.getD 35 []).length)
    (j : Nat) (hj : j < (repChars.getD 97 []).length)
    (hq : (normIsRep.getD 97 []).getD j false = true) :
    species (Q2.reps (⟨35, by decide⟩ : Fin 148)) (colE2 ⟨35, by decide⟩ 1 hp)
        (rowE2 (⟨97, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨35, by decide⟩ : Fin 148))
        (colE1 ⟨35, by decide⟩ 1 (transLenTr ⟨35, by decide⟩ 1 hp))
        (rowE1 (⟨97, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨97, by decide⟩ : Fin 148) ⟨35, by decide⟩ _
      (validAt ⟨97, by decide⟩ (listedAt ⟨97, by decide⟩ hj))
      (colE1 ⟨35, by decide⟩ 1 (transLenTr ⟨35, by decide⟩ 1 hp)) T97_35
      hfix97_35 hinj97_35 hcardT97_35
      (fun i => conj_mem_of_fixedPoints _ _ (T97_35 i) (hfix97_35 i) _)
      ⟨97, by decide⟩ ⟨35, by decide⟩ _
      (Q2.validAt ⟨97, by decide⟩ (Q2.listedAt ⟨97, by decide⟩
        (alnCheck_rep ⟨97, by decide⟩ hj hq).1))
      (colE2 ⟨35, by decide⟩ 1 hp) Q2.T97_35_2 Q2.hfix97_35_2 Q2.hinj97_35_2
      Q2.hcardT97_35_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T97_35_2 i) (Q2.hfix97_35_2 i) _)
      colCert_97_35_1.hD ?_).symm
  rw [alnId_97 j hj]


theorem leaf_97_35_2 (hp : 2 < (Q2.transData.getD 35 []).length)
    (j : Nat) (hj : j < (repChars.getD 97 []).length)
    (hq : (normIsRep.getD 97 []).getD j false = true) :
    species (Q2.reps (⟨35, by decide⟩ : Fin 148)) (colE2 ⟨35, by decide⟩ 2 hp)
        (rowE2 (⟨97, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨35, by decide⟩ : Fin 148))
        (colE1 ⟨35, by decide⟩ 2 (transLenTr ⟨35, by decide⟩ 2 hp))
        (rowE1 (⟨97, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨97, by decide⟩ : Fin 148) ⟨35, by decide⟩ _
      (validAt ⟨97, by decide⟩ (listedAt ⟨97, by decide⟩ hj))
      (colE1 ⟨35, by decide⟩ 2 (transLenTr ⟨35, by decide⟩ 2 hp)) T97_35
      hfix97_35 hinj97_35 hcardT97_35
      (fun i => conj_mem_of_fixedPoints _ _ (T97_35 i) (hfix97_35 i) _)
      ⟨97, by decide⟩ ⟨35, by decide⟩ _
      (Q2.validAt ⟨97, by decide⟩ (Q2.listedAt ⟨97, by decide⟩
        (alnCheck_rep ⟨97, by decide⟩ hj hq).1))
      (colE2 ⟨35, by decide⟩ 2 hp) Q2.T97_35_2 Q2.hfix97_35_2 Q2.hinj97_35_2
      Q2.hcardT97_35_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T97_35_2 i) (Q2.hfix97_35_2 i) _)
      colCert_97_35_2.hD ?_).symm
  rw [alnId_97 j hj]


theorem leaf_97_35_3 (hp : 3 < (Q2.transData.getD 35 []).length)
    (j : Nat) (hj : j < (repChars.getD 97 []).length)
    (hq : (normIsRep.getD 97 []).getD j false = true) :
    species (Q2.reps (⟨35, by decide⟩ : Fin 148)) (colE2 ⟨35, by decide⟩ 3 hp)
        (rowE2 (⟨97, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨35, by decide⟩ : Fin 148))
        (colE1 ⟨35, by decide⟩ 3 (transLenTr ⟨35, by decide⟩ 3 hp))
        (rowE1 (⟨97, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨97, by decide⟩ : Fin 148) ⟨35, by decide⟩ _
      (validAt ⟨97, by decide⟩ (listedAt ⟨97, by decide⟩ hj))
      (colE1 ⟨35, by decide⟩ 3 (transLenTr ⟨35, by decide⟩ 3 hp)) T97_35
      hfix97_35 hinj97_35 hcardT97_35
      (fun i => conj_mem_of_fixedPoints _ _ (T97_35 i) (hfix97_35 i) _)
      ⟨97, by decide⟩ ⟨35, by decide⟩ _
      (Q2.validAt ⟨97, by decide⟩ (Q2.listedAt ⟨97, by decide⟩
        (alnCheck_rep ⟨97, by decide⟩ hj hq).1))
      (colE2 ⟨35, by decide⟩ 3 hp) Q2.T97_35_2 Q2.hfix97_35_2 Q2.hinj97_35_2
      Q2.hcardT97_35_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T97_35_2 i) (Q2.hfix97_35_2 i) _)
      colCert_97_35_3.hD ?_).symm
  rw [alnId_97 j hj]


theorem leaf_97_35_4 (hp : 4 < (Q2.transData.getD 35 []).length)
    (j : Nat) (hj : j < (repChars.getD 97 []).length)
    (hq : (normIsRep.getD 97 []).getD j false = true) :
    species (Q2.reps (⟨35, by decide⟩ : Fin 148)) (colE2 ⟨35, by decide⟩ 4 hp)
        (rowE2 (⟨97, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨35, by decide⟩ : Fin 148))
        (colE1 ⟨35, by decide⟩ 4 (transLenTr ⟨35, by decide⟩ 4 hp))
        (rowE1 (⟨97, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨97, by decide⟩ : Fin 148) ⟨35, by decide⟩ _
      (validAt ⟨97, by decide⟩ (listedAt ⟨97, by decide⟩ hj))
      (colE1 ⟨35, by decide⟩ 4 (transLenTr ⟨35, by decide⟩ 4 hp)) T97_35
      hfix97_35 hinj97_35 hcardT97_35
      (fun i => conj_mem_of_fixedPoints _ _ (T97_35 i) (hfix97_35 i) _)
      ⟨97, by decide⟩ ⟨35, by decide⟩ _
      (Q2.validAt ⟨97, by decide⟩ (Q2.listedAt ⟨97, by decide⟩
        (alnCheck_rep ⟨97, by decide⟩ hj hq).1))
      (colE2 ⟨35, by decide⟩ 4 hp) Q2.T97_35_2 Q2.hfix97_35_2 Q2.hinj97_35_2
      Q2.hcardT97_35_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T97_35_2 i) (Q2.hfix97_35_2 i) _)
      colCert_97_35_4.hD ?_).symm
  rw [alnId_97 j hj]


theorem leaf_97_35_5 (hp : 5 < (Q2.transData.getD 35 []).length)
    (j : Nat) (hj : j < (repChars.getD 97 []).length)
    (hq : (normIsRep.getD 97 []).getD j false = true) :
    species (Q2.reps (⟨35, by decide⟩ : Fin 148)) (colE2 ⟨35, by decide⟩ 5 hp)
        (rowE2 (⟨97, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨35, by decide⟩ : Fin 148))
        (colE1 ⟨35, by decide⟩ 5 (transLenTr ⟨35, by decide⟩ 5 hp))
        (rowE1 (⟨97, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨97, by decide⟩ : Fin 148) ⟨35, by decide⟩ _
      (validAt ⟨97, by decide⟩ (listedAt ⟨97, by decide⟩ hj))
      (colE1 ⟨35, by decide⟩ 5 (transLenTr ⟨35, by decide⟩ 5 hp)) T97_35
      hfix97_35 hinj97_35 hcardT97_35
      (fun i => conj_mem_of_fixedPoints _ _ (T97_35 i) (hfix97_35 i) _)
      ⟨97, by decide⟩ ⟨35, by decide⟩ _
      (Q2.validAt ⟨97, by decide⟩ (Q2.listedAt ⟨97, by decide⟩
        (alnCheck_rep ⟨97, by decide⟩ hj hq).1))
      (colE2 ⟨35, by decide⟩ 5 hp) Q2.T97_35_2 Q2.hfix97_35_2 Q2.hinj97_35_2
      Q2.hcardT97_35_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T97_35_2 i) (Q2.hfix97_35_2 i) _)
      ?_).symm
  rw [show colData1 (⟨97, by decide⟩ : Fin 148)
        ((colE1 ⟨35, by decide⟩ 5 (transLenTr ⟨35, by decide⟩ 5 hp) : ↥(reps ⟨35, by decide⟩)) : Coordinate 1)
        T97_35 = colFn colCertDiv_97_35_5.D1 (m := 25) from colCertDiv_97_35_5.bind1,
    show colData2 (⟨97, by decide⟩ : Fin 148)
        ((colE2 ⟨35, by decide⟩ 5 hp : ↥(Q2.reps ⟨35, by decide⟩)) : Coordinate 2)
        Q2.T97_35_2 = colFn colCertDiv_97_35_5.D2 (m := 25) from colCertDiv_97_35_5.bind2]
  rw [alnId_97 j hj]
  exact fastcode_of_div ⟨97, by decide⟩ _ _ _
    ((alnId_97 j hj) ▸ Q2.listedAt (⟨97, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨97, by decide⟩ : Fin 148) hj hq).1) colCertDiv_97_35_5_match


theorem leaf_97_35_10 (hp : 10 < (Q2.transData.getD 35 []).length)
    (j : Nat) (hj : j < (repChars.getD 97 []).length)
    (hq : (normIsRep.getD 97 []).getD j false = true) :
    species (Q2.reps (⟨35, by decide⟩ : Fin 148)) (colE2 ⟨35, by decide⟩ 10 hp)
        (rowE2 (⟨97, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨35, by decide⟩ : Fin 148))
        (colE1 ⟨35, by decide⟩ 10 (transLenTr ⟨35, by decide⟩ 10 hp))
        (rowE1 (⟨97, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨97, by decide⟩ : Fin 148) ⟨35, by decide⟩ _
      (validAt ⟨97, by decide⟩ (listedAt ⟨97, by decide⟩ hj))
      (colE1 ⟨35, by decide⟩ 10 (transLenTr ⟨35, by decide⟩ 10 hp)) T97_35
      hfix97_35 hinj97_35 hcardT97_35
      (fun i => conj_mem_of_fixedPoints _ _ (T97_35 i) (hfix97_35 i) _)
      ⟨97, by decide⟩ ⟨35, by decide⟩ _
      (Q2.validAt ⟨97, by decide⟩ (Q2.listedAt ⟨97, by decide⟩
        (alnCheck_rep ⟨97, by decide⟩ hj hq).1))
      (colE2 ⟨35, by decide⟩ 10 hp) Q2.T97_35_2 Q2.hfix97_35_2 Q2.hinj97_35_2
      Q2.hcardT97_35_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T97_35_2 i) (Q2.hfix97_35_2 i) _)
      ?_).symm
  rw [show colData1 (⟨97, by decide⟩ : Fin 148)
        ((colE1 ⟨35, by decide⟩ 10 (transLenTr ⟨35, by decide⟩ 10 hp) : ↥(reps ⟨35, by decide⟩)) : Coordinate 1)
        T97_35 = colFn colCertDiv_97_35_10.D1 (m := 25) from colCertDiv_97_35_10.bind1,
    show colData2 (⟨97, by decide⟩ : Fin 148)
        ((colE2 ⟨35, by decide⟩ 10 hp : ↥(Q2.reps ⟨35, by decide⟩)) : Coordinate 2)
        Q2.T97_35_2 = colFn colCertDiv_97_35_10.D2 (m := 25) from colCertDiv_97_35_10.bind2]
  rw [alnId_97 j hj]
  exact fastcode_of_div ⟨97, by decide⟩ _ _ _
    ((alnId_97 j hj) ▸ Q2.listedAt (⟨97, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨97, by decide⟩ : Fin 148) hj hq).1) colCertDiv_97_35_10_match


theorem leaf_97_35_15 (hp : 15 < (Q2.transData.getD 35 []).length)
    (j : Nat) (hj : j < (repChars.getD 97 []).length)
    (hq : (normIsRep.getD 97 []).getD j false = true) :
    species (Q2.reps (⟨35, by decide⟩ : Fin 148)) (colE2 ⟨35, by decide⟩ 15 hp)
        (rowE2 (⟨97, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨35, by decide⟩ : Fin 148))
        (colE1 ⟨35, by decide⟩ 15 (transLenTr ⟨35, by decide⟩ 15 hp))
        (rowE1 (⟨97, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨97, by decide⟩ : Fin 148) ⟨35, by decide⟩ _
      (validAt ⟨97, by decide⟩ (listedAt ⟨97, by decide⟩ hj))
      (colE1 ⟨35, by decide⟩ 15 (transLenTr ⟨35, by decide⟩ 15 hp)) T97_35
      hfix97_35 hinj97_35 hcardT97_35
      (fun i => conj_mem_of_fixedPoints _ _ (T97_35 i) (hfix97_35 i) _)
      ⟨97, by decide⟩ ⟨35, by decide⟩ _
      (Q2.validAt ⟨97, by decide⟩ (Q2.listedAt ⟨97, by decide⟩
        (alnCheck_rep ⟨97, by decide⟩ hj hq).1))
      (colE2 ⟨35, by decide⟩ 15 hp) Q2.T97_35_2 Q2.hfix97_35_2 Q2.hinj97_35_2
      Q2.hcardT97_35_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T97_35_2 i) (Q2.hfix97_35_2 i) _)
      ?_).symm
  rw [show colData1 (⟨97, by decide⟩ : Fin 148)
        ((colE1 ⟨35, by decide⟩ 15 (transLenTr ⟨35, by decide⟩ 15 hp) : ↥(reps ⟨35, by decide⟩)) : Coordinate 1)
        T97_35 = colFn colCertDiv_97_35_15.D1 (m := 25) from colCertDiv_97_35_15.bind1,
    show colData2 (⟨97, by decide⟩ : Fin 148)
        ((colE2 ⟨35, by decide⟩ 15 hp : ↥(Q2.reps ⟨35, by decide⟩)) : Coordinate 2)
        Q2.T97_35_2 = colFn colCertDiv_97_35_15.D2 (m := 25) from colCertDiv_97_35_15.bind2]
  rw [alnId_97 j hj]
  exact fastcode_of_div ⟨97, by decide⟩ _ _ _
    ((alnId_97 j hj) ▸ Q2.listedAt (⟨97, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨97, by decide⟩ : Fin 148) hj hq).1) colCertDiv_97_35_15_match


theorem leaf_97_35_20 (hp : 20 < (Q2.transData.getD 35 []).length)
    (j : Nat) (hj : j < (repChars.getD 97 []).length)
    (hq : (normIsRep.getD 97 []).getD j false = true) :
    species (Q2.reps (⟨35, by decide⟩ : Fin 148)) (colE2 ⟨35, by decide⟩ 20 hp)
        (rowE2 (⟨97, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨35, by decide⟩ : Fin 148))
        (colE1 ⟨35, by decide⟩ 20 (transLenTr ⟨35, by decide⟩ 20 hp))
        (rowE1 (⟨97, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨97, by decide⟩ : Fin 148) ⟨35, by decide⟩ _
      (validAt ⟨97, by decide⟩ (listedAt ⟨97, by decide⟩ hj))
      (colE1 ⟨35, by decide⟩ 20 (transLenTr ⟨35, by decide⟩ 20 hp)) T97_35
      hfix97_35 hinj97_35 hcardT97_35
      (fun i => conj_mem_of_fixedPoints _ _ (T97_35 i) (hfix97_35 i) _)
      ⟨97, by decide⟩ ⟨35, by decide⟩ _
      (Q2.validAt ⟨97, by decide⟩ (Q2.listedAt ⟨97, by decide⟩
        (alnCheck_rep ⟨97, by decide⟩ hj hq).1))
      (colE2 ⟨35, by decide⟩ 20 hp) Q2.T97_35_2 Q2.hfix97_35_2 Q2.hinj97_35_2
      Q2.hcardT97_35_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T97_35_2 i) (Q2.hfix97_35_2 i) _)
      ?_).symm
  rw [show colData1 (⟨97, by decide⟩ : Fin 148)
        ((colE1 ⟨35, by decide⟩ 20 (transLenTr ⟨35, by decide⟩ 20 hp) : ↥(reps ⟨35, by decide⟩)) : Coordinate 1)
        T97_35 = colFn colCertDiv_97_35_20.D1 (m := 25) from colCertDiv_97_35_20.bind1,
    show colData2 (⟨97, by decide⟩ : Fin 148)
        ((colE2 ⟨35, by decide⟩ 20 hp : ↥(Q2.reps ⟨35, by decide⟩)) : Coordinate 2)
        Q2.T97_35_2 = colFn colCertDiv_97_35_20.D2 (m := 25) from colCertDiv_97_35_20.bind2]
  rw [alnId_97 j hj]
  exact fastcode_of_div ⟨97, by decide⟩ _ _ _
    ((alnId_97 j hj) ▸ Q2.listedAt (⟨97, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨97, by decide⟩ : Fin 148) hj hq).1) colCertDiv_97_35_20_match


theorem leaf_97_53_0 (hp : 0 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 97 []).length)
    (hq : (normIsRep.getD 97 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 0 hp)
        (rowE2 (⟨97, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 0 (transLenTr ⟨53, by decide⟩ 0 hp))
        (rowE1 (⟨97, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨97, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨97, by decide⟩ (listedAt ⟨97, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 0 (transLenTr ⟨53, by decide⟩ 0 hp)) T97_53
      hfix97_53 hinj97_53 hcardT97_53
      (fun i => conj_mem_of_fixedPoints _ _ (T97_53 i) (hfix97_53 i) _)
      ⟨97, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨97, by decide⟩ (Q2.listedAt ⟨97, by decide⟩
        (alnCheck_rep ⟨97, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 0 hp) Q2.T97_53_2 Q2.hfix97_53_2 Q2.hinj97_53_2
      Q2.hcardT97_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T97_53_2 i) (Q2.hfix97_53_2 i) _)
      colCert_97_53_0.hD ?_).symm
  rw [alnId_97 j hj]


theorem leaf_97_53_1 (hp : 1 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 97 []).length)
    (hq : (normIsRep.getD 97 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 1 hp)
        (rowE2 (⟨97, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 1 (transLenTr ⟨53, by decide⟩ 1 hp))
        (rowE1 (⟨97, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨97, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨97, by decide⟩ (listedAt ⟨97, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 1 (transLenTr ⟨53, by decide⟩ 1 hp)) T97_53
      hfix97_53 hinj97_53 hcardT97_53
      (fun i => conj_mem_of_fixedPoints _ _ (T97_53 i) (hfix97_53 i) _)
      ⟨97, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨97, by decide⟩ (Q2.listedAt ⟨97, by decide⟩
        (alnCheck_rep ⟨97, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 1 hp) Q2.T97_53_2 Q2.hfix97_53_2 Q2.hinj97_53_2
      Q2.hcardT97_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T97_53_2 i) (Q2.hfix97_53_2 i) _)
      colCert_97_53_1.hD ?_).symm
  rw [alnId_97 j hj]


theorem leaf_97_53_2 (hp : 2 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 97 []).length)
    (hq : (normIsRep.getD 97 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 2 hp)
        (rowE2 (⟨97, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 2 (transLenTr ⟨53, by decide⟩ 2 hp))
        (rowE1 (⟨97, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨97, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨97, by decide⟩ (listedAt ⟨97, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 2 (transLenTr ⟨53, by decide⟩ 2 hp)) T97_53
      hfix97_53 hinj97_53 hcardT97_53
      (fun i => conj_mem_of_fixedPoints _ _ (T97_53 i) (hfix97_53 i) _)
      ⟨97, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨97, by decide⟩ (Q2.listedAt ⟨97, by decide⟩
        (alnCheck_rep ⟨97, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 2 hp) Q2.T97_53_2 Q2.hfix97_53_2 Q2.hinj97_53_2
      Q2.hcardT97_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T97_53_2 i) (Q2.hfix97_53_2 i) _)
      colCert_97_53_2.hD ?_).symm
  rw [alnId_97 j hj]


theorem leaf_97_53_3 (hp : 3 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 97 []).length)
    (hq : (normIsRep.getD 97 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 3 hp)
        (rowE2 (⟨97, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 3 (transLenTr ⟨53, by decide⟩ 3 hp))
        (rowE1 (⟨97, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨97, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨97, by decide⟩ (listedAt ⟨97, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 3 (transLenTr ⟨53, by decide⟩ 3 hp)) T97_53
      hfix97_53 hinj97_53 hcardT97_53
      (fun i => conj_mem_of_fixedPoints _ _ (T97_53 i) (hfix97_53 i) _)
      ⟨97, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨97, by decide⟩ (Q2.listedAt ⟨97, by decide⟩
        (alnCheck_rep ⟨97, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 3 hp) Q2.T97_53_2 Q2.hfix97_53_2 Q2.hinj97_53_2
      Q2.hcardT97_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T97_53_2 i) (Q2.hfix97_53_2 i) _)
      colCert_97_53_3.hD ?_).symm
  rw [alnId_97 j hj]


theorem leaf_97_53_4 (hp : 4 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 97 []).length)
    (hq : (normIsRep.getD 97 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 4 hp)
        (rowE2 (⟨97, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 4 (transLenTr ⟨53, by decide⟩ 4 hp))
        (rowE1 (⟨97, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨97, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨97, by decide⟩ (listedAt ⟨97, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 4 (transLenTr ⟨53, by decide⟩ 4 hp)) T97_53
      hfix97_53 hinj97_53 hcardT97_53
      (fun i => conj_mem_of_fixedPoints _ _ (T97_53 i) (hfix97_53 i) _)
      ⟨97, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨97, by decide⟩ (Q2.listedAt ⟨97, by decide⟩
        (alnCheck_rep ⟨97, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 4 hp) Q2.T97_53_2 Q2.hfix97_53_2 Q2.hinj97_53_2
      Q2.hcardT97_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T97_53_2 i) (Q2.hfix97_53_2 i) _)
      colCert_97_53_4.hD ?_).symm
  rw [alnId_97 j hj]


theorem leaf_97_53_5 (hp : 5 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 97 []).length)
    (hq : (normIsRep.getD 97 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 5 hp)
        (rowE2 (⟨97, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 5 (transLenTr ⟨53, by decide⟩ 5 hp))
        (rowE1 (⟨97, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨97, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨97, by decide⟩ (listedAt ⟨97, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 5 (transLenTr ⟨53, by decide⟩ 5 hp)) T97_53
      hfix97_53 hinj97_53 hcardT97_53
      (fun i => conj_mem_of_fixedPoints _ _ (T97_53 i) (hfix97_53 i) _)
      ⟨97, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨97, by decide⟩ (Q2.listedAt ⟨97, by decide⟩
        (alnCheck_rep ⟨97, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 5 hp) Q2.T97_53_2 Q2.hfix97_53_2 Q2.hinj97_53_2
      Q2.hcardT97_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T97_53_2 i) (Q2.hfix97_53_2 i) _)
      colCert_97_53_5.hD ?_).symm
  rw [alnId_97 j hj]


theorem leaf_97_53_10 (hp : 10 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 97 []).length)
    (hq : (normIsRep.getD 97 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 10 hp)
        (rowE2 (⟨97, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 10 (transLenTr ⟨53, by decide⟩ 10 hp))
        (rowE1 (⟨97, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨97, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨97, by decide⟩ (listedAt ⟨97, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 10 (transLenTr ⟨53, by decide⟩ 10 hp)) T97_53
      hfix97_53 hinj97_53 hcardT97_53
      (fun i => conj_mem_of_fixedPoints _ _ (T97_53 i) (hfix97_53 i) _)
      ⟨97, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨97, by decide⟩ (Q2.listedAt ⟨97, by decide⟩
        (alnCheck_rep ⟨97, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 10 hp) Q2.T97_53_2 Q2.hfix97_53_2 Q2.hinj97_53_2
      Q2.hcardT97_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T97_53_2 i) (Q2.hfix97_53_2 i) _)
      colCert_97_53_10.hD ?_).symm
  rw [alnId_97 j hj]


theorem leaf_97_53_15 (hp : 15 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 97 []).length)
    (hq : (normIsRep.getD 97 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 15 hp)
        (rowE2 (⟨97, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 15 (transLenTr ⟨53, by decide⟩ 15 hp))
        (rowE1 (⟨97, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨97, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨97, by decide⟩ (listedAt ⟨97, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 15 (transLenTr ⟨53, by decide⟩ 15 hp)) T97_53
      hfix97_53 hinj97_53 hcardT97_53
      (fun i => conj_mem_of_fixedPoints _ _ (T97_53 i) (hfix97_53 i) _)
      ⟨97, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨97, by decide⟩ (Q2.listedAt ⟨97, by decide⟩
        (alnCheck_rep ⟨97, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 15 hp) Q2.T97_53_2 Q2.hfix97_53_2 Q2.hinj97_53_2
      Q2.hcardT97_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T97_53_2 i) (Q2.hfix97_53_2 i) _)
      colCert_97_53_15.hD ?_).symm
  rw [alnId_97 j hj]


theorem leaf_97_53_20 (hp : 20 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 97 []).length)
    (hq : (normIsRep.getD 97 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 20 hp)
        (rowE2 (⟨97, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 20 (transLenTr ⟨53, by decide⟩ 20 hp))
        (rowE1 (⟨97, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨97, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨97, by decide⟩ (listedAt ⟨97, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 20 (transLenTr ⟨53, by decide⟩ 20 hp)) T97_53
      hfix97_53 hinj97_53 hcardT97_53
      (fun i => conj_mem_of_fixedPoints _ _ (T97_53 i) (hfix97_53 i) _)
      ⟨97, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨97, by decide⟩ (Q2.listedAt ⟨97, by decide⟩
        (alnCheck_rep ⟨97, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 20 hp) Q2.T97_53_2 Q2.hfix97_53_2 Q2.hinj97_53_2
      Q2.hcardT97_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T97_53_2 i) (Q2.hfix97_53_2 i) _)
      colCert_97_53_20.hD ?_).symm
  rw [alnId_97 j hj]


theorem leaf_97_97_0 (hp : 0 < (Q2.transData.getD 97 []).length)
    (j : Nat) (hj : j < (repChars.getD 97 []).length)
    (hq : (normIsRep.getD 97 []).getD j false = true) :
    species (Q2.reps (⟨97, by decide⟩ : Fin 148)) (colE2 ⟨97, by decide⟩ 0 hp)
        (rowE2 (⟨97, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨97, by decide⟩ : Fin 148))
        (colE1 ⟨97, by decide⟩ 0 (transLenTr ⟨97, by decide⟩ 0 hp))
        (rowE1 (⟨97, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨97, by decide⟩ : Fin 148) ⟨97, by decide⟩ _
      (validAt ⟨97, by decide⟩ (listedAt ⟨97, by decide⟩ hj))
      (colE1 ⟨97, by decide⟩ 0 (transLenTr ⟨97, by decide⟩ 0 hp)) T97_97
      hfix97_97 hinj97_97 hcardT97_97
      (fun i => conj_mem_of_fixedPoints _ _ (T97_97 i) (hfix97_97 i) _)
      ⟨97, by decide⟩ ⟨97, by decide⟩ _
      (Q2.validAt ⟨97, by decide⟩ (Q2.listedAt ⟨97, by decide⟩
        (alnCheck_rep ⟨97, by decide⟩ hj hq).1))
      (colE2 ⟨97, by decide⟩ 0 hp) Q2.T97_97_2 Q2.hfix97_97_2 Q2.hinj97_97_2
      Q2.hcardT97_97_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T97_97_2 i) (Q2.hfix97_97_2 i) _)
      colCert_97_97_0.hD ?_).symm
  rw [alnId_97 j hj]


theorem leaf_97_97_1 (hp : 1 < (Q2.transData.getD 97 []).length)
    (j : Nat) (hj : j < (repChars.getD 97 []).length)
    (hq : (normIsRep.getD 97 []).getD j false = true) :
    species (Q2.reps (⟨97, by decide⟩ : Fin 148)) (colE2 ⟨97, by decide⟩ 1 hp)
        (rowE2 (⟨97, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨97, by decide⟩ : Fin 148))
        (colE1 ⟨97, by decide⟩ 1 (transLenTr ⟨97, by decide⟩ 1 hp))
        (rowE1 (⟨97, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨97, by decide⟩ : Fin 148) ⟨97, by decide⟩ _
      (validAt ⟨97, by decide⟩ (listedAt ⟨97, by decide⟩ hj))
      (colE1 ⟨97, by decide⟩ 1 (transLenTr ⟨97, by decide⟩ 1 hp)) T97_97
      hfix97_97 hinj97_97 hcardT97_97
      (fun i => conj_mem_of_fixedPoints _ _ (T97_97 i) (hfix97_97 i) _)
      ⟨97, by decide⟩ ⟨97, by decide⟩ _
      (Q2.validAt ⟨97, by decide⟩ (Q2.listedAt ⟨97, by decide⟩
        (alnCheck_rep ⟨97, by decide⟩ hj hq).1))
      (colE2 ⟨97, by decide⟩ 1 hp) Q2.T97_97_2 Q2.hfix97_97_2 Q2.hinj97_97_2
      Q2.hcardT97_97_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T97_97_2 i) (Q2.hfix97_97_2 i) _)
      colCert_97_97_1.hD ?_).symm
  rw [alnId_97 j hj]


theorem leaf_97_97_2 (hp : 2 < (Q2.transData.getD 97 []).length)
    (j : Nat) (hj : j < (repChars.getD 97 []).length)
    (hq : (normIsRep.getD 97 []).getD j false = true) :
    species (Q2.reps (⟨97, by decide⟩ : Fin 148)) (colE2 ⟨97, by decide⟩ 2 hp)
        (rowE2 (⟨97, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨97, by decide⟩ : Fin 148))
        (colE1 ⟨97, by decide⟩ 2 (transLenTr ⟨97, by decide⟩ 2 hp))
        (rowE1 (⟨97, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨97, by decide⟩ : Fin 148) ⟨97, by decide⟩ _
      (validAt ⟨97, by decide⟩ (listedAt ⟨97, by decide⟩ hj))
      (colE1 ⟨97, by decide⟩ 2 (transLenTr ⟨97, by decide⟩ 2 hp)) T97_97
      hfix97_97 hinj97_97 hcardT97_97
      (fun i => conj_mem_of_fixedPoints _ _ (T97_97 i) (hfix97_97 i) _)
      ⟨97, by decide⟩ ⟨97, by decide⟩ _
      (Q2.validAt ⟨97, by decide⟩ (Q2.listedAt ⟨97, by decide⟩
        (alnCheck_rep ⟨97, by decide⟩ hj hq).1))
      (colE2 ⟨97, by decide⟩ 2 hp) Q2.T97_97_2 Q2.hfix97_97_2 Q2.hinj97_97_2
      Q2.hcardT97_97_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T97_97_2 i) (Q2.hfix97_97_2 i) _)
      colCert_97_97_2.hD ?_).symm
  rw [alnId_97 j hj]


theorem leaf_97_97_3 (hp : 3 < (Q2.transData.getD 97 []).length)
    (j : Nat) (hj : j < (repChars.getD 97 []).length)
    (hq : (normIsRep.getD 97 []).getD j false = true) :
    species (Q2.reps (⟨97, by decide⟩ : Fin 148)) (colE2 ⟨97, by decide⟩ 3 hp)
        (rowE2 (⟨97, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨97, by decide⟩ : Fin 148))
        (colE1 ⟨97, by decide⟩ 3 (transLenTr ⟨97, by decide⟩ 3 hp))
        (rowE1 (⟨97, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨97, by decide⟩ : Fin 148) ⟨97, by decide⟩ _
      (validAt ⟨97, by decide⟩ (listedAt ⟨97, by decide⟩ hj))
      (colE1 ⟨97, by decide⟩ 3 (transLenTr ⟨97, by decide⟩ 3 hp)) T97_97
      hfix97_97 hinj97_97 hcardT97_97
      (fun i => conj_mem_of_fixedPoints _ _ (T97_97 i) (hfix97_97 i) _)
      ⟨97, by decide⟩ ⟨97, by decide⟩ _
      (Q2.validAt ⟨97, by decide⟩ (Q2.listedAt ⟨97, by decide⟩
        (alnCheck_rep ⟨97, by decide⟩ hj hq).1))
      (colE2 ⟨97, by decide⟩ 3 hp) Q2.T97_97_2 Q2.hfix97_97_2 Q2.hinj97_97_2
      Q2.hcardT97_97_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T97_97_2 i) (Q2.hfix97_97_2 i) _)
      colCert_97_97_3.hD ?_).symm
  rw [alnId_97 j hj]


theorem leaf_97_97_4 (hp : 4 < (Q2.transData.getD 97 []).length)
    (j : Nat) (hj : j < (repChars.getD 97 []).length)
    (hq : (normIsRep.getD 97 []).getD j false = true) :
    species (Q2.reps (⟨97, by decide⟩ : Fin 148)) (colE2 ⟨97, by decide⟩ 4 hp)
        (rowE2 (⟨97, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨97, by decide⟩ : Fin 148))
        (colE1 ⟨97, by decide⟩ 4 (transLenTr ⟨97, by decide⟩ 4 hp))
        (rowE1 (⟨97, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨97, by decide⟩ : Fin 148) ⟨97, by decide⟩ _
      (validAt ⟨97, by decide⟩ (listedAt ⟨97, by decide⟩ hj))
      (colE1 ⟨97, by decide⟩ 4 (transLenTr ⟨97, by decide⟩ 4 hp)) T97_97
      hfix97_97 hinj97_97 hcardT97_97
      (fun i => conj_mem_of_fixedPoints _ _ (T97_97 i) (hfix97_97 i) _)
      ⟨97, by decide⟩ ⟨97, by decide⟩ _
      (Q2.validAt ⟨97, by decide⟩ (Q2.listedAt ⟨97, by decide⟩
        (alnCheck_rep ⟨97, by decide⟩ hj hq).1))
      (colE2 ⟨97, by decide⟩ 4 hp) Q2.T97_97_2 Q2.hfix97_97_2 Q2.hinj97_97_2
      Q2.hcardT97_97_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T97_97_2 i) (Q2.hfix97_97_2 i) _)
      colCert_97_97_4.hD ?_).symm
  rw [alnId_97 j hj]


theorem leaf_97_97_5 (hp : 5 < (Q2.transData.getD 97 []).length)
    (j : Nat) (hj : j < (repChars.getD 97 []).length)
    (hq : (normIsRep.getD 97 []).getD j false = true) :
    species (Q2.reps (⟨97, by decide⟩ : Fin 148)) (colE2 ⟨97, by decide⟩ 5 hp)
        (rowE2 (⟨97, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨97, by decide⟩ : Fin 148))
        (colE1 ⟨97, by decide⟩ 5 (transLenTr ⟨97, by decide⟩ 5 hp))
        (rowE1 (⟨97, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨97, by decide⟩ : Fin 148) ⟨97, by decide⟩ _
      (validAt ⟨97, by decide⟩ (listedAt ⟨97, by decide⟩ hj))
      (colE1 ⟨97, by decide⟩ 5 (transLenTr ⟨97, by decide⟩ 5 hp)) T97_97
      hfix97_97 hinj97_97 hcardT97_97
      (fun i => conj_mem_of_fixedPoints _ _ (T97_97 i) (hfix97_97 i) _)
      ⟨97, by decide⟩ ⟨97, by decide⟩ _
      (Q2.validAt ⟨97, by decide⟩ (Q2.listedAt ⟨97, by decide⟩
        (alnCheck_rep ⟨97, by decide⟩ hj hq).1))
      (colE2 ⟨97, by decide⟩ 5 hp) Q2.T97_97_2 Q2.hfix97_97_2 Q2.hinj97_97_2
      Q2.hcardT97_97_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T97_97_2 i) (Q2.hfix97_97_2 i) _)
      colCert_97_97_5.hD ?_).symm
  rw [alnId_97 j hj]


theorem leaf_97_97_10 (hp : 10 < (Q2.transData.getD 97 []).length)
    (j : Nat) (hj : j < (repChars.getD 97 []).length)
    (hq : (normIsRep.getD 97 []).getD j false = true) :
    species (Q2.reps (⟨97, by decide⟩ : Fin 148)) (colE2 ⟨97, by decide⟩ 10 hp)
        (rowE2 (⟨97, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨97, by decide⟩ : Fin 148))
        (colE1 ⟨97, by decide⟩ 10 (transLenTr ⟨97, by decide⟩ 10 hp))
        (rowE1 (⟨97, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨97, by decide⟩ : Fin 148) ⟨97, by decide⟩ _
      (validAt ⟨97, by decide⟩ (listedAt ⟨97, by decide⟩ hj))
      (colE1 ⟨97, by decide⟩ 10 (transLenTr ⟨97, by decide⟩ 10 hp)) T97_97
      hfix97_97 hinj97_97 hcardT97_97
      (fun i => conj_mem_of_fixedPoints _ _ (T97_97 i) (hfix97_97 i) _)
      ⟨97, by decide⟩ ⟨97, by decide⟩ _
      (Q2.validAt ⟨97, by decide⟩ (Q2.listedAt ⟨97, by decide⟩
        (alnCheck_rep ⟨97, by decide⟩ hj hq).1))
      (colE2 ⟨97, by decide⟩ 10 hp) Q2.T97_97_2 Q2.hfix97_97_2 Q2.hinj97_97_2
      Q2.hcardT97_97_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T97_97_2 i) (Q2.hfix97_97_2 i) _)
      colCert_97_97_10.hD ?_).symm
  rw [alnId_97 j hj]


theorem leaf_97_97_15 (hp : 15 < (Q2.transData.getD 97 []).length)
    (j : Nat) (hj : j < (repChars.getD 97 []).length)
    (hq : (normIsRep.getD 97 []).getD j false = true) :
    species (Q2.reps (⟨97, by decide⟩ : Fin 148)) (colE2 ⟨97, by decide⟩ 15 hp)
        (rowE2 (⟨97, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨97, by decide⟩ : Fin 148))
        (colE1 ⟨97, by decide⟩ 15 (transLenTr ⟨97, by decide⟩ 15 hp))
        (rowE1 (⟨97, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨97, by decide⟩ : Fin 148) ⟨97, by decide⟩ _
      (validAt ⟨97, by decide⟩ (listedAt ⟨97, by decide⟩ hj))
      (colE1 ⟨97, by decide⟩ 15 (transLenTr ⟨97, by decide⟩ 15 hp)) T97_97
      hfix97_97 hinj97_97 hcardT97_97
      (fun i => conj_mem_of_fixedPoints _ _ (T97_97 i) (hfix97_97 i) _)
      ⟨97, by decide⟩ ⟨97, by decide⟩ _
      (Q2.validAt ⟨97, by decide⟩ (Q2.listedAt ⟨97, by decide⟩
        (alnCheck_rep ⟨97, by decide⟩ hj hq).1))
      (colE2 ⟨97, by decide⟩ 15 hp) Q2.T97_97_2 Q2.hfix97_97_2 Q2.hinj97_97_2
      Q2.hcardT97_97_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T97_97_2 i) (Q2.hfix97_97_2 i) _)
      colCert_97_97_15.hD ?_).symm
  rw [alnId_97 j hj]


theorem leaf_97_97_20 (hp : 20 < (Q2.transData.getD 97 []).length)
    (j : Nat) (hj : j < (repChars.getD 97 []).length)
    (hq : (normIsRep.getD 97 []).getD j false = true) :
    species (Q2.reps (⟨97, by decide⟩ : Fin 148)) (colE2 ⟨97, by decide⟩ 20 hp)
        (rowE2 (⟨97, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨97, by decide⟩ : Fin 148))
        (colE1 ⟨97, by decide⟩ 20 (transLenTr ⟨97, by decide⟩ 20 hp))
        (rowE1 (⟨97, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨97, by decide⟩ : Fin 148) ⟨97, by decide⟩ _
      (validAt ⟨97, by decide⟩ (listedAt ⟨97, by decide⟩ hj))
      (colE1 ⟨97, by decide⟩ 20 (transLenTr ⟨97, by decide⟩ 20 hp)) T97_97
      hfix97_97 hinj97_97 hcardT97_97
      (fun i => conj_mem_of_fixedPoints _ _ (T97_97 i) (hfix97_97 i) _)
      ⟨97, by decide⟩ ⟨97, by decide⟩ _
      (Q2.validAt ⟨97, by decide⟩ (Q2.listedAt ⟨97, by decide⟩
        (alnCheck_rep ⟨97, by decide⟩ hj hq).1))
      (colE2 ⟨97, by decide⟩ 20 hp) Q2.T97_97_2 Q2.hfix97_97_2 Q2.hinj97_97_2
      Q2.hcardT97_97_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T97_97_2 i) (Q2.hfix97_97_2 i) _)
      colCert_97_97_20.hD ?_).symm
  rw [alnId_97 j hj]


theorem leaf_98_10_0 (hp : 0 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 98 []).length)
    (hq : (normIsRep.getD 98 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 0 hp)
        (rowE2 (⟨98, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 0 (transLenTr ⟨10, by decide⟩ 0 hp))
        (rowE1 (⟨98, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨98, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨98, by decide⟩ (listedAt ⟨98, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 0 (transLenTr ⟨10, by decide⟩ 0 hp)) T98_10
      hfix98_10 hinj98_10 hcardT98_10
      (fun i => conj_mem_of_fixedPoints _ _ (T98_10 i) (hfix98_10 i) _)
      ⟨98, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨98, by decide⟩ (Q2.listedAt ⟨98, by decide⟩
        (alnCheck_rep ⟨98, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 0 hp) Q2.T98_10_2 Q2.hfix98_10_2 Q2.hinj98_10_2
      Q2.hcardT98_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T98_10_2 i) (Q2.hfix98_10_2 i) _)
      colCert_98_10_0.hD ?_).symm
  rw [alnId_98 j hj]


theorem leaf_98_10_1 (hp : 1 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 98 []).length)
    (hq : (normIsRep.getD 98 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 1 hp)
        (rowE2 (⟨98, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 1 (transLenTr ⟨10, by decide⟩ 1 hp))
        (rowE1 (⟨98, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨98, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨98, by decide⟩ (listedAt ⟨98, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 1 (transLenTr ⟨10, by decide⟩ 1 hp)) T98_10
      hfix98_10 hinj98_10 hcardT98_10
      (fun i => conj_mem_of_fixedPoints _ _ (T98_10 i) (hfix98_10 i) _)
      ⟨98, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨98, by decide⟩ (Q2.listedAt ⟨98, by decide⟩
        (alnCheck_rep ⟨98, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 1 hp) Q2.T98_10_2 Q2.hfix98_10_2 Q2.hinj98_10_2
      Q2.hcardT98_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T98_10_2 i) (Q2.hfix98_10_2 i) _)
      colCert_98_10_1.hD ?_).symm
  rw [alnId_98 j hj]


theorem leaf_98_10_2 (hp : 2 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 98 []).length)
    (hq : (normIsRep.getD 98 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 2 hp)
        (rowE2 (⟨98, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 2 (transLenTr ⟨10, by decide⟩ 2 hp))
        (rowE1 (⟨98, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨98, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨98, by decide⟩ (listedAt ⟨98, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 2 (transLenTr ⟨10, by decide⟩ 2 hp)) T98_10
      hfix98_10 hinj98_10 hcardT98_10
      (fun i => conj_mem_of_fixedPoints _ _ (T98_10 i) (hfix98_10 i) _)
      ⟨98, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨98, by decide⟩ (Q2.listedAt ⟨98, by decide⟩
        (alnCheck_rep ⟨98, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 2 hp) Q2.T98_10_2 Q2.hfix98_10_2 Q2.hinj98_10_2
      Q2.hcardT98_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T98_10_2 i) (Q2.hfix98_10_2 i) _)
      colCert_98_10_2.hD ?_).symm
  rw [alnId_98 j hj]


theorem leaf_98_10_3 (hp : 3 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 98 []).length)
    (hq : (normIsRep.getD 98 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 3 hp)
        (rowE2 (⟨98, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 3 (transLenTr ⟨10, by decide⟩ 3 hp))
        (rowE1 (⟨98, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨98, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨98, by decide⟩ (listedAt ⟨98, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 3 (transLenTr ⟨10, by decide⟩ 3 hp)) T98_10
      hfix98_10 hinj98_10 hcardT98_10
      (fun i => conj_mem_of_fixedPoints _ _ (T98_10 i) (hfix98_10 i) _)
      ⟨98, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨98, by decide⟩ (Q2.listedAt ⟨98, by decide⟩
        (alnCheck_rep ⟨98, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 3 hp) Q2.T98_10_2 Q2.hfix98_10_2 Q2.hinj98_10_2
      Q2.hcardT98_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T98_10_2 i) (Q2.hfix98_10_2 i) _)
      colCert_98_10_3.hD ?_).symm
  rw [alnId_98 j hj]


theorem leaf_98_10_4 (hp : 4 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 98 []).length)
    (hq : (normIsRep.getD 98 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 4 hp)
        (rowE2 (⟨98, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 4 (transLenTr ⟨10, by decide⟩ 4 hp))
        (rowE1 (⟨98, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨98, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨98, by decide⟩ (listedAt ⟨98, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 4 (transLenTr ⟨10, by decide⟩ 4 hp)) T98_10
      hfix98_10 hinj98_10 hcardT98_10
      (fun i => conj_mem_of_fixedPoints _ _ (T98_10 i) (hfix98_10 i) _)
      ⟨98, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨98, by decide⟩ (Q2.listedAt ⟨98, by decide⟩
        (alnCheck_rep ⟨98, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 4 hp) Q2.T98_10_2 Q2.hfix98_10_2 Q2.hinj98_10_2
      Q2.hcardT98_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T98_10_2 i) (Q2.hfix98_10_2 i) _)
      colCert_98_10_4.hD ?_).symm
  rw [alnId_98 j hj]


theorem leaf_98_12_0 (hp : 0 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 98 []).length)
    (hq : (normIsRep.getD 98 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 0 hp)
        (rowE2 (⟨98, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp))
        (rowE1 (⟨98, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨98, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨98, by decide⟩ (listedAt ⟨98, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp)) T98_12
      hfix98_12 hinj98_12 hcardT98_12
      (fun i => conj_mem_of_fixedPoints _ _ (T98_12 i) (hfix98_12 i) _)
      ⟨98, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨98, by decide⟩ (Q2.listedAt ⟨98, by decide⟩
        (alnCheck_rep ⟨98, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 0 hp) Q2.T98_12_2 Q2.hfix98_12_2 Q2.hinj98_12_2
      Q2.hcardT98_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T98_12_2 i) (Q2.hfix98_12_2 i) _)
      colCert_98_12_0.hD ?_).symm
  rw [alnId_98 j hj]


theorem leaf_98_12_1 (hp : 1 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 98 []).length)
    (hq : (normIsRep.getD 98 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 1 hp)
        (rowE2 (⟨98, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp))
        (rowE1 (⟨98, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨98, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨98, by decide⟩ (listedAt ⟨98, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp)) T98_12
      hfix98_12 hinj98_12 hcardT98_12
      (fun i => conj_mem_of_fixedPoints _ _ (T98_12 i) (hfix98_12 i) _)
      ⟨98, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨98, by decide⟩ (Q2.listedAt ⟨98, by decide⟩
        (alnCheck_rep ⟨98, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 1 hp) Q2.T98_12_2 Q2.hfix98_12_2 Q2.hinj98_12_2
      Q2.hcardT98_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T98_12_2 i) (Q2.hfix98_12_2 i) _)
      colCert_98_12_1.hD ?_).symm
  rw [alnId_98 j hj]


theorem leaf_98_12_2 (hp : 2 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 98 []).length)
    (hq : (normIsRep.getD 98 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 2 hp)
        (rowE2 (⟨98, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp))
        (rowE1 (⟨98, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨98, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨98, by decide⟩ (listedAt ⟨98, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp)) T98_12
      hfix98_12 hinj98_12 hcardT98_12
      (fun i => conj_mem_of_fixedPoints _ _ (T98_12 i) (hfix98_12 i) _)
      ⟨98, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨98, by decide⟩ (Q2.listedAt ⟨98, by decide⟩
        (alnCheck_rep ⟨98, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 2 hp) Q2.T98_12_2 Q2.hfix98_12_2 Q2.hinj98_12_2
      Q2.hcardT98_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T98_12_2 i) (Q2.hfix98_12_2 i) _)
      colCert_98_12_2.hD ?_).symm
  rw [alnId_98 j hj]


theorem leaf_98_12_3 (hp : 3 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 98 []).length)
    (hq : (normIsRep.getD 98 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 3 hp)
        (rowE2 (⟨98, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp))
        (rowE1 (⟨98, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨98, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨98, by decide⟩ (listedAt ⟨98, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp)) T98_12
      hfix98_12 hinj98_12 hcardT98_12
      (fun i => conj_mem_of_fixedPoints _ _ (T98_12 i) (hfix98_12 i) _)
      ⟨98, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨98, by decide⟩ (Q2.listedAt ⟨98, by decide⟩
        (alnCheck_rep ⟨98, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 3 hp) Q2.T98_12_2 Q2.hfix98_12_2 Q2.hinj98_12_2
      Q2.hcardT98_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T98_12_2 i) (Q2.hfix98_12_2 i) _)
      colCert_98_12_3.hD ?_).symm
  rw [alnId_98 j hj]


theorem leaf_98_12_4 (hp : 4 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 98 []).length)
    (hq : (normIsRep.getD 98 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 4 hp)
        (rowE2 (⟨98, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp))
        (rowE1 (⟨98, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨98, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨98, by decide⟩ (listedAt ⟨98, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp)) T98_12
      hfix98_12 hinj98_12 hcardT98_12
      (fun i => conj_mem_of_fixedPoints _ _ (T98_12 i) (hfix98_12 i) _)
      ⟨98, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨98, by decide⟩ (Q2.listedAt ⟨98, by decide⟩
        (alnCheck_rep ⟨98, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 4 hp) Q2.T98_12_2 Q2.hfix98_12_2 Q2.hinj98_12_2
      Q2.hcardT98_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T98_12_2 i) (Q2.hfix98_12_2 i) _)
      colCert_98_12_4.hD ?_).symm
  rw [alnId_98 j hj]


theorem leaf_98_36_0 (hp : 0 < (Q2.transData.getD 36 []).length)
    (j : Nat) (hj : j < (repChars.getD 98 []).length)
    (hq : (normIsRep.getD 98 []).getD j false = true) :
    species (Q2.reps (⟨36, by decide⟩ : Fin 148)) (colE2 ⟨36, by decide⟩ 0 hp)
        (rowE2 (⟨98, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨36, by decide⟩ : Fin 148))
        (colE1 ⟨36, by decide⟩ 0 (transLenTr ⟨36, by decide⟩ 0 hp))
        (rowE1 (⟨98, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨98, by decide⟩ : Fin 148) ⟨36, by decide⟩ _
      (validAt ⟨98, by decide⟩ (listedAt ⟨98, by decide⟩ hj))
      (colE1 ⟨36, by decide⟩ 0 (transLenTr ⟨36, by decide⟩ 0 hp)) T98_36
      hfix98_36 hinj98_36 hcardT98_36
      (fun i => conj_mem_of_fixedPoints _ _ (T98_36 i) (hfix98_36 i) _)
      ⟨98, by decide⟩ ⟨36, by decide⟩ _
      (Q2.validAt ⟨98, by decide⟩ (Q2.listedAt ⟨98, by decide⟩
        (alnCheck_rep ⟨98, by decide⟩ hj hq).1))
      (colE2 ⟨36, by decide⟩ 0 hp) Q2.T98_36_2 Q2.hfix98_36_2 Q2.hinj98_36_2
      Q2.hcardT98_36_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T98_36_2 i) (Q2.hfix98_36_2 i) _)
      colCert_98_36_0.hD ?_).symm
  rw [alnId_98 j hj]


theorem leaf_98_36_1 (hp : 1 < (Q2.transData.getD 36 []).length)
    (j : Nat) (hj : j < (repChars.getD 98 []).length)
    (hq : (normIsRep.getD 98 []).getD j false = true) :
    species (Q2.reps (⟨36, by decide⟩ : Fin 148)) (colE2 ⟨36, by decide⟩ 1 hp)
        (rowE2 (⟨98, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨36, by decide⟩ : Fin 148))
        (colE1 ⟨36, by decide⟩ 1 (transLenTr ⟨36, by decide⟩ 1 hp))
        (rowE1 (⟨98, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨98, by decide⟩ : Fin 148) ⟨36, by decide⟩ _
      (validAt ⟨98, by decide⟩ (listedAt ⟨98, by decide⟩ hj))
      (colE1 ⟨36, by decide⟩ 1 (transLenTr ⟨36, by decide⟩ 1 hp)) T98_36
      hfix98_36 hinj98_36 hcardT98_36
      (fun i => conj_mem_of_fixedPoints _ _ (T98_36 i) (hfix98_36 i) _)
      ⟨98, by decide⟩ ⟨36, by decide⟩ _
      (Q2.validAt ⟨98, by decide⟩ (Q2.listedAt ⟨98, by decide⟩
        (alnCheck_rep ⟨98, by decide⟩ hj hq).1))
      (colE2 ⟨36, by decide⟩ 1 hp) Q2.T98_36_2 Q2.hfix98_36_2 Q2.hinj98_36_2
      Q2.hcardT98_36_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T98_36_2 i) (Q2.hfix98_36_2 i) _)
      colCert_98_36_1.hD ?_).symm
  rw [alnId_98 j hj]


theorem leaf_98_36_2 (hp : 2 < (Q2.transData.getD 36 []).length)
    (j : Nat) (hj : j < (repChars.getD 98 []).length)
    (hq : (normIsRep.getD 98 []).getD j false = true) :
    species (Q2.reps (⟨36, by decide⟩ : Fin 148)) (colE2 ⟨36, by decide⟩ 2 hp)
        (rowE2 (⟨98, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨36, by decide⟩ : Fin 148))
        (colE1 ⟨36, by decide⟩ 2 (transLenTr ⟨36, by decide⟩ 2 hp))
        (rowE1 (⟨98, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨98, by decide⟩ : Fin 148) ⟨36, by decide⟩ _
      (validAt ⟨98, by decide⟩ (listedAt ⟨98, by decide⟩ hj))
      (colE1 ⟨36, by decide⟩ 2 (transLenTr ⟨36, by decide⟩ 2 hp)) T98_36
      hfix98_36 hinj98_36 hcardT98_36
      (fun i => conj_mem_of_fixedPoints _ _ (T98_36 i) (hfix98_36 i) _)
      ⟨98, by decide⟩ ⟨36, by decide⟩ _
      (Q2.validAt ⟨98, by decide⟩ (Q2.listedAt ⟨98, by decide⟩
        (alnCheck_rep ⟨98, by decide⟩ hj hq).1))
      (colE2 ⟨36, by decide⟩ 2 hp) Q2.T98_36_2 Q2.hfix98_36_2 Q2.hinj98_36_2
      Q2.hcardT98_36_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T98_36_2 i) (Q2.hfix98_36_2 i) _)
      colCert_98_36_2.hD ?_).symm
  rw [alnId_98 j hj]


theorem leaf_98_36_3 (hp : 3 < (Q2.transData.getD 36 []).length)
    (j : Nat) (hj : j < (repChars.getD 98 []).length)
    (hq : (normIsRep.getD 98 []).getD j false = true) :
    species (Q2.reps (⟨36, by decide⟩ : Fin 148)) (colE2 ⟨36, by decide⟩ 3 hp)
        (rowE2 (⟨98, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨36, by decide⟩ : Fin 148))
        (colE1 ⟨36, by decide⟩ 3 (transLenTr ⟨36, by decide⟩ 3 hp))
        (rowE1 (⟨98, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨98, by decide⟩ : Fin 148) ⟨36, by decide⟩ _
      (validAt ⟨98, by decide⟩ (listedAt ⟨98, by decide⟩ hj))
      (colE1 ⟨36, by decide⟩ 3 (transLenTr ⟨36, by decide⟩ 3 hp)) T98_36
      hfix98_36 hinj98_36 hcardT98_36
      (fun i => conj_mem_of_fixedPoints _ _ (T98_36 i) (hfix98_36 i) _)
      ⟨98, by decide⟩ ⟨36, by decide⟩ _
      (Q2.validAt ⟨98, by decide⟩ (Q2.listedAt ⟨98, by decide⟩
        (alnCheck_rep ⟨98, by decide⟩ hj hq).1))
      (colE2 ⟨36, by decide⟩ 3 hp) Q2.T98_36_2 Q2.hfix98_36_2 Q2.hinj98_36_2
      Q2.hcardT98_36_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T98_36_2 i) (Q2.hfix98_36_2 i) _)
      colCert_98_36_3.hD ?_).symm
  rw [alnId_98 j hj]


theorem leaf_98_36_4 (hp : 4 < (Q2.transData.getD 36 []).length)
    (j : Nat) (hj : j < (repChars.getD 98 []).length)
    (hq : (normIsRep.getD 98 []).getD j false = true) :
    species (Q2.reps (⟨36, by decide⟩ : Fin 148)) (colE2 ⟨36, by decide⟩ 4 hp)
        (rowE2 (⟨98, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨36, by decide⟩ : Fin 148))
        (colE1 ⟨36, by decide⟩ 4 (transLenTr ⟨36, by decide⟩ 4 hp))
        (rowE1 (⟨98, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨98, by decide⟩ : Fin 148) ⟨36, by decide⟩ _
      (validAt ⟨98, by decide⟩ (listedAt ⟨98, by decide⟩ hj))
      (colE1 ⟨36, by decide⟩ 4 (transLenTr ⟨36, by decide⟩ 4 hp)) T98_36
      hfix98_36 hinj98_36 hcardT98_36
      (fun i => conj_mem_of_fixedPoints _ _ (T98_36 i) (hfix98_36 i) _)
      ⟨98, by decide⟩ ⟨36, by decide⟩ _
      (Q2.validAt ⟨98, by decide⟩ (Q2.listedAt ⟨98, by decide⟩
        (alnCheck_rep ⟨98, by decide⟩ hj hq).1))
      (colE2 ⟨36, by decide⟩ 4 hp) Q2.T98_36_2 Q2.hfix98_36_2 Q2.hinj98_36_2
      Q2.hcardT98_36_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T98_36_2 i) (Q2.hfix98_36_2 i) _)
      colCert_98_36_4.hD ?_).symm
  rw [alnId_98 j hj]


theorem leaf_98_36_5 (hp : 5 < (Q2.transData.getD 36 []).length)
    (j : Nat) (hj : j < (repChars.getD 98 []).length)
    (hq : (normIsRep.getD 98 []).getD j false = true) :
    species (Q2.reps (⟨36, by decide⟩ : Fin 148)) (colE2 ⟨36, by decide⟩ 5 hp)
        (rowE2 (⟨98, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨36, by decide⟩ : Fin 148))
        (colE1 ⟨36, by decide⟩ 5 (transLenTr ⟨36, by decide⟩ 5 hp))
        (rowE1 (⟨98, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨98, by decide⟩ : Fin 148) ⟨36, by decide⟩ _
      (validAt ⟨98, by decide⟩ (listedAt ⟨98, by decide⟩ hj))
      (colE1 ⟨36, by decide⟩ 5 (transLenTr ⟨36, by decide⟩ 5 hp)) T98_36
      hfix98_36 hinj98_36 hcardT98_36
      (fun i => conj_mem_of_fixedPoints _ _ (T98_36 i) (hfix98_36 i) _)
      ⟨98, by decide⟩ ⟨36, by decide⟩ _
      (Q2.validAt ⟨98, by decide⟩ (Q2.listedAt ⟨98, by decide⟩
        (alnCheck_rep ⟨98, by decide⟩ hj hq).1))
      (colE2 ⟨36, by decide⟩ 5 hp) Q2.T98_36_2 Q2.hfix98_36_2 Q2.hinj98_36_2
      Q2.hcardT98_36_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T98_36_2 i) (Q2.hfix98_36_2 i) _)
      ?_).symm
  rw [show colData1 (⟨98, by decide⟩ : Fin 148)
        ((colE1 ⟨36, by decide⟩ 5 (transLenTr ⟨36, by decide⟩ 5 hp) : ↥(reps ⟨36, by decide⟩)) : Coordinate 1)
        T98_36 = colFn colCertDiv_98_36_5.D1 (m := 25) from colCertDiv_98_36_5.bind1,
    show colData2 (⟨98, by decide⟩ : Fin 148)
        ((colE2 ⟨36, by decide⟩ 5 hp : ↥(Q2.reps ⟨36, by decide⟩)) : Coordinate 2)
        Q2.T98_36_2 = colFn colCertDiv_98_36_5.D2 (m := 25) from colCertDiv_98_36_5.bind2]
  rw [alnId_98 j hj]
  exact fastcode_of_div ⟨98, by decide⟩ _ _ _
    ((alnId_98 j hj) ▸ Q2.listedAt (⟨98, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨98, by decide⟩ : Fin 148) hj hq).1) colCertDiv_98_36_5_match


theorem leaf_98_36_10 (hp : 10 < (Q2.transData.getD 36 []).length)
    (j : Nat) (hj : j < (repChars.getD 98 []).length)
    (hq : (normIsRep.getD 98 []).getD j false = true) :
    species (Q2.reps (⟨36, by decide⟩ : Fin 148)) (colE2 ⟨36, by decide⟩ 10 hp)
        (rowE2 (⟨98, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨36, by decide⟩ : Fin 148))
        (colE1 ⟨36, by decide⟩ 10 (transLenTr ⟨36, by decide⟩ 10 hp))
        (rowE1 (⟨98, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨98, by decide⟩ : Fin 148) ⟨36, by decide⟩ _
      (validAt ⟨98, by decide⟩ (listedAt ⟨98, by decide⟩ hj))
      (colE1 ⟨36, by decide⟩ 10 (transLenTr ⟨36, by decide⟩ 10 hp)) T98_36
      hfix98_36 hinj98_36 hcardT98_36
      (fun i => conj_mem_of_fixedPoints _ _ (T98_36 i) (hfix98_36 i) _)
      ⟨98, by decide⟩ ⟨36, by decide⟩ _
      (Q2.validAt ⟨98, by decide⟩ (Q2.listedAt ⟨98, by decide⟩
        (alnCheck_rep ⟨98, by decide⟩ hj hq).1))
      (colE2 ⟨36, by decide⟩ 10 hp) Q2.T98_36_2 Q2.hfix98_36_2 Q2.hinj98_36_2
      Q2.hcardT98_36_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T98_36_2 i) (Q2.hfix98_36_2 i) _)
      ?_).symm
  rw [show colData1 (⟨98, by decide⟩ : Fin 148)
        ((colE1 ⟨36, by decide⟩ 10 (transLenTr ⟨36, by decide⟩ 10 hp) : ↥(reps ⟨36, by decide⟩)) : Coordinate 1)
        T98_36 = colFn colCertDiv_98_36_10.D1 (m := 25) from colCertDiv_98_36_10.bind1,
    show colData2 (⟨98, by decide⟩ : Fin 148)
        ((colE2 ⟨36, by decide⟩ 10 hp : ↥(Q2.reps ⟨36, by decide⟩)) : Coordinate 2)
        Q2.T98_36_2 = colFn colCertDiv_98_36_10.D2 (m := 25) from colCertDiv_98_36_10.bind2]
  rw [alnId_98 j hj]
  exact fastcode_of_div ⟨98, by decide⟩ _ _ _
    ((alnId_98 j hj) ▸ Q2.listedAt (⟨98, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨98, by decide⟩ : Fin 148) hj hq).1) colCertDiv_98_36_10_match


theorem leaf_98_36_15 (hp : 15 < (Q2.transData.getD 36 []).length)
    (j : Nat) (hj : j < (repChars.getD 98 []).length)
    (hq : (normIsRep.getD 98 []).getD j false = true) :
    species (Q2.reps (⟨36, by decide⟩ : Fin 148)) (colE2 ⟨36, by decide⟩ 15 hp)
        (rowE2 (⟨98, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨36, by decide⟩ : Fin 148))
        (colE1 ⟨36, by decide⟩ 15 (transLenTr ⟨36, by decide⟩ 15 hp))
        (rowE1 (⟨98, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨98, by decide⟩ : Fin 148) ⟨36, by decide⟩ _
      (validAt ⟨98, by decide⟩ (listedAt ⟨98, by decide⟩ hj))
      (colE1 ⟨36, by decide⟩ 15 (transLenTr ⟨36, by decide⟩ 15 hp)) T98_36
      hfix98_36 hinj98_36 hcardT98_36
      (fun i => conj_mem_of_fixedPoints _ _ (T98_36 i) (hfix98_36 i) _)
      ⟨98, by decide⟩ ⟨36, by decide⟩ _
      (Q2.validAt ⟨98, by decide⟩ (Q2.listedAt ⟨98, by decide⟩
        (alnCheck_rep ⟨98, by decide⟩ hj hq).1))
      (colE2 ⟨36, by decide⟩ 15 hp) Q2.T98_36_2 Q2.hfix98_36_2 Q2.hinj98_36_2
      Q2.hcardT98_36_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T98_36_2 i) (Q2.hfix98_36_2 i) _)
      ?_).symm
  rw [show colData1 (⟨98, by decide⟩ : Fin 148)
        ((colE1 ⟨36, by decide⟩ 15 (transLenTr ⟨36, by decide⟩ 15 hp) : ↥(reps ⟨36, by decide⟩)) : Coordinate 1)
        T98_36 = colFn colCertDiv_98_36_15.D1 (m := 25) from colCertDiv_98_36_15.bind1,
    show colData2 (⟨98, by decide⟩ : Fin 148)
        ((colE2 ⟨36, by decide⟩ 15 hp : ↥(Q2.reps ⟨36, by decide⟩)) : Coordinate 2)
        Q2.T98_36_2 = colFn colCertDiv_98_36_15.D2 (m := 25) from colCertDiv_98_36_15.bind2]
  rw [alnId_98 j hj]
  exact fastcode_of_div ⟨98, by decide⟩ _ _ _
    ((alnId_98 j hj) ▸ Q2.listedAt (⟨98, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨98, by decide⟩ : Fin 148) hj hq).1) colCertDiv_98_36_15_match


theorem leaf_98_36_20 (hp : 20 < (Q2.transData.getD 36 []).length)
    (j : Nat) (hj : j < (repChars.getD 98 []).length)
    (hq : (normIsRep.getD 98 []).getD j false = true) :
    species (Q2.reps (⟨36, by decide⟩ : Fin 148)) (colE2 ⟨36, by decide⟩ 20 hp)
        (rowE2 (⟨98, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨36, by decide⟩ : Fin 148))
        (colE1 ⟨36, by decide⟩ 20 (transLenTr ⟨36, by decide⟩ 20 hp))
        (rowE1 (⟨98, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨98, by decide⟩ : Fin 148) ⟨36, by decide⟩ _
      (validAt ⟨98, by decide⟩ (listedAt ⟨98, by decide⟩ hj))
      (colE1 ⟨36, by decide⟩ 20 (transLenTr ⟨36, by decide⟩ 20 hp)) T98_36
      hfix98_36 hinj98_36 hcardT98_36
      (fun i => conj_mem_of_fixedPoints _ _ (T98_36 i) (hfix98_36 i) _)
      ⟨98, by decide⟩ ⟨36, by decide⟩ _
      (Q2.validAt ⟨98, by decide⟩ (Q2.listedAt ⟨98, by decide⟩
        (alnCheck_rep ⟨98, by decide⟩ hj hq).1))
      (colE2 ⟨36, by decide⟩ 20 hp) Q2.T98_36_2 Q2.hfix98_36_2 Q2.hinj98_36_2
      Q2.hcardT98_36_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T98_36_2 i) (Q2.hfix98_36_2 i) _)
      ?_).symm
  rw [show colData1 (⟨98, by decide⟩ : Fin 148)
        ((colE1 ⟨36, by decide⟩ 20 (transLenTr ⟨36, by decide⟩ 20 hp) : ↥(reps ⟨36, by decide⟩)) : Coordinate 1)
        T98_36 = colFn colCertDiv_98_36_20.D1 (m := 25) from colCertDiv_98_36_20.bind1,
    show colData2 (⟨98, by decide⟩ : Fin 148)
        ((colE2 ⟨36, by decide⟩ 20 hp : ↥(Q2.reps ⟨36, by decide⟩)) : Coordinate 2)
        Q2.T98_36_2 = colFn colCertDiv_98_36_20.D2 (m := 25) from colCertDiv_98_36_20.bind2]
  rw [alnId_98 j hj]
  exact fastcode_of_div ⟨98, by decide⟩ _ _ _
    ((alnId_98 j hj) ▸ Q2.listedAt (⟨98, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨98, by decide⟩ : Fin 148) hj hq).1) colCertDiv_98_36_20_match


theorem leaf_98_53_0 (hp : 0 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 98 []).length)
    (hq : (normIsRep.getD 98 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 0 hp)
        (rowE2 (⟨98, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 0 (transLenTr ⟨53, by decide⟩ 0 hp))
        (rowE1 (⟨98, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨98, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨98, by decide⟩ (listedAt ⟨98, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 0 (transLenTr ⟨53, by decide⟩ 0 hp)) T98_53
      hfix98_53 hinj98_53 hcardT98_53
      (fun i => conj_mem_of_fixedPoints _ _ (T98_53 i) (hfix98_53 i) _)
      ⟨98, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨98, by decide⟩ (Q2.listedAt ⟨98, by decide⟩
        (alnCheck_rep ⟨98, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 0 hp) Q2.T98_53_2 Q2.hfix98_53_2 Q2.hinj98_53_2
      Q2.hcardT98_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T98_53_2 i) (Q2.hfix98_53_2 i) _)
      colCert_98_53_0.hD ?_).symm
  rw [alnId_98 j hj]


theorem leaf_98_53_1 (hp : 1 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 98 []).length)
    (hq : (normIsRep.getD 98 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 1 hp)
        (rowE2 (⟨98, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 1 (transLenTr ⟨53, by decide⟩ 1 hp))
        (rowE1 (⟨98, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨98, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨98, by decide⟩ (listedAt ⟨98, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 1 (transLenTr ⟨53, by decide⟩ 1 hp)) T98_53
      hfix98_53 hinj98_53 hcardT98_53
      (fun i => conj_mem_of_fixedPoints _ _ (T98_53 i) (hfix98_53 i) _)
      ⟨98, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨98, by decide⟩ (Q2.listedAt ⟨98, by decide⟩
        (alnCheck_rep ⟨98, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 1 hp) Q2.T98_53_2 Q2.hfix98_53_2 Q2.hinj98_53_2
      Q2.hcardT98_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T98_53_2 i) (Q2.hfix98_53_2 i) _)
      colCert_98_53_1.hD ?_).symm
  rw [alnId_98 j hj]


theorem leaf_98_53_2 (hp : 2 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 98 []).length)
    (hq : (normIsRep.getD 98 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 2 hp)
        (rowE2 (⟨98, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 2 (transLenTr ⟨53, by decide⟩ 2 hp))
        (rowE1 (⟨98, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨98, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨98, by decide⟩ (listedAt ⟨98, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 2 (transLenTr ⟨53, by decide⟩ 2 hp)) T98_53
      hfix98_53 hinj98_53 hcardT98_53
      (fun i => conj_mem_of_fixedPoints _ _ (T98_53 i) (hfix98_53 i) _)
      ⟨98, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨98, by decide⟩ (Q2.listedAt ⟨98, by decide⟩
        (alnCheck_rep ⟨98, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 2 hp) Q2.T98_53_2 Q2.hfix98_53_2 Q2.hinj98_53_2
      Q2.hcardT98_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T98_53_2 i) (Q2.hfix98_53_2 i) _)
      colCert_98_53_2.hD ?_).symm
  rw [alnId_98 j hj]


theorem leaf_98_53_3 (hp : 3 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 98 []).length)
    (hq : (normIsRep.getD 98 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 3 hp)
        (rowE2 (⟨98, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 3 (transLenTr ⟨53, by decide⟩ 3 hp))
        (rowE1 (⟨98, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨98, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨98, by decide⟩ (listedAt ⟨98, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 3 (transLenTr ⟨53, by decide⟩ 3 hp)) T98_53
      hfix98_53 hinj98_53 hcardT98_53
      (fun i => conj_mem_of_fixedPoints _ _ (T98_53 i) (hfix98_53 i) _)
      ⟨98, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨98, by decide⟩ (Q2.listedAt ⟨98, by decide⟩
        (alnCheck_rep ⟨98, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 3 hp) Q2.T98_53_2 Q2.hfix98_53_2 Q2.hinj98_53_2
      Q2.hcardT98_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T98_53_2 i) (Q2.hfix98_53_2 i) _)
      colCert_98_53_3.hD ?_).symm
  rw [alnId_98 j hj]


theorem leaf_98_53_4 (hp : 4 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 98 []).length)
    (hq : (normIsRep.getD 98 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 4 hp)
        (rowE2 (⟨98, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 4 (transLenTr ⟨53, by decide⟩ 4 hp))
        (rowE1 (⟨98, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨98, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨98, by decide⟩ (listedAt ⟨98, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 4 (transLenTr ⟨53, by decide⟩ 4 hp)) T98_53
      hfix98_53 hinj98_53 hcardT98_53
      (fun i => conj_mem_of_fixedPoints _ _ (T98_53 i) (hfix98_53 i) _)
      ⟨98, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨98, by decide⟩ (Q2.listedAt ⟨98, by decide⟩
        (alnCheck_rep ⟨98, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 4 hp) Q2.T98_53_2 Q2.hfix98_53_2 Q2.hinj98_53_2
      Q2.hcardT98_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T98_53_2 i) (Q2.hfix98_53_2 i) _)
      colCert_98_53_4.hD ?_).symm
  rw [alnId_98 j hj]


theorem leaf_98_53_5 (hp : 5 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 98 []).length)
    (hq : (normIsRep.getD 98 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 5 hp)
        (rowE2 (⟨98, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 5 (transLenTr ⟨53, by decide⟩ 5 hp))
        (rowE1 (⟨98, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨98, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨98, by decide⟩ (listedAt ⟨98, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 5 (transLenTr ⟨53, by decide⟩ 5 hp)) T98_53
      hfix98_53 hinj98_53 hcardT98_53
      (fun i => conj_mem_of_fixedPoints _ _ (T98_53 i) (hfix98_53 i) _)
      ⟨98, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨98, by decide⟩ (Q2.listedAt ⟨98, by decide⟩
        (alnCheck_rep ⟨98, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 5 hp) Q2.T98_53_2 Q2.hfix98_53_2 Q2.hinj98_53_2
      Q2.hcardT98_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T98_53_2 i) (Q2.hfix98_53_2 i) _)
      colCert_98_53_5.hD ?_).symm
  rw [alnId_98 j hj]


theorem leaf_98_53_10 (hp : 10 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 98 []).length)
    (hq : (normIsRep.getD 98 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 10 hp)
        (rowE2 (⟨98, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 10 (transLenTr ⟨53, by decide⟩ 10 hp))
        (rowE1 (⟨98, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨98, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨98, by decide⟩ (listedAt ⟨98, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 10 (transLenTr ⟨53, by decide⟩ 10 hp)) T98_53
      hfix98_53 hinj98_53 hcardT98_53
      (fun i => conj_mem_of_fixedPoints _ _ (T98_53 i) (hfix98_53 i) _)
      ⟨98, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨98, by decide⟩ (Q2.listedAt ⟨98, by decide⟩
        (alnCheck_rep ⟨98, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 10 hp) Q2.T98_53_2 Q2.hfix98_53_2 Q2.hinj98_53_2
      Q2.hcardT98_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T98_53_2 i) (Q2.hfix98_53_2 i) _)
      colCert_98_53_10.hD ?_).symm
  rw [alnId_98 j hj]


theorem leaf_98_53_15 (hp : 15 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 98 []).length)
    (hq : (normIsRep.getD 98 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 15 hp)
        (rowE2 (⟨98, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 15 (transLenTr ⟨53, by decide⟩ 15 hp))
        (rowE1 (⟨98, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨98, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨98, by decide⟩ (listedAt ⟨98, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 15 (transLenTr ⟨53, by decide⟩ 15 hp)) T98_53
      hfix98_53 hinj98_53 hcardT98_53
      (fun i => conj_mem_of_fixedPoints _ _ (T98_53 i) (hfix98_53 i) _)
      ⟨98, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨98, by decide⟩ (Q2.listedAt ⟨98, by decide⟩
        (alnCheck_rep ⟨98, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 15 hp) Q2.T98_53_2 Q2.hfix98_53_2 Q2.hinj98_53_2
      Q2.hcardT98_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T98_53_2 i) (Q2.hfix98_53_2 i) _)
      colCert_98_53_15.hD ?_).symm
  rw [alnId_98 j hj]


theorem leaf_98_53_20 (hp : 20 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 98 []).length)
    (hq : (normIsRep.getD 98 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 20 hp)
        (rowE2 (⟨98, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 20 (transLenTr ⟨53, by decide⟩ 20 hp))
        (rowE1 (⟨98, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨98, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨98, by decide⟩ (listedAt ⟨98, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 20 (transLenTr ⟨53, by decide⟩ 20 hp)) T98_53
      hfix98_53 hinj98_53 hcardT98_53
      (fun i => conj_mem_of_fixedPoints _ _ (T98_53 i) (hfix98_53 i) _)
      ⟨98, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨98, by decide⟩ (Q2.listedAt ⟨98, by decide⟩
        (alnCheck_rep ⟨98, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 20 hp) Q2.T98_53_2 Q2.hfix98_53_2 Q2.hinj98_53_2
      Q2.hcardT98_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T98_53_2 i) (Q2.hfix98_53_2 i) _)
      colCert_98_53_20.hD ?_).symm
  rw [alnId_98 j hj]


theorem leaf_98_98_0 (hp : 0 < (Q2.transData.getD 98 []).length)
    (j : Nat) (hj : j < (repChars.getD 98 []).length)
    (hq : (normIsRep.getD 98 []).getD j false = true) :
    species (Q2.reps (⟨98, by decide⟩ : Fin 148)) (colE2 ⟨98, by decide⟩ 0 hp)
        (rowE2 (⟨98, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨98, by decide⟩ : Fin 148))
        (colE1 ⟨98, by decide⟩ 0 (transLenTr ⟨98, by decide⟩ 0 hp))
        (rowE1 (⟨98, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨98, by decide⟩ : Fin 148) ⟨98, by decide⟩ _
      (validAt ⟨98, by decide⟩ (listedAt ⟨98, by decide⟩ hj))
      (colE1 ⟨98, by decide⟩ 0 (transLenTr ⟨98, by decide⟩ 0 hp)) T98_98
      hfix98_98 hinj98_98 hcardT98_98
      (fun i => conj_mem_of_fixedPoints _ _ (T98_98 i) (hfix98_98 i) _)
      ⟨98, by decide⟩ ⟨98, by decide⟩ _
      (Q2.validAt ⟨98, by decide⟩ (Q2.listedAt ⟨98, by decide⟩
        (alnCheck_rep ⟨98, by decide⟩ hj hq).1))
      (colE2 ⟨98, by decide⟩ 0 hp) Q2.T98_98_2 Q2.hfix98_98_2 Q2.hinj98_98_2
      Q2.hcardT98_98_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T98_98_2 i) (Q2.hfix98_98_2 i) _)
      colCert_98_98_0.hD ?_).symm
  rw [alnId_98 j hj]


theorem leaf_98_98_1 (hp : 1 < (Q2.transData.getD 98 []).length)
    (j : Nat) (hj : j < (repChars.getD 98 []).length)
    (hq : (normIsRep.getD 98 []).getD j false = true) :
    species (Q2.reps (⟨98, by decide⟩ : Fin 148)) (colE2 ⟨98, by decide⟩ 1 hp)
        (rowE2 (⟨98, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨98, by decide⟩ : Fin 148))
        (colE1 ⟨98, by decide⟩ 1 (transLenTr ⟨98, by decide⟩ 1 hp))
        (rowE1 (⟨98, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨98, by decide⟩ : Fin 148) ⟨98, by decide⟩ _
      (validAt ⟨98, by decide⟩ (listedAt ⟨98, by decide⟩ hj))
      (colE1 ⟨98, by decide⟩ 1 (transLenTr ⟨98, by decide⟩ 1 hp)) T98_98
      hfix98_98 hinj98_98 hcardT98_98
      (fun i => conj_mem_of_fixedPoints _ _ (T98_98 i) (hfix98_98 i) _)
      ⟨98, by decide⟩ ⟨98, by decide⟩ _
      (Q2.validAt ⟨98, by decide⟩ (Q2.listedAt ⟨98, by decide⟩
        (alnCheck_rep ⟨98, by decide⟩ hj hq).1))
      (colE2 ⟨98, by decide⟩ 1 hp) Q2.T98_98_2 Q2.hfix98_98_2 Q2.hinj98_98_2
      Q2.hcardT98_98_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T98_98_2 i) (Q2.hfix98_98_2 i) _)
      colCert_98_98_1.hD ?_).symm
  rw [alnId_98 j hj]


theorem leaf_98_98_2 (hp : 2 < (Q2.transData.getD 98 []).length)
    (j : Nat) (hj : j < (repChars.getD 98 []).length)
    (hq : (normIsRep.getD 98 []).getD j false = true) :
    species (Q2.reps (⟨98, by decide⟩ : Fin 148)) (colE2 ⟨98, by decide⟩ 2 hp)
        (rowE2 (⟨98, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨98, by decide⟩ : Fin 148))
        (colE1 ⟨98, by decide⟩ 2 (transLenTr ⟨98, by decide⟩ 2 hp))
        (rowE1 (⟨98, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨98, by decide⟩ : Fin 148) ⟨98, by decide⟩ _
      (validAt ⟨98, by decide⟩ (listedAt ⟨98, by decide⟩ hj))
      (colE1 ⟨98, by decide⟩ 2 (transLenTr ⟨98, by decide⟩ 2 hp)) T98_98
      hfix98_98 hinj98_98 hcardT98_98
      (fun i => conj_mem_of_fixedPoints _ _ (T98_98 i) (hfix98_98 i) _)
      ⟨98, by decide⟩ ⟨98, by decide⟩ _
      (Q2.validAt ⟨98, by decide⟩ (Q2.listedAt ⟨98, by decide⟩
        (alnCheck_rep ⟨98, by decide⟩ hj hq).1))
      (colE2 ⟨98, by decide⟩ 2 hp) Q2.T98_98_2 Q2.hfix98_98_2 Q2.hinj98_98_2
      Q2.hcardT98_98_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T98_98_2 i) (Q2.hfix98_98_2 i) _)
      colCert_98_98_2.hD ?_).symm
  rw [alnId_98 j hj]


theorem leaf_98_98_3 (hp : 3 < (Q2.transData.getD 98 []).length)
    (j : Nat) (hj : j < (repChars.getD 98 []).length)
    (hq : (normIsRep.getD 98 []).getD j false = true) :
    species (Q2.reps (⟨98, by decide⟩ : Fin 148)) (colE2 ⟨98, by decide⟩ 3 hp)
        (rowE2 (⟨98, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨98, by decide⟩ : Fin 148))
        (colE1 ⟨98, by decide⟩ 3 (transLenTr ⟨98, by decide⟩ 3 hp))
        (rowE1 (⟨98, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨98, by decide⟩ : Fin 148) ⟨98, by decide⟩ _
      (validAt ⟨98, by decide⟩ (listedAt ⟨98, by decide⟩ hj))
      (colE1 ⟨98, by decide⟩ 3 (transLenTr ⟨98, by decide⟩ 3 hp)) T98_98
      hfix98_98 hinj98_98 hcardT98_98
      (fun i => conj_mem_of_fixedPoints _ _ (T98_98 i) (hfix98_98 i) _)
      ⟨98, by decide⟩ ⟨98, by decide⟩ _
      (Q2.validAt ⟨98, by decide⟩ (Q2.listedAt ⟨98, by decide⟩
        (alnCheck_rep ⟨98, by decide⟩ hj hq).1))
      (colE2 ⟨98, by decide⟩ 3 hp) Q2.T98_98_2 Q2.hfix98_98_2 Q2.hinj98_98_2
      Q2.hcardT98_98_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T98_98_2 i) (Q2.hfix98_98_2 i) _)
      colCert_98_98_3.hD ?_).symm
  rw [alnId_98 j hj]


theorem leaf_98_98_4 (hp : 4 < (Q2.transData.getD 98 []).length)
    (j : Nat) (hj : j < (repChars.getD 98 []).length)
    (hq : (normIsRep.getD 98 []).getD j false = true) :
    species (Q2.reps (⟨98, by decide⟩ : Fin 148)) (colE2 ⟨98, by decide⟩ 4 hp)
        (rowE2 (⟨98, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨98, by decide⟩ : Fin 148))
        (colE1 ⟨98, by decide⟩ 4 (transLenTr ⟨98, by decide⟩ 4 hp))
        (rowE1 (⟨98, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨98, by decide⟩ : Fin 148) ⟨98, by decide⟩ _
      (validAt ⟨98, by decide⟩ (listedAt ⟨98, by decide⟩ hj))
      (colE1 ⟨98, by decide⟩ 4 (transLenTr ⟨98, by decide⟩ 4 hp)) T98_98
      hfix98_98 hinj98_98 hcardT98_98
      (fun i => conj_mem_of_fixedPoints _ _ (T98_98 i) (hfix98_98 i) _)
      ⟨98, by decide⟩ ⟨98, by decide⟩ _
      (Q2.validAt ⟨98, by decide⟩ (Q2.listedAt ⟨98, by decide⟩
        (alnCheck_rep ⟨98, by decide⟩ hj hq).1))
      (colE2 ⟨98, by decide⟩ 4 hp) Q2.T98_98_2 Q2.hfix98_98_2 Q2.hinj98_98_2
      Q2.hcardT98_98_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T98_98_2 i) (Q2.hfix98_98_2 i) _)
      colCert_98_98_4.hD ?_).symm
  rw [alnId_98 j hj]


theorem leaf_98_98_5 (hp : 5 < (Q2.transData.getD 98 []).length)
    (j : Nat) (hj : j < (repChars.getD 98 []).length)
    (hq : (normIsRep.getD 98 []).getD j false = true) :
    species (Q2.reps (⟨98, by decide⟩ : Fin 148)) (colE2 ⟨98, by decide⟩ 5 hp)
        (rowE2 (⟨98, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨98, by decide⟩ : Fin 148))
        (colE1 ⟨98, by decide⟩ 5 (transLenTr ⟨98, by decide⟩ 5 hp))
        (rowE1 (⟨98, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨98, by decide⟩ : Fin 148) ⟨98, by decide⟩ _
      (validAt ⟨98, by decide⟩ (listedAt ⟨98, by decide⟩ hj))
      (colE1 ⟨98, by decide⟩ 5 (transLenTr ⟨98, by decide⟩ 5 hp)) T98_98
      hfix98_98 hinj98_98 hcardT98_98
      (fun i => conj_mem_of_fixedPoints _ _ (T98_98 i) (hfix98_98 i) _)
      ⟨98, by decide⟩ ⟨98, by decide⟩ _
      (Q2.validAt ⟨98, by decide⟩ (Q2.listedAt ⟨98, by decide⟩
        (alnCheck_rep ⟨98, by decide⟩ hj hq).1))
      (colE2 ⟨98, by decide⟩ 5 hp) Q2.T98_98_2 Q2.hfix98_98_2 Q2.hinj98_98_2
      Q2.hcardT98_98_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T98_98_2 i) (Q2.hfix98_98_2 i) _)
      colCert_98_98_5.hD ?_).symm
  rw [alnId_98 j hj]


theorem leaf_98_98_10 (hp : 10 < (Q2.transData.getD 98 []).length)
    (j : Nat) (hj : j < (repChars.getD 98 []).length)
    (hq : (normIsRep.getD 98 []).getD j false = true) :
    species (Q2.reps (⟨98, by decide⟩ : Fin 148)) (colE2 ⟨98, by decide⟩ 10 hp)
        (rowE2 (⟨98, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨98, by decide⟩ : Fin 148))
        (colE1 ⟨98, by decide⟩ 10 (transLenTr ⟨98, by decide⟩ 10 hp))
        (rowE1 (⟨98, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨98, by decide⟩ : Fin 148) ⟨98, by decide⟩ _
      (validAt ⟨98, by decide⟩ (listedAt ⟨98, by decide⟩ hj))
      (colE1 ⟨98, by decide⟩ 10 (transLenTr ⟨98, by decide⟩ 10 hp)) T98_98
      hfix98_98 hinj98_98 hcardT98_98
      (fun i => conj_mem_of_fixedPoints _ _ (T98_98 i) (hfix98_98 i) _)
      ⟨98, by decide⟩ ⟨98, by decide⟩ _
      (Q2.validAt ⟨98, by decide⟩ (Q2.listedAt ⟨98, by decide⟩
        (alnCheck_rep ⟨98, by decide⟩ hj hq).1))
      (colE2 ⟨98, by decide⟩ 10 hp) Q2.T98_98_2 Q2.hfix98_98_2 Q2.hinj98_98_2
      Q2.hcardT98_98_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T98_98_2 i) (Q2.hfix98_98_2 i) _)
      colCert_98_98_10.hD ?_).symm
  rw [alnId_98 j hj]


theorem leaf_98_98_15 (hp : 15 < (Q2.transData.getD 98 []).length)
    (j : Nat) (hj : j < (repChars.getD 98 []).length)
    (hq : (normIsRep.getD 98 []).getD j false = true) :
    species (Q2.reps (⟨98, by decide⟩ : Fin 148)) (colE2 ⟨98, by decide⟩ 15 hp)
        (rowE2 (⟨98, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨98, by decide⟩ : Fin 148))
        (colE1 ⟨98, by decide⟩ 15 (transLenTr ⟨98, by decide⟩ 15 hp))
        (rowE1 (⟨98, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨98, by decide⟩ : Fin 148) ⟨98, by decide⟩ _
      (validAt ⟨98, by decide⟩ (listedAt ⟨98, by decide⟩ hj))
      (colE1 ⟨98, by decide⟩ 15 (transLenTr ⟨98, by decide⟩ 15 hp)) T98_98
      hfix98_98 hinj98_98 hcardT98_98
      (fun i => conj_mem_of_fixedPoints _ _ (T98_98 i) (hfix98_98 i) _)
      ⟨98, by decide⟩ ⟨98, by decide⟩ _
      (Q2.validAt ⟨98, by decide⟩ (Q2.listedAt ⟨98, by decide⟩
        (alnCheck_rep ⟨98, by decide⟩ hj hq).1))
      (colE2 ⟨98, by decide⟩ 15 hp) Q2.T98_98_2 Q2.hfix98_98_2 Q2.hinj98_98_2
      Q2.hcardT98_98_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T98_98_2 i) (Q2.hfix98_98_2 i) _)
      colCert_98_98_15.hD ?_).symm
  rw [alnId_98 j hj]


theorem leaf_98_98_20 (hp : 20 < (Q2.transData.getD 98 []).length)
    (j : Nat) (hj : j < (repChars.getD 98 []).length)
    (hq : (normIsRep.getD 98 []).getD j false = true) :
    species (Q2.reps (⟨98, by decide⟩ : Fin 148)) (colE2 ⟨98, by decide⟩ 20 hp)
        (rowE2 (⟨98, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨98, by decide⟩ : Fin 148))
        (colE1 ⟨98, by decide⟩ 20 (transLenTr ⟨98, by decide⟩ 20 hp))
        (rowE1 (⟨98, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨98, by decide⟩ : Fin 148) ⟨98, by decide⟩ _
      (validAt ⟨98, by decide⟩ (listedAt ⟨98, by decide⟩ hj))
      (colE1 ⟨98, by decide⟩ 20 (transLenTr ⟨98, by decide⟩ 20 hp)) T98_98
      hfix98_98 hinj98_98 hcardT98_98
      (fun i => conj_mem_of_fixedPoints _ _ (T98_98 i) (hfix98_98 i) _)
      ⟨98, by decide⟩ ⟨98, by decide⟩ _
      (Q2.validAt ⟨98, by decide⟩ (Q2.listedAt ⟨98, by decide⟩
        (alnCheck_rep ⟨98, by decide⟩ hj hq).1))
      (colE2 ⟨98, by decide⟩ 20 hp) Q2.T98_98_2 Q2.hfix98_98_2 Q2.hinj98_98_2
      Q2.hcardT98_98_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T98_98_2 i) (Q2.hfix98_98_2 i) _)
      colCert_98_98_20.hD ?_).symm
  rw [alnId_98 j hj]


theorem leaf_99_10_0 (hp : 0 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 99 []).length)
    (hq : (normIsRep.getD 99 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 0 hp)
        (rowE2 (⟨99, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 0 (transLenTr ⟨10, by decide⟩ 0 hp))
        (rowE1 (⟨99, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨99, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨99, by decide⟩ (listedAt ⟨99, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 0 (transLenTr ⟨10, by decide⟩ 0 hp)) T99_10
      hfix99_10 hinj99_10 hcardT99_10
      (fun i => conj_mem_of_fixedPoints _ _ (T99_10 i) (hfix99_10 i) _)
      ⟨99, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨99, by decide⟩ (Q2.listedAt ⟨99, by decide⟩
        (alnCheck_rep ⟨99, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 0 hp) Q2.T99_10_2 Q2.hfix99_10_2 Q2.hinj99_10_2
      Q2.hcardT99_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T99_10_2 i) (Q2.hfix99_10_2 i) _)
      colCert_99_10_0.hD ?_).symm
  rw [alnId_99 j hj]


theorem leaf_99_10_1 (hp : 1 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 99 []).length)
    (hq : (normIsRep.getD 99 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 1 hp)
        (rowE2 (⟨99, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 1 (transLenTr ⟨10, by decide⟩ 1 hp))
        (rowE1 (⟨99, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨99, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨99, by decide⟩ (listedAt ⟨99, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 1 (transLenTr ⟨10, by decide⟩ 1 hp)) T99_10
      hfix99_10 hinj99_10 hcardT99_10
      (fun i => conj_mem_of_fixedPoints _ _ (T99_10 i) (hfix99_10 i) _)
      ⟨99, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨99, by decide⟩ (Q2.listedAt ⟨99, by decide⟩
        (alnCheck_rep ⟨99, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 1 hp) Q2.T99_10_2 Q2.hfix99_10_2 Q2.hinj99_10_2
      Q2.hcardT99_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T99_10_2 i) (Q2.hfix99_10_2 i) _)
      colCert_99_10_1.hD ?_).symm
  rw [alnId_99 j hj]


theorem leaf_99_10_2 (hp : 2 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 99 []).length)
    (hq : (normIsRep.getD 99 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 2 hp)
        (rowE2 (⟨99, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 2 (transLenTr ⟨10, by decide⟩ 2 hp))
        (rowE1 (⟨99, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨99, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨99, by decide⟩ (listedAt ⟨99, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 2 (transLenTr ⟨10, by decide⟩ 2 hp)) T99_10
      hfix99_10 hinj99_10 hcardT99_10
      (fun i => conj_mem_of_fixedPoints _ _ (T99_10 i) (hfix99_10 i) _)
      ⟨99, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨99, by decide⟩ (Q2.listedAt ⟨99, by decide⟩
        (alnCheck_rep ⟨99, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 2 hp) Q2.T99_10_2 Q2.hfix99_10_2 Q2.hinj99_10_2
      Q2.hcardT99_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T99_10_2 i) (Q2.hfix99_10_2 i) _)
      colCert_99_10_2.hD ?_).symm
  rw [alnId_99 j hj]


theorem leaf_99_10_3 (hp : 3 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 99 []).length)
    (hq : (normIsRep.getD 99 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 3 hp)
        (rowE2 (⟨99, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 3 (transLenTr ⟨10, by decide⟩ 3 hp))
        (rowE1 (⟨99, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨99, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨99, by decide⟩ (listedAt ⟨99, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 3 (transLenTr ⟨10, by decide⟩ 3 hp)) T99_10
      hfix99_10 hinj99_10 hcardT99_10
      (fun i => conj_mem_of_fixedPoints _ _ (T99_10 i) (hfix99_10 i) _)
      ⟨99, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨99, by decide⟩ (Q2.listedAt ⟨99, by decide⟩
        (alnCheck_rep ⟨99, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 3 hp) Q2.T99_10_2 Q2.hfix99_10_2 Q2.hinj99_10_2
      Q2.hcardT99_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T99_10_2 i) (Q2.hfix99_10_2 i) _)
      colCert_99_10_3.hD ?_).symm
  rw [alnId_99 j hj]


theorem leaf_99_10_4 (hp : 4 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 99 []).length)
    (hq : (normIsRep.getD 99 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 4 hp)
        (rowE2 (⟨99, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 4 (transLenTr ⟨10, by decide⟩ 4 hp))
        (rowE1 (⟨99, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨99, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨99, by decide⟩ (listedAt ⟨99, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 4 (transLenTr ⟨10, by decide⟩ 4 hp)) T99_10
      hfix99_10 hinj99_10 hcardT99_10
      (fun i => conj_mem_of_fixedPoints _ _ (T99_10 i) (hfix99_10 i) _)
      ⟨99, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨99, by decide⟩ (Q2.listedAt ⟨99, by decide⟩
        (alnCheck_rep ⟨99, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 4 hp) Q2.T99_10_2 Q2.hfix99_10_2 Q2.hinj99_10_2
      Q2.hcardT99_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T99_10_2 i) (Q2.hfix99_10_2 i) _)
      colCert_99_10_4.hD ?_).symm
  rw [alnId_99 j hj]


theorem leaf_99_12_0 (hp : 0 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 99 []).length)
    (hq : (normIsRep.getD 99 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 0 hp)
        (rowE2 (⟨99, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp))
        (rowE1 (⟨99, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨99, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨99, by decide⟩ (listedAt ⟨99, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp)) T99_12
      hfix99_12 hinj99_12 hcardT99_12
      (fun i => conj_mem_of_fixedPoints _ _ (T99_12 i) (hfix99_12 i) _)
      ⟨99, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨99, by decide⟩ (Q2.listedAt ⟨99, by decide⟩
        (alnCheck_rep ⟨99, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 0 hp) Q2.T99_12_2 Q2.hfix99_12_2 Q2.hinj99_12_2
      Q2.hcardT99_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T99_12_2 i) (Q2.hfix99_12_2 i) _)
      colCert_99_12_0.hD ?_).symm
  rw [alnId_99 j hj]


theorem leaf_99_12_1 (hp : 1 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 99 []).length)
    (hq : (normIsRep.getD 99 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 1 hp)
        (rowE2 (⟨99, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp))
        (rowE1 (⟨99, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨99, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨99, by decide⟩ (listedAt ⟨99, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp)) T99_12
      hfix99_12 hinj99_12 hcardT99_12
      (fun i => conj_mem_of_fixedPoints _ _ (T99_12 i) (hfix99_12 i) _)
      ⟨99, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨99, by decide⟩ (Q2.listedAt ⟨99, by decide⟩
        (alnCheck_rep ⟨99, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 1 hp) Q2.T99_12_2 Q2.hfix99_12_2 Q2.hinj99_12_2
      Q2.hcardT99_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T99_12_2 i) (Q2.hfix99_12_2 i) _)
      colCert_99_12_1.hD ?_).symm
  rw [alnId_99 j hj]


theorem leaf_99_12_2 (hp : 2 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 99 []).length)
    (hq : (normIsRep.getD 99 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 2 hp)
        (rowE2 (⟨99, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp))
        (rowE1 (⟨99, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨99, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨99, by decide⟩ (listedAt ⟨99, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp)) T99_12
      hfix99_12 hinj99_12 hcardT99_12
      (fun i => conj_mem_of_fixedPoints _ _ (T99_12 i) (hfix99_12 i) _)
      ⟨99, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨99, by decide⟩ (Q2.listedAt ⟨99, by decide⟩
        (alnCheck_rep ⟨99, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 2 hp) Q2.T99_12_2 Q2.hfix99_12_2 Q2.hinj99_12_2
      Q2.hcardT99_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T99_12_2 i) (Q2.hfix99_12_2 i) _)
      colCert_99_12_2.hD ?_).symm
  rw [alnId_99 j hj]


theorem leaf_99_12_3 (hp : 3 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 99 []).length)
    (hq : (normIsRep.getD 99 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 3 hp)
        (rowE2 (⟨99, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp))
        (rowE1 (⟨99, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨99, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨99, by decide⟩ (listedAt ⟨99, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp)) T99_12
      hfix99_12 hinj99_12 hcardT99_12
      (fun i => conj_mem_of_fixedPoints _ _ (T99_12 i) (hfix99_12 i) _)
      ⟨99, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨99, by decide⟩ (Q2.listedAt ⟨99, by decide⟩
        (alnCheck_rep ⟨99, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 3 hp) Q2.T99_12_2 Q2.hfix99_12_2 Q2.hinj99_12_2
      Q2.hcardT99_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T99_12_2 i) (Q2.hfix99_12_2 i) _)
      colCert_99_12_3.hD ?_).symm
  rw [alnId_99 j hj]


theorem leaf_99_12_4 (hp : 4 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 99 []).length)
    (hq : (normIsRep.getD 99 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 4 hp)
        (rowE2 (⟨99, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp))
        (rowE1 (⟨99, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨99, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨99, by decide⟩ (listedAt ⟨99, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp)) T99_12
      hfix99_12 hinj99_12 hcardT99_12
      (fun i => conj_mem_of_fixedPoints _ _ (T99_12 i) (hfix99_12 i) _)
      ⟨99, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨99, by decide⟩ (Q2.listedAt ⟨99, by decide⟩
        (alnCheck_rep ⟨99, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 4 hp) Q2.T99_12_2 Q2.hfix99_12_2 Q2.hinj99_12_2
      Q2.hcardT99_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T99_12_2 i) (Q2.hfix99_12_2 i) _)
      colCert_99_12_4.hD ?_).symm
  rw [alnId_99 j hj]


theorem leaf_99_37_0 (hp : 0 < (Q2.transData.getD 37 []).length)
    (j : Nat) (hj : j < (repChars.getD 99 []).length)
    (hq : (normIsRep.getD 99 []).getD j false = true) :
    species (Q2.reps (⟨37, by decide⟩ : Fin 148)) (colE2 ⟨37, by decide⟩ 0 hp)
        (rowE2 (⟨99, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨37, by decide⟩ : Fin 148))
        (colE1 ⟨37, by decide⟩ 0 (transLenTr ⟨37, by decide⟩ 0 hp))
        (rowE1 (⟨99, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨99, by decide⟩ : Fin 148) ⟨37, by decide⟩ _
      (validAt ⟨99, by decide⟩ (listedAt ⟨99, by decide⟩ hj))
      (colE1 ⟨37, by decide⟩ 0 (transLenTr ⟨37, by decide⟩ 0 hp)) T99_37
      hfix99_37 hinj99_37 hcardT99_37
      (fun i => conj_mem_of_fixedPoints _ _ (T99_37 i) (hfix99_37 i) _)
      ⟨99, by decide⟩ ⟨37, by decide⟩ _
      (Q2.validAt ⟨99, by decide⟩ (Q2.listedAt ⟨99, by decide⟩
        (alnCheck_rep ⟨99, by decide⟩ hj hq).1))
      (colE2 ⟨37, by decide⟩ 0 hp) Q2.T99_37_2 Q2.hfix99_37_2 Q2.hinj99_37_2
      Q2.hcardT99_37_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T99_37_2 i) (Q2.hfix99_37_2 i) _)
      colCert_99_37_0.hD ?_).symm
  rw [alnId_99 j hj]


theorem leaf_99_37_1 (hp : 1 < (Q2.transData.getD 37 []).length)
    (j : Nat) (hj : j < (repChars.getD 99 []).length)
    (hq : (normIsRep.getD 99 []).getD j false = true) :
    species (Q2.reps (⟨37, by decide⟩ : Fin 148)) (colE2 ⟨37, by decide⟩ 1 hp)
        (rowE2 (⟨99, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨37, by decide⟩ : Fin 148))
        (colE1 ⟨37, by decide⟩ 1 (transLenTr ⟨37, by decide⟩ 1 hp))
        (rowE1 (⟨99, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨99, by decide⟩ : Fin 148) ⟨37, by decide⟩ _
      (validAt ⟨99, by decide⟩ (listedAt ⟨99, by decide⟩ hj))
      (colE1 ⟨37, by decide⟩ 1 (transLenTr ⟨37, by decide⟩ 1 hp)) T99_37
      hfix99_37 hinj99_37 hcardT99_37
      (fun i => conj_mem_of_fixedPoints _ _ (T99_37 i) (hfix99_37 i) _)
      ⟨99, by decide⟩ ⟨37, by decide⟩ _
      (Q2.validAt ⟨99, by decide⟩ (Q2.listedAt ⟨99, by decide⟩
        (alnCheck_rep ⟨99, by decide⟩ hj hq).1))
      (colE2 ⟨37, by decide⟩ 1 hp) Q2.T99_37_2 Q2.hfix99_37_2 Q2.hinj99_37_2
      Q2.hcardT99_37_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T99_37_2 i) (Q2.hfix99_37_2 i) _)
      colCert_99_37_1.hD ?_).symm
  rw [alnId_99 j hj]


theorem leaf_99_37_2 (hp : 2 < (Q2.transData.getD 37 []).length)
    (j : Nat) (hj : j < (repChars.getD 99 []).length)
    (hq : (normIsRep.getD 99 []).getD j false = true) :
    species (Q2.reps (⟨37, by decide⟩ : Fin 148)) (colE2 ⟨37, by decide⟩ 2 hp)
        (rowE2 (⟨99, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨37, by decide⟩ : Fin 148))
        (colE1 ⟨37, by decide⟩ 2 (transLenTr ⟨37, by decide⟩ 2 hp))
        (rowE1 (⟨99, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨99, by decide⟩ : Fin 148) ⟨37, by decide⟩ _
      (validAt ⟨99, by decide⟩ (listedAt ⟨99, by decide⟩ hj))
      (colE1 ⟨37, by decide⟩ 2 (transLenTr ⟨37, by decide⟩ 2 hp)) T99_37
      hfix99_37 hinj99_37 hcardT99_37
      (fun i => conj_mem_of_fixedPoints _ _ (T99_37 i) (hfix99_37 i) _)
      ⟨99, by decide⟩ ⟨37, by decide⟩ _
      (Q2.validAt ⟨99, by decide⟩ (Q2.listedAt ⟨99, by decide⟩
        (alnCheck_rep ⟨99, by decide⟩ hj hq).1))
      (colE2 ⟨37, by decide⟩ 2 hp) Q2.T99_37_2 Q2.hfix99_37_2 Q2.hinj99_37_2
      Q2.hcardT99_37_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T99_37_2 i) (Q2.hfix99_37_2 i) _)
      colCert_99_37_2.hD ?_).symm
  rw [alnId_99 j hj]


theorem leaf_99_37_3 (hp : 3 < (Q2.transData.getD 37 []).length)
    (j : Nat) (hj : j < (repChars.getD 99 []).length)
    (hq : (normIsRep.getD 99 []).getD j false = true) :
    species (Q2.reps (⟨37, by decide⟩ : Fin 148)) (colE2 ⟨37, by decide⟩ 3 hp)
        (rowE2 (⟨99, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨37, by decide⟩ : Fin 148))
        (colE1 ⟨37, by decide⟩ 3 (transLenTr ⟨37, by decide⟩ 3 hp))
        (rowE1 (⟨99, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨99, by decide⟩ : Fin 148) ⟨37, by decide⟩ _
      (validAt ⟨99, by decide⟩ (listedAt ⟨99, by decide⟩ hj))
      (colE1 ⟨37, by decide⟩ 3 (transLenTr ⟨37, by decide⟩ 3 hp)) T99_37
      hfix99_37 hinj99_37 hcardT99_37
      (fun i => conj_mem_of_fixedPoints _ _ (T99_37 i) (hfix99_37 i) _)
      ⟨99, by decide⟩ ⟨37, by decide⟩ _
      (Q2.validAt ⟨99, by decide⟩ (Q2.listedAt ⟨99, by decide⟩
        (alnCheck_rep ⟨99, by decide⟩ hj hq).1))
      (colE2 ⟨37, by decide⟩ 3 hp) Q2.T99_37_2 Q2.hfix99_37_2 Q2.hinj99_37_2
      Q2.hcardT99_37_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T99_37_2 i) (Q2.hfix99_37_2 i) _)
      colCert_99_37_3.hD ?_).symm
  rw [alnId_99 j hj]


theorem leaf_99_37_4 (hp : 4 < (Q2.transData.getD 37 []).length)
    (j : Nat) (hj : j < (repChars.getD 99 []).length)
    (hq : (normIsRep.getD 99 []).getD j false = true) :
    species (Q2.reps (⟨37, by decide⟩ : Fin 148)) (colE2 ⟨37, by decide⟩ 4 hp)
        (rowE2 (⟨99, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨37, by decide⟩ : Fin 148))
        (colE1 ⟨37, by decide⟩ 4 (transLenTr ⟨37, by decide⟩ 4 hp))
        (rowE1 (⟨99, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨99, by decide⟩ : Fin 148) ⟨37, by decide⟩ _
      (validAt ⟨99, by decide⟩ (listedAt ⟨99, by decide⟩ hj))
      (colE1 ⟨37, by decide⟩ 4 (transLenTr ⟨37, by decide⟩ 4 hp)) T99_37
      hfix99_37 hinj99_37 hcardT99_37
      (fun i => conj_mem_of_fixedPoints _ _ (T99_37 i) (hfix99_37 i) _)
      ⟨99, by decide⟩ ⟨37, by decide⟩ _
      (Q2.validAt ⟨99, by decide⟩ (Q2.listedAt ⟨99, by decide⟩
        (alnCheck_rep ⟨99, by decide⟩ hj hq).1))
      (colE2 ⟨37, by decide⟩ 4 hp) Q2.T99_37_2 Q2.hfix99_37_2 Q2.hinj99_37_2
      Q2.hcardT99_37_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T99_37_2 i) (Q2.hfix99_37_2 i) _)
      colCert_99_37_4.hD ?_).symm
  rw [alnId_99 j hj]


theorem leaf_99_37_5 (hp : 5 < (Q2.transData.getD 37 []).length)
    (j : Nat) (hj : j < (repChars.getD 99 []).length)
    (hq : (normIsRep.getD 99 []).getD j false = true) :
    species (Q2.reps (⟨37, by decide⟩ : Fin 148)) (colE2 ⟨37, by decide⟩ 5 hp)
        (rowE2 (⟨99, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨37, by decide⟩ : Fin 148))
        (colE1 ⟨37, by decide⟩ 5 (transLenTr ⟨37, by decide⟩ 5 hp))
        (rowE1 (⟨99, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨99, by decide⟩ : Fin 148) ⟨37, by decide⟩ _
      (validAt ⟨99, by decide⟩ (listedAt ⟨99, by decide⟩ hj))
      (colE1 ⟨37, by decide⟩ 5 (transLenTr ⟨37, by decide⟩ 5 hp)) T99_37
      hfix99_37 hinj99_37 hcardT99_37
      (fun i => conj_mem_of_fixedPoints _ _ (T99_37 i) (hfix99_37 i) _)
      ⟨99, by decide⟩ ⟨37, by decide⟩ _
      (Q2.validAt ⟨99, by decide⟩ (Q2.listedAt ⟨99, by decide⟩
        (alnCheck_rep ⟨99, by decide⟩ hj hq).1))
      (colE2 ⟨37, by decide⟩ 5 hp) Q2.T99_37_2 Q2.hfix99_37_2 Q2.hinj99_37_2
      Q2.hcardT99_37_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T99_37_2 i) (Q2.hfix99_37_2 i) _)
      ?_).symm
  rw [show colData1 (⟨99, by decide⟩ : Fin 148)
        ((colE1 ⟨37, by decide⟩ 5 (transLenTr ⟨37, by decide⟩ 5 hp) : ↥(reps ⟨37, by decide⟩)) : Coordinate 1)
        T99_37 = colFn colCertDiv_99_37_5.D1 (m := 25) from colCertDiv_99_37_5.bind1,
    show colData2 (⟨99, by decide⟩ : Fin 148)
        ((colE2 ⟨37, by decide⟩ 5 hp : ↥(Q2.reps ⟨37, by decide⟩)) : Coordinate 2)
        Q2.T99_37_2 = colFn colCertDiv_99_37_5.D2 (m := 25) from colCertDiv_99_37_5.bind2]
  rw [alnId_99 j hj]
  exact fastcode_of_div ⟨99, by decide⟩ _ _ _
    ((alnId_99 j hj) ▸ Q2.listedAt (⟨99, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨99, by decide⟩ : Fin 148) hj hq).1) colCertDiv_99_37_5_match


theorem leaf_99_37_10 (hp : 10 < (Q2.transData.getD 37 []).length)
    (j : Nat) (hj : j < (repChars.getD 99 []).length)
    (hq : (normIsRep.getD 99 []).getD j false = true) :
    species (Q2.reps (⟨37, by decide⟩ : Fin 148)) (colE2 ⟨37, by decide⟩ 10 hp)
        (rowE2 (⟨99, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨37, by decide⟩ : Fin 148))
        (colE1 ⟨37, by decide⟩ 10 (transLenTr ⟨37, by decide⟩ 10 hp))
        (rowE1 (⟨99, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨99, by decide⟩ : Fin 148) ⟨37, by decide⟩ _
      (validAt ⟨99, by decide⟩ (listedAt ⟨99, by decide⟩ hj))
      (colE1 ⟨37, by decide⟩ 10 (transLenTr ⟨37, by decide⟩ 10 hp)) T99_37
      hfix99_37 hinj99_37 hcardT99_37
      (fun i => conj_mem_of_fixedPoints _ _ (T99_37 i) (hfix99_37 i) _)
      ⟨99, by decide⟩ ⟨37, by decide⟩ _
      (Q2.validAt ⟨99, by decide⟩ (Q2.listedAt ⟨99, by decide⟩
        (alnCheck_rep ⟨99, by decide⟩ hj hq).1))
      (colE2 ⟨37, by decide⟩ 10 hp) Q2.T99_37_2 Q2.hfix99_37_2 Q2.hinj99_37_2
      Q2.hcardT99_37_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T99_37_2 i) (Q2.hfix99_37_2 i) _)
      ?_).symm
  rw [show colData1 (⟨99, by decide⟩ : Fin 148)
        ((colE1 ⟨37, by decide⟩ 10 (transLenTr ⟨37, by decide⟩ 10 hp) : ↥(reps ⟨37, by decide⟩)) : Coordinate 1)
        T99_37 = colFn colCertDiv_99_37_10.D1 (m := 25) from colCertDiv_99_37_10.bind1,
    show colData2 (⟨99, by decide⟩ : Fin 148)
        ((colE2 ⟨37, by decide⟩ 10 hp : ↥(Q2.reps ⟨37, by decide⟩)) : Coordinate 2)
        Q2.T99_37_2 = colFn colCertDiv_99_37_10.D2 (m := 25) from colCertDiv_99_37_10.bind2]
  rw [alnId_99 j hj]
  exact fastcode_of_div ⟨99, by decide⟩ _ _ _
    ((alnId_99 j hj) ▸ Q2.listedAt (⟨99, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨99, by decide⟩ : Fin 148) hj hq).1) colCertDiv_99_37_10_match


theorem leaf_99_37_15 (hp : 15 < (Q2.transData.getD 37 []).length)
    (j : Nat) (hj : j < (repChars.getD 99 []).length)
    (hq : (normIsRep.getD 99 []).getD j false = true) :
    species (Q2.reps (⟨37, by decide⟩ : Fin 148)) (colE2 ⟨37, by decide⟩ 15 hp)
        (rowE2 (⟨99, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨37, by decide⟩ : Fin 148))
        (colE1 ⟨37, by decide⟩ 15 (transLenTr ⟨37, by decide⟩ 15 hp))
        (rowE1 (⟨99, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨99, by decide⟩ : Fin 148) ⟨37, by decide⟩ _
      (validAt ⟨99, by decide⟩ (listedAt ⟨99, by decide⟩ hj))
      (colE1 ⟨37, by decide⟩ 15 (transLenTr ⟨37, by decide⟩ 15 hp)) T99_37
      hfix99_37 hinj99_37 hcardT99_37
      (fun i => conj_mem_of_fixedPoints _ _ (T99_37 i) (hfix99_37 i) _)
      ⟨99, by decide⟩ ⟨37, by decide⟩ _
      (Q2.validAt ⟨99, by decide⟩ (Q2.listedAt ⟨99, by decide⟩
        (alnCheck_rep ⟨99, by decide⟩ hj hq).1))
      (colE2 ⟨37, by decide⟩ 15 hp) Q2.T99_37_2 Q2.hfix99_37_2 Q2.hinj99_37_2
      Q2.hcardT99_37_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T99_37_2 i) (Q2.hfix99_37_2 i) _)
      ?_).symm
  rw [show colData1 (⟨99, by decide⟩ : Fin 148)
        ((colE1 ⟨37, by decide⟩ 15 (transLenTr ⟨37, by decide⟩ 15 hp) : ↥(reps ⟨37, by decide⟩)) : Coordinate 1)
        T99_37 = colFn colCertDiv_99_37_15.D1 (m := 25) from colCertDiv_99_37_15.bind1,
    show colData2 (⟨99, by decide⟩ : Fin 148)
        ((colE2 ⟨37, by decide⟩ 15 hp : ↥(Q2.reps ⟨37, by decide⟩)) : Coordinate 2)
        Q2.T99_37_2 = colFn colCertDiv_99_37_15.D2 (m := 25) from colCertDiv_99_37_15.bind2]
  rw [alnId_99 j hj]
  exact fastcode_of_div ⟨99, by decide⟩ _ _ _
    ((alnId_99 j hj) ▸ Q2.listedAt (⟨99, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨99, by decide⟩ : Fin 148) hj hq).1) colCertDiv_99_37_15_match


theorem leaf_99_37_20 (hp : 20 < (Q2.transData.getD 37 []).length)
    (j : Nat) (hj : j < (repChars.getD 99 []).length)
    (hq : (normIsRep.getD 99 []).getD j false = true) :
    species (Q2.reps (⟨37, by decide⟩ : Fin 148)) (colE2 ⟨37, by decide⟩ 20 hp)
        (rowE2 (⟨99, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨37, by decide⟩ : Fin 148))
        (colE1 ⟨37, by decide⟩ 20 (transLenTr ⟨37, by decide⟩ 20 hp))
        (rowE1 (⟨99, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨99, by decide⟩ : Fin 148) ⟨37, by decide⟩ _
      (validAt ⟨99, by decide⟩ (listedAt ⟨99, by decide⟩ hj))
      (colE1 ⟨37, by decide⟩ 20 (transLenTr ⟨37, by decide⟩ 20 hp)) T99_37
      hfix99_37 hinj99_37 hcardT99_37
      (fun i => conj_mem_of_fixedPoints _ _ (T99_37 i) (hfix99_37 i) _)
      ⟨99, by decide⟩ ⟨37, by decide⟩ _
      (Q2.validAt ⟨99, by decide⟩ (Q2.listedAt ⟨99, by decide⟩
        (alnCheck_rep ⟨99, by decide⟩ hj hq).1))
      (colE2 ⟨37, by decide⟩ 20 hp) Q2.T99_37_2 Q2.hfix99_37_2 Q2.hinj99_37_2
      Q2.hcardT99_37_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T99_37_2 i) (Q2.hfix99_37_2 i) _)
      ?_).symm
  rw [show colData1 (⟨99, by decide⟩ : Fin 148)
        ((colE1 ⟨37, by decide⟩ 20 (transLenTr ⟨37, by decide⟩ 20 hp) : ↥(reps ⟨37, by decide⟩)) : Coordinate 1)
        T99_37 = colFn colCertDiv_99_37_20.D1 (m := 25) from colCertDiv_99_37_20.bind1,
    show colData2 (⟨99, by decide⟩ : Fin 148)
        ((colE2 ⟨37, by decide⟩ 20 hp : ↥(Q2.reps ⟨37, by decide⟩)) : Coordinate 2)
        Q2.T99_37_2 = colFn colCertDiv_99_37_20.D2 (m := 25) from colCertDiv_99_37_20.bind2]
  rw [alnId_99 j hj]
  exact fastcode_of_div ⟨99, by decide⟩ _ _ _
    ((alnId_99 j hj) ▸ Q2.listedAt (⟨99, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨99, by decide⟩ : Fin 148) hj hq).1) colCertDiv_99_37_20_match


theorem leaf_99_53_0 (hp : 0 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 99 []).length)
    (hq : (normIsRep.getD 99 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 0 hp)
        (rowE2 (⟨99, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 0 (transLenTr ⟨53, by decide⟩ 0 hp))
        (rowE1 (⟨99, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨99, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨99, by decide⟩ (listedAt ⟨99, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 0 (transLenTr ⟨53, by decide⟩ 0 hp)) T99_53
      hfix99_53 hinj99_53 hcardT99_53
      (fun i => conj_mem_of_fixedPoints _ _ (T99_53 i) (hfix99_53 i) _)
      ⟨99, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨99, by decide⟩ (Q2.listedAt ⟨99, by decide⟩
        (alnCheck_rep ⟨99, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 0 hp) Q2.T99_53_2 Q2.hfix99_53_2 Q2.hinj99_53_2
      Q2.hcardT99_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T99_53_2 i) (Q2.hfix99_53_2 i) _)
      colCert_99_53_0.hD ?_).symm
  rw [alnId_99 j hj]


theorem leaf_99_53_1 (hp : 1 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 99 []).length)
    (hq : (normIsRep.getD 99 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 1 hp)
        (rowE2 (⟨99, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 1 (transLenTr ⟨53, by decide⟩ 1 hp))
        (rowE1 (⟨99, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨99, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨99, by decide⟩ (listedAt ⟨99, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 1 (transLenTr ⟨53, by decide⟩ 1 hp)) T99_53
      hfix99_53 hinj99_53 hcardT99_53
      (fun i => conj_mem_of_fixedPoints _ _ (T99_53 i) (hfix99_53 i) _)
      ⟨99, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨99, by decide⟩ (Q2.listedAt ⟨99, by decide⟩
        (alnCheck_rep ⟨99, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 1 hp) Q2.T99_53_2 Q2.hfix99_53_2 Q2.hinj99_53_2
      Q2.hcardT99_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T99_53_2 i) (Q2.hfix99_53_2 i) _)
      colCert_99_53_1.hD ?_).symm
  rw [alnId_99 j hj]


theorem leaf_99_53_2 (hp : 2 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 99 []).length)
    (hq : (normIsRep.getD 99 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 2 hp)
        (rowE2 (⟨99, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 2 (transLenTr ⟨53, by decide⟩ 2 hp))
        (rowE1 (⟨99, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨99, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨99, by decide⟩ (listedAt ⟨99, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 2 (transLenTr ⟨53, by decide⟩ 2 hp)) T99_53
      hfix99_53 hinj99_53 hcardT99_53
      (fun i => conj_mem_of_fixedPoints _ _ (T99_53 i) (hfix99_53 i) _)
      ⟨99, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨99, by decide⟩ (Q2.listedAt ⟨99, by decide⟩
        (alnCheck_rep ⟨99, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 2 hp) Q2.T99_53_2 Q2.hfix99_53_2 Q2.hinj99_53_2
      Q2.hcardT99_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T99_53_2 i) (Q2.hfix99_53_2 i) _)
      colCert_99_53_2.hD ?_).symm
  rw [alnId_99 j hj]


theorem leaf_99_53_3 (hp : 3 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 99 []).length)
    (hq : (normIsRep.getD 99 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 3 hp)
        (rowE2 (⟨99, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 3 (transLenTr ⟨53, by decide⟩ 3 hp))
        (rowE1 (⟨99, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨99, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨99, by decide⟩ (listedAt ⟨99, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 3 (transLenTr ⟨53, by decide⟩ 3 hp)) T99_53
      hfix99_53 hinj99_53 hcardT99_53
      (fun i => conj_mem_of_fixedPoints _ _ (T99_53 i) (hfix99_53 i) _)
      ⟨99, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨99, by decide⟩ (Q2.listedAt ⟨99, by decide⟩
        (alnCheck_rep ⟨99, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 3 hp) Q2.T99_53_2 Q2.hfix99_53_2 Q2.hinj99_53_2
      Q2.hcardT99_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T99_53_2 i) (Q2.hfix99_53_2 i) _)
      colCert_99_53_3.hD ?_).symm
  rw [alnId_99 j hj]


theorem leaf_99_53_4 (hp : 4 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 99 []).length)
    (hq : (normIsRep.getD 99 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 4 hp)
        (rowE2 (⟨99, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 4 (transLenTr ⟨53, by decide⟩ 4 hp))
        (rowE1 (⟨99, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨99, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨99, by decide⟩ (listedAt ⟨99, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 4 (transLenTr ⟨53, by decide⟩ 4 hp)) T99_53
      hfix99_53 hinj99_53 hcardT99_53
      (fun i => conj_mem_of_fixedPoints _ _ (T99_53 i) (hfix99_53 i) _)
      ⟨99, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨99, by decide⟩ (Q2.listedAt ⟨99, by decide⟩
        (alnCheck_rep ⟨99, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 4 hp) Q2.T99_53_2 Q2.hfix99_53_2 Q2.hinj99_53_2
      Q2.hcardT99_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T99_53_2 i) (Q2.hfix99_53_2 i) _)
      colCert_99_53_4.hD ?_).symm
  rw [alnId_99 j hj]


theorem leaf_99_53_5 (hp : 5 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 99 []).length)
    (hq : (normIsRep.getD 99 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 5 hp)
        (rowE2 (⟨99, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 5 (transLenTr ⟨53, by decide⟩ 5 hp))
        (rowE1 (⟨99, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨99, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨99, by decide⟩ (listedAt ⟨99, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 5 (transLenTr ⟨53, by decide⟩ 5 hp)) T99_53
      hfix99_53 hinj99_53 hcardT99_53
      (fun i => conj_mem_of_fixedPoints _ _ (T99_53 i) (hfix99_53 i) _)
      ⟨99, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨99, by decide⟩ (Q2.listedAt ⟨99, by decide⟩
        (alnCheck_rep ⟨99, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 5 hp) Q2.T99_53_2 Q2.hfix99_53_2 Q2.hinj99_53_2
      Q2.hcardT99_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T99_53_2 i) (Q2.hfix99_53_2 i) _)
      colCert_99_53_5.hD ?_).symm
  rw [alnId_99 j hj]


theorem leaf_99_53_10 (hp : 10 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 99 []).length)
    (hq : (normIsRep.getD 99 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 10 hp)
        (rowE2 (⟨99, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 10 (transLenTr ⟨53, by decide⟩ 10 hp))
        (rowE1 (⟨99, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨99, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨99, by decide⟩ (listedAt ⟨99, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 10 (transLenTr ⟨53, by decide⟩ 10 hp)) T99_53
      hfix99_53 hinj99_53 hcardT99_53
      (fun i => conj_mem_of_fixedPoints _ _ (T99_53 i) (hfix99_53 i) _)
      ⟨99, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨99, by decide⟩ (Q2.listedAt ⟨99, by decide⟩
        (alnCheck_rep ⟨99, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 10 hp) Q2.T99_53_2 Q2.hfix99_53_2 Q2.hinj99_53_2
      Q2.hcardT99_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T99_53_2 i) (Q2.hfix99_53_2 i) _)
      colCert_99_53_10.hD ?_).symm
  rw [alnId_99 j hj]


theorem leaf_99_53_15 (hp : 15 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 99 []).length)
    (hq : (normIsRep.getD 99 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 15 hp)
        (rowE2 (⟨99, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 15 (transLenTr ⟨53, by decide⟩ 15 hp))
        (rowE1 (⟨99, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨99, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨99, by decide⟩ (listedAt ⟨99, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 15 (transLenTr ⟨53, by decide⟩ 15 hp)) T99_53
      hfix99_53 hinj99_53 hcardT99_53
      (fun i => conj_mem_of_fixedPoints _ _ (T99_53 i) (hfix99_53 i) _)
      ⟨99, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨99, by decide⟩ (Q2.listedAt ⟨99, by decide⟩
        (alnCheck_rep ⟨99, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 15 hp) Q2.T99_53_2 Q2.hfix99_53_2 Q2.hinj99_53_2
      Q2.hcardT99_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T99_53_2 i) (Q2.hfix99_53_2 i) _)
      colCert_99_53_15.hD ?_).symm
  rw [alnId_99 j hj]


theorem leaf_99_53_20 (hp : 20 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 99 []).length)
    (hq : (normIsRep.getD 99 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 20 hp)
        (rowE2 (⟨99, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 20 (transLenTr ⟨53, by decide⟩ 20 hp))
        (rowE1 (⟨99, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨99, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨99, by decide⟩ (listedAt ⟨99, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 20 (transLenTr ⟨53, by decide⟩ 20 hp)) T99_53
      hfix99_53 hinj99_53 hcardT99_53
      (fun i => conj_mem_of_fixedPoints _ _ (T99_53 i) (hfix99_53 i) _)
      ⟨99, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨99, by decide⟩ (Q2.listedAt ⟨99, by decide⟩
        (alnCheck_rep ⟨99, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 20 hp) Q2.T99_53_2 Q2.hfix99_53_2 Q2.hinj99_53_2
      Q2.hcardT99_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T99_53_2 i) (Q2.hfix99_53_2 i) _)
      colCert_99_53_20.hD ?_).symm
  rw [alnId_99 j hj]


theorem leaf_99_99_0 (hp : 0 < (Q2.transData.getD 99 []).length)
    (j : Nat) (hj : j < (repChars.getD 99 []).length)
    (hq : (normIsRep.getD 99 []).getD j false = true) :
    species (Q2.reps (⟨99, by decide⟩ : Fin 148)) (colE2 ⟨99, by decide⟩ 0 hp)
        (rowE2 (⟨99, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨99, by decide⟩ : Fin 148))
        (colE1 ⟨99, by decide⟩ 0 (transLenTr ⟨99, by decide⟩ 0 hp))
        (rowE1 (⟨99, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨99, by decide⟩ : Fin 148) ⟨99, by decide⟩ _
      (validAt ⟨99, by decide⟩ (listedAt ⟨99, by decide⟩ hj))
      (colE1 ⟨99, by decide⟩ 0 (transLenTr ⟨99, by decide⟩ 0 hp)) T99_99
      hfix99_99 hinj99_99 hcardT99_99
      (fun i => conj_mem_of_fixedPoints _ _ (T99_99 i) (hfix99_99 i) _)
      ⟨99, by decide⟩ ⟨99, by decide⟩ _
      (Q2.validAt ⟨99, by decide⟩ (Q2.listedAt ⟨99, by decide⟩
        (alnCheck_rep ⟨99, by decide⟩ hj hq).1))
      (colE2 ⟨99, by decide⟩ 0 hp) Q2.T99_99_2 Q2.hfix99_99_2 Q2.hinj99_99_2
      Q2.hcardT99_99_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T99_99_2 i) (Q2.hfix99_99_2 i) _)
      colCert_99_99_0.hD ?_).symm
  rw [alnId_99 j hj]


theorem leaf_99_99_1 (hp : 1 < (Q2.transData.getD 99 []).length)
    (j : Nat) (hj : j < (repChars.getD 99 []).length)
    (hq : (normIsRep.getD 99 []).getD j false = true) :
    species (Q2.reps (⟨99, by decide⟩ : Fin 148)) (colE2 ⟨99, by decide⟩ 1 hp)
        (rowE2 (⟨99, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨99, by decide⟩ : Fin 148))
        (colE1 ⟨99, by decide⟩ 1 (transLenTr ⟨99, by decide⟩ 1 hp))
        (rowE1 (⟨99, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨99, by decide⟩ : Fin 148) ⟨99, by decide⟩ _
      (validAt ⟨99, by decide⟩ (listedAt ⟨99, by decide⟩ hj))
      (colE1 ⟨99, by decide⟩ 1 (transLenTr ⟨99, by decide⟩ 1 hp)) T99_99
      hfix99_99 hinj99_99 hcardT99_99
      (fun i => conj_mem_of_fixedPoints _ _ (T99_99 i) (hfix99_99 i) _)
      ⟨99, by decide⟩ ⟨99, by decide⟩ _
      (Q2.validAt ⟨99, by decide⟩ (Q2.listedAt ⟨99, by decide⟩
        (alnCheck_rep ⟨99, by decide⟩ hj hq).1))
      (colE2 ⟨99, by decide⟩ 1 hp) Q2.T99_99_2 Q2.hfix99_99_2 Q2.hinj99_99_2
      Q2.hcardT99_99_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T99_99_2 i) (Q2.hfix99_99_2 i) _)
      colCert_99_99_1.hD ?_).symm
  rw [alnId_99 j hj]


theorem leaf_99_99_2 (hp : 2 < (Q2.transData.getD 99 []).length)
    (j : Nat) (hj : j < (repChars.getD 99 []).length)
    (hq : (normIsRep.getD 99 []).getD j false = true) :
    species (Q2.reps (⟨99, by decide⟩ : Fin 148)) (colE2 ⟨99, by decide⟩ 2 hp)
        (rowE2 (⟨99, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨99, by decide⟩ : Fin 148))
        (colE1 ⟨99, by decide⟩ 2 (transLenTr ⟨99, by decide⟩ 2 hp))
        (rowE1 (⟨99, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨99, by decide⟩ : Fin 148) ⟨99, by decide⟩ _
      (validAt ⟨99, by decide⟩ (listedAt ⟨99, by decide⟩ hj))
      (colE1 ⟨99, by decide⟩ 2 (transLenTr ⟨99, by decide⟩ 2 hp)) T99_99
      hfix99_99 hinj99_99 hcardT99_99
      (fun i => conj_mem_of_fixedPoints _ _ (T99_99 i) (hfix99_99 i) _)
      ⟨99, by decide⟩ ⟨99, by decide⟩ _
      (Q2.validAt ⟨99, by decide⟩ (Q2.listedAt ⟨99, by decide⟩
        (alnCheck_rep ⟨99, by decide⟩ hj hq).1))
      (colE2 ⟨99, by decide⟩ 2 hp) Q2.T99_99_2 Q2.hfix99_99_2 Q2.hinj99_99_2
      Q2.hcardT99_99_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T99_99_2 i) (Q2.hfix99_99_2 i) _)
      colCert_99_99_2.hD ?_).symm
  rw [alnId_99 j hj]


theorem leaf_99_99_3 (hp : 3 < (Q2.transData.getD 99 []).length)
    (j : Nat) (hj : j < (repChars.getD 99 []).length)
    (hq : (normIsRep.getD 99 []).getD j false = true) :
    species (Q2.reps (⟨99, by decide⟩ : Fin 148)) (colE2 ⟨99, by decide⟩ 3 hp)
        (rowE2 (⟨99, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨99, by decide⟩ : Fin 148))
        (colE1 ⟨99, by decide⟩ 3 (transLenTr ⟨99, by decide⟩ 3 hp))
        (rowE1 (⟨99, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨99, by decide⟩ : Fin 148) ⟨99, by decide⟩ _
      (validAt ⟨99, by decide⟩ (listedAt ⟨99, by decide⟩ hj))
      (colE1 ⟨99, by decide⟩ 3 (transLenTr ⟨99, by decide⟩ 3 hp)) T99_99
      hfix99_99 hinj99_99 hcardT99_99
      (fun i => conj_mem_of_fixedPoints _ _ (T99_99 i) (hfix99_99 i) _)
      ⟨99, by decide⟩ ⟨99, by decide⟩ _
      (Q2.validAt ⟨99, by decide⟩ (Q2.listedAt ⟨99, by decide⟩
        (alnCheck_rep ⟨99, by decide⟩ hj hq).1))
      (colE2 ⟨99, by decide⟩ 3 hp) Q2.T99_99_2 Q2.hfix99_99_2 Q2.hinj99_99_2
      Q2.hcardT99_99_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T99_99_2 i) (Q2.hfix99_99_2 i) _)
      colCert_99_99_3.hD ?_).symm
  rw [alnId_99 j hj]


theorem leaf_99_99_4 (hp : 4 < (Q2.transData.getD 99 []).length)
    (j : Nat) (hj : j < (repChars.getD 99 []).length)
    (hq : (normIsRep.getD 99 []).getD j false = true) :
    species (Q2.reps (⟨99, by decide⟩ : Fin 148)) (colE2 ⟨99, by decide⟩ 4 hp)
        (rowE2 (⟨99, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨99, by decide⟩ : Fin 148))
        (colE1 ⟨99, by decide⟩ 4 (transLenTr ⟨99, by decide⟩ 4 hp))
        (rowE1 (⟨99, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨99, by decide⟩ : Fin 148) ⟨99, by decide⟩ _
      (validAt ⟨99, by decide⟩ (listedAt ⟨99, by decide⟩ hj))
      (colE1 ⟨99, by decide⟩ 4 (transLenTr ⟨99, by decide⟩ 4 hp)) T99_99
      hfix99_99 hinj99_99 hcardT99_99
      (fun i => conj_mem_of_fixedPoints _ _ (T99_99 i) (hfix99_99 i) _)
      ⟨99, by decide⟩ ⟨99, by decide⟩ _
      (Q2.validAt ⟨99, by decide⟩ (Q2.listedAt ⟨99, by decide⟩
        (alnCheck_rep ⟨99, by decide⟩ hj hq).1))
      (colE2 ⟨99, by decide⟩ 4 hp) Q2.T99_99_2 Q2.hfix99_99_2 Q2.hinj99_99_2
      Q2.hcardT99_99_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T99_99_2 i) (Q2.hfix99_99_2 i) _)
      colCert_99_99_4.hD ?_).symm
  rw [alnId_99 j hj]


theorem leaf_99_99_5 (hp : 5 < (Q2.transData.getD 99 []).length)
    (j : Nat) (hj : j < (repChars.getD 99 []).length)
    (hq : (normIsRep.getD 99 []).getD j false = true) :
    species (Q2.reps (⟨99, by decide⟩ : Fin 148)) (colE2 ⟨99, by decide⟩ 5 hp)
        (rowE2 (⟨99, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨99, by decide⟩ : Fin 148))
        (colE1 ⟨99, by decide⟩ 5 (transLenTr ⟨99, by decide⟩ 5 hp))
        (rowE1 (⟨99, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨99, by decide⟩ : Fin 148) ⟨99, by decide⟩ _
      (validAt ⟨99, by decide⟩ (listedAt ⟨99, by decide⟩ hj))
      (colE1 ⟨99, by decide⟩ 5 (transLenTr ⟨99, by decide⟩ 5 hp)) T99_99
      hfix99_99 hinj99_99 hcardT99_99
      (fun i => conj_mem_of_fixedPoints _ _ (T99_99 i) (hfix99_99 i) _)
      ⟨99, by decide⟩ ⟨99, by decide⟩ _
      (Q2.validAt ⟨99, by decide⟩ (Q2.listedAt ⟨99, by decide⟩
        (alnCheck_rep ⟨99, by decide⟩ hj hq).1))
      (colE2 ⟨99, by decide⟩ 5 hp) Q2.T99_99_2 Q2.hfix99_99_2 Q2.hinj99_99_2
      Q2.hcardT99_99_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T99_99_2 i) (Q2.hfix99_99_2 i) _)
      colCert_99_99_5.hD ?_).symm
  rw [alnId_99 j hj]


theorem leaf_99_99_10 (hp : 10 < (Q2.transData.getD 99 []).length)
    (j : Nat) (hj : j < (repChars.getD 99 []).length)
    (hq : (normIsRep.getD 99 []).getD j false = true) :
    species (Q2.reps (⟨99, by decide⟩ : Fin 148)) (colE2 ⟨99, by decide⟩ 10 hp)
        (rowE2 (⟨99, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨99, by decide⟩ : Fin 148))
        (colE1 ⟨99, by decide⟩ 10 (transLenTr ⟨99, by decide⟩ 10 hp))
        (rowE1 (⟨99, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨99, by decide⟩ : Fin 148) ⟨99, by decide⟩ _
      (validAt ⟨99, by decide⟩ (listedAt ⟨99, by decide⟩ hj))
      (colE1 ⟨99, by decide⟩ 10 (transLenTr ⟨99, by decide⟩ 10 hp)) T99_99
      hfix99_99 hinj99_99 hcardT99_99
      (fun i => conj_mem_of_fixedPoints _ _ (T99_99 i) (hfix99_99 i) _)
      ⟨99, by decide⟩ ⟨99, by decide⟩ _
      (Q2.validAt ⟨99, by decide⟩ (Q2.listedAt ⟨99, by decide⟩
        (alnCheck_rep ⟨99, by decide⟩ hj hq).1))
      (colE2 ⟨99, by decide⟩ 10 hp) Q2.T99_99_2 Q2.hfix99_99_2 Q2.hinj99_99_2
      Q2.hcardT99_99_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T99_99_2 i) (Q2.hfix99_99_2 i) _)
      colCert_99_99_10.hD ?_).symm
  rw [alnId_99 j hj]


theorem leaf_99_99_15 (hp : 15 < (Q2.transData.getD 99 []).length)
    (j : Nat) (hj : j < (repChars.getD 99 []).length)
    (hq : (normIsRep.getD 99 []).getD j false = true) :
    species (Q2.reps (⟨99, by decide⟩ : Fin 148)) (colE2 ⟨99, by decide⟩ 15 hp)
        (rowE2 (⟨99, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨99, by decide⟩ : Fin 148))
        (colE1 ⟨99, by decide⟩ 15 (transLenTr ⟨99, by decide⟩ 15 hp))
        (rowE1 (⟨99, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨99, by decide⟩ : Fin 148) ⟨99, by decide⟩ _
      (validAt ⟨99, by decide⟩ (listedAt ⟨99, by decide⟩ hj))
      (colE1 ⟨99, by decide⟩ 15 (transLenTr ⟨99, by decide⟩ 15 hp)) T99_99
      hfix99_99 hinj99_99 hcardT99_99
      (fun i => conj_mem_of_fixedPoints _ _ (T99_99 i) (hfix99_99 i) _)
      ⟨99, by decide⟩ ⟨99, by decide⟩ _
      (Q2.validAt ⟨99, by decide⟩ (Q2.listedAt ⟨99, by decide⟩
        (alnCheck_rep ⟨99, by decide⟩ hj hq).1))
      (colE2 ⟨99, by decide⟩ 15 hp) Q2.T99_99_2 Q2.hfix99_99_2 Q2.hinj99_99_2
      Q2.hcardT99_99_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T99_99_2 i) (Q2.hfix99_99_2 i) _)
      colCert_99_99_15.hD ?_).symm
  rw [alnId_99 j hj]


theorem leaf_99_99_20 (hp : 20 < (Q2.transData.getD 99 []).length)
    (j : Nat) (hj : j < (repChars.getD 99 []).length)
    (hq : (normIsRep.getD 99 []).getD j false = true) :
    species (Q2.reps (⟨99, by decide⟩ : Fin 148)) (colE2 ⟨99, by decide⟩ 20 hp)
        (rowE2 (⟨99, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨99, by decide⟩ : Fin 148))
        (colE1 ⟨99, by decide⟩ 20 (transLenTr ⟨99, by decide⟩ 20 hp))
        (rowE1 (⟨99, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨99, by decide⟩ : Fin 148) ⟨99, by decide⟩ _
      (validAt ⟨99, by decide⟩ (listedAt ⟨99, by decide⟩ hj))
      (colE1 ⟨99, by decide⟩ 20 (transLenTr ⟨99, by decide⟩ 20 hp)) T99_99
      hfix99_99 hinj99_99 hcardT99_99
      (fun i => conj_mem_of_fixedPoints _ _ (T99_99 i) (hfix99_99 i) _)
      ⟨99, by decide⟩ ⟨99, by decide⟩ _
      (Q2.validAt ⟨99, by decide⟩ (Q2.listedAt ⟨99, by decide⟩
        (alnCheck_rep ⟨99, by decide⟩ hj hq).1))
      (colE2 ⟨99, by decide⟩ 20 hp) Q2.T99_99_2 Q2.hfix99_99_2 Q2.hinj99_99_2
      Q2.hcardT99_99_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T99_99_2 i) (Q2.hfix99_99_2 i) _)
      colCert_99_99_20.hD ?_).symm
  rw [alnId_99 j hj]


theorem leaf_100_10_0 (hp : 0 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 100 []).length)
    (hq : (normIsRep.getD 100 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 0 hp)
        (rowE2 (⟨100, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 0 (transLenTr ⟨10, by decide⟩ 0 hp))
        (rowE1 (⟨100, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨100, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨100, by decide⟩ (listedAt ⟨100, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 0 (transLenTr ⟨10, by decide⟩ 0 hp)) T100_10
      hfix100_10 hinj100_10 hcardT100_10
      (fun i => conj_mem_of_fixedPoints _ _ (T100_10 i) (hfix100_10 i) _)
      ⟨100, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨100, by decide⟩ (Q2.listedAt ⟨100, by decide⟩
        (alnCheck_rep ⟨100, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 0 hp) Q2.T100_10_2 Q2.hfix100_10_2 Q2.hinj100_10_2
      Q2.hcardT100_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T100_10_2 i) (Q2.hfix100_10_2 i) _)
      ?_).symm
  rw [show colData1 (⟨100, by decide⟩ : Fin 148)
        ((colE1 ⟨10, by decide⟩ 0 (transLenTr ⟨10, by decide⟩ 0 hp) : ↥(reps ⟨10, by decide⟩)) : Coordinate 1)
        T100_10 = colFn colCert_100_10_0.D (m := 25) from colCert_100_10_0.bind1,
    show colData2 (⟨100, by decide⟩ : Fin 148)
        ((colE2 ⟨10, by decide⟩ 0 hp : ↥(Q2.reps ⟨10, by decide⟩)) : Coordinate 2)
        Q2.T100_10_2 = colFn colCert_100_10_0.D (m := 25) from colCert_100_10_0.bind2]
  exact alnAll_100_10_0 j hj hq

theorem leaf_100_10_1 (hp : 1 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 100 []).length)
    (hq : (normIsRep.getD 100 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 1 hp)
        (rowE2 (⟨100, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 1 (transLenTr ⟨10, by decide⟩ 1 hp))
        (rowE1 (⟨100, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨100, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨100, by decide⟩ (listedAt ⟨100, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 1 (transLenTr ⟨10, by decide⟩ 1 hp)) T100_10
      hfix100_10 hinj100_10 hcardT100_10
      (fun i => conj_mem_of_fixedPoints _ _ (T100_10 i) (hfix100_10 i) _)
      ⟨100, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨100, by decide⟩ (Q2.listedAt ⟨100, by decide⟩
        (alnCheck_rep ⟨100, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 1 hp) Q2.T100_10_2 Q2.hfix100_10_2 Q2.hinj100_10_2
      Q2.hcardT100_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T100_10_2 i) (Q2.hfix100_10_2 i) _)
      ?_).symm
  rw [show colData1 (⟨100, by decide⟩ : Fin 148)
        ((colE1 ⟨10, by decide⟩ 1 (transLenTr ⟨10, by decide⟩ 1 hp) : ↥(reps ⟨10, by decide⟩)) : Coordinate 1)
        T100_10 = colFn colCert_100_10_1.D (m := 25) from colCert_100_10_1.bind1,
    show colData2 (⟨100, by decide⟩ : Fin 148)
        ((colE2 ⟨10, by decide⟩ 1 hp : ↥(Q2.reps ⟨10, by decide⟩)) : Coordinate 2)
        Q2.T100_10_2 = colFn colCert_100_10_1.D (m := 25) from colCert_100_10_1.bind2]
  exact alnAll_100_10_1 j hj hq

theorem leaf_100_10_2 (hp : 2 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 100 []).length)
    (hq : (normIsRep.getD 100 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 2 hp)
        (rowE2 (⟨100, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 2 (transLenTr ⟨10, by decide⟩ 2 hp))
        (rowE1 (⟨100, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨100, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨100, by decide⟩ (listedAt ⟨100, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 2 (transLenTr ⟨10, by decide⟩ 2 hp)) T100_10
      hfix100_10 hinj100_10 hcardT100_10
      (fun i => conj_mem_of_fixedPoints _ _ (T100_10 i) (hfix100_10 i) _)
      ⟨100, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨100, by decide⟩ (Q2.listedAt ⟨100, by decide⟩
        (alnCheck_rep ⟨100, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 2 hp) Q2.T100_10_2 Q2.hfix100_10_2 Q2.hinj100_10_2
      Q2.hcardT100_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T100_10_2 i) (Q2.hfix100_10_2 i) _)
      ?_).symm
  rw [show colData1 (⟨100, by decide⟩ : Fin 148)
        ((colE1 ⟨10, by decide⟩ 2 (transLenTr ⟨10, by decide⟩ 2 hp) : ↥(reps ⟨10, by decide⟩)) : Coordinate 1)
        T100_10 = colFn colCert_100_10_2.D (m := 25) from colCert_100_10_2.bind1,
    show colData2 (⟨100, by decide⟩ : Fin 148)
        ((colE2 ⟨10, by decide⟩ 2 hp : ↥(Q2.reps ⟨10, by decide⟩)) : Coordinate 2)
        Q2.T100_10_2 = colFn colCert_100_10_2.D (m := 25) from colCert_100_10_2.bind2]
  exact alnAll_100_10_2 j hj hq

theorem leaf_100_10_3 (hp : 3 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 100 []).length)
    (hq : (normIsRep.getD 100 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 3 hp)
        (rowE2 (⟨100, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 3 (transLenTr ⟨10, by decide⟩ 3 hp))
        (rowE1 (⟨100, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨100, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨100, by decide⟩ (listedAt ⟨100, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 3 (transLenTr ⟨10, by decide⟩ 3 hp)) T100_10
      hfix100_10 hinj100_10 hcardT100_10
      (fun i => conj_mem_of_fixedPoints _ _ (T100_10 i) (hfix100_10 i) _)
      ⟨100, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨100, by decide⟩ (Q2.listedAt ⟨100, by decide⟩
        (alnCheck_rep ⟨100, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 3 hp) Q2.T100_10_2 Q2.hfix100_10_2 Q2.hinj100_10_2
      Q2.hcardT100_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T100_10_2 i) (Q2.hfix100_10_2 i) _)
      ?_).symm
  rw [show colData1 (⟨100, by decide⟩ : Fin 148)
        ((colE1 ⟨10, by decide⟩ 3 (transLenTr ⟨10, by decide⟩ 3 hp) : ↥(reps ⟨10, by decide⟩)) : Coordinate 1)
        T100_10 = colFn colCert_100_10_3.D (m := 25) from colCert_100_10_3.bind1,
    show colData2 (⟨100, by decide⟩ : Fin 148)
        ((colE2 ⟨10, by decide⟩ 3 hp : ↥(Q2.reps ⟨10, by decide⟩)) : Coordinate 2)
        Q2.T100_10_2 = colFn colCert_100_10_3.D (m := 25) from colCert_100_10_3.bind2]
  exact alnAll_100_10_3 j hj hq

theorem leaf_100_10_4 (hp : 4 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 100 []).length)
    (hq : (normIsRep.getD 100 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 4 hp)
        (rowE2 (⟨100, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 4 (transLenTr ⟨10, by decide⟩ 4 hp))
        (rowE1 (⟨100, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨100, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨100, by decide⟩ (listedAt ⟨100, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 4 (transLenTr ⟨10, by decide⟩ 4 hp)) T100_10
      hfix100_10 hinj100_10 hcardT100_10
      (fun i => conj_mem_of_fixedPoints _ _ (T100_10 i) (hfix100_10 i) _)
      ⟨100, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨100, by decide⟩ (Q2.listedAt ⟨100, by decide⟩
        (alnCheck_rep ⟨100, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 4 hp) Q2.T100_10_2 Q2.hfix100_10_2 Q2.hinj100_10_2
      Q2.hcardT100_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T100_10_2 i) (Q2.hfix100_10_2 i) _)
      ?_).symm
  rw [show colData1 (⟨100, by decide⟩ : Fin 148)
        ((colE1 ⟨10, by decide⟩ 4 (transLenTr ⟨10, by decide⟩ 4 hp) : ↥(reps ⟨10, by decide⟩)) : Coordinate 1)
        T100_10 = colFn colCert_100_10_4.D (m := 25) from colCert_100_10_4.bind1,
    show colData2 (⟨100, by decide⟩ : Fin 148)
        ((colE2 ⟨10, by decide⟩ 4 hp : ↥(Q2.reps ⟨10, by decide⟩)) : Coordinate 2)
        Q2.T100_10_2 = colFn colCert_100_10_4.D (m := 25) from colCert_100_10_4.bind2]
  exact alnAll_100_10_4 j hj hq

theorem leaf_100_12_0 (hp : 0 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 100 []).length)
    (hq : (normIsRep.getD 100 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 0 hp)
        (rowE2 (⟨100, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp))
        (rowE1 (⟨100, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨100, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨100, by decide⟩ (listedAt ⟨100, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp)) T100_12
      hfix100_12 hinj100_12 hcardT100_12
      (fun i => conj_mem_of_fixedPoints _ _ (T100_12 i) (hfix100_12 i) _)
      ⟨100, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨100, by decide⟩ (Q2.listedAt ⟨100, by decide⟩
        (alnCheck_rep ⟨100, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 0 hp) Q2.T100_12_2 Q2.hfix100_12_2 Q2.hinj100_12_2
      Q2.hcardT100_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T100_12_2 i) (Q2.hfix100_12_2 i) _)
      ?_).symm
  rw [show colData1 (⟨100, by decide⟩ : Fin 148)
        ((colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp) : ↥(reps ⟨12, by decide⟩)) : Coordinate 1)
        T100_12 = colFn colCert_100_12_0.D (m := 25) from colCert_100_12_0.bind1,
    show colData2 (⟨100, by decide⟩ : Fin 148)
        ((colE2 ⟨12, by decide⟩ 0 hp : ↥(Q2.reps ⟨12, by decide⟩)) : Coordinate 2)
        Q2.T100_12_2 = colFn colCert_100_12_0.D (m := 25) from colCert_100_12_0.bind2]
  exact alnAll_100_12_0 j hj hq

theorem leaf_100_12_1 (hp : 1 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 100 []).length)
    (hq : (normIsRep.getD 100 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 1 hp)
        (rowE2 (⟨100, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp))
        (rowE1 (⟨100, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨100, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨100, by decide⟩ (listedAt ⟨100, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp)) T100_12
      hfix100_12 hinj100_12 hcardT100_12
      (fun i => conj_mem_of_fixedPoints _ _ (T100_12 i) (hfix100_12 i) _)
      ⟨100, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨100, by decide⟩ (Q2.listedAt ⟨100, by decide⟩
        (alnCheck_rep ⟨100, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 1 hp) Q2.T100_12_2 Q2.hfix100_12_2 Q2.hinj100_12_2
      Q2.hcardT100_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T100_12_2 i) (Q2.hfix100_12_2 i) _)
      ?_).symm
  rw [show colData1 (⟨100, by decide⟩ : Fin 148)
        ((colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp) : ↥(reps ⟨12, by decide⟩)) : Coordinate 1)
        T100_12 = colFn colCert_100_12_1.D (m := 25) from colCert_100_12_1.bind1,
    show colData2 (⟨100, by decide⟩ : Fin 148)
        ((colE2 ⟨12, by decide⟩ 1 hp : ↥(Q2.reps ⟨12, by decide⟩)) : Coordinate 2)
        Q2.T100_12_2 = colFn colCert_100_12_1.D (m := 25) from colCert_100_12_1.bind2]
  exact alnAll_100_12_1 j hj hq

theorem leaf_100_12_2 (hp : 2 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 100 []).length)
    (hq : (normIsRep.getD 100 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 2 hp)
        (rowE2 (⟨100, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp))
        (rowE1 (⟨100, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨100, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨100, by decide⟩ (listedAt ⟨100, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp)) T100_12
      hfix100_12 hinj100_12 hcardT100_12
      (fun i => conj_mem_of_fixedPoints _ _ (T100_12 i) (hfix100_12 i) _)
      ⟨100, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨100, by decide⟩ (Q2.listedAt ⟨100, by decide⟩
        (alnCheck_rep ⟨100, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 2 hp) Q2.T100_12_2 Q2.hfix100_12_2 Q2.hinj100_12_2
      Q2.hcardT100_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T100_12_2 i) (Q2.hfix100_12_2 i) _)
      ?_).symm
  rw [show colData1 (⟨100, by decide⟩ : Fin 148)
        ((colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp) : ↥(reps ⟨12, by decide⟩)) : Coordinate 1)
        T100_12 = colFn colCert_100_12_2.D (m := 25) from colCert_100_12_2.bind1,
    show colData2 (⟨100, by decide⟩ : Fin 148)
        ((colE2 ⟨12, by decide⟩ 2 hp : ↥(Q2.reps ⟨12, by decide⟩)) : Coordinate 2)
        Q2.T100_12_2 = colFn colCert_100_12_2.D (m := 25) from colCert_100_12_2.bind2]
  exact alnAll_100_12_2 j hj hq

theorem leaf_100_12_3 (hp : 3 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 100 []).length)
    (hq : (normIsRep.getD 100 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 3 hp)
        (rowE2 (⟨100, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp))
        (rowE1 (⟨100, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨100, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨100, by decide⟩ (listedAt ⟨100, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp)) T100_12
      hfix100_12 hinj100_12 hcardT100_12
      (fun i => conj_mem_of_fixedPoints _ _ (T100_12 i) (hfix100_12 i) _)
      ⟨100, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨100, by decide⟩ (Q2.listedAt ⟨100, by decide⟩
        (alnCheck_rep ⟨100, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 3 hp) Q2.T100_12_2 Q2.hfix100_12_2 Q2.hinj100_12_2
      Q2.hcardT100_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T100_12_2 i) (Q2.hfix100_12_2 i) _)
      ?_).symm
  rw [show colData1 (⟨100, by decide⟩ : Fin 148)
        ((colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp) : ↥(reps ⟨12, by decide⟩)) : Coordinate 1)
        T100_12 = colFn colCert_100_12_3.D (m := 25) from colCert_100_12_3.bind1,
    show colData2 (⟨100, by decide⟩ : Fin 148)
        ((colE2 ⟨12, by decide⟩ 3 hp : ↥(Q2.reps ⟨12, by decide⟩)) : Coordinate 2)
        Q2.T100_12_2 = colFn colCert_100_12_3.D (m := 25) from colCert_100_12_3.bind2]
  exact alnAll_100_12_3 j hj hq

theorem leaf_100_12_4 (hp : 4 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 100 []).length)
    (hq : (normIsRep.getD 100 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 4 hp)
        (rowE2 (⟨100, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp))
        (rowE1 (⟨100, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨100, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨100, by decide⟩ (listedAt ⟨100, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp)) T100_12
      hfix100_12 hinj100_12 hcardT100_12
      (fun i => conj_mem_of_fixedPoints _ _ (T100_12 i) (hfix100_12 i) _)
      ⟨100, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨100, by decide⟩ (Q2.listedAt ⟨100, by decide⟩
        (alnCheck_rep ⟨100, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 4 hp) Q2.T100_12_2 Q2.hfix100_12_2 Q2.hinj100_12_2
      Q2.hcardT100_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T100_12_2 i) (Q2.hfix100_12_2 i) _)
      ?_).symm
  rw [show colData1 (⟨100, by decide⟩ : Fin 148)
        ((colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp) : ↥(reps ⟨12, by decide⟩)) : Coordinate 1)
        T100_12 = colFn colCert_100_12_4.D (m := 25) from colCert_100_12_4.bind1,
    show colData2 (⟨100, by decide⟩ : Fin 148)
        ((colE2 ⟨12, by decide⟩ 4 hp : ↥(Q2.reps ⟨12, by decide⟩)) : Coordinate 2)
        Q2.T100_12_2 = colFn colCert_100_12_4.D (m := 25) from colCert_100_12_4.bind2]
  exact alnAll_100_12_4 j hj hq

theorem leaf_100_38_0 (hp : 0 < (Q2.transData.getD 38 []).length)
    (j : Nat) (hj : j < (repChars.getD 100 []).length)
    (hq : (normIsRep.getD 100 []).getD j false = true) :
    species (Q2.reps (⟨38, by decide⟩ : Fin 148)) (colE2 ⟨38, by decide⟩ 0 hp)
        (rowE2 (⟨100, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨38, by decide⟩ : Fin 148))
        (colE1 ⟨38, by decide⟩ 0 (transLenTr ⟨38, by decide⟩ 0 hp))
        (rowE1 (⟨100, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨100, by decide⟩ : Fin 148) ⟨38, by decide⟩ _
      (validAt ⟨100, by decide⟩ (listedAt ⟨100, by decide⟩ hj))
      (colE1 ⟨38, by decide⟩ 0 (transLenTr ⟨38, by decide⟩ 0 hp)) T100_38
      hfix100_38 hinj100_38 hcardT100_38
      (fun i => conj_mem_of_fixedPoints _ _ (T100_38 i) (hfix100_38 i) _)
      ⟨100, by decide⟩ ⟨38, by decide⟩ _
      (Q2.validAt ⟨100, by decide⟩ (Q2.listedAt ⟨100, by decide⟩
        (alnCheck_rep ⟨100, by decide⟩ hj hq).1))
      (colE2 ⟨38, by decide⟩ 0 hp) Q2.T100_38_2 Q2.hfix100_38_2 Q2.hinj100_38_2
      Q2.hcardT100_38_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T100_38_2 i) (Q2.hfix100_38_2 i) _)
      ?_).symm
  rw [show colData1 (⟨100, by decide⟩ : Fin 148)
        ((colE1 ⟨38, by decide⟩ 0 (transLenTr ⟨38, by decide⟩ 0 hp) : ↥(reps ⟨38, by decide⟩)) : Coordinate 1)
        T100_38 = colFn colCert_100_38_0.D (m := 25) from colCert_100_38_0.bind1,
    show colData2 (⟨100, by decide⟩ : Fin 148)
        ((colE2 ⟨38, by decide⟩ 0 hp : ↥(Q2.reps ⟨38, by decide⟩)) : Coordinate 2)
        Q2.T100_38_2 = colFn colCert_100_38_0.D (m := 25) from colCert_100_38_0.bind2]
  exact alnAll_100_38_0 j hj hq

theorem leaf_100_38_1 (hp : 1 < (Q2.transData.getD 38 []).length)
    (j : Nat) (hj : j < (repChars.getD 100 []).length)
    (hq : (normIsRep.getD 100 []).getD j false = true) :
    species (Q2.reps (⟨38, by decide⟩ : Fin 148)) (colE2 ⟨38, by decide⟩ 1 hp)
        (rowE2 (⟨100, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨38, by decide⟩ : Fin 148))
        (colE1 ⟨38, by decide⟩ 1 (transLenTr ⟨38, by decide⟩ 1 hp))
        (rowE1 (⟨100, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨100, by decide⟩ : Fin 148) ⟨38, by decide⟩ _
      (validAt ⟨100, by decide⟩ (listedAt ⟨100, by decide⟩ hj))
      (colE1 ⟨38, by decide⟩ 1 (transLenTr ⟨38, by decide⟩ 1 hp)) T100_38
      hfix100_38 hinj100_38 hcardT100_38
      (fun i => conj_mem_of_fixedPoints _ _ (T100_38 i) (hfix100_38 i) _)
      ⟨100, by decide⟩ ⟨38, by decide⟩ _
      (Q2.validAt ⟨100, by decide⟩ (Q2.listedAt ⟨100, by decide⟩
        (alnCheck_rep ⟨100, by decide⟩ hj hq).1))
      (colE2 ⟨38, by decide⟩ 1 hp) Q2.T100_38_2 Q2.hfix100_38_2 Q2.hinj100_38_2
      Q2.hcardT100_38_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T100_38_2 i) (Q2.hfix100_38_2 i) _)
      ?_).symm
  rw [show colData1 (⟨100, by decide⟩ : Fin 148)
        ((colE1 ⟨38, by decide⟩ 1 (transLenTr ⟨38, by decide⟩ 1 hp) : ↥(reps ⟨38, by decide⟩)) : Coordinate 1)
        T100_38 = colFn colCert_100_38_1.D (m := 25) from colCert_100_38_1.bind1,
    show colData2 (⟨100, by decide⟩ : Fin 148)
        ((colE2 ⟨38, by decide⟩ 1 hp : ↥(Q2.reps ⟨38, by decide⟩)) : Coordinate 2)
        Q2.T100_38_2 = colFn colCert_100_38_1.D (m := 25) from colCert_100_38_1.bind2]
  exact alnAll_100_38_1 j hj hq

theorem leaf_100_38_2 (hp : 2 < (Q2.transData.getD 38 []).length)
    (j : Nat) (hj : j < (repChars.getD 100 []).length)
    (hq : (normIsRep.getD 100 []).getD j false = true) :
    species (Q2.reps (⟨38, by decide⟩ : Fin 148)) (colE2 ⟨38, by decide⟩ 2 hp)
        (rowE2 (⟨100, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨38, by decide⟩ : Fin 148))
        (colE1 ⟨38, by decide⟩ 2 (transLenTr ⟨38, by decide⟩ 2 hp))
        (rowE1 (⟨100, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨100, by decide⟩ : Fin 148) ⟨38, by decide⟩ _
      (validAt ⟨100, by decide⟩ (listedAt ⟨100, by decide⟩ hj))
      (colE1 ⟨38, by decide⟩ 2 (transLenTr ⟨38, by decide⟩ 2 hp)) T100_38
      hfix100_38 hinj100_38 hcardT100_38
      (fun i => conj_mem_of_fixedPoints _ _ (T100_38 i) (hfix100_38 i) _)
      ⟨100, by decide⟩ ⟨38, by decide⟩ _
      (Q2.validAt ⟨100, by decide⟩ (Q2.listedAt ⟨100, by decide⟩
        (alnCheck_rep ⟨100, by decide⟩ hj hq).1))
      (colE2 ⟨38, by decide⟩ 2 hp) Q2.T100_38_2 Q2.hfix100_38_2 Q2.hinj100_38_2
      Q2.hcardT100_38_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T100_38_2 i) (Q2.hfix100_38_2 i) _)
      ?_).symm
  rw [show colData1 (⟨100, by decide⟩ : Fin 148)
        ((colE1 ⟨38, by decide⟩ 2 (transLenTr ⟨38, by decide⟩ 2 hp) : ↥(reps ⟨38, by decide⟩)) : Coordinate 1)
        T100_38 = colFn colCert_100_38_2.D (m := 25) from colCert_100_38_2.bind1,
    show colData2 (⟨100, by decide⟩ : Fin 148)
        ((colE2 ⟨38, by decide⟩ 2 hp : ↥(Q2.reps ⟨38, by decide⟩)) : Coordinate 2)
        Q2.T100_38_2 = colFn colCert_100_38_2.D (m := 25) from colCert_100_38_2.bind2]
  exact alnAll_100_38_2 j hj hq

theorem leaf_100_38_3 (hp : 3 < (Q2.transData.getD 38 []).length)
    (j : Nat) (hj : j < (repChars.getD 100 []).length)
    (hq : (normIsRep.getD 100 []).getD j false = true) :
    species (Q2.reps (⟨38, by decide⟩ : Fin 148)) (colE2 ⟨38, by decide⟩ 3 hp)
        (rowE2 (⟨100, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨38, by decide⟩ : Fin 148))
        (colE1 ⟨38, by decide⟩ 3 (transLenTr ⟨38, by decide⟩ 3 hp))
        (rowE1 (⟨100, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨100, by decide⟩ : Fin 148) ⟨38, by decide⟩ _
      (validAt ⟨100, by decide⟩ (listedAt ⟨100, by decide⟩ hj))
      (colE1 ⟨38, by decide⟩ 3 (transLenTr ⟨38, by decide⟩ 3 hp)) T100_38
      hfix100_38 hinj100_38 hcardT100_38
      (fun i => conj_mem_of_fixedPoints _ _ (T100_38 i) (hfix100_38 i) _)
      ⟨100, by decide⟩ ⟨38, by decide⟩ _
      (Q2.validAt ⟨100, by decide⟩ (Q2.listedAt ⟨100, by decide⟩
        (alnCheck_rep ⟨100, by decide⟩ hj hq).1))
      (colE2 ⟨38, by decide⟩ 3 hp) Q2.T100_38_2 Q2.hfix100_38_2 Q2.hinj100_38_2
      Q2.hcardT100_38_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T100_38_2 i) (Q2.hfix100_38_2 i) _)
      ?_).symm
  rw [show colData1 (⟨100, by decide⟩ : Fin 148)
        ((colE1 ⟨38, by decide⟩ 3 (transLenTr ⟨38, by decide⟩ 3 hp) : ↥(reps ⟨38, by decide⟩)) : Coordinate 1)
        T100_38 = colFn colCert_100_38_3.D (m := 25) from colCert_100_38_3.bind1,
    show colData2 (⟨100, by decide⟩ : Fin 148)
        ((colE2 ⟨38, by decide⟩ 3 hp : ↥(Q2.reps ⟨38, by decide⟩)) : Coordinate 2)
        Q2.T100_38_2 = colFn colCert_100_38_3.D (m := 25) from colCert_100_38_3.bind2]
  exact alnAll_100_38_3 j hj hq

theorem leaf_100_38_4 (hp : 4 < (Q2.transData.getD 38 []).length)
    (j : Nat) (hj : j < (repChars.getD 100 []).length)
    (hq : (normIsRep.getD 100 []).getD j false = true) :
    species (Q2.reps (⟨38, by decide⟩ : Fin 148)) (colE2 ⟨38, by decide⟩ 4 hp)
        (rowE2 (⟨100, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨38, by decide⟩ : Fin 148))
        (colE1 ⟨38, by decide⟩ 4 (transLenTr ⟨38, by decide⟩ 4 hp))
        (rowE1 (⟨100, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨100, by decide⟩ : Fin 148) ⟨38, by decide⟩ _
      (validAt ⟨100, by decide⟩ (listedAt ⟨100, by decide⟩ hj))
      (colE1 ⟨38, by decide⟩ 4 (transLenTr ⟨38, by decide⟩ 4 hp)) T100_38
      hfix100_38 hinj100_38 hcardT100_38
      (fun i => conj_mem_of_fixedPoints _ _ (T100_38 i) (hfix100_38 i) _)
      ⟨100, by decide⟩ ⟨38, by decide⟩ _
      (Q2.validAt ⟨100, by decide⟩ (Q2.listedAt ⟨100, by decide⟩
        (alnCheck_rep ⟨100, by decide⟩ hj hq).1))
      (colE2 ⟨38, by decide⟩ 4 hp) Q2.T100_38_2 Q2.hfix100_38_2 Q2.hinj100_38_2
      Q2.hcardT100_38_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T100_38_2 i) (Q2.hfix100_38_2 i) _)
      ?_).symm
  rw [show colData1 (⟨100, by decide⟩ : Fin 148)
        ((colE1 ⟨38, by decide⟩ 4 (transLenTr ⟨38, by decide⟩ 4 hp) : ↥(reps ⟨38, by decide⟩)) : Coordinate 1)
        T100_38 = colFn colCert_100_38_4.D (m := 25) from colCert_100_38_4.bind1,
    show colData2 (⟨100, by decide⟩ : Fin 148)
        ((colE2 ⟨38, by decide⟩ 4 hp : ↥(Q2.reps ⟨38, by decide⟩)) : Coordinate 2)
        Q2.T100_38_2 = colFn colCert_100_38_4.D (m := 25) from colCert_100_38_4.bind2]
  exact alnAll_100_38_4 j hj hq

theorem leaf_100_38_5 (hp : 5 < (Q2.transData.getD 38 []).length)
    (j : Nat) (hj : j < (repChars.getD 100 []).length)
    (hq : (normIsRep.getD 100 []).getD j false = true) :
    species (Q2.reps (⟨38, by decide⟩ : Fin 148)) (colE2 ⟨38, by decide⟩ 5 hp)
        (rowE2 (⟨100, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨38, by decide⟩ : Fin 148))
        (colE1 ⟨38, by decide⟩ 5 (transLenTr ⟨38, by decide⟩ 5 hp))
        (rowE1 (⟨100, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨100, by decide⟩ : Fin 148) ⟨38, by decide⟩ _
      (validAt ⟨100, by decide⟩ (listedAt ⟨100, by decide⟩ hj))
      (colE1 ⟨38, by decide⟩ 5 (transLenTr ⟨38, by decide⟩ 5 hp)) T100_38
      hfix100_38 hinj100_38 hcardT100_38
      (fun i => conj_mem_of_fixedPoints _ _ (T100_38 i) (hfix100_38 i) _)
      ⟨100, by decide⟩ ⟨38, by decide⟩ _
      (Q2.validAt ⟨100, by decide⟩ (Q2.listedAt ⟨100, by decide⟩
        (alnCheck_rep ⟨100, by decide⟩ hj hq).1))
      (colE2 ⟨38, by decide⟩ 5 hp) Q2.T100_38_2 Q2.hfix100_38_2 Q2.hinj100_38_2
      Q2.hcardT100_38_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T100_38_2 i) (Q2.hfix100_38_2 i) _)
      ?_).symm
  rw [show colData1 (⟨100, by decide⟩ : Fin 148)
        ((colE1 ⟨38, by decide⟩ 5 (transLenTr ⟨38, by decide⟩ 5 hp) : ↥(reps ⟨38, by decide⟩)) : Coordinate 1)
        T100_38 = colFn colCertDiv_100_38_5.D1 (m := 25) from colCertDiv_100_38_5.bind1,
    show colData2 (⟨100, by decide⟩ : Fin 148)
        ((colE2 ⟨38, by decide⟩ 5 hp : ↥(Q2.reps ⟨38, by decide⟩)) : Coordinate 2)
        Q2.T100_38_2 = colFn colCertDiv_100_38_5.D2 (m := 25) from colCertDiv_100_38_5.bind2]
  exact alnAll_100_38_5 j hj hq

theorem leaf_100_38_10 (hp : 10 < (Q2.transData.getD 38 []).length)
    (j : Nat) (hj : j < (repChars.getD 100 []).length)
    (hq : (normIsRep.getD 100 []).getD j false = true) :
    species (Q2.reps (⟨38, by decide⟩ : Fin 148)) (colE2 ⟨38, by decide⟩ 10 hp)
        (rowE2 (⟨100, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨38, by decide⟩ : Fin 148))
        (colE1 ⟨38, by decide⟩ 10 (transLenTr ⟨38, by decide⟩ 10 hp))
        (rowE1 (⟨100, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨100, by decide⟩ : Fin 148) ⟨38, by decide⟩ _
      (validAt ⟨100, by decide⟩ (listedAt ⟨100, by decide⟩ hj))
      (colE1 ⟨38, by decide⟩ 10 (transLenTr ⟨38, by decide⟩ 10 hp)) T100_38
      hfix100_38 hinj100_38 hcardT100_38
      (fun i => conj_mem_of_fixedPoints _ _ (T100_38 i) (hfix100_38 i) _)
      ⟨100, by decide⟩ ⟨38, by decide⟩ _
      (Q2.validAt ⟨100, by decide⟩ (Q2.listedAt ⟨100, by decide⟩
        (alnCheck_rep ⟨100, by decide⟩ hj hq).1))
      (colE2 ⟨38, by decide⟩ 10 hp) Q2.T100_38_2 Q2.hfix100_38_2 Q2.hinj100_38_2
      Q2.hcardT100_38_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T100_38_2 i) (Q2.hfix100_38_2 i) _)
      ?_).symm
  rw [show colData1 (⟨100, by decide⟩ : Fin 148)
        ((colE1 ⟨38, by decide⟩ 10 (transLenTr ⟨38, by decide⟩ 10 hp) : ↥(reps ⟨38, by decide⟩)) : Coordinate 1)
        T100_38 = colFn colCertDiv_100_38_10.D1 (m := 25) from colCertDiv_100_38_10.bind1,
    show colData2 (⟨100, by decide⟩ : Fin 148)
        ((colE2 ⟨38, by decide⟩ 10 hp : ↥(Q2.reps ⟨38, by decide⟩)) : Coordinate 2)
        Q2.T100_38_2 = colFn colCertDiv_100_38_10.D2 (m := 25) from colCertDiv_100_38_10.bind2]
  exact alnAll_100_38_10 j hj hq

theorem leaf_100_38_15 (hp : 15 < (Q2.transData.getD 38 []).length)
    (j : Nat) (hj : j < (repChars.getD 100 []).length)
    (hq : (normIsRep.getD 100 []).getD j false = true) :
    species (Q2.reps (⟨38, by decide⟩ : Fin 148)) (colE2 ⟨38, by decide⟩ 15 hp)
        (rowE2 (⟨100, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨38, by decide⟩ : Fin 148))
        (colE1 ⟨38, by decide⟩ 15 (transLenTr ⟨38, by decide⟩ 15 hp))
        (rowE1 (⟨100, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨100, by decide⟩ : Fin 148) ⟨38, by decide⟩ _
      (validAt ⟨100, by decide⟩ (listedAt ⟨100, by decide⟩ hj))
      (colE1 ⟨38, by decide⟩ 15 (transLenTr ⟨38, by decide⟩ 15 hp)) T100_38
      hfix100_38 hinj100_38 hcardT100_38
      (fun i => conj_mem_of_fixedPoints _ _ (T100_38 i) (hfix100_38 i) _)
      ⟨100, by decide⟩ ⟨38, by decide⟩ _
      (Q2.validAt ⟨100, by decide⟩ (Q2.listedAt ⟨100, by decide⟩
        (alnCheck_rep ⟨100, by decide⟩ hj hq).1))
      (colE2 ⟨38, by decide⟩ 15 hp) Q2.T100_38_2 Q2.hfix100_38_2 Q2.hinj100_38_2
      Q2.hcardT100_38_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T100_38_2 i) (Q2.hfix100_38_2 i) _)
      ?_).symm
  rw [show colData1 (⟨100, by decide⟩ : Fin 148)
        ((colE1 ⟨38, by decide⟩ 15 (transLenTr ⟨38, by decide⟩ 15 hp) : ↥(reps ⟨38, by decide⟩)) : Coordinate 1)
        T100_38 = colFn colCertDiv_100_38_15.D1 (m := 25) from colCertDiv_100_38_15.bind1,
    show colData2 (⟨100, by decide⟩ : Fin 148)
        ((colE2 ⟨38, by decide⟩ 15 hp : ↥(Q2.reps ⟨38, by decide⟩)) : Coordinate 2)
        Q2.T100_38_2 = colFn colCertDiv_100_38_15.D2 (m := 25) from colCertDiv_100_38_15.bind2]
  exact alnAll_100_38_15 j hj hq

theorem leaf_100_38_20 (hp : 20 < (Q2.transData.getD 38 []).length)
    (j : Nat) (hj : j < (repChars.getD 100 []).length)
    (hq : (normIsRep.getD 100 []).getD j false = true) :
    species (Q2.reps (⟨38, by decide⟩ : Fin 148)) (colE2 ⟨38, by decide⟩ 20 hp)
        (rowE2 (⟨100, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨38, by decide⟩ : Fin 148))
        (colE1 ⟨38, by decide⟩ 20 (transLenTr ⟨38, by decide⟩ 20 hp))
        (rowE1 (⟨100, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨100, by decide⟩ : Fin 148) ⟨38, by decide⟩ _
      (validAt ⟨100, by decide⟩ (listedAt ⟨100, by decide⟩ hj))
      (colE1 ⟨38, by decide⟩ 20 (transLenTr ⟨38, by decide⟩ 20 hp)) T100_38
      hfix100_38 hinj100_38 hcardT100_38
      (fun i => conj_mem_of_fixedPoints _ _ (T100_38 i) (hfix100_38 i) _)
      ⟨100, by decide⟩ ⟨38, by decide⟩ _
      (Q2.validAt ⟨100, by decide⟩ (Q2.listedAt ⟨100, by decide⟩
        (alnCheck_rep ⟨100, by decide⟩ hj hq).1))
      (colE2 ⟨38, by decide⟩ 20 hp) Q2.T100_38_2 Q2.hfix100_38_2 Q2.hinj100_38_2
      Q2.hcardT100_38_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T100_38_2 i) (Q2.hfix100_38_2 i) _)
      ?_).symm
  rw [show colData1 (⟨100, by decide⟩ : Fin 148)
        ((colE1 ⟨38, by decide⟩ 20 (transLenTr ⟨38, by decide⟩ 20 hp) : ↥(reps ⟨38, by decide⟩)) : Coordinate 1)
        T100_38 = colFn colCertDiv_100_38_20.D1 (m := 25) from colCertDiv_100_38_20.bind1,
    show colData2 (⟨100, by decide⟩ : Fin 148)
        ((colE2 ⟨38, by decide⟩ 20 hp : ↥(Q2.reps ⟨38, by decide⟩)) : Coordinate 2)
        Q2.T100_38_2 = colFn colCertDiv_100_38_20.D2 (m := 25) from colCertDiv_100_38_20.bind2]
  exact alnAll_100_38_20 j hj hq

theorem leaf_100_53_0 (hp : 0 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 100 []).length)
    (hq : (normIsRep.getD 100 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 0 hp)
        (rowE2 (⟨100, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 0 (transLenTr ⟨53, by decide⟩ 0 hp))
        (rowE1 (⟨100, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨100, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨100, by decide⟩ (listedAt ⟨100, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 0 (transLenTr ⟨53, by decide⟩ 0 hp)) T100_53
      hfix100_53 hinj100_53 hcardT100_53
      (fun i => conj_mem_of_fixedPoints _ _ (T100_53 i) (hfix100_53 i) _)
      ⟨100, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨100, by decide⟩ (Q2.listedAt ⟨100, by decide⟩
        (alnCheck_rep ⟨100, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 0 hp) Q2.T100_53_2 Q2.hfix100_53_2 Q2.hinj100_53_2
      Q2.hcardT100_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T100_53_2 i) (Q2.hfix100_53_2 i) _)
      ?_).symm
  rw [show colData1 (⟨100, by decide⟩ : Fin 148)
        ((colE1 ⟨53, by decide⟩ 0 (transLenTr ⟨53, by decide⟩ 0 hp) : ↥(reps ⟨53, by decide⟩)) : Coordinate 1)
        T100_53 = colFn colCert_100_53_0.D (m := 25) from colCert_100_53_0.bind1,
    show colData2 (⟨100, by decide⟩ : Fin 148)
        ((colE2 ⟨53, by decide⟩ 0 hp : ↥(Q2.reps ⟨53, by decide⟩)) : Coordinate 2)
        Q2.T100_53_2 = colFn colCert_100_53_0.D (m := 25) from colCert_100_53_0.bind2]
  exact alnAll_100_53_0 j hj hq

theorem leaf_100_53_1 (hp : 1 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 100 []).length)
    (hq : (normIsRep.getD 100 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 1 hp)
        (rowE2 (⟨100, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 1 (transLenTr ⟨53, by decide⟩ 1 hp))
        (rowE1 (⟨100, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨100, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨100, by decide⟩ (listedAt ⟨100, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 1 (transLenTr ⟨53, by decide⟩ 1 hp)) T100_53
      hfix100_53 hinj100_53 hcardT100_53
      (fun i => conj_mem_of_fixedPoints _ _ (T100_53 i) (hfix100_53 i) _)
      ⟨100, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨100, by decide⟩ (Q2.listedAt ⟨100, by decide⟩
        (alnCheck_rep ⟨100, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 1 hp) Q2.T100_53_2 Q2.hfix100_53_2 Q2.hinj100_53_2
      Q2.hcardT100_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T100_53_2 i) (Q2.hfix100_53_2 i) _)
      ?_).symm
  rw [show colData1 (⟨100, by decide⟩ : Fin 148)
        ((colE1 ⟨53, by decide⟩ 1 (transLenTr ⟨53, by decide⟩ 1 hp) : ↥(reps ⟨53, by decide⟩)) : Coordinate 1)
        T100_53 = colFn colCert_100_53_1.D (m := 25) from colCert_100_53_1.bind1,
    show colData2 (⟨100, by decide⟩ : Fin 148)
        ((colE2 ⟨53, by decide⟩ 1 hp : ↥(Q2.reps ⟨53, by decide⟩)) : Coordinate 2)
        Q2.T100_53_2 = colFn colCert_100_53_1.D (m := 25) from colCert_100_53_1.bind2]
  exact alnAll_100_53_1 j hj hq

theorem leaf_100_53_2 (hp : 2 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 100 []).length)
    (hq : (normIsRep.getD 100 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 2 hp)
        (rowE2 (⟨100, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 2 (transLenTr ⟨53, by decide⟩ 2 hp))
        (rowE1 (⟨100, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨100, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨100, by decide⟩ (listedAt ⟨100, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 2 (transLenTr ⟨53, by decide⟩ 2 hp)) T100_53
      hfix100_53 hinj100_53 hcardT100_53
      (fun i => conj_mem_of_fixedPoints _ _ (T100_53 i) (hfix100_53 i) _)
      ⟨100, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨100, by decide⟩ (Q2.listedAt ⟨100, by decide⟩
        (alnCheck_rep ⟨100, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 2 hp) Q2.T100_53_2 Q2.hfix100_53_2 Q2.hinj100_53_2
      Q2.hcardT100_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T100_53_2 i) (Q2.hfix100_53_2 i) _)
      ?_).symm
  rw [show colData1 (⟨100, by decide⟩ : Fin 148)
        ((colE1 ⟨53, by decide⟩ 2 (transLenTr ⟨53, by decide⟩ 2 hp) : ↥(reps ⟨53, by decide⟩)) : Coordinate 1)
        T100_53 = colFn colCert_100_53_2.D (m := 25) from colCert_100_53_2.bind1,
    show colData2 (⟨100, by decide⟩ : Fin 148)
        ((colE2 ⟨53, by decide⟩ 2 hp : ↥(Q2.reps ⟨53, by decide⟩)) : Coordinate 2)
        Q2.T100_53_2 = colFn colCert_100_53_2.D (m := 25) from colCert_100_53_2.bind2]
  exact alnAll_100_53_2 j hj hq

theorem leaf_100_53_3 (hp : 3 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 100 []).length)
    (hq : (normIsRep.getD 100 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 3 hp)
        (rowE2 (⟨100, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 3 (transLenTr ⟨53, by decide⟩ 3 hp))
        (rowE1 (⟨100, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨100, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨100, by decide⟩ (listedAt ⟨100, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 3 (transLenTr ⟨53, by decide⟩ 3 hp)) T100_53
      hfix100_53 hinj100_53 hcardT100_53
      (fun i => conj_mem_of_fixedPoints _ _ (T100_53 i) (hfix100_53 i) _)
      ⟨100, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨100, by decide⟩ (Q2.listedAt ⟨100, by decide⟩
        (alnCheck_rep ⟨100, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 3 hp) Q2.T100_53_2 Q2.hfix100_53_2 Q2.hinj100_53_2
      Q2.hcardT100_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T100_53_2 i) (Q2.hfix100_53_2 i) _)
      ?_).symm
  rw [show colData1 (⟨100, by decide⟩ : Fin 148)
        ((colE1 ⟨53, by decide⟩ 3 (transLenTr ⟨53, by decide⟩ 3 hp) : ↥(reps ⟨53, by decide⟩)) : Coordinate 1)
        T100_53 = colFn colCert_100_53_3.D (m := 25) from colCert_100_53_3.bind1,
    show colData2 (⟨100, by decide⟩ : Fin 148)
        ((colE2 ⟨53, by decide⟩ 3 hp : ↥(Q2.reps ⟨53, by decide⟩)) : Coordinate 2)
        Q2.T100_53_2 = colFn colCert_100_53_3.D (m := 25) from colCert_100_53_3.bind2]
  exact alnAll_100_53_3 j hj hq

theorem leaf_100_53_4 (hp : 4 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 100 []).length)
    (hq : (normIsRep.getD 100 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 4 hp)
        (rowE2 (⟨100, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 4 (transLenTr ⟨53, by decide⟩ 4 hp))
        (rowE1 (⟨100, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨100, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨100, by decide⟩ (listedAt ⟨100, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 4 (transLenTr ⟨53, by decide⟩ 4 hp)) T100_53
      hfix100_53 hinj100_53 hcardT100_53
      (fun i => conj_mem_of_fixedPoints _ _ (T100_53 i) (hfix100_53 i) _)
      ⟨100, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨100, by decide⟩ (Q2.listedAt ⟨100, by decide⟩
        (alnCheck_rep ⟨100, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 4 hp) Q2.T100_53_2 Q2.hfix100_53_2 Q2.hinj100_53_2
      Q2.hcardT100_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T100_53_2 i) (Q2.hfix100_53_2 i) _)
      ?_).symm
  rw [show colData1 (⟨100, by decide⟩ : Fin 148)
        ((colE1 ⟨53, by decide⟩ 4 (transLenTr ⟨53, by decide⟩ 4 hp) : ↥(reps ⟨53, by decide⟩)) : Coordinate 1)
        T100_53 = colFn colCert_100_53_4.D (m := 25) from colCert_100_53_4.bind1,
    show colData2 (⟨100, by decide⟩ : Fin 148)
        ((colE2 ⟨53, by decide⟩ 4 hp : ↥(Q2.reps ⟨53, by decide⟩)) : Coordinate 2)
        Q2.T100_53_2 = colFn colCert_100_53_4.D (m := 25) from colCert_100_53_4.bind2]
  exact alnAll_100_53_4 j hj hq

theorem leaf_100_53_5 (hp : 5 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 100 []).length)
    (hq : (normIsRep.getD 100 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 5 hp)
        (rowE2 (⟨100, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 5 (transLenTr ⟨53, by decide⟩ 5 hp))
        (rowE1 (⟨100, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨100, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨100, by decide⟩ (listedAt ⟨100, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 5 (transLenTr ⟨53, by decide⟩ 5 hp)) T100_53
      hfix100_53 hinj100_53 hcardT100_53
      (fun i => conj_mem_of_fixedPoints _ _ (T100_53 i) (hfix100_53 i) _)
      ⟨100, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨100, by decide⟩ (Q2.listedAt ⟨100, by decide⟩
        (alnCheck_rep ⟨100, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 5 hp) Q2.T100_53_2 Q2.hfix100_53_2 Q2.hinj100_53_2
      Q2.hcardT100_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T100_53_2 i) (Q2.hfix100_53_2 i) _)
      ?_).symm
  rw [show colData1 (⟨100, by decide⟩ : Fin 148)
        ((colE1 ⟨53, by decide⟩ 5 (transLenTr ⟨53, by decide⟩ 5 hp) : ↥(reps ⟨53, by decide⟩)) : Coordinate 1)
        T100_53 = colFn colCert_100_53_5.D (m := 25) from colCert_100_53_5.bind1,
    show colData2 (⟨100, by decide⟩ : Fin 148)
        ((colE2 ⟨53, by decide⟩ 5 hp : ↥(Q2.reps ⟨53, by decide⟩)) : Coordinate 2)
        Q2.T100_53_2 = colFn colCert_100_53_5.D (m := 25) from colCert_100_53_5.bind2]
  exact alnAll_100_53_5 j hj hq

theorem leaf_100_53_10 (hp : 10 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 100 []).length)
    (hq : (normIsRep.getD 100 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 10 hp)
        (rowE2 (⟨100, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 10 (transLenTr ⟨53, by decide⟩ 10 hp))
        (rowE1 (⟨100, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨100, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨100, by decide⟩ (listedAt ⟨100, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 10 (transLenTr ⟨53, by decide⟩ 10 hp)) T100_53
      hfix100_53 hinj100_53 hcardT100_53
      (fun i => conj_mem_of_fixedPoints _ _ (T100_53 i) (hfix100_53 i) _)
      ⟨100, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨100, by decide⟩ (Q2.listedAt ⟨100, by decide⟩
        (alnCheck_rep ⟨100, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 10 hp) Q2.T100_53_2 Q2.hfix100_53_2 Q2.hinj100_53_2
      Q2.hcardT100_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T100_53_2 i) (Q2.hfix100_53_2 i) _)
      ?_).symm
  rw [show colData1 (⟨100, by decide⟩ : Fin 148)
        ((colE1 ⟨53, by decide⟩ 10 (transLenTr ⟨53, by decide⟩ 10 hp) : ↥(reps ⟨53, by decide⟩)) : Coordinate 1)
        T100_53 = colFn colCert_100_53_10.D (m := 25) from colCert_100_53_10.bind1,
    show colData2 (⟨100, by decide⟩ : Fin 148)
        ((colE2 ⟨53, by decide⟩ 10 hp : ↥(Q2.reps ⟨53, by decide⟩)) : Coordinate 2)
        Q2.T100_53_2 = colFn colCert_100_53_10.D (m := 25) from colCert_100_53_10.bind2]
  exact alnAll_100_53_10 j hj hq

theorem leaf_100_53_15 (hp : 15 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 100 []).length)
    (hq : (normIsRep.getD 100 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 15 hp)
        (rowE2 (⟨100, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 15 (transLenTr ⟨53, by decide⟩ 15 hp))
        (rowE1 (⟨100, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨100, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨100, by decide⟩ (listedAt ⟨100, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 15 (transLenTr ⟨53, by decide⟩ 15 hp)) T100_53
      hfix100_53 hinj100_53 hcardT100_53
      (fun i => conj_mem_of_fixedPoints _ _ (T100_53 i) (hfix100_53 i) _)
      ⟨100, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨100, by decide⟩ (Q2.listedAt ⟨100, by decide⟩
        (alnCheck_rep ⟨100, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 15 hp) Q2.T100_53_2 Q2.hfix100_53_2 Q2.hinj100_53_2
      Q2.hcardT100_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T100_53_2 i) (Q2.hfix100_53_2 i) _)
      ?_).symm
  rw [show colData1 (⟨100, by decide⟩ : Fin 148)
        ((colE1 ⟨53, by decide⟩ 15 (transLenTr ⟨53, by decide⟩ 15 hp) : ↥(reps ⟨53, by decide⟩)) : Coordinate 1)
        T100_53 = colFn colCert_100_53_15.D (m := 25) from colCert_100_53_15.bind1,
    show colData2 (⟨100, by decide⟩ : Fin 148)
        ((colE2 ⟨53, by decide⟩ 15 hp : ↥(Q2.reps ⟨53, by decide⟩)) : Coordinate 2)
        Q2.T100_53_2 = colFn colCert_100_53_15.D (m := 25) from colCert_100_53_15.bind2]
  exact alnAll_100_53_15 j hj hq

theorem leaf_100_53_20 (hp : 20 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 100 []).length)
    (hq : (normIsRep.getD 100 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 20 hp)
        (rowE2 (⟨100, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 20 (transLenTr ⟨53, by decide⟩ 20 hp))
        (rowE1 (⟨100, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨100, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨100, by decide⟩ (listedAt ⟨100, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 20 (transLenTr ⟨53, by decide⟩ 20 hp)) T100_53
      hfix100_53 hinj100_53 hcardT100_53
      (fun i => conj_mem_of_fixedPoints _ _ (T100_53 i) (hfix100_53 i) _)
      ⟨100, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨100, by decide⟩ (Q2.listedAt ⟨100, by decide⟩
        (alnCheck_rep ⟨100, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 20 hp) Q2.T100_53_2 Q2.hfix100_53_2 Q2.hinj100_53_2
      Q2.hcardT100_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T100_53_2 i) (Q2.hfix100_53_2 i) _)
      ?_).symm
  rw [show colData1 (⟨100, by decide⟩ : Fin 148)
        ((colE1 ⟨53, by decide⟩ 20 (transLenTr ⟨53, by decide⟩ 20 hp) : ↥(reps ⟨53, by decide⟩)) : Coordinate 1)
        T100_53 = colFn colCert_100_53_20.D (m := 25) from colCert_100_53_20.bind1,
    show colData2 (⟨100, by decide⟩ : Fin 148)
        ((colE2 ⟨53, by decide⟩ 20 hp : ↥(Q2.reps ⟨53, by decide⟩)) : Coordinate 2)
        Q2.T100_53_2 = colFn colCert_100_53_20.D (m := 25) from colCert_100_53_20.bind2]
  exact alnAll_100_53_20 j hj hq

theorem leaf_100_100_0 (hp : 0 < (Q2.transData.getD 100 []).length)
    (j : Nat) (hj : j < (repChars.getD 100 []).length)
    (hq : (normIsRep.getD 100 []).getD j false = true) :
    species (Q2.reps (⟨100, by decide⟩ : Fin 148)) (colE2 ⟨100, by decide⟩ 0 hp)
        (rowE2 (⟨100, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨100, by decide⟩ : Fin 148))
        (colE1 ⟨100, by decide⟩ 0 (transLenTr ⟨100, by decide⟩ 0 hp))
        (rowE1 (⟨100, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨100, by decide⟩ : Fin 148) ⟨100, by decide⟩ _
      (validAt ⟨100, by decide⟩ (listedAt ⟨100, by decide⟩ hj))
      (colE1 ⟨100, by decide⟩ 0 (transLenTr ⟨100, by decide⟩ 0 hp)) T100_100
      hfix100_100 hinj100_100 hcardT100_100
      (fun i => conj_mem_of_fixedPoints _ _ (T100_100 i) (hfix100_100 i) _)
      ⟨100, by decide⟩ ⟨100, by decide⟩ _
      (Q2.validAt ⟨100, by decide⟩ (Q2.listedAt ⟨100, by decide⟩
        (alnCheck_rep ⟨100, by decide⟩ hj hq).1))
      (colE2 ⟨100, by decide⟩ 0 hp) Q2.T100_100_2 Q2.hfix100_100_2 Q2.hinj100_100_2
      Q2.hcardT100_100_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T100_100_2 i) (Q2.hfix100_100_2 i) _)
      ?_).symm
  rw [show colData1 (⟨100, by decide⟩ : Fin 148)
        ((colE1 ⟨100, by decide⟩ 0 (transLenTr ⟨100, by decide⟩ 0 hp) : ↥(reps ⟨100, by decide⟩)) : Coordinate 1)
        T100_100 = colFn colCert_100_100_0.D (m := 25) from colCert_100_100_0.bind1,
    show colData2 (⟨100, by decide⟩ : Fin 148)
        ((colE2 ⟨100, by decide⟩ 0 hp : ↥(Q2.reps ⟨100, by decide⟩)) : Coordinate 2)
        Q2.T100_100_2 = colFn colCert_100_100_0.D (m := 25) from colCert_100_100_0.bind2]
  exact alnAll_100_100_0 j hj hq

theorem leaf_100_100_1 (hp : 1 < (Q2.transData.getD 100 []).length)
    (j : Nat) (hj : j < (repChars.getD 100 []).length)
    (hq : (normIsRep.getD 100 []).getD j false = true) :
    species (Q2.reps (⟨100, by decide⟩ : Fin 148)) (colE2 ⟨100, by decide⟩ 1 hp)
        (rowE2 (⟨100, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨100, by decide⟩ : Fin 148))
        (colE1 ⟨100, by decide⟩ 1 (transLenTr ⟨100, by decide⟩ 1 hp))
        (rowE1 (⟨100, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨100, by decide⟩ : Fin 148) ⟨100, by decide⟩ _
      (validAt ⟨100, by decide⟩ (listedAt ⟨100, by decide⟩ hj))
      (colE1 ⟨100, by decide⟩ 1 (transLenTr ⟨100, by decide⟩ 1 hp)) T100_100
      hfix100_100 hinj100_100 hcardT100_100
      (fun i => conj_mem_of_fixedPoints _ _ (T100_100 i) (hfix100_100 i) _)
      ⟨100, by decide⟩ ⟨100, by decide⟩ _
      (Q2.validAt ⟨100, by decide⟩ (Q2.listedAt ⟨100, by decide⟩
        (alnCheck_rep ⟨100, by decide⟩ hj hq).1))
      (colE2 ⟨100, by decide⟩ 1 hp) Q2.T100_100_2 Q2.hfix100_100_2 Q2.hinj100_100_2
      Q2.hcardT100_100_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T100_100_2 i) (Q2.hfix100_100_2 i) _)
      ?_).symm
  rw [show colData1 (⟨100, by decide⟩ : Fin 148)
        ((colE1 ⟨100, by decide⟩ 1 (transLenTr ⟨100, by decide⟩ 1 hp) : ↥(reps ⟨100, by decide⟩)) : Coordinate 1)
        T100_100 = colFn colCert_100_100_1.D (m := 25) from colCert_100_100_1.bind1,
    show colData2 (⟨100, by decide⟩ : Fin 148)
        ((colE2 ⟨100, by decide⟩ 1 hp : ↥(Q2.reps ⟨100, by decide⟩)) : Coordinate 2)
        Q2.T100_100_2 = colFn colCert_100_100_1.D (m := 25) from colCert_100_100_1.bind2]
  exact alnAll_100_100_1 j hj hq

theorem leaf_100_100_2 (hp : 2 < (Q2.transData.getD 100 []).length)
    (j : Nat) (hj : j < (repChars.getD 100 []).length)
    (hq : (normIsRep.getD 100 []).getD j false = true) :
    species (Q2.reps (⟨100, by decide⟩ : Fin 148)) (colE2 ⟨100, by decide⟩ 2 hp)
        (rowE2 (⟨100, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨100, by decide⟩ : Fin 148))
        (colE1 ⟨100, by decide⟩ 2 (transLenTr ⟨100, by decide⟩ 2 hp))
        (rowE1 (⟨100, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨100, by decide⟩ : Fin 148) ⟨100, by decide⟩ _
      (validAt ⟨100, by decide⟩ (listedAt ⟨100, by decide⟩ hj))
      (colE1 ⟨100, by decide⟩ 2 (transLenTr ⟨100, by decide⟩ 2 hp)) T100_100
      hfix100_100 hinj100_100 hcardT100_100
      (fun i => conj_mem_of_fixedPoints _ _ (T100_100 i) (hfix100_100 i) _)
      ⟨100, by decide⟩ ⟨100, by decide⟩ _
      (Q2.validAt ⟨100, by decide⟩ (Q2.listedAt ⟨100, by decide⟩
        (alnCheck_rep ⟨100, by decide⟩ hj hq).1))
      (colE2 ⟨100, by decide⟩ 2 hp) Q2.T100_100_2 Q2.hfix100_100_2 Q2.hinj100_100_2
      Q2.hcardT100_100_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T100_100_2 i) (Q2.hfix100_100_2 i) _)
      ?_).symm
  rw [show colData1 (⟨100, by decide⟩ : Fin 148)
        ((colE1 ⟨100, by decide⟩ 2 (transLenTr ⟨100, by decide⟩ 2 hp) : ↥(reps ⟨100, by decide⟩)) : Coordinate 1)
        T100_100 = colFn colCert_100_100_2.D (m := 25) from colCert_100_100_2.bind1,
    show colData2 (⟨100, by decide⟩ : Fin 148)
        ((colE2 ⟨100, by decide⟩ 2 hp : ↥(Q2.reps ⟨100, by decide⟩)) : Coordinate 2)
        Q2.T100_100_2 = colFn colCert_100_100_2.D (m := 25) from colCert_100_100_2.bind2]
  exact alnAll_100_100_2 j hj hq

theorem leaf_100_100_3 (hp : 3 < (Q2.transData.getD 100 []).length)
    (j : Nat) (hj : j < (repChars.getD 100 []).length)
    (hq : (normIsRep.getD 100 []).getD j false = true) :
    species (Q2.reps (⟨100, by decide⟩ : Fin 148)) (colE2 ⟨100, by decide⟩ 3 hp)
        (rowE2 (⟨100, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨100, by decide⟩ : Fin 148))
        (colE1 ⟨100, by decide⟩ 3 (transLenTr ⟨100, by decide⟩ 3 hp))
        (rowE1 (⟨100, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨100, by decide⟩ : Fin 148) ⟨100, by decide⟩ _
      (validAt ⟨100, by decide⟩ (listedAt ⟨100, by decide⟩ hj))
      (colE1 ⟨100, by decide⟩ 3 (transLenTr ⟨100, by decide⟩ 3 hp)) T100_100
      hfix100_100 hinj100_100 hcardT100_100
      (fun i => conj_mem_of_fixedPoints _ _ (T100_100 i) (hfix100_100 i) _)
      ⟨100, by decide⟩ ⟨100, by decide⟩ _
      (Q2.validAt ⟨100, by decide⟩ (Q2.listedAt ⟨100, by decide⟩
        (alnCheck_rep ⟨100, by decide⟩ hj hq).1))
      (colE2 ⟨100, by decide⟩ 3 hp) Q2.T100_100_2 Q2.hfix100_100_2 Q2.hinj100_100_2
      Q2.hcardT100_100_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T100_100_2 i) (Q2.hfix100_100_2 i) _)
      ?_).symm
  rw [show colData1 (⟨100, by decide⟩ : Fin 148)
        ((colE1 ⟨100, by decide⟩ 3 (transLenTr ⟨100, by decide⟩ 3 hp) : ↥(reps ⟨100, by decide⟩)) : Coordinate 1)
        T100_100 = colFn colCert_100_100_3.D (m := 25) from colCert_100_100_3.bind1,
    show colData2 (⟨100, by decide⟩ : Fin 148)
        ((colE2 ⟨100, by decide⟩ 3 hp : ↥(Q2.reps ⟨100, by decide⟩)) : Coordinate 2)
        Q2.T100_100_2 = colFn colCert_100_100_3.D (m := 25) from colCert_100_100_3.bind2]
  exact alnAll_100_100_3 j hj hq

theorem leaf_100_100_4 (hp : 4 < (Q2.transData.getD 100 []).length)
    (j : Nat) (hj : j < (repChars.getD 100 []).length)
    (hq : (normIsRep.getD 100 []).getD j false = true) :
    species (Q2.reps (⟨100, by decide⟩ : Fin 148)) (colE2 ⟨100, by decide⟩ 4 hp)
        (rowE2 (⟨100, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨100, by decide⟩ : Fin 148))
        (colE1 ⟨100, by decide⟩ 4 (transLenTr ⟨100, by decide⟩ 4 hp))
        (rowE1 (⟨100, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨100, by decide⟩ : Fin 148) ⟨100, by decide⟩ _
      (validAt ⟨100, by decide⟩ (listedAt ⟨100, by decide⟩ hj))
      (colE1 ⟨100, by decide⟩ 4 (transLenTr ⟨100, by decide⟩ 4 hp)) T100_100
      hfix100_100 hinj100_100 hcardT100_100
      (fun i => conj_mem_of_fixedPoints _ _ (T100_100 i) (hfix100_100 i) _)
      ⟨100, by decide⟩ ⟨100, by decide⟩ _
      (Q2.validAt ⟨100, by decide⟩ (Q2.listedAt ⟨100, by decide⟩
        (alnCheck_rep ⟨100, by decide⟩ hj hq).1))
      (colE2 ⟨100, by decide⟩ 4 hp) Q2.T100_100_2 Q2.hfix100_100_2 Q2.hinj100_100_2
      Q2.hcardT100_100_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T100_100_2 i) (Q2.hfix100_100_2 i) _)
      ?_).symm
  rw [show colData1 (⟨100, by decide⟩ : Fin 148)
        ((colE1 ⟨100, by decide⟩ 4 (transLenTr ⟨100, by decide⟩ 4 hp) : ↥(reps ⟨100, by decide⟩)) : Coordinate 1)
        T100_100 = colFn colCert_100_100_4.D (m := 25) from colCert_100_100_4.bind1,
    show colData2 (⟨100, by decide⟩ : Fin 148)
        ((colE2 ⟨100, by decide⟩ 4 hp : ↥(Q2.reps ⟨100, by decide⟩)) : Coordinate 2)
        Q2.T100_100_2 = colFn colCert_100_100_4.D (m := 25) from colCert_100_100_4.bind2]
  exact alnAll_100_100_4 j hj hq

theorem leaf_100_100_5 (hp : 5 < (Q2.transData.getD 100 []).length)
    (j : Nat) (hj : j < (repChars.getD 100 []).length)
    (hq : (normIsRep.getD 100 []).getD j false = true) :
    species (Q2.reps (⟨100, by decide⟩ : Fin 148)) (colE2 ⟨100, by decide⟩ 5 hp)
        (rowE2 (⟨100, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨100, by decide⟩ : Fin 148))
        (colE1 ⟨100, by decide⟩ 5 (transLenTr ⟨100, by decide⟩ 5 hp))
        (rowE1 (⟨100, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨100, by decide⟩ : Fin 148) ⟨100, by decide⟩ _
      (validAt ⟨100, by decide⟩ (listedAt ⟨100, by decide⟩ hj))
      (colE1 ⟨100, by decide⟩ 5 (transLenTr ⟨100, by decide⟩ 5 hp)) T100_100
      hfix100_100 hinj100_100 hcardT100_100
      (fun i => conj_mem_of_fixedPoints _ _ (T100_100 i) (hfix100_100 i) _)
      ⟨100, by decide⟩ ⟨100, by decide⟩ _
      (Q2.validAt ⟨100, by decide⟩ (Q2.listedAt ⟨100, by decide⟩
        (alnCheck_rep ⟨100, by decide⟩ hj hq).1))
      (colE2 ⟨100, by decide⟩ 5 hp) Q2.T100_100_2 Q2.hfix100_100_2 Q2.hinj100_100_2
      Q2.hcardT100_100_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T100_100_2 i) (Q2.hfix100_100_2 i) _)
      ?_).symm
  rw [show colData1 (⟨100, by decide⟩ : Fin 148)
        ((colE1 ⟨100, by decide⟩ 5 (transLenTr ⟨100, by decide⟩ 5 hp) : ↥(reps ⟨100, by decide⟩)) : Coordinate 1)
        T100_100 = colFn colCert_100_100_5.D (m := 25) from colCert_100_100_5.bind1,
    show colData2 (⟨100, by decide⟩ : Fin 148)
        ((colE2 ⟨100, by decide⟩ 5 hp : ↥(Q2.reps ⟨100, by decide⟩)) : Coordinate 2)
        Q2.T100_100_2 = colFn colCert_100_100_5.D (m := 25) from colCert_100_100_5.bind2]
  exact alnAll_100_100_5 j hj hq

theorem leaf_100_100_10 (hp : 10 < (Q2.transData.getD 100 []).length)
    (j : Nat) (hj : j < (repChars.getD 100 []).length)
    (hq : (normIsRep.getD 100 []).getD j false = true) :
    species (Q2.reps (⟨100, by decide⟩ : Fin 148)) (colE2 ⟨100, by decide⟩ 10 hp)
        (rowE2 (⟨100, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨100, by decide⟩ : Fin 148))
        (colE1 ⟨100, by decide⟩ 10 (transLenTr ⟨100, by decide⟩ 10 hp))
        (rowE1 (⟨100, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨100, by decide⟩ : Fin 148) ⟨100, by decide⟩ _
      (validAt ⟨100, by decide⟩ (listedAt ⟨100, by decide⟩ hj))
      (colE1 ⟨100, by decide⟩ 10 (transLenTr ⟨100, by decide⟩ 10 hp)) T100_100
      hfix100_100 hinj100_100 hcardT100_100
      (fun i => conj_mem_of_fixedPoints _ _ (T100_100 i) (hfix100_100 i) _)
      ⟨100, by decide⟩ ⟨100, by decide⟩ _
      (Q2.validAt ⟨100, by decide⟩ (Q2.listedAt ⟨100, by decide⟩
        (alnCheck_rep ⟨100, by decide⟩ hj hq).1))
      (colE2 ⟨100, by decide⟩ 10 hp) Q2.T100_100_2 Q2.hfix100_100_2 Q2.hinj100_100_2
      Q2.hcardT100_100_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T100_100_2 i) (Q2.hfix100_100_2 i) _)
      ?_).symm
  rw [show colData1 (⟨100, by decide⟩ : Fin 148)
        ((colE1 ⟨100, by decide⟩ 10 (transLenTr ⟨100, by decide⟩ 10 hp) : ↥(reps ⟨100, by decide⟩)) : Coordinate 1)
        T100_100 = colFn colCert_100_100_10.D (m := 25) from colCert_100_100_10.bind1,
    show colData2 (⟨100, by decide⟩ : Fin 148)
        ((colE2 ⟨100, by decide⟩ 10 hp : ↥(Q2.reps ⟨100, by decide⟩)) : Coordinate 2)
        Q2.T100_100_2 = colFn colCert_100_100_10.D (m := 25) from colCert_100_100_10.bind2]
  exact alnAll_100_100_10 j hj hq

theorem leaf_100_100_15 (hp : 15 < (Q2.transData.getD 100 []).length)
    (j : Nat) (hj : j < (repChars.getD 100 []).length)
    (hq : (normIsRep.getD 100 []).getD j false = true) :
    species (Q2.reps (⟨100, by decide⟩ : Fin 148)) (colE2 ⟨100, by decide⟩ 15 hp)
        (rowE2 (⟨100, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨100, by decide⟩ : Fin 148))
        (colE1 ⟨100, by decide⟩ 15 (transLenTr ⟨100, by decide⟩ 15 hp))
        (rowE1 (⟨100, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨100, by decide⟩ : Fin 148) ⟨100, by decide⟩ _
      (validAt ⟨100, by decide⟩ (listedAt ⟨100, by decide⟩ hj))
      (colE1 ⟨100, by decide⟩ 15 (transLenTr ⟨100, by decide⟩ 15 hp)) T100_100
      hfix100_100 hinj100_100 hcardT100_100
      (fun i => conj_mem_of_fixedPoints _ _ (T100_100 i) (hfix100_100 i) _)
      ⟨100, by decide⟩ ⟨100, by decide⟩ _
      (Q2.validAt ⟨100, by decide⟩ (Q2.listedAt ⟨100, by decide⟩
        (alnCheck_rep ⟨100, by decide⟩ hj hq).1))
      (colE2 ⟨100, by decide⟩ 15 hp) Q2.T100_100_2 Q2.hfix100_100_2 Q2.hinj100_100_2
      Q2.hcardT100_100_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T100_100_2 i) (Q2.hfix100_100_2 i) _)
      ?_).symm
  rw [show colData1 (⟨100, by decide⟩ : Fin 148)
        ((colE1 ⟨100, by decide⟩ 15 (transLenTr ⟨100, by decide⟩ 15 hp) : ↥(reps ⟨100, by decide⟩)) : Coordinate 1)
        T100_100 = colFn colCert_100_100_15.D (m := 25) from colCert_100_100_15.bind1,
    show colData2 (⟨100, by decide⟩ : Fin 148)
        ((colE2 ⟨100, by decide⟩ 15 hp : ↥(Q2.reps ⟨100, by decide⟩)) : Coordinate 2)
        Q2.T100_100_2 = colFn colCert_100_100_15.D (m := 25) from colCert_100_100_15.bind2]
  exact alnAll_100_100_15 j hj hq

theorem leaf_100_100_20 (hp : 20 < (Q2.transData.getD 100 []).length)
    (j : Nat) (hj : j < (repChars.getD 100 []).length)
    (hq : (normIsRep.getD 100 []).getD j false = true) :
    species (Q2.reps (⟨100, by decide⟩ : Fin 148)) (colE2 ⟨100, by decide⟩ 20 hp)
        (rowE2 (⟨100, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨100, by decide⟩ : Fin 148))
        (colE1 ⟨100, by decide⟩ 20 (transLenTr ⟨100, by decide⟩ 20 hp))
        (rowE1 (⟨100, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨100, by decide⟩ : Fin 148) ⟨100, by decide⟩ _
      (validAt ⟨100, by decide⟩ (listedAt ⟨100, by decide⟩ hj))
      (colE1 ⟨100, by decide⟩ 20 (transLenTr ⟨100, by decide⟩ 20 hp)) T100_100
      hfix100_100 hinj100_100 hcardT100_100
      (fun i => conj_mem_of_fixedPoints _ _ (T100_100 i) (hfix100_100 i) _)
      ⟨100, by decide⟩ ⟨100, by decide⟩ _
      (Q2.validAt ⟨100, by decide⟩ (Q2.listedAt ⟨100, by decide⟩
        (alnCheck_rep ⟨100, by decide⟩ hj hq).1))
      (colE2 ⟨100, by decide⟩ 20 hp) Q2.T100_100_2 Q2.hfix100_100_2 Q2.hinj100_100_2
      Q2.hcardT100_100_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T100_100_2 i) (Q2.hfix100_100_2 i) _)
      ?_).symm
  rw [show colData1 (⟨100, by decide⟩ : Fin 148)
        ((colE1 ⟨100, by decide⟩ 20 (transLenTr ⟨100, by decide⟩ 20 hp) : ↥(reps ⟨100, by decide⟩)) : Coordinate 1)
        T100_100 = colFn colCert_100_100_20.D (m := 25) from colCert_100_100_20.bind1,
    show colData2 (⟨100, by decide⟩ : Fin 148)
        ((colE2 ⟨100, by decide⟩ 20 hp : ↥(Q2.reps ⟨100, by decide⟩)) : Coordinate 2)
        Q2.T100_100_2 = colFn colCert_100_100_20.D (m := 25) from colCert_100_100_20.bind2]
  exact alnAll_100_100_20 j hj hq

theorem leaf_100_100_25 (hp : 25 < (Q2.transData.getD 100 []).length)
    (j : Nat) (hj : j < (repChars.getD 100 []).length)
    (hq : (normIsRep.getD 100 []).getD j false = true) :
    species (Q2.reps (⟨100, by decide⟩ : Fin 148)) (colE2 ⟨100, by decide⟩ 25 hp)
        (rowE2 (⟨100, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨100, by decide⟩ : Fin 148))
        (colE1 ⟨100, by decide⟩ 25 (transLenTr ⟨100, by decide⟩ 25 hp))
        (rowE1 (⟨100, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨100, by decide⟩ : Fin 148) ⟨100, by decide⟩ _
      (validAt ⟨100, by decide⟩ (listedAt ⟨100, by decide⟩ hj))
      (colE1 ⟨100, by decide⟩ 25 (transLenTr ⟨100, by decide⟩ 25 hp)) T100_100
      hfix100_100 hinj100_100 hcardT100_100
      (fun i => conj_mem_of_fixedPoints _ _ (T100_100 i) (hfix100_100 i) _)
      ⟨100, by decide⟩ ⟨100, by decide⟩ _
      (Q2.validAt ⟨100, by decide⟩ (Q2.listedAt ⟨100, by decide⟩
        (alnCheck_rep ⟨100, by decide⟩ hj hq).1))
      (colE2 ⟨100, by decide⟩ 25 hp) Q2.T100_100_2 Q2.hfix100_100_2 Q2.hinj100_100_2
      Q2.hcardT100_100_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T100_100_2 i) (Q2.hfix100_100_2 i) _)
      ?_).symm
  rw [show colData1 (⟨100, by decide⟩ : Fin 148)
        ((colE1 ⟨100, by decide⟩ 25 (transLenTr ⟨100, by decide⟩ 25 hp) : ↥(reps ⟨100, by decide⟩)) : Coordinate 1)
        T100_100 = colFn colCert_100_100_25.D (m := 25) from colCert_100_100_25.bind1,
    show colData2 (⟨100, by decide⟩ : Fin 148)
        ((colE2 ⟨100, by decide⟩ 25 hp : ↥(Q2.reps ⟨100, by decide⟩)) : Coordinate 2)
        Q2.T100_100_2 = colFn colCert_100_100_25.D (m := 25) from colCert_100_100_25.bind2]
  exact alnAll_100_100_25 j hj hq

theorem leaf_100_100_50 (hp : 50 < (Q2.transData.getD 100 []).length)
    (j : Nat) (hj : j < (repChars.getD 100 []).length)
    (hq : (normIsRep.getD 100 []).getD j false = true) :
    species (Q2.reps (⟨100, by decide⟩ : Fin 148)) (colE2 ⟨100, by decide⟩ 50 hp)
        (rowE2 (⟨100, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨100, by decide⟩ : Fin 148))
        (colE1 ⟨100, by decide⟩ 50 (transLenTr ⟨100, by decide⟩ 50 hp))
        (rowE1 (⟨100, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨100, by decide⟩ : Fin 148) ⟨100, by decide⟩ _
      (validAt ⟨100, by decide⟩ (listedAt ⟨100, by decide⟩ hj))
      (colE1 ⟨100, by decide⟩ 50 (transLenTr ⟨100, by decide⟩ 50 hp)) T100_100
      hfix100_100 hinj100_100 hcardT100_100
      (fun i => conj_mem_of_fixedPoints _ _ (T100_100 i) (hfix100_100 i) _)
      ⟨100, by decide⟩ ⟨100, by decide⟩ _
      (Q2.validAt ⟨100, by decide⟩ (Q2.listedAt ⟨100, by decide⟩
        (alnCheck_rep ⟨100, by decide⟩ hj hq).1))
      (colE2 ⟨100, by decide⟩ 50 hp) Q2.T100_100_2 Q2.hfix100_100_2 Q2.hinj100_100_2
      Q2.hcardT100_100_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T100_100_2 i) (Q2.hfix100_100_2 i) _)
      ?_).symm
  rw [show colData1 (⟨100, by decide⟩ : Fin 148)
        ((colE1 ⟨100, by decide⟩ 50 (transLenTr ⟨100, by decide⟩ 50 hp) : ↥(reps ⟨100, by decide⟩)) : Coordinate 1)
        T100_100 = colFn colCert_100_100_50.D (m := 25) from colCert_100_100_50.bind1,
    show colData2 (⟨100, by decide⟩ : Fin 148)
        ((colE2 ⟨100, by decide⟩ 50 hp : ↥(Q2.reps ⟨100, by decide⟩)) : Coordinate 2)
        Q2.T100_100_2 = colFn colCert_100_100_50.D (m := 25) from colCert_100_100_50.bind2]
  exact alnAll_100_100_50 j hj hq

theorem leaf_100_100_75 (hp : 75 < (Q2.transData.getD 100 []).length)
    (j : Nat) (hj : j < (repChars.getD 100 []).length)
    (hq : (normIsRep.getD 100 []).getD j false = true) :
    species (Q2.reps (⟨100, by decide⟩ : Fin 148)) (colE2 ⟨100, by decide⟩ 75 hp)
        (rowE2 (⟨100, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨100, by decide⟩ : Fin 148))
        (colE1 ⟨100, by decide⟩ 75 (transLenTr ⟨100, by decide⟩ 75 hp))
        (rowE1 (⟨100, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨100, by decide⟩ : Fin 148) ⟨100, by decide⟩ _
      (validAt ⟨100, by decide⟩ (listedAt ⟨100, by decide⟩ hj))
      (colE1 ⟨100, by decide⟩ 75 (transLenTr ⟨100, by decide⟩ 75 hp)) T100_100
      hfix100_100 hinj100_100 hcardT100_100
      (fun i => conj_mem_of_fixedPoints _ _ (T100_100 i) (hfix100_100 i) _)
      ⟨100, by decide⟩ ⟨100, by decide⟩ _
      (Q2.validAt ⟨100, by decide⟩ (Q2.listedAt ⟨100, by decide⟩
        (alnCheck_rep ⟨100, by decide⟩ hj hq).1))
      (colE2 ⟨100, by decide⟩ 75 hp) Q2.T100_100_2 Q2.hfix100_100_2 Q2.hinj100_100_2
      Q2.hcardT100_100_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T100_100_2 i) (Q2.hfix100_100_2 i) _)
      ?_).symm
  rw [show colData1 (⟨100, by decide⟩ : Fin 148)
        ((colE1 ⟨100, by decide⟩ 75 (transLenTr ⟨100, by decide⟩ 75 hp) : ↥(reps ⟨100, by decide⟩)) : Coordinate 1)
        T100_100 = colFn colCert_100_100_75.D (m := 25) from colCert_100_100_75.bind1,
    show colData2 (⟨100, by decide⟩ : Fin 148)
        ((colE2 ⟨100, by decide⟩ 75 hp : ↥(Q2.reps ⟨100, by decide⟩)) : Coordinate 2)
        Q2.T100_100_2 = colFn colCert_100_100_75.D (m := 25) from colCert_100_100_75.bind2]
  exact alnAll_100_100_75 j hj hq

theorem leaf_100_100_100 (hp : 100 < (Q2.transData.getD 100 []).length)
    (j : Nat) (hj : j < (repChars.getD 100 []).length)
    (hq : (normIsRep.getD 100 []).getD j false = true) :
    species (Q2.reps (⟨100, by decide⟩ : Fin 148)) (colE2 ⟨100, by decide⟩ 100 hp)
        (rowE2 (⟨100, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨100, by decide⟩ : Fin 148))
        (colE1 ⟨100, by decide⟩ 100 (transLenTr ⟨100, by decide⟩ 100 hp))
        (rowE1 (⟨100, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨100, by decide⟩ : Fin 148) ⟨100, by decide⟩ _
      (validAt ⟨100, by decide⟩ (listedAt ⟨100, by decide⟩ hj))
      (colE1 ⟨100, by decide⟩ 100 (transLenTr ⟨100, by decide⟩ 100 hp)) T100_100
      hfix100_100 hinj100_100 hcardT100_100
      (fun i => conj_mem_of_fixedPoints _ _ (T100_100 i) (hfix100_100 i) _)
      ⟨100, by decide⟩ ⟨100, by decide⟩ _
      (Q2.validAt ⟨100, by decide⟩ (Q2.listedAt ⟨100, by decide⟩
        (alnCheck_rep ⟨100, by decide⟩ hj hq).1))
      (colE2 ⟨100, by decide⟩ 100 hp) Q2.T100_100_2 Q2.hfix100_100_2 Q2.hinj100_100_2
      Q2.hcardT100_100_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T100_100_2 i) (Q2.hfix100_100_2 i) _)
      ?_).symm
  rw [show colData1 (⟨100, by decide⟩ : Fin 148)
        ((colE1 ⟨100, by decide⟩ 100 (transLenTr ⟨100, by decide⟩ 100 hp) : ↥(reps ⟨100, by decide⟩)) : Coordinate 1)
        T100_100 = colFn colCert_100_100_100.D (m := 25) from colCert_100_100_100.bind1,
    show colData2 (⟨100, by decide⟩ : Fin 148)
        ((colE2 ⟨100, by decide⟩ 100 hp : ↥(Q2.reps ⟨100, by decide⟩)) : Coordinate 2)
        Q2.T100_100_2 = colFn colCert_100_100_100.D (m := 25) from colCert_100_100_100.bind2]
  exact alnAll_100_100_100 j hj hq

theorem leaf_101_10_0 (hp : 0 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 101 []).length)
    (hq : (normIsRep.getD 101 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 0 hp)
        (rowE2 (⟨101, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 0 (transLenTr ⟨10, by decide⟩ 0 hp))
        (rowE1 (⟨101, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨101, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨101, by decide⟩ (listedAt ⟨101, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 0 (transLenTr ⟨10, by decide⟩ 0 hp)) T101_10
      hfix101_10 hinj101_10 hcardT101_10
      (fun i => conj_mem_of_fixedPoints _ _ (T101_10 i) (hfix101_10 i) _)
      ⟨101, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨101, by decide⟩ (Q2.listedAt ⟨101, by decide⟩
        (alnCheck_rep ⟨101, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 0 hp) Q2.T101_10_2 Q2.hfix101_10_2 Q2.hinj101_10_2
      Q2.hcardT101_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T101_10_2 i) (Q2.hfix101_10_2 i) _)
      colCert_101_10_0.hD ?_).symm
  rw [alnId_101 j hj]


theorem leaf_101_10_1 (hp : 1 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 101 []).length)
    (hq : (normIsRep.getD 101 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 1 hp)
        (rowE2 (⟨101, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 1 (transLenTr ⟨10, by decide⟩ 1 hp))
        (rowE1 (⟨101, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨101, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨101, by decide⟩ (listedAt ⟨101, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 1 (transLenTr ⟨10, by decide⟩ 1 hp)) T101_10
      hfix101_10 hinj101_10 hcardT101_10
      (fun i => conj_mem_of_fixedPoints _ _ (T101_10 i) (hfix101_10 i) _)
      ⟨101, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨101, by decide⟩ (Q2.listedAt ⟨101, by decide⟩
        (alnCheck_rep ⟨101, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 1 hp) Q2.T101_10_2 Q2.hfix101_10_2 Q2.hinj101_10_2
      Q2.hcardT101_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T101_10_2 i) (Q2.hfix101_10_2 i) _)
      colCert_101_10_1.hD ?_).symm
  rw [alnId_101 j hj]


theorem leaf_101_10_2 (hp : 2 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 101 []).length)
    (hq : (normIsRep.getD 101 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 2 hp)
        (rowE2 (⟨101, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 2 (transLenTr ⟨10, by decide⟩ 2 hp))
        (rowE1 (⟨101, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨101, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨101, by decide⟩ (listedAt ⟨101, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 2 (transLenTr ⟨10, by decide⟩ 2 hp)) T101_10
      hfix101_10 hinj101_10 hcardT101_10
      (fun i => conj_mem_of_fixedPoints _ _ (T101_10 i) (hfix101_10 i) _)
      ⟨101, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨101, by decide⟩ (Q2.listedAt ⟨101, by decide⟩
        (alnCheck_rep ⟨101, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 2 hp) Q2.T101_10_2 Q2.hfix101_10_2 Q2.hinj101_10_2
      Q2.hcardT101_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T101_10_2 i) (Q2.hfix101_10_2 i) _)
      colCert_101_10_2.hD ?_).symm
  rw [alnId_101 j hj]


theorem leaf_101_10_3 (hp : 3 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 101 []).length)
    (hq : (normIsRep.getD 101 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 3 hp)
        (rowE2 (⟨101, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 3 (transLenTr ⟨10, by decide⟩ 3 hp))
        (rowE1 (⟨101, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨101, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨101, by decide⟩ (listedAt ⟨101, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 3 (transLenTr ⟨10, by decide⟩ 3 hp)) T101_10
      hfix101_10 hinj101_10 hcardT101_10
      (fun i => conj_mem_of_fixedPoints _ _ (T101_10 i) (hfix101_10 i) _)
      ⟨101, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨101, by decide⟩ (Q2.listedAt ⟨101, by decide⟩
        (alnCheck_rep ⟨101, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 3 hp) Q2.T101_10_2 Q2.hfix101_10_2 Q2.hinj101_10_2
      Q2.hcardT101_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T101_10_2 i) (Q2.hfix101_10_2 i) _)
      colCert_101_10_3.hD ?_).symm
  rw [alnId_101 j hj]


theorem leaf_101_10_4 (hp : 4 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 101 []).length)
    (hq : (normIsRep.getD 101 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 4 hp)
        (rowE2 (⟨101, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 4 (transLenTr ⟨10, by decide⟩ 4 hp))
        (rowE1 (⟨101, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨101, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨101, by decide⟩ (listedAt ⟨101, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 4 (transLenTr ⟨10, by decide⟩ 4 hp)) T101_10
      hfix101_10 hinj101_10 hcardT101_10
      (fun i => conj_mem_of_fixedPoints _ _ (T101_10 i) (hfix101_10 i) _)
      ⟨101, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨101, by decide⟩ (Q2.listedAt ⟨101, by decide⟩
        (alnCheck_rep ⟨101, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 4 hp) Q2.T101_10_2 Q2.hfix101_10_2 Q2.hinj101_10_2
      Q2.hcardT101_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T101_10_2 i) (Q2.hfix101_10_2 i) _)
      colCert_101_10_4.hD ?_).symm
  rw [alnId_101 j hj]


theorem leaf_101_12_0 (hp : 0 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 101 []).length)
    (hq : (normIsRep.getD 101 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 0 hp)
        (rowE2 (⟨101, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp))
        (rowE1 (⟨101, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨101, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨101, by decide⟩ (listedAt ⟨101, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp)) T101_12
      hfix101_12 hinj101_12 hcardT101_12
      (fun i => conj_mem_of_fixedPoints _ _ (T101_12 i) (hfix101_12 i) _)
      ⟨101, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨101, by decide⟩ (Q2.listedAt ⟨101, by decide⟩
        (alnCheck_rep ⟨101, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 0 hp) Q2.T101_12_2 Q2.hfix101_12_2 Q2.hinj101_12_2
      Q2.hcardT101_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T101_12_2 i) (Q2.hfix101_12_2 i) _)
      colCert_101_12_0.hD ?_).symm
  rw [alnId_101 j hj]


theorem leaf_101_12_1 (hp : 1 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 101 []).length)
    (hq : (normIsRep.getD 101 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 1 hp)
        (rowE2 (⟨101, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp))
        (rowE1 (⟨101, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨101, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨101, by decide⟩ (listedAt ⟨101, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp)) T101_12
      hfix101_12 hinj101_12 hcardT101_12
      (fun i => conj_mem_of_fixedPoints _ _ (T101_12 i) (hfix101_12 i) _)
      ⟨101, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨101, by decide⟩ (Q2.listedAt ⟨101, by decide⟩
        (alnCheck_rep ⟨101, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 1 hp) Q2.T101_12_2 Q2.hfix101_12_2 Q2.hinj101_12_2
      Q2.hcardT101_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T101_12_2 i) (Q2.hfix101_12_2 i) _)
      colCert_101_12_1.hD ?_).symm
  rw [alnId_101 j hj]


theorem leaf_101_12_2 (hp : 2 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 101 []).length)
    (hq : (normIsRep.getD 101 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 2 hp)
        (rowE2 (⟨101, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp))
        (rowE1 (⟨101, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨101, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨101, by decide⟩ (listedAt ⟨101, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp)) T101_12
      hfix101_12 hinj101_12 hcardT101_12
      (fun i => conj_mem_of_fixedPoints _ _ (T101_12 i) (hfix101_12 i) _)
      ⟨101, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨101, by decide⟩ (Q2.listedAt ⟨101, by decide⟩
        (alnCheck_rep ⟨101, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 2 hp) Q2.T101_12_2 Q2.hfix101_12_2 Q2.hinj101_12_2
      Q2.hcardT101_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T101_12_2 i) (Q2.hfix101_12_2 i) _)
      colCert_101_12_2.hD ?_).symm
  rw [alnId_101 j hj]


theorem leaf_101_12_3 (hp : 3 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 101 []).length)
    (hq : (normIsRep.getD 101 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 3 hp)
        (rowE2 (⟨101, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp))
        (rowE1 (⟨101, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨101, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨101, by decide⟩ (listedAt ⟨101, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp)) T101_12
      hfix101_12 hinj101_12 hcardT101_12
      (fun i => conj_mem_of_fixedPoints _ _ (T101_12 i) (hfix101_12 i) _)
      ⟨101, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨101, by decide⟩ (Q2.listedAt ⟨101, by decide⟩
        (alnCheck_rep ⟨101, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 3 hp) Q2.T101_12_2 Q2.hfix101_12_2 Q2.hinj101_12_2
      Q2.hcardT101_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T101_12_2 i) (Q2.hfix101_12_2 i) _)
      colCert_101_12_3.hD ?_).symm
  rw [alnId_101 j hj]


theorem leaf_101_12_4 (hp : 4 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 101 []).length)
    (hq : (normIsRep.getD 101 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 4 hp)
        (rowE2 (⟨101, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp))
        (rowE1 (⟨101, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨101, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨101, by decide⟩ (listedAt ⟨101, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp)) T101_12
      hfix101_12 hinj101_12 hcardT101_12
      (fun i => conj_mem_of_fixedPoints _ _ (T101_12 i) (hfix101_12 i) _)
      ⟨101, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨101, by decide⟩ (Q2.listedAt ⟨101, by decide⟩
        (alnCheck_rep ⟨101, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 4 hp) Q2.T101_12_2 Q2.hfix101_12_2 Q2.hinj101_12_2
      Q2.hcardT101_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T101_12_2 i) (Q2.hfix101_12_2 i) _)
      colCert_101_12_4.hD ?_).symm
  rw [alnId_101 j hj]


theorem leaf_101_39_0 (hp : 0 < (Q2.transData.getD 39 []).length)
    (j : Nat) (hj : j < (repChars.getD 101 []).length)
    (hq : (normIsRep.getD 101 []).getD j false = true) :
    species (Q2.reps (⟨39, by decide⟩ : Fin 148)) (colE2 ⟨39, by decide⟩ 0 hp)
        (rowE2 (⟨101, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨39, by decide⟩ : Fin 148))
        (colE1 ⟨39, by decide⟩ 0 (transLenTr ⟨39, by decide⟩ 0 hp))
        (rowE1 (⟨101, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨101, by decide⟩ : Fin 148) ⟨39, by decide⟩ _
      (validAt ⟨101, by decide⟩ (listedAt ⟨101, by decide⟩ hj))
      (colE1 ⟨39, by decide⟩ 0 (transLenTr ⟨39, by decide⟩ 0 hp)) T101_39
      hfix101_39 hinj101_39 hcardT101_39
      (fun i => conj_mem_of_fixedPoints _ _ (T101_39 i) (hfix101_39 i) _)
      ⟨101, by decide⟩ ⟨39, by decide⟩ _
      (Q2.validAt ⟨101, by decide⟩ (Q2.listedAt ⟨101, by decide⟩
        (alnCheck_rep ⟨101, by decide⟩ hj hq).1))
      (colE2 ⟨39, by decide⟩ 0 hp) Q2.T101_39_2 Q2.hfix101_39_2 Q2.hinj101_39_2
      Q2.hcardT101_39_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T101_39_2 i) (Q2.hfix101_39_2 i) _)
      colCert_101_39_0.hD ?_).symm
  rw [alnId_101 j hj]


theorem leaf_101_39_1 (hp : 1 < (Q2.transData.getD 39 []).length)
    (j : Nat) (hj : j < (repChars.getD 101 []).length)
    (hq : (normIsRep.getD 101 []).getD j false = true) :
    species (Q2.reps (⟨39, by decide⟩ : Fin 148)) (colE2 ⟨39, by decide⟩ 1 hp)
        (rowE2 (⟨101, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨39, by decide⟩ : Fin 148))
        (colE1 ⟨39, by decide⟩ 1 (transLenTr ⟨39, by decide⟩ 1 hp))
        (rowE1 (⟨101, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨101, by decide⟩ : Fin 148) ⟨39, by decide⟩ _
      (validAt ⟨101, by decide⟩ (listedAt ⟨101, by decide⟩ hj))
      (colE1 ⟨39, by decide⟩ 1 (transLenTr ⟨39, by decide⟩ 1 hp)) T101_39
      hfix101_39 hinj101_39 hcardT101_39
      (fun i => conj_mem_of_fixedPoints _ _ (T101_39 i) (hfix101_39 i) _)
      ⟨101, by decide⟩ ⟨39, by decide⟩ _
      (Q2.validAt ⟨101, by decide⟩ (Q2.listedAt ⟨101, by decide⟩
        (alnCheck_rep ⟨101, by decide⟩ hj hq).1))
      (colE2 ⟨39, by decide⟩ 1 hp) Q2.T101_39_2 Q2.hfix101_39_2 Q2.hinj101_39_2
      Q2.hcardT101_39_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T101_39_2 i) (Q2.hfix101_39_2 i) _)
      colCert_101_39_1.hD ?_).symm
  rw [alnId_101 j hj]


theorem leaf_101_39_2 (hp : 2 < (Q2.transData.getD 39 []).length)
    (j : Nat) (hj : j < (repChars.getD 101 []).length)
    (hq : (normIsRep.getD 101 []).getD j false = true) :
    species (Q2.reps (⟨39, by decide⟩ : Fin 148)) (colE2 ⟨39, by decide⟩ 2 hp)
        (rowE2 (⟨101, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨39, by decide⟩ : Fin 148))
        (colE1 ⟨39, by decide⟩ 2 (transLenTr ⟨39, by decide⟩ 2 hp))
        (rowE1 (⟨101, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨101, by decide⟩ : Fin 148) ⟨39, by decide⟩ _
      (validAt ⟨101, by decide⟩ (listedAt ⟨101, by decide⟩ hj))
      (colE1 ⟨39, by decide⟩ 2 (transLenTr ⟨39, by decide⟩ 2 hp)) T101_39
      hfix101_39 hinj101_39 hcardT101_39
      (fun i => conj_mem_of_fixedPoints _ _ (T101_39 i) (hfix101_39 i) _)
      ⟨101, by decide⟩ ⟨39, by decide⟩ _
      (Q2.validAt ⟨101, by decide⟩ (Q2.listedAt ⟨101, by decide⟩
        (alnCheck_rep ⟨101, by decide⟩ hj hq).1))
      (colE2 ⟨39, by decide⟩ 2 hp) Q2.T101_39_2 Q2.hfix101_39_2 Q2.hinj101_39_2
      Q2.hcardT101_39_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T101_39_2 i) (Q2.hfix101_39_2 i) _)
      colCert_101_39_2.hD ?_).symm
  rw [alnId_101 j hj]


theorem leaf_101_39_3 (hp : 3 < (Q2.transData.getD 39 []).length)
    (j : Nat) (hj : j < (repChars.getD 101 []).length)
    (hq : (normIsRep.getD 101 []).getD j false = true) :
    species (Q2.reps (⟨39, by decide⟩ : Fin 148)) (colE2 ⟨39, by decide⟩ 3 hp)
        (rowE2 (⟨101, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨39, by decide⟩ : Fin 148))
        (colE1 ⟨39, by decide⟩ 3 (transLenTr ⟨39, by decide⟩ 3 hp))
        (rowE1 (⟨101, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨101, by decide⟩ : Fin 148) ⟨39, by decide⟩ _
      (validAt ⟨101, by decide⟩ (listedAt ⟨101, by decide⟩ hj))
      (colE1 ⟨39, by decide⟩ 3 (transLenTr ⟨39, by decide⟩ 3 hp)) T101_39
      hfix101_39 hinj101_39 hcardT101_39
      (fun i => conj_mem_of_fixedPoints _ _ (T101_39 i) (hfix101_39 i) _)
      ⟨101, by decide⟩ ⟨39, by decide⟩ _
      (Q2.validAt ⟨101, by decide⟩ (Q2.listedAt ⟨101, by decide⟩
        (alnCheck_rep ⟨101, by decide⟩ hj hq).1))
      (colE2 ⟨39, by decide⟩ 3 hp) Q2.T101_39_2 Q2.hfix101_39_2 Q2.hinj101_39_2
      Q2.hcardT101_39_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T101_39_2 i) (Q2.hfix101_39_2 i) _)
      colCert_101_39_3.hD ?_).symm
  rw [alnId_101 j hj]


theorem leaf_101_39_4 (hp : 4 < (Q2.transData.getD 39 []).length)
    (j : Nat) (hj : j < (repChars.getD 101 []).length)
    (hq : (normIsRep.getD 101 []).getD j false = true) :
    species (Q2.reps (⟨39, by decide⟩ : Fin 148)) (colE2 ⟨39, by decide⟩ 4 hp)
        (rowE2 (⟨101, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨39, by decide⟩ : Fin 148))
        (colE1 ⟨39, by decide⟩ 4 (transLenTr ⟨39, by decide⟩ 4 hp))
        (rowE1 (⟨101, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨101, by decide⟩ : Fin 148) ⟨39, by decide⟩ _
      (validAt ⟨101, by decide⟩ (listedAt ⟨101, by decide⟩ hj))
      (colE1 ⟨39, by decide⟩ 4 (transLenTr ⟨39, by decide⟩ 4 hp)) T101_39
      hfix101_39 hinj101_39 hcardT101_39
      (fun i => conj_mem_of_fixedPoints _ _ (T101_39 i) (hfix101_39 i) _)
      ⟨101, by decide⟩ ⟨39, by decide⟩ _
      (Q2.validAt ⟨101, by decide⟩ (Q2.listedAt ⟨101, by decide⟩
        (alnCheck_rep ⟨101, by decide⟩ hj hq).1))
      (colE2 ⟨39, by decide⟩ 4 hp) Q2.T101_39_2 Q2.hfix101_39_2 Q2.hinj101_39_2
      Q2.hcardT101_39_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T101_39_2 i) (Q2.hfix101_39_2 i) _)
      colCert_101_39_4.hD ?_).symm
  rw [alnId_101 j hj]


theorem leaf_101_39_5 (hp : 5 < (Q2.transData.getD 39 []).length)
    (j : Nat) (hj : j < (repChars.getD 101 []).length)
    (hq : (normIsRep.getD 101 []).getD j false = true) :
    species (Q2.reps (⟨39, by decide⟩ : Fin 148)) (colE2 ⟨39, by decide⟩ 5 hp)
        (rowE2 (⟨101, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨39, by decide⟩ : Fin 148))
        (colE1 ⟨39, by decide⟩ 5 (transLenTr ⟨39, by decide⟩ 5 hp))
        (rowE1 (⟨101, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨101, by decide⟩ : Fin 148) ⟨39, by decide⟩ _
      (validAt ⟨101, by decide⟩ (listedAt ⟨101, by decide⟩ hj))
      (colE1 ⟨39, by decide⟩ 5 (transLenTr ⟨39, by decide⟩ 5 hp)) T101_39
      hfix101_39 hinj101_39 hcardT101_39
      (fun i => conj_mem_of_fixedPoints _ _ (T101_39 i) (hfix101_39 i) _)
      ⟨101, by decide⟩ ⟨39, by decide⟩ _
      (Q2.validAt ⟨101, by decide⟩ (Q2.listedAt ⟨101, by decide⟩
        (alnCheck_rep ⟨101, by decide⟩ hj hq).1))
      (colE2 ⟨39, by decide⟩ 5 hp) Q2.T101_39_2 Q2.hfix101_39_2 Q2.hinj101_39_2
      Q2.hcardT101_39_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T101_39_2 i) (Q2.hfix101_39_2 i) _)
      colCert_101_39_5.hD ?_).symm
  rw [alnId_101 j hj]


theorem leaf_101_39_10 (hp : 10 < (Q2.transData.getD 39 []).length)
    (j : Nat) (hj : j < (repChars.getD 101 []).length)
    (hq : (normIsRep.getD 101 []).getD j false = true) :
    species (Q2.reps (⟨39, by decide⟩ : Fin 148)) (colE2 ⟨39, by decide⟩ 10 hp)
        (rowE2 (⟨101, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨39, by decide⟩ : Fin 148))
        (colE1 ⟨39, by decide⟩ 10 (transLenTr ⟨39, by decide⟩ 10 hp))
        (rowE1 (⟨101, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨101, by decide⟩ : Fin 148) ⟨39, by decide⟩ _
      (validAt ⟨101, by decide⟩ (listedAt ⟨101, by decide⟩ hj))
      (colE1 ⟨39, by decide⟩ 10 (transLenTr ⟨39, by decide⟩ 10 hp)) T101_39
      hfix101_39 hinj101_39 hcardT101_39
      (fun i => conj_mem_of_fixedPoints _ _ (T101_39 i) (hfix101_39 i) _)
      ⟨101, by decide⟩ ⟨39, by decide⟩ _
      (Q2.validAt ⟨101, by decide⟩ (Q2.listedAt ⟨101, by decide⟩
        (alnCheck_rep ⟨101, by decide⟩ hj hq).1))
      (colE2 ⟨39, by decide⟩ 10 hp) Q2.T101_39_2 Q2.hfix101_39_2 Q2.hinj101_39_2
      Q2.hcardT101_39_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T101_39_2 i) (Q2.hfix101_39_2 i) _)
      colCert_101_39_10.hD ?_).symm
  rw [alnId_101 j hj]


theorem leaf_101_39_15 (hp : 15 < (Q2.transData.getD 39 []).length)
    (j : Nat) (hj : j < (repChars.getD 101 []).length)
    (hq : (normIsRep.getD 101 []).getD j false = true) :
    species (Q2.reps (⟨39, by decide⟩ : Fin 148)) (colE2 ⟨39, by decide⟩ 15 hp)
        (rowE2 (⟨101, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨39, by decide⟩ : Fin 148))
        (colE1 ⟨39, by decide⟩ 15 (transLenTr ⟨39, by decide⟩ 15 hp))
        (rowE1 (⟨101, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨101, by decide⟩ : Fin 148) ⟨39, by decide⟩ _
      (validAt ⟨101, by decide⟩ (listedAt ⟨101, by decide⟩ hj))
      (colE1 ⟨39, by decide⟩ 15 (transLenTr ⟨39, by decide⟩ 15 hp)) T101_39
      hfix101_39 hinj101_39 hcardT101_39
      (fun i => conj_mem_of_fixedPoints _ _ (T101_39 i) (hfix101_39 i) _)
      ⟨101, by decide⟩ ⟨39, by decide⟩ _
      (Q2.validAt ⟨101, by decide⟩ (Q2.listedAt ⟨101, by decide⟩
        (alnCheck_rep ⟨101, by decide⟩ hj hq).1))
      (colE2 ⟨39, by decide⟩ 15 hp) Q2.T101_39_2 Q2.hfix101_39_2 Q2.hinj101_39_2
      Q2.hcardT101_39_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T101_39_2 i) (Q2.hfix101_39_2 i) _)
      colCert_101_39_15.hD ?_).symm
  rw [alnId_101 j hj]


theorem leaf_101_39_20 (hp : 20 < (Q2.transData.getD 39 []).length)
    (j : Nat) (hj : j < (repChars.getD 101 []).length)
    (hq : (normIsRep.getD 101 []).getD j false = true) :
    species (Q2.reps (⟨39, by decide⟩ : Fin 148)) (colE2 ⟨39, by decide⟩ 20 hp)
        (rowE2 (⟨101, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨39, by decide⟩ : Fin 148))
        (colE1 ⟨39, by decide⟩ 20 (transLenTr ⟨39, by decide⟩ 20 hp))
        (rowE1 (⟨101, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨101, by decide⟩ : Fin 148) ⟨39, by decide⟩ _
      (validAt ⟨101, by decide⟩ (listedAt ⟨101, by decide⟩ hj))
      (colE1 ⟨39, by decide⟩ 20 (transLenTr ⟨39, by decide⟩ 20 hp)) T101_39
      hfix101_39 hinj101_39 hcardT101_39
      (fun i => conj_mem_of_fixedPoints _ _ (T101_39 i) (hfix101_39 i) _)
      ⟨101, by decide⟩ ⟨39, by decide⟩ _
      (Q2.validAt ⟨101, by decide⟩ (Q2.listedAt ⟨101, by decide⟩
        (alnCheck_rep ⟨101, by decide⟩ hj hq).1))
      (colE2 ⟨39, by decide⟩ 20 hp) Q2.T101_39_2 Q2.hfix101_39_2 Q2.hinj101_39_2
      Q2.hcardT101_39_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T101_39_2 i) (Q2.hfix101_39_2 i) _)
      colCert_101_39_20.hD ?_).symm
  rw [alnId_101 j hj]


theorem leaf_101_53_0 (hp : 0 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 101 []).length)
    (hq : (normIsRep.getD 101 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 0 hp)
        (rowE2 (⟨101, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 0 (transLenTr ⟨53, by decide⟩ 0 hp))
        (rowE1 (⟨101, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨101, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨101, by decide⟩ (listedAt ⟨101, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 0 (transLenTr ⟨53, by decide⟩ 0 hp)) T101_53
      hfix101_53 hinj101_53 hcardT101_53
      (fun i => conj_mem_of_fixedPoints _ _ (T101_53 i) (hfix101_53 i) _)
      ⟨101, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨101, by decide⟩ (Q2.listedAt ⟨101, by decide⟩
        (alnCheck_rep ⟨101, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 0 hp) Q2.T101_53_2 Q2.hfix101_53_2 Q2.hinj101_53_2
      Q2.hcardT101_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T101_53_2 i) (Q2.hfix101_53_2 i) _)
      colCert_101_53_0.hD ?_).symm
  rw [alnId_101 j hj]


theorem leaf_101_53_1 (hp : 1 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 101 []).length)
    (hq : (normIsRep.getD 101 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 1 hp)
        (rowE2 (⟨101, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 1 (transLenTr ⟨53, by decide⟩ 1 hp))
        (rowE1 (⟨101, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨101, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨101, by decide⟩ (listedAt ⟨101, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 1 (transLenTr ⟨53, by decide⟩ 1 hp)) T101_53
      hfix101_53 hinj101_53 hcardT101_53
      (fun i => conj_mem_of_fixedPoints _ _ (T101_53 i) (hfix101_53 i) _)
      ⟨101, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨101, by decide⟩ (Q2.listedAt ⟨101, by decide⟩
        (alnCheck_rep ⟨101, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 1 hp) Q2.T101_53_2 Q2.hfix101_53_2 Q2.hinj101_53_2
      Q2.hcardT101_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T101_53_2 i) (Q2.hfix101_53_2 i) _)
      colCert_101_53_1.hD ?_).symm
  rw [alnId_101 j hj]


theorem leaf_101_53_2 (hp : 2 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 101 []).length)
    (hq : (normIsRep.getD 101 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 2 hp)
        (rowE2 (⟨101, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 2 (transLenTr ⟨53, by decide⟩ 2 hp))
        (rowE1 (⟨101, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨101, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨101, by decide⟩ (listedAt ⟨101, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 2 (transLenTr ⟨53, by decide⟩ 2 hp)) T101_53
      hfix101_53 hinj101_53 hcardT101_53
      (fun i => conj_mem_of_fixedPoints _ _ (T101_53 i) (hfix101_53 i) _)
      ⟨101, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨101, by decide⟩ (Q2.listedAt ⟨101, by decide⟩
        (alnCheck_rep ⟨101, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 2 hp) Q2.T101_53_2 Q2.hfix101_53_2 Q2.hinj101_53_2
      Q2.hcardT101_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T101_53_2 i) (Q2.hfix101_53_2 i) _)
      colCert_101_53_2.hD ?_).symm
  rw [alnId_101 j hj]


theorem leaf_101_53_3 (hp : 3 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 101 []).length)
    (hq : (normIsRep.getD 101 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 3 hp)
        (rowE2 (⟨101, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 3 (transLenTr ⟨53, by decide⟩ 3 hp))
        (rowE1 (⟨101, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨101, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨101, by decide⟩ (listedAt ⟨101, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 3 (transLenTr ⟨53, by decide⟩ 3 hp)) T101_53
      hfix101_53 hinj101_53 hcardT101_53
      (fun i => conj_mem_of_fixedPoints _ _ (T101_53 i) (hfix101_53 i) _)
      ⟨101, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨101, by decide⟩ (Q2.listedAt ⟨101, by decide⟩
        (alnCheck_rep ⟨101, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 3 hp) Q2.T101_53_2 Q2.hfix101_53_2 Q2.hinj101_53_2
      Q2.hcardT101_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T101_53_2 i) (Q2.hfix101_53_2 i) _)
      colCert_101_53_3.hD ?_).symm
  rw [alnId_101 j hj]


theorem leaf_101_53_4 (hp : 4 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 101 []).length)
    (hq : (normIsRep.getD 101 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 4 hp)
        (rowE2 (⟨101, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 4 (transLenTr ⟨53, by decide⟩ 4 hp))
        (rowE1 (⟨101, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨101, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨101, by decide⟩ (listedAt ⟨101, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 4 (transLenTr ⟨53, by decide⟩ 4 hp)) T101_53
      hfix101_53 hinj101_53 hcardT101_53
      (fun i => conj_mem_of_fixedPoints _ _ (T101_53 i) (hfix101_53 i) _)
      ⟨101, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨101, by decide⟩ (Q2.listedAt ⟨101, by decide⟩
        (alnCheck_rep ⟨101, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 4 hp) Q2.T101_53_2 Q2.hfix101_53_2 Q2.hinj101_53_2
      Q2.hcardT101_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T101_53_2 i) (Q2.hfix101_53_2 i) _)
      colCert_101_53_4.hD ?_).symm
  rw [alnId_101 j hj]


theorem leaf_101_53_5 (hp : 5 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 101 []).length)
    (hq : (normIsRep.getD 101 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 5 hp)
        (rowE2 (⟨101, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 5 (transLenTr ⟨53, by decide⟩ 5 hp))
        (rowE1 (⟨101, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨101, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨101, by decide⟩ (listedAt ⟨101, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 5 (transLenTr ⟨53, by decide⟩ 5 hp)) T101_53
      hfix101_53 hinj101_53 hcardT101_53
      (fun i => conj_mem_of_fixedPoints _ _ (T101_53 i) (hfix101_53 i) _)
      ⟨101, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨101, by decide⟩ (Q2.listedAt ⟨101, by decide⟩
        (alnCheck_rep ⟨101, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 5 hp) Q2.T101_53_2 Q2.hfix101_53_2 Q2.hinj101_53_2
      Q2.hcardT101_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T101_53_2 i) (Q2.hfix101_53_2 i) _)
      colCert_101_53_5.hD ?_).symm
  rw [alnId_101 j hj]


theorem leaf_101_53_10 (hp : 10 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 101 []).length)
    (hq : (normIsRep.getD 101 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 10 hp)
        (rowE2 (⟨101, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 10 (transLenTr ⟨53, by decide⟩ 10 hp))
        (rowE1 (⟨101, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨101, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨101, by decide⟩ (listedAt ⟨101, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 10 (transLenTr ⟨53, by decide⟩ 10 hp)) T101_53
      hfix101_53 hinj101_53 hcardT101_53
      (fun i => conj_mem_of_fixedPoints _ _ (T101_53 i) (hfix101_53 i) _)
      ⟨101, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨101, by decide⟩ (Q2.listedAt ⟨101, by decide⟩
        (alnCheck_rep ⟨101, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 10 hp) Q2.T101_53_2 Q2.hfix101_53_2 Q2.hinj101_53_2
      Q2.hcardT101_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T101_53_2 i) (Q2.hfix101_53_2 i) _)
      colCert_101_53_10.hD ?_).symm
  rw [alnId_101 j hj]


theorem leaf_101_53_15 (hp : 15 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 101 []).length)
    (hq : (normIsRep.getD 101 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 15 hp)
        (rowE2 (⟨101, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 15 (transLenTr ⟨53, by decide⟩ 15 hp))
        (rowE1 (⟨101, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨101, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨101, by decide⟩ (listedAt ⟨101, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 15 (transLenTr ⟨53, by decide⟩ 15 hp)) T101_53
      hfix101_53 hinj101_53 hcardT101_53
      (fun i => conj_mem_of_fixedPoints _ _ (T101_53 i) (hfix101_53 i) _)
      ⟨101, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨101, by decide⟩ (Q2.listedAt ⟨101, by decide⟩
        (alnCheck_rep ⟨101, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 15 hp) Q2.T101_53_2 Q2.hfix101_53_2 Q2.hinj101_53_2
      Q2.hcardT101_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T101_53_2 i) (Q2.hfix101_53_2 i) _)
      colCert_101_53_15.hD ?_).symm
  rw [alnId_101 j hj]


theorem leaf_101_53_20 (hp : 20 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 101 []).length)
    (hq : (normIsRep.getD 101 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 20 hp)
        (rowE2 (⟨101, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 20 (transLenTr ⟨53, by decide⟩ 20 hp))
        (rowE1 (⟨101, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨101, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨101, by decide⟩ (listedAt ⟨101, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 20 (transLenTr ⟨53, by decide⟩ 20 hp)) T101_53
      hfix101_53 hinj101_53 hcardT101_53
      (fun i => conj_mem_of_fixedPoints _ _ (T101_53 i) (hfix101_53 i) _)
      ⟨101, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨101, by decide⟩ (Q2.listedAt ⟨101, by decide⟩
        (alnCheck_rep ⟨101, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 20 hp) Q2.T101_53_2 Q2.hfix101_53_2 Q2.hinj101_53_2
      Q2.hcardT101_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T101_53_2 i) (Q2.hfix101_53_2 i) _)
      colCert_101_53_20.hD ?_).symm
  rw [alnId_101 j hj]


theorem leaf_101_101_0 (hp : 0 < (Q2.transData.getD 101 []).length)
    (j : Nat) (hj : j < (repChars.getD 101 []).length)
    (hq : (normIsRep.getD 101 []).getD j false = true) :
    species (Q2.reps (⟨101, by decide⟩ : Fin 148)) (colE2 ⟨101, by decide⟩ 0 hp)
        (rowE2 (⟨101, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨101, by decide⟩ : Fin 148))
        (colE1 ⟨101, by decide⟩ 0 (transLenTr ⟨101, by decide⟩ 0 hp))
        (rowE1 (⟨101, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨101, by decide⟩ : Fin 148) ⟨101, by decide⟩ _
      (validAt ⟨101, by decide⟩ (listedAt ⟨101, by decide⟩ hj))
      (colE1 ⟨101, by decide⟩ 0 (transLenTr ⟨101, by decide⟩ 0 hp)) T101_101
      hfix101_101 hinj101_101 hcardT101_101
      (fun i => conj_mem_of_fixedPoints _ _ (T101_101 i) (hfix101_101 i) _)
      ⟨101, by decide⟩ ⟨101, by decide⟩ _
      (Q2.validAt ⟨101, by decide⟩ (Q2.listedAt ⟨101, by decide⟩
        (alnCheck_rep ⟨101, by decide⟩ hj hq).1))
      (colE2 ⟨101, by decide⟩ 0 hp) Q2.T101_101_2 Q2.hfix101_101_2 Q2.hinj101_101_2
      Q2.hcardT101_101_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T101_101_2 i) (Q2.hfix101_101_2 i) _)
      colCert_101_101_0.hD ?_).symm
  rw [alnId_101 j hj]


theorem leaf_101_101_1 (hp : 1 < (Q2.transData.getD 101 []).length)
    (j : Nat) (hj : j < (repChars.getD 101 []).length)
    (hq : (normIsRep.getD 101 []).getD j false = true) :
    species (Q2.reps (⟨101, by decide⟩ : Fin 148)) (colE2 ⟨101, by decide⟩ 1 hp)
        (rowE2 (⟨101, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨101, by decide⟩ : Fin 148))
        (colE1 ⟨101, by decide⟩ 1 (transLenTr ⟨101, by decide⟩ 1 hp))
        (rowE1 (⟨101, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨101, by decide⟩ : Fin 148) ⟨101, by decide⟩ _
      (validAt ⟨101, by decide⟩ (listedAt ⟨101, by decide⟩ hj))
      (colE1 ⟨101, by decide⟩ 1 (transLenTr ⟨101, by decide⟩ 1 hp)) T101_101
      hfix101_101 hinj101_101 hcardT101_101
      (fun i => conj_mem_of_fixedPoints _ _ (T101_101 i) (hfix101_101 i) _)
      ⟨101, by decide⟩ ⟨101, by decide⟩ _
      (Q2.validAt ⟨101, by decide⟩ (Q2.listedAt ⟨101, by decide⟩
        (alnCheck_rep ⟨101, by decide⟩ hj hq).1))
      (colE2 ⟨101, by decide⟩ 1 hp) Q2.T101_101_2 Q2.hfix101_101_2 Q2.hinj101_101_2
      Q2.hcardT101_101_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T101_101_2 i) (Q2.hfix101_101_2 i) _)
      colCert_101_101_1.hD ?_).symm
  rw [alnId_101 j hj]


theorem leaf_101_101_2 (hp : 2 < (Q2.transData.getD 101 []).length)
    (j : Nat) (hj : j < (repChars.getD 101 []).length)
    (hq : (normIsRep.getD 101 []).getD j false = true) :
    species (Q2.reps (⟨101, by decide⟩ : Fin 148)) (colE2 ⟨101, by decide⟩ 2 hp)
        (rowE2 (⟨101, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨101, by decide⟩ : Fin 148))
        (colE1 ⟨101, by decide⟩ 2 (transLenTr ⟨101, by decide⟩ 2 hp))
        (rowE1 (⟨101, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨101, by decide⟩ : Fin 148) ⟨101, by decide⟩ _
      (validAt ⟨101, by decide⟩ (listedAt ⟨101, by decide⟩ hj))
      (colE1 ⟨101, by decide⟩ 2 (transLenTr ⟨101, by decide⟩ 2 hp)) T101_101
      hfix101_101 hinj101_101 hcardT101_101
      (fun i => conj_mem_of_fixedPoints _ _ (T101_101 i) (hfix101_101 i) _)
      ⟨101, by decide⟩ ⟨101, by decide⟩ _
      (Q2.validAt ⟨101, by decide⟩ (Q2.listedAt ⟨101, by decide⟩
        (alnCheck_rep ⟨101, by decide⟩ hj hq).1))
      (colE2 ⟨101, by decide⟩ 2 hp) Q2.T101_101_2 Q2.hfix101_101_2 Q2.hinj101_101_2
      Q2.hcardT101_101_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T101_101_2 i) (Q2.hfix101_101_2 i) _)
      colCert_101_101_2.hD ?_).symm
  rw [alnId_101 j hj]


theorem leaf_101_101_3 (hp : 3 < (Q2.transData.getD 101 []).length)
    (j : Nat) (hj : j < (repChars.getD 101 []).length)
    (hq : (normIsRep.getD 101 []).getD j false = true) :
    species (Q2.reps (⟨101, by decide⟩ : Fin 148)) (colE2 ⟨101, by decide⟩ 3 hp)
        (rowE2 (⟨101, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨101, by decide⟩ : Fin 148))
        (colE1 ⟨101, by decide⟩ 3 (transLenTr ⟨101, by decide⟩ 3 hp))
        (rowE1 (⟨101, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨101, by decide⟩ : Fin 148) ⟨101, by decide⟩ _
      (validAt ⟨101, by decide⟩ (listedAt ⟨101, by decide⟩ hj))
      (colE1 ⟨101, by decide⟩ 3 (transLenTr ⟨101, by decide⟩ 3 hp)) T101_101
      hfix101_101 hinj101_101 hcardT101_101
      (fun i => conj_mem_of_fixedPoints _ _ (T101_101 i) (hfix101_101 i) _)
      ⟨101, by decide⟩ ⟨101, by decide⟩ _
      (Q2.validAt ⟨101, by decide⟩ (Q2.listedAt ⟨101, by decide⟩
        (alnCheck_rep ⟨101, by decide⟩ hj hq).1))
      (colE2 ⟨101, by decide⟩ 3 hp) Q2.T101_101_2 Q2.hfix101_101_2 Q2.hinj101_101_2
      Q2.hcardT101_101_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T101_101_2 i) (Q2.hfix101_101_2 i) _)
      colCert_101_101_3.hD ?_).symm
  rw [alnId_101 j hj]


theorem leaf_101_101_4 (hp : 4 < (Q2.transData.getD 101 []).length)
    (j : Nat) (hj : j < (repChars.getD 101 []).length)
    (hq : (normIsRep.getD 101 []).getD j false = true) :
    species (Q2.reps (⟨101, by decide⟩ : Fin 148)) (colE2 ⟨101, by decide⟩ 4 hp)
        (rowE2 (⟨101, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨101, by decide⟩ : Fin 148))
        (colE1 ⟨101, by decide⟩ 4 (transLenTr ⟨101, by decide⟩ 4 hp))
        (rowE1 (⟨101, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨101, by decide⟩ : Fin 148) ⟨101, by decide⟩ _
      (validAt ⟨101, by decide⟩ (listedAt ⟨101, by decide⟩ hj))
      (colE1 ⟨101, by decide⟩ 4 (transLenTr ⟨101, by decide⟩ 4 hp)) T101_101
      hfix101_101 hinj101_101 hcardT101_101
      (fun i => conj_mem_of_fixedPoints _ _ (T101_101 i) (hfix101_101 i) _)
      ⟨101, by decide⟩ ⟨101, by decide⟩ _
      (Q2.validAt ⟨101, by decide⟩ (Q2.listedAt ⟨101, by decide⟩
        (alnCheck_rep ⟨101, by decide⟩ hj hq).1))
      (colE2 ⟨101, by decide⟩ 4 hp) Q2.T101_101_2 Q2.hfix101_101_2 Q2.hinj101_101_2
      Q2.hcardT101_101_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T101_101_2 i) (Q2.hfix101_101_2 i) _)
      colCert_101_101_4.hD ?_).symm
  rw [alnId_101 j hj]


theorem leaf_101_101_5 (hp : 5 < (Q2.transData.getD 101 []).length)
    (j : Nat) (hj : j < (repChars.getD 101 []).length)
    (hq : (normIsRep.getD 101 []).getD j false = true) :
    species (Q2.reps (⟨101, by decide⟩ : Fin 148)) (colE2 ⟨101, by decide⟩ 5 hp)
        (rowE2 (⟨101, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨101, by decide⟩ : Fin 148))
        (colE1 ⟨101, by decide⟩ 5 (transLenTr ⟨101, by decide⟩ 5 hp))
        (rowE1 (⟨101, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨101, by decide⟩ : Fin 148) ⟨101, by decide⟩ _
      (validAt ⟨101, by decide⟩ (listedAt ⟨101, by decide⟩ hj))
      (colE1 ⟨101, by decide⟩ 5 (transLenTr ⟨101, by decide⟩ 5 hp)) T101_101
      hfix101_101 hinj101_101 hcardT101_101
      (fun i => conj_mem_of_fixedPoints _ _ (T101_101 i) (hfix101_101 i) _)
      ⟨101, by decide⟩ ⟨101, by decide⟩ _
      (Q2.validAt ⟨101, by decide⟩ (Q2.listedAt ⟨101, by decide⟩
        (alnCheck_rep ⟨101, by decide⟩ hj hq).1))
      (colE2 ⟨101, by decide⟩ 5 hp) Q2.T101_101_2 Q2.hfix101_101_2 Q2.hinj101_101_2
      Q2.hcardT101_101_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T101_101_2 i) (Q2.hfix101_101_2 i) _)
      colCert_101_101_5.hD ?_).symm
  rw [alnId_101 j hj]


theorem leaf_101_101_10 (hp : 10 < (Q2.transData.getD 101 []).length)
    (j : Nat) (hj : j < (repChars.getD 101 []).length)
    (hq : (normIsRep.getD 101 []).getD j false = true) :
    species (Q2.reps (⟨101, by decide⟩ : Fin 148)) (colE2 ⟨101, by decide⟩ 10 hp)
        (rowE2 (⟨101, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨101, by decide⟩ : Fin 148))
        (colE1 ⟨101, by decide⟩ 10 (transLenTr ⟨101, by decide⟩ 10 hp))
        (rowE1 (⟨101, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨101, by decide⟩ : Fin 148) ⟨101, by decide⟩ _
      (validAt ⟨101, by decide⟩ (listedAt ⟨101, by decide⟩ hj))
      (colE1 ⟨101, by decide⟩ 10 (transLenTr ⟨101, by decide⟩ 10 hp)) T101_101
      hfix101_101 hinj101_101 hcardT101_101
      (fun i => conj_mem_of_fixedPoints _ _ (T101_101 i) (hfix101_101 i) _)
      ⟨101, by decide⟩ ⟨101, by decide⟩ _
      (Q2.validAt ⟨101, by decide⟩ (Q2.listedAt ⟨101, by decide⟩
        (alnCheck_rep ⟨101, by decide⟩ hj hq).1))
      (colE2 ⟨101, by decide⟩ 10 hp) Q2.T101_101_2 Q2.hfix101_101_2 Q2.hinj101_101_2
      Q2.hcardT101_101_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T101_101_2 i) (Q2.hfix101_101_2 i) _)
      colCert_101_101_10.hD ?_).symm
  rw [alnId_101 j hj]


theorem leaf_101_101_15 (hp : 15 < (Q2.transData.getD 101 []).length)
    (j : Nat) (hj : j < (repChars.getD 101 []).length)
    (hq : (normIsRep.getD 101 []).getD j false = true) :
    species (Q2.reps (⟨101, by decide⟩ : Fin 148)) (colE2 ⟨101, by decide⟩ 15 hp)
        (rowE2 (⟨101, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨101, by decide⟩ : Fin 148))
        (colE1 ⟨101, by decide⟩ 15 (transLenTr ⟨101, by decide⟩ 15 hp))
        (rowE1 (⟨101, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨101, by decide⟩ : Fin 148) ⟨101, by decide⟩ _
      (validAt ⟨101, by decide⟩ (listedAt ⟨101, by decide⟩ hj))
      (colE1 ⟨101, by decide⟩ 15 (transLenTr ⟨101, by decide⟩ 15 hp)) T101_101
      hfix101_101 hinj101_101 hcardT101_101
      (fun i => conj_mem_of_fixedPoints _ _ (T101_101 i) (hfix101_101 i) _)
      ⟨101, by decide⟩ ⟨101, by decide⟩ _
      (Q2.validAt ⟨101, by decide⟩ (Q2.listedAt ⟨101, by decide⟩
        (alnCheck_rep ⟨101, by decide⟩ hj hq).1))
      (colE2 ⟨101, by decide⟩ 15 hp) Q2.T101_101_2 Q2.hfix101_101_2 Q2.hinj101_101_2
      Q2.hcardT101_101_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T101_101_2 i) (Q2.hfix101_101_2 i) _)
      colCert_101_101_15.hD ?_).symm
  rw [alnId_101 j hj]


theorem leaf_101_101_20 (hp : 20 < (Q2.transData.getD 101 []).length)
    (j : Nat) (hj : j < (repChars.getD 101 []).length)
    (hq : (normIsRep.getD 101 []).getD j false = true) :
    species (Q2.reps (⟨101, by decide⟩ : Fin 148)) (colE2 ⟨101, by decide⟩ 20 hp)
        (rowE2 (⟨101, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨101, by decide⟩ : Fin 148))
        (colE1 ⟨101, by decide⟩ 20 (transLenTr ⟨101, by decide⟩ 20 hp))
        (rowE1 (⟨101, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨101, by decide⟩ : Fin 148) ⟨101, by decide⟩ _
      (validAt ⟨101, by decide⟩ (listedAt ⟨101, by decide⟩ hj))
      (colE1 ⟨101, by decide⟩ 20 (transLenTr ⟨101, by decide⟩ 20 hp)) T101_101
      hfix101_101 hinj101_101 hcardT101_101
      (fun i => conj_mem_of_fixedPoints _ _ (T101_101 i) (hfix101_101 i) _)
      ⟨101, by decide⟩ ⟨101, by decide⟩ _
      (Q2.validAt ⟨101, by decide⟩ (Q2.listedAt ⟨101, by decide⟩
        (alnCheck_rep ⟨101, by decide⟩ hj hq).1))
      (colE2 ⟨101, by decide⟩ 20 hp) Q2.T101_101_2 Q2.hfix101_101_2 Q2.hinj101_101_2
      Q2.hcardT101_101_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T101_101_2 i) (Q2.hfix101_101_2 i) _)
      colCert_101_101_20.hD ?_).symm
  rw [alnId_101 j hj]


theorem leaf_102_10_0 (hp : 0 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 102 []).length)
    (hq : (normIsRep.getD 102 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 0 hp)
        (rowE2 (⟨102, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 0 (transLenTr ⟨10, by decide⟩ 0 hp))
        (rowE1 (⟨102, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨102, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨102, by decide⟩ (listedAt ⟨102, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 0 (transLenTr ⟨10, by decide⟩ 0 hp)) T102_10
      hfix102_10 hinj102_10 hcardT102_10
      (fun i => conj_mem_of_fixedPoints _ _ (T102_10 i) (hfix102_10 i) _)
      ⟨102, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨102, by decide⟩ (Q2.listedAt ⟨102, by decide⟩
        (alnCheck_rep ⟨102, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 0 hp) Q2.T102_10_2 Q2.hfix102_10_2 Q2.hinj102_10_2
      Q2.hcardT102_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T102_10_2 i) (Q2.hfix102_10_2 i) _)
      colCert_102_10_0.hD ?_).symm
  rw [alnId_102 j hj]


theorem leaf_102_10_1 (hp : 1 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 102 []).length)
    (hq : (normIsRep.getD 102 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 1 hp)
        (rowE2 (⟨102, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 1 (transLenTr ⟨10, by decide⟩ 1 hp))
        (rowE1 (⟨102, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨102, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨102, by decide⟩ (listedAt ⟨102, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 1 (transLenTr ⟨10, by decide⟩ 1 hp)) T102_10
      hfix102_10 hinj102_10 hcardT102_10
      (fun i => conj_mem_of_fixedPoints _ _ (T102_10 i) (hfix102_10 i) _)
      ⟨102, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨102, by decide⟩ (Q2.listedAt ⟨102, by decide⟩
        (alnCheck_rep ⟨102, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 1 hp) Q2.T102_10_2 Q2.hfix102_10_2 Q2.hinj102_10_2
      Q2.hcardT102_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T102_10_2 i) (Q2.hfix102_10_2 i) _)
      colCert_102_10_1.hD ?_).symm
  rw [alnId_102 j hj]


theorem leaf_102_10_2 (hp : 2 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 102 []).length)
    (hq : (normIsRep.getD 102 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 2 hp)
        (rowE2 (⟨102, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 2 (transLenTr ⟨10, by decide⟩ 2 hp))
        (rowE1 (⟨102, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨102, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨102, by decide⟩ (listedAt ⟨102, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 2 (transLenTr ⟨10, by decide⟩ 2 hp)) T102_10
      hfix102_10 hinj102_10 hcardT102_10
      (fun i => conj_mem_of_fixedPoints _ _ (T102_10 i) (hfix102_10 i) _)
      ⟨102, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨102, by decide⟩ (Q2.listedAt ⟨102, by decide⟩
        (alnCheck_rep ⟨102, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 2 hp) Q2.T102_10_2 Q2.hfix102_10_2 Q2.hinj102_10_2
      Q2.hcardT102_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T102_10_2 i) (Q2.hfix102_10_2 i) _)
      colCert_102_10_2.hD ?_).symm
  rw [alnId_102 j hj]


theorem leaf_102_10_3 (hp : 3 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 102 []).length)
    (hq : (normIsRep.getD 102 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 3 hp)
        (rowE2 (⟨102, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 3 (transLenTr ⟨10, by decide⟩ 3 hp))
        (rowE1 (⟨102, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨102, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨102, by decide⟩ (listedAt ⟨102, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 3 (transLenTr ⟨10, by decide⟩ 3 hp)) T102_10
      hfix102_10 hinj102_10 hcardT102_10
      (fun i => conj_mem_of_fixedPoints _ _ (T102_10 i) (hfix102_10 i) _)
      ⟨102, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨102, by decide⟩ (Q2.listedAt ⟨102, by decide⟩
        (alnCheck_rep ⟨102, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 3 hp) Q2.T102_10_2 Q2.hfix102_10_2 Q2.hinj102_10_2
      Q2.hcardT102_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T102_10_2 i) (Q2.hfix102_10_2 i) _)
      colCert_102_10_3.hD ?_).symm
  rw [alnId_102 j hj]


theorem leaf_102_10_4 (hp : 4 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 102 []).length)
    (hq : (normIsRep.getD 102 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 4 hp)
        (rowE2 (⟨102, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 4 (transLenTr ⟨10, by decide⟩ 4 hp))
        (rowE1 (⟨102, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨102, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨102, by decide⟩ (listedAt ⟨102, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 4 (transLenTr ⟨10, by decide⟩ 4 hp)) T102_10
      hfix102_10 hinj102_10 hcardT102_10
      (fun i => conj_mem_of_fixedPoints _ _ (T102_10 i) (hfix102_10 i) _)
      ⟨102, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨102, by decide⟩ (Q2.listedAt ⟨102, by decide⟩
        (alnCheck_rep ⟨102, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 4 hp) Q2.T102_10_2 Q2.hfix102_10_2 Q2.hinj102_10_2
      Q2.hcardT102_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T102_10_2 i) (Q2.hfix102_10_2 i) _)
      colCert_102_10_4.hD ?_).symm
  rw [alnId_102 j hj]


theorem leaf_102_12_0 (hp : 0 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 102 []).length)
    (hq : (normIsRep.getD 102 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 0 hp)
        (rowE2 (⟨102, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp))
        (rowE1 (⟨102, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨102, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨102, by decide⟩ (listedAt ⟨102, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp)) T102_12
      hfix102_12 hinj102_12 hcardT102_12
      (fun i => conj_mem_of_fixedPoints _ _ (T102_12 i) (hfix102_12 i) _)
      ⟨102, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨102, by decide⟩ (Q2.listedAt ⟨102, by decide⟩
        (alnCheck_rep ⟨102, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 0 hp) Q2.T102_12_2 Q2.hfix102_12_2 Q2.hinj102_12_2
      Q2.hcardT102_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T102_12_2 i) (Q2.hfix102_12_2 i) _)
      colCert_102_12_0.hD ?_).symm
  rw [alnId_102 j hj]


theorem leaf_102_12_1 (hp : 1 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 102 []).length)
    (hq : (normIsRep.getD 102 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 1 hp)
        (rowE2 (⟨102, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp))
        (rowE1 (⟨102, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨102, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨102, by decide⟩ (listedAt ⟨102, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp)) T102_12
      hfix102_12 hinj102_12 hcardT102_12
      (fun i => conj_mem_of_fixedPoints _ _ (T102_12 i) (hfix102_12 i) _)
      ⟨102, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨102, by decide⟩ (Q2.listedAt ⟨102, by decide⟩
        (alnCheck_rep ⟨102, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 1 hp) Q2.T102_12_2 Q2.hfix102_12_2 Q2.hinj102_12_2
      Q2.hcardT102_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T102_12_2 i) (Q2.hfix102_12_2 i) _)
      colCert_102_12_1.hD ?_).symm
  rw [alnId_102 j hj]


theorem leaf_102_12_2 (hp : 2 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 102 []).length)
    (hq : (normIsRep.getD 102 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 2 hp)
        (rowE2 (⟨102, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp))
        (rowE1 (⟨102, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨102, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨102, by decide⟩ (listedAt ⟨102, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp)) T102_12
      hfix102_12 hinj102_12 hcardT102_12
      (fun i => conj_mem_of_fixedPoints _ _ (T102_12 i) (hfix102_12 i) _)
      ⟨102, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨102, by decide⟩ (Q2.listedAt ⟨102, by decide⟩
        (alnCheck_rep ⟨102, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 2 hp) Q2.T102_12_2 Q2.hfix102_12_2 Q2.hinj102_12_2
      Q2.hcardT102_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T102_12_2 i) (Q2.hfix102_12_2 i) _)
      colCert_102_12_2.hD ?_).symm
  rw [alnId_102 j hj]


theorem leaf_102_12_3 (hp : 3 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 102 []).length)
    (hq : (normIsRep.getD 102 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 3 hp)
        (rowE2 (⟨102, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp))
        (rowE1 (⟨102, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨102, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨102, by decide⟩ (listedAt ⟨102, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp)) T102_12
      hfix102_12 hinj102_12 hcardT102_12
      (fun i => conj_mem_of_fixedPoints _ _ (T102_12 i) (hfix102_12 i) _)
      ⟨102, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨102, by decide⟩ (Q2.listedAt ⟨102, by decide⟩
        (alnCheck_rep ⟨102, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 3 hp) Q2.T102_12_2 Q2.hfix102_12_2 Q2.hinj102_12_2
      Q2.hcardT102_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T102_12_2 i) (Q2.hfix102_12_2 i) _)
      colCert_102_12_3.hD ?_).symm
  rw [alnId_102 j hj]


theorem leaf_102_12_4 (hp : 4 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 102 []).length)
    (hq : (normIsRep.getD 102 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 4 hp)
        (rowE2 (⟨102, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp))
        (rowE1 (⟨102, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨102, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨102, by decide⟩ (listedAt ⟨102, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp)) T102_12
      hfix102_12 hinj102_12 hcardT102_12
      (fun i => conj_mem_of_fixedPoints _ _ (T102_12 i) (hfix102_12 i) _)
      ⟨102, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨102, by decide⟩ (Q2.listedAt ⟨102, by decide⟩
        (alnCheck_rep ⟨102, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 4 hp) Q2.T102_12_2 Q2.hfix102_12_2 Q2.hinj102_12_2
      Q2.hcardT102_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T102_12_2 i) (Q2.hfix102_12_2 i) _)
      colCert_102_12_4.hD ?_).symm
  rw [alnId_102 j hj]


theorem leaf_102_40_0 (hp : 0 < (Q2.transData.getD 40 []).length)
    (j : Nat) (hj : j < (repChars.getD 102 []).length)
    (hq : (normIsRep.getD 102 []).getD j false = true) :
    species (Q2.reps (⟨40, by decide⟩ : Fin 148)) (colE2 ⟨40, by decide⟩ 0 hp)
        (rowE2 (⟨102, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨40, by decide⟩ : Fin 148))
        (colE1 ⟨40, by decide⟩ 0 (transLenTr ⟨40, by decide⟩ 0 hp))
        (rowE1 (⟨102, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨102, by decide⟩ : Fin 148) ⟨40, by decide⟩ _
      (validAt ⟨102, by decide⟩ (listedAt ⟨102, by decide⟩ hj))
      (colE1 ⟨40, by decide⟩ 0 (transLenTr ⟨40, by decide⟩ 0 hp)) T102_40
      hfix102_40 hinj102_40 hcardT102_40
      (fun i => conj_mem_of_fixedPoints _ _ (T102_40 i) (hfix102_40 i) _)
      ⟨102, by decide⟩ ⟨40, by decide⟩ _
      (Q2.validAt ⟨102, by decide⟩ (Q2.listedAt ⟨102, by decide⟩
        (alnCheck_rep ⟨102, by decide⟩ hj hq).1))
      (colE2 ⟨40, by decide⟩ 0 hp) Q2.T102_40_2 Q2.hfix102_40_2 Q2.hinj102_40_2
      Q2.hcardT102_40_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T102_40_2 i) (Q2.hfix102_40_2 i) _)
      colCert_102_40_0.hD ?_).symm
  rw [alnId_102 j hj]


theorem leaf_102_40_1 (hp : 1 < (Q2.transData.getD 40 []).length)
    (j : Nat) (hj : j < (repChars.getD 102 []).length)
    (hq : (normIsRep.getD 102 []).getD j false = true) :
    species (Q2.reps (⟨40, by decide⟩ : Fin 148)) (colE2 ⟨40, by decide⟩ 1 hp)
        (rowE2 (⟨102, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨40, by decide⟩ : Fin 148))
        (colE1 ⟨40, by decide⟩ 1 (transLenTr ⟨40, by decide⟩ 1 hp))
        (rowE1 (⟨102, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨102, by decide⟩ : Fin 148) ⟨40, by decide⟩ _
      (validAt ⟨102, by decide⟩ (listedAt ⟨102, by decide⟩ hj))
      (colE1 ⟨40, by decide⟩ 1 (transLenTr ⟨40, by decide⟩ 1 hp)) T102_40
      hfix102_40 hinj102_40 hcardT102_40
      (fun i => conj_mem_of_fixedPoints _ _ (T102_40 i) (hfix102_40 i) _)
      ⟨102, by decide⟩ ⟨40, by decide⟩ _
      (Q2.validAt ⟨102, by decide⟩ (Q2.listedAt ⟨102, by decide⟩
        (alnCheck_rep ⟨102, by decide⟩ hj hq).1))
      (colE2 ⟨40, by decide⟩ 1 hp) Q2.T102_40_2 Q2.hfix102_40_2 Q2.hinj102_40_2
      Q2.hcardT102_40_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T102_40_2 i) (Q2.hfix102_40_2 i) _)
      colCert_102_40_1.hD ?_).symm
  rw [alnId_102 j hj]


theorem leaf_102_40_2 (hp : 2 < (Q2.transData.getD 40 []).length)
    (j : Nat) (hj : j < (repChars.getD 102 []).length)
    (hq : (normIsRep.getD 102 []).getD j false = true) :
    species (Q2.reps (⟨40, by decide⟩ : Fin 148)) (colE2 ⟨40, by decide⟩ 2 hp)
        (rowE2 (⟨102, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨40, by decide⟩ : Fin 148))
        (colE1 ⟨40, by decide⟩ 2 (transLenTr ⟨40, by decide⟩ 2 hp))
        (rowE1 (⟨102, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨102, by decide⟩ : Fin 148) ⟨40, by decide⟩ _
      (validAt ⟨102, by decide⟩ (listedAt ⟨102, by decide⟩ hj))
      (colE1 ⟨40, by decide⟩ 2 (transLenTr ⟨40, by decide⟩ 2 hp)) T102_40
      hfix102_40 hinj102_40 hcardT102_40
      (fun i => conj_mem_of_fixedPoints _ _ (T102_40 i) (hfix102_40 i) _)
      ⟨102, by decide⟩ ⟨40, by decide⟩ _
      (Q2.validAt ⟨102, by decide⟩ (Q2.listedAt ⟨102, by decide⟩
        (alnCheck_rep ⟨102, by decide⟩ hj hq).1))
      (colE2 ⟨40, by decide⟩ 2 hp) Q2.T102_40_2 Q2.hfix102_40_2 Q2.hinj102_40_2
      Q2.hcardT102_40_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T102_40_2 i) (Q2.hfix102_40_2 i) _)
      colCert_102_40_2.hD ?_).symm
  rw [alnId_102 j hj]


theorem leaf_102_40_3 (hp : 3 < (Q2.transData.getD 40 []).length)
    (j : Nat) (hj : j < (repChars.getD 102 []).length)
    (hq : (normIsRep.getD 102 []).getD j false = true) :
    species (Q2.reps (⟨40, by decide⟩ : Fin 148)) (colE2 ⟨40, by decide⟩ 3 hp)
        (rowE2 (⟨102, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨40, by decide⟩ : Fin 148))
        (colE1 ⟨40, by decide⟩ 3 (transLenTr ⟨40, by decide⟩ 3 hp))
        (rowE1 (⟨102, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨102, by decide⟩ : Fin 148) ⟨40, by decide⟩ _
      (validAt ⟨102, by decide⟩ (listedAt ⟨102, by decide⟩ hj))
      (colE1 ⟨40, by decide⟩ 3 (transLenTr ⟨40, by decide⟩ 3 hp)) T102_40
      hfix102_40 hinj102_40 hcardT102_40
      (fun i => conj_mem_of_fixedPoints _ _ (T102_40 i) (hfix102_40 i) _)
      ⟨102, by decide⟩ ⟨40, by decide⟩ _
      (Q2.validAt ⟨102, by decide⟩ (Q2.listedAt ⟨102, by decide⟩
        (alnCheck_rep ⟨102, by decide⟩ hj hq).1))
      (colE2 ⟨40, by decide⟩ 3 hp) Q2.T102_40_2 Q2.hfix102_40_2 Q2.hinj102_40_2
      Q2.hcardT102_40_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T102_40_2 i) (Q2.hfix102_40_2 i) _)
      colCert_102_40_3.hD ?_).symm
  rw [alnId_102 j hj]


end LeanDring.P5Presentation
