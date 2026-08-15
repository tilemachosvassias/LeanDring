/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Data.ColRestCheap.C151
import LeanDring.P5.Data.ColRestCheap.C152
import LeanDring.P5.Data.ColRestCheap.C153
import LeanDring.P5.Data.ColRestCheap.C154
import LeanDring.P5.Data.ColRestCheap.C155
import LeanDring.P5.Data.EntryK.C015
import LeanDring.P5.Data.EntryK.C016
import LeanDring.P5.Certificate.RingIsomorphism.MatchCore
import LeanDring.P5.Data.SpeciesAlign.C011
import LeanDring.P5.Data.SpeciesAlign.C012
import LeanDring.P5.Data.SpeciesAlign.C013
import LeanDring.P5.Data.SpeciesAlign.C014

/-! # Stage-5 leaves, chunk 7 (auto-emitted).  -/

namespace LeanDring.P5Presentation

open MulAction Finset LeanDring.DRing LeanDring.MonGSet

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.style.longLine false

theorem leaf_64_8_0 (hp : 0 < (Q2.transData.getD 8 []).length)
    (j : Nat) (hj : j < (repChars.getD 64 []).length)
    (hq : (normIsRep.getD 64 []).getD j false = true) :
    species (Q2.reps (⟨8, by decide⟩ : Fin 148)) (colE2 ⟨8, by decide⟩ 0 hp)
        (rowE2 (⟨64, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨8, by decide⟩ : Fin 148))
        (colE1 ⟨8, by decide⟩ 0 (transLenTr ⟨8, by decide⟩ 0 hp))
        (rowE1 (⟨64, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨64, by decide⟩ : Fin 148) ⟨8, by decide⟩ _
      (validAt ⟨64, by decide⟩ (listedAt ⟨64, by decide⟩ hj))
      (colE1 ⟨8, by decide⟩ 0 (transLenTr ⟨8, by decide⟩ 0 hp)) T64_8
      hfix64_8 hinj64_8 hcardT64_8
      (fun i => conj_mem_of_fixedPoints _ _ (T64_8 i) (hfix64_8 i) _)
      ⟨64, by decide⟩ ⟨8, by decide⟩ _
      (Q2.validAt ⟨64, by decide⟩ (Q2.listedAt ⟨64, by decide⟩
        (alnCheck_rep ⟨64, by decide⟩ hj hq).1))
      (colE2 ⟨8, by decide⟩ 0 hp) Q2.T64_8_2 Q2.hfix64_8_2 Q2.hinj64_8_2
      Q2.hcardT64_8_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T64_8_2 i) (Q2.hfix64_8_2 i) _)
      ?_).symm
  rw [show colData1 (⟨64, by decide⟩ : Fin 148)
        ((colE1 ⟨8, by decide⟩ 0 (transLenTr ⟨8, by decide⟩ 0 hp) : ↥(reps ⟨8, by decide⟩)) : Coordinate 1)
        T64_8 = colFn colCert_64_8_0.D (m := 25) from colCert_64_8_0.bind1,
    show colData2 (⟨64, by decide⟩ : Fin 148)
        ((colE2 ⟨8, by decide⟩ 0 hp : ↥(Q2.reps ⟨8, by decide⟩)) : Coordinate 2)
        Q2.T64_8_2 = colFn colCert_64_8_0.D (m := 25) from colCert_64_8_0.bind2]
  exact alnAll_64_8_0 j hj hq

theorem leaf_64_8_1 (hp : 1 < (Q2.transData.getD 8 []).length)
    (j : Nat) (hj : j < (repChars.getD 64 []).length)
    (hq : (normIsRep.getD 64 []).getD j false = true) :
    species (Q2.reps (⟨8, by decide⟩ : Fin 148)) (colE2 ⟨8, by decide⟩ 1 hp)
        (rowE2 (⟨64, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨8, by decide⟩ : Fin 148))
        (colE1 ⟨8, by decide⟩ 1 (transLenTr ⟨8, by decide⟩ 1 hp))
        (rowE1 (⟨64, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨64, by decide⟩ : Fin 148) ⟨8, by decide⟩ _
      (validAt ⟨64, by decide⟩ (listedAt ⟨64, by decide⟩ hj))
      (colE1 ⟨8, by decide⟩ 1 (transLenTr ⟨8, by decide⟩ 1 hp)) T64_8
      hfix64_8 hinj64_8 hcardT64_8
      (fun i => conj_mem_of_fixedPoints _ _ (T64_8 i) (hfix64_8 i) _)
      ⟨64, by decide⟩ ⟨8, by decide⟩ _
      (Q2.validAt ⟨64, by decide⟩ (Q2.listedAt ⟨64, by decide⟩
        (alnCheck_rep ⟨64, by decide⟩ hj hq).1))
      (colE2 ⟨8, by decide⟩ 1 hp) Q2.T64_8_2 Q2.hfix64_8_2 Q2.hinj64_8_2
      Q2.hcardT64_8_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T64_8_2 i) (Q2.hfix64_8_2 i) _)
      ?_).symm
  rw [show colData1 (⟨64, by decide⟩ : Fin 148)
        ((colE1 ⟨8, by decide⟩ 1 (transLenTr ⟨8, by decide⟩ 1 hp) : ↥(reps ⟨8, by decide⟩)) : Coordinate 1)
        T64_8 = colFn colCert_64_8_1.D (m := 25) from colCert_64_8_1.bind1,
    show colData2 (⟨64, by decide⟩ : Fin 148)
        ((colE2 ⟨8, by decide⟩ 1 hp : ↥(Q2.reps ⟨8, by decide⟩)) : Coordinate 2)
        Q2.T64_8_2 = colFn colCert_64_8_1.D (m := 25) from colCert_64_8_1.bind2]
  exact alnAll_64_8_1 j hj hq

theorem leaf_64_8_2 (hp : 2 < (Q2.transData.getD 8 []).length)
    (j : Nat) (hj : j < (repChars.getD 64 []).length)
    (hq : (normIsRep.getD 64 []).getD j false = true) :
    species (Q2.reps (⟨8, by decide⟩ : Fin 148)) (colE2 ⟨8, by decide⟩ 2 hp)
        (rowE2 (⟨64, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨8, by decide⟩ : Fin 148))
        (colE1 ⟨8, by decide⟩ 2 (transLenTr ⟨8, by decide⟩ 2 hp))
        (rowE1 (⟨64, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨64, by decide⟩ : Fin 148) ⟨8, by decide⟩ _
      (validAt ⟨64, by decide⟩ (listedAt ⟨64, by decide⟩ hj))
      (colE1 ⟨8, by decide⟩ 2 (transLenTr ⟨8, by decide⟩ 2 hp)) T64_8
      hfix64_8 hinj64_8 hcardT64_8
      (fun i => conj_mem_of_fixedPoints _ _ (T64_8 i) (hfix64_8 i) _)
      ⟨64, by decide⟩ ⟨8, by decide⟩ _
      (Q2.validAt ⟨64, by decide⟩ (Q2.listedAt ⟨64, by decide⟩
        (alnCheck_rep ⟨64, by decide⟩ hj hq).1))
      (colE2 ⟨8, by decide⟩ 2 hp) Q2.T64_8_2 Q2.hfix64_8_2 Q2.hinj64_8_2
      Q2.hcardT64_8_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T64_8_2 i) (Q2.hfix64_8_2 i) _)
      ?_).symm
  rw [show colData1 (⟨64, by decide⟩ : Fin 148)
        ((colE1 ⟨8, by decide⟩ 2 (transLenTr ⟨8, by decide⟩ 2 hp) : ↥(reps ⟨8, by decide⟩)) : Coordinate 1)
        T64_8 = colFn colCert_64_8_2.D (m := 25) from colCert_64_8_2.bind1,
    show colData2 (⟨64, by decide⟩ : Fin 148)
        ((colE2 ⟨8, by decide⟩ 2 hp : ↥(Q2.reps ⟨8, by decide⟩)) : Coordinate 2)
        Q2.T64_8_2 = colFn colCert_64_8_2.D (m := 25) from colCert_64_8_2.bind2]
  exact alnAll_64_8_2 j hj hq

theorem leaf_64_8_3 (hp : 3 < (Q2.transData.getD 8 []).length)
    (j : Nat) (hj : j < (repChars.getD 64 []).length)
    (hq : (normIsRep.getD 64 []).getD j false = true) :
    species (Q2.reps (⟨8, by decide⟩ : Fin 148)) (colE2 ⟨8, by decide⟩ 3 hp)
        (rowE2 (⟨64, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨8, by decide⟩ : Fin 148))
        (colE1 ⟨8, by decide⟩ 3 (transLenTr ⟨8, by decide⟩ 3 hp))
        (rowE1 (⟨64, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨64, by decide⟩ : Fin 148) ⟨8, by decide⟩ _
      (validAt ⟨64, by decide⟩ (listedAt ⟨64, by decide⟩ hj))
      (colE1 ⟨8, by decide⟩ 3 (transLenTr ⟨8, by decide⟩ 3 hp)) T64_8
      hfix64_8 hinj64_8 hcardT64_8
      (fun i => conj_mem_of_fixedPoints _ _ (T64_8 i) (hfix64_8 i) _)
      ⟨64, by decide⟩ ⟨8, by decide⟩ _
      (Q2.validAt ⟨64, by decide⟩ (Q2.listedAt ⟨64, by decide⟩
        (alnCheck_rep ⟨64, by decide⟩ hj hq).1))
      (colE2 ⟨8, by decide⟩ 3 hp) Q2.T64_8_2 Q2.hfix64_8_2 Q2.hinj64_8_2
      Q2.hcardT64_8_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T64_8_2 i) (Q2.hfix64_8_2 i) _)
      ?_).symm
  rw [show colData1 (⟨64, by decide⟩ : Fin 148)
        ((colE1 ⟨8, by decide⟩ 3 (transLenTr ⟨8, by decide⟩ 3 hp) : ↥(reps ⟨8, by decide⟩)) : Coordinate 1)
        T64_8 = colFn colCert_64_8_3.D (m := 25) from colCert_64_8_3.bind1,
    show colData2 (⟨64, by decide⟩ : Fin 148)
        ((colE2 ⟨8, by decide⟩ 3 hp : ↥(Q2.reps ⟨8, by decide⟩)) : Coordinate 2)
        Q2.T64_8_2 = colFn colCert_64_8_3.D (m := 25) from colCert_64_8_3.bind2]
  exact alnAll_64_8_3 j hj hq

theorem leaf_64_8_4 (hp : 4 < (Q2.transData.getD 8 []).length)
    (j : Nat) (hj : j < (repChars.getD 64 []).length)
    (hq : (normIsRep.getD 64 []).getD j false = true) :
    species (Q2.reps (⟨8, by decide⟩ : Fin 148)) (colE2 ⟨8, by decide⟩ 4 hp)
        (rowE2 (⟨64, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨8, by decide⟩ : Fin 148))
        (colE1 ⟨8, by decide⟩ 4 (transLenTr ⟨8, by decide⟩ 4 hp))
        (rowE1 (⟨64, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨64, by decide⟩ : Fin 148) ⟨8, by decide⟩ _
      (validAt ⟨64, by decide⟩ (listedAt ⟨64, by decide⟩ hj))
      (colE1 ⟨8, by decide⟩ 4 (transLenTr ⟨8, by decide⟩ 4 hp)) T64_8
      hfix64_8 hinj64_8 hcardT64_8
      (fun i => conj_mem_of_fixedPoints _ _ (T64_8 i) (hfix64_8 i) _)
      ⟨64, by decide⟩ ⟨8, by decide⟩ _
      (Q2.validAt ⟨64, by decide⟩ (Q2.listedAt ⟨64, by decide⟩
        (alnCheck_rep ⟨64, by decide⟩ hj hq).1))
      (colE2 ⟨8, by decide⟩ 4 hp) Q2.T64_8_2 Q2.hfix64_8_2 Q2.hinj64_8_2
      Q2.hcardT64_8_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T64_8_2 i) (Q2.hfix64_8_2 i) _)
      ?_).symm
  rw [show colData1 (⟨64, by decide⟩ : Fin 148)
        ((colE1 ⟨8, by decide⟩ 4 (transLenTr ⟨8, by decide⟩ 4 hp) : ↥(reps ⟨8, by decide⟩)) : Coordinate 1)
        T64_8 = colFn colCert_64_8_4.D (m := 25) from colCert_64_8_4.bind1,
    show colData2 (⟨64, by decide⟩ : Fin 148)
        ((colE2 ⟨8, by decide⟩ 4 hp : ↥(Q2.reps ⟨8, by decide⟩)) : Coordinate 2)
        Q2.T64_8_2 = colFn colCert_64_8_4.D (m := 25) from colCert_64_8_4.bind2]
  exact alnAll_64_8_4 j hj hq

theorem leaf_64_12_0 (hp : 0 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 64 []).length)
    (hq : (normIsRep.getD 64 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 0 hp)
        (rowE2 (⟨64, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp))
        (rowE1 (⟨64, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨64, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨64, by decide⟩ (listedAt ⟨64, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp)) T64_12
      hfix64_12 hinj64_12 hcardT64_12
      (fun i => conj_mem_of_fixedPoints _ _ (T64_12 i) (hfix64_12 i) _)
      ⟨64, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨64, by decide⟩ (Q2.listedAt ⟨64, by decide⟩
        (alnCheck_rep ⟨64, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 0 hp) Q2.T64_12_2 Q2.hfix64_12_2 Q2.hinj64_12_2
      Q2.hcardT64_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T64_12_2 i) (Q2.hfix64_12_2 i) _)
      ?_).symm
  rw [show colData1 (⟨64, by decide⟩ : Fin 148)
        ((colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp) : ↥(reps ⟨12, by decide⟩)) : Coordinate 1)
        T64_12 = colFn colCert_64_12_0.D (m := 25) from colCert_64_12_0.bind1,
    show colData2 (⟨64, by decide⟩ : Fin 148)
        ((colE2 ⟨12, by decide⟩ 0 hp : ↥(Q2.reps ⟨12, by decide⟩)) : Coordinate 2)
        Q2.T64_12_2 = colFn colCert_64_12_0.D (m := 25) from colCert_64_12_0.bind2]
  exact alnAll_64_12_0 j hj hq

theorem leaf_64_12_1 (hp : 1 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 64 []).length)
    (hq : (normIsRep.getD 64 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 1 hp)
        (rowE2 (⟨64, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp))
        (rowE1 (⟨64, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨64, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨64, by decide⟩ (listedAt ⟨64, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp)) T64_12
      hfix64_12 hinj64_12 hcardT64_12
      (fun i => conj_mem_of_fixedPoints _ _ (T64_12 i) (hfix64_12 i) _)
      ⟨64, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨64, by decide⟩ (Q2.listedAt ⟨64, by decide⟩
        (alnCheck_rep ⟨64, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 1 hp) Q2.T64_12_2 Q2.hfix64_12_2 Q2.hinj64_12_2
      Q2.hcardT64_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T64_12_2 i) (Q2.hfix64_12_2 i) _)
      ?_).symm
  rw [show colData1 (⟨64, by decide⟩ : Fin 148)
        ((colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp) : ↥(reps ⟨12, by decide⟩)) : Coordinate 1)
        T64_12 = colFn colCert_64_12_1.D (m := 25) from colCert_64_12_1.bind1,
    show colData2 (⟨64, by decide⟩ : Fin 148)
        ((colE2 ⟨12, by decide⟩ 1 hp : ↥(Q2.reps ⟨12, by decide⟩)) : Coordinate 2)
        Q2.T64_12_2 = colFn colCert_64_12_1.D (m := 25) from colCert_64_12_1.bind2]
  exact alnAll_64_12_1 j hj hq

theorem leaf_64_12_2 (hp : 2 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 64 []).length)
    (hq : (normIsRep.getD 64 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 2 hp)
        (rowE2 (⟨64, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp))
        (rowE1 (⟨64, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨64, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨64, by decide⟩ (listedAt ⟨64, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp)) T64_12
      hfix64_12 hinj64_12 hcardT64_12
      (fun i => conj_mem_of_fixedPoints _ _ (T64_12 i) (hfix64_12 i) _)
      ⟨64, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨64, by decide⟩ (Q2.listedAt ⟨64, by decide⟩
        (alnCheck_rep ⟨64, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 2 hp) Q2.T64_12_2 Q2.hfix64_12_2 Q2.hinj64_12_2
      Q2.hcardT64_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T64_12_2 i) (Q2.hfix64_12_2 i) _)
      ?_).symm
  rw [show colData1 (⟨64, by decide⟩ : Fin 148)
        ((colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp) : ↥(reps ⟨12, by decide⟩)) : Coordinate 1)
        T64_12 = colFn colCert_64_12_2.D (m := 25) from colCert_64_12_2.bind1,
    show colData2 (⟨64, by decide⟩ : Fin 148)
        ((colE2 ⟨12, by decide⟩ 2 hp : ↥(Q2.reps ⟨12, by decide⟩)) : Coordinate 2)
        Q2.T64_12_2 = colFn colCert_64_12_2.D (m := 25) from colCert_64_12_2.bind2]
  exact alnAll_64_12_2 j hj hq

theorem leaf_64_12_3 (hp : 3 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 64 []).length)
    (hq : (normIsRep.getD 64 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 3 hp)
        (rowE2 (⟨64, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp))
        (rowE1 (⟨64, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨64, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨64, by decide⟩ (listedAt ⟨64, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp)) T64_12
      hfix64_12 hinj64_12 hcardT64_12
      (fun i => conj_mem_of_fixedPoints _ _ (T64_12 i) (hfix64_12 i) _)
      ⟨64, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨64, by decide⟩ (Q2.listedAt ⟨64, by decide⟩
        (alnCheck_rep ⟨64, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 3 hp) Q2.T64_12_2 Q2.hfix64_12_2 Q2.hinj64_12_2
      Q2.hcardT64_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T64_12_2 i) (Q2.hfix64_12_2 i) _)
      ?_).symm
  rw [show colData1 (⟨64, by decide⟩ : Fin 148)
        ((colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp) : ↥(reps ⟨12, by decide⟩)) : Coordinate 1)
        T64_12 = colFn colCert_64_12_3.D (m := 25) from colCert_64_12_3.bind1,
    show colData2 (⟨64, by decide⟩ : Fin 148)
        ((colE2 ⟨12, by decide⟩ 3 hp : ↥(Q2.reps ⟨12, by decide⟩)) : Coordinate 2)
        Q2.T64_12_2 = colFn colCert_64_12_3.D (m := 25) from colCert_64_12_3.bind2]
  exact alnAll_64_12_3 j hj hq

theorem leaf_64_12_4 (hp : 4 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 64 []).length)
    (hq : (normIsRep.getD 64 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 4 hp)
        (rowE2 (⟨64, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp))
        (rowE1 (⟨64, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨64, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨64, by decide⟩ (listedAt ⟨64, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp)) T64_12
      hfix64_12 hinj64_12 hcardT64_12
      (fun i => conj_mem_of_fixedPoints _ _ (T64_12 i) (hfix64_12 i) _)
      ⟨64, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨64, by decide⟩ (Q2.listedAt ⟨64, by decide⟩
        (alnCheck_rep ⟨64, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 4 hp) Q2.T64_12_2 Q2.hfix64_12_2 Q2.hinj64_12_2
      Q2.hcardT64_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T64_12_2 i) (Q2.hfix64_12_2 i) _)
      ?_).symm
  rw [show colData1 (⟨64, by decide⟩ : Fin 148)
        ((colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp) : ↥(reps ⟨12, by decide⟩)) : Coordinate 1)
        T64_12 = colFn colCert_64_12_4.D (m := 25) from colCert_64_12_4.bind1,
    show colData2 (⟨64, by decide⟩ : Fin 148)
        ((colE2 ⟨12, by decide⟩ 4 hp : ↥(Q2.reps ⟨12, by decide⟩)) : Coordinate 2)
        Q2.T64_12_2 = colFn colCert_64_12_4.D (m := 25) from colCert_64_12_4.bind2]
  exact alnAll_64_12_4 j hj hq

theorem leaf_64_26_0 (hp : 0 < (Q2.transData.getD 26 []).length)
    (j : Nat) (hj : j < (repChars.getD 64 []).length)
    (hq : (normIsRep.getD 64 []).getD j false = true) :
    species (Q2.reps (⟨26, by decide⟩ : Fin 148)) (colE2 ⟨26, by decide⟩ 0 hp)
        (rowE2 (⟨64, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨26, by decide⟩ : Fin 148))
        (colE1 ⟨26, by decide⟩ 0 (transLenTr ⟨26, by decide⟩ 0 hp))
        (rowE1 (⟨64, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨64, by decide⟩ : Fin 148) ⟨26, by decide⟩ _
      (validAt ⟨64, by decide⟩ (listedAt ⟨64, by decide⟩ hj))
      (colE1 ⟨26, by decide⟩ 0 (transLenTr ⟨26, by decide⟩ 0 hp)) T64_26
      hfix64_26 hinj64_26 hcardT64_26
      (fun i => conj_mem_of_fixedPoints _ _ (T64_26 i) (hfix64_26 i) _)
      ⟨64, by decide⟩ ⟨26, by decide⟩ _
      (Q2.validAt ⟨64, by decide⟩ (Q2.listedAt ⟨64, by decide⟩
        (alnCheck_rep ⟨64, by decide⟩ hj hq).1))
      (colE2 ⟨26, by decide⟩ 0 hp) Q2.T64_26_2 Q2.hfix64_26_2 Q2.hinj64_26_2
      Q2.hcardT64_26_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T64_26_2 i) (Q2.hfix64_26_2 i) _)
      ?_).symm
  rw [show colData1 (⟨64, by decide⟩ : Fin 148)
        ((colE1 ⟨26, by decide⟩ 0 (transLenTr ⟨26, by decide⟩ 0 hp) : ↥(reps ⟨26, by decide⟩)) : Coordinate 1)
        T64_26 = colFn colCert_64_26_0.D (m := 25) from colCert_64_26_0.bind1,
    show colData2 (⟨64, by decide⟩ : Fin 148)
        ((colE2 ⟨26, by decide⟩ 0 hp : ↥(Q2.reps ⟨26, by decide⟩)) : Coordinate 2)
        Q2.T64_26_2 = colFn colCert_64_26_0.D (m := 25) from colCert_64_26_0.bind2]
  exact alnAll_64_26_0 j hj hq

theorem leaf_64_26_1 (hp : 1 < (Q2.transData.getD 26 []).length)
    (j : Nat) (hj : j < (repChars.getD 64 []).length)
    (hq : (normIsRep.getD 64 []).getD j false = true) :
    species (Q2.reps (⟨26, by decide⟩ : Fin 148)) (colE2 ⟨26, by decide⟩ 1 hp)
        (rowE2 (⟨64, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨26, by decide⟩ : Fin 148))
        (colE1 ⟨26, by decide⟩ 1 (transLenTr ⟨26, by decide⟩ 1 hp))
        (rowE1 (⟨64, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨64, by decide⟩ : Fin 148) ⟨26, by decide⟩ _
      (validAt ⟨64, by decide⟩ (listedAt ⟨64, by decide⟩ hj))
      (colE1 ⟨26, by decide⟩ 1 (transLenTr ⟨26, by decide⟩ 1 hp)) T64_26
      hfix64_26 hinj64_26 hcardT64_26
      (fun i => conj_mem_of_fixedPoints _ _ (T64_26 i) (hfix64_26 i) _)
      ⟨64, by decide⟩ ⟨26, by decide⟩ _
      (Q2.validAt ⟨64, by decide⟩ (Q2.listedAt ⟨64, by decide⟩
        (alnCheck_rep ⟨64, by decide⟩ hj hq).1))
      (colE2 ⟨26, by decide⟩ 1 hp) Q2.T64_26_2 Q2.hfix64_26_2 Q2.hinj64_26_2
      Q2.hcardT64_26_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T64_26_2 i) (Q2.hfix64_26_2 i) _)
      ?_).symm
  rw [show colData1 (⟨64, by decide⟩ : Fin 148)
        ((colE1 ⟨26, by decide⟩ 1 (transLenTr ⟨26, by decide⟩ 1 hp) : ↥(reps ⟨26, by decide⟩)) : Coordinate 1)
        T64_26 = colFn colCert_64_26_1.D (m := 25) from colCert_64_26_1.bind1,
    show colData2 (⟨64, by decide⟩ : Fin 148)
        ((colE2 ⟨26, by decide⟩ 1 hp : ↥(Q2.reps ⟨26, by decide⟩)) : Coordinate 2)
        Q2.T64_26_2 = colFn colCert_64_26_1.D (m := 25) from colCert_64_26_1.bind2]
  exact alnAll_64_26_1 j hj hq

theorem leaf_64_26_2 (hp : 2 < (Q2.transData.getD 26 []).length)
    (j : Nat) (hj : j < (repChars.getD 64 []).length)
    (hq : (normIsRep.getD 64 []).getD j false = true) :
    species (Q2.reps (⟨26, by decide⟩ : Fin 148)) (colE2 ⟨26, by decide⟩ 2 hp)
        (rowE2 (⟨64, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨26, by decide⟩ : Fin 148))
        (colE1 ⟨26, by decide⟩ 2 (transLenTr ⟨26, by decide⟩ 2 hp))
        (rowE1 (⟨64, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨64, by decide⟩ : Fin 148) ⟨26, by decide⟩ _
      (validAt ⟨64, by decide⟩ (listedAt ⟨64, by decide⟩ hj))
      (colE1 ⟨26, by decide⟩ 2 (transLenTr ⟨26, by decide⟩ 2 hp)) T64_26
      hfix64_26 hinj64_26 hcardT64_26
      (fun i => conj_mem_of_fixedPoints _ _ (T64_26 i) (hfix64_26 i) _)
      ⟨64, by decide⟩ ⟨26, by decide⟩ _
      (Q2.validAt ⟨64, by decide⟩ (Q2.listedAt ⟨64, by decide⟩
        (alnCheck_rep ⟨64, by decide⟩ hj hq).1))
      (colE2 ⟨26, by decide⟩ 2 hp) Q2.T64_26_2 Q2.hfix64_26_2 Q2.hinj64_26_2
      Q2.hcardT64_26_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T64_26_2 i) (Q2.hfix64_26_2 i) _)
      ?_).symm
  rw [show colData1 (⟨64, by decide⟩ : Fin 148)
        ((colE1 ⟨26, by decide⟩ 2 (transLenTr ⟨26, by decide⟩ 2 hp) : ↥(reps ⟨26, by decide⟩)) : Coordinate 1)
        T64_26 = colFn colCert_64_26_2.D (m := 25) from colCert_64_26_2.bind1,
    show colData2 (⟨64, by decide⟩ : Fin 148)
        ((colE2 ⟨26, by decide⟩ 2 hp : ↥(Q2.reps ⟨26, by decide⟩)) : Coordinate 2)
        Q2.T64_26_2 = colFn colCert_64_26_2.D (m := 25) from colCert_64_26_2.bind2]
  exact alnAll_64_26_2 j hj hq

theorem leaf_64_26_3 (hp : 3 < (Q2.transData.getD 26 []).length)
    (j : Nat) (hj : j < (repChars.getD 64 []).length)
    (hq : (normIsRep.getD 64 []).getD j false = true) :
    species (Q2.reps (⟨26, by decide⟩ : Fin 148)) (colE2 ⟨26, by decide⟩ 3 hp)
        (rowE2 (⟨64, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨26, by decide⟩ : Fin 148))
        (colE1 ⟨26, by decide⟩ 3 (transLenTr ⟨26, by decide⟩ 3 hp))
        (rowE1 (⟨64, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨64, by decide⟩ : Fin 148) ⟨26, by decide⟩ _
      (validAt ⟨64, by decide⟩ (listedAt ⟨64, by decide⟩ hj))
      (colE1 ⟨26, by decide⟩ 3 (transLenTr ⟨26, by decide⟩ 3 hp)) T64_26
      hfix64_26 hinj64_26 hcardT64_26
      (fun i => conj_mem_of_fixedPoints _ _ (T64_26 i) (hfix64_26 i) _)
      ⟨64, by decide⟩ ⟨26, by decide⟩ _
      (Q2.validAt ⟨64, by decide⟩ (Q2.listedAt ⟨64, by decide⟩
        (alnCheck_rep ⟨64, by decide⟩ hj hq).1))
      (colE2 ⟨26, by decide⟩ 3 hp) Q2.T64_26_2 Q2.hfix64_26_2 Q2.hinj64_26_2
      Q2.hcardT64_26_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T64_26_2 i) (Q2.hfix64_26_2 i) _)
      ?_).symm
  rw [show colData1 (⟨64, by decide⟩ : Fin 148)
        ((colE1 ⟨26, by decide⟩ 3 (transLenTr ⟨26, by decide⟩ 3 hp) : ↥(reps ⟨26, by decide⟩)) : Coordinate 1)
        T64_26 = colFn colCert_64_26_3.D (m := 25) from colCert_64_26_3.bind1,
    show colData2 (⟨64, by decide⟩ : Fin 148)
        ((colE2 ⟨26, by decide⟩ 3 hp : ↥(Q2.reps ⟨26, by decide⟩)) : Coordinate 2)
        Q2.T64_26_2 = colFn colCert_64_26_3.D (m := 25) from colCert_64_26_3.bind2]
  exact alnAll_64_26_3 j hj hq

theorem leaf_64_26_4 (hp : 4 < (Q2.transData.getD 26 []).length)
    (j : Nat) (hj : j < (repChars.getD 64 []).length)
    (hq : (normIsRep.getD 64 []).getD j false = true) :
    species (Q2.reps (⟨26, by decide⟩ : Fin 148)) (colE2 ⟨26, by decide⟩ 4 hp)
        (rowE2 (⟨64, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨26, by decide⟩ : Fin 148))
        (colE1 ⟨26, by decide⟩ 4 (transLenTr ⟨26, by decide⟩ 4 hp))
        (rowE1 (⟨64, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨64, by decide⟩ : Fin 148) ⟨26, by decide⟩ _
      (validAt ⟨64, by decide⟩ (listedAt ⟨64, by decide⟩ hj))
      (colE1 ⟨26, by decide⟩ 4 (transLenTr ⟨26, by decide⟩ 4 hp)) T64_26
      hfix64_26 hinj64_26 hcardT64_26
      (fun i => conj_mem_of_fixedPoints _ _ (T64_26 i) (hfix64_26 i) _)
      ⟨64, by decide⟩ ⟨26, by decide⟩ _
      (Q2.validAt ⟨64, by decide⟩ (Q2.listedAt ⟨64, by decide⟩
        (alnCheck_rep ⟨64, by decide⟩ hj hq).1))
      (colE2 ⟨26, by decide⟩ 4 hp) Q2.T64_26_2 Q2.hfix64_26_2 Q2.hinj64_26_2
      Q2.hcardT64_26_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T64_26_2 i) (Q2.hfix64_26_2 i) _)
      ?_).symm
  rw [show colData1 (⟨64, by decide⟩ : Fin 148)
        ((colE1 ⟨26, by decide⟩ 4 (transLenTr ⟨26, by decide⟩ 4 hp) : ↥(reps ⟨26, by decide⟩)) : Coordinate 1)
        T64_26 = colFn colCert_64_26_4.D (m := 25) from colCert_64_26_4.bind1,
    show colData2 (⟨64, by decide⟩ : Fin 148)
        ((colE2 ⟨26, by decide⟩ 4 hp : ↥(Q2.reps ⟨26, by decide⟩)) : Coordinate 2)
        Q2.T64_26_2 = colFn colCert_64_26_4.D (m := 25) from colCert_64_26_4.bind2]
  exact alnAll_64_26_4 j hj hq

theorem leaf_64_26_5 (hp : 5 < (Q2.transData.getD 26 []).length)
    (j : Nat) (hj : j < (repChars.getD 64 []).length)
    (hq : (normIsRep.getD 64 []).getD j false = true) :
    species (Q2.reps (⟨26, by decide⟩ : Fin 148)) (colE2 ⟨26, by decide⟩ 5 hp)
        (rowE2 (⟨64, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨26, by decide⟩ : Fin 148))
        (colE1 ⟨26, by decide⟩ 5 (transLenTr ⟨26, by decide⟩ 5 hp))
        (rowE1 (⟨64, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨64, by decide⟩ : Fin 148) ⟨26, by decide⟩ _
      (validAt ⟨64, by decide⟩ (listedAt ⟨64, by decide⟩ hj))
      (colE1 ⟨26, by decide⟩ 5 (transLenTr ⟨26, by decide⟩ 5 hp)) T64_26
      hfix64_26 hinj64_26 hcardT64_26
      (fun i => conj_mem_of_fixedPoints _ _ (T64_26 i) (hfix64_26 i) _)
      ⟨64, by decide⟩ ⟨26, by decide⟩ _
      (Q2.validAt ⟨64, by decide⟩ (Q2.listedAt ⟨64, by decide⟩
        (alnCheck_rep ⟨64, by decide⟩ hj hq).1))
      (colE2 ⟨26, by decide⟩ 5 hp) Q2.T64_26_2 Q2.hfix64_26_2 Q2.hinj64_26_2
      Q2.hcardT64_26_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T64_26_2 i) (Q2.hfix64_26_2 i) _)
      ?_).symm
  rw [show colData1 (⟨64, by decide⟩ : Fin 148)
        ((colE1 ⟨26, by decide⟩ 5 (transLenTr ⟨26, by decide⟩ 5 hp) : ↥(reps ⟨26, by decide⟩)) : Coordinate 1)
        T64_26 = colFn colCert_64_26_5.D (m := 25) from colCert_64_26_5.bind1,
    show colData2 (⟨64, by decide⟩ : Fin 148)
        ((colE2 ⟨26, by decide⟩ 5 hp : ↥(Q2.reps ⟨26, by decide⟩)) : Coordinate 2)
        Q2.T64_26_2 = colFn colCert_64_26_5.D (m := 25) from colCert_64_26_5.bind2]
  exact alnAll_64_26_5 j hj hq

theorem leaf_64_26_10 (hp : 10 < (Q2.transData.getD 26 []).length)
    (j : Nat) (hj : j < (repChars.getD 64 []).length)
    (hq : (normIsRep.getD 64 []).getD j false = true) :
    species (Q2.reps (⟨26, by decide⟩ : Fin 148)) (colE2 ⟨26, by decide⟩ 10 hp)
        (rowE2 (⟨64, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨26, by decide⟩ : Fin 148))
        (colE1 ⟨26, by decide⟩ 10 (transLenTr ⟨26, by decide⟩ 10 hp))
        (rowE1 (⟨64, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨64, by decide⟩ : Fin 148) ⟨26, by decide⟩ _
      (validAt ⟨64, by decide⟩ (listedAt ⟨64, by decide⟩ hj))
      (colE1 ⟨26, by decide⟩ 10 (transLenTr ⟨26, by decide⟩ 10 hp)) T64_26
      hfix64_26 hinj64_26 hcardT64_26
      (fun i => conj_mem_of_fixedPoints _ _ (T64_26 i) (hfix64_26 i) _)
      ⟨64, by decide⟩ ⟨26, by decide⟩ _
      (Q2.validAt ⟨64, by decide⟩ (Q2.listedAt ⟨64, by decide⟩
        (alnCheck_rep ⟨64, by decide⟩ hj hq).1))
      (colE2 ⟨26, by decide⟩ 10 hp) Q2.T64_26_2 Q2.hfix64_26_2 Q2.hinj64_26_2
      Q2.hcardT64_26_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T64_26_2 i) (Q2.hfix64_26_2 i) _)
      ?_).symm
  rw [show colData1 (⟨64, by decide⟩ : Fin 148)
        ((colE1 ⟨26, by decide⟩ 10 (transLenTr ⟨26, by decide⟩ 10 hp) : ↥(reps ⟨26, by decide⟩)) : Coordinate 1)
        T64_26 = colFn colCert_64_26_10.D (m := 25) from colCert_64_26_10.bind1,
    show colData2 (⟨64, by decide⟩ : Fin 148)
        ((colE2 ⟨26, by decide⟩ 10 hp : ↥(Q2.reps ⟨26, by decide⟩)) : Coordinate 2)
        Q2.T64_26_2 = colFn colCert_64_26_10.D (m := 25) from colCert_64_26_10.bind2]
  exact alnAll_64_26_10 j hj hq

theorem leaf_64_26_15 (hp : 15 < (Q2.transData.getD 26 []).length)
    (j : Nat) (hj : j < (repChars.getD 64 []).length)
    (hq : (normIsRep.getD 64 []).getD j false = true) :
    species (Q2.reps (⟨26, by decide⟩ : Fin 148)) (colE2 ⟨26, by decide⟩ 15 hp)
        (rowE2 (⟨64, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨26, by decide⟩ : Fin 148))
        (colE1 ⟨26, by decide⟩ 15 (transLenTr ⟨26, by decide⟩ 15 hp))
        (rowE1 (⟨64, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨64, by decide⟩ : Fin 148) ⟨26, by decide⟩ _
      (validAt ⟨64, by decide⟩ (listedAt ⟨64, by decide⟩ hj))
      (colE1 ⟨26, by decide⟩ 15 (transLenTr ⟨26, by decide⟩ 15 hp)) T64_26
      hfix64_26 hinj64_26 hcardT64_26
      (fun i => conj_mem_of_fixedPoints _ _ (T64_26 i) (hfix64_26 i) _)
      ⟨64, by decide⟩ ⟨26, by decide⟩ _
      (Q2.validAt ⟨64, by decide⟩ (Q2.listedAt ⟨64, by decide⟩
        (alnCheck_rep ⟨64, by decide⟩ hj hq).1))
      (colE2 ⟨26, by decide⟩ 15 hp) Q2.T64_26_2 Q2.hfix64_26_2 Q2.hinj64_26_2
      Q2.hcardT64_26_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T64_26_2 i) (Q2.hfix64_26_2 i) _)
      ?_).symm
  rw [show colData1 (⟨64, by decide⟩ : Fin 148)
        ((colE1 ⟨26, by decide⟩ 15 (transLenTr ⟨26, by decide⟩ 15 hp) : ↥(reps ⟨26, by decide⟩)) : Coordinate 1)
        T64_26 = colFn colCert_64_26_15.D (m := 25) from colCert_64_26_15.bind1,
    show colData2 (⟨64, by decide⟩ : Fin 148)
        ((colE2 ⟨26, by decide⟩ 15 hp : ↥(Q2.reps ⟨26, by decide⟩)) : Coordinate 2)
        Q2.T64_26_2 = colFn colCert_64_26_15.D (m := 25) from colCert_64_26_15.bind2]
  exact alnAll_64_26_15 j hj hq

theorem leaf_64_26_20 (hp : 20 < (Q2.transData.getD 26 []).length)
    (j : Nat) (hj : j < (repChars.getD 64 []).length)
    (hq : (normIsRep.getD 64 []).getD j false = true) :
    species (Q2.reps (⟨26, by decide⟩ : Fin 148)) (colE2 ⟨26, by decide⟩ 20 hp)
        (rowE2 (⟨64, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨26, by decide⟩ : Fin 148))
        (colE1 ⟨26, by decide⟩ 20 (transLenTr ⟨26, by decide⟩ 20 hp))
        (rowE1 (⟨64, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨64, by decide⟩ : Fin 148) ⟨26, by decide⟩ _
      (validAt ⟨64, by decide⟩ (listedAt ⟨64, by decide⟩ hj))
      (colE1 ⟨26, by decide⟩ 20 (transLenTr ⟨26, by decide⟩ 20 hp)) T64_26
      hfix64_26 hinj64_26 hcardT64_26
      (fun i => conj_mem_of_fixedPoints _ _ (T64_26 i) (hfix64_26 i) _)
      ⟨64, by decide⟩ ⟨26, by decide⟩ _
      (Q2.validAt ⟨64, by decide⟩ (Q2.listedAt ⟨64, by decide⟩
        (alnCheck_rep ⟨64, by decide⟩ hj hq).1))
      (colE2 ⟨26, by decide⟩ 20 hp) Q2.T64_26_2 Q2.hfix64_26_2 Q2.hinj64_26_2
      Q2.hcardT64_26_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T64_26_2 i) (Q2.hfix64_26_2 i) _)
      ?_).symm
  rw [show colData1 (⟨64, by decide⟩ : Fin 148)
        ((colE1 ⟨26, by decide⟩ 20 (transLenTr ⟨26, by decide⟩ 20 hp) : ↥(reps ⟨26, by decide⟩)) : Coordinate 1)
        T64_26 = colFn colCert_64_26_20.D (m := 25) from colCert_64_26_20.bind1,
    show colData2 (⟨64, by decide⟩ : Fin 148)
        ((colE2 ⟨26, by decide⟩ 20 hp : ↥(Q2.reps ⟨26, by decide⟩)) : Coordinate 2)
        Q2.T64_26_2 = colFn colCert_64_26_20.D (m := 25) from colCert_64_26_20.bind2]
  exact alnAll_64_26_20 j hj hq

theorem leaf_64_29_0 (hp : 0 < (Q2.transData.getD 29 []).length)
    (j : Nat) (hj : j < (repChars.getD 64 []).length)
    (hq : (normIsRep.getD 64 []).getD j false = true) :
    species (Q2.reps (⟨29, by decide⟩ : Fin 148)) (colE2 ⟨29, by decide⟩ 0 hp)
        (rowE2 (⟨64, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨29, by decide⟩ : Fin 148))
        (colE1 ⟨29, by decide⟩ 0 (transLenTr ⟨29, by decide⟩ 0 hp))
        (rowE1 (⟨64, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨64, by decide⟩ : Fin 148) ⟨29, by decide⟩ _
      (validAt ⟨64, by decide⟩ (listedAt ⟨64, by decide⟩ hj))
      (colE1 ⟨29, by decide⟩ 0 (transLenTr ⟨29, by decide⟩ 0 hp)) T64_29
      hfix64_29 hinj64_29 hcardT64_29
      (fun i => conj_mem_of_fixedPoints _ _ (T64_29 i) (hfix64_29 i) _)
      ⟨64, by decide⟩ ⟨29, by decide⟩ _
      (Q2.validAt ⟨64, by decide⟩ (Q2.listedAt ⟨64, by decide⟩
        (alnCheck_rep ⟨64, by decide⟩ hj hq).1))
      (colE2 ⟨29, by decide⟩ 0 hp) Q2.T64_29_2 Q2.hfix64_29_2 Q2.hinj64_29_2
      Q2.hcardT64_29_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T64_29_2 i) (Q2.hfix64_29_2 i) _)
      ?_).symm
  rw [show colData1 (⟨64, by decide⟩ : Fin 148)
        ((colE1 ⟨29, by decide⟩ 0 (transLenTr ⟨29, by decide⟩ 0 hp) : ↥(reps ⟨29, by decide⟩)) : Coordinate 1)
        T64_29 = colFn colCert_64_29_0.D (m := 5) from colCert_64_29_0.bind1,
    show colData2 (⟨64, by decide⟩ : Fin 148)
        ((colE2 ⟨29, by decide⟩ 0 hp : ↥(Q2.reps ⟨29, by decide⟩)) : Coordinate 2)
        Q2.T64_29_2 = colFn colCert_64_29_0.D (m := 5) from colCert_64_29_0.bind2]
  exact alnAll_64_29_0 j hj hq

theorem leaf_64_29_1 (hp : 1 < (Q2.transData.getD 29 []).length)
    (j : Nat) (hj : j < (repChars.getD 64 []).length)
    (hq : (normIsRep.getD 64 []).getD j false = true) :
    species (Q2.reps (⟨29, by decide⟩ : Fin 148)) (colE2 ⟨29, by decide⟩ 1 hp)
        (rowE2 (⟨64, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨29, by decide⟩ : Fin 148))
        (colE1 ⟨29, by decide⟩ 1 (transLenTr ⟨29, by decide⟩ 1 hp))
        (rowE1 (⟨64, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨64, by decide⟩ : Fin 148) ⟨29, by decide⟩ _
      (validAt ⟨64, by decide⟩ (listedAt ⟨64, by decide⟩ hj))
      (colE1 ⟨29, by decide⟩ 1 (transLenTr ⟨29, by decide⟩ 1 hp)) T64_29
      hfix64_29 hinj64_29 hcardT64_29
      (fun i => conj_mem_of_fixedPoints _ _ (T64_29 i) (hfix64_29 i) _)
      ⟨64, by decide⟩ ⟨29, by decide⟩ _
      (Q2.validAt ⟨64, by decide⟩ (Q2.listedAt ⟨64, by decide⟩
        (alnCheck_rep ⟨64, by decide⟩ hj hq).1))
      (colE2 ⟨29, by decide⟩ 1 hp) Q2.T64_29_2 Q2.hfix64_29_2 Q2.hinj64_29_2
      Q2.hcardT64_29_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T64_29_2 i) (Q2.hfix64_29_2 i) _)
      ?_).symm
  rw [show colData1 (⟨64, by decide⟩ : Fin 148)
        ((colE1 ⟨29, by decide⟩ 1 (transLenTr ⟨29, by decide⟩ 1 hp) : ↥(reps ⟨29, by decide⟩)) : Coordinate 1)
        T64_29 = colFn colCert_64_29_1.D (m := 5) from colCert_64_29_1.bind1,
    show colData2 (⟨64, by decide⟩ : Fin 148)
        ((colE2 ⟨29, by decide⟩ 1 hp : ↥(Q2.reps ⟨29, by decide⟩)) : Coordinate 2)
        Q2.T64_29_2 = colFn colCert_64_29_1.D (m := 5) from colCert_64_29_1.bind2]
  exact alnAll_64_29_1 j hj hq

theorem leaf_64_29_2 (hp : 2 < (Q2.transData.getD 29 []).length)
    (j : Nat) (hj : j < (repChars.getD 64 []).length)
    (hq : (normIsRep.getD 64 []).getD j false = true) :
    species (Q2.reps (⟨29, by decide⟩ : Fin 148)) (colE2 ⟨29, by decide⟩ 2 hp)
        (rowE2 (⟨64, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨29, by decide⟩ : Fin 148))
        (colE1 ⟨29, by decide⟩ 2 (transLenTr ⟨29, by decide⟩ 2 hp))
        (rowE1 (⟨64, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨64, by decide⟩ : Fin 148) ⟨29, by decide⟩ _
      (validAt ⟨64, by decide⟩ (listedAt ⟨64, by decide⟩ hj))
      (colE1 ⟨29, by decide⟩ 2 (transLenTr ⟨29, by decide⟩ 2 hp)) T64_29
      hfix64_29 hinj64_29 hcardT64_29
      (fun i => conj_mem_of_fixedPoints _ _ (T64_29 i) (hfix64_29 i) _)
      ⟨64, by decide⟩ ⟨29, by decide⟩ _
      (Q2.validAt ⟨64, by decide⟩ (Q2.listedAt ⟨64, by decide⟩
        (alnCheck_rep ⟨64, by decide⟩ hj hq).1))
      (colE2 ⟨29, by decide⟩ 2 hp) Q2.T64_29_2 Q2.hfix64_29_2 Q2.hinj64_29_2
      Q2.hcardT64_29_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T64_29_2 i) (Q2.hfix64_29_2 i) _)
      ?_).symm
  rw [show colData1 (⟨64, by decide⟩ : Fin 148)
        ((colE1 ⟨29, by decide⟩ 2 (transLenTr ⟨29, by decide⟩ 2 hp) : ↥(reps ⟨29, by decide⟩)) : Coordinate 1)
        T64_29 = colFn colCert_64_29_2.D (m := 5) from colCert_64_29_2.bind1,
    show colData2 (⟨64, by decide⟩ : Fin 148)
        ((colE2 ⟨29, by decide⟩ 2 hp : ↥(Q2.reps ⟨29, by decide⟩)) : Coordinate 2)
        Q2.T64_29_2 = colFn colCert_64_29_2.D (m := 5) from colCert_64_29_2.bind2]
  exact alnAll_64_29_2 j hj hq

theorem leaf_64_29_3 (hp : 3 < (Q2.transData.getD 29 []).length)
    (j : Nat) (hj : j < (repChars.getD 64 []).length)
    (hq : (normIsRep.getD 64 []).getD j false = true) :
    species (Q2.reps (⟨29, by decide⟩ : Fin 148)) (colE2 ⟨29, by decide⟩ 3 hp)
        (rowE2 (⟨64, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨29, by decide⟩ : Fin 148))
        (colE1 ⟨29, by decide⟩ 3 (transLenTr ⟨29, by decide⟩ 3 hp))
        (rowE1 (⟨64, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨64, by decide⟩ : Fin 148) ⟨29, by decide⟩ _
      (validAt ⟨64, by decide⟩ (listedAt ⟨64, by decide⟩ hj))
      (colE1 ⟨29, by decide⟩ 3 (transLenTr ⟨29, by decide⟩ 3 hp)) T64_29
      hfix64_29 hinj64_29 hcardT64_29
      (fun i => conj_mem_of_fixedPoints _ _ (T64_29 i) (hfix64_29 i) _)
      ⟨64, by decide⟩ ⟨29, by decide⟩ _
      (Q2.validAt ⟨64, by decide⟩ (Q2.listedAt ⟨64, by decide⟩
        (alnCheck_rep ⟨64, by decide⟩ hj hq).1))
      (colE2 ⟨29, by decide⟩ 3 hp) Q2.T64_29_2 Q2.hfix64_29_2 Q2.hinj64_29_2
      Q2.hcardT64_29_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T64_29_2 i) (Q2.hfix64_29_2 i) _)
      ?_).symm
  rw [show colData1 (⟨64, by decide⟩ : Fin 148)
        ((colE1 ⟨29, by decide⟩ 3 (transLenTr ⟨29, by decide⟩ 3 hp) : ↥(reps ⟨29, by decide⟩)) : Coordinate 1)
        T64_29 = colFn colCert_64_29_3.D (m := 5) from colCert_64_29_3.bind1,
    show colData2 (⟨64, by decide⟩ : Fin 148)
        ((colE2 ⟨29, by decide⟩ 3 hp : ↥(Q2.reps ⟨29, by decide⟩)) : Coordinate 2)
        Q2.T64_29_2 = colFn colCert_64_29_3.D (m := 5) from colCert_64_29_3.bind2]
  exact alnAll_64_29_3 j hj hq

theorem leaf_64_29_4 (hp : 4 < (Q2.transData.getD 29 []).length)
    (j : Nat) (hj : j < (repChars.getD 64 []).length)
    (hq : (normIsRep.getD 64 []).getD j false = true) :
    species (Q2.reps (⟨29, by decide⟩ : Fin 148)) (colE2 ⟨29, by decide⟩ 4 hp)
        (rowE2 (⟨64, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨29, by decide⟩ : Fin 148))
        (colE1 ⟨29, by decide⟩ 4 (transLenTr ⟨29, by decide⟩ 4 hp))
        (rowE1 (⟨64, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨64, by decide⟩ : Fin 148) ⟨29, by decide⟩ _
      (validAt ⟨64, by decide⟩ (listedAt ⟨64, by decide⟩ hj))
      (colE1 ⟨29, by decide⟩ 4 (transLenTr ⟨29, by decide⟩ 4 hp)) T64_29
      hfix64_29 hinj64_29 hcardT64_29
      (fun i => conj_mem_of_fixedPoints _ _ (T64_29 i) (hfix64_29 i) _)
      ⟨64, by decide⟩ ⟨29, by decide⟩ _
      (Q2.validAt ⟨64, by decide⟩ (Q2.listedAt ⟨64, by decide⟩
        (alnCheck_rep ⟨64, by decide⟩ hj hq).1))
      (colE2 ⟨29, by decide⟩ 4 hp) Q2.T64_29_2 Q2.hfix64_29_2 Q2.hinj64_29_2
      Q2.hcardT64_29_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T64_29_2 i) (Q2.hfix64_29_2 i) _)
      ?_).symm
  rw [show colData1 (⟨64, by decide⟩ : Fin 148)
        ((colE1 ⟨29, by decide⟩ 4 (transLenTr ⟨29, by decide⟩ 4 hp) : ↥(reps ⟨29, by decide⟩)) : Coordinate 1)
        T64_29 = colFn colCert_64_29_4.D (m := 5) from colCert_64_29_4.bind1,
    show colData2 (⟨64, by decide⟩ : Fin 148)
        ((colE2 ⟨29, by decide⟩ 4 hp : ↥(Q2.reps ⟨29, by decide⟩)) : Coordinate 2)
        Q2.T64_29_2 = colFn colCert_64_29_4.D (m := 5) from colCert_64_29_4.bind2]
  exact alnAll_64_29_4 j hj hq

theorem leaf_64_29_5 (hp : 5 < (Q2.transData.getD 29 []).length)
    (j : Nat) (hj : j < (repChars.getD 64 []).length)
    (hq : (normIsRep.getD 64 []).getD j false = true) :
    species (Q2.reps (⟨29, by decide⟩ : Fin 148)) (colE2 ⟨29, by decide⟩ 5 hp)
        (rowE2 (⟨64, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨29, by decide⟩ : Fin 148))
        (colE1 ⟨29, by decide⟩ 5 (transLenTr ⟨29, by decide⟩ 5 hp))
        (rowE1 (⟨64, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨64, by decide⟩ : Fin 148) ⟨29, by decide⟩ _
      (validAt ⟨64, by decide⟩ (listedAt ⟨64, by decide⟩ hj))
      (colE1 ⟨29, by decide⟩ 5 (transLenTr ⟨29, by decide⟩ 5 hp)) T64_29
      hfix64_29 hinj64_29 hcardT64_29
      (fun i => conj_mem_of_fixedPoints _ _ (T64_29 i) (hfix64_29 i) _)
      ⟨64, by decide⟩ ⟨29, by decide⟩ _
      (Q2.validAt ⟨64, by decide⟩ (Q2.listedAt ⟨64, by decide⟩
        (alnCheck_rep ⟨64, by decide⟩ hj hq).1))
      (colE2 ⟨29, by decide⟩ 5 hp) Q2.T64_29_2 Q2.hfix64_29_2 Q2.hinj64_29_2
      Q2.hcardT64_29_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T64_29_2 i) (Q2.hfix64_29_2 i) _)
      ?_).symm
  rw [show colData1 (⟨64, by decide⟩ : Fin 148)
        ((colE1 ⟨29, by decide⟩ 5 (transLenTr ⟨29, by decide⟩ 5 hp) : ↥(reps ⟨29, by decide⟩)) : Coordinate 1)
        T64_29 = colFn colCert_64_29_5.D (m := 5) from colCert_64_29_5.bind1,
    show colData2 (⟨64, by decide⟩ : Fin 148)
        ((colE2 ⟨29, by decide⟩ 5 hp : ↥(Q2.reps ⟨29, by decide⟩)) : Coordinate 2)
        Q2.T64_29_2 = colFn colCert_64_29_5.D (m := 5) from colCert_64_29_5.bind2]
  exact alnAll_64_29_5 j hj hq

theorem leaf_64_29_10 (hp : 10 < (Q2.transData.getD 29 []).length)
    (j : Nat) (hj : j < (repChars.getD 64 []).length)
    (hq : (normIsRep.getD 64 []).getD j false = true) :
    species (Q2.reps (⟨29, by decide⟩ : Fin 148)) (colE2 ⟨29, by decide⟩ 10 hp)
        (rowE2 (⟨64, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨29, by decide⟩ : Fin 148))
        (colE1 ⟨29, by decide⟩ 10 (transLenTr ⟨29, by decide⟩ 10 hp))
        (rowE1 (⟨64, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨64, by decide⟩ : Fin 148) ⟨29, by decide⟩ _
      (validAt ⟨64, by decide⟩ (listedAt ⟨64, by decide⟩ hj))
      (colE1 ⟨29, by decide⟩ 10 (transLenTr ⟨29, by decide⟩ 10 hp)) T64_29
      hfix64_29 hinj64_29 hcardT64_29
      (fun i => conj_mem_of_fixedPoints _ _ (T64_29 i) (hfix64_29 i) _)
      ⟨64, by decide⟩ ⟨29, by decide⟩ _
      (Q2.validAt ⟨64, by decide⟩ (Q2.listedAt ⟨64, by decide⟩
        (alnCheck_rep ⟨64, by decide⟩ hj hq).1))
      (colE2 ⟨29, by decide⟩ 10 hp) Q2.T64_29_2 Q2.hfix64_29_2 Q2.hinj64_29_2
      Q2.hcardT64_29_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T64_29_2 i) (Q2.hfix64_29_2 i) _)
      ?_).symm
  rw [show colData1 (⟨64, by decide⟩ : Fin 148)
        ((colE1 ⟨29, by decide⟩ 10 (transLenTr ⟨29, by decide⟩ 10 hp) : ↥(reps ⟨29, by decide⟩)) : Coordinate 1)
        T64_29 = colFn colCert_64_29_10.D (m := 5) from colCert_64_29_10.bind1,
    show colData2 (⟨64, by decide⟩ : Fin 148)
        ((colE2 ⟨29, by decide⟩ 10 hp : ↥(Q2.reps ⟨29, by decide⟩)) : Coordinate 2)
        Q2.T64_29_2 = colFn colCert_64_29_10.D (m := 5) from colCert_64_29_10.bind2]
  exact alnAll_64_29_10 j hj hq

theorem leaf_64_29_15 (hp : 15 < (Q2.transData.getD 29 []).length)
    (j : Nat) (hj : j < (repChars.getD 64 []).length)
    (hq : (normIsRep.getD 64 []).getD j false = true) :
    species (Q2.reps (⟨29, by decide⟩ : Fin 148)) (colE2 ⟨29, by decide⟩ 15 hp)
        (rowE2 (⟨64, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨29, by decide⟩ : Fin 148))
        (colE1 ⟨29, by decide⟩ 15 (transLenTr ⟨29, by decide⟩ 15 hp))
        (rowE1 (⟨64, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨64, by decide⟩ : Fin 148) ⟨29, by decide⟩ _
      (validAt ⟨64, by decide⟩ (listedAt ⟨64, by decide⟩ hj))
      (colE1 ⟨29, by decide⟩ 15 (transLenTr ⟨29, by decide⟩ 15 hp)) T64_29
      hfix64_29 hinj64_29 hcardT64_29
      (fun i => conj_mem_of_fixedPoints _ _ (T64_29 i) (hfix64_29 i) _)
      ⟨64, by decide⟩ ⟨29, by decide⟩ _
      (Q2.validAt ⟨64, by decide⟩ (Q2.listedAt ⟨64, by decide⟩
        (alnCheck_rep ⟨64, by decide⟩ hj hq).1))
      (colE2 ⟨29, by decide⟩ 15 hp) Q2.T64_29_2 Q2.hfix64_29_2 Q2.hinj64_29_2
      Q2.hcardT64_29_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T64_29_2 i) (Q2.hfix64_29_2 i) _)
      ?_).symm
  rw [show colData1 (⟨64, by decide⟩ : Fin 148)
        ((colE1 ⟨29, by decide⟩ 15 (transLenTr ⟨29, by decide⟩ 15 hp) : ↥(reps ⟨29, by decide⟩)) : Coordinate 1)
        T64_29 = colFn colCert_64_29_15.D (m := 5) from colCert_64_29_15.bind1,
    show colData2 (⟨64, by decide⟩ : Fin 148)
        ((colE2 ⟨29, by decide⟩ 15 hp : ↥(Q2.reps ⟨29, by decide⟩)) : Coordinate 2)
        Q2.T64_29_2 = colFn colCert_64_29_15.D (m := 5) from colCert_64_29_15.bind2]
  exact alnAll_64_29_15 j hj hq

theorem leaf_64_29_20 (hp : 20 < (Q2.transData.getD 29 []).length)
    (j : Nat) (hj : j < (repChars.getD 64 []).length)
    (hq : (normIsRep.getD 64 []).getD j false = true) :
    species (Q2.reps (⟨29, by decide⟩ : Fin 148)) (colE2 ⟨29, by decide⟩ 20 hp)
        (rowE2 (⟨64, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨29, by decide⟩ : Fin 148))
        (colE1 ⟨29, by decide⟩ 20 (transLenTr ⟨29, by decide⟩ 20 hp))
        (rowE1 (⟨64, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨64, by decide⟩ : Fin 148) ⟨29, by decide⟩ _
      (validAt ⟨64, by decide⟩ (listedAt ⟨64, by decide⟩ hj))
      (colE1 ⟨29, by decide⟩ 20 (transLenTr ⟨29, by decide⟩ 20 hp)) T64_29
      hfix64_29 hinj64_29 hcardT64_29
      (fun i => conj_mem_of_fixedPoints _ _ (T64_29 i) (hfix64_29 i) _)
      ⟨64, by decide⟩ ⟨29, by decide⟩ _
      (Q2.validAt ⟨64, by decide⟩ (Q2.listedAt ⟨64, by decide⟩
        (alnCheck_rep ⟨64, by decide⟩ hj hq).1))
      (colE2 ⟨29, by decide⟩ 20 hp) Q2.T64_29_2 Q2.hfix64_29_2 Q2.hinj64_29_2
      Q2.hcardT64_29_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T64_29_2 i) (Q2.hfix64_29_2 i) _)
      ?_).symm
  rw [show colData1 (⟨64, by decide⟩ : Fin 148)
        ((colE1 ⟨29, by decide⟩ 20 (transLenTr ⟨29, by decide⟩ 20 hp) : ↥(reps ⟨29, by decide⟩)) : Coordinate 1)
        T64_29 = colFn colCert_64_29_20.D (m := 5) from colCert_64_29_20.bind1,
    show colData2 (⟨64, by decide⟩ : Fin 148)
        ((colE2 ⟨29, by decide⟩ 20 hp : ↥(Q2.reps ⟨29, by decide⟩)) : Coordinate 2)
        Q2.T64_29_2 = colFn colCert_64_29_20.D (m := 5) from colCert_64_29_20.bind2]
  exact alnAll_64_29_20 j hj hq

theorem leaf_64_34_0 (hp : 0 < (Q2.transData.getD 34 []).length)
    (j : Nat) (hj : j < (repChars.getD 64 []).length)
    (hq : (normIsRep.getD 64 []).getD j false = true) :
    species (Q2.reps (⟨34, by decide⟩ : Fin 148)) (colE2 ⟨34, by decide⟩ 0 hp)
        (rowE2 (⟨64, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨34, by decide⟩ : Fin 148))
        (colE1 ⟨34, by decide⟩ 0 (transLenTr ⟨34, by decide⟩ 0 hp))
        (rowE1 (⟨64, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨64, by decide⟩ : Fin 148) ⟨34, by decide⟩ _
      (validAt ⟨64, by decide⟩ (listedAt ⟨64, by decide⟩ hj))
      (colE1 ⟨34, by decide⟩ 0 (transLenTr ⟨34, by decide⟩ 0 hp)) T64_34
      hfix64_34 hinj64_34 hcardT64_34
      (fun i => conj_mem_of_fixedPoints _ _ (T64_34 i) (hfix64_34 i) _)
      ⟨64, by decide⟩ ⟨34, by decide⟩ _
      (Q2.validAt ⟨64, by decide⟩ (Q2.listedAt ⟨64, by decide⟩
        (alnCheck_rep ⟨64, by decide⟩ hj hq).1))
      (colE2 ⟨34, by decide⟩ 0 hp) Q2.T64_34_2 Q2.hfix64_34_2 Q2.hinj64_34_2
      Q2.hcardT64_34_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T64_34_2 i) (Q2.hfix64_34_2 i) _)
      ?_).symm
  rw [show colData1 (⟨64, by decide⟩ : Fin 148)
        ((colE1 ⟨34, by decide⟩ 0 (transLenTr ⟨34, by decide⟩ 0 hp) : ↥(reps ⟨34, by decide⟩)) : Coordinate 1)
        T64_34 = colFn colCert_64_34_0.D (m := 5) from colCert_64_34_0.bind1,
    show colData2 (⟨64, by decide⟩ : Fin 148)
        ((colE2 ⟨34, by decide⟩ 0 hp : ↥(Q2.reps ⟨34, by decide⟩)) : Coordinate 2)
        Q2.T64_34_2 = colFn colCert_64_34_0.D (m := 5) from colCert_64_34_0.bind2]
  exact alnAll_64_34_0 j hj hq

theorem leaf_64_34_1 (hp : 1 < (Q2.transData.getD 34 []).length)
    (j : Nat) (hj : j < (repChars.getD 64 []).length)
    (hq : (normIsRep.getD 64 []).getD j false = true) :
    species (Q2.reps (⟨34, by decide⟩ : Fin 148)) (colE2 ⟨34, by decide⟩ 1 hp)
        (rowE2 (⟨64, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨34, by decide⟩ : Fin 148))
        (colE1 ⟨34, by decide⟩ 1 (transLenTr ⟨34, by decide⟩ 1 hp))
        (rowE1 (⟨64, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨64, by decide⟩ : Fin 148) ⟨34, by decide⟩ _
      (validAt ⟨64, by decide⟩ (listedAt ⟨64, by decide⟩ hj))
      (colE1 ⟨34, by decide⟩ 1 (transLenTr ⟨34, by decide⟩ 1 hp)) T64_34
      hfix64_34 hinj64_34 hcardT64_34
      (fun i => conj_mem_of_fixedPoints _ _ (T64_34 i) (hfix64_34 i) _)
      ⟨64, by decide⟩ ⟨34, by decide⟩ _
      (Q2.validAt ⟨64, by decide⟩ (Q2.listedAt ⟨64, by decide⟩
        (alnCheck_rep ⟨64, by decide⟩ hj hq).1))
      (colE2 ⟨34, by decide⟩ 1 hp) Q2.T64_34_2 Q2.hfix64_34_2 Q2.hinj64_34_2
      Q2.hcardT64_34_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T64_34_2 i) (Q2.hfix64_34_2 i) _)
      ?_).symm
  rw [show colData1 (⟨64, by decide⟩ : Fin 148)
        ((colE1 ⟨34, by decide⟩ 1 (transLenTr ⟨34, by decide⟩ 1 hp) : ↥(reps ⟨34, by decide⟩)) : Coordinate 1)
        T64_34 = colFn colCert_64_34_1.D (m := 5) from colCert_64_34_1.bind1,
    show colData2 (⟨64, by decide⟩ : Fin 148)
        ((colE2 ⟨34, by decide⟩ 1 hp : ↥(Q2.reps ⟨34, by decide⟩)) : Coordinate 2)
        Q2.T64_34_2 = colFn colCert_64_34_1.D (m := 5) from colCert_64_34_1.bind2]
  exact alnAll_64_34_1 j hj hq

theorem leaf_64_34_2 (hp : 2 < (Q2.transData.getD 34 []).length)
    (j : Nat) (hj : j < (repChars.getD 64 []).length)
    (hq : (normIsRep.getD 64 []).getD j false = true) :
    species (Q2.reps (⟨34, by decide⟩ : Fin 148)) (colE2 ⟨34, by decide⟩ 2 hp)
        (rowE2 (⟨64, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨34, by decide⟩ : Fin 148))
        (colE1 ⟨34, by decide⟩ 2 (transLenTr ⟨34, by decide⟩ 2 hp))
        (rowE1 (⟨64, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨64, by decide⟩ : Fin 148) ⟨34, by decide⟩ _
      (validAt ⟨64, by decide⟩ (listedAt ⟨64, by decide⟩ hj))
      (colE1 ⟨34, by decide⟩ 2 (transLenTr ⟨34, by decide⟩ 2 hp)) T64_34
      hfix64_34 hinj64_34 hcardT64_34
      (fun i => conj_mem_of_fixedPoints _ _ (T64_34 i) (hfix64_34 i) _)
      ⟨64, by decide⟩ ⟨34, by decide⟩ _
      (Q2.validAt ⟨64, by decide⟩ (Q2.listedAt ⟨64, by decide⟩
        (alnCheck_rep ⟨64, by decide⟩ hj hq).1))
      (colE2 ⟨34, by decide⟩ 2 hp) Q2.T64_34_2 Q2.hfix64_34_2 Q2.hinj64_34_2
      Q2.hcardT64_34_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T64_34_2 i) (Q2.hfix64_34_2 i) _)
      ?_).symm
  rw [show colData1 (⟨64, by decide⟩ : Fin 148)
        ((colE1 ⟨34, by decide⟩ 2 (transLenTr ⟨34, by decide⟩ 2 hp) : ↥(reps ⟨34, by decide⟩)) : Coordinate 1)
        T64_34 = colFn colCert_64_34_2.D (m := 5) from colCert_64_34_2.bind1,
    show colData2 (⟨64, by decide⟩ : Fin 148)
        ((colE2 ⟨34, by decide⟩ 2 hp : ↥(Q2.reps ⟨34, by decide⟩)) : Coordinate 2)
        Q2.T64_34_2 = colFn colCert_64_34_2.D (m := 5) from colCert_64_34_2.bind2]
  exact alnAll_64_34_2 j hj hq

theorem leaf_64_34_3 (hp : 3 < (Q2.transData.getD 34 []).length)
    (j : Nat) (hj : j < (repChars.getD 64 []).length)
    (hq : (normIsRep.getD 64 []).getD j false = true) :
    species (Q2.reps (⟨34, by decide⟩ : Fin 148)) (colE2 ⟨34, by decide⟩ 3 hp)
        (rowE2 (⟨64, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨34, by decide⟩ : Fin 148))
        (colE1 ⟨34, by decide⟩ 3 (transLenTr ⟨34, by decide⟩ 3 hp))
        (rowE1 (⟨64, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨64, by decide⟩ : Fin 148) ⟨34, by decide⟩ _
      (validAt ⟨64, by decide⟩ (listedAt ⟨64, by decide⟩ hj))
      (colE1 ⟨34, by decide⟩ 3 (transLenTr ⟨34, by decide⟩ 3 hp)) T64_34
      hfix64_34 hinj64_34 hcardT64_34
      (fun i => conj_mem_of_fixedPoints _ _ (T64_34 i) (hfix64_34 i) _)
      ⟨64, by decide⟩ ⟨34, by decide⟩ _
      (Q2.validAt ⟨64, by decide⟩ (Q2.listedAt ⟨64, by decide⟩
        (alnCheck_rep ⟨64, by decide⟩ hj hq).1))
      (colE2 ⟨34, by decide⟩ 3 hp) Q2.T64_34_2 Q2.hfix64_34_2 Q2.hinj64_34_2
      Q2.hcardT64_34_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T64_34_2 i) (Q2.hfix64_34_2 i) _)
      ?_).symm
  rw [show colData1 (⟨64, by decide⟩ : Fin 148)
        ((colE1 ⟨34, by decide⟩ 3 (transLenTr ⟨34, by decide⟩ 3 hp) : ↥(reps ⟨34, by decide⟩)) : Coordinate 1)
        T64_34 = colFn colCert_64_34_3.D (m := 5) from colCert_64_34_3.bind1,
    show colData2 (⟨64, by decide⟩ : Fin 148)
        ((colE2 ⟨34, by decide⟩ 3 hp : ↥(Q2.reps ⟨34, by decide⟩)) : Coordinate 2)
        Q2.T64_34_2 = colFn colCert_64_34_3.D (m := 5) from colCert_64_34_3.bind2]
  exact alnAll_64_34_3 j hj hq

theorem leaf_64_34_4 (hp : 4 < (Q2.transData.getD 34 []).length)
    (j : Nat) (hj : j < (repChars.getD 64 []).length)
    (hq : (normIsRep.getD 64 []).getD j false = true) :
    species (Q2.reps (⟨34, by decide⟩ : Fin 148)) (colE2 ⟨34, by decide⟩ 4 hp)
        (rowE2 (⟨64, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨34, by decide⟩ : Fin 148))
        (colE1 ⟨34, by decide⟩ 4 (transLenTr ⟨34, by decide⟩ 4 hp))
        (rowE1 (⟨64, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨64, by decide⟩ : Fin 148) ⟨34, by decide⟩ _
      (validAt ⟨64, by decide⟩ (listedAt ⟨64, by decide⟩ hj))
      (colE1 ⟨34, by decide⟩ 4 (transLenTr ⟨34, by decide⟩ 4 hp)) T64_34
      hfix64_34 hinj64_34 hcardT64_34
      (fun i => conj_mem_of_fixedPoints _ _ (T64_34 i) (hfix64_34 i) _)
      ⟨64, by decide⟩ ⟨34, by decide⟩ _
      (Q2.validAt ⟨64, by decide⟩ (Q2.listedAt ⟨64, by decide⟩
        (alnCheck_rep ⟨64, by decide⟩ hj hq).1))
      (colE2 ⟨34, by decide⟩ 4 hp) Q2.T64_34_2 Q2.hfix64_34_2 Q2.hinj64_34_2
      Q2.hcardT64_34_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T64_34_2 i) (Q2.hfix64_34_2 i) _)
      ?_).symm
  rw [show colData1 (⟨64, by decide⟩ : Fin 148)
        ((colE1 ⟨34, by decide⟩ 4 (transLenTr ⟨34, by decide⟩ 4 hp) : ↥(reps ⟨34, by decide⟩)) : Coordinate 1)
        T64_34 = colFn colCert_64_34_4.D (m := 5) from colCert_64_34_4.bind1,
    show colData2 (⟨64, by decide⟩ : Fin 148)
        ((colE2 ⟨34, by decide⟩ 4 hp : ↥(Q2.reps ⟨34, by decide⟩)) : Coordinate 2)
        Q2.T64_34_2 = colFn colCert_64_34_4.D (m := 5) from colCert_64_34_4.bind2]
  exact alnAll_64_34_4 j hj hq

theorem leaf_64_34_5 (hp : 5 < (Q2.transData.getD 34 []).length)
    (j : Nat) (hj : j < (repChars.getD 64 []).length)
    (hq : (normIsRep.getD 64 []).getD j false = true) :
    species (Q2.reps (⟨34, by decide⟩ : Fin 148)) (colE2 ⟨34, by decide⟩ 5 hp)
        (rowE2 (⟨64, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨34, by decide⟩ : Fin 148))
        (colE1 ⟨34, by decide⟩ 5 (transLenTr ⟨34, by decide⟩ 5 hp))
        (rowE1 (⟨64, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨64, by decide⟩ : Fin 148) ⟨34, by decide⟩ _
      (validAt ⟨64, by decide⟩ (listedAt ⟨64, by decide⟩ hj))
      (colE1 ⟨34, by decide⟩ 5 (transLenTr ⟨34, by decide⟩ 5 hp)) T64_34
      hfix64_34 hinj64_34 hcardT64_34
      (fun i => conj_mem_of_fixedPoints _ _ (T64_34 i) (hfix64_34 i) _)
      ⟨64, by decide⟩ ⟨34, by decide⟩ _
      (Q2.validAt ⟨64, by decide⟩ (Q2.listedAt ⟨64, by decide⟩
        (alnCheck_rep ⟨64, by decide⟩ hj hq).1))
      (colE2 ⟨34, by decide⟩ 5 hp) Q2.T64_34_2 Q2.hfix64_34_2 Q2.hinj64_34_2
      Q2.hcardT64_34_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T64_34_2 i) (Q2.hfix64_34_2 i) _)
      ?_).symm
  rw [show colData1 (⟨64, by decide⟩ : Fin 148)
        ((colE1 ⟨34, by decide⟩ 5 (transLenTr ⟨34, by decide⟩ 5 hp) : ↥(reps ⟨34, by decide⟩)) : Coordinate 1)
        T64_34 = colFn colCert_64_34_5.D (m := 5) from colCert_64_34_5.bind1,
    show colData2 (⟨64, by decide⟩ : Fin 148)
        ((colE2 ⟨34, by decide⟩ 5 hp : ↥(Q2.reps ⟨34, by decide⟩)) : Coordinate 2)
        Q2.T64_34_2 = colFn colCert_64_34_5.D (m := 5) from colCert_64_34_5.bind2]
  exact alnAll_64_34_5 j hj hq

theorem leaf_64_34_10 (hp : 10 < (Q2.transData.getD 34 []).length)
    (j : Nat) (hj : j < (repChars.getD 64 []).length)
    (hq : (normIsRep.getD 64 []).getD j false = true) :
    species (Q2.reps (⟨34, by decide⟩ : Fin 148)) (colE2 ⟨34, by decide⟩ 10 hp)
        (rowE2 (⟨64, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨34, by decide⟩ : Fin 148))
        (colE1 ⟨34, by decide⟩ 10 (transLenTr ⟨34, by decide⟩ 10 hp))
        (rowE1 (⟨64, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨64, by decide⟩ : Fin 148) ⟨34, by decide⟩ _
      (validAt ⟨64, by decide⟩ (listedAt ⟨64, by decide⟩ hj))
      (colE1 ⟨34, by decide⟩ 10 (transLenTr ⟨34, by decide⟩ 10 hp)) T64_34
      hfix64_34 hinj64_34 hcardT64_34
      (fun i => conj_mem_of_fixedPoints _ _ (T64_34 i) (hfix64_34 i) _)
      ⟨64, by decide⟩ ⟨34, by decide⟩ _
      (Q2.validAt ⟨64, by decide⟩ (Q2.listedAt ⟨64, by decide⟩
        (alnCheck_rep ⟨64, by decide⟩ hj hq).1))
      (colE2 ⟨34, by decide⟩ 10 hp) Q2.T64_34_2 Q2.hfix64_34_2 Q2.hinj64_34_2
      Q2.hcardT64_34_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T64_34_2 i) (Q2.hfix64_34_2 i) _)
      ?_).symm
  rw [show colData1 (⟨64, by decide⟩ : Fin 148)
        ((colE1 ⟨34, by decide⟩ 10 (transLenTr ⟨34, by decide⟩ 10 hp) : ↥(reps ⟨34, by decide⟩)) : Coordinate 1)
        T64_34 = colFn colCert_64_34_10.D (m := 5) from colCert_64_34_10.bind1,
    show colData2 (⟨64, by decide⟩ : Fin 148)
        ((colE2 ⟨34, by decide⟩ 10 hp : ↥(Q2.reps ⟨34, by decide⟩)) : Coordinate 2)
        Q2.T64_34_2 = colFn colCert_64_34_10.D (m := 5) from colCert_64_34_10.bind2]
  exact alnAll_64_34_10 j hj hq

theorem leaf_64_34_15 (hp : 15 < (Q2.transData.getD 34 []).length)
    (j : Nat) (hj : j < (repChars.getD 64 []).length)
    (hq : (normIsRep.getD 64 []).getD j false = true) :
    species (Q2.reps (⟨34, by decide⟩ : Fin 148)) (colE2 ⟨34, by decide⟩ 15 hp)
        (rowE2 (⟨64, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨34, by decide⟩ : Fin 148))
        (colE1 ⟨34, by decide⟩ 15 (transLenTr ⟨34, by decide⟩ 15 hp))
        (rowE1 (⟨64, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨64, by decide⟩ : Fin 148) ⟨34, by decide⟩ _
      (validAt ⟨64, by decide⟩ (listedAt ⟨64, by decide⟩ hj))
      (colE1 ⟨34, by decide⟩ 15 (transLenTr ⟨34, by decide⟩ 15 hp)) T64_34
      hfix64_34 hinj64_34 hcardT64_34
      (fun i => conj_mem_of_fixedPoints _ _ (T64_34 i) (hfix64_34 i) _)
      ⟨64, by decide⟩ ⟨34, by decide⟩ _
      (Q2.validAt ⟨64, by decide⟩ (Q2.listedAt ⟨64, by decide⟩
        (alnCheck_rep ⟨64, by decide⟩ hj hq).1))
      (colE2 ⟨34, by decide⟩ 15 hp) Q2.T64_34_2 Q2.hfix64_34_2 Q2.hinj64_34_2
      Q2.hcardT64_34_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T64_34_2 i) (Q2.hfix64_34_2 i) _)
      ?_).symm
  rw [show colData1 (⟨64, by decide⟩ : Fin 148)
        ((colE1 ⟨34, by decide⟩ 15 (transLenTr ⟨34, by decide⟩ 15 hp) : ↥(reps ⟨34, by decide⟩)) : Coordinate 1)
        T64_34 = colFn colCert_64_34_15.D (m := 5) from colCert_64_34_15.bind1,
    show colData2 (⟨64, by decide⟩ : Fin 148)
        ((colE2 ⟨34, by decide⟩ 15 hp : ↥(Q2.reps ⟨34, by decide⟩)) : Coordinate 2)
        Q2.T64_34_2 = colFn colCert_64_34_15.D (m := 5) from colCert_64_34_15.bind2]
  exact alnAll_64_34_15 j hj hq

theorem leaf_64_34_20 (hp : 20 < (Q2.transData.getD 34 []).length)
    (j : Nat) (hj : j < (repChars.getD 64 []).length)
    (hq : (normIsRep.getD 64 []).getD j false = true) :
    species (Q2.reps (⟨34, by decide⟩ : Fin 148)) (colE2 ⟨34, by decide⟩ 20 hp)
        (rowE2 (⟨64, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨34, by decide⟩ : Fin 148))
        (colE1 ⟨34, by decide⟩ 20 (transLenTr ⟨34, by decide⟩ 20 hp))
        (rowE1 (⟨64, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨64, by decide⟩ : Fin 148) ⟨34, by decide⟩ _
      (validAt ⟨64, by decide⟩ (listedAt ⟨64, by decide⟩ hj))
      (colE1 ⟨34, by decide⟩ 20 (transLenTr ⟨34, by decide⟩ 20 hp)) T64_34
      hfix64_34 hinj64_34 hcardT64_34
      (fun i => conj_mem_of_fixedPoints _ _ (T64_34 i) (hfix64_34 i) _)
      ⟨64, by decide⟩ ⟨34, by decide⟩ _
      (Q2.validAt ⟨64, by decide⟩ (Q2.listedAt ⟨64, by decide⟩
        (alnCheck_rep ⟨64, by decide⟩ hj hq).1))
      (colE2 ⟨34, by decide⟩ 20 hp) Q2.T64_34_2 Q2.hfix64_34_2 Q2.hinj64_34_2
      Q2.hcardT64_34_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T64_34_2 i) (Q2.hfix64_34_2 i) _)
      ?_).symm
  rw [show colData1 (⟨64, by decide⟩ : Fin 148)
        ((colE1 ⟨34, by decide⟩ 20 (transLenTr ⟨34, by decide⟩ 20 hp) : ↥(reps ⟨34, by decide⟩)) : Coordinate 1)
        T64_34 = colFn colCert_64_34_20.D (m := 5) from colCert_64_34_20.bind1,
    show colData2 (⟨64, by decide⟩ : Fin 148)
        ((colE2 ⟨34, by decide⟩ 20 hp : ↥(Q2.reps ⟨34, by decide⟩)) : Coordinate 2)
        Q2.T64_34_2 = colFn colCert_64_34_20.D (m := 5) from colCert_64_34_20.bind2]
  exact alnAll_64_34_20 j hj hq

theorem leaf_64_39_0 (hp : 0 < (Q2.transData.getD 39 []).length)
    (j : Nat) (hj : j < (repChars.getD 64 []).length)
    (hq : (normIsRep.getD 64 []).getD j false = true) :
    species (Q2.reps (⟨39, by decide⟩ : Fin 148)) (colE2 ⟨39, by decide⟩ 0 hp)
        (rowE2 (⟨64, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨39, by decide⟩ : Fin 148))
        (colE1 ⟨39, by decide⟩ 0 (transLenTr ⟨39, by decide⟩ 0 hp))
        (rowE1 (⟨64, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨64, by decide⟩ : Fin 148) ⟨39, by decide⟩ _
      (validAt ⟨64, by decide⟩ (listedAt ⟨64, by decide⟩ hj))
      (colE1 ⟨39, by decide⟩ 0 (transLenTr ⟨39, by decide⟩ 0 hp)) T64_39
      hfix64_39 hinj64_39 hcardT64_39
      (fun i => conj_mem_of_fixedPoints _ _ (T64_39 i) (hfix64_39 i) _)
      ⟨64, by decide⟩ ⟨39, by decide⟩ _
      (Q2.validAt ⟨64, by decide⟩ (Q2.listedAt ⟨64, by decide⟩
        (alnCheck_rep ⟨64, by decide⟩ hj hq).1))
      (colE2 ⟨39, by decide⟩ 0 hp) Q2.T64_39_2 Q2.hfix64_39_2 Q2.hinj64_39_2
      Q2.hcardT64_39_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T64_39_2 i) (Q2.hfix64_39_2 i) _)
      ?_).symm
  rw [show colData1 (⟨64, by decide⟩ : Fin 148)
        ((colE1 ⟨39, by decide⟩ 0 (transLenTr ⟨39, by decide⟩ 0 hp) : ↥(reps ⟨39, by decide⟩)) : Coordinate 1)
        T64_39 = colFn colCert_64_39_0.D (m := 5) from colCert_64_39_0.bind1,
    show colData2 (⟨64, by decide⟩ : Fin 148)
        ((colE2 ⟨39, by decide⟩ 0 hp : ↥(Q2.reps ⟨39, by decide⟩)) : Coordinate 2)
        Q2.T64_39_2 = colFn colCert_64_39_0.D (m := 5) from colCert_64_39_0.bind2]
  exact alnAll_64_39_0 j hj hq

theorem leaf_64_39_1 (hp : 1 < (Q2.transData.getD 39 []).length)
    (j : Nat) (hj : j < (repChars.getD 64 []).length)
    (hq : (normIsRep.getD 64 []).getD j false = true) :
    species (Q2.reps (⟨39, by decide⟩ : Fin 148)) (colE2 ⟨39, by decide⟩ 1 hp)
        (rowE2 (⟨64, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨39, by decide⟩ : Fin 148))
        (colE1 ⟨39, by decide⟩ 1 (transLenTr ⟨39, by decide⟩ 1 hp))
        (rowE1 (⟨64, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨64, by decide⟩ : Fin 148) ⟨39, by decide⟩ _
      (validAt ⟨64, by decide⟩ (listedAt ⟨64, by decide⟩ hj))
      (colE1 ⟨39, by decide⟩ 1 (transLenTr ⟨39, by decide⟩ 1 hp)) T64_39
      hfix64_39 hinj64_39 hcardT64_39
      (fun i => conj_mem_of_fixedPoints _ _ (T64_39 i) (hfix64_39 i) _)
      ⟨64, by decide⟩ ⟨39, by decide⟩ _
      (Q2.validAt ⟨64, by decide⟩ (Q2.listedAt ⟨64, by decide⟩
        (alnCheck_rep ⟨64, by decide⟩ hj hq).1))
      (colE2 ⟨39, by decide⟩ 1 hp) Q2.T64_39_2 Q2.hfix64_39_2 Q2.hinj64_39_2
      Q2.hcardT64_39_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T64_39_2 i) (Q2.hfix64_39_2 i) _)
      ?_).symm
  rw [show colData1 (⟨64, by decide⟩ : Fin 148)
        ((colE1 ⟨39, by decide⟩ 1 (transLenTr ⟨39, by decide⟩ 1 hp) : ↥(reps ⟨39, by decide⟩)) : Coordinate 1)
        T64_39 = colFn colCert_64_39_1.D (m := 5) from colCert_64_39_1.bind1,
    show colData2 (⟨64, by decide⟩ : Fin 148)
        ((colE2 ⟨39, by decide⟩ 1 hp : ↥(Q2.reps ⟨39, by decide⟩)) : Coordinate 2)
        Q2.T64_39_2 = colFn colCert_64_39_1.D (m := 5) from colCert_64_39_1.bind2]
  exact alnAll_64_39_1 j hj hq

theorem leaf_64_39_2 (hp : 2 < (Q2.transData.getD 39 []).length)
    (j : Nat) (hj : j < (repChars.getD 64 []).length)
    (hq : (normIsRep.getD 64 []).getD j false = true) :
    species (Q2.reps (⟨39, by decide⟩ : Fin 148)) (colE2 ⟨39, by decide⟩ 2 hp)
        (rowE2 (⟨64, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨39, by decide⟩ : Fin 148))
        (colE1 ⟨39, by decide⟩ 2 (transLenTr ⟨39, by decide⟩ 2 hp))
        (rowE1 (⟨64, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨64, by decide⟩ : Fin 148) ⟨39, by decide⟩ _
      (validAt ⟨64, by decide⟩ (listedAt ⟨64, by decide⟩ hj))
      (colE1 ⟨39, by decide⟩ 2 (transLenTr ⟨39, by decide⟩ 2 hp)) T64_39
      hfix64_39 hinj64_39 hcardT64_39
      (fun i => conj_mem_of_fixedPoints _ _ (T64_39 i) (hfix64_39 i) _)
      ⟨64, by decide⟩ ⟨39, by decide⟩ _
      (Q2.validAt ⟨64, by decide⟩ (Q2.listedAt ⟨64, by decide⟩
        (alnCheck_rep ⟨64, by decide⟩ hj hq).1))
      (colE2 ⟨39, by decide⟩ 2 hp) Q2.T64_39_2 Q2.hfix64_39_2 Q2.hinj64_39_2
      Q2.hcardT64_39_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T64_39_2 i) (Q2.hfix64_39_2 i) _)
      ?_).symm
  rw [show colData1 (⟨64, by decide⟩ : Fin 148)
        ((colE1 ⟨39, by decide⟩ 2 (transLenTr ⟨39, by decide⟩ 2 hp) : ↥(reps ⟨39, by decide⟩)) : Coordinate 1)
        T64_39 = colFn colCert_64_39_2.D (m := 5) from colCert_64_39_2.bind1,
    show colData2 (⟨64, by decide⟩ : Fin 148)
        ((colE2 ⟨39, by decide⟩ 2 hp : ↥(Q2.reps ⟨39, by decide⟩)) : Coordinate 2)
        Q2.T64_39_2 = colFn colCert_64_39_2.D (m := 5) from colCert_64_39_2.bind2]
  exact alnAll_64_39_2 j hj hq

theorem leaf_64_39_3 (hp : 3 < (Q2.transData.getD 39 []).length)
    (j : Nat) (hj : j < (repChars.getD 64 []).length)
    (hq : (normIsRep.getD 64 []).getD j false = true) :
    species (Q2.reps (⟨39, by decide⟩ : Fin 148)) (colE2 ⟨39, by decide⟩ 3 hp)
        (rowE2 (⟨64, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨39, by decide⟩ : Fin 148))
        (colE1 ⟨39, by decide⟩ 3 (transLenTr ⟨39, by decide⟩ 3 hp))
        (rowE1 (⟨64, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨64, by decide⟩ : Fin 148) ⟨39, by decide⟩ _
      (validAt ⟨64, by decide⟩ (listedAt ⟨64, by decide⟩ hj))
      (colE1 ⟨39, by decide⟩ 3 (transLenTr ⟨39, by decide⟩ 3 hp)) T64_39
      hfix64_39 hinj64_39 hcardT64_39
      (fun i => conj_mem_of_fixedPoints _ _ (T64_39 i) (hfix64_39 i) _)
      ⟨64, by decide⟩ ⟨39, by decide⟩ _
      (Q2.validAt ⟨64, by decide⟩ (Q2.listedAt ⟨64, by decide⟩
        (alnCheck_rep ⟨64, by decide⟩ hj hq).1))
      (colE2 ⟨39, by decide⟩ 3 hp) Q2.T64_39_2 Q2.hfix64_39_2 Q2.hinj64_39_2
      Q2.hcardT64_39_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T64_39_2 i) (Q2.hfix64_39_2 i) _)
      ?_).symm
  rw [show colData1 (⟨64, by decide⟩ : Fin 148)
        ((colE1 ⟨39, by decide⟩ 3 (transLenTr ⟨39, by decide⟩ 3 hp) : ↥(reps ⟨39, by decide⟩)) : Coordinate 1)
        T64_39 = colFn colCert_64_39_3.D (m := 5) from colCert_64_39_3.bind1,
    show colData2 (⟨64, by decide⟩ : Fin 148)
        ((colE2 ⟨39, by decide⟩ 3 hp : ↥(Q2.reps ⟨39, by decide⟩)) : Coordinate 2)
        Q2.T64_39_2 = colFn colCert_64_39_3.D (m := 5) from colCert_64_39_3.bind2]
  exact alnAll_64_39_3 j hj hq

theorem leaf_64_39_4 (hp : 4 < (Q2.transData.getD 39 []).length)
    (j : Nat) (hj : j < (repChars.getD 64 []).length)
    (hq : (normIsRep.getD 64 []).getD j false = true) :
    species (Q2.reps (⟨39, by decide⟩ : Fin 148)) (colE2 ⟨39, by decide⟩ 4 hp)
        (rowE2 (⟨64, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨39, by decide⟩ : Fin 148))
        (colE1 ⟨39, by decide⟩ 4 (transLenTr ⟨39, by decide⟩ 4 hp))
        (rowE1 (⟨64, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨64, by decide⟩ : Fin 148) ⟨39, by decide⟩ _
      (validAt ⟨64, by decide⟩ (listedAt ⟨64, by decide⟩ hj))
      (colE1 ⟨39, by decide⟩ 4 (transLenTr ⟨39, by decide⟩ 4 hp)) T64_39
      hfix64_39 hinj64_39 hcardT64_39
      (fun i => conj_mem_of_fixedPoints _ _ (T64_39 i) (hfix64_39 i) _)
      ⟨64, by decide⟩ ⟨39, by decide⟩ _
      (Q2.validAt ⟨64, by decide⟩ (Q2.listedAt ⟨64, by decide⟩
        (alnCheck_rep ⟨64, by decide⟩ hj hq).1))
      (colE2 ⟨39, by decide⟩ 4 hp) Q2.T64_39_2 Q2.hfix64_39_2 Q2.hinj64_39_2
      Q2.hcardT64_39_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T64_39_2 i) (Q2.hfix64_39_2 i) _)
      ?_).symm
  rw [show colData1 (⟨64, by decide⟩ : Fin 148)
        ((colE1 ⟨39, by decide⟩ 4 (transLenTr ⟨39, by decide⟩ 4 hp) : ↥(reps ⟨39, by decide⟩)) : Coordinate 1)
        T64_39 = colFn colCert_64_39_4.D (m := 5) from colCert_64_39_4.bind1,
    show colData2 (⟨64, by decide⟩ : Fin 148)
        ((colE2 ⟨39, by decide⟩ 4 hp : ↥(Q2.reps ⟨39, by decide⟩)) : Coordinate 2)
        Q2.T64_39_2 = colFn colCert_64_39_4.D (m := 5) from colCert_64_39_4.bind2]
  exact alnAll_64_39_4 j hj hq

theorem leaf_64_39_5 (hp : 5 < (Q2.transData.getD 39 []).length)
    (j : Nat) (hj : j < (repChars.getD 64 []).length)
    (hq : (normIsRep.getD 64 []).getD j false = true) :
    species (Q2.reps (⟨39, by decide⟩ : Fin 148)) (colE2 ⟨39, by decide⟩ 5 hp)
        (rowE2 (⟨64, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨39, by decide⟩ : Fin 148))
        (colE1 ⟨39, by decide⟩ 5 (transLenTr ⟨39, by decide⟩ 5 hp))
        (rowE1 (⟨64, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨64, by decide⟩ : Fin 148) ⟨39, by decide⟩ _
      (validAt ⟨64, by decide⟩ (listedAt ⟨64, by decide⟩ hj))
      (colE1 ⟨39, by decide⟩ 5 (transLenTr ⟨39, by decide⟩ 5 hp)) T64_39
      hfix64_39 hinj64_39 hcardT64_39
      (fun i => conj_mem_of_fixedPoints _ _ (T64_39 i) (hfix64_39 i) _)
      ⟨64, by decide⟩ ⟨39, by decide⟩ _
      (Q2.validAt ⟨64, by decide⟩ (Q2.listedAt ⟨64, by decide⟩
        (alnCheck_rep ⟨64, by decide⟩ hj hq).1))
      (colE2 ⟨39, by decide⟩ 5 hp) Q2.T64_39_2 Q2.hfix64_39_2 Q2.hinj64_39_2
      Q2.hcardT64_39_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T64_39_2 i) (Q2.hfix64_39_2 i) _)
      ?_).symm
  rw [show colData1 (⟨64, by decide⟩ : Fin 148)
        ((colE1 ⟨39, by decide⟩ 5 (transLenTr ⟨39, by decide⟩ 5 hp) : ↥(reps ⟨39, by decide⟩)) : Coordinate 1)
        T64_39 = colFn colCert_64_39_5.D (m := 5) from colCert_64_39_5.bind1,
    show colData2 (⟨64, by decide⟩ : Fin 148)
        ((colE2 ⟨39, by decide⟩ 5 hp : ↥(Q2.reps ⟨39, by decide⟩)) : Coordinate 2)
        Q2.T64_39_2 = colFn colCert_64_39_5.D (m := 5) from colCert_64_39_5.bind2]
  exact alnAll_64_39_5 j hj hq

theorem leaf_64_39_10 (hp : 10 < (Q2.transData.getD 39 []).length)
    (j : Nat) (hj : j < (repChars.getD 64 []).length)
    (hq : (normIsRep.getD 64 []).getD j false = true) :
    species (Q2.reps (⟨39, by decide⟩ : Fin 148)) (colE2 ⟨39, by decide⟩ 10 hp)
        (rowE2 (⟨64, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨39, by decide⟩ : Fin 148))
        (colE1 ⟨39, by decide⟩ 10 (transLenTr ⟨39, by decide⟩ 10 hp))
        (rowE1 (⟨64, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨64, by decide⟩ : Fin 148) ⟨39, by decide⟩ _
      (validAt ⟨64, by decide⟩ (listedAt ⟨64, by decide⟩ hj))
      (colE1 ⟨39, by decide⟩ 10 (transLenTr ⟨39, by decide⟩ 10 hp)) T64_39
      hfix64_39 hinj64_39 hcardT64_39
      (fun i => conj_mem_of_fixedPoints _ _ (T64_39 i) (hfix64_39 i) _)
      ⟨64, by decide⟩ ⟨39, by decide⟩ _
      (Q2.validAt ⟨64, by decide⟩ (Q2.listedAt ⟨64, by decide⟩
        (alnCheck_rep ⟨64, by decide⟩ hj hq).1))
      (colE2 ⟨39, by decide⟩ 10 hp) Q2.T64_39_2 Q2.hfix64_39_2 Q2.hinj64_39_2
      Q2.hcardT64_39_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T64_39_2 i) (Q2.hfix64_39_2 i) _)
      ?_).symm
  rw [show colData1 (⟨64, by decide⟩ : Fin 148)
        ((colE1 ⟨39, by decide⟩ 10 (transLenTr ⟨39, by decide⟩ 10 hp) : ↥(reps ⟨39, by decide⟩)) : Coordinate 1)
        T64_39 = colFn colCert_64_39_10.D (m := 5) from colCert_64_39_10.bind1,
    show colData2 (⟨64, by decide⟩ : Fin 148)
        ((colE2 ⟨39, by decide⟩ 10 hp : ↥(Q2.reps ⟨39, by decide⟩)) : Coordinate 2)
        Q2.T64_39_2 = colFn colCert_64_39_10.D (m := 5) from colCert_64_39_10.bind2]
  exact alnAll_64_39_10 j hj hq

theorem leaf_64_39_15 (hp : 15 < (Q2.transData.getD 39 []).length)
    (j : Nat) (hj : j < (repChars.getD 64 []).length)
    (hq : (normIsRep.getD 64 []).getD j false = true) :
    species (Q2.reps (⟨39, by decide⟩ : Fin 148)) (colE2 ⟨39, by decide⟩ 15 hp)
        (rowE2 (⟨64, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨39, by decide⟩ : Fin 148))
        (colE1 ⟨39, by decide⟩ 15 (transLenTr ⟨39, by decide⟩ 15 hp))
        (rowE1 (⟨64, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨64, by decide⟩ : Fin 148) ⟨39, by decide⟩ _
      (validAt ⟨64, by decide⟩ (listedAt ⟨64, by decide⟩ hj))
      (colE1 ⟨39, by decide⟩ 15 (transLenTr ⟨39, by decide⟩ 15 hp)) T64_39
      hfix64_39 hinj64_39 hcardT64_39
      (fun i => conj_mem_of_fixedPoints _ _ (T64_39 i) (hfix64_39 i) _)
      ⟨64, by decide⟩ ⟨39, by decide⟩ _
      (Q2.validAt ⟨64, by decide⟩ (Q2.listedAt ⟨64, by decide⟩
        (alnCheck_rep ⟨64, by decide⟩ hj hq).1))
      (colE2 ⟨39, by decide⟩ 15 hp) Q2.T64_39_2 Q2.hfix64_39_2 Q2.hinj64_39_2
      Q2.hcardT64_39_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T64_39_2 i) (Q2.hfix64_39_2 i) _)
      ?_).symm
  rw [show colData1 (⟨64, by decide⟩ : Fin 148)
        ((colE1 ⟨39, by decide⟩ 15 (transLenTr ⟨39, by decide⟩ 15 hp) : ↥(reps ⟨39, by decide⟩)) : Coordinate 1)
        T64_39 = colFn colCert_64_39_15.D (m := 5) from colCert_64_39_15.bind1,
    show colData2 (⟨64, by decide⟩ : Fin 148)
        ((colE2 ⟨39, by decide⟩ 15 hp : ↥(Q2.reps ⟨39, by decide⟩)) : Coordinate 2)
        Q2.T64_39_2 = colFn colCert_64_39_15.D (m := 5) from colCert_64_39_15.bind2]
  exact alnAll_64_39_15 j hj hq

theorem leaf_64_39_20 (hp : 20 < (Q2.transData.getD 39 []).length)
    (j : Nat) (hj : j < (repChars.getD 64 []).length)
    (hq : (normIsRep.getD 64 []).getD j false = true) :
    species (Q2.reps (⟨39, by decide⟩ : Fin 148)) (colE2 ⟨39, by decide⟩ 20 hp)
        (rowE2 (⟨64, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨39, by decide⟩ : Fin 148))
        (colE1 ⟨39, by decide⟩ 20 (transLenTr ⟨39, by decide⟩ 20 hp))
        (rowE1 (⟨64, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨64, by decide⟩ : Fin 148) ⟨39, by decide⟩ _
      (validAt ⟨64, by decide⟩ (listedAt ⟨64, by decide⟩ hj))
      (colE1 ⟨39, by decide⟩ 20 (transLenTr ⟨39, by decide⟩ 20 hp)) T64_39
      hfix64_39 hinj64_39 hcardT64_39
      (fun i => conj_mem_of_fixedPoints _ _ (T64_39 i) (hfix64_39 i) _)
      ⟨64, by decide⟩ ⟨39, by decide⟩ _
      (Q2.validAt ⟨64, by decide⟩ (Q2.listedAt ⟨64, by decide⟩
        (alnCheck_rep ⟨64, by decide⟩ hj hq).1))
      (colE2 ⟨39, by decide⟩ 20 hp) Q2.T64_39_2 Q2.hfix64_39_2 Q2.hinj64_39_2
      Q2.hcardT64_39_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T64_39_2 i) (Q2.hfix64_39_2 i) _)
      ?_).symm
  rw [show colData1 (⟨64, by decide⟩ : Fin 148)
        ((colE1 ⟨39, by decide⟩ 20 (transLenTr ⟨39, by decide⟩ 20 hp) : ↥(reps ⟨39, by decide⟩)) : Coordinate 1)
        T64_39 = colFn colCert_64_39_20.D (m := 5) from colCert_64_39_20.bind1,
    show colData2 (⟨64, by decide⟩ : Fin 148)
        ((colE2 ⟨39, by decide⟩ 20 hp : ↥(Q2.reps ⟨39, by decide⟩)) : Coordinate 2)
        Q2.T64_39_2 = colFn colCert_64_39_20.D (m := 5) from colCert_64_39_20.bind2]
  exact alnAll_64_39_20 j hj hq

theorem leaf_64_44_0 (hp : 0 < (Q2.transData.getD 44 []).length)
    (j : Nat) (hj : j < (repChars.getD 64 []).length)
    (hq : (normIsRep.getD 64 []).getD j false = true) :
    species (Q2.reps (⟨44, by decide⟩ : Fin 148)) (colE2 ⟨44, by decide⟩ 0 hp)
        (rowE2 (⟨64, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨44, by decide⟩ : Fin 148))
        (colE1 ⟨44, by decide⟩ 0 (transLenTr ⟨44, by decide⟩ 0 hp))
        (rowE1 (⟨64, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨64, by decide⟩ : Fin 148) ⟨44, by decide⟩ _
      (validAt ⟨64, by decide⟩ (listedAt ⟨64, by decide⟩ hj))
      (colE1 ⟨44, by decide⟩ 0 (transLenTr ⟨44, by decide⟩ 0 hp)) T64_44
      hfix64_44 hinj64_44 hcardT64_44
      (fun i => conj_mem_of_fixedPoints _ _ (T64_44 i) (hfix64_44 i) _)
      ⟨64, by decide⟩ ⟨44, by decide⟩ _
      (Q2.validAt ⟨64, by decide⟩ (Q2.listedAt ⟨64, by decide⟩
        (alnCheck_rep ⟨64, by decide⟩ hj hq).1))
      (colE2 ⟨44, by decide⟩ 0 hp) Q2.T64_44_2 Q2.hfix64_44_2 Q2.hinj64_44_2
      Q2.hcardT64_44_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T64_44_2 i) (Q2.hfix64_44_2 i) _)
      ?_).symm
  rw [show colData1 (⟨64, by decide⟩ : Fin 148)
        ((colE1 ⟨44, by decide⟩ 0 (transLenTr ⟨44, by decide⟩ 0 hp) : ↥(reps ⟨44, by decide⟩)) : Coordinate 1)
        T64_44 = colFn colCert_64_44_0.D (m := 5) from colCert_64_44_0.bind1,
    show colData2 (⟨64, by decide⟩ : Fin 148)
        ((colE2 ⟨44, by decide⟩ 0 hp : ↥(Q2.reps ⟨44, by decide⟩)) : Coordinate 2)
        Q2.T64_44_2 = colFn colCert_64_44_0.D (m := 5) from colCert_64_44_0.bind2]
  exact alnAll_64_44_0 j hj hq

theorem leaf_64_44_1 (hp : 1 < (Q2.transData.getD 44 []).length)
    (j : Nat) (hj : j < (repChars.getD 64 []).length)
    (hq : (normIsRep.getD 64 []).getD j false = true) :
    species (Q2.reps (⟨44, by decide⟩ : Fin 148)) (colE2 ⟨44, by decide⟩ 1 hp)
        (rowE2 (⟨64, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨44, by decide⟩ : Fin 148))
        (colE1 ⟨44, by decide⟩ 1 (transLenTr ⟨44, by decide⟩ 1 hp))
        (rowE1 (⟨64, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨64, by decide⟩ : Fin 148) ⟨44, by decide⟩ _
      (validAt ⟨64, by decide⟩ (listedAt ⟨64, by decide⟩ hj))
      (colE1 ⟨44, by decide⟩ 1 (transLenTr ⟨44, by decide⟩ 1 hp)) T64_44
      hfix64_44 hinj64_44 hcardT64_44
      (fun i => conj_mem_of_fixedPoints _ _ (T64_44 i) (hfix64_44 i) _)
      ⟨64, by decide⟩ ⟨44, by decide⟩ _
      (Q2.validAt ⟨64, by decide⟩ (Q2.listedAt ⟨64, by decide⟩
        (alnCheck_rep ⟨64, by decide⟩ hj hq).1))
      (colE2 ⟨44, by decide⟩ 1 hp) Q2.T64_44_2 Q2.hfix64_44_2 Q2.hinj64_44_2
      Q2.hcardT64_44_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T64_44_2 i) (Q2.hfix64_44_2 i) _)
      ?_).symm
  rw [show colData1 (⟨64, by decide⟩ : Fin 148)
        ((colE1 ⟨44, by decide⟩ 1 (transLenTr ⟨44, by decide⟩ 1 hp) : ↥(reps ⟨44, by decide⟩)) : Coordinate 1)
        T64_44 = colFn colCert_64_44_1.D (m := 5) from colCert_64_44_1.bind1,
    show colData2 (⟨64, by decide⟩ : Fin 148)
        ((colE2 ⟨44, by decide⟩ 1 hp : ↥(Q2.reps ⟨44, by decide⟩)) : Coordinate 2)
        Q2.T64_44_2 = colFn colCert_64_44_1.D (m := 5) from colCert_64_44_1.bind2]
  exact alnAll_64_44_1 j hj hq

theorem leaf_64_44_2 (hp : 2 < (Q2.transData.getD 44 []).length)
    (j : Nat) (hj : j < (repChars.getD 64 []).length)
    (hq : (normIsRep.getD 64 []).getD j false = true) :
    species (Q2.reps (⟨44, by decide⟩ : Fin 148)) (colE2 ⟨44, by decide⟩ 2 hp)
        (rowE2 (⟨64, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨44, by decide⟩ : Fin 148))
        (colE1 ⟨44, by decide⟩ 2 (transLenTr ⟨44, by decide⟩ 2 hp))
        (rowE1 (⟨64, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨64, by decide⟩ : Fin 148) ⟨44, by decide⟩ _
      (validAt ⟨64, by decide⟩ (listedAt ⟨64, by decide⟩ hj))
      (colE1 ⟨44, by decide⟩ 2 (transLenTr ⟨44, by decide⟩ 2 hp)) T64_44
      hfix64_44 hinj64_44 hcardT64_44
      (fun i => conj_mem_of_fixedPoints _ _ (T64_44 i) (hfix64_44 i) _)
      ⟨64, by decide⟩ ⟨44, by decide⟩ _
      (Q2.validAt ⟨64, by decide⟩ (Q2.listedAt ⟨64, by decide⟩
        (alnCheck_rep ⟨64, by decide⟩ hj hq).1))
      (colE2 ⟨44, by decide⟩ 2 hp) Q2.T64_44_2 Q2.hfix64_44_2 Q2.hinj64_44_2
      Q2.hcardT64_44_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T64_44_2 i) (Q2.hfix64_44_2 i) _)
      ?_).symm
  rw [show colData1 (⟨64, by decide⟩ : Fin 148)
        ((colE1 ⟨44, by decide⟩ 2 (transLenTr ⟨44, by decide⟩ 2 hp) : ↥(reps ⟨44, by decide⟩)) : Coordinate 1)
        T64_44 = colFn colCert_64_44_2.D (m := 5) from colCert_64_44_2.bind1,
    show colData2 (⟨64, by decide⟩ : Fin 148)
        ((colE2 ⟨44, by decide⟩ 2 hp : ↥(Q2.reps ⟨44, by decide⟩)) : Coordinate 2)
        Q2.T64_44_2 = colFn colCert_64_44_2.D (m := 5) from colCert_64_44_2.bind2]
  exact alnAll_64_44_2 j hj hq

theorem leaf_64_44_3 (hp : 3 < (Q2.transData.getD 44 []).length)
    (j : Nat) (hj : j < (repChars.getD 64 []).length)
    (hq : (normIsRep.getD 64 []).getD j false = true) :
    species (Q2.reps (⟨44, by decide⟩ : Fin 148)) (colE2 ⟨44, by decide⟩ 3 hp)
        (rowE2 (⟨64, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨44, by decide⟩ : Fin 148))
        (colE1 ⟨44, by decide⟩ 3 (transLenTr ⟨44, by decide⟩ 3 hp))
        (rowE1 (⟨64, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨64, by decide⟩ : Fin 148) ⟨44, by decide⟩ _
      (validAt ⟨64, by decide⟩ (listedAt ⟨64, by decide⟩ hj))
      (colE1 ⟨44, by decide⟩ 3 (transLenTr ⟨44, by decide⟩ 3 hp)) T64_44
      hfix64_44 hinj64_44 hcardT64_44
      (fun i => conj_mem_of_fixedPoints _ _ (T64_44 i) (hfix64_44 i) _)
      ⟨64, by decide⟩ ⟨44, by decide⟩ _
      (Q2.validAt ⟨64, by decide⟩ (Q2.listedAt ⟨64, by decide⟩
        (alnCheck_rep ⟨64, by decide⟩ hj hq).1))
      (colE2 ⟨44, by decide⟩ 3 hp) Q2.T64_44_2 Q2.hfix64_44_2 Q2.hinj64_44_2
      Q2.hcardT64_44_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T64_44_2 i) (Q2.hfix64_44_2 i) _)
      ?_).symm
  rw [show colData1 (⟨64, by decide⟩ : Fin 148)
        ((colE1 ⟨44, by decide⟩ 3 (transLenTr ⟨44, by decide⟩ 3 hp) : ↥(reps ⟨44, by decide⟩)) : Coordinate 1)
        T64_44 = colFn colCert_64_44_3.D (m := 5) from colCert_64_44_3.bind1,
    show colData2 (⟨64, by decide⟩ : Fin 148)
        ((colE2 ⟨44, by decide⟩ 3 hp : ↥(Q2.reps ⟨44, by decide⟩)) : Coordinate 2)
        Q2.T64_44_2 = colFn colCert_64_44_3.D (m := 5) from colCert_64_44_3.bind2]
  exact alnAll_64_44_3 j hj hq

theorem leaf_64_44_4 (hp : 4 < (Q2.transData.getD 44 []).length)
    (j : Nat) (hj : j < (repChars.getD 64 []).length)
    (hq : (normIsRep.getD 64 []).getD j false = true) :
    species (Q2.reps (⟨44, by decide⟩ : Fin 148)) (colE2 ⟨44, by decide⟩ 4 hp)
        (rowE2 (⟨64, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨44, by decide⟩ : Fin 148))
        (colE1 ⟨44, by decide⟩ 4 (transLenTr ⟨44, by decide⟩ 4 hp))
        (rowE1 (⟨64, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨64, by decide⟩ : Fin 148) ⟨44, by decide⟩ _
      (validAt ⟨64, by decide⟩ (listedAt ⟨64, by decide⟩ hj))
      (colE1 ⟨44, by decide⟩ 4 (transLenTr ⟨44, by decide⟩ 4 hp)) T64_44
      hfix64_44 hinj64_44 hcardT64_44
      (fun i => conj_mem_of_fixedPoints _ _ (T64_44 i) (hfix64_44 i) _)
      ⟨64, by decide⟩ ⟨44, by decide⟩ _
      (Q2.validAt ⟨64, by decide⟩ (Q2.listedAt ⟨64, by decide⟩
        (alnCheck_rep ⟨64, by decide⟩ hj hq).1))
      (colE2 ⟨44, by decide⟩ 4 hp) Q2.T64_44_2 Q2.hfix64_44_2 Q2.hinj64_44_2
      Q2.hcardT64_44_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T64_44_2 i) (Q2.hfix64_44_2 i) _)
      ?_).symm
  rw [show colData1 (⟨64, by decide⟩ : Fin 148)
        ((colE1 ⟨44, by decide⟩ 4 (transLenTr ⟨44, by decide⟩ 4 hp) : ↥(reps ⟨44, by decide⟩)) : Coordinate 1)
        T64_44 = colFn colCert_64_44_4.D (m := 5) from colCert_64_44_4.bind1,
    show colData2 (⟨64, by decide⟩ : Fin 148)
        ((colE2 ⟨44, by decide⟩ 4 hp : ↥(Q2.reps ⟨44, by decide⟩)) : Coordinate 2)
        Q2.T64_44_2 = colFn colCert_64_44_4.D (m := 5) from colCert_64_44_4.bind2]
  exact alnAll_64_44_4 j hj hq

theorem leaf_64_44_5 (hp : 5 < (Q2.transData.getD 44 []).length)
    (j : Nat) (hj : j < (repChars.getD 64 []).length)
    (hq : (normIsRep.getD 64 []).getD j false = true) :
    species (Q2.reps (⟨44, by decide⟩ : Fin 148)) (colE2 ⟨44, by decide⟩ 5 hp)
        (rowE2 (⟨64, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨44, by decide⟩ : Fin 148))
        (colE1 ⟨44, by decide⟩ 5 (transLenTr ⟨44, by decide⟩ 5 hp))
        (rowE1 (⟨64, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨64, by decide⟩ : Fin 148) ⟨44, by decide⟩ _
      (validAt ⟨64, by decide⟩ (listedAt ⟨64, by decide⟩ hj))
      (colE1 ⟨44, by decide⟩ 5 (transLenTr ⟨44, by decide⟩ 5 hp)) T64_44
      hfix64_44 hinj64_44 hcardT64_44
      (fun i => conj_mem_of_fixedPoints _ _ (T64_44 i) (hfix64_44 i) _)
      ⟨64, by decide⟩ ⟨44, by decide⟩ _
      (Q2.validAt ⟨64, by decide⟩ (Q2.listedAt ⟨64, by decide⟩
        (alnCheck_rep ⟨64, by decide⟩ hj hq).1))
      (colE2 ⟨44, by decide⟩ 5 hp) Q2.T64_44_2 Q2.hfix64_44_2 Q2.hinj64_44_2
      Q2.hcardT64_44_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T64_44_2 i) (Q2.hfix64_44_2 i) _)
      ?_).symm
  rw [show colData1 (⟨64, by decide⟩ : Fin 148)
        ((colE1 ⟨44, by decide⟩ 5 (transLenTr ⟨44, by decide⟩ 5 hp) : ↥(reps ⟨44, by decide⟩)) : Coordinate 1)
        T64_44 = colFn colCert_64_44_5.D (m := 5) from colCert_64_44_5.bind1,
    show colData2 (⟨64, by decide⟩ : Fin 148)
        ((colE2 ⟨44, by decide⟩ 5 hp : ↥(Q2.reps ⟨44, by decide⟩)) : Coordinate 2)
        Q2.T64_44_2 = colFn colCert_64_44_5.D (m := 5) from colCert_64_44_5.bind2]
  exact alnAll_64_44_5 j hj hq

theorem leaf_64_44_10 (hp : 10 < (Q2.transData.getD 44 []).length)
    (j : Nat) (hj : j < (repChars.getD 64 []).length)
    (hq : (normIsRep.getD 64 []).getD j false = true) :
    species (Q2.reps (⟨44, by decide⟩ : Fin 148)) (colE2 ⟨44, by decide⟩ 10 hp)
        (rowE2 (⟨64, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨44, by decide⟩ : Fin 148))
        (colE1 ⟨44, by decide⟩ 10 (transLenTr ⟨44, by decide⟩ 10 hp))
        (rowE1 (⟨64, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨64, by decide⟩ : Fin 148) ⟨44, by decide⟩ _
      (validAt ⟨64, by decide⟩ (listedAt ⟨64, by decide⟩ hj))
      (colE1 ⟨44, by decide⟩ 10 (transLenTr ⟨44, by decide⟩ 10 hp)) T64_44
      hfix64_44 hinj64_44 hcardT64_44
      (fun i => conj_mem_of_fixedPoints _ _ (T64_44 i) (hfix64_44 i) _)
      ⟨64, by decide⟩ ⟨44, by decide⟩ _
      (Q2.validAt ⟨64, by decide⟩ (Q2.listedAt ⟨64, by decide⟩
        (alnCheck_rep ⟨64, by decide⟩ hj hq).1))
      (colE2 ⟨44, by decide⟩ 10 hp) Q2.T64_44_2 Q2.hfix64_44_2 Q2.hinj64_44_2
      Q2.hcardT64_44_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T64_44_2 i) (Q2.hfix64_44_2 i) _)
      ?_).symm
  rw [show colData1 (⟨64, by decide⟩ : Fin 148)
        ((colE1 ⟨44, by decide⟩ 10 (transLenTr ⟨44, by decide⟩ 10 hp) : ↥(reps ⟨44, by decide⟩)) : Coordinate 1)
        T64_44 = colFn colCert_64_44_10.D (m := 5) from colCert_64_44_10.bind1,
    show colData2 (⟨64, by decide⟩ : Fin 148)
        ((colE2 ⟨44, by decide⟩ 10 hp : ↥(Q2.reps ⟨44, by decide⟩)) : Coordinate 2)
        Q2.T64_44_2 = colFn colCert_64_44_10.D (m := 5) from colCert_64_44_10.bind2]
  exact alnAll_64_44_10 j hj hq

theorem leaf_64_44_15 (hp : 15 < (Q2.transData.getD 44 []).length)
    (j : Nat) (hj : j < (repChars.getD 64 []).length)
    (hq : (normIsRep.getD 64 []).getD j false = true) :
    species (Q2.reps (⟨44, by decide⟩ : Fin 148)) (colE2 ⟨44, by decide⟩ 15 hp)
        (rowE2 (⟨64, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨44, by decide⟩ : Fin 148))
        (colE1 ⟨44, by decide⟩ 15 (transLenTr ⟨44, by decide⟩ 15 hp))
        (rowE1 (⟨64, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨64, by decide⟩ : Fin 148) ⟨44, by decide⟩ _
      (validAt ⟨64, by decide⟩ (listedAt ⟨64, by decide⟩ hj))
      (colE1 ⟨44, by decide⟩ 15 (transLenTr ⟨44, by decide⟩ 15 hp)) T64_44
      hfix64_44 hinj64_44 hcardT64_44
      (fun i => conj_mem_of_fixedPoints _ _ (T64_44 i) (hfix64_44 i) _)
      ⟨64, by decide⟩ ⟨44, by decide⟩ _
      (Q2.validAt ⟨64, by decide⟩ (Q2.listedAt ⟨64, by decide⟩
        (alnCheck_rep ⟨64, by decide⟩ hj hq).1))
      (colE2 ⟨44, by decide⟩ 15 hp) Q2.T64_44_2 Q2.hfix64_44_2 Q2.hinj64_44_2
      Q2.hcardT64_44_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T64_44_2 i) (Q2.hfix64_44_2 i) _)
      ?_).symm
  rw [show colData1 (⟨64, by decide⟩ : Fin 148)
        ((colE1 ⟨44, by decide⟩ 15 (transLenTr ⟨44, by decide⟩ 15 hp) : ↥(reps ⟨44, by decide⟩)) : Coordinate 1)
        T64_44 = colFn colCert_64_44_15.D (m := 5) from colCert_64_44_15.bind1,
    show colData2 (⟨64, by decide⟩ : Fin 148)
        ((colE2 ⟨44, by decide⟩ 15 hp : ↥(Q2.reps ⟨44, by decide⟩)) : Coordinate 2)
        Q2.T64_44_2 = colFn colCert_64_44_15.D (m := 5) from colCert_64_44_15.bind2]
  exact alnAll_64_44_15 j hj hq

theorem leaf_64_44_20 (hp : 20 < (Q2.transData.getD 44 []).length)
    (j : Nat) (hj : j < (repChars.getD 64 []).length)
    (hq : (normIsRep.getD 64 []).getD j false = true) :
    species (Q2.reps (⟨44, by decide⟩ : Fin 148)) (colE2 ⟨44, by decide⟩ 20 hp)
        (rowE2 (⟨64, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨44, by decide⟩ : Fin 148))
        (colE1 ⟨44, by decide⟩ 20 (transLenTr ⟨44, by decide⟩ 20 hp))
        (rowE1 (⟨64, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨64, by decide⟩ : Fin 148) ⟨44, by decide⟩ _
      (validAt ⟨64, by decide⟩ (listedAt ⟨64, by decide⟩ hj))
      (colE1 ⟨44, by decide⟩ 20 (transLenTr ⟨44, by decide⟩ 20 hp)) T64_44
      hfix64_44 hinj64_44 hcardT64_44
      (fun i => conj_mem_of_fixedPoints _ _ (T64_44 i) (hfix64_44 i) _)
      ⟨64, by decide⟩ ⟨44, by decide⟩ _
      (Q2.validAt ⟨64, by decide⟩ (Q2.listedAt ⟨64, by decide⟩
        (alnCheck_rep ⟨64, by decide⟩ hj hq).1))
      (colE2 ⟨44, by decide⟩ 20 hp) Q2.T64_44_2 Q2.hfix64_44_2 Q2.hinj64_44_2
      Q2.hcardT64_44_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T64_44_2 i) (Q2.hfix64_44_2 i) _)
      ?_).symm
  rw [show colData1 (⟨64, by decide⟩ : Fin 148)
        ((colE1 ⟨44, by decide⟩ 20 (transLenTr ⟨44, by decide⟩ 20 hp) : ↥(reps ⟨44, by decide⟩)) : Coordinate 1)
        T64_44 = colFn colCert_64_44_20.D (m := 5) from colCert_64_44_20.bind1,
    show colData2 (⟨64, by decide⟩ : Fin 148)
        ((colE2 ⟨44, by decide⟩ 20 hp : ↥(Q2.reps ⟨44, by decide⟩)) : Coordinate 2)
        Q2.T64_44_2 = colFn colCert_64_44_20.D (m := 5) from colCert_64_44_20.bind2]
  exact alnAll_64_44_20 j hj hq

theorem leaf_64_49_0 (hp : 0 < (Q2.transData.getD 49 []).length)
    (j : Nat) (hj : j < (repChars.getD 64 []).length)
    (hq : (normIsRep.getD 64 []).getD j false = true) :
    species (Q2.reps (⟨49, by decide⟩ : Fin 148)) (colE2 ⟨49, by decide⟩ 0 hp)
        (rowE2 (⟨64, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨49, by decide⟩ : Fin 148))
        (colE1 ⟨49, by decide⟩ 0 (transLenTr ⟨49, by decide⟩ 0 hp))
        (rowE1 (⟨64, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨64, by decide⟩ : Fin 148) ⟨49, by decide⟩ _
      (validAt ⟨64, by decide⟩ (listedAt ⟨64, by decide⟩ hj))
      (colE1 ⟨49, by decide⟩ 0 (transLenTr ⟨49, by decide⟩ 0 hp)) T64_49
      hfix64_49 hinj64_49 hcardT64_49
      (fun i => conj_mem_of_fixedPoints _ _ (T64_49 i) (hfix64_49 i) _)
      ⟨64, by decide⟩ ⟨49, by decide⟩ _
      (Q2.validAt ⟨64, by decide⟩ (Q2.listedAt ⟨64, by decide⟩
        (alnCheck_rep ⟨64, by decide⟩ hj hq).1))
      (colE2 ⟨49, by decide⟩ 0 hp) Q2.T64_49_2 Q2.hfix64_49_2 Q2.hinj64_49_2
      Q2.hcardT64_49_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T64_49_2 i) (Q2.hfix64_49_2 i) _)
      ?_).symm
  rw [show colData1 (⟨64, by decide⟩ : Fin 148)
        ((colE1 ⟨49, by decide⟩ 0 (transLenTr ⟨49, by decide⟩ 0 hp) : ↥(reps ⟨49, by decide⟩)) : Coordinate 1)
        T64_49 = colFn colCert_64_49_0.D (m := 5) from colCert_64_49_0.bind1,
    show colData2 (⟨64, by decide⟩ : Fin 148)
        ((colE2 ⟨49, by decide⟩ 0 hp : ↥(Q2.reps ⟨49, by decide⟩)) : Coordinate 2)
        Q2.T64_49_2 = colFn colCert_64_49_0.D (m := 5) from colCert_64_49_0.bind2]
  exact alnAll_64_49_0 j hj hq

theorem leaf_64_49_1 (hp : 1 < (Q2.transData.getD 49 []).length)
    (j : Nat) (hj : j < (repChars.getD 64 []).length)
    (hq : (normIsRep.getD 64 []).getD j false = true) :
    species (Q2.reps (⟨49, by decide⟩ : Fin 148)) (colE2 ⟨49, by decide⟩ 1 hp)
        (rowE2 (⟨64, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨49, by decide⟩ : Fin 148))
        (colE1 ⟨49, by decide⟩ 1 (transLenTr ⟨49, by decide⟩ 1 hp))
        (rowE1 (⟨64, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨64, by decide⟩ : Fin 148) ⟨49, by decide⟩ _
      (validAt ⟨64, by decide⟩ (listedAt ⟨64, by decide⟩ hj))
      (colE1 ⟨49, by decide⟩ 1 (transLenTr ⟨49, by decide⟩ 1 hp)) T64_49
      hfix64_49 hinj64_49 hcardT64_49
      (fun i => conj_mem_of_fixedPoints _ _ (T64_49 i) (hfix64_49 i) _)
      ⟨64, by decide⟩ ⟨49, by decide⟩ _
      (Q2.validAt ⟨64, by decide⟩ (Q2.listedAt ⟨64, by decide⟩
        (alnCheck_rep ⟨64, by decide⟩ hj hq).1))
      (colE2 ⟨49, by decide⟩ 1 hp) Q2.T64_49_2 Q2.hfix64_49_2 Q2.hinj64_49_2
      Q2.hcardT64_49_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T64_49_2 i) (Q2.hfix64_49_2 i) _)
      ?_).symm
  rw [show colData1 (⟨64, by decide⟩ : Fin 148)
        ((colE1 ⟨49, by decide⟩ 1 (transLenTr ⟨49, by decide⟩ 1 hp) : ↥(reps ⟨49, by decide⟩)) : Coordinate 1)
        T64_49 = colFn colCert_64_49_1.D (m := 5) from colCert_64_49_1.bind1,
    show colData2 (⟨64, by decide⟩ : Fin 148)
        ((colE2 ⟨49, by decide⟩ 1 hp : ↥(Q2.reps ⟨49, by decide⟩)) : Coordinate 2)
        Q2.T64_49_2 = colFn colCert_64_49_1.D (m := 5) from colCert_64_49_1.bind2]
  exact alnAll_64_49_1 j hj hq

theorem leaf_64_49_2 (hp : 2 < (Q2.transData.getD 49 []).length)
    (j : Nat) (hj : j < (repChars.getD 64 []).length)
    (hq : (normIsRep.getD 64 []).getD j false = true) :
    species (Q2.reps (⟨49, by decide⟩ : Fin 148)) (colE2 ⟨49, by decide⟩ 2 hp)
        (rowE2 (⟨64, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨49, by decide⟩ : Fin 148))
        (colE1 ⟨49, by decide⟩ 2 (transLenTr ⟨49, by decide⟩ 2 hp))
        (rowE1 (⟨64, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨64, by decide⟩ : Fin 148) ⟨49, by decide⟩ _
      (validAt ⟨64, by decide⟩ (listedAt ⟨64, by decide⟩ hj))
      (colE1 ⟨49, by decide⟩ 2 (transLenTr ⟨49, by decide⟩ 2 hp)) T64_49
      hfix64_49 hinj64_49 hcardT64_49
      (fun i => conj_mem_of_fixedPoints _ _ (T64_49 i) (hfix64_49 i) _)
      ⟨64, by decide⟩ ⟨49, by decide⟩ _
      (Q2.validAt ⟨64, by decide⟩ (Q2.listedAt ⟨64, by decide⟩
        (alnCheck_rep ⟨64, by decide⟩ hj hq).1))
      (colE2 ⟨49, by decide⟩ 2 hp) Q2.T64_49_2 Q2.hfix64_49_2 Q2.hinj64_49_2
      Q2.hcardT64_49_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T64_49_2 i) (Q2.hfix64_49_2 i) _)
      ?_).symm
  rw [show colData1 (⟨64, by decide⟩ : Fin 148)
        ((colE1 ⟨49, by decide⟩ 2 (transLenTr ⟨49, by decide⟩ 2 hp) : ↥(reps ⟨49, by decide⟩)) : Coordinate 1)
        T64_49 = colFn colCert_64_49_2.D (m := 5) from colCert_64_49_2.bind1,
    show colData2 (⟨64, by decide⟩ : Fin 148)
        ((colE2 ⟨49, by decide⟩ 2 hp : ↥(Q2.reps ⟨49, by decide⟩)) : Coordinate 2)
        Q2.T64_49_2 = colFn colCert_64_49_2.D (m := 5) from colCert_64_49_2.bind2]
  exact alnAll_64_49_2 j hj hq

theorem leaf_64_49_3 (hp : 3 < (Q2.transData.getD 49 []).length)
    (j : Nat) (hj : j < (repChars.getD 64 []).length)
    (hq : (normIsRep.getD 64 []).getD j false = true) :
    species (Q2.reps (⟨49, by decide⟩ : Fin 148)) (colE2 ⟨49, by decide⟩ 3 hp)
        (rowE2 (⟨64, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨49, by decide⟩ : Fin 148))
        (colE1 ⟨49, by decide⟩ 3 (transLenTr ⟨49, by decide⟩ 3 hp))
        (rowE1 (⟨64, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨64, by decide⟩ : Fin 148) ⟨49, by decide⟩ _
      (validAt ⟨64, by decide⟩ (listedAt ⟨64, by decide⟩ hj))
      (colE1 ⟨49, by decide⟩ 3 (transLenTr ⟨49, by decide⟩ 3 hp)) T64_49
      hfix64_49 hinj64_49 hcardT64_49
      (fun i => conj_mem_of_fixedPoints _ _ (T64_49 i) (hfix64_49 i) _)
      ⟨64, by decide⟩ ⟨49, by decide⟩ _
      (Q2.validAt ⟨64, by decide⟩ (Q2.listedAt ⟨64, by decide⟩
        (alnCheck_rep ⟨64, by decide⟩ hj hq).1))
      (colE2 ⟨49, by decide⟩ 3 hp) Q2.T64_49_2 Q2.hfix64_49_2 Q2.hinj64_49_2
      Q2.hcardT64_49_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T64_49_2 i) (Q2.hfix64_49_2 i) _)
      ?_).symm
  rw [show colData1 (⟨64, by decide⟩ : Fin 148)
        ((colE1 ⟨49, by decide⟩ 3 (transLenTr ⟨49, by decide⟩ 3 hp) : ↥(reps ⟨49, by decide⟩)) : Coordinate 1)
        T64_49 = colFn colCert_64_49_3.D (m := 5) from colCert_64_49_3.bind1,
    show colData2 (⟨64, by decide⟩ : Fin 148)
        ((colE2 ⟨49, by decide⟩ 3 hp : ↥(Q2.reps ⟨49, by decide⟩)) : Coordinate 2)
        Q2.T64_49_2 = colFn colCert_64_49_3.D (m := 5) from colCert_64_49_3.bind2]
  exact alnAll_64_49_3 j hj hq

theorem leaf_64_49_4 (hp : 4 < (Q2.transData.getD 49 []).length)
    (j : Nat) (hj : j < (repChars.getD 64 []).length)
    (hq : (normIsRep.getD 64 []).getD j false = true) :
    species (Q2.reps (⟨49, by decide⟩ : Fin 148)) (colE2 ⟨49, by decide⟩ 4 hp)
        (rowE2 (⟨64, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨49, by decide⟩ : Fin 148))
        (colE1 ⟨49, by decide⟩ 4 (transLenTr ⟨49, by decide⟩ 4 hp))
        (rowE1 (⟨64, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨64, by decide⟩ : Fin 148) ⟨49, by decide⟩ _
      (validAt ⟨64, by decide⟩ (listedAt ⟨64, by decide⟩ hj))
      (colE1 ⟨49, by decide⟩ 4 (transLenTr ⟨49, by decide⟩ 4 hp)) T64_49
      hfix64_49 hinj64_49 hcardT64_49
      (fun i => conj_mem_of_fixedPoints _ _ (T64_49 i) (hfix64_49 i) _)
      ⟨64, by decide⟩ ⟨49, by decide⟩ _
      (Q2.validAt ⟨64, by decide⟩ (Q2.listedAt ⟨64, by decide⟩
        (alnCheck_rep ⟨64, by decide⟩ hj hq).1))
      (colE2 ⟨49, by decide⟩ 4 hp) Q2.T64_49_2 Q2.hfix64_49_2 Q2.hinj64_49_2
      Q2.hcardT64_49_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T64_49_2 i) (Q2.hfix64_49_2 i) _)
      ?_).symm
  rw [show colData1 (⟨64, by decide⟩ : Fin 148)
        ((colE1 ⟨49, by decide⟩ 4 (transLenTr ⟨49, by decide⟩ 4 hp) : ↥(reps ⟨49, by decide⟩)) : Coordinate 1)
        T64_49 = colFn colCert_64_49_4.D (m := 5) from colCert_64_49_4.bind1,
    show colData2 (⟨64, by decide⟩ : Fin 148)
        ((colE2 ⟨49, by decide⟩ 4 hp : ↥(Q2.reps ⟨49, by decide⟩)) : Coordinate 2)
        Q2.T64_49_2 = colFn colCert_64_49_4.D (m := 5) from colCert_64_49_4.bind2]
  exact alnAll_64_49_4 j hj hq

theorem leaf_64_49_5 (hp : 5 < (Q2.transData.getD 49 []).length)
    (j : Nat) (hj : j < (repChars.getD 64 []).length)
    (hq : (normIsRep.getD 64 []).getD j false = true) :
    species (Q2.reps (⟨49, by decide⟩ : Fin 148)) (colE2 ⟨49, by decide⟩ 5 hp)
        (rowE2 (⟨64, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨49, by decide⟩ : Fin 148))
        (colE1 ⟨49, by decide⟩ 5 (transLenTr ⟨49, by decide⟩ 5 hp))
        (rowE1 (⟨64, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨64, by decide⟩ : Fin 148) ⟨49, by decide⟩ _
      (validAt ⟨64, by decide⟩ (listedAt ⟨64, by decide⟩ hj))
      (colE1 ⟨49, by decide⟩ 5 (transLenTr ⟨49, by decide⟩ 5 hp)) T64_49
      hfix64_49 hinj64_49 hcardT64_49
      (fun i => conj_mem_of_fixedPoints _ _ (T64_49 i) (hfix64_49 i) _)
      ⟨64, by decide⟩ ⟨49, by decide⟩ _
      (Q2.validAt ⟨64, by decide⟩ (Q2.listedAt ⟨64, by decide⟩
        (alnCheck_rep ⟨64, by decide⟩ hj hq).1))
      (colE2 ⟨49, by decide⟩ 5 hp) Q2.T64_49_2 Q2.hfix64_49_2 Q2.hinj64_49_2
      Q2.hcardT64_49_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T64_49_2 i) (Q2.hfix64_49_2 i) _)
      ?_).symm
  rw [show colData1 (⟨64, by decide⟩ : Fin 148)
        ((colE1 ⟨49, by decide⟩ 5 (transLenTr ⟨49, by decide⟩ 5 hp) : ↥(reps ⟨49, by decide⟩)) : Coordinate 1)
        T64_49 = colFn colCert_64_49_5.D (m := 5) from colCert_64_49_5.bind1,
    show colData2 (⟨64, by decide⟩ : Fin 148)
        ((colE2 ⟨49, by decide⟩ 5 hp : ↥(Q2.reps ⟨49, by decide⟩)) : Coordinate 2)
        Q2.T64_49_2 = colFn colCert_64_49_5.D (m := 5) from colCert_64_49_5.bind2]
  exact alnAll_64_49_5 j hj hq

theorem leaf_64_49_10 (hp : 10 < (Q2.transData.getD 49 []).length)
    (j : Nat) (hj : j < (repChars.getD 64 []).length)
    (hq : (normIsRep.getD 64 []).getD j false = true) :
    species (Q2.reps (⟨49, by decide⟩ : Fin 148)) (colE2 ⟨49, by decide⟩ 10 hp)
        (rowE2 (⟨64, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨49, by decide⟩ : Fin 148))
        (colE1 ⟨49, by decide⟩ 10 (transLenTr ⟨49, by decide⟩ 10 hp))
        (rowE1 (⟨64, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨64, by decide⟩ : Fin 148) ⟨49, by decide⟩ _
      (validAt ⟨64, by decide⟩ (listedAt ⟨64, by decide⟩ hj))
      (colE1 ⟨49, by decide⟩ 10 (transLenTr ⟨49, by decide⟩ 10 hp)) T64_49
      hfix64_49 hinj64_49 hcardT64_49
      (fun i => conj_mem_of_fixedPoints _ _ (T64_49 i) (hfix64_49 i) _)
      ⟨64, by decide⟩ ⟨49, by decide⟩ _
      (Q2.validAt ⟨64, by decide⟩ (Q2.listedAt ⟨64, by decide⟩
        (alnCheck_rep ⟨64, by decide⟩ hj hq).1))
      (colE2 ⟨49, by decide⟩ 10 hp) Q2.T64_49_2 Q2.hfix64_49_2 Q2.hinj64_49_2
      Q2.hcardT64_49_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T64_49_2 i) (Q2.hfix64_49_2 i) _)
      ?_).symm
  rw [show colData1 (⟨64, by decide⟩ : Fin 148)
        ((colE1 ⟨49, by decide⟩ 10 (transLenTr ⟨49, by decide⟩ 10 hp) : ↥(reps ⟨49, by decide⟩)) : Coordinate 1)
        T64_49 = colFn colCert_64_49_10.D (m := 5) from colCert_64_49_10.bind1,
    show colData2 (⟨64, by decide⟩ : Fin 148)
        ((colE2 ⟨49, by decide⟩ 10 hp : ↥(Q2.reps ⟨49, by decide⟩)) : Coordinate 2)
        Q2.T64_49_2 = colFn colCert_64_49_10.D (m := 5) from colCert_64_49_10.bind2]
  exact alnAll_64_49_10 j hj hq

theorem leaf_64_49_15 (hp : 15 < (Q2.transData.getD 49 []).length)
    (j : Nat) (hj : j < (repChars.getD 64 []).length)
    (hq : (normIsRep.getD 64 []).getD j false = true) :
    species (Q2.reps (⟨49, by decide⟩ : Fin 148)) (colE2 ⟨49, by decide⟩ 15 hp)
        (rowE2 (⟨64, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨49, by decide⟩ : Fin 148))
        (colE1 ⟨49, by decide⟩ 15 (transLenTr ⟨49, by decide⟩ 15 hp))
        (rowE1 (⟨64, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨64, by decide⟩ : Fin 148) ⟨49, by decide⟩ _
      (validAt ⟨64, by decide⟩ (listedAt ⟨64, by decide⟩ hj))
      (colE1 ⟨49, by decide⟩ 15 (transLenTr ⟨49, by decide⟩ 15 hp)) T64_49
      hfix64_49 hinj64_49 hcardT64_49
      (fun i => conj_mem_of_fixedPoints _ _ (T64_49 i) (hfix64_49 i) _)
      ⟨64, by decide⟩ ⟨49, by decide⟩ _
      (Q2.validAt ⟨64, by decide⟩ (Q2.listedAt ⟨64, by decide⟩
        (alnCheck_rep ⟨64, by decide⟩ hj hq).1))
      (colE2 ⟨49, by decide⟩ 15 hp) Q2.T64_49_2 Q2.hfix64_49_2 Q2.hinj64_49_2
      Q2.hcardT64_49_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T64_49_2 i) (Q2.hfix64_49_2 i) _)
      ?_).symm
  rw [show colData1 (⟨64, by decide⟩ : Fin 148)
        ((colE1 ⟨49, by decide⟩ 15 (transLenTr ⟨49, by decide⟩ 15 hp) : ↥(reps ⟨49, by decide⟩)) : Coordinate 1)
        T64_49 = colFn colCert_64_49_15.D (m := 5) from colCert_64_49_15.bind1,
    show colData2 (⟨64, by decide⟩ : Fin 148)
        ((colE2 ⟨49, by decide⟩ 15 hp : ↥(Q2.reps ⟨49, by decide⟩)) : Coordinate 2)
        Q2.T64_49_2 = colFn colCert_64_49_15.D (m := 5) from colCert_64_49_15.bind2]
  exact alnAll_64_49_15 j hj hq

theorem leaf_64_49_20 (hp : 20 < (Q2.transData.getD 49 []).length)
    (j : Nat) (hj : j < (repChars.getD 64 []).length)
    (hq : (normIsRep.getD 64 []).getD j false = true) :
    species (Q2.reps (⟨49, by decide⟩ : Fin 148)) (colE2 ⟨49, by decide⟩ 20 hp)
        (rowE2 (⟨64, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨49, by decide⟩ : Fin 148))
        (colE1 ⟨49, by decide⟩ 20 (transLenTr ⟨49, by decide⟩ 20 hp))
        (rowE1 (⟨64, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨64, by decide⟩ : Fin 148) ⟨49, by decide⟩ _
      (validAt ⟨64, by decide⟩ (listedAt ⟨64, by decide⟩ hj))
      (colE1 ⟨49, by decide⟩ 20 (transLenTr ⟨49, by decide⟩ 20 hp)) T64_49
      hfix64_49 hinj64_49 hcardT64_49
      (fun i => conj_mem_of_fixedPoints _ _ (T64_49 i) (hfix64_49 i) _)
      ⟨64, by decide⟩ ⟨49, by decide⟩ _
      (Q2.validAt ⟨64, by decide⟩ (Q2.listedAt ⟨64, by decide⟩
        (alnCheck_rep ⟨64, by decide⟩ hj hq).1))
      (colE2 ⟨49, by decide⟩ 20 hp) Q2.T64_49_2 Q2.hfix64_49_2 Q2.hinj64_49_2
      Q2.hcardT64_49_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T64_49_2 i) (Q2.hfix64_49_2 i) _)
      ?_).symm
  rw [show colData1 (⟨64, by decide⟩ : Fin 148)
        ((colE1 ⟨49, by decide⟩ 20 (transLenTr ⟨49, by decide⟩ 20 hp) : ↥(reps ⟨49, by decide⟩)) : Coordinate 1)
        T64_49 = colFn colCert_64_49_20.D (m := 5) from colCert_64_49_20.bind1,
    show colData2 (⟨64, by decide⟩ : Fin 148)
        ((colE2 ⟨49, by decide⟩ 20 hp : ↥(Q2.reps ⟨49, by decide⟩)) : Coordinate 2)
        Q2.T64_49_2 = colFn colCert_64_49_20.D (m := 5) from colCert_64_49_20.bind2]
  exact alnAll_64_49_20 j hj hq

theorem leaf_64_64_0 (hp : 0 < (Q2.transData.getD 64 []).length)
    (j : Nat) (hj : j < (repChars.getD 64 []).length)
    (hq : (normIsRep.getD 64 []).getD j false = true) :
    species (Q2.reps (⟨64, by decide⟩ : Fin 148)) (colE2 ⟨64, by decide⟩ 0 hp)
        (rowE2 (⟨64, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨64, by decide⟩ : Fin 148))
        (colE1 ⟨64, by decide⟩ 0 (transLenTr ⟨64, by decide⟩ 0 hp))
        (rowE1 (⟨64, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨64, by decide⟩ : Fin 148) ⟨64, by decide⟩ _
      (validAt ⟨64, by decide⟩ (listedAt ⟨64, by decide⟩ hj))
      (colE1 ⟨64, by decide⟩ 0 (transLenTr ⟨64, by decide⟩ 0 hp)) T64_64
      hfix64_64 hinj64_64 hcardT64_64
      (fun i => conj_mem_of_fixedPoints _ _ (T64_64 i) (hfix64_64 i) _)
      ⟨64, by decide⟩ ⟨64, by decide⟩ _
      (Q2.validAt ⟨64, by decide⟩ (Q2.listedAt ⟨64, by decide⟩
        (alnCheck_rep ⟨64, by decide⟩ hj hq).1))
      (colE2 ⟨64, by decide⟩ 0 hp) Q2.T64_64_2 Q2.hfix64_64_2 Q2.hinj64_64_2
      Q2.hcardT64_64_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T64_64_2 i) (Q2.hfix64_64_2 i) _)
      ?_).symm
  rw [show colData1 (⟨64, by decide⟩ : Fin 148)
        ((colE1 ⟨64, by decide⟩ 0 (transLenTr ⟨64, by decide⟩ 0 hp) : ↥(reps ⟨64, by decide⟩)) : Coordinate 1)
        T64_64 = colFn colCert_64_64_0.D (m := 5) from colCert_64_64_0.bind1,
    show colData2 (⟨64, by decide⟩ : Fin 148)
        ((colE2 ⟨64, by decide⟩ 0 hp : ↥(Q2.reps ⟨64, by decide⟩)) : Coordinate 2)
        Q2.T64_64_2 = colFn colCert_64_64_0.D (m := 5) from colCert_64_64_0.bind2]
  exact alnAll_64_64_0 j hj hq

theorem leaf_64_64_1 (hp : 1 < (Q2.transData.getD 64 []).length)
    (j : Nat) (hj : j < (repChars.getD 64 []).length)
    (hq : (normIsRep.getD 64 []).getD j false = true) :
    species (Q2.reps (⟨64, by decide⟩ : Fin 148)) (colE2 ⟨64, by decide⟩ 1 hp)
        (rowE2 (⟨64, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨64, by decide⟩ : Fin 148))
        (colE1 ⟨64, by decide⟩ 1 (transLenTr ⟨64, by decide⟩ 1 hp))
        (rowE1 (⟨64, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨64, by decide⟩ : Fin 148) ⟨64, by decide⟩ _
      (validAt ⟨64, by decide⟩ (listedAt ⟨64, by decide⟩ hj))
      (colE1 ⟨64, by decide⟩ 1 (transLenTr ⟨64, by decide⟩ 1 hp)) T64_64
      hfix64_64 hinj64_64 hcardT64_64
      (fun i => conj_mem_of_fixedPoints _ _ (T64_64 i) (hfix64_64 i) _)
      ⟨64, by decide⟩ ⟨64, by decide⟩ _
      (Q2.validAt ⟨64, by decide⟩ (Q2.listedAt ⟨64, by decide⟩
        (alnCheck_rep ⟨64, by decide⟩ hj hq).1))
      (colE2 ⟨64, by decide⟩ 1 hp) Q2.T64_64_2 Q2.hfix64_64_2 Q2.hinj64_64_2
      Q2.hcardT64_64_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T64_64_2 i) (Q2.hfix64_64_2 i) _)
      ?_).symm
  rw [show colData1 (⟨64, by decide⟩ : Fin 148)
        ((colE1 ⟨64, by decide⟩ 1 (transLenTr ⟨64, by decide⟩ 1 hp) : ↥(reps ⟨64, by decide⟩)) : Coordinate 1)
        T64_64 = colFn colCert_64_64_1.D (m := 5) from colCert_64_64_1.bind1,
    show colData2 (⟨64, by decide⟩ : Fin 148)
        ((colE2 ⟨64, by decide⟩ 1 hp : ↥(Q2.reps ⟨64, by decide⟩)) : Coordinate 2)
        Q2.T64_64_2 = colFn colCert_64_64_1.D (m := 5) from colCert_64_64_1.bind2]
  exact alnAll_64_64_1 j hj hq

theorem leaf_64_64_2 (hp : 2 < (Q2.transData.getD 64 []).length)
    (j : Nat) (hj : j < (repChars.getD 64 []).length)
    (hq : (normIsRep.getD 64 []).getD j false = true) :
    species (Q2.reps (⟨64, by decide⟩ : Fin 148)) (colE2 ⟨64, by decide⟩ 2 hp)
        (rowE2 (⟨64, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨64, by decide⟩ : Fin 148))
        (colE1 ⟨64, by decide⟩ 2 (transLenTr ⟨64, by decide⟩ 2 hp))
        (rowE1 (⟨64, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨64, by decide⟩ : Fin 148) ⟨64, by decide⟩ _
      (validAt ⟨64, by decide⟩ (listedAt ⟨64, by decide⟩ hj))
      (colE1 ⟨64, by decide⟩ 2 (transLenTr ⟨64, by decide⟩ 2 hp)) T64_64
      hfix64_64 hinj64_64 hcardT64_64
      (fun i => conj_mem_of_fixedPoints _ _ (T64_64 i) (hfix64_64 i) _)
      ⟨64, by decide⟩ ⟨64, by decide⟩ _
      (Q2.validAt ⟨64, by decide⟩ (Q2.listedAt ⟨64, by decide⟩
        (alnCheck_rep ⟨64, by decide⟩ hj hq).1))
      (colE2 ⟨64, by decide⟩ 2 hp) Q2.T64_64_2 Q2.hfix64_64_2 Q2.hinj64_64_2
      Q2.hcardT64_64_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T64_64_2 i) (Q2.hfix64_64_2 i) _)
      ?_).symm
  rw [show colData1 (⟨64, by decide⟩ : Fin 148)
        ((colE1 ⟨64, by decide⟩ 2 (transLenTr ⟨64, by decide⟩ 2 hp) : ↥(reps ⟨64, by decide⟩)) : Coordinate 1)
        T64_64 = colFn colCert_64_64_2.D (m := 5) from colCert_64_64_2.bind1,
    show colData2 (⟨64, by decide⟩ : Fin 148)
        ((colE2 ⟨64, by decide⟩ 2 hp : ↥(Q2.reps ⟨64, by decide⟩)) : Coordinate 2)
        Q2.T64_64_2 = colFn colCert_64_64_2.D (m := 5) from colCert_64_64_2.bind2]
  exact alnAll_64_64_2 j hj hq

theorem leaf_64_64_3 (hp : 3 < (Q2.transData.getD 64 []).length)
    (j : Nat) (hj : j < (repChars.getD 64 []).length)
    (hq : (normIsRep.getD 64 []).getD j false = true) :
    species (Q2.reps (⟨64, by decide⟩ : Fin 148)) (colE2 ⟨64, by decide⟩ 3 hp)
        (rowE2 (⟨64, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨64, by decide⟩ : Fin 148))
        (colE1 ⟨64, by decide⟩ 3 (transLenTr ⟨64, by decide⟩ 3 hp))
        (rowE1 (⟨64, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨64, by decide⟩ : Fin 148) ⟨64, by decide⟩ _
      (validAt ⟨64, by decide⟩ (listedAt ⟨64, by decide⟩ hj))
      (colE1 ⟨64, by decide⟩ 3 (transLenTr ⟨64, by decide⟩ 3 hp)) T64_64
      hfix64_64 hinj64_64 hcardT64_64
      (fun i => conj_mem_of_fixedPoints _ _ (T64_64 i) (hfix64_64 i) _)
      ⟨64, by decide⟩ ⟨64, by decide⟩ _
      (Q2.validAt ⟨64, by decide⟩ (Q2.listedAt ⟨64, by decide⟩
        (alnCheck_rep ⟨64, by decide⟩ hj hq).1))
      (colE2 ⟨64, by decide⟩ 3 hp) Q2.T64_64_2 Q2.hfix64_64_2 Q2.hinj64_64_2
      Q2.hcardT64_64_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T64_64_2 i) (Q2.hfix64_64_2 i) _)
      ?_).symm
  rw [show colData1 (⟨64, by decide⟩ : Fin 148)
        ((colE1 ⟨64, by decide⟩ 3 (transLenTr ⟨64, by decide⟩ 3 hp) : ↥(reps ⟨64, by decide⟩)) : Coordinate 1)
        T64_64 = colFn colCert_64_64_3.D (m := 5) from colCert_64_64_3.bind1,
    show colData2 (⟨64, by decide⟩ : Fin 148)
        ((colE2 ⟨64, by decide⟩ 3 hp : ↥(Q2.reps ⟨64, by decide⟩)) : Coordinate 2)
        Q2.T64_64_2 = colFn colCert_64_64_3.D (m := 5) from colCert_64_64_3.bind2]
  exact alnAll_64_64_3 j hj hq

theorem leaf_64_64_4 (hp : 4 < (Q2.transData.getD 64 []).length)
    (j : Nat) (hj : j < (repChars.getD 64 []).length)
    (hq : (normIsRep.getD 64 []).getD j false = true) :
    species (Q2.reps (⟨64, by decide⟩ : Fin 148)) (colE2 ⟨64, by decide⟩ 4 hp)
        (rowE2 (⟨64, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨64, by decide⟩ : Fin 148))
        (colE1 ⟨64, by decide⟩ 4 (transLenTr ⟨64, by decide⟩ 4 hp))
        (rowE1 (⟨64, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨64, by decide⟩ : Fin 148) ⟨64, by decide⟩ _
      (validAt ⟨64, by decide⟩ (listedAt ⟨64, by decide⟩ hj))
      (colE1 ⟨64, by decide⟩ 4 (transLenTr ⟨64, by decide⟩ 4 hp)) T64_64
      hfix64_64 hinj64_64 hcardT64_64
      (fun i => conj_mem_of_fixedPoints _ _ (T64_64 i) (hfix64_64 i) _)
      ⟨64, by decide⟩ ⟨64, by decide⟩ _
      (Q2.validAt ⟨64, by decide⟩ (Q2.listedAt ⟨64, by decide⟩
        (alnCheck_rep ⟨64, by decide⟩ hj hq).1))
      (colE2 ⟨64, by decide⟩ 4 hp) Q2.T64_64_2 Q2.hfix64_64_2 Q2.hinj64_64_2
      Q2.hcardT64_64_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T64_64_2 i) (Q2.hfix64_64_2 i) _)
      ?_).symm
  rw [show colData1 (⟨64, by decide⟩ : Fin 148)
        ((colE1 ⟨64, by decide⟩ 4 (transLenTr ⟨64, by decide⟩ 4 hp) : ↥(reps ⟨64, by decide⟩)) : Coordinate 1)
        T64_64 = colFn colCert_64_64_4.D (m := 5) from colCert_64_64_4.bind1,
    show colData2 (⟨64, by decide⟩ : Fin 148)
        ((colE2 ⟨64, by decide⟩ 4 hp : ↥(Q2.reps ⟨64, by decide⟩)) : Coordinate 2)
        Q2.T64_64_2 = colFn colCert_64_64_4.D (m := 5) from colCert_64_64_4.bind2]
  exact alnAll_64_64_4 j hj hq

theorem leaf_64_64_5 (hp : 5 < (Q2.transData.getD 64 []).length)
    (j : Nat) (hj : j < (repChars.getD 64 []).length)
    (hq : (normIsRep.getD 64 []).getD j false = true) :
    species (Q2.reps (⟨64, by decide⟩ : Fin 148)) (colE2 ⟨64, by decide⟩ 5 hp)
        (rowE2 (⟨64, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨64, by decide⟩ : Fin 148))
        (colE1 ⟨64, by decide⟩ 5 (transLenTr ⟨64, by decide⟩ 5 hp))
        (rowE1 (⟨64, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨64, by decide⟩ : Fin 148) ⟨64, by decide⟩ _
      (validAt ⟨64, by decide⟩ (listedAt ⟨64, by decide⟩ hj))
      (colE1 ⟨64, by decide⟩ 5 (transLenTr ⟨64, by decide⟩ 5 hp)) T64_64
      hfix64_64 hinj64_64 hcardT64_64
      (fun i => conj_mem_of_fixedPoints _ _ (T64_64 i) (hfix64_64 i) _)
      ⟨64, by decide⟩ ⟨64, by decide⟩ _
      (Q2.validAt ⟨64, by decide⟩ (Q2.listedAt ⟨64, by decide⟩
        (alnCheck_rep ⟨64, by decide⟩ hj hq).1))
      (colE2 ⟨64, by decide⟩ 5 hp) Q2.T64_64_2 Q2.hfix64_64_2 Q2.hinj64_64_2
      Q2.hcardT64_64_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T64_64_2 i) (Q2.hfix64_64_2 i) _)
      ?_).symm
  rw [show colData1 (⟨64, by decide⟩ : Fin 148)
        ((colE1 ⟨64, by decide⟩ 5 (transLenTr ⟨64, by decide⟩ 5 hp) : ↥(reps ⟨64, by decide⟩)) : Coordinate 1)
        T64_64 = colFn colCert_64_64_5.D (m := 5) from colCert_64_64_5.bind1,
    show colData2 (⟨64, by decide⟩ : Fin 148)
        ((colE2 ⟨64, by decide⟩ 5 hp : ↥(Q2.reps ⟨64, by decide⟩)) : Coordinate 2)
        Q2.T64_64_2 = colFn colCert_64_64_5.D (m := 5) from colCert_64_64_5.bind2]
  exact alnAll_64_64_5 j hj hq

theorem leaf_64_64_6 (hp : 6 < (Q2.transData.getD 64 []).length)
    (j : Nat) (hj : j < (repChars.getD 64 []).length)
    (hq : (normIsRep.getD 64 []).getD j false = true) :
    species (Q2.reps (⟨64, by decide⟩ : Fin 148)) (colE2 ⟨64, by decide⟩ 6 hp)
        (rowE2 (⟨64, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨64, by decide⟩ : Fin 148))
        (colE1 ⟨64, by decide⟩ 6 (transLenTr ⟨64, by decide⟩ 6 hp))
        (rowE1 (⟨64, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨64, by decide⟩ : Fin 148) ⟨64, by decide⟩ _
      (validAt ⟨64, by decide⟩ (listedAt ⟨64, by decide⟩ hj))
      (colE1 ⟨64, by decide⟩ 6 (transLenTr ⟨64, by decide⟩ 6 hp)) T64_64
      hfix64_64 hinj64_64 hcardT64_64
      (fun i => conj_mem_of_fixedPoints _ _ (T64_64 i) (hfix64_64 i) _)
      ⟨64, by decide⟩ ⟨64, by decide⟩ _
      (Q2.validAt ⟨64, by decide⟩ (Q2.listedAt ⟨64, by decide⟩
        (alnCheck_rep ⟨64, by decide⟩ hj hq).1))
      (colE2 ⟨64, by decide⟩ 6 hp) Q2.T64_64_2 Q2.hfix64_64_2 Q2.hinj64_64_2
      Q2.hcardT64_64_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T64_64_2 i) (Q2.hfix64_64_2 i) _)
      ?_).symm
  rw [show colData1 (⟨64, by decide⟩ : Fin 148)
        ((colE1 ⟨64, by decide⟩ 6 (transLenTr ⟨64, by decide⟩ 6 hp) : ↥(reps ⟨64, by decide⟩)) : Coordinate 1)
        T64_64 = colFn colCert_64_64_6.D (m := 5) from colCert_64_64_6.bind1,
    show colData2 (⟨64, by decide⟩ : Fin 148)
        ((colE2 ⟨64, by decide⟩ 6 hp : ↥(Q2.reps ⟨64, by decide⟩)) : Coordinate 2)
        Q2.T64_64_2 = colFn colCert_64_64_6.D (m := 5) from colCert_64_64_6.bind2]
  exact alnAll_64_64_6 j hj hq

theorem leaf_64_64_7 (hp : 7 < (Q2.transData.getD 64 []).length)
    (j : Nat) (hj : j < (repChars.getD 64 []).length)
    (hq : (normIsRep.getD 64 []).getD j false = true) :
    species (Q2.reps (⟨64, by decide⟩ : Fin 148)) (colE2 ⟨64, by decide⟩ 7 hp)
        (rowE2 (⟨64, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨64, by decide⟩ : Fin 148))
        (colE1 ⟨64, by decide⟩ 7 (transLenTr ⟨64, by decide⟩ 7 hp))
        (rowE1 (⟨64, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨64, by decide⟩ : Fin 148) ⟨64, by decide⟩ _
      (validAt ⟨64, by decide⟩ (listedAt ⟨64, by decide⟩ hj))
      (colE1 ⟨64, by decide⟩ 7 (transLenTr ⟨64, by decide⟩ 7 hp)) T64_64
      hfix64_64 hinj64_64 hcardT64_64
      (fun i => conj_mem_of_fixedPoints _ _ (T64_64 i) (hfix64_64 i) _)
      ⟨64, by decide⟩ ⟨64, by decide⟩ _
      (Q2.validAt ⟨64, by decide⟩ (Q2.listedAt ⟨64, by decide⟩
        (alnCheck_rep ⟨64, by decide⟩ hj hq).1))
      (colE2 ⟨64, by decide⟩ 7 hp) Q2.T64_64_2 Q2.hfix64_64_2 Q2.hinj64_64_2
      Q2.hcardT64_64_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T64_64_2 i) (Q2.hfix64_64_2 i) _)
      ?_).symm
  rw [show colData1 (⟨64, by decide⟩ : Fin 148)
        ((colE1 ⟨64, by decide⟩ 7 (transLenTr ⟨64, by decide⟩ 7 hp) : ↥(reps ⟨64, by decide⟩)) : Coordinate 1)
        T64_64 = colFn colCert_64_64_7.D (m := 5) from colCert_64_64_7.bind1,
    show colData2 (⟨64, by decide⟩ : Fin 148)
        ((colE2 ⟨64, by decide⟩ 7 hp : ↥(Q2.reps ⟨64, by decide⟩)) : Coordinate 2)
        Q2.T64_64_2 = colFn colCert_64_64_7.D (m := 5) from colCert_64_64_7.bind2]
  exact alnAll_64_64_7 j hj hq

theorem leaf_64_64_8 (hp : 8 < (Q2.transData.getD 64 []).length)
    (j : Nat) (hj : j < (repChars.getD 64 []).length)
    (hq : (normIsRep.getD 64 []).getD j false = true) :
    species (Q2.reps (⟨64, by decide⟩ : Fin 148)) (colE2 ⟨64, by decide⟩ 8 hp)
        (rowE2 (⟨64, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨64, by decide⟩ : Fin 148))
        (colE1 ⟨64, by decide⟩ 8 (transLenTr ⟨64, by decide⟩ 8 hp))
        (rowE1 (⟨64, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨64, by decide⟩ : Fin 148) ⟨64, by decide⟩ _
      (validAt ⟨64, by decide⟩ (listedAt ⟨64, by decide⟩ hj))
      (colE1 ⟨64, by decide⟩ 8 (transLenTr ⟨64, by decide⟩ 8 hp)) T64_64
      hfix64_64 hinj64_64 hcardT64_64
      (fun i => conj_mem_of_fixedPoints _ _ (T64_64 i) (hfix64_64 i) _)
      ⟨64, by decide⟩ ⟨64, by decide⟩ _
      (Q2.validAt ⟨64, by decide⟩ (Q2.listedAt ⟨64, by decide⟩
        (alnCheck_rep ⟨64, by decide⟩ hj hq).1))
      (colE2 ⟨64, by decide⟩ 8 hp) Q2.T64_64_2 Q2.hfix64_64_2 Q2.hinj64_64_2
      Q2.hcardT64_64_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T64_64_2 i) (Q2.hfix64_64_2 i) _)
      ?_).symm
  rw [show colData1 (⟨64, by decide⟩ : Fin 148)
        ((colE1 ⟨64, by decide⟩ 8 (transLenTr ⟨64, by decide⟩ 8 hp) : ↥(reps ⟨64, by decide⟩)) : Coordinate 1)
        T64_64 = colFn colCert_64_64_8.D (m := 5) from colCert_64_64_8.bind1,
    show colData2 (⟨64, by decide⟩ : Fin 148)
        ((colE2 ⟨64, by decide⟩ 8 hp : ↥(Q2.reps ⟨64, by decide⟩)) : Coordinate 2)
        Q2.T64_64_2 = colFn colCert_64_64_8.D (m := 5) from colCert_64_64_8.bind2]
  exact alnAll_64_64_8 j hj hq

theorem leaf_64_64_9 (hp : 9 < (Q2.transData.getD 64 []).length)
    (j : Nat) (hj : j < (repChars.getD 64 []).length)
    (hq : (normIsRep.getD 64 []).getD j false = true) :
    species (Q2.reps (⟨64, by decide⟩ : Fin 148)) (colE2 ⟨64, by decide⟩ 9 hp)
        (rowE2 (⟨64, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨64, by decide⟩ : Fin 148))
        (colE1 ⟨64, by decide⟩ 9 (transLenTr ⟨64, by decide⟩ 9 hp))
        (rowE1 (⟨64, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨64, by decide⟩ : Fin 148) ⟨64, by decide⟩ _
      (validAt ⟨64, by decide⟩ (listedAt ⟨64, by decide⟩ hj))
      (colE1 ⟨64, by decide⟩ 9 (transLenTr ⟨64, by decide⟩ 9 hp)) T64_64
      hfix64_64 hinj64_64 hcardT64_64
      (fun i => conj_mem_of_fixedPoints _ _ (T64_64 i) (hfix64_64 i) _)
      ⟨64, by decide⟩ ⟨64, by decide⟩ _
      (Q2.validAt ⟨64, by decide⟩ (Q2.listedAt ⟨64, by decide⟩
        (alnCheck_rep ⟨64, by decide⟩ hj hq).1))
      (colE2 ⟨64, by decide⟩ 9 hp) Q2.T64_64_2 Q2.hfix64_64_2 Q2.hinj64_64_2
      Q2.hcardT64_64_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T64_64_2 i) (Q2.hfix64_64_2 i) _)
      ?_).symm
  rw [show colData1 (⟨64, by decide⟩ : Fin 148)
        ((colE1 ⟨64, by decide⟩ 9 (transLenTr ⟨64, by decide⟩ 9 hp) : ↥(reps ⟨64, by decide⟩)) : Coordinate 1)
        T64_64 = colFn colCert_64_64_9.D (m := 5) from colCert_64_64_9.bind1,
    show colData2 (⟨64, by decide⟩ : Fin 148)
        ((colE2 ⟨64, by decide⟩ 9 hp : ↥(Q2.reps ⟨64, by decide⟩)) : Coordinate 2)
        Q2.T64_64_2 = colFn colCert_64_64_9.D (m := 5) from colCert_64_64_9.bind2]
  exact alnAll_64_64_9 j hj hq

theorem leaf_64_64_10 (hp : 10 < (Q2.transData.getD 64 []).length)
    (j : Nat) (hj : j < (repChars.getD 64 []).length)
    (hq : (normIsRep.getD 64 []).getD j false = true) :
    species (Q2.reps (⟨64, by decide⟩ : Fin 148)) (colE2 ⟨64, by decide⟩ 10 hp)
        (rowE2 (⟨64, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨64, by decide⟩ : Fin 148))
        (colE1 ⟨64, by decide⟩ 10 (transLenTr ⟨64, by decide⟩ 10 hp))
        (rowE1 (⟨64, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨64, by decide⟩ : Fin 148) ⟨64, by decide⟩ _
      (validAt ⟨64, by decide⟩ (listedAt ⟨64, by decide⟩ hj))
      (colE1 ⟨64, by decide⟩ 10 (transLenTr ⟨64, by decide⟩ 10 hp)) T64_64
      hfix64_64 hinj64_64 hcardT64_64
      (fun i => conj_mem_of_fixedPoints _ _ (T64_64 i) (hfix64_64 i) _)
      ⟨64, by decide⟩ ⟨64, by decide⟩ _
      (Q2.validAt ⟨64, by decide⟩ (Q2.listedAt ⟨64, by decide⟩
        (alnCheck_rep ⟨64, by decide⟩ hj hq).1))
      (colE2 ⟨64, by decide⟩ 10 hp) Q2.T64_64_2 Q2.hfix64_64_2 Q2.hinj64_64_2
      Q2.hcardT64_64_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T64_64_2 i) (Q2.hfix64_64_2 i) _)
      ?_).symm
  rw [show colData1 (⟨64, by decide⟩ : Fin 148)
        ((colE1 ⟨64, by decide⟩ 10 (transLenTr ⟨64, by decide⟩ 10 hp) : ↥(reps ⟨64, by decide⟩)) : Coordinate 1)
        T64_64 = colFn colCert_64_64_10.D (m := 5) from colCert_64_64_10.bind1,
    show colData2 (⟨64, by decide⟩ : Fin 148)
        ((colE2 ⟨64, by decide⟩ 10 hp : ↥(Q2.reps ⟨64, by decide⟩)) : Coordinate 2)
        Q2.T64_64_2 = colFn colCert_64_64_10.D (m := 5) from colCert_64_64_10.bind2]
  exact alnAll_64_64_10 j hj hq

theorem leaf_64_64_11 (hp : 11 < (Q2.transData.getD 64 []).length)
    (j : Nat) (hj : j < (repChars.getD 64 []).length)
    (hq : (normIsRep.getD 64 []).getD j false = true) :
    species (Q2.reps (⟨64, by decide⟩ : Fin 148)) (colE2 ⟨64, by decide⟩ 11 hp)
        (rowE2 (⟨64, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨64, by decide⟩ : Fin 148))
        (colE1 ⟨64, by decide⟩ 11 (transLenTr ⟨64, by decide⟩ 11 hp))
        (rowE1 (⟨64, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨64, by decide⟩ : Fin 148) ⟨64, by decide⟩ _
      (validAt ⟨64, by decide⟩ (listedAt ⟨64, by decide⟩ hj))
      (colE1 ⟨64, by decide⟩ 11 (transLenTr ⟨64, by decide⟩ 11 hp)) T64_64
      hfix64_64 hinj64_64 hcardT64_64
      (fun i => conj_mem_of_fixedPoints _ _ (T64_64 i) (hfix64_64 i) _)
      ⟨64, by decide⟩ ⟨64, by decide⟩ _
      (Q2.validAt ⟨64, by decide⟩ (Q2.listedAt ⟨64, by decide⟩
        (alnCheck_rep ⟨64, by decide⟩ hj hq).1))
      (colE2 ⟨64, by decide⟩ 11 hp) Q2.T64_64_2 Q2.hfix64_64_2 Q2.hinj64_64_2
      Q2.hcardT64_64_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T64_64_2 i) (Q2.hfix64_64_2 i) _)
      ?_).symm
  rw [show colData1 (⟨64, by decide⟩ : Fin 148)
        ((colE1 ⟨64, by decide⟩ 11 (transLenTr ⟨64, by decide⟩ 11 hp) : ↥(reps ⟨64, by decide⟩)) : Coordinate 1)
        T64_64 = colFn colCert_64_64_11.D (m := 5) from colCert_64_64_11.bind1,
    show colData2 (⟨64, by decide⟩ : Fin 148)
        ((colE2 ⟨64, by decide⟩ 11 hp : ↥(Q2.reps ⟨64, by decide⟩)) : Coordinate 2)
        Q2.T64_64_2 = colFn colCert_64_64_11.D (m := 5) from colCert_64_64_11.bind2]
  exact alnAll_64_64_11 j hj hq

theorem leaf_64_64_12 (hp : 12 < (Q2.transData.getD 64 []).length)
    (j : Nat) (hj : j < (repChars.getD 64 []).length)
    (hq : (normIsRep.getD 64 []).getD j false = true) :
    species (Q2.reps (⟨64, by decide⟩ : Fin 148)) (colE2 ⟨64, by decide⟩ 12 hp)
        (rowE2 (⟨64, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨64, by decide⟩ : Fin 148))
        (colE1 ⟨64, by decide⟩ 12 (transLenTr ⟨64, by decide⟩ 12 hp))
        (rowE1 (⟨64, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨64, by decide⟩ : Fin 148) ⟨64, by decide⟩ _
      (validAt ⟨64, by decide⟩ (listedAt ⟨64, by decide⟩ hj))
      (colE1 ⟨64, by decide⟩ 12 (transLenTr ⟨64, by decide⟩ 12 hp)) T64_64
      hfix64_64 hinj64_64 hcardT64_64
      (fun i => conj_mem_of_fixedPoints _ _ (T64_64 i) (hfix64_64 i) _)
      ⟨64, by decide⟩ ⟨64, by decide⟩ _
      (Q2.validAt ⟨64, by decide⟩ (Q2.listedAt ⟨64, by decide⟩
        (alnCheck_rep ⟨64, by decide⟩ hj hq).1))
      (colE2 ⟨64, by decide⟩ 12 hp) Q2.T64_64_2 Q2.hfix64_64_2 Q2.hinj64_64_2
      Q2.hcardT64_64_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T64_64_2 i) (Q2.hfix64_64_2 i) _)
      ?_).symm
  rw [show colData1 (⟨64, by decide⟩ : Fin 148)
        ((colE1 ⟨64, by decide⟩ 12 (transLenTr ⟨64, by decide⟩ 12 hp) : ↥(reps ⟨64, by decide⟩)) : Coordinate 1)
        T64_64 = colFn colCert_64_64_12.D (m := 5) from colCert_64_64_12.bind1,
    show colData2 (⟨64, by decide⟩ : Fin 148)
        ((colE2 ⟨64, by decide⟩ 12 hp : ↥(Q2.reps ⟨64, by decide⟩)) : Coordinate 2)
        Q2.T64_64_2 = colFn colCert_64_64_12.D (m := 5) from colCert_64_64_12.bind2]
  exact alnAll_64_64_12 j hj hq

theorem leaf_64_64_13 (hp : 13 < (Q2.transData.getD 64 []).length)
    (j : Nat) (hj : j < (repChars.getD 64 []).length)
    (hq : (normIsRep.getD 64 []).getD j false = true) :
    species (Q2.reps (⟨64, by decide⟩ : Fin 148)) (colE2 ⟨64, by decide⟩ 13 hp)
        (rowE2 (⟨64, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨64, by decide⟩ : Fin 148))
        (colE1 ⟨64, by decide⟩ 13 (transLenTr ⟨64, by decide⟩ 13 hp))
        (rowE1 (⟨64, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨64, by decide⟩ : Fin 148) ⟨64, by decide⟩ _
      (validAt ⟨64, by decide⟩ (listedAt ⟨64, by decide⟩ hj))
      (colE1 ⟨64, by decide⟩ 13 (transLenTr ⟨64, by decide⟩ 13 hp)) T64_64
      hfix64_64 hinj64_64 hcardT64_64
      (fun i => conj_mem_of_fixedPoints _ _ (T64_64 i) (hfix64_64 i) _)
      ⟨64, by decide⟩ ⟨64, by decide⟩ _
      (Q2.validAt ⟨64, by decide⟩ (Q2.listedAt ⟨64, by decide⟩
        (alnCheck_rep ⟨64, by decide⟩ hj hq).1))
      (colE2 ⟨64, by decide⟩ 13 hp) Q2.T64_64_2 Q2.hfix64_64_2 Q2.hinj64_64_2
      Q2.hcardT64_64_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T64_64_2 i) (Q2.hfix64_64_2 i) _)
      ?_).symm
  rw [show colData1 (⟨64, by decide⟩ : Fin 148)
        ((colE1 ⟨64, by decide⟩ 13 (transLenTr ⟨64, by decide⟩ 13 hp) : ↥(reps ⟨64, by decide⟩)) : Coordinate 1)
        T64_64 = colFn colCert_64_64_13.D (m := 5) from colCert_64_64_13.bind1,
    show colData2 (⟨64, by decide⟩ : Fin 148)
        ((colE2 ⟨64, by decide⟩ 13 hp : ↥(Q2.reps ⟨64, by decide⟩)) : Coordinate 2)
        Q2.T64_64_2 = colFn colCert_64_64_13.D (m := 5) from colCert_64_64_13.bind2]
  exact alnAll_64_64_13 j hj hq

theorem leaf_64_64_14 (hp : 14 < (Q2.transData.getD 64 []).length)
    (j : Nat) (hj : j < (repChars.getD 64 []).length)
    (hq : (normIsRep.getD 64 []).getD j false = true) :
    species (Q2.reps (⟨64, by decide⟩ : Fin 148)) (colE2 ⟨64, by decide⟩ 14 hp)
        (rowE2 (⟨64, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨64, by decide⟩ : Fin 148))
        (colE1 ⟨64, by decide⟩ 14 (transLenTr ⟨64, by decide⟩ 14 hp))
        (rowE1 (⟨64, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨64, by decide⟩ : Fin 148) ⟨64, by decide⟩ _
      (validAt ⟨64, by decide⟩ (listedAt ⟨64, by decide⟩ hj))
      (colE1 ⟨64, by decide⟩ 14 (transLenTr ⟨64, by decide⟩ 14 hp)) T64_64
      hfix64_64 hinj64_64 hcardT64_64
      (fun i => conj_mem_of_fixedPoints _ _ (T64_64 i) (hfix64_64 i) _)
      ⟨64, by decide⟩ ⟨64, by decide⟩ _
      (Q2.validAt ⟨64, by decide⟩ (Q2.listedAt ⟨64, by decide⟩
        (alnCheck_rep ⟨64, by decide⟩ hj hq).1))
      (colE2 ⟨64, by decide⟩ 14 hp) Q2.T64_64_2 Q2.hfix64_64_2 Q2.hinj64_64_2
      Q2.hcardT64_64_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T64_64_2 i) (Q2.hfix64_64_2 i) _)
      ?_).symm
  rw [show colData1 (⟨64, by decide⟩ : Fin 148)
        ((colE1 ⟨64, by decide⟩ 14 (transLenTr ⟨64, by decide⟩ 14 hp) : ↥(reps ⟨64, by decide⟩)) : Coordinate 1)
        T64_64 = colFn colCert_64_64_14.D (m := 5) from colCert_64_64_14.bind1,
    show colData2 (⟨64, by decide⟩ : Fin 148)
        ((colE2 ⟨64, by decide⟩ 14 hp : ↥(Q2.reps ⟨64, by decide⟩)) : Coordinate 2)
        Q2.T64_64_2 = colFn colCert_64_64_14.D (m := 5) from colCert_64_64_14.bind2]
  exact alnAll_64_64_14 j hj hq

theorem leaf_64_64_15 (hp : 15 < (Q2.transData.getD 64 []).length)
    (j : Nat) (hj : j < (repChars.getD 64 []).length)
    (hq : (normIsRep.getD 64 []).getD j false = true) :
    species (Q2.reps (⟨64, by decide⟩ : Fin 148)) (colE2 ⟨64, by decide⟩ 15 hp)
        (rowE2 (⟨64, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨64, by decide⟩ : Fin 148))
        (colE1 ⟨64, by decide⟩ 15 (transLenTr ⟨64, by decide⟩ 15 hp))
        (rowE1 (⟨64, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨64, by decide⟩ : Fin 148) ⟨64, by decide⟩ _
      (validAt ⟨64, by decide⟩ (listedAt ⟨64, by decide⟩ hj))
      (colE1 ⟨64, by decide⟩ 15 (transLenTr ⟨64, by decide⟩ 15 hp)) T64_64
      hfix64_64 hinj64_64 hcardT64_64
      (fun i => conj_mem_of_fixedPoints _ _ (T64_64 i) (hfix64_64 i) _)
      ⟨64, by decide⟩ ⟨64, by decide⟩ _
      (Q2.validAt ⟨64, by decide⟩ (Q2.listedAt ⟨64, by decide⟩
        (alnCheck_rep ⟨64, by decide⟩ hj hq).1))
      (colE2 ⟨64, by decide⟩ 15 hp) Q2.T64_64_2 Q2.hfix64_64_2 Q2.hinj64_64_2
      Q2.hcardT64_64_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T64_64_2 i) (Q2.hfix64_64_2 i) _)
      ?_).symm
  rw [show colData1 (⟨64, by decide⟩ : Fin 148)
        ((colE1 ⟨64, by decide⟩ 15 (transLenTr ⟨64, by decide⟩ 15 hp) : ↥(reps ⟨64, by decide⟩)) : Coordinate 1)
        T64_64 = colFn colCert_64_64_15.D (m := 5) from colCert_64_64_15.bind1,
    show colData2 (⟨64, by decide⟩ : Fin 148)
        ((colE2 ⟨64, by decide⟩ 15 hp : ↥(Q2.reps ⟨64, by decide⟩)) : Coordinate 2)
        Q2.T64_64_2 = colFn colCert_64_64_15.D (m := 5) from colCert_64_64_15.bind2]
  exact alnAll_64_64_15 j hj hq

theorem leaf_64_64_16 (hp : 16 < (Q2.transData.getD 64 []).length)
    (j : Nat) (hj : j < (repChars.getD 64 []).length)
    (hq : (normIsRep.getD 64 []).getD j false = true) :
    species (Q2.reps (⟨64, by decide⟩ : Fin 148)) (colE2 ⟨64, by decide⟩ 16 hp)
        (rowE2 (⟨64, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨64, by decide⟩ : Fin 148))
        (colE1 ⟨64, by decide⟩ 16 (transLenTr ⟨64, by decide⟩ 16 hp))
        (rowE1 (⟨64, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨64, by decide⟩ : Fin 148) ⟨64, by decide⟩ _
      (validAt ⟨64, by decide⟩ (listedAt ⟨64, by decide⟩ hj))
      (colE1 ⟨64, by decide⟩ 16 (transLenTr ⟨64, by decide⟩ 16 hp)) T64_64
      hfix64_64 hinj64_64 hcardT64_64
      (fun i => conj_mem_of_fixedPoints _ _ (T64_64 i) (hfix64_64 i) _)
      ⟨64, by decide⟩ ⟨64, by decide⟩ _
      (Q2.validAt ⟨64, by decide⟩ (Q2.listedAt ⟨64, by decide⟩
        (alnCheck_rep ⟨64, by decide⟩ hj hq).1))
      (colE2 ⟨64, by decide⟩ 16 hp) Q2.T64_64_2 Q2.hfix64_64_2 Q2.hinj64_64_2
      Q2.hcardT64_64_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T64_64_2 i) (Q2.hfix64_64_2 i) _)
      ?_).symm
  rw [show colData1 (⟨64, by decide⟩ : Fin 148)
        ((colE1 ⟨64, by decide⟩ 16 (transLenTr ⟨64, by decide⟩ 16 hp) : ↥(reps ⟨64, by decide⟩)) : Coordinate 1)
        T64_64 = colFn colCert_64_64_16.D (m := 5) from colCert_64_64_16.bind1,
    show colData2 (⟨64, by decide⟩ : Fin 148)
        ((colE2 ⟨64, by decide⟩ 16 hp : ↥(Q2.reps ⟨64, by decide⟩)) : Coordinate 2)
        Q2.T64_64_2 = colFn colCert_64_64_16.D (m := 5) from colCert_64_64_16.bind2]
  exact alnAll_64_64_16 j hj hq

theorem leaf_64_64_17 (hp : 17 < (Q2.transData.getD 64 []).length)
    (j : Nat) (hj : j < (repChars.getD 64 []).length)
    (hq : (normIsRep.getD 64 []).getD j false = true) :
    species (Q2.reps (⟨64, by decide⟩ : Fin 148)) (colE2 ⟨64, by decide⟩ 17 hp)
        (rowE2 (⟨64, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨64, by decide⟩ : Fin 148))
        (colE1 ⟨64, by decide⟩ 17 (transLenTr ⟨64, by decide⟩ 17 hp))
        (rowE1 (⟨64, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨64, by decide⟩ : Fin 148) ⟨64, by decide⟩ _
      (validAt ⟨64, by decide⟩ (listedAt ⟨64, by decide⟩ hj))
      (colE1 ⟨64, by decide⟩ 17 (transLenTr ⟨64, by decide⟩ 17 hp)) T64_64
      hfix64_64 hinj64_64 hcardT64_64
      (fun i => conj_mem_of_fixedPoints _ _ (T64_64 i) (hfix64_64 i) _)
      ⟨64, by decide⟩ ⟨64, by decide⟩ _
      (Q2.validAt ⟨64, by decide⟩ (Q2.listedAt ⟨64, by decide⟩
        (alnCheck_rep ⟨64, by decide⟩ hj hq).1))
      (colE2 ⟨64, by decide⟩ 17 hp) Q2.T64_64_2 Q2.hfix64_64_2 Q2.hinj64_64_2
      Q2.hcardT64_64_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T64_64_2 i) (Q2.hfix64_64_2 i) _)
      ?_).symm
  rw [show colData1 (⟨64, by decide⟩ : Fin 148)
        ((colE1 ⟨64, by decide⟩ 17 (transLenTr ⟨64, by decide⟩ 17 hp) : ↥(reps ⟨64, by decide⟩)) : Coordinate 1)
        T64_64 = colFn colCert_64_64_17.D (m := 5) from colCert_64_64_17.bind1,
    show colData2 (⟨64, by decide⟩ : Fin 148)
        ((colE2 ⟨64, by decide⟩ 17 hp : ↥(Q2.reps ⟨64, by decide⟩)) : Coordinate 2)
        Q2.T64_64_2 = colFn colCert_64_64_17.D (m := 5) from colCert_64_64_17.bind2]
  exact alnAll_64_64_17 j hj hq

theorem leaf_64_64_18 (hp : 18 < (Q2.transData.getD 64 []).length)
    (j : Nat) (hj : j < (repChars.getD 64 []).length)
    (hq : (normIsRep.getD 64 []).getD j false = true) :
    species (Q2.reps (⟨64, by decide⟩ : Fin 148)) (colE2 ⟨64, by decide⟩ 18 hp)
        (rowE2 (⟨64, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨64, by decide⟩ : Fin 148))
        (colE1 ⟨64, by decide⟩ 18 (transLenTr ⟨64, by decide⟩ 18 hp))
        (rowE1 (⟨64, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨64, by decide⟩ : Fin 148) ⟨64, by decide⟩ _
      (validAt ⟨64, by decide⟩ (listedAt ⟨64, by decide⟩ hj))
      (colE1 ⟨64, by decide⟩ 18 (transLenTr ⟨64, by decide⟩ 18 hp)) T64_64
      hfix64_64 hinj64_64 hcardT64_64
      (fun i => conj_mem_of_fixedPoints _ _ (T64_64 i) (hfix64_64 i) _)
      ⟨64, by decide⟩ ⟨64, by decide⟩ _
      (Q2.validAt ⟨64, by decide⟩ (Q2.listedAt ⟨64, by decide⟩
        (alnCheck_rep ⟨64, by decide⟩ hj hq).1))
      (colE2 ⟨64, by decide⟩ 18 hp) Q2.T64_64_2 Q2.hfix64_64_2 Q2.hinj64_64_2
      Q2.hcardT64_64_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T64_64_2 i) (Q2.hfix64_64_2 i) _)
      ?_).symm
  rw [show colData1 (⟨64, by decide⟩ : Fin 148)
        ((colE1 ⟨64, by decide⟩ 18 (transLenTr ⟨64, by decide⟩ 18 hp) : ↥(reps ⟨64, by decide⟩)) : Coordinate 1)
        T64_64 = colFn colCert_64_64_18.D (m := 5) from colCert_64_64_18.bind1,
    show colData2 (⟨64, by decide⟩ : Fin 148)
        ((colE2 ⟨64, by decide⟩ 18 hp : ↥(Q2.reps ⟨64, by decide⟩)) : Coordinate 2)
        Q2.T64_64_2 = colFn colCert_64_64_18.D (m := 5) from colCert_64_64_18.bind2]
  exact alnAll_64_64_18 j hj hq

theorem leaf_64_64_19 (hp : 19 < (Q2.transData.getD 64 []).length)
    (j : Nat) (hj : j < (repChars.getD 64 []).length)
    (hq : (normIsRep.getD 64 []).getD j false = true) :
    species (Q2.reps (⟨64, by decide⟩ : Fin 148)) (colE2 ⟨64, by decide⟩ 19 hp)
        (rowE2 (⟨64, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨64, by decide⟩ : Fin 148))
        (colE1 ⟨64, by decide⟩ 19 (transLenTr ⟨64, by decide⟩ 19 hp))
        (rowE1 (⟨64, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨64, by decide⟩ : Fin 148) ⟨64, by decide⟩ _
      (validAt ⟨64, by decide⟩ (listedAt ⟨64, by decide⟩ hj))
      (colE1 ⟨64, by decide⟩ 19 (transLenTr ⟨64, by decide⟩ 19 hp)) T64_64
      hfix64_64 hinj64_64 hcardT64_64
      (fun i => conj_mem_of_fixedPoints _ _ (T64_64 i) (hfix64_64 i) _)
      ⟨64, by decide⟩ ⟨64, by decide⟩ _
      (Q2.validAt ⟨64, by decide⟩ (Q2.listedAt ⟨64, by decide⟩
        (alnCheck_rep ⟨64, by decide⟩ hj hq).1))
      (colE2 ⟨64, by decide⟩ 19 hp) Q2.T64_64_2 Q2.hfix64_64_2 Q2.hinj64_64_2
      Q2.hcardT64_64_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T64_64_2 i) (Q2.hfix64_64_2 i) _)
      ?_).symm
  rw [show colData1 (⟨64, by decide⟩ : Fin 148)
        ((colE1 ⟨64, by decide⟩ 19 (transLenTr ⟨64, by decide⟩ 19 hp) : ↥(reps ⟨64, by decide⟩)) : Coordinate 1)
        T64_64 = colFn colCert_64_64_19.D (m := 5) from colCert_64_64_19.bind1,
    show colData2 (⟨64, by decide⟩ : Fin 148)
        ((colE2 ⟨64, by decide⟩ 19 hp : ↥(Q2.reps ⟨64, by decide⟩)) : Coordinate 2)
        Q2.T64_64_2 = colFn colCert_64_64_19.D (m := 5) from colCert_64_64_19.bind2]
  exact alnAll_64_64_19 j hj hq

theorem leaf_64_64_20 (hp : 20 < (Q2.transData.getD 64 []).length)
    (j : Nat) (hj : j < (repChars.getD 64 []).length)
    (hq : (normIsRep.getD 64 []).getD j false = true) :
    species (Q2.reps (⟨64, by decide⟩ : Fin 148)) (colE2 ⟨64, by decide⟩ 20 hp)
        (rowE2 (⟨64, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨64, by decide⟩ : Fin 148))
        (colE1 ⟨64, by decide⟩ 20 (transLenTr ⟨64, by decide⟩ 20 hp))
        (rowE1 (⟨64, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨64, by decide⟩ : Fin 148) ⟨64, by decide⟩ _
      (validAt ⟨64, by decide⟩ (listedAt ⟨64, by decide⟩ hj))
      (colE1 ⟨64, by decide⟩ 20 (transLenTr ⟨64, by decide⟩ 20 hp)) T64_64
      hfix64_64 hinj64_64 hcardT64_64
      (fun i => conj_mem_of_fixedPoints _ _ (T64_64 i) (hfix64_64 i) _)
      ⟨64, by decide⟩ ⟨64, by decide⟩ _
      (Q2.validAt ⟨64, by decide⟩ (Q2.listedAt ⟨64, by decide⟩
        (alnCheck_rep ⟨64, by decide⟩ hj hq).1))
      (colE2 ⟨64, by decide⟩ 20 hp) Q2.T64_64_2 Q2.hfix64_64_2 Q2.hinj64_64_2
      Q2.hcardT64_64_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T64_64_2 i) (Q2.hfix64_64_2 i) _)
      ?_).symm
  rw [show colData1 (⟨64, by decide⟩ : Fin 148)
        ((colE1 ⟨64, by decide⟩ 20 (transLenTr ⟨64, by decide⟩ 20 hp) : ↥(reps ⟨64, by decide⟩)) : Coordinate 1)
        T64_64 = colFn colCert_64_64_20.D (m := 5) from colCert_64_64_20.bind1,
    show colData2 (⟨64, by decide⟩ : Fin 148)
        ((colE2 ⟨64, by decide⟩ 20 hp : ↥(Q2.reps ⟨64, by decide⟩)) : Coordinate 2)
        Q2.T64_64_2 = colFn colCert_64_64_20.D (m := 5) from colCert_64_64_20.bind2]
  exact alnAll_64_64_20 j hj hq

theorem leaf_64_64_21 (hp : 21 < (Q2.transData.getD 64 []).length)
    (j : Nat) (hj : j < (repChars.getD 64 []).length)
    (hq : (normIsRep.getD 64 []).getD j false = true) :
    species (Q2.reps (⟨64, by decide⟩ : Fin 148)) (colE2 ⟨64, by decide⟩ 21 hp)
        (rowE2 (⟨64, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨64, by decide⟩ : Fin 148))
        (colE1 ⟨64, by decide⟩ 21 (transLenTr ⟨64, by decide⟩ 21 hp))
        (rowE1 (⟨64, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨64, by decide⟩ : Fin 148) ⟨64, by decide⟩ _
      (validAt ⟨64, by decide⟩ (listedAt ⟨64, by decide⟩ hj))
      (colE1 ⟨64, by decide⟩ 21 (transLenTr ⟨64, by decide⟩ 21 hp)) T64_64
      hfix64_64 hinj64_64 hcardT64_64
      (fun i => conj_mem_of_fixedPoints _ _ (T64_64 i) (hfix64_64 i) _)
      ⟨64, by decide⟩ ⟨64, by decide⟩ _
      (Q2.validAt ⟨64, by decide⟩ (Q2.listedAt ⟨64, by decide⟩
        (alnCheck_rep ⟨64, by decide⟩ hj hq).1))
      (colE2 ⟨64, by decide⟩ 21 hp) Q2.T64_64_2 Q2.hfix64_64_2 Q2.hinj64_64_2
      Q2.hcardT64_64_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T64_64_2 i) (Q2.hfix64_64_2 i) _)
      ?_).symm
  rw [show colData1 (⟨64, by decide⟩ : Fin 148)
        ((colE1 ⟨64, by decide⟩ 21 (transLenTr ⟨64, by decide⟩ 21 hp) : ↥(reps ⟨64, by decide⟩)) : Coordinate 1)
        T64_64 = colFn colCert_64_64_21.D (m := 5) from colCert_64_64_21.bind1,
    show colData2 (⟨64, by decide⟩ : Fin 148)
        ((colE2 ⟨64, by decide⟩ 21 hp : ↥(Q2.reps ⟨64, by decide⟩)) : Coordinate 2)
        Q2.T64_64_2 = colFn colCert_64_64_21.D (m := 5) from colCert_64_64_21.bind2]
  exact alnAll_64_64_21 j hj hq

theorem leaf_64_64_22 (hp : 22 < (Q2.transData.getD 64 []).length)
    (j : Nat) (hj : j < (repChars.getD 64 []).length)
    (hq : (normIsRep.getD 64 []).getD j false = true) :
    species (Q2.reps (⟨64, by decide⟩ : Fin 148)) (colE2 ⟨64, by decide⟩ 22 hp)
        (rowE2 (⟨64, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨64, by decide⟩ : Fin 148))
        (colE1 ⟨64, by decide⟩ 22 (transLenTr ⟨64, by decide⟩ 22 hp))
        (rowE1 (⟨64, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨64, by decide⟩ : Fin 148) ⟨64, by decide⟩ _
      (validAt ⟨64, by decide⟩ (listedAt ⟨64, by decide⟩ hj))
      (colE1 ⟨64, by decide⟩ 22 (transLenTr ⟨64, by decide⟩ 22 hp)) T64_64
      hfix64_64 hinj64_64 hcardT64_64
      (fun i => conj_mem_of_fixedPoints _ _ (T64_64 i) (hfix64_64 i) _)
      ⟨64, by decide⟩ ⟨64, by decide⟩ _
      (Q2.validAt ⟨64, by decide⟩ (Q2.listedAt ⟨64, by decide⟩
        (alnCheck_rep ⟨64, by decide⟩ hj hq).1))
      (colE2 ⟨64, by decide⟩ 22 hp) Q2.T64_64_2 Q2.hfix64_64_2 Q2.hinj64_64_2
      Q2.hcardT64_64_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T64_64_2 i) (Q2.hfix64_64_2 i) _)
      ?_).symm
  rw [show colData1 (⟨64, by decide⟩ : Fin 148)
        ((colE1 ⟨64, by decide⟩ 22 (transLenTr ⟨64, by decide⟩ 22 hp) : ↥(reps ⟨64, by decide⟩)) : Coordinate 1)
        T64_64 = colFn colCert_64_64_22.D (m := 5) from colCert_64_64_22.bind1,
    show colData2 (⟨64, by decide⟩ : Fin 148)
        ((colE2 ⟨64, by decide⟩ 22 hp : ↥(Q2.reps ⟨64, by decide⟩)) : Coordinate 2)
        Q2.T64_64_2 = colFn colCert_64_64_22.D (m := 5) from colCert_64_64_22.bind2]
  exact alnAll_64_64_22 j hj hq

theorem leaf_64_64_23 (hp : 23 < (Q2.transData.getD 64 []).length)
    (j : Nat) (hj : j < (repChars.getD 64 []).length)
    (hq : (normIsRep.getD 64 []).getD j false = true) :
    species (Q2.reps (⟨64, by decide⟩ : Fin 148)) (colE2 ⟨64, by decide⟩ 23 hp)
        (rowE2 (⟨64, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨64, by decide⟩ : Fin 148))
        (colE1 ⟨64, by decide⟩ 23 (transLenTr ⟨64, by decide⟩ 23 hp))
        (rowE1 (⟨64, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨64, by decide⟩ : Fin 148) ⟨64, by decide⟩ _
      (validAt ⟨64, by decide⟩ (listedAt ⟨64, by decide⟩ hj))
      (colE1 ⟨64, by decide⟩ 23 (transLenTr ⟨64, by decide⟩ 23 hp)) T64_64
      hfix64_64 hinj64_64 hcardT64_64
      (fun i => conj_mem_of_fixedPoints _ _ (T64_64 i) (hfix64_64 i) _)
      ⟨64, by decide⟩ ⟨64, by decide⟩ _
      (Q2.validAt ⟨64, by decide⟩ (Q2.listedAt ⟨64, by decide⟩
        (alnCheck_rep ⟨64, by decide⟩ hj hq).1))
      (colE2 ⟨64, by decide⟩ 23 hp) Q2.T64_64_2 Q2.hfix64_64_2 Q2.hinj64_64_2
      Q2.hcardT64_64_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T64_64_2 i) (Q2.hfix64_64_2 i) _)
      ?_).symm
  rw [show colData1 (⟨64, by decide⟩ : Fin 148)
        ((colE1 ⟨64, by decide⟩ 23 (transLenTr ⟨64, by decide⟩ 23 hp) : ↥(reps ⟨64, by decide⟩)) : Coordinate 1)
        T64_64 = colFn colCert_64_64_23.D (m := 5) from colCert_64_64_23.bind1,
    show colData2 (⟨64, by decide⟩ : Fin 148)
        ((colE2 ⟨64, by decide⟩ 23 hp : ↥(Q2.reps ⟨64, by decide⟩)) : Coordinate 2)
        Q2.T64_64_2 = colFn colCert_64_64_23.D (m := 5) from colCert_64_64_23.bind2]
  exact alnAll_64_64_23 j hj hq

theorem leaf_64_64_24 (hp : 24 < (Q2.transData.getD 64 []).length)
    (j : Nat) (hj : j < (repChars.getD 64 []).length)
    (hq : (normIsRep.getD 64 []).getD j false = true) :
    species (Q2.reps (⟨64, by decide⟩ : Fin 148)) (colE2 ⟨64, by decide⟩ 24 hp)
        (rowE2 (⟨64, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨64, by decide⟩ : Fin 148))
        (colE1 ⟨64, by decide⟩ 24 (transLenTr ⟨64, by decide⟩ 24 hp))
        (rowE1 (⟨64, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨64, by decide⟩ : Fin 148) ⟨64, by decide⟩ _
      (validAt ⟨64, by decide⟩ (listedAt ⟨64, by decide⟩ hj))
      (colE1 ⟨64, by decide⟩ 24 (transLenTr ⟨64, by decide⟩ 24 hp)) T64_64
      hfix64_64 hinj64_64 hcardT64_64
      (fun i => conj_mem_of_fixedPoints _ _ (T64_64 i) (hfix64_64 i) _)
      ⟨64, by decide⟩ ⟨64, by decide⟩ _
      (Q2.validAt ⟨64, by decide⟩ (Q2.listedAt ⟨64, by decide⟩
        (alnCheck_rep ⟨64, by decide⟩ hj hq).1))
      (colE2 ⟨64, by decide⟩ 24 hp) Q2.T64_64_2 Q2.hfix64_64_2 Q2.hinj64_64_2
      Q2.hcardT64_64_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T64_64_2 i) (Q2.hfix64_64_2 i) _)
      ?_).symm
  rw [show colData1 (⟨64, by decide⟩ : Fin 148)
        ((colE1 ⟨64, by decide⟩ 24 (transLenTr ⟨64, by decide⟩ 24 hp) : ↥(reps ⟨64, by decide⟩)) : Coordinate 1)
        T64_64 = colFn colCert_64_64_24.D (m := 5) from colCert_64_64_24.bind1,
    show colData2 (⟨64, by decide⟩ : Fin 148)
        ((colE2 ⟨64, by decide⟩ 24 hp : ↥(Q2.reps ⟨64, by decide⟩)) : Coordinate 2)
        Q2.T64_64_2 = colFn colCert_64_64_24.D (m := 5) from colCert_64_64_24.bind2]
  exact alnAll_64_64_24 j hj hq

theorem leaf_64_64_25 (hp : 25 < (Q2.transData.getD 64 []).length)
    (j : Nat) (hj : j < (repChars.getD 64 []).length)
    (hq : (normIsRep.getD 64 []).getD j false = true) :
    species (Q2.reps (⟨64, by decide⟩ : Fin 148)) (colE2 ⟨64, by decide⟩ 25 hp)
        (rowE2 (⟨64, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨64, by decide⟩ : Fin 148))
        (colE1 ⟨64, by decide⟩ 25 (transLenTr ⟨64, by decide⟩ 25 hp))
        (rowE1 (⟨64, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨64, by decide⟩ : Fin 148) ⟨64, by decide⟩ _
      (validAt ⟨64, by decide⟩ (listedAt ⟨64, by decide⟩ hj))
      (colE1 ⟨64, by decide⟩ 25 (transLenTr ⟨64, by decide⟩ 25 hp)) T64_64
      hfix64_64 hinj64_64 hcardT64_64
      (fun i => conj_mem_of_fixedPoints _ _ (T64_64 i) (hfix64_64 i) _)
      ⟨64, by decide⟩ ⟨64, by decide⟩ _
      (Q2.validAt ⟨64, by decide⟩ (Q2.listedAt ⟨64, by decide⟩
        (alnCheck_rep ⟨64, by decide⟩ hj hq).1))
      (colE2 ⟨64, by decide⟩ 25 hp) Q2.T64_64_2 Q2.hfix64_64_2 Q2.hinj64_64_2
      Q2.hcardT64_64_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T64_64_2 i) (Q2.hfix64_64_2 i) _)
      ?_).symm
  rw [show colData1 (⟨64, by decide⟩ : Fin 148)
        ((colE1 ⟨64, by decide⟩ 25 (transLenTr ⟨64, by decide⟩ 25 hp) : ↥(reps ⟨64, by decide⟩)) : Coordinate 1)
        T64_64 = colFn colCert_64_64_25.D (m := 5) from colCert_64_64_25.bind1,
    show colData2 (⟨64, by decide⟩ : Fin 148)
        ((colE2 ⟨64, by decide⟩ 25 hp : ↥(Q2.reps ⟨64, by decide⟩)) : Coordinate 2)
        Q2.T64_64_2 = colFn colCert_64_64_25.D (m := 5) from colCert_64_64_25.bind2]
  exact alnAll_64_64_25 j hj hq

theorem leaf_64_64_30 (hp : 30 < (Q2.transData.getD 64 []).length)
    (j : Nat) (hj : j < (repChars.getD 64 []).length)
    (hq : (normIsRep.getD 64 []).getD j false = true) :
    species (Q2.reps (⟨64, by decide⟩ : Fin 148)) (colE2 ⟨64, by decide⟩ 30 hp)
        (rowE2 (⟨64, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨64, by decide⟩ : Fin 148))
        (colE1 ⟨64, by decide⟩ 30 (transLenTr ⟨64, by decide⟩ 30 hp))
        (rowE1 (⟨64, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨64, by decide⟩ : Fin 148) ⟨64, by decide⟩ _
      (validAt ⟨64, by decide⟩ (listedAt ⟨64, by decide⟩ hj))
      (colE1 ⟨64, by decide⟩ 30 (transLenTr ⟨64, by decide⟩ 30 hp)) T64_64
      hfix64_64 hinj64_64 hcardT64_64
      (fun i => conj_mem_of_fixedPoints _ _ (T64_64 i) (hfix64_64 i) _)
      ⟨64, by decide⟩ ⟨64, by decide⟩ _
      (Q2.validAt ⟨64, by decide⟩ (Q2.listedAt ⟨64, by decide⟩
        (alnCheck_rep ⟨64, by decide⟩ hj hq).1))
      (colE2 ⟨64, by decide⟩ 30 hp) Q2.T64_64_2 Q2.hfix64_64_2 Q2.hinj64_64_2
      Q2.hcardT64_64_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T64_64_2 i) (Q2.hfix64_64_2 i) _)
      ?_).symm
  rw [show colData1 (⟨64, by decide⟩ : Fin 148)
        ((colE1 ⟨64, by decide⟩ 30 (transLenTr ⟨64, by decide⟩ 30 hp) : ↥(reps ⟨64, by decide⟩)) : Coordinate 1)
        T64_64 = colFn colCert_64_64_30.D (m := 5) from colCert_64_64_30.bind1,
    show colData2 (⟨64, by decide⟩ : Fin 148)
        ((colE2 ⟨64, by decide⟩ 30 hp : ↥(Q2.reps ⟨64, by decide⟩)) : Coordinate 2)
        Q2.T64_64_2 = colFn colCert_64_64_30.D (m := 5) from colCert_64_64_30.bind2]
  exact alnAll_64_64_30 j hj hq

theorem leaf_64_64_35 (hp : 35 < (Q2.transData.getD 64 []).length)
    (j : Nat) (hj : j < (repChars.getD 64 []).length)
    (hq : (normIsRep.getD 64 []).getD j false = true) :
    species (Q2.reps (⟨64, by decide⟩ : Fin 148)) (colE2 ⟨64, by decide⟩ 35 hp)
        (rowE2 (⟨64, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨64, by decide⟩ : Fin 148))
        (colE1 ⟨64, by decide⟩ 35 (transLenTr ⟨64, by decide⟩ 35 hp))
        (rowE1 (⟨64, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨64, by decide⟩ : Fin 148) ⟨64, by decide⟩ _
      (validAt ⟨64, by decide⟩ (listedAt ⟨64, by decide⟩ hj))
      (colE1 ⟨64, by decide⟩ 35 (transLenTr ⟨64, by decide⟩ 35 hp)) T64_64
      hfix64_64 hinj64_64 hcardT64_64
      (fun i => conj_mem_of_fixedPoints _ _ (T64_64 i) (hfix64_64 i) _)
      ⟨64, by decide⟩ ⟨64, by decide⟩ _
      (Q2.validAt ⟨64, by decide⟩ (Q2.listedAt ⟨64, by decide⟩
        (alnCheck_rep ⟨64, by decide⟩ hj hq).1))
      (colE2 ⟨64, by decide⟩ 35 hp) Q2.T64_64_2 Q2.hfix64_64_2 Q2.hinj64_64_2
      Q2.hcardT64_64_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T64_64_2 i) (Q2.hfix64_64_2 i) _)
      ?_).symm
  rw [show colData1 (⟨64, by decide⟩ : Fin 148)
        ((colE1 ⟨64, by decide⟩ 35 (transLenTr ⟨64, by decide⟩ 35 hp) : ↥(reps ⟨64, by decide⟩)) : Coordinate 1)
        T64_64 = colFn colCert_64_64_35.D (m := 5) from colCert_64_64_35.bind1,
    show colData2 (⟨64, by decide⟩ : Fin 148)
        ((colE2 ⟨64, by decide⟩ 35 hp : ↥(Q2.reps ⟨64, by decide⟩)) : Coordinate 2)
        Q2.T64_64_2 = colFn colCert_64_64_35.D (m := 5) from colCert_64_64_35.bind2]
  exact alnAll_64_64_35 j hj hq

theorem leaf_64_64_40 (hp : 40 < (Q2.transData.getD 64 []).length)
    (j : Nat) (hj : j < (repChars.getD 64 []).length)
    (hq : (normIsRep.getD 64 []).getD j false = true) :
    species (Q2.reps (⟨64, by decide⟩ : Fin 148)) (colE2 ⟨64, by decide⟩ 40 hp)
        (rowE2 (⟨64, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨64, by decide⟩ : Fin 148))
        (colE1 ⟨64, by decide⟩ 40 (transLenTr ⟨64, by decide⟩ 40 hp))
        (rowE1 (⟨64, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨64, by decide⟩ : Fin 148) ⟨64, by decide⟩ _
      (validAt ⟨64, by decide⟩ (listedAt ⟨64, by decide⟩ hj))
      (colE1 ⟨64, by decide⟩ 40 (transLenTr ⟨64, by decide⟩ 40 hp)) T64_64
      hfix64_64 hinj64_64 hcardT64_64
      (fun i => conj_mem_of_fixedPoints _ _ (T64_64 i) (hfix64_64 i) _)
      ⟨64, by decide⟩ ⟨64, by decide⟩ _
      (Q2.validAt ⟨64, by decide⟩ (Q2.listedAt ⟨64, by decide⟩
        (alnCheck_rep ⟨64, by decide⟩ hj hq).1))
      (colE2 ⟨64, by decide⟩ 40 hp) Q2.T64_64_2 Q2.hfix64_64_2 Q2.hinj64_64_2
      Q2.hcardT64_64_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T64_64_2 i) (Q2.hfix64_64_2 i) _)
      ?_).symm
  rw [show colData1 (⟨64, by decide⟩ : Fin 148)
        ((colE1 ⟨64, by decide⟩ 40 (transLenTr ⟨64, by decide⟩ 40 hp) : ↥(reps ⟨64, by decide⟩)) : Coordinate 1)
        T64_64 = colFn colCert_64_64_40.D (m := 5) from colCert_64_64_40.bind1,
    show colData2 (⟨64, by decide⟩ : Fin 148)
        ((colE2 ⟨64, by decide⟩ 40 hp : ↥(Q2.reps ⟨64, by decide⟩)) : Coordinate 2)
        Q2.T64_64_2 = colFn colCert_64_64_40.D (m := 5) from colCert_64_64_40.bind2]
  exact alnAll_64_64_40 j hj hq

theorem leaf_64_64_45 (hp : 45 < (Q2.transData.getD 64 []).length)
    (j : Nat) (hj : j < (repChars.getD 64 []).length)
    (hq : (normIsRep.getD 64 []).getD j false = true) :
    species (Q2.reps (⟨64, by decide⟩ : Fin 148)) (colE2 ⟨64, by decide⟩ 45 hp)
        (rowE2 (⟨64, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨64, by decide⟩ : Fin 148))
        (colE1 ⟨64, by decide⟩ 45 (transLenTr ⟨64, by decide⟩ 45 hp))
        (rowE1 (⟨64, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨64, by decide⟩ : Fin 148) ⟨64, by decide⟩ _
      (validAt ⟨64, by decide⟩ (listedAt ⟨64, by decide⟩ hj))
      (colE1 ⟨64, by decide⟩ 45 (transLenTr ⟨64, by decide⟩ 45 hp)) T64_64
      hfix64_64 hinj64_64 hcardT64_64
      (fun i => conj_mem_of_fixedPoints _ _ (T64_64 i) (hfix64_64 i) _)
      ⟨64, by decide⟩ ⟨64, by decide⟩ _
      (Q2.validAt ⟨64, by decide⟩ (Q2.listedAt ⟨64, by decide⟩
        (alnCheck_rep ⟨64, by decide⟩ hj hq).1))
      (colE2 ⟨64, by decide⟩ 45 hp) Q2.T64_64_2 Q2.hfix64_64_2 Q2.hinj64_64_2
      Q2.hcardT64_64_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T64_64_2 i) (Q2.hfix64_64_2 i) _)
      ?_).symm
  rw [show colData1 (⟨64, by decide⟩ : Fin 148)
        ((colE1 ⟨64, by decide⟩ 45 (transLenTr ⟨64, by decide⟩ 45 hp) : ↥(reps ⟨64, by decide⟩)) : Coordinate 1)
        T64_64 = colFn colCert_64_64_45.D (m := 5) from colCert_64_64_45.bind1,
    show colData2 (⟨64, by decide⟩ : Fin 148)
        ((colE2 ⟨64, by decide⟩ 45 hp : ↥(Q2.reps ⟨64, by decide⟩)) : Coordinate 2)
        Q2.T64_64_2 = colFn colCert_64_64_45.D (m := 5) from colCert_64_64_45.bind2]
  exact alnAll_64_64_45 j hj hq

theorem leaf_64_64_50 (hp : 50 < (Q2.transData.getD 64 []).length)
    (j : Nat) (hj : j < (repChars.getD 64 []).length)
    (hq : (normIsRep.getD 64 []).getD j false = true) :
    species (Q2.reps (⟨64, by decide⟩ : Fin 148)) (colE2 ⟨64, by decide⟩ 50 hp)
        (rowE2 (⟨64, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨64, by decide⟩ : Fin 148))
        (colE1 ⟨64, by decide⟩ 50 (transLenTr ⟨64, by decide⟩ 50 hp))
        (rowE1 (⟨64, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨64, by decide⟩ : Fin 148) ⟨64, by decide⟩ _
      (validAt ⟨64, by decide⟩ (listedAt ⟨64, by decide⟩ hj))
      (colE1 ⟨64, by decide⟩ 50 (transLenTr ⟨64, by decide⟩ 50 hp)) T64_64
      hfix64_64 hinj64_64 hcardT64_64
      (fun i => conj_mem_of_fixedPoints _ _ (T64_64 i) (hfix64_64 i) _)
      ⟨64, by decide⟩ ⟨64, by decide⟩ _
      (Q2.validAt ⟨64, by decide⟩ (Q2.listedAt ⟨64, by decide⟩
        (alnCheck_rep ⟨64, by decide⟩ hj hq).1))
      (colE2 ⟨64, by decide⟩ 50 hp) Q2.T64_64_2 Q2.hfix64_64_2 Q2.hinj64_64_2
      Q2.hcardT64_64_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T64_64_2 i) (Q2.hfix64_64_2 i) _)
      ?_).symm
  rw [show colData1 (⟨64, by decide⟩ : Fin 148)
        ((colE1 ⟨64, by decide⟩ 50 (transLenTr ⟨64, by decide⟩ 50 hp) : ↥(reps ⟨64, by decide⟩)) : Coordinate 1)
        T64_64 = colFn colCert_64_64_50.D (m := 5) from colCert_64_64_50.bind1,
    show colData2 (⟨64, by decide⟩ : Fin 148)
        ((colE2 ⟨64, by decide⟩ 50 hp : ↥(Q2.reps ⟨64, by decide⟩)) : Coordinate 2)
        Q2.T64_64_2 = colFn colCert_64_64_50.D (m := 5) from colCert_64_64_50.bind2]
  exact alnAll_64_64_50 j hj hq

theorem leaf_64_64_55 (hp : 55 < (Q2.transData.getD 64 []).length)
    (j : Nat) (hj : j < (repChars.getD 64 []).length)
    (hq : (normIsRep.getD 64 []).getD j false = true) :
    species (Q2.reps (⟨64, by decide⟩ : Fin 148)) (colE2 ⟨64, by decide⟩ 55 hp)
        (rowE2 (⟨64, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨64, by decide⟩ : Fin 148))
        (colE1 ⟨64, by decide⟩ 55 (transLenTr ⟨64, by decide⟩ 55 hp))
        (rowE1 (⟨64, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨64, by decide⟩ : Fin 148) ⟨64, by decide⟩ _
      (validAt ⟨64, by decide⟩ (listedAt ⟨64, by decide⟩ hj))
      (colE1 ⟨64, by decide⟩ 55 (transLenTr ⟨64, by decide⟩ 55 hp)) T64_64
      hfix64_64 hinj64_64 hcardT64_64
      (fun i => conj_mem_of_fixedPoints _ _ (T64_64 i) (hfix64_64 i) _)
      ⟨64, by decide⟩ ⟨64, by decide⟩ _
      (Q2.validAt ⟨64, by decide⟩ (Q2.listedAt ⟨64, by decide⟩
        (alnCheck_rep ⟨64, by decide⟩ hj hq).1))
      (colE2 ⟨64, by decide⟩ 55 hp) Q2.T64_64_2 Q2.hfix64_64_2 Q2.hinj64_64_2
      Q2.hcardT64_64_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T64_64_2 i) (Q2.hfix64_64_2 i) _)
      ?_).symm
  rw [show colData1 (⟨64, by decide⟩ : Fin 148)
        ((colE1 ⟨64, by decide⟩ 55 (transLenTr ⟨64, by decide⟩ 55 hp) : ↥(reps ⟨64, by decide⟩)) : Coordinate 1)
        T64_64 = colFn colCert_64_64_55.D (m := 5) from colCert_64_64_55.bind1,
    show colData2 (⟨64, by decide⟩ : Fin 148)
        ((colE2 ⟨64, by decide⟩ 55 hp : ↥(Q2.reps ⟨64, by decide⟩)) : Coordinate 2)
        Q2.T64_64_2 = colFn colCert_64_64_55.D (m := 5) from colCert_64_64_55.bind2]
  exact alnAll_64_64_55 j hj hq

theorem leaf_64_64_60 (hp : 60 < (Q2.transData.getD 64 []).length)
    (j : Nat) (hj : j < (repChars.getD 64 []).length)
    (hq : (normIsRep.getD 64 []).getD j false = true) :
    species (Q2.reps (⟨64, by decide⟩ : Fin 148)) (colE2 ⟨64, by decide⟩ 60 hp)
        (rowE2 (⟨64, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨64, by decide⟩ : Fin 148))
        (colE1 ⟨64, by decide⟩ 60 (transLenTr ⟨64, by decide⟩ 60 hp))
        (rowE1 (⟨64, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨64, by decide⟩ : Fin 148) ⟨64, by decide⟩ _
      (validAt ⟨64, by decide⟩ (listedAt ⟨64, by decide⟩ hj))
      (colE1 ⟨64, by decide⟩ 60 (transLenTr ⟨64, by decide⟩ 60 hp)) T64_64
      hfix64_64 hinj64_64 hcardT64_64
      (fun i => conj_mem_of_fixedPoints _ _ (T64_64 i) (hfix64_64 i) _)
      ⟨64, by decide⟩ ⟨64, by decide⟩ _
      (Q2.validAt ⟨64, by decide⟩ (Q2.listedAt ⟨64, by decide⟩
        (alnCheck_rep ⟨64, by decide⟩ hj hq).1))
      (colE2 ⟨64, by decide⟩ 60 hp) Q2.T64_64_2 Q2.hfix64_64_2 Q2.hinj64_64_2
      Q2.hcardT64_64_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T64_64_2 i) (Q2.hfix64_64_2 i) _)
      ?_).symm
  rw [show colData1 (⟨64, by decide⟩ : Fin 148)
        ((colE1 ⟨64, by decide⟩ 60 (transLenTr ⟨64, by decide⟩ 60 hp) : ↥(reps ⟨64, by decide⟩)) : Coordinate 1)
        T64_64 = colFn colCert_64_64_60.D (m := 5) from colCert_64_64_60.bind1,
    show colData2 (⟨64, by decide⟩ : Fin 148)
        ((colE2 ⟨64, by decide⟩ 60 hp : ↥(Q2.reps ⟨64, by decide⟩)) : Coordinate 2)
        Q2.T64_64_2 = colFn colCert_64_64_60.D (m := 5) from colCert_64_64_60.bind2]
  exact alnAll_64_64_60 j hj hq

theorem leaf_64_64_65 (hp : 65 < (Q2.transData.getD 64 []).length)
    (j : Nat) (hj : j < (repChars.getD 64 []).length)
    (hq : (normIsRep.getD 64 []).getD j false = true) :
    species (Q2.reps (⟨64, by decide⟩ : Fin 148)) (colE2 ⟨64, by decide⟩ 65 hp)
        (rowE2 (⟨64, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨64, by decide⟩ : Fin 148))
        (colE1 ⟨64, by decide⟩ 65 (transLenTr ⟨64, by decide⟩ 65 hp))
        (rowE1 (⟨64, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨64, by decide⟩ : Fin 148) ⟨64, by decide⟩ _
      (validAt ⟨64, by decide⟩ (listedAt ⟨64, by decide⟩ hj))
      (colE1 ⟨64, by decide⟩ 65 (transLenTr ⟨64, by decide⟩ 65 hp)) T64_64
      hfix64_64 hinj64_64 hcardT64_64
      (fun i => conj_mem_of_fixedPoints _ _ (T64_64 i) (hfix64_64 i) _)
      ⟨64, by decide⟩ ⟨64, by decide⟩ _
      (Q2.validAt ⟨64, by decide⟩ (Q2.listedAt ⟨64, by decide⟩
        (alnCheck_rep ⟨64, by decide⟩ hj hq).1))
      (colE2 ⟨64, by decide⟩ 65 hp) Q2.T64_64_2 Q2.hfix64_64_2 Q2.hinj64_64_2
      Q2.hcardT64_64_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T64_64_2 i) (Q2.hfix64_64_2 i) _)
      ?_).symm
  rw [show colData1 (⟨64, by decide⟩ : Fin 148)
        ((colE1 ⟨64, by decide⟩ 65 (transLenTr ⟨64, by decide⟩ 65 hp) : ↥(reps ⟨64, by decide⟩)) : Coordinate 1)
        T64_64 = colFn colCert_64_64_65.D (m := 5) from colCert_64_64_65.bind1,
    show colData2 (⟨64, by decide⟩ : Fin 148)
        ((colE2 ⟨64, by decide⟩ 65 hp : ↥(Q2.reps ⟨64, by decide⟩)) : Coordinate 2)
        Q2.T64_64_2 = colFn colCert_64_64_65.D (m := 5) from colCert_64_64_65.bind2]
  exact alnAll_64_64_65 j hj hq

theorem leaf_64_64_70 (hp : 70 < (Q2.transData.getD 64 []).length)
    (j : Nat) (hj : j < (repChars.getD 64 []).length)
    (hq : (normIsRep.getD 64 []).getD j false = true) :
    species (Q2.reps (⟨64, by decide⟩ : Fin 148)) (colE2 ⟨64, by decide⟩ 70 hp)
        (rowE2 (⟨64, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨64, by decide⟩ : Fin 148))
        (colE1 ⟨64, by decide⟩ 70 (transLenTr ⟨64, by decide⟩ 70 hp))
        (rowE1 (⟨64, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨64, by decide⟩ : Fin 148) ⟨64, by decide⟩ _
      (validAt ⟨64, by decide⟩ (listedAt ⟨64, by decide⟩ hj))
      (colE1 ⟨64, by decide⟩ 70 (transLenTr ⟨64, by decide⟩ 70 hp)) T64_64
      hfix64_64 hinj64_64 hcardT64_64
      (fun i => conj_mem_of_fixedPoints _ _ (T64_64 i) (hfix64_64 i) _)
      ⟨64, by decide⟩ ⟨64, by decide⟩ _
      (Q2.validAt ⟨64, by decide⟩ (Q2.listedAt ⟨64, by decide⟩
        (alnCheck_rep ⟨64, by decide⟩ hj hq).1))
      (colE2 ⟨64, by decide⟩ 70 hp) Q2.T64_64_2 Q2.hfix64_64_2 Q2.hinj64_64_2
      Q2.hcardT64_64_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T64_64_2 i) (Q2.hfix64_64_2 i) _)
      ?_).symm
  rw [show colData1 (⟨64, by decide⟩ : Fin 148)
        ((colE1 ⟨64, by decide⟩ 70 (transLenTr ⟨64, by decide⟩ 70 hp) : ↥(reps ⟨64, by decide⟩)) : Coordinate 1)
        T64_64 = colFn colCert_64_64_70.D (m := 5) from colCert_64_64_70.bind1,
    show colData2 (⟨64, by decide⟩ : Fin 148)
        ((colE2 ⟨64, by decide⟩ 70 hp : ↥(Q2.reps ⟨64, by decide⟩)) : Coordinate 2)
        Q2.T64_64_2 = colFn colCert_64_64_70.D (m := 5) from colCert_64_64_70.bind2]
  exact alnAll_64_64_70 j hj hq

theorem leaf_64_64_75 (hp : 75 < (Q2.transData.getD 64 []).length)
    (j : Nat) (hj : j < (repChars.getD 64 []).length)
    (hq : (normIsRep.getD 64 []).getD j false = true) :
    species (Q2.reps (⟨64, by decide⟩ : Fin 148)) (colE2 ⟨64, by decide⟩ 75 hp)
        (rowE2 (⟨64, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨64, by decide⟩ : Fin 148))
        (colE1 ⟨64, by decide⟩ 75 (transLenTr ⟨64, by decide⟩ 75 hp))
        (rowE1 (⟨64, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨64, by decide⟩ : Fin 148) ⟨64, by decide⟩ _
      (validAt ⟨64, by decide⟩ (listedAt ⟨64, by decide⟩ hj))
      (colE1 ⟨64, by decide⟩ 75 (transLenTr ⟨64, by decide⟩ 75 hp)) T64_64
      hfix64_64 hinj64_64 hcardT64_64
      (fun i => conj_mem_of_fixedPoints _ _ (T64_64 i) (hfix64_64 i) _)
      ⟨64, by decide⟩ ⟨64, by decide⟩ _
      (Q2.validAt ⟨64, by decide⟩ (Q2.listedAt ⟨64, by decide⟩
        (alnCheck_rep ⟨64, by decide⟩ hj hq).1))
      (colE2 ⟨64, by decide⟩ 75 hp) Q2.T64_64_2 Q2.hfix64_64_2 Q2.hinj64_64_2
      Q2.hcardT64_64_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T64_64_2 i) (Q2.hfix64_64_2 i) _)
      ?_).symm
  rw [show colData1 (⟨64, by decide⟩ : Fin 148)
        ((colE1 ⟨64, by decide⟩ 75 (transLenTr ⟨64, by decide⟩ 75 hp) : ↥(reps ⟨64, by decide⟩)) : Coordinate 1)
        T64_64 = colFn colCert_64_64_75.D (m := 5) from colCert_64_64_75.bind1,
    show colData2 (⟨64, by decide⟩ : Fin 148)
        ((colE2 ⟨64, by decide⟩ 75 hp : ↥(Q2.reps ⟨64, by decide⟩)) : Coordinate 2)
        Q2.T64_64_2 = colFn colCert_64_64_75.D (m := 5) from colCert_64_64_75.bind2]
  exact alnAll_64_64_75 j hj hq

theorem leaf_64_64_80 (hp : 80 < (Q2.transData.getD 64 []).length)
    (j : Nat) (hj : j < (repChars.getD 64 []).length)
    (hq : (normIsRep.getD 64 []).getD j false = true) :
    species (Q2.reps (⟨64, by decide⟩ : Fin 148)) (colE2 ⟨64, by decide⟩ 80 hp)
        (rowE2 (⟨64, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨64, by decide⟩ : Fin 148))
        (colE1 ⟨64, by decide⟩ 80 (transLenTr ⟨64, by decide⟩ 80 hp))
        (rowE1 (⟨64, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨64, by decide⟩ : Fin 148) ⟨64, by decide⟩ _
      (validAt ⟨64, by decide⟩ (listedAt ⟨64, by decide⟩ hj))
      (colE1 ⟨64, by decide⟩ 80 (transLenTr ⟨64, by decide⟩ 80 hp)) T64_64
      hfix64_64 hinj64_64 hcardT64_64
      (fun i => conj_mem_of_fixedPoints _ _ (T64_64 i) (hfix64_64 i) _)
      ⟨64, by decide⟩ ⟨64, by decide⟩ _
      (Q2.validAt ⟨64, by decide⟩ (Q2.listedAt ⟨64, by decide⟩
        (alnCheck_rep ⟨64, by decide⟩ hj hq).1))
      (colE2 ⟨64, by decide⟩ 80 hp) Q2.T64_64_2 Q2.hfix64_64_2 Q2.hinj64_64_2
      Q2.hcardT64_64_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T64_64_2 i) (Q2.hfix64_64_2 i) _)
      ?_).symm
  rw [show colData1 (⟨64, by decide⟩ : Fin 148)
        ((colE1 ⟨64, by decide⟩ 80 (transLenTr ⟨64, by decide⟩ 80 hp) : ↥(reps ⟨64, by decide⟩)) : Coordinate 1)
        T64_64 = colFn colCert_64_64_80.D (m := 5) from colCert_64_64_80.bind1,
    show colData2 (⟨64, by decide⟩ : Fin 148)
        ((colE2 ⟨64, by decide⟩ 80 hp : ↥(Q2.reps ⟨64, by decide⟩)) : Coordinate 2)
        Q2.T64_64_2 = colFn colCert_64_64_80.D (m := 5) from colCert_64_64_80.bind2]
  exact alnAll_64_64_80 j hj hq

theorem leaf_64_64_85 (hp : 85 < (Q2.transData.getD 64 []).length)
    (j : Nat) (hj : j < (repChars.getD 64 []).length)
    (hq : (normIsRep.getD 64 []).getD j false = true) :
    species (Q2.reps (⟨64, by decide⟩ : Fin 148)) (colE2 ⟨64, by decide⟩ 85 hp)
        (rowE2 (⟨64, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨64, by decide⟩ : Fin 148))
        (colE1 ⟨64, by decide⟩ 85 (transLenTr ⟨64, by decide⟩ 85 hp))
        (rowE1 (⟨64, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨64, by decide⟩ : Fin 148) ⟨64, by decide⟩ _
      (validAt ⟨64, by decide⟩ (listedAt ⟨64, by decide⟩ hj))
      (colE1 ⟨64, by decide⟩ 85 (transLenTr ⟨64, by decide⟩ 85 hp)) T64_64
      hfix64_64 hinj64_64 hcardT64_64
      (fun i => conj_mem_of_fixedPoints _ _ (T64_64 i) (hfix64_64 i) _)
      ⟨64, by decide⟩ ⟨64, by decide⟩ _
      (Q2.validAt ⟨64, by decide⟩ (Q2.listedAt ⟨64, by decide⟩
        (alnCheck_rep ⟨64, by decide⟩ hj hq).1))
      (colE2 ⟨64, by decide⟩ 85 hp) Q2.T64_64_2 Q2.hfix64_64_2 Q2.hinj64_64_2
      Q2.hcardT64_64_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T64_64_2 i) (Q2.hfix64_64_2 i) _)
      ?_).symm
  rw [show colData1 (⟨64, by decide⟩ : Fin 148)
        ((colE1 ⟨64, by decide⟩ 85 (transLenTr ⟨64, by decide⟩ 85 hp) : ↥(reps ⟨64, by decide⟩)) : Coordinate 1)
        T64_64 = colFn colCert_64_64_85.D (m := 5) from colCert_64_64_85.bind1,
    show colData2 (⟨64, by decide⟩ : Fin 148)
        ((colE2 ⟨64, by decide⟩ 85 hp : ↥(Q2.reps ⟨64, by decide⟩)) : Coordinate 2)
        Q2.T64_64_2 = colFn colCert_64_64_85.D (m := 5) from colCert_64_64_85.bind2]
  exact alnAll_64_64_85 j hj hq

theorem leaf_64_64_90 (hp : 90 < (Q2.transData.getD 64 []).length)
    (j : Nat) (hj : j < (repChars.getD 64 []).length)
    (hq : (normIsRep.getD 64 []).getD j false = true) :
    species (Q2.reps (⟨64, by decide⟩ : Fin 148)) (colE2 ⟨64, by decide⟩ 90 hp)
        (rowE2 (⟨64, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨64, by decide⟩ : Fin 148))
        (colE1 ⟨64, by decide⟩ 90 (transLenTr ⟨64, by decide⟩ 90 hp))
        (rowE1 (⟨64, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨64, by decide⟩ : Fin 148) ⟨64, by decide⟩ _
      (validAt ⟨64, by decide⟩ (listedAt ⟨64, by decide⟩ hj))
      (colE1 ⟨64, by decide⟩ 90 (transLenTr ⟨64, by decide⟩ 90 hp)) T64_64
      hfix64_64 hinj64_64 hcardT64_64
      (fun i => conj_mem_of_fixedPoints _ _ (T64_64 i) (hfix64_64 i) _)
      ⟨64, by decide⟩ ⟨64, by decide⟩ _
      (Q2.validAt ⟨64, by decide⟩ (Q2.listedAt ⟨64, by decide⟩
        (alnCheck_rep ⟨64, by decide⟩ hj hq).1))
      (colE2 ⟨64, by decide⟩ 90 hp) Q2.T64_64_2 Q2.hfix64_64_2 Q2.hinj64_64_2
      Q2.hcardT64_64_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T64_64_2 i) (Q2.hfix64_64_2 i) _)
      ?_).symm
  rw [show colData1 (⟨64, by decide⟩ : Fin 148)
        ((colE1 ⟨64, by decide⟩ 90 (transLenTr ⟨64, by decide⟩ 90 hp) : ↥(reps ⟨64, by decide⟩)) : Coordinate 1)
        T64_64 = colFn colCert_64_64_90.D (m := 5) from colCert_64_64_90.bind1,
    show colData2 (⟨64, by decide⟩ : Fin 148)
        ((colE2 ⟨64, by decide⟩ 90 hp : ↥(Q2.reps ⟨64, by decide⟩)) : Coordinate 2)
        Q2.T64_64_2 = colFn colCert_64_64_90.D (m := 5) from colCert_64_64_90.bind2]
  exact alnAll_64_64_90 j hj hq

theorem leaf_64_64_95 (hp : 95 < (Q2.transData.getD 64 []).length)
    (j : Nat) (hj : j < (repChars.getD 64 []).length)
    (hq : (normIsRep.getD 64 []).getD j false = true) :
    species (Q2.reps (⟨64, by decide⟩ : Fin 148)) (colE2 ⟨64, by decide⟩ 95 hp)
        (rowE2 (⟨64, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨64, by decide⟩ : Fin 148))
        (colE1 ⟨64, by decide⟩ 95 (transLenTr ⟨64, by decide⟩ 95 hp))
        (rowE1 (⟨64, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨64, by decide⟩ : Fin 148) ⟨64, by decide⟩ _
      (validAt ⟨64, by decide⟩ (listedAt ⟨64, by decide⟩ hj))
      (colE1 ⟨64, by decide⟩ 95 (transLenTr ⟨64, by decide⟩ 95 hp)) T64_64
      hfix64_64 hinj64_64 hcardT64_64
      (fun i => conj_mem_of_fixedPoints _ _ (T64_64 i) (hfix64_64 i) _)
      ⟨64, by decide⟩ ⟨64, by decide⟩ _
      (Q2.validAt ⟨64, by decide⟩ (Q2.listedAt ⟨64, by decide⟩
        (alnCheck_rep ⟨64, by decide⟩ hj hq).1))
      (colE2 ⟨64, by decide⟩ 95 hp) Q2.T64_64_2 Q2.hfix64_64_2 Q2.hinj64_64_2
      Q2.hcardT64_64_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T64_64_2 i) (Q2.hfix64_64_2 i) _)
      ?_).symm
  rw [show colData1 (⟨64, by decide⟩ : Fin 148)
        ((colE1 ⟨64, by decide⟩ 95 (transLenTr ⟨64, by decide⟩ 95 hp) : ↥(reps ⟨64, by decide⟩)) : Coordinate 1)
        T64_64 = colFn colCert_64_64_95.D (m := 5) from colCert_64_64_95.bind1,
    show colData2 (⟨64, by decide⟩ : Fin 148)
        ((colE2 ⟨64, by decide⟩ 95 hp : ↥(Q2.reps ⟨64, by decide⟩)) : Coordinate 2)
        Q2.T64_64_2 = colFn colCert_64_64_95.D (m := 5) from colCert_64_64_95.bind2]
  exact alnAll_64_64_95 j hj hq

theorem leaf_64_64_100 (hp : 100 < (Q2.transData.getD 64 []).length)
    (j : Nat) (hj : j < (repChars.getD 64 []).length)
    (hq : (normIsRep.getD 64 []).getD j false = true) :
    species (Q2.reps (⟨64, by decide⟩ : Fin 148)) (colE2 ⟨64, by decide⟩ 100 hp)
        (rowE2 (⟨64, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨64, by decide⟩ : Fin 148))
        (colE1 ⟨64, by decide⟩ 100 (transLenTr ⟨64, by decide⟩ 100 hp))
        (rowE1 (⟨64, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨64, by decide⟩ : Fin 148) ⟨64, by decide⟩ _
      (validAt ⟨64, by decide⟩ (listedAt ⟨64, by decide⟩ hj))
      (colE1 ⟨64, by decide⟩ 100 (transLenTr ⟨64, by decide⟩ 100 hp)) T64_64
      hfix64_64 hinj64_64 hcardT64_64
      (fun i => conj_mem_of_fixedPoints _ _ (T64_64 i) (hfix64_64 i) _)
      ⟨64, by decide⟩ ⟨64, by decide⟩ _
      (Q2.validAt ⟨64, by decide⟩ (Q2.listedAt ⟨64, by decide⟩
        (alnCheck_rep ⟨64, by decide⟩ hj hq).1))
      (colE2 ⟨64, by decide⟩ 100 hp) Q2.T64_64_2 Q2.hfix64_64_2 Q2.hinj64_64_2
      Q2.hcardT64_64_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T64_64_2 i) (Q2.hfix64_64_2 i) _)
      ?_).symm
  rw [show colData1 (⟨64, by decide⟩ : Fin 148)
        ((colE1 ⟨64, by decide⟩ 100 (transLenTr ⟨64, by decide⟩ 100 hp) : ↥(reps ⟨64, by decide⟩)) : Coordinate 1)
        T64_64 = colFn colCert_64_64_100.D (m := 5) from colCert_64_64_100.bind1,
    show colData2 (⟨64, by decide⟩ : Fin 148)
        ((colE2 ⟨64, by decide⟩ 100 hp : ↥(Q2.reps ⟨64, by decide⟩)) : Coordinate 2)
        Q2.T64_64_2 = colFn colCert_64_64_100.D (m := 5) from colCert_64_64_100.bind2]
  exact alnAll_64_64_100 j hj hq

theorem leaf_64_64_105 (hp : 105 < (Q2.transData.getD 64 []).length)
    (j : Nat) (hj : j < (repChars.getD 64 []).length)
    (hq : (normIsRep.getD 64 []).getD j false = true) :
    species (Q2.reps (⟨64, by decide⟩ : Fin 148)) (colE2 ⟨64, by decide⟩ 105 hp)
        (rowE2 (⟨64, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨64, by decide⟩ : Fin 148))
        (colE1 ⟨64, by decide⟩ 105 (transLenTr ⟨64, by decide⟩ 105 hp))
        (rowE1 (⟨64, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨64, by decide⟩ : Fin 148) ⟨64, by decide⟩ _
      (validAt ⟨64, by decide⟩ (listedAt ⟨64, by decide⟩ hj))
      (colE1 ⟨64, by decide⟩ 105 (transLenTr ⟨64, by decide⟩ 105 hp)) T64_64
      hfix64_64 hinj64_64 hcardT64_64
      (fun i => conj_mem_of_fixedPoints _ _ (T64_64 i) (hfix64_64 i) _)
      ⟨64, by decide⟩ ⟨64, by decide⟩ _
      (Q2.validAt ⟨64, by decide⟩ (Q2.listedAt ⟨64, by decide⟩
        (alnCheck_rep ⟨64, by decide⟩ hj hq).1))
      (colE2 ⟨64, by decide⟩ 105 hp) Q2.T64_64_2 Q2.hfix64_64_2 Q2.hinj64_64_2
      Q2.hcardT64_64_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T64_64_2 i) (Q2.hfix64_64_2 i) _)
      ?_).symm
  rw [show colData1 (⟨64, by decide⟩ : Fin 148)
        ((colE1 ⟨64, by decide⟩ 105 (transLenTr ⟨64, by decide⟩ 105 hp) : ↥(reps ⟨64, by decide⟩)) : Coordinate 1)
        T64_64 = colFn colCert_64_64_105.D (m := 5) from colCert_64_64_105.bind1,
    show colData2 (⟨64, by decide⟩ : Fin 148)
        ((colE2 ⟨64, by decide⟩ 105 hp : ↥(Q2.reps ⟨64, by decide⟩)) : Coordinate 2)
        Q2.T64_64_2 = colFn colCert_64_64_105.D (m := 5) from colCert_64_64_105.bind2]
  exact alnAll_64_64_105 j hj hq

theorem leaf_64_64_110 (hp : 110 < (Q2.transData.getD 64 []).length)
    (j : Nat) (hj : j < (repChars.getD 64 []).length)
    (hq : (normIsRep.getD 64 []).getD j false = true) :
    species (Q2.reps (⟨64, by decide⟩ : Fin 148)) (colE2 ⟨64, by decide⟩ 110 hp)
        (rowE2 (⟨64, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨64, by decide⟩ : Fin 148))
        (colE1 ⟨64, by decide⟩ 110 (transLenTr ⟨64, by decide⟩ 110 hp))
        (rowE1 (⟨64, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨64, by decide⟩ : Fin 148) ⟨64, by decide⟩ _
      (validAt ⟨64, by decide⟩ (listedAt ⟨64, by decide⟩ hj))
      (colE1 ⟨64, by decide⟩ 110 (transLenTr ⟨64, by decide⟩ 110 hp)) T64_64
      hfix64_64 hinj64_64 hcardT64_64
      (fun i => conj_mem_of_fixedPoints _ _ (T64_64 i) (hfix64_64 i) _)
      ⟨64, by decide⟩ ⟨64, by decide⟩ _
      (Q2.validAt ⟨64, by decide⟩ (Q2.listedAt ⟨64, by decide⟩
        (alnCheck_rep ⟨64, by decide⟩ hj hq).1))
      (colE2 ⟨64, by decide⟩ 110 hp) Q2.T64_64_2 Q2.hfix64_64_2 Q2.hinj64_64_2
      Q2.hcardT64_64_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T64_64_2 i) (Q2.hfix64_64_2 i) _)
      ?_).symm
  rw [show colData1 (⟨64, by decide⟩ : Fin 148)
        ((colE1 ⟨64, by decide⟩ 110 (transLenTr ⟨64, by decide⟩ 110 hp) : ↥(reps ⟨64, by decide⟩)) : Coordinate 1)
        T64_64 = colFn colCert_64_64_110.D (m := 5) from colCert_64_64_110.bind1,
    show colData2 (⟨64, by decide⟩ : Fin 148)
        ((colE2 ⟨64, by decide⟩ 110 hp : ↥(Q2.reps ⟨64, by decide⟩)) : Coordinate 2)
        Q2.T64_64_2 = colFn colCert_64_64_110.D (m := 5) from colCert_64_64_110.bind2]
  exact alnAll_64_64_110 j hj hq

theorem leaf_64_64_115 (hp : 115 < (Q2.transData.getD 64 []).length)
    (j : Nat) (hj : j < (repChars.getD 64 []).length)
    (hq : (normIsRep.getD 64 []).getD j false = true) :
    species (Q2.reps (⟨64, by decide⟩ : Fin 148)) (colE2 ⟨64, by decide⟩ 115 hp)
        (rowE2 (⟨64, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨64, by decide⟩ : Fin 148))
        (colE1 ⟨64, by decide⟩ 115 (transLenTr ⟨64, by decide⟩ 115 hp))
        (rowE1 (⟨64, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨64, by decide⟩ : Fin 148) ⟨64, by decide⟩ _
      (validAt ⟨64, by decide⟩ (listedAt ⟨64, by decide⟩ hj))
      (colE1 ⟨64, by decide⟩ 115 (transLenTr ⟨64, by decide⟩ 115 hp)) T64_64
      hfix64_64 hinj64_64 hcardT64_64
      (fun i => conj_mem_of_fixedPoints _ _ (T64_64 i) (hfix64_64 i) _)
      ⟨64, by decide⟩ ⟨64, by decide⟩ _
      (Q2.validAt ⟨64, by decide⟩ (Q2.listedAt ⟨64, by decide⟩
        (alnCheck_rep ⟨64, by decide⟩ hj hq).1))
      (colE2 ⟨64, by decide⟩ 115 hp) Q2.T64_64_2 Q2.hfix64_64_2 Q2.hinj64_64_2
      Q2.hcardT64_64_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T64_64_2 i) (Q2.hfix64_64_2 i) _)
      ?_).symm
  rw [show colData1 (⟨64, by decide⟩ : Fin 148)
        ((colE1 ⟨64, by decide⟩ 115 (transLenTr ⟨64, by decide⟩ 115 hp) : ↥(reps ⟨64, by decide⟩)) : Coordinate 1)
        T64_64 = colFn colCert_64_64_115.D (m := 5) from colCert_64_64_115.bind1,
    show colData2 (⟨64, by decide⟩ : Fin 148)
        ((colE2 ⟨64, by decide⟩ 115 hp : ↥(Q2.reps ⟨64, by decide⟩)) : Coordinate 2)
        Q2.T64_64_2 = colFn colCert_64_64_115.D (m := 5) from colCert_64_64_115.bind2]
  exact alnAll_64_64_115 j hj hq

theorem leaf_64_64_120 (hp : 120 < (Q2.transData.getD 64 []).length)
    (j : Nat) (hj : j < (repChars.getD 64 []).length)
    (hq : (normIsRep.getD 64 []).getD j false = true) :
    species (Q2.reps (⟨64, by decide⟩ : Fin 148)) (colE2 ⟨64, by decide⟩ 120 hp)
        (rowE2 (⟨64, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨64, by decide⟩ : Fin 148))
        (colE1 ⟨64, by decide⟩ 120 (transLenTr ⟨64, by decide⟩ 120 hp))
        (rowE1 (⟨64, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨64, by decide⟩ : Fin 148) ⟨64, by decide⟩ _
      (validAt ⟨64, by decide⟩ (listedAt ⟨64, by decide⟩ hj))
      (colE1 ⟨64, by decide⟩ 120 (transLenTr ⟨64, by decide⟩ 120 hp)) T64_64
      hfix64_64 hinj64_64 hcardT64_64
      (fun i => conj_mem_of_fixedPoints _ _ (T64_64 i) (hfix64_64 i) _)
      ⟨64, by decide⟩ ⟨64, by decide⟩ _
      (Q2.validAt ⟨64, by decide⟩ (Q2.listedAt ⟨64, by decide⟩
        (alnCheck_rep ⟨64, by decide⟩ hj hq).1))
      (colE2 ⟨64, by decide⟩ 120 hp) Q2.T64_64_2 Q2.hfix64_64_2 Q2.hinj64_64_2
      Q2.hcardT64_64_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T64_64_2 i) (Q2.hfix64_64_2 i) _)
      ?_).symm
  rw [show colData1 (⟨64, by decide⟩ : Fin 148)
        ((colE1 ⟨64, by decide⟩ 120 (transLenTr ⟨64, by decide⟩ 120 hp) : ↥(reps ⟨64, by decide⟩)) : Coordinate 1)
        T64_64 = colFn colCert_64_64_120.D (m := 5) from colCert_64_64_120.bind1,
    show colData2 (⟨64, by decide⟩ : Fin 148)
        ((colE2 ⟨64, by decide⟩ 120 hp : ↥(Q2.reps ⟨64, by decide⟩)) : Coordinate 2)
        Q2.T64_64_2 = colFn colCert_64_64_120.D (m := 5) from colCert_64_64_120.bind2]
  exact alnAll_64_64_120 j hj hq

theorem leaf_65_9_0 (hp : 0 < (Q2.transData.getD 9 []).length)
    (j : Nat) (hj : j < (repChars.getD 65 []).length)
    (hq : (normIsRep.getD 65 []).getD j false = true) :
    species (Q2.reps (⟨9, by decide⟩ : Fin 148)) (colE2 ⟨9, by decide⟩ 0 hp)
        (rowE2 (⟨65, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨9, by decide⟩ : Fin 148))
        (colE1 ⟨9, by decide⟩ 0 (transLenTr ⟨9, by decide⟩ 0 hp))
        (rowE1 (⟨65, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨65, by decide⟩ : Fin 148) ⟨9, by decide⟩ _
      (validAt ⟨65, by decide⟩ (listedAt ⟨65, by decide⟩ hj))
      (colE1 ⟨9, by decide⟩ 0 (transLenTr ⟨9, by decide⟩ 0 hp)) T65_9
      hfix65_9 hinj65_9 hcardT65_9
      (fun i => conj_mem_of_fixedPoints _ _ (T65_9 i) (hfix65_9 i) _)
      ⟨65, by decide⟩ ⟨9, by decide⟩ _
      (Q2.validAt ⟨65, by decide⟩ (Q2.listedAt ⟨65, by decide⟩
        (alnCheck_rep ⟨65, by decide⟩ hj hq).1))
      (colE2 ⟨9, by decide⟩ 0 hp) Q2.T65_9_2 Q2.hfix65_9_2 Q2.hinj65_9_2
      Q2.hcardT65_9_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T65_9_2 i) (Q2.hfix65_9_2 i) _)
      colCert_65_9_0.hD ?_).symm
  rw [alnId_65 j hj]


theorem leaf_65_9_1 (hp : 1 < (Q2.transData.getD 9 []).length)
    (j : Nat) (hj : j < (repChars.getD 65 []).length)
    (hq : (normIsRep.getD 65 []).getD j false = true) :
    species (Q2.reps (⟨9, by decide⟩ : Fin 148)) (colE2 ⟨9, by decide⟩ 1 hp)
        (rowE2 (⟨65, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨9, by decide⟩ : Fin 148))
        (colE1 ⟨9, by decide⟩ 1 (transLenTr ⟨9, by decide⟩ 1 hp))
        (rowE1 (⟨65, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨65, by decide⟩ : Fin 148) ⟨9, by decide⟩ _
      (validAt ⟨65, by decide⟩ (listedAt ⟨65, by decide⟩ hj))
      (colE1 ⟨9, by decide⟩ 1 (transLenTr ⟨9, by decide⟩ 1 hp)) T65_9
      hfix65_9 hinj65_9 hcardT65_9
      (fun i => conj_mem_of_fixedPoints _ _ (T65_9 i) (hfix65_9 i) _)
      ⟨65, by decide⟩ ⟨9, by decide⟩ _
      (Q2.validAt ⟨65, by decide⟩ (Q2.listedAt ⟨65, by decide⟩
        (alnCheck_rep ⟨65, by decide⟩ hj hq).1))
      (colE2 ⟨9, by decide⟩ 1 hp) Q2.T65_9_2 Q2.hfix65_9_2 Q2.hinj65_9_2
      Q2.hcardT65_9_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T65_9_2 i) (Q2.hfix65_9_2 i) _)
      colCert_65_9_1.hD ?_).symm
  rw [alnId_65 j hj]


theorem leaf_65_9_2 (hp : 2 < (Q2.transData.getD 9 []).length)
    (j : Nat) (hj : j < (repChars.getD 65 []).length)
    (hq : (normIsRep.getD 65 []).getD j false = true) :
    species (Q2.reps (⟨9, by decide⟩ : Fin 148)) (colE2 ⟨9, by decide⟩ 2 hp)
        (rowE2 (⟨65, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨9, by decide⟩ : Fin 148))
        (colE1 ⟨9, by decide⟩ 2 (transLenTr ⟨9, by decide⟩ 2 hp))
        (rowE1 (⟨65, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨65, by decide⟩ : Fin 148) ⟨9, by decide⟩ _
      (validAt ⟨65, by decide⟩ (listedAt ⟨65, by decide⟩ hj))
      (colE1 ⟨9, by decide⟩ 2 (transLenTr ⟨9, by decide⟩ 2 hp)) T65_9
      hfix65_9 hinj65_9 hcardT65_9
      (fun i => conj_mem_of_fixedPoints _ _ (T65_9 i) (hfix65_9 i) _)
      ⟨65, by decide⟩ ⟨9, by decide⟩ _
      (Q2.validAt ⟨65, by decide⟩ (Q2.listedAt ⟨65, by decide⟩
        (alnCheck_rep ⟨65, by decide⟩ hj hq).1))
      (colE2 ⟨9, by decide⟩ 2 hp) Q2.T65_9_2 Q2.hfix65_9_2 Q2.hinj65_9_2
      Q2.hcardT65_9_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T65_9_2 i) (Q2.hfix65_9_2 i) _)
      colCert_65_9_2.hD ?_).symm
  rw [alnId_65 j hj]


theorem leaf_65_9_3 (hp : 3 < (Q2.transData.getD 9 []).length)
    (j : Nat) (hj : j < (repChars.getD 65 []).length)
    (hq : (normIsRep.getD 65 []).getD j false = true) :
    species (Q2.reps (⟨9, by decide⟩ : Fin 148)) (colE2 ⟨9, by decide⟩ 3 hp)
        (rowE2 (⟨65, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨9, by decide⟩ : Fin 148))
        (colE1 ⟨9, by decide⟩ 3 (transLenTr ⟨9, by decide⟩ 3 hp))
        (rowE1 (⟨65, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨65, by decide⟩ : Fin 148) ⟨9, by decide⟩ _
      (validAt ⟨65, by decide⟩ (listedAt ⟨65, by decide⟩ hj))
      (colE1 ⟨9, by decide⟩ 3 (transLenTr ⟨9, by decide⟩ 3 hp)) T65_9
      hfix65_9 hinj65_9 hcardT65_9
      (fun i => conj_mem_of_fixedPoints _ _ (T65_9 i) (hfix65_9 i) _)
      ⟨65, by decide⟩ ⟨9, by decide⟩ _
      (Q2.validAt ⟨65, by decide⟩ (Q2.listedAt ⟨65, by decide⟩
        (alnCheck_rep ⟨65, by decide⟩ hj hq).1))
      (colE2 ⟨9, by decide⟩ 3 hp) Q2.T65_9_2 Q2.hfix65_9_2 Q2.hinj65_9_2
      Q2.hcardT65_9_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T65_9_2 i) (Q2.hfix65_9_2 i) _)
      colCert_65_9_3.hD ?_).symm
  rw [alnId_65 j hj]


theorem leaf_65_9_4 (hp : 4 < (Q2.transData.getD 9 []).length)
    (j : Nat) (hj : j < (repChars.getD 65 []).length)
    (hq : (normIsRep.getD 65 []).getD j false = true) :
    species (Q2.reps (⟨9, by decide⟩ : Fin 148)) (colE2 ⟨9, by decide⟩ 4 hp)
        (rowE2 (⟨65, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨9, by decide⟩ : Fin 148))
        (colE1 ⟨9, by decide⟩ 4 (transLenTr ⟨9, by decide⟩ 4 hp))
        (rowE1 (⟨65, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨65, by decide⟩ : Fin 148) ⟨9, by decide⟩ _
      (validAt ⟨65, by decide⟩ (listedAt ⟨65, by decide⟩ hj))
      (colE1 ⟨9, by decide⟩ 4 (transLenTr ⟨9, by decide⟩ 4 hp)) T65_9
      hfix65_9 hinj65_9 hcardT65_9
      (fun i => conj_mem_of_fixedPoints _ _ (T65_9 i) (hfix65_9 i) _)
      ⟨65, by decide⟩ ⟨9, by decide⟩ _
      (Q2.validAt ⟨65, by decide⟩ (Q2.listedAt ⟨65, by decide⟩
        (alnCheck_rep ⟨65, by decide⟩ hj hq).1))
      (colE2 ⟨9, by decide⟩ 4 hp) Q2.T65_9_2 Q2.hfix65_9_2 Q2.hinj65_9_2
      Q2.hcardT65_9_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T65_9_2 i) (Q2.hfix65_9_2 i) _)
      colCert_65_9_4.hD ?_).symm
  rw [alnId_65 j hj]


theorem leaf_65_12_0 (hp : 0 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 65 []).length)
    (hq : (normIsRep.getD 65 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 0 hp)
        (rowE2 (⟨65, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp))
        (rowE1 (⟨65, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨65, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨65, by decide⟩ (listedAt ⟨65, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp)) T65_12
      hfix65_12 hinj65_12 hcardT65_12
      (fun i => conj_mem_of_fixedPoints _ _ (T65_12 i) (hfix65_12 i) _)
      ⟨65, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨65, by decide⟩ (Q2.listedAt ⟨65, by decide⟩
        (alnCheck_rep ⟨65, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 0 hp) Q2.T65_12_2 Q2.hfix65_12_2 Q2.hinj65_12_2
      Q2.hcardT65_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T65_12_2 i) (Q2.hfix65_12_2 i) _)
      colCert_65_12_0.hD ?_).symm
  rw [alnId_65 j hj]


theorem leaf_65_12_1 (hp : 1 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 65 []).length)
    (hq : (normIsRep.getD 65 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 1 hp)
        (rowE2 (⟨65, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp))
        (rowE1 (⟨65, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨65, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨65, by decide⟩ (listedAt ⟨65, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp)) T65_12
      hfix65_12 hinj65_12 hcardT65_12
      (fun i => conj_mem_of_fixedPoints _ _ (T65_12 i) (hfix65_12 i) _)
      ⟨65, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨65, by decide⟩ (Q2.listedAt ⟨65, by decide⟩
        (alnCheck_rep ⟨65, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 1 hp) Q2.T65_12_2 Q2.hfix65_12_2 Q2.hinj65_12_2
      Q2.hcardT65_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T65_12_2 i) (Q2.hfix65_12_2 i) _)
      colCert_65_12_1.hD ?_).symm
  rw [alnId_65 j hj]


theorem leaf_65_12_2 (hp : 2 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 65 []).length)
    (hq : (normIsRep.getD 65 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 2 hp)
        (rowE2 (⟨65, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp))
        (rowE1 (⟨65, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨65, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨65, by decide⟩ (listedAt ⟨65, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp)) T65_12
      hfix65_12 hinj65_12 hcardT65_12
      (fun i => conj_mem_of_fixedPoints _ _ (T65_12 i) (hfix65_12 i) _)
      ⟨65, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨65, by decide⟩ (Q2.listedAt ⟨65, by decide⟩
        (alnCheck_rep ⟨65, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 2 hp) Q2.T65_12_2 Q2.hfix65_12_2 Q2.hinj65_12_2
      Q2.hcardT65_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T65_12_2 i) (Q2.hfix65_12_2 i) _)
      colCert_65_12_2.hD ?_).symm
  rw [alnId_65 j hj]


theorem leaf_65_12_3 (hp : 3 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 65 []).length)
    (hq : (normIsRep.getD 65 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 3 hp)
        (rowE2 (⟨65, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp))
        (rowE1 (⟨65, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨65, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨65, by decide⟩ (listedAt ⟨65, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp)) T65_12
      hfix65_12 hinj65_12 hcardT65_12
      (fun i => conj_mem_of_fixedPoints _ _ (T65_12 i) (hfix65_12 i) _)
      ⟨65, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨65, by decide⟩ (Q2.listedAt ⟨65, by decide⟩
        (alnCheck_rep ⟨65, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 3 hp) Q2.T65_12_2 Q2.hfix65_12_2 Q2.hinj65_12_2
      Q2.hcardT65_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T65_12_2 i) (Q2.hfix65_12_2 i) _)
      colCert_65_12_3.hD ?_).symm
  rw [alnId_65 j hj]


theorem leaf_65_12_4 (hp : 4 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 65 []).length)
    (hq : (normIsRep.getD 65 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 4 hp)
        (rowE2 (⟨65, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp))
        (rowE1 (⟨65, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨65, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨65, by decide⟩ (listedAt ⟨65, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp)) T65_12
      hfix65_12 hinj65_12 hcardT65_12
      (fun i => conj_mem_of_fixedPoints _ _ (T65_12 i) (hfix65_12 i) _)
      ⟨65, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨65, by decide⟩ (Q2.listedAt ⟨65, by decide⟩
        (alnCheck_rep ⟨65, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 4 hp) Q2.T65_12_2 Q2.hfix65_12_2 Q2.hinj65_12_2
      Q2.hcardT65_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T65_12_2 i) (Q2.hfix65_12_2 i) _)
      colCert_65_12_4.hD ?_).symm
  rw [alnId_65 j hj]


theorem leaf_65_27_0 (hp : 0 < (Q2.transData.getD 27 []).length)
    (j : Nat) (hj : j < (repChars.getD 65 []).length)
    (hq : (normIsRep.getD 65 []).getD j false = true) :
    species (Q2.reps (⟨27, by decide⟩ : Fin 148)) (colE2 ⟨27, by decide⟩ 0 hp)
        (rowE2 (⟨65, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨27, by decide⟩ : Fin 148))
        (colE1 ⟨27, by decide⟩ 0 (transLenTr ⟨27, by decide⟩ 0 hp))
        (rowE1 (⟨65, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨65, by decide⟩ : Fin 148) ⟨27, by decide⟩ _
      (validAt ⟨65, by decide⟩ (listedAt ⟨65, by decide⟩ hj))
      (colE1 ⟨27, by decide⟩ 0 (transLenTr ⟨27, by decide⟩ 0 hp)) T65_27
      hfix65_27 hinj65_27 hcardT65_27
      (fun i => conj_mem_of_fixedPoints _ _ (T65_27 i) (hfix65_27 i) _)
      ⟨65, by decide⟩ ⟨27, by decide⟩ _
      (Q2.validAt ⟨65, by decide⟩ (Q2.listedAt ⟨65, by decide⟩
        (alnCheck_rep ⟨65, by decide⟩ hj hq).1))
      (colE2 ⟨27, by decide⟩ 0 hp) Q2.T65_27_2 Q2.hfix65_27_2 Q2.hinj65_27_2
      Q2.hcardT65_27_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T65_27_2 i) (Q2.hfix65_27_2 i) _)
      colCert_65_27_0.hD ?_).symm
  rw [alnId_65 j hj]


theorem leaf_65_27_1 (hp : 1 < (Q2.transData.getD 27 []).length)
    (j : Nat) (hj : j < (repChars.getD 65 []).length)
    (hq : (normIsRep.getD 65 []).getD j false = true) :
    species (Q2.reps (⟨27, by decide⟩ : Fin 148)) (colE2 ⟨27, by decide⟩ 1 hp)
        (rowE2 (⟨65, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨27, by decide⟩ : Fin 148))
        (colE1 ⟨27, by decide⟩ 1 (transLenTr ⟨27, by decide⟩ 1 hp))
        (rowE1 (⟨65, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨65, by decide⟩ : Fin 148) ⟨27, by decide⟩ _
      (validAt ⟨65, by decide⟩ (listedAt ⟨65, by decide⟩ hj))
      (colE1 ⟨27, by decide⟩ 1 (transLenTr ⟨27, by decide⟩ 1 hp)) T65_27
      hfix65_27 hinj65_27 hcardT65_27
      (fun i => conj_mem_of_fixedPoints _ _ (T65_27 i) (hfix65_27 i) _)
      ⟨65, by decide⟩ ⟨27, by decide⟩ _
      (Q2.validAt ⟨65, by decide⟩ (Q2.listedAt ⟨65, by decide⟩
        (alnCheck_rep ⟨65, by decide⟩ hj hq).1))
      (colE2 ⟨27, by decide⟩ 1 hp) Q2.T65_27_2 Q2.hfix65_27_2 Q2.hinj65_27_2
      Q2.hcardT65_27_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T65_27_2 i) (Q2.hfix65_27_2 i) _)
      colCert_65_27_1.hD ?_).symm
  rw [alnId_65 j hj]


theorem leaf_65_27_2 (hp : 2 < (Q2.transData.getD 27 []).length)
    (j : Nat) (hj : j < (repChars.getD 65 []).length)
    (hq : (normIsRep.getD 65 []).getD j false = true) :
    species (Q2.reps (⟨27, by decide⟩ : Fin 148)) (colE2 ⟨27, by decide⟩ 2 hp)
        (rowE2 (⟨65, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨27, by decide⟩ : Fin 148))
        (colE1 ⟨27, by decide⟩ 2 (transLenTr ⟨27, by decide⟩ 2 hp))
        (rowE1 (⟨65, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨65, by decide⟩ : Fin 148) ⟨27, by decide⟩ _
      (validAt ⟨65, by decide⟩ (listedAt ⟨65, by decide⟩ hj))
      (colE1 ⟨27, by decide⟩ 2 (transLenTr ⟨27, by decide⟩ 2 hp)) T65_27
      hfix65_27 hinj65_27 hcardT65_27
      (fun i => conj_mem_of_fixedPoints _ _ (T65_27 i) (hfix65_27 i) _)
      ⟨65, by decide⟩ ⟨27, by decide⟩ _
      (Q2.validAt ⟨65, by decide⟩ (Q2.listedAt ⟨65, by decide⟩
        (alnCheck_rep ⟨65, by decide⟩ hj hq).1))
      (colE2 ⟨27, by decide⟩ 2 hp) Q2.T65_27_2 Q2.hfix65_27_2 Q2.hinj65_27_2
      Q2.hcardT65_27_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T65_27_2 i) (Q2.hfix65_27_2 i) _)
      colCert_65_27_2.hD ?_).symm
  rw [alnId_65 j hj]


theorem leaf_65_27_3 (hp : 3 < (Q2.transData.getD 27 []).length)
    (j : Nat) (hj : j < (repChars.getD 65 []).length)
    (hq : (normIsRep.getD 65 []).getD j false = true) :
    species (Q2.reps (⟨27, by decide⟩ : Fin 148)) (colE2 ⟨27, by decide⟩ 3 hp)
        (rowE2 (⟨65, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨27, by decide⟩ : Fin 148))
        (colE1 ⟨27, by decide⟩ 3 (transLenTr ⟨27, by decide⟩ 3 hp))
        (rowE1 (⟨65, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨65, by decide⟩ : Fin 148) ⟨27, by decide⟩ _
      (validAt ⟨65, by decide⟩ (listedAt ⟨65, by decide⟩ hj))
      (colE1 ⟨27, by decide⟩ 3 (transLenTr ⟨27, by decide⟩ 3 hp)) T65_27
      hfix65_27 hinj65_27 hcardT65_27
      (fun i => conj_mem_of_fixedPoints _ _ (T65_27 i) (hfix65_27 i) _)
      ⟨65, by decide⟩ ⟨27, by decide⟩ _
      (Q2.validAt ⟨65, by decide⟩ (Q2.listedAt ⟨65, by decide⟩
        (alnCheck_rep ⟨65, by decide⟩ hj hq).1))
      (colE2 ⟨27, by decide⟩ 3 hp) Q2.T65_27_2 Q2.hfix65_27_2 Q2.hinj65_27_2
      Q2.hcardT65_27_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T65_27_2 i) (Q2.hfix65_27_2 i) _)
      colCert_65_27_3.hD ?_).symm
  rw [alnId_65 j hj]


theorem leaf_65_27_4 (hp : 4 < (Q2.transData.getD 27 []).length)
    (j : Nat) (hj : j < (repChars.getD 65 []).length)
    (hq : (normIsRep.getD 65 []).getD j false = true) :
    species (Q2.reps (⟨27, by decide⟩ : Fin 148)) (colE2 ⟨27, by decide⟩ 4 hp)
        (rowE2 (⟨65, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨27, by decide⟩ : Fin 148))
        (colE1 ⟨27, by decide⟩ 4 (transLenTr ⟨27, by decide⟩ 4 hp))
        (rowE1 (⟨65, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨65, by decide⟩ : Fin 148) ⟨27, by decide⟩ _
      (validAt ⟨65, by decide⟩ (listedAt ⟨65, by decide⟩ hj))
      (colE1 ⟨27, by decide⟩ 4 (transLenTr ⟨27, by decide⟩ 4 hp)) T65_27
      hfix65_27 hinj65_27 hcardT65_27
      (fun i => conj_mem_of_fixedPoints _ _ (T65_27 i) (hfix65_27 i) _)
      ⟨65, by decide⟩ ⟨27, by decide⟩ _
      (Q2.validAt ⟨65, by decide⟩ (Q2.listedAt ⟨65, by decide⟩
        (alnCheck_rep ⟨65, by decide⟩ hj hq).1))
      (colE2 ⟨27, by decide⟩ 4 hp) Q2.T65_27_2 Q2.hfix65_27_2 Q2.hinj65_27_2
      Q2.hcardT65_27_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T65_27_2 i) (Q2.hfix65_27_2 i) _)
      colCert_65_27_4.hD ?_).symm
  rw [alnId_65 j hj]


theorem leaf_65_27_5 (hp : 5 < (Q2.transData.getD 27 []).length)
    (j : Nat) (hj : j < (repChars.getD 65 []).length)
    (hq : (normIsRep.getD 65 []).getD j false = true) :
    species (Q2.reps (⟨27, by decide⟩ : Fin 148)) (colE2 ⟨27, by decide⟩ 5 hp)
        (rowE2 (⟨65, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨27, by decide⟩ : Fin 148))
        (colE1 ⟨27, by decide⟩ 5 (transLenTr ⟨27, by decide⟩ 5 hp))
        (rowE1 (⟨65, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨65, by decide⟩ : Fin 148) ⟨27, by decide⟩ _
      (validAt ⟨65, by decide⟩ (listedAt ⟨65, by decide⟩ hj))
      (colE1 ⟨27, by decide⟩ 5 (transLenTr ⟨27, by decide⟩ 5 hp)) T65_27
      hfix65_27 hinj65_27 hcardT65_27
      (fun i => conj_mem_of_fixedPoints _ _ (T65_27 i) (hfix65_27 i) _)
      ⟨65, by decide⟩ ⟨27, by decide⟩ _
      (Q2.validAt ⟨65, by decide⟩ (Q2.listedAt ⟨65, by decide⟩
        (alnCheck_rep ⟨65, by decide⟩ hj hq).1))
      (colE2 ⟨27, by decide⟩ 5 hp) Q2.T65_27_2 Q2.hfix65_27_2 Q2.hinj65_27_2
      Q2.hcardT65_27_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T65_27_2 i) (Q2.hfix65_27_2 i) _)
      colCert_65_27_5.hD ?_).symm
  rw [alnId_65 j hj]


theorem leaf_65_27_10 (hp : 10 < (Q2.transData.getD 27 []).length)
    (j : Nat) (hj : j < (repChars.getD 65 []).length)
    (hq : (normIsRep.getD 65 []).getD j false = true) :
    species (Q2.reps (⟨27, by decide⟩ : Fin 148)) (colE2 ⟨27, by decide⟩ 10 hp)
        (rowE2 (⟨65, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨27, by decide⟩ : Fin 148))
        (colE1 ⟨27, by decide⟩ 10 (transLenTr ⟨27, by decide⟩ 10 hp))
        (rowE1 (⟨65, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨65, by decide⟩ : Fin 148) ⟨27, by decide⟩ _
      (validAt ⟨65, by decide⟩ (listedAt ⟨65, by decide⟩ hj))
      (colE1 ⟨27, by decide⟩ 10 (transLenTr ⟨27, by decide⟩ 10 hp)) T65_27
      hfix65_27 hinj65_27 hcardT65_27
      (fun i => conj_mem_of_fixedPoints _ _ (T65_27 i) (hfix65_27 i) _)
      ⟨65, by decide⟩ ⟨27, by decide⟩ _
      (Q2.validAt ⟨65, by decide⟩ (Q2.listedAt ⟨65, by decide⟩
        (alnCheck_rep ⟨65, by decide⟩ hj hq).1))
      (colE2 ⟨27, by decide⟩ 10 hp) Q2.T65_27_2 Q2.hfix65_27_2 Q2.hinj65_27_2
      Q2.hcardT65_27_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T65_27_2 i) (Q2.hfix65_27_2 i) _)
      colCert_65_27_10.hD ?_).symm
  rw [alnId_65 j hj]


theorem leaf_65_27_15 (hp : 15 < (Q2.transData.getD 27 []).length)
    (j : Nat) (hj : j < (repChars.getD 65 []).length)
    (hq : (normIsRep.getD 65 []).getD j false = true) :
    species (Q2.reps (⟨27, by decide⟩ : Fin 148)) (colE2 ⟨27, by decide⟩ 15 hp)
        (rowE2 (⟨65, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨27, by decide⟩ : Fin 148))
        (colE1 ⟨27, by decide⟩ 15 (transLenTr ⟨27, by decide⟩ 15 hp))
        (rowE1 (⟨65, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨65, by decide⟩ : Fin 148) ⟨27, by decide⟩ _
      (validAt ⟨65, by decide⟩ (listedAt ⟨65, by decide⟩ hj))
      (colE1 ⟨27, by decide⟩ 15 (transLenTr ⟨27, by decide⟩ 15 hp)) T65_27
      hfix65_27 hinj65_27 hcardT65_27
      (fun i => conj_mem_of_fixedPoints _ _ (T65_27 i) (hfix65_27 i) _)
      ⟨65, by decide⟩ ⟨27, by decide⟩ _
      (Q2.validAt ⟨65, by decide⟩ (Q2.listedAt ⟨65, by decide⟩
        (alnCheck_rep ⟨65, by decide⟩ hj hq).1))
      (colE2 ⟨27, by decide⟩ 15 hp) Q2.T65_27_2 Q2.hfix65_27_2 Q2.hinj65_27_2
      Q2.hcardT65_27_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T65_27_2 i) (Q2.hfix65_27_2 i) _)
      colCert_65_27_15.hD ?_).symm
  rw [alnId_65 j hj]


theorem leaf_65_27_20 (hp : 20 < (Q2.transData.getD 27 []).length)
    (j : Nat) (hj : j < (repChars.getD 65 []).length)
    (hq : (normIsRep.getD 65 []).getD j false = true) :
    species (Q2.reps (⟨27, by decide⟩ : Fin 148)) (colE2 ⟨27, by decide⟩ 20 hp)
        (rowE2 (⟨65, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨27, by decide⟩ : Fin 148))
        (colE1 ⟨27, by decide⟩ 20 (transLenTr ⟨27, by decide⟩ 20 hp))
        (rowE1 (⟨65, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨65, by decide⟩ : Fin 148) ⟨27, by decide⟩ _
      (validAt ⟨65, by decide⟩ (listedAt ⟨65, by decide⟩ hj))
      (colE1 ⟨27, by decide⟩ 20 (transLenTr ⟨27, by decide⟩ 20 hp)) T65_27
      hfix65_27 hinj65_27 hcardT65_27
      (fun i => conj_mem_of_fixedPoints _ _ (T65_27 i) (hfix65_27 i) _)
      ⟨65, by decide⟩ ⟨27, by decide⟩ _
      (Q2.validAt ⟨65, by decide⟩ (Q2.listedAt ⟨65, by decide⟩
        (alnCheck_rep ⟨65, by decide⟩ hj hq).1))
      (colE2 ⟨27, by decide⟩ 20 hp) Q2.T65_27_2 Q2.hfix65_27_2 Q2.hinj65_27_2
      Q2.hcardT65_27_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T65_27_2 i) (Q2.hfix65_27_2 i) _)
      colCert_65_27_20.hD ?_).symm
  rw [alnId_65 j hj]


theorem leaf_65_30_0 (hp : 0 < (Q2.transData.getD 30 []).length)
    (j : Nat) (hj : j < (repChars.getD 65 []).length)
    (hq : (normIsRep.getD 65 []).getD j false = true) :
    species (Q2.reps (⟨30, by decide⟩ : Fin 148)) (colE2 ⟨30, by decide⟩ 0 hp)
        (rowE2 (⟨65, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨30, by decide⟩ : Fin 148))
        (colE1 ⟨30, by decide⟩ 0 (transLenTr ⟨30, by decide⟩ 0 hp))
        (rowE1 (⟨65, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨65, by decide⟩ : Fin 148) ⟨30, by decide⟩ _
      (validAt ⟨65, by decide⟩ (listedAt ⟨65, by decide⟩ hj))
      (colE1 ⟨30, by decide⟩ 0 (transLenTr ⟨30, by decide⟩ 0 hp)) T65_30
      hfix65_30 hinj65_30 hcardT65_30
      (fun i => conj_mem_of_fixedPoints _ _ (T65_30 i) (hfix65_30 i) _)
      ⟨65, by decide⟩ ⟨30, by decide⟩ _
      (Q2.validAt ⟨65, by decide⟩ (Q2.listedAt ⟨65, by decide⟩
        (alnCheck_rep ⟨65, by decide⟩ hj hq).1))
      (colE2 ⟨30, by decide⟩ 0 hp) Q2.T65_30_2 Q2.hfix65_30_2 Q2.hinj65_30_2
      Q2.hcardT65_30_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T65_30_2 i) (Q2.hfix65_30_2 i) _)
      colCert_65_30_0.hD ?_).symm
  rw [alnId_65 j hj]


theorem leaf_65_30_1 (hp : 1 < (Q2.transData.getD 30 []).length)
    (j : Nat) (hj : j < (repChars.getD 65 []).length)
    (hq : (normIsRep.getD 65 []).getD j false = true) :
    species (Q2.reps (⟨30, by decide⟩ : Fin 148)) (colE2 ⟨30, by decide⟩ 1 hp)
        (rowE2 (⟨65, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨30, by decide⟩ : Fin 148))
        (colE1 ⟨30, by decide⟩ 1 (transLenTr ⟨30, by decide⟩ 1 hp))
        (rowE1 (⟨65, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨65, by decide⟩ : Fin 148) ⟨30, by decide⟩ _
      (validAt ⟨65, by decide⟩ (listedAt ⟨65, by decide⟩ hj))
      (colE1 ⟨30, by decide⟩ 1 (transLenTr ⟨30, by decide⟩ 1 hp)) T65_30
      hfix65_30 hinj65_30 hcardT65_30
      (fun i => conj_mem_of_fixedPoints _ _ (T65_30 i) (hfix65_30 i) _)
      ⟨65, by decide⟩ ⟨30, by decide⟩ _
      (Q2.validAt ⟨65, by decide⟩ (Q2.listedAt ⟨65, by decide⟩
        (alnCheck_rep ⟨65, by decide⟩ hj hq).1))
      (colE2 ⟨30, by decide⟩ 1 hp) Q2.T65_30_2 Q2.hfix65_30_2 Q2.hinj65_30_2
      Q2.hcardT65_30_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T65_30_2 i) (Q2.hfix65_30_2 i) _)
      colCert_65_30_1.hD ?_).symm
  rw [alnId_65 j hj]


theorem leaf_65_30_2 (hp : 2 < (Q2.transData.getD 30 []).length)
    (j : Nat) (hj : j < (repChars.getD 65 []).length)
    (hq : (normIsRep.getD 65 []).getD j false = true) :
    species (Q2.reps (⟨30, by decide⟩ : Fin 148)) (colE2 ⟨30, by decide⟩ 2 hp)
        (rowE2 (⟨65, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨30, by decide⟩ : Fin 148))
        (colE1 ⟨30, by decide⟩ 2 (transLenTr ⟨30, by decide⟩ 2 hp))
        (rowE1 (⟨65, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨65, by decide⟩ : Fin 148) ⟨30, by decide⟩ _
      (validAt ⟨65, by decide⟩ (listedAt ⟨65, by decide⟩ hj))
      (colE1 ⟨30, by decide⟩ 2 (transLenTr ⟨30, by decide⟩ 2 hp)) T65_30
      hfix65_30 hinj65_30 hcardT65_30
      (fun i => conj_mem_of_fixedPoints _ _ (T65_30 i) (hfix65_30 i) _)
      ⟨65, by decide⟩ ⟨30, by decide⟩ _
      (Q2.validAt ⟨65, by decide⟩ (Q2.listedAt ⟨65, by decide⟩
        (alnCheck_rep ⟨65, by decide⟩ hj hq).1))
      (colE2 ⟨30, by decide⟩ 2 hp) Q2.T65_30_2 Q2.hfix65_30_2 Q2.hinj65_30_2
      Q2.hcardT65_30_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T65_30_2 i) (Q2.hfix65_30_2 i) _)
      colCert_65_30_2.hD ?_).symm
  rw [alnId_65 j hj]


theorem leaf_65_30_3 (hp : 3 < (Q2.transData.getD 30 []).length)
    (j : Nat) (hj : j < (repChars.getD 65 []).length)
    (hq : (normIsRep.getD 65 []).getD j false = true) :
    species (Q2.reps (⟨30, by decide⟩ : Fin 148)) (colE2 ⟨30, by decide⟩ 3 hp)
        (rowE2 (⟨65, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨30, by decide⟩ : Fin 148))
        (colE1 ⟨30, by decide⟩ 3 (transLenTr ⟨30, by decide⟩ 3 hp))
        (rowE1 (⟨65, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨65, by decide⟩ : Fin 148) ⟨30, by decide⟩ _
      (validAt ⟨65, by decide⟩ (listedAt ⟨65, by decide⟩ hj))
      (colE1 ⟨30, by decide⟩ 3 (transLenTr ⟨30, by decide⟩ 3 hp)) T65_30
      hfix65_30 hinj65_30 hcardT65_30
      (fun i => conj_mem_of_fixedPoints _ _ (T65_30 i) (hfix65_30 i) _)
      ⟨65, by decide⟩ ⟨30, by decide⟩ _
      (Q2.validAt ⟨65, by decide⟩ (Q2.listedAt ⟨65, by decide⟩
        (alnCheck_rep ⟨65, by decide⟩ hj hq).1))
      (colE2 ⟨30, by decide⟩ 3 hp) Q2.T65_30_2 Q2.hfix65_30_2 Q2.hinj65_30_2
      Q2.hcardT65_30_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T65_30_2 i) (Q2.hfix65_30_2 i) _)
      colCert_65_30_3.hD ?_).symm
  rw [alnId_65 j hj]


theorem leaf_65_30_4 (hp : 4 < (Q2.transData.getD 30 []).length)
    (j : Nat) (hj : j < (repChars.getD 65 []).length)
    (hq : (normIsRep.getD 65 []).getD j false = true) :
    species (Q2.reps (⟨30, by decide⟩ : Fin 148)) (colE2 ⟨30, by decide⟩ 4 hp)
        (rowE2 (⟨65, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨30, by decide⟩ : Fin 148))
        (colE1 ⟨30, by decide⟩ 4 (transLenTr ⟨30, by decide⟩ 4 hp))
        (rowE1 (⟨65, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨65, by decide⟩ : Fin 148) ⟨30, by decide⟩ _
      (validAt ⟨65, by decide⟩ (listedAt ⟨65, by decide⟩ hj))
      (colE1 ⟨30, by decide⟩ 4 (transLenTr ⟨30, by decide⟩ 4 hp)) T65_30
      hfix65_30 hinj65_30 hcardT65_30
      (fun i => conj_mem_of_fixedPoints _ _ (T65_30 i) (hfix65_30 i) _)
      ⟨65, by decide⟩ ⟨30, by decide⟩ _
      (Q2.validAt ⟨65, by decide⟩ (Q2.listedAt ⟨65, by decide⟩
        (alnCheck_rep ⟨65, by decide⟩ hj hq).1))
      (colE2 ⟨30, by decide⟩ 4 hp) Q2.T65_30_2 Q2.hfix65_30_2 Q2.hinj65_30_2
      Q2.hcardT65_30_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T65_30_2 i) (Q2.hfix65_30_2 i) _)
      colCert_65_30_4.hD ?_).symm
  rw [alnId_65 j hj]


theorem leaf_65_30_5 (hp : 5 < (Q2.transData.getD 30 []).length)
    (j : Nat) (hj : j < (repChars.getD 65 []).length)
    (hq : (normIsRep.getD 65 []).getD j false = true) :
    species (Q2.reps (⟨30, by decide⟩ : Fin 148)) (colE2 ⟨30, by decide⟩ 5 hp)
        (rowE2 (⟨65, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨30, by decide⟩ : Fin 148))
        (colE1 ⟨30, by decide⟩ 5 (transLenTr ⟨30, by decide⟩ 5 hp))
        (rowE1 (⟨65, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨65, by decide⟩ : Fin 148) ⟨30, by decide⟩ _
      (validAt ⟨65, by decide⟩ (listedAt ⟨65, by decide⟩ hj))
      (colE1 ⟨30, by decide⟩ 5 (transLenTr ⟨30, by decide⟩ 5 hp)) T65_30
      hfix65_30 hinj65_30 hcardT65_30
      (fun i => conj_mem_of_fixedPoints _ _ (T65_30 i) (hfix65_30 i) _)
      ⟨65, by decide⟩ ⟨30, by decide⟩ _
      (Q2.validAt ⟨65, by decide⟩ (Q2.listedAt ⟨65, by decide⟩
        (alnCheck_rep ⟨65, by decide⟩ hj hq).1))
      (colE2 ⟨30, by decide⟩ 5 hp) Q2.T65_30_2 Q2.hfix65_30_2 Q2.hinj65_30_2
      Q2.hcardT65_30_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T65_30_2 i) (Q2.hfix65_30_2 i) _)
      colCert_65_30_5.hD ?_).symm
  rw [alnId_65 j hj]


theorem leaf_65_30_10 (hp : 10 < (Q2.transData.getD 30 []).length)
    (j : Nat) (hj : j < (repChars.getD 65 []).length)
    (hq : (normIsRep.getD 65 []).getD j false = true) :
    species (Q2.reps (⟨30, by decide⟩ : Fin 148)) (colE2 ⟨30, by decide⟩ 10 hp)
        (rowE2 (⟨65, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨30, by decide⟩ : Fin 148))
        (colE1 ⟨30, by decide⟩ 10 (transLenTr ⟨30, by decide⟩ 10 hp))
        (rowE1 (⟨65, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨65, by decide⟩ : Fin 148) ⟨30, by decide⟩ _
      (validAt ⟨65, by decide⟩ (listedAt ⟨65, by decide⟩ hj))
      (colE1 ⟨30, by decide⟩ 10 (transLenTr ⟨30, by decide⟩ 10 hp)) T65_30
      hfix65_30 hinj65_30 hcardT65_30
      (fun i => conj_mem_of_fixedPoints _ _ (T65_30 i) (hfix65_30 i) _)
      ⟨65, by decide⟩ ⟨30, by decide⟩ _
      (Q2.validAt ⟨65, by decide⟩ (Q2.listedAt ⟨65, by decide⟩
        (alnCheck_rep ⟨65, by decide⟩ hj hq).1))
      (colE2 ⟨30, by decide⟩ 10 hp) Q2.T65_30_2 Q2.hfix65_30_2 Q2.hinj65_30_2
      Q2.hcardT65_30_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T65_30_2 i) (Q2.hfix65_30_2 i) _)
      colCert_65_30_10.hD ?_).symm
  rw [alnId_65 j hj]


theorem leaf_65_30_15 (hp : 15 < (Q2.transData.getD 30 []).length)
    (j : Nat) (hj : j < (repChars.getD 65 []).length)
    (hq : (normIsRep.getD 65 []).getD j false = true) :
    species (Q2.reps (⟨30, by decide⟩ : Fin 148)) (colE2 ⟨30, by decide⟩ 15 hp)
        (rowE2 (⟨65, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨30, by decide⟩ : Fin 148))
        (colE1 ⟨30, by decide⟩ 15 (transLenTr ⟨30, by decide⟩ 15 hp))
        (rowE1 (⟨65, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨65, by decide⟩ : Fin 148) ⟨30, by decide⟩ _
      (validAt ⟨65, by decide⟩ (listedAt ⟨65, by decide⟩ hj))
      (colE1 ⟨30, by decide⟩ 15 (transLenTr ⟨30, by decide⟩ 15 hp)) T65_30
      hfix65_30 hinj65_30 hcardT65_30
      (fun i => conj_mem_of_fixedPoints _ _ (T65_30 i) (hfix65_30 i) _)
      ⟨65, by decide⟩ ⟨30, by decide⟩ _
      (Q2.validAt ⟨65, by decide⟩ (Q2.listedAt ⟨65, by decide⟩
        (alnCheck_rep ⟨65, by decide⟩ hj hq).1))
      (colE2 ⟨30, by decide⟩ 15 hp) Q2.T65_30_2 Q2.hfix65_30_2 Q2.hinj65_30_2
      Q2.hcardT65_30_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T65_30_2 i) (Q2.hfix65_30_2 i) _)
      colCert_65_30_15.hD ?_).symm
  rw [alnId_65 j hj]


theorem leaf_65_30_20 (hp : 20 < (Q2.transData.getD 30 []).length)
    (j : Nat) (hj : j < (repChars.getD 65 []).length)
    (hq : (normIsRep.getD 65 []).getD j false = true) :
    species (Q2.reps (⟨30, by decide⟩ : Fin 148)) (colE2 ⟨30, by decide⟩ 20 hp)
        (rowE2 (⟨65, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨30, by decide⟩ : Fin 148))
        (colE1 ⟨30, by decide⟩ 20 (transLenTr ⟨30, by decide⟩ 20 hp))
        (rowE1 (⟨65, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨65, by decide⟩ : Fin 148) ⟨30, by decide⟩ _
      (validAt ⟨65, by decide⟩ (listedAt ⟨65, by decide⟩ hj))
      (colE1 ⟨30, by decide⟩ 20 (transLenTr ⟨30, by decide⟩ 20 hp)) T65_30
      hfix65_30 hinj65_30 hcardT65_30
      (fun i => conj_mem_of_fixedPoints _ _ (T65_30 i) (hfix65_30 i) _)
      ⟨65, by decide⟩ ⟨30, by decide⟩ _
      (Q2.validAt ⟨65, by decide⟩ (Q2.listedAt ⟨65, by decide⟩
        (alnCheck_rep ⟨65, by decide⟩ hj hq).1))
      (colE2 ⟨30, by decide⟩ 20 hp) Q2.T65_30_2 Q2.hfix65_30_2 Q2.hinj65_30_2
      Q2.hcardT65_30_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T65_30_2 i) (Q2.hfix65_30_2 i) _)
      colCert_65_30_20.hD ?_).symm
  rw [alnId_65 j hj]


theorem leaf_65_35_0 (hp : 0 < (Q2.transData.getD 35 []).length)
    (j : Nat) (hj : j < (repChars.getD 65 []).length)
    (hq : (normIsRep.getD 65 []).getD j false = true) :
    species (Q2.reps (⟨35, by decide⟩ : Fin 148)) (colE2 ⟨35, by decide⟩ 0 hp)
        (rowE2 (⟨65, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨35, by decide⟩ : Fin 148))
        (colE1 ⟨35, by decide⟩ 0 (transLenTr ⟨35, by decide⟩ 0 hp))
        (rowE1 (⟨65, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨65, by decide⟩ : Fin 148) ⟨35, by decide⟩ _
      (validAt ⟨65, by decide⟩ (listedAt ⟨65, by decide⟩ hj))
      (colE1 ⟨35, by decide⟩ 0 (transLenTr ⟨35, by decide⟩ 0 hp)) T65_35
      hfix65_35 hinj65_35 hcardT65_35
      (fun i => conj_mem_of_fixedPoints _ _ (T65_35 i) (hfix65_35 i) _)
      ⟨65, by decide⟩ ⟨35, by decide⟩ _
      (Q2.validAt ⟨65, by decide⟩ (Q2.listedAt ⟨65, by decide⟩
        (alnCheck_rep ⟨65, by decide⟩ hj hq).1))
      (colE2 ⟨35, by decide⟩ 0 hp) Q2.T65_35_2 Q2.hfix65_35_2 Q2.hinj65_35_2
      Q2.hcardT65_35_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T65_35_2 i) (Q2.hfix65_35_2 i) _)
      colCert_65_35_0.hD ?_).symm
  rw [alnId_65 j hj]


theorem leaf_65_35_1 (hp : 1 < (Q2.transData.getD 35 []).length)
    (j : Nat) (hj : j < (repChars.getD 65 []).length)
    (hq : (normIsRep.getD 65 []).getD j false = true) :
    species (Q2.reps (⟨35, by decide⟩ : Fin 148)) (colE2 ⟨35, by decide⟩ 1 hp)
        (rowE2 (⟨65, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨35, by decide⟩ : Fin 148))
        (colE1 ⟨35, by decide⟩ 1 (transLenTr ⟨35, by decide⟩ 1 hp))
        (rowE1 (⟨65, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨65, by decide⟩ : Fin 148) ⟨35, by decide⟩ _
      (validAt ⟨65, by decide⟩ (listedAt ⟨65, by decide⟩ hj))
      (colE1 ⟨35, by decide⟩ 1 (transLenTr ⟨35, by decide⟩ 1 hp)) T65_35
      hfix65_35 hinj65_35 hcardT65_35
      (fun i => conj_mem_of_fixedPoints _ _ (T65_35 i) (hfix65_35 i) _)
      ⟨65, by decide⟩ ⟨35, by decide⟩ _
      (Q2.validAt ⟨65, by decide⟩ (Q2.listedAt ⟨65, by decide⟩
        (alnCheck_rep ⟨65, by decide⟩ hj hq).1))
      (colE2 ⟨35, by decide⟩ 1 hp) Q2.T65_35_2 Q2.hfix65_35_2 Q2.hinj65_35_2
      Q2.hcardT65_35_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T65_35_2 i) (Q2.hfix65_35_2 i) _)
      colCert_65_35_1.hD ?_).symm
  rw [alnId_65 j hj]


theorem leaf_65_35_2 (hp : 2 < (Q2.transData.getD 35 []).length)
    (j : Nat) (hj : j < (repChars.getD 65 []).length)
    (hq : (normIsRep.getD 65 []).getD j false = true) :
    species (Q2.reps (⟨35, by decide⟩ : Fin 148)) (colE2 ⟨35, by decide⟩ 2 hp)
        (rowE2 (⟨65, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨35, by decide⟩ : Fin 148))
        (colE1 ⟨35, by decide⟩ 2 (transLenTr ⟨35, by decide⟩ 2 hp))
        (rowE1 (⟨65, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨65, by decide⟩ : Fin 148) ⟨35, by decide⟩ _
      (validAt ⟨65, by decide⟩ (listedAt ⟨65, by decide⟩ hj))
      (colE1 ⟨35, by decide⟩ 2 (transLenTr ⟨35, by decide⟩ 2 hp)) T65_35
      hfix65_35 hinj65_35 hcardT65_35
      (fun i => conj_mem_of_fixedPoints _ _ (T65_35 i) (hfix65_35 i) _)
      ⟨65, by decide⟩ ⟨35, by decide⟩ _
      (Q2.validAt ⟨65, by decide⟩ (Q2.listedAt ⟨65, by decide⟩
        (alnCheck_rep ⟨65, by decide⟩ hj hq).1))
      (colE2 ⟨35, by decide⟩ 2 hp) Q2.T65_35_2 Q2.hfix65_35_2 Q2.hinj65_35_2
      Q2.hcardT65_35_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T65_35_2 i) (Q2.hfix65_35_2 i) _)
      colCert_65_35_2.hD ?_).symm
  rw [alnId_65 j hj]


theorem leaf_65_35_3 (hp : 3 < (Q2.transData.getD 35 []).length)
    (j : Nat) (hj : j < (repChars.getD 65 []).length)
    (hq : (normIsRep.getD 65 []).getD j false = true) :
    species (Q2.reps (⟨35, by decide⟩ : Fin 148)) (colE2 ⟨35, by decide⟩ 3 hp)
        (rowE2 (⟨65, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨35, by decide⟩ : Fin 148))
        (colE1 ⟨35, by decide⟩ 3 (transLenTr ⟨35, by decide⟩ 3 hp))
        (rowE1 (⟨65, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨65, by decide⟩ : Fin 148) ⟨35, by decide⟩ _
      (validAt ⟨65, by decide⟩ (listedAt ⟨65, by decide⟩ hj))
      (colE1 ⟨35, by decide⟩ 3 (transLenTr ⟨35, by decide⟩ 3 hp)) T65_35
      hfix65_35 hinj65_35 hcardT65_35
      (fun i => conj_mem_of_fixedPoints _ _ (T65_35 i) (hfix65_35 i) _)
      ⟨65, by decide⟩ ⟨35, by decide⟩ _
      (Q2.validAt ⟨65, by decide⟩ (Q2.listedAt ⟨65, by decide⟩
        (alnCheck_rep ⟨65, by decide⟩ hj hq).1))
      (colE2 ⟨35, by decide⟩ 3 hp) Q2.T65_35_2 Q2.hfix65_35_2 Q2.hinj65_35_2
      Q2.hcardT65_35_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T65_35_2 i) (Q2.hfix65_35_2 i) _)
      colCert_65_35_3.hD ?_).symm
  rw [alnId_65 j hj]


theorem leaf_65_35_4 (hp : 4 < (Q2.transData.getD 35 []).length)
    (j : Nat) (hj : j < (repChars.getD 65 []).length)
    (hq : (normIsRep.getD 65 []).getD j false = true) :
    species (Q2.reps (⟨35, by decide⟩ : Fin 148)) (colE2 ⟨35, by decide⟩ 4 hp)
        (rowE2 (⟨65, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨35, by decide⟩ : Fin 148))
        (colE1 ⟨35, by decide⟩ 4 (transLenTr ⟨35, by decide⟩ 4 hp))
        (rowE1 (⟨65, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨65, by decide⟩ : Fin 148) ⟨35, by decide⟩ _
      (validAt ⟨65, by decide⟩ (listedAt ⟨65, by decide⟩ hj))
      (colE1 ⟨35, by decide⟩ 4 (transLenTr ⟨35, by decide⟩ 4 hp)) T65_35
      hfix65_35 hinj65_35 hcardT65_35
      (fun i => conj_mem_of_fixedPoints _ _ (T65_35 i) (hfix65_35 i) _)
      ⟨65, by decide⟩ ⟨35, by decide⟩ _
      (Q2.validAt ⟨65, by decide⟩ (Q2.listedAt ⟨65, by decide⟩
        (alnCheck_rep ⟨65, by decide⟩ hj hq).1))
      (colE2 ⟨35, by decide⟩ 4 hp) Q2.T65_35_2 Q2.hfix65_35_2 Q2.hinj65_35_2
      Q2.hcardT65_35_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T65_35_2 i) (Q2.hfix65_35_2 i) _)
      colCert_65_35_4.hD ?_).symm
  rw [alnId_65 j hj]


theorem leaf_65_35_5 (hp : 5 < (Q2.transData.getD 35 []).length)
    (j : Nat) (hj : j < (repChars.getD 65 []).length)
    (hq : (normIsRep.getD 65 []).getD j false = true) :
    species (Q2.reps (⟨35, by decide⟩ : Fin 148)) (colE2 ⟨35, by decide⟩ 5 hp)
        (rowE2 (⟨65, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨35, by decide⟩ : Fin 148))
        (colE1 ⟨35, by decide⟩ 5 (transLenTr ⟨35, by decide⟩ 5 hp))
        (rowE1 (⟨65, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨65, by decide⟩ : Fin 148) ⟨35, by decide⟩ _
      (validAt ⟨65, by decide⟩ (listedAt ⟨65, by decide⟩ hj))
      (colE1 ⟨35, by decide⟩ 5 (transLenTr ⟨35, by decide⟩ 5 hp)) T65_35
      hfix65_35 hinj65_35 hcardT65_35
      (fun i => conj_mem_of_fixedPoints _ _ (T65_35 i) (hfix65_35 i) _)
      ⟨65, by decide⟩ ⟨35, by decide⟩ _
      (Q2.validAt ⟨65, by decide⟩ (Q2.listedAt ⟨65, by decide⟩
        (alnCheck_rep ⟨65, by decide⟩ hj hq).1))
      (colE2 ⟨35, by decide⟩ 5 hp) Q2.T65_35_2 Q2.hfix65_35_2 Q2.hinj65_35_2
      Q2.hcardT65_35_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T65_35_2 i) (Q2.hfix65_35_2 i) _)
      colCert_65_35_5.hD ?_).symm
  rw [alnId_65 j hj]


theorem leaf_65_35_10 (hp : 10 < (Q2.transData.getD 35 []).length)
    (j : Nat) (hj : j < (repChars.getD 65 []).length)
    (hq : (normIsRep.getD 65 []).getD j false = true) :
    species (Q2.reps (⟨35, by decide⟩ : Fin 148)) (colE2 ⟨35, by decide⟩ 10 hp)
        (rowE2 (⟨65, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨35, by decide⟩ : Fin 148))
        (colE1 ⟨35, by decide⟩ 10 (transLenTr ⟨35, by decide⟩ 10 hp))
        (rowE1 (⟨65, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨65, by decide⟩ : Fin 148) ⟨35, by decide⟩ _
      (validAt ⟨65, by decide⟩ (listedAt ⟨65, by decide⟩ hj))
      (colE1 ⟨35, by decide⟩ 10 (transLenTr ⟨35, by decide⟩ 10 hp)) T65_35
      hfix65_35 hinj65_35 hcardT65_35
      (fun i => conj_mem_of_fixedPoints _ _ (T65_35 i) (hfix65_35 i) _)
      ⟨65, by decide⟩ ⟨35, by decide⟩ _
      (Q2.validAt ⟨65, by decide⟩ (Q2.listedAt ⟨65, by decide⟩
        (alnCheck_rep ⟨65, by decide⟩ hj hq).1))
      (colE2 ⟨35, by decide⟩ 10 hp) Q2.T65_35_2 Q2.hfix65_35_2 Q2.hinj65_35_2
      Q2.hcardT65_35_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T65_35_2 i) (Q2.hfix65_35_2 i) _)
      colCert_65_35_10.hD ?_).symm
  rw [alnId_65 j hj]


theorem leaf_65_35_15 (hp : 15 < (Q2.transData.getD 35 []).length)
    (j : Nat) (hj : j < (repChars.getD 65 []).length)
    (hq : (normIsRep.getD 65 []).getD j false = true) :
    species (Q2.reps (⟨35, by decide⟩ : Fin 148)) (colE2 ⟨35, by decide⟩ 15 hp)
        (rowE2 (⟨65, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨35, by decide⟩ : Fin 148))
        (colE1 ⟨35, by decide⟩ 15 (transLenTr ⟨35, by decide⟩ 15 hp))
        (rowE1 (⟨65, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨65, by decide⟩ : Fin 148) ⟨35, by decide⟩ _
      (validAt ⟨65, by decide⟩ (listedAt ⟨65, by decide⟩ hj))
      (colE1 ⟨35, by decide⟩ 15 (transLenTr ⟨35, by decide⟩ 15 hp)) T65_35
      hfix65_35 hinj65_35 hcardT65_35
      (fun i => conj_mem_of_fixedPoints _ _ (T65_35 i) (hfix65_35 i) _)
      ⟨65, by decide⟩ ⟨35, by decide⟩ _
      (Q2.validAt ⟨65, by decide⟩ (Q2.listedAt ⟨65, by decide⟩
        (alnCheck_rep ⟨65, by decide⟩ hj hq).1))
      (colE2 ⟨35, by decide⟩ 15 hp) Q2.T65_35_2 Q2.hfix65_35_2 Q2.hinj65_35_2
      Q2.hcardT65_35_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T65_35_2 i) (Q2.hfix65_35_2 i) _)
      colCert_65_35_15.hD ?_).symm
  rw [alnId_65 j hj]


theorem leaf_65_35_20 (hp : 20 < (Q2.transData.getD 35 []).length)
    (j : Nat) (hj : j < (repChars.getD 65 []).length)
    (hq : (normIsRep.getD 65 []).getD j false = true) :
    species (Q2.reps (⟨35, by decide⟩ : Fin 148)) (colE2 ⟨35, by decide⟩ 20 hp)
        (rowE2 (⟨65, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨35, by decide⟩ : Fin 148))
        (colE1 ⟨35, by decide⟩ 20 (transLenTr ⟨35, by decide⟩ 20 hp))
        (rowE1 (⟨65, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨65, by decide⟩ : Fin 148) ⟨35, by decide⟩ _
      (validAt ⟨65, by decide⟩ (listedAt ⟨65, by decide⟩ hj))
      (colE1 ⟨35, by decide⟩ 20 (transLenTr ⟨35, by decide⟩ 20 hp)) T65_35
      hfix65_35 hinj65_35 hcardT65_35
      (fun i => conj_mem_of_fixedPoints _ _ (T65_35 i) (hfix65_35 i) _)
      ⟨65, by decide⟩ ⟨35, by decide⟩ _
      (Q2.validAt ⟨65, by decide⟩ (Q2.listedAt ⟨65, by decide⟩
        (alnCheck_rep ⟨65, by decide⟩ hj hq).1))
      (colE2 ⟨35, by decide⟩ 20 hp) Q2.T65_35_2 Q2.hfix65_35_2 Q2.hinj65_35_2
      Q2.hcardT65_35_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T65_35_2 i) (Q2.hfix65_35_2 i) _)
      colCert_65_35_20.hD ?_).symm
  rw [alnId_65 j hj]


theorem leaf_65_40_0 (hp : 0 < (Q2.transData.getD 40 []).length)
    (j : Nat) (hj : j < (repChars.getD 65 []).length)
    (hq : (normIsRep.getD 65 []).getD j false = true) :
    species (Q2.reps (⟨40, by decide⟩ : Fin 148)) (colE2 ⟨40, by decide⟩ 0 hp)
        (rowE2 (⟨65, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨40, by decide⟩ : Fin 148))
        (colE1 ⟨40, by decide⟩ 0 (transLenTr ⟨40, by decide⟩ 0 hp))
        (rowE1 (⟨65, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨65, by decide⟩ : Fin 148) ⟨40, by decide⟩ _
      (validAt ⟨65, by decide⟩ (listedAt ⟨65, by decide⟩ hj))
      (colE1 ⟨40, by decide⟩ 0 (transLenTr ⟨40, by decide⟩ 0 hp)) T65_40
      hfix65_40 hinj65_40 hcardT65_40
      (fun i => conj_mem_of_fixedPoints _ _ (T65_40 i) (hfix65_40 i) _)
      ⟨65, by decide⟩ ⟨40, by decide⟩ _
      (Q2.validAt ⟨65, by decide⟩ (Q2.listedAt ⟨65, by decide⟩
        (alnCheck_rep ⟨65, by decide⟩ hj hq).1))
      (colE2 ⟨40, by decide⟩ 0 hp) Q2.T65_40_2 Q2.hfix65_40_2 Q2.hinj65_40_2
      Q2.hcardT65_40_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T65_40_2 i) (Q2.hfix65_40_2 i) _)
      colCert_65_40_0.hD ?_).symm
  rw [alnId_65 j hj]


theorem leaf_65_40_1 (hp : 1 < (Q2.transData.getD 40 []).length)
    (j : Nat) (hj : j < (repChars.getD 65 []).length)
    (hq : (normIsRep.getD 65 []).getD j false = true) :
    species (Q2.reps (⟨40, by decide⟩ : Fin 148)) (colE2 ⟨40, by decide⟩ 1 hp)
        (rowE2 (⟨65, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨40, by decide⟩ : Fin 148))
        (colE1 ⟨40, by decide⟩ 1 (transLenTr ⟨40, by decide⟩ 1 hp))
        (rowE1 (⟨65, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨65, by decide⟩ : Fin 148) ⟨40, by decide⟩ _
      (validAt ⟨65, by decide⟩ (listedAt ⟨65, by decide⟩ hj))
      (colE1 ⟨40, by decide⟩ 1 (transLenTr ⟨40, by decide⟩ 1 hp)) T65_40
      hfix65_40 hinj65_40 hcardT65_40
      (fun i => conj_mem_of_fixedPoints _ _ (T65_40 i) (hfix65_40 i) _)
      ⟨65, by decide⟩ ⟨40, by decide⟩ _
      (Q2.validAt ⟨65, by decide⟩ (Q2.listedAt ⟨65, by decide⟩
        (alnCheck_rep ⟨65, by decide⟩ hj hq).1))
      (colE2 ⟨40, by decide⟩ 1 hp) Q2.T65_40_2 Q2.hfix65_40_2 Q2.hinj65_40_2
      Q2.hcardT65_40_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T65_40_2 i) (Q2.hfix65_40_2 i) _)
      colCert_65_40_1.hD ?_).symm
  rw [alnId_65 j hj]


theorem leaf_65_40_2 (hp : 2 < (Q2.transData.getD 40 []).length)
    (j : Nat) (hj : j < (repChars.getD 65 []).length)
    (hq : (normIsRep.getD 65 []).getD j false = true) :
    species (Q2.reps (⟨40, by decide⟩ : Fin 148)) (colE2 ⟨40, by decide⟩ 2 hp)
        (rowE2 (⟨65, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨40, by decide⟩ : Fin 148))
        (colE1 ⟨40, by decide⟩ 2 (transLenTr ⟨40, by decide⟩ 2 hp))
        (rowE1 (⟨65, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨65, by decide⟩ : Fin 148) ⟨40, by decide⟩ _
      (validAt ⟨65, by decide⟩ (listedAt ⟨65, by decide⟩ hj))
      (colE1 ⟨40, by decide⟩ 2 (transLenTr ⟨40, by decide⟩ 2 hp)) T65_40
      hfix65_40 hinj65_40 hcardT65_40
      (fun i => conj_mem_of_fixedPoints _ _ (T65_40 i) (hfix65_40 i) _)
      ⟨65, by decide⟩ ⟨40, by decide⟩ _
      (Q2.validAt ⟨65, by decide⟩ (Q2.listedAt ⟨65, by decide⟩
        (alnCheck_rep ⟨65, by decide⟩ hj hq).1))
      (colE2 ⟨40, by decide⟩ 2 hp) Q2.T65_40_2 Q2.hfix65_40_2 Q2.hinj65_40_2
      Q2.hcardT65_40_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T65_40_2 i) (Q2.hfix65_40_2 i) _)
      colCert_65_40_2.hD ?_).symm
  rw [alnId_65 j hj]


theorem leaf_65_40_3 (hp : 3 < (Q2.transData.getD 40 []).length)
    (j : Nat) (hj : j < (repChars.getD 65 []).length)
    (hq : (normIsRep.getD 65 []).getD j false = true) :
    species (Q2.reps (⟨40, by decide⟩ : Fin 148)) (colE2 ⟨40, by decide⟩ 3 hp)
        (rowE2 (⟨65, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨40, by decide⟩ : Fin 148))
        (colE1 ⟨40, by decide⟩ 3 (transLenTr ⟨40, by decide⟩ 3 hp))
        (rowE1 (⟨65, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨65, by decide⟩ : Fin 148) ⟨40, by decide⟩ _
      (validAt ⟨65, by decide⟩ (listedAt ⟨65, by decide⟩ hj))
      (colE1 ⟨40, by decide⟩ 3 (transLenTr ⟨40, by decide⟩ 3 hp)) T65_40
      hfix65_40 hinj65_40 hcardT65_40
      (fun i => conj_mem_of_fixedPoints _ _ (T65_40 i) (hfix65_40 i) _)
      ⟨65, by decide⟩ ⟨40, by decide⟩ _
      (Q2.validAt ⟨65, by decide⟩ (Q2.listedAt ⟨65, by decide⟩
        (alnCheck_rep ⟨65, by decide⟩ hj hq).1))
      (colE2 ⟨40, by decide⟩ 3 hp) Q2.T65_40_2 Q2.hfix65_40_2 Q2.hinj65_40_2
      Q2.hcardT65_40_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T65_40_2 i) (Q2.hfix65_40_2 i) _)
      colCert_65_40_3.hD ?_).symm
  rw [alnId_65 j hj]


theorem leaf_65_40_4 (hp : 4 < (Q2.transData.getD 40 []).length)
    (j : Nat) (hj : j < (repChars.getD 65 []).length)
    (hq : (normIsRep.getD 65 []).getD j false = true) :
    species (Q2.reps (⟨40, by decide⟩ : Fin 148)) (colE2 ⟨40, by decide⟩ 4 hp)
        (rowE2 (⟨65, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨40, by decide⟩ : Fin 148))
        (colE1 ⟨40, by decide⟩ 4 (transLenTr ⟨40, by decide⟩ 4 hp))
        (rowE1 (⟨65, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨65, by decide⟩ : Fin 148) ⟨40, by decide⟩ _
      (validAt ⟨65, by decide⟩ (listedAt ⟨65, by decide⟩ hj))
      (colE1 ⟨40, by decide⟩ 4 (transLenTr ⟨40, by decide⟩ 4 hp)) T65_40
      hfix65_40 hinj65_40 hcardT65_40
      (fun i => conj_mem_of_fixedPoints _ _ (T65_40 i) (hfix65_40 i) _)
      ⟨65, by decide⟩ ⟨40, by decide⟩ _
      (Q2.validAt ⟨65, by decide⟩ (Q2.listedAt ⟨65, by decide⟩
        (alnCheck_rep ⟨65, by decide⟩ hj hq).1))
      (colE2 ⟨40, by decide⟩ 4 hp) Q2.T65_40_2 Q2.hfix65_40_2 Q2.hinj65_40_2
      Q2.hcardT65_40_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T65_40_2 i) (Q2.hfix65_40_2 i) _)
      colCert_65_40_4.hD ?_).symm
  rw [alnId_65 j hj]


theorem leaf_65_40_5 (hp : 5 < (Q2.transData.getD 40 []).length)
    (j : Nat) (hj : j < (repChars.getD 65 []).length)
    (hq : (normIsRep.getD 65 []).getD j false = true) :
    species (Q2.reps (⟨40, by decide⟩ : Fin 148)) (colE2 ⟨40, by decide⟩ 5 hp)
        (rowE2 (⟨65, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨40, by decide⟩ : Fin 148))
        (colE1 ⟨40, by decide⟩ 5 (transLenTr ⟨40, by decide⟩ 5 hp))
        (rowE1 (⟨65, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨65, by decide⟩ : Fin 148) ⟨40, by decide⟩ _
      (validAt ⟨65, by decide⟩ (listedAt ⟨65, by decide⟩ hj))
      (colE1 ⟨40, by decide⟩ 5 (transLenTr ⟨40, by decide⟩ 5 hp)) T65_40
      hfix65_40 hinj65_40 hcardT65_40
      (fun i => conj_mem_of_fixedPoints _ _ (T65_40 i) (hfix65_40 i) _)
      ⟨65, by decide⟩ ⟨40, by decide⟩ _
      (Q2.validAt ⟨65, by decide⟩ (Q2.listedAt ⟨65, by decide⟩
        (alnCheck_rep ⟨65, by decide⟩ hj hq).1))
      (colE2 ⟨40, by decide⟩ 5 hp) Q2.T65_40_2 Q2.hfix65_40_2 Q2.hinj65_40_2
      Q2.hcardT65_40_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T65_40_2 i) (Q2.hfix65_40_2 i) _)
      colCert_65_40_5.hD ?_).symm
  rw [alnId_65 j hj]


theorem leaf_65_40_10 (hp : 10 < (Q2.transData.getD 40 []).length)
    (j : Nat) (hj : j < (repChars.getD 65 []).length)
    (hq : (normIsRep.getD 65 []).getD j false = true) :
    species (Q2.reps (⟨40, by decide⟩ : Fin 148)) (colE2 ⟨40, by decide⟩ 10 hp)
        (rowE2 (⟨65, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨40, by decide⟩ : Fin 148))
        (colE1 ⟨40, by decide⟩ 10 (transLenTr ⟨40, by decide⟩ 10 hp))
        (rowE1 (⟨65, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨65, by decide⟩ : Fin 148) ⟨40, by decide⟩ _
      (validAt ⟨65, by decide⟩ (listedAt ⟨65, by decide⟩ hj))
      (colE1 ⟨40, by decide⟩ 10 (transLenTr ⟨40, by decide⟩ 10 hp)) T65_40
      hfix65_40 hinj65_40 hcardT65_40
      (fun i => conj_mem_of_fixedPoints _ _ (T65_40 i) (hfix65_40 i) _)
      ⟨65, by decide⟩ ⟨40, by decide⟩ _
      (Q2.validAt ⟨65, by decide⟩ (Q2.listedAt ⟨65, by decide⟩
        (alnCheck_rep ⟨65, by decide⟩ hj hq).1))
      (colE2 ⟨40, by decide⟩ 10 hp) Q2.T65_40_2 Q2.hfix65_40_2 Q2.hinj65_40_2
      Q2.hcardT65_40_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T65_40_2 i) (Q2.hfix65_40_2 i) _)
      colCert_65_40_10.hD ?_).symm
  rw [alnId_65 j hj]


theorem leaf_65_40_15 (hp : 15 < (Q2.transData.getD 40 []).length)
    (j : Nat) (hj : j < (repChars.getD 65 []).length)
    (hq : (normIsRep.getD 65 []).getD j false = true) :
    species (Q2.reps (⟨40, by decide⟩ : Fin 148)) (colE2 ⟨40, by decide⟩ 15 hp)
        (rowE2 (⟨65, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨40, by decide⟩ : Fin 148))
        (colE1 ⟨40, by decide⟩ 15 (transLenTr ⟨40, by decide⟩ 15 hp))
        (rowE1 (⟨65, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨65, by decide⟩ : Fin 148) ⟨40, by decide⟩ _
      (validAt ⟨65, by decide⟩ (listedAt ⟨65, by decide⟩ hj))
      (colE1 ⟨40, by decide⟩ 15 (transLenTr ⟨40, by decide⟩ 15 hp)) T65_40
      hfix65_40 hinj65_40 hcardT65_40
      (fun i => conj_mem_of_fixedPoints _ _ (T65_40 i) (hfix65_40 i) _)
      ⟨65, by decide⟩ ⟨40, by decide⟩ _
      (Q2.validAt ⟨65, by decide⟩ (Q2.listedAt ⟨65, by decide⟩
        (alnCheck_rep ⟨65, by decide⟩ hj hq).1))
      (colE2 ⟨40, by decide⟩ 15 hp) Q2.T65_40_2 Q2.hfix65_40_2 Q2.hinj65_40_2
      Q2.hcardT65_40_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T65_40_2 i) (Q2.hfix65_40_2 i) _)
      colCert_65_40_15.hD ?_).symm
  rw [alnId_65 j hj]


theorem leaf_65_40_20 (hp : 20 < (Q2.transData.getD 40 []).length)
    (j : Nat) (hj : j < (repChars.getD 65 []).length)
    (hq : (normIsRep.getD 65 []).getD j false = true) :
    species (Q2.reps (⟨40, by decide⟩ : Fin 148)) (colE2 ⟨40, by decide⟩ 20 hp)
        (rowE2 (⟨65, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨40, by decide⟩ : Fin 148))
        (colE1 ⟨40, by decide⟩ 20 (transLenTr ⟨40, by decide⟩ 20 hp))
        (rowE1 (⟨65, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨65, by decide⟩ : Fin 148) ⟨40, by decide⟩ _
      (validAt ⟨65, by decide⟩ (listedAt ⟨65, by decide⟩ hj))
      (colE1 ⟨40, by decide⟩ 20 (transLenTr ⟨40, by decide⟩ 20 hp)) T65_40
      hfix65_40 hinj65_40 hcardT65_40
      (fun i => conj_mem_of_fixedPoints _ _ (T65_40 i) (hfix65_40 i) _)
      ⟨65, by decide⟩ ⟨40, by decide⟩ _
      (Q2.validAt ⟨65, by decide⟩ (Q2.listedAt ⟨65, by decide⟩
        (alnCheck_rep ⟨65, by decide⟩ hj hq).1))
      (colE2 ⟨40, by decide⟩ 20 hp) Q2.T65_40_2 Q2.hfix65_40_2 Q2.hinj65_40_2
      Q2.hcardT65_40_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T65_40_2 i) (Q2.hfix65_40_2 i) _)
      colCert_65_40_20.hD ?_).symm
  rw [alnId_65 j hj]


theorem leaf_65_45_0 (hp : 0 < (Q2.transData.getD 45 []).length)
    (j : Nat) (hj : j < (repChars.getD 65 []).length)
    (hq : (normIsRep.getD 65 []).getD j false = true) :
    species (Q2.reps (⟨45, by decide⟩ : Fin 148)) (colE2 ⟨45, by decide⟩ 0 hp)
        (rowE2 (⟨65, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨45, by decide⟩ : Fin 148))
        (colE1 ⟨45, by decide⟩ 0 (transLenTr ⟨45, by decide⟩ 0 hp))
        (rowE1 (⟨65, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨65, by decide⟩ : Fin 148) ⟨45, by decide⟩ _
      (validAt ⟨65, by decide⟩ (listedAt ⟨65, by decide⟩ hj))
      (colE1 ⟨45, by decide⟩ 0 (transLenTr ⟨45, by decide⟩ 0 hp)) T65_45
      hfix65_45 hinj65_45 hcardT65_45
      (fun i => conj_mem_of_fixedPoints _ _ (T65_45 i) (hfix65_45 i) _)
      ⟨65, by decide⟩ ⟨45, by decide⟩ _
      (Q2.validAt ⟨65, by decide⟩ (Q2.listedAt ⟨65, by decide⟩
        (alnCheck_rep ⟨65, by decide⟩ hj hq).1))
      (colE2 ⟨45, by decide⟩ 0 hp) Q2.T65_45_2 Q2.hfix65_45_2 Q2.hinj65_45_2
      Q2.hcardT65_45_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T65_45_2 i) (Q2.hfix65_45_2 i) _)
      colCert_65_45_0.hD ?_).symm
  rw [alnId_65 j hj]


theorem leaf_65_45_1 (hp : 1 < (Q2.transData.getD 45 []).length)
    (j : Nat) (hj : j < (repChars.getD 65 []).length)
    (hq : (normIsRep.getD 65 []).getD j false = true) :
    species (Q2.reps (⟨45, by decide⟩ : Fin 148)) (colE2 ⟨45, by decide⟩ 1 hp)
        (rowE2 (⟨65, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨45, by decide⟩ : Fin 148))
        (colE1 ⟨45, by decide⟩ 1 (transLenTr ⟨45, by decide⟩ 1 hp))
        (rowE1 (⟨65, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨65, by decide⟩ : Fin 148) ⟨45, by decide⟩ _
      (validAt ⟨65, by decide⟩ (listedAt ⟨65, by decide⟩ hj))
      (colE1 ⟨45, by decide⟩ 1 (transLenTr ⟨45, by decide⟩ 1 hp)) T65_45
      hfix65_45 hinj65_45 hcardT65_45
      (fun i => conj_mem_of_fixedPoints _ _ (T65_45 i) (hfix65_45 i) _)
      ⟨65, by decide⟩ ⟨45, by decide⟩ _
      (Q2.validAt ⟨65, by decide⟩ (Q2.listedAt ⟨65, by decide⟩
        (alnCheck_rep ⟨65, by decide⟩ hj hq).1))
      (colE2 ⟨45, by decide⟩ 1 hp) Q2.T65_45_2 Q2.hfix65_45_2 Q2.hinj65_45_2
      Q2.hcardT65_45_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T65_45_2 i) (Q2.hfix65_45_2 i) _)
      colCert_65_45_1.hD ?_).symm
  rw [alnId_65 j hj]


theorem leaf_65_45_2 (hp : 2 < (Q2.transData.getD 45 []).length)
    (j : Nat) (hj : j < (repChars.getD 65 []).length)
    (hq : (normIsRep.getD 65 []).getD j false = true) :
    species (Q2.reps (⟨45, by decide⟩ : Fin 148)) (colE2 ⟨45, by decide⟩ 2 hp)
        (rowE2 (⟨65, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨45, by decide⟩ : Fin 148))
        (colE1 ⟨45, by decide⟩ 2 (transLenTr ⟨45, by decide⟩ 2 hp))
        (rowE1 (⟨65, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨65, by decide⟩ : Fin 148) ⟨45, by decide⟩ _
      (validAt ⟨65, by decide⟩ (listedAt ⟨65, by decide⟩ hj))
      (colE1 ⟨45, by decide⟩ 2 (transLenTr ⟨45, by decide⟩ 2 hp)) T65_45
      hfix65_45 hinj65_45 hcardT65_45
      (fun i => conj_mem_of_fixedPoints _ _ (T65_45 i) (hfix65_45 i) _)
      ⟨65, by decide⟩ ⟨45, by decide⟩ _
      (Q2.validAt ⟨65, by decide⟩ (Q2.listedAt ⟨65, by decide⟩
        (alnCheck_rep ⟨65, by decide⟩ hj hq).1))
      (colE2 ⟨45, by decide⟩ 2 hp) Q2.T65_45_2 Q2.hfix65_45_2 Q2.hinj65_45_2
      Q2.hcardT65_45_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T65_45_2 i) (Q2.hfix65_45_2 i) _)
      colCert_65_45_2.hD ?_).symm
  rw [alnId_65 j hj]


theorem leaf_65_45_3 (hp : 3 < (Q2.transData.getD 45 []).length)
    (j : Nat) (hj : j < (repChars.getD 65 []).length)
    (hq : (normIsRep.getD 65 []).getD j false = true) :
    species (Q2.reps (⟨45, by decide⟩ : Fin 148)) (colE2 ⟨45, by decide⟩ 3 hp)
        (rowE2 (⟨65, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨45, by decide⟩ : Fin 148))
        (colE1 ⟨45, by decide⟩ 3 (transLenTr ⟨45, by decide⟩ 3 hp))
        (rowE1 (⟨65, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨65, by decide⟩ : Fin 148) ⟨45, by decide⟩ _
      (validAt ⟨65, by decide⟩ (listedAt ⟨65, by decide⟩ hj))
      (colE1 ⟨45, by decide⟩ 3 (transLenTr ⟨45, by decide⟩ 3 hp)) T65_45
      hfix65_45 hinj65_45 hcardT65_45
      (fun i => conj_mem_of_fixedPoints _ _ (T65_45 i) (hfix65_45 i) _)
      ⟨65, by decide⟩ ⟨45, by decide⟩ _
      (Q2.validAt ⟨65, by decide⟩ (Q2.listedAt ⟨65, by decide⟩
        (alnCheck_rep ⟨65, by decide⟩ hj hq).1))
      (colE2 ⟨45, by decide⟩ 3 hp) Q2.T65_45_2 Q2.hfix65_45_2 Q2.hinj65_45_2
      Q2.hcardT65_45_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T65_45_2 i) (Q2.hfix65_45_2 i) _)
      colCert_65_45_3.hD ?_).symm
  rw [alnId_65 j hj]


theorem leaf_65_45_4 (hp : 4 < (Q2.transData.getD 45 []).length)
    (j : Nat) (hj : j < (repChars.getD 65 []).length)
    (hq : (normIsRep.getD 65 []).getD j false = true) :
    species (Q2.reps (⟨45, by decide⟩ : Fin 148)) (colE2 ⟨45, by decide⟩ 4 hp)
        (rowE2 (⟨65, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨45, by decide⟩ : Fin 148))
        (colE1 ⟨45, by decide⟩ 4 (transLenTr ⟨45, by decide⟩ 4 hp))
        (rowE1 (⟨65, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨65, by decide⟩ : Fin 148) ⟨45, by decide⟩ _
      (validAt ⟨65, by decide⟩ (listedAt ⟨65, by decide⟩ hj))
      (colE1 ⟨45, by decide⟩ 4 (transLenTr ⟨45, by decide⟩ 4 hp)) T65_45
      hfix65_45 hinj65_45 hcardT65_45
      (fun i => conj_mem_of_fixedPoints _ _ (T65_45 i) (hfix65_45 i) _)
      ⟨65, by decide⟩ ⟨45, by decide⟩ _
      (Q2.validAt ⟨65, by decide⟩ (Q2.listedAt ⟨65, by decide⟩
        (alnCheck_rep ⟨65, by decide⟩ hj hq).1))
      (colE2 ⟨45, by decide⟩ 4 hp) Q2.T65_45_2 Q2.hfix65_45_2 Q2.hinj65_45_2
      Q2.hcardT65_45_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T65_45_2 i) (Q2.hfix65_45_2 i) _)
      colCert_65_45_4.hD ?_).symm
  rw [alnId_65 j hj]


theorem leaf_65_45_5 (hp : 5 < (Q2.transData.getD 45 []).length)
    (j : Nat) (hj : j < (repChars.getD 65 []).length)
    (hq : (normIsRep.getD 65 []).getD j false = true) :
    species (Q2.reps (⟨45, by decide⟩ : Fin 148)) (colE2 ⟨45, by decide⟩ 5 hp)
        (rowE2 (⟨65, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨45, by decide⟩ : Fin 148))
        (colE1 ⟨45, by decide⟩ 5 (transLenTr ⟨45, by decide⟩ 5 hp))
        (rowE1 (⟨65, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨65, by decide⟩ : Fin 148) ⟨45, by decide⟩ _
      (validAt ⟨65, by decide⟩ (listedAt ⟨65, by decide⟩ hj))
      (colE1 ⟨45, by decide⟩ 5 (transLenTr ⟨45, by decide⟩ 5 hp)) T65_45
      hfix65_45 hinj65_45 hcardT65_45
      (fun i => conj_mem_of_fixedPoints _ _ (T65_45 i) (hfix65_45 i) _)
      ⟨65, by decide⟩ ⟨45, by decide⟩ _
      (Q2.validAt ⟨65, by decide⟩ (Q2.listedAt ⟨65, by decide⟩
        (alnCheck_rep ⟨65, by decide⟩ hj hq).1))
      (colE2 ⟨45, by decide⟩ 5 hp) Q2.T65_45_2 Q2.hfix65_45_2 Q2.hinj65_45_2
      Q2.hcardT65_45_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T65_45_2 i) (Q2.hfix65_45_2 i) _)
      colCert_65_45_5.hD ?_).symm
  rw [alnId_65 j hj]


theorem leaf_65_45_10 (hp : 10 < (Q2.transData.getD 45 []).length)
    (j : Nat) (hj : j < (repChars.getD 65 []).length)
    (hq : (normIsRep.getD 65 []).getD j false = true) :
    species (Q2.reps (⟨45, by decide⟩ : Fin 148)) (colE2 ⟨45, by decide⟩ 10 hp)
        (rowE2 (⟨65, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨45, by decide⟩ : Fin 148))
        (colE1 ⟨45, by decide⟩ 10 (transLenTr ⟨45, by decide⟩ 10 hp))
        (rowE1 (⟨65, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨65, by decide⟩ : Fin 148) ⟨45, by decide⟩ _
      (validAt ⟨65, by decide⟩ (listedAt ⟨65, by decide⟩ hj))
      (colE1 ⟨45, by decide⟩ 10 (transLenTr ⟨45, by decide⟩ 10 hp)) T65_45
      hfix65_45 hinj65_45 hcardT65_45
      (fun i => conj_mem_of_fixedPoints _ _ (T65_45 i) (hfix65_45 i) _)
      ⟨65, by decide⟩ ⟨45, by decide⟩ _
      (Q2.validAt ⟨65, by decide⟩ (Q2.listedAt ⟨65, by decide⟩
        (alnCheck_rep ⟨65, by decide⟩ hj hq).1))
      (colE2 ⟨45, by decide⟩ 10 hp) Q2.T65_45_2 Q2.hfix65_45_2 Q2.hinj65_45_2
      Q2.hcardT65_45_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T65_45_2 i) (Q2.hfix65_45_2 i) _)
      colCert_65_45_10.hD ?_).symm
  rw [alnId_65 j hj]


theorem leaf_65_45_15 (hp : 15 < (Q2.transData.getD 45 []).length)
    (j : Nat) (hj : j < (repChars.getD 65 []).length)
    (hq : (normIsRep.getD 65 []).getD j false = true) :
    species (Q2.reps (⟨45, by decide⟩ : Fin 148)) (colE2 ⟨45, by decide⟩ 15 hp)
        (rowE2 (⟨65, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨45, by decide⟩ : Fin 148))
        (colE1 ⟨45, by decide⟩ 15 (transLenTr ⟨45, by decide⟩ 15 hp))
        (rowE1 (⟨65, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨65, by decide⟩ : Fin 148) ⟨45, by decide⟩ _
      (validAt ⟨65, by decide⟩ (listedAt ⟨65, by decide⟩ hj))
      (colE1 ⟨45, by decide⟩ 15 (transLenTr ⟨45, by decide⟩ 15 hp)) T65_45
      hfix65_45 hinj65_45 hcardT65_45
      (fun i => conj_mem_of_fixedPoints _ _ (T65_45 i) (hfix65_45 i) _)
      ⟨65, by decide⟩ ⟨45, by decide⟩ _
      (Q2.validAt ⟨65, by decide⟩ (Q2.listedAt ⟨65, by decide⟩
        (alnCheck_rep ⟨65, by decide⟩ hj hq).1))
      (colE2 ⟨45, by decide⟩ 15 hp) Q2.T65_45_2 Q2.hfix65_45_2 Q2.hinj65_45_2
      Q2.hcardT65_45_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T65_45_2 i) (Q2.hfix65_45_2 i) _)
      colCert_65_45_15.hD ?_).symm
  rw [alnId_65 j hj]


theorem leaf_65_45_20 (hp : 20 < (Q2.transData.getD 45 []).length)
    (j : Nat) (hj : j < (repChars.getD 65 []).length)
    (hq : (normIsRep.getD 65 []).getD j false = true) :
    species (Q2.reps (⟨45, by decide⟩ : Fin 148)) (colE2 ⟨45, by decide⟩ 20 hp)
        (rowE2 (⟨65, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨45, by decide⟩ : Fin 148))
        (colE1 ⟨45, by decide⟩ 20 (transLenTr ⟨45, by decide⟩ 20 hp))
        (rowE1 (⟨65, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨65, by decide⟩ : Fin 148) ⟨45, by decide⟩ _
      (validAt ⟨65, by decide⟩ (listedAt ⟨65, by decide⟩ hj))
      (colE1 ⟨45, by decide⟩ 20 (transLenTr ⟨45, by decide⟩ 20 hp)) T65_45
      hfix65_45 hinj65_45 hcardT65_45
      (fun i => conj_mem_of_fixedPoints _ _ (T65_45 i) (hfix65_45 i) _)
      ⟨65, by decide⟩ ⟨45, by decide⟩ _
      (Q2.validAt ⟨65, by decide⟩ (Q2.listedAt ⟨65, by decide⟩
        (alnCheck_rep ⟨65, by decide⟩ hj hq).1))
      (colE2 ⟨45, by decide⟩ 20 hp) Q2.T65_45_2 Q2.hfix65_45_2 Q2.hinj65_45_2
      Q2.hcardT65_45_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T65_45_2 i) (Q2.hfix65_45_2 i) _)
      colCert_65_45_20.hD ?_).symm
  rw [alnId_65 j hj]


theorem leaf_65_50_0 (hp : 0 < (Q2.transData.getD 50 []).length)
    (j : Nat) (hj : j < (repChars.getD 65 []).length)
    (hq : (normIsRep.getD 65 []).getD j false = true) :
    species (Q2.reps (⟨50, by decide⟩ : Fin 148)) (colE2 ⟨50, by decide⟩ 0 hp)
        (rowE2 (⟨65, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨50, by decide⟩ : Fin 148))
        (colE1 ⟨50, by decide⟩ 0 (transLenTr ⟨50, by decide⟩ 0 hp))
        (rowE1 (⟨65, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨65, by decide⟩ : Fin 148) ⟨50, by decide⟩ _
      (validAt ⟨65, by decide⟩ (listedAt ⟨65, by decide⟩ hj))
      (colE1 ⟨50, by decide⟩ 0 (transLenTr ⟨50, by decide⟩ 0 hp)) T65_50
      hfix65_50 hinj65_50 hcardT65_50
      (fun i => conj_mem_of_fixedPoints _ _ (T65_50 i) (hfix65_50 i) _)
      ⟨65, by decide⟩ ⟨50, by decide⟩ _
      (Q2.validAt ⟨65, by decide⟩ (Q2.listedAt ⟨65, by decide⟩
        (alnCheck_rep ⟨65, by decide⟩ hj hq).1))
      (colE2 ⟨50, by decide⟩ 0 hp) Q2.T65_50_2 Q2.hfix65_50_2 Q2.hinj65_50_2
      Q2.hcardT65_50_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T65_50_2 i) (Q2.hfix65_50_2 i) _)
      colCert_65_50_0.hD ?_).symm
  rw [alnId_65 j hj]


theorem leaf_65_50_1 (hp : 1 < (Q2.transData.getD 50 []).length)
    (j : Nat) (hj : j < (repChars.getD 65 []).length)
    (hq : (normIsRep.getD 65 []).getD j false = true) :
    species (Q2.reps (⟨50, by decide⟩ : Fin 148)) (colE2 ⟨50, by decide⟩ 1 hp)
        (rowE2 (⟨65, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨50, by decide⟩ : Fin 148))
        (colE1 ⟨50, by decide⟩ 1 (transLenTr ⟨50, by decide⟩ 1 hp))
        (rowE1 (⟨65, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨65, by decide⟩ : Fin 148) ⟨50, by decide⟩ _
      (validAt ⟨65, by decide⟩ (listedAt ⟨65, by decide⟩ hj))
      (colE1 ⟨50, by decide⟩ 1 (transLenTr ⟨50, by decide⟩ 1 hp)) T65_50
      hfix65_50 hinj65_50 hcardT65_50
      (fun i => conj_mem_of_fixedPoints _ _ (T65_50 i) (hfix65_50 i) _)
      ⟨65, by decide⟩ ⟨50, by decide⟩ _
      (Q2.validAt ⟨65, by decide⟩ (Q2.listedAt ⟨65, by decide⟩
        (alnCheck_rep ⟨65, by decide⟩ hj hq).1))
      (colE2 ⟨50, by decide⟩ 1 hp) Q2.T65_50_2 Q2.hfix65_50_2 Q2.hinj65_50_2
      Q2.hcardT65_50_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T65_50_2 i) (Q2.hfix65_50_2 i) _)
      colCert_65_50_1.hD ?_).symm
  rw [alnId_65 j hj]


theorem leaf_65_50_2 (hp : 2 < (Q2.transData.getD 50 []).length)
    (j : Nat) (hj : j < (repChars.getD 65 []).length)
    (hq : (normIsRep.getD 65 []).getD j false = true) :
    species (Q2.reps (⟨50, by decide⟩ : Fin 148)) (colE2 ⟨50, by decide⟩ 2 hp)
        (rowE2 (⟨65, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨50, by decide⟩ : Fin 148))
        (colE1 ⟨50, by decide⟩ 2 (transLenTr ⟨50, by decide⟩ 2 hp))
        (rowE1 (⟨65, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨65, by decide⟩ : Fin 148) ⟨50, by decide⟩ _
      (validAt ⟨65, by decide⟩ (listedAt ⟨65, by decide⟩ hj))
      (colE1 ⟨50, by decide⟩ 2 (transLenTr ⟨50, by decide⟩ 2 hp)) T65_50
      hfix65_50 hinj65_50 hcardT65_50
      (fun i => conj_mem_of_fixedPoints _ _ (T65_50 i) (hfix65_50 i) _)
      ⟨65, by decide⟩ ⟨50, by decide⟩ _
      (Q2.validAt ⟨65, by decide⟩ (Q2.listedAt ⟨65, by decide⟩
        (alnCheck_rep ⟨65, by decide⟩ hj hq).1))
      (colE2 ⟨50, by decide⟩ 2 hp) Q2.T65_50_2 Q2.hfix65_50_2 Q2.hinj65_50_2
      Q2.hcardT65_50_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T65_50_2 i) (Q2.hfix65_50_2 i) _)
      colCert_65_50_2.hD ?_).symm
  rw [alnId_65 j hj]


theorem leaf_65_50_3 (hp : 3 < (Q2.transData.getD 50 []).length)
    (j : Nat) (hj : j < (repChars.getD 65 []).length)
    (hq : (normIsRep.getD 65 []).getD j false = true) :
    species (Q2.reps (⟨50, by decide⟩ : Fin 148)) (colE2 ⟨50, by decide⟩ 3 hp)
        (rowE2 (⟨65, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨50, by decide⟩ : Fin 148))
        (colE1 ⟨50, by decide⟩ 3 (transLenTr ⟨50, by decide⟩ 3 hp))
        (rowE1 (⟨65, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨65, by decide⟩ : Fin 148) ⟨50, by decide⟩ _
      (validAt ⟨65, by decide⟩ (listedAt ⟨65, by decide⟩ hj))
      (colE1 ⟨50, by decide⟩ 3 (transLenTr ⟨50, by decide⟩ 3 hp)) T65_50
      hfix65_50 hinj65_50 hcardT65_50
      (fun i => conj_mem_of_fixedPoints _ _ (T65_50 i) (hfix65_50 i) _)
      ⟨65, by decide⟩ ⟨50, by decide⟩ _
      (Q2.validAt ⟨65, by decide⟩ (Q2.listedAt ⟨65, by decide⟩
        (alnCheck_rep ⟨65, by decide⟩ hj hq).1))
      (colE2 ⟨50, by decide⟩ 3 hp) Q2.T65_50_2 Q2.hfix65_50_2 Q2.hinj65_50_2
      Q2.hcardT65_50_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T65_50_2 i) (Q2.hfix65_50_2 i) _)
      colCert_65_50_3.hD ?_).symm
  rw [alnId_65 j hj]


theorem leaf_65_50_4 (hp : 4 < (Q2.transData.getD 50 []).length)
    (j : Nat) (hj : j < (repChars.getD 65 []).length)
    (hq : (normIsRep.getD 65 []).getD j false = true) :
    species (Q2.reps (⟨50, by decide⟩ : Fin 148)) (colE2 ⟨50, by decide⟩ 4 hp)
        (rowE2 (⟨65, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨50, by decide⟩ : Fin 148))
        (colE1 ⟨50, by decide⟩ 4 (transLenTr ⟨50, by decide⟩ 4 hp))
        (rowE1 (⟨65, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨65, by decide⟩ : Fin 148) ⟨50, by decide⟩ _
      (validAt ⟨65, by decide⟩ (listedAt ⟨65, by decide⟩ hj))
      (colE1 ⟨50, by decide⟩ 4 (transLenTr ⟨50, by decide⟩ 4 hp)) T65_50
      hfix65_50 hinj65_50 hcardT65_50
      (fun i => conj_mem_of_fixedPoints _ _ (T65_50 i) (hfix65_50 i) _)
      ⟨65, by decide⟩ ⟨50, by decide⟩ _
      (Q2.validAt ⟨65, by decide⟩ (Q2.listedAt ⟨65, by decide⟩
        (alnCheck_rep ⟨65, by decide⟩ hj hq).1))
      (colE2 ⟨50, by decide⟩ 4 hp) Q2.T65_50_2 Q2.hfix65_50_2 Q2.hinj65_50_2
      Q2.hcardT65_50_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T65_50_2 i) (Q2.hfix65_50_2 i) _)
      colCert_65_50_4.hD ?_).symm
  rw [alnId_65 j hj]


theorem leaf_65_50_5 (hp : 5 < (Q2.transData.getD 50 []).length)
    (j : Nat) (hj : j < (repChars.getD 65 []).length)
    (hq : (normIsRep.getD 65 []).getD j false = true) :
    species (Q2.reps (⟨50, by decide⟩ : Fin 148)) (colE2 ⟨50, by decide⟩ 5 hp)
        (rowE2 (⟨65, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨50, by decide⟩ : Fin 148))
        (colE1 ⟨50, by decide⟩ 5 (transLenTr ⟨50, by decide⟩ 5 hp))
        (rowE1 (⟨65, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨65, by decide⟩ : Fin 148) ⟨50, by decide⟩ _
      (validAt ⟨65, by decide⟩ (listedAt ⟨65, by decide⟩ hj))
      (colE1 ⟨50, by decide⟩ 5 (transLenTr ⟨50, by decide⟩ 5 hp)) T65_50
      hfix65_50 hinj65_50 hcardT65_50
      (fun i => conj_mem_of_fixedPoints _ _ (T65_50 i) (hfix65_50 i) _)
      ⟨65, by decide⟩ ⟨50, by decide⟩ _
      (Q2.validAt ⟨65, by decide⟩ (Q2.listedAt ⟨65, by decide⟩
        (alnCheck_rep ⟨65, by decide⟩ hj hq).1))
      (colE2 ⟨50, by decide⟩ 5 hp) Q2.T65_50_2 Q2.hfix65_50_2 Q2.hinj65_50_2
      Q2.hcardT65_50_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T65_50_2 i) (Q2.hfix65_50_2 i) _)
      colCert_65_50_5.hD ?_).symm
  rw [alnId_65 j hj]


theorem leaf_65_50_10 (hp : 10 < (Q2.transData.getD 50 []).length)
    (j : Nat) (hj : j < (repChars.getD 65 []).length)
    (hq : (normIsRep.getD 65 []).getD j false = true) :
    species (Q2.reps (⟨50, by decide⟩ : Fin 148)) (colE2 ⟨50, by decide⟩ 10 hp)
        (rowE2 (⟨65, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨50, by decide⟩ : Fin 148))
        (colE1 ⟨50, by decide⟩ 10 (transLenTr ⟨50, by decide⟩ 10 hp))
        (rowE1 (⟨65, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨65, by decide⟩ : Fin 148) ⟨50, by decide⟩ _
      (validAt ⟨65, by decide⟩ (listedAt ⟨65, by decide⟩ hj))
      (colE1 ⟨50, by decide⟩ 10 (transLenTr ⟨50, by decide⟩ 10 hp)) T65_50
      hfix65_50 hinj65_50 hcardT65_50
      (fun i => conj_mem_of_fixedPoints _ _ (T65_50 i) (hfix65_50 i) _)
      ⟨65, by decide⟩ ⟨50, by decide⟩ _
      (Q2.validAt ⟨65, by decide⟩ (Q2.listedAt ⟨65, by decide⟩
        (alnCheck_rep ⟨65, by decide⟩ hj hq).1))
      (colE2 ⟨50, by decide⟩ 10 hp) Q2.T65_50_2 Q2.hfix65_50_2 Q2.hinj65_50_2
      Q2.hcardT65_50_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T65_50_2 i) (Q2.hfix65_50_2 i) _)
      colCert_65_50_10.hD ?_).symm
  rw [alnId_65 j hj]


theorem leaf_65_50_15 (hp : 15 < (Q2.transData.getD 50 []).length)
    (j : Nat) (hj : j < (repChars.getD 65 []).length)
    (hq : (normIsRep.getD 65 []).getD j false = true) :
    species (Q2.reps (⟨50, by decide⟩ : Fin 148)) (colE2 ⟨50, by decide⟩ 15 hp)
        (rowE2 (⟨65, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨50, by decide⟩ : Fin 148))
        (colE1 ⟨50, by decide⟩ 15 (transLenTr ⟨50, by decide⟩ 15 hp))
        (rowE1 (⟨65, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨65, by decide⟩ : Fin 148) ⟨50, by decide⟩ _
      (validAt ⟨65, by decide⟩ (listedAt ⟨65, by decide⟩ hj))
      (colE1 ⟨50, by decide⟩ 15 (transLenTr ⟨50, by decide⟩ 15 hp)) T65_50
      hfix65_50 hinj65_50 hcardT65_50
      (fun i => conj_mem_of_fixedPoints _ _ (T65_50 i) (hfix65_50 i) _)
      ⟨65, by decide⟩ ⟨50, by decide⟩ _
      (Q2.validAt ⟨65, by decide⟩ (Q2.listedAt ⟨65, by decide⟩
        (alnCheck_rep ⟨65, by decide⟩ hj hq).1))
      (colE2 ⟨50, by decide⟩ 15 hp) Q2.T65_50_2 Q2.hfix65_50_2 Q2.hinj65_50_2
      Q2.hcardT65_50_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T65_50_2 i) (Q2.hfix65_50_2 i) _)
      colCert_65_50_15.hD ?_).symm
  rw [alnId_65 j hj]


theorem leaf_65_50_20 (hp : 20 < (Q2.transData.getD 50 []).length)
    (j : Nat) (hj : j < (repChars.getD 65 []).length)
    (hq : (normIsRep.getD 65 []).getD j false = true) :
    species (Q2.reps (⟨50, by decide⟩ : Fin 148)) (colE2 ⟨50, by decide⟩ 20 hp)
        (rowE2 (⟨65, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨50, by decide⟩ : Fin 148))
        (colE1 ⟨50, by decide⟩ 20 (transLenTr ⟨50, by decide⟩ 20 hp))
        (rowE1 (⟨65, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨65, by decide⟩ : Fin 148) ⟨50, by decide⟩ _
      (validAt ⟨65, by decide⟩ (listedAt ⟨65, by decide⟩ hj))
      (colE1 ⟨50, by decide⟩ 20 (transLenTr ⟨50, by decide⟩ 20 hp)) T65_50
      hfix65_50 hinj65_50 hcardT65_50
      (fun i => conj_mem_of_fixedPoints _ _ (T65_50 i) (hfix65_50 i) _)
      ⟨65, by decide⟩ ⟨50, by decide⟩ _
      (Q2.validAt ⟨65, by decide⟩ (Q2.listedAt ⟨65, by decide⟩
        (alnCheck_rep ⟨65, by decide⟩ hj hq).1))
      (colE2 ⟨50, by decide⟩ 20 hp) Q2.T65_50_2 Q2.hfix65_50_2 Q2.hinj65_50_2
      Q2.hcardT65_50_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T65_50_2 i) (Q2.hfix65_50_2 i) _)
      colCert_65_50_20.hD ?_).symm
  rw [alnId_65 j hj]


theorem leaf_65_65_0 (hp : 0 < (Q2.transData.getD 65 []).length)
    (j : Nat) (hj : j < (repChars.getD 65 []).length)
    (hq : (normIsRep.getD 65 []).getD j false = true) :
    species (Q2.reps (⟨65, by decide⟩ : Fin 148)) (colE2 ⟨65, by decide⟩ 0 hp)
        (rowE2 (⟨65, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨65, by decide⟩ : Fin 148))
        (colE1 ⟨65, by decide⟩ 0 (transLenTr ⟨65, by decide⟩ 0 hp))
        (rowE1 (⟨65, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨65, by decide⟩ : Fin 148) ⟨65, by decide⟩ _
      (validAt ⟨65, by decide⟩ (listedAt ⟨65, by decide⟩ hj))
      (colE1 ⟨65, by decide⟩ 0 (transLenTr ⟨65, by decide⟩ 0 hp)) T65_65
      hfix65_65 hinj65_65 hcardT65_65
      (fun i => conj_mem_of_fixedPoints _ _ (T65_65 i) (hfix65_65 i) _)
      ⟨65, by decide⟩ ⟨65, by decide⟩ _
      (Q2.validAt ⟨65, by decide⟩ (Q2.listedAt ⟨65, by decide⟩
        (alnCheck_rep ⟨65, by decide⟩ hj hq).1))
      (colE2 ⟨65, by decide⟩ 0 hp) Q2.T65_65_2 Q2.hfix65_65_2 Q2.hinj65_65_2
      Q2.hcardT65_65_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T65_65_2 i) (Q2.hfix65_65_2 i) _)
      colCert_65_65_0.hD ?_).symm
  rw [alnId_65 j hj]


theorem leaf_65_65_1 (hp : 1 < (Q2.transData.getD 65 []).length)
    (j : Nat) (hj : j < (repChars.getD 65 []).length)
    (hq : (normIsRep.getD 65 []).getD j false = true) :
    species (Q2.reps (⟨65, by decide⟩ : Fin 148)) (colE2 ⟨65, by decide⟩ 1 hp)
        (rowE2 (⟨65, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨65, by decide⟩ : Fin 148))
        (colE1 ⟨65, by decide⟩ 1 (transLenTr ⟨65, by decide⟩ 1 hp))
        (rowE1 (⟨65, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨65, by decide⟩ : Fin 148) ⟨65, by decide⟩ _
      (validAt ⟨65, by decide⟩ (listedAt ⟨65, by decide⟩ hj))
      (colE1 ⟨65, by decide⟩ 1 (transLenTr ⟨65, by decide⟩ 1 hp)) T65_65
      hfix65_65 hinj65_65 hcardT65_65
      (fun i => conj_mem_of_fixedPoints _ _ (T65_65 i) (hfix65_65 i) _)
      ⟨65, by decide⟩ ⟨65, by decide⟩ _
      (Q2.validAt ⟨65, by decide⟩ (Q2.listedAt ⟨65, by decide⟩
        (alnCheck_rep ⟨65, by decide⟩ hj hq).1))
      (colE2 ⟨65, by decide⟩ 1 hp) Q2.T65_65_2 Q2.hfix65_65_2 Q2.hinj65_65_2
      Q2.hcardT65_65_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T65_65_2 i) (Q2.hfix65_65_2 i) _)
      colCert_65_65_1.hD ?_).symm
  rw [alnId_65 j hj]


theorem leaf_65_65_2 (hp : 2 < (Q2.transData.getD 65 []).length)
    (j : Nat) (hj : j < (repChars.getD 65 []).length)
    (hq : (normIsRep.getD 65 []).getD j false = true) :
    species (Q2.reps (⟨65, by decide⟩ : Fin 148)) (colE2 ⟨65, by decide⟩ 2 hp)
        (rowE2 (⟨65, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨65, by decide⟩ : Fin 148))
        (colE1 ⟨65, by decide⟩ 2 (transLenTr ⟨65, by decide⟩ 2 hp))
        (rowE1 (⟨65, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨65, by decide⟩ : Fin 148) ⟨65, by decide⟩ _
      (validAt ⟨65, by decide⟩ (listedAt ⟨65, by decide⟩ hj))
      (colE1 ⟨65, by decide⟩ 2 (transLenTr ⟨65, by decide⟩ 2 hp)) T65_65
      hfix65_65 hinj65_65 hcardT65_65
      (fun i => conj_mem_of_fixedPoints _ _ (T65_65 i) (hfix65_65 i) _)
      ⟨65, by decide⟩ ⟨65, by decide⟩ _
      (Q2.validAt ⟨65, by decide⟩ (Q2.listedAt ⟨65, by decide⟩
        (alnCheck_rep ⟨65, by decide⟩ hj hq).1))
      (colE2 ⟨65, by decide⟩ 2 hp) Q2.T65_65_2 Q2.hfix65_65_2 Q2.hinj65_65_2
      Q2.hcardT65_65_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T65_65_2 i) (Q2.hfix65_65_2 i) _)
      colCert_65_65_2.hD ?_).symm
  rw [alnId_65 j hj]


theorem leaf_65_65_3 (hp : 3 < (Q2.transData.getD 65 []).length)
    (j : Nat) (hj : j < (repChars.getD 65 []).length)
    (hq : (normIsRep.getD 65 []).getD j false = true) :
    species (Q2.reps (⟨65, by decide⟩ : Fin 148)) (colE2 ⟨65, by decide⟩ 3 hp)
        (rowE2 (⟨65, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨65, by decide⟩ : Fin 148))
        (colE1 ⟨65, by decide⟩ 3 (transLenTr ⟨65, by decide⟩ 3 hp))
        (rowE1 (⟨65, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨65, by decide⟩ : Fin 148) ⟨65, by decide⟩ _
      (validAt ⟨65, by decide⟩ (listedAt ⟨65, by decide⟩ hj))
      (colE1 ⟨65, by decide⟩ 3 (transLenTr ⟨65, by decide⟩ 3 hp)) T65_65
      hfix65_65 hinj65_65 hcardT65_65
      (fun i => conj_mem_of_fixedPoints _ _ (T65_65 i) (hfix65_65 i) _)
      ⟨65, by decide⟩ ⟨65, by decide⟩ _
      (Q2.validAt ⟨65, by decide⟩ (Q2.listedAt ⟨65, by decide⟩
        (alnCheck_rep ⟨65, by decide⟩ hj hq).1))
      (colE2 ⟨65, by decide⟩ 3 hp) Q2.T65_65_2 Q2.hfix65_65_2 Q2.hinj65_65_2
      Q2.hcardT65_65_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T65_65_2 i) (Q2.hfix65_65_2 i) _)
      colCert_65_65_3.hD ?_).symm
  rw [alnId_65 j hj]


theorem leaf_65_65_4 (hp : 4 < (Q2.transData.getD 65 []).length)
    (j : Nat) (hj : j < (repChars.getD 65 []).length)
    (hq : (normIsRep.getD 65 []).getD j false = true) :
    species (Q2.reps (⟨65, by decide⟩ : Fin 148)) (colE2 ⟨65, by decide⟩ 4 hp)
        (rowE2 (⟨65, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨65, by decide⟩ : Fin 148))
        (colE1 ⟨65, by decide⟩ 4 (transLenTr ⟨65, by decide⟩ 4 hp))
        (rowE1 (⟨65, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨65, by decide⟩ : Fin 148) ⟨65, by decide⟩ _
      (validAt ⟨65, by decide⟩ (listedAt ⟨65, by decide⟩ hj))
      (colE1 ⟨65, by decide⟩ 4 (transLenTr ⟨65, by decide⟩ 4 hp)) T65_65
      hfix65_65 hinj65_65 hcardT65_65
      (fun i => conj_mem_of_fixedPoints _ _ (T65_65 i) (hfix65_65 i) _)
      ⟨65, by decide⟩ ⟨65, by decide⟩ _
      (Q2.validAt ⟨65, by decide⟩ (Q2.listedAt ⟨65, by decide⟩
        (alnCheck_rep ⟨65, by decide⟩ hj hq).1))
      (colE2 ⟨65, by decide⟩ 4 hp) Q2.T65_65_2 Q2.hfix65_65_2 Q2.hinj65_65_2
      Q2.hcardT65_65_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T65_65_2 i) (Q2.hfix65_65_2 i) _)
      colCert_65_65_4.hD ?_).symm
  rw [alnId_65 j hj]


theorem leaf_65_65_5 (hp : 5 < (Q2.transData.getD 65 []).length)
    (j : Nat) (hj : j < (repChars.getD 65 []).length)
    (hq : (normIsRep.getD 65 []).getD j false = true) :
    species (Q2.reps (⟨65, by decide⟩ : Fin 148)) (colE2 ⟨65, by decide⟩ 5 hp)
        (rowE2 (⟨65, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨65, by decide⟩ : Fin 148))
        (colE1 ⟨65, by decide⟩ 5 (transLenTr ⟨65, by decide⟩ 5 hp))
        (rowE1 (⟨65, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨65, by decide⟩ : Fin 148) ⟨65, by decide⟩ _
      (validAt ⟨65, by decide⟩ (listedAt ⟨65, by decide⟩ hj))
      (colE1 ⟨65, by decide⟩ 5 (transLenTr ⟨65, by decide⟩ 5 hp)) T65_65
      hfix65_65 hinj65_65 hcardT65_65
      (fun i => conj_mem_of_fixedPoints _ _ (T65_65 i) (hfix65_65 i) _)
      ⟨65, by decide⟩ ⟨65, by decide⟩ _
      (Q2.validAt ⟨65, by decide⟩ (Q2.listedAt ⟨65, by decide⟩
        (alnCheck_rep ⟨65, by decide⟩ hj hq).1))
      (colE2 ⟨65, by decide⟩ 5 hp) Q2.T65_65_2 Q2.hfix65_65_2 Q2.hinj65_65_2
      Q2.hcardT65_65_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T65_65_2 i) (Q2.hfix65_65_2 i) _)
      colCert_65_65_5.hD ?_).symm
  rw [alnId_65 j hj]


theorem leaf_65_65_6 (hp : 6 < (Q2.transData.getD 65 []).length)
    (j : Nat) (hj : j < (repChars.getD 65 []).length)
    (hq : (normIsRep.getD 65 []).getD j false = true) :
    species (Q2.reps (⟨65, by decide⟩ : Fin 148)) (colE2 ⟨65, by decide⟩ 6 hp)
        (rowE2 (⟨65, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨65, by decide⟩ : Fin 148))
        (colE1 ⟨65, by decide⟩ 6 (transLenTr ⟨65, by decide⟩ 6 hp))
        (rowE1 (⟨65, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨65, by decide⟩ : Fin 148) ⟨65, by decide⟩ _
      (validAt ⟨65, by decide⟩ (listedAt ⟨65, by decide⟩ hj))
      (colE1 ⟨65, by decide⟩ 6 (transLenTr ⟨65, by decide⟩ 6 hp)) T65_65
      hfix65_65 hinj65_65 hcardT65_65
      (fun i => conj_mem_of_fixedPoints _ _ (T65_65 i) (hfix65_65 i) _)
      ⟨65, by decide⟩ ⟨65, by decide⟩ _
      (Q2.validAt ⟨65, by decide⟩ (Q2.listedAt ⟨65, by decide⟩
        (alnCheck_rep ⟨65, by decide⟩ hj hq).1))
      (colE2 ⟨65, by decide⟩ 6 hp) Q2.T65_65_2 Q2.hfix65_65_2 Q2.hinj65_65_2
      Q2.hcardT65_65_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T65_65_2 i) (Q2.hfix65_65_2 i) _)
      colCert_65_65_6.hD ?_).symm
  rw [alnId_65 j hj]


theorem leaf_65_65_7 (hp : 7 < (Q2.transData.getD 65 []).length)
    (j : Nat) (hj : j < (repChars.getD 65 []).length)
    (hq : (normIsRep.getD 65 []).getD j false = true) :
    species (Q2.reps (⟨65, by decide⟩ : Fin 148)) (colE2 ⟨65, by decide⟩ 7 hp)
        (rowE2 (⟨65, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨65, by decide⟩ : Fin 148))
        (colE1 ⟨65, by decide⟩ 7 (transLenTr ⟨65, by decide⟩ 7 hp))
        (rowE1 (⟨65, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨65, by decide⟩ : Fin 148) ⟨65, by decide⟩ _
      (validAt ⟨65, by decide⟩ (listedAt ⟨65, by decide⟩ hj))
      (colE1 ⟨65, by decide⟩ 7 (transLenTr ⟨65, by decide⟩ 7 hp)) T65_65
      hfix65_65 hinj65_65 hcardT65_65
      (fun i => conj_mem_of_fixedPoints _ _ (T65_65 i) (hfix65_65 i) _)
      ⟨65, by decide⟩ ⟨65, by decide⟩ _
      (Q2.validAt ⟨65, by decide⟩ (Q2.listedAt ⟨65, by decide⟩
        (alnCheck_rep ⟨65, by decide⟩ hj hq).1))
      (colE2 ⟨65, by decide⟩ 7 hp) Q2.T65_65_2 Q2.hfix65_65_2 Q2.hinj65_65_2
      Q2.hcardT65_65_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T65_65_2 i) (Q2.hfix65_65_2 i) _)
      colCert_65_65_7.hD ?_).symm
  rw [alnId_65 j hj]


theorem leaf_65_65_8 (hp : 8 < (Q2.transData.getD 65 []).length)
    (j : Nat) (hj : j < (repChars.getD 65 []).length)
    (hq : (normIsRep.getD 65 []).getD j false = true) :
    species (Q2.reps (⟨65, by decide⟩ : Fin 148)) (colE2 ⟨65, by decide⟩ 8 hp)
        (rowE2 (⟨65, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨65, by decide⟩ : Fin 148))
        (colE1 ⟨65, by decide⟩ 8 (transLenTr ⟨65, by decide⟩ 8 hp))
        (rowE1 (⟨65, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨65, by decide⟩ : Fin 148) ⟨65, by decide⟩ _
      (validAt ⟨65, by decide⟩ (listedAt ⟨65, by decide⟩ hj))
      (colE1 ⟨65, by decide⟩ 8 (transLenTr ⟨65, by decide⟩ 8 hp)) T65_65
      hfix65_65 hinj65_65 hcardT65_65
      (fun i => conj_mem_of_fixedPoints _ _ (T65_65 i) (hfix65_65 i) _)
      ⟨65, by decide⟩ ⟨65, by decide⟩ _
      (Q2.validAt ⟨65, by decide⟩ (Q2.listedAt ⟨65, by decide⟩
        (alnCheck_rep ⟨65, by decide⟩ hj hq).1))
      (colE2 ⟨65, by decide⟩ 8 hp) Q2.T65_65_2 Q2.hfix65_65_2 Q2.hinj65_65_2
      Q2.hcardT65_65_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T65_65_2 i) (Q2.hfix65_65_2 i) _)
      colCert_65_65_8.hD ?_).symm
  rw [alnId_65 j hj]


theorem leaf_65_65_9 (hp : 9 < (Q2.transData.getD 65 []).length)
    (j : Nat) (hj : j < (repChars.getD 65 []).length)
    (hq : (normIsRep.getD 65 []).getD j false = true) :
    species (Q2.reps (⟨65, by decide⟩ : Fin 148)) (colE2 ⟨65, by decide⟩ 9 hp)
        (rowE2 (⟨65, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨65, by decide⟩ : Fin 148))
        (colE1 ⟨65, by decide⟩ 9 (transLenTr ⟨65, by decide⟩ 9 hp))
        (rowE1 (⟨65, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨65, by decide⟩ : Fin 148) ⟨65, by decide⟩ _
      (validAt ⟨65, by decide⟩ (listedAt ⟨65, by decide⟩ hj))
      (colE1 ⟨65, by decide⟩ 9 (transLenTr ⟨65, by decide⟩ 9 hp)) T65_65
      hfix65_65 hinj65_65 hcardT65_65
      (fun i => conj_mem_of_fixedPoints _ _ (T65_65 i) (hfix65_65 i) _)
      ⟨65, by decide⟩ ⟨65, by decide⟩ _
      (Q2.validAt ⟨65, by decide⟩ (Q2.listedAt ⟨65, by decide⟩
        (alnCheck_rep ⟨65, by decide⟩ hj hq).1))
      (colE2 ⟨65, by decide⟩ 9 hp) Q2.T65_65_2 Q2.hfix65_65_2 Q2.hinj65_65_2
      Q2.hcardT65_65_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T65_65_2 i) (Q2.hfix65_65_2 i) _)
      colCert_65_65_9.hD ?_).symm
  rw [alnId_65 j hj]


theorem leaf_65_65_10 (hp : 10 < (Q2.transData.getD 65 []).length)
    (j : Nat) (hj : j < (repChars.getD 65 []).length)
    (hq : (normIsRep.getD 65 []).getD j false = true) :
    species (Q2.reps (⟨65, by decide⟩ : Fin 148)) (colE2 ⟨65, by decide⟩ 10 hp)
        (rowE2 (⟨65, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨65, by decide⟩ : Fin 148))
        (colE1 ⟨65, by decide⟩ 10 (transLenTr ⟨65, by decide⟩ 10 hp))
        (rowE1 (⟨65, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨65, by decide⟩ : Fin 148) ⟨65, by decide⟩ _
      (validAt ⟨65, by decide⟩ (listedAt ⟨65, by decide⟩ hj))
      (colE1 ⟨65, by decide⟩ 10 (transLenTr ⟨65, by decide⟩ 10 hp)) T65_65
      hfix65_65 hinj65_65 hcardT65_65
      (fun i => conj_mem_of_fixedPoints _ _ (T65_65 i) (hfix65_65 i) _)
      ⟨65, by decide⟩ ⟨65, by decide⟩ _
      (Q2.validAt ⟨65, by decide⟩ (Q2.listedAt ⟨65, by decide⟩
        (alnCheck_rep ⟨65, by decide⟩ hj hq).1))
      (colE2 ⟨65, by decide⟩ 10 hp) Q2.T65_65_2 Q2.hfix65_65_2 Q2.hinj65_65_2
      Q2.hcardT65_65_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T65_65_2 i) (Q2.hfix65_65_2 i) _)
      colCert_65_65_10.hD ?_).symm
  rw [alnId_65 j hj]


theorem leaf_65_65_11 (hp : 11 < (Q2.transData.getD 65 []).length)
    (j : Nat) (hj : j < (repChars.getD 65 []).length)
    (hq : (normIsRep.getD 65 []).getD j false = true) :
    species (Q2.reps (⟨65, by decide⟩ : Fin 148)) (colE2 ⟨65, by decide⟩ 11 hp)
        (rowE2 (⟨65, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨65, by decide⟩ : Fin 148))
        (colE1 ⟨65, by decide⟩ 11 (transLenTr ⟨65, by decide⟩ 11 hp))
        (rowE1 (⟨65, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨65, by decide⟩ : Fin 148) ⟨65, by decide⟩ _
      (validAt ⟨65, by decide⟩ (listedAt ⟨65, by decide⟩ hj))
      (colE1 ⟨65, by decide⟩ 11 (transLenTr ⟨65, by decide⟩ 11 hp)) T65_65
      hfix65_65 hinj65_65 hcardT65_65
      (fun i => conj_mem_of_fixedPoints _ _ (T65_65 i) (hfix65_65 i) _)
      ⟨65, by decide⟩ ⟨65, by decide⟩ _
      (Q2.validAt ⟨65, by decide⟩ (Q2.listedAt ⟨65, by decide⟩
        (alnCheck_rep ⟨65, by decide⟩ hj hq).1))
      (colE2 ⟨65, by decide⟩ 11 hp) Q2.T65_65_2 Q2.hfix65_65_2 Q2.hinj65_65_2
      Q2.hcardT65_65_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T65_65_2 i) (Q2.hfix65_65_2 i) _)
      colCert_65_65_11.hD ?_).symm
  rw [alnId_65 j hj]


theorem leaf_65_65_12 (hp : 12 < (Q2.transData.getD 65 []).length)
    (j : Nat) (hj : j < (repChars.getD 65 []).length)
    (hq : (normIsRep.getD 65 []).getD j false = true) :
    species (Q2.reps (⟨65, by decide⟩ : Fin 148)) (colE2 ⟨65, by decide⟩ 12 hp)
        (rowE2 (⟨65, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨65, by decide⟩ : Fin 148))
        (colE1 ⟨65, by decide⟩ 12 (transLenTr ⟨65, by decide⟩ 12 hp))
        (rowE1 (⟨65, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨65, by decide⟩ : Fin 148) ⟨65, by decide⟩ _
      (validAt ⟨65, by decide⟩ (listedAt ⟨65, by decide⟩ hj))
      (colE1 ⟨65, by decide⟩ 12 (transLenTr ⟨65, by decide⟩ 12 hp)) T65_65
      hfix65_65 hinj65_65 hcardT65_65
      (fun i => conj_mem_of_fixedPoints _ _ (T65_65 i) (hfix65_65 i) _)
      ⟨65, by decide⟩ ⟨65, by decide⟩ _
      (Q2.validAt ⟨65, by decide⟩ (Q2.listedAt ⟨65, by decide⟩
        (alnCheck_rep ⟨65, by decide⟩ hj hq).1))
      (colE2 ⟨65, by decide⟩ 12 hp) Q2.T65_65_2 Q2.hfix65_65_2 Q2.hinj65_65_2
      Q2.hcardT65_65_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T65_65_2 i) (Q2.hfix65_65_2 i) _)
      colCert_65_65_12.hD ?_).symm
  rw [alnId_65 j hj]


theorem leaf_65_65_13 (hp : 13 < (Q2.transData.getD 65 []).length)
    (j : Nat) (hj : j < (repChars.getD 65 []).length)
    (hq : (normIsRep.getD 65 []).getD j false = true) :
    species (Q2.reps (⟨65, by decide⟩ : Fin 148)) (colE2 ⟨65, by decide⟩ 13 hp)
        (rowE2 (⟨65, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨65, by decide⟩ : Fin 148))
        (colE1 ⟨65, by decide⟩ 13 (transLenTr ⟨65, by decide⟩ 13 hp))
        (rowE1 (⟨65, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨65, by decide⟩ : Fin 148) ⟨65, by decide⟩ _
      (validAt ⟨65, by decide⟩ (listedAt ⟨65, by decide⟩ hj))
      (colE1 ⟨65, by decide⟩ 13 (transLenTr ⟨65, by decide⟩ 13 hp)) T65_65
      hfix65_65 hinj65_65 hcardT65_65
      (fun i => conj_mem_of_fixedPoints _ _ (T65_65 i) (hfix65_65 i) _)
      ⟨65, by decide⟩ ⟨65, by decide⟩ _
      (Q2.validAt ⟨65, by decide⟩ (Q2.listedAt ⟨65, by decide⟩
        (alnCheck_rep ⟨65, by decide⟩ hj hq).1))
      (colE2 ⟨65, by decide⟩ 13 hp) Q2.T65_65_2 Q2.hfix65_65_2 Q2.hinj65_65_2
      Q2.hcardT65_65_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T65_65_2 i) (Q2.hfix65_65_2 i) _)
      colCert_65_65_13.hD ?_).symm
  rw [alnId_65 j hj]


theorem leaf_65_65_14 (hp : 14 < (Q2.transData.getD 65 []).length)
    (j : Nat) (hj : j < (repChars.getD 65 []).length)
    (hq : (normIsRep.getD 65 []).getD j false = true) :
    species (Q2.reps (⟨65, by decide⟩ : Fin 148)) (colE2 ⟨65, by decide⟩ 14 hp)
        (rowE2 (⟨65, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨65, by decide⟩ : Fin 148))
        (colE1 ⟨65, by decide⟩ 14 (transLenTr ⟨65, by decide⟩ 14 hp))
        (rowE1 (⟨65, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨65, by decide⟩ : Fin 148) ⟨65, by decide⟩ _
      (validAt ⟨65, by decide⟩ (listedAt ⟨65, by decide⟩ hj))
      (colE1 ⟨65, by decide⟩ 14 (transLenTr ⟨65, by decide⟩ 14 hp)) T65_65
      hfix65_65 hinj65_65 hcardT65_65
      (fun i => conj_mem_of_fixedPoints _ _ (T65_65 i) (hfix65_65 i) _)
      ⟨65, by decide⟩ ⟨65, by decide⟩ _
      (Q2.validAt ⟨65, by decide⟩ (Q2.listedAt ⟨65, by decide⟩
        (alnCheck_rep ⟨65, by decide⟩ hj hq).1))
      (colE2 ⟨65, by decide⟩ 14 hp) Q2.T65_65_2 Q2.hfix65_65_2 Q2.hinj65_65_2
      Q2.hcardT65_65_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T65_65_2 i) (Q2.hfix65_65_2 i) _)
      colCert_65_65_14.hD ?_).symm
  rw [alnId_65 j hj]


theorem leaf_65_65_15 (hp : 15 < (Q2.transData.getD 65 []).length)
    (j : Nat) (hj : j < (repChars.getD 65 []).length)
    (hq : (normIsRep.getD 65 []).getD j false = true) :
    species (Q2.reps (⟨65, by decide⟩ : Fin 148)) (colE2 ⟨65, by decide⟩ 15 hp)
        (rowE2 (⟨65, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨65, by decide⟩ : Fin 148))
        (colE1 ⟨65, by decide⟩ 15 (transLenTr ⟨65, by decide⟩ 15 hp))
        (rowE1 (⟨65, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨65, by decide⟩ : Fin 148) ⟨65, by decide⟩ _
      (validAt ⟨65, by decide⟩ (listedAt ⟨65, by decide⟩ hj))
      (colE1 ⟨65, by decide⟩ 15 (transLenTr ⟨65, by decide⟩ 15 hp)) T65_65
      hfix65_65 hinj65_65 hcardT65_65
      (fun i => conj_mem_of_fixedPoints _ _ (T65_65 i) (hfix65_65 i) _)
      ⟨65, by decide⟩ ⟨65, by decide⟩ _
      (Q2.validAt ⟨65, by decide⟩ (Q2.listedAt ⟨65, by decide⟩
        (alnCheck_rep ⟨65, by decide⟩ hj hq).1))
      (colE2 ⟨65, by decide⟩ 15 hp) Q2.T65_65_2 Q2.hfix65_65_2 Q2.hinj65_65_2
      Q2.hcardT65_65_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T65_65_2 i) (Q2.hfix65_65_2 i) _)
      colCert_65_65_15.hD ?_).symm
  rw [alnId_65 j hj]


theorem leaf_65_65_16 (hp : 16 < (Q2.transData.getD 65 []).length)
    (j : Nat) (hj : j < (repChars.getD 65 []).length)
    (hq : (normIsRep.getD 65 []).getD j false = true) :
    species (Q2.reps (⟨65, by decide⟩ : Fin 148)) (colE2 ⟨65, by decide⟩ 16 hp)
        (rowE2 (⟨65, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨65, by decide⟩ : Fin 148))
        (colE1 ⟨65, by decide⟩ 16 (transLenTr ⟨65, by decide⟩ 16 hp))
        (rowE1 (⟨65, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨65, by decide⟩ : Fin 148) ⟨65, by decide⟩ _
      (validAt ⟨65, by decide⟩ (listedAt ⟨65, by decide⟩ hj))
      (colE1 ⟨65, by decide⟩ 16 (transLenTr ⟨65, by decide⟩ 16 hp)) T65_65
      hfix65_65 hinj65_65 hcardT65_65
      (fun i => conj_mem_of_fixedPoints _ _ (T65_65 i) (hfix65_65 i) _)
      ⟨65, by decide⟩ ⟨65, by decide⟩ _
      (Q2.validAt ⟨65, by decide⟩ (Q2.listedAt ⟨65, by decide⟩
        (alnCheck_rep ⟨65, by decide⟩ hj hq).1))
      (colE2 ⟨65, by decide⟩ 16 hp) Q2.T65_65_2 Q2.hfix65_65_2 Q2.hinj65_65_2
      Q2.hcardT65_65_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T65_65_2 i) (Q2.hfix65_65_2 i) _)
      colCert_65_65_16.hD ?_).symm
  rw [alnId_65 j hj]


theorem leaf_65_65_17 (hp : 17 < (Q2.transData.getD 65 []).length)
    (j : Nat) (hj : j < (repChars.getD 65 []).length)
    (hq : (normIsRep.getD 65 []).getD j false = true) :
    species (Q2.reps (⟨65, by decide⟩ : Fin 148)) (colE2 ⟨65, by decide⟩ 17 hp)
        (rowE2 (⟨65, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨65, by decide⟩ : Fin 148))
        (colE1 ⟨65, by decide⟩ 17 (transLenTr ⟨65, by decide⟩ 17 hp))
        (rowE1 (⟨65, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨65, by decide⟩ : Fin 148) ⟨65, by decide⟩ _
      (validAt ⟨65, by decide⟩ (listedAt ⟨65, by decide⟩ hj))
      (colE1 ⟨65, by decide⟩ 17 (transLenTr ⟨65, by decide⟩ 17 hp)) T65_65
      hfix65_65 hinj65_65 hcardT65_65
      (fun i => conj_mem_of_fixedPoints _ _ (T65_65 i) (hfix65_65 i) _)
      ⟨65, by decide⟩ ⟨65, by decide⟩ _
      (Q2.validAt ⟨65, by decide⟩ (Q2.listedAt ⟨65, by decide⟩
        (alnCheck_rep ⟨65, by decide⟩ hj hq).1))
      (colE2 ⟨65, by decide⟩ 17 hp) Q2.T65_65_2 Q2.hfix65_65_2 Q2.hinj65_65_2
      Q2.hcardT65_65_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T65_65_2 i) (Q2.hfix65_65_2 i) _)
      colCert_65_65_17.hD ?_).symm
  rw [alnId_65 j hj]


theorem leaf_65_65_18 (hp : 18 < (Q2.transData.getD 65 []).length)
    (j : Nat) (hj : j < (repChars.getD 65 []).length)
    (hq : (normIsRep.getD 65 []).getD j false = true) :
    species (Q2.reps (⟨65, by decide⟩ : Fin 148)) (colE2 ⟨65, by decide⟩ 18 hp)
        (rowE2 (⟨65, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨65, by decide⟩ : Fin 148))
        (colE1 ⟨65, by decide⟩ 18 (transLenTr ⟨65, by decide⟩ 18 hp))
        (rowE1 (⟨65, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨65, by decide⟩ : Fin 148) ⟨65, by decide⟩ _
      (validAt ⟨65, by decide⟩ (listedAt ⟨65, by decide⟩ hj))
      (colE1 ⟨65, by decide⟩ 18 (transLenTr ⟨65, by decide⟩ 18 hp)) T65_65
      hfix65_65 hinj65_65 hcardT65_65
      (fun i => conj_mem_of_fixedPoints _ _ (T65_65 i) (hfix65_65 i) _)
      ⟨65, by decide⟩ ⟨65, by decide⟩ _
      (Q2.validAt ⟨65, by decide⟩ (Q2.listedAt ⟨65, by decide⟩
        (alnCheck_rep ⟨65, by decide⟩ hj hq).1))
      (colE2 ⟨65, by decide⟩ 18 hp) Q2.T65_65_2 Q2.hfix65_65_2 Q2.hinj65_65_2
      Q2.hcardT65_65_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T65_65_2 i) (Q2.hfix65_65_2 i) _)
      colCert_65_65_18.hD ?_).symm
  rw [alnId_65 j hj]


theorem leaf_65_65_19 (hp : 19 < (Q2.transData.getD 65 []).length)
    (j : Nat) (hj : j < (repChars.getD 65 []).length)
    (hq : (normIsRep.getD 65 []).getD j false = true) :
    species (Q2.reps (⟨65, by decide⟩ : Fin 148)) (colE2 ⟨65, by decide⟩ 19 hp)
        (rowE2 (⟨65, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨65, by decide⟩ : Fin 148))
        (colE1 ⟨65, by decide⟩ 19 (transLenTr ⟨65, by decide⟩ 19 hp))
        (rowE1 (⟨65, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨65, by decide⟩ : Fin 148) ⟨65, by decide⟩ _
      (validAt ⟨65, by decide⟩ (listedAt ⟨65, by decide⟩ hj))
      (colE1 ⟨65, by decide⟩ 19 (transLenTr ⟨65, by decide⟩ 19 hp)) T65_65
      hfix65_65 hinj65_65 hcardT65_65
      (fun i => conj_mem_of_fixedPoints _ _ (T65_65 i) (hfix65_65 i) _)
      ⟨65, by decide⟩ ⟨65, by decide⟩ _
      (Q2.validAt ⟨65, by decide⟩ (Q2.listedAt ⟨65, by decide⟩
        (alnCheck_rep ⟨65, by decide⟩ hj hq).1))
      (colE2 ⟨65, by decide⟩ 19 hp) Q2.T65_65_2 Q2.hfix65_65_2 Q2.hinj65_65_2
      Q2.hcardT65_65_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T65_65_2 i) (Q2.hfix65_65_2 i) _)
      colCert_65_65_19.hD ?_).symm
  rw [alnId_65 j hj]


theorem leaf_65_65_20 (hp : 20 < (Q2.transData.getD 65 []).length)
    (j : Nat) (hj : j < (repChars.getD 65 []).length)
    (hq : (normIsRep.getD 65 []).getD j false = true) :
    species (Q2.reps (⟨65, by decide⟩ : Fin 148)) (colE2 ⟨65, by decide⟩ 20 hp)
        (rowE2 (⟨65, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨65, by decide⟩ : Fin 148))
        (colE1 ⟨65, by decide⟩ 20 (transLenTr ⟨65, by decide⟩ 20 hp))
        (rowE1 (⟨65, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨65, by decide⟩ : Fin 148) ⟨65, by decide⟩ _
      (validAt ⟨65, by decide⟩ (listedAt ⟨65, by decide⟩ hj))
      (colE1 ⟨65, by decide⟩ 20 (transLenTr ⟨65, by decide⟩ 20 hp)) T65_65
      hfix65_65 hinj65_65 hcardT65_65
      (fun i => conj_mem_of_fixedPoints _ _ (T65_65 i) (hfix65_65 i) _)
      ⟨65, by decide⟩ ⟨65, by decide⟩ _
      (Q2.validAt ⟨65, by decide⟩ (Q2.listedAt ⟨65, by decide⟩
        (alnCheck_rep ⟨65, by decide⟩ hj hq).1))
      (colE2 ⟨65, by decide⟩ 20 hp) Q2.T65_65_2 Q2.hfix65_65_2 Q2.hinj65_65_2
      Q2.hcardT65_65_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T65_65_2 i) (Q2.hfix65_65_2 i) _)
      colCert_65_65_20.hD ?_).symm
  rw [alnId_65 j hj]


theorem leaf_65_65_21 (hp : 21 < (Q2.transData.getD 65 []).length)
    (j : Nat) (hj : j < (repChars.getD 65 []).length)
    (hq : (normIsRep.getD 65 []).getD j false = true) :
    species (Q2.reps (⟨65, by decide⟩ : Fin 148)) (colE2 ⟨65, by decide⟩ 21 hp)
        (rowE2 (⟨65, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨65, by decide⟩ : Fin 148))
        (colE1 ⟨65, by decide⟩ 21 (transLenTr ⟨65, by decide⟩ 21 hp))
        (rowE1 (⟨65, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨65, by decide⟩ : Fin 148) ⟨65, by decide⟩ _
      (validAt ⟨65, by decide⟩ (listedAt ⟨65, by decide⟩ hj))
      (colE1 ⟨65, by decide⟩ 21 (transLenTr ⟨65, by decide⟩ 21 hp)) T65_65
      hfix65_65 hinj65_65 hcardT65_65
      (fun i => conj_mem_of_fixedPoints _ _ (T65_65 i) (hfix65_65 i) _)
      ⟨65, by decide⟩ ⟨65, by decide⟩ _
      (Q2.validAt ⟨65, by decide⟩ (Q2.listedAt ⟨65, by decide⟩
        (alnCheck_rep ⟨65, by decide⟩ hj hq).1))
      (colE2 ⟨65, by decide⟩ 21 hp) Q2.T65_65_2 Q2.hfix65_65_2 Q2.hinj65_65_2
      Q2.hcardT65_65_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T65_65_2 i) (Q2.hfix65_65_2 i) _)
      colCert_65_65_21.hD ?_).symm
  rw [alnId_65 j hj]


theorem leaf_65_65_22 (hp : 22 < (Q2.transData.getD 65 []).length)
    (j : Nat) (hj : j < (repChars.getD 65 []).length)
    (hq : (normIsRep.getD 65 []).getD j false = true) :
    species (Q2.reps (⟨65, by decide⟩ : Fin 148)) (colE2 ⟨65, by decide⟩ 22 hp)
        (rowE2 (⟨65, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨65, by decide⟩ : Fin 148))
        (colE1 ⟨65, by decide⟩ 22 (transLenTr ⟨65, by decide⟩ 22 hp))
        (rowE1 (⟨65, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨65, by decide⟩ : Fin 148) ⟨65, by decide⟩ _
      (validAt ⟨65, by decide⟩ (listedAt ⟨65, by decide⟩ hj))
      (colE1 ⟨65, by decide⟩ 22 (transLenTr ⟨65, by decide⟩ 22 hp)) T65_65
      hfix65_65 hinj65_65 hcardT65_65
      (fun i => conj_mem_of_fixedPoints _ _ (T65_65 i) (hfix65_65 i) _)
      ⟨65, by decide⟩ ⟨65, by decide⟩ _
      (Q2.validAt ⟨65, by decide⟩ (Q2.listedAt ⟨65, by decide⟩
        (alnCheck_rep ⟨65, by decide⟩ hj hq).1))
      (colE2 ⟨65, by decide⟩ 22 hp) Q2.T65_65_2 Q2.hfix65_65_2 Q2.hinj65_65_2
      Q2.hcardT65_65_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T65_65_2 i) (Q2.hfix65_65_2 i) _)
      colCert_65_65_22.hD ?_).symm
  rw [alnId_65 j hj]


theorem leaf_65_65_23 (hp : 23 < (Q2.transData.getD 65 []).length)
    (j : Nat) (hj : j < (repChars.getD 65 []).length)
    (hq : (normIsRep.getD 65 []).getD j false = true) :
    species (Q2.reps (⟨65, by decide⟩ : Fin 148)) (colE2 ⟨65, by decide⟩ 23 hp)
        (rowE2 (⟨65, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨65, by decide⟩ : Fin 148))
        (colE1 ⟨65, by decide⟩ 23 (transLenTr ⟨65, by decide⟩ 23 hp))
        (rowE1 (⟨65, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨65, by decide⟩ : Fin 148) ⟨65, by decide⟩ _
      (validAt ⟨65, by decide⟩ (listedAt ⟨65, by decide⟩ hj))
      (colE1 ⟨65, by decide⟩ 23 (transLenTr ⟨65, by decide⟩ 23 hp)) T65_65
      hfix65_65 hinj65_65 hcardT65_65
      (fun i => conj_mem_of_fixedPoints _ _ (T65_65 i) (hfix65_65 i) _)
      ⟨65, by decide⟩ ⟨65, by decide⟩ _
      (Q2.validAt ⟨65, by decide⟩ (Q2.listedAt ⟨65, by decide⟩
        (alnCheck_rep ⟨65, by decide⟩ hj hq).1))
      (colE2 ⟨65, by decide⟩ 23 hp) Q2.T65_65_2 Q2.hfix65_65_2 Q2.hinj65_65_2
      Q2.hcardT65_65_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T65_65_2 i) (Q2.hfix65_65_2 i) _)
      colCert_65_65_23.hD ?_).symm
  rw [alnId_65 j hj]


theorem leaf_65_65_24 (hp : 24 < (Q2.transData.getD 65 []).length)
    (j : Nat) (hj : j < (repChars.getD 65 []).length)
    (hq : (normIsRep.getD 65 []).getD j false = true) :
    species (Q2.reps (⟨65, by decide⟩ : Fin 148)) (colE2 ⟨65, by decide⟩ 24 hp)
        (rowE2 (⟨65, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨65, by decide⟩ : Fin 148))
        (colE1 ⟨65, by decide⟩ 24 (transLenTr ⟨65, by decide⟩ 24 hp))
        (rowE1 (⟨65, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨65, by decide⟩ : Fin 148) ⟨65, by decide⟩ _
      (validAt ⟨65, by decide⟩ (listedAt ⟨65, by decide⟩ hj))
      (colE1 ⟨65, by decide⟩ 24 (transLenTr ⟨65, by decide⟩ 24 hp)) T65_65
      hfix65_65 hinj65_65 hcardT65_65
      (fun i => conj_mem_of_fixedPoints _ _ (T65_65 i) (hfix65_65 i) _)
      ⟨65, by decide⟩ ⟨65, by decide⟩ _
      (Q2.validAt ⟨65, by decide⟩ (Q2.listedAt ⟨65, by decide⟩
        (alnCheck_rep ⟨65, by decide⟩ hj hq).1))
      (colE2 ⟨65, by decide⟩ 24 hp) Q2.T65_65_2 Q2.hfix65_65_2 Q2.hinj65_65_2
      Q2.hcardT65_65_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T65_65_2 i) (Q2.hfix65_65_2 i) _)
      colCert_65_65_24.hD ?_).symm
  rw [alnId_65 j hj]


theorem leaf_66_1_0 (hp : 0 < (Q2.transData.getD 1 []).length)
    (j : Nat) (hj : j < (repChars.getD 66 []).length)
    (hq : (normIsRep.getD 66 []).getD j false = true) :
    species (Q2.reps (⟨1, by decide⟩ : Fin 148)) (colE2 ⟨1, by decide⟩ 0 hp)
        (rowE2 (⟨66, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨1, by decide⟩ : Fin 148))
        (colE1 ⟨1, by decide⟩ 0 (transLenTr ⟨1, by decide⟩ 0 hp))
        (rowE1 (⟨66, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨66, by decide⟩ : Fin 148) ⟨1, by decide⟩ _
      (validAt ⟨66, by decide⟩ (listedAt ⟨66, by decide⟩ hj))
      (colE1 ⟨1, by decide⟩ 0 (transLenTr ⟨1, by decide⟩ 0 hp)) T66_1
      hfix66_1 hinj66_1 hcardT66_1
      (fun i => conj_mem_of_fixedPoints _ _ (T66_1 i) (hfix66_1 i) _)
      ⟨66, by decide⟩ ⟨1, by decide⟩ _
      (Q2.validAt ⟨66, by decide⟩ (Q2.listedAt ⟨66, by decide⟩
        (alnCheck_rep ⟨66, by decide⟩ hj hq).1))
      (colE2 ⟨1, by decide⟩ 0 hp) Q2.T66_1_2 Q2.hfix66_1_2 Q2.hinj66_1_2
      Q2.hcardT66_1_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T66_1_2 i) (Q2.hfix66_1_2 i) _)
      colCert_66_1_0.hD ?_).symm
  rw [alnId_66 j hj]


theorem leaf_66_1_1 (hp : 1 < (Q2.transData.getD 1 []).length)
    (j : Nat) (hj : j < (repChars.getD 66 []).length)
    (hq : (normIsRep.getD 66 []).getD j false = true) :
    species (Q2.reps (⟨1, by decide⟩ : Fin 148)) (colE2 ⟨1, by decide⟩ 1 hp)
        (rowE2 (⟨66, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨1, by decide⟩ : Fin 148))
        (colE1 ⟨1, by decide⟩ 1 (transLenTr ⟨1, by decide⟩ 1 hp))
        (rowE1 (⟨66, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨66, by decide⟩ : Fin 148) ⟨1, by decide⟩ _
      (validAt ⟨66, by decide⟩ (listedAt ⟨66, by decide⟩ hj))
      (colE1 ⟨1, by decide⟩ 1 (transLenTr ⟨1, by decide⟩ 1 hp)) T66_1
      hfix66_1 hinj66_1 hcardT66_1
      (fun i => conj_mem_of_fixedPoints _ _ (T66_1 i) (hfix66_1 i) _)
      ⟨66, by decide⟩ ⟨1, by decide⟩ _
      (Q2.validAt ⟨66, by decide⟩ (Q2.listedAt ⟨66, by decide⟩
        (alnCheck_rep ⟨66, by decide⟩ hj hq).1))
      (colE2 ⟨1, by decide⟩ 1 hp) Q2.T66_1_2 Q2.hfix66_1_2 Q2.hinj66_1_2
      Q2.hcardT66_1_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T66_1_2 i) (Q2.hfix66_1_2 i) _)
      colCert_66_1_1.hD ?_).symm
  rw [alnId_66 j hj]


theorem leaf_66_1_2 (hp : 2 < (Q2.transData.getD 1 []).length)
    (j : Nat) (hj : j < (repChars.getD 66 []).length)
    (hq : (normIsRep.getD 66 []).getD j false = true) :
    species (Q2.reps (⟨1, by decide⟩ : Fin 148)) (colE2 ⟨1, by decide⟩ 2 hp)
        (rowE2 (⟨66, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨1, by decide⟩ : Fin 148))
        (colE1 ⟨1, by decide⟩ 2 (transLenTr ⟨1, by decide⟩ 2 hp))
        (rowE1 (⟨66, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨66, by decide⟩ : Fin 148) ⟨1, by decide⟩ _
      (validAt ⟨66, by decide⟩ (listedAt ⟨66, by decide⟩ hj))
      (colE1 ⟨1, by decide⟩ 2 (transLenTr ⟨1, by decide⟩ 2 hp)) T66_1
      hfix66_1 hinj66_1 hcardT66_1
      (fun i => conj_mem_of_fixedPoints _ _ (T66_1 i) (hfix66_1 i) _)
      ⟨66, by decide⟩ ⟨1, by decide⟩ _
      (Q2.validAt ⟨66, by decide⟩ (Q2.listedAt ⟨66, by decide⟩
        (alnCheck_rep ⟨66, by decide⟩ hj hq).1))
      (colE2 ⟨1, by decide⟩ 2 hp) Q2.T66_1_2 Q2.hfix66_1_2 Q2.hinj66_1_2
      Q2.hcardT66_1_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T66_1_2 i) (Q2.hfix66_1_2 i) _)
      colCert_66_1_2.hD ?_).symm
  rw [alnId_66 j hj]


theorem leaf_66_1_3 (hp : 3 < (Q2.transData.getD 1 []).length)
    (j : Nat) (hj : j < (repChars.getD 66 []).length)
    (hq : (normIsRep.getD 66 []).getD j false = true) :
    species (Q2.reps (⟨1, by decide⟩ : Fin 148)) (colE2 ⟨1, by decide⟩ 3 hp)
        (rowE2 (⟨66, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨1, by decide⟩ : Fin 148))
        (colE1 ⟨1, by decide⟩ 3 (transLenTr ⟨1, by decide⟩ 3 hp))
        (rowE1 (⟨66, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨66, by decide⟩ : Fin 148) ⟨1, by decide⟩ _
      (validAt ⟨66, by decide⟩ (listedAt ⟨66, by decide⟩ hj))
      (colE1 ⟨1, by decide⟩ 3 (transLenTr ⟨1, by decide⟩ 3 hp)) T66_1
      hfix66_1 hinj66_1 hcardT66_1
      (fun i => conj_mem_of_fixedPoints _ _ (T66_1 i) (hfix66_1 i) _)
      ⟨66, by decide⟩ ⟨1, by decide⟩ _
      (Q2.validAt ⟨66, by decide⟩ (Q2.listedAt ⟨66, by decide⟩
        (alnCheck_rep ⟨66, by decide⟩ hj hq).1))
      (colE2 ⟨1, by decide⟩ 3 hp) Q2.T66_1_2 Q2.hfix66_1_2 Q2.hinj66_1_2
      Q2.hcardT66_1_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T66_1_2 i) (Q2.hfix66_1_2 i) _)
      colCert_66_1_3.hD ?_).symm
  rw [alnId_66 j hj]


theorem leaf_66_1_4 (hp : 4 < (Q2.transData.getD 1 []).length)
    (j : Nat) (hj : j < (repChars.getD 66 []).length)
    (hq : (normIsRep.getD 66 []).getD j false = true) :
    species (Q2.reps (⟨1, by decide⟩ : Fin 148)) (colE2 ⟨1, by decide⟩ 4 hp)
        (rowE2 (⟨66, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨1, by decide⟩ : Fin 148))
        (colE1 ⟨1, by decide⟩ 4 (transLenTr ⟨1, by decide⟩ 4 hp))
        (rowE1 (⟨66, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨66, by decide⟩ : Fin 148) ⟨1, by decide⟩ _
      (validAt ⟨66, by decide⟩ (listedAt ⟨66, by decide⟩ hj))
      (colE1 ⟨1, by decide⟩ 4 (transLenTr ⟨1, by decide⟩ 4 hp)) T66_1
      hfix66_1 hinj66_1 hcardT66_1
      (fun i => conj_mem_of_fixedPoints _ _ (T66_1 i) (hfix66_1 i) _)
      ⟨66, by decide⟩ ⟨1, by decide⟩ _
      (Q2.validAt ⟨66, by decide⟩ (Q2.listedAt ⟨66, by decide⟩
        (alnCheck_rep ⟨66, by decide⟩ hj hq).1))
      (colE2 ⟨1, by decide⟩ 4 hp) Q2.T66_1_2 Q2.hfix66_1_2 Q2.hinj66_1_2
      Q2.hcardT66_1_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T66_1_2 i) (Q2.hfix66_1_2 i) _)
      colCert_66_1_4.hD ?_).symm
  rw [alnId_66 j hj]


theorem leaf_66_12_0 (hp : 0 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 66 []).length)
    (hq : (normIsRep.getD 66 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 0 hp)
        (rowE2 (⟨66, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp))
        (rowE1 (⟨66, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨66, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨66, by decide⟩ (listedAt ⟨66, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp)) T66_12
      hfix66_12 hinj66_12 hcardT66_12
      (fun i => conj_mem_of_fixedPoints _ _ (T66_12 i) (hfix66_12 i) _)
      ⟨66, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨66, by decide⟩ (Q2.listedAt ⟨66, by decide⟩
        (alnCheck_rep ⟨66, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 0 hp) Q2.T66_12_2 Q2.hfix66_12_2 Q2.hinj66_12_2
      Q2.hcardT66_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T66_12_2 i) (Q2.hfix66_12_2 i) _)
      colCert_66_12_0.hD ?_).symm
  rw [alnId_66 j hj]


theorem leaf_66_12_1 (hp : 1 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 66 []).length)
    (hq : (normIsRep.getD 66 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 1 hp)
        (rowE2 (⟨66, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp))
        (rowE1 (⟨66, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨66, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨66, by decide⟩ (listedAt ⟨66, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp)) T66_12
      hfix66_12 hinj66_12 hcardT66_12
      (fun i => conj_mem_of_fixedPoints _ _ (T66_12 i) (hfix66_12 i) _)
      ⟨66, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨66, by decide⟩ (Q2.listedAt ⟨66, by decide⟩
        (alnCheck_rep ⟨66, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 1 hp) Q2.T66_12_2 Q2.hfix66_12_2 Q2.hinj66_12_2
      Q2.hcardT66_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T66_12_2 i) (Q2.hfix66_12_2 i) _)
      colCert_66_12_1.hD ?_).symm
  rw [alnId_66 j hj]


theorem leaf_66_12_2 (hp : 2 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 66 []).length)
    (hq : (normIsRep.getD 66 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 2 hp)
        (rowE2 (⟨66, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp))
        (rowE1 (⟨66, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨66, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨66, by decide⟩ (listedAt ⟨66, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp)) T66_12
      hfix66_12 hinj66_12 hcardT66_12
      (fun i => conj_mem_of_fixedPoints _ _ (T66_12 i) (hfix66_12 i) _)
      ⟨66, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨66, by decide⟩ (Q2.listedAt ⟨66, by decide⟩
        (alnCheck_rep ⟨66, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 2 hp) Q2.T66_12_2 Q2.hfix66_12_2 Q2.hinj66_12_2
      Q2.hcardT66_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T66_12_2 i) (Q2.hfix66_12_2 i) _)
      colCert_66_12_2.hD ?_).symm
  rw [alnId_66 j hj]


theorem leaf_66_12_3 (hp : 3 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 66 []).length)
    (hq : (normIsRep.getD 66 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 3 hp)
        (rowE2 (⟨66, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp))
        (rowE1 (⟨66, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨66, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨66, by decide⟩ (listedAt ⟨66, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp)) T66_12
      hfix66_12 hinj66_12 hcardT66_12
      (fun i => conj_mem_of_fixedPoints _ _ (T66_12 i) (hfix66_12 i) _)
      ⟨66, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨66, by decide⟩ (Q2.listedAt ⟨66, by decide⟩
        (alnCheck_rep ⟨66, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 3 hp) Q2.T66_12_2 Q2.hfix66_12_2 Q2.hinj66_12_2
      Q2.hcardT66_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T66_12_2 i) (Q2.hfix66_12_2 i) _)
      colCert_66_12_3.hD ?_).symm
  rw [alnId_66 j hj]


theorem leaf_66_12_4 (hp : 4 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 66 []).length)
    (hq : (normIsRep.getD 66 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 4 hp)
        (rowE2 (⟨66, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp))
        (rowE1 (⟨66, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨66, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨66, by decide⟩ (listedAt ⟨66, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp)) T66_12
      hfix66_12 hinj66_12 hcardT66_12
      (fun i => conj_mem_of_fixedPoints _ _ (T66_12 i) (hfix66_12 i) _)
      ⟨66, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨66, by decide⟩ (Q2.listedAt ⟨66, by decide⟩
        (alnCheck_rep ⟨66, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 4 hp) Q2.T66_12_2 Q2.hfix66_12_2 Q2.hinj66_12_2
      Q2.hcardT66_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T66_12_2 i) (Q2.hfix66_12_2 i) _)
      colCert_66_12_4.hD ?_).symm
  rw [alnId_66 j hj]


theorem leaf_66_19_0 (hp : 0 < (Q2.transData.getD 19 []).length)
    (j : Nat) (hj : j < (repChars.getD 66 []).length)
    (hq : (normIsRep.getD 66 []).getD j false = true) :
    species (Q2.reps (⟨19, by decide⟩ : Fin 148)) (colE2 ⟨19, by decide⟩ 0 hp)
        (rowE2 (⟨66, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨19, by decide⟩ : Fin 148))
        (colE1 ⟨19, by decide⟩ 0 (transLenTr ⟨19, by decide⟩ 0 hp))
        (rowE1 (⟨66, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨66, by decide⟩ : Fin 148) ⟨19, by decide⟩ _
      (validAt ⟨66, by decide⟩ (listedAt ⟨66, by decide⟩ hj))
      (colE1 ⟨19, by decide⟩ 0 (transLenTr ⟨19, by decide⟩ 0 hp)) T66_19
      hfix66_19 hinj66_19 hcardT66_19
      (fun i => conj_mem_of_fixedPoints _ _ (T66_19 i) (hfix66_19 i) _)
      ⟨66, by decide⟩ ⟨19, by decide⟩ _
      (Q2.validAt ⟨66, by decide⟩ (Q2.listedAt ⟨66, by decide⟩
        (alnCheck_rep ⟨66, by decide⟩ hj hq).1))
      (colE2 ⟨19, by decide⟩ 0 hp) Q2.T66_19_2 Q2.hfix66_19_2 Q2.hinj66_19_2
      Q2.hcardT66_19_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T66_19_2 i) (Q2.hfix66_19_2 i) _)
      colCert_66_19_0.hD ?_).symm
  rw [alnId_66 j hj]


theorem leaf_66_19_1 (hp : 1 < (Q2.transData.getD 19 []).length)
    (j : Nat) (hj : j < (repChars.getD 66 []).length)
    (hq : (normIsRep.getD 66 []).getD j false = true) :
    species (Q2.reps (⟨19, by decide⟩ : Fin 148)) (colE2 ⟨19, by decide⟩ 1 hp)
        (rowE2 (⟨66, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨19, by decide⟩ : Fin 148))
        (colE1 ⟨19, by decide⟩ 1 (transLenTr ⟨19, by decide⟩ 1 hp))
        (rowE1 (⟨66, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨66, by decide⟩ : Fin 148) ⟨19, by decide⟩ _
      (validAt ⟨66, by decide⟩ (listedAt ⟨66, by decide⟩ hj))
      (colE1 ⟨19, by decide⟩ 1 (transLenTr ⟨19, by decide⟩ 1 hp)) T66_19
      hfix66_19 hinj66_19 hcardT66_19
      (fun i => conj_mem_of_fixedPoints _ _ (T66_19 i) (hfix66_19 i) _)
      ⟨66, by decide⟩ ⟨19, by decide⟩ _
      (Q2.validAt ⟨66, by decide⟩ (Q2.listedAt ⟨66, by decide⟩
        (alnCheck_rep ⟨66, by decide⟩ hj hq).1))
      (colE2 ⟨19, by decide⟩ 1 hp) Q2.T66_19_2 Q2.hfix66_19_2 Q2.hinj66_19_2
      Q2.hcardT66_19_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T66_19_2 i) (Q2.hfix66_19_2 i) _)
      colCert_66_19_1.hD ?_).symm
  rw [alnId_66 j hj]


theorem leaf_66_19_2 (hp : 2 < (Q2.transData.getD 19 []).length)
    (j : Nat) (hj : j < (repChars.getD 66 []).length)
    (hq : (normIsRep.getD 66 []).getD j false = true) :
    species (Q2.reps (⟨19, by decide⟩ : Fin 148)) (colE2 ⟨19, by decide⟩ 2 hp)
        (rowE2 (⟨66, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨19, by decide⟩ : Fin 148))
        (colE1 ⟨19, by decide⟩ 2 (transLenTr ⟨19, by decide⟩ 2 hp))
        (rowE1 (⟨66, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨66, by decide⟩ : Fin 148) ⟨19, by decide⟩ _
      (validAt ⟨66, by decide⟩ (listedAt ⟨66, by decide⟩ hj))
      (colE1 ⟨19, by decide⟩ 2 (transLenTr ⟨19, by decide⟩ 2 hp)) T66_19
      hfix66_19 hinj66_19 hcardT66_19
      (fun i => conj_mem_of_fixedPoints _ _ (T66_19 i) (hfix66_19 i) _)
      ⟨66, by decide⟩ ⟨19, by decide⟩ _
      (Q2.validAt ⟨66, by decide⟩ (Q2.listedAt ⟨66, by decide⟩
        (alnCheck_rep ⟨66, by decide⟩ hj hq).1))
      (colE2 ⟨19, by decide⟩ 2 hp) Q2.T66_19_2 Q2.hfix66_19_2 Q2.hinj66_19_2
      Q2.hcardT66_19_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T66_19_2 i) (Q2.hfix66_19_2 i) _)
      colCert_66_19_2.hD ?_).symm
  rw [alnId_66 j hj]


theorem leaf_66_19_3 (hp : 3 < (Q2.transData.getD 19 []).length)
    (j : Nat) (hj : j < (repChars.getD 66 []).length)
    (hq : (normIsRep.getD 66 []).getD j false = true) :
    species (Q2.reps (⟨19, by decide⟩ : Fin 148)) (colE2 ⟨19, by decide⟩ 3 hp)
        (rowE2 (⟨66, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨19, by decide⟩ : Fin 148))
        (colE1 ⟨19, by decide⟩ 3 (transLenTr ⟨19, by decide⟩ 3 hp))
        (rowE1 (⟨66, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨66, by decide⟩ : Fin 148) ⟨19, by decide⟩ _
      (validAt ⟨66, by decide⟩ (listedAt ⟨66, by decide⟩ hj))
      (colE1 ⟨19, by decide⟩ 3 (transLenTr ⟨19, by decide⟩ 3 hp)) T66_19
      hfix66_19 hinj66_19 hcardT66_19
      (fun i => conj_mem_of_fixedPoints _ _ (T66_19 i) (hfix66_19 i) _)
      ⟨66, by decide⟩ ⟨19, by decide⟩ _
      (Q2.validAt ⟨66, by decide⟩ (Q2.listedAt ⟨66, by decide⟩
        (alnCheck_rep ⟨66, by decide⟩ hj hq).1))
      (colE2 ⟨19, by decide⟩ 3 hp) Q2.T66_19_2 Q2.hfix66_19_2 Q2.hinj66_19_2
      Q2.hcardT66_19_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T66_19_2 i) (Q2.hfix66_19_2 i) _)
      colCert_66_19_3.hD ?_).symm
  rw [alnId_66 j hj]


theorem leaf_66_19_4 (hp : 4 < (Q2.transData.getD 19 []).length)
    (j : Nat) (hj : j < (repChars.getD 66 []).length)
    (hq : (normIsRep.getD 66 []).getD j false = true) :
    species (Q2.reps (⟨19, by decide⟩ : Fin 148)) (colE2 ⟨19, by decide⟩ 4 hp)
        (rowE2 (⟨66, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨19, by decide⟩ : Fin 148))
        (colE1 ⟨19, by decide⟩ 4 (transLenTr ⟨19, by decide⟩ 4 hp))
        (rowE1 (⟨66, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨66, by decide⟩ : Fin 148) ⟨19, by decide⟩ _
      (validAt ⟨66, by decide⟩ (listedAt ⟨66, by decide⟩ hj))
      (colE1 ⟨19, by decide⟩ 4 (transLenTr ⟨19, by decide⟩ 4 hp)) T66_19
      hfix66_19 hinj66_19 hcardT66_19
      (fun i => conj_mem_of_fixedPoints _ _ (T66_19 i) (hfix66_19 i) _)
      ⟨66, by decide⟩ ⟨19, by decide⟩ _
      (Q2.validAt ⟨66, by decide⟩ (Q2.listedAt ⟨66, by decide⟩
        (alnCheck_rep ⟨66, by decide⟩ hj hq).1))
      (colE2 ⟨19, by decide⟩ 4 hp) Q2.T66_19_2 Q2.hfix66_19_2 Q2.hinj66_19_2
      Q2.hcardT66_19_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T66_19_2 i) (Q2.hfix66_19_2 i) _)
      colCert_66_19_4.hD ?_).symm
  rw [alnId_66 j hj]


theorem leaf_66_19_5 (hp : 5 < (Q2.transData.getD 19 []).length)
    (j : Nat) (hj : j < (repChars.getD 66 []).length)
    (hq : (normIsRep.getD 66 []).getD j false = true) :
    species (Q2.reps (⟨19, by decide⟩ : Fin 148)) (colE2 ⟨19, by decide⟩ 5 hp)
        (rowE2 (⟨66, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨19, by decide⟩ : Fin 148))
        (colE1 ⟨19, by decide⟩ 5 (transLenTr ⟨19, by decide⟩ 5 hp))
        (rowE1 (⟨66, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨66, by decide⟩ : Fin 148) ⟨19, by decide⟩ _
      (validAt ⟨66, by decide⟩ (listedAt ⟨66, by decide⟩ hj))
      (colE1 ⟨19, by decide⟩ 5 (transLenTr ⟨19, by decide⟩ 5 hp)) T66_19
      hfix66_19 hinj66_19 hcardT66_19
      (fun i => conj_mem_of_fixedPoints _ _ (T66_19 i) (hfix66_19 i) _)
      ⟨66, by decide⟩ ⟨19, by decide⟩ _
      (Q2.validAt ⟨66, by decide⟩ (Q2.listedAt ⟨66, by decide⟩
        (alnCheck_rep ⟨66, by decide⟩ hj hq).1))
      (colE2 ⟨19, by decide⟩ 5 hp) Q2.T66_19_2 Q2.hfix66_19_2 Q2.hinj66_19_2
      Q2.hcardT66_19_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T66_19_2 i) (Q2.hfix66_19_2 i) _)
      colCert_66_19_5.hD ?_).symm
  rw [alnId_66 j hj]


theorem leaf_66_19_10 (hp : 10 < (Q2.transData.getD 19 []).length)
    (j : Nat) (hj : j < (repChars.getD 66 []).length)
    (hq : (normIsRep.getD 66 []).getD j false = true) :
    species (Q2.reps (⟨19, by decide⟩ : Fin 148)) (colE2 ⟨19, by decide⟩ 10 hp)
        (rowE2 (⟨66, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨19, by decide⟩ : Fin 148))
        (colE1 ⟨19, by decide⟩ 10 (transLenTr ⟨19, by decide⟩ 10 hp))
        (rowE1 (⟨66, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨66, by decide⟩ : Fin 148) ⟨19, by decide⟩ _
      (validAt ⟨66, by decide⟩ (listedAt ⟨66, by decide⟩ hj))
      (colE1 ⟨19, by decide⟩ 10 (transLenTr ⟨19, by decide⟩ 10 hp)) T66_19
      hfix66_19 hinj66_19 hcardT66_19
      (fun i => conj_mem_of_fixedPoints _ _ (T66_19 i) (hfix66_19 i) _)
      ⟨66, by decide⟩ ⟨19, by decide⟩ _
      (Q2.validAt ⟨66, by decide⟩ (Q2.listedAt ⟨66, by decide⟩
        (alnCheck_rep ⟨66, by decide⟩ hj hq).1))
      (colE2 ⟨19, by decide⟩ 10 hp) Q2.T66_19_2 Q2.hfix66_19_2 Q2.hinj66_19_2
      Q2.hcardT66_19_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T66_19_2 i) (Q2.hfix66_19_2 i) _)
      colCert_66_19_10.hD ?_).symm
  rw [alnId_66 j hj]


theorem leaf_66_19_15 (hp : 15 < (Q2.transData.getD 19 []).length)
    (j : Nat) (hj : j < (repChars.getD 66 []).length)
    (hq : (normIsRep.getD 66 []).getD j false = true) :
    species (Q2.reps (⟨19, by decide⟩ : Fin 148)) (colE2 ⟨19, by decide⟩ 15 hp)
        (rowE2 (⟨66, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨19, by decide⟩ : Fin 148))
        (colE1 ⟨19, by decide⟩ 15 (transLenTr ⟨19, by decide⟩ 15 hp))
        (rowE1 (⟨66, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨66, by decide⟩ : Fin 148) ⟨19, by decide⟩ _
      (validAt ⟨66, by decide⟩ (listedAt ⟨66, by decide⟩ hj))
      (colE1 ⟨19, by decide⟩ 15 (transLenTr ⟨19, by decide⟩ 15 hp)) T66_19
      hfix66_19 hinj66_19 hcardT66_19
      (fun i => conj_mem_of_fixedPoints _ _ (T66_19 i) (hfix66_19 i) _)
      ⟨66, by decide⟩ ⟨19, by decide⟩ _
      (Q2.validAt ⟨66, by decide⟩ (Q2.listedAt ⟨66, by decide⟩
        (alnCheck_rep ⟨66, by decide⟩ hj hq).1))
      (colE2 ⟨19, by decide⟩ 15 hp) Q2.T66_19_2 Q2.hfix66_19_2 Q2.hinj66_19_2
      Q2.hcardT66_19_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T66_19_2 i) (Q2.hfix66_19_2 i) _)
      colCert_66_19_15.hD ?_).symm
  rw [alnId_66 j hj]


theorem leaf_66_19_20 (hp : 20 < (Q2.transData.getD 19 []).length)
    (j : Nat) (hj : j < (repChars.getD 66 []).length)
    (hq : (normIsRep.getD 66 []).getD j false = true) :
    species (Q2.reps (⟨19, by decide⟩ : Fin 148)) (colE2 ⟨19, by decide⟩ 20 hp)
        (rowE2 (⟨66, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨19, by decide⟩ : Fin 148))
        (colE1 ⟨19, by decide⟩ 20 (transLenTr ⟨19, by decide⟩ 20 hp))
        (rowE1 (⟨66, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨66, by decide⟩ : Fin 148) ⟨19, by decide⟩ _
      (validAt ⟨66, by decide⟩ (listedAt ⟨66, by decide⟩ hj))
      (colE1 ⟨19, by decide⟩ 20 (transLenTr ⟨19, by decide⟩ 20 hp)) T66_19
      hfix66_19 hinj66_19 hcardT66_19
      (fun i => conj_mem_of_fixedPoints _ _ (T66_19 i) (hfix66_19 i) _)
      ⟨66, by decide⟩ ⟨19, by decide⟩ _
      (Q2.validAt ⟨66, by decide⟩ (Q2.listedAt ⟨66, by decide⟩
        (alnCheck_rep ⟨66, by decide⟩ hj hq).1))
      (colE2 ⟨19, by decide⟩ 20 hp) Q2.T66_19_2 Q2.hfix66_19_2 Q2.hinj66_19_2
      Q2.hcardT66_19_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T66_19_2 i) (Q2.hfix66_19_2 i) _)
      colCert_66_19_20.hD ?_).symm
  rw [alnId_66 j hj]


theorem leaf_66_30_0 (hp : 0 < (Q2.transData.getD 30 []).length)
    (j : Nat) (hj : j < (repChars.getD 66 []).length)
    (hq : (normIsRep.getD 66 []).getD j false = true) :
    species (Q2.reps (⟨30, by decide⟩ : Fin 148)) (colE2 ⟨30, by decide⟩ 0 hp)
        (rowE2 (⟨66, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨30, by decide⟩ : Fin 148))
        (colE1 ⟨30, by decide⟩ 0 (transLenTr ⟨30, by decide⟩ 0 hp))
        (rowE1 (⟨66, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨66, by decide⟩ : Fin 148) ⟨30, by decide⟩ _
      (validAt ⟨66, by decide⟩ (listedAt ⟨66, by decide⟩ hj))
      (colE1 ⟨30, by decide⟩ 0 (transLenTr ⟨30, by decide⟩ 0 hp)) T66_30
      hfix66_30 hinj66_30 hcardT66_30
      (fun i => conj_mem_of_fixedPoints _ _ (T66_30 i) (hfix66_30 i) _)
      ⟨66, by decide⟩ ⟨30, by decide⟩ _
      (Q2.validAt ⟨66, by decide⟩ (Q2.listedAt ⟨66, by decide⟩
        (alnCheck_rep ⟨66, by decide⟩ hj hq).1))
      (colE2 ⟨30, by decide⟩ 0 hp) Q2.T66_30_2 Q2.hfix66_30_2 Q2.hinj66_30_2
      Q2.hcardT66_30_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T66_30_2 i) (Q2.hfix66_30_2 i) _)
      colCert_66_30_0.hD ?_).symm
  rw [alnId_66 j hj]


theorem leaf_66_30_1 (hp : 1 < (Q2.transData.getD 30 []).length)
    (j : Nat) (hj : j < (repChars.getD 66 []).length)
    (hq : (normIsRep.getD 66 []).getD j false = true) :
    species (Q2.reps (⟨30, by decide⟩ : Fin 148)) (colE2 ⟨30, by decide⟩ 1 hp)
        (rowE2 (⟨66, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨30, by decide⟩ : Fin 148))
        (colE1 ⟨30, by decide⟩ 1 (transLenTr ⟨30, by decide⟩ 1 hp))
        (rowE1 (⟨66, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨66, by decide⟩ : Fin 148) ⟨30, by decide⟩ _
      (validAt ⟨66, by decide⟩ (listedAt ⟨66, by decide⟩ hj))
      (colE1 ⟨30, by decide⟩ 1 (transLenTr ⟨30, by decide⟩ 1 hp)) T66_30
      hfix66_30 hinj66_30 hcardT66_30
      (fun i => conj_mem_of_fixedPoints _ _ (T66_30 i) (hfix66_30 i) _)
      ⟨66, by decide⟩ ⟨30, by decide⟩ _
      (Q2.validAt ⟨66, by decide⟩ (Q2.listedAt ⟨66, by decide⟩
        (alnCheck_rep ⟨66, by decide⟩ hj hq).1))
      (colE2 ⟨30, by decide⟩ 1 hp) Q2.T66_30_2 Q2.hfix66_30_2 Q2.hinj66_30_2
      Q2.hcardT66_30_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T66_30_2 i) (Q2.hfix66_30_2 i) _)
      colCert_66_30_1.hD ?_).symm
  rw [alnId_66 j hj]


theorem leaf_66_30_2 (hp : 2 < (Q2.transData.getD 30 []).length)
    (j : Nat) (hj : j < (repChars.getD 66 []).length)
    (hq : (normIsRep.getD 66 []).getD j false = true) :
    species (Q2.reps (⟨30, by decide⟩ : Fin 148)) (colE2 ⟨30, by decide⟩ 2 hp)
        (rowE2 (⟨66, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨30, by decide⟩ : Fin 148))
        (colE1 ⟨30, by decide⟩ 2 (transLenTr ⟨30, by decide⟩ 2 hp))
        (rowE1 (⟨66, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨66, by decide⟩ : Fin 148) ⟨30, by decide⟩ _
      (validAt ⟨66, by decide⟩ (listedAt ⟨66, by decide⟩ hj))
      (colE1 ⟨30, by decide⟩ 2 (transLenTr ⟨30, by decide⟩ 2 hp)) T66_30
      hfix66_30 hinj66_30 hcardT66_30
      (fun i => conj_mem_of_fixedPoints _ _ (T66_30 i) (hfix66_30 i) _)
      ⟨66, by decide⟩ ⟨30, by decide⟩ _
      (Q2.validAt ⟨66, by decide⟩ (Q2.listedAt ⟨66, by decide⟩
        (alnCheck_rep ⟨66, by decide⟩ hj hq).1))
      (colE2 ⟨30, by decide⟩ 2 hp) Q2.T66_30_2 Q2.hfix66_30_2 Q2.hinj66_30_2
      Q2.hcardT66_30_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T66_30_2 i) (Q2.hfix66_30_2 i) _)
      colCert_66_30_2.hD ?_).symm
  rw [alnId_66 j hj]


theorem leaf_66_30_3 (hp : 3 < (Q2.transData.getD 30 []).length)
    (j : Nat) (hj : j < (repChars.getD 66 []).length)
    (hq : (normIsRep.getD 66 []).getD j false = true) :
    species (Q2.reps (⟨30, by decide⟩ : Fin 148)) (colE2 ⟨30, by decide⟩ 3 hp)
        (rowE2 (⟨66, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨30, by decide⟩ : Fin 148))
        (colE1 ⟨30, by decide⟩ 3 (transLenTr ⟨30, by decide⟩ 3 hp))
        (rowE1 (⟨66, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨66, by decide⟩ : Fin 148) ⟨30, by decide⟩ _
      (validAt ⟨66, by decide⟩ (listedAt ⟨66, by decide⟩ hj))
      (colE1 ⟨30, by decide⟩ 3 (transLenTr ⟨30, by decide⟩ 3 hp)) T66_30
      hfix66_30 hinj66_30 hcardT66_30
      (fun i => conj_mem_of_fixedPoints _ _ (T66_30 i) (hfix66_30 i) _)
      ⟨66, by decide⟩ ⟨30, by decide⟩ _
      (Q2.validAt ⟨66, by decide⟩ (Q2.listedAt ⟨66, by decide⟩
        (alnCheck_rep ⟨66, by decide⟩ hj hq).1))
      (colE2 ⟨30, by decide⟩ 3 hp) Q2.T66_30_2 Q2.hfix66_30_2 Q2.hinj66_30_2
      Q2.hcardT66_30_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T66_30_2 i) (Q2.hfix66_30_2 i) _)
      colCert_66_30_3.hD ?_).symm
  rw [alnId_66 j hj]


theorem leaf_66_30_4 (hp : 4 < (Q2.transData.getD 30 []).length)
    (j : Nat) (hj : j < (repChars.getD 66 []).length)
    (hq : (normIsRep.getD 66 []).getD j false = true) :
    species (Q2.reps (⟨30, by decide⟩ : Fin 148)) (colE2 ⟨30, by decide⟩ 4 hp)
        (rowE2 (⟨66, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨30, by decide⟩ : Fin 148))
        (colE1 ⟨30, by decide⟩ 4 (transLenTr ⟨30, by decide⟩ 4 hp))
        (rowE1 (⟨66, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨66, by decide⟩ : Fin 148) ⟨30, by decide⟩ _
      (validAt ⟨66, by decide⟩ (listedAt ⟨66, by decide⟩ hj))
      (colE1 ⟨30, by decide⟩ 4 (transLenTr ⟨30, by decide⟩ 4 hp)) T66_30
      hfix66_30 hinj66_30 hcardT66_30
      (fun i => conj_mem_of_fixedPoints _ _ (T66_30 i) (hfix66_30 i) _)
      ⟨66, by decide⟩ ⟨30, by decide⟩ _
      (Q2.validAt ⟨66, by decide⟩ (Q2.listedAt ⟨66, by decide⟩
        (alnCheck_rep ⟨66, by decide⟩ hj hq).1))
      (colE2 ⟨30, by decide⟩ 4 hp) Q2.T66_30_2 Q2.hfix66_30_2 Q2.hinj66_30_2
      Q2.hcardT66_30_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T66_30_2 i) (Q2.hfix66_30_2 i) _)
      colCert_66_30_4.hD ?_).symm
  rw [alnId_66 j hj]


theorem leaf_66_30_5 (hp : 5 < (Q2.transData.getD 30 []).length)
    (j : Nat) (hj : j < (repChars.getD 66 []).length)
    (hq : (normIsRep.getD 66 []).getD j false = true) :
    species (Q2.reps (⟨30, by decide⟩ : Fin 148)) (colE2 ⟨30, by decide⟩ 5 hp)
        (rowE2 (⟨66, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨30, by decide⟩ : Fin 148))
        (colE1 ⟨30, by decide⟩ 5 (transLenTr ⟨30, by decide⟩ 5 hp))
        (rowE1 (⟨66, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨66, by decide⟩ : Fin 148) ⟨30, by decide⟩ _
      (validAt ⟨66, by decide⟩ (listedAt ⟨66, by decide⟩ hj))
      (colE1 ⟨30, by decide⟩ 5 (transLenTr ⟨30, by decide⟩ 5 hp)) T66_30
      hfix66_30 hinj66_30 hcardT66_30
      (fun i => conj_mem_of_fixedPoints _ _ (T66_30 i) (hfix66_30 i) _)
      ⟨66, by decide⟩ ⟨30, by decide⟩ _
      (Q2.validAt ⟨66, by decide⟩ (Q2.listedAt ⟨66, by decide⟩
        (alnCheck_rep ⟨66, by decide⟩ hj hq).1))
      (colE2 ⟨30, by decide⟩ 5 hp) Q2.T66_30_2 Q2.hfix66_30_2 Q2.hinj66_30_2
      Q2.hcardT66_30_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T66_30_2 i) (Q2.hfix66_30_2 i) _)
      colCert_66_30_5.hD ?_).symm
  rw [alnId_66 j hj]


theorem leaf_66_30_10 (hp : 10 < (Q2.transData.getD 30 []).length)
    (j : Nat) (hj : j < (repChars.getD 66 []).length)
    (hq : (normIsRep.getD 66 []).getD j false = true) :
    species (Q2.reps (⟨30, by decide⟩ : Fin 148)) (colE2 ⟨30, by decide⟩ 10 hp)
        (rowE2 (⟨66, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨30, by decide⟩ : Fin 148))
        (colE1 ⟨30, by decide⟩ 10 (transLenTr ⟨30, by decide⟩ 10 hp))
        (rowE1 (⟨66, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨66, by decide⟩ : Fin 148) ⟨30, by decide⟩ _
      (validAt ⟨66, by decide⟩ (listedAt ⟨66, by decide⟩ hj))
      (colE1 ⟨30, by decide⟩ 10 (transLenTr ⟨30, by decide⟩ 10 hp)) T66_30
      hfix66_30 hinj66_30 hcardT66_30
      (fun i => conj_mem_of_fixedPoints _ _ (T66_30 i) (hfix66_30 i) _)
      ⟨66, by decide⟩ ⟨30, by decide⟩ _
      (Q2.validAt ⟨66, by decide⟩ (Q2.listedAt ⟨66, by decide⟩
        (alnCheck_rep ⟨66, by decide⟩ hj hq).1))
      (colE2 ⟨30, by decide⟩ 10 hp) Q2.T66_30_2 Q2.hfix66_30_2 Q2.hinj66_30_2
      Q2.hcardT66_30_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T66_30_2 i) (Q2.hfix66_30_2 i) _)
      colCert_66_30_10.hD ?_).symm
  rw [alnId_66 j hj]


theorem leaf_66_30_15 (hp : 15 < (Q2.transData.getD 30 []).length)
    (j : Nat) (hj : j < (repChars.getD 66 []).length)
    (hq : (normIsRep.getD 66 []).getD j false = true) :
    species (Q2.reps (⟨30, by decide⟩ : Fin 148)) (colE2 ⟨30, by decide⟩ 15 hp)
        (rowE2 (⟨66, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨30, by decide⟩ : Fin 148))
        (colE1 ⟨30, by decide⟩ 15 (transLenTr ⟨30, by decide⟩ 15 hp))
        (rowE1 (⟨66, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨66, by decide⟩ : Fin 148) ⟨30, by decide⟩ _
      (validAt ⟨66, by decide⟩ (listedAt ⟨66, by decide⟩ hj))
      (colE1 ⟨30, by decide⟩ 15 (transLenTr ⟨30, by decide⟩ 15 hp)) T66_30
      hfix66_30 hinj66_30 hcardT66_30
      (fun i => conj_mem_of_fixedPoints _ _ (T66_30 i) (hfix66_30 i) _)
      ⟨66, by decide⟩ ⟨30, by decide⟩ _
      (Q2.validAt ⟨66, by decide⟩ (Q2.listedAt ⟨66, by decide⟩
        (alnCheck_rep ⟨66, by decide⟩ hj hq).1))
      (colE2 ⟨30, by decide⟩ 15 hp) Q2.T66_30_2 Q2.hfix66_30_2 Q2.hinj66_30_2
      Q2.hcardT66_30_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T66_30_2 i) (Q2.hfix66_30_2 i) _)
      colCert_66_30_15.hD ?_).symm
  rw [alnId_66 j hj]


theorem leaf_66_30_20 (hp : 20 < (Q2.transData.getD 30 []).length)
    (j : Nat) (hj : j < (repChars.getD 66 []).length)
    (hq : (normIsRep.getD 66 []).getD j false = true) :
    species (Q2.reps (⟨30, by decide⟩ : Fin 148)) (colE2 ⟨30, by decide⟩ 20 hp)
        (rowE2 (⟨66, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨30, by decide⟩ : Fin 148))
        (colE1 ⟨30, by decide⟩ 20 (transLenTr ⟨30, by decide⟩ 20 hp))
        (rowE1 (⟨66, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨66, by decide⟩ : Fin 148) ⟨30, by decide⟩ _
      (validAt ⟨66, by decide⟩ (listedAt ⟨66, by decide⟩ hj))
      (colE1 ⟨30, by decide⟩ 20 (transLenTr ⟨30, by decide⟩ 20 hp)) T66_30
      hfix66_30 hinj66_30 hcardT66_30
      (fun i => conj_mem_of_fixedPoints _ _ (T66_30 i) (hfix66_30 i) _)
      ⟨66, by decide⟩ ⟨30, by decide⟩ _
      (Q2.validAt ⟨66, by decide⟩ (Q2.listedAt ⟨66, by decide⟩
        (alnCheck_rep ⟨66, by decide⟩ hj hq).1))
      (colE2 ⟨30, by decide⟩ 20 hp) Q2.T66_30_2 Q2.hfix66_30_2 Q2.hinj66_30_2
      Q2.hcardT66_30_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T66_30_2 i) (Q2.hfix66_30_2 i) _)
      colCert_66_30_20.hD ?_).symm
  rw [alnId_66 j hj]


theorem leaf_66_35_0 (hp : 0 < (Q2.transData.getD 35 []).length)
    (j : Nat) (hj : j < (repChars.getD 66 []).length)
    (hq : (normIsRep.getD 66 []).getD j false = true) :
    species (Q2.reps (⟨35, by decide⟩ : Fin 148)) (colE2 ⟨35, by decide⟩ 0 hp)
        (rowE2 (⟨66, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨35, by decide⟩ : Fin 148))
        (colE1 ⟨35, by decide⟩ 0 (transLenTr ⟨35, by decide⟩ 0 hp))
        (rowE1 (⟨66, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨66, by decide⟩ : Fin 148) ⟨35, by decide⟩ _
      (validAt ⟨66, by decide⟩ (listedAt ⟨66, by decide⟩ hj))
      (colE1 ⟨35, by decide⟩ 0 (transLenTr ⟨35, by decide⟩ 0 hp)) T66_35
      hfix66_35 hinj66_35 hcardT66_35
      (fun i => conj_mem_of_fixedPoints _ _ (T66_35 i) (hfix66_35 i) _)
      ⟨66, by decide⟩ ⟨35, by decide⟩ _
      (Q2.validAt ⟨66, by decide⟩ (Q2.listedAt ⟨66, by decide⟩
        (alnCheck_rep ⟨66, by decide⟩ hj hq).1))
      (colE2 ⟨35, by decide⟩ 0 hp) Q2.T66_35_2 Q2.hfix66_35_2 Q2.hinj66_35_2
      Q2.hcardT66_35_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T66_35_2 i) (Q2.hfix66_35_2 i) _)
      colCert_66_35_0.hD ?_).symm
  rw [alnId_66 j hj]


theorem leaf_66_35_1 (hp : 1 < (Q2.transData.getD 35 []).length)
    (j : Nat) (hj : j < (repChars.getD 66 []).length)
    (hq : (normIsRep.getD 66 []).getD j false = true) :
    species (Q2.reps (⟨35, by decide⟩ : Fin 148)) (colE2 ⟨35, by decide⟩ 1 hp)
        (rowE2 (⟨66, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨35, by decide⟩ : Fin 148))
        (colE1 ⟨35, by decide⟩ 1 (transLenTr ⟨35, by decide⟩ 1 hp))
        (rowE1 (⟨66, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨66, by decide⟩ : Fin 148) ⟨35, by decide⟩ _
      (validAt ⟨66, by decide⟩ (listedAt ⟨66, by decide⟩ hj))
      (colE1 ⟨35, by decide⟩ 1 (transLenTr ⟨35, by decide⟩ 1 hp)) T66_35
      hfix66_35 hinj66_35 hcardT66_35
      (fun i => conj_mem_of_fixedPoints _ _ (T66_35 i) (hfix66_35 i) _)
      ⟨66, by decide⟩ ⟨35, by decide⟩ _
      (Q2.validAt ⟨66, by decide⟩ (Q2.listedAt ⟨66, by decide⟩
        (alnCheck_rep ⟨66, by decide⟩ hj hq).1))
      (colE2 ⟨35, by decide⟩ 1 hp) Q2.T66_35_2 Q2.hfix66_35_2 Q2.hinj66_35_2
      Q2.hcardT66_35_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T66_35_2 i) (Q2.hfix66_35_2 i) _)
      colCert_66_35_1.hD ?_).symm
  rw [alnId_66 j hj]


theorem leaf_66_35_2 (hp : 2 < (Q2.transData.getD 35 []).length)
    (j : Nat) (hj : j < (repChars.getD 66 []).length)
    (hq : (normIsRep.getD 66 []).getD j false = true) :
    species (Q2.reps (⟨35, by decide⟩ : Fin 148)) (colE2 ⟨35, by decide⟩ 2 hp)
        (rowE2 (⟨66, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨35, by decide⟩ : Fin 148))
        (colE1 ⟨35, by decide⟩ 2 (transLenTr ⟨35, by decide⟩ 2 hp))
        (rowE1 (⟨66, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨66, by decide⟩ : Fin 148) ⟨35, by decide⟩ _
      (validAt ⟨66, by decide⟩ (listedAt ⟨66, by decide⟩ hj))
      (colE1 ⟨35, by decide⟩ 2 (transLenTr ⟨35, by decide⟩ 2 hp)) T66_35
      hfix66_35 hinj66_35 hcardT66_35
      (fun i => conj_mem_of_fixedPoints _ _ (T66_35 i) (hfix66_35 i) _)
      ⟨66, by decide⟩ ⟨35, by decide⟩ _
      (Q2.validAt ⟨66, by decide⟩ (Q2.listedAt ⟨66, by decide⟩
        (alnCheck_rep ⟨66, by decide⟩ hj hq).1))
      (colE2 ⟨35, by decide⟩ 2 hp) Q2.T66_35_2 Q2.hfix66_35_2 Q2.hinj66_35_2
      Q2.hcardT66_35_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T66_35_2 i) (Q2.hfix66_35_2 i) _)
      colCert_66_35_2.hD ?_).symm
  rw [alnId_66 j hj]


theorem leaf_66_35_3 (hp : 3 < (Q2.transData.getD 35 []).length)
    (j : Nat) (hj : j < (repChars.getD 66 []).length)
    (hq : (normIsRep.getD 66 []).getD j false = true) :
    species (Q2.reps (⟨35, by decide⟩ : Fin 148)) (colE2 ⟨35, by decide⟩ 3 hp)
        (rowE2 (⟨66, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨35, by decide⟩ : Fin 148))
        (colE1 ⟨35, by decide⟩ 3 (transLenTr ⟨35, by decide⟩ 3 hp))
        (rowE1 (⟨66, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨66, by decide⟩ : Fin 148) ⟨35, by decide⟩ _
      (validAt ⟨66, by decide⟩ (listedAt ⟨66, by decide⟩ hj))
      (colE1 ⟨35, by decide⟩ 3 (transLenTr ⟨35, by decide⟩ 3 hp)) T66_35
      hfix66_35 hinj66_35 hcardT66_35
      (fun i => conj_mem_of_fixedPoints _ _ (T66_35 i) (hfix66_35 i) _)
      ⟨66, by decide⟩ ⟨35, by decide⟩ _
      (Q2.validAt ⟨66, by decide⟩ (Q2.listedAt ⟨66, by decide⟩
        (alnCheck_rep ⟨66, by decide⟩ hj hq).1))
      (colE2 ⟨35, by decide⟩ 3 hp) Q2.T66_35_2 Q2.hfix66_35_2 Q2.hinj66_35_2
      Q2.hcardT66_35_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T66_35_2 i) (Q2.hfix66_35_2 i) _)
      colCert_66_35_3.hD ?_).symm
  rw [alnId_66 j hj]


theorem leaf_66_35_4 (hp : 4 < (Q2.transData.getD 35 []).length)
    (j : Nat) (hj : j < (repChars.getD 66 []).length)
    (hq : (normIsRep.getD 66 []).getD j false = true) :
    species (Q2.reps (⟨35, by decide⟩ : Fin 148)) (colE2 ⟨35, by decide⟩ 4 hp)
        (rowE2 (⟨66, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨35, by decide⟩ : Fin 148))
        (colE1 ⟨35, by decide⟩ 4 (transLenTr ⟨35, by decide⟩ 4 hp))
        (rowE1 (⟨66, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨66, by decide⟩ : Fin 148) ⟨35, by decide⟩ _
      (validAt ⟨66, by decide⟩ (listedAt ⟨66, by decide⟩ hj))
      (colE1 ⟨35, by decide⟩ 4 (transLenTr ⟨35, by decide⟩ 4 hp)) T66_35
      hfix66_35 hinj66_35 hcardT66_35
      (fun i => conj_mem_of_fixedPoints _ _ (T66_35 i) (hfix66_35 i) _)
      ⟨66, by decide⟩ ⟨35, by decide⟩ _
      (Q2.validAt ⟨66, by decide⟩ (Q2.listedAt ⟨66, by decide⟩
        (alnCheck_rep ⟨66, by decide⟩ hj hq).1))
      (colE2 ⟨35, by decide⟩ 4 hp) Q2.T66_35_2 Q2.hfix66_35_2 Q2.hinj66_35_2
      Q2.hcardT66_35_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T66_35_2 i) (Q2.hfix66_35_2 i) _)
      colCert_66_35_4.hD ?_).symm
  rw [alnId_66 j hj]


theorem leaf_66_35_5 (hp : 5 < (Q2.transData.getD 35 []).length)
    (j : Nat) (hj : j < (repChars.getD 66 []).length)
    (hq : (normIsRep.getD 66 []).getD j false = true) :
    species (Q2.reps (⟨35, by decide⟩ : Fin 148)) (colE2 ⟨35, by decide⟩ 5 hp)
        (rowE2 (⟨66, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨35, by decide⟩ : Fin 148))
        (colE1 ⟨35, by decide⟩ 5 (transLenTr ⟨35, by decide⟩ 5 hp))
        (rowE1 (⟨66, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨66, by decide⟩ : Fin 148) ⟨35, by decide⟩ _
      (validAt ⟨66, by decide⟩ (listedAt ⟨66, by decide⟩ hj))
      (colE1 ⟨35, by decide⟩ 5 (transLenTr ⟨35, by decide⟩ 5 hp)) T66_35
      hfix66_35 hinj66_35 hcardT66_35
      (fun i => conj_mem_of_fixedPoints _ _ (T66_35 i) (hfix66_35 i) _)
      ⟨66, by decide⟩ ⟨35, by decide⟩ _
      (Q2.validAt ⟨66, by decide⟩ (Q2.listedAt ⟨66, by decide⟩
        (alnCheck_rep ⟨66, by decide⟩ hj hq).1))
      (colE2 ⟨35, by decide⟩ 5 hp) Q2.T66_35_2 Q2.hfix66_35_2 Q2.hinj66_35_2
      Q2.hcardT66_35_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T66_35_2 i) (Q2.hfix66_35_2 i) _)
      colCert_66_35_5.hD ?_).symm
  rw [alnId_66 j hj]


theorem leaf_66_35_10 (hp : 10 < (Q2.transData.getD 35 []).length)
    (j : Nat) (hj : j < (repChars.getD 66 []).length)
    (hq : (normIsRep.getD 66 []).getD j false = true) :
    species (Q2.reps (⟨35, by decide⟩ : Fin 148)) (colE2 ⟨35, by decide⟩ 10 hp)
        (rowE2 (⟨66, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨35, by decide⟩ : Fin 148))
        (colE1 ⟨35, by decide⟩ 10 (transLenTr ⟨35, by decide⟩ 10 hp))
        (rowE1 (⟨66, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨66, by decide⟩ : Fin 148) ⟨35, by decide⟩ _
      (validAt ⟨66, by decide⟩ (listedAt ⟨66, by decide⟩ hj))
      (colE1 ⟨35, by decide⟩ 10 (transLenTr ⟨35, by decide⟩ 10 hp)) T66_35
      hfix66_35 hinj66_35 hcardT66_35
      (fun i => conj_mem_of_fixedPoints _ _ (T66_35 i) (hfix66_35 i) _)
      ⟨66, by decide⟩ ⟨35, by decide⟩ _
      (Q2.validAt ⟨66, by decide⟩ (Q2.listedAt ⟨66, by decide⟩
        (alnCheck_rep ⟨66, by decide⟩ hj hq).1))
      (colE2 ⟨35, by decide⟩ 10 hp) Q2.T66_35_2 Q2.hfix66_35_2 Q2.hinj66_35_2
      Q2.hcardT66_35_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T66_35_2 i) (Q2.hfix66_35_2 i) _)
      colCert_66_35_10.hD ?_).symm
  rw [alnId_66 j hj]


theorem leaf_66_35_15 (hp : 15 < (Q2.transData.getD 35 []).length)
    (j : Nat) (hj : j < (repChars.getD 66 []).length)
    (hq : (normIsRep.getD 66 []).getD j false = true) :
    species (Q2.reps (⟨35, by decide⟩ : Fin 148)) (colE2 ⟨35, by decide⟩ 15 hp)
        (rowE2 (⟨66, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨35, by decide⟩ : Fin 148))
        (colE1 ⟨35, by decide⟩ 15 (transLenTr ⟨35, by decide⟩ 15 hp))
        (rowE1 (⟨66, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨66, by decide⟩ : Fin 148) ⟨35, by decide⟩ _
      (validAt ⟨66, by decide⟩ (listedAt ⟨66, by decide⟩ hj))
      (colE1 ⟨35, by decide⟩ 15 (transLenTr ⟨35, by decide⟩ 15 hp)) T66_35
      hfix66_35 hinj66_35 hcardT66_35
      (fun i => conj_mem_of_fixedPoints _ _ (T66_35 i) (hfix66_35 i) _)
      ⟨66, by decide⟩ ⟨35, by decide⟩ _
      (Q2.validAt ⟨66, by decide⟩ (Q2.listedAt ⟨66, by decide⟩
        (alnCheck_rep ⟨66, by decide⟩ hj hq).1))
      (colE2 ⟨35, by decide⟩ 15 hp) Q2.T66_35_2 Q2.hfix66_35_2 Q2.hinj66_35_2
      Q2.hcardT66_35_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T66_35_2 i) (Q2.hfix66_35_2 i) _)
      colCert_66_35_15.hD ?_).symm
  rw [alnId_66 j hj]


theorem leaf_66_35_20 (hp : 20 < (Q2.transData.getD 35 []).length)
    (j : Nat) (hj : j < (repChars.getD 66 []).length)
    (hq : (normIsRep.getD 66 []).getD j false = true) :
    species (Q2.reps (⟨35, by decide⟩ : Fin 148)) (colE2 ⟨35, by decide⟩ 20 hp)
        (rowE2 (⟨66, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨35, by decide⟩ : Fin 148))
        (colE1 ⟨35, by decide⟩ 20 (transLenTr ⟨35, by decide⟩ 20 hp))
        (rowE1 (⟨66, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨66, by decide⟩ : Fin 148) ⟨35, by decide⟩ _
      (validAt ⟨66, by decide⟩ (listedAt ⟨66, by decide⟩ hj))
      (colE1 ⟨35, by decide⟩ 20 (transLenTr ⟨35, by decide⟩ 20 hp)) T66_35
      hfix66_35 hinj66_35 hcardT66_35
      (fun i => conj_mem_of_fixedPoints _ _ (T66_35 i) (hfix66_35 i) _)
      ⟨66, by decide⟩ ⟨35, by decide⟩ _
      (Q2.validAt ⟨66, by decide⟩ (Q2.listedAt ⟨66, by decide⟩
        (alnCheck_rep ⟨66, by decide⟩ hj hq).1))
      (colE2 ⟨35, by decide⟩ 20 hp) Q2.T66_35_2 Q2.hfix66_35_2 Q2.hinj66_35_2
      Q2.hcardT66_35_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T66_35_2 i) (Q2.hfix66_35_2 i) _)
      colCert_66_35_20.hD ?_).symm
  rw [alnId_66 j hj]


theorem leaf_66_40_0 (hp : 0 < (Q2.transData.getD 40 []).length)
    (j : Nat) (hj : j < (repChars.getD 66 []).length)
    (hq : (normIsRep.getD 66 []).getD j false = true) :
    species (Q2.reps (⟨40, by decide⟩ : Fin 148)) (colE2 ⟨40, by decide⟩ 0 hp)
        (rowE2 (⟨66, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨40, by decide⟩ : Fin 148))
        (colE1 ⟨40, by decide⟩ 0 (transLenTr ⟨40, by decide⟩ 0 hp))
        (rowE1 (⟨66, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨66, by decide⟩ : Fin 148) ⟨40, by decide⟩ _
      (validAt ⟨66, by decide⟩ (listedAt ⟨66, by decide⟩ hj))
      (colE1 ⟨40, by decide⟩ 0 (transLenTr ⟨40, by decide⟩ 0 hp)) T66_40
      hfix66_40 hinj66_40 hcardT66_40
      (fun i => conj_mem_of_fixedPoints _ _ (T66_40 i) (hfix66_40 i) _)
      ⟨66, by decide⟩ ⟨40, by decide⟩ _
      (Q2.validAt ⟨66, by decide⟩ (Q2.listedAt ⟨66, by decide⟩
        (alnCheck_rep ⟨66, by decide⟩ hj hq).1))
      (colE2 ⟨40, by decide⟩ 0 hp) Q2.T66_40_2 Q2.hfix66_40_2 Q2.hinj66_40_2
      Q2.hcardT66_40_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T66_40_2 i) (Q2.hfix66_40_2 i) _)
      colCert_66_40_0.hD ?_).symm
  rw [alnId_66 j hj]


theorem leaf_66_40_1 (hp : 1 < (Q2.transData.getD 40 []).length)
    (j : Nat) (hj : j < (repChars.getD 66 []).length)
    (hq : (normIsRep.getD 66 []).getD j false = true) :
    species (Q2.reps (⟨40, by decide⟩ : Fin 148)) (colE2 ⟨40, by decide⟩ 1 hp)
        (rowE2 (⟨66, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨40, by decide⟩ : Fin 148))
        (colE1 ⟨40, by decide⟩ 1 (transLenTr ⟨40, by decide⟩ 1 hp))
        (rowE1 (⟨66, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨66, by decide⟩ : Fin 148) ⟨40, by decide⟩ _
      (validAt ⟨66, by decide⟩ (listedAt ⟨66, by decide⟩ hj))
      (colE1 ⟨40, by decide⟩ 1 (transLenTr ⟨40, by decide⟩ 1 hp)) T66_40
      hfix66_40 hinj66_40 hcardT66_40
      (fun i => conj_mem_of_fixedPoints _ _ (T66_40 i) (hfix66_40 i) _)
      ⟨66, by decide⟩ ⟨40, by decide⟩ _
      (Q2.validAt ⟨66, by decide⟩ (Q2.listedAt ⟨66, by decide⟩
        (alnCheck_rep ⟨66, by decide⟩ hj hq).1))
      (colE2 ⟨40, by decide⟩ 1 hp) Q2.T66_40_2 Q2.hfix66_40_2 Q2.hinj66_40_2
      Q2.hcardT66_40_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T66_40_2 i) (Q2.hfix66_40_2 i) _)
      colCert_66_40_1.hD ?_).symm
  rw [alnId_66 j hj]


theorem leaf_66_40_2 (hp : 2 < (Q2.transData.getD 40 []).length)
    (j : Nat) (hj : j < (repChars.getD 66 []).length)
    (hq : (normIsRep.getD 66 []).getD j false = true) :
    species (Q2.reps (⟨40, by decide⟩ : Fin 148)) (colE2 ⟨40, by decide⟩ 2 hp)
        (rowE2 (⟨66, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨40, by decide⟩ : Fin 148))
        (colE1 ⟨40, by decide⟩ 2 (transLenTr ⟨40, by decide⟩ 2 hp))
        (rowE1 (⟨66, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨66, by decide⟩ : Fin 148) ⟨40, by decide⟩ _
      (validAt ⟨66, by decide⟩ (listedAt ⟨66, by decide⟩ hj))
      (colE1 ⟨40, by decide⟩ 2 (transLenTr ⟨40, by decide⟩ 2 hp)) T66_40
      hfix66_40 hinj66_40 hcardT66_40
      (fun i => conj_mem_of_fixedPoints _ _ (T66_40 i) (hfix66_40 i) _)
      ⟨66, by decide⟩ ⟨40, by decide⟩ _
      (Q2.validAt ⟨66, by decide⟩ (Q2.listedAt ⟨66, by decide⟩
        (alnCheck_rep ⟨66, by decide⟩ hj hq).1))
      (colE2 ⟨40, by decide⟩ 2 hp) Q2.T66_40_2 Q2.hfix66_40_2 Q2.hinj66_40_2
      Q2.hcardT66_40_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T66_40_2 i) (Q2.hfix66_40_2 i) _)
      colCert_66_40_2.hD ?_).symm
  rw [alnId_66 j hj]


theorem leaf_66_40_3 (hp : 3 < (Q2.transData.getD 40 []).length)
    (j : Nat) (hj : j < (repChars.getD 66 []).length)
    (hq : (normIsRep.getD 66 []).getD j false = true) :
    species (Q2.reps (⟨40, by decide⟩ : Fin 148)) (colE2 ⟨40, by decide⟩ 3 hp)
        (rowE2 (⟨66, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨40, by decide⟩ : Fin 148))
        (colE1 ⟨40, by decide⟩ 3 (transLenTr ⟨40, by decide⟩ 3 hp))
        (rowE1 (⟨66, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨66, by decide⟩ : Fin 148) ⟨40, by decide⟩ _
      (validAt ⟨66, by decide⟩ (listedAt ⟨66, by decide⟩ hj))
      (colE1 ⟨40, by decide⟩ 3 (transLenTr ⟨40, by decide⟩ 3 hp)) T66_40
      hfix66_40 hinj66_40 hcardT66_40
      (fun i => conj_mem_of_fixedPoints _ _ (T66_40 i) (hfix66_40 i) _)
      ⟨66, by decide⟩ ⟨40, by decide⟩ _
      (Q2.validAt ⟨66, by decide⟩ (Q2.listedAt ⟨66, by decide⟩
        (alnCheck_rep ⟨66, by decide⟩ hj hq).1))
      (colE2 ⟨40, by decide⟩ 3 hp) Q2.T66_40_2 Q2.hfix66_40_2 Q2.hinj66_40_2
      Q2.hcardT66_40_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T66_40_2 i) (Q2.hfix66_40_2 i) _)
      colCert_66_40_3.hD ?_).symm
  rw [alnId_66 j hj]


theorem leaf_66_40_4 (hp : 4 < (Q2.transData.getD 40 []).length)
    (j : Nat) (hj : j < (repChars.getD 66 []).length)
    (hq : (normIsRep.getD 66 []).getD j false = true) :
    species (Q2.reps (⟨40, by decide⟩ : Fin 148)) (colE2 ⟨40, by decide⟩ 4 hp)
        (rowE2 (⟨66, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨40, by decide⟩ : Fin 148))
        (colE1 ⟨40, by decide⟩ 4 (transLenTr ⟨40, by decide⟩ 4 hp))
        (rowE1 (⟨66, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨66, by decide⟩ : Fin 148) ⟨40, by decide⟩ _
      (validAt ⟨66, by decide⟩ (listedAt ⟨66, by decide⟩ hj))
      (colE1 ⟨40, by decide⟩ 4 (transLenTr ⟨40, by decide⟩ 4 hp)) T66_40
      hfix66_40 hinj66_40 hcardT66_40
      (fun i => conj_mem_of_fixedPoints _ _ (T66_40 i) (hfix66_40 i) _)
      ⟨66, by decide⟩ ⟨40, by decide⟩ _
      (Q2.validAt ⟨66, by decide⟩ (Q2.listedAt ⟨66, by decide⟩
        (alnCheck_rep ⟨66, by decide⟩ hj hq).1))
      (colE2 ⟨40, by decide⟩ 4 hp) Q2.T66_40_2 Q2.hfix66_40_2 Q2.hinj66_40_2
      Q2.hcardT66_40_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T66_40_2 i) (Q2.hfix66_40_2 i) _)
      colCert_66_40_4.hD ?_).symm
  rw [alnId_66 j hj]


theorem leaf_66_40_5 (hp : 5 < (Q2.transData.getD 40 []).length)
    (j : Nat) (hj : j < (repChars.getD 66 []).length)
    (hq : (normIsRep.getD 66 []).getD j false = true) :
    species (Q2.reps (⟨40, by decide⟩ : Fin 148)) (colE2 ⟨40, by decide⟩ 5 hp)
        (rowE2 (⟨66, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨40, by decide⟩ : Fin 148))
        (colE1 ⟨40, by decide⟩ 5 (transLenTr ⟨40, by decide⟩ 5 hp))
        (rowE1 (⟨66, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨66, by decide⟩ : Fin 148) ⟨40, by decide⟩ _
      (validAt ⟨66, by decide⟩ (listedAt ⟨66, by decide⟩ hj))
      (colE1 ⟨40, by decide⟩ 5 (transLenTr ⟨40, by decide⟩ 5 hp)) T66_40
      hfix66_40 hinj66_40 hcardT66_40
      (fun i => conj_mem_of_fixedPoints _ _ (T66_40 i) (hfix66_40 i) _)
      ⟨66, by decide⟩ ⟨40, by decide⟩ _
      (Q2.validAt ⟨66, by decide⟩ (Q2.listedAt ⟨66, by decide⟩
        (alnCheck_rep ⟨66, by decide⟩ hj hq).1))
      (colE2 ⟨40, by decide⟩ 5 hp) Q2.T66_40_2 Q2.hfix66_40_2 Q2.hinj66_40_2
      Q2.hcardT66_40_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T66_40_2 i) (Q2.hfix66_40_2 i) _)
      colCert_66_40_5.hD ?_).symm
  rw [alnId_66 j hj]


theorem leaf_66_40_10 (hp : 10 < (Q2.transData.getD 40 []).length)
    (j : Nat) (hj : j < (repChars.getD 66 []).length)
    (hq : (normIsRep.getD 66 []).getD j false = true) :
    species (Q2.reps (⟨40, by decide⟩ : Fin 148)) (colE2 ⟨40, by decide⟩ 10 hp)
        (rowE2 (⟨66, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨40, by decide⟩ : Fin 148))
        (colE1 ⟨40, by decide⟩ 10 (transLenTr ⟨40, by decide⟩ 10 hp))
        (rowE1 (⟨66, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨66, by decide⟩ : Fin 148) ⟨40, by decide⟩ _
      (validAt ⟨66, by decide⟩ (listedAt ⟨66, by decide⟩ hj))
      (colE1 ⟨40, by decide⟩ 10 (transLenTr ⟨40, by decide⟩ 10 hp)) T66_40
      hfix66_40 hinj66_40 hcardT66_40
      (fun i => conj_mem_of_fixedPoints _ _ (T66_40 i) (hfix66_40 i) _)
      ⟨66, by decide⟩ ⟨40, by decide⟩ _
      (Q2.validAt ⟨66, by decide⟩ (Q2.listedAt ⟨66, by decide⟩
        (alnCheck_rep ⟨66, by decide⟩ hj hq).1))
      (colE2 ⟨40, by decide⟩ 10 hp) Q2.T66_40_2 Q2.hfix66_40_2 Q2.hinj66_40_2
      Q2.hcardT66_40_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T66_40_2 i) (Q2.hfix66_40_2 i) _)
      colCert_66_40_10.hD ?_).symm
  rw [alnId_66 j hj]


theorem leaf_66_40_15 (hp : 15 < (Q2.transData.getD 40 []).length)
    (j : Nat) (hj : j < (repChars.getD 66 []).length)
    (hq : (normIsRep.getD 66 []).getD j false = true) :
    species (Q2.reps (⟨40, by decide⟩ : Fin 148)) (colE2 ⟨40, by decide⟩ 15 hp)
        (rowE2 (⟨66, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨40, by decide⟩ : Fin 148))
        (colE1 ⟨40, by decide⟩ 15 (transLenTr ⟨40, by decide⟩ 15 hp))
        (rowE1 (⟨66, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨66, by decide⟩ : Fin 148) ⟨40, by decide⟩ _
      (validAt ⟨66, by decide⟩ (listedAt ⟨66, by decide⟩ hj))
      (colE1 ⟨40, by decide⟩ 15 (transLenTr ⟨40, by decide⟩ 15 hp)) T66_40
      hfix66_40 hinj66_40 hcardT66_40
      (fun i => conj_mem_of_fixedPoints _ _ (T66_40 i) (hfix66_40 i) _)
      ⟨66, by decide⟩ ⟨40, by decide⟩ _
      (Q2.validAt ⟨66, by decide⟩ (Q2.listedAt ⟨66, by decide⟩
        (alnCheck_rep ⟨66, by decide⟩ hj hq).1))
      (colE2 ⟨40, by decide⟩ 15 hp) Q2.T66_40_2 Q2.hfix66_40_2 Q2.hinj66_40_2
      Q2.hcardT66_40_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T66_40_2 i) (Q2.hfix66_40_2 i) _)
      colCert_66_40_15.hD ?_).symm
  rw [alnId_66 j hj]


theorem leaf_66_40_20 (hp : 20 < (Q2.transData.getD 40 []).length)
    (j : Nat) (hj : j < (repChars.getD 66 []).length)
    (hq : (normIsRep.getD 66 []).getD j false = true) :
    species (Q2.reps (⟨40, by decide⟩ : Fin 148)) (colE2 ⟨40, by decide⟩ 20 hp)
        (rowE2 (⟨66, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨40, by decide⟩ : Fin 148))
        (colE1 ⟨40, by decide⟩ 20 (transLenTr ⟨40, by decide⟩ 20 hp))
        (rowE1 (⟨66, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨66, by decide⟩ : Fin 148) ⟨40, by decide⟩ _
      (validAt ⟨66, by decide⟩ (listedAt ⟨66, by decide⟩ hj))
      (colE1 ⟨40, by decide⟩ 20 (transLenTr ⟨40, by decide⟩ 20 hp)) T66_40
      hfix66_40 hinj66_40 hcardT66_40
      (fun i => conj_mem_of_fixedPoints _ _ (T66_40 i) (hfix66_40 i) _)
      ⟨66, by decide⟩ ⟨40, by decide⟩ _
      (Q2.validAt ⟨66, by decide⟩ (Q2.listedAt ⟨66, by decide⟩
        (alnCheck_rep ⟨66, by decide⟩ hj hq).1))
      (colE2 ⟨40, by decide⟩ 20 hp) Q2.T66_40_2 Q2.hfix66_40_2 Q2.hinj66_40_2
      Q2.hcardT66_40_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T66_40_2 i) (Q2.hfix66_40_2 i) _)
      colCert_66_40_20.hD ?_).symm
  rw [alnId_66 j hj]


theorem leaf_66_45_0 (hp : 0 < (Q2.transData.getD 45 []).length)
    (j : Nat) (hj : j < (repChars.getD 66 []).length)
    (hq : (normIsRep.getD 66 []).getD j false = true) :
    species (Q2.reps (⟨45, by decide⟩ : Fin 148)) (colE2 ⟨45, by decide⟩ 0 hp)
        (rowE2 (⟨66, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨45, by decide⟩ : Fin 148))
        (colE1 ⟨45, by decide⟩ 0 (transLenTr ⟨45, by decide⟩ 0 hp))
        (rowE1 (⟨66, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨66, by decide⟩ : Fin 148) ⟨45, by decide⟩ _
      (validAt ⟨66, by decide⟩ (listedAt ⟨66, by decide⟩ hj))
      (colE1 ⟨45, by decide⟩ 0 (transLenTr ⟨45, by decide⟩ 0 hp)) T66_45
      hfix66_45 hinj66_45 hcardT66_45
      (fun i => conj_mem_of_fixedPoints _ _ (T66_45 i) (hfix66_45 i) _)
      ⟨66, by decide⟩ ⟨45, by decide⟩ _
      (Q2.validAt ⟨66, by decide⟩ (Q2.listedAt ⟨66, by decide⟩
        (alnCheck_rep ⟨66, by decide⟩ hj hq).1))
      (colE2 ⟨45, by decide⟩ 0 hp) Q2.T66_45_2 Q2.hfix66_45_2 Q2.hinj66_45_2
      Q2.hcardT66_45_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T66_45_2 i) (Q2.hfix66_45_2 i) _)
      colCert_66_45_0.hD ?_).symm
  rw [alnId_66 j hj]


theorem leaf_66_45_1 (hp : 1 < (Q2.transData.getD 45 []).length)
    (j : Nat) (hj : j < (repChars.getD 66 []).length)
    (hq : (normIsRep.getD 66 []).getD j false = true) :
    species (Q2.reps (⟨45, by decide⟩ : Fin 148)) (colE2 ⟨45, by decide⟩ 1 hp)
        (rowE2 (⟨66, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨45, by decide⟩ : Fin 148))
        (colE1 ⟨45, by decide⟩ 1 (transLenTr ⟨45, by decide⟩ 1 hp))
        (rowE1 (⟨66, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨66, by decide⟩ : Fin 148) ⟨45, by decide⟩ _
      (validAt ⟨66, by decide⟩ (listedAt ⟨66, by decide⟩ hj))
      (colE1 ⟨45, by decide⟩ 1 (transLenTr ⟨45, by decide⟩ 1 hp)) T66_45
      hfix66_45 hinj66_45 hcardT66_45
      (fun i => conj_mem_of_fixedPoints _ _ (T66_45 i) (hfix66_45 i) _)
      ⟨66, by decide⟩ ⟨45, by decide⟩ _
      (Q2.validAt ⟨66, by decide⟩ (Q2.listedAt ⟨66, by decide⟩
        (alnCheck_rep ⟨66, by decide⟩ hj hq).1))
      (colE2 ⟨45, by decide⟩ 1 hp) Q2.T66_45_2 Q2.hfix66_45_2 Q2.hinj66_45_2
      Q2.hcardT66_45_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T66_45_2 i) (Q2.hfix66_45_2 i) _)
      colCert_66_45_1.hD ?_).symm
  rw [alnId_66 j hj]


theorem leaf_66_45_2 (hp : 2 < (Q2.transData.getD 45 []).length)
    (j : Nat) (hj : j < (repChars.getD 66 []).length)
    (hq : (normIsRep.getD 66 []).getD j false = true) :
    species (Q2.reps (⟨45, by decide⟩ : Fin 148)) (colE2 ⟨45, by decide⟩ 2 hp)
        (rowE2 (⟨66, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨45, by decide⟩ : Fin 148))
        (colE1 ⟨45, by decide⟩ 2 (transLenTr ⟨45, by decide⟩ 2 hp))
        (rowE1 (⟨66, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨66, by decide⟩ : Fin 148) ⟨45, by decide⟩ _
      (validAt ⟨66, by decide⟩ (listedAt ⟨66, by decide⟩ hj))
      (colE1 ⟨45, by decide⟩ 2 (transLenTr ⟨45, by decide⟩ 2 hp)) T66_45
      hfix66_45 hinj66_45 hcardT66_45
      (fun i => conj_mem_of_fixedPoints _ _ (T66_45 i) (hfix66_45 i) _)
      ⟨66, by decide⟩ ⟨45, by decide⟩ _
      (Q2.validAt ⟨66, by decide⟩ (Q2.listedAt ⟨66, by decide⟩
        (alnCheck_rep ⟨66, by decide⟩ hj hq).1))
      (colE2 ⟨45, by decide⟩ 2 hp) Q2.T66_45_2 Q2.hfix66_45_2 Q2.hinj66_45_2
      Q2.hcardT66_45_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T66_45_2 i) (Q2.hfix66_45_2 i) _)
      colCert_66_45_2.hD ?_).symm
  rw [alnId_66 j hj]


theorem leaf_66_45_3 (hp : 3 < (Q2.transData.getD 45 []).length)
    (j : Nat) (hj : j < (repChars.getD 66 []).length)
    (hq : (normIsRep.getD 66 []).getD j false = true) :
    species (Q2.reps (⟨45, by decide⟩ : Fin 148)) (colE2 ⟨45, by decide⟩ 3 hp)
        (rowE2 (⟨66, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨45, by decide⟩ : Fin 148))
        (colE1 ⟨45, by decide⟩ 3 (transLenTr ⟨45, by decide⟩ 3 hp))
        (rowE1 (⟨66, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨66, by decide⟩ : Fin 148) ⟨45, by decide⟩ _
      (validAt ⟨66, by decide⟩ (listedAt ⟨66, by decide⟩ hj))
      (colE1 ⟨45, by decide⟩ 3 (transLenTr ⟨45, by decide⟩ 3 hp)) T66_45
      hfix66_45 hinj66_45 hcardT66_45
      (fun i => conj_mem_of_fixedPoints _ _ (T66_45 i) (hfix66_45 i) _)
      ⟨66, by decide⟩ ⟨45, by decide⟩ _
      (Q2.validAt ⟨66, by decide⟩ (Q2.listedAt ⟨66, by decide⟩
        (alnCheck_rep ⟨66, by decide⟩ hj hq).1))
      (colE2 ⟨45, by decide⟩ 3 hp) Q2.T66_45_2 Q2.hfix66_45_2 Q2.hinj66_45_2
      Q2.hcardT66_45_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T66_45_2 i) (Q2.hfix66_45_2 i) _)
      colCert_66_45_3.hD ?_).symm
  rw [alnId_66 j hj]


theorem leaf_66_45_4 (hp : 4 < (Q2.transData.getD 45 []).length)
    (j : Nat) (hj : j < (repChars.getD 66 []).length)
    (hq : (normIsRep.getD 66 []).getD j false = true) :
    species (Q2.reps (⟨45, by decide⟩ : Fin 148)) (colE2 ⟨45, by decide⟩ 4 hp)
        (rowE2 (⟨66, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨45, by decide⟩ : Fin 148))
        (colE1 ⟨45, by decide⟩ 4 (transLenTr ⟨45, by decide⟩ 4 hp))
        (rowE1 (⟨66, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨66, by decide⟩ : Fin 148) ⟨45, by decide⟩ _
      (validAt ⟨66, by decide⟩ (listedAt ⟨66, by decide⟩ hj))
      (colE1 ⟨45, by decide⟩ 4 (transLenTr ⟨45, by decide⟩ 4 hp)) T66_45
      hfix66_45 hinj66_45 hcardT66_45
      (fun i => conj_mem_of_fixedPoints _ _ (T66_45 i) (hfix66_45 i) _)
      ⟨66, by decide⟩ ⟨45, by decide⟩ _
      (Q2.validAt ⟨66, by decide⟩ (Q2.listedAt ⟨66, by decide⟩
        (alnCheck_rep ⟨66, by decide⟩ hj hq).1))
      (colE2 ⟨45, by decide⟩ 4 hp) Q2.T66_45_2 Q2.hfix66_45_2 Q2.hinj66_45_2
      Q2.hcardT66_45_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T66_45_2 i) (Q2.hfix66_45_2 i) _)
      colCert_66_45_4.hD ?_).symm
  rw [alnId_66 j hj]


theorem leaf_66_45_5 (hp : 5 < (Q2.transData.getD 45 []).length)
    (j : Nat) (hj : j < (repChars.getD 66 []).length)
    (hq : (normIsRep.getD 66 []).getD j false = true) :
    species (Q2.reps (⟨45, by decide⟩ : Fin 148)) (colE2 ⟨45, by decide⟩ 5 hp)
        (rowE2 (⟨66, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨45, by decide⟩ : Fin 148))
        (colE1 ⟨45, by decide⟩ 5 (transLenTr ⟨45, by decide⟩ 5 hp))
        (rowE1 (⟨66, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨66, by decide⟩ : Fin 148) ⟨45, by decide⟩ _
      (validAt ⟨66, by decide⟩ (listedAt ⟨66, by decide⟩ hj))
      (colE1 ⟨45, by decide⟩ 5 (transLenTr ⟨45, by decide⟩ 5 hp)) T66_45
      hfix66_45 hinj66_45 hcardT66_45
      (fun i => conj_mem_of_fixedPoints _ _ (T66_45 i) (hfix66_45 i) _)
      ⟨66, by decide⟩ ⟨45, by decide⟩ _
      (Q2.validAt ⟨66, by decide⟩ (Q2.listedAt ⟨66, by decide⟩
        (alnCheck_rep ⟨66, by decide⟩ hj hq).1))
      (colE2 ⟨45, by decide⟩ 5 hp) Q2.T66_45_2 Q2.hfix66_45_2 Q2.hinj66_45_2
      Q2.hcardT66_45_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T66_45_2 i) (Q2.hfix66_45_2 i) _)
      colCert_66_45_5.hD ?_).symm
  rw [alnId_66 j hj]


end LeanDring.P5Presentation
