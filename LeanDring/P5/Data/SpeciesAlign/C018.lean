/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.Characters.Twin2.CharAlign
import LeanDring.P5.Data.ColCdd.C039
import LeanDring.P5.Data.ColRestCheap.C165

/-!
# Species-table cells, α-paired residual decides, chunk 17

For the 34 subgroup classes whose q1/q2 character SETS differ, σ pairs a q1
orbit-representative vector with a different q2 vector; this chunk certifies the
cyclotomic-value equality of the two fast codes at those pairs, over the already
kernel-bound column data.  Auto-emitted by `python/p5_alignmatch_emit.py`.
-/

namespace LeanDring.P5Presentation

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.style.longLine false

theorem alnAll_73_24_3 : ∀ j, j < (repChars.getD 73 []).length →
    (normIsRep.getD 73 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_73_24_3.D (m := 25))
        (List.map ZMod.val ((repChars.getD 73 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_73_24_3.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 73 []).getD ((alnPos.getD 73 []).getD j 0) []))) := by decide

theorem alnAll_73_24_4 : ∀ j, j < (repChars.getD 73 []).length →
    (normIsRep.getD 73 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_73_24_4.D (m := 25))
        (List.map ZMod.val ((repChars.getD 73 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_73_24_4.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 73 []).getD ((alnPos.getD 73 []).getD j 0) []))) := by decide

theorem alnAll_73_24_5 : ∀ j, j < (repChars.getD 73 []).length →
    (normIsRep.getD 73 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_73_24_5.D (m := 25))
        (List.map ZMod.val ((repChars.getD 73 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_73_24_5.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 73 []).getD ((alnPos.getD 73 []).getD j 0) []))) := by decide

theorem alnAll_73_24_10 : ∀ j, j < (repChars.getD 73 []).length →
    (normIsRep.getD 73 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_73_24_10.D (m := 25))
        (List.map ZMod.val ((repChars.getD 73 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_73_24_10.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 73 []).getD ((alnPos.getD 73 []).getD j 0) []))) := by decide

theorem alnAll_73_24_15 : ∀ j, j < (repChars.getD 73 []).length →
    (normIsRep.getD 73 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_73_24_15.D (m := 25))
        (List.map ZMod.val ((repChars.getD 73 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_73_24_15.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 73 []).getD ((alnPos.getD 73 []).getD j 0) []))) := by decide

theorem alnAll_73_24_20 : ∀ j, j < (repChars.getD 73 []).length →
    (normIsRep.getD 73 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_73_24_20.D (m := 25))
        (List.map ZMod.val ((repChars.getD 73 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_73_24_20.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 73 []).getD ((alnPos.getD 73 []).getD j 0) []))) := by decide

theorem alnAll_73_31_0 : ∀ j, j < (repChars.getD 73 []).length →
    (normIsRep.getD 73 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_73_31_0.D (m := 5))
        (List.map ZMod.val ((repChars.getD 73 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_73_31_0.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 73 []).getD ((alnPos.getD 73 []).getD j 0) []))) := by decide

theorem alnAll_73_31_1 : ∀ j, j < (repChars.getD 73 []).length →
    (normIsRep.getD 73 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_73_31_1.D (m := 5))
        (List.map ZMod.val ((repChars.getD 73 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_73_31_1.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 73 []).getD ((alnPos.getD 73 []).getD j 0) []))) := by decide

theorem alnAll_73_31_2 : ∀ j, j < (repChars.getD 73 []).length →
    (normIsRep.getD 73 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_73_31_2.D (m := 5))
        (List.map ZMod.val ((repChars.getD 73 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_73_31_2.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 73 []).getD ((alnPos.getD 73 []).getD j 0) []))) := by decide

theorem alnAll_73_31_3 : ∀ j, j < (repChars.getD 73 []).length →
    (normIsRep.getD 73 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_73_31_3.D (m := 5))
        (List.map ZMod.val ((repChars.getD 73 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_73_31_3.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 73 []).getD ((alnPos.getD 73 []).getD j 0) []))) := by decide

theorem alnAll_73_31_4 : ∀ j, j < (repChars.getD 73 []).length →
    (normIsRep.getD 73 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_73_31_4.D (m := 5))
        (List.map ZMod.val ((repChars.getD 73 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_73_31_4.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 73 []).getD ((alnPos.getD 73 []).getD j 0) []))) := by decide

theorem alnAll_73_31_5 : ∀ j, j < (repChars.getD 73 []).length →
    (normIsRep.getD 73 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCertDiv_73_31_5.D1 (m := 5))
        (List.map ZMod.val ((repChars.getD 73 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCertDiv_73_31_5.D2 (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 73 []).getD ((alnPos.getD 73 []).getD j 0) []))) := by decide

theorem alnAll_73_31_10 : ∀ j, j < (repChars.getD 73 []).length →
    (normIsRep.getD 73 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCertDiv_73_31_10.D1 (m := 5))
        (List.map ZMod.val ((repChars.getD 73 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCertDiv_73_31_10.D2 (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 73 []).getD ((alnPos.getD 73 []).getD j 0) []))) := by decide

theorem alnAll_73_31_15 : ∀ j, j < (repChars.getD 73 []).length →
    (normIsRep.getD 73 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCertDiv_73_31_15.D1 (m := 5))
        (List.map ZMod.val ((repChars.getD 73 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCertDiv_73_31_15.D2 (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 73 []).getD ((alnPos.getD 73 []).getD j 0) []))) := by decide

theorem alnAll_73_31_20 : ∀ j, j < (repChars.getD 73 []).length →
    (normIsRep.getD 73 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCertDiv_73_31_20.D1 (m := 5))
        (List.map ZMod.val ((repChars.getD 73 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCertDiv_73_31_20.D2 (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 73 []).getD ((alnPos.getD 73 []).getD j 0) []))) := by decide

theorem alnAll_73_36_0 : ∀ j, j < (repChars.getD 73 []).length →
    (normIsRep.getD 73 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_73_36_0.D (m := 5))
        (List.map ZMod.val ((repChars.getD 73 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_73_36_0.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 73 []).getD ((alnPos.getD 73 []).getD j 0) []))) := by decide

theorem alnAll_73_36_1 : ∀ j, j < (repChars.getD 73 []).length →
    (normIsRep.getD 73 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_73_36_1.D (m := 5))
        (List.map ZMod.val ((repChars.getD 73 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_73_36_1.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 73 []).getD ((alnPos.getD 73 []).getD j 0) []))) := by decide

theorem alnAll_73_36_2 : ∀ j, j < (repChars.getD 73 []).length →
    (normIsRep.getD 73 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_73_36_2.D (m := 5))
        (List.map ZMod.val ((repChars.getD 73 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_73_36_2.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 73 []).getD ((alnPos.getD 73 []).getD j 0) []))) := by decide

theorem alnAll_73_36_3 : ∀ j, j < (repChars.getD 73 []).length →
    (normIsRep.getD 73 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_73_36_3.D (m := 5))
        (List.map ZMod.val ((repChars.getD 73 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_73_36_3.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 73 []).getD ((alnPos.getD 73 []).getD j 0) []))) := by decide

theorem alnAll_73_36_4 : ∀ j, j < (repChars.getD 73 []).length →
    (normIsRep.getD 73 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_73_36_4.D (m := 5))
        (List.map ZMod.val ((repChars.getD 73 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_73_36_4.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 73 []).getD ((alnPos.getD 73 []).getD j 0) []))) := by decide

theorem alnAll_73_36_5 : ∀ j, j < (repChars.getD 73 []).length →
    (normIsRep.getD 73 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCertDiv_73_36_5.D1 (m := 5))
        (List.map ZMod.val ((repChars.getD 73 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCertDiv_73_36_5.D2 (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 73 []).getD ((alnPos.getD 73 []).getD j 0) []))) := by decide

theorem alnAll_73_36_10 : ∀ j, j < (repChars.getD 73 []).length →
    (normIsRep.getD 73 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCertDiv_73_36_10.D1 (m := 5))
        (List.map ZMod.val ((repChars.getD 73 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCertDiv_73_36_10.D2 (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 73 []).getD ((alnPos.getD 73 []).getD j 0) []))) := by decide

theorem alnAll_73_36_15 : ∀ j, j < (repChars.getD 73 []).length →
    (normIsRep.getD 73 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCertDiv_73_36_15.D1 (m := 5))
        (List.map ZMod.val ((repChars.getD 73 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCertDiv_73_36_15.D2 (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 73 []).getD ((alnPos.getD 73 []).getD j 0) []))) := by decide

theorem alnAll_73_36_20 : ∀ j, j < (repChars.getD 73 []).length →
    (normIsRep.getD 73 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCertDiv_73_36_20.D1 (m := 5))
        (List.map ZMod.val ((repChars.getD 73 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCertDiv_73_36_20.D2 (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 73 []).getD ((alnPos.getD 73 []).getD j 0) []))) := by decide

theorem alnAll_73_41_0 : ∀ j, j < (repChars.getD 73 []).length →
    (normIsRep.getD 73 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_73_41_0.D (m := 5))
        (List.map ZMod.val ((repChars.getD 73 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_73_41_0.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 73 []).getD ((alnPos.getD 73 []).getD j 0) []))) := by decide

theorem alnAll_73_41_1 : ∀ j, j < (repChars.getD 73 []).length →
    (normIsRep.getD 73 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_73_41_1.D (m := 5))
        (List.map ZMod.val ((repChars.getD 73 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_73_41_1.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 73 []).getD ((alnPos.getD 73 []).getD j 0) []))) := by decide

theorem alnAll_73_41_2 : ∀ j, j < (repChars.getD 73 []).length →
    (normIsRep.getD 73 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_73_41_2.D (m := 5))
        (List.map ZMod.val ((repChars.getD 73 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_73_41_2.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 73 []).getD ((alnPos.getD 73 []).getD j 0) []))) := by decide

theorem alnAll_73_41_3 : ∀ j, j < (repChars.getD 73 []).length →
    (normIsRep.getD 73 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_73_41_3.D (m := 5))
        (List.map ZMod.val ((repChars.getD 73 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_73_41_3.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 73 []).getD ((alnPos.getD 73 []).getD j 0) []))) := by decide

theorem alnAll_73_41_4 : ∀ j, j < (repChars.getD 73 []).length →
    (normIsRep.getD 73 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_73_41_4.D (m := 5))
        (List.map ZMod.val ((repChars.getD 73 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_73_41_4.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 73 []).getD ((alnPos.getD 73 []).getD j 0) []))) := by decide

theorem alnAll_73_41_5 : ∀ j, j < (repChars.getD 73 []).length →
    (normIsRep.getD 73 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCertDiv_73_41_5.D1 (m := 5))
        (List.map ZMod.val ((repChars.getD 73 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCertDiv_73_41_5.D2 (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 73 []).getD ((alnPos.getD 73 []).getD j 0) []))) := by decide

theorem alnAll_73_41_10 : ∀ j, j < (repChars.getD 73 []).length →
    (normIsRep.getD 73 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCertDiv_73_41_10.D1 (m := 5))
        (List.map ZMod.val ((repChars.getD 73 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCertDiv_73_41_10.D2 (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 73 []).getD ((alnPos.getD 73 []).getD j 0) []))) := by decide

theorem alnAll_73_41_15 : ∀ j, j < (repChars.getD 73 []).length →
    (normIsRep.getD 73 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCertDiv_73_41_15.D1 (m := 5))
        (List.map ZMod.val ((repChars.getD 73 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCertDiv_73_41_15.D2 (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 73 []).getD ((alnPos.getD 73 []).getD j 0) []))) := by decide

theorem alnAll_73_41_20 : ∀ j, j < (repChars.getD 73 []).length →
    (normIsRep.getD 73 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCertDiv_73_41_20.D1 (m := 5))
        (List.map ZMod.val ((repChars.getD 73 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCertDiv_73_41_20.D2 (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 73 []).getD ((alnPos.getD 73 []).getD j 0) []))) := by decide

theorem alnAll_73_46_0 : ∀ j, j < (repChars.getD 73 []).length →
    (normIsRep.getD 73 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_73_46_0.D (m := 5))
        (List.map ZMod.val ((repChars.getD 73 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_73_46_0.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 73 []).getD ((alnPos.getD 73 []).getD j 0) []))) := by decide

theorem alnAll_73_46_1 : ∀ j, j < (repChars.getD 73 []).length →
    (normIsRep.getD 73 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_73_46_1.D (m := 5))
        (List.map ZMod.val ((repChars.getD 73 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_73_46_1.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 73 []).getD ((alnPos.getD 73 []).getD j 0) []))) := by decide

theorem alnAll_73_46_2 : ∀ j, j < (repChars.getD 73 []).length →
    (normIsRep.getD 73 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_73_46_2.D (m := 5))
        (List.map ZMod.val ((repChars.getD 73 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_73_46_2.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 73 []).getD ((alnPos.getD 73 []).getD j 0) []))) := by decide

theorem alnAll_73_46_3 : ∀ j, j < (repChars.getD 73 []).length →
    (normIsRep.getD 73 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_73_46_3.D (m := 5))
        (List.map ZMod.val ((repChars.getD 73 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_73_46_3.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 73 []).getD ((alnPos.getD 73 []).getD j 0) []))) := by decide

theorem alnAll_73_46_4 : ∀ j, j < (repChars.getD 73 []).length →
    (normIsRep.getD 73 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_73_46_4.D (m := 5))
        (List.map ZMod.val ((repChars.getD 73 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_73_46_4.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 73 []).getD ((alnPos.getD 73 []).getD j 0) []))) := by decide

theorem alnAll_73_46_5 : ∀ j, j < (repChars.getD 73 []).length →
    (normIsRep.getD 73 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCertDiv_73_46_5.D1 (m := 5))
        (List.map ZMod.val ((repChars.getD 73 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCertDiv_73_46_5.D2 (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 73 []).getD ((alnPos.getD 73 []).getD j 0) []))) := by decide

theorem alnAll_73_46_10 : ∀ j, j < (repChars.getD 73 []).length →
    (normIsRep.getD 73 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCertDiv_73_46_10.D1 (m := 5))
        (List.map ZMod.val ((repChars.getD 73 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCertDiv_73_46_10.D2 (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 73 []).getD ((alnPos.getD 73 []).getD j 0) []))) := by decide

theorem alnAll_73_46_15 : ∀ j, j < (repChars.getD 73 []).length →
    (normIsRep.getD 73 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCertDiv_73_46_15.D1 (m := 5))
        (List.map ZMod.val ((repChars.getD 73 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCertDiv_73_46_15.D2 (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 73 []).getD ((alnPos.getD 73 []).getD j 0) []))) := by decide

theorem alnAll_73_46_20 : ∀ j, j < (repChars.getD 73 []).length →
    (normIsRep.getD 73 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCertDiv_73_46_20.D1 (m := 5))
        (List.map ZMod.val ((repChars.getD 73 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCertDiv_73_46_20.D2 (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 73 []).getD ((alnPos.getD 73 []).getD j 0) []))) := by decide

theorem alnAll_73_51_0 : ∀ j, j < (repChars.getD 73 []).length →
    (normIsRep.getD 73 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_73_51_0.D (m := 5))
        (List.map ZMod.val ((repChars.getD 73 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_73_51_0.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 73 []).getD ((alnPos.getD 73 []).getD j 0) []))) := by decide

end LeanDring.P5Presentation
