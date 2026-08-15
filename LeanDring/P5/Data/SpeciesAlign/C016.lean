/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.Characters.Twin2.CharAlign
import LeanDring.P5.Data.ColCdd.C039
import LeanDring.P5.Data.ColRestCheap.C156
import LeanDring.P5.Data.ColRestCheap.C157

/-!
# Species-table cells, α-paired residual decides, chunk 15

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

theorem alnAll_67_40_20 : ∀ j, j < (repChars.getD 67 []).length →
    (normIsRep.getD 67 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCertDiv_67_40_20.D1 (m := 5))
        (List.map ZMod.val ((repChars.getD 67 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCertDiv_67_40_20.D2 (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 67 []).getD ((alnPos.getD 67 []).getD j 0) []))) := by decide

theorem alnAll_67_45_0 : ∀ j, j < (repChars.getD 67 []).length →
    (normIsRep.getD 67 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_67_45_0.D (m := 5))
        (List.map ZMod.val ((repChars.getD 67 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_67_45_0.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 67 []).getD ((alnPos.getD 67 []).getD j 0) []))) := by decide

theorem alnAll_67_45_1 : ∀ j, j < (repChars.getD 67 []).length →
    (normIsRep.getD 67 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_67_45_1.D (m := 5))
        (List.map ZMod.val ((repChars.getD 67 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_67_45_1.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 67 []).getD ((alnPos.getD 67 []).getD j 0) []))) := by decide

theorem alnAll_67_45_2 : ∀ j, j < (repChars.getD 67 []).length →
    (normIsRep.getD 67 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_67_45_2.D (m := 5))
        (List.map ZMod.val ((repChars.getD 67 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_67_45_2.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 67 []).getD ((alnPos.getD 67 []).getD j 0) []))) := by decide

theorem alnAll_67_45_3 : ∀ j, j < (repChars.getD 67 []).length →
    (normIsRep.getD 67 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_67_45_3.D (m := 5))
        (List.map ZMod.val ((repChars.getD 67 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_67_45_3.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 67 []).getD ((alnPos.getD 67 []).getD j 0) []))) := by decide

theorem alnAll_67_45_4 : ∀ j, j < (repChars.getD 67 []).length →
    (normIsRep.getD 67 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_67_45_4.D (m := 5))
        (List.map ZMod.val ((repChars.getD 67 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_67_45_4.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 67 []).getD ((alnPos.getD 67 []).getD j 0) []))) := by decide

theorem alnAll_67_45_5 : ∀ j, j < (repChars.getD 67 []).length →
    (normIsRep.getD 67 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCertDiv_67_45_5.D1 (m := 5))
        (List.map ZMod.val ((repChars.getD 67 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCertDiv_67_45_5.D2 (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 67 []).getD ((alnPos.getD 67 []).getD j 0) []))) := by decide

theorem alnAll_67_45_10 : ∀ j, j < (repChars.getD 67 []).length →
    (normIsRep.getD 67 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCertDiv_67_45_10.D1 (m := 5))
        (List.map ZMod.val ((repChars.getD 67 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCertDiv_67_45_10.D2 (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 67 []).getD ((alnPos.getD 67 []).getD j 0) []))) := by decide

theorem alnAll_67_45_15 : ∀ j, j < (repChars.getD 67 []).length →
    (normIsRep.getD 67 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCertDiv_67_45_15.D1 (m := 5))
        (List.map ZMod.val ((repChars.getD 67 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCertDiv_67_45_15.D2 (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 67 []).getD ((alnPos.getD 67 []).getD j 0) []))) := by decide

theorem alnAll_67_45_20 : ∀ j, j < (repChars.getD 67 []).length →
    (normIsRep.getD 67 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCertDiv_67_45_20.D1 (m := 5))
        (List.map ZMod.val ((repChars.getD 67 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCertDiv_67_45_20.D2 (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 67 []).getD ((alnPos.getD 67 []).getD j 0) []))) := by decide

theorem alnAll_67_50_0 : ∀ j, j < (repChars.getD 67 []).length →
    (normIsRep.getD 67 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_67_50_0.D (m := 5))
        (List.map ZMod.val ((repChars.getD 67 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_67_50_0.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 67 []).getD ((alnPos.getD 67 []).getD j 0) []))) := by decide

theorem alnAll_67_50_1 : ∀ j, j < (repChars.getD 67 []).length →
    (normIsRep.getD 67 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_67_50_1.D (m := 5))
        (List.map ZMod.val ((repChars.getD 67 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_67_50_1.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 67 []).getD ((alnPos.getD 67 []).getD j 0) []))) := by decide

theorem alnAll_67_50_2 : ∀ j, j < (repChars.getD 67 []).length →
    (normIsRep.getD 67 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_67_50_2.D (m := 5))
        (List.map ZMod.val ((repChars.getD 67 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_67_50_2.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 67 []).getD ((alnPos.getD 67 []).getD j 0) []))) := by decide

theorem alnAll_67_50_3 : ∀ j, j < (repChars.getD 67 []).length →
    (normIsRep.getD 67 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_67_50_3.D (m := 5))
        (List.map ZMod.val ((repChars.getD 67 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_67_50_3.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 67 []).getD ((alnPos.getD 67 []).getD j 0) []))) := by decide

theorem alnAll_67_50_4 : ∀ j, j < (repChars.getD 67 []).length →
    (normIsRep.getD 67 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_67_50_4.D (m := 5))
        (List.map ZMod.val ((repChars.getD 67 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_67_50_4.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 67 []).getD ((alnPos.getD 67 []).getD j 0) []))) := by decide

theorem alnAll_67_50_5 : ∀ j, j < (repChars.getD 67 []).length →
    (normIsRep.getD 67 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCertDiv_67_50_5.D1 (m := 5))
        (List.map ZMod.val ((repChars.getD 67 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCertDiv_67_50_5.D2 (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 67 []).getD ((alnPos.getD 67 []).getD j 0) []))) := by decide

theorem alnAll_67_50_10 : ∀ j, j < (repChars.getD 67 []).length →
    (normIsRep.getD 67 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCertDiv_67_50_10.D1 (m := 5))
        (List.map ZMod.val ((repChars.getD 67 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCertDiv_67_50_10.D2 (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 67 []).getD ((alnPos.getD 67 []).getD j 0) []))) := by decide

theorem alnAll_67_50_15 : ∀ j, j < (repChars.getD 67 []).length →
    (normIsRep.getD 67 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCertDiv_67_50_15.D1 (m := 5))
        (List.map ZMod.val ((repChars.getD 67 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCertDiv_67_50_15.D2 (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 67 []).getD ((alnPos.getD 67 []).getD j 0) []))) := by decide

theorem alnAll_67_50_20 : ∀ j, j < (repChars.getD 67 []).length →
    (normIsRep.getD 67 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCertDiv_67_50_20.D1 (m := 5))
        (List.map ZMod.val ((repChars.getD 67 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCertDiv_67_50_20.D2 (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 67 []).getD ((alnPos.getD 67 []).getD j 0) []))) := by decide

theorem alnAll_67_67_0 : ∀ j, j < (repChars.getD 67 []).length →
    (normIsRep.getD 67 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_67_67_0.D (m := 5))
        (List.map ZMod.val ((repChars.getD 67 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_67_67_0.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 67 []).getD ((alnPos.getD 67 []).getD j 0) []))) := by decide

theorem alnAll_67_67_1 : ∀ j, j < (repChars.getD 67 []).length →
    (normIsRep.getD 67 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_67_67_1.D (m := 5))
        (List.map ZMod.val ((repChars.getD 67 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_67_67_1.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 67 []).getD ((alnPos.getD 67 []).getD j 0) []))) := by decide

theorem alnAll_67_67_2 : ∀ j, j < (repChars.getD 67 []).length →
    (normIsRep.getD 67 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_67_67_2.D (m := 5))
        (List.map ZMod.val ((repChars.getD 67 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_67_67_2.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 67 []).getD ((alnPos.getD 67 []).getD j 0) []))) := by decide

theorem alnAll_67_67_3 : ∀ j, j < (repChars.getD 67 []).length →
    (normIsRep.getD 67 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_67_67_3.D (m := 5))
        (List.map ZMod.val ((repChars.getD 67 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_67_67_3.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 67 []).getD ((alnPos.getD 67 []).getD j 0) []))) := by decide

theorem alnAll_67_67_4 : ∀ j, j < (repChars.getD 67 []).length →
    (normIsRep.getD 67 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_67_67_4.D (m := 5))
        (List.map ZMod.val ((repChars.getD 67 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_67_67_4.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 67 []).getD ((alnPos.getD 67 []).getD j 0) []))) := by decide

theorem alnAll_67_67_5 : ∀ j, j < (repChars.getD 67 []).length →
    (normIsRep.getD 67 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_67_67_5.D (m := 5))
        (List.map ZMod.val ((repChars.getD 67 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_67_67_5.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 67 []).getD ((alnPos.getD 67 []).getD j 0) []))) := by decide

theorem alnAll_67_67_6 : ∀ j, j < (repChars.getD 67 []).length →
    (normIsRep.getD 67 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_67_67_6.D (m := 5))
        (List.map ZMod.val ((repChars.getD 67 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_67_67_6.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 67 []).getD ((alnPos.getD 67 []).getD j 0) []))) := by decide

theorem alnAll_67_67_7 : ∀ j, j < (repChars.getD 67 []).length →
    (normIsRep.getD 67 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_67_67_7.D (m := 5))
        (List.map ZMod.val ((repChars.getD 67 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_67_67_7.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 67 []).getD ((alnPos.getD 67 []).getD j 0) []))) := by decide

theorem alnAll_67_67_8 : ∀ j, j < (repChars.getD 67 []).length →
    (normIsRep.getD 67 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_67_67_8.D (m := 5))
        (List.map ZMod.val ((repChars.getD 67 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_67_67_8.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 67 []).getD ((alnPos.getD 67 []).getD j 0) []))) := by decide

theorem alnAll_67_67_9 : ∀ j, j < (repChars.getD 67 []).length →
    (normIsRep.getD 67 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_67_67_9.D (m := 5))
        (List.map ZMod.val ((repChars.getD 67 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_67_67_9.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 67 []).getD ((alnPos.getD 67 []).getD j 0) []))) := by decide

theorem alnAll_67_67_10 : ∀ j, j < (repChars.getD 67 []).length →
    (normIsRep.getD 67 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_67_67_10.D (m := 5))
        (List.map ZMod.val ((repChars.getD 67 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_67_67_10.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 67 []).getD ((alnPos.getD 67 []).getD j 0) []))) := by decide

theorem alnAll_67_67_11 : ∀ j, j < (repChars.getD 67 []).length →
    (normIsRep.getD 67 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_67_67_11.D (m := 5))
        (List.map ZMod.val ((repChars.getD 67 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_67_67_11.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 67 []).getD ((alnPos.getD 67 []).getD j 0) []))) := by decide

theorem alnAll_67_67_12 : ∀ j, j < (repChars.getD 67 []).length →
    (normIsRep.getD 67 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_67_67_12.D (m := 5))
        (List.map ZMod.val ((repChars.getD 67 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_67_67_12.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 67 []).getD ((alnPos.getD 67 []).getD j 0) []))) := by decide

theorem alnAll_67_67_13 : ∀ j, j < (repChars.getD 67 []).length →
    (normIsRep.getD 67 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_67_67_13.D (m := 5))
        (List.map ZMod.val ((repChars.getD 67 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_67_67_13.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 67 []).getD ((alnPos.getD 67 []).getD j 0) []))) := by decide

theorem alnAll_67_67_14 : ∀ j, j < (repChars.getD 67 []).length →
    (normIsRep.getD 67 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_67_67_14.D (m := 5))
        (List.map ZMod.val ((repChars.getD 67 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_67_67_14.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 67 []).getD ((alnPos.getD 67 []).getD j 0) []))) := by decide

theorem alnAll_67_67_15 : ∀ j, j < (repChars.getD 67 []).length →
    (normIsRep.getD 67 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_67_67_15.D (m := 5))
        (List.map ZMod.val ((repChars.getD 67 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_67_67_15.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 67 []).getD ((alnPos.getD 67 []).getD j 0) []))) := by decide

theorem alnAll_67_67_16 : ∀ j, j < (repChars.getD 67 []).length →
    (normIsRep.getD 67 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_67_67_16.D (m := 5))
        (List.map ZMod.val ((repChars.getD 67 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_67_67_16.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 67 []).getD ((alnPos.getD 67 []).getD j 0) []))) := by decide

theorem alnAll_67_67_17 : ∀ j, j < (repChars.getD 67 []).length →
    (normIsRep.getD 67 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_67_67_17.D (m := 5))
        (List.map ZMod.val ((repChars.getD 67 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_67_67_17.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 67 []).getD ((alnPos.getD 67 []).getD j 0) []))) := by decide

theorem alnAll_67_67_18 : ∀ j, j < (repChars.getD 67 []).length →
    (normIsRep.getD 67 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_67_67_18.D (m := 5))
        (List.map ZMod.val ((repChars.getD 67 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_67_67_18.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 67 []).getD ((alnPos.getD 67 []).getD j 0) []))) := by decide

theorem alnAll_67_67_19 : ∀ j, j < (repChars.getD 67 []).length →
    (normIsRep.getD 67 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_67_67_19.D (m := 5))
        (List.map ZMod.val ((repChars.getD 67 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_67_67_19.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 67 []).getD ((alnPos.getD 67 []).getD j 0) []))) := by decide

theorem alnAll_67_67_20 : ∀ j, j < (repChars.getD 67 []).length →
    (normIsRep.getD 67 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_67_67_20.D (m := 5))
        (List.map ZMod.val ((repChars.getD 67 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_67_67_20.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 67 []).getD ((alnPos.getD 67 []).getD j 0) []))) := by decide

theorem alnAll_67_67_21 : ∀ j, j < (repChars.getD 67 []).length →
    (normIsRep.getD 67 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_67_67_21.D (m := 5))
        (List.map ZMod.val ((repChars.getD 67 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_67_67_21.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 67 []).getD ((alnPos.getD 67 []).getD j 0) []))) := by decide

theorem alnAll_67_67_22 : ∀ j, j < (repChars.getD 67 []).length →
    (normIsRep.getD 67 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_67_67_22.D (m := 5))
        (List.map ZMod.val ((repChars.getD 67 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_67_67_22.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 67 []).getD ((alnPos.getD 67 []).getD j 0) []))) := by decide

theorem alnAll_67_67_23 : ∀ j, j < (repChars.getD 67 []).length →
    (normIsRep.getD 67 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_67_67_23.D (m := 5))
        (List.map ZMod.val ((repChars.getD 67 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_67_67_23.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 67 []).getD ((alnPos.getD 67 []).getD j 0) []))) := by decide

theorem alnAll_67_67_24 : ∀ j, j < (repChars.getD 67 []).length →
    (normIsRep.getD 67 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_67_67_24.D (m := 5))
        (List.map ZMod.val ((repChars.getD 67 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_67_67_24.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 67 []).getD ((alnPos.getD 67 []).getD j 0) []))) := by decide

theorem alnAll_67_67_25 : ∀ j, j < (repChars.getD 67 []).length →
    (normIsRep.getD 67 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_67_67_25.D (m := 5))
        (List.map ZMod.val ((repChars.getD 67 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_67_67_25.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 67 []).getD ((alnPos.getD 67 []).getD j 0) []))) := by decide

theorem alnAll_67_67_30 : ∀ j, j < (repChars.getD 67 []).length →
    (normIsRep.getD 67 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_67_67_30.D (m := 5))
        (List.map ZMod.val ((repChars.getD 67 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_67_67_30.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 67 []).getD ((alnPos.getD 67 []).getD j 0) []))) := by decide

theorem alnAll_67_67_35 : ∀ j, j < (repChars.getD 67 []).length →
    (normIsRep.getD 67 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_67_67_35.D (m := 5))
        (List.map ZMod.val ((repChars.getD 67 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_67_67_35.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 67 []).getD ((alnPos.getD 67 []).getD j 0) []))) := by decide

theorem alnAll_67_67_40 : ∀ j, j < (repChars.getD 67 []).length →
    (normIsRep.getD 67 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_67_67_40.D (m := 5))
        (List.map ZMod.val ((repChars.getD 67 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_67_67_40.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 67 []).getD ((alnPos.getD 67 []).getD j 0) []))) := by decide

theorem alnAll_67_67_45 : ∀ j, j < (repChars.getD 67 []).length →
    (normIsRep.getD 67 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_67_67_45.D (m := 5))
        (List.map ZMod.val ((repChars.getD 67 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_67_67_45.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 67 []).getD ((alnPos.getD 67 []).getD j 0) []))) := by decide

theorem alnAll_67_67_50 : ∀ j, j < (repChars.getD 67 []).length →
    (normIsRep.getD 67 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_67_67_50.D (m := 5))
        (List.map ZMod.val ((repChars.getD 67 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_67_67_50.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 67 []).getD ((alnPos.getD 67 []).getD j 0) []))) := by decide

theorem alnAll_67_67_55 : ∀ j, j < (repChars.getD 67 []).length →
    (normIsRep.getD 67 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_67_67_55.D (m := 5))
        (List.map ZMod.val ((repChars.getD 67 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_67_67_55.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 67 []).getD ((alnPos.getD 67 []).getD j 0) []))) := by decide

theorem alnAll_67_67_60 : ∀ j, j < (repChars.getD 67 []).length →
    (normIsRep.getD 67 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_67_67_60.D (m := 5))
        (List.map ZMod.val ((repChars.getD 67 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_67_67_60.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 67 []).getD ((alnPos.getD 67 []).getD j 0) []))) := by decide

theorem alnAll_67_67_65 : ∀ j, j < (repChars.getD 67 []).length →
    (normIsRep.getD 67 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_67_67_65.D (m := 5))
        (List.map ZMod.val ((repChars.getD 67 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_67_67_65.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 67 []).getD ((alnPos.getD 67 []).getD j 0) []))) := by decide

theorem alnAll_67_67_70 : ∀ j, j < (repChars.getD 67 []).length →
    (normIsRep.getD 67 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_67_67_70.D (m := 5))
        (List.map ZMod.val ((repChars.getD 67 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_67_67_70.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 67 []).getD ((alnPos.getD 67 []).getD j 0) []))) := by decide

theorem alnAll_67_67_75 : ∀ j, j < (repChars.getD 67 []).length →
    (normIsRep.getD 67 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_67_67_75.D (m := 5))
        (List.map ZMod.val ((repChars.getD 67 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_67_67_75.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 67 []).getD ((alnPos.getD 67 []).getD j 0) []))) := by decide

theorem alnAll_67_67_80 : ∀ j, j < (repChars.getD 67 []).length →
    (normIsRep.getD 67 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_67_67_80.D (m := 5))
        (List.map ZMod.val ((repChars.getD 67 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_67_67_80.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 67 []).getD ((alnPos.getD 67 []).getD j 0) []))) := by decide

theorem alnAll_67_67_85 : ∀ j, j < (repChars.getD 67 []).length →
    (normIsRep.getD 67 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_67_67_85.D (m := 5))
        (List.map ZMod.val ((repChars.getD 67 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_67_67_85.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 67 []).getD ((alnPos.getD 67 []).getD j 0) []))) := by decide

theorem alnAll_67_67_90 : ∀ j, j < (repChars.getD 67 []).length →
    (normIsRep.getD 67 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_67_67_90.D (m := 5))
        (List.map ZMod.val ((repChars.getD 67 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_67_67_90.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 67 []).getD ((alnPos.getD 67 []).getD j 0) []))) := by decide

end LeanDring.P5Presentation
