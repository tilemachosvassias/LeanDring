/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.Characters.Twin2.CharAlign
import LeanDring.P5.Data.ColCdd.C001
import LeanDring.P5.Data.ColRestCheap.C011
import LeanDring.P5.Data.ColRestCheap.C012
import LeanDring.P5.Data.ColRestCheap.C014

/-!
# Species-table cells, α-paired residual decides, chunk 24

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

theorem alnAll_105_10_1 : ∀ j, j < (repChars.getD 105 []).length →
    (normIsRep.getD 105 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_105_10_1.D (m := 25))
        (List.map ZMod.val ((repChars.getD 105 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_105_10_1.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 105 []).getD ((alnPos.getD 105 []).getD j 0) []))) := by decide

theorem alnAll_105_10_2 : ∀ j, j < (repChars.getD 105 []).length →
    (normIsRep.getD 105 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_105_10_2.D (m := 25))
        (List.map ZMod.val ((repChars.getD 105 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_105_10_2.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 105 []).getD ((alnPos.getD 105 []).getD j 0) []))) := by decide

theorem alnAll_105_10_3 : ∀ j, j < (repChars.getD 105 []).length →
    (normIsRep.getD 105 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_105_10_3.D (m := 25))
        (List.map ZMod.val ((repChars.getD 105 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_105_10_3.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 105 []).getD ((alnPos.getD 105 []).getD j 0) []))) := by decide

theorem alnAll_105_10_4 : ∀ j, j < (repChars.getD 105 []).length →
    (normIsRep.getD 105 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_105_10_4.D (m := 25))
        (List.map ZMod.val ((repChars.getD 105 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_105_10_4.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 105 []).getD ((alnPos.getD 105 []).getD j 0) []))) := by decide

theorem alnAll_105_12_0 : ∀ j, j < (repChars.getD 105 []).length →
    (normIsRep.getD 105 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_105_12_0.D (m := 25))
        (List.map ZMod.val ((repChars.getD 105 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_105_12_0.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 105 []).getD ((alnPos.getD 105 []).getD j 0) []))) := by decide

theorem alnAll_105_12_1 : ∀ j, j < (repChars.getD 105 []).length →
    (normIsRep.getD 105 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_105_12_1.D (m := 25))
        (List.map ZMod.val ((repChars.getD 105 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_105_12_1.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 105 []).getD ((alnPos.getD 105 []).getD j 0) []))) := by decide

theorem alnAll_105_12_2 : ∀ j, j < (repChars.getD 105 []).length →
    (normIsRep.getD 105 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_105_12_2.D (m := 25))
        (List.map ZMod.val ((repChars.getD 105 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_105_12_2.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 105 []).getD ((alnPos.getD 105 []).getD j 0) []))) := by decide

theorem alnAll_105_12_3 : ∀ j, j < (repChars.getD 105 []).length →
    (normIsRep.getD 105 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_105_12_3.D (m := 25))
        (List.map ZMod.val ((repChars.getD 105 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_105_12_3.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 105 []).getD ((alnPos.getD 105 []).getD j 0) []))) := by decide

theorem alnAll_105_12_4 : ∀ j, j < (repChars.getD 105 []).length →
    (normIsRep.getD 105 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_105_12_4.D (m := 25))
        (List.map ZMod.val ((repChars.getD 105 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_105_12_4.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 105 []).getD ((alnPos.getD 105 []).getD j 0) []))) := by decide

theorem alnAll_105_43_0 : ∀ j, j < (repChars.getD 105 []).length →
    (normIsRep.getD 105 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_105_43_0.D (m := 25))
        (List.map ZMod.val ((repChars.getD 105 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_105_43_0.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 105 []).getD ((alnPos.getD 105 []).getD j 0) []))) := by decide

theorem alnAll_105_43_1 : ∀ j, j < (repChars.getD 105 []).length →
    (normIsRep.getD 105 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_105_43_1.D (m := 25))
        (List.map ZMod.val ((repChars.getD 105 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_105_43_1.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 105 []).getD ((alnPos.getD 105 []).getD j 0) []))) := by decide

theorem alnAll_105_43_2 : ∀ j, j < (repChars.getD 105 []).length →
    (normIsRep.getD 105 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_105_43_2.D (m := 25))
        (List.map ZMod.val ((repChars.getD 105 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_105_43_2.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 105 []).getD ((alnPos.getD 105 []).getD j 0) []))) := by decide

theorem alnAll_105_43_3 : ∀ j, j < (repChars.getD 105 []).length →
    (normIsRep.getD 105 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_105_43_3.D (m := 25))
        (List.map ZMod.val ((repChars.getD 105 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_105_43_3.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 105 []).getD ((alnPos.getD 105 []).getD j 0) []))) := by decide

theorem alnAll_105_43_4 : ∀ j, j < (repChars.getD 105 []).length →
    (normIsRep.getD 105 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_105_43_4.D (m := 25))
        (List.map ZMod.val ((repChars.getD 105 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_105_43_4.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 105 []).getD ((alnPos.getD 105 []).getD j 0) []))) := by decide

theorem alnAll_105_43_5 : ∀ j, j < (repChars.getD 105 []).length →
    (normIsRep.getD 105 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCertDiv_105_43_5.D1 (m := 25))
        (List.map ZMod.val ((repChars.getD 105 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCertDiv_105_43_5.D2 (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 105 []).getD ((alnPos.getD 105 []).getD j 0) []))) := by decide

theorem alnAll_105_43_10 : ∀ j, j < (repChars.getD 105 []).length →
    (normIsRep.getD 105 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCertDiv_105_43_10.D1 (m := 25))
        (List.map ZMod.val ((repChars.getD 105 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCertDiv_105_43_10.D2 (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 105 []).getD ((alnPos.getD 105 []).getD j 0) []))) := by decide

theorem alnAll_105_43_15 : ∀ j, j < (repChars.getD 105 []).length →
    (normIsRep.getD 105 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCertDiv_105_43_15.D1 (m := 25))
        (List.map ZMod.val ((repChars.getD 105 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCertDiv_105_43_15.D2 (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 105 []).getD ((alnPos.getD 105 []).getD j 0) []))) := by decide

theorem alnAll_105_43_20 : ∀ j, j < (repChars.getD 105 []).length →
    (normIsRep.getD 105 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCertDiv_105_43_20.D1 (m := 25))
        (List.map ZMod.val ((repChars.getD 105 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCertDiv_105_43_20.D2 (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 105 []).getD ((alnPos.getD 105 []).getD j 0) []))) := by decide

theorem alnAll_105_53_0 : ∀ j, j < (repChars.getD 105 []).length →
    (normIsRep.getD 105 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_105_53_0.D (m := 25))
        (List.map ZMod.val ((repChars.getD 105 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_105_53_0.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 105 []).getD ((alnPos.getD 105 []).getD j 0) []))) := by decide

theorem alnAll_105_53_1 : ∀ j, j < (repChars.getD 105 []).length →
    (normIsRep.getD 105 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_105_53_1.D (m := 25))
        (List.map ZMod.val ((repChars.getD 105 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_105_53_1.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 105 []).getD ((alnPos.getD 105 []).getD j 0) []))) := by decide

theorem alnAll_105_53_2 : ∀ j, j < (repChars.getD 105 []).length →
    (normIsRep.getD 105 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_105_53_2.D (m := 25))
        (List.map ZMod.val ((repChars.getD 105 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_105_53_2.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 105 []).getD ((alnPos.getD 105 []).getD j 0) []))) := by decide

theorem alnAll_105_53_3 : ∀ j, j < (repChars.getD 105 []).length →
    (normIsRep.getD 105 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_105_53_3.D (m := 25))
        (List.map ZMod.val ((repChars.getD 105 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_105_53_3.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 105 []).getD ((alnPos.getD 105 []).getD j 0) []))) := by decide

theorem alnAll_105_53_4 : ∀ j, j < (repChars.getD 105 []).length →
    (normIsRep.getD 105 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_105_53_4.D (m := 25))
        (List.map ZMod.val ((repChars.getD 105 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_105_53_4.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 105 []).getD ((alnPos.getD 105 []).getD j 0) []))) := by decide

theorem alnAll_105_53_5 : ∀ j, j < (repChars.getD 105 []).length →
    (normIsRep.getD 105 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_105_53_5.D (m := 25))
        (List.map ZMod.val ((repChars.getD 105 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_105_53_5.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 105 []).getD ((alnPos.getD 105 []).getD j 0) []))) := by decide

theorem alnAll_105_53_10 : ∀ j, j < (repChars.getD 105 []).length →
    (normIsRep.getD 105 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_105_53_10.D (m := 25))
        (List.map ZMod.val ((repChars.getD 105 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_105_53_10.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 105 []).getD ((alnPos.getD 105 []).getD j 0) []))) := by decide

theorem alnAll_105_53_15 : ∀ j, j < (repChars.getD 105 []).length →
    (normIsRep.getD 105 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_105_53_15.D (m := 25))
        (List.map ZMod.val ((repChars.getD 105 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_105_53_15.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 105 []).getD ((alnPos.getD 105 []).getD j 0) []))) := by decide

theorem alnAll_105_53_20 : ∀ j, j < (repChars.getD 105 []).length →
    (normIsRep.getD 105 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_105_53_20.D (m := 25))
        (List.map ZMod.val ((repChars.getD 105 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_105_53_20.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 105 []).getD ((alnPos.getD 105 []).getD j 0) []))) := by decide

theorem alnAll_105_105_0 : ∀ j, j < (repChars.getD 105 []).length →
    (normIsRep.getD 105 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_105_105_0.D (m := 25))
        (List.map ZMod.val ((repChars.getD 105 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_105_105_0.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 105 []).getD ((alnPos.getD 105 []).getD j 0) []))) := by decide

theorem alnAll_105_105_1 : ∀ j, j < (repChars.getD 105 []).length →
    (normIsRep.getD 105 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_105_105_1.D (m := 25))
        (List.map ZMod.val ((repChars.getD 105 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_105_105_1.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 105 []).getD ((alnPos.getD 105 []).getD j 0) []))) := by decide

theorem alnAll_105_105_2 : ∀ j, j < (repChars.getD 105 []).length →
    (normIsRep.getD 105 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_105_105_2.D (m := 25))
        (List.map ZMod.val ((repChars.getD 105 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_105_105_2.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 105 []).getD ((alnPos.getD 105 []).getD j 0) []))) := by decide

theorem alnAll_105_105_3 : ∀ j, j < (repChars.getD 105 []).length →
    (normIsRep.getD 105 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_105_105_3.D (m := 25))
        (List.map ZMod.val ((repChars.getD 105 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_105_105_3.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 105 []).getD ((alnPos.getD 105 []).getD j 0) []))) := by decide

theorem alnAll_105_105_4 : ∀ j, j < (repChars.getD 105 []).length →
    (normIsRep.getD 105 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_105_105_4.D (m := 25))
        (List.map ZMod.val ((repChars.getD 105 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_105_105_4.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 105 []).getD ((alnPos.getD 105 []).getD j 0) []))) := by decide

theorem alnAll_105_105_5 : ∀ j, j < (repChars.getD 105 []).length →
    (normIsRep.getD 105 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_105_105_5.D (m := 25))
        (List.map ZMod.val ((repChars.getD 105 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_105_105_5.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 105 []).getD ((alnPos.getD 105 []).getD j 0) []))) := by decide

theorem alnAll_105_105_10 : ∀ j, j < (repChars.getD 105 []).length →
    (normIsRep.getD 105 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_105_105_10.D (m := 25))
        (List.map ZMod.val ((repChars.getD 105 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_105_105_10.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 105 []).getD ((alnPos.getD 105 []).getD j 0) []))) := by decide

theorem alnAll_105_105_15 : ∀ j, j < (repChars.getD 105 []).length →
    (normIsRep.getD 105 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_105_105_15.D (m := 25))
        (List.map ZMod.val ((repChars.getD 105 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_105_105_15.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 105 []).getD ((alnPos.getD 105 []).getD j 0) []))) := by decide

theorem alnAll_105_105_20 : ∀ j, j < (repChars.getD 105 []).length →
    (normIsRep.getD 105 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_105_105_20.D (m := 25))
        (List.map ZMod.val ((repChars.getD 105 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_105_105_20.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 105 []).getD ((alnPos.getD 105 []).getD j 0) []))) := by decide

theorem alnAll_105_105_25 : ∀ j, j < (repChars.getD 105 []).length →
    (normIsRep.getD 105 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_105_105_25.D (m := 25))
        (List.map ZMod.val ((repChars.getD 105 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_105_105_25.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 105 []).getD ((alnPos.getD 105 []).getD j 0) []))) := by decide

theorem alnAll_105_105_50 : ∀ j, j < (repChars.getD 105 []).length →
    (normIsRep.getD 105 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_105_105_50.D (m := 25))
        (List.map ZMod.val ((repChars.getD 105 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_105_105_50.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 105 []).getD ((alnPos.getD 105 []).getD j 0) []))) := by decide

theorem alnAll_105_105_75 : ∀ j, j < (repChars.getD 105 []).length →
    (normIsRep.getD 105 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_105_105_75.D (m := 25))
        (List.map ZMod.val ((repChars.getD 105 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_105_105_75.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 105 []).getD ((alnPos.getD 105 []).getD j 0) []))) := by decide

theorem alnAll_105_105_100 : ∀ j, j < (repChars.getD 105 []).length →
    (normIsRep.getD 105 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_105_105_100.D (m := 25))
        (List.map ZMod.val ((repChars.getD 105 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_105_105_100.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 105 []).getD ((alnPos.getD 105 []).getD j 0) []))) := by decide

theorem alnAll_110_0_0 : ∀ j, j < (repChars.getD 110 []).length →
    (normIsRep.getD 110 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_110_0_0.D (m := 25))
        (List.map ZMod.val ((repChars.getD 110 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_110_0_0.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 110 []).getD ((alnPos.getD 110 []).getD j 0) []))) := by decide

theorem alnAll_110_10_0 : ∀ j, j < (repChars.getD 110 []).length →
    (normIsRep.getD 110 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_110_10_0.D (m := 25))
        (List.map ZMod.val ((repChars.getD 110 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_110_10_0.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 110 []).getD ((alnPos.getD 110 []).getD j 0) []))) := by decide

theorem alnAll_110_10_1 : ∀ j, j < (repChars.getD 110 []).length →
    (normIsRep.getD 110 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_110_10_1.D (m := 25))
        (List.map ZMod.val ((repChars.getD 110 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_110_10_1.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 110 []).getD ((alnPos.getD 110 []).getD j 0) []))) := by decide

theorem alnAll_110_10_2 : ∀ j, j < (repChars.getD 110 []).length →
    (normIsRep.getD 110 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_110_10_2.D (m := 25))
        (List.map ZMod.val ((repChars.getD 110 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_110_10_2.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 110 []).getD ((alnPos.getD 110 []).getD j 0) []))) := by decide

theorem alnAll_110_10_3 : ∀ j, j < (repChars.getD 110 []).length →
    (normIsRep.getD 110 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_110_10_3.D (m := 25))
        (List.map ZMod.val ((repChars.getD 110 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_110_10_3.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 110 []).getD ((alnPos.getD 110 []).getD j 0) []))) := by decide

theorem alnAll_110_10_4 : ∀ j, j < (repChars.getD 110 []).length →
    (normIsRep.getD 110 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_110_10_4.D (m := 25))
        (List.map ZMod.val ((repChars.getD 110 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_110_10_4.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 110 []).getD ((alnPos.getD 110 []).getD j 0) []))) := by decide

theorem alnAll_110_12_0 : ∀ j, j < (repChars.getD 110 []).length →
    (normIsRep.getD 110 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_110_12_0.D (m := 25))
        (List.map ZMod.val ((repChars.getD 110 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_110_12_0.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 110 []).getD ((alnPos.getD 110 []).getD j 0) []))) := by decide

theorem alnAll_110_12_1 : ∀ j, j < (repChars.getD 110 []).length →
    (normIsRep.getD 110 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_110_12_1.D (m := 25))
        (List.map ZMod.val ((repChars.getD 110 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_110_12_1.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 110 []).getD ((alnPos.getD 110 []).getD j 0) []))) := by decide

theorem alnAll_110_12_2 : ∀ j, j < (repChars.getD 110 []).length →
    (normIsRep.getD 110 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_110_12_2.D (m := 25))
        (List.map ZMod.val ((repChars.getD 110 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_110_12_2.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 110 []).getD ((alnPos.getD 110 []).getD j 0) []))) := by decide

theorem alnAll_110_12_3 : ∀ j, j < (repChars.getD 110 []).length →
    (normIsRep.getD 110 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_110_12_3.D (m := 25))
        (List.map ZMod.val ((repChars.getD 110 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_110_12_3.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 110 []).getD ((alnPos.getD 110 []).getD j 0) []))) := by decide

theorem alnAll_110_12_4 : ∀ j, j < (repChars.getD 110 []).length →
    (normIsRep.getD 110 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_110_12_4.D (m := 25))
        (List.map ZMod.val ((repChars.getD 110 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_110_12_4.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 110 []).getD ((alnPos.getD 110 []).getD j 0) []))) := by decide

theorem alnAll_110_48_0 : ∀ j, j < (repChars.getD 110 []).length →
    (normIsRep.getD 110 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_110_48_0.D (m := 25))
        (List.map ZMod.val ((repChars.getD 110 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_110_48_0.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 110 []).getD ((alnPos.getD 110 []).getD j 0) []))) := by decide

theorem alnAll_110_48_1 : ∀ j, j < (repChars.getD 110 []).length →
    (normIsRep.getD 110 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_110_48_1.D (m := 25))
        (List.map ZMod.val ((repChars.getD 110 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_110_48_1.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 110 []).getD ((alnPos.getD 110 []).getD j 0) []))) := by decide

theorem alnAll_110_48_2 : ∀ j, j < (repChars.getD 110 []).length →
    (normIsRep.getD 110 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_110_48_2.D (m := 25))
        (List.map ZMod.val ((repChars.getD 110 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_110_48_2.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 110 []).getD ((alnPos.getD 110 []).getD j 0) []))) := by decide

theorem alnAll_110_48_3 : ∀ j, j < (repChars.getD 110 []).length →
    (normIsRep.getD 110 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_110_48_3.D (m := 25))
        (List.map ZMod.val ((repChars.getD 110 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_110_48_3.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 110 []).getD ((alnPos.getD 110 []).getD j 0) []))) := by decide

theorem alnAll_110_48_4 : ∀ j, j < (repChars.getD 110 []).length →
    (normIsRep.getD 110 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_110_48_4.D (m := 25))
        (List.map ZMod.val ((repChars.getD 110 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_110_48_4.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 110 []).getD ((alnPos.getD 110 []).getD j 0) []))) := by decide

end LeanDring.P5Presentation
