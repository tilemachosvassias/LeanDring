/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.Characters.Twin2.CharAlign
import LeanDring.P5.Data.ColCdd.C001
import LeanDring.P5.Data.ColRestCheap.C014
import LeanDring.P5.Data.ColRestCheap.C015

/-!
# Species-table cells, α-paired residual decides, chunk 25

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

theorem alnAll_110_48_5 : ∀ j, j < (repChars.getD 110 []).length →
    (normIsRep.getD 110 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCertDiv_110_48_5.D1 (m := 25))
        (List.map ZMod.val ((repChars.getD 110 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCertDiv_110_48_5.D2 (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 110 []).getD ((alnPos.getD 110 []).getD j 0) []))) := by decide

theorem alnAll_110_48_10 : ∀ j, j < (repChars.getD 110 []).length →
    (normIsRep.getD 110 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCertDiv_110_48_10.D1 (m := 25))
        (List.map ZMod.val ((repChars.getD 110 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCertDiv_110_48_10.D2 (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 110 []).getD ((alnPos.getD 110 []).getD j 0) []))) := by decide

theorem alnAll_110_48_15 : ∀ j, j < (repChars.getD 110 []).length →
    (normIsRep.getD 110 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCertDiv_110_48_15.D1 (m := 25))
        (List.map ZMod.val ((repChars.getD 110 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCertDiv_110_48_15.D2 (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 110 []).getD ((alnPos.getD 110 []).getD j 0) []))) := by decide

theorem alnAll_110_48_20 : ∀ j, j < (repChars.getD 110 []).length →
    (normIsRep.getD 110 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCertDiv_110_48_20.D1 (m := 25))
        (List.map ZMod.val ((repChars.getD 110 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCertDiv_110_48_20.D2 (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 110 []).getD ((alnPos.getD 110 []).getD j 0) []))) := by decide

theorem alnAll_110_53_0 : ∀ j, j < (repChars.getD 110 []).length →
    (normIsRep.getD 110 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_110_53_0.D (m := 25))
        (List.map ZMod.val ((repChars.getD 110 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_110_53_0.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 110 []).getD ((alnPos.getD 110 []).getD j 0) []))) := by decide

theorem alnAll_110_53_1 : ∀ j, j < (repChars.getD 110 []).length →
    (normIsRep.getD 110 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_110_53_1.D (m := 25))
        (List.map ZMod.val ((repChars.getD 110 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_110_53_1.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 110 []).getD ((alnPos.getD 110 []).getD j 0) []))) := by decide

theorem alnAll_110_53_2 : ∀ j, j < (repChars.getD 110 []).length →
    (normIsRep.getD 110 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_110_53_2.D (m := 25))
        (List.map ZMod.val ((repChars.getD 110 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_110_53_2.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 110 []).getD ((alnPos.getD 110 []).getD j 0) []))) := by decide

theorem alnAll_110_53_3 : ∀ j, j < (repChars.getD 110 []).length →
    (normIsRep.getD 110 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_110_53_3.D (m := 25))
        (List.map ZMod.val ((repChars.getD 110 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_110_53_3.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 110 []).getD ((alnPos.getD 110 []).getD j 0) []))) := by decide

theorem alnAll_110_53_4 : ∀ j, j < (repChars.getD 110 []).length →
    (normIsRep.getD 110 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_110_53_4.D (m := 25))
        (List.map ZMod.val ((repChars.getD 110 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_110_53_4.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 110 []).getD ((alnPos.getD 110 []).getD j 0) []))) := by decide

theorem alnAll_110_53_5 : ∀ j, j < (repChars.getD 110 []).length →
    (normIsRep.getD 110 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_110_53_5.D (m := 25))
        (List.map ZMod.val ((repChars.getD 110 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_110_53_5.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 110 []).getD ((alnPos.getD 110 []).getD j 0) []))) := by decide

theorem alnAll_110_53_10 : ∀ j, j < (repChars.getD 110 []).length →
    (normIsRep.getD 110 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_110_53_10.D (m := 25))
        (List.map ZMod.val ((repChars.getD 110 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_110_53_10.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 110 []).getD ((alnPos.getD 110 []).getD j 0) []))) := by decide

theorem alnAll_110_53_15 : ∀ j, j < (repChars.getD 110 []).length →
    (normIsRep.getD 110 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_110_53_15.D (m := 25))
        (List.map ZMod.val ((repChars.getD 110 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_110_53_15.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 110 []).getD ((alnPos.getD 110 []).getD j 0) []))) := by decide

theorem alnAll_110_53_20 : ∀ j, j < (repChars.getD 110 []).length →
    (normIsRep.getD 110 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_110_53_20.D (m := 25))
        (List.map ZMod.val ((repChars.getD 110 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_110_53_20.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 110 []).getD ((alnPos.getD 110 []).getD j 0) []))) := by decide

theorem alnAll_110_110_0 : ∀ j, j < (repChars.getD 110 []).length →
    (normIsRep.getD 110 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_110_110_0.D (m := 25))
        (List.map ZMod.val ((repChars.getD 110 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_110_110_0.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 110 []).getD ((alnPos.getD 110 []).getD j 0) []))) := by decide

theorem alnAll_110_110_1 : ∀ j, j < (repChars.getD 110 []).length →
    (normIsRep.getD 110 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_110_110_1.D (m := 25))
        (List.map ZMod.val ((repChars.getD 110 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_110_110_1.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 110 []).getD ((alnPos.getD 110 []).getD j 0) []))) := by decide

theorem alnAll_110_110_2 : ∀ j, j < (repChars.getD 110 []).length →
    (normIsRep.getD 110 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_110_110_2.D (m := 25))
        (List.map ZMod.val ((repChars.getD 110 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_110_110_2.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 110 []).getD ((alnPos.getD 110 []).getD j 0) []))) := by decide

theorem alnAll_110_110_3 : ∀ j, j < (repChars.getD 110 []).length →
    (normIsRep.getD 110 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_110_110_3.D (m := 25))
        (List.map ZMod.val ((repChars.getD 110 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_110_110_3.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 110 []).getD ((alnPos.getD 110 []).getD j 0) []))) := by decide

theorem alnAll_110_110_4 : ∀ j, j < (repChars.getD 110 []).length →
    (normIsRep.getD 110 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_110_110_4.D (m := 25))
        (List.map ZMod.val ((repChars.getD 110 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_110_110_4.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 110 []).getD ((alnPos.getD 110 []).getD j 0) []))) := by decide

theorem alnAll_110_110_5 : ∀ j, j < (repChars.getD 110 []).length →
    (normIsRep.getD 110 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_110_110_5.D (m := 25))
        (List.map ZMod.val ((repChars.getD 110 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_110_110_5.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 110 []).getD ((alnPos.getD 110 []).getD j 0) []))) := by decide

theorem alnAll_110_110_10 : ∀ j, j < (repChars.getD 110 []).length →
    (normIsRep.getD 110 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_110_110_10.D (m := 25))
        (List.map ZMod.val ((repChars.getD 110 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_110_110_10.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 110 []).getD ((alnPos.getD 110 []).getD j 0) []))) := by decide

theorem alnAll_110_110_15 : ∀ j, j < (repChars.getD 110 []).length →
    (normIsRep.getD 110 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_110_110_15.D (m := 25))
        (List.map ZMod.val ((repChars.getD 110 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_110_110_15.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 110 []).getD ((alnPos.getD 110 []).getD j 0) []))) := by decide

theorem alnAll_110_110_20 : ∀ j, j < (repChars.getD 110 []).length →
    (normIsRep.getD 110 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_110_110_20.D (m := 25))
        (List.map ZMod.val ((repChars.getD 110 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_110_110_20.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 110 []).getD ((alnPos.getD 110 []).getD j 0) []))) := by decide

theorem alnAll_110_110_25 : ∀ j, j < (repChars.getD 110 []).length →
    (normIsRep.getD 110 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_110_110_25.D (m := 25))
        (List.map ZMod.val ((repChars.getD 110 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_110_110_25.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 110 []).getD ((alnPos.getD 110 []).getD j 0) []))) := by decide

theorem alnAll_110_110_50 : ∀ j, j < (repChars.getD 110 []).length →
    (normIsRep.getD 110 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_110_110_50.D (m := 25))
        (List.map ZMod.val ((repChars.getD 110 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_110_110_50.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 110 []).getD ((alnPos.getD 110 []).getD j 0) []))) := by decide

theorem alnAll_110_110_75 : ∀ j, j < (repChars.getD 110 []).length →
    (normIsRep.getD 110 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_110_110_75.D (m := 25))
        (List.map ZMod.val ((repChars.getD 110 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_110_110_75.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 110 []).getD ((alnPos.getD 110 []).getD j 0) []))) := by decide

theorem alnAll_110_110_100 : ∀ j, j < (repChars.getD 110 []).length →
    (normIsRep.getD 110 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_110_110_100.D (m := 25))
        (List.map ZMod.val ((repChars.getD 110 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_110_110_100.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 110 []).getD ((alnPos.getD 110 []).getD j 0) []))) := by decide

end LeanDring.P5Presentation
