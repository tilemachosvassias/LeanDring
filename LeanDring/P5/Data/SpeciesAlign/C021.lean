/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.Characters.Twin2.CharAlign
import LeanDring.P5.Data.ColRestCheap.C169
import LeanDring.P5.Data.ColRestCheap.C170

/-!
# Species-table cells, α-paired residual decides, chunk 20

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

theorem alnAll_76_19_10 : ∀ j, j < (repChars.getD 76 []).length →
    (normIsRep.getD 76 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_19_10.D (m := 25))
        (List.map ZMod.val ((repChars.getD 76 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_19_10.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 76 []).getD ((alnPos.getD 76 []).getD j 0) []))) := by decide

theorem alnAll_76_19_15 : ∀ j, j < (repChars.getD 76 []).length →
    (normIsRep.getD 76 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_19_15.D (m := 25))
        (List.map ZMod.val ((repChars.getD 76 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_19_15.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 76 []).getD ((alnPos.getD 76 []).getD j 0) []))) := by decide

theorem alnAll_76_19_20 : ∀ j, j < (repChars.getD 76 []).length →
    (normIsRep.getD 76 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_19_20.D (m := 25))
        (List.map ZMod.val ((repChars.getD 76 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_19_20.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 76 []).getD ((alnPos.getD 76 []).getD j 0) []))) := by decide

theorem alnAll_76_32_0 : ∀ j, j < (repChars.getD 76 []).length →
    (normIsRep.getD 76 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_32_0.D (m := 5))
        (List.map ZMod.val ((repChars.getD 76 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_32_0.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 76 []).getD ((alnPos.getD 76 []).getD j 0) []))) := by decide

theorem alnAll_76_32_1 : ∀ j, j < (repChars.getD 76 []).length →
    (normIsRep.getD 76 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_32_1.D (m := 5))
        (List.map ZMod.val ((repChars.getD 76 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_32_1.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 76 []).getD ((alnPos.getD 76 []).getD j 0) []))) := by decide

theorem alnAll_76_32_2 : ∀ j, j < (repChars.getD 76 []).length →
    (normIsRep.getD 76 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_32_2.D (m := 5))
        (List.map ZMod.val ((repChars.getD 76 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_32_2.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 76 []).getD ((alnPos.getD 76 []).getD j 0) []))) := by decide

theorem alnAll_76_32_3 : ∀ j, j < (repChars.getD 76 []).length →
    (normIsRep.getD 76 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_32_3.D (m := 5))
        (List.map ZMod.val ((repChars.getD 76 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_32_3.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 76 []).getD ((alnPos.getD 76 []).getD j 0) []))) := by decide

theorem alnAll_76_32_4 : ∀ j, j < (repChars.getD 76 []).length →
    (normIsRep.getD 76 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_32_4.D (m := 5))
        (List.map ZMod.val ((repChars.getD 76 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_32_4.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 76 []).getD ((alnPos.getD 76 []).getD j 0) []))) := by decide

theorem alnAll_76_32_5 : ∀ j, j < (repChars.getD 76 []).length →
    (normIsRep.getD 76 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_32_5.D (m := 5))
        (List.map ZMod.val ((repChars.getD 76 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_32_5.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 76 []).getD ((alnPos.getD 76 []).getD j 0) []))) := by decide

theorem alnAll_76_32_10 : ∀ j, j < (repChars.getD 76 []).length →
    (normIsRep.getD 76 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_32_10.D (m := 5))
        (List.map ZMod.val ((repChars.getD 76 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_32_10.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 76 []).getD ((alnPos.getD 76 []).getD j 0) []))) := by decide

theorem alnAll_76_32_15 : ∀ j, j < (repChars.getD 76 []).length →
    (normIsRep.getD 76 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_32_15.D (m := 5))
        (List.map ZMod.val ((repChars.getD 76 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_32_15.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 76 []).getD ((alnPos.getD 76 []).getD j 0) []))) := by decide

theorem alnAll_76_32_20 : ∀ j, j < (repChars.getD 76 []).length →
    (normIsRep.getD 76 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_32_20.D (m := 5))
        (List.map ZMod.val ((repChars.getD 76 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_32_20.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 76 []).getD ((alnPos.getD 76 []).getD j 0) []))) := by decide

theorem alnAll_76_37_0 : ∀ j, j < (repChars.getD 76 []).length →
    (normIsRep.getD 76 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_37_0.D (m := 5))
        (List.map ZMod.val ((repChars.getD 76 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_37_0.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 76 []).getD ((alnPos.getD 76 []).getD j 0) []))) := by decide

theorem alnAll_76_37_1 : ∀ j, j < (repChars.getD 76 []).length →
    (normIsRep.getD 76 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_37_1.D (m := 5))
        (List.map ZMod.val ((repChars.getD 76 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_37_1.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 76 []).getD ((alnPos.getD 76 []).getD j 0) []))) := by decide

theorem alnAll_76_37_2 : ∀ j, j < (repChars.getD 76 []).length →
    (normIsRep.getD 76 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_37_2.D (m := 5))
        (List.map ZMod.val ((repChars.getD 76 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_37_2.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 76 []).getD ((alnPos.getD 76 []).getD j 0) []))) := by decide

theorem alnAll_76_37_3 : ∀ j, j < (repChars.getD 76 []).length →
    (normIsRep.getD 76 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_37_3.D (m := 5))
        (List.map ZMod.val ((repChars.getD 76 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_37_3.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 76 []).getD ((alnPos.getD 76 []).getD j 0) []))) := by decide

theorem alnAll_76_37_4 : ∀ j, j < (repChars.getD 76 []).length →
    (normIsRep.getD 76 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_37_4.D (m := 5))
        (List.map ZMod.val ((repChars.getD 76 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_37_4.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 76 []).getD ((alnPos.getD 76 []).getD j 0) []))) := by decide

theorem alnAll_76_37_5 : ∀ j, j < (repChars.getD 76 []).length →
    (normIsRep.getD 76 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_37_5.D (m := 5))
        (List.map ZMod.val ((repChars.getD 76 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_37_5.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 76 []).getD ((alnPos.getD 76 []).getD j 0) []))) := by decide

theorem alnAll_76_37_10 : ∀ j, j < (repChars.getD 76 []).length →
    (normIsRep.getD 76 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_37_10.D (m := 5))
        (List.map ZMod.val ((repChars.getD 76 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_37_10.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 76 []).getD ((alnPos.getD 76 []).getD j 0) []))) := by decide

theorem alnAll_76_37_15 : ∀ j, j < (repChars.getD 76 []).length →
    (normIsRep.getD 76 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_37_15.D (m := 5))
        (List.map ZMod.val ((repChars.getD 76 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_37_15.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 76 []).getD ((alnPos.getD 76 []).getD j 0) []))) := by decide

theorem alnAll_76_37_20 : ∀ j, j < (repChars.getD 76 []).length →
    (normIsRep.getD 76 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_37_20.D (m := 5))
        (List.map ZMod.val ((repChars.getD 76 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_37_20.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 76 []).getD ((alnPos.getD 76 []).getD j 0) []))) := by decide

theorem alnAll_76_42_0 : ∀ j, j < (repChars.getD 76 []).length →
    (normIsRep.getD 76 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_42_0.D (m := 5))
        (List.map ZMod.val ((repChars.getD 76 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_42_0.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 76 []).getD ((alnPos.getD 76 []).getD j 0) []))) := by decide

theorem alnAll_76_42_1 : ∀ j, j < (repChars.getD 76 []).length →
    (normIsRep.getD 76 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_42_1.D (m := 5))
        (List.map ZMod.val ((repChars.getD 76 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_42_1.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 76 []).getD ((alnPos.getD 76 []).getD j 0) []))) := by decide

theorem alnAll_76_42_2 : ∀ j, j < (repChars.getD 76 []).length →
    (normIsRep.getD 76 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_42_2.D (m := 5))
        (List.map ZMod.val ((repChars.getD 76 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_42_2.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 76 []).getD ((alnPos.getD 76 []).getD j 0) []))) := by decide

theorem alnAll_76_42_3 : ∀ j, j < (repChars.getD 76 []).length →
    (normIsRep.getD 76 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_42_3.D (m := 5))
        (List.map ZMod.val ((repChars.getD 76 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_42_3.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 76 []).getD ((alnPos.getD 76 []).getD j 0) []))) := by decide

theorem alnAll_76_42_4 : ∀ j, j < (repChars.getD 76 []).length →
    (normIsRep.getD 76 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_42_4.D (m := 5))
        (List.map ZMod.val ((repChars.getD 76 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_42_4.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 76 []).getD ((alnPos.getD 76 []).getD j 0) []))) := by decide

theorem alnAll_76_42_5 : ∀ j, j < (repChars.getD 76 []).length →
    (normIsRep.getD 76 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_42_5.D (m := 5))
        (List.map ZMod.val ((repChars.getD 76 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_42_5.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 76 []).getD ((alnPos.getD 76 []).getD j 0) []))) := by decide

theorem alnAll_76_42_10 : ∀ j, j < (repChars.getD 76 []).length →
    (normIsRep.getD 76 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_42_10.D (m := 5))
        (List.map ZMod.val ((repChars.getD 76 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_42_10.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 76 []).getD ((alnPos.getD 76 []).getD j 0) []))) := by decide

theorem alnAll_76_42_15 : ∀ j, j < (repChars.getD 76 []).length →
    (normIsRep.getD 76 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_42_15.D (m := 5))
        (List.map ZMod.val ((repChars.getD 76 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_42_15.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 76 []).getD ((alnPos.getD 76 []).getD j 0) []))) := by decide

theorem alnAll_76_42_20 : ∀ j, j < (repChars.getD 76 []).length →
    (normIsRep.getD 76 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_42_20.D (m := 5))
        (List.map ZMod.val ((repChars.getD 76 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_42_20.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 76 []).getD ((alnPos.getD 76 []).getD j 0) []))) := by decide

theorem alnAll_76_47_0 : ∀ j, j < (repChars.getD 76 []).length →
    (normIsRep.getD 76 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_47_0.D (m := 5))
        (List.map ZMod.val ((repChars.getD 76 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_47_0.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 76 []).getD ((alnPos.getD 76 []).getD j 0) []))) := by decide

theorem alnAll_76_47_1 : ∀ j, j < (repChars.getD 76 []).length →
    (normIsRep.getD 76 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_47_1.D (m := 5))
        (List.map ZMod.val ((repChars.getD 76 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_47_1.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 76 []).getD ((alnPos.getD 76 []).getD j 0) []))) := by decide

theorem alnAll_76_47_2 : ∀ j, j < (repChars.getD 76 []).length →
    (normIsRep.getD 76 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_47_2.D (m := 5))
        (List.map ZMod.val ((repChars.getD 76 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_47_2.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 76 []).getD ((alnPos.getD 76 []).getD j 0) []))) := by decide

theorem alnAll_76_47_3 : ∀ j, j < (repChars.getD 76 []).length →
    (normIsRep.getD 76 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_47_3.D (m := 5))
        (List.map ZMod.val ((repChars.getD 76 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_47_3.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 76 []).getD ((alnPos.getD 76 []).getD j 0) []))) := by decide

theorem alnAll_76_47_4 : ∀ j, j < (repChars.getD 76 []).length →
    (normIsRep.getD 76 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_47_4.D (m := 5))
        (List.map ZMod.val ((repChars.getD 76 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_47_4.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 76 []).getD ((alnPos.getD 76 []).getD j 0) []))) := by decide

theorem alnAll_76_47_5 : ∀ j, j < (repChars.getD 76 []).length →
    (normIsRep.getD 76 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_47_5.D (m := 5))
        (List.map ZMod.val ((repChars.getD 76 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_47_5.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 76 []).getD ((alnPos.getD 76 []).getD j 0) []))) := by decide

theorem alnAll_76_47_10 : ∀ j, j < (repChars.getD 76 []).length →
    (normIsRep.getD 76 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_47_10.D (m := 5))
        (List.map ZMod.val ((repChars.getD 76 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_47_10.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 76 []).getD ((alnPos.getD 76 []).getD j 0) []))) := by decide

theorem alnAll_76_47_15 : ∀ j, j < (repChars.getD 76 []).length →
    (normIsRep.getD 76 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_47_15.D (m := 5))
        (List.map ZMod.val ((repChars.getD 76 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_47_15.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 76 []).getD ((alnPos.getD 76 []).getD j 0) []))) := by decide

theorem alnAll_76_47_20 : ∀ j, j < (repChars.getD 76 []).length →
    (normIsRep.getD 76 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_47_20.D (m := 5))
        (List.map ZMod.val ((repChars.getD 76 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_47_20.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 76 []).getD ((alnPos.getD 76 []).getD j 0) []))) := by decide

theorem alnAll_76_52_0 : ∀ j, j < (repChars.getD 76 []).length →
    (normIsRep.getD 76 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_52_0.D (m := 5))
        (List.map ZMod.val ((repChars.getD 76 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_52_0.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 76 []).getD ((alnPos.getD 76 []).getD j 0) []))) := by decide

theorem alnAll_76_52_1 : ∀ j, j < (repChars.getD 76 []).length →
    (normIsRep.getD 76 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_52_1.D (m := 5))
        (List.map ZMod.val ((repChars.getD 76 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_52_1.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 76 []).getD ((alnPos.getD 76 []).getD j 0) []))) := by decide

theorem alnAll_76_52_2 : ∀ j, j < (repChars.getD 76 []).length →
    (normIsRep.getD 76 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_52_2.D (m := 5))
        (List.map ZMod.val ((repChars.getD 76 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_52_2.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 76 []).getD ((alnPos.getD 76 []).getD j 0) []))) := by decide

theorem alnAll_76_52_3 : ∀ j, j < (repChars.getD 76 []).length →
    (normIsRep.getD 76 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_52_3.D (m := 5))
        (List.map ZMod.val ((repChars.getD 76 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_52_3.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 76 []).getD ((alnPos.getD 76 []).getD j 0) []))) := by decide

theorem alnAll_76_52_4 : ∀ j, j < (repChars.getD 76 []).length →
    (normIsRep.getD 76 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_52_4.D (m := 5))
        (List.map ZMod.val ((repChars.getD 76 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_52_4.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 76 []).getD ((alnPos.getD 76 []).getD j 0) []))) := by decide

theorem alnAll_76_52_5 : ∀ j, j < (repChars.getD 76 []).length →
    (normIsRep.getD 76 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_52_5.D (m := 5))
        (List.map ZMod.val ((repChars.getD 76 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_52_5.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 76 []).getD ((alnPos.getD 76 []).getD j 0) []))) := by decide

theorem alnAll_76_52_10 : ∀ j, j < (repChars.getD 76 []).length →
    (normIsRep.getD 76 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_52_10.D (m := 5))
        (List.map ZMod.val ((repChars.getD 76 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_52_10.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 76 []).getD ((alnPos.getD 76 []).getD j 0) []))) := by decide

theorem alnAll_76_52_15 : ∀ j, j < (repChars.getD 76 []).length →
    (normIsRep.getD 76 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_52_15.D (m := 5))
        (List.map ZMod.val ((repChars.getD 76 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_52_15.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 76 []).getD ((alnPos.getD 76 []).getD j 0) []))) := by decide

theorem alnAll_76_52_20 : ∀ j, j < (repChars.getD 76 []).length →
    (normIsRep.getD 76 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_52_20.D (m := 5))
        (List.map ZMod.val ((repChars.getD 76 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_52_20.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 76 []).getD ((alnPos.getD 76 []).getD j 0) []))) := by decide

theorem alnAll_76_76_0 : ∀ j, j < (repChars.getD 76 []).length →
    (normIsRep.getD 76 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_76_0.D (m := 5))
        (List.map ZMod.val ((repChars.getD 76 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_76_0.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 76 []).getD ((alnPos.getD 76 []).getD j 0) []))) := by decide

theorem alnAll_76_76_1 : ∀ j, j < (repChars.getD 76 []).length →
    (normIsRep.getD 76 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_76_1.D (m := 5))
        (List.map ZMod.val ((repChars.getD 76 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_76_1.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 76 []).getD ((alnPos.getD 76 []).getD j 0) []))) := by decide

theorem alnAll_76_76_2 : ∀ j, j < (repChars.getD 76 []).length →
    (normIsRep.getD 76 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_76_2.D (m := 5))
        (List.map ZMod.val ((repChars.getD 76 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_76_2.D (m := 5))
        (List.map ZMod.val ((Q2.repChars2.getD 76 []).getD ((alnPos.getD 76 []).getD j 0) []))) := by decide

end LeanDring.P5Presentation
