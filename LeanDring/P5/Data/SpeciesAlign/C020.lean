/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.Characters.Twin2.CharAlign
import LeanDring.P5.Data.ColRestCheap.C168
import LeanDring.P5.Data.ColRestCheap.C169

/-!
# Species-table cells, α-paired residual decides, chunk 19

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

theorem alnAll_76_1_0 : ∀ j, j < (repChars.getD 76 []).length →
    (normIsRep.getD 76 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_1_0.D (m := 25))
        (List.map ZMod.val ((repChars.getD 76 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_1_0.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 76 []).getD ((alnPos.getD 76 []).getD j 0) []))) := by decide

theorem alnAll_76_1_1 : ∀ j, j < (repChars.getD 76 []).length →
    (normIsRep.getD 76 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_1_1.D (m := 25))
        (List.map ZMod.val ((repChars.getD 76 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_1_1.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 76 []).getD ((alnPos.getD 76 []).getD j 0) []))) := by decide

theorem alnAll_76_1_2 : ∀ j, j < (repChars.getD 76 []).length →
    (normIsRep.getD 76 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_1_2.D (m := 25))
        (List.map ZMod.val ((repChars.getD 76 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_1_2.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 76 []).getD ((alnPos.getD 76 []).getD j 0) []))) := by decide

theorem alnAll_76_1_3 : ∀ j, j < (repChars.getD 76 []).length →
    (normIsRep.getD 76 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_1_3.D (m := 25))
        (List.map ZMod.val ((repChars.getD 76 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_1_3.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 76 []).getD ((alnPos.getD 76 []).getD j 0) []))) := by decide

theorem alnAll_76_1_4 : ∀ j, j < (repChars.getD 76 []).length →
    (normIsRep.getD 76 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_1_4.D (m := 25))
        (List.map ZMod.val ((repChars.getD 76 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_1_4.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 76 []).getD ((alnPos.getD 76 []).getD j 0) []))) := by decide

theorem alnAll_76_12_0 : ∀ j, j < (repChars.getD 76 []).length →
    (normIsRep.getD 76 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_12_0.D (m := 25))
        (List.map ZMod.val ((repChars.getD 76 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_12_0.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 76 []).getD ((alnPos.getD 76 []).getD j 0) []))) := by decide

theorem alnAll_76_12_1 : ∀ j, j < (repChars.getD 76 []).length →
    (normIsRep.getD 76 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_12_1.D (m := 25))
        (List.map ZMod.val ((repChars.getD 76 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_12_1.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 76 []).getD ((alnPos.getD 76 []).getD j 0) []))) := by decide

theorem alnAll_76_12_2 : ∀ j, j < (repChars.getD 76 []).length →
    (normIsRep.getD 76 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_12_2.D (m := 25))
        (List.map ZMod.val ((repChars.getD 76 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_12_2.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 76 []).getD ((alnPos.getD 76 []).getD j 0) []))) := by decide

theorem alnAll_76_12_3 : ∀ j, j < (repChars.getD 76 []).length →
    (normIsRep.getD 76 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_12_3.D (m := 25))
        (List.map ZMod.val ((repChars.getD 76 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_12_3.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 76 []).getD ((alnPos.getD 76 []).getD j 0) []))) := by decide

theorem alnAll_76_12_4 : ∀ j, j < (repChars.getD 76 []).length →
    (normIsRep.getD 76 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_12_4.D (m := 25))
        (List.map ZMod.val ((repChars.getD 76 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_12_4.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 76 []).getD ((alnPos.getD 76 []).getD j 0) []))) := by decide

theorem alnAll_76_19_0 : ∀ j, j < (repChars.getD 76 []).length →
    (normIsRep.getD 76 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_19_0.D (m := 25))
        (List.map ZMod.val ((repChars.getD 76 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_19_0.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 76 []).getD ((alnPos.getD 76 []).getD j 0) []))) := by decide

theorem alnAll_76_19_1 : ∀ j, j < (repChars.getD 76 []).length →
    (normIsRep.getD 76 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_19_1.D (m := 25))
        (List.map ZMod.val ((repChars.getD 76 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_19_1.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 76 []).getD ((alnPos.getD 76 []).getD j 0) []))) := by decide

theorem alnAll_76_19_2 : ∀ j, j < (repChars.getD 76 []).length →
    (normIsRep.getD 76 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_19_2.D (m := 25))
        (List.map ZMod.val ((repChars.getD 76 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_19_2.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 76 []).getD ((alnPos.getD 76 []).getD j 0) []))) := by decide

theorem alnAll_76_19_3 : ∀ j, j < (repChars.getD 76 []).length →
    (normIsRep.getD 76 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_19_3.D (m := 25))
        (List.map ZMod.val ((repChars.getD 76 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_19_3.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 76 []).getD ((alnPos.getD 76 []).getD j 0) []))) := by decide

theorem alnAll_76_19_4 : ∀ j, j < (repChars.getD 76 []).length →
    (normIsRep.getD 76 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_19_4.D (m := 25))
        (List.map ZMod.val ((repChars.getD 76 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_19_4.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 76 []).getD ((alnPos.getD 76 []).getD j 0) []))) := by decide

theorem alnAll_76_19_5 : ∀ j, j < (repChars.getD 76 []).length →
    (normIsRep.getD 76 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_19_5.D (m := 25))
        (List.map ZMod.val ((repChars.getD 76 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_76_19_5.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 76 []).getD ((alnPos.getD 76 []).getD j 0) []))) := by decide

end LeanDring.P5Presentation
