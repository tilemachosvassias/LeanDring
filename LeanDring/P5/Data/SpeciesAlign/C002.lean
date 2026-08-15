/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.Characters.Twin2.CharAlign
import LeanDring.P5.Data.ColRestCheap.C005
import LeanDring.P5.Data.ColRestHeavy.C018
import LeanDring.P5.Data.ColRestHeavy.C019
import LeanDring.P5.Data.ColRestHeavy.C020

/-!
# Species-table cells, α-paired residual decides, chunk 1

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

theorem alnAll_30_12_2 : ∀ j, j < (repChars.getD 30 []).length →
    (normIsRep.getD 30 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_30_12_2.D (m := 125))
        (List.map ZMod.val ((repChars.getD 30 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_30_12_2.D (m := 125))
        (List.map ZMod.val ((Q2.repChars2.getD 30 []).getD ((alnPos.getD 30 []).getD j 0) []))) := by decide

theorem alnAll_30_12_3 : ∀ j, j < (repChars.getD 30 []).length →
    (normIsRep.getD 30 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_30_12_3.D (m := 125))
        (List.map ZMod.val ((repChars.getD 30 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_30_12_3.D (m := 125))
        (List.map ZMod.val ((Q2.repChars2.getD 30 []).getD ((alnPos.getD 30 []).getD j 0) []))) := by decide

theorem alnAll_30_12_4 : ∀ j, j < (repChars.getD 30 []).length →
    (normIsRep.getD 30 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_30_12_4.D (m := 125))
        (List.map ZMod.val ((repChars.getD 30 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_30_12_4.D (m := 125))
        (List.map ZMod.val ((Q2.repChars2.getD 30 []).getD ((alnPos.getD 30 []).getD j 0) []))) := by decide

theorem alnAll_30_30_0 : ∀ j, j < (repChars.getD 30 []).length →
    (normIsRep.getD 30 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_30_30_0.D (m := 25))
        (List.map ZMod.val ((repChars.getD 30 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_30_30_0.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 30 []).getD ((alnPos.getD 30 []).getD j 0) []))) := by decide

theorem alnAll_30_30_1 : ∀ j, j < (repChars.getD 30 []).length →
    (normIsRep.getD 30 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_30_30_1.D (m := 25))
        (List.map ZMod.val ((repChars.getD 30 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_30_30_1.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 30 []).getD ((alnPos.getD 30 []).getD j 0) []))) := by decide

theorem alnAll_30_30_2 : ∀ j, j < (repChars.getD 30 []).length →
    (normIsRep.getD 30 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_30_30_2.D (m := 25))
        (List.map ZMod.val ((repChars.getD 30 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_30_30_2.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 30 []).getD ((alnPos.getD 30 []).getD j 0) []))) := by decide

theorem alnAll_30_30_3 : ∀ j, j < (repChars.getD 30 []).length →
    (normIsRep.getD 30 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_30_30_3.D (m := 25))
        (List.map ZMod.val ((repChars.getD 30 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_30_30_3.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 30 []).getD ((alnPos.getD 30 []).getD j 0) []))) := by decide

theorem alnAll_30_30_4 : ∀ j, j < (repChars.getD 30 []).length →
    (normIsRep.getD 30 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_30_30_4.D (m := 25))
        (List.map ZMod.val ((repChars.getD 30 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_30_30_4.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 30 []).getD ((alnPos.getD 30 []).getD j 0) []))) := by decide

theorem alnAll_30_30_5 : ∀ j, j < (repChars.getD 30 []).length →
    (normIsRep.getD 30 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_30_30_5.D (m := 25))
        (List.map ZMod.val ((repChars.getD 30 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_30_30_5.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 30 []).getD ((alnPos.getD 30 []).getD j 0) []))) := by decide

theorem alnAll_30_30_10 : ∀ j, j < (repChars.getD 30 []).length →
    (normIsRep.getD 30 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_30_30_10.D (m := 25))
        (List.map ZMod.val ((repChars.getD 30 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_30_30_10.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 30 []).getD ((alnPos.getD 30 []).getD j 0) []))) := by decide

theorem alnAll_30_30_15 : ∀ j, j < (repChars.getD 30 []).length →
    (normIsRep.getD 30 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_30_30_15.D (m := 25))
        (List.map ZMod.val ((repChars.getD 30 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_30_30_15.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 30 []).getD ((alnPos.getD 30 []).getD j 0) []))) := by decide

theorem alnAll_30_30_20 : ∀ j, j < (repChars.getD 30 []).length →
    (normIsRep.getD 30 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_30_30_20.D (m := 25))
        (List.map ZMod.val ((repChars.getD 30 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_30_30_20.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 30 []).getD ((alnPos.getD 30 []).getD j 0) []))) := by decide

theorem alnAll_31_0_0 : ∀ j, j < (repChars.getD 31 []).length →
    (normIsRep.getD 31 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_31_0_0.D (m := 125))
        (List.map ZMod.val ((repChars.getD 31 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_31_0_0.D (m := 125))
        (List.map ZMod.val ((Q2.repChars2.getD 31 []).getD ((alnPos.getD 31 []).getD j 0) []))) := by decide

theorem alnAll_31_12_0 : ∀ j, j < (repChars.getD 31 []).length →
    (normIsRep.getD 31 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_31_12_0.D (m := 125))
        (List.map ZMod.val ((repChars.getD 31 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_31_12_0.D (m := 125))
        (List.map ZMod.val ((Q2.repChars2.getD 31 []).getD ((alnPos.getD 31 []).getD j 0) []))) := by decide

theorem alnAll_31_12_1 : ∀ j, j < (repChars.getD 31 []).length →
    (normIsRep.getD 31 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_31_12_1.D (m := 125))
        (List.map ZMod.val ((repChars.getD 31 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_31_12_1.D (m := 125))
        (List.map ZMod.val ((Q2.repChars2.getD 31 []).getD ((alnPos.getD 31 []).getD j 0) []))) := by decide

theorem alnAll_31_12_2 : ∀ j, j < (repChars.getD 31 []).length →
    (normIsRep.getD 31 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_31_12_2.D (m := 125))
        (List.map ZMod.val ((repChars.getD 31 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_31_12_2.D (m := 125))
        (List.map ZMod.val ((Q2.repChars2.getD 31 []).getD ((alnPos.getD 31 []).getD j 0) []))) := by decide

theorem alnAll_31_12_3 : ∀ j, j < (repChars.getD 31 []).length →
    (normIsRep.getD 31 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_31_12_3.D (m := 125))
        (List.map ZMod.val ((repChars.getD 31 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_31_12_3.D (m := 125))
        (List.map ZMod.val ((Q2.repChars2.getD 31 []).getD ((alnPos.getD 31 []).getD j 0) []))) := by decide

theorem alnAll_31_12_4 : ∀ j, j < (repChars.getD 31 []).length →
    (normIsRep.getD 31 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_31_12_4.D (m := 125))
        (List.map ZMod.val ((repChars.getD 31 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_31_12_4.D (m := 125))
        (List.map ZMod.val ((Q2.repChars2.getD 31 []).getD ((alnPos.getD 31 []).getD j 0) []))) := by decide

theorem alnAll_31_31_0 : ∀ j, j < (repChars.getD 31 []).length →
    (normIsRep.getD 31 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_31_31_0.D (m := 25))
        (List.map ZMod.val ((repChars.getD 31 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_31_31_0.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 31 []).getD ((alnPos.getD 31 []).getD j 0) []))) := by decide

theorem alnAll_31_31_1 : ∀ j, j < (repChars.getD 31 []).length →
    (normIsRep.getD 31 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_31_31_1.D (m := 25))
        (List.map ZMod.val ((repChars.getD 31 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_31_31_1.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 31 []).getD ((alnPos.getD 31 []).getD j 0) []))) := by decide

theorem alnAll_31_31_2 : ∀ j, j < (repChars.getD 31 []).length →
    (normIsRep.getD 31 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_31_31_2.D (m := 25))
        (List.map ZMod.val ((repChars.getD 31 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_31_31_2.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 31 []).getD ((alnPos.getD 31 []).getD j 0) []))) := by decide

theorem alnAll_31_31_3 : ∀ j, j < (repChars.getD 31 []).length →
    (normIsRep.getD 31 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_31_31_3.D (m := 25))
        (List.map ZMod.val ((repChars.getD 31 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_31_31_3.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 31 []).getD ((alnPos.getD 31 []).getD j 0) []))) := by decide

theorem alnAll_31_31_4 : ∀ j, j < (repChars.getD 31 []).length →
    (normIsRep.getD 31 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_31_31_4.D (m := 25))
        (List.map ZMod.val ((repChars.getD 31 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_31_31_4.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 31 []).getD ((alnPos.getD 31 []).getD j 0) []))) := by decide

theorem alnAll_31_31_5 : ∀ j, j < (repChars.getD 31 []).length →
    (normIsRep.getD 31 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_31_31_5.D (m := 25))
        (List.map ZMod.val ((repChars.getD 31 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_31_31_5.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 31 []).getD ((alnPos.getD 31 []).getD j 0) []))) := by decide

theorem alnAll_31_31_10 : ∀ j, j < (repChars.getD 31 []).length →
    (normIsRep.getD 31 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_31_31_10.D (m := 25))
        (List.map ZMod.val ((repChars.getD 31 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_31_31_10.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 31 []).getD ((alnPos.getD 31 []).getD j 0) []))) := by decide

theorem alnAll_31_31_15 : ∀ j, j < (repChars.getD 31 []).length →
    (normIsRep.getD 31 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_31_31_15.D (m := 25))
        (List.map ZMod.val ((repChars.getD 31 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_31_31_15.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 31 []).getD ((alnPos.getD 31 []).getD j 0) []))) := by decide

theorem alnAll_31_31_20 : ∀ j, j < (repChars.getD 31 []).length →
    (normIsRep.getD 31 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_31_31_20.D (m := 25))
        (List.map ZMod.val ((repChars.getD 31 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_31_31_20.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 31 []).getD ((alnPos.getD 31 []).getD j 0) []))) := by decide

theorem alnAll_32_0_0 : ∀ j, j < (repChars.getD 32 []).length →
    (normIsRep.getD 32 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_32_0_0.D (m := 125))
        (List.map ZMod.val ((repChars.getD 32 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_32_0_0.D (m := 125))
        (List.map ZMod.val ((Q2.repChars2.getD 32 []).getD ((alnPos.getD 32 []).getD j 0) []))) := by decide

theorem alnAll_32_12_0 : ∀ j, j < (repChars.getD 32 []).length →
    (normIsRep.getD 32 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_32_12_0.D (m := 125))
        (List.map ZMod.val ((repChars.getD 32 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_32_12_0.D (m := 125))
        (List.map ZMod.val ((Q2.repChars2.getD 32 []).getD ((alnPos.getD 32 []).getD j 0) []))) := by decide

theorem alnAll_32_12_1 : ∀ j, j < (repChars.getD 32 []).length →
    (normIsRep.getD 32 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_32_12_1.D (m := 125))
        (List.map ZMod.val ((repChars.getD 32 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_32_12_1.D (m := 125))
        (List.map ZMod.val ((Q2.repChars2.getD 32 []).getD ((alnPos.getD 32 []).getD j 0) []))) := by decide

theorem alnAll_32_12_2 : ∀ j, j < (repChars.getD 32 []).length →
    (normIsRep.getD 32 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_32_12_2.D (m := 125))
        (List.map ZMod.val ((repChars.getD 32 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_32_12_2.D (m := 125))
        (List.map ZMod.val ((Q2.repChars2.getD 32 []).getD ((alnPos.getD 32 []).getD j 0) []))) := by decide

theorem alnAll_32_12_3 : ∀ j, j < (repChars.getD 32 []).length →
    (normIsRep.getD 32 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_32_12_3.D (m := 125))
        (List.map ZMod.val ((repChars.getD 32 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_32_12_3.D (m := 125))
        (List.map ZMod.val ((Q2.repChars2.getD 32 []).getD ((alnPos.getD 32 []).getD j 0) []))) := by decide

theorem alnAll_32_12_4 : ∀ j, j < (repChars.getD 32 []).length →
    (normIsRep.getD 32 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_32_12_4.D (m := 125))
        (List.map ZMod.val ((repChars.getD 32 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_32_12_4.D (m := 125))
        (List.map ZMod.val ((Q2.repChars2.getD 32 []).getD ((alnPos.getD 32 []).getD j 0) []))) := by decide

theorem alnAll_32_32_0 : ∀ j, j < (repChars.getD 32 []).length →
    (normIsRep.getD 32 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_32_32_0.D (m := 25))
        (List.map ZMod.val ((repChars.getD 32 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_32_32_0.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 32 []).getD ((alnPos.getD 32 []).getD j 0) []))) := by decide

theorem alnAll_32_32_1 : ∀ j, j < (repChars.getD 32 []).length →
    (normIsRep.getD 32 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_32_32_1.D (m := 25))
        (List.map ZMod.val ((repChars.getD 32 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_32_32_1.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 32 []).getD ((alnPos.getD 32 []).getD j 0) []))) := by decide

end LeanDring.P5Presentation
