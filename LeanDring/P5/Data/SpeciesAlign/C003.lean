/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.Characters.Twin2.CharAlign
import LeanDring.P5.Data.ColRestCheap.C005
import LeanDring.P5.Data.ColRestCheap.C006
import LeanDring.P5.Data.ColRestHeavy.C020
import LeanDring.P5.Data.ColRestHeavy.C021
import LeanDring.P5.Data.ColRestHeavy.C022

/-!
# Species-table cells, α-paired residual decides, chunk 2

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

theorem alnAll_32_32_2 : ∀ j, j < (repChars.getD 32 []).length →
    (normIsRep.getD 32 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_32_32_2.D (m := 25))
        (List.map ZMod.val ((repChars.getD 32 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_32_32_2.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 32 []).getD ((alnPos.getD 32 []).getD j 0) []))) := by decide

theorem alnAll_32_32_3 : ∀ j, j < (repChars.getD 32 []).length →
    (normIsRep.getD 32 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_32_32_3.D (m := 25))
        (List.map ZMod.val ((repChars.getD 32 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_32_32_3.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 32 []).getD ((alnPos.getD 32 []).getD j 0) []))) := by decide

theorem alnAll_32_32_4 : ∀ j, j < (repChars.getD 32 []).length →
    (normIsRep.getD 32 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_32_32_4.D (m := 25))
        (List.map ZMod.val ((repChars.getD 32 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_32_32_4.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 32 []).getD ((alnPos.getD 32 []).getD j 0) []))) := by decide

theorem alnAll_32_32_5 : ∀ j, j < (repChars.getD 32 []).length →
    (normIsRep.getD 32 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_32_32_5.D (m := 25))
        (List.map ZMod.val ((repChars.getD 32 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_32_32_5.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 32 []).getD ((alnPos.getD 32 []).getD j 0) []))) := by decide

theorem alnAll_32_32_10 : ∀ j, j < (repChars.getD 32 []).length →
    (normIsRep.getD 32 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_32_32_10.D (m := 25))
        (List.map ZMod.val ((repChars.getD 32 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_32_32_10.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 32 []).getD ((alnPos.getD 32 []).getD j 0) []))) := by decide

theorem alnAll_32_32_15 : ∀ j, j < (repChars.getD 32 []).length →
    (normIsRep.getD 32 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_32_32_15.D (m := 25))
        (List.map ZMod.val ((repChars.getD 32 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_32_32_15.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 32 []).getD ((alnPos.getD 32 []).getD j 0) []))) := by decide

theorem alnAll_32_32_20 : ∀ j, j < (repChars.getD 32 []).length →
    (normIsRep.getD 32 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_32_32_20.D (m := 25))
        (List.map ZMod.val ((repChars.getD 32 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_32_32_20.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 32 []).getD ((alnPos.getD 32 []).getD j 0) []))) := by decide

theorem alnAll_33_0_0 : ∀ j, j < (repChars.getD 33 []).length →
    (normIsRep.getD 33 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_33_0_0.D (m := 125))
        (List.map ZMod.val ((repChars.getD 33 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_33_0_0.D (m := 125))
        (List.map ZMod.val ((Q2.repChars2.getD 33 []).getD ((alnPos.getD 33 []).getD j 0) []))) := by decide

theorem alnAll_33_12_0 : ∀ j, j < (repChars.getD 33 []).length →
    (normIsRep.getD 33 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_33_12_0.D (m := 125))
        (List.map ZMod.val ((repChars.getD 33 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_33_12_0.D (m := 125))
        (List.map ZMod.val ((Q2.repChars2.getD 33 []).getD ((alnPos.getD 33 []).getD j 0) []))) := by decide

theorem alnAll_33_12_1 : ∀ j, j < (repChars.getD 33 []).length →
    (normIsRep.getD 33 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_33_12_1.D (m := 125))
        (List.map ZMod.val ((repChars.getD 33 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_33_12_1.D (m := 125))
        (List.map ZMod.val ((Q2.repChars2.getD 33 []).getD ((alnPos.getD 33 []).getD j 0) []))) := by decide

theorem alnAll_33_12_2 : ∀ j, j < (repChars.getD 33 []).length →
    (normIsRep.getD 33 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_33_12_2.D (m := 125))
        (List.map ZMod.val ((repChars.getD 33 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_33_12_2.D (m := 125))
        (List.map ZMod.val ((Q2.repChars2.getD 33 []).getD ((alnPos.getD 33 []).getD j 0) []))) := by decide

theorem alnAll_33_12_3 : ∀ j, j < (repChars.getD 33 []).length →
    (normIsRep.getD 33 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_33_12_3.D (m := 125))
        (List.map ZMod.val ((repChars.getD 33 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_33_12_3.D (m := 125))
        (List.map ZMod.val ((Q2.repChars2.getD 33 []).getD ((alnPos.getD 33 []).getD j 0) []))) := by decide

theorem alnAll_33_12_4 : ∀ j, j < (repChars.getD 33 []).length →
    (normIsRep.getD 33 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_33_12_4.D (m := 125))
        (List.map ZMod.val ((repChars.getD 33 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_33_12_4.D (m := 125))
        (List.map ZMod.val ((Q2.repChars2.getD 33 []).getD ((alnPos.getD 33 []).getD j 0) []))) := by decide

theorem alnAll_33_33_0 : ∀ j, j < (repChars.getD 33 []).length →
    (normIsRep.getD 33 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_33_33_0.D (m := 25))
        (List.map ZMod.val ((repChars.getD 33 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_33_33_0.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 33 []).getD ((alnPos.getD 33 []).getD j 0) []))) := by decide

theorem alnAll_33_33_1 : ∀ j, j < (repChars.getD 33 []).length →
    (normIsRep.getD 33 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_33_33_1.D (m := 25))
        (List.map ZMod.val ((repChars.getD 33 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_33_33_1.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 33 []).getD ((alnPos.getD 33 []).getD j 0) []))) := by decide

theorem alnAll_33_33_2 : ∀ j, j < (repChars.getD 33 []).length →
    (normIsRep.getD 33 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_33_33_2.D (m := 25))
        (List.map ZMod.val ((repChars.getD 33 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_33_33_2.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 33 []).getD ((alnPos.getD 33 []).getD j 0) []))) := by decide

theorem alnAll_33_33_3 : ∀ j, j < (repChars.getD 33 []).length →
    (normIsRep.getD 33 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_33_33_3.D (m := 25))
        (List.map ZMod.val ((repChars.getD 33 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_33_33_3.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 33 []).getD ((alnPos.getD 33 []).getD j 0) []))) := by decide

theorem alnAll_33_33_4 : ∀ j, j < (repChars.getD 33 []).length →
    (normIsRep.getD 33 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_33_33_4.D (m := 25))
        (List.map ZMod.val ((repChars.getD 33 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_33_33_4.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 33 []).getD ((alnPos.getD 33 []).getD j 0) []))) := by decide

theorem alnAll_33_33_5 : ∀ j, j < (repChars.getD 33 []).length →
    (normIsRep.getD 33 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_33_33_5.D (m := 25))
        (List.map ZMod.val ((repChars.getD 33 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_33_33_5.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 33 []).getD ((alnPos.getD 33 []).getD j 0) []))) := by decide

theorem alnAll_33_33_10 : ∀ j, j < (repChars.getD 33 []).length →
    (normIsRep.getD 33 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_33_33_10.D (m := 25))
        (List.map ZMod.val ((repChars.getD 33 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_33_33_10.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 33 []).getD ((alnPos.getD 33 []).getD j 0) []))) := by decide

theorem alnAll_33_33_15 : ∀ j, j < (repChars.getD 33 []).length →
    (normIsRep.getD 33 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_33_33_15.D (m := 25))
        (List.map ZMod.val ((repChars.getD 33 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_33_33_15.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 33 []).getD ((alnPos.getD 33 []).getD j 0) []))) := by decide

theorem alnAll_33_33_20 : ∀ j, j < (repChars.getD 33 []).length →
    (normIsRep.getD 33 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_33_33_20.D (m := 25))
        (List.map ZMod.val ((repChars.getD 33 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_33_33_20.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 33 []).getD ((alnPos.getD 33 []).getD j 0) []))) := by decide

theorem alnAll_34_0_0 : ∀ j, j < (repChars.getD 34 []).length →
    (normIsRep.getD 34 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_34_0_0.D (m := 125))
        (List.map ZMod.val ((repChars.getD 34 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_34_0_0.D (m := 125))
        (List.map ZMod.val ((Q2.repChars2.getD 34 []).getD ((alnPos.getD 34 []).getD j 0) []))) := by decide

theorem alnAll_34_12_0 : ∀ j, j < (repChars.getD 34 []).length →
    (normIsRep.getD 34 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_34_12_0.D (m := 125))
        (List.map ZMod.val ((repChars.getD 34 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_34_12_0.D (m := 125))
        (List.map ZMod.val ((Q2.repChars2.getD 34 []).getD ((alnPos.getD 34 []).getD j 0) []))) := by decide

theorem alnAll_34_12_1 : ∀ j, j < (repChars.getD 34 []).length →
    (normIsRep.getD 34 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_34_12_1.D (m := 125))
        (List.map ZMod.val ((repChars.getD 34 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_34_12_1.D (m := 125))
        (List.map ZMod.val ((Q2.repChars2.getD 34 []).getD ((alnPos.getD 34 []).getD j 0) []))) := by decide

theorem alnAll_34_12_2 : ∀ j, j < (repChars.getD 34 []).length →
    (normIsRep.getD 34 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_34_12_2.D (m := 125))
        (List.map ZMod.val ((repChars.getD 34 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_34_12_2.D (m := 125))
        (List.map ZMod.val ((Q2.repChars2.getD 34 []).getD ((alnPos.getD 34 []).getD j 0) []))) := by decide

theorem alnAll_34_12_3 : ∀ j, j < (repChars.getD 34 []).length →
    (normIsRep.getD 34 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_34_12_3.D (m := 125))
        (List.map ZMod.val ((repChars.getD 34 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_34_12_3.D (m := 125))
        (List.map ZMod.val ((Q2.repChars2.getD 34 []).getD ((alnPos.getD 34 []).getD j 0) []))) := by decide

theorem alnAll_34_12_4 : ∀ j, j < (repChars.getD 34 []).length →
    (normIsRep.getD 34 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_34_12_4.D (m := 125))
        (List.map ZMod.val ((repChars.getD 34 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_34_12_4.D (m := 125))
        (List.map ZMod.val ((Q2.repChars2.getD 34 []).getD ((alnPos.getD 34 []).getD j 0) []))) := by decide

theorem alnAll_34_34_0 : ∀ j, j < (repChars.getD 34 []).length →
    (normIsRep.getD 34 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_34_34_0.D (m := 25))
        (List.map ZMod.val ((repChars.getD 34 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_34_34_0.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 34 []).getD ((alnPos.getD 34 []).getD j 0) []))) := by decide

theorem alnAll_34_34_1 : ∀ j, j < (repChars.getD 34 []).length →
    (normIsRep.getD 34 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_34_34_1.D (m := 25))
        (List.map ZMod.val ((repChars.getD 34 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_34_34_1.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 34 []).getD ((alnPos.getD 34 []).getD j 0) []))) := by decide

theorem alnAll_34_34_2 : ∀ j, j < (repChars.getD 34 []).length →
    (normIsRep.getD 34 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_34_34_2.D (m := 25))
        (List.map ZMod.val ((repChars.getD 34 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_34_34_2.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 34 []).getD ((alnPos.getD 34 []).getD j 0) []))) := by decide

theorem alnAll_34_34_3 : ∀ j, j < (repChars.getD 34 []).length →
    (normIsRep.getD 34 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_34_34_3.D (m := 25))
        (List.map ZMod.val ((repChars.getD 34 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_34_34_3.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 34 []).getD ((alnPos.getD 34 []).getD j 0) []))) := by decide

theorem alnAll_34_34_4 : ∀ j, j < (repChars.getD 34 []).length →
    (normIsRep.getD 34 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_34_34_4.D (m := 25))
        (List.map ZMod.val ((repChars.getD 34 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_34_34_4.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 34 []).getD ((alnPos.getD 34 []).getD j 0) []))) := by decide

theorem alnAll_34_34_5 : ∀ j, j < (repChars.getD 34 []).length →
    (normIsRep.getD 34 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_34_34_5.D (m := 25))
        (List.map ZMod.val ((repChars.getD 34 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_34_34_5.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 34 []).getD ((alnPos.getD 34 []).getD j 0) []))) := by decide

theorem alnAll_34_34_10 : ∀ j, j < (repChars.getD 34 []).length →
    (normIsRep.getD 34 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_34_34_10.D (m := 25))
        (List.map ZMod.val ((repChars.getD 34 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_34_34_10.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 34 []).getD ((alnPos.getD 34 []).getD j 0) []))) := by decide

theorem alnAll_34_34_15 : ∀ j, j < (repChars.getD 34 []).length →
    (normIsRep.getD 34 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_34_34_15.D (m := 25))
        (List.map ZMod.val ((repChars.getD 34 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_34_34_15.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 34 []).getD ((alnPos.getD 34 []).getD j 0) []))) := by decide

theorem alnAll_34_34_20 : ∀ j, j < (repChars.getD 34 []).length →
    (normIsRep.getD 34 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_34_34_20.D (m := 25))
        (List.map ZMod.val ((repChars.getD 34 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_34_34_20.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 34 []).getD ((alnPos.getD 34 []).getD j 0) []))) := by decide

theorem alnAll_35_0_0 : ∀ j, j < (repChars.getD 35 []).length →
    (normIsRep.getD 35 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_35_0_0.D (m := 125))
        (List.map ZMod.val ((repChars.getD 35 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_35_0_0.D (m := 125))
        (List.map ZMod.val ((Q2.repChars2.getD 35 []).getD ((alnPos.getD 35 []).getD j 0) []))) := by decide

end LeanDring.P5Presentation
