/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.Characters.Twin2.CharAlign
import LeanDring.P5.Data.ColRestCheap.C008
import LeanDring.P5.Data.ColRestHeavy.C033
import LeanDring.P5.Data.ColRestHeavy.C034

/-!
# Species-table cells, α-paired residual decides, chunk 9

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

theorem alnAll_49_12_2 : ∀ j, j < (repChars.getD 49 []).length →
    (normIsRep.getD 49 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_49_12_2.D (m := 125))
        (List.map ZMod.val ((repChars.getD 49 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_49_12_2.D (m := 125))
        (List.map ZMod.val ((Q2.repChars2.getD 49 []).getD ((alnPos.getD 49 []).getD j 0) []))) := by decide

theorem alnAll_49_12_3 : ∀ j, j < (repChars.getD 49 []).length →
    (normIsRep.getD 49 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_49_12_3.D (m := 125))
        (List.map ZMod.val ((repChars.getD 49 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_49_12_3.D (m := 125))
        (List.map ZMod.val ((Q2.repChars2.getD 49 []).getD ((alnPos.getD 49 []).getD j 0) []))) := by decide

theorem alnAll_49_12_4 : ∀ j, j < (repChars.getD 49 []).length →
    (normIsRep.getD 49 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_49_12_4.D (m := 125))
        (List.map ZMod.val ((repChars.getD 49 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_49_12_4.D (m := 125))
        (List.map ZMod.val ((Q2.repChars2.getD 49 []).getD ((alnPos.getD 49 []).getD j 0) []))) := by decide

theorem alnAll_49_49_0 : ∀ j, j < (repChars.getD 49 []).length →
    (normIsRep.getD 49 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_49_49_0.D (m := 25))
        (List.map ZMod.val ((repChars.getD 49 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_49_49_0.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 49 []).getD ((alnPos.getD 49 []).getD j 0) []))) := by decide

theorem alnAll_49_49_1 : ∀ j, j < (repChars.getD 49 []).length →
    (normIsRep.getD 49 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_49_49_1.D (m := 25))
        (List.map ZMod.val ((repChars.getD 49 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_49_49_1.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 49 []).getD ((alnPos.getD 49 []).getD j 0) []))) := by decide

theorem alnAll_49_49_2 : ∀ j, j < (repChars.getD 49 []).length →
    (normIsRep.getD 49 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_49_49_2.D (m := 25))
        (List.map ZMod.val ((repChars.getD 49 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_49_49_2.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 49 []).getD ((alnPos.getD 49 []).getD j 0) []))) := by decide

theorem alnAll_49_49_3 : ∀ j, j < (repChars.getD 49 []).length →
    (normIsRep.getD 49 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_49_49_3.D (m := 25))
        (List.map ZMod.val ((repChars.getD 49 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_49_49_3.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 49 []).getD ((alnPos.getD 49 []).getD j 0) []))) := by decide

theorem alnAll_49_49_4 : ∀ j, j < (repChars.getD 49 []).length →
    (normIsRep.getD 49 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_49_49_4.D (m := 25))
        (List.map ZMod.val ((repChars.getD 49 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_49_49_4.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 49 []).getD ((alnPos.getD 49 []).getD j 0) []))) := by decide

theorem alnAll_49_49_5 : ∀ j, j < (repChars.getD 49 []).length →
    (normIsRep.getD 49 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_49_49_5.D (m := 25))
        (List.map ZMod.val ((repChars.getD 49 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_49_49_5.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 49 []).getD ((alnPos.getD 49 []).getD j 0) []))) := by decide

theorem alnAll_49_49_10 : ∀ j, j < (repChars.getD 49 []).length →
    (normIsRep.getD 49 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_49_49_10.D (m := 25))
        (List.map ZMod.val ((repChars.getD 49 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_49_49_10.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 49 []).getD ((alnPos.getD 49 []).getD j 0) []))) := by decide

theorem alnAll_49_49_15 : ∀ j, j < (repChars.getD 49 []).length →
    (normIsRep.getD 49 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_49_49_15.D (m := 25))
        (List.map ZMod.val ((repChars.getD 49 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_49_49_15.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 49 []).getD ((alnPos.getD 49 []).getD j 0) []))) := by decide

theorem alnAll_49_49_20 : ∀ j, j < (repChars.getD 49 []).length →
    (normIsRep.getD 49 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_49_49_20.D (m := 25))
        (List.map ZMod.val ((repChars.getD 49 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_49_49_20.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 49 []).getD ((alnPos.getD 49 []).getD j 0) []))) := by decide

theorem alnAll_50_0_0 : ∀ j, j < (repChars.getD 50 []).length →
    (normIsRep.getD 50 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_50_0_0.D (m := 125))
        (List.map ZMod.val ((repChars.getD 50 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_50_0_0.D (m := 125))
        (List.map ZMod.val ((Q2.repChars2.getD 50 []).getD ((alnPos.getD 50 []).getD j 0) []))) := by decide

theorem alnAll_50_12_0 : ∀ j, j < (repChars.getD 50 []).length →
    (normIsRep.getD 50 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_50_12_0.D (m := 125))
        (List.map ZMod.val ((repChars.getD 50 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_50_12_0.D (m := 125))
        (List.map ZMod.val ((Q2.repChars2.getD 50 []).getD ((alnPos.getD 50 []).getD j 0) []))) := by decide

theorem alnAll_50_12_1 : ∀ j, j < (repChars.getD 50 []).length →
    (normIsRep.getD 50 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_50_12_1.D (m := 125))
        (List.map ZMod.val ((repChars.getD 50 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_50_12_1.D (m := 125))
        (List.map ZMod.val ((Q2.repChars2.getD 50 []).getD ((alnPos.getD 50 []).getD j 0) []))) := by decide

theorem alnAll_50_12_2 : ∀ j, j < (repChars.getD 50 []).length →
    (normIsRep.getD 50 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_50_12_2.D (m := 125))
        (List.map ZMod.val ((repChars.getD 50 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_50_12_2.D (m := 125))
        (List.map ZMod.val ((Q2.repChars2.getD 50 []).getD ((alnPos.getD 50 []).getD j 0) []))) := by decide

theorem alnAll_50_12_3 : ∀ j, j < (repChars.getD 50 []).length →
    (normIsRep.getD 50 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_50_12_3.D (m := 125))
        (List.map ZMod.val ((repChars.getD 50 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_50_12_3.D (m := 125))
        (List.map ZMod.val ((Q2.repChars2.getD 50 []).getD ((alnPos.getD 50 []).getD j 0) []))) := by decide

theorem alnAll_50_12_4 : ∀ j, j < (repChars.getD 50 []).length →
    (normIsRep.getD 50 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_50_12_4.D (m := 125))
        (List.map ZMod.val ((repChars.getD 50 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_50_12_4.D (m := 125))
        (List.map ZMod.val ((Q2.repChars2.getD 50 []).getD ((alnPos.getD 50 []).getD j 0) []))) := by decide

theorem alnAll_50_50_0 : ∀ j, j < (repChars.getD 50 []).length →
    (normIsRep.getD 50 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_50_50_0.D (m := 25))
        (List.map ZMod.val ((repChars.getD 50 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_50_50_0.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 50 []).getD ((alnPos.getD 50 []).getD j 0) []))) := by decide

theorem alnAll_50_50_1 : ∀ j, j < (repChars.getD 50 []).length →
    (normIsRep.getD 50 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_50_50_1.D (m := 25))
        (List.map ZMod.val ((repChars.getD 50 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_50_50_1.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 50 []).getD ((alnPos.getD 50 []).getD j 0) []))) := by decide

theorem alnAll_50_50_2 : ∀ j, j < (repChars.getD 50 []).length →
    (normIsRep.getD 50 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_50_50_2.D (m := 25))
        (List.map ZMod.val ((repChars.getD 50 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_50_50_2.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 50 []).getD ((alnPos.getD 50 []).getD j 0) []))) := by decide

theorem alnAll_50_50_3 : ∀ j, j < (repChars.getD 50 []).length →
    (normIsRep.getD 50 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_50_50_3.D (m := 25))
        (List.map ZMod.val ((repChars.getD 50 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_50_50_3.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 50 []).getD ((alnPos.getD 50 []).getD j 0) []))) := by decide

theorem alnAll_50_50_4 : ∀ j, j < (repChars.getD 50 []).length →
    (normIsRep.getD 50 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_50_50_4.D (m := 25))
        (List.map ZMod.val ((repChars.getD 50 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_50_50_4.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 50 []).getD ((alnPos.getD 50 []).getD j 0) []))) := by decide

theorem alnAll_50_50_5 : ∀ j, j < (repChars.getD 50 []).length →
    (normIsRep.getD 50 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_50_50_5.D (m := 25))
        (List.map ZMod.val ((repChars.getD 50 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_50_50_5.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 50 []).getD ((alnPos.getD 50 []).getD j 0) []))) := by decide

theorem alnAll_50_50_10 : ∀ j, j < (repChars.getD 50 []).length →
    (normIsRep.getD 50 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_50_50_10.D (m := 25))
        (List.map ZMod.val ((repChars.getD 50 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_50_50_10.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 50 []).getD ((alnPos.getD 50 []).getD j 0) []))) := by decide

theorem alnAll_50_50_15 : ∀ j, j < (repChars.getD 50 []).length →
    (normIsRep.getD 50 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_50_50_15.D (m := 25))
        (List.map ZMod.val ((repChars.getD 50 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_50_50_15.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 50 []).getD ((alnPos.getD 50 []).getD j 0) []))) := by decide

theorem alnAll_50_50_20 : ∀ j, j < (repChars.getD 50 []).length →
    (normIsRep.getD 50 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_50_50_20.D (m := 25))
        (List.map ZMod.val ((repChars.getD 50 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_50_50_20.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 50 []).getD ((alnPos.getD 50 []).getD j 0) []))) := by decide

theorem alnAll_51_0_0 : ∀ j, j < (repChars.getD 51 []).length →
    (normIsRep.getD 51 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_51_0_0.D (m := 125))
        (List.map ZMod.val ((repChars.getD 51 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_51_0_0.D (m := 125))
        (List.map ZMod.val ((Q2.repChars2.getD 51 []).getD ((alnPos.getD 51 []).getD j 0) []))) := by decide

theorem alnAll_51_12_0 : ∀ j, j < (repChars.getD 51 []).length →
    (normIsRep.getD 51 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_51_12_0.D (m := 125))
        (List.map ZMod.val ((repChars.getD 51 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_51_12_0.D (m := 125))
        (List.map ZMod.val ((Q2.repChars2.getD 51 []).getD ((alnPos.getD 51 []).getD j 0) []))) := by decide

theorem alnAll_51_12_1 : ∀ j, j < (repChars.getD 51 []).length →
    (normIsRep.getD 51 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_51_12_1.D (m := 125))
        (List.map ZMod.val ((repChars.getD 51 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_51_12_1.D (m := 125))
        (List.map ZMod.val ((Q2.repChars2.getD 51 []).getD ((alnPos.getD 51 []).getD j 0) []))) := by decide

theorem alnAll_51_12_2 : ∀ j, j < (repChars.getD 51 []).length →
    (normIsRep.getD 51 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_51_12_2.D (m := 125))
        (List.map ZMod.val ((repChars.getD 51 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_51_12_2.D (m := 125))
        (List.map ZMod.val ((Q2.repChars2.getD 51 []).getD ((alnPos.getD 51 []).getD j 0) []))) := by decide

theorem alnAll_51_12_3 : ∀ j, j < (repChars.getD 51 []).length →
    (normIsRep.getD 51 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_51_12_3.D (m := 125))
        (List.map ZMod.val ((repChars.getD 51 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_51_12_3.D (m := 125))
        (List.map ZMod.val ((Q2.repChars2.getD 51 []).getD ((alnPos.getD 51 []).getD j 0) []))) := by decide

theorem alnAll_51_12_4 : ∀ j, j < (repChars.getD 51 []).length →
    (normIsRep.getD 51 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_51_12_4.D (m := 125))
        (List.map ZMod.val ((repChars.getD 51 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_51_12_4.D (m := 125))
        (List.map ZMod.val ((Q2.repChars2.getD 51 []).getD ((alnPos.getD 51 []).getD j 0) []))) := by decide

theorem alnAll_51_51_0 : ∀ j, j < (repChars.getD 51 []).length →
    (normIsRep.getD 51 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_51_51_0.D (m := 25))
        (List.map ZMod.val ((repChars.getD 51 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_51_51_0.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 51 []).getD ((alnPos.getD 51 []).getD j 0) []))) := by decide

theorem alnAll_51_51_1 : ∀ j, j < (repChars.getD 51 []).length →
    (normIsRep.getD 51 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_51_51_1.D (m := 25))
        (List.map ZMod.val ((repChars.getD 51 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_51_51_1.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 51 []).getD ((alnPos.getD 51 []).getD j 0) []))) := by decide

end LeanDring.P5Presentation
