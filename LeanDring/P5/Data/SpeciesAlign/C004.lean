/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.Characters.Twin2.CharAlign
import LeanDring.P5.Data.ColRestCheap.C006
import LeanDring.P5.Data.ColRestHeavy.C022
import LeanDring.P5.Data.ColRestHeavy.C023
import LeanDring.P5.Data.ColRestHeavy.C024

/-!
# Species-table cells, α-paired residual decides, chunk 3

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

theorem alnAll_35_12_0 : ∀ j, j < (repChars.getD 35 []).length →
    (normIsRep.getD 35 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_35_12_0.D (m := 125))
        (List.map ZMod.val ((repChars.getD 35 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_35_12_0.D (m := 125))
        (List.map ZMod.val ((Q2.repChars2.getD 35 []).getD ((alnPos.getD 35 []).getD j 0) []))) := by decide

theorem alnAll_35_12_1 : ∀ j, j < (repChars.getD 35 []).length →
    (normIsRep.getD 35 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_35_12_1.D (m := 125))
        (List.map ZMod.val ((repChars.getD 35 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_35_12_1.D (m := 125))
        (List.map ZMod.val ((Q2.repChars2.getD 35 []).getD ((alnPos.getD 35 []).getD j 0) []))) := by decide

theorem alnAll_35_12_2 : ∀ j, j < (repChars.getD 35 []).length →
    (normIsRep.getD 35 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_35_12_2.D (m := 125))
        (List.map ZMod.val ((repChars.getD 35 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_35_12_2.D (m := 125))
        (List.map ZMod.val ((Q2.repChars2.getD 35 []).getD ((alnPos.getD 35 []).getD j 0) []))) := by decide

theorem alnAll_35_12_3 : ∀ j, j < (repChars.getD 35 []).length →
    (normIsRep.getD 35 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_35_12_3.D (m := 125))
        (List.map ZMod.val ((repChars.getD 35 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_35_12_3.D (m := 125))
        (List.map ZMod.val ((Q2.repChars2.getD 35 []).getD ((alnPos.getD 35 []).getD j 0) []))) := by decide

theorem alnAll_35_12_4 : ∀ j, j < (repChars.getD 35 []).length →
    (normIsRep.getD 35 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_35_12_4.D (m := 125))
        (List.map ZMod.val ((repChars.getD 35 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_35_12_4.D (m := 125))
        (List.map ZMod.val ((Q2.repChars2.getD 35 []).getD ((alnPos.getD 35 []).getD j 0) []))) := by decide

theorem alnAll_35_35_0 : ∀ j, j < (repChars.getD 35 []).length →
    (normIsRep.getD 35 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_35_35_0.D (m := 25))
        (List.map ZMod.val ((repChars.getD 35 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_35_35_0.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 35 []).getD ((alnPos.getD 35 []).getD j 0) []))) := by decide

theorem alnAll_35_35_1 : ∀ j, j < (repChars.getD 35 []).length →
    (normIsRep.getD 35 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_35_35_1.D (m := 25))
        (List.map ZMod.val ((repChars.getD 35 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_35_35_1.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 35 []).getD ((alnPos.getD 35 []).getD j 0) []))) := by decide

theorem alnAll_35_35_2 : ∀ j, j < (repChars.getD 35 []).length →
    (normIsRep.getD 35 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_35_35_2.D (m := 25))
        (List.map ZMod.val ((repChars.getD 35 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_35_35_2.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 35 []).getD ((alnPos.getD 35 []).getD j 0) []))) := by decide

theorem alnAll_35_35_3 : ∀ j, j < (repChars.getD 35 []).length →
    (normIsRep.getD 35 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_35_35_3.D (m := 25))
        (List.map ZMod.val ((repChars.getD 35 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_35_35_3.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 35 []).getD ((alnPos.getD 35 []).getD j 0) []))) := by decide

theorem alnAll_35_35_4 : ∀ j, j < (repChars.getD 35 []).length →
    (normIsRep.getD 35 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_35_35_4.D (m := 25))
        (List.map ZMod.val ((repChars.getD 35 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_35_35_4.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 35 []).getD ((alnPos.getD 35 []).getD j 0) []))) := by decide

theorem alnAll_35_35_5 : ∀ j, j < (repChars.getD 35 []).length →
    (normIsRep.getD 35 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_35_35_5.D (m := 25))
        (List.map ZMod.val ((repChars.getD 35 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_35_35_5.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 35 []).getD ((alnPos.getD 35 []).getD j 0) []))) := by decide

theorem alnAll_35_35_10 : ∀ j, j < (repChars.getD 35 []).length →
    (normIsRep.getD 35 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_35_35_10.D (m := 25))
        (List.map ZMod.val ((repChars.getD 35 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_35_35_10.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 35 []).getD ((alnPos.getD 35 []).getD j 0) []))) := by decide

theorem alnAll_35_35_15 : ∀ j, j < (repChars.getD 35 []).length →
    (normIsRep.getD 35 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_35_35_15.D (m := 25))
        (List.map ZMod.val ((repChars.getD 35 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_35_35_15.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 35 []).getD ((alnPos.getD 35 []).getD j 0) []))) := by decide

theorem alnAll_35_35_20 : ∀ j, j < (repChars.getD 35 []).length →
    (normIsRep.getD 35 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_35_35_20.D (m := 25))
        (List.map ZMod.val ((repChars.getD 35 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_35_35_20.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 35 []).getD ((alnPos.getD 35 []).getD j 0) []))) := by decide

theorem alnAll_36_0_0 : ∀ j, j < (repChars.getD 36 []).length →
    (normIsRep.getD 36 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_36_0_0.D (m := 125))
        (List.map ZMod.val ((repChars.getD 36 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_36_0_0.D (m := 125))
        (List.map ZMod.val ((Q2.repChars2.getD 36 []).getD ((alnPos.getD 36 []).getD j 0) []))) := by decide

theorem alnAll_36_12_0 : ∀ j, j < (repChars.getD 36 []).length →
    (normIsRep.getD 36 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_36_12_0.D (m := 125))
        (List.map ZMod.val ((repChars.getD 36 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_36_12_0.D (m := 125))
        (List.map ZMod.val ((Q2.repChars2.getD 36 []).getD ((alnPos.getD 36 []).getD j 0) []))) := by decide

theorem alnAll_36_12_1 : ∀ j, j < (repChars.getD 36 []).length →
    (normIsRep.getD 36 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_36_12_1.D (m := 125))
        (List.map ZMod.val ((repChars.getD 36 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_36_12_1.D (m := 125))
        (List.map ZMod.val ((Q2.repChars2.getD 36 []).getD ((alnPos.getD 36 []).getD j 0) []))) := by decide

theorem alnAll_36_12_2 : ∀ j, j < (repChars.getD 36 []).length →
    (normIsRep.getD 36 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_36_12_2.D (m := 125))
        (List.map ZMod.val ((repChars.getD 36 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_36_12_2.D (m := 125))
        (List.map ZMod.val ((Q2.repChars2.getD 36 []).getD ((alnPos.getD 36 []).getD j 0) []))) := by decide

theorem alnAll_36_12_3 : ∀ j, j < (repChars.getD 36 []).length →
    (normIsRep.getD 36 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_36_12_3.D (m := 125))
        (List.map ZMod.val ((repChars.getD 36 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_36_12_3.D (m := 125))
        (List.map ZMod.val ((Q2.repChars2.getD 36 []).getD ((alnPos.getD 36 []).getD j 0) []))) := by decide

theorem alnAll_36_12_4 : ∀ j, j < (repChars.getD 36 []).length →
    (normIsRep.getD 36 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_36_12_4.D (m := 125))
        (List.map ZMod.val ((repChars.getD 36 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_36_12_4.D (m := 125))
        (List.map ZMod.val ((Q2.repChars2.getD 36 []).getD ((alnPos.getD 36 []).getD j 0) []))) := by decide

theorem alnAll_36_36_0 : ∀ j, j < (repChars.getD 36 []).length →
    (normIsRep.getD 36 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_36_36_0.D (m := 25))
        (List.map ZMod.val ((repChars.getD 36 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_36_36_0.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 36 []).getD ((alnPos.getD 36 []).getD j 0) []))) := by decide

theorem alnAll_36_36_1 : ∀ j, j < (repChars.getD 36 []).length →
    (normIsRep.getD 36 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_36_36_1.D (m := 25))
        (List.map ZMod.val ((repChars.getD 36 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_36_36_1.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 36 []).getD ((alnPos.getD 36 []).getD j 0) []))) := by decide

theorem alnAll_36_36_2 : ∀ j, j < (repChars.getD 36 []).length →
    (normIsRep.getD 36 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_36_36_2.D (m := 25))
        (List.map ZMod.val ((repChars.getD 36 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_36_36_2.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 36 []).getD ((alnPos.getD 36 []).getD j 0) []))) := by decide

theorem alnAll_36_36_3 : ∀ j, j < (repChars.getD 36 []).length →
    (normIsRep.getD 36 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_36_36_3.D (m := 25))
        (List.map ZMod.val ((repChars.getD 36 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_36_36_3.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 36 []).getD ((alnPos.getD 36 []).getD j 0) []))) := by decide

theorem alnAll_36_36_4 : ∀ j, j < (repChars.getD 36 []).length →
    (normIsRep.getD 36 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_36_36_4.D (m := 25))
        (List.map ZMod.val ((repChars.getD 36 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_36_36_4.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 36 []).getD ((alnPos.getD 36 []).getD j 0) []))) := by decide

theorem alnAll_36_36_5 : ∀ j, j < (repChars.getD 36 []).length →
    (normIsRep.getD 36 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_36_36_5.D (m := 25))
        (List.map ZMod.val ((repChars.getD 36 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_36_36_5.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 36 []).getD ((alnPos.getD 36 []).getD j 0) []))) := by decide

theorem alnAll_36_36_10 : ∀ j, j < (repChars.getD 36 []).length →
    (normIsRep.getD 36 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_36_36_10.D (m := 25))
        (List.map ZMod.val ((repChars.getD 36 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_36_36_10.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 36 []).getD ((alnPos.getD 36 []).getD j 0) []))) := by decide

theorem alnAll_36_36_15 : ∀ j, j < (repChars.getD 36 []).length →
    (normIsRep.getD 36 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_36_36_15.D (m := 25))
        (List.map ZMod.val ((repChars.getD 36 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_36_36_15.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 36 []).getD ((alnPos.getD 36 []).getD j 0) []))) := by decide

theorem alnAll_36_36_20 : ∀ j, j < (repChars.getD 36 []).length →
    (normIsRep.getD 36 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_36_36_20.D (m := 25))
        (List.map ZMod.val ((repChars.getD 36 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_36_36_20.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 36 []).getD ((alnPos.getD 36 []).getD j 0) []))) := by decide

theorem alnAll_37_0_0 : ∀ j, j < (repChars.getD 37 []).length →
    (normIsRep.getD 37 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_37_0_0.D (m := 125))
        (List.map ZMod.val ((repChars.getD 37 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_37_0_0.D (m := 125))
        (List.map ZMod.val ((Q2.repChars2.getD 37 []).getD ((alnPos.getD 37 []).getD j 0) []))) := by decide

theorem alnAll_37_12_0 : ∀ j, j < (repChars.getD 37 []).length →
    (normIsRep.getD 37 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_37_12_0.D (m := 125))
        (List.map ZMod.val ((repChars.getD 37 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_37_12_0.D (m := 125))
        (List.map ZMod.val ((Q2.repChars2.getD 37 []).getD ((alnPos.getD 37 []).getD j 0) []))) := by decide

theorem alnAll_37_12_1 : ∀ j, j < (repChars.getD 37 []).length →
    (normIsRep.getD 37 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_37_12_1.D (m := 125))
        (List.map ZMod.val ((repChars.getD 37 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_37_12_1.D (m := 125))
        (List.map ZMod.val ((Q2.repChars2.getD 37 []).getD ((alnPos.getD 37 []).getD j 0) []))) := by decide

theorem alnAll_37_12_2 : ∀ j, j < (repChars.getD 37 []).length →
    (normIsRep.getD 37 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_37_12_2.D (m := 125))
        (List.map ZMod.val ((repChars.getD 37 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_37_12_2.D (m := 125))
        (List.map ZMod.val ((Q2.repChars2.getD 37 []).getD ((alnPos.getD 37 []).getD j 0) []))) := by decide

end LeanDring.P5Presentation
