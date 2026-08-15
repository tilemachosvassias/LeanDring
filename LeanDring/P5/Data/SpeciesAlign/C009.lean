/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.Characters.Twin2.CharAlign
import LeanDring.P5.Data.ColRestCheap.C007
import LeanDring.P5.Data.ColRestCheap.C008
import LeanDring.P5.Data.ColRestHeavy.C031
import LeanDring.P5.Data.ColRestHeavy.C032

/-!
# Species-table cells, α-paired residual decides, chunk 8

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

theorem alnAll_47_0_0 : ∀ j, j < (repChars.getD 47 []).length →
    (normIsRep.getD 47 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_47_0_0.D (m := 125))
        (List.map ZMod.val ((repChars.getD 47 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_47_0_0.D (m := 125))
        (List.map ZMod.val ((Q2.repChars2.getD 47 []).getD ((alnPos.getD 47 []).getD j 0) []))) := by decide

theorem alnAll_47_12_0 : ∀ j, j < (repChars.getD 47 []).length →
    (normIsRep.getD 47 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_47_12_0.D (m := 125))
        (List.map ZMod.val ((repChars.getD 47 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_47_12_0.D (m := 125))
        (List.map ZMod.val ((Q2.repChars2.getD 47 []).getD ((alnPos.getD 47 []).getD j 0) []))) := by decide

theorem alnAll_47_12_1 : ∀ j, j < (repChars.getD 47 []).length →
    (normIsRep.getD 47 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_47_12_1.D (m := 125))
        (List.map ZMod.val ((repChars.getD 47 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_47_12_1.D (m := 125))
        (List.map ZMod.val ((Q2.repChars2.getD 47 []).getD ((alnPos.getD 47 []).getD j 0) []))) := by decide

theorem alnAll_47_12_2 : ∀ j, j < (repChars.getD 47 []).length →
    (normIsRep.getD 47 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_47_12_2.D (m := 125))
        (List.map ZMod.val ((repChars.getD 47 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_47_12_2.D (m := 125))
        (List.map ZMod.val ((Q2.repChars2.getD 47 []).getD ((alnPos.getD 47 []).getD j 0) []))) := by decide

theorem alnAll_47_12_3 : ∀ j, j < (repChars.getD 47 []).length →
    (normIsRep.getD 47 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_47_12_3.D (m := 125))
        (List.map ZMod.val ((repChars.getD 47 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_47_12_3.D (m := 125))
        (List.map ZMod.val ((Q2.repChars2.getD 47 []).getD ((alnPos.getD 47 []).getD j 0) []))) := by decide

theorem alnAll_47_12_4 : ∀ j, j < (repChars.getD 47 []).length →
    (normIsRep.getD 47 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_47_12_4.D (m := 125))
        (List.map ZMod.val ((repChars.getD 47 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_47_12_4.D (m := 125))
        (List.map ZMod.val ((Q2.repChars2.getD 47 []).getD ((alnPos.getD 47 []).getD j 0) []))) := by decide

theorem alnAll_47_47_0 : ∀ j, j < (repChars.getD 47 []).length →
    (normIsRep.getD 47 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_47_47_0.D (m := 25))
        (List.map ZMod.val ((repChars.getD 47 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_47_47_0.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 47 []).getD ((alnPos.getD 47 []).getD j 0) []))) := by decide

theorem alnAll_47_47_1 : ∀ j, j < (repChars.getD 47 []).length →
    (normIsRep.getD 47 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_47_47_1.D (m := 25))
        (List.map ZMod.val ((repChars.getD 47 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_47_47_1.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 47 []).getD ((alnPos.getD 47 []).getD j 0) []))) := by decide

theorem alnAll_47_47_2 : ∀ j, j < (repChars.getD 47 []).length →
    (normIsRep.getD 47 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_47_47_2.D (m := 25))
        (List.map ZMod.val ((repChars.getD 47 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_47_47_2.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 47 []).getD ((alnPos.getD 47 []).getD j 0) []))) := by decide

theorem alnAll_47_47_3 : ∀ j, j < (repChars.getD 47 []).length →
    (normIsRep.getD 47 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_47_47_3.D (m := 25))
        (List.map ZMod.val ((repChars.getD 47 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_47_47_3.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 47 []).getD ((alnPos.getD 47 []).getD j 0) []))) := by decide

theorem alnAll_47_47_4 : ∀ j, j < (repChars.getD 47 []).length →
    (normIsRep.getD 47 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_47_47_4.D (m := 25))
        (List.map ZMod.val ((repChars.getD 47 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_47_47_4.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 47 []).getD ((alnPos.getD 47 []).getD j 0) []))) := by decide

theorem alnAll_47_47_5 : ∀ j, j < (repChars.getD 47 []).length →
    (normIsRep.getD 47 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_47_47_5.D (m := 25))
        (List.map ZMod.val ((repChars.getD 47 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_47_47_5.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 47 []).getD ((alnPos.getD 47 []).getD j 0) []))) := by decide

theorem alnAll_47_47_10 : ∀ j, j < (repChars.getD 47 []).length →
    (normIsRep.getD 47 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_47_47_10.D (m := 25))
        (List.map ZMod.val ((repChars.getD 47 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_47_47_10.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 47 []).getD ((alnPos.getD 47 []).getD j 0) []))) := by decide

theorem alnAll_47_47_15 : ∀ j, j < (repChars.getD 47 []).length →
    (normIsRep.getD 47 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_47_47_15.D (m := 25))
        (List.map ZMod.val ((repChars.getD 47 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_47_47_15.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 47 []).getD ((alnPos.getD 47 []).getD j 0) []))) := by decide

theorem alnAll_47_47_20 : ∀ j, j < (repChars.getD 47 []).length →
    (normIsRep.getD 47 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_47_47_20.D (m := 25))
        (List.map ZMod.val ((repChars.getD 47 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_47_47_20.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 47 []).getD ((alnPos.getD 47 []).getD j 0) []))) := by decide

theorem alnAll_48_0_0 : ∀ j, j < (repChars.getD 48 []).length →
    (normIsRep.getD 48 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_48_0_0.D (m := 125))
        (List.map ZMod.val ((repChars.getD 48 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_48_0_0.D (m := 125))
        (List.map ZMod.val ((Q2.repChars2.getD 48 []).getD ((alnPos.getD 48 []).getD j 0) []))) := by decide

theorem alnAll_48_12_0 : ∀ j, j < (repChars.getD 48 []).length →
    (normIsRep.getD 48 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_48_12_0.D (m := 125))
        (List.map ZMod.val ((repChars.getD 48 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_48_12_0.D (m := 125))
        (List.map ZMod.val ((Q2.repChars2.getD 48 []).getD ((alnPos.getD 48 []).getD j 0) []))) := by decide

theorem alnAll_48_12_1 : ∀ j, j < (repChars.getD 48 []).length →
    (normIsRep.getD 48 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_48_12_1.D (m := 125))
        (List.map ZMod.val ((repChars.getD 48 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_48_12_1.D (m := 125))
        (List.map ZMod.val ((Q2.repChars2.getD 48 []).getD ((alnPos.getD 48 []).getD j 0) []))) := by decide

theorem alnAll_48_12_2 : ∀ j, j < (repChars.getD 48 []).length →
    (normIsRep.getD 48 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_48_12_2.D (m := 125))
        (List.map ZMod.val ((repChars.getD 48 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_48_12_2.D (m := 125))
        (List.map ZMod.val ((Q2.repChars2.getD 48 []).getD ((alnPos.getD 48 []).getD j 0) []))) := by decide

theorem alnAll_48_12_3 : ∀ j, j < (repChars.getD 48 []).length →
    (normIsRep.getD 48 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_48_12_3.D (m := 125))
        (List.map ZMod.val ((repChars.getD 48 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_48_12_3.D (m := 125))
        (List.map ZMod.val ((Q2.repChars2.getD 48 []).getD ((alnPos.getD 48 []).getD j 0) []))) := by decide

theorem alnAll_48_12_4 : ∀ j, j < (repChars.getD 48 []).length →
    (normIsRep.getD 48 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_48_12_4.D (m := 125))
        (List.map ZMod.val ((repChars.getD 48 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_48_12_4.D (m := 125))
        (List.map ZMod.val ((Q2.repChars2.getD 48 []).getD ((alnPos.getD 48 []).getD j 0) []))) := by decide

theorem alnAll_48_48_0 : ∀ j, j < (repChars.getD 48 []).length →
    (normIsRep.getD 48 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_48_48_0.D (m := 25))
        (List.map ZMod.val ((repChars.getD 48 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_48_48_0.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 48 []).getD ((alnPos.getD 48 []).getD j 0) []))) := by decide

theorem alnAll_48_48_1 : ∀ j, j < (repChars.getD 48 []).length →
    (normIsRep.getD 48 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_48_48_1.D (m := 25))
        (List.map ZMod.val ((repChars.getD 48 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_48_48_1.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 48 []).getD ((alnPos.getD 48 []).getD j 0) []))) := by decide

theorem alnAll_48_48_2 : ∀ j, j < (repChars.getD 48 []).length →
    (normIsRep.getD 48 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_48_48_2.D (m := 25))
        (List.map ZMod.val ((repChars.getD 48 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_48_48_2.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 48 []).getD ((alnPos.getD 48 []).getD j 0) []))) := by decide

theorem alnAll_48_48_3 : ∀ j, j < (repChars.getD 48 []).length →
    (normIsRep.getD 48 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_48_48_3.D (m := 25))
        (List.map ZMod.val ((repChars.getD 48 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_48_48_3.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 48 []).getD ((alnPos.getD 48 []).getD j 0) []))) := by decide

theorem alnAll_48_48_4 : ∀ j, j < (repChars.getD 48 []).length →
    (normIsRep.getD 48 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_48_48_4.D (m := 25))
        (List.map ZMod.val ((repChars.getD 48 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_48_48_4.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 48 []).getD ((alnPos.getD 48 []).getD j 0) []))) := by decide

theorem alnAll_48_48_5 : ∀ j, j < (repChars.getD 48 []).length →
    (normIsRep.getD 48 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_48_48_5.D (m := 25))
        (List.map ZMod.val ((repChars.getD 48 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_48_48_5.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 48 []).getD ((alnPos.getD 48 []).getD j 0) []))) := by decide

theorem alnAll_48_48_10 : ∀ j, j < (repChars.getD 48 []).length →
    (normIsRep.getD 48 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_48_48_10.D (m := 25))
        (List.map ZMod.val ((repChars.getD 48 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_48_48_10.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 48 []).getD ((alnPos.getD 48 []).getD j 0) []))) := by decide

theorem alnAll_48_48_15 : ∀ j, j < (repChars.getD 48 []).length →
    (normIsRep.getD 48 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_48_48_15.D (m := 25))
        (List.map ZMod.val ((repChars.getD 48 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_48_48_15.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 48 []).getD ((alnPos.getD 48 []).getD j 0) []))) := by decide

theorem alnAll_48_48_20 : ∀ j, j < (repChars.getD 48 []).length →
    (normIsRep.getD 48 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_48_48_20.D (m := 25))
        (List.map ZMod.val ((repChars.getD 48 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_48_48_20.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 48 []).getD ((alnPos.getD 48 []).getD j 0) []))) := by decide

theorem alnAll_49_0_0 : ∀ j, j < (repChars.getD 49 []).length →
    (normIsRep.getD 49 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_49_0_0.D (m := 125))
        (List.map ZMod.val ((repChars.getD 49 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_49_0_0.D (m := 125))
        (List.map ZMod.val ((Q2.repChars2.getD 49 []).getD ((alnPos.getD 49 []).getD j 0) []))) := by decide

theorem alnAll_49_12_0 : ∀ j, j < (repChars.getD 49 []).length →
    (normIsRep.getD 49 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_49_12_0.D (m := 125))
        (List.map ZMod.val ((repChars.getD 49 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_49_12_0.D (m := 125))
        (List.map ZMod.val ((Q2.repChars2.getD 49 []).getD ((alnPos.getD 49 []).getD j 0) []))) := by decide

theorem alnAll_49_12_1 : ∀ j, j < (repChars.getD 49 []).length →
    (normIsRep.getD 49 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_49_12_1.D (m := 125))
        (List.map ZMod.val ((repChars.getD 49 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_49_12_1.D (m := 125))
        (List.map ZMod.val ((Q2.repChars2.getD 49 []).getD ((alnPos.getD 49 []).getD j 0) []))) := by decide

end LeanDring.P5Presentation
