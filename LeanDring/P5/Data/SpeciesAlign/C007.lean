/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.Characters.Twin2.CharAlign
import LeanDring.P5.Data.ColRestCheap.C007
import LeanDring.P5.Data.ColRestHeavy.C027
import LeanDring.P5.Data.ColRestHeavy.C028
import LeanDring.P5.Data.ColRestHeavy.C029

/-!
# Species-table cells, α-paired residual decides, chunk 6

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

theorem alnAll_42_12_1 : ∀ j, j < (repChars.getD 42 []).length →
    (normIsRep.getD 42 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_42_12_1.D (m := 125))
        (List.map ZMod.val ((repChars.getD 42 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_42_12_1.D (m := 125))
        (List.map ZMod.val ((Q2.repChars2.getD 42 []).getD ((alnPos.getD 42 []).getD j 0) []))) := by decide

theorem alnAll_42_12_2 : ∀ j, j < (repChars.getD 42 []).length →
    (normIsRep.getD 42 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_42_12_2.D (m := 125))
        (List.map ZMod.val ((repChars.getD 42 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_42_12_2.D (m := 125))
        (List.map ZMod.val ((Q2.repChars2.getD 42 []).getD ((alnPos.getD 42 []).getD j 0) []))) := by decide

theorem alnAll_42_12_3 : ∀ j, j < (repChars.getD 42 []).length →
    (normIsRep.getD 42 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_42_12_3.D (m := 125))
        (List.map ZMod.val ((repChars.getD 42 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_42_12_3.D (m := 125))
        (List.map ZMod.val ((Q2.repChars2.getD 42 []).getD ((alnPos.getD 42 []).getD j 0) []))) := by decide

theorem alnAll_42_12_4 : ∀ j, j < (repChars.getD 42 []).length →
    (normIsRep.getD 42 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_42_12_4.D (m := 125))
        (List.map ZMod.val ((repChars.getD 42 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_42_12_4.D (m := 125))
        (List.map ZMod.val ((Q2.repChars2.getD 42 []).getD ((alnPos.getD 42 []).getD j 0) []))) := by decide

theorem alnAll_42_42_0 : ∀ j, j < (repChars.getD 42 []).length →
    (normIsRep.getD 42 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_42_42_0.D (m := 25))
        (List.map ZMod.val ((repChars.getD 42 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_42_42_0.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 42 []).getD ((alnPos.getD 42 []).getD j 0) []))) := by decide

theorem alnAll_42_42_1 : ∀ j, j < (repChars.getD 42 []).length →
    (normIsRep.getD 42 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_42_42_1.D (m := 25))
        (List.map ZMod.val ((repChars.getD 42 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_42_42_1.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 42 []).getD ((alnPos.getD 42 []).getD j 0) []))) := by decide

theorem alnAll_42_42_2 : ∀ j, j < (repChars.getD 42 []).length →
    (normIsRep.getD 42 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_42_42_2.D (m := 25))
        (List.map ZMod.val ((repChars.getD 42 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_42_42_2.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 42 []).getD ((alnPos.getD 42 []).getD j 0) []))) := by decide

theorem alnAll_42_42_3 : ∀ j, j < (repChars.getD 42 []).length →
    (normIsRep.getD 42 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_42_42_3.D (m := 25))
        (List.map ZMod.val ((repChars.getD 42 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_42_42_3.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 42 []).getD ((alnPos.getD 42 []).getD j 0) []))) := by decide

theorem alnAll_42_42_4 : ∀ j, j < (repChars.getD 42 []).length →
    (normIsRep.getD 42 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_42_42_4.D (m := 25))
        (List.map ZMod.val ((repChars.getD 42 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_42_42_4.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 42 []).getD ((alnPos.getD 42 []).getD j 0) []))) := by decide

theorem alnAll_42_42_5 : ∀ j, j < (repChars.getD 42 []).length →
    (normIsRep.getD 42 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_42_42_5.D (m := 25))
        (List.map ZMod.val ((repChars.getD 42 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_42_42_5.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 42 []).getD ((alnPos.getD 42 []).getD j 0) []))) := by decide

theorem alnAll_42_42_10 : ∀ j, j < (repChars.getD 42 []).length →
    (normIsRep.getD 42 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_42_42_10.D (m := 25))
        (List.map ZMod.val ((repChars.getD 42 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_42_42_10.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 42 []).getD ((alnPos.getD 42 []).getD j 0) []))) := by decide

theorem alnAll_42_42_15 : ∀ j, j < (repChars.getD 42 []).length →
    (normIsRep.getD 42 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_42_42_15.D (m := 25))
        (List.map ZMod.val ((repChars.getD 42 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_42_42_15.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 42 []).getD ((alnPos.getD 42 []).getD j 0) []))) := by decide

theorem alnAll_42_42_20 : ∀ j, j < (repChars.getD 42 []).length →
    (normIsRep.getD 42 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_42_42_20.D (m := 25))
        (List.map ZMod.val ((repChars.getD 42 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_42_42_20.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 42 []).getD ((alnPos.getD 42 []).getD j 0) []))) := by decide

theorem alnAll_43_0_0 : ∀ j, j < (repChars.getD 43 []).length →
    (normIsRep.getD 43 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_43_0_0.D (m := 125))
        (List.map ZMod.val ((repChars.getD 43 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_43_0_0.D (m := 125))
        (List.map ZMod.val ((Q2.repChars2.getD 43 []).getD ((alnPos.getD 43 []).getD j 0) []))) := by decide

theorem alnAll_43_12_0 : ∀ j, j < (repChars.getD 43 []).length →
    (normIsRep.getD 43 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_43_12_0.D (m := 125))
        (List.map ZMod.val ((repChars.getD 43 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_43_12_0.D (m := 125))
        (List.map ZMod.val ((Q2.repChars2.getD 43 []).getD ((alnPos.getD 43 []).getD j 0) []))) := by decide

theorem alnAll_43_12_1 : ∀ j, j < (repChars.getD 43 []).length →
    (normIsRep.getD 43 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_43_12_1.D (m := 125))
        (List.map ZMod.val ((repChars.getD 43 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_43_12_1.D (m := 125))
        (List.map ZMod.val ((Q2.repChars2.getD 43 []).getD ((alnPos.getD 43 []).getD j 0) []))) := by decide

theorem alnAll_43_12_2 : ∀ j, j < (repChars.getD 43 []).length →
    (normIsRep.getD 43 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_43_12_2.D (m := 125))
        (List.map ZMod.val ((repChars.getD 43 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_43_12_2.D (m := 125))
        (List.map ZMod.val ((Q2.repChars2.getD 43 []).getD ((alnPos.getD 43 []).getD j 0) []))) := by decide

theorem alnAll_43_12_3 : ∀ j, j < (repChars.getD 43 []).length →
    (normIsRep.getD 43 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_43_12_3.D (m := 125))
        (List.map ZMod.val ((repChars.getD 43 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_43_12_3.D (m := 125))
        (List.map ZMod.val ((Q2.repChars2.getD 43 []).getD ((alnPos.getD 43 []).getD j 0) []))) := by decide

theorem alnAll_43_12_4 : ∀ j, j < (repChars.getD 43 []).length →
    (normIsRep.getD 43 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_43_12_4.D (m := 125))
        (List.map ZMod.val ((repChars.getD 43 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_43_12_4.D (m := 125))
        (List.map ZMod.val ((Q2.repChars2.getD 43 []).getD ((alnPos.getD 43 []).getD j 0) []))) := by decide

theorem alnAll_43_43_0 : ∀ j, j < (repChars.getD 43 []).length →
    (normIsRep.getD 43 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_43_43_0.D (m := 25))
        (List.map ZMod.val ((repChars.getD 43 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_43_43_0.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 43 []).getD ((alnPos.getD 43 []).getD j 0) []))) := by decide

theorem alnAll_43_43_1 : ∀ j, j < (repChars.getD 43 []).length →
    (normIsRep.getD 43 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_43_43_1.D (m := 25))
        (List.map ZMod.val ((repChars.getD 43 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_43_43_1.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 43 []).getD ((alnPos.getD 43 []).getD j 0) []))) := by decide

theorem alnAll_43_43_2 : ∀ j, j < (repChars.getD 43 []).length →
    (normIsRep.getD 43 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_43_43_2.D (m := 25))
        (List.map ZMod.val ((repChars.getD 43 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_43_43_2.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 43 []).getD ((alnPos.getD 43 []).getD j 0) []))) := by decide

theorem alnAll_43_43_3 : ∀ j, j < (repChars.getD 43 []).length →
    (normIsRep.getD 43 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_43_43_3.D (m := 25))
        (List.map ZMod.val ((repChars.getD 43 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_43_43_3.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 43 []).getD ((alnPos.getD 43 []).getD j 0) []))) := by decide

theorem alnAll_43_43_4 : ∀ j, j < (repChars.getD 43 []).length →
    (normIsRep.getD 43 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_43_43_4.D (m := 25))
        (List.map ZMod.val ((repChars.getD 43 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_43_43_4.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 43 []).getD ((alnPos.getD 43 []).getD j 0) []))) := by decide

theorem alnAll_43_43_5 : ∀ j, j < (repChars.getD 43 []).length →
    (normIsRep.getD 43 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_43_43_5.D (m := 25))
        (List.map ZMod.val ((repChars.getD 43 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_43_43_5.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 43 []).getD ((alnPos.getD 43 []).getD j 0) []))) := by decide

theorem alnAll_43_43_10 : ∀ j, j < (repChars.getD 43 []).length →
    (normIsRep.getD 43 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_43_43_10.D (m := 25))
        (List.map ZMod.val ((repChars.getD 43 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_43_43_10.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 43 []).getD ((alnPos.getD 43 []).getD j 0) []))) := by decide

theorem alnAll_43_43_15 : ∀ j, j < (repChars.getD 43 []).length →
    (normIsRep.getD 43 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_43_43_15.D (m := 25))
        (List.map ZMod.val ((repChars.getD 43 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_43_43_15.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 43 []).getD ((alnPos.getD 43 []).getD j 0) []))) := by decide

theorem alnAll_43_43_20 : ∀ j, j < (repChars.getD 43 []).length →
    (normIsRep.getD 43 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_43_43_20.D (m := 25))
        (List.map ZMod.val ((repChars.getD 43 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_43_43_20.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 43 []).getD ((alnPos.getD 43 []).getD j 0) []))) := by decide

theorem alnAll_44_0_0 : ∀ j, j < (repChars.getD 44 []).length →
    (normIsRep.getD 44 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_44_0_0.D (m := 125))
        (List.map ZMod.val ((repChars.getD 44 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_44_0_0.D (m := 125))
        (List.map ZMod.val ((Q2.repChars2.getD 44 []).getD ((alnPos.getD 44 []).getD j 0) []))) := by decide

theorem alnAll_44_12_0 : ∀ j, j < (repChars.getD 44 []).length →
    (normIsRep.getD 44 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_44_12_0.D (m := 125))
        (List.map ZMod.val ((repChars.getD 44 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_44_12_0.D (m := 125))
        (List.map ZMod.val ((Q2.repChars2.getD 44 []).getD ((alnPos.getD 44 []).getD j 0) []))) := by decide

theorem alnAll_44_12_1 : ∀ j, j < (repChars.getD 44 []).length →
    (normIsRep.getD 44 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_44_12_1.D (m := 125))
        (List.map ZMod.val ((repChars.getD 44 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_44_12_1.D (m := 125))
        (List.map ZMod.val ((Q2.repChars2.getD 44 []).getD ((alnPos.getD 44 []).getD j 0) []))) := by decide

theorem alnAll_44_12_2 : ∀ j, j < (repChars.getD 44 []).length →
    (normIsRep.getD 44 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_44_12_2.D (m := 125))
        (List.map ZMod.val ((repChars.getD 44 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_44_12_2.D (m := 125))
        (List.map ZMod.val ((Q2.repChars2.getD 44 []).getD ((alnPos.getD 44 []).getD j 0) []))) := by decide

theorem alnAll_44_12_3 : ∀ j, j < (repChars.getD 44 []).length →
    (normIsRep.getD 44 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_44_12_3.D (m := 125))
        (List.map ZMod.val ((repChars.getD 44 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_44_12_3.D (m := 125))
        (List.map ZMod.val ((Q2.repChars2.getD 44 []).getD ((alnPos.getD 44 []).getD j 0) []))) := by decide

end LeanDring.P5Presentation
