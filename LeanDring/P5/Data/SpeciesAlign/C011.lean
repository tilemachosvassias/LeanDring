/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.Characters.Twin2.CharAlign
import LeanDring.P5.Data.ColRestCheap.C151
import LeanDring.P5.Data.ColRestCheap.C008
import LeanDring.P5.Data.ColRestHeavy.C034
import LeanDring.P5.Data.ColRestHeavy.C035

/-!
# Species-table cells, α-paired residual decides, chunk 10

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

theorem alnAll_51_51_2 : ∀ j, j < (repChars.getD 51 []).length →
    (normIsRep.getD 51 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_51_51_2.D (m := 25))
        (List.map ZMod.val ((repChars.getD 51 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_51_51_2.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 51 []).getD ((alnPos.getD 51 []).getD j 0) []))) := by decide

theorem alnAll_51_51_3 : ∀ j, j < (repChars.getD 51 []).length →
    (normIsRep.getD 51 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_51_51_3.D (m := 25))
        (List.map ZMod.val ((repChars.getD 51 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_51_51_3.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 51 []).getD ((alnPos.getD 51 []).getD j 0) []))) := by decide

theorem alnAll_51_51_4 : ∀ j, j < (repChars.getD 51 []).length →
    (normIsRep.getD 51 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_51_51_4.D (m := 25))
        (List.map ZMod.val ((repChars.getD 51 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_51_51_4.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 51 []).getD ((alnPos.getD 51 []).getD j 0) []))) := by decide

theorem alnAll_51_51_5 : ∀ j, j < (repChars.getD 51 []).length →
    (normIsRep.getD 51 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_51_51_5.D (m := 25))
        (List.map ZMod.val ((repChars.getD 51 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_51_51_5.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 51 []).getD ((alnPos.getD 51 []).getD j 0) []))) := by decide

theorem alnAll_51_51_10 : ∀ j, j < (repChars.getD 51 []).length →
    (normIsRep.getD 51 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_51_51_10.D (m := 25))
        (List.map ZMod.val ((repChars.getD 51 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_51_51_10.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 51 []).getD ((alnPos.getD 51 []).getD j 0) []))) := by decide

theorem alnAll_51_51_15 : ∀ j, j < (repChars.getD 51 []).length →
    (normIsRep.getD 51 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_51_51_15.D (m := 25))
        (List.map ZMod.val ((repChars.getD 51 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_51_51_15.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 51 []).getD ((alnPos.getD 51 []).getD j 0) []))) := by decide

theorem alnAll_51_51_20 : ∀ j, j < (repChars.getD 51 []).length →
    (normIsRep.getD 51 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_51_51_20.D (m := 25))
        (List.map ZMod.val ((repChars.getD 51 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_51_51_20.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 51 []).getD ((alnPos.getD 51 []).getD j 0) []))) := by decide

theorem alnAll_52_0_0 : ∀ j, j < (repChars.getD 52 []).length →
    (normIsRep.getD 52 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_52_0_0.D (m := 125))
        (List.map ZMod.val ((repChars.getD 52 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_52_0_0.D (m := 125))
        (List.map ZMod.val ((Q2.repChars2.getD 52 []).getD ((alnPos.getD 52 []).getD j 0) []))) := by decide

theorem alnAll_52_12_0 : ∀ j, j < (repChars.getD 52 []).length →
    (normIsRep.getD 52 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_52_12_0.D (m := 125))
        (List.map ZMod.val ((repChars.getD 52 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_52_12_0.D (m := 125))
        (List.map ZMod.val ((Q2.repChars2.getD 52 []).getD ((alnPos.getD 52 []).getD j 0) []))) := by decide

theorem alnAll_52_12_1 : ∀ j, j < (repChars.getD 52 []).length →
    (normIsRep.getD 52 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_52_12_1.D (m := 125))
        (List.map ZMod.val ((repChars.getD 52 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_52_12_1.D (m := 125))
        (List.map ZMod.val ((Q2.repChars2.getD 52 []).getD ((alnPos.getD 52 []).getD j 0) []))) := by decide

theorem alnAll_52_12_2 : ∀ j, j < (repChars.getD 52 []).length →
    (normIsRep.getD 52 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_52_12_2.D (m := 125))
        (List.map ZMod.val ((repChars.getD 52 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_52_12_2.D (m := 125))
        (List.map ZMod.val ((Q2.repChars2.getD 52 []).getD ((alnPos.getD 52 []).getD j 0) []))) := by decide

theorem alnAll_52_12_3 : ∀ j, j < (repChars.getD 52 []).length →
    (normIsRep.getD 52 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_52_12_3.D (m := 125))
        (List.map ZMod.val ((repChars.getD 52 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_52_12_3.D (m := 125))
        (List.map ZMod.val ((Q2.repChars2.getD 52 []).getD ((alnPos.getD 52 []).getD j 0) []))) := by decide

theorem alnAll_52_12_4 : ∀ j, j < (repChars.getD 52 []).length →
    (normIsRep.getD 52 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_52_12_4.D (m := 125))
        (List.map ZMod.val ((repChars.getD 52 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_52_12_4.D (m := 125))
        (List.map ZMod.val ((Q2.repChars2.getD 52 []).getD ((alnPos.getD 52 []).getD j 0) []))) := by decide

theorem alnAll_52_52_0 : ∀ j, j < (repChars.getD 52 []).length →
    (normIsRep.getD 52 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_52_52_0.D (m := 25))
        (List.map ZMod.val ((repChars.getD 52 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_52_52_0.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 52 []).getD ((alnPos.getD 52 []).getD j 0) []))) := by decide

theorem alnAll_52_52_1 : ∀ j, j < (repChars.getD 52 []).length →
    (normIsRep.getD 52 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_52_52_1.D (m := 25))
        (List.map ZMod.val ((repChars.getD 52 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_52_52_1.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 52 []).getD ((alnPos.getD 52 []).getD j 0) []))) := by decide

theorem alnAll_52_52_2 : ∀ j, j < (repChars.getD 52 []).length →
    (normIsRep.getD 52 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_52_52_2.D (m := 25))
        (List.map ZMod.val ((repChars.getD 52 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_52_52_2.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 52 []).getD ((alnPos.getD 52 []).getD j 0) []))) := by decide

theorem alnAll_52_52_3 : ∀ j, j < (repChars.getD 52 []).length →
    (normIsRep.getD 52 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_52_52_3.D (m := 25))
        (List.map ZMod.val ((repChars.getD 52 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_52_52_3.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 52 []).getD ((alnPos.getD 52 []).getD j 0) []))) := by decide

theorem alnAll_52_52_4 : ∀ j, j < (repChars.getD 52 []).length →
    (normIsRep.getD 52 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_52_52_4.D (m := 25))
        (List.map ZMod.val ((repChars.getD 52 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_52_52_4.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 52 []).getD ((alnPos.getD 52 []).getD j 0) []))) := by decide

theorem alnAll_52_52_5 : ∀ j, j < (repChars.getD 52 []).length →
    (normIsRep.getD 52 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_52_52_5.D (m := 25))
        (List.map ZMod.val ((repChars.getD 52 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_52_52_5.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 52 []).getD ((alnPos.getD 52 []).getD j 0) []))) := by decide

theorem alnAll_52_52_10 : ∀ j, j < (repChars.getD 52 []).length →
    (normIsRep.getD 52 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_52_52_10.D (m := 25))
        (List.map ZMod.val ((repChars.getD 52 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_52_52_10.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 52 []).getD ((alnPos.getD 52 []).getD j 0) []))) := by decide

theorem alnAll_52_52_15 : ∀ j, j < (repChars.getD 52 []).length →
    (normIsRep.getD 52 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_52_52_15.D (m := 25))
        (List.map ZMod.val ((repChars.getD 52 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_52_52_15.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 52 []).getD ((alnPos.getD 52 []).getD j 0) []))) := by decide

theorem alnAll_52_52_20 : ∀ j, j < (repChars.getD 52 []).length →
    (normIsRep.getD 52 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_52_52_20.D (m := 25))
        (List.map ZMod.val ((repChars.getD 52 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_52_52_20.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 52 []).getD ((alnPos.getD 52 []).getD j 0) []))) := by decide

theorem alnAll_64_0_0 : ∀ j, j < (repChars.getD 64 []).length →
    (normIsRep.getD 64 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_0_0.D (m := 25))
        (List.map ZMod.val ((repChars.getD 64 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_0_0.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 64 []).getD ((alnPos.getD 64 []).getD j 0) []))) := by decide

theorem alnAll_64_8_0 : ∀ j, j < (repChars.getD 64 []).length →
    (normIsRep.getD 64 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_8_0.D (m := 25))
        (List.map ZMod.val ((repChars.getD 64 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_8_0.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 64 []).getD ((alnPos.getD 64 []).getD j 0) []))) := by decide

theorem alnAll_64_8_1 : ∀ j, j < (repChars.getD 64 []).length →
    (normIsRep.getD 64 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_8_1.D (m := 25))
        (List.map ZMod.val ((repChars.getD 64 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_8_1.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 64 []).getD ((alnPos.getD 64 []).getD j 0) []))) := by decide

theorem alnAll_64_8_2 : ∀ j, j < (repChars.getD 64 []).length →
    (normIsRep.getD 64 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_8_2.D (m := 25))
        (List.map ZMod.val ((repChars.getD 64 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_8_2.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 64 []).getD ((alnPos.getD 64 []).getD j 0) []))) := by decide

theorem alnAll_64_8_3 : ∀ j, j < (repChars.getD 64 []).length →
    (normIsRep.getD 64 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_8_3.D (m := 25))
        (List.map ZMod.val ((repChars.getD 64 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_8_3.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 64 []).getD ((alnPos.getD 64 []).getD j 0) []))) := by decide

theorem alnAll_64_8_4 : ∀ j, j < (repChars.getD 64 []).length →
    (normIsRep.getD 64 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_8_4.D (m := 25))
        (List.map ZMod.val ((repChars.getD 64 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_8_4.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 64 []).getD ((alnPos.getD 64 []).getD j 0) []))) := by decide

theorem alnAll_64_12_0 : ∀ j, j < (repChars.getD 64 []).length →
    (normIsRep.getD 64 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_12_0.D (m := 25))
        (List.map ZMod.val ((repChars.getD 64 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_12_0.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 64 []).getD ((alnPos.getD 64 []).getD j 0) []))) := by decide

theorem alnAll_64_12_1 : ∀ j, j < (repChars.getD 64 []).length →
    (normIsRep.getD 64 []).getD j false = true →
    LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_12_1.D (m := 25))
        (List.map ZMod.val ((repChars.getD 64 []).getD j [])))
      = LeanDring.P5CyclotomicCode.sumPowers (fastCode (colFn colCert_64_12_1.D (m := 25))
        (List.map ZMod.val ((Q2.repChars2.getD 64 []).getD ((alnPos.getD 64 []).getD j 0) []))) := by decide

end LeanDring.P5Presentation
