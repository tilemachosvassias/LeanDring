/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.EntrySupport
import LeanDring.P5.Certificate.Characters.Twin1.CharAssembly
import LeanDring.P5.Certificate.Characters.Twin2.CharAssembly
import LeanDring.P5.Data.ColCdd.C022
import LeanDring.P5.Data.ColCdd.C023

/-!
# Species-table cells, stages 3-4 — residual real-decide certificates (divergent columns).
Auto-emitted by python/p5_stage34_emit.py. Chunk 36: 82 columns.
Each theorem: for every character vector of the row class, the two twins'
fast codes have equal cyclotomic value (identity row matching). Fed to
`species_eq_of_fastcode_eq` at stage-5 assembly.
-/

-- machine-emitted data: silence style linters (generated long lines, file-level options)
set_option linter.style.longLine false

namespace LeanDring.P5Presentation

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

theorem colCertDiv_146_49_20_match :
    ((Q2.charsAt2 ⟨146, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_146_49_20.D2 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_146_49_20.D1 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_146_50_5_match :
    ((Q2.charsAt2 ⟨146, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_146_50_5.D2 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_146_50_5.D1 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_146_50_10_match :
    ((Q2.charsAt2 ⟨146, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_146_50_10.D2 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_146_50_10.D1 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_146_50_15_match :
    ((Q2.charsAt2 ⟨146, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_146_50_15.D2 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_146_50_15.D1 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_146_50_20_match :
    ((Q2.charsAt2 ⟨146, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_146_50_20.D2 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_146_50_20.D1 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_146_51_5_match :
    ((Q2.charsAt2 ⟨146, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_146_51_5.D2 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_146_51_5.D1 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_146_51_10_match :
    ((Q2.charsAt2 ⟨146, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_146_51_10.D2 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_146_51_10.D1 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_146_51_15_match :
    ((Q2.charsAt2 ⟨146, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_146_51_15.D2 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_146_51_15.D1 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_146_51_20_match :
    ((Q2.charsAt2 ⟨146, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_146_51_20.D2 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_146_51_20.D1 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_146_52_5_match :
    ((Q2.charsAt2 ⟨146, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_146_52_5.D2 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_146_52_5.D1 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_146_52_10_match :
    ((Q2.charsAt2 ⟨146, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_146_52_10.D2 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_146_52_10.D1 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_146_52_15_match :
    ((Q2.charsAt2 ⟨146, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_146_52_15.D2 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_146_52_15.D1 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_146_52_20_match :
    ((Q2.charsAt2 ⟨146, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_146_52_20.D2 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_146_52_20.D1 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_146_111_10_match :
    ((Q2.charsAt2 ⟨146, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_146_111_10.D2 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_146_111_10.D1 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_146_111_15_match :
    ((Q2.charsAt2 ⟨146, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_146_111_15.D2 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_146_111_15.D1 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_146_111_20_match :
    ((Q2.charsAt2 ⟨146, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_146_111_20.D2 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_146_111_20.D1 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_146_112_15_match :
    ((Q2.charsAt2 ⟨146, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_146_112_15.D2 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_146_112_15.D1 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_146_112_20_match :
    ((Q2.charsAt2 ⟨146, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_146_112_20.D2 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_146_112_20.D1 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_146_113_10_match :
    ((Q2.charsAt2 ⟨146, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_146_113_10.D2 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_146_113_10.D1 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_146_113_15_match :
    ((Q2.charsAt2 ⟨146, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_146_113_15.D2 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_146_113_15.D1 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_146_113_20_match :
    ((Q2.charsAt2 ⟨146, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_146_113_20.D2 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_146_113_20.D1 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_28_5_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_28_5.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_28_5.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_28_10_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_28_10.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_28_10.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_28_15_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_28_15.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_28_15.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_28_20_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_28_20.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_28_20.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_29_10_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_29_10.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_29_10.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_29_15_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_29_15.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_29_15.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_29_20_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_29_20.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_29_20.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_30_5_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_30_5.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_30_5.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_30_10_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_30_10.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_30_10.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_30_15_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_30_15.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_30_15.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_30_20_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_30_20.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_30_20.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_31_5_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_31_5.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_31_5.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_31_10_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_31_10.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_31_10.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_31_15_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_31_15.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_31_15.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_31_20_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_31_20.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_31_20.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_32_5_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_32_5.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_32_5.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_32_10_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_32_10.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_32_10.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_32_15_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_32_15.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_32_15.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_32_20_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_32_20.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_32_20.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_33_5_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_33_5.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_33_5.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_33_10_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_33_10.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_33_10.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_33_15_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_33_15.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_33_15.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_33_20_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_33_20.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_33_20.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_34_10_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_34_10.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_34_10.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_34_15_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_34_15.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_34_15.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_34_20_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_34_20.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_34_20.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_35_5_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_35_5.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_35_5.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_35_10_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_35_10.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_35_10.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_35_15_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_35_15.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_35_15.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_35_20_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_35_20.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_35_20.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_36_5_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_36_5.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_36_5.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_36_10_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_36_10.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_36_10.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_36_15_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_36_15.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_36_15.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_36_20_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_36_20.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_36_20.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_37_5_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_37_5.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_37_5.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_37_10_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_37_10.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_37_10.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_37_15_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_37_15.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_37_15.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_37_20_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_37_20.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_37_20.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_38_5_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_38_5.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_38_5.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_38_10_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_38_10.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_38_10.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_38_15_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_38_15.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_38_15.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_38_20_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_38_20.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_38_20.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_39_10_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_39_10.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_39_10.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_39_15_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_39_15.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_39_15.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_39_20_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_39_20.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_39_20.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_40_5_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_40_5.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_40_5.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_40_10_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_40_10.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_40_10.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_40_15_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_40_15.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_40_15.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_40_20_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_40_20.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_40_20.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_41_5_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_41_5.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_41_5.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_41_10_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_41_10.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_41_10.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_41_15_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_41_15.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_41_15.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_41_20_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_41_20.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_41_20.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_42_5_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_42_5.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_42_5.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_42_10_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_42_10.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_42_10.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_42_15_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_42_15.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_42_15.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_42_20_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_42_20.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_42_20.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_43_5_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_43_5.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_43_5.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_43_10_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_43_10.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_43_10.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_43_15_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_43_15.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_43_15.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_43_20_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_43_20.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_43_20.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

end LeanDring.P5Presentation
