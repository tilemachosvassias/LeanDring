/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.EntrySupport
import LeanDring.P5.Certificate.Characters.Twin1.CharAssembly
import LeanDring.P5.Certificate.Characters.Twin2.CharAssembly
import LeanDring.P5.Data.ColCdd.C027
import LeanDring.P5.Data.ColCdd.C028
import LeanDring.P5.Data.ColCdd.C029
import LeanDring.P5.Data.ColCdd.C030
import LeanDring.P5.Data.ColCdd.C004

/-!
# Species-table cells, stages 3-4 — residual real-decide certificates (divergent columns).
Auto-emitted by python/p5_stage34_emit.py. Chunk 38: 187 columns.
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

theorem colCertDiv_147_68_6_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_68_6.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_68_6.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_68_7_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_68_7.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_68_7.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_68_8_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_68_8.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_68_8.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_68_9_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_68_9.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_68_9.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_68_10_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_68_10.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_68_10.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_68_11_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_68_11.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_68_11.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_68_12_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_68_12.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_68_12.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_68_13_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_68_13.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_68_13.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_68_14_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_68_14.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_68_14.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_68_15_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_68_15.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_68_15.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_68_16_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_68_16.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_68_16.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_68_17_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_68_17.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_68_17.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_68_18_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_68_18.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_68_18.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_68_23_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_68_23.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_68_23.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_68_24_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_68_24.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_68_24.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_69_15_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_69_15.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_69_15.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_69_16_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_69_16.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_69_16.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_69_17_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_69_17.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_69_17.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_69_18_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_69_18.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_69_18.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_69_19_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_69_19.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_69_19.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_69_20_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_69_20.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_69_20.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_69_21_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_69_21.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_69_21.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_69_22_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_69_22.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_69_22.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_69_23_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_69_23.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_69_23.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_69_24_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_69_24.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_69_24.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_70_5_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_70_5.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_70_5.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_70_6_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_70_6.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_70_6.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_70_7_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_70_7.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_70_7.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_70_8_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_70_8.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_70_8.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_70_9_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_70_9.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_70_9.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_70_10_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_70_10.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_70_10.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_70_11_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_70_11.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_70_11.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_70_12_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_70_12.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_70_12.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_70_13_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_70_13.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_70_13.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_70_14_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_70_14.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_70_14.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_70_15_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_70_15.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_70_15.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_70_16_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_70_16.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_70_16.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_70_17_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_70_17.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_70_17.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_70_18_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_70_18.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_70_18.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_70_19_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_70_19.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_70_19.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_70_20_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_70_20.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_70_20.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_70_21_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_70_21.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_70_21.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_70_22_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_70_22.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_70_22.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_70_23_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_70_23.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_70_23.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_70_24_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_70_24.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_70_24.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_71_5_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_71_5.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_71_5.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_71_6_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_71_6.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_71_6.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_71_7_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_71_7.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_71_7.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_71_8_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_71_8.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_71_8.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_71_9_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_71_9.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_71_9.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_71_10_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_71_10.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_71_10.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_71_11_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_71_11.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_71_11.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_71_12_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_71_12.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_71_12.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_71_13_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_71_13.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_71_13.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_71_14_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_71_14.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_71_14.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_71_15_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_71_15.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_71_15.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_71_16_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_71_16.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_71_16.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_71_17_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_71_17.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_71_17.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_71_18_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_71_18.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_71_18.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_71_19_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_71_19.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_71_19.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_71_20_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_71_20.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_71_20.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_71_21_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_71_21.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_71_21.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_71_22_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_71_22.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_71_22.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_71_23_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_71_23.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_71_23.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_71_24_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_71_24.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_71_24.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_72_5_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_72_5.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_72_5.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_72_6_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_72_6.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_72_6.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_72_7_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_72_7.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_72_7.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_72_8_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_72_8.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_72_8.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_72_9_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_72_9.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_72_9.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_72_10_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_72_10.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_72_10.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_72_11_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_72_11.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_72_11.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_72_12_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_72_12.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_72_12.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_72_13_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_72_13.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_72_13.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_72_14_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_72_14.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_72_14.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_72_15_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_72_15.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_72_15.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_72_16_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_72_16.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_72_16.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_72_17_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_72_17.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_72_17.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_72_18_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_72_18.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_72_18.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_72_19_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_72_19.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_72_19.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_72_20_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_72_20.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_72_20.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_72_21_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_72_21.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_72_21.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_72_22_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_72_22.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_72_22.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_72_23_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_72_23.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_72_23.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_72_24_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_72_24.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_72_24.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_73_50_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_73_50.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_73_50.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_73_55_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_73_55.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_73_55.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_73_60_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_73_60.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_73_60.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_73_65_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_73_65.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_73_65.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_73_70_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_73_70.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_73_70.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_73_75_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_73_75.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_73_75.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_73_80_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_73_80.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_73_80.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_73_85_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_73_85.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_73_85.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_73_90_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_73_90.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_73_90.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_73_95_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_73_95.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_73_95.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_73_100_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_73_100.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_73_100.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_73_105_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_73_105.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_73_105.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_73_110_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_73_110.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_73_110.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_73_115_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_73_115.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_73_115.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_73_120_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_73_120.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_73_120.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_74_10_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_74_10.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_74_10.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_74_11_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_74_11.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_74_11.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_74_12_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_74_12.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_74_12.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_74_13_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_74_13.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_74_13.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_74_14_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_74_14.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_74_14.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_74_15_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_74_15.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_74_15.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_74_16_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_74_16.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_74_16.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_74_17_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_74_17.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_74_17.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_74_18_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_74_18.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_74_18.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_74_19_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_74_19.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_74_19.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_74_20_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_74_20.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_74_20.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_74_21_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_74_21.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_74_21.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_74_22_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_74_22.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_74_22.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_74_23_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_74_23.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_74_23.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_74_24_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_74_24.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_74_24.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_75_5_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_75_5.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_75_5.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_75_6_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_75_6.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_75_6.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_75_7_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_75_7.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_75_7.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_75_8_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_75_8.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_75_8.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_75_9_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_75_9.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_75_9.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_75_10_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_75_10.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_75_10.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_75_11_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_75_11.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_75_11.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_75_12_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_75_12.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_75_12.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_75_13_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_75_13.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_75_13.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_75_14_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_75_14.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_75_14.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_75_15_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_75_15.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_75_15.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_75_16_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_75_16.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_75_16.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_75_17_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_75_17.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_75_17.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_75_18_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_75_18.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_75_18.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_75_19_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_75_19.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_75_19.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_75_20_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_75_20.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_75_20.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_75_21_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_75_21.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_75_21.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_75_22_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_75_22.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_75_22.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_75_23_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_75_23.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_75_23.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_75_24_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_75_24.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_75_24.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_76_25_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_76_25.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_76_25.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_76_30_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_76_30.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_76_30.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_76_35_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_76_35.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_76_35.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_76_40_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_76_40.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_76_40.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_76_45_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_76_45.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_76_45.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_76_50_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_76_50.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_76_50.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_76_55_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_76_55.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_76_55.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_76_60_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_76_60.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_76_60.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_76_65_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_76_65.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_76_65.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_76_70_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_76_70.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_76_70.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_76_75_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_76_75.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_76_75.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_76_80_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_76_80.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_76_80.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_76_85_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_76_85.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_76_85.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_76_90_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_76_90.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_76_90.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_76_95_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_76_95.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_76_95.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_76_100_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_76_100.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_76_100.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_76_105_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_76_105.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_76_105.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_76_110_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_76_110.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_76_110.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_76_115_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_76_115.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_76_115.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_76_120_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_76_120.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_76_120.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_77_5_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_77_5.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_77_5.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_77_6_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_77_6.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_77_6.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_77_7_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_77_7.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_77_7.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_77_8_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_77_8.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_77_8.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_77_9_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_77_9.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_77_9.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_77_10_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_77_10.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_77_10.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_77_11_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_77_11.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_77_11.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_77_12_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_77_12.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_77_12.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_77_13_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_77_13.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_77_13.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_77_14_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_77_14.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_77_14.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_77_15_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_77_15.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_77_15.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_77_16_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_77_16.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_77_16.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_77_17_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_77_17.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_77_17.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_77_18_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_77_18.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_77_18.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_77_19_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_77_19.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_77_19.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_77_20_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_77_20.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_77_20.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_77_21_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_77_21.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_77_21.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_77_22_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_77_22.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_77_22.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_77_23_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_77_23.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_77_23.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_77_24_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_77_24.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_77_24.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_78_5_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_78_5.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_78_5.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_78_6_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_78_6.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_78_6.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_78_7_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_78_7.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_78_7.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_78_8_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_78_8.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_78_8.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_78_9_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_78_9.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_78_9.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_78_10_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_78_10.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_78_10.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_118_50_5_match :
    ((Q2.charsAt2 ⟨118, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_118_50_5.D2 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_118_50_5.D1 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_118_50_10_match :
    ((Q2.charsAt2 ⟨118, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_118_50_10.D2 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_118_50_10.D1 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_118_50_15_match :
    ((Q2.charsAt2 ⟨118, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_118_50_15.D2 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_118_50_15.D1 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_118_50_20_match :
    ((Q2.charsAt2 ⟨118, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_118_50_20.D2 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_118_50_20.D1 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_118_65_5_match :
    ((Q2.charsAt2 ⟨118, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_118_65_5.D2 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_118_65_5.D1 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_118_65_6_match :
    ((Q2.charsAt2 ⟨118, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_118_65_6.D2 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_118_65_6.D1 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

end LeanDring.P5Presentation
