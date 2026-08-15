/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.EntrySupport
import LeanDring.P5.Certificate.Characters.Twin1.CharAssembly
import LeanDring.P5.Certificate.Characters.Twin2.CharAssembly
import LeanDring.P5.Data.ColCdd.C023
import LeanDring.P5.Data.ColCdd.C024
import LeanDring.P5.Data.ColCdd.C025
import LeanDring.P5.Data.ColCdd.C026
import LeanDring.P5.Data.ColCdd.C027

/-!
# Species-table cells, stages 3-4 — residual real-decide certificates (divergent columns).
Auto-emitted by python/p5_stage34_emit.py. Chunk 37: 240 columns.
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

theorem colCertDiv_147_44_10_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_44_10.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_44_10.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_44_15_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_44_15.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_44_15.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_44_20_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_44_20.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_44_20.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_45_5_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_45_5.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_45_5.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_45_10_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_45_10.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_45_10.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_45_15_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_45_15.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_45_15.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_45_20_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_45_20.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_45_20.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_46_5_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_46_5.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_46_5.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_46_10_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_46_10.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_46_10.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_46_15_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_46_15.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_46_15.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_46_20_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_46_20.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_46_20.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_47_5_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_47_5.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_47_5.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_47_10_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_47_10.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_47_10.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_47_15_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_47_15.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_47_15.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_47_20_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_47_20.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_47_20.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_48_5_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_48_5.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_48_5.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_48_10_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_48_10.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_48_10.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_48_15_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_48_15.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_48_15.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_48_20_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_48_20.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_48_20.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_49_10_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_49_10.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_49_10.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_49_15_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_49_15.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_49_15.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_49_20_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_49_20.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_49_20.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_50_5_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_50_5.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_50_5.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_50_10_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_50_10.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_50_10.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_50_15_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_50_15.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_50_15.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_50_20_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_50_20.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_50_20.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_51_5_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_51_5.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_51_5.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_51_10_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_51_10.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_51_10.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_51_15_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_51_15.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_51_15.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_51_20_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_51_20.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_51_20.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_52_5_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_52_5.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_52_5.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_52_10_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_52_10.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_52_10.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_52_15_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_52_15.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_52_15.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_52_20_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_52_20.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_52_20.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_55_5_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_55_5.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_55_5.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_55_6_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_55_6.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_55_6.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_55_7_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_55_7.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_55_7.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_55_8_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_55_8.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_55_8.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_55_9_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_55_9.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_55_9.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_55_10_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_55_10.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_55_10.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_55_11_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_55_11.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_55_11.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_55_12_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_55_12.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_55_12.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_55_13_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_55_13.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_55_13.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_55_14_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_55_14.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_55_14.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_55_15_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_55_15.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_55_15.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_55_16_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_55_16.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_55_16.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_55_17_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_55_17.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_55_17.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_55_18_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_55_18.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_55_18.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_55_19_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_55_19.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_55_19.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_55_20_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_55_20.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_55_20.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_55_21_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_55_21.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_55_21.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_55_22_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_55_22.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_55_22.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_55_23_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_55_23.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_55_23.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_55_24_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_55_24.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_55_24.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_56_5_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_56_5.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_56_5.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_56_6_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_56_6.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_56_6.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_56_7_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_56_7.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_56_7.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_56_8_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_56_8.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_56_8.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_56_9_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_56_9.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_56_9.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_56_10_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_56_10.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_56_10.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_56_11_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_56_11.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_56_11.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_56_12_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_56_12.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_56_12.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_56_13_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_56_13.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_56_13.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_56_14_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_56_14.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_56_14.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_56_15_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_56_15.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_56_15.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_56_16_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_56_16.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_56_16.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_56_17_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_56_17.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_56_17.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_56_18_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_56_18.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_56_18.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_56_19_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_56_19.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_56_19.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_56_20_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_56_20.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_56_20.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_56_21_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_56_21.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_56_21.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_56_22_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_56_22.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_56_22.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_56_23_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_56_23.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_56_23.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_56_24_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_56_24.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_56_24.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_57_5_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_57_5.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_57_5.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_57_6_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_57_6.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_57_6.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_57_7_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_57_7.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_57_7.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_57_8_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_57_8.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_57_8.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_57_9_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_57_9.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_57_9.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_57_10_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_57_10.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_57_10.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_57_11_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_57_11.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_57_11.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_57_12_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_57_12.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_57_12.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_57_13_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_57_13.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_57_13.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_57_14_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_57_14.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_57_14.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_57_15_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_57_15.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_57_15.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_57_16_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_57_16.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_57_16.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_57_17_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_57_17.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_57_17.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_57_18_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_57_18.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_57_18.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_57_19_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_57_19.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_57_19.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_57_20_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_57_20.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_57_20.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_57_21_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_57_21.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_57_21.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_57_22_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_57_22.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_57_22.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_57_23_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_57_23.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_57_23.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_57_24_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_57_24.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_57_24.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_58_5_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_58_5.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_58_5.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_58_6_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_58_6.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_58_6.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_58_7_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_58_7.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_58_7.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_58_8_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_58_8.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_58_8.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_58_9_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_58_9.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_58_9.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_58_10_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_58_10.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_58_10.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_58_11_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_58_11.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_58_11.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_58_12_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_58_12.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_58_12.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_58_13_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_58_13.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_58_13.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_58_14_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_58_14.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_58_14.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_58_15_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_58_15.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_58_15.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_58_16_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_58_16.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_58_16.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_58_17_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_58_17.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_58_17.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_58_18_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_58_18.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_58_18.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_58_19_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_58_19.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_58_19.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_58_20_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_58_20.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_58_20.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_58_21_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_58_21.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_58_21.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_58_22_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_58_22.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_58_22.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_58_23_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_58_23.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_58_23.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_58_24_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_58_24.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_58_24.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_60_10_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_60_10.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_60_10.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_60_11_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_60_11.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_60_11.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_60_12_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_60_12.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_60_12.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_60_13_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_60_13.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_60_13.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_60_14_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_60_14.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_60_14.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_60_15_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_60_15.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_60_15.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_60_16_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_60_16.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_60_16.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_60_17_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_60_17.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_60_17.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_60_18_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_60_18.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_60_18.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_60_19_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_60_19.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_60_19.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_60_20_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_60_20.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_60_20.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_60_21_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_60_21.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_60_21.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_60_22_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_60_22.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_60_22.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_60_23_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_60_23.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_60_23.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_60_24_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_60_24.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_60_24.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_61_10_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_61_10.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_61_10.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_61_11_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_61_11.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_61_11.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_61_12_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_61_12.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_61_12.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_61_13_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_61_13.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_61_13.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_61_14_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_61_14.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_61_14.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_61_15_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_61_15.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_61_15.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_61_16_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_61_16.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_61_16.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_61_17_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_61_17.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_61_17.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_61_18_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_61_18.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_61_18.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_61_19_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_61_19.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_61_19.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_61_20_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_61_20.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_61_20.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_61_21_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_61_21.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_61_21.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_61_22_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_61_22.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_61_22.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_61_23_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_61_23.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_61_23.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_61_24_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_61_24.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_61_24.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_62_10_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_62_10.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_62_10.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_62_11_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_62_11.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_62_11.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_62_12_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_62_12.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_62_12.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_62_13_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_62_13.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_62_13.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_62_14_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_62_14.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_62_14.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_62_15_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_62_15.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_62_15.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_62_16_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_62_16.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_62_16.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_62_17_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_62_17.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_62_17.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_62_18_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_62_18.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_62_18.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_62_19_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_62_19.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_62_19.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_62_20_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_62_20.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_62_20.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_62_21_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_62_21.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_62_21.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_62_22_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_62_22.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_62_22.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_62_23_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_62_23.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_62_23.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_62_24_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_62_24.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_62_24.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_63_5_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_63_5.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_63_5.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_63_6_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_63_6.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_63_6.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_63_7_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_63_7.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_63_7.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_63_8_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_63_8.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_63_8.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_63_9_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_63_9.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_63_9.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_63_10_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_63_10.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_63_10.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_63_11_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_63_11.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_63_11.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_63_12_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_63_12.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_63_12.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_63_13_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_63_13.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_63_13.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_63_14_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_63_14.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_63_14.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_63_20_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_63_20.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_63_20.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_63_21_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_63_21.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_63_21.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_63_22_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_63_22.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_63_22.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_63_23_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_63_23.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_63_23.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_63_24_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_63_24.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_63_24.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_64_50_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_64_50.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_64_50.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_64_55_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_64_55.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_64_55.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_64_60_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_64_60.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_64_60.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_64_65_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_64_65.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_64_65.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_64_70_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_64_70.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_64_70.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_64_75_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_64_75.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_64_75.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_64_80_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_64_80.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_64_80.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_64_85_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_64_85.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_64_85.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_64_90_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_64_90.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_64_90.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_64_95_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_64_95.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_64_95.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_64_100_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_64_100.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_64_100.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_64_105_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_64_105.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_64_105.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_64_110_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_64_110.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_64_110.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_64_115_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_64_115.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_64_115.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_64_120_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_64_120.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_64_120.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_65_5_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_65_5.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_65_5.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_65_6_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_65_6.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_65_6.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_65_7_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_65_7.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_65_7.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_65_8_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_65_8.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_65_8.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_65_9_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_65_9.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_65_9.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_65_10_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_65_10.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_65_10.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_65_11_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_65_11.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_65_11.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_65_12_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_65_12.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_65_12.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_65_13_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_65_13.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_65_13.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_65_14_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_65_14.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_65_14.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_65_15_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_65_15.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_65_15.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_65_16_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_65_16.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_65_16.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_65_17_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_65_17.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_65_17.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_65_18_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_65_18.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_65_18.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_65_19_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_65_19.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_65_19.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_65_20_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_65_20.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_65_20.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_65_21_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_65_21.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_65_21.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_65_22_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_65_22.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_65_22.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_65_23_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_65_23.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_65_23.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_65_24_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_65_24.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_65_24.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_66_5_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_66_5.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_66_5.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_66_6_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_66_6.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_66_6.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_66_7_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_66_7.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_66_7.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_66_8_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_66_8.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_66_8.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_66_9_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_66_9.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_66_9.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_66_10_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_66_10.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_66_10.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_66_11_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_66_11.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_66_11.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_66_12_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_66_12.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_66_12.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_66_13_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_66_13.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_66_13.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_66_14_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_66_14.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_66_14.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_66_15_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_66_15.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_66_15.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_66_16_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_66_16.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_66_16.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_66_17_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_66_17.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_66_17.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_66_18_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_66_18.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_66_18.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_66_19_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_66_19.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_66_19.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_66_20_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_66_20.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_66_20.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_66_21_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_66_21.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_66_21.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_66_22_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_66_22.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_66_22.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_66_23_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_66_23.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_66_23.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_66_24_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_66_24.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_66_24.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_67_75_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_67_75.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_67_75.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_67_80_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_67_80.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_67_80.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_67_85_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_67_85.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_67_85.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_67_90_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_67_90.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_67_90.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_67_95_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_67_95.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_67_95.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_67_100_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_67_100.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_67_100.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_67_105_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_67_105.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_67_105.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_67_110_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_67_110.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_67_110.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_67_115_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_67_115.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_67_115.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_67_120_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_67_120.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_67_120.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_147_68_5_match :
    ((Q2.charsAt2 ⟨147, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_68_5.D2 (m := 1)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_147_68_5.D1 (m := 1)) (e.map ZMod.val))))).all id = true := by decide

end LeanDring.P5Presentation
