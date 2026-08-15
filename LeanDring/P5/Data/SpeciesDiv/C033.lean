/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.EntrySupport
import LeanDring.P5.Certificate.Characters.Twin1.CharAssembly
import LeanDring.P5.Certificate.Characters.Twin2.CharAssembly
import LeanDring.P5.Data.ColCdd.C003
import LeanDring.P5.Data.ColCdd.C021

/-!
# Species-table cells, stages 3-4 — residual real-decide certificates (divergent columns).
Auto-emitted by python/p5_stage34_emit.py. Chunk 32: 28 columns.
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

theorem colCertDiv_118_30_10_match :
    ((Q2.charsAt2 ⟨118, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_118_30_10.D2 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_118_30_10.D1 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_118_30_15_match :
    ((Q2.charsAt2 ⟨118, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_118_30_15.D2 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_118_30_15.D1 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_118_30_20_match :
    ((Q2.charsAt2 ⟨118, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_118_30_20.D2 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_118_30_20.D1 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_118_35_5_match :
    ((Q2.charsAt2 ⟨118, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_118_35_5.D2 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_118_35_5.D1 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_118_35_10_match :
    ((Q2.charsAt2 ⟨118, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_118_35_10.D2 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_118_35_10.D1 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_118_35_15_match :
    ((Q2.charsAt2 ⟨118, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_118_35_15.D2 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_118_35_15.D1 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_118_35_20_match :
    ((Q2.charsAt2 ⟨118, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_118_35_20.D2 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_118_35_20.D1 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_118_40_5_match :
    ((Q2.charsAt2 ⟨118, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_118_40_5.D2 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_118_40_5.D1 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_118_40_10_match :
    ((Q2.charsAt2 ⟨118, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_118_40_10.D2 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_118_40_10.D1 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_118_40_15_match :
    ((Q2.charsAt2 ⟨118, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_118_40_15.D2 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_118_40_15.D1 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_118_40_20_match :
    ((Q2.charsAt2 ⟨118, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_118_40_20.D2 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_118_40_20.D1 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_118_45_5_match :
    ((Q2.charsAt2 ⟨118, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_118_45_5.D2 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_118_45_5.D1 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_118_45_10_match :
    ((Q2.charsAt2 ⟨118, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_118_45_10.D2 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_118_45_10.D1 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_118_45_15_match :
    ((Q2.charsAt2 ⟨118, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_118_45_15.D2 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_118_45_15.D1 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_118_45_20_match :
    ((Q2.charsAt2 ⟨118, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_118_45_20.D2 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_118_45_20.D1 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_143_33_5_match :
    ((Q2.charsAt2 ⟨143, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_143_33_5.D2 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_143_33_5.D1 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_143_33_10_match :
    ((Q2.charsAt2 ⟨143, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_143_33_10.D2 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_143_33_10.D1 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_143_33_15_match :
    ((Q2.charsAt2 ⟨143, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_143_33_15.D2 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_143_33_15.D1 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_143_33_20_match :
    ((Q2.charsAt2 ⟨143, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_143_33_20.D2 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_143_33_20.D1 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_143_34_5_match :
    ((Q2.charsAt2 ⟨143, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_143_34_5.D2 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_143_34_5.D1 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_143_34_10_match :
    ((Q2.charsAt2 ⟨143, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_143_34_10.D2 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_143_34_10.D1 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_143_34_20_match :
    ((Q2.charsAt2 ⟨143, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_143_34_20.D2 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_143_34_20.D1 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_143_35_15_match :
    ((Q2.charsAt2 ⟨143, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_143_35_15.D2 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_143_35_15.D1 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_143_35_20_match :
    ((Q2.charsAt2 ⟨143, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_143_35_20.D2 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_143_35_20.D1 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_143_36_5_match :
    ((Q2.charsAt2 ⟨143, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_143_36_5.D2 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_143_36_5.D1 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_143_36_10_match :
    ((Q2.charsAt2 ⟨143, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_143_36_10.D2 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_143_36_10.D1 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_143_36_20_match :
    ((Q2.charsAt2 ⟨143, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_143_36_20.D2 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_143_36_20.D1 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_143_37_5_match :
    ((Q2.charsAt2 ⟨143, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_143_37_5.D2 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_143_37_5.D1 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

end LeanDring.P5Presentation
