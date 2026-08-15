/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.EntrySupport
import LeanDring.P5.Certificate.Characters.Twin1.CharAssembly
import LeanDring.P5.Certificate.Characters.Twin2.CharAssembly
import LeanDring.P5.Data.ColCdd.C039
import LeanDring.P5.Data.ColCdd.C040

/-!
# Species-table cells, stages 3-4 — residual real-decide certificates (divergent columns).
Auto-emitted by python/p5_stage34_emit.py. Chunk 47: 28 columns.
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

theorem colCertDiv_73_36_5_match :
    ((Q2.charsAt2 ⟨73, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_73_36_5.D2 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_73_36_5.D1 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_73_36_10_match :
    ((Q2.charsAt2 ⟨73, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_73_36_10.D2 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_73_36_10.D1 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_73_36_15_match :
    ((Q2.charsAt2 ⟨73, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_73_36_15.D2 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_73_36_15.D1 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_73_36_20_match :
    ((Q2.charsAt2 ⟨73, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_73_36_20.D2 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_73_36_20.D1 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_73_41_5_match :
    ((Q2.charsAt2 ⟨73, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_73_41_5.D2 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_73_41_5.D1 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_73_41_10_match :
    ((Q2.charsAt2 ⟨73, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_73_41_10.D2 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_73_41_10.D1 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_73_41_15_match :
    ((Q2.charsAt2 ⟨73, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_73_41_15.D2 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_73_41_15.D1 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_73_41_20_match :
    ((Q2.charsAt2 ⟨73, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_73_41_20.D2 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_73_41_20.D1 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_73_46_5_match :
    ((Q2.charsAt2 ⟨73, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_73_46_5.D2 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_73_46_5.D1 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_73_46_10_match :
    ((Q2.charsAt2 ⟨73, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_73_46_10.D2 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_73_46_10.D1 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_73_46_15_match :
    ((Q2.charsAt2 ⟨73, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_73_46_15.D2 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_73_46_15.D1 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_73_46_20_match :
    ((Q2.charsAt2 ⟨73, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_73_46_20.D2 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_73_46_20.D1 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_73_51_5_match :
    ((Q2.charsAt2 ⟨73, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_73_51_5.D2 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_73_51_5.D1 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_73_51_10_match :
    ((Q2.charsAt2 ⟨73, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_73_51_10.D2 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_73_51_10.D1 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_73_51_15_match :
    ((Q2.charsAt2 ⟨73, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_73_51_15.D2 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_73_51_15.D1 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_73_51_20_match :
    ((Q2.charsAt2 ⟨73, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_73_51_20.D2 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_73_51_20.D1 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_74_31_5_match :
    ((Q2.charsAt2 ⟨74, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_74_31_5.D2 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_74_31_5.D1 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_74_31_10_match :
    ((Q2.charsAt2 ⟨74, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_74_31_10.D2 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_74_31_10.D1 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_74_31_15_match :
    ((Q2.charsAt2 ⟨74, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_74_31_15.D2 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_74_31_15.D1 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_74_31_20_match :
    ((Q2.charsAt2 ⟨74, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_74_31_20.D2 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_74_31_20.D1 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_74_36_5_match :
    ((Q2.charsAt2 ⟨74, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_74_36_5.D2 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_74_36_5.D1 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_74_36_10_match :
    ((Q2.charsAt2 ⟨74, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_74_36_10.D2 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_74_36_10.D1 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_74_36_15_match :
    ((Q2.charsAt2 ⟨74, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_74_36_15.D2 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_74_36_15.D1 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_74_36_20_match :
    ((Q2.charsAt2 ⟨74, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_74_36_20.D2 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_74_36_20.D1 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_74_41_5_match :
    ((Q2.charsAt2 ⟨74, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_74_41_5.D2 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_74_41_5.D1 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_74_41_10_match :
    ((Q2.charsAt2 ⟨74, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_74_41_10.D2 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_74_41_10.D1 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_74_41_15_match :
    ((Q2.charsAt2 ⟨74, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_74_41_15.D2 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_74_41_15.D1 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_74_41_20_match :
    ((Q2.charsAt2 ⟨74, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_74_41_20.D2 (m := 5)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_74_41_20.D1 (m := 5)) (e.map ZMod.val))))).all id = true := by decide

end LeanDring.P5Presentation
