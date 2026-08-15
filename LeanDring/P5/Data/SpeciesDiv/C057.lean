/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.EntrySupport
import LeanDring.P5.Certificate.Characters.Twin1.CharAssembly
import LeanDring.P5.Certificate.Characters.Twin2.CharAssembly
import LeanDring.P5.Data.ColCdd.C041

/-!
# Species-table cells, stages 3-4 — residual real-decide certificates (divergent columns).
Auto-emitted by python/p5_stage34_emit.py. Chunk 56: 7 columns.
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

theorem colCertDiv_98_36_5_match :
    ((Q2.charsAt2 ⟨98, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_98_36_5.D2 (m := 25)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_98_36_5.D1 (m := 25)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_98_36_10_match :
    ((Q2.charsAt2 ⟨98, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_98_36_10.D2 (m := 25)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_98_36_10.D1 (m := 25)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_98_36_15_match :
    ((Q2.charsAt2 ⟨98, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_98_36_15.D2 (m := 25)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_98_36_15.D1 (m := 25)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_98_36_20_match :
    ((Q2.charsAt2 ⟨98, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_98_36_20.D2 (m := 25)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_98_36_20.D1 (m := 25)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_99_37_5_match :
    ((Q2.charsAt2 ⟨99, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_99_37_5.D2 (m := 25)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_99_37_5.D1 (m := 25)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_99_37_10_match :
    ((Q2.charsAt2 ⟨99, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_99_37_10.D2 (m := 25)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_99_37_10.D1 (m := 25)) (e.map ZMod.val))))).all id = true := by decide

theorem colCertDiv_99_37_15_match :
    ((Q2.charsAt2 ⟨99, by decide⟩).map (fun e =>
        decide (LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_99_37_15.D2 (m := 25)) (e.map ZMod.val))
          = LeanDring.P5CyclotomicCode.sumPowers
            (fastCode (colFn colCertDiv_99_37_15.D1 (m := 25)) (e.map ZMod.val))))).all id = true := by decide

end LeanDring.P5Presentation
