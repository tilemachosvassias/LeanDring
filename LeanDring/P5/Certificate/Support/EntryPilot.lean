/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.Twin1.EntryCore

/-!
# Kernel-cost probes for the species-entry machinery

**Outside the build closure.** Nothing imports this file. It proves nothing the
development uses: each declaration below is a `decide` on hand-picked sample
data, run to measure what one stage of the `entryCode` pipeline costs the kernel
so that the emitted certificate files could be chunked to a size the elaborator
accepts. It is kept for provenance of that sizing.

The stages measured are those a real species-table cell goes through: the return
elements `t⁻¹·h·t` (`invC` and two `mulC`), `charForm` over the transversal, and
the `sumPowers` code comparison. `B143` and `B28` are sample echelon bases of
length 4 and 2, `T5` and `T25` sample transversals; none of them is certified
data.
-/

-- The probes below are deliberately run past the default budgets: measuring the
-- kernel cost of a stage is the point of the file.
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace LeanDring.P5EntryPilot
open LeanDring.P5Presentation LeanDring.P5CyclotomicCode

/-- A length-4 (maximal) echelon-shaped basis, standing in for `basisAt rK`. -/
def B143 : List Coordinates := [(1,0,0,0,0),(0,1,2,0,4),(0,0,0,1,0),(0,0,0,0,1)]

/-- A length-2 basis (order-25 subgroup), where the 68≠69 A-block lives. -/
def B28 : List Coordinates := [(0,1,4,4,2),(0,0,0,0,1)]

/-- An explicit 5-element transversal (coset reps in `G`). -/
def T5 : List Coordinates :=
 [(0,0,0,0,0),(1,0,4,1,0),(2,0,3,2,1),(3,0,2,3,3),(4,0,1,4,1)]

/-- A 25-element transversal, projecting the larger fixed-point sets. -/
def T25 : List Coordinates :=
 [(0,0,0,0,0),(1,0,0,0,0),(0,1,0,0,0),(0,0,1,0,0),(0,0,0,1,0),
  (1,1,1,1,1),(2,3,4,0,1),(3,1,4,1,2),(4,4,4,4,4),(1,2,3,4,0),
  (0,2,0,2,0),(2,0,2,0,2),(1,3,1,3,1),(3,3,3,0,0),(4,0,1,2,3),
  (2,2,0,1,4),(1,4,2,3,0),(0,1,2,3,4),(4,3,2,1,0),(2,1,0,4,3),
  (3,0,0,0,1),(0,0,3,0,0),(1,1,0,0,2),(2,2,2,2,2),(0,4,0,1,3)]

/-- The return element `t⁻¹·h·t` in the `Coordinate q` group. -/
def returnElt (q : ℕ) (h t : Coordinates) : Coordinates :=
  mulC q (mulC q (invC q t) h) t

/-! ## Return elements `t⁻¹·h·t` (`invC` + 2×`mulC`) -/

-- 25 return elements in the q=1 group.
theorem cost_returnElt_25_q1 :
    (T25.map (fun t => (returnElt 1 (1,2,3,4,0) t).1)).count 0 ≤ 25 := by decide

-- 25 return elements in the q=2 group (touches the second step table).
theorem cost_returnElt_25_q2 :
    (T25.map (fun t => (returnElt 2 (1,2,3,4,0) t).1)).count 0 ≤ 25 := by decide

/-! ## `charForm` over the transversal — the per-cell exponent list -/

-- 25 charForm evaluations at return elements against the length-4 basis (q=1).
theorem cost_charForm_25_len4_q1 :
    (T25.map (fun t => (charForm B143 [7,3,11,19] (returnElt 1 (1,2,3,4,0) t)).val)).sum
      ≤ 500000 := by decide

-- 25 charForm evaluations against the length-2 (order-25) basis.
theorem cost_charForm_25_len2_q1 :
    (T25.map (fun t => (charForm B28 [7,3] (returnElt 1 (1,2,3,4,0) t)).val)).sum
      ≤ 500000 := by decide

/-! ## Full per-cell `entryCode` build (`sumPowers`) and comparison -/

-- Build a real entryCode from a 5-element transversal (charForm over the returns).
def pilotExp (t : Fin 5 → Coordinates) : Fin 5 → ℕ :=
  fun i => (charForm B143 [7,3,11,19] (returnElt 1 (1,2,3,4,0) (t i))).val

-- Force one entryCode to a concrete length-20 integer array in the kernel; the
-- statement is trivial, the reduction it demands is what is being measured.
theorem cost_entryCode_build :
    sumPowers (pilotExp (fun i => T5.getD i.val (0,0,0,0,0)))
      = sumPowers (pilotExp (fun i => T5.getD i.val (0,0,0,0,0))) := by decide

-- 400 sumPowers comparisons (a 20×20 block) — `checkCertificate` throughput.
theorem cost_sumPowers_compare_400 :
    (List.range 20).all (fun a =>
      (List.range 20).all (fun b =>
        (decide (sumPowers (fun i : Fin 5 => (a + i.val) % 25)
              = sumPowers (fun i : Fin 5 => (b + i.val) % 25)))
          == (decide (a = b)))) = true := by decide

end LeanDring.P5EntryPilot
