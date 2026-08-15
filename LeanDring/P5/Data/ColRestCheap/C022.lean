/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.Twin1.ColCert
import LeanDring.P5.Data.EntryK.C025

/-!
# Species-table cell data, stage 2 — twin-coincident columns (cheap tier)

Per-column certified exponent-vector data (`ColCert`/`ColCertDiv`) with kernel
`decide` bindings. Emitted; the embedded lists are what the kernel certifies.
rest tier, chunk 21: 60 columns.
-/

-- machine-emitted data: silence style linters (generated long lines, file-level options)
set_option linter.style.longLine false

namespace LeanDring.P5Presentation

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

def colCert_116_95_15 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨95, by decide⟩
  m := 5
  T1 := T116_95
  T2 := Q2.T116_95_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 3, 0], [0, 0, 3, 3], [0, 0, 3, 1], [0, 0, 3, 4], [0, 0, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_95_20 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨95, by decide⟩
  m := 5
  T1 := T116_95
  T2 := Q2.T116_95_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 4, 0], [0, 0, 4, 4], [0, 0, 4, 3], [0, 0, 4, 2], [0, 0, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_95_25 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨95, by decide⟩
  m := 5
  T1 := T116_95
  T2 := Q2.T116_95_2
  h1 := (0,1,2,0,0)
  h2 := (0,1,2,0,0)
  D := [[1, 2, 0, 3], [1, 2, 1, 3], [1, 2, 2, 4], [1, 2, 3, 1], [1, 2, 4, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_95_50 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨95, by decide⟩
  m := 5
  T1 := T116_95
  T2 := Q2.T116_95_2
  h1 := (0,2,4,0,2)
  h2 := (0,2,4,0,2)
  D := [[2, 4, 0, 4], [2, 4, 2, 4], [2, 4, 4, 1], [2, 4, 1, 0], [2, 4, 3, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_95_75 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨95, by decide⟩
  m := 5
  T1 := T116_95
  T2 := Q2.T116_95_2
  h1 := (0,3,1,0,1)
  h2 := (0,3,1,0,1)
  D := [[3, 1, 0, 3], [3, 1, 3, 3], [3, 1, 1, 1], [3, 1, 4, 2], [3, 1, 2, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_95_100 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨95, by decide⟩
  m := 5
  T1 := T116_95
  T2 := Q2.T116_95_2
  h1 := (0,4,3,0,2)
  h2 := (0,4,3,0,2)
  D := [[4, 3, 0, 0], [4, 3, 4, 0], [4, 3, 3, 4], [4, 3, 2, 2], [4, 3, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_100_0 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨100, by decide⟩
  m := 5
  T1 := T116_100
  T2 := Q2.T116_100_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_100_1 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨100, by decide⟩
  m := 5
  T1 := T116_100
  T2 := Q2.T116_100_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_100_2 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨100, by decide⟩
  m := 5
  T1 := T116_100
  T2 := Q2.T116_100_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_100_3 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨100, by decide⟩
  m := 5
  T1 := T116_100
  T2 := Q2.T116_100_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_100_4 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨100, by decide⟩
  m := 5
  T1 := T116_100
  T2 := Q2.T116_100_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_100_5 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨100, by decide⟩
  m := 5
  T1 := T116_100
  T2 := Q2.T116_100_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 1, 0], [0, 0, 1, 1], [0, 0, 1, 2], [0, 0, 1, 3], [0, 0, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_100_10 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨100, by decide⟩
  m := 5
  T1 := T116_100
  T2 := Q2.T116_100_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 2, 0], [0, 0, 2, 2], [0, 0, 2, 4], [0, 0, 2, 1], [0, 0, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_100_15 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨100, by decide⟩
  m := 5
  T1 := T116_100
  T2 := Q2.T116_100_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 3, 0], [0, 0, 3, 3], [0, 0, 3, 1], [0, 0, 3, 4], [0, 0, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_100_20 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨100, by decide⟩
  m := 5
  T1 := T116_100
  T2 := Q2.T116_100_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 4, 0], [0, 0, 4, 4], [0, 0, 4, 3], [0, 0, 4, 2], [0, 0, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_100_25 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨100, by decide⟩
  m := 5
  T1 := T116_100
  T2 := Q2.T116_100_2
  h1 := (0,1,3,0,0)
  h2 := (0,1,3,0,0)
  D := [[1, 3, 0, 2], [1, 3, 1, 2], [1, 3, 2, 3], [1, 3, 3, 0], [1, 3, 4, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_100_50 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨100, by decide⟩
  m := 5
  T1 := T116_100
  T2 := Q2.T116_100_2
  h1 := (0,2,1,0,3)
  h2 := (0,2,1,0,3)
  D := [[2, 1, 0, 1], [2, 1, 2, 1], [2, 1, 4, 3], [2, 1, 1, 2], [2, 1, 3, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_100_75 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨100, by decide⟩
  m := 5
  T1 := T116_100
  T2 := Q2.T116_100_2
  h1 := (0,3,4,0,4)
  h2 := (0,3,4,0,4)
  D := [[3, 4, 0, 2], [3, 4, 3, 2], [3, 4, 1, 0], [3, 4, 4, 1], [3, 4, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_100_100 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨100, by decide⟩
  m := 5
  T1 := T116_100
  T2 := Q2.T116_100_2
  h1 := (0,4,2,0,3)
  h2 := (0,4,2,0,3)
  D := [[4, 2, 0, 0], [4, 2, 4, 0], [4, 2, 3, 4], [4, 2, 2, 2], [4, 2, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_105_0 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨105, by decide⟩
  m := 5
  T1 := T116_105
  T2 := Q2.T116_105_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_105_1 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨105, by decide⟩
  m := 5
  T1 := T116_105
  T2 := Q2.T116_105_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_105_2 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨105, by decide⟩
  m := 5
  T1 := T116_105
  T2 := Q2.T116_105_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_105_3 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨105, by decide⟩
  m := 5
  T1 := T116_105
  T2 := Q2.T116_105_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_105_4 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨105, by decide⟩
  m := 5
  T1 := T116_105
  T2 := Q2.T116_105_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_105_5 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨105, by decide⟩
  m := 5
  T1 := T116_105
  T2 := Q2.T116_105_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 1, 0], [0, 0, 1, 1], [0, 0, 1, 2], [0, 0, 1, 3], [0, 0, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_105_10 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨105, by decide⟩
  m := 5
  T1 := T116_105
  T2 := Q2.T116_105_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 2, 0], [0, 0, 2, 2], [0, 0, 2, 4], [0, 0, 2, 1], [0, 0, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_105_15 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨105, by decide⟩
  m := 5
  T1 := T116_105
  T2 := Q2.T116_105_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 3, 0], [0, 0, 3, 3], [0, 0, 3, 1], [0, 0, 3, 4], [0, 0, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_105_20 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨105, by decide⟩
  m := 5
  T1 := T116_105
  T2 := Q2.T116_105_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 4, 0], [0, 0, 4, 4], [0, 0, 4, 3], [0, 0, 4, 2], [0, 0, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_105_25 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨105, by decide⟩
  m := 5
  T1 := T116_105
  T2 := Q2.T116_105_2
  h1 := (0,1,1,0,0)
  h2 := (0,1,1,0,0)
  D := [[1, 1, 0, 4], [1, 1, 1, 4], [1, 1, 2, 0], [1, 1, 3, 2], [1, 1, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_105_50 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨105, by decide⟩
  m := 5
  T1 := T116_105
  T2 := Q2.T116_105_2
  h1 := (0,2,2,0,1)
  h2 := (0,2,2,0,1)
  D := [[2, 2, 0, 2], [2, 2, 2, 2], [2, 2, 4, 4], [2, 2, 1, 3], [2, 2, 3, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_105_75 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨105, by decide⟩
  m := 5
  T1 := T116_105
  T2 := Q2.T116_105_2
  h1 := (0,3,3,0,3)
  h2 := (0,3,3,0,3)
  D := [[3, 3, 0, 4], [3, 3, 3, 4], [3, 3, 1, 2], [3, 3, 4, 3], [3, 3, 2, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_105_100 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨105, by decide⟩
  m := 5
  T1 := T116_105
  T2 := Q2.T116_105_2
  h1 := (0,4,4,0,1)
  h2 := (0,4,4,0,1)
  D := [[4, 4, 0, 0], [4, 4, 4, 0], [4, 4, 3, 4], [4, 4, 2, 2], [4, 4, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_110_0 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨110, by decide⟩
  m := 5
  T1 := T116_110
  T2 := Q2.T116_110_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_110_1 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨110, by decide⟩
  m := 5
  T1 := T116_110
  T2 := Q2.T116_110_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_110_2 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨110, by decide⟩
  m := 5
  T1 := T116_110
  T2 := Q2.T116_110_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_110_3 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨110, by decide⟩
  m := 5
  T1 := T116_110
  T2 := Q2.T116_110_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_110_4 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨110, by decide⟩
  m := 5
  T1 := T116_110
  T2 := Q2.T116_110_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_110_5 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨110, by decide⟩
  m := 5
  T1 := T116_110
  T2 := Q2.T116_110_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 1, 0], [0, 0, 1, 1], [0, 0, 1, 2], [0, 0, 1, 3], [0, 0, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_110_10 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨110, by decide⟩
  m := 5
  T1 := T116_110
  T2 := Q2.T116_110_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 2, 0], [0, 0, 2, 2], [0, 0, 2, 4], [0, 0, 2, 1], [0, 0, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_110_15 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨110, by decide⟩
  m := 5
  T1 := T116_110
  T2 := Q2.T116_110_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 3, 0], [0, 0, 3, 3], [0, 0, 3, 1], [0, 0, 3, 4], [0, 0, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_110_20 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨110, by decide⟩
  m := 5
  T1 := T116_110
  T2 := Q2.T116_110_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 4, 0], [0, 0, 4, 4], [0, 0, 4, 3], [0, 0, 4, 2], [0, 0, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_110_25 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨110, by decide⟩
  m := 5
  T1 := T116_110
  T2 := Q2.T116_110_2
  h1 := (0,1,0,0,0)
  h2 := (0,1,0,0,0)
  D := [[1, 0, 0, 0], [1, 0, 1, 0], [1, 0, 2, 1], [1, 0, 3, 3], [1, 0, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_110_50 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨110, by decide⟩
  m := 5
  T1 := T116_110
  T2 := Q2.T116_110_2
  h1 := (0,2,0,0,0)
  h2 := (0,2,0,0,0)
  D := [[2, 0, 0, 0], [2, 0, 2, 0], [2, 0, 4, 2], [2, 0, 1, 1], [2, 0, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_110_75 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨110, by decide⟩
  m := 5
  T1 := T116_110
  T2 := Q2.T116_110_2
  h1 := (0,3,0,0,0)
  h2 := (0,3,0,0,0)
  D := [[3, 0, 0, 0], [3, 0, 3, 0], [3, 0, 1, 3], [3, 0, 4, 4], [3, 0, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_110_100 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨110, by decide⟩
  m := 5
  T1 := T116_110
  T2 := Q2.T116_110_2
  h1 := (0,4,0,0,0)
  h2 := (0,4,0,0,0)
  D := [[4, 0, 0, 0], [4, 0, 4, 0], [4, 0, 3, 4], [4, 0, 2, 2], [4, 0, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_116_0 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨116, by decide⟩
  m := 5
  T1 := T116_116
  T2 := Q2.T116_116_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_116_1 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨116, by decide⟩
  m := 5
  T1 := T116_116
  T2 := Q2.T116_116_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 1, 0], [0, 0, 1, 1], [0, 0, 1, 2], [0, 0, 1, 3], [0, 0, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_116_2 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨116, by decide⟩
  m := 5
  T1 := T116_116
  T2 := Q2.T116_116_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 2, 0], [0, 0, 2, 2], [0, 0, 2, 4], [0, 0, 2, 1], [0, 0, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_116_3 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨116, by decide⟩
  m := 5
  T1 := T116_116
  T2 := Q2.T116_116_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 3, 0], [0, 0, 3, 3], [0, 0, 3, 1], [0, 0, 3, 4], [0, 0, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_116_4 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨116, by decide⟩
  m := 5
  T1 := T116_116
  T2 := Q2.T116_116_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 4, 0], [0, 0, 4, 4], [0, 0, 4, 3], [0, 0, 4, 2], [0, 0, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_116_5 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨116, by decide⟩
  m := 5
  T1 := T116_116
  T2 := Q2.T116_116_2
  h1 := (0,0,1,0,0)
  h2 := (0,0,1,0,0)
  D := [[0, 1, 0, 0], [0, 1, 0, 0], [0, 1, 0, 0], [0, 1, 0, 0], [0, 1, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_116_6 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨116, by decide⟩
  m := 5
  T1 := T116_116
  T2 := Q2.T116_116_2
  h1 := (0,0,1,1,0)
  h2 := (0,0,1,1,0)
  D := [[0, 1, 1, 0], [0, 1, 1, 1], [0, 1, 1, 2], [0, 1, 1, 3], [0, 1, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_116_7 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨116, by decide⟩
  m := 5
  T1 := T116_116
  T2 := Q2.T116_116_2
  h1 := (0,0,1,2,0)
  h2 := (0,0,1,2,0)
  D := [[0, 1, 2, 0], [0, 1, 2, 2], [0, 1, 2, 4], [0, 1, 2, 1], [0, 1, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_116_8 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨116, by decide⟩
  m := 5
  T1 := T116_116
  T2 := Q2.T116_116_2
  h1 := (0,0,1,3,0)
  h2 := (0,0,1,3,0)
  D := [[0, 1, 3, 0], [0, 1, 3, 3], [0, 1, 3, 1], [0, 1, 3, 4], [0, 1, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_116_9 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨116, by decide⟩
  m := 5
  T1 := T116_116
  T2 := Q2.T116_116_2
  h1 := (0,0,1,4,0)
  h2 := (0,0,1,4,0)
  D := [[0, 1, 4, 0], [0, 1, 4, 4], [0, 1, 4, 3], [0, 1, 4, 2], [0, 1, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_116_10 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨116, by decide⟩
  m := 5
  T1 := T116_116
  T2 := Q2.T116_116_2
  h1 := (0,0,2,0,0)
  h2 := (0,0,2,0,0)
  D := [[0, 2, 0, 0], [0, 2, 0, 0], [0, 2, 0, 0], [0, 2, 0, 0], [0, 2, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_116_11 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨116, by decide⟩
  m := 5
  T1 := T116_116
  T2 := Q2.T116_116_2
  h1 := (0,0,2,1,0)
  h2 := (0,0,2,1,0)
  D := [[0, 2, 1, 0], [0, 2, 1, 1], [0, 2, 1, 2], [0, 2, 1, 3], [0, 2, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_116_12 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨116, by decide⟩
  m := 5
  T1 := T116_116
  T2 := Q2.T116_116_2
  h1 := (0,0,2,2,0)
  h2 := (0,0,2,2,0)
  D := [[0, 2, 2, 0], [0, 2, 2, 2], [0, 2, 2, 4], [0, 2, 2, 1], [0, 2, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_116_13 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨116, by decide⟩
  m := 5
  T1 := T116_116
  T2 := Q2.T116_116_2
  h1 := (0,0,2,3,0)
  h2 := (0,0,2,3,0)
  D := [[0, 2, 3, 0], [0, 2, 3, 3], [0, 2, 3, 1], [0, 2, 3, 4], [0, 2, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_116_14 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨116, by decide⟩
  m := 5
  T1 := T116_116
  T2 := Q2.T116_116_2
  h1 := (0,0,2,4,0)
  h2 := (0,0,2,4,0)
  D := [[0, 2, 4, 0], [0, 2, 4, 4], [0, 2, 4, 3], [0, 2, 4, 2], [0, 2, 4, 1]]
  bind1 := by decide
  bind2 := by decide

end LeanDring.P5Presentation
