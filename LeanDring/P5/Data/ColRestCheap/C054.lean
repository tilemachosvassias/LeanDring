/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.Twin1.ColCert
import LeanDring.P5.Data.EntryK.C031

/-!
# Species-table cell data, stage 2 — twin-coincident columns (cheap tier)

Per-column certified exponent-vector data (`ColCert`/`ColCertDiv`) with kernel
`decide` bindings. Emitted; the embedded lists are what the kernel certifies.
rest tier, chunk 53: 60 columns.
-/

-- machine-emitted data: silence style linters (generated long lines, file-level options)
set_option linter.style.longLine false

namespace LeanDring.P5Presentation

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

def colCert_124_92_0 : ColCert where
  rK := ⟨124, by decide⟩
  rH := ⟨92, by decide⟩
  m := 5
  T1 := T124_92
  T2 := Q2.T124_92_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_124_92_1 : ColCert where
  rK := ⟨124, by decide⟩
  rH := ⟨92, by decide⟩
  m := 5
  T1 := T124_92
  T2 := Q2.T124_92_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_124_92_2 : ColCert where
  rK := ⟨124, by decide⟩
  rH := ⟨92, by decide⟩
  m := 5
  T1 := T124_92
  T2 := Q2.T124_92_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_124_92_3 : ColCert where
  rK := ⟨124, by decide⟩
  rH := ⟨92, by decide⟩
  m := 5
  T1 := T124_92
  T2 := Q2.T124_92_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_124_92_4 : ColCert where
  rK := ⟨124, by decide⟩
  rH := ⟨92, by decide⟩
  m := 5
  T1 := T124_92
  T2 := Q2.T124_92_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_124_92_20 : ColCert where
  rK := ⟨124, by decide⟩
  rH := ⟨92, by decide⟩
  m := 5
  T1 := T124_92
  T2 := Q2.T124_92_2
  h1 := (4,3,2,4,1)
  h2 := (4,3,2,4,2)
  D := [[4, 3, 3, 1], [4, 3, 3, 3], [4, 3, 3, 0], [4, 3, 3, 2], [4, 3, 3, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_124_95_0 : ColCert where
  rK := ⟨124, by decide⟩
  rH := ⟨95, by decide⟩
  m := 5
  T1 := T124_95
  T2 := Q2.T124_95_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_124_95_1 : ColCert where
  rK := ⟨124, by decide⟩
  rH := ⟨95, by decide⟩
  m := 5
  T1 := T124_95
  T2 := Q2.T124_95_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_124_95_2 : ColCert where
  rK := ⟨124, by decide⟩
  rH := ⟨95, by decide⟩
  m := 5
  T1 := T124_95
  T2 := Q2.T124_95_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_124_95_3 : ColCert where
  rK := ⟨124, by decide⟩
  rH := ⟨95, by decide⟩
  m := 5
  T1 := T124_95
  T2 := Q2.T124_95_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_124_95_4 : ColCert where
  rK := ⟨124, by decide⟩
  rH := ⟨95, by decide⟩
  m := 5
  T1 := T124_95
  T2 := Q2.T124_95_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_124_95_5 : ColCert where
  rK := ⟨124, by decide⟩
  rH := ⟨95, by decide⟩
  m := 5
  T1 := T124_95
  T2 := Q2.T124_95_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_124_95_10 : ColCert where
  rK := ⟨124, by decide⟩
  rH := ⟨95, by decide⟩
  m := 5
  T1 := T124_95
  T2 := Q2.T124_95_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_124_95_15 : ColCert where
  rK := ⟨124, by decide⟩
  rH := ⟨95, by decide⟩
  m := 5
  T1 := T124_95
  T2 := Q2.T124_95_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_124_95_20 : ColCert where
  rK := ⟨124, by decide⟩
  rH := ⟨95, by decide⟩
  m := 5
  T1 := T124_95
  T2 := Q2.T124_95_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_124_101_0 : ColCert where
  rK := ⟨124, by decide⟩
  rH := ⟨101, by decide⟩
  m := 5
  T1 := T124_101
  T2 := Q2.T124_101_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_124_101_1 : ColCert where
  rK := ⟨124, by decide⟩
  rH := ⟨101, by decide⟩
  m := 5
  T1 := T124_101
  T2 := Q2.T124_101_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_124_101_2 : ColCert where
  rK := ⟨124, by decide⟩
  rH := ⟨101, by decide⟩
  m := 5
  T1 := T124_101
  T2 := Q2.T124_101_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_124_101_3 : ColCert where
  rK := ⟨124, by decide⟩
  rH := ⟨101, by decide⟩
  m := 5
  T1 := T124_101
  T2 := Q2.T124_101_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_124_101_4 : ColCert where
  rK := ⟨124, by decide⟩
  rH := ⟨101, by decide⟩
  m := 5
  T1 := T124_101
  T2 := Q2.T124_101_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_124_109_0 : ColCert where
  rK := ⟨124, by decide⟩
  rH := ⟨109, by decide⟩
  m := 5
  T1 := T124_109
  T2 := Q2.T124_109_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_124_109_1 : ColCert where
  rK := ⟨124, by decide⟩
  rH := ⟨109, by decide⟩
  m := 5
  T1 := T124_109
  T2 := Q2.T124_109_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_124_109_2 : ColCert where
  rK := ⟨124, by decide⟩
  rH := ⟨109, by decide⟩
  m := 5
  T1 := T124_109
  T2 := Q2.T124_109_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_124_109_3 : ColCert where
  rK := ⟨124, by decide⟩
  rH := ⟨109, by decide⟩
  m := 5
  T1 := T124_109
  T2 := Q2.T124_109_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_124_109_4 : ColCert where
  rK := ⟨124, by decide⟩
  rH := ⟨109, by decide⟩
  m := 5
  T1 := T124_109
  T2 := Q2.T124_109_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_124_113_0 : ColCert where
  rK := ⟨124, by decide⟩
  rH := ⟨113, by decide⟩
  m := 5
  T1 := T124_113
  T2 := Q2.T124_113_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_124_113_1 : ColCert where
  rK := ⟨124, by decide⟩
  rH := ⟨113, by decide⟩
  m := 5
  T1 := T124_113
  T2 := Q2.T124_113_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_124_113_2 : ColCert where
  rK := ⟨124, by decide⟩
  rH := ⟨113, by decide⟩
  m := 5
  T1 := T124_113
  T2 := Q2.T124_113_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_124_113_3 : ColCert where
  rK := ⟨124, by decide⟩
  rH := ⟨113, by decide⟩
  m := 5
  T1 := T124_113
  T2 := Q2.T124_113_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_124_113_4 : ColCert where
  rK := ⟨124, by decide⟩
  rH := ⟨113, by decide⟩
  m := 5
  T1 := T124_113
  T2 := Q2.T124_113_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_124_113_5 : ColCert where
  rK := ⟨124, by decide⟩
  rH := ⟨113, by decide⟩
  m := 5
  T1 := T124_113
  T2 := Q2.T124_113_2
  h1 := (1,3,0,1,2)
  h2 := (1,3,0,1,2)
  D := [[1, 3, 2, 2], [1, 3, 2, 4], [1, 3, 2, 1], [1, 3, 2, 3], [1, 3, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_124_124_0 : ColCert where
  rK := ⟨124, by decide⟩
  rH := ⟨124, by decide⟩
  m := 5
  T1 := T124_124
  T2 := Q2.T124_124_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_124_124_1 : ColCert where
  rK := ⟨124, by decide⟩
  rH := ⟨124, by decide⟩
  m := 5
  T1 := T124_124
  T2 := Q2.T124_124_2
  h1 := (0,1,2,0,4)
  h2 := (0,1,2,0,0)
  D := [[0, 1, 0, 4], [0, 1, 0, 3], [0, 1, 0, 2], [0, 1, 0, 1], [0, 1, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_124_124_2 : ColCert where
  rK := ⟨124, by decide⟩
  rH := ⟨124, by decide⟩
  m := 5
  T1 := T124_124
  T2 := Q2.T124_124_2
  h1 := (0,2,4,0,0)
  h2 := (0,2,4,0,2)
  D := [[0, 2, 0, 3], [0, 2, 0, 1], [0, 2, 0, 4], [0, 2, 0, 2], [0, 2, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_124_124_3 : ColCert where
  rK := ⟨124, by decide⟩
  rH := ⟨124, by decide⟩
  m := 5
  T1 := T124_124
  T2 := Q2.T124_124_2
  h1 := (0,3,1,0,3)
  h2 := (0,3,1,0,1)
  D := [[0, 3, 0, 2], [0, 3, 0, 4], [0, 3, 0, 1], [0, 3, 0, 3], [0, 3, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_124_124_4 : ColCert where
  rK := ⟨124, by decide⟩
  rH := ⟨124, by decide⟩
  m := 5
  T1 := T124_124
  T2 := Q2.T124_124_2
  h1 := (0,4,3,0,3)
  h2 := (0,4,3,0,2)
  D := [[0, 4, 0, 1], [0, 4, 0, 2], [0, 4, 0, 3], [0, 4, 0, 4], [0, 4, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_124_124_5 : ColCert where
  rK := ⟨124, by decide⟩
  rH := ⟨124, by decide⟩
  m := 5
  T1 := T124_124
  T2 := Q2.T124_124_2
  h1 := (1,0,4,1,2)
  h2 := (1,0,4,1,4)
  D := [[1, 0, 0, 0], [1, 0, 0, 0], [1, 0, 0, 0], [1, 0, 0, 0], [1, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_124_124_6 : ColCert where
  rK := ⟨124, by decide⟩
  rH := ⟨124, by decide⟩
  m := 5
  T1 := T124_124
  T2 := Q2.T124_124_2
  h1 := (1,1,1,1,0)
  h2 := (1,1,1,1,3)
  D := [[1, 1, 4, 4], [1, 1, 4, 3], [1, 1, 4, 2], [1, 1, 4, 1], [1, 1, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_124_124_7 : ColCert where
  rK := ⟨124, by decide⟩
  rH := ⟨124, by decide⟩
  m := 5
  T1 := T124_124
  T2 := Q2.T124_124_2
  h1 := (1,2,3,1,0)
  h2 := (1,2,3,1,4)
  D := [[1, 2, 3, 3], [1, 2, 3, 1], [1, 2, 3, 4], [1, 2, 3, 2], [1, 2, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_124_124_8 : ColCert where
  rK := ⟨124, by decide⟩
  rH := ⟨124, by decide⟩
  m := 5
  T1 := T124_124
  T2 := Q2.T124_124_2
  h1 := (1,3,0,1,2)
  h2 := (1,3,0,1,2)
  D := [[1, 3, 2, 2], [1, 3, 2, 4], [1, 3, 2, 1], [1, 3, 2, 3], [1, 3, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_124_124_9 : ColCert where
  rK := ⟨124, by decide⟩
  rH := ⟨124, by decide⟩
  m := 5
  T1 := T124_124
  T2 := Q2.T124_124_2
  h1 := (1,4,2,1,1)
  h2 := (1,4,2,1,2)
  D := [[1, 4, 1, 1], [1, 4, 1, 2], [1, 4, 1, 3], [1, 4, 1, 4], [1, 4, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_124_124_10 : ColCert where
  rK := ⟨124, by decide⟩
  rH := ⟨124, by decide⟩
  m := 5
  T1 := T124_124
  T2 := Q2.T124_124_2
  h1 := (2,0,3,2,0)
  h2 := (2,0,3,2,4)
  D := [[2, 0, 0, 0], [2, 0, 0, 0], [2, 0, 0, 0], [2, 0, 0, 0], [2, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_124_124_11 : ColCert where
  rK := ⟨124, by decide⟩
  rH := ⟨124, by decide⟩
  m := 5
  T1 := T124_124
  T2 := Q2.T124_124_2
  h1 := (2,1,0,2,2)
  h2 := (2,1,0,2,2)
  D := [[2, 1, 3, 0], [2, 1, 3, 4], [2, 1, 3, 3], [2, 1, 3, 2], [2, 1, 3, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_124_124_12 : ColCert where
  rK := ⟨124, by decide⟩
  rH := ⟨124, by decide⟩
  m := 5
  T1 := T124_124
  T2 := Q2.T124_124_2
  h1 := (2,2,2,2,1)
  h2 := (2,2,2,2,2)
  D := [[2, 2, 1, 0], [2, 2, 1, 3], [2, 2, 1, 1], [2, 2, 1, 4], [2, 2, 1, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_124_124_13 : ColCert where
  rK := ⟨124, by decide⟩
  rH := ⟨124, by decide⟩
  m := 5
  T1 := T124_124
  T2 := Q2.T124_124_2
  h1 := (2,3,4,2,2)
  h2 := (2,3,4,2,4)
  D := [[2, 3, 4, 0], [2, 3, 4, 2], [2, 3, 4, 4], [2, 3, 4, 1], [2, 3, 4, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_124_124_14 : ColCert where
  rK := ⟨124, by decide⟩
  rH := ⟨124, by decide⟩
  m := 5
  T1 := T124_124
  T2 := Q2.T124_124_2
  h1 := (2,4,1,2,0)
  h2 := (2,4,1,2,3)
  D := [[2, 4, 2, 0], [2, 4, 2, 1], [2, 4, 2, 2], [2, 4, 2, 3], [2, 4, 2, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_124_124_15 : ColCert where
  rK := ⟨124, by decide⟩
  rH := ⟨124, by decide⟩
  m := 5
  T1 := T124_124
  T2 := Q2.T124_124_2
  h1 := (3,0,2,3,4)
  h2 := (3,0,2,3,0)
  D := [[3, 0, 0, 0], [3, 0, 0, 0], [3, 0, 0, 0], [3, 0, 0, 0], [3, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_124_124_16 : ColCert where
  rK := ⟨124, by decide⟩
  rH := ⟨124, by decide⟩
  m := 5
  T1 := T124_124
  T2 := Q2.T124_124_2
  h1 := (3,1,4,3,0)
  h2 := (3,1,4,3,2)
  D := [[3, 1, 2, 2], [3, 1, 2, 1], [3, 1, 2, 0], [3, 1, 2, 4], [3, 1, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_124_124_17 : ColCert where
  rK := ⟨124, by decide⟩
  rH := ⟨124, by decide⟩
  m := 5
  T1 := T124_124
  T2 := Q2.T124_124_2
  h1 := (3,2,1,3,3)
  h2 := (3,2,1,3,1)
  D := [[3, 2, 4, 4], [3, 2, 4, 2], [3, 2, 4, 0], [3, 2, 4, 3], [3, 2, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_124_124_18 : ColCert where
  rK := ⟨124, by decide⟩
  rH := ⟨124, by decide⟩
  m := 5
  T1 := T124_124
  T2 := Q2.T124_124_2
  h1 := (3,3,3,3,3)
  h2 := (3,3,3,3,2)
  D := [[3, 3, 1, 1], [3, 3, 1, 3], [3, 3, 1, 0], [3, 3, 1, 2], [3, 3, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_124_124_19 : ColCert where
  rK := ⟨124, by decide⟩
  rH := ⟨124, by decide⟩
  m := 5
  T1 := T124_124
  T2 := Q2.T124_124_2
  h1 := (3,4,0,3,0)
  h2 := (3,4,0,3,0)
  D := [[3, 4, 3, 3], [3, 4, 3, 4], [3, 4, 3, 0], [3, 4, 3, 1], [3, 4, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_124_124_20 : ColCert where
  rK := ⟨124, by decide⟩
  rH := ⟨124, by decide⟩
  m := 5
  T1 := T124_124
  T2 := Q2.T124_124_2
  h1 := (4,0,1,4,4)
  h2 := (4,0,1,4,2)
  D := [[4, 0, 0, 0], [4, 0, 0, 0], [4, 0, 0, 0], [4, 0, 0, 0], [4, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_124_124_21 : ColCert where
  rK := ⟨124, by decide⟩
  rH := ⟨124, by decide⟩
  m := 5
  T1 := T124_124
  T2 := Q2.T124_124_2
  h1 := (4,1,3,4,4)
  h2 := (4,1,3,4,3)
  D := [[4, 1, 1, 0], [4, 1, 1, 4], [4, 1, 1, 3], [4, 1, 1, 2], [4, 1, 1, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_124_124_22 : ColCert where
  rK := ⟨124, by decide⟩
  rH := ⟨124, by decide⟩
  m := 5
  T1 := T124_124
  T2 := Q2.T124_124_2
  h1 := (4,2,0,4,1)
  h2 := (4,2,0,4,1)
  D := [[4, 2, 2, 0], [4, 2, 2, 3], [4, 2, 2, 1], [4, 2, 2, 4], [4, 2, 2, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_124_124_23 : ColCert where
  rK := ⟨124, by decide⟩
  rH := ⟨124, by decide⟩
  m := 5
  T1 := T124_124
  T2 := Q2.T124_124_2
  h1 := (4,3,2,4,0)
  h2 := (4,3,2,4,1)
  D := [[4, 3, 3, 0], [4, 3, 3, 2], [4, 3, 3, 4], [4, 3, 3, 1], [4, 3, 3, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_124_124_24 : ColCert where
  rK := ⟨124, by decide⟩
  rH := ⟨124, by decide⟩
  m := 5
  T1 := T124_124
  T2 := Q2.T124_124_2
  h1 := (4,4,4,4,1)
  h2 := (4,4,4,4,3)
  D := [[4, 4, 4, 0], [4, 4, 4, 1], [4, 4, 4, 2], [4, 4, 4, 3], [4, 4, 4, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_125_0_0 : ColCert where
  rK := ⟨125, by decide⟩
  rH := ⟨0, by decide⟩
  m := 5
  T1 := T125_0
  T2 := Q2.T125_0_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_125_2_0 : ColCert where
  rK := ⟨125, by decide⟩
  rH := ⟨2, by decide⟩
  m := 5
  T1 := T125_2
  T2 := Q2.T125_2_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_125_2_1 : ColCert where
  rK := ⟨125, by decide⟩
  rH := ⟨2, by decide⟩
  m := 5
  T1 := T125_2
  T2 := Q2.T125_2_2
  h1 := (1,0,4,1,0)
  h2 := (1,0,4,1,0)
  D := [[1, 0, 1, 3], [1, 0, 1, 3], [1, 0, 1, 3], [1, 0, 1, 3], [1, 0, 1, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_125_2_2 : ColCert where
  rK := ⟨125, by decide⟩
  rH := ⟨2, by decide⟩
  m := 5
  T1 := T125_2
  T2 := Q2.T125_2_2
  h1 := (2,0,3,2,1)
  h2 := (2,0,3,2,1)
  D := [[2, 0, 2, 0], [2, 0, 2, 0], [2, 0, 2, 0], [2, 0, 2, 0], [2, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

end LeanDring.P5Presentation
