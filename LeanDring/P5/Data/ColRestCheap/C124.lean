/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.Twin1.ColCert
import LeanDring.P5.Data.EntryK.C044

/-!
# Species-table cell data, stage 2 — twin-coincident columns (cheap tier)

Per-column certified exponent-vector data (`ColCert`/`ColCertDiv`) with kernel
`decide` bindings. Emitted; the embedded lists are what the kernel certifies.
rest tier, chunk 123: 60 columns.
-/

-- machine-emitted data: silence style linters (generated long lines, file-level options)
set_option linter.style.longLine false

namespace LeanDring.P5Presentation

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

def colCert_147_90_2 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨90, by decide⟩
  m := 1
  T1 := T147_90
  T2 := Q2.T147_90_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_90_3 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨90, by decide⟩
  m := 1
  T1 := T147_90
  T2 := Q2.T147_90_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_90_4 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨90, by decide⟩
  m := 1
  T1 := T147_90
  T2 := Q2.T147_90_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_90_5 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨90, by decide⟩
  m := 1
  T1 := T147_90
  T2 := Q2.T147_90_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_90_10 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨90, by decide⟩
  m := 1
  T1 := T147_90
  T2 := Q2.T147_90_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_90_15 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨90, by decide⟩
  m := 1
  T1 := T147_90
  T2 := Q2.T147_90_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_90_20 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨90, by decide⟩
  m := 1
  T1 := T147_90
  T2 := Q2.T147_90_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_90_25 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨90, by decide⟩
  m := 1
  T1 := T147_90
  T2 := Q2.T147_90_2
  h1 := (0,1,4,0,0)
  h2 := (0,1,4,0,0)
  D := [[0, 1, 4, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_90_50 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨90, by decide⟩
  m := 1
  T1 := T147_90
  T2 := Q2.T147_90_2
  h1 := (0,2,3,0,4)
  h2 := (0,2,3,0,4)
  D := [[0, 2, 3, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_90_75 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨90, by decide⟩
  m := 1
  T1 := T147_90
  T2 := Q2.T147_90_2
  h1 := (0,3,2,0,2)
  h2 := (0,3,2,0,2)
  D := [[0, 3, 2, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_90_100 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨90, by decide⟩
  m := 1
  T1 := T147_90
  T2 := Q2.T147_90_2
  h1 := (0,4,1,0,4)
  h2 := (0,4,1,0,4)
  D := [[0, 4, 1, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_91_0 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨91, by decide⟩
  m := 1
  T1 := T147_91
  T2 := Q2.T147_91_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_91_1 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨91, by decide⟩
  m := 1
  T1 := T147_91
  T2 := Q2.T147_91_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_91_2 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨91, by decide⟩
  m := 1
  T1 := T147_91
  T2 := Q2.T147_91_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_91_3 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨91, by decide⟩
  m := 1
  T1 := T147_91
  T2 := Q2.T147_91_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_91_4 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨91, by decide⟩
  m := 1
  T1 := T147_91
  T2 := Q2.T147_91_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_91_5 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨91, by decide⟩
  m := 1
  T1 := T147_91
  T2 := Q2.T147_91_2
  h1 := (1,4,1,4,4)
  h2 := (1,4,1,4,4)
  D := [[1, 4, 1, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_92_0 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨92, by decide⟩
  m := 1
  T1 := T147_92
  T2 := Q2.T147_92_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_92_1 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨92, by decide⟩
  m := 1
  T1 := T147_92
  T2 := Q2.T147_92_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_92_2 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨92, by decide⟩
  m := 1
  T1 := T147_92
  T2 := Q2.T147_92_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_92_3 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨92, by decide⟩
  m := 1
  T1 := T147_92
  T2 := Q2.T147_92_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_92_4 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨92, by decide⟩
  m := 1
  T1 := T147_92
  T2 := Q2.T147_92_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_92_5 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨92, by decide⟩
  m := 1
  T1 := T147_92
  T2 := Q2.T147_92_2
  h1 := (1,2,3,3,2)
  h2 := (1,2,3,3,2)
  D := [[1, 2, 3, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_92_10 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨92, by decide⟩
  m := 1
  T1 := T147_92
  T2 := Q2.T147_92_2
  h1 := (2,4,1,3,3)
  h2 := (2,4,1,3,3)
  D := [[2, 4, 1, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_93_0 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨93, by decide⟩
  m := 1
  T1 := T147_93
  T2 := Q2.T147_93_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_93_1 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨93, by decide⟩
  m := 1
  T1 := T147_93
  T2 := Q2.T147_93_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_93_2 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨93, by decide⟩
  m := 1
  T1 := T147_93
  T2 := Q2.T147_93_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_93_3 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨93, by decide⟩
  m := 1
  T1 := T147_93
  T2 := Q2.T147_93_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_93_4 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨93, by decide⟩
  m := 1
  T1 := T147_93
  T2 := Q2.T147_93_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_93_5 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨93, by decide⟩
  m := 1
  T1 := T147_93
  T2 := Q2.T147_93_2
  h1 := (1,3,2,1,4)
  h2 := (1,3,2,1,4)
  D := [[1, 3, 2, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_94_0 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨94, by decide⟩
  m := 1
  T1 := T147_94
  T2 := Q2.T147_94_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_94_1 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨94, by decide⟩
  m := 1
  T1 := T147_94
  T2 := Q2.T147_94_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_94_2 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨94, by decide⟩
  m := 1
  T1 := T147_94
  T2 := Q2.T147_94_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_94_3 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨94, by decide⟩
  m := 1
  T1 := T147_94
  T2 := Q2.T147_94_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_94_4 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨94, by decide⟩
  m := 1
  T1 := T147_94
  T2 := Q2.T147_94_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_94_5 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨94, by decide⟩
  m := 1
  T1 := T147_94
  T2 := Q2.T147_94_2
  h1 := (1,1,4,0,0)
  h2 := (1,1,4,0,0)
  D := [[1, 1, 4, 4, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_94_10 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨94, by decide⟩
  m := 1
  T1 := T147_94
  T2 := Q2.T147_94_2
  h1 := (2,2,3,1,4)
  h2 := (2,2,3,1,4)
  D := [[2, 2, 3, 2, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_94_15 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨94, by decide⟩
  m := 1
  T1 := T147_94
  T2 := Q2.T147_94_2
  h1 := (3,3,2,3,3)
  h2 := (3,3,2,3,3)
  D := [[3, 3, 2, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_94_20 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨94, by decide⟩
  m := 1
  T1 := T147_94
  T2 := Q2.T147_94_2
  h1 := (4,4,1,1,3)
  h2 := (4,4,1,1,3)
  D := [[4, 4, 1, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_95_0 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨95, by decide⟩
  m := 1
  T1 := T147_95
  T2 := Q2.T147_95_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_95_1 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨95, by decide⟩
  m := 1
  T1 := T147_95
  T2 := Q2.T147_95_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_95_2 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨95, by decide⟩
  m := 1
  T1 := T147_95
  T2 := Q2.T147_95_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_95_3 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨95, by decide⟩
  m := 1
  T1 := T147_95
  T2 := Q2.T147_95_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_95_4 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨95, by decide⟩
  m := 1
  T1 := T147_95
  T2 := Q2.T147_95_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_95_5 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨95, by decide⟩
  m := 1
  T1 := T147_95
  T2 := Q2.T147_95_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_95_10 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨95, by decide⟩
  m := 1
  T1 := T147_95
  T2 := Q2.T147_95_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_95_15 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨95, by decide⟩
  m := 1
  T1 := T147_95
  T2 := Q2.T147_95_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_95_20 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨95, by decide⟩
  m := 1
  T1 := T147_95
  T2 := Q2.T147_95_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_95_25 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨95, by decide⟩
  m := 1
  T1 := T147_95
  T2 := Q2.T147_95_2
  h1 := (0,1,2,0,0)
  h2 := (0,1,2,0,0)
  D := [[0, 1, 2, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_95_50 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨95, by decide⟩
  m := 1
  T1 := T147_95
  T2 := Q2.T147_95_2
  h1 := (0,2,4,0,2)
  h2 := (0,2,4,0,2)
  D := [[0, 2, 4, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_95_75 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨95, by decide⟩
  m := 1
  T1 := T147_95
  T2 := Q2.T147_95_2
  h1 := (0,3,1,0,1)
  h2 := (0,3,1,0,1)
  D := [[0, 3, 1, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_95_100 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨95, by decide⟩
  m := 1
  T1 := T147_95
  T2 := Q2.T147_95_2
  h1 := (0,4,3,0,2)
  h2 := (0,4,3,0,2)
  D := [[0, 4, 3, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_96_0 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨96, by decide⟩
  m := 1
  T1 := T147_96
  T2 := Q2.T147_96_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_96_1 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨96, by decide⟩
  m := 1
  T1 := T147_96
  T2 := Q2.T147_96_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_96_2 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨96, by decide⟩
  m := 1
  T1 := T147_96
  T2 := Q2.T147_96_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_96_3 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨96, by decide⟩
  m := 1
  T1 := T147_96
  T2 := Q2.T147_96_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_96_4 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨96, by decide⟩
  m := 1
  T1 := T147_96
  T2 := Q2.T147_96_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_96_5 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨96, by decide⟩
  m := 1
  T1 := T147_96
  T2 := Q2.T147_96_2
  h1 := (1,4,3,4,2)
  h2 := (1,4,3,4,2)
  D := [[1, 4, 3, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_97_0 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨97, by decide⟩
  m := 1
  T1 := T147_97
  T2 := Q2.T147_97_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_97_1 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨97, by decide⟩
  m := 1
  T1 := T147_97
  T2 := Q2.T147_97_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

end LeanDring.P5Presentation
