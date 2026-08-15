/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.Twin1.ColCert
import LeanDring.P5.Data.EntryK.C029

/-!
# Species-table cell data, stage 2 — twin-coincident columns (cheap tier)

Per-column certified exponent-vector data (`ColCert`/`ColCertDiv`) with kernel
`decide` bindings. Emitted; the embedded lists are what the kernel certifies.
rest tier, chunk 44: 60 columns.
-/

-- machine-emitted data: silence style linters (generated long lines, file-level options)
set_option linter.style.longLine false

namespace LeanDring.P5Presentation

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

def colCert_120_80_25 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨80, by decide⟩
  m := 5
  T1 := T120_80
  T2 := Q2.T120_80_2
  h1 := (0,0,1,0,0)
  h2 := (0,0,1,0,0)
  D := [[0, 1, 0, 1], [0, 1, 0, 2], [0, 1, 0, 3], [0, 1, 0, 4], [0, 1, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_80_30 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨80, by decide⟩
  m := 5
  T1 := T120_80
  T2 := Q2.T120_80_2
  h1 := (0,0,1,1,0)
  h2 := (0,0,1,1,0)
  D := [[0, 1, 1, 1], [0, 1, 1, 2], [0, 1, 1, 3], [0, 1, 1, 4], [0, 1, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_80_35 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨80, by decide⟩
  m := 5
  T1 := T120_80
  T2 := Q2.T120_80_2
  h1 := (0,0,1,2,0)
  h2 := (0,0,1,2,0)
  D := [[0, 1, 2, 1], [0, 1, 2, 2], [0, 1, 2, 3], [0, 1, 2, 4], [0, 1, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_80_40 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨80, by decide⟩
  m := 5
  T1 := T120_80
  T2 := Q2.T120_80_2
  h1 := (0,0,1,3,0)
  h2 := (0,0,1,3,0)
  D := [[0, 1, 3, 1], [0, 1, 3, 2], [0, 1, 3, 3], [0, 1, 3, 4], [0, 1, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_80_45 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨80, by decide⟩
  m := 5
  T1 := T120_80
  T2 := Q2.T120_80_2
  h1 := (0,0,1,4,0)
  h2 := (0,0,1,4,0)
  D := [[0, 1, 4, 1], [0, 1, 4, 2], [0, 1, 4, 3], [0, 1, 4, 4], [0, 1, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_80_50 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨80, by decide⟩
  m := 5
  T1 := T120_80
  T2 := Q2.T120_80_2
  h1 := (0,0,2,0,0)
  h2 := (0,0,2,0,0)
  D := [[0, 2, 0, 2], [0, 2, 0, 4], [0, 2, 0, 1], [0, 2, 0, 3], [0, 2, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_80_55 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨80, by decide⟩
  m := 5
  T1 := T120_80
  T2 := Q2.T120_80_2
  h1 := (0,0,2,1,0)
  h2 := (0,0,2,1,0)
  D := [[0, 2, 1, 2], [0, 2, 1, 4], [0, 2, 1, 1], [0, 2, 1, 3], [0, 2, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_80_60 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨80, by decide⟩
  m := 5
  T1 := T120_80
  T2 := Q2.T120_80_2
  h1 := (0,0,2,2,0)
  h2 := (0,0,2,2,0)
  D := [[0, 2, 2, 2], [0, 2, 2, 4], [0, 2, 2, 1], [0, 2, 2, 3], [0, 2, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_80_65 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨80, by decide⟩
  m := 5
  T1 := T120_80
  T2 := Q2.T120_80_2
  h1 := (0,0,2,3,0)
  h2 := (0,0,2,3,0)
  D := [[0, 2, 3, 2], [0, 2, 3, 4], [0, 2, 3, 1], [0, 2, 3, 3], [0, 2, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_80_70 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨80, by decide⟩
  m := 5
  T1 := T120_80
  T2 := Q2.T120_80_2
  h1 := (0,0,2,4,0)
  h2 := (0,0,2,4,0)
  D := [[0, 2, 4, 2], [0, 2, 4, 4], [0, 2, 4, 1], [0, 2, 4, 3], [0, 2, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_80_75 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨80, by decide⟩
  m := 5
  T1 := T120_80
  T2 := Q2.T120_80_2
  h1 := (0,0,3,0,0)
  h2 := (0,0,3,0,0)
  D := [[0, 3, 0, 3], [0, 3, 0, 1], [0, 3, 0, 4], [0, 3, 0, 2], [0, 3, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_80_80 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨80, by decide⟩
  m := 5
  T1 := T120_80
  T2 := Q2.T120_80_2
  h1 := (0,0,3,1,0)
  h2 := (0,0,3,1,0)
  D := [[0, 3, 1, 3], [0, 3, 1, 1], [0, 3, 1, 4], [0, 3, 1, 2], [0, 3, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_80_85 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨80, by decide⟩
  m := 5
  T1 := T120_80
  T2 := Q2.T120_80_2
  h1 := (0,0,3,2,0)
  h2 := (0,0,3,2,0)
  D := [[0, 3, 2, 3], [0, 3, 2, 1], [0, 3, 2, 4], [0, 3, 2, 2], [0, 3, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_80_90 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨80, by decide⟩
  m := 5
  T1 := T120_80
  T2 := Q2.T120_80_2
  h1 := (0,0,3,3,0)
  h2 := (0,0,3,3,0)
  D := [[0, 3, 3, 3], [0, 3, 3, 1], [0, 3, 3, 4], [0, 3, 3, 2], [0, 3, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_80_95 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨80, by decide⟩
  m := 5
  T1 := T120_80
  T2 := Q2.T120_80_2
  h1 := (0,0,3,4,0)
  h2 := (0,0,3,4,0)
  D := [[0, 3, 4, 3], [0, 3, 4, 1], [0, 3, 4, 4], [0, 3, 4, 2], [0, 3, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_80_100 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨80, by decide⟩
  m := 5
  T1 := T120_80
  T2 := Q2.T120_80_2
  h1 := (0,0,4,0,0)
  h2 := (0,0,4,0,0)
  D := [[0, 4, 0, 4], [0, 4, 0, 3], [0, 4, 0, 2], [0, 4, 0, 1], [0, 4, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_80_105 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨80, by decide⟩
  m := 5
  T1 := T120_80
  T2 := Q2.T120_80_2
  h1 := (0,0,4,1,0)
  h2 := (0,0,4,1,0)
  D := [[0, 4, 1, 4], [0, 4, 1, 3], [0, 4, 1, 2], [0, 4, 1, 1], [0, 4, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_80_110 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨80, by decide⟩
  m := 5
  T1 := T120_80
  T2 := Q2.T120_80_2
  h1 := (0,0,4,2,0)
  h2 := (0,0,4,2,0)
  D := [[0, 4, 2, 4], [0, 4, 2, 3], [0, 4, 2, 2], [0, 4, 2, 1], [0, 4, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_80_115 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨80, by decide⟩
  m := 5
  T1 := T120_80
  T2 := Q2.T120_80_2
  h1 := (0,0,4,3,0)
  h2 := (0,0,4,3,0)
  D := [[0, 4, 3, 4], [0, 4, 3, 3], [0, 4, 3, 2], [0, 4, 3, 1], [0, 4, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_80_120 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨80, by decide⟩
  m := 5
  T1 := T120_80
  T2 := Q2.T120_80_2
  h1 := (0,0,4,4,0)
  h2 := (0,0,4,4,0)
  D := [[0, 4, 4, 4], [0, 4, 4, 3], [0, 4, 4, 2], [0, 4, 4, 1], [0, 4, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_94_0 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨94, by decide⟩
  m := 5
  T1 := T120_94
  T2 := Q2.T120_94_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_94_1 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨94, by decide⟩
  m := 5
  T1 := T120_94
  T2 := Q2.T120_94_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_94_2 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨94, by decide⟩
  m := 5
  T1 := T120_94
  T2 := Q2.T120_94_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_94_3 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨94, by decide⟩
  m := 5
  T1 := T120_94
  T2 := Q2.T120_94_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_94_4 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨94, by decide⟩
  m := 5
  T1 := T120_94
  T2 := Q2.T120_94_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_94_5 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨94, by decide⟩
  m := 5
  T1 := T120_94
  T2 := Q2.T120_94_2
  h1 := (1,1,4,0,0)
  h2 := (1,1,4,0,0)
  D := [[1, 4, 4, 1], [1, 4, 3, 1], [1, 4, 2, 1], [1, 4, 1, 1], [1, 4, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_94_10 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨94, by decide⟩
  m := 5
  T1 := T120_94
  T2 := Q2.T120_94_2
  h1 := (2,2,3,1,4)
  h2 := (2,2,3,1,4)
  D := [[2, 3, 3, 4], [2, 3, 1, 0], [2, 3, 4, 1], [2, 3, 2, 2], [2, 3, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_94_15 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨94, by decide⟩
  m := 5
  T1 := T120_94
  T2 := Q2.T120_94_2
  h1 := (3,3,2,3,3)
  h2 := (3,3,2,3,3)
  D := [[3, 2, 2, 4], [3, 2, 4, 2], [3, 2, 1, 0], [3, 2, 3, 3], [3, 2, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_94_20 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨94, by decide⟩
  m := 5
  T1 := T120_94
  T2 := Q2.T120_94_2
  h1 := (4,4,1,1,3)
  h2 := (4,4,1,1,3)
  D := [[4, 1, 1, 1], [4, 1, 2, 2], [4, 1, 3, 3], [4, 1, 4, 4], [4, 1, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_99_0 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨99, by decide⟩
  m := 5
  T1 := T120_99
  T2 := Q2.T120_99_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_99_1 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨99, by decide⟩
  m := 5
  T1 := T120_99
  T2 := Q2.T120_99_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_99_2 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨99, by decide⟩
  m := 5
  T1 := T120_99
  T2 := Q2.T120_99_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_99_3 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨99, by decide⟩
  m := 5
  T1 := T120_99
  T2 := Q2.T120_99_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_99_4 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨99, by decide⟩
  m := 5
  T1 := T120_99
  T2 := Q2.T120_99_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_99_5 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨99, by decide⟩
  m := 5
  T1 := T120_99
  T2 := Q2.T120_99_2
  h1 := (1,1,2,0,0)
  h2 := (1,1,2,0,0)
  D := [[1, 2, 4, 1], [1, 2, 3, 4], [1, 2, 2, 2], [1, 2, 1, 0], [1, 2, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_99_10 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨99, by decide⟩
  m := 5
  T1 := T120_99
  T2 := Q2.T120_99_2
  h1 := (2,2,4,1,2)
  h2 := (2,2,4,1,2)
  D := [[2, 4, 3, 1], [2, 4, 1, 3], [2, 4, 4, 0], [2, 4, 2, 2], [2, 4, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_99_15 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨99, by decide⟩
  m := 5
  T1 := T120_99
  T2 := Q2.T120_99_2
  h1 := (3,3,1,3,2)
  h2 := (3,3,1,3,2)
  D := [[3, 1, 2, 0], [3, 1, 4, 2], [3, 1, 1, 4], [3, 1, 3, 1], [3, 1, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_99_20 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨99, by decide⟩
  m := 5
  T1 := T120_99
  T2 := Q2.T120_99_2
  h1 := (4,4,3,1,1)
  h2 := (4,4,3,1,1)
  D := [[4, 3, 1, 3], [4, 3, 2, 1], [4, 3, 3, 4], [4, 3, 4, 2], [4, 3, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_104_0 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨104, by decide⟩
  m := 5
  T1 := T120_104
  T2 := Q2.T120_104_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_104_1 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨104, by decide⟩
  m := 5
  T1 := T120_104
  T2 := Q2.T120_104_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_104_2 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨104, by decide⟩
  m := 5
  T1 := T120_104
  T2 := Q2.T120_104_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_104_3 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨104, by decide⟩
  m := 5
  T1 := T120_104
  T2 := Q2.T120_104_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_104_4 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨104, by decide⟩
  m := 5
  T1 := T120_104
  T2 := Q2.T120_104_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_104_5 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨104, by decide⟩
  m := 5
  T1 := T120_104
  T2 := Q2.T120_104_2
  h1 := (1,1,3,0,0)
  h2 := (1,1,3,0,0)
  D := [[1, 3, 4, 1], [1, 3, 3, 0], [1, 3, 2, 4], [1, 3, 1, 3], [1, 3, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_104_10 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨104, by decide⟩
  m := 5
  T1 := T120_104
  T2 := Q2.T120_104_2
  h1 := (2,2,1,1,3)
  h2 := (2,2,1,1,3)
  D := [[2, 1, 3, 0], [2, 1, 1, 4], [2, 1, 4, 3], [2, 1, 2, 2], [2, 1, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_104_15 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨104, by decide⟩
  m := 5
  T1 := T120_104
  T2 := Q2.T120_104_2
  h1 := (3,3,4,3,0)
  h2 := (3,3,4,3,0)
  D := [[3, 4, 2, 2], [3, 4, 4, 2], [3, 4, 1, 2], [3, 4, 3, 2], [3, 4, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_104_20 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨104, by decide⟩
  m := 5
  T1 := T120_104
  T2 := Q2.T120_104_2
  h1 := (4,4,2,1,2)
  h2 := (4,4,2,1,2)
  D := [[4, 2, 1, 2], [4, 2, 2, 4], [4, 2, 3, 1], [4, 2, 4, 3], [4, 2, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_109_0 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨109, by decide⟩
  m := 5
  T1 := T120_109
  T2 := Q2.T120_109_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_109_1 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨109, by decide⟩
  m := 5
  T1 := T120_109
  T2 := Q2.T120_109_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_109_2 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨109, by decide⟩
  m := 5
  T1 := T120_109
  T2 := Q2.T120_109_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_109_3 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨109, by decide⟩
  m := 5
  T1 := T120_109
  T2 := Q2.T120_109_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_109_4 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨109, by decide⟩
  m := 5
  T1 := T120_109
  T2 := Q2.T120_109_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_109_5 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨109, by decide⟩
  m := 5
  T1 := T120_109
  T2 := Q2.T120_109_2
  h1 := (1,1,1,0,0)
  h2 := (1,1,1,0,0)
  D := [[1, 1, 4, 1], [1, 1, 3, 3], [1, 1, 2, 0], [1, 1, 1, 2], [1, 1, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_109_10 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨109, by decide⟩
  m := 5
  T1 := T120_109
  T2 := Q2.T120_109_2
  h1 := (2,2,2,1,1)
  h2 := (2,2,2,1,1)
  D := [[2, 2, 3, 2], [2, 2, 1, 2], [2, 2, 4, 2], [2, 2, 2, 2], [2, 2, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_109_15 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨109, by decide⟩
  m := 5
  T1 := T120_109
  T2 := Q2.T120_109_2
  h1 := (3,3,3,3,4)
  h2 := (3,3,3,3,4)
  D := [[3, 3, 2, 3], [3, 3, 4, 2], [3, 3, 1, 1], [3, 3, 3, 0], [3, 3, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_109_20 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨109, by decide⟩
  m := 5
  T1 := T120_109
  T2 := Q2.T120_109_2
  h1 := (4,4,4,1,0)
  h2 := (4,4,4,1,0)
  D := [[4, 4, 1, 4], [4, 4, 2, 3], [4, 4, 3, 2], [4, 4, 4, 1], [4, 4, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_114_0 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨114, by decide⟩
  m := 5
  T1 := T120_114
  T2 := Q2.T120_114_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_114_1 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨114, by decide⟩
  m := 5
  T1 := T120_114
  T2 := Q2.T120_114_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_114_2 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨114, by decide⟩
  m := 5
  T1 := T120_114
  T2 := Q2.T120_114_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_114_3 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨114, by decide⟩
  m := 5
  T1 := T120_114
  T2 := Q2.T120_114_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

end LeanDring.P5Presentation
