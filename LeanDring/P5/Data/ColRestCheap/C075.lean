/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.Twin1.ColCert
import LeanDring.P5.Data.EntryK.C036

/-!
# Species-table cell data, stage 2 — twin-coincident columns (cheap tier)

Per-column certified exponent-vector data (`ColCert`/`ColCertDiv`) with kernel
`decide` bindings. Emitted; the embedded lists are what the kernel certifies.
rest tier, chunk 74: 60 columns.
-/

-- machine-emitted data: silence style linters (generated long lines, file-level options)
set_option linter.style.longLine false

namespace LeanDring.P5Presentation

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

def colCert_134_90_1 : ColCert where
  rK := ⟨134, by decide⟩
  rH := ⟨90, by decide⟩
  m := 5
  T1 := T134_90
  T2 := Q2.T134_90_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_134_90_2 : ColCert where
  rK := ⟨134, by decide⟩
  rH := ⟨90, by decide⟩
  m := 5
  T1 := T134_90
  T2 := Q2.T134_90_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_134_90_3 : ColCert where
  rK := ⟨134, by decide⟩
  rH := ⟨90, by decide⟩
  m := 5
  T1 := T134_90
  T2 := Q2.T134_90_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_134_90_4 : ColCert where
  rK := ⟨134, by decide⟩
  rH := ⟨90, by decide⟩
  m := 5
  T1 := T134_90
  T2 := Q2.T134_90_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_134_90_5 : ColCert where
  rK := ⟨134, by decide⟩
  rH := ⟨90, by decide⟩
  m := 5
  T1 := T134_90
  T2 := Q2.T134_90_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_134_90_10 : ColCert where
  rK := ⟨134, by decide⟩
  rH := ⟨90, by decide⟩
  m := 5
  T1 := T134_90
  T2 := Q2.T134_90_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_134_90_15 : ColCert where
  rK := ⟨134, by decide⟩
  rH := ⟨90, by decide⟩
  m := 5
  T1 := T134_90
  T2 := Q2.T134_90_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_134_90_20 : ColCert where
  rK := ⟨134, by decide⟩
  rH := ⟨90, by decide⟩
  m := 5
  T1 := T134_90
  T2 := Q2.T134_90_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_134_99_0 : ColCert where
  rK := ⟨134, by decide⟩
  rH := ⟨99, by decide⟩
  m := 5
  T1 := T134_99
  T2 := Q2.T134_99_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_134_99_1 : ColCert where
  rK := ⟨134, by decide⟩
  rH := ⟨99, by decide⟩
  m := 5
  T1 := T134_99
  T2 := Q2.T134_99_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_134_99_2 : ColCert where
  rK := ⟨134, by decide⟩
  rH := ⟨99, by decide⟩
  m := 5
  T1 := T134_99
  T2 := Q2.T134_99_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_134_99_3 : ColCert where
  rK := ⟨134, by decide⟩
  rH := ⟨99, by decide⟩
  m := 5
  T1 := T134_99
  T2 := Q2.T134_99_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_134_99_4 : ColCert where
  rK := ⟨134, by decide⟩
  rH := ⟨99, by decide⟩
  m := 5
  T1 := T134_99
  T2 := Q2.T134_99_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_134_102_0 : ColCert where
  rK := ⟨134, by decide⟩
  rH := ⟨102, by decide⟩
  m := 5
  T1 := T134_102
  T2 := Q2.T134_102_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_134_102_1 : ColCert where
  rK := ⟨134, by decide⟩
  rH := ⟨102, by decide⟩
  m := 5
  T1 := T134_102
  T2 := Q2.T134_102_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_134_102_2 : ColCert where
  rK := ⟨134, by decide⟩
  rH := ⟨102, by decide⟩
  m := 5
  T1 := T134_102
  T2 := Q2.T134_102_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_134_102_3 : ColCert where
  rK := ⟨134, by decide⟩
  rH := ⟨102, by decide⟩
  m := 5
  T1 := T134_102
  T2 := Q2.T134_102_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_134_102_4 : ColCert where
  rK := ⟨134, by decide⟩
  rH := ⟨102, by decide⟩
  m := 5
  T1 := T134_102
  T2 := Q2.T134_102_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_134_102_15 : ColCert where
  rK := ⟨134, by decide⟩
  rH := ⟨102, by decide⟩
  m := 5
  T1 := T134_102
  T2 := Q2.T134_102_2
  h1 := (3,1,3,0,1)
  h2 := (3,1,3,0,2)
  D := [[3, 1, 4, 4], [3, 1, 4, 3], [3, 1, 4, 2], [3, 1, 4, 1], [3, 1, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_134_106_0 : ColCert where
  rK := ⟨134, by decide⟩
  rH := ⟨106, by decide⟩
  m := 5
  T1 := T134_106
  T2 := Q2.T134_106_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_134_106_1 : ColCert where
  rK := ⟨134, by decide⟩
  rH := ⟨106, by decide⟩
  m := 5
  T1 := T134_106
  T2 := Q2.T134_106_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_134_106_2 : ColCert where
  rK := ⟨134, by decide⟩
  rH := ⟨106, by decide⟩
  m := 5
  T1 := T134_106
  T2 := Q2.T134_106_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_134_106_3 : ColCert where
  rK := ⟨134, by decide⟩
  rH := ⟨106, by decide⟩
  m := 5
  T1 := T134_106
  T2 := Q2.T134_106_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_134_106_4 : ColCert where
  rK := ⟨134, by decide⟩
  rH := ⟨106, by decide⟩
  m := 5
  T1 := T134_106
  T2 := Q2.T134_106_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_134_106_10 : ColCert where
  rK := ⟨134, by decide⟩
  rH := ⟨106, by decide⟩
  m := 5
  T1 := T134_106
  T2 := Q2.T134_106_2
  h1 := (2,3,3,2,3)
  h2 := (2,3,3,2,4)
  D := [[2, 3, 4, 2], [2, 3, 4, 4], [2, 3, 4, 1], [2, 3, 4, 3], [2, 3, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_134_113_0 : ColCert where
  rK := ⟨134, by decide⟩
  rH := ⟨113, by decide⟩
  m := 5
  T1 := T134_113
  T2 := Q2.T134_113_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_134_113_1 : ColCert where
  rK := ⟨134, by decide⟩
  rH := ⟨113, by decide⟩
  m := 5
  T1 := T134_113
  T2 := Q2.T134_113_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_134_113_2 : ColCert where
  rK := ⟨134, by decide⟩
  rH := ⟨113, by decide⟩
  m := 5
  T1 := T134_113
  T2 := Q2.T134_113_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_134_113_3 : ColCert where
  rK := ⟨134, by decide⟩
  rH := ⟨113, by decide⟩
  m := 5
  T1 := T134_113
  T2 := Q2.T134_113_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_134_113_4 : ColCert where
  rK := ⟨134, by decide⟩
  rH := ⟨113, by decide⟩
  m := 5
  T1 := T134_113
  T2 := Q2.T134_113_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_134_113_5 : ColCert where
  rK := ⟨134, by decide⟩
  rH := ⟨113, by decide⟩
  m := 5
  T1 := T134_113
  T2 := Q2.T134_113_2
  h1 := (1,3,0,1,2)
  h2 := (1,3,0,1,2)
  D := [[1, 3, 2, 1], [1, 3, 2, 3], [1, 3, 2, 0], [1, 3, 2, 2], [1, 3, 2, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_134_134_0 : ColCert where
  rK := ⟨134, by decide⟩
  rH := ⟨134, by decide⟩
  m := 5
  T1 := T134_134
  T2 := Q2.T134_134_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_134_134_1 : ColCert where
  rK := ⟨134, by decide⟩
  rH := ⟨134, by decide⟩
  m := 5
  T1 := T134_134
  T2 := Q2.T134_134_2
  h1 := (0,1,4,0,2)
  h2 := (0,1,4,0,0)
  D := [[0, 1, 0, 3], [0, 1, 0, 2], [0, 1, 0, 1], [0, 1, 0, 0], [0, 1, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_134_134_2 : ColCert where
  rK := ⟨134, by decide⟩
  rH := ⟨134, by decide⟩
  m := 5
  T1 := T134_134
  T2 := Q2.T134_134_2
  h1 := (0,2,3,0,3)
  h2 := (0,2,3,0,4)
  D := [[0, 2, 0, 1], [0, 2, 0, 4], [0, 2, 0, 2], [0, 2, 0, 0], [0, 2, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_134_134_3 : ColCert where
  rK := ⟨134, by decide⟩
  rH := ⟨134, by decide⟩
  m := 5
  T1 := T134_134
  T2 := Q2.T134_134_2
  h1 := (0,3,2,0,3)
  h2 := (0,3,2,0,2)
  D := [[0, 3, 0, 4], [0, 3, 0, 1], [0, 3, 0, 3], [0, 3, 0, 0], [0, 3, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_134_134_4 : ColCert where
  rK := ⟨134, by decide⟩
  rH := ⟨134, by decide⟩
  m := 5
  T1 := T134_134
  T2 := Q2.T134_134_2
  h1 := (0,4,1,0,2)
  h2 := (0,4,1,0,4)
  D := [[0, 4, 0, 2], [0, 4, 0, 3], [0, 4, 0, 4], [0, 4, 0, 0], [0, 4, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_134_134_5 : ColCert where
  rK := ⟨134, by decide⟩
  rH := ⟨134, by decide⟩
  m := 5
  T1 := T134_134
  T2 := Q2.T134_134_2
  h1 := (1,0,3,1,0)
  h2 := (1,0,3,1,1)
  D := [[1, 0, 0, 0], [1, 0, 0, 0], [1, 0, 0, 0], [1, 0, 0, 0], [1, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_134_134_6 : ColCert where
  rK := ⟨134, by decide⟩
  rH := ⟨134, by decide⟩
  m := 5
  T1 := T134_134
  T2 := Q2.T134_134_2
  h1 := (1,1,2,1,0)
  h2 := (1,1,2,1,4)
  D := [[1, 1, 4, 2], [1, 1, 4, 1], [1, 1, 4, 0], [1, 1, 4, 4], [1, 1, 4, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_134_134_7 : ColCert where
  rK := ⟨134, by decide⟩
  rH := ⟨134, by decide⟩
  m := 5
  T1 := T134_134
  T2 := Q2.T134_134_2
  h1 := (1,2,1,1,4)
  h2 := (1,2,1,1,1)
  D := [[1, 2, 3, 4], [1, 2, 3, 2], [1, 2, 3, 0], [1, 2, 3, 3], [1, 2, 3, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_134_134_8 : ColCert where
  rK := ⟨134, by decide⟩
  rH := ⟨134, by decide⟩
  m := 5
  T1 := T134_134
  T2 := Q2.T134_134_2
  h1 := (1,3,0,1,2)
  h2 := (1,3,0,1,2)
  D := [[1, 3, 2, 1], [1, 3, 2, 3], [1, 3, 2, 0], [1, 3, 2, 2], [1, 3, 2, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_134_134_9 : ColCert where
  rK := ⟨134, by decide⟩
  rH := ⟨134, by decide⟩
  m := 5
  T1 := T134_134
  T2 := Q2.T134_134_2
  h1 := (1,4,4,1,4)
  h2 := (1,4,4,1,2)
  D := [[1, 4, 1, 3], [1, 4, 1, 4], [1, 4, 1, 0], [1, 4, 1, 1], [1, 4, 1, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_134_134_10 : ColCert where
  rK := ⟨134, by decide⟩
  rH := ⟨134, by decide⟩
  m := 5
  T1 := T134_134
  T2 := Q2.T134_134_2
  h1 := (2,0,1,2,1)
  h2 := (2,0,1,2,3)
  D := [[2, 0, 0, 0], [2, 0, 0, 0], [2, 0, 0, 0], [2, 0, 0, 0], [2, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_134_134_11 : ColCert where
  rK := ⟨134, by decide⟩
  rH := ⟨134, by decide⟩
  m := 5
  T1 := T134_134
  T2 := Q2.T134_134_2
  h1 := (2,1,0,2,4)
  h2 := (2,1,0,2,4)
  D := [[2, 1, 3, 2], [2, 1, 3, 1], [2, 1, 3, 0], [2, 1, 3, 4], [2, 1, 3, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_134_134_12 : ColCert where
  rK := ⟨134, by decide⟩
  rH := ⟨134, by decide⟩
  m := 5
  T1 := T134_134
  T2 := Q2.T134_134_2
  h1 := (2,2,4,2,1)
  h2 := (2,2,4,2,4)
  D := [[2, 2, 1, 4], [2, 2, 1, 2], [2, 2, 1, 0], [2, 2, 1, 3], [2, 2, 1, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_134_134_13 : ColCert where
  rK := ⟨134, by decide⟩
  rH := ⟨134, by decide⟩
  m := 5
  T1 := T134_134
  T2 := Q2.T134_134_2
  h1 := (2,3,3,2,2)
  h2 := (2,3,3,2,3)
  D := [[2, 3, 4, 1], [2, 3, 4, 3], [2, 3, 4, 0], [2, 3, 4, 2], [2, 3, 4, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_134_134_14 : ColCert where
  rK := ⟨134, by decide⟩
  rH := ⟨134, by decide⟩
  m := 5
  T1 := T134_134
  T2 := Q2.T134_134_2
  h1 := (2,4,2,2,2)
  h2 := (2,4,2,2,1)
  D := [[2, 4, 2, 3], [2, 4, 2, 4], [2, 4, 2, 0], [2, 4, 2, 1], [2, 4, 2, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_134_134_15 : ColCert where
  rK := ⟨134, by decide⟩
  rH := ⟨134, by decide⟩
  m := 5
  T1 := T134_134
  T2 := Q2.T134_134_2
  h1 := (3,0,4,3,3)
  h2 := (3,0,4,3,1)
  D := [[3, 0, 0, 0], [3, 0, 0, 0], [3, 0, 0, 0], [3, 0, 0, 0], [3, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_134_134_16 : ColCert where
  rK := ⟨134, by decide⟩
  rH := ⟨134, by decide⟩
  m := 5
  T1 := T134_134
  T2 := Q2.T134_134_2
  h1 := (3,1,3,3,4)
  h2 := (3,1,3,3,0)
  D := [[3, 1, 2, 3], [3, 1, 2, 2], [3, 1, 2, 1], [3, 1, 2, 0], [3, 1, 2, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_134_134_17 : ColCert where
  rK := ⟨134, by decide⟩
  rH := ⟨134, by decide⟩
  m := 5
  T1 := T134_134
  T2 := Q2.T134_134_2
  h1 := (3,2,2,3,4)
  h2 := (3,2,2,3,3)
  D := [[3, 2, 4, 1], [3, 2, 4, 4], [3, 2, 4, 2], [3, 2, 4, 0], [3, 2, 4, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_134_134_18 : ColCert where
  rK := ⟨134, by decide⟩
  rH := ⟨134, by decide⟩
  m := 5
  T1 := T134_134
  T2 := Q2.T134_134_2
  h1 := (3,3,1,3,3)
  h2 := (3,3,1,3,0)
  D := [[3, 3, 1, 4], [3, 3, 1, 1], [3, 3, 1, 3], [3, 3, 1, 0], [3, 3, 1, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_134_134_19 : ColCert where
  rK := ⟨134, by decide⟩
  rH := ⟨134, by decide⟩
  m := 5
  T1 := T134_134
  T2 := Q2.T134_134_2
  h1 := (3,4,0,3,1)
  h2 := (3,4,0,3,1)
  D := [[3, 4, 3, 2], [3, 4, 3, 3], [3, 4, 3, 4], [3, 4, 3, 0], [3, 4, 3, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_134_134_20 : ColCert where
  rK := ⟨134, by decide⟩
  rH := ⟨134, by decide⟩
  m := 5
  T1 := T134_134
  T2 := Q2.T134_134_2
  h1 := (4,0,2,4,1)
  h2 := (4,0,2,4,0)
  D := [[4, 0, 0, 0], [4, 0, 0, 0], [4, 0, 0, 0], [4, 0, 0, 0], [4, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_134_134_21 : ColCert where
  rK := ⟨134, by decide⟩
  rH := ⟨134, by decide⟩
  m := 5
  T1 := T134_134
  T2 := Q2.T134_134_2
  h1 := (4,1,1,4,0)
  h2 := (4,1,1,4,2)
  D := [[4, 1, 1, 0], [4, 1, 1, 4], [4, 1, 1, 3], [4, 1, 1, 2], [4, 1, 1, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_134_134_22 : ColCert where
  rK := ⟨134, by decide⟩
  rH := ⟨134, by decide⟩
  m := 5
  T1 := T134_134
  T2 := Q2.T134_134_2
  h1 := (4,2,0,4,3)
  h2 := (4,2,0,4,3)
  D := [[4, 2, 2, 0], [4, 2, 2, 3], [4, 2, 2, 1], [4, 2, 2, 4], [4, 2, 2, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_134_134_23 : ColCert where
  rK := ⟨134, by decide⟩
  rH := ⟨134, by decide⟩
  m := 5
  T1 := T134_134
  T2 := Q2.T134_134_2
  h1 := (4,3,4,4,0)
  h2 := (4,3,4,4,3)
  D := [[4, 3, 3, 0], [4, 3, 3, 2], [4, 3, 3, 4], [4, 3, 3, 1], [4, 3, 3, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_134_134_24 : ColCert where
  rK := ⟨134, by decide⟩
  rH := ⟨134, by decide⟩
  m := 5
  T1 := T134_134
  T2 := Q2.T134_134_2
  h1 := (4,4,3,4,1)
  h2 := (4,4,3,4,2)
  D := [[4, 4, 4, 0], [4, 4, 4, 1], [4, 4, 4, 2], [4, 4, 4, 3], [4, 4, 4, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_135_0_0 : ColCert where
  rK := ⟨135, by decide⟩
  rH := ⟨0, by decide⟩
  m := 5
  T1 := T135_0
  T2 := Q2.T135_0_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_135_4_0 : ColCert where
  rK := ⟨135, by decide⟩
  rH := ⟨4, by decide⟩
  m := 5
  T1 := T135_4
  T2 := Q2.T135_4_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_135_10_0 : ColCert where
  rK := ⟨135, by decide⟩
  rH := ⟨10, by decide⟩
  m := 5
  T1 := T135_10
  T2 := Q2.T135_10_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_135_10_1 : ColCert where
  rK := ⟨135, by decide⟩
  rH := ⟨10, by decide⟩
  m := 5
  T1 := T135_10
  T2 := Q2.T135_10_2
  h1 := (0,0,0,1,4)
  h2 := (0,0,0,1,4)
  D := [[0, 0, 1, 4], [0, 0, 1, 4], [0, 0, 1, 4], [0, 0, 1, 4], [0, 0, 1, 4]]
  bind1 := by decide
  bind2 := by decide

end LeanDring.P5Presentation
