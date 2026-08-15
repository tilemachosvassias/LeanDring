/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.Twin1.ColCert
import LeanDring.P5.Data.EntryK.C034
import LeanDring.P5.Data.EntryK.C035

/-!
# Species-table cell data, stage 2 — twin-coincident columns (cheap tier)

Per-column certified exponent-vector data (`ColCert`/`ColCertDiv`) with kernel
`decide` bindings. Emitted; the embedded lists are what the kernel certifies.
rest tier, chunk 68: 60 columns.
-/

-- machine-emitted data: silence style linters (generated long lines, file-level options)
set_option linter.style.longLine false

namespace LeanDring.P5Presentation

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

def colCert_131_104_10 : ColCert where
  rK := ⟨131, by decide⟩
  rH := ⟨104, by decide⟩
  m := 5
  T1 := T131_104
  T2 := Q2.T131_104_2
  h1 := (2,2,1,1,3)
  h2 := (2,2,1,1,3)
  D := [[2, 2, 2, 1], [2, 2, 2, 4], [2, 2, 2, 2], [2, 2, 2, 0], [2, 2, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_131_104_15 : ColCert where
  rK := ⟨131, by decide⟩
  rH := ⟨104, by decide⟩
  m := 5
  T1 := T131_104
  T2 := Q2.T131_104_2
  h1 := (3,3,4,3,0)
  h2 := (3,3,4,3,0)
  D := [[3, 3, 4, 0], [3, 3, 4, 2], [3, 3, 4, 4], [3, 3, 4, 1], [3, 3, 4, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_131_104_20 : ColCert where
  rK := ⟨131, by decide⟩
  rH := ⟨104, by decide⟩
  m := 5
  T1 := T131_104
  T2 := Q2.T131_104_2
  h1 := (4,4,2,1,2)
  h2 := (4,4,2,1,2)
  D := [[4, 4, 0, 1], [4, 4, 0, 2], [4, 4, 0, 3], [4, 4, 0, 4], [4, 4, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_131_108_0 : ColCert where
  rK := ⟨131, by decide⟩
  rH := ⟨108, by decide⟩
  m := 5
  T1 := T131_108
  T2 := Q2.T131_108_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_131_108_1 : ColCert where
  rK := ⟨131, by decide⟩
  rH := ⟨108, by decide⟩
  m := 5
  T1 := T131_108
  T2 := Q2.T131_108_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_131_108_2 : ColCert where
  rK := ⟨131, by decide⟩
  rH := ⟨108, by decide⟩
  m := 5
  T1 := T131_108
  T2 := Q2.T131_108_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_131_108_3 : ColCert where
  rK := ⟨131, by decide⟩
  rH := ⟨108, by decide⟩
  m := 5
  T1 := T131_108
  T2 := Q2.T131_108_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_131_108_4 : ColCert where
  rK := ⟨131, by decide⟩
  rH := ⟨108, by decide⟩
  m := 5
  T1 := T131_108
  T2 := Q2.T131_108_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_131_108_5 : ColCert where
  rK := ⟨131, by decide⟩
  rH := ⟨108, by decide⟩
  m := 5
  T1 := T131_108
  T2 := Q2.T131_108_2
  h1 := (1,3,3,1,0)
  h2 := (1,3,3,1,0)
  D := [[1, 3, 3, 3], [1, 3, 3, 0], [1, 3, 3, 2], [1, 3, 3, 4], [1, 3, 3, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_131_110_0 : ColCert where
  rK := ⟨131, by decide⟩
  rH := ⟨110, by decide⟩
  m := 5
  T1 := T131_110
  T2 := Q2.T131_110_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_131_110_1 : ColCert where
  rK := ⟨131, by decide⟩
  rH := ⟨110, by decide⟩
  m := 5
  T1 := T131_110
  T2 := Q2.T131_110_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_131_110_2 : ColCert where
  rK := ⟨131, by decide⟩
  rH := ⟨110, by decide⟩
  m := 5
  T1 := T131_110
  T2 := Q2.T131_110_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_131_110_3 : ColCert where
  rK := ⟨131, by decide⟩
  rH := ⟨110, by decide⟩
  m := 5
  T1 := T131_110
  T2 := Q2.T131_110_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_131_110_4 : ColCert where
  rK := ⟨131, by decide⟩
  rH := ⟨110, by decide⟩
  m := 5
  T1 := T131_110
  T2 := Q2.T131_110_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_131_110_5 : ColCert where
  rK := ⟨131, by decide⟩
  rH := ⟨110, by decide⟩
  m := 5
  T1 := T131_110
  T2 := Q2.T131_110_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_131_110_10 : ColCert where
  rK := ⟨131, by decide⟩
  rH := ⟨110, by decide⟩
  m := 5
  T1 := T131_110
  T2 := Q2.T131_110_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_131_110_15 : ColCert where
  rK := ⟨131, by decide⟩
  rH := ⟨110, by decide⟩
  m := 5
  T1 := T131_110
  T2 := Q2.T131_110_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_131_110_20 : ColCert where
  rK := ⟨131, by decide⟩
  rH := ⟨110, by decide⟩
  m := 5
  T1 := T131_110
  T2 := Q2.T131_110_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_131_110_25 : ColCert where
  rK := ⟨131, by decide⟩
  rH := ⟨110, by decide⟩
  m := 5
  T1 := T131_110
  T2 := Q2.T131_110_2
  h1 := (0,1,0,0,0)
  h2 := (0,1,0,0,0)
  D := [[0, 1, 0, 2], [0, 1, 0, 1], [0, 1, 0, 0], [0, 1, 0, 4], [0, 1, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_131_110_50 : ColCert where
  rK := ⟨131, by decide⟩
  rH := ⟨110, by decide⟩
  m := 5
  T1 := T131_110
  T2 := Q2.T131_110_2
  h1 := (0,2,0,0,0)
  h2 := (0,2,0,0,0)
  D := [[0, 2, 0, 4], [0, 2, 0, 2], [0, 2, 0, 0], [0, 2, 0, 3], [0, 2, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_131_110_75 : ColCert where
  rK := ⟨131, by decide⟩
  rH := ⟨110, by decide⟩
  m := 5
  T1 := T131_110
  T2 := Q2.T131_110_2
  h1 := (0,3,0,0,0)
  h2 := (0,3,0,0,0)
  D := [[0, 3, 0, 1], [0, 3, 0, 3], [0, 3, 0, 0], [0, 3, 0, 2], [0, 3, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_131_110_100 : ColCert where
  rK := ⟨131, by decide⟩
  rH := ⟨110, by decide⟩
  m := 5
  T1 := T131_110
  T2 := Q2.T131_110_2
  h1 := (0,4,0,0,0)
  h2 := (0,4,0,0,0)
  D := [[0, 4, 0, 3], [0, 4, 0, 4], [0, 4, 0, 0], [0, 4, 0, 1], [0, 4, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_131_131_0 : ColCert where
  rK := ⟨131, by decide⟩
  rH := ⟨131, by decide⟩
  m := 5
  T1 := T131_131
  T2 := Q2.T131_131_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_131_131_1 : ColCert where
  rK := ⟨131, by decide⟩
  rH := ⟨131, by decide⟩
  m := 5
  T1 := T131_131
  T2 := Q2.T131_131_2
  h1 := (0,1,0,0,0)
  h2 := (0,1,0,0,0)
  D := [[0, 1, 0, 2], [0, 1, 0, 1], [0, 1, 0, 0], [0, 1, 0, 4], [0, 1, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_131_131_2 : ColCert where
  rK := ⟨131, by decide⟩
  rH := ⟨131, by decide⟩
  m := 5
  T1 := T131_131
  T2 := Q2.T131_131_2
  h1 := (0,2,0,0,0)
  h2 := (0,2,0,0,0)
  D := [[0, 2, 0, 4], [0, 2, 0, 2], [0, 2, 0, 0], [0, 2, 0, 3], [0, 2, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_131_131_3 : ColCert where
  rK := ⟨131, by decide⟩
  rH := ⟨131, by decide⟩
  m := 5
  T1 := T131_131
  T2 := Q2.T131_131_2
  h1 := (0,3,0,0,0)
  h2 := (0,3,0,0,0)
  D := [[0, 3, 0, 1], [0, 3, 0, 3], [0, 3, 0, 0], [0, 3, 0, 2], [0, 3, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_131_131_4 : ColCert where
  rK := ⟨131, by decide⟩
  rH := ⟨131, by decide⟩
  m := 5
  T1 := T131_131
  T2 := Q2.T131_131_2
  h1 := (0,4,0,0,0)
  h2 := (0,4,0,0,0)
  D := [[0, 4, 0, 3], [0, 4, 0, 4], [0, 4, 0, 0], [0, 4, 0, 1], [0, 4, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_131_131_5 : ColCert where
  rK := ⟨131, by decide⟩
  rH := ⟨131, by decide⟩
  m := 5
  T1 := T131_131
  T2 := Q2.T131_131_2
  h1 := (1,0,3,0,0)
  h2 := (1,0,3,0,0)
  D := [[1, 0, 0, 0], [1, 0, 0, 0], [1, 0, 0, 0], [1, 0, 0, 0], [1, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_131_131_6 : ColCert where
  rK := ⟨131, by decide⟩
  rH := ⟨131, by decide⟩
  m := 5
  T1 := T131_131
  T2 := Q2.T131_131_2
  h1 := (1,1,3,0,3)
  h2 := (1,1,3,0,3)
  D := [[1, 1, 4, 1], [1, 1, 4, 0], [1, 1, 4, 4], [1, 1, 4, 3], [1, 1, 4, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_131_131_7 : ColCert where
  rK := ⟨131, by decide⟩
  rH := ⟨131, by decide⟩
  m := 5
  T1 := T131_131
  T2 := Q2.T131_131_2
  h1 := (1,2,3,0,1)
  h2 := (1,2,3,0,1)
  D := [[1, 2, 3, 2], [1, 2, 3, 0], [1, 2, 3, 3], [1, 2, 3, 1], [1, 2, 3, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_131_131_8 : ColCert where
  rK := ⟨131, by decide⟩
  rH := ⟨131, by decide⟩
  m := 5
  T1 := T131_131
  T2 := Q2.T131_131_2
  h1 := (1,3,3,0,4)
  h2 := (1,3,3,0,4)
  D := [[1, 3, 2, 3], [1, 3, 2, 0], [1, 3, 2, 2], [1, 3, 2, 4], [1, 3, 2, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_131_131_9 : ColCert where
  rK := ⟨131, by decide⟩
  rH := ⟨131, by decide⟩
  m := 5
  T1 := T131_131
  T2 := Q2.T131_131_2
  h1 := (1,4,3,0,2)
  h2 := (1,4,3,0,2)
  D := [[1, 4, 1, 4], [1, 4, 1, 0], [1, 4, 1, 1], [1, 4, 1, 2], [1, 4, 1, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_131_131_10 : ColCert where
  rK := ⟨131, by decide⟩
  rH := ⟨131, by decide⟩
  m := 5
  T1 := T131_131
  T2 := Q2.T131_131_2
  h1 := (2,0,1,0,0)
  h2 := (2,0,1,0,0)
  D := [[2, 0, 0, 0], [2, 0, 0, 0], [2, 0, 0, 0], [2, 0, 0, 0], [2, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_131_131_11 : ColCert where
  rK := ⟨131, by decide⟩
  rH := ⟨131, by decide⟩
  m := 5
  T1 := T131_131
  T2 := Q2.T131_131_2
  h1 := (2,1,1,0,1)
  h2 := (2,1,1,0,1)
  D := [[2, 1, 3, 1], [2, 1, 3, 0], [2, 1, 3, 4], [2, 1, 3, 3], [2, 1, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_131_131_12 : ColCert where
  rK := ⟨131, by decide⟩
  rH := ⟨131, by decide⟩
  m := 5
  T1 := T131_131
  T2 := Q2.T131_131_2
  h1 := (2,2,1,0,2)
  h2 := (2,2,1,0,2)
  D := [[2, 2, 1, 2], [2, 2, 1, 0], [2, 2, 1, 3], [2, 2, 1, 1], [2, 2, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_131_131_13 : ColCert where
  rK := ⟨131, by decide⟩
  rH := ⟨131, by decide⟩
  m := 5
  T1 := T131_131
  T2 := Q2.T131_131_2
  h1 := (2,3,1,0,3)
  h2 := (2,3,1,0,3)
  D := [[2, 3, 4, 3], [2, 3, 4, 0], [2, 3, 4, 2], [2, 3, 4, 4], [2, 3, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_131_131_14 : ColCert where
  rK := ⟨131, by decide⟩
  rH := ⟨131, by decide⟩
  m := 5
  T1 := T131_131
  T2 := Q2.T131_131_2
  h1 := (2,4,1,0,4)
  h2 := (2,4,1,0,4)
  D := [[2, 4, 2, 4], [2, 4, 2, 0], [2, 4, 2, 1], [2, 4, 2, 2], [2, 4, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_131_131_15 : ColCert where
  rK := ⟨131, by decide⟩
  rH := ⟨131, by decide⟩
  m := 5
  T1 := T131_131
  T2 := Q2.T131_131_2
  h1 := (3,0,4,0,0)
  h2 := (3,0,4,0,0)
  D := [[3, 0, 0, 0], [3, 0, 0, 0], [3, 0, 0, 0], [3, 0, 0, 0], [3, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_131_131_16 : ColCert where
  rK := ⟨131, by decide⟩
  rH := ⟨131, by decide⟩
  m := 5
  T1 := T131_131
  T2 := Q2.T131_131_2
  h1 := (3,1,4,0,4)
  h2 := (3,1,4,0,4)
  D := [[3, 1, 2, 2], [3, 1, 2, 1], [3, 1, 2, 0], [3, 1, 2, 4], [3, 1, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_131_131_17 : ColCert where
  rK := ⟨131, by decide⟩
  rH := ⟨131, by decide⟩
  m := 5
  T1 := T131_131
  T2 := Q2.T131_131_2
  h1 := (3,2,4,0,3)
  h2 := (3,2,4,0,3)
  D := [[3, 2, 4, 4], [3, 2, 4, 2], [3, 2, 4, 0], [3, 2, 4, 3], [3, 2, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_131_131_18 : ColCert where
  rK := ⟨131, by decide⟩
  rH := ⟨131, by decide⟩
  m := 5
  T1 := T131_131
  T2 := Q2.T131_131_2
  h1 := (3,3,4,0,2)
  h2 := (3,3,4,0,2)
  D := [[3, 3, 1, 1], [3, 3, 1, 3], [3, 3, 1, 0], [3, 3, 1, 2], [3, 3, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_131_131_19 : ColCert where
  rK := ⟨131, by decide⟩
  rH := ⟨131, by decide⟩
  m := 5
  T1 := T131_131
  T2 := Q2.T131_131_2
  h1 := (3,4,4,0,1)
  h2 := (3,4,4,0,1)
  D := [[3, 4, 3, 3], [3, 4, 3, 4], [3, 4, 3, 0], [3, 4, 3, 1], [3, 4, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_131_131_20 : ColCert where
  rK := ⟨131, by decide⟩
  rH := ⟨131, by decide⟩
  m := 5
  T1 := T131_131
  T2 := Q2.T131_131_2
  h1 := (4,0,2,0,0)
  h2 := (4,0,2,0,0)
  D := [[4, 0, 0, 0], [4, 0, 0, 0], [4, 0, 0, 0], [4, 0, 0, 0], [4, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_131_131_21 : ColCert where
  rK := ⟨131, by decide⟩
  rH := ⟨131, by decide⟩
  m := 5
  T1 := T131_131
  T2 := Q2.T131_131_2
  h1 := (4,1,2,0,2)
  h2 := (4,1,2,0,2)
  D := [[4, 1, 1, 4], [4, 1, 1, 3], [4, 1, 1, 2], [4, 1, 1, 1], [4, 1, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_131_131_22 : ColCert where
  rK := ⟨131, by decide⟩
  rH := ⟨131, by decide⟩
  m := 5
  T1 := T131_131
  T2 := Q2.T131_131_2
  h1 := (4,2,2,0,4)
  h2 := (4,2,2,0,4)
  D := [[4, 2, 2, 3], [4, 2, 2, 1], [4, 2, 2, 4], [4, 2, 2, 2], [4, 2, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_131_131_23 : ColCert where
  rK := ⟨131, by decide⟩
  rH := ⟨131, by decide⟩
  m := 5
  T1 := T131_131
  T2 := Q2.T131_131_2
  h1 := (4,3,2,0,1)
  h2 := (4,3,2,0,1)
  D := [[4, 3, 3, 2], [4, 3, 3, 4], [4, 3, 3, 1], [4, 3, 3, 3], [4, 3, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_131_131_24 : ColCert where
  rK := ⟨131, by decide⟩
  rH := ⟨131, by decide⟩
  m := 5
  T1 := T131_131
  T2 := Q2.T131_131_2
  h1 := (4,4,2,0,3)
  h2 := (4,4,2,0,3)
  D := [[4, 4, 4, 1], [4, 4, 4, 2], [4, 4, 4, 3], [4, 4, 4, 4], [4, 4, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_132_0_0 : ColCert where
  rK := ⟨132, by decide⟩
  rH := ⟨0, by decide⟩
  m := 5
  T1 := T132_0
  T2 := Q2.T132_0_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_132_4_0 : ColCert where
  rK := ⟨132, by decide⟩
  rH := ⟨4, by decide⟩
  m := 5
  T1 := T132_4
  T2 := Q2.T132_4_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_132_10_0 : ColCert where
  rK := ⟨132, by decide⟩
  rH := ⟨10, by decide⟩
  m := 5
  T1 := T132_10
  T2 := Q2.T132_10_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_132_10_1 : ColCert where
  rK := ⟨132, by decide⟩
  rH := ⟨10, by decide⟩
  m := 5
  T1 := T132_10
  T2 := Q2.T132_10_2
  h1 := (0,0,0,1,4)
  h2 := (0,0,0,1,4)
  D := [[0, 0, 1, 4], [0, 0, 1, 4], [0, 0, 1, 4], [0, 0, 1, 4], [0, 0, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_132_10_2 : ColCert where
  rK := ⟨132, by decide⟩
  rH := ⟨10, by decide⟩
  m := 5
  T1 := T132_10
  T2 := Q2.T132_10_2
  h1 := (0,0,0,2,3)
  h2 := (0,0,0,2,3)
  D := [[0, 0, 2, 3], [0, 0, 2, 3], [0, 0, 2, 3], [0, 0, 2, 3], [0, 0, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_132_10_3 : ColCert where
  rK := ⟨132, by decide⟩
  rH := ⟨10, by decide⟩
  m := 5
  T1 := T132_10
  T2 := Q2.T132_10_2
  h1 := (0,0,0,3,2)
  h2 := (0,0,0,3,2)
  D := [[0, 0, 3, 2], [0, 0, 3, 2], [0, 0, 3, 2], [0, 0, 3, 2], [0, 0, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_132_10_4 : ColCert where
  rK := ⟨132, by decide⟩
  rH := ⟨10, by decide⟩
  m := 5
  T1 := T132_10
  T2 := Q2.T132_10_2
  h1 := (0,0,0,4,1)
  h2 := (0,0,0,4,1)
  D := [[0, 0, 4, 1], [0, 0, 4, 1], [0, 0, 4, 1], [0, 0, 4, 1], [0, 0, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_132_12_0 : ColCert where
  rK := ⟨132, by decide⟩
  rH := ⟨12, by decide⟩
  m := 5
  T1 := T132_12
  T2 := Q2.T132_12_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_132_12_1 : ColCert where
  rK := ⟨132, by decide⟩
  rH := ⟨12, by decide⟩
  m := 5
  T1 := T132_12
  T2 := Q2.T132_12_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_132_12_2 : ColCert where
  rK := ⟨132, by decide⟩
  rH := ⟨12, by decide⟩
  m := 5
  T1 := T132_12
  T2 := Q2.T132_12_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_132_12_3 : ColCert where
  rK := ⟨132, by decide⟩
  rH := ⟨12, by decide⟩
  m := 5
  T1 := T132_12
  T2 := Q2.T132_12_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_132_12_4 : ColCert where
  rK := ⟨132, by decide⟩
  rH := ⟨12, by decide⟩
  m := 5
  T1 := T132_12
  T2 := Q2.T132_12_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_132_22_0 : ColCert where
  rK := ⟨132, by decide⟩
  rH := ⟨22, by decide⟩
  m := 5
  T1 := T132_22
  T2 := Q2.T132_22_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

end LeanDring.P5Presentation
