/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.Twin1.ColCert
import LeanDring.P5.Data.EntryK.C034
import LeanDring.P5.Data.EntryK.C035

/-!
# Species-table cell data, stage 2 — column-data-divergent columns

Per-column certified exponent-vector data (`ColCert`/`ColCertDiv`) with kernel
`decide` bindings. Emitted; the embedded lists are what the kernel certifies.
cdd tier, chunk 13: 60 columns.
-/

-- machine-emitted data: silence style linters (generated long lines, file-level options)
set_option linter.style.longLine false

namespace LeanDring.P5Presentation

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

def colCertDiv_130_82_5 : ColCertDiv where
  rK := ⟨130, by decide⟩
  rH := ⟨82, by decide⟩
  m := 5
  T1 := T130_82
  T2 := Q2.T130_82_2
  h1 := (1,0,2,0,0)
  h2 := (1,0,2,0,0)
  D1 := [[1, 0, 0, 4], [1, 0, 0, 4], [1, 0, 0, 4], [1, 0, 0, 4], [1, 0, 0, 4]]
  D2 := [[1, 0, 0, 0], [1, 0, 0, 0], [1, 0, 0, 0], [1, 0, 0, 0], [1, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_130_82_10 : ColCertDiv where
  rK := ⟨130, by decide⟩
  rH := ⟨82, by decide⟩
  m := 5
  T1 := T130_82
  T2 := Q2.T130_82_2
  h1 := (2,0,4,0,0)
  h2 := (2,0,4,0,0)
  D1 := [[2, 0, 0, 3], [2, 0, 0, 3], [2, 0, 0, 3], [2, 0, 0, 3], [2, 0, 0, 3]]
  D2 := [[2, 0, 0, 0], [2, 0, 0, 0], [2, 0, 0, 0], [2, 0, 0, 0], [2, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_130_82_15 : ColCertDiv where
  rK := ⟨130, by decide⟩
  rH := ⟨82, by decide⟩
  m := 5
  T1 := T130_82
  T2 := Q2.T130_82_2
  h1 := (3,0,1,0,0)
  h2 := (3,0,1,0,0)
  D1 := [[3, 0, 0, 2], [3, 0, 0, 2], [3, 0, 0, 2], [3, 0, 0, 2], [3, 0, 0, 2]]
  D2 := [[3, 0, 0, 0], [3, 0, 0, 0], [3, 0, 0, 0], [3, 0, 0, 0], [3, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_130_82_20 : ColCertDiv where
  rK := ⟨130, by decide⟩
  rH := ⟨82, by decide⟩
  m := 5
  T1 := T130_82
  T2 := Q2.T130_82_2
  h1 := (4,0,3,0,0)
  h2 := (4,0,3,0,0)
  D1 := [[4, 0, 0, 1], [4, 0, 0, 1], [4, 0, 0, 1], [4, 0, 0, 1], [4, 0, 0, 1]]
  D2 := [[4, 0, 0, 0], [4, 0, 0, 0], [4, 0, 0, 0], [4, 0, 0, 0], [4, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_130_92_5 : ColCertDiv where
  rK := ⟨130, by decide⟩
  rH := ⟨92, by decide⟩
  m := 5
  T1 := T130_92
  T2 := Q2.T130_92_2
  h1 := (1,2,3,3,2)
  h2 := (1,2,3,3,2)
  D1 := [[1, 2, 1, 3], [1, 2, 1, 1], [1, 2, 1, 4], [1, 2, 1, 2], [1, 2, 1, 0]]
  D2 := [[1, 2, 1, 2], [1, 2, 1, 0], [1, 2, 1, 3], [1, 2, 1, 1], [1, 2, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_130_92_10 : ColCertDiv where
  rK := ⟨130, by decide⟩
  rH := ⟨92, by decide⟩
  m := 5
  T1 := T130_92
  T2 := Q2.T130_92_2
  h1 := (2,4,1,3,3)
  h2 := (2,4,1,3,3)
  D1 := [[2, 4, 0, 1], [2, 4, 0, 2], [2, 4, 0, 3], [2, 4, 0, 4], [2, 4, 0, 0]]
  D2 := [[2, 4, 0, 4], [2, 4, 0, 0], [2, 4, 0, 1], [2, 4, 0, 2], [2, 4, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_130_92_15 : ColCertDiv where
  rK := ⟨130, by decide⟩
  rH := ⟨92, by decide⟩
  m := 5
  T1 := T130_92
  T2 := Q2.T130_92_2
  h1 := (3,1,4,0,1)
  h2 := (3,1,4,0,2)
  D1 := [[3, 1, 2, 2], [3, 1, 2, 1], [3, 1, 2, 0], [3, 1, 2, 4], [3, 1, 2, 3]]
  D2 := [[3, 1, 2, 0], [3, 1, 2, 4], [3, 1, 2, 3], [3, 1, 2, 2], [3, 1, 2, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_130_92_20 : ColCertDiv where
  rK := ⟨130, by decide⟩
  rH := ⟨92, by decide⟩
  m := 5
  T1 := T130_92
  T2 := Q2.T130_92_2
  h1 := (4,3,2,4,1)
  h2 := (4,3,2,4,2)
  D1 := [[4, 3, 2, 1], [4, 3, 2, 3], [4, 3, 2, 0], [4, 3, 2, 2], [4, 3, 2, 4]]
  D2 := [[4, 3, 2, 3], [4, 3, 2, 0], [4, 3, 2, 2], [4, 3, 2, 4], [4, 3, 2, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_130_98_5 : ColCertDiv where
  rK := ⟨130, by decide⟩
  rH := ⟨98, by decide⟩
  m := 5
  T1 := T130_98
  T2 := Q2.T130_98_2
  h1 := (1,3,1,1,3)
  h2 := (1,3,1,1,3)
  D1 := [[1, 3, 3, 4], [1, 3, 3, 1], [1, 3, 3, 3], [1, 3, 3, 0], [1, 3, 3, 2]]
  D2 := [[1, 3, 3, 2], [1, 3, 3, 4], [1, 3, 3, 1], [1, 3, 3, 3], [1, 3, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_130_98_10 : ColCertDiv where
  rK := ⟨130, by decide⟩
  rH := ⟨98, by decide⟩
  m := 5
  T1 := T130_98
  T2 := Q2.T130_98_2
  h1 := (2,1,2,0,1)
  h2 := (2,1,2,0,2)
  D1 := [[2, 1, 3, 0], [2, 1, 3, 4], [2, 1, 3, 3], [2, 1, 3, 2], [2, 1, 3, 1]]
  D2 := [[2, 1, 3, 2], [2, 1, 3, 1], [2, 1, 3, 0], [2, 1, 3, 4], [2, 1, 3, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_130_98_20 : ColCertDiv where
  rK := ⟨130, by decide⟩
  rH := ⟨98, by decide⟩
  m := 5
  T1 := T130_98
  T2 := Q2.T130_98_2
  h1 := (4,2,4,2,0)
  h2 := (4,2,4,2,2)
  D1 := [[4, 2, 4, 1], [4, 2, 4, 4], [4, 2, 4, 2], [4, 2, 4, 0], [4, 2, 4, 3]]
  D2 := [[4, 2, 4, 0], [4, 2, 4, 3], [4, 2, 4, 1], [4, 2, 4, 4], [4, 2, 4, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_130_100_25 : ColCertDiv where
  rK := ⟨130, by decide⟩
  rH := ⟨100, by decide⟩
  m := 5
  T1 := T130_100
  T2 := Q2.T130_100_2
  h1 := (0,1,3,0,0)
  h2 := (0,1,3,0,0)
  D1 := [[0, 1, 0, 3], [0, 1, 0, 2], [0, 1, 0, 1], [0, 1, 0, 0], [0, 1, 0, 4]]
  D2 := [[0, 1, 0, 2], [0, 1, 0, 1], [0, 1, 0, 0], [0, 1, 0, 4], [0, 1, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_130_100_50 : ColCertDiv where
  rK := ⟨130, by decide⟩
  rH := ⟨100, by decide⟩
  m := 5
  T1 := T130_100
  T2 := Q2.T130_100_2
  h1 := (0,2,1,0,3)
  h2 := (0,2,1,0,3)
  D1 := [[0, 2, 0, 1], [0, 2, 0, 4], [0, 2, 0, 2], [0, 2, 0, 0], [0, 2, 0, 3]]
  D2 := [[0, 2, 0, 4], [0, 2, 0, 2], [0, 2, 0, 0], [0, 2, 0, 3], [0, 2, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_130_100_75 : ColCertDiv where
  rK := ⟨130, by decide⟩
  rH := ⟨100, by decide⟩
  m := 5
  T1 := T130_100
  T2 := Q2.T130_100_2
  h1 := (0,3,4,0,4)
  h2 := (0,3,4,0,4)
  D1 := [[0, 3, 0, 4], [0, 3, 0, 1], [0, 3, 0, 3], [0, 3, 0, 0], [0, 3, 0, 2]]
  D2 := [[0, 3, 0, 1], [0, 3, 0, 3], [0, 3, 0, 0], [0, 3, 0, 2], [0, 3, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_130_100_100 : ColCertDiv where
  rK := ⟨130, by decide⟩
  rH := ⟨100, by decide⟩
  m := 5
  T1 := T130_100
  T2 := Q2.T130_100_2
  h1 := (0,4,2,0,3)
  h2 := (0,4,2,0,3)
  D1 := [[0, 4, 0, 2], [0, 4, 0, 3], [0, 4, 0, 4], [0, 4, 0, 0], [0, 4, 0, 1]]
  D2 := [[0, 4, 0, 3], [0, 4, 0, 4], [0, 4, 0, 0], [0, 4, 0, 1], [0, 4, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_130_106_5 : ColCertDiv where
  rK := ⟨130, by decide⟩
  rH := ⟨106, by decide⟩
  m := 5
  T1 := T130_106
  T2 := Q2.T130_106_2
  h1 := (1,4,4,4,1)
  h2 := (1,4,4,4,1)
  D1 := [[1, 4, 0, 4], [1, 4, 0, 0], [1, 4, 0, 1], [1, 4, 0, 2], [1, 4, 0, 3]]
  D2 := [[1, 4, 0, 1], [1, 4, 0, 2], [1, 4, 0, 3], [1, 4, 0, 4], [1, 4, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_130_106_15 : ColCertDiv where
  rK := ⟨130, by decide⟩
  rH := ⟨106, by decide⟩
  m := 5
  T1 := T130_106
  T2 := Q2.T130_106_2
  h1 := (3,2,2,4,4)
  h2 := (3,2,2,4,1)
  D1 := [[3, 2, 3, 4], [3, 2, 3, 2], [3, 2, 3, 0], [3, 2, 3, 3], [3, 2, 3, 1]]
  D2 := [[3, 2, 3, 2], [3, 2, 3, 0], [3, 2, 3, 3], [3, 2, 3, 1], [3, 2, 3, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_130_106_20 : ColCertDiv where
  rK := ⟨130, by decide⟩
  rH := ⟨106, by decide⟩
  m := 5
  T1 := T130_106
  T2 := Q2.T130_106_2
  h1 := (4,1,1,0,3)
  h2 := (4,1,1,0,1)
  D1 := [[4, 1, 1, 2], [4, 1, 1, 1], [4, 1, 1, 0], [4, 1, 1, 4], [4, 1, 1, 3]]
  D2 := [[4, 1, 1, 3], [4, 1, 1, 2], [4, 1, 1, 1], [4, 1, 1, 0], [4, 1, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_131_30_5 : ColCertDiv where
  rK := ⟨131, by decide⟩
  rH := ⟨30, by decide⟩
  m := 5
  T1 := T131_30
  T2 := Q2.T131_30_2
  h1 := (1,2,3,2,3)
  h2 := (1,2,3,2,0)
  D1 := [[1, 2, 0, 2], [1, 2, 0, 0], [1, 2, 0, 3], [1, 2, 0, 1], [1, 2, 0, 4]]
  D2 := [[1, 2, 0, 4], [1, 2, 0, 2], [1, 2, 0, 0], [1, 2, 0, 3], [1, 2, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_131_30_10 : ColCertDiv where
  rK := ⟨131, by decide⟩
  rH := ⟨30, by decide⟩
  m := 5
  T1 := T131_30
  T2 := Q2.T131_30_2
  h1 := (2,4,1,1,4)
  h2 := (2,4,1,1,3)
  D1 := [[2, 4, 3, 2], [2, 4, 3, 3], [2, 4, 3, 4], [2, 4, 3, 0], [2, 4, 3, 1]]
  D2 := [[2, 4, 3, 1], [2, 4, 3, 2], [2, 4, 3, 3], [2, 4, 3, 4], [2, 4, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_131_30_15 : ColCertDiv where
  rK := ⟨131, by decide⟩
  rH := ⟨30, by decide⟩
  m := 5
  T1 := T131_30
  T2 := Q2.T131_30_2
  h1 := (3,1,4,2,1)
  h2 := (3,1,4,2,3)
  D1 := [[3, 1, 4, 3], [3, 1, 4, 2], [3, 1, 4, 1], [3, 1, 4, 0], [3, 1, 4, 4]]
  D2 := [[3, 1, 4, 0], [3, 1, 4, 4], [3, 1, 4, 3], [3, 1, 4, 2], [3, 1, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_131_30_20 : ColCertDiv where
  rK := ⟨131, by decide⟩
  rH := ⟨30, by decide⟩
  m := 5
  T1 := T131_30
  T2 := Q2.T131_30_2
  h1 := (4,3,2,0,4)
  h2 := (4,3,2,0,3)
  D1 := [[4, 3, 3, 0], [4, 3, 3, 2], [4, 3, 3, 4], [4, 3, 3, 1], [4, 3, 3, 3]]
  D2 := [[4, 3, 3, 4], [4, 3, 3, 1], [4, 3, 3, 3], [4, 3, 3, 0], [4, 3, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_131_34_10 : ColCertDiv where
  rK := ⟨131, by decide⟩
  rH := ⟨34, by decide⟩
  m := 5
  T1 := T131_34
  T2 := Q2.T131_34_2
  h1 := (2,3,1,0,3)
  h2 := (2,3,1,0,4)
  D1 := [[2, 3, 4, 3], [2, 3, 4, 0], [2, 3, 4, 2], [2, 3, 4, 4], [2, 3, 4, 1]]
  D2 := [[2, 3, 4, 4], [2, 3, 4, 1], [2, 3, 4, 3], [2, 3, 4, 0], [2, 3, 4, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_131_34_15 : ColCertDiv where
  rK := ⟨131, by decide⟩
  rH := ⟨34, by decide⟩
  m := 5
  T1 := T131_34
  T2 := Q2.T131_34_2
  h1 := (3,2,4,1,4)
  h2 := (3,2,4,1,1)
  D1 := [[3, 2, 0, 2], [3, 2, 0, 0], [3, 2, 0, 3], [3, 2, 0, 1], [3, 2, 0, 4]]
  D2 := [[3, 2, 0, 4], [3, 2, 0, 2], [3, 2, 0, 0], [3, 2, 0, 3], [3, 2, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_131_34_20 : ColCertDiv where
  rK := ⟨131, by decide⟩
  rH := ⟨34, by decide⟩
  m := 5
  T1 := T131_34
  T2 := Q2.T131_34_2
  h1 := (4,1,2,1,3)
  h2 := (4,1,2,1,1)
  D1 := [[4, 1, 2, 1], [4, 1, 2, 0], [4, 1, 2, 4], [4, 1, 2, 3], [4, 1, 2, 2]]
  D2 := [[4, 1, 2, 4], [4, 1, 2, 3], [4, 1, 2, 2], [4, 1, 2, 1], [4, 1, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_131_42_5 : ColCertDiv where
  rK := ⟨131, by decide⟩
  rH := ⟨42, by decide⟩
  m := 5
  T1 := T131_42
  T2 := Q2.T131_42_2
  h1 := (1,1,3,4,4)
  h2 := (1,1,3,4,2)
  D1 := [[1, 1, 3, 3], [1, 1, 3, 2], [1, 1, 3, 1], [1, 1, 3, 0], [1, 1, 3, 4]]
  D2 := [[1, 1, 3, 1], [1, 1, 3, 0], [1, 1, 3, 4], [1, 1, 3, 3], [1, 1, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_131_42_10 : ColCertDiv where
  rK := ⟨131, by decide⟩
  rH := ⟨42, by decide⟩
  m := 5
  T1 := T131_42
  T2 := Q2.T131_42_2
  h1 := (2,2,1,4,0)
  h2 := (2,2,1,4,1)
  D1 := [[2, 2, 0, 2], [2, 2, 0, 0], [2, 2, 0, 3], [2, 2, 0, 1], [2, 2, 0, 4]]
  D2 := [[2, 2, 0, 3], [2, 2, 0, 1], [2, 2, 0, 4], [2, 2, 0, 2], [2, 2, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_131_42_15 : ColCertDiv where
  rK := ⟨131, by decide⟩
  rH := ⟨42, by decide⟩
  m := 5
  T1 := T131_42
  T2 := Q2.T131_42_2
  h1 := (3,3,4,0,4)
  h2 := (3,3,4,0,3)
  D1 := [[3, 3, 1, 3], [3, 3, 1, 0], [3, 3, 1, 2], [3, 3, 1, 4], [3, 3, 1, 1]]
  D2 := [[3, 3, 1, 2], [3, 3, 1, 4], [3, 3, 1, 1], [3, 3, 1, 3], [3, 3, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_131_42_20 : ColCertDiv where
  rK := ⟨131, by decide⟩
  rH := ⟨42, by decide⟩
  m := 5
  T1 := T131_42
  T2 := Q2.T131_42_2
  h1 := (4,4,2,2,2)
  h2 := (4,4,2,2,4)
  D1 := [[4, 4, 1, 2], [4, 4, 1, 3], [4, 4, 1, 4], [4, 4, 1, 0], [4, 4, 1, 1]]
  D2 := [[4, 4, 1, 4], [4, 4, 1, 0], [4, 4, 1, 1], [4, 4, 1, 2], [4, 4, 1, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_131_46_5 : ColCertDiv where
  rK := ⟨131, by decide⟩
  rH := ⟨46, by decide⟩
  m := 5
  T1 := T131_46
  T2 := Q2.T131_46_2
  h1 := (1,3,3,0,2)
  h2 := (1,3,3,0,3)
  D1 := [[1, 3, 2, 1], [1, 3, 2, 3], [1, 3, 2, 0], [1, 3, 2, 2], [1, 3, 2, 4]]
  D2 := [[1, 3, 2, 2], [1, 3, 2, 4], [1, 3, 2, 1], [1, 3, 2, 3], [1, 3, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_131_46_10 : ColCertDiv where
  rK := ⟨131, by decide⟩
  rH := ⟨46, by decide⟩
  m := 5
  T1 := T131_46
  T2 := Q2.T131_46_2
  h1 := (2,1,1,3,4)
  h2 := (2,1,1,3,2)
  D1 := [[2, 1, 1, 3], [2, 1, 1, 2], [2, 1, 1, 1], [2, 1, 1, 0], [2, 1, 1, 4]]
  D2 := [[2, 1, 1, 1], [2, 1, 1, 0], [2, 1, 1, 4], [2, 1, 1, 3], [2, 1, 1, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_131_46_15 : ColCertDiv where
  rK := ⟨131, by decide⟩
  rH := ⟨46, by decide⟩
  m := 5
  T1 := T131_46
  T2 := Q2.T131_46_2
  h1 := (3,4,4,4,2)
  h2 := (3,4,4,4,1)
  D1 := [[3, 4, 2, 2], [3, 4, 2, 3], [3, 4, 2, 4], [3, 4, 2, 0], [3, 4, 2, 1]]
  D2 := [[3, 4, 2, 1], [3, 4, 2, 2], [3, 4, 2, 3], [3, 4, 2, 4], [3, 4, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_131_46_20 : ColCertDiv where
  rK := ⟨131, by decide⟩
  rH := ⟨46, by decide⟩
  m := 5
  T1 := T131_46
  T2 := Q2.T131_46_2
  h1 := (4,2,2,3,1)
  h2 := (4,2,2,3,2)
  D1 := [[4, 2, 0, 3], [4, 2, 0, 1], [4, 2, 0, 4], [4, 2, 0, 2], [4, 2, 0, 0]]
  D2 := [[4, 2, 0, 4], [4, 2, 0, 2], [4, 2, 0, 0], [4, 2, 0, 3], [4, 2, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_131_48_5 : ColCertDiv where
  rK := ⟨131, by decide⟩
  rH := ⟨48, by decide⟩
  m := 5
  T1 := T131_48
  T2 := Q2.T131_48_2
  h1 := (0,1,0,4,3)
  h2 := (0,1,0,4,1)
  D1 := [[0, 1, 4, 0], [0, 1, 4, 4], [0, 1, 4, 3], [0, 1, 4, 2], [0, 1, 4, 1]]
  D2 := [[0, 1, 4, 3], [0, 1, 4, 2], [0, 1, 4, 1], [0, 1, 4, 0], [0, 1, 4, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_131_48_10 : ColCertDiv where
  rK := ⟨131, by decide⟩
  rH := ⟨48, by decide⟩
  m := 5
  T1 := T131_48
  T2 := Q2.T131_48_2
  h1 := (0,2,0,3,1)
  h2 := (0,2,0,3,2)
  D1 := [[0, 2, 3, 0], [0, 2, 3, 3], [0, 2, 3, 1], [0, 2, 3, 4], [0, 2, 3, 2]]
  D2 := [[0, 2, 3, 1], [0, 2, 3, 4], [0, 2, 3, 2], [0, 2, 3, 0], [0, 2, 3, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_131_48_15 : ColCertDiv where
  rK := ⟨131, by decide⟩
  rH := ⟨48, by decide⟩
  m := 5
  T1 := T131_48
  T2 := Q2.T131_48_2
  h1 := (0,3,0,2,4)
  h2 := (0,3,0,2,3)
  D1 := [[0, 3, 2, 0], [0, 3, 2, 2], [0, 3, 2, 4], [0, 3, 2, 1], [0, 3, 2, 3]]
  D2 := [[0, 3, 2, 4], [0, 3, 2, 1], [0, 3, 2, 3], [0, 3, 2, 0], [0, 3, 2, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_131_48_20 : ColCertDiv where
  rK := ⟨131, by decide⟩
  rH := ⟨48, by decide⟩
  m := 5
  T1 := T131_48
  T2 := Q2.T131_48_2
  h1 := (0,4,0,1,2)
  h2 := (0,4,0,1,4)
  D1 := [[0, 4, 1, 0], [0, 4, 1, 1], [0, 4, 1, 2], [0, 4, 1, 3], [0, 4, 1, 4]]
  D2 := [[0, 4, 1, 2], [0, 4, 1, 3], [0, 4, 1, 4], [0, 4, 1, 0], [0, 4, 1, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_131_92_15 : ColCertDiv where
  rK := ⟨131, by decide⟩
  rH := ⟨92, by decide⟩
  m := 5
  T1 := T131_92
  T2 := Q2.T131_92_2
  h1 := (3,1,4,0,1)
  h2 := (3,1,4,0,2)
  D1 := [[3, 1, 2, 4], [3, 1, 2, 3], [3, 1, 2, 2], [3, 1, 2, 1], [3, 1, 2, 0]]
  D2 := [[3, 1, 2, 0], [3, 1, 2, 4], [3, 1, 2, 3], [3, 1, 2, 2], [3, 1, 2, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_131_92_20 : ColCertDiv where
  rK := ⟨131, by decide⟩
  rH := ⟨92, by decide⟩
  m := 5
  T1 := T131_92
  T2 := Q2.T131_92_2
  h1 := (4,3,2,4,1)
  h2 := (4,3,2,4,2)
  D1 := [[4, 3, 2, 1], [4, 3, 2, 3], [4, 3, 2, 0], [4, 3, 2, 2], [4, 3, 2, 4]]
  D2 := [[4, 3, 2, 2], [4, 3, 2, 4], [4, 3, 2, 1], [4, 3, 2, 3], [4, 3, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_131_96_10 : ColCertDiv where
  rK := ⟨131, by decide⟩
  rH := ⟨96, by decide⟩
  m := 5
  T1 := T131_96
  T2 := Q2.T131_96_2
  h1 := (2,3,1,2,1)
  h2 := (2,3,1,2,2)
  D1 := [[2, 3, 1, 2], [2, 3, 1, 4], [2, 3, 1, 1], [2, 3, 1, 3], [2, 3, 1, 0]]
  D2 := [[2, 3, 1, 3], [2, 3, 1, 0], [2, 3, 1, 2], [2, 3, 1, 4], [2, 3, 1, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_131_96_15 : ColCertDiv where
  rK := ⟨131, by decide⟩
  rH := ⟨96, by decide⟩
  m := 5
  T1 := T131_96
  T2 := Q2.T131_96_2
  h1 := (3,2,4,4,0)
  h2 := (3,2,4,4,2)
  D1 := [[3, 2, 3, 4], [3, 2, 3, 2], [3, 2, 3, 0], [3, 2, 3, 3], [3, 2, 3, 1]]
  D2 := [[3, 2, 3, 1], [3, 2, 3, 4], [3, 2, 3, 2], [3, 2, 3, 0], [3, 2, 3, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_131_96_20 : ColCertDiv where
  rK := ⟨131, by decide⟩
  rH := ⟨96, by decide⟩
  m := 5
  T1 := T131_96
  T2 := Q2.T131_96_2
  h1 := (4,1,2,0,3)
  h2 := (4,1,2,0,1)
  D1 := [[4, 1, 1, 0], [4, 1, 1, 4], [4, 1, 1, 3], [4, 1, 1, 2], [4, 1, 1, 1]]
  D2 := [[4, 1, 1, 3], [4, 1, 1, 2], [4, 1, 1, 1], [4, 1, 1, 0], [4, 1, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_131_108_10 : ColCertDiv where
  rK := ⟨131, by decide⟩
  rH := ⟨108, by decide⟩
  m := 5
  T1 := T131_108
  T2 := Q2.T131_108_2
  h1 := (2,1,1,0,1)
  h2 := (2,1,1,0,2)
  D1 := [[2, 1, 3, 1], [2, 1, 3, 0], [2, 1, 3, 4], [2, 1, 3, 3], [2, 1, 3, 2]]
  D2 := [[2, 1, 3, 2], [2, 1, 3, 1], [2, 1, 3, 0], [2, 1, 3, 4], [2, 1, 3, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_131_108_15 : ColCertDiv where
  rK := ⟨131, by decide⟩
  rH := ⟨108, by decide⟩
  m := 5
  T1 := T131_108
  T2 := Q2.T131_108_2
  h1 := (3,4,4,2,4)
  h2 := (3,4,4,2,0)
  D1 := [[3, 4, 0, 0], [3, 4, 0, 1], [3, 4, 0, 2], [3, 4, 0, 3], [3, 4, 0, 4]]
  D2 := [[3, 4, 0, 1], [3, 4, 0, 2], [3, 4, 0, 3], [3, 4, 0, 4], [3, 4, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_131_108_20 : ColCertDiv where
  rK := ⟨131, by decide⟩
  rH := ⟨108, by decide⟩
  m := 5
  T1 := T131_108
  T2 := Q2.T131_108_2
  h1 := (4,2,2,2,4)
  h2 := (4,2,2,2,1)
  D1 := [[4, 2, 4, 0], [4, 2, 4, 3], [4, 2, 4, 1], [4, 2, 4, 4], [4, 2, 4, 2]]
  D2 := [[4, 2, 4, 2], [4, 2, 4, 0], [4, 2, 4, 3], [4, 2, 4, 1], [4, 2, 4, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_132_4_1 : ColCertDiv where
  rK := ⟨132, by decide⟩
  rH := ⟨4, by decide⟩
  m := 5
  T1 := T132_4
  T2 := Q2.T132_4_2
  h1 := (1,0,3,2,3)
  h2 := (1,0,3,2,3)
  D1 := [[1, 0, 3, 3], [1, 0, 3, 3], [1, 0, 3, 3], [1, 0, 3, 3], [1, 0, 3, 3]]
  D2 := [[1, 0, 3, 2], [1, 0, 3, 2], [1, 0, 3, 2], [1, 0, 3, 2], [1, 0, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_132_4_2 : ColCertDiv where
  rK := ⟨132, by decide⟩
  rH := ⟨4, by decide⟩
  m := 5
  T1 := T132_4
  T2 := Q2.T132_4_2
  h1 := (2,0,1,4,3)
  h2 := (2,0,1,4,3)
  D1 := [[2, 0, 1, 3], [2, 0, 1, 3], [2, 0, 1, 3], [2, 0, 1, 3], [2, 0, 1, 3]]
  D2 := [[2, 0, 1, 1], [2, 0, 1, 1], [2, 0, 1, 1], [2, 0, 1, 1], [2, 0, 1, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_132_4_3 : ColCertDiv where
  rK := ⟨132, by decide⟩
  rH := ⟨4, by decide⟩
  m := 5
  T1 := T132_4
  T2 := Q2.T132_4_2
  h1 := (3,0,4,1,0)
  h2 := (3,0,4,1,0)
  D1 := [[3, 0, 4, 0], [3, 0, 4, 0], [3, 0, 4, 0], [3, 0, 4, 0], [3, 0, 4, 0]]
  D2 := [[3, 0, 4, 2], [3, 0, 4, 2], [3, 0, 4, 2], [3, 0, 4, 2], [3, 0, 4, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_132_4_4 : ColCertDiv where
  rK := ⟨132, by decide⟩
  rH := ⟨4, by decide⟩
  m := 5
  T1 := T132_4
  T2 := Q2.T132_4_2
  h1 := (4,0,2,3,4)
  h2 := (4,0,2,3,4)
  D1 := [[4, 0, 2, 4], [4, 0, 2, 4], [4, 0, 2, 4], [4, 0, 2, 4], [4, 0, 2, 4]]
  D2 := [[4, 0, 2, 0], [4, 0, 2, 0], [4, 0, 2, 0], [4, 0, 2, 0], [4, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_132_22_5 : ColCertDiv where
  rK := ⟨132, by decide⟩
  rH := ⟨22, by decide⟩
  m := 5
  T1 := T132_22
  T2 := Q2.T132_22_2
  h1 := (1,0,3,2,4)
  h2 := (1,0,3,2,4)
  D1 := [[1, 0, 3, 4], [1, 0, 3, 4], [1, 0, 3, 4], [1, 0, 3, 4], [1, 0, 3, 4]]
  D2 := [[1, 0, 3, 3], [1, 0, 3, 3], [1, 0, 3, 3], [1, 0, 3, 3], [1, 0, 3, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_132_22_10 : ColCertDiv where
  rK := ⟨132, by decide⟩
  rH := ⟨22, by decide⟩
  m := 5
  T1 := T132_22
  T2 := Q2.T132_22_2
  h1 := (2,0,1,4,0)
  h2 := (2,0,1,4,0)
  D1 := [[2, 0, 1, 0], [2, 0, 1, 0], [2, 0, 1, 0], [2, 0, 1, 0], [2, 0, 1, 0]]
  D2 := [[2, 0, 1, 3], [2, 0, 1, 3], [2, 0, 1, 3], [2, 0, 1, 3], [2, 0, 1, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_132_22_15 : ColCertDiv where
  rK := ⟨132, by decide⟩
  rH := ⟨22, by decide⟩
  m := 5
  T1 := T132_22
  T2 := Q2.T132_22_2
  h1 := (3,0,4,1,3)
  h2 := (3,0,4,1,3)
  D1 := [[3, 0, 4, 3], [3, 0, 4, 3], [3, 0, 4, 3], [3, 0, 4, 3], [3, 0, 4, 3]]
  D2 := [[3, 0, 4, 0], [3, 0, 4, 0], [3, 0, 4, 0], [3, 0, 4, 0], [3, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_132_22_20 : ColCertDiv where
  rK := ⟨132, by decide⟩
  rH := ⟨22, by decide⟩
  m := 5
  T1 := T132_22
  T2 := Q2.T132_22_2
  h1 := (4,0,2,3,3)
  h2 := (4,0,2,3,3)
  D1 := [[4, 0, 2, 3], [4, 0, 2, 3], [4, 0, 2, 3], [4, 0, 2, 3], [4, 0, 2, 3]]
  D2 := [[4, 0, 2, 4], [4, 0, 2, 4], [4, 0, 2, 4], [4, 0, 2, 4], [4, 0, 2, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_132_31_5 : ColCertDiv where
  rK := ⟨132, by decide⟩
  rH := ⟨31, by decide⟩
  m := 5
  T1 := T132_31
  T2 := Q2.T132_31_2
  h1 := (1,3,2,0,4)
  h2 := (1,3,2,0,0)
  D1 := [[1, 3, 3, 1], [1, 3, 3, 3], [1, 3, 3, 0], [1, 3, 3, 2], [1, 3, 3, 4]]
  D2 := [[1, 3, 3, 3], [1, 3, 3, 0], [1, 3, 3, 2], [1, 3, 3, 4], [1, 3, 3, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_132_31_15 : ColCertDiv where
  rK := ⟨132, by decide⟩
  rH := ⟨31, by decide⟩
  m := 5
  T1 := T132_31
  T2 := Q2.T132_31_2
  h1 := (3,4,1,4,4)
  h2 := (3,4,1,4,3)
  D1 := [[3, 4, 0, 4], [3, 4, 0, 0], [3, 4, 0, 1], [3, 4, 0, 2], [3, 4, 0, 3]]
  D2 := [[3, 4, 0, 1], [3, 4, 0, 2], [3, 4, 0, 3], [3, 4, 0, 4], [3, 4, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_132_35_5 : ColCertDiv where
  rK := ⟨132, by decide⟩
  rH := ⟨35, by decide⟩
  m := 5
  T1 := T132_35
  T2 := Q2.T132_35_2
  h1 := (1,2,4,2,0)
  h2 := (1,2,4,2,2)
  D1 := [[1, 2, 1, 3], [1, 2, 1, 1], [1, 2, 1, 4], [1, 2, 1, 2], [1, 2, 1, 0]]
  D2 := [[1, 2, 1, 2], [1, 2, 1, 0], [1, 2, 1, 3], [1, 2, 1, 1], [1, 2, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_132_35_10 : ColCertDiv where
  rK := ⟨132, by decide⟩
  rH := ⟨35, by decide⟩
  m := 5
  T1 := T132_35
  T2 := Q2.T132_35_2
  h1 := (2,4,3,1,0)
  h2 := (2,4,3,1,4)
  D1 := [[2, 4, 0, 3], [2, 4, 0, 4], [2, 4, 0, 0], [2, 4, 0, 1], [2, 4, 0, 2]]
  D2 := [[2, 4, 0, 1], [2, 4, 0, 2], [2, 4, 0, 3], [2, 4, 0, 4], [2, 4, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_132_35_15 : ColCertDiv where
  rK := ⟨132, by decide⟩
  rH := ⟨35, by decide⟩
  m := 5
  T1 := T132_35
  T2 := Q2.T132_35_2
  h1 := (3,1,2,2,3)
  h2 := (3,1,2,2,0)
  D1 := [[3, 1, 2, 3], [3, 1, 2, 2], [3, 1, 2, 1], [3, 1, 2, 0], [3, 1, 2, 4]]
  D2 := [[3, 1, 2, 1], [3, 1, 2, 0], [3, 1, 2, 4], [3, 1, 2, 3], [3, 1, 2, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_132_35_20 : ColCertDiv where
  rK := ⟨132, by decide⟩
  rH := ⟨35, by decide⟩
  m := 5
  T1 := T132_35
  T2 := Q2.T132_35_2
  h1 := (4,3,1,0,4)
  h2 := (4,3,1,0,3)
  D1 := [[4, 3, 2, 3], [4, 3, 2, 0], [4, 3, 2, 2], [4, 3, 2, 4], [4, 3, 2, 1]]
  D2 := [[4, 3, 2, 0], [4, 3, 2, 2], [4, 3, 2, 4], [4, 3, 2, 1], [4, 3, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_132_38_5 : ColCertDiv where
  rK := ⟨132, by decide⟩
  rH := ⟨38, by decide⟩
  m := 5
  T1 := T132_38
  T2 := Q2.T132_38_2
  h1 := (0,1,3,4,1)
  h2 := (0,1,3,4,4)
  D1 := [[0, 1, 4, 3], [0, 1, 4, 2], [0, 1, 4, 1], [0, 1, 4, 0], [0, 1, 4, 4]]
  D2 := [[0, 1, 4, 0], [0, 1, 4, 4], [0, 1, 4, 3], [0, 1, 4, 2], [0, 1, 4, 1]]
  bind1 := by decide
  bind2 := by decide

end LeanDring.P5Presentation
