/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.Twin1.ColCert
import LeanDring.P5.Data.EntryK.C044

/-!
# Species-table cell data, stage 2 — column-data-divergent columns

Per-column certified exponent-vector data (`ColCert`/`ColCertDiv`) with kernel
`decide` bindings. Emitted; the embedded lists are what the kernel certifies.
cdd tier, chunk 32: 60 columns.
-/

-- machine-emitted data: silence style linters (generated long lines, file-level options)
set_option linter.style.longLine false

namespace LeanDring.P5Presentation

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

def colCertDiv_147_123_8 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨123, by decide⟩
  m := 1
  T1 := T147_123
  T2 := Q2.T147_123_2
  h1 := (1,3,3,3,0)
  h2 := (1,3,3,3,1)
  D1 := [[1, 3, 3, 0, 1]]
  D2 := [[1, 3, 3, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_123_9 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨123, by decide⟩
  m := 1
  T1 := T147_123
  T2 := Q2.T147_123_2
  h1 := (1,4,1,3,0)
  h2 := (1,4,1,3,2)
  D1 := [[1, 4, 1, 4, 2]]
  D2 := [[1, 4, 1, 4, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_123_10 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨123, by decide⟩
  m := 1
  T1 := T147_123
  T2 := Q2.T147_123_2
  h1 := (2,0,3,1,4)
  h2 := (2,0,3,1,0)
  D1 := [[2, 0, 3, 1, 2]]
  D2 := [[2, 0, 3, 1, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_123_11 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨123, by decide⟩
  m := 1
  T1 := T147_123
  T2 := Q2.T147_123_2
  h1 := (2,1,1,1,4)
  h2 := (2,1,1,1,1)
  D1 := [[2, 1, 1, 4, 4]]
  D2 := [[2, 1, 1, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_123_12 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨123, by decide⟩
  m := 1
  T1 := T147_123
  T2 := Q2.T147_123_2
  h1 := (2,2,4,1,2)
  h2 := (2,2,4,1,0)
  D1 := [[2, 2, 4, 2, 3]]
  D2 := [[2, 2, 4, 2, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_123_13 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨123, by decide⟩
  m := 1
  T1 := T147_123
  T2 := Q2.T147_123_2
  h1 := (2,3,2,1,3)
  h2 := (2,3,2,1,2)
  D1 := [[2, 3, 2, 0, 4]]
  D2 := [[2, 3, 2, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_123_15 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨123, by decide⟩
  m := 1
  T1 := T147_123
  T2 := Q2.T147_123_2
  h1 := (3,0,2,4,3)
  h2 := (3,0,2,4,2)
  D1 := [[3, 0, 2, 4, 1]]
  D2 := [[3, 0, 2, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_123_17 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨123, by decide⟩
  m := 1
  T1 := T147_123
  T2 := Q2.T147_123_2
  h1 := (3,2,3,4,4)
  h2 := (3,2,3,4,0)
  D1 := [[3, 2, 3, 3, 3]]
  D2 := [[3, 2, 3, 3, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_123_18 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨123, by decide⟩
  m := 1
  T1 := T147_123
  T2 := Q2.T147_123_2
  h1 := (3,3,1,4,4)
  h2 := (3,3,1,4,1)
  D1 := [[3, 3, 1, 0, 2]]
  D2 := [[3, 3, 1, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_123_19 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨123, by decide⟩
  m := 1
  T1 := T147_123
  T2 := Q2.T147_123_2
  h1 := (3,4,4,4,2)
  h2 := (3,4,4,4,0)
  D1 := [[3, 4, 4, 2, 3]]
  D2 := [[3, 4, 4, 2, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_123_20 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨123, by decide⟩
  m := 1
  T1 := T147_123
  T2 := Q2.T147_123_2
  h1 := (4,0,1,2,0)
  h2 := (4,0,1,2,2)
  D1 := [[4, 0, 1, 2, 2]]
  D2 := [[4, 0, 1, 2, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_123_21 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨123, by decide⟩
  m := 1
  T1 := T147_123
  T2 := Q2.T147_123_2
  h1 := (4,1,4,2,3)
  h2 := (4,1,4,2,1)
  D1 := [[4, 1, 4, 3, 1]]
  D2 := [[4, 1, 4, 3, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_123_22 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨123, by decide⟩
  m := 1
  T1 := T147_123
  T2 := Q2.T147_123_2
  h1 := (4,2,2,2,4)
  h2 := (4,2,2,2,3)
  D1 := [[4, 2, 2, 4, 2]]
  D2 := [[4, 2, 2, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_123_24 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨123, by decide⟩
  m := 1
  T1 := T147_123
  T2 := Q2.T147_123_2
  h1 := (4,4,3,2,0)
  h2 := (4,4,3,2,1)
  D1 := [[4, 4, 3, 1, 0]]
  D2 := [[4, 4, 3, 1, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_124_1 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨124, by decide⟩
  m := 1
  T1 := T147_124
  T2 := Q2.T147_124_2
  h1 := (0,1,2,0,4)
  h2 := (0,1,2,0,0)
  D1 := [[0, 1, 2, 0, 2]]
  D2 := [[0, 1, 2, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_124_2 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨124, by decide⟩
  m := 1
  T1 := T147_124
  T2 := Q2.T147_124_2
  h1 := (0,2,4,0,0)
  h2 := (0,2,4,0,2)
  D1 := [[0, 2, 4, 0, 2]]
  D2 := [[0, 2, 4, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_124_3 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨124, by decide⟩
  m := 1
  T1 := T147_124
  T2 := Q2.T147_124_2
  h1 := (0,3,1,0,3)
  h2 := (0,3,1,0,1)
  D1 := [[0, 3, 1, 0, 0]]
  D2 := [[0, 3, 1, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_124_4 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨124, by decide⟩
  m := 1
  T1 := T147_124
  T2 := Q2.T147_124_2
  h1 := (0,4,3,0,3)
  h2 := (0,4,3,0,2)
  D1 := [[0, 4, 3, 0, 1]]
  D2 := [[0, 4, 3, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_124_5 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨124, by decide⟩
  m := 1
  T1 := T147_124
  T2 := Q2.T147_124_2
  h1 := (1,0,4,1,2)
  h2 := (1,0,4,1,4)
  D1 := [[1, 0, 4, 1, 1]]
  D2 := [[1, 0, 4, 1, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_124_6 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨124, by decide⟩
  m := 1
  T1 := T147_124
  T2 := Q2.T147_124_2
  h1 := (1,1,1,1,0)
  h2 := (1,1,1,1,3)
  D1 := [[1, 1, 1, 0, 4]]
  D2 := [[1, 1, 1, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_124_7 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨124, by decide⟩
  m := 1
  T1 := T147_124
  T2 := Q2.T147_124_2
  h1 := (1,2,3,1,0)
  h2 := (1,2,3,1,4)
  D1 := [[1, 2, 3, 4, 0]]
  D2 := [[1, 2, 3, 4, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_124_9 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨124, by decide⟩
  m := 1
  T1 := T147_124
  T2 := Q2.T147_124_2
  h1 := (1,4,2,1,1)
  h2 := (1,4,2,1,2)
  D1 := [[1, 4, 2, 2, 1]]
  D2 := [[1, 4, 2, 2, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_124_10 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨124, by decide⟩
  m := 1
  T1 := T147_124
  T2 := Q2.T147_124_2
  h1 := (2,0,3,2,0)
  h2 := (2,0,3,2,4)
  D1 := [[2, 0, 3, 2, 1]]
  D2 := [[2, 0, 3, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_124_12 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨124, by decide⟩
  m := 1
  T1 := T147_124
  T2 := Q2.T147_124_2
  h1 := (2,2,2,2,1)
  h2 := (2,2,2,2,2)
  D1 := [[2, 2, 2, 3, 4]]
  D2 := [[2, 2, 2, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_124_13 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨124, by decide⟩
  m := 1
  T1 := T147_124
  T2 := Q2.T147_124_2
  h1 := (2,3,4,2,2)
  h2 := (2,3,4,2,4)
  D1 := [[2, 3, 4, 1, 0]]
  D2 := [[2, 3, 4, 1, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_124_14 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨124, by decide⟩
  m := 1
  T1 := T147_124
  T2 := Q2.T147_124_2
  h1 := (2,4,1,2,0)
  h2 := (2,4,1,2,3)
  D1 := [[2, 4, 1, 4, 4]]
  D2 := [[2, 4, 1, 4, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_124_15 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨124, by decide⟩
  m := 1
  T1 := T147_124
  T2 := Q2.T147_124_2
  h1 := (3,0,2,3,4)
  h2 := (3,0,2,3,0)
  D1 := [[3, 0, 2, 3, 0]]
  D2 := [[3, 0, 2, 3, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_124_16 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨124, by decide⟩
  m := 1
  T1 := T147_124
  T2 := Q2.T147_124_2
  h1 := (3,1,4,3,0)
  h2 := (3,1,4,3,2)
  D1 := [[3, 1, 4, 0, 3]]
  D2 := [[3, 1, 4, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_124_17 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨124, by decide⟩
  m := 1
  T1 := T147_124
  T2 := Q2.T147_124_2
  h1 := (3,2,1,3,3)
  h2 := (3,2,1,3,1)
  D1 := [[3, 2, 1, 2, 4]]
  D2 := [[3, 2, 1, 2, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_124_18 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨124, by decide⟩
  m := 1
  T1 := T147_124
  T2 := Q2.T147_124_2
  h1 := (3,3,3,3,3)
  h2 := (3,3,3,3,2)
  D1 := [[3, 3, 3, 4, 3]]
  D2 := [[3, 3, 3, 4, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_124_20 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨124, by decide⟩
  m := 1
  T1 := T147_124
  T2 := Q2.T147_124_2
  h1 := (4,0,1,4,4)
  h2 := (4,0,1,4,2)
  D1 := [[4, 0, 1, 4, 3]]
  D2 := [[4, 0, 1, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_124_21 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨124, by decide⟩
  m := 1
  T1 := T147_124
  T2 := Q2.T147_124_2
  h1 := (4,1,3,4,4)
  h2 := (4,1,3,4,3)
  D1 := [[4, 1, 3, 0, 0]]
  D2 := [[4, 1, 3, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_124_23 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨124, by decide⟩
  m := 1
  T1 := T147_124
  T2 := Q2.T147_124_2
  h1 := (4,3,2,4,0)
  h2 := (4,3,2,4,1)
  D1 := [[4, 3, 2, 2, 3]]
  D2 := [[4, 3, 2, 2, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_124_24 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨124, by decide⟩
  m := 1
  T1 := T147_124
  T2 := Q2.T147_124_2
  h1 := (4,4,4,4,1)
  h2 := (4,4,4,4,3)
  D1 := [[4, 4, 4, 3, 4]]
  D2 := [[4, 4, 4, 3, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_127_1 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨127, by decide⟩
  m := 1
  T1 := T147_127
  T2 := Q2.T147_127_2
  h1 := (0,1,2,0,4)
  h2 := (0,1,2,0,0)
  D1 := [[0, 1, 2, 0, 2]]
  D2 := [[0, 1, 2, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_127_2 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨127, by decide⟩
  m := 1
  T1 := T147_127
  T2 := Q2.T147_127_2
  h1 := (0,2,4,0,0)
  h2 := (0,2,4,0,2)
  D1 := [[0, 2, 4, 0, 2]]
  D2 := [[0, 2, 4, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_127_3 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨127, by decide⟩
  m := 1
  T1 := T147_127
  T2 := Q2.T147_127_2
  h1 := (0,3,1,0,3)
  h2 := (0,3,1,0,1)
  D1 := [[0, 3, 1, 0, 0]]
  D2 := [[0, 3, 1, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_127_4 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨127, by decide⟩
  m := 1
  T1 := T147_127
  T2 := Q2.T147_127_2
  h1 := (0,4,3,0,3)
  h2 := (0,4,3,0,2)
  D1 := [[0, 4, 3, 0, 1]]
  D2 := [[0, 4, 3, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_127_5 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨127, by decide⟩
  m := 1
  T1 := T147_127
  T2 := Q2.T147_127_2
  h1 := (1,0,2,4,4)
  h2 := (1,0,2,4,0)
  D1 := [[1, 0, 2, 4, 0]]
  D2 := [[1, 0, 2, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_127_6 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨127, by decide⟩
  m := 1
  T1 := T147_127
  T2 := Q2.T147_127_2
  h1 := (1,1,4,4,0)
  h2 := (1,1,4,4,2)
  D1 := [[1, 1, 4, 3, 3]]
  D2 := [[1, 1, 4, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_127_7 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨127, by decide⟩
  m := 1
  T1 := T147_127
  T2 := Q2.T147_127_2
  h1 := (1,2,1,4,3)
  h2 := (1,2,1,4,1)
  D1 := [[1, 2, 1, 2, 4]]
  D2 := [[1, 2, 1, 2, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_127_8 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨127, by decide⟩
  m := 1
  T1 := T147_127
  T2 := Q2.T147_127_2
  h1 := (1,3,3,4,3)
  h2 := (1,3,3,4,2)
  D1 := [[1, 3, 3, 1, 3]]
  D2 := [[1, 3, 3, 1, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_127_10 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨127, by decide⟩
  m := 1
  T1 := T147_127
  T2 := Q2.T147_127_2
  h1 := (2,0,4,3,2)
  h2 := (2,0,4,3,4)
  D1 := [[2, 0, 4, 3, 1]]
  D2 := [[2, 0, 4, 3, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_127_11 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨127, by decide⟩
  m := 1
  T1 := T147_127
  T2 := Q2.T147_127_2
  h1 := (2,1,1,3,0)
  h2 := (2,1,1,3,3)
  D1 := [[2, 1, 1, 1, 1]]
  D2 := [[2, 1, 1, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_127_12 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨127, by decide⟩
  m := 1
  T1 := T147_127
  T2 := Q2.T147_127_2
  h1 := (2,2,3,3,0)
  h2 := (2,2,3,3,4)
  D1 := [[2, 2, 3, 4, 4]]
  D2 := [[2, 2, 3, 4, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_127_14 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨127, by decide⟩
  m := 1
  T1 := T147_127
  T2 := Q2.T147_127_2
  h1 := (2,4,2,3,1)
  h2 := (2,4,2,3,2)
  D1 := [[2, 4, 2, 0, 4]]
  D2 := [[2, 4, 2, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_127_15 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨127, by decide⟩
  m := 1
  T1 := T147_127
  T2 := Q2.T147_127_2
  h1 := (3,0,1,2,4)
  h2 := (3,0,1,2,2)
  D1 := [[3, 0, 1, 2, 3]]
  D2 := [[3, 0, 1, 2, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_127_16 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨127, by decide⟩
  m := 1
  T1 := T147_127
  T2 := Q2.T147_127_2
  h1 := (3,1,3,2,4)
  h2 := (3,1,3,2,3)
  D1 := [[3, 1, 3, 4, 1]]
  D2 := [[3, 1, 3, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_127_18 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨127, by decide⟩
  m := 1
  T1 := T147_127
  T2 := Q2.T147_127_2
  h1 := (3,3,2,2,0)
  h2 := (3,3,2,2,1)
  D1 := [[3, 3, 2, 3, 1]]
  D2 := [[3, 3, 2, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_127_19 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨127, by decide⟩
  m := 1
  T1 := T147_127
  T2 := Q2.T147_127_2
  h1 := (3,4,4,2,1)
  h2 := (3,4,4,2,3)
  D1 := [[3, 4, 4, 0, 3]]
  D2 := [[3, 4, 4, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_127_20 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨127, by decide⟩
  m := 1
  T1 := T147_127
  T2 := Q2.T147_127_2
  h1 := (4,0,3,1,0)
  h2 := (4,0,3,1,4)
  D1 := [[4, 0, 3, 1, 1]]
  D2 := [[4, 0, 3, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_127_22 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨127, by decide⟩
  m := 1
  T1 := T147_127
  T2 := Q2.T147_127_2
  h1 := (4,2,2,1,1)
  h2 := (4,2,2,1,2)
  D1 := [[4, 2, 2, 3, 3]]
  D2 := [[4, 2, 2, 3, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_127_23 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨127, by decide⟩
  m := 1
  T1 := T147_127
  T2 := Q2.T147_127_2
  h1 := (4,3,4,1,2)
  h2 := (4,3,4,1,4)
  D1 := [[4, 3, 4, 4, 1]]
  D2 := [[4, 3, 4, 4, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_127_24 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨127, by decide⟩
  m := 1
  T1 := T147_127
  T2 := Q2.T147_127_2
  h1 := (4,4,1,1,0)
  h2 := (4,4,1,1,3)
  D1 := [[4, 4, 1, 0, 2]]
  D2 := [[4, 4, 1, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_128_1 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨128, by decide⟩
  m := 1
  T1 := T147_128
  T2 := Q2.T147_128_2
  h1 := (0,1,4,0,2)
  h2 := (0,1,4,0,0)
  D1 := [[0, 1, 4, 0, 3]]
  D2 := [[0, 1, 4, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_128_2 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨128, by decide⟩
  m := 1
  T1 := T147_128
  T2 := Q2.T147_128_2
  h1 := (0,2,3,0,3)
  h2 := (0,2,3,0,4)
  D1 := [[0, 2, 3, 0, 2]]
  D2 := [[0, 2, 3, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_128_3 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨128, by decide⟩
  m := 1
  T1 := T147_128
  T2 := Q2.T147_128_2
  h1 := (0,3,2,0,3)
  h2 := (0,3,2,0,2)
  D1 := [[0, 3, 2, 0, 2]]
  D2 := [[0, 3, 2, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_128_4 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨128, by decide⟩
  m := 1
  T1 := T147_128
  T2 := Q2.T147_128_2
  h1 := (0,4,1,0,2)
  h2 := (0,4,1,0,4)
  D1 := [[0, 4, 1, 0, 3]]
  D2 := [[0, 4, 1, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_128_5 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨128, by decide⟩
  m := 1
  T1 := T147_128
  T2 := Q2.T147_128_2
  h1 := (1,0,2,3,1)
  h2 := (1,0,2,3,0)
  D1 := [[1, 0, 2, 3, 3]]
  D2 := [[1, 0, 2, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_128_6 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨128, by decide⟩
  m := 1
  T1 := T147_128
  T2 := Q2.T147_128_2
  h1 := (1,1,1,3,0)
  h2 := (1,1,1,3,2)
  D1 := [[1, 1, 1, 2, 2]]
  D2 := [[1, 1, 1, 2, 4]]
  bind1 := by decide
  bind2 := by decide

end LeanDring.P5Presentation
