/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.Twin1.ColCert
import LeanDring.P5.Data.EntryK.C044
import LeanDring.P5.Data.EntryK.C014

/-!
# Species-table cell data, stage 2 — column-data-divergent columns

Per-column certified exponent-vector data (`ColCert`/`ColCertDiv`) with kernel
`decide` bindings. Emitted; the embedded lists are what the kernel certifies.
cdd tier, chunk 36: 60 columns.
-/

-- machine-emitted data: silence style linters (generated long lines, file-level options)
set_option linter.style.longLine false

namespace LeanDring.P5Presentation

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

def colCertDiv_147_143_8 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨143, by decide⟩
  m := 1
  T1 := T147_143
  T2 := Q2.T147_143_2
  h1 := (1,3,1,0,3)
  h2 := (1,3,1,0,1)
  D1 := [[1, 3, 1, 2, 3]]
  D2 := [[1, 3, 1, 2, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_143_9 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨143, by decide⟩
  m := 1
  T1 := T147_143
  T2 := Q2.T147_143_2
  h1 := (1,4,3,0,3)
  h2 := (1,4,3,0,2)
  D1 := [[1, 4, 3, 1, 0]]
  D2 := [[1, 4, 3, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_143_11 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨143, by decide⟩
  m := 1
  T1 := T147_143
  T2 := Q2.T147_143_2
  h1 := (2,1,2,0,4)
  h2 := (2,1,2,0,0)
  D1 := [[2, 1, 2, 3, 0]]
  D2 := [[2, 1, 2, 3, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_143_12 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨143, by decide⟩
  m := 1
  T1 := T147_143
  T2 := Q2.T147_143_2
  h1 := (2,2,4,0,0)
  h2 := (2,2,4,0,2)
  D1 := [[2, 2, 4, 1, 3]]
  D2 := [[2, 2, 4, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_143_13 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨143, by decide⟩
  m := 1
  T1 := T147_143
  T2 := Q2.T147_143_2
  h1 := (2,3,1,0,3)
  h2 := (2,3,1,0,1)
  D1 := [[2, 3, 1, 4, 4]]
  D2 := [[2, 3, 1, 4, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_143_14 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨143, by decide⟩
  m := 1
  T1 := T147_143
  T2 := Q2.T147_143_2
  h1 := (2,4,3,0,3)
  h2 := (2,4,3,0,2)
  D1 := [[2, 4, 3, 2, 3]]
  D2 := [[2, 4, 3, 2, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_143_16 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨143, by decide⟩
  m := 1
  T1 := T147_143
  T2 := Q2.T147_143_2
  h1 := (3,1,2,0,4)
  h2 := (3,1,2,0,0)
  D1 := [[3, 1, 2, 2, 3]]
  D2 := [[3, 1, 2, 2, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_143_17 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨143, by decide⟩
  m := 1
  T1 := T147_143
  T2 := Q2.T147_143_2
  h1 := (3,2,4,0,0)
  h2 := (3,2,4,0,2)
  D1 := [[3, 2, 4, 4, 4]]
  D2 := [[3, 2, 4, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_143_18 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨143, by decide⟩
  m := 1
  T1 := T147_143
  T2 := Q2.T147_143_2
  h1 := (3,3,1,0,3)
  h2 := (3,3,1,0,1)
  D1 := [[3, 3, 1, 1, 3]]
  D2 := [[3, 3, 1, 1, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_143_19 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨143, by decide⟩
  m := 1
  T1 := T147_143
  T2 := Q2.T147_143_2
  h1 := (3,4,3,0,3)
  h2 := (3,4,3,0,2)
  D1 := [[3, 4, 3, 3, 0]]
  D2 := [[3, 4, 3, 3, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_143_21 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨143, by decide⟩
  m := 1
  T1 := T147_143
  T2 := Q2.T147_143_2
  h1 := (4,1,2,0,4)
  h2 := (4,1,2,0,0)
  D1 := [[4, 1, 2, 1, 2]]
  D2 := [[4, 1, 2, 1, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_143_22 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨143, by decide⟩
  m := 1
  T1 := T147_143
  T2 := Q2.T147_143_2
  h1 := (4,2,4,0,0)
  h2 := (4,2,4,0,2)
  D1 := [[4, 2, 4, 2, 2]]
  D2 := [[4, 2, 4, 2, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_143_23 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨143, by decide⟩
  m := 1
  T1 := T147_143
  T2 := Q2.T147_143_2
  h1 := (4,3,1,0,3)
  h2 := (4,3,1,0,1)
  D1 := [[4, 3, 1, 3, 0]]
  D2 := [[4, 3, 1, 3, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_143_24 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨143, by decide⟩
  m := 1
  T1 := T147_143
  T2 := Q2.T147_143_2
  h1 := (4,4,3,0,3)
  h2 := (4,4,3,0,2)
  D1 := [[4, 4, 3, 4, 1]]
  D2 := [[4, 4, 3, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_144_1 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨144, by decide⟩
  m := 1
  T1 := T147_144
  T2 := Q2.T147_144_2
  h1 := (0,1,3,0,2)
  h2 := (0,1,3,0,3)
  D1 := [[0, 1, 3, 0, 4]]
  D2 := [[0, 1, 3, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_144_2 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨144, by decide⟩
  m := 1
  T1 := T147_144
  T2 := Q2.T147_144_2
  h1 := (0,2,1,0,2)
  h2 := (0,2,1,0,4)
  D1 := [[0, 2, 1, 0, 0]]
  D2 := [[0, 2, 1, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_144_3 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨144, by decide⟩
  m := 1
  T1 := T147_144
  T2 := Q2.T147_144_2
  h1 := (0,3,4,0,0)
  h2 := (0,3,4,0,3)
  D1 := [[0, 3, 4, 0, 3]]
  D2 := [[0, 3, 4, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_144_4 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨144, by decide⟩
  m := 1
  T1 := T147_144
  T2 := Q2.T147_144_2
  h1 := (0,4,2,0,1)
  h2 := (0,4,2,0,0)
  D1 := [[0, 4, 2, 0, 3]]
  D2 := [[0, 4, 2, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_144_6 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨144, by decide⟩
  m := 1
  T1 := T147_144
  T2 := Q2.T147_144_2
  h1 := (1,1,3,0,2)
  h2 := (1,1,3,0,3)
  D1 := [[1, 1, 3, 4, 0]]
  D2 := [[1, 1, 3, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_144_7 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨144, by decide⟩
  m := 1
  T1 := T147_144
  T2 := Q2.T147_144_2
  h1 := (1,2,1,0,2)
  h2 := (1,2,1,0,4)
  D1 := [[1, 2, 1, 3, 2]]
  D2 := [[1, 2, 1, 3, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_144_8 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨144, by decide⟩
  m := 1
  T1 := T147_144
  T2 := Q2.T147_144_2
  h1 := (1,3,4,0,0)
  h2 := (1,3,4,0,3)
  D1 := [[1, 3, 4, 2, 1]]
  D2 := [[1, 3, 4, 2, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_144_9 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨144, by decide⟩
  m := 1
  T1 := T147_144
  T2 := Q2.T147_144_2
  h1 := (1,4,2,0,1)
  h2 := (1,4,2,0,0)
  D1 := [[1, 4, 2, 1, 2]]
  D2 := [[1, 4, 2, 1, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_144_11 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨144, by decide⟩
  m := 1
  T1 := T147_144
  T2 := Q2.T147_144_2
  h1 := (2,1,3,0,2)
  h2 := (2,1,3,0,3)
  D1 := [[2, 1, 3, 3, 2]]
  D2 := [[2, 1, 3, 3, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_144_12 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨144, by decide⟩
  m := 1
  T1 := T147_144
  T2 := Q2.T147_144_2
  h1 := (2,2,1,0,2)
  h2 := (2,2,1,0,4)
  D1 := [[2, 2, 1, 1, 1]]
  D2 := [[2, 2, 1, 1, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_144_13 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨144, by decide⟩
  m := 1
  T1 := T147_144
  T2 := Q2.T147_144_2
  h1 := (2,3,4,0,0)
  h2 := (2,3,4,0,3)
  D1 := [[2, 3, 4, 4, 2]]
  D2 := [[2, 3, 4, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_144_14 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨144, by decide⟩
  m := 1
  T1 := T147_144
  T2 := Q2.T147_144_2
  h1 := (2,4,2,0,1)
  h2 := (2,4,2,0,0)
  D1 := [[2, 4, 2, 2, 0]]
  D2 := [[2, 4, 2, 2, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_144_16 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨144, by decide⟩
  m := 1
  T1 := T147_144
  T2 := Q2.T147_144_2
  h1 := (3,1,3,0,2)
  h2 := (3,1,3,0,3)
  D1 := [[3, 1, 3, 2, 0]]
  D2 := [[3, 1, 3, 2, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_144_17 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨144, by decide⟩
  m := 1
  T1 := T147_144
  T2 := Q2.T147_144_2
  h1 := (3,2,1,0,2)
  h2 := (3,2,1,0,4)
  D1 := [[3, 2, 1, 4, 2]]
  D2 := [[3, 2, 1, 4, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_144_18 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨144, by decide⟩
  m := 1
  T1 := T147_144
  T2 := Q2.T147_144_2
  h1 := (3,3,4,0,0)
  h2 := (3,3,4,0,3)
  D1 := [[3, 3, 4, 1, 1]]
  D2 := [[3, 3, 4, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_144_19 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨144, by decide⟩
  m := 1
  T1 := T147_144
  T2 := Q2.T147_144_2
  h1 := (3,4,2,0,1)
  h2 := (3,4,2,0,0)
  D1 := [[3, 4, 2, 3, 2]]
  D2 := [[3, 4, 2, 3, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_144_21 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨144, by decide⟩
  m := 1
  T1 := T147_144
  T2 := Q2.T147_144_2
  h1 := (4,1,3,0,2)
  h2 := (4,1,3,0,3)
  D1 := [[4, 1, 3, 1, 4]]
  D2 := [[4, 1, 3, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_144_22 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨144, by decide⟩
  m := 1
  T1 := T147_144
  T2 := Q2.T147_144_2
  h1 := (4,2,1,0,2)
  h2 := (4,2,1,0,4)
  D1 := [[4, 2, 1, 2, 0]]
  D2 := [[4, 2, 1, 2, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_144_23 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨144, by decide⟩
  m := 1
  T1 := T147_144
  T2 := Q2.T147_144_2
  h1 := (4,3,4,0,0)
  h2 := (4,3,4,0,3)
  D1 := [[4, 3, 4, 3, 3]]
  D2 := [[4, 3, 4, 3, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_144_24 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨144, by decide⟩
  m := 1
  T1 := T147_144
  T2 := Q2.T147_144_2
  h1 := (4,4,2,0,1)
  h2 := (4,4,2,0,0)
  D1 := [[4, 4, 2, 4, 3]]
  D2 := [[4, 4, 2, 4, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_57_28_5 : ColCertDiv where
  rK := ⟨57, by decide⟩
  rH := ⟨28, by decide⟩
  m := 5
  T1 := T57_28
  T2 := Q2.T57_28_2
  h1 := (0,1,4,4,2)
  h2 := (0,1,4,4,0)
  D1 := [[1, 4, 3], [1, 4, 3], [1, 4, 3], [1, 4, 3], [1, 4, 3]]
  D2 := [[1, 4, 0], [1, 4, 0], [1, 4, 0], [1, 4, 0], [1, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_57_28_10 : ColCertDiv where
  rK := ⟨57, by decide⟩
  rH := ⟨28, by decide⟩
  m := 5
  T1 := T57_28
  T2 := Q2.T57_28_2
  h1 := (0,2,3,3,3)
  h2 := (0,2,3,3,4)
  D1 := [[2, 3, 2], [2, 3, 2], [2, 3, 2], [2, 3, 2], [2, 3, 2]]
  D2 := [[2, 3, 1], [2, 3, 1], [2, 3, 1], [2, 3, 1], [2, 3, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_57_28_15 : ColCertDiv where
  rK := ⟨57, by decide⟩
  rH := ⟨28, by decide⟩
  m := 5
  T1 := T57_28
  T2 := Q2.T57_28_2
  h1 := (0,3,2,2,3)
  h2 := (0,3,2,2,2)
  D1 := [[3, 2, 2], [3, 2, 2], [3, 2, 2], [3, 2, 2], [3, 2, 2]]
  D2 := [[3, 2, 3], [3, 2, 3], [3, 2, 3], [3, 2, 3], [3, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_57_28_20 : ColCertDiv where
  rK := ⟨57, by decide⟩
  rH := ⟨28, by decide⟩
  m := 5
  T1 := T57_28
  T2 := Q2.T57_28_2
  h1 := (0,4,1,1,2)
  h2 := (0,4,1,1,4)
  D1 := [[4, 1, 3], [4, 1, 3], [4, 1, 3], [4, 1, 3], [4, 1, 3]]
  D2 := [[4, 1, 1], [4, 1, 1], [4, 1, 1], [4, 1, 1], [4, 1, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_57_33_5 : ColCertDiv where
  rK := ⟨57, by decide⟩
  rH := ⟨33, by decide⟩
  m := 5
  T1 := T57_33
  T2 := Q2.T57_33_2
  h1 := (0,1,2,4,0)
  h2 := (0,1,2,4,3)
  D1 := [[1, 2, 3], [1, 2, 3], [1, 2, 3], [1, 2, 3], [1, 2, 3]]
  D2 := [[1, 2, 0], [1, 2, 0], [1, 2, 0], [1, 2, 0], [1, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_57_33_10 : ColCertDiv where
  rK := ⟨57, by decide⟩
  rH := ⟨33, by decide⟩
  m := 5
  T1 := T57_33
  T2 := Q2.T57_33_2
  h1 := (0,2,4,3,2)
  h2 := (0,2,4,3,3)
  D1 := [[2, 4, 4], [2, 4, 4], [2, 4, 4], [2, 4, 4], [2, 4, 4]]
  D2 := [[2, 4, 3], [2, 4, 3], [2, 4, 3], [2, 4, 3], [2, 4, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_57_33_15 : ColCertDiv where
  rK := ⟨57, by decide⟩
  rH := ⟨33, by decide⟩
  m := 5
  T1 := T57_33
  T2 := Q2.T57_33_2
  h1 := (0,3,1,2,1)
  h2 := (0,3,1,2,0)
  D1 := [[3, 1, 3], [3, 1, 3], [3, 1, 3], [3, 1, 3], [3, 1, 3]]
  D2 := [[3, 1, 4], [3, 1, 4], [3, 1, 4], [3, 1, 4], [3, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_57_33_20 : ColCertDiv where
  rK := ⟨57, by decide⟩
  rH := ⟨33, by decide⟩
  m := 5
  T1 := T57_33
  T2 := Q2.T57_33_2
  h1 := (0,4,3,1,2)
  h2 := (0,4,3,1,4)
  D1 := [[4, 3, 0], [4, 3, 0], [4, 3, 0], [4, 3, 0], [4, 3, 0]]
  D2 := [[4, 3, 3], [4, 3, 3], [4, 3, 3], [4, 3, 3], [4, 3, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_57_38_5 : ColCertDiv where
  rK := ⟨57, by decide⟩
  rH := ⟨38, by decide⟩
  m := 5
  T1 := T57_38
  T2 := Q2.T57_38_2
  h1 := (0,1,3,4,1)
  h2 := (0,1,3,4,4)
  D1 := [[1, 3, 1], [1, 3, 1], [1, 3, 1], [1, 3, 1], [1, 3, 1]]
  D2 := [[1, 3, 3], [1, 3, 3], [1, 3, 3], [1, 3, 3], [1, 3, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_57_38_10 : ColCertDiv where
  rK := ⟨57, by decide⟩
  rH := ⟨38, by decide⟩
  m := 5
  T1 := T57_38
  T2 := Q2.T57_38_2
  h1 := (0,2,1,3,0)
  h2 := (0,2,1,3,1)
  D1 := [[2, 1, 4], [2, 1, 4], [2, 1, 4], [2, 1, 4], [2, 1, 4]]
  D2 := [[2, 1, 3], [2, 1, 3], [2, 1, 3], [2, 1, 3], [2, 1, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_57_38_15 : ColCertDiv where
  rK := ⟨57, by decide⟩
  rH := ⟨38, by decide⟩
  m := 5
  T1 := T57_38
  T2 := Q2.T57_38_2
  h1 := (0,3,4,2,2)
  h2 := (0,3,4,2,1)
  D1 := [[3, 4, 4], [3, 4, 4], [3, 4, 4], [3, 4, 4], [3, 4, 4]]
  D2 := [[3, 4, 0], [3, 4, 0], [3, 4, 0], [3, 4, 0], [3, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_57_38_20 : ColCertDiv where
  rK := ⟨57, by decide⟩
  rH := ⟨38, by decide⟩
  m := 5
  T1 := T57_38
  T2 := Q2.T57_38_2
  h1 := (0,4,2,1,2)
  h2 := (0,4,2,1,4)
  D1 := [[4, 2, 1], [4, 2, 1], [4, 2, 1], [4, 2, 1], [4, 2, 1]]
  D2 := [[4, 2, 4], [4, 2, 4], [4, 2, 4], [4, 2, 4], [4, 2, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_57_43_5 : ColCertDiv where
  rK := ⟨57, by decide⟩
  rH := ⟨43, by decide⟩
  m := 5
  T1 := T57_43
  T2 := Q2.T57_43_2
  h1 := (0,1,1,4,4)
  h2 := (0,1,1,4,2)
  D1 := [[1, 1, 4], [1, 1, 4], [1, 1, 4], [1, 1, 4], [1, 1, 4]]
  D2 := [[1, 1, 1], [1, 1, 1], [1, 1, 1], [1, 1, 1], [1, 1, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_57_43_10 : ColCertDiv where
  rK := ⟨57, by decide⟩
  rH := ⟨43, by decide⟩
  m := 5
  T1 := T57_43
  T2 := Q2.T57_43_2
  h1 := (0,2,2,3,4)
  h2 := (0,2,2,3,0)
  D1 := [[2, 2, 2], [2, 2, 2], [2, 2, 2], [2, 2, 2], [2, 2, 2]]
  D2 := [[2, 2, 1], [2, 2, 1], [2, 2, 1], [2, 2, 1], [2, 2, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_57_43_15 : ColCertDiv where
  rK := ⟨57, by decide⟩
  rH := ⟨43, by decide⟩
  m := 5
  T1 := T57_43
  T2 := Q2.T57_43_2
  h1 := (0,3,3,2,0)
  h2 := (0,3,3,2,4)
  D1 := [[3, 3, 4], [3, 3, 4], [3, 3, 4], [3, 3, 4], [3, 3, 4]]
  D2 := [[3, 3, 0], [3, 3, 0], [3, 3, 0], [3, 3, 0], [3, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_57_43_20 : ColCertDiv where
  rK := ⟨57, by decide⟩
  rH := ⟨43, by decide⟩
  m := 5
  T1 := T57_43
  T2 := Q2.T57_43_2
  h1 := (0,4,4,1,2)
  h2 := (0,4,4,1,4)
  D1 := [[4, 4, 0], [4, 4, 0], [4, 4, 0], [4, 4, 0], [4, 4, 0]]
  D2 := [[4, 4, 3], [4, 4, 3], [4, 4, 3], [4, 4, 3], [4, 4, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_57_48_5 : ColCertDiv where
  rK := ⟨57, by decide⟩
  rH := ⟨48, by decide⟩
  m := 5
  T1 := T57_48
  T2 := Q2.T57_48_2
  h1 := (0,1,0,4,3)
  h2 := (0,1,0,4,1)
  D1 := [[1, 0, 4], [1, 0, 4], [1, 0, 4], [1, 0, 4], [1, 0, 4]]
  D2 := [[1, 0, 1], [1, 0, 1], [1, 0, 1], [1, 0, 1], [1, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_57_48_10 : ColCertDiv where
  rK := ⟨57, by decide⟩
  rH := ⟨48, by decide⟩
  m := 5
  T1 := T57_48
  T2 := Q2.T57_48_2
  h1 := (0,2,0,3,1)
  h2 := (0,2,0,3,2)
  D1 := [[2, 0, 3], [2, 0, 3], [2, 0, 3], [2, 0, 3], [2, 0, 3]]
  D2 := [[2, 0, 2], [2, 0, 2], [2, 0, 2], [2, 0, 2], [2, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_57_48_15 : ColCertDiv where
  rK := ⟨57, by decide⟩
  rH := ⟨48, by decide⟩
  m := 5
  T1 := T57_48
  T2 := Q2.T57_48_2
  h1 := (0,3,0,2,4)
  h2 := (0,3,0,2,3)
  D1 := [[3, 0, 2], [3, 0, 2], [3, 0, 2], [3, 0, 2], [3, 0, 2]]
  D2 := [[3, 0, 3], [3, 0, 3], [3, 0, 3], [3, 0, 3], [3, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_57_48_20 : ColCertDiv where
  rK := ⟨57, by decide⟩
  rH := ⟨48, by decide⟩
  m := 5
  T1 := T57_48
  T2 := Q2.T57_48_2
  h1 := (0,4,0,1,2)
  h2 := (0,4,0,1,4)
  D1 := [[4, 0, 1], [4, 0, 1], [4, 0, 1], [4, 0, 1], [4, 0, 1]]
  D2 := [[4, 0, 4], [4, 0, 4], [4, 0, 4], [4, 0, 4], [4, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_58_28_5 : ColCertDiv where
  rK := ⟨58, by decide⟩
  rH := ⟨28, by decide⟩
  m := 5
  T1 := T58_28
  T2 := Q2.T58_28_2
  h1 := (0,1,4,4,2)
  h2 := (0,1,4,4,0)
  D1 := [[1, 4, 1], [1, 4, 1], [1, 4, 1], [1, 4, 1], [1, 4, 1]]
  D2 := [[1, 4, 3], [1, 4, 3], [1, 4, 3], [1, 4, 3], [1, 4, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_58_28_10 : ColCertDiv where
  rK := ⟨58, by decide⟩
  rH := ⟨28, by decide⟩
  m := 5
  T1 := T58_28
  T2 := Q2.T58_28_2
  h1 := (0,2,3,3,3)
  h2 := (0,2,3,3,4)
  D1 := [[2, 3, 3], [2, 3, 3], [2, 3, 3], [2, 3, 3], [2, 3, 3]]
  D2 := [[2, 3, 2], [2, 3, 2], [2, 3, 2], [2, 3, 2], [2, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_58_28_15 : ColCertDiv where
  rK := ⟨58, by decide⟩
  rH := ⟨28, by decide⟩
  m := 5
  T1 := T58_28
  T2 := Q2.T58_28_2
  h1 := (0,3,2,2,3)
  h2 := (0,3,2,2,2)
  D1 := [[3, 2, 1], [3, 2, 1], [3, 2, 1], [3, 2, 1], [3, 2, 1]]
  D2 := [[3, 2, 2], [3, 2, 2], [3, 2, 2], [3, 2, 2], [3, 2, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_58_28_20 : ColCertDiv where
  rK := ⟨58, by decide⟩
  rH := ⟨28, by decide⟩
  m := 5
  T1 := T58_28
  T2 := Q2.T58_28_2
  h1 := (0,4,1,1,2)
  h2 := (0,4,1,1,4)
  D1 := [[4, 1, 0], [4, 1, 0], [4, 1, 0], [4, 1, 0], [4, 1, 0]]
  D2 := [[4, 1, 3], [4, 1, 3], [4, 1, 3], [4, 1, 3], [4, 1, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_58_33_5 : ColCertDiv where
  rK := ⟨58, by decide⟩
  rH := ⟨33, by decide⟩
  m := 5
  T1 := T58_33
  T2 := Q2.T58_33_2
  h1 := (0,1,2,4,0)
  h2 := (0,1,2,4,3)
  D1 := [[1, 2, 3], [1, 2, 3], [1, 2, 3], [1, 2, 3], [1, 2, 3]]
  D2 := [[1, 2, 0], [1, 2, 0], [1, 2, 0], [1, 2, 0], [1, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_58_33_10 : ColCertDiv where
  rK := ⟨58, by decide⟩
  rH := ⟨33, by decide⟩
  m := 5
  T1 := T58_33
  T2 := Q2.T58_33_2
  h1 := (0,2,4,3,2)
  h2 := (0,2,4,3,3)
  D1 := [[2, 4, 4], [2, 4, 4], [2, 4, 4], [2, 4, 4], [2, 4, 4]]
  D2 := [[2, 4, 3], [2, 4, 3], [2, 4, 3], [2, 4, 3], [2, 4, 3]]
  bind1 := by decide
  bind2 := by decide

end LeanDring.P5Presentation
