/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.Twin1.ColCert
import LeanDring.P5.Data.EntryK.C031

/-!
# Species-table cell data, stage 2 — column-data-divergent columns

Per-column certified exponent-vector data (`ColCert`/`ColCertDiv`) with kernel
`decide` bindings. Emitted; the embedded lists are what the kernel certifies.
cdd tier, chunk 9: 60 columns.
-/

-- machine-emitted data: silence style linters (generated long lines, file-level options)
set_option linter.style.longLine false

namespace LeanDring.P5Presentation

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

def colCertDiv_124_2_4 : ColCertDiv where
  rK := ⟨124, by decide⟩
  rH := ⟨2, by decide⟩
  m := 5
  T1 := T124_2
  T2 := Q2.T124_2_2
  h1 := (4,0,1,4,1)
  h2 := (4,0,1,4,1)
  D1 := [[4, 0, 0, 2], [4, 0, 0, 2], [4, 0, 0, 2], [4, 0, 0, 2], [4, 0, 0, 2]]
  D2 := [[4, 0, 0, 4], [4, 0, 0, 4], [4, 0, 0, 4], [4, 0, 0, 4], [4, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_124_20_5 : ColCertDiv where
  rK := ⟨124, by decide⟩
  rH := ⟨20, by decide⟩
  m := 5
  T1 := T124_20
  T2 := Q2.T124_20_2
  h1 := (1,0,4,1,1)
  h2 := (1,0,4,1,1)
  D1 := [[1, 0, 0, 4], [1, 0, 0, 4], [1, 0, 0, 4], [1, 0, 0, 4], [1, 0, 0, 4]]
  D2 := [[1, 0, 0, 2], [1, 0, 0, 2], [1, 0, 0, 2], [1, 0, 0, 2], [1, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_124_20_10 : ColCertDiv where
  rK := ⟨124, by decide⟩
  rH := ⟨20, by decide⟩
  m := 5
  T1 := T124_20
  T2 := Q2.T124_20_2
  h1 := (2,0,3,2,3)
  h2 := (2,0,3,2,3)
  D1 := [[2, 0, 0, 3], [2, 0, 0, 3], [2, 0, 0, 3], [2, 0, 0, 3], [2, 0, 0, 3]]
  D2 := [[2, 0, 0, 4], [2, 0, 0, 4], [2, 0, 0, 4], [2, 0, 0, 4], [2, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_124_20_15 : ColCertDiv where
  rK := ⟨124, by decide⟩
  rH := ⟨20, by decide⟩
  m := 5
  T1 := T124_20
  T2 := Q2.T124_20_2
  h1 := (3,0,2,3,1)
  h2 := (3,0,2,3,1)
  D1 := [[3, 0, 0, 2], [3, 0, 0, 2], [3, 0, 0, 2], [3, 0, 0, 2], [3, 0, 0, 2]]
  D2 := [[3, 0, 0, 1], [3, 0, 0, 1], [3, 0, 0, 1], [3, 0, 0, 1], [3, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_124_20_20 : ColCertDiv where
  rK := ⟨124, by decide⟩
  rH := ⟨20, by decide⟩
  m := 5
  T1 := T124_20
  T2 := Q2.T124_20_2
  h1 := (4,0,1,4,0)
  h2 := (4,0,1,4,0)
  D1 := [[4, 0, 0, 1], [4, 0, 0, 1], [4, 0, 0, 1], [4, 0, 0, 1], [4, 0, 0, 1]]
  D2 := [[4, 0, 0, 3], [4, 0, 0, 3], [4, 0, 0, 3], [4, 0, 0, 3], [4, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_124_30_5 : ColCertDiv where
  rK := ⟨124, by decide⟩
  rH := ⟨30, by decide⟩
  m := 5
  T1 := T124_30
  T2 := Q2.T124_30_2
  h1 := (1,2,3,2,3)
  h2 := (1,2,3,2,0)
  D1 := [[1, 2, 4, 0], [1, 2, 4, 3], [1, 2, 4, 1], [1, 2, 4, 4], [1, 2, 4, 2]]
  D2 := [[1, 2, 4, 3], [1, 2, 4, 1], [1, 2, 4, 4], [1, 2, 4, 2], [1, 2, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_124_30_10 : ColCertDiv where
  rK := ⟨124, by decide⟩
  rH := ⟨30, by decide⟩
  m := 5
  T1 := T124_30
  T2 := Q2.T124_30_2
  h1 := (2,4,1,1,4)
  h2 := (2,4,1,1,3)
  D1 := [[2, 4, 1, 1], [2, 4, 1, 2], [2, 4, 1, 3], [2, 4, 1, 4], [2, 4, 1, 0]]
  D2 := [[2, 4, 1, 2], [2, 4, 1, 3], [2, 4, 1, 4], [2, 4, 1, 0], [2, 4, 1, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_124_30_20 : ColCertDiv where
  rK := ⟨124, by decide⟩
  rH := ⟨30, by decide⟩
  m := 5
  T1 := T124_30
  T2 := Q2.T124_30_2
  h1 := (4,3,2,0,4)
  h2 := (4,3,2,0,3)
  D1 := [[4, 3, 4, 0], [4, 3, 4, 2], [4, 3, 4, 4], [4, 3, 4, 1], [4, 3, 4, 3]]
  D2 := [[4, 3, 4, 3], [4, 3, 4, 0], [4, 3, 4, 2], [4, 3, 4, 4], [4, 3, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_124_33_5 : ColCertDiv where
  rK := ⟨124, by decide⟩
  rH := ⟨33, by decide⟩
  m := 5
  T1 := T124_33
  T2 := Q2.T124_33_2
  h1 := (0,1,2,4,0)
  h2 := (0,1,2,4,3)
  D1 := [[0, 1, 4, 0], [0, 1, 4, 4], [0, 1, 4, 3], [0, 1, 4, 2], [0, 1, 4, 1]]
  D2 := [[0, 1, 4, 2], [0, 1, 4, 1], [0, 1, 4, 0], [0, 1, 4, 4], [0, 1, 4, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_124_33_10 : ColCertDiv where
  rK := ⟨124, by decide⟩
  rH := ⟨33, by decide⟩
  m := 5
  T1 := T124_33
  T2 := Q2.T124_33_2
  h1 := (0,2,4,3,2)
  h2 := (0,2,4,3,3)
  D1 := [[0, 2, 3, 0], [0, 2, 3, 3], [0, 2, 3, 1], [0, 2, 3, 4], [0, 2, 3, 2]]
  D2 := [[0, 2, 3, 4], [0, 2, 3, 2], [0, 2, 3, 0], [0, 2, 3, 3], [0, 2, 3, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_124_33_15 : ColCertDiv where
  rK := ⟨124, by decide⟩
  rH := ⟨33, by decide⟩
  m := 5
  T1 := T124_33
  T2 := Q2.T124_33_2
  h1 := (0,3,1,2,1)
  h2 := (0,3,1,2,0)
  D1 := [[0, 3, 2, 0], [0, 3, 2, 2], [0, 3, 2, 4], [0, 3, 2, 1], [0, 3, 2, 3]]
  D2 := [[0, 3, 2, 1], [0, 3, 2, 3], [0, 3, 2, 0], [0, 3, 2, 2], [0, 3, 2, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_124_33_20 : ColCertDiv where
  rK := ⟨124, by decide⟩
  rH := ⟨33, by decide⟩
  m := 5
  T1 := T124_33
  T2 := Q2.T124_33_2
  h1 := (0,4,3,1,2)
  h2 := (0,4,3,1,4)
  D1 := [[0, 4, 1, 0], [0, 4, 1, 1], [0, 4, 1, 2], [0, 4, 1, 3], [0, 4, 1, 4]]
  D2 := [[0, 4, 1, 3], [0, 4, 1, 4], [0, 4, 1, 0], [0, 4, 1, 1], [0, 4, 1, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_124_39_5 : ColCertDiv where
  rK := ⟨124, by decide⟩
  rH := ⟨39, by decide⟩
  m := 5
  T1 := T124_39
  T2 := Q2.T124_39_2
  h1 := (1,4,2,3,2)
  h2 := (1,4,2,3,2)
  D1 := [[1, 4, 3, 0], [1, 4, 3, 1], [1, 4, 3, 2], [1, 4, 3, 3], [1, 4, 3, 4]]
  D2 := [[1, 4, 3, 4], [1, 4, 3, 0], [1, 4, 3, 1], [1, 4, 3, 2], [1, 4, 3, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_124_39_10 : ColCertDiv where
  rK := ⟨124, by decide⟩
  rH := ⟨39, by decide⟩
  m := 5
  T1 := T124_39
  T2 := Q2.T124_39_2
  h1 := (2,3,4,0,1)
  h2 := (2,3,4,0,2)
  D1 := [[2, 3, 2, 3], [2, 3, 2, 0], [2, 3, 2, 2], [2, 3, 2, 4], [2, 3, 2, 1]]
  D2 := [[2, 3, 2, 2], [2, 3, 2, 4], [2, 3, 2, 1], [2, 3, 2, 3], [2, 3, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_124_39_15 : ColCertDiv where
  rK := ⟨124, by decide⟩
  rH := ⟨39, by decide⟩
  m := 5
  T1 := T124_39
  T2 := Q2.T124_39_2
  h1 := (3,2,1,1,0)
  h2 := (3,2,1,1,2)
  D1 := [[3, 2, 2, 2], [3, 2, 2, 0], [3, 2, 2, 3], [3, 2, 2, 1], [3, 2, 2, 4]]
  D2 := [[3, 2, 2, 1], [3, 2, 2, 4], [3, 2, 2, 2], [3, 2, 2, 0], [3, 2, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_124_39_20 : ColCertDiv where
  rK := ⟨124, by decide⟩
  rH := ⟨39, by decide⟩
  m := 5
  T1 := T124_39
  T2 := Q2.T124_39_2
  h1 := (4,1,3,1,3)
  h2 := (4,1,3,1,1)
  D1 := [[4, 1, 3, 1], [4, 1, 3, 0], [4, 1, 3, 4], [4, 1, 3, 3], [4, 1, 3, 2]]
  D2 := [[4, 1, 3, 0], [4, 1, 3, 4], [4, 1, 3, 3], [4, 1, 3, 2], [4, 1, 3, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_124_51_5 : ColCertDiv where
  rK := ⟨124, by decide⟩
  rH := ⟨51, by decide⟩
  m := 5
  T1 := T124_51
  T2 := Q2.T124_51_2
  h1 := (1,3,0,0,3)
  h2 := (1,3,0,0,4)
  D1 := [[1, 3, 1, 4], [1, 3, 1, 1], [1, 3, 1, 3], [1, 3, 1, 0], [1, 3, 1, 2]]
  D2 := [[1, 3, 1, 0], [1, 3, 1, 2], [1, 3, 1, 4], [1, 3, 1, 1], [1, 3, 1, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_124_51_10 : ColCertDiv where
  rK := ⟨124, by decide⟩
  rH := ⟨51, by decide⟩
  m := 5
  T1 := T124_51
  T2 := Q2.T124_51_2
  h1 := (2,1,0,3,2)
  h2 := (2,1,0,3,0)
  D1 := [[2, 1, 4, 3], [2, 1, 4, 2], [2, 1, 4, 1], [2, 1, 4, 0], [2, 1, 4, 4]]
  D2 := [[2, 1, 4, 1], [2, 1, 4, 0], [2, 1, 4, 4], [2, 1, 4, 3], [2, 1, 4, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_124_51_15 : ColCertDiv where
  rK := ⟨124, by decide⟩
  rH := ⟨51, by decide⟩
  m := 5
  T1 := T124_51
  T2 := Q2.T124_51_2
  h1 := (3,4,0,4,3)
  h2 := (3,4,0,4,2)
  D1 := [[3, 4, 4, 3], [3, 4, 4, 4], [3, 4, 4, 0], [3, 4, 4, 1], [3, 4, 4, 2]]
  D2 := [[3, 4, 4, 2], [3, 4, 4, 3], [3, 4, 4, 4], [3, 4, 4, 0], [3, 4, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_124_51_20 : ColCertDiv where
  rK := ⟨124, by decide⟩
  rH := ⟨51, by decide⟩
  m := 5
  T1 := T124_51
  T2 := Q2.T124_51_2
  h1 := (4,2,0,3,1)
  h2 := (4,2,0,3,2)
  D1 := [[4, 2, 1, 4], [4, 2, 1, 2], [4, 2, 1, 0], [4, 2, 1, 3], [4, 2, 1, 1]]
  D2 := [[4, 2, 1, 0], [4, 2, 1, 3], [4, 2, 1, 1], [4, 2, 1, 4], [4, 2, 1, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_124_81_5 : ColCertDiv where
  rK := ⟨124, by decide⟩
  rH := ⟨81, by decide⟩
  m := 5
  T1 := T124_81
  T2 := Q2.T124_81_2
  h1 := (1,0,4,0,0)
  h2 := (1,0,4,0,0)
  D1 := [[1, 0, 4, 4], [1, 0, 4, 4], [1, 0, 4, 4], [1, 0, 4, 4], [1, 0, 4, 4]]
  D2 := [[1, 0, 4, 2], [1, 0, 4, 2], [1, 0, 4, 2], [1, 0, 4, 2], [1, 0, 4, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_124_81_10 : ColCertDiv where
  rK := ⟨124, by decide⟩
  rH := ⟨81, by decide⟩
  m := 5
  T1 := T124_81
  T2 := Q2.T124_81_2
  h1 := (2,0,3,0,0)
  h2 := (2,0,3,0,0)
  D1 := [[2, 0, 3, 4], [2, 0, 3, 4], [2, 0, 3, 4], [2, 0, 3, 4], [2, 0, 3, 4]]
  D2 := [[2, 0, 3, 0], [2, 0, 3, 0], [2, 0, 3, 0], [2, 0, 3, 0], [2, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_124_81_15 : ColCertDiv where
  rK := ⟨124, by decide⟩
  rH := ⟨81, by decide⟩
  m := 5
  T1 := T124_81
  T2 := Q2.T124_81_2
  h1 := (3,0,2,0,0)
  h2 := (3,0,2,0,0)
  D1 := [[3, 0, 2, 0], [3, 0, 2, 0], [3, 0, 2, 0], [3, 0, 2, 0], [3, 0, 2, 0]]
  D2 := [[3, 0, 2, 4], [3, 0, 2, 4], [3, 0, 2, 4], [3, 0, 2, 4], [3, 0, 2, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_124_81_20 : ColCertDiv where
  rK := ⟨124, by decide⟩
  rH := ⟨81, by decide⟩
  m := 5
  T1 := T124_81
  T2 := Q2.T124_81_2
  h1 := (4,0,1,0,0)
  h2 := (4,0,1,0,0)
  D1 := [[4, 0, 1, 2], [4, 0, 1, 2], [4, 0, 1, 2], [4, 0, 1, 2], [4, 0, 1, 2]]
  D2 := [[4, 0, 1, 4], [4, 0, 1, 4], [4, 0, 1, 4], [4, 0, 1, 4], [4, 0, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_124_92_5 : ColCertDiv where
  rK := ⟨124, by decide⟩
  rH := ⟨92, by decide⟩
  m := 5
  T1 := T124_92
  T2 := Q2.T124_92_2
  h1 := (1,2,3,3,2)
  h2 := (1,2,3,3,2)
  D1 := [[1, 2, 0, 3], [1, 2, 0, 1], [1, 2, 0, 4], [1, 2, 0, 2], [1, 2, 0, 0]]
  D2 := [[1, 2, 0, 4], [1, 2, 0, 2], [1, 2, 0, 0], [1, 2, 0, 3], [1, 2, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_124_92_10 : ColCertDiv where
  rK := ⟨124, by decide⟩
  rH := ⟨92, by decide⟩
  m := 5
  T1 := T124_92
  T2 := Q2.T124_92_2
  h1 := (2,4,1,3,3)
  h2 := (2,4,1,3,3)
  D1 := [[2, 4, 3, 1], [2, 4, 3, 2], [2, 4, 3, 3], [2, 4, 3, 4], [2, 4, 3, 0]]
  D2 := [[2, 4, 3, 3], [2, 4, 3, 4], [2, 4, 3, 0], [2, 4, 3, 1], [2, 4, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_124_92_15 : ColCertDiv where
  rK := ⟨124, by decide⟩
  rH := ⟨92, by decide⟩
  m := 5
  T1 := T124_92
  T2 := Q2.T124_92_2
  h1 := (3,1,4,0,1)
  h2 := (3,1,4,0,2)
  D1 := [[3, 1, 4, 2], [3, 1, 4, 1], [3, 1, 4, 0], [3, 1, 4, 4], [3, 1, 4, 3]]
  D2 := [[3, 1, 4, 1], [3, 1, 4, 0], [3, 1, 4, 4], [3, 1, 4, 3], [3, 1, 4, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_124_95_25 : ColCertDiv where
  rK := ⟨124, by decide⟩
  rH := ⟨95, by decide⟩
  m := 5
  T1 := T124_95
  T2 := Q2.T124_95_2
  h1 := (0,1,2,0,0)
  h2 := (0,1,2,0,0)
  D1 := [[0, 1, 0, 0], [0, 1, 0, 4], [0, 1, 0, 3], [0, 1, 0, 2], [0, 1, 0, 1]]
  D2 := [[0, 1, 0, 4], [0, 1, 0, 3], [0, 1, 0, 2], [0, 1, 0, 1], [0, 1, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_124_95_50 : ColCertDiv where
  rK := ⟨124, by decide⟩
  rH := ⟨95, by decide⟩
  m := 5
  T1 := T124_95
  T2 := Q2.T124_95_2
  h1 := (0,2,4,0,2)
  h2 := (0,2,4,0,2)
  D1 := [[0, 2, 0, 0], [0, 2, 0, 3], [0, 2, 0, 1], [0, 2, 0, 4], [0, 2, 0, 2]]
  D2 := [[0, 2, 0, 3], [0, 2, 0, 1], [0, 2, 0, 4], [0, 2, 0, 2], [0, 2, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_124_95_75 : ColCertDiv where
  rK := ⟨124, by decide⟩
  rH := ⟨95, by decide⟩
  m := 5
  T1 := T124_95
  T2 := Q2.T124_95_2
  h1 := (0,3,1,0,1)
  h2 := (0,3,1,0,1)
  D1 := [[0, 3, 0, 0], [0, 3, 0, 2], [0, 3, 0, 4], [0, 3, 0, 1], [0, 3, 0, 3]]
  D2 := [[0, 3, 0, 2], [0, 3, 0, 4], [0, 3, 0, 1], [0, 3, 0, 3], [0, 3, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_124_95_100 : ColCertDiv where
  rK := ⟨124, by decide⟩
  rH := ⟨95, by decide⟩
  m := 5
  T1 := T124_95
  T2 := Q2.T124_95_2
  h1 := (0,4,3,0,2)
  h2 := (0,4,3,0,2)
  D1 := [[0, 4, 0, 0], [0, 4, 0, 1], [0, 4, 0, 2], [0, 4, 0, 3], [0, 4, 0, 4]]
  D2 := [[0, 4, 0, 1], [0, 4, 0, 2], [0, 4, 0, 3], [0, 4, 0, 4], [0, 4, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_124_101_5 : ColCertDiv where
  rK := ⟨124, by decide⟩
  rH := ⟨101, by decide⟩
  m := 5
  T1 := T124_101
  T2 := Q2.T124_101_2
  h1 := (1,4,2,4,3)
  h2 := (1,4,2,4,3)
  D1 := [[1, 4, 4, 0], [1, 4, 4, 1], [1, 4, 4, 2], [1, 4, 4, 3], [1, 4, 4, 4]]
  D2 := [[1, 4, 4, 4], [1, 4, 4, 0], [1, 4, 4, 1], [1, 4, 4, 2], [1, 4, 4, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_124_101_10 : ColCertDiv where
  rK := ⟨124, by decide⟩
  rH := ⟨101, by decide⟩
  m := 5
  T1 := T124_101
  T2 := Q2.T124_101_2
  h1 := (2,3,4,2,4)
  h2 := (2,3,4,2,0)
  D1 := [[2, 3, 4, 2], [2, 3, 4, 4], [2, 3, 4, 1], [2, 3, 4, 3], [2, 3, 4, 0]]
  D2 := [[2, 3, 4, 1], [2, 3, 4, 3], [2, 3, 4, 0], [2, 3, 4, 2], [2, 3, 4, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_124_101_15 : ColCertDiv where
  rK := ⟨124, by decide⟩
  rH := ⟨101, by decide⟩
  m := 5
  T1 := T124_101
  T2 := Q2.T124_101_2
  h1 := (3,2,1,4,1)
  h2 := (3,2,1,4,3)
  D1 := [[3, 2, 0, 4], [3, 2, 0, 2], [3, 2, 0, 0], [3, 2, 0, 3], [3, 2, 0, 1]]
  D2 := [[3, 2, 0, 3], [3, 2, 0, 1], [3, 2, 0, 4], [3, 2, 0, 2], [3, 2, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_124_101_20 : ColCertDiv where
  rK := ⟨124, by decide⟩
  rH := ⟨101, by decide⟩
  m := 5
  T1 := T124_101
  T2 := Q2.T124_101_2
  h1 := (4,1,3,0,3)
  h2 := (4,1,3,0,1)
  D1 := [[4, 1, 2, 0], [4, 1, 2, 4], [4, 1, 2, 3], [4, 1, 2, 2], [4, 1, 2, 1]]
  D2 := [[4, 1, 2, 4], [4, 1, 2, 3], [4, 1, 2, 2], [4, 1, 2, 1], [4, 1, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_124_109_5 : ColCertDiv where
  rK := ⟨124, by decide⟩
  rH := ⟨109, by decide⟩
  m := 5
  T1 := T124_109
  T2 := Q2.T124_109_2
  h1 := (1,1,1,0,0)
  h2 := (1,1,1,0,0)
  D1 := [[1, 1, 3, 0], [1, 1, 3, 4], [1, 1, 3, 3], [1, 1, 3, 2], [1, 1, 3, 1]]
  D2 := [[1, 1, 3, 2], [1, 1, 3, 1], [1, 1, 3, 0], [1, 1, 3, 4], [1, 1, 3, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_124_109_10 : ColCertDiv where
  rK := ⟨124, by decide⟩
  rH := ⟨109, by decide⟩
  m := 5
  T1 := T124_109
  T2 := Q2.T124_109_2
  h1 := (2,2,2,1,1)
  h2 := (2,2,2,1,1)
  D1 := [[2, 2, 0, 2], [2, 2, 0, 0], [2, 2, 0, 3], [2, 2, 0, 1], [2, 2, 0, 4]]
  D2 := [[2, 2, 0, 1], [2, 2, 0, 4], [2, 2, 0, 2], [2, 2, 0, 0], [2, 2, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_124_109_15 : ColCertDiv where
  rK := ⟨124, by decide⟩
  rH := ⟨109, by decide⟩
  m := 5
  T1 := T124_109
  T2 := Q2.T124_109_2
  h1 := (3,3,3,3,4)
  h2 := (3,3,3,3,4)
  D1 := [[3, 3, 1, 2], [3, 3, 1, 4], [3, 3, 1, 1], [3, 3, 1, 3], [3, 3, 1, 0]]
  D2 := [[3, 3, 1, 3], [3, 3, 1, 0], [3, 3, 1, 2], [3, 3, 1, 4], [3, 3, 1, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_124_109_20 : ColCertDiv where
  rK := ⟨124, by decide⟩
  rH := ⟨109, by decide⟩
  m := 5
  T1 := T124_109
  T2 := Q2.T124_109_2
  h1 := (4,4,4,1,0)
  h2 := (4,4,4,1,0)
  D1 := [[4, 4, 1, 1], [4, 4, 1, 2], [4, 4, 1, 3], [4, 4, 1, 4], [4, 4, 1, 0]]
  D2 := [[4, 4, 1, 4], [4, 4, 1, 0], [4, 4, 1, 1], [4, 4, 1, 2], [4, 4, 1, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_124_113_10 : ColCertDiv where
  rK := ⟨124, by decide⟩
  rH := ⟨113, by decide⟩
  m := 5
  T1 := T124_113
  T2 := Q2.T124_113_2
  h1 := (2,1,0,0,1)
  h2 := (2,1,0,0,2)
  D1 := [[2, 1, 1, 3], [2, 1, 1, 2], [2, 1, 1, 1], [2, 1, 1, 0], [2, 1, 1, 4]]
  D2 := [[2, 1, 1, 4], [2, 1, 1, 3], [2, 1, 1, 2], [2, 1, 1, 1], [2, 1, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_124_113_15 : ColCertDiv where
  rK := ⟨124, by decide⟩
  rH := ⟨113, by decide⟩
  m := 5
  T1 := T124_113
  T2 := Q2.T124_113_2
  h1 := (3,4,0,2,3)
  h2 := (3,4,0,2,4)
  D1 := [[3, 4, 2, 4], [3, 4, 2, 0], [3, 4, 2, 1], [3, 4, 2, 2], [3, 4, 2, 3]]
  D2 := [[3, 4, 2, 0], [3, 4, 2, 1], [3, 4, 2, 2], [3, 4, 2, 3], [3, 4, 2, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_124_113_20 : ColCertDiv where
  rK := ⟨124, by decide⟩
  rH := ⟨113, by decide⟩
  m := 5
  T1 := T124_113
  T2 := Q2.T124_113_2
  h1 := (4,2,0,2,3)
  h2 := (4,2,0,2,0)
  D1 := [[4, 2, 0, 0], [4, 2, 0, 3], [4, 2, 0, 1], [4, 2, 0, 4], [4, 2, 0, 2]]
  D2 := [[4, 2, 0, 2], [4, 2, 0, 0], [4, 2, 0, 3], [4, 2, 0, 1], [4, 2, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_125_31_5 : ColCertDiv where
  rK := ⟨125, by decide⟩
  rH := ⟨31, by decide⟩
  m := 5
  T1 := T125_31
  T2 := Q2.T125_31_2
  h1 := (1,3,2,0,4)
  h2 := (1,3,2,0,0)
  D1 := [[1, 3, 2, 3], [1, 3, 2, 0], [1, 3, 2, 2], [1, 3, 2, 4], [1, 3, 2, 1]]
  D2 := [[1, 3, 2, 4], [1, 3, 2, 1], [1, 3, 2, 3], [1, 3, 2, 0], [1, 3, 2, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_125_31_10 : ColCertDiv where
  rK := ⟨125, by decide⟩
  rH := ⟨31, by decide⟩
  m := 5
  T1 := T125_31
  T2 := Q2.T125_31_2
  h1 := (2,1,4,3,0)
  h2 := (2,1,4,3,3)
  D1 := [[2, 1, 1, 0], [2, 1, 1, 4], [2, 1, 1, 3], [2, 1, 1, 2], [2, 1, 1, 1]]
  D2 := [[2, 1, 1, 3], [2, 1, 1, 2], [2, 1, 1, 1], [2, 1, 1, 0], [2, 1, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_125_31_15 : ColCertDiv where
  rK := ⟨125, by decide⟩
  rH := ⟨31, by decide⟩
  m := 5
  T1 := T125_31
  T2 := Q2.T125_31_2
  h1 := (3,4,1,4,4)
  h2 := (3,4,1,4,3)
  D1 := [[3, 4, 2, 2], [3, 4, 2, 3], [3, 4, 2, 4], [3, 4, 2, 0], [3, 4, 2, 1]]
  D2 := [[3, 4, 2, 1], [3, 4, 2, 2], [3, 4, 2, 3], [3, 4, 2, 4], [3, 4, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_125_31_20 : ColCertDiv where
  rK := ⟨125, by decide⟩
  rH := ⟨31, by decide⟩
  m := 5
  T1 := T125_31
  T2 := Q2.T125_31_2
  h1 := (4,2,3,3,1)
  h2 := (4,2,3,3,2)
  D1 := [[4, 2, 0, 4], [4, 2, 0, 2], [4, 2, 0, 0], [4, 2, 0, 3], [4, 2, 0, 1]]
  D2 := [[4, 2, 0, 0], [4, 2, 0, 3], [4, 2, 0, 1], [4, 2, 0, 4], [4, 2, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_125_34_10 : ColCertDiv where
  rK := ⟨125, by decide⟩
  rH := ⟨34, by decide⟩
  m := 5
  T1 := T125_34
  T2 := Q2.T125_34_2
  h1 := (2,3,1,0,3)
  h2 := (2,3,1,0,4)
  D1 := [[2, 3, 4, 2], [2, 3, 4, 4], [2, 3, 4, 1], [2, 3, 4, 3], [2, 3, 4, 0]]
  D2 := [[2, 3, 4, 3], [2, 3, 4, 0], [2, 3, 4, 2], [2, 3, 4, 4], [2, 3, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_125_34_15 : ColCertDiv where
  rK := ⟨125, by decide⟩
  rH := ⟨34, by decide⟩
  m := 5
  T1 := T125_34
  T2 := Q2.T125_34_2
  h1 := (3,2,4,1,4)
  h2 := (3,2,4,1,1)
  D1 := [[3, 2, 0, 4], [3, 2, 0, 2], [3, 2, 0, 0], [3, 2, 0, 3], [3, 2, 0, 1]]
  D2 := [[3, 2, 0, 1], [3, 2, 0, 4], [3, 2, 0, 2], [3, 2, 0, 0], [3, 2, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_125_34_20 : ColCertDiv where
  rK := ⟨125, by decide⟩
  rH := ⟨34, by decide⟩
  m := 5
  T1 := T125_34
  T2 := Q2.T125_34_2
  h1 := (4,1,2,1,3)
  h2 := (4,1,2,1,1)
  D1 := [[4, 1, 2, 0], [4, 1, 2, 4], [4, 1, 2, 3], [4, 1, 2, 2], [4, 1, 2, 1]]
  D2 := [[4, 1, 2, 3], [4, 1, 2, 2], [4, 1, 2, 1], [4, 1, 2, 0], [4, 1, 2, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_125_40_5 : ColCertDiv where
  rK := ⟨125, by decide⟩
  rH := ⟨40, by decide⟩
  m := 5
  T1 := T125_40
  T2 := Q2.T125_40_2
  h1 := (1,2,1,2,4)
  h2 := (1,2,1,2,1)
  D1 := [[1, 2, 0, 2], [1, 2, 0, 0], [1, 2, 0, 3], [1, 2, 0, 1], [1, 2, 0, 4]]
  D2 := [[1, 2, 0, 4], [1, 2, 0, 2], [1, 2, 0, 0], [1, 2, 0, 3], [1, 2, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_125_40_10 : ColCertDiv where
  rK := ⟨125, by decide⟩
  rH := ⟨40, by decide⟩
  m := 5
  T1 := T125_40
  T2 := Q2.T125_40_2
  h1 := (2,4,2,1,2)
  h2 := (2,4,2,1,1)
  D1 := [[2, 4, 3, 4], [2, 4, 3, 0], [2, 4, 3, 1], [2, 4, 3, 2], [2, 4, 3, 3]]
  D2 := [[2, 4, 3, 3], [2, 4, 3, 4], [2, 4, 3, 0], [2, 4, 3, 1], [2, 4, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_125_40_15 : ColCertDiv where
  rK := ⟨125, by decide⟩
  rH := ⟨40, by decide⟩
  m := 5
  T1 := T125_40
  T2 := Q2.T125_40_2
  h1 := (3,1,3,2,2)
  h2 := (3,1,3,2,4)
  D1 := [[3, 1, 4, 4], [3, 1, 4, 3], [3, 1, 4, 2], [3, 1, 4, 1], [3, 1, 4, 0]]
  D2 := [[3, 1, 4, 1], [3, 1, 4, 0], [3, 1, 4, 4], [3, 1, 4, 3], [3, 1, 4, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_125_40_20 : ColCertDiv where
  rK := ⟨125, by decide⟩
  rH := ⟨40, by decide⟩
  m := 5
  T1 := T125_40
  T2 := Q2.T125_40_2
  h1 := (4,3,4,0,4)
  h2 := (4,3,4,0,3)
  D1 := [[4, 3, 3, 2], [4, 3, 3, 4], [4, 3, 3, 1], [4, 3, 3, 3], [4, 3, 3, 0]]
  D2 := [[4, 3, 3, 1], [4, 3, 3, 3], [4, 3, 3, 0], [4, 3, 3, 2], [4, 3, 3, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_125_43_5 : ColCertDiv where
  rK := ⟨125, by decide⟩
  rH := ⟨43, by decide⟩
  m := 5
  T1 := T125_43
  T2 := Q2.T125_43_2
  h1 := (0,1,1,4,4)
  h2 := (0,1,1,4,2)
  D1 := [[0, 1, 4, 4], [0, 1, 4, 3], [0, 1, 4, 2], [0, 1, 4, 1], [0, 1, 4, 0]]
  D2 := [[0, 1, 4, 2], [0, 1, 4, 1], [0, 1, 4, 0], [0, 1, 4, 4], [0, 1, 4, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_125_43_10 : ColCertDiv where
  rK := ⟨125, by decide⟩
  rH := ⟨43, by decide⟩
  m := 5
  T1 := T125_43
  T2 := Q2.T125_43_2
  h1 := (0,2,2,3,4)
  h2 := (0,2,2,3,0)
  D1 := [[0, 2, 3, 3], [0, 2, 3, 1], [0, 2, 3, 4], [0, 2, 3, 2], [0, 2, 3, 0]]
  D2 := [[0, 2, 3, 4], [0, 2, 3, 2], [0, 2, 3, 0], [0, 2, 3, 3], [0, 2, 3, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_125_43_15 : ColCertDiv where
  rK := ⟨125, by decide⟩
  rH := ⟨43, by decide⟩
  m := 5
  T1 := T125_43
  T2 := Q2.T125_43_2
  h1 := (0,3,3,2,0)
  h2 := (0,3,3,2,4)
  D1 := [[0, 3, 2, 2], [0, 3, 2, 4], [0, 3, 2, 1], [0, 3, 2, 3], [0, 3, 2, 0]]
  D2 := [[0, 3, 2, 1], [0, 3, 2, 3], [0, 3, 2, 0], [0, 3, 2, 2], [0, 3, 2, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_125_43_20 : ColCertDiv where
  rK := ⟨125, by decide⟩
  rH := ⟨43, by decide⟩
  m := 5
  T1 := T125_43
  T2 := Q2.T125_43_2
  h1 := (0,4,4,1,2)
  h2 := (0,4,4,1,4)
  D1 := [[0, 4, 1, 1], [0, 4, 1, 2], [0, 4, 1, 3], [0, 4, 1, 4], [0, 4, 1, 0]]
  D2 := [[0, 4, 1, 3], [0, 4, 1, 4], [0, 4, 1, 0], [0, 4, 1, 1], [0, 4, 1, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_125_52_5 : ColCertDiv where
  rK := ⟨125, by decide⟩
  rH := ⟨52, by decide⟩
  m := 5
  T1 := T125_52
  T2 := Q2.T125_52_2
  h1 := (1,1,0,4,1)
  h2 := (1,1,0,4,4)
  D1 := [[1, 1, 3, 2], [1, 1, 3, 1], [1, 1, 3, 0], [1, 1, 3, 4], [1, 1, 3, 3]]
  D2 := [[1, 1, 3, 0], [1, 1, 3, 4], [1, 1, 3, 3], [1, 1, 3, 2], [1, 1, 3, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_125_52_10 : ColCertDiv where
  rK := ⟨125, by decide⟩
  rH := ⟨52, by decide⟩
  m := 5
  T1 := T125_52
  T2 := Q2.T125_52_2
  h1 := (2,2,0,4,1)
  h2 := (2,2,0,4,2)
  D1 := [[2, 2, 0, 1], [2, 2, 0, 4], [2, 2, 0, 2], [2, 2, 0, 0], [2, 2, 0, 3]]
  D2 := [[2, 2, 0, 2], [2, 2, 0, 0], [2, 2, 0, 3], [2, 2, 0, 1], [2, 2, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_125_52_15 : ColCertDiv where
  rK := ⟨125, by decide⟩
  rH := ⟨52, by decide⟩
  m := 5
  T1 := T125_52
  T2 := Q2.T125_52_2
  h1 := (3,3,0,0,1)
  h2 := (3,3,0,0,0)
  D1 := [[3, 3, 1, 3], [3, 3, 1, 0], [3, 3, 1, 2], [3, 3, 1, 4], [3, 3, 1, 1]]
  D2 := [[3, 3, 1, 2], [3, 3, 1, 4], [3, 3, 1, 1], [3, 3, 1, 3], [3, 3, 1, 0]]
  bind1 := by decide
  bind2 := by decide

end LeanDring.P5Presentation
