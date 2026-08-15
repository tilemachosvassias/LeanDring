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
rest tier, chunk 52: 60 columns.
-/

-- machine-emitted data: silence style linters (generated long lines, file-level options)
set_option linter.style.longLine false

namespace LeanDring.P5Presentation

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

def colCert_124_2_0 : ColCert where
  rK := ⟨124, by decide⟩
  rH := ⟨2, by decide⟩
  m := 5
  T1 := T124_2
  T2 := Q2.T124_2_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_124_10_0 : ColCert where
  rK := ⟨124, by decide⟩
  rH := ⟨10, by decide⟩
  m := 5
  T1 := T124_10
  T2 := Q2.T124_10_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_124_10_1 : ColCert where
  rK := ⟨124, by decide⟩
  rH := ⟨10, by decide⟩
  m := 5
  T1 := T124_10
  T2 := Q2.T124_10_2
  h1 := (0,0,0,1,4)
  h2 := (0,0,0,1,4)
  D := [[0, 0, 1, 4], [0, 0, 1, 4], [0, 0, 1, 4], [0, 0, 1, 4], [0, 0, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_124_10_2 : ColCert where
  rK := ⟨124, by decide⟩
  rH := ⟨10, by decide⟩
  m := 5
  T1 := T124_10
  T2 := Q2.T124_10_2
  h1 := (0,0,0,2,3)
  h2 := (0,0,0,2,3)
  D := [[0, 0, 2, 3], [0, 0, 2, 3], [0, 0, 2, 3], [0, 0, 2, 3], [0, 0, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_124_10_3 : ColCert where
  rK := ⟨124, by decide⟩
  rH := ⟨10, by decide⟩
  m := 5
  T1 := T124_10
  T2 := Q2.T124_10_2
  h1 := (0,0,0,3,2)
  h2 := (0,0,0,3,2)
  D := [[0, 0, 3, 2], [0, 0, 3, 2], [0, 0, 3, 2], [0, 0, 3, 2], [0, 0, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_124_10_4 : ColCert where
  rK := ⟨124, by decide⟩
  rH := ⟨10, by decide⟩
  m := 5
  T1 := T124_10
  T2 := Q2.T124_10_2
  h1 := (0,0,0,4,1)
  h2 := (0,0,0,4,1)
  D := [[0, 0, 4, 1], [0, 0, 4, 1], [0, 0, 4, 1], [0, 0, 4, 1], [0, 0, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_124_12_0 : ColCert where
  rK := ⟨124, by decide⟩
  rH := ⟨12, by decide⟩
  m := 5
  T1 := T124_12
  T2 := Q2.T124_12_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_124_12_1 : ColCert where
  rK := ⟨124, by decide⟩
  rH := ⟨12, by decide⟩
  m := 5
  T1 := T124_12
  T2 := Q2.T124_12_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_124_12_2 : ColCert where
  rK := ⟨124, by decide⟩
  rH := ⟨12, by decide⟩
  m := 5
  T1 := T124_12
  T2 := Q2.T124_12_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_124_12_3 : ColCert where
  rK := ⟨124, by decide⟩
  rH := ⟨12, by decide⟩
  m := 5
  T1 := T124_12
  T2 := Q2.T124_12_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_124_12_4 : ColCert where
  rK := ⟨124, by decide⟩
  rH := ⟨12, by decide⟩
  m := 5
  T1 := T124_12
  T2 := Q2.T124_12_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_124_20_0 : ColCert where
  rK := ⟨124, by decide⟩
  rH := ⟨20, by decide⟩
  m := 5
  T1 := T124_20
  T2 := Q2.T124_20_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_124_20_1 : ColCert where
  rK := ⟨124, by decide⟩
  rH := ⟨20, by decide⟩
  m := 5
  T1 := T124_20
  T2 := Q2.T124_20_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_124_20_2 : ColCert where
  rK := ⟨124, by decide⟩
  rH := ⟨20, by decide⟩
  m := 5
  T1 := T124_20
  T2 := Q2.T124_20_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_124_20_3 : ColCert where
  rK := ⟨124, by decide⟩
  rH := ⟨20, by decide⟩
  m := 5
  T1 := T124_20
  T2 := Q2.T124_20_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_124_20_4 : ColCert where
  rK := ⟨124, by decide⟩
  rH := ⟨20, by decide⟩
  m := 5
  T1 := T124_20
  T2 := Q2.T124_20_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_124_30_0 : ColCert where
  rK := ⟨124, by decide⟩
  rH := ⟨30, by decide⟩
  m := 5
  T1 := T124_30
  T2 := Q2.T124_30_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_124_30_1 : ColCert where
  rK := ⟨124, by decide⟩
  rH := ⟨30, by decide⟩
  m := 5
  T1 := T124_30
  T2 := Q2.T124_30_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_124_30_2 : ColCert where
  rK := ⟨124, by decide⟩
  rH := ⟨30, by decide⟩
  m := 5
  T1 := T124_30
  T2 := Q2.T124_30_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_124_30_3 : ColCert where
  rK := ⟨124, by decide⟩
  rH := ⟨30, by decide⟩
  m := 5
  T1 := T124_30
  T2 := Q2.T124_30_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_124_30_4 : ColCert where
  rK := ⟨124, by decide⟩
  rH := ⟨30, by decide⟩
  m := 5
  T1 := T124_30
  T2 := Q2.T124_30_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_124_30_15 : ColCert where
  rK := ⟨124, by decide⟩
  rH := ⟨30, by decide⟩
  m := 5
  T1 := T124_30
  T2 := Q2.T124_30_2
  h1 := (3,1,4,2,1)
  h2 := (3,1,4,2,3)
  D := [[3, 1, 1, 1], [3, 1, 1, 0], [3, 1, 1, 4], [3, 1, 1, 3], [3, 1, 1, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_124_33_0 : ColCert where
  rK := ⟨124, by decide⟩
  rH := ⟨33, by decide⟩
  m := 5
  T1 := T124_33
  T2 := Q2.T124_33_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_124_33_1 : ColCert where
  rK := ⟨124, by decide⟩
  rH := ⟨33, by decide⟩
  m := 5
  T1 := T124_33
  T2 := Q2.T124_33_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_124_33_2 : ColCert where
  rK := ⟨124, by decide⟩
  rH := ⟨33, by decide⟩
  m := 5
  T1 := T124_33
  T2 := Q2.T124_33_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_124_33_3 : ColCert where
  rK := ⟨124, by decide⟩
  rH := ⟨33, by decide⟩
  m := 5
  T1 := T124_33
  T2 := Q2.T124_33_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_124_33_4 : ColCert where
  rK := ⟨124, by decide⟩
  rH := ⟨33, by decide⟩
  m := 5
  T1 := T124_33
  T2 := Q2.T124_33_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_124_39_0 : ColCert where
  rK := ⟨124, by decide⟩
  rH := ⟨39, by decide⟩
  m := 5
  T1 := T124_39
  T2 := Q2.T124_39_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_124_39_1 : ColCert where
  rK := ⟨124, by decide⟩
  rH := ⟨39, by decide⟩
  m := 5
  T1 := T124_39
  T2 := Q2.T124_39_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_124_39_2 : ColCert where
  rK := ⟨124, by decide⟩
  rH := ⟨39, by decide⟩
  m := 5
  T1 := T124_39
  T2 := Q2.T124_39_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_124_39_3 : ColCert where
  rK := ⟨124, by decide⟩
  rH := ⟨39, by decide⟩
  m := 5
  T1 := T124_39
  T2 := Q2.T124_39_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_124_39_4 : ColCert where
  rK := ⟨124, by decide⟩
  rH := ⟨39, by decide⟩
  m := 5
  T1 := T124_39
  T2 := Q2.T124_39_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_124_47_0 : ColCert where
  rK := ⟨124, by decide⟩
  rH := ⟨47, by decide⟩
  m := 5
  T1 := T124_47
  T2 := Q2.T124_47_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_124_47_1 : ColCert where
  rK := ⟨124, by decide⟩
  rH := ⟨47, by decide⟩
  m := 5
  T1 := T124_47
  T2 := Q2.T124_47_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_124_47_2 : ColCert where
  rK := ⟨124, by decide⟩
  rH := ⟨47, by decide⟩
  m := 5
  T1 := T124_47
  T2 := Q2.T124_47_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_124_47_3 : ColCert where
  rK := ⟨124, by decide⟩
  rH := ⟨47, by decide⟩
  m := 5
  T1 := T124_47
  T2 := Q2.T124_47_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_124_47_4 : ColCert where
  rK := ⟨124, by decide⟩
  rH := ⟨47, by decide⟩
  m := 5
  T1 := T124_47
  T2 := Q2.T124_47_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_124_47_5 : ColCert where
  rK := ⟨124, by decide⟩
  rH := ⟨47, by decide⟩
  m := 5
  T1 := T124_47
  T2 := Q2.T124_47_2
  h1 := (1,1,1,4,2)
  h2 := (1,1,1,4,0)
  D := [[1, 1, 2, 3], [1, 1, 2, 2], [1, 1, 2, 1], [1, 1, 2, 0], [1, 1, 2, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_124_47_10 : ColCert where
  rK := ⟨124, by decide⟩
  rH := ⟨47, by decide⟩
  m := 5
  T1 := T124_47
  T2 := Q2.T124_47_2
  h1 := (2,2,2,4,4)
  h2 := (2,2,2,4,0)
  D := [[2, 2, 3, 4], [2, 2, 3, 2], [2, 2, 3, 0], [2, 2, 3, 3], [2, 2, 3, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_124_47_15 : ColCert where
  rK := ⟨124, by decide⟩
  rH := ⟨47, by decide⟩
  m := 5
  T1 := T124_47
  T2 := Q2.T124_47_2
  h1 := (3,3,3,0,2)
  h2 := (3,3,3,0,1)
  D := [[3, 3, 3, 4], [3, 3, 3, 1], [3, 3, 3, 3], [3, 3, 3, 0], [3, 3, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_124_47_20 : ColCert where
  rK := ⟨124, by decide⟩
  rH := ⟨47, by decide⟩
  m := 5
  T1 := T124_47
  T2 := Q2.T124_47_2
  h1 := (4,4,4,2,2)
  h2 := (4,4,4,2,4)
  D := [[4, 4, 2, 4], [4, 4, 2, 0], [4, 4, 2, 1], [4, 4, 2, 2], [4, 4, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_124_51_0 : ColCert where
  rK := ⟨124, by decide⟩
  rH := ⟨51, by decide⟩
  m := 5
  T1 := T124_51
  T2 := Q2.T124_51_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_124_51_1 : ColCert where
  rK := ⟨124, by decide⟩
  rH := ⟨51, by decide⟩
  m := 5
  T1 := T124_51
  T2 := Q2.T124_51_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_124_51_2 : ColCert where
  rK := ⟨124, by decide⟩
  rH := ⟨51, by decide⟩
  m := 5
  T1 := T124_51
  T2 := Q2.T124_51_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_124_51_3 : ColCert where
  rK := ⟨124, by decide⟩
  rH := ⟨51, by decide⟩
  m := 5
  T1 := T124_51
  T2 := Q2.T124_51_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_124_51_4 : ColCert where
  rK := ⟨124, by decide⟩
  rH := ⟨51, by decide⟩
  m := 5
  T1 := T124_51
  T2 := Q2.T124_51_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_124_53_0 : ColCert where
  rK := ⟨124, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T124_53
  T2 := Q2.T124_53_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_124_53_1 : ColCert where
  rK := ⟨124, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T124_53
  T2 := Q2.T124_53_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_124_53_2 : ColCert where
  rK := ⟨124, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T124_53
  T2 := Q2.T124_53_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_124_53_3 : ColCert where
  rK := ⟨124, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T124_53
  T2 := Q2.T124_53_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_124_53_4 : ColCert where
  rK := ⟨124, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T124_53
  T2 := Q2.T124_53_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_124_53_5 : ColCert where
  rK := ⟨124, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T124_53
  T2 := Q2.T124_53_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_124_53_10 : ColCert where
  rK := ⟨124, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T124_53
  T2 := Q2.T124_53_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_124_53_15 : ColCert where
  rK := ⟨124, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T124_53
  T2 := Q2.T124_53_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_124_53_20 : ColCert where
  rK := ⟨124, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T124_53
  T2 := Q2.T124_53_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_124_81_0 : ColCert where
  rK := ⟨124, by decide⟩
  rH := ⟨81, by decide⟩
  m := 5
  T1 := T124_81
  T2 := Q2.T124_81_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_124_81_1 : ColCert where
  rK := ⟨124, by decide⟩
  rH := ⟨81, by decide⟩
  m := 5
  T1 := T124_81
  T2 := Q2.T124_81_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_124_81_2 : ColCert where
  rK := ⟨124, by decide⟩
  rH := ⟨81, by decide⟩
  m := 5
  T1 := T124_81
  T2 := Q2.T124_81_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_124_81_3 : ColCert where
  rK := ⟨124, by decide⟩
  rH := ⟨81, by decide⟩
  m := 5
  T1 := T124_81
  T2 := Q2.T124_81_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_124_81_4 : ColCert where
  rK := ⟨124, by decide⟩
  rH := ⟨81, by decide⟩
  m := 5
  T1 := T124_81
  T2 := Q2.T124_81_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

end LeanDring.P5Presentation
