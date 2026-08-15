/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.Twin1.ColCert
import LeanDring.P5.Data.EntryK.C037

/-!
# Species-table cell data, stage 2 — twin-coincident columns (cheap tier)

Per-column certified exponent-vector data (`ColCert`/`ColCertDiv`) with kernel
`decide` bindings. Emitted; the embedded lists are what the kernel certifies.
rest tier, chunk 77: 60 columns.
-/

-- machine-emitted data: silence style linters (generated long lines, file-level options)
set_option linter.style.longLine false

namespace LeanDring.P5Presentation

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

def colCert_136_10_0 : ColCert where
  rK := ⟨136, by decide⟩
  rH := ⟨10, by decide⟩
  m := 5
  T1 := T136_10
  T2 := Q2.T136_10_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_136_10_1 : ColCert where
  rK := ⟨136, by decide⟩
  rH := ⟨10, by decide⟩
  m := 5
  T1 := T136_10
  T2 := Q2.T136_10_2
  h1 := (0,0,0,1,4)
  h2 := (0,0,0,1,4)
  D := [[0, 0, 1, 4], [0, 0, 1, 4], [0, 0, 1, 4], [0, 0, 1, 4], [0, 0, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_136_10_2 : ColCert where
  rK := ⟨136, by decide⟩
  rH := ⟨10, by decide⟩
  m := 5
  T1 := T136_10
  T2 := Q2.T136_10_2
  h1 := (0,0,0,2,3)
  h2 := (0,0,0,2,3)
  D := [[0, 0, 2, 3], [0, 0, 2, 3], [0, 0, 2, 3], [0, 0, 2, 3], [0, 0, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_136_10_3 : ColCert where
  rK := ⟨136, by decide⟩
  rH := ⟨10, by decide⟩
  m := 5
  T1 := T136_10
  T2 := Q2.T136_10_2
  h1 := (0,0,0,3,2)
  h2 := (0,0,0,3,2)
  D := [[0, 0, 3, 2], [0, 0, 3, 2], [0, 0, 3, 2], [0, 0, 3, 2], [0, 0, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_136_10_4 : ColCert where
  rK := ⟨136, by decide⟩
  rH := ⟨10, by decide⟩
  m := 5
  T1 := T136_10
  T2 := Q2.T136_10_2
  h1 := (0,0,0,4,1)
  h2 := (0,0,0,4,1)
  D := [[0, 0, 4, 1], [0, 0, 4, 1], [0, 0, 4, 1], [0, 0, 4, 1], [0, 0, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_136_12_0 : ColCert where
  rK := ⟨136, by decide⟩
  rH := ⟨12, by decide⟩
  m := 5
  T1 := T136_12
  T2 := Q2.T136_12_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_136_12_1 : ColCert where
  rK := ⟨136, by decide⟩
  rH := ⟨12, by decide⟩
  m := 5
  T1 := T136_12
  T2 := Q2.T136_12_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_136_12_2 : ColCert where
  rK := ⟨136, by decide⟩
  rH := ⟨12, by decide⟩
  m := 5
  T1 := T136_12
  T2 := Q2.T136_12_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_136_12_3 : ColCert where
  rK := ⟨136, by decide⟩
  rH := ⟨12, by decide⟩
  m := 5
  T1 := T136_12
  T2 := Q2.T136_12_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_136_12_4 : ColCert where
  rK := ⟨136, by decide⟩
  rH := ⟨12, by decide⟩
  m := 5
  T1 := T136_12
  T2 := Q2.T136_12_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_136_23_0 : ColCert where
  rK := ⟨136, by decide⟩
  rH := ⟨23, by decide⟩
  m := 5
  T1 := T136_23
  T2 := Q2.T136_23_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_136_23_1 : ColCert where
  rK := ⟨136, by decide⟩
  rH := ⟨23, by decide⟩
  m := 5
  T1 := T136_23
  T2 := Q2.T136_23_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_136_23_2 : ColCert where
  rK := ⟨136, by decide⟩
  rH := ⟨23, by decide⟩
  m := 5
  T1 := T136_23
  T2 := Q2.T136_23_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_136_23_3 : ColCert where
  rK := ⟨136, by decide⟩
  rH := ⟨23, by decide⟩
  m := 5
  T1 := T136_23
  T2 := Q2.T136_23_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_136_23_4 : ColCert where
  rK := ⟨136, by decide⟩
  rH := ⟨23, by decide⟩
  m := 5
  T1 := T136_23
  T2 := Q2.T136_23_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_136_23_5 : ColCert where
  rK := ⟨136, by decide⟩
  rH := ⟨23, by decide⟩
  m := 5
  T1 := T136_23
  T2 := Q2.T136_23_2
  h1 := (1,0,1,4,0)
  h2 := (1,0,1,4,0)
  D := [[1, 0, 4, 1], [1, 0, 4, 1], [1, 0, 4, 1], [1, 0, 4, 1], [1, 0, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_136_23_10 : ColCert where
  rK := ⟨136, by decide⟩
  rH := ⟨23, by decide⟩
  m := 5
  T1 := T136_23
  T2 := Q2.T136_23_2
  h1 := (2,0,2,3,4)
  h2 := (2,0,2,3,4)
  D := [[2, 0, 3, 3], [2, 0, 3, 3], [2, 0, 3, 3], [2, 0, 3, 3], [2, 0, 3, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_136_23_15 : ColCert where
  rK := ⟨136, by decide⟩
  rH := ⟨23, by decide⟩
  m := 5
  T1 := T136_23
  T2 := Q2.T136_23_2
  h1 := (3,0,3,2,2)
  h2 := (3,0,3,2,2)
  D := [[3, 0, 2, 1], [3, 0, 2, 1], [3, 0, 2, 1], [3, 0, 2, 1], [3, 0, 2, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_136_23_20 : ColCert where
  rK := ⟨136, by decide⟩
  rH := ⟨23, by decide⟩
  m := 5
  T1 := T136_23
  T2 := Q2.T136_23_2
  h1 := (4,0,4,1,4)
  h2 := (4,0,4,1,4)
  D := [[4, 0, 1, 0], [4, 0, 1, 0], [4, 0, 1, 0], [4, 0, 1, 0], [4, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_136_29_0 : ColCert where
  rK := ⟨136, by decide⟩
  rH := ⟨29, by decide⟩
  m := 5
  T1 := T136_29
  T2 := Q2.T136_29_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_136_29_1 : ColCert where
  rK := ⟨136, by decide⟩
  rH := ⟨29, by decide⟩
  m := 5
  T1 := T136_29
  T2 := Q2.T136_29_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_136_29_2 : ColCert where
  rK := ⟨136, by decide⟩
  rH := ⟨29, by decide⟩
  m := 5
  T1 := T136_29
  T2 := Q2.T136_29_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_136_29_3 : ColCert where
  rK := ⟨136, by decide⟩
  rH := ⟨29, by decide⟩
  m := 5
  T1 := T136_29
  T2 := Q2.T136_29_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_136_29_4 : ColCert where
  rK := ⟨136, by decide⟩
  rH := ⟨29, by decide⟩
  m := 5
  T1 := T136_29
  T2 := Q2.T136_29_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_136_29_5 : ColCert where
  rK := ⟨136, by decide⟩
  rH := ⟨29, by decide⟩
  m := 5
  T1 := T136_29
  T2 := Q2.T136_29_2
  h1 := (1,4,1,3,3)
  h2 := (1,4,1,3,3)
  D := [[1, 4, 4, 0], [1, 4, 4, 1], [1, 4, 4, 2], [1, 4, 4, 3], [1, 4, 4, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_136_36_0 : ColCert where
  rK := ⟨136, by decide⟩
  rH := ⟨36, by decide⟩
  m := 5
  T1 := T136_36
  T2 := Q2.T136_36_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_136_36_1 : ColCert where
  rK := ⟨136, by decide⟩
  rH := ⟨36, by decide⟩
  m := 5
  T1 := T136_36
  T2 := Q2.T136_36_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_136_36_2 : ColCert where
  rK := ⟨136, by decide⟩
  rH := ⟨36, by decide⟩
  m := 5
  T1 := T136_36
  T2 := Q2.T136_36_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_136_36_3 : ColCert where
  rK := ⟨136, by decide⟩
  rH := ⟨36, by decide⟩
  m := 5
  T1 := T136_36
  T2 := Q2.T136_36_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_136_36_4 : ColCert where
  rK := ⟨136, by decide⟩
  rH := ⟨36, by decide⟩
  m := 5
  T1 := T136_36
  T2 := Q2.T136_36_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_136_40_0 : ColCert where
  rK := ⟨136, by decide⟩
  rH := ⟨40, by decide⟩
  m := 5
  T1 := T136_40
  T2 := Q2.T136_40_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_136_40_1 : ColCert where
  rK := ⟨136, by decide⟩
  rH := ⟨40, by decide⟩
  m := 5
  T1 := T136_40
  T2 := Q2.T136_40_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_136_40_2 : ColCert where
  rK := ⟨136, by decide⟩
  rH := ⟨40, by decide⟩
  m := 5
  T1 := T136_40
  T2 := Q2.T136_40_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_136_40_3 : ColCert where
  rK := ⟨136, by decide⟩
  rH := ⟨40, by decide⟩
  m := 5
  T1 := T136_40
  T2 := Q2.T136_40_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_136_40_4 : ColCert where
  rK := ⟨136, by decide⟩
  rH := ⟨40, by decide⟩
  m := 5
  T1 := T136_40
  T2 := Q2.T136_40_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_136_47_0 : ColCert where
  rK := ⟨136, by decide⟩
  rH := ⟨47, by decide⟩
  m := 5
  T1 := T136_47
  T2 := Q2.T136_47_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_136_47_1 : ColCert where
  rK := ⟨136, by decide⟩
  rH := ⟨47, by decide⟩
  m := 5
  T1 := T136_47
  T2 := Q2.T136_47_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_136_47_2 : ColCert where
  rK := ⟨136, by decide⟩
  rH := ⟨47, by decide⟩
  m := 5
  T1 := T136_47
  T2 := Q2.T136_47_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_136_47_3 : ColCert where
  rK := ⟨136, by decide⟩
  rH := ⟨47, by decide⟩
  m := 5
  T1 := T136_47
  T2 := Q2.T136_47_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_136_47_4 : ColCert where
  rK := ⟨136, by decide⟩
  rH := ⟨47, by decide⟩
  m := 5
  T1 := T136_47
  T2 := Q2.T136_47_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_136_48_0 : ColCert where
  rK := ⟨136, by decide⟩
  rH := ⟨48, by decide⟩
  m := 5
  T1 := T136_48
  T2 := Q2.T136_48_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_136_48_1 : ColCert where
  rK := ⟨136, by decide⟩
  rH := ⟨48, by decide⟩
  m := 5
  T1 := T136_48
  T2 := Q2.T136_48_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_136_48_2 : ColCert where
  rK := ⟨136, by decide⟩
  rH := ⟨48, by decide⟩
  m := 5
  T1 := T136_48
  T2 := Q2.T136_48_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_136_48_3 : ColCert where
  rK := ⟨136, by decide⟩
  rH := ⟨48, by decide⟩
  m := 5
  T1 := T136_48
  T2 := Q2.T136_48_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_136_48_4 : ColCert where
  rK := ⟨136, by decide⟩
  rH := ⟨48, by decide⟩
  m := 5
  T1 := T136_48
  T2 := Q2.T136_48_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_136_53_0 : ColCert where
  rK := ⟨136, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T136_53
  T2 := Q2.T136_53_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_136_53_1 : ColCert where
  rK := ⟨136, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T136_53
  T2 := Q2.T136_53_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_136_53_2 : ColCert where
  rK := ⟨136, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T136_53
  T2 := Q2.T136_53_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_136_53_3 : ColCert where
  rK := ⟨136, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T136_53
  T2 := Q2.T136_53_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_136_53_4 : ColCert where
  rK := ⟨136, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T136_53
  T2 := Q2.T136_53_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_136_53_5 : ColCert where
  rK := ⟨136, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T136_53
  T2 := Q2.T136_53_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_136_53_10 : ColCert where
  rK := ⟨136, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T136_53
  T2 := Q2.T136_53_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_136_53_15 : ColCert where
  rK := ⟨136, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T136_53
  T2 := Q2.T136_53_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_136_53_20 : ColCert where
  rK := ⟨136, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T136_53
  T2 := Q2.T136_53_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_136_84_0 : ColCert where
  rK := ⟨136, by decide⟩
  rH := ⟨84, by decide⟩
  m := 5
  T1 := T136_84
  T2 := Q2.T136_84_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_136_84_1 : ColCert where
  rK := ⟨136, by decide⟩
  rH := ⟨84, by decide⟩
  m := 5
  T1 := T136_84
  T2 := Q2.T136_84_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_136_84_2 : ColCert where
  rK := ⟨136, by decide⟩
  rH := ⟨84, by decide⟩
  m := 5
  T1 := T136_84
  T2 := Q2.T136_84_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_136_84_3 : ColCert where
  rK := ⟨136, by decide⟩
  rH := ⟨84, by decide⟩
  m := 5
  T1 := T136_84
  T2 := Q2.T136_84_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_136_84_4 : ColCert where
  rK := ⟨136, by decide⟩
  rH := ⟨84, by decide⟩
  m := 5
  T1 := T136_84
  T2 := Q2.T136_84_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_136_84_5 : ColCert where
  rK := ⟨136, by decide⟩
  rH := ⟨84, by decide⟩
  m := 5
  T1 := T136_84
  T2 := Q2.T136_84_2
  h1 := (1,0,1,0,0)
  h2 := (1,0,1,0,0)
  D := [[1, 0, 0, 0], [1, 0, 0, 0], [1, 0, 0, 0], [1, 0, 0, 0], [1, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

end LeanDring.P5Presentation
