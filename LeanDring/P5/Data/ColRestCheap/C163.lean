/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.Twin1.ColCert
import LeanDring.P5.Data.EntryK.C017

/-!
# Species-table cell data, stage 2 — twin-coincident columns (cheap tier)

Per-column certified exponent-vector data (`ColCert`/`ColCertDiv`) with kernel
`decide` bindings. Emitted; the embedded lists are what the kernel certifies.
rest tier, chunk 162: 60 columns.
-/

-- machine-emitted data: silence style linters (generated long lines, file-level options)
set_option linter.style.longLine false

namespace LeanDring.P5Presentation

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

def colCert_71_71_7 : ColCert where
  rK := ⟨71, by decide⟩
  rH := ⟨71, by decide⟩
  m := 5
  T1 := T71_71
  T2 := Q2.T71_71_2
  h1 := (1,3,2,3,1)
  h2 := (1,3,2,3,2)
  D := [[1, 2, 0], [1, 2, 4], [1, 2, 3], [1, 2, 2], [1, 2, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_71_71_8 : ColCert where
  rK := ⟨71, by decide⟩
  rH := ⟨71, by decide⟩
  m := 5
  T1 := T71_71
  T2 := Q2.T71_71_2
  h1 := (1,3,3,2,1)
  h2 := (1,3,3,2,2)
  D := [[1, 3, 3], [1, 3, 2], [1, 3, 1], [1, 3, 0], [1, 3, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_71_71_9 : ColCert where
  rK := ⟨71, by decide⟩
  rH := ⟨71, by decide⟩
  m := 5
  T1 := T71_71
  T2 := Q2.T71_71_2
  h1 := (1,3,4,1,1)
  h2 := (1,3,4,1,2)
  D := [[1, 4, 1], [1, 4, 0], [1, 4, 4], [1, 4, 3], [1, 4, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_71_71_10 : ColCert where
  rK := ⟨71, by decide⟩
  rH := ⟨71, by decide⟩
  m := 5
  T1 := T71_71
  T2 := Q2.T71_71_2
  h1 := (2,1,0,3,3)
  h2 := (2,1,0,3,1)
  D := [[2, 0, 3], [2, 0, 1], [2, 0, 4], [2, 0, 2], [2, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_71_71_11 : ColCert where
  rK := ⟨71, by decide⟩
  rH := ⟨71, by decide⟩
  m := 5
  T1 := T71_71
  T2 := Q2.T71_71_2
  h1 := (2,1,1,2,3)
  h2 := (2,1,1,2,1)
  D := [[2, 1, 4], [2, 1, 2], [2, 1, 0], [2, 1, 3], [2, 1, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_71_71_12 : ColCert where
  rK := ⟨71, by decide⟩
  rH := ⟨71, by decide⟩
  m := 5
  T1 := T71_71
  T2 := Q2.T71_71_2
  h1 := (2,1,2,1,3)
  h2 := (2,1,2,1,1)
  D := [[2, 2, 0], [2, 2, 3], [2, 2, 1], [2, 2, 4], [2, 2, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_71_71_13 : ColCert where
  rK := ⟨71, by decide⟩
  rH := ⟨71, by decide⟩
  m := 5
  T1 := T71_71
  T2 := Q2.T71_71_2
  h1 := (2,1,3,0,3)
  h2 := (2,1,3,0,1)
  D := [[2, 3, 1], [2, 3, 4], [2, 3, 2], [2, 3, 0], [2, 3, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_71_71_14 : ColCert where
  rK := ⟨71, by decide⟩
  rH := ⟨71, by decide⟩
  m := 5
  T1 := T71_71
  T2 := Q2.T71_71_2
  h1 := (2,1,4,4,3)
  h2 := (2,1,4,4,1)
  D := [[2, 4, 2], [2, 4, 0], [2, 4, 3], [2, 4, 1], [2, 4, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_71_71_15 : ColCert where
  rK := ⟨71, by decide⟩
  rH := ⟨71, by decide⟩
  m := 5
  T1 := T71_71
  T2 := Q2.T71_71_2
  h1 := (3,4,0,4,2)
  h2 := (3,4,0,4,1)
  D := [[3, 0, 2], [3, 0, 4], [3, 0, 1], [3, 0, 3], [3, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_71_71_16 : ColCert where
  rK := ⟨71, by decide⟩
  rH := ⟨71, by decide⟩
  m := 5
  T1 := T71_71
  T2 := Q2.T71_71_2
  h1 := (3,4,1,3,2)
  h2 := (3,4,1,3,1)
  D := [[3, 1, 1], [3, 1, 3], [3, 1, 0], [3, 1, 2], [3, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_71_71_17 : ColCert where
  rK := ⟨71, by decide⟩
  rH := ⟨71, by decide⟩
  m := 5
  T1 := T71_71
  T2 := Q2.T71_71_2
  h1 := (3,4,2,2,2)
  h2 := (3,4,2,2,1)
  D := [[3, 2, 0], [3, 2, 2], [3, 2, 4], [3, 2, 1], [3, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_71_71_18 : ColCert where
  rK := ⟨71, by decide⟩
  rH := ⟨71, by decide⟩
  m := 5
  T1 := T71_71
  T2 := Q2.T71_71_2
  h1 := (3,4,3,1,2)
  h2 := (3,4,3,1,1)
  D := [[3, 3, 4], [3, 3, 1], [3, 3, 3], [3, 3, 0], [3, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_71_71_19 : ColCert where
  rK := ⟨71, by decide⟩
  rH := ⟨71, by decide⟩
  m := 5
  T1 := T71_71
  T2 := Q2.T71_71_2
  h1 := (3,4,4,0,2)
  h2 := (3,4,4,0,1)
  D := [[3, 4, 3], [3, 4, 0], [3, 4, 2], [3, 4, 4], [3, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_71_71_20 : ColCert where
  rK := ⟨71, by decide⟩
  rH := ⟨71, by decide⟩
  m := 5
  T1 := T71_71
  T2 := Q2.T71_71_2
  h1 := (4,2,0,3,3)
  h2 := (4,2,0,3,4)
  D := [[4, 0, 1], [4, 0, 2], [4, 0, 3], [4, 0, 4], [4, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_71_71_21 : ColCert where
  rK := ⟨71, by decide⟩
  rH := ⟨71, by decide⟩
  m := 5
  T1 := T71_71
  T2 := Q2.T71_71_2
  h1 := (4,2,1,2,3)
  h2 := (4,2,1,2,4)
  D := [[4, 1, 3], [4, 1, 4], [4, 1, 0], [4, 1, 1], [4, 1, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_71_71_22 : ColCert where
  rK := ⟨71, by decide⟩
  rH := ⟨71, by decide⟩
  m := 5
  T1 := T71_71
  T2 := Q2.T71_71_2
  h1 := (4,2,2,1,3)
  h2 := (4,2,2,1,4)
  D := [[4, 2, 0], [4, 2, 1], [4, 2, 2], [4, 2, 3], [4, 2, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_71_71_23 : ColCert where
  rK := ⟨71, by decide⟩
  rH := ⟨71, by decide⟩
  m := 5
  T1 := T71_71
  T2 := Q2.T71_71_2
  h1 := (4,2,3,0,3)
  h2 := (4,2,3,0,4)
  D := [[4, 3, 2], [4, 3, 3], [4, 3, 4], [4, 3, 0], [4, 3, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_71_71_24 : ColCert where
  rK := ⟨71, by decide⟩
  rH := ⟨71, by decide⟩
  m := 5
  T1 := T71_71
  T2 := Q2.T71_71_2
  h1 := (4,2,4,4,3)
  h2 := (4,2,4,4,4)
  D := [[4, 4, 4], [4, 4, 0], [4, 4, 1], [4, 4, 2], [4, 4, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_72_0_0 : ColCert where
  rK := ⟨72, by decide⟩
  rH := ⟨0, by decide⟩
  m := 25
  T1 := T72_0
  T2 := Q2.T72_0_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_72_7_0 : ColCert where
  rK := ⟨72, by decide⟩
  rH := ⟨7, by decide⟩
  m := 25
  T1 := T72_7
  T2 := Q2.T72_7_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_72_7_1 : ColCert where
  rK := ⟨72, by decide⟩
  rH := ⟨7, by decide⟩
  m := 25
  T1 := T72_7
  T2 := Q2.T72_7_2
  h1 := (0,0,1,3,4)
  h2 := (0,0,1,3,4)
  D := [[0, 1, 2], [0, 1, 2], [0, 1, 2], [0, 1, 2], [0, 1, 2], [0, 1, 3], [0, 1, 3], [0, 1, 3], [0, 1, 3], [0, 1, 3], [0, 1, 4], [0, 1, 4], [0, 1, 4], [0, 1, 4], [0, 1, 4], [0, 1, 0], [0, 1, 0], [0, 1, 0], [0, 1, 0], [0, 1, 0], [0, 1, 1], [0, 1, 1], [0, 1, 1], [0, 1, 1], [0, 1, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_72_7_2 : ColCert where
  rK := ⟨72, by decide⟩
  rH := ⟨7, by decide⟩
  m := 25
  T1 := T72_7
  T2 := Q2.T72_7_2
  h1 := (0,0,2,1,3)
  h2 := (0,0,2,1,3)
  D := [[0, 2, 4], [0, 2, 4], [0, 2, 4], [0, 2, 4], [0, 2, 4], [0, 2, 1], [0, 2, 1], [0, 2, 1], [0, 2, 1], [0, 2, 1], [0, 2, 3], [0, 2, 3], [0, 2, 3], [0, 2, 3], [0, 2, 3], [0, 2, 0], [0, 2, 0], [0, 2, 0], [0, 2, 0], [0, 2, 0], [0, 2, 2], [0, 2, 2], [0, 2, 2], [0, 2, 2], [0, 2, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_72_7_3 : ColCert where
  rK := ⟨72, by decide⟩
  rH := ⟨7, by decide⟩
  m := 25
  T1 := T72_7
  T2 := Q2.T72_7_2
  h1 := (0,0,3,4,2)
  h2 := (0,0,3,4,2)
  D := [[0, 3, 1], [0, 3, 1], [0, 3, 1], [0, 3, 1], [0, 3, 1], [0, 3, 4], [0, 3, 4], [0, 3, 4], [0, 3, 4], [0, 3, 4], [0, 3, 2], [0, 3, 2], [0, 3, 2], [0, 3, 2], [0, 3, 2], [0, 3, 0], [0, 3, 0], [0, 3, 0], [0, 3, 0], [0, 3, 0], [0, 3, 3], [0, 3, 3], [0, 3, 3], [0, 3, 3], [0, 3, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_72_7_4 : ColCert where
  rK := ⟨72, by decide⟩
  rH := ⟨7, by decide⟩
  m := 25
  T1 := T72_7
  T2 := Q2.T72_7_2
  h1 := (0,0,4,2,1)
  h2 := (0,0,4,2,1)
  D := [[0, 4, 3], [0, 4, 3], [0, 4, 3], [0, 4, 3], [0, 4, 3], [0, 4, 2], [0, 4, 2], [0, 4, 2], [0, 4, 2], [0, 4, 2], [0, 4, 1], [0, 4, 1], [0, 4, 1], [0, 4, 1], [0, 4, 1], [0, 4, 0], [0, 4, 0], [0, 4, 0], [0, 4, 0], [0, 4, 0], [0, 4, 4], [0, 4, 4], [0, 4, 4], [0, 4, 4], [0, 4, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_72_12_0 : ColCert where
  rK := ⟨72, by decide⟩
  rH := ⟨12, by decide⟩
  m := 25
  T1 := T72_12
  T2 := Q2.T72_12_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_72_12_1 : ColCert where
  rK := ⟨72, by decide⟩
  rH := ⟨12, by decide⟩
  m := 25
  T1 := T72_12
  T2 := Q2.T72_12_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_72_12_2 : ColCert where
  rK := ⟨72, by decide⟩
  rH := ⟨12, by decide⟩
  m := 25
  T1 := T72_12
  T2 := Q2.T72_12_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_72_12_3 : ColCert where
  rK := ⟨72, by decide⟩
  rH := ⟨12, by decide⟩
  m := 25
  T1 := T72_12
  T2 := Q2.T72_12_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_72_12_4 : ColCert where
  rK := ⟨72, by decide⟩
  rH := ⟨12, by decide⟩
  m := 25
  T1 := T72_12
  T2 := Q2.T72_12_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_72_25_0 : ColCert where
  rK := ⟨72, by decide⟩
  rH := ⟨25, by decide⟩
  m := 25
  T1 := T72_25
  T2 := Q2.T72_25_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_72_25_1 : ColCert where
  rK := ⟨72, by decide⟩
  rH := ⟨25, by decide⟩
  m := 25
  T1 := T72_25
  T2 := Q2.T72_25_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_72_25_2 : ColCert where
  rK := ⟨72, by decide⟩
  rH := ⟨25, by decide⟩
  m := 25
  T1 := T72_25
  T2 := Q2.T72_25_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_72_25_3 : ColCert where
  rK := ⟨72, by decide⟩
  rH := ⟨25, by decide⟩
  m := 25
  T1 := T72_25
  T2 := Q2.T72_25_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_72_25_4 : ColCert where
  rK := ⟨72, by decide⟩
  rH := ⟨25, by decide⟩
  m := 25
  T1 := T72_25
  T2 := Q2.T72_25_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_72_25_5 : ColCert where
  rK := ⟨72, by decide⟩
  rH := ⟨25, by decide⟩
  m := 25
  T1 := T72_25
  T2 := Q2.T72_25_2
  h1 := (0,0,1,3,0)
  h2 := (0,0,1,3,0)
  D := [[0, 1, 3], [0, 1, 3], [0, 1, 3], [0, 1, 3], [0, 1, 3], [0, 1, 4], [0, 1, 4], [0, 1, 4], [0, 1, 4], [0, 1, 4], [0, 1, 0], [0, 1, 0], [0, 1, 0], [0, 1, 0], [0, 1, 0], [0, 1, 1], [0, 1, 1], [0, 1, 1], [0, 1, 1], [0, 1, 1], [0, 1, 2], [0, 1, 2], [0, 1, 2], [0, 1, 2], [0, 1, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_72_25_10 : ColCert where
  rK := ⟨72, by decide⟩
  rH := ⟨25, by decide⟩
  m := 25
  T1 := T72_25
  T2 := Q2.T72_25_2
  h1 := (0,0,2,1,0)
  h2 := (0,0,2,1,0)
  D := [[0, 2, 1], [0, 2, 1], [0, 2, 1], [0, 2, 1], [0, 2, 1], [0, 2, 3], [0, 2, 3], [0, 2, 3], [0, 2, 3], [0, 2, 3], [0, 2, 0], [0, 2, 0], [0, 2, 0], [0, 2, 0], [0, 2, 0], [0, 2, 2], [0, 2, 2], [0, 2, 2], [0, 2, 2], [0, 2, 2], [0, 2, 4], [0, 2, 4], [0, 2, 4], [0, 2, 4], [0, 2, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_72_25_15 : ColCert where
  rK := ⟨72, by decide⟩
  rH := ⟨25, by decide⟩
  m := 25
  T1 := T72_25
  T2 := Q2.T72_25_2
  h1 := (0,0,3,4,0)
  h2 := (0,0,3,4,0)
  D := [[0, 3, 4], [0, 3, 4], [0, 3, 4], [0, 3, 4], [0, 3, 4], [0, 3, 2], [0, 3, 2], [0, 3, 2], [0, 3, 2], [0, 3, 2], [0, 3, 0], [0, 3, 0], [0, 3, 0], [0, 3, 0], [0, 3, 0], [0, 3, 3], [0, 3, 3], [0, 3, 3], [0, 3, 3], [0, 3, 3], [0, 3, 1], [0, 3, 1], [0, 3, 1], [0, 3, 1], [0, 3, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_72_25_20 : ColCert where
  rK := ⟨72, by decide⟩
  rH := ⟨25, by decide⟩
  m := 25
  T1 := T72_25
  T2 := Q2.T72_25_2
  h1 := (0,0,4,2,0)
  h2 := (0,0,4,2,0)
  D := [[0, 4, 2], [0, 4, 2], [0, 4, 2], [0, 4, 2], [0, 4, 2], [0, 4, 1], [0, 4, 1], [0, 4, 1], [0, 4, 1], [0, 4, 1], [0, 4, 0], [0, 4, 0], [0, 4, 0], [0, 4, 0], [0, 4, 0], [0, 4, 4], [0, 4, 4], [0, 4, 4], [0, 4, 4], [0, 4, 4], [0, 4, 3], [0, 4, 3], [0, 4, 3], [0, 4, 3], [0, 4, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_72_31_0 : ColCert where
  rK := ⟨72, by decide⟩
  rH := ⟨31, by decide⟩
  m := 5
  T1 := T72_31
  T2 := Q2.T72_31_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_72_31_1 : ColCert where
  rK := ⟨72, by decide⟩
  rH := ⟨31, by decide⟩
  m := 5
  T1 := T72_31
  T2 := Q2.T72_31_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_72_31_2 : ColCert where
  rK := ⟨72, by decide⟩
  rH := ⟨31, by decide⟩
  m := 5
  T1 := T72_31
  T2 := Q2.T72_31_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_72_31_3 : ColCert where
  rK := ⟨72, by decide⟩
  rH := ⟨31, by decide⟩
  m := 5
  T1 := T72_31
  T2 := Q2.T72_31_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_72_31_4 : ColCert where
  rK := ⟨72, by decide⟩
  rH := ⟨31, by decide⟩
  m := 5
  T1 := T72_31
  T2 := Q2.T72_31_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_72_31_5 : ColCert where
  rK := ⟨72, by decide⟩
  rH := ⟨31, by decide⟩
  m := 5
  T1 := T72_31
  T2 := Q2.T72_31_2
  h1 := (1,3,2,0,4)
  h2 := (1,3,2,0,0)
  D := [[1, 2, 3], [1, 2, 2], [1, 2, 1], [1, 2, 0], [1, 2, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_72_31_10 : ColCert where
  rK := ⟨72, by decide⟩
  rH := ⟨31, by decide⟩
  m := 5
  T1 := T72_31
  T2 := Q2.T72_31_2
  h1 := (2,1,4,3,0)
  h2 := (2,1,4,3,3)
  D := [[2, 4, 4], [2, 4, 2], [2, 4, 0], [2, 4, 3], [2, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_72_31_15 : ColCert where
  rK := ⟨72, by decide⟩
  rH := ⟨31, by decide⟩
  m := 5
  T1 := T72_31
  T2 := Q2.T72_31_2
  h1 := (3,4,1,4,4)
  h2 := (3,4,1,4,3)
  D := [[3, 1, 3], [3, 1, 0], [3, 1, 2], [3, 1, 4], [3, 1, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_72_31_20 : ColCert where
  rK := ⟨72, by decide⟩
  rH := ⟨31, by decide⟩
  m := 5
  T1 := T72_31
  T2 := Q2.T72_31_2
  h1 := (4,2,3,3,1)
  h2 := (4,2,3,3,2)
  D := [[4, 3, 0], [4, 3, 1], [4, 3, 2], [4, 3, 3], [4, 3, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_72_36_0 : ColCert where
  rK := ⟨72, by decide⟩
  rH := ⟨36, by decide⟩
  m := 5
  T1 := T72_36
  T2 := Q2.T72_36_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_72_36_1 : ColCert where
  rK := ⟨72, by decide⟩
  rH := ⟨36, by decide⟩
  m := 5
  T1 := T72_36
  T2 := Q2.T72_36_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_72_36_2 : ColCert where
  rK := ⟨72, by decide⟩
  rH := ⟨36, by decide⟩
  m := 5
  T1 := T72_36
  T2 := Q2.T72_36_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_72_36_3 : ColCert where
  rK := ⟨72, by decide⟩
  rH := ⟨36, by decide⟩
  m := 5
  T1 := T72_36
  T2 := Q2.T72_36_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_72_36_4 : ColCert where
  rK := ⟨72, by decide⟩
  rH := ⟨36, by decide⟩
  m := 5
  T1 := T72_36
  T2 := Q2.T72_36_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_72_36_5 : ColCert where
  rK := ⟨72, by decide⟩
  rH := ⟨36, by decide⟩
  m := 5
  T1 := T72_36
  T2 := Q2.T72_36_2
  h1 := (1,3,1,0,1)
  h2 := (1,3,1,0,2)
  D := [[1, 1, 2], [1, 1, 1], [1, 1, 0], [1, 1, 4], [1, 1, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_72_36_10 : ColCert where
  rK := ⟨72, by decide⟩
  rH := ⟨36, by decide⟩
  m := 5
  T1 := T72_36
  T2 := Q2.T72_36_2
  h1 := (2,1,2,3,1)
  h2 := (2,1,2,3,4)
  D := [[2, 2, 3], [2, 2, 1], [2, 2, 4], [2, 2, 2], [2, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_72_36_15 : ColCert where
  rK := ⟨72, by decide⟩
  rH := ⟨36, by decide⟩
  m := 5
  T1 := T72_36
  T2 := Q2.T72_36_2
  h1 := (3,4,3,4,1)
  h2 := (3,4,3,4,0)
  D := [[3, 3, 3], [3, 3, 0], [3, 3, 2], [3, 3, 4], [3, 3, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_72_36_20 : ColCert where
  rK := ⟨72, by decide⟩
  rH := ⟨36, by decide⟩
  m := 5
  T1 := T72_36
  T2 := Q2.T72_36_2
  h1 := (4,2,4,3,1)
  h2 := (4,2,4,3,2)
  D := [[4, 4, 2], [4, 4, 3], [4, 4, 4], [4, 4, 0], [4, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_72_41_0 : ColCert where
  rK := ⟨72, by decide⟩
  rH := ⟨41, by decide⟩
  m := 5
  T1 := T72_41
  T2 := Q2.T72_41_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_72_41_1 : ColCert where
  rK := ⟨72, by decide⟩
  rH := ⟨41, by decide⟩
  m := 5
  T1 := T72_41
  T2 := Q2.T72_41_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_72_41_2 : ColCert where
  rK := ⟨72, by decide⟩
  rH := ⟨41, by decide⟩
  m := 5
  T1 := T72_41
  T2 := Q2.T72_41_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_72_41_3 : ColCert where
  rK := ⟨72, by decide⟩
  rH := ⟨41, by decide⟩
  m := 5
  T1 := T72_41
  T2 := Q2.T72_41_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

end LeanDring.P5Presentation
