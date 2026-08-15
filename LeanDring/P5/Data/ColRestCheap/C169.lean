/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.Twin1.ColCert
import LeanDring.P5.Data.EntryK.C018

/-!
# Species-table cell data, stage 2 — twin-coincident columns (cheap tier)

Per-column certified exponent-vector data (`ColCert`/`ColCertDiv`) with kernel
`decide` bindings. Emitted; the embedded lists are what the kernel certifies.
rest tier, chunk 168: 60 columns.
-/

-- machine-emitted data: silence style linters (generated long lines, file-level options)
set_option linter.style.longLine false

namespace LeanDring.P5Presentation

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

def colCert_76_1_1 : ColCert where
  rK := ⟨76, by decide⟩
  rH := ⟨1, by decide⟩
  m := 25
  T1 := T76_1
  T2 := Q2.T76_1_2
  h1 := (0,0,1,4,4)
  h2 := (0,0,1,4,4)
  D := [[0, 1, 0], [0, 1, 0], [0, 1, 0], [0, 1, 0], [0, 1, 0], [0, 1, 1], [0, 1, 1], [0, 1, 1], [0, 1, 1], [0, 1, 1], [0, 1, 2], [0, 1, 2], [0, 1, 2], [0, 1, 2], [0, 1, 2], [0, 1, 3], [0, 1, 3], [0, 1, 3], [0, 1, 3], [0, 1, 3], [0, 1, 4], [0, 1, 4], [0, 1, 4], [0, 1, 4], [0, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_76_1_2 : ColCert where
  rK := ⟨76, by decide⟩
  rH := ⟨1, by decide⟩
  m := 25
  T1 := T76_1
  T2 := Q2.T76_1_2
  h1 := (0,0,2,3,3)
  h2 := (0,0,2,3,3)
  D := [[0, 2, 0], [0, 2, 0], [0, 2, 0], [0, 2, 0], [0, 2, 0], [0, 2, 2], [0, 2, 2], [0, 2, 2], [0, 2, 2], [0, 2, 2], [0, 2, 4], [0, 2, 4], [0, 2, 4], [0, 2, 4], [0, 2, 4], [0, 2, 1], [0, 2, 1], [0, 2, 1], [0, 2, 1], [0, 2, 1], [0, 2, 3], [0, 2, 3], [0, 2, 3], [0, 2, 3], [0, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_76_1_3 : ColCert where
  rK := ⟨76, by decide⟩
  rH := ⟨1, by decide⟩
  m := 25
  T1 := T76_1
  T2 := Q2.T76_1_2
  h1 := (0,0,3,2,2)
  h2 := (0,0,3,2,2)
  D := [[0, 3, 0], [0, 3, 0], [0, 3, 0], [0, 3, 0], [0, 3, 0], [0, 3, 3], [0, 3, 3], [0, 3, 3], [0, 3, 3], [0, 3, 3], [0, 3, 1], [0, 3, 1], [0, 3, 1], [0, 3, 1], [0, 3, 1], [0, 3, 4], [0, 3, 4], [0, 3, 4], [0, 3, 4], [0, 3, 4], [0, 3, 2], [0, 3, 2], [0, 3, 2], [0, 3, 2], [0, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_76_1_4 : ColCert where
  rK := ⟨76, by decide⟩
  rH := ⟨1, by decide⟩
  m := 25
  T1 := T76_1
  T2 := Q2.T76_1_2
  h1 := (0,0,4,1,1)
  h2 := (0,0,4,1,1)
  D := [[0, 4, 0], [0, 4, 0], [0, 4, 0], [0, 4, 0], [0, 4, 0], [0, 4, 4], [0, 4, 4], [0, 4, 4], [0, 4, 4], [0, 4, 4], [0, 4, 3], [0, 4, 3], [0, 4, 3], [0, 4, 3], [0, 4, 3], [0, 4, 2], [0, 4, 2], [0, 4, 2], [0, 4, 2], [0, 4, 2], [0, 4, 1], [0, 4, 1], [0, 4, 1], [0, 4, 1], [0, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_76_12_0 : ColCert where
  rK := ⟨76, by decide⟩
  rH := ⟨12, by decide⟩
  m := 25
  T1 := T76_12
  T2 := Q2.T76_12_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_76_12_1 : ColCert where
  rK := ⟨76, by decide⟩
  rH := ⟨12, by decide⟩
  m := 25
  T1 := T76_12
  T2 := Q2.T76_12_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_76_12_2 : ColCert where
  rK := ⟨76, by decide⟩
  rH := ⟨12, by decide⟩
  m := 25
  T1 := T76_12
  T2 := Q2.T76_12_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_76_12_3 : ColCert where
  rK := ⟨76, by decide⟩
  rH := ⟨12, by decide⟩
  m := 25
  T1 := T76_12
  T2 := Q2.T76_12_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_76_12_4 : ColCert where
  rK := ⟨76, by decide⟩
  rH := ⟨12, by decide⟩
  m := 25
  T1 := T76_12
  T2 := Q2.T76_12_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_76_19_0 : ColCert where
  rK := ⟨76, by decide⟩
  rH := ⟨19, by decide⟩
  m := 25
  T1 := T76_19
  T2 := Q2.T76_19_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_76_19_1 : ColCert where
  rK := ⟨76, by decide⟩
  rH := ⟨19, by decide⟩
  m := 25
  T1 := T76_19
  T2 := Q2.T76_19_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_76_19_2 : ColCert where
  rK := ⟨76, by decide⟩
  rH := ⟨19, by decide⟩
  m := 25
  T1 := T76_19
  T2 := Q2.T76_19_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_76_19_3 : ColCert where
  rK := ⟨76, by decide⟩
  rH := ⟨19, by decide⟩
  m := 25
  T1 := T76_19
  T2 := Q2.T76_19_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_76_19_4 : ColCert where
  rK := ⟨76, by decide⟩
  rH := ⟨19, by decide⟩
  m := 25
  T1 := T76_19
  T2 := Q2.T76_19_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_76_19_5 : ColCert where
  rK := ⟨76, by decide⟩
  rH := ⟨19, by decide⟩
  m := 25
  T1 := T76_19
  T2 := Q2.T76_19_2
  h1 := (0,0,1,4,0)
  h2 := (0,0,1,4,0)
  D := [[0, 1, 1], [0, 1, 1], [0, 1, 1], [0, 1, 1], [0, 1, 1], [0, 1, 2], [0, 1, 2], [0, 1, 2], [0, 1, 2], [0, 1, 2], [0, 1, 3], [0, 1, 3], [0, 1, 3], [0, 1, 3], [0, 1, 3], [0, 1, 4], [0, 1, 4], [0, 1, 4], [0, 1, 4], [0, 1, 4], [0, 1, 0], [0, 1, 0], [0, 1, 0], [0, 1, 0], [0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_76_19_10 : ColCert where
  rK := ⟨76, by decide⟩
  rH := ⟨19, by decide⟩
  m := 25
  T1 := T76_19
  T2 := Q2.T76_19_2
  h1 := (0,0,2,3,0)
  h2 := (0,0,2,3,0)
  D := [[0, 2, 2], [0, 2, 2], [0, 2, 2], [0, 2, 2], [0, 2, 2], [0, 2, 4], [0, 2, 4], [0, 2, 4], [0, 2, 4], [0, 2, 4], [0, 2, 1], [0, 2, 1], [0, 2, 1], [0, 2, 1], [0, 2, 1], [0, 2, 3], [0, 2, 3], [0, 2, 3], [0, 2, 3], [0, 2, 3], [0, 2, 0], [0, 2, 0], [0, 2, 0], [0, 2, 0], [0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_76_19_15 : ColCert where
  rK := ⟨76, by decide⟩
  rH := ⟨19, by decide⟩
  m := 25
  T1 := T76_19
  T2 := Q2.T76_19_2
  h1 := (0,0,3,2,0)
  h2 := (0,0,3,2,0)
  D := [[0, 3, 3], [0, 3, 3], [0, 3, 3], [0, 3, 3], [0, 3, 3], [0, 3, 1], [0, 3, 1], [0, 3, 1], [0, 3, 1], [0, 3, 1], [0, 3, 4], [0, 3, 4], [0, 3, 4], [0, 3, 4], [0, 3, 4], [0, 3, 2], [0, 3, 2], [0, 3, 2], [0, 3, 2], [0, 3, 2], [0, 3, 0], [0, 3, 0], [0, 3, 0], [0, 3, 0], [0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_76_19_20 : ColCert where
  rK := ⟨76, by decide⟩
  rH := ⟨19, by decide⟩
  m := 25
  T1 := T76_19
  T2 := Q2.T76_19_2
  h1 := (0,0,4,1,0)
  h2 := (0,0,4,1,0)
  D := [[0, 4, 4], [0, 4, 4], [0, 4, 4], [0, 4, 4], [0, 4, 4], [0, 4, 3], [0, 4, 3], [0, 4, 3], [0, 4, 3], [0, 4, 3], [0, 4, 2], [0, 4, 2], [0, 4, 2], [0, 4, 2], [0, 4, 2], [0, 4, 1], [0, 4, 1], [0, 4, 1], [0, 4, 1], [0, 4, 1], [0, 4, 0], [0, 4, 0], [0, 4, 0], [0, 4, 0], [0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_76_32_0 : ColCert where
  rK := ⟨76, by decide⟩
  rH := ⟨32, by decide⟩
  m := 5
  T1 := T76_32
  T2 := Q2.T76_32_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_76_32_1 : ColCert where
  rK := ⟨76, by decide⟩
  rH := ⟨32, by decide⟩
  m := 5
  T1 := T76_32
  T2 := Q2.T76_32_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_76_32_2 : ColCert where
  rK := ⟨76, by decide⟩
  rH := ⟨32, by decide⟩
  m := 5
  T1 := T76_32
  T2 := Q2.T76_32_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_76_32_3 : ColCert where
  rK := ⟨76, by decide⟩
  rH := ⟨32, by decide⟩
  m := 5
  T1 := T76_32
  T2 := Q2.T76_32_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_76_32_4 : ColCert where
  rK := ⟨76, by decide⟩
  rH := ⟨32, by decide⟩
  m := 5
  T1 := T76_32
  T2 := Q2.T76_32_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_76_32_5 : ColCert where
  rK := ⟨76, by decide⟩
  rH := ⟨32, by decide⟩
  m := 5
  T1 := T76_32
  T2 := Q2.T76_32_2
  h1 := (1,1,4,4,0)
  h2 := (1,1,4,4,3)
  D := [[1, 4, 4], [1, 4, 3], [1, 4, 2], [1, 4, 1], [1, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_76_32_10 : ColCert where
  rK := ⟨76, by decide⟩
  rH := ⟨32, by decide⟩
  m := 5
  T1 := T76_32
  T2 := Q2.T76_32_2
  h1 := (2,2,3,4,3)
  h2 := (2,2,3,4,4)
  D := [[2, 3, 3], [2, 3, 1], [2, 3, 4], [2, 3, 2], [2, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_76_32_15 : ColCert where
  rK := ⟨76, by decide⟩
  rH := ⟨32, by decide⟩
  m := 5
  T1 := T76_32
  T2 := Q2.T76_32_2
  h1 := (3,3,2,0,0)
  h2 := (3,3,2,0,4)
  D := [[3, 2, 2], [3, 2, 4], [3, 2, 1], [3, 2, 3], [3, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_76_32_20 : ColCert where
  rK := ⟨76, by decide⟩
  rH := ⟨32, by decide⟩
  m := 5
  T1 := T76_32
  T2 := Q2.T76_32_2
  h1 := (4,4,1,2,2)
  h2 := (4,4,1,2,4)
  D := [[4, 1, 1], [4, 1, 2], [4, 1, 3], [4, 1, 4], [4, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_76_37_0 : ColCert where
  rK := ⟨76, by decide⟩
  rH := ⟨37, by decide⟩
  m := 5
  T1 := T76_37
  T2 := Q2.T76_37_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_76_37_1 : ColCert where
  rK := ⟨76, by decide⟩
  rH := ⟨37, by decide⟩
  m := 5
  T1 := T76_37
  T2 := Q2.T76_37_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_76_37_2 : ColCert where
  rK := ⟨76, by decide⟩
  rH := ⟨37, by decide⟩
  m := 5
  T1 := T76_37
  T2 := Q2.T76_37_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_76_37_3 : ColCert where
  rK := ⟨76, by decide⟩
  rH := ⟨37, by decide⟩
  m := 5
  T1 := T76_37
  T2 := Q2.T76_37_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_76_37_4 : ColCert where
  rK := ⟨76, by decide⟩
  rH := ⟨37, by decide⟩
  m := 5
  T1 := T76_37
  T2 := Q2.T76_37_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_76_37_5 : ColCert where
  rK := ⟨76, by decide⟩
  rH := ⟨37, by decide⟩
  m := 5
  T1 := T76_37
  T2 := Q2.T76_37_2
  h1 := (1,1,2,4,3)
  h2 := (1,1,2,4,1)
  D := [[1, 2, 2], [1, 2, 1], [1, 2, 0], [1, 2, 4], [1, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_76_37_10 : ColCert where
  rK := ⟨76, by decide⟩
  rH := ⟨37, by decide⟩
  m := 5
  T1 := T76_37
  T2 := Q2.T76_37_2
  h1 := (2,2,4,4,2)
  h2 := (2,2,4,4,3)
  D := [[2, 4, 4], [2, 4, 2], [2, 4, 0], [2, 4, 3], [2, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_76_37_15 : ColCert where
  rK := ⟨76, by decide⟩
  rH := ⟨37, by decide⟩
  m := 5
  T1 := T76_37
  T2 := Q2.T76_37_2
  h1 := (3,3,1,0,3)
  h2 := (3,3,1,0,2)
  D := [[3, 1, 1], [3, 1, 3], [3, 1, 0], [3, 1, 2], [3, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_76_37_20 : ColCert where
  rK := ⟨76, by decide⟩
  rH := ⟨37, by decide⟩
  m := 5
  T1 := T76_37
  T2 := Q2.T76_37_2
  h1 := (4,4,3,2,2)
  h2 := (4,4,3,2,4)
  D := [[4, 3, 3], [4, 3, 4], [4, 3, 0], [4, 3, 1], [4, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_76_42_0 : ColCert where
  rK := ⟨76, by decide⟩
  rH := ⟨42, by decide⟩
  m := 5
  T1 := T76_42
  T2 := Q2.T76_42_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_76_42_1 : ColCert where
  rK := ⟨76, by decide⟩
  rH := ⟨42, by decide⟩
  m := 5
  T1 := T76_42
  T2 := Q2.T76_42_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_76_42_2 : ColCert where
  rK := ⟨76, by decide⟩
  rH := ⟨42, by decide⟩
  m := 5
  T1 := T76_42
  T2 := Q2.T76_42_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_76_42_3 : ColCert where
  rK := ⟨76, by decide⟩
  rH := ⟨42, by decide⟩
  m := 5
  T1 := T76_42
  T2 := Q2.T76_42_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_76_42_4 : ColCert where
  rK := ⟨76, by decide⟩
  rH := ⟨42, by decide⟩
  m := 5
  T1 := T76_42
  T2 := Q2.T76_42_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_76_42_5 : ColCert where
  rK := ⟨76, by decide⟩
  rH := ⟨42, by decide⟩
  m := 5
  T1 := T76_42
  T2 := Q2.T76_42_2
  h1 := (1,1,3,4,4)
  h2 := (1,1,3,4,2)
  D := [[1, 3, 2], [1, 3, 1], [1, 3, 0], [1, 3, 4], [1, 3, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_76_42_10 : ColCert where
  rK := ⟨76, by decide⟩
  rH := ⟨42, by decide⟩
  m := 5
  T1 := T76_42
  T2 := Q2.T76_42_2
  h1 := (2,2,1,4,0)
  h2 := (2,2,1,4,1)
  D := [[2, 1, 4], [2, 1, 2], [2, 1, 0], [2, 1, 3], [2, 1, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_76_42_15 : ColCert where
  rK := ⟨76, by decide⟩
  rH := ⟨42, by decide⟩
  m := 5
  T1 := T76_42
  T2 := Q2.T76_42_2
  h1 := (3,3,4,0,4)
  h2 := (3,3,4,0,3)
  D := [[3, 4, 1], [3, 4, 3], [3, 4, 0], [3, 4, 2], [3, 4, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_76_42_20 : ColCert where
  rK := ⟨76, by decide⟩
  rH := ⟨42, by decide⟩
  m := 5
  T1 := T76_42
  T2 := Q2.T76_42_2
  h1 := (4,4,2,2,2)
  h2 := (4,4,2,2,4)
  D := [[4, 2, 3], [4, 2, 4], [4, 2, 0], [4, 2, 1], [4, 2, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_76_47_0 : ColCert where
  rK := ⟨76, by decide⟩
  rH := ⟨47, by decide⟩
  m := 5
  T1 := T76_47
  T2 := Q2.T76_47_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_76_47_1 : ColCert where
  rK := ⟨76, by decide⟩
  rH := ⟨47, by decide⟩
  m := 5
  T1 := T76_47
  T2 := Q2.T76_47_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_76_47_2 : ColCert where
  rK := ⟨76, by decide⟩
  rH := ⟨47, by decide⟩
  m := 5
  T1 := T76_47
  T2 := Q2.T76_47_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_76_47_3 : ColCert where
  rK := ⟨76, by decide⟩
  rH := ⟨47, by decide⟩
  m := 5
  T1 := T76_47
  T2 := Q2.T76_47_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_76_47_4 : ColCert where
  rK := ⟨76, by decide⟩
  rH := ⟨47, by decide⟩
  m := 5
  T1 := T76_47
  T2 := Q2.T76_47_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_76_47_5 : ColCert where
  rK := ⟨76, by decide⟩
  rH := ⟨47, by decide⟩
  m := 5
  T1 := T76_47
  T2 := Q2.T76_47_2
  h1 := (1,1,1,4,2)
  h2 := (1,1,1,4,0)
  D := [[1, 1, 4], [1, 1, 3], [1, 1, 2], [1, 1, 1], [1, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_76_47_10 : ColCert where
  rK := ⟨76, by decide⟩
  rH := ⟨47, by decide⟩
  m := 5
  T1 := T76_47
  T2 := Q2.T76_47_2
  h1 := (2,2,2,4,4)
  h2 := (2,2,2,4,0)
  D := [[2, 2, 3], [2, 2, 1], [2, 2, 4], [2, 2, 2], [2, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_76_47_15 : ColCert where
  rK := ⟨76, by decide⟩
  rH := ⟨47, by decide⟩
  m := 5
  T1 := T76_47
  T2 := Q2.T76_47_2
  h1 := (3,3,3,0,2)
  h2 := (3,3,3,0,1)
  D := [[3, 3, 2], [3, 3, 4], [3, 3, 1], [3, 3, 3], [3, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_76_47_20 : ColCert where
  rK := ⟨76, by decide⟩
  rH := ⟨47, by decide⟩
  m := 5
  T1 := T76_47
  T2 := Q2.T76_47_2
  h1 := (4,4,4,2,2)
  h2 := (4,4,4,2,4)
  D := [[4, 4, 1], [4, 4, 2], [4, 4, 3], [4, 4, 4], [4, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_76_52_0 : ColCert where
  rK := ⟨76, by decide⟩
  rH := ⟨52, by decide⟩
  m := 5
  T1 := T76_52
  T2 := Q2.T76_52_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_76_52_1 : ColCert where
  rK := ⟨76, by decide⟩
  rH := ⟨52, by decide⟩
  m := 5
  T1 := T76_52
  T2 := Q2.T76_52_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_76_52_2 : ColCert where
  rK := ⟨76, by decide⟩
  rH := ⟨52, by decide⟩
  m := 5
  T1 := T76_52
  T2 := Q2.T76_52_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_76_52_3 : ColCert where
  rK := ⟨76, by decide⟩
  rH := ⟨52, by decide⟩
  m := 5
  T1 := T76_52
  T2 := Q2.T76_52_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_76_52_4 : ColCert where
  rK := ⟨76, by decide⟩
  rH := ⟨52, by decide⟩
  m := 5
  T1 := T76_52
  T2 := Q2.T76_52_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_76_52_5 : ColCert where
  rK := ⟨76, by decide⟩
  rH := ⟨52, by decide⟩
  m := 5
  T1 := T76_52
  T2 := Q2.T76_52_2
  h1 := (1,1,0,4,1)
  h2 := (1,1,0,4,4)
  D := [[1, 0, 3], [1, 0, 2], [1, 0, 1], [1, 0, 0], [1, 0, 4]]
  bind1 := by decide
  bind2 := by decide

end LeanDring.P5Presentation
