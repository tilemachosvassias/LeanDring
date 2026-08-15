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
rest tier, chunk 171: 60 columns.
-/

-- machine-emitted data: silence style linters (generated long lines, file-level options)
set_option linter.style.longLine false

namespace LeanDring.P5Presentation

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

def colCert_78_6_1 : ColCert where
  rK := ⟨78, by decide⟩
  rH := ⟨6, by decide⟩
  m := 25
  T1 := T78_6
  T2 := Q2.T78_6_2
  h1 := (0,0,1,2,4)
  h2 := (0,0,1,2,4)
  D := [[0, 1, 0], [0, 1, 0], [0, 1, 0], [0, 1, 0], [0, 1, 0], [0, 1, 1], [0, 1, 1], [0, 1, 1], [0, 1, 1], [0, 1, 1], [0, 1, 2], [0, 1, 2], [0, 1, 2], [0, 1, 2], [0, 1, 2], [0, 1, 3], [0, 1, 3], [0, 1, 3], [0, 1, 3], [0, 1, 3], [0, 1, 4], [0, 1, 4], [0, 1, 4], [0, 1, 4], [0, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_78_6_2 : ColCert where
  rK := ⟨78, by decide⟩
  rH := ⟨6, by decide⟩
  m := 25
  T1 := T78_6
  T2 := Q2.T78_6_2
  h1 := (0,0,2,4,3)
  h2 := (0,0,2,4,3)
  D := [[0, 2, 0], [0, 2, 0], [0, 2, 0], [0, 2, 0], [0, 2, 0], [0, 2, 2], [0, 2, 2], [0, 2, 2], [0, 2, 2], [0, 2, 2], [0, 2, 4], [0, 2, 4], [0, 2, 4], [0, 2, 4], [0, 2, 4], [0, 2, 1], [0, 2, 1], [0, 2, 1], [0, 2, 1], [0, 2, 1], [0, 2, 3], [0, 2, 3], [0, 2, 3], [0, 2, 3], [0, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_78_6_3 : ColCert where
  rK := ⟨78, by decide⟩
  rH := ⟨6, by decide⟩
  m := 25
  T1 := T78_6
  T2 := Q2.T78_6_2
  h1 := (0,0,3,1,2)
  h2 := (0,0,3,1,2)
  D := [[0, 3, 0], [0, 3, 0], [0, 3, 0], [0, 3, 0], [0, 3, 0], [0, 3, 3], [0, 3, 3], [0, 3, 3], [0, 3, 3], [0, 3, 3], [0, 3, 1], [0, 3, 1], [0, 3, 1], [0, 3, 1], [0, 3, 1], [0, 3, 4], [0, 3, 4], [0, 3, 4], [0, 3, 4], [0, 3, 4], [0, 3, 2], [0, 3, 2], [0, 3, 2], [0, 3, 2], [0, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_78_6_4 : ColCert where
  rK := ⟨78, by decide⟩
  rH := ⟨6, by decide⟩
  m := 25
  T1 := T78_6
  T2 := Q2.T78_6_2
  h1 := (0,0,4,3,1)
  h2 := (0,0,4,3,1)
  D := [[0, 4, 0], [0, 4, 0], [0, 4, 0], [0, 4, 0], [0, 4, 0], [0, 4, 4], [0, 4, 4], [0, 4, 4], [0, 4, 4], [0, 4, 4], [0, 4, 3], [0, 4, 3], [0, 4, 3], [0, 4, 3], [0, 4, 3], [0, 4, 2], [0, 4, 2], [0, 4, 2], [0, 4, 2], [0, 4, 2], [0, 4, 1], [0, 4, 1], [0, 4, 1], [0, 4, 1], [0, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_78_12_0 : ColCert where
  rK := ⟨78, by decide⟩
  rH := ⟨12, by decide⟩
  m := 25
  T1 := T78_12
  T2 := Q2.T78_12_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_78_12_1 : ColCert where
  rK := ⟨78, by decide⟩
  rH := ⟨12, by decide⟩
  m := 25
  T1 := T78_12
  T2 := Q2.T78_12_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_78_12_2 : ColCert where
  rK := ⟨78, by decide⟩
  rH := ⟨12, by decide⟩
  m := 25
  T1 := T78_12
  T2 := Q2.T78_12_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_78_12_3 : ColCert where
  rK := ⟨78, by decide⟩
  rH := ⟨12, by decide⟩
  m := 25
  T1 := T78_12
  T2 := Q2.T78_12_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_78_12_4 : ColCert where
  rK := ⟨78, by decide⟩
  rH := ⟨12, by decide⟩
  m := 25
  T1 := T78_12
  T2 := Q2.T78_12_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_78_24_0 : ColCert where
  rK := ⟨78, by decide⟩
  rH := ⟨24, by decide⟩
  m := 25
  T1 := T78_24
  T2 := Q2.T78_24_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_78_24_1 : ColCert where
  rK := ⟨78, by decide⟩
  rH := ⟨24, by decide⟩
  m := 25
  T1 := T78_24
  T2 := Q2.T78_24_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_78_24_2 : ColCert where
  rK := ⟨78, by decide⟩
  rH := ⟨24, by decide⟩
  m := 25
  T1 := T78_24
  T2 := Q2.T78_24_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_78_24_3 : ColCert where
  rK := ⟨78, by decide⟩
  rH := ⟨24, by decide⟩
  m := 25
  T1 := T78_24
  T2 := Q2.T78_24_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_78_24_4 : ColCert where
  rK := ⟨78, by decide⟩
  rH := ⟨24, by decide⟩
  m := 25
  T1 := T78_24
  T2 := Q2.T78_24_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_78_24_5 : ColCert where
  rK := ⟨78, by decide⟩
  rH := ⟨24, by decide⟩
  m := 25
  T1 := T78_24
  T2 := Q2.T78_24_2
  h1 := (0,0,1,2,0)
  h2 := (0,0,1,2,0)
  D := [[0, 1, 1], [0, 1, 1], [0, 1, 1], [0, 1, 1], [0, 1, 1], [0, 1, 2], [0, 1, 2], [0, 1, 2], [0, 1, 2], [0, 1, 2], [0, 1, 3], [0, 1, 3], [0, 1, 3], [0, 1, 3], [0, 1, 3], [0, 1, 4], [0, 1, 4], [0, 1, 4], [0, 1, 4], [0, 1, 4], [0, 1, 0], [0, 1, 0], [0, 1, 0], [0, 1, 0], [0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_78_24_10 : ColCert where
  rK := ⟨78, by decide⟩
  rH := ⟨24, by decide⟩
  m := 25
  T1 := T78_24
  T2 := Q2.T78_24_2
  h1 := (0,0,2,4,0)
  h2 := (0,0,2,4,0)
  D := [[0, 2, 2], [0, 2, 2], [0, 2, 2], [0, 2, 2], [0, 2, 2], [0, 2, 4], [0, 2, 4], [0, 2, 4], [0, 2, 4], [0, 2, 4], [0, 2, 1], [0, 2, 1], [0, 2, 1], [0, 2, 1], [0, 2, 1], [0, 2, 3], [0, 2, 3], [0, 2, 3], [0, 2, 3], [0, 2, 3], [0, 2, 0], [0, 2, 0], [0, 2, 0], [0, 2, 0], [0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_78_24_15 : ColCert where
  rK := ⟨78, by decide⟩
  rH := ⟨24, by decide⟩
  m := 25
  T1 := T78_24
  T2 := Q2.T78_24_2
  h1 := (0,0,3,1,0)
  h2 := (0,0,3,1,0)
  D := [[0, 3, 3], [0, 3, 3], [0, 3, 3], [0, 3, 3], [0, 3, 3], [0, 3, 1], [0, 3, 1], [0, 3, 1], [0, 3, 1], [0, 3, 1], [0, 3, 4], [0, 3, 4], [0, 3, 4], [0, 3, 4], [0, 3, 4], [0, 3, 2], [0, 3, 2], [0, 3, 2], [0, 3, 2], [0, 3, 2], [0, 3, 0], [0, 3, 0], [0, 3, 0], [0, 3, 0], [0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_78_24_20 : ColCert where
  rK := ⟨78, by decide⟩
  rH := ⟨24, by decide⟩
  m := 25
  T1 := T78_24
  T2 := Q2.T78_24_2
  h1 := (0,0,4,3,0)
  h2 := (0,0,4,3,0)
  D := [[0, 4, 4], [0, 4, 4], [0, 4, 4], [0, 4, 4], [0, 4, 4], [0, 4, 3], [0, 4, 3], [0, 4, 3], [0, 4, 3], [0, 4, 3], [0, 4, 2], [0, 4, 2], [0, 4, 2], [0, 4, 2], [0, 4, 2], [0, 4, 1], [0, 4, 1], [0, 4, 1], [0, 4, 1], [0, 4, 1], [0, 4, 0], [0, 4, 0], [0, 4, 0], [0, 4, 0], [0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_78_32_0 : ColCert where
  rK := ⟨78, by decide⟩
  rH := ⟨32, by decide⟩
  m := 5
  T1 := T78_32
  T2 := Q2.T78_32_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_78_32_1 : ColCert where
  rK := ⟨78, by decide⟩
  rH := ⟨32, by decide⟩
  m := 5
  T1 := T78_32
  T2 := Q2.T78_32_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_78_32_2 : ColCert where
  rK := ⟨78, by decide⟩
  rH := ⟨32, by decide⟩
  m := 5
  T1 := T78_32
  T2 := Q2.T78_32_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_78_32_3 : ColCert where
  rK := ⟨78, by decide⟩
  rH := ⟨32, by decide⟩
  m := 5
  T1 := T78_32
  T2 := Q2.T78_32_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_78_32_4 : ColCert where
  rK := ⟨78, by decide⟩
  rH := ⟨32, by decide⟩
  m := 5
  T1 := T78_32
  T2 := Q2.T78_32_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_78_37_0 : ColCert where
  rK := ⟨78, by decide⟩
  rH := ⟨37, by decide⟩
  m := 5
  T1 := T78_37
  T2 := Q2.T78_37_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_78_37_1 : ColCert where
  rK := ⟨78, by decide⟩
  rH := ⟨37, by decide⟩
  m := 5
  T1 := T78_37
  T2 := Q2.T78_37_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_78_37_2 : ColCert where
  rK := ⟨78, by decide⟩
  rH := ⟨37, by decide⟩
  m := 5
  T1 := T78_37
  T2 := Q2.T78_37_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_78_37_3 : ColCert where
  rK := ⟨78, by decide⟩
  rH := ⟨37, by decide⟩
  m := 5
  T1 := T78_37
  T2 := Q2.T78_37_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_78_37_4 : ColCert where
  rK := ⟨78, by decide⟩
  rH := ⟨37, by decide⟩
  m := 5
  T1 := T78_37
  T2 := Q2.T78_37_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_78_42_0 : ColCert where
  rK := ⟨78, by decide⟩
  rH := ⟨42, by decide⟩
  m := 5
  T1 := T78_42
  T2 := Q2.T78_42_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_78_42_1 : ColCert where
  rK := ⟨78, by decide⟩
  rH := ⟨42, by decide⟩
  m := 5
  T1 := T78_42
  T2 := Q2.T78_42_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_78_42_2 : ColCert where
  rK := ⟨78, by decide⟩
  rH := ⟨42, by decide⟩
  m := 5
  T1 := T78_42
  T2 := Q2.T78_42_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_78_42_3 : ColCert where
  rK := ⟨78, by decide⟩
  rH := ⟨42, by decide⟩
  m := 5
  T1 := T78_42
  T2 := Q2.T78_42_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_78_42_4 : ColCert where
  rK := ⟨78, by decide⟩
  rH := ⟨42, by decide⟩
  m := 5
  T1 := T78_42
  T2 := Q2.T78_42_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_78_47_0 : ColCert where
  rK := ⟨78, by decide⟩
  rH := ⟨47, by decide⟩
  m := 5
  T1 := T78_47
  T2 := Q2.T78_47_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_78_47_1 : ColCert where
  rK := ⟨78, by decide⟩
  rH := ⟨47, by decide⟩
  m := 5
  T1 := T78_47
  T2 := Q2.T78_47_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_78_47_2 : ColCert where
  rK := ⟨78, by decide⟩
  rH := ⟨47, by decide⟩
  m := 5
  T1 := T78_47
  T2 := Q2.T78_47_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_78_47_3 : ColCert where
  rK := ⟨78, by decide⟩
  rH := ⟨47, by decide⟩
  m := 5
  T1 := T78_47
  T2 := Q2.T78_47_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_78_47_4 : ColCert where
  rK := ⟨78, by decide⟩
  rH := ⟨47, by decide⟩
  m := 5
  T1 := T78_47
  T2 := Q2.T78_47_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_78_52_0 : ColCert where
  rK := ⟨78, by decide⟩
  rH := ⟨52, by decide⟩
  m := 5
  T1 := T78_52
  T2 := Q2.T78_52_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_78_52_1 : ColCert where
  rK := ⟨78, by decide⟩
  rH := ⟨52, by decide⟩
  m := 5
  T1 := T78_52
  T2 := Q2.T78_52_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_78_52_2 : ColCert where
  rK := ⟨78, by decide⟩
  rH := ⟨52, by decide⟩
  m := 5
  T1 := T78_52
  T2 := Q2.T78_52_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_78_52_3 : ColCert where
  rK := ⟨78, by decide⟩
  rH := ⟨52, by decide⟩
  m := 5
  T1 := T78_52
  T2 := Q2.T78_52_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_78_52_4 : ColCert where
  rK := ⟨78, by decide⟩
  rH := ⟨52, by decide⟩
  m := 5
  T1 := T78_52
  T2 := Q2.T78_52_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_78_78_0 : ColCert where
  rK := ⟨78, by decide⟩
  rH := ⟨78, by decide⟩
  m := 5
  T1 := T78_78
  T2 := Q2.T78_78_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_78_78_1 : ColCert where
  rK := ⟨78, by decide⟩
  rH := ⟨78, by decide⟩
  m := 5
  T1 := T78_78
  T2 := Q2.T78_78_2
  h1 := (0,0,1,2,0)
  h2 := (0,0,1,2,0)
  D := [[0, 1, 0], [0, 1, 0], [0, 1, 0], [0, 1, 0], [0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_78_78_2 : ColCert where
  rK := ⟨78, by decide⟩
  rH := ⟨78, by decide⟩
  m := 5
  T1 := T78_78
  T2 := Q2.T78_78_2
  h1 := (0,0,2,4,0)
  h2 := (0,0,2,4,0)
  D := [[0, 2, 0], [0, 2, 0], [0, 2, 0], [0, 2, 0], [0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_78_78_3 : ColCert where
  rK := ⟨78, by decide⟩
  rH := ⟨78, by decide⟩
  m := 5
  T1 := T78_78
  T2 := Q2.T78_78_2
  h1 := (0,0,3,1,0)
  h2 := (0,0,3,1,0)
  D := [[0, 3, 0], [0, 3, 0], [0, 3, 0], [0, 3, 0], [0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_78_78_4 : ColCert where
  rK := ⟨78, by decide⟩
  rH := ⟨78, by decide⟩
  m := 5
  T1 := T78_78
  T2 := Q2.T78_78_2
  h1 := (0,0,4,3,0)
  h2 := (0,0,4,3,0)
  D := [[0, 4, 0], [0, 4, 0], [0, 4, 0], [0, 4, 0], [0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_78_78_5 : ColCert where
  rK := ⟨78, by decide⟩
  rH := ⟨78, by decide⟩
  m := 5
  T1 := T78_78
  T2 := Q2.T78_78_2
  h1 := (1,1,0,4,2)
  h2 := (1,1,0,4,3)
  D := [[1, 0, 0], [1, 0, 4], [1, 0, 3], [1, 0, 2], [1, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_78_78_6 : ColCert where
  rK := ⟨78, by decide⟩
  rH := ⟨78, by decide⟩
  m := 5
  T1 := T78_78
  T2 := Q2.T78_78_2
  h1 := (1,1,1,1,2)
  h2 := (1,1,1,1,3)
  D := [[1, 1, 2], [1, 1, 1], [1, 1, 0], [1, 1, 4], [1, 1, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_78_78_7 : ColCert where
  rK := ⟨78, by decide⟩
  rH := ⟨78, by decide⟩
  m := 5
  T1 := T78_78
  T2 := Q2.T78_78_2
  h1 := (1,1,2,3,2)
  h2 := (1,1,2,3,3)
  D := [[1, 2, 4], [1, 2, 3], [1, 2, 2], [1, 2, 1], [1, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_78_78_8 : ColCert where
  rK := ⟨78, by decide⟩
  rH := ⟨78, by decide⟩
  m := 5
  T1 := T78_78
  T2 := Q2.T78_78_2
  h1 := (1,1,3,0,2)
  h2 := (1,1,3,0,3)
  D := [[1, 3, 1], [1, 3, 0], [1, 3, 4], [1, 3, 3], [1, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_78_78_9 : ColCert where
  rK := ⟨78, by decide⟩
  rH := ⟨78, by decide⟩
  m := 5
  T1 := T78_78
  T2 := Q2.T78_78_2
  h1 := (1,1,4,2,2)
  h2 := (1,1,4,2,3)
  D := [[1, 4, 3], [1, 4, 2], [1, 4, 1], [1, 4, 0], [1, 4, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_78_78_10 : ColCert where
  rK := ⟨78, by decide⟩
  rH := ⟨78, by decide⟩
  m := 5
  T1 := T78_78
  T2 := Q2.T78_78_2
  h1 := (2,2,0,4,3)
  h2 := (2,2,0,4,0)
  D := [[2, 0, 0], [2, 0, 3], [2, 0, 1], [2, 0, 4], [2, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_78_78_11 : ColCert where
  rK := ⟨78, by decide⟩
  rH := ⟨78, by decide⟩
  m := 5
  T1 := T78_78
  T2 := Q2.T78_78_2
  h1 := (2,2,1,1,3)
  h2 := (2,2,1,1,0)
  D := [[2, 1, 4], [2, 1, 2], [2, 1, 0], [2, 1, 3], [2, 1, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_78_78_12 : ColCert where
  rK := ⟨78, by decide⟩
  rH := ⟨78, by decide⟩
  m := 5
  T1 := T78_78
  T2 := Q2.T78_78_2
  h1 := (2,2,2,3,3)
  h2 := (2,2,2,3,0)
  D := [[2, 2, 3], [2, 2, 1], [2, 2, 4], [2, 2, 2], [2, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_78_78_13 : ColCert where
  rK := ⟨78, by decide⟩
  rH := ⟨78, by decide⟩
  m := 5
  T1 := T78_78
  T2 := Q2.T78_78_2
  h1 := (2,2,3,0,3)
  h2 := (2,2,3,0,0)
  D := [[2, 3, 2], [2, 3, 0], [2, 3, 3], [2, 3, 1], [2, 3, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_78_78_14 : ColCert where
  rK := ⟨78, by decide⟩
  rH := ⟨78, by decide⟩
  m := 5
  T1 := T78_78
  T2 := Q2.T78_78_2
  h1 := (2,2,4,2,3)
  h2 := (2,2,4,2,0)
  D := [[2, 4, 1], [2, 4, 4], [2, 4, 2], [2, 4, 0], [2, 4, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_78_78_15 : ColCert where
  rK := ⟨78, by decide⟩
  rH := ⟨78, by decide⟩
  m := 5
  T1 := T78_78
  T2 := Q2.T78_78_2
  h1 := (3,3,0,0,4)
  h2 := (3,3,0,0,2)
  D := [[3, 0, 0], [3, 0, 2], [3, 0, 4], [3, 0, 1], [3, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_78_78_16 : ColCert where
  rK := ⟨78, by decide⟩
  rH := ⟨78, by decide⟩
  m := 5
  T1 := T78_78
  T2 := Q2.T78_78_2
  h1 := (3,3,1,2,4)
  h2 := (3,3,1,2,2)
  D := [[3, 1, 1], [3, 1, 3], [3, 1, 0], [3, 1, 2], [3, 1, 4]]
  bind1 := by decide
  bind2 := by decide

end LeanDring.P5Presentation
