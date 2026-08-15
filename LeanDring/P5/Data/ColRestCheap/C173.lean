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
rest tier, chunk 172: 60 columns.
-/

-- machine-emitted data: silence style linters (generated long lines, file-level options)
set_option linter.style.longLine false

namespace LeanDring.P5Presentation

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

def colCert_78_78_17 : ColCert where
  rK := ⟨78, by decide⟩
  rH := ⟨78, by decide⟩
  m := 5
  T1 := T78_78
  T2 := Q2.T78_78_2
  h1 := (3,3,2,4,4)
  h2 := (3,3,2,4,2)
  D := [[3, 2, 2], [3, 2, 4], [3, 2, 1], [3, 2, 3], [3, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_78_78_18 : ColCert where
  rK := ⟨78, by decide⟩
  rH := ⟨78, by decide⟩
  m := 5
  T1 := T78_78
  T2 := Q2.T78_78_2
  h1 := (3,3,3,1,4)
  h2 := (3,3,3,1,2)
  D := [[3, 3, 3], [3, 3, 0], [3, 3, 2], [3, 3, 4], [3, 3, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_78_78_19 : ColCert where
  rK := ⟨78, by decide⟩
  rH := ⟨78, by decide⟩
  m := 5
  T1 := T78_78
  T2 := Q2.T78_78_2
  h1 := (3,3,4,3,4)
  h2 := (3,3,4,3,2)
  D := [[3, 4, 4], [3, 4, 1], [3, 4, 3], [3, 4, 0], [3, 4, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_78_78_20 : ColCert where
  rK := ⟨78, by decide⟩
  rH := ⟨78, by decide⟩
  m := 5
  T1 := T78_78
  T2 := Q2.T78_78_2
  h1 := (4,4,0,2,1)
  h2 := (4,4,0,2,0)
  D := [[4, 0, 0], [4, 0, 1], [4, 0, 2], [4, 0, 3], [4, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_78_78_21 : ColCert where
  rK := ⟨78, by decide⟩
  rH := ⟨78, by decide⟩
  m := 5
  T1 := T78_78
  T2 := Q2.T78_78_2
  h1 := (4,4,1,4,1)
  h2 := (4,4,1,4,0)
  D := [[4, 1, 3], [4, 1, 4], [4, 1, 0], [4, 1, 1], [4, 1, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_78_78_22 : ColCert where
  rK := ⟨78, by decide⟩
  rH := ⟨78, by decide⟩
  m := 5
  T1 := T78_78
  T2 := Q2.T78_78_2
  h1 := (4,4,2,1,1)
  h2 := (4,4,2,1,0)
  D := [[4, 2, 1], [4, 2, 2], [4, 2, 3], [4, 2, 4], [4, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_78_78_23 : ColCert where
  rK := ⟨78, by decide⟩
  rH := ⟨78, by decide⟩
  m := 5
  T1 := T78_78
  T2 := Q2.T78_78_2
  h1 := (4,4,3,3,1)
  h2 := (4,4,3,3,0)
  D := [[4, 3, 4], [4, 3, 0], [4, 3, 1], [4, 3, 2], [4, 3, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_78_78_24 : ColCert where
  rK := ⟨78, by decide⟩
  rH := ⟨78, by decide⟩
  m := 5
  T1 := T78_78
  T2 := Q2.T78_78_2
  h1 := (4,4,4,0,1)
  h2 := (4,4,4,0,0)
  D := [[4, 4, 2], [4, 4, 3], [4, 4, 4], [4, 4, 0], [4, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_79_0_0 : ColCert where
  rK := ⟨79, by decide⟩
  rH := ⟨0, by decide⟩
  m := 25
  T1 := T79_0
  T2 := Q2.T79_0_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_79_8_0 : ColCert where
  rK := ⟨79, by decide⟩
  rH := ⟨8, by decide⟩
  m := 25
  T1 := T79_8
  T2 := Q2.T79_8_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_79_8_1 : ColCert where
  rK := ⟨79, by decide⟩
  rH := ⟨8, by decide⟩
  m := 25
  T1 := T79_8
  T2 := Q2.T79_8_2
  h1 := (0,0,1,1,4)
  h2 := (0,0,1,1,4)
  D := [[0, 1, 0], [0, 1, 0], [0, 1, 0], [0, 1, 0], [0, 1, 0], [0, 1, 1], [0, 1, 1], [0, 1, 1], [0, 1, 1], [0, 1, 1], [0, 1, 2], [0, 1, 2], [0, 1, 2], [0, 1, 2], [0, 1, 2], [0, 1, 3], [0, 1, 3], [0, 1, 3], [0, 1, 3], [0, 1, 3], [0, 1, 4], [0, 1, 4], [0, 1, 4], [0, 1, 4], [0, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_79_8_2 : ColCert where
  rK := ⟨79, by decide⟩
  rH := ⟨8, by decide⟩
  m := 25
  T1 := T79_8
  T2 := Q2.T79_8_2
  h1 := (0,0,2,2,3)
  h2 := (0,0,2,2,3)
  D := [[0, 2, 0], [0, 2, 0], [0, 2, 0], [0, 2, 0], [0, 2, 0], [0, 2, 2], [0, 2, 2], [0, 2, 2], [0, 2, 2], [0, 2, 2], [0, 2, 4], [0, 2, 4], [0, 2, 4], [0, 2, 4], [0, 2, 4], [0, 2, 1], [0, 2, 1], [0, 2, 1], [0, 2, 1], [0, 2, 1], [0, 2, 3], [0, 2, 3], [0, 2, 3], [0, 2, 3], [0, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_79_8_3 : ColCert where
  rK := ⟨79, by decide⟩
  rH := ⟨8, by decide⟩
  m := 25
  T1 := T79_8
  T2 := Q2.T79_8_2
  h1 := (0,0,3,3,2)
  h2 := (0,0,3,3,2)
  D := [[0, 3, 0], [0, 3, 0], [0, 3, 0], [0, 3, 0], [0, 3, 0], [0, 3, 3], [0, 3, 3], [0, 3, 3], [0, 3, 3], [0, 3, 3], [0, 3, 1], [0, 3, 1], [0, 3, 1], [0, 3, 1], [0, 3, 1], [0, 3, 4], [0, 3, 4], [0, 3, 4], [0, 3, 4], [0, 3, 4], [0, 3, 2], [0, 3, 2], [0, 3, 2], [0, 3, 2], [0, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_79_8_4 : ColCert where
  rK := ⟨79, by decide⟩
  rH := ⟨8, by decide⟩
  m := 25
  T1 := T79_8
  T2 := Q2.T79_8_2
  h1 := (0,0,4,4,1)
  h2 := (0,0,4,4,1)
  D := [[0, 4, 0], [0, 4, 0], [0, 4, 0], [0, 4, 0], [0, 4, 0], [0, 4, 4], [0, 4, 4], [0, 4, 4], [0, 4, 4], [0, 4, 4], [0, 4, 3], [0, 4, 3], [0, 4, 3], [0, 4, 3], [0, 4, 3], [0, 4, 2], [0, 4, 2], [0, 4, 2], [0, 4, 2], [0, 4, 2], [0, 4, 1], [0, 4, 1], [0, 4, 1], [0, 4, 1], [0, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_79_12_0 : ColCert where
  rK := ⟨79, by decide⟩
  rH := ⟨12, by decide⟩
  m := 25
  T1 := T79_12
  T2 := Q2.T79_12_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_79_12_1 : ColCert where
  rK := ⟨79, by decide⟩
  rH := ⟨12, by decide⟩
  m := 25
  T1 := T79_12
  T2 := Q2.T79_12_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_79_12_2 : ColCert where
  rK := ⟨79, by decide⟩
  rH := ⟨12, by decide⟩
  m := 25
  T1 := T79_12
  T2 := Q2.T79_12_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_79_12_3 : ColCert where
  rK := ⟨79, by decide⟩
  rH := ⟨12, by decide⟩
  m := 25
  T1 := T79_12
  T2 := Q2.T79_12_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_79_12_4 : ColCert where
  rK := ⟨79, by decide⟩
  rH := ⟨12, by decide⟩
  m := 25
  T1 := T79_12
  T2 := Q2.T79_12_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_79_26_0 : ColCert where
  rK := ⟨79, by decide⟩
  rH := ⟨26, by decide⟩
  m := 25
  T1 := T79_26
  T2 := Q2.T79_26_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_79_26_1 : ColCert where
  rK := ⟨79, by decide⟩
  rH := ⟨26, by decide⟩
  m := 25
  T1 := T79_26
  T2 := Q2.T79_26_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_79_26_2 : ColCert where
  rK := ⟨79, by decide⟩
  rH := ⟨26, by decide⟩
  m := 25
  T1 := T79_26
  T2 := Q2.T79_26_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_79_26_3 : ColCert where
  rK := ⟨79, by decide⟩
  rH := ⟨26, by decide⟩
  m := 25
  T1 := T79_26
  T2 := Q2.T79_26_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_79_26_4 : ColCert where
  rK := ⟨79, by decide⟩
  rH := ⟨26, by decide⟩
  m := 25
  T1 := T79_26
  T2 := Q2.T79_26_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_79_26_5 : ColCert where
  rK := ⟨79, by decide⟩
  rH := ⟨26, by decide⟩
  m := 25
  T1 := T79_26
  T2 := Q2.T79_26_2
  h1 := (0,0,1,1,0)
  h2 := (0,0,1,1,0)
  D := [[0, 1, 1], [0, 1, 1], [0, 1, 1], [0, 1, 1], [0, 1, 1], [0, 1, 2], [0, 1, 2], [0, 1, 2], [0, 1, 2], [0, 1, 2], [0, 1, 3], [0, 1, 3], [0, 1, 3], [0, 1, 3], [0, 1, 3], [0, 1, 4], [0, 1, 4], [0, 1, 4], [0, 1, 4], [0, 1, 4], [0, 1, 0], [0, 1, 0], [0, 1, 0], [0, 1, 0], [0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_79_26_10 : ColCert where
  rK := ⟨79, by decide⟩
  rH := ⟨26, by decide⟩
  m := 25
  T1 := T79_26
  T2 := Q2.T79_26_2
  h1 := (0,0,2,2,0)
  h2 := (0,0,2,2,0)
  D := [[0, 2, 2], [0, 2, 2], [0, 2, 2], [0, 2, 2], [0, 2, 2], [0, 2, 4], [0, 2, 4], [0, 2, 4], [0, 2, 4], [0, 2, 4], [0, 2, 1], [0, 2, 1], [0, 2, 1], [0, 2, 1], [0, 2, 1], [0, 2, 3], [0, 2, 3], [0, 2, 3], [0, 2, 3], [0, 2, 3], [0, 2, 0], [0, 2, 0], [0, 2, 0], [0, 2, 0], [0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_79_26_15 : ColCert where
  rK := ⟨79, by decide⟩
  rH := ⟨26, by decide⟩
  m := 25
  T1 := T79_26
  T2 := Q2.T79_26_2
  h1 := (0,0,3,3,0)
  h2 := (0,0,3,3,0)
  D := [[0, 3, 3], [0, 3, 3], [0, 3, 3], [0, 3, 3], [0, 3, 3], [0, 3, 1], [0, 3, 1], [0, 3, 1], [0, 3, 1], [0, 3, 1], [0, 3, 4], [0, 3, 4], [0, 3, 4], [0, 3, 4], [0, 3, 4], [0, 3, 2], [0, 3, 2], [0, 3, 2], [0, 3, 2], [0, 3, 2], [0, 3, 0], [0, 3, 0], [0, 3, 0], [0, 3, 0], [0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_79_26_20 : ColCert where
  rK := ⟨79, by decide⟩
  rH := ⟨26, by decide⟩
  m := 25
  T1 := T79_26
  T2 := Q2.T79_26_2
  h1 := (0,0,4,4,0)
  h2 := (0,0,4,4,0)
  D := [[0, 4, 4], [0, 4, 4], [0, 4, 4], [0, 4, 4], [0, 4, 4], [0, 4, 3], [0, 4, 3], [0, 4, 3], [0, 4, 3], [0, 4, 3], [0, 4, 2], [0, 4, 2], [0, 4, 2], [0, 4, 2], [0, 4, 2], [0, 4, 1], [0, 4, 1], [0, 4, 1], [0, 4, 1], [0, 4, 1], [0, 4, 0], [0, 4, 0], [0, 4, 0], [0, 4, 0], [0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_79_32_0 : ColCert where
  rK := ⟨79, by decide⟩
  rH := ⟨32, by decide⟩
  m := 5
  T1 := T79_32
  T2 := Q2.T79_32_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_79_32_1 : ColCert where
  rK := ⟨79, by decide⟩
  rH := ⟨32, by decide⟩
  m := 5
  T1 := T79_32
  T2 := Q2.T79_32_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_79_32_2 : ColCert where
  rK := ⟨79, by decide⟩
  rH := ⟨32, by decide⟩
  m := 5
  T1 := T79_32
  T2 := Q2.T79_32_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_79_32_3 : ColCert where
  rK := ⟨79, by decide⟩
  rH := ⟨32, by decide⟩
  m := 5
  T1 := T79_32
  T2 := Q2.T79_32_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_79_32_4 : ColCert where
  rK := ⟨79, by decide⟩
  rH := ⟨32, by decide⟩
  m := 5
  T1 := T79_32
  T2 := Q2.T79_32_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_79_37_0 : ColCert where
  rK := ⟨79, by decide⟩
  rH := ⟨37, by decide⟩
  m := 5
  T1 := T79_37
  T2 := Q2.T79_37_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_79_37_1 : ColCert where
  rK := ⟨79, by decide⟩
  rH := ⟨37, by decide⟩
  m := 5
  T1 := T79_37
  T2 := Q2.T79_37_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_79_37_2 : ColCert where
  rK := ⟨79, by decide⟩
  rH := ⟨37, by decide⟩
  m := 5
  T1 := T79_37
  T2 := Q2.T79_37_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_79_37_3 : ColCert where
  rK := ⟨79, by decide⟩
  rH := ⟨37, by decide⟩
  m := 5
  T1 := T79_37
  T2 := Q2.T79_37_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_79_37_4 : ColCert where
  rK := ⟨79, by decide⟩
  rH := ⟨37, by decide⟩
  m := 5
  T1 := T79_37
  T2 := Q2.T79_37_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_79_42_0 : ColCert where
  rK := ⟨79, by decide⟩
  rH := ⟨42, by decide⟩
  m := 5
  T1 := T79_42
  T2 := Q2.T79_42_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_79_42_1 : ColCert where
  rK := ⟨79, by decide⟩
  rH := ⟨42, by decide⟩
  m := 5
  T1 := T79_42
  T2 := Q2.T79_42_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_79_42_2 : ColCert where
  rK := ⟨79, by decide⟩
  rH := ⟨42, by decide⟩
  m := 5
  T1 := T79_42
  T2 := Q2.T79_42_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_79_42_3 : ColCert where
  rK := ⟨79, by decide⟩
  rH := ⟨42, by decide⟩
  m := 5
  T1 := T79_42
  T2 := Q2.T79_42_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_79_42_4 : ColCert where
  rK := ⟨79, by decide⟩
  rH := ⟨42, by decide⟩
  m := 5
  T1 := T79_42
  T2 := Q2.T79_42_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_79_47_0 : ColCert where
  rK := ⟨79, by decide⟩
  rH := ⟨47, by decide⟩
  m := 5
  T1 := T79_47
  T2 := Q2.T79_47_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_79_47_1 : ColCert where
  rK := ⟨79, by decide⟩
  rH := ⟨47, by decide⟩
  m := 5
  T1 := T79_47
  T2 := Q2.T79_47_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_79_47_2 : ColCert where
  rK := ⟨79, by decide⟩
  rH := ⟨47, by decide⟩
  m := 5
  T1 := T79_47
  T2 := Q2.T79_47_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_79_47_3 : ColCert where
  rK := ⟨79, by decide⟩
  rH := ⟨47, by decide⟩
  m := 5
  T1 := T79_47
  T2 := Q2.T79_47_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_79_47_4 : ColCert where
  rK := ⟨79, by decide⟩
  rH := ⟨47, by decide⟩
  m := 5
  T1 := T79_47
  T2 := Q2.T79_47_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_79_52_0 : ColCert where
  rK := ⟨79, by decide⟩
  rH := ⟨52, by decide⟩
  m := 5
  T1 := T79_52
  T2 := Q2.T79_52_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_79_52_1 : ColCert where
  rK := ⟨79, by decide⟩
  rH := ⟨52, by decide⟩
  m := 5
  T1 := T79_52
  T2 := Q2.T79_52_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_79_52_2 : ColCert where
  rK := ⟨79, by decide⟩
  rH := ⟨52, by decide⟩
  m := 5
  T1 := T79_52
  T2 := Q2.T79_52_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_79_52_3 : ColCert where
  rK := ⟨79, by decide⟩
  rH := ⟨52, by decide⟩
  m := 5
  T1 := T79_52
  T2 := Q2.T79_52_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_79_52_4 : ColCert where
  rK := ⟨79, by decide⟩
  rH := ⟨52, by decide⟩
  m := 5
  T1 := T79_52
  T2 := Q2.T79_52_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_79_79_0 : ColCert where
  rK := ⟨79, by decide⟩
  rH := ⟨79, by decide⟩
  m := 5
  T1 := T79_79
  T2 := Q2.T79_79_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_79_79_1 : ColCert where
  rK := ⟨79, by decide⟩
  rH := ⟨79, by decide⟩
  m := 5
  T1 := T79_79
  T2 := Q2.T79_79_2
  h1 := (0,0,1,1,0)
  h2 := (0,0,1,1,0)
  D := [[0, 1, 0], [0, 1, 0], [0, 1, 0], [0, 1, 0], [0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_79_79_2 : ColCert where
  rK := ⟨79, by decide⟩
  rH := ⟨79, by decide⟩
  m := 5
  T1 := T79_79
  T2 := Q2.T79_79_2
  h1 := (0,0,2,2,0)
  h2 := (0,0,2,2,0)
  D := [[0, 2, 0], [0, 2, 0], [0, 2, 0], [0, 2, 0], [0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_79_79_3 : ColCert where
  rK := ⟨79, by decide⟩
  rH := ⟨79, by decide⟩
  m := 5
  T1 := T79_79
  T2 := Q2.T79_79_2
  h1 := (0,0,3,3,0)
  h2 := (0,0,3,3,0)
  D := [[0, 3, 0], [0, 3, 0], [0, 3, 0], [0, 3, 0], [0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_79_79_4 : ColCert where
  rK := ⟨79, by decide⟩
  rH := ⟨79, by decide⟩
  m := 5
  T1 := T79_79
  T2 := Q2.T79_79_2
  h1 := (0,0,4,4,0)
  h2 := (0,0,4,4,0)
  D := [[0, 4, 0], [0, 4, 0], [0, 4, 0], [0, 4, 0], [0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_79_79_5 : ColCert where
  rK := ⟨79, by decide⟩
  rH := ⟨79, by decide⟩
  m := 5
  T1 := T79_79
  T2 := Q2.T79_79_2
  h1 := (1,1,0,4,0)
  h2 := (1,1,0,4,0)
  D := [[1, 0, 1], [1, 0, 0], [1, 0, 4], [1, 0, 3], [1, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_79_79_6 : ColCert where
  rK := ⟨79, by decide⟩
  rH := ⟨79, by decide⟩
  m := 5
  T1 := T79_79
  T2 := Q2.T79_79_2
  h1 := (1,1,1,0,0)
  h2 := (1,1,1,0,0)
  D := [[1, 1, 4], [1, 1, 3], [1, 1, 2], [1, 1, 1], [1, 1, 0]]
  bind1 := by decide
  bind2 := by decide

end LeanDring.P5Presentation
