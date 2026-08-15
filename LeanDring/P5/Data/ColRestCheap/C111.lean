/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.Twin1.ColCert
import LeanDring.P5.Data.EntryK.C044

/-!
# Species-table cell data, stage 2 — twin-coincident columns (cheap tier)

Per-column certified exponent-vector data (`ColCert`/`ColCertDiv`) with kernel
`decide` bindings. Emitted; the embedded lists are what the kernel certifies.
rest tier, chunk 110: 60 columns.
-/

-- machine-emitted data: silence style linters (generated long lines, file-level options)
set_option linter.style.longLine false

namespace LeanDring.P5Presentation

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

def colCert_147_16_16 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨16, by decide⟩
  m := 1
  T1 := T147_16
  T2 := Q2.T147_16_2
  h1 := (3,0,1,2,4)
  h2 := (3,0,1,2,4)
  D := [[3, 0, 1, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_16_17 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨16, by decide⟩
  m := 1
  T1 := T147_16
  T2 := Q2.T147_16_2
  h1 := (3,0,2,2,2)
  h2 := (3,0,2,2,2)
  D := [[3, 0, 2, 2, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_16_18 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨16, by decide⟩
  m := 1
  T1 := T147_16
  T2 := Q2.T147_16_2
  h1 := (3,0,3,2,0)
  h2 := (3,0,3,2,0)
  D := [[3, 0, 3, 2, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_16_19 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨16, by decide⟩
  m := 1
  T1 := T147_16
  T2 := Q2.T147_16_2
  h1 := (3,0,4,2,3)
  h2 := (3,0,4,2,3)
  D := [[3, 0, 4, 2, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_16_20 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨16, by decide⟩
  m := 1
  T1 := T147_16
  T2 := Q2.T147_16_2
  h1 := (4,0,0,1,1)
  h2 := (4,0,0,1,1)
  D := [[4, 0, 0, 1, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_16_21 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨16, by decide⟩
  m := 1
  T1 := T147_16
  T2 := Q2.T147_16_2
  h1 := (4,0,1,1,4)
  h2 := (4,0,1,1,4)
  D := [[4, 0, 1, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_16_22 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨16, by decide⟩
  m := 1
  T1 := T147_16
  T2 := Q2.T147_16_2
  h1 := (4,0,2,1,2)
  h2 := (4,0,2,1,2)
  D := [[4, 0, 2, 1, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_16_23 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨16, by decide⟩
  m := 1
  T1 := T147_16
  T2 := Q2.T147_16_2
  h1 := (4,0,3,1,0)
  h2 := (4,0,3,1,0)
  D := [[4, 0, 3, 1, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_16_24 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨16, by decide⟩
  m := 1
  T1 := T147_16
  T2 := Q2.T147_16_2
  h1 := (4,0,4,1,3)
  h2 := (4,0,4,1,3)
  D := [[4, 0, 4, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_17_0 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨17, by decide⟩
  m := 1
  T1 := T147_17
  T2 := Q2.T147_17_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_17_1 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨17, by decide⟩
  m := 1
  T1 := T147_17
  T2 := Q2.T147_17_2
  h1 := (0,0,1,0,2)
  h2 := (0,0,1,0,2)
  D := [[0, 0, 1, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_17_2 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨17, by decide⟩
  m := 1
  T1 := T147_17
  T2 := Q2.T147_17_2
  h1 := (0,0,2,0,4)
  h2 := (0,0,2,0,4)
  D := [[0, 0, 2, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_17_3 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨17, by decide⟩
  m := 1
  T1 := T147_17
  T2 := Q2.T147_17_2
  h1 := (0,0,3,0,1)
  h2 := (0,0,3,0,1)
  D := [[0, 0, 3, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_17_4 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨17, by decide⟩
  m := 1
  T1 := T147_17
  T2 := Q2.T147_17_2
  h1 := (0,0,4,0,3)
  h2 := (0,0,4,0,3)
  D := [[0, 0, 4, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_17_5 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨17, by decide⟩
  m := 1
  T1 := T147_17
  T2 := Q2.T147_17_2
  h1 := (1,0,0,4,3)
  h2 := (1,0,0,4,3)
  D := [[1, 0, 0, 4, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_17_6 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨17, by decide⟩
  m := 1
  T1 := T147_17
  T2 := Q2.T147_17_2
  h1 := (1,0,1,4,0)
  h2 := (1,0,1,4,0)
  D := [[1, 0, 1, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_17_7 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨17, by decide⟩
  m := 1
  T1 := T147_17
  T2 := Q2.T147_17_2
  h1 := (1,0,2,4,2)
  h2 := (1,0,2,4,2)
  D := [[1, 0, 2, 4, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_17_8 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨17, by decide⟩
  m := 1
  T1 := T147_17
  T2 := Q2.T147_17_2
  h1 := (1,0,3,4,4)
  h2 := (1,0,3,4,4)
  D := [[1, 0, 3, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_17_9 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨17, by decide⟩
  m := 1
  T1 := T147_17
  T2 := Q2.T147_17_2
  h1 := (1,0,4,4,1)
  h2 := (1,0,4,4,1)
  D := [[1, 0, 4, 4, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_17_10 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨17, by decide⟩
  m := 1
  T1 := T147_17
  T2 := Q2.T147_17_2
  h1 := (2,0,0,3,0)
  h2 := (2,0,0,3,0)
  D := [[2, 0, 0, 3, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_17_11 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨17, by decide⟩
  m := 1
  T1 := T147_17
  T2 := Q2.T147_17_2
  h1 := (2,0,1,3,2)
  h2 := (2,0,1,3,2)
  D := [[2, 0, 1, 3, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_17_12 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨17, by decide⟩
  m := 1
  T1 := T147_17
  T2 := Q2.T147_17_2
  h1 := (2,0,2,3,4)
  h2 := (2,0,2,3,4)
  D := [[2, 0, 2, 3, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_17_13 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨17, by decide⟩
  m := 1
  T1 := T147_17
  T2 := Q2.T147_17_2
  h1 := (2,0,3,3,1)
  h2 := (2,0,3,3,1)
  D := [[2, 0, 3, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_17_14 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨17, by decide⟩
  m := 1
  T1 := T147_17
  T2 := Q2.T147_17_2
  h1 := (2,0,4,3,3)
  h2 := (2,0,4,3,3)
  D := [[2, 0, 4, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_17_15 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨17, by decide⟩
  m := 1
  T1 := T147_17
  T2 := Q2.T147_17_2
  h1 := (3,0,0,2,1)
  h2 := (3,0,0,2,1)
  D := [[3, 0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_17_16 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨17, by decide⟩
  m := 1
  T1 := T147_17
  T2 := Q2.T147_17_2
  h1 := (3,0,1,2,3)
  h2 := (3,0,1,2,3)
  D := [[3, 0, 1, 2, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_17_17 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨17, by decide⟩
  m := 1
  T1 := T147_17
  T2 := Q2.T147_17_2
  h1 := (3,0,2,2,0)
  h2 := (3,0,2,2,0)
  D := [[3, 0, 2, 2, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_17_18 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨17, by decide⟩
  m := 1
  T1 := T147_17
  T2 := Q2.T147_17_2
  h1 := (3,0,3,2,2)
  h2 := (3,0,3,2,2)
  D := [[3, 0, 3, 2, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_17_19 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨17, by decide⟩
  m := 1
  T1 := T147_17
  T2 := Q2.T147_17_2
  h1 := (3,0,4,2,4)
  h2 := (3,0,4,2,4)
  D := [[3, 0, 4, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_17_20 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨17, by decide⟩
  m := 1
  T1 := T147_17
  T2 := Q2.T147_17_2
  h1 := (4,0,0,1,1)
  h2 := (4,0,0,1,1)
  D := [[4, 0, 0, 1, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_17_21 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨17, by decide⟩
  m := 1
  T1 := T147_17
  T2 := Q2.T147_17_2
  h1 := (4,0,1,1,3)
  h2 := (4,0,1,1,3)
  D := [[4, 0, 1, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_17_22 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨17, by decide⟩
  m := 1
  T1 := T147_17
  T2 := Q2.T147_17_2
  h1 := (4,0,2,1,0)
  h2 := (4,0,2,1,0)
  D := [[4, 0, 2, 1, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_17_23 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨17, by decide⟩
  m := 1
  T1 := T147_17
  T2 := Q2.T147_17_2
  h1 := (4,0,3,1,2)
  h2 := (4,0,3,1,2)
  D := [[4, 0, 3, 1, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_17_24 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨17, by decide⟩
  m := 1
  T1 := T147_17
  T2 := Q2.T147_17_2
  h1 := (4,0,4,1,4)
  h2 := (4,0,4,1,4)
  D := [[4, 0, 4, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_18_0 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨18, by decide⟩
  m := 1
  T1 := T147_18
  T2 := Q2.T147_18_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_18_1 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨18, by decide⟩
  m := 1
  T1 := T147_18
  T2 := Q2.T147_18_2
  h1 := (0,0,1,0,1)
  h2 := (0,0,1,0,1)
  D := [[0, 0, 1, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_18_2 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨18, by decide⟩
  m := 1
  T1 := T147_18
  T2 := Q2.T147_18_2
  h1 := (0,0,2,0,2)
  h2 := (0,0,2,0,2)
  D := [[0, 0, 2, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_18_3 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨18, by decide⟩
  m := 1
  T1 := T147_18
  T2 := Q2.T147_18_2
  h1 := (0,0,3,0,3)
  h2 := (0,0,3,0,3)
  D := [[0, 0, 3, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_18_4 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨18, by decide⟩
  m := 1
  T1 := T147_18
  T2 := Q2.T147_18_2
  h1 := (0,0,4,0,4)
  h2 := (0,0,4,0,4)
  D := [[0, 0, 4, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_18_5 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨18, by decide⟩
  m := 1
  T1 := T147_18
  T2 := Q2.T147_18_2
  h1 := (1,0,0,4,3)
  h2 := (1,0,0,4,3)
  D := [[1, 0, 0, 4, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_18_6 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨18, by decide⟩
  m := 1
  T1 := T147_18
  T2 := Q2.T147_18_2
  h1 := (1,0,1,4,4)
  h2 := (1,0,1,4,4)
  D := [[1, 0, 1, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_18_7 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨18, by decide⟩
  m := 1
  T1 := T147_18
  T2 := Q2.T147_18_2
  h1 := (1,0,2,4,0)
  h2 := (1,0,2,4,0)
  D := [[1, 0, 2, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_18_8 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨18, by decide⟩
  m := 1
  T1 := T147_18
  T2 := Q2.T147_18_2
  h1 := (1,0,3,4,1)
  h2 := (1,0,3,4,1)
  D := [[1, 0, 3, 4, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_18_9 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨18, by decide⟩
  m := 1
  T1 := T147_18
  T2 := Q2.T147_18_2
  h1 := (1,0,4,4,2)
  h2 := (1,0,4,4,2)
  D := [[1, 0, 4, 4, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_18_10 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨18, by decide⟩
  m := 1
  T1 := T147_18
  T2 := Q2.T147_18_2
  h1 := (2,0,0,3,0)
  h2 := (2,0,0,3,0)
  D := [[2, 0, 0, 3, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_18_11 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨18, by decide⟩
  m := 1
  T1 := T147_18
  T2 := Q2.T147_18_2
  h1 := (2,0,1,3,1)
  h2 := (2,0,1,3,1)
  D := [[2, 0, 1, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_18_12 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨18, by decide⟩
  m := 1
  T1 := T147_18
  T2 := Q2.T147_18_2
  h1 := (2,0,2,3,2)
  h2 := (2,0,2,3,2)
  D := [[2, 0, 2, 3, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_18_13 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨18, by decide⟩
  m := 1
  T1 := T147_18
  T2 := Q2.T147_18_2
  h1 := (2,0,3,3,3)
  h2 := (2,0,3,3,3)
  D := [[2, 0, 3, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_18_14 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨18, by decide⟩
  m := 1
  T1 := T147_18
  T2 := Q2.T147_18_2
  h1 := (2,0,4,3,4)
  h2 := (2,0,4,3,4)
  D := [[2, 0, 4, 3, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_18_15 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨18, by decide⟩
  m := 1
  T1 := T147_18
  T2 := Q2.T147_18_2
  h1 := (3,0,0,2,1)
  h2 := (3,0,0,2,1)
  D := [[3, 0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_18_16 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨18, by decide⟩
  m := 1
  T1 := T147_18
  T2 := Q2.T147_18_2
  h1 := (3,0,1,2,2)
  h2 := (3,0,1,2,2)
  D := [[3, 0, 1, 2, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_18_17 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨18, by decide⟩
  m := 1
  T1 := T147_18
  T2 := Q2.T147_18_2
  h1 := (3,0,2,2,3)
  h2 := (3,0,2,2,3)
  D := [[3, 0, 2, 2, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_18_18 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨18, by decide⟩
  m := 1
  T1 := T147_18
  T2 := Q2.T147_18_2
  h1 := (3,0,3,2,4)
  h2 := (3,0,3,2,4)
  D := [[3, 0, 3, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_18_19 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨18, by decide⟩
  m := 1
  T1 := T147_18
  T2 := Q2.T147_18_2
  h1 := (3,0,4,2,0)
  h2 := (3,0,4,2,0)
  D := [[3, 0, 4, 2, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_18_20 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨18, by decide⟩
  m := 1
  T1 := T147_18
  T2 := Q2.T147_18_2
  h1 := (4,0,0,1,1)
  h2 := (4,0,0,1,1)
  D := [[4, 0, 0, 1, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_18_21 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨18, by decide⟩
  m := 1
  T1 := T147_18
  T2 := Q2.T147_18_2
  h1 := (4,0,1,1,2)
  h2 := (4,0,1,1,2)
  D := [[4, 0, 1, 1, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_18_22 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨18, by decide⟩
  m := 1
  T1 := T147_18
  T2 := Q2.T147_18_2
  h1 := (4,0,2,1,3)
  h2 := (4,0,2,1,3)
  D := [[4, 0, 2, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_18_23 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨18, by decide⟩
  m := 1
  T1 := T147_18
  T2 := Q2.T147_18_2
  h1 := (4,0,3,1,4)
  h2 := (4,0,3,1,4)
  D := [[4, 0, 3, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_18_24 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨18, by decide⟩
  m := 1
  T1 := T147_18
  T2 := Q2.T147_18_2
  h1 := (4,0,4,1,0)
  h2 := (4,0,4,1,0)
  D := [[4, 0, 4, 1, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_19_0 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨19, by decide⟩
  m := 1
  T1 := T147_19
  T2 := Q2.T147_19_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

end LeanDring.P5Presentation
