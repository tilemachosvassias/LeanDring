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
rest tier, chunk 108: 60 columns.
-/

-- machine-emitted data: silence style linters (generated long lines, file-level options)
set_option linter.style.longLine false

namespace LeanDring.P5Presentation

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

def colCert_147_6_2 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨6, by decide⟩
  m := 1
  T1 := T147_6
  T2 := Q2.T147_6_2
  h1 := (0,0,2,4,3)
  h2 := (0,0,2,4,3)
  D := [[0, 0, 2, 4, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_6_3 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨6, by decide⟩
  m := 1
  T1 := T147_6
  T2 := Q2.T147_6_2
  h1 := (0,0,3,1,2)
  h2 := (0,0,3,1,2)
  D := [[0, 0, 3, 1, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_6_4 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨6, by decide⟩
  m := 1
  T1 := T147_6
  T2 := Q2.T147_6_2
  h1 := (0,0,4,3,1)
  h2 := (0,0,4,3,1)
  D := [[0, 0, 4, 3, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_7_0 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨7, by decide⟩
  m := 1
  T1 := T147_7
  T2 := Q2.T147_7_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_7_1 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨7, by decide⟩
  m := 1
  T1 := T147_7
  T2 := Q2.T147_7_2
  h1 := (0,0,1,3,4)
  h2 := (0,0,1,3,4)
  D := [[0, 0, 1, 3, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_7_2 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨7, by decide⟩
  m := 1
  T1 := T147_7
  T2 := Q2.T147_7_2
  h1 := (0,0,2,1,3)
  h2 := (0,0,2,1,3)
  D := [[0, 0, 2, 1, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_7_3 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨7, by decide⟩
  m := 1
  T1 := T147_7
  T2 := Q2.T147_7_2
  h1 := (0,0,3,4,2)
  h2 := (0,0,3,4,2)
  D := [[0, 0, 3, 4, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_7_4 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨7, by decide⟩
  m := 1
  T1 := T147_7
  T2 := Q2.T147_7_2
  h1 := (0,0,4,2,1)
  h2 := (0,0,4,2,1)
  D := [[0, 0, 4, 2, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_8_0 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨8, by decide⟩
  m := 1
  T1 := T147_8
  T2 := Q2.T147_8_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_8_1 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨8, by decide⟩
  m := 1
  T1 := T147_8
  T2 := Q2.T147_8_2
  h1 := (0,0,1,1,4)
  h2 := (0,0,1,1,4)
  D := [[0, 0, 1, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_8_2 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨8, by decide⟩
  m := 1
  T1 := T147_8
  T2 := Q2.T147_8_2
  h1 := (0,0,2,2,3)
  h2 := (0,0,2,2,3)
  D := [[0, 0, 2, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_8_3 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨8, by decide⟩
  m := 1
  T1 := T147_8
  T2 := Q2.T147_8_2
  h1 := (0,0,3,3,2)
  h2 := (0,0,3,3,2)
  D := [[0, 0, 3, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_8_4 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨8, by decide⟩
  m := 1
  T1 := T147_8
  T2 := Q2.T147_8_2
  h1 := (0,0,4,4,1)
  h2 := (0,0,4,4,1)
  D := [[0, 0, 4, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_9_0 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨9, by decide⟩
  m := 1
  T1 := T147_9
  T2 := Q2.T147_9_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_9_1 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨9, by decide⟩
  m := 1
  T1 := T147_9
  T2 := Q2.T147_9_2
  h1 := (0,0,1,0,4)
  h2 := (0,0,1,0,4)
  D := [[0, 0, 1, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_9_2 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨9, by decide⟩
  m := 1
  T1 := T147_9
  T2 := Q2.T147_9_2
  h1 := (0,0,2,0,3)
  h2 := (0,0,2,0,3)
  D := [[0, 0, 2, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_9_3 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨9, by decide⟩
  m := 1
  T1 := T147_9
  T2 := Q2.T147_9_2
  h1 := (0,0,3,0,2)
  h2 := (0,0,3,0,2)
  D := [[0, 0, 3, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_9_4 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨9, by decide⟩
  m := 1
  T1 := T147_9
  T2 := Q2.T147_9_2
  h1 := (0,0,4,0,1)
  h2 := (0,0,4,0,1)
  D := [[0, 0, 4, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_10_0 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨10, by decide⟩
  m := 1
  T1 := T147_10
  T2 := Q2.T147_10_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_10_1 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨10, by decide⟩
  m := 1
  T1 := T147_10
  T2 := Q2.T147_10_2
  h1 := (0,0,0,1,4)
  h2 := (0,0,0,1,4)
  D := [[0, 0, 0, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_10_2 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨10, by decide⟩
  m := 1
  T1 := T147_10
  T2 := Q2.T147_10_2
  h1 := (0,0,0,2,3)
  h2 := (0,0,0,2,3)
  D := [[0, 0, 0, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_10_3 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨10, by decide⟩
  m := 1
  T1 := T147_10
  T2 := Q2.T147_10_2
  h1 := (0,0,0,3,2)
  h2 := (0,0,0,3,2)
  D := [[0, 0, 0, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_10_4 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨10, by decide⟩
  m := 1
  T1 := T147_10
  T2 := Q2.T147_10_2
  h1 := (0,0,0,4,1)
  h2 := (0,0,0,4,1)
  D := [[0, 0, 0, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_11_0 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨11, by decide⟩
  m := 1
  T1 := T147_11
  T2 := Q2.T147_11_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_11_1 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨11, by decide⟩
  m := 1
  T1 := T147_11
  T2 := Q2.T147_11_2
  h1 := (1,0,0,4,3)
  h2 := (1,0,0,4,3)
  D := [[1, 0, 0, 4, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_11_2 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨11, by decide⟩
  m := 1
  T1 := T147_11
  T2 := Q2.T147_11_2
  h1 := (2,0,0,3,0)
  h2 := (2,0,0,3,0)
  D := [[2, 0, 0, 3, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_11_3 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨11, by decide⟩
  m := 1
  T1 := T147_11
  T2 := Q2.T147_11_2
  h1 := (3,0,0,2,1)
  h2 := (3,0,0,2,1)
  D := [[3, 0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_11_4 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨11, by decide⟩
  m := 1
  T1 := T147_11
  T2 := Q2.T147_11_2
  h1 := (4,0,0,1,1)
  h2 := (4,0,0,1,1)
  D := [[4, 0, 0, 1, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_12_0 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨12, by decide⟩
  m := 1
  T1 := T147_12
  T2 := Q2.T147_12_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_12_1 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨12, by decide⟩
  m := 1
  T1 := T147_12
  T2 := Q2.T147_12_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_12_2 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨12, by decide⟩
  m := 1
  T1 := T147_12
  T2 := Q2.T147_12_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_12_3 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨12, by decide⟩
  m := 1
  T1 := T147_12
  T2 := Q2.T147_12_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_12_4 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨12, by decide⟩
  m := 1
  T1 := T147_12
  T2 := Q2.T147_12_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_13_0 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨13, by decide⟩
  m := 1
  T1 := T147_13
  T2 := Q2.T147_13_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_13_1 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨13, by decide⟩
  m := 1
  T1 := T147_13
  T2 := Q2.T147_13_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_13_2 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨13, by decide⟩
  m := 1
  T1 := T147_13
  T2 := Q2.T147_13_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_13_3 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨13, by decide⟩
  m := 1
  T1 := T147_13
  T2 := Q2.T147_13_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_13_4 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨13, by decide⟩
  m := 1
  T1 := T147_13
  T2 := Q2.T147_13_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_13_9 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨13, by decide⟩
  m := 1
  T1 := T147_13
  T2 := Q2.T147_13_2
  h1 := (0,0,1,4,4)
  h2 := (0,0,1,4,4)
  D := [[0, 0, 1, 4, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_13_10 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨13, by decide⟩
  m := 1
  T1 := T147_13
  T2 := Q2.T147_13_2
  h1 := (0,0,2,0,3)
  h2 := (0,0,2,0,3)
  D := [[0, 0, 2, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_13_11 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨13, by decide⟩
  m := 1
  T1 := T147_13
  T2 := Q2.T147_13_2
  h1 := (0,0,2,1,3)
  h2 := (0,0,2,1,3)
  D := [[0, 0, 2, 1, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_13_12 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨13, by decide⟩
  m := 1
  T1 := T147_13
  T2 := Q2.T147_13_2
  h1 := (0,0,2,2,3)
  h2 := (0,0,2,2,3)
  D := [[0, 0, 2, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_13_13 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨13, by decide⟩
  m := 1
  T1 := T147_13
  T2 := Q2.T147_13_2
  h1 := (0,0,2,3,3)
  h2 := (0,0,2,3,3)
  D := [[0, 0, 2, 3, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_13_14 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨13, by decide⟩
  m := 1
  T1 := T147_13
  T2 := Q2.T147_13_2
  h1 := (0,0,2,4,3)
  h2 := (0,0,2,4,3)
  D := [[0, 0, 2, 4, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_13_15 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨13, by decide⟩
  m := 1
  T1 := T147_13
  T2 := Q2.T147_13_2
  h1 := (0,0,3,0,2)
  h2 := (0,0,3,0,2)
  D := [[0, 0, 3, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_13_16 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨13, by decide⟩
  m := 1
  T1 := T147_13
  T2 := Q2.T147_13_2
  h1 := (0,0,3,1,2)
  h2 := (0,0,3,1,2)
  D := [[0, 0, 3, 1, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_13_17 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨13, by decide⟩
  m := 1
  T1 := T147_13
  T2 := Q2.T147_13_2
  h1 := (0,0,3,2,2)
  h2 := (0,0,3,2,2)
  D := [[0, 0, 3, 2, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_13_18 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨13, by decide⟩
  m := 1
  T1 := T147_13
  T2 := Q2.T147_13_2
  h1 := (0,0,3,3,2)
  h2 := (0,0,3,3,2)
  D := [[0, 0, 3, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_13_19 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨13, by decide⟩
  m := 1
  T1 := T147_13
  T2 := Q2.T147_13_2
  h1 := (0,0,3,4,2)
  h2 := (0,0,3,4,2)
  D := [[0, 0, 3, 4, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_13_20 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨13, by decide⟩
  m := 1
  T1 := T147_13
  T2 := Q2.T147_13_2
  h1 := (0,0,4,0,1)
  h2 := (0,0,4,0,1)
  D := [[0, 0, 4, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_13_21 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨13, by decide⟩
  m := 1
  T1 := T147_13
  T2 := Q2.T147_13_2
  h1 := (0,0,4,1,1)
  h2 := (0,0,4,1,1)
  D := [[0, 0, 4, 1, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_13_22 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨13, by decide⟩
  m := 1
  T1 := T147_13
  T2 := Q2.T147_13_2
  h1 := (0,0,4,2,1)
  h2 := (0,0,4,2,1)
  D := [[0, 0, 4, 2, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_13_23 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨13, by decide⟩
  m := 1
  T1 := T147_13
  T2 := Q2.T147_13_2
  h1 := (0,0,4,3,1)
  h2 := (0,0,4,3,1)
  D := [[0, 0, 4, 3, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_13_24 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨13, by decide⟩
  m := 1
  T1 := T147_13
  T2 := Q2.T147_13_2
  h1 := (0,0,4,4,1)
  h2 := (0,0,4,4,1)
  D := [[0, 0, 4, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_14_0 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨14, by decide⟩
  m := 1
  T1 := T147_14
  T2 := Q2.T147_14_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_14_1 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨14, by decide⟩
  m := 1
  T1 := T147_14
  T2 := Q2.T147_14_2
  h1 := (0,0,1,0,0)
  h2 := (0,0,1,0,0)
  D := [[0, 0, 1, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_14_2 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨14, by decide⟩
  m := 1
  T1 := T147_14
  T2 := Q2.T147_14_2
  h1 := (0,0,2,0,0)
  h2 := (0,0,2,0,0)
  D := [[0, 0, 2, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_14_3 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨14, by decide⟩
  m := 1
  T1 := T147_14
  T2 := Q2.T147_14_2
  h1 := (0,0,3,0,0)
  h2 := (0,0,3,0,0)
  D := [[0, 0, 3, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_14_4 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨14, by decide⟩
  m := 1
  T1 := T147_14
  T2 := Q2.T147_14_2
  h1 := (0,0,4,0,0)
  h2 := (0,0,4,0,0)
  D := [[0, 0, 4, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_14_5 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨14, by decide⟩
  m := 1
  T1 := T147_14
  T2 := Q2.T147_14_2
  h1 := (1,0,0,4,3)
  h2 := (1,0,0,4,3)
  D := [[1, 0, 0, 4, 4]]
  bind1 := by decide
  bind2 := by decide

end LeanDring.P5Presentation
