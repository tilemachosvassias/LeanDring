/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.Twin1.ColCert
import LeanDring.P5.Data.EntryK.C028

/-!
# Species-table cell data, stage 2 — twin-coincident columns (cheap tier)

Per-column certified exponent-vector data (`ColCert`/`ColCertDiv`) with kernel
`decide` bindings. Emitted; the embedded lists are what the kernel certifies.
rest tier, chunk 35: 60 columns.
-/

-- machine-emitted data: silence style linters (generated long lines, file-level options)
set_option linter.style.longLine false

namespace LeanDring.P5Presentation

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

def colCert_119_6_4 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨6, by decide⟩
  m := 5
  T1 := T119_6
  T2 := Q2.T119_6_2
  h1 := (0,0,4,3,1)
  h2 := (0,0,4,3,1)
  D := [[0, 4, 3, 3], [0, 4, 3, 2], [0, 4, 3, 1], [0, 4, 3, 0], [0, 4, 3, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_7_0 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨7, by decide⟩
  m := 5
  T1 := T119_7
  T2 := Q2.T119_7_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_7_1 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨7, by decide⟩
  m := 5
  T1 := T119_7
  T2 := Q2.T119_7_2
  h1 := (0,0,1,3,4)
  h2 := (0,0,1,3,4)
  D := [[0, 1, 3, 2], [0, 1, 3, 3], [0, 1, 3, 4], [0, 1, 3, 0], [0, 1, 3, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_7_2 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨7, by decide⟩
  m := 5
  T1 := T119_7
  T2 := Q2.T119_7_2
  h1 := (0,0,2,1,3)
  h2 := (0,0,2,1,3)
  D := [[0, 2, 1, 4], [0, 2, 1, 1], [0, 2, 1, 3], [0, 2, 1, 0], [0, 2, 1, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_7_3 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨7, by decide⟩
  m := 5
  T1 := T119_7
  T2 := Q2.T119_7_2
  h1 := (0,0,3,4,2)
  h2 := (0,0,3,4,2)
  D := [[0, 3, 4, 1], [0, 3, 4, 4], [0, 3, 4, 2], [0, 3, 4, 0], [0, 3, 4, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_7_4 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨7, by decide⟩
  m := 5
  T1 := T119_7
  T2 := Q2.T119_7_2
  h1 := (0,0,4,2,1)
  h2 := (0,0,4,2,1)
  D := [[0, 4, 2, 3], [0, 4, 2, 2], [0, 4, 2, 1], [0, 4, 2, 0], [0, 4, 2, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_8_0 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨8, by decide⟩
  m := 5
  T1 := T119_8
  T2 := Q2.T119_8_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_8_1 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨8, by decide⟩
  m := 5
  T1 := T119_8
  T2 := Q2.T119_8_2
  h1 := (0,0,1,1,4)
  h2 := (0,0,1,1,4)
  D := [[0, 1, 1, 2], [0, 1, 1, 3], [0, 1, 1, 4], [0, 1, 1, 0], [0, 1, 1, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_8_2 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨8, by decide⟩
  m := 5
  T1 := T119_8
  T2 := Q2.T119_8_2
  h1 := (0,0,2,2,3)
  h2 := (0,0,2,2,3)
  D := [[0, 2, 2, 4], [0, 2, 2, 1], [0, 2, 2, 3], [0, 2, 2, 0], [0, 2, 2, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_8_3 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨8, by decide⟩
  m := 5
  T1 := T119_8
  T2 := Q2.T119_8_2
  h1 := (0,0,3,3,2)
  h2 := (0,0,3,3,2)
  D := [[0, 3, 3, 1], [0, 3, 3, 4], [0, 3, 3, 2], [0, 3, 3, 0], [0, 3, 3, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_8_4 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨8, by decide⟩
  m := 5
  T1 := T119_8
  T2 := Q2.T119_8_2
  h1 := (0,0,4,4,1)
  h2 := (0,0,4,4,1)
  D := [[0, 4, 4, 3], [0, 4, 4, 2], [0, 4, 4, 1], [0, 4, 4, 0], [0, 4, 4, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_9_0 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨9, by decide⟩
  m := 5
  T1 := T119_9
  T2 := Q2.T119_9_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_9_1 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨9, by decide⟩
  m := 5
  T1 := T119_9
  T2 := Q2.T119_9_2
  h1 := (0,0,1,0,4)
  h2 := (0,0,1,0,4)
  D := [[0, 1, 0, 2], [0, 1, 0, 3], [0, 1, 0, 4], [0, 1, 0, 0], [0, 1, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_9_2 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨9, by decide⟩
  m := 5
  T1 := T119_9
  T2 := Q2.T119_9_2
  h1 := (0,0,2,0,3)
  h2 := (0,0,2,0,3)
  D := [[0, 2, 0, 4], [0, 2, 0, 1], [0, 2, 0, 3], [0, 2, 0, 0], [0, 2, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_9_3 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨9, by decide⟩
  m := 5
  T1 := T119_9
  T2 := Q2.T119_9_2
  h1 := (0,0,3,0,2)
  h2 := (0,0,3,0,2)
  D := [[0, 3, 0, 1], [0, 3, 0, 4], [0, 3, 0, 2], [0, 3, 0, 0], [0, 3, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_9_4 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨9, by decide⟩
  m := 5
  T1 := T119_9
  T2 := Q2.T119_9_2
  h1 := (0,0,4,0,1)
  h2 := (0,0,4,0,1)
  D := [[0, 4, 0, 3], [0, 4, 0, 2], [0, 4, 0, 1], [0, 4, 0, 0], [0, 4, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_10_0 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨10, by decide⟩
  m := 5
  T1 := T119_10
  T2 := Q2.T119_10_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_10_1 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨10, by decide⟩
  m := 5
  T1 := T119_10
  T2 := Q2.T119_10_2
  h1 := (0,0,0,1,4)
  h2 := (0,0,0,1,4)
  D := [[0, 0, 1, 4], [0, 0, 1, 4], [0, 0, 1, 4], [0, 0, 1, 4], [0, 0, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_10_2 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨10, by decide⟩
  m := 5
  T1 := T119_10
  T2 := Q2.T119_10_2
  h1 := (0,0,0,2,3)
  h2 := (0,0,0,2,3)
  D := [[0, 0, 2, 3], [0, 0, 2, 3], [0, 0, 2, 3], [0, 0, 2, 3], [0, 0, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_10_3 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨10, by decide⟩
  m := 5
  T1 := T119_10
  T2 := Q2.T119_10_2
  h1 := (0,0,0,3,2)
  h2 := (0,0,0,3,2)
  D := [[0, 0, 3, 2], [0, 0, 3, 2], [0, 0, 3, 2], [0, 0, 3, 2], [0, 0, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_10_4 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨10, by decide⟩
  m := 5
  T1 := T119_10
  T2 := Q2.T119_10_2
  h1 := (0,0,0,4,1)
  h2 := (0,0,0,4,1)
  D := [[0, 0, 4, 1], [0, 0, 4, 1], [0, 0, 4, 1], [0, 0, 4, 1], [0, 0, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_12_0 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨12, by decide⟩
  m := 5
  T1 := T119_12
  T2 := Q2.T119_12_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_12_1 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨12, by decide⟩
  m := 5
  T1 := T119_12
  T2 := Q2.T119_12_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_12_2 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨12, by decide⟩
  m := 5
  T1 := T119_12
  T2 := Q2.T119_12_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_12_3 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨12, by decide⟩
  m := 5
  T1 := T119_12
  T2 := Q2.T119_12_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_12_4 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨12, by decide⟩
  m := 5
  T1 := T119_12
  T2 := Q2.T119_12_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_13_0 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨13, by decide⟩
  m := 5
  T1 := T119_13
  T2 := Q2.T119_13_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_13_1 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨13, by decide⟩
  m := 5
  T1 := T119_13
  T2 := Q2.T119_13_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_13_2 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨13, by decide⟩
  m := 5
  T1 := T119_13
  T2 := Q2.T119_13_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_13_3 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨13, by decide⟩
  m := 5
  T1 := T119_13
  T2 := Q2.T119_13_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_13_4 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨13, by decide⟩
  m := 5
  T1 := T119_13
  T2 := Q2.T119_13_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_13_9 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨13, by decide⟩
  m := 5
  T1 := T119_13
  T2 := Q2.T119_13_2
  h1 := (0,0,1,4,4)
  h2 := (0,0,1,4,4)
  D := [[0, 1, 4, 2], [0, 1, 4, 3], [0, 1, 4, 4], [0, 1, 4, 0], [0, 1, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_13_10 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨13, by decide⟩
  m := 5
  T1 := T119_13
  T2 := Q2.T119_13_2
  h1 := (0,0,2,0,3)
  h2 := (0,0,2,0,3)
  D := [[0, 2, 0, 4], [0, 2, 0, 1], [0, 2, 0, 3], [0, 2, 0, 0], [0, 2, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_13_11 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨13, by decide⟩
  m := 5
  T1 := T119_13
  T2 := Q2.T119_13_2
  h1 := (0,0,2,1,3)
  h2 := (0,0,2,1,3)
  D := [[0, 2, 1, 4], [0, 2, 1, 1], [0, 2, 1, 3], [0, 2, 1, 0], [0, 2, 1, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_13_12 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨13, by decide⟩
  m := 5
  T1 := T119_13
  T2 := Q2.T119_13_2
  h1 := (0,0,2,2,3)
  h2 := (0,0,2,2,3)
  D := [[0, 2, 2, 4], [0, 2, 2, 1], [0, 2, 2, 3], [0, 2, 2, 0], [0, 2, 2, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_13_13 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨13, by decide⟩
  m := 5
  T1 := T119_13
  T2 := Q2.T119_13_2
  h1 := (0,0,2,3,3)
  h2 := (0,0,2,3,3)
  D := [[0, 2, 3, 4], [0, 2, 3, 1], [0, 2, 3, 3], [0, 2, 3, 0], [0, 2, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_13_14 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨13, by decide⟩
  m := 5
  T1 := T119_13
  T2 := Q2.T119_13_2
  h1 := (0,0,2,4,3)
  h2 := (0,0,2,4,3)
  D := [[0, 2, 4, 4], [0, 2, 4, 1], [0, 2, 4, 3], [0, 2, 4, 0], [0, 2, 4, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_13_15 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨13, by decide⟩
  m := 5
  T1 := T119_13
  T2 := Q2.T119_13_2
  h1 := (0,0,3,0,2)
  h2 := (0,0,3,0,2)
  D := [[0, 3, 0, 1], [0, 3, 0, 4], [0, 3, 0, 2], [0, 3, 0, 0], [0, 3, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_13_16 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨13, by decide⟩
  m := 5
  T1 := T119_13
  T2 := Q2.T119_13_2
  h1 := (0,0,3,1,2)
  h2 := (0,0,3,1,2)
  D := [[0, 3, 1, 1], [0, 3, 1, 4], [0, 3, 1, 2], [0, 3, 1, 0], [0, 3, 1, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_13_17 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨13, by decide⟩
  m := 5
  T1 := T119_13
  T2 := Q2.T119_13_2
  h1 := (0,0,3,2,2)
  h2 := (0,0,3,2,2)
  D := [[0, 3, 2, 1], [0, 3, 2, 4], [0, 3, 2, 2], [0, 3, 2, 0], [0, 3, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_13_18 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨13, by decide⟩
  m := 5
  T1 := T119_13
  T2 := Q2.T119_13_2
  h1 := (0,0,3,3,2)
  h2 := (0,0,3,3,2)
  D := [[0, 3, 3, 1], [0, 3, 3, 4], [0, 3, 3, 2], [0, 3, 3, 0], [0, 3, 3, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_13_19 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨13, by decide⟩
  m := 5
  T1 := T119_13
  T2 := Q2.T119_13_2
  h1 := (0,0,3,4,2)
  h2 := (0,0,3,4,2)
  D := [[0, 3, 4, 1], [0, 3, 4, 4], [0, 3, 4, 2], [0, 3, 4, 0], [0, 3, 4, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_13_20 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨13, by decide⟩
  m := 5
  T1 := T119_13
  T2 := Q2.T119_13_2
  h1 := (0,0,4,0,1)
  h2 := (0,0,4,0,1)
  D := [[0, 4, 0, 3], [0, 4, 0, 2], [0, 4, 0, 1], [0, 4, 0, 0], [0, 4, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_13_21 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨13, by decide⟩
  m := 5
  T1 := T119_13
  T2 := Q2.T119_13_2
  h1 := (0,0,4,1,1)
  h2 := (0,0,4,1,1)
  D := [[0, 4, 1, 3], [0, 4, 1, 2], [0, 4, 1, 1], [0, 4, 1, 0], [0, 4, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_13_22 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨13, by decide⟩
  m := 5
  T1 := T119_13
  T2 := Q2.T119_13_2
  h1 := (0,0,4,2,1)
  h2 := (0,0,4,2,1)
  D := [[0, 4, 2, 3], [0, 4, 2, 2], [0, 4, 2, 1], [0, 4, 2, 0], [0, 4, 2, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_13_23 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨13, by decide⟩
  m := 5
  T1 := T119_13
  T2 := Q2.T119_13_2
  h1 := (0,0,4,3,1)
  h2 := (0,0,4,3,1)
  D := [[0, 4, 3, 3], [0, 4, 3, 2], [0, 4, 3, 1], [0, 4, 3, 0], [0, 4, 3, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_13_24 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨13, by decide⟩
  m := 5
  T1 := T119_13
  T2 := Q2.T119_13_2
  h1 := (0,0,4,4,1)
  h2 := (0,0,4,4,1)
  D := [[0, 4, 4, 3], [0, 4, 4, 2], [0, 4, 4, 1], [0, 4, 4, 0], [0, 4, 4, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_19_0 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨19, by decide⟩
  m := 5
  T1 := T119_19
  T2 := Q2.T119_19_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_19_1 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨19, by decide⟩
  m := 5
  T1 := T119_19
  T2 := Q2.T119_19_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_19_2 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨19, by decide⟩
  m := 5
  T1 := T119_19
  T2 := Q2.T119_19_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_19_3 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨19, by decide⟩
  m := 5
  T1 := T119_19
  T2 := Q2.T119_19_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_19_4 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨19, by decide⟩
  m := 5
  T1 := T119_19
  T2 := Q2.T119_19_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_19_5 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨19, by decide⟩
  m := 5
  T1 := T119_19
  T2 := Q2.T119_19_2
  h1 := (0,0,1,4,0)
  h2 := (0,0,1,4,0)
  D := [[0, 1, 4, 3], [0, 1, 4, 4], [0, 1, 4, 0], [0, 1, 4, 1], [0, 1, 4, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_19_10 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨19, by decide⟩
  m := 5
  T1 := T119_19
  T2 := Q2.T119_19_2
  h1 := (0,0,2,3,0)
  h2 := (0,0,2,3,0)
  D := [[0, 2, 3, 1], [0, 2, 3, 3], [0, 2, 3, 0], [0, 2, 3, 2], [0, 2, 3, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_19_15 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨19, by decide⟩
  m := 5
  T1 := T119_19
  T2 := Q2.T119_19_2
  h1 := (0,0,3,2,0)
  h2 := (0,0,3,2,0)
  D := [[0, 3, 2, 4], [0, 3, 2, 2], [0, 3, 2, 0], [0, 3, 2, 3], [0, 3, 2, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_19_20 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨19, by decide⟩
  m := 5
  T1 := T119_19
  T2 := Q2.T119_19_2
  h1 := (0,0,4,1,0)
  h2 := (0,0,4,1,0)
  D := [[0, 4, 1, 2], [0, 4, 1, 1], [0, 4, 1, 0], [0, 4, 1, 4], [0, 4, 1, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_24_0 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨24, by decide⟩
  m := 5
  T1 := T119_24
  T2 := Q2.T119_24_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_24_1 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨24, by decide⟩
  m := 5
  T1 := T119_24
  T2 := Q2.T119_24_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_24_2 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨24, by decide⟩
  m := 5
  T1 := T119_24
  T2 := Q2.T119_24_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_24_3 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨24, by decide⟩
  m := 5
  T1 := T119_24
  T2 := Q2.T119_24_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

end LeanDring.P5Presentation
