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
rest tier, chunk 36: 60 columns.
-/

-- machine-emitted data: silence style linters (generated long lines, file-level options)
set_option linter.style.longLine false

namespace LeanDring.P5Presentation

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

def colCert_119_24_4 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨24, by decide⟩
  m := 5
  T1 := T119_24
  T2 := Q2.T119_24_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_24_5 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨24, by decide⟩
  m := 5
  T1 := T119_24
  T2 := Q2.T119_24_2
  h1 := (0,0,1,2,0)
  h2 := (0,0,1,2,0)
  D := [[0, 1, 2, 3], [0, 1, 2, 4], [0, 1, 2, 0], [0, 1, 2, 1], [0, 1, 2, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_24_10 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨24, by decide⟩
  m := 5
  T1 := T119_24
  T2 := Q2.T119_24_2
  h1 := (0,0,2,4,0)
  h2 := (0,0,2,4,0)
  D := [[0, 2, 4, 1], [0, 2, 4, 3], [0, 2, 4, 0], [0, 2, 4, 2], [0, 2, 4, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_24_15 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨24, by decide⟩
  m := 5
  T1 := T119_24
  T2 := Q2.T119_24_2
  h1 := (0,0,3,1,0)
  h2 := (0,0,3,1,0)
  D := [[0, 3, 1, 4], [0, 3, 1, 2], [0, 3, 1, 0], [0, 3, 1, 3], [0, 3, 1, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_24_20 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨24, by decide⟩
  m := 5
  T1 := T119_24
  T2 := Q2.T119_24_2
  h1 := (0,0,4,3,0)
  h2 := (0,0,4,3,0)
  D := [[0, 4, 3, 2], [0, 4, 3, 1], [0, 4, 3, 0], [0, 4, 3, 4], [0, 4, 3, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_25_0 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨25, by decide⟩
  m := 5
  T1 := T119_25
  T2 := Q2.T119_25_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_25_1 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨25, by decide⟩
  m := 5
  T1 := T119_25
  T2 := Q2.T119_25_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_25_2 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨25, by decide⟩
  m := 5
  T1 := T119_25
  T2 := Q2.T119_25_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_25_3 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨25, by decide⟩
  m := 5
  T1 := T119_25
  T2 := Q2.T119_25_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_25_4 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨25, by decide⟩
  m := 5
  T1 := T119_25
  T2 := Q2.T119_25_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_25_5 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨25, by decide⟩
  m := 5
  T1 := T119_25
  T2 := Q2.T119_25_2
  h1 := (0,0,1,3,0)
  h2 := (0,0,1,3,0)
  D := [[0, 1, 3, 3], [0, 1, 3, 4], [0, 1, 3, 0], [0, 1, 3, 1], [0, 1, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_25_10 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨25, by decide⟩
  m := 5
  T1 := T119_25
  T2 := Q2.T119_25_2
  h1 := (0,0,2,1,0)
  h2 := (0,0,2,1,0)
  D := [[0, 2, 1, 1], [0, 2, 1, 3], [0, 2, 1, 0], [0, 2, 1, 2], [0, 2, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_25_15 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨25, by decide⟩
  m := 5
  T1 := T119_25
  T2 := Q2.T119_25_2
  h1 := (0,0,3,4,0)
  h2 := (0,0,3,4,0)
  D := [[0, 3, 4, 4], [0, 3, 4, 2], [0, 3, 4, 0], [0, 3, 4, 3], [0, 3, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_25_20 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨25, by decide⟩
  m := 5
  T1 := T119_25
  T2 := Q2.T119_25_2
  h1 := (0,0,4,2,0)
  h2 := (0,0,4,2,0)
  D := [[0, 4, 2, 2], [0, 4, 2, 1], [0, 4, 2, 0], [0, 4, 2, 4], [0, 4, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_26_0 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨26, by decide⟩
  m := 5
  T1 := T119_26
  T2 := Q2.T119_26_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_26_1 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨26, by decide⟩
  m := 5
  T1 := T119_26
  T2 := Q2.T119_26_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_26_2 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨26, by decide⟩
  m := 5
  T1 := T119_26
  T2 := Q2.T119_26_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_26_3 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨26, by decide⟩
  m := 5
  T1 := T119_26
  T2 := Q2.T119_26_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_26_4 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨26, by decide⟩
  m := 5
  T1 := T119_26
  T2 := Q2.T119_26_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_26_5 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨26, by decide⟩
  m := 5
  T1 := T119_26
  T2 := Q2.T119_26_2
  h1 := (0,0,1,1,0)
  h2 := (0,0,1,1,0)
  D := [[0, 1, 1, 3], [0, 1, 1, 4], [0, 1, 1, 0], [0, 1, 1, 1], [0, 1, 1, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_26_10 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨26, by decide⟩
  m := 5
  T1 := T119_26
  T2 := Q2.T119_26_2
  h1 := (0,0,2,2,0)
  h2 := (0,0,2,2,0)
  D := [[0, 2, 2, 1], [0, 2, 2, 3], [0, 2, 2, 0], [0, 2, 2, 2], [0, 2, 2, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_26_15 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨26, by decide⟩
  m := 5
  T1 := T119_26
  T2 := Q2.T119_26_2
  h1 := (0,0,3,3,0)
  h2 := (0,0,3,3,0)
  D := [[0, 3, 3, 4], [0, 3, 3, 2], [0, 3, 3, 0], [0, 3, 3, 3], [0, 3, 3, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_26_20 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨26, by decide⟩
  m := 5
  T1 := T119_26
  T2 := Q2.T119_26_2
  h1 := (0,0,4,4,0)
  h2 := (0,0,4,4,0)
  D := [[0, 4, 4, 2], [0, 4, 4, 1], [0, 4, 4, 0], [0, 4, 4, 4], [0, 4, 4, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_27_0 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨27, by decide⟩
  m := 5
  T1 := T119_27
  T2 := Q2.T119_27_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_27_1 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨27, by decide⟩
  m := 5
  T1 := T119_27
  T2 := Q2.T119_27_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_27_2 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨27, by decide⟩
  m := 5
  T1 := T119_27
  T2 := Q2.T119_27_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_27_3 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨27, by decide⟩
  m := 5
  T1 := T119_27
  T2 := Q2.T119_27_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_27_4 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨27, by decide⟩
  m := 5
  T1 := T119_27
  T2 := Q2.T119_27_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_27_5 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨27, by decide⟩
  m := 5
  T1 := T119_27
  T2 := Q2.T119_27_2
  h1 := (0,0,1,0,0)
  h2 := (0,0,1,0,0)
  D := [[0, 1, 0, 3], [0, 1, 0, 4], [0, 1, 0, 0], [0, 1, 0, 1], [0, 1, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_27_10 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨27, by decide⟩
  m := 5
  T1 := T119_27
  T2 := Q2.T119_27_2
  h1 := (0,0,2,0,0)
  h2 := (0,0,2,0,0)
  D := [[0, 2, 0, 1], [0, 2, 0, 3], [0, 2, 0, 0], [0, 2, 0, 2], [0, 2, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_27_15 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨27, by decide⟩
  m := 5
  T1 := T119_27
  T2 := Q2.T119_27_2
  h1 := (0,0,3,0,0)
  h2 := (0,0,3,0,0)
  D := [[0, 3, 0, 4], [0, 3, 0, 2], [0, 3, 0, 0], [0, 3, 0, 3], [0, 3, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_27_20 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨27, by decide⟩
  m := 5
  T1 := T119_27
  T2 := Q2.T119_27_2
  h1 := (0,0,4,0,0)
  h2 := (0,0,4,0,0)
  D := [[0, 4, 0, 2], [0, 4, 0, 1], [0, 4, 0, 0], [0, 4, 0, 4], [0, 4, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_31_0 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨31, by decide⟩
  m := 5
  T1 := T119_31
  T2 := Q2.T119_31_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_31_1 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨31, by decide⟩
  m := 5
  T1 := T119_31
  T2 := Q2.T119_31_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_31_2 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨31, by decide⟩
  m := 5
  T1 := T119_31
  T2 := Q2.T119_31_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_31_3 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨31, by decide⟩
  m := 5
  T1 := T119_31
  T2 := Q2.T119_31_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_31_4 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨31, by decide⟩
  m := 5
  T1 := T119_31
  T2 := Q2.T119_31_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_36_0 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨36, by decide⟩
  m := 5
  T1 := T119_36
  T2 := Q2.T119_36_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_36_1 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨36, by decide⟩
  m := 5
  T1 := T119_36
  T2 := Q2.T119_36_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_36_2 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨36, by decide⟩
  m := 5
  T1 := T119_36
  T2 := Q2.T119_36_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_36_3 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨36, by decide⟩
  m := 5
  T1 := T119_36
  T2 := Q2.T119_36_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_36_4 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨36, by decide⟩
  m := 5
  T1 := T119_36
  T2 := Q2.T119_36_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_41_0 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨41, by decide⟩
  m := 5
  T1 := T119_41
  T2 := Q2.T119_41_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_41_1 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨41, by decide⟩
  m := 5
  T1 := T119_41
  T2 := Q2.T119_41_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_41_2 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨41, by decide⟩
  m := 5
  T1 := T119_41
  T2 := Q2.T119_41_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_41_3 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨41, by decide⟩
  m := 5
  T1 := T119_41
  T2 := Q2.T119_41_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_41_4 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨41, by decide⟩
  m := 5
  T1 := T119_41
  T2 := Q2.T119_41_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_46_0 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨46, by decide⟩
  m := 5
  T1 := T119_46
  T2 := Q2.T119_46_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_46_1 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨46, by decide⟩
  m := 5
  T1 := T119_46
  T2 := Q2.T119_46_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_46_2 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨46, by decide⟩
  m := 5
  T1 := T119_46
  T2 := Q2.T119_46_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_46_3 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨46, by decide⟩
  m := 5
  T1 := T119_46
  T2 := Q2.T119_46_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_46_4 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨46, by decide⟩
  m := 5
  T1 := T119_46
  T2 := Q2.T119_46_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_51_0 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨51, by decide⟩
  m := 5
  T1 := T119_51
  T2 := Q2.T119_51_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_51_1 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨51, by decide⟩
  m := 5
  T1 := T119_51
  T2 := Q2.T119_51_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_51_2 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨51, by decide⟩
  m := 5
  T1 := T119_51
  T2 := Q2.T119_51_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_51_3 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨51, by decide⟩
  m := 5
  T1 := T119_51
  T2 := Q2.T119_51_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_51_4 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨51, by decide⟩
  m := 5
  T1 := T119_51
  T2 := Q2.T119_51_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_53_0 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T119_53
  T2 := Q2.T119_53_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_53_1 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T119_53
  T2 := Q2.T119_53_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_53_2 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T119_53
  T2 := Q2.T119_53_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

end LeanDring.P5Presentation
