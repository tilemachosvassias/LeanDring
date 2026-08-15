/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.Twin1.ColCert
import LeanDring.P5.Data.EntryK.C026

/-!
# Species-table cell data, stage 2 — twin-coincident columns (cheap tier)

Per-column certified exponent-vector data (`ColCert`/`ColCertDiv`) with kernel
`decide` bindings. Emitted; the embedded lists are what the kernel certifies.
rest tier, chunk 24: 60 columns.
-/

-- machine-emitted data: silence style linters (generated long lines, file-level options)
set_option linter.style.longLine false

namespace LeanDring.P5Presentation

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

def colCert_117_26_10 : ColCert where
  rK := ⟨117, by decide⟩
  rH := ⟨26, by decide⟩
  m := 5
  T1 := T117_26
  T2 := Q2.T117_26_2
  h1 := (0,0,2,2,0)
  h2 := (0,0,2,2,0)
  D := [[0, 2, 2, 3], [0, 2, 2, 0], [0, 2, 2, 2], [0, 2, 2, 4], [0, 2, 2, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_117_26_15 : ColCert where
  rK := ⟨117, by decide⟩
  rH := ⟨26, by decide⟩
  m := 5
  T1 := T117_26
  T2 := Q2.T117_26_2
  h1 := (0,0,3,3,0)
  h2 := (0,0,3,3,0)
  D := [[0, 3, 3, 2], [0, 3, 3, 0], [0, 3, 3, 3], [0, 3, 3, 1], [0, 3, 3, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_117_26_20 : ColCert where
  rK := ⟨117, by decide⟩
  rH := ⟨26, by decide⟩
  m := 5
  T1 := T117_26
  T2 := Q2.T117_26_2
  h1 := (0,0,4,4,0)
  h2 := (0,0,4,4,0)
  D := [[0, 4, 4, 1], [0, 4, 4, 0], [0, 4, 4, 4], [0, 4, 4, 3], [0, 4, 4, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_117_27_0 : ColCert where
  rK := ⟨117, by decide⟩
  rH := ⟨27, by decide⟩
  m := 5
  T1 := T117_27
  T2 := Q2.T117_27_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_117_27_1 : ColCert where
  rK := ⟨117, by decide⟩
  rH := ⟨27, by decide⟩
  m := 5
  T1 := T117_27
  T2 := Q2.T117_27_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_117_27_2 : ColCert where
  rK := ⟨117, by decide⟩
  rH := ⟨27, by decide⟩
  m := 5
  T1 := T117_27
  T2 := Q2.T117_27_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_117_27_3 : ColCert where
  rK := ⟨117, by decide⟩
  rH := ⟨27, by decide⟩
  m := 5
  T1 := T117_27
  T2 := Q2.T117_27_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_117_27_4 : ColCert where
  rK := ⟨117, by decide⟩
  rH := ⟨27, by decide⟩
  m := 5
  T1 := T117_27
  T2 := Q2.T117_27_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_117_27_5 : ColCert where
  rK := ⟨117, by decide⟩
  rH := ⟨27, by decide⟩
  m := 5
  T1 := T117_27
  T2 := Q2.T117_27_2
  h1 := (0,0,1,0,0)
  h2 := (0,0,1,0,0)
  D := [[0, 1, 0, 4], [0, 1, 0, 0], [0, 1, 0, 1], [0, 1, 0, 2], [0, 1, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_117_27_10 : ColCert where
  rK := ⟨117, by decide⟩
  rH := ⟨27, by decide⟩
  m := 5
  T1 := T117_27
  T2 := Q2.T117_27_2
  h1 := (0,0,2,0,0)
  h2 := (0,0,2,0,0)
  D := [[0, 2, 0, 3], [0, 2, 0, 0], [0, 2, 0, 2], [0, 2, 0, 4], [0, 2, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_117_27_15 : ColCert where
  rK := ⟨117, by decide⟩
  rH := ⟨27, by decide⟩
  m := 5
  T1 := T117_27
  T2 := Q2.T117_27_2
  h1 := (0,0,3,0,0)
  h2 := (0,0,3,0,0)
  D := [[0, 3, 0, 2], [0, 3, 0, 0], [0, 3, 0, 3], [0, 3, 0, 1], [0, 3, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_117_27_20 : ColCert where
  rK := ⟨117, by decide⟩
  rH := ⟨27, by decide⟩
  m := 5
  T1 := T117_27
  T2 := Q2.T117_27_2
  h1 := (0,0,4,0,0)
  h2 := (0,0,4,0,0)
  D := [[0, 4, 0, 1], [0, 4, 0, 0], [0, 4, 0, 4], [0, 4, 0, 3], [0, 4, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_117_29_0 : ColCert where
  rK := ⟨117, by decide⟩
  rH := ⟨29, by decide⟩
  m := 5
  T1 := T117_29
  T2 := Q2.T117_29_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_117_29_1 : ColCert where
  rK := ⟨117, by decide⟩
  rH := ⟨29, by decide⟩
  m := 5
  T1 := T117_29
  T2 := Q2.T117_29_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_117_29_2 : ColCert where
  rK := ⟨117, by decide⟩
  rH := ⟨29, by decide⟩
  m := 5
  T1 := T117_29
  T2 := Q2.T117_29_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_117_29_3 : ColCert where
  rK := ⟨117, by decide⟩
  rH := ⟨29, by decide⟩
  m := 5
  T1 := T117_29
  T2 := Q2.T117_29_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_117_29_4 : ColCert where
  rK := ⟨117, by decide⟩
  rH := ⟨29, by decide⟩
  m := 5
  T1 := T117_29
  T2 := Q2.T117_29_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_117_29_5 : ColCert where
  rK := ⟨117, by decide⟩
  rH := ⟨29, by decide⟩
  m := 5
  T1 := T117_29
  T2 := Q2.T117_29_2
  h1 := (1,4,1,3,3)
  h2 := (1,4,1,3,3)
  D := [[1, 1, 0, 3], [1, 1, 4, 0], [1, 1, 3, 2], [1, 1, 2, 4], [1, 1, 1, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_117_29_10 : ColCert where
  rK := ⟨117, by decide⟩
  rH := ⟨29, by decide⟩
  m := 5
  T1 := T117_29
  T2 := Q2.T117_29_2
  h1 := (2,3,2,0,4)
  h2 := (2,3,2,0,0)
  D := [[2, 2, 0, 2], [2, 2, 3, 2], [2, 2, 1, 2], [2, 2, 4, 2], [2, 2, 2, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_117_29_15 : ColCert where
  rK := ⟨117, by decide⟩
  rH := ⟨29, by decide⟩
  m := 5
  T1 := T117_29
  T2 := Q2.T117_29_2
  h1 := (3,2,3,1,1)
  h2 := (3,2,3,1,3)
  D := [[3, 3, 0, 2], [3, 3, 2, 1], [3, 3, 4, 0], [3, 3, 1, 4], [3, 3, 3, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_117_29_20 : ColCert where
  rK := ⟨117, by decide⟩
  rH := ⟨29, by decide⟩
  m := 5
  T1 := T117_29
  T2 := Q2.T117_29_2
  h1 := (4,1,4,1,3)
  h2 := (4,1,4,1,1)
  D := [[4, 4, 0, 3], [4, 4, 1, 2], [4, 4, 2, 1], [4, 4, 3, 0], [4, 4, 4, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_117_34_0 : ColCert where
  rK := ⟨117, by decide⟩
  rH := ⟨34, by decide⟩
  m := 5
  T1 := T117_34
  T2 := Q2.T117_34_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_117_34_1 : ColCert where
  rK := ⟨117, by decide⟩
  rH := ⟨34, by decide⟩
  m := 5
  T1 := T117_34
  T2 := Q2.T117_34_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_117_34_2 : ColCert where
  rK := ⟨117, by decide⟩
  rH := ⟨34, by decide⟩
  m := 5
  T1 := T117_34
  T2 := Q2.T117_34_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_117_34_3 : ColCert where
  rK := ⟨117, by decide⟩
  rH := ⟨34, by decide⟩
  m := 5
  T1 := T117_34
  T2 := Q2.T117_34_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_117_34_4 : ColCert where
  rK := ⟨117, by decide⟩
  rH := ⟨34, by decide⟩
  m := 5
  T1 := T117_34
  T2 := Q2.T117_34_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_117_34_5 : ColCert where
  rK := ⟨117, by decide⟩
  rH := ⟨34, by decide⟩
  m := 5
  T1 := T117_34
  T2 := Q2.T117_34_2
  h1 := (1,4,3,3,1)
  h2 := (1,4,3,3,1)
  D := [[1, 3, 0, 1], [1, 3, 4, 0], [1, 3, 3, 4], [1, 3, 2, 3], [1, 3, 1, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_117_34_10 : ColCert where
  rK := ⟨117, by decide⟩
  rH := ⟨34, by decide⟩
  m := 5
  T1 := T117_34
  T2 := Q2.T117_34_2
  h1 := (2,3,1,0,3)
  h2 := (2,3,1,0,4)
  D := [[2, 1, 0, 0], [2, 1, 3, 4], [2, 1, 1, 3], [2, 1, 4, 2], [2, 1, 2, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_117_34_15 : ColCert where
  rK := ⟨117, by decide⟩
  rH := ⟨34, by decide⟩
  m := 5
  T1 := T117_34
  T2 := Q2.T117_34_2
  h1 := (3,2,4,1,4)
  h2 := (3,2,4,1,1)
  D := [[3, 4, 0, 2], [3, 4, 2, 2], [3, 4, 4, 2], [3, 4, 1, 2], [3, 4, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_117_34_20 : ColCert where
  rK := ⟨117, by decide⟩
  rH := ⟨34, by decide⟩
  m := 5
  T1 := T117_34
  T2 := Q2.T117_34_2
  h1 := (4,1,2,1,3)
  h2 := (4,1,2,1,1)
  D := [[4, 2, 0, 2], [4, 2, 1, 4], [4, 2, 2, 1], [4, 2, 3, 3], [4, 2, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_117_39_0 : ColCert where
  rK := ⟨117, by decide⟩
  rH := ⟨39, by decide⟩
  m := 5
  T1 := T117_39
  T2 := Q2.T117_39_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_117_39_1 : ColCert where
  rK := ⟨117, by decide⟩
  rH := ⟨39, by decide⟩
  m := 5
  T1 := T117_39
  T2 := Q2.T117_39_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_117_39_2 : ColCert where
  rK := ⟨117, by decide⟩
  rH := ⟨39, by decide⟩
  m := 5
  T1 := T117_39
  T2 := Q2.T117_39_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_117_39_3 : ColCert where
  rK := ⟨117, by decide⟩
  rH := ⟨39, by decide⟩
  m := 5
  T1 := T117_39
  T2 := Q2.T117_39_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_117_39_4 : ColCert where
  rK := ⟨117, by decide⟩
  rH := ⟨39, by decide⟩
  m := 5
  T1 := T117_39
  T2 := Q2.T117_39_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_117_39_5 : ColCert where
  rK := ⟨117, by decide⟩
  rH := ⟨39, by decide⟩
  m := 5
  T1 := T117_39
  T2 := Q2.T117_39_2
  h1 := (1,4,2,3,2)
  h2 := (1,4,2,3,2)
  D := [[1, 2, 0, 2], [1, 2, 4, 0], [1, 2, 3, 3], [1, 2, 2, 1], [1, 2, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_117_39_10 : ColCert where
  rK := ⟨117, by decide⟩
  rH := ⟨39, by decide⟩
  m := 5
  T1 := T117_39
  T2 := Q2.T117_39_2
  h1 := (2,3,4,0,1)
  h2 := (2,3,4,0,2)
  D := [[2, 4, 0, 1], [2, 4, 3, 3], [2, 4, 1, 0], [2, 4, 4, 2], [2, 4, 2, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_117_39_15 : ColCert where
  rK := ⟨117, by decide⟩
  rH := ⟨39, by decide⟩
  m := 5
  T1 := T117_39
  T2 := Q2.T117_39_2
  h1 := (3,2,1,1,0)
  h2 := (3,2,1,1,2)
  D := [[3, 1, 0, 2], [3, 1, 2, 4], [3, 1, 4, 1], [3, 1, 1, 3], [3, 1, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_117_39_20 : ColCert where
  rK := ⟨117, by decide⟩
  rH := ⟨39, by decide⟩
  m := 5
  T1 := T117_39
  T2 := Q2.T117_39_2
  h1 := (4,1,3,1,3)
  h2 := (4,1,3,1,1)
  D := [[4, 3, 0, 0], [4, 3, 1, 3], [4, 3, 2, 1], [4, 3, 3, 4], [4, 3, 4, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_117_44_0 : ColCert where
  rK := ⟨117, by decide⟩
  rH := ⟨44, by decide⟩
  m := 5
  T1 := T117_44
  T2 := Q2.T117_44_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_117_44_1 : ColCert where
  rK := ⟨117, by decide⟩
  rH := ⟨44, by decide⟩
  m := 5
  T1 := T117_44
  T2 := Q2.T117_44_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_117_44_2 : ColCert where
  rK := ⟨117, by decide⟩
  rH := ⟨44, by decide⟩
  m := 5
  T1 := T117_44
  T2 := Q2.T117_44_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_117_44_3 : ColCert where
  rK := ⟨117, by decide⟩
  rH := ⟨44, by decide⟩
  m := 5
  T1 := T117_44
  T2 := Q2.T117_44_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_117_44_4 : ColCert where
  rK := ⟨117, by decide⟩
  rH := ⟨44, by decide⟩
  m := 5
  T1 := T117_44
  T2 := Q2.T117_44_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_117_44_5 : ColCert where
  rK := ⟨117, by decide⟩
  rH := ⟨44, by decide⟩
  m := 5
  T1 := T117_44
  T2 := Q2.T117_44_2
  h1 := (1,4,4,3,0)
  h2 := (1,4,4,3,0)
  D := [[1, 4, 0, 0], [1, 4, 4, 0], [1, 4, 3, 0], [1, 4, 2, 0], [1, 4, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_117_44_10 : ColCert where
  rK := ⟨117, by decide⟩
  rH := ⟨44, by decide⟩
  m := 5
  T1 := T117_44
  T2 := Q2.T117_44_2
  h1 := (2,3,3,0,0)
  h2 := (2,3,3,0,1)
  D := [[2, 3, 0, 4], [2, 3, 3, 0], [2, 3, 1, 1], [2, 3, 4, 2], [2, 3, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_117_44_15 : ColCert where
  rK := ⟨117, by decide⟩
  rH := ⟨44, by decide⟩
  m := 5
  T1 := T117_44
  T2 := Q2.T117_44_2
  h1 := (3,2,2,1,3)
  h2 := (3,2,2,1,0)
  D := [[3, 2, 0, 2], [3, 2, 2, 0], [3, 2, 4, 3], [3, 2, 1, 1], [3, 2, 3, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_117_44_20 : ColCert where
  rK := ⟨117, by decide⟩
  rH := ⟨44, by decide⟩
  m := 5
  T1 := T117_44
  T2 := Q2.T117_44_2
  h1 := (4,1,1,1,3)
  h2 := (4,1,1,1,1)
  D := [[4, 1, 0, 4], [4, 1, 1, 0], [4, 1, 2, 1], [4, 1, 3, 2], [4, 1, 4, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_117_49_0 : ColCert where
  rK := ⟨117, by decide⟩
  rH := ⟨49, by decide⟩
  m := 5
  T1 := T117_49
  T2 := Q2.T117_49_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_117_49_1 : ColCert where
  rK := ⟨117, by decide⟩
  rH := ⟨49, by decide⟩
  m := 5
  T1 := T117_49
  T2 := Q2.T117_49_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_117_49_2 : ColCert where
  rK := ⟨117, by decide⟩
  rH := ⟨49, by decide⟩
  m := 5
  T1 := T117_49
  T2 := Q2.T117_49_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_117_49_3 : ColCert where
  rK := ⟨117, by decide⟩
  rH := ⟨49, by decide⟩
  m := 5
  T1 := T117_49
  T2 := Q2.T117_49_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_117_49_4 : ColCert where
  rK := ⟨117, by decide⟩
  rH := ⟨49, by decide⟩
  m := 5
  T1 := T117_49
  T2 := Q2.T117_49_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_117_49_5 : ColCert where
  rK := ⟨117, by decide⟩
  rH := ⟨49, by decide⟩
  m := 5
  T1 := T117_49
  T2 := Q2.T117_49_2
  h1 := (1,4,0,3,4)
  h2 := (1,4,0,3,4)
  D := [[1, 0, 0, 4], [1, 0, 4, 0], [1, 0, 3, 1], [1, 0, 2, 2], [1, 0, 1, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_117_49_10 : ColCert where
  rK := ⟨117, by decide⟩
  rH := ⟨49, by decide⟩
  m := 5
  T1 := T117_49
  T2 := Q2.T117_49_2
  h1 := (2,3,0,0,2)
  h2 := (2,3,0,0,3)
  D := [[2, 0, 0, 3], [2, 0, 3, 1], [2, 0, 1, 4], [2, 0, 4, 2], [2, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_117_49_15 : ColCert where
  rK := ⟨117, by decide⟩
  rH := ⟨49, by decide⟩
  m := 5
  T1 := T117_49
  T2 := Q2.T117_49_2
  h1 := (3,2,0,1,2)
  h2 := (3,2,0,1,4)
  D := [[3, 0, 0, 2], [3, 0, 2, 3], [3, 0, 4, 4], [3, 0, 1, 0], [3, 0, 3, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_117_49_20 : ColCert where
  rK := ⟨117, by decide⟩
  rH := ⟨49, by decide⟩
  m := 5
  T1 := T117_49
  T2 := Q2.T117_49_2
  h1 := (4,1,0,1,3)
  h2 := (4,1,0,1,1)
  D := [[4, 0, 0, 1], [4, 0, 1, 1], [4, 0, 2, 1], [4, 0, 3, 1], [4, 0, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_117_53_0 : ColCert where
  rK := ⟨117, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T117_53
  T2 := Q2.T117_53_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_117_53_1 : ColCert where
  rK := ⟨117, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T117_53
  T2 := Q2.T117_53_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_117_53_2 : ColCert where
  rK := ⟨117, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T117_53
  T2 := Q2.T117_53_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

end LeanDring.P5Presentation
