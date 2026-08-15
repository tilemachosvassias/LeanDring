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
rest tier, chunk 112: 60 columns.
-/

-- machine-emitted data: silence style linters (generated long lines, file-level options)
set_option linter.style.longLine false

namespace LeanDring.P5Presentation

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

def colCert_147_25_15 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨25, by decide⟩
  m := 1
  T1 := T147_25
  T2 := Q2.T147_25_2
  h1 := (0,0,3,4,0)
  h2 := (0,0,3,4,0)
  D := [[0, 0, 3, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_25_20 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨25, by decide⟩
  m := 1
  T1 := T147_25
  T2 := Q2.T147_25_2
  h1 := (0,0,4,2,0)
  h2 := (0,0,4,2,0)
  D := [[0, 0, 4, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_26_0 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨26, by decide⟩
  m := 1
  T1 := T147_26
  T2 := Q2.T147_26_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_26_1 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨26, by decide⟩
  m := 1
  T1 := T147_26
  T2 := Q2.T147_26_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_26_2 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨26, by decide⟩
  m := 1
  T1 := T147_26
  T2 := Q2.T147_26_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_26_3 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨26, by decide⟩
  m := 1
  T1 := T147_26
  T2 := Q2.T147_26_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_26_4 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨26, by decide⟩
  m := 1
  T1 := T147_26
  T2 := Q2.T147_26_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_26_5 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨26, by decide⟩
  m := 1
  T1 := T147_26
  T2 := Q2.T147_26_2
  h1 := (0,0,1,1,0)
  h2 := (0,0,1,1,0)
  D := [[0, 0, 1, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_26_10 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨26, by decide⟩
  m := 1
  T1 := T147_26
  T2 := Q2.T147_26_2
  h1 := (0,0,2,2,0)
  h2 := (0,0,2,2,0)
  D := [[0, 0, 2, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_26_15 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨26, by decide⟩
  m := 1
  T1 := T147_26
  T2 := Q2.T147_26_2
  h1 := (0,0,3,3,0)
  h2 := (0,0,3,3,0)
  D := [[0, 0, 3, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_26_20 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨26, by decide⟩
  m := 1
  T1 := T147_26
  T2 := Q2.T147_26_2
  h1 := (0,0,4,4,0)
  h2 := (0,0,4,4,0)
  D := [[0, 0, 4, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_27_0 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨27, by decide⟩
  m := 1
  T1 := T147_27
  T2 := Q2.T147_27_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_27_1 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨27, by decide⟩
  m := 1
  T1 := T147_27
  T2 := Q2.T147_27_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_27_2 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨27, by decide⟩
  m := 1
  T1 := T147_27
  T2 := Q2.T147_27_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_27_3 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨27, by decide⟩
  m := 1
  T1 := T147_27
  T2 := Q2.T147_27_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_27_4 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨27, by decide⟩
  m := 1
  T1 := T147_27
  T2 := Q2.T147_27_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_27_5 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨27, by decide⟩
  m := 1
  T1 := T147_27
  T2 := Q2.T147_27_2
  h1 := (0,0,1,0,0)
  h2 := (0,0,1,0,0)
  D := [[0, 0, 1, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_27_10 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨27, by decide⟩
  m := 1
  T1 := T147_27
  T2 := Q2.T147_27_2
  h1 := (0,0,2,0,0)
  h2 := (0,0,2,0,0)
  D := [[0, 0, 2, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_27_15 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨27, by decide⟩
  m := 1
  T1 := T147_27
  T2 := Q2.T147_27_2
  h1 := (0,0,3,0,0)
  h2 := (0,0,3,0,0)
  D := [[0, 0, 3, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_27_20 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨27, by decide⟩
  m := 1
  T1 := T147_27
  T2 := Q2.T147_27_2
  h1 := (0,0,4,0,0)
  h2 := (0,0,4,0,0)
  D := [[0, 0, 4, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_28_0 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨28, by decide⟩
  m := 1
  T1 := T147_28
  T2 := Q2.T147_28_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_28_1 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨28, by decide⟩
  m := 1
  T1 := T147_28
  T2 := Q2.T147_28_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_28_2 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨28, by decide⟩
  m := 1
  T1 := T147_28
  T2 := Q2.T147_28_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_28_3 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨28, by decide⟩
  m := 1
  T1 := T147_28
  T2 := Q2.T147_28_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_28_4 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨28, by decide⟩
  m := 1
  T1 := T147_28
  T2 := Q2.T147_28_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_29_0 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨29, by decide⟩
  m := 1
  T1 := T147_29
  T2 := Q2.T147_29_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_29_1 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨29, by decide⟩
  m := 1
  T1 := T147_29
  T2 := Q2.T147_29_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_29_2 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨29, by decide⟩
  m := 1
  T1 := T147_29
  T2 := Q2.T147_29_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_29_3 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨29, by decide⟩
  m := 1
  T1 := T147_29
  T2 := Q2.T147_29_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_29_4 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨29, by decide⟩
  m := 1
  T1 := T147_29
  T2 := Q2.T147_29_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_29_5 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨29, by decide⟩
  m := 1
  T1 := T147_29
  T2 := Q2.T147_29_2
  h1 := (1,4,1,3,3)
  h2 := (1,4,1,3,3)
  D := [[1, 4, 1, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_30_0 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨30, by decide⟩
  m := 1
  T1 := T147_30
  T2 := Q2.T147_30_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_30_1 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨30, by decide⟩
  m := 1
  T1 := T147_30
  T2 := Q2.T147_30_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_30_2 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨30, by decide⟩
  m := 1
  T1 := T147_30
  T2 := Q2.T147_30_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_30_3 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨30, by decide⟩
  m := 1
  T1 := T147_30
  T2 := Q2.T147_30_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_30_4 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨30, by decide⟩
  m := 1
  T1 := T147_30
  T2 := Q2.T147_30_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_31_0 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨31, by decide⟩
  m := 1
  T1 := T147_31
  T2 := Q2.T147_31_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_31_1 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨31, by decide⟩
  m := 1
  T1 := T147_31
  T2 := Q2.T147_31_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_31_2 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨31, by decide⟩
  m := 1
  T1 := T147_31
  T2 := Q2.T147_31_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_31_3 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨31, by decide⟩
  m := 1
  T1 := T147_31
  T2 := Q2.T147_31_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_31_4 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨31, by decide⟩
  m := 1
  T1 := T147_31
  T2 := Q2.T147_31_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_32_0 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨32, by decide⟩
  m := 1
  T1 := T147_32
  T2 := Q2.T147_32_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_32_1 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨32, by decide⟩
  m := 1
  T1 := T147_32
  T2 := Q2.T147_32_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_32_2 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨32, by decide⟩
  m := 1
  T1 := T147_32
  T2 := Q2.T147_32_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_32_3 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨32, by decide⟩
  m := 1
  T1 := T147_32
  T2 := Q2.T147_32_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_32_4 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨32, by decide⟩
  m := 1
  T1 := T147_32
  T2 := Q2.T147_32_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_33_0 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨33, by decide⟩
  m := 1
  T1 := T147_33
  T2 := Q2.T147_33_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_33_1 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨33, by decide⟩
  m := 1
  T1 := T147_33
  T2 := Q2.T147_33_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_33_2 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨33, by decide⟩
  m := 1
  T1 := T147_33
  T2 := Q2.T147_33_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_33_3 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨33, by decide⟩
  m := 1
  T1 := T147_33
  T2 := Q2.T147_33_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_33_4 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨33, by decide⟩
  m := 1
  T1 := T147_33
  T2 := Q2.T147_33_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_34_0 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨34, by decide⟩
  m := 1
  T1 := T147_34
  T2 := Q2.T147_34_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_34_1 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨34, by decide⟩
  m := 1
  T1 := T147_34
  T2 := Q2.T147_34_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_34_2 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨34, by decide⟩
  m := 1
  T1 := T147_34
  T2 := Q2.T147_34_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_34_3 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨34, by decide⟩
  m := 1
  T1 := T147_34
  T2 := Q2.T147_34_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_34_4 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨34, by decide⟩
  m := 1
  T1 := T147_34
  T2 := Q2.T147_34_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_34_5 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨34, by decide⟩
  m := 1
  T1 := T147_34
  T2 := Q2.T147_34_2
  h1 := (1,4,3,3,1)
  h2 := (1,4,3,3,1)
  D := [[1, 4, 3, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_35_0 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨35, by decide⟩
  m := 1
  T1 := T147_35
  T2 := Q2.T147_35_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_35_1 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨35, by decide⟩
  m := 1
  T1 := T147_35
  T2 := Q2.T147_35_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_35_2 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨35, by decide⟩
  m := 1
  T1 := T147_35
  T2 := Q2.T147_35_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

end LeanDring.P5Presentation
