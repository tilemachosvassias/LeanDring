/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.Twin1.ColCert
import LeanDring.P5.Data.EntryK.C031

/-!
# Species-table cell data, stage 2 — twin-coincident columns (cheap tier)

Per-column certified exponent-vector data (`ColCert`/`ColCertDiv`) with kernel
`decide` bindings. Emitted; the embedded lists are what the kernel certifies.
rest tier, chunk 54: 60 columns.
-/

-- machine-emitted data: silence style linters (generated long lines, file-level options)
set_option linter.style.longLine false

namespace LeanDring.P5Presentation

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

def colCert_125_2_3 : ColCert where
  rK := ⟨125, by decide⟩
  rH := ⟨2, by decide⟩
  m := 5
  T1 := T125_2
  T2 := Q2.T125_2_2
  h1 := (3,0,2,3,3)
  h2 := (3,0,2,3,3)
  D := [[3, 0, 3, 1], [3, 0, 3, 1], [3, 0, 3, 1], [3, 0, 3, 1], [3, 0, 3, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_125_2_4 : ColCert where
  rK := ⟨125, by decide⟩
  rH := ⟨2, by decide⟩
  m := 5
  T1 := T125_2
  T2 := Q2.T125_2_2
  h1 := (4,0,1,4,1)
  h2 := (4,0,1,4,1)
  D := [[4, 0, 4, 1], [4, 0, 4, 1], [4, 0, 4, 1], [4, 0, 4, 1], [4, 0, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_125_10_0 : ColCert where
  rK := ⟨125, by decide⟩
  rH := ⟨10, by decide⟩
  m := 5
  T1 := T125_10
  T2 := Q2.T125_10_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_125_10_1 : ColCert where
  rK := ⟨125, by decide⟩
  rH := ⟨10, by decide⟩
  m := 5
  T1 := T125_10
  T2 := Q2.T125_10_2
  h1 := (0,0,0,1,4)
  h2 := (0,0,0,1,4)
  D := [[0, 0, 1, 4], [0, 0, 1, 4], [0, 0, 1, 4], [0, 0, 1, 4], [0, 0, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_125_10_2 : ColCert where
  rK := ⟨125, by decide⟩
  rH := ⟨10, by decide⟩
  m := 5
  T1 := T125_10
  T2 := Q2.T125_10_2
  h1 := (0,0,0,2,3)
  h2 := (0,0,0,2,3)
  D := [[0, 0, 2, 3], [0, 0, 2, 3], [0, 0, 2, 3], [0, 0, 2, 3], [0, 0, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_125_10_3 : ColCert where
  rK := ⟨125, by decide⟩
  rH := ⟨10, by decide⟩
  m := 5
  T1 := T125_10
  T2 := Q2.T125_10_2
  h1 := (0,0,0,3,2)
  h2 := (0,0,0,3,2)
  D := [[0, 0, 3, 2], [0, 0, 3, 2], [0, 0, 3, 2], [0, 0, 3, 2], [0, 0, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_125_10_4 : ColCert where
  rK := ⟨125, by decide⟩
  rH := ⟨10, by decide⟩
  m := 5
  T1 := T125_10
  T2 := Q2.T125_10_2
  h1 := (0,0,0,4,1)
  h2 := (0,0,0,4,1)
  D := [[0, 0, 4, 1], [0, 0, 4, 1], [0, 0, 4, 1], [0, 0, 4, 1], [0, 0, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_125_12_0 : ColCert where
  rK := ⟨125, by decide⟩
  rH := ⟨12, by decide⟩
  m := 5
  T1 := T125_12
  T2 := Q2.T125_12_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_125_12_1 : ColCert where
  rK := ⟨125, by decide⟩
  rH := ⟨12, by decide⟩
  m := 5
  T1 := T125_12
  T2 := Q2.T125_12_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_125_12_2 : ColCert where
  rK := ⟨125, by decide⟩
  rH := ⟨12, by decide⟩
  m := 5
  T1 := T125_12
  T2 := Q2.T125_12_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_125_12_3 : ColCert where
  rK := ⟨125, by decide⟩
  rH := ⟨12, by decide⟩
  m := 5
  T1 := T125_12
  T2 := Q2.T125_12_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_125_12_4 : ColCert where
  rK := ⟨125, by decide⟩
  rH := ⟨12, by decide⟩
  m := 5
  T1 := T125_12
  T2 := Q2.T125_12_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_125_20_0 : ColCert where
  rK := ⟨125, by decide⟩
  rH := ⟨20, by decide⟩
  m := 5
  T1 := T125_20
  T2 := Q2.T125_20_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_125_20_1 : ColCert where
  rK := ⟨125, by decide⟩
  rH := ⟨20, by decide⟩
  m := 5
  T1 := T125_20
  T2 := Q2.T125_20_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_125_20_2 : ColCert where
  rK := ⟨125, by decide⟩
  rH := ⟨20, by decide⟩
  m := 5
  T1 := T125_20
  T2 := Q2.T125_20_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_125_20_3 : ColCert where
  rK := ⟨125, by decide⟩
  rH := ⟨20, by decide⟩
  m := 5
  T1 := T125_20
  T2 := Q2.T125_20_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_125_20_4 : ColCert where
  rK := ⟨125, by decide⟩
  rH := ⟨20, by decide⟩
  m := 5
  T1 := T125_20
  T2 := Q2.T125_20_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_125_20_5 : ColCert where
  rK := ⟨125, by decide⟩
  rH := ⟨20, by decide⟩
  m := 5
  T1 := T125_20
  T2 := Q2.T125_20_2
  h1 := (1,0,4,1,1)
  h2 := (1,0,4,1,1)
  D := [[1, 0, 1, 4], [1, 0, 1, 4], [1, 0, 1, 4], [1, 0, 1, 4], [1, 0, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_125_20_10 : ColCert where
  rK := ⟨125, by decide⟩
  rH := ⟨20, by decide⟩
  m := 5
  T1 := T125_20
  T2 := Q2.T125_20_2
  h1 := (2,0,3,2,3)
  h2 := (2,0,3,2,3)
  D := [[2, 0, 2, 2], [2, 0, 2, 2], [2, 0, 2, 2], [2, 0, 2, 2], [2, 0, 2, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_125_20_15 : ColCert where
  rK := ⟨125, by decide⟩
  rH := ⟨20, by decide⟩
  m := 5
  T1 := T125_20
  T2 := Q2.T125_20_2
  h1 := (3,0,2,3,1)
  h2 := (3,0,2,3,1)
  D := [[3, 0, 3, 4], [3, 0, 3, 4], [3, 0, 3, 4], [3, 0, 3, 4], [3, 0, 3, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_125_20_20 : ColCert where
  rK := ⟨125, by decide⟩
  rH := ⟨20, by decide⟩
  m := 5
  T1 := T125_20
  T2 := Q2.T125_20_2
  h1 := (4,0,1,4,0)
  h2 := (4,0,1,4,0)
  D := [[4, 0, 4, 0], [4, 0, 4, 0], [4, 0, 4, 0], [4, 0, 4, 0], [4, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_125_31_0 : ColCert where
  rK := ⟨125, by decide⟩
  rH := ⟨31, by decide⟩
  m := 5
  T1 := T125_31
  T2 := Q2.T125_31_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_125_31_1 : ColCert where
  rK := ⟨125, by decide⟩
  rH := ⟨31, by decide⟩
  m := 5
  T1 := T125_31
  T2 := Q2.T125_31_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_125_31_2 : ColCert where
  rK := ⟨125, by decide⟩
  rH := ⟨31, by decide⟩
  m := 5
  T1 := T125_31
  T2 := Q2.T125_31_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_125_31_3 : ColCert where
  rK := ⟨125, by decide⟩
  rH := ⟨31, by decide⟩
  m := 5
  T1 := T125_31
  T2 := Q2.T125_31_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_125_31_4 : ColCert where
  rK := ⟨125, by decide⟩
  rH := ⟨31, by decide⟩
  m := 5
  T1 := T125_31
  T2 := Q2.T125_31_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_125_34_0 : ColCert where
  rK := ⟨125, by decide⟩
  rH := ⟨34, by decide⟩
  m := 5
  T1 := T125_34
  T2 := Q2.T125_34_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_125_34_1 : ColCert where
  rK := ⟨125, by decide⟩
  rH := ⟨34, by decide⟩
  m := 5
  T1 := T125_34
  T2 := Q2.T125_34_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_125_34_2 : ColCert where
  rK := ⟨125, by decide⟩
  rH := ⟨34, by decide⟩
  m := 5
  T1 := T125_34
  T2 := Q2.T125_34_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_125_34_3 : ColCert where
  rK := ⟨125, by decide⟩
  rH := ⟨34, by decide⟩
  m := 5
  T1 := T125_34
  T2 := Q2.T125_34_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_125_34_4 : ColCert where
  rK := ⟨125, by decide⟩
  rH := ⟨34, by decide⟩
  m := 5
  T1 := T125_34
  T2 := Q2.T125_34_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_125_34_5 : ColCert where
  rK := ⟨125, by decide⟩
  rH := ⟨34, by decide⟩
  m := 5
  T1 := T125_34
  T2 := Q2.T125_34_2
  h1 := (1,4,3,3,1)
  h2 := (1,4,3,3,1)
  D := [[1, 4, 4, 0], [1, 4, 4, 1], [1, 4, 4, 2], [1, 4, 4, 3], [1, 4, 4, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_125_40_0 : ColCert where
  rK := ⟨125, by decide⟩
  rH := ⟨40, by decide⟩
  m := 5
  T1 := T125_40
  T2 := Q2.T125_40_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_125_40_1 : ColCert where
  rK := ⟨125, by decide⟩
  rH := ⟨40, by decide⟩
  m := 5
  T1 := T125_40
  T2 := Q2.T125_40_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_125_40_2 : ColCert where
  rK := ⟨125, by decide⟩
  rH := ⟨40, by decide⟩
  m := 5
  T1 := T125_40
  T2 := Q2.T125_40_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_125_40_3 : ColCert where
  rK := ⟨125, by decide⟩
  rH := ⟨40, by decide⟩
  m := 5
  T1 := T125_40
  T2 := Q2.T125_40_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_125_40_4 : ColCert where
  rK := ⟨125, by decide⟩
  rH := ⟨40, by decide⟩
  m := 5
  T1 := T125_40
  T2 := Q2.T125_40_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_125_43_0 : ColCert where
  rK := ⟨125, by decide⟩
  rH := ⟨43, by decide⟩
  m := 5
  T1 := T125_43
  T2 := Q2.T125_43_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_125_43_1 : ColCert where
  rK := ⟨125, by decide⟩
  rH := ⟨43, by decide⟩
  m := 5
  T1 := T125_43
  T2 := Q2.T125_43_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_125_43_2 : ColCert where
  rK := ⟨125, by decide⟩
  rH := ⟨43, by decide⟩
  m := 5
  T1 := T125_43
  T2 := Q2.T125_43_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_125_43_3 : ColCert where
  rK := ⟨125, by decide⟩
  rH := ⟨43, by decide⟩
  m := 5
  T1 := T125_43
  T2 := Q2.T125_43_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_125_43_4 : ColCert where
  rK := ⟨125, by decide⟩
  rH := ⟨43, by decide⟩
  m := 5
  T1 := T125_43
  T2 := Q2.T125_43_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_125_52_0 : ColCert where
  rK := ⟨125, by decide⟩
  rH := ⟨52, by decide⟩
  m := 5
  T1 := T125_52
  T2 := Q2.T125_52_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_125_52_1 : ColCert where
  rK := ⟨125, by decide⟩
  rH := ⟨52, by decide⟩
  m := 5
  T1 := T125_52
  T2 := Q2.T125_52_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_125_52_2 : ColCert where
  rK := ⟨125, by decide⟩
  rH := ⟨52, by decide⟩
  m := 5
  T1 := T125_52
  T2 := Q2.T125_52_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_125_52_3 : ColCert where
  rK := ⟨125, by decide⟩
  rH := ⟨52, by decide⟩
  m := 5
  T1 := T125_52
  T2 := Q2.T125_52_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_125_52_4 : ColCert where
  rK := ⟨125, by decide⟩
  rH := ⟨52, by decide⟩
  m := 5
  T1 := T125_52
  T2 := Q2.T125_52_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_125_53_0 : ColCert where
  rK := ⟨125, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T125_53
  T2 := Q2.T125_53_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_125_53_1 : ColCert where
  rK := ⟨125, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T125_53
  T2 := Q2.T125_53_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_125_53_2 : ColCert where
  rK := ⟨125, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T125_53
  T2 := Q2.T125_53_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_125_53_3 : ColCert where
  rK := ⟨125, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T125_53
  T2 := Q2.T125_53_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_125_53_4 : ColCert where
  rK := ⟨125, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T125_53
  T2 := Q2.T125_53_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_125_53_5 : ColCert where
  rK := ⟨125, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T125_53
  T2 := Q2.T125_53_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_125_53_10 : ColCert where
  rK := ⟨125, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T125_53
  T2 := Q2.T125_53_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_125_53_15 : ColCert where
  rK := ⟨125, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T125_53
  T2 := Q2.T125_53_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_125_53_20 : ColCert where
  rK := ⟨125, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T125_53
  T2 := Q2.T125_53_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_125_81_0 : ColCert where
  rK := ⟨125, by decide⟩
  rH := ⟨81, by decide⟩
  m := 5
  T1 := T125_81
  T2 := Q2.T125_81_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_125_81_1 : ColCert where
  rK := ⟨125, by decide⟩
  rH := ⟨81, by decide⟩
  m := 5
  T1 := T125_81
  T2 := Q2.T125_81_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_125_81_2 : ColCert where
  rK := ⟨125, by decide⟩
  rH := ⟨81, by decide⟩
  m := 5
  T1 := T125_81
  T2 := Q2.T125_81_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_125_81_3 : ColCert where
  rK := ⟨125, by decide⟩
  rH := ⟨81, by decide⟩
  m := 5
  T1 := T125_81
  T2 := Q2.T125_81_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

end LeanDring.P5Presentation
