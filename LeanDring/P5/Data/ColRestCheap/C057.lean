/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.Twin1.ColCert
import LeanDring.P5.Data.EntryK.C031
import LeanDring.P5.Data.EntryK.C032

/-!
# Species-table cell data, stage 2 — twin-coincident columns (cheap tier)

Per-column certified exponent-vector data (`ColCert`/`ColCertDiv`) with kernel
`decide` bindings. Emitted; the embedded lists are what the kernel certifies.
rest tier, chunk 56: 60 columns.
-/

-- machine-emitted data: silence style linters (generated long lines, file-level options)
set_option linter.style.longLine false

namespace LeanDring.P5Presentation

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

def colCert_125_125_14 : ColCert where
  rK := ⟨125, by decide⟩
  rH := ⟨125, by decide⟩
  m := 5
  T1 := T125_125
  T2 := Q2.T125_125_2
  h1 := (2,4,2,0,0)
  h2 := (2,4,2,0,0)
  D := [[2, 4, 2, 4], [2, 4, 2, 0], [2, 4, 2, 1], [2, 4, 2, 2], [2, 4, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_125_125_15 : ColCert where
  rK := ⟨125, by decide⟩
  rH := ⟨125, by decide⟩
  m := 5
  T1 := T125_125
  T2 := Q2.T125_125_2
  h1 := (3,0,2,0,3)
  h2 := (3,0,2,0,3)
  D := [[3, 0, 0, 0], [3, 0, 0, 0], [3, 0, 0, 0], [3, 0, 0, 0], [3, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_125_125_16 : ColCert where
  rK := ⟨125, by decide⟩
  rH := ⟨125, by decide⟩
  m := 5
  T1 := T125_125
  T2 := Q2.T125_125_2
  h1 := (3,1,3,0,0)
  h2 := (3,1,3,0,0)
  D := [[3, 1, 2, 3], [3, 1, 2, 2], [3, 1, 2, 1], [3, 1, 2, 0], [3, 1, 2, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_125_125_17 : ColCert where
  rK := ⟨125, by decide⟩
  rH := ⟨125, by decide⟩
  m := 5
  T1 := T125_125
  T2 := Q2.T125_125_2
  h1 := (3,2,4,0,3)
  h2 := (3,2,4,0,3)
  D := [[3, 2, 4, 1], [3, 2, 4, 4], [3, 2, 4, 2], [3, 2, 4, 0], [3, 2, 4, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_125_125_18 : ColCert where
  rK := ⟨125, by decide⟩
  rH := ⟨125, by decide⟩
  m := 5
  T1 := T125_125
  T2 := Q2.T125_125_2
  h1 := (3,3,0,0,2)
  h2 := (3,3,0,0,2)
  D := [[3, 3, 1, 4], [3, 3, 1, 1], [3, 3, 1, 3], [3, 3, 1, 0], [3, 3, 1, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_125_125_19 : ColCert where
  rK := ⟨125, by decide⟩
  rH := ⟨125, by decide⟩
  m := 5
  T1 := T125_125
  T2 := Q2.T125_125_2
  h1 := (3,4,1,0,2)
  h2 := (3,4,1,0,2)
  D := [[3, 4, 3, 2], [3, 4, 3, 3], [3, 4, 3, 4], [3, 4, 3, 0], [3, 4, 3, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_125_125_20 : ColCert where
  rK := ⟨125, by decide⟩
  rH := ⟨125, by decide⟩
  m := 5
  T1 := T125_125
  T2 := Q2.T125_125_2
  h1 := (4,0,1,0,4)
  h2 := (4,0,1,0,4)
  D := [[4, 0, 0, 0], [4, 0, 0, 0], [4, 0, 0, 0], [4, 0, 0, 0], [4, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_125_125_21 : ColCert where
  rK := ⟨125, by decide⟩
  rH := ⟨125, by decide⟩
  m := 5
  T1 := T125_125
  T2 := Q2.T125_125_2
  h1 := (4,1,2,0,0)
  h2 := (4,1,2,0,0)
  D := [[4, 1, 1, 1], [4, 1, 1, 0], [4, 1, 1, 4], [4, 1, 1, 3], [4, 1, 1, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_125_125_22 : ColCert where
  rK := ⟨125, by decide⟩
  rH := ⟨125, by decide⟩
  m := 5
  T1 := T125_125
  T2 := Q2.T125_125_2
  h1 := (4,2,3,0,2)
  h2 := (4,2,3,0,2)
  D := [[4, 2, 2, 2], [4, 2, 2, 0], [4, 2, 2, 3], [4, 2, 2, 1], [4, 2, 2, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_125_125_23 : ColCert where
  rK := ⟨125, by decide⟩
  rH := ⟨125, by decide⟩
  m := 5
  T1 := T125_125
  T2 := Q2.T125_125_2
  h1 := (4,3,4,0,0)
  h2 := (4,3,4,0,0)
  D := [[4, 3, 3, 3], [4, 3, 3, 0], [4, 3, 3, 2], [4, 3, 3, 4], [4, 3, 3, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_125_125_24 : ColCert where
  rK := ⟨125, by decide⟩
  rH := ⟨125, by decide⟩
  m := 5
  T1 := T125_125
  T2 := Q2.T125_125_2
  h1 := (4,4,0,0,4)
  h2 := (4,4,0,0,4)
  D := [[4, 4, 4, 4], [4, 4, 4, 0], [4, 4, 4, 1], [4, 4, 4, 2], [4, 4, 4, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_126_0_0 : ColCert where
  rK := ⟨126, by decide⟩
  rH := ⟨0, by decide⟩
  m := 5
  T1 := T126_0
  T2 := Q2.T126_0_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_126_3_0 : ColCert where
  rK := ⟨126, by decide⟩
  rH := ⟨3, by decide⟩
  m := 5
  T1 := T126_3
  T2 := Q2.T126_3_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_126_3_1 : ColCert where
  rK := ⟨126, by decide⟩
  rH := ⟨3, by decide⟩
  m := 5
  T1 := T126_3
  T2 := Q2.T126_3_2
  h1 := (1,0,2,3,1)
  h2 := (1,0,2,3,1)
  D := [[1, 0, 3, 3], [1, 0, 3, 3], [1, 0, 3, 3], [1, 0, 3, 3], [1, 0, 3, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_126_3_2 : ColCert where
  rK := ⟨126, by decide⟩
  rH := ⟨3, by decide⟩
  m := 5
  T1 := T126_3
  T2 := Q2.T126_3_2
  h1 := (2,0,4,1,0)
  h2 := (2,0,4,1,0)
  D := [[2, 0, 1, 3], [2, 0, 1, 3], [2, 0, 1, 3], [2, 0, 1, 3], [2, 0, 1, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_126_3_3 : ColCert where
  rK := ⟨126, by decide⟩
  rH := ⟨3, by decide⟩
  m := 5
  T1 := T126_3
  T2 := Q2.T126_3_2
  h1 := (3,0,1,4,2)
  h2 := (3,0,1,4,2)
  D := [[3, 0, 4, 0], [3, 0, 4, 0], [3, 0, 4, 0], [3, 0, 4, 0], [3, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_126_3_4 : ColCert where
  rK := ⟨126, by decide⟩
  rH := ⟨3, by decide⟩
  m := 5
  T1 := T126_3
  T2 := Q2.T126_3_2
  h1 := (4,0,3,2,2)
  h2 := (4,0,3,2,2)
  D := [[4, 0, 2, 4], [4, 0, 2, 4], [4, 0, 2, 4], [4, 0, 2, 4], [4, 0, 2, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_126_10_0 : ColCert where
  rK := ⟨126, by decide⟩
  rH := ⟨10, by decide⟩
  m := 5
  T1 := T126_10
  T2 := Q2.T126_10_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_126_10_1 : ColCert where
  rK := ⟨126, by decide⟩
  rH := ⟨10, by decide⟩
  m := 5
  T1 := T126_10
  T2 := Q2.T126_10_2
  h1 := (0,0,0,1,4)
  h2 := (0,0,0,1,4)
  D := [[0, 0, 1, 4], [0, 0, 1, 4], [0, 0, 1, 4], [0, 0, 1, 4], [0, 0, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_126_10_2 : ColCert where
  rK := ⟨126, by decide⟩
  rH := ⟨10, by decide⟩
  m := 5
  T1 := T126_10
  T2 := Q2.T126_10_2
  h1 := (0,0,0,2,3)
  h2 := (0,0,0,2,3)
  D := [[0, 0, 2, 3], [0, 0, 2, 3], [0, 0, 2, 3], [0, 0, 2, 3], [0, 0, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_126_10_3 : ColCert where
  rK := ⟨126, by decide⟩
  rH := ⟨10, by decide⟩
  m := 5
  T1 := T126_10
  T2 := Q2.T126_10_2
  h1 := (0,0,0,3,2)
  h2 := (0,0,0,3,2)
  D := [[0, 0, 3, 2], [0, 0, 3, 2], [0, 0, 3, 2], [0, 0, 3, 2], [0, 0, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_126_10_4 : ColCert where
  rK := ⟨126, by decide⟩
  rH := ⟨10, by decide⟩
  m := 5
  T1 := T126_10
  T2 := Q2.T126_10_2
  h1 := (0,0,0,4,1)
  h2 := (0,0,0,4,1)
  D := [[0, 0, 4, 1], [0, 0, 4, 1], [0, 0, 4, 1], [0, 0, 4, 1], [0, 0, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_126_12_0 : ColCert where
  rK := ⟨126, by decide⟩
  rH := ⟨12, by decide⟩
  m := 5
  T1 := T126_12
  T2 := Q2.T126_12_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_126_12_1 : ColCert where
  rK := ⟨126, by decide⟩
  rH := ⟨12, by decide⟩
  m := 5
  T1 := T126_12
  T2 := Q2.T126_12_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_126_12_2 : ColCert where
  rK := ⟨126, by decide⟩
  rH := ⟨12, by decide⟩
  m := 5
  T1 := T126_12
  T2 := Q2.T126_12_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_126_12_3 : ColCert where
  rK := ⟨126, by decide⟩
  rH := ⟨12, by decide⟩
  m := 5
  T1 := T126_12
  T2 := Q2.T126_12_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_126_12_4 : ColCert where
  rK := ⟨126, by decide⟩
  rH := ⟨12, by decide⟩
  m := 5
  T1 := T126_12
  T2 := Q2.T126_12_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_126_21_0 : ColCert where
  rK := ⟨126, by decide⟩
  rH := ⟨21, by decide⟩
  m := 5
  T1 := T126_21
  T2 := Q2.T126_21_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_126_21_1 : ColCert where
  rK := ⟨126, by decide⟩
  rH := ⟨21, by decide⟩
  m := 5
  T1 := T126_21
  T2 := Q2.T126_21_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_126_21_2 : ColCert where
  rK := ⟨126, by decide⟩
  rH := ⟨21, by decide⟩
  m := 5
  T1 := T126_21
  T2 := Q2.T126_21_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_126_21_3 : ColCert where
  rK := ⟨126, by decide⟩
  rH := ⟨21, by decide⟩
  m := 5
  T1 := T126_21
  T2 := Q2.T126_21_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_126_21_4 : ColCert where
  rK := ⟨126, by decide⟩
  rH := ⟨21, by decide⟩
  m := 5
  T1 := T126_21
  T2 := Q2.T126_21_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_126_21_5 : ColCert where
  rK := ⟨126, by decide⟩
  rH := ⟨21, by decide⟩
  m := 5
  T1 := T126_21
  T2 := Q2.T126_21_2
  h1 := (1,0,2,3,2)
  h2 := (1,0,2,3,2)
  D := [[1, 0, 3, 4], [1, 0, 3, 4], [1, 0, 3, 4], [1, 0, 3, 4], [1, 0, 3, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_126_21_10 : ColCert where
  rK := ⟨126, by decide⟩
  rH := ⟨21, by decide⟩
  m := 5
  T1 := T126_21
  T2 := Q2.T126_21_2
  h1 := (2,0,4,1,2)
  h2 := (2,0,4,1,2)
  D := [[2, 0, 1, 0], [2, 0, 1, 0], [2, 0, 1, 0], [2, 0, 1, 0], [2, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_126_21_15 : ColCert where
  rK := ⟨126, by decide⟩
  rH := ⟨21, by decide⟩
  m := 5
  T1 := T126_21
  T2 := Q2.T126_21_2
  h1 := (3,0,1,4,0)
  h2 := (3,0,1,4,0)
  D := [[3, 0, 4, 3], [3, 0, 4, 3], [3, 0, 4, 3], [3, 0, 4, 3], [3, 0, 4, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_126_21_20 : ColCert where
  rK := ⟨126, by decide⟩
  rH := ⟨21, by decide⟩
  m := 5
  T1 := T126_21
  T2 := Q2.T126_21_2
  h1 := (4,0,3,2,1)
  h2 := (4,0,3,2,1)
  D := [[4, 0, 2, 3], [4, 0, 2, 3], [4, 0, 2, 3], [4, 0, 2, 3], [4, 0, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_126_31_0 : ColCert where
  rK := ⟨126, by decide⟩
  rH := ⟨31, by decide⟩
  m := 5
  T1 := T126_31
  T2 := Q2.T126_31_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_126_31_1 : ColCert where
  rK := ⟨126, by decide⟩
  rH := ⟨31, by decide⟩
  m := 5
  T1 := T126_31
  T2 := Q2.T126_31_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_126_31_2 : ColCert where
  rK := ⟨126, by decide⟩
  rH := ⟨31, by decide⟩
  m := 5
  T1 := T126_31
  T2 := Q2.T126_31_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_126_31_3 : ColCert where
  rK := ⟨126, by decide⟩
  rH := ⟨31, by decide⟩
  m := 5
  T1 := T126_31
  T2 := Q2.T126_31_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_126_31_4 : ColCert where
  rK := ⟨126, by decide⟩
  rH := ⟨31, by decide⟩
  m := 5
  T1 := T126_31
  T2 := Q2.T126_31_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_126_37_0 : ColCert where
  rK := ⟨126, by decide⟩
  rH := ⟨37, by decide⟩
  m := 5
  T1 := T126_37
  T2 := Q2.T126_37_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_126_37_1 : ColCert where
  rK := ⟨126, by decide⟩
  rH := ⟨37, by decide⟩
  m := 5
  T1 := T126_37
  T2 := Q2.T126_37_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_126_37_2 : ColCert where
  rK := ⟨126, by decide⟩
  rH := ⟨37, by decide⟩
  m := 5
  T1 := T126_37
  T2 := Q2.T126_37_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_126_37_3 : ColCert where
  rK := ⟨126, by decide⟩
  rH := ⟨37, by decide⟩
  m := 5
  T1 := T126_37
  T2 := Q2.T126_37_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_126_37_4 : ColCert where
  rK := ⟨126, by decide⟩
  rH := ⟨37, by decide⟩
  m := 5
  T1 := T126_37
  T2 := Q2.T126_37_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_126_39_0 : ColCert where
  rK := ⟨126, by decide⟩
  rH := ⟨39, by decide⟩
  m := 5
  T1 := T126_39
  T2 := Q2.T126_39_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_126_39_1 : ColCert where
  rK := ⟨126, by decide⟩
  rH := ⟨39, by decide⟩
  m := 5
  T1 := T126_39
  T2 := Q2.T126_39_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_126_39_2 : ColCert where
  rK := ⟨126, by decide⟩
  rH := ⟨39, by decide⟩
  m := 5
  T1 := T126_39
  T2 := Q2.T126_39_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_126_39_3 : ColCert where
  rK := ⟨126, by decide⟩
  rH := ⟨39, by decide⟩
  m := 5
  T1 := T126_39
  T2 := Q2.T126_39_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_126_39_4 : ColCert where
  rK := ⟨126, by decide⟩
  rH := ⟨39, by decide⟩
  m := 5
  T1 := T126_39
  T2 := Q2.T126_39_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_126_39_5 : ColCert where
  rK := ⟨126, by decide⟩
  rH := ⟨39, by decide⟩
  m := 5
  T1 := T126_39
  T2 := Q2.T126_39_2
  h1 := (1,4,2,3,2)
  h2 := (1,4,2,3,2)
  D := [[1, 4, 4, 0], [1, 4, 4, 1], [1, 4, 4, 2], [1, 4, 4, 3], [1, 4, 4, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_126_45_0 : ColCert where
  rK := ⟨126, by decide⟩
  rH := ⟨45, by decide⟩
  m := 5
  T1 := T126_45
  T2 := Q2.T126_45_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_126_45_1 : ColCert where
  rK := ⟨126, by decide⟩
  rH := ⟨45, by decide⟩
  m := 5
  T1 := T126_45
  T2 := Q2.T126_45_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_126_45_2 : ColCert where
  rK := ⟨126, by decide⟩
  rH := ⟨45, by decide⟩
  m := 5
  T1 := T126_45
  T2 := Q2.T126_45_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_126_45_3 : ColCert where
  rK := ⟨126, by decide⟩
  rH := ⟨45, by decide⟩
  m := 5
  T1 := T126_45
  T2 := Q2.T126_45_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_126_45_4 : ColCert where
  rK := ⟨126, by decide⟩
  rH := ⟨45, by decide⟩
  m := 5
  T1 := T126_45
  T2 := Q2.T126_45_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_126_48_0 : ColCert where
  rK := ⟨126, by decide⟩
  rH := ⟨48, by decide⟩
  m := 5
  T1 := T126_48
  T2 := Q2.T126_48_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_126_48_1 : ColCert where
  rK := ⟨126, by decide⟩
  rH := ⟨48, by decide⟩
  m := 5
  T1 := T126_48
  T2 := Q2.T126_48_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_126_48_2 : ColCert where
  rK := ⟨126, by decide⟩
  rH := ⟨48, by decide⟩
  m := 5
  T1 := T126_48
  T2 := Q2.T126_48_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

end LeanDring.P5Presentation
