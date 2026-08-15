/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.Twin1.ColCert
import LeanDring.P5.Data.EntryK.C021

/-!
# Species-table cell data, stage 2 — twin-coincident columns (cheap tier)

Per-column certified exponent-vector data (`ColCert`/`ColCertDiv`) with kernel
`decide` bindings. Emitted; the embedded lists are what the kernel certifies.
rest tier, chunk 189: 60 columns.
-/

-- machine-emitted data: silence style linters (generated long lines, file-level options)
set_option linter.style.longLine false

namespace LeanDring.P5Presentation

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

def colCert_89_21_0 : ColCert where
  rK := ⟨89, by decide⟩
  rH := ⟨21, by decide⟩
  m := 5
  T1 := T89_21
  T2 := Q2.T89_21_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_89_21_1 : ColCert where
  rK := ⟨89, by decide⟩
  rH := ⟨21, by decide⟩
  m := 5
  T1 := T89_21
  T2 := Q2.T89_21_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_89_21_2 : ColCert where
  rK := ⟨89, by decide⟩
  rH := ⟨21, by decide⟩
  m := 5
  T1 := T89_21
  T2 := Q2.T89_21_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_89_21_3 : ColCert where
  rK := ⟨89, by decide⟩
  rH := ⟨21, by decide⟩
  m := 5
  T1 := T89_21
  T2 := Q2.T89_21_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_89_21_4 : ColCert where
  rK := ⟨89, by decide⟩
  rH := ⟨21, by decide⟩
  m := 5
  T1 := T89_21
  T2 := Q2.T89_21_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_89_21_5 : ColCert where
  rK := ⟨89, by decide⟩
  rH := ⟨21, by decide⟩
  m := 5
  T1 := T89_21
  T2 := Q2.T89_21_2
  h1 := (1,0,2,3,2)
  h2 := (1,0,2,3,2)
  D := [[1, 2, 2], [1, 2, 1], [1, 2, 0], [1, 2, 4], [1, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_89_21_10 : ColCert where
  rK := ⟨89, by decide⟩
  rH := ⟨21, by decide⟩
  m := 5
  T1 := T89_21
  T2 := Q2.T89_21_2
  h1 := (2,0,4,1,2)
  h2 := (2,0,4,1,2)
  D := [[2, 4, 2], [2, 4, 0], [2, 4, 3], [2, 4, 1], [2, 4, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_89_21_15 : ColCert where
  rK := ⟨89, by decide⟩
  rH := ⟨21, by decide⟩
  m := 5
  T1 := T89_21
  T2 := Q2.T89_21_2
  h1 := (3,0,1,4,0)
  h2 := (3,0,1,4,0)
  D := [[3, 1, 0], [3, 1, 2], [3, 1, 4], [3, 1, 1], [3, 1, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_89_21_20 : ColCert where
  rK := ⟨89, by decide⟩
  rH := ⟨21, by decide⟩
  m := 5
  T1 := T89_21
  T2 := Q2.T89_21_2
  h1 := (4,0,3,2,1)
  h2 := (4,0,3,2,1)
  D := [[4, 3, 1], [4, 3, 2], [4, 3, 3], [4, 3, 4], [4, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_89_22_0 : ColCert where
  rK := ⟨89, by decide⟩
  rH := ⟨22, by decide⟩
  m := 5
  T1 := T89_22
  T2 := Q2.T89_22_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_89_22_1 : ColCert where
  rK := ⟨89, by decide⟩
  rH := ⟨22, by decide⟩
  m := 5
  T1 := T89_22
  T2 := Q2.T89_22_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_89_22_2 : ColCert where
  rK := ⟨89, by decide⟩
  rH := ⟨22, by decide⟩
  m := 5
  T1 := T89_22
  T2 := Q2.T89_22_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_89_22_3 : ColCert where
  rK := ⟨89, by decide⟩
  rH := ⟨22, by decide⟩
  m := 5
  T1 := T89_22
  T2 := Q2.T89_22_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_89_22_4 : ColCert where
  rK := ⟨89, by decide⟩
  rH := ⟨22, by decide⟩
  m := 5
  T1 := T89_22
  T2 := Q2.T89_22_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_89_22_5 : ColCert where
  rK := ⟨89, by decide⟩
  rH := ⟨22, by decide⟩
  m := 5
  T1 := T89_22
  T2 := Q2.T89_22_2
  h1 := (1,0,3,2,4)
  h2 := (1,0,3,2,4)
  D := [[1, 3, 1], [1, 3, 0], [1, 3, 4], [1, 3, 3], [1, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_89_22_10 : ColCert where
  rK := ⟨89, by decide⟩
  rH := ⟨22, by decide⟩
  m := 5
  T1 := T89_22
  T2 := Q2.T89_22_2
  h1 := (2,0,1,4,0)
  h2 := (2,0,1,4,0)
  D := [[2, 1, 4], [2, 1, 2], [2, 1, 0], [2, 1, 3], [2, 1, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_89_22_15 : ColCert where
  rK := ⟨89, by decide⟩
  rH := ⟨22, by decide⟩
  m := 5
  T1 := T89_22
  T2 := Q2.T89_22_2
  h1 := (3,0,4,1,3)
  h2 := (3,0,4,1,3)
  D := [[3, 4, 4], [3, 4, 1], [3, 4, 3], [3, 4, 0], [3, 4, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_89_22_20 : ColCert where
  rK := ⟨89, by decide⟩
  rH := ⟨22, by decide⟩
  m := 5
  T1 := T89_22
  T2 := Q2.T89_22_2
  h1 := (4,0,2,3,3)
  h2 := (4,0,2,3,3)
  D := [[4, 2, 1], [4, 2, 2], [4, 2, 3], [4, 2, 4], [4, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_89_23_0 : ColCert where
  rK := ⟨89, by decide⟩
  rH := ⟨23, by decide⟩
  m := 5
  T1 := T89_23
  T2 := Q2.T89_23_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_89_23_1 : ColCert where
  rK := ⟨89, by decide⟩
  rH := ⟨23, by decide⟩
  m := 5
  T1 := T89_23
  T2 := Q2.T89_23_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_89_23_2 : ColCert where
  rK := ⟨89, by decide⟩
  rH := ⟨23, by decide⟩
  m := 5
  T1 := T89_23
  T2 := Q2.T89_23_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_89_23_3 : ColCert where
  rK := ⟨89, by decide⟩
  rH := ⟨23, by decide⟩
  m := 5
  T1 := T89_23
  T2 := Q2.T89_23_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_89_23_4 : ColCert where
  rK := ⟨89, by decide⟩
  rH := ⟨23, by decide⟩
  m := 5
  T1 := T89_23
  T2 := Q2.T89_23_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_89_23_5 : ColCert where
  rK := ⟨89, by decide⟩
  rH := ⟨23, by decide⟩
  m := 5
  T1 := T89_23
  T2 := Q2.T89_23_2
  h1 := (1,0,1,4,0)
  h2 := (1,0,1,4,0)
  D := [[1, 1, 4], [1, 1, 3], [1, 1, 2], [1, 1, 1], [1, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_89_23_10 : ColCert where
  rK := ⟨89, by decide⟩
  rH := ⟨23, by decide⟩
  m := 5
  T1 := T89_23
  T2 := Q2.T89_23_2
  h1 := (2,0,2,3,4)
  h2 := (2,0,2,3,4)
  D := [[2, 2, 2], [2, 2, 0], [2, 2, 3], [2, 2, 1], [2, 2, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_89_23_15 : ColCert where
  rK := ⟨89, by decide⟩
  rH := ⟨23, by decide⟩
  m := 5
  T1 := T89_23
  T2 := Q2.T89_23_2
  h1 := (3,0,3,2,2)
  h2 := (3,0,3,2,2)
  D := [[3, 3, 4], [3, 3, 1], [3, 3, 3], [3, 3, 0], [3, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_89_23_20 : ColCert where
  rK := ⟨89, by decide⟩
  rH := ⟨23, by decide⟩
  m := 5
  T1 := T89_23
  T2 := Q2.T89_23_2
  h1 := (4,0,4,1,4)
  h2 := (4,0,4,1,4)
  D := [[4, 4, 0], [4, 4, 1], [4, 4, 2], [4, 4, 3], [4, 4, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_89_26_0 : ColCert where
  rK := ⟨89, by decide⟩
  rH := ⟨26, by decide⟩
  m := 25
  T1 := T89_26
  T2 := Q2.T89_26_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_89_26_1 : ColCert where
  rK := ⟨89, by decide⟩
  rH := ⟨26, by decide⟩
  m := 25
  T1 := T89_26
  T2 := Q2.T89_26_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_89_26_2 : ColCert where
  rK := ⟨89, by decide⟩
  rH := ⟨26, by decide⟩
  m := 25
  T1 := T89_26
  T2 := Q2.T89_26_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_89_26_3 : ColCert where
  rK := ⟨89, by decide⟩
  rH := ⟨26, by decide⟩
  m := 25
  T1 := T89_26
  T2 := Q2.T89_26_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_89_26_4 : ColCert where
  rK := ⟨89, by decide⟩
  rH := ⟨26, by decide⟩
  m := 25
  T1 := T89_26
  T2 := Q2.T89_26_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_89_26_5 : ColCert where
  rK := ⟨89, by decide⟩
  rH := ⟨26, by decide⟩
  m := 25
  T1 := T89_26
  T2 := Q2.T89_26_2
  h1 := (0,0,1,1,0)
  h2 := (0,0,1,1,0)
  D := [[0, 1, 0], [0, 1, 0], [0, 1, 0], [0, 1, 0], [0, 1, 0], [0, 1, 1], [0, 1, 1], [0, 1, 1], [0, 1, 1], [0, 1, 1], [0, 1, 2], [0, 1, 2], [0, 1, 2], [0, 1, 2], [0, 1, 2], [0, 1, 3], [0, 1, 3], [0, 1, 3], [0, 1, 3], [0, 1, 3], [0, 1, 4], [0, 1, 4], [0, 1, 4], [0, 1, 4], [0, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_89_26_10 : ColCert where
  rK := ⟨89, by decide⟩
  rH := ⟨26, by decide⟩
  m := 25
  T1 := T89_26
  T2 := Q2.T89_26_2
  h1 := (0,0,2,2,0)
  h2 := (0,0,2,2,0)
  D := [[0, 2, 0], [0, 2, 0], [0, 2, 0], [0, 2, 0], [0, 2, 0], [0, 2, 2], [0, 2, 2], [0, 2, 2], [0, 2, 2], [0, 2, 2], [0, 2, 4], [0, 2, 4], [0, 2, 4], [0, 2, 4], [0, 2, 4], [0, 2, 1], [0, 2, 1], [0, 2, 1], [0, 2, 1], [0, 2, 1], [0, 2, 3], [0, 2, 3], [0, 2, 3], [0, 2, 3], [0, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_89_26_15 : ColCert where
  rK := ⟨89, by decide⟩
  rH := ⟨26, by decide⟩
  m := 25
  T1 := T89_26
  T2 := Q2.T89_26_2
  h1 := (0,0,3,3,0)
  h2 := (0,0,3,3,0)
  D := [[0, 3, 0], [0, 3, 0], [0, 3, 0], [0, 3, 0], [0, 3, 0], [0, 3, 3], [0, 3, 3], [0, 3, 3], [0, 3, 3], [0, 3, 3], [0, 3, 1], [0, 3, 1], [0, 3, 1], [0, 3, 1], [0, 3, 1], [0, 3, 4], [0, 3, 4], [0, 3, 4], [0, 3, 4], [0, 3, 4], [0, 3, 2], [0, 3, 2], [0, 3, 2], [0, 3, 2], [0, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_89_26_20 : ColCert where
  rK := ⟨89, by decide⟩
  rH := ⟨26, by decide⟩
  m := 25
  T1 := T89_26
  T2 := Q2.T89_26_2
  h1 := (0,0,4,4,0)
  h2 := (0,0,4,4,0)
  D := [[0, 4, 0], [0, 4, 0], [0, 4, 0], [0, 4, 0], [0, 4, 0], [0, 4, 4], [0, 4, 4], [0, 4, 4], [0, 4, 4], [0, 4, 4], [0, 4, 3], [0, 4, 3], [0, 4, 3], [0, 4, 3], [0, 4, 3], [0, 4, 2], [0, 4, 2], [0, 4, 2], [0, 4, 2], [0, 4, 2], [0, 4, 1], [0, 4, 1], [0, 4, 1], [0, 4, 1], [0, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_89_54_0 : ColCert where
  rK := ⟨89, by decide⟩
  rH := ⟨54, by decide⟩
  m := 5
  T1 := T89_54
  T2 := Q2.T89_54_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_89_54_1 : ColCert where
  rK := ⟨89, by decide⟩
  rH := ⟨54, by decide⟩
  m := 5
  T1 := T89_54
  T2 := Q2.T89_54_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_89_54_2 : ColCert where
  rK := ⟨89, by decide⟩
  rH := ⟨54, by decide⟩
  m := 5
  T1 := T89_54
  T2 := Q2.T89_54_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_89_54_3 : ColCert where
  rK := ⟨89, by decide⟩
  rH := ⟨54, by decide⟩
  m := 5
  T1 := T89_54
  T2 := Q2.T89_54_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_89_54_4 : ColCert where
  rK := ⟨89, by decide⟩
  rH := ⟨54, by decide⟩
  m := 5
  T1 := T89_54
  T2 := Q2.T89_54_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_89_54_5 : ColCert where
  rK := ⟨89, by decide⟩
  rH := ⟨54, by decide⟩
  m := 5
  T1 := T89_54
  T2 := Q2.T89_54_2
  h1 := (1,0,0,4,4)
  h2 := (1,0,0,4,4)
  D := [[1, 0, 4], [1, 0, 3], [1, 0, 2], [1, 0, 1], [1, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_89_54_10 : ColCert where
  rK := ⟨89, by decide⟩
  rH := ⟨54, by decide⟩
  m := 5
  T1 := T89_54
  T2 := Q2.T89_54_2
  h1 := (2,0,0,3,2)
  h2 := (2,0,0,3,2)
  D := [[2, 0, 3], [2, 0, 1], [2, 0, 4], [2, 0, 2], [2, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_89_54_15 : ColCert where
  rK := ⟨89, by decide⟩
  rH := ⟨54, by decide⟩
  m := 5
  T1 := T89_54
  T2 := Q2.T89_54_2
  h1 := (3,0,0,2,4)
  h2 := (3,0,0,2,4)
  D := [[3, 0, 2], [3, 0, 4], [3, 0, 1], [3, 0, 3], [3, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_89_54_20 : ColCert where
  rK := ⟨89, by decide⟩
  rH := ⟨54, by decide⟩
  m := 5
  T1 := T89_54
  T2 := Q2.T89_54_2
  h1 := (4,0,0,1,0)
  h2 := (4,0,0,1,0)
  D := [[4, 0, 1], [4, 0, 2], [4, 0, 3], [4, 0, 4], [4, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_89_89_0 : ColCert where
  rK := ⟨89, by decide⟩
  rH := ⟨89, by decide⟩
  m := 5
  T1 := T89_89
  T2 := Q2.T89_89_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_89_89_1 : ColCert where
  rK := ⟨89, by decide⟩
  rH := ⟨89, by decide⟩
  m := 5
  T1 := T89_89
  T2 := Q2.T89_89_2
  h1 := (0,0,1,1,0)
  h2 := (0,0,1,1,0)
  D := [[0, 1, 0], [0, 1, 0], [0, 1, 0], [0, 1, 0], [0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_89_89_2 : ColCert where
  rK := ⟨89, by decide⟩
  rH := ⟨89, by decide⟩
  m := 5
  T1 := T89_89
  T2 := Q2.T89_89_2
  h1 := (0,0,2,2,0)
  h2 := (0,0,2,2,0)
  D := [[0, 2, 0], [0, 2, 0], [0, 2, 0], [0, 2, 0], [0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_89_89_3 : ColCert where
  rK := ⟨89, by decide⟩
  rH := ⟨89, by decide⟩
  m := 5
  T1 := T89_89
  T2 := Q2.T89_89_2
  h1 := (0,0,3,3,0)
  h2 := (0,0,3,3,0)
  D := [[0, 3, 0], [0, 3, 0], [0, 3, 0], [0, 3, 0], [0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_89_89_4 : ColCert where
  rK := ⟨89, by decide⟩
  rH := ⟨89, by decide⟩
  m := 5
  T1 := T89_89
  T2 := Q2.T89_89_2
  h1 := (0,0,4,4,0)
  h2 := (0,0,4,4,0)
  D := [[0, 4, 0], [0, 4, 0], [0, 4, 0], [0, 4, 0], [0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_89_89_5 : ColCert where
  rK := ⟨89, by decide⟩
  rH := ⟨89, by decide⟩
  m := 5
  T1 := T89_89
  T2 := Q2.T89_89_2
  h1 := (1,0,0,4,0)
  h2 := (1,0,0,4,0)
  D := [[1, 0, 0], [1, 0, 4], [1, 0, 3], [1, 0, 2], [1, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_89_89_6 : ColCert where
  rK := ⟨89, by decide⟩
  rH := ⟨89, by decide⟩
  m := 5
  T1 := T89_89
  T2 := Q2.T89_89_2
  h1 := (1,0,1,0,0)
  h2 := (1,0,1,0,0)
  D := [[1, 1, 4], [1, 1, 3], [1, 1, 2], [1, 1, 1], [1, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_89_89_7 : ColCert where
  rK := ⟨89, by decide⟩
  rH := ⟨89, by decide⟩
  m := 5
  T1 := T89_89
  T2 := Q2.T89_89_2
  h1 := (1,0,2,1,0)
  h2 := (1,0,2,1,0)
  D := [[1, 2, 3], [1, 2, 2], [1, 2, 1], [1, 2, 0], [1, 2, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_89_89_8 : ColCert where
  rK := ⟨89, by decide⟩
  rH := ⟨89, by decide⟩
  m := 5
  T1 := T89_89
  T2 := Q2.T89_89_2
  h1 := (1,0,3,2,0)
  h2 := (1,0,3,2,0)
  D := [[1, 3, 2], [1, 3, 1], [1, 3, 0], [1, 3, 4], [1, 3, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_89_89_9 : ColCert where
  rK := ⟨89, by decide⟩
  rH := ⟨89, by decide⟩
  m := 5
  T1 := T89_89
  T2 := Q2.T89_89_2
  h1 := (1,0,4,3,0)
  h2 := (1,0,4,3,0)
  D := [[1, 4, 1], [1, 4, 0], [1, 4, 4], [1, 4, 3], [1, 4, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_89_89_10 : ColCert where
  rK := ⟨89, by decide⟩
  rH := ⟨89, by decide⟩
  m := 5
  T1 := T89_89
  T2 := Q2.T89_89_2
  h1 := (2,0,0,3,4)
  h2 := (2,0,0,3,4)
  D := [[2, 0, 0], [2, 0, 3], [2, 0, 1], [2, 0, 4], [2, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_89_89_11 : ColCert where
  rK := ⟨89, by decide⟩
  rH := ⟨89, by decide⟩
  m := 5
  T1 := T89_89
  T2 := Q2.T89_89_2
  h1 := (2,0,1,4,4)
  h2 := (2,0,1,4,4)
  D := [[2, 1, 3], [2, 1, 1], [2, 1, 4], [2, 1, 2], [2, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_89_89_12 : ColCert where
  rK := ⟨89, by decide⟩
  rH := ⟨89, by decide⟩
  m := 5
  T1 := T89_89
  T2 := Q2.T89_89_2
  h1 := (2,0,2,0,4)
  h2 := (2,0,2,0,4)
  D := [[2, 2, 1], [2, 2, 4], [2, 2, 2], [2, 2, 0], [2, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_89_89_13 : ColCert where
  rK := ⟨89, by decide⟩
  rH := ⟨89, by decide⟩
  m := 5
  T1 := T89_89
  T2 := Q2.T89_89_2
  h1 := (2,0,3,1,4)
  h2 := (2,0,3,1,4)
  D := [[2, 3, 4], [2, 3, 2], [2, 3, 0], [2, 3, 3], [2, 3, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_89_89_14 : ColCert where
  rK := ⟨89, by decide⟩
  rH := ⟨89, by decide⟩
  m := 5
  T1 := T89_89
  T2 := Q2.T89_89_2
  h1 := (2,0,4,2,4)
  h2 := (2,0,4,2,4)
  D := [[2, 4, 2], [2, 4, 0], [2, 4, 3], [2, 4, 1], [2, 4, 4]]
  bind1 := by decide
  bind2 := by decide

end LeanDring.P5Presentation
