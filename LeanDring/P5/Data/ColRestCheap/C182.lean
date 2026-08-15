/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.Twin1.ColCert
import LeanDring.P5.Data.EntryK.C020

/-!
# Species-table cell data, stage 2 — twin-coincident columns (cheap tier)

Per-column certified exponent-vector data (`ColCert`/`ColCertDiv`) with kernel
`decide` bindings. Emitted; the embedded lists are what the kernel certifies.
rest tier, chunk 181: 60 columns.
-/

-- machine-emitted data: silence style linters (generated long lines, file-level options)
set_option linter.style.longLine false

namespace LeanDring.P5Presentation

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

def colCert_85_18_14 : ColCert where
  rK := ⟨85, by decide⟩
  rH := ⟨18, by decide⟩
  m := 5
  T1 := T85_18
  T2 := Q2.T85_18_2
  h1 := (2,0,4,3,4)
  h2 := (2,0,4,3,4)
  D := [[2, 4, 4], [2, 4, 2], [2, 4, 0], [2, 4, 3], [2, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_85_18_15 : ColCert where
  rK := ⟨85, by decide⟩
  rH := ⟨18, by decide⟩
  m := 5
  T1 := T85_18
  T2 := Q2.T85_18_2
  h1 := (3,0,0,2,1)
  h2 := (3,0,0,2,1)
  D := [[3, 0, 0], [3, 0, 2], [3, 0, 4], [3, 0, 1], [3, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_85_18_16 : ColCert where
  rK := ⟨85, by decide⟩
  rH := ⟨18, by decide⟩
  m := 5
  T1 := T85_18
  T2 := Q2.T85_18_2
  h1 := (3,0,1,2,2)
  h2 := (3,0,1,2,2)
  D := [[3, 1, 1], [3, 1, 3], [3, 1, 0], [3, 1, 2], [3, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_85_18_17 : ColCert where
  rK := ⟨85, by decide⟩
  rH := ⟨18, by decide⟩
  m := 5
  T1 := T85_18
  T2 := Q2.T85_18_2
  h1 := (3,0,2,2,3)
  h2 := (3,0,2,2,3)
  D := [[3, 2, 2], [3, 2, 4], [3, 2, 1], [3, 2, 3], [3, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_85_18_18 : ColCert where
  rK := ⟨85, by decide⟩
  rH := ⟨18, by decide⟩
  m := 5
  T1 := T85_18
  T2 := Q2.T85_18_2
  h1 := (3,0,3,2,4)
  h2 := (3,0,3,2,4)
  D := [[3, 3, 3], [3, 3, 0], [3, 3, 2], [3, 3, 4], [3, 3, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_85_18_19 : ColCert where
  rK := ⟨85, by decide⟩
  rH := ⟨18, by decide⟩
  m := 5
  T1 := T85_18
  T2 := Q2.T85_18_2
  h1 := (3,0,4,2,0)
  h2 := (3,0,4,2,0)
  D := [[3, 4, 4], [3, 4, 1], [3, 4, 3], [3, 4, 0], [3, 4, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_85_18_20 : ColCert where
  rK := ⟨85, by decide⟩
  rH := ⟨18, by decide⟩
  m := 5
  T1 := T85_18
  T2 := Q2.T85_18_2
  h1 := (4,0,0,1,1)
  h2 := (4,0,0,1,1)
  D := [[4, 0, 0], [4, 0, 1], [4, 0, 2], [4, 0, 3], [4, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_85_18_21 : ColCert where
  rK := ⟨85, by decide⟩
  rH := ⟨18, by decide⟩
  m := 5
  T1 := T85_18
  T2 := Q2.T85_18_2
  h1 := (4,0,1,1,2)
  h2 := (4,0,1,1,2)
  D := [[4, 1, 1], [4, 1, 2], [4, 1, 3], [4, 1, 4], [4, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_85_18_22 : ColCert where
  rK := ⟨85, by decide⟩
  rH := ⟨18, by decide⟩
  m := 5
  T1 := T85_18
  T2 := Q2.T85_18_2
  h1 := (4,0,2,1,3)
  h2 := (4,0,2,1,3)
  D := [[4, 2, 2], [4, 2, 3], [4, 2, 4], [4, 2, 0], [4, 2, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_85_18_23 : ColCert where
  rK := ⟨85, by decide⟩
  rH := ⟨18, by decide⟩
  m := 5
  T1 := T85_18
  T2 := Q2.T85_18_2
  h1 := (4,0,3,1,4)
  h2 := (4,0,3,1,4)
  D := [[4, 3, 3], [4, 3, 4], [4, 3, 0], [4, 3, 1], [4, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_85_18_24 : ColCert where
  rK := ⟨85, by decide⟩
  rH := ⟨18, by decide⟩
  m := 5
  T1 := T85_18
  T2 := Q2.T85_18_2
  h1 := (4,0,4,1,0)
  h2 := (4,0,4,1,0)
  D := [[4, 4, 4], [4, 4, 0], [4, 4, 1], [4, 4, 2], [4, 4, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_85_20_0 : ColCert where
  rK := ⟨85, by decide⟩
  rH := ⟨20, by decide⟩
  m := 5
  T1 := T85_20
  T2 := Q2.T85_20_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_85_20_1 : ColCert where
  rK := ⟨85, by decide⟩
  rH := ⟨20, by decide⟩
  m := 5
  T1 := T85_20
  T2 := Q2.T85_20_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_85_20_2 : ColCert where
  rK := ⟨85, by decide⟩
  rH := ⟨20, by decide⟩
  m := 5
  T1 := T85_20
  T2 := Q2.T85_20_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_85_20_3 : ColCert where
  rK := ⟨85, by decide⟩
  rH := ⟨20, by decide⟩
  m := 5
  T1 := T85_20
  T2 := Q2.T85_20_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_85_20_4 : ColCert where
  rK := ⟨85, by decide⟩
  rH := ⟨20, by decide⟩
  m := 5
  T1 := T85_20
  T2 := Q2.T85_20_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_85_20_5 : ColCert where
  rK := ⟨85, by decide⟩
  rH := ⟨20, by decide⟩
  m := 5
  T1 := T85_20
  T2 := Q2.T85_20_2
  h1 := (1,0,4,1,1)
  h2 := (1,0,4,1,1)
  D := [[1, 4, 4], [1, 4, 3], [1, 4, 2], [1, 4, 1], [1, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_85_20_10 : ColCert where
  rK := ⟨85, by decide⟩
  rH := ⟨20, by decide⟩
  m := 5
  T1 := T85_20
  T2 := Q2.T85_20_2
  h1 := (2,0,3,2,3)
  h2 := (2,0,3,2,3)
  D := [[2, 3, 3], [2, 3, 1], [2, 3, 4], [2, 3, 2], [2, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_85_20_15 : ColCert where
  rK := ⟨85, by decide⟩
  rH := ⟨20, by decide⟩
  m := 5
  T1 := T85_20
  T2 := Q2.T85_20_2
  h1 := (3,0,2,3,1)
  h2 := (3,0,2,3,1)
  D := [[3, 2, 2], [3, 2, 4], [3, 2, 1], [3, 2, 3], [3, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_85_20_20 : ColCert where
  rK := ⟨85, by decide⟩
  rH := ⟨20, by decide⟩
  m := 5
  T1 := T85_20
  T2 := Q2.T85_20_2
  h1 := (4,0,1,4,0)
  h2 := (4,0,1,4,0)
  D := [[4, 1, 1], [4, 1, 2], [4, 1, 3], [4, 1, 4], [4, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_85_21_0 : ColCert where
  rK := ⟨85, by decide⟩
  rH := ⟨21, by decide⟩
  m := 5
  T1 := T85_21
  T2 := Q2.T85_21_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_85_21_1 : ColCert where
  rK := ⟨85, by decide⟩
  rH := ⟨21, by decide⟩
  m := 5
  T1 := T85_21
  T2 := Q2.T85_21_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_85_21_2 : ColCert where
  rK := ⟨85, by decide⟩
  rH := ⟨21, by decide⟩
  m := 5
  T1 := T85_21
  T2 := Q2.T85_21_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_85_21_3 : ColCert where
  rK := ⟨85, by decide⟩
  rH := ⟨21, by decide⟩
  m := 5
  T1 := T85_21
  T2 := Q2.T85_21_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_85_21_4 : ColCert where
  rK := ⟨85, by decide⟩
  rH := ⟨21, by decide⟩
  m := 5
  T1 := T85_21
  T2 := Q2.T85_21_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_85_21_5 : ColCert where
  rK := ⟨85, by decide⟩
  rH := ⟨21, by decide⟩
  m := 5
  T1 := T85_21
  T2 := Q2.T85_21_2
  h1 := (1,0,2,3,2)
  h2 := (1,0,2,3,2)
  D := [[1, 2, 3], [1, 2, 2], [1, 2, 1], [1, 2, 0], [1, 2, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_85_21_10 : ColCert where
  rK := ⟨85, by decide⟩
  rH := ⟨21, by decide⟩
  m := 5
  T1 := T85_21
  T2 := Q2.T85_21_2
  h1 := (2,0,4,1,2)
  h2 := (2,0,4,1,2)
  D := [[2, 4, 1], [2, 4, 4], [2, 4, 2], [2, 4, 0], [2, 4, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_85_21_15 : ColCert where
  rK := ⟨85, by decide⟩
  rH := ⟨21, by decide⟩
  m := 5
  T1 := T85_21
  T2 := Q2.T85_21_2
  h1 := (3,0,1,4,0)
  h2 := (3,0,1,4,0)
  D := [[3, 1, 4], [3, 1, 1], [3, 1, 3], [3, 1, 0], [3, 1, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_85_21_20 : ColCert where
  rK := ⟨85, by decide⟩
  rH := ⟨21, by decide⟩
  m := 5
  T1 := T85_21
  T2 := Q2.T85_21_2
  h1 := (4,0,3,2,1)
  h2 := (4,0,3,2,1)
  D := [[4, 3, 2], [4, 3, 3], [4, 3, 4], [4, 3, 0], [4, 3, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_85_22_0 : ColCert where
  rK := ⟨85, by decide⟩
  rH := ⟨22, by decide⟩
  m := 5
  T1 := T85_22
  T2 := Q2.T85_22_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_85_22_1 : ColCert where
  rK := ⟨85, by decide⟩
  rH := ⟨22, by decide⟩
  m := 5
  T1 := T85_22
  T2 := Q2.T85_22_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_85_22_2 : ColCert where
  rK := ⟨85, by decide⟩
  rH := ⟨22, by decide⟩
  m := 5
  T1 := T85_22
  T2 := Q2.T85_22_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_85_22_3 : ColCert where
  rK := ⟨85, by decide⟩
  rH := ⟨22, by decide⟩
  m := 5
  T1 := T85_22
  T2 := Q2.T85_22_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_85_22_4 : ColCert where
  rK := ⟨85, by decide⟩
  rH := ⟨22, by decide⟩
  m := 5
  T1 := T85_22
  T2 := Q2.T85_22_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_85_22_5 : ColCert where
  rK := ⟨85, by decide⟩
  rH := ⟨22, by decide⟩
  m := 5
  T1 := T85_22
  T2 := Q2.T85_22_2
  h1 := (1,0,3,2,4)
  h2 := (1,0,3,2,4)
  D := [[1, 3, 2], [1, 3, 1], [1, 3, 0], [1, 3, 4], [1, 3, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_85_22_10 : ColCert where
  rK := ⟨85, by decide⟩
  rH := ⟨22, by decide⟩
  m := 5
  T1 := T85_22
  T2 := Q2.T85_22_2
  h1 := (2,0,1,4,0)
  h2 := (2,0,1,4,0)
  D := [[2, 1, 4], [2, 1, 2], [2, 1, 0], [2, 1, 3], [2, 1, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_85_22_15 : ColCert where
  rK := ⟨85, by decide⟩
  rH := ⟨22, by decide⟩
  m := 5
  T1 := T85_22
  T2 := Q2.T85_22_2
  h1 := (3,0,4,1,3)
  h2 := (3,0,4,1,3)
  D := [[3, 4, 1], [3, 4, 3], [3, 4, 0], [3, 4, 2], [3, 4, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_85_22_20 : ColCert where
  rK := ⟨85, by decide⟩
  rH := ⟨22, by decide⟩
  m := 5
  T1 := T85_22
  T2 := Q2.T85_22_2
  h1 := (4,0,2,3,3)
  h2 := (4,0,2,3,3)
  D := [[4, 2, 3], [4, 2, 4], [4, 2, 0], [4, 2, 1], [4, 2, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_85_23_0 : ColCert where
  rK := ⟨85, by decide⟩
  rH := ⟨23, by decide⟩
  m := 5
  T1 := T85_23
  T2 := Q2.T85_23_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_85_23_1 : ColCert where
  rK := ⟨85, by decide⟩
  rH := ⟨23, by decide⟩
  m := 5
  T1 := T85_23
  T2 := Q2.T85_23_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_85_23_2 : ColCert where
  rK := ⟨85, by decide⟩
  rH := ⟨23, by decide⟩
  m := 5
  T1 := T85_23
  T2 := Q2.T85_23_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_85_23_3 : ColCert where
  rK := ⟨85, by decide⟩
  rH := ⟨23, by decide⟩
  m := 5
  T1 := T85_23
  T2 := Q2.T85_23_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_85_23_4 : ColCert where
  rK := ⟨85, by decide⟩
  rH := ⟨23, by decide⟩
  m := 5
  T1 := T85_23
  T2 := Q2.T85_23_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_85_23_5 : ColCert where
  rK := ⟨85, by decide⟩
  rH := ⟨23, by decide⟩
  m := 5
  T1 := T85_23
  T2 := Q2.T85_23_2
  h1 := (1,0,1,4,0)
  h2 := (1,0,1,4,0)
  D := [[1, 1, 2], [1, 1, 1], [1, 1, 0], [1, 1, 4], [1, 1, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_85_23_10 : ColCert where
  rK := ⟨85, by decide⟩
  rH := ⟨23, by decide⟩
  m := 5
  T1 := T85_23
  T2 := Q2.T85_23_2
  h1 := (2,0,2,3,4)
  h2 := (2,0,2,3,4)
  D := [[2, 2, 4], [2, 2, 2], [2, 2, 0], [2, 2, 3], [2, 2, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_85_23_15 : ColCert where
  rK := ⟨85, by decide⟩
  rH := ⟨23, by decide⟩
  m := 5
  T1 := T85_23
  T2 := Q2.T85_23_2
  h1 := (3,0,3,2,2)
  h2 := (3,0,3,2,2)
  D := [[3, 3, 1], [3, 3, 3], [3, 3, 0], [3, 3, 2], [3, 3, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_85_23_20 : ColCert where
  rK := ⟨85, by decide⟩
  rH := ⟨23, by decide⟩
  m := 5
  T1 := T85_23
  T2 := Q2.T85_23_2
  h1 := (4,0,4,1,4)
  h2 := (4,0,4,1,4)
  D := [[4, 4, 3], [4, 4, 4], [4, 4, 0], [4, 4, 1], [4, 4, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_85_27_0 : ColCert where
  rK := ⟨85, by decide⟩
  rH := ⟨27, by decide⟩
  m := 25
  T1 := T85_27
  T2 := Q2.T85_27_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_85_27_1 : ColCert where
  rK := ⟨85, by decide⟩
  rH := ⟨27, by decide⟩
  m := 25
  T1 := T85_27
  T2 := Q2.T85_27_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_85_27_2 : ColCert where
  rK := ⟨85, by decide⟩
  rH := ⟨27, by decide⟩
  m := 25
  T1 := T85_27
  T2 := Q2.T85_27_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_85_27_3 : ColCert where
  rK := ⟨85, by decide⟩
  rH := ⟨27, by decide⟩
  m := 25
  T1 := T85_27
  T2 := Q2.T85_27_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_85_27_4 : ColCert where
  rK := ⟨85, by decide⟩
  rH := ⟨27, by decide⟩
  m := 25
  T1 := T85_27
  T2 := Q2.T85_27_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_85_27_5 : ColCert where
  rK := ⟨85, by decide⟩
  rH := ⟨27, by decide⟩
  m := 25
  T1 := T85_27
  T2 := Q2.T85_27_2
  h1 := (0,0,1,0,0)
  h2 := (0,0,1,0,0)
  D := [[0, 1, 0], [0, 1, 0], [0, 1, 0], [0, 1, 0], [0, 1, 0], [0, 1, 1], [0, 1, 1], [0, 1, 1], [0, 1, 1], [0, 1, 1], [0, 1, 2], [0, 1, 2], [0, 1, 2], [0, 1, 2], [0, 1, 2], [0, 1, 3], [0, 1, 3], [0, 1, 3], [0, 1, 3], [0, 1, 3], [0, 1, 4], [0, 1, 4], [0, 1, 4], [0, 1, 4], [0, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_85_27_10 : ColCert where
  rK := ⟨85, by decide⟩
  rH := ⟨27, by decide⟩
  m := 25
  T1 := T85_27
  T2 := Q2.T85_27_2
  h1 := (0,0,2,0,0)
  h2 := (0,0,2,0,0)
  D := [[0, 2, 0], [0, 2, 0], [0, 2, 0], [0, 2, 0], [0, 2, 0], [0, 2, 2], [0, 2, 2], [0, 2, 2], [0, 2, 2], [0, 2, 2], [0, 2, 4], [0, 2, 4], [0, 2, 4], [0, 2, 4], [0, 2, 4], [0, 2, 1], [0, 2, 1], [0, 2, 1], [0, 2, 1], [0, 2, 1], [0, 2, 3], [0, 2, 3], [0, 2, 3], [0, 2, 3], [0, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_85_27_15 : ColCert where
  rK := ⟨85, by decide⟩
  rH := ⟨27, by decide⟩
  m := 25
  T1 := T85_27
  T2 := Q2.T85_27_2
  h1 := (0,0,3,0,0)
  h2 := (0,0,3,0,0)
  D := [[0, 3, 0], [0, 3, 0], [0, 3, 0], [0, 3, 0], [0, 3, 0], [0, 3, 3], [0, 3, 3], [0, 3, 3], [0, 3, 3], [0, 3, 3], [0, 3, 1], [0, 3, 1], [0, 3, 1], [0, 3, 1], [0, 3, 1], [0, 3, 4], [0, 3, 4], [0, 3, 4], [0, 3, 4], [0, 3, 4], [0, 3, 2], [0, 3, 2], [0, 3, 2], [0, 3, 2], [0, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_85_27_20 : ColCert where
  rK := ⟨85, by decide⟩
  rH := ⟨27, by decide⟩
  m := 25
  T1 := T85_27
  T2 := Q2.T85_27_2
  h1 := (0,0,4,0,0)
  h2 := (0,0,4,0,0)
  D := [[0, 4, 0], [0, 4, 0], [0, 4, 0], [0, 4, 0], [0, 4, 0], [0, 4, 4], [0, 4, 4], [0, 4, 4], [0, 4, 4], [0, 4, 4], [0, 4, 3], [0, 4, 3], [0, 4, 3], [0, 4, 3], [0, 4, 3], [0, 4, 2], [0, 4, 2], [0, 4, 2], [0, 4, 2], [0, 4, 2], [0, 4, 1], [0, 4, 1], [0, 4, 1], [0, 4, 1], [0, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_85_54_0 : ColCert where
  rK := ⟨85, by decide⟩
  rH := ⟨54, by decide⟩
  m := 5
  T1 := T85_54
  T2 := Q2.T85_54_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_85_54_1 : ColCert where
  rK := ⟨85, by decide⟩
  rH := ⟨54, by decide⟩
  m := 5
  T1 := T85_54
  T2 := Q2.T85_54_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_85_54_2 : ColCert where
  rK := ⟨85, by decide⟩
  rH := ⟨54, by decide⟩
  m := 5
  T1 := T85_54
  T2 := Q2.T85_54_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_85_54_3 : ColCert where
  rK := ⟨85, by decide⟩
  rH := ⟨54, by decide⟩
  m := 5
  T1 := T85_54
  T2 := Q2.T85_54_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

end LeanDring.P5Presentation
