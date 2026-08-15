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
rest tier, chunk 183: 60 columns.
-/

-- machine-emitted data: silence style linters (generated long lines, file-level options)
set_option linter.style.longLine false

namespace LeanDring.P5Presentation

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

def colCert_86_5_4 : ColCert where
  rK := ⟨86, by decide⟩
  rH := ⟨5, by decide⟩
  m := 5
  T1 := T86_5
  T2 := Q2.T86_5_2
  h1 := (4,0,4,1,0)
  h2 := (4,0,4,1,0)
  D := [[4, 4, 4], [4, 4, 0], [4, 4, 1], [4, 4, 2], [4, 4, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_86_11_0 : ColCert where
  rK := ⟨86, by decide⟩
  rH := ⟨11, by decide⟩
  m := 5
  T1 := T86_11
  T2 := Q2.T86_11_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_86_11_1 : ColCert where
  rK := ⟨86, by decide⟩
  rH := ⟨11, by decide⟩
  m := 5
  T1 := T86_11
  T2 := Q2.T86_11_2
  h1 := (1,0,0,4,3)
  h2 := (1,0,0,4,3)
  D := [[1, 0, 0], [1, 0, 4], [1, 0, 3], [1, 0, 2], [1, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_86_11_2 : ColCert where
  rK := ⟨86, by decide⟩
  rH := ⟨11, by decide⟩
  m := 5
  T1 := T86_11
  T2 := Q2.T86_11_2
  h1 := (2,0,0,3,0)
  h2 := (2,0,0,3,0)
  D := [[2, 0, 0], [2, 0, 3], [2, 0, 1], [2, 0, 4], [2, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_86_11_3 : ColCert where
  rK := ⟨86, by decide⟩
  rH := ⟨11, by decide⟩
  m := 5
  T1 := T86_11
  T2 := Q2.T86_11_2
  h1 := (3,0,0,2,1)
  h2 := (3,0,0,2,1)
  D := [[3, 0, 0], [3, 0, 2], [3, 0, 4], [3, 0, 1], [3, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_86_11_4 : ColCert where
  rK := ⟨86, by decide⟩
  rH := ⟨11, by decide⟩
  m := 5
  T1 := T86_11
  T2 := Q2.T86_11_2
  h1 := (4,0,0,1,1)
  h2 := (4,0,0,1,1)
  D := [[4, 0, 0], [4, 0, 1], [4, 0, 2], [4, 0, 3], [4, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_86_12_0 : ColCert where
  rK := ⟨86, by decide⟩
  rH := ⟨12, by decide⟩
  m := 25
  T1 := T86_12
  T2 := Q2.T86_12_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_86_12_1 : ColCert where
  rK := ⟨86, by decide⟩
  rH := ⟨12, by decide⟩
  m := 25
  T1 := T86_12
  T2 := Q2.T86_12_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_86_12_2 : ColCert where
  rK := ⟨86, by decide⟩
  rH := ⟨12, by decide⟩
  m := 25
  T1 := T86_12
  T2 := Q2.T86_12_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_86_12_3 : ColCert where
  rK := ⟨86, by decide⟩
  rH := ⟨12, by decide⟩
  m := 25
  T1 := T86_12
  T2 := Q2.T86_12_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_86_12_4 : ColCert where
  rK := ⟨86, by decide⟩
  rH := ⟨12, by decide⟩
  m := 25
  T1 := T86_12
  T2 := Q2.T86_12_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_86_19_0 : ColCert where
  rK := ⟨86, by decide⟩
  rH := ⟨19, by decide⟩
  m := 25
  T1 := T86_19
  T2 := Q2.T86_19_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_86_19_1 : ColCert where
  rK := ⟨86, by decide⟩
  rH := ⟨19, by decide⟩
  m := 25
  T1 := T86_19
  T2 := Q2.T86_19_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_86_19_2 : ColCert where
  rK := ⟨86, by decide⟩
  rH := ⟨19, by decide⟩
  m := 25
  T1 := T86_19
  T2 := Q2.T86_19_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_86_19_3 : ColCert where
  rK := ⟨86, by decide⟩
  rH := ⟨19, by decide⟩
  m := 25
  T1 := T86_19
  T2 := Q2.T86_19_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_86_19_4 : ColCert where
  rK := ⟨86, by decide⟩
  rH := ⟨19, by decide⟩
  m := 25
  T1 := T86_19
  T2 := Q2.T86_19_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_86_19_5 : ColCert where
  rK := ⟨86, by decide⟩
  rH := ⟨19, by decide⟩
  m := 25
  T1 := T86_19
  T2 := Q2.T86_19_2
  h1 := (0,0,1,4,0)
  h2 := (0,0,1,4,0)
  D := [[0, 1, 0], [0, 1, 0], [0, 1, 0], [0, 1, 0], [0, 1, 0], [0, 1, 1], [0, 1, 1], [0, 1, 1], [0, 1, 1], [0, 1, 1], [0, 1, 2], [0, 1, 2], [0, 1, 2], [0, 1, 2], [0, 1, 2], [0, 1, 3], [0, 1, 3], [0, 1, 3], [0, 1, 3], [0, 1, 3], [0, 1, 4], [0, 1, 4], [0, 1, 4], [0, 1, 4], [0, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_86_19_10 : ColCert where
  rK := ⟨86, by decide⟩
  rH := ⟨19, by decide⟩
  m := 25
  T1 := T86_19
  T2 := Q2.T86_19_2
  h1 := (0,0,2,3,0)
  h2 := (0,0,2,3,0)
  D := [[0, 2, 0], [0, 2, 0], [0, 2, 0], [0, 2, 0], [0, 2, 0], [0, 2, 2], [0, 2, 2], [0, 2, 2], [0, 2, 2], [0, 2, 2], [0, 2, 4], [0, 2, 4], [0, 2, 4], [0, 2, 4], [0, 2, 4], [0, 2, 1], [0, 2, 1], [0, 2, 1], [0, 2, 1], [0, 2, 1], [0, 2, 3], [0, 2, 3], [0, 2, 3], [0, 2, 3], [0, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_86_19_15 : ColCert where
  rK := ⟨86, by decide⟩
  rH := ⟨19, by decide⟩
  m := 25
  T1 := T86_19
  T2 := Q2.T86_19_2
  h1 := (0,0,3,2,0)
  h2 := (0,0,3,2,0)
  D := [[0, 3, 0], [0, 3, 0], [0, 3, 0], [0, 3, 0], [0, 3, 0], [0, 3, 3], [0, 3, 3], [0, 3, 3], [0, 3, 3], [0, 3, 3], [0, 3, 1], [0, 3, 1], [0, 3, 1], [0, 3, 1], [0, 3, 1], [0, 3, 4], [0, 3, 4], [0, 3, 4], [0, 3, 4], [0, 3, 4], [0, 3, 2], [0, 3, 2], [0, 3, 2], [0, 3, 2], [0, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_86_19_20 : ColCert where
  rK := ⟨86, by decide⟩
  rH := ⟨19, by decide⟩
  m := 25
  T1 := T86_19
  T2 := Q2.T86_19_2
  h1 := (0,0,4,1,0)
  h2 := (0,0,4,1,0)
  D := [[0, 4, 0], [0, 4, 0], [0, 4, 0], [0, 4, 0], [0, 4, 0], [0, 4, 4], [0, 4, 4], [0, 4, 4], [0, 4, 4], [0, 4, 4], [0, 4, 3], [0, 4, 3], [0, 4, 3], [0, 4, 3], [0, 4, 3], [0, 4, 2], [0, 4, 2], [0, 4, 2], [0, 4, 2], [0, 4, 2], [0, 4, 1], [0, 4, 1], [0, 4, 1], [0, 4, 1], [0, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_86_20_0 : ColCert where
  rK := ⟨86, by decide⟩
  rH := ⟨20, by decide⟩
  m := 5
  T1 := T86_20
  T2 := Q2.T86_20_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_86_20_1 : ColCert where
  rK := ⟨86, by decide⟩
  rH := ⟨20, by decide⟩
  m := 5
  T1 := T86_20
  T2 := Q2.T86_20_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_86_20_2 : ColCert where
  rK := ⟨86, by decide⟩
  rH := ⟨20, by decide⟩
  m := 5
  T1 := T86_20
  T2 := Q2.T86_20_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_86_20_3 : ColCert where
  rK := ⟨86, by decide⟩
  rH := ⟨20, by decide⟩
  m := 5
  T1 := T86_20
  T2 := Q2.T86_20_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_86_20_4 : ColCert where
  rK := ⟨86, by decide⟩
  rH := ⟨20, by decide⟩
  m := 5
  T1 := T86_20
  T2 := Q2.T86_20_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_86_20_5 : ColCert where
  rK := ⟨86, by decide⟩
  rH := ⟨20, by decide⟩
  m := 5
  T1 := T86_20
  T2 := Q2.T86_20_2
  h1 := (1,0,4,1,1)
  h2 := (1,0,4,1,1)
  D := [[1, 4, 0], [1, 4, 4], [1, 4, 3], [1, 4, 2], [1, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_86_20_10 : ColCert where
  rK := ⟨86, by decide⟩
  rH := ⟨20, by decide⟩
  m := 5
  T1 := T86_20
  T2 := Q2.T86_20_2
  h1 := (2,0,3,2,3)
  h2 := (2,0,3,2,3)
  D := [[2, 3, 4], [2, 3, 2], [2, 3, 0], [2, 3, 3], [2, 3, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_86_20_15 : ColCert where
  rK := ⟨86, by decide⟩
  rH := ⟨20, by decide⟩
  m := 5
  T1 := T86_20
  T2 := Q2.T86_20_2
  h1 := (3,0,2,3,1)
  h2 := (3,0,2,3,1)
  D := [[3, 2, 2], [3, 2, 4], [3, 2, 1], [3, 2, 3], [3, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_86_20_20 : ColCert where
  rK := ⟨86, by decide⟩
  rH := ⟨20, by decide⟩
  m := 5
  T1 := T86_20
  T2 := Q2.T86_20_2
  h1 := (4,0,1,4,0)
  h2 := (4,0,1,4,0)
  D := [[4, 1, 4], [4, 1, 0], [4, 1, 1], [4, 1, 2], [4, 1, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_86_21_0 : ColCert where
  rK := ⟨86, by decide⟩
  rH := ⟨21, by decide⟩
  m := 5
  T1 := T86_21
  T2 := Q2.T86_21_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_86_21_1 : ColCert where
  rK := ⟨86, by decide⟩
  rH := ⟨21, by decide⟩
  m := 5
  T1 := T86_21
  T2 := Q2.T86_21_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_86_21_2 : ColCert where
  rK := ⟨86, by decide⟩
  rH := ⟨21, by decide⟩
  m := 5
  T1 := T86_21
  T2 := Q2.T86_21_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_86_21_3 : ColCert where
  rK := ⟨86, by decide⟩
  rH := ⟨21, by decide⟩
  m := 5
  T1 := T86_21
  T2 := Q2.T86_21_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_86_21_4 : ColCert where
  rK := ⟨86, by decide⟩
  rH := ⟨21, by decide⟩
  m := 5
  T1 := T86_21
  T2 := Q2.T86_21_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_86_21_5 : ColCert where
  rK := ⟨86, by decide⟩
  rH := ⟨21, by decide⟩
  m := 5
  T1 := T86_21
  T2 := Q2.T86_21_2
  h1 := (1,0,2,3,2)
  h2 := (1,0,2,3,2)
  D := [[1, 2, 2], [1, 2, 1], [1, 2, 0], [1, 2, 4], [1, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_86_21_10 : ColCert where
  rK := ⟨86, by decide⟩
  rH := ⟨21, by decide⟩
  m := 5
  T1 := T86_21
  T2 := Q2.T86_21_2
  h1 := (2,0,4,1,2)
  h2 := (2,0,4,1,2)
  D := [[2, 4, 1], [2, 4, 4], [2, 4, 2], [2, 4, 0], [2, 4, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_86_21_15 : ColCert where
  rK := ⟨86, by decide⟩
  rH := ⟨21, by decide⟩
  m := 5
  T1 := T86_21
  T2 := Q2.T86_21_2
  h1 := (3,0,1,4,0)
  h2 := (3,0,1,4,0)
  D := [[3, 1, 2], [3, 1, 4], [3, 1, 1], [3, 1, 3], [3, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_86_21_20 : ColCert where
  rK := ⟨86, by decide⟩
  rH := ⟨21, by decide⟩
  m := 5
  T1 := T86_21
  T2 := Q2.T86_21_2
  h1 := (4,0,3,2,1)
  h2 := (4,0,3,2,1)
  D := [[4, 3, 0], [4, 3, 1], [4, 3, 2], [4, 3, 3], [4, 3, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_86_22_0 : ColCert where
  rK := ⟨86, by decide⟩
  rH := ⟨22, by decide⟩
  m := 5
  T1 := T86_22
  T2 := Q2.T86_22_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_86_22_1 : ColCert where
  rK := ⟨86, by decide⟩
  rH := ⟨22, by decide⟩
  m := 5
  T1 := T86_22
  T2 := Q2.T86_22_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_86_22_2 : ColCert where
  rK := ⟨86, by decide⟩
  rH := ⟨22, by decide⟩
  m := 5
  T1 := T86_22
  T2 := Q2.T86_22_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_86_22_3 : ColCert where
  rK := ⟨86, by decide⟩
  rH := ⟨22, by decide⟩
  m := 5
  T1 := T86_22
  T2 := Q2.T86_22_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_86_22_4 : ColCert where
  rK := ⟨86, by decide⟩
  rH := ⟨22, by decide⟩
  m := 5
  T1 := T86_22
  T2 := Q2.T86_22_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_86_22_5 : ColCert where
  rK := ⟨86, by decide⟩
  rH := ⟨22, by decide⟩
  m := 5
  T1 := T86_22
  T2 := Q2.T86_22_2
  h1 := (1,0,3,2,4)
  h2 := (1,0,3,2,4)
  D := [[1, 3, 1], [1, 3, 0], [1, 3, 4], [1, 3, 3], [1, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_86_22_10 : ColCert where
  rK := ⟨86, by decide⟩
  rH := ⟨22, by decide⟩
  m := 5
  T1 := T86_22
  T2 := Q2.T86_22_2
  h1 := (2,0,1,4,0)
  h2 := (2,0,1,4,0)
  D := [[2, 1, 0], [2, 1, 3], [2, 1, 1], [2, 1, 4], [2, 1, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_86_22_15 : ColCert where
  rK := ⟨86, by decide⟩
  rH := ⟨22, by decide⟩
  m := 5
  T1 := T86_22
  T2 := Q2.T86_22_2
  h1 := (3,0,4,1,3)
  h2 := (3,0,4,1,3)
  D := [[3, 4, 2], [3, 4, 4], [3, 4, 1], [3, 4, 3], [3, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_86_22_20 : ColCert where
  rK := ⟨86, by decide⟩
  rH := ⟨22, by decide⟩
  m := 5
  T1 := T86_22
  T2 := Q2.T86_22_2
  h1 := (4,0,2,3,3)
  h2 := (4,0,2,3,3)
  D := [[4, 2, 2], [4, 2, 3], [4, 2, 4], [4, 2, 0], [4, 2, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_86_23_0 : ColCert where
  rK := ⟨86, by decide⟩
  rH := ⟨23, by decide⟩
  m := 5
  T1 := T86_23
  T2 := Q2.T86_23_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_86_23_1 : ColCert where
  rK := ⟨86, by decide⟩
  rH := ⟨23, by decide⟩
  m := 5
  T1 := T86_23
  T2 := Q2.T86_23_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_86_23_2 : ColCert where
  rK := ⟨86, by decide⟩
  rH := ⟨23, by decide⟩
  m := 5
  T1 := T86_23
  T2 := Q2.T86_23_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_86_23_3 : ColCert where
  rK := ⟨86, by decide⟩
  rH := ⟨23, by decide⟩
  m := 5
  T1 := T86_23
  T2 := Q2.T86_23_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_86_23_4 : ColCert where
  rK := ⟨86, by decide⟩
  rH := ⟨23, by decide⟩
  m := 5
  T1 := T86_23
  T2 := Q2.T86_23_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_86_23_5 : ColCert where
  rK := ⟨86, by decide⟩
  rH := ⟨23, by decide⟩
  m := 5
  T1 := T86_23
  T2 := Q2.T86_23_2
  h1 := (1,0,1,4,0)
  h2 := (1,0,1,4,0)
  D := [[1, 1, 3], [1, 1, 2], [1, 1, 1], [1, 1, 0], [1, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_86_23_10 : ColCert where
  rK := ⟨86, by decide⟩
  rH := ⟨23, by decide⟩
  m := 5
  T1 := T86_23
  T2 := Q2.T86_23_2
  h1 := (2,0,2,3,4)
  h2 := (2,0,2,3,4)
  D := [[2, 2, 2], [2, 2, 0], [2, 2, 3], [2, 2, 1], [2, 2, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_86_23_15 : ColCert where
  rK := ⟨86, by decide⟩
  rH := ⟨23, by decide⟩
  m := 5
  T1 := T86_23
  T2 := Q2.T86_23_2
  h1 := (3,0,3,2,2)
  h2 := (3,0,3,2,2)
  D := [[3, 3, 2], [3, 3, 4], [3, 3, 1], [3, 3, 3], [3, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_86_23_20 : ColCert where
  rK := ⟨86, by decide⟩
  rH := ⟨23, by decide⟩
  m := 5
  T1 := T86_23
  T2 := Q2.T86_23_2
  h1 := (4,0,4,1,4)
  h2 := (4,0,4,1,4)
  D := [[4, 4, 3], [4, 4, 4], [4, 4, 0], [4, 4, 1], [4, 4, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_86_54_0 : ColCert where
  rK := ⟨86, by decide⟩
  rH := ⟨54, by decide⟩
  m := 5
  T1 := T86_54
  T2 := Q2.T86_54_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_86_54_1 : ColCert where
  rK := ⟨86, by decide⟩
  rH := ⟨54, by decide⟩
  m := 5
  T1 := T86_54
  T2 := Q2.T86_54_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_86_54_2 : ColCert where
  rK := ⟨86, by decide⟩
  rH := ⟨54, by decide⟩
  m := 5
  T1 := T86_54
  T2 := Q2.T86_54_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_86_54_3 : ColCert where
  rK := ⟨86, by decide⟩
  rH := ⟨54, by decide⟩
  m := 5
  T1 := T86_54
  T2 := Q2.T86_54_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

end LeanDring.P5Presentation
