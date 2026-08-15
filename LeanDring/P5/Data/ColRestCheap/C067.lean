/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.Twin1.ColCert
import LeanDring.P5.Data.EntryK.C034

/-!
# Species-table cell data, stage 2 — twin-coincident columns (cheap tier)

Per-column certified exponent-vector data (`ColCert`/`ColCertDiv`) with kernel
`decide` bindings. Emitted; the embedded lists are what the kernel certifies.
rest tier, chunk 66: 60 columns.
-/

-- machine-emitted data: silence style linters (generated long lines, file-level options)
set_option linter.style.longLine false

namespace LeanDring.P5Presentation

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

def colCert_130_114_2 : ColCert where
  rK := ⟨130, by decide⟩
  rH := ⟨114, by decide⟩
  m := 5
  T1 := T130_114
  T2 := Q2.T130_114_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_130_114_3 : ColCert where
  rK := ⟨130, by decide⟩
  rH := ⟨114, by decide⟩
  m := 5
  T1 := T130_114
  T2 := Q2.T130_114_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_130_114_4 : ColCert where
  rK := ⟨130, by decide⟩
  rH := ⟨114, by decide⟩
  m := 5
  T1 := T130_114
  T2 := Q2.T130_114_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_130_114_5 : ColCert where
  rK := ⟨130, by decide⟩
  rH := ⟨114, by decide⟩
  m := 5
  T1 := T130_114
  T2 := Q2.T130_114_2
  h1 := (1,1,0,0,0)
  h2 := (1,1,0,0,0)
  D := [[1, 1, 4, 3], [1, 1, 4, 2], [1, 1, 4, 1], [1, 1, 4, 0], [1, 1, 4, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_130_114_10 : ColCert where
  rK := ⟨130, by decide⟩
  rH := ⟨114, by decide⟩
  m := 5
  T1 := T130_114
  T2 := Q2.T130_114_2
  h1 := (2,2,0,1,0)
  h2 := (2,2,0,1,0)
  D := [[2, 2, 2, 0], [2, 2, 2, 3], [2, 2, 2, 1], [2, 2, 2, 4], [2, 2, 2, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_130_114_15 : ColCert where
  rK := ⟨130, by decide⟩
  rH := ⟨114, by decide⟩
  m := 5
  T1 := T130_114
  T2 := Q2.T130_114_2
  h1 := (3,3,0,3,1)
  h2 := (3,3,0,3,1)
  D := [[3, 3, 4, 2], [3, 3, 4, 4], [3, 3, 4, 1], [3, 3, 4, 3], [3, 3, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_130_114_20 : ColCert where
  rK := ⟨130, by decide⟩
  rH := ⟨114, by decide⟩
  m := 5
  T1 := T130_114
  T2 := Q2.T130_114_2
  h1 := (4,4,0,1,4)
  h2 := (4,4,0,1,4)
  D := [[4, 4, 0, 0], [4, 4, 0, 1], [4, 4, 0, 2], [4, 4, 0, 3], [4, 4, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_130_130_0 : ColCert where
  rK := ⟨130, by decide⟩
  rH := ⟨130, by decide⟩
  m := 5
  T1 := T130_130
  T2 := Q2.T130_130_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_130_130_1 : ColCert where
  rK := ⟨130, by decide⟩
  rH := ⟨130, by decide⟩
  m := 5
  T1 := T130_130
  T2 := Q2.T130_130_2
  h1 := (0,1,3,0,2)
  h2 := (0,1,3,0,3)
  D := [[0, 1, 0, 0], [0, 1, 0, 4], [0, 1, 0, 3], [0, 1, 0, 2], [0, 1, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_130_130_2 : ColCert where
  rK := ⟨130, by decide⟩
  rH := ⟨130, by decide⟩
  m := 5
  T1 := T130_130
  T2 := Q2.T130_130_2
  h1 := (0,2,1,0,2)
  h2 := (0,2,1,0,4)
  D := [[0, 2, 0, 0], [0, 2, 0, 3], [0, 2, 0, 1], [0, 2, 0, 4], [0, 2, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_130_130_3 : ColCert where
  rK := ⟨130, by decide⟩
  rH := ⟨130, by decide⟩
  m := 5
  T1 := T130_130
  T2 := Q2.T130_130_2
  h1 := (0,3,4,0,0)
  h2 := (0,3,4,0,3)
  D := [[0, 3, 0, 0], [0, 3, 0, 2], [0, 3, 0, 4], [0, 3, 0, 1], [0, 3, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_130_130_4 : ColCert where
  rK := ⟨130, by decide⟩
  rH := ⟨130, by decide⟩
  m := 5
  T1 := T130_130
  T2 := Q2.T130_130_2
  h1 := (0,4,2,0,1)
  h2 := (0,4,2,0,0)
  D := [[0, 4, 0, 0], [0, 4, 0, 1], [0, 4, 0, 2], [0, 4, 0, 3], [0, 4, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_130_130_5 : ColCert where
  rK := ⟨130, by decide⟩
  rH := ⟨130, by decide⟩
  m := 5
  T1 := T130_130
  T2 := Q2.T130_130_2
  h1 := (1,0,2,0,1)
  h2 := (1,0,2,0,0)
  D := [[1, 0, 0, 0], [1, 0, 0, 0], [1, 0, 0, 0], [1, 0, 0, 0], [1, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_130_130_6 : ColCert where
  rK := ⟨130, by decide⟩
  rH := ⟨130, by decide⟩
  m := 5
  T1 := T130_130
  T2 := Q2.T130_130_2
  h1 := (1,1,0,0,0)
  h2 := (1,1,0,0,0)
  D := [[1, 1, 4, 3], [1, 1, 4, 2], [1, 1, 4, 1], [1, 1, 4, 0], [1, 1, 4, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_130_130_7 : ColCert where
  rK := ⟨130, by decide⟩
  rH := ⟨130, by decide⟩
  m := 5
  T1 := T130_130
  T2 := Q2.T130_130_2
  h1 := (1,2,3,0,2)
  h2 := (1,2,3,0,3)
  D := [[1, 2, 3, 1], [1, 2, 3, 4], [1, 2, 3, 2], [1, 2, 3, 0], [1, 2, 3, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_130_130_8 : ColCert where
  rK := ⟨130, by decide⟩
  rH := ⟨130, by decide⟩
  m := 5
  T1 := T130_130
  T2 := Q2.T130_130_2
  h1 := (1,3,1,0,2)
  h2 := (1,3,1,0,4)
  D := [[1, 3, 2, 4], [1, 3, 2, 1], [1, 3, 2, 3], [1, 3, 2, 0], [1, 3, 2, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_130_130_9 : ColCert where
  rK := ⟨130, by decide⟩
  rH := ⟨130, by decide⟩
  m := 5
  T1 := T130_130
  T2 := Q2.T130_130_2
  h1 := (1,4,4,0,0)
  h2 := (1,4,4,0,3)
  D := [[1, 4, 1, 2], [1, 4, 1, 3], [1, 4, 1, 4], [1, 4, 1, 0], [1, 4, 1, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_130_130_10 : ColCert where
  rK := ⟨130, by decide⟩
  rH := ⟨130, by decide⟩
  m := 5
  T1 := T130_130
  T2 := Q2.T130_130_2
  h1 := (2,0,4,0,2)
  h2 := (2,0,4,0,0)
  D := [[2, 0, 0, 0], [2, 0, 0, 0], [2, 0, 0, 0], [2, 0, 0, 0], [2, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_130_130_11 : ColCert where
  rK := ⟨130, by decide⟩
  rH := ⟨130, by decide⟩
  m := 5
  T1 := T130_130
  T2 := Q2.T130_130_2
  h1 := (2,1,2,0,3)
  h2 := (2,1,2,0,2)
  D := [[2, 1, 3, 2], [2, 1, 3, 1], [2, 1, 3, 0], [2, 1, 3, 4], [2, 1, 3, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_130_130_12 : ColCert where
  rK := ⟨130, by decide⟩
  rH := ⟨130, by decide⟩
  m := 5
  T1 := T130_130
  T2 := Q2.T130_130_2
  h1 := (2,2,0,0,2)
  h2 := (2,2,0,0,2)
  D := [[2, 2, 1, 4], [2, 2, 1, 2], [2, 2, 1, 0], [2, 2, 1, 3], [2, 2, 1, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_130_130_13 : ColCert where
  rK := ⟨130, by decide⟩
  rH := ⟨130, by decide⟩
  m := 5
  T1 := T130_130
  T2 := Q2.T130_130_2
  h1 := (2,3,3,0,4)
  h2 := (2,3,3,0,0)
  D := [[2, 3, 4, 1], [2, 3, 4, 3], [2, 3, 4, 0], [2, 3, 4, 2], [2, 3, 4, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_130_130_14 : ColCert where
  rK := ⟨130, by decide⟩
  rH := ⟨130, by decide⟩
  m := 5
  T1 := T130_130
  T2 := Q2.T130_130_2
  h1 := (2,4,1,0,4)
  h2 := (2,4,1,0,1)
  D := [[2, 4, 2, 3], [2, 4, 2, 4], [2, 4, 2, 0], [2, 4, 2, 1], [2, 4, 2, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_130_130_15 : ColCert where
  rK := ⟨130, by decide⟩
  rH := ⟨130, by decide⟩
  m := 5
  T1 := T130_130
  T2 := Q2.T130_130_2
  h1 := (3,0,1,0,3)
  h2 := (3,0,1,0,0)
  D := [[3, 0, 0, 0], [3, 0, 0, 0], [3, 0, 0, 0], [3, 0, 0, 0], [3, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_130_130_16 : ColCert where
  rK := ⟨130, by decide⟩
  rH := ⟨130, by decide⟩
  m := 5
  T1 := T130_130
  T2 := Q2.T130_130_2
  h1 := (3,1,4,0,1)
  h2 := (3,1,4,0,4)
  D := [[3, 1, 2, 2], [3, 1, 2, 1], [3, 1, 2, 0], [3, 1, 2, 4], [3, 1, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_130_130_17 : ColCert where
  rK := ⟨130, by decide⟩
  rH := ⟨130, by decide⟩
  m := 5
  T1 := T130_130
  T2 := Q2.T130_130_2
  h1 := (3,2,2,0,2)
  h2 := (3,2,2,0,1)
  D := [[3, 2, 4, 4], [3, 2, 4, 2], [3, 2, 4, 0], [3, 2, 4, 3], [3, 2, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_130_130_18 : ColCert where
  rK := ⟨130, by decide⟩
  rH := ⟨130, by decide⟩
  m := 5
  T1 := T130_130
  T2 := Q2.T130_130_2
  h1 := (3,3,0,0,1)
  h2 := (3,3,0,0,1)
  D := [[3, 3, 1, 1], [3, 3, 1, 3], [3, 3, 1, 0], [3, 3, 1, 2], [3, 3, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_130_130_19 : ColCert where
  rK := ⟨130, by decide⟩
  rH := ⟨130, by decide⟩
  m := 5
  T1 := T130_130
  T2 := Q2.T130_130_2
  h1 := (3,4,3,0,3)
  h2 := (3,4,3,0,4)
  D := [[3, 4, 3, 3], [3, 4, 3, 4], [3, 4, 3, 0], [3, 4, 3, 1], [3, 4, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_130_130_20 : ColCert where
  rK := ⟨130, by decide⟩
  rH := ⟨130, by decide⟩
  m := 5
  T1 := T130_130
  T2 := Q2.T130_130_2
  h1 := (4,0,3,0,4)
  h2 := (4,0,3,0,0)
  D := [[4, 0, 0, 0], [4, 0, 0, 0], [4, 0, 0, 0], [4, 0, 0, 0], [4, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_130_130_21 : ColCert where
  rK := ⟨130, by decide⟩
  rH := ⟨130, by decide⟩
  m := 5
  T1 := T130_130
  T2 := Q2.T130_130_2
  h1 := (4,1,1,0,4)
  h2 := (4,1,1,0,1)
  D := [[4, 1, 1, 3], [4, 1, 1, 2], [4, 1, 1, 1], [4, 1, 1, 0], [4, 1, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_130_130_22 : ColCert where
  rK := ⟨130, by decide⟩
  rH := ⟨130, by decide⟩
  m := 5
  T1 := T130_130
  T2 := Q2.T130_130_2
  h1 := (4,2,4,0,2)
  h2 := (4,2,4,0,0)
  D := [[4, 2, 2, 1], [4, 2, 2, 4], [4, 2, 2, 2], [4, 2, 2, 0], [4, 2, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_130_130_23 : ColCert where
  rK := ⟨130, by decide⟩
  rH := ⟨130, by decide⟩
  m := 5
  T1 := T130_130
  T2 := Q2.T130_130_2
  h1 := (4,3,2,0,3)
  h2 := (4,3,2,0,2)
  D := [[4, 3, 3, 4], [4, 3, 3, 1], [4, 3, 3, 3], [4, 3, 3, 0], [4, 3, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_130_130_24 : ColCert where
  rK := ⟨130, by decide⟩
  rH := ⟨130, by decide⟩
  m := 5
  T1 := T130_130
  T2 := Q2.T130_130_2
  h1 := (4,4,0,0,2)
  h2 := (4,4,0,0,2)
  D := [[4, 4, 4, 2], [4, 4, 4, 3], [4, 4, 4, 4], [4, 4, 4, 0], [4, 4, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_131_0_0 : ColCert where
  rK := ⟨131, by decide⟩
  rH := ⟨0, by decide⟩
  m := 5
  T1 := T131_0
  T2 := Q2.T131_0_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_131_4_0 : ColCert where
  rK := ⟨131, by decide⟩
  rH := ⟨4, by decide⟩
  m := 5
  T1 := T131_4
  T2 := Q2.T131_4_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_131_4_1 : ColCert where
  rK := ⟨131, by decide⟩
  rH := ⟨4, by decide⟩
  m := 5
  T1 := T131_4
  T2 := Q2.T131_4_2
  h1 := (1,0,3,2,3)
  h2 := (1,0,3,2,3)
  D := [[1, 0, 2, 1], [1, 0, 2, 1], [1, 0, 2, 1], [1, 0, 2, 1], [1, 0, 2, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_131_4_2 : ColCert where
  rK := ⟨131, by decide⟩
  rH := ⟨4, by decide⟩
  m := 5
  T1 := T131_4
  T2 := Q2.T131_4_2
  h1 := (2,0,1,4,3)
  h2 := (2,0,1,4,3)
  D := [[2, 0, 4, 0], [2, 0, 4, 0], [2, 0, 4, 0], [2, 0, 4, 0], [2, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_131_4_3 : ColCert where
  rK := ⟨131, by decide⟩
  rH := ⟨4, by decide⟩
  m := 5
  T1 := T131_4
  T2 := Q2.T131_4_2
  h1 := (3,0,4,1,0)
  h2 := (3,0,4,1,0)
  D := [[3, 0, 1, 2], [3, 0, 1, 2], [3, 0, 1, 2], [3, 0, 1, 2], [3, 0, 1, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_131_4_4 : ColCert where
  rK := ⟨131, by decide⟩
  rH := ⟨4, by decide⟩
  m := 5
  T1 := T131_4
  T2 := Q2.T131_4_2
  h1 := (4,0,2,3,4)
  h2 := (4,0,2,3,4)
  D := [[4, 0, 3, 2], [4, 0, 3, 2], [4, 0, 3, 2], [4, 0, 3, 2], [4, 0, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_131_10_0 : ColCert where
  rK := ⟨131, by decide⟩
  rH := ⟨10, by decide⟩
  m := 5
  T1 := T131_10
  T2 := Q2.T131_10_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_131_10_1 : ColCert where
  rK := ⟨131, by decide⟩
  rH := ⟨10, by decide⟩
  m := 5
  T1 := T131_10
  T2 := Q2.T131_10_2
  h1 := (0,0,0,1,4)
  h2 := (0,0,0,1,4)
  D := [[0, 0, 1, 4], [0, 0, 1, 4], [0, 0, 1, 4], [0, 0, 1, 4], [0, 0, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_131_10_2 : ColCert where
  rK := ⟨131, by decide⟩
  rH := ⟨10, by decide⟩
  m := 5
  T1 := T131_10
  T2 := Q2.T131_10_2
  h1 := (0,0,0,2,3)
  h2 := (0,0,0,2,3)
  D := [[0, 0, 2, 3], [0, 0, 2, 3], [0, 0, 2, 3], [0, 0, 2, 3], [0, 0, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_131_10_3 : ColCert where
  rK := ⟨131, by decide⟩
  rH := ⟨10, by decide⟩
  m := 5
  T1 := T131_10
  T2 := Q2.T131_10_2
  h1 := (0,0,0,3,2)
  h2 := (0,0,0,3,2)
  D := [[0, 0, 3, 2], [0, 0, 3, 2], [0, 0, 3, 2], [0, 0, 3, 2], [0, 0, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_131_10_4 : ColCert where
  rK := ⟨131, by decide⟩
  rH := ⟨10, by decide⟩
  m := 5
  T1 := T131_10
  T2 := Q2.T131_10_2
  h1 := (0,0,0,4,1)
  h2 := (0,0,0,4,1)
  D := [[0, 0, 4, 1], [0, 0, 4, 1], [0, 0, 4, 1], [0, 0, 4, 1], [0, 0, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_131_12_0 : ColCert where
  rK := ⟨131, by decide⟩
  rH := ⟨12, by decide⟩
  m := 5
  T1 := T131_12
  T2 := Q2.T131_12_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_131_12_1 : ColCert where
  rK := ⟨131, by decide⟩
  rH := ⟨12, by decide⟩
  m := 5
  T1 := T131_12
  T2 := Q2.T131_12_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_131_12_2 : ColCert where
  rK := ⟨131, by decide⟩
  rH := ⟨12, by decide⟩
  m := 5
  T1 := T131_12
  T2 := Q2.T131_12_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_131_12_3 : ColCert where
  rK := ⟨131, by decide⟩
  rH := ⟨12, by decide⟩
  m := 5
  T1 := T131_12
  T2 := Q2.T131_12_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_131_12_4 : ColCert where
  rK := ⟨131, by decide⟩
  rH := ⟨12, by decide⟩
  m := 5
  T1 := T131_12
  T2 := Q2.T131_12_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_131_22_0 : ColCert where
  rK := ⟨131, by decide⟩
  rH := ⟨22, by decide⟩
  m := 5
  T1 := T131_22
  T2 := Q2.T131_22_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_131_22_1 : ColCert where
  rK := ⟨131, by decide⟩
  rH := ⟨22, by decide⟩
  m := 5
  T1 := T131_22
  T2 := Q2.T131_22_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_131_22_2 : ColCert where
  rK := ⟨131, by decide⟩
  rH := ⟨22, by decide⟩
  m := 5
  T1 := T131_22
  T2 := Q2.T131_22_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_131_22_3 : ColCert where
  rK := ⟨131, by decide⟩
  rH := ⟨22, by decide⟩
  m := 5
  T1 := T131_22
  T2 := Q2.T131_22_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_131_22_4 : ColCert where
  rK := ⟨131, by decide⟩
  rH := ⟨22, by decide⟩
  m := 5
  T1 := T131_22
  T2 := Q2.T131_22_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_131_22_5 : ColCert where
  rK := ⟨131, by decide⟩
  rH := ⟨22, by decide⟩
  m := 5
  T1 := T131_22
  T2 := Q2.T131_22_2
  h1 := (1,0,3,2,4)
  h2 := (1,0,3,2,4)
  D := [[1, 0, 2, 2], [1, 0, 2, 2], [1, 0, 2, 2], [1, 0, 2, 2], [1, 0, 2, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_131_22_10 : ColCert where
  rK := ⟨131, by decide⟩
  rH := ⟨22, by decide⟩
  m := 5
  T1 := T131_22
  T2 := Q2.T131_22_2
  h1 := (2,0,1,4,0)
  h2 := (2,0,1,4,0)
  D := [[2, 0, 4, 2], [2, 0, 4, 2], [2, 0, 4, 2], [2, 0, 4, 2], [2, 0, 4, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_131_22_15 : ColCert where
  rK := ⟨131, by decide⟩
  rH := ⟨22, by decide⟩
  m := 5
  T1 := T131_22
  T2 := Q2.T131_22_2
  h1 := (3,0,4,1,3)
  h2 := (3,0,4,1,3)
  D := [[3, 0, 1, 0], [3, 0, 1, 0], [3, 0, 1, 0], [3, 0, 1, 0], [3, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_131_22_20 : ColCert where
  rK := ⟨131, by decide⟩
  rH := ⟨22, by decide⟩
  m := 5
  T1 := T131_22
  T2 := Q2.T131_22_2
  h1 := (4,0,2,3,3)
  h2 := (4,0,2,3,3)
  D := [[4, 0, 3, 1], [4, 0, 3, 1], [4, 0, 3, 1], [4, 0, 3, 1], [4, 0, 3, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_131_30_0 : ColCert where
  rK := ⟨131, by decide⟩
  rH := ⟨30, by decide⟩
  m := 5
  T1 := T131_30
  T2 := Q2.T131_30_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_131_30_1 : ColCert where
  rK := ⟨131, by decide⟩
  rH := ⟨30, by decide⟩
  m := 5
  T1 := T131_30
  T2 := Q2.T131_30_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_131_30_2 : ColCert where
  rK := ⟨131, by decide⟩
  rH := ⟨30, by decide⟩
  m := 5
  T1 := T131_30
  T2 := Q2.T131_30_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

end LeanDring.P5Presentation
