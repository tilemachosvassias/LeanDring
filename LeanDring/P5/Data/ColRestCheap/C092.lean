/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.Twin1.ColCert
import LeanDring.P5.Data.EntryK.C040

/-!
# Species-table cell data, stage 2 — twin-coincident columns (cheap tier)

Per-column certified exponent-vector data (`ColCert`/`ColCertDiv`) with kernel
`decide` bindings. Emitted; the embedded lists are what the kernel certifies.
rest tier, chunk 91: 60 columns.
-/

-- machine-emitted data: silence style linters (generated long lines, file-level options)
set_option linter.style.longLine false

namespace LeanDring.P5Presentation

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

def colCert_141_20_15 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨20, by decide⟩
  m := 5
  T1 := T141_20
  T2 := Q2.T141_20_2
  h1 := (3,0,2,3,1)
  h2 := (3,0,2,3,1)
  D := [[3, 2, 3, 2], [3, 2, 0, 0], [3, 2, 2, 3], [3, 2, 4, 1], [3, 2, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_20_20 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨20, by decide⟩
  m := 5
  T1 := T141_20
  T2 := Q2.T141_20_2
  h1 := (4,0,1,4,0)
  h2 := (4,0,1,4,0)
  D := [[4, 1, 4, 4], [4, 1, 0, 0], [4, 1, 1, 1], [4, 1, 2, 2], [4, 1, 3, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_21_0 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨21, by decide⟩
  m := 5
  T1 := T141_21
  T2 := Q2.T141_21_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_21_1 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨21, by decide⟩
  m := 5
  T1 := T141_21
  T2 := Q2.T141_21_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_21_2 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨21, by decide⟩
  m := 5
  T1 := T141_21
  T2 := Q2.T141_21_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_21_3 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨21, by decide⟩
  m := 5
  T1 := T141_21
  T2 := Q2.T141_21_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_21_4 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨21, by decide⟩
  m := 5
  T1 := T141_21
  T2 := Q2.T141_21_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_21_5 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨21, by decide⟩
  m := 5
  T1 := T141_21
  T2 := Q2.T141_21_2
  h1 := (1,0,2,3,2)
  h2 := (1,0,2,3,2)
  D := [[1, 2, 3, 4], [1, 2, 2, 2], [1, 2, 1, 0], [1, 2, 0, 3], [1, 2, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_21_10 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨21, by decide⟩
  m := 5
  T1 := T141_21
  T2 := Q2.T141_21_2
  h1 := (2,0,4,1,2)
  h2 := (2,0,4,1,2)
  D := [[2, 4, 1, 0], [2, 4, 4, 2], [2, 4, 2, 4], [2, 4, 0, 1], [2, 4, 3, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_21_15 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨21, by decide⟩
  m := 5
  T1 := T141_21
  T2 := Q2.T141_21_2
  h1 := (3,0,1,4,0)
  h2 := (3,0,1,4,0)
  D := [[3, 1, 4, 3], [3, 1, 1, 0], [3, 1, 3, 2], [3, 1, 0, 4], [3, 1, 2, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_21_20 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨21, by decide⟩
  m := 5
  T1 := T141_21
  T2 := Q2.T141_21_2
  h1 := (4,0,3,2,1)
  h2 := (4,0,3,2,1)
  D := [[4, 3, 2, 3], [4, 3, 3, 1], [4, 3, 4, 4], [4, 3, 0, 2], [4, 3, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_22_0 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨22, by decide⟩
  m := 5
  T1 := T141_22
  T2 := Q2.T141_22_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_22_1 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨22, by decide⟩
  m := 5
  T1 := T141_22
  T2 := Q2.T141_22_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_22_2 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨22, by decide⟩
  m := 5
  T1 := T141_22
  T2 := Q2.T141_22_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_22_3 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨22, by decide⟩
  m := 5
  T1 := T141_22
  T2 := Q2.T141_22_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_22_4 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨22, by decide⟩
  m := 5
  T1 := T141_22
  T2 := Q2.T141_22_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_22_5 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨22, by decide⟩
  m := 5
  T1 := T141_22
  T2 := Q2.T141_22_2
  h1 := (1,0,3,2,4)
  h2 := (1,0,3,2,4)
  D := [[1, 3, 2, 2], [1, 3, 1, 1], [1, 3, 0, 0], [1, 3, 4, 4], [1, 3, 3, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_22_10 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨22, by decide⟩
  m := 5
  T1 := T141_22
  T2 := Q2.T141_22_2
  h1 := (2,0,1,4,0)
  h2 := (2,0,1,4,0)
  D := [[2, 1, 4, 2], [2, 1, 2, 1], [2, 1, 0, 0], [2, 1, 3, 4], [2, 1, 1, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_22_15 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨22, by decide⟩
  m := 5
  T1 := T141_22
  T2 := Q2.T141_22_2
  h1 := (3,0,4,1,3)
  h2 := (3,0,4,1,3)
  D := [[3, 4, 1, 0], [3, 4, 3, 0], [3, 4, 0, 0], [3, 4, 2, 0], [3, 4, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_22_20 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨22, by decide⟩
  m := 5
  T1 := T141_22
  T2 := Q2.T141_22_2
  h1 := (4,0,2,3,3)
  h2 := (4,0,2,3,3)
  D := [[4, 2, 3, 1], [4, 2, 4, 3], [4, 2, 0, 0], [4, 2, 1, 2], [4, 2, 2, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_23_0 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨23, by decide⟩
  m := 5
  T1 := T141_23
  T2 := Q2.T141_23_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_23_1 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨23, by decide⟩
  m := 5
  T1 := T141_23
  T2 := Q2.T141_23_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_23_2 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨23, by decide⟩
  m := 5
  T1 := T141_23
  T2 := Q2.T141_23_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_23_3 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨23, by decide⟩
  m := 5
  T1 := T141_23
  T2 := Q2.T141_23_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_23_4 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨23, by decide⟩
  m := 5
  T1 := T141_23
  T2 := Q2.T141_23_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_23_5 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨23, by decide⟩
  m := 5
  T1 := T141_23
  T2 := Q2.T141_23_2
  h1 := (1,0,1,4,0)
  h2 := (1,0,1,4,0)
  D := [[1, 1, 4, 1], [1, 1, 3, 3], [1, 1, 2, 0], [1, 1, 1, 2], [1, 1, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_23_10 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨23, by decide⟩
  m := 5
  T1 := T141_23
  T2 := Q2.T141_23_2
  h1 := (2,0,2,3,4)
  h2 := (2,0,2,3,4)
  D := [[2, 2, 3, 3], [2, 2, 1, 3], [2, 2, 4, 3], [2, 2, 2, 3], [2, 2, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_23_15 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨23, by decide⟩
  m := 5
  T1 := T141_23
  T2 := Q2.T141_23_2
  h1 := (3,0,3,2,2)
  h2 := (3,0,3,2,2)
  D := [[3, 3, 2, 1], [3, 3, 4, 0], [3, 3, 1, 4], [3, 3, 3, 3], [3, 3, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_23_20 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨23, by decide⟩
  m := 5
  T1 := T141_23
  T2 := Q2.T141_23_2
  h1 := (4,0,4,1,4)
  h2 := (4,0,4,1,4)
  D := [[4, 4, 1, 0], [4, 4, 2, 4], [4, 4, 3, 3], [4, 4, 4, 2], [4, 4, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_24_0 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨24, by decide⟩
  m := 5
  T1 := T141_24
  T2 := Q2.T141_24_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_24_1 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨24, by decide⟩
  m := 5
  T1 := T141_24
  T2 := Q2.T141_24_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_24_2 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨24, by decide⟩
  m := 5
  T1 := T141_24
  T2 := Q2.T141_24_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_24_3 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨24, by decide⟩
  m := 5
  T1 := T141_24
  T2 := Q2.T141_24_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_24_4 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨24, by decide⟩
  m := 5
  T1 := T141_24
  T2 := Q2.T141_24_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_24_5 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨24, by decide⟩
  m := 5
  T1 := T141_24
  T2 := Q2.T141_24_2
  h1 := (0,0,1,2,0)
  h2 := (0,0,1,2,0)
  D := [[0, 1, 2, 0], [0, 1, 2, 1], [0, 1, 2, 2], [0, 1, 2, 3], [0, 1, 2, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_24_10 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨24, by decide⟩
  m := 5
  T1 := T141_24
  T2 := Q2.T141_24_2
  h1 := (0,0,2,4,0)
  h2 := (0,0,2,4,0)
  D := [[0, 2, 4, 0], [0, 2, 4, 2], [0, 2, 4, 4], [0, 2, 4, 1], [0, 2, 4, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_24_15 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨24, by decide⟩
  m := 5
  T1 := T141_24
  T2 := Q2.T141_24_2
  h1 := (0,0,3,1,0)
  h2 := (0,0,3,1,0)
  D := [[0, 3, 1, 0], [0, 3, 1, 3], [0, 3, 1, 1], [0, 3, 1, 4], [0, 3, 1, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_24_20 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨24, by decide⟩
  m := 5
  T1 := T141_24
  T2 := Q2.T141_24_2
  h1 := (0,0,4,3,0)
  h2 := (0,0,4,3,0)
  D := [[0, 4, 3, 0], [0, 4, 3, 4], [0, 4, 3, 3], [0, 4, 3, 2], [0, 4, 3, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_25_0 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨25, by decide⟩
  m := 5
  T1 := T141_25
  T2 := Q2.T141_25_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_25_1 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨25, by decide⟩
  m := 5
  T1 := T141_25
  T2 := Q2.T141_25_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_25_2 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨25, by decide⟩
  m := 5
  T1 := T141_25
  T2 := Q2.T141_25_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_25_3 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨25, by decide⟩
  m := 5
  T1 := T141_25
  T2 := Q2.T141_25_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_25_4 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨25, by decide⟩
  m := 5
  T1 := T141_25
  T2 := Q2.T141_25_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_25_5 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨25, by decide⟩
  m := 5
  T1 := T141_25
  T2 := Q2.T141_25_2
  h1 := (0,0,1,3,0)
  h2 := (0,0,1,3,0)
  D := [[0, 1, 3, 0], [0, 1, 3, 1], [0, 1, 3, 2], [0, 1, 3, 3], [0, 1, 3, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_25_10 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨25, by decide⟩
  m := 5
  T1 := T141_25
  T2 := Q2.T141_25_2
  h1 := (0,0,2,1,0)
  h2 := (0,0,2,1,0)
  D := [[0, 2, 1, 0], [0, 2, 1, 2], [0, 2, 1, 4], [0, 2, 1, 1], [0, 2, 1, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_25_15 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨25, by decide⟩
  m := 5
  T1 := T141_25
  T2 := Q2.T141_25_2
  h1 := (0,0,3,4,0)
  h2 := (0,0,3,4,0)
  D := [[0, 3, 4, 0], [0, 3, 4, 3], [0, 3, 4, 1], [0, 3, 4, 4], [0, 3, 4, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_25_20 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨25, by decide⟩
  m := 5
  T1 := T141_25
  T2 := Q2.T141_25_2
  h1 := (0,0,4,2,0)
  h2 := (0,0,4,2,0)
  D := [[0, 4, 2, 0], [0, 4, 2, 4], [0, 4, 2, 3], [0, 4, 2, 2], [0, 4, 2, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_26_0 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨26, by decide⟩
  m := 5
  T1 := T141_26
  T2 := Q2.T141_26_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_26_1 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨26, by decide⟩
  m := 5
  T1 := T141_26
  T2 := Q2.T141_26_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_26_2 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨26, by decide⟩
  m := 5
  T1 := T141_26
  T2 := Q2.T141_26_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_26_3 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨26, by decide⟩
  m := 5
  T1 := T141_26
  T2 := Q2.T141_26_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_26_4 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨26, by decide⟩
  m := 5
  T1 := T141_26
  T2 := Q2.T141_26_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_26_5 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨26, by decide⟩
  m := 5
  T1 := T141_26
  T2 := Q2.T141_26_2
  h1 := (0,0,1,1,0)
  h2 := (0,0,1,1,0)
  D := [[0, 1, 1, 0], [0, 1, 1, 1], [0, 1, 1, 2], [0, 1, 1, 3], [0, 1, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_26_10 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨26, by decide⟩
  m := 5
  T1 := T141_26
  T2 := Q2.T141_26_2
  h1 := (0,0,2,2,0)
  h2 := (0,0,2,2,0)
  D := [[0, 2, 2, 0], [0, 2, 2, 2], [0, 2, 2, 4], [0, 2, 2, 1], [0, 2, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_26_15 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨26, by decide⟩
  m := 5
  T1 := T141_26
  T2 := Q2.T141_26_2
  h1 := (0,0,3,3,0)
  h2 := (0,0,3,3,0)
  D := [[0, 3, 3, 0], [0, 3, 3, 3], [0, 3, 3, 1], [0, 3, 3, 4], [0, 3, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_26_20 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨26, by decide⟩
  m := 5
  T1 := T141_26
  T2 := Q2.T141_26_2
  h1 := (0,0,4,4,0)
  h2 := (0,0,4,4,0)
  D := [[0, 4, 4, 0], [0, 4, 4, 4], [0, 4, 4, 3], [0, 4, 4, 2], [0, 4, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_27_0 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨27, by decide⟩
  m := 5
  T1 := T141_27
  T2 := Q2.T141_27_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_27_1 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨27, by decide⟩
  m := 5
  T1 := T141_27
  T2 := Q2.T141_27_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_27_2 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨27, by decide⟩
  m := 5
  T1 := T141_27
  T2 := Q2.T141_27_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_27_3 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨27, by decide⟩
  m := 5
  T1 := T141_27
  T2 := Q2.T141_27_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

end LeanDring.P5Presentation
