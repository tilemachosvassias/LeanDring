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
rest tier, chunk 94: 60 columns.
-/

-- machine-emitted data: silence style linters (generated long lines, file-level options)
set_option linter.style.longLine false

namespace LeanDring.P5Presentation

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

def colCert_141_86_7 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨86, by decide⟩
  m := 5
  T1 := T141_86
  T2 := Q2.T141_86_2
  h1 := (1,0,2,2,0)
  h2 := (1,0,2,2,0)
  D := [[1, 2, 2, 3], [1, 2, 1, 1], [1, 2, 0, 4], [1, 2, 4, 2], [1, 2, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_86_8 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨86, by decide⟩
  m := 5
  T1 := T141_86
  T2 := Q2.T141_86_2
  h1 := (1,0,3,1,0)
  h2 := (1,0,3,1,0)
  D := [[1, 3, 1, 4], [1, 3, 0, 3], [1, 3, 4, 2], [1, 3, 3, 1], [1, 3, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_86_9 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨86, by decide⟩
  m := 5
  T1 := T141_86
  T2 := Q2.T141_86_2
  h1 := (1,0,4,0,0)
  h2 := (1,0,4,0,0)
  D := [[1, 4, 0, 0], [1, 4, 4, 0], [1, 4, 3, 0], [1, 4, 2, 0], [1, 4, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_86_10 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨86, by decide⟩
  m := 5
  T1 := T141_86
  T2 := Q2.T141_86_2
  h1 := (2,0,0,3,4)
  h2 := (2,0,0,3,4)
  D := [[2, 0, 3, 3], [2, 0, 1, 1], [2, 0, 4, 4], [2, 0, 2, 2], [2, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_86_11 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨86, by decide⟩
  m := 5
  T1 := T141_86
  T2 := Q2.T141_86_2
  h1 := (2,0,1,2,4)
  h2 := (2,0,1,2,4)
  D := [[2, 1, 2, 0], [2, 1, 0, 4], [2, 1, 3, 3], [2, 1, 1, 2], [2, 1, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_86_12 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨86, by decide⟩
  m := 5
  T1 := T141_86
  T2 := Q2.T141_86_2
  h1 := (2,0,2,1,4)
  h2 := (2,0,2,1,4)
  D := [[2, 2, 1, 2], [2, 2, 4, 2], [2, 2, 2, 2], [2, 2, 0, 2], [2, 2, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_86_13 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨86, by decide⟩
  m := 5
  T1 := T141_86
  T2 := Q2.T141_86_2
  h1 := (2,0,3,0,4)
  h2 := (2,0,3,0,4)
  D := [[2, 3, 0, 4], [2, 3, 3, 0], [2, 3, 1, 1], [2, 3, 4, 2], [2, 3, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_86_14 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨86, by decide⟩
  m := 5
  T1 := T141_86
  T2 := Q2.T141_86_2
  h1 := (2,0,4,4,4)
  h2 := (2,0,4,4,4)
  D := [[2, 4, 4, 1], [2, 4, 2, 3], [2, 4, 0, 0], [2, 4, 3, 2], [2, 4, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_86_15 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨86, by decide⟩
  m := 5
  T1 := T141_86
  T2 := Q2.T141_86_2
  h1 := (3,0,0,2,2)
  h2 := (3,0,0,2,2)
  D := [[3, 0, 2, 1], [3, 0, 4, 2], [3, 0, 1, 3], [3, 0, 3, 4], [3, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_86_16 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨86, by decide⟩
  m := 5
  T1 := T141_86
  T2 := Q2.T141_86_2
  h1 := (3,0,1,1,2)
  h2 := (3,0,1,1,2)
  D := [[3, 1, 1, 4], [3, 1, 3, 1], [3, 1, 0, 3], [3, 1, 2, 0], [3, 1, 4, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_86_17 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨86, by decide⟩
  m := 5
  T1 := T141_86
  T2 := Q2.T141_86_2
  h1 := (3,0,2,0,2)
  h2 := (3,0,2,0,2)
  D := [[3, 2, 0, 2], [3, 2, 2, 0], [3, 2, 4, 3], [3, 2, 1, 1], [3, 2, 3, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_86_18 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨86, by decide⟩
  m := 5
  T1 := T141_86
  T2 := Q2.T141_86_2
  h1 := (3,0,3,4,2)
  h2 := (3,0,3,4,2)
  D := [[3, 3, 4, 0], [3, 3, 1, 4], [3, 3, 3, 3], [3, 3, 0, 2], [3, 3, 2, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_86_19 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨86, by decide⟩
  m := 5
  T1 := T141_86
  T2 := Q2.T141_86_2
  h1 := (3,0,4,3,2)
  h2 := (3,0,4,3,2)
  D := [[3, 4, 3, 3], [3, 4, 0, 3], [3, 4, 2, 3], [3, 4, 4, 3], [3, 4, 1, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_86_20 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨86, by decide⟩
  m := 5
  T1 := T141_86
  T2 := Q2.T141_86_2
  h1 := (4,0,0,1,4)
  h2 := (4,0,0,1,4)
  D := [[4, 0, 1, 0], [4, 0, 2, 0], [4, 0, 3, 0], [4, 0, 4, 0], [4, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_86_21 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨86, by decide⟩
  m := 5
  T1 := T141_86
  T2 := Q2.T141_86_2
  h1 := (4,0,1,0,4)
  h2 := (4,0,1,0,4)
  D := [[4, 1, 0, 4], [4, 1, 1, 0], [4, 1, 2, 1], [4, 1, 3, 2], [4, 1, 4, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_86_22 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨86, by decide⟩
  m := 5
  T1 := T141_86
  T2 := Q2.T141_86_2
  h1 := (4,0,2,4,4)
  h2 := (4,0,2,4,4)
  D := [[4, 2, 4, 3], [4, 2, 0, 0], [4, 2, 1, 2], [4, 2, 2, 4], [4, 2, 3, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_86_23 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨86, by decide⟩
  m := 5
  T1 := T141_86
  T2 := Q2.T141_86_2
  h1 := (4,0,3,3,4)
  h2 := (4,0,3,3,4)
  D := [[4, 3, 3, 2], [4, 3, 4, 0], [4, 3, 0, 3], [4, 3, 1, 1], [4, 3, 2, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_86_24 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨86, by decide⟩
  m := 5
  T1 := T141_86
  T2 := Q2.T141_86_2
  h1 := (4,0,4,2,4)
  h2 := (4,0,4,2,4)
  D := [[4, 4, 2, 1], [4, 4, 3, 0], [4, 4, 4, 4], [4, 4, 0, 3], [4, 4, 1, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_87_0 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨87, by decide⟩
  m := 5
  T1 := T141_87
  T2 := Q2.T141_87_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_87_1 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨87, by decide⟩
  m := 5
  T1 := T141_87
  T2 := Q2.T141_87_2
  h1 := (0,0,1,3,0)
  h2 := (0,0,1,3,0)
  D := [[0, 1, 3, 0], [0, 1, 3, 1], [0, 1, 3, 2], [0, 1, 3, 3], [0, 1, 3, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_87_2 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨87, by decide⟩
  m := 5
  T1 := T141_87
  T2 := Q2.T141_87_2
  h1 := (0,0,2,1,0)
  h2 := (0,0,2,1,0)
  D := [[0, 2, 1, 0], [0, 2, 1, 2], [0, 2, 1, 4], [0, 2, 1, 1], [0, 2, 1, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_87_3 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨87, by decide⟩
  m := 5
  T1 := T141_87
  T2 := Q2.T141_87_2
  h1 := (0,0,3,4,0)
  h2 := (0,0,3,4,0)
  D := [[0, 3, 4, 0], [0, 3, 4, 3], [0, 3, 4, 1], [0, 3, 4, 4], [0, 3, 4, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_87_4 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨87, by decide⟩
  m := 5
  T1 := T141_87
  T2 := Q2.T141_87_2
  h1 := (0,0,4,2,0)
  h2 := (0,0,4,2,0)
  D := [[0, 4, 2, 0], [0, 4, 2, 4], [0, 4, 2, 3], [0, 4, 2, 2], [0, 4, 2, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_87_5 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨87, by decide⟩
  m := 5
  T1 := T141_87
  T2 := Q2.T141_87_2
  h1 := (1,0,0,4,0)
  h2 := (1,0,0,4,0)
  D := [[1, 0, 4, 1], [1, 0, 3, 2], [1, 0, 2, 3], [1, 0, 1, 4], [1, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_87_6 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨87, by decide⟩
  m := 5
  T1 := T141_87
  T2 := Q2.T141_87_2
  h1 := (1,0,1,2,0)
  h2 := (1,0,1,2,0)
  D := [[1, 1, 2, 3], [1, 1, 1, 0], [1, 1, 0, 2], [1, 1, 4, 4], [1, 1, 3, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_87_7 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨87, by decide⟩
  m := 5
  T1 := T141_87
  T2 := Q2.T141_87_2
  h1 := (1,0,2,0,0)
  h2 := (1,0,2,0,0)
  D := [[1, 2, 0, 0], [1, 2, 4, 3], [1, 2, 3, 1], [1, 2, 2, 4], [1, 2, 1, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_87_8 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨87, by decide⟩
  m := 5
  T1 := T141_87
  T2 := Q2.T141_87_2
  h1 := (1,0,3,3,0)
  h2 := (1,0,3,3,0)
  D := [[1, 3, 3, 2], [1, 3, 2, 1], [1, 3, 1, 0], [1, 3, 0, 4], [1, 3, 4, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_87_9 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨87, by decide⟩
  m := 5
  T1 := T141_87
  T2 := Q2.T141_87_2
  h1 := (1,0,4,1,0)
  h2 := (1,0,4,1,0)
  D := [[1, 4, 1, 4], [1, 4, 0, 4], [1, 4, 4, 4], [1, 4, 3, 4], [1, 4, 2, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_87_10 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨87, by decide⟩
  m := 5
  T1 := T141_87
  T2 := Q2.T141_87_2
  h1 := (2,0,0,3,4)
  h2 := (2,0,0,3,4)
  D := [[2, 0, 3, 3], [2, 0, 1, 1], [2, 0, 4, 4], [2, 0, 2, 2], [2, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_87_11 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨87, by decide⟩
  m := 5
  T1 := T141_87
  T2 := Q2.T141_87_2
  h1 := (2,0,1,1,4)
  h2 := (2,0,1,1,4)
  D := [[2, 1, 1, 2], [2, 1, 4, 1], [2, 1, 2, 0], [2, 1, 0, 4], [2, 1, 3, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_87_12 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨87, by decide⟩
  m := 5
  T1 := T141_87
  T2 := Q2.T141_87_2
  h1 := (2,0,2,4,4)
  h2 := (2,0,2,4,4)
  D := [[2, 2, 4, 1], [2, 2, 2, 1], [2, 2, 0, 1], [2, 2, 3, 1], [2, 2, 1, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_87_13 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨87, by decide⟩
  m := 5
  T1 := T141_87
  T2 := Q2.T141_87_2
  h1 := (2,0,3,2,4)
  h2 := (2,0,3,2,4)
  D := [[2, 3, 2, 0], [2, 3, 0, 1], [2, 3, 3, 2], [2, 3, 1, 3], [2, 3, 4, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_87_14 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨87, by decide⟩
  m := 5
  T1 := T141_87
  T2 := Q2.T141_87_2
  h1 := (2,0,4,0,4)
  h2 := (2,0,4,0,4)
  D := [[2, 4, 0, 4], [2, 4, 3, 1], [2, 4, 1, 3], [2, 4, 4, 0], [2, 4, 2, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_87_15 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨87, by decide⟩
  m := 5
  T1 := T141_87
  T2 := Q2.T141_87_2
  h1 := (3,0,0,2,2)
  h2 := (3,0,0,2,2)
  D := [[3, 0, 2, 1], [3, 0, 4, 2], [3, 0, 1, 3], [3, 0, 3, 4], [3, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_87_16 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨87, by decide⟩
  m := 5
  T1 := T141_87
  T2 := Q2.T141_87_2
  h1 := (3,0,1,0,2)
  h2 := (3,0,1,0,2)
  D := [[3, 1, 0, 2], [3, 1, 2, 4], [3, 1, 4, 1], [3, 1, 1, 3], [3, 1, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_87_17 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨87, by decide⟩
  m := 5
  T1 := T141_87
  T2 := Q2.T141_87_2
  h1 := (3,0,2,3,2)
  h2 := (3,0,2,3,2)
  D := [[3, 2, 3, 3], [3, 2, 0, 1], [3, 2, 2, 4], [3, 2, 4, 2], [3, 2, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_87_18 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨87, by decide⟩
  m := 5
  T1 := T141_87
  T2 := Q2.T141_87_2
  h1 := (3,0,3,1,2)
  h2 := (3,0,3,1,2)
  D := [[3, 3, 1, 4], [3, 3, 3, 3], [3, 3, 0, 2], [3, 3, 2, 1], [3, 3, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_87_19 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨87, by decide⟩
  m := 5
  T1 := T141_87
  T2 := Q2.T141_87_2
  h1 := (3,0,4,4,2)
  h2 := (3,0,4,4,2)
  D := [[3, 4, 4, 0], [3, 4, 1, 0], [3, 4, 3, 0], [3, 4, 0, 0], [3, 4, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_87_20 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨87, by decide⟩
  m := 5
  T1 := T141_87
  T2 := Q2.T141_87_2
  h1 := (4,0,0,1,4)
  h2 := (4,0,0,1,4)
  D := [[4, 0, 1, 0], [4, 0, 2, 0], [4, 0, 3, 0], [4, 0, 4, 0], [4, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_87_21 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨87, by decide⟩
  m := 5
  T1 := T141_87
  T2 := Q2.T141_87_2
  h1 := (4,0,1,4,4)
  h2 := (4,0,1,4,4)
  D := [[4, 1, 4, 3], [4, 1, 0, 4], [4, 1, 1, 0], [4, 1, 2, 1], [4, 1, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_87_22 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨87, by decide⟩
  m := 5
  T1 := T141_87
  T2 := Q2.T141_87_2
  h1 := (4,0,2,2,4)
  h2 := (4,0,2,2,4)
  D := [[4, 2, 2, 1], [4, 2, 3, 3], [4, 2, 4, 0], [4, 2, 0, 2], [4, 2, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_87_23 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨87, by decide⟩
  m := 5
  T1 := T141_87
  T2 := Q2.T141_87_2
  h1 := (4,0,3,0,4)
  h2 := (4,0,3,0,4)
  D := [[4, 3, 0, 4], [4, 3, 1, 2], [4, 3, 2, 0], [4, 3, 3, 3], [4, 3, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_87_24 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨87, by decide⟩
  m := 5
  T1 := T141_87
  T2 := Q2.T141_87_2
  h1 := (4,0,4,3,4)
  h2 := (4,0,4,3,4)
  D := [[4, 4, 3, 2], [4, 4, 4, 1], [4, 4, 0, 0], [4, 4, 1, 4], [4, 4, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_88_0 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨88, by decide⟩
  m := 5
  T1 := T141_88
  T2 := Q2.T141_88_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_88_1 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨88, by decide⟩
  m := 5
  T1 := T141_88
  T2 := Q2.T141_88_2
  h1 := (0,0,1,2,0)
  h2 := (0,0,1,2,0)
  D := [[0, 1, 2, 0], [0, 1, 2, 1], [0, 1, 2, 2], [0, 1, 2, 3], [0, 1, 2, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_88_2 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨88, by decide⟩
  m := 5
  T1 := T141_88
  T2 := Q2.T141_88_2
  h1 := (0,0,2,4,0)
  h2 := (0,0,2,4,0)
  D := [[0, 2, 4, 0], [0, 2, 4, 2], [0, 2, 4, 4], [0, 2, 4, 1], [0, 2, 4, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_88_3 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨88, by decide⟩
  m := 5
  T1 := T141_88
  T2 := Q2.T141_88_2
  h1 := (0,0,3,1,0)
  h2 := (0,0,3,1,0)
  D := [[0, 3, 1, 0], [0, 3, 1, 3], [0, 3, 1, 1], [0, 3, 1, 4], [0, 3, 1, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_88_4 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨88, by decide⟩
  m := 5
  T1 := T141_88
  T2 := Q2.T141_88_2
  h1 := (0,0,4,3,0)
  h2 := (0,0,4,3,0)
  D := [[0, 4, 3, 0], [0, 4, 3, 4], [0, 4, 3, 3], [0, 4, 3, 2], [0, 4, 3, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_88_5 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨88, by decide⟩
  m := 5
  T1 := T141_88
  T2 := Q2.T141_88_2
  h1 := (1,0,0,4,0)
  h2 := (1,0,0,4,0)
  D := [[1, 0, 4, 1], [1, 0, 3, 2], [1, 0, 2, 3], [1, 0, 1, 4], [1, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_88_6 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨88, by decide⟩
  m := 5
  T1 := T141_88
  T2 := Q2.T141_88_2
  h1 := (1,0,1,1,0)
  h2 := (1,0,1,1,0)
  D := [[1, 1, 1, 4], [1, 1, 0, 1], [1, 1, 4, 3], [1, 1, 3, 0], [1, 1, 2, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_88_7 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨88, by decide⟩
  m := 5
  T1 := T141_88
  T2 := Q2.T141_88_2
  h1 := (1,0,2,3,0)
  h2 := (1,0,2,3,0)
  D := [[1, 2, 3, 2], [1, 2, 2, 0], [1, 2, 1, 3], [1, 2, 0, 1], [1, 2, 4, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_88_8 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨88, by decide⟩
  m := 5
  T1 := T141_88
  T2 := Q2.T141_88_2
  h1 := (1,0,3,0,0)
  h2 := (1,0,3,0,0)
  D := [[1, 3, 0, 0], [1, 3, 4, 4], [1, 3, 3, 3], [1, 3, 2, 2], [1, 3, 1, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_88_9 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨88, by decide⟩
  m := 5
  T1 := T141_88
  T2 := Q2.T141_88_2
  h1 := (1,0,4,2,0)
  h2 := (1,0,4,2,0)
  D := [[1, 4, 2, 3], [1, 4, 1, 3], [1, 4, 0, 3], [1, 4, 4, 3], [1, 4, 3, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_88_10 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨88, by decide⟩
  m := 5
  T1 := T141_88
  T2 := Q2.T141_88_2
  h1 := (2,0,0,3,4)
  h2 := (2,0,0,3,4)
  D := [[2, 0, 3, 3], [2, 0, 1, 1], [2, 0, 4, 4], [2, 0, 2, 2], [2, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_88_11 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨88, by decide⟩
  m := 5
  T1 := T141_88
  T2 := Q2.T141_88_2
  h1 := (2,0,1,0,4)
  h2 := (2,0,1,0,4)
  D := [[2, 1, 0, 4], [2, 1, 3, 3], [2, 1, 1, 2], [2, 1, 4, 1], [2, 1, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_88_12 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨88, by decide⟩
  m := 5
  T1 := T141_88
  T2 := Q2.T141_88_2
  h1 := (2,0,2,2,4)
  h2 := (2,0,2,2,4)
  D := [[2, 2, 2, 0], [2, 2, 0, 0], [2, 2, 3, 0], [2, 2, 1, 0], [2, 2, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_88_13 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨88, by decide⟩
  m := 5
  T1 := T141_88
  T2 := Q2.T141_88_2
  h1 := (2,0,3,4,4)
  h2 := (2,0,3,4,4)
  D := [[2, 3, 4, 1], [2, 3, 2, 2], [2, 3, 0, 3], [2, 3, 3, 4], [2, 3, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_88_14 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨88, by decide⟩
  m := 5
  T1 := T141_88
  T2 := Q2.T141_88_2
  h1 := (2,0,4,1,4)
  h2 := (2,0,4,1,4)
  D := [[2, 4, 1, 2], [2, 4, 4, 4], [2, 4, 2, 1], [2, 4, 0, 3], [2, 4, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_88_15 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨88, by decide⟩
  m := 5
  T1 := T141_88
  T2 := Q2.T141_88_2
  h1 := (3,0,0,2,2)
  h2 := (3,0,0,2,2)
  D := [[3, 0, 2, 1], [3, 0, 4, 2], [3, 0, 1, 3], [3, 0, 3, 4], [3, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_141_88_16 : ColCert where
  rK := ⟨141, by decide⟩
  rH := ⟨88, by decide⟩
  m := 5
  T1 := T141_88
  T2 := Q2.T141_88_2
  h1 := (3,0,1,4,2)
  h2 := (3,0,1,4,2)
  D := [[3, 1, 4, 0], [3, 1, 1, 2], [3, 1, 3, 4], [3, 1, 0, 1], [3, 1, 2, 3]]
  bind1 := by decide
  bind2 := by decide

end LeanDring.P5Presentation
