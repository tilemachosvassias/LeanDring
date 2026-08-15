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
rest tier, chunk 131: 60 columns.
-/

-- machine-emitted data: silence style linters (generated long lines, file-level options)
set_option linter.style.longLine false

namespace LeanDring.P5Presentation

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

def colCert_147_126_18 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨126, by decide⟩
  m := 1
  T1 := T147_126
  T2 := Q2.T147_126_2
  h1 := (3,3,1,0,3)
  h2 := (3,3,1,0,3)
  D := [[3, 3, 1, 1, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_126_19 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨126, by decide⟩
  m := 1
  T1 := T147_126
  T2 := Q2.T147_126_2
  h1 := (3,4,1,0,4)
  h2 := (3,4,1,0,4)
  D := [[3, 4, 1, 3, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_126_20 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨126, by decide⟩
  m := 1
  T1 := T147_126
  T2 := Q2.T147_126_2
  h1 := (4,0,3,0,0)
  h2 := (4,0,3,0,0)
  D := [[4, 0, 3, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_126_21 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨126, by decide⟩
  m := 1
  T1 := T147_126
  T2 := Q2.T147_126_2
  h1 := (4,1,3,0,3)
  h2 := (4,1,3,0,3)
  D := [[4, 1, 3, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_126_22 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨126, by decide⟩
  m := 1
  T1 := T147_126
  T2 := Q2.T147_126_2
  h1 := (4,2,3,0,1)
  h2 := (4,2,3,0,1)
  D := [[4, 2, 3, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_126_23 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨126, by decide⟩
  m := 1
  T1 := T147_126
  T2 := Q2.T147_126_2
  h1 := (4,3,3,0,4)
  h2 := (4,3,3,0,4)
  D := [[4, 3, 3, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_126_24 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨126, by decide⟩
  m := 1
  T1 := T147_126
  T2 := Q2.T147_126_2
  h1 := (4,4,3,0,2)
  h2 := (4,4,3,0,2)
  D := [[4, 4, 3, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_127_0 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨127, by decide⟩
  m := 1
  T1 := T147_127
  T2 := Q2.T147_127_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_127_9 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨127, by decide⟩
  m := 1
  T1 := T147_127
  T2 := Q2.T147_127_2
  h1 := (1,4,0,4,0)
  h2 := (1,4,0,4,0)
  D := [[1, 4, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_127_13 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨127, by decide⟩
  m := 1
  T1 := T147_127
  T2 := Q2.T147_127_2
  h1 := (2,3,0,3,2)
  h2 := (2,3,0,3,2)
  D := [[2, 3, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_127_17 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨127, by decide⟩
  m := 1
  T1 := T147_127
  T2 := Q2.T147_127_2
  h1 := (3,2,0,2,1)
  h2 := (3,2,0,2,1)
  D := [[3, 2, 0, 1, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_127_21 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨127, by decide⟩
  m := 1
  T1 := T147_127
  T2 := Q2.T147_127_2
  h1 := (4,1,0,1,2)
  h2 := (4,1,0,1,2)
  D := [[4, 1, 0, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_128_0 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨128, by decide⟩
  m := 1
  T1 := T147_128
  T2 := Q2.T147_128_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_128_7 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨128, by decide⟩
  m := 1
  T1 := T147_128
  T2 := Q2.T147_128_2
  h1 := (1,2,0,3,3)
  h2 := (1,2,0,3,3)
  D := [[1, 2, 0, 1, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_128_14 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨128, by decide⟩
  m := 1
  T1 := T147_128
  T2 := Q2.T147_128_2
  h1 := (2,4,0,1,3)
  h2 := (2,4,0,1,3)
  D := [[2, 4, 0, 3, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_128_16 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨128, by decide⟩
  m := 1
  T1 := T147_128
  T2 := Q2.T147_128_2
  h1 := (3,1,0,4,0)
  h2 := (3,1,0,4,0)
  D := [[3, 1, 0, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_128_23 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨128, by decide⟩
  m := 1
  T1 := T147_128
  T2 := Q2.T147_128_2
  h1 := (4,3,0,2,4)
  h2 := (4,3,0,2,4)
  D := [[4, 3, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_129_0 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨129, by decide⟩
  m := 1
  T1 := T147_129
  T2 := Q2.T147_129_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_129_1 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨129, by decide⟩
  m := 1
  T1 := T147_129
  T2 := Q2.T147_129_2
  h1 := (0,1,1,0,0)
  h2 := (0,1,1,0,0)
  D := [[0, 1, 1, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_129_2 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨129, by decide⟩
  m := 1
  T1 := T147_129
  T2 := Q2.T147_129_2
  h1 := (0,2,2,0,1)
  h2 := (0,2,2,0,1)
  D := [[0, 2, 2, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_129_3 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨129, by decide⟩
  m := 1
  T1 := T147_129
  T2 := Q2.T147_129_2
  h1 := (0,3,3,0,3)
  h2 := (0,3,3,0,3)
  D := [[0, 3, 3, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_129_4 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨129, by decide⟩
  m := 1
  T1 := T147_129
  T2 := Q2.T147_129_2
  h1 := (0,4,4,0,1)
  h2 := (0,4,4,0,1)
  D := [[0, 4, 4, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_129_5 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨129, by decide⟩
  m := 1
  T1 := T147_129
  T2 := Q2.T147_129_2
  h1 := (1,0,2,1,3)
  h2 := (1,0,2,1,3)
  D := [[1, 0, 2, 1, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_129_6 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨129, by decide⟩
  m := 1
  T1 := T147_129
  T2 := Q2.T147_129_2
  h1 := (1,1,3,1,0)
  h2 := (1,1,3,1,0)
  D := [[1, 1, 3, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_129_7 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨129, by decide⟩
  m := 1
  T1 := T147_129
  T2 := Q2.T147_129_2
  h1 := (1,2,4,1,3)
  h2 := (1,2,4,1,3)
  D := [[1, 2, 4, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_129_8 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨129, by decide⟩
  m := 1
  T1 := T147_129
  T2 := Q2.T147_129_2
  h1 := (1,3,0,1,2)
  h2 := (1,3,0,1,2)
  D := [[1, 3, 0, 3, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_129_9 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨129, by decide⟩
  m := 1
  T1 := T147_129
  T2 := Q2.T147_129_2
  h1 := (1,4,1,1,2)
  h2 := (1,4,1,1,2)
  D := [[1, 4, 1, 2, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_129_10 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨129, by decide⟩
  m := 1
  T1 := T147_129
  T2 := Q2.T147_129_2
  h1 := (2,0,4,2,2)
  h2 := (2,0,4,2,2)
  D := [[2, 0, 4, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_129_11 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨129, by decide⟩
  m := 1
  T1 := T147_129
  T2 := Q2.T147_129_2
  h1 := (2,1,0,2,1)
  h2 := (2,1,0,2,1)
  D := [[2, 1, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_129_12 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨129, by decide⟩
  m := 1
  T1 := T147_129
  T2 := Q2.T147_129_2
  h1 := (2,2,1,2,1)
  h2 := (2,2,1,2,1)
  D := [[2, 2, 1, 3, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_129_13 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨129, by decide⟩
  m := 1
  T1 := T147_129
  T2 := Q2.T147_129_2
  h1 := (2,3,2,2,2)
  h2 := (2,3,2,2,2)
  D := [[2, 3, 2, 1, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_129_14 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨129, by decide⟩
  m := 1
  T1 := T147_129
  T2 := Q2.T147_129_2
  h1 := (2,4,3,2,4)
  h2 := (2,4,3,2,4)
  D := [[2, 4, 3, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_129_15 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨129, by decide⟩
  m := 1
  T1 := T147_129
  T2 := Q2.T147_129_2
  h1 := (3,0,1,3,2)
  h2 := (3,0,1,3,2)
  D := [[3, 0, 1, 3, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_129_16 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨129, by decide⟩
  m := 1
  T1 := T147_129
  T2 := Q2.T147_129_2
  h1 := (3,1,2,3,3)
  h2 := (3,1,2,3,3)
  D := [[3, 1, 2, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_129_17 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨129, by decide⟩
  m := 1
  T1 := T147_129
  T2 := Q2.T147_129_2
  h1 := (3,2,3,3,0)
  h2 := (3,2,3,3,0)
  D := [[3, 2, 3, 2, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_129_18 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨129, by decide⟩
  m := 1
  T1 := T147_129
  T2 := Q2.T147_129_2
  h1 := (3,3,4,3,3)
  h2 := (3,3,4,3,3)
  D := [[3, 3, 4, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_129_19 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨129, by decide⟩
  m := 1
  T1 := T147_129
  T2 := Q2.T147_129_2
  h1 := (3,4,0,3,2)
  h2 := (3,4,0,3,2)
  D := [[3, 4, 0, 1, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_129_20 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨129, by decide⟩
  m := 1
  T1 := T147_129
  T2 := Q2.T147_129_2
  h1 := (4,0,3,4,3)
  h2 := (4,0,3,4,3)
  D := [[4, 0, 3, 4, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_129_21 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨129, by decide⟩
  m := 1
  T1 := T147_129
  T2 := Q2.T147_129_2
  h1 := (4,1,4,4,1)
  h2 := (4,1,4,4,1)
  D := [[4, 1, 4, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_129_22 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨129, by decide⟩
  m := 1
  T1 := T147_129
  T2 := Q2.T147_129_2
  h1 := (4,2,0,4,0)
  h2 := (4,2,0,4,0)
  D := [[4, 2, 0, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_129_23 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨129, by decide⟩
  m := 1
  T1 := T147_129
  T2 := Q2.T147_129_2
  h1 := (4,3,1,4,0)
  h2 := (4,3,1,4,0)
  D := [[4, 3, 1, 2, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_129_24 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨129, by decide⟩
  m := 1
  T1 := T147_129
  T2 := Q2.T147_129_2
  h1 := (4,4,2,4,1)
  h2 := (4,4,2,4,1)
  D := [[4, 4, 2, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_130_0 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨130, by decide⟩
  m := 1
  T1 := T147_130
  T2 := Q2.T147_130_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_130_6 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨130, by decide⟩
  m := 1
  T1 := T147_130
  T2 := Q2.T147_130_2
  h1 := (1,1,0,0,0)
  h2 := (1,1,0,0,0)
  D := [[1, 1, 0, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_130_12 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨130, by decide⟩
  m := 1
  T1 := T147_130
  T2 := Q2.T147_130_2
  h1 := (2,2,0,0,2)
  h2 := (2,2,0,0,2)
  D := [[2, 2, 0, 1, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_130_18 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨130, by decide⟩
  m := 1
  T1 := T147_130
  T2 := Q2.T147_130_2
  h1 := (3,3,0,0,1)
  h2 := (3,3,0,0,1)
  D := [[3, 3, 0, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_130_24 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨130, by decide⟩
  m := 1
  T1 := T147_130
  T2 := Q2.T147_130_2
  h1 := (4,4,0,0,2)
  h2 := (4,4,0,0,2)
  D := [[4, 4, 0, 4, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_131_0 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨131, by decide⟩
  m := 1
  T1 := T147_131
  T2 := Q2.T147_131_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_131_1 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨131, by decide⟩
  m := 1
  T1 := T147_131
  T2 := Q2.T147_131_2
  h1 := (0,1,0,0,0)
  h2 := (0,1,0,0,0)
  D := [[0, 1, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_131_2 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨131, by decide⟩
  m := 1
  T1 := T147_131
  T2 := Q2.T147_131_2
  h1 := (0,2,0,0,0)
  h2 := (0,2,0,0,0)
  D := [[0, 2, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_131_3 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨131, by decide⟩
  m := 1
  T1 := T147_131
  T2 := Q2.T147_131_2
  h1 := (0,3,0,0,0)
  h2 := (0,3,0,0,0)
  D := [[0, 3, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_131_4 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨131, by decide⟩
  m := 1
  T1 := T147_131
  T2 := Q2.T147_131_2
  h1 := (0,4,0,0,0)
  h2 := (0,4,0,0,0)
  D := [[0, 4, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_131_5 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨131, by decide⟩
  m := 1
  T1 := T147_131
  T2 := Q2.T147_131_2
  h1 := (1,0,3,0,0)
  h2 := (1,0,3,0,0)
  D := [[1, 0, 3, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_131_6 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨131, by decide⟩
  m := 1
  T1 := T147_131
  T2 := Q2.T147_131_2
  h1 := (1,1,3,0,3)
  h2 := (1,1,3,0,3)
  D := [[1, 1, 3, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_131_7 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨131, by decide⟩
  m := 1
  T1 := T147_131
  T2 := Q2.T147_131_2
  h1 := (1,2,3,0,1)
  h2 := (1,2,3,0,1)
  D := [[1, 2, 3, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_131_8 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨131, by decide⟩
  m := 1
  T1 := T147_131
  T2 := Q2.T147_131_2
  h1 := (1,3,3,0,4)
  h2 := (1,3,3,0,4)
  D := [[1, 3, 3, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_131_9 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨131, by decide⟩
  m := 1
  T1 := T147_131
  T2 := Q2.T147_131_2
  h1 := (1,4,3,0,2)
  h2 := (1,4,3,0,2)
  D := [[1, 4, 3, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_131_10 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨131, by decide⟩
  m := 1
  T1 := T147_131
  T2 := Q2.T147_131_2
  h1 := (2,0,1,0,0)
  h2 := (2,0,1,0,0)
  D := [[2, 0, 1, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_131_11 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨131, by decide⟩
  m := 1
  T1 := T147_131
  T2 := Q2.T147_131_2
  h1 := (2,1,1,0,1)
  h2 := (2,1,1,0,1)
  D := [[2, 1, 1, 3, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_131_12 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨131, by decide⟩
  m := 1
  T1 := T147_131
  T2 := Q2.T147_131_2
  h1 := (2,2,1,0,2)
  h2 := (2,2,1,0,2)
  D := [[2, 2, 1, 1, 1]]
  bind1 := by decide
  bind2 := by decide

end LeanDring.P5Presentation
