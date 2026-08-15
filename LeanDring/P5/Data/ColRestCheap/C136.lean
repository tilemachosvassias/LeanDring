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
rest tier, chunk 135: 60 columns.
-/

-- machine-emitted data: silence style linters (generated long lines, file-level options)
set_option linter.style.longLine false

namespace LeanDring.P5Presentation

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

def colCert_147_145_3 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨145, by decide⟩
  m := 1
  T1 := T147_145
  T2 := Q2.T147_145_2
  h1 := (0,3,3,0,3)
  h2 := (0,3,3,0,3)
  D := [[0, 3, 3, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_145_4 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨145, by decide⟩
  m := 1
  T1 := T147_145
  T2 := Q2.T147_145_2
  h1 := (0,4,4,0,1)
  h2 := (0,4,4,0,1)
  D := [[0, 4, 4, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_145_5 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨145, by decide⟩
  m := 1
  T1 := T147_145
  T2 := Q2.T147_145_2
  h1 := (1,0,0,0,0)
  h2 := (1,0,0,0,0)
  D := [[1, 0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_145_6 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨145, by decide⟩
  m := 1
  T1 := T147_145
  T2 := Q2.T147_145_2
  h1 := (1,1,1,0,0)
  h2 := (1,1,1,0,0)
  D := [[1, 1, 1, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_145_7 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨145, by decide⟩
  m := 1
  T1 := T147_145
  T2 := Q2.T147_145_2
  h1 := (1,2,2,0,1)
  h2 := (1,2,2,0,1)
  D := [[1, 2, 2, 3, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_145_8 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨145, by decide⟩
  m := 1
  T1 := T147_145
  T2 := Q2.T147_145_2
  h1 := (1,3,3,0,3)
  h2 := (1,3,3,0,3)
  D := [[1, 3, 3, 2, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_145_9 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨145, by decide⟩
  m := 1
  T1 := T147_145
  T2 := Q2.T147_145_2
  h1 := (1,4,4,0,1)
  h2 := (1,4,4,0,1)
  D := [[1, 4, 4, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_145_10 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨145, by decide⟩
  m := 1
  T1 := T147_145
  T2 := Q2.T147_145_2
  h1 := (2,0,0,0,0)
  h2 := (2,0,0,0,0)
  D := [[2, 0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_145_11 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨145, by decide⟩
  m := 1
  T1 := T147_145
  T2 := Q2.T147_145_2
  h1 := (2,1,1,0,0)
  h2 := (2,1,1,0,0)
  D := [[2, 1, 1, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_145_12 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨145, by decide⟩
  m := 1
  T1 := T147_145
  T2 := Q2.T147_145_2
  h1 := (2,2,2,0,1)
  h2 := (2,2,2,0,1)
  D := [[2, 2, 2, 1, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_145_13 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨145, by decide⟩
  m := 1
  T1 := T147_145
  T2 := Q2.T147_145_2
  h1 := (2,3,3,0,3)
  h2 := (2,3,3,0,3)
  D := [[2, 3, 3, 4, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_145_14 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨145, by decide⟩
  m := 1
  T1 := T147_145
  T2 := Q2.T147_145_2
  h1 := (2,4,4,0,1)
  h2 := (2,4,4,0,1)
  D := [[2, 4, 4, 2, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_145_15 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨145, by decide⟩
  m := 1
  T1 := T147_145
  T2 := Q2.T147_145_2
  h1 := (3,0,0,0,0)
  h2 := (3,0,0,0,0)
  D := [[3, 0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_145_16 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨145, by decide⟩
  m := 1
  T1 := T147_145
  T2 := Q2.T147_145_2
  h1 := (3,1,1,0,0)
  h2 := (3,1,1,0,0)
  D := [[3, 1, 1, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_145_17 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨145, by decide⟩
  m := 1
  T1 := T147_145
  T2 := Q2.T147_145_2
  h1 := (3,2,2,0,1)
  h2 := (3,2,2,0,1)
  D := [[3, 2, 2, 4, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_145_18 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨145, by decide⟩
  m := 1
  T1 := T147_145
  T2 := Q2.T147_145_2
  h1 := (3,3,3,0,3)
  h2 := (3,3,3,0,3)
  D := [[3, 3, 3, 1, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_145_19 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨145, by decide⟩
  m := 1
  T1 := T147_145
  T2 := Q2.T147_145_2
  h1 := (3,4,4,0,1)
  h2 := (3,4,4,0,1)
  D := [[3, 4, 4, 3, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_145_20 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨145, by decide⟩
  m := 1
  T1 := T147_145
  T2 := Q2.T147_145_2
  h1 := (4,0,0,0,0)
  h2 := (4,0,0,0,0)
  D := [[4, 0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_145_21 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨145, by decide⟩
  m := 1
  T1 := T147_145
  T2 := Q2.T147_145_2
  h1 := (4,1,1,0,0)
  h2 := (4,1,1,0,0)
  D := [[4, 1, 1, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_145_22 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨145, by decide⟩
  m := 1
  T1 := T147_145
  T2 := Q2.T147_145_2
  h1 := (4,2,2,0,1)
  h2 := (4,2,2,0,1)
  D := [[4, 2, 2, 2, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_145_23 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨145, by decide⟩
  m := 1
  T1 := T147_145
  T2 := Q2.T147_145_2
  h1 := (4,3,3,0,3)
  h2 := (4,3,3,0,3)
  D := [[4, 3, 3, 3, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_145_24 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨145, by decide⟩
  m := 1
  T1 := T147_145
  T2 := Q2.T147_145_2
  h1 := (4,4,4,0,1)
  h2 := (4,4,4,0,1)
  D := [[4, 4, 4, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_146_0 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨146, by decide⟩
  m := 1
  T1 := T147_146
  T2 := Q2.T147_146_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_146_1 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨146, by decide⟩
  m := 1
  T1 := T147_146
  T2 := Q2.T147_146_2
  h1 := (0,1,0,0,0)
  h2 := (0,1,0,0,0)
  D := [[0, 1, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_146_2 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨146, by decide⟩
  m := 1
  T1 := T147_146
  T2 := Q2.T147_146_2
  h1 := (0,2,0,0,0)
  h2 := (0,2,0,0,0)
  D := [[0, 2, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_146_3 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨146, by decide⟩
  m := 1
  T1 := T147_146
  T2 := Q2.T147_146_2
  h1 := (0,3,0,0,0)
  h2 := (0,3,0,0,0)
  D := [[0, 3, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_146_4 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨146, by decide⟩
  m := 1
  T1 := T147_146
  T2 := Q2.T147_146_2
  h1 := (0,4,0,0,0)
  h2 := (0,4,0,0,0)
  D := [[0, 4, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_146_5 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨146, by decide⟩
  m := 1
  T1 := T147_146
  T2 := Q2.T147_146_2
  h1 := (1,0,0,0,0)
  h2 := (1,0,0,0,0)
  D := [[1, 0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_146_6 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨146, by decide⟩
  m := 1
  T1 := T147_146
  T2 := Q2.T147_146_2
  h1 := (1,1,0,0,0)
  h2 := (1,1,0,0,0)
  D := [[1, 1, 0, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_146_7 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨146, by decide⟩
  m := 1
  T1 := T147_146
  T2 := Q2.T147_146_2
  h1 := (1,2,0,0,0)
  h2 := (1,2,0,0,0)
  D := [[1, 2, 0, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_146_8 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨146, by decide⟩
  m := 1
  T1 := T147_146
  T2 := Q2.T147_146_2
  h1 := (1,3,0,0,0)
  h2 := (1,3,0,0,0)
  D := [[1, 3, 0, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_146_9 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨146, by decide⟩
  m := 1
  T1 := T147_146
  T2 := Q2.T147_146_2
  h1 := (1,4,0,0,0)
  h2 := (1,4,0,0,0)
  D := [[1, 4, 0, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_146_10 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨146, by decide⟩
  m := 1
  T1 := T147_146
  T2 := Q2.T147_146_2
  h1 := (2,0,0,0,0)
  h2 := (2,0,0,0,0)
  D := [[2, 0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_146_11 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨146, by decide⟩
  m := 1
  T1 := T147_146
  T2 := Q2.T147_146_2
  h1 := (2,1,0,0,0)
  h2 := (2,1,0,0,0)
  D := [[2, 1, 0, 3, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_146_12 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨146, by decide⟩
  m := 1
  T1 := T147_146
  T2 := Q2.T147_146_2
  h1 := (2,2,0,0,0)
  h2 := (2,2,0,0,0)
  D := [[2, 2, 0, 1, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_146_13 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨146, by decide⟩
  m := 1
  T1 := T147_146
  T2 := Q2.T147_146_2
  h1 := (2,3,0,0,0)
  h2 := (2,3,0,0,0)
  D := [[2, 3, 0, 4, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_146_14 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨146, by decide⟩
  m := 1
  T1 := T147_146
  T2 := Q2.T147_146_2
  h1 := (2,4,0,0,0)
  h2 := (2,4,0,0,0)
  D := [[2, 4, 0, 2, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_146_15 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨146, by decide⟩
  m := 1
  T1 := T147_146
  T2 := Q2.T147_146_2
  h1 := (3,0,0,0,0)
  h2 := (3,0,0,0,0)
  D := [[3, 0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_146_16 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨146, by decide⟩
  m := 1
  T1 := T147_146
  T2 := Q2.T147_146_2
  h1 := (3,1,0,0,0)
  h2 := (3,1,0,0,0)
  D := [[3, 1, 0, 2, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_146_17 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨146, by decide⟩
  m := 1
  T1 := T147_146
  T2 := Q2.T147_146_2
  h1 := (3,2,0,0,0)
  h2 := (3,2,0,0,0)
  D := [[3, 2, 0, 4, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_146_18 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨146, by decide⟩
  m := 1
  T1 := T147_146
  T2 := Q2.T147_146_2
  h1 := (3,3,0,0,0)
  h2 := (3,3,0,0,0)
  D := [[3, 3, 0, 1, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_146_19 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨146, by decide⟩
  m := 1
  T1 := T147_146
  T2 := Q2.T147_146_2
  h1 := (3,4,0,0,0)
  h2 := (3,4,0,0,0)
  D := [[3, 4, 0, 3, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_146_20 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨146, by decide⟩
  m := 1
  T1 := T147_146
  T2 := Q2.T147_146_2
  h1 := (4,0,0,0,0)
  h2 := (4,0,0,0,0)
  D := [[4, 0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_146_21 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨146, by decide⟩
  m := 1
  T1 := T147_146
  T2 := Q2.T147_146_2
  h1 := (4,1,0,0,0)
  h2 := (4,1,0,0,0)
  D := [[4, 1, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_146_22 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨146, by decide⟩
  m := 1
  T1 := T147_146
  T2 := Q2.T147_146_2
  h1 := (4,2,0,0,0)
  h2 := (4,2,0,0,0)
  D := [[4, 2, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_146_23 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨146, by decide⟩
  m := 1
  T1 := T147_146
  T2 := Q2.T147_146_2
  h1 := (4,3,0,0,0)
  h2 := (4,3,0,0,0)
  D := [[4, 3, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_146_24 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨146, by decide⟩
  m := 1
  T1 := T147_146
  T2 := Q2.T147_146_2
  h1 := (4,4,0,0,0)
  h2 := (4,4,0,0,0)
  D := [[4, 4, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_147_0 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨147, by decide⟩
  m := 1
  T1 := T147_147
  T2 := Q2.T147_147_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_147_1 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨147, by decide⟩
  m := 1
  T1 := T147_147
  T2 := Q2.T147_147_2
  h1 := (0,0,1,0,0)
  h2 := (0,0,1,0,0)
  D := [[0, 0, 1, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_147_2 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨147, by decide⟩
  m := 1
  T1 := T147_147
  T2 := Q2.T147_147_2
  h1 := (0,0,2,0,0)
  h2 := (0,0,2,0,0)
  D := [[0, 0, 2, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_147_3 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨147, by decide⟩
  m := 1
  T1 := T147_147
  T2 := Q2.T147_147_2
  h1 := (0,0,3,0,0)
  h2 := (0,0,3,0,0)
  D := [[0, 0, 3, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_147_4 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨147, by decide⟩
  m := 1
  T1 := T147_147
  T2 := Q2.T147_147_2
  h1 := (0,0,4,0,0)
  h2 := (0,0,4,0,0)
  D := [[0, 0, 4, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_147_5 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨147, by decide⟩
  m := 1
  T1 := T147_147
  T2 := Q2.T147_147_2
  h1 := (0,1,0,0,0)
  h2 := (0,1,0,0,0)
  D := [[0, 1, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_147_6 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨147, by decide⟩
  m := 1
  T1 := T147_147
  T2 := Q2.T147_147_2
  h1 := (0,1,1,0,0)
  h2 := (0,1,1,0,0)
  D := [[0, 1, 1, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_147_7 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨147, by decide⟩
  m := 1
  T1 := T147_147
  T2 := Q2.T147_147_2
  h1 := (0,1,2,0,0)
  h2 := (0,1,2,0,0)
  D := [[0, 1, 2, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_147_8 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨147, by decide⟩
  m := 1
  T1 := T147_147
  T2 := Q2.T147_147_2
  h1 := (0,1,3,0,0)
  h2 := (0,1,3,0,0)
  D := [[0, 1, 3, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_147_9 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨147, by decide⟩
  m := 1
  T1 := T147_147
  T2 := Q2.T147_147_2
  h1 := (0,1,4,0,0)
  h2 := (0,1,4,0,0)
  D := [[0, 1, 4, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_147_10 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨147, by decide⟩
  m := 1
  T1 := T147_147
  T2 := Q2.T147_147_2
  h1 := (0,2,0,0,0)
  h2 := (0,2,0,0,0)
  D := [[0, 2, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_147_11 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨147, by decide⟩
  m := 1
  T1 := T147_147
  T2 := Q2.T147_147_2
  h1 := (0,2,1,0,0)
  h2 := (0,2,1,0,0)
  D := [[0, 2, 1, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_147_12 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨147, by decide⟩
  m := 1
  T1 := T147_147
  T2 := Q2.T147_147_2
  h1 := (0,2,2,0,0)
  h2 := (0,2,2,0,0)
  D := [[0, 2, 2, 0, 1]]
  bind1 := by decide
  bind2 := by decide

end LeanDring.P5Presentation
