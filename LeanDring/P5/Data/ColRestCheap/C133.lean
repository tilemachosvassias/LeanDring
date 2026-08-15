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
rest tier, chunk 132: 60 columns.
-/

-- machine-emitted data: silence style linters (generated long lines, file-level options)
set_option linter.style.longLine false

namespace LeanDring.P5Presentation

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

def colCert_147_131_13 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨131, by decide⟩
  m := 1
  T1 := T147_131
  T2 := Q2.T147_131_2
  h1 := (2,3,1,0,3)
  h2 := (2,3,1,0,3)
  D := [[2, 3, 1, 4, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_131_14 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨131, by decide⟩
  m := 1
  T1 := T147_131
  T2 := Q2.T147_131_2
  h1 := (2,4,1,0,4)
  h2 := (2,4,1,0,4)
  D := [[2, 4, 1, 2, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_131_15 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨131, by decide⟩
  m := 1
  T1 := T147_131
  T2 := Q2.T147_131_2
  h1 := (3,0,4,0,0)
  h2 := (3,0,4,0,0)
  D := [[3, 0, 4, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_131_16 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨131, by decide⟩
  m := 1
  T1 := T147_131
  T2 := Q2.T147_131_2
  h1 := (3,1,4,0,4)
  h2 := (3,1,4,0,4)
  D := [[3, 1, 4, 2, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_131_17 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨131, by decide⟩
  m := 1
  T1 := T147_131
  T2 := Q2.T147_131_2
  h1 := (3,2,4,0,3)
  h2 := (3,2,4,0,3)
  D := [[3, 2, 4, 4, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_131_18 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨131, by decide⟩
  m := 1
  T1 := T147_131
  T2 := Q2.T147_131_2
  h1 := (3,3,4,0,2)
  h2 := (3,3,4,0,2)
  D := [[3, 3, 4, 1, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_131_19 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨131, by decide⟩
  m := 1
  T1 := T147_131
  T2 := Q2.T147_131_2
  h1 := (3,4,4,0,1)
  h2 := (3,4,4,0,1)
  D := [[3, 4, 4, 3, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_131_20 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨131, by decide⟩
  m := 1
  T1 := T147_131
  T2 := Q2.T147_131_2
  h1 := (4,0,2,0,0)
  h2 := (4,0,2,0,0)
  D := [[4, 0, 2, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_131_21 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨131, by decide⟩
  m := 1
  T1 := T147_131
  T2 := Q2.T147_131_2
  h1 := (4,1,2,0,2)
  h2 := (4,1,2,0,2)
  D := [[4, 1, 2, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_131_22 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨131, by decide⟩
  m := 1
  T1 := T147_131
  T2 := Q2.T147_131_2
  h1 := (4,2,2,0,4)
  h2 := (4,2,2,0,4)
  D := [[4, 2, 2, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_131_23 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨131, by decide⟩
  m := 1
  T1 := T147_131
  T2 := Q2.T147_131_2
  h1 := (4,3,2,0,1)
  h2 := (4,3,2,0,1)
  D := [[4, 3, 2, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_131_24 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨131, by decide⟩
  m := 1
  T1 := T147_131
  T2 := Q2.T147_131_2
  h1 := (4,4,2,0,3)
  h2 := (4,4,2,0,3)
  D := [[4, 4, 2, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_132_0 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨132, by decide⟩
  m := 1
  T1 := T147_132
  T2 := Q2.T147_132_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_132_9 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨132, by decide⟩
  m := 1
  T1 := T147_132
  T2 := Q2.T147_132_2
  h1 := (1,4,0,4,0)
  h2 := (1,4,0,4,0)
  D := [[1, 4, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_132_13 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨132, by decide⟩
  m := 1
  T1 := T147_132
  T2 := Q2.T147_132_2
  h1 := (2,3,0,3,1)
  h2 := (2,3,0,3,1)
  D := [[2, 3, 0, 2, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_132_17 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨132, by decide⟩
  m := 1
  T1 := T147_132
  T2 := Q2.T147_132_2
  h1 := (3,2,0,2,3)
  h2 := (3,2,0,2,3)
  D := [[3, 2, 0, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_132_21 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨132, by decide⟩
  m := 1
  T1 := T147_132
  T2 := Q2.T147_132_2
  h1 := (4,1,0,1,1)
  h2 := (4,1,0,1,1)
  D := [[4, 1, 0, 2, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_133_0 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨133, by decide⟩
  m := 1
  T1 := T147_133
  T2 := Q2.T147_133_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_133_1 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨133, by decide⟩
  m := 1
  T1 := T147_133
  T2 := Q2.T147_133_2
  h1 := (0,1,1,0,0)
  h2 := (0,1,1,0,0)
  D := [[0, 1, 1, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_133_2 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨133, by decide⟩
  m := 1
  T1 := T147_133
  T2 := Q2.T147_133_2
  h1 := (0,2,2,0,1)
  h2 := (0,2,2,0,1)
  D := [[0, 2, 2, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_133_3 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨133, by decide⟩
  m := 1
  T1 := T147_133
  T2 := Q2.T147_133_2
  h1 := (0,3,3,0,3)
  h2 := (0,3,3,0,3)
  D := [[0, 3, 3, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_133_4 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨133, by decide⟩
  m := 1
  T1 := T147_133
  T2 := Q2.T147_133_2
  h1 := (0,4,4,0,1)
  h2 := (0,4,4,0,1)
  D := [[0, 4, 4, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_133_5 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨133, by decide⟩
  m := 1
  T1 := T147_133
  T2 := Q2.T147_133_2
  h1 := (1,0,3,3,1)
  h2 := (1,0,3,3,1)
  D := [[1, 0, 3, 3, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_133_6 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨133, by decide⟩
  m := 1
  T1 := T147_133
  T2 := Q2.T147_133_2
  h1 := (1,1,4,3,4)
  h2 := (1,1,4,3,4)
  D := [[1, 1, 4, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_133_7 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨133, by decide⟩
  m := 1
  T1 := T147_133
  T2 := Q2.T147_133_2
  h1 := (1,2,0,3,3)
  h2 := (1,2,0,3,3)
  D := [[1, 2, 0, 1, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_133_8 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨133, by decide⟩
  m := 1
  T1 := T147_133
  T2 := Q2.T147_133_2
  h1 := (1,3,1,3,3)
  h2 := (1,3,1,3,3)
  D := [[1, 3, 1, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_133_9 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨133, by decide⟩
  m := 1
  T1 := T147_133
  T2 := Q2.T147_133_2
  h1 := (1,4,2,3,4)
  h2 := (1,4,2,3,4)
  D := [[1, 4, 2, 4, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_133_10 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨133, by decide⟩
  m := 1
  T1 := T147_133
  T2 := Q2.T147_133_2
  h1 := (2,0,1,1,0)
  h2 := (2,0,1,1,0)
  D := [[2, 0, 1, 1, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_133_11 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨133, by decide⟩
  m := 1
  T1 := T147_133
  T2 := Q2.T147_133_2
  h1 := (2,1,2,1,1)
  h2 := (2,1,2,1,1)
  D := [[2, 1, 2, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_133_12 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨133, by decide⟩
  m := 1
  T1 := T147_133
  T2 := Q2.T147_133_2
  h1 := (2,2,3,1,3)
  h2 := (2,2,3,1,3)
  D := [[2, 2, 3, 2, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_133_13 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨133, by decide⟩
  m := 1
  T1 := T147_133
  T2 := Q2.T147_133_2
  h1 := (2,3,4,1,1)
  h2 := (2,3,4,1,1)
  D := [[2, 3, 4, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_133_14 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨133, by decide⟩
  m := 1
  T1 := T147_133
  T2 := Q2.T147_133_2
  h1 := (2,4,0,1,0)
  h2 := (2,4,0,1,0)
  D := [[2, 4, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_133_15 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨133, by decide⟩
  m := 1
  T1 := T147_133
  T2 := Q2.T147_133_2
  h1 := (3,0,4,4,2)
  h2 := (3,0,4,4,2)
  D := [[3, 0, 4, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_133_16 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨133, by decide⟩
  m := 1
  T1 := T147_133
  T2 := Q2.T147_133_2
  h1 := (3,1,0,4,1)
  h2 := (3,1,0,4,1)
  D := [[3, 1, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_133_17 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨133, by decide⟩
  m := 1
  T1 := T147_133
  T2 := Q2.T147_133_2
  h1 := (3,2,1,4,1)
  h2 := (3,2,1,4,1)
  D := [[3, 2, 1, 3, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_133_18 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨133, by decide⟩
  m := 1
  T1 := T147_133
  T2 := Q2.T147_133_2
  h1 := (3,3,2,4,2)
  h2 := (3,3,2,4,2)
  D := [[3, 3, 2, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_133_19 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨133, by decide⟩
  m := 1
  T1 := T147_133
  T2 := Q2.T147_133_2
  h1 := (3,4,3,4,4)
  h2 := (3,4,3,4,4)
  D := [[3, 4, 3, 2, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_133_20 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨133, by decide⟩
  m := 1
  T1 := T147_133
  T2 := Q2.T147_133_2
  h1 := (4,0,2,2,2)
  h2 := (4,0,2,2,2)
  D := [[4, 0, 2, 2, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_133_21 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨133, by decide⟩
  m := 1
  T1 := T147_133
  T2 := Q2.T147_133_2
  h1 := (4,1,3,2,4)
  h2 := (4,1,3,2,4)
  D := [[4, 1, 3, 3, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_133_22 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨133, by decide⟩
  m := 1
  T1 := T147_133
  T2 := Q2.T147_133_2
  h1 := (4,2,4,2,2)
  h2 := (4,2,4,2,2)
  D := [[4, 2, 4, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_133_23 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨133, by decide⟩
  m := 1
  T1 := T147_133
  T2 := Q2.T147_133_2
  h1 := (4,3,0,2,1)
  h2 := (4,3,0,2,1)
  D := [[4, 3, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_133_24 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨133, by decide⟩
  m := 1
  T1 := T147_133
  T2 := Q2.T147_133_2
  h1 := (4,4,1,2,1)
  h2 := (4,4,1,2,1)
  D := [[4, 4, 1, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_134_0 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨134, by decide⟩
  m := 1
  T1 := T147_134
  T2 := Q2.T147_134_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_134_8 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨134, by decide⟩
  m := 1
  T1 := T147_134
  T2 := Q2.T147_134_2
  h1 := (1,3,0,1,2)
  h2 := (1,3,0,1,2)
  D := [[1, 3, 0, 3, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_134_11 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨134, by decide⟩
  m := 1
  T1 := T147_134
  T2 := Q2.T147_134_2
  h1 := (2,1,0,2,4)
  h2 := (2,1,0,2,4)
  D := [[2, 1, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_134_19 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨134, by decide⟩
  m := 1
  T1 := T147_134
  T2 := Q2.T147_134_2
  h1 := (3,4,0,3,1)
  h2 := (3,4,0,3,1)
  D := [[3, 4, 0, 1, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_134_22 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨134, by decide⟩
  m := 1
  T1 := T147_134
  T2 := Q2.T147_134_2
  h1 := (4,2,0,4,3)
  h2 := (4,2,0,4,3)
  D := [[4, 2, 0, 1, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_135_0 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨135, by decide⟩
  m := 1
  T1 := T147_135
  T2 := Q2.T147_135_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_135_6 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨135, by decide⟩
  m := 1
  T1 := T147_135
  T2 := Q2.T147_135_2
  h1 := (1,1,0,0,0)
  h2 := (1,1,0,0,0)
  D := [[1, 1, 0, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_135_12 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨135, by decide⟩
  m := 1
  T1 := T147_135
  T2 := Q2.T147_135_2
  h1 := (2,2,0,0,3)
  h2 := (2,2,0,0,3)
  D := [[2, 2, 0, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_135_18 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨135, by decide⟩
  m := 1
  T1 := T147_135
  T2 := Q2.T147_135_2
  h1 := (3,3,0,0,4)
  h2 := (3,3,0,0,4)
  D := [[3, 3, 0, 1, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_135_24 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨135, by decide⟩
  m := 1
  T1 := T147_135
  T2 := Q2.T147_135_2
  h1 := (4,4,0,0,3)
  h2 := (4,4,0,0,3)
  D := [[4, 4, 0, 4, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_136_0 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨136, by decide⟩
  m := 1
  T1 := T147_136
  T2 := Q2.T147_136_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_136_1 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨136, by decide⟩
  m := 1
  T1 := T147_136
  T2 := Q2.T147_136_2
  h1 := (0,1,0,0,0)
  h2 := (0,1,0,0,0)
  D := [[0, 1, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_136_2 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨136, by decide⟩
  m := 1
  T1 := T147_136
  T2 := Q2.T147_136_2
  h1 := (0,2,0,0,0)
  h2 := (0,2,0,0,0)
  D := [[0, 2, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_136_3 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨136, by decide⟩
  m := 1
  T1 := T147_136
  T2 := Q2.T147_136_2
  h1 := (0,3,0,0,0)
  h2 := (0,3,0,0,0)
  D := [[0, 3, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_136_4 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨136, by decide⟩
  m := 1
  T1 := T147_136
  T2 := Q2.T147_136_2
  h1 := (0,4,0,0,0)
  h2 := (0,4,0,0,0)
  D := [[0, 4, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_136_5 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨136, by decide⟩
  m := 1
  T1 := T147_136
  T2 := Q2.T147_136_2
  h1 := (1,0,1,0,0)
  h2 := (1,0,1,0,0)
  D := [[1, 0, 1, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_136_6 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨136, by decide⟩
  m := 1
  T1 := T147_136
  T2 := Q2.T147_136_2
  h1 := (1,1,1,0,1)
  h2 := (1,1,1,0,1)
  D := [[1, 1, 1, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_136_7 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨136, by decide⟩
  m := 1
  T1 := T147_136
  T2 := Q2.T147_136_2
  h1 := (1,2,1,0,2)
  h2 := (1,2,1,0,2)
  D := [[1, 2, 1, 3, 2]]
  bind1 := by decide
  bind2 := by decide

end LeanDring.P5Presentation
