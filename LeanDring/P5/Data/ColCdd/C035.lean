/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.Twin1.ColCert
import LeanDring.P5.Data.EntryK.C044

/-!
# Species-table cell data, stage 2 — column-data-divergent columns

Per-column certified exponent-vector data (`ColCert`/`ColCertDiv`) with kernel
`decide` bindings. Emitted; the embedded lists are what the kernel certifies.
cdd tier, chunk 34: 60 columns.
-/

-- machine-emitted data: silence style linters (generated long lines, file-level options)
set_option linter.style.longLine false

namespace LeanDring.P5Presentation

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

def colCertDiv_147_134_7 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨134, by decide⟩
  m := 1
  T1 := T147_134
  T2 := Q2.T147_134_2
  h1 := (1,2,1,1,4)
  h2 := (1,2,1,1,1)
  D1 := [[1, 2, 1, 4, 3]]
  D2 := [[1, 2, 1, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_134_9 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨134, by decide⟩
  m := 1
  T1 := T147_134
  T2 := Q2.T147_134_2
  h1 := (1,4,4,1,4)
  h2 := (1,4,4,1,2)
  D1 := [[1, 4, 4, 2, 1]]
  D2 := [[1, 4, 4, 2, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_134_10 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨134, by decide⟩
  m := 1
  T1 := T147_134
  T2 := Q2.T147_134_2
  h1 := (2,0,1,2,1)
  h2 := (2,0,1,2,3)
  D1 := [[2, 0, 1, 2, 2]]
  D2 := [[2, 0, 1, 2, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_134_12 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨134, by decide⟩
  m := 1
  T1 := T147_134
  T2 := Q2.T147_134_2
  h1 := (2,2,4,2,1)
  h2 := (2,2,4,2,4)
  D1 := [[2, 2, 4, 3, 0]]
  D2 := [[2, 2, 4, 3, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_134_13 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨134, by decide⟩
  m := 1
  T1 := T147_134
  T2 := Q2.T147_134_2
  h1 := (2,3,3,2,2)
  h2 := (2,3,3,2,3)
  D1 := [[2, 3, 3, 1, 3]]
  D2 := [[2, 3, 3, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_134_14 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨134, by decide⟩
  m := 1
  T1 := T147_134
  T2 := Q2.T147_134_2
  h1 := (2,4,2,2,2)
  h2 := (2,4,2,2,1)
  D1 := [[2, 4, 2, 4, 2]]
  D2 := [[2, 4, 2, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_134_15 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨134, by decide⟩
  m := 1
  T1 := T147_134
  T2 := Q2.T147_134_2
  h1 := (3,0,4,3,3)
  h2 := (3,0,4,3,1)
  D1 := [[3, 0, 4, 3, 4]]
  D2 := [[3, 0, 4, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_134_16 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨134, by decide⟩
  m := 1
  T1 := T147_134
  T2 := Q2.T147_134_2
  h1 := (3,1,3,3,4)
  h2 := (3,1,3,3,0)
  D1 := [[3, 1, 3, 0, 3]]
  D2 := [[3, 1, 3, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_134_17 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨134, by decide⟩
  m := 1
  T1 := T147_134
  T2 := Q2.T147_134_2
  h1 := (3,2,2,3,4)
  h2 := (3,2,2,3,3)
  D1 := [[3, 2, 2, 2, 3]]
  D2 := [[3, 2, 2, 2, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_134_18 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨134, by decide⟩
  m := 1
  T1 := T147_134
  T2 := Q2.T147_134_2
  h1 := (3,3,1,3,3)
  h2 := (3,3,1,3,0)
  D1 := [[3, 3, 1, 4, 4]]
  D2 := [[3, 3, 1, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_134_20 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨134, by decide⟩
  m := 1
  T1 := T147_134
  T2 := Q2.T147_134_2
  h1 := (4,0,2,4,1)
  h2 := (4,0,2,4,0)
  D1 := [[4, 0, 2, 4, 0]]
  D2 := [[4, 0, 2, 4, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_134_21 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨134, by decide⟩
  m := 1
  T1 := T147_134
  T2 := Q2.T147_134_2
  h1 := (4,1,1,4,0)
  h2 := (4,1,1,4,2)
  D1 := [[4, 1, 1, 0, 3]]
  D2 := [[4, 1, 1, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_134_23 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨134, by decide⟩
  m := 1
  T1 := T147_134
  T2 := Q2.T147_134_2
  h1 := (4,3,4,4,0)
  h2 := (4,3,4,4,3)
  D1 := [[4, 3, 4, 2, 2]]
  D2 := [[4, 3, 4, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_134_24 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨134, by decide⟩
  m := 1
  T1 := T147_134
  T2 := Q2.T147_134_2
  h1 := (4,4,3,4,1)
  h2 := (4,4,3,4,2)
  D1 := [[4, 4, 3, 3, 3]]
  D2 := [[4, 4, 3, 3, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_135_1 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨135, by decide⟩
  m := 1
  T1 := T147_135
  T2 := Q2.T147_135_2
  h1 := (0,1,2,0,4)
  h2 := (0,1,2,0,0)
  D1 := [[0, 1, 2, 0, 2]]
  D2 := [[0, 1, 2, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_135_2 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨135, by decide⟩
  m := 1
  T1 := T147_135
  T2 := Q2.T147_135_2
  h1 := (0,2,4,0,0)
  h2 := (0,2,4,0,2)
  D1 := [[0, 2, 4, 0, 2]]
  D2 := [[0, 2, 4, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_135_3 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨135, by decide⟩
  m := 1
  T1 := T147_135
  T2 := Q2.T147_135_2
  h1 := (0,3,1,0,3)
  h2 := (0,3,1,0,1)
  D1 := [[0, 3, 1, 0, 0]]
  D2 := [[0, 3, 1, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_135_4 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨135, by decide⟩
  m := 1
  T1 := T147_135
  T2 := Q2.T147_135_2
  h1 := (0,4,3,0,3)
  h2 := (0,4,3,0,2)
  D1 := [[0, 4, 3, 0, 1]]
  D2 := [[0, 4, 3, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_135_5 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨135, by decide⟩
  m := 1
  T1 := T147_135
  T2 := Q2.T147_135_2
  h1 := (1,0,3,0,3)
  h2 := (1,0,3,0,2)
  D1 := [[1, 0, 3, 0, 3]]
  D2 := [[1, 0, 3, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_135_7 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨135, by decide⟩
  m := 1
  T1 := T147_135
  T2 := Q2.T147_135_2
  h1 := (1,2,2,0,4)
  h2 := (1,2,2,0,0)
  D1 := [[1, 2, 2, 3, 2]]
  D2 := [[1, 2, 2, 3, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_135_8 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨135, by decide⟩
  m := 1
  T1 := T147_135
  T2 := Q2.T147_135_2
  h1 := (1,3,4,0,0)
  h2 := (1,3,4,0,2)
  D1 := [[1, 3, 4, 2, 1]]
  D2 := [[1, 3, 4, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_135_9 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨135, by decide⟩
  m := 1
  T1 := T147_135
  T2 := Q2.T147_135_2
  h1 := (1,4,1,0,3)
  h2 := (1,4,1,0,1)
  D1 := [[1, 4, 1, 1, 3]]
  D2 := [[1, 4, 1, 1, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_135_10 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨135, by decide⟩
  m := 1
  T1 := T147_135
  T2 := Q2.T147_135_2
  h1 := (2,0,1,0,1)
  h2 := (2,0,1,0,4)
  D1 := [[2, 0, 1, 0, 1]]
  D2 := [[2, 0, 1, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_135_11 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨135, by decide⟩
  m := 1
  T1 := T147_135
  T2 := Q2.T147_135_2
  h1 := (2,1,3,0,1)
  h2 := (2,1,3,0,0)
  D1 := [[2, 1, 3, 3, 1]]
  D2 := [[2, 1, 3, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_135_13 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨135, by decide⟩
  m := 1
  T1 := T147_135
  T2 := Q2.T147_135_2
  h1 := (2,3,2,0,2)
  h2 := (2,3,2,0,3)
  D1 := [[2, 3, 2, 4, 0]]
  D2 := [[2, 3, 2, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_135_14 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨135, by decide⟩
  m := 1
  T1 := T147_135
  T2 := Q2.T147_135_2
  h1 := (2,4,4,0,3)
  h2 := (2,4,4,0,0)
  D1 := [[2, 4, 4, 2, 4]]
  D2 := [[2, 4, 4, 2, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_135_15 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨135, by decide⟩
  m := 1
  T1 := T147_135
  T2 := Q2.T147_135_2
  h1 := (3,0,4,0,4)
  h2 := (3,0,4,0,1)
  D1 := [[3, 0, 4, 0, 4]]
  D2 := [[3, 0, 4, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_135_16 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨135, by decide⟩
  m := 1
  T1 := T147_135
  T2 := Q2.T147_135_2
  h1 := (3,1,1,0,2)
  h2 := (3,1,1,0,0)
  D1 := [[3, 1, 1, 2, 2]]
  D2 := [[3, 1, 1, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_135_17 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨135, by decide⟩
  m := 1
  T1 := T147_135
  T2 := Q2.T147_135_2
  h1 := (3,2,3,0,2)
  h2 := (3,2,3,0,1)
  D1 := [[3, 2, 3, 4, 3]]
  D2 := [[3, 2, 3, 4, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_135_19 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨135, by decide⟩
  m := 1
  T1 := T147_135
  T2 := Q2.T147_135_2
  h1 := (3,4,2,0,3)
  h2 := (3,4,2,0,4)
  D1 := [[3, 4, 2, 3, 4]]
  D2 := [[3, 4, 2, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_135_20 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨135, by decide⟩
  m := 1
  T1 := T147_135
  T2 := Q2.T147_135_2
  h1 := (4,0,2,0,2)
  h2 := (4,0,2,0,3)
  D1 := [[4, 0, 2, 0, 2]]
  D2 := [[4, 0, 2, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_135_21 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨135, by decide⟩
  m := 1
  T1 := T147_135
  T2 := Q2.T147_135_2
  h1 := (4,1,4,0,3)
  h2 := (4,1,4,0,0)
  D1 := [[4, 1, 4, 1, 4]]
  D2 := [[4, 1, 4, 1, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_135_22 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨135, by decide⟩
  m := 1
  T1 := T147_135
  T2 := Q2.T147_135_2
  h1 := (4,2,1,0,1)
  h2 := (4,2,1,0,4)
  D1 := [[4, 2, 1, 2, 4]]
  D2 := [[4, 2, 1, 2, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_135_23 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨135, by decide⟩
  m := 1
  T1 := T147_135
  T2 := Q2.T147_135_2
  h1 := (4,3,3,0,1)
  h2 := (4,3,3,0,0)
  D1 := [[4, 3, 3, 3, 2]]
  D2 := [[4, 3, 3, 3, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_138_1 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨138, by decide⟩
  m := 1
  T1 := T147_138
  T2 := Q2.T147_138_2
  h1 := (0,1,2,0,4)
  h2 := (0,1,2,0,0)
  D1 := [[0, 1, 2, 0, 2]]
  D2 := [[0, 1, 2, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_138_2 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨138, by decide⟩
  m := 1
  T1 := T147_138
  T2 := Q2.T147_138_2
  h1 := (0,2,4,0,0)
  h2 := (0,2,4,0,2)
  D1 := [[0, 2, 4, 0, 2]]
  D2 := [[0, 2, 4, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_138_3 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨138, by decide⟩
  m := 1
  T1 := T147_138
  T2 := Q2.T147_138_2
  h1 := (0,3,1,0,3)
  h2 := (0,3,1,0,1)
  D1 := [[0, 3, 1, 0, 0]]
  D2 := [[0, 3, 1, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_138_4 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨138, by decide⟩
  m := 1
  T1 := T147_138
  T2 := Q2.T147_138_2
  h1 := (0,4,3,0,3)
  h2 := (0,4,3,0,2)
  D1 := [[0, 4, 3, 0, 1]]
  D2 := [[0, 4, 3, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_138_5 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨138, by decide⟩
  m := 1
  T1 := T147_138
  T2 := Q2.T147_138_2
  h1 := (1,0,1,3,1)
  h2 := (1,0,1,3,4)
  D1 := [[1, 0, 1, 3, 3]]
  D2 := [[1, 0, 1, 3, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_138_6 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨138, by decide⟩
  m := 1
  T1 := T147_138
  T2 := Q2.T147_138_2
  h1 := (1,1,3,3,1)
  h2 := (1,1,3,3,0)
  D1 := [[1, 1, 3, 2, 1]]
  D2 := [[1, 1, 3, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_138_8 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨138, by decide⟩
  m := 1
  T1 := T147_138
  T2 := Q2.T147_138_2
  h1 := (1,3,2,3,2)
  h2 := (1,3,2,3,3)
  D1 := [[1, 3, 2, 0, 1]]
  D2 := [[1, 3, 2, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_138_9 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨138, by decide⟩
  m := 1
  T1 := T147_138
  T2 := Q2.T147_138_2
  h1 := (1,4,4,3,3)
  h2 := (1,4,4,3,0)
  D1 := [[1, 4, 4, 4, 3]]
  D2 := [[1, 4, 4, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_138_10 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨138, by decide⟩
  m := 1
  T1 := T147_138
  T2 := Q2.T147_138_2
  h1 := (2,0,2,1,0)
  h2 := (2,0,2,1,1)
  D1 := [[2, 0, 2, 1, 3]]
  D2 := [[2, 0, 2, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_138_11 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨138, by decide⟩
  m := 1
  T1 := T147_138
  T2 := Q2.T147_138_2
  h1 := (2,1,4,1,1)
  h2 := (2,1,4,1,3)
  D1 := [[2, 1, 4, 4, 3]]
  D2 := [[2, 1, 4, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_138_12 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨138, by decide⟩
  m := 1
  T1 := T147_138
  T2 := Q2.T147_138_2
  h1 := (2,2,1,1,4)
  h2 := (2,2,1,1,2)
  D1 := [[2, 2, 1, 2, 1]]
  D2 := [[2, 2, 1, 2, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_138_13 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨138, by decide⟩
  m := 1
  T1 := T147_138
  T2 := Q2.T147_138_2
  h1 := (2,3,3,1,4)
  h2 := (2,3,3,1,3)
  D1 := [[2, 3, 3, 0, 2]]
  D2 := [[2, 3, 3, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_138_15 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨138, by decide⟩
  m := 1
  T1 := T147_138
  T2 := Q2.T147_138_2
  h1 := (3,0,3,4,2)
  h2 := (3,0,3,4,1)
  D1 := [[3, 0, 3, 4, 0]]
  D2 := [[3, 0, 3, 4, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_138_17 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨138, by decide⟩
  m := 1
  T1 := T147_138
  T2 := Q2.T147_138_2
  h1 := (3,2,2,4,3)
  h2 := (3,2,2,4,4)
  D1 := [[3, 2, 2, 3, 4]]
  D2 := [[3, 2, 2, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_138_18 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨138, by decide⟩
  m := 1
  T1 := T147_138
  T2 := Q2.T147_138_2
  h1 := (3,3,4,4,4)
  h2 := (3,3,4,4,1)
  D1 := [[3, 3, 4, 0, 3]]
  D2 := [[3, 3, 4, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_138_19 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨138, by decide⟩
  m := 1
  T1 := T147_138
  T2 := Q2.T147_138_2
  h1 := (3,4,1,4,2)
  h2 := (3,4,1,4,0)
  D1 := [[3, 4, 1, 2, 0]]
  D2 := [[3, 4, 1, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_138_20 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨138, by decide⟩
  m := 1
  T1 := T147_138
  T2 := Q2.T147_138_2
  h1 := (4,0,4,2,2)
  h2 := (4,0,4,2,4)
  D1 := [[4, 0, 4, 2, 4]]
  D2 := [[4, 0, 4, 2, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_138_21 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨138, by decide⟩
  m := 1
  T1 := T147_138
  T2 := Q2.T147_138_2
  h1 := (4,1,1,2,0)
  h2 := (4,1,1,2,3)
  D1 := [[4, 1, 1, 3, 1]]
  D2 := [[4, 1, 1, 3, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_138_22 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨138, by decide⟩
  m := 1
  T1 := T147_138
  T2 := Q2.T147_138_2
  h1 := (4,2,3,2,0)
  h2 := (4,2,3,2,4)
  D1 := [[4, 2, 3, 4, 1]]
  D2 := [[4, 2, 3, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_138_24 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨138, by decide⟩
  m := 1
  T1 := T147_138
  T2 := Q2.T147_138_2
  h1 := (4,4,2,2,1)
  h2 := (4,4,2,2,2)
  D1 := [[4, 4, 2, 1, 0]]
  D2 := [[4, 4, 2, 1, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_139_1 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨139, by decide⟩
  m := 1
  T1 := T147_139
  T2 := Q2.T147_139_2
  h1 := (0,1,3,0,2)
  h2 := (0,1,3,0,3)
  D1 := [[0, 1, 3, 0, 4]]
  D2 := [[0, 1, 3, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_139_2 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨139, by decide⟩
  m := 1
  T1 := T147_139
  T2 := Q2.T147_139_2
  h1 := (0,2,1,0,2)
  h2 := (0,2,1,0,4)
  D1 := [[0, 2, 1, 0, 0]]
  D2 := [[0, 2, 1, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_139_3 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨139, by decide⟩
  m := 1
  T1 := T147_139
  T2 := Q2.T147_139_2
  h1 := (0,3,4,0,0)
  h2 := (0,3,4,0,3)
  D1 := [[0, 3, 4, 0, 3]]
  D2 := [[0, 3, 4, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_139_4 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨139, by decide⟩
  m := 1
  T1 := T147_139
  T2 := Q2.T147_139_2
  h1 := (0,4,2,0,1)
  h2 := (0,4,2,0,0)
  D1 := [[0, 4, 2, 0, 3]]
  D2 := [[0, 4, 2, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_139_5 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨139, by decide⟩
  m := 1
  T1 := T147_139
  T2 := Q2.T147_139_2
  h1 := (1,0,1,1,4)
  h2 := (1,0,1,1,1)
  D1 := [[1, 0, 1, 1, 3]]
  D2 := [[1, 0, 1, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_139_6 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨139, by decide⟩
  m := 1
  T1 := T147_139
  T2 := Q2.T147_139_2
  h1 := (1,1,4,1,2)
  h2 := (1,1,4,1,0)
  D1 := [[1, 1, 4, 0, 3]]
  D2 := [[1, 1, 4, 0, 1]]
  bind1 := by decide
  bind2 := by decide

end LeanDring.P5Presentation
