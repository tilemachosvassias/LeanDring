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
cdd tier, chunk 35: 60 columns.
-/

-- machine-emitted data: silence style linters (generated long lines, file-level options)
set_option linter.style.longLine false

namespace LeanDring.P5Presentation

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

def colCertDiv_147_139_7 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨139, by decide⟩
  m := 1
  T1 := T147_139
  T2 := Q2.T147_139_2
  h1 := (1,2,2,1,3)
  h2 := (1,2,2,1,2)
  D1 := [[1, 2, 2, 4, 0]]
  D2 := [[1, 2, 2, 4, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_139_9 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨139, by decide⟩
  m := 1
  T1 := T147_139
  T2 := Q2.T147_139_2
  h1 := (1,4,3,1,4)
  h2 := (1,4,3,1,0)
  D1 := [[1, 4, 3, 2, 0]]
  D2 := [[1, 4, 3, 2, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_139_10 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨139, by decide⟩
  m := 1
  T1 := T147_139
  T2 := Q2.T147_139_2
  h1 := (2,0,2,2,4)
  h2 := (2,0,2,2,3)
  D1 := [[2, 0, 2, 2, 0]]
  D2 := [[2, 0, 2, 2, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_139_12 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨139, by decide⟩
  m := 1
  T1 := T147_139
  T2 := Q2.T147_139_2
  h1 := (2,2,3,2,0)
  h2 := (2,2,3,2,1)
  D1 := [[2, 2, 3, 3, 1]]
  D2 := [[2, 2, 3, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_139_13 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨139, by decide⟩
  m := 1
  T1 := T147_139
  T2 := Q2.T147_139_2
  h1 := (2,3,1,2,0)
  h2 := (2,3,1,2,2)
  D1 := [[2, 3, 1, 1, 2]]
  D2 := [[2, 3, 1, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_139_14 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨139, by decide⟩
  m := 1
  T1 := T147_139
  T2 := Q2.T147_139_2
  h1 := (2,4,4,2,3)
  h2 := (2,4,4,2,1)
  D1 := [[2, 4, 4, 4, 0]]
  D2 := [[2, 4, 4, 4, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_139_15 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨139, by decide⟩
  m := 1
  T1 := T147_139
  T2 := Q2.T147_139_2
  h1 := (3,0,3,3,0)
  h2 := (3,0,3,3,1)
  D1 := [[3, 0, 3, 3, 1]]
  D2 := [[3, 0, 3, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_139_16 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨139, by decide⟩
  m := 1
  T1 := T147_139
  T2 := Q2.T147_139_2
  h1 := (3,1,1,3,0)
  h2 := (3,1,1,3,2)
  D1 := [[3, 1, 1, 0, 1]]
  D2 := [[3, 1, 1, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_139_17 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨139, by decide⟩
  m := 1
  T1 := T147_139
  T2 := Q2.T147_139_2
  h1 := (3,2,4,3,3)
  h2 := (3,2,4,3,1)
  D1 := [[3, 2, 4, 2, 3]]
  D2 := [[3, 2, 4, 2, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_139_18 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨139, by decide⟩
  m := 1
  T1 := T147_139
  T2 := Q2.T147_139_2
  h1 := (3,3,2,3,4)
  h2 := (3,3,2,3,3)
  D1 := [[3, 3, 2, 4, 2]]
  D2 := [[3, 3, 2, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_139_20 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨139, by decide⟩
  m := 1
  T1 := T147_139
  T2 := Q2.T147_139_2
  h1 := (4,0,4,4,2)
  h2 := (4,0,4,4,0)
  D1 := [[4, 0, 4, 4, 1]]
  D2 := [[4, 0, 4, 4, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_139_21 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨139, by decide⟩
  m := 1
  T1 := T147_139
  T2 := Q2.T147_139_2
  h1 := (4,1,2,4,3)
  h2 := (4,1,2,4,2)
  D1 := [[4, 1, 2, 0, 0]]
  D2 := [[4, 1, 2, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_139_23 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨139, by decide⟩
  m := 1
  T1 := T147_139
  T2 := Q2.T147_139_2
  h1 := (4,3,3,4,4)
  h2 := (4,3,3,4,0)
  D1 := [[4, 3, 3, 2, 4]]
  D2 := [[4, 3, 3, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_139_24 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨139, by decide⟩
  m := 1
  T1 := T147_139
  T2 := Q2.T147_139_2
  h1 := (4,4,1,4,4)
  h2 := (4,4,1,4,1)
  D1 := [[4, 4, 1, 3, 4]]
  D2 := [[4, 4, 1, 3, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_140_1 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨140, by decide⟩
  m := 1
  T1 := T147_140
  T2 := Q2.T147_140_2
  h1 := (0,1,4,0,2)
  h2 := (0,1,4,0,0)
  D1 := [[0, 1, 4, 0, 3]]
  D2 := [[0, 1, 4, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_140_2 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨140, by decide⟩
  m := 1
  T1 := T147_140
  T2 := Q2.T147_140_2
  h1 := (0,2,3,0,3)
  h2 := (0,2,3,0,4)
  D1 := [[0, 2, 3, 0, 2]]
  D2 := [[0, 2, 3, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_140_3 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨140, by decide⟩
  m := 1
  T1 := T147_140
  T2 := Q2.T147_140_2
  h1 := (0,3,2,0,3)
  h2 := (0,3,2,0,2)
  D1 := [[0, 3, 2, 0, 2]]
  D2 := [[0, 3, 2, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_140_4 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨140, by decide⟩
  m := 1
  T1 := T147_140
  T2 := Q2.T147_140_2
  h1 := (0,4,1,0,2)
  h2 := (0,4,1,0,4)
  D1 := [[0, 4, 1, 0, 3]]
  D2 := [[0, 4, 1, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_140_5 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨140, by decide⟩
  m := 1
  T1 := T147_140
  T2 := Q2.T147_140_2
  h1 := (1,0,1,0,2)
  h2 := (1,0,1,0,4)
  D1 := [[1, 0, 1, 0, 2]]
  D2 := [[1, 0, 1, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_140_7 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨140, by decide⟩
  m := 1
  T1 := T147_140
  T2 := Q2.T147_140_2
  h1 := (1,2,4,0,2)
  h2 := (1,2,4,0,0)
  D1 := [[1, 2, 4, 3, 1]]
  D2 := [[1, 2, 4, 3, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_140_8 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨140, by decide⟩
  m := 1
  T1 := T147_140
  T2 := Q2.T147_140_2
  h1 := (1,3,3,0,3)
  h2 := (1,3,3,0,4)
  D1 := [[1, 3, 3, 2, 2]]
  D2 := [[1, 3, 3, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_140_9 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨140, by decide⟩
  m := 1
  T1 := T147_140
  T2 := Q2.T147_140_2
  h1 := (1,4,2,0,3)
  h2 := (1,4,2,0,2)
  D1 := [[1, 4, 2, 1, 4]]
  D2 := [[1, 4, 2, 1, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_140_10 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨140, by decide⟩
  m := 1
  T1 := T147_140
  T2 := Q2.T147_140_2
  h1 := (2,0,2,0,4)
  h2 := (2,0,2,0,3)
  D1 := [[2, 0, 2, 0, 4]]
  D2 := [[2, 0, 2, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_140_11 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨140, by decide⟩
  m := 1
  T1 := T147_140
  T2 := Q2.T147_140_2
  h1 := (2,1,1,0,3)
  h2 := (2,1,1,0,0)
  D1 := [[2, 1, 1, 3, 0]]
  D2 := [[2, 1, 1, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_140_13 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨140, by decide⟩
  m := 1
  T1 := T147_140
  T2 := Q2.T147_140_2
  h1 := (2,3,4,0,3)
  h2 := (2,3,4,0,1)
  D1 := [[2, 3, 4, 4, 0]]
  D2 := [[2, 3, 4, 4, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_140_14 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨140, by decide⟩
  m := 1
  T1 := T147_140
  T2 := Q2.T147_140_2
  h1 := (2,4,3,0,4)
  h2 := (2,4,3,0,0)
  D1 := [[2, 4, 3, 2, 4]]
  D2 := [[2, 4, 3, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_140_15 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨140, by decide⟩
  m := 1
  T1 := T147_140
  T2 := Q2.T147_140_2
  h1 := (3,0,3,0,1)
  h2 := (3,0,3,0,2)
  D1 := [[3, 0, 3, 0, 1]]
  D2 := [[3, 0, 3, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_140_16 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨140, by decide⟩
  m := 1
  T1 := T147_140
  T2 := Q2.T147_140_2
  h1 := (3,1,2,0,1)
  h2 := (3,1,2,0,0)
  D1 := [[3, 1, 2, 2, 0]]
  D2 := [[3, 1, 2, 2, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_140_17 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨140, by decide⟩
  m := 1
  T1 := T147_140
  T2 := Q2.T147_140_2
  h1 := (3,2,1,0,0)
  h2 := (3,2,1,0,2)
  D1 := [[3, 2, 1, 4, 0]]
  D2 := [[3, 2, 1, 4, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_140_19 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨140, by decide⟩
  m := 1
  T1 := T147_140
  T2 := Q2.T147_140_2
  h1 := (3,4,4,0,0)
  h2 := (3,4,4,0,3)
  D1 := [[3, 4, 4, 3, 3]]
  D2 := [[3, 4, 4, 3, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_140_20 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨140, by decide⟩
  m := 1
  T1 := T147_140
  T2 := Q2.T147_140_2
  h1 := (4,0,4,0,3)
  h2 := (4,0,4,0,1)
  D1 := [[4, 0, 4, 0, 3]]
  D2 := [[4, 0, 4, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_140_21 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨140, by decide⟩
  m := 1
  T1 := T147_140
  T2 := Q2.T147_140_2
  h1 := (4,1,3,0,4)
  h2 := (4,1,3,0,0)
  D1 := [[4, 1, 3, 1, 1]]
  D2 := [[4, 1, 3, 1, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_140_22 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨140, by decide⟩
  m := 1
  T1 := T147_140
  T2 := Q2.T147_140_2
  h1 := (4,2,2,0,4)
  h2 := (4,2,2,0,3)
  D1 := [[4, 2, 2, 2, 0]]
  D2 := [[4, 2, 2, 2, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_140_23 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨140, by decide⟩
  m := 1
  T1 := T147_140
  T2 := Q2.T147_140_2
  h1 := (4,3,1,0,3)
  h2 := (4,3,1,0,0)
  D1 := [[4, 3, 1, 3, 0]]
  D2 := [[4, 3, 1, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_142_1 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨142, by decide⟩
  m := 1
  T1 := T147_142
  T2 := Q2.T147_142_2
  h1 := (0,1,4,0,2)
  h2 := (0,1,4,0,0)
  D1 := [[0, 1, 4, 0, 3]]
  D2 := [[0, 1, 4, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_142_2 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨142, by decide⟩
  m := 1
  T1 := T147_142
  T2 := Q2.T147_142_2
  h1 := (0,2,3,0,3)
  h2 := (0,2,3,0,4)
  D1 := [[0, 2, 3, 0, 2]]
  D2 := [[0, 2, 3, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_142_3 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨142, by decide⟩
  m := 1
  T1 := T147_142
  T2 := Q2.T147_142_2
  h1 := (0,3,2,0,3)
  h2 := (0,3,2,0,2)
  D1 := [[0, 3, 2, 0, 2]]
  D2 := [[0, 3, 2, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_142_4 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨142, by decide⟩
  m := 1
  T1 := T147_142
  T2 := Q2.T147_142_2
  h1 := (0,4,1,0,2)
  h2 := (0,4,1,0,4)
  D1 := [[0, 4, 1, 0, 3]]
  D2 := [[0, 4, 1, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_142_6 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨142, by decide⟩
  m := 1
  T1 := T147_142
  T2 := Q2.T147_142_2
  h1 := (1,1,4,0,2)
  h2 := (1,1,4,0,0)
  D1 := [[1, 1, 4, 4, 4]]
  D2 := [[1, 1, 4, 4, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_142_7 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨142, by decide⟩
  m := 1
  T1 := T147_142
  T2 := Q2.T147_142_2
  h1 := (1,2,3,0,3)
  h2 := (1,2,3,0,4)
  D1 := [[1, 2, 3, 3, 4]]
  D2 := [[1, 2, 3, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_142_8 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨142, by decide⟩
  m := 1
  T1 := T147_142
  T2 := Q2.T147_142_2
  h1 := (1,3,2,0,3)
  h2 := (1,3,2,0,2)
  D1 := [[1, 3, 2, 2, 0]]
  D2 := [[1, 3, 2, 2, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_142_9 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨142, by decide⟩
  m := 1
  T1 := T147_142
  T2 := Q2.T147_142_2
  h1 := (1,4,1,0,2)
  h2 := (1,4,1,0,4)
  D1 := [[1, 4, 1, 1, 2]]
  D2 := [[1, 4, 1, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_142_11 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨142, by decide⟩
  m := 1
  T1 := T147_142
  T2 := Q2.T147_142_2
  h1 := (2,1,4,0,2)
  h2 := (2,1,4,0,0)
  D1 := [[2, 1, 4, 3, 1]]
  D2 := [[2, 1, 4, 3, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_142_12 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨142, by decide⟩
  m := 1
  T1 := T147_142
  T2 := Q2.T147_142_2
  h1 := (2,2,3,0,3)
  h2 := (2,2,3,0,4)
  D1 := [[2, 2, 3, 1, 3]]
  D2 := [[2, 2, 3, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_142_13 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨142, by decide⟩
  m := 1
  T1 := T147_142
  T2 := Q2.T147_142_2
  h1 := (2,3,2,0,3)
  h2 := (2,3,2,0,2)
  D1 := [[2, 3, 2, 4, 1]]
  D2 := [[2, 3, 2, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_142_14 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨142, by decide⟩
  m := 1
  T1 := T147_142
  T2 := Q2.T147_142_2
  h1 := (2,4,1,0,2)
  h2 := (2,4,1,0,4)
  D1 := [[2, 4, 1, 2, 0]]
  D2 := [[2, 4, 1, 2, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_142_16 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨142, by decide⟩
  m := 1
  T1 := T147_142
  T2 := Q2.T147_142_2
  h1 := (3,1,4,0,2)
  h2 := (3,1,4,0,0)
  D1 := [[3, 1, 4, 2, 4]]
  D2 := [[3, 1, 4, 2, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_142_17 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨142, by decide⟩
  m := 1
  T1 := T147_142
  T2 := Q2.T147_142_2
  h1 := (3,2,3,0,3)
  h2 := (3,2,3,0,4)
  D1 := [[3, 2, 3, 4, 4]]
  D2 := [[3, 2, 3, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_142_18 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨142, by decide⟩
  m := 1
  T1 := T147_142
  T2 := Q2.T147_142_2
  h1 := (3,3,2,0,3)
  h2 := (3,3,2,0,2)
  D1 := [[3, 3, 2, 1, 0]]
  D2 := [[3, 3, 2, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_142_19 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨142, by decide⟩
  m := 1
  T1 := T147_142
  T2 := Q2.T147_142_2
  h1 := (3,4,1,0,2)
  h2 := (3,4,1,0,4)
  D1 := [[3, 4, 1, 3, 2]]
  D2 := [[3, 4, 1, 3, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_142_21 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨142, by decide⟩
  m := 1
  T1 := T147_142
  T2 := Q2.T147_142_2
  h1 := (4,1,4,0,2)
  h2 := (4,1,4,0,0)
  D1 := [[4, 1, 4, 1, 3]]
  D2 := [[4, 1, 4, 1, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_142_22 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨142, by decide⟩
  m := 1
  T1 := T147_142
  T2 := Q2.T147_142_2
  h1 := (4,2,3,0,3)
  h2 := (4,2,3,0,4)
  D1 := [[4, 2, 3, 2, 2]]
  D2 := [[4, 2, 3, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_142_23 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨142, by decide⟩
  m := 1
  T1 := T147_142
  T2 := Q2.T147_142_2
  h1 := (4,3,2,0,3)
  h2 := (4,3,2,0,2)
  D1 := [[4, 3, 2, 3, 2]]
  D2 := [[4, 3, 2, 3, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_142_24 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨142, by decide⟩
  m := 1
  T1 := T147_142
  T2 := Q2.T147_142_2
  h1 := (4,4,1,0,2)
  h2 := (4,4,1,0,4)
  D1 := [[4, 4, 1, 4, 3]]
  D2 := [[4, 4, 1, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_143_1 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨143, by decide⟩
  m := 1
  T1 := T147_143
  T2 := Q2.T147_143_2
  h1 := (0,1,2,0,4)
  h2 := (0,1,2,0,0)
  D1 := [[0, 1, 2, 0, 2]]
  D2 := [[0, 1, 2, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_143_2 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨143, by decide⟩
  m := 1
  T1 := T147_143
  T2 := Q2.T147_143_2
  h1 := (0,2,4,0,0)
  h2 := (0,2,4,0,2)
  D1 := [[0, 2, 4, 0, 2]]
  D2 := [[0, 2, 4, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_143_3 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨143, by decide⟩
  m := 1
  T1 := T147_143
  T2 := Q2.T147_143_2
  h1 := (0,3,1,0,3)
  h2 := (0,3,1,0,1)
  D1 := [[0, 3, 1, 0, 0]]
  D2 := [[0, 3, 1, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_143_4 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨143, by decide⟩
  m := 1
  T1 := T147_143
  T2 := Q2.T147_143_2
  h1 := (0,4,3,0,3)
  h2 := (0,4,3,0,2)
  D1 := [[0, 4, 3, 0, 1]]
  D2 := [[0, 4, 3, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_143_6 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨143, by decide⟩
  m := 1
  T1 := T147_143
  T2 := Q2.T147_143_2
  h1 := (1,1,2,0,4)
  h2 := (1,1,2,0,0)
  D1 := [[1, 1, 2, 4, 3]]
  D2 := [[1, 1, 2, 4, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_143_7 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨143, by decide⟩
  m := 1
  T1 := T147_143
  T2 := Q2.T147_143_2
  h1 := (1,2,4,0,0)
  h2 := (1,2,4,0,2)
  D1 := [[1, 2, 4, 3, 4]]
  D2 := [[1, 2, 4, 3, 1]]
  bind1 := by decide
  bind2 := by decide

end LeanDring.P5Presentation
