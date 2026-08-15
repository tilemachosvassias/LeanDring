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
rest tier, chunk 133: 60 columns.
-/

-- machine-emitted data: silence style linters (generated long lines, file-level options)
set_option linter.style.longLine false

namespace LeanDring.P5Presentation

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

def colCert_147_136_8 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨136, by decide⟩
  m := 1
  T1 := T147_136
  T2 := Q2.T147_136_2
  h1 := (1,3,1,0,3)
  h2 := (1,3,1,0,3)
  D := [[1, 3, 1, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_136_9 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨136, by decide⟩
  m := 1
  T1 := T147_136
  T2 := Q2.T147_136_2
  h1 := (1,4,1,0,4)
  h2 := (1,4,1,0,4)
  D := [[1, 4, 1, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_136_10 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨136, by decide⟩
  m := 1
  T1 := T147_136
  T2 := Q2.T147_136_2
  h1 := (2,0,2,0,0)
  h2 := (2,0,2,0,0)
  D := [[2, 0, 2, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_136_11 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨136, by decide⟩
  m := 1
  T1 := T147_136
  T2 := Q2.T147_136_2
  h1 := (2,1,2,0,2)
  h2 := (2,1,2,0,2)
  D := [[2, 1, 2, 3, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_136_12 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨136, by decide⟩
  m := 1
  T1 := T147_136
  T2 := Q2.T147_136_2
  h1 := (2,2,2,0,4)
  h2 := (2,2,2,0,4)
  D := [[2, 2, 2, 1, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_136_13 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨136, by decide⟩
  m := 1
  T1 := T147_136
  T2 := Q2.T147_136_2
  h1 := (2,3,2,0,1)
  h2 := (2,3,2,0,1)
  D := [[2, 3, 2, 4, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_136_14 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨136, by decide⟩
  m := 1
  T1 := T147_136
  T2 := Q2.T147_136_2
  h1 := (2,4,2,0,3)
  h2 := (2,4,2,0,3)
  D := [[2, 4, 2, 2, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_136_15 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨136, by decide⟩
  m := 1
  T1 := T147_136
  T2 := Q2.T147_136_2
  h1 := (3,0,3,0,0)
  h2 := (3,0,3,0,0)
  D := [[3, 0, 3, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_136_16 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨136, by decide⟩
  m := 1
  T1 := T147_136
  T2 := Q2.T147_136_2
  h1 := (3,1,3,0,3)
  h2 := (3,1,3,0,3)
  D := [[3, 1, 3, 2, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_136_17 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨136, by decide⟩
  m := 1
  T1 := T147_136
  T2 := Q2.T147_136_2
  h1 := (3,2,3,0,1)
  h2 := (3,2,3,0,1)
  D := [[3, 2, 3, 4, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_136_18 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨136, by decide⟩
  m := 1
  T1 := T147_136
  T2 := Q2.T147_136_2
  h1 := (3,3,3,0,4)
  h2 := (3,3,3,0,4)
  D := [[3, 3, 3, 1, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_136_19 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨136, by decide⟩
  m := 1
  T1 := T147_136
  T2 := Q2.T147_136_2
  h1 := (3,4,3,0,2)
  h2 := (3,4,3,0,2)
  D := [[3, 4, 3, 3, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_136_20 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨136, by decide⟩
  m := 1
  T1 := T147_136
  T2 := Q2.T147_136_2
  h1 := (4,0,4,0,0)
  h2 := (4,0,4,0,0)
  D := [[4, 0, 4, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_136_21 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨136, by decide⟩
  m := 1
  T1 := T147_136
  T2 := Q2.T147_136_2
  h1 := (4,1,4,0,4)
  h2 := (4,1,4,0,4)
  D := [[4, 1, 4, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_136_22 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨136, by decide⟩
  m := 1
  T1 := T147_136
  T2 := Q2.T147_136_2
  h1 := (4,2,4,0,3)
  h2 := (4,2,4,0,3)
  D := [[4, 2, 4, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_136_23 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨136, by decide⟩
  m := 1
  T1 := T147_136
  T2 := Q2.T147_136_2
  h1 := (4,3,4,0,2)
  h2 := (4,3,4,0,2)
  D := [[4, 3, 4, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_136_24 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨136, by decide⟩
  m := 1
  T1 := T147_136
  T2 := Q2.T147_136_2
  h1 := (4,4,4,0,1)
  h2 := (4,4,4,0,1)
  D := [[4, 4, 4, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_137_0 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨137, by decide⟩
  m := 1
  T1 := T147_137
  T2 := Q2.T147_137_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_137_1 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨137, by decide⟩
  m := 1
  T1 := T147_137
  T2 := Q2.T147_137_2
  h1 := (0,1,1,0,0)
  h2 := (0,1,1,0,0)
  D := [[0, 1, 1, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_137_2 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨137, by decide⟩
  m := 1
  T1 := T147_137
  T2 := Q2.T147_137_2
  h1 := (0,2,2,0,1)
  h2 := (0,2,2,0,1)
  D := [[0, 2, 2, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_137_3 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨137, by decide⟩
  m := 1
  T1 := T147_137
  T2 := Q2.T147_137_2
  h1 := (0,3,3,0,3)
  h2 := (0,3,3,0,3)
  D := [[0, 3, 3, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_137_4 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨137, by decide⟩
  m := 1
  T1 := T147_137
  T2 := Q2.T147_137_2
  h1 := (0,4,4,0,1)
  h2 := (0,4,4,0,1)
  D := [[0, 4, 4, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_137_5 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨137, by decide⟩
  m := 1
  T1 := T147_137
  T2 := Q2.T147_137_2
  h1 := (1,0,1,4,0)
  h2 := (1,0,1,4,0)
  D := [[1, 0, 1, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_137_6 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨137, by decide⟩
  m := 1
  T1 := T147_137
  T2 := Q2.T147_137_2
  h1 := (1,1,2,4,1)
  h2 := (1,1,2,4,1)
  D := [[1, 1, 2, 3, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_137_7 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨137, by decide⟩
  m := 1
  T1 := T147_137
  T2 := Q2.T147_137_2
  h1 := (1,2,3,4,3)
  h2 := (1,2,3,4,3)
  D := [[1, 2, 3, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_137_8 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨137, by decide⟩
  m := 1
  T1 := T147_137
  T2 := Q2.T147_137_2
  h1 := (1,3,4,4,1)
  h2 := (1,3,4,4,1)
  D := [[1, 3, 4, 1, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_137_9 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨137, by decide⟩
  m := 1
  T1 := T147_137
  T2 := Q2.T147_137_2
  h1 := (1,4,0,4,0)
  h2 := (1,4,0,4,0)
  D := [[1, 4, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_137_10 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨137, by decide⟩
  m := 1
  T1 := T147_137
  T2 := Q2.T147_137_2
  h1 := (2,0,2,3,4)
  h2 := (2,0,2,3,4)
  D := [[2, 0, 2, 3, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_137_11 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨137, by decide⟩
  m := 1
  T1 := T147_137
  T2 := Q2.T147_137_2
  h1 := (2,1,3,3,1)
  h2 := (2,1,3,3,1)
  D := [[2, 1, 3, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_137_12 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨137, by decide⟩
  m := 1
  T1 := T147_137
  T2 := Q2.T147_137_2
  h1 := (2,2,4,3,4)
  h2 := (2,2,4,3,4)
  D := [[2, 2, 4, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_137_13 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨137, by decide⟩
  m := 1
  T1 := T147_137
  T2 := Q2.T147_137_2
  h1 := (2,3,0,3,3)
  h2 := (2,3,0,3,3)
  D := [[2, 3, 0, 2, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_137_14 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨137, by decide⟩
  m := 1
  T1 := T147_137
  T2 := Q2.T147_137_2
  h1 := (2,4,1,3,3)
  h2 := (2,4,1,3,3)
  D := [[2, 4, 1, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_137_15 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨137, by decide⟩
  m := 1
  T1 := T147_137
  T2 := Q2.T147_137_2
  h1 := (3,0,3,2,2)
  h2 := (3,0,3,2,2)
  D := [[3, 0, 3, 2, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_137_16 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨137, by decide⟩
  m := 1
  T1 := T147_137
  T2 := Q2.T147_137_2
  h1 := (3,1,4,2,0)
  h2 := (3,1,4,2,0)
  D := [[3, 1, 4, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_137_17 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨137, by decide⟩
  m := 1
  T1 := T147_137
  T2 := Q2.T147_137_2
  h1 := (3,2,0,2,4)
  h2 := (3,2,0,2,4)
  D := [[3, 2, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_137_18 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨137, by decide⟩
  m := 1
  T1 := T147_137
  T2 := Q2.T147_137_2
  h1 := (3,3,1,2,4)
  h2 := (3,3,1,2,4)
  D := [[3, 3, 1, 3, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_137_19 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨137, by decide⟩
  m := 1
  T1 := T147_137
  T2 := Q2.T147_137_2
  h1 := (3,4,2,2,0)
  h2 := (3,4,2,2,0)
  D := [[3, 4, 2, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_137_20 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨137, by decide⟩
  m := 1
  T1 := T147_137
  T2 := Q2.T147_137_2
  h1 := (4,0,4,1,4)
  h2 := (4,0,4,1,4)
  D := [[4, 0, 4, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_137_21 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨137, by decide⟩
  m := 1
  T1 := T147_137
  T2 := Q2.T147_137_2
  h1 := (4,1,0,1,3)
  h2 := (4,1,0,1,3)
  D := [[4, 1, 0, 2, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_137_22 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨137, by decide⟩
  m := 1
  T1 := T147_137
  T2 := Q2.T147_137_2
  h1 := (4,2,1,1,3)
  h2 := (4,2,1,1,3)
  D := [[4, 2, 1, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_137_23 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨137, by decide⟩
  m := 1
  T1 := T147_137
  T2 := Q2.T147_137_2
  h1 := (4,3,2,1,4)
  h2 := (4,3,2,1,4)
  D := [[4, 3, 2, 4, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_137_24 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨137, by decide⟩
  m := 1
  T1 := T147_137
  T2 := Q2.T147_137_2
  h1 := (4,4,3,1,1)
  h2 := (4,4,3,1,1)
  D := [[4, 4, 3, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_138_0 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨138, by decide⟩
  m := 1
  T1 := T147_138
  T2 := Q2.T147_138_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_138_7 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨138, by decide⟩
  m := 1
  T1 := T147_138
  T2 := Q2.T147_138_2
  h1 := (1,2,0,3,3)
  h2 := (1,2,0,3,3)
  D := [[1, 2, 0, 1, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_138_14 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨138, by decide⟩
  m := 1
  T1 := T147_138
  T2 := Q2.T147_138_2
  h1 := (2,4,0,1,1)
  h2 := (2,4,0,1,1)
  D := [[2, 4, 0, 3, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_138_16 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨138, by decide⟩
  m := 1
  T1 := T147_138
  T2 := Q2.T147_138_2
  h1 := (3,1,0,4,4)
  h2 := (3,1,0,4,4)
  D := [[3, 1, 0, 1, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_138_23 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨138, by decide⟩
  m := 1
  T1 := T147_138
  T2 := Q2.T147_138_2
  h1 := (4,3,0,2,2)
  h2 := (4,3,0,2,2)
  D := [[4, 3, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_139_0 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨139, by decide⟩
  m := 1
  T1 := T147_139
  T2 := Q2.T147_139_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_139_8 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨139, by decide⟩
  m := 1
  T1 := T147_139
  T2 := Q2.T147_139_2
  h1 := (1,3,0,1,2)
  h2 := (1,3,0,1,2)
  D := [[1, 3, 0, 3, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_139_11 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨139, by decide⟩
  m := 1
  T1 := T147_139
  T2 := Q2.T147_139_2
  h1 := (2,1,0,2,3)
  h2 := (2,1,0,2,3)
  D := [[2, 1, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_139_19 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨139, by decide⟩
  m := 1
  T1 := T147_139
  T2 := Q2.T147_139_2
  h1 := (3,4,0,3,3)
  h2 := (3,4,0,3,3)
  D := [[3, 4, 0, 1, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_139_22 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨139, by decide⟩
  m := 1
  T1 := T147_139
  T2 := Q2.T147_139_2
  h1 := (4,2,0,4,2)
  h2 := (4,2,0,4,2)
  D := [[4, 2, 0, 1, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_140_0 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨140, by decide⟩
  m := 1
  T1 := T147_140
  T2 := Q2.T147_140_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_140_6 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨140, by decide⟩
  m := 1
  T1 := T147_140
  T2 := Q2.T147_140_2
  h1 := (1,1,0,0,0)
  h2 := (1,1,0,0,0)
  D := [[1, 1, 0, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_140_12 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨140, by decide⟩
  m := 1
  T1 := T147_140
  T2 := Q2.T147_140_2
  h1 := (2,2,0,0,1)
  h2 := (2,2,0,0,1)
  D := [[2, 2, 0, 1, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_140_18 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨140, by decide⟩
  m := 1
  T1 := T147_140
  T2 := Q2.T147_140_2
  h1 := (3,3,0,0,3)
  h2 := (3,3,0,0,3)
  D := [[3, 3, 0, 1, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_140_24 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨140, by decide⟩
  m := 1
  T1 := T147_140
  T2 := Q2.T147_140_2
  h1 := (4,4,0,0,1)
  h2 := (4,4,0,0,1)
  D := [[4, 4, 0, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_141_0 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨141, by decide⟩
  m := 1
  T1 := T147_141
  T2 := Q2.T147_141_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_141_1 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨141, by decide⟩
  m := 1
  T1 := T147_141
  T2 := Q2.T147_141_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_141_2 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨141, by decide⟩
  m := 1
  T1 := T147_141
  T2 := Q2.T147_141_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

end LeanDring.P5Presentation
