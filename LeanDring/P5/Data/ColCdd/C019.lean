/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.Twin1.ColCert
import LeanDring.P5.Data.EntryK.C038
import LeanDring.P5.Data.EntryK.C039

/-!
# Species-table cell data, stage 2 — column-data-divergent columns

Per-column certified exponent-vector data (`ColCert`/`ColCertDiv`) with kernel
`decide` bindings. Emitted; the embedded lists are what the kernel certifies.
cdd tier, chunk 18: 60 columns.
-/

-- machine-emitted data: silence style linters (generated long lines, file-level options)
set_option linter.style.longLine false

namespace LeanDring.P5Presentation

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

def colCertDiv_138_104_15 : ColCertDiv where
  rK := ⟨138, by decide⟩
  rH := ⟨104, by decide⟩
  m := 5
  T1 := T138_104
  T2 := Q2.T138_104_2
  h1 := (3,3,4,3,0)
  h2 := (3,3,4,3,0)
  D1 := [[3, 3, 0, 2], [3, 3, 0, 4], [3, 3, 0, 1], [3, 3, 0, 3], [3, 3, 0, 0]]
  D2 := [[3, 3, 0, 0], [3, 3, 0, 2], [3, 3, 0, 4], [3, 3, 0, 1], [3, 3, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_138_104_20 : ColCertDiv where
  rK := ⟨138, by decide⟩
  rH := ⟨104, by decide⟩
  m := 5
  T1 := T138_104
  T2 := Q2.T138_104_2
  h1 := (4,4,2,1,2)
  h2 := (4,4,2,1,2)
  D1 := [[4, 4, 3, 4], [4, 4, 3, 0], [4, 4, 3, 1], [4, 4, 3, 2], [4, 4, 3, 3]]
  D2 := [[4, 4, 3, 3], [4, 4, 3, 4], [4, 4, 3, 0], [4, 4, 3, 1], [4, 4, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_138_106_5 : ColCertDiv where
  rK := ⟨138, by decide⟩
  rH := ⟨106, by decide⟩
  m := 5
  T1 := T138_106
  T2 := Q2.T138_106_2
  h1 := (1,4,4,4,1)
  h2 := (1,4,4,4,1)
  D1 := [[1, 4, 2, 3], [1, 4, 2, 4], [1, 4, 2, 0], [1, 4, 2, 1], [1, 4, 2, 2]]
  D2 := [[1, 4, 2, 1], [1, 4, 2, 2], [1, 4, 2, 3], [1, 4, 2, 4], [1, 4, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_138_106_10 : ColCertDiv where
  rK := ⟨138, by decide⟩
  rH := ⟨106, by decide⟩
  m := 5
  T1 := T138_106
  T2 := Q2.T138_106_2
  h1 := (2,3,3,2,3)
  h2 := (2,3,3,2,4)
  D1 := [[2, 3, 0, 3], [2, 3, 0, 0], [2, 3, 0, 2], [2, 3, 0, 4], [2, 3, 0, 1]]
  D2 := [[2, 3, 0, 0], [2, 3, 0, 2], [2, 3, 0, 4], [2, 3, 0, 1], [2, 3, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_138_106_15 : ColCertDiv where
  rK := ⟨138, by decide⟩
  rH := ⟨106, by decide⟩
  m := 5
  T1 := T138_106
  T2 := Q2.T138_106_2
  h1 := (3,2,2,4,4)
  h2 := (3,2,2,4,1)
  D1 := [[3, 2, 4, 3], [3, 2, 4, 1], [3, 2, 4, 4], [3, 2, 4, 2], [3, 2, 4, 0]]
  D2 := [[3, 2, 4, 4], [3, 2, 4, 2], [3, 2, 4, 0], [3, 2, 4, 3], [3, 2, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_138_112_15 : ColCertDiv where
  rK := ⟨138, by decide⟩
  rH := ⟨112, by decide⟩
  m := 5
  T1 := T138_112
  T2 := Q2.T138_112_2
  h1 := (3,1,0,0,1)
  h2 := (3,1,0,0,2)
  D1 := [[3, 1, 3, 0], [3, 1, 3, 4], [3, 1, 3, 3], [3, 1, 3, 2], [3, 1, 3, 1]]
  D2 := [[3, 1, 3, 1], [3, 1, 3, 0], [3, 1, 3, 4], [3, 1, 3, 3], [3, 1, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_138_112_20 : ColCertDiv where
  rK := ⟨138, by decide⟩
  rH := ⟨112, by decide⟩
  m := 5
  T1 := T138_112
  T2 := Q2.T138_112_2
  h1 := (4,3,0,4,4)
  h2 := (4,3,0,4,0)
  D1 := [[4, 3, 0, 2], [4, 3, 0, 4], [4, 3, 0, 1], [4, 3, 0, 3], [4, 3, 0, 0]]
  D2 := [[4, 3, 0, 3], [4, 3, 0, 0], [4, 3, 0, 2], [4, 3, 0, 4], [4, 3, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_139_5_1 : ColCertDiv where
  rK := ⟨139, by decide⟩
  rH := ⟨5, by decide⟩
  m := 5
  T1 := T139_5
  T2 := Q2.T139_5_2
  h1 := (1,0,1,4,4)
  h2 := (1,0,1,4,4)
  D1 := [[1, 0, 3, 2], [1, 0, 3, 2], [1, 0, 3, 2], [1, 0, 3, 2], [1, 0, 3, 2]]
  D2 := [[1, 0, 3, 0], [1, 0, 3, 0], [1, 0, 3, 0], [1, 0, 3, 0], [1, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_139_5_2 : ColCertDiv where
  rK := ⟨139, by decide⟩
  rH := ⟨5, by decide⟩
  m := 5
  T1 := T139_5
  T2 := Q2.T139_5_2
  h1 := (2,0,2,3,2)
  h2 := (2,0,2,3,2)
  D1 := [[2, 0, 1, 1], [2, 0, 1, 1], [2, 0, 1, 1], [2, 0, 1, 1], [2, 0, 1, 1]]
  D2 := [[2, 0, 1, 2], [2, 0, 1, 2], [2, 0, 1, 2], [2, 0, 1, 2], [2, 0, 1, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_139_5_3 : ColCertDiv where
  rK := ⟨139, by decide⟩
  rH := ⟨5, by decide⟩
  m := 5
  T1 := T139_5
  T2 := Q2.T139_5_2
  h1 := (3,0,3,2,4)
  h2 := (3,0,3,2,4)
  D1 := [[3, 0, 4, 2], [3, 0, 4, 2], [3, 0, 4, 2], [3, 0, 4, 2], [3, 0, 4, 2]]
  D2 := [[3, 0, 4, 1], [3, 0, 4, 1], [3, 0, 4, 1], [3, 0, 4, 1], [3, 0, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_139_5_4 : ColCertDiv where
  rK := ⟨139, by decide⟩
  rH := ⟨5, by decide⟩
  m := 5
  T1 := T139_5
  T2 := Q2.T139_5_2
  h1 := (4,0,4,1,0)
  h2 := (4,0,4,1,0)
  D1 := [[4, 0, 2, 0], [4, 0, 2, 0], [4, 0, 2, 0], [4, 0, 2, 0], [4, 0, 2, 0]]
  D2 := [[4, 0, 2, 2], [4, 0, 2, 2], [4, 0, 2, 2], [4, 0, 2, 2], [4, 0, 2, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_139_23_5 : ColCertDiv where
  rK := ⟨139, by decide⟩
  rH := ⟨23, by decide⟩
  m := 5
  T1 := T139_23
  T2 := Q2.T139_23_2
  h1 := (1,0,1,4,0)
  h2 := (1,0,1,4,0)
  D1 := [[1, 0, 3, 3], [1, 0, 3, 3], [1, 0, 3, 3], [1, 0, 3, 3], [1, 0, 3, 3]]
  D2 := [[1, 0, 3, 1], [1, 0, 3, 1], [1, 0, 3, 1], [1, 0, 3, 1], [1, 0, 3, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_139_23_10 : ColCertDiv where
  rK := ⟨139, by decide⟩
  rH := ⟨23, by decide⟩
  m := 5
  T1 := T139_23
  T2 := Q2.T139_23_2
  h1 := (2,0,2,3,4)
  h2 := (2,0,2,3,4)
  D1 := [[2, 0, 1, 3], [2, 0, 1, 3], [2, 0, 1, 3], [2, 0, 1, 3], [2, 0, 1, 3]]
  D2 := [[2, 0, 1, 4], [2, 0, 1, 4], [2, 0, 1, 4], [2, 0, 1, 4], [2, 0, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_139_23_15 : ColCertDiv where
  rK := ⟨139, by decide⟩
  rH := ⟨23, by decide⟩
  m := 5
  T1 := T139_23
  T2 := Q2.T139_23_2
  h1 := (3,0,3,2,2)
  h2 := (3,0,3,2,2)
  D1 := [[3, 0, 4, 0], [3, 0, 4, 0], [3, 0, 4, 0], [3, 0, 4, 0], [3, 0, 4, 0]]
  D2 := [[3, 0, 4, 4], [3, 0, 4, 4], [3, 0, 4, 4], [3, 0, 4, 4], [3, 0, 4, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_139_23_20 : ColCertDiv where
  rK := ⟨139, by decide⟩
  rH := ⟨23, by decide⟩
  m := 5
  T1 := T139_23
  T2 := Q2.T139_23_2
  h1 := (4,0,4,1,4)
  h2 := (4,0,4,1,4)
  D1 := [[4, 0, 2, 4], [4, 0, 2, 4], [4, 0, 2, 4], [4, 0, 2, 4], [4, 0, 2, 4]]
  D2 := [[4, 0, 2, 1], [4, 0, 2, 1], [4, 0, 2, 1], [4, 0, 2, 1], [4, 0, 2, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_139_34_5 : ColCertDiv where
  rK := ⟨139, by decide⟩
  rH := ⟨34, by decide⟩
  m := 5
  T1 := T139_34
  T2 := Q2.T139_34_2
  h1 := (1,4,3,3,1)
  h2 := (1,4,3,3,1)
  D1 := [[1, 4, 3, 2], [1, 4, 3, 3], [1, 4, 3, 4], [1, 4, 3, 0], [1, 4, 3, 1]]
  D2 := [[1, 4, 3, 1], [1, 4, 3, 2], [1, 4, 3, 3], [1, 4, 3, 4], [1, 4, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_139_34_10 : ColCertDiv where
  rK := ⟨139, by decide⟩
  rH := ⟨34, by decide⟩
  m := 5
  T1 := T139_34
  T2 := Q2.T139_34_2
  h1 := (2,3,1,0,3)
  h2 := (2,3,1,0,4)
  D1 := [[2, 3, 2, 0], [2, 3, 2, 2], [2, 3, 2, 4], [2, 3, 2, 1], [2, 3, 2, 3]]
  D2 := [[2, 3, 2, 4], [2, 3, 2, 1], [2, 3, 2, 3], [2, 3, 2, 0], [2, 3, 2, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_139_34_15 : ColCertDiv where
  rK := ⟨139, by decide⟩
  rH := ⟨34, by decide⟩
  m := 5
  T1 := T139_34
  T2 := Q2.T139_34_2
  h1 := (3,2,4,1,4)
  h2 := (3,2,4,1,1)
  D1 := [[3, 2, 2, 2], [3, 2, 2, 0], [3, 2, 2, 3], [3, 2, 2, 1], [3, 2, 2, 4]]
  D2 := [[3, 2, 2, 1], [3, 2, 2, 4], [3, 2, 2, 2], [3, 2, 2, 0], [3, 2, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_139_34_20 : ColCertDiv where
  rK := ⟨139, by decide⟩
  rH := ⟨34, by decide⟩
  m := 5
  T1 := T139_34
  T2 := Q2.T139_34_2
  h1 := (4,1,2,1,3)
  h2 := (4,1,2,1,1)
  D1 := [[4, 1, 3, 2], [4, 1, 3, 1], [4, 1, 3, 0], [4, 1, 3, 4], [4, 1, 3, 3]]
  D2 := [[4, 1, 3, 1], [4, 1, 3, 0], [4, 1, 3, 4], [4, 1, 3, 3], [4, 1, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_139_38_5 : ColCertDiv where
  rK := ⟨139, by decide⟩
  rH := ⟨38, by decide⟩
  m := 5
  T1 := T139_38
  T2 := Q2.T139_38_2
  h1 := (0,1,3,4,1)
  h2 := (0,1,3,4,4)
  D1 := [[0, 1, 4, 0], [0, 1, 4, 4], [0, 1, 4, 3], [0, 1, 4, 2], [0, 1, 4, 1]]
  D2 := [[0, 1, 4, 2], [0, 1, 4, 1], [0, 1, 4, 0], [0, 1, 4, 4], [0, 1, 4, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_139_38_10 : ColCertDiv where
  rK := ⟨139, by decide⟩
  rH := ⟨38, by decide⟩
  m := 5
  T1 := T139_38
  T2 := Q2.T139_38_2
  h1 := (0,2,1,3,0)
  h2 := (0,2,1,3,1)
  D1 := [[0, 2, 3, 0], [0, 2, 3, 3], [0, 2, 3, 1], [0, 2, 3, 4], [0, 2, 3, 2]]
  D2 := [[0, 2, 3, 4], [0, 2, 3, 2], [0, 2, 3, 0], [0, 2, 3, 3], [0, 2, 3, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_139_38_15 : ColCertDiv where
  rK := ⟨139, by decide⟩
  rH := ⟨38, by decide⟩
  m := 5
  T1 := T139_38
  T2 := Q2.T139_38_2
  h1 := (0,3,4,2,2)
  h2 := (0,3,4,2,1)
  D1 := [[0, 3, 2, 0], [0, 3, 2, 2], [0, 3, 2, 4], [0, 3, 2, 1], [0, 3, 2, 3]]
  D2 := [[0, 3, 2, 1], [0, 3, 2, 3], [0, 3, 2, 0], [0, 3, 2, 2], [0, 3, 2, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_139_38_20 : ColCertDiv where
  rK := ⟨139, by decide⟩
  rH := ⟨38, by decide⟩
  m := 5
  T1 := T139_38
  T2 := Q2.T139_38_2
  h1 := (0,4,2,1,2)
  h2 := (0,4,2,1,4)
  D1 := [[0, 4, 1, 0], [0, 4, 1, 1], [0, 4, 1, 2], [0, 4, 1, 3], [0, 4, 1, 4]]
  D2 := [[0, 4, 1, 3], [0, 4, 1, 4], [0, 4, 1, 0], [0, 4, 1, 1], [0, 4, 1, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_139_45_5 : ColCertDiv where
  rK := ⟨139, by decide⟩
  rH := ⟨45, by decide⟩
  m := 5
  T1 := T139_45
  T2 := Q2.T139_45_2
  h1 := (1,2,2,2,1)
  h2 := (1,2,2,2,3)
  D1 := [[1, 2, 4, 3], [1, 2, 4, 1], [1, 2, 4, 4], [1, 2, 4, 2], [1, 2, 4, 0]]
  D2 := [[1, 2, 4, 1], [1, 2, 4, 4], [1, 2, 4, 2], [1, 2, 4, 0], [1, 2, 4, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_139_45_10 : ColCertDiv where
  rK := ⟨139, by decide⟩
  rH := ⟨45, by decide⟩
  m := 5
  T1 := T139_45
  T2 := Q2.T139_45_2
  h1 := (2,4,4,1,3)
  h2 := (2,4,4,1,2)
  D1 := [[2, 4, 1, 1], [2, 4, 1, 2], [2, 4, 1, 3], [2, 4, 1, 4], [2, 4, 1, 0]]
  D2 := [[2, 4, 1, 2], [2, 4, 1, 3], [2, 4, 1, 4], [2, 4, 1, 0], [2, 4, 1, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_139_45_20 : ColCertDiv where
  rK := ⟨139, by decide⟩
  rH := ⟨45, by decide⟩
  m := 5
  T1 := T139_45
  T2 := Q2.T139_45_2
  h1 := (4,3,3,0,4)
  h2 := (4,3,3,0,3)
  D1 := [[4, 3, 4, 1], [4, 3, 4, 3], [4, 3, 4, 0], [4, 3, 4, 2], [4, 3, 4, 4]]
  D2 := [[4, 3, 4, 4], [4, 3, 4, 1], [4, 3, 4, 3], [4, 3, 4, 0], [4, 3, 4, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_139_51_5 : ColCertDiv where
  rK := ⟨139, by decide⟩
  rH := ⟨51, by decide⟩
  m := 5
  T1 := T139_51
  T2 := Q2.T139_51_2
  h1 := (1,3,0,0,3)
  h2 := (1,3,0,0,4)
  D1 := [[1, 3, 1, 1], [1, 3, 1, 3], [1, 3, 1, 0], [1, 3, 1, 2], [1, 3, 1, 4]]
  D2 := [[1, 3, 1, 2], [1, 3, 1, 4], [1, 3, 1, 1], [1, 3, 1, 3], [1, 3, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_139_51_10 : ColCertDiv where
  rK := ⟨139, by decide⟩
  rH := ⟨51, by decide⟩
  m := 5
  T1 := T139_51
  T2 := Q2.T139_51_2
  h1 := (2,1,0,3,2)
  h2 := (2,1,0,3,0)
  D1 := [[2, 1, 4, 3], [2, 1, 4, 2], [2, 1, 4, 1], [2, 1, 4, 0], [2, 1, 4, 4]]
  D2 := [[2, 1, 4, 1], [2, 1, 4, 0], [2, 1, 4, 4], [2, 1, 4, 3], [2, 1, 4, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_139_51_15 : ColCertDiv where
  rK := ⟨139, by decide⟩
  rH := ⟨51, by decide⟩
  m := 5
  T1 := T139_51
  T2 := Q2.T139_51_2
  h1 := (3,4,0,4,3)
  h2 := (3,4,0,4,2)
  D1 := [[3, 4, 4, 2], [3, 4, 4, 3], [3, 4, 4, 4], [3, 4, 4, 0], [3, 4, 4, 1]]
  D2 := [[3, 4, 4, 1], [3, 4, 4, 2], [3, 4, 4, 3], [3, 4, 4, 4], [3, 4, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_139_51_20 : ColCertDiv where
  rK := ⟨139, by decide⟩
  rH := ⟨51, by decide⟩
  m := 5
  T1 := T139_51
  T2 := Q2.T139_51_2
  h1 := (4,2,0,3,1)
  h2 := (4,2,0,3,2)
  D1 := [[4, 2, 1, 3], [4, 2, 1, 1], [4, 2, 1, 4], [4, 2, 1, 2], [4, 2, 1, 0]]
  D2 := [[4, 2, 1, 4], [4, 2, 1, 2], [4, 2, 1, 0], [4, 2, 1, 3], [4, 2, 1, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_139_84_5 : ColCertDiv where
  rK := ⟨139, by decide⟩
  rH := ⟨84, by decide⟩
  m := 5
  T1 := T139_84
  T2 := Q2.T139_84_2
  h1 := (1,0,1,0,0)
  h2 := (1,0,1,0,0)
  D1 := [[1, 0, 4, 2], [1, 0, 4, 2], [1, 0, 4, 2], [1, 0, 4, 2], [1, 0, 4, 2]]
  D2 := [[1, 0, 4, 0], [1, 0, 4, 0], [1, 0, 4, 0], [1, 0, 4, 0], [1, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_139_84_10 : ColCertDiv where
  rK := ⟨139, by decide⟩
  rH := ⟨84, by decide⟩
  m := 5
  T1 := T139_84
  T2 := Q2.T139_84_2
  h1 := (2,0,2,0,0)
  h2 := (2,0,2,0,0)
  D1 := [[2, 0, 3, 0], [2, 0, 3, 0], [2, 0, 3, 0], [2, 0, 3, 0], [2, 0, 3, 0]]
  D2 := [[2, 0, 3, 1], [2, 0, 3, 1], [2, 0, 3, 1], [2, 0, 3, 1], [2, 0, 3, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_139_84_15 : ColCertDiv where
  rK := ⟨139, by decide⟩
  rH := ⟨84, by decide⟩
  m := 5
  T1 := T139_84
  T2 := Q2.T139_84_2
  h1 := (3,0,3,0,0)
  h2 := (3,0,3,0,0)
  D1 := [[3, 0, 2, 4], [3, 0, 2, 4], [3, 0, 2, 4], [3, 0, 2, 4], [3, 0, 2, 4]]
  D2 := [[3, 0, 2, 3], [3, 0, 2, 3], [3, 0, 2, 3], [3, 0, 2, 3], [3, 0, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_139_84_20 : ColCertDiv where
  rK := ⟨139, by decide⟩
  rH := ⟨84, by decide⟩
  m := 5
  T1 := T139_84
  T2 := Q2.T139_84_2
  h1 := (4,0,4,0,0)
  h2 := (4,0,4,0,0)
  D1 := [[4, 0, 1, 4], [4, 0, 1, 4], [4, 0, 1, 4], [4, 0, 1, 4], [4, 0, 1, 4]]
  D2 := [[4, 0, 1, 1], [4, 0, 1, 1], [4, 0, 1, 1], [4, 0, 1, 1], [4, 0, 1, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_139_94_5 : ColCertDiv where
  rK := ⟨139, by decide⟩
  rH := ⟨94, by decide⟩
  m := 5
  T1 := T139_94
  T2 := Q2.T139_94_2
  h1 := (1,1,4,0,0)
  h2 := (1,1,4,0,0)
  D1 := [[1, 1, 3, 2], [1, 1, 3, 1], [1, 1, 3, 0], [1, 1, 3, 4], [1, 1, 3, 3]]
  D2 := [[1, 1, 3, 4], [1, 1, 3, 3], [1, 1, 3, 2], [1, 1, 3, 1], [1, 1, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_139_94_10 : ColCertDiv where
  rK := ⟨139, by decide⟩
  rH := ⟨94, by decide⟩
  m := 5
  T1 := T139_94
  T2 := Q2.T139_94_2
  h1 := (2,2,3,1,4)
  h2 := (2,2,3,1,4)
  D1 := [[2, 2, 0, 3], [2, 2, 0, 1], [2, 2, 0, 4], [2, 2, 0, 2], [2, 2, 0, 0]]
  D2 := [[2, 2, 0, 2], [2, 2, 0, 0], [2, 2, 0, 3], [2, 2, 0, 1], [2, 2, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_139_94_15 : ColCertDiv where
  rK := ⟨139, by decide⟩
  rH := ⟨94, by decide⟩
  m := 5
  T1 := T139_94
  T2 := Q2.T139_94_2
  h1 := (3,3,2,3,3)
  h2 := (3,3,2,3,3)
  D1 := [[3, 3, 1, 4], [3, 3, 1, 1], [3, 3, 1, 3], [3, 3, 1, 0], [3, 3, 1, 2]]
  D2 := [[3, 3, 1, 0], [3, 3, 1, 2], [3, 3, 1, 4], [3, 3, 1, 1], [3, 3, 1, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_139_94_20 : ColCertDiv where
  rK := ⟨139, by decide⟩
  rH := ⟨94, by decide⟩
  m := 5
  T1 := T139_94
  T2 := Q2.T139_94_2
  h1 := (4,4,1,1,3)
  h2 := (4,4,1,1,3)
  D1 := [[4, 4, 1, 1], [4, 4, 1, 2], [4, 4, 1, 3], [4, 4, 1, 4], [4, 4, 1, 0]]
  D2 := [[4, 4, 1, 4], [4, 4, 1, 0], [4, 4, 1, 1], [4, 4, 1, 2], [4, 4, 1, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_139_96_5 : ColCertDiv where
  rK := ⟨139, by decide⟩
  rH := ⟨96, by decide⟩
  m := 5
  T1 := T139_96
  T2 := Q2.T139_96_2
  h1 := (1,4,3,4,2)
  h2 := (1,4,3,4,2)
  D1 := [[1, 4, 4, 2], [1, 4, 4, 3], [1, 4, 4, 4], [1, 4, 4, 0], [1, 4, 4, 1]]
  D2 := [[1, 4, 4, 1], [1, 4, 4, 2], [1, 4, 4, 3], [1, 4, 4, 4], [1, 4, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_139_96_10 : ColCertDiv where
  rK := ⟨139, by decide⟩
  rH := ⟨96, by decide⟩
  m := 5
  T1 := T139_96
  T2 := Q2.T139_96_2
  h1 := (2,3,1,2,1)
  h2 := (2,3,1,2,2)
  D1 := [[2, 3, 4, 4], [2, 3, 4, 1], [2, 3, 4, 3], [2, 3, 4, 0], [2, 3, 4, 2]]
  D2 := [[2, 3, 4, 3], [2, 3, 4, 0], [2, 3, 4, 2], [2, 3, 4, 4], [2, 3, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_139_96_15 : ColCertDiv where
  rK := ⟨139, by decide⟩
  rH := ⟨96, by decide⟩
  m := 5
  T1 := T139_96
  T2 := Q2.T139_96_2
  h1 := (3,2,4,4,0)
  h2 := (3,2,4,4,2)
  D1 := [[3, 2, 0, 4], [3, 2, 0, 2], [3, 2, 0, 0], [3, 2, 0, 3], [3, 2, 0, 1]]
  D2 := [[3, 2, 0, 3], [3, 2, 0, 1], [3, 2, 0, 4], [3, 2, 0, 2], [3, 2, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_139_96_20 : ColCertDiv where
  rK := ⟨139, by decide⟩
  rH := ⟨96, by decide⟩
  m := 5
  T1 := T139_96
  T2 := Q2.T139_96_2
  h1 := (4,1,2,0,3)
  h2 := (4,1,2,0,1)
  D1 := [[4, 1, 2, 1], [4, 1, 2, 0], [4, 1, 2, 4], [4, 1, 2, 3], [4, 1, 2, 2]]
  D2 := [[4, 1, 2, 0], [4, 1, 2, 4], [4, 1, 2, 3], [4, 1, 2, 2], [4, 1, 2, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_139_100_25 : ColCertDiv where
  rK := ⟨139, by decide⟩
  rH := ⟨100, by decide⟩
  m := 5
  T1 := T139_100
  T2 := Q2.T139_100_2
  h1 := (0,1,3,0,0)
  h2 := (0,1,3,0,0)
  D1 := [[0, 1, 0, 4], [0, 1, 0, 3], [0, 1, 0, 2], [0, 1, 0, 1], [0, 1, 0, 0]]
  D2 := [[0, 1, 0, 3], [0, 1, 0, 2], [0, 1, 0, 1], [0, 1, 0, 0], [0, 1, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_139_100_50 : ColCertDiv where
  rK := ⟨139, by decide⟩
  rH := ⟨100, by decide⟩
  m := 5
  T1 := T139_100
  T2 := Q2.T139_100_2
  h1 := (0,2,1,0,3)
  h2 := (0,2,1,0,3)
  D1 := [[0, 2, 0, 3], [0, 2, 0, 1], [0, 2, 0, 4], [0, 2, 0, 2], [0, 2, 0, 0]]
  D2 := [[0, 2, 0, 1], [0, 2, 0, 4], [0, 2, 0, 2], [0, 2, 0, 0], [0, 2, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_139_100_75 : ColCertDiv where
  rK := ⟨139, by decide⟩
  rH := ⟨100, by decide⟩
  m := 5
  T1 := T139_100
  T2 := Q2.T139_100_2
  h1 := (0,3,4,0,4)
  h2 := (0,3,4,0,4)
  D1 := [[0, 3, 0, 2], [0, 3, 0, 4], [0, 3, 0, 1], [0, 3, 0, 3], [0, 3, 0, 0]]
  D2 := [[0, 3, 0, 4], [0, 3, 0, 1], [0, 3, 0, 3], [0, 3, 0, 0], [0, 3, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_139_100_100 : ColCertDiv where
  rK := ⟨139, by decide⟩
  rH := ⟨100, by decide⟩
  m := 5
  T1 := T139_100
  T2 := Q2.T139_100_2
  h1 := (0,4,2,0,3)
  h2 := (0,4,2,0,3)
  D1 := [[0, 4, 0, 1], [0, 4, 0, 2], [0, 4, 0, 3], [0, 4, 0, 4], [0, 4, 0, 0]]
  D2 := [[0, 4, 0, 2], [0, 4, 0, 3], [0, 4, 0, 4], [0, 4, 0, 0], [0, 4, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_139_107_5 : ColCertDiv where
  rK := ⟨139, by decide⟩
  rH := ⟨107, by decide⟩
  m := 5
  T1 := T139_107
  T2 := Q2.T139_107_2
  h1 := (1,2,2,3,4)
  h2 := (1,2,2,3,4)
  D1 := [[1, 2, 0, 0], [1, 2, 0, 3], [1, 2, 0, 1], [1, 2, 0, 4], [1, 2, 0, 2]]
  D2 := [[1, 2, 0, 1], [1, 2, 0, 4], [1, 2, 0, 2], [1, 2, 0, 0], [1, 2, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_139_107_10 : ColCertDiv where
  rK := ⟨139, by decide⟩
  rH := ⟨107, by decide⟩
  m := 5
  T1 := T139_107
  T2 := Q2.T139_107_2
  h1 := (2,4,4,3,0)
  h2 := (2,4,4,3,0)
  D1 := [[2, 4, 3, 4], [2, 4, 3, 0], [2, 4, 3, 1], [2, 4, 3, 2], [2, 4, 3, 3]]
  D2 := [[2, 4, 3, 1], [2, 4, 3, 2], [2, 4, 3, 3], [2, 4, 3, 4], [2, 4, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_139_107_15 : ColCertDiv where
  rK := ⟨139, by decide⟩
  rH := ⟨107, by decide⟩
  m := 5
  T1 := T139_107
  T2 := Q2.T139_107_2
  h1 := (3,1,1,0,1)
  h2 := (3,1,1,0,2)
  D1 := [[3, 1, 4, 0], [3, 1, 4, 4], [3, 1, 4, 3], [3, 1, 4, 2], [3, 1, 4, 1]]
  D2 := [[3, 1, 4, 4], [3, 1, 4, 3], [3, 1, 4, 2], [3, 1, 4, 1], [3, 1, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_139_113_10 : ColCertDiv where
  rK := ⟨139, by decide⟩
  rH := ⟨113, by decide⟩
  m := 5
  T1 := T139_113
  T2 := Q2.T139_113_2
  h1 := (2,1,0,0,1)
  h2 := (2,1,0,0,2)
  D1 := [[2, 1, 1, 3], [2, 1, 1, 2], [2, 1, 1, 1], [2, 1, 1, 0], [2, 1, 1, 4]]
  D2 := [[2, 1, 1, 4], [2, 1, 1, 3], [2, 1, 1, 2], [2, 1, 1, 1], [2, 1, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_139_113_15 : ColCertDiv where
  rK := ⟨139, by decide⟩
  rH := ⟨113, by decide⟩
  m := 5
  T1 := T139_113
  T2 := Q2.T139_113_2
  h1 := (3,4,0,2,3)
  h2 := (3,4,0,2,4)
  D1 := [[3, 4, 2, 3], [3, 4, 2, 4], [3, 4, 2, 0], [3, 4, 2, 1], [3, 4, 2, 2]]
  D2 := [[3, 4, 2, 4], [3, 4, 2, 0], [3, 4, 2, 1], [3, 4, 2, 2], [3, 4, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_139_113_20 : ColCertDiv where
  rK := ⟨139, by decide⟩
  rH := ⟨113, by decide⟩
  m := 5
  T1 := T139_113
  T2 := Q2.T139_113_2
  h1 := (4,2,0,2,3)
  h2 := (4,2,0,2,0)
  D1 := [[4, 2, 0, 4], [4, 2, 0, 2], [4, 2, 0, 0], [4, 2, 0, 3], [4, 2, 0, 1]]
  D2 := [[4, 2, 0, 1], [4, 2, 0, 4], [4, 2, 0, 2], [4, 2, 0, 0], [4, 2, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_140_5_1 : ColCertDiv where
  rK := ⟨140, by decide⟩
  rH := ⟨5, by decide⟩
  m := 5
  T1 := T140_5
  T2 := Q2.T140_5_2
  h1 := (1,0,1,4,4)
  h2 := (1,0,1,4,4)
  D1 := [[1, 0, 4, 3], [1, 0, 4, 3], [1, 0, 4, 3], [1, 0, 4, 3], [1, 0, 4, 3]]
  D2 := [[1, 0, 4, 1], [1, 0, 4, 1], [1, 0, 4, 1], [1, 0, 4, 1], [1, 0, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_140_5_2 : ColCertDiv where
  rK := ⟨140, by decide⟩
  rH := ⟨5, by decide⟩
  m := 5
  T1 := T140_5
  T2 := Q2.T140_5_2
  h1 := (2,0,2,3,2)
  h2 := (2,0,2,3,2)
  D1 := [[2, 0, 3, 2], [2, 0, 3, 2], [2, 0, 3, 2], [2, 0, 3, 2], [2, 0, 3, 2]]
  D2 := [[2, 0, 3, 3], [2, 0, 3, 3], [2, 0, 3, 3], [2, 0, 3, 3], [2, 0, 3, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_140_5_3 : ColCertDiv where
  rK := ⟨140, by decide⟩
  rH := ⟨5, by decide⟩
  m := 5
  T1 := T140_5
  T2 := Q2.T140_5_2
  h1 := (3,0,3,2,4)
  h2 := (3,0,3,2,4)
  D1 := [[3, 0, 2, 2], [3, 0, 2, 2], [3, 0, 2, 2], [3, 0, 2, 2], [3, 0, 2, 2]]
  D2 := [[3, 0, 2, 1], [3, 0, 2, 1], [3, 0, 2, 1], [3, 0, 2, 1], [3, 0, 2, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_140_5_4 : ColCertDiv where
  rK := ⟨140, by decide⟩
  rH := ⟨5, by decide⟩
  m := 5
  T1 := T140_5
  T2 := Q2.T140_5_2
  h1 := (4,0,4,1,0)
  h2 := (4,0,4,1,0)
  D1 := [[4, 0, 1, 3], [4, 0, 1, 3], [4, 0, 1, 3], [4, 0, 1, 3], [4, 0, 1, 3]]
  D2 := [[4, 0, 1, 0], [4, 0, 1, 0], [4, 0, 1, 0], [4, 0, 1, 0], [4, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_140_23_5 : ColCertDiv where
  rK := ⟨140, by decide⟩
  rH := ⟨23, by decide⟩
  m := 5
  T1 := T140_23
  T2 := Q2.T140_23_2
  h1 := (1,0,1,4,0)
  h2 := (1,0,1,4,0)
  D1 := [[1, 0, 4, 4], [1, 0, 4, 4], [1, 0, 4, 4], [1, 0, 4, 4], [1, 0, 4, 4]]
  D2 := [[1, 0, 4, 2], [1, 0, 4, 2], [1, 0, 4, 2], [1, 0, 4, 2], [1, 0, 4, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_140_23_10 : ColCertDiv where
  rK := ⟨140, by decide⟩
  rH := ⟨23, by decide⟩
  m := 5
  T1 := T140_23
  T2 := Q2.T140_23_2
  h1 := (2,0,2,3,4)
  h2 := (2,0,2,3,4)
  D1 := [[2, 0, 3, 4], [2, 0, 3, 4], [2, 0, 3, 4], [2, 0, 3, 4], [2, 0, 3, 4]]
  D2 := [[2, 0, 3, 0], [2, 0, 3, 0], [2, 0, 3, 0], [2, 0, 3, 0], [2, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_140_23_15 : ColCertDiv where
  rK := ⟨140, by decide⟩
  rH := ⟨23, by decide⟩
  m := 5
  T1 := T140_23
  T2 := Q2.T140_23_2
  h1 := (3,0,3,2,2)
  h2 := (3,0,3,2,2)
  D1 := [[3, 0, 2, 0], [3, 0, 2, 0], [3, 0, 2, 0], [3, 0, 2, 0], [3, 0, 2, 0]]
  D2 := [[3, 0, 2, 4], [3, 0, 2, 4], [3, 0, 2, 4], [3, 0, 2, 4], [3, 0, 2, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_140_23_20 : ColCertDiv where
  rK := ⟨140, by decide⟩
  rH := ⟨23, by decide⟩
  m := 5
  T1 := T140_23
  T2 := Q2.T140_23_2
  h1 := (4,0,4,1,4)
  h2 := (4,0,4,1,4)
  D1 := [[4, 0, 1, 2], [4, 0, 1, 2], [4, 0, 1, 2], [4, 0, 1, 2], [4, 0, 1, 2]]
  D2 := [[4, 0, 1, 4], [4, 0, 1, 4], [4, 0, 1, 4], [4, 0, 1, 4], [4, 0, 1, 4]]
  bind1 := by decide
  bind2 := by decide

end LeanDring.P5Presentation
