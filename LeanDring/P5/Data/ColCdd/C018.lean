/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.Twin1.ColCert
import LeanDring.P5.Data.EntryK.C037
import LeanDring.P5.Data.EntryK.C038

/-!
# Species-table cell data, stage 2 — column-data-divergent columns

Per-column certified exponent-vector data (`ColCert`/`ColCertDiv`) with kernel
`decide` bindings. Emitted; the embedded lists are what the kernel certifies.
cdd tier, chunk 17: 60 columns.
-/

-- machine-emitted data: silence style linters (generated long lines, file-level options)
set_option linter.style.longLine false

namespace LeanDring.P5Presentation

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

def colCertDiv_137_37_20 : ColCertDiv where
  rK := ⟨137, by decide⟩
  rH := ⟨37, by decide⟩
  m := 5
  T1 := T137_37
  T2 := Q2.T137_37_2
  h1 := (4,4,3,2,2)
  h2 := (4,4,3,2,4)
  D1 := [[4, 4, 0, 0], [4, 4, 0, 1], [4, 4, 0, 2], [4, 4, 0, 3], [4, 4, 0, 4]]
  D2 := [[4, 4, 0, 2], [4, 4, 0, 3], [4, 4, 0, 4], [4, 4, 0, 0], [4, 4, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_137_41_5 : ColCertDiv where
  rK := ⟨137, by decide⟩
  rH := ⟨41, by decide⟩
  m := 5
  T1 := T137_41
  T2 := Q2.T137_41_2
  h1 := (1,3,4,0,0)
  h2 := (1,3,4,0,1)
  D1 := [[1, 3, 3, 3], [1, 3, 3, 0], [1, 3, 3, 2], [1, 3, 3, 4], [1, 3, 3, 1]]
  D2 := [[1, 3, 3, 4], [1, 3, 3, 1], [1, 3, 3, 3], [1, 3, 3, 0], [1, 3, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_137_41_10 : ColCertDiv where
  rK := ⟨137, by decide⟩
  rH := ⟨41, by decide⟩
  m := 5
  T1 := T137_41
  T2 := Q2.T137_41_2
  h1 := (2,1,3,3,3)
  h2 := (2,1,3,3,1)
  D1 := [[2, 1, 3, 0], [2, 1, 3, 4], [2, 1, 3, 3], [2, 1, 3, 2], [2, 1, 3, 1]]
  D2 := [[2, 1, 3, 3], [2, 1, 3, 2], [2, 1, 3, 1], [2, 1, 3, 0], [2, 1, 3, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_137_41_15 : ColCertDiv where
  rK := ⟨137, by decide⟩
  rH := ⟨41, by decide⟩
  m := 5
  T1 := T137_41
  T2 := Q2.T137_41_2
  h1 := (3,4,2,4,0)
  h2 := (3,4,2,4,4)
  D1 := [[3, 4, 0, 2], [3, 4, 0, 3], [3, 4, 0, 4], [3, 4, 0, 0], [3, 4, 0, 1]]
  D2 := [[3, 4, 0, 1], [3, 4, 0, 2], [3, 4, 0, 3], [3, 4, 0, 4], [3, 4, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_137_41_20 : ColCertDiv where
  rK := ⟨137, by decide⟩
  rH := ⟨41, by decide⟩
  m := 5
  T1 := T137_41
  T2 := Q2.T137_41_2
  h1 := (4,2,1,3,1)
  h2 := (4,2,1,3,2)
  D1 := [[4, 2, 4, 4], [4, 2, 4, 2], [4, 2, 4, 0], [4, 2, 4, 3], [4, 2, 4, 1]]
  D2 := [[4, 2, 4, 0], [4, 2, 4, 3], [4, 2, 4, 1], [4, 2, 4, 4], [4, 2, 4, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_137_43_5 : ColCertDiv where
  rK := ⟨137, by decide⟩
  rH := ⟨43, by decide⟩
  m := 5
  T1 := T137_43
  T2 := Q2.T137_43_2
  h1 := (0,1,1,4,4)
  h2 := (0,1,1,4,2)
  D1 := [[0, 1, 4, 2], [0, 1, 4, 1], [0, 1, 4, 0], [0, 1, 4, 4], [0, 1, 4, 3]]
  D2 := [[0, 1, 4, 0], [0, 1, 4, 4], [0, 1, 4, 3], [0, 1, 4, 2], [0, 1, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_137_43_10 : ColCertDiv where
  rK := ⟨137, by decide⟩
  rH := ⟨43, by decide⟩
  m := 5
  T1 := T137_43
  T2 := Q2.T137_43_2
  h1 := (0,2,2,3,4)
  h2 := (0,2,2,3,0)
  D1 := [[0, 2, 3, 4], [0, 2, 3, 2], [0, 2, 3, 0], [0, 2, 3, 3], [0, 2, 3, 1]]
  D2 := [[0, 2, 3, 0], [0, 2, 3, 3], [0, 2, 3, 1], [0, 2, 3, 4], [0, 2, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_137_43_15 : ColCertDiv where
  rK := ⟨137, by decide⟩
  rH := ⟨43, by decide⟩
  m := 5
  T1 := T137_43
  T2 := Q2.T137_43_2
  h1 := (0,3,3,2,0)
  h2 := (0,3,3,2,4)
  D1 := [[0, 3, 2, 1], [0, 3, 2, 3], [0, 3, 2, 0], [0, 3, 2, 2], [0, 3, 2, 4]]
  D2 := [[0, 3, 2, 0], [0, 3, 2, 2], [0, 3, 2, 4], [0, 3, 2, 1], [0, 3, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_137_43_20 : ColCertDiv where
  rK := ⟨137, by decide⟩
  rH := ⟨43, by decide⟩
  m := 5
  T1 := T137_43
  T2 := Q2.T137_43_2
  h1 := (0,4,4,1,2)
  h2 := (0,4,4,1,4)
  D1 := [[0, 4, 1, 3], [0, 4, 1, 4], [0, 4, 1, 0], [0, 4, 1, 1], [0, 4, 1, 2]]
  D2 := [[0, 4, 1, 0], [0, 4, 1, 1], [0, 4, 1, 2], [0, 4, 1, 3], [0, 4, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_137_49_10 : ColCertDiv where
  rK := ⟨137, by decide⟩
  rH := ⟨49, by decide⟩
  m := 5
  T1 := T137_49
  T2 := Q2.T137_49_2
  h1 := (2,3,0,0,2)
  h2 := (2,3,0,0,3)
  D1 := [[2, 3, 1, 4], [2, 3, 1, 1], [2, 3, 1, 3], [2, 3, 1, 0], [2, 3, 1, 2]]
  D2 := [[2, 3, 1, 0], [2, 3, 1, 2], [2, 3, 1, 4], [2, 3, 1, 1], [2, 3, 1, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_137_49_15 : ColCertDiv where
  rK := ⟨137, by decide⟩
  rH := ⟨49, by decide⟩
  m := 5
  T1 := T137_49
  T2 := Q2.T137_49_2
  h1 := (3,2,0,1,2)
  h2 := (3,2,0,1,4)
  D1 := [[3, 2, 3, 0], [3, 2, 3, 3], [3, 2, 3, 1], [3, 2, 3, 4], [3, 2, 3, 2]]
  D2 := [[3, 2, 3, 2], [3, 2, 3, 0], [3, 2, 3, 3], [3, 2, 3, 1], [3, 2, 3, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_137_49_20 : ColCertDiv where
  rK := ⟨137, by decide⟩
  rH := ⟨49, by decide⟩
  m := 5
  T1 := T137_49
  T2 := Q2.T137_49_2
  h1 := (4,1,0,1,3)
  h2 := (4,1,0,1,1)
  D1 := [[4, 1, 1, 2], [4, 1, 1, 1], [4, 1, 1, 0], [4, 1, 1, 4], [4, 1, 1, 3]]
  D2 := [[4, 1, 1, 0], [4, 1, 1, 4], [4, 1, 1, 3], [4, 1, 1, 2], [4, 1, 1, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_137_92_15 : ColCertDiv where
  rK := ⟨137, by decide⟩
  rH := ⟨92, by decide⟩
  m := 5
  T1 := T137_92
  T2 := Q2.T137_92_2
  h1 := (3,1,4,0,1)
  h2 := (3,1,4,0,2)
  D1 := [[3, 1, 0, 4], [3, 1, 0, 3], [3, 1, 0, 2], [3, 1, 0, 1], [3, 1, 0, 0]]
  D2 := [[3, 1, 0, 0], [3, 1, 0, 4], [3, 1, 0, 3], [3, 1, 0, 2], [3, 1, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_137_92_20 : ColCertDiv where
  rK := ⟨137, by decide⟩
  rH := ⟨92, by decide⟩
  m := 5
  T1 := T137_92
  T2 := Q2.T137_92_2
  h1 := (4,3,2,4,1)
  h2 := (4,3,2,4,2)
  D1 := [[4, 3, 1, 1], [4, 3, 1, 3], [4, 3, 1, 0], [4, 3, 1, 2], [4, 3, 1, 4]]
  D2 := [[4, 3, 1, 2], [4, 3, 1, 4], [4, 3, 1, 1], [4, 3, 1, 3], [4, 3, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_137_103_10 : ColCertDiv where
  rK := ⟨137, by decide⟩
  rH := ⟨103, by decide⟩
  m := 5
  T1 := T137_103
  T2 := Q2.T137_103_2
  h1 := (2,1,3,0,1)
  h2 := (2,1,3,0,2)
  D1 := [[2, 1, 0, 4], [2, 1, 0, 3], [2, 1, 0, 2], [2, 1, 0, 1], [2, 1, 0, 0]]
  D2 := [[2, 1, 0, 0], [2, 1, 0, 4], [2, 1, 0, 3], [2, 1, 0, 2], [2, 1, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_137_103_15 : ColCertDiv where
  rK := ⟨137, by decide⟩
  rH := ⟨103, by decide⟩
  m := 5
  T1 := T137_103
  T2 := Q2.T137_103_2
  h1 := (3,4,2,2,1)
  h2 := (3,4,2,2,2)
  D1 := [[3, 4, 3, 4], [3, 4, 3, 0], [3, 4, 3, 1], [3, 4, 3, 2], [3, 4, 3, 3]]
  D2 := [[3, 4, 3, 0], [3, 4, 3, 1], [3, 4, 3, 2], [3, 4, 3, 3], [3, 4, 3, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_137_103_20 : ColCertDiv where
  rK := ⟨137, by decide⟩
  rH := ⟨103, by decide⟩
  m := 5
  T1 := T137_103
  T2 := Q2.T137_103_2
  h1 := (4,2,1,2,1)
  h2 := (4,2,1,2,3)
  D1 := [[4, 2, 3, 3], [4, 2, 3, 1], [4, 2, 3, 4], [4, 2, 3, 2], [4, 2, 3, 0]]
  D2 := [[4, 2, 3, 0], [4, 2, 3, 3], [4, 2, 3, 1], [4, 2, 3, 4], [4, 2, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_137_111_10 : ColCertDiv where
  rK := ⟨137, by decide⟩
  rH := ⟨111, by decide⟩
  m := 5
  T1 := T137_111
  T2 := Q2.T137_111_2
  h1 := (2,3,0,2,0)
  h2 := (2,3,0,2,1)
  D1 := [[2, 3, 3, 3], [2, 3, 3, 0], [2, 3, 3, 2], [2, 3, 3, 4], [2, 3, 3, 1]]
  D2 := [[2, 3, 3, 4], [2, 3, 3, 1], [2, 3, 3, 3], [2, 3, 3, 0], [2, 3, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_137_111_15 : ColCertDiv where
  rK := ⟨137, by decide⟩
  rH := ⟨111, by decide⟩
  m := 5
  T1 := T137_111
  T2 := Q2.T137_111_2
  h1 := (3,2,0,4,3)
  h2 := (3,2,0,4,0)
  D1 := [[3, 2, 1, 2], [3, 2, 1, 0], [3, 2, 1, 3], [3, 2, 1, 1], [3, 2, 1, 4]]
  D2 := [[3, 2, 1, 4], [3, 2, 1, 2], [3, 2, 1, 0], [3, 2, 1, 3], [3, 2, 1, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_137_111_20 : ColCertDiv where
  rK := ⟨137, by decide⟩
  rH := ⟨111, by decide⟩
  m := 5
  T1 := T137_111
  T2 := Q2.T137_111_2
  h1 := (4,1,0,0,3)
  h2 := (4,1,0,0,1)
  D1 := [[4, 1, 0, 1], [4, 1, 0, 0], [4, 1, 0, 4], [4, 1, 0, 3], [4, 1, 0, 2]]
  D2 := [[4, 1, 0, 4], [4, 1, 0, 3], [4, 1, 0, 2], [4, 1, 0, 1], [4, 1, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_138_5_1 : ColCertDiv where
  rK := ⟨138, by decide⟩
  rH := ⟨5, by decide⟩
  m := 5
  T1 := T138_5
  T2 := Q2.T138_5_2
  h1 := (1,0,1,4,4)
  h2 := (1,0,1,4,4)
  D1 := [[1, 0, 1, 2], [1, 0, 1, 2], [1, 0, 1, 2], [1, 0, 1, 2], [1, 0, 1, 2]]
  D2 := [[1, 0, 1, 4], [1, 0, 1, 4], [1, 0, 1, 4], [1, 0, 1, 4], [1, 0, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_138_5_2 : ColCertDiv where
  rK := ⟨138, by decide⟩
  rH := ⟨5, by decide⟩
  m := 5
  T1 := T138_5
  T2 := Q2.T138_5_2
  h1 := (2,0,2,3,2)
  h2 := (2,0,2,3,2)
  D1 := [[2, 0, 2, 3], [2, 0, 2, 3], [2, 0, 2, 3], [2, 0, 2, 3], [2, 0, 2, 3]]
  D2 := [[2, 0, 2, 2], [2, 0, 2, 2], [2, 0, 2, 2], [2, 0, 2, 2], [2, 0, 2, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_138_5_3 : ColCertDiv where
  rK := ⟨138, by decide⟩
  rH := ⟨5, by decide⟩
  m := 5
  T1 := T138_5
  T2 := Q2.T138_5_2
  h1 := (3,0,3,2,4)
  h2 := (3,0,3,2,4)
  D1 := [[3, 0, 3, 3], [3, 0, 3, 3], [3, 0, 3, 3], [3, 0, 3, 3], [3, 0, 3, 3]]
  D2 := [[3, 0, 3, 4], [3, 0, 3, 4], [3, 0, 3, 4], [3, 0, 3, 4], [3, 0, 3, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_138_5_4 : ColCertDiv where
  rK := ⟨138, by decide⟩
  rH := ⟨5, by decide⟩
  m := 5
  T1 := T138_5
  T2 := Q2.T138_5_2
  h1 := (4,0,4,1,0)
  h2 := (4,0,4,1,0)
  D1 := [[4, 0, 4, 2], [4, 0, 4, 2], [4, 0, 4, 2], [4, 0, 4, 2], [4, 0, 4, 2]]
  D2 := [[4, 0, 4, 0], [4, 0, 4, 0], [4, 0, 4, 0], [4, 0, 4, 0], [4, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_138_23_5 : ColCertDiv where
  rK := ⟨138, by decide⟩
  rH := ⟨23, by decide⟩
  m := 5
  T1 := T138_23
  T2 := Q2.T138_23_2
  h1 := (1,0,1,4,0)
  h2 := (1,0,1,4,0)
  D1 := [[1, 0, 1, 3], [1, 0, 1, 3], [1, 0, 1, 3], [1, 0, 1, 3], [1, 0, 1, 3]]
  D2 := [[1, 0, 1, 0], [1, 0, 1, 0], [1, 0, 1, 0], [1, 0, 1, 0], [1, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_138_23_10 : ColCertDiv where
  rK := ⟨138, by decide⟩
  rH := ⟨23, by decide⟩
  m := 5
  T1 := T138_23
  T2 := Q2.T138_23_2
  h1 := (2,0,2,3,4)
  h2 := (2,0,2,3,4)
  D1 := [[2, 0, 2, 0], [2, 0, 2, 0], [2, 0, 2, 0], [2, 0, 2, 0], [2, 0, 2, 0]]
  D2 := [[2, 0, 2, 4], [2, 0, 2, 4], [2, 0, 2, 4], [2, 0, 2, 4], [2, 0, 2, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_138_23_15 : ColCertDiv where
  rK := ⟨138, by decide⟩
  rH := ⟨23, by decide⟩
  m := 5
  T1 := T138_23
  T2 := Q2.T138_23_2
  h1 := (3,0,3,2,2)
  h2 := (3,0,3,2,2)
  D1 := [[3, 0, 3, 1], [3, 0, 3, 1], [3, 0, 3, 1], [3, 0, 3, 1], [3, 0, 3, 1]]
  D2 := [[3, 0, 3, 2], [3, 0, 3, 2], [3, 0, 3, 2], [3, 0, 3, 2], [3, 0, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_138_23_20 : ColCertDiv where
  rK := ⟨138, by decide⟩
  rH := ⟨23, by decide⟩
  m := 5
  T1 := T138_23
  T2 := Q2.T138_23_2
  h1 := (4,0,4,1,4)
  h2 := (4,0,4,1,4)
  D1 := [[4, 0, 4, 1], [4, 0, 4, 1], [4, 0, 4, 1], [4, 0, 4, 1], [4, 0, 4, 1]]
  D2 := [[4, 0, 4, 4], [4, 0, 4, 4], [4, 0, 4, 4], [4, 0, 4, 4], [4, 0, 4, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_138_31_10 : ColCertDiv where
  rK := ⟨138, by decide⟩
  rH := ⟨31, by decide⟩
  m := 5
  T1 := T138_31
  T2 := Q2.T138_31_2
  h1 := (2,1,4,3,0)
  h2 := (2,1,4,3,3)
  D1 := [[2, 1, 0, 2], [2, 1, 0, 1], [2, 1, 0, 0], [2, 1, 0, 4], [2, 1, 0, 3]]
  D2 := [[2, 1, 0, 3], [2, 1, 0, 2], [2, 1, 0, 1], [2, 1, 0, 0], [2, 1, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_138_31_15 : ColCertDiv where
  rK := ⟨138, by decide⟩
  rH := ⟨31, by decide⟩
  m := 5
  T1 := T138_31
  T2 := Q2.T138_31_2
  h1 := (3,4,1,4,4)
  h2 := (3,4,1,4,3)
  D1 := [[3, 4, 3, 1], [3, 4, 3, 2], [3, 4, 3, 3], [3, 4, 3, 4], [3, 4, 3, 0]]
  D2 := [[3, 4, 3, 2], [3, 4, 3, 3], [3, 4, 3, 4], [3, 4, 3, 0], [3, 4, 3, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_138_31_20 : ColCertDiv where
  rK := ⟨138, by decide⟩
  rH := ⟨31, by decide⟩
  m := 5
  T1 := T138_31
  T2 := Q2.T138_31_2
  h1 := (4,2,3,3,1)
  h2 := (4,2,3,3,2)
  D1 := [[4, 2, 3, 4], [4, 2, 3, 2], [4, 2, 3, 0], [4, 2, 3, 3], [4, 2, 3, 1]]
  D2 := [[4, 2, 3, 1], [4, 2, 3, 4], [4, 2, 3, 2], [4, 2, 3, 0], [4, 2, 3, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_138_33_5 : ColCertDiv where
  rK := ⟨138, by decide⟩
  rH := ⟨33, by decide⟩
  m := 5
  T1 := T138_33
  T2 := Q2.T138_33_2
  h1 := (0,1,2,4,0)
  h2 := (0,1,2,4,3)
  D1 := [[0, 1, 4, 3], [0, 1, 4, 2], [0, 1, 4, 1], [0, 1, 4, 0], [0, 1, 4, 4]]
  D2 := [[0, 1, 4, 0], [0, 1, 4, 4], [0, 1, 4, 3], [0, 1, 4, 2], [0, 1, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_138_33_10 : ColCertDiv where
  rK := ⟨138, by decide⟩
  rH := ⟨33, by decide⟩
  m := 5
  T1 := T138_33
  T2 := Q2.T138_33_2
  h1 := (0,2,4,3,2)
  h2 := (0,2,4,3,3)
  D1 := [[0, 2, 3, 1], [0, 2, 3, 4], [0, 2, 3, 2], [0, 2, 3, 0], [0, 2, 3, 3]]
  D2 := [[0, 2, 3, 0], [0, 2, 3, 3], [0, 2, 3, 1], [0, 2, 3, 4], [0, 2, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_138_33_15 : ColCertDiv where
  rK := ⟨138, by decide⟩
  rH := ⟨33, by decide⟩
  m := 5
  T1 := T138_33
  T2 := Q2.T138_33_2
  h1 := (0,3,1,2,1)
  h2 := (0,3,1,2,0)
  D1 := [[0, 3, 2, 4], [0, 3, 2, 1], [0, 3, 2, 3], [0, 3, 2, 0], [0, 3, 2, 2]]
  D2 := [[0, 3, 2, 0], [0, 3, 2, 2], [0, 3, 2, 4], [0, 3, 2, 1], [0, 3, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_138_33_20 : ColCertDiv where
  rK := ⟨138, by decide⟩
  rH := ⟨33, by decide⟩
  m := 5
  T1 := T138_33
  T2 := Q2.T138_33_2
  h1 := (0,4,3,1,2)
  h2 := (0,4,3,1,4)
  D1 := [[0, 4, 1, 2], [0, 4, 1, 3], [0, 4, 1, 4], [0, 4, 1, 0], [0, 4, 1, 1]]
  D2 := [[0, 4, 1, 0], [0, 4, 1, 1], [0, 4, 1, 2], [0, 4, 1, 3], [0, 4, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_138_42_5 : ColCertDiv where
  rK := ⟨138, by decide⟩
  rH := ⟨42, by decide⟩
  m := 5
  T1 := T138_42
  T2 := Q2.T138_42_2
  h1 := (1,1,3,4,4)
  h2 := (1,1,3,4,2)
  D1 := [[1, 1, 0, 1], [1, 1, 0, 0], [1, 1, 0, 4], [1, 1, 0, 3], [1, 1, 0, 2]]
  D2 := [[1, 1, 0, 0], [1, 1, 0, 4], [1, 1, 0, 3], [1, 1, 0, 2], [1, 1, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_138_42_10 : ColCertDiv where
  rK := ⟨138, by decide⟩
  rH := ⟨42, by decide⟩
  m := 5
  T1 := T138_42
  T2 := Q2.T138_42_2
  h1 := (2,2,1,4,0)
  h2 := (2,2,1,4,1)
  D1 := [[2, 2, 4, 4], [2, 2, 4, 2], [2, 2, 4, 0], [2, 2, 4, 3], [2, 2, 4, 1]]
  D2 := [[2, 2, 4, 2], [2, 2, 4, 0], [2, 2, 4, 3], [2, 2, 4, 1], [2, 2, 4, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_138_42_15 : ColCertDiv where
  rK := ⟨138, by decide⟩
  rH := ⟨42, by decide⟩
  m := 5
  T1 := T138_42
  T2 := Q2.T138_42_2
  h1 := (3,3,4,0,4)
  h2 := (3,3,4,0,3)
  D1 := [[3, 3, 2, 0], [3, 3, 2, 2], [3, 3, 2, 4], [3, 3, 2, 1], [3, 3, 2, 3]]
  D2 := [[3, 3, 2, 2], [3, 3, 2, 4], [3, 3, 2, 1], [3, 3, 2, 3], [3, 3, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_138_42_20 : ColCertDiv where
  rK := ⟨138, by decide⟩
  rH := ⟨42, by decide⟩
  m := 5
  T1 := T138_42
  T2 := Q2.T138_42_2
  h1 := (4,4,2,2,2)
  h2 := (4,4,2,2,4)
  D1 := [[4, 4, 4, 0], [4, 4, 4, 1], [4, 4, 4, 2], [4, 4, 4, 3], [4, 4, 4, 4]]
  D2 := [[4, 4, 4, 1], [4, 4, 4, 2], [4, 4, 4, 3], [4, 4, 4, 4], [4, 4, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_138_44_5 : ColCertDiv where
  rK := ⟨138, by decide⟩
  rH := ⟨44, by decide⟩
  m := 5
  T1 := T138_44
  T2 := Q2.T138_44_2
  h1 := (1,4,4,3,0)
  h2 := (1,4,4,3,0)
  D1 := [[1, 4, 1, 3], [1, 4, 1, 4], [1, 4, 1, 0], [1, 4, 1, 1], [1, 4, 1, 2]]
  D2 := [[1, 4, 1, 1], [1, 4, 1, 2], [1, 4, 1, 3], [1, 4, 1, 4], [1, 4, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_138_44_10 : ColCertDiv where
  rK := ⟨138, by decide⟩
  rH := ⟨44, by decide⟩
  m := 5
  T1 := T138_44
  T2 := Q2.T138_44_2
  h1 := (2,3,3,0,0)
  h2 := (2,3,3,0,1)
  D1 := [[2, 3, 3, 4], [2, 3, 3, 1], [2, 3, 3, 3], [2, 3, 3, 0], [2, 3, 3, 2]]
  D2 := [[2, 3, 3, 1], [2, 3, 3, 3], [2, 3, 3, 0], [2, 3, 3, 2], [2, 3, 3, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_138_44_15 : ColCertDiv where
  rK := ⟨138, by decide⟩
  rH := ⟨44, by decide⟩
  m := 5
  T1 := T138_44
  T2 := Q2.T138_44_2
  h1 := (3,2,2,1,3)
  h2 := (3,2,2,1,0)
  D1 := [[3, 2, 1, 1], [3, 2, 1, 4], [3, 2, 1, 2], [3, 2, 1, 0], [3, 2, 1, 3]]
  D2 := [[3, 2, 1, 2], [3, 2, 1, 0], [3, 2, 1, 3], [3, 2, 1, 1], [3, 2, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_138_50_5 : ColCertDiv where
  rK := ⟨138, by decide⟩
  rH := ⟨50, by decide⟩
  m := 5
  T1 := T138_50
  T2 := Q2.T138_50_2
  h1 := (1,2,0,2,2)
  h2 := (1,2,0,2,4)
  D1 := [[1, 2, 2, 3], [1, 2, 2, 1], [1, 2, 2, 4], [1, 2, 2, 2], [1, 2, 2, 0]]
  D2 := [[1, 2, 2, 0], [1, 2, 2, 3], [1, 2, 2, 1], [1, 2, 2, 4], [1, 2, 2, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_138_50_10 : ColCertDiv where
  rK := ⟨138, by decide⟩
  rH := ⟨50, by decide⟩
  m := 5
  T1 := T138_50
  T2 := Q2.T138_50_2
  h1 := (2,4,0,1,1)
  h2 := (2,4,0,1,0)
  D1 := [[2, 4, 2, 3], [2, 4, 2, 4], [2, 4, 2, 0], [2, 4, 2, 1], [2, 4, 2, 2]]
  D2 := [[2, 4, 2, 2], [2, 4, 2, 3], [2, 4, 2, 4], [2, 4, 2, 0], [2, 4, 2, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_138_50_15 : ColCertDiv where
  rK := ⟨138, by decide⟩
  rH := ⟨50, by decide⟩
  m := 5
  T1 := T138_50
  T2 := Q2.T138_50_2
  h1 := (3,1,0,2,0)
  h2 := (3,1,0,2,2)
  D1 := [[3, 1, 0, 3], [3, 1, 0, 2], [3, 1, 0, 1], [3, 1, 0, 0], [3, 1, 0, 4]]
  D2 := [[3, 1, 0, 0], [3, 1, 0, 4], [3, 1, 0, 3], [3, 1, 0, 2], [3, 1, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_138_50_20 : ColCertDiv where
  rK := ⟨138, by decide⟩
  rH := ⟨50, by decide⟩
  m := 5
  T1 := T138_50
  T2 := Q2.T138_50_2
  h1 := (4,3,0,0,4)
  h2 := (4,3,0,0,3)
  D1 := [[4, 3, 1, 3], [4, 3, 1, 0], [4, 3, 1, 2], [4, 3, 1, 4], [4, 3, 1, 1]]
  D2 := [[4, 3, 1, 2], [4, 3, 1, 4], [4, 3, 1, 1], [4, 3, 1, 3], [4, 3, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_138_84_5 : ColCertDiv where
  rK := ⟨138, by decide⟩
  rH := ⟨84, by decide⟩
  m := 5
  T1 := T138_84
  T2 := Q2.T138_84_2
  h1 := (1,0,1,0,0)
  h2 := (1,0,1,0,0)
  D1 := [[1, 0, 2, 2], [1, 0, 2, 2], [1, 0, 2, 2], [1, 0, 2, 2], [1, 0, 2, 2]]
  D2 := [[1, 0, 2, 4], [1, 0, 2, 4], [1, 0, 2, 4], [1, 0, 2, 4], [1, 0, 2, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_138_84_10 : ColCertDiv where
  rK := ⟨138, by decide⟩
  rH := ⟨84, by decide⟩
  m := 5
  T1 := T138_84
  T2 := Q2.T138_84_2
  h1 := (2,0,2,0,0)
  h2 := (2,0,2,0,0)
  D1 := [[2, 0, 4, 2], [2, 0, 4, 2], [2, 0, 4, 2], [2, 0, 4, 2], [2, 0, 4, 2]]
  D2 := [[2, 0, 4, 1], [2, 0, 4, 1], [2, 0, 4, 1], [2, 0, 4, 1], [2, 0, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_138_84_15 : ColCertDiv where
  rK := ⟨138, by decide⟩
  rH := ⟨84, by decide⟩
  m := 5
  T1 := T138_84
  T2 := Q2.T138_84_2
  h1 := (3,0,3,0,0)
  h2 := (3,0,3,0,0)
  D1 := [[3, 0, 1, 0], [3, 0, 1, 0], [3, 0, 1, 0], [3, 0, 1, 0], [3, 0, 1, 0]]
  D2 := [[3, 0, 1, 1], [3, 0, 1, 1], [3, 0, 1, 1], [3, 0, 1, 1], [3, 0, 1, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_138_84_20 : ColCertDiv where
  rK := ⟨138, by decide⟩
  rH := ⟨84, by decide⟩
  m := 5
  T1 := T138_84
  T2 := Q2.T138_84_2
  h1 := (4,0,4,0,0)
  h2 := (4,0,4,0,0)
  D1 := [[4, 0, 3, 1], [4, 0, 3, 1], [4, 0, 3, 1], [4, 0, 3, 1], [4, 0, 3, 1]]
  D2 := [[4, 0, 3, 4], [4, 0, 3, 4], [4, 0, 3, 4], [4, 0, 3, 4], [4, 0, 3, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_138_93_5 : ColCertDiv where
  rK := ⟨138, by decide⟩
  rH := ⟨93, by decide⟩
  m := 5
  T1 := T138_93
  T2 := Q2.T138_93_2
  h1 := (1,3,2,1,4)
  h2 := (1,3,2,1,4)
  D1 := [[1, 3, 0, 1], [1, 3, 0, 3], [1, 3, 0, 0], [1, 3, 0, 2], [1, 3, 0, 4]]
  D2 := [[1, 3, 0, 0], [1, 3, 0, 2], [1, 3, 0, 4], [1, 3, 0, 1], [1, 3, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_138_93_10 : ColCertDiv where
  rK := ⟨138, by decide⟩
  rH := ⟨93, by decide⟩
  m := 5
  T1 := T138_93
  T2 := Q2.T138_93_2
  h1 := (2,1,4,0,1)
  h2 := (2,1,4,0,2)
  D1 := [[2, 1, 2, 4], [2, 1, 2, 3], [2, 1, 2, 2], [2, 1, 2, 1], [2, 1, 2, 0]]
  D2 := [[2, 1, 2, 3], [2, 1, 2, 2], [2, 1, 2, 1], [2, 1, 2, 0], [2, 1, 2, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_138_93_15 : ColCertDiv where
  rK := ⟨138, by decide⟩
  rH := ⟨93, by decide⟩
  m := 5
  T1 := T138_93
  T2 := Q2.T138_93_2
  h1 := (3,4,1,2,2)
  h2 := (3,4,1,2,3)
  D1 := [[3, 4, 1, 0], [3, 4, 1, 1], [3, 4, 1, 2], [3, 4, 1, 3], [3, 4, 1, 4]]
  D2 := [[3, 4, 1, 3], [3, 4, 1, 4], [3, 4, 1, 0], [3, 4, 1, 1], [3, 4, 1, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_138_93_20 : ColCertDiv where
  rK := ⟨138, by decide⟩
  rH := ⟨93, by decide⟩
  m := 5
  T1 := T138_93
  T2 := Q2.T138_93_2
  h1 := (4,2,3,2,2)
  h2 := (4,2,3,2,4)
  D1 := [[4, 2, 2, 4], [4, 2, 2, 2], [4, 2, 2, 0], [4, 2, 2, 3], [4, 2, 2, 1]]
  D2 := [[4, 2, 2, 2], [4, 2, 2, 0], [4, 2, 2, 3], [4, 2, 2, 1], [4, 2, 2, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_138_95_25 : ColCertDiv where
  rK := ⟨138, by decide⟩
  rH := ⟨95, by decide⟩
  m := 5
  T1 := T138_95
  T2 := Q2.T138_95_2
  h1 := (0,1,2,0,0)
  h2 := (0,1,2,0,0)
  D1 := [[0, 1, 0, 3], [0, 1, 0, 2], [0, 1, 0, 1], [0, 1, 0, 0], [0, 1, 0, 4]]
  D2 := [[0, 1, 0, 2], [0, 1, 0, 1], [0, 1, 0, 0], [0, 1, 0, 4], [0, 1, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_138_95_50 : ColCertDiv where
  rK := ⟨138, by decide⟩
  rH := ⟨95, by decide⟩
  m := 5
  T1 := T138_95
  T2 := Q2.T138_95_2
  h1 := (0,2,4,0,2)
  h2 := (0,2,4,0,2)
  D1 := [[0, 2, 0, 1], [0, 2, 0, 4], [0, 2, 0, 2], [0, 2, 0, 0], [0, 2, 0, 3]]
  D2 := [[0, 2, 0, 4], [0, 2, 0, 2], [0, 2, 0, 0], [0, 2, 0, 3], [0, 2, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_138_95_75 : ColCertDiv where
  rK := ⟨138, by decide⟩
  rH := ⟨95, by decide⟩
  m := 5
  T1 := T138_95
  T2 := Q2.T138_95_2
  h1 := (0,3,1,0,1)
  h2 := (0,3,1,0,1)
  D1 := [[0, 3, 0, 4], [0, 3, 0, 1], [0, 3, 0, 3], [0, 3, 0, 0], [0, 3, 0, 2]]
  D2 := [[0, 3, 0, 1], [0, 3, 0, 3], [0, 3, 0, 0], [0, 3, 0, 2], [0, 3, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_138_95_100 : ColCertDiv where
  rK := ⟨138, by decide⟩
  rH := ⟨95, by decide⟩
  m := 5
  T1 := T138_95
  T2 := Q2.T138_95_2
  h1 := (0,4,3,0,2)
  h2 := (0,4,3,0,2)
  D1 := [[0, 4, 0, 2], [0, 4, 0, 3], [0, 4, 0, 4], [0, 4, 0, 0], [0, 4, 0, 1]]
  D2 := [[0, 4, 0, 3], [0, 4, 0, 4], [0, 4, 0, 0], [0, 4, 0, 1], [0, 4, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_138_104_5 : ColCertDiv where
  rK := ⟨138, by decide⟩
  rH := ⟨104, by decide⟩
  m := 5
  T1 := T138_104
  T2 := Q2.T138_104_2
  h1 := (1,1,3,0,0)
  h2 := (1,1,3,0,0)
  D1 := [[1, 1, 1, 1], [1, 1, 1, 0], [1, 1, 1, 4], [1, 1, 1, 3], [1, 1, 1, 2]]
  D2 := [[1, 1, 1, 2], [1, 1, 1, 1], [1, 1, 1, 0], [1, 1, 1, 4], [1, 1, 1, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_138_104_10 : ColCertDiv where
  rK := ⟨138, by decide⟩
  rH := ⟨104, by decide⟩
  m := 5
  T1 := T138_104
  T2 := Q2.T138_104_2
  h1 := (2,2,1,1,3)
  h2 := (2,2,1,1,3)
  D1 := [[2, 2, 1, 3], [2, 2, 1, 1], [2, 2, 1, 4], [2, 2, 1, 2], [2, 2, 1, 0]]
  D2 := [[2, 2, 1, 0], [2, 2, 1, 3], [2, 2, 1, 1], [2, 2, 1, 4], [2, 2, 1, 2]]
  bind1 := by decide
  bind2 := by decide

end LeanDring.P5Presentation
