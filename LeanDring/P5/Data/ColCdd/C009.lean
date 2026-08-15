/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.Twin1.ColCert
import LeanDring.P5.Data.EntryK.C030
import LeanDring.P5.Data.EntryK.C031

/-!
# Species-table cell data, stage 2 — column-data-divergent columns

Per-column certified exponent-vector data (`ColCert`/`ColCertDiv`) with kernel
`decide` bindings. Emitted; the embedded lists are what the kernel certifies.
cdd tier, chunk 8: 60 columns.
-/

-- machine-emitted data: silence style linters (generated long lines, file-level options)
set_option linter.style.longLine false

namespace LeanDring.P5Presentation

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

def colCertDiv_122_104_5 : ColCertDiv where
  rK := ⟨122, by decide⟩
  rH := ⟨104, by decide⟩
  m := 5
  T1 := T122_104
  T2 := Q2.T122_104_2
  h1 := (1,1,3,0,0)
  h2 := (1,1,3,0,0)
  D1 := [[1, 1, 0, 3], [1, 1, 0, 2], [1, 1, 0, 1], [1, 1, 0, 0], [1, 1, 0, 4]]
  D2 := [[1, 1, 0, 2], [1, 1, 0, 1], [1, 1, 0, 0], [1, 1, 0, 4], [1, 1, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_122_104_10 : ColCertDiv where
  rK := ⟨122, by decide⟩
  rH := ⟨104, by decide⟩
  m := 5
  T1 := T122_104
  T2 := Q2.T122_104_2
  h1 := (2,2,1,1,3)
  h2 := (2,2,1,1,3)
  D1 := [[2, 2, 4, 1], [2, 2, 4, 4], [2, 2, 4, 2], [2, 2, 4, 0], [2, 2, 4, 3]]
  D2 := [[2, 2, 4, 4], [2, 2, 4, 2], [2, 2, 4, 0], [2, 2, 4, 3], [2, 2, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_122_104_15 : ColCertDiv where
  rK := ⟨122, by decide⟩
  rH := ⟨104, by decide⟩
  m := 5
  T1 := T122_104
  T2 := Q2.T122_104_2
  h1 := (3,3,4,3,0)
  h2 := (3,3,4,3,0)
  D1 := [[3, 3, 2, 0], [3, 3, 2, 2], [3, 3, 2, 4], [3, 3, 2, 1], [3, 3, 2, 3]]
  D2 := [[3, 3, 2, 2], [3, 3, 2, 4], [3, 3, 2, 1], [3, 3, 2, 3], [3, 3, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_122_104_20 : ColCertDiv where
  rK := ⟨122, by decide⟩
  rH := ⟨104, by decide⟩
  m := 5
  T1 := T122_104
  T2 := Q2.T122_104_2
  h1 := (4,4,2,1,2)
  h2 := (4,4,2,1,2)
  D1 := [[4, 4, 4, 1], [4, 4, 4, 2], [4, 4, 4, 3], [4, 4, 4, 4], [4, 4, 4, 0]]
  D2 := [[4, 4, 4, 2], [4, 4, 4, 3], [4, 4, 4, 4], [4, 4, 4, 0], [4, 4, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_122_107_5 : ColCertDiv where
  rK := ⟨122, by decide⟩
  rH := ⟨107, by decide⟩
  m := 5
  T1 := T122_107
  T2 := Q2.T122_107_2
  h1 := (1,2,2,3,4)
  h2 := (1,2,2,3,4)
  D1 := [[1, 2, 2, 1], [1, 2, 2, 4], [1, 2, 2, 2], [1, 2, 2, 0], [1, 2, 2, 3]]
  D2 := [[1, 2, 2, 2], [1, 2, 2, 0], [1, 2, 2, 3], [1, 2, 2, 1], [1, 2, 2, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_122_107_10 : ColCertDiv where
  rK := ⟨122, by decide⟩
  rH := ⟨107, by decide⟩
  m := 5
  T1 := T122_107
  T2 := Q2.T122_107_2
  h1 := (2,4,4,3,0)
  h2 := (2,4,4,3,0)
  D1 := [[2, 4, 2, 0], [2, 4, 2, 1], [2, 4, 2, 2], [2, 4, 2, 3], [2, 4, 2, 4]]
  D2 := [[2, 4, 2, 2], [2, 4, 2, 3], [2, 4, 2, 4], [2, 4, 2, 0], [2, 4, 2, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_122_107_15 : ColCertDiv where
  rK := ⟨122, by decide⟩
  rH := ⟨107, by decide⟩
  m := 5
  T1 := T122_107
  T2 := Q2.T122_107_2
  h1 := (3,1,1,0,1)
  h2 := (3,1,1,0,2)
  D1 := [[3, 1, 0, 0], [3, 1, 0, 4], [3, 1, 0, 3], [3, 1, 0, 2], [3, 1, 0, 1]]
  D2 := [[3, 1, 0, 4], [3, 1, 0, 3], [3, 1, 0, 2], [3, 1, 0, 1], [3, 1, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_122_111_10 : ColCertDiv where
  rK := ⟨122, by decide⟩
  rH := ⟨111, by decide⟩
  m := 5
  T1 := T122_111
  T2 := Q2.T122_111_2
  h1 := (2,3,0,2,0)
  h2 := (2,3,0,2,1)
  D1 := [[2, 3, 3, 1], [2, 3, 3, 3], [2, 3, 3, 0], [2, 3, 3, 2], [2, 3, 3, 4]]
  D2 := [[2, 3, 3, 2], [2, 3, 3, 4], [2, 3, 3, 1], [2, 3, 3, 3], [2, 3, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_122_111_15 : ColCertDiv where
  rK := ⟨122, by decide⟩
  rH := ⟨111, by decide⟩
  m := 5
  T1 := T122_111
  T2 := Q2.T122_111_2
  h1 := (3,2,0,4,3)
  h2 := (3,2,0,4,0)
  D1 := [[3, 2, 1, 2], [3, 2, 1, 0], [3, 2, 1, 3], [3, 2, 1, 1], [3, 2, 1, 4]]
  D2 := [[3, 2, 1, 4], [3, 2, 1, 2], [3, 2, 1, 0], [3, 2, 1, 3], [3, 2, 1, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_122_111_20 : ColCertDiv where
  rK := ⟨122, by decide⟩
  rH := ⟨111, by decide⟩
  m := 5
  T1 := T122_111
  T2 := Q2.T122_111_2
  h1 := (4,1,0,0,3)
  h2 := (4,1,0,0,1)
  D1 := [[4, 1, 0, 0], [4, 1, 0, 4], [4, 1, 0, 3], [4, 1, 0, 2], [4, 1, 0, 1]]
  D2 := [[4, 1, 0, 3], [4, 1, 0, 2], [4, 1, 0, 1], [4, 1, 0, 0], [4, 1, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_123_2_1 : ColCertDiv where
  rK := ⟨123, by decide⟩
  rH := ⟨2, by decide⟩
  m := 5
  T1 := T123_2
  T2 := Q2.T123_2_2
  h1 := (1,0,4,1,0)
  h2 := (1,0,4,1,0)
  D1 := [[1, 0, 3, 4], [1, 0, 3, 4], [1, 0, 3, 4], [1, 0, 3, 4], [1, 0, 3, 4]]
  D2 := [[1, 0, 3, 1], [1, 0, 3, 1], [1, 0, 3, 1], [1, 0, 3, 1], [1, 0, 3, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_123_2_2 : ColCertDiv where
  rK := ⟨123, by decide⟩
  rH := ⟨2, by decide⟩
  m := 5
  T1 := T123_2
  T2 := Q2.T123_2_2
  h1 := (2,0,3,2,1)
  h2 := (2,0,3,2,1)
  D1 := [[2, 0, 1, 0], [2, 0, 1, 0], [2, 0, 1, 0], [2, 0, 1, 0], [2, 0, 1, 0]]
  D2 := [[2, 0, 1, 4], [2, 0, 1, 4], [2, 0, 1, 4], [2, 0, 1, 4], [2, 0, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_123_2_3 : ColCertDiv where
  rK := ⟨123, by decide⟩
  rH := ⟨2, by decide⟩
  m := 5
  T1 := T123_2
  T2 := Q2.T123_2_2
  h1 := (3,0,2,3,3)
  h2 := (3,0,2,3,3)
  D1 := [[3, 0, 4, 3], [3, 0, 4, 3], [3, 0, 4, 3], [3, 0, 4, 3], [3, 0, 4, 3]]
  D2 := [[3, 0, 4, 4], [3, 0, 4, 4], [3, 0, 4, 4], [3, 0, 4, 4], [3, 0, 4, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_123_2_4 : ColCertDiv where
  rK := ⟨123, by decide⟩
  rH := ⟨2, by decide⟩
  m := 5
  T1 := T123_2
  T2 := Q2.T123_2_2
  h1 := (4,0,1,4,1)
  h2 := (4,0,1,4,1)
  D1 := [[4, 0, 2, 3], [4, 0, 2, 3], [4, 0, 2, 3], [4, 0, 2, 3], [4, 0, 2, 3]]
  D2 := [[4, 0, 2, 1], [4, 0, 2, 1], [4, 0, 2, 1], [4, 0, 2, 1], [4, 0, 2, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_123_20_5 : ColCertDiv where
  rK := ⟨123, by decide⟩
  rH := ⟨20, by decide⟩
  m := 5
  T1 := T123_20
  T2 := Q2.T123_20_2
  h1 := (1,0,4,1,1)
  h2 := (1,0,4,1,1)
  D1 := [[1, 0, 3, 0], [1, 0, 3, 0], [1, 0, 3, 0], [1, 0, 3, 0], [1, 0, 3, 0]]
  D2 := [[1, 0, 3, 2], [1, 0, 3, 2], [1, 0, 3, 2], [1, 0, 3, 2], [1, 0, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_123_20_10 : ColCertDiv where
  rK := ⟨123, by decide⟩
  rH := ⟨20, by decide⟩
  m := 5
  T1 := T123_20
  T2 := Q2.T123_20_2
  h1 := (2,0,3,2,3)
  h2 := (2,0,3,2,3)
  D1 := [[2, 0, 1, 2], [2, 0, 1, 2], [2, 0, 1, 2], [2, 0, 1, 2], [2, 0, 1, 2]]
  D2 := [[2, 0, 1, 1], [2, 0, 1, 1], [2, 0, 1, 1], [2, 0, 1, 1], [2, 0, 1, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_123_20_15 : ColCertDiv where
  rK := ⟨123, by decide⟩
  rH := ⟨20, by decide⟩
  m := 5
  T1 := T123_20
  T2 := Q2.T123_20_2
  h1 := (3,0,2,3,1)
  h2 := (3,0,2,3,1)
  D1 := [[3, 0, 4, 1], [3, 0, 4, 1], [3, 0, 4, 1], [3, 0, 4, 1], [3, 0, 4, 1]]
  D2 := [[3, 0, 4, 2], [3, 0, 4, 2], [3, 0, 4, 2], [3, 0, 4, 2], [3, 0, 4, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_123_20_20 : ColCertDiv where
  rK := ⟨123, by decide⟩
  rH := ⟨20, by decide⟩
  m := 5
  T1 := T123_20
  T2 := Q2.T123_20_2
  h1 := (4,0,1,4,0)
  h2 := (4,0,1,4,0)
  D1 := [[4, 0, 2, 2], [4, 0, 2, 2], [4, 0, 2, 2], [4, 0, 2, 2], [4, 0, 2, 2]]
  D2 := [[4, 0, 2, 0], [4, 0, 2, 0], [4, 0, 2, 0], [4, 0, 2, 0], [4, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_123_29_5 : ColCertDiv where
  rK := ⟨123, by decide⟩
  rH := ⟨29, by decide⟩
  m := 5
  T1 := T123_29
  T2 := Q2.T123_29_2
  h1 := (1,4,1,3,3)
  h2 := (1,4,1,3,3)
  D1 := [[1, 4, 1, 0], [1, 4, 1, 1], [1, 4, 1, 2], [1, 4, 1, 3], [1, 4, 1, 4]]
  D2 := [[1, 4, 1, 3], [1, 4, 1, 4], [1, 4, 1, 0], [1, 4, 1, 1], [1, 4, 1, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_123_29_10 : ColCertDiv where
  rK := ⟨123, by decide⟩
  rH := ⟨29, by decide⟩
  m := 5
  T1 := T123_29
  T2 := Q2.T123_29_2
  h1 := (2,3,2,0,4)
  h2 := (2,3,2,0,0)
  D1 := [[2, 3, 3, 0], [2, 3, 3, 2], [2, 3, 3, 4], [2, 3, 3, 1], [2, 3, 3, 3]]
  D2 := [[2, 3, 3, 2], [2, 3, 3, 4], [2, 3, 3, 1], [2, 3, 3, 3], [2, 3, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_123_29_15 : ColCertDiv where
  rK := ⟨123, by decide⟩
  rH := ⟨29, by decide⟩
  m := 5
  T1 := T123_29
  T2 := Q2.T123_29_2
  h1 := (3,2,3,1,1)
  h2 := (3,2,3,1,3)
  D1 := [[3, 2, 1, 3], [3, 2, 1, 1], [3, 2, 1, 4], [3, 2, 1, 2], [3, 2, 1, 0]]
  D2 := [[3, 2, 1, 4], [3, 2, 1, 2], [3, 2, 1, 0], [3, 2, 1, 3], [3, 2, 1, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_123_37_5 : ColCertDiv where
  rK := ⟨123, by decide⟩
  rH := ⟨37, by decide⟩
  m := 5
  T1 := T123_37
  T2 := Q2.T123_37_2
  h1 := (1,1,2,4,3)
  h2 := (1,1,2,4,1)
  D1 := [[1, 1, 0, 1], [1, 1, 0, 0], [1, 1, 0, 4], [1, 1, 0, 3], [1, 1, 0, 2]]
  D2 := [[1, 1, 0, 0], [1, 1, 0, 4], [1, 1, 0, 3], [1, 1, 0, 2], [1, 1, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_123_37_10 : ColCertDiv where
  rK := ⟨123, by decide⟩
  rH := ⟨37, by decide⟩
  m := 5
  T1 := T123_37
  T2 := Q2.T123_37_2
  h1 := (2,2,4,4,2)
  h2 := (2,2,4,4,3)
  D1 := [[2, 2, 4, 2], [2, 2, 4, 0], [2, 2, 4, 3], [2, 2, 4, 1], [2, 2, 4, 4]]
  D2 := [[2, 2, 4, 0], [2, 2, 4, 3], [2, 2, 4, 1], [2, 2, 4, 4], [2, 2, 4, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_123_37_15 : ColCertDiv where
  rK := ⟨123, by decide⟩
  rH := ⟨37, by decide⟩
  m := 5
  T1 := T123_37
  T2 := Q2.T123_37_2
  h1 := (3,3,1,0,3)
  h2 := (3,3,1,0,2)
  D1 := [[3, 3, 2, 4], [3, 3, 2, 1], [3, 3, 2, 3], [3, 3, 2, 0], [3, 3, 2, 2]]
  D2 := [[3, 3, 2, 1], [3, 3, 2, 3], [3, 3, 2, 0], [3, 3, 2, 2], [3, 3, 2, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_123_37_20 : ColCertDiv where
  rK := ⟨123, by decide⟩
  rH := ⟨37, by decide⟩
  m := 5
  T1 := T123_37
  T2 := Q2.T123_37_2
  h1 := (4,4,3,2,2)
  h2 := (4,4,3,2,4)
  D1 := [[4, 4, 4, 3], [4, 4, 4, 4], [4, 4, 4, 0], [4, 4, 4, 1], [4, 4, 4, 2]]
  D2 := [[4, 4, 4, 4], [4, 4, 4, 0], [4, 4, 4, 1], [4, 4, 4, 2], [4, 4, 4, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_123_38_5 : ColCertDiv where
  rK := ⟨123, by decide⟩
  rH := ⟨38, by decide⟩
  m := 5
  T1 := T123_38
  T2 := Q2.T123_38_2
  h1 := (0,1,3,4,1)
  h2 := (0,1,3,4,4)
  D1 := [[0, 1, 4, 2], [0, 1, 4, 1], [0, 1, 4, 0], [0, 1, 4, 4], [0, 1, 4, 3]]
  D2 := [[0, 1, 4, 4], [0, 1, 4, 3], [0, 1, 4, 2], [0, 1, 4, 1], [0, 1, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_123_38_10 : ColCertDiv where
  rK := ⟨123, by decide⟩
  rH := ⟨38, by decide⟩
  m := 5
  T1 := T123_38
  T2 := Q2.T123_38_2
  h1 := (0,2,1,3,0)
  h2 := (0,2,1,3,1)
  D1 := [[0, 2, 3, 4], [0, 2, 3, 2], [0, 2, 3, 0], [0, 2, 3, 3], [0, 2, 3, 1]]
  D2 := [[0, 2, 3, 3], [0, 2, 3, 1], [0, 2, 3, 4], [0, 2, 3, 2], [0, 2, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_123_38_15 : ColCertDiv where
  rK := ⟨123, by decide⟩
  rH := ⟨38, by decide⟩
  m := 5
  T1 := T123_38
  T2 := Q2.T123_38_2
  h1 := (0,3,4,2,2)
  h2 := (0,3,4,2,1)
  D1 := [[0, 3, 2, 1], [0, 3, 2, 3], [0, 3, 2, 0], [0, 3, 2, 2], [0, 3, 2, 4]]
  D2 := [[0, 3, 2, 2], [0, 3, 2, 4], [0, 3, 2, 1], [0, 3, 2, 3], [0, 3, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_123_38_20 : ColCertDiv where
  rK := ⟨123, by decide⟩
  rH := ⟨38, by decide⟩
  m := 5
  T1 := T123_38
  T2 := Q2.T123_38_2
  h1 := (0,4,2,1,2)
  h2 := (0,4,2,1,4)
  D1 := [[0, 4, 1, 3], [0, 4, 1, 4], [0, 4, 1, 0], [0, 4, 1, 1], [0, 4, 1, 2]]
  D2 := [[0, 4, 1, 1], [0, 4, 1, 2], [0, 4, 1, 3], [0, 4, 1, 4], [0, 4, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_123_46_10 : ColCertDiv where
  rK := ⟨123, by decide⟩
  rH := ⟨46, by decide⟩
  m := 5
  T1 := T123_46
  T2 := Q2.T123_46_2
  h1 := (2,1,1,3,4)
  h2 := (2,1,1,3,2)
  D1 := [[2, 1, 0, 0], [2, 1, 0, 4], [2, 1, 0, 3], [2, 1, 0, 2], [2, 1, 0, 1]]
  D2 := [[2, 1, 0, 1], [2, 1, 0, 0], [2, 1, 0, 4], [2, 1, 0, 3], [2, 1, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_123_46_15 : ColCertDiv where
  rK := ⟨123, by decide⟩
  rH := ⟨46, by decide⟩
  m := 5
  T1 := T123_46
  T2 := Q2.T123_46_2
  h1 := (3,4,4,4,2)
  h2 := (3,4,4,4,1)
  D1 := [[3, 4, 3, 4], [3, 4, 3, 0], [3, 4, 3, 1], [3, 4, 3, 2], [3, 4, 3, 3]]
  D2 := [[3, 4, 3, 0], [3, 4, 3, 1], [3, 4, 3, 2], [3, 4, 3, 3], [3, 4, 3, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_123_46_20 : ColCertDiv where
  rK := ⟨123, by decide⟩
  rH := ⟨46, by decide⟩
  m := 5
  T1 := T123_46
  T2 := Q2.T123_46_2
  h1 := (4,2,2,3,1)
  h2 := (4,2,2,3,2)
  D1 := [[4, 2, 3, 1], [4, 2, 3, 4], [4, 2, 3, 2], [4, 2, 3, 0], [4, 2, 3, 3]]
  D2 := [[4, 2, 3, 3], [4, 2, 3, 1], [4, 2, 3, 4], [4, 2, 3, 2], [4, 2, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_123_50_5 : ColCertDiv where
  rK := ⟨123, by decide⟩
  rH := ⟨50, by decide⟩
  m := 5
  T1 := T123_50
  T2 := Q2.T123_50_2
  h1 := (1,2,0,2,2)
  h2 := (1,2,0,2,4)
  D1 := [[1, 2, 2, 1], [1, 2, 2, 4], [1, 2, 2, 2], [1, 2, 2, 0], [1, 2, 2, 3]]
  D2 := [[1, 2, 2, 3], [1, 2, 2, 1], [1, 2, 2, 4], [1, 2, 2, 2], [1, 2, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_123_50_10 : ColCertDiv where
  rK := ⟨123, by decide⟩
  rH := ⟨50, by decide⟩
  m := 5
  T1 := T123_50
  T2 := Q2.T123_50_2
  h1 := (2,4,0,1,1)
  h2 := (2,4,0,1,0)
  D1 := [[2, 4, 2, 0], [2, 4, 2, 1], [2, 4, 2, 2], [2, 4, 2, 3], [2, 4, 2, 4]]
  D2 := [[2, 4, 2, 4], [2, 4, 2, 0], [2, 4, 2, 1], [2, 4, 2, 2], [2, 4, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_123_50_15 : ColCertDiv where
  rK := ⟨123, by decide⟩
  rH := ⟨50, by decide⟩
  m := 5
  T1 := T123_50
  T2 := Q2.T123_50_2
  h1 := (3,1,0,2,0)
  h2 := (3,1,0,2,2)
  D1 := [[3, 1, 0, 0], [3, 1, 0, 4], [3, 1, 0, 3], [3, 1, 0, 2], [3, 1, 0, 1]]
  D2 := [[3, 1, 0, 2], [3, 1, 0, 1], [3, 1, 0, 0], [3, 1, 0, 4], [3, 1, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_123_50_20 : ColCertDiv where
  rK := ⟨123, by decide⟩
  rH := ⟨50, by decide⟩
  m := 5
  T1 := T123_50
  T2 := Q2.T123_50_2
  h1 := (4,3,0,0,4)
  h2 := (4,3,0,0,3)
  D1 := [[4, 3, 1, 1], [4, 3, 1, 3], [4, 3, 1, 0], [4, 3, 1, 2], [4, 3, 1, 4]]
  D2 := [[4, 3, 1, 0], [4, 3, 1, 2], [4, 3, 1, 4], [4, 3, 1, 1], [4, 3, 1, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_123_81_5 : ColCertDiv where
  rK := ⟨123, by decide⟩
  rH := ⟨81, by decide⟩
  m := 5
  T1 := T123_81
  T2 := Q2.T123_81_2
  h1 := (1,0,4,0,0)
  h2 := (1,0,4,0,0)
  D1 := [[1, 0, 2, 0], [1, 0, 2, 0], [1, 0, 2, 0], [1, 0, 2, 0], [1, 0, 2, 0]]
  D2 := [[1, 0, 2, 2], [1, 0, 2, 2], [1, 0, 2, 2], [1, 0, 2, 2], [1, 0, 2, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_123_81_10 : ColCertDiv where
  rK := ⟨123, by decide⟩
  rH := ⟨81, by decide⟩
  m := 5
  T1 := T123_81
  T2 := Q2.T123_81_2
  h1 := (2,0,3,0,0)
  h2 := (2,0,3,0,0)
  D1 := [[2, 0, 4, 3], [2, 0, 4, 3], [2, 0, 4, 3], [2, 0, 4, 3], [2, 0, 4, 3]]
  D2 := [[2, 0, 4, 2], [2, 0, 4, 2], [2, 0, 4, 2], [2, 0, 4, 2], [2, 0, 4, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_123_81_15 : ColCertDiv where
  rK := ⟨123, by decide⟩
  rH := ⟨81, by decide⟩
  m := 5
  T1 := T123_81
  T2 := Q2.T123_81_2
  h1 := (3,0,2,0,0)
  h2 := (3,0,2,0,0)
  D1 := [[3, 0, 1, 4], [3, 0, 1, 4], [3, 0, 1, 4], [3, 0, 1, 4], [3, 0, 1, 4]]
  D2 := [[3, 0, 1, 0], [3, 0, 1, 0], [3, 0, 1, 0], [3, 0, 1, 0], [3, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_123_81_20 : ColCertDiv where
  rK := ⟨123, by decide⟩
  rH := ⟨81, by decide⟩
  m := 5
  T1 := T123_81
  T2 := Q2.T123_81_2
  h1 := (4,0,1,0,0)
  h2 := (4,0,1,0,0)
  D1 := [[4, 0, 3, 3], [4, 0, 3, 3], [4, 0, 3, 3], [4, 0, 3, 3], [4, 0, 3, 3]]
  D2 := [[4, 0, 3, 1], [4, 0, 3, 1], [4, 0, 3, 1], [4, 0, 3, 1], [4, 0, 3, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_123_91_5 : ColCertDiv where
  rK := ⟨123, by decide⟩
  rH := ⟨91, by decide⟩
  m := 5
  T1 := T123_91
  T2 := Q2.T123_91_2
  h1 := (1,4,1,4,4)
  h2 := (1,4,1,4,4)
  D1 := [[1, 4, 2, 0], [1, 4, 2, 1], [1, 4, 2, 2], [1, 4, 2, 3], [1, 4, 2, 4]]
  D2 := [[1, 4, 2, 3], [1, 4, 2, 4], [1, 4, 2, 0], [1, 4, 2, 1], [1, 4, 2, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_123_91_10 : ColCertDiv where
  rK := ⟨123, by decide⟩
  rH := ⟨91, by decide⟩
  m := 5
  T1 := T123_91
  T2 := Q2.T123_91_2
  h1 := (2,3,2,2,2)
  h2 := (2,3,2,2,3)
  D1 := [[2, 3, 0, 4], [2, 3, 0, 1], [2, 3, 0, 3], [2, 3, 0, 0], [2, 3, 0, 2]]
  D2 := [[2, 3, 0, 1], [2, 3, 0, 3], [2, 3, 0, 0], [2, 3, 0, 2], [2, 3, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_123_91_15 : ColCertDiv where
  rK := ⟨123, by decide⟩
  rH := ⟨91, by decide⟩
  m := 5
  T1 := T123_91
  T2 := Q2.T123_91_2
  h1 := (3,2,3,4,2)
  h2 := (3,2,3,4,4)
  D1 := [[3, 2, 4, 0], [3, 2, 4, 3], [3, 2, 4, 1], [3, 2, 4, 4], [3, 2, 4, 2]]
  D2 := [[3, 2, 4, 1], [3, 2, 4, 4], [3, 2, 4, 2], [3, 2, 4, 0], [3, 2, 4, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_123_99_5 : ColCertDiv where
  rK := ⟨123, by decide⟩
  rH := ⟨99, by decide⟩
  m := 5
  T1 := T123_99
  T2 := Q2.T123_99_2
  h1 := (1,1,2,0,0)
  h2 := (1,1,2,0,0)
  D1 := [[1, 1, 1, 2], [1, 1, 1, 1], [1, 1, 1, 0], [1, 1, 1, 4], [1, 1, 1, 3]]
  D2 := [[1, 1, 1, 3], [1, 1, 1, 2], [1, 1, 1, 1], [1, 1, 1, 0], [1, 1, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_123_99_10 : ColCertDiv where
  rK := ⟨123, by decide⟩
  rH := ⟨99, by decide⟩
  m := 5
  T1 := T123_99
  T2 := Q2.T123_99_2
  h1 := (2,2,4,1,2)
  h2 := (2,2,4,1,2)
  D1 := [[2, 2, 1, 3], [2, 2, 1, 1], [2, 2, 1, 4], [2, 2, 1, 2], [2, 2, 1, 0]]
  D2 := [[2, 2, 1, 0], [2, 2, 1, 3], [2, 2, 1, 1], [2, 2, 1, 4], [2, 2, 1, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_123_99_15 : ColCertDiv where
  rK := ⟨123, by decide⟩
  rH := ⟨99, by decide⟩
  m := 5
  T1 := T123_99
  T2 := Q2.T123_99_2
  h1 := (3,3,1,3,2)
  h2 := (3,3,1,3,2)
  D1 := [[3, 3, 0, 4], [3, 3, 0, 1], [3, 3, 0, 3], [3, 3, 0, 0], [3, 3, 0, 2]]
  D2 := [[3, 3, 0, 2], [3, 3, 0, 4], [3, 3, 0, 1], [3, 3, 0, 3], [3, 3, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_123_99_20 : ColCertDiv where
  rK := ⟨123, by decide⟩
  rH := ⟨99, by decide⟩
  m := 5
  T1 := T123_99
  T2 := Q2.T123_99_2
  h1 := (4,4,3,1,1)
  h2 := (4,4,3,1,1)
  D1 := [[4, 4, 3, 1], [4, 4, 3, 2], [4, 4, 3, 3], [4, 4, 3, 4], [4, 4, 3, 0]]
  D2 := [[4, 4, 3, 0], [4, 4, 3, 1], [4, 4, 3, 2], [4, 4, 3, 3], [4, 4, 3, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_123_100_25 : ColCertDiv where
  rK := ⟨123, by decide⟩
  rH := ⟨100, by decide⟩
  m := 5
  T1 := T123_100
  T2 := Q2.T123_100_2
  h1 := (0,1,3,0,0)
  h2 := (0,1,3,0,0)
  D1 := [[0, 1, 0, 1], [0, 1, 0, 0], [0, 1, 0, 4], [0, 1, 0, 3], [0, 1, 0, 2]]
  D2 := [[0, 1, 0, 0], [0, 1, 0, 4], [0, 1, 0, 3], [0, 1, 0, 2], [0, 1, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_123_100_50 : ColCertDiv where
  rK := ⟨123, by decide⟩
  rH := ⟨100, by decide⟩
  m := 5
  T1 := T123_100
  T2 := Q2.T123_100_2
  h1 := (0,2,1,0,3)
  h2 := (0,2,1,0,3)
  D1 := [[0, 2, 0, 2], [0, 2, 0, 0], [0, 2, 0, 3], [0, 2, 0, 1], [0, 2, 0, 4]]
  D2 := [[0, 2, 0, 0], [0, 2, 0, 3], [0, 2, 0, 1], [0, 2, 0, 4], [0, 2, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_123_100_75 : ColCertDiv where
  rK := ⟨123, by decide⟩
  rH := ⟨100, by decide⟩
  m := 5
  T1 := T123_100
  T2 := Q2.T123_100_2
  h1 := (0,3,4,0,4)
  h2 := (0,3,4,0,4)
  D1 := [[0, 3, 0, 3], [0, 3, 0, 0], [0, 3, 0, 2], [0, 3, 0, 4], [0, 3, 0, 1]]
  D2 := [[0, 3, 0, 0], [0, 3, 0, 2], [0, 3, 0, 4], [0, 3, 0, 1], [0, 3, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_123_100_100 : ColCertDiv where
  rK := ⟨123, by decide⟩
  rH := ⟨100, by decide⟩
  m := 5
  T1 := T123_100
  T2 := Q2.T123_100_2
  h1 := (0,4,2,0,3)
  h2 := (0,4,2,0,3)
  D1 := [[0, 4, 0, 4], [0, 4, 0, 0], [0, 4, 0, 1], [0, 4, 0, 2], [0, 4, 0, 3]]
  D2 := [[0, 4, 0, 0], [0, 4, 0, 1], [0, 4, 0, 2], [0, 4, 0, 3], [0, 4, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_123_108_5 : ColCertDiv where
  rK := ⟨123, by decide⟩
  rH := ⟨108, by decide⟩
  m := 5
  T1 := T123_108
  T2 := Q2.T123_108_2
  h1 := (1,3,3,1,0)
  h2 := (1,3,3,1,0)
  D1 := [[1, 3, 0, 1], [1, 3, 0, 3], [1, 3, 0, 0], [1, 3, 0, 2], [1, 3, 0, 4]]
  D2 := [[1, 3, 0, 0], [1, 3, 0, 2], [1, 3, 0, 4], [1, 3, 0, 1], [1, 3, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_123_108_10 : ColCertDiv where
  rK := ⟨123, by decide⟩
  rH := ⟨108, by decide⟩
  m := 5
  T1 := T123_108
  T2 := Q2.T123_108_2
  h1 := (2,1,1,0,1)
  h2 := (2,1,1,0,2)
  D1 := [[2, 1, 2, 3], [2, 1, 2, 2], [2, 1, 2, 1], [2, 1, 2, 0], [2, 1, 2, 4]]
  D2 := [[2, 1, 2, 2], [2, 1, 2, 1], [2, 1, 2, 0], [2, 1, 2, 4], [2, 1, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_123_108_15 : ColCertDiv where
  rK := ⟨123, by decide⟩
  rH := ⟨108, by decide⟩
  m := 5
  T1 := T123_108
  T2 := Q2.T123_108_2
  h1 := (3,4,4,2,4)
  h2 := (3,4,4,2,0)
  D1 := [[3, 4, 1, 2], [3, 4, 1, 3], [3, 4, 1, 4], [3, 4, 1, 0], [3, 4, 1, 1]]
  D2 := [[3, 4, 1, 0], [3, 4, 1, 1], [3, 4, 1, 2], [3, 4, 1, 3], [3, 4, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_123_108_20 : ColCertDiv where
  rK := ⟨123, by decide⟩
  rH := ⟨108, by decide⟩
  m := 5
  T1 := T123_108
  T2 := Q2.T123_108_2
  h1 := (4,2,2,2,4)
  h2 := (4,2,2,2,1)
  D1 := [[4, 2, 2, 3], [4, 2, 2, 1], [4, 2, 2, 4], [4, 2, 2, 2], [4, 2, 2, 0]]
  D2 := [[4, 2, 2, 1], [4, 2, 2, 4], [4, 2, 2, 2], [4, 2, 2, 0], [4, 2, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_123_112_15 : ColCertDiv where
  rK := ⟨123, by decide⟩
  rH := ⟨112, by decide⟩
  m := 5
  T1 := T123_112
  T2 := Q2.T123_112_2
  h1 := (3,1,0,0,1)
  h2 := (3,1,0,0,2)
  D1 := [[3, 1, 3, 2], [3, 1, 3, 1], [3, 1, 3, 0], [3, 1, 3, 4], [3, 1, 3, 3]]
  D2 := [[3, 1, 3, 3], [3, 1, 3, 2], [3, 1, 3, 1], [3, 1, 3, 0], [3, 1, 3, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_123_112_20 : ColCertDiv where
  rK := ⟨123, by decide⟩
  rH := ⟨112, by decide⟩
  m := 5
  T1 := T123_112
  T2 := Q2.T123_112_2
  h1 := (4,3,0,4,4)
  h2 := (4,3,0,4,0)
  D1 := [[4, 3, 0, 0], [4, 3, 0, 2], [4, 3, 0, 4], [4, 3, 0, 1], [4, 3, 0, 3]]
  D2 := [[4, 3, 0, 1], [4, 3, 0, 3], [4, 3, 0, 0], [4, 3, 0, 2], [4, 3, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_124_2_1 : ColCertDiv where
  rK := ⟨124, by decide⟩
  rH := ⟨2, by decide⟩
  m := 5
  T1 := T124_2
  T2 := Q2.T124_2_2
  h1 := (1,0,4,1,0)
  h2 := (1,0,4,1,0)
  D1 := [[1, 0, 0, 3], [1, 0, 0, 3], [1, 0, 0, 3], [1, 0, 0, 3], [1, 0, 0, 3]]
  D2 := [[1, 0, 0, 1], [1, 0, 0, 1], [1, 0, 0, 1], [1, 0, 0, 1], [1, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_124_2_2 : ColCertDiv where
  rK := ⟨124, by decide⟩
  rH := ⟨2, by decide⟩
  m := 5
  T1 := T124_2
  T2 := Q2.T124_2_2
  h1 := (2,0,3,2,1)
  h2 := (2,0,3,2,1)
  D1 := [[2, 0, 0, 1], [2, 0, 0, 1], [2, 0, 0, 1], [2, 0, 0, 1], [2, 0, 0, 1]]
  D2 := [[2, 0, 0, 2], [2, 0, 0, 2], [2, 0, 0, 2], [2, 0, 0, 2], [2, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_124_2_3 : ColCertDiv where
  rK := ⟨124, by decide⟩
  rH := ⟨2, by decide⟩
  m := 5
  T1 := T124_2
  T2 := Q2.T124_2_2
  h1 := (3,0,2,3,3)
  h2 := (3,0,2,3,3)
  D1 := [[3, 0, 0, 4], [3, 0, 0, 4], [3, 0, 0, 4], [3, 0, 0, 4], [3, 0, 0, 4]]
  D2 := [[3, 0, 0, 3], [3, 0, 0, 3], [3, 0, 0, 3], [3, 0, 0, 3], [3, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

end LeanDring.P5Presentation
