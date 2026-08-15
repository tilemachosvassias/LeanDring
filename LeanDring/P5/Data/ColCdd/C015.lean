/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.Twin1.ColCert
import LeanDring.P5.Data.EntryK.C035

/-!
# Species-table cell data, stage 2 — column-data-divergent columns

Per-column certified exponent-vector data (`ColCert`/`ColCertDiv`) with kernel
`decide` bindings. Emitted; the embedded lists are what the kernel certifies.
cdd tier, chunk 14: 60 columns.
-/

-- machine-emitted data: silence style linters (generated long lines, file-level options)
set_option linter.style.longLine false

namespace LeanDring.P5Presentation

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

def colCertDiv_132_38_10 : ColCertDiv where
  rK := ⟨132, by decide⟩
  rH := ⟨38, by decide⟩
  m := 5
  T1 := T132_38
  T2 := Q2.T132_38_2
  h1 := (0,2,1,3,0)
  h2 := (0,2,1,3,1)
  D1 := [[0, 2, 3, 1], [0, 2, 3, 4], [0, 2, 3, 2], [0, 2, 3, 0], [0, 2, 3, 3]]
  D2 := [[0, 2, 3, 0], [0, 2, 3, 3], [0, 2, 3, 1], [0, 2, 3, 4], [0, 2, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_132_38_15 : ColCertDiv where
  rK := ⟨132, by decide⟩
  rH := ⟨38, by decide⟩
  m := 5
  T1 := T132_38
  T2 := Q2.T132_38_2
  h1 := (0,3,4,2,2)
  h2 := (0,3,4,2,1)
  D1 := [[0, 3, 2, 4], [0, 3, 2, 1], [0, 3, 2, 3], [0, 3, 2, 0], [0, 3, 2, 2]]
  D2 := [[0, 3, 2, 0], [0, 3, 2, 2], [0, 3, 2, 4], [0, 3, 2, 1], [0, 3, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_132_38_20 : ColCertDiv where
  rK := ⟨132, by decide⟩
  rH := ⟨38, by decide⟩
  m := 5
  T1 := T132_38
  T2 := Q2.T132_38_2
  h1 := (0,4,2,1,2)
  h2 := (0,4,2,1,4)
  D1 := [[0, 4, 1, 2], [0, 4, 1, 3], [0, 4, 1, 4], [0, 4, 1, 0], [0, 4, 1, 1]]
  D2 := [[0, 4, 1, 0], [0, 4, 1, 1], [0, 4, 1, 2], [0, 4, 1, 3], [0, 4, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_132_47_5 : ColCertDiv where
  rK := ⟨132, by decide⟩
  rH := ⟨47, by decide⟩
  m := 5
  T1 := T132_47
  T2 := Q2.T132_47_2
  h1 := (1,1,1,4,2)
  h2 := (1,1,1,4,0)
  D1 := [[1, 1, 4, 3], [1, 1, 4, 2], [1, 1, 4, 1], [1, 1, 4, 0], [1, 1, 4, 4]]
  D2 := [[1, 1, 4, 4], [1, 1, 4, 3], [1, 1, 4, 2], [1, 1, 4, 1], [1, 1, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_132_47_10 : ColCertDiv where
  rK := ⟨132, by decide⟩
  rH := ⟨47, by decide⟩
  m := 5
  T1 := T132_47
  T2 := Q2.T132_47_2
  h1 := (2,2,2,4,4)
  h2 := (2,2,2,4,0)
  D1 := [[2, 2, 2, 1], [2, 2, 2, 4], [2, 2, 2, 2], [2, 2, 2, 0], [2, 2, 2, 3]]
  D2 := [[2, 2, 2, 3], [2, 2, 2, 1], [2, 2, 2, 4], [2, 2, 2, 2], [2, 2, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_132_47_15 : ColCertDiv where
  rK := ⟨132, by decide⟩
  rH := ⟨47, by decide⟩
  m := 5
  T1 := T132_47
  T2 := Q2.T132_47_2
  h1 := (3,3,3,0,2)
  h2 := (3,3,3,0,1)
  D1 := [[3, 3, 4, 0], [3, 3, 4, 2], [3, 3, 4, 4], [3, 3, 4, 1], [3, 3, 4, 3]]
  D2 := [[3, 3, 4, 3], [3, 3, 4, 0], [3, 3, 4, 2], [3, 3, 4, 4], [3, 3, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_132_47_20 : ColCertDiv where
  rK := ⟨132, by decide⟩
  rH := ⟨47, by decide⟩
  m := 5
  T1 := T132_47
  T2 := Q2.T132_47_2
  h1 := (4,4,4,2,2)
  h2 := (4,4,4,2,4)
  D1 := [[4, 4, 0, 1], [4, 4, 0, 2], [4, 4, 0, 3], [4, 4, 0, 4], [4, 4, 0, 0]]
  D2 := [[4, 4, 0, 0], [4, 4, 0, 1], [4, 4, 0, 2], [4, 4, 0, 3], [4, 4, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_132_49_10 : ColCertDiv where
  rK := ⟨132, by decide⟩
  rH := ⟨49, by decide⟩
  m := 5
  T1 := T132_49
  T2 := Q2.T132_49_2
  h1 := (2,3,0,0,2)
  h2 := (2,3,0,0,3)
  D1 := [[2, 3, 1, 1], [2, 3, 1, 3], [2, 3, 1, 0], [2, 3, 1, 2], [2, 3, 1, 4]]
  D2 := [[2, 3, 1, 2], [2, 3, 1, 4], [2, 3, 1, 1], [2, 3, 1, 3], [2, 3, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_132_49_15 : ColCertDiv where
  rK := ⟨132, by decide⟩
  rH := ⟨49, by decide⟩
  m := 5
  T1 := T132_49
  T2 := Q2.T132_49_2
  h1 := (3,2,0,1,2)
  h2 := (3,2,0,1,4)
  D1 := [[3, 2, 3, 0], [3, 2, 3, 3], [3, 2, 3, 1], [3, 2, 3, 4], [3, 2, 3, 2]]
  D2 := [[3, 2, 3, 2], [3, 2, 3, 0], [3, 2, 3, 3], [3, 2, 3, 1], [3, 2, 3, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_132_49_20 : ColCertDiv where
  rK := ⟨132, by decide⟩
  rH := ⟨49, by decide⟩
  m := 5
  T1 := T132_49
  T2 := Q2.T132_49_2
  h1 := (4,1,0,1,3)
  h2 := (4,1,0,1,1)
  D1 := [[4, 1, 1, 3], [4, 1, 1, 2], [4, 1, 1, 1], [4, 1, 1, 0], [4, 1, 1, 4]]
  D2 := [[4, 1, 1, 1], [4, 1, 1, 0], [4, 1, 1, 4], [4, 1, 1, 3], [4, 1, 1, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_132_83_5 : ColCertDiv where
  rK := ⟨132, by decide⟩
  rH := ⟨83, by decide⟩
  m := 5
  T1 := T132_83
  T2 := Q2.T132_83_2
  h1 := (1,0,3,0,0)
  h2 := (1,0,3,0,0)
  D1 := [[1, 0, 1, 2], [1, 0, 1, 2], [1, 0, 1, 2], [1, 0, 1, 2], [1, 0, 1, 2]]
  D2 := [[1, 0, 1, 1], [1, 0, 1, 1], [1, 0, 1, 1], [1, 0, 1, 1], [1, 0, 1, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_132_83_10 : ColCertDiv where
  rK := ⟨132, by decide⟩
  rH := ⟨83, by decide⟩
  m := 5
  T1 := T132_83
  T2 := Q2.T132_83_2
  h1 := (2,0,1,0,0)
  h2 := (2,0,1,0,0)
  D1 := [[2, 0, 2, 3], [2, 0, 2, 3], [2, 0, 2, 3], [2, 0, 2, 3], [2, 0, 2, 3]]
  D2 := [[2, 0, 2, 1], [2, 0, 2, 1], [2, 0, 2, 1], [2, 0, 2, 1], [2, 0, 2, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_132_83_15 : ColCertDiv where
  rK := ⟨132, by decide⟩
  rH := ⟨83, by decide⟩
  m := 5
  T1 := T132_83
  T2 := Q2.T132_83_2
  h1 := (3,0,4,0,0)
  h2 := (3,0,4,0,0)
  D1 := [[3, 0, 3, 3], [3, 0, 3, 3], [3, 0, 3, 3], [3, 0, 3, 3], [3, 0, 3, 3]]
  D2 := [[3, 0, 3, 0], [3, 0, 3, 0], [3, 0, 3, 0], [3, 0, 3, 0], [3, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_132_83_20 : ColCertDiv where
  rK := ⟨132, by decide⟩
  rH := ⟨83, by decide⟩
  m := 5
  T1 := T132_83
  T2 := Q2.T132_83_2
  h1 := (4,0,2,0,0)
  h2 := (4,0,2,0,0)
  D1 := [[4, 0, 4, 2], [4, 0, 4, 2], [4, 0, 4, 2], [4, 0, 4, 2], [4, 0, 4, 2]]
  D2 := [[4, 0, 4, 3], [4, 0, 4, 3], [4, 0, 4, 3], [4, 0, 4, 3], [4, 0, 4, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_132_93_5 : ColCertDiv where
  rK := ⟨132, by decide⟩
  rH := ⟨93, by decide⟩
  m := 5
  T1 := T132_93
  T2 := Q2.T132_93_2
  h1 := (1,3,2,1,4)
  h2 := (1,3,2,1,4)
  D1 := [[1, 3, 4, 0], [1, 3, 4, 2], [1, 3, 4, 4], [1, 3, 4, 1], [1, 3, 4, 3]]
  D2 := [[1, 3, 4, 1], [1, 3, 4, 3], [1, 3, 4, 0], [1, 3, 4, 2], [1, 3, 4, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_132_93_10 : ColCertDiv where
  rK := ⟨132, by decide⟩
  rH := ⟨93, by decide⟩
  m := 5
  T1 := T132_93
  T2 := Q2.T132_93_2
  h1 := (2,1,4,0,1)
  h2 := (2,1,4,0,2)
  D1 := [[2, 1, 0, 4], [2, 1, 0, 3], [2, 1, 0, 2], [2, 1, 0, 1], [2, 1, 0, 0]]
  D2 := [[2, 1, 0, 2], [2, 1, 0, 1], [2, 1, 0, 0], [2, 1, 0, 4], [2, 1, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_132_93_15 : ColCertDiv where
  rK := ⟨132, by decide⟩
  rH := ⟨93, by decide⟩
  m := 5
  T1 := T132_93
  T2 := Q2.T132_93_2
  h1 := (3,4,1,2,2)
  h2 := (3,4,1,2,3)
  D1 := [[3, 4, 3, 3], [3, 4, 3, 4], [3, 4, 3, 0], [3, 4, 3, 1], [3, 4, 3, 2]]
  D2 := [[3, 4, 3, 2], [3, 4, 3, 3], [3, 4, 3, 4], [3, 4, 3, 0], [3, 4, 3, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_132_93_20 : ColCertDiv where
  rK := ⟨132, by decide⟩
  rH := ⟨93, by decide⟩
  m := 5
  T1 := T132_93
  T2 := Q2.T132_93_2
  h1 := (4,2,3,2,2)
  h2 := (4,2,3,2,4)
  D1 := [[4, 2, 3, 2], [4, 2, 3, 0], [4, 2, 3, 3], [4, 2, 3, 1], [4, 2, 3, 4]]
  D2 := [[4, 2, 3, 3], [4, 2, 3, 1], [4, 2, 3, 4], [4, 2, 3, 2], [4, 2, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_132_97_5 : ColCertDiv where
  rK := ⟨132, by decide⟩
  rH := ⟨97, by decide⟩
  m := 5
  T1 := T132_97
  T2 := Q2.T132_97_2
  h1 := (1,2,4,3,0)
  h2 := (1,2,4,3,0)
  D1 := [[1, 2, 2, 2], [1, 2, 2, 0], [1, 2, 2, 3], [1, 2, 2, 1], [1, 2, 2, 4]]
  D2 := [[1, 2, 2, 4], [1, 2, 2, 2], [1, 2, 2, 0], [1, 2, 2, 3], [1, 2, 2, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_132_97_10 : ColCertDiv where
  rK := ⟨132, by decide⟩
  rH := ⟨97, by decide⟩
  m := 5
  T1 := T132_97
  T2 := Q2.T132_97_2
  h1 := (2,4,3,3,1)
  h2 := (2,4,3,3,1)
  D1 := [[2, 4, 2, 0], [2, 4, 2, 1], [2, 4, 2, 2], [2, 4, 2, 3], [2, 4, 2, 4]]
  D2 := [[2, 4, 2, 4], [2, 4, 2, 0], [2, 4, 2, 1], [2, 4, 2, 2], [2, 4, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_132_97_15 : ColCertDiv where
  rK := ⟨132, by decide⟩
  rH := ⟨97, by decide⟩
  m := 5
  T1 := T132_97
  T2 := Q2.T132_97_2
  h1 := (3,1,2,0,1)
  h2 := (3,1,2,0,2)
  D1 := [[3, 1, 0, 2], [3, 1, 0, 1], [3, 1, 0, 0], [3, 1, 0, 4], [3, 1, 0, 3]]
  D2 := [[3, 1, 0, 4], [3, 1, 0, 3], [3, 1, 0, 2], [3, 1, 0, 1], [3, 1, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_132_97_20 : ColCertDiv where
  rK := ⟨132, by decide⟩
  rH := ⟨97, by decide⟩
  m := 5
  T1 := T132_97
  T2 := Q2.T132_97_2
  h1 := (4,3,1,4,0)
  h2 := (4,3,1,4,1)
  D1 := [[4, 3, 1, 3], [4, 3, 1, 0], [4, 3, 1, 2], [4, 3, 1, 4], [4, 3, 1, 1]]
  D2 := [[4, 3, 1, 2], [4, 3, 1, 4], [4, 3, 1, 1], [4, 3, 1, 3], [4, 3, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_132_100_25 : ColCertDiv where
  rK := ⟨132, by decide⟩
  rH := ⟨100, by decide⟩
  m := 5
  T1 := T132_100
  T2 := Q2.T132_100_2
  h1 := (0,1,3,0,0)
  h2 := (0,1,3,0,0)
  D1 := [[0, 1, 0, 2], [0, 1, 0, 1], [0, 1, 0, 0], [0, 1, 0, 4], [0, 1, 0, 3]]
  D2 := [[0, 1, 0, 1], [0, 1, 0, 0], [0, 1, 0, 4], [0, 1, 0, 3], [0, 1, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_132_100_50 : ColCertDiv where
  rK := ⟨132, by decide⟩
  rH := ⟨100, by decide⟩
  m := 5
  T1 := T132_100
  T2 := Q2.T132_100_2
  h1 := (0,2,1,0,3)
  h2 := (0,2,1,0,3)
  D1 := [[0, 2, 0, 4], [0, 2, 0, 2], [0, 2, 0, 0], [0, 2, 0, 3], [0, 2, 0, 1]]
  D2 := [[0, 2, 0, 2], [0, 2, 0, 0], [0, 2, 0, 3], [0, 2, 0, 1], [0, 2, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_132_100_75 : ColCertDiv where
  rK := ⟨132, by decide⟩
  rH := ⟨100, by decide⟩
  m := 5
  T1 := T132_100
  T2 := Q2.T132_100_2
  h1 := (0,3,4,0,4)
  h2 := (0,3,4,0,4)
  D1 := [[0, 3, 0, 1], [0, 3, 0, 3], [0, 3, 0, 0], [0, 3, 0, 2], [0, 3, 0, 4]]
  D2 := [[0, 3, 0, 3], [0, 3, 0, 0], [0, 3, 0, 2], [0, 3, 0, 4], [0, 3, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_132_100_100 : ColCertDiv where
  rK := ⟨132, by decide⟩
  rH := ⟨100, by decide⟩
  m := 5
  T1 := T132_100
  T2 := Q2.T132_100_2
  h1 := (0,4,2,0,3)
  h2 := (0,4,2,0,3)
  D1 := [[0, 4, 0, 3], [0, 4, 0, 4], [0, 4, 0, 0], [0, 4, 0, 1], [0, 4, 0, 2]]
  D2 := [[0, 4, 0, 4], [0, 4, 0, 0], [0, 4, 0, 1], [0, 4, 0, 2], [0, 4, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_132_109_5 : ColCertDiv where
  rK := ⟨132, by decide⟩
  rH := ⟨109, by decide⟩
  m := 5
  T1 := T132_109
  T2 := Q2.T132_109_2
  h1 := (1,1,1,0,0)
  h2 := (1,1,1,0,0)
  D1 := [[1, 1, 0, 0], [1, 1, 0, 4], [1, 1, 0, 3], [1, 1, 0, 2], [1, 1, 0, 1]]
  D2 := [[1, 1, 0, 3], [1, 1, 0, 2], [1, 1, 0, 1], [1, 1, 0, 0], [1, 1, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_132_109_10 : ColCertDiv where
  rK := ⟨132, by decide⟩
  rH := ⟨109, by decide⟩
  m := 5
  T1 := T132_109
  T2 := Q2.T132_109_2
  h1 := (2,2,2,1,1)
  h2 := (2,2,2,1,1)
  D1 := [[2, 2, 4, 4], [2, 2, 4, 2], [2, 2, 4, 0], [2, 2, 4, 3], [2, 2, 4, 1]]
  D2 := [[2, 2, 4, 0], [2, 2, 4, 3], [2, 2, 4, 1], [2, 2, 4, 4], [2, 2, 4, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_132_109_15 : ColCertDiv where
  rK := ⟨132, by decide⟩
  rH := ⟨109, by decide⟩
  m := 5
  T1 := T132_109
  T2 := Q2.T132_109_2
  h1 := (3,3,3,3,4)
  h2 := (3,3,3,3,4)
  D1 := [[3, 3, 2, 3], [3, 3, 2, 0], [3, 3, 2, 2], [3, 3, 2, 4], [3, 3, 2, 1]]
  D2 := [[3, 3, 2, 2], [3, 3, 2, 4], [3, 3, 2, 1], [3, 3, 2, 3], [3, 3, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_132_109_20 : ColCertDiv where
  rK := ⟨132, by decide⟩
  rH := ⟨109, by decide⟩
  m := 5
  T1 := T132_109
  T2 := Q2.T132_109_2
  h1 := (4,4,4,1,0)
  h2 := (4,4,4,1,0)
  D1 := [[4, 4, 4, 3], [4, 4, 4, 4], [4, 4, 4, 0], [4, 4, 4, 1], [4, 4, 4, 2]]
  D2 := [[4, 4, 4, 0], [4, 4, 4, 1], [4, 4, 4, 2], [4, 4, 4, 3], [4, 4, 4, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_132_111_10 : ColCertDiv where
  rK := ⟨132, by decide⟩
  rH := ⟨111, by decide⟩
  m := 5
  T1 := T132_111
  T2 := Q2.T132_111_2
  h1 := (2,3,0,2,0)
  h2 := (2,3,0,2,1)
  D1 := [[2, 3, 3, 0], [2, 3, 3, 2], [2, 3, 3, 4], [2, 3, 3, 1], [2, 3, 3, 3]]
  D2 := [[2, 3, 3, 1], [2, 3, 3, 3], [2, 3, 3, 0], [2, 3, 3, 2], [2, 3, 3, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_132_111_15 : ColCertDiv where
  rK := ⟨132, by decide⟩
  rH := ⟨111, by decide⟩
  m := 5
  T1 := T132_111
  T2 := Q2.T132_111_2
  h1 := (3,2,0,4,3)
  h2 := (3,2,0,4,0)
  D1 := [[3, 2, 1, 2], [3, 2, 1, 0], [3, 2, 1, 3], [3, 2, 1, 1], [3, 2, 1, 4]]
  D2 := [[3, 2, 1, 4], [3, 2, 1, 2], [3, 2, 1, 0], [3, 2, 1, 3], [3, 2, 1, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_132_111_20 : ColCertDiv where
  rK := ⟨132, by decide⟩
  rH := ⟨111, by decide⟩
  m := 5
  T1 := T132_111
  T2 := Q2.T132_111_2
  h1 := (4,1,0,0,3)
  h2 := (4,1,0,0,1)
  D1 := [[4, 1, 0, 2], [4, 1, 0, 1], [4, 1, 0, 0], [4, 1, 0, 4], [4, 1, 0, 3]]
  D2 := [[4, 1, 0, 0], [4, 1, 0, 4], [4, 1, 0, 3], [4, 1, 0, 2], [4, 1, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_133_32_5 : ColCertDiv where
  rK := ⟨133, by decide⟩
  rH := ⟨32, by decide⟩
  m := 5
  T1 := T133_32
  T2 := Q2.T133_32_2
  h1 := (1,1,4,4,0)
  h2 := (1,1,4,4,3)
  D1 := [[1, 1, 0, 0], [1, 1, 0, 4], [1, 1, 0, 3], [1, 1, 0, 2], [1, 1, 0, 1]]
  D2 := [[1, 1, 0, 3], [1, 1, 0, 2], [1, 1, 0, 1], [1, 1, 0, 0], [1, 1, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_133_32_10 : ColCertDiv where
  rK := ⟨133, by decide⟩
  rH := ⟨32, by decide⟩
  m := 5
  T1 := T133_32
  T2 := Q2.T133_32_2
  h1 := (2,2,3,4,3)
  h2 := (2,2,3,4,4)
  D1 := [[2, 2, 4, 4], [2, 2, 4, 2], [2, 2, 4, 0], [2, 2, 4, 3], [2, 2, 4, 1]]
  D2 := [[2, 2, 4, 0], [2, 2, 4, 3], [2, 2, 4, 1], [2, 2, 4, 4], [2, 2, 4, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_133_32_15 : ColCertDiv where
  rK := ⟨133, by decide⟩
  rH := ⟨32, by decide⟩
  m := 5
  T1 := T133_32
  T2 := Q2.T133_32_2
  h1 := (3,3,2,0,0)
  h2 := (3,3,2,0,4)
  D1 := [[3, 3, 2, 3], [3, 3, 2, 0], [3, 3, 2, 2], [3, 3, 2, 4], [3, 3, 2, 1]]
  D2 := [[3, 3, 2, 2], [3, 3, 2, 4], [3, 3, 2, 1], [3, 3, 2, 3], [3, 3, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_133_32_20 : ColCertDiv where
  rK := ⟨133, by decide⟩
  rH := ⟨32, by decide⟩
  m := 5
  T1 := T133_32
  T2 := Q2.T133_32_2
  h1 := (4,4,1,2,2)
  h2 := (4,4,1,2,4)
  D1 := [[4, 4, 4, 3], [4, 4, 4, 4], [4, 4, 4, 0], [4, 4, 4, 1], [4, 4, 4, 2]]
  D2 := [[4, 4, 4, 0], [4, 4, 4, 1], [4, 4, 4, 2], [4, 4, 4, 3], [4, 4, 4, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_133_36_5 : ColCertDiv where
  rK := ⟨133, by decide⟩
  rH := ⟨36, by decide⟩
  m := 5
  T1 := T133_36
  T2 := Q2.T133_36_2
  h1 := (1,3,1,0,1)
  h2 := (1,3,1,0,2)
  D1 := [[1, 3, 4, 1], [1, 3, 4, 3], [1, 3, 4, 0], [1, 3, 4, 2], [1, 3, 4, 4]]
  D2 := [[1, 3, 4, 2], [1, 3, 4, 4], [1, 3, 4, 1], [1, 3, 4, 3], [1, 3, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_133_36_10 : ColCertDiv where
  rK := ⟨133, by decide⟩
  rH := ⟨36, by decide⟩
  m := 5
  T1 := T133_36
  T2 := Q2.T133_36_2
  h1 := (2,1,2,3,1)
  h2 := (2,1,2,3,4)
  D1 := [[2, 1, 0, 1], [2, 1, 0, 0], [2, 1, 0, 4], [2, 1, 0, 3], [2, 1, 0, 2]]
  D2 := [[2, 1, 0, 4], [2, 1, 0, 3], [2, 1, 0, 2], [2, 1, 0, 1], [2, 1, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_133_36_15 : ColCertDiv where
  rK := ⟨133, by decide⟩
  rH := ⟨36, by decide⟩
  m := 5
  T1 := T133_36
  T2 := Q2.T133_36_2
  h1 := (3,4,3,4,1)
  h2 := (3,4,3,4,0)
  D1 := [[3, 4, 3, 1], [3, 4, 3, 2], [3, 4, 3, 3], [3, 4, 3, 4], [3, 4, 3, 0]]
  D2 := [[3, 4, 3, 0], [3, 4, 3, 1], [3, 4, 3, 2], [3, 4, 3, 3], [3, 4, 3, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_133_36_20 : ColCertDiv where
  rK := ⟨133, by decide⟩
  rH := ⟨36, by decide⟩
  m := 5
  T1 := T133_36
  T2 := Q2.T133_36_2
  h1 := (4,2,4,3,1)
  h2 := (4,2,4,3,2)
  D1 := [[4, 2, 3, 1], [4, 2, 3, 4], [4, 2, 3, 2], [4, 2, 3, 0], [4, 2, 3, 3]]
  D2 := [[4, 2, 3, 2], [4, 2, 3, 0], [4, 2, 3, 3], [4, 2, 3, 1], [4, 2, 3, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_133_39_10 : ColCertDiv where
  rK := ⟨133, by decide⟩
  rH := ⟨39, by decide⟩
  m := 5
  T1 := T133_39
  T2 := Q2.T133_39_2
  h1 := (2,3,4,0,1)
  h2 := (2,3,4,0,2)
  D1 := [[2, 3, 3, 2], [2, 3, 3, 4], [2, 3, 3, 1], [2, 3, 3, 3], [2, 3, 3, 0]]
  D2 := [[2, 3, 3, 3], [2, 3, 3, 0], [2, 3, 3, 2], [2, 3, 3, 4], [2, 3, 3, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_133_39_15 : ColCertDiv where
  rK := ⟨133, by decide⟩
  rH := ⟨39, by decide⟩
  m := 5
  T1 := T133_39
  T2 := Q2.T133_39_2
  h1 := (3,2,1,1,0)
  h2 := (3,2,1,1,2)
  D1 := [[3, 2, 1, 0], [3, 2, 1, 3], [3, 2, 1, 1], [3, 2, 1, 4], [3, 2, 1, 2]]
  D2 := [[3, 2, 1, 2], [3, 2, 1, 0], [3, 2, 1, 3], [3, 2, 1, 1], [3, 2, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_133_39_20 : ColCertDiv where
  rK := ⟨133, by decide⟩
  rH := ⟨39, by decide⟩
  m := 5
  T1 := T133_39
  T2 := Q2.T133_39_2
  h1 := (4,1,3,1,3)
  h2 := (4,1,3,1,1)
  D1 := [[4, 1, 0, 1], [4, 1, 0, 0], [4, 1, 0, 4], [4, 1, 0, 3], [4, 1, 0, 2]]
  D2 := [[4, 1, 0, 4], [4, 1, 0, 3], [4, 1, 0, 2], [4, 1, 0, 1], [4, 1, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_133_43_5 : ColCertDiv where
  rK := ⟨133, by decide⟩
  rH := ⟨43, by decide⟩
  m := 5
  T1 := T133_43
  T2 := Q2.T133_43_2
  h1 := (0,1,1,4,4)
  h2 := (0,1,1,4,2)
  D1 := [[0, 1, 4, 0], [0, 1, 4, 4], [0, 1, 4, 3], [0, 1, 4, 2], [0, 1, 4, 1]]
  D2 := [[0, 1, 4, 3], [0, 1, 4, 2], [0, 1, 4, 1], [0, 1, 4, 0], [0, 1, 4, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_133_43_10 : ColCertDiv where
  rK := ⟨133, by decide⟩
  rH := ⟨43, by decide⟩
  m := 5
  T1 := T133_43
  T2 := Q2.T133_43_2
  h1 := (0,2,2,3,4)
  h2 := (0,2,2,3,0)
  D1 := [[0, 2, 3, 0], [0, 2, 3, 3], [0, 2, 3, 1], [0, 2, 3, 4], [0, 2, 3, 2]]
  D2 := [[0, 2, 3, 1], [0, 2, 3, 4], [0, 2, 3, 2], [0, 2, 3, 0], [0, 2, 3, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_133_43_15 : ColCertDiv where
  rK := ⟨133, by decide⟩
  rH := ⟨43, by decide⟩
  m := 5
  T1 := T133_43
  T2 := Q2.T133_43_2
  h1 := (0,3,3,2,0)
  h2 := (0,3,3,2,4)
  D1 := [[0, 3, 2, 0], [0, 3, 2, 2], [0, 3, 2, 4], [0, 3, 2, 1], [0, 3, 2, 3]]
  D2 := [[0, 3, 2, 4], [0, 3, 2, 1], [0, 3, 2, 3], [0, 3, 2, 0], [0, 3, 2, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_133_43_20 : ColCertDiv where
  rK := ⟨133, by decide⟩
  rH := ⟨43, by decide⟩
  m := 5
  T1 := T133_43
  T2 := Q2.T133_43_2
  h1 := (0,4,4,1,2)
  h2 := (0,4,4,1,4)
  D1 := [[0, 4, 1, 0], [0, 4, 1, 1], [0, 4, 1, 2], [0, 4, 1, 3], [0, 4, 1, 4]]
  D2 := [[0, 4, 1, 2], [0, 4, 1, 3], [0, 4, 1, 4], [0, 4, 1, 0], [0, 4, 1, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_133_50_5 : ColCertDiv where
  rK := ⟨133, by decide⟩
  rH := ⟨50, by decide⟩
  m := 5
  T1 := T133_50
  T2 := Q2.T133_50_2
  h1 := (1,2,0,2,2)
  h2 := (1,2,0,2,4)
  D1 := [[1, 2, 2, 0], [1, 2, 2, 3], [1, 2, 2, 1], [1, 2, 2, 4], [1, 2, 2, 2]]
  D2 := [[1, 2, 2, 2], [1, 2, 2, 0], [1, 2, 2, 3], [1, 2, 2, 1], [1, 2, 2, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_133_50_10 : ColCertDiv where
  rK := ⟨133, by decide⟩
  rH := ⟨50, by decide⟩
  m := 5
  T1 := T133_50
  T2 := Q2.T133_50_2
  h1 := (2,4,0,1,1)
  h2 := (2,4,0,1,0)
  D1 := [[2, 4, 2, 1], [2, 4, 2, 2], [2, 4, 2, 3], [2, 4, 2, 4], [2, 4, 2, 0]]
  D2 := [[2, 4, 2, 0], [2, 4, 2, 1], [2, 4, 2, 2], [2, 4, 2, 3], [2, 4, 2, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_133_50_15 : ColCertDiv where
  rK := ⟨133, by decide⟩
  rH := ⟨50, by decide⟩
  m := 5
  T1 := T133_50
  T2 := Q2.T133_50_2
  h1 := (3,1,0,2,0)
  h2 := (3,1,0,2,2)
  D1 := [[3, 1, 0, 1], [3, 1, 0, 0], [3, 1, 0, 4], [3, 1, 0, 3], [3, 1, 0, 2]]
  D2 := [[3, 1, 0, 3], [3, 1, 0, 2], [3, 1, 0, 1], [3, 1, 0, 0], [3, 1, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_133_50_20 : ColCertDiv where
  rK := ⟨133, by decide⟩
  rH := ⟨50, by decide⟩
  m := 5
  T1 := T133_50
  T2 := Q2.T133_50_2
  h1 := (4,3,0,0,4)
  h2 := (4,3,0,0,3)
  D1 := [[4, 3, 1, 0], [4, 3, 1, 2], [4, 3, 1, 4], [4, 3, 1, 1], [4, 3, 1, 3]]
  D2 := [[4, 3, 1, 4], [4, 3, 1, 1], [4, 3, 1, 3], [4, 3, 1, 0], [4, 3, 1, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_133_98_10 : ColCertDiv where
  rK := ⟨133, by decide⟩
  rH := ⟨98, by decide⟩
  m := 5
  T1 := T133_98
  T2 := Q2.T133_98_2
  h1 := (2,1,2,0,1)
  h2 := (2,1,2,0,2)
  D1 := [[2, 1, 2, 2], [2, 1, 2, 1], [2, 1, 2, 0], [2, 1, 2, 4], [2, 1, 2, 3]]
  D2 := [[2, 1, 2, 3], [2, 1, 2, 2], [2, 1, 2, 1], [2, 1, 2, 0], [2, 1, 2, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_133_98_15 : ColCertDiv where
  rK := ⟨133, by decide⟩
  rH := ⟨98, by decide⟩
  m := 5
  T1 := T133_98
  T2 := Q2.T133_98_2
  h1 := (3,4,3,2,0)
  h2 := (3,4,3,2,1)
  D1 := [[3, 4, 1, 1], [3, 4, 1, 2], [3, 4, 1, 3], [3, 4, 1, 4], [3, 4, 1, 0]]
  D2 := [[3, 4, 1, 2], [3, 4, 1, 3], [3, 4, 1, 4], [3, 4, 1, 0], [3, 4, 1, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_133_98_20 : ColCertDiv where
  rK := ⟨133, by decide⟩
  rH := ⟨98, by decide⟩
  m := 5
  T1 := T133_98
  T2 := Q2.T133_98_2
  h1 := (4,2,4,2,0)
  h2 := (4,2,4,2,2)
  D1 := [[4, 2, 2, 4], [4, 2, 2, 2], [4, 2, 2, 0], [4, 2, 2, 3], [4, 2, 2, 1]]
  D2 := [[4, 2, 2, 1], [4, 2, 2, 4], [4, 2, 2, 2], [4, 2, 2, 0], [4, 2, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_133_101_10 : ColCertDiv where
  rK := ⟨133, by decide⟩
  rH := ⟨101, by decide⟩
  m := 5
  T1 := T133_101
  T2 := Q2.T133_101_2
  h1 := (2,3,4,2,4)
  h2 := (2,3,4,2,0)
  D1 := [[2, 3, 0, 1], [2, 3, 0, 3], [2, 3, 0, 0], [2, 3, 0, 2], [2, 3, 0, 4]]
  D2 := [[2, 3, 0, 2], [2, 3, 0, 4], [2, 3, 0, 1], [2, 3, 0, 3], [2, 3, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_133_101_15 : ColCertDiv where
  rK := ⟨133, by decide⟩
  rH := ⟨101, by decide⟩
  m := 5
  T1 := T133_101
  T2 := Q2.T133_101_2
  h1 := (3,2,1,4,1)
  h2 := (3,2,1,4,3)
  D1 := [[3, 2, 4, 2], [3, 2, 4, 0], [3, 2, 4, 3], [3, 2, 4, 1], [3, 2, 4, 4]]
  D2 := [[3, 2, 4, 4], [3, 2, 4, 2], [3, 2, 4, 0], [3, 2, 4, 3], [3, 2, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_133_101_20 : ColCertDiv where
  rK := ⟨133, by decide⟩
  rH := ⟨101, by decide⟩
  m := 5
  T1 := T133_101
  T2 := Q2.T133_101_2
  h1 := (4,1,3,0,3)
  h2 := (4,1,3,0,1)
  D1 := [[4, 1, 4, 0], [4, 1, 4, 4], [4, 1, 4, 3], [4, 1, 4, 2], [4, 1, 4, 1]]
  D2 := [[4, 1, 4, 3], [4, 1, 4, 2], [4, 1, 4, 1], [4, 1, 4, 0], [4, 1, 4, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_133_112_15 : ColCertDiv where
  rK := ⟨133, by decide⟩
  rH := ⟨112, by decide⟩
  m := 5
  T1 := T133_112
  T2 := Q2.T133_112_2
  h1 := (3,1,0,0,1)
  h2 := (3,1,0,0,2)
  D1 := [[3, 1, 3, 3], [3, 1, 3, 2], [3, 1, 3, 1], [3, 1, 3, 0], [3, 1, 3, 4]]
  D2 := [[3, 1, 3, 4], [3, 1, 3, 3], [3, 1, 3, 2], [3, 1, 3, 1], [3, 1, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_133_112_20 : ColCertDiv where
  rK := ⟨133, by decide⟩
  rH := ⟨112, by decide⟩
  m := 5
  T1 := T133_112
  T2 := Q2.T133_112_2
  h1 := (4,3,0,4,4)
  h2 := (4,3,0,4,0)
  D1 := [[4, 3, 0, 4], [4, 3, 0, 1], [4, 3, 0, 3], [4, 3, 0, 0], [4, 3, 0, 2]]
  D2 := [[4, 3, 0, 0], [4, 3, 0, 2], [4, 3, 0, 4], [4, 3, 0, 1], [4, 3, 0, 3]]
  bind1 := by decide
  bind2 := by decide

end LeanDring.P5Presentation
