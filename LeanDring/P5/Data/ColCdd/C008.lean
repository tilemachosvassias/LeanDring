/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.Twin1.ColCert
import LeanDring.P5.Data.EntryK.C029
import LeanDring.P5.Data.EntryK.C030

/-!
# Species-table cell data, stage 2 — column-data-divergent columns

Per-column certified exponent-vector data (`ColCert`/`ColCertDiv`) with kernel
`decide` bindings. Emitted; the embedded lists are what the kernel certifies.
cdd tier, chunk 7: 60 columns.
-/

-- machine-emitted data: silence style linters (generated long lines, file-level options)
set_option linter.style.longLine false

namespace LeanDring.P5Presentation

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

def colCertDiv_121_32_5 : ColCertDiv where
  rK := ⟨121, by decide⟩
  rH := ⟨32, by decide⟩
  m := 5
  T1 := T121_32
  T2 := Q2.T121_32_2
  h1 := (1,1,4,4,0)
  h2 := (1,1,4,4,3)
  D1 := [[1, 1, 3, 3], [1, 1, 3, 2], [1, 1, 3, 1], [1, 1, 3, 0], [1, 1, 3, 4]]
  D2 := [[1, 1, 3, 1], [1, 1, 3, 0], [1, 1, 3, 4], [1, 1, 3, 3], [1, 1, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_121_32_10 : ColCertDiv where
  rK := ⟨121, by decide⟩
  rH := ⟨32, by decide⟩
  m := 5
  T1 := T121_32
  T2 := Q2.T121_32_2
  h1 := (2,2,3,4,3)
  h2 := (2,2,3,4,4)
  D1 := [[2, 2, 0, 3], [2, 2, 0, 1], [2, 2, 0, 4], [2, 2, 0, 2], [2, 2, 0, 0]]
  D2 := [[2, 2, 0, 4], [2, 2, 0, 2], [2, 2, 0, 0], [2, 2, 0, 3], [2, 2, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_121_32_15 : ColCertDiv where
  rK := ⟨121, by decide⟩
  rH := ⟨32, by decide⟩
  m := 5
  T1 := T121_32
  T2 := Q2.T121_32_2
  h1 := (3,3,2,0,0)
  h2 := (3,3,2,0,4)
  D1 := [[3, 3, 1, 1], [3, 3, 1, 3], [3, 3, 1, 0], [3, 3, 1, 2], [3, 3, 1, 4]]
  D2 := [[3, 3, 1, 0], [3, 3, 1, 2], [3, 3, 1, 4], [3, 3, 1, 1], [3, 3, 1, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_121_32_20 : ColCertDiv where
  rK := ⟨121, by decide⟩
  rH := ⟨32, by decide⟩
  m := 5
  T1 := T121_32
  T2 := Q2.T121_32_2
  h1 := (4,4,1,2,2)
  h2 := (4,4,1,2,4)
  D1 := [[4, 4, 1, 3], [4, 4, 1, 4], [4, 4, 1, 0], [4, 4, 1, 1], [4, 4, 1, 2]]
  D2 := [[4, 4, 1, 0], [4, 4, 1, 1], [4, 4, 1, 2], [4, 4, 1, 3], [4, 4, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_121_35_5 : ColCertDiv where
  rK := ⟨121, by decide⟩
  rH := ⟨35, by decide⟩
  m := 5
  T1 := T121_35
  T2 := Q2.T121_35_2
  h1 := (1,2,4,2,0)
  h2 := (1,2,4,2,2)
  D1 := [[1, 2, 0, 2], [1, 2, 0, 0], [1, 2, 0, 3], [1, 2, 0, 1], [1, 2, 0, 4]]
  D2 := [[1, 2, 0, 4], [1, 2, 0, 2], [1, 2, 0, 0], [1, 2, 0, 3], [1, 2, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_121_35_10 : ColCertDiv where
  rK := ⟨121, by decide⟩
  rH := ⟨35, by decide⟩
  m := 5
  T1 := T121_35
  T2 := Q2.T121_35_2
  h1 := (2,4,3,1,0)
  h2 := (2,4,3,1,4)
  D1 := [[2, 4, 3, 4], [2, 4, 3, 0], [2, 4, 3, 1], [2, 4, 3, 2], [2, 4, 3, 3]]
  D2 := [[2, 4, 3, 3], [2, 4, 3, 4], [2, 4, 3, 0], [2, 4, 3, 1], [2, 4, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_121_35_15 : ColCertDiv where
  rK := ⟨121, by decide⟩
  rH := ⟨35, by decide⟩
  m := 5
  T1 := T121_35
  T2 := Q2.T121_35_2
  h1 := (3,1,2,2,3)
  h2 := (3,1,2,2,0)
  D1 := [[3, 1, 4, 4], [3, 1, 4, 3], [3, 1, 4, 2], [3, 1, 4, 1], [3, 1, 4, 0]]
  D2 := [[3, 1, 4, 1], [3, 1, 4, 0], [3, 1, 4, 4], [3, 1, 4, 3], [3, 1, 4, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_121_35_20 : ColCertDiv where
  rK := ⟨121, by decide⟩
  rH := ⟨35, by decide⟩
  m := 5
  T1 := T121_35
  T2 := Q2.T121_35_2
  h1 := (4,3,1,0,4)
  h2 := (4,3,1,0,3)
  D1 := [[4, 3, 3, 2], [4, 3, 3, 4], [4, 3, 3, 1], [4, 3, 3, 3], [4, 3, 3, 0]]
  D2 := [[4, 3, 3, 1], [4, 3, 3, 3], [4, 3, 3, 0], [4, 3, 3, 2], [4, 3, 3, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_121_41_5 : ColCertDiv where
  rK := ⟨121, by decide⟩
  rH := ⟨41, by decide⟩
  m := 5
  T1 := T121_41
  T2 := Q2.T121_41_2
  h1 := (1,3,4,0,0)
  h2 := (1,3,4,0,1)
  D1 := [[1, 3, 2, 1], [1, 3, 2, 3], [1, 3, 2, 0], [1, 3, 2, 2], [1, 3, 2, 4]]
  D2 := [[1, 3, 2, 2], [1, 3, 2, 4], [1, 3, 2, 1], [1, 3, 2, 3], [1, 3, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_121_41_10 : ColCertDiv where
  rK := ⟨121, by decide⟩
  rH := ⟨41, by decide⟩
  m := 5
  T1 := T121_41
  T2 := Q2.T121_41_2
  h1 := (2,1,3,3,3)
  h2 := (2,1,3,3,1)
  D1 := [[2, 1, 1, 1], [2, 1, 1, 0], [2, 1, 1, 4], [2, 1, 1, 3], [2, 1, 1, 2]]
  D2 := [[2, 1, 1, 4], [2, 1, 1, 3], [2, 1, 1, 2], [2, 1, 1, 1], [2, 1, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_121_41_15 : ColCertDiv where
  rK := ⟨121, by decide⟩
  rH := ⟨41, by decide⟩
  m := 5
  T1 := T121_41
  T2 := Q2.T121_41_2
  h1 := (3,4,2,4,0)
  h2 := (3,4,2,4,4)
  D1 := [[3, 4, 2, 1], [3, 4, 2, 2], [3, 4, 2, 3], [3, 4, 2, 4], [3, 4, 2, 0]]
  D2 := [[3, 4, 2, 0], [3, 4, 2, 1], [3, 4, 2, 2], [3, 4, 2, 3], [3, 4, 2, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_121_41_20 : ColCertDiv where
  rK := ⟨121, by decide⟩
  rH := ⟨41, by decide⟩
  m := 5
  T1 := T121_41
  T2 := Q2.T121_41_2
  h1 := (4,2,1,3,1)
  h2 := (4,2,1,3,2)
  D1 := [[4, 2, 0, 1], [4, 2, 0, 4], [4, 2, 0, 2], [4, 2, 0, 0], [4, 2, 0, 3]]
  D2 := [[4, 2, 0, 2], [4, 2, 0, 0], [4, 2, 0, 3], [4, 2, 0, 1], [4, 2, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_121_44_10 : ColCertDiv where
  rK := ⟨121, by decide⟩
  rH := ⟨44, by decide⟩
  m := 5
  T1 := T121_44
  T2 := Q2.T121_44_2
  h1 := (2,3,3,0,0)
  h2 := (2,3,3,0,1)
  D1 := [[2, 3, 4, 2], [2, 3, 4, 4], [2, 3, 4, 1], [2, 3, 4, 3], [2, 3, 4, 0]]
  D2 := [[2, 3, 4, 3], [2, 3, 4, 0], [2, 3, 4, 2], [2, 3, 4, 4], [2, 3, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_121_44_15 : ColCertDiv where
  rK := ⟨121, by decide⟩
  rH := ⟨44, by decide⟩
  m := 5
  T1 := T121_44
  T2 := Q2.T121_44_2
  h1 := (3,2,2,1,3)
  h2 := (3,2,2,1,0)
  D1 := [[3, 2, 0, 4], [3, 2, 0, 2], [3, 2, 0, 0], [3, 2, 0, 3], [3, 2, 0, 1]]
  D2 := [[3, 2, 0, 1], [3, 2, 0, 4], [3, 2, 0, 2], [3, 2, 0, 0], [3, 2, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_121_44_20 : ColCertDiv where
  rK := ⟨121, by decide⟩
  rH := ⟨44, by decide⟩
  m := 5
  T1 := T121_44
  T2 := Q2.T121_44_2
  h1 := (4,1,1,1,3)
  h2 := (4,1,1,1,1)
  D1 := [[4, 1, 2, 0], [4, 1, 2, 4], [4, 1, 2, 3], [4, 1, 2, 2], [4, 1, 2, 1]]
  D2 := [[4, 1, 2, 3], [4, 1, 2, 2], [4, 1, 2, 1], [4, 1, 2, 0], [4, 1, 2, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_121_48_5 : ColCertDiv where
  rK := ⟨121, by decide⟩
  rH := ⟨48, by decide⟩
  m := 5
  T1 := T121_48
  T2 := Q2.T121_48_2
  h1 := (0,1,0,4,3)
  h2 := (0,1,0,4,1)
  D1 := [[0, 1, 4, 4], [0, 1, 4, 3], [0, 1, 4, 2], [0, 1, 4, 1], [0, 1, 4, 0]]
  D2 := [[0, 1, 4, 2], [0, 1, 4, 1], [0, 1, 4, 0], [0, 1, 4, 4], [0, 1, 4, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_121_48_10 : ColCertDiv where
  rK := ⟨121, by decide⟩
  rH := ⟨48, by decide⟩
  m := 5
  T1 := T121_48
  T2 := Q2.T121_48_2
  h1 := (0,2,0,3,1)
  h2 := (0,2,0,3,2)
  D1 := [[0, 2, 3, 3], [0, 2, 3, 1], [0, 2, 3, 4], [0, 2, 3, 2], [0, 2, 3, 0]]
  D2 := [[0, 2, 3, 4], [0, 2, 3, 2], [0, 2, 3, 0], [0, 2, 3, 3], [0, 2, 3, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_121_48_15 : ColCertDiv where
  rK := ⟨121, by decide⟩
  rH := ⟨48, by decide⟩
  m := 5
  T1 := T121_48
  T2 := Q2.T121_48_2
  h1 := (0,3,0,2,4)
  h2 := (0,3,0,2,3)
  D1 := [[0, 3, 2, 2], [0, 3, 2, 4], [0, 3, 2, 1], [0, 3, 2, 3], [0, 3, 2, 0]]
  D2 := [[0, 3, 2, 1], [0, 3, 2, 3], [0, 3, 2, 0], [0, 3, 2, 2], [0, 3, 2, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_121_48_20 : ColCertDiv where
  rK := ⟨121, by decide⟩
  rH := ⟨48, by decide⟩
  m := 5
  T1 := T121_48
  T2 := Q2.T121_48_2
  h1 := (0,4,0,1,2)
  h2 := (0,4,0,1,4)
  D1 := [[0, 4, 1, 1], [0, 4, 1, 2], [0, 4, 1, 3], [0, 4, 1, 4], [0, 4, 1, 0]]
  D2 := [[0, 4, 1, 3], [0, 4, 1, 4], [0, 4, 1, 0], [0, 4, 1, 1], [0, 4, 1, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_121_97_15 : ColCertDiv where
  rK := ⟨121, by decide⟩
  rH := ⟨97, by decide⟩
  m := 5
  T1 := T121_97
  T2 := Q2.T121_97_2
  h1 := (3,1,2,0,1)
  h2 := (3,1,2,0,2)
  D1 := [[3, 1, 2, 3], [3, 1, 2, 2], [3, 1, 2, 1], [3, 1, 2, 0], [3, 1, 2, 4]]
  D2 := [[3, 1, 2, 4], [3, 1, 2, 3], [3, 1, 2, 2], [3, 1, 2, 1], [3, 1, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_121_97_20 : ColCertDiv where
  rK := ⟨121, by decide⟩
  rH := ⟨97, by decide⟩
  m := 5
  T1 := T121_97
  T2 := Q2.T121_97_2
  h1 := (4,3,1,4,0)
  h2 := (4,3,1,4,1)
  D1 := [[4, 3, 2, 2], [4, 3, 2, 4], [4, 3, 2, 1], [4, 3, 2, 3], [4, 3, 2, 0]]
  D2 := [[4, 3, 2, 3], [4, 3, 2, 0], [4, 3, 2, 2], [4, 3, 2, 4], [4, 3, 2, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_121_103_10 : ColCertDiv where
  rK := ⟨121, by decide⟩
  rH := ⟨103, by decide⟩
  m := 5
  T1 := T121_103
  T2 := Q2.T121_103_2
  h1 := (2,1,3,0,1)
  h2 := (2,1,3,0,2)
  D1 := [[2, 1, 3, 0], [2, 1, 3, 4], [2, 1, 3, 3], [2, 1, 3, 2], [2, 1, 3, 1]]
  D2 := [[2, 1, 3, 1], [2, 1, 3, 0], [2, 1, 3, 4], [2, 1, 3, 3], [2, 1, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_121_103_15 : ColCertDiv where
  rK := ⟨121, by decide⟩
  rH := ⟨103, by decide⟩
  m := 5
  T1 := T121_103
  T2 := Q2.T121_103_2
  h1 := (3,4,2,2,1)
  h2 := (3,4,2,2,2)
  D1 := [[3, 4, 0, 3], [3, 4, 0, 4], [3, 4, 0, 0], [3, 4, 0, 1], [3, 4, 0, 2]]
  D2 := [[3, 4, 0, 4], [3, 4, 0, 0], [3, 4, 0, 1], [3, 4, 0, 2], [3, 4, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_121_103_20 : ColCertDiv where
  rK := ⟨121, by decide⟩
  rH := ⟨103, by decide⟩
  m := 5
  T1 := T121_103
  T2 := Q2.T121_103_2
  h1 := (4,2,1,2,1)
  h2 := (4,2,1,2,3)
  D1 := [[4, 2, 4, 0], [4, 2, 4, 3], [4, 2, 4, 1], [4, 2, 4, 4], [4, 2, 4, 2]]
  D2 := [[4, 2, 4, 2], [4, 2, 4, 0], [4, 2, 4, 3], [4, 2, 4, 1], [4, 2, 4, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_121_106_10 : ColCertDiv where
  rK := ⟨121, by decide⟩
  rH := ⟨106, by decide⟩
  m := 5
  T1 := T121_106
  T2 := Q2.T121_106_2
  h1 := (2,3,3,2,3)
  h2 := (2,3,3,2,4)
  D1 := [[2, 3, 1, 1], [2, 3, 1, 3], [2, 3, 1, 0], [2, 3, 1, 2], [2, 3, 1, 4]]
  D2 := [[2, 3, 1, 2], [2, 3, 1, 4], [2, 3, 1, 1], [2, 3, 1, 3], [2, 3, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_121_106_15 : ColCertDiv where
  rK := ⟨121, by decide⟩
  rH := ⟨106, by decide⟩
  m := 5
  T1 := T121_106
  T2 := Q2.T121_106_2
  h1 := (3,2,2,4,4)
  h2 := (3,2,2,4,1)
  D1 := [[3, 2, 3, 1], [3, 2, 3, 4], [3, 2, 3, 2], [3, 2, 3, 0], [3, 2, 3, 3]]
  D2 := [[3, 2, 3, 3], [3, 2, 3, 1], [3, 2, 3, 4], [3, 2, 3, 2], [3, 2, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_121_106_20 : ColCertDiv where
  rK := ⟨121, by decide⟩
  rH := ⟨106, by decide⟩
  m := 5
  T1 := T121_106
  T2 := Q2.T121_106_2
  h1 := (4,1,1,0,3)
  h2 := (4,1,1,0,1)
  D1 := [[4, 1, 1, 4], [4, 1, 1, 3], [4, 1, 1, 2], [4, 1, 1, 1], [4, 1, 1, 0]]
  D2 := [[4, 1, 1, 2], [4, 1, 1, 1], [4, 1, 1, 0], [4, 1, 1, 4], [4, 1, 1, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_122_2_1 : ColCertDiv where
  rK := ⟨122, by decide⟩
  rH := ⟨2, by decide⟩
  m := 5
  T1 := T122_2
  T2 := Q2.T122_2_2
  h1 := (1,0,4,1,0)
  h2 := (1,0,4,1,0)
  D1 := [[1, 0, 2, 1], [1, 0, 2, 1], [1, 0, 2, 1], [1, 0, 2, 1], [1, 0, 2, 1]]
  D2 := [[1, 0, 2, 3], [1, 0, 2, 3], [1, 0, 2, 3], [1, 0, 2, 3], [1, 0, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_122_2_2 : ColCertDiv where
  rK := ⟨122, by decide⟩
  rH := ⟨2, by decide⟩
  m := 5
  T1 := T122_2
  T2 := Q2.T122_2_2
  h1 := (2,0,3,2,1)
  h2 := (2,0,3,2,1)
  D1 := [[2, 0, 4, 0], [2, 0, 4, 0], [2, 0, 4, 0], [2, 0, 4, 0], [2, 0, 4, 0]]
  D2 := [[2, 0, 4, 4], [2, 0, 4, 4], [2, 0, 4, 4], [2, 0, 4, 4], [2, 0, 4, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_122_2_3 : ColCertDiv where
  rK := ⟨122, by decide⟩
  rH := ⟨2, by decide⟩
  m := 5
  T1 := T122_2
  T2 := Q2.T122_2_2
  h1 := (3,0,2,3,3)
  h2 := (3,0,2,3,3)
  D1 := [[3, 0, 1, 2], [3, 0, 1, 2], [3, 0, 1, 2], [3, 0, 1, 2], [3, 0, 1, 2]]
  D2 := [[3, 0, 1, 3], [3, 0, 1, 3], [3, 0, 1, 3], [3, 0, 1, 3], [3, 0, 1, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_122_2_4 : ColCertDiv where
  rK := ⟨122, by decide⟩
  rH := ⟨2, by decide⟩
  m := 5
  T1 := T122_2
  T2 := Q2.T122_2_2
  h1 := (4,0,1,4,1)
  h2 := (4,0,1,4,1)
  D1 := [[4, 0, 3, 2], [4, 0, 3, 2], [4, 0, 3, 2], [4, 0, 3, 2], [4, 0, 3, 2]]
  D2 := [[4, 0, 3, 0], [4, 0, 3, 0], [4, 0, 3, 0], [4, 0, 3, 0], [4, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_122_20_5 : ColCertDiv where
  rK := ⟨122, by decide⟩
  rH := ⟨20, by decide⟩
  m := 5
  T1 := T122_20
  T2 := Q2.T122_20_2
  h1 := (1,0,4,1,1)
  h2 := (1,0,4,1,1)
  D1 := [[1, 0, 2, 2], [1, 0, 2, 2], [1, 0, 2, 2], [1, 0, 2, 2], [1, 0, 2, 2]]
  D2 := [[1, 0, 2, 4], [1, 0, 2, 4], [1, 0, 2, 4], [1, 0, 2, 4], [1, 0, 2, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_122_20_10 : ColCertDiv where
  rK := ⟨122, by decide⟩
  rH := ⟨20, by decide⟩
  m := 5
  T1 := T122_20
  T2 := Q2.T122_20_2
  h1 := (2,0,3,2,3)
  h2 := (2,0,3,2,3)
  D1 := [[2, 0, 4, 2], [2, 0, 4, 2], [2, 0, 4, 2], [2, 0, 4, 2], [2, 0, 4, 2]]
  D2 := [[2, 0, 4, 1], [2, 0, 4, 1], [2, 0, 4, 1], [2, 0, 4, 1], [2, 0, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_122_20_15 : ColCertDiv where
  rK := ⟨122, by decide⟩
  rH := ⟨20, by decide⟩
  m := 5
  T1 := T122_20
  T2 := Q2.T122_20_2
  h1 := (3,0,2,3,1)
  h2 := (3,0,2,3,1)
  D1 := [[3, 0, 1, 0], [3, 0, 1, 0], [3, 0, 1, 0], [3, 0, 1, 0], [3, 0, 1, 0]]
  D2 := [[3, 0, 1, 1], [3, 0, 1, 1], [3, 0, 1, 1], [3, 0, 1, 1], [3, 0, 1, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_122_20_20 : ColCertDiv where
  rK := ⟨122, by decide⟩
  rH := ⟨20, by decide⟩
  m := 5
  T1 := T122_20
  T2 := Q2.T122_20_2
  h1 := (4,0,1,4,0)
  h2 := (4,0,1,4,0)
  D1 := [[4, 0, 3, 1], [4, 0, 3, 1], [4, 0, 3, 1], [4, 0, 3, 1], [4, 0, 3, 1]]
  D2 := [[4, 0, 3, 4], [4, 0, 3, 4], [4, 0, 3, 4], [4, 0, 3, 4], [4, 0, 3, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_122_36_5 : ColCertDiv where
  rK := ⟨122, by decide⟩
  rH := ⟨36, by decide⟩
  m := 5
  T1 := T122_36
  T2 := Q2.T122_36_2
  h1 := (1,3,1,0,1)
  h2 := (1,3,1,0,2)
  D1 := [[1, 3, 3, 4], [1, 3, 3, 1], [1, 3, 3, 3], [1, 3, 3, 0], [1, 3, 3, 2]]
  D2 := [[1, 3, 3, 3], [1, 3, 3, 0], [1, 3, 3, 2], [1, 3, 3, 4], [1, 3, 3, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_122_36_10 : ColCertDiv where
  rK := ⟨122, by decide⟩
  rH := ⟨36, by decide⟩
  m := 5
  T1 := T122_36
  T2 := Q2.T122_36_2
  h1 := (2,1,2,3,1)
  h2 := (2,1,2,3,4)
  D1 := [[2, 1, 3, 1], [2, 1, 3, 0], [2, 1, 3, 4], [2, 1, 3, 3], [2, 1, 3, 2]]
  D2 := [[2, 1, 3, 0], [2, 1, 3, 4], [2, 1, 3, 3], [2, 1, 3, 2], [2, 1, 3, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_122_36_15 : ColCertDiv where
  rK := ⟨122, by decide⟩
  rH := ⟨36, by decide⟩
  m := 5
  T1 := T122_36
  T2 := Q2.T122_36_2
  h1 := (3,4,3,4,1)
  h2 := (3,4,3,4,0)
  D1 := [[3, 4, 0, 2], [3, 4, 0, 3], [3, 4, 0, 4], [3, 4, 0, 0], [3, 4, 0, 1]]
  D2 := [[3, 4, 0, 0], [3, 4, 0, 1], [3, 4, 0, 2], [3, 4, 0, 3], [3, 4, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_122_36_20 : ColCertDiv where
  rK := ⟨122, by decide⟩
  rH := ⟨36, by decide⟩
  m := 5
  T1 := T122_36
  T2 := Q2.T122_36_2
  h1 := (4,2,4,3,1)
  h2 := (4,2,4,3,2)
  D1 := [[4, 2, 4, 2], [4, 2, 4, 0], [4, 2, 4, 3], [4, 2, 4, 1], [4, 2, 4, 4]]
  D2 := [[4, 2, 4, 0], [4, 2, 4, 3], [4, 2, 4, 1], [4, 2, 4, 4], [4, 2, 4, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_122_42_5 : ColCertDiv where
  rK := ⟨122, by decide⟩
  rH := ⟨42, by decide⟩
  m := 5
  T1 := T122_42
  T2 := Q2.T122_42_2
  h1 := (1,1,3,4,4)
  h2 := (1,1,3,4,2)
  D1 := [[1, 1, 4, 3], [1, 1, 4, 2], [1, 1, 4, 1], [1, 1, 4, 0], [1, 1, 4, 4]]
  D2 := [[1, 1, 4, 0], [1, 1, 4, 4], [1, 1, 4, 3], [1, 1, 4, 2], [1, 1, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_122_42_10 : ColCertDiv where
  rK := ⟨122, by decide⟩
  rH := ⟨42, by decide⟩
  m := 5
  T1 := T122_42
  T2 := Q2.T122_42_2
  h1 := (2,2,1,4,0)
  h2 := (2,2,1,4,1)
  D1 := [[2, 2, 2, 2], [2, 2, 2, 0], [2, 2, 2, 3], [2, 2, 2, 1], [2, 2, 2, 4]]
  D2 := [[2, 2, 2, 1], [2, 2, 2, 4], [2, 2, 2, 2], [2, 2, 2, 0], [2, 2, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_122_42_15 : ColCertDiv where
  rK := ⟨122, by decide⟩
  rH := ⟨42, by decide⟩
  m := 5
  T1 := T122_42
  T2 := Q2.T122_42_2
  h1 := (3,3,4,0,4)
  h2 := (3,3,4,0,3)
  D1 := [[3, 3, 4, 3], [3, 3, 4, 0], [3, 3, 4, 2], [3, 3, 4, 4], [3, 3, 4, 1]]
  D2 := [[3, 3, 4, 4], [3, 3, 4, 1], [3, 3, 4, 3], [3, 3, 4, 0], [3, 3, 4, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_122_42_20 : ColCertDiv where
  rK := ⟨122, by decide⟩
  rH := ⟨42, by decide⟩
  m := 5
  T1 := T122_42
  T2 := Q2.T122_42_2
  h1 := (4,4,2,2,2)
  h2 := (4,4,2,2,4)
  D1 := [[4, 4, 0, 2], [4, 4, 0, 3], [4, 4, 0, 4], [4, 4, 0, 0], [4, 4, 0, 1]]
  D2 := [[4, 4, 0, 0], [4, 4, 0, 1], [4, 4, 0, 2], [4, 4, 0, 3], [4, 4, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_122_45_5 : ColCertDiv where
  rK := ⟨122, by decide⟩
  rH := ⟨45, by decide⟩
  m := 5
  T1 := T122_45
  T2 := Q2.T122_45_2
  h1 := (1,2,2,2,1)
  h2 := (1,2,2,2,3)
  D1 := [[1, 2, 1, 4], [1, 2, 1, 2], [1, 2, 1, 0], [1, 2, 1, 3], [1, 2, 1, 1]]
  D2 := [[1, 2, 1, 2], [1, 2, 1, 0], [1, 2, 1, 3], [1, 2, 1, 1], [1, 2, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_122_45_10 : ColCertDiv where
  rK := ⟨122, by decide⟩
  rH := ⟨45, by decide⟩
  m := 5
  T1 := T122_45
  T2 := Q2.T122_45_2
  h1 := (2,4,4,1,3)
  h2 := (2,4,4,1,2)
  D1 := [[2, 4, 0, 2], [2, 4, 0, 3], [2, 4, 0, 4], [2, 4, 0, 0], [2, 4, 0, 1]]
  D2 := [[2, 4, 0, 3], [2, 4, 0, 4], [2, 4, 0, 0], [2, 4, 0, 1], [2, 4, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_122_45_20 : ColCertDiv where
  rK := ⟨122, by decide⟩
  rH := ⟨45, by decide⟩
  m := 5
  T1 := T122_45
  T2 := Q2.T122_45_2
  h1 := (4,3,3,0,4)
  h2 := (4,3,3,0,3)
  D1 := [[4, 3, 2, 4], [4, 3, 2, 1], [4, 3, 2, 3], [4, 3, 2, 0], [4, 3, 2, 2]]
  D2 := [[4, 3, 2, 2], [4, 3, 2, 4], [4, 3, 2, 1], [4, 3, 2, 3], [4, 3, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_122_49_10 : ColCertDiv where
  rK := ⟨122, by decide⟩
  rH := ⟨49, by decide⟩
  m := 5
  T1 := T122_49
  T2 := Q2.T122_49_2
  h1 := (2,3,0,0,2)
  h2 := (2,3,0,0,3)
  D1 := [[2, 3, 1, 2], [2, 3, 1, 4], [2, 3, 1, 1], [2, 3, 1, 3], [2, 3, 1, 0]]
  D2 := [[2, 3, 1, 3], [2, 3, 1, 0], [2, 3, 1, 2], [2, 3, 1, 4], [2, 3, 1, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_122_49_15 : ColCertDiv where
  rK := ⟨122, by decide⟩
  rH := ⟨49, by decide⟩
  m := 5
  T1 := T122_49
  T2 := Q2.T122_49_2
  h1 := (3,2,0,1,2)
  h2 := (3,2,0,1,4)
  D1 := [[3, 2, 3, 0], [3, 2, 3, 3], [3, 2, 3, 1], [3, 2, 3, 4], [3, 2, 3, 2]]
  D2 := [[3, 2, 3, 2], [3, 2, 3, 0], [3, 2, 3, 3], [3, 2, 3, 1], [3, 2, 3, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_122_49_20 : ColCertDiv where
  rK := ⟨122, by decide⟩
  rH := ⟨49, by decide⟩
  m := 5
  T1 := T122_49
  T2 := Q2.T122_49_2
  h1 := (4,1,0,1,3)
  h2 := (4,1,0,1,1)
  D1 := [[4, 1, 1, 1], [4, 1, 1, 0], [4, 1, 1, 4], [4, 1, 1, 3], [4, 1, 1, 2]]
  D2 := [[4, 1, 1, 4], [4, 1, 1, 3], [4, 1, 1, 2], [4, 1, 1, 1], [4, 1, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_122_81_5 : ColCertDiv where
  rK := ⟨122, by decide⟩
  rH := ⟨81, by decide⟩
  m := 5
  T1 := T122_81
  T2 := Q2.T122_81_2
  h1 := (1,0,4,0,0)
  h2 := (1,0,4,0,0)
  D1 := [[1, 0, 1, 2], [1, 0, 1, 2], [1, 0, 1, 2], [1, 0, 1, 2], [1, 0, 1, 2]]
  D2 := [[1, 0, 1, 4], [1, 0, 1, 4], [1, 0, 1, 4], [1, 0, 1, 4], [1, 0, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_122_81_10 : ColCertDiv where
  rK := ⟨122, by decide⟩
  rH := ⟨81, by decide⟩
  m := 5
  T1 := T122_81
  T2 := Q2.T122_81_2
  h1 := (2,0,3,0,0)
  h2 := (2,0,3,0,0)
  D1 := [[2, 0, 2, 3], [2, 0, 2, 3], [2, 0, 2, 3], [2, 0, 2, 3], [2, 0, 2, 3]]
  D2 := [[2, 0, 2, 2], [2, 0, 2, 2], [2, 0, 2, 2], [2, 0, 2, 2], [2, 0, 2, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_122_81_15 : ColCertDiv where
  rK := ⟨122, by decide⟩
  rH := ⟨81, by decide⟩
  m := 5
  T1 := T122_81
  T2 := Q2.T122_81_2
  h1 := (3,0,2,0,0)
  h2 := (3,0,2,0,0)
  D1 := [[3, 0, 3, 3], [3, 0, 3, 3], [3, 0, 3, 3], [3, 0, 3, 3], [3, 0, 3, 3]]
  D2 := [[3, 0, 3, 4], [3, 0, 3, 4], [3, 0, 3, 4], [3, 0, 3, 4], [3, 0, 3, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_122_81_20 : ColCertDiv where
  rK := ⟨122, by decide⟩
  rH := ⟨81, by decide⟩
  m := 5
  T1 := T122_81
  T2 := Q2.T122_81_2
  h1 := (4,0,1,0,0)
  h2 := (4,0,1,0,0)
  D1 := [[4, 0, 4, 2], [4, 0, 4, 2], [4, 0, 4, 2], [4, 0, 4, 2], [4, 0, 4, 2]]
  D2 := [[4, 0, 4, 0], [4, 0, 4, 0], [4, 0, 4, 0], [4, 0, 4, 0], [4, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_122_90_25 : ColCertDiv where
  rK := ⟨122, by decide⟩
  rH := ⟨90, by decide⟩
  m := 5
  T1 := T122_90
  T2 := Q2.T122_90_2
  h1 := (0,1,4,0,0)
  h2 := (0,1,4,0,0)
  D1 := [[0, 1, 0, 0], [0, 1, 0, 4], [0, 1, 0, 3], [0, 1, 0, 2], [0, 1, 0, 1]]
  D2 := [[0, 1, 0, 2], [0, 1, 0, 1], [0, 1, 0, 0], [0, 1, 0, 4], [0, 1, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_122_90_50 : ColCertDiv where
  rK := ⟨122, by decide⟩
  rH := ⟨90, by decide⟩
  m := 5
  T1 := T122_90
  T2 := Q2.T122_90_2
  h1 := (0,2,3,0,4)
  h2 := (0,2,3,0,4)
  D1 := [[0, 2, 0, 0], [0, 2, 0, 3], [0, 2, 0, 1], [0, 2, 0, 4], [0, 2, 0, 2]]
  D2 := [[0, 2, 0, 4], [0, 2, 0, 2], [0, 2, 0, 0], [0, 2, 0, 3], [0, 2, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_122_90_75 : ColCertDiv where
  rK := ⟨122, by decide⟩
  rH := ⟨90, by decide⟩
  m := 5
  T1 := T122_90
  T2 := Q2.T122_90_2
  h1 := (0,3,2,0,2)
  h2 := (0,3,2,0,2)
  D1 := [[0, 3, 0, 0], [0, 3, 0, 2], [0, 3, 0, 4], [0, 3, 0, 1], [0, 3, 0, 3]]
  D2 := [[0, 3, 0, 1], [0, 3, 0, 3], [0, 3, 0, 0], [0, 3, 0, 2], [0, 3, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_122_90_100 : ColCertDiv where
  rK := ⟨122, by decide⟩
  rH := ⟨90, by decide⟩
  m := 5
  T1 := T122_90
  T2 := Q2.T122_90_2
  h1 := (0,4,1,0,4)
  h2 := (0,4,1,0,4)
  D1 := [[0, 4, 0, 0], [0, 4, 0, 1], [0, 4, 0, 2], [0, 4, 0, 3], [0, 4, 0, 4]]
  D2 := [[0, 4, 0, 3], [0, 4, 0, 4], [0, 4, 0, 0], [0, 4, 0, 1], [0, 4, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_122_98_5 : ColCertDiv where
  rK := ⟨122, by decide⟩
  rH := ⟨98, by decide⟩
  m := 5
  T1 := T122_98
  T2 := Q2.T122_98_2
  h1 := (1,3,1,1,3)
  h2 := (1,3,1,1,3)
  D1 := [[1, 3, 4, 0], [1, 3, 4, 2], [1, 3, 4, 4], [1, 3, 4, 1], [1, 3, 4, 3]]
  D2 := [[1, 3, 4, 3], [1, 3, 4, 0], [1, 3, 4, 2], [1, 3, 4, 4], [1, 3, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_122_98_10 : ColCertDiv where
  rK := ⟨122, by decide⟩
  rH := ⟨98, by decide⟩
  m := 5
  T1 := T122_98
  T2 := Q2.T122_98_2
  h1 := (2,1,2,0,1)
  h2 := (2,1,2,0,2)
  D1 := [[2, 1, 0, 2], [2, 1, 0, 1], [2, 1, 0, 0], [2, 1, 0, 4], [2, 1, 0, 3]]
  D2 := [[2, 1, 0, 4], [2, 1, 0, 3], [2, 1, 0, 2], [2, 1, 0, 1], [2, 1, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_122_98_20 : ColCertDiv where
  rK := ⟨122, by decide⟩
  rH := ⟨98, by decide⟩
  m := 5
  T1 := T122_98
  T2 := Q2.T122_98_2
  h1 := (4,2,4,2,0)
  h2 := (4,2,4,2,2)
  D1 := [[4, 2, 3, 0], [4, 2, 3, 3], [4, 2, 3, 1], [4, 2, 3, 4], [4, 2, 3, 2]]
  D2 := [[4, 2, 3, 4], [4, 2, 3, 2], [4, 2, 3, 0], [4, 2, 3, 3], [4, 2, 3, 1]]
  bind1 := by decide
  bind2 := by decide

end LeanDring.P5Presentation
