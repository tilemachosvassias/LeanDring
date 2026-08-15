/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.Twin1.ColCert
import LeanDring.P5.Data.EntryK.C036
import LeanDring.P5.Data.EntryK.C037

/-!
# Species-table cell data, stage 2 — column-data-divergent columns

Per-column certified exponent-vector data (`ColCert`/`ColCertDiv`) with kernel
`decide` bindings. Emitted; the embedded lists are what the kernel certifies.
cdd tier, chunk 16: 60 columns.
-/

-- machine-emitted data: silence style linters (generated long lines, file-level options)
set_option linter.style.longLine false

namespace LeanDring.P5Presentation

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

def colCertDiv_135_41_20 : ColCertDiv where
  rK := ⟨135, by decide⟩
  rH := ⟨41, by decide⟩
  m := 5
  T1 := T135_41
  T2 := Q2.T135_41_2
  h1 := (4,2,1,3,1)
  h2 := (4,2,1,3,2)
  D1 := [[4, 2, 0, 2], [4, 2, 0, 0], [4, 2, 0, 3], [4, 2, 0, 1], [4, 2, 0, 4]]
  D2 := [[4, 2, 0, 0], [4, 2, 0, 3], [4, 2, 0, 1], [4, 2, 0, 4], [4, 2, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_135_45_5 : ColCertDiv where
  rK := ⟨135, by decide⟩
  rH := ⟨45, by decide⟩
  m := 5
  T1 := T135_45
  T2 := Q2.T135_45_2
  h1 := (1,2,2,2,1)
  h2 := (1,2,2,2,3)
  D1 := [[1, 2, 0, 3], [1, 2, 0, 1], [1, 2, 0, 4], [1, 2, 0, 2], [1, 2, 0, 0]]
  D2 := [[1, 2, 0, 4], [1, 2, 0, 2], [1, 2, 0, 0], [1, 2, 0, 3], [1, 2, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_135_45_10 : ColCertDiv where
  rK := ⟨135, by decide⟩
  rH := ⟨45, by decide⟩
  m := 5
  T1 := T135_45
  T2 := Q2.T135_45_2
  h1 := (2,4,4,1,3)
  h2 := (2,4,4,1,2)
  D1 := [[2, 4, 3, 4], [2, 4, 3, 0], [2, 4, 3, 1], [2, 4, 3, 2], [2, 4, 3, 3]]
  D2 := [[2, 4, 3, 1], [2, 4, 3, 2], [2, 4, 3, 3], [2, 4, 3, 4], [2, 4, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_135_45_15 : ColCertDiv where
  rK := ⟨135, by decide⟩
  rH := ⟨45, by decide⟩
  m := 5
  T1 := T135_45
  T2 := Q2.T135_45_2
  h1 := (3,1,1,2,4)
  h2 := (3,1,1,2,1)
  D1 := [[3, 1, 4, 1], [3, 1, 4, 0], [3, 1, 4, 4], [3, 1, 4, 3], [3, 1, 4, 2]]
  D2 := [[3, 1, 4, 0], [3, 1, 4, 4], [3, 1, 4, 3], [3, 1, 4, 2], [3, 1, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_135_52_5 : ColCertDiv where
  rK := ⟨135, by decide⟩
  rH := ⟨52, by decide⟩
  m := 5
  T1 := T135_52
  T2 := Q2.T135_52_2
  h1 := (1,1,0,4,1)
  h2 := (1,1,0,4,4)
  D1 := [[1, 1, 3, 1], [1, 1, 3, 0], [1, 1, 3, 4], [1, 1, 3, 3], [1, 1, 3, 2]]
  D2 := [[1, 1, 3, 4], [1, 1, 3, 3], [1, 1, 3, 2], [1, 1, 3, 1], [1, 1, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_135_52_10 : ColCertDiv where
  rK := ⟨135, by decide⟩
  rH := ⟨52, by decide⟩
  m := 5
  T1 := T135_52
  T2 := Q2.T135_52_2
  h1 := (2,2,0,4,1)
  h2 := (2,2,0,4,2)
  D1 := [[2, 2, 0, 3], [2, 2, 0, 1], [2, 2, 0, 4], [2, 2, 0, 2], [2, 2, 0, 0]]
  D2 := [[2, 2, 0, 4], [2, 2, 0, 2], [2, 2, 0, 0], [2, 2, 0, 3], [2, 2, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_135_52_15 : ColCertDiv where
  rK := ⟨135, by decide⟩
  rH := ⟨52, by decide⟩
  m := 5
  T1 := T135_52
  T2 := Q2.T135_52_2
  h1 := (3,3,0,0,1)
  h2 := (3,3,0,0,0)
  D1 := [[3, 3, 1, 2], [3, 3, 1, 4], [3, 3, 1, 1], [3, 3, 1, 3], [3, 3, 1, 0]]
  D2 := [[3, 3, 1, 1], [3, 3, 1, 3], [3, 3, 1, 0], [3, 3, 1, 2], [3, 3, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_135_52_20 : ColCertDiv where
  rK := ⟨135, by decide⟩
  rH := ⟨52, by decide⟩
  m := 5
  T1 := T135_52
  T2 := Q2.T135_52_2
  h1 := (4,4,0,2,2)
  h2 := (4,4,0,2,4)
  D1 := [[4, 4, 1, 4], [4, 4, 1, 0], [4, 4, 1, 1], [4, 4, 1, 2], [4, 4, 1, 3]]
  D2 := [[4, 4, 1, 1], [4, 4, 1, 2], [4, 4, 1, 3], [4, 4, 1, 4], [4, 4, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_135_83_5 : ColCertDiv where
  rK := ⟨135, by decide⟩
  rH := ⟨83, by decide⟩
  m := 5
  T1 := T135_83
  T2 := Q2.T135_83_2
  h1 := (1,0,3,0,0)
  h2 := (1,0,3,0,0)
  D1 := [[1, 0, 0, 2], [1, 0, 0, 2], [1, 0, 0, 2], [1, 0, 0, 2], [1, 0, 0, 2]]
  D2 := [[1, 0, 0, 3], [1, 0, 0, 3], [1, 0, 0, 3], [1, 0, 0, 3], [1, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_135_83_10 : ColCertDiv where
  rK := ⟨135, by decide⟩
  rH := ⟨83, by decide⟩
  m := 5
  T1 := T135_83
  T2 := Q2.T135_83_2
  h1 := (2,0,1,0,0)
  h2 := (2,0,1,0,0)
  D1 := [[2, 0, 0, 4], [2, 0, 0, 4], [2, 0, 0, 4], [2, 0, 0, 4], [2, 0, 0, 4]]
  D2 := [[2, 0, 0, 1], [2, 0, 0, 1], [2, 0, 0, 1], [2, 0, 0, 1], [2, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_135_83_15 : ColCertDiv where
  rK := ⟨135, by decide⟩
  rH := ⟨83, by decide⟩
  m := 5
  T1 := T135_83
  T2 := Q2.T135_83_2
  h1 := (3,0,4,0,0)
  h2 := (3,0,4,0,0)
  D1 := [[3, 0, 0, 1], [3, 0, 0, 1], [3, 0, 0, 1], [3, 0, 0, 1], [3, 0, 0, 1]]
  D2 := [[3, 0, 0, 4], [3, 0, 0, 4], [3, 0, 0, 4], [3, 0, 0, 4], [3, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_135_83_20 : ColCertDiv where
  rK := ⟨135, by decide⟩
  rH := ⟨83, by decide⟩
  m := 5
  T1 := T135_83
  T2 := Q2.T135_83_2
  h1 := (4,0,2,0,0)
  h2 := (4,0,2,0,0)
  D1 := [[4, 0, 0, 3], [4, 0, 0, 3], [4, 0, 0, 3], [4, 0, 0, 3], [4, 0, 0, 3]]
  D2 := [[4, 0, 0, 2], [4, 0, 0, 2], [4, 0, 0, 2], [4, 0, 0, 2], [4, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_135_91_5 : ColCertDiv where
  rK := ⟨135, by decide⟩
  rH := ⟨91, by decide⟩
  m := 5
  T1 := T135_91
  T2 := Q2.T135_91_2
  h1 := (1,4,1,4,4)
  h2 := (1,4,1,4,4)
  D1 := [[1, 4, 0, 3], [1, 4, 0, 4], [1, 4, 0, 0], [1, 4, 0, 1], [1, 4, 0, 2]]
  D2 := [[1, 4, 0, 0], [1, 4, 0, 1], [1, 4, 0, 2], [1, 4, 0, 3], [1, 4, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_135_91_15 : ColCertDiv where
  rK := ⟨135, by decide⟩
  rH := ⟨91, by decide⟩
  m := 5
  T1 := T135_91
  T2 := Q2.T135_91_2
  h1 := (3,2,3,4,2)
  h2 := (3,2,3,4,4)
  D1 := [[3, 2, 3, 3], [3, 2, 3, 1], [3, 2, 3, 4], [3, 2, 3, 2], [3, 2, 3, 0]]
  D2 := [[3, 2, 3, 1], [3, 2, 3, 4], [3, 2, 3, 2], [3, 2, 3, 0], [3, 2, 3, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_135_91_20 : ColCertDiv where
  rK := ⟨135, by decide⟩
  rH := ⟨91, by decide⟩
  m := 5
  T1 := T135_91
  T2 := Q2.T135_91_2
  h1 := (4,1,4,0,3)
  h2 := (4,1,4,0,1)
  D1 := [[4, 1, 1, 2], [4, 1, 1, 1], [4, 1, 1, 0], [4, 1, 1, 4], [4, 1, 1, 3]]
  D2 := [[4, 1, 1, 3], [4, 1, 1, 2], [4, 1, 1, 1], [4, 1, 1, 0], [4, 1, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_135_95_25 : ColCertDiv where
  rK := ⟨135, by decide⟩
  rH := ⟨95, by decide⟩
  m := 5
  T1 := T135_95
  T2 := Q2.T135_95_2
  h1 := (0,1,2,0,0)
  h2 := (0,1,2,0,0)
  D1 := [[0, 1, 0, 1], [0, 1, 0, 0], [0, 1, 0, 4], [0, 1, 0, 3], [0, 1, 0, 2]]
  D2 := [[0, 1, 0, 0], [0, 1, 0, 4], [0, 1, 0, 3], [0, 1, 0, 2], [0, 1, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_135_95_50 : ColCertDiv where
  rK := ⟨135, by decide⟩
  rH := ⟨95, by decide⟩
  m := 5
  T1 := T135_95
  T2 := Q2.T135_95_2
  h1 := (0,2,4,0,2)
  h2 := (0,2,4,0,2)
  D1 := [[0, 2, 0, 2], [0, 2, 0, 0], [0, 2, 0, 3], [0, 2, 0, 1], [0, 2, 0, 4]]
  D2 := [[0, 2, 0, 0], [0, 2, 0, 3], [0, 2, 0, 1], [0, 2, 0, 4], [0, 2, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_135_95_75 : ColCertDiv where
  rK := ⟨135, by decide⟩
  rH := ⟨95, by decide⟩
  m := 5
  T1 := T135_95
  T2 := Q2.T135_95_2
  h1 := (0,3,1,0,1)
  h2 := (0,3,1,0,1)
  D1 := [[0, 3, 0, 3], [0, 3, 0, 0], [0, 3, 0, 2], [0, 3, 0, 4], [0, 3, 0, 1]]
  D2 := [[0, 3, 0, 0], [0, 3, 0, 2], [0, 3, 0, 4], [0, 3, 0, 1], [0, 3, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_135_95_100 : ColCertDiv where
  rK := ⟨135, by decide⟩
  rH := ⟨95, by decide⟩
  m := 5
  T1 := T135_95
  T2 := Q2.T135_95_2
  h1 := (0,4,3,0,2)
  h2 := (0,4,3,0,2)
  D1 := [[0, 4, 0, 4], [0, 4, 0, 0], [0, 4, 0, 1], [0, 4, 0, 2], [0, 4, 0, 3]]
  D2 := [[0, 4, 0, 0], [0, 4, 0, 1], [0, 4, 0, 2], [0, 4, 0, 3], [0, 4, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_135_103_5 : ColCertDiv where
  rK := ⟨135, by decide⟩
  rH := ⟨103, by decide⟩
  m := 5
  T1 := T135_103
  T2 := Q2.T135_103_2
  h1 := (1,3,4,1,1)
  h2 := (1,3,4,1,1)
  D1 := [[1, 3, 3, 2], [1, 3, 3, 4], [1, 3, 3, 1], [1, 3, 3, 3], [1, 3, 3, 0]]
  D2 := [[1, 3, 3, 0], [1, 3, 3, 2], [1, 3, 3, 4], [1, 3, 3, 1], [1, 3, 3, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_135_103_10 : ColCertDiv where
  rK := ⟨135, by decide⟩
  rH := ⟨103, by decide⟩
  m := 5
  T1 := T135_103
  T2 := Q2.T135_103_2
  h1 := (2,1,3,0,1)
  h2 := (2,1,3,0,2)
  D1 := [[2, 1, 3, 4], [2, 1, 3, 3], [2, 1, 3, 2], [2, 1, 3, 1], [2, 1, 3, 0]]
  D2 := [[2, 1, 3, 1], [2, 1, 3, 0], [2, 1, 3, 4], [2, 1, 3, 3], [2, 1, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_135_103_20 : ColCertDiv where
  rK := ⟨135, by decide⟩
  rH := ⟨103, by decide⟩
  m := 5
  T1 := T135_103
  T2 := Q2.T135_103_2
  h1 := (4,2,1,2,1)
  h2 := (4,2,1,2,3)
  D1 := [[4, 2, 4, 1], [4, 2, 4, 4], [4, 2, 4, 2], [4, 2, 4, 0], [4, 2, 4, 3]]
  D2 := [[4, 2, 4, 0], [4, 2, 4, 3], [4, 2, 4, 1], [4, 2, 4, 4], [4, 2, 4, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_135_107_5 : ColCertDiv where
  rK := ⟨135, by decide⟩
  rH := ⟨107, by decide⟩
  m := 5
  T1 := T135_107
  T2 := Q2.T135_107_2
  h1 := (1,2,2,3,4)
  h2 := (1,2,2,3,4)
  D1 := [[1, 2, 1, 0], [1, 2, 1, 3], [1, 2, 1, 1], [1, 2, 1, 4], [1, 2, 1, 2]]
  D2 := [[1, 2, 1, 4], [1, 2, 1, 2], [1, 2, 1, 0], [1, 2, 1, 3], [1, 2, 1, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_135_107_10 : ColCertDiv where
  rK := ⟨135, by decide⟩
  rH := ⟨107, by decide⟩
  m := 5
  T1 := T135_107
  T2 := Q2.T135_107_2
  h1 := (2,4,4,3,0)
  h2 := (2,4,4,3,0)
  D1 := [[2, 4, 0, 2], [2, 4, 0, 3], [2, 4, 0, 4], [2, 4, 0, 0], [2, 4, 0, 1]]
  D2 := [[2, 4, 0, 0], [2, 4, 0, 1], [2, 4, 0, 2], [2, 4, 0, 3], [2, 4, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_135_107_15 : ColCertDiv where
  rK := ⟨135, by decide⟩
  rH := ⟨107, by decide⟩
  m := 5
  T1 := T135_107
  T2 := Q2.T135_107_2
  h1 := (3,1,1,0,1)
  h2 := (3,1,1,0,2)
  D1 := [[3, 1, 2, 4], [3, 1, 2, 3], [3, 1, 2, 2], [3, 1, 2, 1], [3, 1, 2, 0]]
  D2 := [[3, 1, 2, 2], [3, 1, 2, 1], [3, 1, 2, 0], [3, 1, 2, 4], [3, 1, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_135_107_20 : ColCertDiv where
  rK := ⟨135, by decide⟩
  rH := ⟨107, by decide⟩
  m := 5
  T1 := T135_107
  T2 := Q2.T135_107_2
  h1 := (4,3,3,4,2)
  h2 := (4,3,3,4,3)
  D1 := [[4, 3, 2, 1], [4, 3, 2, 3], [4, 3, 2, 0], [4, 3, 2, 2], [4, 3, 2, 4]]
  D2 := [[4, 3, 2, 3], [4, 3, 2, 0], [4, 3, 2, 2], [4, 3, 2, 4], [4, 3, 2, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_136_29_10 : ColCertDiv where
  rK := ⟨136, by decide⟩
  rH := ⟨29, by decide⟩
  m := 5
  T1 := T136_29
  T2 := Q2.T136_29_2
  h1 := (2,3,2,0,4)
  h2 := (2,3,2,0,0)
  D1 := [[2, 3, 4, 0], [2, 3, 4, 2], [2, 3, 4, 4], [2, 3, 4, 1], [2, 3, 4, 3]]
  D2 := [[2, 3, 4, 1], [2, 3, 4, 3], [2, 3, 4, 0], [2, 3, 4, 2], [2, 3, 4, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_136_29_15 : ColCertDiv where
  rK := ⟨136, by decide⟩
  rH := ⟨29, by decide⟩
  m := 5
  T1 := T136_29
  T2 := Q2.T136_29_2
  h1 := (3,2,3,1,1)
  h2 := (3,2,3,1,3)
  D1 := [[3, 2, 0, 3], [3, 2, 0, 1], [3, 2, 0, 4], [3, 2, 0, 2], [3, 2, 0, 0]]
  D2 := [[3, 2, 0, 0], [3, 2, 0, 3], [3, 2, 0, 1], [3, 2, 0, 4], [3, 2, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_136_29_20 : ColCertDiv where
  rK := ⟨136, by decide⟩
  rH := ⟨29, by decide⟩
  m := 5
  T1 := T136_29
  T2 := Q2.T136_29_2
  h1 := (4,1,4,1,3)
  h2 := (4,1,4,1,1)
  D1 := [[4, 1, 2, 3], [4, 1, 2, 2], [4, 1, 2, 1], [4, 1, 2, 0], [4, 1, 2, 4]]
  D2 := [[4, 1, 2, 1], [4, 1, 2, 0], [4, 1, 2, 4], [4, 1, 2, 3], [4, 1, 2, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_136_36_5 : ColCertDiv where
  rK := ⟨136, by decide⟩
  rH := ⟨36, by decide⟩
  m := 5
  T1 := T136_36
  T2 := Q2.T136_36_2
  h1 := (1,3,1,0,1)
  h2 := (1,3,1,0,2)
  D1 := [[1, 3, 2, 1], [1, 3, 2, 3], [1, 3, 2, 0], [1, 3, 2, 2], [1, 3, 2, 4]]
  D2 := [[1, 3, 2, 2], [1, 3, 2, 4], [1, 3, 2, 1], [1, 3, 2, 3], [1, 3, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_136_36_10 : ColCertDiv where
  rK := ⟨136, by decide⟩
  rH := ⟨36, by decide⟩
  m := 5
  T1 := T136_36
  T2 := Q2.T136_36_2
  h1 := (2,1,2,3,1)
  h2 := (2,1,2,3,4)
  D1 := [[2, 1, 1, 2], [2, 1, 1, 1], [2, 1, 1, 0], [2, 1, 1, 4], [2, 1, 1, 3]]
  D2 := [[2, 1, 1, 0], [2, 1, 1, 4], [2, 1, 1, 3], [2, 1, 1, 2], [2, 1, 1, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_136_36_15 : ColCertDiv where
  rK := ⟨136, by decide⟩
  rH := ⟨36, by decide⟩
  m := 5
  T1 := T136_36
  T2 := Q2.T136_36_2
  h1 := (3,4,3,4,1)
  h2 := (3,4,3,4,0)
  D1 := [[3, 4, 2, 4], [3, 4, 2, 0], [3, 4, 2, 1], [3, 4, 2, 2], [3, 4, 2, 3]]
  D2 := [[3, 4, 2, 3], [3, 4, 2, 4], [3, 4, 2, 0], [3, 4, 2, 1], [3, 4, 2, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_136_36_20 : ColCertDiv where
  rK := ⟨136, by decide⟩
  rH := ⟨36, by decide⟩
  m := 5
  T1 := T136_36
  T2 := Q2.T136_36_2
  h1 := (4,2,4,3,1)
  h2 := (4,2,4,3,2)
  D1 := [[4, 2, 0, 2], [4, 2, 0, 0], [4, 2, 0, 3], [4, 2, 0, 1], [4, 2, 0, 4]]
  D2 := [[4, 2, 0, 3], [4, 2, 0, 1], [4, 2, 0, 4], [4, 2, 0, 2], [4, 2, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_136_40_5 : ColCertDiv where
  rK := ⟨136, by decide⟩
  rH := ⟨40, by decide⟩
  m := 5
  T1 := T136_40
  T2 := Q2.T136_40_2
  h1 := (1,2,1,2,4)
  h2 := (1,2,1,2,1)
  D1 := [[1, 2, 0, 2], [1, 2, 0, 0], [1, 2, 0, 3], [1, 2, 0, 1], [1, 2, 0, 4]]
  D2 := [[1, 2, 0, 4], [1, 2, 0, 2], [1, 2, 0, 0], [1, 2, 0, 3], [1, 2, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_136_40_10 : ColCertDiv where
  rK := ⟨136, by decide⟩
  rH := ⟨40, by decide⟩
  m := 5
  T1 := T136_40
  T2 := Q2.T136_40_2
  h1 := (2,4,2,1,2)
  h2 := (2,4,2,1,1)
  D1 := [[2, 4, 3, 3], [2, 4, 3, 4], [2, 4, 3, 0], [2, 4, 3, 1], [2, 4, 3, 2]]
  D2 := [[2, 4, 3, 2], [2, 4, 3, 3], [2, 4, 3, 4], [2, 4, 3, 0], [2, 4, 3, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_136_40_15 : ColCertDiv where
  rK := ⟨136, by decide⟩
  rH := ⟨40, by decide⟩
  m := 5
  T1 := T136_40
  T2 := Q2.T136_40_2
  h1 := (3,1,3,2,2)
  h2 := (3,1,3,2,4)
  D1 := [[3, 1, 4, 1], [3, 1, 4, 0], [3, 1, 4, 4], [3, 1, 4, 3], [3, 1, 4, 2]]
  D2 := [[3, 1, 4, 3], [3, 1, 4, 2], [3, 1, 4, 1], [3, 1, 4, 0], [3, 1, 4, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_136_40_20 : ColCertDiv where
  rK := ⟨136, by decide⟩
  rH := ⟨40, by decide⟩
  m := 5
  T1 := T136_40
  T2 := Q2.T136_40_2
  h1 := (4,3,4,0,4)
  h2 := (4,3,4,0,3)
  D1 := [[4, 3, 3, 1], [4, 3, 3, 3], [4, 3, 3, 0], [4, 3, 3, 2], [4, 3, 3, 4]]
  D2 := [[4, 3, 3, 0], [4, 3, 3, 2], [4, 3, 3, 4], [4, 3, 3, 1], [4, 3, 3, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_136_47_5 : ColCertDiv where
  rK := ⟨136, by decide⟩
  rH := ⟨47, by decide⟩
  m := 5
  T1 := T136_47
  T2 := Q2.T136_47_2
  h1 := (1,1,1,4,2)
  h2 := (1,1,1,4,0)
  D1 := [[1, 1, 3, 3], [1, 1, 3, 2], [1, 1, 3, 1], [1, 1, 3, 0], [1, 1, 3, 4]]
  D2 := [[1, 1, 3, 1], [1, 1, 3, 0], [1, 1, 3, 4], [1, 1, 3, 3], [1, 1, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_136_47_10 : ColCertDiv where
  rK := ⟨136, by decide⟩
  rH := ⟨47, by decide⟩
  m := 5
  T1 := T136_47
  T2 := Q2.T136_47_2
  h1 := (2,2,2,4,4)
  h2 := (2,2,2,4,0)
  D1 := [[2, 2, 0, 0], [2, 2, 0, 3], [2, 2, 0, 1], [2, 2, 0, 4], [2, 2, 0, 2]]
  D2 := [[2, 2, 0, 1], [2, 2, 0, 4], [2, 2, 0, 2], [2, 2, 0, 0], [2, 2, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_136_47_15 : ColCertDiv where
  rK := ⟨136, by decide⟩
  rH := ⟨47, by decide⟩
  m := 5
  T1 := T136_47
  T2 := Q2.T136_47_2
  h1 := (3,3,3,0,2)
  h2 := (3,3,3,0,1)
  D1 := [[3, 3, 1, 2], [3, 3, 1, 4], [3, 3, 1, 1], [3, 3, 1, 3], [3, 3, 1, 0]]
  D2 := [[3, 3, 1, 1], [3, 3, 1, 3], [3, 3, 1, 0], [3, 3, 1, 2], [3, 3, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_136_47_20 : ColCertDiv where
  rK := ⟨136, by decide⟩
  rH := ⟨47, by decide⟩
  m := 5
  T1 := T136_47
  T2 := Q2.T136_47_2
  h1 := (4,4,4,2,2)
  h2 := (4,4,4,2,4)
  D1 := [[4, 4, 1, 0], [4, 4, 1, 1], [4, 4, 1, 2], [4, 4, 1, 3], [4, 4, 1, 4]]
  D2 := [[4, 4, 1, 2], [4, 4, 1, 3], [4, 4, 1, 4], [4, 4, 1, 0], [4, 4, 1, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_136_48_5 : ColCertDiv where
  rK := ⟨136, by decide⟩
  rH := ⟨48, by decide⟩
  m := 5
  T1 := T136_48
  T2 := Q2.T136_48_2
  h1 := (0,1,0,4,3)
  h2 := (0,1,0,4,1)
  D1 := [[0, 1, 4, 2], [0, 1, 4, 1], [0, 1, 4, 0], [0, 1, 4, 4], [0, 1, 4, 3]]
  D2 := [[0, 1, 4, 0], [0, 1, 4, 4], [0, 1, 4, 3], [0, 1, 4, 2], [0, 1, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_136_48_10 : ColCertDiv where
  rK := ⟨136, by decide⟩
  rH := ⟨48, by decide⟩
  m := 5
  T1 := T136_48
  T2 := Q2.T136_48_2
  h1 := (0,2,0,3,1)
  h2 := (0,2,0,3,2)
  D1 := [[0, 2, 3, 4], [0, 2, 3, 2], [0, 2, 3, 0], [0, 2, 3, 3], [0, 2, 3, 1]]
  D2 := [[0, 2, 3, 0], [0, 2, 3, 3], [0, 2, 3, 1], [0, 2, 3, 4], [0, 2, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_136_48_15 : ColCertDiv where
  rK := ⟨136, by decide⟩
  rH := ⟨48, by decide⟩
  m := 5
  T1 := T136_48
  T2 := Q2.T136_48_2
  h1 := (0,3,0,2,4)
  h2 := (0,3,0,2,3)
  D1 := [[0, 3, 2, 1], [0, 3, 2, 3], [0, 3, 2, 0], [0, 3, 2, 2], [0, 3, 2, 4]]
  D2 := [[0, 3, 2, 0], [0, 3, 2, 2], [0, 3, 2, 4], [0, 3, 2, 1], [0, 3, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_136_48_20 : ColCertDiv where
  rK := ⟨136, by decide⟩
  rH := ⟨48, by decide⟩
  m := 5
  T1 := T136_48
  T2 := Q2.T136_48_2
  h1 := (0,4,0,1,2)
  h2 := (0,4,0,1,4)
  D1 := [[0, 4, 1, 3], [0, 4, 1, 4], [0, 4, 1, 0], [0, 4, 1, 1], [0, 4, 1, 2]]
  D2 := [[0, 4, 1, 0], [0, 4, 1, 1], [0, 4, 1, 2], [0, 4, 1, 3], [0, 4, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_136_91_10 : ColCertDiv where
  rK := ⟨136, by decide⟩
  rH := ⟨91, by decide⟩
  m := 5
  T1 := T136_91
  T2 := Q2.T136_91_2
  h1 := (2,3,2,2,2)
  h2 := (2,3,2,2,3)
  D1 := [[2, 3, 1, 4], [2, 3, 1, 1], [2, 3, 1, 3], [2, 3, 1, 0], [2, 3, 1, 2]]
  D2 := [[2, 3, 1, 0], [2, 3, 1, 2], [2, 3, 1, 4], [2, 3, 1, 1], [2, 3, 1, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_136_91_15 : ColCertDiv where
  rK := ⟨136, by decide⟩
  rH := ⟨91, by decide⟩
  m := 5
  T1 := T136_91
  T2 := Q2.T136_91_2
  h1 := (3,2,3,4,2)
  h2 := (3,2,3,4,4)
  D1 := [[3, 2, 3, 0], [3, 2, 3, 3], [3, 2, 3, 1], [3, 2, 3, 4], [3, 2, 3, 2]]
  D2 := [[3, 2, 3, 2], [3, 2, 3, 0], [3, 2, 3, 3], [3, 2, 3, 1], [3, 2, 3, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_136_91_20 : ColCertDiv where
  rK := ⟨136, by decide⟩
  rH := ⟨91, by decide⟩
  m := 5
  T1 := T136_91
  T2 := Q2.T136_91_2
  h1 := (4,1,4,0,3)
  h2 := (4,1,4,0,1)
  D1 := [[4, 1, 1, 2], [4, 1, 1, 1], [4, 1, 1, 0], [4, 1, 1, 4], [4, 1, 1, 3]]
  D2 := [[4, 1, 1, 0], [4, 1, 1, 4], [4, 1, 1, 3], [4, 1, 1, 2], [4, 1, 1, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_136_98_10 : ColCertDiv where
  rK := ⟨136, by decide⟩
  rH := ⟨98, by decide⟩
  m := 5
  T1 := T136_98
  T2 := Q2.T136_98_2
  h1 := (2,1,2,0,1)
  h2 := (2,1,2,0,2)
  D1 := [[2, 1, 3, 3], [2, 1, 3, 2], [2, 1, 3, 1], [2, 1, 3, 0], [2, 1, 3, 4]]
  D2 := [[2, 1, 3, 4], [2, 1, 3, 3], [2, 1, 3, 2], [2, 1, 3, 1], [2, 1, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_136_98_15 : ColCertDiv where
  rK := ⟨136, by decide⟩
  rH := ⟨98, by decide⟩
  m := 5
  T1 := T136_98
  T2 := Q2.T136_98_2
  h1 := (3,4,3,2,0)
  h2 := (3,4,3,2,1)
  D1 := [[3, 4, 0, 4], [3, 4, 0, 0], [3, 4, 0, 1], [3, 4, 0, 2], [3, 4, 0, 3]]
  D2 := [[3, 4, 0, 0], [3, 4, 0, 1], [3, 4, 0, 2], [3, 4, 0, 3], [3, 4, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_136_98_20 : ColCertDiv where
  rK := ⟨136, by decide⟩
  rH := ⟨98, by decide⟩
  m := 5
  T1 := T136_98
  T2 := Q2.T136_98_2
  h1 := (4,2,4,2,0)
  h2 := (4,2,4,2,2)
  D1 := [[4, 2, 4, 0], [4, 2, 4, 3], [4, 2, 4, 1], [4, 2, 4, 4], [4, 2, 4, 2]]
  D2 := [[4, 2, 4, 2], [4, 2, 4, 0], [4, 2, 4, 3], [4, 2, 4, 1], [4, 2, 4, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_136_102_15 : ColCertDiv where
  rK := ⟨136, by decide⟩
  rH := ⟨102, by decide⟩
  m := 5
  T1 := T136_102
  T2 := Q2.T136_102_2
  h1 := (3,1,3,0,1)
  h2 := (3,1,3,0,2)
  D1 := [[3, 1, 2, 1], [3, 1, 2, 0], [3, 1, 2, 4], [3, 1, 2, 3], [3, 1, 2, 2]]
  D2 := [[3, 1, 2, 2], [3, 1, 2, 1], [3, 1, 2, 0], [3, 1, 2, 4], [3, 1, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_136_102_20 : ColCertDiv where
  rK := ⟨136, by decide⟩
  rH := ⟨102, by decide⟩
  m := 5
  T1 := T136_102
  T2 := Q2.T136_102_2
  h1 := (4,3,4,4,3)
  h2 := (4,3,4,4,4)
  D1 := [[4, 3, 2, 4], [4, 3, 2, 1], [4, 3, 2, 3], [4, 3, 2, 0], [4, 3, 2, 2]]
  D2 := [[4, 3, 2, 0], [4, 3, 2, 2], [4, 3, 2, 4], [4, 3, 2, 1], [4, 3, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_137_30_5 : ColCertDiv where
  rK := ⟨137, by decide⟩
  rH := ⟨30, by decide⟩
  m := 5
  T1 := T137_30
  T2 := Q2.T137_30_2
  h1 := (1,2,3,2,3)
  h2 := (1,2,3,2,0)
  D1 := [[1, 2, 1, 2], [1, 2, 1, 0], [1, 2, 1, 3], [1, 2, 1, 1], [1, 2, 1, 4]]
  D2 := [[1, 2, 1, 4], [1, 2, 1, 2], [1, 2, 1, 0], [1, 2, 1, 3], [1, 2, 1, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_137_30_10 : ColCertDiv where
  rK := ⟨137, by decide⟩
  rH := ⟨30, by decide⟩
  m := 5
  T1 := T137_30
  T2 := Q2.T137_30_2
  h1 := (2,4,1,1,4)
  h2 := (2,4,1,1,3)
  D1 := [[2, 4, 0, 2], [2, 4, 0, 3], [2, 4, 0, 4], [2, 4, 0, 0], [2, 4, 0, 1]]
  D2 := [[2, 4, 0, 1], [2, 4, 0, 2], [2, 4, 0, 3], [2, 4, 0, 4], [2, 4, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_137_30_15 : ColCertDiv where
  rK := ⟨137, by decide⟩
  rH := ⟨30, by decide⟩
  m := 5
  T1 := T137_30
  T2 := Q2.T137_30_2
  h1 := (3,1,4,2,1)
  h2 := (3,1,4,2,3)
  D1 := [[3, 1, 2, 3], [3, 1, 2, 2], [3, 1, 2, 1], [3, 1, 2, 0], [3, 1, 2, 4]]
  D2 := [[3, 1, 2, 0], [3, 1, 2, 4], [3, 1, 2, 3], [3, 1, 2, 2], [3, 1, 2, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_137_30_20 : ColCertDiv where
  rK := ⟨137, by decide⟩
  rH := ⟨30, by decide⟩
  m := 5
  T1 := T137_30
  T2 := Q2.T137_30_2
  h1 := (4,3,2,0,4)
  h2 := (4,3,2,0,3)
  D1 := [[4, 3, 2, 0], [4, 3, 2, 2], [4, 3, 2, 4], [4, 3, 2, 1], [4, 3, 2, 3]]
  D2 := [[4, 3, 2, 4], [4, 3, 2, 1], [4, 3, 2, 3], [4, 3, 2, 0], [4, 3, 2, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_137_37_5 : ColCertDiv where
  rK := ⟨137, by decide⟩
  rH := ⟨37, by decide⟩
  m := 5
  T1 := T137_37
  T2 := Q2.T137_37_2
  h1 := (1,1,2,4,3)
  h2 := (1,1,2,4,1)
  D1 := [[1, 1, 4, 2], [1, 1, 4, 1], [1, 1, 4, 0], [1, 1, 4, 4], [1, 1, 4, 3]]
  D2 := [[1, 1, 4, 0], [1, 1, 4, 4], [1, 1, 4, 3], [1, 1, 4, 2], [1, 1, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_137_37_10 : ColCertDiv where
  rK := ⟨137, by decide⟩
  rH := ⟨37, by decide⟩
  m := 5
  T1 := T137_37
  T2 := Q2.T137_37_2
  h1 := (2,2,4,4,2)
  h2 := (2,2,4,4,3)
  D1 := [[2, 2, 2, 2], [2, 2, 2, 0], [2, 2, 2, 3], [2, 2, 2, 1], [2, 2, 2, 4]]
  D2 := [[2, 2, 2, 3], [2, 2, 2, 1], [2, 2, 2, 4], [2, 2, 2, 2], [2, 2, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_137_37_15 : ColCertDiv where
  rK := ⟨137, by decide⟩
  rH := ⟨37, by decide⟩
  m := 5
  T1 := T137_37
  T2 := Q2.T137_37_2
  h1 := (3,3,1,0,3)
  h2 := (3,3,1,0,2)
  D1 := [[3, 3, 4, 1], [3, 3, 4, 3], [3, 3, 4, 0], [3, 3, 4, 2], [3, 3, 4, 4]]
  D2 := [[3, 3, 4, 0], [3, 3, 4, 2], [3, 3, 4, 4], [3, 3, 4, 1], [3, 3, 4, 3]]
  bind1 := by decide
  bind2 := by decide

end LeanDring.P5Presentation
