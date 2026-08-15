/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.Twin1.ColCert
import LeanDring.P5.Data.EntryK.C036

/-!
# Species-table cell data, stage 2 — column-data-divergent columns

Per-column certified exponent-vector data (`ColCert`/`ColCertDiv`) with kernel
`decide` bindings. Emitted; the embedded lists are what the kernel certifies.
cdd tier, chunk 15: 60 columns.
-/

-- machine-emitted data: silence style linters (generated long lines, file-level options)
set_option linter.style.longLine false

namespace LeanDring.P5Presentation

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

def colCertDiv_134_4_1 : ColCertDiv where
  rK := ⟨134, by decide⟩
  rH := ⟨4, by decide⟩
  m := 5
  T1 := T134_4
  T2 := Q2.T134_4_2
  h1 := (1,0,3,2,3)
  h2 := (1,0,3,2,3)
  D1 := [[1, 0, 1, 2], [1, 0, 1, 2], [1, 0, 1, 2], [1, 0, 1, 2], [1, 0, 1, 2]]
  D2 := [[1, 0, 1, 1], [1, 0, 1, 1], [1, 0, 1, 1], [1, 0, 1, 1], [1, 0, 1, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_134_4_2 : ColCertDiv where
  rK := ⟨134, by decide⟩
  rH := ⟨4, by decide⟩
  m := 5
  T1 := T134_4
  T2 := Q2.T134_4_2
  h1 := (2,0,1,4,3)
  h2 := (2,0,1,4,3)
  D1 := [[2, 0, 2, 3], [2, 0, 2, 3], [2, 0, 2, 3], [2, 0, 2, 3], [2, 0, 2, 3]]
  D2 := [[2, 0, 2, 1], [2, 0, 2, 1], [2, 0, 2, 1], [2, 0, 2, 1], [2, 0, 2, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_134_4_3 : ColCertDiv where
  rK := ⟨134, by decide⟩
  rH := ⟨4, by decide⟩
  m := 5
  T1 := T134_4
  T2 := Q2.T134_4_2
  h1 := (3,0,4,1,0)
  h2 := (3,0,4,1,0)
  D1 := [[3, 0, 3, 3], [3, 0, 3, 3], [3, 0, 3, 3], [3, 0, 3, 3], [3, 0, 3, 3]]
  D2 := [[3, 0, 3, 0], [3, 0, 3, 0], [3, 0, 3, 0], [3, 0, 3, 0], [3, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_134_4_4 : ColCertDiv where
  rK := ⟨134, by decide⟩
  rH := ⟨4, by decide⟩
  m := 5
  T1 := T134_4
  T2 := Q2.T134_4_2
  h1 := (4,0,2,3,4)
  h2 := (4,0,2,3,4)
  D1 := [[4, 0, 4, 2], [4, 0, 4, 2], [4, 0, 4, 2], [4, 0, 4, 2], [4, 0, 4, 2]]
  D2 := [[4, 0, 4, 3], [4, 0, 4, 3], [4, 0, 4, 3], [4, 0, 4, 3], [4, 0, 4, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_134_22_5 : ColCertDiv where
  rK := ⟨134, by decide⟩
  rH := ⟨22, by decide⟩
  m := 5
  T1 := T134_22
  T2 := Q2.T134_22_2
  h1 := (1,0,3,2,4)
  h2 := (1,0,3,2,4)
  D1 := [[1, 0, 1, 3], [1, 0, 1, 3], [1, 0, 1, 3], [1, 0, 1, 3], [1, 0, 1, 3]]
  D2 := [[1, 0, 1, 2], [1, 0, 1, 2], [1, 0, 1, 2], [1, 0, 1, 2], [1, 0, 1, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_134_22_10 : ColCertDiv where
  rK := ⟨134, by decide⟩
  rH := ⟨22, by decide⟩
  m := 5
  T1 := T134_22
  T2 := Q2.T134_22_2
  h1 := (2,0,1,4,0)
  h2 := (2,0,1,4,0)
  D1 := [[2, 0, 2, 0], [2, 0, 2, 0], [2, 0, 2, 0], [2, 0, 2, 0], [2, 0, 2, 0]]
  D2 := [[2, 0, 2, 3], [2, 0, 2, 3], [2, 0, 2, 3], [2, 0, 2, 3], [2, 0, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_134_22_15 : ColCertDiv where
  rK := ⟨134, by decide⟩
  rH := ⟨22, by decide⟩
  m := 5
  T1 := T134_22
  T2 := Q2.T134_22_2
  h1 := (3,0,4,1,3)
  h2 := (3,0,4,1,3)
  D1 := [[3, 0, 3, 1], [3, 0, 3, 1], [3, 0, 3, 1], [3, 0, 3, 1], [3, 0, 3, 1]]
  D2 := [[3, 0, 3, 3], [3, 0, 3, 3], [3, 0, 3, 3], [3, 0, 3, 3], [3, 0, 3, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_134_22_20 : ColCertDiv where
  rK := ⟨134, by decide⟩
  rH := ⟨22, by decide⟩
  m := 5
  T1 := T134_22
  T2 := Q2.T134_22_2
  h1 := (4,0,2,3,3)
  h2 := (4,0,2,3,3)
  D1 := [[4, 0, 4, 1], [4, 0, 4, 1], [4, 0, 4, 1], [4, 0, 4, 1], [4, 0, 4, 1]]
  D2 := [[4, 0, 4, 2], [4, 0, 4, 2], [4, 0, 4, 2], [4, 0, 4, 2], [4, 0, 4, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_134_37_5 : ColCertDiv where
  rK := ⟨134, by decide⟩
  rH := ⟨37, by decide⟩
  m := 5
  T1 := T134_37
  T2 := Q2.T134_37_2
  h1 := (1,1,2,4,3)
  h2 := (1,1,2,4,1)
  D1 := [[1, 1, 2, 2], [1, 1, 2, 1], [1, 1, 2, 0], [1, 1, 2, 4], [1, 1, 2, 3]]
  D2 := [[1, 1, 2, 1], [1, 1, 2, 0], [1, 1, 2, 4], [1, 1, 2, 3], [1, 1, 2, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_134_37_10 : ColCertDiv where
  rK := ⟨134, by decide⟩
  rH := ⟨37, by decide⟩
  m := 5
  T1 := T134_37
  T2 := Q2.T134_37_2
  h1 := (2,2,4,4,2)
  h2 := (2,2,4,4,3)
  D1 := [[2, 2, 3, 1], [2, 2, 3, 4], [2, 2, 3, 2], [2, 2, 3, 0], [2, 2, 3, 3]]
  D2 := [[2, 2, 3, 4], [2, 2, 3, 2], [2, 2, 3, 0], [2, 2, 3, 3], [2, 2, 3, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_134_37_15 : ColCertDiv where
  rK := ⟨134, by decide⟩
  rH := ⟨37, by decide⟩
  m := 5
  T1 := T134_37
  T2 := Q2.T134_37_2
  h1 := (3,3,1,0,3)
  h2 := (3,3,1,0,2)
  D1 := [[3, 3, 3, 3], [3, 3, 3, 0], [3, 3, 3, 2], [3, 3, 3, 4], [3, 3, 3, 1]]
  D2 := [[3, 3, 3, 0], [3, 3, 3, 2], [3, 3, 3, 4], [3, 3, 3, 1], [3, 3, 3, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_134_37_20 : ColCertDiv where
  rK := ⟨134, by decide⟩
  rH := ⟨37, by decide⟩
  m := 5
  T1 := T134_37
  T2 := Q2.T134_37_2
  h1 := (4,4,3,2,2)
  h2 := (4,4,3,2,4)
  D1 := [[4, 4, 2, 4], [4, 4, 2, 0], [4, 4, 2, 1], [4, 4, 2, 2], [4, 4, 2, 3]]
  D2 := [[4, 4, 2, 0], [4, 4, 2, 1], [4, 4, 2, 2], [4, 4, 2, 3], [4, 4, 2, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_134_40_15 : ColCertDiv where
  rK := ⟨134, by decide⟩
  rH := ⟨40, by decide⟩
  m := 5
  T1 := T134_40
  T2 := Q2.T134_40_2
  h1 := (3,1,3,2,2)
  h2 := (3,1,3,2,4)
  D1 := [[3, 1, 1, 4], [3, 1, 1, 3], [3, 1, 1, 2], [3, 1, 1, 1], [3, 1, 1, 0]]
  D2 := [[3, 1, 1, 0], [3, 1, 1, 4], [3, 1, 1, 3], [3, 1, 1, 2], [3, 1, 1, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_134_40_20 : ColCertDiv where
  rK := ⟨134, by decide⟩
  rH := ⟨40, by decide⟩
  m := 5
  T1 := T134_40
  T2 := Q2.T134_40_2
  h1 := (4,3,4,0,4)
  h2 := (4,3,4,0,3)
  D1 := [[4, 3, 4, 0], [4, 3, 4, 2], [4, 3, 4, 4], [4, 3, 4, 1], [4, 3, 4, 3]]
  D2 := [[4, 3, 4, 1], [4, 3, 4, 3], [4, 3, 4, 0], [4, 3, 4, 2], [4, 3, 4, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_134_44_5 : ColCertDiv where
  rK := ⟨134, by decide⟩
  rH := ⟨44, by decide⟩
  m := 5
  T1 := T134_44
  T2 := Q2.T134_44_2
  h1 := (1,4,4,3,0)
  h2 := (1,4,4,3,0)
  D1 := [[1, 4, 3, 2], [1, 4, 3, 3], [1, 4, 3, 4], [1, 4, 3, 0], [1, 4, 3, 1]]
  D2 := [[1, 4, 3, 4], [1, 4, 3, 0], [1, 4, 3, 1], [1, 4, 3, 2], [1, 4, 3, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_134_44_15 : ColCertDiv where
  rK := ⟨134, by decide⟩
  rH := ⟨44, by decide⟩
  m := 5
  T1 := T134_44
  T2 := Q2.T134_44_2
  h1 := (3,2,2,1,3)
  h2 := (3,2,2,1,0)
  D1 := [[3, 2, 2, 1], [3, 2, 2, 4], [3, 2, 2, 2], [3, 2, 2, 0], [3, 2, 2, 3]]
  D2 := [[3, 2, 2, 4], [3, 2, 2, 2], [3, 2, 2, 0], [3, 2, 2, 3], [3, 2, 2, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_134_44_20 : ColCertDiv where
  rK := ⟨134, by decide⟩
  rH := ⟨44, by decide⟩
  m := 5
  T1 := T134_44
  T2 := Q2.T134_44_2
  h1 := (4,1,1,1,3)
  h2 := (4,1,1,1,1)
  D1 := [[4, 1, 3, 0], [4, 1, 3, 4], [4, 1, 3, 3], [4, 1, 3, 2], [4, 1, 3, 1]]
  D2 := [[4, 1, 3, 1], [4, 1, 3, 0], [4, 1, 3, 4], [4, 1, 3, 3], [4, 1, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_134_51_5 : ColCertDiv where
  rK := ⟨134, by decide⟩
  rH := ⟨51, by decide⟩
  m := 5
  T1 := T134_51
  T2 := Q2.T134_51_2
  h1 := (1,3,0,0,3)
  h2 := (1,3,0,0,4)
  D1 := [[1, 3, 1, 3], [1, 3, 1, 0], [1, 3, 1, 2], [1, 3, 1, 4], [1, 3, 1, 1]]
  D2 := [[1, 3, 1, 4], [1, 3, 1, 1], [1, 3, 1, 3], [1, 3, 1, 0], [1, 3, 1, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_134_51_10 : ColCertDiv where
  rK := ⟨134, by decide⟩
  rH := ⟨51, by decide⟩
  m := 5
  T1 := T134_51
  T2 := Q2.T134_51_2
  h1 := (2,1,0,3,2)
  h2 := (2,1,0,3,0)
  D1 := [[2, 1, 4, 3], [2, 1, 4, 2], [2, 1, 4, 1], [2, 1, 4, 0], [2, 1, 4, 4]]
  D2 := [[2, 1, 4, 1], [2, 1, 4, 0], [2, 1, 4, 4], [2, 1, 4, 3], [2, 1, 4, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_134_51_15 : ColCertDiv where
  rK := ⟨134, by decide⟩
  rH := ⟨51, by decide⟩
  m := 5
  T1 := T134_51
  T2 := Q2.T134_51_2
  h1 := (3,4,0,4,3)
  h2 := (3,4,0,4,2)
  D1 := [[3, 4, 4, 1], [3, 4, 4, 2], [3, 4, 4, 3], [3, 4, 4, 4], [3, 4, 4, 0]]
  D2 := [[3, 4, 4, 0], [3, 4, 4, 1], [3, 4, 4, 2], [3, 4, 4, 3], [3, 4, 4, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_134_51_20 : ColCertDiv where
  rK := ⟨134, by decide⟩
  rH := ⟨51, by decide⟩
  m := 5
  T1 := T134_51
  T2 := Q2.T134_51_2
  h1 := (4,2,0,3,1)
  h2 := (4,2,0,3,2)
  D1 := [[4, 2, 1, 2], [4, 2, 1, 0], [4, 2, 1, 3], [4, 2, 1, 1], [4, 2, 1, 4]]
  D2 := [[4, 2, 1, 3], [4, 2, 1, 1], [4, 2, 1, 4], [4, 2, 1, 2], [4, 2, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_134_83_5 : ColCertDiv where
  rK := ⟨134, by decide⟩
  rH := ⟨83, by decide⟩
  m := 5
  T1 := T134_83
  T2 := Q2.T134_83_2
  h1 := (1,0,3,0,0)
  h2 := (1,0,3,0,0)
  D1 := [[1, 0, 4, 1], [1, 0, 4, 1], [1, 0, 4, 1], [1, 0, 4, 1], [1, 0, 4, 1]]
  D2 := [[1, 0, 4, 0], [1, 0, 4, 0], [1, 0, 4, 0], [1, 0, 4, 0], [1, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_134_83_10 : ColCertDiv where
  rK := ⟨134, by decide⟩
  rH := ⟨83, by decide⟩
  m := 5
  T1 := T134_83
  T2 := Q2.T134_83_2
  h1 := (2,0,1,0,0)
  h2 := (2,0,1,0,0)
  D1 := [[2, 0, 3, 3], [2, 0, 3, 3], [2, 0, 3, 3], [2, 0, 3, 3], [2, 0, 3, 3]]
  D2 := [[2, 0, 3, 1], [2, 0, 3, 1], [2, 0, 3, 1], [2, 0, 3, 1], [2, 0, 3, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_134_83_15 : ColCertDiv where
  rK := ⟨134, by decide⟩
  rH := ⟨83, by decide⟩
  m := 5
  T1 := T134_83
  T2 := Q2.T134_83_2
  h1 := (3,0,4,0,0)
  h2 := (3,0,4,0,0)
  D1 := [[3, 0, 2, 1], [3, 0, 2, 1], [3, 0, 2, 1], [3, 0, 2, 1], [3, 0, 2, 1]]
  D2 := [[3, 0, 2, 3], [3, 0, 2, 3], [3, 0, 2, 3], [3, 0, 2, 3], [3, 0, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_134_83_20 : ColCertDiv where
  rK := ⟨134, by decide⟩
  rH := ⟨83, by decide⟩
  m := 5
  T1 := T134_83
  T2 := Q2.T134_83_2
  h1 := (4,0,2,0,0)
  h2 := (4,0,2,0,0)
  D1 := [[4, 0, 1, 0], [4, 0, 1, 0], [4, 0, 1, 0], [4, 0, 1, 0], [4, 0, 1, 0]]
  D2 := [[4, 0, 1, 1], [4, 0, 1, 1], [4, 0, 1, 1], [4, 0, 1, 1], [4, 0, 1, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_134_90_25 : ColCertDiv where
  rK := ⟨134, by decide⟩
  rH := ⟨90, by decide⟩
  m := 5
  T1 := T134_90
  T2 := Q2.T134_90_2
  h1 := (0,1,4,0,0)
  h2 := (0,1,4,0,0)
  D1 := [[0, 1, 0, 1], [0, 1, 0, 0], [0, 1, 0, 4], [0, 1, 0, 3], [0, 1, 0, 2]]
  D2 := [[0, 1, 0, 3], [0, 1, 0, 2], [0, 1, 0, 1], [0, 1, 0, 0], [0, 1, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_134_90_50 : ColCertDiv where
  rK := ⟨134, by decide⟩
  rH := ⟨90, by decide⟩
  m := 5
  T1 := T134_90
  T2 := Q2.T134_90_2
  h1 := (0,2,3,0,4)
  h2 := (0,2,3,0,4)
  D1 := [[0, 2, 0, 2], [0, 2, 0, 0], [0, 2, 0, 3], [0, 2, 0, 1], [0, 2, 0, 4]]
  D2 := [[0, 2, 0, 1], [0, 2, 0, 4], [0, 2, 0, 2], [0, 2, 0, 0], [0, 2, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_134_90_75 : ColCertDiv where
  rK := ⟨134, by decide⟩
  rH := ⟨90, by decide⟩
  m := 5
  T1 := T134_90
  T2 := Q2.T134_90_2
  h1 := (0,3,2,0,2)
  h2 := (0,3,2,0,2)
  D1 := [[0, 3, 0, 3], [0, 3, 0, 0], [0, 3, 0, 2], [0, 3, 0, 4], [0, 3, 0, 1]]
  D2 := [[0, 3, 0, 4], [0, 3, 0, 1], [0, 3, 0, 3], [0, 3, 0, 0], [0, 3, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_134_90_100 : ColCertDiv where
  rK := ⟨134, by decide⟩
  rH := ⟨90, by decide⟩
  m := 5
  T1 := T134_90
  T2 := Q2.T134_90_2
  h1 := (0,4,1,0,4)
  h2 := (0,4,1,0,4)
  D1 := [[0, 4, 0, 4], [0, 4, 0, 0], [0, 4, 0, 1], [0, 4, 0, 2], [0, 4, 0, 3]]
  D2 := [[0, 4, 0, 2], [0, 4, 0, 3], [0, 4, 0, 4], [0, 4, 0, 0], [0, 4, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_134_99_5 : ColCertDiv where
  rK := ⟨134, by decide⟩
  rH := ⟨99, by decide⟩
  m := 5
  T1 := T134_99
  T2 := Q2.T134_99_2
  h1 := (1,1,2,0,0)
  h2 := (1,1,2,0,0)
  D1 := [[1, 1, 3, 3], [1, 1, 3, 2], [1, 1, 3, 1], [1, 1, 3, 0], [1, 1, 3, 4]]
  D2 := [[1, 1, 3, 4], [1, 1, 3, 3], [1, 1, 3, 2], [1, 1, 3, 1], [1, 1, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_134_99_10 : ColCertDiv where
  rK := ⟨134, by decide⟩
  rH := ⟨99, by decide⟩
  m := 5
  T1 := T134_99
  T2 := Q2.T134_99_2
  h1 := (2,2,4,1,2)
  h2 := (2,2,4,1,2)
  D1 := [[2, 2, 0, 2], [2, 2, 0, 0], [2, 2, 0, 3], [2, 2, 0, 1], [2, 2, 0, 4]]
  D2 := [[2, 2, 0, 4], [2, 2, 0, 2], [2, 2, 0, 0], [2, 2, 0, 3], [2, 2, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_134_99_15 : ColCertDiv where
  rK := ⟨134, by decide⟩
  rH := ⟨99, by decide⟩
  m := 5
  T1 := T134_99
  T2 := Q2.T134_99_2
  h1 := (3,3,1,3,2)
  h2 := (3,3,1,3,2)
  D1 := [[3, 3, 1, 3], [3, 3, 1, 0], [3, 3, 1, 2], [3, 3, 1, 4], [3, 3, 1, 1]]
  D2 := [[3, 3, 1, 1], [3, 3, 1, 3], [3, 3, 1, 0], [3, 3, 1, 2], [3, 3, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_134_99_20 : ColCertDiv where
  rK := ⟨134, by decide⟩
  rH := ⟨99, by decide⟩
  m := 5
  T1 := T134_99
  T2 := Q2.T134_99_2
  h1 := (4,4,3,1,1)
  h2 := (4,4,3,1,1)
  D1 := [[4, 4, 1, 2], [4, 4, 1, 3], [4, 4, 1, 4], [4, 4, 1, 0], [4, 4, 1, 1]]
  D2 := [[4, 4, 1, 1], [4, 4, 1, 2], [4, 4, 1, 3], [4, 4, 1, 4], [4, 4, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_134_102_5 : ColCertDiv where
  rK := ⟨134, by decide⟩
  rH := ⟨102, by decide⟩
  m := 5
  T1 := T134_102
  T2 := Q2.T134_102_2
  h1 := (1,2,1,3,1)
  h2 := (1,2,1,3,1)
  D1 := [[1, 2, 0, 4], [1, 2, 0, 2], [1, 2, 0, 0], [1, 2, 0, 3], [1, 2, 0, 1]]
  D2 := [[1, 2, 0, 2], [1, 2, 0, 0], [1, 2, 0, 3], [1, 2, 0, 1], [1, 2, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_134_102_10 : ColCertDiv where
  rK := ⟨134, by decide⟩
  rH := ⟨102, by decide⟩
  m := 5
  T1 := T134_102
  T2 := Q2.T134_102_2
  h1 := (2,4,2,3,2)
  h2 := (2,4,2,3,2)
  D1 := [[2, 4, 3, 1], [2, 4, 3, 2], [2, 4, 3, 3], [2, 4, 3, 4], [2, 4, 3, 0]]
  D2 := [[2, 4, 3, 2], [2, 4, 3, 3], [2, 4, 3, 4], [2, 4, 3, 0], [2, 4, 3, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_134_102_20 : ColCertDiv where
  rK := ⟨134, by decide⟩
  rH := ⟨102, by decide⟩
  m := 5
  T1 := T134_102
  T2 := Q2.T134_102_2
  h1 := (4,3,4,4,3)
  h2 := (4,3,4,4,4)
  D1 := [[4, 3, 3, 3], [4, 3, 3, 0], [4, 3, 3, 2], [4, 3, 3, 4], [4, 3, 3, 1]]
  D2 := [[4, 3, 3, 1], [4, 3, 3, 3], [4, 3, 3, 0], [4, 3, 3, 2], [4, 3, 3, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_134_106_5 : ColCertDiv where
  rK := ⟨134, by decide⟩
  rH := ⟨106, by decide⟩
  m := 5
  T1 := T134_106
  T2 := Q2.T134_106_2
  h1 := (1,4,4,4,1)
  h2 := (1,4,4,4,1)
  D1 := [[1, 4, 4, 2], [1, 4, 4, 3], [1, 4, 4, 4], [1, 4, 4, 0], [1, 4, 4, 1]]
  D2 := [[1, 4, 4, 4], [1, 4, 4, 0], [1, 4, 4, 1], [1, 4, 4, 2], [1, 4, 4, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_134_106_15 : ColCertDiv where
  rK := ⟨134, by decide⟩
  rH := ⟨106, by decide⟩
  m := 5
  T1 := T134_106
  T2 := Q2.T134_106_2
  h1 := (3,2,2,4,4)
  h2 := (3,2,2,4,1)
  D1 := [[3, 2, 0, 3], [3, 2, 0, 1], [3, 2, 0, 4], [3, 2, 0, 2], [3, 2, 0, 0]]
  D2 := [[3, 2, 0, 1], [3, 2, 0, 4], [3, 2, 0, 2], [3, 2, 0, 0], [3, 2, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_134_106_20 : ColCertDiv where
  rK := ⟨134, by decide⟩
  rH := ⟨106, by decide⟩
  m := 5
  T1 := T134_106
  T2 := Q2.T134_106_2
  h1 := (4,1,1,0,3)
  h2 := (4,1,1,0,1)
  D1 := [[4, 1, 2, 4], [4, 1, 2, 3], [4, 1, 2, 2], [4, 1, 2, 1], [4, 1, 2, 0]]
  D2 := [[4, 1, 2, 0], [4, 1, 2, 4], [4, 1, 2, 3], [4, 1, 2, 2], [4, 1, 2, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_134_113_10 : ColCertDiv where
  rK := ⟨134, by decide⟩
  rH := ⟨113, by decide⟩
  m := 5
  T1 := T134_113
  T2 := Q2.T134_113_2
  h1 := (2,1,0,0,1)
  h2 := (2,1,0,0,2)
  D1 := [[2, 1, 1, 3], [2, 1, 1, 2], [2, 1, 1, 1], [2, 1, 1, 0], [2, 1, 1, 4]]
  D2 := [[2, 1, 1, 4], [2, 1, 1, 3], [2, 1, 1, 2], [2, 1, 1, 1], [2, 1, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_134_113_15 : ColCertDiv where
  rK := ⟨134, by decide⟩
  rH := ⟨113, by decide⟩
  m := 5
  T1 := T134_113
  T2 := Q2.T134_113_2
  h1 := (3,4,0,2,3)
  h2 := (3,4,0,2,4)
  D1 := [[3, 4, 2, 2], [3, 4, 2, 3], [3, 4, 2, 4], [3, 4, 2, 0], [3, 4, 2, 1]]
  D2 := [[3, 4, 2, 3], [3, 4, 2, 4], [3, 4, 2, 0], [3, 4, 2, 1], [3, 4, 2, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_134_113_20 : ColCertDiv where
  rK := ⟨134, by decide⟩
  rH := ⟨113, by decide⟩
  m := 5
  T1 := T134_113
  T2 := Q2.T134_113_2
  h1 := (4,2,0,2,3)
  h2 := (4,2,0,2,0)
  D1 := [[4, 2, 0, 3], [4, 2, 0, 1], [4, 2, 0, 4], [4, 2, 0, 2], [4, 2, 0, 0]]
  D2 := [[4, 2, 0, 0], [4, 2, 0, 3], [4, 2, 0, 1], [4, 2, 0, 4], [4, 2, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_135_4_1 : ColCertDiv where
  rK := ⟨135, by decide⟩
  rH := ⟨4, by decide⟩
  m := 5
  T1 := T135_4
  T2 := Q2.T135_4_2
  h1 := (1,0,3,2,3)
  h2 := (1,0,3,2,3)
  D1 := [[1, 0, 2, 3], [1, 0, 2, 3], [1, 0, 2, 3], [1, 0, 2, 3], [1, 0, 2, 3]]
  D2 := [[1, 0, 2, 4], [1, 0, 2, 4], [1, 0, 2, 4], [1, 0, 2, 4], [1, 0, 2, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_135_4_2 : ColCertDiv where
  rK := ⟨135, by decide⟩
  rH := ⟨4, by decide⟩
  m := 5
  T1 := T135_4
  T2 := Q2.T135_4_2
  h1 := (2,0,1,4,3)
  h2 := (2,0,1,4,3)
  D1 := [[2, 0, 4, 4], [2, 0, 4, 4], [2, 0, 4, 4], [2, 0, 4, 4], [2, 0, 4, 4]]
  D2 := [[2, 0, 4, 1], [2, 0, 4, 1], [2, 0, 4, 1], [2, 0, 4, 1], [2, 0, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_135_4_3 : ColCertDiv where
  rK := ⟨135, by decide⟩
  rH := ⟨4, by decide⟩
  m := 5
  T1 := T135_4
  T2 := Q2.T135_4_2
  h1 := (3,0,4,1,0)
  h2 := (3,0,4,1,0)
  D1 := [[3, 0, 1, 3], [3, 0, 1, 3], [3, 0, 1, 3], [3, 0, 1, 3], [3, 0, 1, 3]]
  D2 := [[3, 0, 1, 1], [3, 0, 1, 1], [3, 0, 1, 1], [3, 0, 1, 1], [3, 0, 1, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_135_4_4 : ColCertDiv where
  rK := ⟨135, by decide⟩
  rH := ⟨4, by decide⟩
  m := 5
  T1 := T135_4
  T2 := Q2.T135_4_2
  h1 := (4,0,2,3,4)
  h2 := (4,0,2,3,4)
  D1 := [[4, 0, 3, 0], [4, 0, 3, 0], [4, 0, 3, 0], [4, 0, 3, 0], [4, 0, 3, 0]]
  D2 := [[4, 0, 3, 4], [4, 0, 3, 4], [4, 0, 3, 4], [4, 0, 3, 4], [4, 0, 3, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_135_22_5 : ColCertDiv where
  rK := ⟨135, by decide⟩
  rH := ⟨22, by decide⟩
  m := 5
  T1 := T135_22
  T2 := Q2.T135_22_2
  h1 := (1,0,3,2,4)
  h2 := (1,0,3,2,4)
  D1 := [[1, 0, 2, 4], [1, 0, 2, 4], [1, 0, 2, 4], [1, 0, 2, 4], [1, 0, 2, 4]]
  D2 := [[1, 0, 2, 0], [1, 0, 2, 0], [1, 0, 2, 0], [1, 0, 2, 0], [1, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_135_22_10 : ColCertDiv where
  rK := ⟨135, by decide⟩
  rH := ⟨22, by decide⟩
  m := 5
  T1 := T135_22
  T2 := Q2.T135_22_2
  h1 := (2,0,1,4,0)
  h2 := (2,0,1,4,0)
  D1 := [[2, 0, 4, 1], [2, 0, 4, 1], [2, 0, 4, 1], [2, 0, 4, 1], [2, 0, 4, 1]]
  D2 := [[2, 0, 4, 3], [2, 0, 4, 3], [2, 0, 4, 3], [2, 0, 4, 3], [2, 0, 4, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_135_22_15 : ColCertDiv where
  rK := ⟨135, by decide⟩
  rH := ⟨22, by decide⟩
  m := 5
  T1 := T135_22
  T2 := Q2.T135_22_2
  h1 := (3,0,4,1,3)
  h2 := (3,0,4,1,3)
  D1 := [[3, 0, 1, 1], [3, 0, 1, 1], [3, 0, 1, 1], [3, 0, 1, 1], [3, 0, 1, 1]]
  D2 := [[3, 0, 1, 4], [3, 0, 1, 4], [3, 0, 1, 4], [3, 0, 1, 4], [3, 0, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_135_22_20 : ColCertDiv where
  rK := ⟨135, by decide⟩
  rH := ⟨22, by decide⟩
  m := 5
  T1 := T135_22
  T2 := Q2.T135_22_2
  h1 := (4,0,2,3,3)
  h2 := (4,0,2,3,3)
  D1 := [[4, 0, 3, 4], [4, 0, 3, 4], [4, 0, 3, 4], [4, 0, 3, 4], [4, 0, 3, 4]]
  D2 := [[4, 0, 3, 3], [4, 0, 3, 3], [4, 0, 3, 3], [4, 0, 3, 3], [4, 0, 3, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_135_29_5 : ColCertDiv where
  rK := ⟨135, by decide⟩
  rH := ⟨29, by decide⟩
  m := 5
  T1 := T135_29
  T2 := Q2.T135_29_2
  h1 := (1,4,1,3,3)
  h2 := (1,4,1,3,3)
  D1 := [[1, 4, 4, 3], [1, 4, 4, 4], [1, 4, 4, 0], [1, 4, 4, 1], [1, 4, 4, 2]]
  D2 := [[1, 4, 4, 0], [1, 4, 4, 1], [1, 4, 4, 2], [1, 4, 4, 3], [1, 4, 4, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_135_29_15 : ColCertDiv where
  rK := ⟨135, by decide⟩
  rH := ⟨29, by decide⟩
  m := 5
  T1 := T135_29
  T2 := Q2.T135_29_2
  h1 := (3,2,3,1,1)
  h2 := (3,2,3,1,3)
  D1 := [[3, 2, 0, 1], [3, 2, 0, 4], [3, 2, 0, 2], [3, 2, 0, 0], [3, 2, 0, 3]]
  D2 := [[3, 2, 0, 4], [3, 2, 0, 2], [3, 2, 0, 0], [3, 2, 0, 3], [3, 2, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_135_29_20 : ColCertDiv where
  rK := ⟨135, by decide⟩
  rH := ⟨29, by decide⟩
  m := 5
  T1 := T135_29
  T2 := Q2.T135_29_2
  h1 := (4,1,4,1,3)
  h2 := (4,1,4,1,1)
  D1 := [[4, 1, 2, 3], [4, 1, 2, 2], [4, 1, 2, 1], [4, 1, 2, 0], [4, 1, 2, 4]]
  D2 := [[4, 1, 2, 4], [4, 1, 2, 3], [4, 1, 2, 2], [4, 1, 2, 1], [4, 1, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_135_33_5 : ColCertDiv where
  rK := ⟨135, by decide⟩
  rH := ⟨33, by decide⟩
  m := 5
  T1 := T135_33
  T2 := Q2.T135_33_2
  h1 := (0,1,2,4,0)
  h2 := (0,1,2,4,3)
  D1 := [[0, 1, 4, 1], [0, 1, 4, 0], [0, 1, 4, 4], [0, 1, 4, 3], [0, 1, 4, 2]]
  D2 := [[0, 1, 4, 3], [0, 1, 4, 2], [0, 1, 4, 1], [0, 1, 4, 0], [0, 1, 4, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_135_33_10 : ColCertDiv where
  rK := ⟨135, by decide⟩
  rH := ⟨33, by decide⟩
  m := 5
  T1 := T135_33
  T2 := Q2.T135_33_2
  h1 := (0,2,4,3,2)
  h2 := (0,2,4,3,3)
  D1 := [[0, 2, 3, 2], [0, 2, 3, 0], [0, 2, 3, 3], [0, 2, 3, 1], [0, 2, 3, 4]]
  D2 := [[0, 2, 3, 1], [0, 2, 3, 4], [0, 2, 3, 2], [0, 2, 3, 0], [0, 2, 3, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_135_33_15 : ColCertDiv where
  rK := ⟨135, by decide⟩
  rH := ⟨33, by decide⟩
  m := 5
  T1 := T135_33
  T2 := Q2.T135_33_2
  h1 := (0,3,1,2,1)
  h2 := (0,3,1,2,0)
  D1 := [[0, 3, 2, 3], [0, 3, 2, 0], [0, 3, 2, 2], [0, 3, 2, 4], [0, 3, 2, 1]]
  D2 := [[0, 3, 2, 4], [0, 3, 2, 1], [0, 3, 2, 3], [0, 3, 2, 0], [0, 3, 2, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_135_33_20 : ColCertDiv where
  rK := ⟨135, by decide⟩
  rH := ⟨33, by decide⟩
  m := 5
  T1 := T135_33
  T2 := Q2.T135_33_2
  h1 := (0,4,3,1,2)
  h2 := (0,4,3,1,4)
  D1 := [[0, 4, 1, 4], [0, 4, 1, 0], [0, 4, 1, 1], [0, 4, 1, 2], [0, 4, 1, 3]]
  D2 := [[0, 4, 1, 2], [0, 4, 1, 3], [0, 4, 1, 4], [0, 4, 1, 0], [0, 4, 1, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_135_41_5 : ColCertDiv where
  rK := ⟨135, by decide⟩
  rH := ⟨41, by decide⟩
  m := 5
  T1 := T135_41
  T2 := Q2.T135_41_2
  h1 := (1,3,4,0,0)
  h2 := (1,3,4,0,1)
  D1 := [[1, 3, 2, 2], [1, 3, 2, 4], [1, 3, 2, 1], [1, 3, 2, 3], [1, 3, 2, 0]]
  D2 := [[1, 3, 2, 1], [1, 3, 2, 3], [1, 3, 2, 0], [1, 3, 2, 2], [1, 3, 2, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_135_41_10 : ColCertDiv where
  rK := ⟨135, by decide⟩
  rH := ⟨41, by decide⟩
  m := 5
  T1 := T135_41
  T2 := Q2.T135_41_2
  h1 := (2,1,3,3,3)
  h2 := (2,1,3,3,1)
  D1 := [[2, 1, 1, 0], [2, 1, 1, 4], [2, 1, 1, 3], [2, 1, 1, 2], [2, 1, 1, 1]]
  D2 := [[2, 1, 1, 4], [2, 1, 1, 3], [2, 1, 1, 2], [2, 1, 1, 1], [2, 1, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_135_41_15 : ColCertDiv where
  rK := ⟨135, by decide⟩
  rH := ⟨41, by decide⟩
  m := 5
  T1 := T135_41
  T2 := Q2.T135_41_2
  h1 := (3,4,2,4,0)
  h2 := (3,4,2,4,4)
  D1 := [[3, 4, 2, 0], [3, 4, 2, 1], [3, 4, 2, 2], [3, 4, 2, 3], [3, 4, 2, 4]]
  D2 := [[3, 4, 2, 3], [3, 4, 2, 4], [3, 4, 2, 0], [3, 4, 2, 1], [3, 4, 2, 2]]
  bind1 := by decide
  bind2 := by decide

end LeanDring.P5Presentation
