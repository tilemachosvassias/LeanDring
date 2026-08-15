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
cdd tier, chunk 23: 60 columns.
-/

-- machine-emitted data: silence style linters (generated long lines, file-level options)
set_option linter.style.longLine false

namespace LeanDring.P5Presentation

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

def colCertDiv_147_44_15 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨44, by decide⟩
  m := 1
  T1 := T147_44
  T2 := Q2.T147_44_2
  h1 := (3,2,2,1,3)
  h2 := (3,2,2,1,0)
  D1 := [[3, 2, 2, 0, 3]]
  D2 := [[3, 2, 2, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_44_20 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨44, by decide⟩
  m := 1
  T1 := T147_44
  T2 := Q2.T147_44_2
  h1 := (4,1,1,1,3)
  h2 := (4,1,1,1,1)
  D1 := [[4, 1, 1, 2, 3]]
  D2 := [[4, 1, 1, 2, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_45_5 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨45, by decide⟩
  m := 1
  T1 := T147_45
  T2 := Q2.T147_45_2
  h1 := (1,2,2,2,1)
  h2 := (1,2,2,2,3)
  D1 := [[1, 2, 2, 0, 2]]
  D2 := [[1, 2, 2, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_45_10 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨45, by decide⟩
  m := 1
  T1 := T147_45
  T2 := Q2.T147_45_2
  h1 := (2,4,4,1,3)
  h2 := (2,4,4,1,2)
  D1 := [[2, 4, 4, 3, 2]]
  D2 := [[2, 4, 4, 3, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_45_15 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨45, by decide⟩
  m := 1
  T1 := T147_45
  T2 := Q2.T147_45_2
  h1 := (3,1,1,2,4)
  h2 := (3,1,1,2,1)
  D1 := [[3, 1, 1, 4, 3]]
  D2 := [[3, 1, 1, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_45_20 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨45, by decide⟩
  m := 1
  T1 := T147_45
  T2 := Q2.T147_45_2
  h1 := (4,3,3,0,4)
  h2 := (4,3,3,0,3)
  D1 := [[4, 3, 3, 3, 0]]
  D2 := [[4, 3, 3, 3, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_46_5 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨46, by decide⟩
  m := 1
  T1 := T147_46
  T2 := Q2.T147_46_2
  h1 := (1,3,3,0,2)
  h2 := (1,3,3,0,3)
  D1 := [[1, 3, 3, 2, 1]]
  D2 := [[1, 3, 3, 2, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_46_10 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨46, by decide⟩
  m := 1
  T1 := T147_46
  T2 := Q2.T147_46_2
  h1 := (2,1,1,3,4)
  h2 := (2,1,1,3,2)
  D1 := [[2, 1, 1, 1, 0]]
  D2 := [[2, 1, 1, 1, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_46_15 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨46, by decide⟩
  m := 1
  T1 := T147_46
  T2 := Q2.T147_46_2
  h1 := (3,4,4,4,2)
  h2 := (3,4,4,4,1)
  D1 := [[3, 4, 4, 2, 3]]
  D2 := [[3, 4, 4, 2, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_46_20 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨46, by decide⟩
  m := 1
  T1 := T147_46
  T2 := Q2.T147_46_2
  h1 := (4,2,2,3,1)
  h2 := (4,2,2,3,2)
  D1 := [[4, 2, 2, 0, 0]]
  D2 := [[4, 2, 2, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_47_5 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨47, by decide⟩
  m := 1
  T1 := T147_47
  T2 := Q2.T147_47_2
  h1 := (1,1,1,4,2)
  h2 := (1,1,1,4,0)
  D1 := [[1, 1, 1, 3, 3]]
  D2 := [[1, 1, 1, 3, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_47_10 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨47, by decide⟩
  m := 1
  T1 := T147_47
  T2 := Q2.T147_47_2
  h1 := (2,2,2,4,4)
  h2 := (2,2,2,4,0)
  D1 := [[2, 2, 2, 0, 3]]
  D2 := [[2, 2, 2, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_47_15 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨47, by decide⟩
  m := 1
  T1 := T147_47
  T2 := Q2.T147_47_2
  h1 := (3,3,3,0,2)
  h2 := (3,3,3,0,1)
  D1 := [[3, 3, 3, 1, 1]]
  D2 := [[3, 3, 3, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_47_20 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨47, by decide⟩
  m := 1
  T1 := T147_47
  T2 := Q2.T147_47_2
  h1 := (4,4,4,2,2)
  h2 := (4,4,4,2,4)
  D1 := [[4, 4, 4, 1, 3]]
  D2 := [[4, 4, 4, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_48_5 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨48, by decide⟩
  m := 1
  T1 := T147_48
  T2 := Q2.T147_48_2
  h1 := (0,1,0,4,3)
  h2 := (0,1,0,4,1)
  D1 := [[0, 1, 0, 4, 3]]
  D2 := [[0, 1, 0, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_48_10 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨48, by decide⟩
  m := 1
  T1 := T147_48
  T2 := Q2.T147_48_2
  h1 := (0,2,0,3,1)
  h2 := (0,2,0,3,2)
  D1 := [[0, 2, 0, 3, 1]]
  D2 := [[0, 2, 0, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_48_15 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨48, by decide⟩
  m := 1
  T1 := T147_48
  T2 := Q2.T147_48_2
  h1 := (0,3,0,2,4)
  h2 := (0,3,0,2,3)
  D1 := [[0, 3, 0, 2, 4]]
  D2 := [[0, 3, 0, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_48_20 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨48, by decide⟩
  m := 1
  T1 := T147_48
  T2 := Q2.T147_48_2
  h1 := (0,4,0,1,2)
  h2 := (0,4,0,1,4)
  D1 := [[0, 4, 0, 1, 2]]
  D2 := [[0, 4, 0, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_49_10 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨49, by decide⟩
  m := 1
  T1 := T147_49
  T2 := Q2.T147_49_2
  h1 := (2,3,0,0,2)
  h2 := (2,3,0,0,3)
  D1 := [[2, 3, 0, 4, 1]]
  D2 := [[2, 3, 0, 4, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_49_15 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨49, by decide⟩
  m := 1
  T1 := T147_49
  T2 := Q2.T147_49_2
  h1 := (3,2,0,1,2)
  h2 := (3,2,0,1,4)
  D1 := [[3, 2, 0, 0, 1]]
  D2 := [[3, 2, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_49_20 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨49, by decide⟩
  m := 1
  T1 := T147_49
  T2 := Q2.T147_49_2
  h1 := (4,1,0,1,3)
  h2 := (4,1,0,1,1)
  D1 := [[4, 1, 0, 2, 4]]
  D2 := [[4, 1, 0, 2, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_50_5 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨50, by decide⟩
  m := 1
  T1 := T147_50
  T2 := Q2.T147_50_2
  h1 := (1,2,0,2,2)
  h2 := (1,2,0,2,4)
  D1 := [[1, 2, 0, 0, 2]]
  D2 := [[1, 2, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_50_10 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨50, by decide⟩
  m := 1
  T1 := T147_50
  T2 := Q2.T147_50_2
  h1 := (2,4,0,1,1)
  h2 := (2,4,0,1,0)
  D1 := [[2, 4, 0, 3, 1]]
  D2 := [[2, 4, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_50_15 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨50, by decide⟩
  m := 1
  T1 := T147_50
  T2 := Q2.T147_50_2
  h1 := (3,1,0,2,0)
  h2 := (3,1,0,2,2)
  D1 := [[3, 1, 0, 4, 0]]
  D2 := [[3, 1, 0, 4, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_50_20 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨50, by decide⟩
  m := 1
  T1 := T147_50
  T2 := Q2.T147_50_2
  h1 := (4,3,0,0,4)
  h2 := (4,3,0,0,3)
  D1 := [[4, 3, 0, 3, 4]]
  D2 := [[4, 3, 0, 3, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_51_5 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨51, by decide⟩
  m := 1
  T1 := T147_51
  T2 := Q2.T147_51_2
  h1 := (1,3,0,0,3)
  h2 := (1,3,0,0,4)
  D1 := [[1, 3, 0, 2, 1]]
  D2 := [[1, 3, 0, 2, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_51_10 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨51, by decide⟩
  m := 1
  T1 := T147_51
  T2 := Q2.T147_51_2
  h1 := (2,1,0,3,2)
  h2 := (2,1,0,3,0)
  D1 := [[2, 1, 0, 1, 4]]
  D2 := [[2, 1, 0, 1, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_51_15 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨51, by decide⟩
  m := 1
  T1 := T147_51
  T2 := Q2.T147_51_2
  h1 := (3,4,0,4,3)
  h2 := (3,4,0,4,2)
  D1 := [[3, 4, 0, 2, 0]]
  D2 := [[3, 4, 0, 2, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_51_20 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨51, by decide⟩
  m := 1
  T1 := T147_51
  T2 := Q2.T147_51_2
  h1 := (4,2,0,3,1)
  h2 := (4,2,0,3,2)
  D1 := [[4, 2, 0, 0, 4]]
  D2 := [[4, 2, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_52_5 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨52, by decide⟩
  m := 1
  T1 := T147_52
  T2 := Q2.T147_52_2
  h1 := (1,1,0,4,1)
  h2 := (1,1,0,4,4)
  D1 := [[1, 1, 0, 3, 3]]
  D2 := [[1, 1, 0, 3, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_52_10 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨52, by decide⟩
  m := 1
  T1 := T147_52
  T2 := Q2.T147_52_2
  h1 := (2,2,0,4,1)
  h2 := (2,2,0,4,2)
  D1 := [[2, 2, 0, 0, 4]]
  D2 := [[2, 2, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_52_15 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨52, by decide⟩
  m := 1
  T1 := T147_52
  T2 := Q2.T147_52_2
  h1 := (3,3,0,0,1)
  h2 := (3,3,0,0,0)
  D1 := [[3, 3, 0, 1, 4]]
  D2 := [[3, 3, 0, 1, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_52_20 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨52, by decide⟩
  m := 1
  T1 := T147_52
  T2 := Q2.T147_52_2
  h1 := (4,4,0,2,2)
  h2 := (4,4,0,2,4)
  D1 := [[4, 4, 0, 1, 4]]
  D2 := [[4, 4, 0, 1, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_55_5 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨55, by decide⟩
  m := 1
  T1 := T147_55
  T2 := Q2.T147_55_2
  h1 := (0,1,0,4,3)
  h2 := (0,1,0,4,1)
  D1 := [[0, 1, 0, 4, 3]]
  D2 := [[0, 1, 0, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_55_6 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨55, by decide⟩
  m := 1
  T1 := T147_55
  T2 := Q2.T147_55_2
  h1 := (0,1,1,4,3)
  h2 := (0,1,1,4,1)
  D1 := [[0, 1, 1, 4, 2]]
  D2 := [[0, 1, 1, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_55_7 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨55, by decide⟩
  m := 1
  T1 := T147_55
  T2 := Q2.T147_55_2
  h1 := (0,1,2,4,3)
  h2 := (0,1,2,4,1)
  D1 := [[0, 1, 2, 4, 1]]
  D2 := [[0, 1, 2, 4, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_55_8 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨55, by decide⟩
  m := 1
  T1 := T147_55
  T2 := Q2.T147_55_2
  h1 := (0,1,3,4,3)
  h2 := (0,1,3,4,1)
  D1 := [[0, 1, 3, 4, 0]]
  D2 := [[0, 1, 3, 4, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_55_9 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨55, by decide⟩
  m := 1
  T1 := T147_55
  T2 := Q2.T147_55_2
  h1 := (0,1,4,4,3)
  h2 := (0,1,4,4,1)
  D1 := [[0, 1, 4, 4, 4]]
  D2 := [[0, 1, 4, 4, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_55_10 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨55, by decide⟩
  m := 1
  T1 := T147_55
  T2 := Q2.T147_55_2
  h1 := (0,2,0,3,1)
  h2 := (0,2,0,3,2)
  D1 := [[0, 2, 0, 3, 1]]
  D2 := [[0, 2, 0, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_55_11 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨55, by decide⟩
  m := 1
  T1 := T147_55
  T2 := Q2.T147_55_2
  h1 := (0,2,1,3,1)
  h2 := (0,2,1,3,2)
  D1 := [[0, 2, 1, 3, 4]]
  D2 := [[0, 2, 1, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_55_12 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨55, by decide⟩
  m := 1
  T1 := T147_55
  T2 := Q2.T147_55_2
  h1 := (0,2,2,3,1)
  h2 := (0,2,2,3,2)
  D1 := [[0, 2, 2, 3, 2]]
  D2 := [[0, 2, 2, 3, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_55_13 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨55, by decide⟩
  m := 1
  T1 := T147_55
  T2 := Q2.T147_55_2
  h1 := (0,2,3,3,1)
  h2 := (0,2,3,3,2)
  D1 := [[0, 2, 3, 3, 0]]
  D2 := [[0, 2, 3, 3, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_55_14 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨55, by decide⟩
  m := 1
  T1 := T147_55
  T2 := Q2.T147_55_2
  h1 := (0,2,4,3,1)
  h2 := (0,2,4,3,2)
  D1 := [[0, 2, 4, 3, 3]]
  D2 := [[0, 2, 4, 3, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_55_15 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨55, by decide⟩
  m := 1
  T1 := T147_55
  T2 := Q2.T147_55_2
  h1 := (0,3,0,2,4)
  h2 := (0,3,0,2,3)
  D1 := [[0, 3, 0, 2, 4]]
  D2 := [[0, 3, 0, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_55_16 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨55, by decide⟩
  m := 1
  T1 := T147_55
  T2 := Q2.T147_55_2
  h1 := (0,3,1,2,4)
  h2 := (0,3,1,2,3)
  D1 := [[0, 3, 1, 2, 1]]
  D2 := [[0, 3, 1, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_55_17 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨55, by decide⟩
  m := 1
  T1 := T147_55
  T2 := Q2.T147_55_2
  h1 := (0,3,2,2,4)
  h2 := (0,3,2,2,3)
  D1 := [[0, 3, 2, 2, 3]]
  D2 := [[0, 3, 2, 2, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_55_18 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨55, by decide⟩
  m := 1
  T1 := T147_55
  T2 := Q2.T147_55_2
  h1 := (0,3,3,2,4)
  h2 := (0,3,3,2,3)
  D1 := [[0, 3, 3, 2, 0]]
  D2 := [[0, 3, 3, 2, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_55_19 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨55, by decide⟩
  m := 1
  T1 := T147_55
  T2 := Q2.T147_55_2
  h1 := (0,3,4,2,4)
  h2 := (0,3,4,2,3)
  D1 := [[0, 3, 4, 2, 2]]
  D2 := [[0, 3, 4, 2, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_55_20 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨55, by decide⟩
  m := 1
  T1 := T147_55
  T2 := Q2.T147_55_2
  h1 := (0,4,0,1,2)
  h2 := (0,4,0,1,4)
  D1 := [[0, 4, 0, 1, 2]]
  D2 := [[0, 4, 0, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_55_21 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨55, by decide⟩
  m := 1
  T1 := T147_55
  T2 := Q2.T147_55_2
  h1 := (0,4,1,1,2)
  h2 := (0,4,1,1,4)
  D1 := [[0, 4, 1, 1, 3]]
  D2 := [[0, 4, 1, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_55_22 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨55, by decide⟩
  m := 1
  T1 := T147_55
  T2 := Q2.T147_55_2
  h1 := (0,4,2,1,2)
  h2 := (0,4,2,1,4)
  D1 := [[0, 4, 2, 1, 4]]
  D2 := [[0, 4, 2, 1, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_55_23 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨55, by decide⟩
  m := 1
  T1 := T147_55
  T2 := Q2.T147_55_2
  h1 := (0,4,3,1,2)
  h2 := (0,4,3,1,4)
  D1 := [[0, 4, 3, 1, 0]]
  D2 := [[0, 4, 3, 1, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_55_24 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨55, by decide⟩
  m := 1
  T1 := T147_55
  T2 := Q2.T147_55_2
  h1 := (0,4,4,1,2)
  h2 := (0,4,4,1,4)
  D1 := [[0, 4, 4, 1, 1]]
  D2 := [[0, 4, 4, 1, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_56_5 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨56, by decide⟩
  m := 1
  T1 := T147_56
  T2 := Q2.T147_56_2
  h1 := (0,1,0,4,2)
  h2 := (0,1,0,4,0)
  D1 := [[0, 1, 0, 4, 2]]
  D2 := [[0, 1, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_56_6 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨56, by decide⟩
  m := 1
  T1 := T147_56
  T2 := Q2.T147_56_2
  h1 := (0,1,1,3,2)
  h2 := (0,1,1,3,0)
  D1 := [[0, 1, 1, 3, 1]]
  D2 := [[0, 1, 1, 3, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_56_7 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨56, by decide⟩
  m := 1
  T1 := T147_56
  T2 := Q2.T147_56_2
  h1 := (0,1,2,2,2)
  h2 := (0,1,2,2,0)
  D1 := [[0, 1, 2, 2, 0]]
  D2 := [[0, 1, 2, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_56_8 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨56, by decide⟩
  m := 1
  T1 := T147_56
  T2 := Q2.T147_56_2
  h1 := (0,1,3,1,2)
  h2 := (0,1,3,1,0)
  D1 := [[0, 1, 3, 1, 4]]
  D2 := [[0, 1, 3, 1, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_56_9 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨56, by decide⟩
  m := 1
  T1 := T147_56
  T2 := Q2.T147_56_2
  h1 := (0,1,4,0,2)
  h2 := (0,1,4,0,0)
  D1 := [[0, 1, 4, 0, 3]]
  D2 := [[0, 1, 4, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_56_10 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨56, by decide⟩
  m := 1
  T1 := T147_56
  T2 := Q2.T147_56_2
  h1 := (0,2,0,3,4)
  h2 := (0,2,0,3,0)
  D1 := [[0, 2, 0, 3, 4]]
  D2 := [[0, 2, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_56_11 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨56, by decide⟩
  m := 1
  T1 := T147_56
  T2 := Q2.T147_56_2
  h1 := (0,2,1,2,4)
  h2 := (0,2,1,2,0)
  D1 := [[0, 2, 1, 2, 2]]
  D2 := [[0, 2, 1, 2, 3]]
  bind1 := by decide
  bind2 := by decide

end LeanDring.P5Presentation
