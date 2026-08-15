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
cdd tier, chunk 28: 60 columns.
-/

-- machine-emitted data: silence style linters (generated long lines, file-level options)
set_option linter.style.longLine false

namespace LeanDring.P5Presentation

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

def colCertDiv_147_71_21 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨71, by decide⟩
  m := 1
  T1 := T147_71
  T2 := Q2.T147_71_2
  h1 := (4,2,1,2,3)
  h2 := (4,2,1,2,4)
  D1 := [[4, 2, 1, 4, 3]]
  D2 := [[4, 2, 1, 4, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_71_22 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨71, by decide⟩
  m := 1
  T1 := T147_71
  T2 := Q2.T147_71_2
  h1 := (4,2,2,1,3)
  h2 := (4,2,2,1,4)
  D1 := [[4, 2, 2, 3, 0]]
  D2 := [[4, 2, 2, 3, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_71_23 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨71, by decide⟩
  m := 1
  T1 := T147_71
  T2 := Q2.T147_71_2
  h1 := (4,2,3,0,3)
  h2 := (4,2,3,0,4)
  D1 := [[4, 2, 3, 2, 2]]
  D2 := [[4, 2, 3, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_71_24 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨71, by decide⟩
  m := 1
  T1 := T147_71
  T2 := Q2.T147_71_2
  h1 := (4,2,4,4,3)
  h2 := (4,2,4,4,4)
  D1 := [[4, 2, 4, 1, 4]]
  D2 := [[4, 2, 4, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_72_5 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨72, by decide⟩
  m := 1
  T1 := T147_72
  T2 := Q2.T147_72_2
  h1 := (1,3,0,0,3)
  h2 := (1,3,0,0,4)
  D1 := [[1, 3, 0, 2, 1]]
  D2 := [[1, 3, 0, 2, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_72_6 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨72, by decide⟩
  m := 1
  T1 := T147_72
  T2 := Q2.T147_72_2
  h1 := (1,3,1,3,3)
  h2 := (1,3,1,3,4)
  D1 := [[1, 3, 1, 0, 0]]
  D2 := [[1, 3, 1, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_72_7 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨72, by decide⟩
  m := 1
  T1 := T147_72
  T2 := Q2.T147_72_2
  h1 := (1,3,2,1,3)
  h2 := (1,3,2,1,4)
  D1 := [[1, 3, 2, 3, 4]]
  D2 := [[1, 3, 2, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_72_8 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨72, by decide⟩
  m := 1
  T1 := T147_72
  T2 := Q2.T147_72_2
  h1 := (1,3,3,4,3)
  h2 := (1,3,3,4,4)
  D1 := [[1, 3, 3, 1, 3]]
  D2 := [[1, 3, 3, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_72_9 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨72, by decide⟩
  m := 1
  T1 := T147_72
  T2 := Q2.T147_72_2
  h1 := (1,3,4,2,3)
  h2 := (1,3,4,2,4)
  D1 := [[1, 3, 4, 4, 2]]
  D2 := [[1, 3, 4, 4, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_72_10 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨72, by decide⟩
  m := 1
  T1 := T147_72
  T2 := Q2.T147_72_2
  h1 := (2,1,0,3,2)
  h2 := (2,1,0,3,0)
  D1 := [[2, 1, 0, 1, 4]]
  D2 := [[2, 1, 0, 1, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_72_11 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨72, by decide⟩
  m := 1
  T1 := T147_72
  T2 := Q2.T147_72_2
  h1 := (2,1,1,1,2)
  h2 := (2,1,1,1,0)
  D1 := [[2, 1, 1, 4, 2]]
  D2 := [[2, 1, 1, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_72_12 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨72, by decide⟩
  m := 1
  T1 := T147_72
  T2 := Q2.T147_72_2
  h1 := (2,1,2,4,2)
  h2 := (2,1,2,4,0)
  D1 := [[2, 1, 2, 2, 0]]
  D2 := [[2, 1, 2, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_72_13 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨72, by decide⟩
  m := 1
  T1 := T147_72
  T2 := Q2.T147_72_2
  h1 := (2,1,3,2,2)
  h2 := (2,1,3,2,0)
  D1 := [[2, 1, 3, 0, 3]]
  D2 := [[2, 1, 3, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_72_14 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨72, by decide⟩
  m := 1
  T1 := T147_72
  T2 := Q2.T147_72_2
  h1 := (2,1,4,0,2)
  h2 := (2,1,4,0,0)
  D1 := [[2, 1, 4, 3, 1]]
  D2 := [[2, 1, 4, 3, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_72_15 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨72, by decide⟩
  m := 1
  T1 := T147_72
  T2 := Q2.T147_72_2
  h1 := (3,4,0,4,3)
  h2 := (3,4,0,4,2)
  D1 := [[3, 4, 0, 2, 0]]
  D2 := [[3, 4, 0, 2, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_72_16 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨72, by decide⟩
  m := 1
  T1 := T147_72
  T2 := Q2.T147_72_2
  h1 := (3,4,1,2,3)
  h2 := (3,4,1,2,2)
  D1 := [[3, 4, 1, 0, 2]]
  D2 := [[3, 4, 1, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_72_17 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨72, by decide⟩
  m := 1
  T1 := T147_72
  T2 := Q2.T147_72_2
  h1 := (3,4,2,0,3)
  h2 := (3,4,2,0,2)
  D1 := [[3, 4, 2, 3, 4]]
  D2 := [[3, 4, 2, 3, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_72_18 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨72, by decide⟩
  m := 1
  T1 := T147_72
  T2 := Q2.T147_72_2
  h1 := (3,4,3,3,3)
  h2 := (3,4,3,3,2)
  D1 := [[3, 4, 3, 1, 1]]
  D2 := [[3, 4, 3, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_72_19 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨72, by decide⟩
  m := 1
  T1 := T147_72
  T2 := Q2.T147_72_2
  h1 := (3,4,4,1,3)
  h2 := (3,4,4,1,2)
  D1 := [[3, 4, 4, 4, 3]]
  D2 := [[3, 4, 4, 4, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_72_20 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨72, by decide⟩
  m := 1
  T1 := T147_72
  T2 := Q2.T147_72_2
  h1 := (4,2,0,3,1)
  h2 := (4,2,0,3,2)
  D1 := [[4, 2, 0, 0, 4]]
  D2 := [[4, 2, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_72_21 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨72, by decide⟩
  m := 1
  T1 := T147_72
  T2 := Q2.T147_72_2
  h1 := (4,2,1,1,1)
  h2 := (4,2,1,1,2)
  D1 := [[4, 2, 1, 3, 0]]
  D2 := [[4, 2, 1, 3, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_72_22 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨72, by decide⟩
  m := 1
  T1 := T147_72
  T2 := Q2.T147_72_2
  h1 := (4,2,2,4,1)
  h2 := (4,2,2,4,2)
  D1 := [[4, 2, 2, 1, 1]]
  D2 := [[4, 2, 2, 1, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_72_23 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨72, by decide⟩
  m := 1
  T1 := T147_72
  T2 := Q2.T147_72_2
  h1 := (4,2,3,2,1)
  h2 := (4,2,3,2,2)
  D1 := [[4, 2, 3, 4, 2]]
  D2 := [[4, 2, 3, 4, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_72_24 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨72, by decide⟩
  m := 1
  T1 := T147_72
  T2 := Q2.T147_72_2
  h1 := (4,2,4,0,1)
  h2 := (4,2,4,0,2)
  D1 := [[4, 2, 4, 2, 3]]
  D2 := [[4, 2, 4, 2, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_73_50 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨73, by decide⟩
  m := 1
  T1 := T147_73
  T2 := Q2.T147_73_2
  h1 := (2,1,0,3,1)
  h2 := (2,1,0,3,2)
  D1 := [[2, 1, 0, 1, 3]]
  D2 := [[2, 1, 0, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_73_55 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨73, by decide⟩
  m := 1
  T1 := T147_73
  T2 := Q2.T147_73_2
  h1 := (2,1,1,0,1)
  h2 := (2,1,1,0,2)
  D1 := [[2, 1, 1, 3, 3]]
  D2 := [[2, 1, 1, 3, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_73_60 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨73, by decide⟩
  m := 1
  T1 := T147_73
  T2 := Q2.T147_73_2
  h1 := (2,1,2,2,1)
  h2 := (2,1,2,2,2)
  D1 := [[2, 1, 2, 0, 3]]
  D2 := [[2, 1, 2, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_73_65 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨73, by decide⟩
  m := 1
  T1 := T147_73
  T2 := Q2.T147_73_2
  h1 := (2,1,3,4,1)
  h2 := (2,1,3,4,2)
  D1 := [[2, 1, 3, 2, 3]]
  D2 := [[2, 1, 3, 2, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_73_70 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨73, by decide⟩
  m := 1
  T1 := T147_73
  T2 := Q2.T147_73_2
  h1 := (2,1,4,1,1)
  h2 := (2,1,4,1,2)
  D1 := [[2, 1, 4, 4, 3]]
  D2 := [[2, 1, 4, 4, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_73_75 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨73, by decide⟩
  m := 1
  T1 := T147_73
  T2 := Q2.T147_73_2
  h1 := (3,4,0,4,4)
  h2 := (3,4,0,4,0)
  D1 := [[3, 4, 0, 2, 1]]
  D2 := [[3, 4, 0, 2, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_73_80 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨73, by decide⟩
  m := 1
  T1 := T147_73
  T2 := Q2.T147_73_2
  h1 := (3,4,1,1,4)
  h2 := (3,4,1,1,0)
  D1 := [[3, 4, 1, 4, 1]]
  D2 := [[3, 4, 1, 4, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_73_85 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨73, by decide⟩
  m := 1
  T1 := T147_73
  T2 := Q2.T147_73_2
  h1 := (3,4,2,3,4)
  h2 := (3,4,2,3,0)
  D1 := [[3, 4, 2, 1, 1]]
  D2 := [[3, 4, 2, 1, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_73_90 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨73, by decide⟩
  m := 1
  T1 := T147_73
  T2 := Q2.T147_73_2
  h1 := (3,4,3,0,4)
  h2 := (3,4,3,0,0)
  D1 := [[3, 4, 3, 3, 1]]
  D2 := [[3, 4, 3, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_73_95 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨73, by decide⟩
  m := 1
  T1 := T147_73
  T2 := Q2.T147_73_2
  h1 := (3,4,4,2,4)
  h2 := (3,4,4,2,0)
  D1 := [[3, 4, 4, 0, 1]]
  D2 := [[3, 4, 4, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_73_100 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨73, by decide⟩
  m := 1
  T1 := T147_73
  T2 := Q2.T147_73_2
  h1 := (4,2,0,3,4)
  h2 := (4,2,0,3,1)
  D1 := [[4, 2, 0, 0, 2]]
  D2 := [[4, 2, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_73_105 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨73, by decide⟩
  m := 1
  T1 := T147_73
  T2 := Q2.T147_73_2
  h1 := (4,2,1,0,4)
  h2 := (4,2,1,0,1)
  D1 := [[4, 2, 1, 2, 2]]
  D2 := [[4, 2, 1, 2, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_73_110 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨73, by decide⟩
  m := 1
  T1 := T147_73
  T2 := Q2.T147_73_2
  h1 := (4,2,2,2,4)
  h2 := (4,2,2,2,1)
  D1 := [[4, 2, 2, 4, 2]]
  D2 := [[4, 2, 2, 4, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_73_115 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨73, by decide⟩
  m := 1
  T1 := T147_73
  T2 := Q2.T147_73_2
  h1 := (4,2,3,4,4)
  h2 := (4,2,3,4,1)
  D1 := [[4, 2, 3, 1, 2]]
  D2 := [[4, 2, 3, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_73_120 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨73, by decide⟩
  m := 1
  T1 := T147_73
  T2 := Q2.T147_73_2
  h1 := (4,2,4,1,4)
  h2 := (4,2,4,1,1)
  D1 := [[4, 2, 4, 3, 2]]
  D2 := [[4, 2, 4, 3, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_74_10 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨74, by decide⟩
  m := 1
  T1 := T147_74
  T2 := Q2.T147_74_2
  h1 := (2,1,0,3,1)
  h2 := (2,1,0,3,2)
  D1 := [[2, 1, 0, 1, 3]]
  D2 := [[2, 1, 0, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_74_11 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨74, by decide⟩
  m := 1
  T1 := T147_74
  T2 := Q2.T147_74_2
  h1 := (2,1,1,4,1)
  h2 := (2,1,1,4,2)
  D1 := [[2, 1, 1, 2, 0]]
  D2 := [[2, 1, 1, 2, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_74_12 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨74, by decide⟩
  m := 1
  T1 := T147_74
  T2 := Q2.T147_74_2
  h1 := (2,1,2,0,1)
  h2 := (2,1,2,0,2)
  D1 := [[2, 1, 2, 3, 2]]
  D2 := [[2, 1, 2, 3, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_74_13 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨74, by decide⟩
  m := 1
  T1 := T147_74
  T2 := Q2.T147_74_2
  h1 := (2,1,3,1,1)
  h2 := (2,1,3,1,2)
  D1 := [[2, 1, 3, 4, 4]]
  D2 := [[2, 1, 3, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_74_14 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨74, by decide⟩
  m := 1
  T1 := T147_74
  T2 := Q2.T147_74_2
  h1 := (2,1,4,2,1)
  h2 := (2,1,4,2,2)
  D1 := [[2, 1, 4, 0, 1]]
  D2 := [[2, 1, 4, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_74_15 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨74, by decide⟩
  m := 1
  T1 := T147_74
  T2 := Q2.T147_74_2
  h1 := (3,4,0,4,4)
  h2 := (3,4,0,4,0)
  D1 := [[3, 4, 0, 2, 1]]
  D2 := [[3, 4, 0, 2, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_74_16 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨74, by decide⟩
  m := 1
  T1 := T147_74
  T2 := Q2.T147_74_2
  h1 := (3,4,1,0,4)
  h2 := (3,4,1,0,0)
  D1 := [[3, 4, 1, 3, 4]]
  D2 := [[3, 4, 1, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_74_17 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨74, by decide⟩
  m := 1
  T1 := T147_74
  T2 := Q2.T147_74_2
  h1 := (3,4,2,1,4)
  h2 := (3,4,2,1,0)
  D1 := [[3, 4, 2, 4, 2]]
  D2 := [[3, 4, 2, 4, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_74_18 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨74, by decide⟩
  m := 1
  T1 := T147_74
  T2 := Q2.T147_74_2
  h1 := (3,4,3,2,4)
  h2 := (3,4,3,2,0)
  D1 := [[3, 4, 3, 0, 0]]
  D2 := [[3, 4, 3, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_74_19 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨74, by decide⟩
  m := 1
  T1 := T147_74
  T2 := Q2.T147_74_2
  h1 := (3,4,4,3,4)
  h2 := (3,4,4,3,0)
  D1 := [[3, 4, 4, 1, 3]]
  D2 := [[3, 4, 4, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_74_20 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨74, by decide⟩
  m := 1
  T1 := T147_74
  T2 := Q2.T147_74_2
  h1 := (4,2,0,3,4)
  h2 := (4,2,0,3,1)
  D1 := [[4, 2, 0, 0, 2]]
  D2 := [[4, 2, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_74_21 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨74, by decide⟩
  m := 1
  T1 := T147_74
  T2 := Q2.T147_74_2
  h1 := (4,2,1,4,4)
  h2 := (4,2,1,4,1)
  D1 := [[4, 2, 1, 1, 1]]
  D2 := [[4, 2, 1, 1, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_74_22 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨74, by decide⟩
  m := 1
  T1 := T147_74
  T2 := Q2.T147_74_2
  h1 := (4,2,2,0,4)
  h2 := (4,2,2,0,1)
  D1 := [[4, 2, 2, 2, 0]]
  D2 := [[4, 2, 2, 2, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_74_23 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨74, by decide⟩
  m := 1
  T1 := T147_74
  T2 := Q2.T147_74_2
  h1 := (4,2,3,1,4)
  h2 := (4,2,3,1,1)
  D1 := [[4, 2, 3, 3, 4]]
  D2 := [[4, 2, 3, 3, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_74_24 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨74, by decide⟩
  m := 1
  T1 := T147_74
  T2 := Q2.T147_74_2
  h1 := (4,2,4,2,4)
  h2 := (4,2,4,2,1)
  D1 := [[4, 2, 4, 4, 3]]
  D2 := [[4, 2, 4, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_75_5 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨75, by decide⟩
  m := 1
  T1 := T147_75
  T2 := Q2.T147_75_2
  h1 := (1,1,0,4,1)
  h2 := (1,1,0,4,4)
  D1 := [[1, 1, 0, 3, 3]]
  D2 := [[1, 1, 0, 3, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_75_6 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨75, by decide⟩
  m := 1
  T1 := T147_75
  T2 := Q2.T147_75_2
  h1 := (1,1,1,4,1)
  h2 := (1,1,1,4,4)
  D1 := [[1, 1, 1, 3, 2]]
  D2 := [[1, 1, 1, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_75_7 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨75, by decide⟩
  m := 1
  T1 := T147_75
  T2 := Q2.T147_75_2
  h1 := (1,1,2,4,1)
  h2 := (1,1,2,4,4)
  D1 := [[1, 1, 2, 3, 1]]
  D2 := [[1, 1, 2, 3, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_75_8 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨75, by decide⟩
  m := 1
  T1 := T147_75
  T2 := Q2.T147_75_2
  h1 := (1,1,3,4,1)
  h2 := (1,1,3,4,4)
  D1 := [[1, 1, 3, 3, 0]]
  D2 := [[1, 1, 3, 3, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_75_9 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨75, by decide⟩
  m := 1
  T1 := T147_75
  T2 := Q2.T147_75_2
  h1 := (1,1,4,4,1)
  h2 := (1,1,4,4,4)
  D1 := [[1, 1, 4, 3, 4]]
  D2 := [[1, 1, 4, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_75_10 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨75, by decide⟩
  m := 1
  T1 := T147_75
  T2 := Q2.T147_75_2
  h1 := (2,2,0,4,1)
  h2 := (2,2,0,4,2)
  D1 := [[2, 2, 0, 0, 4]]
  D2 := [[2, 2, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

end LeanDring.P5Presentation
