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
cdd tier, chunk 26: 60 columns.
-/

-- machine-emitted data: silence style linters (generated long lines, file-level options)
set_option linter.style.longLine false

namespace LeanDring.P5Presentation

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

def colCertDiv_147_64_85 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨64, by decide⟩
  m := 1
  T1 := T147_64
  T2 := Q2.T147_64_2
  h1 := (3,2,2,3,0)
  h2 := (3,2,2,3,2)
  D1 := [[3, 2, 2, 2, 4]]
  D2 := [[3, 2, 2, 2, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_64_90 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨64, by decide⟩
  m := 1
  T1 := T147_64
  T2 := Q2.T147_64_2
  h1 := (3,2,3,4,0)
  h2 := (3,2,3,4,2)
  D1 := [[3, 2, 3, 3, 4]]
  D2 := [[3, 2, 3, 3, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_64_95 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨64, by decide⟩
  m := 1
  T1 := T147_64
  T2 := Q2.T147_64_2
  h1 := (3,2,4,0,0)
  h2 := (3,2,4,0,2)
  D1 := [[3, 2, 4, 4, 4]]
  D2 := [[3, 2, 4, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_64_100 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨64, by decide⟩
  m := 1
  T1 := T147_64
  T2 := Q2.T147_64_2
  h1 := (4,1,0,1,2)
  h2 := (4,1,0,1,0)
  D1 := [[4, 1, 0, 2, 3]]
  D2 := [[4, 1, 0, 2, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_64_105 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨64, by decide⟩
  m := 1
  T1 := T147_64
  T2 := Q2.T147_64_2
  h1 := (4,1,1,2,2)
  h2 := (4,1,1,2,0)
  D1 := [[4, 1, 1, 3, 3]]
  D2 := [[4, 1, 1, 3, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_64_110 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨64, by decide⟩
  m := 1
  T1 := T147_64
  T2 := Q2.T147_64_2
  h1 := (4,1,2,3,2)
  h2 := (4,1,2,3,0)
  D1 := [[4, 1, 2, 4, 3]]
  D2 := [[4, 1, 2, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_64_115 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨64, by decide⟩
  m := 1
  T1 := T147_64
  T2 := Q2.T147_64_2
  h1 := (4,1,3,4,2)
  h2 := (4,1,3,4,0)
  D1 := [[4, 1, 3, 0, 3]]
  D2 := [[4, 1, 3, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_64_120 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨64, by decide⟩
  m := 1
  T1 := T147_64
  T2 := Q2.T147_64_2
  h1 := (4,1,4,0,2)
  h2 := (4,1,4,0,0)
  D1 := [[4, 1, 4, 1, 3]]
  D2 := [[4, 1, 4, 1, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_65_5 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨65, by decide⟩
  m := 1
  T1 := T147_65
  T2 := Q2.T147_65_2
  h1 := (1,2,0,2,2)
  h2 := (1,2,0,2,4)
  D1 := [[1, 2, 0, 0, 2]]
  D2 := [[1, 2, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_65_6 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨65, by decide⟩
  m := 1
  T1 := T147_65
  T2 := Q2.T147_65_2
  h1 := (1,2,1,2,2)
  h2 := (1,2,1,2,4)
  D1 := [[1, 2, 1, 0, 0]]
  D2 := [[1, 2, 1, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_65_7 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨65, by decide⟩
  m := 1
  T1 := T147_65
  T2 := Q2.T147_65_2
  h1 := (1,2,2,2,2)
  h2 := (1,2,2,2,4)
  D1 := [[1, 2, 2, 0, 3]]
  D2 := [[1, 2, 2, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_65_8 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨65, by decide⟩
  m := 1
  T1 := T147_65
  T2 := Q2.T147_65_2
  h1 := (1,2,3,2,2)
  h2 := (1,2,3,2,4)
  D1 := [[1, 2, 3, 0, 1]]
  D2 := [[1, 2, 3, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_65_9 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨65, by decide⟩
  m := 1
  T1 := T147_65
  T2 := Q2.T147_65_2
  h1 := (1,2,4,2,2)
  h2 := (1,2,4,2,4)
  D1 := [[1, 2, 4, 0, 4]]
  D2 := [[1, 2, 4, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_65_10 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨65, by decide⟩
  m := 1
  T1 := T147_65
  T2 := Q2.T147_65_2
  h1 := (2,4,0,1,1)
  h2 := (2,4,0,1,0)
  D1 := [[2, 4, 0, 3, 1]]
  D2 := [[2, 4, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_65_11 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨65, by decide⟩
  m := 1
  T1 := T147_65
  T2 := Q2.T147_65_2
  h1 := (2,4,1,1,1)
  h2 := (2,4,1,1,0)
  D1 := [[2, 4, 1, 3, 2]]
  D2 := [[2, 4, 1, 3, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_65_12 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨65, by decide⟩
  m := 1
  T1 := T147_65
  T2 := Q2.T147_65_2
  h1 := (2,4,2,1,1)
  h2 := (2,4,2,1,0)
  D1 := [[2, 4, 2, 3, 3]]
  D2 := [[2, 4, 2, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_65_13 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨65, by decide⟩
  m := 1
  T1 := T147_65
  T2 := Q2.T147_65_2
  h1 := (2,4,3,1,1)
  h2 := (2,4,3,1,0)
  D1 := [[2, 4, 3, 3, 4]]
  D2 := [[2, 4, 3, 3, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_65_14 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨65, by decide⟩
  m := 1
  T1 := T147_65
  T2 := Q2.T147_65_2
  h1 := (2,4,4,1,1)
  h2 := (2,4,4,1,0)
  D1 := [[2, 4, 4, 3, 0]]
  D2 := [[2, 4, 4, 3, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_65_15 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨65, by decide⟩
  m := 1
  T1 := T147_65
  T2 := Q2.T147_65_2
  h1 := (3,1,0,2,0)
  h2 := (3,1,0,2,2)
  D1 := [[3, 1, 0, 4, 0]]
  D2 := [[3, 1, 0, 4, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_65_16 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨65, by decide⟩
  m := 1
  T1 := T147_65
  T2 := Q2.T147_65_2
  h1 := (3,1,1,2,0)
  h2 := (3,1,1,2,2)
  D1 := [[3, 1, 1, 4, 4]]
  D2 := [[3, 1, 1, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_65_17 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨65, by decide⟩
  m := 1
  T1 := T147_65
  T2 := Q2.T147_65_2
  h1 := (3,1,2,2,0)
  h2 := (3,1,2,2,2)
  D1 := [[3, 1, 2, 4, 3]]
  D2 := [[3, 1, 2, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_65_18 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨65, by decide⟩
  m := 1
  T1 := T147_65
  T2 := Q2.T147_65_2
  h1 := (3,1,3,2,0)
  h2 := (3,1,3,2,2)
  D1 := [[3, 1, 3, 4, 2]]
  D2 := [[3, 1, 3, 4, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_65_19 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨65, by decide⟩
  m := 1
  T1 := T147_65
  T2 := Q2.T147_65_2
  h1 := (3,1,4,2,0)
  h2 := (3,1,4,2,2)
  D1 := [[3, 1, 4, 4, 1]]
  D2 := [[3, 1, 4, 4, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_65_20 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨65, by decide⟩
  m := 1
  T1 := T147_65
  T2 := Q2.T147_65_2
  h1 := (4,3,0,0,4)
  h2 := (4,3,0,0,3)
  D1 := [[4, 3, 0, 3, 4]]
  D2 := [[4, 3, 0, 3, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_65_21 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨65, by decide⟩
  m := 1
  T1 := T147_65
  T2 := Q2.T147_65_2
  h1 := (4,3,1,0,4)
  h2 := (4,3,1,0,3)
  D1 := [[4, 3, 1, 3, 1]]
  D2 := [[4, 3, 1, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_65_22 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨65, by decide⟩
  m := 1
  T1 := T147_65
  T2 := Q2.T147_65_2
  h1 := (4,3,2,0,4)
  h2 := (4,3,2,0,3)
  D1 := [[4, 3, 2, 3, 3]]
  D2 := [[4, 3, 2, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_65_23 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨65, by decide⟩
  m := 1
  T1 := T147_65
  T2 := Q2.T147_65_2
  h1 := (4,3,3,0,4)
  h2 := (4,3,3,0,3)
  D1 := [[4, 3, 3, 3, 0]]
  D2 := [[4, 3, 3, 3, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_65_24 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨65, by decide⟩
  m := 1
  T1 := T147_65
  T2 := Q2.T147_65_2
  h1 := (4,3,4,0,4)
  h2 := (4,3,4,0,3)
  D1 := [[4, 3, 4, 3, 2]]
  D2 := [[4, 3, 4, 3, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_66_5 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨66, by decide⟩
  m := 1
  T1 := T147_66
  T2 := Q2.T147_66_2
  h1 := (1,2,0,2,1)
  h2 := (1,2,0,2,3)
  D1 := [[1, 2, 0, 0, 1]]
  D2 := [[1, 2, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_66_6 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨66, by decide⟩
  m := 1
  T1 := T147_66
  T2 := Q2.T147_66_2
  h1 := (1,2,1,1,1)
  h2 := (1,2,1,1,3)
  D1 := [[1, 2, 1, 4, 0]]
  D2 := [[1, 2, 1, 4, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_66_7 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨66, by decide⟩
  m := 1
  T1 := T147_66
  T2 := Q2.T147_66_2
  h1 := (1,2,2,0,1)
  h2 := (1,2,2,0,3)
  D1 := [[1, 2, 2, 3, 4]]
  D2 := [[1, 2, 2, 3, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_66_8 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨66, by decide⟩
  m := 1
  T1 := T147_66
  T2 := Q2.T147_66_2
  h1 := (1,2,3,4,1)
  h2 := (1,2,3,4,3)
  D1 := [[1, 2, 3, 2, 3]]
  D2 := [[1, 2, 3, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_66_9 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨66, by decide⟩
  m := 1
  T1 := T147_66
  T2 := Q2.T147_66_2
  h1 := (1,2,4,3,1)
  h2 := (1,2,4,3,3)
  D1 := [[1, 2, 4, 1, 2]]
  D2 := [[1, 2, 4, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_66_10 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨66, by decide⟩
  m := 1
  T1 := T147_66
  T2 := Q2.T147_66_2
  h1 := (2,4,0,1,4)
  h2 := (2,4,0,1,3)
  D1 := [[2, 4, 0, 3, 4]]
  D2 := [[2, 4, 0, 3, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_66_11 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨66, by decide⟩
  m := 1
  T1 := T147_66
  T2 := Q2.T147_66_2
  h1 := (2,4,1,0,4)
  h2 := (2,4,1,0,3)
  D1 := [[2, 4, 1, 2, 2]]
  D2 := [[2, 4, 1, 2, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_66_12 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨66, by decide⟩
  m := 1
  T1 := T147_66
  T2 := Q2.T147_66_2
  h1 := (2,4,2,4,4)
  h2 := (2,4,2,4,3)
  D1 := [[2, 4, 2, 1, 0]]
  D2 := [[2, 4, 2, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_66_13 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨66, by decide⟩
  m := 1
  T1 := T147_66
  T2 := Q2.T147_66_2
  h1 := (2,4,3,3,4)
  h2 := (2,4,3,3,3)
  D1 := [[2, 4, 3, 0, 3]]
  D2 := [[2, 4, 3, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_66_14 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨66, by decide⟩
  m := 1
  T1 := T147_66
  T2 := Q2.T147_66_2
  h1 := (2,4,4,2,4)
  h2 := (2,4,4,2,3)
  D1 := [[2, 4, 4, 4, 1]]
  D2 := [[2, 4, 4, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_66_15 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨66, by decide⟩
  m := 1
  T1 := T147_66
  T2 := Q2.T147_66_2
  h1 := (3,1,0,2,2)
  h2 := (3,1,0,2,4)
  D1 := [[3, 1, 0, 4, 2]]
  D2 := [[3, 1, 0, 4, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_66_16 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨66, by decide⟩
  m := 1
  T1 := T147_66
  T2 := Q2.T147_66_2
  h1 := (3,1,1,1,2)
  h2 := (3,1,1,1,4)
  D1 := [[3, 1, 1, 3, 4]]
  D2 := [[3, 1, 1, 3, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_66_17 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨66, by decide⟩
  m := 1
  T1 := T147_66
  T2 := Q2.T147_66_2
  h1 := (3,1,2,0,2)
  h2 := (3,1,2,0,4)
  D1 := [[3, 1, 2, 2, 1]]
  D2 := [[3, 1, 2, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_66_18 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨66, by decide⟩
  m := 1
  T1 := T147_66
  T2 := Q2.T147_66_2
  h1 := (3,1,3,4,2)
  h2 := (3,1,3,4,4)
  D1 := [[3, 1, 3, 1, 3]]
  D2 := [[3, 1, 3, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_66_19 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨66, by decide⟩
  m := 1
  T1 := T147_66
  T2 := Q2.T147_66_2
  h1 := (3,1,4,3,2)
  h2 := (3,1,4,3,4)
  D1 := [[3, 1, 4, 0, 0]]
  D2 := [[3, 1, 4, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_66_20 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨66, by decide⟩
  m := 1
  T1 := T147_66
  T2 := Q2.T147_66_2
  h1 := (4,3,0,0,0)
  h2 := (4,3,0,0,4)
  D1 := [[4, 3, 0, 3, 0]]
  D2 := [[4, 3, 0, 3, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_66_21 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨66, by decide⟩
  m := 1
  T1 := T147_66
  T2 := Q2.T147_66_2
  h1 := (4,3,1,4,0)
  h2 := (4,3,1,4,4)
  D1 := [[4, 3, 1, 2, 1]]
  D2 := [[4, 3, 1, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_66_22 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨66, by decide⟩
  m := 1
  T1 := T147_66
  T2 := Q2.T147_66_2
  h1 := (4,3,2,3,0)
  h2 := (4,3,2,3,4)
  D1 := [[4, 3, 2, 1, 2]]
  D2 := [[4, 3, 2, 1, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_66_23 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨66, by decide⟩
  m := 1
  T1 := T147_66
  T2 := Q2.T147_66_2
  h1 := (4,3,3,2,0)
  h2 := (4,3,3,2,4)
  D1 := [[4, 3, 3, 0, 3]]
  D2 := [[4, 3, 3, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_66_24 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨66, by decide⟩
  m := 1
  T1 := T147_66
  T2 := Q2.T147_66_2
  h1 := (4,3,4,1,0)
  h2 := (4,3,4,1,4)
  D1 := [[4, 3, 4, 4, 4]]
  D2 := [[4, 3, 4, 4, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_67_75 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨67, by decide⟩
  m := 1
  T1 := T147_67
  T2 := Q2.T147_67_2
  h1 := (3,1,0,2,1)
  h2 := (3,1,0,2,2)
  D1 := [[3, 1, 0, 4, 1]]
  D2 := [[3, 1, 0, 4, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_67_80 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨67, by decide⟩
  m := 1
  T1 := T147_67
  T2 := Q2.T147_67_2
  h1 := (3,1,1,0,1)
  h2 := (3,1,1,0,2)
  D1 := [[3, 1, 1, 2, 1]]
  D2 := [[3, 1, 1, 2, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_67_85 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨67, by decide⟩
  m := 1
  T1 := T147_67
  T2 := Q2.T147_67_2
  h1 := (3,1,2,3,1)
  h2 := (3,1,2,3,2)
  D1 := [[3, 1, 2, 0, 1]]
  D2 := [[3, 1, 2, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_67_90 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨67, by decide⟩
  m := 1
  T1 := T147_67
  T2 := Q2.T147_67_2
  h1 := (3,1,3,1,1)
  h2 := (3,1,3,1,2)
  D1 := [[3, 1, 3, 3, 1]]
  D2 := [[3, 1, 3, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_67_95 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨67, by decide⟩
  m := 1
  T1 := T147_67
  T2 := Q2.T147_67_2
  h1 := (3,1,4,4,1)
  h2 := (3,1,4,4,2)
  D1 := [[3, 1, 4, 1, 1]]
  D2 := [[3, 1, 4, 1, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_67_100 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨67, by decide⟩
  m := 1
  T1 := T147_67
  T2 := Q2.T147_67_2
  h1 := (4,3,0,0,2)
  h2 := (4,3,0,0,3)
  D1 := [[4, 3, 0, 3, 2]]
  D2 := [[4, 3, 0, 3, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_67_105 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨67, by decide⟩
  m := 1
  T1 := T147_67
  T2 := Q2.T147_67_2
  h1 := (4,3,1,3,2)
  h2 := (4,3,1,3,3)
  D1 := [[4, 3, 1, 1, 2]]
  D2 := [[4, 3, 1, 1, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_67_110 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨67, by decide⟩
  m := 1
  T1 := T147_67
  T2 := Q2.T147_67_2
  h1 := (4,3,2,1,2)
  h2 := (4,3,2,1,3)
  D1 := [[4, 3, 2, 4, 2]]
  D2 := [[4, 3, 2, 4, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_67_115 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨67, by decide⟩
  m := 1
  T1 := T147_67
  T2 := Q2.T147_67_2
  h1 := (4,3,3,4,2)
  h2 := (4,3,3,4,3)
  D1 := [[4, 3, 3, 2, 2]]
  D2 := [[4, 3, 3, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_67_120 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨67, by decide⟩
  m := 1
  T1 := T147_67
  T2 := Q2.T147_67_2
  h1 := (4,3,4,2,2)
  h2 := (4,3,4,2,3)
  D1 := [[4, 3, 4, 0, 2]]
  D2 := [[4, 3, 4, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_68_5 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨68, by decide⟩
  m := 1
  T1 := T147_68
  T2 := Q2.T147_68_2
  h1 := (1,2,0,2,0)
  h2 := (1,2,0,2,2)
  D1 := [[1, 2, 0, 0, 0]]
  D2 := [[1, 2, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_68_6 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨68, by decide⟩
  m := 1
  T1 := T147_68
  T2 := Q2.T147_68_2
  h1 := (1,2,1,4,0)
  h2 := (1,2,1,4,2)
  D1 := [[1, 2, 1, 2, 1]]
  D2 := [[1, 2, 1, 2, 3]]
  bind1 := by decide
  bind2 := by decide

end LeanDring.P5Presentation
