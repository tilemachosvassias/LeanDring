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
cdd tier, chunk 25: 60 columns.
-/

-- machine-emitted data: silence style linters (generated long lines, file-level options)
set_option linter.style.longLine false

namespace LeanDring.P5Presentation

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

def colCertDiv_147_60_17 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨60, by decide⟩
  m := 1
  T1 := T147_60
  T2 := Q2.T147_60_2
  h1 := (3,2,2,1,2)
  h2 := (3,2,2,1,4)
  D1 := [[3, 2, 2, 0, 2]]
  D2 := [[3, 2, 2, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_60_18 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨60, by decide⟩
  m := 1
  T1 := T147_60
  T2 := Q2.T147_60_2
  h1 := (3,2,3,1,2)
  h2 := (3,2,3,1,4)
  D1 := [[3, 2, 3, 0, 0]]
  D2 := [[3, 2, 3, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_60_19 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨60, by decide⟩
  m := 1
  T1 := T147_60
  T2 := Q2.T147_60_2
  h1 := (3,2,4,1,2)
  h2 := (3,2,4,1,4)
  D1 := [[3, 2, 4, 0, 3]]
  D2 := [[3, 2, 4, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_60_20 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨60, by decide⟩
  m := 1
  T1 := T147_60
  T2 := Q2.T147_60_2
  h1 := (4,1,0,1,3)
  h2 := (4,1,0,1,1)
  D1 := [[4, 1, 0, 2, 4]]
  D2 := [[4, 1, 0, 2, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_60_21 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨60, by decide⟩
  m := 1
  T1 := T147_60
  T2 := Q2.T147_60_2
  h1 := (4,1,1,1,3)
  h2 := (4,1,1,1,1)
  D1 := [[4, 1, 1, 2, 3]]
  D2 := [[4, 1, 1, 2, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_60_22 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨60, by decide⟩
  m := 1
  T1 := T147_60
  T2 := Q2.T147_60_2
  h1 := (4,1,2,1,3)
  h2 := (4,1,2,1,1)
  D1 := [[4, 1, 2, 2, 2]]
  D2 := [[4, 1, 2, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_60_23 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨60, by decide⟩
  m := 1
  T1 := T147_60
  T2 := Q2.T147_60_2
  h1 := (4,1,3,1,3)
  h2 := (4,1,3,1,1)
  D1 := [[4, 1, 3, 2, 1]]
  D2 := [[4, 1, 3, 2, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_60_24 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨60, by decide⟩
  m := 1
  T1 := T147_60
  T2 := Q2.T147_60_2
  h1 := (4,1,4,1,3)
  h2 := (4,1,4,1,1)
  D1 := [[4, 1, 4, 2, 0]]
  D2 := [[4, 1, 4, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_61_10 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨61, by decide⟩
  m := 1
  T1 := T147_61
  T2 := Q2.T147_61_2
  h1 := (2,3,0,0,1)
  h2 := (2,3,0,0,2)
  D1 := [[2, 3, 0, 4, 0]]
  D2 := [[2, 3, 0, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_61_11 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨61, by decide⟩
  m := 1
  T1 := T147_61
  T2 := Q2.T147_61_2
  h1 := (2,3,1,4,1)
  h2 := (2,3,1,4,2)
  D1 := [[2, 3, 1, 3, 4]]
  D2 := [[2, 3, 1, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_61_12 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨61, by decide⟩
  m := 1
  T1 := T147_61
  T2 := Q2.T147_61_2
  h1 := (2,3,2,3,1)
  h2 := (2,3,2,3,2)
  D1 := [[2, 3, 2, 2, 3]]
  D2 := [[2, 3, 2, 2, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_61_13 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨61, by decide⟩
  m := 1
  T1 := T147_61
  T2 := Q2.T147_61_2
  h1 := (2,3,3,2,1)
  h2 := (2,3,3,2,2)
  D1 := [[2, 3, 3, 1, 2]]
  D2 := [[2, 3, 3, 1, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_61_14 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨61, by decide⟩
  m := 1
  T1 := T147_61
  T2 := Q2.T147_61_2
  h1 := (2,3,4,1,1)
  h2 := (2,3,4,1,2)
  D1 := [[2, 3, 4, 0, 1]]
  D2 := [[2, 3, 4, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_61_15 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨61, by decide⟩
  m := 1
  T1 := T147_61
  T2 := Q2.T147_61_2
  h1 := (3,2,0,1,3)
  h2 := (3,2,0,1,0)
  D1 := [[3, 2, 0, 0, 2]]
  D2 := [[3, 2, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_61_16 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨61, by decide⟩
  m := 1
  T1 := T147_61
  T2 := Q2.T147_61_2
  h1 := (3,2,1,0,3)
  h2 := (3,2,1,0,0)
  D1 := [[3, 2, 1, 4, 3]]
  D2 := [[3, 2, 1, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_61_17 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨61, by decide⟩
  m := 1
  T1 := T147_61
  T2 := Q2.T147_61_2
  h1 := (3,2,2,4,3)
  h2 := (3,2,2,4,0)
  D1 := [[3, 2, 2, 3, 4]]
  D2 := [[3, 2, 2, 3, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_61_18 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨61, by decide⟩
  m := 1
  T1 := T147_61
  T2 := Q2.T147_61_2
  h1 := (3,2,3,3,3)
  h2 := (3,2,3,3,0)
  D1 := [[3, 2, 3, 2, 0]]
  D2 := [[3, 2, 3, 2, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_61_19 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨61, by decide⟩
  m := 1
  T1 := T147_61
  T2 := Q2.T147_61_2
  h1 := (3,2,4,2,3)
  h2 := (3,2,4,2,0)
  D1 := [[3, 2, 4, 1, 1]]
  D2 := [[3, 2, 4, 1, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_61_20 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨61, by decide⟩
  m := 1
  T1 := T147_61
  T2 := Q2.T147_61_2
  h1 := (4,1,0,1,1)
  h2 := (4,1,0,1,4)
  D1 := [[4, 1, 0, 2, 2]]
  D2 := [[4, 1, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_61_21 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨61, by decide⟩
  m := 1
  T1 := T147_61
  T2 := Q2.T147_61_2
  h1 := (4,1,1,0,1)
  h2 := (4,1,1,0,4)
  D1 := [[4, 1, 1, 1, 0]]
  D2 := [[4, 1, 1, 1, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_61_22 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨61, by decide⟩
  m := 1
  T1 := T147_61
  T2 := Q2.T147_61_2
  h1 := (4,1,2,4,1)
  h2 := (4,1,2,4,4)
  D1 := [[4, 1, 2, 0, 3]]
  D2 := [[4, 1, 2, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_61_23 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨61, by decide⟩
  m := 1
  T1 := T147_61
  T2 := Q2.T147_61_2
  h1 := (4,1,3,3,1)
  h2 := (4,1,3,3,4)
  D1 := [[4, 1, 3, 4, 1]]
  D2 := [[4, 1, 3, 4, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_61_24 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨61, by decide⟩
  m := 1
  T1 := T147_61
  T2 := Q2.T147_61_2
  h1 := (4,1,4,2,1)
  h2 := (4,1,4,2,4)
  D1 := [[4, 1, 4, 3, 4]]
  D2 := [[4, 1, 4, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_62_10 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨62, by decide⟩
  m := 1
  T1 := T147_62
  T2 := Q2.T147_62_2
  h1 := (2,3,0,0,4)
  h2 := (2,3,0,0,0)
  D1 := [[2, 3, 0, 4, 3]]
  D2 := [[2, 3, 0, 4, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_62_11 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨62, by decide⟩
  m := 1
  T1 := T147_62
  T2 := Q2.T147_62_2
  h1 := (2,3,1,3,4)
  h2 := (2,3,1,3,0)
  D1 := [[2, 3, 1, 2, 4]]
  D2 := [[2, 3, 1, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_62_12 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨62, by decide⟩
  m := 1
  T1 := T147_62
  T2 := Q2.T147_62_2
  h1 := (2,3,2,1,4)
  h2 := (2,3,2,1,0)
  D1 := [[2, 3, 2, 0, 0]]
  D2 := [[2, 3, 2, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_62_13 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨62, by decide⟩
  m := 1
  T1 := T147_62
  T2 := Q2.T147_62_2
  h1 := (2,3,3,4,4)
  h2 := (2,3,3,4,0)
  D1 := [[2, 3, 3, 3, 1]]
  D2 := [[2, 3, 3, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_62_14 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨62, by decide⟩
  m := 1
  T1 := T147_62
  T2 := Q2.T147_62_2
  h1 := (2,3,4,2,4)
  h2 := (2,3,4,2,0)
  D1 := [[2, 3, 4, 1, 2]]
  D2 := [[2, 3, 4, 1, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_62_15 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨62, by decide⟩
  m := 1
  T1 := T147_62
  T2 := Q2.T147_62_2
  h1 := (3,2,0,1,0)
  h2 := (3,2,0,1,2)
  D1 := [[3, 2, 0, 0, 4]]
  D2 := [[3, 2, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_62_16 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨62, by decide⟩
  m := 1
  T1 := T147_62
  T2 := Q2.T147_62_2
  h1 := (3,2,1,4,0)
  h2 := (3,2,1,4,2)
  D1 := [[3, 2, 1, 3, 3]]
  D2 := [[3, 2, 1, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_62_17 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨62, by decide⟩
  m := 1
  T1 := T147_62
  T2 := Q2.T147_62_2
  h1 := (3,2,2,2,0)
  h2 := (3,2,2,2,2)
  D1 := [[3, 2, 2, 1, 2]]
  D2 := [[3, 2, 2, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_62_18 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨62, by decide⟩
  m := 1
  T1 := T147_62
  T2 := Q2.T147_62_2
  h1 := (3,2,3,0,0)
  h2 := (3,2,3,0,2)
  D1 := [[3, 2, 3, 4, 1]]
  D2 := [[3, 2, 3, 4, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_62_19 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨62, by decide⟩
  m := 1
  T1 := T147_62
  T2 := Q2.T147_62_2
  h1 := (3,2,4,3,0)
  h2 := (3,2,4,3,2)
  D1 := [[3, 2, 4, 2, 0]]
  D2 := [[3, 2, 4, 2, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_62_20 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨62, by decide⟩
  m := 1
  T1 := T147_62
  T2 := Q2.T147_62_2
  h1 := (4,1,0,1,2)
  h2 := (4,1,0,1,0)
  D1 := [[4, 1, 0, 2, 3]]
  D2 := [[4, 1, 0, 2, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_62_21 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨62, by decide⟩
  m := 1
  T1 := T147_62
  T2 := Q2.T147_62_2
  h1 := (4,1,1,4,2)
  h2 := (4,1,1,4,0)
  D1 := [[4, 1, 1, 0, 0]]
  D2 := [[4, 1, 1, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_62_22 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨62, by decide⟩
  m := 1
  T1 := T147_62
  T2 := Q2.T147_62_2
  h1 := (4,1,2,2,2)
  h2 := (4,1,2,2,0)
  D1 := [[4, 1, 2, 3, 2]]
  D2 := [[4, 1, 2, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_62_23 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨62, by decide⟩
  m := 1
  T1 := T147_62
  T2 := Q2.T147_62_2
  h1 := (4,1,3,0,2)
  h2 := (4,1,3,0,0)
  D1 := [[4, 1, 3, 1, 4]]
  D2 := [[4, 1, 3, 1, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_62_24 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨62, by decide⟩
  m := 1
  T1 := T147_62
  T2 := Q2.T147_62_2
  h1 := (4,1,4,3,2)
  h2 := (4,1,4,3,0)
  D1 := [[4, 1, 4, 4, 1]]
  D2 := [[4, 1, 4, 4, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_63_5 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨63, by decide⟩
  m := 1
  T1 := T147_63
  T2 := Q2.T147_63_2
  h1 := (1,4,0,3,3)
  h2 := (1,4,0,3,4)
  D1 := [[1, 4, 0, 4, 4]]
  D2 := [[1, 4, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_63_6 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨63, by decide⟩
  m := 1
  T1 := T147_63
  T2 := Q2.T147_63_2
  h1 := (1,4,1,0,3)
  h2 := (1,4,1,0,4)
  D1 := [[1, 4, 1, 1, 3]]
  D2 := [[1, 4, 1, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_63_7 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨63, by decide⟩
  m := 1
  T1 := T147_63
  T2 := Q2.T147_63_2
  h1 := (1,4,2,2,3)
  h2 := (1,4,2,2,4)
  D1 := [[1, 4, 2, 3, 2]]
  D2 := [[1, 4, 2, 3, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_63_8 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨63, by decide⟩
  m := 1
  T1 := T147_63
  T2 := Q2.T147_63_2
  h1 := (1,4,3,4,3)
  h2 := (1,4,3,4,4)
  D1 := [[1, 4, 3, 0, 1]]
  D2 := [[1, 4, 3, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_63_9 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨63, by decide⟩
  m := 1
  T1 := T147_63
  T2 := Q2.T147_63_2
  h1 := (1,4,4,1,3)
  h2 := (1,4,4,1,4)
  D1 := [[1, 4, 4, 2, 0]]
  D2 := [[1, 4, 4, 2, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_63_10 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨63, by decide⟩
  m := 1
  T1 := T147_63
  T2 := Q2.T147_63_2
  h1 := (2,3,0,0,0)
  h2 := (2,3,0,0,3)
  D1 := [[2, 3, 0, 4, 4]]
  D2 := [[2, 3, 0, 4, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_63_11 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨63, by decide⟩
  m := 1
  T1 := T147_63
  T2 := Q2.T147_63_2
  h1 := (2,3,1,2,0)
  h2 := (2,3,1,2,3)
  D1 := [[2, 3, 1, 1, 2]]
  D2 := [[2, 3, 1, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_63_12 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨63, by decide⟩
  m := 1
  T1 := T147_63
  T2 := Q2.T147_63_2
  h1 := (2,3,2,4,0)
  h2 := (2,3,2,4,3)
  D1 := [[2, 3, 2, 3, 0]]
  D2 := [[2, 3, 2, 3, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_63_13 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨63, by decide⟩
  m := 1
  T1 := T147_63
  T2 := Q2.T147_63_2
  h1 := (2,3,3,1,0)
  h2 := (2,3,3,1,3)
  D1 := [[2, 3, 3, 0, 3]]
  D2 := [[2, 3, 3, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_63_14 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨63, by decide⟩
  m := 1
  T1 := T147_63
  T2 := Q2.T147_63_2
  h1 := (2,3,4,3,0)
  h2 := (2,3,4,3,3)
  D1 := [[2, 3, 4, 2, 1]]
  D2 := [[2, 3, 4, 2, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_63_20 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨63, by decide⟩
  m := 1
  T1 := T147_63
  T2 := Q2.T147_63_2
  h1 := (4,1,0,1,4)
  h2 := (4,1,0,1,1)
  D1 := [[4, 1, 0, 2, 0]]
  D2 := [[4, 1, 0, 2, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_63_21 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨63, by decide⟩
  m := 1
  T1 := T147_63
  T2 := Q2.T147_63_2
  h1 := (4,1,1,3,4)
  h2 := (4,1,1,3,1)
  D1 := [[4, 1, 1, 4, 1]]
  D2 := [[4, 1, 1, 4, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_63_22 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨63, by decide⟩
  m := 1
  T1 := T147_63
  T2 := Q2.T147_63_2
  h1 := (4,1,2,0,4)
  h2 := (4,1,2,0,1)
  D1 := [[4, 1, 2, 1, 2]]
  D2 := [[4, 1, 2, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_63_23 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨63, by decide⟩
  m := 1
  T1 := T147_63
  T2 := Q2.T147_63_2
  h1 := (4,1,3,2,4)
  h2 := (4,1,3,2,1)
  D1 := [[4, 1, 3, 3, 3]]
  D2 := [[4, 1, 3, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_63_24 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨63, by decide⟩
  m := 1
  T1 := T147_63
  T2 := Q2.T147_63_2
  h1 := (4,1,4,4,4)
  h2 := (4,1,4,4,1)
  D1 := [[4, 1, 4, 0, 4]]
  D2 := [[4, 1, 4, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_64_50 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨64, by decide⟩
  m := 1
  T1 := T147_64
  T2 := Q2.T147_64_2
  h1 := (2,3,0,0,4)
  h2 := (2,3,0,0,0)
  D1 := [[2, 3, 0, 4, 3]]
  D2 := [[2, 3, 0, 4, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_64_55 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨64, by decide⟩
  m := 1
  T1 := T147_64
  T2 := Q2.T147_64_2
  h1 := (2,3,1,1,4)
  h2 := (2,3,1,1,0)
  D1 := [[2, 3, 1, 0, 3]]
  D2 := [[2, 3, 1, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_64_60 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨64, by decide⟩
  m := 1
  T1 := T147_64
  T2 := Q2.T147_64_2
  h1 := (2,3,2,2,4)
  h2 := (2,3,2,2,0)
  D1 := [[2, 3, 2, 1, 3]]
  D2 := [[2, 3, 2, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_64_65 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨64, by decide⟩
  m := 1
  T1 := T147_64
  T2 := Q2.T147_64_2
  h1 := (2,3,3,3,4)
  h2 := (2,3,3,3,0)
  D1 := [[2, 3, 3, 2, 3]]
  D2 := [[2, 3, 3, 2, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_64_70 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨64, by decide⟩
  m := 1
  T1 := T147_64
  T2 := Q2.T147_64_2
  h1 := (2,3,4,4,4)
  h2 := (2,3,4,4,0)
  D1 := [[2, 3, 4, 3, 3]]
  D2 := [[2, 3, 4, 3, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_64_75 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨64, by decide⟩
  m := 1
  T1 := T147_64
  T2 := Q2.T147_64_2
  h1 := (3,2,0,1,0)
  h2 := (3,2,0,1,2)
  D1 := [[3, 2, 0, 0, 4]]
  D2 := [[3, 2, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_64_80 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨64, by decide⟩
  m := 1
  T1 := T147_64
  T2 := Q2.T147_64_2
  h1 := (3,2,1,2,0)
  h2 := (3,2,1,2,2)
  D1 := [[3, 2, 1, 1, 4]]
  D2 := [[3, 2, 1, 1, 1]]
  bind1 := by decide
  bind2 := by decide

end LeanDring.P5Presentation
