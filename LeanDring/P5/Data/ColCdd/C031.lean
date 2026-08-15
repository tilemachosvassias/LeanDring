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
cdd tier, chunk 30: 60 columns.
-/

-- machine-emitted data: silence style linters (generated long lines, file-level options)
set_option linter.style.longLine false

namespace LeanDring.P5Presentation

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

def colCertDiv_147_78_11 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨78, by decide⟩
  m := 1
  T1 := T147_78
  T2 := Q2.T147_78_2
  h1 := (2,2,1,1,3)
  h2 := (2,2,1,1,0)
  D1 := [[2, 2, 1, 2, 0]]
  D2 := [[2, 2, 1, 2, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_78_12 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨78, by decide⟩
  m := 1
  T1 := T147_78
  T2 := Q2.T147_78_2
  h1 := (2,2,2,3,3)
  h2 := (2,2,2,3,0)
  D1 := [[2, 2, 2, 4, 4]]
  D2 := [[2, 2, 2, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_78_13 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨78, by decide⟩
  m := 1
  T1 := T147_78
  T2 := Q2.T147_78_2
  h1 := (2,2,3,0,3)
  h2 := (2,2,3,0,0)
  D1 := [[2, 2, 3, 1, 3]]
  D2 := [[2, 2, 3, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_78_14 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨78, by decide⟩
  m := 1
  T1 := T147_78
  T2 := Q2.T147_78_2
  h1 := (2,2,4,2,3)
  h2 := (2,2,4,2,0)
  D1 := [[2, 2, 4, 3, 2]]
  D2 := [[2, 2, 4, 3, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_78_15 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨78, by decide⟩
  m := 1
  T1 := T147_78
  T2 := Q2.T147_78_2
  h1 := (3,3,0,0,4)
  h2 := (3,3,0,0,2)
  D1 := [[3, 3, 0, 1, 2]]
  D2 := [[3, 3, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_78_16 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨78, by decide⟩
  m := 1
  T1 := T147_78
  T2 := Q2.T147_78_2
  h1 := (3,3,1,2,4)
  h2 := (3,3,1,2,2)
  D1 := [[3, 3, 1, 3, 3]]
  D2 := [[3, 3, 1, 3, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_78_17 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨78, by decide⟩
  m := 1
  T1 := T147_78
  T2 := Q2.T147_78_2
  h1 := (3,3,2,4,4)
  h2 := (3,3,2,4,2)
  D1 := [[3, 3, 2, 0, 4]]
  D2 := [[3, 3, 2, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_78_18 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨78, by decide⟩
  m := 1
  T1 := T147_78
  T2 := Q2.T147_78_2
  h1 := (3,3,3,1,4)
  h2 := (3,3,3,1,2)
  D1 := [[3, 3, 3, 2, 0]]
  D2 := [[3, 3, 3, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_78_19 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨78, by decide⟩
  m := 1
  T1 := T147_78
  T2 := Q2.T147_78_2
  h1 := (3,3,4,3,4)
  h2 := (3,3,4,3,2)
  D1 := [[3, 3, 4, 4, 1]]
  D2 := [[3, 3, 4, 4, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_78_20 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨78, by decide⟩
  m := 1
  T1 := T147_78
  T2 := Q2.T147_78_2
  h1 := (4,4,0,2,1)
  h2 := (4,4,0,2,0)
  D1 := [[4, 4, 0, 1, 3]]
  D2 := [[4, 4, 0, 1, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_78_21 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨78, by decide⟩
  m := 1
  T1 := T147_78
  T2 := Q2.T147_78_2
  h1 := (4,4,1,4,1)
  h2 := (4,4,1,4,0)
  D1 := [[4, 4, 1, 3, 1]]
  D2 := [[4, 4, 1, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_78_22 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨78, by decide⟩
  m := 1
  T1 := T147_78
  T2 := Q2.T147_78_2
  h1 := (4,4,2,1,1)
  h2 := (4,4,2,1,0)
  D1 := [[4, 4, 2, 0, 4]]
  D2 := [[4, 4, 2, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_78_23 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨78, by decide⟩
  m := 1
  T1 := T147_78
  T2 := Q2.T147_78_2
  h1 := (4,4,3,3,1)
  h2 := (4,4,3,3,0)
  D1 := [[4, 4, 3, 2, 2]]
  D2 := [[4, 4, 3, 2, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_78_24 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨78, by decide⟩
  m := 1
  T1 := T147_78
  T2 := Q2.T147_78_2
  h1 := (4,4,4,0,1)
  h2 := (4,4,4,0,0)
  D1 := [[4, 4, 4, 4, 0]]
  D2 := [[4, 4, 4, 4, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_91_10 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨91, by decide⟩
  m := 1
  T1 := T147_91
  T2 := Q2.T147_91_2
  h1 := (2,3,2,2,2)
  h2 := (2,3,2,2,3)
  D1 := [[2, 3, 2, 1, 1]]
  D2 := [[2, 3, 2, 1, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_91_15 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨91, by decide⟩
  m := 1
  T1 := T147_91
  T2 := Q2.T147_91_2
  h1 := (3,2,3,4,2)
  h2 := (3,2,3,4,4)
  D1 := [[3, 2, 3, 3, 1]]
  D2 := [[3, 2, 3, 3, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_91_20 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨91, by decide⟩
  m := 1
  T1 := T147_91
  T2 := Q2.T147_91_2
  h1 := (4,1,4,0,3)
  h2 := (4,1,4,0,1)
  D1 := [[4, 1, 4, 1, 4]]
  D2 := [[4, 1, 4, 1, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_92_15 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨92, by decide⟩
  m := 1
  T1 := T147_92
  T2 := Q2.T147_92_2
  h1 := (3,1,4,0,1)
  h2 := (3,1,4,0,2)
  D1 := [[3, 1, 4, 2, 3]]
  D2 := [[3, 1, 4, 2, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_92_20 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨92, by decide⟩
  m := 1
  T1 := T147_92
  T2 := Q2.T147_92_2
  h1 := (4,3,2,4,1)
  h2 := (4,3,2,4,2)
  D1 := [[4, 3, 2, 2, 4]]
  D2 := [[4, 3, 2, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_93_10 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨93, by decide⟩
  m := 1
  T1 := T147_93
  T2 := Q2.T147_93_2
  h1 := (2,1,4,0,1)
  h2 := (2,1,4,0,2)
  D1 := [[2, 1, 4, 3, 0]]
  D2 := [[2, 1, 4, 3, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_93_15 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨93, by decide⟩
  m := 1
  T1 := T147_93
  T2 := Q2.T147_93_2
  h1 := (3,4,1,2,2)
  h2 := (3,4,1,2,3)
  D1 := [[3, 4, 1, 0, 1]]
  D2 := [[3, 4, 1, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_93_20 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨93, by decide⟩
  m := 1
  T1 := T147_93
  T2 := Q2.T147_93_2
  h1 := (4,2,3,2,2)
  h2 := (4,2,3,2,4)
  D1 := [[4, 2, 3, 4, 3]]
  D2 := [[4, 2, 3, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_96_10 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨96, by decide⟩
  m := 1
  T1 := T147_96
  T2 := Q2.T147_96_2
  h1 := (2,3,1,2,1)
  h2 := (2,3,1,2,2)
  D1 := [[2, 3, 1, 1, 3]]
  D2 := [[2, 3, 1, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_96_15 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨96, by decide⟩
  m := 1
  T1 := T147_96
  T2 := Q2.T147_96_2
  h1 := (3,2,4,4,0)
  h2 := (3,2,4,4,2)
  D1 := [[3, 2, 4, 3, 2]]
  D2 := [[3, 2, 4, 3, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_96_20 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨96, by decide⟩
  m := 1
  T1 := T147_96
  T2 := Q2.T147_96_2
  h1 := (4,1,2,0,3)
  h2 := (4,1,2,0,1)
  D1 := [[4, 1, 2, 1, 1]]
  D2 := [[4, 1, 2, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_97_15 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨97, by decide⟩
  m := 1
  T1 := T147_97
  T2 := Q2.T147_97_2
  h1 := (3,1,2,0,1)
  h2 := (3,1,2,0,2)
  D1 := [[3, 1, 2, 2, 0]]
  D2 := [[3, 1, 2, 2, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_97_20 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨97, by decide⟩
  m := 1
  T1 := T147_97
  T2 := Q2.T147_97_2
  h1 := (4,3,1,4,0)
  h2 := (4,3,1,4,1)
  D1 := [[4, 3, 1, 2, 1]]
  D2 := [[4, 3, 1, 2, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_98_10 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨98, by decide⟩
  m := 1
  T1 := T147_98
  T2 := Q2.T147_98_2
  h1 := (2,1,2,0,1)
  h2 := (2,1,2,0,2)
  D1 := [[2, 1, 2, 3, 2]]
  D2 := [[2, 1, 2, 3, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_98_15 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨98, by decide⟩
  m := 1
  T1 := T147_98
  T2 := Q2.T147_98_2
  h1 := (3,4,3,2,0)
  h2 := (3,4,3,2,1)
  D1 := [[3, 4, 3, 0, 1]]
  D2 := [[3, 4, 3, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_98_20 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨98, by decide⟩
  m := 1
  T1 := T147_98
  T2 := Q2.T147_98_2
  h1 := (4,2,4,2,0)
  h2 := (4,2,4,2,2)
  D1 := [[4, 2, 4, 4, 4]]
  D2 := [[4, 2, 4, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_101_10 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨101, by decide⟩
  m := 1
  T1 := T147_101
  T2 := Q2.T147_101_2
  h1 := (2,3,4,2,4)
  h2 := (2,3,4,2,0)
  D1 := [[2, 3, 4, 1, 2]]
  D2 := [[2, 3, 4, 1, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_101_15 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨101, by decide⟩
  m := 1
  T1 := T147_101
  T2 := Q2.T147_101_2
  h1 := (3,2,1,4,1)
  h2 := (3,2,1,4,3)
  D1 := [[3, 2, 1, 3, 4]]
  D2 := [[3, 2, 1, 3, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_101_20 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨101, by decide⟩
  m := 1
  T1 := T147_101
  T2 := Q2.T147_101_2
  h1 := (4,1,3,0,3)
  h2 := (4,1,3,0,1)
  D1 := [[4, 1, 3, 1, 0]]
  D2 := [[4, 1, 3, 1, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_102_15 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨102, by decide⟩
  m := 1
  T1 := T147_102
  T2 := Q2.T147_102_2
  h1 := (3,1,3,0,1)
  h2 := (3,1,3,0,2)
  D1 := [[3, 1, 3, 2, 4]]
  D2 := [[3, 1, 3, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_102_20 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨102, by decide⟩
  m := 1
  T1 := T147_102
  T2 := Q2.T147_102_2
  h1 := (4,3,4,4,3)
  h2 := (4,3,4,4,4)
  D1 := [[4, 3, 4, 2, 0]]
  D2 := [[4, 3, 4, 2, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_103_10 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨103, by decide⟩
  m := 1
  T1 := T147_103
  T2 := Q2.T147_103_2
  h1 := (2,1,3,0,1)
  h2 := (2,1,3,0,2)
  D1 := [[2, 1, 3, 3, 1]]
  D2 := [[2, 1, 3, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_103_15 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨103, by decide⟩
  m := 1
  T1 := T147_103
  T2 := Q2.T147_103_2
  h1 := (3,4,2,2,1)
  h2 := (3,4,2,2,2)
  D1 := [[3, 4, 2, 0, 1]]
  D2 := [[3, 4, 2, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_103_20 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨103, by decide⟩
  m := 1
  T1 := T147_103
  T2 := Q2.T147_103_2
  h1 := (4,2,1,2,1)
  h2 := (4,2,1,2,3)
  D1 := [[4, 2, 1, 4, 1]]
  D2 := [[4, 2, 1, 4, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_106_10 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨106, by decide⟩
  m := 1
  T1 := T147_106
  T2 := Q2.T147_106_2
  h1 := (2,3,3,2,3)
  h2 := (2,3,3,2,4)
  D1 := [[2, 3, 3, 1, 4]]
  D2 := [[2, 3, 3, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_106_15 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨106, by decide⟩
  m := 1
  T1 := T147_106
  T2 := Q2.T147_106_2
  h1 := (3,2,2,4,4)
  h2 := (3,2,2,4,1)
  D1 := [[3, 2, 2, 3, 0]]
  D2 := [[3, 2, 2, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_106_20 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨106, by decide⟩
  m := 1
  T1 := T147_106
  T2 := Q2.T147_106_2
  h1 := (4,1,1,0,3)
  h2 := (4,1,1,0,1)
  D1 := [[4, 1, 1, 1, 2]]
  D2 := [[4, 1, 1, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_107_15 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨107, by decide⟩
  m := 1
  T1 := T147_107
  T2 := Q2.T147_107_2
  h1 := (3,1,1,0,1)
  h2 := (3,1,1,0,2)
  D1 := [[3, 1, 1, 2, 1]]
  D2 := [[3, 1, 1, 2, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_107_20 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨107, by decide⟩
  m := 1
  T1 := T147_107
  T2 := Q2.T147_107_2
  h1 := (4,3,3,4,2)
  h2 := (4,3,3,4,3)
  D1 := [[4, 3, 3, 2, 2]]
  D2 := [[4, 3, 3, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_108_10 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨108, by decide⟩
  m := 1
  T1 := T147_108
  T2 := Q2.T147_108_2
  h1 := (2,1,1,0,1)
  h2 := (2,1,1,0,2)
  D1 := [[2, 1, 1, 3, 3]]
  D2 := [[2, 1, 1, 3, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_108_15 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨108, by decide⟩
  m := 1
  T1 := T147_108
  T2 := Q2.T147_108_2
  h1 := (3,4,4,2,4)
  h2 := (3,4,4,2,0)
  D1 := [[3, 4, 4, 0, 1]]
  D2 := [[3, 4, 4, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_108_20 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨108, by decide⟩
  m := 1
  T1 := T147_108
  T2 := Q2.T147_108_2
  h1 := (4,2,2,2,4)
  h2 := (4,2,2,2,1)
  D1 := [[4, 2, 2, 4, 2]]
  D2 := [[4, 2, 2, 4, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_111_10 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨111, by decide⟩
  m := 1
  T1 := T147_111
  T2 := Q2.T147_111_2
  h1 := (2,3,0,2,0)
  h2 := (2,3,0,2,1)
  D1 := [[2, 3, 0, 1, 0]]
  D2 := [[2, 3, 0, 1, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_111_15 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨111, by decide⟩
  m := 1
  T1 := T147_111
  T2 := Q2.T147_111_2
  h1 := (3,2,0,4,3)
  h2 := (3,2,0,4,0)
  D1 := [[3, 2, 0, 3, 3]]
  D2 := [[3, 2, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_111_20 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨111, by decide⟩
  m := 1
  T1 := T147_111
  T2 := Q2.T147_111_2
  h1 := (4,1,0,0,3)
  h2 := (4,1,0,0,1)
  D1 := [[4, 1, 0, 1, 3]]
  D2 := [[4, 1, 0, 1, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_112_15 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨112, by decide⟩
  m := 1
  T1 := T147_112
  T2 := Q2.T147_112_2
  h1 := (3,1,0,0,1)
  h2 := (3,1,0,0,2)
  D1 := [[3, 1, 0, 2, 2]]
  D2 := [[3, 1, 0, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_112_20 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨112, by decide⟩
  m := 1
  T1 := T147_112
  T2 := Q2.T147_112_2
  h1 := (4,3,0,4,4)
  h2 := (4,3,0,4,0)
  D1 := [[4, 3, 0, 2, 3]]
  D2 := [[4, 3, 0, 2, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_113_10 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨113, by decide⟩
  m := 1
  T1 := T147_113
  T2 := Q2.T147_113_2
  h1 := (2,1,0,0,1)
  h2 := (2,1,0,0,2)
  D1 := [[2, 1, 0, 3, 4]]
  D2 := [[2, 1, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_113_15 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨113, by decide⟩
  m := 1
  T1 := T147_113
  T2 := Q2.T147_113_2
  h1 := (3,4,0,2,3)
  h2 := (3,4,0,2,4)
  D1 := [[3, 4, 0, 0, 1]]
  D2 := [[3, 4, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_113_20 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨113, by decide⟩
  m := 1
  T1 := T147_113
  T2 := Q2.T147_113_2
  h1 := (4,2,0,2,3)
  h2 := (4,2,0,2,0)
  D1 := [[4, 2, 0, 4, 0]]
  D2 := [[4, 2, 0, 4, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_117_50 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨117, by decide⟩
  m := 1
  T1 := T147_117
  T2 := Q2.T147_117_2
  h1 := (2,3,0,2,0)
  h2 := (2,3,0,2,1)
  D1 := [[2, 3, 0, 1, 0]]
  D2 := [[2, 3, 0, 1, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_117_55 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨117, by decide⟩
  m := 1
  T1 := T147_117
  T2 := Q2.T147_117_2
  h1 := (2,3,1,2,0)
  h2 := (2,3,1,2,1)
  D1 := [[2, 3, 1, 1, 2]]
  D2 := [[2, 3, 1, 1, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_117_60 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨117, by decide⟩
  m := 1
  T1 := T147_117
  T2 := Q2.T147_117_2
  h1 := (2,3,2,2,0)
  h2 := (2,3,2,2,1)
  D1 := [[2, 3, 2, 1, 4]]
  D2 := [[2, 3, 2, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_117_65 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨117, by decide⟩
  m := 1
  T1 := T147_117
  T2 := Q2.T147_117_2
  h1 := (2,3,3,2,0)
  h2 := (2,3,3,2,1)
  D1 := [[2, 3, 3, 1, 1]]
  D2 := [[2, 3, 3, 1, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_117_70 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨117, by decide⟩
  m := 1
  T1 := T147_117
  T2 := Q2.T147_117_2
  h1 := (2,3,4,2,0)
  h2 := (2,3,4,2,1)
  D1 := [[2, 3, 4, 1, 3]]
  D2 := [[2, 3, 4, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_147_117_75 : ColCertDiv where
  rK := ⟨147, by decide⟩
  rH := ⟨117, by decide⟩
  m := 1
  T1 := T147_117
  T2 := Q2.T147_117_2
  h1 := (3,2,0,4,3)
  h2 := (3,2,0,4,0)
  D1 := [[3, 2, 0, 3, 3]]
  D2 := [[3, 2, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

end LeanDring.P5Presentation
