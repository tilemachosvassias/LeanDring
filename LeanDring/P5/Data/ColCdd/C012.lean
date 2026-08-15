/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.Twin1.ColCert
import LeanDring.P5.Data.EntryK.C032
import LeanDring.P5.Data.EntryK.C033

/-!
# Species-table cell data, stage 2 — column-data-divergent columns

Per-column certified exponent-vector data (`ColCert`/`ColCertDiv`) with kernel
`decide` bindings. Emitted; the embedded lists are what the kernel certifies.
cdd tier, chunk 11: 60 columns.
-/

-- machine-emitted data: silence style linters (generated long lines, file-level options)
set_option linter.style.longLine false

namespace LeanDring.P5Presentation

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

def colCertDiv_127_49_20 : ColCertDiv where
  rK := ⟨127, by decide⟩
  rH := ⟨49, by decide⟩
  m := 5
  T1 := T127_49
  T2 := Q2.T127_49_2
  h1 := (4,1,0,1,3)
  h2 := (4,1,0,1,1)
  D1 := [[4, 1, 1, 0], [4, 1, 1, 4], [4, 1, 1, 3], [4, 1, 1, 2], [4, 1, 1, 1]]
  D2 := [[4, 1, 1, 3], [4, 1, 1, 2], [4, 1, 1, 1], [4, 1, 1, 0], [4, 1, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_127_82_5 : ColCertDiv where
  rK := ⟨127, by decide⟩
  rH := ⟨82, by decide⟩
  m := 5
  T1 := T127_82
  T2 := Q2.T127_82_2
  h1 := (1,0,2,0,0)
  h2 := (1,0,2,0,0)
  D1 := [[1, 0, 1, 0], [1, 0, 1, 0], [1, 0, 1, 0], [1, 0, 1, 0], [1, 0, 1, 0]]
  D2 := [[1, 0, 1, 4], [1, 0, 1, 4], [1, 0, 1, 4], [1, 0, 1, 4], [1, 0, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_127_82_10 : ColCertDiv where
  rK := ⟨127, by decide⟩
  rH := ⟨82, by decide⟩
  m := 5
  T1 := T127_82
  T2 := Q2.T127_82_2
  h1 := (2,0,4,0,0)
  h2 := (2,0,4,0,0)
  D1 := [[2, 0, 2, 4], [2, 0, 2, 4], [2, 0, 2, 4], [2, 0, 2, 4], [2, 0, 2, 4]]
  D2 := [[2, 0, 2, 2], [2, 0, 2, 2], [2, 0, 2, 2], [2, 0, 2, 2], [2, 0, 2, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_127_82_15 : ColCertDiv where
  rK := ⟨127, by decide⟩
  rH := ⟨82, by decide⟩
  m := 5
  T1 := T127_82
  T2 := Q2.T127_82_2
  h1 := (3,0,1,0,0)
  h2 := (3,0,1,0,0)
  D1 := [[3, 0, 3, 2], [3, 0, 3, 2], [3, 0, 3, 2], [3, 0, 3, 2], [3, 0, 3, 2]]
  D2 := [[3, 0, 3, 4], [3, 0, 3, 4], [3, 0, 3, 4], [3, 0, 3, 4], [3, 0, 3, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_127_82_20 : ColCertDiv where
  rK := ⟨127, by decide⟩
  rH := ⟨82, by decide⟩
  m := 5
  T1 := T127_82
  T2 := Q2.T127_82_2
  h1 := (4,0,3,0,0)
  h2 := (4,0,3,0,0)
  D1 := [[4, 0, 4, 4], [4, 0, 4, 4], [4, 0, 4, 4], [4, 0, 4, 4], [4, 0, 4, 4]]
  D2 := [[4, 0, 4, 0], [4, 0, 4, 0], [4, 0, 4, 0], [4, 0, 4, 0], [4, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_127_94_5 : ColCertDiv where
  rK := ⟨127, by decide⟩
  rH := ⟨94, by decide⟩
  m := 5
  T1 := T127_94
  T2 := Q2.T127_94_2
  h1 := (1,1,4,0,0)
  h2 := (1,1,4,0,0)
  D1 := [[1, 1, 0, 3], [1, 1, 0, 2], [1, 1, 0, 1], [1, 1, 0, 0], [1, 1, 0, 4]]
  D2 := [[1, 1, 0, 1], [1, 1, 0, 0], [1, 1, 0, 4], [1, 1, 0, 3], [1, 1, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_127_94_10 : ColCertDiv where
  rK := ⟨127, by decide⟩
  rH := ⟨94, by decide⟩
  m := 5
  T1 := T127_94
  T2 := Q2.T127_94_2
  h1 := (2,2,3,1,4)
  h2 := (2,2,3,1,4)
  D1 := [[2, 2, 4, 4], [2, 2, 4, 2], [2, 2, 4, 0], [2, 2, 4, 3], [2, 2, 4, 1]]
  D2 := [[2, 2, 4, 0], [2, 2, 4, 3], [2, 2, 4, 1], [2, 2, 4, 4], [2, 2, 4, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_127_94_15 : ColCertDiv where
  rK := ⟨127, by decide⟩
  rH := ⟨94, by decide⟩
  m := 5
  T1 := T127_94
  T2 := Q2.T127_94_2
  h1 := (3,3,2,3,3)
  h2 := (3,3,2,3,3)
  D1 := [[3, 3, 2, 4], [3, 3, 2, 1], [3, 3, 2, 3], [3, 3, 2, 0], [3, 3, 2, 2]]
  D2 := [[3, 3, 2, 3], [3, 3, 2, 0], [3, 3, 2, 2], [3, 3, 2, 4], [3, 3, 2, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_127_94_20 : ColCertDiv where
  rK := ⟨127, by decide⟩
  rH := ⟨94, by decide⟩
  m := 5
  T1 := T127_94
  T2 := Q2.T127_94_2
  h1 := (4,4,1,1,3)
  h2 := (4,4,1,1,3)
  D1 := [[4, 4, 4, 4], [4, 4, 4, 0], [4, 4, 4, 1], [4, 4, 4, 2], [4, 4, 4, 3]]
  D2 := [[4, 4, 4, 1], [4, 4, 4, 2], [4, 4, 4, 3], [4, 4, 4, 4], [4, 4, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_127_95_25 : ColCertDiv where
  rK := ⟨127, by decide⟩
  rH := ⟨95, by decide⟩
  m := 5
  T1 := T127_95
  T2 := Q2.T127_95_2
  h1 := (0,1,2,0,0)
  h2 := (0,1,2,0,0)
  D1 := [[0, 1, 0, 2], [0, 1, 0, 1], [0, 1, 0, 0], [0, 1, 0, 4], [0, 1, 0, 3]]
  D2 := [[0, 1, 0, 1], [0, 1, 0, 0], [0, 1, 0, 4], [0, 1, 0, 3], [0, 1, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_127_95_50 : ColCertDiv where
  rK := ⟨127, by decide⟩
  rH := ⟨95, by decide⟩
  m := 5
  T1 := T127_95
  T2 := Q2.T127_95_2
  h1 := (0,2,4,0,2)
  h2 := (0,2,4,0,2)
  D1 := [[0, 2, 0, 4], [0, 2, 0, 2], [0, 2, 0, 0], [0, 2, 0, 3], [0, 2, 0, 1]]
  D2 := [[0, 2, 0, 2], [0, 2, 0, 0], [0, 2, 0, 3], [0, 2, 0, 1], [0, 2, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_127_95_75 : ColCertDiv where
  rK := ⟨127, by decide⟩
  rH := ⟨95, by decide⟩
  m := 5
  T1 := T127_95
  T2 := Q2.T127_95_2
  h1 := (0,3,1,0,1)
  h2 := (0,3,1,0,1)
  D1 := [[0, 3, 0, 1], [0, 3, 0, 3], [0, 3, 0, 0], [0, 3, 0, 2], [0, 3, 0, 4]]
  D2 := [[0, 3, 0, 3], [0, 3, 0, 0], [0, 3, 0, 2], [0, 3, 0, 4], [0, 3, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_127_95_100 : ColCertDiv where
  rK := ⟨127, by decide⟩
  rH := ⟨95, by decide⟩
  m := 5
  T1 := T127_95
  T2 := Q2.T127_95_2
  h1 := (0,4,3,0,2)
  h2 := (0,4,3,0,2)
  D1 := [[0, 4, 0, 3], [0, 4, 0, 4], [0, 4, 0, 0], [0, 4, 0, 1], [0, 4, 0, 2]]
  D2 := [[0, 4, 0, 4], [0, 4, 0, 0], [0, 4, 0, 1], [0, 4, 0, 2], [0, 4, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_127_102_5 : ColCertDiv where
  rK := ⟨127, by decide⟩
  rH := ⟨102, by decide⟩
  m := 5
  T1 := T127_102
  T2 := Q2.T127_102_2
  h1 := (1,2,1,3,1)
  h2 := (1,2,1,3,1)
  D1 := [[1, 2, 2, 2], [1, 2, 2, 0], [1, 2, 2, 3], [1, 2, 2, 1], [1, 2, 2, 4]]
  D2 := [[1, 2, 2, 4], [1, 2, 2, 2], [1, 2, 2, 0], [1, 2, 2, 3], [1, 2, 2, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_127_102_10 : ColCertDiv where
  rK := ⟨127, by decide⟩
  rH := ⟨102, by decide⟩
  m := 5
  T1 := T127_102
  T2 := Q2.T127_102_2
  h1 := (2,4,2,3,2)
  h2 := (2,4,2,3,2)
  D1 := [[2, 4, 2, 3], [2, 4, 2, 4], [2, 4, 2, 0], [2, 4, 2, 1], [2, 4, 2, 2]]
  D2 := [[2, 4, 2, 2], [2, 4, 2, 3], [2, 4, 2, 4], [2, 4, 2, 0], [2, 4, 2, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_127_102_15 : ColCertDiv where
  rK := ⟨127, by decide⟩
  rH := ⟨102, by decide⟩
  m := 5
  T1 := T127_102
  T2 := Q2.T127_102_2
  h1 := (3,1,3,0,1)
  h2 := (3,1,3,0,2)
  D1 := [[3, 1, 0, 1], [3, 1, 0, 0], [3, 1, 0, 4], [3, 1, 0, 3], [3, 1, 0, 2]]
  D2 := [[3, 1, 0, 3], [3, 1, 0, 2], [3, 1, 0, 1], [3, 1, 0, 0], [3, 1, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_127_102_20 : ColCertDiv where
  rK := ⟨127, by decide⟩
  rH := ⟨102, by decide⟩
  m := 5
  T1 := T127_102
  T2 := Q2.T127_102_2
  h1 := (4,3,4,4,3)
  h2 := (4,3,4,4,4)
  D1 := [[4, 3, 1, 1], [4, 3, 1, 3], [4, 3, 1, 0], [4, 3, 1, 2], [4, 3, 1, 4]]
  D2 := [[4, 3, 1, 0], [4, 3, 1, 2], [4, 3, 1, 4], [4, 3, 1, 1], [4, 3, 1, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_127_108_5 : ColCertDiv where
  rK := ⟨127, by decide⟩
  rH := ⟨108, by decide⟩
  m := 5
  T1 := T127_108
  T2 := Q2.T127_108_2
  h1 := (1,3,3,1,0)
  h2 := (1,3,3,1,0)
  D1 := [[1, 3, 4, 2], [1, 3, 4, 4], [1, 3, 4, 1], [1, 3, 4, 3], [1, 3, 4, 0]]
  D2 := [[1, 3, 4, 3], [1, 3, 4, 0], [1, 3, 4, 2], [1, 3, 4, 4], [1, 3, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_127_108_10 : ColCertDiv where
  rK := ⟨127, by decide⟩
  rH := ⟨108, by decide⟩
  m := 5
  T1 := T127_108
  T2 := Q2.T127_108_2
  h1 := (2,1,1,0,1)
  h2 := (2,1,1,0,2)
  D1 := [[2, 1, 0, 0], [2, 1, 0, 4], [2, 1, 0, 3], [2, 1, 0, 2], [2, 1, 0, 1]]
  D2 := [[2, 1, 0, 3], [2, 1, 0, 2], [2, 1, 0, 1], [2, 1, 0, 0], [2, 1, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_127_108_15 : ColCertDiv where
  rK := ⟨127, by decide⟩
  rH := ⟨108, by decide⟩
  m := 5
  T1 := T127_108
  T2 := Q2.T127_108_2
  h1 := (3,4,4,2,4)
  h2 := (3,4,4,2,0)
  D1 := [[3, 4, 3, 0], [3, 4, 3, 1], [3, 4, 3, 2], [3, 4, 3, 3], [3, 4, 3, 4]]
  D2 := [[3, 4, 3, 4], [3, 4, 3, 0], [3, 4, 3, 1], [3, 4, 3, 2], [3, 4, 3, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_127_108_20 : ColCertDiv where
  rK := ⟨127, by decide⟩
  rH := ⟨108, by decide⟩
  m := 5
  T1 := T127_108
  T2 := Q2.T127_108_2
  h1 := (4,2,2,2,4)
  h2 := (4,2,2,2,1)
  D1 := [[4, 2, 3, 2], [4, 2, 3, 0], [4, 2, 3, 3], [4, 2, 3, 1], [4, 2, 3, 4]]
  D2 := [[4, 2, 3, 3], [4, 2, 3, 1], [4, 2, 3, 4], [4, 2, 3, 2], [4, 2, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_127_111_10 : ColCertDiv where
  rK := ⟨127, by decide⟩
  rH := ⟨111, by decide⟩
  m := 5
  T1 := T127_111
  T2 := Q2.T127_111_2
  h1 := (2,3,0,2,0)
  h2 := (2,3,0,2,1)
  D1 := [[2, 3, 3, 4], [2, 3, 3, 1], [2, 3, 3, 3], [2, 3, 3, 0], [2, 3, 3, 2]]
  D2 := [[2, 3, 3, 0], [2, 3, 3, 2], [2, 3, 3, 4], [2, 3, 3, 1], [2, 3, 3, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_127_111_15 : ColCertDiv where
  rK := ⟨127, by decide⟩
  rH := ⟨111, by decide⟩
  m := 5
  T1 := T127_111
  T2 := Q2.T127_111_2
  h1 := (3,2,0,4,3)
  h2 := (3,2,0,4,0)
  D1 := [[3, 2, 1, 2], [3, 2, 1, 0], [3, 2, 1, 3], [3, 2, 1, 1], [3, 2, 1, 4]]
  D2 := [[3, 2, 1, 4], [3, 2, 1, 2], [3, 2, 1, 0], [3, 2, 1, 3], [3, 2, 1, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_127_111_20 : ColCertDiv where
  rK := ⟨127, by decide⟩
  rH := ⟨111, by decide⟩
  m := 5
  T1 := T127_111
  T2 := Q2.T127_111_2
  h1 := (4,1,0,0,3)
  h2 := (4,1,0,0,1)
  D1 := [[4, 1, 0, 4], [4, 1, 0, 3], [4, 1, 0, 2], [4, 1, 0, 1], [4, 1, 0, 0]]
  D2 := [[4, 1, 0, 2], [4, 1, 0, 1], [4, 1, 0, 0], [4, 1, 0, 4], [4, 1, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_128_3_1 : ColCertDiv where
  rK := ⟨128, by decide⟩
  rH := ⟨3, by decide⟩
  m := 5
  T1 := T128_3
  T2 := Q2.T128_3_2
  h1 := (1,0,2,3,1)
  h2 := (1,0,2,3,1)
  D1 := [[1, 0, 0, 0], [1, 0, 0, 0], [1, 0, 0, 0], [1, 0, 0, 0], [1, 0, 0, 0]]
  D2 := [[1, 0, 0, 1], [1, 0, 0, 1], [1, 0, 0, 1], [1, 0, 0, 1], [1, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_128_3_2 : ColCertDiv where
  rK := ⟨128, by decide⟩
  rH := ⟨3, by decide⟩
  m := 5
  T1 := T128_3
  T2 := Q2.T128_3_2
  h1 := (2,0,4,1,0)
  h2 := (2,0,4,1,0)
  D1 := [[2, 0, 0, 0], [2, 0, 0, 0], [2, 0, 0, 0], [2, 0, 0, 0], [2, 0, 0, 0]]
  D2 := [[2, 0, 0, 2], [2, 0, 0, 2], [2, 0, 0, 2], [2, 0, 0, 2], [2, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_128_3_3 : ColCertDiv where
  rK := ⟨128, by decide⟩
  rH := ⟨3, by decide⟩
  m := 5
  T1 := T128_3
  T2 := Q2.T128_3_2
  h1 := (3,0,1,4,2)
  h2 := (3,0,1,4,2)
  D1 := [[3, 0, 0, 0], [3, 0, 0, 0], [3, 0, 0, 0], [3, 0, 0, 0], [3, 0, 0, 0]]
  D2 := [[3, 0, 0, 3], [3, 0, 0, 3], [3, 0, 0, 3], [3, 0, 0, 3], [3, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_128_3_4 : ColCertDiv where
  rK := ⟨128, by decide⟩
  rH := ⟨3, by decide⟩
  m := 5
  T1 := T128_3
  T2 := Q2.T128_3_2
  h1 := (4,0,3,2,2)
  h2 := (4,0,3,2,2)
  D1 := [[4, 0, 0, 0], [4, 0, 0, 0], [4, 0, 0, 0], [4, 0, 0, 0], [4, 0, 0, 0]]
  D2 := [[4, 0, 0, 4], [4, 0, 0, 4], [4, 0, 0, 4], [4, 0, 0, 4], [4, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_128_21_5 : ColCertDiv where
  rK := ⟨128, by decide⟩
  rH := ⟨21, by decide⟩
  m := 5
  T1 := T128_21
  T2 := Q2.T128_21_2
  h1 := (1,0,2,3,2)
  h2 := (1,0,2,3,2)
  D1 := [[1, 0, 0, 1], [1, 0, 0, 1], [1, 0, 0, 1], [1, 0, 0, 1], [1, 0, 0, 1]]
  D2 := [[1, 0, 0, 2], [1, 0, 0, 2], [1, 0, 0, 2], [1, 0, 0, 2], [1, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_128_21_10 : ColCertDiv where
  rK := ⟨128, by decide⟩
  rH := ⟨21, by decide⟩
  m := 5
  T1 := T128_21
  T2 := Q2.T128_21_2
  h1 := (2,0,4,1,2)
  h2 := (2,0,4,1,2)
  D1 := [[2, 0, 0, 2], [2, 0, 0, 2], [2, 0, 0, 2], [2, 0, 0, 2], [2, 0, 0, 2]]
  D2 := [[2, 0, 0, 4], [2, 0, 0, 4], [2, 0, 0, 4], [2, 0, 0, 4], [2, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_128_21_15 : ColCertDiv where
  rK := ⟨128, by decide⟩
  rH := ⟨21, by decide⟩
  m := 5
  T1 := T128_21
  T2 := Q2.T128_21_2
  h1 := (3,0,1,4,0)
  h2 := (3,0,1,4,0)
  D1 := [[3, 0, 0, 3], [3, 0, 0, 3], [3, 0, 0, 3], [3, 0, 0, 3], [3, 0, 0, 3]]
  D2 := [[3, 0, 0, 1], [3, 0, 0, 1], [3, 0, 0, 1], [3, 0, 0, 1], [3, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_128_21_20 : ColCertDiv where
  rK := ⟨128, by decide⟩
  rH := ⟨21, by decide⟩
  m := 5
  T1 := T128_21
  T2 := Q2.T128_21_2
  h1 := (4,0,3,2,1)
  h2 := (4,0,3,2,1)
  D1 := [[4, 0, 0, 4], [4, 0, 0, 4], [4, 0, 0, 4], [4, 0, 0, 4], [4, 0, 0, 4]]
  D2 := [[4, 0, 0, 3], [4, 0, 0, 3], [4, 0, 0, 3], [4, 0, 0, 3], [4, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_128_34_5 : ColCertDiv where
  rK := ⟨128, by decide⟩
  rH := ⟨34, by decide⟩
  m := 5
  T1 := T128_34
  T2 := Q2.T128_34_2
  h1 := (1,4,3,3,1)
  h2 := (1,4,3,3,1)
  D1 := [[1, 4, 1, 3], [1, 4, 1, 4], [1, 4, 1, 0], [1, 4, 1, 1], [1, 4, 1, 2]]
  D2 := [[1, 4, 1, 2], [1, 4, 1, 3], [1, 4, 1, 4], [1, 4, 1, 0], [1, 4, 1, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_128_34_10 : ColCertDiv where
  rK := ⟨128, by decide⟩
  rH := ⟨34, by decide⟩
  m := 5
  T1 := T128_34
  T2 := Q2.T128_34_2
  h1 := (2,3,1,0,3)
  h2 := (2,3,1,0,4)
  D1 := [[2, 3, 3, 3], [2, 3, 3, 0], [2, 3, 3, 2], [2, 3, 3, 4], [2, 3, 3, 1]]
  D2 := [[2, 3, 3, 2], [2, 3, 3, 4], [2, 3, 3, 1], [2, 3, 3, 3], [2, 3, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_128_34_15 : ColCertDiv where
  rK := ⟨128, by decide⟩
  rH := ⟨34, by decide⟩
  m := 5
  T1 := T128_34
  T2 := Q2.T128_34_2
  h1 := (3,2,4,1,4)
  h2 := (3,2,4,1,1)
  D1 := [[3, 2, 1, 3], [3, 2, 1, 1], [3, 2, 1, 4], [3, 2, 1, 2], [3, 2, 1, 0]]
  D2 := [[3, 2, 1, 2], [3, 2, 1, 0], [3, 2, 1, 3], [3, 2, 1, 1], [3, 2, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_128_34_20 : ColCertDiv where
  rK := ⟨128, by decide⟩
  rH := ⟨34, by decide⟩
  m := 5
  T1 := T128_34
  T2 := Q2.T128_34_2
  h1 := (4,1,2,1,3)
  h2 := (4,1,2,1,1)
  D1 := [[4, 1, 0, 2], [4, 1, 0, 1], [4, 1, 0, 0], [4, 1, 0, 4], [4, 1, 0, 3]]
  D2 := [[4, 1, 0, 1], [4, 1, 0, 0], [4, 1, 0, 4], [4, 1, 0, 3], [4, 1, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_128_41_5 : ColCertDiv where
  rK := ⟨128, by decide⟩
  rH := ⟨41, by decide⟩
  m := 5
  T1 := T128_41
  T2 := Q2.T128_41_2
  h1 := (1,3,4,0,0)
  h2 := (1,3,4,0,1)
  D1 := [[1, 3, 4, 4], [1, 3, 4, 1], [1, 3, 4, 3], [1, 3, 4, 0], [1, 3, 4, 2]]
  D2 := [[1, 3, 4, 2], [1, 3, 4, 4], [1, 3, 4, 1], [1, 3, 4, 3], [1, 3, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_128_41_10 : ColCertDiv where
  rK := ⟨128, by decide⟩
  rH := ⟨41, by decide⟩
  m := 5
  T1 := T128_41
  T2 := Q2.T128_41_2
  h1 := (2,1,3,3,3)
  h2 := (2,1,3,3,1)
  D1 := [[2, 1, 0, 4], [2, 1, 0, 3], [2, 1, 0, 2], [2, 1, 0, 1], [2, 1, 0, 0]]
  D2 := [[2, 1, 0, 1], [2, 1, 0, 0], [2, 1, 0, 4], [2, 1, 0, 3], [2, 1, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_128_41_20 : ColCertDiv where
  rK := ⟨128, by decide⟩
  rH := ⟨41, by decide⟩
  m := 5
  T1 := T128_41
  T2 := Q2.T128_41_2
  h1 := (4,2,1,3,1)
  h2 := (4,2,1,3,2)
  D1 := [[4, 2, 3, 0], [4, 2, 3, 3], [4, 2, 3, 1], [4, 2, 3, 4], [4, 2, 3, 2]]
  D2 := [[4, 2, 3, 4], [4, 2, 3, 2], [4, 2, 3, 0], [4, 2, 3, 3], [4, 2, 3, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_128_47_5 : ColCertDiv where
  rK := ⟨128, by decide⟩
  rH := ⟨47, by decide⟩
  m := 5
  T1 := T128_47
  T2 := Q2.T128_47_2
  h1 := (1,1,1,4,2)
  h2 := (1,1,1,4,0)
  D1 := [[1, 1, 0, 3], [1, 1, 0, 2], [1, 1, 0, 1], [1, 1, 0, 0], [1, 1, 0, 4]]
  D2 := [[1, 1, 0, 4], [1, 1, 0, 3], [1, 1, 0, 2], [1, 1, 0, 1], [1, 1, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_128_47_10 : ColCertDiv where
  rK := ⟨128, by decide⟩
  rH := ⟨47, by decide⟩
  m := 5
  T1 := T128_47
  T2 := Q2.T128_47_2
  h1 := (2,2,2,4,4)
  h2 := (2,2,2,4,0)
  D1 := [[2, 2, 4, 4], [2, 2, 4, 2], [2, 2, 4, 0], [2, 2, 4, 3], [2, 2, 4, 1]]
  D2 := [[2, 2, 4, 1], [2, 2, 4, 4], [2, 2, 4, 2], [2, 2, 4, 0], [2, 2, 4, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_128_47_15 : ColCertDiv where
  rK := ⟨128, by decide⟩
  rH := ⟨47, by decide⟩
  m := 5
  T1 := T128_47
  T2 := Q2.T128_47_2
  h1 := (3,3,3,0,2)
  h2 := (3,3,3,0,1)
  D1 := [[3, 3, 2, 4], [3, 3, 2, 1], [3, 3, 2, 3], [3, 3, 2, 0], [3, 3, 2, 2]]
  D2 := [[3, 3, 2, 2], [3, 3, 2, 4], [3, 3, 2, 1], [3, 3, 2, 3], [3, 3, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_128_47_20 : ColCertDiv where
  rK := ⟨128, by decide⟩
  rH := ⟨47, by decide⟩
  m := 5
  T1 := T128_47
  T2 := Q2.T128_47_2
  h1 := (4,4,4,2,2)
  h2 := (4,4,4,2,4)
  D1 := [[4, 4, 4, 4], [4, 4, 4, 0], [4, 4, 4, 1], [4, 4, 4, 2], [4, 4, 4, 3]]
  D2 := [[4, 4, 4, 3], [4, 4, 4, 4], [4, 4, 4, 0], [4, 4, 4, 1], [4, 4, 4, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_128_50_5 : ColCertDiv where
  rK := ⟨128, by decide⟩
  rH := ⟨50, by decide⟩
  m := 5
  T1 := T128_50
  T2 := Q2.T128_50_2
  h1 := (1,2,0,2,2)
  h2 := (1,2,0,2,4)
  D1 := [[1, 2, 2, 4], [1, 2, 2, 2], [1, 2, 2, 0], [1, 2, 2, 3], [1, 2, 2, 1]]
  D2 := [[1, 2, 2, 1], [1, 2, 2, 4], [1, 2, 2, 2], [1, 2, 2, 0], [1, 2, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_128_50_10 : ColCertDiv where
  rK := ⟨128, by decide⟩
  rH := ⟨50, by decide⟩
  m := 5
  T1 := T128_50
  T2 := Q2.T128_50_2
  h1 := (2,4,0,1,1)
  h2 := (2,4,0,1,0)
  D1 := [[2, 4, 2, 2], [2, 4, 2, 3], [2, 4, 2, 4], [2, 4, 2, 0], [2, 4, 2, 1]]
  D2 := [[2, 4, 2, 1], [2, 4, 2, 2], [2, 4, 2, 3], [2, 4, 2, 4], [2, 4, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_128_50_15 : ColCertDiv where
  rK := ⟨128, by decide⟩
  rH := ⟨50, by decide⟩
  m := 5
  T1 := T128_50
  T2 := Q2.T128_50_2
  h1 := (3,1,0,2,0)
  h2 := (3,1,0,2,2)
  D1 := [[3, 1, 0, 2], [3, 1, 0, 1], [3, 1, 0, 0], [3, 1, 0, 4], [3, 1, 0, 3]]
  D2 := [[3, 1, 0, 4], [3, 1, 0, 3], [3, 1, 0, 2], [3, 1, 0, 1], [3, 1, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_128_50_20 : ColCertDiv where
  rK := ⟨128, by decide⟩
  rH := ⟨50, by decide⟩
  m := 5
  T1 := T128_50
  T2 := Q2.T128_50_2
  h1 := (4,3,0,0,4)
  h2 := (4,3,0,0,3)
  D1 := [[4, 3, 1, 4], [4, 3, 1, 1], [4, 3, 1, 3], [4, 3, 1, 0], [4, 3, 1, 2]]
  D2 := [[4, 3, 1, 3], [4, 3, 1, 0], [4, 3, 1, 2], [4, 3, 1, 4], [4, 3, 1, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_128_82_5 : ColCertDiv where
  rK := ⟨128, by decide⟩
  rH := ⟨82, by decide⟩
  m := 5
  T1 := T128_82
  T2 := Q2.T128_82_2
  h1 := (1,0,2,0,0)
  h2 := (1,0,2,0,0)
  D1 := [[1, 0, 2, 2], [1, 0, 2, 2], [1, 0, 2, 2], [1, 0, 2, 2], [1, 0, 2, 2]]
  D2 := [[1, 0, 2, 3], [1, 0, 2, 3], [1, 0, 2, 3], [1, 0, 2, 3], [1, 0, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_128_82_10 : ColCertDiv where
  rK := ⟨128, by decide⟩
  rH := ⟨82, by decide⟩
  m := 5
  T1 := T128_82
  T2 := Q2.T128_82_2
  h1 := (2,0,4,0,0)
  h2 := (2,0,4,0,0)
  D1 := [[2, 0, 4, 2], [2, 0, 4, 2], [2, 0, 4, 2], [2, 0, 4, 2], [2, 0, 4, 2]]
  D2 := [[2, 0, 4, 4], [2, 0, 4, 4], [2, 0, 4, 4], [2, 0, 4, 4], [2, 0, 4, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_128_82_15 : ColCertDiv where
  rK := ⟨128, by decide⟩
  rH := ⟨82, by decide⟩
  m := 5
  T1 := T128_82
  T2 := Q2.T128_82_2
  h1 := (3,0,1,0,0)
  h2 := (3,0,1,0,0)
  D1 := [[3, 0, 1, 0], [3, 0, 1, 0], [3, 0, 1, 0], [3, 0, 1, 0], [3, 0, 1, 0]]
  D2 := [[3, 0, 1, 3], [3, 0, 1, 3], [3, 0, 1, 3], [3, 0, 1, 3], [3, 0, 1, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_128_82_20 : ColCertDiv where
  rK := ⟨128, by decide⟩
  rH := ⟨82, by decide⟩
  m := 5
  T1 := T128_82
  T2 := Q2.T128_82_2
  h1 := (4,0,3,0,0)
  h2 := (4,0,3,0,0)
  D1 := [[4, 0, 3, 1], [4, 0, 3, 1], [4, 0, 3, 1], [4, 0, 3, 1], [4, 0, 3, 1]]
  D2 := [[4, 0, 3, 0], [4, 0, 3, 0], [4, 0, 3, 0], [4, 0, 3, 0], [4, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_128_90_25 : ColCertDiv where
  rK := ⟨128, by decide⟩
  rH := ⟨90, by decide⟩
  m := 5
  T1 := T128_90
  T2 := Q2.T128_90_2
  h1 := (0,1,4,0,0)
  h2 := (0,1,4,0,0)
  D1 := [[0, 1, 0, 2], [0, 1, 0, 1], [0, 1, 0, 0], [0, 1, 0, 4], [0, 1, 0, 3]]
  D2 := [[0, 1, 0, 4], [0, 1, 0, 3], [0, 1, 0, 2], [0, 1, 0, 1], [0, 1, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_128_90_50 : ColCertDiv where
  rK := ⟨128, by decide⟩
  rH := ⟨90, by decide⟩
  m := 5
  T1 := T128_90
  T2 := Q2.T128_90_2
  h1 := (0,2,3,0,4)
  h2 := (0,2,3,0,4)
  D1 := [[0, 2, 0, 4], [0, 2, 0, 2], [0, 2, 0, 0], [0, 2, 0, 3], [0, 2, 0, 1]]
  D2 := [[0, 2, 0, 3], [0, 2, 0, 1], [0, 2, 0, 4], [0, 2, 0, 2], [0, 2, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_128_90_75 : ColCertDiv where
  rK := ⟨128, by decide⟩
  rH := ⟨90, by decide⟩
  m := 5
  T1 := T128_90
  T2 := Q2.T128_90_2
  h1 := (0,3,2,0,2)
  h2 := (0,3,2,0,2)
  D1 := [[0, 3, 0, 1], [0, 3, 0, 3], [0, 3, 0, 0], [0, 3, 0, 2], [0, 3, 0, 4]]
  D2 := [[0, 3, 0, 2], [0, 3, 0, 4], [0, 3, 0, 1], [0, 3, 0, 3], [0, 3, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_128_90_100 : ColCertDiv where
  rK := ⟨128, by decide⟩
  rH := ⟨90, by decide⟩
  m := 5
  T1 := T128_90
  T2 := Q2.T128_90_2
  h1 := (0,4,1,0,4)
  h2 := (0,4,1,0,4)
  D1 := [[0, 4, 0, 3], [0, 4, 0, 4], [0, 4, 0, 0], [0, 4, 0, 1], [0, 4, 0, 2]]
  D2 := [[0, 4, 0, 1], [0, 4, 0, 2], [0, 4, 0, 3], [0, 4, 0, 4], [0, 4, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_128_96_5 : ColCertDiv where
  rK := ⟨128, by decide⟩
  rH := ⟨96, by decide⟩
  m := 5
  T1 := T128_96
  T2 := Q2.T128_96_2
  h1 := (1,4,3,4,2)
  h2 := (1,4,3,4,2)
  D1 := [[1, 4, 2, 3], [1, 4, 2, 4], [1, 4, 2, 0], [1, 4, 2, 1], [1, 4, 2, 2]]
  D2 := [[1, 4, 2, 2], [1, 4, 2, 3], [1, 4, 2, 4], [1, 4, 2, 0], [1, 4, 2, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_128_96_10 : ColCertDiv where
  rK := ⟨128, by decide⟩
  rH := ⟨96, by decide⟩
  m := 5
  T1 := T128_96
  T2 := Q2.T128_96_2
  h1 := (2,3,1,2,1)
  h2 := (2,3,1,2,2)
  D1 := [[2, 3, 0, 2], [2, 3, 0, 4], [2, 3, 0, 1], [2, 3, 0, 3], [2, 3, 0, 0]]
  D2 := [[2, 3, 0, 1], [2, 3, 0, 3], [2, 3, 0, 0], [2, 3, 0, 2], [2, 3, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_128_96_15 : ColCertDiv where
  rK := ⟨128, by decide⟩
  rH := ⟨96, by decide⟩
  m := 5
  T1 := T128_96
  T2 := Q2.T128_96_2
  h1 := (3,2,4,4,0)
  h2 := (3,2,4,4,2)
  D1 := [[3, 2, 4, 0], [3, 2, 4, 3], [3, 2, 4, 1], [3, 2, 4, 4], [3, 2, 4, 2]]
  D2 := [[3, 2, 4, 4], [3, 2, 4, 2], [3, 2, 4, 0], [3, 2, 4, 3], [3, 2, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_128_96_20 : ColCertDiv where
  rK := ⟨128, by decide⟩
  rH := ⟨96, by decide⟩
  m := 5
  T1 := T128_96
  T2 := Q2.T128_96_2
  h1 := (4,1,2,0,3)
  h2 := (4,1,2,0,1)
  D1 := [[4, 1, 4, 1], [4, 1, 4, 0], [4, 1, 4, 4], [4, 1, 4, 3], [4, 1, 4, 2]]
  D2 := [[4, 1, 4, 0], [4, 1, 4, 4], [4, 1, 4, 3], [4, 1, 4, 2], [4, 1, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_128_103_5 : ColCertDiv where
  rK := ⟨128, by decide⟩
  rH := ⟨103, by decide⟩
  m := 5
  T1 := T128_103
  T2 := Q2.T128_103_2
  h1 := (1,3,4,1,1)
  h2 := (1,3,4,1,1)
  D1 := [[1, 3, 0, 4], [1, 3, 0, 1], [1, 3, 0, 3], [1, 3, 0, 0], [1, 3, 0, 2]]
  D2 := [[1, 3, 0, 1], [1, 3, 0, 3], [1, 3, 0, 0], [1, 3, 0, 2], [1, 3, 0, 4]]
  bind1 := by decide
  bind2 := by decide

end LeanDring.P5Presentation
