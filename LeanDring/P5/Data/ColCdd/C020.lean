/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.Twin1.ColCert
import LeanDring.P5.Data.EntryK.C039
import LeanDring.P5.Data.EntryK.C041

/-!
# Species-table cell data, stage 2 — column-data-divergent columns

Per-column certified exponent-vector data (`ColCert`/`ColCertDiv`) with kernel
`decide` bindings. Emitted; the embedded lists are what the kernel certifies.
cdd tier, chunk 19: 60 columns.
-/

-- machine-emitted data: silence style linters (generated long lines, file-level options)
set_option linter.style.longLine false

namespace LeanDring.P5Presentation

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

def colCertDiv_140_35_5 : ColCertDiv where
  rK := ⟨140, by decide⟩
  rH := ⟨35, by decide⟩
  m := 5
  T1 := T140_35
  T2 := Q2.T140_35_2
  h1 := (1,2,4,2,0)
  h2 := (1,2,4,2,2)
  D1 := [[1, 2, 0, 0], [1, 2, 0, 3], [1, 2, 0, 1], [1, 2, 0, 4], [1, 2, 0, 2]]
  D2 := [[1, 2, 0, 4], [1, 2, 0, 2], [1, 2, 0, 0], [1, 2, 0, 3], [1, 2, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_140_35_10 : ColCertDiv where
  rK := ⟨140, by decide⟩
  rH := ⟨35, by decide⟩
  m := 5
  T1 := T140_35
  T2 := Q2.T140_35_2
  h1 := (2,4,3,1,0)
  h2 := (2,4,3,1,4)
  D1 := [[2, 4, 3, 4], [2, 4, 3, 0], [2, 4, 3, 1], [2, 4, 3, 2], [2, 4, 3, 3]]
  D2 := [[2, 4, 3, 2], [2, 4, 3, 3], [2, 4, 3, 4], [2, 4, 3, 0], [2, 4, 3, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_140_35_15 : ColCertDiv where
  rK := ⟨140, by decide⟩
  rH := ⟨35, by decide⟩
  m := 5
  T1 := T140_35
  T2 := Q2.T140_35_2
  h1 := (3,1,2,2,3)
  h2 := (3,1,2,2,0)
  D1 := [[3, 1, 4, 0], [3, 1, 4, 4], [3, 1, 4, 3], [3, 1, 4, 2], [3, 1, 4, 1]]
  D2 := [[3, 1, 4, 3], [3, 1, 4, 2], [3, 1, 4, 1], [3, 1, 4, 0], [3, 1, 4, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_140_35_20 : ColCertDiv where
  rK := ⟨140, by decide⟩
  rH := ⟨35, by decide⟩
  m := 5
  T1 := T140_35
  T2 := Q2.T140_35_2
  h1 := (4,3,1,0,4)
  h2 := (4,3,1,0,3)
  D1 := [[4, 3, 3, 3], [4, 3, 3, 0], [4, 3, 3, 2], [4, 3, 3, 4], [4, 3, 3, 1]]
  D2 := [[4, 3, 3, 0], [4, 3, 3, 2], [4, 3, 3, 4], [4, 3, 3, 1], [4, 3, 3, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_140_39_5 : ColCertDiv where
  rK := ⟨140, by decide⟩
  rH := ⟨39, by decide⟩
  m := 5
  T1 := T140_39
  T2 := Q2.T140_39_2
  h1 := (1,4,2,3,2)
  h2 := (1,4,2,3,2)
  D1 := [[1, 4, 4, 4], [1, 4, 4, 0], [1, 4, 4, 1], [1, 4, 4, 2], [1, 4, 4, 3]]
  D2 := [[1, 4, 4, 0], [1, 4, 4, 1], [1, 4, 4, 2], [1, 4, 4, 3], [1, 4, 4, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_140_39_10 : ColCertDiv where
  rK := ⟨140, by decide⟩
  rH := ⟨39, by decide⟩
  m := 5
  T1 := T140_39
  T2 := Q2.T140_39_2
  h1 := (2,3,4,0,1)
  h2 := (2,3,4,0,2)
  D1 := [[2, 3, 4, 3], [2, 3, 4, 0], [2, 3, 4, 2], [2, 3, 4, 4], [2, 3, 4, 1]]
  D2 := [[2, 3, 4, 1], [2, 3, 4, 3], [2, 3, 4, 0], [2, 3, 4, 2], [2, 3, 4, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_140_39_20 : ColCertDiv where
  rK := ⟨140, by decide⟩
  rH := ⟨39, by decide⟩
  m := 5
  T1 := T140_39
  T2 := Q2.T140_39_2
  h1 := (4,1,3,1,3)
  h2 := (4,1,3,1,1)
  D1 := [[4, 1, 2, 4], [4, 1, 2, 3], [4, 1, 2, 2], [4, 1, 2, 1], [4, 1, 2, 0]]
  D2 := [[4, 1, 2, 1], [4, 1, 2, 0], [4, 1, 2, 4], [4, 1, 2, 3], [4, 1, 2, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_140_46_10 : ColCertDiv where
  rK := ⟨140, by decide⟩
  rH := ⟨46, by decide⟩
  m := 5
  T1 := T140_46
  T2 := Q2.T140_46_2
  h1 := (2,1,1,3,4)
  h2 := (2,1,1,3,2)
  D1 := [[2, 1, 1, 0], [2, 1, 1, 4], [2, 1, 1, 3], [2, 1, 1, 2], [2, 1, 1, 1]]
  D2 := [[2, 1, 1, 1], [2, 1, 1, 0], [2, 1, 1, 4], [2, 1, 1, 3], [2, 1, 1, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_140_46_15 : ColCertDiv where
  rK := ⟨140, by decide⟩
  rH := ⟨46, by decide⟩
  m := 5
  T1 := T140_46
  T2 := Q2.T140_46_2
  h1 := (3,4,4,4,2)
  h2 := (3,4,4,4,1)
  D1 := [[3, 4, 2, 1], [3, 4, 2, 2], [3, 4, 2, 3], [3, 4, 2, 4], [3, 4, 2, 0]]
  D2 := [[3, 4, 2, 2], [3, 4, 2, 3], [3, 4, 2, 4], [3, 4, 2, 0], [3, 4, 2, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_140_46_20 : ColCertDiv where
  rK := ⟨140, by decide⟩
  rH := ⟨46, by decide⟩
  m := 5
  T1 := T140_46
  T2 := Q2.T140_46_2
  h1 := (4,2,2,3,1)
  h2 := (4,2,2,3,2)
  D1 := [[4, 2, 0, 3], [4, 2, 0, 1], [4, 2, 0, 4], [4, 2, 0, 2], [4, 2, 0, 0]]
  D2 := [[4, 2, 0, 0], [4, 2, 0, 3], [4, 2, 0, 1], [4, 2, 0, 4], [4, 2, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_140_52_5 : ColCertDiv where
  rK := ⟨140, by decide⟩
  rH := ⟨52, by decide⟩
  m := 5
  T1 := T140_52
  T2 := Q2.T140_52_2
  h1 := (1,1,0,4,1)
  h2 := (1,1,0,4,4)
  D1 := [[1, 1, 3, 4], [1, 1, 3, 3], [1, 1, 3, 2], [1, 1, 3, 1], [1, 1, 3, 0]]
  D2 := [[1, 1, 3, 2], [1, 1, 3, 1], [1, 1, 3, 0], [1, 1, 3, 4], [1, 1, 3, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_140_52_10 : ColCertDiv where
  rK := ⟨140, by decide⟩
  rH := ⟨52, by decide⟩
  m := 5
  T1 := T140_52
  T2 := Q2.T140_52_2
  h1 := (2,2,0,4,1)
  h2 := (2,2,0,4,2)
  D1 := [[2, 2, 0, 2], [2, 2, 0, 0], [2, 2, 0, 3], [2, 2, 0, 1], [2, 2, 0, 4]]
  D2 := [[2, 2, 0, 3], [2, 2, 0, 1], [2, 2, 0, 4], [2, 2, 0, 2], [2, 2, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_140_52_15 : ColCertDiv where
  rK := ⟨140, by decide⟩
  rH := ⟨52, by decide⟩
  m := 5
  T1 := T140_52
  T2 := Q2.T140_52_2
  h1 := (3,3,0,0,1)
  h2 := (3,3,0,0,0)
  D1 := [[3, 3, 1, 0], [3, 3, 1, 2], [3, 3, 1, 4], [3, 3, 1, 1], [3, 3, 1, 3]]
  D2 := [[3, 3, 1, 4], [3, 3, 1, 1], [3, 3, 1, 3], [3, 3, 1, 0], [3, 3, 1, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_140_52_20 : ColCertDiv where
  rK := ⟨140, by decide⟩
  rH := ⟨52, by decide⟩
  m := 5
  T1 := T140_52
  T2 := Q2.T140_52_2
  h1 := (4,4,0,2,2)
  h2 := (4,4,0,2,4)
  D1 := [[4, 4, 1, 4], [4, 4, 1, 0], [4, 4, 1, 1], [4, 4, 1, 2], [4, 4, 1, 3]]
  D2 := [[4, 4, 1, 1], [4, 4, 1, 2], [4, 4, 1, 3], [4, 4, 1, 4], [4, 4, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_140_84_5 : ColCertDiv where
  rK := ⟨140, by decide⟩
  rH := ⟨84, by decide⟩
  m := 5
  T1 := T140_84
  T2 := Q2.T140_84_2
  h1 := (1,0,1,0,0)
  h2 := (1,0,1,0,0)
  D1 := [[1, 0, 0, 3], [1, 0, 0, 3], [1, 0, 0, 3], [1, 0, 0, 3], [1, 0, 0, 3]]
  D2 := [[1, 0, 0, 1], [1, 0, 0, 1], [1, 0, 0, 1], [1, 0, 0, 1], [1, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_140_84_10 : ColCertDiv where
  rK := ⟨140, by decide⟩
  rH := ⟨84, by decide⟩
  m := 5
  T1 := T140_84
  T2 := Q2.T140_84_2
  h1 := (2,0,2,0,0)
  h2 := (2,0,2,0,0)
  D1 := [[2, 0, 0, 1], [2, 0, 0, 1], [2, 0, 0, 1], [2, 0, 0, 1], [2, 0, 0, 1]]
  D2 := [[2, 0, 0, 2], [2, 0, 0, 2], [2, 0, 0, 2], [2, 0, 0, 2], [2, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_140_84_15 : ColCertDiv where
  rK := ⟨140, by decide⟩
  rH := ⟨84, by decide⟩
  m := 5
  T1 := T140_84
  T2 := Q2.T140_84_2
  h1 := (3,0,3,0,0)
  h2 := (3,0,3,0,0)
  D1 := [[3, 0, 0, 4], [3, 0, 0, 4], [3, 0, 0, 4], [3, 0, 0, 4], [3, 0, 0, 4]]
  D2 := [[3, 0, 0, 3], [3, 0, 0, 3], [3, 0, 0, 3], [3, 0, 0, 3], [3, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_140_84_20 : ColCertDiv where
  rK := ⟨140, by decide⟩
  rH := ⟨84, by decide⟩
  m := 5
  T1 := T140_84
  T2 := Q2.T140_84_2
  h1 := (4,0,4,0,0)
  h2 := (4,0,4,0,0)
  D1 := [[4, 0, 0, 2], [4, 0, 0, 2], [4, 0, 0, 2], [4, 0, 0, 2], [4, 0, 0, 2]]
  D2 := [[4, 0, 0, 4], [4, 0, 0, 4], [4, 0, 0, 4], [4, 0, 0, 4], [4, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_140_90_25 : ColCertDiv where
  rK := ⟨140, by decide⟩
  rH := ⟨90, by decide⟩
  m := 5
  T1 := T140_90
  T2 := Q2.T140_90_2
  h1 := (0,1,4,0,0)
  h2 := (0,1,4,0,0)
  D1 := [[0, 1, 0, 3], [0, 1, 0, 2], [0, 1, 0, 1], [0, 1, 0, 0], [0, 1, 0, 4]]
  D2 := [[0, 1, 0, 0], [0, 1, 0, 4], [0, 1, 0, 3], [0, 1, 0, 2], [0, 1, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_140_90_50 : ColCertDiv where
  rK := ⟨140, by decide⟩
  rH := ⟨90, by decide⟩
  m := 5
  T1 := T140_90
  T2 := Q2.T140_90_2
  h1 := (0,2,3,0,4)
  h2 := (0,2,3,0,4)
  D1 := [[0, 2, 0, 1], [0, 2, 0, 4], [0, 2, 0, 2], [0, 2, 0, 0], [0, 2, 0, 3]]
  D2 := [[0, 2, 0, 0], [0, 2, 0, 3], [0, 2, 0, 1], [0, 2, 0, 4], [0, 2, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_140_90_75 : ColCertDiv where
  rK := ⟨140, by decide⟩
  rH := ⟨90, by decide⟩
  m := 5
  T1 := T140_90
  T2 := Q2.T140_90_2
  h1 := (0,3,2,0,2)
  h2 := (0,3,2,0,2)
  D1 := [[0, 3, 0, 4], [0, 3, 0, 1], [0, 3, 0, 3], [0, 3, 0, 0], [0, 3, 0, 2]]
  D2 := [[0, 3, 0, 0], [0, 3, 0, 2], [0, 3, 0, 4], [0, 3, 0, 1], [0, 3, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_140_90_100 : ColCertDiv where
  rK := ⟨140, by decide⟩
  rH := ⟨90, by decide⟩
  m := 5
  T1 := T140_90
  T2 := Q2.T140_90_2
  h1 := (0,4,1,0,4)
  h2 := (0,4,1,0,4)
  D1 := [[0, 4, 0, 2], [0, 4, 0, 3], [0, 4, 0, 4], [0, 4, 0, 0], [0, 4, 0, 1]]
  D2 := [[0, 4, 0, 0], [0, 4, 0, 1], [0, 4, 0, 2], [0, 4, 0, 3], [0, 4, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_140_97_5 : ColCertDiv where
  rK := ⟨140, by decide⟩
  rH := ⟨97, by decide⟩
  m := 5
  T1 := T140_97
  T2 := Q2.T140_97_2
  h1 := (1,2,4,3,0)
  h2 := (1,2,4,3,0)
  D1 := [[1, 2, 1, 4], [1, 2, 1, 2], [1, 2, 1, 0], [1, 2, 1, 3], [1, 2, 1, 1]]
  D2 := [[1, 2, 1, 1], [1, 2, 1, 4], [1, 2, 1, 2], [1, 2, 1, 0], [1, 2, 1, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_140_97_10 : ColCertDiv where
  rK := ⟨140, by decide⟩
  rH := ⟨97, by decide⟩
  m := 5
  T1 := T140_97
  T2 := Q2.T140_97_2
  h1 := (2,4,3,3,1)
  h2 := (2,4,3,3,1)
  D1 := [[2, 4, 0, 1], [2, 4, 0, 2], [2, 4, 0, 3], [2, 4, 0, 4], [2, 4, 0, 0]]
  D2 := [[2, 4, 0, 0], [2, 4, 0, 1], [2, 4, 0, 2], [2, 4, 0, 3], [2, 4, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_140_97_15 : ColCertDiv where
  rK := ⟨140, by decide⟩
  rH := ⟨97, by decide⟩
  m := 5
  T1 := T140_97
  T2 := Q2.T140_97_2
  h1 := (3,1,2,0,1)
  h2 := (3,1,2,0,2)
  D1 := [[3, 1, 2, 4], [3, 1, 2, 3], [3, 1, 2, 2], [3, 1, 2, 1], [3, 1, 2, 0]]
  D2 := [[3, 1, 2, 1], [3, 1, 2, 0], [3, 1, 2, 4], [3, 1, 2, 3], [3, 1, 2, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_140_97_20 : ColCertDiv where
  rK := ⟨140, by decide⟩
  rH := ⟨97, by decide⟩
  m := 5
  T1 := T140_97
  T2 := Q2.T140_97_2
  h1 := (4,3,1,4,0)
  h2 := (4,3,1,4,1)
  D1 := [[4, 3, 2, 3], [4, 3, 2, 0], [4, 3, 2, 2], [4, 3, 2, 4], [4, 3, 2, 1]]
  D2 := [[4, 3, 2, 2], [4, 3, 2, 4], [4, 3, 2, 1], [4, 3, 2, 3], [4, 3, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_140_101_5 : ColCertDiv where
  rK := ⟨140, by decide⟩
  rH := ⟨101, by decide⟩
  m := 5
  T1 := T140_101
  T2 := Q2.T140_101_2
  h1 := (1,4,2,4,3)
  h2 := (1,4,2,4,3)
  D1 := [[1, 4, 0, 4], [1, 4, 0, 0], [1, 4, 0, 1], [1, 4, 0, 2], [1, 4, 0, 3]]
  D2 := [[1, 4, 0, 0], [1, 4, 0, 1], [1, 4, 0, 2], [1, 4, 0, 3], [1, 4, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_140_101_10 : ColCertDiv where
  rK := ⟨140, by decide⟩
  rH := ⟨101, by decide⟩
  m := 5
  T1 := T140_101
  T2 := Q2.T140_101_2
  h1 := (2,3,4,2,4)
  h2 := (2,3,4,2,0)
  D1 := [[2, 3, 1, 2], [2, 3, 1, 4], [2, 3, 1, 1], [2, 3, 1, 3], [2, 3, 1, 0]]
  D2 := [[2, 3, 1, 0], [2, 3, 1, 2], [2, 3, 1, 4], [2, 3, 1, 1], [2, 3, 1, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_140_101_20 : ColCertDiv where
  rK := ⟨140, by decide⟩
  rH := ⟨101, by decide⟩
  m := 5
  T1 := T140_101
  T2 := Q2.T140_101_2
  h1 := (4,1,3,0,3)
  h2 := (4,1,3,0,1)
  D1 := [[4, 1, 1, 3], [4, 1, 1, 2], [4, 1, 1, 1], [4, 1, 1, 0], [4, 1, 1, 4]]
  D2 := [[4, 1, 1, 0], [4, 1, 1, 4], [4, 1, 1, 3], [4, 1, 1, 2], [4, 1, 1, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_140_108_5 : ColCertDiv where
  rK := ⟨140, by decide⟩
  rH := ⟨108, by decide⟩
  m := 5
  T1 := T140_108
  T2 := Q2.T140_108_2
  h1 := (1,3,3,1,0)
  h2 := (1,3,3,1,0)
  D1 := [[1, 3, 3, 2], [1, 3, 3, 4], [1, 3, 3, 1], [1, 3, 3, 3], [1, 3, 3, 0]]
  D2 := [[1, 3, 3, 1], [1, 3, 3, 3], [1, 3, 3, 0], [1, 3, 3, 2], [1, 3, 3, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_140_108_10 : ColCertDiv where
  rK := ⟨140, by decide⟩
  rH := ⟨108, by decide⟩
  m := 5
  T1 := T140_108
  T2 := Q2.T140_108_2
  h1 := (2,1,1,0,1)
  h2 := (2,1,1,0,2)
  D1 := [[2, 1, 3, 3], [2, 1, 3, 2], [2, 1, 3, 1], [2, 1, 3, 0], [2, 1, 3, 4]]
  D2 := [[2, 1, 3, 2], [2, 1, 3, 1], [2, 1, 3, 0], [2, 1, 3, 4], [2, 1, 3, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_140_108_15 : ColCertDiv where
  rK := ⟨140, by decide⟩
  rH := ⟨108, by decide⟩
  m := 5
  T1 := T140_108
  T2 := Q2.T140_108_2
  h1 := (3,4,4,2,4)
  h2 := (3,4,4,2,0)
  D1 := [[3, 4, 0, 4], [3, 4, 0, 0], [3, 4, 0, 1], [3, 4, 0, 2], [3, 4, 0, 3]]
  D2 := [[3, 4, 0, 2], [3, 4, 0, 3], [3, 4, 0, 4], [3, 4, 0, 0], [3, 4, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_140_108_20 : ColCertDiv where
  rK := ⟨140, by decide⟩
  rH := ⟨108, by decide⟩
  m := 5
  T1 := T140_108
  T2 := Q2.T140_108_2
  h1 := (4,2,2,2,4)
  h2 := (4,2,2,2,1)
  D1 := [[4, 2, 4, 0], [4, 2, 4, 3], [4, 2, 4, 1], [4, 2, 4, 4], [4, 2, 4, 2]]
  D2 := [[4, 2, 4, 3], [4, 2, 4, 1], [4, 2, 4, 4], [4, 2, 4, 2], [4, 2, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_142_29_5 : ColCertDiv where
  rK := ⟨142, by decide⟩
  rH := ⟨29, by decide⟩
  m := 5
  T1 := T142_29
  T2 := Q2.T142_29_2
  h1 := (1,4,1,3,3)
  h2 := (1,4,1,3,3)
  D1 := [[1, 4, 4, 1], [1, 4, 4, 2], [1, 4, 4, 3], [1, 4, 4, 4], [1, 4, 4, 0]]
  D2 := [[1, 4, 4, 4], [1, 4, 4, 0], [1, 4, 4, 1], [1, 4, 4, 2], [1, 4, 4, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_142_29_10 : ColCertDiv where
  rK := ⟨142, by decide⟩
  rH := ⟨29, by decide⟩
  m := 5
  T1 := T142_29
  T2 := Q2.T142_29_2
  h1 := (2,3,2,0,4)
  h2 := (2,3,2,0,0)
  D1 := [[2, 3, 4, 3], [2, 3, 4, 0], [2, 3, 4, 2], [2, 3, 4, 4], [2, 3, 4, 1]]
  D2 := [[2, 3, 4, 0], [2, 3, 4, 2], [2, 3, 4, 4], [2, 3, 4, 1], [2, 3, 4, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_142_29_15 : ColCertDiv where
  rK := ⟨142, by decide⟩
  rH := ⟨29, by decide⟩
  m := 5
  T1 := T142_29
  T2 := Q2.T142_29_2
  h1 := (3,2,3,1,1)
  h2 := (3,2,3,1,3)
  D1 := [[3, 2, 0, 4], [3, 2, 0, 2], [3, 2, 0, 0], [3, 2, 0, 3], [3, 2, 0, 1]]
  D2 := [[3, 2, 0, 0], [3, 2, 0, 3], [3, 2, 0, 1], [3, 2, 0, 4], [3, 2, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_142_30_5 : ColCertDiv where
  rK := ⟨142, by decide⟩
  rH := ⟨30, by decide⟩
  m := 5
  T1 := T142_30
  T2 := Q2.T142_30_2
  h1 := (1,2,3,2,3)
  h2 := (1,2,3,2,0)
  D1 := [[1, 2, 0, 2], [1, 2, 0, 0], [1, 2, 0, 3], [1, 2, 0, 1], [1, 2, 0, 4]]
  D2 := [[1, 2, 0, 3], [1, 2, 0, 1], [1, 2, 0, 4], [1, 2, 0, 2], [1, 2, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_142_30_10 : ColCertDiv where
  rK := ⟨142, by decide⟩
  rH := ⟨30, by decide⟩
  m := 5
  T1 := T142_30
  T2 := Q2.T142_30_2
  h1 := (2,4,1,1,4)
  h2 := (2,4,1,1,3)
  D1 := [[2, 4, 3, 1], [2, 4, 3, 2], [2, 4, 3, 3], [2, 4, 3, 4], [2, 4, 3, 0]]
  D2 := [[2, 4, 3, 3], [2, 4, 3, 4], [2, 4, 3, 0], [2, 4, 3, 1], [2, 4, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_142_30_15 : ColCertDiv where
  rK := ⟨142, by decide⟩
  rH := ⟨30, by decide⟩
  m := 5
  T1 := T142_30
  T2 := Q2.T142_30_2
  h1 := (3,1,4,2,1)
  h2 := (3,1,4,2,3)
  D1 := [[3, 1, 4, 0], [3, 1, 4, 4], [3, 1, 4, 3], [3, 1, 4, 2], [3, 1, 4, 1]]
  D2 := [[3, 1, 4, 4], [3, 1, 4, 3], [3, 1, 4, 2], [3, 1, 4, 1], [3, 1, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_142_31_5 : ColCertDiv where
  rK := ⟨142, by decide⟩
  rH := ⟨31, by decide⟩
  m := 5
  T1 := T142_31
  T2 := Q2.T142_31_2
  h1 := (1,3,2,0,4)
  h2 := (1,3,2,0,0)
  D1 := [[1, 3, 2, 2], [1, 3, 2, 4], [1, 3, 2, 1], [1, 3, 2, 3], [1, 3, 2, 0]]
  D2 := [[1, 3, 2, 4], [1, 3, 2, 1], [1, 3, 2, 3], [1, 3, 2, 0], [1, 3, 2, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_142_31_15 : ColCertDiv where
  rK := ⟨142, by decide⟩
  rH := ⟨31, by decide⟩
  m := 5
  T1 := T142_31
  T2 := Q2.T142_31_2
  h1 := (3,4,1,4,4)
  h2 := (3,4,1,4,3)
  D1 := [[3, 4, 2, 3], [3, 4, 2, 4], [3, 4, 2, 0], [3, 4, 2, 1], [3, 4, 2, 2]]
  D2 := [[3, 4, 2, 0], [3, 4, 2, 1], [3, 4, 2, 2], [3, 4, 2, 3], [3, 4, 2, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_142_90_25 : ColCertDiv where
  rK := ⟨142, by decide⟩
  rH := ⟨90, by decide⟩
  m := 5
  T1 := T142_90
  T2 := Q2.T142_90_2
  h1 := (0,1,4,0,0)
  h2 := (0,1,4,0,0)
  D1 := [[0, 1, 0, 4], [0, 1, 0, 3], [0, 1, 0, 2], [0, 1, 0, 1], [0, 1, 0, 0]]
  D2 := [[0, 1, 0, 1], [0, 1, 0, 0], [0, 1, 0, 4], [0, 1, 0, 3], [0, 1, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_142_90_50 : ColCertDiv where
  rK := ⟨142, by decide⟩
  rH := ⟨90, by decide⟩
  m := 5
  T1 := T142_90
  T2 := Q2.T142_90_2
  h1 := (0,2,3,0,4)
  h2 := (0,2,3,0,4)
  D1 := [[0, 2, 0, 3], [0, 2, 0, 1], [0, 2, 0, 4], [0, 2, 0, 2], [0, 2, 0, 0]]
  D2 := [[0, 2, 0, 2], [0, 2, 0, 0], [0, 2, 0, 3], [0, 2, 0, 1], [0, 2, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_142_90_75 : ColCertDiv where
  rK := ⟨142, by decide⟩
  rH := ⟨90, by decide⟩
  m := 5
  T1 := T142_90
  T2 := Q2.T142_90_2
  h1 := (0,3,2,0,2)
  h2 := (0,3,2,0,2)
  D1 := [[0, 3, 0, 2], [0, 3, 0, 4], [0, 3, 0, 1], [0, 3, 0, 3], [0, 3, 0, 0]]
  D2 := [[0, 3, 0, 3], [0, 3, 0, 0], [0, 3, 0, 2], [0, 3, 0, 4], [0, 3, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_142_90_100 : ColCertDiv where
  rK := ⟨142, by decide⟩
  rH := ⟨90, by decide⟩
  m := 5
  T1 := T142_90
  T2 := Q2.T142_90_2
  h1 := (0,4,1,0,4)
  h2 := (0,4,1,0,4)
  D1 := [[0, 4, 0, 1], [0, 4, 0, 2], [0, 4, 0, 3], [0, 4, 0, 4], [0, 4, 0, 0]]
  D2 := [[0, 4, 0, 4], [0, 4, 0, 0], [0, 4, 0, 1], [0, 4, 0, 2], [0, 4, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_142_91_5 : ColCertDiv where
  rK := ⟨142, by decide⟩
  rH := ⟨91, by decide⟩
  m := 5
  T1 := T142_91
  T2 := Q2.T142_91_2
  h1 := (1,4,1,4,4)
  h2 := (1,4,1,4,4)
  D1 := [[1, 4, 0, 1], [1, 4, 0, 2], [1, 4, 0, 3], [1, 4, 0, 4], [1, 4, 0, 0]]
  D2 := [[1, 4, 0, 4], [1, 4, 0, 0], [1, 4, 0, 1], [1, 4, 0, 2], [1, 4, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_142_91_10 : ColCertDiv where
  rK := ⟨142, by decide⟩
  rH := ⟨91, by decide⟩
  m := 5
  T1 := T142_91
  T2 := Q2.T142_91_2
  h1 := (2,3,2,2,2)
  h2 := (2,3,2,2,3)
  D1 := [[2, 3, 1, 2], [2, 3, 1, 4], [2, 3, 1, 1], [2, 3, 1, 3], [2, 3, 1, 0]]
  D2 := [[2, 3, 1, 4], [2, 3, 1, 1], [2, 3, 1, 3], [2, 3, 1, 0], [2, 3, 1, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_142_91_15 : ColCertDiv where
  rK := ⟨142, by decide⟩
  rH := ⟨91, by decide⟩
  m := 5
  T1 := T142_91
  T2 := Q2.T142_91_2
  h1 := (3,2,3,4,2)
  h2 := (3,2,3,4,4)
  D1 := [[3, 2, 3, 1], [3, 2, 3, 4], [3, 2, 3, 2], [3, 2, 3, 0], [3, 2, 3, 3]]
  D2 := [[3, 2, 3, 2], [3, 2, 3, 0], [3, 2, 3, 3], [3, 2, 3, 1], [3, 2, 3, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_142_92_5 : ColCertDiv where
  rK := ⟨142, by decide⟩
  rH := ⟨92, by decide⟩
  m := 5
  T1 := T142_92
  T2 := Q2.T142_92_2
  h1 := (1,2,3,3,2)
  h2 := (1,2,3,3,2)
  D1 := [[1, 2, 1, 0], [1, 2, 1, 3], [1, 2, 1, 1], [1, 2, 1, 4], [1, 2, 1, 2]]
  D2 := [[1, 2, 1, 4], [1, 2, 1, 2], [1, 2, 1, 0], [1, 2, 1, 3], [1, 2, 1, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_142_92_10 : ColCertDiv where
  rK := ⟨142, by decide⟩
  rH := ⟨92, by decide⟩
  m := 5
  T1 := T142_92
  T2 := Q2.T142_92_2
  h1 := (2,4,1,3,3)
  h2 := (2,4,1,3,3)
  D1 := [[2, 4, 0, 1], [2, 4, 0, 2], [2, 4, 0, 3], [2, 4, 0, 4], [2, 4, 0, 0]]
  D2 := [[2, 4, 0, 4], [2, 4, 0, 0], [2, 4, 0, 1], [2, 4, 0, 2], [2, 4, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_142_92_15 : ColCertDiv where
  rK := ⟨142, by decide⟩
  rH := ⟨92, by decide⟩
  m := 5
  T1 := T142_92
  T2 := Q2.T142_92_2
  h1 := (3,1,4,0,1)
  h2 := (3,1,4,0,2)
  D1 := [[3, 1, 2, 1], [3, 1, 2, 0], [3, 1, 2, 4], [3, 1, 2, 3], [3, 1, 2, 2]]
  D2 := [[3, 1, 2, 4], [3, 1, 2, 3], [3, 1, 2, 2], [3, 1, 2, 1], [3, 1, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_142_92_20 : ColCertDiv where
  rK := ⟨142, by decide⟩
  rH := ⟨92, by decide⟩
  m := 5
  T1 := T142_92
  T2 := Q2.T142_92_2
  h1 := (4,3,2,4,1)
  h2 := (4,3,2,4,2)
  D1 := [[4, 3, 2, 0], [4, 3, 2, 2], [4, 3, 2, 4], [4, 3, 2, 1], [4, 3, 2, 3]]
  D2 := [[4, 3, 2, 2], [4, 3, 2, 4], [4, 3, 2, 1], [4, 3, 2, 3], [4, 3, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_142_93_5 : ColCertDiv where
  rK := ⟨142, by decide⟩
  rH := ⟨93, by decide⟩
  m := 5
  T1 := T142_93
  T2 := Q2.T142_93_2
  h1 := (1,3,2,1,4)
  h2 := (1,3,2,1,4)
  D1 := [[1, 3, 3, 1], [1, 3, 3, 3], [1, 3, 3, 0], [1, 3, 3, 2], [1, 3, 3, 4]]
  D2 := [[1, 3, 3, 2], [1, 3, 3, 4], [1, 3, 3, 1], [1, 3, 3, 3], [1, 3, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_142_93_10 : ColCertDiv where
  rK := ⟨142, by decide⟩
  rH := ⟨93, by decide⟩
  m := 5
  T1 := T142_93
  T2 := Q2.T142_93_2
  h1 := (2,1,4,0,1)
  h2 := (2,1,4,0,2)
  D1 := [[2, 1, 3, 3], [2, 1, 3, 2], [2, 1, 3, 1], [2, 1, 3, 0], [2, 1, 3, 4]]
  D2 := [[2, 1, 3, 1], [2, 1, 3, 0], [2, 1, 3, 4], [2, 1, 3, 3], [2, 1, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_142_93_15 : ColCertDiv where
  rK := ⟨142, by decide⟩
  rH := ⟨93, by decide⟩
  m := 5
  T1 := T142_93
  T2 := Q2.T142_93_2
  h1 := (3,4,1,2,2)
  h2 := (3,4,1,2,3)
  D1 := [[3, 4, 0, 2], [3, 4, 0, 3], [3, 4, 0, 4], [3, 4, 0, 0], [3, 4, 0, 1]]
  D2 := [[3, 4, 0, 1], [3, 4, 0, 2], [3, 4, 0, 3], [3, 4, 0, 4], [3, 4, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_142_93_20 : ColCertDiv where
  rK := ⟨142, by decide⟩
  rH := ⟨93, by decide⟩
  m := 5
  T1 := T142_93
  T2 := Q2.T142_93_2
  h1 := (4,2,3,2,2)
  h2 := (4,2,3,2,4)
  D1 := [[4, 2, 4, 3], [4, 2, 4, 1], [4, 2, 4, 4], [4, 2, 4, 2], [4, 2, 4, 0]]
  D2 := [[4, 2, 4, 4], [4, 2, 4, 2], [4, 2, 4, 0], [4, 2, 4, 3], [4, 2, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_142_94_5 : ColCertDiv where
  rK := ⟨142, by decide⟩
  rH := ⟨94, by decide⟩
  m := 5
  T1 := T142_94
  T2 := Q2.T142_94_2
  h1 := (1,1,4,0,0)
  h2 := (1,1,4,0,0)
  D1 := [[1, 1, 4, 0], [1, 1, 4, 4], [1, 1, 4, 3], [1, 1, 4, 2], [1, 1, 4, 1]]
  D2 := [[1, 1, 4, 2], [1, 1, 4, 1], [1, 1, 4, 0], [1, 1, 4, 4], [1, 1, 4, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_142_94_10 : ColCertDiv where
  rK := ⟨142, by decide⟩
  rH := ⟨94, by decide⟩
  m := 5
  T1 := T142_94
  T2 := Q2.T142_94_2
  h1 := (2,2,3,1,4)
  h2 := (2,2,3,1,4)
  D1 := [[2, 2, 2, 2], [2, 2, 2, 0], [2, 2, 2, 3], [2, 2, 2, 1], [2, 2, 2, 4]]
  D2 := [[2, 2, 2, 1], [2, 2, 2, 4], [2, 2, 2, 2], [2, 2, 2, 0], [2, 2, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_142_94_15 : ColCertDiv where
  rK := ⟨142, by decide⟩
  rH := ⟨94, by decide⟩
  m := 5
  T1 := T142_94
  T2 := Q2.T142_94_2
  h1 := (3,3,2,3,3)
  h2 := (3,3,2,3,3)
  D1 := [[3, 3, 4, 2], [3, 3, 4, 4], [3, 3, 4, 1], [3, 3, 4, 3], [3, 3, 4, 0]]
  D2 := [[3, 3, 4, 3], [3, 3, 4, 0], [3, 3, 4, 2], [3, 3, 4, 4], [3, 3, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_142_94_20 : ColCertDiv where
  rK := ⟨142, by decide⟩
  rH := ⟨94, by decide⟩
  m := 5
  T1 := T142_94
  T2 := Q2.T142_94_2
  h1 := (4,4,1,1,3)
  h2 := (4,4,1,1,3)
  D1 := [[4, 4, 0, 1], [4, 4, 0, 2], [4, 4, 0, 3], [4, 4, 0, 4], [4, 4, 0, 0]]
  D2 := [[4, 4, 0, 4], [4, 4, 0, 0], [4, 4, 0, 1], [4, 4, 0, 2], [4, 4, 0, 3]]
  bind1 := by decide
  bind2 := by decide

end LeanDring.P5Presentation
