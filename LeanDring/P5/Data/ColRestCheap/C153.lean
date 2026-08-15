/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.Twin1.ColCert
import LeanDring.P5.Data.EntryK.C015
import LeanDring.P5.Data.EntryK.C016

/-!
# Species-table cell data, stage 2 — twin-coincident columns (cheap tier)

Per-column certified exponent-vector data (`ColCert`/`ColCertDiv`) with kernel
`decide` bindings. Emitted; the embedded lists are what the kernel certifies.
rest tier, chunk 152: 60 columns.
-/

-- machine-emitted data: silence style linters (generated long lines, file-level options)
set_option linter.style.longLine false

namespace LeanDring.P5Presentation

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

def colCert_64_64_65 : ColCert where
  rK := ⟨64, by decide⟩
  rH := ⟨64, by decide⟩
  m := 5
  T1 := T64_64
  T2 := Q2.T64_64_2
  h1 := (2,3,3,3,4)
  h2 := (2,3,3,3,0)
  D := [[2, 3, 0], [2, 3, 3], [2, 3, 1], [2, 3, 4], [2, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_64_64_70 : ColCert where
  rK := ⟨64, by decide⟩
  rH := ⟨64, by decide⟩
  m := 5
  T1 := T64_64
  T2 := Q2.T64_64_2
  h1 := (2,3,4,4,4)
  h2 := (2,3,4,4,0)
  D := [[2, 4, 0], [2, 4, 3], [2, 4, 1], [2, 4, 4], [2, 4, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_64_64_75 : ColCert where
  rK := ⟨64, by decide⟩
  rH := ⟨64, by decide⟩
  m := 5
  T1 := T64_64
  T2 := Q2.T64_64_2
  h1 := (3,2,0,1,0)
  h2 := (3,2,0,1,2)
  D := [[3, 0, 0], [3, 0, 2], [3, 0, 4], [3, 0, 1], [3, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_64_64_80 : ColCert where
  rK := ⟨64, by decide⟩
  rH := ⟨64, by decide⟩
  m := 5
  T1 := T64_64
  T2 := Q2.T64_64_2
  h1 := (3,2,1,2,0)
  h2 := (3,2,1,2,2)
  D := [[3, 1, 0], [3, 1, 2], [3, 1, 4], [3, 1, 1], [3, 1, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_64_64_85 : ColCert where
  rK := ⟨64, by decide⟩
  rH := ⟨64, by decide⟩
  m := 5
  T1 := T64_64
  T2 := Q2.T64_64_2
  h1 := (3,2,2,3,0)
  h2 := (3,2,2,3,2)
  D := [[3, 2, 0], [3, 2, 2], [3, 2, 4], [3, 2, 1], [3, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_64_64_90 : ColCert where
  rK := ⟨64, by decide⟩
  rH := ⟨64, by decide⟩
  m := 5
  T1 := T64_64
  T2 := Q2.T64_64_2
  h1 := (3,2,3,4,0)
  h2 := (3,2,3,4,2)
  D := [[3, 3, 0], [3, 3, 2], [3, 3, 4], [3, 3, 1], [3, 3, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_64_64_95 : ColCert where
  rK := ⟨64, by decide⟩
  rH := ⟨64, by decide⟩
  m := 5
  T1 := T64_64
  T2 := Q2.T64_64_2
  h1 := (3,2,4,0,0)
  h2 := (3,2,4,0,2)
  D := [[3, 4, 0], [3, 4, 2], [3, 4, 4], [3, 4, 1], [3, 4, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_64_64_100 : ColCert where
  rK := ⟨64, by decide⟩
  rH := ⟨64, by decide⟩
  m := 5
  T1 := T64_64
  T2 := Q2.T64_64_2
  h1 := (4,1,0,1,2)
  h2 := (4,1,0,1,0)
  D := [[4, 0, 0], [4, 0, 1], [4, 0, 2], [4, 0, 3], [4, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_64_64_105 : ColCert where
  rK := ⟨64, by decide⟩
  rH := ⟨64, by decide⟩
  m := 5
  T1 := T64_64
  T2 := Q2.T64_64_2
  h1 := (4,1,1,2,2)
  h2 := (4,1,1,2,0)
  D := [[4, 1, 0], [4, 1, 1], [4, 1, 2], [4, 1, 3], [4, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_64_64_110 : ColCert where
  rK := ⟨64, by decide⟩
  rH := ⟨64, by decide⟩
  m := 5
  T1 := T64_64
  T2 := Q2.T64_64_2
  h1 := (4,1,2,3,2)
  h2 := (4,1,2,3,0)
  D := [[4, 2, 0], [4, 2, 1], [4, 2, 2], [4, 2, 3], [4, 2, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_64_64_115 : ColCert where
  rK := ⟨64, by decide⟩
  rH := ⟨64, by decide⟩
  m := 5
  T1 := T64_64
  T2 := Q2.T64_64_2
  h1 := (4,1,3,4,2)
  h2 := (4,1,3,4,0)
  D := [[4, 3, 0], [4, 3, 1], [4, 3, 2], [4, 3, 3], [4, 3, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_64_64_120 : ColCert where
  rK := ⟨64, by decide⟩
  rH := ⟨64, by decide⟩
  m := 5
  T1 := T64_64
  T2 := Q2.T64_64_2
  h1 := (4,1,4,0,2)
  h2 := (4,1,4,0,0)
  D := [[4, 4, 0], [4, 4, 1], [4, 4, 2], [4, 4, 3], [4, 4, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_65_0_0 : ColCert where
  rK := ⟨65, by decide⟩
  rH := ⟨0, by decide⟩
  m := 25
  T1 := T65_0
  T2 := Q2.T65_0_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_65_9_0 : ColCert where
  rK := ⟨65, by decide⟩
  rH := ⟨9, by decide⟩
  m := 25
  T1 := T65_9
  T2 := Q2.T65_9_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_65_9_1 : ColCert where
  rK := ⟨65, by decide⟩
  rH := ⟨9, by decide⟩
  m := 25
  T1 := T65_9
  T2 := Q2.T65_9_2
  h1 := (0,0,1,0,4)
  h2 := (0,0,1,0,4)
  D := [[0, 1, 1], [0, 1, 1], [0, 1, 1], [0, 1, 1], [0, 1, 1], [0, 1, 2], [0, 1, 2], [0, 1, 2], [0, 1, 2], [0, 1, 2], [0, 1, 3], [0, 1, 3], [0, 1, 3], [0, 1, 3], [0, 1, 3], [0, 1, 4], [0, 1, 4], [0, 1, 4], [0, 1, 4], [0, 1, 4], [0, 1, 0], [0, 1, 0], [0, 1, 0], [0, 1, 0], [0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_65_9_2 : ColCert where
  rK := ⟨65, by decide⟩
  rH := ⟨9, by decide⟩
  m := 25
  T1 := T65_9
  T2 := Q2.T65_9_2
  h1 := (0,0,2,0,3)
  h2 := (0,0,2,0,3)
  D := [[0, 2, 2], [0, 2, 2], [0, 2, 2], [0, 2, 2], [0, 2, 2], [0, 2, 4], [0, 2, 4], [0, 2, 4], [0, 2, 4], [0, 2, 4], [0, 2, 1], [0, 2, 1], [0, 2, 1], [0, 2, 1], [0, 2, 1], [0, 2, 3], [0, 2, 3], [0, 2, 3], [0, 2, 3], [0, 2, 3], [0, 2, 0], [0, 2, 0], [0, 2, 0], [0, 2, 0], [0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_65_9_3 : ColCert where
  rK := ⟨65, by decide⟩
  rH := ⟨9, by decide⟩
  m := 25
  T1 := T65_9
  T2 := Q2.T65_9_2
  h1 := (0,0,3,0,2)
  h2 := (0,0,3,0,2)
  D := [[0, 3, 3], [0, 3, 3], [0, 3, 3], [0, 3, 3], [0, 3, 3], [0, 3, 1], [0, 3, 1], [0, 3, 1], [0, 3, 1], [0, 3, 1], [0, 3, 4], [0, 3, 4], [0, 3, 4], [0, 3, 4], [0, 3, 4], [0, 3, 2], [0, 3, 2], [0, 3, 2], [0, 3, 2], [0, 3, 2], [0, 3, 0], [0, 3, 0], [0, 3, 0], [0, 3, 0], [0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_65_9_4 : ColCert where
  rK := ⟨65, by decide⟩
  rH := ⟨9, by decide⟩
  m := 25
  T1 := T65_9
  T2 := Q2.T65_9_2
  h1 := (0,0,4,0,1)
  h2 := (0,0,4,0,1)
  D := [[0, 4, 4], [0, 4, 4], [0, 4, 4], [0, 4, 4], [0, 4, 4], [0, 4, 3], [0, 4, 3], [0, 4, 3], [0, 4, 3], [0, 4, 3], [0, 4, 2], [0, 4, 2], [0, 4, 2], [0, 4, 2], [0, 4, 2], [0, 4, 1], [0, 4, 1], [0, 4, 1], [0, 4, 1], [0, 4, 1], [0, 4, 0], [0, 4, 0], [0, 4, 0], [0, 4, 0], [0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_65_12_0 : ColCert where
  rK := ⟨65, by decide⟩
  rH := ⟨12, by decide⟩
  m := 25
  T1 := T65_12
  T2 := Q2.T65_12_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_65_12_1 : ColCert where
  rK := ⟨65, by decide⟩
  rH := ⟨12, by decide⟩
  m := 25
  T1 := T65_12
  T2 := Q2.T65_12_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_65_12_2 : ColCert where
  rK := ⟨65, by decide⟩
  rH := ⟨12, by decide⟩
  m := 25
  T1 := T65_12
  T2 := Q2.T65_12_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_65_12_3 : ColCert where
  rK := ⟨65, by decide⟩
  rH := ⟨12, by decide⟩
  m := 25
  T1 := T65_12
  T2 := Q2.T65_12_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_65_12_4 : ColCert where
  rK := ⟨65, by decide⟩
  rH := ⟨12, by decide⟩
  m := 25
  T1 := T65_12
  T2 := Q2.T65_12_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_65_27_0 : ColCert where
  rK := ⟨65, by decide⟩
  rH := ⟨27, by decide⟩
  m := 25
  T1 := T65_27
  T2 := Q2.T65_27_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_65_27_1 : ColCert where
  rK := ⟨65, by decide⟩
  rH := ⟨27, by decide⟩
  m := 25
  T1 := T65_27
  T2 := Q2.T65_27_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_65_27_2 : ColCert where
  rK := ⟨65, by decide⟩
  rH := ⟨27, by decide⟩
  m := 25
  T1 := T65_27
  T2 := Q2.T65_27_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_65_27_3 : ColCert where
  rK := ⟨65, by decide⟩
  rH := ⟨27, by decide⟩
  m := 25
  T1 := T65_27
  T2 := Q2.T65_27_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_65_27_4 : ColCert where
  rK := ⟨65, by decide⟩
  rH := ⟨27, by decide⟩
  m := 25
  T1 := T65_27
  T2 := Q2.T65_27_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_65_27_5 : ColCert where
  rK := ⟨65, by decide⟩
  rH := ⟨27, by decide⟩
  m := 25
  T1 := T65_27
  T2 := Q2.T65_27_2
  h1 := (0,0,1,0,0)
  h2 := (0,0,1,0,0)
  D := [[0, 1, 2], [0, 1, 2], [0, 1, 2], [0, 1, 2], [0, 1, 2], [0, 1, 3], [0, 1, 3], [0, 1, 3], [0, 1, 3], [0, 1, 3], [0, 1, 4], [0, 1, 4], [0, 1, 4], [0, 1, 4], [0, 1, 4], [0, 1, 0], [0, 1, 0], [0, 1, 0], [0, 1, 0], [0, 1, 0], [0, 1, 1], [0, 1, 1], [0, 1, 1], [0, 1, 1], [0, 1, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_65_27_10 : ColCert where
  rK := ⟨65, by decide⟩
  rH := ⟨27, by decide⟩
  m := 25
  T1 := T65_27
  T2 := Q2.T65_27_2
  h1 := (0,0,2,0,0)
  h2 := (0,0,2,0,0)
  D := [[0, 2, 4], [0, 2, 4], [0, 2, 4], [0, 2, 4], [0, 2, 4], [0, 2, 1], [0, 2, 1], [0, 2, 1], [0, 2, 1], [0, 2, 1], [0, 2, 3], [0, 2, 3], [0, 2, 3], [0, 2, 3], [0, 2, 3], [0, 2, 0], [0, 2, 0], [0, 2, 0], [0, 2, 0], [0, 2, 0], [0, 2, 2], [0, 2, 2], [0, 2, 2], [0, 2, 2], [0, 2, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_65_27_15 : ColCert where
  rK := ⟨65, by decide⟩
  rH := ⟨27, by decide⟩
  m := 25
  T1 := T65_27
  T2 := Q2.T65_27_2
  h1 := (0,0,3,0,0)
  h2 := (0,0,3,0,0)
  D := [[0, 3, 1], [0, 3, 1], [0, 3, 1], [0, 3, 1], [0, 3, 1], [0, 3, 4], [0, 3, 4], [0, 3, 4], [0, 3, 4], [0, 3, 4], [0, 3, 2], [0, 3, 2], [0, 3, 2], [0, 3, 2], [0, 3, 2], [0, 3, 0], [0, 3, 0], [0, 3, 0], [0, 3, 0], [0, 3, 0], [0, 3, 3], [0, 3, 3], [0, 3, 3], [0, 3, 3], [0, 3, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_65_27_20 : ColCert where
  rK := ⟨65, by decide⟩
  rH := ⟨27, by decide⟩
  m := 25
  T1 := T65_27
  T2 := Q2.T65_27_2
  h1 := (0,0,4,0,0)
  h2 := (0,0,4,0,0)
  D := [[0, 4, 3], [0, 4, 3], [0, 4, 3], [0, 4, 3], [0, 4, 3], [0, 4, 2], [0, 4, 2], [0, 4, 2], [0, 4, 2], [0, 4, 2], [0, 4, 1], [0, 4, 1], [0, 4, 1], [0, 4, 1], [0, 4, 1], [0, 4, 0], [0, 4, 0], [0, 4, 0], [0, 4, 0], [0, 4, 0], [0, 4, 4], [0, 4, 4], [0, 4, 4], [0, 4, 4], [0, 4, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_65_30_0 : ColCert where
  rK := ⟨65, by decide⟩
  rH := ⟨30, by decide⟩
  m := 5
  T1 := T65_30
  T2 := Q2.T65_30_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_65_30_1 : ColCert where
  rK := ⟨65, by decide⟩
  rH := ⟨30, by decide⟩
  m := 5
  T1 := T65_30
  T2 := Q2.T65_30_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_65_30_2 : ColCert where
  rK := ⟨65, by decide⟩
  rH := ⟨30, by decide⟩
  m := 5
  T1 := T65_30
  T2 := Q2.T65_30_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_65_30_3 : ColCert where
  rK := ⟨65, by decide⟩
  rH := ⟨30, by decide⟩
  m := 5
  T1 := T65_30
  T2 := Q2.T65_30_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_65_30_4 : ColCert where
  rK := ⟨65, by decide⟩
  rH := ⟨30, by decide⟩
  m := 5
  T1 := T65_30
  T2 := Q2.T65_30_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_65_30_5 : ColCert where
  rK := ⟨65, by decide⟩
  rH := ⟨30, by decide⟩
  m := 5
  T1 := T65_30
  T2 := Q2.T65_30_2
  h1 := (1,2,3,2,3)
  h2 := (1,2,3,2,0)
  D := [[1, 3, 0], [1, 3, 4], [1, 3, 3], [1, 3, 2], [1, 3, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_65_30_10 : ColCert where
  rK := ⟨65, by decide⟩
  rH := ⟨30, by decide⟩
  m := 5
  T1 := T65_30
  T2 := Q2.T65_30_2
  h1 := (2,4,1,1,4)
  h2 := (2,4,1,1,3)
  D := [[2, 1, 4], [2, 1, 2], [2, 1, 0], [2, 1, 3], [2, 1, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_65_30_15 : ColCert where
  rK := ⟨65, by decide⟩
  rH := ⟨30, by decide⟩
  m := 5
  T1 := T65_30
  T2 := Q2.T65_30_2
  h1 := (3,1,4,2,1)
  h2 := (3,1,4,2,3)
  D := [[3, 4, 2], [3, 4, 4], [3, 4, 1], [3, 4, 3], [3, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_65_30_20 : ColCert where
  rK := ⟨65, by decide⟩
  rH := ⟨30, by decide⟩
  m := 5
  T1 := T65_30
  T2 := Q2.T65_30_2
  h1 := (4,3,2,0,4)
  h2 := (4,3,2,0,3)
  D := [[4, 2, 4], [4, 2, 0], [4, 2, 1], [4, 2, 2], [4, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_65_35_0 : ColCert where
  rK := ⟨65, by decide⟩
  rH := ⟨35, by decide⟩
  m := 5
  T1 := T65_35
  T2 := Q2.T65_35_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_65_35_1 : ColCert where
  rK := ⟨65, by decide⟩
  rH := ⟨35, by decide⟩
  m := 5
  T1 := T65_35
  T2 := Q2.T65_35_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_65_35_2 : ColCert where
  rK := ⟨65, by decide⟩
  rH := ⟨35, by decide⟩
  m := 5
  T1 := T65_35
  T2 := Q2.T65_35_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_65_35_3 : ColCert where
  rK := ⟨65, by decide⟩
  rH := ⟨35, by decide⟩
  m := 5
  T1 := T65_35
  T2 := Q2.T65_35_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_65_35_4 : ColCert where
  rK := ⟨65, by decide⟩
  rH := ⟨35, by decide⟩
  m := 5
  T1 := T65_35
  T2 := Q2.T65_35_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_65_35_5 : ColCert where
  rK := ⟨65, by decide⟩
  rH := ⟨35, by decide⟩
  m := 5
  T1 := T65_35
  T2 := Q2.T65_35_2
  h1 := (1,2,4,2,0)
  h2 := (1,2,4,2,2)
  D := [[1, 4, 0], [1, 4, 4], [1, 4, 3], [1, 4, 2], [1, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_65_35_10 : ColCert where
  rK := ⟨65, by decide⟩
  rH := ⟨35, by decide⟩
  m := 5
  T1 := T65_35
  T2 := Q2.T65_35_2
  h1 := (2,4,3,1,0)
  h2 := (2,4,3,1,4)
  D := [[2, 3, 2], [2, 3, 0], [2, 3, 3], [2, 3, 1], [2, 3, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_65_35_15 : ColCert where
  rK := ⟨65, by decide⟩
  rH := ⟨35, by decide⟩
  m := 5
  T1 := T65_35
  T2 := Q2.T65_35_2
  h1 := (3,1,2,2,3)
  h2 := (3,1,2,2,0)
  D := [[3, 2, 1], [3, 2, 3], [3, 2, 0], [3, 2, 2], [3, 2, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_65_35_20 : ColCert where
  rK := ⟨65, by decide⟩
  rH := ⟨35, by decide⟩
  m := 5
  T1 := T65_35
  T2 := Q2.T65_35_2
  h1 := (4,3,1,0,4)
  h2 := (4,3,1,0,3)
  D := [[4, 1, 2], [4, 1, 3], [4, 1, 4], [4, 1, 0], [4, 1, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_65_40_0 : ColCert where
  rK := ⟨65, by decide⟩
  rH := ⟨40, by decide⟩
  m := 5
  T1 := T65_40
  T2 := Q2.T65_40_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_65_40_1 : ColCert where
  rK := ⟨65, by decide⟩
  rH := ⟨40, by decide⟩
  m := 5
  T1 := T65_40
  T2 := Q2.T65_40_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_65_40_2 : ColCert where
  rK := ⟨65, by decide⟩
  rH := ⟨40, by decide⟩
  m := 5
  T1 := T65_40
  T2 := Q2.T65_40_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_65_40_3 : ColCert where
  rK := ⟨65, by decide⟩
  rH := ⟨40, by decide⟩
  m := 5
  T1 := T65_40
  T2 := Q2.T65_40_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_65_40_4 : ColCert where
  rK := ⟨65, by decide⟩
  rH := ⟨40, by decide⟩
  m := 5
  T1 := T65_40
  T2 := Q2.T65_40_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_65_40_5 : ColCert where
  rK := ⟨65, by decide⟩
  rH := ⟨40, by decide⟩
  m := 5
  T1 := T65_40
  T2 := Q2.T65_40_2
  h1 := (1,2,1,2,4)
  h2 := (1,2,1,2,1)
  D := [[1, 1, 0], [1, 1, 4], [1, 1, 3], [1, 1, 2], [1, 1, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_65_40_10 : ColCert where
  rK := ⟨65, by decide⟩
  rH := ⟨40, by decide⟩
  m := 5
  T1 := T65_40
  T2 := Q2.T65_40_2
  h1 := (2,4,2,1,2)
  h2 := (2,4,2,1,1)
  D := [[2, 2, 3], [2, 2, 1], [2, 2, 4], [2, 2, 2], [2, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_65_40_15 : ColCert where
  rK := ⟨65, by decide⟩
  rH := ⟨40, by decide⟩
  m := 5
  T1 := T65_40
  T2 := Q2.T65_40_2
  h1 := (3,1,3,2,2)
  h2 := (3,1,3,2,4)
  D := [[3, 3, 4], [3, 3, 1], [3, 3, 3], [3, 3, 0], [3, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_65_40_20 : ColCert where
  rK := ⟨65, by decide⟩
  rH := ⟨40, by decide⟩
  m := 5
  T1 := T65_40
  T2 := Q2.T65_40_2
  h1 := (4,3,4,0,4)
  h2 := (4,3,4,0,3)
  D := [[4, 4, 3], [4, 4, 4], [4, 4, 0], [4, 4, 1], [4, 4, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_65_45_0 : ColCert where
  rK := ⟨65, by decide⟩
  rH := ⟨45, by decide⟩
  m := 5
  T1 := T65_45
  T2 := Q2.T65_45_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

end LeanDring.P5Presentation
