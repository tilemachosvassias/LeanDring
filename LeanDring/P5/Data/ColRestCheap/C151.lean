/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.Twin1.ColCert
import LeanDring.P5.Data.EntryK.C015

/-!
# Species-table cell data, stage 2 — twin-coincident columns (cheap tier)

Per-column certified exponent-vector data (`ColCert`/`ColCertDiv`) with kernel
`decide` bindings. Emitted; the embedded lists are what the kernel certifies.
rest tier, chunk 150: 60 columns.
-/

-- machine-emitted data: silence style linters (generated long lines, file-level options)
set_option linter.style.longLine false

namespace LeanDring.P5Presentation

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

def colCert_63_63_3 : ColCert where
  rK := ⟨63, by decide⟩
  rH := ⟨63, by decide⟩
  m := 5
  T1 := T63_63
  T2 := Q2.T63_63_2
  h1 := (0,0,3,1,0)
  h2 := (0,0,3,1,0)
  D := [[0, 3, 0], [0, 3, 0], [0, 3, 0], [0, 3, 0], [0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_63_63_4 : ColCert where
  rK := ⟨63, by decide⟩
  rH := ⟨63, by decide⟩
  m := 5
  T1 := T63_63
  T2 := Q2.T63_63_2
  h1 := (0,0,4,3,0)
  h2 := (0,0,4,3,0)
  D := [[0, 4, 0], [0, 4, 0], [0, 4, 0], [0, 4, 0], [0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_63_63_5 : ColCert where
  rK := ⟨63, by decide⟩
  rH := ⟨63, by decide⟩
  m := 5
  T1 := T63_63
  T2 := Q2.T63_63_2
  h1 := (1,4,0,3,3)
  h2 := (1,4,0,3,4)
  D := [[1, 0, 4], [1, 0, 3], [1, 0, 2], [1, 0, 1], [1, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_63_63_6 : ColCert where
  rK := ⟨63, by decide⟩
  rH := ⟨63, by decide⟩
  m := 5
  T1 := T63_63
  T2 := Q2.T63_63_2
  h1 := (1,4,1,0,3)
  h2 := (1,4,1,0,4)
  D := [[1, 1, 3], [1, 1, 2], [1, 1, 1], [1, 1, 0], [1, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_63_63_7 : ColCert where
  rK := ⟨63, by decide⟩
  rH := ⟨63, by decide⟩
  m := 5
  T1 := T63_63
  T2 := Q2.T63_63_2
  h1 := (1,4,2,2,3)
  h2 := (1,4,2,2,4)
  D := [[1, 2, 2], [1, 2, 1], [1, 2, 0], [1, 2, 4], [1, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_63_63_8 : ColCert where
  rK := ⟨63, by decide⟩
  rH := ⟨63, by decide⟩
  m := 5
  T1 := T63_63
  T2 := Q2.T63_63_2
  h1 := (1,4,3,4,3)
  h2 := (1,4,3,4,4)
  D := [[1, 3, 1], [1, 3, 0], [1, 3, 4], [1, 3, 3], [1, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_63_63_9 : ColCert where
  rK := ⟨63, by decide⟩
  rH := ⟨63, by decide⟩
  m := 5
  T1 := T63_63
  T2 := Q2.T63_63_2
  h1 := (1,4,4,1,3)
  h2 := (1,4,4,1,4)
  D := [[1, 4, 0], [1, 4, 4], [1, 4, 3], [1, 4, 2], [1, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_63_63_10 : ColCert where
  rK := ⟨63, by decide⟩
  rH := ⟨63, by decide⟩
  m := 5
  T1 := T63_63
  T2 := Q2.T63_63_2
  h1 := (2,3,0,0,0)
  h2 := (2,3,0,0,3)
  D := [[2, 0, 3], [2, 0, 1], [2, 0, 4], [2, 0, 2], [2, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_63_63_11 : ColCert where
  rK := ⟨63, by decide⟩
  rH := ⟨63, by decide⟩
  m := 5
  T1 := T63_63
  T2 := Q2.T63_63_2
  h1 := (2,3,1,2,0)
  h2 := (2,3,1,2,3)
  D := [[2, 1, 1], [2, 1, 4], [2, 1, 2], [2, 1, 0], [2, 1, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_63_63_12 : ColCert where
  rK := ⟨63, by decide⟩
  rH := ⟨63, by decide⟩
  m := 5
  T1 := T63_63
  T2 := Q2.T63_63_2
  h1 := (2,3,2,4,0)
  h2 := (2,3,2,4,3)
  D := [[2, 2, 4], [2, 2, 2], [2, 2, 0], [2, 2, 3], [2, 2, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_63_63_13 : ColCert where
  rK := ⟨63, by decide⟩
  rH := ⟨63, by decide⟩
  m := 5
  T1 := T63_63
  T2 := Q2.T63_63_2
  h1 := (2,3,3,1,0)
  h2 := (2,3,3,1,3)
  D := [[2, 3, 2], [2, 3, 0], [2, 3, 3], [2, 3, 1], [2, 3, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_63_63_14 : ColCert where
  rK := ⟨63, by decide⟩
  rH := ⟨63, by decide⟩
  m := 5
  T1 := T63_63
  T2 := Q2.T63_63_2
  h1 := (2,3,4,3,0)
  h2 := (2,3,4,3,3)
  D := [[2, 4, 0], [2, 4, 3], [2, 4, 1], [2, 4, 4], [2, 4, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_63_63_15 : ColCert where
  rK := ⟨63, by decide⟩
  rH := ⟨63, by decide⟩
  m := 5
  T1 := T63_63
  T2 := Q2.T63_63_2
  h1 := (3,2,0,1,4)
  h2 := (3,2,0,1,4)
  D := [[3, 0, 2], [3, 0, 4], [3, 0, 1], [3, 0, 3], [3, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_63_63_16 : ColCert where
  rK := ⟨63, by decide⟩
  rH := ⟨63, by decide⟩
  m := 5
  T1 := T63_63
  T2 := Q2.T63_63_2
  h1 := (3,2,1,3,4)
  h2 := (3,2,1,3,4)
  D := [[3, 1, 4], [3, 1, 1], [3, 1, 3], [3, 1, 0], [3, 1, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_63_63_17 : ColCert where
  rK := ⟨63, by decide⟩
  rH := ⟨63, by decide⟩
  m := 5
  T1 := T63_63
  T2 := Q2.T63_63_2
  h1 := (3,2,2,0,4)
  h2 := (3,2,2,0,4)
  D := [[3, 2, 1], [3, 2, 3], [3, 2, 0], [3, 2, 2], [3, 2, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_63_63_18 : ColCert where
  rK := ⟨63, by decide⟩
  rH := ⟨63, by decide⟩
  m := 5
  T1 := T63_63
  T2 := Q2.T63_63_2
  h1 := (3,2,3,2,4)
  h2 := (3,2,3,2,4)
  D := [[3, 3, 3], [3, 3, 0], [3, 3, 2], [3, 3, 4], [3, 3, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_63_63_19 : ColCert where
  rK := ⟨63, by decide⟩
  rH := ⟨63, by decide⟩
  m := 5
  T1 := T63_63
  T2 := Q2.T63_63_2
  h1 := (3,2,4,4,4)
  h2 := (3,2,4,4,4)
  D := [[3, 4, 0], [3, 4, 2], [3, 4, 4], [3, 4, 1], [3, 4, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_63_63_20 : ColCert where
  rK := ⟨63, by decide⟩
  rH := ⟨63, by decide⟩
  m := 5
  T1 := T63_63
  T2 := Q2.T63_63_2
  h1 := (4,1,0,1,4)
  h2 := (4,1,0,1,1)
  D := [[4, 0, 1], [4, 0, 2], [4, 0, 3], [4, 0, 4], [4, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_63_63_21 : ColCert where
  rK := ⟨63, by decide⟩
  rH := ⟨63, by decide⟩
  m := 5
  T1 := T63_63
  T2 := Q2.T63_63_2
  h1 := (4,1,1,3,4)
  h2 := (4,1,1,3,1)
  D := [[4, 1, 2], [4, 1, 3], [4, 1, 4], [4, 1, 0], [4, 1, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_63_63_22 : ColCert where
  rK := ⟨63, by decide⟩
  rH := ⟨63, by decide⟩
  m := 5
  T1 := T63_63
  T2 := Q2.T63_63_2
  h1 := (4,1,2,0,4)
  h2 := (4,1,2,0,1)
  D := [[4, 2, 3], [4, 2, 4], [4, 2, 0], [4, 2, 1], [4, 2, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_63_63_23 : ColCert where
  rK := ⟨63, by decide⟩
  rH := ⟨63, by decide⟩
  m := 5
  T1 := T63_63
  T2 := Q2.T63_63_2
  h1 := (4,1,3,2,4)
  h2 := (4,1,3,2,1)
  D := [[4, 3, 4], [4, 3, 0], [4, 3, 1], [4, 3, 2], [4, 3, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_63_63_24 : ColCert where
  rK := ⟨63, by decide⟩
  rH := ⟨63, by decide⟩
  m := 5
  T1 := T63_63
  T2 := Q2.T63_63_2
  h1 := (4,1,4,4,4)
  h2 := (4,1,4,4,1)
  D := [[4, 4, 0], [4, 4, 1], [4, 4, 2], [4, 4, 3], [4, 4, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_64_0_0 : ColCert where
  rK := ⟨64, by decide⟩
  rH := ⟨0, by decide⟩
  m := 25
  T1 := T64_0
  T2 := Q2.T64_0_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_64_8_0 : ColCert where
  rK := ⟨64, by decide⟩
  rH := ⟨8, by decide⟩
  m := 25
  T1 := T64_8
  T2 := Q2.T64_8_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_64_8_1 : ColCert where
  rK := ⟨64, by decide⟩
  rH := ⟨8, by decide⟩
  m := 25
  T1 := T64_8
  T2 := Q2.T64_8_2
  h1 := (0,0,1,1,4)
  h2 := (0,0,1,1,4)
  D := [[0, 1, 3], [0, 1, 3], [0, 1, 3], [0, 1, 3], [0, 1, 3], [0, 1, 4], [0, 1, 4], [0, 1, 4], [0, 1, 4], [0, 1, 4], [0, 1, 0], [0, 1, 0], [0, 1, 0], [0, 1, 0], [0, 1, 0], [0, 1, 1], [0, 1, 1], [0, 1, 1], [0, 1, 1], [0, 1, 1], [0, 1, 2], [0, 1, 2], [0, 1, 2], [0, 1, 2], [0, 1, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_64_8_2 : ColCert where
  rK := ⟨64, by decide⟩
  rH := ⟨8, by decide⟩
  m := 25
  T1 := T64_8
  T2 := Q2.T64_8_2
  h1 := (0,0,2,2,3)
  h2 := (0,0,2,2,3)
  D := [[0, 2, 1], [0, 2, 1], [0, 2, 1], [0, 2, 1], [0, 2, 1], [0, 2, 3], [0, 2, 3], [0, 2, 3], [0, 2, 3], [0, 2, 3], [0, 2, 0], [0, 2, 0], [0, 2, 0], [0, 2, 0], [0, 2, 0], [0, 2, 2], [0, 2, 2], [0, 2, 2], [0, 2, 2], [0, 2, 2], [0, 2, 4], [0, 2, 4], [0, 2, 4], [0, 2, 4], [0, 2, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_64_8_3 : ColCert where
  rK := ⟨64, by decide⟩
  rH := ⟨8, by decide⟩
  m := 25
  T1 := T64_8
  T2 := Q2.T64_8_2
  h1 := (0,0,3,3,2)
  h2 := (0,0,3,3,2)
  D := [[0, 3, 4], [0, 3, 4], [0, 3, 4], [0, 3, 4], [0, 3, 4], [0, 3, 2], [0, 3, 2], [0, 3, 2], [0, 3, 2], [0, 3, 2], [0, 3, 0], [0, 3, 0], [0, 3, 0], [0, 3, 0], [0, 3, 0], [0, 3, 3], [0, 3, 3], [0, 3, 3], [0, 3, 3], [0, 3, 3], [0, 3, 1], [0, 3, 1], [0, 3, 1], [0, 3, 1], [0, 3, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_64_8_4 : ColCert where
  rK := ⟨64, by decide⟩
  rH := ⟨8, by decide⟩
  m := 25
  T1 := T64_8
  T2 := Q2.T64_8_2
  h1 := (0,0,4,4,1)
  h2 := (0,0,4,4,1)
  D := [[0, 4, 2], [0, 4, 2], [0, 4, 2], [0, 4, 2], [0, 4, 2], [0, 4, 1], [0, 4, 1], [0, 4, 1], [0, 4, 1], [0, 4, 1], [0, 4, 0], [0, 4, 0], [0, 4, 0], [0, 4, 0], [0, 4, 0], [0, 4, 4], [0, 4, 4], [0, 4, 4], [0, 4, 4], [0, 4, 4], [0, 4, 3], [0, 4, 3], [0, 4, 3], [0, 4, 3], [0, 4, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_64_12_0 : ColCert where
  rK := ⟨64, by decide⟩
  rH := ⟨12, by decide⟩
  m := 25
  T1 := T64_12
  T2 := Q2.T64_12_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_64_12_1 : ColCert where
  rK := ⟨64, by decide⟩
  rH := ⟨12, by decide⟩
  m := 25
  T1 := T64_12
  T2 := Q2.T64_12_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_64_12_2 : ColCert where
  rK := ⟨64, by decide⟩
  rH := ⟨12, by decide⟩
  m := 25
  T1 := T64_12
  T2 := Q2.T64_12_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_64_12_3 : ColCert where
  rK := ⟨64, by decide⟩
  rH := ⟨12, by decide⟩
  m := 25
  T1 := T64_12
  T2 := Q2.T64_12_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_64_12_4 : ColCert where
  rK := ⟨64, by decide⟩
  rH := ⟨12, by decide⟩
  m := 25
  T1 := T64_12
  T2 := Q2.T64_12_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_64_26_0 : ColCert where
  rK := ⟨64, by decide⟩
  rH := ⟨26, by decide⟩
  m := 25
  T1 := T64_26
  T2 := Q2.T64_26_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_64_26_1 : ColCert where
  rK := ⟨64, by decide⟩
  rH := ⟨26, by decide⟩
  m := 25
  T1 := T64_26
  T2 := Q2.T64_26_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_64_26_2 : ColCert where
  rK := ⟨64, by decide⟩
  rH := ⟨26, by decide⟩
  m := 25
  T1 := T64_26
  T2 := Q2.T64_26_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_64_26_3 : ColCert where
  rK := ⟨64, by decide⟩
  rH := ⟨26, by decide⟩
  m := 25
  T1 := T64_26
  T2 := Q2.T64_26_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_64_26_4 : ColCert where
  rK := ⟨64, by decide⟩
  rH := ⟨26, by decide⟩
  m := 25
  T1 := T64_26
  T2 := Q2.T64_26_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_64_26_5 : ColCert where
  rK := ⟨64, by decide⟩
  rH := ⟨26, by decide⟩
  m := 25
  T1 := T64_26
  T2 := Q2.T64_26_2
  h1 := (0,0,1,1,0)
  h2 := (0,0,1,1,0)
  D := [[0, 1, 4], [0, 1, 4], [0, 1, 4], [0, 1, 4], [0, 1, 4], [0, 1, 0], [0, 1, 0], [0, 1, 0], [0, 1, 0], [0, 1, 0], [0, 1, 1], [0, 1, 1], [0, 1, 1], [0, 1, 1], [0, 1, 1], [0, 1, 2], [0, 1, 2], [0, 1, 2], [0, 1, 2], [0, 1, 2], [0, 1, 3], [0, 1, 3], [0, 1, 3], [0, 1, 3], [0, 1, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_64_26_10 : ColCert where
  rK := ⟨64, by decide⟩
  rH := ⟨26, by decide⟩
  m := 25
  T1 := T64_26
  T2 := Q2.T64_26_2
  h1 := (0,0,2,2,0)
  h2 := (0,0,2,2,0)
  D := [[0, 2, 3], [0, 2, 3], [0, 2, 3], [0, 2, 3], [0, 2, 3], [0, 2, 0], [0, 2, 0], [0, 2, 0], [0, 2, 0], [0, 2, 0], [0, 2, 2], [0, 2, 2], [0, 2, 2], [0, 2, 2], [0, 2, 2], [0, 2, 4], [0, 2, 4], [0, 2, 4], [0, 2, 4], [0, 2, 4], [0, 2, 1], [0, 2, 1], [0, 2, 1], [0, 2, 1], [0, 2, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_64_26_15 : ColCert where
  rK := ⟨64, by decide⟩
  rH := ⟨26, by decide⟩
  m := 25
  T1 := T64_26
  T2 := Q2.T64_26_2
  h1 := (0,0,3,3,0)
  h2 := (0,0,3,3,0)
  D := [[0, 3, 2], [0, 3, 2], [0, 3, 2], [0, 3, 2], [0, 3, 2], [0, 3, 0], [0, 3, 0], [0, 3, 0], [0, 3, 0], [0, 3, 0], [0, 3, 3], [0, 3, 3], [0, 3, 3], [0, 3, 3], [0, 3, 3], [0, 3, 1], [0, 3, 1], [0, 3, 1], [0, 3, 1], [0, 3, 1], [0, 3, 4], [0, 3, 4], [0, 3, 4], [0, 3, 4], [0, 3, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_64_26_20 : ColCert where
  rK := ⟨64, by decide⟩
  rH := ⟨26, by decide⟩
  m := 25
  T1 := T64_26
  T2 := Q2.T64_26_2
  h1 := (0,0,4,4,0)
  h2 := (0,0,4,4,0)
  D := [[0, 4, 1], [0, 4, 1], [0, 4, 1], [0, 4, 1], [0, 4, 1], [0, 4, 0], [0, 4, 0], [0, 4, 0], [0, 4, 0], [0, 4, 0], [0, 4, 4], [0, 4, 4], [0, 4, 4], [0, 4, 4], [0, 4, 4], [0, 4, 3], [0, 4, 3], [0, 4, 3], [0, 4, 3], [0, 4, 3], [0, 4, 2], [0, 4, 2], [0, 4, 2], [0, 4, 2], [0, 4, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_64_29_0 : ColCert where
  rK := ⟨64, by decide⟩
  rH := ⟨29, by decide⟩
  m := 5
  T1 := T64_29
  T2 := Q2.T64_29_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_64_29_1 : ColCert where
  rK := ⟨64, by decide⟩
  rH := ⟨29, by decide⟩
  m := 5
  T1 := T64_29
  T2 := Q2.T64_29_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_64_29_2 : ColCert where
  rK := ⟨64, by decide⟩
  rH := ⟨29, by decide⟩
  m := 5
  T1 := T64_29
  T2 := Q2.T64_29_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_64_29_3 : ColCert where
  rK := ⟨64, by decide⟩
  rH := ⟨29, by decide⟩
  m := 5
  T1 := T64_29
  T2 := Q2.T64_29_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_64_29_4 : ColCert where
  rK := ⟨64, by decide⟩
  rH := ⟨29, by decide⟩
  m := 5
  T1 := T64_29
  T2 := Q2.T64_29_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_64_29_5 : ColCert where
  rK := ⟨64, by decide⟩
  rH := ⟨29, by decide⟩
  m := 5
  T1 := T64_29
  T2 := Q2.T64_29_2
  h1 := (1,4,1,3,3)
  h2 := (1,4,1,3,3)
  D := [[1, 1, 3], [1, 1, 2], [1, 1, 1], [1, 1, 0], [1, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_64_29_10 : ColCert where
  rK := ⟨64, by decide⟩
  rH := ⟨29, by decide⟩
  m := 5
  T1 := T64_29
  T2 := Q2.T64_29_2
  h1 := (2,3,2,0,4)
  h2 := (2,3,2,0,0)
  D := [[2, 2, 1], [2, 2, 4], [2, 2, 2], [2, 2, 0], [2, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_64_29_15 : ColCert where
  rK := ⟨64, by decide⟩
  rH := ⟨29, by decide⟩
  m := 5
  T1 := T64_29
  T2 := Q2.T64_29_2
  h1 := (3,2,3,1,1)
  h2 := (3,2,3,1,3)
  D := [[3, 3, 4], [3, 3, 1], [3, 3, 3], [3, 3, 0], [3, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_64_29_20 : ColCert where
  rK := ⟨64, by decide⟩
  rH := ⟨29, by decide⟩
  m := 5
  T1 := T64_29
  T2 := Q2.T64_29_2
  h1 := (4,1,4,1,3)
  h2 := (4,1,4,1,1)
  D := [[4, 4, 2], [4, 4, 3], [4, 4, 4], [4, 4, 0], [4, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_64_34_0 : ColCert where
  rK := ⟨64, by decide⟩
  rH := ⟨34, by decide⟩
  m := 5
  T1 := T64_34
  T2 := Q2.T64_34_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_64_34_1 : ColCert where
  rK := ⟨64, by decide⟩
  rH := ⟨34, by decide⟩
  m := 5
  T1 := T64_34
  T2 := Q2.T64_34_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_64_34_2 : ColCert where
  rK := ⟨64, by decide⟩
  rH := ⟨34, by decide⟩
  m := 5
  T1 := T64_34
  T2 := Q2.T64_34_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_64_34_3 : ColCert where
  rK := ⟨64, by decide⟩
  rH := ⟨34, by decide⟩
  m := 5
  T1 := T64_34
  T2 := Q2.T64_34_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_64_34_4 : ColCert where
  rK := ⟨64, by decide⟩
  rH := ⟨34, by decide⟩
  m := 5
  T1 := T64_34
  T2 := Q2.T64_34_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_64_34_5 : ColCert where
  rK := ⟨64, by decide⟩
  rH := ⟨34, by decide⟩
  m := 5
  T1 := T64_34
  T2 := Q2.T64_34_2
  h1 := (1,4,3,3,1)
  h2 := (1,4,3,3,1)
  D := [[1, 3, 0], [1, 3, 4], [1, 3, 3], [1, 3, 2], [1, 3, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_64_34_10 : ColCert where
  rK := ⟨64, by decide⟩
  rH := ⟨34, by decide⟩
  m := 5
  T1 := T64_34
  T2 := Q2.T64_34_2
  h1 := (2,3,1,0,3)
  h2 := (2,3,1,0,4)
  D := [[2, 1, 0], [2, 1, 3], [2, 1, 1], [2, 1, 4], [2, 1, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_64_34_15 : ColCert where
  rK := ⟨64, by decide⟩
  rH := ⟨34, by decide⟩
  m := 5
  T1 := T64_34
  T2 := Q2.T64_34_2
  h1 := (3,2,4,1,4)
  h2 := (3,2,4,1,1)
  D := [[3, 4, 0], [3, 4, 2], [3, 4, 4], [3, 4, 1], [3, 4, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_64_34_20 : ColCert where
  rK := ⟨64, by decide⟩
  rH := ⟨34, by decide⟩
  m := 5
  T1 := T64_34
  T2 := Q2.T64_34_2
  h1 := (4,1,2,1,3)
  h2 := (4,1,2,1,1)
  D := [[4, 2, 0], [4, 2, 1], [4, 2, 2], [4, 2, 3], [4, 2, 4]]
  bind1 := by decide
  bind2 := by decide

end LeanDring.P5Presentation
