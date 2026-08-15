/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.Twin1.ColCert
import LeanDring.P5.Data.EntryK.C025

/-!
# Species-table cell data, stage 2 — column-data-divergent columns

Per-column certified exponent-vector data (`ColCert`/`ColCertDiv`) with kernel
`decide` bindings. Emitted; the embedded lists are what the kernel certifies.
cdd tier, chunk 1: 60 columns.
-/

-- machine-emitted data: silence style linters (generated long lines, file-level options)
set_option linter.style.longLine false

namespace LeanDring.P5Presentation

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

def colCertDiv_116_48_5 : ColCertDiv where
  rK := ⟨116, by decide⟩
  rH := ⟨48, by decide⟩
  m := 5
  T1 := T116_48
  T2 := Q2.T116_48_2
  h1 := (0,1,0,4,3)
  h2 := (0,1,0,4,1)
  D1 := [[1, 0, 4, 3], [1, 0, 0, 2], [1, 0, 1, 2], [1, 0, 2, 3], [1, 0, 3, 0]]
  D2 := [[1, 0, 4, 1], [1, 0, 0, 0], [1, 0, 1, 0], [1, 0, 2, 1], [1, 0, 3, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_116_48_10 : ColCertDiv where
  rK := ⟨116, by decide⟩
  rH := ⟨48, by decide⟩
  m := 5
  T1 := T116_48
  T2 := Q2.T116_48_2
  h1 := (0,2,0,3,1)
  h2 := (0,2,0,3,2)
  D1 := [[2, 0, 3, 1], [2, 0, 0, 4], [2, 0, 2, 4], [2, 0, 4, 1], [2, 0, 1, 0]]
  D2 := [[2, 0, 3, 2], [2, 0, 0, 0], [2, 0, 2, 0], [2, 0, 4, 2], [2, 0, 1, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_116_48_15 : ColCertDiv where
  rK := ⟨116, by decide⟩
  rH := ⟨48, by decide⟩
  m := 5
  T1 := T116_48
  T2 := Q2.T116_48_2
  h1 := (0,3,0,2,4)
  h2 := (0,3,0,2,3)
  D1 := [[3, 0, 2, 4], [3, 0, 0, 1], [3, 0, 3, 1], [3, 0, 1, 4], [3, 0, 4, 0]]
  D2 := [[3, 0, 2, 3], [3, 0, 0, 0], [3, 0, 3, 0], [3, 0, 1, 3], [3, 0, 4, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_116_48_20 : ColCertDiv where
  rK := ⟨116, by decide⟩
  rH := ⟨48, by decide⟩
  m := 5
  T1 := T116_48
  T2 := Q2.T116_48_2
  h1 := (0,4,0,1,2)
  h2 := (0,4,0,1,4)
  D1 := [[4, 0, 1, 2], [4, 0, 0, 3], [4, 0, 4, 3], [4, 0, 3, 2], [4, 0, 2, 0]]
  D2 := [[4, 0, 1, 4], [4, 0, 0, 0], [4, 0, 4, 0], [4, 0, 3, 4], [4, 0, 2, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_116_55_5 : ColCertDiv where
  rK := ⟨116, by decide⟩
  rH := ⟨55, by decide⟩
  m := 5
  T1 := T116_55
  T2 := Q2.T116_55_2
  h1 := (0,1,0,4,3)
  h2 := (0,1,0,4,1)
  D1 := [[1, 0, 4, 3], [1, 0, 0, 2], [1, 0, 1, 2], [1, 0, 2, 3], [1, 0, 3, 0]]
  D2 := [[1, 0, 4, 1], [1, 0, 0, 0], [1, 0, 1, 0], [1, 0, 2, 1], [1, 0, 3, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_116_55_6 : ColCertDiv where
  rK := ⟨116, by decide⟩
  rH := ⟨55, by decide⟩
  m := 5
  T1 := T116_55
  T2 := Q2.T116_55_2
  h1 := (0,1,1,4,3)
  h2 := (0,1,1,4,1)
  D1 := [[1, 1, 4, 2], [1, 1, 0, 1], [1, 1, 1, 1], [1, 1, 2, 2], [1, 1, 3, 4]]
  D2 := [[1, 1, 4, 0], [1, 1, 0, 4], [1, 1, 1, 4], [1, 1, 2, 0], [1, 1, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_116_55_7 : ColCertDiv where
  rK := ⟨116, by decide⟩
  rH := ⟨55, by decide⟩
  m := 5
  T1 := T116_55
  T2 := Q2.T116_55_2
  h1 := (0,1,2,4,3)
  h2 := (0,1,2,4,1)
  D1 := [[1, 2, 4, 1], [1, 2, 0, 0], [1, 2, 1, 0], [1, 2, 2, 1], [1, 2, 3, 3]]
  D2 := [[1, 2, 4, 4], [1, 2, 0, 3], [1, 2, 1, 3], [1, 2, 2, 4], [1, 2, 3, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_116_55_8 : ColCertDiv where
  rK := ⟨116, by decide⟩
  rH := ⟨55, by decide⟩
  m := 5
  T1 := T116_55
  T2 := Q2.T116_55_2
  h1 := (0,1,3,4,3)
  h2 := (0,1,3,4,1)
  D1 := [[1, 3, 4, 0], [1, 3, 0, 4], [1, 3, 1, 4], [1, 3, 2, 0], [1, 3, 3, 2]]
  D2 := [[1, 3, 4, 3], [1, 3, 0, 2], [1, 3, 1, 2], [1, 3, 2, 3], [1, 3, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_116_55_9 : ColCertDiv where
  rK := ⟨116, by decide⟩
  rH := ⟨55, by decide⟩
  m := 5
  T1 := T116_55
  T2 := Q2.T116_55_2
  h1 := (0,1,4,4,3)
  h2 := (0,1,4,4,1)
  D1 := [[1, 4, 4, 4], [1, 4, 0, 3], [1, 4, 1, 3], [1, 4, 2, 4], [1, 4, 3, 1]]
  D2 := [[1, 4, 4, 2], [1, 4, 0, 1], [1, 4, 1, 1], [1, 4, 2, 2], [1, 4, 3, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_116_55_10 : ColCertDiv where
  rK := ⟨116, by decide⟩
  rH := ⟨55, by decide⟩
  m := 5
  T1 := T116_55
  T2 := Q2.T116_55_2
  h1 := (0,2,0,3,1)
  h2 := (0,2,0,3,2)
  D1 := [[2, 0, 3, 1], [2, 0, 0, 4], [2, 0, 2, 4], [2, 0, 4, 1], [2, 0, 1, 0]]
  D2 := [[2, 0, 3, 2], [2, 0, 0, 0], [2, 0, 2, 0], [2, 0, 4, 2], [2, 0, 1, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_116_55_11 : ColCertDiv where
  rK := ⟨116, by decide⟩
  rH := ⟨55, by decide⟩
  m := 5
  T1 := T116_55
  T2 := Q2.T116_55_2
  h1 := (0,2,1,3,1)
  h2 := (0,2,1,3,2)
  D1 := [[2, 1, 3, 4], [2, 1, 0, 2], [2, 1, 2, 2], [2, 1, 4, 4], [2, 1, 1, 3]]
  D2 := [[2, 1, 3, 0], [2, 1, 0, 3], [2, 1, 2, 3], [2, 1, 4, 0], [2, 1, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_116_55_12 : ColCertDiv where
  rK := ⟨116, by decide⟩
  rH := ⟨55, by decide⟩
  m := 5
  T1 := T116_55
  T2 := Q2.T116_55_2
  h1 := (0,2,2,3,1)
  h2 := (0,2,2,3,2)
  D1 := [[2, 2, 3, 2], [2, 2, 0, 0], [2, 2, 2, 0], [2, 2, 4, 2], [2, 2, 1, 1]]
  D2 := [[2, 2, 3, 3], [2, 2, 0, 1], [2, 2, 2, 1], [2, 2, 4, 3], [2, 2, 1, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_116_55_13 : ColCertDiv where
  rK := ⟨116, by decide⟩
  rH := ⟨55, by decide⟩
  m := 5
  T1 := T116_55
  T2 := Q2.T116_55_2
  h1 := (0,2,3,3,1)
  h2 := (0,2,3,3,2)
  D1 := [[2, 3, 3, 0], [2, 3, 0, 3], [2, 3, 2, 3], [2, 3, 4, 0], [2, 3, 1, 4]]
  D2 := [[2, 3, 3, 1], [2, 3, 0, 4], [2, 3, 2, 4], [2, 3, 4, 1], [2, 3, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_116_55_14 : ColCertDiv where
  rK := ⟨116, by decide⟩
  rH := ⟨55, by decide⟩
  m := 5
  T1 := T116_55
  T2 := Q2.T116_55_2
  h1 := (0,2,4,3,1)
  h2 := (0,2,4,3,2)
  D1 := [[2, 4, 3, 3], [2, 4, 0, 1], [2, 4, 2, 1], [2, 4, 4, 3], [2, 4, 1, 2]]
  D2 := [[2, 4, 3, 4], [2, 4, 0, 2], [2, 4, 2, 2], [2, 4, 4, 4], [2, 4, 1, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_116_55_15 : ColCertDiv where
  rK := ⟨116, by decide⟩
  rH := ⟨55, by decide⟩
  m := 5
  T1 := T116_55
  T2 := Q2.T116_55_2
  h1 := (0,3,0,2,4)
  h2 := (0,3,0,2,3)
  D1 := [[3, 0, 2, 4], [3, 0, 0, 1], [3, 0, 3, 1], [3, 0, 1, 4], [3, 0, 4, 0]]
  D2 := [[3, 0, 2, 3], [3, 0, 0, 0], [3, 0, 3, 0], [3, 0, 1, 3], [3, 0, 4, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_116_55_16 : ColCertDiv where
  rK := ⟨116, by decide⟩
  rH := ⟨55, by decide⟩
  m := 5
  T1 := T116_55
  T2 := Q2.T116_55_2
  h1 := (0,3,1,2,4)
  h2 := (0,3,1,2,3)
  D1 := [[3, 1, 2, 1], [3, 1, 0, 3], [3, 1, 3, 3], [3, 1, 1, 1], [3, 1, 4, 2]]
  D2 := [[3, 1, 2, 0], [3, 1, 0, 2], [3, 1, 3, 2], [3, 1, 1, 0], [3, 1, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_116_55_17 : ColCertDiv where
  rK := ⟨116, by decide⟩
  rH := ⟨55, by decide⟩
  m := 5
  T1 := T116_55
  T2 := Q2.T116_55_2
  h1 := (0,3,2,2,4)
  h2 := (0,3,2,2,3)
  D1 := [[3, 2, 2, 3], [3, 2, 0, 0], [3, 2, 3, 0], [3, 2, 1, 3], [3, 2, 4, 4]]
  D2 := [[3, 2, 2, 2], [3, 2, 0, 4], [3, 2, 3, 4], [3, 2, 1, 2], [3, 2, 4, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_116_55_18 : ColCertDiv where
  rK := ⟨116, by decide⟩
  rH := ⟨55, by decide⟩
  m := 5
  T1 := T116_55
  T2 := Q2.T116_55_2
  h1 := (0,3,3,2,4)
  h2 := (0,3,3,2,3)
  D1 := [[3, 3, 2, 0], [3, 3, 0, 2], [3, 3, 3, 2], [3, 3, 1, 0], [3, 3, 4, 1]]
  D2 := [[3, 3, 2, 4], [3, 3, 0, 1], [3, 3, 3, 1], [3, 3, 1, 4], [3, 3, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_116_55_19 : ColCertDiv where
  rK := ⟨116, by decide⟩
  rH := ⟨55, by decide⟩
  m := 5
  T1 := T116_55
  T2 := Q2.T116_55_2
  h1 := (0,3,4,2,4)
  h2 := (0,3,4,2,3)
  D1 := [[3, 4, 2, 2], [3, 4, 0, 4], [3, 4, 3, 4], [3, 4, 1, 2], [3, 4, 4, 3]]
  D2 := [[3, 4, 2, 1], [3, 4, 0, 3], [3, 4, 3, 3], [3, 4, 1, 1], [3, 4, 4, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_116_55_20 : ColCertDiv where
  rK := ⟨116, by decide⟩
  rH := ⟨55, by decide⟩
  m := 5
  T1 := T116_55
  T2 := Q2.T116_55_2
  h1 := (0,4,0,1,2)
  h2 := (0,4,0,1,4)
  D1 := [[4, 0, 1, 2], [4, 0, 0, 3], [4, 0, 4, 3], [4, 0, 3, 2], [4, 0, 2, 0]]
  D2 := [[4, 0, 1, 4], [4, 0, 0, 0], [4, 0, 4, 0], [4, 0, 3, 4], [4, 0, 2, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_116_55_21 : ColCertDiv where
  rK := ⟨116, by decide⟩
  rH := ⟨55, by decide⟩
  m := 5
  T1 := T116_55
  T2 := Q2.T116_55_2
  h1 := (0,4,1,1,2)
  h2 := (0,4,1,1,4)
  D1 := [[4, 1, 1, 3], [4, 1, 0, 4], [4, 1, 4, 4], [4, 1, 3, 3], [4, 1, 2, 1]]
  D2 := [[4, 1, 1, 0], [4, 1, 0, 1], [4, 1, 4, 1], [4, 1, 3, 0], [4, 1, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_116_55_22 : ColCertDiv where
  rK := ⟨116, by decide⟩
  rH := ⟨55, by decide⟩
  m := 5
  T1 := T116_55
  T2 := Q2.T116_55_2
  h1 := (0,4,2,1,2)
  h2 := (0,4,2,1,4)
  D1 := [[4, 2, 1, 4], [4, 2, 0, 0], [4, 2, 4, 0], [4, 2, 3, 4], [4, 2, 2, 2]]
  D2 := [[4, 2, 1, 1], [4, 2, 0, 2], [4, 2, 4, 2], [4, 2, 3, 1], [4, 2, 2, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_116_55_23 : ColCertDiv where
  rK := ⟨116, by decide⟩
  rH := ⟨55, by decide⟩
  m := 5
  T1 := T116_55
  T2 := Q2.T116_55_2
  h1 := (0,4,3,1,2)
  h2 := (0,4,3,1,4)
  D1 := [[4, 3, 1, 0], [4, 3, 0, 1], [4, 3, 4, 1], [4, 3, 3, 0], [4, 3, 2, 3]]
  D2 := [[4, 3, 1, 2], [4, 3, 0, 3], [4, 3, 4, 3], [4, 3, 3, 2], [4, 3, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_116_55_24 : ColCertDiv where
  rK := ⟨116, by decide⟩
  rH := ⟨55, by decide⟩
  m := 5
  T1 := T116_55
  T2 := Q2.T116_55_2
  h1 := (0,4,4,1,2)
  h2 := (0,4,4,1,4)
  D1 := [[4, 4, 1, 1], [4, 4, 0, 2], [4, 4, 4, 2], [4, 4, 3, 1], [4, 4, 2, 4]]
  D2 := [[4, 4, 1, 3], [4, 4, 0, 4], [4, 4, 4, 4], [4, 4, 3, 3], [4, 4, 2, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_116_56_5 : ColCertDiv where
  rK := ⟨116, by decide⟩
  rH := ⟨56, by decide⟩
  m := 5
  T1 := T116_56
  T2 := Q2.T116_56_2
  h1 := (0,1,0,4,2)
  h2 := (0,1,0,4,0)
  D1 := [[1, 0, 4, 2], [1, 0, 0, 1], [1, 0, 1, 1], [1, 0, 2, 2], [1, 0, 3, 4]]
  D2 := [[1, 0, 4, 0], [1, 0, 0, 4], [1, 0, 1, 4], [1, 0, 2, 0], [1, 0, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_116_56_6 : ColCertDiv where
  rK := ⟨116, by decide⟩
  rH := ⟨56, by decide⟩
  m := 5
  T1 := T116_56
  T2 := Q2.T116_56_2
  h1 := (0,1,1,3,2)
  h2 := (0,1,1,3,0)
  D1 := [[1, 1, 3, 1], [1, 1, 4, 4], [1, 1, 0, 3], [1, 1, 1, 3], [1, 1, 2, 4]]
  D2 := [[1, 1, 3, 4], [1, 1, 4, 2], [1, 1, 0, 1], [1, 1, 1, 1], [1, 1, 2, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_116_56_7 : ColCertDiv where
  rK := ⟨116, by decide⟩
  rH := ⟨56, by decide⟩
  m := 5
  T1 := T116_56
  T2 := Q2.T116_56_2
  h1 := (0,1,2,2,2)
  h2 := (0,1,2,2,0)
  D1 := [[1, 2, 2, 0], [1, 2, 3, 2], [1, 2, 4, 0], [1, 2, 0, 4], [1, 2, 1, 4]]
  D2 := [[1, 2, 2, 3], [1, 2, 3, 0], [1, 2, 4, 3], [1, 2, 0, 2], [1, 2, 1, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_116_56_8 : ColCertDiv where
  rK := ⟨116, by decide⟩
  rH := ⟨56, by decide⟩
  m := 5
  T1 := T116_56
  T2 := Q2.T116_56_2
  h1 := (0,1,3,1,2)
  h2 := (0,1,3,1,0)
  D1 := [[1, 3, 1, 4], [1, 3, 2, 0], [1, 3, 3, 2], [1, 3, 4, 0], [1, 3, 0, 4]]
  D2 := [[1, 3, 1, 2], [1, 3, 2, 3], [1, 3, 3, 0], [1, 3, 4, 3], [1, 3, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_116_56_9 : ColCertDiv where
  rK := ⟨116, by decide⟩
  rH := ⟨56, by decide⟩
  m := 5
  T1 := T116_56
  T2 := Q2.T116_56_2
  h1 := (0,1,4,0,2)
  h2 := (0,1,4,0,0)
  D1 := [[1, 4, 0, 3], [1, 4, 1, 3], [1, 4, 2, 4], [1, 4, 3, 1], [1, 4, 4, 4]]
  D2 := [[1, 4, 0, 1], [1, 4, 1, 1], [1, 4, 2, 2], [1, 4, 3, 4], [1, 4, 4, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_116_56_10 : ColCertDiv where
  rK := ⟨116, by decide⟩
  rH := ⟨56, by decide⟩
  m := 5
  T1 := T116_56
  T2 := Q2.T116_56_2
  h1 := (0,2,0,3,4)
  h2 := (0,2,0,3,0)
  D1 := [[2, 0, 3, 4], [2, 0, 0, 2], [2, 0, 2, 2], [2, 0, 4, 4], [2, 0, 1, 3]]
  D2 := [[2, 0, 3, 0], [2, 0, 0, 3], [2, 0, 2, 3], [2, 0, 4, 0], [2, 0, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_116_56_11 : ColCertDiv where
  rK := ⟨116, by decide⟩
  rH := ⟨56, by decide⟩
  m := 5
  T1 := T116_56
  T2 := Q2.T116_56_2
  h1 := (0,2,1,2,4)
  h2 := (0,2,1,2,0)
  D1 := [[2, 1, 2, 2], [2, 1, 4, 4], [2, 1, 1, 3], [2, 1, 3, 4], [2, 1, 0, 2]]
  D2 := [[2, 1, 2, 3], [2, 1, 4, 0], [2, 1, 1, 4], [2, 1, 3, 0], [2, 1, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_116_56_12 : ColCertDiv where
  rK := ⟨116, by decide⟩
  rH := ⟨56, by decide⟩
  m := 5
  T1 := T116_56
  T2 := Q2.T116_56_2
  h1 := (0,2,2,1,4)
  h2 := (0,2,2,1,0)
  D1 := [[2, 2, 1, 0], [2, 2, 3, 1], [2, 2, 0, 4], [2, 2, 2, 4], [2, 2, 4, 1]]
  D2 := [[2, 2, 1, 1], [2, 2, 3, 2], [2, 2, 0, 0], [2, 2, 2, 0], [2, 2, 4, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_116_56_13 : ColCertDiv where
  rK := ⟨116, by decide⟩
  rH := ⟨56, by decide⟩
  m := 5
  T1 := T116_56
  T2 := Q2.T116_56_2
  h1 := (0,2,3,0,4)
  h2 := (0,2,3,0,0)
  D1 := [[2, 3, 0, 3], [2, 3, 2, 3], [2, 3, 4, 0], [2, 3, 1, 4], [2, 3, 3, 0]]
  D2 := [[2, 3, 0, 4], [2, 3, 2, 4], [2, 3, 4, 1], [2, 3, 1, 0], [2, 3, 3, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_116_56_14 : ColCertDiv where
  rK := ⟨116, by decide⟩
  rH := ⟨56, by decide⟩
  m := 5
  T1 := T116_56
  T2 := Q2.T116_56_2
  h1 := (0,2,4,4,4)
  h2 := (0,2,4,4,0)
  D1 := [[2, 4, 4, 1], [2, 4, 1, 0], [2, 4, 3, 1], [2, 4, 0, 4], [2, 4, 2, 4]]
  D2 := [[2, 4, 4, 2], [2, 4, 1, 1], [2, 4, 3, 2], [2, 4, 0, 0], [2, 4, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_116_56_15 : ColCertDiv where
  rK := ⟨116, by decide⟩
  rH := ⟨56, by decide⟩
  m := 5
  T1 := T116_56
  T2 := Q2.T116_56_2
  h1 := (0,3,0,2,1)
  h2 := (0,3,0,2,0)
  D1 := [[3, 0, 2, 1], [3, 0, 0, 3], [3, 0, 3, 3], [3, 0, 1, 1], [3, 0, 4, 2]]
  D2 := [[3, 0, 2, 0], [3, 0, 0, 2], [3, 0, 3, 2], [3, 0, 1, 0], [3, 0, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_116_56_16 : ColCertDiv where
  rK := ⟨116, by decide⟩
  rH := ⟨56, by decide⟩
  m := 5
  T1 := T116_56
  T2 := Q2.T116_56_2
  h1 := (0,3,1,1,1)
  h2 := (0,3,1,1,0)
  D1 := [[3, 1, 1, 3], [3, 1, 4, 4], [3, 1, 2, 3], [3, 1, 0, 0], [3, 1, 3, 0]]
  D2 := [[3, 1, 1, 2], [3, 1, 4, 3], [3, 1, 2, 2], [3, 1, 0, 4], [3, 1, 3, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_116_56_17 : ColCertDiv where
  rK := ⟨116, by decide⟩
  rH := ⟨56, by decide⟩
  m := 5
  T1 := T116_56
  T2 := Q2.T116_56_2
  h1 := (0,3,2,0,1)
  h2 := (0,3,2,0,0)
  D1 := [[3, 2, 0, 0], [3, 2, 3, 0], [3, 2, 1, 3], [3, 2, 4, 4], [3, 2, 2, 3]]
  D2 := [[3, 2, 0, 4], [3, 2, 3, 4], [3, 2, 1, 2], [3, 2, 4, 3], [3, 2, 2, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_116_56_18 : ColCertDiv where
  rK := ⟨116, by decide⟩
  rH := ⟨56, by decide⟩
  m := 5
  T1 := T116_56
  T2 := Q2.T116_56_2
  h1 := (0,3,3,4,1)
  h2 := (0,3,3,4,0)
  D1 := [[3, 3, 4, 2], [3, 3, 2, 1], [3, 3, 0, 3], [3, 3, 3, 3], [3, 3, 1, 1]]
  D2 := [[3, 3, 4, 1], [3, 3, 2, 0], [3, 3, 0, 2], [3, 3, 3, 2], [3, 3, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_116_56_19 : ColCertDiv where
  rK := ⟨116, by decide⟩
  rH := ⟨56, by decide⟩
  m := 5
  T1 := T116_56
  T2 := Q2.T116_56_2
  h1 := (0,3,4,3,1)
  h2 := (0,3,4,3,0)
  D1 := [[3, 4, 3, 4], [3, 4, 1, 2], [3, 4, 4, 3], [3, 4, 2, 2], [3, 4, 0, 4]]
  D2 := [[3, 4, 3, 3], [3, 4, 1, 1], [3, 4, 4, 2], [3, 4, 2, 1], [3, 4, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_116_56_20 : ColCertDiv where
  rK := ⟨116, by decide⟩
  rH := ⟨56, by decide⟩
  m := 5
  T1 := T116_56
  T2 := Q2.T116_56_2
  h1 := (0,4,0,1,3)
  h2 := (0,4,0,1,0)
  D1 := [[4, 0, 1, 3], [4, 0, 0, 4], [4, 0, 4, 4], [4, 0, 3, 3], [4, 0, 2, 1]]
  D2 := [[4, 0, 1, 0], [4, 0, 0, 1], [4, 0, 4, 1], [4, 0, 3, 0], [4, 0, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_116_56_21 : ColCertDiv where
  rK := ⟨116, by decide⟩
  rH := ⟨56, by decide⟩
  m := 5
  T1 := T116_56
  T2 := Q2.T116_56_2
  h1 := (0,4,1,0,3)
  h2 := (0,4,1,0,0)
  D1 := [[4, 1, 0, 4], [4, 1, 4, 4], [4, 1, 3, 3], [4, 1, 2, 1], [4, 1, 1, 3]]
  D2 := [[4, 1, 0, 1], [4, 1, 4, 1], [4, 1, 3, 0], [4, 1, 2, 3], [4, 1, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_116_56_22 : ColCertDiv where
  rK := ⟨116, by decide⟩
  rH := ⟨56, by decide⟩
  m := 5
  T1 := T116_56
  T2 := Q2.T116_56_2
  h1 := (0,4,2,4,3)
  h2 := (0,4,2,4,0)
  D1 := [[4, 2, 4, 0], [4, 2, 3, 4], [4, 2, 2, 2], [4, 2, 1, 4], [4, 2, 0, 0]]
  D2 := [[4, 2, 4, 2], [4, 2, 3, 1], [4, 2, 2, 4], [4, 2, 1, 1], [4, 2, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_116_56_23 : ColCertDiv where
  rK := ⟨116, by decide⟩
  rH := ⟨56, by decide⟩
  m := 5
  T1 := T116_56
  T2 := Q2.T116_56_2
  h1 := (0,4,3,3,3)
  h2 := (0,4,3,3,0)
  D1 := [[4, 3, 3, 1], [4, 3, 2, 4], [4, 3, 1, 1], [4, 3, 0, 2], [4, 3, 4, 2]]
  D2 := [[4, 3, 3, 3], [4, 3, 2, 1], [4, 3, 1, 3], [4, 3, 0, 4], [4, 3, 4, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_116_56_24 : ColCertDiv where
  rK := ⟨116, by decide⟩
  rH := ⟨56, by decide⟩
  m := 5
  T1 := T116_56
  T2 := Q2.T116_56_2
  h1 := (0,4,4,2,3)
  h2 := (0,4,4,2,0)
  D1 := [[4, 4, 2, 2], [4, 4, 1, 4], [4, 4, 0, 0], [4, 4, 4, 0], [4, 4, 3, 4]]
  D2 := [[4, 4, 2, 4], [4, 4, 1, 1], [4, 4, 0, 2], [4, 4, 4, 2], [4, 4, 3, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_116_57_5 : ColCertDiv where
  rK := ⟨116, by decide⟩
  rH := ⟨57, by decide⟩
  m := 5
  T1 := T116_57
  T2 := Q2.T116_57_2
  h1 := (0,1,0,4,4)
  h2 := (0,1,0,4,0)
  D1 := [[1, 0, 4, 4], [1, 0, 0, 3], [1, 0, 1, 3], [1, 0, 2, 4], [1, 0, 3, 1]]
  D2 := [[1, 0, 4, 0], [1, 0, 0, 4], [1, 0, 1, 4], [1, 0, 2, 0], [1, 0, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_116_57_6 : ColCertDiv where
  rK := ⟨116, by decide⟩
  rH := ⟨57, by decide⟩
  m := 5
  T1 := T116_57
  T2 := Q2.T116_57_2
  h1 := (0,1,1,2,4)
  h2 := (0,1,1,2,0)
  D1 := [[1, 1, 2, 3], [1, 1, 3, 0], [1, 1, 4, 3], [1, 1, 0, 2], [1, 1, 1, 2]]
  D2 := [[1, 1, 2, 4], [1, 1, 3, 1], [1, 1, 4, 4], [1, 1, 0, 3], [1, 1, 1, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_116_57_7 : ColCertDiv where
  rK := ⟨116, by decide⟩
  rH := ⟨57, by decide⟩
  m := 5
  T1 := T116_57
  T2 := Q2.T116_57_2
  h1 := (0,1,2,0,4)
  h2 := (0,1,2,0,0)
  D1 := [[1, 2, 0, 2], [1, 2, 1, 2], [1, 2, 2, 3], [1, 2, 3, 0], [1, 2, 4, 3]]
  D2 := [[1, 2, 0, 3], [1, 2, 1, 3], [1, 2, 2, 4], [1, 2, 3, 1], [1, 2, 4, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_116_57_8 : ColCertDiv where
  rK := ⟨116, by decide⟩
  rH := ⟨57, by decide⟩
  m := 5
  T1 := T116_57
  T2 := Q2.T116_57_2
  h1 := (0,1,3,3,4)
  h2 := (0,1,3,3,0)
  D1 := [[1, 3, 3, 1], [1, 3, 4, 4], [1, 3, 0, 3], [1, 3, 1, 3], [1, 3, 2, 4]]
  D2 := [[1, 3, 3, 2], [1, 3, 4, 0], [1, 3, 0, 4], [1, 3, 1, 4], [1, 3, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_116_57_9 : ColCertDiv where
  rK := ⟨116, by decide⟩
  rH := ⟨57, by decide⟩
  m := 5
  T1 := T116_57
  T2 := Q2.T116_57_2
  h1 := (0,1,4,1,4)
  h2 := (0,1,4,1,0)
  D1 := [[1, 4, 1, 0], [1, 4, 2, 1], [1, 4, 3, 3], [1, 4, 4, 1], [1, 4, 0, 0]]
  D2 := [[1, 4, 1, 1], [1, 4, 2, 2], [1, 4, 3, 4], [1, 4, 4, 2], [1, 4, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_116_57_10 : ColCertDiv where
  rK := ⟨116, by decide⟩
  rH := ⟨57, by decide⟩
  m := 5
  T1 := T116_57
  T2 := Q2.T116_57_2
  h1 := (0,2,0,3,3)
  h2 := (0,2,0,3,0)
  D1 := [[2, 0, 3, 3], [2, 0, 0, 1], [2, 0, 2, 1], [2, 0, 4, 3], [2, 0, 1, 2]]
  D2 := [[2, 0, 3, 0], [2, 0, 0, 3], [2, 0, 2, 3], [2, 0, 4, 0], [2, 0, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_116_57_11 : ColCertDiv where
  rK := ⟨116, by decide⟩
  rH := ⟨57, by decide⟩
  m := 5
  T1 := T116_57
  T2 := Q2.T116_57_2
  h1 := (0,2,1,1,3)
  h2 := (0,2,1,1,0)
  D1 := [[2, 1, 1, 1], [2, 1, 3, 2], [2, 1, 0, 0], [2, 1, 2, 0], [2, 1, 4, 2]]
  D2 := [[2, 1, 1, 3], [2, 1, 3, 4], [2, 1, 0, 2], [2, 1, 2, 2], [2, 1, 4, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_116_57_12 : ColCertDiv where
  rK := ⟨116, by decide⟩
  rH := ⟨57, by decide⟩
  m := 5
  T1 := T116_57
  T2 := Q2.T116_57_2
  h1 := (0,2,2,4,3)
  h2 := (0,2,2,4,0)
  D1 := [[2, 2, 4, 4], [2, 2, 1, 3], [2, 2, 3, 4], [2, 2, 0, 2], [2, 2, 2, 2]]
  D2 := [[2, 2, 4, 1], [2, 2, 1, 0], [2, 2, 3, 1], [2, 2, 0, 4], [2, 2, 2, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_116_57_13 : ColCertDiv where
  rK := ⟨116, by decide⟩
  rH := ⟨57, by decide⟩
  m := 5
  T1 := T116_57
  T2 := Q2.T116_57_2
  h1 := (0,2,3,2,3)
  h2 := (0,2,3,2,0)
  D1 := [[2, 3, 2, 2], [2, 3, 4, 4], [2, 3, 1, 3], [2, 3, 3, 4], [2, 3, 0, 2]]
  D2 := [[2, 3, 2, 4], [2, 3, 4, 1], [2, 3, 1, 0], [2, 3, 3, 1], [2, 3, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_116_57_14 : ColCertDiv where
  rK := ⟨116, by decide⟩
  rH := ⟨57, by decide⟩
  m := 5
  T1 := T116_57
  T2 := Q2.T116_57_2
  h1 := (0,2,4,0,3)
  h2 := (0,2,4,0,0)
  D1 := [[2, 4, 0, 0], [2, 4, 2, 0], [2, 4, 4, 2], [2, 4, 1, 1], [2, 4, 3, 2]]
  D2 := [[2, 4, 0, 2], [2, 4, 2, 2], [2, 4, 4, 4], [2, 4, 1, 3], [2, 4, 3, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_116_57_15 : ColCertDiv where
  rK := ⟨116, by decide⟩
  rH := ⟨57, by decide⟩
  m := 5
  T1 := T116_57
  T2 := Q2.T116_57_2
  h1 := (0,3,0,2,2)
  h2 := (0,3,0,2,0)
  D1 := [[3, 0, 2, 2], [3, 0, 0, 4], [3, 0, 3, 4], [3, 0, 1, 2], [3, 0, 4, 3]]
  D2 := [[3, 0, 2, 0], [3, 0, 0, 2], [3, 0, 3, 2], [3, 0, 1, 0], [3, 0, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_116_57_16 : ColCertDiv where
  rK := ⟨116, by decide⟩
  rH := ⟨57, by decide⟩
  m := 5
  T1 := T116_57
  T2 := Q2.T116_57_2
  h1 := (0,3,1,0,2)
  h2 := (0,3,1,0,0)
  D1 := [[3, 1, 0, 4], [3, 1, 3, 4], [3, 1, 1, 2], [3, 1, 4, 3], [3, 1, 2, 2]]
  D2 := [[3, 1, 0, 2], [3, 1, 3, 2], [3, 1, 1, 0], [3, 1, 4, 1], [3, 1, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_116_57_17 : ColCertDiv where
  rK := ⟨116, by decide⟩
  rH := ⟨57, by decide⟩
  m := 5
  T1 := T116_57
  T2 := Q2.T116_57_2
  h1 := (0,3,2,3,2)
  h2 := (0,3,2,3,0)
  D1 := [[3, 2, 3, 1], [3, 2, 1, 4], [3, 2, 4, 0], [3, 2, 2, 4], [3, 2, 0, 1]]
  D2 := [[3, 2, 3, 4], [3, 2, 1, 2], [3, 2, 4, 3], [3, 2, 2, 2], [3, 2, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_116_57_18 : ColCertDiv where
  rK := ⟨116, by decide⟩
  rH := ⟨57, by decide⟩
  m := 5
  T1 := T116_57
  T2 := Q2.T116_57_2
  h1 := (0,3,3,1,2)
  h2 := (0,3,3,1,0)
  D1 := [[3, 3, 1, 3], [3, 3, 4, 4], [3, 3, 2, 3], [3, 3, 0, 0], [3, 3, 3, 0]]
  D2 := [[3, 3, 1, 1], [3, 3, 4, 2], [3, 3, 2, 1], [3, 3, 0, 3], [3, 3, 3, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_116_57_19 : ColCertDiv where
  rK := ⟨116, by decide⟩
  rH := ⟨57, by decide⟩
  m := 5
  T1 := T116_57
  T2 := Q2.T116_57_2
  h1 := (0,3,4,4,2)
  h2 := (0,3,4,4,0)
  D1 := [[3, 4, 4, 0], [3, 4, 2, 4], [3, 4, 0, 1], [3, 4, 3, 1], [3, 4, 1, 4]]
  D2 := [[3, 4, 4, 3], [3, 4, 2, 2], [3, 4, 0, 4], [3, 4, 3, 4], [3, 4, 1, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_116_57_20 : ColCertDiv where
  rK := ⟨116, by decide⟩
  rH := ⟨57, by decide⟩
  m := 5
  T1 := T116_57
  T2 := Q2.T116_57_2
  h1 := (0,4,0,1,1)
  h2 := (0,4,0,1,0)
  D1 := [[4, 0, 1, 1], [4, 0, 0, 2], [4, 0, 4, 2], [4, 0, 3, 1], [4, 0, 2, 4]]
  D2 := [[4, 0, 1, 0], [4, 0, 0, 1], [4, 0, 4, 1], [4, 0, 3, 0], [4, 0, 2, 3]]
  bind1 := by decide
  bind2 := by decide

end LeanDring.P5Presentation
