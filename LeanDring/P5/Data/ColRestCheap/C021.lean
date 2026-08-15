/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.Twin1.ColCert
import LeanDring.P5.Data.EntryK.C025

/-!
# Species-table cell data, stage 2 — twin-coincident columns (cheap tier)

Per-column certified exponent-vector data (`ColCert`/`ColCertDiv`) with kernel
`decide` bindings. Emitted; the embedded lists are what the kernel certifies.
rest tier, chunk 20: 60 columns.
-/

-- machine-emitted data: silence style linters (generated long lines, file-level options)
set_option linter.style.longLine false

namespace LeanDring.P5Presentation

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

def colCert_116_59_14 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨59, by decide⟩
  m := 5
  T1 := T116_59
  T2 := Q2.T116_59_2
  h1 := (0,2,4,2,0)
  h2 := (0,2,4,2,0)
  D := [[2, 4, 2, 2], [2, 4, 4, 4], [2, 4, 1, 3], [2, 4, 3, 4], [2, 4, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_59_15 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨59, by decide⟩
  m := 5
  T1 := T116_59
  T2 := Q2.T116_59_2
  h1 := (0,3,0,2,0)
  h2 := (0,3,0,2,0)
  D := [[3, 0, 2, 0], [3, 0, 0, 2], [3, 0, 3, 2], [3, 0, 1, 0], [3, 0, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_59_16 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨59, by decide⟩
  m := 5
  T1 := T116_59
  T2 := Q2.T116_59_2
  h1 := (0,3,1,3,0)
  h2 := (0,3,1,3,0)
  D := [[3, 1, 3, 2], [3, 1, 1, 0], [3, 1, 4, 1], [3, 1, 2, 0], [3, 1, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_59_17 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨59, by decide⟩
  m := 5
  T1 := T116_59
  T2 := Q2.T116_59_2
  h1 := (0,3,2,4,0)
  h2 := (0,3,2,4,0)
  D := [[3, 2, 4, 4], [3, 2, 2, 3], [3, 2, 0, 0], [3, 2, 3, 0], [3, 2, 1, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_59_18 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨59, by decide⟩
  m := 5
  T1 := T116_59
  T2 := Q2.T116_59_2
  h1 := (0,3,3,0,0)
  h2 := (0,3,3,0,0)
  D := [[3, 3, 0, 1], [3, 3, 3, 1], [3, 3, 1, 4], [3, 3, 4, 0], [3, 3, 2, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_59_19 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨59, by decide⟩
  m := 5
  T1 := T116_59
  T2 := Q2.T116_59_2
  h1 := (0,3,4,1,0)
  h2 := (0,3,4,1,0)
  D := [[3, 4, 1, 3], [3, 4, 4, 4], [3, 4, 2, 3], [3, 4, 0, 0], [3, 4, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_59_20 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨59, by decide⟩
  m := 5
  T1 := T116_59
  T2 := Q2.T116_59_2
  h1 := (0,4,0,1,0)
  h2 := (0,4,0,1,0)
  D := [[4, 0, 1, 0], [4, 0, 0, 1], [4, 0, 4, 1], [4, 0, 3, 0], [4, 0, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_59_21 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨59, by decide⟩
  m := 5
  T1 := T116_59
  T2 := Q2.T116_59_2
  h1 := (0,4,1,2,0)
  h2 := (0,4,1,2,0)
  D := [[4, 1, 2, 1], [4, 1, 1, 3], [4, 1, 0, 4], [4, 1, 4, 4], [4, 1, 3, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_59_22 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨59, by decide⟩
  m := 5
  T1 := T116_59
  T2 := Q2.T116_59_2
  h1 := (0,4,2,3,0)
  h2 := (0,4,2,3,0)
  D := [[4, 2, 3, 2], [4, 2, 2, 0], [4, 2, 1, 2], [4, 2, 0, 3], [4, 2, 4, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_59_23 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨59, by decide⟩
  m := 5
  T1 := T116_59
  T2 := Q2.T116_59_2
  h1 := (0,4,3,4,0)
  h2 := (0,4,3,4,0)
  D := [[4, 3, 4, 3], [4, 3, 3, 2], [4, 3, 2, 0], [4, 3, 1, 2], [4, 3, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_59_24 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨59, by decide⟩
  m := 5
  T1 := T116_59
  T2 := Q2.T116_59_2
  h1 := (0,4,4,0,0)
  h2 := (0,4,4,0,0)
  D := [[4, 4, 0, 4], [4, 4, 4, 4], [4, 4, 3, 3], [4, 4, 2, 1], [4, 4, 1, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_80_0 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨80, by decide⟩
  m := 5
  T1 := T116_80
  T2 := Q2.T116_80_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_80_1 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨80, by decide⟩
  m := 5
  T1 := T116_80
  T2 := Q2.T116_80_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_80_2 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨80, by decide⟩
  m := 5
  T1 := T116_80
  T2 := Q2.T116_80_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_80_3 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨80, by decide⟩
  m := 5
  T1 := T116_80
  T2 := Q2.T116_80_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_80_4 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨80, by decide⟩
  m := 5
  T1 := T116_80
  T2 := Q2.T116_80_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_80_5 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨80, by decide⟩
  m := 5
  T1 := T116_80
  T2 := Q2.T116_80_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 1, 0], [0, 0, 1, 1], [0, 0, 1, 2], [0, 0, 1, 3], [0, 0, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_80_10 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨80, by decide⟩
  m := 5
  T1 := T116_80
  T2 := Q2.T116_80_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 2, 0], [0, 0, 2, 2], [0, 0, 2, 4], [0, 0, 2, 1], [0, 0, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_80_15 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨80, by decide⟩
  m := 5
  T1 := T116_80
  T2 := Q2.T116_80_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 3, 0], [0, 0, 3, 3], [0, 0, 3, 1], [0, 0, 3, 4], [0, 0, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_80_20 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨80, by decide⟩
  m := 5
  T1 := T116_80
  T2 := Q2.T116_80_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 4, 0], [0, 0, 4, 4], [0, 0, 4, 3], [0, 0, 4, 2], [0, 0, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_80_25 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨80, by decide⟩
  m := 5
  T1 := T116_80
  T2 := Q2.T116_80_2
  h1 := (0,0,1,0,0)
  h2 := (0,0,1,0,0)
  D := [[0, 1, 0, 0], [0, 1, 0, 0], [0, 1, 0, 0], [0, 1, 0, 0], [0, 1, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_80_30 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨80, by decide⟩
  m := 5
  T1 := T116_80
  T2 := Q2.T116_80_2
  h1 := (0,0,1,1,0)
  h2 := (0,0,1,1,0)
  D := [[0, 1, 1, 0], [0, 1, 1, 1], [0, 1, 1, 2], [0, 1, 1, 3], [0, 1, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_80_35 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨80, by decide⟩
  m := 5
  T1 := T116_80
  T2 := Q2.T116_80_2
  h1 := (0,0,1,2,0)
  h2 := (0,0,1,2,0)
  D := [[0, 1, 2, 0], [0, 1, 2, 2], [0, 1, 2, 4], [0, 1, 2, 1], [0, 1, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_80_40 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨80, by decide⟩
  m := 5
  T1 := T116_80
  T2 := Q2.T116_80_2
  h1 := (0,0,1,3,0)
  h2 := (0,0,1,3,0)
  D := [[0, 1, 3, 0], [0, 1, 3, 3], [0, 1, 3, 1], [0, 1, 3, 4], [0, 1, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_80_45 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨80, by decide⟩
  m := 5
  T1 := T116_80
  T2 := Q2.T116_80_2
  h1 := (0,0,1,4,0)
  h2 := (0,0,1,4,0)
  D := [[0, 1, 4, 0], [0, 1, 4, 4], [0, 1, 4, 3], [0, 1, 4, 2], [0, 1, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_80_50 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨80, by decide⟩
  m := 5
  T1 := T116_80
  T2 := Q2.T116_80_2
  h1 := (0,0,2,0,0)
  h2 := (0,0,2,0,0)
  D := [[0, 2, 0, 0], [0, 2, 0, 0], [0, 2, 0, 0], [0, 2, 0, 0], [0, 2, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_80_55 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨80, by decide⟩
  m := 5
  T1 := T116_80
  T2 := Q2.T116_80_2
  h1 := (0,0,2,1,0)
  h2 := (0,0,2,1,0)
  D := [[0, 2, 1, 0], [0, 2, 1, 1], [0, 2, 1, 2], [0, 2, 1, 3], [0, 2, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_80_60 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨80, by decide⟩
  m := 5
  T1 := T116_80
  T2 := Q2.T116_80_2
  h1 := (0,0,2,2,0)
  h2 := (0,0,2,2,0)
  D := [[0, 2, 2, 0], [0, 2, 2, 2], [0, 2, 2, 4], [0, 2, 2, 1], [0, 2, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_80_65 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨80, by decide⟩
  m := 5
  T1 := T116_80
  T2 := Q2.T116_80_2
  h1 := (0,0,2,3,0)
  h2 := (0,0,2,3,0)
  D := [[0, 2, 3, 0], [0, 2, 3, 3], [0, 2, 3, 1], [0, 2, 3, 4], [0, 2, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_80_70 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨80, by decide⟩
  m := 5
  T1 := T116_80
  T2 := Q2.T116_80_2
  h1 := (0,0,2,4,0)
  h2 := (0,0,2,4,0)
  D := [[0, 2, 4, 0], [0, 2, 4, 4], [0, 2, 4, 3], [0, 2, 4, 2], [0, 2, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_80_75 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨80, by decide⟩
  m := 5
  T1 := T116_80
  T2 := Q2.T116_80_2
  h1 := (0,0,3,0,0)
  h2 := (0,0,3,0,0)
  D := [[0, 3, 0, 0], [0, 3, 0, 0], [0, 3, 0, 0], [0, 3, 0, 0], [0, 3, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_80_80 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨80, by decide⟩
  m := 5
  T1 := T116_80
  T2 := Q2.T116_80_2
  h1 := (0,0,3,1,0)
  h2 := (0,0,3,1,0)
  D := [[0, 3, 1, 0], [0, 3, 1, 1], [0, 3, 1, 2], [0, 3, 1, 3], [0, 3, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_80_85 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨80, by decide⟩
  m := 5
  T1 := T116_80
  T2 := Q2.T116_80_2
  h1 := (0,0,3,2,0)
  h2 := (0,0,3,2,0)
  D := [[0, 3, 2, 0], [0, 3, 2, 2], [0, 3, 2, 4], [0, 3, 2, 1], [0, 3, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_80_90 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨80, by decide⟩
  m := 5
  T1 := T116_80
  T2 := Q2.T116_80_2
  h1 := (0,0,3,3,0)
  h2 := (0,0,3,3,0)
  D := [[0, 3, 3, 0], [0, 3, 3, 3], [0, 3, 3, 1], [0, 3, 3, 4], [0, 3, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_80_95 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨80, by decide⟩
  m := 5
  T1 := T116_80
  T2 := Q2.T116_80_2
  h1 := (0,0,3,4,0)
  h2 := (0,0,3,4,0)
  D := [[0, 3, 4, 0], [0, 3, 4, 4], [0, 3, 4, 3], [0, 3, 4, 2], [0, 3, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_80_100 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨80, by decide⟩
  m := 5
  T1 := T116_80
  T2 := Q2.T116_80_2
  h1 := (0,0,4,0,0)
  h2 := (0,0,4,0,0)
  D := [[0, 4, 0, 0], [0, 4, 0, 0], [0, 4, 0, 0], [0, 4, 0, 0], [0, 4, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_80_105 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨80, by decide⟩
  m := 5
  T1 := T116_80
  T2 := Q2.T116_80_2
  h1 := (0,0,4,1,0)
  h2 := (0,0,4,1,0)
  D := [[0, 4, 1, 0], [0, 4, 1, 1], [0, 4, 1, 2], [0, 4, 1, 3], [0, 4, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_80_110 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨80, by decide⟩
  m := 5
  T1 := T116_80
  T2 := Q2.T116_80_2
  h1 := (0,0,4,2,0)
  h2 := (0,0,4,2,0)
  D := [[0, 4, 2, 0], [0, 4, 2, 2], [0, 4, 2, 4], [0, 4, 2, 1], [0, 4, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_80_115 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨80, by decide⟩
  m := 5
  T1 := T116_80
  T2 := Q2.T116_80_2
  h1 := (0,0,4,3,0)
  h2 := (0,0,4,3,0)
  D := [[0, 4, 3, 0], [0, 4, 3, 3], [0, 4, 3, 1], [0, 4, 3, 4], [0, 4, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_80_120 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨80, by decide⟩
  m := 5
  T1 := T116_80
  T2 := Q2.T116_80_2
  h1 := (0,0,4,4,0)
  h2 := (0,0,4,4,0)
  D := [[0, 4, 4, 0], [0, 4, 4, 4], [0, 4, 4, 3], [0, 4, 4, 2], [0, 4, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_90_0 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨90, by decide⟩
  m := 5
  T1 := T116_90
  T2 := Q2.T116_90_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_90_1 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨90, by decide⟩
  m := 5
  T1 := T116_90
  T2 := Q2.T116_90_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_90_2 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨90, by decide⟩
  m := 5
  T1 := T116_90
  T2 := Q2.T116_90_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_90_3 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨90, by decide⟩
  m := 5
  T1 := T116_90
  T2 := Q2.T116_90_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_90_4 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨90, by decide⟩
  m := 5
  T1 := T116_90
  T2 := Q2.T116_90_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_90_5 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨90, by decide⟩
  m := 5
  T1 := T116_90
  T2 := Q2.T116_90_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 1, 0], [0, 0, 1, 1], [0, 0, 1, 2], [0, 0, 1, 3], [0, 0, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_90_10 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨90, by decide⟩
  m := 5
  T1 := T116_90
  T2 := Q2.T116_90_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 2, 0], [0, 0, 2, 2], [0, 0, 2, 4], [0, 0, 2, 1], [0, 0, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_90_15 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨90, by decide⟩
  m := 5
  T1 := T116_90
  T2 := Q2.T116_90_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 3, 0], [0, 0, 3, 3], [0, 0, 3, 1], [0, 0, 3, 4], [0, 0, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_90_20 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨90, by decide⟩
  m := 5
  T1 := T116_90
  T2 := Q2.T116_90_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 4, 0], [0, 0, 4, 4], [0, 0, 4, 3], [0, 0, 4, 2], [0, 0, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_90_25 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨90, by decide⟩
  m := 5
  T1 := T116_90
  T2 := Q2.T116_90_2
  h1 := (0,1,4,0,0)
  h2 := (0,1,4,0,0)
  D := [[1, 4, 0, 1], [1, 4, 1, 1], [1, 4, 2, 2], [1, 4, 3, 4], [1, 4, 4, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_90_50 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨90, by decide⟩
  m := 5
  T1 := T116_90
  T2 := Q2.T116_90_2
  h1 := (0,2,3,0,4)
  h2 := (0,2,3,0,4)
  D := [[2, 3, 0, 3], [2, 3, 2, 3], [2, 3, 4, 0], [2, 3, 1, 4], [2, 3, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_90_75 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨90, by decide⟩
  m := 5
  T1 := T116_90
  T2 := Q2.T116_90_2
  h1 := (0,3,2,0,2)
  h2 := (0,3,2,0,2)
  D := [[3, 2, 0, 1], [3, 2, 3, 1], [3, 2, 1, 4], [3, 2, 4, 0], [3, 2, 2, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_90_100 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨90, by decide⟩
  m := 5
  T1 := T116_90
  T2 := Q2.T116_90_2
  h1 := (0,4,1,0,4)
  h2 := (0,4,1,0,4)
  D := [[4, 1, 0, 0], [4, 1, 4, 0], [4, 1, 3, 4], [4, 1, 2, 2], [4, 1, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_95_0 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨95, by decide⟩
  m := 5
  T1 := T116_95
  T2 := Q2.T116_95_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_95_1 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨95, by decide⟩
  m := 5
  T1 := T116_95
  T2 := Q2.T116_95_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_95_2 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨95, by decide⟩
  m := 5
  T1 := T116_95
  T2 := Q2.T116_95_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_95_3 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨95, by decide⟩
  m := 5
  T1 := T116_95
  T2 := Q2.T116_95_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_95_4 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨95, by decide⟩
  m := 5
  T1 := T116_95
  T2 := Q2.T116_95_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_95_5 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨95, by decide⟩
  m := 5
  T1 := T116_95
  T2 := Q2.T116_95_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 1, 0], [0, 0, 1, 1], [0, 0, 1, 2], [0, 0, 1, 3], [0, 0, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_95_10 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨95, by decide⟩
  m := 5
  T1 := T116_95
  T2 := Q2.T116_95_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 2, 0], [0, 0, 2, 2], [0, 0, 2, 4], [0, 0, 2, 1], [0, 0, 2, 3]]
  bind1 := by decide
  bind2 := by decide

end LeanDring.P5Presentation
