/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.Twin1.ColCert
import LeanDring.P5.Data.EntryK.C021

/-!
# Species-table cell data, stage 2 — twin-coincident columns (cheap tier)

Per-column certified exponent-vector data (`ColCert`/`ColCertDiv`) with kernel
`decide` bindings. Emitted; the embedded lists are what the kernel certifies.
rest tier, chunk 188: 60 columns.
-/

-- machine-emitted data: silence style linters (generated long lines, file-level options)
set_option linter.style.longLine false

namespace LeanDring.P5Presentation

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

def colCert_88_88_10 : ColCert where
  rK := ⟨88, by decide⟩
  rH := ⟨88, by decide⟩
  m := 5
  T1 := T88_88
  T2 := Q2.T88_88_2
  h1 := (2,0,0,3,4)
  h2 := (2,0,0,3,4)
  D := [[2, 0, 3], [2, 0, 1], [2, 0, 4], [2, 0, 2], [2, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_88_88_11 : ColCert where
  rK := ⟨88, by decide⟩
  rH := ⟨88, by decide⟩
  m := 5
  T1 := T88_88
  T2 := Q2.T88_88_2
  h1 := (2,0,1,0,4)
  h2 := (2,0,1,0,4)
  D := [[2, 1, 4], [2, 1, 2], [2, 1, 0], [2, 1, 3], [2, 1, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_88_88_12 : ColCert where
  rK := ⟨88, by decide⟩
  rH := ⟨88, by decide⟩
  m := 5
  T1 := T88_88
  T2 := Q2.T88_88_2
  h1 := (2,0,2,2,4)
  h2 := (2,0,2,2,4)
  D := [[2, 2, 0], [2, 2, 3], [2, 2, 1], [2, 2, 4], [2, 2, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_88_88_13 : ColCert where
  rK := ⟨88, by decide⟩
  rH := ⟨88, by decide⟩
  m := 5
  T1 := T88_88
  T2 := Q2.T88_88_2
  h1 := (2,0,3,4,4)
  h2 := (2,0,3,4,4)
  D := [[2, 3, 1], [2, 3, 4], [2, 3, 2], [2, 3, 0], [2, 3, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_88_88_14 : ColCert where
  rK := ⟨88, by decide⟩
  rH := ⟨88, by decide⟩
  m := 5
  T1 := T88_88
  T2 := Q2.T88_88_2
  h1 := (2,0,4,1,4)
  h2 := (2,0,4,1,4)
  D := [[2, 4, 2], [2, 4, 0], [2, 4, 3], [2, 4, 1], [2, 4, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_88_88_15 : ColCert where
  rK := ⟨88, by decide⟩
  rH := ⟨88, by decide⟩
  m := 5
  T1 := T88_88
  T2 := Q2.T88_88_2
  h1 := (3,0,0,2,2)
  h2 := (3,0,0,2,2)
  D := [[3, 0, 2], [3, 0, 4], [3, 0, 1], [3, 0, 3], [3, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_88_88_16 : ColCert where
  rK := ⟨88, by decide⟩
  rH := ⟨88, by decide⟩
  m := 5
  T1 := T88_88
  T2 := Q2.T88_88_2
  h1 := (3,0,1,4,2)
  h2 := (3,0,1,4,2)
  D := [[3, 1, 1], [3, 1, 3], [3, 1, 0], [3, 1, 2], [3, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_88_88_17 : ColCert where
  rK := ⟨88, by decide⟩
  rH := ⟨88, by decide⟩
  m := 5
  T1 := T88_88
  T2 := Q2.T88_88_2
  h1 := (3,0,2,1,2)
  h2 := (3,0,2,1,2)
  D := [[3, 2, 0], [3, 2, 2], [3, 2, 4], [3, 2, 1], [3, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_88_88_18 : ColCert where
  rK := ⟨88, by decide⟩
  rH := ⟨88, by decide⟩
  m := 5
  T1 := T88_88
  T2 := Q2.T88_88_2
  h1 := (3,0,3,3,2)
  h2 := (3,0,3,3,2)
  D := [[3, 3, 4], [3, 3, 1], [3, 3, 3], [3, 3, 0], [3, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_88_88_19 : ColCert where
  rK := ⟨88, by decide⟩
  rH := ⟨88, by decide⟩
  m := 5
  T1 := T88_88
  T2 := Q2.T88_88_2
  h1 := (3,0,4,0,2)
  h2 := (3,0,4,0,2)
  D := [[3, 4, 3], [3, 4, 0], [3, 4, 2], [3, 4, 4], [3, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_88_88_20 : ColCert where
  rK := ⟨88, by decide⟩
  rH := ⟨88, by decide⟩
  m := 5
  T1 := T88_88
  T2 := Q2.T88_88_2
  h1 := (4,0,0,1,4)
  h2 := (4,0,0,1,4)
  D := [[4, 0, 1], [4, 0, 2], [4, 0, 3], [4, 0, 4], [4, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_88_88_21 : ColCert where
  rK := ⟨88, by decide⟩
  rH := ⟨88, by decide⟩
  m := 5
  T1 := T88_88
  T2 := Q2.T88_88_2
  h1 := (4,0,1,3,4)
  h2 := (4,0,1,3,4)
  D := [[4, 1, 3], [4, 1, 4], [4, 1, 0], [4, 1, 1], [4, 1, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_88_88_22 : ColCert where
  rK := ⟨88, by decide⟩
  rH := ⟨88, by decide⟩
  m := 5
  T1 := T88_88
  T2 := Q2.T88_88_2
  h1 := (4,0,2,0,4)
  h2 := (4,0,2,0,4)
  D := [[4, 2, 0], [4, 2, 1], [4, 2, 2], [4, 2, 3], [4, 2, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_88_88_23 : ColCert where
  rK := ⟨88, by decide⟩
  rH := ⟨88, by decide⟩
  m := 5
  T1 := T88_88
  T2 := Q2.T88_88_2
  h1 := (4,0,3,2,4)
  h2 := (4,0,3,2,4)
  D := [[4, 3, 2], [4, 3, 3], [4, 3, 4], [4, 3, 0], [4, 3, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_88_88_24 : ColCert where
  rK := ⟨88, by decide⟩
  rH := ⟨88, by decide⟩
  m := 5
  T1 := T88_88
  T2 := Q2.T88_88_2
  h1 := (4,0,4,4,4)
  h2 := (4,0,4,4,4)
  D := [[4, 4, 4], [4, 4, 0], [4, 4, 1], [4, 4, 2], [4, 4, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_89_0_0 : ColCert where
  rK := ⟨89, by decide⟩
  rH := ⟨0, by decide⟩
  m := 25
  T1 := T89_0
  T2 := Q2.T89_0_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_89_2_0 : ColCert where
  rK := ⟨89, by decide⟩
  rH := ⟨2, by decide⟩
  m := 5
  T1 := T89_2
  T2 := Q2.T89_2_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_89_2_1 : ColCert where
  rK := ⟨89, by decide⟩
  rH := ⟨2, by decide⟩
  m := 5
  T1 := T89_2
  T2 := Q2.T89_2_2
  h1 := (1,0,4,1,0)
  h2 := (1,0,4,1,0)
  D := [[1, 4, 0], [1, 4, 4], [1, 4, 3], [1, 4, 2], [1, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_89_2_2 : ColCert where
  rK := ⟨89, by decide⟩
  rH := ⟨2, by decide⟩
  m := 5
  T1 := T89_2
  T2 := Q2.T89_2_2
  h1 := (2,0,3,2,1)
  h2 := (2,0,3,2,1)
  D := [[2, 3, 1], [2, 3, 4], [2, 3, 2], [2, 3, 0], [2, 3, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_89_2_3 : ColCert where
  rK := ⟨89, by decide⟩
  rH := ⟨2, by decide⟩
  m := 5
  T1 := T89_2
  T2 := Q2.T89_2_2
  h1 := (3,0,2,3,3)
  h2 := (3,0,2,3,3)
  D := [[3, 2, 3], [3, 2, 0], [3, 2, 2], [3, 2, 4], [3, 2, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_89_2_4 : ColCert where
  rK := ⟨89, by decide⟩
  rH := ⟨2, by decide⟩
  m := 5
  T1 := T89_2
  T2 := Q2.T89_2_2
  h1 := (4,0,1,4,1)
  h2 := (4,0,1,4,1)
  D := [[4, 1, 1], [4, 1, 2], [4, 1, 3], [4, 1, 4], [4, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_89_3_0 : ColCert where
  rK := ⟨89, by decide⟩
  rH := ⟨3, by decide⟩
  m := 5
  T1 := T89_3
  T2 := Q2.T89_3_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_89_3_1 : ColCert where
  rK := ⟨89, by decide⟩
  rH := ⟨3, by decide⟩
  m := 5
  T1 := T89_3
  T2 := Q2.T89_3_2
  h1 := (1,0,2,3,1)
  h2 := (1,0,2,3,1)
  D := [[1, 2, 1], [1, 2, 0], [1, 2, 4], [1, 2, 3], [1, 2, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_89_3_2 : ColCert where
  rK := ⟨89, by decide⟩
  rH := ⟨3, by decide⟩
  m := 5
  T1 := T89_3
  T2 := Q2.T89_3_2
  h1 := (2,0,4,1,0)
  h2 := (2,0,4,1,0)
  D := [[2, 4, 0], [2, 4, 3], [2, 4, 1], [2, 4, 4], [2, 4, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_89_3_3 : ColCert where
  rK := ⟨89, by decide⟩
  rH := ⟨3, by decide⟩
  m := 5
  T1 := T89_3
  T2 := Q2.T89_3_2
  h1 := (3,0,1,4,2)
  h2 := (3,0,1,4,2)
  D := [[3, 1, 2], [3, 1, 4], [3, 1, 1], [3, 1, 3], [3, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_89_3_4 : ColCert where
  rK := ⟨89, by decide⟩
  rH := ⟨3, by decide⟩
  m := 5
  T1 := T89_3
  T2 := Q2.T89_3_2
  h1 := (4,0,3,2,2)
  h2 := (4,0,3,2,2)
  D := [[4, 3, 2], [4, 3, 3], [4, 3, 4], [4, 3, 0], [4, 3, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_89_4_0 : ColCert where
  rK := ⟨89, by decide⟩
  rH := ⟨4, by decide⟩
  m := 5
  T1 := T89_4
  T2 := Q2.T89_4_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_89_4_1 : ColCert where
  rK := ⟨89, by decide⟩
  rH := ⟨4, by decide⟩
  m := 5
  T1 := T89_4
  T2 := Q2.T89_4_2
  h1 := (1,0,3,2,3)
  h2 := (1,0,3,2,3)
  D := [[1, 3, 0], [1, 3, 4], [1, 3, 3], [1, 3, 2], [1, 3, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_89_4_2 : ColCert where
  rK := ⟨89, by decide⟩
  rH := ⟨4, by decide⟩
  m := 5
  T1 := T89_4
  T2 := Q2.T89_4_2
  h1 := (2,0,1,4,3)
  h2 := (2,0,1,4,3)
  D := [[2, 1, 2], [2, 1, 0], [2, 1, 3], [2, 1, 1], [2, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_89_4_3 : ColCert where
  rK := ⟨89, by decide⟩
  rH := ⟨4, by decide⟩
  m := 5
  T1 := T89_4
  T2 := Q2.T89_4_2
  h1 := (3,0,4,1,0)
  h2 := (3,0,4,1,0)
  D := [[3, 4, 1], [3, 4, 3], [3, 4, 0], [3, 4, 2], [3, 4, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_89_4_4 : ColCert where
  rK := ⟨89, by decide⟩
  rH := ⟨4, by decide⟩
  m := 5
  T1 := T89_4
  T2 := Q2.T89_4_2
  h1 := (4,0,2,3,4)
  h2 := (4,0,2,3,4)
  D := [[4, 2, 2], [4, 2, 3], [4, 2, 4], [4, 2, 0], [4, 2, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_89_5_0 : ColCert where
  rK := ⟨89, by decide⟩
  rH := ⟨5, by decide⟩
  m := 5
  T1 := T89_5
  T2 := Q2.T89_5_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_89_5_1 : ColCert where
  rK := ⟨89, by decide⟩
  rH := ⟨5, by decide⟩
  m := 5
  T1 := T89_5
  T2 := Q2.T89_5_2
  h1 := (1,0,1,4,4)
  h2 := (1,0,1,4,4)
  D := [[1, 1, 3], [1, 1, 2], [1, 1, 1], [1, 1, 0], [1, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_89_5_2 : ColCert where
  rK := ⟨89, by decide⟩
  rH := ⟨5, by decide⟩
  m := 5
  T1 := T89_5
  T2 := Q2.T89_5_2
  h1 := (2,0,2,3,2)
  h2 := (2,0,2,3,2)
  D := [[2, 2, 0], [2, 2, 3], [2, 2, 1], [2, 2, 4], [2, 2, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_89_5_3 : ColCert where
  rK := ⟨89, by decide⟩
  rH := ⟨5, by decide⟩
  m := 5
  T1 := T89_5
  T2 := Q2.T89_5_2
  h1 := (3,0,3,2,4)
  h2 := (3,0,3,2,4)
  D := [[3, 3, 1], [3, 3, 3], [3, 3, 0], [3, 3, 2], [3, 3, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_89_5_4 : ColCert where
  rK := ⟨89, by decide⟩
  rH := ⟨5, by decide⟩
  m := 5
  T1 := T89_5
  T2 := Q2.T89_5_2
  h1 := (4,0,4,1,0)
  h2 := (4,0,4,1,0)
  D := [[4, 4, 1], [4, 4, 2], [4, 4, 3], [4, 4, 4], [4, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_89_8_0 : ColCert where
  rK := ⟨89, by decide⟩
  rH := ⟨8, by decide⟩
  m := 25
  T1 := T89_8
  T2 := Q2.T89_8_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_89_8_1 : ColCert where
  rK := ⟨89, by decide⟩
  rH := ⟨8, by decide⟩
  m := 25
  T1 := T89_8
  T2 := Q2.T89_8_2
  h1 := (0,0,1,1,4)
  h2 := (0,0,1,1,4)
  D := [[0, 1, 4], [0, 1, 4], [0, 1, 4], [0, 1, 4], [0, 1, 4], [0, 1, 0], [0, 1, 0], [0, 1, 0], [0, 1, 0], [0, 1, 0], [0, 1, 1], [0, 1, 1], [0, 1, 1], [0, 1, 1], [0, 1, 1], [0, 1, 2], [0, 1, 2], [0, 1, 2], [0, 1, 2], [0, 1, 2], [0, 1, 3], [0, 1, 3], [0, 1, 3], [0, 1, 3], [0, 1, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_89_8_2 : ColCert where
  rK := ⟨89, by decide⟩
  rH := ⟨8, by decide⟩
  m := 25
  T1 := T89_8
  T2 := Q2.T89_8_2
  h1 := (0,0,2,2,3)
  h2 := (0,0,2,2,3)
  D := [[0, 2, 3], [0, 2, 3], [0, 2, 3], [0, 2, 3], [0, 2, 3], [0, 2, 0], [0, 2, 0], [0, 2, 0], [0, 2, 0], [0, 2, 0], [0, 2, 2], [0, 2, 2], [0, 2, 2], [0, 2, 2], [0, 2, 2], [0, 2, 4], [0, 2, 4], [0, 2, 4], [0, 2, 4], [0, 2, 4], [0, 2, 1], [0, 2, 1], [0, 2, 1], [0, 2, 1], [0, 2, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_89_8_3 : ColCert where
  rK := ⟨89, by decide⟩
  rH := ⟨8, by decide⟩
  m := 25
  T1 := T89_8
  T2 := Q2.T89_8_2
  h1 := (0,0,3,3,2)
  h2 := (0,0,3,3,2)
  D := [[0, 3, 2], [0, 3, 2], [0, 3, 2], [0, 3, 2], [0, 3, 2], [0, 3, 0], [0, 3, 0], [0, 3, 0], [0, 3, 0], [0, 3, 0], [0, 3, 3], [0, 3, 3], [0, 3, 3], [0, 3, 3], [0, 3, 3], [0, 3, 1], [0, 3, 1], [0, 3, 1], [0, 3, 1], [0, 3, 1], [0, 3, 4], [0, 3, 4], [0, 3, 4], [0, 3, 4], [0, 3, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_89_8_4 : ColCert where
  rK := ⟨89, by decide⟩
  rH := ⟨8, by decide⟩
  m := 25
  T1 := T89_8
  T2 := Q2.T89_8_2
  h1 := (0,0,4,4,1)
  h2 := (0,0,4,4,1)
  D := [[0, 4, 1], [0, 4, 1], [0, 4, 1], [0, 4, 1], [0, 4, 1], [0, 4, 0], [0, 4, 0], [0, 4, 0], [0, 4, 0], [0, 4, 0], [0, 4, 4], [0, 4, 4], [0, 4, 4], [0, 4, 4], [0, 4, 4], [0, 4, 3], [0, 4, 3], [0, 4, 3], [0, 4, 3], [0, 4, 3], [0, 4, 2], [0, 4, 2], [0, 4, 2], [0, 4, 2], [0, 4, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_89_11_0 : ColCert where
  rK := ⟨89, by decide⟩
  rH := ⟨11, by decide⟩
  m := 5
  T1 := T89_11
  T2 := Q2.T89_11_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_89_11_1 : ColCert where
  rK := ⟨89, by decide⟩
  rH := ⟨11, by decide⟩
  m := 5
  T1 := T89_11
  T2 := Q2.T89_11_2
  h1 := (1,0,0,4,3)
  h2 := (1,0,0,4,3)
  D := [[1, 0, 3], [1, 0, 2], [1, 0, 1], [1, 0, 0], [1, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_89_11_2 : ColCert where
  rK := ⟨89, by decide⟩
  rH := ⟨11, by decide⟩
  m := 5
  T1 := T89_11
  T2 := Q2.T89_11_2
  h1 := (2,0,0,3,0)
  h2 := (2,0,0,3,0)
  D := [[2, 0, 1], [2, 0, 4], [2, 0, 2], [2, 0, 0], [2, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_89_11_3 : ColCert where
  rK := ⟨89, by decide⟩
  rH := ⟨11, by decide⟩
  m := 5
  T1 := T89_11
  T2 := Q2.T89_11_2
  h1 := (3,0,0,2,1)
  h2 := (3,0,0,2,1)
  D := [[3, 0, 4], [3, 0, 1], [3, 0, 3], [3, 0, 0], [3, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_89_11_4 : ColCert where
  rK := ⟨89, by decide⟩
  rH := ⟨11, by decide⟩
  m := 5
  T1 := T89_11
  T2 := Q2.T89_11_2
  h1 := (4,0,0,1,1)
  h2 := (4,0,0,1,1)
  D := [[4, 0, 2], [4, 0, 3], [4, 0, 4], [4, 0, 0], [4, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_89_12_0 : ColCert where
  rK := ⟨89, by decide⟩
  rH := ⟨12, by decide⟩
  m := 25
  T1 := T89_12
  T2 := Q2.T89_12_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_89_12_1 : ColCert where
  rK := ⟨89, by decide⟩
  rH := ⟨12, by decide⟩
  m := 25
  T1 := T89_12
  T2 := Q2.T89_12_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_89_12_2 : ColCert where
  rK := ⟨89, by decide⟩
  rH := ⟨12, by decide⟩
  m := 25
  T1 := T89_12
  T2 := Q2.T89_12_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_89_12_3 : ColCert where
  rK := ⟨89, by decide⟩
  rH := ⟨12, by decide⟩
  m := 25
  T1 := T89_12
  T2 := Q2.T89_12_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_89_12_4 : ColCert where
  rK := ⟨89, by decide⟩
  rH := ⟨12, by decide⟩
  m := 25
  T1 := T89_12
  T2 := Q2.T89_12_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_89_20_0 : ColCert where
  rK := ⟨89, by decide⟩
  rH := ⟨20, by decide⟩
  m := 5
  T1 := T89_20
  T2 := Q2.T89_20_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_89_20_1 : ColCert where
  rK := ⟨89, by decide⟩
  rH := ⟨20, by decide⟩
  m := 5
  T1 := T89_20
  T2 := Q2.T89_20_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_89_20_2 : ColCert where
  rK := ⟨89, by decide⟩
  rH := ⟨20, by decide⟩
  m := 5
  T1 := T89_20
  T2 := Q2.T89_20_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_89_20_3 : ColCert where
  rK := ⟨89, by decide⟩
  rH := ⟨20, by decide⟩
  m := 5
  T1 := T89_20
  T2 := Q2.T89_20_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_89_20_4 : ColCert where
  rK := ⟨89, by decide⟩
  rH := ⟨20, by decide⟩
  m := 5
  T1 := T89_20
  T2 := Q2.T89_20_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_89_20_5 : ColCert where
  rK := ⟨89, by decide⟩
  rH := ⟨20, by decide⟩
  m := 5
  T1 := T89_20
  T2 := Q2.T89_20_2
  h1 := (1,0,4,1,1)
  h2 := (1,0,4,1,1)
  D := [[1, 4, 1], [1, 4, 0], [1, 4, 4], [1, 4, 3], [1, 4, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_89_20_10 : ColCert where
  rK := ⟨89, by decide⟩
  rH := ⟨20, by decide⟩
  m := 5
  T1 := T89_20
  T2 := Q2.T89_20_2
  h1 := (2,0,3,2,3)
  h2 := (2,0,3,2,3)
  D := [[2, 3, 3], [2, 3, 1], [2, 3, 4], [2, 3, 2], [2, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_89_20_15 : ColCert where
  rK := ⟨89, by decide⟩
  rH := ⟨20, by decide⟩
  m := 5
  T1 := T89_20
  T2 := Q2.T89_20_2
  h1 := (3,0,2,3,1)
  h2 := (3,0,2,3,1)
  D := [[3, 2, 1], [3, 2, 3], [3, 2, 0], [3, 2, 2], [3, 2, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_89_20_20 : ColCert where
  rK := ⟨89, by decide⟩
  rH := ⟨20, by decide⟩
  m := 5
  T1 := T89_20
  T2 := Q2.T89_20_2
  h1 := (4,0,1,4,0)
  h2 := (4,0,1,4,0)
  D := [[4, 1, 0], [4, 1, 1], [4, 1, 2], [4, 1, 3], [4, 1, 4]]
  bind1 := by decide
  bind2 := by decide

end LeanDring.P5Presentation
