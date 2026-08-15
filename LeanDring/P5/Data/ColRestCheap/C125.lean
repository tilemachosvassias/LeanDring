/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.Twin1.ColCert
import LeanDring.P5.Data.EntryK.C044

/-!
# Species-table cell data, stage 2 — twin-coincident columns (cheap tier)

Per-column certified exponent-vector data (`ColCert`/`ColCertDiv`) with kernel
`decide` bindings. Emitted; the embedded lists are what the kernel certifies.
rest tier, chunk 124: 60 columns.
-/

-- machine-emitted data: silence style linters (generated long lines, file-level options)
set_option linter.style.longLine false

namespace LeanDring.P5Presentation

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

def colCert_147_97_2 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨97, by decide⟩
  m := 1
  T1 := T147_97
  T2 := Q2.T147_97_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_97_3 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨97, by decide⟩
  m := 1
  T1 := T147_97
  T2 := Q2.T147_97_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_97_4 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨97, by decide⟩
  m := 1
  T1 := T147_97
  T2 := Q2.T147_97_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_97_5 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨97, by decide⟩
  m := 1
  T1 := T147_97
  T2 := Q2.T147_97_2
  h1 := (1,2,4,3,0)
  h2 := (1,2,4,3,0)
  D := [[1, 2, 4, 1, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_97_10 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨97, by decide⟩
  m := 1
  T1 := T147_97
  T2 := Q2.T147_97_2
  h1 := (2,4,3,3,1)
  h2 := (2,4,3,3,1)
  D := [[2, 4, 3, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_98_0 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨98, by decide⟩
  m := 1
  T1 := T147_98
  T2 := Q2.T147_98_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_98_1 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨98, by decide⟩
  m := 1
  T1 := T147_98
  T2 := Q2.T147_98_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_98_2 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨98, by decide⟩
  m := 1
  T1 := T147_98
  T2 := Q2.T147_98_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_98_3 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨98, by decide⟩
  m := 1
  T1 := T147_98
  T2 := Q2.T147_98_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_98_4 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨98, by decide⟩
  m := 1
  T1 := T147_98
  T2 := Q2.T147_98_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_98_5 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨98, by decide⟩
  m := 1
  T1 := T147_98
  T2 := Q2.T147_98_2
  h1 := (1,3,1,1,3)
  h2 := (1,3,1,1,3)
  D := [[1, 3, 1, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_99_0 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨99, by decide⟩
  m := 1
  T1 := T147_99
  T2 := Q2.T147_99_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_99_1 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨99, by decide⟩
  m := 1
  T1 := T147_99
  T2 := Q2.T147_99_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_99_2 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨99, by decide⟩
  m := 1
  T1 := T147_99
  T2 := Q2.T147_99_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_99_3 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨99, by decide⟩
  m := 1
  T1 := T147_99
  T2 := Q2.T147_99_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_99_4 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨99, by decide⟩
  m := 1
  T1 := T147_99
  T2 := Q2.T147_99_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_99_5 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨99, by decide⟩
  m := 1
  T1 := T147_99
  T2 := Q2.T147_99_2
  h1 := (1,1,2,0,0)
  h2 := (1,1,2,0,0)
  D := [[1, 1, 2, 4, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_99_10 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨99, by decide⟩
  m := 1
  T1 := T147_99
  T2 := Q2.T147_99_2
  h1 := (2,2,4,1,2)
  h2 := (2,2,4,1,2)
  D := [[2, 2, 4, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_99_15 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨99, by decide⟩
  m := 1
  T1 := T147_99
  T2 := Q2.T147_99_2
  h1 := (3,3,1,3,2)
  h2 := (3,3,1,3,2)
  D := [[3, 3, 1, 4, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_99_20 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨99, by decide⟩
  m := 1
  T1 := T147_99
  T2 := Q2.T147_99_2
  h1 := (4,4,3,1,1)
  h2 := (4,4,3,1,1)
  D := [[4, 4, 3, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_100_0 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨100, by decide⟩
  m := 1
  T1 := T147_100
  T2 := Q2.T147_100_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_100_1 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨100, by decide⟩
  m := 1
  T1 := T147_100
  T2 := Q2.T147_100_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_100_2 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨100, by decide⟩
  m := 1
  T1 := T147_100
  T2 := Q2.T147_100_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_100_3 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨100, by decide⟩
  m := 1
  T1 := T147_100
  T2 := Q2.T147_100_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_100_4 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨100, by decide⟩
  m := 1
  T1 := T147_100
  T2 := Q2.T147_100_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_100_5 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨100, by decide⟩
  m := 1
  T1 := T147_100
  T2 := Q2.T147_100_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_100_10 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨100, by decide⟩
  m := 1
  T1 := T147_100
  T2 := Q2.T147_100_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_100_15 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨100, by decide⟩
  m := 1
  T1 := T147_100
  T2 := Q2.T147_100_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_100_20 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨100, by decide⟩
  m := 1
  T1 := T147_100
  T2 := Q2.T147_100_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_100_25 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨100, by decide⟩
  m := 1
  T1 := T147_100
  T2 := Q2.T147_100_2
  h1 := (0,1,3,0,0)
  h2 := (0,1,3,0,0)
  D := [[0, 1, 3, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_100_50 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨100, by decide⟩
  m := 1
  T1 := T147_100
  T2 := Q2.T147_100_2
  h1 := (0,2,1,0,3)
  h2 := (0,2,1,0,3)
  D := [[0, 2, 1, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_100_75 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨100, by decide⟩
  m := 1
  T1 := T147_100
  T2 := Q2.T147_100_2
  h1 := (0,3,4,0,4)
  h2 := (0,3,4,0,4)
  D := [[0, 3, 4, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_100_100 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨100, by decide⟩
  m := 1
  T1 := T147_100
  T2 := Q2.T147_100_2
  h1 := (0,4,2,0,3)
  h2 := (0,4,2,0,3)
  D := [[0, 4, 2, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_101_0 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨101, by decide⟩
  m := 1
  T1 := T147_101
  T2 := Q2.T147_101_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_101_1 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨101, by decide⟩
  m := 1
  T1 := T147_101
  T2 := Q2.T147_101_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_101_2 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨101, by decide⟩
  m := 1
  T1 := T147_101
  T2 := Q2.T147_101_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_101_3 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨101, by decide⟩
  m := 1
  T1 := T147_101
  T2 := Q2.T147_101_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_101_4 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨101, by decide⟩
  m := 1
  T1 := T147_101
  T2 := Q2.T147_101_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_101_5 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨101, by decide⟩
  m := 1
  T1 := T147_101
  T2 := Q2.T147_101_2
  h1 := (1,4,2,4,3)
  h2 := (1,4,2,4,3)
  D := [[1, 4, 2, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_102_0 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨102, by decide⟩
  m := 1
  T1 := T147_102
  T2 := Q2.T147_102_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_102_1 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨102, by decide⟩
  m := 1
  T1 := T147_102
  T2 := Q2.T147_102_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_102_2 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨102, by decide⟩
  m := 1
  T1 := T147_102
  T2 := Q2.T147_102_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_102_3 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨102, by decide⟩
  m := 1
  T1 := T147_102
  T2 := Q2.T147_102_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_102_4 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨102, by decide⟩
  m := 1
  T1 := T147_102
  T2 := Q2.T147_102_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_102_5 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨102, by decide⟩
  m := 1
  T1 := T147_102
  T2 := Q2.T147_102_2
  h1 := (1,2,1,3,1)
  h2 := (1,2,1,3,1)
  D := [[1, 2, 1, 1, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_102_10 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨102, by decide⟩
  m := 1
  T1 := T147_102
  T2 := Q2.T147_102_2
  h1 := (2,4,2,3,2)
  h2 := (2,4,2,3,2)
  D := [[2, 4, 2, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_103_0 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨103, by decide⟩
  m := 1
  T1 := T147_103
  T2 := Q2.T147_103_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_103_1 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨103, by decide⟩
  m := 1
  T1 := T147_103
  T2 := Q2.T147_103_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_103_2 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨103, by decide⟩
  m := 1
  T1 := T147_103
  T2 := Q2.T147_103_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_103_3 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨103, by decide⟩
  m := 1
  T1 := T147_103
  T2 := Q2.T147_103_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_103_4 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨103, by decide⟩
  m := 1
  T1 := T147_103
  T2 := Q2.T147_103_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_103_5 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨103, by decide⟩
  m := 1
  T1 := T147_103
  T2 := Q2.T147_103_2
  h1 := (1,3,4,1,1)
  h2 := (1,3,4,1,1)
  D := [[1, 3, 4, 3, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_104_0 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨104, by decide⟩
  m := 1
  T1 := T147_104
  T2 := Q2.T147_104_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_104_1 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨104, by decide⟩
  m := 1
  T1 := T147_104
  T2 := Q2.T147_104_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_104_2 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨104, by decide⟩
  m := 1
  T1 := T147_104
  T2 := Q2.T147_104_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_104_3 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨104, by decide⟩
  m := 1
  T1 := T147_104
  T2 := Q2.T147_104_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_104_4 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨104, by decide⟩
  m := 1
  T1 := T147_104
  T2 := Q2.T147_104_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_104_5 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨104, by decide⟩
  m := 1
  T1 := T147_104
  T2 := Q2.T147_104_2
  h1 := (1,1,3,0,0)
  h2 := (1,1,3,0,0)
  D := [[1, 1, 3, 4, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_104_10 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨104, by decide⟩
  m := 1
  T1 := T147_104
  T2 := Q2.T147_104_2
  h1 := (2,2,1,1,3)
  h2 := (2,2,1,1,3)
  D := [[2, 2, 1, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_104_15 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨104, by decide⟩
  m := 1
  T1 := T147_104
  T2 := Q2.T147_104_2
  h1 := (3,3,4,3,0)
  h2 := (3,3,4,3,0)
  D := [[3, 3, 4, 4, 2]]
  bind1 := by decide
  bind2 := by decide

end LeanDring.P5Presentation
