/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.Twin1.ColCert
import LeanDring.P5.Data.EntryK.C042

/-!
# Species-table cell data, stage 2 — twin-coincident columns (cheap tier)

Per-column certified exponent-vector data (`ColCert`/`ColCertDiv`) with kernel
`decide` bindings. Emitted; the embedded lists are what the kernel certifies.
rest tier, chunk 102: 60 columns.
-/

-- machine-emitted data: silence style linters (generated long lines, file-level options)
set_option linter.style.longLine false

namespace LeanDring.P5Presentation

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

def colCert_144_100_5 : ColCert where
  rK := ⟨144, by decide⟩
  rH := ⟨100, by decide⟩
  m := 5
  T1 := T144_100
  T2 := Q2.T144_100_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_144_100_10 : ColCert where
  rK := ⟨144, by decide⟩
  rH := ⟨100, by decide⟩
  m := 5
  T1 := T144_100
  T2 := Q2.T144_100_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_144_100_15 : ColCert where
  rK := ⟨144, by decide⟩
  rH := ⟨100, by decide⟩
  m := 5
  T1 := T144_100
  T2 := Q2.T144_100_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_144_100_20 : ColCert where
  rK := ⟨144, by decide⟩
  rH := ⟨100, by decide⟩
  m := 5
  T1 := T144_100
  T2 := Q2.T144_100_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_144_101_0 : ColCert where
  rK := ⟨144, by decide⟩
  rH := ⟨101, by decide⟩
  m := 5
  T1 := T144_101
  T2 := Q2.T144_101_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_144_101_1 : ColCert where
  rK := ⟨144, by decide⟩
  rH := ⟨101, by decide⟩
  m := 5
  T1 := T144_101
  T2 := Q2.T144_101_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_144_101_2 : ColCert where
  rK := ⟨144, by decide⟩
  rH := ⟨101, by decide⟩
  m := 5
  T1 := T144_101
  T2 := Q2.T144_101_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_144_101_3 : ColCert where
  rK := ⟨144, by decide⟩
  rH := ⟨101, by decide⟩
  m := 5
  T1 := T144_101
  T2 := Q2.T144_101_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_144_101_4 : ColCert where
  rK := ⟨144, by decide⟩
  rH := ⟨101, by decide⟩
  m := 5
  T1 := T144_101
  T2 := Q2.T144_101_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_144_101_15 : ColCert where
  rK := ⟨144, by decide⟩
  rH := ⟨101, by decide⟩
  m := 5
  T1 := T144_101
  T2 := Q2.T144_101_2
  h1 := (3,2,1,4,1)
  h2 := (3,2,1,4,3)
  D := [[3, 2, 3, 3], [3, 2, 3, 1], [3, 2, 3, 4], [3, 2, 3, 2], [3, 2, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_144_102_0 : ColCert where
  rK := ⟨144, by decide⟩
  rH := ⟨102, by decide⟩
  m := 5
  T1 := T144_102
  T2 := Q2.T144_102_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_144_102_1 : ColCert where
  rK := ⟨144, by decide⟩
  rH := ⟨102, by decide⟩
  m := 5
  T1 := T144_102
  T2 := Q2.T144_102_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_144_102_2 : ColCert where
  rK := ⟨144, by decide⟩
  rH := ⟨102, by decide⟩
  m := 5
  T1 := T144_102
  T2 := Q2.T144_102_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_144_102_3 : ColCert where
  rK := ⟨144, by decide⟩
  rH := ⟨102, by decide⟩
  m := 5
  T1 := T144_102
  T2 := Q2.T144_102_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_144_102_4 : ColCert where
  rK := ⟨144, by decide⟩
  rH := ⟨102, by decide⟩
  m := 5
  T1 := T144_102
  T2 := Q2.T144_102_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_144_102_15 : ColCert where
  rK := ⟨144, by decide⟩
  rH := ⟨102, by decide⟩
  m := 5
  T1 := T144_102
  T2 := Q2.T144_102_2
  h1 := (3,1,3,0,1)
  h2 := (3,1,3,0,2)
  D := [[3, 1, 2, 2], [3, 1, 2, 1], [3, 1, 2, 0], [3, 1, 2, 4], [3, 1, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_144_103_0 : ColCert where
  rK := ⟨144, by decide⟩
  rH := ⟨103, by decide⟩
  m := 5
  T1 := T144_103
  T2 := Q2.T144_103_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_144_103_1 : ColCert where
  rK := ⟨144, by decide⟩
  rH := ⟨103, by decide⟩
  m := 5
  T1 := T144_103
  T2 := Q2.T144_103_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_144_103_2 : ColCert where
  rK := ⟨144, by decide⟩
  rH := ⟨103, by decide⟩
  m := 5
  T1 := T144_103
  T2 := Q2.T144_103_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_144_103_3 : ColCert where
  rK := ⟨144, by decide⟩
  rH := ⟨103, by decide⟩
  m := 5
  T1 := T144_103
  T2 := Q2.T144_103_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_144_103_4 : ColCert where
  rK := ⟨144, by decide⟩
  rH := ⟨103, by decide⟩
  m := 5
  T1 := T144_103
  T2 := Q2.T144_103_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_144_103_10 : ColCert where
  rK := ⟨144, by decide⟩
  rH := ⟨103, by decide⟩
  m := 5
  T1 := T144_103
  T2 := Q2.T144_103_2
  h1 := (2,1,3,0,1)
  h2 := (2,1,3,0,2)
  D := [[2, 1, 3, 4], [2, 1, 3, 3], [2, 1, 3, 2], [2, 1, 3, 1], [2, 1, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_144_103_20 : ColCert where
  rK := ⟨144, by decide⟩
  rH := ⟨103, by decide⟩
  m := 5
  T1 := T144_103
  T2 := Q2.T144_103_2
  h1 := (4,2,1,2,1)
  h2 := (4,2,1,2,3)
  D := [[4, 2, 4, 0], [4, 2, 4, 3], [4, 2, 4, 1], [4, 2, 4, 4], [4, 2, 4, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_144_104_0 : ColCert where
  rK := ⟨144, by decide⟩
  rH := ⟨104, by decide⟩
  m := 5
  T1 := T144_104
  T2 := Q2.T144_104_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_144_104_1 : ColCert where
  rK := ⟨144, by decide⟩
  rH := ⟨104, by decide⟩
  m := 5
  T1 := T144_104
  T2 := Q2.T144_104_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_144_104_2 : ColCert where
  rK := ⟨144, by decide⟩
  rH := ⟨104, by decide⟩
  m := 5
  T1 := T144_104
  T2 := Q2.T144_104_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_144_104_3 : ColCert where
  rK := ⟨144, by decide⟩
  rH := ⟨104, by decide⟩
  m := 5
  T1 := T144_104
  T2 := Q2.T144_104_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_144_104_4 : ColCert where
  rK := ⟨144, by decide⟩
  rH := ⟨104, by decide⟩
  m := 5
  T1 := T144_104
  T2 := Q2.T144_104_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_144_115_0 : ColCert where
  rK := ⟨144, by decide⟩
  rH := ⟨115, by decide⟩
  m := 5
  T1 := T144_115
  T2 := Q2.T144_115_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_144_115_1 : ColCert where
  rK := ⟨144, by decide⟩
  rH := ⟨115, by decide⟩
  m := 5
  T1 := T144_115
  T2 := Q2.T144_115_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_144_115_2 : ColCert where
  rK := ⟨144, by decide⟩
  rH := ⟨115, by decide⟩
  m := 5
  T1 := T144_115
  T2 := Q2.T144_115_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_144_115_3 : ColCert where
  rK := ⟨144, by decide⟩
  rH := ⟨115, by decide⟩
  m := 5
  T1 := T144_115
  T2 := Q2.T144_115_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_144_115_4 : ColCert where
  rK := ⟨144, by decide⟩
  rH := ⟨115, by decide⟩
  m := 5
  T1 := T144_115
  T2 := Q2.T144_115_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_144_115_5 : ColCert where
  rK := ⟨144, by decide⟩
  rH := ⟨115, by decide⟩
  m := 5
  T1 := T144_115
  T2 := Q2.T144_115_2
  h1 := (1,0,0,0,0)
  h2 := (1,0,0,0,0)
  D := [[1, 0, 0, 0], [1, 0, 0, 0], [1, 0, 0, 0], [1, 0, 0, 0], [1, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_144_115_10 : ColCert where
  rK := ⟨144, by decide⟩
  rH := ⟨115, by decide⟩
  m := 5
  T1 := T144_115
  T2 := Q2.T144_115_2
  h1 := (2,0,0,0,0)
  h2 := (2,0,0,0,0)
  D := [[2, 0, 0, 0], [2, 0, 0, 0], [2, 0, 0, 0], [2, 0, 0, 0], [2, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_144_115_15 : ColCert where
  rK := ⟨144, by decide⟩
  rH := ⟨115, by decide⟩
  m := 5
  T1 := T144_115
  T2 := Q2.T144_115_2
  h1 := (3,0,0,0,0)
  h2 := (3,0,0,0,0)
  D := [[3, 0, 0, 0], [3, 0, 0, 0], [3, 0, 0, 0], [3, 0, 0, 0], [3, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_144_115_20 : ColCert where
  rK := ⟨144, by decide⟩
  rH := ⟨115, by decide⟩
  m := 5
  T1 := T144_115
  T2 := Q2.T144_115_2
  h1 := (4,0,0,0,0)
  h2 := (4,0,0,0,0)
  D := [[4, 0, 0, 0], [4, 0, 0, 0], [4, 0, 0, 0], [4, 0, 0, 0], [4, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_144_144_0 : ColCert where
  rK := ⟨144, by decide⟩
  rH := ⟨144, by decide⟩
  m := 5
  T1 := T144_144
  T2 := Q2.T144_144_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_144_144_1 : ColCert where
  rK := ⟨144, by decide⟩
  rH := ⟨144, by decide⟩
  m := 5
  T1 := T144_144
  T2 := Q2.T144_144_2
  h1 := (0,1,3,0,2)
  h2 := (0,1,3,0,3)
  D := [[0, 1, 0, 2], [0, 1, 0, 1], [0, 1, 0, 0], [0, 1, 0, 4], [0, 1, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_144_144_2 : ColCert where
  rK := ⟨144, by decide⟩
  rH := ⟨144, by decide⟩
  m := 5
  T1 := T144_144
  T2 := Q2.T144_144_2
  h1 := (0,2,1,0,2)
  h2 := (0,2,1,0,4)
  D := [[0, 2, 0, 4], [0, 2, 0, 2], [0, 2, 0, 0], [0, 2, 0, 3], [0, 2, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_144_144_3 : ColCert where
  rK := ⟨144, by decide⟩
  rH := ⟨144, by decide⟩
  m := 5
  T1 := T144_144
  T2 := Q2.T144_144_2
  h1 := (0,3,4,0,0)
  h2 := (0,3,4,0,3)
  D := [[0, 3, 0, 1], [0, 3, 0, 3], [0, 3, 0, 0], [0, 3, 0, 2], [0, 3, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_144_144_4 : ColCert where
  rK := ⟨144, by decide⟩
  rH := ⟨144, by decide⟩
  m := 5
  T1 := T144_144
  T2 := Q2.T144_144_2
  h1 := (0,4,2,0,1)
  h2 := (0,4,2,0,0)
  D := [[0, 4, 0, 3], [0, 4, 0, 4], [0, 4, 0, 0], [0, 4, 0, 1], [0, 4, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_144_144_5 : ColCert where
  rK := ⟨144, by decide⟩
  rH := ⟨144, by decide⟩
  m := 5
  T1 := T144_144
  T2 := Q2.T144_144_2
  h1 := (1,0,0,0,0)
  h2 := (1,0,0,0,0)
  D := [[1, 0, 0, 0], [1, 0, 0, 0], [1, 0, 0, 0], [1, 0, 0, 0], [1, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_144_144_6 : ColCert where
  rK := ⟨144, by decide⟩
  rH := ⟨144, by decide⟩
  m := 5
  T1 := T144_144
  T2 := Q2.T144_144_2
  h1 := (1,1,3,0,2)
  h2 := (1,1,3,0,3)
  D := [[1, 1, 4, 3], [1, 1, 4, 2], [1, 1, 4, 1], [1, 1, 4, 0], [1, 1, 4, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_144_144_7 : ColCert where
  rK := ⟨144, by decide⟩
  rH := ⟨144, by decide⟩
  m := 5
  T1 := T144_144
  T2 := Q2.T144_144_2
  h1 := (1,2,1,0,2)
  h2 := (1,2,1,0,4)
  D := [[1, 2, 3, 1], [1, 2, 3, 4], [1, 2, 3, 2], [1, 2, 3, 0], [1, 2, 3, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_144_144_8 : ColCert where
  rK := ⟨144, by decide⟩
  rH := ⟨144, by decide⟩
  m := 5
  T1 := T144_144
  T2 := Q2.T144_144_2
  h1 := (1,3,4,0,0)
  h2 := (1,3,4,0,3)
  D := [[1, 3, 2, 4], [1, 3, 2, 1], [1, 3, 2, 3], [1, 3, 2, 0], [1, 3, 2, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_144_144_9 : ColCert where
  rK := ⟨144, by decide⟩
  rH := ⟨144, by decide⟩
  m := 5
  T1 := T144_144
  T2 := Q2.T144_144_2
  h1 := (1,4,2,0,1)
  h2 := (1,4,2,0,0)
  D := [[1, 4, 1, 2], [1, 4, 1, 3], [1, 4, 1, 4], [1, 4, 1, 0], [1, 4, 1, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_144_144_10 : ColCert where
  rK := ⟨144, by decide⟩
  rH := ⟨144, by decide⟩
  m := 5
  T1 := T144_144
  T2 := Q2.T144_144_2
  h1 := (2,0,0,0,0)
  h2 := (2,0,0,0,0)
  D := [[2, 0, 0, 0], [2, 0, 0, 0], [2, 0, 0, 0], [2, 0, 0, 0], [2, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_144_144_11 : ColCert where
  rK := ⟨144, by decide⟩
  rH := ⟨144, by decide⟩
  m := 5
  T1 := T144_144
  T2 := Q2.T144_144_2
  h1 := (2,1,3,0,2)
  h2 := (2,1,3,0,3)
  D := [[2, 1, 3, 0], [2, 1, 3, 4], [2, 1, 3, 3], [2, 1, 3, 2], [2, 1, 3, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_144_144_12 : ColCert where
  rK := ⟨144, by decide⟩
  rH := ⟨144, by decide⟩
  m := 5
  T1 := T144_144
  T2 := Q2.T144_144_2
  h1 := (2,2,1,0,2)
  h2 := (2,2,1,0,4)
  D := [[2, 2, 1, 0], [2, 2, 1, 3], [2, 2, 1, 1], [2, 2, 1, 4], [2, 2, 1, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_144_144_13 : ColCert where
  rK := ⟨144, by decide⟩
  rH := ⟨144, by decide⟩
  m := 5
  T1 := T144_144
  T2 := Q2.T144_144_2
  h1 := (2,3,4,0,0)
  h2 := (2,3,4,0,3)
  D := [[2, 3, 4, 0], [2, 3, 4, 2], [2, 3, 4, 4], [2, 3, 4, 1], [2, 3, 4, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_144_144_14 : ColCert where
  rK := ⟨144, by decide⟩
  rH := ⟨144, by decide⟩
  m := 5
  T1 := T144_144
  T2 := Q2.T144_144_2
  h1 := (2,4,2,0,1)
  h2 := (2,4,2,0,0)
  D := [[2, 4, 2, 0], [2, 4, 2, 1], [2, 4, 2, 2], [2, 4, 2, 3], [2, 4, 2, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_144_144_15 : ColCert where
  rK := ⟨144, by decide⟩
  rH := ⟨144, by decide⟩
  m := 5
  T1 := T144_144
  T2 := Q2.T144_144_2
  h1 := (3,0,0,0,0)
  h2 := (3,0,0,0,0)
  D := [[3, 0, 0, 0], [3, 0, 0, 0], [3, 0, 0, 0], [3, 0, 0, 0], [3, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_144_144_16 : ColCert where
  rK := ⟨144, by decide⟩
  rH := ⟨144, by decide⟩
  m := 5
  T1 := T144_144
  T2 := Q2.T144_144_2
  h1 := (3,1,3,0,2)
  h2 := (3,1,3,0,3)
  D := [[3, 1, 2, 3], [3, 1, 2, 2], [3, 1, 2, 1], [3, 1, 2, 0], [3, 1, 2, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_144_144_17 : ColCert where
  rK := ⟨144, by decide⟩
  rH := ⟨144, by decide⟩
  m := 5
  T1 := T144_144
  T2 := Q2.T144_144_2
  h1 := (3,2,1,0,2)
  h2 := (3,2,1,0,4)
  D := [[3, 2, 4, 1], [3, 2, 4, 4], [3, 2, 4, 2], [3, 2, 4, 0], [3, 2, 4, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_144_144_18 : ColCert where
  rK := ⟨144, by decide⟩
  rH := ⟨144, by decide⟩
  m := 5
  T1 := T144_144
  T2 := Q2.T144_144_2
  h1 := (3,3,4,0,0)
  h2 := (3,3,4,0,3)
  D := [[3, 3, 1, 4], [3, 3, 1, 1], [3, 3, 1, 3], [3, 3, 1, 0], [3, 3, 1, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_144_144_19 : ColCert where
  rK := ⟨144, by decide⟩
  rH := ⟨144, by decide⟩
  m := 5
  T1 := T144_144
  T2 := Q2.T144_144_2
  h1 := (3,4,2,0,1)
  h2 := (3,4,2,0,0)
  D := [[3, 4, 3, 2], [3, 4, 3, 3], [3, 4, 3, 4], [3, 4, 3, 0], [3, 4, 3, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_144_144_20 : ColCert where
  rK := ⟨144, by decide⟩
  rH := ⟨144, by decide⟩
  m := 5
  T1 := T144_144
  T2 := Q2.T144_144_2
  h1 := (4,0,0,0,0)
  h2 := (4,0,0,0,0)
  D := [[4, 0, 0, 0], [4, 0, 0, 0], [4, 0, 0, 0], [4, 0, 0, 0], [4, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_144_144_21 : ColCert where
  rK := ⟨144, by decide⟩
  rH := ⟨144, by decide⟩
  m := 5
  T1 := T144_144
  T2 := Q2.T144_144_2
  h1 := (4,1,3,0,2)
  h2 := (4,1,3,0,3)
  D := [[4, 1, 1, 2], [4, 1, 1, 1], [4, 1, 1, 0], [4, 1, 1, 4], [4, 1, 1, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_144_144_22 : ColCert where
  rK := ⟨144, by decide⟩
  rH := ⟨144, by decide⟩
  m := 5
  T1 := T144_144
  T2 := Q2.T144_144_2
  h1 := (4,2,1,0,2)
  h2 := (4,2,1,0,4)
  D := [[4, 2, 2, 4], [4, 2, 2, 2], [4, 2, 2, 0], [4, 2, 2, 3], [4, 2, 2, 1]]
  bind1 := by decide
  bind2 := by decide

end LeanDring.P5Presentation
