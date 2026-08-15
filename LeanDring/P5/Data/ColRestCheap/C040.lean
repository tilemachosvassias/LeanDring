/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.Twin1.ColCert
import LeanDring.P5.Data.EntryK.C028

/-!
# Species-table cell data, stage 2 — twin-coincident columns (cheap tier)

Per-column certified exponent-vector data (`ColCert`/`ColCertDiv`) with kernel
`decide` bindings. Emitted; the embedded lists are what the kernel certifies.
rest tier, chunk 39: 60 columns.
-/

-- machine-emitted data: silence style linters (generated long lines, file-level options)
set_option linter.style.longLine false

namespace LeanDring.P5Presentation

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

def colCert_119_93_0 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨93, by decide⟩
  m := 5
  T1 := T119_93
  T2 := Q2.T119_93_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_93_1 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨93, by decide⟩
  m := 5
  T1 := T119_93
  T2 := Q2.T119_93_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_93_2 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨93, by decide⟩
  m := 5
  T1 := T119_93
  T2 := Q2.T119_93_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_93_3 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨93, by decide⟩
  m := 5
  T1 := T119_93
  T2 := Q2.T119_93_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_93_4 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨93, by decide⟩
  m := 5
  T1 := T119_93
  T2 := Q2.T119_93_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_93_5 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨93, by decide⟩
  m := 5
  T1 := T119_93
  T2 := Q2.T119_93_2
  h1 := (1,3,2,1,4)
  h2 := (1,3,2,1,4)
  D := [[1, 2, 2, 0], [1, 2, 1, 3], [1, 2, 0, 1], [1, 2, 4, 4], [1, 2, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_93_10 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨93, by decide⟩
  m := 5
  T1 := T119_93
  T2 := Q2.T119_93_2
  h1 := (2,1,4,0,1)
  h2 := (2,1,4,0,2)
  D := [[2, 4, 4, 2], [2, 4, 2, 4], [2, 4, 0, 1], [2, 4, 3, 3], [2, 4, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_93_15 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨93, by decide⟩
  m := 5
  T1 := T119_93
  T2 := Q2.T119_93_2
  h1 := (3,4,1,2,2)
  h2 := (3,4,1,2,3)
  D := [[3, 1, 1, 1], [3, 1, 3, 3], [3, 1, 0, 0], [3, 1, 2, 2], [3, 1, 4, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_93_20 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨93, by decide⟩
  m := 5
  T1 := T119_93
  T2 := Q2.T119_93_2
  h1 := (4,2,3,2,2)
  h2 := (4,2,3,2,4)
  D := [[4, 3, 3, 2], [4, 3, 4, 0], [4, 3, 0, 3], [4, 3, 1, 1], [4, 3, 2, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_98_0 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨98, by decide⟩
  m := 5
  T1 := T119_98
  T2 := Q2.T119_98_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_98_1 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨98, by decide⟩
  m := 5
  T1 := T119_98
  T2 := Q2.T119_98_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_98_2 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨98, by decide⟩
  m := 5
  T1 := T119_98
  T2 := Q2.T119_98_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_98_3 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨98, by decide⟩
  m := 5
  T1 := T119_98
  T2 := Q2.T119_98_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_98_4 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨98, by decide⟩
  m := 5
  T1 := T119_98
  T2 := Q2.T119_98_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_98_5 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨98, by decide⟩
  m := 5
  T1 := T119_98
  T2 := Q2.T119_98_2
  h1 := (1,3,1,1,3)
  h2 := (1,3,1,1,3)
  D := [[1, 1, 2, 4], [1, 1, 1, 1], [1, 1, 0, 3], [1, 1, 4, 0], [1, 1, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_98_10 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨98, by decide⟩
  m := 5
  T1 := T119_98
  T2 := Q2.T119_98_2
  h1 := (2,1,2,0,1)
  h2 := (2,1,2,0,2)
  D := [[2, 2, 4, 3], [2, 2, 2, 3], [2, 2, 0, 3], [2, 2, 3, 3], [2, 2, 1, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_98_15 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨98, by decide⟩
  m := 5
  T1 := T119_98
  T2 := Q2.T119_98_2
  h1 := (3,4,3,2,0)
  h2 := (3,4,3,2,1)
  D := [[3, 3, 1, 2], [3, 3, 3, 1], [3, 3, 0, 0], [3, 3, 2, 4], [3, 3, 4, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_98_20 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨98, by decide⟩
  m := 5
  T1 := T119_98
  T2 := Q2.T119_98_2
  h1 := (4,2,4,2,0)
  h2 := (4,2,4,2,2)
  D := [[4, 4, 3, 1], [4, 4, 4, 0], [4, 4, 0, 4], [4, 4, 1, 3], [4, 4, 2, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_103_0 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨103, by decide⟩
  m := 5
  T1 := T119_103
  T2 := Q2.T119_103_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_103_1 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨103, by decide⟩
  m := 5
  T1 := T119_103
  T2 := Q2.T119_103_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_103_2 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨103, by decide⟩
  m := 5
  T1 := T119_103
  T2 := Q2.T119_103_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_103_3 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨103, by decide⟩
  m := 5
  T1 := T119_103
  T2 := Q2.T119_103_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_103_4 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨103, by decide⟩
  m := 5
  T1 := T119_103
  T2 := Q2.T119_103_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_103_5 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨103, by decide⟩
  m := 5
  T1 := T119_103
  T2 := Q2.T119_103_2
  h1 := (1,3,4,1,1)
  h2 := (1,3,4,1,1)
  D := [[1, 4, 2, 2], [1, 4, 1, 2], [1, 4, 0, 2], [1, 4, 4, 2], [1, 4, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_103_10 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨103, by decide⟩
  m := 5
  T1 := T119_103
  T2 := Q2.T119_103_2
  h1 := (2,1,3,0,1)
  h2 := (2,1,3,0,2)
  D := [[2, 3, 4, 0], [2, 3, 2, 1], [2, 3, 0, 2], [2, 3, 3, 3], [2, 3, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_103_15 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨103, by decide⟩
  m := 5
  T1 := T119_103
  T2 := Q2.T119_103_2
  h1 := (3,4,2,2,1)
  h2 := (3,4,2,2,2)
  D := [[3, 2, 1, 4], [3, 2, 3, 2], [3, 2, 0, 0], [3, 2, 2, 3], [3, 2, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_103_20 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨103, by decide⟩
  m := 5
  T1 := T119_103
  T2 := Q2.T119_103_2
  h1 := (4,2,1,2,1)
  h2 := (4,2,1,2,3)
  D := [[4, 1, 3, 4], [4, 1, 4, 0], [4, 1, 0, 1], [4, 1, 1, 2], [4, 1, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_108_0 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨108, by decide⟩
  m := 5
  T1 := T119_108
  T2 := Q2.T119_108_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_108_1 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨108, by decide⟩
  m := 5
  T1 := T119_108
  T2 := Q2.T119_108_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_108_2 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨108, by decide⟩
  m := 5
  T1 := T119_108
  T2 := Q2.T119_108_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_108_3 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨108, by decide⟩
  m := 5
  T1 := T119_108
  T2 := Q2.T119_108_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_108_4 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨108, by decide⟩
  m := 5
  T1 := T119_108
  T2 := Q2.T119_108_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_108_5 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨108, by decide⟩
  m := 5
  T1 := T119_108
  T2 := Q2.T119_108_2
  h1 := (1,3,3,1,0)
  h2 := (1,3,3,1,0)
  D := [[1, 3, 2, 1], [1, 3, 1, 0], [1, 3, 0, 4], [1, 3, 4, 3], [1, 3, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_108_10 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨108, by decide⟩
  m := 5
  T1 := T119_108
  T2 := Q2.T119_108_2
  h1 := (2,1,1,0,1)
  h2 := (2,1,1,0,2)
  D := [[2, 1, 4, 1], [2, 1, 2, 0], [2, 1, 0, 4], [2, 1, 3, 3], [2, 1, 1, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_108_15 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨108, by decide⟩
  m := 5
  T1 := T119_108
  T2 := Q2.T119_108_2
  h1 := (3,4,4,2,4)
  h2 := (3,4,4,2,0)
  D := [[3, 4, 1, 0], [3, 4, 3, 0], [3, 4, 0, 0], [3, 4, 2, 0], [3, 4, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_108_20 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨108, by decide⟩
  m := 5
  T1 := T119_108
  T2 := Q2.T119_108_2
  h1 := (4,2,2,2,4)
  h2 := (4,2,2,2,1)
  D := [[4, 2, 3, 3], [4, 2, 4, 0], [4, 2, 0, 2], [4, 2, 1, 4], [4, 2, 2, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_113_0 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨113, by decide⟩
  m := 5
  T1 := T119_113
  T2 := Q2.T119_113_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_113_1 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨113, by decide⟩
  m := 5
  T1 := T119_113
  T2 := Q2.T119_113_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_113_2 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨113, by decide⟩
  m := 5
  T1 := T119_113
  T2 := Q2.T119_113_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_113_3 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨113, by decide⟩
  m := 5
  T1 := T119_113
  T2 := Q2.T119_113_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_113_4 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨113, by decide⟩
  m := 5
  T1 := T119_113
  T2 := Q2.T119_113_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_113_5 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨113, by decide⟩
  m := 5
  T1 := T119_113
  T2 := Q2.T119_113_2
  h1 := (1,3,0,1,2)
  h2 := (1,3,0,1,2)
  D := [[1, 0, 2, 3], [1, 0, 1, 4], [1, 0, 0, 0], [1, 0, 4, 1], [1, 0, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_113_10 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨113, by decide⟩
  m := 5
  T1 := T119_113
  T2 := Q2.T119_113_2
  h1 := (2,1,0,0,1)
  h2 := (2,1,0,0,2)
  D := [[2, 0, 4, 4], [2, 0, 2, 2], [2, 0, 0, 0], [2, 0, 3, 3], [2, 0, 1, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_113_15 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨113, by decide⟩
  m := 5
  T1 := T119_113
  T2 := Q2.T119_113_2
  h1 := (3,4,0,2,3)
  h2 := (3,4,0,2,4)
  D := [[3, 0, 1, 3], [3, 0, 3, 4], [3, 0, 0, 0], [3, 0, 2, 1], [3, 0, 4, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_113_20 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨113, by decide⟩
  m := 5
  T1 := T119_113
  T2 := Q2.T119_113_2
  h1 := (4,2,0,2,3)
  h2 := (4,2,0,2,0)
  D := [[4, 0, 3, 0], [4, 0, 4, 0], [4, 0, 0, 0], [4, 0, 1, 0], [4, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_119_0 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨119, by decide⟩
  m := 5
  T1 := T119_119
  T2 := Q2.T119_119_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_119_1 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨119, by decide⟩
  m := 5
  T1 := T119_119
  T2 := Q2.T119_119_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_119_2 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨119, by decide⟩
  m := 5
  T1 := T119_119
  T2 := Q2.T119_119_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_119_3 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨119, by decide⟩
  m := 5
  T1 := T119_119
  T2 := Q2.T119_119_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_119_4 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨119, by decide⟩
  m := 5
  T1 := T119_119
  T2 := Q2.T119_119_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_119_5 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨119, by decide⟩
  m := 5
  T1 := T119_119
  T2 := Q2.T119_119_2
  h1 := (0,0,1,0,0)
  h2 := (0,0,1,0,0)
  D := [[0, 1, 0, 3], [0, 1, 0, 4], [0, 1, 0, 0], [0, 1, 0, 1], [0, 1, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_119_6 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨119, by decide⟩
  m := 5
  T1 := T119_119
  T2 := Q2.T119_119_2
  h1 := (0,0,1,1,0)
  h2 := (0,0,1,1,0)
  D := [[0, 1, 1, 3], [0, 1, 1, 4], [0, 1, 1, 0], [0, 1, 1, 1], [0, 1, 1, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_119_7 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨119, by decide⟩
  m := 5
  T1 := T119_119
  T2 := Q2.T119_119_2
  h1 := (0,0,1,2,0)
  h2 := (0,0,1,2,0)
  D := [[0, 1, 2, 3], [0, 1, 2, 4], [0, 1, 2, 0], [0, 1, 2, 1], [0, 1, 2, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_119_8 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨119, by decide⟩
  m := 5
  T1 := T119_119
  T2 := Q2.T119_119_2
  h1 := (0,0,1,3,0)
  h2 := (0,0,1,3,0)
  D := [[0, 1, 3, 3], [0, 1, 3, 4], [0, 1, 3, 0], [0, 1, 3, 1], [0, 1, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_119_9 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨119, by decide⟩
  m := 5
  T1 := T119_119
  T2 := Q2.T119_119_2
  h1 := (0,0,1,4,0)
  h2 := (0,0,1,4,0)
  D := [[0, 1, 4, 3], [0, 1, 4, 4], [0, 1, 4, 0], [0, 1, 4, 1], [0, 1, 4, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_119_10 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨119, by decide⟩
  m := 5
  T1 := T119_119
  T2 := Q2.T119_119_2
  h1 := (0,0,2,0,0)
  h2 := (0,0,2,0,0)
  D := [[0, 2, 0, 1], [0, 2, 0, 3], [0, 2, 0, 0], [0, 2, 0, 2], [0, 2, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_119_11 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨119, by decide⟩
  m := 5
  T1 := T119_119
  T2 := Q2.T119_119_2
  h1 := (0,0,2,1,0)
  h2 := (0,0,2,1,0)
  D := [[0, 2, 1, 1], [0, 2, 1, 3], [0, 2, 1, 0], [0, 2, 1, 2], [0, 2, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_119_12 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨119, by decide⟩
  m := 5
  T1 := T119_119
  T2 := Q2.T119_119_2
  h1 := (0,0,2,2,0)
  h2 := (0,0,2,2,0)
  D := [[0, 2, 2, 1], [0, 2, 2, 3], [0, 2, 2, 0], [0, 2, 2, 2], [0, 2, 2, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_119_13 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨119, by decide⟩
  m := 5
  T1 := T119_119
  T2 := Q2.T119_119_2
  h1 := (0,0,2,3,0)
  h2 := (0,0,2,3,0)
  D := [[0, 2, 3, 1], [0, 2, 3, 3], [0, 2, 3, 0], [0, 2, 3, 2], [0, 2, 3, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_119_119_14 : ColCert where
  rK := ⟨119, by decide⟩
  rH := ⟨119, by decide⟩
  m := 5
  T1 := T119_119
  T2 := Q2.T119_119_2
  h1 := (0,0,2,4,0)
  h2 := (0,0,2,4,0)
  D := [[0, 2, 4, 1], [0, 2, 4, 3], [0, 2, 4, 0], [0, 2, 4, 2], [0, 2, 4, 4]]
  bind1 := by decide
  bind2 := by decide

end LeanDring.P5Presentation
