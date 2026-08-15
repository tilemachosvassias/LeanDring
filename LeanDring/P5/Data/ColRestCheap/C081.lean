/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.Twin1.ColCert
import LeanDring.P5.Data.EntryK.C037

/-!
# Species-table cell data, stage 2 — twin-coincident columns (cheap tier)

Per-column certified exponent-vector data (`ColCert`/`ColCertDiv`) with kernel
`decide` bindings. Emitted; the embedded lists are what the kernel certifies.
rest tier, chunk 80: 60 columns.
-/

-- machine-emitted data: silence style linters (generated long lines, file-level options)
set_option linter.style.longLine false

namespace LeanDring.P5Presentation

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

def colCert_137_53_0 : ColCert where
  rK := ⟨137, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T137_53
  T2 := Q2.T137_53_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_137_53_1 : ColCert where
  rK := ⟨137, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T137_53
  T2 := Q2.T137_53_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_137_53_2 : ColCert where
  rK := ⟨137, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T137_53
  T2 := Q2.T137_53_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_137_53_3 : ColCert where
  rK := ⟨137, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T137_53
  T2 := Q2.T137_53_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_137_53_4 : ColCert where
  rK := ⟨137, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T137_53
  T2 := Q2.T137_53_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_137_53_5 : ColCert where
  rK := ⟨137, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T137_53
  T2 := Q2.T137_53_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_137_53_10 : ColCert where
  rK := ⟨137, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T137_53
  T2 := Q2.T137_53_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_137_53_15 : ColCert where
  rK := ⟨137, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T137_53
  T2 := Q2.T137_53_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_137_53_20 : ColCert where
  rK := ⟨137, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T137_53
  T2 := Q2.T137_53_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_137_84_0 : ColCert where
  rK := ⟨137, by decide⟩
  rH := ⟨84, by decide⟩
  m := 5
  T1 := T137_84
  T2 := Q2.T137_84_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_137_84_1 : ColCert where
  rK := ⟨137, by decide⟩
  rH := ⟨84, by decide⟩
  m := 5
  T1 := T137_84
  T2 := Q2.T137_84_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_137_84_2 : ColCert where
  rK := ⟨137, by decide⟩
  rH := ⟨84, by decide⟩
  m := 5
  T1 := T137_84
  T2 := Q2.T137_84_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_137_84_3 : ColCert where
  rK := ⟨137, by decide⟩
  rH := ⟨84, by decide⟩
  m := 5
  T1 := T137_84
  T2 := Q2.T137_84_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_137_84_4 : ColCert where
  rK := ⟨137, by decide⟩
  rH := ⟨84, by decide⟩
  m := 5
  T1 := T137_84
  T2 := Q2.T137_84_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_137_84_5 : ColCert where
  rK := ⟨137, by decide⟩
  rH := ⟨84, by decide⟩
  m := 5
  T1 := T137_84
  T2 := Q2.T137_84_2
  h1 := (1,0,1,0,0)
  h2 := (1,0,1,0,0)
  D := [[1, 0, 1, 4], [1, 0, 1, 4], [1, 0, 1, 4], [1, 0, 1, 4], [1, 0, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_137_84_10 : ColCert where
  rK := ⟨137, by decide⟩
  rH := ⟨84, by decide⟩
  m := 5
  T1 := T137_84
  T2 := Q2.T137_84_2
  h1 := (2,0,2,0,0)
  h2 := (2,0,2,0,0)
  D := [[2, 0, 2, 2], [2, 0, 2, 2], [2, 0, 2, 2], [2, 0, 2, 2], [2, 0, 2, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_137_84_15 : ColCert where
  rK := ⟨137, by decide⟩
  rH := ⟨84, by decide⟩
  m := 5
  T1 := T137_84
  T2 := Q2.T137_84_2
  h1 := (3,0,3,0,0)
  h2 := (3,0,3,0,0)
  D := [[3, 0, 3, 4], [3, 0, 3, 4], [3, 0, 3, 4], [3, 0, 3, 4], [3, 0, 3, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_137_84_20 : ColCert where
  rK := ⟨137, by decide⟩
  rH := ⟨84, by decide⟩
  m := 5
  T1 := T137_84
  T2 := Q2.T137_84_2
  h1 := (4,0,4,0,0)
  h2 := (4,0,4,0,0)
  D := [[4, 0, 4, 0], [4, 0, 4, 0], [4, 0, 4, 0], [4, 0, 4, 0], [4, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_137_92_0 : ColCert where
  rK := ⟨137, by decide⟩
  rH := ⟨92, by decide⟩
  m := 5
  T1 := T137_92
  T2 := Q2.T137_92_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_137_92_1 : ColCert where
  rK := ⟨137, by decide⟩
  rH := ⟨92, by decide⟩
  m := 5
  T1 := T137_92
  T2 := Q2.T137_92_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_137_92_2 : ColCert where
  rK := ⟨137, by decide⟩
  rH := ⟨92, by decide⟩
  m := 5
  T1 := T137_92
  T2 := Q2.T137_92_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_137_92_3 : ColCert where
  rK := ⟨137, by decide⟩
  rH := ⟨92, by decide⟩
  m := 5
  T1 := T137_92
  T2 := Q2.T137_92_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_137_92_4 : ColCert where
  rK := ⟨137, by decide⟩
  rH := ⟨92, by decide⟩
  m := 5
  T1 := T137_92
  T2 := Q2.T137_92_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_137_92_5 : ColCert where
  rK := ⟨137, by decide⟩
  rH := ⟨92, by decide⟩
  m := 5
  T1 := T137_92
  T2 := Q2.T137_92_2
  h1 := (1,2,3,3,2)
  h2 := (1,2,3,3,2)
  D := [[1, 2, 2, 0], [1, 2, 2, 3], [1, 2, 2, 1], [1, 2, 2, 4], [1, 2, 2, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_137_92_10 : ColCert where
  rK := ⟨137, by decide⟩
  rH := ⟨92, by decide⟩
  m := 5
  T1 := T137_92
  T2 := Q2.T137_92_2
  h1 := (2,4,1,3,3)
  h2 := (2,4,1,3,3)
  D := [[2, 4, 2, 2], [2, 4, 2, 3], [2, 4, 2, 4], [2, 4, 2, 0], [2, 4, 2, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_137_99_0 : ColCert where
  rK := ⟨137, by decide⟩
  rH := ⟨99, by decide⟩
  m := 5
  T1 := T137_99
  T2 := Q2.T137_99_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_137_99_1 : ColCert where
  rK := ⟨137, by decide⟩
  rH := ⟨99, by decide⟩
  m := 5
  T1 := T137_99
  T2 := Q2.T137_99_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_137_99_2 : ColCert where
  rK := ⟨137, by decide⟩
  rH := ⟨99, by decide⟩
  m := 5
  T1 := T137_99
  T2 := Q2.T137_99_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_137_99_3 : ColCert where
  rK := ⟨137, by decide⟩
  rH := ⟨99, by decide⟩
  m := 5
  T1 := T137_99
  T2 := Q2.T137_99_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_137_99_4 : ColCert where
  rK := ⟨137, by decide⟩
  rH := ⟨99, by decide⟩
  m := 5
  T1 := T137_99
  T2 := Q2.T137_99_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_137_99_5 : ColCert where
  rK := ⟨137, by decide⟩
  rH := ⟨99, by decide⟩
  m := 5
  T1 := T137_99
  T2 := Q2.T137_99_2
  h1 := (1,1,2,0,0)
  h2 := (1,1,2,0,0)
  D := [[1, 1, 0, 3], [1, 1, 0, 2], [1, 1, 0, 1], [1, 1, 0, 0], [1, 1, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_137_99_10 : ColCert where
  rK := ⟨137, by decide⟩
  rH := ⟨99, by decide⟩
  m := 5
  T1 := T137_99
  T2 := Q2.T137_99_2
  h1 := (2,2,4,1,2)
  h2 := (2,2,4,1,2)
  D := [[2, 2, 4, 3], [2, 2, 4, 1], [2, 2, 4, 4], [2, 2, 4, 2], [2, 2, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_137_99_15 : ColCert where
  rK := ⟨137, by decide⟩
  rH := ⟨99, by decide⟩
  m := 5
  T1 := T137_99
  T2 := Q2.T137_99_2
  h1 := (3,3,1,3,2)
  h2 := (3,3,1,3,2)
  D := [[3, 3, 2, 1], [3, 3, 2, 3], [3, 3, 2, 0], [3, 3, 2, 2], [3, 3, 2, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_137_99_20 : ColCert where
  rK := ⟨137, by decide⟩
  rH := ⟨99, by decide⟩
  m := 5
  T1 := T137_99
  T2 := Q2.T137_99_2
  h1 := (4,4,3,1,1)
  h2 := (4,4,3,1,1)
  D := [[4, 4, 4, 3], [4, 4, 4, 4], [4, 4, 4, 0], [4, 4, 4, 1], [4, 4, 4, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_137_103_0 : ColCert where
  rK := ⟨137, by decide⟩
  rH := ⟨103, by decide⟩
  m := 5
  T1 := T137_103
  T2 := Q2.T137_103_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_137_103_1 : ColCert where
  rK := ⟨137, by decide⟩
  rH := ⟨103, by decide⟩
  m := 5
  T1 := T137_103
  T2 := Q2.T137_103_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_137_103_2 : ColCert where
  rK := ⟨137, by decide⟩
  rH := ⟨103, by decide⟩
  m := 5
  T1 := T137_103
  T2 := Q2.T137_103_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_137_103_3 : ColCert where
  rK := ⟨137, by decide⟩
  rH := ⟨103, by decide⟩
  m := 5
  T1 := T137_103
  T2 := Q2.T137_103_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_137_103_4 : ColCert where
  rK := ⟨137, by decide⟩
  rH := ⟨103, by decide⟩
  m := 5
  T1 := T137_103
  T2 := Q2.T137_103_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_137_103_5 : ColCert where
  rK := ⟨137, by decide⟩
  rH := ⟨103, by decide⟩
  m := 5
  T1 := T137_103
  T2 := Q2.T137_103_2
  h1 := (1,3,4,1,1)
  h2 := (1,3,4,1,1)
  D := [[1, 3, 4, 3], [1, 3, 4, 0], [1, 3, 4, 2], [1, 3, 4, 4], [1, 3, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_137_105_0 : ColCert where
  rK := ⟨137, by decide⟩
  rH := ⟨105, by decide⟩
  m := 5
  T1 := T137_105
  T2 := Q2.T137_105_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_137_105_1 : ColCert where
  rK := ⟨137, by decide⟩
  rH := ⟨105, by decide⟩
  m := 5
  T1 := T137_105
  T2 := Q2.T137_105_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_137_105_2 : ColCert where
  rK := ⟨137, by decide⟩
  rH := ⟨105, by decide⟩
  m := 5
  T1 := T137_105
  T2 := Q2.T137_105_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_137_105_3 : ColCert where
  rK := ⟨137, by decide⟩
  rH := ⟨105, by decide⟩
  m := 5
  T1 := T137_105
  T2 := Q2.T137_105_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_137_105_4 : ColCert where
  rK := ⟨137, by decide⟩
  rH := ⟨105, by decide⟩
  m := 5
  T1 := T137_105
  T2 := Q2.T137_105_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_137_105_5 : ColCert where
  rK := ⟨137, by decide⟩
  rH := ⟨105, by decide⟩
  m := 5
  T1 := T137_105
  T2 := Q2.T137_105_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_137_105_10 : ColCert where
  rK := ⟨137, by decide⟩
  rH := ⟨105, by decide⟩
  m := 5
  T1 := T137_105
  T2 := Q2.T137_105_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_137_105_15 : ColCert where
  rK := ⟨137, by decide⟩
  rH := ⟨105, by decide⟩
  m := 5
  T1 := T137_105
  T2 := Q2.T137_105_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_137_105_20 : ColCert where
  rK := ⟨137, by decide⟩
  rH := ⟨105, by decide⟩
  m := 5
  T1 := T137_105
  T2 := Q2.T137_105_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_137_105_25 : ColCert where
  rK := ⟨137, by decide⟩
  rH := ⟨105, by decide⟩
  m := 5
  T1 := T137_105
  T2 := Q2.T137_105_2
  h1 := (0,1,1,0,0)
  h2 := (0,1,1,0,0)
  D := [[0, 1, 0, 3], [0, 1, 0, 2], [0, 1, 0, 1], [0, 1, 0, 0], [0, 1, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_137_105_50 : ColCert where
  rK := ⟨137, by decide⟩
  rH := ⟨105, by decide⟩
  m := 5
  T1 := T137_105
  T2 := Q2.T137_105_2
  h1 := (0,2,2,0,1)
  h2 := (0,2,2,0,1)
  D := [[0, 2, 0, 1], [0, 2, 0, 4], [0, 2, 0, 2], [0, 2, 0, 0], [0, 2, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_137_105_75 : ColCert where
  rK := ⟨137, by decide⟩
  rH := ⟨105, by decide⟩
  m := 5
  T1 := T137_105
  T2 := Q2.T137_105_2
  h1 := (0,3,3,0,3)
  h2 := (0,3,3,0,3)
  D := [[0, 3, 0, 4], [0, 3, 0, 1], [0, 3, 0, 3], [0, 3, 0, 0], [0, 3, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_137_105_100 : ColCert where
  rK := ⟨137, by decide⟩
  rH := ⟨105, by decide⟩
  m := 5
  T1 := T137_105
  T2 := Q2.T137_105_2
  h1 := (0,4,4,0,1)
  h2 := (0,4,4,0,1)
  D := [[0, 4, 0, 2], [0, 4, 0, 3], [0, 4, 0, 4], [0, 4, 0, 0], [0, 4, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_137_111_0 : ColCert where
  rK := ⟨137, by decide⟩
  rH := ⟨111, by decide⟩
  m := 5
  T1 := T137_111
  T2 := Q2.T137_111_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_137_111_1 : ColCert where
  rK := ⟨137, by decide⟩
  rH := ⟨111, by decide⟩
  m := 5
  T1 := T137_111
  T2 := Q2.T137_111_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_137_111_2 : ColCert where
  rK := ⟨137, by decide⟩
  rH := ⟨111, by decide⟩
  m := 5
  T1 := T137_111
  T2 := Q2.T137_111_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_137_111_3 : ColCert where
  rK := ⟨137, by decide⟩
  rH := ⟨111, by decide⟩
  m := 5
  T1 := T137_111
  T2 := Q2.T137_111_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_137_111_4 : ColCert where
  rK := ⟨137, by decide⟩
  rH := ⟨111, by decide⟩
  m := 5
  T1 := T137_111
  T2 := Q2.T137_111_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_137_111_5 : ColCert where
  rK := ⟨137, by decide⟩
  rH := ⟨111, by decide⟩
  m := 5
  T1 := T137_111
  T2 := Q2.T137_111_2
  h1 := (1,4,0,4,0)
  h2 := (1,4,0,4,0)
  D := [[1, 4, 1, 0], [1, 4, 1, 1], [1, 4, 1, 2], [1, 4, 1, 3], [1, 4, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_137_137_0 : ColCert where
  rK := ⟨137, by decide⟩
  rH := ⟨137, by decide⟩
  m := 5
  T1 := T137_137
  T2 := Q2.T137_137_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

end LeanDring.P5Presentation
