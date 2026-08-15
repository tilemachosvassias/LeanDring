/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.Twin1.ColCert
import LeanDring.P5.Data.EntryK.C041
import LeanDring.P5.Data.EntryK.C042

/-!
# Species-table cell data, stage 2 — twin-coincident columns (cheap tier)

Per-column certified exponent-vector data (`ColCert`/`ColCertDiv`) with kernel
`decide` bindings. Emitted; the embedded lists are what the kernel certifies.
rest tier, chunk 100: 60 columns.
-/

-- machine-emitted data: silence style linters (generated long lines, file-level options)
set_option linter.style.longLine false

namespace LeanDring.P5Presentation

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

def colCert_143_97_0 : ColCert where
  rK := ⟨143, by decide⟩
  rH := ⟨97, by decide⟩
  m := 5
  T1 := T143_97
  T2 := Q2.T143_97_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_143_97_1 : ColCert where
  rK := ⟨143, by decide⟩
  rH := ⟨97, by decide⟩
  m := 5
  T1 := T143_97
  T2 := Q2.T143_97_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_143_97_2 : ColCert where
  rK := ⟨143, by decide⟩
  rH := ⟨97, by decide⟩
  m := 5
  T1 := T143_97
  T2 := Q2.T143_97_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_143_97_3 : ColCert where
  rK := ⟨143, by decide⟩
  rH := ⟨97, by decide⟩
  m := 5
  T1 := T143_97
  T2 := Q2.T143_97_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_143_97_4 : ColCert where
  rK := ⟨143, by decide⟩
  rH := ⟨97, by decide⟩
  m := 5
  T1 := T143_97
  T2 := Q2.T143_97_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_143_97_15 : ColCert where
  rK := ⟨143, by decide⟩
  rH := ⟨97, by decide⟩
  m := 5
  T1 := T143_97
  T2 := Q2.T143_97_2
  h1 := (3,1,2,0,1)
  h2 := (3,1,2,0,2)
  D := [[3, 1, 2, 1], [3, 1, 2, 0], [3, 1, 2, 4], [3, 1, 2, 3], [3, 1, 2, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_143_98_0 : ColCert where
  rK := ⟨143, by decide⟩
  rH := ⟨98, by decide⟩
  m := 5
  T1 := T143_98
  T2 := Q2.T143_98_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_143_98_1 : ColCert where
  rK := ⟨143, by decide⟩
  rH := ⟨98, by decide⟩
  m := 5
  T1 := T143_98
  T2 := Q2.T143_98_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_143_98_2 : ColCert where
  rK := ⟨143, by decide⟩
  rH := ⟨98, by decide⟩
  m := 5
  T1 := T143_98
  T2 := Q2.T143_98_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_143_98_3 : ColCert where
  rK := ⟨143, by decide⟩
  rH := ⟨98, by decide⟩
  m := 5
  T1 := T143_98
  T2 := Q2.T143_98_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_143_98_4 : ColCert where
  rK := ⟨143, by decide⟩
  rH := ⟨98, by decide⟩
  m := 5
  T1 := T143_98
  T2 := Q2.T143_98_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_143_98_10 : ColCert where
  rK := ⟨143, by decide⟩
  rH := ⟨98, by decide⟩
  m := 5
  T1 := T143_98
  T2 := Q2.T143_98_2
  h1 := (2,1,2,0,1)
  h2 := (2,1,2,0,2)
  D := [[2, 1, 3, 3], [2, 1, 3, 2], [2, 1, 3, 1], [2, 1, 3, 0], [2, 1, 3, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_143_98_20 : ColCert where
  rK := ⟨143, by decide⟩
  rH := ⟨98, by decide⟩
  m := 5
  T1 := T143_98
  T2 := Q2.T143_98_2
  h1 := (4,2,4,2,0)
  h2 := (4,2,4,2,2)
  D := [[4, 2, 4, 3], [4, 2, 4, 1], [4, 2, 4, 4], [4, 2, 4, 2], [4, 2, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_143_99_0 : ColCert where
  rK := ⟨143, by decide⟩
  rH := ⟨99, by decide⟩
  m := 5
  T1 := T143_99
  T2 := Q2.T143_99_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_143_99_1 : ColCert where
  rK := ⟨143, by decide⟩
  rH := ⟨99, by decide⟩
  m := 5
  T1 := T143_99
  T2 := Q2.T143_99_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_143_99_2 : ColCert where
  rK := ⟨143, by decide⟩
  rH := ⟨99, by decide⟩
  m := 5
  T1 := T143_99
  T2 := Q2.T143_99_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_143_99_3 : ColCert where
  rK := ⟨143, by decide⟩
  rH := ⟨99, by decide⟩
  m := 5
  T1 := T143_99
  T2 := Q2.T143_99_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_143_99_4 : ColCert where
  rK := ⟨143, by decide⟩
  rH := ⟨99, by decide⟩
  m := 5
  T1 := T143_99
  T2 := Q2.T143_99_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_143_115_0 : ColCert where
  rK := ⟨143, by decide⟩
  rH := ⟨115, by decide⟩
  m := 5
  T1 := T143_115
  T2 := Q2.T143_115_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_143_115_1 : ColCert where
  rK := ⟨143, by decide⟩
  rH := ⟨115, by decide⟩
  m := 5
  T1 := T143_115
  T2 := Q2.T143_115_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_143_115_2 : ColCert where
  rK := ⟨143, by decide⟩
  rH := ⟨115, by decide⟩
  m := 5
  T1 := T143_115
  T2 := Q2.T143_115_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_143_115_3 : ColCert where
  rK := ⟨143, by decide⟩
  rH := ⟨115, by decide⟩
  m := 5
  T1 := T143_115
  T2 := Q2.T143_115_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_143_115_4 : ColCert where
  rK := ⟨143, by decide⟩
  rH := ⟨115, by decide⟩
  m := 5
  T1 := T143_115
  T2 := Q2.T143_115_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_143_115_5 : ColCert where
  rK := ⟨143, by decide⟩
  rH := ⟨115, by decide⟩
  m := 5
  T1 := T143_115
  T2 := Q2.T143_115_2
  h1 := (1,0,0,0,0)
  h2 := (1,0,0,0,0)
  D := [[1, 0, 0, 0], [1, 0, 0, 0], [1, 0, 0, 0], [1, 0, 0, 0], [1, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_143_115_10 : ColCert where
  rK := ⟨143, by decide⟩
  rH := ⟨115, by decide⟩
  m := 5
  T1 := T143_115
  T2 := Q2.T143_115_2
  h1 := (2,0,0,0,0)
  h2 := (2,0,0,0,0)
  D := [[2, 0, 0, 0], [2, 0, 0, 0], [2, 0, 0, 0], [2, 0, 0, 0], [2, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_143_115_15 : ColCert where
  rK := ⟨143, by decide⟩
  rH := ⟨115, by decide⟩
  m := 5
  T1 := T143_115
  T2 := Q2.T143_115_2
  h1 := (3,0,0,0,0)
  h2 := (3,0,0,0,0)
  D := [[3, 0, 0, 0], [3, 0, 0, 0], [3, 0, 0, 0], [3, 0, 0, 0], [3, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_143_115_20 : ColCert where
  rK := ⟨143, by decide⟩
  rH := ⟨115, by decide⟩
  m := 5
  T1 := T143_115
  T2 := Q2.T143_115_2
  h1 := (4,0,0,0,0)
  h2 := (4,0,0,0,0)
  D := [[4, 0, 0, 0], [4, 0, 0, 0], [4, 0, 0, 0], [4, 0, 0, 0], [4, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_143_143_0 : ColCert where
  rK := ⟨143, by decide⟩
  rH := ⟨143, by decide⟩
  m := 5
  T1 := T143_143
  T2 := Q2.T143_143_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_143_143_1 : ColCert where
  rK := ⟨143, by decide⟩
  rH := ⟨143, by decide⟩
  m := 5
  T1 := T143_143
  T2 := Q2.T143_143_2
  h1 := (0,1,2,0,4)
  h2 := (0,1,2,0,0)
  D := [[0, 1, 0, 3], [0, 1, 0, 2], [0, 1, 0, 1], [0, 1, 0, 0], [0, 1, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_143_143_2 : ColCert where
  rK := ⟨143, by decide⟩
  rH := ⟨143, by decide⟩
  m := 5
  T1 := T143_143
  T2 := Q2.T143_143_2
  h1 := (0,2,4,0,0)
  h2 := (0,2,4,0,2)
  D := [[0, 2, 0, 1], [0, 2, 0, 4], [0, 2, 0, 2], [0, 2, 0, 0], [0, 2, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_143_143_3 : ColCert where
  rK := ⟨143, by decide⟩
  rH := ⟨143, by decide⟩
  m := 5
  T1 := T143_143
  T2 := Q2.T143_143_2
  h1 := (0,3,1,0,3)
  h2 := (0,3,1,0,1)
  D := [[0, 3, 0, 4], [0, 3, 0, 1], [0, 3, 0, 3], [0, 3, 0, 0], [0, 3, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_143_143_4 : ColCert where
  rK := ⟨143, by decide⟩
  rH := ⟨143, by decide⟩
  m := 5
  T1 := T143_143
  T2 := Q2.T143_143_2
  h1 := (0,4,3,0,3)
  h2 := (0,4,3,0,2)
  D := [[0, 4, 0, 2], [0, 4, 0, 3], [0, 4, 0, 4], [0, 4, 0, 0], [0, 4, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_143_143_5 : ColCert where
  rK := ⟨143, by decide⟩
  rH := ⟨143, by decide⟩
  m := 5
  T1 := T143_143
  T2 := Q2.T143_143_2
  h1 := (1,0,0,0,0)
  h2 := (1,0,0,0,0)
  D := [[1, 0, 0, 0], [1, 0, 0, 0], [1, 0, 0, 0], [1, 0, 0, 0], [1, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_143_143_6 : ColCert where
  rK := ⟨143, by decide⟩
  rH := ⟨143, by decide⟩
  m := 5
  T1 := T143_143
  T2 := Q2.T143_143_2
  h1 := (1,1,2,0,4)
  h2 := (1,1,2,0,0)
  D := [[1, 1, 4, 4], [1, 1, 4, 3], [1, 1, 4, 2], [1, 1, 4, 1], [1, 1, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_143_143_7 : ColCert where
  rK := ⟨143, by decide⟩
  rH := ⟨143, by decide⟩
  m := 5
  T1 := T143_143
  T2 := Q2.T143_143_2
  h1 := (1,2,4,0,0)
  h2 := (1,2,4,0,2)
  D := [[1, 2, 3, 3], [1, 2, 3, 1], [1, 2, 3, 4], [1, 2, 3, 2], [1, 2, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_143_143_8 : ColCert where
  rK := ⟨143, by decide⟩
  rH := ⟨143, by decide⟩
  m := 5
  T1 := T143_143
  T2 := Q2.T143_143_2
  h1 := (1,3,1,0,3)
  h2 := (1,3,1,0,1)
  D := [[1, 3, 2, 2], [1, 3, 2, 4], [1, 3, 2, 1], [1, 3, 2, 3], [1, 3, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_143_143_9 : ColCert where
  rK := ⟨143, by decide⟩
  rH := ⟨143, by decide⟩
  m := 5
  T1 := T143_143
  T2 := Q2.T143_143_2
  h1 := (1,4,3,0,3)
  h2 := (1,4,3,0,2)
  D := [[1, 4, 1, 1], [1, 4, 1, 2], [1, 4, 1, 3], [1, 4, 1, 4], [1, 4, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_143_143_10 : ColCert where
  rK := ⟨143, by decide⟩
  rH := ⟨143, by decide⟩
  m := 5
  T1 := T143_143
  T2 := Q2.T143_143_2
  h1 := (2,0,0,0,0)
  h2 := (2,0,0,0,0)
  D := [[2, 0, 0, 0], [2, 0, 0, 0], [2, 0, 0, 0], [2, 0, 0, 0], [2, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_143_143_11 : ColCert where
  rK := ⟨143, by decide⟩
  rH := ⟨143, by decide⟩
  m := 5
  T1 := T143_143
  T2 := Q2.T143_143_2
  h1 := (2,1,2,0,4)
  h2 := (2,1,2,0,0)
  D := [[2, 1, 3, 1], [2, 1, 3, 0], [2, 1, 3, 4], [2, 1, 3, 3], [2, 1, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_143_143_12 : ColCert where
  rK := ⟨143, by decide⟩
  rH := ⟨143, by decide⟩
  m := 5
  T1 := T143_143
  T2 := Q2.T143_143_2
  h1 := (2,2,4,0,0)
  h2 := (2,2,4,0,2)
  D := [[2, 2, 1, 2], [2, 2, 1, 0], [2, 2, 1, 3], [2, 2, 1, 1], [2, 2, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_143_143_13 : ColCert where
  rK := ⟨143, by decide⟩
  rH := ⟨143, by decide⟩
  m := 5
  T1 := T143_143
  T2 := Q2.T143_143_2
  h1 := (2,3,1,0,3)
  h2 := (2,3,1,0,1)
  D := [[2, 3, 4, 3], [2, 3, 4, 0], [2, 3, 4, 2], [2, 3, 4, 4], [2, 3, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_143_143_14 : ColCert where
  rK := ⟨143, by decide⟩
  rH := ⟨143, by decide⟩
  m := 5
  T1 := T143_143
  T2 := Q2.T143_143_2
  h1 := (2,4,3,0,3)
  h2 := (2,4,3,0,2)
  D := [[2, 4, 2, 4], [2, 4, 2, 0], [2, 4, 2, 1], [2, 4, 2, 2], [2, 4, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_143_143_15 : ColCert where
  rK := ⟨143, by decide⟩
  rH := ⟨143, by decide⟩
  m := 5
  T1 := T143_143
  T2 := Q2.T143_143_2
  h1 := (3,0,0,0,0)
  h2 := (3,0,0,0,0)
  D := [[3, 0, 0, 0], [3, 0, 0, 0], [3, 0, 0, 0], [3, 0, 0, 0], [3, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_143_143_16 : ColCert where
  rK := ⟨143, by decide⟩
  rH := ⟨143, by decide⟩
  m := 5
  T1 := T143_143
  T2 := Q2.T143_143_2
  h1 := (3,1,2,0,4)
  h2 := (3,1,2,0,0)
  D := [[3, 1, 2, 4], [3, 1, 2, 3], [3, 1, 2, 2], [3, 1, 2, 1], [3, 1, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_143_143_17 : ColCert where
  rK := ⟨143, by decide⟩
  rH := ⟨143, by decide⟩
  m := 5
  T1 := T143_143
  T2 := Q2.T143_143_2
  h1 := (3,2,4,0,0)
  h2 := (3,2,4,0,2)
  D := [[3, 2, 4, 3], [3, 2, 4, 1], [3, 2, 4, 4], [3, 2, 4, 2], [3, 2, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_143_143_18 : ColCert where
  rK := ⟨143, by decide⟩
  rH := ⟨143, by decide⟩
  m := 5
  T1 := T143_143
  T2 := Q2.T143_143_2
  h1 := (3,3,1,0,3)
  h2 := (3,3,1,0,1)
  D := [[3, 3, 1, 2], [3, 3, 1, 4], [3, 3, 1, 1], [3, 3, 1, 3], [3, 3, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_143_143_19 : ColCert where
  rK := ⟨143, by decide⟩
  rH := ⟨143, by decide⟩
  m := 5
  T1 := T143_143
  T2 := Q2.T143_143_2
  h1 := (3,4,3,0,3)
  h2 := (3,4,3,0,2)
  D := [[3, 4, 3, 1], [3, 4, 3, 2], [3, 4, 3, 3], [3, 4, 3, 4], [3, 4, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_143_143_20 : ColCert where
  rK := ⟨143, by decide⟩
  rH := ⟨143, by decide⟩
  m := 5
  T1 := T143_143
  T2 := Q2.T143_143_2
  h1 := (4,0,0,0,0)
  h2 := (4,0,0,0,0)
  D := [[4, 0, 0, 0], [4, 0, 0, 0], [4, 0, 0, 0], [4, 0, 0, 0], [4, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_143_143_21 : ColCert where
  rK := ⟨143, by decide⟩
  rH := ⟨143, by decide⟩
  m := 5
  T1 := T143_143
  T2 := Q2.T143_143_2
  h1 := (4,1,2,0,4)
  h2 := (4,1,2,0,0)
  D := [[4, 1, 1, 3], [4, 1, 1, 2], [4, 1, 1, 1], [4, 1, 1, 0], [4, 1, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_143_143_22 : ColCert where
  rK := ⟨143, by decide⟩
  rH := ⟨143, by decide⟩
  m := 5
  T1 := T143_143
  T2 := Q2.T143_143_2
  h1 := (4,2,4,0,0)
  h2 := (4,2,4,0,2)
  D := [[4, 2, 2, 1], [4, 2, 2, 4], [4, 2, 2, 2], [4, 2, 2, 0], [4, 2, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_143_143_23 : ColCert where
  rK := ⟨143, by decide⟩
  rH := ⟨143, by decide⟩
  m := 5
  T1 := T143_143
  T2 := Q2.T143_143_2
  h1 := (4,3,1,0,3)
  h2 := (4,3,1,0,1)
  D := [[4, 3, 3, 4], [4, 3, 3, 1], [4, 3, 3, 3], [4, 3, 3, 0], [4, 3, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_143_143_24 : ColCert where
  rK := ⟨143, by decide⟩
  rH := ⟨143, by decide⟩
  m := 5
  T1 := T143_143
  T2 := Q2.T143_143_2
  h1 := (4,4,3,0,3)
  h2 := (4,4,3,0,2)
  D := [[4, 4, 4, 2], [4, 4, 4, 3], [4, 4, 4, 4], [4, 4, 4, 0], [4, 4, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_144_0_0 : ColCert where
  rK := ⟨144, by decide⟩
  rH := ⟨0, by decide⟩
  m := 5
  T1 := T144_0
  T2 := Q2.T144_0_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_144_10_0 : ColCert where
  rK := ⟨144, by decide⟩
  rH := ⟨10, by decide⟩
  m := 5
  T1 := T144_10
  T2 := Q2.T144_10_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_144_10_1 : ColCert where
  rK := ⟨144, by decide⟩
  rH := ⟨10, by decide⟩
  m := 5
  T1 := T144_10
  T2 := Q2.T144_10_2
  h1 := (0,0,0,1,4)
  h2 := (0,0,0,1,4)
  D := [[0, 0, 1, 4], [0, 0, 1, 4], [0, 0, 1, 4], [0, 0, 1, 4], [0, 0, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_144_10_2 : ColCert where
  rK := ⟨144, by decide⟩
  rH := ⟨10, by decide⟩
  m := 5
  T1 := T144_10
  T2 := Q2.T144_10_2
  h1 := (0,0,0,2,3)
  h2 := (0,0,0,2,3)
  D := [[0, 0, 2, 3], [0, 0, 2, 3], [0, 0, 2, 3], [0, 0, 2, 3], [0, 0, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_144_10_3 : ColCert where
  rK := ⟨144, by decide⟩
  rH := ⟨10, by decide⟩
  m := 5
  T1 := T144_10
  T2 := Q2.T144_10_2
  h1 := (0,0,0,3,2)
  h2 := (0,0,0,3,2)
  D := [[0, 0, 3, 2], [0, 0, 3, 2], [0, 0, 3, 2], [0, 0, 3, 2], [0, 0, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_144_10_4 : ColCert where
  rK := ⟨144, by decide⟩
  rH := ⟨10, by decide⟩
  m := 5
  T1 := T144_10
  T2 := Q2.T144_10_2
  h1 := (0,0,0,4,1)
  h2 := (0,0,0,4,1)
  D := [[0, 0, 4, 1], [0, 0, 4, 1], [0, 0, 4, 1], [0, 0, 4, 1], [0, 0, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_144_11_0 : ColCert where
  rK := ⟨144, by decide⟩
  rH := ⟨11, by decide⟩
  m := 5
  T1 := T144_11
  T2 := Q2.T144_11_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_144_11_1 : ColCert where
  rK := ⟨144, by decide⟩
  rH := ⟨11, by decide⟩
  m := 5
  T1 := T144_11
  T2 := Q2.T144_11_2
  h1 := (1,0,0,4,3)
  h2 := (1,0,0,4,3)
  D := [[1, 0, 4, 4], [1, 0, 4, 4], [1, 0, 4, 4], [1, 0, 4, 4], [1, 0, 4, 4]]
  bind1 := by decide
  bind2 := by decide

end LeanDring.P5Presentation
