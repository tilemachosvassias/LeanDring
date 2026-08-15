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
rest tier, chunk 104: 60 columns.
-/

-- machine-emitted data: silence style linters (generated long lines, file-level options)
set_option linter.style.longLine false

namespace LeanDring.P5Presentation

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

def colCert_145_54_15 : ColCert where
  rK := ⟨145, by decide⟩
  rH := ⟨54, by decide⟩
  m := 5
  T1 := T145_54
  T2 := Q2.T145_54_2
  h1 := (3,0,0,2,4)
  h2 := (3,0,0,2,4)
  D := [[3, 0, 2, 3], [3, 0, 2, 3], [3, 0, 2, 3], [3, 0, 2, 3], [3, 0, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_145_54_20 : ColCert where
  rK := ⟨145, by decide⟩
  rH := ⟨54, by decide⟩
  m := 5
  T1 := T145_54
  T2 := Q2.T145_54_2
  h1 := (4,0,0,1,0)
  h2 := (4,0,0,1,0)
  D := [[4, 0, 1, 1], [4, 0, 1, 1], [4, 0, 1, 1], [4, 0, 1, 1], [4, 0, 1, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_145_105_0 : ColCert where
  rK := ⟨145, by decide⟩
  rH := ⟨105, by decide⟩
  m := 5
  T1 := T145_105
  T2 := Q2.T145_105_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_145_105_1 : ColCert where
  rK := ⟨145, by decide⟩
  rH := ⟨105, by decide⟩
  m := 5
  T1 := T145_105
  T2 := Q2.T145_105_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_145_105_2 : ColCert where
  rK := ⟨145, by decide⟩
  rH := ⟨105, by decide⟩
  m := 5
  T1 := T145_105
  T2 := Q2.T145_105_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_145_105_3 : ColCert where
  rK := ⟨145, by decide⟩
  rH := ⟨105, by decide⟩
  m := 5
  T1 := T145_105
  T2 := Q2.T145_105_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_145_105_4 : ColCert where
  rK := ⟨145, by decide⟩
  rH := ⟨105, by decide⟩
  m := 5
  T1 := T145_105
  T2 := Q2.T145_105_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_145_105_5 : ColCert where
  rK := ⟨145, by decide⟩
  rH := ⟨105, by decide⟩
  m := 5
  T1 := T145_105
  T2 := Q2.T145_105_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_145_105_10 : ColCert where
  rK := ⟨145, by decide⟩
  rH := ⟨105, by decide⟩
  m := 5
  T1 := T145_105
  T2 := Q2.T145_105_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_145_105_15 : ColCert where
  rK := ⟨145, by decide⟩
  rH := ⟨105, by decide⟩
  m := 5
  T1 := T145_105
  T2 := Q2.T145_105_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_145_105_20 : ColCert where
  rK := ⟨145, by decide⟩
  rH := ⟨105, by decide⟩
  m := 5
  T1 := T145_105
  T2 := Q2.T145_105_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_145_105_25 : ColCert where
  rK := ⟨145, by decide⟩
  rH := ⟨105, by decide⟩
  m := 5
  T1 := T145_105
  T2 := Q2.T145_105_2
  h1 := (0,1,1,0,0)
  h2 := (0,1,1,0,0)
  D := [[0, 1, 0, 4], [0, 1, 0, 3], [0, 1, 0, 2], [0, 1, 0, 1], [0, 1, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_145_105_50 : ColCert where
  rK := ⟨145, by decide⟩
  rH := ⟨105, by decide⟩
  m := 5
  T1 := T145_105
  T2 := Q2.T145_105_2
  h1 := (0,2,2,0,1)
  h2 := (0,2,2,0,1)
  D := [[0, 2, 0, 3], [0, 2, 0, 1], [0, 2, 0, 4], [0, 2, 0, 2], [0, 2, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_145_105_75 : ColCert where
  rK := ⟨145, by decide⟩
  rH := ⟨105, by decide⟩
  m := 5
  T1 := T145_105
  T2 := Q2.T145_105_2
  h1 := (0,3,3,0,3)
  h2 := (0,3,3,0,3)
  D := [[0, 3, 0, 2], [0, 3, 0, 4], [0, 3, 0, 1], [0, 3, 0, 3], [0, 3, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_145_105_100 : ColCert where
  rK := ⟨145, by decide⟩
  rH := ⟨105, by decide⟩
  m := 5
  T1 := T145_105
  T2 := Q2.T145_105_2
  h1 := (0,4,4,0,1)
  h2 := (0,4,4,0,1)
  D := [[0, 4, 0, 1], [0, 4, 0, 2], [0, 4, 0, 3], [0, 4, 0, 4], [0, 4, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_145_106_0 : ColCert where
  rK := ⟨145, by decide⟩
  rH := ⟨106, by decide⟩
  m := 5
  T1 := T145_106
  T2 := Q2.T145_106_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_145_106_1 : ColCert where
  rK := ⟨145, by decide⟩
  rH := ⟨106, by decide⟩
  m := 5
  T1 := T145_106
  T2 := Q2.T145_106_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_145_106_2 : ColCert where
  rK := ⟨145, by decide⟩
  rH := ⟨106, by decide⟩
  m := 5
  T1 := T145_106
  T2 := Q2.T145_106_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_145_106_3 : ColCert where
  rK := ⟨145, by decide⟩
  rH := ⟨106, by decide⟩
  m := 5
  T1 := T145_106
  T2 := Q2.T145_106_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_145_106_4 : ColCert where
  rK := ⟨145, by decide⟩
  rH := ⟨106, by decide⟩
  m := 5
  T1 := T145_106
  T2 := Q2.T145_106_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_145_106_5 : ColCert where
  rK := ⟨145, by decide⟩
  rH := ⟨106, by decide⟩
  m := 5
  T1 := T145_106
  T2 := Q2.T145_106_2
  h1 := (1,4,4,4,1)
  h2 := (1,4,4,4,1)
  D := [[1, 4, 0, 1], [1, 4, 0, 2], [1, 4, 0, 3], [1, 4, 0, 4], [1, 4, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_145_107_0 : ColCert where
  rK := ⟨145, by decide⟩
  rH := ⟨107, by decide⟩
  m := 5
  T1 := T145_107
  T2 := Q2.T145_107_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_145_107_1 : ColCert where
  rK := ⟨145, by decide⟩
  rH := ⟨107, by decide⟩
  m := 5
  T1 := T145_107
  T2 := Q2.T145_107_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_145_107_2 : ColCert where
  rK := ⟨145, by decide⟩
  rH := ⟨107, by decide⟩
  m := 5
  T1 := T145_107
  T2 := Q2.T145_107_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_145_107_3 : ColCert where
  rK := ⟨145, by decide⟩
  rH := ⟨107, by decide⟩
  m := 5
  T1 := T145_107
  T2 := Q2.T145_107_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_145_107_4 : ColCert where
  rK := ⟨145, by decide⟩
  rH := ⟨107, by decide⟩
  m := 5
  T1 := T145_107
  T2 := Q2.T145_107_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_145_107_5 : ColCert where
  rK := ⟨145, by decide⟩
  rH := ⟨107, by decide⟩
  m := 5
  T1 := T145_107
  T2 := Q2.T145_107_2
  h1 := (1,2,2,3,4)
  h2 := (1,2,2,3,4)
  D := [[1, 2, 1, 0], [1, 2, 1, 3], [1, 2, 1, 1], [1, 2, 1, 4], [1, 2, 1, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_145_107_10 : ColCert where
  rK := ⟨145, by decide⟩
  rH := ⟨107, by decide⟩
  m := 5
  T1 := T145_107
  T2 := Q2.T145_107_2
  h1 := (2,4,4,3,0)
  h2 := (2,4,4,3,0)
  D := [[2, 4, 0, 1], [2, 4, 0, 2], [2, 4, 0, 3], [2, 4, 0, 4], [2, 4, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_145_108_0 : ColCert where
  rK := ⟨145, by decide⟩
  rH := ⟨108, by decide⟩
  m := 5
  T1 := T145_108
  T2 := Q2.T145_108_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_145_108_1 : ColCert where
  rK := ⟨145, by decide⟩
  rH := ⟨108, by decide⟩
  m := 5
  T1 := T145_108
  T2 := Q2.T145_108_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_145_108_2 : ColCert where
  rK := ⟨145, by decide⟩
  rH := ⟨108, by decide⟩
  m := 5
  T1 := T145_108
  T2 := Q2.T145_108_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_145_108_3 : ColCert where
  rK := ⟨145, by decide⟩
  rH := ⟨108, by decide⟩
  m := 5
  T1 := T145_108
  T2 := Q2.T145_108_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_145_108_4 : ColCert where
  rK := ⟨145, by decide⟩
  rH := ⟨108, by decide⟩
  m := 5
  T1 := T145_108
  T2 := Q2.T145_108_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_145_108_5 : ColCert where
  rK := ⟨145, by decide⟩
  rH := ⟨108, by decide⟩
  m := 5
  T1 := T145_108
  T2 := Q2.T145_108_2
  h1 := (1,3,3,1,0)
  h2 := (1,3,3,1,0)
  D := [[1, 3, 3, 1], [1, 3, 3, 3], [1, 3, 3, 0], [1, 3, 3, 2], [1, 3, 3, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_145_109_0 : ColCert where
  rK := ⟨145, by decide⟩
  rH := ⟨109, by decide⟩
  m := 5
  T1 := T145_109
  T2 := Q2.T145_109_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_145_109_1 : ColCert where
  rK := ⟨145, by decide⟩
  rH := ⟨109, by decide⟩
  m := 5
  T1 := T145_109
  T2 := Q2.T145_109_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_145_109_2 : ColCert where
  rK := ⟨145, by decide⟩
  rH := ⟨109, by decide⟩
  m := 5
  T1 := T145_109
  T2 := Q2.T145_109_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_145_109_3 : ColCert where
  rK := ⟨145, by decide⟩
  rH := ⟨109, by decide⟩
  m := 5
  T1 := T145_109
  T2 := Q2.T145_109_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_145_109_4 : ColCert where
  rK := ⟨145, by decide⟩
  rH := ⟨109, by decide⟩
  m := 5
  T1 := T145_109
  T2 := Q2.T145_109_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_145_109_5 : ColCert where
  rK := ⟨145, by decide⟩
  rH := ⟨109, by decide⟩
  m := 5
  T1 := T145_109
  T2 := Q2.T145_109_2
  h1 := (1,1,1,0,0)
  h2 := (1,1,1,0,0)
  D := [[1, 1, 4, 0], [1, 1, 4, 4], [1, 1, 4, 3], [1, 1, 4, 2], [1, 1, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_145_109_10 : ColCert where
  rK := ⟨145, by decide⟩
  rH := ⟨109, by decide⟩
  m := 5
  T1 := T145_109
  T2 := Q2.T145_109_2
  h1 := (2,2,2,1,1)
  h2 := (2,2,2,1,1)
  D := [[2, 2, 2, 2], [2, 2, 2, 0], [2, 2, 2, 3], [2, 2, 2, 1], [2, 2, 2, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_145_109_15 : ColCert where
  rK := ⟨145, by decide⟩
  rH := ⟨109, by decide⟩
  m := 5
  T1 := T145_109
  T2 := Q2.T145_109_2
  h1 := (3,3,3,3,4)
  h2 := (3,3,3,3,4)
  D := [[3, 3, 4, 2], [3, 3, 4, 4], [3, 3, 4, 1], [3, 3, 4, 3], [3, 3, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_145_109_20 : ColCert where
  rK := ⟨145, by decide⟩
  rH := ⟨109, by decide⟩
  m := 5
  T1 := T145_109
  T2 := Q2.T145_109_2
  h1 := (4,4,4,1,0)
  h2 := (4,4,4,1,0)
  D := [[4, 4, 0, 1], [4, 4, 0, 2], [4, 4, 0, 3], [4, 4, 0, 4], [4, 4, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_145_115_0 : ColCert where
  rK := ⟨145, by decide⟩
  rH := ⟨115, by decide⟩
  m := 5
  T1 := T145_115
  T2 := Q2.T145_115_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_145_115_1 : ColCert where
  rK := ⟨145, by decide⟩
  rH := ⟨115, by decide⟩
  m := 5
  T1 := T145_115
  T2 := Q2.T145_115_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_145_115_2 : ColCert where
  rK := ⟨145, by decide⟩
  rH := ⟨115, by decide⟩
  m := 5
  T1 := T145_115
  T2 := Q2.T145_115_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_145_115_3 : ColCert where
  rK := ⟨145, by decide⟩
  rH := ⟨115, by decide⟩
  m := 5
  T1 := T145_115
  T2 := Q2.T145_115_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_145_115_4 : ColCert where
  rK := ⟨145, by decide⟩
  rH := ⟨115, by decide⟩
  m := 5
  T1 := T145_115
  T2 := Q2.T145_115_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_145_115_5 : ColCert where
  rK := ⟨145, by decide⟩
  rH := ⟨115, by decide⟩
  m := 5
  T1 := T145_115
  T2 := Q2.T145_115_2
  h1 := (1,0,0,0,0)
  h2 := (1,0,0,0,0)
  D := [[1, 0, 0, 0], [1, 0, 0, 0], [1, 0, 0, 0], [1, 0, 0, 0], [1, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_145_115_10 : ColCert where
  rK := ⟨145, by decide⟩
  rH := ⟨115, by decide⟩
  m := 5
  T1 := T145_115
  T2 := Q2.T145_115_2
  h1 := (2,0,0,0,0)
  h2 := (2,0,0,0,0)
  D := [[2, 0, 0, 0], [2, 0, 0, 0], [2, 0, 0, 0], [2, 0, 0, 0], [2, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_145_115_15 : ColCert where
  rK := ⟨145, by decide⟩
  rH := ⟨115, by decide⟩
  m := 5
  T1 := T145_115
  T2 := Q2.T145_115_2
  h1 := (3,0,0,0,0)
  h2 := (3,0,0,0,0)
  D := [[3, 0, 0, 0], [3, 0, 0, 0], [3, 0, 0, 0], [3, 0, 0, 0], [3, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_145_115_20 : ColCert where
  rK := ⟨145, by decide⟩
  rH := ⟨115, by decide⟩
  m := 5
  T1 := T145_115
  T2 := Q2.T145_115_2
  h1 := (4,0,0,0,0)
  h2 := (4,0,0,0,0)
  D := [[4, 0, 0, 0], [4, 0, 0, 0], [4, 0, 0, 0], [4, 0, 0, 0], [4, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_145_145_0 : ColCert where
  rK := ⟨145, by decide⟩
  rH := ⟨145, by decide⟩
  m := 5
  T1 := T145_145
  T2 := Q2.T145_145_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_145_145_1 : ColCert where
  rK := ⟨145, by decide⟩
  rH := ⟨145, by decide⟩
  m := 5
  T1 := T145_145
  T2 := Q2.T145_145_2
  h1 := (0,1,1,0,0)
  h2 := (0,1,1,0,0)
  D := [[0, 1, 0, 4], [0, 1, 0, 3], [0, 1, 0, 2], [0, 1, 0, 1], [0, 1, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_145_145_2 : ColCert where
  rK := ⟨145, by decide⟩
  rH := ⟨145, by decide⟩
  m := 5
  T1 := T145_145
  T2 := Q2.T145_145_2
  h1 := (0,2,2,0,1)
  h2 := (0,2,2,0,1)
  D := [[0, 2, 0, 3], [0, 2, 0, 1], [0, 2, 0, 4], [0, 2, 0, 2], [0, 2, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_145_145_3 : ColCert where
  rK := ⟨145, by decide⟩
  rH := ⟨145, by decide⟩
  m := 5
  T1 := T145_145
  T2 := Q2.T145_145_2
  h1 := (0,3,3,0,3)
  h2 := (0,3,3,0,3)
  D := [[0, 3, 0, 2], [0, 3, 0, 4], [0, 3, 0, 1], [0, 3, 0, 3], [0, 3, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_145_145_4 : ColCert where
  rK := ⟨145, by decide⟩
  rH := ⟨145, by decide⟩
  m := 5
  T1 := T145_145
  T2 := Q2.T145_145_2
  h1 := (0,4,4,0,1)
  h2 := (0,4,4,0,1)
  D := [[0, 4, 0, 1], [0, 4, 0, 2], [0, 4, 0, 3], [0, 4, 0, 4], [0, 4, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_145_145_5 : ColCert where
  rK := ⟨145, by decide⟩
  rH := ⟨145, by decide⟩
  m := 5
  T1 := T145_145
  T2 := Q2.T145_145_2
  h1 := (1,0,0,0,0)
  h2 := (1,0,0,0,0)
  D := [[1, 0, 0, 0], [1, 0, 0, 0], [1, 0, 0, 0], [1, 0, 0, 0], [1, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_145_145_6 : ColCert where
  rK := ⟨145, by decide⟩
  rH := ⟨145, by decide⟩
  m := 5
  T1 := T145_145
  T2 := Q2.T145_145_2
  h1 := (1,1,1,0,0)
  h2 := (1,1,1,0,0)
  D := [[1, 1, 4, 0], [1, 1, 4, 4], [1, 1, 4, 3], [1, 1, 4, 2], [1, 1, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_145_145_7 : ColCert where
  rK := ⟨145, by decide⟩
  rH := ⟨145, by decide⟩
  m := 5
  T1 := T145_145
  T2 := Q2.T145_145_2
  h1 := (1,2,2,0,1)
  h2 := (1,2,2,0,1)
  D := [[1, 2, 3, 0], [1, 2, 3, 3], [1, 2, 3, 1], [1, 2, 3, 4], [1, 2, 3, 2]]
  bind1 := by decide
  bind2 := by decide

end LeanDring.P5Presentation
