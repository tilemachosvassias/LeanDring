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
rest tier, chunk 125: 60 columns.
-/

-- machine-emitted data: silence style linters (generated long lines, file-level options)
set_option linter.style.longLine false

namespace LeanDring.P5Presentation

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

def colCert_147_104_20 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨104, by decide⟩
  m := 1
  T1 := T147_104
  T2 := Q2.T147_104_2
  h1 := (4,4,2,1,2)
  h2 := (4,4,2,1,2)
  D := [[4, 4, 2, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_105_0 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨105, by decide⟩
  m := 1
  T1 := T147_105
  T2 := Q2.T147_105_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_105_1 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨105, by decide⟩
  m := 1
  T1 := T147_105
  T2 := Q2.T147_105_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_105_2 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨105, by decide⟩
  m := 1
  T1 := T147_105
  T2 := Q2.T147_105_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_105_3 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨105, by decide⟩
  m := 1
  T1 := T147_105
  T2 := Q2.T147_105_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_105_4 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨105, by decide⟩
  m := 1
  T1 := T147_105
  T2 := Q2.T147_105_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_105_5 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨105, by decide⟩
  m := 1
  T1 := T147_105
  T2 := Q2.T147_105_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_105_10 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨105, by decide⟩
  m := 1
  T1 := T147_105
  T2 := Q2.T147_105_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_105_15 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨105, by decide⟩
  m := 1
  T1 := T147_105
  T2 := Q2.T147_105_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_105_20 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨105, by decide⟩
  m := 1
  T1 := T147_105
  T2 := Q2.T147_105_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_105_25 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨105, by decide⟩
  m := 1
  T1 := T147_105
  T2 := Q2.T147_105_2
  h1 := (0,1,1,0,0)
  h2 := (0,1,1,0,0)
  D := [[0, 1, 1, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_105_50 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨105, by decide⟩
  m := 1
  T1 := T147_105
  T2 := Q2.T147_105_2
  h1 := (0,2,2,0,1)
  h2 := (0,2,2,0,1)
  D := [[0, 2, 2, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_105_75 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨105, by decide⟩
  m := 1
  T1 := T147_105
  T2 := Q2.T147_105_2
  h1 := (0,3,3,0,3)
  h2 := (0,3,3,0,3)
  D := [[0, 3, 3, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_105_100 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨105, by decide⟩
  m := 1
  T1 := T147_105
  T2 := Q2.T147_105_2
  h1 := (0,4,4,0,1)
  h2 := (0,4,4,0,1)
  D := [[0, 4, 4, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_106_0 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨106, by decide⟩
  m := 1
  T1 := T147_106
  T2 := Q2.T147_106_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_106_1 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨106, by decide⟩
  m := 1
  T1 := T147_106
  T2 := Q2.T147_106_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_106_2 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨106, by decide⟩
  m := 1
  T1 := T147_106
  T2 := Q2.T147_106_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_106_3 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨106, by decide⟩
  m := 1
  T1 := T147_106
  T2 := Q2.T147_106_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_106_4 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨106, by decide⟩
  m := 1
  T1 := T147_106
  T2 := Q2.T147_106_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_106_5 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨106, by decide⟩
  m := 1
  T1 := T147_106
  T2 := Q2.T147_106_2
  h1 := (1,4,4,4,1)
  h2 := (1,4,4,4,1)
  D := [[1, 4, 4, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_107_0 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨107, by decide⟩
  m := 1
  T1 := T147_107
  T2 := Q2.T147_107_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_107_1 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨107, by decide⟩
  m := 1
  T1 := T147_107
  T2 := Q2.T147_107_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_107_2 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨107, by decide⟩
  m := 1
  T1 := T147_107
  T2 := Q2.T147_107_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_107_3 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨107, by decide⟩
  m := 1
  T1 := T147_107
  T2 := Q2.T147_107_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_107_4 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨107, by decide⟩
  m := 1
  T1 := T147_107
  T2 := Q2.T147_107_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_107_5 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨107, by decide⟩
  m := 1
  T1 := T147_107
  T2 := Q2.T147_107_2
  h1 := (1,2,2,3,4)
  h2 := (1,2,2,3,4)
  D := [[1, 2, 2, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_107_10 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨107, by decide⟩
  m := 1
  T1 := T147_107
  T2 := Q2.T147_107_2
  h1 := (2,4,4,3,0)
  h2 := (2,4,4,3,0)
  D := [[2, 4, 4, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_108_0 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨108, by decide⟩
  m := 1
  T1 := T147_108
  T2 := Q2.T147_108_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_108_1 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨108, by decide⟩
  m := 1
  T1 := T147_108
  T2 := Q2.T147_108_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_108_2 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨108, by decide⟩
  m := 1
  T1 := T147_108
  T2 := Q2.T147_108_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_108_3 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨108, by decide⟩
  m := 1
  T1 := T147_108
  T2 := Q2.T147_108_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_108_4 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨108, by decide⟩
  m := 1
  T1 := T147_108
  T2 := Q2.T147_108_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_108_5 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨108, by decide⟩
  m := 1
  T1 := T147_108
  T2 := Q2.T147_108_2
  h1 := (1,3,3,1,0)
  h2 := (1,3,3,1,0)
  D := [[1, 3, 3, 3, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_109_0 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨109, by decide⟩
  m := 1
  T1 := T147_109
  T2 := Q2.T147_109_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_109_1 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨109, by decide⟩
  m := 1
  T1 := T147_109
  T2 := Q2.T147_109_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_109_2 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨109, by decide⟩
  m := 1
  T1 := T147_109
  T2 := Q2.T147_109_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_109_3 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨109, by decide⟩
  m := 1
  T1 := T147_109
  T2 := Q2.T147_109_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_109_4 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨109, by decide⟩
  m := 1
  T1 := T147_109
  T2 := Q2.T147_109_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_109_5 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨109, by decide⟩
  m := 1
  T1 := T147_109
  T2 := Q2.T147_109_2
  h1 := (1,1,1,0,0)
  h2 := (1,1,1,0,0)
  D := [[1, 1, 1, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_109_10 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨109, by decide⟩
  m := 1
  T1 := T147_109
  T2 := Q2.T147_109_2
  h1 := (2,2,2,1,1)
  h2 := (2,2,2,1,1)
  D := [[2, 2, 2, 2, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_109_15 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨109, by decide⟩
  m := 1
  T1 := T147_109
  T2 := Q2.T147_109_2
  h1 := (3,3,3,3,4)
  h2 := (3,3,3,3,4)
  D := [[3, 3, 3, 4, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_109_20 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨109, by decide⟩
  m := 1
  T1 := T147_109
  T2 := Q2.T147_109_2
  h1 := (4,4,4,1,0)
  h2 := (4,4,4,1,0)
  D := [[4, 4, 4, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_110_0 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨110, by decide⟩
  m := 1
  T1 := T147_110
  T2 := Q2.T147_110_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_110_1 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨110, by decide⟩
  m := 1
  T1 := T147_110
  T2 := Q2.T147_110_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_110_2 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨110, by decide⟩
  m := 1
  T1 := T147_110
  T2 := Q2.T147_110_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_110_3 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨110, by decide⟩
  m := 1
  T1 := T147_110
  T2 := Q2.T147_110_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_110_4 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨110, by decide⟩
  m := 1
  T1 := T147_110
  T2 := Q2.T147_110_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_110_5 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨110, by decide⟩
  m := 1
  T1 := T147_110
  T2 := Q2.T147_110_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_110_10 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨110, by decide⟩
  m := 1
  T1 := T147_110
  T2 := Q2.T147_110_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_110_15 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨110, by decide⟩
  m := 1
  T1 := T147_110
  T2 := Q2.T147_110_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_110_20 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨110, by decide⟩
  m := 1
  T1 := T147_110
  T2 := Q2.T147_110_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_110_25 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨110, by decide⟩
  m := 1
  T1 := T147_110
  T2 := Q2.T147_110_2
  h1 := (0,1,0,0,0)
  h2 := (0,1,0,0,0)
  D := [[0, 1, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_110_50 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨110, by decide⟩
  m := 1
  T1 := T147_110
  T2 := Q2.T147_110_2
  h1 := (0,2,0,0,0)
  h2 := (0,2,0,0,0)
  D := [[0, 2, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_110_75 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨110, by decide⟩
  m := 1
  T1 := T147_110
  T2 := Q2.T147_110_2
  h1 := (0,3,0,0,0)
  h2 := (0,3,0,0,0)
  D := [[0, 3, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_110_100 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨110, by decide⟩
  m := 1
  T1 := T147_110
  T2 := Q2.T147_110_2
  h1 := (0,4,0,0,0)
  h2 := (0,4,0,0,0)
  D := [[0, 4, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_111_0 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨111, by decide⟩
  m := 1
  T1 := T147_111
  T2 := Q2.T147_111_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_111_1 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨111, by decide⟩
  m := 1
  T1 := T147_111
  T2 := Q2.T147_111_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_111_2 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨111, by decide⟩
  m := 1
  T1 := T147_111
  T2 := Q2.T147_111_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_111_3 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨111, by decide⟩
  m := 1
  T1 := T147_111
  T2 := Q2.T147_111_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_111_4 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨111, by decide⟩
  m := 1
  T1 := T147_111
  T2 := Q2.T147_111_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

end LeanDring.P5Presentation
