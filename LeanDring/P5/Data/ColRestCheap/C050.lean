/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.Twin1.ColCert
import LeanDring.P5.Data.EntryK.C030

/-!
# Species-table cell data, stage 2 — twin-coincident columns (cheap tier)

Per-column certified exponent-vector data (`ColCert`/`ColCertDiv`) with kernel
`decide` bindings. Emitted; the embedded lists are what the kernel certifies.
rest tier, chunk 49: 60 columns.
-/

-- machine-emitted data: silence style linters (generated long lines, file-level options)
set_option linter.style.longLine false

namespace LeanDring.P5Presentation

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

def colCert_122_53_15 : ColCert where
  rK := ⟨122, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T122_53
  T2 := Q2.T122_53_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_122_53_20 : ColCert where
  rK := ⟨122, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T122_53
  T2 := Q2.T122_53_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_122_81_0 : ColCert where
  rK := ⟨122, by decide⟩
  rH := ⟨81, by decide⟩
  m := 5
  T1 := T122_81
  T2 := Q2.T122_81_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_122_81_1 : ColCert where
  rK := ⟨122, by decide⟩
  rH := ⟨81, by decide⟩
  m := 5
  T1 := T122_81
  T2 := Q2.T122_81_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_122_81_2 : ColCert where
  rK := ⟨122, by decide⟩
  rH := ⟨81, by decide⟩
  m := 5
  T1 := T122_81
  T2 := Q2.T122_81_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_122_81_3 : ColCert where
  rK := ⟨122, by decide⟩
  rH := ⟨81, by decide⟩
  m := 5
  T1 := T122_81
  T2 := Q2.T122_81_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_122_81_4 : ColCert where
  rK := ⟨122, by decide⟩
  rH := ⟨81, by decide⟩
  m := 5
  T1 := T122_81
  T2 := Q2.T122_81_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_122_90_0 : ColCert where
  rK := ⟨122, by decide⟩
  rH := ⟨90, by decide⟩
  m := 5
  T1 := T122_90
  T2 := Q2.T122_90_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_122_90_1 : ColCert where
  rK := ⟨122, by decide⟩
  rH := ⟨90, by decide⟩
  m := 5
  T1 := T122_90
  T2 := Q2.T122_90_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_122_90_2 : ColCert where
  rK := ⟨122, by decide⟩
  rH := ⟨90, by decide⟩
  m := 5
  T1 := T122_90
  T2 := Q2.T122_90_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_122_90_3 : ColCert where
  rK := ⟨122, by decide⟩
  rH := ⟨90, by decide⟩
  m := 5
  T1 := T122_90
  T2 := Q2.T122_90_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_122_90_4 : ColCert where
  rK := ⟨122, by decide⟩
  rH := ⟨90, by decide⟩
  m := 5
  T1 := T122_90
  T2 := Q2.T122_90_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_122_90_5 : ColCert where
  rK := ⟨122, by decide⟩
  rH := ⟨90, by decide⟩
  m := 5
  T1 := T122_90
  T2 := Q2.T122_90_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_122_90_10 : ColCert where
  rK := ⟨122, by decide⟩
  rH := ⟨90, by decide⟩
  m := 5
  T1 := T122_90
  T2 := Q2.T122_90_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_122_90_15 : ColCert where
  rK := ⟨122, by decide⟩
  rH := ⟨90, by decide⟩
  m := 5
  T1 := T122_90
  T2 := Q2.T122_90_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_122_90_20 : ColCert where
  rK := ⟨122, by decide⟩
  rH := ⟨90, by decide⟩
  m := 5
  T1 := T122_90
  T2 := Q2.T122_90_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_122_98_0 : ColCert where
  rK := ⟨122, by decide⟩
  rH := ⟨98, by decide⟩
  m := 5
  T1 := T122_98
  T2 := Q2.T122_98_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_122_98_1 : ColCert where
  rK := ⟨122, by decide⟩
  rH := ⟨98, by decide⟩
  m := 5
  T1 := T122_98
  T2 := Q2.T122_98_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_122_98_2 : ColCert where
  rK := ⟨122, by decide⟩
  rH := ⟨98, by decide⟩
  m := 5
  T1 := T122_98
  T2 := Q2.T122_98_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_122_98_3 : ColCert where
  rK := ⟨122, by decide⟩
  rH := ⟨98, by decide⟩
  m := 5
  T1 := T122_98
  T2 := Q2.T122_98_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_122_98_4 : ColCert where
  rK := ⟨122, by decide⟩
  rH := ⟨98, by decide⟩
  m := 5
  T1 := T122_98
  T2 := Q2.T122_98_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_122_98_15 : ColCert where
  rK := ⟨122, by decide⟩
  rH := ⟨98, by decide⟩
  m := 5
  T1 := T122_98
  T2 := Q2.T122_98_2
  h1 := (3,4,3,2,0)
  h2 := (3,4,3,2,1)
  D := [[3, 4, 3, 2], [3, 4, 3, 3], [3, 4, 3, 4], [3, 4, 3, 0], [3, 4, 3, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_122_104_0 : ColCert where
  rK := ⟨122, by decide⟩
  rH := ⟨104, by decide⟩
  m := 5
  T1 := T122_104
  T2 := Q2.T122_104_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_122_104_1 : ColCert where
  rK := ⟨122, by decide⟩
  rH := ⟨104, by decide⟩
  m := 5
  T1 := T122_104
  T2 := Q2.T122_104_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_122_104_2 : ColCert where
  rK := ⟨122, by decide⟩
  rH := ⟨104, by decide⟩
  m := 5
  T1 := T122_104
  T2 := Q2.T122_104_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_122_104_3 : ColCert where
  rK := ⟨122, by decide⟩
  rH := ⟨104, by decide⟩
  m := 5
  T1 := T122_104
  T2 := Q2.T122_104_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_122_104_4 : ColCert where
  rK := ⟨122, by decide⟩
  rH := ⟨104, by decide⟩
  m := 5
  T1 := T122_104
  T2 := Q2.T122_104_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_122_107_0 : ColCert where
  rK := ⟨122, by decide⟩
  rH := ⟨107, by decide⟩
  m := 5
  T1 := T122_107
  T2 := Q2.T122_107_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_122_107_1 : ColCert where
  rK := ⟨122, by decide⟩
  rH := ⟨107, by decide⟩
  m := 5
  T1 := T122_107
  T2 := Q2.T122_107_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_122_107_2 : ColCert where
  rK := ⟨122, by decide⟩
  rH := ⟨107, by decide⟩
  m := 5
  T1 := T122_107
  T2 := Q2.T122_107_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_122_107_3 : ColCert where
  rK := ⟨122, by decide⟩
  rH := ⟨107, by decide⟩
  m := 5
  T1 := T122_107
  T2 := Q2.T122_107_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_122_107_4 : ColCert where
  rK := ⟨122, by decide⟩
  rH := ⟨107, by decide⟩
  m := 5
  T1 := T122_107
  T2 := Q2.T122_107_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_122_107_20 : ColCert where
  rK := ⟨122, by decide⟩
  rH := ⟨107, by decide⟩
  m := 5
  T1 := T122_107
  T2 := Q2.T122_107_2
  h1 := (4,3,3,4,2)
  h2 := (4,3,3,4,3)
  D := [[4, 3, 1, 1], [4, 3, 1, 3], [4, 3, 1, 0], [4, 3, 1, 2], [4, 3, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_122_111_0 : ColCert where
  rK := ⟨122, by decide⟩
  rH := ⟨111, by decide⟩
  m := 5
  T1 := T122_111
  T2 := Q2.T122_111_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_122_111_1 : ColCert where
  rK := ⟨122, by decide⟩
  rH := ⟨111, by decide⟩
  m := 5
  T1 := T122_111
  T2 := Q2.T122_111_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_122_111_2 : ColCert where
  rK := ⟨122, by decide⟩
  rH := ⟨111, by decide⟩
  m := 5
  T1 := T122_111
  T2 := Q2.T122_111_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_122_111_3 : ColCert where
  rK := ⟨122, by decide⟩
  rH := ⟨111, by decide⟩
  m := 5
  T1 := T122_111
  T2 := Q2.T122_111_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_122_111_4 : ColCert where
  rK := ⟨122, by decide⟩
  rH := ⟨111, by decide⟩
  m := 5
  T1 := T122_111
  T2 := Q2.T122_111_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_122_111_5 : ColCert where
  rK := ⟨122, by decide⟩
  rH := ⟨111, by decide⟩
  m := 5
  T1 := T122_111
  T2 := Q2.T122_111_2
  h1 := (1,4,0,4,0)
  h2 := (1,4,0,4,0)
  D := [[1, 4, 1, 3], [1, 4, 1, 4], [1, 4, 1, 0], [1, 4, 1, 1], [1, 4, 1, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_122_122_0 : ColCert where
  rK := ⟨122, by decide⟩
  rH := ⟨122, by decide⟩
  m := 5
  T1 := T122_122
  T2 := Q2.T122_122_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_122_122_1 : ColCert where
  rK := ⟨122, by decide⟩
  rH := ⟨122, by decide⟩
  m := 5
  T1 := T122_122
  T2 := Q2.T122_122_2
  h1 := (0,1,4,0,2)
  h2 := (0,1,4,0,0)
  D := [[0, 1, 0, 2], [0, 1, 0, 1], [0, 1, 0, 0], [0, 1, 0, 4], [0, 1, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_122_122_2 : ColCert where
  rK := ⟨122, by decide⟩
  rH := ⟨122, by decide⟩
  m := 5
  T1 := T122_122
  T2 := Q2.T122_122_2
  h1 := (0,2,3,0,3)
  h2 := (0,2,3,0,4)
  D := [[0, 2, 0, 4], [0, 2, 0, 2], [0, 2, 0, 0], [0, 2, 0, 3], [0, 2, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_122_122_3 : ColCert where
  rK := ⟨122, by decide⟩
  rH := ⟨122, by decide⟩
  m := 5
  T1 := T122_122
  T2 := Q2.T122_122_2
  h1 := (0,3,2,0,3)
  h2 := (0,3,2,0,2)
  D := [[0, 3, 0, 1], [0, 3, 0, 3], [0, 3, 0, 0], [0, 3, 0, 2], [0, 3, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_122_122_4 : ColCert where
  rK := ⟨122, by decide⟩
  rH := ⟨122, by decide⟩
  m := 5
  T1 := T122_122
  T2 := Q2.T122_122_2
  h1 := (0,4,1,0,2)
  h2 := (0,4,1,0,4)
  D := [[0, 4, 0, 3], [0, 4, 0, 4], [0, 4, 0, 0], [0, 4, 0, 1], [0, 4, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_122_122_5 : ColCert where
  rK := ⟨122, by decide⟩
  rH := ⟨122, by decide⟩
  m := 5
  T1 := T122_122
  T2 := Q2.T122_122_2
  h1 := (1,0,4,4,2)
  h2 := (1,0,4,4,0)
  D := [[1, 0, 0, 0], [1, 0, 0, 0], [1, 0, 0, 0], [1, 0, 0, 0], [1, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_122_122_6 : ColCert where
  rK := ⟨122, by decide⟩
  rH := ⟨122, by decide⟩
  m := 5
  T1 := T122_122
  T2 := Q2.T122_122_2
  h1 := (1,1,3,4,3)
  h2 := (1,1,3,4,4)
  D := [[1, 1, 4, 2], [1, 1, 4, 1], [1, 1, 4, 0], [1, 1, 4, 4], [1, 1, 4, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_122_122_7 : ColCert where
  rK := ⟨122, by decide⟩
  rH := ⟨122, by decide⟩
  m := 5
  T1 := T122_122
  T2 := Q2.T122_122_2
  h1 := (1,2,2,4,3)
  h2 := (1,2,2,4,2)
  D := [[1, 2, 3, 4], [1, 2, 3, 2], [1, 2, 3, 0], [1, 2, 3, 3], [1, 2, 3, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_122_122_8 : ColCert where
  rK := ⟨122, by decide⟩
  rH := ⟨122, by decide⟩
  m := 5
  T1 := T122_122
  T2 := Q2.T122_122_2
  h1 := (1,3,1,4,2)
  h2 := (1,3,1,4,4)
  D := [[1, 3, 2, 1], [1, 3, 2, 3], [1, 3, 2, 0], [1, 3, 2, 2], [1, 3, 2, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_122_122_9 : ColCert where
  rK := ⟨122, by decide⟩
  rH := ⟨122, by decide⟩
  m := 5
  T1 := T122_122
  T2 := Q2.T122_122_2
  h1 := (1,4,0,4,0)
  h2 := (1,4,0,4,0)
  D := [[1, 4, 1, 3], [1, 4, 1, 4], [1, 4, 1, 0], [1, 4, 1, 1], [1, 4, 1, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_122_122_10 : ColCert where
  rK := ⟨122, by decide⟩
  rH := ⟨122, by decide⟩
  m := 5
  T1 := T122_122
  T2 := Q2.T122_122_2
  h1 := (2,0,3,3,3)
  h2 := (2,0,3,3,4)
  D := [[2, 0, 0, 0], [2, 0, 0, 0], [2, 0, 0, 0], [2, 0, 0, 0], [2, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_122_122_11 : ColCert where
  rK := ⟨122, by decide⟩
  rH := ⟨122, by decide⟩
  m := 5
  T1 := T122_122
  T2 := Q2.T122_122_2
  h1 := (2,1,2,3,3)
  h2 := (2,1,2,3,2)
  D := [[2, 1, 3, 3], [2, 1, 3, 2], [2, 1, 3, 1], [2, 1, 3, 0], [2, 1, 3, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_122_122_12 : ColCert where
  rK := ⟨122, by decide⟩
  rH := ⟨122, by decide⟩
  m := 5
  T1 := T122_122
  T2 := Q2.T122_122_2
  h1 := (2,2,1,3,2)
  h2 := (2,2,1,3,4)
  D := [[2, 2, 1, 1], [2, 2, 1, 4], [2, 2, 1, 2], [2, 2, 1, 0], [2, 2, 1, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_122_122_13 : ColCert where
  rK := ⟨122, by decide⟩
  rH := ⟨122, by decide⟩
  m := 5
  T1 := T122_122
  T2 := Q2.T122_122_2
  h1 := (2,3,0,3,0)
  h2 := (2,3,0,3,0)
  D := [[2, 3, 4, 4], [2, 3, 4, 1], [2, 3, 4, 3], [2, 3, 4, 0], [2, 3, 4, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_122_122_14 : ColCert where
  rK := ⟨122, by decide⟩
  rH := ⟨122, by decide⟩
  m := 5
  T1 := T122_122
  T2 := Q2.T122_122_2
  h1 := (2,4,4,3,2)
  h2 := (2,4,4,3,0)
  D := [[2, 4, 2, 2], [2, 4, 2, 3], [2, 4, 2, 4], [2, 4, 2, 0], [2, 4, 2, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_122_122_15 : ColCert where
  rK := ⟨122, by decide⟩
  rH := ⟨122, by decide⟩
  m := 5
  T1 := T122_122
  T2 := Q2.T122_122_2
  h1 := (3,0,2,2,3)
  h2 := (3,0,2,2,2)
  D := [[3, 0, 0, 0], [3, 0, 0, 0], [3, 0, 0, 0], [3, 0, 0, 0], [3, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_122_122_16 : ColCert where
  rK := ⟨122, by decide⟩
  rH := ⟨122, by decide⟩
  m := 5
  T1 := T122_122
  T2 := Q2.T122_122_2
  h1 := (3,1,1,2,2)
  h2 := (3,1,1,2,4)
  D := [[3, 1, 2, 0], [3, 1, 2, 4], [3, 1, 2, 3], [3, 1, 2, 2], [3, 1, 2, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_122_122_17 : ColCert where
  rK := ⟨122, by decide⟩
  rH := ⟨122, by decide⟩
  m := 5
  T1 := T122_122
  T2 := Q2.T122_122_2
  h1 := (3,2,0,2,0)
  h2 := (3,2,0,2,0)
  D := [[3, 2, 4, 0], [3, 2, 4, 3], [3, 2, 4, 1], [3, 2, 4, 4], [3, 2, 4, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_122_122_18 : ColCert where
  rK := ⟨122, by decide⟩
  rH := ⟨122, by decide⟩
  m := 5
  T1 := T122_122
  T2 := Q2.T122_122_2
  h1 := (3,3,4,2,2)
  h2 := (3,3,4,2,0)
  D := [[3, 3, 1, 0], [3, 3, 1, 2], [3, 3, 1, 4], [3, 3, 1, 1], [3, 3, 1, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_122_122_19 : ColCert where
  rK := ⟨122, by decide⟩
  rH := ⟨122, by decide⟩
  m := 5
  T1 := T122_122
  T2 := Q2.T122_122_2
  h1 := (3,4,3,2,3)
  h2 := (3,4,3,2,4)
  D := [[3, 4, 3, 0], [3, 4, 3, 1], [3, 4, 3, 2], [3, 4, 3, 3], [3, 4, 3, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_122_122_20 : ColCert where
  rK := ⟨122, by decide⟩
  rH := ⟨122, by decide⟩
  m := 5
  T1 := T122_122
  T2 := Q2.T122_122_2
  h1 := (4,0,1,1,2)
  h2 := (4,0,1,1,4)
  D := [[4, 0, 0, 0], [4, 0, 0, 0], [4, 0, 0, 0], [4, 0, 0, 0], [4, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

end LeanDring.P5Presentation
