/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.Twin1.ColCert
import LeanDring.P5.Data.EntryK.C035

/-!
# Species-table cell data, stage 2 — twin-coincident columns (cheap tier)

Per-column certified exponent-vector data (`ColCert`/`ColCertDiv`) with kernel
`decide` bindings. Emitted; the embedded lists are what the kernel certifies.
rest tier, chunk 69: 60 columns.
-/

-- machine-emitted data: silence style linters (generated long lines, file-level options)
set_option linter.style.longLine false

namespace LeanDring.P5Presentation

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

def colCert_132_22_1 : ColCert where
  rK := ⟨132, by decide⟩
  rH := ⟨22, by decide⟩
  m := 5
  T1 := T132_22
  T2 := Q2.T132_22_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_132_22_2 : ColCert where
  rK := ⟨132, by decide⟩
  rH := ⟨22, by decide⟩
  m := 5
  T1 := T132_22
  T2 := Q2.T132_22_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_132_22_3 : ColCert where
  rK := ⟨132, by decide⟩
  rH := ⟨22, by decide⟩
  m := 5
  T1 := T132_22
  T2 := Q2.T132_22_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_132_22_4 : ColCert where
  rK := ⟨132, by decide⟩
  rH := ⟨22, by decide⟩
  m := 5
  T1 := T132_22
  T2 := Q2.T132_22_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_132_31_0 : ColCert where
  rK := ⟨132, by decide⟩
  rH := ⟨31, by decide⟩
  m := 5
  T1 := T132_31
  T2 := Q2.T132_31_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_132_31_1 : ColCert where
  rK := ⟨132, by decide⟩
  rH := ⟨31, by decide⟩
  m := 5
  T1 := T132_31
  T2 := Q2.T132_31_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_132_31_2 : ColCert where
  rK := ⟨132, by decide⟩
  rH := ⟨31, by decide⟩
  m := 5
  T1 := T132_31
  T2 := Q2.T132_31_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_132_31_3 : ColCert where
  rK := ⟨132, by decide⟩
  rH := ⟨31, by decide⟩
  m := 5
  T1 := T132_31
  T2 := Q2.T132_31_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_132_31_4 : ColCert where
  rK := ⟨132, by decide⟩
  rH := ⟨31, by decide⟩
  m := 5
  T1 := T132_31
  T2 := Q2.T132_31_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_132_31_10 : ColCert where
  rK := ⟨132, by decide⟩
  rH := ⟨31, by decide⟩
  m := 5
  T1 := T132_31
  T2 := Q2.T132_31_2
  h1 := (2,1,4,3,0)
  h2 := (2,1,4,3,3)
  D := [[2, 1, 3, 2], [2, 1, 3, 1], [2, 1, 3, 0], [2, 1, 3, 4], [2, 1, 3, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_132_31_20 : ColCert where
  rK := ⟨132, by decide⟩
  rH := ⟨31, by decide⟩
  m := 5
  T1 := T132_31
  T2 := Q2.T132_31_2
  h1 := (4,2,3,3,1)
  h2 := (4,2,3,3,2)
  D := [[4, 2, 4, 2], [4, 2, 4, 0], [4, 2, 4, 3], [4, 2, 4, 1], [4, 2, 4, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_132_35_0 : ColCert where
  rK := ⟨132, by decide⟩
  rH := ⟨35, by decide⟩
  m := 5
  T1 := T132_35
  T2 := Q2.T132_35_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_132_35_1 : ColCert where
  rK := ⟨132, by decide⟩
  rH := ⟨35, by decide⟩
  m := 5
  T1 := T132_35
  T2 := Q2.T132_35_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_132_35_2 : ColCert where
  rK := ⟨132, by decide⟩
  rH := ⟨35, by decide⟩
  m := 5
  T1 := T132_35
  T2 := Q2.T132_35_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_132_35_3 : ColCert where
  rK := ⟨132, by decide⟩
  rH := ⟨35, by decide⟩
  m := 5
  T1 := T132_35
  T2 := Q2.T132_35_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_132_35_4 : ColCert where
  rK := ⟨132, by decide⟩
  rH := ⟨35, by decide⟩
  m := 5
  T1 := T132_35
  T2 := Q2.T132_35_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_132_38_0 : ColCert where
  rK := ⟨132, by decide⟩
  rH := ⟨38, by decide⟩
  m := 5
  T1 := T132_38
  T2 := Q2.T132_38_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_132_38_1 : ColCert where
  rK := ⟨132, by decide⟩
  rH := ⟨38, by decide⟩
  m := 5
  T1 := T132_38
  T2 := Q2.T132_38_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_132_38_2 : ColCert where
  rK := ⟨132, by decide⟩
  rH := ⟨38, by decide⟩
  m := 5
  T1 := T132_38
  T2 := Q2.T132_38_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_132_38_3 : ColCert where
  rK := ⟨132, by decide⟩
  rH := ⟨38, by decide⟩
  m := 5
  T1 := T132_38
  T2 := Q2.T132_38_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_132_38_4 : ColCert where
  rK := ⟨132, by decide⟩
  rH := ⟨38, by decide⟩
  m := 5
  T1 := T132_38
  T2 := Q2.T132_38_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_132_47_0 : ColCert where
  rK := ⟨132, by decide⟩
  rH := ⟨47, by decide⟩
  m := 5
  T1 := T132_47
  T2 := Q2.T132_47_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_132_47_1 : ColCert where
  rK := ⟨132, by decide⟩
  rH := ⟨47, by decide⟩
  m := 5
  T1 := T132_47
  T2 := Q2.T132_47_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_132_47_2 : ColCert where
  rK := ⟨132, by decide⟩
  rH := ⟨47, by decide⟩
  m := 5
  T1 := T132_47
  T2 := Q2.T132_47_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_132_47_3 : ColCert where
  rK := ⟨132, by decide⟩
  rH := ⟨47, by decide⟩
  m := 5
  T1 := T132_47
  T2 := Q2.T132_47_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_132_47_4 : ColCert where
  rK := ⟨132, by decide⟩
  rH := ⟨47, by decide⟩
  m := 5
  T1 := T132_47
  T2 := Q2.T132_47_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_132_49_0 : ColCert where
  rK := ⟨132, by decide⟩
  rH := ⟨49, by decide⟩
  m := 5
  T1 := T132_49
  T2 := Q2.T132_49_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_132_49_1 : ColCert where
  rK := ⟨132, by decide⟩
  rH := ⟨49, by decide⟩
  m := 5
  T1 := T132_49
  T2 := Q2.T132_49_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_132_49_2 : ColCert where
  rK := ⟨132, by decide⟩
  rH := ⟨49, by decide⟩
  m := 5
  T1 := T132_49
  T2 := Q2.T132_49_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_132_49_3 : ColCert where
  rK := ⟨132, by decide⟩
  rH := ⟨49, by decide⟩
  m := 5
  T1 := T132_49
  T2 := Q2.T132_49_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_132_49_4 : ColCert where
  rK := ⟨132, by decide⟩
  rH := ⟨49, by decide⟩
  m := 5
  T1 := T132_49
  T2 := Q2.T132_49_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_132_49_5 : ColCert where
  rK := ⟨132, by decide⟩
  rH := ⟨49, by decide⟩
  m := 5
  T1 := T132_49
  T2 := Q2.T132_49_2
  h1 := (1,4,0,3,4)
  h2 := (1,4,0,3,4)
  D := [[1, 4, 0, 2], [1, 4, 0, 3], [1, 4, 0, 4], [1, 4, 0, 0], [1, 4, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_132_53_0 : ColCert where
  rK := ⟨132, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T132_53
  T2 := Q2.T132_53_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_132_53_1 : ColCert where
  rK := ⟨132, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T132_53
  T2 := Q2.T132_53_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_132_53_2 : ColCert where
  rK := ⟨132, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T132_53
  T2 := Q2.T132_53_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_132_53_3 : ColCert where
  rK := ⟨132, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T132_53
  T2 := Q2.T132_53_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_132_53_4 : ColCert where
  rK := ⟨132, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T132_53
  T2 := Q2.T132_53_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_132_53_5 : ColCert where
  rK := ⟨132, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T132_53
  T2 := Q2.T132_53_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_132_53_10 : ColCert where
  rK := ⟨132, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T132_53
  T2 := Q2.T132_53_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_132_53_15 : ColCert where
  rK := ⟨132, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T132_53
  T2 := Q2.T132_53_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_132_53_20 : ColCert where
  rK := ⟨132, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T132_53
  T2 := Q2.T132_53_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_132_83_0 : ColCert where
  rK := ⟨132, by decide⟩
  rH := ⟨83, by decide⟩
  m := 5
  T1 := T132_83
  T2 := Q2.T132_83_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_132_83_1 : ColCert where
  rK := ⟨132, by decide⟩
  rH := ⟨83, by decide⟩
  m := 5
  T1 := T132_83
  T2 := Q2.T132_83_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_132_83_2 : ColCert where
  rK := ⟨132, by decide⟩
  rH := ⟨83, by decide⟩
  m := 5
  T1 := T132_83
  T2 := Q2.T132_83_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_132_83_3 : ColCert where
  rK := ⟨132, by decide⟩
  rH := ⟨83, by decide⟩
  m := 5
  T1 := T132_83
  T2 := Q2.T132_83_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_132_83_4 : ColCert where
  rK := ⟨132, by decide⟩
  rH := ⟨83, by decide⟩
  m := 5
  T1 := T132_83
  T2 := Q2.T132_83_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_132_93_0 : ColCert where
  rK := ⟨132, by decide⟩
  rH := ⟨93, by decide⟩
  m := 5
  T1 := T132_93
  T2 := Q2.T132_93_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_132_93_1 : ColCert where
  rK := ⟨132, by decide⟩
  rH := ⟨93, by decide⟩
  m := 5
  T1 := T132_93
  T2 := Q2.T132_93_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_132_93_2 : ColCert where
  rK := ⟨132, by decide⟩
  rH := ⟨93, by decide⟩
  m := 5
  T1 := T132_93
  T2 := Q2.T132_93_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_132_93_3 : ColCert where
  rK := ⟨132, by decide⟩
  rH := ⟨93, by decide⟩
  m := 5
  T1 := T132_93
  T2 := Q2.T132_93_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_132_93_4 : ColCert where
  rK := ⟨132, by decide⟩
  rH := ⟨93, by decide⟩
  m := 5
  T1 := T132_93
  T2 := Q2.T132_93_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_132_97_0 : ColCert where
  rK := ⟨132, by decide⟩
  rH := ⟨97, by decide⟩
  m := 5
  T1 := T132_97
  T2 := Q2.T132_97_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_132_97_1 : ColCert where
  rK := ⟨132, by decide⟩
  rH := ⟨97, by decide⟩
  m := 5
  T1 := T132_97
  T2 := Q2.T132_97_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_132_97_2 : ColCert where
  rK := ⟨132, by decide⟩
  rH := ⟨97, by decide⟩
  m := 5
  T1 := T132_97
  T2 := Q2.T132_97_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_132_97_3 : ColCert where
  rK := ⟨132, by decide⟩
  rH := ⟨97, by decide⟩
  m := 5
  T1 := T132_97
  T2 := Q2.T132_97_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_132_97_4 : ColCert where
  rK := ⟨132, by decide⟩
  rH := ⟨97, by decide⟩
  m := 5
  T1 := T132_97
  T2 := Q2.T132_97_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_132_100_0 : ColCert where
  rK := ⟨132, by decide⟩
  rH := ⟨100, by decide⟩
  m := 5
  T1 := T132_100
  T2 := Q2.T132_100_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_132_100_1 : ColCert where
  rK := ⟨132, by decide⟩
  rH := ⟨100, by decide⟩
  m := 5
  T1 := T132_100
  T2 := Q2.T132_100_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_132_100_2 : ColCert where
  rK := ⟨132, by decide⟩
  rH := ⟨100, by decide⟩
  m := 5
  T1 := T132_100
  T2 := Q2.T132_100_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_132_100_3 : ColCert where
  rK := ⟨132, by decide⟩
  rH := ⟨100, by decide⟩
  m := 5
  T1 := T132_100
  T2 := Q2.T132_100_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

end LeanDring.P5Presentation
