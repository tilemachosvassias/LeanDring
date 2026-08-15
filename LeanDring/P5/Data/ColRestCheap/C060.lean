/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.Twin1.ColCert
import LeanDring.P5.Data.EntryK.C032

/-!
# Species-table cell data, stage 2 — twin-coincident columns (cheap tier)

Per-column certified exponent-vector data (`ColCert`/`ColCertDiv`) with kernel
`decide` bindings. Emitted; the embedded lists are what the kernel certifies.
rest tier, chunk 59: 60 columns.
-/

-- machine-emitted data: silence style linters (generated long lines, file-level options)
set_option linter.style.longLine false

namespace LeanDring.P5Presentation

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

def colCert_127_46_2 : ColCert where
  rK := ⟨127, by decide⟩
  rH := ⟨46, by decide⟩
  m := 5
  T1 := T127_46
  T2 := Q2.T127_46_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_127_46_3 : ColCert where
  rK := ⟨127, by decide⟩
  rH := ⟨46, by decide⟩
  m := 5
  T1 := T127_46
  T2 := Q2.T127_46_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_127_46_4 : ColCert where
  rK := ⟨127, by decide⟩
  rH := ⟨46, by decide⟩
  m := 5
  T1 := T127_46
  T2 := Q2.T127_46_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_127_46_10 : ColCert where
  rK := ⟨127, by decide⟩
  rH := ⟨46, by decide⟩
  m := 5
  T1 := T127_46
  T2 := Q2.T127_46_2
  h1 := (2,1,1,3,4)
  h2 := (2,1,1,3,2)
  D := [[2, 1, 3, 2], [2, 1, 3, 1], [2, 1, 3, 0], [2, 1, 3, 4], [2, 1, 3, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_127_46_20 : ColCert where
  rK := ⟨127, by decide⟩
  rH := ⟨46, by decide⟩
  m := 5
  T1 := T127_46
  T2 := Q2.T127_46_2
  h1 := (4,2,2,3,1)
  h2 := (4,2,2,3,2)
  D := [[4, 2, 4, 0], [4, 2, 4, 3], [4, 2, 4, 1], [4, 2, 4, 4], [4, 2, 4, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_127_49_0 : ColCert where
  rK := ⟨127, by decide⟩
  rH := ⟨49, by decide⟩
  m := 5
  T1 := T127_49
  T2 := Q2.T127_49_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_127_49_1 : ColCert where
  rK := ⟨127, by decide⟩
  rH := ⟨49, by decide⟩
  m := 5
  T1 := T127_49
  T2 := Q2.T127_49_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_127_49_2 : ColCert where
  rK := ⟨127, by decide⟩
  rH := ⟨49, by decide⟩
  m := 5
  T1 := T127_49
  T2 := Q2.T127_49_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_127_49_3 : ColCert where
  rK := ⟨127, by decide⟩
  rH := ⟨49, by decide⟩
  m := 5
  T1 := T127_49
  T2 := Q2.T127_49_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_127_49_4 : ColCert where
  rK := ⟨127, by decide⟩
  rH := ⟨49, by decide⟩
  m := 5
  T1 := T127_49
  T2 := Q2.T127_49_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_127_49_5 : ColCert where
  rK := ⟨127, by decide⟩
  rH := ⟨49, by decide⟩
  m := 5
  T1 := T127_49
  T2 := Q2.T127_49_2
  h1 := (1,4,0,3,4)
  h2 := (1,4,0,3,4)
  D := [[1, 4, 0, 1], [1, 4, 0, 2], [1, 4, 0, 3], [1, 4, 0, 4], [1, 4, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_127_53_0 : ColCert where
  rK := ⟨127, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T127_53
  T2 := Q2.T127_53_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_127_53_1 : ColCert where
  rK := ⟨127, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T127_53
  T2 := Q2.T127_53_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_127_53_2 : ColCert where
  rK := ⟨127, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T127_53
  T2 := Q2.T127_53_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_127_53_3 : ColCert where
  rK := ⟨127, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T127_53
  T2 := Q2.T127_53_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_127_53_4 : ColCert where
  rK := ⟨127, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T127_53
  T2 := Q2.T127_53_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_127_53_5 : ColCert where
  rK := ⟨127, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T127_53
  T2 := Q2.T127_53_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_127_53_10 : ColCert where
  rK := ⟨127, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T127_53
  T2 := Q2.T127_53_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_127_53_15 : ColCert where
  rK := ⟨127, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T127_53
  T2 := Q2.T127_53_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_127_53_20 : ColCert where
  rK := ⟨127, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T127_53
  T2 := Q2.T127_53_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_127_82_0 : ColCert where
  rK := ⟨127, by decide⟩
  rH := ⟨82, by decide⟩
  m := 5
  T1 := T127_82
  T2 := Q2.T127_82_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_127_82_1 : ColCert where
  rK := ⟨127, by decide⟩
  rH := ⟨82, by decide⟩
  m := 5
  T1 := T127_82
  T2 := Q2.T127_82_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_127_82_2 : ColCert where
  rK := ⟨127, by decide⟩
  rH := ⟨82, by decide⟩
  m := 5
  T1 := T127_82
  T2 := Q2.T127_82_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_127_82_3 : ColCert where
  rK := ⟨127, by decide⟩
  rH := ⟨82, by decide⟩
  m := 5
  T1 := T127_82
  T2 := Q2.T127_82_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_127_82_4 : ColCert where
  rK := ⟨127, by decide⟩
  rH := ⟨82, by decide⟩
  m := 5
  T1 := T127_82
  T2 := Q2.T127_82_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_127_94_0 : ColCert where
  rK := ⟨127, by decide⟩
  rH := ⟨94, by decide⟩
  m := 5
  T1 := T127_94
  T2 := Q2.T127_94_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_127_94_1 : ColCert where
  rK := ⟨127, by decide⟩
  rH := ⟨94, by decide⟩
  m := 5
  T1 := T127_94
  T2 := Q2.T127_94_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_127_94_2 : ColCert where
  rK := ⟨127, by decide⟩
  rH := ⟨94, by decide⟩
  m := 5
  T1 := T127_94
  T2 := Q2.T127_94_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_127_94_3 : ColCert where
  rK := ⟨127, by decide⟩
  rH := ⟨94, by decide⟩
  m := 5
  T1 := T127_94
  T2 := Q2.T127_94_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_127_94_4 : ColCert where
  rK := ⟨127, by decide⟩
  rH := ⟨94, by decide⟩
  m := 5
  T1 := T127_94
  T2 := Q2.T127_94_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_127_95_0 : ColCert where
  rK := ⟨127, by decide⟩
  rH := ⟨95, by decide⟩
  m := 5
  T1 := T127_95
  T2 := Q2.T127_95_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_127_95_1 : ColCert where
  rK := ⟨127, by decide⟩
  rH := ⟨95, by decide⟩
  m := 5
  T1 := T127_95
  T2 := Q2.T127_95_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_127_95_2 : ColCert where
  rK := ⟨127, by decide⟩
  rH := ⟨95, by decide⟩
  m := 5
  T1 := T127_95
  T2 := Q2.T127_95_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_127_95_3 : ColCert where
  rK := ⟨127, by decide⟩
  rH := ⟨95, by decide⟩
  m := 5
  T1 := T127_95
  T2 := Q2.T127_95_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_127_95_4 : ColCert where
  rK := ⟨127, by decide⟩
  rH := ⟨95, by decide⟩
  m := 5
  T1 := T127_95
  T2 := Q2.T127_95_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_127_95_5 : ColCert where
  rK := ⟨127, by decide⟩
  rH := ⟨95, by decide⟩
  m := 5
  T1 := T127_95
  T2 := Q2.T127_95_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_127_95_10 : ColCert where
  rK := ⟨127, by decide⟩
  rH := ⟨95, by decide⟩
  m := 5
  T1 := T127_95
  T2 := Q2.T127_95_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_127_95_15 : ColCert where
  rK := ⟨127, by decide⟩
  rH := ⟨95, by decide⟩
  m := 5
  T1 := T127_95
  T2 := Q2.T127_95_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_127_95_20 : ColCert where
  rK := ⟨127, by decide⟩
  rH := ⟨95, by decide⟩
  m := 5
  T1 := T127_95
  T2 := Q2.T127_95_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_127_102_0 : ColCert where
  rK := ⟨127, by decide⟩
  rH := ⟨102, by decide⟩
  m := 5
  T1 := T127_102
  T2 := Q2.T127_102_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_127_102_1 : ColCert where
  rK := ⟨127, by decide⟩
  rH := ⟨102, by decide⟩
  m := 5
  T1 := T127_102
  T2 := Q2.T127_102_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_127_102_2 : ColCert where
  rK := ⟨127, by decide⟩
  rH := ⟨102, by decide⟩
  m := 5
  T1 := T127_102
  T2 := Q2.T127_102_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_127_102_3 : ColCert where
  rK := ⟨127, by decide⟩
  rH := ⟨102, by decide⟩
  m := 5
  T1 := T127_102
  T2 := Q2.T127_102_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_127_102_4 : ColCert where
  rK := ⟨127, by decide⟩
  rH := ⟨102, by decide⟩
  m := 5
  T1 := T127_102
  T2 := Q2.T127_102_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_127_108_0 : ColCert where
  rK := ⟨127, by decide⟩
  rH := ⟨108, by decide⟩
  m := 5
  T1 := T127_108
  T2 := Q2.T127_108_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_127_108_1 : ColCert where
  rK := ⟨127, by decide⟩
  rH := ⟨108, by decide⟩
  m := 5
  T1 := T127_108
  T2 := Q2.T127_108_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_127_108_2 : ColCert where
  rK := ⟨127, by decide⟩
  rH := ⟨108, by decide⟩
  m := 5
  T1 := T127_108
  T2 := Q2.T127_108_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_127_108_3 : ColCert where
  rK := ⟨127, by decide⟩
  rH := ⟨108, by decide⟩
  m := 5
  T1 := T127_108
  T2 := Q2.T127_108_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_127_108_4 : ColCert where
  rK := ⟨127, by decide⟩
  rH := ⟨108, by decide⟩
  m := 5
  T1 := T127_108
  T2 := Q2.T127_108_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_127_111_0 : ColCert where
  rK := ⟨127, by decide⟩
  rH := ⟨111, by decide⟩
  m := 5
  T1 := T127_111
  T2 := Q2.T127_111_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_127_111_1 : ColCert where
  rK := ⟨127, by decide⟩
  rH := ⟨111, by decide⟩
  m := 5
  T1 := T127_111
  T2 := Q2.T127_111_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_127_111_2 : ColCert where
  rK := ⟨127, by decide⟩
  rH := ⟨111, by decide⟩
  m := 5
  T1 := T127_111
  T2 := Q2.T127_111_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_127_111_3 : ColCert where
  rK := ⟨127, by decide⟩
  rH := ⟨111, by decide⟩
  m := 5
  T1 := T127_111
  T2 := Q2.T127_111_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_127_111_4 : ColCert where
  rK := ⟨127, by decide⟩
  rH := ⟨111, by decide⟩
  m := 5
  T1 := T127_111
  T2 := Q2.T127_111_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_127_111_5 : ColCert where
  rK := ⟨127, by decide⟩
  rH := ⟨111, by decide⟩
  m := 5
  T1 := T127_111
  T2 := Q2.T127_111_2
  h1 := (1,4,0,4,0)
  h2 := (1,4,0,4,0)
  D := [[1, 4, 1, 1], [1, 4, 1, 2], [1, 4, 1, 3], [1, 4, 1, 4], [1, 4, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_127_127_0 : ColCert where
  rK := ⟨127, by decide⟩
  rH := ⟨127, by decide⟩
  m := 5
  T1 := T127_127
  T2 := Q2.T127_127_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_127_127_1 : ColCert where
  rK := ⟨127, by decide⟩
  rH := ⟨127, by decide⟩
  m := 5
  T1 := T127_127
  T2 := Q2.T127_127_2
  h1 := (0,1,2,0,4)
  h2 := (0,1,2,0,0)
  D := [[0, 1, 0, 1], [0, 1, 0, 0], [0, 1, 0, 4], [0, 1, 0, 3], [0, 1, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_127_127_2 : ColCert where
  rK := ⟨127, by decide⟩
  rH := ⟨127, by decide⟩
  m := 5
  T1 := T127_127
  T2 := Q2.T127_127_2
  h1 := (0,2,4,0,0)
  h2 := (0,2,4,0,2)
  D := [[0, 2, 0, 2], [0, 2, 0, 0], [0, 2, 0, 3], [0, 2, 0, 1], [0, 2, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_127_127_3 : ColCert where
  rK := ⟨127, by decide⟩
  rH := ⟨127, by decide⟩
  m := 5
  T1 := T127_127
  T2 := Q2.T127_127_2
  h1 := (0,3,1,0,3)
  h2 := (0,3,1,0,1)
  D := [[0, 3, 0, 3], [0, 3, 0, 0], [0, 3, 0, 2], [0, 3, 0, 4], [0, 3, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_127_127_4 : ColCert where
  rK := ⟨127, by decide⟩
  rH := ⟨127, by decide⟩
  m := 5
  T1 := T127_127
  T2 := Q2.T127_127_2
  h1 := (0,4,3,0,3)
  h2 := (0,4,3,0,2)
  D := [[0, 4, 0, 4], [0, 4, 0, 0], [0, 4, 0, 1], [0, 4, 0, 2], [0, 4, 0, 3]]
  bind1 := by decide
  bind2 := by decide

end LeanDring.P5Presentation
