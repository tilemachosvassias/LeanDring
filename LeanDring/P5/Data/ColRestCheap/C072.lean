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
rest tier, chunk 71: 60 columns.
-/

-- machine-emitted data: silence style linters (generated long lines, file-level options)
set_option linter.style.longLine false

namespace LeanDring.P5Presentation

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

def colCert_133_22_3 : ColCert where
  rK := ⟨133, by decide⟩
  rH := ⟨22, by decide⟩
  m := 5
  T1 := T133_22
  T2 := Q2.T133_22_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_133_22_4 : ColCert where
  rK := ⟨133, by decide⟩
  rH := ⟨22, by decide⟩
  m := 5
  T1 := T133_22
  T2 := Q2.T133_22_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_133_22_5 : ColCert where
  rK := ⟨133, by decide⟩
  rH := ⟨22, by decide⟩
  m := 5
  T1 := T133_22
  T2 := Q2.T133_22_2
  h1 := (1,0,3,2,4)
  h2 := (1,0,3,2,4)
  D := [[1, 0, 4, 4], [1, 0, 4, 4], [1, 0, 4, 4], [1, 0, 4, 4], [1, 0, 4, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_133_22_10 : ColCert where
  rK := ⟨133, by decide⟩
  rH := ⟨22, by decide⟩
  m := 5
  T1 := T133_22
  T2 := Q2.T133_22_2
  h1 := (2,0,1,4,0)
  h2 := (2,0,1,4,0)
  D := [[2, 0, 3, 4], [2, 0, 3, 4], [2, 0, 3, 4], [2, 0, 3, 4], [2, 0, 3, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_133_22_15 : ColCert where
  rK := ⟨133, by decide⟩
  rH := ⟨22, by decide⟩
  m := 5
  T1 := T133_22
  T2 := Q2.T133_22_2
  h1 := (3,0,4,1,3)
  h2 := (3,0,4,1,3)
  D := [[3, 0, 2, 0], [3, 0, 2, 0], [3, 0, 2, 0], [3, 0, 2, 0], [3, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_133_22_20 : ColCert where
  rK := ⟨133, by decide⟩
  rH := ⟨22, by decide⟩
  m := 5
  T1 := T133_22
  T2 := Q2.T133_22_2
  h1 := (4,0,2,3,3)
  h2 := (4,0,2,3,3)
  D := [[4, 0, 1, 2], [4, 0, 1, 2], [4, 0, 1, 2], [4, 0, 1, 2], [4, 0, 1, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_133_32_0 : ColCert where
  rK := ⟨133, by decide⟩
  rH := ⟨32, by decide⟩
  m := 5
  T1 := T133_32
  T2 := Q2.T133_32_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_133_32_1 : ColCert where
  rK := ⟨133, by decide⟩
  rH := ⟨32, by decide⟩
  m := 5
  T1 := T133_32
  T2 := Q2.T133_32_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_133_32_2 : ColCert where
  rK := ⟨133, by decide⟩
  rH := ⟨32, by decide⟩
  m := 5
  T1 := T133_32
  T2 := Q2.T133_32_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_133_32_3 : ColCert where
  rK := ⟨133, by decide⟩
  rH := ⟨32, by decide⟩
  m := 5
  T1 := T133_32
  T2 := Q2.T133_32_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_133_32_4 : ColCert where
  rK := ⟨133, by decide⟩
  rH := ⟨32, by decide⟩
  m := 5
  T1 := T133_32
  T2 := Q2.T133_32_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_133_36_0 : ColCert where
  rK := ⟨133, by decide⟩
  rH := ⟨36, by decide⟩
  m := 5
  T1 := T133_36
  T2 := Q2.T133_36_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_133_36_1 : ColCert where
  rK := ⟨133, by decide⟩
  rH := ⟨36, by decide⟩
  m := 5
  T1 := T133_36
  T2 := Q2.T133_36_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_133_36_2 : ColCert where
  rK := ⟨133, by decide⟩
  rH := ⟨36, by decide⟩
  m := 5
  T1 := T133_36
  T2 := Q2.T133_36_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_133_36_3 : ColCert where
  rK := ⟨133, by decide⟩
  rH := ⟨36, by decide⟩
  m := 5
  T1 := T133_36
  T2 := Q2.T133_36_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_133_36_4 : ColCert where
  rK := ⟨133, by decide⟩
  rH := ⟨36, by decide⟩
  m := 5
  T1 := T133_36
  T2 := Q2.T133_36_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_133_39_0 : ColCert where
  rK := ⟨133, by decide⟩
  rH := ⟨39, by decide⟩
  m := 5
  T1 := T133_39
  T2 := Q2.T133_39_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_133_39_1 : ColCert where
  rK := ⟨133, by decide⟩
  rH := ⟨39, by decide⟩
  m := 5
  T1 := T133_39
  T2 := Q2.T133_39_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_133_39_2 : ColCert where
  rK := ⟨133, by decide⟩
  rH := ⟨39, by decide⟩
  m := 5
  T1 := T133_39
  T2 := Q2.T133_39_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_133_39_3 : ColCert where
  rK := ⟨133, by decide⟩
  rH := ⟨39, by decide⟩
  m := 5
  T1 := T133_39
  T2 := Q2.T133_39_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_133_39_4 : ColCert where
  rK := ⟨133, by decide⟩
  rH := ⟨39, by decide⟩
  m := 5
  T1 := T133_39
  T2 := Q2.T133_39_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_133_39_5 : ColCert where
  rK := ⟨133, by decide⟩
  rH := ⟨39, by decide⟩
  m := 5
  T1 := T133_39
  T2 := Q2.T133_39_2
  h1 := (1,4,2,3,2)
  h2 := (1,4,2,3,2)
  D := [[1, 4, 1, 3], [1, 4, 1, 4], [1, 4, 1, 0], [1, 4, 1, 1], [1, 4, 1, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_133_43_0 : ColCert where
  rK := ⟨133, by decide⟩
  rH := ⟨43, by decide⟩
  m := 5
  T1 := T133_43
  T2 := Q2.T133_43_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_133_43_1 : ColCert where
  rK := ⟨133, by decide⟩
  rH := ⟨43, by decide⟩
  m := 5
  T1 := T133_43
  T2 := Q2.T133_43_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_133_43_2 : ColCert where
  rK := ⟨133, by decide⟩
  rH := ⟨43, by decide⟩
  m := 5
  T1 := T133_43
  T2 := Q2.T133_43_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_133_43_3 : ColCert where
  rK := ⟨133, by decide⟩
  rH := ⟨43, by decide⟩
  m := 5
  T1 := T133_43
  T2 := Q2.T133_43_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_133_43_4 : ColCert where
  rK := ⟨133, by decide⟩
  rH := ⟨43, by decide⟩
  m := 5
  T1 := T133_43
  T2 := Q2.T133_43_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_133_50_0 : ColCert where
  rK := ⟨133, by decide⟩
  rH := ⟨50, by decide⟩
  m := 5
  T1 := T133_50
  T2 := Q2.T133_50_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_133_50_1 : ColCert where
  rK := ⟨133, by decide⟩
  rH := ⟨50, by decide⟩
  m := 5
  T1 := T133_50
  T2 := Q2.T133_50_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_133_50_2 : ColCert where
  rK := ⟨133, by decide⟩
  rH := ⟨50, by decide⟩
  m := 5
  T1 := T133_50
  T2 := Q2.T133_50_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_133_50_3 : ColCert where
  rK := ⟨133, by decide⟩
  rH := ⟨50, by decide⟩
  m := 5
  T1 := T133_50
  T2 := Q2.T133_50_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_133_50_4 : ColCert where
  rK := ⟨133, by decide⟩
  rH := ⟨50, by decide⟩
  m := 5
  T1 := T133_50
  T2 := Q2.T133_50_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_133_53_0 : ColCert where
  rK := ⟨133, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T133_53
  T2 := Q2.T133_53_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_133_53_1 : ColCert where
  rK := ⟨133, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T133_53
  T2 := Q2.T133_53_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_133_53_2 : ColCert where
  rK := ⟨133, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T133_53
  T2 := Q2.T133_53_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_133_53_3 : ColCert where
  rK := ⟨133, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T133_53
  T2 := Q2.T133_53_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_133_53_4 : ColCert where
  rK := ⟨133, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T133_53
  T2 := Q2.T133_53_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_133_53_5 : ColCert where
  rK := ⟨133, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T133_53
  T2 := Q2.T133_53_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_133_53_10 : ColCert where
  rK := ⟨133, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T133_53
  T2 := Q2.T133_53_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_133_53_15 : ColCert where
  rK := ⟨133, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T133_53
  T2 := Q2.T133_53_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_133_53_20 : ColCert where
  rK := ⟨133, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T133_53
  T2 := Q2.T133_53_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_133_83_0 : ColCert where
  rK := ⟨133, by decide⟩
  rH := ⟨83, by decide⟩
  m := 5
  T1 := T133_83
  T2 := Q2.T133_83_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_133_83_1 : ColCert where
  rK := ⟨133, by decide⟩
  rH := ⟨83, by decide⟩
  m := 5
  T1 := T133_83
  T2 := Q2.T133_83_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_133_83_2 : ColCert where
  rK := ⟨133, by decide⟩
  rH := ⟨83, by decide⟩
  m := 5
  T1 := T133_83
  T2 := Q2.T133_83_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_133_83_3 : ColCert where
  rK := ⟨133, by decide⟩
  rH := ⟨83, by decide⟩
  m := 5
  T1 := T133_83
  T2 := Q2.T133_83_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_133_83_4 : ColCert where
  rK := ⟨133, by decide⟩
  rH := ⟨83, by decide⟩
  m := 5
  T1 := T133_83
  T2 := Q2.T133_83_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_133_83_5 : ColCert where
  rK := ⟨133, by decide⟩
  rH := ⟨83, by decide⟩
  m := 5
  T1 := T133_83
  T2 := Q2.T133_83_2
  h1 := (1,0,3,0,0)
  h2 := (1,0,3,0,0)
  D := [[1, 0, 2, 2], [1, 0, 2, 2], [1, 0, 2, 2], [1, 0, 2, 2], [1, 0, 2, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_133_83_10 : ColCert where
  rK := ⟨133, by decide⟩
  rH := ⟨83, by decide⟩
  m := 5
  T1 := T133_83
  T2 := Q2.T133_83_2
  h1 := (2,0,1,0,0)
  h2 := (2,0,1,0,0)
  D := [[2, 0, 4, 2], [2, 0, 4, 2], [2, 0, 4, 2], [2, 0, 4, 2], [2, 0, 4, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_133_83_15 : ColCert where
  rK := ⟨133, by decide⟩
  rH := ⟨83, by decide⟩
  m := 5
  T1 := T133_83
  T2 := Q2.T133_83_2
  h1 := (3,0,4,0,0)
  h2 := (3,0,4,0,0)
  D := [[3, 0, 1, 0], [3, 0, 1, 0], [3, 0, 1, 0], [3, 0, 1, 0], [3, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_133_83_20 : ColCert where
  rK := ⟨133, by decide⟩
  rH := ⟨83, by decide⟩
  m := 5
  T1 := T133_83
  T2 := Q2.T133_83_2
  h1 := (4,0,2,0,0)
  h2 := (4,0,2,0,0)
  D := [[4, 0, 3, 1], [4, 0, 3, 1], [4, 0, 3, 1], [4, 0, 3, 1], [4, 0, 3, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_133_94_0 : ColCert where
  rK := ⟨133, by decide⟩
  rH := ⟨94, by decide⟩
  m := 5
  T1 := T133_94
  T2 := Q2.T133_94_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_133_94_1 : ColCert where
  rK := ⟨133, by decide⟩
  rH := ⟨94, by decide⟩
  m := 5
  T1 := T133_94
  T2 := Q2.T133_94_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_133_94_2 : ColCert where
  rK := ⟨133, by decide⟩
  rH := ⟨94, by decide⟩
  m := 5
  T1 := T133_94
  T2 := Q2.T133_94_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_133_94_3 : ColCert where
  rK := ⟨133, by decide⟩
  rH := ⟨94, by decide⟩
  m := 5
  T1 := T133_94
  T2 := Q2.T133_94_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_133_94_4 : ColCert where
  rK := ⟨133, by decide⟩
  rH := ⟨94, by decide⟩
  m := 5
  T1 := T133_94
  T2 := Q2.T133_94_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_133_94_5 : ColCert where
  rK := ⟨133, by decide⟩
  rH := ⟨94, by decide⟩
  m := 5
  T1 := T133_94
  T2 := Q2.T133_94_2
  h1 := (1,1,4,0,0)
  h2 := (1,1,4,0,0)
  D := [[1, 1, 1, 4], [1, 1, 1, 3], [1, 1, 1, 2], [1, 1, 1, 1], [1, 1, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_133_94_10 : ColCert where
  rK := ⟨133, by decide⟩
  rH := ⟨94, by decide⟩
  m := 5
  T1 := T133_94
  T2 := Q2.T133_94_2
  h1 := (2,2,3,1,4)
  h2 := (2,2,3,1,4)
  D := [[2, 2, 1, 1], [2, 2, 1, 4], [2, 2, 1, 2], [2, 2, 1, 0], [2, 2, 1, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_133_94_15 : ColCert where
  rK := ⟨133, by decide⟩
  rH := ⟨94, by decide⟩
  m := 5
  T1 := T133_94
  T2 := Q2.T133_94_2
  h1 := (3,3,2,3,3)
  h2 := (3,3,2,3,3)
  D := [[3, 3, 0, 2], [3, 3, 0, 4], [3, 3, 0, 1], [3, 3, 0, 3], [3, 3, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_133_94_20 : ColCert where
  rK := ⟨133, by decide⟩
  rH := ⟨94, by decide⟩
  m := 5
  T1 := T133_94
  T2 := Q2.T133_94_2
  h1 := (4,4,1,1,3)
  h2 := (4,4,1,1,3)
  D := [[4, 4, 3, 3], [4, 4, 3, 4], [4, 4, 3, 0], [4, 4, 3, 1], [4, 4, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_133_98_0 : ColCert where
  rK := ⟨133, by decide⟩
  rH := ⟨98, by decide⟩
  m := 5
  T1 := T133_98
  T2 := Q2.T133_98_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

end LeanDring.P5Presentation
