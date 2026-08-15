/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.Twin1.ColCert
import LeanDring.P5.Data.EntryK.C029

/-!
# Species-table cell data, stage 2 — twin-coincident columns (cheap tier)

Per-column certified exponent-vector data (`ColCert`/`ColCertDiv`) with kernel
`decide` bindings. Emitted; the embedded lists are what the kernel certifies.
rest tier, chunk 42: 60 columns.
-/

-- machine-emitted data: silence style linters (generated long lines, file-level options)
set_option linter.style.longLine false

namespace LeanDring.P5Presentation

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

def colCert_120_26_10 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨26, by decide⟩
  m := 5
  T1 := T120_26
  T2 := Q2.T120_26_2
  h1 := (0,0,2,2,0)
  h2 := (0,0,2,2,0)
  D := [[0, 2, 2, 2], [0, 2, 2, 4], [0, 2, 2, 1], [0, 2, 2, 3], [0, 2, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_26_15 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨26, by decide⟩
  m := 5
  T1 := T120_26
  T2 := Q2.T120_26_2
  h1 := (0,0,3,3,0)
  h2 := (0,0,3,3,0)
  D := [[0, 3, 3, 3], [0, 3, 3, 1], [0, 3, 3, 4], [0, 3, 3, 2], [0, 3, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_26_20 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨26, by decide⟩
  m := 5
  T1 := T120_26
  T2 := Q2.T120_26_2
  h1 := (0,0,4,4,0)
  h2 := (0,0,4,4,0)
  D := [[0, 4, 4, 4], [0, 4, 4, 3], [0, 4, 4, 2], [0, 4, 4, 1], [0, 4, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_27_0 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨27, by decide⟩
  m := 5
  T1 := T120_27
  T2 := Q2.T120_27_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_27_1 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨27, by decide⟩
  m := 5
  T1 := T120_27
  T2 := Q2.T120_27_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_27_2 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨27, by decide⟩
  m := 5
  T1 := T120_27
  T2 := Q2.T120_27_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_27_3 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨27, by decide⟩
  m := 5
  T1 := T120_27
  T2 := Q2.T120_27_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_27_4 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨27, by decide⟩
  m := 5
  T1 := T120_27
  T2 := Q2.T120_27_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_27_5 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨27, by decide⟩
  m := 5
  T1 := T120_27
  T2 := Q2.T120_27_2
  h1 := (0,0,1,0,0)
  h2 := (0,0,1,0,0)
  D := [[0, 1, 0, 1], [0, 1, 0, 2], [0, 1, 0, 3], [0, 1, 0, 4], [0, 1, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_27_10 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨27, by decide⟩
  m := 5
  T1 := T120_27
  T2 := Q2.T120_27_2
  h1 := (0,0,2,0,0)
  h2 := (0,0,2,0,0)
  D := [[0, 2, 0, 2], [0, 2, 0, 4], [0, 2, 0, 1], [0, 2, 0, 3], [0, 2, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_27_15 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨27, by decide⟩
  m := 5
  T1 := T120_27
  T2 := Q2.T120_27_2
  h1 := (0,0,3,0,0)
  h2 := (0,0,3,0,0)
  D := [[0, 3, 0, 3], [0, 3, 0, 1], [0, 3, 0, 4], [0, 3, 0, 2], [0, 3, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_27_20 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨27, by decide⟩
  m := 5
  T1 := T120_27
  T2 := Q2.T120_27_2
  h1 := (0,0,4,0,0)
  h2 := (0,0,4,0,0)
  D := [[0, 4, 0, 4], [0, 4, 0, 3], [0, 4, 0, 2], [0, 4, 0, 1], [0, 4, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_32_0 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨32, by decide⟩
  m := 5
  T1 := T120_32
  T2 := Q2.T120_32_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_32_1 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨32, by decide⟩
  m := 5
  T1 := T120_32
  T2 := Q2.T120_32_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_32_2 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨32, by decide⟩
  m := 5
  T1 := T120_32
  T2 := Q2.T120_32_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_32_3 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨32, by decide⟩
  m := 5
  T1 := T120_32
  T2 := Q2.T120_32_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_32_4 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨32, by decide⟩
  m := 5
  T1 := T120_32
  T2 := Q2.T120_32_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_37_0 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨37, by decide⟩
  m := 5
  T1 := T120_37
  T2 := Q2.T120_37_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_37_1 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨37, by decide⟩
  m := 5
  T1 := T120_37
  T2 := Q2.T120_37_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_37_2 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨37, by decide⟩
  m := 5
  T1 := T120_37
  T2 := Q2.T120_37_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_37_3 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨37, by decide⟩
  m := 5
  T1 := T120_37
  T2 := Q2.T120_37_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_37_4 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨37, by decide⟩
  m := 5
  T1 := T120_37
  T2 := Q2.T120_37_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_42_0 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨42, by decide⟩
  m := 5
  T1 := T120_42
  T2 := Q2.T120_42_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_42_1 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨42, by decide⟩
  m := 5
  T1 := T120_42
  T2 := Q2.T120_42_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_42_2 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨42, by decide⟩
  m := 5
  T1 := T120_42
  T2 := Q2.T120_42_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_42_3 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨42, by decide⟩
  m := 5
  T1 := T120_42
  T2 := Q2.T120_42_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_42_4 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨42, by decide⟩
  m := 5
  T1 := T120_42
  T2 := Q2.T120_42_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_47_0 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨47, by decide⟩
  m := 5
  T1 := T120_47
  T2 := Q2.T120_47_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_47_1 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨47, by decide⟩
  m := 5
  T1 := T120_47
  T2 := Q2.T120_47_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_47_2 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨47, by decide⟩
  m := 5
  T1 := T120_47
  T2 := Q2.T120_47_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_47_3 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨47, by decide⟩
  m := 5
  T1 := T120_47
  T2 := Q2.T120_47_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_47_4 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨47, by decide⟩
  m := 5
  T1 := T120_47
  T2 := Q2.T120_47_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_52_0 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨52, by decide⟩
  m := 5
  T1 := T120_52
  T2 := Q2.T120_52_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_52_1 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨52, by decide⟩
  m := 5
  T1 := T120_52
  T2 := Q2.T120_52_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_52_2 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨52, by decide⟩
  m := 5
  T1 := T120_52
  T2 := Q2.T120_52_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_52_3 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨52, by decide⟩
  m := 5
  T1 := T120_52
  T2 := Q2.T120_52_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_52_4 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨52, by decide⟩
  m := 5
  T1 := T120_52
  T2 := Q2.T120_52_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_53_0 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T120_53
  T2 := Q2.T120_53_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_53_1 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T120_53
  T2 := Q2.T120_53_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_53_2 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T120_53
  T2 := Q2.T120_53_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_53_3 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T120_53
  T2 := Q2.T120_53_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_53_4 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T120_53
  T2 := Q2.T120_53_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_53_5 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T120_53
  T2 := Q2.T120_53_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_53_10 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T120_53
  T2 := Q2.T120_53_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_53_15 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T120_53
  T2 := Q2.T120_53_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_53_20 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T120_53
  T2 := Q2.T120_53_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_75_0 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨75, by decide⟩
  m := 5
  T1 := T120_75
  T2 := Q2.T120_75_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_75_1 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨75, by decide⟩
  m := 5
  T1 := T120_75
  T2 := Q2.T120_75_2
  h1 := (0,0,1,0,0)
  h2 := (0,0,1,0,0)
  D := [[0, 1, 0, 1], [0, 1, 0, 2], [0, 1, 0, 3], [0, 1, 0, 4], [0, 1, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_75_2 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨75, by decide⟩
  m := 5
  T1 := T120_75
  T2 := Q2.T120_75_2
  h1 := (0,0,2,0,0)
  h2 := (0,0,2,0,0)
  D := [[0, 2, 0, 2], [0, 2, 0, 4], [0, 2, 0, 1], [0, 2, 0, 3], [0, 2, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_75_3 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨75, by decide⟩
  m := 5
  T1 := T120_75
  T2 := Q2.T120_75_2
  h1 := (0,0,3,0,0)
  h2 := (0,0,3,0,0)
  D := [[0, 3, 0, 3], [0, 3, 0, 1], [0, 3, 0, 4], [0, 3, 0, 2], [0, 3, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_75_4 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨75, by decide⟩
  m := 5
  T1 := T120_75
  T2 := Q2.T120_75_2
  h1 := (0,0,4,0,0)
  h2 := (0,0,4,0,0)
  D := [[0, 4, 0, 4], [0, 4, 0, 3], [0, 4, 0, 2], [0, 4, 0, 1], [0, 4, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_76_0 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨76, by decide⟩
  m := 5
  T1 := T120_76
  T2 := Q2.T120_76_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_76_1 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨76, by decide⟩
  m := 5
  T1 := T120_76
  T2 := Q2.T120_76_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_76_2 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨76, by decide⟩
  m := 5
  T1 := T120_76
  T2 := Q2.T120_76_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_76_3 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨76, by decide⟩
  m := 5
  T1 := T120_76
  T2 := Q2.T120_76_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_76_4 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨76, by decide⟩
  m := 5
  T1 := T120_76
  T2 := Q2.T120_76_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_76_5 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨76, by decide⟩
  m := 5
  T1 := T120_76
  T2 := Q2.T120_76_2
  h1 := (0,0,1,4,0)
  h2 := (0,0,1,4,0)
  D := [[0, 1, 4, 1], [0, 1, 4, 2], [0, 1, 4, 3], [0, 1, 4, 4], [0, 1, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_76_6 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨76, by decide⟩
  m := 5
  T1 := T120_76
  T2 := Q2.T120_76_2
  h1 := (0,0,1,4,1)
  h2 := (0,0,1,4,1)
  D := [[0, 1, 4, 2], [0, 1, 4, 3], [0, 1, 4, 4], [0, 1, 4, 0], [0, 1, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_76_7 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨76, by decide⟩
  m := 5
  T1 := T120_76
  T2 := Q2.T120_76_2
  h1 := (0,0,1,4,2)
  h2 := (0,0,1,4,2)
  D := [[0, 1, 4, 3], [0, 1, 4, 4], [0, 1, 4, 0], [0, 1, 4, 1], [0, 1, 4, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_120_76_8 : ColCert where
  rK := ⟨120, by decide⟩
  rH := ⟨76, by decide⟩
  m := 5
  T1 := T120_76
  T2 := Q2.T120_76_2
  h1 := (0,0,1,4,3)
  h2 := (0,0,1,4,3)
  D := [[0, 1, 4, 4], [0, 1, 4, 0], [0, 1, 4, 1], [0, 1, 4, 2], [0, 1, 4, 3]]
  bind1 := by decide
  bind2 := by decide

end LeanDring.P5Presentation
