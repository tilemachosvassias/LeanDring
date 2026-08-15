/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.Twin1.ColCert
import LeanDring.P5.Data.EntryK.C034

/-!
# Species-table cell data, stage 2 — twin-coincident columns (cheap tier)

Per-column certified exponent-vector data (`ColCert`/`ColCertDiv`) with kernel
`decide` bindings. Emitted; the embedded lists are what the kernel certifies.
rest tier, chunk 67: 60 columns.
-/

-- machine-emitted data: silence style linters (generated long lines, file-level options)
set_option linter.style.longLine false

namespace LeanDring.P5Presentation

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

def colCert_131_30_3 : ColCert where
  rK := ⟨131, by decide⟩
  rH := ⟨30, by decide⟩
  m := 5
  T1 := T131_30
  T2 := Q2.T131_30_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_131_30_4 : ColCert where
  rK := ⟨131, by decide⟩
  rH := ⟨30, by decide⟩
  m := 5
  T1 := T131_30
  T2 := Q2.T131_30_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_131_34_0 : ColCert where
  rK := ⟨131, by decide⟩
  rH := ⟨34, by decide⟩
  m := 5
  T1 := T131_34
  T2 := Q2.T131_34_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_131_34_1 : ColCert where
  rK := ⟨131, by decide⟩
  rH := ⟨34, by decide⟩
  m := 5
  T1 := T131_34
  T2 := Q2.T131_34_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_131_34_2 : ColCert where
  rK := ⟨131, by decide⟩
  rH := ⟨34, by decide⟩
  m := 5
  T1 := T131_34
  T2 := Q2.T131_34_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_131_34_3 : ColCert where
  rK := ⟨131, by decide⟩
  rH := ⟨34, by decide⟩
  m := 5
  T1 := T131_34
  T2 := Q2.T131_34_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_131_34_4 : ColCert where
  rK := ⟨131, by decide⟩
  rH := ⟨34, by decide⟩
  m := 5
  T1 := T131_34
  T2 := Q2.T131_34_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_131_34_5 : ColCert where
  rK := ⟨131, by decide⟩
  rH := ⟨34, by decide⟩
  m := 5
  T1 := T131_34
  T2 := Q2.T131_34_2
  h1 := (1,4,3,3,1)
  h2 := (1,4,3,3,1)
  D := [[1, 4, 4, 0], [1, 4, 4, 1], [1, 4, 4, 2], [1, 4, 4, 3], [1, 4, 4, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_131_42_0 : ColCert where
  rK := ⟨131, by decide⟩
  rH := ⟨42, by decide⟩
  m := 5
  T1 := T131_42
  T2 := Q2.T131_42_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_131_42_1 : ColCert where
  rK := ⟨131, by decide⟩
  rH := ⟨42, by decide⟩
  m := 5
  T1 := T131_42
  T2 := Q2.T131_42_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_131_42_2 : ColCert where
  rK := ⟨131, by decide⟩
  rH := ⟨42, by decide⟩
  m := 5
  T1 := T131_42
  T2 := Q2.T131_42_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_131_42_3 : ColCert where
  rK := ⟨131, by decide⟩
  rH := ⟨42, by decide⟩
  m := 5
  T1 := T131_42
  T2 := Q2.T131_42_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_131_42_4 : ColCert where
  rK := ⟨131, by decide⟩
  rH := ⟨42, by decide⟩
  m := 5
  T1 := T131_42
  T2 := Q2.T131_42_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_131_46_0 : ColCert where
  rK := ⟨131, by decide⟩
  rH := ⟨46, by decide⟩
  m := 5
  T1 := T131_46
  T2 := Q2.T131_46_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_131_46_1 : ColCert where
  rK := ⟨131, by decide⟩
  rH := ⟨46, by decide⟩
  m := 5
  T1 := T131_46
  T2 := Q2.T131_46_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_131_46_2 : ColCert where
  rK := ⟨131, by decide⟩
  rH := ⟨46, by decide⟩
  m := 5
  T1 := T131_46
  T2 := Q2.T131_46_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_131_46_3 : ColCert where
  rK := ⟨131, by decide⟩
  rH := ⟨46, by decide⟩
  m := 5
  T1 := T131_46
  T2 := Q2.T131_46_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_131_46_4 : ColCert where
  rK := ⟨131, by decide⟩
  rH := ⟨46, by decide⟩
  m := 5
  T1 := T131_46
  T2 := Q2.T131_46_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_131_48_0 : ColCert where
  rK := ⟨131, by decide⟩
  rH := ⟨48, by decide⟩
  m := 5
  T1 := T131_48
  T2 := Q2.T131_48_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_131_48_1 : ColCert where
  rK := ⟨131, by decide⟩
  rH := ⟨48, by decide⟩
  m := 5
  T1 := T131_48
  T2 := Q2.T131_48_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_131_48_2 : ColCert where
  rK := ⟨131, by decide⟩
  rH := ⟨48, by decide⟩
  m := 5
  T1 := T131_48
  T2 := Q2.T131_48_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_131_48_3 : ColCert where
  rK := ⟨131, by decide⟩
  rH := ⟨48, by decide⟩
  m := 5
  T1 := T131_48
  T2 := Q2.T131_48_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_131_48_4 : ColCert where
  rK := ⟨131, by decide⟩
  rH := ⟨48, by decide⟩
  m := 5
  T1 := T131_48
  T2 := Q2.T131_48_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_131_53_0 : ColCert where
  rK := ⟨131, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T131_53
  T2 := Q2.T131_53_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_131_53_1 : ColCert where
  rK := ⟨131, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T131_53
  T2 := Q2.T131_53_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_131_53_2 : ColCert where
  rK := ⟨131, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T131_53
  T2 := Q2.T131_53_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_131_53_3 : ColCert where
  rK := ⟨131, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T131_53
  T2 := Q2.T131_53_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_131_53_4 : ColCert where
  rK := ⟨131, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T131_53
  T2 := Q2.T131_53_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_131_53_5 : ColCert where
  rK := ⟨131, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T131_53
  T2 := Q2.T131_53_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_131_53_10 : ColCert where
  rK := ⟨131, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T131_53
  T2 := Q2.T131_53_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_131_53_15 : ColCert where
  rK := ⟨131, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T131_53
  T2 := Q2.T131_53_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_131_53_20 : ColCert where
  rK := ⟨131, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T131_53
  T2 := Q2.T131_53_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_131_83_0 : ColCert where
  rK := ⟨131, by decide⟩
  rH := ⟨83, by decide⟩
  m := 5
  T1 := T131_83
  T2 := Q2.T131_83_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_131_83_1 : ColCert where
  rK := ⟨131, by decide⟩
  rH := ⟨83, by decide⟩
  m := 5
  T1 := T131_83
  T2 := Q2.T131_83_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_131_83_2 : ColCert where
  rK := ⟨131, by decide⟩
  rH := ⟨83, by decide⟩
  m := 5
  T1 := T131_83
  T2 := Q2.T131_83_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_131_83_3 : ColCert where
  rK := ⟨131, by decide⟩
  rH := ⟨83, by decide⟩
  m := 5
  T1 := T131_83
  T2 := Q2.T131_83_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_131_83_4 : ColCert where
  rK := ⟨131, by decide⟩
  rH := ⟨83, by decide⟩
  m := 5
  T1 := T131_83
  T2 := Q2.T131_83_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_131_83_5 : ColCert where
  rK := ⟨131, by decide⟩
  rH := ⟨83, by decide⟩
  m := 5
  T1 := T131_83
  T2 := Q2.T131_83_2
  h1 := (1,0,3,0,0)
  h2 := (1,0,3,0,0)
  D := [[1, 0, 0, 0], [1, 0, 0, 0], [1, 0, 0, 0], [1, 0, 0, 0], [1, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_131_83_10 : ColCert where
  rK := ⟨131, by decide⟩
  rH := ⟨83, by decide⟩
  m := 5
  T1 := T131_83
  T2 := Q2.T131_83_2
  h1 := (2,0,1,0,0)
  h2 := (2,0,1,0,0)
  D := [[2, 0, 0, 0], [2, 0, 0, 0], [2, 0, 0, 0], [2, 0, 0, 0], [2, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_131_83_15 : ColCert where
  rK := ⟨131, by decide⟩
  rH := ⟨83, by decide⟩
  m := 5
  T1 := T131_83
  T2 := Q2.T131_83_2
  h1 := (3,0,4,0,0)
  h2 := (3,0,4,0,0)
  D := [[3, 0, 0, 0], [3, 0, 0, 0], [3, 0, 0, 0], [3, 0, 0, 0], [3, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_131_83_20 : ColCert where
  rK := ⟨131, by decide⟩
  rH := ⟨83, by decide⟩
  m := 5
  T1 := T131_83
  T2 := Q2.T131_83_2
  h1 := (4,0,2,0,0)
  h2 := (4,0,2,0,0)
  D := [[4, 0, 0, 0], [4, 0, 0, 0], [4, 0, 0, 0], [4, 0, 0, 0], [4, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_131_92_0 : ColCert where
  rK := ⟨131, by decide⟩
  rH := ⟨92, by decide⟩
  m := 5
  T1 := T131_92
  T2 := Q2.T131_92_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_131_92_1 : ColCert where
  rK := ⟨131, by decide⟩
  rH := ⟨92, by decide⟩
  m := 5
  T1 := T131_92
  T2 := Q2.T131_92_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_131_92_2 : ColCert where
  rK := ⟨131, by decide⟩
  rH := ⟨92, by decide⟩
  m := 5
  T1 := T131_92
  T2 := Q2.T131_92_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_131_92_3 : ColCert where
  rK := ⟨131, by decide⟩
  rH := ⟨92, by decide⟩
  m := 5
  T1 := T131_92
  T2 := Q2.T131_92_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_131_92_4 : ColCert where
  rK := ⟨131, by decide⟩
  rH := ⟨92, by decide⟩
  m := 5
  T1 := T131_92
  T2 := Q2.T131_92_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_131_92_5 : ColCert where
  rK := ⟨131, by decide⟩
  rH := ⟨92, by decide⟩
  m := 5
  T1 := T131_92
  T2 := Q2.T131_92_2
  h1 := (1,2,3,3,2)
  h2 := (1,2,3,3,2)
  D := [[1, 2, 1, 0], [1, 2, 1, 3], [1, 2, 1, 1], [1, 2, 1, 4], [1, 2, 1, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_131_92_10 : ColCert where
  rK := ⟨131, by decide⟩
  rH := ⟨92, by decide⟩
  m := 5
  T1 := T131_92
  T2 := Q2.T131_92_2
  h1 := (2,4,1,3,3)
  h2 := (2,4,1,3,3)
  D := [[2, 4, 0, 2], [2, 4, 0, 3], [2, 4, 0, 4], [2, 4, 0, 0], [2, 4, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_131_96_0 : ColCert where
  rK := ⟨131, by decide⟩
  rH := ⟨96, by decide⟩
  m := 5
  T1 := T131_96
  T2 := Q2.T131_96_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_131_96_1 : ColCert where
  rK := ⟨131, by decide⟩
  rH := ⟨96, by decide⟩
  m := 5
  T1 := T131_96
  T2 := Q2.T131_96_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_131_96_2 : ColCert where
  rK := ⟨131, by decide⟩
  rH := ⟨96, by decide⟩
  m := 5
  T1 := T131_96
  T2 := Q2.T131_96_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_131_96_3 : ColCert where
  rK := ⟨131, by decide⟩
  rH := ⟨96, by decide⟩
  m := 5
  T1 := T131_96
  T2 := Q2.T131_96_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_131_96_4 : ColCert where
  rK := ⟨131, by decide⟩
  rH := ⟨96, by decide⟩
  m := 5
  T1 := T131_96
  T2 := Q2.T131_96_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_131_96_5 : ColCert where
  rK := ⟨131, by decide⟩
  rH := ⟨96, by decide⟩
  m := 5
  T1 := T131_96
  T2 := Q2.T131_96_2
  h1 := (1,4,3,4,2)
  h2 := (1,4,3,4,2)
  D := [[1, 4, 0, 0], [1, 4, 0, 1], [1, 4, 0, 2], [1, 4, 0, 3], [1, 4, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_131_104_0 : ColCert where
  rK := ⟨131, by decide⟩
  rH := ⟨104, by decide⟩
  m := 5
  T1 := T131_104
  T2 := Q2.T131_104_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_131_104_1 : ColCert where
  rK := ⟨131, by decide⟩
  rH := ⟨104, by decide⟩
  m := 5
  T1 := T131_104
  T2 := Q2.T131_104_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_131_104_2 : ColCert where
  rK := ⟨131, by decide⟩
  rH := ⟨104, by decide⟩
  m := 5
  T1 := T131_104
  T2 := Q2.T131_104_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_131_104_3 : ColCert where
  rK := ⟨131, by decide⟩
  rH := ⟨104, by decide⟩
  m := 5
  T1 := T131_104
  T2 := Q2.T131_104_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_131_104_4 : ColCert where
  rK := ⟨131, by decide⟩
  rH := ⟨104, by decide⟩
  m := 5
  T1 := T131_104
  T2 := Q2.T131_104_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_131_104_5 : ColCert where
  rK := ⟨131, by decide⟩
  rH := ⟨104, by decide⟩
  m := 5
  T1 := T131_104
  T2 := Q2.T131_104_2
  h1 := (1,1,3,0,0)
  h2 := (1,1,3,0,0)
  D := [[1, 1, 4, 3], [1, 1, 4, 2], [1, 1, 4, 1], [1, 1, 4, 0], [1, 1, 4, 4]]
  bind1 := by decide
  bind2 := by decide

end LeanDring.P5Presentation
