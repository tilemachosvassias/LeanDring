/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.Twin1.ColCert
import LeanDring.P5.Data.EntryK.C036

/-!
# Species-table cell data, stage 2 — twin-coincident columns (cheap tier)

Per-column certified exponent-vector data (`ColCert`/`ColCertDiv`) with kernel
`decide` bindings. Emitted; the embedded lists are what the kernel certifies.
rest tier, chunk 75: 60 columns.
-/

-- machine-emitted data: silence style linters (generated long lines, file-level options)
set_option linter.style.longLine false

namespace LeanDring.P5Presentation

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

def colCert_135_10_2 : ColCert where
  rK := ⟨135, by decide⟩
  rH := ⟨10, by decide⟩
  m := 5
  T1 := T135_10
  T2 := Q2.T135_10_2
  h1 := (0,0,0,2,3)
  h2 := (0,0,0,2,3)
  D := [[0, 0, 2, 3], [0, 0, 2, 3], [0, 0, 2, 3], [0, 0, 2, 3], [0, 0, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_135_10_3 : ColCert where
  rK := ⟨135, by decide⟩
  rH := ⟨10, by decide⟩
  m := 5
  T1 := T135_10
  T2 := Q2.T135_10_2
  h1 := (0,0,0,3,2)
  h2 := (0,0,0,3,2)
  D := [[0, 0, 3, 2], [0, 0, 3, 2], [0, 0, 3, 2], [0, 0, 3, 2], [0, 0, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_135_10_4 : ColCert where
  rK := ⟨135, by decide⟩
  rH := ⟨10, by decide⟩
  m := 5
  T1 := T135_10
  T2 := Q2.T135_10_2
  h1 := (0,0,0,4,1)
  h2 := (0,0,0,4,1)
  D := [[0, 0, 4, 1], [0, 0, 4, 1], [0, 0, 4, 1], [0, 0, 4, 1], [0, 0, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_135_12_0 : ColCert where
  rK := ⟨135, by decide⟩
  rH := ⟨12, by decide⟩
  m := 5
  T1 := T135_12
  T2 := Q2.T135_12_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_135_12_1 : ColCert where
  rK := ⟨135, by decide⟩
  rH := ⟨12, by decide⟩
  m := 5
  T1 := T135_12
  T2 := Q2.T135_12_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_135_12_2 : ColCert where
  rK := ⟨135, by decide⟩
  rH := ⟨12, by decide⟩
  m := 5
  T1 := T135_12
  T2 := Q2.T135_12_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_135_12_3 : ColCert where
  rK := ⟨135, by decide⟩
  rH := ⟨12, by decide⟩
  m := 5
  T1 := T135_12
  T2 := Q2.T135_12_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_135_12_4 : ColCert where
  rK := ⟨135, by decide⟩
  rH := ⟨12, by decide⟩
  m := 5
  T1 := T135_12
  T2 := Q2.T135_12_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_135_22_0 : ColCert where
  rK := ⟨135, by decide⟩
  rH := ⟨22, by decide⟩
  m := 5
  T1 := T135_22
  T2 := Q2.T135_22_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_135_22_1 : ColCert where
  rK := ⟨135, by decide⟩
  rH := ⟨22, by decide⟩
  m := 5
  T1 := T135_22
  T2 := Q2.T135_22_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_135_22_2 : ColCert where
  rK := ⟨135, by decide⟩
  rH := ⟨22, by decide⟩
  m := 5
  T1 := T135_22
  T2 := Q2.T135_22_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_135_22_3 : ColCert where
  rK := ⟨135, by decide⟩
  rH := ⟨22, by decide⟩
  m := 5
  T1 := T135_22
  T2 := Q2.T135_22_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_135_22_4 : ColCert where
  rK := ⟨135, by decide⟩
  rH := ⟨22, by decide⟩
  m := 5
  T1 := T135_22
  T2 := Q2.T135_22_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_135_29_0 : ColCert where
  rK := ⟨135, by decide⟩
  rH := ⟨29, by decide⟩
  m := 5
  T1 := T135_29
  T2 := Q2.T135_29_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_135_29_1 : ColCert where
  rK := ⟨135, by decide⟩
  rH := ⟨29, by decide⟩
  m := 5
  T1 := T135_29
  T2 := Q2.T135_29_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_135_29_2 : ColCert where
  rK := ⟨135, by decide⟩
  rH := ⟨29, by decide⟩
  m := 5
  T1 := T135_29
  T2 := Q2.T135_29_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_135_29_3 : ColCert where
  rK := ⟨135, by decide⟩
  rH := ⟨29, by decide⟩
  m := 5
  T1 := T135_29
  T2 := Q2.T135_29_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_135_29_4 : ColCert where
  rK := ⟨135, by decide⟩
  rH := ⟨29, by decide⟩
  m := 5
  T1 := T135_29
  T2 := Q2.T135_29_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_135_29_10 : ColCert where
  rK := ⟨135, by decide⟩
  rH := ⟨29, by decide⟩
  m := 5
  T1 := T135_29
  T2 := Q2.T135_29_2
  h1 := (2,3,2,0,4)
  h2 := (2,3,2,0,0)
  D := [[2, 3, 4, 4], [2, 3, 4, 1], [2, 3, 4, 3], [2, 3, 4, 0], [2, 3, 4, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_135_33_0 : ColCert where
  rK := ⟨135, by decide⟩
  rH := ⟨33, by decide⟩
  m := 5
  T1 := T135_33
  T2 := Q2.T135_33_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_135_33_1 : ColCert where
  rK := ⟨135, by decide⟩
  rH := ⟨33, by decide⟩
  m := 5
  T1 := T135_33
  T2 := Q2.T135_33_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_135_33_2 : ColCert where
  rK := ⟨135, by decide⟩
  rH := ⟨33, by decide⟩
  m := 5
  T1 := T135_33
  T2 := Q2.T135_33_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_135_33_3 : ColCert where
  rK := ⟨135, by decide⟩
  rH := ⟨33, by decide⟩
  m := 5
  T1 := T135_33
  T2 := Q2.T135_33_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_135_33_4 : ColCert where
  rK := ⟨135, by decide⟩
  rH := ⟨33, by decide⟩
  m := 5
  T1 := T135_33
  T2 := Q2.T135_33_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_135_41_0 : ColCert where
  rK := ⟨135, by decide⟩
  rH := ⟨41, by decide⟩
  m := 5
  T1 := T135_41
  T2 := Q2.T135_41_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_135_41_1 : ColCert where
  rK := ⟨135, by decide⟩
  rH := ⟨41, by decide⟩
  m := 5
  T1 := T135_41
  T2 := Q2.T135_41_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_135_41_2 : ColCert where
  rK := ⟨135, by decide⟩
  rH := ⟨41, by decide⟩
  m := 5
  T1 := T135_41
  T2 := Q2.T135_41_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_135_41_3 : ColCert where
  rK := ⟨135, by decide⟩
  rH := ⟨41, by decide⟩
  m := 5
  T1 := T135_41
  T2 := Q2.T135_41_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_135_41_4 : ColCert where
  rK := ⟨135, by decide⟩
  rH := ⟨41, by decide⟩
  m := 5
  T1 := T135_41
  T2 := Q2.T135_41_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_135_45_0 : ColCert where
  rK := ⟨135, by decide⟩
  rH := ⟨45, by decide⟩
  m := 5
  T1 := T135_45
  T2 := Q2.T135_45_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_135_45_1 : ColCert where
  rK := ⟨135, by decide⟩
  rH := ⟨45, by decide⟩
  m := 5
  T1 := T135_45
  T2 := Q2.T135_45_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_135_45_2 : ColCert where
  rK := ⟨135, by decide⟩
  rH := ⟨45, by decide⟩
  m := 5
  T1 := T135_45
  T2 := Q2.T135_45_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_135_45_3 : ColCert where
  rK := ⟨135, by decide⟩
  rH := ⟨45, by decide⟩
  m := 5
  T1 := T135_45
  T2 := Q2.T135_45_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_135_45_4 : ColCert where
  rK := ⟨135, by decide⟩
  rH := ⟨45, by decide⟩
  m := 5
  T1 := T135_45
  T2 := Q2.T135_45_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_135_45_20 : ColCert where
  rK := ⟨135, by decide⟩
  rH := ⟨45, by decide⟩
  m := 5
  T1 := T135_45
  T2 := Q2.T135_45_2
  h1 := (4,3,3,0,4)
  h2 := (4,3,3,0,3)
  D := [[4, 3, 3, 4], [4, 3, 3, 1], [4, 3, 3, 3], [4, 3, 3, 0], [4, 3, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_135_52_0 : ColCert where
  rK := ⟨135, by decide⟩
  rH := ⟨52, by decide⟩
  m := 5
  T1 := T135_52
  T2 := Q2.T135_52_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_135_52_1 : ColCert where
  rK := ⟨135, by decide⟩
  rH := ⟨52, by decide⟩
  m := 5
  T1 := T135_52
  T2 := Q2.T135_52_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_135_52_2 : ColCert where
  rK := ⟨135, by decide⟩
  rH := ⟨52, by decide⟩
  m := 5
  T1 := T135_52
  T2 := Q2.T135_52_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_135_52_3 : ColCert where
  rK := ⟨135, by decide⟩
  rH := ⟨52, by decide⟩
  m := 5
  T1 := T135_52
  T2 := Q2.T135_52_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_135_52_4 : ColCert where
  rK := ⟨135, by decide⟩
  rH := ⟨52, by decide⟩
  m := 5
  T1 := T135_52
  T2 := Q2.T135_52_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_135_53_0 : ColCert where
  rK := ⟨135, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T135_53
  T2 := Q2.T135_53_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_135_53_1 : ColCert where
  rK := ⟨135, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T135_53
  T2 := Q2.T135_53_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_135_53_2 : ColCert where
  rK := ⟨135, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T135_53
  T2 := Q2.T135_53_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_135_53_3 : ColCert where
  rK := ⟨135, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T135_53
  T2 := Q2.T135_53_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_135_53_4 : ColCert where
  rK := ⟨135, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T135_53
  T2 := Q2.T135_53_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_135_53_5 : ColCert where
  rK := ⟨135, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T135_53
  T2 := Q2.T135_53_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_135_53_10 : ColCert where
  rK := ⟨135, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T135_53
  T2 := Q2.T135_53_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_135_53_15 : ColCert where
  rK := ⟨135, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T135_53
  T2 := Q2.T135_53_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_135_53_20 : ColCert where
  rK := ⟨135, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T135_53
  T2 := Q2.T135_53_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_135_83_0 : ColCert where
  rK := ⟨135, by decide⟩
  rH := ⟨83, by decide⟩
  m := 5
  T1 := T135_83
  T2 := Q2.T135_83_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_135_83_1 : ColCert where
  rK := ⟨135, by decide⟩
  rH := ⟨83, by decide⟩
  m := 5
  T1 := T135_83
  T2 := Q2.T135_83_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_135_83_2 : ColCert where
  rK := ⟨135, by decide⟩
  rH := ⟨83, by decide⟩
  m := 5
  T1 := T135_83
  T2 := Q2.T135_83_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_135_83_3 : ColCert where
  rK := ⟨135, by decide⟩
  rH := ⟨83, by decide⟩
  m := 5
  T1 := T135_83
  T2 := Q2.T135_83_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_135_83_4 : ColCert where
  rK := ⟨135, by decide⟩
  rH := ⟨83, by decide⟩
  m := 5
  T1 := T135_83
  T2 := Q2.T135_83_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_135_91_0 : ColCert where
  rK := ⟨135, by decide⟩
  rH := ⟨91, by decide⟩
  m := 5
  T1 := T135_91
  T2 := Q2.T135_91_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_135_91_1 : ColCert where
  rK := ⟨135, by decide⟩
  rH := ⟨91, by decide⟩
  m := 5
  T1 := T135_91
  T2 := Q2.T135_91_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_135_91_2 : ColCert where
  rK := ⟨135, by decide⟩
  rH := ⟨91, by decide⟩
  m := 5
  T1 := T135_91
  T2 := Q2.T135_91_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_135_91_3 : ColCert where
  rK := ⟨135, by decide⟩
  rH := ⟨91, by decide⟩
  m := 5
  T1 := T135_91
  T2 := Q2.T135_91_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_135_91_4 : ColCert where
  rK := ⟨135, by decide⟩
  rH := ⟨91, by decide⟩
  m := 5
  T1 := T135_91
  T2 := Q2.T135_91_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_135_91_10 : ColCert where
  rK := ⟨135, by decide⟩
  rH := ⟨91, by decide⟩
  m := 5
  T1 := T135_91
  T2 := Q2.T135_91_2
  h1 := (2,3,2,2,2)
  h2 := (2,3,2,2,3)
  D := [[2, 3, 1, 3], [2, 3, 1, 0], [2, 3, 1, 2], [2, 3, 1, 4], [2, 3, 1, 1]]
  bind1 := by decide
  bind2 := by decide

end LeanDring.P5Presentation
