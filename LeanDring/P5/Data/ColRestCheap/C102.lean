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
rest tier, chunk 101: 60 columns.
-/

-- machine-emitted data: silence style linters (generated long lines, file-level options)
set_option linter.style.longLine false

namespace LeanDring.P5Presentation

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

def colCert_144_11_2 : ColCert where
  rK := ⟨144, by decide⟩
  rH := ⟨11, by decide⟩
  m := 5
  T1 := T144_11
  T2 := Q2.T144_11_2
  h1 := (2,0,0,3,0)
  h2 := (2,0,0,3,0)
  D := [[2, 0, 3, 4], [2, 0, 3, 4], [2, 0, 3, 4], [2, 0, 3, 4], [2, 0, 3, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_144_11_3 : ColCert where
  rK := ⟨144, by decide⟩
  rH := ⟨11, by decide⟩
  m := 5
  T1 := T144_11
  T2 := Q2.T144_11_2
  h1 := (3,0,0,2,1)
  h2 := (3,0,0,2,1)
  D := [[3, 0, 2, 0], [3, 0, 2, 0], [3, 0, 2, 0], [3, 0, 2, 0], [3, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_144_11_4 : ColCert where
  rK := ⟨144, by decide⟩
  rH := ⟨11, by decide⟩
  m := 5
  T1 := T144_11
  T2 := Q2.T144_11_2
  h1 := (4,0,0,1,1)
  h2 := (4,0,0,1,1)
  D := [[4, 0, 1, 2], [4, 0, 1, 2], [4, 0, 1, 2], [4, 0, 1, 2], [4, 0, 1, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_144_12_0 : ColCert where
  rK := ⟨144, by decide⟩
  rH := ⟨12, by decide⟩
  m := 5
  T1 := T144_12
  T2 := Q2.T144_12_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_144_12_1 : ColCert where
  rK := ⟨144, by decide⟩
  rH := ⟨12, by decide⟩
  m := 5
  T1 := T144_12
  T2 := Q2.T144_12_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_144_12_2 : ColCert where
  rK := ⟨144, by decide⟩
  rH := ⟨12, by decide⟩
  m := 5
  T1 := T144_12
  T2 := Q2.T144_12_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_144_12_3 : ColCert where
  rK := ⟨144, by decide⟩
  rH := ⟨12, by decide⟩
  m := 5
  T1 := T144_12
  T2 := Q2.T144_12_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_144_12_4 : ColCert where
  rK := ⟨144, by decide⟩
  rH := ⟨12, by decide⟩
  m := 5
  T1 := T144_12
  T2 := Q2.T144_12_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_144_38_0 : ColCert where
  rK := ⟨144, by decide⟩
  rH := ⟨38, by decide⟩
  m := 5
  T1 := T144_38
  T2 := Q2.T144_38_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_144_38_1 : ColCert where
  rK := ⟨144, by decide⟩
  rH := ⟨38, by decide⟩
  m := 5
  T1 := T144_38
  T2 := Q2.T144_38_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_144_38_2 : ColCert where
  rK := ⟨144, by decide⟩
  rH := ⟨38, by decide⟩
  m := 5
  T1 := T144_38
  T2 := Q2.T144_38_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_144_38_3 : ColCert where
  rK := ⟨144, by decide⟩
  rH := ⟨38, by decide⟩
  m := 5
  T1 := T144_38
  T2 := Q2.T144_38_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_144_38_4 : ColCert where
  rK := ⟨144, by decide⟩
  rH := ⟨38, by decide⟩
  m := 5
  T1 := T144_38
  T2 := Q2.T144_38_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_144_39_0 : ColCert where
  rK := ⟨144, by decide⟩
  rH := ⟨39, by decide⟩
  m := 5
  T1 := T144_39
  T2 := Q2.T144_39_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_144_39_1 : ColCert where
  rK := ⟨144, by decide⟩
  rH := ⟨39, by decide⟩
  m := 5
  T1 := T144_39
  T2 := Q2.T144_39_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_144_39_2 : ColCert where
  rK := ⟨144, by decide⟩
  rH := ⟨39, by decide⟩
  m := 5
  T1 := T144_39
  T2 := Q2.T144_39_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_144_39_3 : ColCert where
  rK := ⟨144, by decide⟩
  rH := ⟨39, by decide⟩
  m := 5
  T1 := T144_39
  T2 := Q2.T144_39_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_144_39_4 : ColCert where
  rK := ⟨144, by decide⟩
  rH := ⟨39, by decide⟩
  m := 5
  T1 := T144_39
  T2 := Q2.T144_39_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_144_39_15 : ColCert where
  rK := ⟨144, by decide⟩
  rH := ⟨39, by decide⟩
  m := 5
  T1 := T144_39
  T2 := Q2.T144_39_2
  h1 := (3,2,1,1,0)
  h2 := (3,2,1,1,2)
  D := [[3, 2, 0, 1], [3, 2, 0, 4], [3, 2, 0, 2], [3, 2, 0, 0], [3, 2, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_144_40_0 : ColCert where
  rK := ⟨144, by decide⟩
  rH := ⟨40, by decide⟩
  m := 5
  T1 := T144_40
  T2 := Q2.T144_40_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_144_40_1 : ColCert where
  rK := ⟨144, by decide⟩
  rH := ⟨40, by decide⟩
  m := 5
  T1 := T144_40
  T2 := Q2.T144_40_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_144_40_2 : ColCert where
  rK := ⟨144, by decide⟩
  rH := ⟨40, by decide⟩
  m := 5
  T1 := T144_40
  T2 := Q2.T144_40_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_144_40_3 : ColCert where
  rK := ⟨144, by decide⟩
  rH := ⟨40, by decide⟩
  m := 5
  T1 := T144_40
  T2 := Q2.T144_40_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_144_40_4 : ColCert where
  rK := ⟨144, by decide⟩
  rH := ⟨40, by decide⟩
  m := 5
  T1 := T144_40
  T2 := Q2.T144_40_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_144_40_5 : ColCert where
  rK := ⟨144, by decide⟩
  rH := ⟨40, by decide⟩
  m := 5
  T1 := T144_40
  T2 := Q2.T144_40_2
  h1 := (1,2,1,2,4)
  h2 := (1,2,1,2,1)
  D := [[1, 2, 0, 1], [1, 2, 0, 4], [1, 2, 0, 2], [1, 2, 0, 0], [1, 2, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_144_40_10 : ColCert where
  rK := ⟨144, by decide⟩
  rH := ⟨40, by decide⟩
  m := 5
  T1 := T144_40
  T2 := Q2.T144_40_2
  h1 := (2,4,2,1,2)
  h2 := (2,4,2,1,1)
  D := [[2, 4, 3, 4], [2, 4, 3, 0], [2, 4, 3, 1], [2, 4, 3, 2], [2, 4, 3, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_144_41_0 : ColCert where
  rK := ⟨144, by decide⟩
  rH := ⟨41, by decide⟩
  m := 5
  T1 := T144_41
  T2 := Q2.T144_41_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_144_41_1 : ColCert where
  rK := ⟨144, by decide⟩
  rH := ⟨41, by decide⟩
  m := 5
  T1 := T144_41
  T2 := Q2.T144_41_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_144_41_2 : ColCert where
  rK := ⟨144, by decide⟩
  rH := ⟨41, by decide⟩
  m := 5
  T1 := T144_41
  T2 := Q2.T144_41_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_144_41_3 : ColCert where
  rK := ⟨144, by decide⟩
  rH := ⟨41, by decide⟩
  m := 5
  T1 := T144_41
  T2 := Q2.T144_41_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_144_41_4 : ColCert where
  rK := ⟨144, by decide⟩
  rH := ⟨41, by decide⟩
  m := 5
  T1 := T144_41
  T2 := Q2.T144_41_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_144_41_15 : ColCert where
  rK := ⟨144, by decide⟩
  rH := ⟨41, by decide⟩
  m := 5
  T1 := T144_41
  T2 := Q2.T144_41_2
  h1 := (3,4,2,4,0)
  h2 := (3,4,2,4,4)
  D := [[3, 4, 2, 4], [3, 4, 2, 0], [3, 4, 2, 1], [3, 4, 2, 2], [3, 4, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_144_42_0 : ColCert where
  rK := ⟨144, by decide⟩
  rH := ⟨42, by decide⟩
  m := 5
  T1 := T144_42
  T2 := Q2.T144_42_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_144_42_1 : ColCert where
  rK := ⟨144, by decide⟩
  rH := ⟨42, by decide⟩
  m := 5
  T1 := T144_42
  T2 := Q2.T144_42_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_144_42_2 : ColCert where
  rK := ⟨144, by decide⟩
  rH := ⟨42, by decide⟩
  m := 5
  T1 := T144_42
  T2 := Q2.T144_42_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_144_42_3 : ColCert where
  rK := ⟨144, by decide⟩
  rH := ⟨42, by decide⟩
  m := 5
  T1 := T144_42
  T2 := Q2.T144_42_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_144_42_4 : ColCert where
  rK := ⟨144, by decide⟩
  rH := ⟨42, by decide⟩
  m := 5
  T1 := T144_42
  T2 := Q2.T144_42_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_144_53_0 : ColCert where
  rK := ⟨144, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T144_53
  T2 := Q2.T144_53_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_144_53_1 : ColCert where
  rK := ⟨144, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T144_53
  T2 := Q2.T144_53_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_144_53_2 : ColCert where
  rK := ⟨144, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T144_53
  T2 := Q2.T144_53_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_144_53_3 : ColCert where
  rK := ⟨144, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T144_53
  T2 := Q2.T144_53_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_144_53_4 : ColCert where
  rK := ⟨144, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T144_53
  T2 := Q2.T144_53_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_144_53_5 : ColCert where
  rK := ⟨144, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T144_53
  T2 := Q2.T144_53_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_144_53_10 : ColCert where
  rK := ⟨144, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T144_53
  T2 := Q2.T144_53_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_144_53_15 : ColCert where
  rK := ⟨144, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T144_53
  T2 := Q2.T144_53_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_144_53_20 : ColCert where
  rK := ⟨144, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T144_53
  T2 := Q2.T144_53_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_144_54_0 : ColCert where
  rK := ⟨144, by decide⟩
  rH := ⟨54, by decide⟩
  m := 5
  T1 := T144_54
  T2 := Q2.T144_54_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_144_54_1 : ColCert where
  rK := ⟨144, by decide⟩
  rH := ⟨54, by decide⟩
  m := 5
  T1 := T144_54
  T2 := Q2.T144_54_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_144_54_2 : ColCert where
  rK := ⟨144, by decide⟩
  rH := ⟨54, by decide⟩
  m := 5
  T1 := T144_54
  T2 := Q2.T144_54_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_144_54_3 : ColCert where
  rK := ⟨144, by decide⟩
  rH := ⟨54, by decide⟩
  m := 5
  T1 := T144_54
  T2 := Q2.T144_54_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_144_54_4 : ColCert where
  rK := ⟨144, by decide⟩
  rH := ⟨54, by decide⟩
  m := 5
  T1 := T144_54
  T2 := Q2.T144_54_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_144_54_5 : ColCert where
  rK := ⟨144, by decide⟩
  rH := ⟨54, by decide⟩
  m := 5
  T1 := T144_54
  T2 := Q2.T144_54_2
  h1 := (1,0,0,4,4)
  h2 := (1,0,0,4,4)
  D := [[1, 0, 4, 0], [1, 0, 4, 0], [1, 0, 4, 0], [1, 0, 4, 0], [1, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_144_54_10 : ColCert where
  rK := ⟨144, by decide⟩
  rH := ⟨54, by decide⟩
  m := 5
  T1 := T144_54
  T2 := Q2.T144_54_2
  h1 := (2,0,0,3,2)
  h2 := (2,0,0,3,2)
  D := [[2, 0, 3, 1], [2, 0, 3, 1], [2, 0, 3, 1], [2, 0, 3, 1], [2, 0, 3, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_144_54_15 : ColCert where
  rK := ⟨144, by decide⟩
  rH := ⟨54, by decide⟩
  m := 5
  T1 := T144_54
  T2 := Q2.T144_54_2
  h1 := (3,0,0,2,4)
  h2 := (3,0,0,2,4)
  D := [[3, 0, 2, 3], [3, 0, 2, 3], [3, 0, 2, 3], [3, 0, 2, 3], [3, 0, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_144_54_20 : ColCert where
  rK := ⟨144, by decide⟩
  rH := ⟨54, by decide⟩
  m := 5
  T1 := T144_54
  T2 := Q2.T144_54_2
  h1 := (4,0,0,1,0)
  h2 := (4,0,0,1,0)
  D := [[4, 0, 1, 1], [4, 0, 1, 1], [4, 0, 1, 1], [4, 0, 1, 1], [4, 0, 1, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_144_100_0 : ColCert where
  rK := ⟨144, by decide⟩
  rH := ⟨100, by decide⟩
  m := 5
  T1 := T144_100
  T2 := Q2.T144_100_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_144_100_1 : ColCert where
  rK := ⟨144, by decide⟩
  rH := ⟨100, by decide⟩
  m := 5
  T1 := T144_100
  T2 := Q2.T144_100_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_144_100_2 : ColCert where
  rK := ⟨144, by decide⟩
  rH := ⟨100, by decide⟩
  m := 5
  T1 := T144_100
  T2 := Q2.T144_100_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_144_100_3 : ColCert where
  rK := ⟨144, by decide⟩
  rH := ⟨100, by decide⟩
  m := 5
  T1 := T144_100
  T2 := Q2.T144_100_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_144_100_4 : ColCert where
  rK := ⟨144, by decide⟩
  rH := ⟨100, by decide⟩
  m := 5
  T1 := T144_100
  T2 := Q2.T144_100_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

end LeanDring.P5Presentation
