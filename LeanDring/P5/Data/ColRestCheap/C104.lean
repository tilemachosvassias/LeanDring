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
rest tier, chunk 103: 60 columns.
-/

-- machine-emitted data: silence style linters (generated long lines, file-level options)
set_option linter.style.longLine false

namespace LeanDring.P5Presentation

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

def colCert_144_144_23 : ColCert where
  rK := ⟨144, by decide⟩
  rH := ⟨144, by decide⟩
  m := 5
  T1 := T144_144
  T2 := Q2.T144_144_2
  h1 := (4,3,4,0,0)
  h2 := (4,3,4,0,3)
  D := [[4, 3, 3, 1], [4, 3, 3, 3], [4, 3, 3, 0], [4, 3, 3, 2], [4, 3, 3, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_144_144_24 : ColCert where
  rK := ⟨144, by decide⟩
  rH := ⟨144, by decide⟩
  m := 5
  T1 := T144_144
  T2 := Q2.T144_144_2
  h1 := (4,4,2,0,1)
  h2 := (4,4,2,0,0)
  D := [[4, 4, 4, 3], [4, 4, 4, 4], [4, 4, 4, 0], [4, 4, 4, 1], [4, 4, 4, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_145_0_0 : ColCert where
  rK := ⟨145, by decide⟩
  rH := ⟨0, by decide⟩
  m := 5
  T1 := T145_0
  T2 := Q2.T145_0_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_145_10_0 : ColCert where
  rK := ⟨145, by decide⟩
  rH := ⟨10, by decide⟩
  m := 5
  T1 := T145_10
  T2 := Q2.T145_10_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_145_10_1 : ColCert where
  rK := ⟨145, by decide⟩
  rH := ⟨10, by decide⟩
  m := 5
  T1 := T145_10
  T2 := Q2.T145_10_2
  h1 := (0,0,0,1,4)
  h2 := (0,0,0,1,4)
  D := [[0, 0, 1, 4], [0, 0, 1, 4], [0, 0, 1, 4], [0, 0, 1, 4], [0, 0, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_145_10_2 : ColCert where
  rK := ⟨145, by decide⟩
  rH := ⟨10, by decide⟩
  m := 5
  T1 := T145_10
  T2 := Q2.T145_10_2
  h1 := (0,0,0,2,3)
  h2 := (0,0,0,2,3)
  D := [[0, 0, 2, 3], [0, 0, 2, 3], [0, 0, 2, 3], [0, 0, 2, 3], [0, 0, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_145_10_3 : ColCert where
  rK := ⟨145, by decide⟩
  rH := ⟨10, by decide⟩
  m := 5
  T1 := T145_10
  T2 := Q2.T145_10_2
  h1 := (0,0,0,3,2)
  h2 := (0,0,0,3,2)
  D := [[0, 0, 3, 2], [0, 0, 3, 2], [0, 0, 3, 2], [0, 0, 3, 2], [0, 0, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_145_10_4 : ColCert where
  rK := ⟨145, by decide⟩
  rH := ⟨10, by decide⟩
  m := 5
  T1 := T145_10
  T2 := Q2.T145_10_2
  h1 := (0,0,0,4,1)
  h2 := (0,0,0,4,1)
  D := [[0, 0, 4, 1], [0, 0, 4, 1], [0, 0, 4, 1], [0, 0, 4, 1], [0, 0, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_145_11_0 : ColCert where
  rK := ⟨145, by decide⟩
  rH := ⟨11, by decide⟩
  m := 5
  T1 := T145_11
  T2 := Q2.T145_11_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_145_11_1 : ColCert where
  rK := ⟨145, by decide⟩
  rH := ⟨11, by decide⟩
  m := 5
  T1 := T145_11
  T2 := Q2.T145_11_2
  h1 := (1,0,0,4,3)
  h2 := (1,0,0,4,3)
  D := [[1, 0, 4, 4], [1, 0, 4, 4], [1, 0, 4, 4], [1, 0, 4, 4], [1, 0, 4, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_145_11_2 : ColCert where
  rK := ⟨145, by decide⟩
  rH := ⟨11, by decide⟩
  m := 5
  T1 := T145_11
  T2 := Q2.T145_11_2
  h1 := (2,0,0,3,0)
  h2 := (2,0,0,3,0)
  D := [[2, 0, 3, 4], [2, 0, 3, 4], [2, 0, 3, 4], [2, 0, 3, 4], [2, 0, 3, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_145_11_3 : ColCert where
  rK := ⟨145, by decide⟩
  rH := ⟨11, by decide⟩
  m := 5
  T1 := T145_11
  T2 := Q2.T145_11_2
  h1 := (3,0,0,2,1)
  h2 := (3,0,0,2,1)
  D := [[3, 0, 2, 0], [3, 0, 2, 0], [3, 0, 2, 0], [3, 0, 2, 0], [3, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_145_11_4 : ColCert where
  rK := ⟨145, by decide⟩
  rH := ⟨11, by decide⟩
  m := 5
  T1 := T145_11
  T2 := Q2.T145_11_2
  h1 := (4,0,0,1,1)
  h2 := (4,0,0,1,1)
  D := [[4, 0, 1, 2], [4, 0, 1, 2], [4, 0, 1, 2], [4, 0, 1, 2], [4, 0, 1, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_145_12_0 : ColCert where
  rK := ⟨145, by decide⟩
  rH := ⟨12, by decide⟩
  m := 5
  T1 := T145_12
  T2 := Q2.T145_12_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_145_12_1 : ColCert where
  rK := ⟨145, by decide⟩
  rH := ⟨12, by decide⟩
  m := 5
  T1 := T145_12
  T2 := Q2.T145_12_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_145_12_2 : ColCert where
  rK := ⟨145, by decide⟩
  rH := ⟨12, by decide⟩
  m := 5
  T1 := T145_12
  T2 := Q2.T145_12_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_145_12_3 : ColCert where
  rK := ⟨145, by decide⟩
  rH := ⟨12, by decide⟩
  m := 5
  T1 := T145_12
  T2 := Q2.T145_12_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_145_12_4 : ColCert where
  rK := ⟨145, by decide⟩
  rH := ⟨12, by decide⟩
  m := 5
  T1 := T145_12
  T2 := Q2.T145_12_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_145_43_0 : ColCert where
  rK := ⟨145, by decide⟩
  rH := ⟨43, by decide⟩
  m := 5
  T1 := T145_43
  T2 := Q2.T145_43_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_145_43_1 : ColCert where
  rK := ⟨145, by decide⟩
  rH := ⟨43, by decide⟩
  m := 5
  T1 := T145_43
  T2 := Q2.T145_43_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_145_43_2 : ColCert where
  rK := ⟨145, by decide⟩
  rH := ⟨43, by decide⟩
  m := 5
  T1 := T145_43
  T2 := Q2.T145_43_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_145_43_3 : ColCert where
  rK := ⟨145, by decide⟩
  rH := ⟨43, by decide⟩
  m := 5
  T1 := T145_43
  T2 := Q2.T145_43_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_145_43_4 : ColCert where
  rK := ⟨145, by decide⟩
  rH := ⟨43, by decide⟩
  m := 5
  T1 := T145_43
  T2 := Q2.T145_43_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_145_44_0 : ColCert where
  rK := ⟨145, by decide⟩
  rH := ⟨44, by decide⟩
  m := 5
  T1 := T145_44
  T2 := Q2.T145_44_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_145_44_1 : ColCert where
  rK := ⟨145, by decide⟩
  rH := ⟨44, by decide⟩
  m := 5
  T1 := T145_44
  T2 := Q2.T145_44_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_145_44_2 : ColCert where
  rK := ⟨145, by decide⟩
  rH := ⟨44, by decide⟩
  m := 5
  T1 := T145_44
  T2 := Q2.T145_44_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_145_44_3 : ColCert where
  rK := ⟨145, by decide⟩
  rH := ⟨44, by decide⟩
  m := 5
  T1 := T145_44
  T2 := Q2.T145_44_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_145_44_4 : ColCert where
  rK := ⟨145, by decide⟩
  rH := ⟨44, by decide⟩
  m := 5
  T1 := T145_44
  T2 := Q2.T145_44_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_145_44_5 : ColCert where
  rK := ⟨145, by decide⟩
  rH := ⟨44, by decide⟩
  m := 5
  T1 := T145_44
  T2 := Q2.T145_44_2
  h1 := (1,4,4,3,0)
  h2 := (1,4,4,3,0)
  D := [[1, 4, 4, 1], [1, 4, 4, 2], [1, 4, 4, 3], [1, 4, 4, 4], [1, 4, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_145_45_0 : ColCert where
  rK := ⟨145, by decide⟩
  rH := ⟨45, by decide⟩
  m := 5
  T1 := T145_45
  T2 := Q2.T145_45_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_145_45_1 : ColCert where
  rK := ⟨145, by decide⟩
  rH := ⟨45, by decide⟩
  m := 5
  T1 := T145_45
  T2 := Q2.T145_45_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_145_45_2 : ColCert where
  rK := ⟨145, by decide⟩
  rH := ⟨45, by decide⟩
  m := 5
  T1 := T145_45
  T2 := Q2.T145_45_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_145_45_3 : ColCert where
  rK := ⟨145, by decide⟩
  rH := ⟨45, by decide⟩
  m := 5
  T1 := T145_45
  T2 := Q2.T145_45_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_145_45_4 : ColCert where
  rK := ⟨145, by decide⟩
  rH := ⟨45, by decide⟩
  m := 5
  T1 := T145_45
  T2 := Q2.T145_45_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_145_46_0 : ColCert where
  rK := ⟨145, by decide⟩
  rH := ⟨46, by decide⟩
  m := 5
  T1 := T145_46
  T2 := Q2.T145_46_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_145_46_1 : ColCert where
  rK := ⟨145, by decide⟩
  rH := ⟨46, by decide⟩
  m := 5
  T1 := T145_46
  T2 := Q2.T145_46_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_145_46_2 : ColCert where
  rK := ⟨145, by decide⟩
  rH := ⟨46, by decide⟩
  m := 5
  T1 := T145_46
  T2 := Q2.T145_46_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_145_46_3 : ColCert where
  rK := ⟨145, by decide⟩
  rH := ⟨46, by decide⟩
  m := 5
  T1 := T145_46
  T2 := Q2.T145_46_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_145_46_4 : ColCert where
  rK := ⟨145, by decide⟩
  rH := ⟨46, by decide⟩
  m := 5
  T1 := T145_46
  T2 := Q2.T145_46_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_145_47_0 : ColCert where
  rK := ⟨145, by decide⟩
  rH := ⟨47, by decide⟩
  m := 5
  T1 := T145_47
  T2 := Q2.T145_47_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_145_47_1 : ColCert where
  rK := ⟨145, by decide⟩
  rH := ⟨47, by decide⟩
  m := 5
  T1 := T145_47
  T2 := Q2.T145_47_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_145_47_2 : ColCert where
  rK := ⟨145, by decide⟩
  rH := ⟨47, by decide⟩
  m := 5
  T1 := T145_47
  T2 := Q2.T145_47_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_145_47_3 : ColCert where
  rK := ⟨145, by decide⟩
  rH := ⟨47, by decide⟩
  m := 5
  T1 := T145_47
  T2 := Q2.T145_47_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_145_47_4 : ColCert where
  rK := ⟨145, by decide⟩
  rH := ⟨47, by decide⟩
  m := 5
  T1 := T145_47
  T2 := Q2.T145_47_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_145_53_0 : ColCert where
  rK := ⟨145, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T145_53
  T2 := Q2.T145_53_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_145_53_1 : ColCert where
  rK := ⟨145, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T145_53
  T2 := Q2.T145_53_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_145_53_2 : ColCert where
  rK := ⟨145, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T145_53
  T2 := Q2.T145_53_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_145_53_3 : ColCert where
  rK := ⟨145, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T145_53
  T2 := Q2.T145_53_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_145_53_4 : ColCert where
  rK := ⟨145, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T145_53
  T2 := Q2.T145_53_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_145_53_5 : ColCert where
  rK := ⟨145, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T145_53
  T2 := Q2.T145_53_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_145_53_10 : ColCert where
  rK := ⟨145, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T145_53
  T2 := Q2.T145_53_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0], [0, 0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_145_53_15 : ColCert where
  rK := ⟨145, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T145_53
  T2 := Q2.T145_53_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0], [0, 0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_145_53_20 : ColCert where
  rK := ⟨145, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T145_53
  T2 := Q2.T145_53_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0], [0, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_145_54_0 : ColCert where
  rK := ⟨145, by decide⟩
  rH := ⟨54, by decide⟩
  m := 5
  T1 := T145_54
  T2 := Q2.T145_54_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_145_54_1 : ColCert where
  rK := ⟨145, by decide⟩
  rH := ⟨54, by decide⟩
  m := 5
  T1 := T145_54
  T2 := Q2.T145_54_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_145_54_2 : ColCert where
  rK := ⟨145, by decide⟩
  rH := ⟨54, by decide⟩
  m := 5
  T1 := T145_54
  T2 := Q2.T145_54_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_145_54_3 : ColCert where
  rK := ⟨145, by decide⟩
  rH := ⟨54, by decide⟩
  m := 5
  T1 := T145_54
  T2 := Q2.T145_54_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_145_54_4 : ColCert where
  rK := ⟨145, by decide⟩
  rH := ⟨54, by decide⟩
  m := 5
  T1 := T145_54
  T2 := Q2.T145_54_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_145_54_5 : ColCert where
  rK := ⟨145, by decide⟩
  rH := ⟨54, by decide⟩
  m := 5
  T1 := T145_54
  T2 := Q2.T145_54_2
  h1 := (1,0,0,4,4)
  h2 := (1,0,0,4,4)
  D := [[1, 0, 4, 0], [1, 0, 4, 0], [1, 0, 4, 0], [1, 0, 4, 0], [1, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_145_54_10 : ColCert where
  rK := ⟨145, by decide⟩
  rH := ⟨54, by decide⟩
  m := 5
  T1 := T145_54
  T2 := Q2.T145_54_2
  h1 := (2,0,0,3,2)
  h2 := (2,0,0,3,2)
  D := [[2, 0, 3, 1], [2, 0, 3, 1], [2, 0, 3, 1], [2, 0, 3, 1], [2, 0, 3, 1]]
  bind1 := by decide
  bind2 := by decide

end LeanDring.P5Presentation
