/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.Twin1.ColCert
import LeanDring.P5.Data.EntryK.C017

/-!
# Species-table cell data, stage 2 — twin-coincident columns (cheap tier)

Per-column certified exponent-vector data (`ColCert`/`ColCertDiv`) with kernel
`decide` bindings. Emitted; the embedded lists are what the kernel certifies.
rest tier, chunk 164: 60 columns.
-/

-- machine-emitted data: silence style linters (generated long lines, file-level options)
set_option linter.style.longLine false

namespace LeanDring.P5Presentation

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

def colCert_73_24_1 : ColCert where
  rK := ⟨73, by decide⟩
  rH := ⟨24, by decide⟩
  m := 25
  T1 := T73_24
  T2 := Q2.T73_24_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_73_24_2 : ColCert where
  rK := ⟨73, by decide⟩
  rH := ⟨24, by decide⟩
  m := 25
  T1 := T73_24
  T2 := Q2.T73_24_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_73_24_3 : ColCert where
  rK := ⟨73, by decide⟩
  rH := ⟨24, by decide⟩
  m := 25
  T1 := T73_24
  T2 := Q2.T73_24_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_73_24_4 : ColCert where
  rK := ⟨73, by decide⟩
  rH := ⟨24, by decide⟩
  m := 25
  T1 := T73_24
  T2 := Q2.T73_24_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_73_24_5 : ColCert where
  rK := ⟨73, by decide⟩
  rH := ⟨24, by decide⟩
  m := 25
  T1 := T73_24
  T2 := Q2.T73_24_2
  h1 := (0,0,1,2,0)
  h2 := (0,0,1,2,0)
  D := [[0, 1, 3], [0, 1, 3], [0, 1, 3], [0, 1, 3], [0, 1, 3], [0, 1, 4], [0, 1, 4], [0, 1, 4], [0, 1, 4], [0, 1, 4], [0, 1, 0], [0, 1, 0], [0, 1, 0], [0, 1, 0], [0, 1, 0], [0, 1, 1], [0, 1, 1], [0, 1, 1], [0, 1, 1], [0, 1, 1], [0, 1, 2], [0, 1, 2], [0, 1, 2], [0, 1, 2], [0, 1, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_73_24_10 : ColCert where
  rK := ⟨73, by decide⟩
  rH := ⟨24, by decide⟩
  m := 25
  T1 := T73_24
  T2 := Q2.T73_24_2
  h1 := (0,0,2,4,0)
  h2 := (0,0,2,4,0)
  D := [[0, 2, 1], [0, 2, 1], [0, 2, 1], [0, 2, 1], [0, 2, 1], [0, 2, 3], [0, 2, 3], [0, 2, 3], [0, 2, 3], [0, 2, 3], [0, 2, 0], [0, 2, 0], [0, 2, 0], [0, 2, 0], [0, 2, 0], [0, 2, 2], [0, 2, 2], [0, 2, 2], [0, 2, 2], [0, 2, 2], [0, 2, 4], [0, 2, 4], [0, 2, 4], [0, 2, 4], [0, 2, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_73_24_15 : ColCert where
  rK := ⟨73, by decide⟩
  rH := ⟨24, by decide⟩
  m := 25
  T1 := T73_24
  T2 := Q2.T73_24_2
  h1 := (0,0,3,1,0)
  h2 := (0,0,3,1,0)
  D := [[0, 3, 4], [0, 3, 4], [0, 3, 4], [0, 3, 4], [0, 3, 4], [0, 3, 2], [0, 3, 2], [0, 3, 2], [0, 3, 2], [0, 3, 2], [0, 3, 0], [0, 3, 0], [0, 3, 0], [0, 3, 0], [0, 3, 0], [0, 3, 3], [0, 3, 3], [0, 3, 3], [0, 3, 3], [0, 3, 3], [0, 3, 1], [0, 3, 1], [0, 3, 1], [0, 3, 1], [0, 3, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_73_24_20 : ColCert where
  rK := ⟨73, by decide⟩
  rH := ⟨24, by decide⟩
  m := 25
  T1 := T73_24
  T2 := Q2.T73_24_2
  h1 := (0,0,4,3,0)
  h2 := (0,0,4,3,0)
  D := [[0, 4, 2], [0, 4, 2], [0, 4, 2], [0, 4, 2], [0, 4, 2], [0, 4, 1], [0, 4, 1], [0, 4, 1], [0, 4, 1], [0, 4, 1], [0, 4, 0], [0, 4, 0], [0, 4, 0], [0, 4, 0], [0, 4, 0], [0, 4, 4], [0, 4, 4], [0, 4, 4], [0, 4, 4], [0, 4, 4], [0, 4, 3], [0, 4, 3], [0, 4, 3], [0, 4, 3], [0, 4, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_73_31_0 : ColCert where
  rK := ⟨73, by decide⟩
  rH := ⟨31, by decide⟩
  m := 5
  T1 := T73_31
  T2 := Q2.T73_31_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_73_31_1 : ColCert where
  rK := ⟨73, by decide⟩
  rH := ⟨31, by decide⟩
  m := 5
  T1 := T73_31
  T2 := Q2.T73_31_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_73_31_2 : ColCert where
  rK := ⟨73, by decide⟩
  rH := ⟨31, by decide⟩
  m := 5
  T1 := T73_31
  T2 := Q2.T73_31_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_73_31_3 : ColCert where
  rK := ⟨73, by decide⟩
  rH := ⟨31, by decide⟩
  m := 5
  T1 := T73_31
  T2 := Q2.T73_31_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_73_31_4 : ColCert where
  rK := ⟨73, by decide⟩
  rH := ⟨31, by decide⟩
  m := 5
  T1 := T73_31
  T2 := Q2.T73_31_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_73_36_0 : ColCert where
  rK := ⟨73, by decide⟩
  rH := ⟨36, by decide⟩
  m := 5
  T1 := T73_36
  T2 := Q2.T73_36_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_73_36_1 : ColCert where
  rK := ⟨73, by decide⟩
  rH := ⟨36, by decide⟩
  m := 5
  T1 := T73_36
  T2 := Q2.T73_36_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_73_36_2 : ColCert where
  rK := ⟨73, by decide⟩
  rH := ⟨36, by decide⟩
  m := 5
  T1 := T73_36
  T2 := Q2.T73_36_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_73_36_3 : ColCert where
  rK := ⟨73, by decide⟩
  rH := ⟨36, by decide⟩
  m := 5
  T1 := T73_36
  T2 := Q2.T73_36_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_73_36_4 : ColCert where
  rK := ⟨73, by decide⟩
  rH := ⟨36, by decide⟩
  m := 5
  T1 := T73_36
  T2 := Q2.T73_36_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_73_41_0 : ColCert where
  rK := ⟨73, by decide⟩
  rH := ⟨41, by decide⟩
  m := 5
  T1 := T73_41
  T2 := Q2.T73_41_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_73_41_1 : ColCert where
  rK := ⟨73, by decide⟩
  rH := ⟨41, by decide⟩
  m := 5
  T1 := T73_41
  T2 := Q2.T73_41_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_73_41_2 : ColCert where
  rK := ⟨73, by decide⟩
  rH := ⟨41, by decide⟩
  m := 5
  T1 := T73_41
  T2 := Q2.T73_41_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_73_41_3 : ColCert where
  rK := ⟨73, by decide⟩
  rH := ⟨41, by decide⟩
  m := 5
  T1 := T73_41
  T2 := Q2.T73_41_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_73_41_4 : ColCert where
  rK := ⟨73, by decide⟩
  rH := ⟨41, by decide⟩
  m := 5
  T1 := T73_41
  T2 := Q2.T73_41_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_73_46_0 : ColCert where
  rK := ⟨73, by decide⟩
  rH := ⟨46, by decide⟩
  m := 5
  T1 := T73_46
  T2 := Q2.T73_46_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_73_46_1 : ColCert where
  rK := ⟨73, by decide⟩
  rH := ⟨46, by decide⟩
  m := 5
  T1 := T73_46
  T2 := Q2.T73_46_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_73_46_2 : ColCert where
  rK := ⟨73, by decide⟩
  rH := ⟨46, by decide⟩
  m := 5
  T1 := T73_46
  T2 := Q2.T73_46_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_73_46_3 : ColCert where
  rK := ⟨73, by decide⟩
  rH := ⟨46, by decide⟩
  m := 5
  T1 := T73_46
  T2 := Q2.T73_46_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_73_46_4 : ColCert where
  rK := ⟨73, by decide⟩
  rH := ⟨46, by decide⟩
  m := 5
  T1 := T73_46
  T2 := Q2.T73_46_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_73_51_0 : ColCert where
  rK := ⟨73, by decide⟩
  rH := ⟨51, by decide⟩
  m := 5
  T1 := T73_51
  T2 := Q2.T73_51_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_73_51_1 : ColCert where
  rK := ⟨73, by decide⟩
  rH := ⟨51, by decide⟩
  m := 5
  T1 := T73_51
  T2 := Q2.T73_51_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_73_51_2 : ColCert where
  rK := ⟨73, by decide⟩
  rH := ⟨51, by decide⟩
  m := 5
  T1 := T73_51
  T2 := Q2.T73_51_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_73_51_3 : ColCert where
  rK := ⟨73, by decide⟩
  rH := ⟨51, by decide⟩
  m := 5
  T1 := T73_51
  T2 := Q2.T73_51_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_73_51_4 : ColCert where
  rK := ⟨73, by decide⟩
  rH := ⟨51, by decide⟩
  m := 5
  T1 := T73_51
  T2 := Q2.T73_51_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_73_73_0 : ColCert where
  rK := ⟨73, by decide⟩
  rH := ⟨73, by decide⟩
  m := 5
  T1 := T73_73
  T2 := Q2.T73_73_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_73_73_1 : ColCert where
  rK := ⟨73, by decide⟩
  rH := ⟨73, by decide⟩
  m := 5
  T1 := T73_73
  T2 := Q2.T73_73_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_73_73_2 : ColCert where
  rK := ⟨73, by decide⟩
  rH := ⟨73, by decide⟩
  m := 5
  T1 := T73_73
  T2 := Q2.T73_73_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2], [0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_73_73_3 : ColCert where
  rK := ⟨73, by decide⟩
  rH := ⟨73, by decide⟩
  m := 5
  T1 := T73_73
  T2 := Q2.T73_73_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3], [0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_73_73_4 : ColCert where
  rK := ⟨73, by decide⟩
  rH := ⟨73, by decide⟩
  m := 5
  T1 := T73_73
  T2 := Q2.T73_73_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4], [0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_73_73_5 : ColCert where
  rK := ⟨73, by decide⟩
  rH := ⟨73, by decide⟩
  m := 5
  T1 := T73_73
  T2 := Q2.T73_73_2
  h1 := (0,0,1,2,0)
  h2 := (0,0,1,2,0)
  D := [[0, 1, 0], [0, 1, 0], [0, 1, 0], [0, 1, 0], [0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_73_73_6 : ColCert where
  rK := ⟨73, by decide⟩
  rH := ⟨73, by decide⟩
  m := 5
  T1 := T73_73
  T2 := Q2.T73_73_2
  h1 := (0,0,1,2,1)
  h2 := (0,0,1,2,1)
  D := [[0, 1, 1], [0, 1, 1], [0, 1, 1], [0, 1, 1], [0, 1, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_73_73_7 : ColCert where
  rK := ⟨73, by decide⟩
  rH := ⟨73, by decide⟩
  m := 5
  T1 := T73_73
  T2 := Q2.T73_73_2
  h1 := (0,0,1,2,2)
  h2 := (0,0,1,2,2)
  D := [[0, 1, 2], [0, 1, 2], [0, 1, 2], [0, 1, 2], [0, 1, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_73_73_8 : ColCert where
  rK := ⟨73, by decide⟩
  rH := ⟨73, by decide⟩
  m := 5
  T1 := T73_73
  T2 := Q2.T73_73_2
  h1 := (0,0,1,2,3)
  h2 := (0,0,1,2,3)
  D := [[0, 1, 3], [0, 1, 3], [0, 1, 3], [0, 1, 3], [0, 1, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_73_73_9 : ColCert where
  rK := ⟨73, by decide⟩
  rH := ⟨73, by decide⟩
  m := 5
  T1 := T73_73
  T2 := Q2.T73_73_2
  h1 := (0,0,1,2,4)
  h2 := (0,0,1,2,4)
  D := [[0, 1, 4], [0, 1, 4], [0, 1, 4], [0, 1, 4], [0, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_73_73_10 : ColCert where
  rK := ⟨73, by decide⟩
  rH := ⟨73, by decide⟩
  m := 5
  T1 := T73_73
  T2 := Q2.T73_73_2
  h1 := (0,0,2,4,0)
  h2 := (0,0,2,4,0)
  D := [[0, 2, 0], [0, 2, 0], [0, 2, 0], [0, 2, 0], [0, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_73_73_11 : ColCert where
  rK := ⟨73, by decide⟩
  rH := ⟨73, by decide⟩
  m := 5
  T1 := T73_73
  T2 := Q2.T73_73_2
  h1 := (0,0,2,4,1)
  h2 := (0,0,2,4,1)
  D := [[0, 2, 1], [0, 2, 1], [0, 2, 1], [0, 2, 1], [0, 2, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_73_73_12 : ColCert where
  rK := ⟨73, by decide⟩
  rH := ⟨73, by decide⟩
  m := 5
  T1 := T73_73
  T2 := Q2.T73_73_2
  h1 := (0,0,2,4,2)
  h2 := (0,0,2,4,2)
  D := [[0, 2, 2], [0, 2, 2], [0, 2, 2], [0, 2, 2], [0, 2, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_73_73_13 : ColCert where
  rK := ⟨73, by decide⟩
  rH := ⟨73, by decide⟩
  m := 5
  T1 := T73_73
  T2 := Q2.T73_73_2
  h1 := (0,0,2,4,3)
  h2 := (0,0,2,4,3)
  D := [[0, 2, 3], [0, 2, 3], [0, 2, 3], [0, 2, 3], [0, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_73_73_14 : ColCert where
  rK := ⟨73, by decide⟩
  rH := ⟨73, by decide⟩
  m := 5
  T1 := T73_73
  T2 := Q2.T73_73_2
  h1 := (0,0,2,4,4)
  h2 := (0,0,2,4,4)
  D := [[0, 2, 4], [0, 2, 4], [0, 2, 4], [0, 2, 4], [0, 2, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_73_73_15 : ColCert where
  rK := ⟨73, by decide⟩
  rH := ⟨73, by decide⟩
  m := 5
  T1 := T73_73
  T2 := Q2.T73_73_2
  h1 := (0,0,3,1,0)
  h2 := (0,0,3,1,0)
  D := [[0, 3, 0], [0, 3, 0], [0, 3, 0], [0, 3, 0], [0, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_73_73_16 : ColCert where
  rK := ⟨73, by decide⟩
  rH := ⟨73, by decide⟩
  m := 5
  T1 := T73_73
  T2 := Q2.T73_73_2
  h1 := (0,0,3,1,1)
  h2 := (0,0,3,1,1)
  D := [[0, 3, 1], [0, 3, 1], [0, 3, 1], [0, 3, 1], [0, 3, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_73_73_17 : ColCert where
  rK := ⟨73, by decide⟩
  rH := ⟨73, by decide⟩
  m := 5
  T1 := T73_73
  T2 := Q2.T73_73_2
  h1 := (0,0,3,1,2)
  h2 := (0,0,3,1,2)
  D := [[0, 3, 2], [0, 3, 2], [0, 3, 2], [0, 3, 2], [0, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_73_73_18 : ColCert where
  rK := ⟨73, by decide⟩
  rH := ⟨73, by decide⟩
  m := 5
  T1 := T73_73
  T2 := Q2.T73_73_2
  h1 := (0,0,3,1,3)
  h2 := (0,0,3,1,3)
  D := [[0, 3, 3], [0, 3, 3], [0, 3, 3], [0, 3, 3], [0, 3, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_73_73_19 : ColCert where
  rK := ⟨73, by decide⟩
  rH := ⟨73, by decide⟩
  m := 5
  T1 := T73_73
  T2 := Q2.T73_73_2
  h1 := (0,0,3,1,4)
  h2 := (0,0,3,1,4)
  D := [[0, 3, 4], [0, 3, 4], [0, 3, 4], [0, 3, 4], [0, 3, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_73_73_20 : ColCert where
  rK := ⟨73, by decide⟩
  rH := ⟨73, by decide⟩
  m := 5
  T1 := T73_73
  T2 := Q2.T73_73_2
  h1 := (0,0,4,3,0)
  h2 := (0,0,4,3,0)
  D := [[0, 4, 0], [0, 4, 0], [0, 4, 0], [0, 4, 0], [0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_73_73_21 : ColCert where
  rK := ⟨73, by decide⟩
  rH := ⟨73, by decide⟩
  m := 5
  T1 := T73_73
  T2 := Q2.T73_73_2
  h1 := (0,0,4,3,1)
  h2 := (0,0,4,3,1)
  D := [[0, 4, 1], [0, 4, 1], [0, 4, 1], [0, 4, 1], [0, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_73_73_22 : ColCert where
  rK := ⟨73, by decide⟩
  rH := ⟨73, by decide⟩
  m := 5
  T1 := T73_73
  T2 := Q2.T73_73_2
  h1 := (0,0,4,3,2)
  h2 := (0,0,4,3,2)
  D := [[0, 4, 2], [0, 4, 2], [0, 4, 2], [0, 4, 2], [0, 4, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_73_73_23 : ColCert where
  rK := ⟨73, by decide⟩
  rH := ⟨73, by decide⟩
  m := 5
  T1 := T73_73
  T2 := Q2.T73_73_2
  h1 := (0,0,4,3,3)
  h2 := (0,0,4,3,3)
  D := [[0, 4, 3], [0, 4, 3], [0, 4, 3], [0, 4, 3], [0, 4, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_73_73_24 : ColCert where
  rK := ⟨73, by decide⟩
  rH := ⟨73, by decide⟩
  m := 5
  T1 := T73_73
  T2 := Q2.T73_73_2
  h1 := (0,0,4,3,4)
  h2 := (0,0,4,3,4)
  D := [[0, 4, 4], [0, 4, 4], [0, 4, 4], [0, 4, 4], [0, 4, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_73_73_25 : ColCert where
  rK := ⟨73, by decide⟩
  rH := ⟨73, by decide⟩
  m := 5
  T1 := T73_73
  T2 := Q2.T73_73_2
  h1 := (1,3,0,0,0)
  h2 := (1,3,0,0,0)
  D := [[1, 0, 1], [1, 0, 0], [1, 0, 4], [1, 0, 3], [1, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_73_73_30 : ColCert where
  rK := ⟨73, by decide⟩
  rH := ⟨73, by decide⟩
  m := 5
  T1 := T73_73
  T2 := Q2.T73_73_2
  h1 := (1,3,1,2,0)
  h2 := (1,3,1,2,0)
  D := [[1, 1, 1], [1, 1, 0], [1, 1, 4], [1, 1, 3], [1, 1, 2]]
  bind1 := by decide
  bind2 := by decide

end LeanDring.P5Presentation
