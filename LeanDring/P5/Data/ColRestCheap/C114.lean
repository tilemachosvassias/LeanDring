/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.Twin1.ColCert
import LeanDring.P5.Data.EntryK.C044

/-!
# Species-table cell data, stage 2 — twin-coincident columns (cheap tier)

Per-column certified exponent-vector data (`ColCert`/`ColCertDiv`) with kernel
`decide` bindings. Emitted; the embedded lists are what the kernel certifies.
rest tier, chunk 113: 60 columns.
-/

-- machine-emitted data: silence style linters (generated long lines, file-level options)
set_option linter.style.longLine false

namespace LeanDring.P5Presentation

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

def colCert_147_35_3 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨35, by decide⟩
  m := 1
  T1 := T147_35
  T2 := Q2.T147_35_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_35_4 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨35, by decide⟩
  m := 1
  T1 := T147_35
  T2 := Q2.T147_35_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_36_0 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨36, by decide⟩
  m := 1
  T1 := T147_36
  T2 := Q2.T147_36_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_36_1 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨36, by decide⟩
  m := 1
  T1 := T147_36
  T2 := Q2.T147_36_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_36_2 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨36, by decide⟩
  m := 1
  T1 := T147_36
  T2 := Q2.T147_36_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_36_3 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨36, by decide⟩
  m := 1
  T1 := T147_36
  T2 := Q2.T147_36_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_36_4 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨36, by decide⟩
  m := 1
  T1 := T147_36
  T2 := Q2.T147_36_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_37_0 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨37, by decide⟩
  m := 1
  T1 := T147_37
  T2 := Q2.T147_37_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_37_1 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨37, by decide⟩
  m := 1
  T1 := T147_37
  T2 := Q2.T147_37_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_37_2 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨37, by decide⟩
  m := 1
  T1 := T147_37
  T2 := Q2.T147_37_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_37_3 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨37, by decide⟩
  m := 1
  T1 := T147_37
  T2 := Q2.T147_37_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_37_4 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨37, by decide⟩
  m := 1
  T1 := T147_37
  T2 := Q2.T147_37_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_38_0 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨38, by decide⟩
  m := 1
  T1 := T147_38
  T2 := Q2.T147_38_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_38_1 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨38, by decide⟩
  m := 1
  T1 := T147_38
  T2 := Q2.T147_38_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_38_2 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨38, by decide⟩
  m := 1
  T1 := T147_38
  T2 := Q2.T147_38_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_38_3 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨38, by decide⟩
  m := 1
  T1 := T147_38
  T2 := Q2.T147_38_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_38_4 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨38, by decide⟩
  m := 1
  T1 := T147_38
  T2 := Q2.T147_38_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_39_0 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨39, by decide⟩
  m := 1
  T1 := T147_39
  T2 := Q2.T147_39_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_39_1 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨39, by decide⟩
  m := 1
  T1 := T147_39
  T2 := Q2.T147_39_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_39_2 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨39, by decide⟩
  m := 1
  T1 := T147_39
  T2 := Q2.T147_39_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_39_3 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨39, by decide⟩
  m := 1
  T1 := T147_39
  T2 := Q2.T147_39_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_39_4 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨39, by decide⟩
  m := 1
  T1 := T147_39
  T2 := Q2.T147_39_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_39_5 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨39, by decide⟩
  m := 1
  T1 := T147_39
  T2 := Q2.T147_39_2
  h1 := (1,4,2,3,2)
  h2 := (1,4,2,3,2)
  D := [[1, 4, 2, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_40_0 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨40, by decide⟩
  m := 1
  T1 := T147_40
  T2 := Q2.T147_40_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_40_1 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨40, by decide⟩
  m := 1
  T1 := T147_40
  T2 := Q2.T147_40_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_40_2 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨40, by decide⟩
  m := 1
  T1 := T147_40
  T2 := Q2.T147_40_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_40_3 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨40, by decide⟩
  m := 1
  T1 := T147_40
  T2 := Q2.T147_40_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_40_4 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨40, by decide⟩
  m := 1
  T1 := T147_40
  T2 := Q2.T147_40_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_41_0 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨41, by decide⟩
  m := 1
  T1 := T147_41
  T2 := Q2.T147_41_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_41_1 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨41, by decide⟩
  m := 1
  T1 := T147_41
  T2 := Q2.T147_41_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_41_2 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨41, by decide⟩
  m := 1
  T1 := T147_41
  T2 := Q2.T147_41_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_41_3 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨41, by decide⟩
  m := 1
  T1 := T147_41
  T2 := Q2.T147_41_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_41_4 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨41, by decide⟩
  m := 1
  T1 := T147_41
  T2 := Q2.T147_41_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_42_0 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨42, by decide⟩
  m := 1
  T1 := T147_42
  T2 := Q2.T147_42_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_42_1 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨42, by decide⟩
  m := 1
  T1 := T147_42
  T2 := Q2.T147_42_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_42_2 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨42, by decide⟩
  m := 1
  T1 := T147_42
  T2 := Q2.T147_42_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_42_3 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨42, by decide⟩
  m := 1
  T1 := T147_42
  T2 := Q2.T147_42_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_42_4 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨42, by decide⟩
  m := 1
  T1 := T147_42
  T2 := Q2.T147_42_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_43_0 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨43, by decide⟩
  m := 1
  T1 := T147_43
  T2 := Q2.T147_43_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_43_1 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨43, by decide⟩
  m := 1
  T1 := T147_43
  T2 := Q2.T147_43_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_43_2 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨43, by decide⟩
  m := 1
  T1 := T147_43
  T2 := Q2.T147_43_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_43_3 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨43, by decide⟩
  m := 1
  T1 := T147_43
  T2 := Q2.T147_43_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_43_4 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨43, by decide⟩
  m := 1
  T1 := T147_43
  T2 := Q2.T147_43_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_44_0 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨44, by decide⟩
  m := 1
  T1 := T147_44
  T2 := Q2.T147_44_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_44_1 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨44, by decide⟩
  m := 1
  T1 := T147_44
  T2 := Q2.T147_44_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_44_2 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨44, by decide⟩
  m := 1
  T1 := T147_44
  T2 := Q2.T147_44_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_44_3 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨44, by decide⟩
  m := 1
  T1 := T147_44
  T2 := Q2.T147_44_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_44_4 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨44, by decide⟩
  m := 1
  T1 := T147_44
  T2 := Q2.T147_44_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_44_5 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨44, by decide⟩
  m := 1
  T1 := T147_44
  T2 := Q2.T147_44_2
  h1 := (1,4,4,3,0)
  h2 := (1,4,4,3,0)
  D := [[1, 4, 4, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_45_0 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨45, by decide⟩
  m := 1
  T1 := T147_45
  T2 := Q2.T147_45_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_45_1 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨45, by decide⟩
  m := 1
  T1 := T147_45
  T2 := Q2.T147_45_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_45_2 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨45, by decide⟩
  m := 1
  T1 := T147_45
  T2 := Q2.T147_45_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_45_3 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨45, by decide⟩
  m := 1
  T1 := T147_45
  T2 := Q2.T147_45_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_45_4 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨45, by decide⟩
  m := 1
  T1 := T147_45
  T2 := Q2.T147_45_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_46_0 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨46, by decide⟩
  m := 1
  T1 := T147_46
  T2 := Q2.T147_46_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_46_1 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨46, by decide⟩
  m := 1
  T1 := T147_46
  T2 := Q2.T147_46_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_46_2 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨46, by decide⟩
  m := 1
  T1 := T147_46
  T2 := Q2.T147_46_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_46_3 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨46, by decide⟩
  m := 1
  T1 := T147_46
  T2 := Q2.T147_46_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_46_4 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨46, by decide⟩
  m := 1
  T1 := T147_46
  T2 := Q2.T147_46_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_47_0 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨47, by decide⟩
  m := 1
  T1 := T147_47
  T2 := Q2.T147_47_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

end LeanDring.P5Presentation
