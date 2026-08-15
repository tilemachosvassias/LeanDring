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
rest tier, chunk 136: 60 columns.
-/

-- machine-emitted data: silence style linters (generated long lines, file-level options)
set_option linter.style.longLine false

namespace LeanDring.P5Presentation

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

def colCert_147_147_13 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨147, by decide⟩
  m := 1
  T1 := T147_147
  T2 := Q2.T147_147_2
  h1 := (0,2,3,0,0)
  h2 := (0,2,3,0,0)
  D := [[0, 2, 3, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_147_14 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨147, by decide⟩
  m := 1
  T1 := T147_147
  T2 := Q2.T147_147_2
  h1 := (0,2,4,0,0)
  h2 := (0,2,4,0,0)
  D := [[0, 2, 4, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_147_15 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨147, by decide⟩
  m := 1
  T1 := T147_147
  T2 := Q2.T147_147_2
  h1 := (0,3,0,0,0)
  h2 := (0,3,0,0,0)
  D := [[0, 3, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_147_16 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨147, by decide⟩
  m := 1
  T1 := T147_147
  T2 := Q2.T147_147_2
  h1 := (0,3,1,0,0)
  h2 := (0,3,1,0,0)
  D := [[0, 3, 1, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_147_17 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨147, by decide⟩
  m := 1
  T1 := T147_147
  T2 := Q2.T147_147_2
  h1 := (0,3,2,0,0)
  h2 := (0,3,2,0,0)
  D := [[0, 3, 2, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_147_18 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨147, by decide⟩
  m := 1
  T1 := T147_147
  T2 := Q2.T147_147_2
  h1 := (0,3,3,0,0)
  h2 := (0,3,3,0,0)
  D := [[0, 3, 3, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_147_19 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨147, by decide⟩
  m := 1
  T1 := T147_147
  T2 := Q2.T147_147_2
  h1 := (0,3,4,0,0)
  h2 := (0,3,4,0,0)
  D := [[0, 3, 4, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_147_20 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨147, by decide⟩
  m := 1
  T1 := T147_147
  T2 := Q2.T147_147_2
  h1 := (0,4,0,0,0)
  h2 := (0,4,0,0,0)
  D := [[0, 4, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_147_21 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨147, by decide⟩
  m := 1
  T1 := T147_147
  T2 := Q2.T147_147_2
  h1 := (0,4,1,0,0)
  h2 := (0,4,1,0,0)
  D := [[0, 4, 1, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_147_22 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨147, by decide⟩
  m := 1
  T1 := T147_147
  T2 := Q2.T147_147_2
  h1 := (0,4,2,0,0)
  h2 := (0,4,2,0,0)
  D := [[0, 4, 2, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_147_23 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨147, by decide⟩
  m := 1
  T1 := T147_147
  T2 := Q2.T147_147_2
  h1 := (0,4,3,0,0)
  h2 := (0,4,3,0,0)
  D := [[0, 4, 3, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_147_24 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨147, by decide⟩
  m := 1
  T1 := T147_147
  T2 := Q2.T147_147_2
  h1 := (0,4,4,0,0)
  h2 := (0,4,4,0,0)
  D := [[0, 4, 4, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_147_25 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨147, by decide⟩
  m := 1
  T1 := T147_147
  T2 := Q2.T147_147_2
  h1 := (1,0,0,0,0)
  h2 := (1,0,0,0,0)
  D := [[1, 0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_147_26 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨147, by decide⟩
  m := 1
  T1 := T147_147
  T2 := Q2.T147_147_2
  h1 := (1,0,1,0,0)
  h2 := (1,0,1,0,0)
  D := [[1, 0, 1, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_147_27 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨147, by decide⟩
  m := 1
  T1 := T147_147
  T2 := Q2.T147_147_2
  h1 := (1,0,2,0,0)
  h2 := (1,0,2,0,0)
  D := [[1, 0, 2, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_147_28 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨147, by decide⟩
  m := 1
  T1 := T147_147
  T2 := Q2.T147_147_2
  h1 := (1,0,3,0,0)
  h2 := (1,0,3,0,0)
  D := [[1, 0, 3, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_147_29 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨147, by decide⟩
  m := 1
  T1 := T147_147
  T2 := Q2.T147_147_2
  h1 := (1,0,4,0,0)
  h2 := (1,0,4,0,0)
  D := [[1, 0, 4, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_147_30 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨147, by decide⟩
  m := 1
  T1 := T147_147
  T2 := Q2.T147_147_2
  h1 := (1,1,0,0,0)
  h2 := (1,1,0,0,0)
  D := [[1, 1, 0, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_147_31 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨147, by decide⟩
  m := 1
  T1 := T147_147
  T2 := Q2.T147_147_2
  h1 := (1,1,1,0,0)
  h2 := (1,1,1,0,0)
  D := [[1, 1, 1, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_147_32 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨147, by decide⟩
  m := 1
  T1 := T147_147
  T2 := Q2.T147_147_2
  h1 := (1,1,2,0,0)
  h2 := (1,1,2,0,0)
  D := [[1, 1, 2, 4, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_147_33 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨147, by decide⟩
  m := 1
  T1 := T147_147
  T2 := Q2.T147_147_2
  h1 := (1,1,3,0,0)
  h2 := (1,1,3,0,0)
  D := [[1, 1, 3, 4, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_147_34 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨147, by decide⟩
  m := 1
  T1 := T147_147
  T2 := Q2.T147_147_2
  h1 := (1,1,4,0,0)
  h2 := (1,1,4,0,0)
  D := [[1, 1, 4, 4, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_147_35 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨147, by decide⟩
  m := 1
  T1 := T147_147
  T2 := Q2.T147_147_2
  h1 := (1,2,0,0,0)
  h2 := (1,2,0,0,0)
  D := [[1, 2, 0, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_147_36 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨147, by decide⟩
  m := 1
  T1 := T147_147
  T2 := Q2.T147_147_2
  h1 := (1,2,1,0,0)
  h2 := (1,2,1,0,0)
  D := [[1, 2, 1, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_147_37 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨147, by decide⟩
  m := 1
  T1 := T147_147
  T2 := Q2.T147_147_2
  h1 := (1,2,2,0,0)
  h2 := (1,2,2,0,0)
  D := [[1, 2, 2, 3, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_147_38 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨147, by decide⟩
  m := 1
  T1 := T147_147
  T2 := Q2.T147_147_2
  h1 := (1,2,3,0,0)
  h2 := (1,2,3,0,0)
  D := [[1, 2, 3, 3, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_147_39 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨147, by decide⟩
  m := 1
  T1 := T147_147
  T2 := Q2.T147_147_2
  h1 := (1,2,4,0,0)
  h2 := (1,2,4,0,0)
  D := [[1, 2, 4, 3, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_147_40 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨147, by decide⟩
  m := 1
  T1 := T147_147
  T2 := Q2.T147_147_2
  h1 := (1,3,0,0,0)
  h2 := (1,3,0,0,0)
  D := [[1, 3, 0, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_147_41 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨147, by decide⟩
  m := 1
  T1 := T147_147
  T2 := Q2.T147_147_2
  h1 := (1,3,1,0,0)
  h2 := (1,3,1,0,0)
  D := [[1, 3, 1, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_147_42 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨147, by decide⟩
  m := 1
  T1 := T147_147
  T2 := Q2.T147_147_2
  h1 := (1,3,2,0,0)
  h2 := (1,3,2,0,0)
  D := [[1, 3, 2, 2, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_147_43 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨147, by decide⟩
  m := 1
  T1 := T147_147
  T2 := Q2.T147_147_2
  h1 := (1,3,3,0,0)
  h2 := (1,3,3,0,0)
  D := [[1, 3, 3, 2, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_147_44 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨147, by decide⟩
  m := 1
  T1 := T147_147
  T2 := Q2.T147_147_2
  h1 := (1,3,4,0,0)
  h2 := (1,3,4,0,0)
  D := [[1, 3, 4, 2, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_147_45 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨147, by decide⟩
  m := 1
  T1 := T147_147
  T2 := Q2.T147_147_2
  h1 := (1,4,0,0,0)
  h2 := (1,4,0,0,0)
  D := [[1, 4, 0, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_147_46 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨147, by decide⟩
  m := 1
  T1 := T147_147
  T2 := Q2.T147_147_2
  h1 := (1,4,1,0,0)
  h2 := (1,4,1,0,0)
  D := [[1, 4, 1, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_147_47 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨147, by decide⟩
  m := 1
  T1 := T147_147
  T2 := Q2.T147_147_2
  h1 := (1,4,2,0,0)
  h2 := (1,4,2,0,0)
  D := [[1, 4, 2, 1, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_147_48 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨147, by decide⟩
  m := 1
  T1 := T147_147
  T2 := Q2.T147_147_2
  h1 := (1,4,3,0,0)
  h2 := (1,4,3,0,0)
  D := [[1, 4, 3, 1, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_147_49 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨147, by decide⟩
  m := 1
  T1 := T147_147
  T2 := Q2.T147_147_2
  h1 := (1,4,4,0,0)
  h2 := (1,4,4,0,0)
  D := [[1, 4, 4, 1, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_147_50 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨147, by decide⟩
  m := 1
  T1 := T147_147
  T2 := Q2.T147_147_2
  h1 := (2,0,0,0,0)
  h2 := (2,0,0,0,0)
  D := [[2, 0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_147_51 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨147, by decide⟩
  m := 1
  T1 := T147_147
  T2 := Q2.T147_147_2
  h1 := (2,0,1,0,0)
  h2 := (2,0,1,0,0)
  D := [[2, 0, 1, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_147_52 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨147, by decide⟩
  m := 1
  T1 := T147_147
  T2 := Q2.T147_147_2
  h1 := (2,0,2,0,0)
  h2 := (2,0,2,0,0)
  D := [[2, 0, 2, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_147_53 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨147, by decide⟩
  m := 1
  T1 := T147_147
  T2 := Q2.T147_147_2
  h1 := (2,0,3,0,0)
  h2 := (2,0,3,0,0)
  D := [[2, 0, 3, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_147_54 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨147, by decide⟩
  m := 1
  T1 := T147_147
  T2 := Q2.T147_147_2
  h1 := (2,0,4,0,0)
  h2 := (2,0,4,0,0)
  D := [[2, 0, 4, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_147_55 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨147, by decide⟩
  m := 1
  T1 := T147_147
  T2 := Q2.T147_147_2
  h1 := (2,1,0,0,0)
  h2 := (2,1,0,0,0)
  D := [[2, 1, 0, 3, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_147_56 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨147, by decide⟩
  m := 1
  T1 := T147_147
  T2 := Q2.T147_147_2
  h1 := (2,1,1,0,0)
  h2 := (2,1,1,0,0)
  D := [[2, 1, 1, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_147_57 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨147, by decide⟩
  m := 1
  T1 := T147_147
  T2 := Q2.T147_147_2
  h1 := (2,1,2,0,0)
  h2 := (2,1,2,0,0)
  D := [[2, 1, 2, 3, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_147_58 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨147, by decide⟩
  m := 1
  T1 := T147_147
  T2 := Q2.T147_147_2
  h1 := (2,1,3,0,0)
  h2 := (2,1,3,0,0)
  D := [[2, 1, 3, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_147_59 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨147, by decide⟩
  m := 1
  T1 := T147_147
  T2 := Q2.T147_147_2
  h1 := (2,1,4,0,0)
  h2 := (2,1,4,0,0)
  D := [[2, 1, 4, 3, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_147_60 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨147, by decide⟩
  m := 1
  T1 := T147_147
  T2 := Q2.T147_147_2
  h1 := (2,2,0,0,0)
  h2 := (2,2,0,0,0)
  D := [[2, 2, 0, 1, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_147_61 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨147, by decide⟩
  m := 1
  T1 := T147_147
  T2 := Q2.T147_147_2
  h1 := (2,2,1,0,0)
  h2 := (2,2,1,0,0)
  D := [[2, 2, 1, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_147_62 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨147, by decide⟩
  m := 1
  T1 := T147_147
  T2 := Q2.T147_147_2
  h1 := (2,2,2,0,0)
  h2 := (2,2,2,0,0)
  D := [[2, 2, 2, 1, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_147_63 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨147, by decide⟩
  m := 1
  T1 := T147_147
  T2 := Q2.T147_147_2
  h1 := (2,2,3,0,0)
  h2 := (2,2,3,0,0)
  D := [[2, 2, 3, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_147_64 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨147, by decide⟩
  m := 1
  T1 := T147_147
  T2 := Q2.T147_147_2
  h1 := (2,2,4,0,0)
  h2 := (2,2,4,0,0)
  D := [[2, 2, 4, 1, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_147_65 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨147, by decide⟩
  m := 1
  T1 := T147_147
  T2 := Q2.T147_147_2
  h1 := (2,3,0,0,0)
  h2 := (2,3,0,0,0)
  D := [[2, 3, 0, 4, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_147_66 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨147, by decide⟩
  m := 1
  T1 := T147_147
  T2 := Q2.T147_147_2
  h1 := (2,3,1,0,0)
  h2 := (2,3,1,0,0)
  D := [[2, 3, 1, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_147_67 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨147, by decide⟩
  m := 1
  T1 := T147_147
  T2 := Q2.T147_147_2
  h1 := (2,3,2,0,0)
  h2 := (2,3,2,0,0)
  D := [[2, 3, 2, 4, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_147_68 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨147, by decide⟩
  m := 1
  T1 := T147_147
  T2 := Q2.T147_147_2
  h1 := (2,3,3,0,0)
  h2 := (2,3,3,0,0)
  D := [[2, 3, 3, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_147_69 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨147, by decide⟩
  m := 1
  T1 := T147_147
  T2 := Q2.T147_147_2
  h1 := (2,3,4,0,0)
  h2 := (2,3,4,0,0)
  D := [[2, 3, 4, 4, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_147_70 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨147, by decide⟩
  m := 1
  T1 := T147_147
  T2 := Q2.T147_147_2
  h1 := (2,4,0,0,0)
  h2 := (2,4,0,0,0)
  D := [[2, 4, 0, 2, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_147_71 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨147, by decide⟩
  m := 1
  T1 := T147_147
  T2 := Q2.T147_147_2
  h1 := (2,4,1,0,0)
  h2 := (2,4,1,0,0)
  D := [[2, 4, 1, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_147_147_72 : ColCert where
  rK := ⟨147, by decide⟩
  rH := ⟨147, by decide⟩
  m := 1
  T1 := T147_147
  T2 := Q2.T147_147_2
  h1 := (2,4,2,0,0)
  h2 := (2,4,2,0,0)
  D := [[2, 4, 2, 2, 4]]
  bind1 := by decide
  bind2 := by decide

end LeanDring.P5Presentation
