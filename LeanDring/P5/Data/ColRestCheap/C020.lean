/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.Twin1.ColCert
import LeanDring.P5.Data.EntryK.C025

/-!
# Species-table cell data, stage 2 — twin-coincident columns (cheap tier)

Per-column certified exponent-vector data (`ColCert`/`ColCertDiv`) with kernel
`decide` bindings. Emitted; the embedded lists are what the kernel certifies.
rest tier, chunk 19: 60 columns.
-/

-- machine-emitted data: silence style linters (generated long lines, file-level options)
set_option linter.style.longLine false

namespace LeanDring.P5Presentation

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

def colCert_116_33_3 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨33, by decide⟩
  m := 5
  T1 := T116_33
  T2 := Q2.T116_33_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_33_4 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨33, by decide⟩
  m := 5
  T1 := T116_33
  T2 := Q2.T116_33_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_38_0 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨38, by decide⟩
  m := 5
  T1 := T116_38
  T2 := Q2.T116_38_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_38_1 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨38, by decide⟩
  m := 5
  T1 := T116_38
  T2 := Q2.T116_38_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_38_2 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨38, by decide⟩
  m := 5
  T1 := T116_38
  T2 := Q2.T116_38_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_38_3 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨38, by decide⟩
  m := 5
  T1 := T116_38
  T2 := Q2.T116_38_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_38_4 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨38, by decide⟩
  m := 5
  T1 := T116_38
  T2 := Q2.T116_38_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_43_0 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨43, by decide⟩
  m := 5
  T1 := T116_43
  T2 := Q2.T116_43_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_43_1 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨43, by decide⟩
  m := 5
  T1 := T116_43
  T2 := Q2.T116_43_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_43_2 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨43, by decide⟩
  m := 5
  T1 := T116_43
  T2 := Q2.T116_43_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_43_3 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨43, by decide⟩
  m := 5
  T1 := T116_43
  T2 := Q2.T116_43_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_43_4 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨43, by decide⟩
  m := 5
  T1 := T116_43
  T2 := Q2.T116_43_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_48_0 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨48, by decide⟩
  m := 5
  T1 := T116_48
  T2 := Q2.T116_48_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_48_1 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨48, by decide⟩
  m := 5
  T1 := T116_48
  T2 := Q2.T116_48_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_48_2 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨48, by decide⟩
  m := 5
  T1 := T116_48
  T2 := Q2.T116_48_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_48_3 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨48, by decide⟩
  m := 5
  T1 := T116_48
  T2 := Q2.T116_48_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_48_4 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨48, by decide⟩
  m := 5
  T1 := T116_48
  T2 := Q2.T116_48_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_53_0 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T116_53
  T2 := Q2.T116_53_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_53_1 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T116_53
  T2 := Q2.T116_53_2
  h1 := (0,0,0,0,1)
  h2 := (0,0,0,0,1)
  D := [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_53_2 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T116_53
  T2 := Q2.T116_53_2
  h1 := (0,0,0,0,2)
  h2 := (0,0,0,0,2)
  D := [[0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_53_3 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T116_53
  T2 := Q2.T116_53_2
  h1 := (0,0,0,0,3)
  h2 := (0,0,0,0,3)
  D := [[0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3], [0, 0, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_53_4 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T116_53
  T2 := Q2.T116_53_2
  h1 := (0,0,0,0,4)
  h2 := (0,0,0,0,4)
  D := [[0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4], [0, 0, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_53_5 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T116_53
  T2 := Q2.T116_53_2
  h1 := (0,0,0,1,0)
  h2 := (0,0,0,1,0)
  D := [[0, 0, 1, 0], [0, 0, 1, 1], [0, 0, 1, 2], [0, 0, 1, 3], [0, 0, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_53_10 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T116_53
  T2 := Q2.T116_53_2
  h1 := (0,0,0,2,0)
  h2 := (0,0,0,2,0)
  D := [[0, 0, 2, 0], [0, 0, 2, 2], [0, 0, 2, 4], [0, 0, 2, 1], [0, 0, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_53_15 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T116_53
  T2 := Q2.T116_53_2
  h1 := (0,0,0,3,0)
  h2 := (0,0,0,3,0)
  D := [[0, 0, 3, 0], [0, 0, 3, 3], [0, 0, 3, 1], [0, 0, 3, 4], [0, 0, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_53_20 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨53, by decide⟩
  m := 5
  T1 := T116_53
  T2 := Q2.T116_53_2
  h1 := (0,0,0,4,0)
  h2 := (0,0,0,4,0)
  D := [[0, 0, 4, 0], [0, 0, 4, 4], [0, 0, 4, 3], [0, 0, 4, 2], [0, 0, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_55_0 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨55, by decide⟩
  m := 5
  T1 := T116_55
  T2 := Q2.T116_55_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_55_1 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨55, by decide⟩
  m := 5
  T1 := T116_55
  T2 := Q2.T116_55_2
  h1 := (0,0,1,0,0)
  h2 := (0,0,1,0,0)
  D := [[0, 1, 0, 0], [0, 1, 0, 0], [0, 1, 0, 0], [0, 1, 0, 0], [0, 1, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_55_2 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨55, by decide⟩
  m := 5
  T1 := T116_55
  T2 := Q2.T116_55_2
  h1 := (0,0,2,0,0)
  h2 := (0,0,2,0,0)
  D := [[0, 2, 0, 0], [0, 2, 0, 0], [0, 2, 0, 0], [0, 2, 0, 0], [0, 2, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_55_3 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨55, by decide⟩
  m := 5
  T1 := T116_55
  T2 := Q2.T116_55_2
  h1 := (0,0,3,0,0)
  h2 := (0,0,3,0,0)
  D := [[0, 3, 0, 0], [0, 3, 0, 0], [0, 3, 0, 0], [0, 3, 0, 0], [0, 3, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_55_4 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨55, by decide⟩
  m := 5
  T1 := T116_55
  T2 := Q2.T116_55_2
  h1 := (0,0,4,0,0)
  h2 := (0,0,4,0,0)
  D := [[0, 4, 0, 0], [0, 4, 0, 0], [0, 4, 0, 0], [0, 4, 0, 0], [0, 4, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_56_0 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨56, by decide⟩
  m := 5
  T1 := T116_56
  T2 := Q2.T116_56_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_56_1 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨56, by decide⟩
  m := 5
  T1 := T116_56
  T2 := Q2.T116_56_2
  h1 := (0,0,1,4,0)
  h2 := (0,0,1,4,0)
  D := [[0, 1, 4, 0], [0, 1, 4, 4], [0, 1, 4, 3], [0, 1, 4, 2], [0, 1, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_56_2 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨56, by decide⟩
  m := 5
  T1 := T116_56
  T2 := Q2.T116_56_2
  h1 := (0,0,2,3,0)
  h2 := (0,0,2,3,0)
  D := [[0, 2, 3, 0], [0, 2, 3, 3], [0, 2, 3, 1], [0, 2, 3, 4], [0, 2, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_56_3 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨56, by decide⟩
  m := 5
  T1 := T116_56
  T2 := Q2.T116_56_2
  h1 := (0,0,3,2,0)
  h2 := (0,0,3,2,0)
  D := [[0, 3, 2, 0], [0, 3, 2, 2], [0, 3, 2, 4], [0, 3, 2, 1], [0, 3, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_56_4 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨56, by decide⟩
  m := 5
  T1 := T116_56
  T2 := Q2.T116_56_2
  h1 := (0,0,4,1,0)
  h2 := (0,0,4,1,0)
  D := [[0, 4, 1, 0], [0, 4, 1, 1], [0, 4, 1, 2], [0, 4, 1, 3], [0, 4, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_57_0 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨57, by decide⟩
  m := 5
  T1 := T116_57
  T2 := Q2.T116_57_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_57_1 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨57, by decide⟩
  m := 5
  T1 := T116_57
  T2 := Q2.T116_57_2
  h1 := (0,0,1,3,0)
  h2 := (0,0,1,3,0)
  D := [[0, 1, 3, 0], [0, 1, 3, 3], [0, 1, 3, 1], [0, 1, 3, 4], [0, 1, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_57_2 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨57, by decide⟩
  m := 5
  T1 := T116_57
  T2 := Q2.T116_57_2
  h1 := (0,0,2,1,0)
  h2 := (0,0,2,1,0)
  D := [[0, 2, 1, 0], [0, 2, 1, 1], [0, 2, 1, 2], [0, 2, 1, 3], [0, 2, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_57_3 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨57, by decide⟩
  m := 5
  T1 := T116_57
  T2 := Q2.T116_57_2
  h1 := (0,0,3,4,0)
  h2 := (0,0,3,4,0)
  D := [[0, 3, 4, 0], [0, 3, 4, 4], [0, 3, 4, 3], [0, 3, 4, 2], [0, 3, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_57_4 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨57, by decide⟩
  m := 5
  T1 := T116_57
  T2 := Q2.T116_57_2
  h1 := (0,0,4,2,0)
  h2 := (0,0,4,2,0)
  D := [[0, 4, 2, 0], [0, 4, 2, 2], [0, 4, 2, 4], [0, 4, 2, 1], [0, 4, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_58_0 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨58, by decide⟩
  m := 5
  T1 := T116_58
  T2 := Q2.T116_58_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_58_1 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨58, by decide⟩
  m := 5
  T1 := T116_58
  T2 := Q2.T116_58_2
  h1 := (0,0,1,2,0)
  h2 := (0,0,1,2,0)
  D := [[0, 1, 2, 0], [0, 1, 2, 2], [0, 1, 2, 4], [0, 1, 2, 1], [0, 1, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_58_2 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨58, by decide⟩
  m := 5
  T1 := T116_58
  T2 := Q2.T116_58_2
  h1 := (0,0,2,4,0)
  h2 := (0,0,2,4,0)
  D := [[0, 2, 4, 0], [0, 2, 4, 4], [0, 2, 4, 3], [0, 2, 4, 2], [0, 2, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_58_3 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨58, by decide⟩
  m := 5
  T1 := T116_58
  T2 := Q2.T116_58_2
  h1 := (0,0,3,1,0)
  h2 := (0,0,3,1,0)
  D := [[0, 3, 1, 0], [0, 3, 1, 1], [0, 3, 1, 2], [0, 3, 1, 3], [0, 3, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_58_4 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨58, by decide⟩
  m := 5
  T1 := T116_58
  T2 := Q2.T116_58_2
  h1 := (0,0,4,3,0)
  h2 := (0,0,4,3,0)
  D := [[0, 4, 3, 0], [0, 4, 3, 3], [0, 4, 3, 1], [0, 4, 3, 4], [0, 4, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_59_0 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨59, by decide⟩
  m := 5
  T1 := T116_59
  T2 := Q2.T116_59_2
  h1 := (0,0,0,0,0)
  h2 := (0,0,0,0,0)
  D := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_59_1 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨59, by decide⟩
  m := 5
  T1 := T116_59
  T2 := Q2.T116_59_2
  h1 := (0,0,1,1,0)
  h2 := (0,0,1,1,0)
  D := [[0, 1, 1, 0], [0, 1, 1, 1], [0, 1, 1, 2], [0, 1, 1, 3], [0, 1, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_59_2 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨59, by decide⟩
  m := 5
  T1 := T116_59
  T2 := Q2.T116_59_2
  h1 := (0,0,2,2,0)
  h2 := (0,0,2,2,0)
  D := [[0, 2, 2, 0], [0, 2, 2, 2], [0, 2, 2, 4], [0, 2, 2, 1], [0, 2, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_59_3 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨59, by decide⟩
  m := 5
  T1 := T116_59
  T2 := Q2.T116_59_2
  h1 := (0,0,3,3,0)
  h2 := (0,0,3,3,0)
  D := [[0, 3, 3, 0], [0, 3, 3, 3], [0, 3, 3, 1], [0, 3, 3, 4], [0, 3, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_59_4 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨59, by decide⟩
  m := 5
  T1 := T116_59
  T2 := Q2.T116_59_2
  h1 := (0,0,4,4,0)
  h2 := (0,0,4,4,0)
  D := [[0, 4, 4, 0], [0, 4, 4, 4], [0, 4, 4, 3], [0, 4, 4, 2], [0, 4, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_59_5 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨59, by decide⟩
  m := 5
  T1 := T116_59
  T2 := Q2.T116_59_2
  h1 := (0,1,0,4,0)
  h2 := (0,1,0,4,0)
  D := [[1, 0, 4, 0], [1, 0, 0, 4], [1, 0, 1, 4], [1, 0, 2, 0], [1, 0, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_59_6 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨59, by decide⟩
  m := 5
  T1 := T116_59
  T2 := Q2.T116_59_2
  h1 := (0,1,1,0,0)
  h2 := (0,1,1,0,0)
  D := [[1, 1, 0, 4], [1, 1, 1, 4], [1, 1, 2, 0], [1, 1, 3, 2], [1, 1, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_59_7 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨59, by decide⟩
  m := 5
  T1 := T116_59
  T2 := Q2.T116_59_2
  h1 := (0,1,2,1,0)
  h2 := (0,1,2,1,0)
  D := [[1, 2, 1, 3], [1, 2, 2, 4], [1, 2, 3, 1], [1, 2, 4, 4], [1, 2, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_59_8 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨59, by decide⟩
  m := 5
  T1 := T116_59
  T2 := Q2.T116_59_2
  h1 := (0,1,3,2,0)
  h2 := (0,1,3,2,0)
  D := [[1, 3, 2, 2], [1, 3, 3, 4], [1, 3, 4, 2], [1, 3, 0, 1], [1, 3, 1, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_59_9 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨59, by decide⟩
  m := 5
  T1 := T116_59
  T2 := Q2.T116_59_2
  h1 := (0,1,4,3,0)
  h2 := (0,1,4,3,0)
  D := [[1, 4, 3, 1], [1, 4, 4, 4], [1, 4, 0, 3], [1, 4, 1, 3], [1, 4, 2, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_59_10 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨59, by decide⟩
  m := 5
  T1 := T116_59
  T2 := Q2.T116_59_2
  h1 := (0,2,0,3,0)
  h2 := (0,2,0,3,0)
  D := [[2, 0, 3, 0], [2, 0, 0, 3], [2, 0, 2, 3], [2, 0, 4, 0], [2, 0, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_59_11 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨59, by decide⟩
  m := 5
  T1 := T116_59
  T2 := Q2.T116_59_2
  h1 := (0,2,1,4,0)
  h2 := (0,2,1,4,0)
  D := [[2, 1, 4, 3], [2, 1, 1, 2], [2, 1, 3, 3], [2, 1, 0, 1], [2, 1, 2, 1]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_59_12 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨59, by decide⟩
  m := 5
  T1 := T116_59
  T2 := Q2.T116_59_2
  h1 := (0,2,2,0,0)
  h2 := (0,2,2,0,0)
  D := [[2, 2, 0, 1], [2, 2, 2, 1], [2, 2, 4, 3], [2, 2, 1, 2], [2, 2, 3, 3]]
  bind1 := by decide
  bind2 := by decide

def colCert_116_59_13 : ColCert where
  rK := ⟨116, by decide⟩
  rH := ⟨59, by decide⟩
  m := 5
  T1 := T116_59
  T2 := Q2.T116_59_2
  h1 := (0,2,3,1,0)
  h2 := (0,2,3,1,0)
  D := [[2, 3, 1, 4], [2, 3, 3, 0], [2, 3, 0, 3], [2, 3, 2, 3], [2, 3, 4, 0]]
  bind1 := by decide
  bind2 := by decide

end LeanDring.P5Presentation
