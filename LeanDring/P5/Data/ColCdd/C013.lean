/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.Twin1.ColCert
import LeanDring.P5.Data.EntryK.C033
import LeanDring.P5.Data.EntryK.C034

/-!
# Species-table cell data, stage 2 — column-data-divergent columns

Per-column certified exponent-vector data (`ColCert`/`ColCertDiv`) with kernel
`decide` bindings. Emitted; the embedded lists are what the kernel certifies.
cdd tier, chunk 12: 60 columns.
-/

-- machine-emitted data: silence style linters (generated long lines, file-level options)
set_option linter.style.longLine false

namespace LeanDring.P5Presentation

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

def colCertDiv_128_103_15 : ColCertDiv where
  rK := ⟨128, by decide⟩
  rH := ⟨103, by decide⟩
  m := 5
  T1 := T128_103
  T2 := Q2.T128_103_2
  h1 := (3,4,2,2,1)
  h2 := (3,4,2,2,2)
  D1 := [[3, 4, 1, 3], [3, 4, 1, 4], [3, 4, 1, 0], [3, 4, 1, 1], [3, 4, 1, 2]]
  D2 := [[3, 4, 1, 0], [3, 4, 1, 1], [3, 4, 1, 2], [3, 4, 1, 3], [3, 4, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_128_109_5 : ColCertDiv where
  rK := ⟨128, by decide⟩
  rH := ⟨109, by decide⟩
  m := 5
  T1 := T128_109
  T2 := Q2.T128_109_2
  h1 := (1,1,1,0,0)
  h2 := (1,1,1,0,0)
  D1 := [[1, 1, 1, 0], [1, 1, 1, 4], [1, 1, 1, 3], [1, 1, 1, 2], [1, 1, 1, 1]]
  D2 := [[1, 1, 1, 3], [1, 1, 1, 2], [1, 1, 1, 1], [1, 1, 1, 0], [1, 1, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_128_109_10 : ColCertDiv where
  rK := ⟨128, by decide⟩
  rH := ⟨109, by decide⟩
  m := 5
  T1 := T128_109
  T2 := Q2.T128_109_2
  h1 := (2,2,2,1,1)
  h2 := (2,2,2,1,1)
  D1 := [[2, 2, 1, 2], [2, 2, 1, 0], [2, 2, 1, 3], [2, 2, 1, 1], [2, 2, 1, 4]]
  D2 := [[2, 2, 1, 3], [2, 2, 1, 1], [2, 2, 1, 4], [2, 2, 1, 2], [2, 2, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_128_109_15 : ColCertDiv where
  rK := ⟨128, by decide⟩
  rH := ⟨109, by decide⟩
  m := 5
  T1 := T128_109
  T2 := Q2.T128_109_2
  h1 := (3,3,3,3,4)
  h2 := (3,3,3,3,4)
  D1 := [[3, 3, 0, 2], [3, 3, 0, 4], [3, 3, 0, 1], [3, 3, 0, 3], [3, 3, 0, 0]]
  D2 := [[3, 3, 0, 1], [3, 3, 0, 3], [3, 3, 0, 0], [3, 3, 0, 2], [3, 3, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_128_109_20 : ColCertDiv where
  rK := ⟨128, by decide⟩
  rH := ⟨109, by decide⟩
  m := 5
  T1 := T128_109
  T2 := Q2.T128_109_2
  h1 := (4,4,4,1,0)
  h2 := (4,4,4,1,0)
  D1 := [[4, 4, 3, 1], [4, 4, 3, 2], [4, 4, 3, 3], [4, 4, 3, 4], [4, 4, 3, 0]]
  D2 := [[4, 4, 3, 3], [4, 4, 3, 4], [4, 4, 3, 0], [4, 4, 3, 1], [4, 4, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_128_112_15 : ColCertDiv where
  rK := ⟨128, by decide⟩
  rH := ⟨112, by decide⟩
  m := 5
  T1 := T128_112
  T2 := Q2.T128_112_2
  h1 := (3,1,0,0,1)
  h2 := (3,1,0,0,2)
  D1 := [[3, 1, 3, 4], [3, 1, 3, 3], [3, 1, 3, 2], [3, 1, 3, 1], [3, 1, 3, 0]]
  D2 := [[3, 1, 3, 0], [3, 1, 3, 4], [3, 1, 3, 3], [3, 1, 3, 2], [3, 1, 3, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_128_112_20 : ColCertDiv where
  rK := ⟨128, by decide⟩
  rH := ⟨112, by decide⟩
  m := 5
  T1 := T128_112
  T2 := Q2.T128_112_2
  h1 := (4,3,0,4,4)
  h2 := (4,3,0,4,0)
  D1 := [[4, 3, 0, 3], [4, 3, 0, 0], [4, 3, 0, 2], [4, 3, 0, 4], [4, 3, 0, 1]]
  D2 := [[4, 3, 0, 4], [4, 3, 0, 1], [4, 3, 0, 3], [4, 3, 0, 0], [4, 3, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_129_29_10 : ColCertDiv where
  rK := ⟨129, by decide⟩
  rH := ⟨29, by decide⟩
  m := 5
  T1 := T129_29
  T2 := Q2.T129_29_2
  h1 := (2,3,2,0,4)
  h2 := (2,3,2,0,0)
  D1 := [[2, 3, 2, 3], [2, 3, 2, 0], [2, 3, 2, 2], [2, 3, 2, 4], [2, 3, 2, 1]]
  D2 := [[2, 3, 2, 4], [2, 3, 2, 1], [2, 3, 2, 3], [2, 3, 2, 0], [2, 3, 2, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_129_29_15 : ColCertDiv where
  rK := ⟨129, by decide⟩
  rH := ⟨29, by decide⟩
  m := 5
  T1 := T129_29
  T2 := Q2.T129_29_2
  h1 := (3,2,3,1,1)
  h2 := (3,2,3,1,3)
  D1 := [[3, 2, 2, 0], [3, 2, 2, 3], [3, 2, 2, 1], [3, 2, 2, 4], [3, 2, 2, 2]]
  D2 := [[3, 2, 2, 2], [3, 2, 2, 0], [3, 2, 2, 3], [3, 2, 2, 1], [3, 2, 2, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_129_29_20 : ColCertDiv where
  rK := ⟨129, by decide⟩
  rH := ⟨29, by decide⟩
  m := 5
  T1 := T129_29
  T2 := Q2.T129_29_2
  h1 := (4,1,4,1,3)
  h2 := (4,1,4,1,1)
  D1 := [[4, 1, 3, 4], [4, 1, 3, 3], [4, 1, 3, 2], [4, 1, 3, 1], [4, 1, 3, 0]]
  D2 := [[4, 1, 3, 2], [4, 1, 3, 1], [4, 1, 3, 0], [4, 1, 3, 4], [4, 1, 3, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_129_35_5 : ColCertDiv where
  rK := ⟨129, by decide⟩
  rH := ⟨35, by decide⟩
  m := 5
  T1 := T129_35
  T2 := Q2.T129_35_2
  h1 := (1,2,4,2,0)
  h2 := (1,2,4,2,2)
  D1 := [[1, 2, 4, 1], [1, 2, 4, 4], [1, 2, 4, 2], [1, 2, 4, 0], [1, 2, 4, 3]]
  D2 := [[1, 2, 4, 3], [1, 2, 4, 1], [1, 2, 4, 4], [1, 2, 4, 2], [1, 2, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_129_35_10 : ColCertDiv where
  rK := ⟨129, by decide⟩
  rH := ⟨35, by decide⟩
  m := 5
  T1 := T129_35
  T2 := Q2.T129_35_2
  h1 := (2,4,3,1,0)
  h2 := (2,4,3,1,4)
  D1 := [[2, 4, 1, 4], [2, 4, 1, 0], [2, 4, 1, 1], [2, 4, 1, 2], [2, 4, 1, 3]]
  D2 := [[2, 4, 1, 3], [2, 4, 1, 4], [2, 4, 1, 0], [2, 4, 1, 1], [2, 4, 1, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_129_35_15 : ColCertDiv where
  rK := ⟨129, by decide⟩
  rH := ⟨35, by decide⟩
  m := 5
  T1 := T129_35
  T2 := Q2.T129_35_2
  h1 := (3,1,2,2,3)
  h2 := (3,1,2,2,0)
  D1 := [[3, 1, 1, 2], [3, 1, 1, 1], [3, 1, 1, 0], [3, 1, 1, 4], [3, 1, 1, 3]]
  D2 := [[3, 1, 1, 4], [3, 1, 1, 3], [3, 1, 1, 2], [3, 1, 1, 1], [3, 1, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_129_35_20 : ColCertDiv where
  rK := ⟨129, by decide⟩
  rH := ⟨35, by decide⟩
  m := 5
  T1 := T129_35
  T2 := Q2.T129_35_2
  h1 := (4,3,1,0,4)
  h2 := (4,3,1,0,3)
  D1 := [[4, 3, 4, 0], [4, 3, 4, 2], [4, 3, 4, 4], [4, 3, 4, 1], [4, 3, 4, 3]]
  D2 := [[4, 3, 4, 4], [4, 3, 4, 1], [4, 3, 4, 3], [4, 3, 4, 0], [4, 3, 4, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_129_42_5 : ColCertDiv where
  rK := ⟨129, by decide⟩
  rH := ⟨42, by decide⟩
  m := 5
  T1 := T129_42
  T2 := Q2.T129_42_2
  h1 := (1,1,3,4,4)
  h2 := (1,1,3,4,2)
  D1 := [[1, 1, 2, 1], [1, 1, 2, 0], [1, 1, 2, 4], [1, 1, 2, 3], [1, 1, 2, 2]]
  D2 := [[1, 1, 2, 4], [1, 1, 2, 3], [1, 1, 2, 2], [1, 1, 2, 1], [1, 1, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_129_42_10 : ColCertDiv where
  rK := ⟨129, by decide⟩
  rH := ⟨42, by decide⟩
  m := 5
  T1 := T129_42
  T2 := Q2.T129_42_2
  h1 := (2,2,1,4,0)
  h2 := (2,2,1,4,1)
  D1 := [[2, 2, 3, 3], [2, 2, 3, 1], [2, 2, 3, 4], [2, 2, 3, 2], [2, 2, 3, 0]]
  D2 := [[2, 2, 3, 4], [2, 2, 3, 2], [2, 2, 3, 0], [2, 2, 3, 3], [2, 2, 3, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_129_42_15 : ColCertDiv where
  rK := ⟨129, by decide⟩
  rH := ⟨42, by decide⟩
  m := 5
  T1 := T129_42
  T2 := Q2.T129_42_2
  h1 := (3,3,4,0,4)
  h2 := (3,3,4,0,3)
  D1 := [[3, 3, 3, 2], [3, 3, 3, 4], [3, 3, 3, 1], [3, 3, 3, 3], [3, 3, 3, 0]]
  D2 := [[3, 3, 3, 1], [3, 3, 3, 3], [3, 3, 3, 0], [3, 3, 3, 2], [3, 3, 3, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_129_42_20 : ColCertDiv where
  rK := ⟨129, by decide⟩
  rH := ⟨42, by decide⟩
  m := 5
  T1 := T129_42
  T2 := Q2.T129_42_2
  h1 := (4,4,2,2,2)
  h2 := (4,4,2,2,4)
  D1 := [[4, 4, 2, 4], [4, 4, 2, 0], [4, 4, 2, 1], [4, 4, 2, 2], [4, 4, 2, 3]]
  D2 := [[4, 4, 2, 1], [4, 4, 2, 2], [4, 4, 2, 3], [4, 4, 2, 4], [4, 4, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_129_43_5 : ColCertDiv where
  rK := ⟨129, by decide⟩
  rH := ⟨43, by decide⟩
  m := 5
  T1 := T129_43
  T2 := Q2.T129_43_2
  h1 := (0,1,1,4,4)
  h2 := (0,1,1,4,2)
  D1 := [[0, 1, 4, 1], [0, 1, 4, 0], [0, 1, 4, 4], [0, 1, 4, 3], [0, 1, 4, 2]]
  D2 := [[0, 1, 4, 4], [0, 1, 4, 3], [0, 1, 4, 2], [0, 1, 4, 1], [0, 1, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_129_43_10 : ColCertDiv where
  rK := ⟨129, by decide⟩
  rH := ⟨43, by decide⟩
  m := 5
  T1 := T129_43
  T2 := Q2.T129_43_2
  h1 := (0,2,2,3,4)
  h2 := (0,2,2,3,0)
  D1 := [[0, 2, 3, 2], [0, 2, 3, 0], [0, 2, 3, 3], [0, 2, 3, 1], [0, 2, 3, 4]]
  D2 := [[0, 2, 3, 3], [0, 2, 3, 1], [0, 2, 3, 4], [0, 2, 3, 2], [0, 2, 3, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_129_43_15 : ColCertDiv where
  rK := ⟨129, by decide⟩
  rH := ⟨43, by decide⟩
  m := 5
  T1 := T129_43
  T2 := Q2.T129_43_2
  h1 := (0,3,3,2,0)
  h2 := (0,3,3,2,4)
  D1 := [[0, 3, 2, 3], [0, 3, 2, 0], [0, 3, 2, 2], [0, 3, 2, 4], [0, 3, 2, 1]]
  D2 := [[0, 3, 2, 2], [0, 3, 2, 4], [0, 3, 2, 1], [0, 3, 2, 3], [0, 3, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_129_43_20 : ColCertDiv where
  rK := ⟨129, by decide⟩
  rH := ⟨43, by decide⟩
  m := 5
  T1 := T129_43
  T2 := Q2.T129_43_2
  h1 := (0,4,4,1,2)
  h2 := (0,4,4,1,4)
  D1 := [[0, 4, 1, 4], [0, 4, 1, 0], [0, 4, 1, 1], [0, 4, 1, 2], [0, 4, 1, 3]]
  D2 := [[0, 4, 1, 1], [0, 4, 1, 2], [0, 4, 1, 3], [0, 4, 1, 4], [0, 4, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_129_51_5 : ColCertDiv where
  rK := ⟨129, by decide⟩
  rH := ⟨51, by decide⟩
  m := 5
  T1 := T129_51
  T2 := Q2.T129_51_2
  h1 := (1,3,0,0,3)
  h2 := (1,3,0,0,4)
  D1 := [[1, 3, 1, 2], [1, 3, 1, 4], [1, 3, 1, 1], [1, 3, 1, 3], [1, 3, 1, 0]]
  D2 := [[1, 3, 1, 3], [1, 3, 1, 0], [1, 3, 1, 2], [1, 3, 1, 4], [1, 3, 1, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_129_51_10 : ColCertDiv where
  rK := ⟨129, by decide⟩
  rH := ⟨51, by decide⟩
  m := 5
  T1 := T129_51
  T2 := Q2.T129_51_2
  h1 := (2,1,0,3,2)
  h2 := (2,1,0,3,0)
  D1 := [[2, 1, 4, 3], [2, 1, 4, 2], [2, 1, 4, 1], [2, 1, 4, 0], [2, 1, 4, 4]]
  D2 := [[2, 1, 4, 1], [2, 1, 4, 0], [2, 1, 4, 4], [2, 1, 4, 3], [2, 1, 4, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_129_51_15 : ColCertDiv where
  rK := ⟨129, by decide⟩
  rH := ⟨51, by decide⟩
  m := 5
  T1 := T129_51
  T2 := Q2.T129_51_2
  h1 := (3,4,0,4,3)
  h2 := (3,4,0,4,2)
  D1 := [[3, 4, 4, 4], [3, 4, 4, 0], [3, 4, 4, 1], [3, 4, 4, 2], [3, 4, 4, 3]]
  D2 := [[3, 4, 4, 3], [3, 4, 4, 4], [3, 4, 4, 0], [3, 4, 4, 1], [3, 4, 4, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_129_51_20 : ColCertDiv where
  rK := ⟨129, by decide⟩
  rH := ⟨51, by decide⟩
  m := 5
  T1 := T129_51
  T2 := Q2.T129_51_2
  h1 := (4,2,0,3,1)
  h2 := (4,2,0,3,2)
  D1 := [[4, 2, 1, 0], [4, 2, 1, 3], [4, 2, 1, 1], [4, 2, 1, 4], [4, 2, 1, 2]]
  D2 := [[4, 2, 1, 1], [4, 2, 1, 4], [4, 2, 1, 2], [4, 2, 1, 0], [4, 2, 1, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_129_91_10 : ColCertDiv where
  rK := ⟨129, by decide⟩
  rH := ⟨91, by decide⟩
  m := 5
  T1 := T129_91
  T2 := Q2.T129_91_2
  h1 := (2,3,2,2,2)
  h2 := (2,3,2,2,3)
  D1 := [[2, 3, 4, 2], [2, 3, 4, 4], [2, 3, 4, 1], [2, 3, 4, 3], [2, 3, 4, 0]]
  D2 := [[2, 3, 4, 3], [2, 3, 4, 0], [2, 3, 4, 2], [2, 3, 4, 4], [2, 3, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_129_91_15 : ColCertDiv where
  rK := ⟨129, by decide⟩
  rH := ⟨91, by decide⟩
  m := 5
  T1 := T129_91
  T2 := Q2.T129_91_2
  h1 := (3,2,3,4,2)
  h2 := (3,2,3,4,4)
  D1 := [[3, 2, 0, 2], [3, 2, 0, 0], [3, 2, 0, 3], [3, 2, 0, 1], [3, 2, 0, 4]]
  D2 := [[3, 2, 0, 4], [3, 2, 0, 2], [3, 2, 0, 0], [3, 2, 0, 3], [3, 2, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_129_91_20 : ColCertDiv where
  rK := ⟨129, by decide⟩
  rH := ⟨91, by decide⟩
  m := 5
  T1 := T129_91
  T2 := Q2.T129_91_2
  h1 := (4,1,4,0,3)
  h2 := (4,1,4,0,1)
  D1 := [[4, 1, 2, 3], [4, 1, 2, 2], [4, 1, 2, 1], [4, 1, 2, 0], [4, 1, 2, 4]]
  D2 := [[4, 1, 2, 1], [4, 1, 2, 0], [4, 1, 2, 4], [4, 1, 2, 3], [4, 1, 2, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_129_97_15 : ColCertDiv where
  rK := ⟨129, by decide⟩
  rH := ⟨97, by decide⟩
  m := 5
  T1 := T129_97
  T2 := Q2.T129_97_2
  h1 := (3,1,2,0,1)
  h2 := (3,1,2,0,2)
  D1 := [[3, 1, 4, 1], [3, 1, 4, 0], [3, 1, 4, 4], [3, 1, 4, 3], [3, 1, 4, 2]]
  D2 := [[3, 1, 4, 2], [3, 1, 4, 1], [3, 1, 4, 0], [3, 1, 4, 4], [3, 1, 4, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_129_97_20 : ColCertDiv where
  rK := ⟨129, by decide⟩
  rH := ⟨97, by decide⟩
  m := 5
  T1 := T129_97
  T2 := Q2.T129_97_2
  h1 := (4,3,1,4,0)
  h2 := (4,3,1,4,1)
  D1 := [[4, 3, 3, 0], [4, 3, 3, 2], [4, 3, 3, 4], [4, 3, 3, 1], [4, 3, 3, 3]]
  D2 := [[4, 3, 3, 1], [4, 3, 3, 3], [4, 3, 3, 0], [4, 3, 3, 2], [4, 3, 3, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_129_113_10 : ColCertDiv where
  rK := ⟨129, by decide⟩
  rH := ⟨113, by decide⟩
  m := 5
  T1 := T129_113
  T2 := Q2.T129_113_2
  h1 := (2,1,0,0,1)
  h2 := (2,1,0,0,2)
  D1 := [[2, 1, 1, 3], [2, 1, 1, 2], [2, 1, 1, 1], [2, 1, 1, 0], [2, 1, 1, 4]]
  D2 := [[2, 1, 1, 4], [2, 1, 1, 3], [2, 1, 1, 2], [2, 1, 1, 1], [2, 1, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_129_113_15 : ColCertDiv where
  rK := ⟨129, by decide⟩
  rH := ⟨113, by decide⟩
  m := 5
  T1 := T129_113
  T2 := Q2.T129_113_2
  h1 := (3,4,0,2,3)
  h2 := (3,4,0,2,4)
  D1 := [[3, 4, 2, 0], [3, 4, 2, 1], [3, 4, 2, 2], [3, 4, 2, 3], [3, 4, 2, 4]]
  D2 := [[3, 4, 2, 1], [3, 4, 2, 2], [3, 4, 2, 3], [3, 4, 2, 4], [3, 4, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_129_113_20 : ColCertDiv where
  rK := ⟨129, by decide⟩
  rH := ⟨113, by decide⟩
  m := 5
  T1 := T129_113
  T2 := Q2.T129_113_2
  h1 := (4,2,0,2,3)
  h2 := (4,2,0,2,0)
  D1 := [[4, 2, 0, 1], [4, 2, 0, 4], [4, 2, 0, 2], [4, 2, 0, 0], [4, 2, 0, 3]]
  D2 := [[4, 2, 0, 3], [4, 2, 0, 1], [4, 2, 0, 4], [4, 2, 0, 2], [4, 2, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_130_3_1 : ColCertDiv where
  rK := ⟨130, by decide⟩
  rH := ⟨3, by decide⟩
  m := 5
  T1 := T130_3
  T2 := Q2.T130_3_2
  h1 := (1,0,2,3,1)
  h2 := (1,0,2,3,1)
  D1 := [[1, 0, 3, 2], [1, 0, 3, 2], [1, 0, 3, 2], [1, 0, 3, 2], [1, 0, 3, 2]]
  D2 := [[1, 0, 3, 3], [1, 0, 3, 3], [1, 0, 3, 3], [1, 0, 3, 3], [1, 0, 3, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_130_3_2 : ColCertDiv where
  rK := ⟨130, by decide⟩
  rH := ⟨3, by decide⟩
  m := 5
  T1 := T130_3
  T2 := Q2.T130_3_2
  h1 := (2,0,4,1,0)
  h2 := (2,0,4,1,0)
  D1 := [[2, 0, 1, 1], [2, 0, 1, 1], [2, 0, 1, 1], [2, 0, 1, 1], [2, 0, 1, 1]]
  D2 := [[2, 0, 1, 3], [2, 0, 1, 3], [2, 0, 1, 3], [2, 0, 1, 3], [2, 0, 1, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_130_3_3 : ColCertDiv where
  rK := ⟨130, by decide⟩
  rH := ⟨3, by decide⟩
  m := 5
  T1 := T130_3
  T2 := Q2.T130_3_2
  h1 := (3,0,1,4,2)
  h2 := (3,0,1,4,2)
  D1 := [[3, 0, 4, 2], [3, 0, 4, 2], [3, 0, 4, 2], [3, 0, 4, 2], [3, 0, 4, 2]]
  D2 := [[3, 0, 4, 0], [3, 0, 4, 0], [3, 0, 4, 0], [3, 0, 4, 0], [3, 0, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_130_3_4 : ColCertDiv where
  rK := ⟨130, by decide⟩
  rH := ⟨3, by decide⟩
  m := 5
  T1 := T130_3
  T2 := Q2.T130_3_2
  h1 := (4,0,3,2,2)
  h2 := (4,0,3,2,2)
  D1 := [[4, 0, 2, 0], [4, 0, 2, 0], [4, 0, 2, 0], [4, 0, 2, 0], [4, 0, 2, 0]]
  D2 := [[4, 0, 2, 4], [4, 0, 2, 4], [4, 0, 2, 4], [4, 0, 2, 4], [4, 0, 2, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_130_21_5 : ColCertDiv where
  rK := ⟨130, by decide⟩
  rH := ⟨21, by decide⟩
  m := 5
  T1 := T130_21
  T2 := Q2.T130_21_2
  h1 := (1,0,2,3,2)
  h2 := (1,0,2,3,2)
  D1 := [[1, 0, 3, 3], [1, 0, 3, 3], [1, 0, 3, 3], [1, 0, 3, 3], [1, 0, 3, 3]]
  D2 := [[1, 0, 3, 4], [1, 0, 3, 4], [1, 0, 3, 4], [1, 0, 3, 4], [1, 0, 3, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_130_21_10 : ColCertDiv where
  rK := ⟨130, by decide⟩
  rH := ⟨21, by decide⟩
  m := 5
  T1 := T130_21
  T2 := Q2.T130_21_2
  h1 := (2,0,4,1,2)
  h2 := (2,0,4,1,2)
  D1 := [[2, 0, 1, 3], [2, 0, 1, 3], [2, 0, 1, 3], [2, 0, 1, 3], [2, 0, 1, 3]]
  D2 := [[2, 0, 1, 0], [2, 0, 1, 0], [2, 0, 1, 0], [2, 0, 1, 0], [2, 0, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_130_21_15 : ColCertDiv where
  rK := ⟨130, by decide⟩
  rH := ⟨21, by decide⟩
  m := 5
  T1 := T130_21
  T2 := Q2.T130_21_2
  h1 := (3,0,1,4,0)
  h2 := (3,0,1,4,0)
  D1 := [[3, 0, 4, 0], [3, 0, 4, 0], [3, 0, 4, 0], [3, 0, 4, 0], [3, 0, 4, 0]]
  D2 := [[3, 0, 4, 3], [3, 0, 4, 3], [3, 0, 4, 3], [3, 0, 4, 3], [3, 0, 4, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_130_21_20 : ColCertDiv where
  rK := ⟨130, by decide⟩
  rH := ⟨21, by decide⟩
  m := 5
  T1 := T130_21
  T2 := Q2.T130_21_2
  h1 := (4,0,3,2,1)
  h2 := (4,0,3,2,1)
  D1 := [[4, 0, 2, 4], [4, 0, 2, 4], [4, 0, 2, 4], [4, 0, 2, 4], [4, 0, 2, 4]]
  D2 := [[4, 0, 2, 3], [4, 0, 2, 3], [4, 0, 2, 3], [4, 0, 2, 3], [4, 0, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_130_30_5 : ColCertDiv where
  rK := ⟨130, by decide⟩
  rH := ⟨30, by decide⟩
  m := 5
  T1 := T130_30
  T2 := Q2.T130_30_2
  h1 := (1,2,3,2,3)
  h2 := (1,2,3,2,0)
  D1 := [[1, 2, 0, 0], [1, 2, 0, 3], [1, 2, 0, 1], [1, 2, 0, 4], [1, 2, 0, 2]]
  D2 := [[1, 2, 0, 1], [1, 2, 0, 4], [1, 2, 0, 2], [1, 2, 0, 0], [1, 2, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_130_30_10 : ColCertDiv where
  rK := ⟨130, by decide⟩
  rH := ⟨30, by decide⟩
  m := 5
  T1 := T130_30
  T2 := Q2.T130_30_2
  h1 := (2,4,1,1,4)
  h2 := (2,4,1,1,3)
  D1 := [[2, 4, 3, 1], [2, 4, 3, 2], [2, 4, 3, 3], [2, 4, 3, 4], [2, 4, 3, 0]]
  D2 := [[2, 4, 3, 3], [2, 4, 3, 4], [2, 4, 3, 0], [2, 4, 3, 1], [2, 4, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_130_30_15 : ColCertDiv where
  rK := ⟨130, by decide⟩
  rH := ⟨30, by decide⟩
  m := 5
  T1 := T130_30
  T2 := Q2.T130_30_2
  h1 := (3,1,4,2,1)
  h2 := (3,1,4,2,3)
  D1 := [[3, 1, 4, 1], [3, 1, 4, 0], [3, 1, 4, 4], [3, 1, 4, 3], [3, 1, 4, 2]]
  D2 := [[3, 1, 4, 0], [3, 1, 4, 4], [3, 1, 4, 3], [3, 1, 4, 2], [3, 1, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_130_36_5 : ColCertDiv where
  rK := ⟨130, by decide⟩
  rH := ⟨36, by decide⟩
  m := 5
  T1 := T130_36
  T2 := Q2.T130_36_2
  h1 := (1,3,1,0,1)
  h2 := (1,3,1,0,2)
  D1 := [[1, 3, 2, 3], [1, 3, 2, 0], [1, 3, 2, 2], [1, 3, 2, 4], [1, 3, 2, 1]]
  D2 := [[1, 3, 2, 2], [1, 3, 2, 4], [1, 3, 2, 1], [1, 3, 2, 3], [1, 3, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_130_36_10 : ColCertDiv where
  rK := ⟨130, by decide⟩
  rH := ⟨36, by decide⟩
  m := 5
  T1 := T130_36
  T2 := Q2.T130_36_2
  h1 := (2,1,2,3,1)
  h2 := (2,1,2,3,4)
  D1 := [[2, 1, 1, 4], [2, 1, 1, 3], [2, 1, 1, 2], [2, 1, 1, 1], [2, 1, 1, 0]]
  D2 := [[2, 1, 1, 3], [2, 1, 1, 2], [2, 1, 1, 1], [2, 1, 1, 0], [2, 1, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_130_36_15 : ColCertDiv where
  rK := ⟨130, by decide⟩
  rH := ⟨36, by decide⟩
  m := 5
  T1 := T130_36
  T2 := Q2.T130_36_2
  h1 := (3,4,3,4,1)
  h2 := (3,4,3,4,0)
  D1 := [[3, 4, 2, 4], [3, 4, 2, 0], [3, 4, 2, 1], [3, 4, 2, 2], [3, 4, 2, 3]]
  D2 := [[3, 4, 2, 2], [3, 4, 2, 3], [3, 4, 2, 4], [3, 4, 2, 0], [3, 4, 2, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_130_36_20 : ColCertDiv where
  rK := ⟨130, by decide⟩
  rH := ⟨36, by decide⟩
  m := 5
  T1 := T130_36
  T2 := Q2.T130_36_2
  h1 := (4,2,4,3,1)
  h2 := (4,2,4,3,2)
  D1 := [[4, 2, 0, 3], [4, 2, 0, 1], [4, 2, 0, 4], [4, 2, 0, 2], [4, 2, 0, 0]]
  D2 := [[4, 2, 0, 1], [4, 2, 0, 4], [4, 2, 0, 2], [4, 2, 0, 0], [4, 2, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_130_38_5 : ColCertDiv where
  rK := ⟨130, by decide⟩
  rH := ⟨38, by decide⟩
  m := 5
  T1 := T130_38
  T2 := Q2.T130_38_2
  h1 := (0,1,3,4,1)
  h2 := (0,1,3,4,4)
  D1 := [[0, 1, 4, 4], [0, 1, 4, 3], [0, 1, 4, 2], [0, 1, 4, 1], [0, 1, 4, 0]]
  D2 := [[0, 1, 4, 1], [0, 1, 4, 0], [0, 1, 4, 4], [0, 1, 4, 3], [0, 1, 4, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_130_38_10 : ColCertDiv where
  rK := ⟨130, by decide⟩
  rH := ⟨38, by decide⟩
  m := 5
  T1 := T130_38
  T2 := Q2.T130_38_2
  h1 := (0,2,1,3,0)
  h2 := (0,2,1,3,1)
  D1 := [[0, 2, 3, 3], [0, 2, 3, 1], [0, 2, 3, 4], [0, 2, 3, 2], [0, 2, 3, 0]]
  D2 := [[0, 2, 3, 2], [0, 2, 3, 0], [0, 2, 3, 3], [0, 2, 3, 1], [0, 2, 3, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_130_38_15 : ColCertDiv where
  rK := ⟨130, by decide⟩
  rH := ⟨38, by decide⟩
  m := 5
  T1 := T130_38
  T2 := Q2.T130_38_2
  h1 := (0,3,4,2,2)
  h2 := (0,3,4,2,1)
  D1 := [[0, 3, 2, 2], [0, 3, 2, 4], [0, 3, 2, 1], [0, 3, 2, 3], [0, 3, 2, 0]]
  D2 := [[0, 3, 2, 3], [0, 3, 2, 0], [0, 3, 2, 2], [0, 3, 2, 4], [0, 3, 2, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_130_38_20 : ColCertDiv where
  rK := ⟨130, by decide⟩
  rH := ⟨38, by decide⟩
  m := 5
  T1 := T130_38
  T2 := Q2.T130_38_2
  h1 := (0,4,2,1,2)
  h2 := (0,4,2,1,4)
  D1 := [[0, 4, 1, 1], [0, 4, 1, 2], [0, 4, 1, 3], [0, 4, 1, 4], [0, 4, 1, 0]]
  D2 := [[0, 4, 1, 4], [0, 4, 1, 0], [0, 4, 1, 1], [0, 4, 1, 2], [0, 4, 1, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_130_44_5 : ColCertDiv where
  rK := ⟨130, by decide⟩
  rH := ⟨44, by decide⟩
  m := 5
  T1 := T130_44
  T2 := Q2.T130_44_2
  h1 := (1,4,4,3,0)
  h2 := (1,4,4,3,0)
  D1 := [[1, 4, 4, 4], [1, 4, 4, 0], [1, 4, 4, 1], [1, 4, 4, 2], [1, 4, 4, 3]]
  D2 := [[1, 4, 4, 1], [1, 4, 4, 2], [1, 4, 4, 3], [1, 4, 4, 4], [1, 4, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_130_44_15 : ColCertDiv where
  rK := ⟨130, by decide⟩
  rH := ⟨44, by decide⟩
  m := 5
  T1 := T130_44
  T2 := Q2.T130_44_2
  h1 := (3,2,2,1,3)
  h2 := (3,2,2,1,0)
  D1 := [[3, 2, 0, 2], [3, 2, 0, 0], [3, 2, 0, 3], [3, 2, 0, 1], [3, 2, 0, 4]]
  D2 := [[3, 2, 0, 0], [3, 2, 0, 3], [3, 2, 0, 1], [3, 2, 0, 4], [3, 2, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_130_44_20 : ColCertDiv where
  rK := ⟨130, by decide⟩
  rH := ⟨44, by decide⟩
  m := 5
  T1 := T130_44
  T2 := Q2.T130_44_2
  h1 := (4,1,1,1,3)
  h2 := (4,1,1,1,1)
  D1 := [[4, 1, 2, 3], [4, 1, 2, 2], [4, 1, 2, 1], [4, 1, 2, 0], [4, 1, 2, 4]]
  D2 := [[4, 1, 2, 4], [4, 1, 2, 3], [4, 1, 2, 2], [4, 1, 2, 1], [4, 1, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_130_52_5 : ColCertDiv where
  rK := ⟨130, by decide⟩
  rH := ⟨52, by decide⟩
  m := 5
  T1 := T130_52
  T2 := Q2.T130_52_2
  h1 := (1,1,0,4,1)
  h2 := (1,1,0,4,4)
  D1 := [[1, 1, 3, 0], [1, 1, 3, 4], [1, 1, 3, 3], [1, 1, 3, 2], [1, 1, 3, 1]]
  D2 := [[1, 1, 3, 3], [1, 1, 3, 2], [1, 1, 3, 1], [1, 1, 3, 0], [1, 1, 3, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_130_52_10 : ColCertDiv where
  rK := ⟨130, by decide⟩
  rH := ⟨52, by decide⟩
  m := 5
  T1 := T130_52
  T2 := Q2.T130_52_2
  h1 := (2,2,0,4,1)
  h2 := (2,2,0,4,2)
  D1 := [[2, 2, 0, 0], [2, 2, 0, 3], [2, 2, 0, 1], [2, 2, 0, 4], [2, 2, 0, 2]]
  D2 := [[2, 2, 0, 1], [2, 2, 0, 4], [2, 2, 0, 2], [2, 2, 0, 0], [2, 2, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_130_52_15 : ColCertDiv where
  rK := ⟨130, by decide⟩
  rH := ⟨52, by decide⟩
  m := 5
  T1 := T130_52
  T2 := Q2.T130_52_2
  h1 := (3,3,0,0,1)
  h2 := (3,3,0,0,0)
  D1 := [[3, 3, 1, 1], [3, 3, 1, 3], [3, 3, 1, 0], [3, 3, 1, 2], [3, 3, 1, 4]]
  D2 := [[3, 3, 1, 0], [3, 3, 1, 2], [3, 3, 1, 4], [3, 3, 1, 1], [3, 3, 1, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_130_52_20 : ColCertDiv where
  rK := ⟨130, by decide⟩
  rH := ⟨52, by decide⟩
  m := 5
  T1 := T130_52
  T2 := Q2.T130_52_2
  h1 := (4,4,0,2,2)
  h2 := (4,4,0,2,4)
  D1 := [[4, 4, 1, 4], [4, 4, 1, 0], [4, 4, 1, 1], [4, 4, 1, 2], [4, 4, 1, 3]]
  D2 := [[4, 4, 1, 1], [4, 4, 1, 2], [4, 4, 1, 3], [4, 4, 1, 4], [4, 4, 1, 0]]
  bind1 := by decide
  bind2 := by decide

end LeanDring.P5Presentation
