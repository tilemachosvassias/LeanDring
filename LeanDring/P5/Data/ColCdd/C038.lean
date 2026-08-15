/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.Twin1.ColCert
import LeanDring.P5.Data.EntryK.C014
import LeanDring.P5.Data.EntryK.C015
import LeanDring.P5.Data.EntryK.C016

/-!
# Species-table cell data, stage 2 — column-data-divergent columns

Per-column certified exponent-vector data (`ColCert`/`ColCertDiv`) with kernel
`decide` bindings. Emitted; the embedded lists are what the kernel certifies.
cdd tier, chunk 37: 60 columns.
-/

-- machine-emitted data: silence style linters (generated long lines, file-level options)
set_option linter.style.longLine false

namespace LeanDring.P5Presentation

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

def colCertDiv_58_33_15 : ColCertDiv where
  rK := ⟨58, by decide⟩
  rH := ⟨33, by decide⟩
  m := 5
  T1 := T58_33
  T2 := Q2.T58_33_2
  h1 := (0,3,1,2,1)
  h2 := (0,3,1,2,0)
  D1 := [[3, 1, 3], [3, 1, 3], [3, 1, 3], [3, 1, 3], [3, 1, 3]]
  D2 := [[3, 1, 4], [3, 1, 4], [3, 1, 4], [3, 1, 4], [3, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_58_33_20 : ColCertDiv where
  rK := ⟨58, by decide⟩
  rH := ⟨33, by decide⟩
  m := 5
  T1 := T58_33
  T2 := Q2.T58_33_2
  h1 := (0,4,3,1,2)
  h2 := (0,4,3,1,4)
  D1 := [[4, 3, 0], [4, 3, 0], [4, 3, 0], [4, 3, 0], [4, 3, 0]]
  D2 := [[4, 3, 3], [4, 3, 3], [4, 3, 3], [4, 3, 3], [4, 3, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_58_38_5 : ColCertDiv where
  rK := ⟨58, by decide⟩
  rH := ⟨38, by decide⟩
  m := 5
  T1 := T58_38
  T2 := Q2.T58_38_2
  h1 := (0,1,3,4,1)
  h2 := (0,1,3,4,4)
  D1 := [[1, 3, 0], [1, 3, 0], [1, 3, 0], [1, 3, 0], [1, 3, 0]]
  D2 := [[1, 3, 2], [1, 3, 2], [1, 3, 2], [1, 3, 2], [1, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_58_38_10 : ColCertDiv where
  rK := ⟨58, by decide⟩
  rH := ⟨38, by decide⟩
  m := 5
  T1 := T58_38
  T2 := Q2.T58_38_2
  h1 := (0,2,1,3,0)
  h2 := (0,2,1,3,1)
  D1 := [[2, 1, 2], [2, 1, 2], [2, 1, 2], [2, 1, 2], [2, 1, 2]]
  D2 := [[2, 1, 1], [2, 1, 1], [2, 1, 1], [2, 1, 1], [2, 1, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_58_38_15 : ColCertDiv where
  rK := ⟨58, by decide⟩
  rH := ⟨38, by decide⟩
  m := 5
  T1 := T58_38
  T2 := Q2.T58_38_2
  h1 := (0,3,4,2,2)
  h2 := (0,3,4,2,1)
  D1 := [[3, 4, 1], [3, 4, 1], [3, 4, 1], [3, 4, 1], [3, 4, 1]]
  D2 := [[3, 4, 2], [3, 4, 2], [3, 4, 2], [3, 4, 2], [3, 4, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_58_38_20 : ColCertDiv where
  rK := ⟨58, by decide⟩
  rH := ⟨38, by decide⟩
  m := 5
  T1 := T58_38
  T2 := Q2.T58_38_2
  h1 := (0,4,2,1,2)
  h2 := (0,4,2,1,4)
  D1 := [[4, 2, 2], [4, 2, 2], [4, 2, 2], [4, 2, 2], [4, 2, 2]]
  D2 := [[4, 2, 0], [4, 2, 0], [4, 2, 0], [4, 2, 0], [4, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_58_43_5 : ColCertDiv where
  rK := ⟨58, by decide⟩
  rH := ⟨43, by decide⟩
  m := 5
  T1 := T58_43
  T2 := Q2.T58_43_2
  h1 := (0,1,1,4,4)
  h2 := (0,1,1,4,2)
  D1 := [[1, 1, 0], [1, 1, 0], [1, 1, 0], [1, 1, 0], [1, 1, 0]]
  D2 := [[1, 1, 2], [1, 1, 2], [1, 1, 2], [1, 1, 2], [1, 1, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_58_43_10 : ColCertDiv where
  rK := ⟨58, by decide⟩
  rH := ⟨43, by decide⟩
  m := 5
  T1 := T58_43
  T2 := Q2.T58_43_2
  h1 := (0,2,2,3,4)
  h2 := (0,2,2,3,0)
  D1 := [[2, 2, 4], [2, 2, 4], [2, 2, 4], [2, 2, 4], [2, 2, 4]]
  D2 := [[2, 2, 3], [2, 2, 3], [2, 2, 3], [2, 2, 3], [2, 2, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_58_43_15 : ColCertDiv where
  rK := ⟨58, by decide⟩
  rH := ⟨43, by decide⟩
  m := 5
  T1 := T58_43
  T2 := Q2.T58_43_2
  h1 := (0,3,3,2,0)
  h2 := (0,3,3,2,4)
  D1 := [[3, 3, 2], [3, 3, 2], [3, 3, 2], [3, 3, 2], [3, 3, 2]]
  D2 := [[3, 3, 3], [3, 3, 3], [3, 3, 3], [3, 3, 3], [3, 3, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_58_43_20 : ColCertDiv where
  rK := ⟨58, by decide⟩
  rH := ⟨43, by decide⟩
  m := 5
  T1 := T58_43
  T2 := Q2.T58_43_2
  h1 := (0,4,4,1,2)
  h2 := (0,4,4,1,4)
  D1 := [[4, 4, 4], [4, 4, 4], [4, 4, 4], [4, 4, 4], [4, 4, 4]]
  D2 := [[4, 4, 2], [4, 4, 2], [4, 4, 2], [4, 4, 2], [4, 4, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_58_48_5 : ColCertDiv where
  rK := ⟨58, by decide⟩
  rH := ⟨48, by decide⟩
  m := 5
  T1 := T58_48
  T2 := Q2.T58_48_2
  h1 := (0,1,0,4,3)
  h2 := (0,1,0,4,1)
  D1 := [[1, 0, 1], [1, 0, 1], [1, 0, 1], [1, 0, 1], [1, 0, 1]]
  D2 := [[1, 0, 3], [1, 0, 3], [1, 0, 3], [1, 0, 3], [1, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_58_48_10 : ColCertDiv where
  rK := ⟨58, by decide⟩
  rH := ⟨48, by decide⟩
  m := 5
  T1 := T58_48
  T2 := Q2.T58_48_2
  h1 := (0,2,0,3,1)
  h2 := (0,2,0,3,2)
  D1 := [[2, 0, 2], [2, 0, 2], [2, 0, 2], [2, 0, 2], [2, 0, 2]]
  D2 := [[2, 0, 1], [2, 0, 1], [2, 0, 1], [2, 0, 1], [2, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_58_48_15 : ColCertDiv where
  rK := ⟨58, by decide⟩
  rH := ⟨48, by decide⟩
  m := 5
  T1 := T58_48
  T2 := Q2.T58_48_2
  h1 := (0,3,0,2,4)
  h2 := (0,3,0,2,3)
  D1 := [[3, 0, 3], [3, 0, 3], [3, 0, 3], [3, 0, 3], [3, 0, 3]]
  D2 := [[3, 0, 4], [3, 0, 4], [3, 0, 4], [3, 0, 4], [3, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_58_48_20 : ColCertDiv where
  rK := ⟨58, by decide⟩
  rH := ⟨48, by decide⟩
  m := 5
  T1 := T58_48
  T2 := Q2.T58_48_2
  h1 := (0,4,0,1,2)
  h2 := (0,4,0,1,4)
  D1 := [[4, 0, 4], [4, 0, 4], [4, 0, 4], [4, 0, 4], [4, 0, 4]]
  D2 := [[4, 0, 2], [4, 0, 2], [4, 0, 2], [4, 0, 2], [4, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_59_28_5 : ColCertDiv where
  rK := ⟨59, by decide⟩
  rH := ⟨28, by decide⟩
  m := 5
  T1 := T59_28
  T2 := Q2.T59_28_2
  h1 := (0,1,4,4,2)
  h2 := (0,1,4,4,0)
  D1 := [[1, 4, 0], [1, 4, 0], [1, 4, 0], [1, 4, 0], [1, 4, 0]]
  D2 := [[1, 4, 3], [1, 4, 3], [1, 4, 3], [1, 4, 3], [1, 4, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_59_28_10 : ColCertDiv where
  rK := ⟨59, by decide⟩
  rH := ⟨28, by decide⟩
  m := 5
  T1 := T59_28
  T2 := Q2.T59_28_2
  h1 := (0,2,3,3,3)
  h2 := (0,2,3,3,4)
  D1 := [[2, 3, 1], [2, 3, 1], [2, 3, 1], [2, 3, 1], [2, 3, 1]]
  D2 := [[2, 3, 2], [2, 3, 2], [2, 3, 2], [2, 3, 2], [2, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_59_28_15 : ColCertDiv where
  rK := ⟨59, by decide⟩
  rH := ⟨28, by decide⟩
  m := 5
  T1 := T59_28
  T2 := Q2.T59_28_2
  h1 := (0,3,2,2,3)
  h2 := (0,3,2,2,2)
  D1 := [[3, 2, 3], [3, 2, 3], [3, 2, 3], [3, 2, 3], [3, 2, 3]]
  D2 := [[3, 2, 2], [3, 2, 2], [3, 2, 2], [3, 2, 2], [3, 2, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_59_28_20 : ColCertDiv where
  rK := ⟨59, by decide⟩
  rH := ⟨28, by decide⟩
  m := 5
  T1 := T59_28
  T2 := Q2.T59_28_2
  h1 := (0,4,1,1,2)
  h2 := (0,4,1,1,4)
  D1 := [[4, 1, 1], [4, 1, 1], [4, 1, 1], [4, 1, 1], [4, 1, 1]]
  D2 := [[4, 1, 3], [4, 1, 3], [4, 1, 3], [4, 1, 3], [4, 1, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_59_33_5 : ColCertDiv where
  rK := ⟨59, by decide⟩
  rH := ⟨33, by decide⟩
  m := 5
  T1 := T59_33
  T2 := Q2.T59_33_2
  h1 := (0,1,2,4,0)
  h2 := (0,1,2,4,3)
  D1 := [[1, 2, 2], [1, 2, 2], [1, 2, 2], [1, 2, 2], [1, 2, 2]]
  D2 := [[1, 2, 0], [1, 2, 0], [1, 2, 0], [1, 2, 0], [1, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_59_33_10 : ColCertDiv where
  rK := ⟨59, by decide⟩
  rH := ⟨33, by decide⟩
  m := 5
  T1 := T59_33
  T2 := Q2.T59_33_2
  h1 := (0,2,4,3,2)
  h2 := (0,2,4,3,3)
  D1 := [[2, 4, 2], [2, 4, 2], [2, 4, 2], [2, 4, 2], [2, 4, 2]]
  D2 := [[2, 4, 3], [2, 4, 3], [2, 4, 3], [2, 4, 3], [2, 4, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_59_33_15 : ColCertDiv where
  rK := ⟨59, by decide⟩
  rH := ⟨33, by decide⟩
  m := 5
  T1 := T59_33
  T2 := Q2.T59_33_2
  h1 := (0,3,1,2,1)
  h2 := (0,3,1,2,0)
  D1 := [[3, 1, 0], [3, 1, 0], [3, 1, 0], [3, 1, 0], [3, 1, 0]]
  D2 := [[3, 1, 4], [3, 1, 4], [3, 1, 4], [3, 1, 4], [3, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_59_33_20 : ColCertDiv where
  rK := ⟨59, by decide⟩
  rH := ⟨33, by decide⟩
  m := 5
  T1 := T59_33
  T2 := Q2.T59_33_2
  h1 := (0,4,3,1,2)
  h2 := (0,4,3,1,4)
  D1 := [[4, 3, 1], [4, 3, 1], [4, 3, 1], [4, 3, 1], [4, 3, 1]]
  D2 := [[4, 3, 3], [4, 3, 3], [4, 3, 3], [4, 3, 3], [4, 3, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_59_38_5 : ColCertDiv where
  rK := ⟨59, by decide⟩
  rH := ⟨38, by decide⟩
  m := 5
  T1 := T59_38
  T2 := Q2.T59_38_2
  h1 := (0,1,3,4,1)
  h2 := (0,1,3,4,4)
  D1 := [[1, 3, 3], [1, 3, 3], [1, 3, 3], [1, 3, 3], [1, 3, 3]]
  D2 := [[1, 3, 1], [1, 3, 1], [1, 3, 1], [1, 3, 1], [1, 3, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_59_38_10 : ColCertDiv where
  rK := ⟨59, by decide⟩
  rH := ⟨38, by decide⟩
  m := 5
  T1 := T59_38
  T2 := Q2.T59_38_2
  h1 := (0,2,1,3,0)
  h2 := (0,2,1,3,1)
  D1 := [[2, 1, 3], [2, 1, 3], [2, 1, 3], [2, 1, 3], [2, 1, 3]]
  D2 := [[2, 1, 4], [2, 1, 4], [2, 1, 4], [2, 1, 4], [2, 1, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_59_38_15 : ColCertDiv where
  rK := ⟨59, by decide⟩
  rH := ⟨38, by decide⟩
  m := 5
  T1 := T59_38
  T2 := Q2.T59_38_2
  h1 := (0,3,4,2,2)
  h2 := (0,3,4,2,1)
  D1 := [[3, 4, 0], [3, 4, 0], [3, 4, 0], [3, 4, 0], [3, 4, 0]]
  D2 := [[3, 4, 4], [3, 4, 4], [3, 4, 4], [3, 4, 4], [3, 4, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_59_38_20 : ColCertDiv where
  rK := ⟨59, by decide⟩
  rH := ⟨38, by decide⟩
  m := 5
  T1 := T59_38
  T2 := Q2.T59_38_2
  h1 := (0,4,2,1,2)
  h2 := (0,4,2,1,4)
  D1 := [[4, 2, 4], [4, 2, 4], [4, 2, 4], [4, 2, 4], [4, 2, 4]]
  D2 := [[4, 2, 1], [4, 2, 1], [4, 2, 1], [4, 2, 1], [4, 2, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_59_43_5 : ColCertDiv where
  rK := ⟨59, by decide⟩
  rH := ⟨43, by decide⟩
  m := 5
  T1 := T59_43
  T2 := Q2.T59_43_2
  h1 := (0,1,1,4,4)
  h2 := (0,1,1,4,2)
  D1 := [[1, 1, 2], [1, 1, 2], [1, 1, 2], [1, 1, 2], [1, 1, 2]]
  D2 := [[1, 1, 0], [1, 1, 0], [1, 1, 0], [1, 1, 0], [1, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_59_43_10 : ColCertDiv where
  rK := ⟨59, by decide⟩
  rH := ⟨43, by decide⟩
  m := 5
  T1 := T59_43
  T2 := Q2.T59_43_2
  h1 := (0,2,2,3,4)
  h2 := (0,2,2,3,0)
  D1 := [[2, 2, 3], [2, 2, 3], [2, 2, 3], [2, 2, 3], [2, 2, 3]]
  D2 := [[2, 2, 4], [2, 2, 4], [2, 2, 4], [2, 2, 4], [2, 2, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_59_43_15 : ColCertDiv where
  rK := ⟨59, by decide⟩
  rH := ⟨43, by decide⟩
  m := 5
  T1 := T59_43
  T2 := Q2.T59_43_2
  h1 := (0,3,3,2,0)
  h2 := (0,3,3,2,4)
  D1 := [[3, 3, 3], [3, 3, 3], [3, 3, 3], [3, 3, 3], [3, 3, 3]]
  D2 := [[3, 3, 2], [3, 3, 2], [3, 3, 2], [3, 3, 2], [3, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_59_43_20 : ColCertDiv where
  rK := ⟨59, by decide⟩
  rH := ⟨43, by decide⟩
  m := 5
  T1 := T59_43
  T2 := Q2.T59_43_2
  h1 := (0,4,4,1,2)
  h2 := (0,4,4,1,4)
  D1 := [[4, 4, 2], [4, 4, 2], [4, 4, 2], [4, 4, 2], [4, 4, 2]]
  D2 := [[4, 4, 4], [4, 4, 4], [4, 4, 4], [4, 4, 4], [4, 4, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_59_48_5 : ColCertDiv where
  rK := ⟨59, by decide⟩
  rH := ⟨48, by decide⟩
  m := 5
  T1 := T59_48
  T2 := Q2.T59_48_2
  h1 := (0,1,0,4,3)
  h2 := (0,1,0,4,1)
  D1 := [[1, 0, 3], [1, 0, 3], [1, 0, 3], [1, 0, 3], [1, 0, 3]]
  D2 := [[1, 0, 1], [1, 0, 1], [1, 0, 1], [1, 0, 1], [1, 0, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_59_48_10 : ColCertDiv where
  rK := ⟨59, by decide⟩
  rH := ⟨48, by decide⟩
  m := 5
  T1 := T59_48
  T2 := Q2.T59_48_2
  h1 := (0,2,0,3,1)
  h2 := (0,2,0,3,2)
  D1 := [[2, 0, 1], [2, 0, 1], [2, 0, 1], [2, 0, 1], [2, 0, 1]]
  D2 := [[2, 0, 2], [2, 0, 2], [2, 0, 2], [2, 0, 2], [2, 0, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_59_48_15 : ColCertDiv where
  rK := ⟨59, by decide⟩
  rH := ⟨48, by decide⟩
  m := 5
  T1 := T59_48
  T2 := Q2.T59_48_2
  h1 := (0,3,0,2,4)
  h2 := (0,3,0,2,3)
  D1 := [[3, 0, 4], [3, 0, 4], [3, 0, 4], [3, 0, 4], [3, 0, 4]]
  D2 := [[3, 0, 3], [3, 0, 3], [3, 0, 3], [3, 0, 3], [3, 0, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_59_48_20 : ColCertDiv where
  rK := ⟨59, by decide⟩
  rH := ⟨48, by decide⟩
  m := 5
  T1 := T59_48
  T2 := Q2.T59_48_2
  h1 := (0,4,0,1,2)
  h2 := (0,4,0,1,4)
  D1 := [[4, 0, 2], [4, 0, 2], [4, 0, 2], [4, 0, 2], [4, 0, 2]]
  D2 := [[4, 0, 4], [4, 0, 4], [4, 0, 4], [4, 0, 4], [4, 0, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_63_29_5 : ColCertDiv where
  rK := ⟨63, by decide⟩
  rH := ⟨29, by decide⟩
  m := 5
  T1 := T63_29
  T2 := Q2.T63_29_2
  h1 := (1,4,1,3,3)
  h2 := (1,4,1,3,3)
  D1 := [[1, 1, 3], [1, 1, 2], [1, 1, 1], [1, 1, 0], [1, 1, 4]]
  D2 := [[1, 1, 2], [1, 1, 1], [1, 1, 0], [1, 1, 4], [1, 1, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_63_29_10 : ColCertDiv where
  rK := ⟨63, by decide⟩
  rH := ⟨29, by decide⟩
  m := 5
  T1 := T63_29
  T2 := Q2.T63_29_2
  h1 := (2,3,2,0,4)
  h2 := (2,3,2,0,0)
  D1 := [[2, 2, 0], [2, 2, 3], [2, 2, 1], [2, 2, 4], [2, 2, 2]]
  D2 := [[2, 2, 3], [2, 2, 1], [2, 2, 4], [2, 2, 2], [2, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_63_29_15 : ColCertDiv where
  rK := ⟨63, by decide⟩
  rH := ⟨29, by decide⟩
  m := 5
  T1 := T63_29
  T2 := Q2.T63_29_2
  h1 := (3,2,3,1,1)
  h2 := (3,2,3,1,3)
  D1 := [[3, 3, 1], [3, 3, 3], [3, 3, 0], [3, 3, 2], [3, 3, 4]]
  D2 := [[3, 3, 3], [3, 3, 0], [3, 3, 2], [3, 3, 4], [3, 3, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_63_29_20 : ColCertDiv where
  rK := ⟨63, by decide⟩
  rH := ⟨29, by decide⟩
  m := 5
  T1 := T63_29
  T2 := Q2.T63_29_2
  h1 := (4,1,4,1,3)
  h2 := (4,1,4,1,1)
  D1 := [[4, 4, 1], [4, 4, 2], [4, 4, 3], [4, 4, 4], [4, 4, 0]]
  D2 := [[4, 4, 2], [4, 4, 3], [4, 4, 4], [4, 4, 0], [4, 4, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_63_34_5 : ColCertDiv where
  rK := ⟨63, by decide⟩
  rH := ⟨34, by decide⟩
  m := 5
  T1 := T63_34
  T2 := Q2.T63_34_2
  h1 := (1,4,3,3,1)
  h2 := (1,4,3,3,1)
  D1 := [[1, 3, 2], [1, 3, 1], [1, 3, 0], [1, 3, 4], [1, 3, 3]]
  D2 := [[1, 3, 1], [1, 3, 0], [1, 3, 4], [1, 3, 3], [1, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_63_34_10 : ColCertDiv where
  rK := ⟨63, by decide⟩
  rH := ⟨34, by decide⟩
  m := 5
  T1 := T63_34
  T2 := Q2.T63_34_2
  h1 := (2,3,1,0,3)
  h2 := (2,3,1,0,4)
  D1 := [[2, 1, 1], [2, 1, 4], [2, 1, 2], [2, 1, 0], [2, 1, 3]]
  D2 := [[2, 1, 4], [2, 1, 2], [2, 1, 0], [2, 1, 3], [2, 1, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_63_34_15 : ColCertDiv where
  rK := ⟨63, by decide⟩
  rH := ⟨34, by decide⟩
  m := 5
  T1 := T63_34
  T2 := Q2.T63_34_2
  h1 := (3,2,4,1,4)
  h2 := (3,2,4,1,1)
  D1 := [[3, 4, 2], [3, 4, 4], [3, 4, 1], [3, 4, 3], [3, 4, 0]]
  D2 := [[3, 4, 4], [3, 4, 1], [3, 4, 3], [3, 4, 0], [3, 4, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_63_34_20 : ColCertDiv where
  rK := ⟨63, by decide⟩
  rH := ⟨34, by decide⟩
  m := 5
  T1 := T63_34
  T2 := Q2.T63_34_2
  h1 := (4,1,2,1,3)
  h2 := (4,1,2,1,1)
  D1 := [[4, 2, 0], [4, 2, 1], [4, 2, 2], [4, 2, 3], [4, 2, 4]]
  D2 := [[4, 2, 1], [4, 2, 2], [4, 2, 3], [4, 2, 4], [4, 2, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_63_39_5 : ColCertDiv where
  rK := ⟨63, by decide⟩
  rH := ⟨39, by decide⟩
  m := 5
  T1 := T63_39
  T2 := Q2.T63_39_2
  h1 := (1,4,2,3,2)
  h2 := (1,4,2,3,2)
  D1 := [[1, 2, 2], [1, 2, 1], [1, 2, 0], [1, 2, 4], [1, 2, 3]]
  D2 := [[1, 2, 1], [1, 2, 0], [1, 2, 4], [1, 2, 3], [1, 2, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_63_39_10 : ColCertDiv where
  rK := ⟨63, by decide⟩
  rH := ⟨39, by decide⟩
  m := 5
  T1 := T63_39
  T2 := Q2.T63_39_2
  h1 := (2,3,4,0,1)
  h2 := (2,3,4,0,2)
  D1 := [[2, 4, 2], [2, 4, 0], [2, 4, 3], [2, 4, 1], [2, 4, 4]]
  D2 := [[2, 4, 0], [2, 4, 3], [2, 4, 1], [2, 4, 4], [2, 4, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_63_39_15 : ColCertDiv where
  rK := ⟨63, by decide⟩
  rH := ⟨39, by decide⟩
  m := 5
  T1 := T63_39
  T2 := Q2.T63_39_2
  h1 := (3,2,1,1,0)
  h2 := (3,2,1,1,2)
  D1 := [[3, 1, 0], [3, 1, 2], [3, 1, 4], [3, 1, 1], [3, 1, 3]]
  D2 := [[3, 1, 2], [3, 1, 4], [3, 1, 1], [3, 1, 3], [3, 1, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_63_39_20 : ColCertDiv where
  rK := ⟨63, by decide⟩
  rH := ⟨39, by decide⟩
  m := 5
  T1 := T63_39
  T2 := Q2.T63_39_2
  h1 := (4,1,3,1,3)
  h2 := (4,1,3,1,1)
  D1 := [[4, 3, 1], [4, 3, 2], [4, 3, 3], [4, 3, 4], [4, 3, 0]]
  D2 := [[4, 3, 2], [4, 3, 3], [4, 3, 4], [4, 3, 0], [4, 3, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_63_44_5 : ColCertDiv where
  rK := ⟨63, by decide⟩
  rH := ⟨44, by decide⟩
  m := 5
  T1 := T63_44
  T2 := Q2.T63_44_2
  h1 := (1,4,4,3,0)
  h2 := (1,4,4,3,0)
  D1 := [[1, 4, 3], [1, 4, 2], [1, 4, 1], [1, 4, 0], [1, 4, 4]]
  D2 := [[1, 4, 2], [1, 4, 1], [1, 4, 0], [1, 4, 4], [1, 4, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_63_44_10 : ColCertDiv where
  rK := ⟨63, by decide⟩
  rH := ⟨44, by decide⟩
  m := 5
  T1 := T63_44
  T2 := Q2.T63_44_2
  h1 := (2,3,3,0,0)
  h2 := (2,3,3,0,1)
  D1 := [[2, 3, 2], [2, 3, 0], [2, 3, 3], [2, 3, 1], [2, 3, 4]]
  D2 := [[2, 3, 0], [2, 3, 3], [2, 3, 1], [2, 3, 4], [2, 3, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_63_44_15 : ColCertDiv where
  rK := ⟨63, by decide⟩
  rH := ⟨44, by decide⟩
  m := 5
  T1 := T63_44
  T2 := Q2.T63_44_2
  h1 := (3,2,2,1,3)
  h2 := (3,2,2,1,0)
  D1 := [[3, 2, 2], [3, 2, 4], [3, 2, 1], [3, 2, 3], [3, 2, 0]]
  D2 := [[3, 2, 4], [3, 2, 1], [3, 2, 3], [3, 2, 0], [3, 2, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_63_44_20 : ColCertDiv where
  rK := ⟨63, by decide⟩
  rH := ⟨44, by decide⟩
  m := 5
  T1 := T63_44
  T2 := Q2.T63_44_2
  h1 := (4,1,1,1,3)
  h2 := (4,1,1,1,1)
  D1 := [[4, 1, 3], [4, 1, 4], [4, 1, 0], [4, 1, 1], [4, 1, 2]]
  D2 := [[4, 1, 4], [4, 1, 0], [4, 1, 1], [4, 1, 2], [4, 1, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_63_49_5 : ColCertDiv where
  rK := ⟨63, by decide⟩
  rH := ⟨49, by decide⟩
  m := 5
  T1 := T63_49
  T2 := Q2.T63_49_2
  h1 := (1,4,0,3,4)
  h2 := (1,4,0,3,4)
  D1 := [[1, 0, 0], [1, 0, 4], [1, 0, 3], [1, 0, 2], [1, 0, 1]]
  D2 := [[1, 0, 4], [1, 0, 3], [1, 0, 2], [1, 0, 1], [1, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_63_49_10 : ColCertDiv where
  rK := ⟨63, by decide⟩
  rH := ⟨49, by decide⟩
  m := 5
  T1 := T63_49
  T2 := Q2.T63_49_2
  h1 := (2,3,0,0,2)
  h2 := (2,3,0,0,3)
  D1 := [[2, 0, 0], [2, 0, 3], [2, 0, 1], [2, 0, 4], [2, 0, 2]]
  D2 := [[2, 0, 3], [2, 0, 1], [2, 0, 4], [2, 0, 2], [2, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_63_49_15 : ColCertDiv where
  rK := ⟨63, by decide⟩
  rH := ⟨49, by decide⟩
  m := 5
  T1 := T63_49
  T2 := Q2.T63_49_2
  h1 := (3,2,0,1,2)
  h2 := (3,2,0,1,4)
  D1 := [[3, 0, 0], [3, 0, 2], [3, 0, 4], [3, 0, 1], [3, 0, 3]]
  D2 := [[3, 0, 2], [3, 0, 4], [3, 0, 1], [3, 0, 3], [3, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_63_49_20 : ColCertDiv where
  rK := ⟨63, by decide⟩
  rH := ⟨49, by decide⟩
  m := 5
  T1 := T63_49
  T2 := Q2.T63_49_2
  h1 := (4,1,0,1,3)
  h2 := (4,1,0,1,1)
  D1 := [[4, 0, 0], [4, 0, 1], [4, 0, 2], [4, 0, 3], [4, 0, 4]]
  D2 := [[4, 0, 1], [4, 0, 2], [4, 0, 3], [4, 0, 4], [4, 0, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_67_30_5 : ColCertDiv where
  rK := ⟨67, by decide⟩
  rH := ⟨30, by decide⟩
  m := 5
  T1 := T67_30
  T2 := Q2.T67_30_2
  h1 := (1,2,3,2,3)
  h2 := (1,2,3,2,0)
  D1 := [[1, 3, 3], [1, 3, 2], [1, 3, 1], [1, 3, 0], [1, 3, 4]]
  D2 := [[1, 3, 0], [1, 3, 4], [1, 3, 3], [1, 3, 2], [1, 3, 1]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_67_30_10 : ColCertDiv where
  rK := ⟨67, by decide⟩
  rH := ⟨30, by decide⟩
  m := 5
  T1 := T67_30
  T2 := Q2.T67_30_2
  h1 := (2,4,1,1,4)
  h2 := (2,4,1,1,3)
  D1 := [[2, 1, 1], [2, 1, 4], [2, 1, 2], [2, 1, 0], [2, 1, 3]]
  D2 := [[2, 1, 0], [2, 1, 3], [2, 1, 1], [2, 1, 4], [2, 1, 2]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_67_30_15 : ColCertDiv where
  rK := ⟨67, by decide⟩
  rH := ⟨30, by decide⟩
  m := 5
  T1 := T67_30
  T2 := Q2.T67_30_2
  h1 := (3,1,4,2,1)
  h2 := (3,1,4,2,3)
  D1 := [[3, 4, 4], [3, 4, 1], [3, 4, 3], [3, 4, 0], [3, 4, 2]]
  D2 := [[3, 4, 0], [3, 4, 2], [3, 4, 4], [3, 4, 1], [3, 4, 3]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_67_30_20 : ColCertDiv where
  rK := ⟨67, by decide⟩
  rH := ⟨30, by decide⟩
  m := 5
  T1 := T67_30
  T2 := Q2.T67_30_2
  h1 := (4,3,2,0,4)
  h2 := (4,3,2,0,3)
  D1 := [[4, 2, 2], [4, 2, 3], [4, 2, 4], [4, 2, 0], [4, 2, 1]]
  D2 := [[4, 2, 0], [4, 2, 1], [4, 2, 2], [4, 2, 3], [4, 2, 4]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_67_35_5 : ColCertDiv where
  rK := ⟨67, by decide⟩
  rH := ⟨35, by decide⟩
  m := 5
  T1 := T67_35
  T2 := Q2.T67_35_2
  h1 := (1,2,4,2,0)
  h2 := (1,2,4,2,2)
  D1 := [[1, 4, 2], [1, 4, 1], [1, 4, 0], [1, 4, 4], [1, 4, 3]]
  D2 := [[1, 4, 4], [1, 4, 3], [1, 4, 2], [1, 4, 1], [1, 4, 0]]
  bind1 := by decide
  bind2 := by decide

def colCertDiv_67_35_10 : ColCertDiv where
  rK := ⟨67, by decide⟩
  rH := ⟨35, by decide⟩
  m := 5
  T1 := T67_35
  T2 := Q2.T67_35_2
  h1 := (2,4,3,1,0)
  h2 := (2,4,3,1,4)
  D1 := [[2, 3, 4], [2, 3, 2], [2, 3, 0], [2, 3, 3], [2, 3, 1]]
  D2 := [[2, 3, 3], [2, 3, 1], [2, 3, 4], [2, 3, 2], [2, 3, 0]]
  bind1 := by decide
  bind2 := by decide

end LeanDring.P5Presentation
