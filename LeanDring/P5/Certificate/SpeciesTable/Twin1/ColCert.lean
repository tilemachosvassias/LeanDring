/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.EntryFast
import LeanDring.P5.Certificate.SpeciesTable.EntrySupport

/-!
# The per-column certified exponent-vector data

The species-table comparison runs, for every on-support cell of the 2724×2724
species table, over the two twins' species values. The entry-code layer
(`LeanDring/P5/Certificate/SpeciesTable/EntryFast.lean` and
`.../SpeciesTable/EntrySupport.lean`)
reduces a cell to the pure-ℕ fast code `sumPowers (fastCode D e)`, where the
*column data* `D : ι → List ℕ` is the sequence of exponent vectors
`expVec (basisAt rK) (t(i)⁻¹ · h · t(i))` over the certified `H`-fixed transversal
`t = T(H,K)`.  Crucially `D` does **not** depend on the row character `e`, so it is
computed **once per column** `(rK-class, (H,h) orbit-rep)`, not once per cell.

This module defines the uniform certificate that carries that once-per-column data
into the kernel:

* **`ColCert`** — a column whose exponent data **coincides** between the twins
  (83 % of on-support columns): ONE embedded list `D : List (List ℕ)` and two
  kernel `decide` bindings `bind1 : colData1 … = D` (q=1) and
  `bind2 : colData2 … = D` (q=2).  `ColCert.hD` derives
  `colData1 … = colData2 …` (`bind1.trans bind2.symm`) — the exact `hD` input of
  `species_eq_of_data_eq`, so a twin-equal cell then discharges by `rfl` on the
  fast code with **no** genuine evaluation.

* **`ColCertDiv`** — a column whose exponent data **diverges** between the twins
  (the τ-moved columns and the col-data-divergent families): TWO embedded lists
  `D1`, `D2` with the analogous bindings.  These feed a residual
  `decide` of `fastCode D1 e` vs `fastCode D2 e'`.

Each `bind*` is one kernel `decide` that evaluates the `|T|` group products / echelon
sifts **once**; the embedded list is what the
kernel certifies.  The binding is stated as a *function* equality
`colData1 rK h t = fun i => D.getD i.val []` so `ColCert.hD` chains directly into
`species_eq_of_data_eq` (which wants `colData1 … = colData2 …`).

The concrete per-column instances live under `LeanDring/P5/Data/`
(`ColRestCheap/`, `ColRestHeavy/`, `ColCdd/`, `ColTau/`), chunked ≤8 heavy
columns per file (`|T| ∈ {125, 625}` are heavy; `|T| ≤ 25` cheap, batched more).
-/

namespace LeanDring.P5Presentation

open scoped BigOperators

/-- Reconstitute the column-data function from an embedded exponent-vector list:
`i ↦ D[i]` (default `[]` off the end, never hit for a length-`m` list over `Fin m`). -/
def colFn (D : List (List ℕ)) {m : ℕ} : Fin m → List ℕ := fun i => D.getD i.val []

/-- **The coincident-column certificate.** For a row class `rK`, column class `rH`,
shared-length transversals `T1`/`T2` (q=1/q=2, same underlying coordinate list) and
column elements `h1`/`h2`, the single embedded list `D` is the exponent-vector data
of BOTH twins — certified by the two kernel `decide` bindings. -/
structure ColCert where
  /-- Row (subgroup `K`) class index. -/
  rK : Fin 148
  /-- Column (subgroup `H`) class index. -/
  rH : Fin 148
  /-- Transversal length `|T(H,K)| = |(G/K)^H|`. -/
  m : ℕ
  /-- The q=1 certified `H`-fixed transversal. -/
  T1 : Fin m → Coordinate 1
  /-- The q=2 (twin) certified `H`-fixed transversal (same underlying list). -/
  T2 : Fin m → Coordinate 2
  /-- The q=1 column element `h ∈ H`. -/
  h1 : Coordinate 1
  /-- The q=2 (twin) column element. -/
  h2 : Coordinate 2
  /-- The shared embedded exponent-vector data. -/
  D : List (List ℕ)
  /-- q=1 kernel binding: the column data equals the embedded list. -/
  bind1 : colData1 rK h1 T1 = colFn D
  /-- q=2 kernel binding: the twin column data equals the SAME embedded list. -/
  bind2 : colData2 rK h2 T2 = colFn D

/-- **The twin data-equality of a coincident column.** The two twins' column-data
functions coincide — exactly the `hD` hypothesis of `species_eq_of_data_eq`. -/
theorem ColCert.hD (c : ColCert) :
    colData1 c.rK c.h1 c.T1 = colData2 c.rK c.h2 c.T2 :=
  c.bind1.trans c.bind2.symm

/-- **The divergent-column certificate.** The twins' exponent data differ (τ-moved
or col-data-divergent columns): two embedded lists `D1`/`D2`, each certified by a
kernel binding.  Stage 4 compares `fastCode D1 e` vs `fastCode D2 e'` directly. -/
structure ColCertDiv where
  /-- Row (subgroup `K`) class index. -/
  rK : Fin 148
  /-- Column (subgroup `H`) class index. -/
  rH : Fin 148
  /-- Transversal length. -/
  m : ℕ
  /-- The q=1 certified transversal. -/
  T1 : Fin m → Coordinate 1
  /-- The q=2 certified transversal. -/
  T2 : Fin m → Coordinate 2
  /-- The q=1 column element. -/
  h1 : Coordinate 1
  /-- The q=2 column element. -/
  h2 : Coordinate 2
  /-- The q=1 embedded exponent-vector data. -/
  D1 : List (List ℕ)
  /-- The q=2 embedded exponent-vector data. -/
  D2 : List (List ℕ)
  /-- q=1 kernel binding. -/
  bind1 : colData1 rK h1 T1 = colFn D1
  /-- q=2 kernel binding. -/
  bind2 : colData2 rK h2 T2 = colFn D2

end LeanDring.P5Presentation
