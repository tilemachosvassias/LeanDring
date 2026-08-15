/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Data.ColTau.C001
import LeanDring.P5.Data.ColTau.C002
import LeanDring.P5.Data.ColTau.C003
import LeanDring.P5.Data.ColTau.C004

/-!
# P5 Data family: ColTau (4 chunks)

# Species-table cell data, stage 2 — τ-moved columns

Per-column certified exponent-vector data (`ColCert`/`ColCertDiv`) with kernel
`decide` bindings. Emitted; the embedded lists are what the kernel certifies.

This index imports all 4 chunks of the `ColTau` family in
`LeanDring/P5/Data/ColTau/`. Files in this family are machine-emitted
data certificates (see the per-chunk docstrings and the emitter scripts
referenced there); they are not intended to be read chunk-by-chunk and are
skippable for readers auditing the hand-written mathematics in
`LeanDring/Theory/`, `LeanDring/P4/`, and `LeanDring/P5/Certificate/`.
-/

