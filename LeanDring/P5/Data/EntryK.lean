/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Data.EntryK.C001
import LeanDring.P5.Data.EntryK.C002
import LeanDring.P5.Data.EntryK.C003
import LeanDring.P5.Data.EntryK.C004
import LeanDring.P5.Data.EntryK.C005
import LeanDring.P5.Data.EntryK.C006
import LeanDring.P5.Data.EntryK.C007
import LeanDring.P5.Data.EntryK.C008
import LeanDring.P5.Data.EntryK.C009
import LeanDring.P5.Data.EntryK.C010
import LeanDring.P5.Data.EntryK.C011
import LeanDring.P5.Data.EntryK.C012
import LeanDring.P5.Data.EntryK.C013
import LeanDring.P5.Data.EntryK.C014
import LeanDring.P5.Data.EntryK.C015
import LeanDring.P5.Data.EntryK.C016
import LeanDring.P5.Data.EntryK.C017
import LeanDring.P5.Data.EntryK.C018
import LeanDring.P5.Data.EntryK.C019
import LeanDring.P5.Data.EntryK.C020
import LeanDring.P5.Data.EntryK.C021
import LeanDring.P5.Data.EntryK.C022
import LeanDring.P5.Data.EntryK.C023
import LeanDring.P5.Data.EntryK.C024
import LeanDring.P5.Data.EntryK.C025
import LeanDring.P5.Data.EntryK.C026
import LeanDring.P5.Data.EntryK.C027
import LeanDring.P5.Data.EntryK.C028
import LeanDring.P5.Data.EntryK.C029
import LeanDring.P5.Data.EntryK.C030
import LeanDring.P5.Data.EntryK.C031
import LeanDring.P5.Data.EntryK.C032
import LeanDring.P5.Data.EntryK.C033
import LeanDring.P5.Data.EntryK.C034
import LeanDring.P5.Data.EntryK.C035
import LeanDring.P5.Data.EntryK.C036
import LeanDring.P5.Data.EntryK.C037
import LeanDring.P5.Data.EntryK.C038
import LeanDring.P5.Data.EntryK.C039
import LeanDring.P5.Data.EntryK.C040
import LeanDring.P5.Data.EntryK.C041
import LeanDring.P5.Data.EntryK.C042
import LeanDring.P5.Data.EntryK.C043
import LeanDring.P5.Data.EntryK.C044

/-!
# P5 Data family: EntryK (44 chunks)

# Species-table cells, K-stratum data (rK = 0): the abstract K = ⊥ column, both twins.

The `K = ⊥` basis class `[⊥, 1]` is the augmentation basis element (`⊥` carries
only the trivial character).  Its species column is proven **abstractly** — no
`3125`-coset transversal is emitted — by reusing the two generic bridge lemmas:

* `LeanDring.DRing.species_basisElt_bot` — for `H ≠ ⊥`, `φ_{H,h}[⊥,λ] = 0`
  (the `G`-action on `G/⊥ ≅ G` is free, so `(G/⊥)^H = ∅` unless `H = ⊥`);
* `LeanDring.DRing.species_bot_one_basisElt` — the augmentation entry
  `φ_{⊥,1}[⊥,1] = |G/⊥| = |G| = 3125`.

So the whole `rK = 0` column is `0` off the augmentation row and `3125` on it,
uniformly for both twins.  `reps_zero_eq_bot` / `reps_zero_eq_bot2` identify the
class representative `reps 0` with `⊥`, tying these to the presentation's row 0.

This index imports all 44 chunks of the `EntryK` family in
`LeanDring/P5/Data/EntryK/`. Files in this family are machine-emitted
data certificates (see the per-chunk docstrings and the emitter scripts
referenced there); they are not intended to be read chunk-by-chunk and are
skippable for readers auditing the hand-written mathematics in
`LeanDring/Theory/`, `LeanDring/P4/`, and `LeanDring/P5/Certificate/`.
-/

