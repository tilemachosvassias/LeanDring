/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.ConjugacyClasses.Twin2.NormCard

/-!
# Link 1, discharged: the emitted normalizer index is `N_G(reps r)`

The single heavy kernel check of link 1 (`NormCard.lean`): for every one of the 148
representatives, the generators of the candidate normalizer base
`getB (normIdxData r)` (and their inverses) conjugate every generator of
`reps r`'s echelon basis back into `reps r`. Isolated in its own file/process
(sift-only `ZMod 25` arithmetic).

Combined with the normalizer-card pin of `NormCard.lean`, this makes
`normAt_eq` unconditional: `subAt (normIdxData r) = N_G(reps r)` for all `r`.
-/

namespace LeanDring.P5Presentation

namespace Q2

open Fin.NatCast

set_option maxRecDepth 100000

set_option maxHeartbeats 4000000 in
-- kernel decide over large certified lists needs extra heartbeats
/-- **The whole-range link-1 sift certificate.** -/
theorem normSiftCheck_all : (List.range 148).all normSiftCheck = true := by decide

set_option maxHeartbeats 4000000 in
-- kernel decide over large certified lists needs extra heartbeats
/-- **Link 1, unconditional.** The emitted index `normIdxData r` presents exactly
the normalizer `N_G(reps r)` of the `r`-th subgroup-class representative. -/
theorem normAt_eq_final (r : Fin 148) :
    subAt (normIdxData.getD r.val 0) =
      Subgroup.normalizer ((reps r : Subgroup (Coordinate 2)) : Set (Coordinate 2)) :=
  normAt_eq_of_all normSiftCheck_all r

end Q2

end LeanDring.P5Presentation
