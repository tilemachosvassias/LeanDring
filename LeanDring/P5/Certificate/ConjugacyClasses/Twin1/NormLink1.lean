/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.ConjugacyClasses.Twin1.NormCard

/-!
# The normalizer sift certificate, discharged

The single heavy kernel check behind `NormCard.lean`'s identification of the
emitted normalizer index: for every one of the 148 representatives, the
generators of the candidate normalizer base `getB (normIdxData r)` (and their
inverses) conjugate every generator of `reps r`'s echelon basis back into
`reps r`. Isolated in its own file, and hence its own kernel process, because it
is the only sift-heavy step of that argument.

Combined with the normalizer-card pin of `NormCard.lean`, this makes `normAt_eq`
unconditional: `subAt (normIdxData r) = N_G(reps r)` for all `r`.
-/

namespace LeanDring.P5Presentation

open Fin.NatCast

set_option maxRecDepth 100000

set_option maxHeartbeats 4000000 in
-- kernel decide over large certified lists needs extra heartbeats
/-- **The whole-range sift certificate.** -/
theorem normSiftCheck_all : (List.range 148).all normSiftCheck = true := by decide

set_option maxHeartbeats 4000000 in
-- kernel decide over large certified lists needs extra heartbeats
/-- **The identification, unconditional.** The emitted index `normIdxData r`
presents exactly the normalizer `N_G(reps r)` of the `r`-th subgroup-class
representative. -/
theorem normAt_eq_final (r : Fin 148) :
    subAt (normIdxData.getD r.val 0) =
      Subgroup.normalizer ((reps r : Subgroup (Coordinate 1)) : Set (Coordinate 1)) :=
  normAt_eq_of_all normSiftCheck_all r

end LeanDring.P5Presentation
