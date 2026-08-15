/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.ConjugacyClasses.Twin1.ConjData

/-!
# Conjugation row 0 check: `(subAt i)^{g_0} = subAt (conjMove 0 i)`, all 676 `i`

A single kernel `decide` over the zip of `allBases` with row 0 of `conjTab`
(isolated in its own process). No `native_decide`.
-/

namespace LeanDring.P5Presentation

set_option maxRecDepth 100000

set_option maxHeartbeats 10000000 in
-- kernel decide over the full 676-entry conjugation row
theorem conjRowCheck_0 : conjRowCheck 0 = true := by decide

end LeanDring.P5Presentation
