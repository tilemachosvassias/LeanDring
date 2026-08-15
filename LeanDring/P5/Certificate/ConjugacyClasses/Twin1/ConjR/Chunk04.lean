/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.ConjugacyClasses.Twin1.ConjData

/-!
# Conjugation row 3 check: `(subAt i)^{g_3} = subAt (conjMove 3 i)`, all 676 `i`

A single kernel `decide` over the zip of `allBases` with row 3 of `conjTab`
(isolated in its own process). No `native_decide`.
-/

namespace LeanDring.P5Presentation

set_option maxRecDepth 100000

set_option maxHeartbeats 10000000 in
-- kernel decide over large certified lists needs extra heartbeats
theorem conjRowCheck_3 : conjRowCheck 3 = true := by decide

end LeanDring.P5Presentation
