/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.ConjugacyClasses.Twin1.ConjData

/-!
# Class-invariance checks: each conjugation row preserves the class label

Five sift-free `getD`-only kernel `decide`s (one per generator row), plus the five
row-length facts, isolated from the sift-heavy conjugation rows and from the
tree/count checks so that each kernel invocation stays in its own low-memory
process.
-/

namespace LeanDring.P5Presentation

set_option maxRecDepth 100000
-- file-level maxHeartbeats: dozens of decide-heavy declarations below need it
set_option linter.style.setOption false
set_option maxHeartbeats 10000000

theorem classInvRowCheck_0 : classInvRowCheck 0 = true := by decide
theorem classInvRowCheck_1 : classInvRowCheck 1 = true := by decide
theorem classInvRowCheck_2 : classInvRowCheck 2 = true := by decide
theorem classInvRowCheck_3 : classInvRowCheck 3 = true := by decide
theorem classInvRowCheck_4 : classInvRowCheck 4 = true := by decide

theorem conjTab_row_length_0 : (conjTab.getD 0 []).length = 676 := by decide
theorem conjTab_row_length_1 : (conjTab.getD 1 []).length = 676 := by decide
theorem conjTab_row_length_2 : (conjTab.getD 2 []).length = 676 := by decide
theorem conjTab_row_length_3 : (conjTab.getD 3 []).length = 676 := by decide
theorem conjTab_row_length_4 : (conjTab.getD 4 []).length = 676 := by decide

end LeanDring.P5Presentation
