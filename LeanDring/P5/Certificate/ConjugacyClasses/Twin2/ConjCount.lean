/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.ConjugacyClasses.Twin2.ConjData

/-!
# q=2 partition-count checks : class sizes sum to 676, and 71 classes are normal.
-/

namespace LeanDring.P5Presentation

namespace Q2

set_option maxRecDepth 100000

set_option maxHeartbeats 10000000 in
-- kernel decide over large certified lists needs extra heartbeats
theorem classSize_sum : ((List.range 148).map classSizeNat).sum = 676 := by decide

set_option maxHeartbeats 10000000 in
-- kernel decide over large certified lists needs extra heartbeats
theorem normal_count :
    ((List.range 148).filter (fun c => isNormalIdx (classRepsData.getD c 0))).length = 71 := by
  decide

end Q2

end LeanDring.P5Presentation
