/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.ConjugacyClasses.Twin1.ConjData

/-!
# BFS-tree validity check: the reachability tree is well-founded
-/

namespace LeanDring.P5Presentation

set_option maxRecDepth 100000

set_option maxHeartbeats 10000000 in
-- kernel decide over large certified lists needs extra heartbeats
theorem treeCheckAll_true : treeCheckAll = true :=
  all676_of_chunks treeEntryOK (by decide) (by decide) (by decide) (by decide)

end LeanDring.P5Presentation
