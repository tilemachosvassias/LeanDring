/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.Characters.Twin2.CharCert

namespace LeanDring.P5Presentation

open Fin.NatCast

set_option maxRecDepth 100000

set_option maxHeartbeats 4000000 in
-- kernel decide over large certified lists needs extra heartbeats
theorem rowsChunk2h :
    ((((((((List.range 148).drop 37).drop 37).drop 26).drop 16).drop 8).drop 8).drop 8).all
      Q2.checkRows2 = true := by decide

end LeanDring.P5Presentation
