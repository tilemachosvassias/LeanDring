/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.Characters.Twin2.CharCert

namespace LeanDring.P5Presentation

open Fin.NatCast

set_option maxRecDepth 100000
-- file-level maxHeartbeats: the kernel `decide`s below exceed the default budget
set_option linter.style.setOption false
set_option maxHeartbeats 4000000

theorem countChunk2_0 : ((List.range 148).take 37).all Q2.checkCount2 = true := by decide

theorem countChunk2_1 : (((List.range 148).drop 37).take 37).all Q2.checkCount2 = true := by decide

theorem countChunk2_2 :
    ((((List.range 148).drop 37).drop 37).take 37).all Q2.checkCount2 = true := by decide

theorem countChunk2_3 :
    ((((List.range 148).drop 37).drop 37).drop 37).all Q2.checkCount2 = true := by decide


end LeanDring.P5Presentation
