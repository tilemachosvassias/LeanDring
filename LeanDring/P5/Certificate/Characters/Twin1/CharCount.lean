/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.Characters.Twin1.CharCert

namespace LeanDring.P5Presentation
set_option maxRecDepth 100000
-- file-level maxHeartbeats: the kernel `decide`s below exceed the default budget
set_option linter.style.setOption false
set_option maxHeartbeats 2000000

theorem countChunk0 : ((List.range 148).take 37).all checkCount = true := by decide

theorem countChunk1 : (((List.range 148).drop 37).take 37).all checkCount = true := by decide

theorem countChunk2 :
    ((((List.range 148).drop 37).drop 37).take 37).all checkCount = true := by decide

theorem countChunk3 :
    ((((List.range 148).drop 37).drop 37).drop 37).all checkCount = true := by decide

end LeanDring.P5Presentation
