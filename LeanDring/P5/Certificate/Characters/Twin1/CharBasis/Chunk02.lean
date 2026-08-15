/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.Characters.Twin1.CharCert

namespace LeanDring.P5Presentation
set_option maxRecDepth 100000

theorem basisChunk1 : (((List.range 148).drop 37).take 37).all checkBasis = true := by decide

end LeanDring.P5Presentation
