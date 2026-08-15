/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Data.FixZero.C085
import LeanDring.P5.Data.FixZero.C086
import LeanDring.P5.Data.FixZero.C087
import LeanDring.P5.Data.FixZero.C088
import LeanDring.P5.Certificate.RingIsomorphism.MatchCore
import LeanDring.P5.Data.MatchPair.C012
import LeanDring.P5.Data.MatchPair.C007
import LeanDring.P5.Data.MatchPair.C008

/-! # Stage-5 per-column-class master theorems, chunk 15 (auto-emitted).  -/

namespace LeanDring.P5Presentation

open MulAction Finset LeanDring.DRing LeanDring.MonGSet

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.style.longLine false

theorem master_120 (p : Nat) (hp : p < (Q2.transData.getD 120 []).length)
    (hrep : (Q2.cosetIsRep.getD 120 []).getD p false = true)
    (rK : Fin 148) (j : Nat) (hj : j < (repChars.getD rK.val []).length)
    (hq : (normIsRep.getD rK.val []).getD j false = true) :
    species (Q2.reps (⟨120, by decide⟩ : Fin 148)) (colE2 ⟨120, by decide⟩ p hp)
        (rowE2 rK j hj hq)
      = species (reps (⟨120, by decide⟩ : Fin 148))
        (colE1 ⟨120, by decide⟩ p (transLenTr ⟨120, by decide⟩ p hp)) (rowE1 rK j hj) := by
  rcases rK with ⟨nK, hnK⟩; interval_cases nK
  · exact match_zero_len ⟨0, by decide⟩ ⟨120, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨1, by decide⟩ ⟨120, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨2, by decide⟩ ⟨120, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨3, by decide⟩ ⟨120, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨4, by decide⟩ ⟨120, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨5, by decide⟩ ⟨120, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨6, by decide⟩ ⟨120, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨7, by decide⟩ ⟨120, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨8, by decide⟩ ⟨120, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨9, by decide⟩ ⟨120, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨10, by decide⟩ ⟨120, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨11, by decide⟩ ⟨120, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨12, by decide⟩ ⟨120, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨13, by decide⟩ ⟨120, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨14, by decide⟩ ⟨120, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨15, by decide⟩ ⟨120, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨16, by decide⟩ ⟨120, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨17, by decide⟩ ⟨120, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨18, by decide⟩ ⟨120, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨19, by decide⟩ ⟨120, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨20, by decide⟩ ⟨120, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨21, by decide⟩ ⟨120, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨22, by decide⟩ ⟨120, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨23, by decide⟩ ⟨120, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨24, by decide⟩ ⟨120, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨25, by decide⟩ ⟨120, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨26, by decide⟩ ⟨120, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨27, by decide⟩ ⟨120, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨28, by decide⟩ ⟨120, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨29, by decide⟩ ⟨120, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨30, by decide⟩ ⟨120, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨31, by decide⟩ ⟨120, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨32, by decide⟩ ⟨120, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨33, by decide⟩ ⟨120, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨34, by decide⟩ ⟨120, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨35, by decide⟩ ⟨120, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨36, by decide⟩ ⟨120, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨37, by decide⟩ ⟨120, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨38, by decide⟩ ⟨120, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨39, by decide⟩ ⟨120, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨40, by decide⟩ ⟨120, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨41, by decide⟩ ⟨120, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨42, by decide⟩ ⟨120, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨43, by decide⟩ ⟨120, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨44, by decide⟩ ⟨120, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨45, by decide⟩ ⟨120, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨46, by decide⟩ ⟨120, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨47, by decide⟩ ⟨120, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨48, by decide⟩ ⟨120, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨49, by decide⟩ ⟨120, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨50, by decide⟩ ⟨120, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨51, by decide⟩ ⟨120, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨52, by decide⟩ ⟨120, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨53, by decide⟩ ⟨120, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨54, by decide⟩ ⟨120, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨55, by decide⟩ ⟨120, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨56, by decide⟩ ⟨120, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨57, by decide⟩ ⟨120, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨58, by decide⟩ ⟨120, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨59, by decide⟩ ⟨120, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨60, by decide⟩ ⟨120, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨61, by decide⟩ ⟨120, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨62, by decide⟩ ⟨120, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨63, by decide⟩ ⟨120, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨64, by decide⟩ ⟨120, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨65, by decide⟩ ⟨120, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨66, by decide⟩ ⟨120, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨67, by decide⟩ ⟨120, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨68, by decide⟩ ⟨120, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨69, by decide⟩ ⟨120, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨70, by decide⟩ ⟨120, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨71, by decide⟩ ⟨120, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨72, by decide⟩ ⟨120, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨73, by decide⟩ ⟨120, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨74, by decide⟩ ⟨120, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨75, by decide⟩ ⟨120, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨76, by decide⟩ ⟨120, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨77, by decide⟩ ⟨120, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨78, by decide⟩ ⟨120, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨79, by decide⟩ ⟨120, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨80, by decide⟩ ⟨120, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨81, by decide⟩ ⟨120, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨82, by decide⟩ ⟨120, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨83, by decide⟩ ⟨120, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨84, by decide⟩ ⟨120, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨85, by decide⟩ ⟨120, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨86, by decide⟩ ⟨120, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨87, by decide⟩ ⟨120, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨88, by decide⟩ ⟨120, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨89, by decide⟩ ⟨120, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨90, by decide⟩ ⟨120, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨91, by decide⟩ ⟨120, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨92, by decide⟩ ⟨120, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨93, by decide⟩ ⟨120, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨94, by decide⟩ ⟨120, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨95, by decide⟩ ⟨120, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨96, by decide⟩ ⟨120, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨97, by decide⟩ ⟨120, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨98, by decide⟩ ⟨120, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨99, by decide⟩ ⟨120, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨100, by decide⟩ ⟨120, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨101, by decide⟩ ⟨120, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨102, by decide⟩ ⟨120, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨103, by decide⟩ ⟨120, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨104, by decide⟩ ⟨120, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨105, by decide⟩ ⟨120, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨106, by decide⟩ ⟨120, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨107, by decide⟩ ⟨120, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨108, by decide⟩ ⟨120, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨109, by decide⟩ ⟨120, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨110, by decide⟩ ⟨120, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨111, by decide⟩ ⟨120, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨112, by decide⟩ ⟨120, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨113, by decide⟩ ⟨120, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨114, by decide⟩ ⟨120, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨115, by decide⟩ ⟨120, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_fix ⟨116, by decide⟩ ⟨120, by decide⟩ p hp j hj hq fz1_116_120 fz2_116_120
  · exact match_zero_fix ⟨117, by decide⟩ ⟨120, by decide⟩ p hp j hj hq fz1_117_120 fz2_117_120
  · exact match_zero_fix ⟨118, by decide⟩ ⟨120, by decide⟩ p hp j hj hq fz1_118_120 fz2_118_120
  · exact match_zero_fix ⟨119, by decide⟩ ⟨120, by decide⟩ p hp j hj hq fz1_119_120 fz2_119_120
  · exact pair_120_120 p hp hrep j hj hq
  · exact match_zero_fix ⟨121, by decide⟩ ⟨120, by decide⟩ p hp j hj hq fz1_121_120 fz2_121_120
  · exact match_zero_fix ⟨122, by decide⟩ ⟨120, by decide⟩ p hp j hj hq fz1_122_120 fz2_122_120
  · exact match_zero_fix ⟨123, by decide⟩ ⟨120, by decide⟩ p hp j hj hq fz1_123_120 fz2_123_120
  · exact match_zero_fix ⟨124, by decide⟩ ⟨120, by decide⟩ p hp j hj hq fz1_124_120 fz2_124_120
  · exact match_zero_fix ⟨125, by decide⟩ ⟨120, by decide⟩ p hp j hj hq fz1_125_120 fz2_125_120
  · exact match_zero_fix ⟨126, by decide⟩ ⟨120, by decide⟩ p hp j hj hq fz1_126_120 fz2_126_120
  · exact match_zero_fix ⟨127, by decide⟩ ⟨120, by decide⟩ p hp j hj hq fz1_127_120 fz2_127_120
  · exact match_zero_fix ⟨128, by decide⟩ ⟨120, by decide⟩ p hp j hj hq fz1_128_120 fz2_128_120
  · exact match_zero_fix ⟨129, by decide⟩ ⟨120, by decide⟩ p hp j hj hq fz1_129_120 fz2_129_120
  · exact match_zero_fix ⟨130, by decide⟩ ⟨120, by decide⟩ p hp j hj hq fz1_130_120 fz2_130_120
  · exact match_zero_fix ⟨131, by decide⟩ ⟨120, by decide⟩ p hp j hj hq fz1_131_120 fz2_131_120
  · exact match_zero_fix ⟨132, by decide⟩ ⟨120, by decide⟩ p hp j hj hq fz1_132_120 fz2_132_120
  · exact match_zero_fix ⟨133, by decide⟩ ⟨120, by decide⟩ p hp j hj hq fz1_133_120 fz2_133_120
  · exact match_zero_fix ⟨134, by decide⟩ ⟨120, by decide⟩ p hp j hj hq fz1_134_120 fz2_134_120
  · exact match_zero_fix ⟨135, by decide⟩ ⟨120, by decide⟩ p hp j hj hq fz1_135_120 fz2_135_120
  · exact match_zero_fix ⟨136, by decide⟩ ⟨120, by decide⟩ p hp j hj hq fz1_136_120 fz2_136_120
  · exact match_zero_fix ⟨137, by decide⟩ ⟨120, by decide⟩ p hp j hj hq fz1_137_120 fz2_137_120
  · exact match_zero_fix ⟨138, by decide⟩ ⟨120, by decide⟩ p hp j hj hq fz1_138_120 fz2_138_120
  · exact match_zero_fix ⟨139, by decide⟩ ⟨120, by decide⟩ p hp j hj hq fz1_139_120 fz2_139_120
  · exact match_zero_fix ⟨140, by decide⟩ ⟨120, by decide⟩ p hp j hj hq fz1_140_120 fz2_140_120
  · exact match_zero_fix ⟨141, by decide⟩ ⟨120, by decide⟩ p hp j hj hq fz1_141_120 fz2_141_120
  · exact match_zero_fix ⟨142, by decide⟩ ⟨120, by decide⟩ p hp j hj hq fz1_142_120 fz2_142_120
  · exact match_zero_fix ⟨143, by decide⟩ ⟨120, by decide⟩ p hp j hj hq fz1_143_120 fz2_143_120
  · exact match_zero_fix ⟨144, by decide⟩ ⟨120, by decide⟩ p hp j hj hq fz1_144_120 fz2_144_120
  · exact match_zero_fix ⟨145, by decide⟩ ⟨120, by decide⟩ p hp j hj hq fz1_145_120 fz2_145_120
  · exact match_zero_fix ⟨146, by decide⟩ ⟨120, by decide⟩ p hp j hj hq fz1_146_120 fz2_146_120
  · exact pair_147_120 p hp hrep j hj hq

theorem master_121 (p : Nat) (hp : p < (Q2.transData.getD 121 []).length)
    (hrep : (Q2.cosetIsRep.getD 121 []).getD p false = true)
    (rK : Fin 148) (j : Nat) (hj : j < (repChars.getD rK.val []).length)
    (hq : (normIsRep.getD rK.val []).getD j false = true) :
    species (Q2.reps (⟨121, by decide⟩ : Fin 148)) (colE2 ⟨121, by decide⟩ p hp)
        (rowE2 rK j hj hq)
      = species (reps (⟨121, by decide⟩ : Fin 148))
        (colE1 ⟨121, by decide⟩ p (transLenTr ⟨121, by decide⟩ p hp)) (rowE1 rK j hj) := by
  rcases rK with ⟨nK, hnK⟩; interval_cases nK
  · exact match_zero_len ⟨0, by decide⟩ ⟨121, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨1, by decide⟩ ⟨121, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨2, by decide⟩ ⟨121, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨3, by decide⟩ ⟨121, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨4, by decide⟩ ⟨121, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨5, by decide⟩ ⟨121, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨6, by decide⟩ ⟨121, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨7, by decide⟩ ⟨121, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨8, by decide⟩ ⟨121, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨9, by decide⟩ ⟨121, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨10, by decide⟩ ⟨121, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨11, by decide⟩ ⟨121, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨12, by decide⟩ ⟨121, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨13, by decide⟩ ⟨121, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨14, by decide⟩ ⟨121, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨15, by decide⟩ ⟨121, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨16, by decide⟩ ⟨121, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨17, by decide⟩ ⟨121, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨18, by decide⟩ ⟨121, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨19, by decide⟩ ⟨121, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨20, by decide⟩ ⟨121, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨21, by decide⟩ ⟨121, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨22, by decide⟩ ⟨121, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨23, by decide⟩ ⟨121, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨24, by decide⟩ ⟨121, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨25, by decide⟩ ⟨121, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨26, by decide⟩ ⟨121, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨27, by decide⟩ ⟨121, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨28, by decide⟩ ⟨121, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨29, by decide⟩ ⟨121, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨30, by decide⟩ ⟨121, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨31, by decide⟩ ⟨121, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨32, by decide⟩ ⟨121, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨33, by decide⟩ ⟨121, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨34, by decide⟩ ⟨121, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨35, by decide⟩ ⟨121, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨36, by decide⟩ ⟨121, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨37, by decide⟩ ⟨121, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨38, by decide⟩ ⟨121, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨39, by decide⟩ ⟨121, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨40, by decide⟩ ⟨121, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨41, by decide⟩ ⟨121, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨42, by decide⟩ ⟨121, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨43, by decide⟩ ⟨121, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨44, by decide⟩ ⟨121, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨45, by decide⟩ ⟨121, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨46, by decide⟩ ⟨121, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨47, by decide⟩ ⟨121, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨48, by decide⟩ ⟨121, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨49, by decide⟩ ⟨121, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨50, by decide⟩ ⟨121, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨51, by decide⟩ ⟨121, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨52, by decide⟩ ⟨121, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨53, by decide⟩ ⟨121, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨54, by decide⟩ ⟨121, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨55, by decide⟩ ⟨121, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨56, by decide⟩ ⟨121, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨57, by decide⟩ ⟨121, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨58, by decide⟩ ⟨121, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨59, by decide⟩ ⟨121, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨60, by decide⟩ ⟨121, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨61, by decide⟩ ⟨121, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨62, by decide⟩ ⟨121, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨63, by decide⟩ ⟨121, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨64, by decide⟩ ⟨121, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨65, by decide⟩ ⟨121, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨66, by decide⟩ ⟨121, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨67, by decide⟩ ⟨121, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨68, by decide⟩ ⟨121, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨69, by decide⟩ ⟨121, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨70, by decide⟩ ⟨121, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨71, by decide⟩ ⟨121, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨72, by decide⟩ ⟨121, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨73, by decide⟩ ⟨121, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨74, by decide⟩ ⟨121, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨75, by decide⟩ ⟨121, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨76, by decide⟩ ⟨121, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨77, by decide⟩ ⟨121, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨78, by decide⟩ ⟨121, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨79, by decide⟩ ⟨121, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨80, by decide⟩ ⟨121, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨81, by decide⟩ ⟨121, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨82, by decide⟩ ⟨121, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨83, by decide⟩ ⟨121, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨84, by decide⟩ ⟨121, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨85, by decide⟩ ⟨121, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨86, by decide⟩ ⟨121, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨87, by decide⟩ ⟨121, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨88, by decide⟩ ⟨121, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨89, by decide⟩ ⟨121, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨90, by decide⟩ ⟨121, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨91, by decide⟩ ⟨121, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨92, by decide⟩ ⟨121, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨93, by decide⟩ ⟨121, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨94, by decide⟩ ⟨121, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨95, by decide⟩ ⟨121, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨96, by decide⟩ ⟨121, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨97, by decide⟩ ⟨121, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨98, by decide⟩ ⟨121, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨99, by decide⟩ ⟨121, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨100, by decide⟩ ⟨121, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨101, by decide⟩ ⟨121, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨102, by decide⟩ ⟨121, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨103, by decide⟩ ⟨121, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨104, by decide⟩ ⟨121, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨105, by decide⟩ ⟨121, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨106, by decide⟩ ⟨121, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨107, by decide⟩ ⟨121, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨108, by decide⟩ ⟨121, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨109, by decide⟩ ⟨121, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨110, by decide⟩ ⟨121, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨111, by decide⟩ ⟨121, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨112, by decide⟩ ⟨121, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨113, by decide⟩ ⟨121, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨114, by decide⟩ ⟨121, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨115, by decide⟩ ⟨121, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_fix ⟨116, by decide⟩ ⟨121, by decide⟩ p hp j hj hq fz1_116_121 fz2_116_121
  · exact match_zero_fix ⟨117, by decide⟩ ⟨121, by decide⟩ p hp j hj hq fz1_117_121 fz2_117_121
  · exact match_zero_fix ⟨118, by decide⟩ ⟨121, by decide⟩ p hp j hj hq fz1_118_121 fz2_118_121
  · exact match_zero_fix ⟨119, by decide⟩ ⟨121, by decide⟩ p hp j hj hq fz1_119_121 fz2_119_121
  · exact match_zero_fix ⟨120, by decide⟩ ⟨121, by decide⟩ p hp j hj hq fz1_120_121 fz2_120_121
  · exact pair_121_121 p hp hrep j hj hq
  · exact match_zero_fix ⟨122, by decide⟩ ⟨121, by decide⟩ p hp j hj hq fz1_122_121 fz2_122_121
  · exact match_zero_fix ⟨123, by decide⟩ ⟨121, by decide⟩ p hp j hj hq fz1_123_121 fz2_123_121
  · exact match_zero_fix ⟨124, by decide⟩ ⟨121, by decide⟩ p hp j hj hq fz1_124_121 fz2_124_121
  · exact match_zero_fix ⟨125, by decide⟩ ⟨121, by decide⟩ p hp j hj hq fz1_125_121 fz2_125_121
  · exact match_zero_fix ⟨126, by decide⟩ ⟨121, by decide⟩ p hp j hj hq fz1_126_121 fz2_126_121
  · exact match_zero_fix ⟨127, by decide⟩ ⟨121, by decide⟩ p hp j hj hq fz1_127_121 fz2_127_121
  · exact match_zero_fix ⟨128, by decide⟩ ⟨121, by decide⟩ p hp j hj hq fz1_128_121 fz2_128_121
  · exact match_zero_fix ⟨129, by decide⟩ ⟨121, by decide⟩ p hp j hj hq fz1_129_121 fz2_129_121
  · exact match_zero_fix ⟨130, by decide⟩ ⟨121, by decide⟩ p hp j hj hq fz1_130_121 fz2_130_121
  · exact match_zero_fix ⟨131, by decide⟩ ⟨121, by decide⟩ p hp j hj hq fz1_131_121 fz2_131_121
  · exact match_zero_fix ⟨132, by decide⟩ ⟨121, by decide⟩ p hp j hj hq fz1_132_121 fz2_132_121
  · exact match_zero_fix ⟨133, by decide⟩ ⟨121, by decide⟩ p hp j hj hq fz1_133_121 fz2_133_121
  · exact match_zero_fix ⟨134, by decide⟩ ⟨121, by decide⟩ p hp j hj hq fz1_134_121 fz2_134_121
  · exact match_zero_fix ⟨135, by decide⟩ ⟨121, by decide⟩ p hp j hj hq fz1_135_121 fz2_135_121
  · exact match_zero_fix ⟨136, by decide⟩ ⟨121, by decide⟩ p hp j hj hq fz1_136_121 fz2_136_121
  · exact match_zero_fix ⟨137, by decide⟩ ⟨121, by decide⟩ p hp j hj hq fz1_137_121 fz2_137_121
  · exact match_zero_fix ⟨138, by decide⟩ ⟨121, by decide⟩ p hp j hj hq fz1_138_121 fz2_138_121
  · exact match_zero_fix ⟨139, by decide⟩ ⟨121, by decide⟩ p hp j hj hq fz1_139_121 fz2_139_121
  · exact match_zero_fix ⟨140, by decide⟩ ⟨121, by decide⟩ p hp j hj hq fz1_140_121 fz2_140_121
  · exact match_zero_fix ⟨141, by decide⟩ ⟨121, by decide⟩ p hp j hj hq fz1_141_121 fz2_141_121
  · exact match_zero_fix ⟨142, by decide⟩ ⟨121, by decide⟩ p hp j hj hq fz1_142_121 fz2_142_121
  · exact match_zero_fix ⟨143, by decide⟩ ⟨121, by decide⟩ p hp j hj hq fz1_143_121 fz2_143_121
  · exact match_zero_fix ⟨144, by decide⟩ ⟨121, by decide⟩ p hp j hj hq fz1_144_121 fz2_144_121
  · exact match_zero_fix ⟨145, by decide⟩ ⟨121, by decide⟩ p hp j hj hq fz1_145_121 fz2_145_121
  · exact match_zero_fix ⟨146, by decide⟩ ⟨121, by decide⟩ p hp j hj hq fz1_146_121 fz2_146_121
  · exact pair_147_121 p hp hrep j hj hq

theorem master_122 (p : Nat) (hp : p < (Q2.transData.getD 122 []).length)
    (hrep : (Q2.cosetIsRep.getD 122 []).getD p false = true)
    (rK : Fin 148) (j : Nat) (hj : j < (repChars.getD rK.val []).length)
    (hq : (normIsRep.getD rK.val []).getD j false = true) :
    species (Q2.reps (⟨122, by decide⟩ : Fin 148)) (colE2 ⟨122, by decide⟩ p hp)
        (rowE2 rK j hj hq)
      = species (reps (⟨122, by decide⟩ : Fin 148))
        (colE1 ⟨122, by decide⟩ p (transLenTr ⟨122, by decide⟩ p hp)) (rowE1 rK j hj) := by
  rcases rK with ⟨nK, hnK⟩; interval_cases nK
  · exact match_zero_len ⟨0, by decide⟩ ⟨122, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨1, by decide⟩ ⟨122, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨2, by decide⟩ ⟨122, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨3, by decide⟩ ⟨122, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨4, by decide⟩ ⟨122, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨5, by decide⟩ ⟨122, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨6, by decide⟩ ⟨122, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨7, by decide⟩ ⟨122, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨8, by decide⟩ ⟨122, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨9, by decide⟩ ⟨122, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨10, by decide⟩ ⟨122, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨11, by decide⟩ ⟨122, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨12, by decide⟩ ⟨122, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨13, by decide⟩ ⟨122, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨14, by decide⟩ ⟨122, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨15, by decide⟩ ⟨122, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨16, by decide⟩ ⟨122, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨17, by decide⟩ ⟨122, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨18, by decide⟩ ⟨122, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨19, by decide⟩ ⟨122, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨20, by decide⟩ ⟨122, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨21, by decide⟩ ⟨122, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨22, by decide⟩ ⟨122, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨23, by decide⟩ ⟨122, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨24, by decide⟩ ⟨122, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨25, by decide⟩ ⟨122, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨26, by decide⟩ ⟨122, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨27, by decide⟩ ⟨122, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨28, by decide⟩ ⟨122, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨29, by decide⟩ ⟨122, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨30, by decide⟩ ⟨122, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨31, by decide⟩ ⟨122, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨32, by decide⟩ ⟨122, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨33, by decide⟩ ⟨122, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨34, by decide⟩ ⟨122, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨35, by decide⟩ ⟨122, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨36, by decide⟩ ⟨122, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨37, by decide⟩ ⟨122, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨38, by decide⟩ ⟨122, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨39, by decide⟩ ⟨122, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨40, by decide⟩ ⟨122, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨41, by decide⟩ ⟨122, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨42, by decide⟩ ⟨122, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨43, by decide⟩ ⟨122, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨44, by decide⟩ ⟨122, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨45, by decide⟩ ⟨122, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨46, by decide⟩ ⟨122, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨47, by decide⟩ ⟨122, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨48, by decide⟩ ⟨122, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨49, by decide⟩ ⟨122, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨50, by decide⟩ ⟨122, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨51, by decide⟩ ⟨122, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨52, by decide⟩ ⟨122, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨53, by decide⟩ ⟨122, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨54, by decide⟩ ⟨122, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨55, by decide⟩ ⟨122, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨56, by decide⟩ ⟨122, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨57, by decide⟩ ⟨122, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨58, by decide⟩ ⟨122, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨59, by decide⟩ ⟨122, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨60, by decide⟩ ⟨122, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨61, by decide⟩ ⟨122, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨62, by decide⟩ ⟨122, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨63, by decide⟩ ⟨122, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨64, by decide⟩ ⟨122, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨65, by decide⟩ ⟨122, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨66, by decide⟩ ⟨122, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨67, by decide⟩ ⟨122, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨68, by decide⟩ ⟨122, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨69, by decide⟩ ⟨122, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨70, by decide⟩ ⟨122, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨71, by decide⟩ ⟨122, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨72, by decide⟩ ⟨122, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨73, by decide⟩ ⟨122, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨74, by decide⟩ ⟨122, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨75, by decide⟩ ⟨122, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨76, by decide⟩ ⟨122, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨77, by decide⟩ ⟨122, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨78, by decide⟩ ⟨122, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨79, by decide⟩ ⟨122, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨80, by decide⟩ ⟨122, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨81, by decide⟩ ⟨122, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨82, by decide⟩ ⟨122, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨83, by decide⟩ ⟨122, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨84, by decide⟩ ⟨122, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨85, by decide⟩ ⟨122, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨86, by decide⟩ ⟨122, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨87, by decide⟩ ⟨122, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨88, by decide⟩ ⟨122, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨89, by decide⟩ ⟨122, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨90, by decide⟩ ⟨122, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨91, by decide⟩ ⟨122, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨92, by decide⟩ ⟨122, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨93, by decide⟩ ⟨122, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨94, by decide⟩ ⟨122, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨95, by decide⟩ ⟨122, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨96, by decide⟩ ⟨122, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨97, by decide⟩ ⟨122, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨98, by decide⟩ ⟨122, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨99, by decide⟩ ⟨122, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨100, by decide⟩ ⟨122, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨101, by decide⟩ ⟨122, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨102, by decide⟩ ⟨122, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨103, by decide⟩ ⟨122, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨104, by decide⟩ ⟨122, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨105, by decide⟩ ⟨122, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨106, by decide⟩ ⟨122, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨107, by decide⟩ ⟨122, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨108, by decide⟩ ⟨122, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨109, by decide⟩ ⟨122, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨110, by decide⟩ ⟨122, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨111, by decide⟩ ⟨122, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨112, by decide⟩ ⟨122, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨113, by decide⟩ ⟨122, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨114, by decide⟩ ⟨122, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨115, by decide⟩ ⟨122, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_fix ⟨116, by decide⟩ ⟨122, by decide⟩ p hp j hj hq fz1_116_122 fz2_116_122
  · exact match_zero_fix ⟨117, by decide⟩ ⟨122, by decide⟩ p hp j hj hq fz1_117_122 fz2_117_122
  · exact match_zero_fix ⟨118, by decide⟩ ⟨122, by decide⟩ p hp j hj hq fz1_118_122 fz2_118_122
  · exact match_zero_fix ⟨119, by decide⟩ ⟨122, by decide⟩ p hp j hj hq fz1_119_122 fz2_119_122
  · exact match_zero_fix ⟨120, by decide⟩ ⟨122, by decide⟩ p hp j hj hq fz1_120_122 fz2_120_122
  · exact match_zero_fix ⟨121, by decide⟩ ⟨122, by decide⟩ p hp j hj hq fz1_121_122 fz2_121_122
  · exact pair_122_122 p hp hrep j hj hq
  · exact match_zero_fix ⟨123, by decide⟩ ⟨122, by decide⟩ p hp j hj hq fz1_123_122 fz2_123_122
  · exact match_zero_fix ⟨124, by decide⟩ ⟨122, by decide⟩ p hp j hj hq fz1_124_122 fz2_124_122
  · exact match_zero_fix ⟨125, by decide⟩ ⟨122, by decide⟩ p hp j hj hq fz1_125_122 fz2_125_122
  · exact match_zero_fix ⟨126, by decide⟩ ⟨122, by decide⟩ p hp j hj hq fz1_126_122 fz2_126_122
  · exact match_zero_fix ⟨127, by decide⟩ ⟨122, by decide⟩ p hp j hj hq fz1_127_122 fz2_127_122
  · exact match_zero_fix ⟨128, by decide⟩ ⟨122, by decide⟩ p hp j hj hq fz1_128_122 fz2_128_122
  · exact match_zero_fix ⟨129, by decide⟩ ⟨122, by decide⟩ p hp j hj hq fz1_129_122 fz2_129_122
  · exact match_zero_fix ⟨130, by decide⟩ ⟨122, by decide⟩ p hp j hj hq fz1_130_122 fz2_130_122
  · exact match_zero_fix ⟨131, by decide⟩ ⟨122, by decide⟩ p hp j hj hq fz1_131_122 fz2_131_122
  · exact match_zero_fix ⟨132, by decide⟩ ⟨122, by decide⟩ p hp j hj hq fz1_132_122 fz2_132_122
  · exact match_zero_fix ⟨133, by decide⟩ ⟨122, by decide⟩ p hp j hj hq fz1_133_122 fz2_133_122
  · exact match_zero_fix ⟨134, by decide⟩ ⟨122, by decide⟩ p hp j hj hq fz1_134_122 fz2_134_122
  · exact match_zero_fix ⟨135, by decide⟩ ⟨122, by decide⟩ p hp j hj hq fz1_135_122 fz2_135_122
  · exact match_zero_fix ⟨136, by decide⟩ ⟨122, by decide⟩ p hp j hj hq fz1_136_122 fz2_136_122
  · exact match_zero_fix ⟨137, by decide⟩ ⟨122, by decide⟩ p hp j hj hq fz1_137_122 fz2_137_122
  · exact match_zero_fix ⟨138, by decide⟩ ⟨122, by decide⟩ p hp j hj hq fz1_138_122 fz2_138_122
  · exact match_zero_fix ⟨139, by decide⟩ ⟨122, by decide⟩ p hp j hj hq fz1_139_122 fz2_139_122
  · exact match_zero_fix ⟨140, by decide⟩ ⟨122, by decide⟩ p hp j hj hq fz1_140_122 fz2_140_122
  · exact match_zero_fix ⟨141, by decide⟩ ⟨122, by decide⟩ p hp j hj hq fz1_141_122 fz2_141_122
  · exact match_zero_fix ⟨142, by decide⟩ ⟨122, by decide⟩ p hp j hj hq fz1_142_122 fz2_142_122
  · exact match_zero_fix ⟨143, by decide⟩ ⟨122, by decide⟩ p hp j hj hq fz1_143_122 fz2_143_122
  · exact match_zero_fix ⟨144, by decide⟩ ⟨122, by decide⟩ p hp j hj hq fz1_144_122 fz2_144_122
  · exact match_zero_fix ⟨145, by decide⟩ ⟨122, by decide⟩ p hp j hj hq fz1_145_122 fz2_145_122
  · exact match_zero_fix ⟨146, by decide⟩ ⟨122, by decide⟩ p hp j hj hq fz1_146_122 fz2_146_122
  · exact pair_147_122 p hp hrep j hj hq

theorem master_123 (p : Nat) (hp : p < (Q2.transData.getD 123 []).length)
    (hrep : (Q2.cosetIsRep.getD 123 []).getD p false = true)
    (rK : Fin 148) (j : Nat) (hj : j < (repChars.getD rK.val []).length)
    (hq : (normIsRep.getD rK.val []).getD j false = true) :
    species (Q2.reps (⟨123, by decide⟩ : Fin 148)) (colE2 ⟨123, by decide⟩ p hp)
        (rowE2 rK j hj hq)
      = species (reps (⟨123, by decide⟩ : Fin 148))
        (colE1 ⟨123, by decide⟩ p (transLenTr ⟨123, by decide⟩ p hp)) (rowE1 rK j hj) := by
  rcases rK with ⟨nK, hnK⟩; interval_cases nK
  · exact match_zero_len ⟨0, by decide⟩ ⟨123, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨1, by decide⟩ ⟨123, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨2, by decide⟩ ⟨123, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨3, by decide⟩ ⟨123, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨4, by decide⟩ ⟨123, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨5, by decide⟩ ⟨123, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨6, by decide⟩ ⟨123, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨7, by decide⟩ ⟨123, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨8, by decide⟩ ⟨123, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨9, by decide⟩ ⟨123, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨10, by decide⟩ ⟨123, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨11, by decide⟩ ⟨123, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨12, by decide⟩ ⟨123, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨13, by decide⟩ ⟨123, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨14, by decide⟩ ⟨123, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨15, by decide⟩ ⟨123, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨16, by decide⟩ ⟨123, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨17, by decide⟩ ⟨123, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨18, by decide⟩ ⟨123, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨19, by decide⟩ ⟨123, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨20, by decide⟩ ⟨123, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨21, by decide⟩ ⟨123, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨22, by decide⟩ ⟨123, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨23, by decide⟩ ⟨123, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨24, by decide⟩ ⟨123, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨25, by decide⟩ ⟨123, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨26, by decide⟩ ⟨123, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨27, by decide⟩ ⟨123, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨28, by decide⟩ ⟨123, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨29, by decide⟩ ⟨123, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨30, by decide⟩ ⟨123, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨31, by decide⟩ ⟨123, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨32, by decide⟩ ⟨123, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨33, by decide⟩ ⟨123, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨34, by decide⟩ ⟨123, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨35, by decide⟩ ⟨123, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨36, by decide⟩ ⟨123, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨37, by decide⟩ ⟨123, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨38, by decide⟩ ⟨123, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨39, by decide⟩ ⟨123, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨40, by decide⟩ ⟨123, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨41, by decide⟩ ⟨123, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨42, by decide⟩ ⟨123, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨43, by decide⟩ ⟨123, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨44, by decide⟩ ⟨123, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨45, by decide⟩ ⟨123, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨46, by decide⟩ ⟨123, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨47, by decide⟩ ⟨123, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨48, by decide⟩ ⟨123, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨49, by decide⟩ ⟨123, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨50, by decide⟩ ⟨123, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨51, by decide⟩ ⟨123, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨52, by decide⟩ ⟨123, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨53, by decide⟩ ⟨123, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨54, by decide⟩ ⟨123, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨55, by decide⟩ ⟨123, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨56, by decide⟩ ⟨123, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨57, by decide⟩ ⟨123, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨58, by decide⟩ ⟨123, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨59, by decide⟩ ⟨123, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨60, by decide⟩ ⟨123, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨61, by decide⟩ ⟨123, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨62, by decide⟩ ⟨123, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨63, by decide⟩ ⟨123, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨64, by decide⟩ ⟨123, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨65, by decide⟩ ⟨123, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨66, by decide⟩ ⟨123, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨67, by decide⟩ ⟨123, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨68, by decide⟩ ⟨123, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨69, by decide⟩ ⟨123, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨70, by decide⟩ ⟨123, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨71, by decide⟩ ⟨123, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨72, by decide⟩ ⟨123, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨73, by decide⟩ ⟨123, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨74, by decide⟩ ⟨123, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨75, by decide⟩ ⟨123, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨76, by decide⟩ ⟨123, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨77, by decide⟩ ⟨123, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨78, by decide⟩ ⟨123, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨79, by decide⟩ ⟨123, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨80, by decide⟩ ⟨123, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨81, by decide⟩ ⟨123, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨82, by decide⟩ ⟨123, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨83, by decide⟩ ⟨123, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨84, by decide⟩ ⟨123, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨85, by decide⟩ ⟨123, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨86, by decide⟩ ⟨123, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨87, by decide⟩ ⟨123, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨88, by decide⟩ ⟨123, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨89, by decide⟩ ⟨123, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨90, by decide⟩ ⟨123, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨91, by decide⟩ ⟨123, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨92, by decide⟩ ⟨123, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨93, by decide⟩ ⟨123, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨94, by decide⟩ ⟨123, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨95, by decide⟩ ⟨123, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨96, by decide⟩ ⟨123, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨97, by decide⟩ ⟨123, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨98, by decide⟩ ⟨123, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨99, by decide⟩ ⟨123, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨100, by decide⟩ ⟨123, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨101, by decide⟩ ⟨123, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨102, by decide⟩ ⟨123, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨103, by decide⟩ ⟨123, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨104, by decide⟩ ⟨123, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨105, by decide⟩ ⟨123, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨106, by decide⟩ ⟨123, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨107, by decide⟩ ⟨123, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨108, by decide⟩ ⟨123, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨109, by decide⟩ ⟨123, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨110, by decide⟩ ⟨123, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨111, by decide⟩ ⟨123, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨112, by decide⟩ ⟨123, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨113, by decide⟩ ⟨123, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨114, by decide⟩ ⟨123, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨115, by decide⟩ ⟨123, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_fix ⟨116, by decide⟩ ⟨123, by decide⟩ p hp j hj hq fz1_116_123 fz2_116_123
  · exact match_zero_fix ⟨117, by decide⟩ ⟨123, by decide⟩ p hp j hj hq fz1_117_123 fz2_117_123
  · exact match_zero_fix ⟨118, by decide⟩ ⟨123, by decide⟩ p hp j hj hq fz1_118_123 fz2_118_123
  · exact match_zero_fix ⟨119, by decide⟩ ⟨123, by decide⟩ p hp j hj hq fz1_119_123 fz2_119_123
  · exact match_zero_fix ⟨120, by decide⟩ ⟨123, by decide⟩ p hp j hj hq fz1_120_123 fz2_120_123
  · exact match_zero_fix ⟨121, by decide⟩ ⟨123, by decide⟩ p hp j hj hq fz1_121_123 fz2_121_123
  · exact match_zero_fix ⟨122, by decide⟩ ⟨123, by decide⟩ p hp j hj hq fz1_122_123 fz2_122_123
  · exact pair_123_123 p hp hrep j hj hq
  · exact match_zero_fix ⟨124, by decide⟩ ⟨123, by decide⟩ p hp j hj hq fz1_124_123 fz2_124_123
  · exact match_zero_fix ⟨125, by decide⟩ ⟨123, by decide⟩ p hp j hj hq fz1_125_123 fz2_125_123
  · exact match_zero_fix ⟨126, by decide⟩ ⟨123, by decide⟩ p hp j hj hq fz1_126_123 fz2_126_123
  · exact match_zero_fix ⟨127, by decide⟩ ⟨123, by decide⟩ p hp j hj hq fz1_127_123 fz2_127_123
  · exact match_zero_fix ⟨128, by decide⟩ ⟨123, by decide⟩ p hp j hj hq fz1_128_123 fz2_128_123
  · exact match_zero_fix ⟨129, by decide⟩ ⟨123, by decide⟩ p hp j hj hq fz1_129_123 fz2_129_123
  · exact match_zero_fix ⟨130, by decide⟩ ⟨123, by decide⟩ p hp j hj hq fz1_130_123 fz2_130_123
  · exact match_zero_fix ⟨131, by decide⟩ ⟨123, by decide⟩ p hp j hj hq fz1_131_123 fz2_131_123
  · exact match_zero_fix ⟨132, by decide⟩ ⟨123, by decide⟩ p hp j hj hq fz1_132_123 fz2_132_123
  · exact match_zero_fix ⟨133, by decide⟩ ⟨123, by decide⟩ p hp j hj hq fz1_133_123 fz2_133_123
  · exact match_zero_fix ⟨134, by decide⟩ ⟨123, by decide⟩ p hp j hj hq fz1_134_123 fz2_134_123
  · exact match_zero_fix ⟨135, by decide⟩ ⟨123, by decide⟩ p hp j hj hq fz1_135_123 fz2_135_123
  · exact match_zero_fix ⟨136, by decide⟩ ⟨123, by decide⟩ p hp j hj hq fz1_136_123 fz2_136_123
  · exact match_zero_fix ⟨137, by decide⟩ ⟨123, by decide⟩ p hp j hj hq fz1_137_123 fz2_137_123
  · exact match_zero_fix ⟨138, by decide⟩ ⟨123, by decide⟩ p hp j hj hq fz1_138_123 fz2_138_123
  · exact match_zero_fix ⟨139, by decide⟩ ⟨123, by decide⟩ p hp j hj hq fz1_139_123 fz2_139_123
  · exact match_zero_fix ⟨140, by decide⟩ ⟨123, by decide⟩ p hp j hj hq fz1_140_123 fz2_140_123
  · exact match_zero_fix ⟨141, by decide⟩ ⟨123, by decide⟩ p hp j hj hq fz1_141_123 fz2_141_123
  · exact match_zero_fix ⟨142, by decide⟩ ⟨123, by decide⟩ p hp j hj hq fz1_142_123 fz2_142_123
  · exact match_zero_fix ⟨143, by decide⟩ ⟨123, by decide⟩ p hp j hj hq fz1_143_123 fz2_143_123
  · exact match_zero_fix ⟨144, by decide⟩ ⟨123, by decide⟩ p hp j hj hq fz1_144_123 fz2_144_123
  · exact match_zero_fix ⟨145, by decide⟩ ⟨123, by decide⟩ p hp j hj hq fz1_145_123 fz2_145_123
  · exact match_zero_fix ⟨146, by decide⟩ ⟨123, by decide⟩ p hp j hj hq fz1_146_123 fz2_146_123
  · exact pair_147_123 p hp hrep j hj hq

theorem master_124 (p : Nat) (hp : p < (Q2.transData.getD 124 []).length)
    (hrep : (Q2.cosetIsRep.getD 124 []).getD p false = true)
    (rK : Fin 148) (j : Nat) (hj : j < (repChars.getD rK.val []).length)
    (hq : (normIsRep.getD rK.val []).getD j false = true) :
    species (Q2.reps (⟨124, by decide⟩ : Fin 148)) (colE2 ⟨124, by decide⟩ p hp)
        (rowE2 rK j hj hq)
      = species (reps (⟨124, by decide⟩ : Fin 148))
        (colE1 ⟨124, by decide⟩ p (transLenTr ⟨124, by decide⟩ p hp)) (rowE1 rK j hj) := by
  rcases rK with ⟨nK, hnK⟩; interval_cases nK
  · exact match_zero_len ⟨0, by decide⟩ ⟨124, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨1, by decide⟩ ⟨124, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨2, by decide⟩ ⟨124, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨3, by decide⟩ ⟨124, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨4, by decide⟩ ⟨124, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨5, by decide⟩ ⟨124, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨6, by decide⟩ ⟨124, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨7, by decide⟩ ⟨124, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨8, by decide⟩ ⟨124, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨9, by decide⟩ ⟨124, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨10, by decide⟩ ⟨124, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨11, by decide⟩ ⟨124, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨12, by decide⟩ ⟨124, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨13, by decide⟩ ⟨124, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨14, by decide⟩ ⟨124, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨15, by decide⟩ ⟨124, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨16, by decide⟩ ⟨124, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨17, by decide⟩ ⟨124, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨18, by decide⟩ ⟨124, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨19, by decide⟩ ⟨124, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨20, by decide⟩ ⟨124, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨21, by decide⟩ ⟨124, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨22, by decide⟩ ⟨124, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨23, by decide⟩ ⟨124, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨24, by decide⟩ ⟨124, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨25, by decide⟩ ⟨124, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨26, by decide⟩ ⟨124, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨27, by decide⟩ ⟨124, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨28, by decide⟩ ⟨124, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨29, by decide⟩ ⟨124, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨30, by decide⟩ ⟨124, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨31, by decide⟩ ⟨124, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨32, by decide⟩ ⟨124, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨33, by decide⟩ ⟨124, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨34, by decide⟩ ⟨124, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨35, by decide⟩ ⟨124, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨36, by decide⟩ ⟨124, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨37, by decide⟩ ⟨124, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨38, by decide⟩ ⟨124, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨39, by decide⟩ ⟨124, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨40, by decide⟩ ⟨124, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨41, by decide⟩ ⟨124, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨42, by decide⟩ ⟨124, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨43, by decide⟩ ⟨124, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨44, by decide⟩ ⟨124, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨45, by decide⟩ ⟨124, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨46, by decide⟩ ⟨124, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨47, by decide⟩ ⟨124, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨48, by decide⟩ ⟨124, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨49, by decide⟩ ⟨124, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨50, by decide⟩ ⟨124, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨51, by decide⟩ ⟨124, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨52, by decide⟩ ⟨124, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨53, by decide⟩ ⟨124, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨54, by decide⟩ ⟨124, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨55, by decide⟩ ⟨124, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨56, by decide⟩ ⟨124, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨57, by decide⟩ ⟨124, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨58, by decide⟩ ⟨124, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨59, by decide⟩ ⟨124, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨60, by decide⟩ ⟨124, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨61, by decide⟩ ⟨124, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨62, by decide⟩ ⟨124, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨63, by decide⟩ ⟨124, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨64, by decide⟩ ⟨124, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨65, by decide⟩ ⟨124, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨66, by decide⟩ ⟨124, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨67, by decide⟩ ⟨124, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨68, by decide⟩ ⟨124, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨69, by decide⟩ ⟨124, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨70, by decide⟩ ⟨124, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨71, by decide⟩ ⟨124, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨72, by decide⟩ ⟨124, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨73, by decide⟩ ⟨124, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨74, by decide⟩ ⟨124, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨75, by decide⟩ ⟨124, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨76, by decide⟩ ⟨124, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨77, by decide⟩ ⟨124, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨78, by decide⟩ ⟨124, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨79, by decide⟩ ⟨124, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨80, by decide⟩ ⟨124, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨81, by decide⟩ ⟨124, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨82, by decide⟩ ⟨124, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨83, by decide⟩ ⟨124, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨84, by decide⟩ ⟨124, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨85, by decide⟩ ⟨124, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨86, by decide⟩ ⟨124, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨87, by decide⟩ ⟨124, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨88, by decide⟩ ⟨124, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨89, by decide⟩ ⟨124, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨90, by decide⟩ ⟨124, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨91, by decide⟩ ⟨124, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨92, by decide⟩ ⟨124, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨93, by decide⟩ ⟨124, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨94, by decide⟩ ⟨124, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨95, by decide⟩ ⟨124, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨96, by decide⟩ ⟨124, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨97, by decide⟩ ⟨124, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨98, by decide⟩ ⟨124, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨99, by decide⟩ ⟨124, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨100, by decide⟩ ⟨124, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨101, by decide⟩ ⟨124, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨102, by decide⟩ ⟨124, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨103, by decide⟩ ⟨124, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨104, by decide⟩ ⟨124, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨105, by decide⟩ ⟨124, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨106, by decide⟩ ⟨124, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨107, by decide⟩ ⟨124, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨108, by decide⟩ ⟨124, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨109, by decide⟩ ⟨124, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨110, by decide⟩ ⟨124, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨111, by decide⟩ ⟨124, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨112, by decide⟩ ⟨124, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨113, by decide⟩ ⟨124, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨114, by decide⟩ ⟨124, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨115, by decide⟩ ⟨124, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_fix ⟨116, by decide⟩ ⟨124, by decide⟩ p hp j hj hq fz1_116_124 fz2_116_124
  · exact match_zero_fix ⟨117, by decide⟩ ⟨124, by decide⟩ p hp j hj hq fz1_117_124 fz2_117_124
  · exact match_zero_fix ⟨118, by decide⟩ ⟨124, by decide⟩ p hp j hj hq fz1_118_124 fz2_118_124
  · exact match_zero_fix ⟨119, by decide⟩ ⟨124, by decide⟩ p hp j hj hq fz1_119_124 fz2_119_124
  · exact match_zero_fix ⟨120, by decide⟩ ⟨124, by decide⟩ p hp j hj hq fz1_120_124 fz2_120_124
  · exact match_zero_fix ⟨121, by decide⟩ ⟨124, by decide⟩ p hp j hj hq fz1_121_124 fz2_121_124
  · exact match_zero_fix ⟨122, by decide⟩ ⟨124, by decide⟩ p hp j hj hq fz1_122_124 fz2_122_124
  · exact match_zero_fix ⟨123, by decide⟩ ⟨124, by decide⟩ p hp j hj hq fz1_123_124 fz2_123_124
  · exact pair_124_124 p hp hrep j hj hq
  · exact match_zero_fix ⟨125, by decide⟩ ⟨124, by decide⟩ p hp j hj hq fz1_125_124 fz2_125_124
  · exact match_zero_fix ⟨126, by decide⟩ ⟨124, by decide⟩ p hp j hj hq fz1_126_124 fz2_126_124
  · exact match_zero_fix ⟨127, by decide⟩ ⟨124, by decide⟩ p hp j hj hq fz1_127_124 fz2_127_124
  · exact match_zero_fix ⟨128, by decide⟩ ⟨124, by decide⟩ p hp j hj hq fz1_128_124 fz2_128_124
  · exact match_zero_fix ⟨129, by decide⟩ ⟨124, by decide⟩ p hp j hj hq fz1_129_124 fz2_129_124
  · exact match_zero_fix ⟨130, by decide⟩ ⟨124, by decide⟩ p hp j hj hq fz1_130_124 fz2_130_124
  · exact match_zero_fix ⟨131, by decide⟩ ⟨124, by decide⟩ p hp j hj hq fz1_131_124 fz2_131_124
  · exact match_zero_fix ⟨132, by decide⟩ ⟨124, by decide⟩ p hp j hj hq fz1_132_124 fz2_132_124
  · exact match_zero_fix ⟨133, by decide⟩ ⟨124, by decide⟩ p hp j hj hq fz1_133_124 fz2_133_124
  · exact match_zero_fix ⟨134, by decide⟩ ⟨124, by decide⟩ p hp j hj hq fz1_134_124 fz2_134_124
  · exact match_zero_fix ⟨135, by decide⟩ ⟨124, by decide⟩ p hp j hj hq fz1_135_124 fz2_135_124
  · exact match_zero_fix ⟨136, by decide⟩ ⟨124, by decide⟩ p hp j hj hq fz1_136_124 fz2_136_124
  · exact match_zero_fix ⟨137, by decide⟩ ⟨124, by decide⟩ p hp j hj hq fz1_137_124 fz2_137_124
  · exact match_zero_fix ⟨138, by decide⟩ ⟨124, by decide⟩ p hp j hj hq fz1_138_124 fz2_138_124
  · exact match_zero_fix ⟨139, by decide⟩ ⟨124, by decide⟩ p hp j hj hq fz1_139_124 fz2_139_124
  · exact match_zero_fix ⟨140, by decide⟩ ⟨124, by decide⟩ p hp j hj hq fz1_140_124 fz2_140_124
  · exact match_zero_fix ⟨141, by decide⟩ ⟨124, by decide⟩ p hp j hj hq fz1_141_124 fz2_141_124
  · exact match_zero_fix ⟨142, by decide⟩ ⟨124, by decide⟩ p hp j hj hq fz1_142_124 fz2_142_124
  · exact match_zero_fix ⟨143, by decide⟩ ⟨124, by decide⟩ p hp j hj hq fz1_143_124 fz2_143_124
  · exact match_zero_fix ⟨144, by decide⟩ ⟨124, by decide⟩ p hp j hj hq fz1_144_124 fz2_144_124
  · exact match_zero_fix ⟨145, by decide⟩ ⟨124, by decide⟩ p hp j hj hq fz1_145_124 fz2_145_124
  · exact match_zero_fix ⟨146, by decide⟩ ⟨124, by decide⟩ p hp j hj hq fz1_146_124 fz2_146_124
  · exact pair_147_124 p hp hrep j hj hq

theorem master_125 (p : Nat) (hp : p < (Q2.transData.getD 125 []).length)
    (hrep : (Q2.cosetIsRep.getD 125 []).getD p false = true)
    (rK : Fin 148) (j : Nat) (hj : j < (repChars.getD rK.val []).length)
    (hq : (normIsRep.getD rK.val []).getD j false = true) :
    species (Q2.reps (⟨125, by decide⟩ : Fin 148)) (colE2 ⟨125, by decide⟩ p hp)
        (rowE2 rK j hj hq)
      = species (reps (⟨125, by decide⟩ : Fin 148))
        (colE1 ⟨125, by decide⟩ p (transLenTr ⟨125, by decide⟩ p hp)) (rowE1 rK j hj) := by
  rcases rK with ⟨nK, hnK⟩; interval_cases nK
  · exact match_zero_len ⟨0, by decide⟩ ⟨125, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨1, by decide⟩ ⟨125, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨2, by decide⟩ ⟨125, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨3, by decide⟩ ⟨125, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨4, by decide⟩ ⟨125, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨5, by decide⟩ ⟨125, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨6, by decide⟩ ⟨125, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨7, by decide⟩ ⟨125, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨8, by decide⟩ ⟨125, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨9, by decide⟩ ⟨125, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨10, by decide⟩ ⟨125, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨11, by decide⟩ ⟨125, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨12, by decide⟩ ⟨125, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨13, by decide⟩ ⟨125, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨14, by decide⟩ ⟨125, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨15, by decide⟩ ⟨125, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨16, by decide⟩ ⟨125, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨17, by decide⟩ ⟨125, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨18, by decide⟩ ⟨125, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨19, by decide⟩ ⟨125, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨20, by decide⟩ ⟨125, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨21, by decide⟩ ⟨125, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨22, by decide⟩ ⟨125, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨23, by decide⟩ ⟨125, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨24, by decide⟩ ⟨125, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨25, by decide⟩ ⟨125, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨26, by decide⟩ ⟨125, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨27, by decide⟩ ⟨125, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨28, by decide⟩ ⟨125, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨29, by decide⟩ ⟨125, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨30, by decide⟩ ⟨125, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨31, by decide⟩ ⟨125, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨32, by decide⟩ ⟨125, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨33, by decide⟩ ⟨125, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨34, by decide⟩ ⟨125, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨35, by decide⟩ ⟨125, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨36, by decide⟩ ⟨125, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨37, by decide⟩ ⟨125, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨38, by decide⟩ ⟨125, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨39, by decide⟩ ⟨125, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨40, by decide⟩ ⟨125, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨41, by decide⟩ ⟨125, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨42, by decide⟩ ⟨125, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨43, by decide⟩ ⟨125, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨44, by decide⟩ ⟨125, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨45, by decide⟩ ⟨125, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨46, by decide⟩ ⟨125, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨47, by decide⟩ ⟨125, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨48, by decide⟩ ⟨125, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨49, by decide⟩ ⟨125, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨50, by decide⟩ ⟨125, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨51, by decide⟩ ⟨125, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨52, by decide⟩ ⟨125, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨53, by decide⟩ ⟨125, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨54, by decide⟩ ⟨125, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨55, by decide⟩ ⟨125, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨56, by decide⟩ ⟨125, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨57, by decide⟩ ⟨125, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨58, by decide⟩ ⟨125, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨59, by decide⟩ ⟨125, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨60, by decide⟩ ⟨125, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨61, by decide⟩ ⟨125, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨62, by decide⟩ ⟨125, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨63, by decide⟩ ⟨125, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨64, by decide⟩ ⟨125, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨65, by decide⟩ ⟨125, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨66, by decide⟩ ⟨125, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨67, by decide⟩ ⟨125, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨68, by decide⟩ ⟨125, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨69, by decide⟩ ⟨125, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨70, by decide⟩ ⟨125, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨71, by decide⟩ ⟨125, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨72, by decide⟩ ⟨125, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨73, by decide⟩ ⟨125, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨74, by decide⟩ ⟨125, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨75, by decide⟩ ⟨125, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨76, by decide⟩ ⟨125, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨77, by decide⟩ ⟨125, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨78, by decide⟩ ⟨125, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨79, by decide⟩ ⟨125, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨80, by decide⟩ ⟨125, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨81, by decide⟩ ⟨125, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨82, by decide⟩ ⟨125, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨83, by decide⟩ ⟨125, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨84, by decide⟩ ⟨125, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨85, by decide⟩ ⟨125, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨86, by decide⟩ ⟨125, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨87, by decide⟩ ⟨125, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨88, by decide⟩ ⟨125, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨89, by decide⟩ ⟨125, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨90, by decide⟩ ⟨125, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨91, by decide⟩ ⟨125, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨92, by decide⟩ ⟨125, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨93, by decide⟩ ⟨125, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨94, by decide⟩ ⟨125, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨95, by decide⟩ ⟨125, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨96, by decide⟩ ⟨125, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨97, by decide⟩ ⟨125, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨98, by decide⟩ ⟨125, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨99, by decide⟩ ⟨125, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨100, by decide⟩ ⟨125, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨101, by decide⟩ ⟨125, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨102, by decide⟩ ⟨125, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨103, by decide⟩ ⟨125, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨104, by decide⟩ ⟨125, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨105, by decide⟩ ⟨125, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨106, by decide⟩ ⟨125, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨107, by decide⟩ ⟨125, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨108, by decide⟩ ⟨125, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨109, by decide⟩ ⟨125, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨110, by decide⟩ ⟨125, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨111, by decide⟩ ⟨125, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨112, by decide⟩ ⟨125, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨113, by decide⟩ ⟨125, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨114, by decide⟩ ⟨125, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨115, by decide⟩ ⟨125, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_fix ⟨116, by decide⟩ ⟨125, by decide⟩ p hp j hj hq fz1_116_125 fz2_116_125
  · exact match_zero_fix ⟨117, by decide⟩ ⟨125, by decide⟩ p hp j hj hq fz1_117_125 fz2_117_125
  · exact match_zero_fix ⟨118, by decide⟩ ⟨125, by decide⟩ p hp j hj hq fz1_118_125 fz2_118_125
  · exact match_zero_fix ⟨119, by decide⟩ ⟨125, by decide⟩ p hp j hj hq fz1_119_125 fz2_119_125
  · exact match_zero_fix ⟨120, by decide⟩ ⟨125, by decide⟩ p hp j hj hq fz1_120_125 fz2_120_125
  · exact match_zero_fix ⟨121, by decide⟩ ⟨125, by decide⟩ p hp j hj hq fz1_121_125 fz2_121_125
  · exact match_zero_fix ⟨122, by decide⟩ ⟨125, by decide⟩ p hp j hj hq fz1_122_125 fz2_122_125
  · exact match_zero_fix ⟨123, by decide⟩ ⟨125, by decide⟩ p hp j hj hq fz1_123_125 fz2_123_125
  · exact match_zero_fix ⟨124, by decide⟩ ⟨125, by decide⟩ p hp j hj hq fz1_124_125 fz2_124_125
  · exact pair_125_125 p hp hrep j hj hq
  · exact match_zero_fix ⟨126, by decide⟩ ⟨125, by decide⟩ p hp j hj hq fz1_126_125 fz2_126_125
  · exact match_zero_fix ⟨127, by decide⟩ ⟨125, by decide⟩ p hp j hj hq fz1_127_125 fz2_127_125
  · exact match_zero_fix ⟨128, by decide⟩ ⟨125, by decide⟩ p hp j hj hq fz1_128_125 fz2_128_125
  · exact match_zero_fix ⟨129, by decide⟩ ⟨125, by decide⟩ p hp j hj hq fz1_129_125 fz2_129_125
  · exact match_zero_fix ⟨130, by decide⟩ ⟨125, by decide⟩ p hp j hj hq fz1_130_125 fz2_130_125
  · exact match_zero_fix ⟨131, by decide⟩ ⟨125, by decide⟩ p hp j hj hq fz1_131_125 fz2_131_125
  · exact match_zero_fix ⟨132, by decide⟩ ⟨125, by decide⟩ p hp j hj hq fz1_132_125 fz2_132_125
  · exact match_zero_fix ⟨133, by decide⟩ ⟨125, by decide⟩ p hp j hj hq fz1_133_125 fz2_133_125
  · exact match_zero_fix ⟨134, by decide⟩ ⟨125, by decide⟩ p hp j hj hq fz1_134_125 fz2_134_125
  · exact match_zero_fix ⟨135, by decide⟩ ⟨125, by decide⟩ p hp j hj hq fz1_135_125 fz2_135_125
  · exact match_zero_fix ⟨136, by decide⟩ ⟨125, by decide⟩ p hp j hj hq fz1_136_125 fz2_136_125
  · exact match_zero_fix ⟨137, by decide⟩ ⟨125, by decide⟩ p hp j hj hq fz1_137_125 fz2_137_125
  · exact match_zero_fix ⟨138, by decide⟩ ⟨125, by decide⟩ p hp j hj hq fz1_138_125 fz2_138_125
  · exact match_zero_fix ⟨139, by decide⟩ ⟨125, by decide⟩ p hp j hj hq fz1_139_125 fz2_139_125
  · exact match_zero_fix ⟨140, by decide⟩ ⟨125, by decide⟩ p hp j hj hq fz1_140_125 fz2_140_125
  · exact match_zero_fix ⟨141, by decide⟩ ⟨125, by decide⟩ p hp j hj hq fz1_141_125 fz2_141_125
  · exact match_zero_fix ⟨142, by decide⟩ ⟨125, by decide⟩ p hp j hj hq fz1_142_125 fz2_142_125
  · exact match_zero_fix ⟨143, by decide⟩ ⟨125, by decide⟩ p hp j hj hq fz1_143_125 fz2_143_125
  · exact match_zero_fix ⟨144, by decide⟩ ⟨125, by decide⟩ p hp j hj hq fz1_144_125 fz2_144_125
  · exact match_zero_fix ⟨145, by decide⟩ ⟨125, by decide⟩ p hp j hj hq fz1_145_125 fz2_145_125
  · exact match_zero_fix ⟨146, by decide⟩ ⟨125, by decide⟩ p hp j hj hq fz1_146_125 fz2_146_125
  · exact pair_147_125 p hp hrep j hj hq

theorem master_126 (p : Nat) (hp : p < (Q2.transData.getD 126 []).length)
    (hrep : (Q2.cosetIsRep.getD 126 []).getD p false = true)
    (rK : Fin 148) (j : Nat) (hj : j < (repChars.getD rK.val []).length)
    (hq : (normIsRep.getD rK.val []).getD j false = true) :
    species (Q2.reps (⟨126, by decide⟩ : Fin 148)) (colE2 ⟨126, by decide⟩ p hp)
        (rowE2 rK j hj hq)
      = species (reps (⟨126, by decide⟩ : Fin 148))
        (colE1 ⟨126, by decide⟩ p (transLenTr ⟨126, by decide⟩ p hp)) (rowE1 rK j hj) := by
  rcases rK with ⟨nK, hnK⟩; interval_cases nK
  · exact match_zero_len ⟨0, by decide⟩ ⟨126, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨1, by decide⟩ ⟨126, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨2, by decide⟩ ⟨126, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨3, by decide⟩ ⟨126, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨4, by decide⟩ ⟨126, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨5, by decide⟩ ⟨126, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨6, by decide⟩ ⟨126, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨7, by decide⟩ ⟨126, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨8, by decide⟩ ⟨126, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨9, by decide⟩ ⟨126, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨10, by decide⟩ ⟨126, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨11, by decide⟩ ⟨126, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨12, by decide⟩ ⟨126, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨13, by decide⟩ ⟨126, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨14, by decide⟩ ⟨126, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨15, by decide⟩ ⟨126, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨16, by decide⟩ ⟨126, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨17, by decide⟩ ⟨126, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨18, by decide⟩ ⟨126, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨19, by decide⟩ ⟨126, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨20, by decide⟩ ⟨126, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨21, by decide⟩ ⟨126, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨22, by decide⟩ ⟨126, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨23, by decide⟩ ⟨126, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨24, by decide⟩ ⟨126, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨25, by decide⟩ ⟨126, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨26, by decide⟩ ⟨126, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨27, by decide⟩ ⟨126, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨28, by decide⟩ ⟨126, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨29, by decide⟩ ⟨126, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨30, by decide⟩ ⟨126, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨31, by decide⟩ ⟨126, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨32, by decide⟩ ⟨126, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨33, by decide⟩ ⟨126, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨34, by decide⟩ ⟨126, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨35, by decide⟩ ⟨126, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨36, by decide⟩ ⟨126, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨37, by decide⟩ ⟨126, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨38, by decide⟩ ⟨126, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨39, by decide⟩ ⟨126, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨40, by decide⟩ ⟨126, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨41, by decide⟩ ⟨126, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨42, by decide⟩ ⟨126, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨43, by decide⟩ ⟨126, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨44, by decide⟩ ⟨126, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨45, by decide⟩ ⟨126, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨46, by decide⟩ ⟨126, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨47, by decide⟩ ⟨126, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨48, by decide⟩ ⟨126, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨49, by decide⟩ ⟨126, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨50, by decide⟩ ⟨126, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨51, by decide⟩ ⟨126, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨52, by decide⟩ ⟨126, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨53, by decide⟩ ⟨126, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨54, by decide⟩ ⟨126, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨55, by decide⟩ ⟨126, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨56, by decide⟩ ⟨126, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨57, by decide⟩ ⟨126, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨58, by decide⟩ ⟨126, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨59, by decide⟩ ⟨126, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨60, by decide⟩ ⟨126, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨61, by decide⟩ ⟨126, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨62, by decide⟩ ⟨126, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨63, by decide⟩ ⟨126, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨64, by decide⟩ ⟨126, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨65, by decide⟩ ⟨126, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨66, by decide⟩ ⟨126, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨67, by decide⟩ ⟨126, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨68, by decide⟩ ⟨126, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨69, by decide⟩ ⟨126, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨70, by decide⟩ ⟨126, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨71, by decide⟩ ⟨126, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨72, by decide⟩ ⟨126, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨73, by decide⟩ ⟨126, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨74, by decide⟩ ⟨126, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨75, by decide⟩ ⟨126, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨76, by decide⟩ ⟨126, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨77, by decide⟩ ⟨126, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨78, by decide⟩ ⟨126, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨79, by decide⟩ ⟨126, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨80, by decide⟩ ⟨126, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨81, by decide⟩ ⟨126, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨82, by decide⟩ ⟨126, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨83, by decide⟩ ⟨126, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨84, by decide⟩ ⟨126, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨85, by decide⟩ ⟨126, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨86, by decide⟩ ⟨126, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨87, by decide⟩ ⟨126, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨88, by decide⟩ ⟨126, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨89, by decide⟩ ⟨126, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨90, by decide⟩ ⟨126, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨91, by decide⟩ ⟨126, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨92, by decide⟩ ⟨126, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨93, by decide⟩ ⟨126, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨94, by decide⟩ ⟨126, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨95, by decide⟩ ⟨126, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨96, by decide⟩ ⟨126, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨97, by decide⟩ ⟨126, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨98, by decide⟩ ⟨126, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨99, by decide⟩ ⟨126, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨100, by decide⟩ ⟨126, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨101, by decide⟩ ⟨126, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨102, by decide⟩ ⟨126, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨103, by decide⟩ ⟨126, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨104, by decide⟩ ⟨126, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨105, by decide⟩ ⟨126, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨106, by decide⟩ ⟨126, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨107, by decide⟩ ⟨126, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨108, by decide⟩ ⟨126, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨109, by decide⟩ ⟨126, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨110, by decide⟩ ⟨126, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨111, by decide⟩ ⟨126, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨112, by decide⟩ ⟨126, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨113, by decide⟩ ⟨126, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨114, by decide⟩ ⟨126, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨115, by decide⟩ ⟨126, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_fix ⟨116, by decide⟩ ⟨126, by decide⟩ p hp j hj hq fz1_116_126 fz2_116_126
  · exact match_zero_fix ⟨117, by decide⟩ ⟨126, by decide⟩ p hp j hj hq fz1_117_126 fz2_117_126
  · exact match_zero_fix ⟨118, by decide⟩ ⟨126, by decide⟩ p hp j hj hq fz1_118_126 fz2_118_126
  · exact match_zero_fix ⟨119, by decide⟩ ⟨126, by decide⟩ p hp j hj hq fz1_119_126 fz2_119_126
  · exact match_zero_fix ⟨120, by decide⟩ ⟨126, by decide⟩ p hp j hj hq fz1_120_126 fz2_120_126
  · exact match_zero_fix ⟨121, by decide⟩ ⟨126, by decide⟩ p hp j hj hq fz1_121_126 fz2_121_126
  · exact match_zero_fix ⟨122, by decide⟩ ⟨126, by decide⟩ p hp j hj hq fz1_122_126 fz2_122_126
  · exact match_zero_fix ⟨123, by decide⟩ ⟨126, by decide⟩ p hp j hj hq fz1_123_126 fz2_123_126
  · exact match_zero_fix ⟨124, by decide⟩ ⟨126, by decide⟩ p hp j hj hq fz1_124_126 fz2_124_126
  · exact match_zero_fix ⟨125, by decide⟩ ⟨126, by decide⟩ p hp j hj hq fz1_125_126 fz2_125_126
  · exact pair_126_126 p hp hrep j hj hq
  · exact match_zero_fix ⟨127, by decide⟩ ⟨126, by decide⟩ p hp j hj hq fz1_127_126 fz2_127_126
  · exact match_zero_fix ⟨128, by decide⟩ ⟨126, by decide⟩ p hp j hj hq fz1_128_126 fz2_128_126
  · exact match_zero_fix ⟨129, by decide⟩ ⟨126, by decide⟩ p hp j hj hq fz1_129_126 fz2_129_126
  · exact match_zero_fix ⟨130, by decide⟩ ⟨126, by decide⟩ p hp j hj hq fz1_130_126 fz2_130_126
  · exact match_zero_fix ⟨131, by decide⟩ ⟨126, by decide⟩ p hp j hj hq fz1_131_126 fz2_131_126
  · exact match_zero_fix ⟨132, by decide⟩ ⟨126, by decide⟩ p hp j hj hq fz1_132_126 fz2_132_126
  · exact match_zero_fix ⟨133, by decide⟩ ⟨126, by decide⟩ p hp j hj hq fz1_133_126 fz2_133_126
  · exact match_zero_fix ⟨134, by decide⟩ ⟨126, by decide⟩ p hp j hj hq fz1_134_126 fz2_134_126
  · exact match_zero_fix ⟨135, by decide⟩ ⟨126, by decide⟩ p hp j hj hq fz1_135_126 fz2_135_126
  · exact match_zero_fix ⟨136, by decide⟩ ⟨126, by decide⟩ p hp j hj hq fz1_136_126 fz2_136_126
  · exact match_zero_fix ⟨137, by decide⟩ ⟨126, by decide⟩ p hp j hj hq fz1_137_126 fz2_137_126
  · exact match_zero_fix ⟨138, by decide⟩ ⟨126, by decide⟩ p hp j hj hq fz1_138_126 fz2_138_126
  · exact match_zero_fix ⟨139, by decide⟩ ⟨126, by decide⟩ p hp j hj hq fz1_139_126 fz2_139_126
  · exact match_zero_fix ⟨140, by decide⟩ ⟨126, by decide⟩ p hp j hj hq fz1_140_126 fz2_140_126
  · exact match_zero_fix ⟨141, by decide⟩ ⟨126, by decide⟩ p hp j hj hq fz1_141_126 fz2_141_126
  · exact match_zero_fix ⟨142, by decide⟩ ⟨126, by decide⟩ p hp j hj hq fz1_142_126 fz2_142_126
  · exact match_zero_fix ⟨143, by decide⟩ ⟨126, by decide⟩ p hp j hj hq fz1_143_126 fz2_143_126
  · exact match_zero_fix ⟨144, by decide⟩ ⟨126, by decide⟩ p hp j hj hq fz1_144_126 fz2_144_126
  · exact match_zero_fix ⟨145, by decide⟩ ⟨126, by decide⟩ p hp j hj hq fz1_145_126 fz2_145_126
  · exact match_zero_fix ⟨146, by decide⟩ ⟨126, by decide⟩ p hp j hj hq fz1_146_126 fz2_146_126
  · exact pair_147_126 p hp hrep j hj hq

theorem master_127 (p : Nat) (hp : p < (Q2.transData.getD 127 []).length)
    (hrep : (Q2.cosetIsRep.getD 127 []).getD p false = true)
    (rK : Fin 148) (j : Nat) (hj : j < (repChars.getD rK.val []).length)
    (hq : (normIsRep.getD rK.val []).getD j false = true) :
    species (Q2.reps (⟨127, by decide⟩ : Fin 148)) (colE2 ⟨127, by decide⟩ p hp)
        (rowE2 rK j hj hq)
      = species (reps (⟨127, by decide⟩ : Fin 148))
        (colE1 ⟨127, by decide⟩ p (transLenTr ⟨127, by decide⟩ p hp)) (rowE1 rK j hj) := by
  rcases rK with ⟨nK, hnK⟩; interval_cases nK
  · exact match_zero_len ⟨0, by decide⟩ ⟨127, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨1, by decide⟩ ⟨127, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨2, by decide⟩ ⟨127, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨3, by decide⟩ ⟨127, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨4, by decide⟩ ⟨127, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨5, by decide⟩ ⟨127, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨6, by decide⟩ ⟨127, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨7, by decide⟩ ⟨127, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨8, by decide⟩ ⟨127, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨9, by decide⟩ ⟨127, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨10, by decide⟩ ⟨127, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨11, by decide⟩ ⟨127, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨12, by decide⟩ ⟨127, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨13, by decide⟩ ⟨127, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨14, by decide⟩ ⟨127, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨15, by decide⟩ ⟨127, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨16, by decide⟩ ⟨127, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨17, by decide⟩ ⟨127, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨18, by decide⟩ ⟨127, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨19, by decide⟩ ⟨127, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨20, by decide⟩ ⟨127, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨21, by decide⟩ ⟨127, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨22, by decide⟩ ⟨127, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨23, by decide⟩ ⟨127, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨24, by decide⟩ ⟨127, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨25, by decide⟩ ⟨127, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨26, by decide⟩ ⟨127, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨27, by decide⟩ ⟨127, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨28, by decide⟩ ⟨127, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨29, by decide⟩ ⟨127, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨30, by decide⟩ ⟨127, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨31, by decide⟩ ⟨127, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨32, by decide⟩ ⟨127, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨33, by decide⟩ ⟨127, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨34, by decide⟩ ⟨127, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨35, by decide⟩ ⟨127, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨36, by decide⟩ ⟨127, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨37, by decide⟩ ⟨127, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨38, by decide⟩ ⟨127, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨39, by decide⟩ ⟨127, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨40, by decide⟩ ⟨127, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨41, by decide⟩ ⟨127, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨42, by decide⟩ ⟨127, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨43, by decide⟩ ⟨127, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨44, by decide⟩ ⟨127, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨45, by decide⟩ ⟨127, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨46, by decide⟩ ⟨127, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨47, by decide⟩ ⟨127, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨48, by decide⟩ ⟨127, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨49, by decide⟩ ⟨127, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨50, by decide⟩ ⟨127, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨51, by decide⟩ ⟨127, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨52, by decide⟩ ⟨127, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨53, by decide⟩ ⟨127, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨54, by decide⟩ ⟨127, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨55, by decide⟩ ⟨127, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨56, by decide⟩ ⟨127, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨57, by decide⟩ ⟨127, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨58, by decide⟩ ⟨127, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨59, by decide⟩ ⟨127, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨60, by decide⟩ ⟨127, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨61, by decide⟩ ⟨127, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨62, by decide⟩ ⟨127, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨63, by decide⟩ ⟨127, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨64, by decide⟩ ⟨127, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨65, by decide⟩ ⟨127, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨66, by decide⟩ ⟨127, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨67, by decide⟩ ⟨127, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨68, by decide⟩ ⟨127, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨69, by decide⟩ ⟨127, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨70, by decide⟩ ⟨127, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨71, by decide⟩ ⟨127, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨72, by decide⟩ ⟨127, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨73, by decide⟩ ⟨127, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨74, by decide⟩ ⟨127, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨75, by decide⟩ ⟨127, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨76, by decide⟩ ⟨127, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨77, by decide⟩ ⟨127, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨78, by decide⟩ ⟨127, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨79, by decide⟩ ⟨127, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨80, by decide⟩ ⟨127, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨81, by decide⟩ ⟨127, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨82, by decide⟩ ⟨127, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨83, by decide⟩ ⟨127, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨84, by decide⟩ ⟨127, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨85, by decide⟩ ⟨127, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨86, by decide⟩ ⟨127, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨87, by decide⟩ ⟨127, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨88, by decide⟩ ⟨127, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨89, by decide⟩ ⟨127, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨90, by decide⟩ ⟨127, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨91, by decide⟩ ⟨127, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨92, by decide⟩ ⟨127, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨93, by decide⟩ ⟨127, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨94, by decide⟩ ⟨127, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨95, by decide⟩ ⟨127, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨96, by decide⟩ ⟨127, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨97, by decide⟩ ⟨127, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨98, by decide⟩ ⟨127, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨99, by decide⟩ ⟨127, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨100, by decide⟩ ⟨127, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨101, by decide⟩ ⟨127, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨102, by decide⟩ ⟨127, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨103, by decide⟩ ⟨127, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨104, by decide⟩ ⟨127, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨105, by decide⟩ ⟨127, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨106, by decide⟩ ⟨127, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨107, by decide⟩ ⟨127, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨108, by decide⟩ ⟨127, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨109, by decide⟩ ⟨127, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨110, by decide⟩ ⟨127, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨111, by decide⟩ ⟨127, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨112, by decide⟩ ⟨127, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨113, by decide⟩ ⟨127, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨114, by decide⟩ ⟨127, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨115, by decide⟩ ⟨127, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_fix ⟨116, by decide⟩ ⟨127, by decide⟩ p hp j hj hq fz1_116_127 fz2_116_127
  · exact match_zero_fix ⟨117, by decide⟩ ⟨127, by decide⟩ p hp j hj hq fz1_117_127 fz2_117_127
  · exact match_zero_fix ⟨118, by decide⟩ ⟨127, by decide⟩ p hp j hj hq fz1_118_127 fz2_118_127
  · exact match_zero_fix ⟨119, by decide⟩ ⟨127, by decide⟩ p hp j hj hq fz1_119_127 fz2_119_127
  · exact match_zero_fix ⟨120, by decide⟩ ⟨127, by decide⟩ p hp j hj hq fz1_120_127 fz2_120_127
  · exact match_zero_fix ⟨121, by decide⟩ ⟨127, by decide⟩ p hp j hj hq fz1_121_127 fz2_121_127
  · exact match_zero_fix ⟨122, by decide⟩ ⟨127, by decide⟩ p hp j hj hq fz1_122_127 fz2_122_127
  · exact match_zero_fix ⟨123, by decide⟩ ⟨127, by decide⟩ p hp j hj hq fz1_123_127 fz2_123_127
  · exact match_zero_fix ⟨124, by decide⟩ ⟨127, by decide⟩ p hp j hj hq fz1_124_127 fz2_124_127
  · exact match_zero_fix ⟨125, by decide⟩ ⟨127, by decide⟩ p hp j hj hq fz1_125_127 fz2_125_127
  · exact match_zero_fix ⟨126, by decide⟩ ⟨127, by decide⟩ p hp j hj hq fz1_126_127 fz2_126_127
  · exact pair_127_127 p hp hrep j hj hq
  · exact match_zero_fix ⟨128, by decide⟩ ⟨127, by decide⟩ p hp j hj hq fz1_128_127 fz2_128_127
  · exact match_zero_fix ⟨129, by decide⟩ ⟨127, by decide⟩ p hp j hj hq fz1_129_127 fz2_129_127
  · exact match_zero_fix ⟨130, by decide⟩ ⟨127, by decide⟩ p hp j hj hq fz1_130_127 fz2_130_127
  · exact match_zero_fix ⟨131, by decide⟩ ⟨127, by decide⟩ p hp j hj hq fz1_131_127 fz2_131_127
  · exact match_zero_fix ⟨132, by decide⟩ ⟨127, by decide⟩ p hp j hj hq fz1_132_127 fz2_132_127
  · exact match_zero_fix ⟨133, by decide⟩ ⟨127, by decide⟩ p hp j hj hq fz1_133_127 fz2_133_127
  · exact match_zero_fix ⟨134, by decide⟩ ⟨127, by decide⟩ p hp j hj hq fz1_134_127 fz2_134_127
  · exact match_zero_fix ⟨135, by decide⟩ ⟨127, by decide⟩ p hp j hj hq fz1_135_127 fz2_135_127
  · exact match_zero_fix ⟨136, by decide⟩ ⟨127, by decide⟩ p hp j hj hq fz1_136_127 fz2_136_127
  · exact match_zero_fix ⟨137, by decide⟩ ⟨127, by decide⟩ p hp j hj hq fz1_137_127 fz2_137_127
  · exact match_zero_fix ⟨138, by decide⟩ ⟨127, by decide⟩ p hp j hj hq fz1_138_127 fz2_138_127
  · exact match_zero_fix ⟨139, by decide⟩ ⟨127, by decide⟩ p hp j hj hq fz1_139_127 fz2_139_127
  · exact match_zero_fix ⟨140, by decide⟩ ⟨127, by decide⟩ p hp j hj hq fz1_140_127 fz2_140_127
  · exact match_zero_fix ⟨141, by decide⟩ ⟨127, by decide⟩ p hp j hj hq fz1_141_127 fz2_141_127
  · exact match_zero_fix ⟨142, by decide⟩ ⟨127, by decide⟩ p hp j hj hq fz1_142_127 fz2_142_127
  · exact match_zero_fix ⟨143, by decide⟩ ⟨127, by decide⟩ p hp j hj hq fz1_143_127 fz2_143_127
  · exact match_zero_fix ⟨144, by decide⟩ ⟨127, by decide⟩ p hp j hj hq fz1_144_127 fz2_144_127
  · exact match_zero_fix ⟨145, by decide⟩ ⟨127, by decide⟩ p hp j hj hq fz1_145_127 fz2_145_127
  · exact match_zero_fix ⟨146, by decide⟩ ⟨127, by decide⟩ p hp j hj hq fz1_146_127 fz2_146_127
  · exact pair_147_127 p hp hrep j hj hq

end LeanDring.P5Presentation
