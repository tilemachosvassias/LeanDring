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
import LeanDring.P5.Data.MatchPair.C008
import LeanDring.P5.Data.MatchPair.C009

/-! # Stage-5 per-column-class master theorems, chunk 16 (auto-emitted).  -/

namespace LeanDring.P5Presentation

open MulAction Finset LeanDring.DRing LeanDring.MonGSet

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.style.longLine false

theorem master_128 (p : Nat) (hp : p < (Q2.transData.getD 128 []).length)
    (hrep : (Q2.cosetIsRep.getD 128 []).getD p false = true)
    (rK : Fin 148) (j : Nat) (hj : j < (repChars.getD rK.val []).length)
    (hq : (normIsRep.getD rK.val []).getD j false = true) :
    species (Q2.reps (⟨128, by decide⟩ : Fin 148)) (colE2 ⟨128, by decide⟩ p hp)
        (rowE2 rK j hj hq)
      = species (reps (⟨128, by decide⟩ : Fin 148))
        (colE1 ⟨128, by decide⟩ p (transLenTr ⟨128, by decide⟩ p hp)) (rowE1 rK j hj) := by
  rcases rK with ⟨nK, hnK⟩; interval_cases nK
  · exact match_zero_len ⟨0, by decide⟩ ⟨128, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨1, by decide⟩ ⟨128, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨2, by decide⟩ ⟨128, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨3, by decide⟩ ⟨128, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨4, by decide⟩ ⟨128, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨5, by decide⟩ ⟨128, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨6, by decide⟩ ⟨128, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨7, by decide⟩ ⟨128, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨8, by decide⟩ ⟨128, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨9, by decide⟩ ⟨128, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨10, by decide⟩ ⟨128, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨11, by decide⟩ ⟨128, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨12, by decide⟩ ⟨128, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨13, by decide⟩ ⟨128, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨14, by decide⟩ ⟨128, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨15, by decide⟩ ⟨128, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨16, by decide⟩ ⟨128, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨17, by decide⟩ ⟨128, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨18, by decide⟩ ⟨128, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨19, by decide⟩ ⟨128, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨20, by decide⟩ ⟨128, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨21, by decide⟩ ⟨128, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨22, by decide⟩ ⟨128, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨23, by decide⟩ ⟨128, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨24, by decide⟩ ⟨128, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨25, by decide⟩ ⟨128, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨26, by decide⟩ ⟨128, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨27, by decide⟩ ⟨128, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨28, by decide⟩ ⟨128, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨29, by decide⟩ ⟨128, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨30, by decide⟩ ⟨128, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨31, by decide⟩ ⟨128, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨32, by decide⟩ ⟨128, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨33, by decide⟩ ⟨128, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨34, by decide⟩ ⟨128, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨35, by decide⟩ ⟨128, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨36, by decide⟩ ⟨128, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨37, by decide⟩ ⟨128, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨38, by decide⟩ ⟨128, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨39, by decide⟩ ⟨128, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨40, by decide⟩ ⟨128, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨41, by decide⟩ ⟨128, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨42, by decide⟩ ⟨128, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨43, by decide⟩ ⟨128, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨44, by decide⟩ ⟨128, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨45, by decide⟩ ⟨128, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨46, by decide⟩ ⟨128, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨47, by decide⟩ ⟨128, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨48, by decide⟩ ⟨128, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨49, by decide⟩ ⟨128, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨50, by decide⟩ ⟨128, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨51, by decide⟩ ⟨128, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨52, by decide⟩ ⟨128, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨53, by decide⟩ ⟨128, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨54, by decide⟩ ⟨128, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨55, by decide⟩ ⟨128, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨56, by decide⟩ ⟨128, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨57, by decide⟩ ⟨128, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨58, by decide⟩ ⟨128, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨59, by decide⟩ ⟨128, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨60, by decide⟩ ⟨128, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨61, by decide⟩ ⟨128, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨62, by decide⟩ ⟨128, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨63, by decide⟩ ⟨128, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨64, by decide⟩ ⟨128, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨65, by decide⟩ ⟨128, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨66, by decide⟩ ⟨128, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨67, by decide⟩ ⟨128, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨68, by decide⟩ ⟨128, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨69, by decide⟩ ⟨128, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨70, by decide⟩ ⟨128, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨71, by decide⟩ ⟨128, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨72, by decide⟩ ⟨128, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨73, by decide⟩ ⟨128, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨74, by decide⟩ ⟨128, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨75, by decide⟩ ⟨128, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨76, by decide⟩ ⟨128, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨77, by decide⟩ ⟨128, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨78, by decide⟩ ⟨128, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨79, by decide⟩ ⟨128, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨80, by decide⟩ ⟨128, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨81, by decide⟩ ⟨128, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨82, by decide⟩ ⟨128, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨83, by decide⟩ ⟨128, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨84, by decide⟩ ⟨128, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨85, by decide⟩ ⟨128, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨86, by decide⟩ ⟨128, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨87, by decide⟩ ⟨128, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨88, by decide⟩ ⟨128, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨89, by decide⟩ ⟨128, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨90, by decide⟩ ⟨128, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨91, by decide⟩ ⟨128, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨92, by decide⟩ ⟨128, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨93, by decide⟩ ⟨128, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨94, by decide⟩ ⟨128, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨95, by decide⟩ ⟨128, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨96, by decide⟩ ⟨128, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨97, by decide⟩ ⟨128, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨98, by decide⟩ ⟨128, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨99, by decide⟩ ⟨128, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨100, by decide⟩ ⟨128, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨101, by decide⟩ ⟨128, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨102, by decide⟩ ⟨128, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨103, by decide⟩ ⟨128, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨104, by decide⟩ ⟨128, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨105, by decide⟩ ⟨128, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨106, by decide⟩ ⟨128, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨107, by decide⟩ ⟨128, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨108, by decide⟩ ⟨128, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨109, by decide⟩ ⟨128, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨110, by decide⟩ ⟨128, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨111, by decide⟩ ⟨128, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨112, by decide⟩ ⟨128, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨113, by decide⟩ ⟨128, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨114, by decide⟩ ⟨128, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨115, by decide⟩ ⟨128, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_fix ⟨116, by decide⟩ ⟨128, by decide⟩ p hp j hj hq fz1_116_128 fz2_116_128
  · exact match_zero_fix ⟨117, by decide⟩ ⟨128, by decide⟩ p hp j hj hq fz1_117_128 fz2_117_128
  · exact match_zero_fix ⟨118, by decide⟩ ⟨128, by decide⟩ p hp j hj hq fz1_118_128 fz2_118_128
  · exact match_zero_fix ⟨119, by decide⟩ ⟨128, by decide⟩ p hp j hj hq fz1_119_128 fz2_119_128
  · exact match_zero_fix ⟨120, by decide⟩ ⟨128, by decide⟩ p hp j hj hq fz1_120_128 fz2_120_128
  · exact match_zero_fix ⟨121, by decide⟩ ⟨128, by decide⟩ p hp j hj hq fz1_121_128 fz2_121_128
  · exact match_zero_fix ⟨122, by decide⟩ ⟨128, by decide⟩ p hp j hj hq fz1_122_128 fz2_122_128
  · exact match_zero_fix ⟨123, by decide⟩ ⟨128, by decide⟩ p hp j hj hq fz1_123_128 fz2_123_128
  · exact match_zero_fix ⟨124, by decide⟩ ⟨128, by decide⟩ p hp j hj hq fz1_124_128 fz2_124_128
  · exact match_zero_fix ⟨125, by decide⟩ ⟨128, by decide⟩ p hp j hj hq fz1_125_128 fz2_125_128
  · exact match_zero_fix ⟨126, by decide⟩ ⟨128, by decide⟩ p hp j hj hq fz1_126_128 fz2_126_128
  · exact match_zero_fix ⟨127, by decide⟩ ⟨128, by decide⟩ p hp j hj hq fz1_127_128 fz2_127_128
  · exact pair_128_128 p hp hrep j hj hq
  · exact match_zero_fix ⟨129, by decide⟩ ⟨128, by decide⟩ p hp j hj hq fz1_129_128 fz2_129_128
  · exact match_zero_fix ⟨130, by decide⟩ ⟨128, by decide⟩ p hp j hj hq fz1_130_128 fz2_130_128
  · exact match_zero_fix ⟨131, by decide⟩ ⟨128, by decide⟩ p hp j hj hq fz1_131_128 fz2_131_128
  · exact match_zero_fix ⟨132, by decide⟩ ⟨128, by decide⟩ p hp j hj hq fz1_132_128 fz2_132_128
  · exact match_zero_fix ⟨133, by decide⟩ ⟨128, by decide⟩ p hp j hj hq fz1_133_128 fz2_133_128
  · exact match_zero_fix ⟨134, by decide⟩ ⟨128, by decide⟩ p hp j hj hq fz1_134_128 fz2_134_128
  · exact match_zero_fix ⟨135, by decide⟩ ⟨128, by decide⟩ p hp j hj hq fz1_135_128 fz2_135_128
  · exact match_zero_fix ⟨136, by decide⟩ ⟨128, by decide⟩ p hp j hj hq fz1_136_128 fz2_136_128
  · exact match_zero_fix ⟨137, by decide⟩ ⟨128, by decide⟩ p hp j hj hq fz1_137_128 fz2_137_128
  · exact match_zero_fix ⟨138, by decide⟩ ⟨128, by decide⟩ p hp j hj hq fz1_138_128 fz2_138_128
  · exact match_zero_fix ⟨139, by decide⟩ ⟨128, by decide⟩ p hp j hj hq fz1_139_128 fz2_139_128
  · exact match_zero_fix ⟨140, by decide⟩ ⟨128, by decide⟩ p hp j hj hq fz1_140_128 fz2_140_128
  · exact match_zero_fix ⟨141, by decide⟩ ⟨128, by decide⟩ p hp j hj hq fz1_141_128 fz2_141_128
  · exact match_zero_fix ⟨142, by decide⟩ ⟨128, by decide⟩ p hp j hj hq fz1_142_128 fz2_142_128
  · exact match_zero_fix ⟨143, by decide⟩ ⟨128, by decide⟩ p hp j hj hq fz1_143_128 fz2_143_128
  · exact match_zero_fix ⟨144, by decide⟩ ⟨128, by decide⟩ p hp j hj hq fz1_144_128 fz2_144_128
  · exact match_zero_fix ⟨145, by decide⟩ ⟨128, by decide⟩ p hp j hj hq fz1_145_128 fz2_145_128
  · exact match_zero_fix ⟨146, by decide⟩ ⟨128, by decide⟩ p hp j hj hq fz1_146_128 fz2_146_128
  · exact pair_147_128 p hp hrep j hj hq

theorem master_129 (p : Nat) (hp : p < (Q2.transData.getD 129 []).length)
    (hrep : (Q2.cosetIsRep.getD 129 []).getD p false = true)
    (rK : Fin 148) (j : Nat) (hj : j < (repChars.getD rK.val []).length)
    (hq : (normIsRep.getD rK.val []).getD j false = true) :
    species (Q2.reps (⟨129, by decide⟩ : Fin 148)) (colE2 ⟨129, by decide⟩ p hp)
        (rowE2 rK j hj hq)
      = species (reps (⟨129, by decide⟩ : Fin 148))
        (colE1 ⟨129, by decide⟩ p (transLenTr ⟨129, by decide⟩ p hp)) (rowE1 rK j hj) := by
  rcases rK with ⟨nK, hnK⟩; interval_cases nK
  · exact match_zero_len ⟨0, by decide⟩ ⟨129, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨1, by decide⟩ ⟨129, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨2, by decide⟩ ⟨129, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨3, by decide⟩ ⟨129, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨4, by decide⟩ ⟨129, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨5, by decide⟩ ⟨129, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨6, by decide⟩ ⟨129, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨7, by decide⟩ ⟨129, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨8, by decide⟩ ⟨129, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨9, by decide⟩ ⟨129, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨10, by decide⟩ ⟨129, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨11, by decide⟩ ⟨129, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨12, by decide⟩ ⟨129, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨13, by decide⟩ ⟨129, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨14, by decide⟩ ⟨129, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨15, by decide⟩ ⟨129, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨16, by decide⟩ ⟨129, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨17, by decide⟩ ⟨129, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨18, by decide⟩ ⟨129, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨19, by decide⟩ ⟨129, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨20, by decide⟩ ⟨129, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨21, by decide⟩ ⟨129, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨22, by decide⟩ ⟨129, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨23, by decide⟩ ⟨129, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨24, by decide⟩ ⟨129, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨25, by decide⟩ ⟨129, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨26, by decide⟩ ⟨129, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨27, by decide⟩ ⟨129, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨28, by decide⟩ ⟨129, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨29, by decide⟩ ⟨129, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨30, by decide⟩ ⟨129, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨31, by decide⟩ ⟨129, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨32, by decide⟩ ⟨129, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨33, by decide⟩ ⟨129, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨34, by decide⟩ ⟨129, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨35, by decide⟩ ⟨129, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨36, by decide⟩ ⟨129, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨37, by decide⟩ ⟨129, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨38, by decide⟩ ⟨129, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨39, by decide⟩ ⟨129, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨40, by decide⟩ ⟨129, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨41, by decide⟩ ⟨129, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨42, by decide⟩ ⟨129, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨43, by decide⟩ ⟨129, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨44, by decide⟩ ⟨129, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨45, by decide⟩ ⟨129, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨46, by decide⟩ ⟨129, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨47, by decide⟩ ⟨129, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨48, by decide⟩ ⟨129, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨49, by decide⟩ ⟨129, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨50, by decide⟩ ⟨129, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨51, by decide⟩ ⟨129, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨52, by decide⟩ ⟨129, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨53, by decide⟩ ⟨129, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨54, by decide⟩ ⟨129, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨55, by decide⟩ ⟨129, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨56, by decide⟩ ⟨129, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨57, by decide⟩ ⟨129, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨58, by decide⟩ ⟨129, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨59, by decide⟩ ⟨129, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨60, by decide⟩ ⟨129, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨61, by decide⟩ ⟨129, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨62, by decide⟩ ⟨129, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨63, by decide⟩ ⟨129, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨64, by decide⟩ ⟨129, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨65, by decide⟩ ⟨129, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨66, by decide⟩ ⟨129, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨67, by decide⟩ ⟨129, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨68, by decide⟩ ⟨129, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨69, by decide⟩ ⟨129, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨70, by decide⟩ ⟨129, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨71, by decide⟩ ⟨129, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨72, by decide⟩ ⟨129, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨73, by decide⟩ ⟨129, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨74, by decide⟩ ⟨129, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨75, by decide⟩ ⟨129, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨76, by decide⟩ ⟨129, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨77, by decide⟩ ⟨129, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨78, by decide⟩ ⟨129, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨79, by decide⟩ ⟨129, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨80, by decide⟩ ⟨129, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨81, by decide⟩ ⟨129, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨82, by decide⟩ ⟨129, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨83, by decide⟩ ⟨129, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨84, by decide⟩ ⟨129, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨85, by decide⟩ ⟨129, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨86, by decide⟩ ⟨129, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨87, by decide⟩ ⟨129, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨88, by decide⟩ ⟨129, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨89, by decide⟩ ⟨129, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨90, by decide⟩ ⟨129, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨91, by decide⟩ ⟨129, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨92, by decide⟩ ⟨129, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨93, by decide⟩ ⟨129, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨94, by decide⟩ ⟨129, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨95, by decide⟩ ⟨129, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨96, by decide⟩ ⟨129, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨97, by decide⟩ ⟨129, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨98, by decide⟩ ⟨129, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨99, by decide⟩ ⟨129, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨100, by decide⟩ ⟨129, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨101, by decide⟩ ⟨129, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨102, by decide⟩ ⟨129, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨103, by decide⟩ ⟨129, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨104, by decide⟩ ⟨129, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨105, by decide⟩ ⟨129, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨106, by decide⟩ ⟨129, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨107, by decide⟩ ⟨129, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨108, by decide⟩ ⟨129, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨109, by decide⟩ ⟨129, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨110, by decide⟩ ⟨129, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨111, by decide⟩ ⟨129, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨112, by decide⟩ ⟨129, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨113, by decide⟩ ⟨129, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨114, by decide⟩ ⟨129, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨115, by decide⟩ ⟨129, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_fix ⟨116, by decide⟩ ⟨129, by decide⟩ p hp j hj hq fz1_116_129 fz2_116_129
  · exact match_zero_fix ⟨117, by decide⟩ ⟨129, by decide⟩ p hp j hj hq fz1_117_129 fz2_117_129
  · exact match_zero_fix ⟨118, by decide⟩ ⟨129, by decide⟩ p hp j hj hq fz1_118_129 fz2_118_129
  · exact match_zero_fix ⟨119, by decide⟩ ⟨129, by decide⟩ p hp j hj hq fz1_119_129 fz2_119_129
  · exact match_zero_fix ⟨120, by decide⟩ ⟨129, by decide⟩ p hp j hj hq fz1_120_129 fz2_120_129
  · exact match_zero_fix ⟨121, by decide⟩ ⟨129, by decide⟩ p hp j hj hq fz1_121_129 fz2_121_129
  · exact match_zero_fix ⟨122, by decide⟩ ⟨129, by decide⟩ p hp j hj hq fz1_122_129 fz2_122_129
  · exact match_zero_fix ⟨123, by decide⟩ ⟨129, by decide⟩ p hp j hj hq fz1_123_129 fz2_123_129
  · exact match_zero_fix ⟨124, by decide⟩ ⟨129, by decide⟩ p hp j hj hq fz1_124_129 fz2_124_129
  · exact match_zero_fix ⟨125, by decide⟩ ⟨129, by decide⟩ p hp j hj hq fz1_125_129 fz2_125_129
  · exact match_zero_fix ⟨126, by decide⟩ ⟨129, by decide⟩ p hp j hj hq fz1_126_129 fz2_126_129
  · exact match_zero_fix ⟨127, by decide⟩ ⟨129, by decide⟩ p hp j hj hq fz1_127_129 fz2_127_129
  · exact match_zero_fix ⟨128, by decide⟩ ⟨129, by decide⟩ p hp j hj hq fz1_128_129 fz2_128_129
  · exact pair_129_129 p hp hrep j hj hq
  · exact match_zero_fix ⟨130, by decide⟩ ⟨129, by decide⟩ p hp j hj hq fz1_130_129 fz2_130_129
  · exact match_zero_fix ⟨131, by decide⟩ ⟨129, by decide⟩ p hp j hj hq fz1_131_129 fz2_131_129
  · exact match_zero_fix ⟨132, by decide⟩ ⟨129, by decide⟩ p hp j hj hq fz1_132_129 fz2_132_129
  · exact match_zero_fix ⟨133, by decide⟩ ⟨129, by decide⟩ p hp j hj hq fz1_133_129 fz2_133_129
  · exact match_zero_fix ⟨134, by decide⟩ ⟨129, by decide⟩ p hp j hj hq fz1_134_129 fz2_134_129
  · exact match_zero_fix ⟨135, by decide⟩ ⟨129, by decide⟩ p hp j hj hq fz1_135_129 fz2_135_129
  · exact match_zero_fix ⟨136, by decide⟩ ⟨129, by decide⟩ p hp j hj hq fz1_136_129 fz2_136_129
  · exact match_zero_fix ⟨137, by decide⟩ ⟨129, by decide⟩ p hp j hj hq fz1_137_129 fz2_137_129
  · exact match_zero_fix ⟨138, by decide⟩ ⟨129, by decide⟩ p hp j hj hq fz1_138_129 fz2_138_129
  · exact match_zero_fix ⟨139, by decide⟩ ⟨129, by decide⟩ p hp j hj hq fz1_139_129 fz2_139_129
  · exact match_zero_fix ⟨140, by decide⟩ ⟨129, by decide⟩ p hp j hj hq fz1_140_129 fz2_140_129
  · exact match_zero_fix ⟨141, by decide⟩ ⟨129, by decide⟩ p hp j hj hq fz1_141_129 fz2_141_129
  · exact match_zero_fix ⟨142, by decide⟩ ⟨129, by decide⟩ p hp j hj hq fz1_142_129 fz2_142_129
  · exact match_zero_fix ⟨143, by decide⟩ ⟨129, by decide⟩ p hp j hj hq fz1_143_129 fz2_143_129
  · exact match_zero_fix ⟨144, by decide⟩ ⟨129, by decide⟩ p hp j hj hq fz1_144_129 fz2_144_129
  · exact match_zero_fix ⟨145, by decide⟩ ⟨129, by decide⟩ p hp j hj hq fz1_145_129 fz2_145_129
  · exact match_zero_fix ⟨146, by decide⟩ ⟨129, by decide⟩ p hp j hj hq fz1_146_129 fz2_146_129
  · exact pair_147_129 p hp hrep j hj hq

theorem master_130 (p : Nat) (hp : p < (Q2.transData.getD 130 []).length)
    (hrep : (Q2.cosetIsRep.getD 130 []).getD p false = true)
    (rK : Fin 148) (j : Nat) (hj : j < (repChars.getD rK.val []).length)
    (hq : (normIsRep.getD rK.val []).getD j false = true) :
    species (Q2.reps (⟨130, by decide⟩ : Fin 148)) (colE2 ⟨130, by decide⟩ p hp)
        (rowE2 rK j hj hq)
      = species (reps (⟨130, by decide⟩ : Fin 148))
        (colE1 ⟨130, by decide⟩ p (transLenTr ⟨130, by decide⟩ p hp)) (rowE1 rK j hj) := by
  rcases rK with ⟨nK, hnK⟩; interval_cases nK
  · exact match_zero_len ⟨0, by decide⟩ ⟨130, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨1, by decide⟩ ⟨130, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨2, by decide⟩ ⟨130, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨3, by decide⟩ ⟨130, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨4, by decide⟩ ⟨130, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨5, by decide⟩ ⟨130, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨6, by decide⟩ ⟨130, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨7, by decide⟩ ⟨130, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨8, by decide⟩ ⟨130, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨9, by decide⟩ ⟨130, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨10, by decide⟩ ⟨130, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨11, by decide⟩ ⟨130, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨12, by decide⟩ ⟨130, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨13, by decide⟩ ⟨130, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨14, by decide⟩ ⟨130, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨15, by decide⟩ ⟨130, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨16, by decide⟩ ⟨130, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨17, by decide⟩ ⟨130, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨18, by decide⟩ ⟨130, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨19, by decide⟩ ⟨130, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨20, by decide⟩ ⟨130, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨21, by decide⟩ ⟨130, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨22, by decide⟩ ⟨130, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨23, by decide⟩ ⟨130, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨24, by decide⟩ ⟨130, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨25, by decide⟩ ⟨130, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨26, by decide⟩ ⟨130, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨27, by decide⟩ ⟨130, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨28, by decide⟩ ⟨130, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨29, by decide⟩ ⟨130, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨30, by decide⟩ ⟨130, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨31, by decide⟩ ⟨130, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨32, by decide⟩ ⟨130, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨33, by decide⟩ ⟨130, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨34, by decide⟩ ⟨130, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨35, by decide⟩ ⟨130, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨36, by decide⟩ ⟨130, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨37, by decide⟩ ⟨130, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨38, by decide⟩ ⟨130, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨39, by decide⟩ ⟨130, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨40, by decide⟩ ⟨130, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨41, by decide⟩ ⟨130, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨42, by decide⟩ ⟨130, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨43, by decide⟩ ⟨130, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨44, by decide⟩ ⟨130, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨45, by decide⟩ ⟨130, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨46, by decide⟩ ⟨130, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨47, by decide⟩ ⟨130, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨48, by decide⟩ ⟨130, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨49, by decide⟩ ⟨130, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨50, by decide⟩ ⟨130, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨51, by decide⟩ ⟨130, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨52, by decide⟩ ⟨130, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨53, by decide⟩ ⟨130, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨54, by decide⟩ ⟨130, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨55, by decide⟩ ⟨130, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨56, by decide⟩ ⟨130, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨57, by decide⟩ ⟨130, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨58, by decide⟩ ⟨130, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨59, by decide⟩ ⟨130, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨60, by decide⟩ ⟨130, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨61, by decide⟩ ⟨130, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨62, by decide⟩ ⟨130, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨63, by decide⟩ ⟨130, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨64, by decide⟩ ⟨130, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨65, by decide⟩ ⟨130, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨66, by decide⟩ ⟨130, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨67, by decide⟩ ⟨130, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨68, by decide⟩ ⟨130, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨69, by decide⟩ ⟨130, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨70, by decide⟩ ⟨130, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨71, by decide⟩ ⟨130, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨72, by decide⟩ ⟨130, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨73, by decide⟩ ⟨130, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨74, by decide⟩ ⟨130, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨75, by decide⟩ ⟨130, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨76, by decide⟩ ⟨130, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨77, by decide⟩ ⟨130, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨78, by decide⟩ ⟨130, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨79, by decide⟩ ⟨130, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨80, by decide⟩ ⟨130, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨81, by decide⟩ ⟨130, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨82, by decide⟩ ⟨130, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨83, by decide⟩ ⟨130, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨84, by decide⟩ ⟨130, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨85, by decide⟩ ⟨130, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨86, by decide⟩ ⟨130, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨87, by decide⟩ ⟨130, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨88, by decide⟩ ⟨130, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨89, by decide⟩ ⟨130, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨90, by decide⟩ ⟨130, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨91, by decide⟩ ⟨130, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨92, by decide⟩ ⟨130, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨93, by decide⟩ ⟨130, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨94, by decide⟩ ⟨130, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨95, by decide⟩ ⟨130, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨96, by decide⟩ ⟨130, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨97, by decide⟩ ⟨130, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨98, by decide⟩ ⟨130, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨99, by decide⟩ ⟨130, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨100, by decide⟩ ⟨130, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨101, by decide⟩ ⟨130, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨102, by decide⟩ ⟨130, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨103, by decide⟩ ⟨130, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨104, by decide⟩ ⟨130, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨105, by decide⟩ ⟨130, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨106, by decide⟩ ⟨130, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨107, by decide⟩ ⟨130, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨108, by decide⟩ ⟨130, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨109, by decide⟩ ⟨130, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨110, by decide⟩ ⟨130, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨111, by decide⟩ ⟨130, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨112, by decide⟩ ⟨130, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨113, by decide⟩ ⟨130, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨114, by decide⟩ ⟨130, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨115, by decide⟩ ⟨130, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_fix ⟨116, by decide⟩ ⟨130, by decide⟩ p hp j hj hq fz1_116_130 fz2_116_130
  · exact match_zero_fix ⟨117, by decide⟩ ⟨130, by decide⟩ p hp j hj hq fz1_117_130 fz2_117_130
  · exact match_zero_fix ⟨118, by decide⟩ ⟨130, by decide⟩ p hp j hj hq fz1_118_130 fz2_118_130
  · exact match_zero_fix ⟨119, by decide⟩ ⟨130, by decide⟩ p hp j hj hq fz1_119_130 fz2_119_130
  · exact match_zero_fix ⟨120, by decide⟩ ⟨130, by decide⟩ p hp j hj hq fz1_120_130 fz2_120_130
  · exact match_zero_fix ⟨121, by decide⟩ ⟨130, by decide⟩ p hp j hj hq fz1_121_130 fz2_121_130
  · exact match_zero_fix ⟨122, by decide⟩ ⟨130, by decide⟩ p hp j hj hq fz1_122_130 fz2_122_130
  · exact match_zero_fix ⟨123, by decide⟩ ⟨130, by decide⟩ p hp j hj hq fz1_123_130 fz2_123_130
  · exact match_zero_fix ⟨124, by decide⟩ ⟨130, by decide⟩ p hp j hj hq fz1_124_130 fz2_124_130
  · exact match_zero_fix ⟨125, by decide⟩ ⟨130, by decide⟩ p hp j hj hq fz1_125_130 fz2_125_130
  · exact match_zero_fix ⟨126, by decide⟩ ⟨130, by decide⟩ p hp j hj hq fz1_126_130 fz2_126_130
  · exact match_zero_fix ⟨127, by decide⟩ ⟨130, by decide⟩ p hp j hj hq fz1_127_130 fz2_127_130
  · exact match_zero_fix ⟨128, by decide⟩ ⟨130, by decide⟩ p hp j hj hq fz1_128_130 fz2_128_130
  · exact match_zero_fix ⟨129, by decide⟩ ⟨130, by decide⟩ p hp j hj hq fz1_129_130 fz2_129_130
  · exact pair_130_130 p hp hrep j hj hq
  · exact match_zero_fix ⟨131, by decide⟩ ⟨130, by decide⟩ p hp j hj hq fz1_131_130 fz2_131_130
  · exact match_zero_fix ⟨132, by decide⟩ ⟨130, by decide⟩ p hp j hj hq fz1_132_130 fz2_132_130
  · exact match_zero_fix ⟨133, by decide⟩ ⟨130, by decide⟩ p hp j hj hq fz1_133_130 fz2_133_130
  · exact match_zero_fix ⟨134, by decide⟩ ⟨130, by decide⟩ p hp j hj hq fz1_134_130 fz2_134_130
  · exact match_zero_fix ⟨135, by decide⟩ ⟨130, by decide⟩ p hp j hj hq fz1_135_130 fz2_135_130
  · exact match_zero_fix ⟨136, by decide⟩ ⟨130, by decide⟩ p hp j hj hq fz1_136_130 fz2_136_130
  · exact match_zero_fix ⟨137, by decide⟩ ⟨130, by decide⟩ p hp j hj hq fz1_137_130 fz2_137_130
  · exact match_zero_fix ⟨138, by decide⟩ ⟨130, by decide⟩ p hp j hj hq fz1_138_130 fz2_138_130
  · exact match_zero_fix ⟨139, by decide⟩ ⟨130, by decide⟩ p hp j hj hq fz1_139_130 fz2_139_130
  · exact match_zero_fix ⟨140, by decide⟩ ⟨130, by decide⟩ p hp j hj hq fz1_140_130 fz2_140_130
  · exact match_zero_fix ⟨141, by decide⟩ ⟨130, by decide⟩ p hp j hj hq fz1_141_130 fz2_141_130
  · exact match_zero_fix ⟨142, by decide⟩ ⟨130, by decide⟩ p hp j hj hq fz1_142_130 fz2_142_130
  · exact match_zero_fix ⟨143, by decide⟩ ⟨130, by decide⟩ p hp j hj hq fz1_143_130 fz2_143_130
  · exact match_zero_fix ⟨144, by decide⟩ ⟨130, by decide⟩ p hp j hj hq fz1_144_130 fz2_144_130
  · exact match_zero_fix ⟨145, by decide⟩ ⟨130, by decide⟩ p hp j hj hq fz1_145_130 fz2_145_130
  · exact match_zero_fix ⟨146, by decide⟩ ⟨130, by decide⟩ p hp j hj hq fz1_146_130 fz2_146_130
  · exact pair_147_130 p hp hrep j hj hq

theorem master_131 (p : Nat) (hp : p < (Q2.transData.getD 131 []).length)
    (hrep : (Q2.cosetIsRep.getD 131 []).getD p false = true)
    (rK : Fin 148) (j : Nat) (hj : j < (repChars.getD rK.val []).length)
    (hq : (normIsRep.getD rK.val []).getD j false = true) :
    species (Q2.reps (⟨131, by decide⟩ : Fin 148)) (colE2 ⟨131, by decide⟩ p hp)
        (rowE2 rK j hj hq)
      = species (reps (⟨131, by decide⟩ : Fin 148))
        (colE1 ⟨131, by decide⟩ p (transLenTr ⟨131, by decide⟩ p hp)) (rowE1 rK j hj) := by
  rcases rK with ⟨nK, hnK⟩; interval_cases nK
  · exact match_zero_len ⟨0, by decide⟩ ⟨131, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨1, by decide⟩ ⟨131, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨2, by decide⟩ ⟨131, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨3, by decide⟩ ⟨131, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨4, by decide⟩ ⟨131, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨5, by decide⟩ ⟨131, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨6, by decide⟩ ⟨131, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨7, by decide⟩ ⟨131, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨8, by decide⟩ ⟨131, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨9, by decide⟩ ⟨131, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨10, by decide⟩ ⟨131, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨11, by decide⟩ ⟨131, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨12, by decide⟩ ⟨131, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨13, by decide⟩ ⟨131, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨14, by decide⟩ ⟨131, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨15, by decide⟩ ⟨131, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨16, by decide⟩ ⟨131, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨17, by decide⟩ ⟨131, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨18, by decide⟩ ⟨131, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨19, by decide⟩ ⟨131, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨20, by decide⟩ ⟨131, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨21, by decide⟩ ⟨131, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨22, by decide⟩ ⟨131, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨23, by decide⟩ ⟨131, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨24, by decide⟩ ⟨131, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨25, by decide⟩ ⟨131, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨26, by decide⟩ ⟨131, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨27, by decide⟩ ⟨131, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨28, by decide⟩ ⟨131, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨29, by decide⟩ ⟨131, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨30, by decide⟩ ⟨131, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨31, by decide⟩ ⟨131, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨32, by decide⟩ ⟨131, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨33, by decide⟩ ⟨131, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨34, by decide⟩ ⟨131, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨35, by decide⟩ ⟨131, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨36, by decide⟩ ⟨131, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨37, by decide⟩ ⟨131, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨38, by decide⟩ ⟨131, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨39, by decide⟩ ⟨131, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨40, by decide⟩ ⟨131, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨41, by decide⟩ ⟨131, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨42, by decide⟩ ⟨131, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨43, by decide⟩ ⟨131, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨44, by decide⟩ ⟨131, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨45, by decide⟩ ⟨131, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨46, by decide⟩ ⟨131, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨47, by decide⟩ ⟨131, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨48, by decide⟩ ⟨131, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨49, by decide⟩ ⟨131, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨50, by decide⟩ ⟨131, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨51, by decide⟩ ⟨131, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨52, by decide⟩ ⟨131, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨53, by decide⟩ ⟨131, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨54, by decide⟩ ⟨131, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨55, by decide⟩ ⟨131, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨56, by decide⟩ ⟨131, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨57, by decide⟩ ⟨131, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨58, by decide⟩ ⟨131, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨59, by decide⟩ ⟨131, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨60, by decide⟩ ⟨131, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨61, by decide⟩ ⟨131, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨62, by decide⟩ ⟨131, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨63, by decide⟩ ⟨131, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨64, by decide⟩ ⟨131, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨65, by decide⟩ ⟨131, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨66, by decide⟩ ⟨131, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨67, by decide⟩ ⟨131, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨68, by decide⟩ ⟨131, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨69, by decide⟩ ⟨131, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨70, by decide⟩ ⟨131, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨71, by decide⟩ ⟨131, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨72, by decide⟩ ⟨131, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨73, by decide⟩ ⟨131, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨74, by decide⟩ ⟨131, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨75, by decide⟩ ⟨131, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨76, by decide⟩ ⟨131, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨77, by decide⟩ ⟨131, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨78, by decide⟩ ⟨131, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨79, by decide⟩ ⟨131, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨80, by decide⟩ ⟨131, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨81, by decide⟩ ⟨131, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨82, by decide⟩ ⟨131, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨83, by decide⟩ ⟨131, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨84, by decide⟩ ⟨131, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨85, by decide⟩ ⟨131, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨86, by decide⟩ ⟨131, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨87, by decide⟩ ⟨131, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨88, by decide⟩ ⟨131, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨89, by decide⟩ ⟨131, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨90, by decide⟩ ⟨131, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨91, by decide⟩ ⟨131, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨92, by decide⟩ ⟨131, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨93, by decide⟩ ⟨131, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨94, by decide⟩ ⟨131, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨95, by decide⟩ ⟨131, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨96, by decide⟩ ⟨131, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨97, by decide⟩ ⟨131, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨98, by decide⟩ ⟨131, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨99, by decide⟩ ⟨131, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨100, by decide⟩ ⟨131, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨101, by decide⟩ ⟨131, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨102, by decide⟩ ⟨131, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨103, by decide⟩ ⟨131, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨104, by decide⟩ ⟨131, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨105, by decide⟩ ⟨131, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨106, by decide⟩ ⟨131, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨107, by decide⟩ ⟨131, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨108, by decide⟩ ⟨131, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨109, by decide⟩ ⟨131, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨110, by decide⟩ ⟨131, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨111, by decide⟩ ⟨131, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨112, by decide⟩ ⟨131, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨113, by decide⟩ ⟨131, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨114, by decide⟩ ⟨131, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨115, by decide⟩ ⟨131, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_fix ⟨116, by decide⟩ ⟨131, by decide⟩ p hp j hj hq fz1_116_131 fz2_116_131
  · exact match_zero_fix ⟨117, by decide⟩ ⟨131, by decide⟩ p hp j hj hq fz1_117_131 fz2_117_131
  · exact match_zero_fix ⟨118, by decide⟩ ⟨131, by decide⟩ p hp j hj hq fz1_118_131 fz2_118_131
  · exact match_zero_fix ⟨119, by decide⟩ ⟨131, by decide⟩ p hp j hj hq fz1_119_131 fz2_119_131
  · exact match_zero_fix ⟨120, by decide⟩ ⟨131, by decide⟩ p hp j hj hq fz1_120_131 fz2_120_131
  · exact match_zero_fix ⟨121, by decide⟩ ⟨131, by decide⟩ p hp j hj hq fz1_121_131 fz2_121_131
  · exact match_zero_fix ⟨122, by decide⟩ ⟨131, by decide⟩ p hp j hj hq fz1_122_131 fz2_122_131
  · exact match_zero_fix ⟨123, by decide⟩ ⟨131, by decide⟩ p hp j hj hq fz1_123_131 fz2_123_131
  · exact match_zero_fix ⟨124, by decide⟩ ⟨131, by decide⟩ p hp j hj hq fz1_124_131 fz2_124_131
  · exact match_zero_fix ⟨125, by decide⟩ ⟨131, by decide⟩ p hp j hj hq fz1_125_131 fz2_125_131
  · exact match_zero_fix ⟨126, by decide⟩ ⟨131, by decide⟩ p hp j hj hq fz1_126_131 fz2_126_131
  · exact match_zero_fix ⟨127, by decide⟩ ⟨131, by decide⟩ p hp j hj hq fz1_127_131 fz2_127_131
  · exact match_zero_fix ⟨128, by decide⟩ ⟨131, by decide⟩ p hp j hj hq fz1_128_131 fz2_128_131
  · exact match_zero_fix ⟨129, by decide⟩ ⟨131, by decide⟩ p hp j hj hq fz1_129_131 fz2_129_131
  · exact match_zero_fix ⟨130, by decide⟩ ⟨131, by decide⟩ p hp j hj hq fz1_130_131 fz2_130_131
  · exact pair_131_131 p hp hrep j hj hq
  · exact match_zero_fix ⟨132, by decide⟩ ⟨131, by decide⟩ p hp j hj hq fz1_132_131 fz2_132_131
  · exact match_zero_fix ⟨133, by decide⟩ ⟨131, by decide⟩ p hp j hj hq fz1_133_131 fz2_133_131
  · exact match_zero_fix ⟨134, by decide⟩ ⟨131, by decide⟩ p hp j hj hq fz1_134_131 fz2_134_131
  · exact match_zero_fix ⟨135, by decide⟩ ⟨131, by decide⟩ p hp j hj hq fz1_135_131 fz2_135_131
  · exact match_zero_fix ⟨136, by decide⟩ ⟨131, by decide⟩ p hp j hj hq fz1_136_131 fz2_136_131
  · exact match_zero_fix ⟨137, by decide⟩ ⟨131, by decide⟩ p hp j hj hq fz1_137_131 fz2_137_131
  · exact match_zero_fix ⟨138, by decide⟩ ⟨131, by decide⟩ p hp j hj hq fz1_138_131 fz2_138_131
  · exact match_zero_fix ⟨139, by decide⟩ ⟨131, by decide⟩ p hp j hj hq fz1_139_131 fz2_139_131
  · exact match_zero_fix ⟨140, by decide⟩ ⟨131, by decide⟩ p hp j hj hq fz1_140_131 fz2_140_131
  · exact match_zero_fix ⟨141, by decide⟩ ⟨131, by decide⟩ p hp j hj hq fz1_141_131 fz2_141_131
  · exact match_zero_fix ⟨142, by decide⟩ ⟨131, by decide⟩ p hp j hj hq fz1_142_131 fz2_142_131
  · exact match_zero_fix ⟨143, by decide⟩ ⟨131, by decide⟩ p hp j hj hq fz1_143_131 fz2_143_131
  · exact match_zero_fix ⟨144, by decide⟩ ⟨131, by decide⟩ p hp j hj hq fz1_144_131 fz2_144_131
  · exact match_zero_fix ⟨145, by decide⟩ ⟨131, by decide⟩ p hp j hj hq fz1_145_131 fz2_145_131
  · exact match_zero_fix ⟨146, by decide⟩ ⟨131, by decide⟩ p hp j hj hq fz1_146_131 fz2_146_131
  · exact pair_147_131 p hp hrep j hj hq

theorem master_132 (p : Nat) (hp : p < (Q2.transData.getD 132 []).length)
    (hrep : (Q2.cosetIsRep.getD 132 []).getD p false = true)
    (rK : Fin 148) (j : Nat) (hj : j < (repChars.getD rK.val []).length)
    (hq : (normIsRep.getD rK.val []).getD j false = true) :
    species (Q2.reps (⟨132, by decide⟩ : Fin 148)) (colE2 ⟨132, by decide⟩ p hp)
        (rowE2 rK j hj hq)
      = species (reps (⟨132, by decide⟩ : Fin 148))
        (colE1 ⟨132, by decide⟩ p (transLenTr ⟨132, by decide⟩ p hp)) (rowE1 rK j hj) := by
  rcases rK with ⟨nK, hnK⟩; interval_cases nK
  · exact match_zero_len ⟨0, by decide⟩ ⟨132, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨1, by decide⟩ ⟨132, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨2, by decide⟩ ⟨132, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨3, by decide⟩ ⟨132, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨4, by decide⟩ ⟨132, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨5, by decide⟩ ⟨132, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨6, by decide⟩ ⟨132, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨7, by decide⟩ ⟨132, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨8, by decide⟩ ⟨132, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨9, by decide⟩ ⟨132, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨10, by decide⟩ ⟨132, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨11, by decide⟩ ⟨132, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨12, by decide⟩ ⟨132, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨13, by decide⟩ ⟨132, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨14, by decide⟩ ⟨132, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨15, by decide⟩ ⟨132, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨16, by decide⟩ ⟨132, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨17, by decide⟩ ⟨132, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨18, by decide⟩ ⟨132, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨19, by decide⟩ ⟨132, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨20, by decide⟩ ⟨132, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨21, by decide⟩ ⟨132, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨22, by decide⟩ ⟨132, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨23, by decide⟩ ⟨132, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨24, by decide⟩ ⟨132, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨25, by decide⟩ ⟨132, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨26, by decide⟩ ⟨132, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨27, by decide⟩ ⟨132, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨28, by decide⟩ ⟨132, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨29, by decide⟩ ⟨132, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨30, by decide⟩ ⟨132, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨31, by decide⟩ ⟨132, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨32, by decide⟩ ⟨132, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨33, by decide⟩ ⟨132, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨34, by decide⟩ ⟨132, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨35, by decide⟩ ⟨132, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨36, by decide⟩ ⟨132, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨37, by decide⟩ ⟨132, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨38, by decide⟩ ⟨132, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨39, by decide⟩ ⟨132, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨40, by decide⟩ ⟨132, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨41, by decide⟩ ⟨132, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨42, by decide⟩ ⟨132, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨43, by decide⟩ ⟨132, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨44, by decide⟩ ⟨132, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨45, by decide⟩ ⟨132, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨46, by decide⟩ ⟨132, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨47, by decide⟩ ⟨132, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨48, by decide⟩ ⟨132, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨49, by decide⟩ ⟨132, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨50, by decide⟩ ⟨132, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨51, by decide⟩ ⟨132, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨52, by decide⟩ ⟨132, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨53, by decide⟩ ⟨132, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨54, by decide⟩ ⟨132, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨55, by decide⟩ ⟨132, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨56, by decide⟩ ⟨132, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨57, by decide⟩ ⟨132, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨58, by decide⟩ ⟨132, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨59, by decide⟩ ⟨132, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨60, by decide⟩ ⟨132, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨61, by decide⟩ ⟨132, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨62, by decide⟩ ⟨132, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨63, by decide⟩ ⟨132, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨64, by decide⟩ ⟨132, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨65, by decide⟩ ⟨132, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨66, by decide⟩ ⟨132, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨67, by decide⟩ ⟨132, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨68, by decide⟩ ⟨132, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨69, by decide⟩ ⟨132, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨70, by decide⟩ ⟨132, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨71, by decide⟩ ⟨132, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨72, by decide⟩ ⟨132, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨73, by decide⟩ ⟨132, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨74, by decide⟩ ⟨132, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨75, by decide⟩ ⟨132, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨76, by decide⟩ ⟨132, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨77, by decide⟩ ⟨132, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨78, by decide⟩ ⟨132, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨79, by decide⟩ ⟨132, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨80, by decide⟩ ⟨132, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨81, by decide⟩ ⟨132, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨82, by decide⟩ ⟨132, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨83, by decide⟩ ⟨132, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨84, by decide⟩ ⟨132, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨85, by decide⟩ ⟨132, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨86, by decide⟩ ⟨132, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨87, by decide⟩ ⟨132, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨88, by decide⟩ ⟨132, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨89, by decide⟩ ⟨132, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨90, by decide⟩ ⟨132, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨91, by decide⟩ ⟨132, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨92, by decide⟩ ⟨132, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨93, by decide⟩ ⟨132, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨94, by decide⟩ ⟨132, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨95, by decide⟩ ⟨132, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨96, by decide⟩ ⟨132, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨97, by decide⟩ ⟨132, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨98, by decide⟩ ⟨132, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨99, by decide⟩ ⟨132, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨100, by decide⟩ ⟨132, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨101, by decide⟩ ⟨132, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨102, by decide⟩ ⟨132, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨103, by decide⟩ ⟨132, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨104, by decide⟩ ⟨132, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨105, by decide⟩ ⟨132, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨106, by decide⟩ ⟨132, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨107, by decide⟩ ⟨132, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨108, by decide⟩ ⟨132, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨109, by decide⟩ ⟨132, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨110, by decide⟩ ⟨132, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨111, by decide⟩ ⟨132, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨112, by decide⟩ ⟨132, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨113, by decide⟩ ⟨132, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨114, by decide⟩ ⟨132, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨115, by decide⟩ ⟨132, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_fix ⟨116, by decide⟩ ⟨132, by decide⟩ p hp j hj hq fz1_116_132 fz2_116_132
  · exact match_zero_fix ⟨117, by decide⟩ ⟨132, by decide⟩ p hp j hj hq fz1_117_132 fz2_117_132
  · exact match_zero_fix ⟨118, by decide⟩ ⟨132, by decide⟩ p hp j hj hq fz1_118_132 fz2_118_132
  · exact match_zero_fix ⟨119, by decide⟩ ⟨132, by decide⟩ p hp j hj hq fz1_119_132 fz2_119_132
  · exact match_zero_fix ⟨120, by decide⟩ ⟨132, by decide⟩ p hp j hj hq fz1_120_132 fz2_120_132
  · exact match_zero_fix ⟨121, by decide⟩ ⟨132, by decide⟩ p hp j hj hq fz1_121_132 fz2_121_132
  · exact match_zero_fix ⟨122, by decide⟩ ⟨132, by decide⟩ p hp j hj hq fz1_122_132 fz2_122_132
  · exact match_zero_fix ⟨123, by decide⟩ ⟨132, by decide⟩ p hp j hj hq fz1_123_132 fz2_123_132
  · exact match_zero_fix ⟨124, by decide⟩ ⟨132, by decide⟩ p hp j hj hq fz1_124_132 fz2_124_132
  · exact match_zero_fix ⟨125, by decide⟩ ⟨132, by decide⟩ p hp j hj hq fz1_125_132 fz2_125_132
  · exact match_zero_fix ⟨126, by decide⟩ ⟨132, by decide⟩ p hp j hj hq fz1_126_132 fz2_126_132
  · exact match_zero_fix ⟨127, by decide⟩ ⟨132, by decide⟩ p hp j hj hq fz1_127_132 fz2_127_132
  · exact match_zero_fix ⟨128, by decide⟩ ⟨132, by decide⟩ p hp j hj hq fz1_128_132 fz2_128_132
  · exact match_zero_fix ⟨129, by decide⟩ ⟨132, by decide⟩ p hp j hj hq fz1_129_132 fz2_129_132
  · exact match_zero_fix ⟨130, by decide⟩ ⟨132, by decide⟩ p hp j hj hq fz1_130_132 fz2_130_132
  · exact match_zero_fix ⟨131, by decide⟩ ⟨132, by decide⟩ p hp j hj hq fz1_131_132 fz2_131_132
  · exact pair_132_132 p hp hrep j hj hq
  · exact match_zero_fix ⟨133, by decide⟩ ⟨132, by decide⟩ p hp j hj hq fz1_133_132 fz2_133_132
  · exact match_zero_fix ⟨134, by decide⟩ ⟨132, by decide⟩ p hp j hj hq fz1_134_132 fz2_134_132
  · exact match_zero_fix ⟨135, by decide⟩ ⟨132, by decide⟩ p hp j hj hq fz1_135_132 fz2_135_132
  · exact match_zero_fix ⟨136, by decide⟩ ⟨132, by decide⟩ p hp j hj hq fz1_136_132 fz2_136_132
  · exact match_zero_fix ⟨137, by decide⟩ ⟨132, by decide⟩ p hp j hj hq fz1_137_132 fz2_137_132
  · exact match_zero_fix ⟨138, by decide⟩ ⟨132, by decide⟩ p hp j hj hq fz1_138_132 fz2_138_132
  · exact match_zero_fix ⟨139, by decide⟩ ⟨132, by decide⟩ p hp j hj hq fz1_139_132 fz2_139_132
  · exact match_zero_fix ⟨140, by decide⟩ ⟨132, by decide⟩ p hp j hj hq fz1_140_132 fz2_140_132
  · exact match_zero_fix ⟨141, by decide⟩ ⟨132, by decide⟩ p hp j hj hq fz1_141_132 fz2_141_132
  · exact match_zero_fix ⟨142, by decide⟩ ⟨132, by decide⟩ p hp j hj hq fz1_142_132 fz2_142_132
  · exact match_zero_fix ⟨143, by decide⟩ ⟨132, by decide⟩ p hp j hj hq fz1_143_132 fz2_143_132
  · exact match_zero_fix ⟨144, by decide⟩ ⟨132, by decide⟩ p hp j hj hq fz1_144_132 fz2_144_132
  · exact match_zero_fix ⟨145, by decide⟩ ⟨132, by decide⟩ p hp j hj hq fz1_145_132 fz2_145_132
  · exact match_zero_fix ⟨146, by decide⟩ ⟨132, by decide⟩ p hp j hj hq fz1_146_132 fz2_146_132
  · exact pair_147_132 p hp hrep j hj hq

theorem master_133 (p : Nat) (hp : p < (Q2.transData.getD 133 []).length)
    (hrep : (Q2.cosetIsRep.getD 133 []).getD p false = true)
    (rK : Fin 148) (j : Nat) (hj : j < (repChars.getD rK.val []).length)
    (hq : (normIsRep.getD rK.val []).getD j false = true) :
    species (Q2.reps (⟨133, by decide⟩ : Fin 148)) (colE2 ⟨133, by decide⟩ p hp)
        (rowE2 rK j hj hq)
      = species (reps (⟨133, by decide⟩ : Fin 148))
        (colE1 ⟨133, by decide⟩ p (transLenTr ⟨133, by decide⟩ p hp)) (rowE1 rK j hj) := by
  rcases rK with ⟨nK, hnK⟩; interval_cases nK
  · exact match_zero_len ⟨0, by decide⟩ ⟨133, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨1, by decide⟩ ⟨133, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨2, by decide⟩ ⟨133, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨3, by decide⟩ ⟨133, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨4, by decide⟩ ⟨133, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨5, by decide⟩ ⟨133, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨6, by decide⟩ ⟨133, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨7, by decide⟩ ⟨133, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨8, by decide⟩ ⟨133, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨9, by decide⟩ ⟨133, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨10, by decide⟩ ⟨133, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨11, by decide⟩ ⟨133, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨12, by decide⟩ ⟨133, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨13, by decide⟩ ⟨133, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨14, by decide⟩ ⟨133, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨15, by decide⟩ ⟨133, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨16, by decide⟩ ⟨133, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨17, by decide⟩ ⟨133, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨18, by decide⟩ ⟨133, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨19, by decide⟩ ⟨133, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨20, by decide⟩ ⟨133, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨21, by decide⟩ ⟨133, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨22, by decide⟩ ⟨133, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨23, by decide⟩ ⟨133, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨24, by decide⟩ ⟨133, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨25, by decide⟩ ⟨133, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨26, by decide⟩ ⟨133, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨27, by decide⟩ ⟨133, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨28, by decide⟩ ⟨133, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨29, by decide⟩ ⟨133, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨30, by decide⟩ ⟨133, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨31, by decide⟩ ⟨133, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨32, by decide⟩ ⟨133, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨33, by decide⟩ ⟨133, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨34, by decide⟩ ⟨133, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨35, by decide⟩ ⟨133, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨36, by decide⟩ ⟨133, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨37, by decide⟩ ⟨133, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨38, by decide⟩ ⟨133, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨39, by decide⟩ ⟨133, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨40, by decide⟩ ⟨133, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨41, by decide⟩ ⟨133, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨42, by decide⟩ ⟨133, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨43, by decide⟩ ⟨133, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨44, by decide⟩ ⟨133, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨45, by decide⟩ ⟨133, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨46, by decide⟩ ⟨133, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨47, by decide⟩ ⟨133, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨48, by decide⟩ ⟨133, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨49, by decide⟩ ⟨133, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨50, by decide⟩ ⟨133, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨51, by decide⟩ ⟨133, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨52, by decide⟩ ⟨133, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨53, by decide⟩ ⟨133, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨54, by decide⟩ ⟨133, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨55, by decide⟩ ⟨133, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨56, by decide⟩ ⟨133, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨57, by decide⟩ ⟨133, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨58, by decide⟩ ⟨133, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨59, by decide⟩ ⟨133, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨60, by decide⟩ ⟨133, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨61, by decide⟩ ⟨133, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨62, by decide⟩ ⟨133, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨63, by decide⟩ ⟨133, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨64, by decide⟩ ⟨133, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨65, by decide⟩ ⟨133, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨66, by decide⟩ ⟨133, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨67, by decide⟩ ⟨133, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨68, by decide⟩ ⟨133, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨69, by decide⟩ ⟨133, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨70, by decide⟩ ⟨133, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨71, by decide⟩ ⟨133, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨72, by decide⟩ ⟨133, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨73, by decide⟩ ⟨133, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨74, by decide⟩ ⟨133, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨75, by decide⟩ ⟨133, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨76, by decide⟩ ⟨133, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨77, by decide⟩ ⟨133, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨78, by decide⟩ ⟨133, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨79, by decide⟩ ⟨133, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨80, by decide⟩ ⟨133, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨81, by decide⟩ ⟨133, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨82, by decide⟩ ⟨133, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨83, by decide⟩ ⟨133, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨84, by decide⟩ ⟨133, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨85, by decide⟩ ⟨133, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨86, by decide⟩ ⟨133, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨87, by decide⟩ ⟨133, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨88, by decide⟩ ⟨133, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨89, by decide⟩ ⟨133, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨90, by decide⟩ ⟨133, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨91, by decide⟩ ⟨133, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨92, by decide⟩ ⟨133, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨93, by decide⟩ ⟨133, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨94, by decide⟩ ⟨133, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨95, by decide⟩ ⟨133, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨96, by decide⟩ ⟨133, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨97, by decide⟩ ⟨133, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨98, by decide⟩ ⟨133, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨99, by decide⟩ ⟨133, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨100, by decide⟩ ⟨133, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨101, by decide⟩ ⟨133, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨102, by decide⟩ ⟨133, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨103, by decide⟩ ⟨133, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨104, by decide⟩ ⟨133, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨105, by decide⟩ ⟨133, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨106, by decide⟩ ⟨133, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨107, by decide⟩ ⟨133, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨108, by decide⟩ ⟨133, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨109, by decide⟩ ⟨133, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨110, by decide⟩ ⟨133, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨111, by decide⟩ ⟨133, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨112, by decide⟩ ⟨133, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨113, by decide⟩ ⟨133, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨114, by decide⟩ ⟨133, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨115, by decide⟩ ⟨133, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_fix ⟨116, by decide⟩ ⟨133, by decide⟩ p hp j hj hq fz1_116_133 fz2_116_133
  · exact match_zero_fix ⟨117, by decide⟩ ⟨133, by decide⟩ p hp j hj hq fz1_117_133 fz2_117_133
  · exact match_zero_fix ⟨118, by decide⟩ ⟨133, by decide⟩ p hp j hj hq fz1_118_133 fz2_118_133
  · exact match_zero_fix ⟨119, by decide⟩ ⟨133, by decide⟩ p hp j hj hq fz1_119_133 fz2_119_133
  · exact match_zero_fix ⟨120, by decide⟩ ⟨133, by decide⟩ p hp j hj hq fz1_120_133 fz2_120_133
  · exact match_zero_fix ⟨121, by decide⟩ ⟨133, by decide⟩ p hp j hj hq fz1_121_133 fz2_121_133
  · exact match_zero_fix ⟨122, by decide⟩ ⟨133, by decide⟩ p hp j hj hq fz1_122_133 fz2_122_133
  · exact match_zero_fix ⟨123, by decide⟩ ⟨133, by decide⟩ p hp j hj hq fz1_123_133 fz2_123_133
  · exact match_zero_fix ⟨124, by decide⟩ ⟨133, by decide⟩ p hp j hj hq fz1_124_133 fz2_124_133
  · exact match_zero_fix ⟨125, by decide⟩ ⟨133, by decide⟩ p hp j hj hq fz1_125_133 fz2_125_133
  · exact match_zero_fix ⟨126, by decide⟩ ⟨133, by decide⟩ p hp j hj hq fz1_126_133 fz2_126_133
  · exact match_zero_fix ⟨127, by decide⟩ ⟨133, by decide⟩ p hp j hj hq fz1_127_133 fz2_127_133
  · exact match_zero_fix ⟨128, by decide⟩ ⟨133, by decide⟩ p hp j hj hq fz1_128_133 fz2_128_133
  · exact match_zero_fix ⟨129, by decide⟩ ⟨133, by decide⟩ p hp j hj hq fz1_129_133 fz2_129_133
  · exact match_zero_fix ⟨130, by decide⟩ ⟨133, by decide⟩ p hp j hj hq fz1_130_133 fz2_130_133
  · exact match_zero_fix ⟨131, by decide⟩ ⟨133, by decide⟩ p hp j hj hq fz1_131_133 fz2_131_133
  · exact match_zero_fix ⟨132, by decide⟩ ⟨133, by decide⟩ p hp j hj hq fz1_132_133 fz2_132_133
  · exact pair_133_133 p hp hrep j hj hq
  · exact match_zero_fix ⟨134, by decide⟩ ⟨133, by decide⟩ p hp j hj hq fz1_134_133 fz2_134_133
  · exact match_zero_fix ⟨135, by decide⟩ ⟨133, by decide⟩ p hp j hj hq fz1_135_133 fz2_135_133
  · exact match_zero_fix ⟨136, by decide⟩ ⟨133, by decide⟩ p hp j hj hq fz1_136_133 fz2_136_133
  · exact match_zero_fix ⟨137, by decide⟩ ⟨133, by decide⟩ p hp j hj hq fz1_137_133 fz2_137_133
  · exact match_zero_fix ⟨138, by decide⟩ ⟨133, by decide⟩ p hp j hj hq fz1_138_133 fz2_138_133
  · exact match_zero_fix ⟨139, by decide⟩ ⟨133, by decide⟩ p hp j hj hq fz1_139_133 fz2_139_133
  · exact match_zero_fix ⟨140, by decide⟩ ⟨133, by decide⟩ p hp j hj hq fz1_140_133 fz2_140_133
  · exact match_zero_fix ⟨141, by decide⟩ ⟨133, by decide⟩ p hp j hj hq fz1_141_133 fz2_141_133
  · exact match_zero_fix ⟨142, by decide⟩ ⟨133, by decide⟩ p hp j hj hq fz1_142_133 fz2_142_133
  · exact match_zero_fix ⟨143, by decide⟩ ⟨133, by decide⟩ p hp j hj hq fz1_143_133 fz2_143_133
  · exact match_zero_fix ⟨144, by decide⟩ ⟨133, by decide⟩ p hp j hj hq fz1_144_133 fz2_144_133
  · exact match_zero_fix ⟨145, by decide⟩ ⟨133, by decide⟩ p hp j hj hq fz1_145_133 fz2_145_133
  · exact match_zero_fix ⟨146, by decide⟩ ⟨133, by decide⟩ p hp j hj hq fz1_146_133 fz2_146_133
  · exact pair_147_133 p hp hrep j hj hq

theorem master_134 (p : Nat) (hp : p < (Q2.transData.getD 134 []).length)
    (hrep : (Q2.cosetIsRep.getD 134 []).getD p false = true)
    (rK : Fin 148) (j : Nat) (hj : j < (repChars.getD rK.val []).length)
    (hq : (normIsRep.getD rK.val []).getD j false = true) :
    species (Q2.reps (⟨134, by decide⟩ : Fin 148)) (colE2 ⟨134, by decide⟩ p hp)
        (rowE2 rK j hj hq)
      = species (reps (⟨134, by decide⟩ : Fin 148))
        (colE1 ⟨134, by decide⟩ p (transLenTr ⟨134, by decide⟩ p hp)) (rowE1 rK j hj) := by
  rcases rK with ⟨nK, hnK⟩; interval_cases nK
  · exact match_zero_len ⟨0, by decide⟩ ⟨134, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨1, by decide⟩ ⟨134, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨2, by decide⟩ ⟨134, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨3, by decide⟩ ⟨134, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨4, by decide⟩ ⟨134, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨5, by decide⟩ ⟨134, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨6, by decide⟩ ⟨134, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨7, by decide⟩ ⟨134, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨8, by decide⟩ ⟨134, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨9, by decide⟩ ⟨134, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨10, by decide⟩ ⟨134, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨11, by decide⟩ ⟨134, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨12, by decide⟩ ⟨134, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨13, by decide⟩ ⟨134, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨14, by decide⟩ ⟨134, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨15, by decide⟩ ⟨134, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨16, by decide⟩ ⟨134, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨17, by decide⟩ ⟨134, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨18, by decide⟩ ⟨134, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨19, by decide⟩ ⟨134, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨20, by decide⟩ ⟨134, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨21, by decide⟩ ⟨134, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨22, by decide⟩ ⟨134, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨23, by decide⟩ ⟨134, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨24, by decide⟩ ⟨134, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨25, by decide⟩ ⟨134, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨26, by decide⟩ ⟨134, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨27, by decide⟩ ⟨134, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨28, by decide⟩ ⟨134, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨29, by decide⟩ ⟨134, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨30, by decide⟩ ⟨134, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨31, by decide⟩ ⟨134, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨32, by decide⟩ ⟨134, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨33, by decide⟩ ⟨134, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨34, by decide⟩ ⟨134, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨35, by decide⟩ ⟨134, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨36, by decide⟩ ⟨134, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨37, by decide⟩ ⟨134, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨38, by decide⟩ ⟨134, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨39, by decide⟩ ⟨134, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨40, by decide⟩ ⟨134, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨41, by decide⟩ ⟨134, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨42, by decide⟩ ⟨134, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨43, by decide⟩ ⟨134, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨44, by decide⟩ ⟨134, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨45, by decide⟩ ⟨134, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨46, by decide⟩ ⟨134, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨47, by decide⟩ ⟨134, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨48, by decide⟩ ⟨134, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨49, by decide⟩ ⟨134, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨50, by decide⟩ ⟨134, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨51, by decide⟩ ⟨134, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨52, by decide⟩ ⟨134, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨53, by decide⟩ ⟨134, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨54, by decide⟩ ⟨134, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨55, by decide⟩ ⟨134, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨56, by decide⟩ ⟨134, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨57, by decide⟩ ⟨134, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨58, by decide⟩ ⟨134, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨59, by decide⟩ ⟨134, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨60, by decide⟩ ⟨134, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨61, by decide⟩ ⟨134, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨62, by decide⟩ ⟨134, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨63, by decide⟩ ⟨134, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨64, by decide⟩ ⟨134, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨65, by decide⟩ ⟨134, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨66, by decide⟩ ⟨134, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨67, by decide⟩ ⟨134, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨68, by decide⟩ ⟨134, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨69, by decide⟩ ⟨134, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨70, by decide⟩ ⟨134, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨71, by decide⟩ ⟨134, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨72, by decide⟩ ⟨134, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨73, by decide⟩ ⟨134, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨74, by decide⟩ ⟨134, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨75, by decide⟩ ⟨134, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨76, by decide⟩ ⟨134, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨77, by decide⟩ ⟨134, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨78, by decide⟩ ⟨134, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨79, by decide⟩ ⟨134, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨80, by decide⟩ ⟨134, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨81, by decide⟩ ⟨134, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨82, by decide⟩ ⟨134, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨83, by decide⟩ ⟨134, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨84, by decide⟩ ⟨134, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨85, by decide⟩ ⟨134, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨86, by decide⟩ ⟨134, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨87, by decide⟩ ⟨134, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨88, by decide⟩ ⟨134, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨89, by decide⟩ ⟨134, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨90, by decide⟩ ⟨134, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨91, by decide⟩ ⟨134, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨92, by decide⟩ ⟨134, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨93, by decide⟩ ⟨134, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨94, by decide⟩ ⟨134, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨95, by decide⟩ ⟨134, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨96, by decide⟩ ⟨134, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨97, by decide⟩ ⟨134, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨98, by decide⟩ ⟨134, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨99, by decide⟩ ⟨134, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨100, by decide⟩ ⟨134, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨101, by decide⟩ ⟨134, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨102, by decide⟩ ⟨134, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨103, by decide⟩ ⟨134, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨104, by decide⟩ ⟨134, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨105, by decide⟩ ⟨134, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨106, by decide⟩ ⟨134, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨107, by decide⟩ ⟨134, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨108, by decide⟩ ⟨134, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨109, by decide⟩ ⟨134, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨110, by decide⟩ ⟨134, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨111, by decide⟩ ⟨134, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨112, by decide⟩ ⟨134, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨113, by decide⟩ ⟨134, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨114, by decide⟩ ⟨134, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨115, by decide⟩ ⟨134, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_fix ⟨116, by decide⟩ ⟨134, by decide⟩ p hp j hj hq fz1_116_134 fz2_116_134
  · exact match_zero_fix ⟨117, by decide⟩ ⟨134, by decide⟩ p hp j hj hq fz1_117_134 fz2_117_134
  · exact match_zero_fix ⟨118, by decide⟩ ⟨134, by decide⟩ p hp j hj hq fz1_118_134 fz2_118_134
  · exact match_zero_fix ⟨119, by decide⟩ ⟨134, by decide⟩ p hp j hj hq fz1_119_134 fz2_119_134
  · exact match_zero_fix ⟨120, by decide⟩ ⟨134, by decide⟩ p hp j hj hq fz1_120_134 fz2_120_134
  · exact match_zero_fix ⟨121, by decide⟩ ⟨134, by decide⟩ p hp j hj hq fz1_121_134 fz2_121_134
  · exact match_zero_fix ⟨122, by decide⟩ ⟨134, by decide⟩ p hp j hj hq fz1_122_134 fz2_122_134
  · exact match_zero_fix ⟨123, by decide⟩ ⟨134, by decide⟩ p hp j hj hq fz1_123_134 fz2_123_134
  · exact match_zero_fix ⟨124, by decide⟩ ⟨134, by decide⟩ p hp j hj hq fz1_124_134 fz2_124_134
  · exact match_zero_fix ⟨125, by decide⟩ ⟨134, by decide⟩ p hp j hj hq fz1_125_134 fz2_125_134
  · exact match_zero_fix ⟨126, by decide⟩ ⟨134, by decide⟩ p hp j hj hq fz1_126_134 fz2_126_134
  · exact match_zero_fix ⟨127, by decide⟩ ⟨134, by decide⟩ p hp j hj hq fz1_127_134 fz2_127_134
  · exact match_zero_fix ⟨128, by decide⟩ ⟨134, by decide⟩ p hp j hj hq fz1_128_134 fz2_128_134
  · exact match_zero_fix ⟨129, by decide⟩ ⟨134, by decide⟩ p hp j hj hq fz1_129_134 fz2_129_134
  · exact match_zero_fix ⟨130, by decide⟩ ⟨134, by decide⟩ p hp j hj hq fz1_130_134 fz2_130_134
  · exact match_zero_fix ⟨131, by decide⟩ ⟨134, by decide⟩ p hp j hj hq fz1_131_134 fz2_131_134
  · exact match_zero_fix ⟨132, by decide⟩ ⟨134, by decide⟩ p hp j hj hq fz1_132_134 fz2_132_134
  · exact match_zero_fix ⟨133, by decide⟩ ⟨134, by decide⟩ p hp j hj hq fz1_133_134 fz2_133_134
  · exact pair_134_134 p hp hrep j hj hq
  · exact match_zero_fix ⟨135, by decide⟩ ⟨134, by decide⟩ p hp j hj hq fz1_135_134 fz2_135_134
  · exact match_zero_fix ⟨136, by decide⟩ ⟨134, by decide⟩ p hp j hj hq fz1_136_134 fz2_136_134
  · exact match_zero_fix ⟨137, by decide⟩ ⟨134, by decide⟩ p hp j hj hq fz1_137_134 fz2_137_134
  · exact match_zero_fix ⟨138, by decide⟩ ⟨134, by decide⟩ p hp j hj hq fz1_138_134 fz2_138_134
  · exact match_zero_fix ⟨139, by decide⟩ ⟨134, by decide⟩ p hp j hj hq fz1_139_134 fz2_139_134
  · exact match_zero_fix ⟨140, by decide⟩ ⟨134, by decide⟩ p hp j hj hq fz1_140_134 fz2_140_134
  · exact match_zero_fix ⟨141, by decide⟩ ⟨134, by decide⟩ p hp j hj hq fz1_141_134 fz2_141_134
  · exact match_zero_fix ⟨142, by decide⟩ ⟨134, by decide⟩ p hp j hj hq fz1_142_134 fz2_142_134
  · exact match_zero_fix ⟨143, by decide⟩ ⟨134, by decide⟩ p hp j hj hq fz1_143_134 fz2_143_134
  · exact match_zero_fix ⟨144, by decide⟩ ⟨134, by decide⟩ p hp j hj hq fz1_144_134 fz2_144_134
  · exact match_zero_fix ⟨145, by decide⟩ ⟨134, by decide⟩ p hp j hj hq fz1_145_134 fz2_145_134
  · exact match_zero_fix ⟨146, by decide⟩ ⟨134, by decide⟩ p hp j hj hq fz1_146_134 fz2_146_134
  · exact pair_147_134 p hp hrep j hj hq

theorem master_135 (p : Nat) (hp : p < (Q2.transData.getD 135 []).length)
    (hrep : (Q2.cosetIsRep.getD 135 []).getD p false = true)
    (rK : Fin 148) (j : Nat) (hj : j < (repChars.getD rK.val []).length)
    (hq : (normIsRep.getD rK.val []).getD j false = true) :
    species (Q2.reps (⟨135, by decide⟩ : Fin 148)) (colE2 ⟨135, by decide⟩ p hp)
        (rowE2 rK j hj hq)
      = species (reps (⟨135, by decide⟩ : Fin 148))
        (colE1 ⟨135, by decide⟩ p (transLenTr ⟨135, by decide⟩ p hp)) (rowE1 rK j hj) := by
  rcases rK with ⟨nK, hnK⟩; interval_cases nK
  · exact match_zero_len ⟨0, by decide⟩ ⟨135, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨1, by decide⟩ ⟨135, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨2, by decide⟩ ⟨135, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨3, by decide⟩ ⟨135, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨4, by decide⟩ ⟨135, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨5, by decide⟩ ⟨135, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨6, by decide⟩ ⟨135, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨7, by decide⟩ ⟨135, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨8, by decide⟩ ⟨135, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨9, by decide⟩ ⟨135, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨10, by decide⟩ ⟨135, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨11, by decide⟩ ⟨135, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨12, by decide⟩ ⟨135, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨13, by decide⟩ ⟨135, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨14, by decide⟩ ⟨135, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨15, by decide⟩ ⟨135, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨16, by decide⟩ ⟨135, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨17, by decide⟩ ⟨135, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨18, by decide⟩ ⟨135, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨19, by decide⟩ ⟨135, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨20, by decide⟩ ⟨135, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨21, by decide⟩ ⟨135, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨22, by decide⟩ ⟨135, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨23, by decide⟩ ⟨135, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨24, by decide⟩ ⟨135, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨25, by decide⟩ ⟨135, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨26, by decide⟩ ⟨135, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨27, by decide⟩ ⟨135, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨28, by decide⟩ ⟨135, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨29, by decide⟩ ⟨135, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨30, by decide⟩ ⟨135, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨31, by decide⟩ ⟨135, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨32, by decide⟩ ⟨135, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨33, by decide⟩ ⟨135, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨34, by decide⟩ ⟨135, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨35, by decide⟩ ⟨135, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨36, by decide⟩ ⟨135, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨37, by decide⟩ ⟨135, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨38, by decide⟩ ⟨135, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨39, by decide⟩ ⟨135, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨40, by decide⟩ ⟨135, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨41, by decide⟩ ⟨135, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨42, by decide⟩ ⟨135, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨43, by decide⟩ ⟨135, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨44, by decide⟩ ⟨135, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨45, by decide⟩ ⟨135, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨46, by decide⟩ ⟨135, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨47, by decide⟩ ⟨135, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨48, by decide⟩ ⟨135, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨49, by decide⟩ ⟨135, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨50, by decide⟩ ⟨135, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨51, by decide⟩ ⟨135, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨52, by decide⟩ ⟨135, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨53, by decide⟩ ⟨135, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨54, by decide⟩ ⟨135, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨55, by decide⟩ ⟨135, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨56, by decide⟩ ⟨135, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨57, by decide⟩ ⟨135, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨58, by decide⟩ ⟨135, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨59, by decide⟩ ⟨135, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨60, by decide⟩ ⟨135, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨61, by decide⟩ ⟨135, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨62, by decide⟩ ⟨135, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨63, by decide⟩ ⟨135, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨64, by decide⟩ ⟨135, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨65, by decide⟩ ⟨135, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨66, by decide⟩ ⟨135, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨67, by decide⟩ ⟨135, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨68, by decide⟩ ⟨135, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨69, by decide⟩ ⟨135, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨70, by decide⟩ ⟨135, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨71, by decide⟩ ⟨135, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨72, by decide⟩ ⟨135, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨73, by decide⟩ ⟨135, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨74, by decide⟩ ⟨135, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨75, by decide⟩ ⟨135, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨76, by decide⟩ ⟨135, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨77, by decide⟩ ⟨135, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨78, by decide⟩ ⟨135, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨79, by decide⟩ ⟨135, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨80, by decide⟩ ⟨135, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨81, by decide⟩ ⟨135, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨82, by decide⟩ ⟨135, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨83, by decide⟩ ⟨135, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨84, by decide⟩ ⟨135, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨85, by decide⟩ ⟨135, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨86, by decide⟩ ⟨135, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨87, by decide⟩ ⟨135, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨88, by decide⟩ ⟨135, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨89, by decide⟩ ⟨135, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨90, by decide⟩ ⟨135, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨91, by decide⟩ ⟨135, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨92, by decide⟩ ⟨135, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨93, by decide⟩ ⟨135, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨94, by decide⟩ ⟨135, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨95, by decide⟩ ⟨135, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨96, by decide⟩ ⟨135, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨97, by decide⟩ ⟨135, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨98, by decide⟩ ⟨135, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨99, by decide⟩ ⟨135, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨100, by decide⟩ ⟨135, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨101, by decide⟩ ⟨135, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨102, by decide⟩ ⟨135, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨103, by decide⟩ ⟨135, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨104, by decide⟩ ⟨135, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨105, by decide⟩ ⟨135, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨106, by decide⟩ ⟨135, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨107, by decide⟩ ⟨135, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨108, by decide⟩ ⟨135, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨109, by decide⟩ ⟨135, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨110, by decide⟩ ⟨135, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨111, by decide⟩ ⟨135, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨112, by decide⟩ ⟨135, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨113, by decide⟩ ⟨135, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨114, by decide⟩ ⟨135, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨115, by decide⟩ ⟨135, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_fix ⟨116, by decide⟩ ⟨135, by decide⟩ p hp j hj hq fz1_116_135 fz2_116_135
  · exact match_zero_fix ⟨117, by decide⟩ ⟨135, by decide⟩ p hp j hj hq fz1_117_135 fz2_117_135
  · exact match_zero_fix ⟨118, by decide⟩ ⟨135, by decide⟩ p hp j hj hq fz1_118_135 fz2_118_135
  · exact match_zero_fix ⟨119, by decide⟩ ⟨135, by decide⟩ p hp j hj hq fz1_119_135 fz2_119_135
  · exact match_zero_fix ⟨120, by decide⟩ ⟨135, by decide⟩ p hp j hj hq fz1_120_135 fz2_120_135
  · exact match_zero_fix ⟨121, by decide⟩ ⟨135, by decide⟩ p hp j hj hq fz1_121_135 fz2_121_135
  · exact match_zero_fix ⟨122, by decide⟩ ⟨135, by decide⟩ p hp j hj hq fz1_122_135 fz2_122_135
  · exact match_zero_fix ⟨123, by decide⟩ ⟨135, by decide⟩ p hp j hj hq fz1_123_135 fz2_123_135
  · exact match_zero_fix ⟨124, by decide⟩ ⟨135, by decide⟩ p hp j hj hq fz1_124_135 fz2_124_135
  · exact match_zero_fix ⟨125, by decide⟩ ⟨135, by decide⟩ p hp j hj hq fz1_125_135 fz2_125_135
  · exact match_zero_fix ⟨126, by decide⟩ ⟨135, by decide⟩ p hp j hj hq fz1_126_135 fz2_126_135
  · exact match_zero_fix ⟨127, by decide⟩ ⟨135, by decide⟩ p hp j hj hq fz1_127_135 fz2_127_135
  · exact match_zero_fix ⟨128, by decide⟩ ⟨135, by decide⟩ p hp j hj hq fz1_128_135 fz2_128_135
  · exact match_zero_fix ⟨129, by decide⟩ ⟨135, by decide⟩ p hp j hj hq fz1_129_135 fz2_129_135
  · exact match_zero_fix ⟨130, by decide⟩ ⟨135, by decide⟩ p hp j hj hq fz1_130_135 fz2_130_135
  · exact match_zero_fix ⟨131, by decide⟩ ⟨135, by decide⟩ p hp j hj hq fz1_131_135 fz2_131_135
  · exact match_zero_fix ⟨132, by decide⟩ ⟨135, by decide⟩ p hp j hj hq fz1_132_135 fz2_132_135
  · exact match_zero_fix ⟨133, by decide⟩ ⟨135, by decide⟩ p hp j hj hq fz1_133_135 fz2_133_135
  · exact match_zero_fix ⟨134, by decide⟩ ⟨135, by decide⟩ p hp j hj hq fz1_134_135 fz2_134_135
  · exact pair_135_135 p hp hrep j hj hq
  · exact match_zero_fix ⟨136, by decide⟩ ⟨135, by decide⟩ p hp j hj hq fz1_136_135 fz2_136_135
  · exact match_zero_fix ⟨137, by decide⟩ ⟨135, by decide⟩ p hp j hj hq fz1_137_135 fz2_137_135
  · exact match_zero_fix ⟨138, by decide⟩ ⟨135, by decide⟩ p hp j hj hq fz1_138_135 fz2_138_135
  · exact match_zero_fix ⟨139, by decide⟩ ⟨135, by decide⟩ p hp j hj hq fz1_139_135 fz2_139_135
  · exact match_zero_fix ⟨140, by decide⟩ ⟨135, by decide⟩ p hp j hj hq fz1_140_135 fz2_140_135
  · exact match_zero_fix ⟨141, by decide⟩ ⟨135, by decide⟩ p hp j hj hq fz1_141_135 fz2_141_135
  · exact match_zero_fix ⟨142, by decide⟩ ⟨135, by decide⟩ p hp j hj hq fz1_142_135 fz2_142_135
  · exact match_zero_fix ⟨143, by decide⟩ ⟨135, by decide⟩ p hp j hj hq fz1_143_135 fz2_143_135
  · exact match_zero_fix ⟨144, by decide⟩ ⟨135, by decide⟩ p hp j hj hq fz1_144_135 fz2_144_135
  · exact match_zero_fix ⟨145, by decide⟩ ⟨135, by decide⟩ p hp j hj hq fz1_145_135 fz2_145_135
  · exact match_zero_fix ⟨146, by decide⟩ ⟨135, by decide⟩ p hp j hj hq fz1_146_135 fz2_146_135
  · exact pair_147_135 p hp hrep j hj hq

end LeanDring.P5Presentation
