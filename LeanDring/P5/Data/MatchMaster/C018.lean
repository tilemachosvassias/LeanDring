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
import LeanDring.P5.Data.MatchPair.C009
import LeanDring.P5.Data.MatchPair.C010

/-! # Stage-5 per-column-class master theorems, chunk 17 (auto-emitted).  -/

namespace LeanDring.P5Presentation

open MulAction Finset LeanDring.DRing LeanDring.MonGSet

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.style.longLine false

theorem master_136 (p : Nat) (hp : p < (Q2.transData.getD 136 []).length)
    (hrep : (Q2.cosetIsRep.getD 136 []).getD p false = true)
    (rK : Fin 148) (j : Nat) (hj : j < (repChars.getD rK.val []).length)
    (hq : (normIsRep.getD rK.val []).getD j false = true) :
    species (Q2.reps (⟨136, by decide⟩ : Fin 148)) (colE2 ⟨136, by decide⟩ p hp)
        (rowE2 rK j hj hq)
      = species (reps (⟨136, by decide⟩ : Fin 148))
        (colE1 ⟨136, by decide⟩ p (transLenTr ⟨136, by decide⟩ p hp)) (rowE1 rK j hj) := by
  rcases rK with ⟨nK, hnK⟩; interval_cases nK
  · exact match_zero_len ⟨0, by decide⟩ ⟨136, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨1, by decide⟩ ⟨136, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨2, by decide⟩ ⟨136, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨3, by decide⟩ ⟨136, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨4, by decide⟩ ⟨136, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨5, by decide⟩ ⟨136, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨6, by decide⟩ ⟨136, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨7, by decide⟩ ⟨136, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨8, by decide⟩ ⟨136, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨9, by decide⟩ ⟨136, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨10, by decide⟩ ⟨136, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨11, by decide⟩ ⟨136, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨12, by decide⟩ ⟨136, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨13, by decide⟩ ⟨136, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨14, by decide⟩ ⟨136, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨15, by decide⟩ ⟨136, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨16, by decide⟩ ⟨136, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨17, by decide⟩ ⟨136, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨18, by decide⟩ ⟨136, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨19, by decide⟩ ⟨136, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨20, by decide⟩ ⟨136, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨21, by decide⟩ ⟨136, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨22, by decide⟩ ⟨136, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨23, by decide⟩ ⟨136, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨24, by decide⟩ ⟨136, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨25, by decide⟩ ⟨136, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨26, by decide⟩ ⟨136, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨27, by decide⟩ ⟨136, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨28, by decide⟩ ⟨136, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨29, by decide⟩ ⟨136, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨30, by decide⟩ ⟨136, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨31, by decide⟩ ⟨136, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨32, by decide⟩ ⟨136, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨33, by decide⟩ ⟨136, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨34, by decide⟩ ⟨136, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨35, by decide⟩ ⟨136, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨36, by decide⟩ ⟨136, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨37, by decide⟩ ⟨136, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨38, by decide⟩ ⟨136, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨39, by decide⟩ ⟨136, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨40, by decide⟩ ⟨136, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨41, by decide⟩ ⟨136, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨42, by decide⟩ ⟨136, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨43, by decide⟩ ⟨136, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨44, by decide⟩ ⟨136, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨45, by decide⟩ ⟨136, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨46, by decide⟩ ⟨136, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨47, by decide⟩ ⟨136, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨48, by decide⟩ ⟨136, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨49, by decide⟩ ⟨136, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨50, by decide⟩ ⟨136, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨51, by decide⟩ ⟨136, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨52, by decide⟩ ⟨136, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨53, by decide⟩ ⟨136, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨54, by decide⟩ ⟨136, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨55, by decide⟩ ⟨136, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨56, by decide⟩ ⟨136, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨57, by decide⟩ ⟨136, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨58, by decide⟩ ⟨136, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨59, by decide⟩ ⟨136, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨60, by decide⟩ ⟨136, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨61, by decide⟩ ⟨136, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨62, by decide⟩ ⟨136, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨63, by decide⟩ ⟨136, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨64, by decide⟩ ⟨136, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨65, by decide⟩ ⟨136, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨66, by decide⟩ ⟨136, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨67, by decide⟩ ⟨136, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨68, by decide⟩ ⟨136, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨69, by decide⟩ ⟨136, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨70, by decide⟩ ⟨136, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨71, by decide⟩ ⟨136, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨72, by decide⟩ ⟨136, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨73, by decide⟩ ⟨136, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨74, by decide⟩ ⟨136, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨75, by decide⟩ ⟨136, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨76, by decide⟩ ⟨136, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨77, by decide⟩ ⟨136, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨78, by decide⟩ ⟨136, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨79, by decide⟩ ⟨136, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨80, by decide⟩ ⟨136, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨81, by decide⟩ ⟨136, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨82, by decide⟩ ⟨136, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨83, by decide⟩ ⟨136, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨84, by decide⟩ ⟨136, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨85, by decide⟩ ⟨136, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨86, by decide⟩ ⟨136, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨87, by decide⟩ ⟨136, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨88, by decide⟩ ⟨136, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨89, by decide⟩ ⟨136, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨90, by decide⟩ ⟨136, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨91, by decide⟩ ⟨136, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨92, by decide⟩ ⟨136, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨93, by decide⟩ ⟨136, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨94, by decide⟩ ⟨136, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨95, by decide⟩ ⟨136, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨96, by decide⟩ ⟨136, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨97, by decide⟩ ⟨136, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨98, by decide⟩ ⟨136, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨99, by decide⟩ ⟨136, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨100, by decide⟩ ⟨136, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨101, by decide⟩ ⟨136, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨102, by decide⟩ ⟨136, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨103, by decide⟩ ⟨136, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨104, by decide⟩ ⟨136, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨105, by decide⟩ ⟨136, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨106, by decide⟩ ⟨136, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨107, by decide⟩ ⟨136, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨108, by decide⟩ ⟨136, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨109, by decide⟩ ⟨136, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨110, by decide⟩ ⟨136, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨111, by decide⟩ ⟨136, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨112, by decide⟩ ⟨136, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨113, by decide⟩ ⟨136, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨114, by decide⟩ ⟨136, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨115, by decide⟩ ⟨136, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_fix ⟨116, by decide⟩ ⟨136, by decide⟩ p hp j hj hq fz1_116_136 fz2_116_136
  · exact match_zero_fix ⟨117, by decide⟩ ⟨136, by decide⟩ p hp j hj hq fz1_117_136 fz2_117_136
  · exact match_zero_fix ⟨118, by decide⟩ ⟨136, by decide⟩ p hp j hj hq fz1_118_136 fz2_118_136
  · exact match_zero_fix ⟨119, by decide⟩ ⟨136, by decide⟩ p hp j hj hq fz1_119_136 fz2_119_136
  · exact match_zero_fix ⟨120, by decide⟩ ⟨136, by decide⟩ p hp j hj hq fz1_120_136 fz2_120_136
  · exact match_zero_fix ⟨121, by decide⟩ ⟨136, by decide⟩ p hp j hj hq fz1_121_136 fz2_121_136
  · exact match_zero_fix ⟨122, by decide⟩ ⟨136, by decide⟩ p hp j hj hq fz1_122_136 fz2_122_136
  · exact match_zero_fix ⟨123, by decide⟩ ⟨136, by decide⟩ p hp j hj hq fz1_123_136 fz2_123_136
  · exact match_zero_fix ⟨124, by decide⟩ ⟨136, by decide⟩ p hp j hj hq fz1_124_136 fz2_124_136
  · exact match_zero_fix ⟨125, by decide⟩ ⟨136, by decide⟩ p hp j hj hq fz1_125_136 fz2_125_136
  · exact match_zero_fix ⟨126, by decide⟩ ⟨136, by decide⟩ p hp j hj hq fz1_126_136 fz2_126_136
  · exact match_zero_fix ⟨127, by decide⟩ ⟨136, by decide⟩ p hp j hj hq fz1_127_136 fz2_127_136
  · exact match_zero_fix ⟨128, by decide⟩ ⟨136, by decide⟩ p hp j hj hq fz1_128_136 fz2_128_136
  · exact match_zero_fix ⟨129, by decide⟩ ⟨136, by decide⟩ p hp j hj hq fz1_129_136 fz2_129_136
  · exact match_zero_fix ⟨130, by decide⟩ ⟨136, by decide⟩ p hp j hj hq fz1_130_136 fz2_130_136
  · exact match_zero_fix ⟨131, by decide⟩ ⟨136, by decide⟩ p hp j hj hq fz1_131_136 fz2_131_136
  · exact match_zero_fix ⟨132, by decide⟩ ⟨136, by decide⟩ p hp j hj hq fz1_132_136 fz2_132_136
  · exact match_zero_fix ⟨133, by decide⟩ ⟨136, by decide⟩ p hp j hj hq fz1_133_136 fz2_133_136
  · exact match_zero_fix ⟨134, by decide⟩ ⟨136, by decide⟩ p hp j hj hq fz1_134_136 fz2_134_136
  · exact match_zero_fix ⟨135, by decide⟩ ⟨136, by decide⟩ p hp j hj hq fz1_135_136 fz2_135_136
  · exact pair_136_136 p hp hrep j hj hq
  · exact match_zero_fix ⟨137, by decide⟩ ⟨136, by decide⟩ p hp j hj hq fz1_137_136 fz2_137_136
  · exact match_zero_fix ⟨138, by decide⟩ ⟨136, by decide⟩ p hp j hj hq fz1_138_136 fz2_138_136
  · exact match_zero_fix ⟨139, by decide⟩ ⟨136, by decide⟩ p hp j hj hq fz1_139_136 fz2_139_136
  · exact match_zero_fix ⟨140, by decide⟩ ⟨136, by decide⟩ p hp j hj hq fz1_140_136 fz2_140_136
  · exact match_zero_fix ⟨141, by decide⟩ ⟨136, by decide⟩ p hp j hj hq fz1_141_136 fz2_141_136
  · exact match_zero_fix ⟨142, by decide⟩ ⟨136, by decide⟩ p hp j hj hq fz1_142_136 fz2_142_136
  · exact match_zero_fix ⟨143, by decide⟩ ⟨136, by decide⟩ p hp j hj hq fz1_143_136 fz2_143_136
  · exact match_zero_fix ⟨144, by decide⟩ ⟨136, by decide⟩ p hp j hj hq fz1_144_136 fz2_144_136
  · exact match_zero_fix ⟨145, by decide⟩ ⟨136, by decide⟩ p hp j hj hq fz1_145_136 fz2_145_136
  · exact match_zero_fix ⟨146, by decide⟩ ⟨136, by decide⟩ p hp j hj hq fz1_146_136 fz2_146_136
  · exact pair_147_136 p hp hrep j hj hq

theorem master_137 (p : Nat) (hp : p < (Q2.transData.getD 137 []).length)
    (hrep : (Q2.cosetIsRep.getD 137 []).getD p false = true)
    (rK : Fin 148) (j : Nat) (hj : j < (repChars.getD rK.val []).length)
    (hq : (normIsRep.getD rK.val []).getD j false = true) :
    species (Q2.reps (⟨137, by decide⟩ : Fin 148)) (colE2 ⟨137, by decide⟩ p hp)
        (rowE2 rK j hj hq)
      = species (reps (⟨137, by decide⟩ : Fin 148))
        (colE1 ⟨137, by decide⟩ p (transLenTr ⟨137, by decide⟩ p hp)) (rowE1 rK j hj) := by
  rcases rK with ⟨nK, hnK⟩; interval_cases nK
  · exact match_zero_len ⟨0, by decide⟩ ⟨137, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨1, by decide⟩ ⟨137, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨2, by decide⟩ ⟨137, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨3, by decide⟩ ⟨137, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨4, by decide⟩ ⟨137, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨5, by decide⟩ ⟨137, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨6, by decide⟩ ⟨137, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨7, by decide⟩ ⟨137, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨8, by decide⟩ ⟨137, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨9, by decide⟩ ⟨137, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨10, by decide⟩ ⟨137, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨11, by decide⟩ ⟨137, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨12, by decide⟩ ⟨137, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨13, by decide⟩ ⟨137, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨14, by decide⟩ ⟨137, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨15, by decide⟩ ⟨137, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨16, by decide⟩ ⟨137, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨17, by decide⟩ ⟨137, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨18, by decide⟩ ⟨137, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨19, by decide⟩ ⟨137, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨20, by decide⟩ ⟨137, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨21, by decide⟩ ⟨137, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨22, by decide⟩ ⟨137, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨23, by decide⟩ ⟨137, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨24, by decide⟩ ⟨137, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨25, by decide⟩ ⟨137, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨26, by decide⟩ ⟨137, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨27, by decide⟩ ⟨137, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨28, by decide⟩ ⟨137, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨29, by decide⟩ ⟨137, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨30, by decide⟩ ⟨137, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨31, by decide⟩ ⟨137, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨32, by decide⟩ ⟨137, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨33, by decide⟩ ⟨137, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨34, by decide⟩ ⟨137, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨35, by decide⟩ ⟨137, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨36, by decide⟩ ⟨137, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨37, by decide⟩ ⟨137, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨38, by decide⟩ ⟨137, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨39, by decide⟩ ⟨137, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨40, by decide⟩ ⟨137, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨41, by decide⟩ ⟨137, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨42, by decide⟩ ⟨137, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨43, by decide⟩ ⟨137, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨44, by decide⟩ ⟨137, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨45, by decide⟩ ⟨137, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨46, by decide⟩ ⟨137, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨47, by decide⟩ ⟨137, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨48, by decide⟩ ⟨137, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨49, by decide⟩ ⟨137, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨50, by decide⟩ ⟨137, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨51, by decide⟩ ⟨137, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨52, by decide⟩ ⟨137, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨53, by decide⟩ ⟨137, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨54, by decide⟩ ⟨137, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨55, by decide⟩ ⟨137, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨56, by decide⟩ ⟨137, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨57, by decide⟩ ⟨137, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨58, by decide⟩ ⟨137, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨59, by decide⟩ ⟨137, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨60, by decide⟩ ⟨137, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨61, by decide⟩ ⟨137, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨62, by decide⟩ ⟨137, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨63, by decide⟩ ⟨137, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨64, by decide⟩ ⟨137, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨65, by decide⟩ ⟨137, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨66, by decide⟩ ⟨137, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨67, by decide⟩ ⟨137, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨68, by decide⟩ ⟨137, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨69, by decide⟩ ⟨137, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨70, by decide⟩ ⟨137, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨71, by decide⟩ ⟨137, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨72, by decide⟩ ⟨137, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨73, by decide⟩ ⟨137, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨74, by decide⟩ ⟨137, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨75, by decide⟩ ⟨137, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨76, by decide⟩ ⟨137, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨77, by decide⟩ ⟨137, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨78, by decide⟩ ⟨137, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨79, by decide⟩ ⟨137, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨80, by decide⟩ ⟨137, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨81, by decide⟩ ⟨137, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨82, by decide⟩ ⟨137, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨83, by decide⟩ ⟨137, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨84, by decide⟩ ⟨137, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨85, by decide⟩ ⟨137, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨86, by decide⟩ ⟨137, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨87, by decide⟩ ⟨137, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨88, by decide⟩ ⟨137, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨89, by decide⟩ ⟨137, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨90, by decide⟩ ⟨137, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨91, by decide⟩ ⟨137, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨92, by decide⟩ ⟨137, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨93, by decide⟩ ⟨137, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨94, by decide⟩ ⟨137, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨95, by decide⟩ ⟨137, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨96, by decide⟩ ⟨137, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨97, by decide⟩ ⟨137, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨98, by decide⟩ ⟨137, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨99, by decide⟩ ⟨137, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨100, by decide⟩ ⟨137, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨101, by decide⟩ ⟨137, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨102, by decide⟩ ⟨137, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨103, by decide⟩ ⟨137, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨104, by decide⟩ ⟨137, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨105, by decide⟩ ⟨137, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨106, by decide⟩ ⟨137, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨107, by decide⟩ ⟨137, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨108, by decide⟩ ⟨137, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨109, by decide⟩ ⟨137, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨110, by decide⟩ ⟨137, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨111, by decide⟩ ⟨137, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨112, by decide⟩ ⟨137, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨113, by decide⟩ ⟨137, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨114, by decide⟩ ⟨137, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨115, by decide⟩ ⟨137, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_fix ⟨116, by decide⟩ ⟨137, by decide⟩ p hp j hj hq fz1_116_137 fz2_116_137
  · exact match_zero_fix ⟨117, by decide⟩ ⟨137, by decide⟩ p hp j hj hq fz1_117_137 fz2_117_137
  · exact match_zero_fix ⟨118, by decide⟩ ⟨137, by decide⟩ p hp j hj hq fz1_118_137 fz2_118_137
  · exact match_zero_fix ⟨119, by decide⟩ ⟨137, by decide⟩ p hp j hj hq fz1_119_137 fz2_119_137
  · exact match_zero_fix ⟨120, by decide⟩ ⟨137, by decide⟩ p hp j hj hq fz1_120_137 fz2_120_137
  · exact match_zero_fix ⟨121, by decide⟩ ⟨137, by decide⟩ p hp j hj hq fz1_121_137 fz2_121_137
  · exact match_zero_fix ⟨122, by decide⟩ ⟨137, by decide⟩ p hp j hj hq fz1_122_137 fz2_122_137
  · exact match_zero_fix ⟨123, by decide⟩ ⟨137, by decide⟩ p hp j hj hq fz1_123_137 fz2_123_137
  · exact match_zero_fix ⟨124, by decide⟩ ⟨137, by decide⟩ p hp j hj hq fz1_124_137 fz2_124_137
  · exact match_zero_fix ⟨125, by decide⟩ ⟨137, by decide⟩ p hp j hj hq fz1_125_137 fz2_125_137
  · exact match_zero_fix ⟨126, by decide⟩ ⟨137, by decide⟩ p hp j hj hq fz1_126_137 fz2_126_137
  · exact match_zero_fix ⟨127, by decide⟩ ⟨137, by decide⟩ p hp j hj hq fz1_127_137 fz2_127_137
  · exact match_zero_fix ⟨128, by decide⟩ ⟨137, by decide⟩ p hp j hj hq fz1_128_137 fz2_128_137
  · exact match_zero_fix ⟨129, by decide⟩ ⟨137, by decide⟩ p hp j hj hq fz1_129_137 fz2_129_137
  · exact match_zero_fix ⟨130, by decide⟩ ⟨137, by decide⟩ p hp j hj hq fz1_130_137 fz2_130_137
  · exact match_zero_fix ⟨131, by decide⟩ ⟨137, by decide⟩ p hp j hj hq fz1_131_137 fz2_131_137
  · exact match_zero_fix ⟨132, by decide⟩ ⟨137, by decide⟩ p hp j hj hq fz1_132_137 fz2_132_137
  · exact match_zero_fix ⟨133, by decide⟩ ⟨137, by decide⟩ p hp j hj hq fz1_133_137 fz2_133_137
  · exact match_zero_fix ⟨134, by decide⟩ ⟨137, by decide⟩ p hp j hj hq fz1_134_137 fz2_134_137
  · exact match_zero_fix ⟨135, by decide⟩ ⟨137, by decide⟩ p hp j hj hq fz1_135_137 fz2_135_137
  · exact match_zero_fix ⟨136, by decide⟩ ⟨137, by decide⟩ p hp j hj hq fz1_136_137 fz2_136_137
  · exact pair_137_137 p hp hrep j hj hq
  · exact match_zero_fix ⟨138, by decide⟩ ⟨137, by decide⟩ p hp j hj hq fz1_138_137 fz2_138_137
  · exact match_zero_fix ⟨139, by decide⟩ ⟨137, by decide⟩ p hp j hj hq fz1_139_137 fz2_139_137
  · exact match_zero_fix ⟨140, by decide⟩ ⟨137, by decide⟩ p hp j hj hq fz1_140_137 fz2_140_137
  · exact match_zero_fix ⟨141, by decide⟩ ⟨137, by decide⟩ p hp j hj hq fz1_141_137 fz2_141_137
  · exact match_zero_fix ⟨142, by decide⟩ ⟨137, by decide⟩ p hp j hj hq fz1_142_137 fz2_142_137
  · exact match_zero_fix ⟨143, by decide⟩ ⟨137, by decide⟩ p hp j hj hq fz1_143_137 fz2_143_137
  · exact match_zero_fix ⟨144, by decide⟩ ⟨137, by decide⟩ p hp j hj hq fz1_144_137 fz2_144_137
  · exact match_zero_fix ⟨145, by decide⟩ ⟨137, by decide⟩ p hp j hj hq fz1_145_137 fz2_145_137
  · exact match_zero_fix ⟨146, by decide⟩ ⟨137, by decide⟩ p hp j hj hq fz1_146_137 fz2_146_137
  · exact pair_147_137 p hp hrep j hj hq

theorem master_138 (p : Nat) (hp : p < (Q2.transData.getD 138 []).length)
    (hrep : (Q2.cosetIsRep.getD 138 []).getD p false = true)
    (rK : Fin 148) (j : Nat) (hj : j < (repChars.getD rK.val []).length)
    (hq : (normIsRep.getD rK.val []).getD j false = true) :
    species (Q2.reps (⟨138, by decide⟩ : Fin 148)) (colE2 ⟨138, by decide⟩ p hp)
        (rowE2 rK j hj hq)
      = species (reps (⟨138, by decide⟩ : Fin 148))
        (colE1 ⟨138, by decide⟩ p (transLenTr ⟨138, by decide⟩ p hp)) (rowE1 rK j hj) := by
  rcases rK with ⟨nK, hnK⟩; interval_cases nK
  · exact match_zero_len ⟨0, by decide⟩ ⟨138, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨1, by decide⟩ ⟨138, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨2, by decide⟩ ⟨138, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨3, by decide⟩ ⟨138, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨4, by decide⟩ ⟨138, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨5, by decide⟩ ⟨138, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨6, by decide⟩ ⟨138, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨7, by decide⟩ ⟨138, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨8, by decide⟩ ⟨138, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨9, by decide⟩ ⟨138, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨10, by decide⟩ ⟨138, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨11, by decide⟩ ⟨138, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨12, by decide⟩ ⟨138, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨13, by decide⟩ ⟨138, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨14, by decide⟩ ⟨138, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨15, by decide⟩ ⟨138, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨16, by decide⟩ ⟨138, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨17, by decide⟩ ⟨138, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨18, by decide⟩ ⟨138, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨19, by decide⟩ ⟨138, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨20, by decide⟩ ⟨138, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨21, by decide⟩ ⟨138, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨22, by decide⟩ ⟨138, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨23, by decide⟩ ⟨138, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨24, by decide⟩ ⟨138, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨25, by decide⟩ ⟨138, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨26, by decide⟩ ⟨138, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨27, by decide⟩ ⟨138, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨28, by decide⟩ ⟨138, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨29, by decide⟩ ⟨138, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨30, by decide⟩ ⟨138, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨31, by decide⟩ ⟨138, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨32, by decide⟩ ⟨138, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨33, by decide⟩ ⟨138, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨34, by decide⟩ ⟨138, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨35, by decide⟩ ⟨138, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨36, by decide⟩ ⟨138, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨37, by decide⟩ ⟨138, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨38, by decide⟩ ⟨138, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨39, by decide⟩ ⟨138, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨40, by decide⟩ ⟨138, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨41, by decide⟩ ⟨138, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨42, by decide⟩ ⟨138, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨43, by decide⟩ ⟨138, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨44, by decide⟩ ⟨138, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨45, by decide⟩ ⟨138, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨46, by decide⟩ ⟨138, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨47, by decide⟩ ⟨138, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨48, by decide⟩ ⟨138, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨49, by decide⟩ ⟨138, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨50, by decide⟩ ⟨138, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨51, by decide⟩ ⟨138, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨52, by decide⟩ ⟨138, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨53, by decide⟩ ⟨138, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨54, by decide⟩ ⟨138, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨55, by decide⟩ ⟨138, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨56, by decide⟩ ⟨138, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨57, by decide⟩ ⟨138, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨58, by decide⟩ ⟨138, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨59, by decide⟩ ⟨138, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨60, by decide⟩ ⟨138, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨61, by decide⟩ ⟨138, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨62, by decide⟩ ⟨138, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨63, by decide⟩ ⟨138, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨64, by decide⟩ ⟨138, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨65, by decide⟩ ⟨138, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨66, by decide⟩ ⟨138, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨67, by decide⟩ ⟨138, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨68, by decide⟩ ⟨138, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨69, by decide⟩ ⟨138, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨70, by decide⟩ ⟨138, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨71, by decide⟩ ⟨138, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨72, by decide⟩ ⟨138, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨73, by decide⟩ ⟨138, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨74, by decide⟩ ⟨138, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨75, by decide⟩ ⟨138, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨76, by decide⟩ ⟨138, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨77, by decide⟩ ⟨138, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨78, by decide⟩ ⟨138, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨79, by decide⟩ ⟨138, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨80, by decide⟩ ⟨138, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨81, by decide⟩ ⟨138, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨82, by decide⟩ ⟨138, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨83, by decide⟩ ⟨138, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨84, by decide⟩ ⟨138, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨85, by decide⟩ ⟨138, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨86, by decide⟩ ⟨138, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨87, by decide⟩ ⟨138, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨88, by decide⟩ ⟨138, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨89, by decide⟩ ⟨138, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨90, by decide⟩ ⟨138, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨91, by decide⟩ ⟨138, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨92, by decide⟩ ⟨138, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨93, by decide⟩ ⟨138, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨94, by decide⟩ ⟨138, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨95, by decide⟩ ⟨138, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨96, by decide⟩ ⟨138, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨97, by decide⟩ ⟨138, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨98, by decide⟩ ⟨138, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨99, by decide⟩ ⟨138, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨100, by decide⟩ ⟨138, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨101, by decide⟩ ⟨138, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨102, by decide⟩ ⟨138, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨103, by decide⟩ ⟨138, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨104, by decide⟩ ⟨138, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨105, by decide⟩ ⟨138, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨106, by decide⟩ ⟨138, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨107, by decide⟩ ⟨138, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨108, by decide⟩ ⟨138, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨109, by decide⟩ ⟨138, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨110, by decide⟩ ⟨138, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨111, by decide⟩ ⟨138, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨112, by decide⟩ ⟨138, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨113, by decide⟩ ⟨138, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨114, by decide⟩ ⟨138, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨115, by decide⟩ ⟨138, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_fix ⟨116, by decide⟩ ⟨138, by decide⟩ p hp j hj hq fz1_116_138 fz2_116_138
  · exact match_zero_fix ⟨117, by decide⟩ ⟨138, by decide⟩ p hp j hj hq fz1_117_138 fz2_117_138
  · exact match_zero_fix ⟨118, by decide⟩ ⟨138, by decide⟩ p hp j hj hq fz1_118_138 fz2_118_138
  · exact match_zero_fix ⟨119, by decide⟩ ⟨138, by decide⟩ p hp j hj hq fz1_119_138 fz2_119_138
  · exact match_zero_fix ⟨120, by decide⟩ ⟨138, by decide⟩ p hp j hj hq fz1_120_138 fz2_120_138
  · exact match_zero_fix ⟨121, by decide⟩ ⟨138, by decide⟩ p hp j hj hq fz1_121_138 fz2_121_138
  · exact match_zero_fix ⟨122, by decide⟩ ⟨138, by decide⟩ p hp j hj hq fz1_122_138 fz2_122_138
  · exact match_zero_fix ⟨123, by decide⟩ ⟨138, by decide⟩ p hp j hj hq fz1_123_138 fz2_123_138
  · exact match_zero_fix ⟨124, by decide⟩ ⟨138, by decide⟩ p hp j hj hq fz1_124_138 fz2_124_138
  · exact match_zero_fix ⟨125, by decide⟩ ⟨138, by decide⟩ p hp j hj hq fz1_125_138 fz2_125_138
  · exact match_zero_fix ⟨126, by decide⟩ ⟨138, by decide⟩ p hp j hj hq fz1_126_138 fz2_126_138
  · exact match_zero_fix ⟨127, by decide⟩ ⟨138, by decide⟩ p hp j hj hq fz1_127_138 fz2_127_138
  · exact match_zero_fix ⟨128, by decide⟩ ⟨138, by decide⟩ p hp j hj hq fz1_128_138 fz2_128_138
  · exact match_zero_fix ⟨129, by decide⟩ ⟨138, by decide⟩ p hp j hj hq fz1_129_138 fz2_129_138
  · exact match_zero_fix ⟨130, by decide⟩ ⟨138, by decide⟩ p hp j hj hq fz1_130_138 fz2_130_138
  · exact match_zero_fix ⟨131, by decide⟩ ⟨138, by decide⟩ p hp j hj hq fz1_131_138 fz2_131_138
  · exact match_zero_fix ⟨132, by decide⟩ ⟨138, by decide⟩ p hp j hj hq fz1_132_138 fz2_132_138
  · exact match_zero_fix ⟨133, by decide⟩ ⟨138, by decide⟩ p hp j hj hq fz1_133_138 fz2_133_138
  · exact match_zero_fix ⟨134, by decide⟩ ⟨138, by decide⟩ p hp j hj hq fz1_134_138 fz2_134_138
  · exact match_zero_fix ⟨135, by decide⟩ ⟨138, by decide⟩ p hp j hj hq fz1_135_138 fz2_135_138
  · exact match_zero_fix ⟨136, by decide⟩ ⟨138, by decide⟩ p hp j hj hq fz1_136_138 fz2_136_138
  · exact match_zero_fix ⟨137, by decide⟩ ⟨138, by decide⟩ p hp j hj hq fz1_137_138 fz2_137_138
  · exact pair_138_138 p hp hrep j hj hq
  · exact match_zero_fix ⟨139, by decide⟩ ⟨138, by decide⟩ p hp j hj hq fz1_139_138 fz2_139_138
  · exact match_zero_fix ⟨140, by decide⟩ ⟨138, by decide⟩ p hp j hj hq fz1_140_138 fz2_140_138
  · exact match_zero_fix ⟨141, by decide⟩ ⟨138, by decide⟩ p hp j hj hq fz1_141_138 fz2_141_138
  · exact match_zero_fix ⟨142, by decide⟩ ⟨138, by decide⟩ p hp j hj hq fz1_142_138 fz2_142_138
  · exact match_zero_fix ⟨143, by decide⟩ ⟨138, by decide⟩ p hp j hj hq fz1_143_138 fz2_143_138
  · exact match_zero_fix ⟨144, by decide⟩ ⟨138, by decide⟩ p hp j hj hq fz1_144_138 fz2_144_138
  · exact match_zero_fix ⟨145, by decide⟩ ⟨138, by decide⟩ p hp j hj hq fz1_145_138 fz2_145_138
  · exact match_zero_fix ⟨146, by decide⟩ ⟨138, by decide⟩ p hp j hj hq fz1_146_138 fz2_146_138
  · exact pair_147_138 p hp hrep j hj hq

theorem master_139 (p : Nat) (hp : p < (Q2.transData.getD 139 []).length)
    (hrep : (Q2.cosetIsRep.getD 139 []).getD p false = true)
    (rK : Fin 148) (j : Nat) (hj : j < (repChars.getD rK.val []).length)
    (hq : (normIsRep.getD rK.val []).getD j false = true) :
    species (Q2.reps (⟨139, by decide⟩ : Fin 148)) (colE2 ⟨139, by decide⟩ p hp)
        (rowE2 rK j hj hq)
      = species (reps (⟨139, by decide⟩ : Fin 148))
        (colE1 ⟨139, by decide⟩ p (transLenTr ⟨139, by decide⟩ p hp)) (rowE1 rK j hj) := by
  rcases rK with ⟨nK, hnK⟩; interval_cases nK
  · exact match_zero_len ⟨0, by decide⟩ ⟨139, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨1, by decide⟩ ⟨139, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨2, by decide⟩ ⟨139, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨3, by decide⟩ ⟨139, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨4, by decide⟩ ⟨139, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨5, by decide⟩ ⟨139, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨6, by decide⟩ ⟨139, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨7, by decide⟩ ⟨139, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨8, by decide⟩ ⟨139, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨9, by decide⟩ ⟨139, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨10, by decide⟩ ⟨139, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨11, by decide⟩ ⟨139, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨12, by decide⟩ ⟨139, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨13, by decide⟩ ⟨139, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨14, by decide⟩ ⟨139, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨15, by decide⟩ ⟨139, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨16, by decide⟩ ⟨139, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨17, by decide⟩ ⟨139, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨18, by decide⟩ ⟨139, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨19, by decide⟩ ⟨139, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨20, by decide⟩ ⟨139, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨21, by decide⟩ ⟨139, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨22, by decide⟩ ⟨139, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨23, by decide⟩ ⟨139, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨24, by decide⟩ ⟨139, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨25, by decide⟩ ⟨139, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨26, by decide⟩ ⟨139, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨27, by decide⟩ ⟨139, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨28, by decide⟩ ⟨139, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨29, by decide⟩ ⟨139, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨30, by decide⟩ ⟨139, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨31, by decide⟩ ⟨139, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨32, by decide⟩ ⟨139, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨33, by decide⟩ ⟨139, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨34, by decide⟩ ⟨139, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨35, by decide⟩ ⟨139, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨36, by decide⟩ ⟨139, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨37, by decide⟩ ⟨139, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨38, by decide⟩ ⟨139, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨39, by decide⟩ ⟨139, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨40, by decide⟩ ⟨139, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨41, by decide⟩ ⟨139, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨42, by decide⟩ ⟨139, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨43, by decide⟩ ⟨139, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨44, by decide⟩ ⟨139, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨45, by decide⟩ ⟨139, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨46, by decide⟩ ⟨139, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨47, by decide⟩ ⟨139, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨48, by decide⟩ ⟨139, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨49, by decide⟩ ⟨139, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨50, by decide⟩ ⟨139, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨51, by decide⟩ ⟨139, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨52, by decide⟩ ⟨139, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨53, by decide⟩ ⟨139, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨54, by decide⟩ ⟨139, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨55, by decide⟩ ⟨139, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨56, by decide⟩ ⟨139, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨57, by decide⟩ ⟨139, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨58, by decide⟩ ⟨139, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨59, by decide⟩ ⟨139, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨60, by decide⟩ ⟨139, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨61, by decide⟩ ⟨139, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨62, by decide⟩ ⟨139, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨63, by decide⟩ ⟨139, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨64, by decide⟩ ⟨139, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨65, by decide⟩ ⟨139, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨66, by decide⟩ ⟨139, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨67, by decide⟩ ⟨139, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨68, by decide⟩ ⟨139, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨69, by decide⟩ ⟨139, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨70, by decide⟩ ⟨139, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨71, by decide⟩ ⟨139, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨72, by decide⟩ ⟨139, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨73, by decide⟩ ⟨139, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨74, by decide⟩ ⟨139, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨75, by decide⟩ ⟨139, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨76, by decide⟩ ⟨139, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨77, by decide⟩ ⟨139, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨78, by decide⟩ ⟨139, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨79, by decide⟩ ⟨139, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨80, by decide⟩ ⟨139, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨81, by decide⟩ ⟨139, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨82, by decide⟩ ⟨139, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨83, by decide⟩ ⟨139, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨84, by decide⟩ ⟨139, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨85, by decide⟩ ⟨139, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨86, by decide⟩ ⟨139, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨87, by decide⟩ ⟨139, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨88, by decide⟩ ⟨139, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨89, by decide⟩ ⟨139, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨90, by decide⟩ ⟨139, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨91, by decide⟩ ⟨139, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨92, by decide⟩ ⟨139, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨93, by decide⟩ ⟨139, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨94, by decide⟩ ⟨139, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨95, by decide⟩ ⟨139, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨96, by decide⟩ ⟨139, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨97, by decide⟩ ⟨139, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨98, by decide⟩ ⟨139, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨99, by decide⟩ ⟨139, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨100, by decide⟩ ⟨139, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨101, by decide⟩ ⟨139, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨102, by decide⟩ ⟨139, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨103, by decide⟩ ⟨139, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨104, by decide⟩ ⟨139, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨105, by decide⟩ ⟨139, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨106, by decide⟩ ⟨139, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨107, by decide⟩ ⟨139, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨108, by decide⟩ ⟨139, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨109, by decide⟩ ⟨139, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨110, by decide⟩ ⟨139, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨111, by decide⟩ ⟨139, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨112, by decide⟩ ⟨139, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨113, by decide⟩ ⟨139, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨114, by decide⟩ ⟨139, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨115, by decide⟩ ⟨139, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_fix ⟨116, by decide⟩ ⟨139, by decide⟩ p hp j hj hq fz1_116_139 fz2_116_139
  · exact match_zero_fix ⟨117, by decide⟩ ⟨139, by decide⟩ p hp j hj hq fz1_117_139 fz2_117_139
  · exact match_zero_fix ⟨118, by decide⟩ ⟨139, by decide⟩ p hp j hj hq fz1_118_139 fz2_118_139
  · exact match_zero_fix ⟨119, by decide⟩ ⟨139, by decide⟩ p hp j hj hq fz1_119_139 fz2_119_139
  · exact match_zero_fix ⟨120, by decide⟩ ⟨139, by decide⟩ p hp j hj hq fz1_120_139 fz2_120_139
  · exact match_zero_fix ⟨121, by decide⟩ ⟨139, by decide⟩ p hp j hj hq fz1_121_139 fz2_121_139
  · exact match_zero_fix ⟨122, by decide⟩ ⟨139, by decide⟩ p hp j hj hq fz1_122_139 fz2_122_139
  · exact match_zero_fix ⟨123, by decide⟩ ⟨139, by decide⟩ p hp j hj hq fz1_123_139 fz2_123_139
  · exact match_zero_fix ⟨124, by decide⟩ ⟨139, by decide⟩ p hp j hj hq fz1_124_139 fz2_124_139
  · exact match_zero_fix ⟨125, by decide⟩ ⟨139, by decide⟩ p hp j hj hq fz1_125_139 fz2_125_139
  · exact match_zero_fix ⟨126, by decide⟩ ⟨139, by decide⟩ p hp j hj hq fz1_126_139 fz2_126_139
  · exact match_zero_fix ⟨127, by decide⟩ ⟨139, by decide⟩ p hp j hj hq fz1_127_139 fz2_127_139
  · exact match_zero_fix ⟨128, by decide⟩ ⟨139, by decide⟩ p hp j hj hq fz1_128_139 fz2_128_139
  · exact match_zero_fix ⟨129, by decide⟩ ⟨139, by decide⟩ p hp j hj hq fz1_129_139 fz2_129_139
  · exact match_zero_fix ⟨130, by decide⟩ ⟨139, by decide⟩ p hp j hj hq fz1_130_139 fz2_130_139
  · exact match_zero_fix ⟨131, by decide⟩ ⟨139, by decide⟩ p hp j hj hq fz1_131_139 fz2_131_139
  · exact match_zero_fix ⟨132, by decide⟩ ⟨139, by decide⟩ p hp j hj hq fz1_132_139 fz2_132_139
  · exact match_zero_fix ⟨133, by decide⟩ ⟨139, by decide⟩ p hp j hj hq fz1_133_139 fz2_133_139
  · exact match_zero_fix ⟨134, by decide⟩ ⟨139, by decide⟩ p hp j hj hq fz1_134_139 fz2_134_139
  · exact match_zero_fix ⟨135, by decide⟩ ⟨139, by decide⟩ p hp j hj hq fz1_135_139 fz2_135_139
  · exact match_zero_fix ⟨136, by decide⟩ ⟨139, by decide⟩ p hp j hj hq fz1_136_139 fz2_136_139
  · exact match_zero_fix ⟨137, by decide⟩ ⟨139, by decide⟩ p hp j hj hq fz1_137_139 fz2_137_139
  · exact match_zero_fix ⟨138, by decide⟩ ⟨139, by decide⟩ p hp j hj hq fz1_138_139 fz2_138_139
  · exact pair_139_139 p hp hrep j hj hq
  · exact match_zero_fix ⟨140, by decide⟩ ⟨139, by decide⟩ p hp j hj hq fz1_140_139 fz2_140_139
  · exact match_zero_fix ⟨141, by decide⟩ ⟨139, by decide⟩ p hp j hj hq fz1_141_139 fz2_141_139
  · exact match_zero_fix ⟨142, by decide⟩ ⟨139, by decide⟩ p hp j hj hq fz1_142_139 fz2_142_139
  · exact match_zero_fix ⟨143, by decide⟩ ⟨139, by decide⟩ p hp j hj hq fz1_143_139 fz2_143_139
  · exact match_zero_fix ⟨144, by decide⟩ ⟨139, by decide⟩ p hp j hj hq fz1_144_139 fz2_144_139
  · exact match_zero_fix ⟨145, by decide⟩ ⟨139, by decide⟩ p hp j hj hq fz1_145_139 fz2_145_139
  · exact match_zero_fix ⟨146, by decide⟩ ⟨139, by decide⟩ p hp j hj hq fz1_146_139 fz2_146_139
  · exact pair_147_139 p hp hrep j hj hq

theorem master_140 (p : Nat) (hp : p < (Q2.transData.getD 140 []).length)
    (hrep : (Q2.cosetIsRep.getD 140 []).getD p false = true)
    (rK : Fin 148) (j : Nat) (hj : j < (repChars.getD rK.val []).length)
    (hq : (normIsRep.getD rK.val []).getD j false = true) :
    species (Q2.reps (⟨140, by decide⟩ : Fin 148)) (colE2 ⟨140, by decide⟩ p hp)
        (rowE2 rK j hj hq)
      = species (reps (⟨140, by decide⟩ : Fin 148))
        (colE1 ⟨140, by decide⟩ p (transLenTr ⟨140, by decide⟩ p hp)) (rowE1 rK j hj) := by
  rcases rK with ⟨nK, hnK⟩; interval_cases nK
  · exact match_zero_len ⟨0, by decide⟩ ⟨140, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨1, by decide⟩ ⟨140, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨2, by decide⟩ ⟨140, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨3, by decide⟩ ⟨140, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨4, by decide⟩ ⟨140, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨5, by decide⟩ ⟨140, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨6, by decide⟩ ⟨140, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨7, by decide⟩ ⟨140, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨8, by decide⟩ ⟨140, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨9, by decide⟩ ⟨140, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨10, by decide⟩ ⟨140, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨11, by decide⟩ ⟨140, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨12, by decide⟩ ⟨140, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨13, by decide⟩ ⟨140, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨14, by decide⟩ ⟨140, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨15, by decide⟩ ⟨140, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨16, by decide⟩ ⟨140, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨17, by decide⟩ ⟨140, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨18, by decide⟩ ⟨140, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨19, by decide⟩ ⟨140, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨20, by decide⟩ ⟨140, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨21, by decide⟩ ⟨140, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨22, by decide⟩ ⟨140, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨23, by decide⟩ ⟨140, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨24, by decide⟩ ⟨140, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨25, by decide⟩ ⟨140, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨26, by decide⟩ ⟨140, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨27, by decide⟩ ⟨140, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨28, by decide⟩ ⟨140, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨29, by decide⟩ ⟨140, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨30, by decide⟩ ⟨140, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨31, by decide⟩ ⟨140, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨32, by decide⟩ ⟨140, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨33, by decide⟩ ⟨140, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨34, by decide⟩ ⟨140, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨35, by decide⟩ ⟨140, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨36, by decide⟩ ⟨140, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨37, by decide⟩ ⟨140, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨38, by decide⟩ ⟨140, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨39, by decide⟩ ⟨140, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨40, by decide⟩ ⟨140, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨41, by decide⟩ ⟨140, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨42, by decide⟩ ⟨140, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨43, by decide⟩ ⟨140, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨44, by decide⟩ ⟨140, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨45, by decide⟩ ⟨140, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨46, by decide⟩ ⟨140, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨47, by decide⟩ ⟨140, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨48, by decide⟩ ⟨140, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨49, by decide⟩ ⟨140, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨50, by decide⟩ ⟨140, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨51, by decide⟩ ⟨140, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨52, by decide⟩ ⟨140, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨53, by decide⟩ ⟨140, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨54, by decide⟩ ⟨140, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨55, by decide⟩ ⟨140, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨56, by decide⟩ ⟨140, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨57, by decide⟩ ⟨140, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨58, by decide⟩ ⟨140, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨59, by decide⟩ ⟨140, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨60, by decide⟩ ⟨140, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨61, by decide⟩ ⟨140, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨62, by decide⟩ ⟨140, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨63, by decide⟩ ⟨140, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨64, by decide⟩ ⟨140, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨65, by decide⟩ ⟨140, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨66, by decide⟩ ⟨140, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨67, by decide⟩ ⟨140, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨68, by decide⟩ ⟨140, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨69, by decide⟩ ⟨140, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨70, by decide⟩ ⟨140, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨71, by decide⟩ ⟨140, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨72, by decide⟩ ⟨140, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨73, by decide⟩ ⟨140, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨74, by decide⟩ ⟨140, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨75, by decide⟩ ⟨140, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨76, by decide⟩ ⟨140, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨77, by decide⟩ ⟨140, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨78, by decide⟩ ⟨140, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨79, by decide⟩ ⟨140, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨80, by decide⟩ ⟨140, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨81, by decide⟩ ⟨140, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨82, by decide⟩ ⟨140, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨83, by decide⟩ ⟨140, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨84, by decide⟩ ⟨140, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨85, by decide⟩ ⟨140, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨86, by decide⟩ ⟨140, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨87, by decide⟩ ⟨140, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨88, by decide⟩ ⟨140, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨89, by decide⟩ ⟨140, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨90, by decide⟩ ⟨140, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨91, by decide⟩ ⟨140, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨92, by decide⟩ ⟨140, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨93, by decide⟩ ⟨140, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨94, by decide⟩ ⟨140, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨95, by decide⟩ ⟨140, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨96, by decide⟩ ⟨140, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨97, by decide⟩ ⟨140, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨98, by decide⟩ ⟨140, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨99, by decide⟩ ⟨140, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨100, by decide⟩ ⟨140, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨101, by decide⟩ ⟨140, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨102, by decide⟩ ⟨140, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨103, by decide⟩ ⟨140, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨104, by decide⟩ ⟨140, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨105, by decide⟩ ⟨140, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨106, by decide⟩ ⟨140, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨107, by decide⟩ ⟨140, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨108, by decide⟩ ⟨140, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨109, by decide⟩ ⟨140, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨110, by decide⟩ ⟨140, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨111, by decide⟩ ⟨140, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨112, by decide⟩ ⟨140, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨113, by decide⟩ ⟨140, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨114, by decide⟩ ⟨140, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨115, by decide⟩ ⟨140, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_fix ⟨116, by decide⟩ ⟨140, by decide⟩ p hp j hj hq fz1_116_140 fz2_116_140
  · exact match_zero_fix ⟨117, by decide⟩ ⟨140, by decide⟩ p hp j hj hq fz1_117_140 fz2_117_140
  · exact match_zero_fix ⟨118, by decide⟩ ⟨140, by decide⟩ p hp j hj hq fz1_118_140 fz2_118_140
  · exact match_zero_fix ⟨119, by decide⟩ ⟨140, by decide⟩ p hp j hj hq fz1_119_140 fz2_119_140
  · exact match_zero_fix ⟨120, by decide⟩ ⟨140, by decide⟩ p hp j hj hq fz1_120_140 fz2_120_140
  · exact match_zero_fix ⟨121, by decide⟩ ⟨140, by decide⟩ p hp j hj hq fz1_121_140 fz2_121_140
  · exact match_zero_fix ⟨122, by decide⟩ ⟨140, by decide⟩ p hp j hj hq fz1_122_140 fz2_122_140
  · exact match_zero_fix ⟨123, by decide⟩ ⟨140, by decide⟩ p hp j hj hq fz1_123_140 fz2_123_140
  · exact match_zero_fix ⟨124, by decide⟩ ⟨140, by decide⟩ p hp j hj hq fz1_124_140 fz2_124_140
  · exact match_zero_fix ⟨125, by decide⟩ ⟨140, by decide⟩ p hp j hj hq fz1_125_140 fz2_125_140
  · exact match_zero_fix ⟨126, by decide⟩ ⟨140, by decide⟩ p hp j hj hq fz1_126_140 fz2_126_140
  · exact match_zero_fix ⟨127, by decide⟩ ⟨140, by decide⟩ p hp j hj hq fz1_127_140 fz2_127_140
  · exact match_zero_fix ⟨128, by decide⟩ ⟨140, by decide⟩ p hp j hj hq fz1_128_140 fz2_128_140
  · exact match_zero_fix ⟨129, by decide⟩ ⟨140, by decide⟩ p hp j hj hq fz1_129_140 fz2_129_140
  · exact match_zero_fix ⟨130, by decide⟩ ⟨140, by decide⟩ p hp j hj hq fz1_130_140 fz2_130_140
  · exact match_zero_fix ⟨131, by decide⟩ ⟨140, by decide⟩ p hp j hj hq fz1_131_140 fz2_131_140
  · exact match_zero_fix ⟨132, by decide⟩ ⟨140, by decide⟩ p hp j hj hq fz1_132_140 fz2_132_140
  · exact match_zero_fix ⟨133, by decide⟩ ⟨140, by decide⟩ p hp j hj hq fz1_133_140 fz2_133_140
  · exact match_zero_fix ⟨134, by decide⟩ ⟨140, by decide⟩ p hp j hj hq fz1_134_140 fz2_134_140
  · exact match_zero_fix ⟨135, by decide⟩ ⟨140, by decide⟩ p hp j hj hq fz1_135_140 fz2_135_140
  · exact match_zero_fix ⟨136, by decide⟩ ⟨140, by decide⟩ p hp j hj hq fz1_136_140 fz2_136_140
  · exact match_zero_fix ⟨137, by decide⟩ ⟨140, by decide⟩ p hp j hj hq fz1_137_140 fz2_137_140
  · exact match_zero_fix ⟨138, by decide⟩ ⟨140, by decide⟩ p hp j hj hq fz1_138_140 fz2_138_140
  · exact match_zero_fix ⟨139, by decide⟩ ⟨140, by decide⟩ p hp j hj hq fz1_139_140 fz2_139_140
  · exact pair_140_140 p hp hrep j hj hq
  · exact match_zero_fix ⟨141, by decide⟩ ⟨140, by decide⟩ p hp j hj hq fz1_141_140 fz2_141_140
  · exact match_zero_fix ⟨142, by decide⟩ ⟨140, by decide⟩ p hp j hj hq fz1_142_140 fz2_142_140
  · exact match_zero_fix ⟨143, by decide⟩ ⟨140, by decide⟩ p hp j hj hq fz1_143_140 fz2_143_140
  · exact match_zero_fix ⟨144, by decide⟩ ⟨140, by decide⟩ p hp j hj hq fz1_144_140 fz2_144_140
  · exact match_zero_fix ⟨145, by decide⟩ ⟨140, by decide⟩ p hp j hj hq fz1_145_140 fz2_145_140
  · exact match_zero_fix ⟨146, by decide⟩ ⟨140, by decide⟩ p hp j hj hq fz1_146_140 fz2_146_140
  · exact pair_147_140 p hp hrep j hj hq

theorem master_141 (p : Nat) (hp : p < (Q2.transData.getD 141 []).length)
    (hrep : (Q2.cosetIsRep.getD 141 []).getD p false = true)
    (rK : Fin 148) (j : Nat) (hj : j < (repChars.getD rK.val []).length)
    (hq : (normIsRep.getD rK.val []).getD j false = true) :
    species (Q2.reps (⟨141, by decide⟩ : Fin 148)) (colE2 ⟨141, by decide⟩ p hp)
        (rowE2 rK j hj hq)
      = species (reps (⟨141, by decide⟩ : Fin 148))
        (colE1 ⟨141, by decide⟩ p (transLenTr ⟨141, by decide⟩ p hp)) (rowE1 rK j hj) := by
  rcases rK with ⟨nK, hnK⟩; interval_cases nK
  · exact match_zero_len ⟨0, by decide⟩ ⟨141, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨1, by decide⟩ ⟨141, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨2, by decide⟩ ⟨141, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨3, by decide⟩ ⟨141, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨4, by decide⟩ ⟨141, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨5, by decide⟩ ⟨141, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨6, by decide⟩ ⟨141, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨7, by decide⟩ ⟨141, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨8, by decide⟩ ⟨141, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨9, by decide⟩ ⟨141, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨10, by decide⟩ ⟨141, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨11, by decide⟩ ⟨141, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨12, by decide⟩ ⟨141, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨13, by decide⟩ ⟨141, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨14, by decide⟩ ⟨141, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨15, by decide⟩ ⟨141, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨16, by decide⟩ ⟨141, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨17, by decide⟩ ⟨141, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨18, by decide⟩ ⟨141, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨19, by decide⟩ ⟨141, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨20, by decide⟩ ⟨141, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨21, by decide⟩ ⟨141, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨22, by decide⟩ ⟨141, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨23, by decide⟩ ⟨141, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨24, by decide⟩ ⟨141, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨25, by decide⟩ ⟨141, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨26, by decide⟩ ⟨141, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨27, by decide⟩ ⟨141, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨28, by decide⟩ ⟨141, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨29, by decide⟩ ⟨141, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨30, by decide⟩ ⟨141, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨31, by decide⟩ ⟨141, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨32, by decide⟩ ⟨141, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨33, by decide⟩ ⟨141, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨34, by decide⟩ ⟨141, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨35, by decide⟩ ⟨141, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨36, by decide⟩ ⟨141, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨37, by decide⟩ ⟨141, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨38, by decide⟩ ⟨141, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨39, by decide⟩ ⟨141, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨40, by decide⟩ ⟨141, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨41, by decide⟩ ⟨141, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨42, by decide⟩ ⟨141, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨43, by decide⟩ ⟨141, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨44, by decide⟩ ⟨141, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨45, by decide⟩ ⟨141, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨46, by decide⟩ ⟨141, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨47, by decide⟩ ⟨141, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨48, by decide⟩ ⟨141, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨49, by decide⟩ ⟨141, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨50, by decide⟩ ⟨141, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨51, by decide⟩ ⟨141, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨52, by decide⟩ ⟨141, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨53, by decide⟩ ⟨141, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨54, by decide⟩ ⟨141, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨55, by decide⟩ ⟨141, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨56, by decide⟩ ⟨141, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨57, by decide⟩ ⟨141, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨58, by decide⟩ ⟨141, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨59, by decide⟩ ⟨141, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨60, by decide⟩ ⟨141, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨61, by decide⟩ ⟨141, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨62, by decide⟩ ⟨141, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨63, by decide⟩ ⟨141, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨64, by decide⟩ ⟨141, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨65, by decide⟩ ⟨141, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨66, by decide⟩ ⟨141, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨67, by decide⟩ ⟨141, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨68, by decide⟩ ⟨141, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨69, by decide⟩ ⟨141, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨70, by decide⟩ ⟨141, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨71, by decide⟩ ⟨141, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨72, by decide⟩ ⟨141, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨73, by decide⟩ ⟨141, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨74, by decide⟩ ⟨141, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨75, by decide⟩ ⟨141, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨76, by decide⟩ ⟨141, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨77, by decide⟩ ⟨141, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨78, by decide⟩ ⟨141, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨79, by decide⟩ ⟨141, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨80, by decide⟩ ⟨141, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨81, by decide⟩ ⟨141, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨82, by decide⟩ ⟨141, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨83, by decide⟩ ⟨141, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨84, by decide⟩ ⟨141, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨85, by decide⟩ ⟨141, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨86, by decide⟩ ⟨141, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨87, by decide⟩ ⟨141, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨88, by decide⟩ ⟨141, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨89, by decide⟩ ⟨141, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨90, by decide⟩ ⟨141, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨91, by decide⟩ ⟨141, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨92, by decide⟩ ⟨141, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨93, by decide⟩ ⟨141, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨94, by decide⟩ ⟨141, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨95, by decide⟩ ⟨141, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨96, by decide⟩ ⟨141, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨97, by decide⟩ ⟨141, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨98, by decide⟩ ⟨141, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨99, by decide⟩ ⟨141, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨100, by decide⟩ ⟨141, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨101, by decide⟩ ⟨141, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨102, by decide⟩ ⟨141, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨103, by decide⟩ ⟨141, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨104, by decide⟩ ⟨141, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨105, by decide⟩ ⟨141, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨106, by decide⟩ ⟨141, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨107, by decide⟩ ⟨141, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨108, by decide⟩ ⟨141, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨109, by decide⟩ ⟨141, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨110, by decide⟩ ⟨141, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨111, by decide⟩ ⟨141, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨112, by decide⟩ ⟨141, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨113, by decide⟩ ⟨141, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨114, by decide⟩ ⟨141, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨115, by decide⟩ ⟨141, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_fix ⟨116, by decide⟩ ⟨141, by decide⟩ p hp j hj hq fz1_116_141 fz2_116_141
  · exact match_zero_fix ⟨117, by decide⟩ ⟨141, by decide⟩ p hp j hj hq fz1_117_141 fz2_117_141
  · exact match_zero_fix ⟨118, by decide⟩ ⟨141, by decide⟩ p hp j hj hq fz1_118_141 fz2_118_141
  · exact match_zero_fix ⟨119, by decide⟩ ⟨141, by decide⟩ p hp j hj hq fz1_119_141 fz2_119_141
  · exact match_zero_fix ⟨120, by decide⟩ ⟨141, by decide⟩ p hp j hj hq fz1_120_141 fz2_120_141
  · exact match_zero_fix ⟨121, by decide⟩ ⟨141, by decide⟩ p hp j hj hq fz1_121_141 fz2_121_141
  · exact match_zero_fix ⟨122, by decide⟩ ⟨141, by decide⟩ p hp j hj hq fz1_122_141 fz2_122_141
  · exact match_zero_fix ⟨123, by decide⟩ ⟨141, by decide⟩ p hp j hj hq fz1_123_141 fz2_123_141
  · exact match_zero_fix ⟨124, by decide⟩ ⟨141, by decide⟩ p hp j hj hq fz1_124_141 fz2_124_141
  · exact match_zero_fix ⟨125, by decide⟩ ⟨141, by decide⟩ p hp j hj hq fz1_125_141 fz2_125_141
  · exact match_zero_fix ⟨126, by decide⟩ ⟨141, by decide⟩ p hp j hj hq fz1_126_141 fz2_126_141
  · exact match_zero_fix ⟨127, by decide⟩ ⟨141, by decide⟩ p hp j hj hq fz1_127_141 fz2_127_141
  · exact match_zero_fix ⟨128, by decide⟩ ⟨141, by decide⟩ p hp j hj hq fz1_128_141 fz2_128_141
  · exact match_zero_fix ⟨129, by decide⟩ ⟨141, by decide⟩ p hp j hj hq fz1_129_141 fz2_129_141
  · exact match_zero_fix ⟨130, by decide⟩ ⟨141, by decide⟩ p hp j hj hq fz1_130_141 fz2_130_141
  · exact match_zero_fix ⟨131, by decide⟩ ⟨141, by decide⟩ p hp j hj hq fz1_131_141 fz2_131_141
  · exact match_zero_fix ⟨132, by decide⟩ ⟨141, by decide⟩ p hp j hj hq fz1_132_141 fz2_132_141
  · exact match_zero_fix ⟨133, by decide⟩ ⟨141, by decide⟩ p hp j hj hq fz1_133_141 fz2_133_141
  · exact match_zero_fix ⟨134, by decide⟩ ⟨141, by decide⟩ p hp j hj hq fz1_134_141 fz2_134_141
  · exact match_zero_fix ⟨135, by decide⟩ ⟨141, by decide⟩ p hp j hj hq fz1_135_141 fz2_135_141
  · exact match_zero_fix ⟨136, by decide⟩ ⟨141, by decide⟩ p hp j hj hq fz1_136_141 fz2_136_141
  · exact match_zero_fix ⟨137, by decide⟩ ⟨141, by decide⟩ p hp j hj hq fz1_137_141 fz2_137_141
  · exact match_zero_fix ⟨138, by decide⟩ ⟨141, by decide⟩ p hp j hj hq fz1_138_141 fz2_138_141
  · exact match_zero_fix ⟨139, by decide⟩ ⟨141, by decide⟩ p hp j hj hq fz1_139_141 fz2_139_141
  · exact match_zero_fix ⟨140, by decide⟩ ⟨141, by decide⟩ p hp j hj hq fz1_140_141 fz2_140_141
  · exact pair_141_141 p hp hrep j hj hq
  · exact match_zero_fix ⟨142, by decide⟩ ⟨141, by decide⟩ p hp j hj hq fz1_142_141 fz2_142_141
  · exact match_zero_fix ⟨143, by decide⟩ ⟨141, by decide⟩ p hp j hj hq fz1_143_141 fz2_143_141
  · exact match_zero_fix ⟨144, by decide⟩ ⟨141, by decide⟩ p hp j hj hq fz1_144_141 fz2_144_141
  · exact match_zero_fix ⟨145, by decide⟩ ⟨141, by decide⟩ p hp j hj hq fz1_145_141 fz2_145_141
  · exact match_zero_fix ⟨146, by decide⟩ ⟨141, by decide⟩ p hp j hj hq fz1_146_141 fz2_146_141
  · exact pair_147_141 p hp hrep j hj hq

theorem master_142 (p : Nat) (hp : p < (Q2.transData.getD 142 []).length)
    (hrep : (Q2.cosetIsRep.getD 142 []).getD p false = true)
    (rK : Fin 148) (j : Nat) (hj : j < (repChars.getD rK.val []).length)
    (hq : (normIsRep.getD rK.val []).getD j false = true) :
    species (Q2.reps (⟨142, by decide⟩ : Fin 148)) (colE2 ⟨142, by decide⟩ p hp)
        (rowE2 rK j hj hq)
      = species (reps (⟨142, by decide⟩ : Fin 148))
        (colE1 ⟨142, by decide⟩ p (transLenTr ⟨142, by decide⟩ p hp)) (rowE1 rK j hj) := by
  rcases rK with ⟨nK, hnK⟩; interval_cases nK
  · exact match_zero_len ⟨0, by decide⟩ ⟨142, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨1, by decide⟩ ⟨142, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨2, by decide⟩ ⟨142, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨3, by decide⟩ ⟨142, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨4, by decide⟩ ⟨142, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨5, by decide⟩ ⟨142, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨6, by decide⟩ ⟨142, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨7, by decide⟩ ⟨142, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨8, by decide⟩ ⟨142, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨9, by decide⟩ ⟨142, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨10, by decide⟩ ⟨142, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨11, by decide⟩ ⟨142, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨12, by decide⟩ ⟨142, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨13, by decide⟩ ⟨142, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨14, by decide⟩ ⟨142, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨15, by decide⟩ ⟨142, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨16, by decide⟩ ⟨142, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨17, by decide⟩ ⟨142, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨18, by decide⟩ ⟨142, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨19, by decide⟩ ⟨142, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨20, by decide⟩ ⟨142, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨21, by decide⟩ ⟨142, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨22, by decide⟩ ⟨142, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨23, by decide⟩ ⟨142, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨24, by decide⟩ ⟨142, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨25, by decide⟩ ⟨142, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨26, by decide⟩ ⟨142, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨27, by decide⟩ ⟨142, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨28, by decide⟩ ⟨142, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨29, by decide⟩ ⟨142, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨30, by decide⟩ ⟨142, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨31, by decide⟩ ⟨142, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨32, by decide⟩ ⟨142, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨33, by decide⟩ ⟨142, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨34, by decide⟩ ⟨142, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨35, by decide⟩ ⟨142, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨36, by decide⟩ ⟨142, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨37, by decide⟩ ⟨142, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨38, by decide⟩ ⟨142, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨39, by decide⟩ ⟨142, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨40, by decide⟩ ⟨142, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨41, by decide⟩ ⟨142, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨42, by decide⟩ ⟨142, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨43, by decide⟩ ⟨142, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨44, by decide⟩ ⟨142, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨45, by decide⟩ ⟨142, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨46, by decide⟩ ⟨142, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨47, by decide⟩ ⟨142, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨48, by decide⟩ ⟨142, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨49, by decide⟩ ⟨142, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨50, by decide⟩ ⟨142, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨51, by decide⟩ ⟨142, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨52, by decide⟩ ⟨142, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨53, by decide⟩ ⟨142, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨54, by decide⟩ ⟨142, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨55, by decide⟩ ⟨142, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨56, by decide⟩ ⟨142, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨57, by decide⟩ ⟨142, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨58, by decide⟩ ⟨142, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨59, by decide⟩ ⟨142, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨60, by decide⟩ ⟨142, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨61, by decide⟩ ⟨142, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨62, by decide⟩ ⟨142, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨63, by decide⟩ ⟨142, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨64, by decide⟩ ⟨142, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨65, by decide⟩ ⟨142, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨66, by decide⟩ ⟨142, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨67, by decide⟩ ⟨142, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨68, by decide⟩ ⟨142, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨69, by decide⟩ ⟨142, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨70, by decide⟩ ⟨142, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨71, by decide⟩ ⟨142, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨72, by decide⟩ ⟨142, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨73, by decide⟩ ⟨142, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨74, by decide⟩ ⟨142, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨75, by decide⟩ ⟨142, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨76, by decide⟩ ⟨142, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨77, by decide⟩ ⟨142, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨78, by decide⟩ ⟨142, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨79, by decide⟩ ⟨142, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨80, by decide⟩ ⟨142, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨81, by decide⟩ ⟨142, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨82, by decide⟩ ⟨142, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨83, by decide⟩ ⟨142, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨84, by decide⟩ ⟨142, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨85, by decide⟩ ⟨142, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨86, by decide⟩ ⟨142, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨87, by decide⟩ ⟨142, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨88, by decide⟩ ⟨142, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨89, by decide⟩ ⟨142, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨90, by decide⟩ ⟨142, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨91, by decide⟩ ⟨142, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨92, by decide⟩ ⟨142, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨93, by decide⟩ ⟨142, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨94, by decide⟩ ⟨142, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨95, by decide⟩ ⟨142, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨96, by decide⟩ ⟨142, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨97, by decide⟩ ⟨142, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨98, by decide⟩ ⟨142, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨99, by decide⟩ ⟨142, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨100, by decide⟩ ⟨142, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨101, by decide⟩ ⟨142, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨102, by decide⟩ ⟨142, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨103, by decide⟩ ⟨142, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨104, by decide⟩ ⟨142, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨105, by decide⟩ ⟨142, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨106, by decide⟩ ⟨142, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨107, by decide⟩ ⟨142, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨108, by decide⟩ ⟨142, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨109, by decide⟩ ⟨142, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨110, by decide⟩ ⟨142, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨111, by decide⟩ ⟨142, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨112, by decide⟩ ⟨142, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨113, by decide⟩ ⟨142, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨114, by decide⟩ ⟨142, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨115, by decide⟩ ⟨142, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_fix ⟨116, by decide⟩ ⟨142, by decide⟩ p hp j hj hq fz1_116_142 fz2_116_142
  · exact match_zero_fix ⟨117, by decide⟩ ⟨142, by decide⟩ p hp j hj hq fz1_117_142 fz2_117_142
  · exact match_zero_fix ⟨118, by decide⟩ ⟨142, by decide⟩ p hp j hj hq fz1_118_142 fz2_118_142
  · exact match_zero_fix ⟨119, by decide⟩ ⟨142, by decide⟩ p hp j hj hq fz1_119_142 fz2_119_142
  · exact match_zero_fix ⟨120, by decide⟩ ⟨142, by decide⟩ p hp j hj hq fz1_120_142 fz2_120_142
  · exact match_zero_fix ⟨121, by decide⟩ ⟨142, by decide⟩ p hp j hj hq fz1_121_142 fz2_121_142
  · exact match_zero_fix ⟨122, by decide⟩ ⟨142, by decide⟩ p hp j hj hq fz1_122_142 fz2_122_142
  · exact match_zero_fix ⟨123, by decide⟩ ⟨142, by decide⟩ p hp j hj hq fz1_123_142 fz2_123_142
  · exact match_zero_fix ⟨124, by decide⟩ ⟨142, by decide⟩ p hp j hj hq fz1_124_142 fz2_124_142
  · exact match_zero_fix ⟨125, by decide⟩ ⟨142, by decide⟩ p hp j hj hq fz1_125_142 fz2_125_142
  · exact match_zero_fix ⟨126, by decide⟩ ⟨142, by decide⟩ p hp j hj hq fz1_126_142 fz2_126_142
  · exact match_zero_fix ⟨127, by decide⟩ ⟨142, by decide⟩ p hp j hj hq fz1_127_142 fz2_127_142
  · exact match_zero_fix ⟨128, by decide⟩ ⟨142, by decide⟩ p hp j hj hq fz1_128_142 fz2_128_142
  · exact match_zero_fix ⟨129, by decide⟩ ⟨142, by decide⟩ p hp j hj hq fz1_129_142 fz2_129_142
  · exact match_zero_fix ⟨130, by decide⟩ ⟨142, by decide⟩ p hp j hj hq fz1_130_142 fz2_130_142
  · exact match_zero_fix ⟨131, by decide⟩ ⟨142, by decide⟩ p hp j hj hq fz1_131_142 fz2_131_142
  · exact match_zero_fix ⟨132, by decide⟩ ⟨142, by decide⟩ p hp j hj hq fz1_132_142 fz2_132_142
  · exact match_zero_fix ⟨133, by decide⟩ ⟨142, by decide⟩ p hp j hj hq fz1_133_142 fz2_133_142
  · exact match_zero_fix ⟨134, by decide⟩ ⟨142, by decide⟩ p hp j hj hq fz1_134_142 fz2_134_142
  · exact match_zero_fix ⟨135, by decide⟩ ⟨142, by decide⟩ p hp j hj hq fz1_135_142 fz2_135_142
  · exact match_zero_fix ⟨136, by decide⟩ ⟨142, by decide⟩ p hp j hj hq fz1_136_142 fz2_136_142
  · exact match_zero_fix ⟨137, by decide⟩ ⟨142, by decide⟩ p hp j hj hq fz1_137_142 fz2_137_142
  · exact match_zero_fix ⟨138, by decide⟩ ⟨142, by decide⟩ p hp j hj hq fz1_138_142 fz2_138_142
  · exact match_zero_fix ⟨139, by decide⟩ ⟨142, by decide⟩ p hp j hj hq fz1_139_142 fz2_139_142
  · exact match_zero_fix ⟨140, by decide⟩ ⟨142, by decide⟩ p hp j hj hq fz1_140_142 fz2_140_142
  · exact match_zero_fix ⟨141, by decide⟩ ⟨142, by decide⟩ p hp j hj hq fz1_141_142 fz2_141_142
  · exact pair_142_142 p hp hrep j hj hq
  · exact match_zero_fix ⟨143, by decide⟩ ⟨142, by decide⟩ p hp j hj hq fz1_143_142 fz2_143_142
  · exact match_zero_fix ⟨144, by decide⟩ ⟨142, by decide⟩ p hp j hj hq fz1_144_142 fz2_144_142
  · exact match_zero_fix ⟨145, by decide⟩ ⟨142, by decide⟩ p hp j hj hq fz1_145_142 fz2_145_142
  · exact match_zero_fix ⟨146, by decide⟩ ⟨142, by decide⟩ p hp j hj hq fz1_146_142 fz2_146_142
  · exact pair_147_142 p hp hrep j hj hq

theorem master_143 (p : Nat) (hp : p < (Q2.transData.getD 143 []).length)
    (hrep : (Q2.cosetIsRep.getD 143 []).getD p false = true)
    (rK : Fin 148) (j : Nat) (hj : j < (repChars.getD rK.val []).length)
    (hq : (normIsRep.getD rK.val []).getD j false = true) :
    species (Q2.reps (⟨143, by decide⟩ : Fin 148)) (colE2 ⟨143, by decide⟩ p hp)
        (rowE2 rK j hj hq)
      = species (reps (⟨143, by decide⟩ : Fin 148))
        (colE1 ⟨143, by decide⟩ p (transLenTr ⟨143, by decide⟩ p hp)) (rowE1 rK j hj) := by
  rcases rK with ⟨nK, hnK⟩; interval_cases nK
  · exact match_zero_len ⟨0, by decide⟩ ⟨143, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨1, by decide⟩ ⟨143, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨2, by decide⟩ ⟨143, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨3, by decide⟩ ⟨143, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨4, by decide⟩ ⟨143, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨5, by decide⟩ ⟨143, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨6, by decide⟩ ⟨143, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨7, by decide⟩ ⟨143, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨8, by decide⟩ ⟨143, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨9, by decide⟩ ⟨143, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨10, by decide⟩ ⟨143, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨11, by decide⟩ ⟨143, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨12, by decide⟩ ⟨143, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨13, by decide⟩ ⟨143, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨14, by decide⟩ ⟨143, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨15, by decide⟩ ⟨143, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨16, by decide⟩ ⟨143, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨17, by decide⟩ ⟨143, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨18, by decide⟩ ⟨143, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨19, by decide⟩ ⟨143, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨20, by decide⟩ ⟨143, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨21, by decide⟩ ⟨143, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨22, by decide⟩ ⟨143, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨23, by decide⟩ ⟨143, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨24, by decide⟩ ⟨143, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨25, by decide⟩ ⟨143, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨26, by decide⟩ ⟨143, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨27, by decide⟩ ⟨143, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨28, by decide⟩ ⟨143, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨29, by decide⟩ ⟨143, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨30, by decide⟩ ⟨143, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨31, by decide⟩ ⟨143, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨32, by decide⟩ ⟨143, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨33, by decide⟩ ⟨143, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨34, by decide⟩ ⟨143, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨35, by decide⟩ ⟨143, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨36, by decide⟩ ⟨143, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨37, by decide⟩ ⟨143, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨38, by decide⟩ ⟨143, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨39, by decide⟩ ⟨143, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨40, by decide⟩ ⟨143, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨41, by decide⟩ ⟨143, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨42, by decide⟩ ⟨143, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨43, by decide⟩ ⟨143, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨44, by decide⟩ ⟨143, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨45, by decide⟩ ⟨143, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨46, by decide⟩ ⟨143, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨47, by decide⟩ ⟨143, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨48, by decide⟩ ⟨143, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨49, by decide⟩ ⟨143, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨50, by decide⟩ ⟨143, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨51, by decide⟩ ⟨143, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨52, by decide⟩ ⟨143, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨53, by decide⟩ ⟨143, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨54, by decide⟩ ⟨143, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨55, by decide⟩ ⟨143, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨56, by decide⟩ ⟨143, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨57, by decide⟩ ⟨143, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨58, by decide⟩ ⟨143, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨59, by decide⟩ ⟨143, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨60, by decide⟩ ⟨143, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨61, by decide⟩ ⟨143, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨62, by decide⟩ ⟨143, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨63, by decide⟩ ⟨143, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨64, by decide⟩ ⟨143, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨65, by decide⟩ ⟨143, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨66, by decide⟩ ⟨143, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨67, by decide⟩ ⟨143, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨68, by decide⟩ ⟨143, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨69, by decide⟩ ⟨143, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨70, by decide⟩ ⟨143, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨71, by decide⟩ ⟨143, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨72, by decide⟩ ⟨143, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨73, by decide⟩ ⟨143, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨74, by decide⟩ ⟨143, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨75, by decide⟩ ⟨143, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨76, by decide⟩ ⟨143, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨77, by decide⟩ ⟨143, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨78, by decide⟩ ⟨143, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨79, by decide⟩ ⟨143, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨80, by decide⟩ ⟨143, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨81, by decide⟩ ⟨143, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨82, by decide⟩ ⟨143, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨83, by decide⟩ ⟨143, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨84, by decide⟩ ⟨143, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨85, by decide⟩ ⟨143, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨86, by decide⟩ ⟨143, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨87, by decide⟩ ⟨143, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨88, by decide⟩ ⟨143, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨89, by decide⟩ ⟨143, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨90, by decide⟩ ⟨143, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨91, by decide⟩ ⟨143, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨92, by decide⟩ ⟨143, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨93, by decide⟩ ⟨143, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨94, by decide⟩ ⟨143, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨95, by decide⟩ ⟨143, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨96, by decide⟩ ⟨143, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨97, by decide⟩ ⟨143, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨98, by decide⟩ ⟨143, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨99, by decide⟩ ⟨143, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨100, by decide⟩ ⟨143, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨101, by decide⟩ ⟨143, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨102, by decide⟩ ⟨143, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨103, by decide⟩ ⟨143, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨104, by decide⟩ ⟨143, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨105, by decide⟩ ⟨143, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨106, by decide⟩ ⟨143, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨107, by decide⟩ ⟨143, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨108, by decide⟩ ⟨143, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨109, by decide⟩ ⟨143, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨110, by decide⟩ ⟨143, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨111, by decide⟩ ⟨143, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨112, by decide⟩ ⟨143, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨113, by decide⟩ ⟨143, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨114, by decide⟩ ⟨143, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨115, by decide⟩ ⟨143, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_fix ⟨116, by decide⟩ ⟨143, by decide⟩ p hp j hj hq fz1_116_143 fz2_116_143
  · exact match_zero_fix ⟨117, by decide⟩ ⟨143, by decide⟩ p hp j hj hq fz1_117_143 fz2_117_143
  · exact match_zero_fix ⟨118, by decide⟩ ⟨143, by decide⟩ p hp j hj hq fz1_118_143 fz2_118_143
  · exact match_zero_fix ⟨119, by decide⟩ ⟨143, by decide⟩ p hp j hj hq fz1_119_143 fz2_119_143
  · exact match_zero_fix ⟨120, by decide⟩ ⟨143, by decide⟩ p hp j hj hq fz1_120_143 fz2_120_143
  · exact match_zero_fix ⟨121, by decide⟩ ⟨143, by decide⟩ p hp j hj hq fz1_121_143 fz2_121_143
  · exact match_zero_fix ⟨122, by decide⟩ ⟨143, by decide⟩ p hp j hj hq fz1_122_143 fz2_122_143
  · exact match_zero_fix ⟨123, by decide⟩ ⟨143, by decide⟩ p hp j hj hq fz1_123_143 fz2_123_143
  · exact match_zero_fix ⟨124, by decide⟩ ⟨143, by decide⟩ p hp j hj hq fz1_124_143 fz2_124_143
  · exact match_zero_fix ⟨125, by decide⟩ ⟨143, by decide⟩ p hp j hj hq fz1_125_143 fz2_125_143
  · exact match_zero_fix ⟨126, by decide⟩ ⟨143, by decide⟩ p hp j hj hq fz1_126_143 fz2_126_143
  · exact match_zero_fix ⟨127, by decide⟩ ⟨143, by decide⟩ p hp j hj hq fz1_127_143 fz2_127_143
  · exact match_zero_fix ⟨128, by decide⟩ ⟨143, by decide⟩ p hp j hj hq fz1_128_143 fz2_128_143
  · exact match_zero_fix ⟨129, by decide⟩ ⟨143, by decide⟩ p hp j hj hq fz1_129_143 fz2_129_143
  · exact match_zero_fix ⟨130, by decide⟩ ⟨143, by decide⟩ p hp j hj hq fz1_130_143 fz2_130_143
  · exact match_zero_fix ⟨131, by decide⟩ ⟨143, by decide⟩ p hp j hj hq fz1_131_143 fz2_131_143
  · exact match_zero_fix ⟨132, by decide⟩ ⟨143, by decide⟩ p hp j hj hq fz1_132_143 fz2_132_143
  · exact match_zero_fix ⟨133, by decide⟩ ⟨143, by decide⟩ p hp j hj hq fz1_133_143 fz2_133_143
  · exact match_zero_fix ⟨134, by decide⟩ ⟨143, by decide⟩ p hp j hj hq fz1_134_143 fz2_134_143
  · exact match_zero_fix ⟨135, by decide⟩ ⟨143, by decide⟩ p hp j hj hq fz1_135_143 fz2_135_143
  · exact match_zero_fix ⟨136, by decide⟩ ⟨143, by decide⟩ p hp j hj hq fz1_136_143 fz2_136_143
  · exact match_zero_fix ⟨137, by decide⟩ ⟨143, by decide⟩ p hp j hj hq fz1_137_143 fz2_137_143
  · exact match_zero_fix ⟨138, by decide⟩ ⟨143, by decide⟩ p hp j hj hq fz1_138_143 fz2_138_143
  · exact match_zero_fix ⟨139, by decide⟩ ⟨143, by decide⟩ p hp j hj hq fz1_139_143 fz2_139_143
  · exact match_zero_fix ⟨140, by decide⟩ ⟨143, by decide⟩ p hp j hj hq fz1_140_143 fz2_140_143
  · exact match_zero_fix ⟨141, by decide⟩ ⟨143, by decide⟩ p hp j hj hq fz1_141_143 fz2_141_143
  · exact match_zero_fix ⟨142, by decide⟩ ⟨143, by decide⟩ p hp j hj hq fz1_142_143 fz2_142_143
  · exact pair_143_143 p hp hrep j hj hq
  · exact match_zero_fix ⟨144, by decide⟩ ⟨143, by decide⟩ p hp j hj hq fz1_144_143 fz2_144_143
  · exact match_zero_fix ⟨145, by decide⟩ ⟨143, by decide⟩ p hp j hj hq fz1_145_143 fz2_145_143
  · exact match_zero_fix ⟨146, by decide⟩ ⟨143, by decide⟩ p hp j hj hq fz1_146_143 fz2_146_143
  · exact pair_147_143 p hp hrep j hj hq

end LeanDring.P5Presentation
