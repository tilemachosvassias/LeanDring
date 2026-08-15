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
import LeanDring.P5.Data.MatchPair.C011
import LeanDring.P5.Data.MatchPair.C012
import LeanDring.P5.Data.MatchPair.C010

/-! # Stage-5 per-column-class master theorems, chunk 18 (auto-emitted).  -/

namespace LeanDring.P5Presentation

open MulAction Finset LeanDring.DRing LeanDring.MonGSet

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.style.longLine false

theorem master_144 (p : Nat) (hp : p < (Q2.transData.getD 144 []).length)
    (hrep : (Q2.cosetIsRep.getD 144 []).getD p false = true)
    (rK : Fin 148) (j : Nat) (hj : j < (repChars.getD rK.val []).length)
    (hq : (normIsRep.getD rK.val []).getD j false = true) :
    species (Q2.reps (⟨144, by decide⟩ : Fin 148)) (colE2 ⟨144, by decide⟩ p hp)
        (rowE2 rK j hj hq)
      = species (reps (⟨144, by decide⟩ : Fin 148))
        (colE1 ⟨144, by decide⟩ p (transLenTr ⟨144, by decide⟩ p hp)) (rowE1 rK j hj) := by
  rcases rK with ⟨nK, hnK⟩; interval_cases nK
  · exact match_zero_len ⟨0, by decide⟩ ⟨144, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨1, by decide⟩ ⟨144, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨2, by decide⟩ ⟨144, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨3, by decide⟩ ⟨144, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨4, by decide⟩ ⟨144, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨5, by decide⟩ ⟨144, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨6, by decide⟩ ⟨144, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨7, by decide⟩ ⟨144, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨8, by decide⟩ ⟨144, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨9, by decide⟩ ⟨144, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨10, by decide⟩ ⟨144, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨11, by decide⟩ ⟨144, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨12, by decide⟩ ⟨144, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨13, by decide⟩ ⟨144, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨14, by decide⟩ ⟨144, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨15, by decide⟩ ⟨144, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨16, by decide⟩ ⟨144, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨17, by decide⟩ ⟨144, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨18, by decide⟩ ⟨144, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨19, by decide⟩ ⟨144, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨20, by decide⟩ ⟨144, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨21, by decide⟩ ⟨144, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨22, by decide⟩ ⟨144, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨23, by decide⟩ ⟨144, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨24, by decide⟩ ⟨144, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨25, by decide⟩ ⟨144, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨26, by decide⟩ ⟨144, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨27, by decide⟩ ⟨144, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨28, by decide⟩ ⟨144, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨29, by decide⟩ ⟨144, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨30, by decide⟩ ⟨144, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨31, by decide⟩ ⟨144, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨32, by decide⟩ ⟨144, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨33, by decide⟩ ⟨144, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨34, by decide⟩ ⟨144, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨35, by decide⟩ ⟨144, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨36, by decide⟩ ⟨144, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨37, by decide⟩ ⟨144, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨38, by decide⟩ ⟨144, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨39, by decide⟩ ⟨144, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨40, by decide⟩ ⟨144, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨41, by decide⟩ ⟨144, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨42, by decide⟩ ⟨144, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨43, by decide⟩ ⟨144, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨44, by decide⟩ ⟨144, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨45, by decide⟩ ⟨144, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨46, by decide⟩ ⟨144, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨47, by decide⟩ ⟨144, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨48, by decide⟩ ⟨144, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨49, by decide⟩ ⟨144, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨50, by decide⟩ ⟨144, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨51, by decide⟩ ⟨144, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨52, by decide⟩ ⟨144, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨53, by decide⟩ ⟨144, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨54, by decide⟩ ⟨144, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨55, by decide⟩ ⟨144, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨56, by decide⟩ ⟨144, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨57, by decide⟩ ⟨144, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨58, by decide⟩ ⟨144, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨59, by decide⟩ ⟨144, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨60, by decide⟩ ⟨144, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨61, by decide⟩ ⟨144, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨62, by decide⟩ ⟨144, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨63, by decide⟩ ⟨144, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨64, by decide⟩ ⟨144, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨65, by decide⟩ ⟨144, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨66, by decide⟩ ⟨144, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨67, by decide⟩ ⟨144, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨68, by decide⟩ ⟨144, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨69, by decide⟩ ⟨144, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨70, by decide⟩ ⟨144, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨71, by decide⟩ ⟨144, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨72, by decide⟩ ⟨144, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨73, by decide⟩ ⟨144, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨74, by decide⟩ ⟨144, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨75, by decide⟩ ⟨144, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨76, by decide⟩ ⟨144, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨77, by decide⟩ ⟨144, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨78, by decide⟩ ⟨144, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨79, by decide⟩ ⟨144, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨80, by decide⟩ ⟨144, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨81, by decide⟩ ⟨144, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨82, by decide⟩ ⟨144, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨83, by decide⟩ ⟨144, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨84, by decide⟩ ⟨144, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨85, by decide⟩ ⟨144, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨86, by decide⟩ ⟨144, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨87, by decide⟩ ⟨144, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨88, by decide⟩ ⟨144, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨89, by decide⟩ ⟨144, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨90, by decide⟩ ⟨144, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨91, by decide⟩ ⟨144, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨92, by decide⟩ ⟨144, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨93, by decide⟩ ⟨144, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨94, by decide⟩ ⟨144, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨95, by decide⟩ ⟨144, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨96, by decide⟩ ⟨144, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨97, by decide⟩ ⟨144, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨98, by decide⟩ ⟨144, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨99, by decide⟩ ⟨144, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨100, by decide⟩ ⟨144, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨101, by decide⟩ ⟨144, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨102, by decide⟩ ⟨144, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨103, by decide⟩ ⟨144, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨104, by decide⟩ ⟨144, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨105, by decide⟩ ⟨144, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨106, by decide⟩ ⟨144, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨107, by decide⟩ ⟨144, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨108, by decide⟩ ⟨144, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨109, by decide⟩ ⟨144, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨110, by decide⟩ ⟨144, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨111, by decide⟩ ⟨144, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨112, by decide⟩ ⟨144, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨113, by decide⟩ ⟨144, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨114, by decide⟩ ⟨144, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨115, by decide⟩ ⟨144, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_fix ⟨116, by decide⟩ ⟨144, by decide⟩ p hp j hj hq fz1_116_144 fz2_116_144
  · exact match_zero_fix ⟨117, by decide⟩ ⟨144, by decide⟩ p hp j hj hq fz1_117_144 fz2_117_144
  · exact match_zero_fix ⟨118, by decide⟩ ⟨144, by decide⟩ p hp j hj hq fz1_118_144 fz2_118_144
  · exact match_zero_fix ⟨119, by decide⟩ ⟨144, by decide⟩ p hp j hj hq fz1_119_144 fz2_119_144
  · exact match_zero_fix ⟨120, by decide⟩ ⟨144, by decide⟩ p hp j hj hq fz1_120_144 fz2_120_144
  · exact match_zero_fix ⟨121, by decide⟩ ⟨144, by decide⟩ p hp j hj hq fz1_121_144 fz2_121_144
  · exact match_zero_fix ⟨122, by decide⟩ ⟨144, by decide⟩ p hp j hj hq fz1_122_144 fz2_122_144
  · exact match_zero_fix ⟨123, by decide⟩ ⟨144, by decide⟩ p hp j hj hq fz1_123_144 fz2_123_144
  · exact match_zero_fix ⟨124, by decide⟩ ⟨144, by decide⟩ p hp j hj hq fz1_124_144 fz2_124_144
  · exact match_zero_fix ⟨125, by decide⟩ ⟨144, by decide⟩ p hp j hj hq fz1_125_144 fz2_125_144
  · exact match_zero_fix ⟨126, by decide⟩ ⟨144, by decide⟩ p hp j hj hq fz1_126_144 fz2_126_144
  · exact match_zero_fix ⟨127, by decide⟩ ⟨144, by decide⟩ p hp j hj hq fz1_127_144 fz2_127_144
  · exact match_zero_fix ⟨128, by decide⟩ ⟨144, by decide⟩ p hp j hj hq fz1_128_144 fz2_128_144
  · exact match_zero_fix ⟨129, by decide⟩ ⟨144, by decide⟩ p hp j hj hq fz1_129_144 fz2_129_144
  · exact match_zero_fix ⟨130, by decide⟩ ⟨144, by decide⟩ p hp j hj hq fz1_130_144 fz2_130_144
  · exact match_zero_fix ⟨131, by decide⟩ ⟨144, by decide⟩ p hp j hj hq fz1_131_144 fz2_131_144
  · exact match_zero_fix ⟨132, by decide⟩ ⟨144, by decide⟩ p hp j hj hq fz1_132_144 fz2_132_144
  · exact match_zero_fix ⟨133, by decide⟩ ⟨144, by decide⟩ p hp j hj hq fz1_133_144 fz2_133_144
  · exact match_zero_fix ⟨134, by decide⟩ ⟨144, by decide⟩ p hp j hj hq fz1_134_144 fz2_134_144
  · exact match_zero_fix ⟨135, by decide⟩ ⟨144, by decide⟩ p hp j hj hq fz1_135_144 fz2_135_144
  · exact match_zero_fix ⟨136, by decide⟩ ⟨144, by decide⟩ p hp j hj hq fz1_136_144 fz2_136_144
  · exact match_zero_fix ⟨137, by decide⟩ ⟨144, by decide⟩ p hp j hj hq fz1_137_144 fz2_137_144
  · exact match_zero_fix ⟨138, by decide⟩ ⟨144, by decide⟩ p hp j hj hq fz1_138_144 fz2_138_144
  · exact match_zero_fix ⟨139, by decide⟩ ⟨144, by decide⟩ p hp j hj hq fz1_139_144 fz2_139_144
  · exact match_zero_fix ⟨140, by decide⟩ ⟨144, by decide⟩ p hp j hj hq fz1_140_144 fz2_140_144
  · exact match_zero_fix ⟨141, by decide⟩ ⟨144, by decide⟩ p hp j hj hq fz1_141_144 fz2_141_144
  · exact match_zero_fix ⟨142, by decide⟩ ⟨144, by decide⟩ p hp j hj hq fz1_142_144 fz2_142_144
  · exact match_zero_fix ⟨143, by decide⟩ ⟨144, by decide⟩ p hp j hj hq fz1_143_144 fz2_143_144
  · exact pair_144_144 p hp hrep j hj hq
  · exact match_zero_fix ⟨145, by decide⟩ ⟨144, by decide⟩ p hp j hj hq fz1_145_144 fz2_145_144
  · exact match_zero_fix ⟨146, by decide⟩ ⟨144, by decide⟩ p hp j hj hq fz1_146_144 fz2_146_144
  · exact pair_147_144 p hp hrep j hj hq

theorem master_145 (p : Nat) (hp : p < (Q2.transData.getD 145 []).length)
    (hrep : (Q2.cosetIsRep.getD 145 []).getD p false = true)
    (rK : Fin 148) (j : Nat) (hj : j < (repChars.getD rK.val []).length)
    (hq : (normIsRep.getD rK.val []).getD j false = true) :
    species (Q2.reps (⟨145, by decide⟩ : Fin 148)) (colE2 ⟨145, by decide⟩ p hp)
        (rowE2 rK j hj hq)
      = species (reps (⟨145, by decide⟩ : Fin 148))
        (colE1 ⟨145, by decide⟩ p (transLenTr ⟨145, by decide⟩ p hp)) (rowE1 rK j hj) := by
  rcases rK with ⟨nK, hnK⟩; interval_cases nK
  · exact match_zero_len ⟨0, by decide⟩ ⟨145, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨1, by decide⟩ ⟨145, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨2, by decide⟩ ⟨145, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨3, by decide⟩ ⟨145, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨4, by decide⟩ ⟨145, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨5, by decide⟩ ⟨145, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨6, by decide⟩ ⟨145, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨7, by decide⟩ ⟨145, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨8, by decide⟩ ⟨145, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨9, by decide⟩ ⟨145, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨10, by decide⟩ ⟨145, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨11, by decide⟩ ⟨145, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨12, by decide⟩ ⟨145, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨13, by decide⟩ ⟨145, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨14, by decide⟩ ⟨145, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨15, by decide⟩ ⟨145, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨16, by decide⟩ ⟨145, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨17, by decide⟩ ⟨145, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨18, by decide⟩ ⟨145, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨19, by decide⟩ ⟨145, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨20, by decide⟩ ⟨145, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨21, by decide⟩ ⟨145, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨22, by decide⟩ ⟨145, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨23, by decide⟩ ⟨145, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨24, by decide⟩ ⟨145, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨25, by decide⟩ ⟨145, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨26, by decide⟩ ⟨145, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨27, by decide⟩ ⟨145, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨28, by decide⟩ ⟨145, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨29, by decide⟩ ⟨145, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨30, by decide⟩ ⟨145, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨31, by decide⟩ ⟨145, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨32, by decide⟩ ⟨145, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨33, by decide⟩ ⟨145, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨34, by decide⟩ ⟨145, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨35, by decide⟩ ⟨145, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨36, by decide⟩ ⟨145, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨37, by decide⟩ ⟨145, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨38, by decide⟩ ⟨145, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨39, by decide⟩ ⟨145, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨40, by decide⟩ ⟨145, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨41, by decide⟩ ⟨145, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨42, by decide⟩ ⟨145, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨43, by decide⟩ ⟨145, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨44, by decide⟩ ⟨145, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨45, by decide⟩ ⟨145, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨46, by decide⟩ ⟨145, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨47, by decide⟩ ⟨145, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨48, by decide⟩ ⟨145, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨49, by decide⟩ ⟨145, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨50, by decide⟩ ⟨145, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨51, by decide⟩ ⟨145, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨52, by decide⟩ ⟨145, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨53, by decide⟩ ⟨145, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨54, by decide⟩ ⟨145, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨55, by decide⟩ ⟨145, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨56, by decide⟩ ⟨145, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨57, by decide⟩ ⟨145, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨58, by decide⟩ ⟨145, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨59, by decide⟩ ⟨145, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨60, by decide⟩ ⟨145, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨61, by decide⟩ ⟨145, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨62, by decide⟩ ⟨145, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨63, by decide⟩ ⟨145, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨64, by decide⟩ ⟨145, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨65, by decide⟩ ⟨145, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨66, by decide⟩ ⟨145, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨67, by decide⟩ ⟨145, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨68, by decide⟩ ⟨145, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨69, by decide⟩ ⟨145, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨70, by decide⟩ ⟨145, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨71, by decide⟩ ⟨145, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨72, by decide⟩ ⟨145, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨73, by decide⟩ ⟨145, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨74, by decide⟩ ⟨145, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨75, by decide⟩ ⟨145, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨76, by decide⟩ ⟨145, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨77, by decide⟩ ⟨145, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨78, by decide⟩ ⟨145, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨79, by decide⟩ ⟨145, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨80, by decide⟩ ⟨145, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨81, by decide⟩ ⟨145, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨82, by decide⟩ ⟨145, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨83, by decide⟩ ⟨145, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨84, by decide⟩ ⟨145, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨85, by decide⟩ ⟨145, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨86, by decide⟩ ⟨145, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨87, by decide⟩ ⟨145, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨88, by decide⟩ ⟨145, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨89, by decide⟩ ⟨145, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨90, by decide⟩ ⟨145, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨91, by decide⟩ ⟨145, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨92, by decide⟩ ⟨145, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨93, by decide⟩ ⟨145, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨94, by decide⟩ ⟨145, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨95, by decide⟩ ⟨145, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨96, by decide⟩ ⟨145, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨97, by decide⟩ ⟨145, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨98, by decide⟩ ⟨145, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨99, by decide⟩ ⟨145, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨100, by decide⟩ ⟨145, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨101, by decide⟩ ⟨145, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨102, by decide⟩ ⟨145, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨103, by decide⟩ ⟨145, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨104, by decide⟩ ⟨145, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨105, by decide⟩ ⟨145, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨106, by decide⟩ ⟨145, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨107, by decide⟩ ⟨145, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨108, by decide⟩ ⟨145, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨109, by decide⟩ ⟨145, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨110, by decide⟩ ⟨145, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨111, by decide⟩ ⟨145, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨112, by decide⟩ ⟨145, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨113, by decide⟩ ⟨145, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨114, by decide⟩ ⟨145, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨115, by decide⟩ ⟨145, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_fix ⟨116, by decide⟩ ⟨145, by decide⟩ p hp j hj hq fz1_116_145 fz2_116_145
  · exact match_zero_fix ⟨117, by decide⟩ ⟨145, by decide⟩ p hp j hj hq fz1_117_145 fz2_117_145
  · exact match_zero_fix ⟨118, by decide⟩ ⟨145, by decide⟩ p hp j hj hq fz1_118_145 fz2_118_145
  · exact match_zero_fix ⟨119, by decide⟩ ⟨145, by decide⟩ p hp j hj hq fz1_119_145 fz2_119_145
  · exact match_zero_fix ⟨120, by decide⟩ ⟨145, by decide⟩ p hp j hj hq fz1_120_145 fz2_120_145
  · exact match_zero_fix ⟨121, by decide⟩ ⟨145, by decide⟩ p hp j hj hq fz1_121_145 fz2_121_145
  · exact match_zero_fix ⟨122, by decide⟩ ⟨145, by decide⟩ p hp j hj hq fz1_122_145 fz2_122_145
  · exact match_zero_fix ⟨123, by decide⟩ ⟨145, by decide⟩ p hp j hj hq fz1_123_145 fz2_123_145
  · exact match_zero_fix ⟨124, by decide⟩ ⟨145, by decide⟩ p hp j hj hq fz1_124_145 fz2_124_145
  · exact match_zero_fix ⟨125, by decide⟩ ⟨145, by decide⟩ p hp j hj hq fz1_125_145 fz2_125_145
  · exact match_zero_fix ⟨126, by decide⟩ ⟨145, by decide⟩ p hp j hj hq fz1_126_145 fz2_126_145
  · exact match_zero_fix ⟨127, by decide⟩ ⟨145, by decide⟩ p hp j hj hq fz1_127_145 fz2_127_145
  · exact match_zero_fix ⟨128, by decide⟩ ⟨145, by decide⟩ p hp j hj hq fz1_128_145 fz2_128_145
  · exact match_zero_fix ⟨129, by decide⟩ ⟨145, by decide⟩ p hp j hj hq fz1_129_145 fz2_129_145
  · exact match_zero_fix ⟨130, by decide⟩ ⟨145, by decide⟩ p hp j hj hq fz1_130_145 fz2_130_145
  · exact match_zero_fix ⟨131, by decide⟩ ⟨145, by decide⟩ p hp j hj hq fz1_131_145 fz2_131_145
  · exact match_zero_fix ⟨132, by decide⟩ ⟨145, by decide⟩ p hp j hj hq fz1_132_145 fz2_132_145
  · exact match_zero_fix ⟨133, by decide⟩ ⟨145, by decide⟩ p hp j hj hq fz1_133_145 fz2_133_145
  · exact match_zero_fix ⟨134, by decide⟩ ⟨145, by decide⟩ p hp j hj hq fz1_134_145 fz2_134_145
  · exact match_zero_fix ⟨135, by decide⟩ ⟨145, by decide⟩ p hp j hj hq fz1_135_145 fz2_135_145
  · exact match_zero_fix ⟨136, by decide⟩ ⟨145, by decide⟩ p hp j hj hq fz1_136_145 fz2_136_145
  · exact match_zero_fix ⟨137, by decide⟩ ⟨145, by decide⟩ p hp j hj hq fz1_137_145 fz2_137_145
  · exact match_zero_fix ⟨138, by decide⟩ ⟨145, by decide⟩ p hp j hj hq fz1_138_145 fz2_138_145
  · exact match_zero_fix ⟨139, by decide⟩ ⟨145, by decide⟩ p hp j hj hq fz1_139_145 fz2_139_145
  · exact match_zero_fix ⟨140, by decide⟩ ⟨145, by decide⟩ p hp j hj hq fz1_140_145 fz2_140_145
  · exact match_zero_fix ⟨141, by decide⟩ ⟨145, by decide⟩ p hp j hj hq fz1_141_145 fz2_141_145
  · exact match_zero_fix ⟨142, by decide⟩ ⟨145, by decide⟩ p hp j hj hq fz1_142_145 fz2_142_145
  · exact match_zero_fix ⟨143, by decide⟩ ⟨145, by decide⟩ p hp j hj hq fz1_143_145 fz2_143_145
  · exact match_zero_fix ⟨144, by decide⟩ ⟨145, by decide⟩ p hp j hj hq fz1_144_145 fz2_144_145
  · exact pair_145_145 p hp hrep j hj hq
  · exact match_zero_fix ⟨146, by decide⟩ ⟨145, by decide⟩ p hp j hj hq fz1_146_145 fz2_146_145
  · exact pair_147_145 p hp hrep j hj hq

theorem master_146 (p : Nat) (hp : p < (Q2.transData.getD 146 []).length)
    (hrep : (Q2.cosetIsRep.getD 146 []).getD p false = true)
    (rK : Fin 148) (j : Nat) (hj : j < (repChars.getD rK.val []).length)
    (hq : (normIsRep.getD rK.val []).getD j false = true) :
    species (Q2.reps (⟨146, by decide⟩ : Fin 148)) (colE2 ⟨146, by decide⟩ p hp)
        (rowE2 rK j hj hq)
      = species (reps (⟨146, by decide⟩ : Fin 148))
        (colE1 ⟨146, by decide⟩ p (transLenTr ⟨146, by decide⟩ p hp)) (rowE1 rK j hj) := by
  rcases rK with ⟨nK, hnK⟩; interval_cases nK
  · exact match_zero_len ⟨0, by decide⟩ ⟨146, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨1, by decide⟩ ⟨146, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨2, by decide⟩ ⟨146, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨3, by decide⟩ ⟨146, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨4, by decide⟩ ⟨146, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨5, by decide⟩ ⟨146, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨6, by decide⟩ ⟨146, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨7, by decide⟩ ⟨146, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨8, by decide⟩ ⟨146, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨9, by decide⟩ ⟨146, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨10, by decide⟩ ⟨146, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨11, by decide⟩ ⟨146, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨12, by decide⟩ ⟨146, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨13, by decide⟩ ⟨146, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨14, by decide⟩ ⟨146, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨15, by decide⟩ ⟨146, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨16, by decide⟩ ⟨146, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨17, by decide⟩ ⟨146, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨18, by decide⟩ ⟨146, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨19, by decide⟩ ⟨146, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨20, by decide⟩ ⟨146, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨21, by decide⟩ ⟨146, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨22, by decide⟩ ⟨146, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨23, by decide⟩ ⟨146, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨24, by decide⟩ ⟨146, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨25, by decide⟩ ⟨146, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨26, by decide⟩ ⟨146, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨27, by decide⟩ ⟨146, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨28, by decide⟩ ⟨146, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨29, by decide⟩ ⟨146, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨30, by decide⟩ ⟨146, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨31, by decide⟩ ⟨146, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨32, by decide⟩ ⟨146, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨33, by decide⟩ ⟨146, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨34, by decide⟩ ⟨146, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨35, by decide⟩ ⟨146, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨36, by decide⟩ ⟨146, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨37, by decide⟩ ⟨146, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨38, by decide⟩ ⟨146, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨39, by decide⟩ ⟨146, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨40, by decide⟩ ⟨146, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨41, by decide⟩ ⟨146, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨42, by decide⟩ ⟨146, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨43, by decide⟩ ⟨146, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨44, by decide⟩ ⟨146, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨45, by decide⟩ ⟨146, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨46, by decide⟩ ⟨146, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨47, by decide⟩ ⟨146, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨48, by decide⟩ ⟨146, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨49, by decide⟩ ⟨146, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨50, by decide⟩ ⟨146, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨51, by decide⟩ ⟨146, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨52, by decide⟩ ⟨146, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨53, by decide⟩ ⟨146, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨54, by decide⟩ ⟨146, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨55, by decide⟩ ⟨146, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨56, by decide⟩ ⟨146, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨57, by decide⟩ ⟨146, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨58, by decide⟩ ⟨146, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨59, by decide⟩ ⟨146, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨60, by decide⟩ ⟨146, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨61, by decide⟩ ⟨146, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨62, by decide⟩ ⟨146, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨63, by decide⟩ ⟨146, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨64, by decide⟩ ⟨146, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨65, by decide⟩ ⟨146, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨66, by decide⟩ ⟨146, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨67, by decide⟩ ⟨146, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨68, by decide⟩ ⟨146, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨69, by decide⟩ ⟨146, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨70, by decide⟩ ⟨146, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨71, by decide⟩ ⟨146, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨72, by decide⟩ ⟨146, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨73, by decide⟩ ⟨146, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨74, by decide⟩ ⟨146, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨75, by decide⟩ ⟨146, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨76, by decide⟩ ⟨146, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨77, by decide⟩ ⟨146, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨78, by decide⟩ ⟨146, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨79, by decide⟩ ⟨146, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨80, by decide⟩ ⟨146, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨81, by decide⟩ ⟨146, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨82, by decide⟩ ⟨146, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨83, by decide⟩ ⟨146, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨84, by decide⟩ ⟨146, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨85, by decide⟩ ⟨146, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨86, by decide⟩ ⟨146, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨87, by decide⟩ ⟨146, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨88, by decide⟩ ⟨146, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨89, by decide⟩ ⟨146, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨90, by decide⟩ ⟨146, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨91, by decide⟩ ⟨146, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨92, by decide⟩ ⟨146, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨93, by decide⟩ ⟨146, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨94, by decide⟩ ⟨146, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨95, by decide⟩ ⟨146, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨96, by decide⟩ ⟨146, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨97, by decide⟩ ⟨146, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨98, by decide⟩ ⟨146, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨99, by decide⟩ ⟨146, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨100, by decide⟩ ⟨146, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨101, by decide⟩ ⟨146, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨102, by decide⟩ ⟨146, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨103, by decide⟩ ⟨146, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨104, by decide⟩ ⟨146, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨105, by decide⟩ ⟨146, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨106, by decide⟩ ⟨146, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨107, by decide⟩ ⟨146, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨108, by decide⟩ ⟨146, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨109, by decide⟩ ⟨146, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨110, by decide⟩ ⟨146, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨111, by decide⟩ ⟨146, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨112, by decide⟩ ⟨146, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨113, by decide⟩ ⟨146, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨114, by decide⟩ ⟨146, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨115, by decide⟩ ⟨146, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_fix ⟨116, by decide⟩ ⟨146, by decide⟩ p hp j hj hq fz1_116_146 fz2_116_146
  · exact match_zero_fix ⟨117, by decide⟩ ⟨146, by decide⟩ p hp j hj hq fz1_117_146 fz2_117_146
  · exact match_zero_fix ⟨118, by decide⟩ ⟨146, by decide⟩ p hp j hj hq fz1_118_146 fz2_118_146
  · exact match_zero_fix ⟨119, by decide⟩ ⟨146, by decide⟩ p hp j hj hq fz1_119_146 fz2_119_146
  · exact match_zero_fix ⟨120, by decide⟩ ⟨146, by decide⟩ p hp j hj hq fz1_120_146 fz2_120_146
  · exact match_zero_fix ⟨121, by decide⟩ ⟨146, by decide⟩ p hp j hj hq fz1_121_146 fz2_121_146
  · exact match_zero_fix ⟨122, by decide⟩ ⟨146, by decide⟩ p hp j hj hq fz1_122_146 fz2_122_146
  · exact match_zero_fix ⟨123, by decide⟩ ⟨146, by decide⟩ p hp j hj hq fz1_123_146 fz2_123_146
  · exact match_zero_fix ⟨124, by decide⟩ ⟨146, by decide⟩ p hp j hj hq fz1_124_146 fz2_124_146
  · exact match_zero_fix ⟨125, by decide⟩ ⟨146, by decide⟩ p hp j hj hq fz1_125_146 fz2_125_146
  · exact match_zero_fix ⟨126, by decide⟩ ⟨146, by decide⟩ p hp j hj hq fz1_126_146 fz2_126_146
  · exact match_zero_fix ⟨127, by decide⟩ ⟨146, by decide⟩ p hp j hj hq fz1_127_146 fz2_127_146
  · exact match_zero_fix ⟨128, by decide⟩ ⟨146, by decide⟩ p hp j hj hq fz1_128_146 fz2_128_146
  · exact match_zero_fix ⟨129, by decide⟩ ⟨146, by decide⟩ p hp j hj hq fz1_129_146 fz2_129_146
  · exact match_zero_fix ⟨130, by decide⟩ ⟨146, by decide⟩ p hp j hj hq fz1_130_146 fz2_130_146
  · exact match_zero_fix ⟨131, by decide⟩ ⟨146, by decide⟩ p hp j hj hq fz1_131_146 fz2_131_146
  · exact match_zero_fix ⟨132, by decide⟩ ⟨146, by decide⟩ p hp j hj hq fz1_132_146 fz2_132_146
  · exact match_zero_fix ⟨133, by decide⟩ ⟨146, by decide⟩ p hp j hj hq fz1_133_146 fz2_133_146
  · exact match_zero_fix ⟨134, by decide⟩ ⟨146, by decide⟩ p hp j hj hq fz1_134_146 fz2_134_146
  · exact match_zero_fix ⟨135, by decide⟩ ⟨146, by decide⟩ p hp j hj hq fz1_135_146 fz2_135_146
  · exact match_zero_fix ⟨136, by decide⟩ ⟨146, by decide⟩ p hp j hj hq fz1_136_146 fz2_136_146
  · exact match_zero_fix ⟨137, by decide⟩ ⟨146, by decide⟩ p hp j hj hq fz1_137_146 fz2_137_146
  · exact match_zero_fix ⟨138, by decide⟩ ⟨146, by decide⟩ p hp j hj hq fz1_138_146 fz2_138_146
  · exact match_zero_fix ⟨139, by decide⟩ ⟨146, by decide⟩ p hp j hj hq fz1_139_146 fz2_139_146
  · exact match_zero_fix ⟨140, by decide⟩ ⟨146, by decide⟩ p hp j hj hq fz1_140_146 fz2_140_146
  · exact match_zero_fix ⟨141, by decide⟩ ⟨146, by decide⟩ p hp j hj hq fz1_141_146 fz2_141_146
  · exact match_zero_fix ⟨142, by decide⟩ ⟨146, by decide⟩ p hp j hj hq fz1_142_146 fz2_142_146
  · exact match_zero_fix ⟨143, by decide⟩ ⟨146, by decide⟩ p hp j hj hq fz1_143_146 fz2_143_146
  · exact match_zero_fix ⟨144, by decide⟩ ⟨146, by decide⟩ p hp j hj hq fz1_144_146 fz2_144_146
  · exact match_zero_fix ⟨145, by decide⟩ ⟨146, by decide⟩ p hp j hj hq fz1_145_146 fz2_145_146
  · exact pair_146_146 p hp hrep j hj hq
  · exact pair_147_146 p hp hrep j hj hq

theorem master_147 (p : Nat) (hp : p < (Q2.transData.getD 147 []).length)
    (hrep : (Q2.cosetIsRep.getD 147 []).getD p false = true)
    (rK : Fin 148) (j : Nat) (hj : j < (repChars.getD rK.val []).length)
    (hq : (normIsRep.getD rK.val []).getD j false = true) :
    species (Q2.reps (⟨147, by decide⟩ : Fin 148)) (colE2 ⟨147, by decide⟩ p hp)
        (rowE2 rK j hj hq)
      = species (reps (⟨147, by decide⟩ : Fin 148))
        (colE1 ⟨147, by decide⟩ p (transLenTr ⟨147, by decide⟩ p hp)) (rowE1 rK j hj) := by
  rcases rK with ⟨nK, hnK⟩; interval_cases nK
  · exact match_zero_len ⟨0, by decide⟩ ⟨147, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨1, by decide⟩ ⟨147, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨2, by decide⟩ ⟨147, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨3, by decide⟩ ⟨147, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨4, by decide⟩ ⟨147, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨5, by decide⟩ ⟨147, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨6, by decide⟩ ⟨147, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨7, by decide⟩ ⟨147, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨8, by decide⟩ ⟨147, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨9, by decide⟩ ⟨147, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨10, by decide⟩ ⟨147, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨11, by decide⟩ ⟨147, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨12, by decide⟩ ⟨147, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨13, by decide⟩ ⟨147, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨14, by decide⟩ ⟨147, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨15, by decide⟩ ⟨147, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨16, by decide⟩ ⟨147, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨17, by decide⟩ ⟨147, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨18, by decide⟩ ⟨147, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨19, by decide⟩ ⟨147, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨20, by decide⟩ ⟨147, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨21, by decide⟩ ⟨147, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨22, by decide⟩ ⟨147, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨23, by decide⟩ ⟨147, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨24, by decide⟩ ⟨147, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨25, by decide⟩ ⟨147, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨26, by decide⟩ ⟨147, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨27, by decide⟩ ⟨147, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨28, by decide⟩ ⟨147, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨29, by decide⟩ ⟨147, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨30, by decide⟩ ⟨147, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨31, by decide⟩ ⟨147, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨32, by decide⟩ ⟨147, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨33, by decide⟩ ⟨147, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨34, by decide⟩ ⟨147, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨35, by decide⟩ ⟨147, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨36, by decide⟩ ⟨147, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨37, by decide⟩ ⟨147, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨38, by decide⟩ ⟨147, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨39, by decide⟩ ⟨147, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨40, by decide⟩ ⟨147, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨41, by decide⟩ ⟨147, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨42, by decide⟩ ⟨147, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨43, by decide⟩ ⟨147, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨44, by decide⟩ ⟨147, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨45, by decide⟩ ⟨147, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨46, by decide⟩ ⟨147, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨47, by decide⟩ ⟨147, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨48, by decide⟩ ⟨147, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨49, by decide⟩ ⟨147, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨50, by decide⟩ ⟨147, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨51, by decide⟩ ⟨147, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨52, by decide⟩ ⟨147, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨53, by decide⟩ ⟨147, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨54, by decide⟩ ⟨147, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨55, by decide⟩ ⟨147, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨56, by decide⟩ ⟨147, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨57, by decide⟩ ⟨147, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨58, by decide⟩ ⟨147, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨59, by decide⟩ ⟨147, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨60, by decide⟩ ⟨147, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨61, by decide⟩ ⟨147, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨62, by decide⟩ ⟨147, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨63, by decide⟩ ⟨147, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨64, by decide⟩ ⟨147, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨65, by decide⟩ ⟨147, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨66, by decide⟩ ⟨147, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨67, by decide⟩ ⟨147, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨68, by decide⟩ ⟨147, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨69, by decide⟩ ⟨147, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨70, by decide⟩ ⟨147, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨71, by decide⟩ ⟨147, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨72, by decide⟩ ⟨147, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨73, by decide⟩ ⟨147, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨74, by decide⟩ ⟨147, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨75, by decide⟩ ⟨147, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨76, by decide⟩ ⟨147, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨77, by decide⟩ ⟨147, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨78, by decide⟩ ⟨147, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨79, by decide⟩ ⟨147, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨80, by decide⟩ ⟨147, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨81, by decide⟩ ⟨147, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨82, by decide⟩ ⟨147, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨83, by decide⟩ ⟨147, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨84, by decide⟩ ⟨147, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨85, by decide⟩ ⟨147, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨86, by decide⟩ ⟨147, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨87, by decide⟩ ⟨147, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨88, by decide⟩ ⟨147, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨89, by decide⟩ ⟨147, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨90, by decide⟩ ⟨147, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨91, by decide⟩ ⟨147, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨92, by decide⟩ ⟨147, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨93, by decide⟩ ⟨147, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨94, by decide⟩ ⟨147, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨95, by decide⟩ ⟨147, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨96, by decide⟩ ⟨147, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨97, by decide⟩ ⟨147, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨98, by decide⟩ ⟨147, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨99, by decide⟩ ⟨147, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨100, by decide⟩ ⟨147, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨101, by decide⟩ ⟨147, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨102, by decide⟩ ⟨147, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨103, by decide⟩ ⟨147, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨104, by decide⟩ ⟨147, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨105, by decide⟩ ⟨147, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨106, by decide⟩ ⟨147, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨107, by decide⟩ ⟨147, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨108, by decide⟩ ⟨147, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨109, by decide⟩ ⟨147, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨110, by decide⟩ ⟨147, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨111, by decide⟩ ⟨147, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨112, by decide⟩ ⟨147, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨113, by decide⟩ ⟨147, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨114, by decide⟩ ⟨147, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨115, by decide⟩ ⟨147, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨116, by decide⟩ ⟨147, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨117, by decide⟩ ⟨147, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨118, by decide⟩ ⟨147, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨119, by decide⟩ ⟨147, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨120, by decide⟩ ⟨147, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨121, by decide⟩ ⟨147, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨122, by decide⟩ ⟨147, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨123, by decide⟩ ⟨147, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨124, by decide⟩ ⟨147, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨125, by decide⟩ ⟨147, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨126, by decide⟩ ⟨147, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨127, by decide⟩ ⟨147, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨128, by decide⟩ ⟨147, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨129, by decide⟩ ⟨147, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨130, by decide⟩ ⟨147, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨131, by decide⟩ ⟨147, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨132, by decide⟩ ⟨147, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨133, by decide⟩ ⟨147, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨134, by decide⟩ ⟨147, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨135, by decide⟩ ⟨147, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨136, by decide⟩ ⟨147, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨137, by decide⟩ ⟨147, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨138, by decide⟩ ⟨147, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨139, by decide⟩ ⟨147, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨140, by decide⟩ ⟨147, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨141, by decide⟩ ⟨147, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨142, by decide⟩ ⟨147, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨143, by decide⟩ ⟨147, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨144, by decide⟩ ⟨147, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨145, by decide⟩ ⟨147, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨146, by decide⟩ ⟨147, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact pair_147_147 p hp hrep j hj hq

end LeanDring.P5Presentation
