/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Data.FixZero.C055
import LeanDring.P5.Data.FixZero.C056
import LeanDring.P5.Data.FixZero.C057
import LeanDring.P5.Data.FixZero.C058
import LeanDring.P5.Data.FixZero.C059
import LeanDring.P5.Data.FixZero.C060
import LeanDring.P5.Data.FixZero.C061
import LeanDring.P5.Data.FixZero.C062
import LeanDring.P5.Data.FixZero.C063
import LeanDring.P5.Data.FixZero.C064
import LeanDring.P5.Data.FixZero.C065
import LeanDring.P5.Data.FixZero.C066
import LeanDring.P5.Data.FixZero.C067
import LeanDring.P5.Data.FixZero.C068
import LeanDring.P5.Data.FixZero.C069
import LeanDring.P5.Data.FixZero.C070
import LeanDring.P5.Data.FixZero.C071
import LeanDring.P5.Data.FixZero.C072
import LeanDring.P5.Data.FixZero.C073
import LeanDring.P5.Data.FixZero.C074
import LeanDring.P5.Data.FixZero.C075
import LeanDring.P5.Data.FixZero.C076
import LeanDring.P5.Data.FixZero.C077
import LeanDring.P5.Data.FixZero.C078
import LeanDring.P5.Data.FixZero.C079
import LeanDring.P5.Data.FixZero.C080
import LeanDring.P5.Data.FixZero.C081
import LeanDring.P5.Data.FixZero.C082
import LeanDring.P5.Data.FixZero.C083
import LeanDring.P5.Data.FixZero.C084
import LeanDring.P5.Data.FixZero.C085
import LeanDring.P5.Data.FixZero.C086
import LeanDring.P5.Data.FixZero.C087
import LeanDring.P5.Data.FixZero.C088
import LeanDring.P5.Certificate.RingIsomorphism.MatchCore
import LeanDring.P5.Data.MatchPair.C011
import LeanDring.P5.Data.MatchPair.C003
import LeanDring.P5.Data.MatchPair.C004
import LeanDring.P5.Data.MatchPair.C007

/-! # Stage-5 per-column-class master theorems, chunk 9 (auto-emitted).  -/

namespace LeanDring.P5Presentation

open MulAction Finset LeanDring.DRing LeanDring.MonGSet

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.style.longLine false

theorem master_72 (p : Nat) (hp : p < (Q2.transData.getD 72 []).length)
    (hrep : (Q2.cosetIsRep.getD 72 []).getD p false = true)
    (rK : Fin 148) (j : Nat) (hj : j < (repChars.getD rK.val []).length)
    (hq : (normIsRep.getD rK.val []).getD j false = true) :
    species (Q2.reps (⟨72, by decide⟩ : Fin 148)) (colE2 ⟨72, by decide⟩ p hp)
        (rowE2 rK j hj hq)
      = species (reps (⟨72, by decide⟩ : Fin 148))
        (colE1 ⟨72, by decide⟩ p (transLenTr ⟨72, by decide⟩ p hp)) (rowE1 rK j hj) := by
  rcases rK with ⟨nK, hnK⟩; interval_cases nK
  · exact match_zero_len ⟨0, by decide⟩ ⟨72, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨1, by decide⟩ ⟨72, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨2, by decide⟩ ⟨72, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨3, by decide⟩ ⟨72, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨4, by decide⟩ ⟨72, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨5, by decide⟩ ⟨72, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨6, by decide⟩ ⟨72, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨7, by decide⟩ ⟨72, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨8, by decide⟩ ⟨72, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨9, by decide⟩ ⟨72, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨10, by decide⟩ ⟨72, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨11, by decide⟩ ⟨72, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨12, by decide⟩ ⟨72, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨13, by decide⟩ ⟨72, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨14, by decide⟩ ⟨72, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨15, by decide⟩ ⟨72, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨16, by decide⟩ ⟨72, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨17, by decide⟩ ⟨72, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨18, by decide⟩ ⟨72, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨19, by decide⟩ ⟨72, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨20, by decide⟩ ⟨72, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨21, by decide⟩ ⟨72, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨22, by decide⟩ ⟨72, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨23, by decide⟩ ⟨72, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨24, by decide⟩ ⟨72, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨25, by decide⟩ ⟨72, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨26, by decide⟩ ⟨72, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨27, by decide⟩ ⟨72, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨28, by decide⟩ ⟨72, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨29, by decide⟩ ⟨72, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨30, by decide⟩ ⟨72, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨31, by decide⟩ ⟨72, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨32, by decide⟩ ⟨72, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨33, by decide⟩ ⟨72, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨34, by decide⟩ ⟨72, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨35, by decide⟩ ⟨72, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨36, by decide⟩ ⟨72, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨37, by decide⟩ ⟨72, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨38, by decide⟩ ⟨72, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨39, by decide⟩ ⟨72, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨40, by decide⟩ ⟨72, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨41, by decide⟩ ⟨72, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨42, by decide⟩ ⟨72, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨43, by decide⟩ ⟨72, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨44, by decide⟩ ⟨72, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨45, by decide⟩ ⟨72, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨46, by decide⟩ ⟨72, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨47, by decide⟩ ⟨72, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨48, by decide⟩ ⟨72, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨49, by decide⟩ ⟨72, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨50, by decide⟩ ⟨72, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨51, by decide⟩ ⟨72, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨52, by decide⟩ ⟨72, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨53, by decide⟩ ⟨72, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨54, by decide⟩ ⟨72, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_fix ⟨55, by decide⟩ ⟨72, by decide⟩ p hp j hj hq fz1_55_72 fz2_55_72
  · exact match_zero_fix ⟨56, by decide⟩ ⟨72, by decide⟩ p hp j hj hq fz1_56_72 fz2_56_72
  · exact match_zero_fix ⟨57, by decide⟩ ⟨72, by decide⟩ p hp j hj hq fz1_57_72 fz2_57_72
  · exact match_zero_fix ⟨58, by decide⟩ ⟨72, by decide⟩ p hp j hj hq fz1_58_72 fz2_58_72
  · exact match_zero_fix ⟨59, by decide⟩ ⟨72, by decide⟩ p hp j hj hq fz1_59_72 fz2_59_72
  · exact match_zero_fix ⟨60, by decide⟩ ⟨72, by decide⟩ p hp j hj hq fz1_60_72 fz2_60_72
  · exact match_zero_fix ⟨61, by decide⟩ ⟨72, by decide⟩ p hp j hj hq fz1_61_72 fz2_61_72
  · exact match_zero_fix ⟨62, by decide⟩ ⟨72, by decide⟩ p hp j hj hq fz1_62_72 fz2_62_72
  · exact match_zero_fix ⟨63, by decide⟩ ⟨72, by decide⟩ p hp j hj hq fz1_63_72 fz2_63_72
  · exact match_zero_fix ⟨64, by decide⟩ ⟨72, by decide⟩ p hp j hj hq fz1_64_72 fz2_64_72
  · exact match_zero_fix ⟨65, by decide⟩ ⟨72, by decide⟩ p hp j hj hq fz1_65_72 fz2_65_72
  · exact match_zero_fix ⟨66, by decide⟩ ⟨72, by decide⟩ p hp j hj hq fz1_66_72 fz2_66_72
  · exact match_zero_fix ⟨67, by decide⟩ ⟨72, by decide⟩ p hp j hj hq fz1_67_72 fz2_67_72
  · exact match_zero_fix ⟨68, by decide⟩ ⟨72, by decide⟩ p hp j hj hq fz1_68_72 fz2_68_72
  · exact match_zero_fix ⟨69, by decide⟩ ⟨72, by decide⟩ p hp j hj hq fz1_69_72 fz2_69_72
  · exact match_zero_fix ⟨70, by decide⟩ ⟨72, by decide⟩ p hp j hj hq fz1_70_72 fz2_70_72
  · exact match_zero_fix ⟨71, by decide⟩ ⟨72, by decide⟩ p hp j hj hq fz1_71_72 fz2_71_72
  · exact pair_72_72 p hp hrep j hj hq
  · exact match_zero_fix ⟨73, by decide⟩ ⟨72, by decide⟩ p hp j hj hq fz1_73_72 fz2_73_72
  · exact match_zero_fix ⟨74, by decide⟩ ⟨72, by decide⟩ p hp j hj hq fz1_74_72 fz2_74_72
  · exact match_zero_fix ⟨75, by decide⟩ ⟨72, by decide⟩ p hp j hj hq fz1_75_72 fz2_75_72
  · exact match_zero_fix ⟨76, by decide⟩ ⟨72, by decide⟩ p hp j hj hq fz1_76_72 fz2_76_72
  · exact match_zero_fix ⟨77, by decide⟩ ⟨72, by decide⟩ p hp j hj hq fz1_77_72 fz2_77_72
  · exact match_zero_fix ⟨78, by decide⟩ ⟨72, by decide⟩ p hp j hj hq fz1_78_72 fz2_78_72
  · exact match_zero_fix ⟨79, by decide⟩ ⟨72, by decide⟩ p hp j hj hq fz1_79_72 fz2_79_72
  · exact match_zero_fix ⟨80, by decide⟩ ⟨72, by decide⟩ p hp j hj hq fz1_80_72 fz2_80_72
  · exact match_zero_fix ⟨81, by decide⟩ ⟨72, by decide⟩ p hp j hj hq fz1_81_72 fz2_81_72
  · exact match_zero_fix ⟨82, by decide⟩ ⟨72, by decide⟩ p hp j hj hq fz1_82_72 fz2_82_72
  · exact match_zero_fix ⟨83, by decide⟩ ⟨72, by decide⟩ p hp j hj hq fz1_83_72 fz2_83_72
  · exact match_zero_fix ⟨84, by decide⟩ ⟨72, by decide⟩ p hp j hj hq fz1_84_72 fz2_84_72
  · exact match_zero_fix ⟨85, by decide⟩ ⟨72, by decide⟩ p hp j hj hq fz1_85_72 fz2_85_72
  · exact match_zero_fix ⟨86, by decide⟩ ⟨72, by decide⟩ p hp j hj hq fz1_86_72 fz2_86_72
  · exact match_zero_fix ⟨87, by decide⟩ ⟨72, by decide⟩ p hp j hj hq fz1_87_72 fz2_87_72
  · exact match_zero_fix ⟨88, by decide⟩ ⟨72, by decide⟩ p hp j hj hq fz1_88_72 fz2_88_72
  · exact match_zero_fix ⟨89, by decide⟩ ⟨72, by decide⟩ p hp j hj hq fz1_89_72 fz2_89_72
  · exact match_zero_fix ⟨90, by decide⟩ ⟨72, by decide⟩ p hp j hj hq fz1_90_72 fz2_90_72
  · exact match_zero_fix ⟨91, by decide⟩ ⟨72, by decide⟩ p hp j hj hq fz1_91_72 fz2_91_72
  · exact match_zero_fix ⟨92, by decide⟩ ⟨72, by decide⟩ p hp j hj hq fz1_92_72 fz2_92_72
  · exact match_zero_fix ⟨93, by decide⟩ ⟨72, by decide⟩ p hp j hj hq fz1_93_72 fz2_93_72
  · exact match_zero_fix ⟨94, by decide⟩ ⟨72, by decide⟩ p hp j hj hq fz1_94_72 fz2_94_72
  · exact match_zero_fix ⟨95, by decide⟩ ⟨72, by decide⟩ p hp j hj hq fz1_95_72 fz2_95_72
  · exact match_zero_fix ⟨96, by decide⟩ ⟨72, by decide⟩ p hp j hj hq fz1_96_72 fz2_96_72
  · exact match_zero_fix ⟨97, by decide⟩ ⟨72, by decide⟩ p hp j hj hq fz1_97_72 fz2_97_72
  · exact match_zero_fix ⟨98, by decide⟩ ⟨72, by decide⟩ p hp j hj hq fz1_98_72 fz2_98_72
  · exact match_zero_fix ⟨99, by decide⟩ ⟨72, by decide⟩ p hp j hj hq fz1_99_72 fz2_99_72
  · exact match_zero_fix ⟨100, by decide⟩ ⟨72, by decide⟩ p hp j hj hq fz1_100_72 fz2_100_72
  · exact match_zero_fix ⟨101, by decide⟩ ⟨72, by decide⟩ p hp j hj hq fz1_101_72 fz2_101_72
  · exact match_zero_fix ⟨102, by decide⟩ ⟨72, by decide⟩ p hp j hj hq fz1_102_72 fz2_102_72
  · exact match_zero_fix ⟨103, by decide⟩ ⟨72, by decide⟩ p hp j hj hq fz1_103_72 fz2_103_72
  · exact match_zero_fix ⟨104, by decide⟩ ⟨72, by decide⟩ p hp j hj hq fz1_104_72 fz2_104_72
  · exact match_zero_fix ⟨105, by decide⟩ ⟨72, by decide⟩ p hp j hj hq fz1_105_72 fz2_105_72
  · exact match_zero_fix ⟨106, by decide⟩ ⟨72, by decide⟩ p hp j hj hq fz1_106_72 fz2_106_72
  · exact match_zero_fix ⟨107, by decide⟩ ⟨72, by decide⟩ p hp j hj hq fz1_107_72 fz2_107_72
  · exact match_zero_fix ⟨108, by decide⟩ ⟨72, by decide⟩ p hp j hj hq fz1_108_72 fz2_108_72
  · exact match_zero_fix ⟨109, by decide⟩ ⟨72, by decide⟩ p hp j hj hq fz1_109_72 fz2_109_72
  · exact match_zero_fix ⟨110, by decide⟩ ⟨72, by decide⟩ p hp j hj hq fz1_110_72 fz2_110_72
  · exact match_zero_fix ⟨111, by decide⟩ ⟨72, by decide⟩ p hp j hj hq fz1_111_72 fz2_111_72
  · exact match_zero_fix ⟨112, by decide⟩ ⟨72, by decide⟩ p hp j hj hq fz1_112_72 fz2_112_72
  · exact match_zero_fix ⟨113, by decide⟩ ⟨72, by decide⟩ p hp j hj hq fz1_113_72 fz2_113_72
  · exact match_zero_fix ⟨114, by decide⟩ ⟨72, by decide⟩ p hp j hj hq fz1_114_72 fz2_114_72
  · exact match_zero_fix ⟨115, by decide⟩ ⟨72, by decide⟩ p hp j hj hq fz1_115_72 fz2_115_72
  · exact match_zero_fix ⟨116, by decide⟩ ⟨72, by decide⟩ p hp j hj hq fz1_116_72 fz2_116_72
  · exact match_zero_fix ⟨117, by decide⟩ ⟨72, by decide⟩ p hp j hj hq fz1_117_72 fz2_117_72
  · exact match_zero_fix ⟨118, by decide⟩ ⟨72, by decide⟩ p hp j hj hq fz1_118_72 fz2_118_72
  · exact pair_119_72 p hp hrep j hj hq
  · exact match_zero_fix ⟨120, by decide⟩ ⟨72, by decide⟩ p hp j hj hq fz1_120_72 fz2_120_72
  · exact match_zero_fix ⟨121, by decide⟩ ⟨72, by decide⟩ p hp j hj hq fz1_121_72 fz2_121_72
  · exact match_zero_fix ⟨122, by decide⟩ ⟨72, by decide⟩ p hp j hj hq fz1_122_72 fz2_122_72
  · exact match_zero_fix ⟨123, by decide⟩ ⟨72, by decide⟩ p hp j hj hq fz1_123_72 fz2_123_72
  · exact match_zero_fix ⟨124, by decide⟩ ⟨72, by decide⟩ p hp j hj hq fz1_124_72 fz2_124_72
  · exact match_zero_fix ⟨125, by decide⟩ ⟨72, by decide⟩ p hp j hj hq fz1_125_72 fz2_125_72
  · exact match_zero_fix ⟨126, by decide⟩ ⟨72, by decide⟩ p hp j hj hq fz1_126_72 fz2_126_72
  · exact match_zero_fix ⟨127, by decide⟩ ⟨72, by decide⟩ p hp j hj hq fz1_127_72 fz2_127_72
  · exact match_zero_fix ⟨128, by decide⟩ ⟨72, by decide⟩ p hp j hj hq fz1_128_72 fz2_128_72
  · exact match_zero_fix ⟨129, by decide⟩ ⟨72, by decide⟩ p hp j hj hq fz1_129_72 fz2_129_72
  · exact match_zero_fix ⟨130, by decide⟩ ⟨72, by decide⟩ p hp j hj hq fz1_130_72 fz2_130_72
  · exact match_zero_fix ⟨131, by decide⟩ ⟨72, by decide⟩ p hp j hj hq fz1_131_72 fz2_131_72
  · exact match_zero_fix ⟨132, by decide⟩ ⟨72, by decide⟩ p hp j hj hq fz1_132_72 fz2_132_72
  · exact match_zero_fix ⟨133, by decide⟩ ⟨72, by decide⟩ p hp j hj hq fz1_133_72 fz2_133_72
  · exact match_zero_fix ⟨134, by decide⟩ ⟨72, by decide⟩ p hp j hj hq fz1_134_72 fz2_134_72
  · exact match_zero_fix ⟨135, by decide⟩ ⟨72, by decide⟩ p hp j hj hq fz1_135_72 fz2_135_72
  · exact match_zero_fix ⟨136, by decide⟩ ⟨72, by decide⟩ p hp j hj hq fz1_136_72 fz2_136_72
  · exact match_zero_fix ⟨137, by decide⟩ ⟨72, by decide⟩ p hp j hj hq fz1_137_72 fz2_137_72
  · exact match_zero_fix ⟨138, by decide⟩ ⟨72, by decide⟩ p hp j hj hq fz1_138_72 fz2_138_72
  · exact match_zero_fix ⟨139, by decide⟩ ⟨72, by decide⟩ p hp j hj hq fz1_139_72 fz2_139_72
  · exact match_zero_fix ⟨140, by decide⟩ ⟨72, by decide⟩ p hp j hj hq fz1_140_72 fz2_140_72
  · exact match_zero_fix ⟨141, by decide⟩ ⟨72, by decide⟩ p hp j hj hq fz1_141_72 fz2_141_72
  · exact match_zero_fix ⟨142, by decide⟩ ⟨72, by decide⟩ p hp j hj hq fz1_142_72 fz2_142_72
  · exact match_zero_fix ⟨143, by decide⟩ ⟨72, by decide⟩ p hp j hj hq fz1_143_72 fz2_143_72
  · exact match_zero_fix ⟨144, by decide⟩ ⟨72, by decide⟩ p hp j hj hq fz1_144_72 fz2_144_72
  · exact match_zero_fix ⟨145, by decide⟩ ⟨72, by decide⟩ p hp j hj hq fz1_145_72 fz2_145_72
  · exact match_zero_fix ⟨146, by decide⟩ ⟨72, by decide⟩ p hp j hj hq fz1_146_72 fz2_146_72
  · exact pair_147_72 p hp hrep j hj hq

theorem master_73 (p : Nat) (hp : p < (Q2.transData.getD 73 []).length)
    (hrep : (Q2.cosetIsRep.getD 73 []).getD p false = true)
    (rK : Fin 148) (j : Nat) (hj : j < (repChars.getD rK.val []).length)
    (hq : (normIsRep.getD rK.val []).getD j false = true) :
    species (Q2.reps (⟨73, by decide⟩ : Fin 148)) (colE2 ⟨73, by decide⟩ p hp)
        (rowE2 rK j hj hq)
      = species (reps (⟨73, by decide⟩ : Fin 148))
        (colE1 ⟨73, by decide⟩ p (transLenTr ⟨73, by decide⟩ p hp)) (rowE1 rK j hj) := by
  rcases rK with ⟨nK, hnK⟩; interval_cases nK
  · exact match_zero_len ⟨0, by decide⟩ ⟨73, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨1, by decide⟩ ⟨73, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨2, by decide⟩ ⟨73, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨3, by decide⟩ ⟨73, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨4, by decide⟩ ⟨73, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨5, by decide⟩ ⟨73, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨6, by decide⟩ ⟨73, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨7, by decide⟩ ⟨73, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨8, by decide⟩ ⟨73, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨9, by decide⟩ ⟨73, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨10, by decide⟩ ⟨73, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨11, by decide⟩ ⟨73, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨12, by decide⟩ ⟨73, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨13, by decide⟩ ⟨73, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨14, by decide⟩ ⟨73, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨15, by decide⟩ ⟨73, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨16, by decide⟩ ⟨73, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨17, by decide⟩ ⟨73, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨18, by decide⟩ ⟨73, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨19, by decide⟩ ⟨73, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨20, by decide⟩ ⟨73, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨21, by decide⟩ ⟨73, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨22, by decide⟩ ⟨73, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨23, by decide⟩ ⟨73, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨24, by decide⟩ ⟨73, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨25, by decide⟩ ⟨73, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨26, by decide⟩ ⟨73, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨27, by decide⟩ ⟨73, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨28, by decide⟩ ⟨73, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨29, by decide⟩ ⟨73, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨30, by decide⟩ ⟨73, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨31, by decide⟩ ⟨73, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨32, by decide⟩ ⟨73, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨33, by decide⟩ ⟨73, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨34, by decide⟩ ⟨73, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨35, by decide⟩ ⟨73, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨36, by decide⟩ ⟨73, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨37, by decide⟩ ⟨73, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨38, by decide⟩ ⟨73, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨39, by decide⟩ ⟨73, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨40, by decide⟩ ⟨73, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨41, by decide⟩ ⟨73, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨42, by decide⟩ ⟨73, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨43, by decide⟩ ⟨73, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨44, by decide⟩ ⟨73, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨45, by decide⟩ ⟨73, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨46, by decide⟩ ⟨73, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨47, by decide⟩ ⟨73, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨48, by decide⟩ ⟨73, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨49, by decide⟩ ⟨73, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨50, by decide⟩ ⟨73, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨51, by decide⟩ ⟨73, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨52, by decide⟩ ⟨73, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨53, by decide⟩ ⟨73, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨54, by decide⟩ ⟨73, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_fix ⟨55, by decide⟩ ⟨73, by decide⟩ p hp j hj hq fz1_55_73 fz2_55_73
  · exact match_zero_fix ⟨56, by decide⟩ ⟨73, by decide⟩ p hp j hj hq fz1_56_73 fz2_56_73
  · exact match_zero_fix ⟨57, by decide⟩ ⟨73, by decide⟩ p hp j hj hq fz1_57_73 fz2_57_73
  · exact match_zero_fix ⟨58, by decide⟩ ⟨73, by decide⟩ p hp j hj hq fz1_58_73 fz2_58_73
  · exact match_zero_fix ⟨59, by decide⟩ ⟨73, by decide⟩ p hp j hj hq fz1_59_73 fz2_59_73
  · exact match_zero_fix ⟨60, by decide⟩ ⟨73, by decide⟩ p hp j hj hq fz1_60_73 fz2_60_73
  · exact match_zero_fix ⟨61, by decide⟩ ⟨73, by decide⟩ p hp j hj hq fz1_61_73 fz2_61_73
  · exact match_zero_fix ⟨62, by decide⟩ ⟨73, by decide⟩ p hp j hj hq fz1_62_73 fz2_62_73
  · exact match_zero_fix ⟨63, by decide⟩ ⟨73, by decide⟩ p hp j hj hq fz1_63_73 fz2_63_73
  · exact match_zero_fix ⟨64, by decide⟩ ⟨73, by decide⟩ p hp j hj hq fz1_64_73 fz2_64_73
  · exact match_zero_fix ⟨65, by decide⟩ ⟨73, by decide⟩ p hp j hj hq fz1_65_73 fz2_65_73
  · exact match_zero_fix ⟨66, by decide⟩ ⟨73, by decide⟩ p hp j hj hq fz1_66_73 fz2_66_73
  · exact match_zero_fix ⟨67, by decide⟩ ⟨73, by decide⟩ p hp j hj hq fz1_67_73 fz2_67_73
  · exact match_zero_fix ⟨68, by decide⟩ ⟨73, by decide⟩ p hp j hj hq fz1_68_73 fz2_68_73
  · exact match_zero_fix ⟨69, by decide⟩ ⟨73, by decide⟩ p hp j hj hq fz1_69_73 fz2_69_73
  · exact match_zero_fix ⟨70, by decide⟩ ⟨73, by decide⟩ p hp j hj hq fz1_70_73 fz2_70_73
  · exact match_zero_fix ⟨71, by decide⟩ ⟨73, by decide⟩ p hp j hj hq fz1_71_73 fz2_71_73
  · exact match_zero_fix ⟨72, by decide⟩ ⟨73, by decide⟩ p hp j hj hq fz1_72_73 fz2_72_73
  · exact pair_73_73 p hp hrep j hj hq
  · exact match_zero_fix ⟨74, by decide⟩ ⟨73, by decide⟩ p hp j hj hq fz1_74_73 fz2_74_73
  · exact match_zero_fix ⟨75, by decide⟩ ⟨73, by decide⟩ p hp j hj hq fz1_75_73 fz2_75_73
  · exact match_zero_fix ⟨76, by decide⟩ ⟨73, by decide⟩ p hp j hj hq fz1_76_73 fz2_76_73
  · exact match_zero_fix ⟨77, by decide⟩ ⟨73, by decide⟩ p hp j hj hq fz1_77_73 fz2_77_73
  · exact match_zero_fix ⟨78, by decide⟩ ⟨73, by decide⟩ p hp j hj hq fz1_78_73 fz2_78_73
  · exact match_zero_fix ⟨79, by decide⟩ ⟨73, by decide⟩ p hp j hj hq fz1_79_73 fz2_79_73
  · exact match_zero_fix ⟨80, by decide⟩ ⟨73, by decide⟩ p hp j hj hq fz1_80_73 fz2_80_73
  · exact match_zero_fix ⟨81, by decide⟩ ⟨73, by decide⟩ p hp j hj hq fz1_81_73 fz2_81_73
  · exact match_zero_fix ⟨82, by decide⟩ ⟨73, by decide⟩ p hp j hj hq fz1_82_73 fz2_82_73
  · exact match_zero_fix ⟨83, by decide⟩ ⟨73, by decide⟩ p hp j hj hq fz1_83_73 fz2_83_73
  · exact match_zero_fix ⟨84, by decide⟩ ⟨73, by decide⟩ p hp j hj hq fz1_84_73 fz2_84_73
  · exact match_zero_fix ⟨85, by decide⟩ ⟨73, by decide⟩ p hp j hj hq fz1_85_73 fz2_85_73
  · exact match_zero_fix ⟨86, by decide⟩ ⟨73, by decide⟩ p hp j hj hq fz1_86_73 fz2_86_73
  · exact match_zero_fix ⟨87, by decide⟩ ⟨73, by decide⟩ p hp j hj hq fz1_87_73 fz2_87_73
  · exact match_zero_fix ⟨88, by decide⟩ ⟨73, by decide⟩ p hp j hj hq fz1_88_73 fz2_88_73
  · exact match_zero_fix ⟨89, by decide⟩ ⟨73, by decide⟩ p hp j hj hq fz1_89_73 fz2_89_73
  · exact match_zero_fix ⟨90, by decide⟩ ⟨73, by decide⟩ p hp j hj hq fz1_90_73 fz2_90_73
  · exact match_zero_fix ⟨91, by decide⟩ ⟨73, by decide⟩ p hp j hj hq fz1_91_73 fz2_91_73
  · exact match_zero_fix ⟨92, by decide⟩ ⟨73, by decide⟩ p hp j hj hq fz1_92_73 fz2_92_73
  · exact match_zero_fix ⟨93, by decide⟩ ⟨73, by decide⟩ p hp j hj hq fz1_93_73 fz2_93_73
  · exact match_zero_fix ⟨94, by decide⟩ ⟨73, by decide⟩ p hp j hj hq fz1_94_73 fz2_94_73
  · exact match_zero_fix ⟨95, by decide⟩ ⟨73, by decide⟩ p hp j hj hq fz1_95_73 fz2_95_73
  · exact match_zero_fix ⟨96, by decide⟩ ⟨73, by decide⟩ p hp j hj hq fz1_96_73 fz2_96_73
  · exact match_zero_fix ⟨97, by decide⟩ ⟨73, by decide⟩ p hp j hj hq fz1_97_73 fz2_97_73
  · exact match_zero_fix ⟨98, by decide⟩ ⟨73, by decide⟩ p hp j hj hq fz1_98_73 fz2_98_73
  · exact match_zero_fix ⟨99, by decide⟩ ⟨73, by decide⟩ p hp j hj hq fz1_99_73 fz2_99_73
  · exact match_zero_fix ⟨100, by decide⟩ ⟨73, by decide⟩ p hp j hj hq fz1_100_73 fz2_100_73
  · exact match_zero_fix ⟨101, by decide⟩ ⟨73, by decide⟩ p hp j hj hq fz1_101_73 fz2_101_73
  · exact match_zero_fix ⟨102, by decide⟩ ⟨73, by decide⟩ p hp j hj hq fz1_102_73 fz2_102_73
  · exact match_zero_fix ⟨103, by decide⟩ ⟨73, by decide⟩ p hp j hj hq fz1_103_73 fz2_103_73
  · exact match_zero_fix ⟨104, by decide⟩ ⟨73, by decide⟩ p hp j hj hq fz1_104_73 fz2_104_73
  · exact match_zero_fix ⟨105, by decide⟩ ⟨73, by decide⟩ p hp j hj hq fz1_105_73 fz2_105_73
  · exact match_zero_fix ⟨106, by decide⟩ ⟨73, by decide⟩ p hp j hj hq fz1_106_73 fz2_106_73
  · exact match_zero_fix ⟨107, by decide⟩ ⟨73, by decide⟩ p hp j hj hq fz1_107_73 fz2_107_73
  · exact match_zero_fix ⟨108, by decide⟩ ⟨73, by decide⟩ p hp j hj hq fz1_108_73 fz2_108_73
  · exact match_zero_fix ⟨109, by decide⟩ ⟨73, by decide⟩ p hp j hj hq fz1_109_73 fz2_109_73
  · exact match_zero_fix ⟨110, by decide⟩ ⟨73, by decide⟩ p hp j hj hq fz1_110_73 fz2_110_73
  · exact match_zero_fix ⟨111, by decide⟩ ⟨73, by decide⟩ p hp j hj hq fz1_111_73 fz2_111_73
  · exact match_zero_fix ⟨112, by decide⟩ ⟨73, by decide⟩ p hp j hj hq fz1_112_73 fz2_112_73
  · exact match_zero_fix ⟨113, by decide⟩ ⟨73, by decide⟩ p hp j hj hq fz1_113_73 fz2_113_73
  · exact match_zero_fix ⟨114, by decide⟩ ⟨73, by decide⟩ p hp j hj hq fz1_114_73 fz2_114_73
  · exact match_zero_fix ⟨115, by decide⟩ ⟨73, by decide⟩ p hp j hj hq fz1_115_73 fz2_115_73
  · exact match_zero_fix ⟨116, by decide⟩ ⟨73, by decide⟩ p hp j hj hq fz1_116_73 fz2_116_73
  · exact match_zero_fix ⟨117, by decide⟩ ⟨73, by decide⟩ p hp j hj hq fz1_117_73 fz2_117_73
  · exact match_zero_fix ⟨118, by decide⟩ ⟨73, by decide⟩ p hp j hj hq fz1_118_73 fz2_118_73
  · exact pair_119_73 p hp hrep j hj hq
  · exact match_zero_fix ⟨120, by decide⟩ ⟨73, by decide⟩ p hp j hj hq fz1_120_73 fz2_120_73
  · exact match_zero_fix ⟨121, by decide⟩ ⟨73, by decide⟩ p hp j hj hq fz1_121_73 fz2_121_73
  · exact match_zero_fix ⟨122, by decide⟩ ⟨73, by decide⟩ p hp j hj hq fz1_122_73 fz2_122_73
  · exact match_zero_fix ⟨123, by decide⟩ ⟨73, by decide⟩ p hp j hj hq fz1_123_73 fz2_123_73
  · exact match_zero_fix ⟨124, by decide⟩ ⟨73, by decide⟩ p hp j hj hq fz1_124_73 fz2_124_73
  · exact match_zero_fix ⟨125, by decide⟩ ⟨73, by decide⟩ p hp j hj hq fz1_125_73 fz2_125_73
  · exact match_zero_fix ⟨126, by decide⟩ ⟨73, by decide⟩ p hp j hj hq fz1_126_73 fz2_126_73
  · exact match_zero_fix ⟨127, by decide⟩ ⟨73, by decide⟩ p hp j hj hq fz1_127_73 fz2_127_73
  · exact match_zero_fix ⟨128, by decide⟩ ⟨73, by decide⟩ p hp j hj hq fz1_128_73 fz2_128_73
  · exact match_zero_fix ⟨129, by decide⟩ ⟨73, by decide⟩ p hp j hj hq fz1_129_73 fz2_129_73
  · exact match_zero_fix ⟨130, by decide⟩ ⟨73, by decide⟩ p hp j hj hq fz1_130_73 fz2_130_73
  · exact match_zero_fix ⟨131, by decide⟩ ⟨73, by decide⟩ p hp j hj hq fz1_131_73 fz2_131_73
  · exact match_zero_fix ⟨132, by decide⟩ ⟨73, by decide⟩ p hp j hj hq fz1_132_73 fz2_132_73
  · exact match_zero_fix ⟨133, by decide⟩ ⟨73, by decide⟩ p hp j hj hq fz1_133_73 fz2_133_73
  · exact match_zero_fix ⟨134, by decide⟩ ⟨73, by decide⟩ p hp j hj hq fz1_134_73 fz2_134_73
  · exact match_zero_fix ⟨135, by decide⟩ ⟨73, by decide⟩ p hp j hj hq fz1_135_73 fz2_135_73
  · exact match_zero_fix ⟨136, by decide⟩ ⟨73, by decide⟩ p hp j hj hq fz1_136_73 fz2_136_73
  · exact match_zero_fix ⟨137, by decide⟩ ⟨73, by decide⟩ p hp j hj hq fz1_137_73 fz2_137_73
  · exact match_zero_fix ⟨138, by decide⟩ ⟨73, by decide⟩ p hp j hj hq fz1_138_73 fz2_138_73
  · exact match_zero_fix ⟨139, by decide⟩ ⟨73, by decide⟩ p hp j hj hq fz1_139_73 fz2_139_73
  · exact match_zero_fix ⟨140, by decide⟩ ⟨73, by decide⟩ p hp j hj hq fz1_140_73 fz2_140_73
  · exact match_zero_fix ⟨141, by decide⟩ ⟨73, by decide⟩ p hp j hj hq fz1_141_73 fz2_141_73
  · exact match_zero_fix ⟨142, by decide⟩ ⟨73, by decide⟩ p hp j hj hq fz1_142_73 fz2_142_73
  · exact match_zero_fix ⟨143, by decide⟩ ⟨73, by decide⟩ p hp j hj hq fz1_143_73 fz2_143_73
  · exact match_zero_fix ⟨144, by decide⟩ ⟨73, by decide⟩ p hp j hj hq fz1_144_73 fz2_144_73
  · exact match_zero_fix ⟨145, by decide⟩ ⟨73, by decide⟩ p hp j hj hq fz1_145_73 fz2_145_73
  · exact match_zero_fix ⟨146, by decide⟩ ⟨73, by decide⟩ p hp j hj hq fz1_146_73 fz2_146_73
  · exact pair_147_73 p hp hrep j hj hq

theorem master_74 (p : Nat) (hp : p < (Q2.transData.getD 74 []).length)
    (hrep : (Q2.cosetIsRep.getD 74 []).getD p false = true)
    (rK : Fin 148) (j : Nat) (hj : j < (repChars.getD rK.val []).length)
    (hq : (normIsRep.getD rK.val []).getD j false = true) :
    species (Q2.reps (⟨74, by decide⟩ : Fin 148)) (colE2 ⟨74, by decide⟩ p hp)
        (rowE2 rK j hj hq)
      = species (reps (⟨74, by decide⟩ : Fin 148))
        (colE1 ⟨74, by decide⟩ p (transLenTr ⟨74, by decide⟩ p hp)) (rowE1 rK j hj) := by
  rcases rK with ⟨nK, hnK⟩; interval_cases nK
  · exact match_zero_len ⟨0, by decide⟩ ⟨74, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨1, by decide⟩ ⟨74, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨2, by decide⟩ ⟨74, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨3, by decide⟩ ⟨74, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨4, by decide⟩ ⟨74, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨5, by decide⟩ ⟨74, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨6, by decide⟩ ⟨74, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨7, by decide⟩ ⟨74, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨8, by decide⟩ ⟨74, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨9, by decide⟩ ⟨74, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨10, by decide⟩ ⟨74, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨11, by decide⟩ ⟨74, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨12, by decide⟩ ⟨74, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨13, by decide⟩ ⟨74, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨14, by decide⟩ ⟨74, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨15, by decide⟩ ⟨74, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨16, by decide⟩ ⟨74, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨17, by decide⟩ ⟨74, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨18, by decide⟩ ⟨74, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨19, by decide⟩ ⟨74, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨20, by decide⟩ ⟨74, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨21, by decide⟩ ⟨74, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨22, by decide⟩ ⟨74, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨23, by decide⟩ ⟨74, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨24, by decide⟩ ⟨74, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨25, by decide⟩ ⟨74, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨26, by decide⟩ ⟨74, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨27, by decide⟩ ⟨74, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨28, by decide⟩ ⟨74, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨29, by decide⟩ ⟨74, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨30, by decide⟩ ⟨74, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨31, by decide⟩ ⟨74, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨32, by decide⟩ ⟨74, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨33, by decide⟩ ⟨74, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨34, by decide⟩ ⟨74, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨35, by decide⟩ ⟨74, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨36, by decide⟩ ⟨74, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨37, by decide⟩ ⟨74, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨38, by decide⟩ ⟨74, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨39, by decide⟩ ⟨74, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨40, by decide⟩ ⟨74, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨41, by decide⟩ ⟨74, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨42, by decide⟩ ⟨74, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨43, by decide⟩ ⟨74, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨44, by decide⟩ ⟨74, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨45, by decide⟩ ⟨74, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨46, by decide⟩ ⟨74, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨47, by decide⟩ ⟨74, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨48, by decide⟩ ⟨74, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨49, by decide⟩ ⟨74, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨50, by decide⟩ ⟨74, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨51, by decide⟩ ⟨74, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨52, by decide⟩ ⟨74, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨53, by decide⟩ ⟨74, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨54, by decide⟩ ⟨74, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_fix ⟨55, by decide⟩ ⟨74, by decide⟩ p hp j hj hq fz1_55_74 fz2_55_74
  · exact match_zero_fix ⟨56, by decide⟩ ⟨74, by decide⟩ p hp j hj hq fz1_56_74 fz2_56_74
  · exact match_zero_fix ⟨57, by decide⟩ ⟨74, by decide⟩ p hp j hj hq fz1_57_74 fz2_57_74
  · exact match_zero_fix ⟨58, by decide⟩ ⟨74, by decide⟩ p hp j hj hq fz1_58_74 fz2_58_74
  · exact match_zero_fix ⟨59, by decide⟩ ⟨74, by decide⟩ p hp j hj hq fz1_59_74 fz2_59_74
  · exact match_zero_fix ⟨60, by decide⟩ ⟨74, by decide⟩ p hp j hj hq fz1_60_74 fz2_60_74
  · exact match_zero_fix ⟨61, by decide⟩ ⟨74, by decide⟩ p hp j hj hq fz1_61_74 fz2_61_74
  · exact match_zero_fix ⟨62, by decide⟩ ⟨74, by decide⟩ p hp j hj hq fz1_62_74 fz2_62_74
  · exact match_zero_fix ⟨63, by decide⟩ ⟨74, by decide⟩ p hp j hj hq fz1_63_74 fz2_63_74
  · exact match_zero_fix ⟨64, by decide⟩ ⟨74, by decide⟩ p hp j hj hq fz1_64_74 fz2_64_74
  · exact match_zero_fix ⟨65, by decide⟩ ⟨74, by decide⟩ p hp j hj hq fz1_65_74 fz2_65_74
  · exact match_zero_fix ⟨66, by decide⟩ ⟨74, by decide⟩ p hp j hj hq fz1_66_74 fz2_66_74
  · exact match_zero_fix ⟨67, by decide⟩ ⟨74, by decide⟩ p hp j hj hq fz1_67_74 fz2_67_74
  · exact match_zero_fix ⟨68, by decide⟩ ⟨74, by decide⟩ p hp j hj hq fz1_68_74 fz2_68_74
  · exact match_zero_fix ⟨69, by decide⟩ ⟨74, by decide⟩ p hp j hj hq fz1_69_74 fz2_69_74
  · exact match_zero_fix ⟨70, by decide⟩ ⟨74, by decide⟩ p hp j hj hq fz1_70_74 fz2_70_74
  · exact match_zero_fix ⟨71, by decide⟩ ⟨74, by decide⟩ p hp j hj hq fz1_71_74 fz2_71_74
  · exact match_zero_fix ⟨72, by decide⟩ ⟨74, by decide⟩ p hp j hj hq fz1_72_74 fz2_72_74
  · exact match_zero_fix ⟨73, by decide⟩ ⟨74, by decide⟩ p hp j hj hq fz1_73_74 fz2_73_74
  · exact pair_74_74 p hp hrep j hj hq
  · exact match_zero_fix ⟨75, by decide⟩ ⟨74, by decide⟩ p hp j hj hq fz1_75_74 fz2_75_74
  · exact match_zero_fix ⟨76, by decide⟩ ⟨74, by decide⟩ p hp j hj hq fz1_76_74 fz2_76_74
  · exact match_zero_fix ⟨77, by decide⟩ ⟨74, by decide⟩ p hp j hj hq fz1_77_74 fz2_77_74
  · exact match_zero_fix ⟨78, by decide⟩ ⟨74, by decide⟩ p hp j hj hq fz1_78_74 fz2_78_74
  · exact match_zero_fix ⟨79, by decide⟩ ⟨74, by decide⟩ p hp j hj hq fz1_79_74 fz2_79_74
  · exact match_zero_fix ⟨80, by decide⟩ ⟨74, by decide⟩ p hp j hj hq fz1_80_74 fz2_80_74
  · exact match_zero_fix ⟨81, by decide⟩ ⟨74, by decide⟩ p hp j hj hq fz1_81_74 fz2_81_74
  · exact match_zero_fix ⟨82, by decide⟩ ⟨74, by decide⟩ p hp j hj hq fz1_82_74 fz2_82_74
  · exact match_zero_fix ⟨83, by decide⟩ ⟨74, by decide⟩ p hp j hj hq fz1_83_74 fz2_83_74
  · exact match_zero_fix ⟨84, by decide⟩ ⟨74, by decide⟩ p hp j hj hq fz1_84_74 fz2_84_74
  · exact match_zero_fix ⟨85, by decide⟩ ⟨74, by decide⟩ p hp j hj hq fz1_85_74 fz2_85_74
  · exact match_zero_fix ⟨86, by decide⟩ ⟨74, by decide⟩ p hp j hj hq fz1_86_74 fz2_86_74
  · exact match_zero_fix ⟨87, by decide⟩ ⟨74, by decide⟩ p hp j hj hq fz1_87_74 fz2_87_74
  · exact match_zero_fix ⟨88, by decide⟩ ⟨74, by decide⟩ p hp j hj hq fz1_88_74 fz2_88_74
  · exact match_zero_fix ⟨89, by decide⟩ ⟨74, by decide⟩ p hp j hj hq fz1_89_74 fz2_89_74
  · exact match_zero_fix ⟨90, by decide⟩ ⟨74, by decide⟩ p hp j hj hq fz1_90_74 fz2_90_74
  · exact match_zero_fix ⟨91, by decide⟩ ⟨74, by decide⟩ p hp j hj hq fz1_91_74 fz2_91_74
  · exact match_zero_fix ⟨92, by decide⟩ ⟨74, by decide⟩ p hp j hj hq fz1_92_74 fz2_92_74
  · exact match_zero_fix ⟨93, by decide⟩ ⟨74, by decide⟩ p hp j hj hq fz1_93_74 fz2_93_74
  · exact match_zero_fix ⟨94, by decide⟩ ⟨74, by decide⟩ p hp j hj hq fz1_94_74 fz2_94_74
  · exact match_zero_fix ⟨95, by decide⟩ ⟨74, by decide⟩ p hp j hj hq fz1_95_74 fz2_95_74
  · exact match_zero_fix ⟨96, by decide⟩ ⟨74, by decide⟩ p hp j hj hq fz1_96_74 fz2_96_74
  · exact match_zero_fix ⟨97, by decide⟩ ⟨74, by decide⟩ p hp j hj hq fz1_97_74 fz2_97_74
  · exact match_zero_fix ⟨98, by decide⟩ ⟨74, by decide⟩ p hp j hj hq fz1_98_74 fz2_98_74
  · exact match_zero_fix ⟨99, by decide⟩ ⟨74, by decide⟩ p hp j hj hq fz1_99_74 fz2_99_74
  · exact match_zero_fix ⟨100, by decide⟩ ⟨74, by decide⟩ p hp j hj hq fz1_100_74 fz2_100_74
  · exact match_zero_fix ⟨101, by decide⟩ ⟨74, by decide⟩ p hp j hj hq fz1_101_74 fz2_101_74
  · exact match_zero_fix ⟨102, by decide⟩ ⟨74, by decide⟩ p hp j hj hq fz1_102_74 fz2_102_74
  · exact match_zero_fix ⟨103, by decide⟩ ⟨74, by decide⟩ p hp j hj hq fz1_103_74 fz2_103_74
  · exact match_zero_fix ⟨104, by decide⟩ ⟨74, by decide⟩ p hp j hj hq fz1_104_74 fz2_104_74
  · exact match_zero_fix ⟨105, by decide⟩ ⟨74, by decide⟩ p hp j hj hq fz1_105_74 fz2_105_74
  · exact match_zero_fix ⟨106, by decide⟩ ⟨74, by decide⟩ p hp j hj hq fz1_106_74 fz2_106_74
  · exact match_zero_fix ⟨107, by decide⟩ ⟨74, by decide⟩ p hp j hj hq fz1_107_74 fz2_107_74
  · exact match_zero_fix ⟨108, by decide⟩ ⟨74, by decide⟩ p hp j hj hq fz1_108_74 fz2_108_74
  · exact match_zero_fix ⟨109, by decide⟩ ⟨74, by decide⟩ p hp j hj hq fz1_109_74 fz2_109_74
  · exact match_zero_fix ⟨110, by decide⟩ ⟨74, by decide⟩ p hp j hj hq fz1_110_74 fz2_110_74
  · exact match_zero_fix ⟨111, by decide⟩ ⟨74, by decide⟩ p hp j hj hq fz1_111_74 fz2_111_74
  · exact match_zero_fix ⟨112, by decide⟩ ⟨74, by decide⟩ p hp j hj hq fz1_112_74 fz2_112_74
  · exact match_zero_fix ⟨113, by decide⟩ ⟨74, by decide⟩ p hp j hj hq fz1_113_74 fz2_113_74
  · exact match_zero_fix ⟨114, by decide⟩ ⟨74, by decide⟩ p hp j hj hq fz1_114_74 fz2_114_74
  · exact match_zero_fix ⟨115, by decide⟩ ⟨74, by decide⟩ p hp j hj hq fz1_115_74 fz2_115_74
  · exact match_zero_fix ⟨116, by decide⟩ ⟨74, by decide⟩ p hp j hj hq fz1_116_74 fz2_116_74
  · exact match_zero_fix ⟨117, by decide⟩ ⟨74, by decide⟩ p hp j hj hq fz1_117_74 fz2_117_74
  · exact match_zero_fix ⟨118, by decide⟩ ⟨74, by decide⟩ p hp j hj hq fz1_118_74 fz2_118_74
  · exact pair_119_74 p hp hrep j hj hq
  · exact match_zero_fix ⟨120, by decide⟩ ⟨74, by decide⟩ p hp j hj hq fz1_120_74 fz2_120_74
  · exact match_zero_fix ⟨121, by decide⟩ ⟨74, by decide⟩ p hp j hj hq fz1_121_74 fz2_121_74
  · exact match_zero_fix ⟨122, by decide⟩ ⟨74, by decide⟩ p hp j hj hq fz1_122_74 fz2_122_74
  · exact match_zero_fix ⟨123, by decide⟩ ⟨74, by decide⟩ p hp j hj hq fz1_123_74 fz2_123_74
  · exact match_zero_fix ⟨124, by decide⟩ ⟨74, by decide⟩ p hp j hj hq fz1_124_74 fz2_124_74
  · exact match_zero_fix ⟨125, by decide⟩ ⟨74, by decide⟩ p hp j hj hq fz1_125_74 fz2_125_74
  · exact match_zero_fix ⟨126, by decide⟩ ⟨74, by decide⟩ p hp j hj hq fz1_126_74 fz2_126_74
  · exact match_zero_fix ⟨127, by decide⟩ ⟨74, by decide⟩ p hp j hj hq fz1_127_74 fz2_127_74
  · exact match_zero_fix ⟨128, by decide⟩ ⟨74, by decide⟩ p hp j hj hq fz1_128_74 fz2_128_74
  · exact match_zero_fix ⟨129, by decide⟩ ⟨74, by decide⟩ p hp j hj hq fz1_129_74 fz2_129_74
  · exact match_zero_fix ⟨130, by decide⟩ ⟨74, by decide⟩ p hp j hj hq fz1_130_74 fz2_130_74
  · exact match_zero_fix ⟨131, by decide⟩ ⟨74, by decide⟩ p hp j hj hq fz1_131_74 fz2_131_74
  · exact match_zero_fix ⟨132, by decide⟩ ⟨74, by decide⟩ p hp j hj hq fz1_132_74 fz2_132_74
  · exact match_zero_fix ⟨133, by decide⟩ ⟨74, by decide⟩ p hp j hj hq fz1_133_74 fz2_133_74
  · exact match_zero_fix ⟨134, by decide⟩ ⟨74, by decide⟩ p hp j hj hq fz1_134_74 fz2_134_74
  · exact match_zero_fix ⟨135, by decide⟩ ⟨74, by decide⟩ p hp j hj hq fz1_135_74 fz2_135_74
  · exact match_zero_fix ⟨136, by decide⟩ ⟨74, by decide⟩ p hp j hj hq fz1_136_74 fz2_136_74
  · exact match_zero_fix ⟨137, by decide⟩ ⟨74, by decide⟩ p hp j hj hq fz1_137_74 fz2_137_74
  · exact match_zero_fix ⟨138, by decide⟩ ⟨74, by decide⟩ p hp j hj hq fz1_138_74 fz2_138_74
  · exact match_zero_fix ⟨139, by decide⟩ ⟨74, by decide⟩ p hp j hj hq fz1_139_74 fz2_139_74
  · exact match_zero_fix ⟨140, by decide⟩ ⟨74, by decide⟩ p hp j hj hq fz1_140_74 fz2_140_74
  · exact match_zero_fix ⟨141, by decide⟩ ⟨74, by decide⟩ p hp j hj hq fz1_141_74 fz2_141_74
  · exact match_zero_fix ⟨142, by decide⟩ ⟨74, by decide⟩ p hp j hj hq fz1_142_74 fz2_142_74
  · exact match_zero_fix ⟨143, by decide⟩ ⟨74, by decide⟩ p hp j hj hq fz1_143_74 fz2_143_74
  · exact match_zero_fix ⟨144, by decide⟩ ⟨74, by decide⟩ p hp j hj hq fz1_144_74 fz2_144_74
  · exact match_zero_fix ⟨145, by decide⟩ ⟨74, by decide⟩ p hp j hj hq fz1_145_74 fz2_145_74
  · exact match_zero_fix ⟨146, by decide⟩ ⟨74, by decide⟩ p hp j hj hq fz1_146_74 fz2_146_74
  · exact pair_147_74 p hp hrep j hj hq

theorem master_75 (p : Nat) (hp : p < (Q2.transData.getD 75 []).length)
    (hrep : (Q2.cosetIsRep.getD 75 []).getD p false = true)
    (rK : Fin 148) (j : Nat) (hj : j < (repChars.getD rK.val []).length)
    (hq : (normIsRep.getD rK.val []).getD j false = true) :
    species (Q2.reps (⟨75, by decide⟩ : Fin 148)) (colE2 ⟨75, by decide⟩ p hp)
        (rowE2 rK j hj hq)
      = species (reps (⟨75, by decide⟩ : Fin 148))
        (colE1 ⟨75, by decide⟩ p (transLenTr ⟨75, by decide⟩ p hp)) (rowE1 rK j hj) := by
  rcases rK with ⟨nK, hnK⟩; interval_cases nK
  · exact match_zero_len ⟨0, by decide⟩ ⟨75, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨1, by decide⟩ ⟨75, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨2, by decide⟩ ⟨75, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨3, by decide⟩ ⟨75, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨4, by decide⟩ ⟨75, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨5, by decide⟩ ⟨75, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨6, by decide⟩ ⟨75, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨7, by decide⟩ ⟨75, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨8, by decide⟩ ⟨75, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨9, by decide⟩ ⟨75, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨10, by decide⟩ ⟨75, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨11, by decide⟩ ⟨75, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨12, by decide⟩ ⟨75, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨13, by decide⟩ ⟨75, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨14, by decide⟩ ⟨75, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨15, by decide⟩ ⟨75, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨16, by decide⟩ ⟨75, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨17, by decide⟩ ⟨75, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨18, by decide⟩ ⟨75, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨19, by decide⟩ ⟨75, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨20, by decide⟩ ⟨75, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨21, by decide⟩ ⟨75, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨22, by decide⟩ ⟨75, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨23, by decide⟩ ⟨75, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨24, by decide⟩ ⟨75, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨25, by decide⟩ ⟨75, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨26, by decide⟩ ⟨75, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨27, by decide⟩ ⟨75, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨28, by decide⟩ ⟨75, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨29, by decide⟩ ⟨75, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨30, by decide⟩ ⟨75, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨31, by decide⟩ ⟨75, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨32, by decide⟩ ⟨75, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨33, by decide⟩ ⟨75, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨34, by decide⟩ ⟨75, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨35, by decide⟩ ⟨75, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨36, by decide⟩ ⟨75, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨37, by decide⟩ ⟨75, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨38, by decide⟩ ⟨75, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨39, by decide⟩ ⟨75, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨40, by decide⟩ ⟨75, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨41, by decide⟩ ⟨75, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨42, by decide⟩ ⟨75, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨43, by decide⟩ ⟨75, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨44, by decide⟩ ⟨75, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨45, by decide⟩ ⟨75, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨46, by decide⟩ ⟨75, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨47, by decide⟩ ⟨75, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨48, by decide⟩ ⟨75, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨49, by decide⟩ ⟨75, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨50, by decide⟩ ⟨75, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨51, by decide⟩ ⟨75, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨52, by decide⟩ ⟨75, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨53, by decide⟩ ⟨75, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨54, by decide⟩ ⟨75, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_fix ⟨55, by decide⟩ ⟨75, by decide⟩ p hp j hj hq fz1_55_75 fz2_55_75
  · exact match_zero_fix ⟨56, by decide⟩ ⟨75, by decide⟩ p hp j hj hq fz1_56_75 fz2_56_75
  · exact match_zero_fix ⟨57, by decide⟩ ⟨75, by decide⟩ p hp j hj hq fz1_57_75 fz2_57_75
  · exact match_zero_fix ⟨58, by decide⟩ ⟨75, by decide⟩ p hp j hj hq fz1_58_75 fz2_58_75
  · exact match_zero_fix ⟨59, by decide⟩ ⟨75, by decide⟩ p hp j hj hq fz1_59_75 fz2_59_75
  · exact match_zero_fix ⟨60, by decide⟩ ⟨75, by decide⟩ p hp j hj hq fz1_60_75 fz2_60_75
  · exact match_zero_fix ⟨61, by decide⟩ ⟨75, by decide⟩ p hp j hj hq fz1_61_75 fz2_61_75
  · exact match_zero_fix ⟨62, by decide⟩ ⟨75, by decide⟩ p hp j hj hq fz1_62_75 fz2_62_75
  · exact match_zero_fix ⟨63, by decide⟩ ⟨75, by decide⟩ p hp j hj hq fz1_63_75 fz2_63_75
  · exact match_zero_fix ⟨64, by decide⟩ ⟨75, by decide⟩ p hp j hj hq fz1_64_75 fz2_64_75
  · exact match_zero_fix ⟨65, by decide⟩ ⟨75, by decide⟩ p hp j hj hq fz1_65_75 fz2_65_75
  · exact match_zero_fix ⟨66, by decide⟩ ⟨75, by decide⟩ p hp j hj hq fz1_66_75 fz2_66_75
  · exact match_zero_fix ⟨67, by decide⟩ ⟨75, by decide⟩ p hp j hj hq fz1_67_75 fz2_67_75
  · exact match_zero_fix ⟨68, by decide⟩ ⟨75, by decide⟩ p hp j hj hq fz1_68_75 fz2_68_75
  · exact match_zero_fix ⟨69, by decide⟩ ⟨75, by decide⟩ p hp j hj hq fz1_69_75 fz2_69_75
  · exact match_zero_fix ⟨70, by decide⟩ ⟨75, by decide⟩ p hp j hj hq fz1_70_75 fz2_70_75
  · exact match_zero_fix ⟨71, by decide⟩ ⟨75, by decide⟩ p hp j hj hq fz1_71_75 fz2_71_75
  · exact match_zero_fix ⟨72, by decide⟩ ⟨75, by decide⟩ p hp j hj hq fz1_72_75 fz2_72_75
  · exact match_zero_fix ⟨73, by decide⟩ ⟨75, by decide⟩ p hp j hj hq fz1_73_75 fz2_73_75
  · exact match_zero_fix ⟨74, by decide⟩ ⟨75, by decide⟩ p hp j hj hq fz1_74_75 fz2_74_75
  · exact pair_75_75 p hp hrep j hj hq
  · exact match_zero_fix ⟨76, by decide⟩ ⟨75, by decide⟩ p hp j hj hq fz1_76_75 fz2_76_75
  · exact match_zero_fix ⟨77, by decide⟩ ⟨75, by decide⟩ p hp j hj hq fz1_77_75 fz2_77_75
  · exact match_zero_fix ⟨78, by decide⟩ ⟨75, by decide⟩ p hp j hj hq fz1_78_75 fz2_78_75
  · exact match_zero_fix ⟨79, by decide⟩ ⟨75, by decide⟩ p hp j hj hq fz1_79_75 fz2_79_75
  · exact match_zero_fix ⟨80, by decide⟩ ⟨75, by decide⟩ p hp j hj hq fz1_80_75 fz2_80_75
  · exact match_zero_fix ⟨81, by decide⟩ ⟨75, by decide⟩ p hp j hj hq fz1_81_75 fz2_81_75
  · exact match_zero_fix ⟨82, by decide⟩ ⟨75, by decide⟩ p hp j hj hq fz1_82_75 fz2_82_75
  · exact match_zero_fix ⟨83, by decide⟩ ⟨75, by decide⟩ p hp j hj hq fz1_83_75 fz2_83_75
  · exact match_zero_fix ⟨84, by decide⟩ ⟨75, by decide⟩ p hp j hj hq fz1_84_75 fz2_84_75
  · exact match_zero_fix ⟨85, by decide⟩ ⟨75, by decide⟩ p hp j hj hq fz1_85_75 fz2_85_75
  · exact match_zero_fix ⟨86, by decide⟩ ⟨75, by decide⟩ p hp j hj hq fz1_86_75 fz2_86_75
  · exact match_zero_fix ⟨87, by decide⟩ ⟨75, by decide⟩ p hp j hj hq fz1_87_75 fz2_87_75
  · exact match_zero_fix ⟨88, by decide⟩ ⟨75, by decide⟩ p hp j hj hq fz1_88_75 fz2_88_75
  · exact match_zero_fix ⟨89, by decide⟩ ⟨75, by decide⟩ p hp j hj hq fz1_89_75 fz2_89_75
  · exact match_zero_fix ⟨90, by decide⟩ ⟨75, by decide⟩ p hp j hj hq fz1_90_75 fz2_90_75
  · exact match_zero_fix ⟨91, by decide⟩ ⟨75, by decide⟩ p hp j hj hq fz1_91_75 fz2_91_75
  · exact match_zero_fix ⟨92, by decide⟩ ⟨75, by decide⟩ p hp j hj hq fz1_92_75 fz2_92_75
  · exact match_zero_fix ⟨93, by decide⟩ ⟨75, by decide⟩ p hp j hj hq fz1_93_75 fz2_93_75
  · exact match_zero_fix ⟨94, by decide⟩ ⟨75, by decide⟩ p hp j hj hq fz1_94_75 fz2_94_75
  · exact match_zero_fix ⟨95, by decide⟩ ⟨75, by decide⟩ p hp j hj hq fz1_95_75 fz2_95_75
  · exact match_zero_fix ⟨96, by decide⟩ ⟨75, by decide⟩ p hp j hj hq fz1_96_75 fz2_96_75
  · exact match_zero_fix ⟨97, by decide⟩ ⟨75, by decide⟩ p hp j hj hq fz1_97_75 fz2_97_75
  · exact match_zero_fix ⟨98, by decide⟩ ⟨75, by decide⟩ p hp j hj hq fz1_98_75 fz2_98_75
  · exact match_zero_fix ⟨99, by decide⟩ ⟨75, by decide⟩ p hp j hj hq fz1_99_75 fz2_99_75
  · exact match_zero_fix ⟨100, by decide⟩ ⟨75, by decide⟩ p hp j hj hq fz1_100_75 fz2_100_75
  · exact match_zero_fix ⟨101, by decide⟩ ⟨75, by decide⟩ p hp j hj hq fz1_101_75 fz2_101_75
  · exact match_zero_fix ⟨102, by decide⟩ ⟨75, by decide⟩ p hp j hj hq fz1_102_75 fz2_102_75
  · exact match_zero_fix ⟨103, by decide⟩ ⟨75, by decide⟩ p hp j hj hq fz1_103_75 fz2_103_75
  · exact match_zero_fix ⟨104, by decide⟩ ⟨75, by decide⟩ p hp j hj hq fz1_104_75 fz2_104_75
  · exact match_zero_fix ⟨105, by decide⟩ ⟨75, by decide⟩ p hp j hj hq fz1_105_75 fz2_105_75
  · exact match_zero_fix ⟨106, by decide⟩ ⟨75, by decide⟩ p hp j hj hq fz1_106_75 fz2_106_75
  · exact match_zero_fix ⟨107, by decide⟩ ⟨75, by decide⟩ p hp j hj hq fz1_107_75 fz2_107_75
  · exact match_zero_fix ⟨108, by decide⟩ ⟨75, by decide⟩ p hp j hj hq fz1_108_75 fz2_108_75
  · exact match_zero_fix ⟨109, by decide⟩ ⟨75, by decide⟩ p hp j hj hq fz1_109_75 fz2_109_75
  · exact match_zero_fix ⟨110, by decide⟩ ⟨75, by decide⟩ p hp j hj hq fz1_110_75 fz2_110_75
  · exact match_zero_fix ⟨111, by decide⟩ ⟨75, by decide⟩ p hp j hj hq fz1_111_75 fz2_111_75
  · exact match_zero_fix ⟨112, by decide⟩ ⟨75, by decide⟩ p hp j hj hq fz1_112_75 fz2_112_75
  · exact match_zero_fix ⟨113, by decide⟩ ⟨75, by decide⟩ p hp j hj hq fz1_113_75 fz2_113_75
  · exact match_zero_fix ⟨114, by decide⟩ ⟨75, by decide⟩ p hp j hj hq fz1_114_75 fz2_114_75
  · exact match_zero_fix ⟨115, by decide⟩ ⟨75, by decide⟩ p hp j hj hq fz1_115_75 fz2_115_75
  · exact match_zero_fix ⟨116, by decide⟩ ⟨75, by decide⟩ p hp j hj hq fz1_116_75 fz2_116_75
  · exact match_zero_fix ⟨117, by decide⟩ ⟨75, by decide⟩ p hp j hj hq fz1_117_75 fz2_117_75
  · exact match_zero_fix ⟨118, by decide⟩ ⟨75, by decide⟩ p hp j hj hq fz1_118_75 fz2_118_75
  · exact match_zero_fix ⟨119, by decide⟩ ⟨75, by decide⟩ p hp j hj hq fz1_119_75 fz2_119_75
  · exact pair_120_75 p hp hrep j hj hq
  · exact match_zero_fix ⟨121, by decide⟩ ⟨75, by decide⟩ p hp j hj hq fz1_121_75 fz2_121_75
  · exact match_zero_fix ⟨122, by decide⟩ ⟨75, by decide⟩ p hp j hj hq fz1_122_75 fz2_122_75
  · exact match_zero_fix ⟨123, by decide⟩ ⟨75, by decide⟩ p hp j hj hq fz1_123_75 fz2_123_75
  · exact match_zero_fix ⟨124, by decide⟩ ⟨75, by decide⟩ p hp j hj hq fz1_124_75 fz2_124_75
  · exact match_zero_fix ⟨125, by decide⟩ ⟨75, by decide⟩ p hp j hj hq fz1_125_75 fz2_125_75
  · exact match_zero_fix ⟨126, by decide⟩ ⟨75, by decide⟩ p hp j hj hq fz1_126_75 fz2_126_75
  · exact match_zero_fix ⟨127, by decide⟩ ⟨75, by decide⟩ p hp j hj hq fz1_127_75 fz2_127_75
  · exact match_zero_fix ⟨128, by decide⟩ ⟨75, by decide⟩ p hp j hj hq fz1_128_75 fz2_128_75
  · exact match_zero_fix ⟨129, by decide⟩ ⟨75, by decide⟩ p hp j hj hq fz1_129_75 fz2_129_75
  · exact match_zero_fix ⟨130, by decide⟩ ⟨75, by decide⟩ p hp j hj hq fz1_130_75 fz2_130_75
  · exact match_zero_fix ⟨131, by decide⟩ ⟨75, by decide⟩ p hp j hj hq fz1_131_75 fz2_131_75
  · exact match_zero_fix ⟨132, by decide⟩ ⟨75, by decide⟩ p hp j hj hq fz1_132_75 fz2_132_75
  · exact match_zero_fix ⟨133, by decide⟩ ⟨75, by decide⟩ p hp j hj hq fz1_133_75 fz2_133_75
  · exact match_zero_fix ⟨134, by decide⟩ ⟨75, by decide⟩ p hp j hj hq fz1_134_75 fz2_134_75
  · exact match_zero_fix ⟨135, by decide⟩ ⟨75, by decide⟩ p hp j hj hq fz1_135_75 fz2_135_75
  · exact match_zero_fix ⟨136, by decide⟩ ⟨75, by decide⟩ p hp j hj hq fz1_136_75 fz2_136_75
  · exact match_zero_fix ⟨137, by decide⟩ ⟨75, by decide⟩ p hp j hj hq fz1_137_75 fz2_137_75
  · exact match_zero_fix ⟨138, by decide⟩ ⟨75, by decide⟩ p hp j hj hq fz1_138_75 fz2_138_75
  · exact match_zero_fix ⟨139, by decide⟩ ⟨75, by decide⟩ p hp j hj hq fz1_139_75 fz2_139_75
  · exact match_zero_fix ⟨140, by decide⟩ ⟨75, by decide⟩ p hp j hj hq fz1_140_75 fz2_140_75
  · exact match_zero_fix ⟨141, by decide⟩ ⟨75, by decide⟩ p hp j hj hq fz1_141_75 fz2_141_75
  · exact match_zero_fix ⟨142, by decide⟩ ⟨75, by decide⟩ p hp j hj hq fz1_142_75 fz2_142_75
  · exact match_zero_fix ⟨143, by decide⟩ ⟨75, by decide⟩ p hp j hj hq fz1_143_75 fz2_143_75
  · exact match_zero_fix ⟨144, by decide⟩ ⟨75, by decide⟩ p hp j hj hq fz1_144_75 fz2_144_75
  · exact match_zero_fix ⟨145, by decide⟩ ⟨75, by decide⟩ p hp j hj hq fz1_145_75 fz2_145_75
  · exact match_zero_fix ⟨146, by decide⟩ ⟨75, by decide⟩ p hp j hj hq fz1_146_75 fz2_146_75
  · exact pair_147_75 p hp hrep j hj hq

theorem master_76 (p : Nat) (hp : p < (Q2.transData.getD 76 []).length)
    (hrep : (Q2.cosetIsRep.getD 76 []).getD p false = true)
    (rK : Fin 148) (j : Nat) (hj : j < (repChars.getD rK.val []).length)
    (hq : (normIsRep.getD rK.val []).getD j false = true) :
    species (Q2.reps (⟨76, by decide⟩ : Fin 148)) (colE2 ⟨76, by decide⟩ p hp)
        (rowE2 rK j hj hq)
      = species (reps (⟨76, by decide⟩ : Fin 148))
        (colE1 ⟨76, by decide⟩ p (transLenTr ⟨76, by decide⟩ p hp)) (rowE1 rK j hj) := by
  rcases rK with ⟨nK, hnK⟩; interval_cases nK
  · exact match_zero_len ⟨0, by decide⟩ ⟨76, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨1, by decide⟩ ⟨76, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨2, by decide⟩ ⟨76, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨3, by decide⟩ ⟨76, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨4, by decide⟩ ⟨76, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨5, by decide⟩ ⟨76, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨6, by decide⟩ ⟨76, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨7, by decide⟩ ⟨76, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨8, by decide⟩ ⟨76, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨9, by decide⟩ ⟨76, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨10, by decide⟩ ⟨76, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨11, by decide⟩ ⟨76, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨12, by decide⟩ ⟨76, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨13, by decide⟩ ⟨76, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨14, by decide⟩ ⟨76, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨15, by decide⟩ ⟨76, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨16, by decide⟩ ⟨76, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨17, by decide⟩ ⟨76, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨18, by decide⟩ ⟨76, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨19, by decide⟩ ⟨76, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨20, by decide⟩ ⟨76, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨21, by decide⟩ ⟨76, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨22, by decide⟩ ⟨76, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨23, by decide⟩ ⟨76, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨24, by decide⟩ ⟨76, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨25, by decide⟩ ⟨76, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨26, by decide⟩ ⟨76, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨27, by decide⟩ ⟨76, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨28, by decide⟩ ⟨76, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨29, by decide⟩ ⟨76, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨30, by decide⟩ ⟨76, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨31, by decide⟩ ⟨76, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨32, by decide⟩ ⟨76, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨33, by decide⟩ ⟨76, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨34, by decide⟩ ⟨76, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨35, by decide⟩ ⟨76, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨36, by decide⟩ ⟨76, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨37, by decide⟩ ⟨76, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨38, by decide⟩ ⟨76, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨39, by decide⟩ ⟨76, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨40, by decide⟩ ⟨76, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨41, by decide⟩ ⟨76, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨42, by decide⟩ ⟨76, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨43, by decide⟩ ⟨76, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨44, by decide⟩ ⟨76, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨45, by decide⟩ ⟨76, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨46, by decide⟩ ⟨76, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨47, by decide⟩ ⟨76, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨48, by decide⟩ ⟨76, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨49, by decide⟩ ⟨76, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨50, by decide⟩ ⟨76, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨51, by decide⟩ ⟨76, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨52, by decide⟩ ⟨76, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨53, by decide⟩ ⟨76, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨54, by decide⟩ ⟨76, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_fix ⟨55, by decide⟩ ⟨76, by decide⟩ p hp j hj hq fz1_55_76 fz2_55_76
  · exact match_zero_fix ⟨56, by decide⟩ ⟨76, by decide⟩ p hp j hj hq fz1_56_76 fz2_56_76
  · exact match_zero_fix ⟨57, by decide⟩ ⟨76, by decide⟩ p hp j hj hq fz1_57_76 fz2_57_76
  · exact match_zero_fix ⟨58, by decide⟩ ⟨76, by decide⟩ p hp j hj hq fz1_58_76 fz2_58_76
  · exact match_zero_fix ⟨59, by decide⟩ ⟨76, by decide⟩ p hp j hj hq fz1_59_76 fz2_59_76
  · exact match_zero_fix ⟨60, by decide⟩ ⟨76, by decide⟩ p hp j hj hq fz1_60_76 fz2_60_76
  · exact match_zero_fix ⟨61, by decide⟩ ⟨76, by decide⟩ p hp j hj hq fz1_61_76 fz2_61_76
  · exact match_zero_fix ⟨62, by decide⟩ ⟨76, by decide⟩ p hp j hj hq fz1_62_76 fz2_62_76
  · exact match_zero_fix ⟨63, by decide⟩ ⟨76, by decide⟩ p hp j hj hq fz1_63_76 fz2_63_76
  · exact match_zero_fix ⟨64, by decide⟩ ⟨76, by decide⟩ p hp j hj hq fz1_64_76 fz2_64_76
  · exact match_zero_fix ⟨65, by decide⟩ ⟨76, by decide⟩ p hp j hj hq fz1_65_76 fz2_65_76
  · exact match_zero_fix ⟨66, by decide⟩ ⟨76, by decide⟩ p hp j hj hq fz1_66_76 fz2_66_76
  · exact match_zero_fix ⟨67, by decide⟩ ⟨76, by decide⟩ p hp j hj hq fz1_67_76 fz2_67_76
  · exact match_zero_fix ⟨68, by decide⟩ ⟨76, by decide⟩ p hp j hj hq fz1_68_76 fz2_68_76
  · exact match_zero_fix ⟨69, by decide⟩ ⟨76, by decide⟩ p hp j hj hq fz1_69_76 fz2_69_76
  · exact match_zero_fix ⟨70, by decide⟩ ⟨76, by decide⟩ p hp j hj hq fz1_70_76 fz2_70_76
  · exact match_zero_fix ⟨71, by decide⟩ ⟨76, by decide⟩ p hp j hj hq fz1_71_76 fz2_71_76
  · exact match_zero_fix ⟨72, by decide⟩ ⟨76, by decide⟩ p hp j hj hq fz1_72_76 fz2_72_76
  · exact match_zero_fix ⟨73, by decide⟩ ⟨76, by decide⟩ p hp j hj hq fz1_73_76 fz2_73_76
  · exact match_zero_fix ⟨74, by decide⟩ ⟨76, by decide⟩ p hp j hj hq fz1_74_76 fz2_74_76
  · exact match_zero_fix ⟨75, by decide⟩ ⟨76, by decide⟩ p hp j hj hq fz1_75_76 fz2_75_76
  · exact pair_76_76 p hp hrep j hj hq
  · exact match_zero_fix ⟨77, by decide⟩ ⟨76, by decide⟩ p hp j hj hq fz1_77_76 fz2_77_76
  · exact match_zero_fix ⟨78, by decide⟩ ⟨76, by decide⟩ p hp j hj hq fz1_78_76 fz2_78_76
  · exact match_zero_fix ⟨79, by decide⟩ ⟨76, by decide⟩ p hp j hj hq fz1_79_76 fz2_79_76
  · exact match_zero_fix ⟨80, by decide⟩ ⟨76, by decide⟩ p hp j hj hq fz1_80_76 fz2_80_76
  · exact match_zero_fix ⟨81, by decide⟩ ⟨76, by decide⟩ p hp j hj hq fz1_81_76 fz2_81_76
  · exact match_zero_fix ⟨82, by decide⟩ ⟨76, by decide⟩ p hp j hj hq fz1_82_76 fz2_82_76
  · exact match_zero_fix ⟨83, by decide⟩ ⟨76, by decide⟩ p hp j hj hq fz1_83_76 fz2_83_76
  · exact match_zero_fix ⟨84, by decide⟩ ⟨76, by decide⟩ p hp j hj hq fz1_84_76 fz2_84_76
  · exact match_zero_fix ⟨85, by decide⟩ ⟨76, by decide⟩ p hp j hj hq fz1_85_76 fz2_85_76
  · exact match_zero_fix ⟨86, by decide⟩ ⟨76, by decide⟩ p hp j hj hq fz1_86_76 fz2_86_76
  · exact match_zero_fix ⟨87, by decide⟩ ⟨76, by decide⟩ p hp j hj hq fz1_87_76 fz2_87_76
  · exact match_zero_fix ⟨88, by decide⟩ ⟨76, by decide⟩ p hp j hj hq fz1_88_76 fz2_88_76
  · exact match_zero_fix ⟨89, by decide⟩ ⟨76, by decide⟩ p hp j hj hq fz1_89_76 fz2_89_76
  · exact match_zero_fix ⟨90, by decide⟩ ⟨76, by decide⟩ p hp j hj hq fz1_90_76 fz2_90_76
  · exact match_zero_fix ⟨91, by decide⟩ ⟨76, by decide⟩ p hp j hj hq fz1_91_76 fz2_91_76
  · exact match_zero_fix ⟨92, by decide⟩ ⟨76, by decide⟩ p hp j hj hq fz1_92_76 fz2_92_76
  · exact match_zero_fix ⟨93, by decide⟩ ⟨76, by decide⟩ p hp j hj hq fz1_93_76 fz2_93_76
  · exact match_zero_fix ⟨94, by decide⟩ ⟨76, by decide⟩ p hp j hj hq fz1_94_76 fz2_94_76
  · exact match_zero_fix ⟨95, by decide⟩ ⟨76, by decide⟩ p hp j hj hq fz1_95_76 fz2_95_76
  · exact match_zero_fix ⟨96, by decide⟩ ⟨76, by decide⟩ p hp j hj hq fz1_96_76 fz2_96_76
  · exact match_zero_fix ⟨97, by decide⟩ ⟨76, by decide⟩ p hp j hj hq fz1_97_76 fz2_97_76
  · exact match_zero_fix ⟨98, by decide⟩ ⟨76, by decide⟩ p hp j hj hq fz1_98_76 fz2_98_76
  · exact match_zero_fix ⟨99, by decide⟩ ⟨76, by decide⟩ p hp j hj hq fz1_99_76 fz2_99_76
  · exact match_zero_fix ⟨100, by decide⟩ ⟨76, by decide⟩ p hp j hj hq fz1_100_76 fz2_100_76
  · exact match_zero_fix ⟨101, by decide⟩ ⟨76, by decide⟩ p hp j hj hq fz1_101_76 fz2_101_76
  · exact match_zero_fix ⟨102, by decide⟩ ⟨76, by decide⟩ p hp j hj hq fz1_102_76 fz2_102_76
  · exact match_zero_fix ⟨103, by decide⟩ ⟨76, by decide⟩ p hp j hj hq fz1_103_76 fz2_103_76
  · exact match_zero_fix ⟨104, by decide⟩ ⟨76, by decide⟩ p hp j hj hq fz1_104_76 fz2_104_76
  · exact match_zero_fix ⟨105, by decide⟩ ⟨76, by decide⟩ p hp j hj hq fz1_105_76 fz2_105_76
  · exact match_zero_fix ⟨106, by decide⟩ ⟨76, by decide⟩ p hp j hj hq fz1_106_76 fz2_106_76
  · exact match_zero_fix ⟨107, by decide⟩ ⟨76, by decide⟩ p hp j hj hq fz1_107_76 fz2_107_76
  · exact match_zero_fix ⟨108, by decide⟩ ⟨76, by decide⟩ p hp j hj hq fz1_108_76 fz2_108_76
  · exact match_zero_fix ⟨109, by decide⟩ ⟨76, by decide⟩ p hp j hj hq fz1_109_76 fz2_109_76
  · exact match_zero_fix ⟨110, by decide⟩ ⟨76, by decide⟩ p hp j hj hq fz1_110_76 fz2_110_76
  · exact match_zero_fix ⟨111, by decide⟩ ⟨76, by decide⟩ p hp j hj hq fz1_111_76 fz2_111_76
  · exact match_zero_fix ⟨112, by decide⟩ ⟨76, by decide⟩ p hp j hj hq fz1_112_76 fz2_112_76
  · exact match_zero_fix ⟨113, by decide⟩ ⟨76, by decide⟩ p hp j hj hq fz1_113_76 fz2_113_76
  · exact match_zero_fix ⟨114, by decide⟩ ⟨76, by decide⟩ p hp j hj hq fz1_114_76 fz2_114_76
  · exact match_zero_fix ⟨115, by decide⟩ ⟨76, by decide⟩ p hp j hj hq fz1_115_76 fz2_115_76
  · exact match_zero_fix ⟨116, by decide⟩ ⟨76, by decide⟩ p hp j hj hq fz1_116_76 fz2_116_76
  · exact match_zero_fix ⟨117, by decide⟩ ⟨76, by decide⟩ p hp j hj hq fz1_117_76 fz2_117_76
  · exact match_zero_fix ⟨118, by decide⟩ ⟨76, by decide⟩ p hp j hj hq fz1_118_76 fz2_118_76
  · exact match_zero_fix ⟨119, by decide⟩ ⟨76, by decide⟩ p hp j hj hq fz1_119_76 fz2_119_76
  · exact pair_120_76 p hp hrep j hj hq
  · exact match_zero_fix ⟨121, by decide⟩ ⟨76, by decide⟩ p hp j hj hq fz1_121_76 fz2_121_76
  · exact match_zero_fix ⟨122, by decide⟩ ⟨76, by decide⟩ p hp j hj hq fz1_122_76 fz2_122_76
  · exact match_zero_fix ⟨123, by decide⟩ ⟨76, by decide⟩ p hp j hj hq fz1_123_76 fz2_123_76
  · exact match_zero_fix ⟨124, by decide⟩ ⟨76, by decide⟩ p hp j hj hq fz1_124_76 fz2_124_76
  · exact match_zero_fix ⟨125, by decide⟩ ⟨76, by decide⟩ p hp j hj hq fz1_125_76 fz2_125_76
  · exact match_zero_fix ⟨126, by decide⟩ ⟨76, by decide⟩ p hp j hj hq fz1_126_76 fz2_126_76
  · exact match_zero_fix ⟨127, by decide⟩ ⟨76, by decide⟩ p hp j hj hq fz1_127_76 fz2_127_76
  · exact match_zero_fix ⟨128, by decide⟩ ⟨76, by decide⟩ p hp j hj hq fz1_128_76 fz2_128_76
  · exact match_zero_fix ⟨129, by decide⟩ ⟨76, by decide⟩ p hp j hj hq fz1_129_76 fz2_129_76
  · exact match_zero_fix ⟨130, by decide⟩ ⟨76, by decide⟩ p hp j hj hq fz1_130_76 fz2_130_76
  · exact match_zero_fix ⟨131, by decide⟩ ⟨76, by decide⟩ p hp j hj hq fz1_131_76 fz2_131_76
  · exact match_zero_fix ⟨132, by decide⟩ ⟨76, by decide⟩ p hp j hj hq fz1_132_76 fz2_132_76
  · exact match_zero_fix ⟨133, by decide⟩ ⟨76, by decide⟩ p hp j hj hq fz1_133_76 fz2_133_76
  · exact match_zero_fix ⟨134, by decide⟩ ⟨76, by decide⟩ p hp j hj hq fz1_134_76 fz2_134_76
  · exact match_zero_fix ⟨135, by decide⟩ ⟨76, by decide⟩ p hp j hj hq fz1_135_76 fz2_135_76
  · exact match_zero_fix ⟨136, by decide⟩ ⟨76, by decide⟩ p hp j hj hq fz1_136_76 fz2_136_76
  · exact match_zero_fix ⟨137, by decide⟩ ⟨76, by decide⟩ p hp j hj hq fz1_137_76 fz2_137_76
  · exact match_zero_fix ⟨138, by decide⟩ ⟨76, by decide⟩ p hp j hj hq fz1_138_76 fz2_138_76
  · exact match_zero_fix ⟨139, by decide⟩ ⟨76, by decide⟩ p hp j hj hq fz1_139_76 fz2_139_76
  · exact match_zero_fix ⟨140, by decide⟩ ⟨76, by decide⟩ p hp j hj hq fz1_140_76 fz2_140_76
  · exact match_zero_fix ⟨141, by decide⟩ ⟨76, by decide⟩ p hp j hj hq fz1_141_76 fz2_141_76
  · exact match_zero_fix ⟨142, by decide⟩ ⟨76, by decide⟩ p hp j hj hq fz1_142_76 fz2_142_76
  · exact match_zero_fix ⟨143, by decide⟩ ⟨76, by decide⟩ p hp j hj hq fz1_143_76 fz2_143_76
  · exact match_zero_fix ⟨144, by decide⟩ ⟨76, by decide⟩ p hp j hj hq fz1_144_76 fz2_144_76
  · exact match_zero_fix ⟨145, by decide⟩ ⟨76, by decide⟩ p hp j hj hq fz1_145_76 fz2_145_76
  · exact match_zero_fix ⟨146, by decide⟩ ⟨76, by decide⟩ p hp j hj hq fz1_146_76 fz2_146_76
  · exact pair_147_76 p hp hrep j hj hq

theorem master_77 (p : Nat) (hp : p < (Q2.transData.getD 77 []).length)
    (hrep : (Q2.cosetIsRep.getD 77 []).getD p false = true)
    (rK : Fin 148) (j : Nat) (hj : j < (repChars.getD rK.val []).length)
    (hq : (normIsRep.getD rK.val []).getD j false = true) :
    species (Q2.reps (⟨77, by decide⟩ : Fin 148)) (colE2 ⟨77, by decide⟩ p hp)
        (rowE2 rK j hj hq)
      = species (reps (⟨77, by decide⟩ : Fin 148))
        (colE1 ⟨77, by decide⟩ p (transLenTr ⟨77, by decide⟩ p hp)) (rowE1 rK j hj) := by
  rcases rK with ⟨nK, hnK⟩; interval_cases nK
  · exact match_zero_len ⟨0, by decide⟩ ⟨77, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨1, by decide⟩ ⟨77, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨2, by decide⟩ ⟨77, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨3, by decide⟩ ⟨77, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨4, by decide⟩ ⟨77, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨5, by decide⟩ ⟨77, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨6, by decide⟩ ⟨77, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨7, by decide⟩ ⟨77, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨8, by decide⟩ ⟨77, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨9, by decide⟩ ⟨77, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨10, by decide⟩ ⟨77, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨11, by decide⟩ ⟨77, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨12, by decide⟩ ⟨77, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨13, by decide⟩ ⟨77, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨14, by decide⟩ ⟨77, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨15, by decide⟩ ⟨77, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨16, by decide⟩ ⟨77, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨17, by decide⟩ ⟨77, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨18, by decide⟩ ⟨77, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨19, by decide⟩ ⟨77, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨20, by decide⟩ ⟨77, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨21, by decide⟩ ⟨77, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨22, by decide⟩ ⟨77, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨23, by decide⟩ ⟨77, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨24, by decide⟩ ⟨77, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨25, by decide⟩ ⟨77, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨26, by decide⟩ ⟨77, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨27, by decide⟩ ⟨77, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨28, by decide⟩ ⟨77, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨29, by decide⟩ ⟨77, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨30, by decide⟩ ⟨77, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨31, by decide⟩ ⟨77, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨32, by decide⟩ ⟨77, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨33, by decide⟩ ⟨77, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨34, by decide⟩ ⟨77, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨35, by decide⟩ ⟨77, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨36, by decide⟩ ⟨77, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨37, by decide⟩ ⟨77, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨38, by decide⟩ ⟨77, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨39, by decide⟩ ⟨77, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨40, by decide⟩ ⟨77, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨41, by decide⟩ ⟨77, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨42, by decide⟩ ⟨77, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨43, by decide⟩ ⟨77, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨44, by decide⟩ ⟨77, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨45, by decide⟩ ⟨77, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨46, by decide⟩ ⟨77, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨47, by decide⟩ ⟨77, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨48, by decide⟩ ⟨77, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨49, by decide⟩ ⟨77, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨50, by decide⟩ ⟨77, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨51, by decide⟩ ⟨77, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨52, by decide⟩ ⟨77, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨53, by decide⟩ ⟨77, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨54, by decide⟩ ⟨77, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_fix ⟨55, by decide⟩ ⟨77, by decide⟩ p hp j hj hq fz1_55_77 fz2_55_77
  · exact match_zero_fix ⟨56, by decide⟩ ⟨77, by decide⟩ p hp j hj hq fz1_56_77 fz2_56_77
  · exact match_zero_fix ⟨57, by decide⟩ ⟨77, by decide⟩ p hp j hj hq fz1_57_77 fz2_57_77
  · exact match_zero_fix ⟨58, by decide⟩ ⟨77, by decide⟩ p hp j hj hq fz1_58_77 fz2_58_77
  · exact match_zero_fix ⟨59, by decide⟩ ⟨77, by decide⟩ p hp j hj hq fz1_59_77 fz2_59_77
  · exact match_zero_fix ⟨60, by decide⟩ ⟨77, by decide⟩ p hp j hj hq fz1_60_77 fz2_60_77
  · exact match_zero_fix ⟨61, by decide⟩ ⟨77, by decide⟩ p hp j hj hq fz1_61_77 fz2_61_77
  · exact match_zero_fix ⟨62, by decide⟩ ⟨77, by decide⟩ p hp j hj hq fz1_62_77 fz2_62_77
  · exact match_zero_fix ⟨63, by decide⟩ ⟨77, by decide⟩ p hp j hj hq fz1_63_77 fz2_63_77
  · exact match_zero_fix ⟨64, by decide⟩ ⟨77, by decide⟩ p hp j hj hq fz1_64_77 fz2_64_77
  · exact match_zero_fix ⟨65, by decide⟩ ⟨77, by decide⟩ p hp j hj hq fz1_65_77 fz2_65_77
  · exact match_zero_fix ⟨66, by decide⟩ ⟨77, by decide⟩ p hp j hj hq fz1_66_77 fz2_66_77
  · exact match_zero_fix ⟨67, by decide⟩ ⟨77, by decide⟩ p hp j hj hq fz1_67_77 fz2_67_77
  · exact match_zero_fix ⟨68, by decide⟩ ⟨77, by decide⟩ p hp j hj hq fz1_68_77 fz2_68_77
  · exact match_zero_fix ⟨69, by decide⟩ ⟨77, by decide⟩ p hp j hj hq fz1_69_77 fz2_69_77
  · exact match_zero_fix ⟨70, by decide⟩ ⟨77, by decide⟩ p hp j hj hq fz1_70_77 fz2_70_77
  · exact match_zero_fix ⟨71, by decide⟩ ⟨77, by decide⟩ p hp j hj hq fz1_71_77 fz2_71_77
  · exact match_zero_fix ⟨72, by decide⟩ ⟨77, by decide⟩ p hp j hj hq fz1_72_77 fz2_72_77
  · exact match_zero_fix ⟨73, by decide⟩ ⟨77, by decide⟩ p hp j hj hq fz1_73_77 fz2_73_77
  · exact match_zero_fix ⟨74, by decide⟩ ⟨77, by decide⟩ p hp j hj hq fz1_74_77 fz2_74_77
  · exact match_zero_fix ⟨75, by decide⟩ ⟨77, by decide⟩ p hp j hj hq fz1_75_77 fz2_75_77
  · exact match_zero_fix ⟨76, by decide⟩ ⟨77, by decide⟩ p hp j hj hq fz1_76_77 fz2_76_77
  · exact pair_77_77 p hp hrep j hj hq
  · exact match_zero_fix ⟨78, by decide⟩ ⟨77, by decide⟩ p hp j hj hq fz1_78_77 fz2_78_77
  · exact match_zero_fix ⟨79, by decide⟩ ⟨77, by decide⟩ p hp j hj hq fz1_79_77 fz2_79_77
  · exact match_zero_fix ⟨80, by decide⟩ ⟨77, by decide⟩ p hp j hj hq fz1_80_77 fz2_80_77
  · exact match_zero_fix ⟨81, by decide⟩ ⟨77, by decide⟩ p hp j hj hq fz1_81_77 fz2_81_77
  · exact match_zero_fix ⟨82, by decide⟩ ⟨77, by decide⟩ p hp j hj hq fz1_82_77 fz2_82_77
  · exact match_zero_fix ⟨83, by decide⟩ ⟨77, by decide⟩ p hp j hj hq fz1_83_77 fz2_83_77
  · exact match_zero_fix ⟨84, by decide⟩ ⟨77, by decide⟩ p hp j hj hq fz1_84_77 fz2_84_77
  · exact match_zero_fix ⟨85, by decide⟩ ⟨77, by decide⟩ p hp j hj hq fz1_85_77 fz2_85_77
  · exact match_zero_fix ⟨86, by decide⟩ ⟨77, by decide⟩ p hp j hj hq fz1_86_77 fz2_86_77
  · exact match_zero_fix ⟨87, by decide⟩ ⟨77, by decide⟩ p hp j hj hq fz1_87_77 fz2_87_77
  · exact match_zero_fix ⟨88, by decide⟩ ⟨77, by decide⟩ p hp j hj hq fz1_88_77 fz2_88_77
  · exact match_zero_fix ⟨89, by decide⟩ ⟨77, by decide⟩ p hp j hj hq fz1_89_77 fz2_89_77
  · exact match_zero_fix ⟨90, by decide⟩ ⟨77, by decide⟩ p hp j hj hq fz1_90_77 fz2_90_77
  · exact match_zero_fix ⟨91, by decide⟩ ⟨77, by decide⟩ p hp j hj hq fz1_91_77 fz2_91_77
  · exact match_zero_fix ⟨92, by decide⟩ ⟨77, by decide⟩ p hp j hj hq fz1_92_77 fz2_92_77
  · exact match_zero_fix ⟨93, by decide⟩ ⟨77, by decide⟩ p hp j hj hq fz1_93_77 fz2_93_77
  · exact match_zero_fix ⟨94, by decide⟩ ⟨77, by decide⟩ p hp j hj hq fz1_94_77 fz2_94_77
  · exact match_zero_fix ⟨95, by decide⟩ ⟨77, by decide⟩ p hp j hj hq fz1_95_77 fz2_95_77
  · exact match_zero_fix ⟨96, by decide⟩ ⟨77, by decide⟩ p hp j hj hq fz1_96_77 fz2_96_77
  · exact match_zero_fix ⟨97, by decide⟩ ⟨77, by decide⟩ p hp j hj hq fz1_97_77 fz2_97_77
  · exact match_zero_fix ⟨98, by decide⟩ ⟨77, by decide⟩ p hp j hj hq fz1_98_77 fz2_98_77
  · exact match_zero_fix ⟨99, by decide⟩ ⟨77, by decide⟩ p hp j hj hq fz1_99_77 fz2_99_77
  · exact match_zero_fix ⟨100, by decide⟩ ⟨77, by decide⟩ p hp j hj hq fz1_100_77 fz2_100_77
  · exact match_zero_fix ⟨101, by decide⟩ ⟨77, by decide⟩ p hp j hj hq fz1_101_77 fz2_101_77
  · exact match_zero_fix ⟨102, by decide⟩ ⟨77, by decide⟩ p hp j hj hq fz1_102_77 fz2_102_77
  · exact match_zero_fix ⟨103, by decide⟩ ⟨77, by decide⟩ p hp j hj hq fz1_103_77 fz2_103_77
  · exact match_zero_fix ⟨104, by decide⟩ ⟨77, by decide⟩ p hp j hj hq fz1_104_77 fz2_104_77
  · exact match_zero_fix ⟨105, by decide⟩ ⟨77, by decide⟩ p hp j hj hq fz1_105_77 fz2_105_77
  · exact match_zero_fix ⟨106, by decide⟩ ⟨77, by decide⟩ p hp j hj hq fz1_106_77 fz2_106_77
  · exact match_zero_fix ⟨107, by decide⟩ ⟨77, by decide⟩ p hp j hj hq fz1_107_77 fz2_107_77
  · exact match_zero_fix ⟨108, by decide⟩ ⟨77, by decide⟩ p hp j hj hq fz1_108_77 fz2_108_77
  · exact match_zero_fix ⟨109, by decide⟩ ⟨77, by decide⟩ p hp j hj hq fz1_109_77 fz2_109_77
  · exact match_zero_fix ⟨110, by decide⟩ ⟨77, by decide⟩ p hp j hj hq fz1_110_77 fz2_110_77
  · exact match_zero_fix ⟨111, by decide⟩ ⟨77, by decide⟩ p hp j hj hq fz1_111_77 fz2_111_77
  · exact match_zero_fix ⟨112, by decide⟩ ⟨77, by decide⟩ p hp j hj hq fz1_112_77 fz2_112_77
  · exact match_zero_fix ⟨113, by decide⟩ ⟨77, by decide⟩ p hp j hj hq fz1_113_77 fz2_113_77
  · exact match_zero_fix ⟨114, by decide⟩ ⟨77, by decide⟩ p hp j hj hq fz1_114_77 fz2_114_77
  · exact match_zero_fix ⟨115, by decide⟩ ⟨77, by decide⟩ p hp j hj hq fz1_115_77 fz2_115_77
  · exact match_zero_fix ⟨116, by decide⟩ ⟨77, by decide⟩ p hp j hj hq fz1_116_77 fz2_116_77
  · exact match_zero_fix ⟨117, by decide⟩ ⟨77, by decide⟩ p hp j hj hq fz1_117_77 fz2_117_77
  · exact match_zero_fix ⟨118, by decide⟩ ⟨77, by decide⟩ p hp j hj hq fz1_118_77 fz2_118_77
  · exact match_zero_fix ⟨119, by decide⟩ ⟨77, by decide⟩ p hp j hj hq fz1_119_77 fz2_119_77
  · exact pair_120_77 p hp hrep j hj hq
  · exact match_zero_fix ⟨121, by decide⟩ ⟨77, by decide⟩ p hp j hj hq fz1_121_77 fz2_121_77
  · exact match_zero_fix ⟨122, by decide⟩ ⟨77, by decide⟩ p hp j hj hq fz1_122_77 fz2_122_77
  · exact match_zero_fix ⟨123, by decide⟩ ⟨77, by decide⟩ p hp j hj hq fz1_123_77 fz2_123_77
  · exact match_zero_fix ⟨124, by decide⟩ ⟨77, by decide⟩ p hp j hj hq fz1_124_77 fz2_124_77
  · exact match_zero_fix ⟨125, by decide⟩ ⟨77, by decide⟩ p hp j hj hq fz1_125_77 fz2_125_77
  · exact match_zero_fix ⟨126, by decide⟩ ⟨77, by decide⟩ p hp j hj hq fz1_126_77 fz2_126_77
  · exact match_zero_fix ⟨127, by decide⟩ ⟨77, by decide⟩ p hp j hj hq fz1_127_77 fz2_127_77
  · exact match_zero_fix ⟨128, by decide⟩ ⟨77, by decide⟩ p hp j hj hq fz1_128_77 fz2_128_77
  · exact match_zero_fix ⟨129, by decide⟩ ⟨77, by decide⟩ p hp j hj hq fz1_129_77 fz2_129_77
  · exact match_zero_fix ⟨130, by decide⟩ ⟨77, by decide⟩ p hp j hj hq fz1_130_77 fz2_130_77
  · exact match_zero_fix ⟨131, by decide⟩ ⟨77, by decide⟩ p hp j hj hq fz1_131_77 fz2_131_77
  · exact match_zero_fix ⟨132, by decide⟩ ⟨77, by decide⟩ p hp j hj hq fz1_132_77 fz2_132_77
  · exact match_zero_fix ⟨133, by decide⟩ ⟨77, by decide⟩ p hp j hj hq fz1_133_77 fz2_133_77
  · exact match_zero_fix ⟨134, by decide⟩ ⟨77, by decide⟩ p hp j hj hq fz1_134_77 fz2_134_77
  · exact match_zero_fix ⟨135, by decide⟩ ⟨77, by decide⟩ p hp j hj hq fz1_135_77 fz2_135_77
  · exact match_zero_fix ⟨136, by decide⟩ ⟨77, by decide⟩ p hp j hj hq fz1_136_77 fz2_136_77
  · exact match_zero_fix ⟨137, by decide⟩ ⟨77, by decide⟩ p hp j hj hq fz1_137_77 fz2_137_77
  · exact match_zero_fix ⟨138, by decide⟩ ⟨77, by decide⟩ p hp j hj hq fz1_138_77 fz2_138_77
  · exact match_zero_fix ⟨139, by decide⟩ ⟨77, by decide⟩ p hp j hj hq fz1_139_77 fz2_139_77
  · exact match_zero_fix ⟨140, by decide⟩ ⟨77, by decide⟩ p hp j hj hq fz1_140_77 fz2_140_77
  · exact match_zero_fix ⟨141, by decide⟩ ⟨77, by decide⟩ p hp j hj hq fz1_141_77 fz2_141_77
  · exact match_zero_fix ⟨142, by decide⟩ ⟨77, by decide⟩ p hp j hj hq fz1_142_77 fz2_142_77
  · exact match_zero_fix ⟨143, by decide⟩ ⟨77, by decide⟩ p hp j hj hq fz1_143_77 fz2_143_77
  · exact match_zero_fix ⟨144, by decide⟩ ⟨77, by decide⟩ p hp j hj hq fz1_144_77 fz2_144_77
  · exact match_zero_fix ⟨145, by decide⟩ ⟨77, by decide⟩ p hp j hj hq fz1_145_77 fz2_145_77
  · exact match_zero_fix ⟨146, by decide⟩ ⟨77, by decide⟩ p hp j hj hq fz1_146_77 fz2_146_77
  · exact pair_147_77 p hp hrep j hj hq

theorem master_78 (p : Nat) (hp : p < (Q2.transData.getD 78 []).length)
    (hrep : (Q2.cosetIsRep.getD 78 []).getD p false = true)
    (rK : Fin 148) (j : Nat) (hj : j < (repChars.getD rK.val []).length)
    (hq : (normIsRep.getD rK.val []).getD j false = true) :
    species (Q2.reps (⟨78, by decide⟩ : Fin 148)) (colE2 ⟨78, by decide⟩ p hp)
        (rowE2 rK j hj hq)
      = species (reps (⟨78, by decide⟩ : Fin 148))
        (colE1 ⟨78, by decide⟩ p (transLenTr ⟨78, by decide⟩ p hp)) (rowE1 rK j hj) := by
  rcases rK with ⟨nK, hnK⟩; interval_cases nK
  · exact match_zero_len ⟨0, by decide⟩ ⟨78, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨1, by decide⟩ ⟨78, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨2, by decide⟩ ⟨78, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨3, by decide⟩ ⟨78, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨4, by decide⟩ ⟨78, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨5, by decide⟩ ⟨78, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨6, by decide⟩ ⟨78, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨7, by decide⟩ ⟨78, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨8, by decide⟩ ⟨78, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨9, by decide⟩ ⟨78, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨10, by decide⟩ ⟨78, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨11, by decide⟩ ⟨78, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨12, by decide⟩ ⟨78, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨13, by decide⟩ ⟨78, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨14, by decide⟩ ⟨78, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨15, by decide⟩ ⟨78, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨16, by decide⟩ ⟨78, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨17, by decide⟩ ⟨78, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨18, by decide⟩ ⟨78, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨19, by decide⟩ ⟨78, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨20, by decide⟩ ⟨78, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨21, by decide⟩ ⟨78, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨22, by decide⟩ ⟨78, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨23, by decide⟩ ⟨78, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨24, by decide⟩ ⟨78, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨25, by decide⟩ ⟨78, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨26, by decide⟩ ⟨78, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨27, by decide⟩ ⟨78, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨28, by decide⟩ ⟨78, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨29, by decide⟩ ⟨78, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨30, by decide⟩ ⟨78, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨31, by decide⟩ ⟨78, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨32, by decide⟩ ⟨78, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨33, by decide⟩ ⟨78, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨34, by decide⟩ ⟨78, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨35, by decide⟩ ⟨78, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨36, by decide⟩ ⟨78, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨37, by decide⟩ ⟨78, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨38, by decide⟩ ⟨78, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨39, by decide⟩ ⟨78, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨40, by decide⟩ ⟨78, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨41, by decide⟩ ⟨78, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨42, by decide⟩ ⟨78, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨43, by decide⟩ ⟨78, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨44, by decide⟩ ⟨78, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨45, by decide⟩ ⟨78, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨46, by decide⟩ ⟨78, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨47, by decide⟩ ⟨78, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨48, by decide⟩ ⟨78, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨49, by decide⟩ ⟨78, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨50, by decide⟩ ⟨78, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨51, by decide⟩ ⟨78, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨52, by decide⟩ ⟨78, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨53, by decide⟩ ⟨78, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨54, by decide⟩ ⟨78, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_fix ⟨55, by decide⟩ ⟨78, by decide⟩ p hp j hj hq fz1_55_78 fz2_55_78
  · exact match_zero_fix ⟨56, by decide⟩ ⟨78, by decide⟩ p hp j hj hq fz1_56_78 fz2_56_78
  · exact match_zero_fix ⟨57, by decide⟩ ⟨78, by decide⟩ p hp j hj hq fz1_57_78 fz2_57_78
  · exact match_zero_fix ⟨58, by decide⟩ ⟨78, by decide⟩ p hp j hj hq fz1_58_78 fz2_58_78
  · exact match_zero_fix ⟨59, by decide⟩ ⟨78, by decide⟩ p hp j hj hq fz1_59_78 fz2_59_78
  · exact match_zero_fix ⟨60, by decide⟩ ⟨78, by decide⟩ p hp j hj hq fz1_60_78 fz2_60_78
  · exact match_zero_fix ⟨61, by decide⟩ ⟨78, by decide⟩ p hp j hj hq fz1_61_78 fz2_61_78
  · exact match_zero_fix ⟨62, by decide⟩ ⟨78, by decide⟩ p hp j hj hq fz1_62_78 fz2_62_78
  · exact match_zero_fix ⟨63, by decide⟩ ⟨78, by decide⟩ p hp j hj hq fz1_63_78 fz2_63_78
  · exact match_zero_fix ⟨64, by decide⟩ ⟨78, by decide⟩ p hp j hj hq fz1_64_78 fz2_64_78
  · exact match_zero_fix ⟨65, by decide⟩ ⟨78, by decide⟩ p hp j hj hq fz1_65_78 fz2_65_78
  · exact match_zero_fix ⟨66, by decide⟩ ⟨78, by decide⟩ p hp j hj hq fz1_66_78 fz2_66_78
  · exact match_zero_fix ⟨67, by decide⟩ ⟨78, by decide⟩ p hp j hj hq fz1_67_78 fz2_67_78
  · exact match_zero_fix ⟨68, by decide⟩ ⟨78, by decide⟩ p hp j hj hq fz1_68_78 fz2_68_78
  · exact match_zero_fix ⟨69, by decide⟩ ⟨78, by decide⟩ p hp j hj hq fz1_69_78 fz2_69_78
  · exact match_zero_fix ⟨70, by decide⟩ ⟨78, by decide⟩ p hp j hj hq fz1_70_78 fz2_70_78
  · exact match_zero_fix ⟨71, by decide⟩ ⟨78, by decide⟩ p hp j hj hq fz1_71_78 fz2_71_78
  · exact match_zero_fix ⟨72, by decide⟩ ⟨78, by decide⟩ p hp j hj hq fz1_72_78 fz2_72_78
  · exact match_zero_fix ⟨73, by decide⟩ ⟨78, by decide⟩ p hp j hj hq fz1_73_78 fz2_73_78
  · exact match_zero_fix ⟨74, by decide⟩ ⟨78, by decide⟩ p hp j hj hq fz1_74_78 fz2_74_78
  · exact match_zero_fix ⟨75, by decide⟩ ⟨78, by decide⟩ p hp j hj hq fz1_75_78 fz2_75_78
  · exact match_zero_fix ⟨76, by decide⟩ ⟨78, by decide⟩ p hp j hj hq fz1_76_78 fz2_76_78
  · exact match_zero_fix ⟨77, by decide⟩ ⟨78, by decide⟩ p hp j hj hq fz1_77_78 fz2_77_78
  · exact pair_78_78 p hp hrep j hj hq
  · exact match_zero_fix ⟨79, by decide⟩ ⟨78, by decide⟩ p hp j hj hq fz1_79_78 fz2_79_78
  · exact match_zero_fix ⟨80, by decide⟩ ⟨78, by decide⟩ p hp j hj hq fz1_80_78 fz2_80_78
  · exact match_zero_fix ⟨81, by decide⟩ ⟨78, by decide⟩ p hp j hj hq fz1_81_78 fz2_81_78
  · exact match_zero_fix ⟨82, by decide⟩ ⟨78, by decide⟩ p hp j hj hq fz1_82_78 fz2_82_78
  · exact match_zero_fix ⟨83, by decide⟩ ⟨78, by decide⟩ p hp j hj hq fz1_83_78 fz2_83_78
  · exact match_zero_fix ⟨84, by decide⟩ ⟨78, by decide⟩ p hp j hj hq fz1_84_78 fz2_84_78
  · exact match_zero_fix ⟨85, by decide⟩ ⟨78, by decide⟩ p hp j hj hq fz1_85_78 fz2_85_78
  · exact match_zero_fix ⟨86, by decide⟩ ⟨78, by decide⟩ p hp j hj hq fz1_86_78 fz2_86_78
  · exact match_zero_fix ⟨87, by decide⟩ ⟨78, by decide⟩ p hp j hj hq fz1_87_78 fz2_87_78
  · exact match_zero_fix ⟨88, by decide⟩ ⟨78, by decide⟩ p hp j hj hq fz1_88_78 fz2_88_78
  · exact match_zero_fix ⟨89, by decide⟩ ⟨78, by decide⟩ p hp j hj hq fz1_89_78 fz2_89_78
  · exact match_zero_fix ⟨90, by decide⟩ ⟨78, by decide⟩ p hp j hj hq fz1_90_78 fz2_90_78
  · exact match_zero_fix ⟨91, by decide⟩ ⟨78, by decide⟩ p hp j hj hq fz1_91_78 fz2_91_78
  · exact match_zero_fix ⟨92, by decide⟩ ⟨78, by decide⟩ p hp j hj hq fz1_92_78 fz2_92_78
  · exact match_zero_fix ⟨93, by decide⟩ ⟨78, by decide⟩ p hp j hj hq fz1_93_78 fz2_93_78
  · exact match_zero_fix ⟨94, by decide⟩ ⟨78, by decide⟩ p hp j hj hq fz1_94_78 fz2_94_78
  · exact match_zero_fix ⟨95, by decide⟩ ⟨78, by decide⟩ p hp j hj hq fz1_95_78 fz2_95_78
  · exact match_zero_fix ⟨96, by decide⟩ ⟨78, by decide⟩ p hp j hj hq fz1_96_78 fz2_96_78
  · exact match_zero_fix ⟨97, by decide⟩ ⟨78, by decide⟩ p hp j hj hq fz1_97_78 fz2_97_78
  · exact match_zero_fix ⟨98, by decide⟩ ⟨78, by decide⟩ p hp j hj hq fz1_98_78 fz2_98_78
  · exact match_zero_fix ⟨99, by decide⟩ ⟨78, by decide⟩ p hp j hj hq fz1_99_78 fz2_99_78
  · exact match_zero_fix ⟨100, by decide⟩ ⟨78, by decide⟩ p hp j hj hq fz1_100_78 fz2_100_78
  · exact match_zero_fix ⟨101, by decide⟩ ⟨78, by decide⟩ p hp j hj hq fz1_101_78 fz2_101_78
  · exact match_zero_fix ⟨102, by decide⟩ ⟨78, by decide⟩ p hp j hj hq fz1_102_78 fz2_102_78
  · exact match_zero_fix ⟨103, by decide⟩ ⟨78, by decide⟩ p hp j hj hq fz1_103_78 fz2_103_78
  · exact match_zero_fix ⟨104, by decide⟩ ⟨78, by decide⟩ p hp j hj hq fz1_104_78 fz2_104_78
  · exact match_zero_fix ⟨105, by decide⟩ ⟨78, by decide⟩ p hp j hj hq fz1_105_78 fz2_105_78
  · exact match_zero_fix ⟨106, by decide⟩ ⟨78, by decide⟩ p hp j hj hq fz1_106_78 fz2_106_78
  · exact match_zero_fix ⟨107, by decide⟩ ⟨78, by decide⟩ p hp j hj hq fz1_107_78 fz2_107_78
  · exact match_zero_fix ⟨108, by decide⟩ ⟨78, by decide⟩ p hp j hj hq fz1_108_78 fz2_108_78
  · exact match_zero_fix ⟨109, by decide⟩ ⟨78, by decide⟩ p hp j hj hq fz1_109_78 fz2_109_78
  · exact match_zero_fix ⟨110, by decide⟩ ⟨78, by decide⟩ p hp j hj hq fz1_110_78 fz2_110_78
  · exact match_zero_fix ⟨111, by decide⟩ ⟨78, by decide⟩ p hp j hj hq fz1_111_78 fz2_111_78
  · exact match_zero_fix ⟨112, by decide⟩ ⟨78, by decide⟩ p hp j hj hq fz1_112_78 fz2_112_78
  · exact match_zero_fix ⟨113, by decide⟩ ⟨78, by decide⟩ p hp j hj hq fz1_113_78 fz2_113_78
  · exact match_zero_fix ⟨114, by decide⟩ ⟨78, by decide⟩ p hp j hj hq fz1_114_78 fz2_114_78
  · exact match_zero_fix ⟨115, by decide⟩ ⟨78, by decide⟩ p hp j hj hq fz1_115_78 fz2_115_78
  · exact match_zero_fix ⟨116, by decide⟩ ⟨78, by decide⟩ p hp j hj hq fz1_116_78 fz2_116_78
  · exact match_zero_fix ⟨117, by decide⟩ ⟨78, by decide⟩ p hp j hj hq fz1_117_78 fz2_117_78
  · exact match_zero_fix ⟨118, by decide⟩ ⟨78, by decide⟩ p hp j hj hq fz1_118_78 fz2_118_78
  · exact match_zero_fix ⟨119, by decide⟩ ⟨78, by decide⟩ p hp j hj hq fz1_119_78 fz2_119_78
  · exact pair_120_78 p hp hrep j hj hq
  · exact match_zero_fix ⟨121, by decide⟩ ⟨78, by decide⟩ p hp j hj hq fz1_121_78 fz2_121_78
  · exact match_zero_fix ⟨122, by decide⟩ ⟨78, by decide⟩ p hp j hj hq fz1_122_78 fz2_122_78
  · exact match_zero_fix ⟨123, by decide⟩ ⟨78, by decide⟩ p hp j hj hq fz1_123_78 fz2_123_78
  · exact match_zero_fix ⟨124, by decide⟩ ⟨78, by decide⟩ p hp j hj hq fz1_124_78 fz2_124_78
  · exact match_zero_fix ⟨125, by decide⟩ ⟨78, by decide⟩ p hp j hj hq fz1_125_78 fz2_125_78
  · exact match_zero_fix ⟨126, by decide⟩ ⟨78, by decide⟩ p hp j hj hq fz1_126_78 fz2_126_78
  · exact match_zero_fix ⟨127, by decide⟩ ⟨78, by decide⟩ p hp j hj hq fz1_127_78 fz2_127_78
  · exact match_zero_fix ⟨128, by decide⟩ ⟨78, by decide⟩ p hp j hj hq fz1_128_78 fz2_128_78
  · exact match_zero_fix ⟨129, by decide⟩ ⟨78, by decide⟩ p hp j hj hq fz1_129_78 fz2_129_78
  · exact match_zero_fix ⟨130, by decide⟩ ⟨78, by decide⟩ p hp j hj hq fz1_130_78 fz2_130_78
  · exact match_zero_fix ⟨131, by decide⟩ ⟨78, by decide⟩ p hp j hj hq fz1_131_78 fz2_131_78
  · exact match_zero_fix ⟨132, by decide⟩ ⟨78, by decide⟩ p hp j hj hq fz1_132_78 fz2_132_78
  · exact match_zero_fix ⟨133, by decide⟩ ⟨78, by decide⟩ p hp j hj hq fz1_133_78 fz2_133_78
  · exact match_zero_fix ⟨134, by decide⟩ ⟨78, by decide⟩ p hp j hj hq fz1_134_78 fz2_134_78
  · exact match_zero_fix ⟨135, by decide⟩ ⟨78, by decide⟩ p hp j hj hq fz1_135_78 fz2_135_78
  · exact match_zero_fix ⟨136, by decide⟩ ⟨78, by decide⟩ p hp j hj hq fz1_136_78 fz2_136_78
  · exact match_zero_fix ⟨137, by decide⟩ ⟨78, by decide⟩ p hp j hj hq fz1_137_78 fz2_137_78
  · exact match_zero_fix ⟨138, by decide⟩ ⟨78, by decide⟩ p hp j hj hq fz1_138_78 fz2_138_78
  · exact match_zero_fix ⟨139, by decide⟩ ⟨78, by decide⟩ p hp j hj hq fz1_139_78 fz2_139_78
  · exact match_zero_fix ⟨140, by decide⟩ ⟨78, by decide⟩ p hp j hj hq fz1_140_78 fz2_140_78
  · exact match_zero_fix ⟨141, by decide⟩ ⟨78, by decide⟩ p hp j hj hq fz1_141_78 fz2_141_78
  · exact match_zero_fix ⟨142, by decide⟩ ⟨78, by decide⟩ p hp j hj hq fz1_142_78 fz2_142_78
  · exact match_zero_fix ⟨143, by decide⟩ ⟨78, by decide⟩ p hp j hj hq fz1_143_78 fz2_143_78
  · exact match_zero_fix ⟨144, by decide⟩ ⟨78, by decide⟩ p hp j hj hq fz1_144_78 fz2_144_78
  · exact match_zero_fix ⟨145, by decide⟩ ⟨78, by decide⟩ p hp j hj hq fz1_145_78 fz2_145_78
  · exact match_zero_fix ⟨146, by decide⟩ ⟨78, by decide⟩ p hp j hj hq fz1_146_78 fz2_146_78
  · exact pair_147_78 p hp hrep j hj hq

theorem master_79 (p : Nat) (hp : p < (Q2.transData.getD 79 []).length)
    (hrep : (Q2.cosetIsRep.getD 79 []).getD p false = true)
    (rK : Fin 148) (j : Nat) (hj : j < (repChars.getD rK.val []).length)
    (hq : (normIsRep.getD rK.val []).getD j false = true) :
    species (Q2.reps (⟨79, by decide⟩ : Fin 148)) (colE2 ⟨79, by decide⟩ p hp)
        (rowE2 rK j hj hq)
      = species (reps (⟨79, by decide⟩ : Fin 148))
        (colE1 ⟨79, by decide⟩ p (transLenTr ⟨79, by decide⟩ p hp)) (rowE1 rK j hj) := by
  rcases rK with ⟨nK, hnK⟩; interval_cases nK
  · exact match_zero_len ⟨0, by decide⟩ ⟨79, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨1, by decide⟩ ⟨79, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨2, by decide⟩ ⟨79, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨3, by decide⟩ ⟨79, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨4, by decide⟩ ⟨79, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨5, by decide⟩ ⟨79, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨6, by decide⟩ ⟨79, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨7, by decide⟩ ⟨79, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨8, by decide⟩ ⟨79, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨9, by decide⟩ ⟨79, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨10, by decide⟩ ⟨79, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨11, by decide⟩ ⟨79, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨12, by decide⟩ ⟨79, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨13, by decide⟩ ⟨79, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨14, by decide⟩ ⟨79, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨15, by decide⟩ ⟨79, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨16, by decide⟩ ⟨79, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨17, by decide⟩ ⟨79, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨18, by decide⟩ ⟨79, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨19, by decide⟩ ⟨79, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨20, by decide⟩ ⟨79, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨21, by decide⟩ ⟨79, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨22, by decide⟩ ⟨79, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨23, by decide⟩ ⟨79, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨24, by decide⟩ ⟨79, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨25, by decide⟩ ⟨79, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨26, by decide⟩ ⟨79, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨27, by decide⟩ ⟨79, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨28, by decide⟩ ⟨79, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨29, by decide⟩ ⟨79, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨30, by decide⟩ ⟨79, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨31, by decide⟩ ⟨79, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨32, by decide⟩ ⟨79, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨33, by decide⟩ ⟨79, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨34, by decide⟩ ⟨79, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨35, by decide⟩ ⟨79, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨36, by decide⟩ ⟨79, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨37, by decide⟩ ⟨79, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨38, by decide⟩ ⟨79, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨39, by decide⟩ ⟨79, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨40, by decide⟩ ⟨79, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨41, by decide⟩ ⟨79, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨42, by decide⟩ ⟨79, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨43, by decide⟩ ⟨79, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨44, by decide⟩ ⟨79, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨45, by decide⟩ ⟨79, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨46, by decide⟩ ⟨79, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨47, by decide⟩ ⟨79, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨48, by decide⟩ ⟨79, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨49, by decide⟩ ⟨79, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨50, by decide⟩ ⟨79, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨51, by decide⟩ ⟨79, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨52, by decide⟩ ⟨79, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨53, by decide⟩ ⟨79, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨54, by decide⟩ ⟨79, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_fix ⟨55, by decide⟩ ⟨79, by decide⟩ p hp j hj hq fz1_55_79 fz2_55_79
  · exact match_zero_fix ⟨56, by decide⟩ ⟨79, by decide⟩ p hp j hj hq fz1_56_79 fz2_56_79
  · exact match_zero_fix ⟨57, by decide⟩ ⟨79, by decide⟩ p hp j hj hq fz1_57_79 fz2_57_79
  · exact match_zero_fix ⟨58, by decide⟩ ⟨79, by decide⟩ p hp j hj hq fz1_58_79 fz2_58_79
  · exact match_zero_fix ⟨59, by decide⟩ ⟨79, by decide⟩ p hp j hj hq fz1_59_79 fz2_59_79
  · exact match_zero_fix ⟨60, by decide⟩ ⟨79, by decide⟩ p hp j hj hq fz1_60_79 fz2_60_79
  · exact match_zero_fix ⟨61, by decide⟩ ⟨79, by decide⟩ p hp j hj hq fz1_61_79 fz2_61_79
  · exact match_zero_fix ⟨62, by decide⟩ ⟨79, by decide⟩ p hp j hj hq fz1_62_79 fz2_62_79
  · exact match_zero_fix ⟨63, by decide⟩ ⟨79, by decide⟩ p hp j hj hq fz1_63_79 fz2_63_79
  · exact match_zero_fix ⟨64, by decide⟩ ⟨79, by decide⟩ p hp j hj hq fz1_64_79 fz2_64_79
  · exact match_zero_fix ⟨65, by decide⟩ ⟨79, by decide⟩ p hp j hj hq fz1_65_79 fz2_65_79
  · exact match_zero_fix ⟨66, by decide⟩ ⟨79, by decide⟩ p hp j hj hq fz1_66_79 fz2_66_79
  · exact match_zero_fix ⟨67, by decide⟩ ⟨79, by decide⟩ p hp j hj hq fz1_67_79 fz2_67_79
  · exact match_zero_fix ⟨68, by decide⟩ ⟨79, by decide⟩ p hp j hj hq fz1_68_79 fz2_68_79
  · exact match_zero_fix ⟨69, by decide⟩ ⟨79, by decide⟩ p hp j hj hq fz1_69_79 fz2_69_79
  · exact match_zero_fix ⟨70, by decide⟩ ⟨79, by decide⟩ p hp j hj hq fz1_70_79 fz2_70_79
  · exact match_zero_fix ⟨71, by decide⟩ ⟨79, by decide⟩ p hp j hj hq fz1_71_79 fz2_71_79
  · exact match_zero_fix ⟨72, by decide⟩ ⟨79, by decide⟩ p hp j hj hq fz1_72_79 fz2_72_79
  · exact match_zero_fix ⟨73, by decide⟩ ⟨79, by decide⟩ p hp j hj hq fz1_73_79 fz2_73_79
  · exact match_zero_fix ⟨74, by decide⟩ ⟨79, by decide⟩ p hp j hj hq fz1_74_79 fz2_74_79
  · exact match_zero_fix ⟨75, by decide⟩ ⟨79, by decide⟩ p hp j hj hq fz1_75_79 fz2_75_79
  · exact match_zero_fix ⟨76, by decide⟩ ⟨79, by decide⟩ p hp j hj hq fz1_76_79 fz2_76_79
  · exact match_zero_fix ⟨77, by decide⟩ ⟨79, by decide⟩ p hp j hj hq fz1_77_79 fz2_77_79
  · exact match_zero_fix ⟨78, by decide⟩ ⟨79, by decide⟩ p hp j hj hq fz1_78_79 fz2_78_79
  · exact pair_79_79 p hp hrep j hj hq
  · exact match_zero_fix ⟨80, by decide⟩ ⟨79, by decide⟩ p hp j hj hq fz1_80_79 fz2_80_79
  · exact match_zero_fix ⟨81, by decide⟩ ⟨79, by decide⟩ p hp j hj hq fz1_81_79 fz2_81_79
  · exact match_zero_fix ⟨82, by decide⟩ ⟨79, by decide⟩ p hp j hj hq fz1_82_79 fz2_82_79
  · exact match_zero_fix ⟨83, by decide⟩ ⟨79, by decide⟩ p hp j hj hq fz1_83_79 fz2_83_79
  · exact match_zero_fix ⟨84, by decide⟩ ⟨79, by decide⟩ p hp j hj hq fz1_84_79 fz2_84_79
  · exact match_zero_fix ⟨85, by decide⟩ ⟨79, by decide⟩ p hp j hj hq fz1_85_79 fz2_85_79
  · exact match_zero_fix ⟨86, by decide⟩ ⟨79, by decide⟩ p hp j hj hq fz1_86_79 fz2_86_79
  · exact match_zero_fix ⟨87, by decide⟩ ⟨79, by decide⟩ p hp j hj hq fz1_87_79 fz2_87_79
  · exact match_zero_fix ⟨88, by decide⟩ ⟨79, by decide⟩ p hp j hj hq fz1_88_79 fz2_88_79
  · exact match_zero_fix ⟨89, by decide⟩ ⟨79, by decide⟩ p hp j hj hq fz1_89_79 fz2_89_79
  · exact match_zero_fix ⟨90, by decide⟩ ⟨79, by decide⟩ p hp j hj hq fz1_90_79 fz2_90_79
  · exact match_zero_fix ⟨91, by decide⟩ ⟨79, by decide⟩ p hp j hj hq fz1_91_79 fz2_91_79
  · exact match_zero_fix ⟨92, by decide⟩ ⟨79, by decide⟩ p hp j hj hq fz1_92_79 fz2_92_79
  · exact match_zero_fix ⟨93, by decide⟩ ⟨79, by decide⟩ p hp j hj hq fz1_93_79 fz2_93_79
  · exact match_zero_fix ⟨94, by decide⟩ ⟨79, by decide⟩ p hp j hj hq fz1_94_79 fz2_94_79
  · exact match_zero_fix ⟨95, by decide⟩ ⟨79, by decide⟩ p hp j hj hq fz1_95_79 fz2_95_79
  · exact match_zero_fix ⟨96, by decide⟩ ⟨79, by decide⟩ p hp j hj hq fz1_96_79 fz2_96_79
  · exact match_zero_fix ⟨97, by decide⟩ ⟨79, by decide⟩ p hp j hj hq fz1_97_79 fz2_97_79
  · exact match_zero_fix ⟨98, by decide⟩ ⟨79, by decide⟩ p hp j hj hq fz1_98_79 fz2_98_79
  · exact match_zero_fix ⟨99, by decide⟩ ⟨79, by decide⟩ p hp j hj hq fz1_99_79 fz2_99_79
  · exact match_zero_fix ⟨100, by decide⟩ ⟨79, by decide⟩ p hp j hj hq fz1_100_79 fz2_100_79
  · exact match_zero_fix ⟨101, by decide⟩ ⟨79, by decide⟩ p hp j hj hq fz1_101_79 fz2_101_79
  · exact match_zero_fix ⟨102, by decide⟩ ⟨79, by decide⟩ p hp j hj hq fz1_102_79 fz2_102_79
  · exact match_zero_fix ⟨103, by decide⟩ ⟨79, by decide⟩ p hp j hj hq fz1_103_79 fz2_103_79
  · exact match_zero_fix ⟨104, by decide⟩ ⟨79, by decide⟩ p hp j hj hq fz1_104_79 fz2_104_79
  · exact match_zero_fix ⟨105, by decide⟩ ⟨79, by decide⟩ p hp j hj hq fz1_105_79 fz2_105_79
  · exact match_zero_fix ⟨106, by decide⟩ ⟨79, by decide⟩ p hp j hj hq fz1_106_79 fz2_106_79
  · exact match_zero_fix ⟨107, by decide⟩ ⟨79, by decide⟩ p hp j hj hq fz1_107_79 fz2_107_79
  · exact match_zero_fix ⟨108, by decide⟩ ⟨79, by decide⟩ p hp j hj hq fz1_108_79 fz2_108_79
  · exact match_zero_fix ⟨109, by decide⟩ ⟨79, by decide⟩ p hp j hj hq fz1_109_79 fz2_109_79
  · exact match_zero_fix ⟨110, by decide⟩ ⟨79, by decide⟩ p hp j hj hq fz1_110_79 fz2_110_79
  · exact match_zero_fix ⟨111, by decide⟩ ⟨79, by decide⟩ p hp j hj hq fz1_111_79 fz2_111_79
  · exact match_zero_fix ⟨112, by decide⟩ ⟨79, by decide⟩ p hp j hj hq fz1_112_79 fz2_112_79
  · exact match_zero_fix ⟨113, by decide⟩ ⟨79, by decide⟩ p hp j hj hq fz1_113_79 fz2_113_79
  · exact match_zero_fix ⟨114, by decide⟩ ⟨79, by decide⟩ p hp j hj hq fz1_114_79 fz2_114_79
  · exact match_zero_fix ⟨115, by decide⟩ ⟨79, by decide⟩ p hp j hj hq fz1_115_79 fz2_115_79
  · exact match_zero_fix ⟨116, by decide⟩ ⟨79, by decide⟩ p hp j hj hq fz1_116_79 fz2_116_79
  · exact match_zero_fix ⟨117, by decide⟩ ⟨79, by decide⟩ p hp j hj hq fz1_117_79 fz2_117_79
  · exact match_zero_fix ⟨118, by decide⟩ ⟨79, by decide⟩ p hp j hj hq fz1_118_79 fz2_118_79
  · exact match_zero_fix ⟨119, by decide⟩ ⟨79, by decide⟩ p hp j hj hq fz1_119_79 fz2_119_79
  · exact pair_120_79 p hp hrep j hj hq
  · exact match_zero_fix ⟨121, by decide⟩ ⟨79, by decide⟩ p hp j hj hq fz1_121_79 fz2_121_79
  · exact match_zero_fix ⟨122, by decide⟩ ⟨79, by decide⟩ p hp j hj hq fz1_122_79 fz2_122_79
  · exact match_zero_fix ⟨123, by decide⟩ ⟨79, by decide⟩ p hp j hj hq fz1_123_79 fz2_123_79
  · exact match_zero_fix ⟨124, by decide⟩ ⟨79, by decide⟩ p hp j hj hq fz1_124_79 fz2_124_79
  · exact match_zero_fix ⟨125, by decide⟩ ⟨79, by decide⟩ p hp j hj hq fz1_125_79 fz2_125_79
  · exact match_zero_fix ⟨126, by decide⟩ ⟨79, by decide⟩ p hp j hj hq fz1_126_79 fz2_126_79
  · exact match_zero_fix ⟨127, by decide⟩ ⟨79, by decide⟩ p hp j hj hq fz1_127_79 fz2_127_79
  · exact match_zero_fix ⟨128, by decide⟩ ⟨79, by decide⟩ p hp j hj hq fz1_128_79 fz2_128_79
  · exact match_zero_fix ⟨129, by decide⟩ ⟨79, by decide⟩ p hp j hj hq fz1_129_79 fz2_129_79
  · exact match_zero_fix ⟨130, by decide⟩ ⟨79, by decide⟩ p hp j hj hq fz1_130_79 fz2_130_79
  · exact match_zero_fix ⟨131, by decide⟩ ⟨79, by decide⟩ p hp j hj hq fz1_131_79 fz2_131_79
  · exact match_zero_fix ⟨132, by decide⟩ ⟨79, by decide⟩ p hp j hj hq fz1_132_79 fz2_132_79
  · exact match_zero_fix ⟨133, by decide⟩ ⟨79, by decide⟩ p hp j hj hq fz1_133_79 fz2_133_79
  · exact match_zero_fix ⟨134, by decide⟩ ⟨79, by decide⟩ p hp j hj hq fz1_134_79 fz2_134_79
  · exact match_zero_fix ⟨135, by decide⟩ ⟨79, by decide⟩ p hp j hj hq fz1_135_79 fz2_135_79
  · exact match_zero_fix ⟨136, by decide⟩ ⟨79, by decide⟩ p hp j hj hq fz1_136_79 fz2_136_79
  · exact match_zero_fix ⟨137, by decide⟩ ⟨79, by decide⟩ p hp j hj hq fz1_137_79 fz2_137_79
  · exact match_zero_fix ⟨138, by decide⟩ ⟨79, by decide⟩ p hp j hj hq fz1_138_79 fz2_138_79
  · exact match_zero_fix ⟨139, by decide⟩ ⟨79, by decide⟩ p hp j hj hq fz1_139_79 fz2_139_79
  · exact match_zero_fix ⟨140, by decide⟩ ⟨79, by decide⟩ p hp j hj hq fz1_140_79 fz2_140_79
  · exact match_zero_fix ⟨141, by decide⟩ ⟨79, by decide⟩ p hp j hj hq fz1_141_79 fz2_141_79
  · exact match_zero_fix ⟨142, by decide⟩ ⟨79, by decide⟩ p hp j hj hq fz1_142_79 fz2_142_79
  · exact match_zero_fix ⟨143, by decide⟩ ⟨79, by decide⟩ p hp j hj hq fz1_143_79 fz2_143_79
  · exact match_zero_fix ⟨144, by decide⟩ ⟨79, by decide⟩ p hp j hj hq fz1_144_79 fz2_144_79
  · exact match_zero_fix ⟨145, by decide⟩ ⟨79, by decide⟩ p hp j hj hq fz1_145_79 fz2_145_79
  · exact match_zero_fix ⟨146, by decide⟩ ⟨79, by decide⟩ p hp j hj hq fz1_146_79 fz2_146_79
  · exact pair_147_79 p hp hrep j hj hq

end LeanDring.P5Presentation
