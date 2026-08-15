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
import LeanDring.P5.Data.MatchPair.C004
import LeanDring.P5.Data.MatchPair.C006
import LeanDring.P5.Data.MatchPair.C007
import LeanDring.P5.Data.MatchPair.C008
import LeanDring.P5.Data.MatchPair.C009
import LeanDring.P5.Data.MatchPair.C010

/-! # Stage-5 per-column-class master theorems, chunk 10 (auto-emitted).  -/

namespace LeanDring.P5Presentation

open MulAction Finset LeanDring.DRing LeanDring.MonGSet

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.style.longLine false

theorem master_80 (p : Nat) (hp : p < (Q2.transData.getD 80 []).length)
    (hrep : (Q2.cosetIsRep.getD 80 []).getD p false = true)
    (rK : Fin 148) (j : Nat) (hj : j < (repChars.getD rK.val []).length)
    (hq : (normIsRep.getD rK.val []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ p hp)
        (rowE2 rK j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ p (transLenTr ⟨80, by decide⟩ p hp)) (rowE1 rK j hj) := by
  rcases rK with ⟨nK, hnK⟩; interval_cases nK
  · exact match_zero_len ⟨0, by decide⟩ ⟨80, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨1, by decide⟩ ⟨80, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨2, by decide⟩ ⟨80, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨3, by decide⟩ ⟨80, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨4, by decide⟩ ⟨80, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨5, by decide⟩ ⟨80, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨6, by decide⟩ ⟨80, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨7, by decide⟩ ⟨80, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨8, by decide⟩ ⟨80, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨9, by decide⟩ ⟨80, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨10, by decide⟩ ⟨80, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨11, by decide⟩ ⟨80, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨12, by decide⟩ ⟨80, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨13, by decide⟩ ⟨80, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨14, by decide⟩ ⟨80, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨15, by decide⟩ ⟨80, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨16, by decide⟩ ⟨80, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨17, by decide⟩ ⟨80, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨18, by decide⟩ ⟨80, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨19, by decide⟩ ⟨80, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨20, by decide⟩ ⟨80, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨21, by decide⟩ ⟨80, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨22, by decide⟩ ⟨80, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨23, by decide⟩ ⟨80, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨24, by decide⟩ ⟨80, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨25, by decide⟩ ⟨80, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨26, by decide⟩ ⟨80, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨27, by decide⟩ ⟨80, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨28, by decide⟩ ⟨80, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨29, by decide⟩ ⟨80, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨30, by decide⟩ ⟨80, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨31, by decide⟩ ⟨80, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨32, by decide⟩ ⟨80, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨33, by decide⟩ ⟨80, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨34, by decide⟩ ⟨80, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨35, by decide⟩ ⟨80, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨36, by decide⟩ ⟨80, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨37, by decide⟩ ⟨80, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨38, by decide⟩ ⟨80, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨39, by decide⟩ ⟨80, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨40, by decide⟩ ⟨80, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨41, by decide⟩ ⟨80, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨42, by decide⟩ ⟨80, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨43, by decide⟩ ⟨80, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨44, by decide⟩ ⟨80, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨45, by decide⟩ ⟨80, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨46, by decide⟩ ⟨80, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨47, by decide⟩ ⟨80, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨48, by decide⟩ ⟨80, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨49, by decide⟩ ⟨80, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨50, by decide⟩ ⟨80, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨51, by decide⟩ ⟨80, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨52, by decide⟩ ⟨80, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨53, by decide⟩ ⟨80, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨54, by decide⟩ ⟨80, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_fix ⟨55, by decide⟩ ⟨80, by decide⟩ p hp j hj hq fz1_55_80 fz2_55_80
  · exact match_zero_fix ⟨56, by decide⟩ ⟨80, by decide⟩ p hp j hj hq fz1_56_80 fz2_56_80
  · exact match_zero_fix ⟨57, by decide⟩ ⟨80, by decide⟩ p hp j hj hq fz1_57_80 fz2_57_80
  · exact match_zero_fix ⟨58, by decide⟩ ⟨80, by decide⟩ p hp j hj hq fz1_58_80 fz2_58_80
  · exact match_zero_fix ⟨59, by decide⟩ ⟨80, by decide⟩ p hp j hj hq fz1_59_80 fz2_59_80
  · exact match_zero_fix ⟨60, by decide⟩ ⟨80, by decide⟩ p hp j hj hq fz1_60_80 fz2_60_80
  · exact match_zero_fix ⟨61, by decide⟩ ⟨80, by decide⟩ p hp j hj hq fz1_61_80 fz2_61_80
  · exact match_zero_fix ⟨62, by decide⟩ ⟨80, by decide⟩ p hp j hj hq fz1_62_80 fz2_62_80
  · exact match_zero_fix ⟨63, by decide⟩ ⟨80, by decide⟩ p hp j hj hq fz1_63_80 fz2_63_80
  · exact match_zero_fix ⟨64, by decide⟩ ⟨80, by decide⟩ p hp j hj hq fz1_64_80 fz2_64_80
  · exact match_zero_fix ⟨65, by decide⟩ ⟨80, by decide⟩ p hp j hj hq fz1_65_80 fz2_65_80
  · exact match_zero_fix ⟨66, by decide⟩ ⟨80, by decide⟩ p hp j hj hq fz1_66_80 fz2_66_80
  · exact match_zero_fix ⟨67, by decide⟩ ⟨80, by decide⟩ p hp j hj hq fz1_67_80 fz2_67_80
  · exact match_zero_fix ⟨68, by decide⟩ ⟨80, by decide⟩ p hp j hj hq fz1_68_80 fz2_68_80
  · exact match_zero_fix ⟨69, by decide⟩ ⟨80, by decide⟩ p hp j hj hq fz1_69_80 fz2_69_80
  · exact match_zero_fix ⟨70, by decide⟩ ⟨80, by decide⟩ p hp j hj hq fz1_70_80 fz2_70_80
  · exact match_zero_fix ⟨71, by decide⟩ ⟨80, by decide⟩ p hp j hj hq fz1_71_80 fz2_71_80
  · exact match_zero_fix ⟨72, by decide⟩ ⟨80, by decide⟩ p hp j hj hq fz1_72_80 fz2_72_80
  · exact match_zero_fix ⟨73, by decide⟩ ⟨80, by decide⟩ p hp j hj hq fz1_73_80 fz2_73_80
  · exact match_zero_fix ⟨74, by decide⟩ ⟨80, by decide⟩ p hp j hj hq fz1_74_80 fz2_74_80
  · exact match_zero_fix ⟨75, by decide⟩ ⟨80, by decide⟩ p hp j hj hq fz1_75_80 fz2_75_80
  · exact match_zero_fix ⟨76, by decide⟩ ⟨80, by decide⟩ p hp j hj hq fz1_76_80 fz2_76_80
  · exact match_zero_fix ⟨77, by decide⟩ ⟨80, by decide⟩ p hp j hj hq fz1_77_80 fz2_77_80
  · exact match_zero_fix ⟨78, by decide⟩ ⟨80, by decide⟩ p hp j hj hq fz1_78_80 fz2_78_80
  · exact match_zero_fix ⟨79, by decide⟩ ⟨80, by decide⟩ p hp j hj hq fz1_79_80 fz2_79_80
  · exact pair_80_80 p hp hrep j hj hq
  · exact match_zero_fix ⟨81, by decide⟩ ⟨80, by decide⟩ p hp j hj hq fz1_81_80 fz2_81_80
  · exact match_zero_fix ⟨82, by decide⟩ ⟨80, by decide⟩ p hp j hj hq fz1_82_80 fz2_82_80
  · exact match_zero_fix ⟨83, by decide⟩ ⟨80, by decide⟩ p hp j hj hq fz1_83_80 fz2_83_80
  · exact match_zero_fix ⟨84, by decide⟩ ⟨80, by decide⟩ p hp j hj hq fz1_84_80 fz2_84_80
  · exact match_zero_fix ⟨85, by decide⟩ ⟨80, by decide⟩ p hp j hj hq fz1_85_80 fz2_85_80
  · exact match_zero_fix ⟨86, by decide⟩ ⟨80, by decide⟩ p hp j hj hq fz1_86_80 fz2_86_80
  · exact match_zero_fix ⟨87, by decide⟩ ⟨80, by decide⟩ p hp j hj hq fz1_87_80 fz2_87_80
  · exact match_zero_fix ⟨88, by decide⟩ ⟨80, by decide⟩ p hp j hj hq fz1_88_80 fz2_88_80
  · exact match_zero_fix ⟨89, by decide⟩ ⟨80, by decide⟩ p hp j hj hq fz1_89_80 fz2_89_80
  · exact match_zero_fix ⟨90, by decide⟩ ⟨80, by decide⟩ p hp j hj hq fz1_90_80 fz2_90_80
  · exact match_zero_fix ⟨91, by decide⟩ ⟨80, by decide⟩ p hp j hj hq fz1_91_80 fz2_91_80
  · exact match_zero_fix ⟨92, by decide⟩ ⟨80, by decide⟩ p hp j hj hq fz1_92_80 fz2_92_80
  · exact match_zero_fix ⟨93, by decide⟩ ⟨80, by decide⟩ p hp j hj hq fz1_93_80 fz2_93_80
  · exact match_zero_fix ⟨94, by decide⟩ ⟨80, by decide⟩ p hp j hj hq fz1_94_80 fz2_94_80
  · exact match_zero_fix ⟨95, by decide⟩ ⟨80, by decide⟩ p hp j hj hq fz1_95_80 fz2_95_80
  · exact match_zero_fix ⟨96, by decide⟩ ⟨80, by decide⟩ p hp j hj hq fz1_96_80 fz2_96_80
  · exact match_zero_fix ⟨97, by decide⟩ ⟨80, by decide⟩ p hp j hj hq fz1_97_80 fz2_97_80
  · exact match_zero_fix ⟨98, by decide⟩ ⟨80, by decide⟩ p hp j hj hq fz1_98_80 fz2_98_80
  · exact match_zero_fix ⟨99, by decide⟩ ⟨80, by decide⟩ p hp j hj hq fz1_99_80 fz2_99_80
  · exact match_zero_fix ⟨100, by decide⟩ ⟨80, by decide⟩ p hp j hj hq fz1_100_80 fz2_100_80
  · exact match_zero_fix ⟨101, by decide⟩ ⟨80, by decide⟩ p hp j hj hq fz1_101_80 fz2_101_80
  · exact match_zero_fix ⟨102, by decide⟩ ⟨80, by decide⟩ p hp j hj hq fz1_102_80 fz2_102_80
  · exact match_zero_fix ⟨103, by decide⟩ ⟨80, by decide⟩ p hp j hj hq fz1_103_80 fz2_103_80
  · exact match_zero_fix ⟨104, by decide⟩ ⟨80, by decide⟩ p hp j hj hq fz1_104_80 fz2_104_80
  · exact match_zero_fix ⟨105, by decide⟩ ⟨80, by decide⟩ p hp j hj hq fz1_105_80 fz2_105_80
  · exact match_zero_fix ⟨106, by decide⟩ ⟨80, by decide⟩ p hp j hj hq fz1_106_80 fz2_106_80
  · exact match_zero_fix ⟨107, by decide⟩ ⟨80, by decide⟩ p hp j hj hq fz1_107_80 fz2_107_80
  · exact match_zero_fix ⟨108, by decide⟩ ⟨80, by decide⟩ p hp j hj hq fz1_108_80 fz2_108_80
  · exact match_zero_fix ⟨109, by decide⟩ ⟨80, by decide⟩ p hp j hj hq fz1_109_80 fz2_109_80
  · exact match_zero_fix ⟨110, by decide⟩ ⟨80, by decide⟩ p hp j hj hq fz1_110_80 fz2_110_80
  · exact match_zero_fix ⟨111, by decide⟩ ⟨80, by decide⟩ p hp j hj hq fz1_111_80 fz2_111_80
  · exact match_zero_fix ⟨112, by decide⟩ ⟨80, by decide⟩ p hp j hj hq fz1_112_80 fz2_112_80
  · exact match_zero_fix ⟨113, by decide⟩ ⟨80, by decide⟩ p hp j hj hq fz1_113_80 fz2_113_80
  · exact match_zero_fix ⟨114, by decide⟩ ⟨80, by decide⟩ p hp j hj hq fz1_114_80 fz2_114_80
  · exact match_zero_fix ⟨115, by decide⟩ ⟨80, by decide⟩ p hp j hj hq fz1_115_80 fz2_115_80
  · exact pair_116_80 p hp hrep j hj hq
  · exact pair_117_80 p hp hrep j hj hq
  · exact pair_118_80 p hp hrep j hj hq
  · exact pair_119_80 p hp hrep j hj hq
  · exact pair_120_80 p hp hrep j hj hq
  · exact match_zero_fix ⟨121, by decide⟩ ⟨80, by decide⟩ p hp j hj hq fz1_121_80 fz2_121_80
  · exact match_zero_fix ⟨122, by decide⟩ ⟨80, by decide⟩ p hp j hj hq fz1_122_80 fz2_122_80
  · exact match_zero_fix ⟨123, by decide⟩ ⟨80, by decide⟩ p hp j hj hq fz1_123_80 fz2_123_80
  · exact match_zero_fix ⟨124, by decide⟩ ⟨80, by decide⟩ p hp j hj hq fz1_124_80 fz2_124_80
  · exact match_zero_fix ⟨125, by decide⟩ ⟨80, by decide⟩ p hp j hj hq fz1_125_80 fz2_125_80
  · exact match_zero_fix ⟨126, by decide⟩ ⟨80, by decide⟩ p hp j hj hq fz1_126_80 fz2_126_80
  · exact match_zero_fix ⟨127, by decide⟩ ⟨80, by decide⟩ p hp j hj hq fz1_127_80 fz2_127_80
  · exact match_zero_fix ⟨128, by decide⟩ ⟨80, by decide⟩ p hp j hj hq fz1_128_80 fz2_128_80
  · exact match_zero_fix ⟨129, by decide⟩ ⟨80, by decide⟩ p hp j hj hq fz1_129_80 fz2_129_80
  · exact match_zero_fix ⟨130, by decide⟩ ⟨80, by decide⟩ p hp j hj hq fz1_130_80 fz2_130_80
  · exact match_zero_fix ⟨131, by decide⟩ ⟨80, by decide⟩ p hp j hj hq fz1_131_80 fz2_131_80
  · exact match_zero_fix ⟨132, by decide⟩ ⟨80, by decide⟩ p hp j hj hq fz1_132_80 fz2_132_80
  · exact match_zero_fix ⟨133, by decide⟩ ⟨80, by decide⟩ p hp j hj hq fz1_133_80 fz2_133_80
  · exact match_zero_fix ⟨134, by decide⟩ ⟨80, by decide⟩ p hp j hj hq fz1_134_80 fz2_134_80
  · exact match_zero_fix ⟨135, by decide⟩ ⟨80, by decide⟩ p hp j hj hq fz1_135_80 fz2_135_80
  · exact match_zero_fix ⟨136, by decide⟩ ⟨80, by decide⟩ p hp j hj hq fz1_136_80 fz2_136_80
  · exact match_zero_fix ⟨137, by decide⟩ ⟨80, by decide⟩ p hp j hj hq fz1_137_80 fz2_137_80
  · exact match_zero_fix ⟨138, by decide⟩ ⟨80, by decide⟩ p hp j hj hq fz1_138_80 fz2_138_80
  · exact match_zero_fix ⟨139, by decide⟩ ⟨80, by decide⟩ p hp j hj hq fz1_139_80 fz2_139_80
  · exact match_zero_fix ⟨140, by decide⟩ ⟨80, by decide⟩ p hp j hj hq fz1_140_80 fz2_140_80
  · exact pair_141_80 p hp hrep j hj hq
  · exact match_zero_fix ⟨142, by decide⟩ ⟨80, by decide⟩ p hp j hj hq fz1_142_80 fz2_142_80
  · exact match_zero_fix ⟨143, by decide⟩ ⟨80, by decide⟩ p hp j hj hq fz1_143_80 fz2_143_80
  · exact match_zero_fix ⟨144, by decide⟩ ⟨80, by decide⟩ p hp j hj hq fz1_144_80 fz2_144_80
  · exact match_zero_fix ⟨145, by decide⟩ ⟨80, by decide⟩ p hp j hj hq fz1_145_80 fz2_145_80
  · exact match_zero_fix ⟨146, by decide⟩ ⟨80, by decide⟩ p hp j hj hq fz1_146_80 fz2_146_80
  · exact pair_147_80 p hp hrep j hj hq

theorem master_81 (p : Nat) (hp : p < (Q2.transData.getD 81 []).length)
    (hrep : (Q2.cosetIsRep.getD 81 []).getD p false = true)
    (rK : Fin 148) (j : Nat) (hj : j < (repChars.getD rK.val []).length)
    (hq : (normIsRep.getD rK.val []).getD j false = true) :
    species (Q2.reps (⟨81, by decide⟩ : Fin 148)) (colE2 ⟨81, by decide⟩ p hp)
        (rowE2 rK j hj hq)
      = species (reps (⟨81, by decide⟩ : Fin 148))
        (colE1 ⟨81, by decide⟩ p (transLenTr ⟨81, by decide⟩ p hp)) (rowE1 rK j hj) := by
  rcases rK with ⟨nK, hnK⟩; interval_cases nK
  · exact match_zero_len ⟨0, by decide⟩ ⟨81, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨1, by decide⟩ ⟨81, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨2, by decide⟩ ⟨81, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨3, by decide⟩ ⟨81, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨4, by decide⟩ ⟨81, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨5, by decide⟩ ⟨81, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨6, by decide⟩ ⟨81, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨7, by decide⟩ ⟨81, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨8, by decide⟩ ⟨81, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨9, by decide⟩ ⟨81, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨10, by decide⟩ ⟨81, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨11, by decide⟩ ⟨81, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨12, by decide⟩ ⟨81, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨13, by decide⟩ ⟨81, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨14, by decide⟩ ⟨81, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨15, by decide⟩ ⟨81, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨16, by decide⟩ ⟨81, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨17, by decide⟩ ⟨81, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨18, by decide⟩ ⟨81, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨19, by decide⟩ ⟨81, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨20, by decide⟩ ⟨81, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨21, by decide⟩ ⟨81, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨22, by decide⟩ ⟨81, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨23, by decide⟩ ⟨81, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨24, by decide⟩ ⟨81, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨25, by decide⟩ ⟨81, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨26, by decide⟩ ⟨81, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨27, by decide⟩ ⟨81, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨28, by decide⟩ ⟨81, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨29, by decide⟩ ⟨81, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨30, by decide⟩ ⟨81, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨31, by decide⟩ ⟨81, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨32, by decide⟩ ⟨81, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨33, by decide⟩ ⟨81, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨34, by decide⟩ ⟨81, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨35, by decide⟩ ⟨81, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨36, by decide⟩ ⟨81, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨37, by decide⟩ ⟨81, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨38, by decide⟩ ⟨81, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨39, by decide⟩ ⟨81, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨40, by decide⟩ ⟨81, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨41, by decide⟩ ⟨81, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨42, by decide⟩ ⟨81, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨43, by decide⟩ ⟨81, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨44, by decide⟩ ⟨81, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨45, by decide⟩ ⟨81, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨46, by decide⟩ ⟨81, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨47, by decide⟩ ⟨81, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨48, by decide⟩ ⟨81, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨49, by decide⟩ ⟨81, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨50, by decide⟩ ⟨81, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨51, by decide⟩ ⟨81, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨52, by decide⟩ ⟨81, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨53, by decide⟩ ⟨81, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨54, by decide⟩ ⟨81, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_fix ⟨55, by decide⟩ ⟨81, by decide⟩ p hp j hj hq fz1_55_81 fz2_55_81
  · exact match_zero_fix ⟨56, by decide⟩ ⟨81, by decide⟩ p hp j hj hq fz1_56_81 fz2_56_81
  · exact match_zero_fix ⟨57, by decide⟩ ⟨81, by decide⟩ p hp j hj hq fz1_57_81 fz2_57_81
  · exact match_zero_fix ⟨58, by decide⟩ ⟨81, by decide⟩ p hp j hj hq fz1_58_81 fz2_58_81
  · exact match_zero_fix ⟨59, by decide⟩ ⟨81, by decide⟩ p hp j hj hq fz1_59_81 fz2_59_81
  · exact match_zero_fix ⟨60, by decide⟩ ⟨81, by decide⟩ p hp j hj hq fz1_60_81 fz2_60_81
  · exact match_zero_fix ⟨61, by decide⟩ ⟨81, by decide⟩ p hp j hj hq fz1_61_81 fz2_61_81
  · exact match_zero_fix ⟨62, by decide⟩ ⟨81, by decide⟩ p hp j hj hq fz1_62_81 fz2_62_81
  · exact match_zero_fix ⟨63, by decide⟩ ⟨81, by decide⟩ p hp j hj hq fz1_63_81 fz2_63_81
  · exact match_zero_fix ⟨64, by decide⟩ ⟨81, by decide⟩ p hp j hj hq fz1_64_81 fz2_64_81
  · exact match_zero_fix ⟨65, by decide⟩ ⟨81, by decide⟩ p hp j hj hq fz1_65_81 fz2_65_81
  · exact match_zero_fix ⟨66, by decide⟩ ⟨81, by decide⟩ p hp j hj hq fz1_66_81 fz2_66_81
  · exact match_zero_fix ⟨67, by decide⟩ ⟨81, by decide⟩ p hp j hj hq fz1_67_81 fz2_67_81
  · exact match_zero_fix ⟨68, by decide⟩ ⟨81, by decide⟩ p hp j hj hq fz1_68_81 fz2_68_81
  · exact match_zero_fix ⟨69, by decide⟩ ⟨81, by decide⟩ p hp j hj hq fz1_69_81 fz2_69_81
  · exact match_zero_fix ⟨70, by decide⟩ ⟨81, by decide⟩ p hp j hj hq fz1_70_81 fz2_70_81
  · exact match_zero_fix ⟨71, by decide⟩ ⟨81, by decide⟩ p hp j hj hq fz1_71_81 fz2_71_81
  · exact match_zero_fix ⟨72, by decide⟩ ⟨81, by decide⟩ p hp j hj hq fz1_72_81 fz2_72_81
  · exact match_zero_fix ⟨73, by decide⟩ ⟨81, by decide⟩ p hp j hj hq fz1_73_81 fz2_73_81
  · exact match_zero_fix ⟨74, by decide⟩ ⟨81, by decide⟩ p hp j hj hq fz1_74_81 fz2_74_81
  · exact match_zero_fix ⟨75, by decide⟩ ⟨81, by decide⟩ p hp j hj hq fz1_75_81 fz2_75_81
  · exact match_zero_fix ⟨76, by decide⟩ ⟨81, by decide⟩ p hp j hj hq fz1_76_81 fz2_76_81
  · exact match_zero_fix ⟨77, by decide⟩ ⟨81, by decide⟩ p hp j hj hq fz1_77_81 fz2_77_81
  · exact match_zero_fix ⟨78, by decide⟩ ⟨81, by decide⟩ p hp j hj hq fz1_78_81 fz2_78_81
  · exact match_zero_fix ⟨79, by decide⟩ ⟨81, by decide⟩ p hp j hj hq fz1_79_81 fz2_79_81
  · exact match_zero_fix ⟨80, by decide⟩ ⟨81, by decide⟩ p hp j hj hq fz1_80_81 fz2_80_81
  · exact pair_81_81 p hp hrep j hj hq
  · exact match_zero_fix ⟨82, by decide⟩ ⟨81, by decide⟩ p hp j hj hq fz1_82_81 fz2_82_81
  · exact match_zero_fix ⟨83, by decide⟩ ⟨81, by decide⟩ p hp j hj hq fz1_83_81 fz2_83_81
  · exact match_zero_fix ⟨84, by decide⟩ ⟨81, by decide⟩ p hp j hj hq fz1_84_81 fz2_84_81
  · exact match_zero_fix ⟨85, by decide⟩ ⟨81, by decide⟩ p hp j hj hq fz1_85_81 fz2_85_81
  · exact match_zero_fix ⟨86, by decide⟩ ⟨81, by decide⟩ p hp j hj hq fz1_86_81 fz2_86_81
  · exact match_zero_fix ⟨87, by decide⟩ ⟨81, by decide⟩ p hp j hj hq fz1_87_81 fz2_87_81
  · exact match_zero_fix ⟨88, by decide⟩ ⟨81, by decide⟩ p hp j hj hq fz1_88_81 fz2_88_81
  · exact match_zero_fix ⟨89, by decide⟩ ⟨81, by decide⟩ p hp j hj hq fz1_89_81 fz2_89_81
  · exact match_zero_fix ⟨90, by decide⟩ ⟨81, by decide⟩ p hp j hj hq fz1_90_81 fz2_90_81
  · exact match_zero_fix ⟨91, by decide⟩ ⟨81, by decide⟩ p hp j hj hq fz1_91_81 fz2_91_81
  · exact match_zero_fix ⟨92, by decide⟩ ⟨81, by decide⟩ p hp j hj hq fz1_92_81 fz2_92_81
  · exact match_zero_fix ⟨93, by decide⟩ ⟨81, by decide⟩ p hp j hj hq fz1_93_81 fz2_93_81
  · exact match_zero_fix ⟨94, by decide⟩ ⟨81, by decide⟩ p hp j hj hq fz1_94_81 fz2_94_81
  · exact match_zero_fix ⟨95, by decide⟩ ⟨81, by decide⟩ p hp j hj hq fz1_95_81 fz2_95_81
  · exact match_zero_fix ⟨96, by decide⟩ ⟨81, by decide⟩ p hp j hj hq fz1_96_81 fz2_96_81
  · exact match_zero_fix ⟨97, by decide⟩ ⟨81, by decide⟩ p hp j hj hq fz1_97_81 fz2_97_81
  · exact match_zero_fix ⟨98, by decide⟩ ⟨81, by decide⟩ p hp j hj hq fz1_98_81 fz2_98_81
  · exact match_zero_fix ⟨99, by decide⟩ ⟨81, by decide⟩ p hp j hj hq fz1_99_81 fz2_99_81
  · exact match_zero_fix ⟨100, by decide⟩ ⟨81, by decide⟩ p hp j hj hq fz1_100_81 fz2_100_81
  · exact match_zero_fix ⟨101, by decide⟩ ⟨81, by decide⟩ p hp j hj hq fz1_101_81 fz2_101_81
  · exact match_zero_fix ⟨102, by decide⟩ ⟨81, by decide⟩ p hp j hj hq fz1_102_81 fz2_102_81
  · exact match_zero_fix ⟨103, by decide⟩ ⟨81, by decide⟩ p hp j hj hq fz1_103_81 fz2_103_81
  · exact match_zero_fix ⟨104, by decide⟩ ⟨81, by decide⟩ p hp j hj hq fz1_104_81 fz2_104_81
  · exact match_zero_fix ⟨105, by decide⟩ ⟨81, by decide⟩ p hp j hj hq fz1_105_81 fz2_105_81
  · exact match_zero_fix ⟨106, by decide⟩ ⟨81, by decide⟩ p hp j hj hq fz1_106_81 fz2_106_81
  · exact match_zero_fix ⟨107, by decide⟩ ⟨81, by decide⟩ p hp j hj hq fz1_107_81 fz2_107_81
  · exact match_zero_fix ⟨108, by decide⟩ ⟨81, by decide⟩ p hp j hj hq fz1_108_81 fz2_108_81
  · exact match_zero_fix ⟨109, by decide⟩ ⟨81, by decide⟩ p hp j hj hq fz1_109_81 fz2_109_81
  · exact match_zero_fix ⟨110, by decide⟩ ⟨81, by decide⟩ p hp j hj hq fz1_110_81 fz2_110_81
  · exact match_zero_fix ⟨111, by decide⟩ ⟨81, by decide⟩ p hp j hj hq fz1_111_81 fz2_111_81
  · exact match_zero_fix ⟨112, by decide⟩ ⟨81, by decide⟩ p hp j hj hq fz1_112_81 fz2_112_81
  · exact match_zero_fix ⟨113, by decide⟩ ⟨81, by decide⟩ p hp j hj hq fz1_113_81 fz2_113_81
  · exact match_zero_fix ⟨114, by decide⟩ ⟨81, by decide⟩ p hp j hj hq fz1_114_81 fz2_114_81
  · exact match_zero_fix ⟨115, by decide⟩ ⟨81, by decide⟩ p hp j hj hq fz1_115_81 fz2_115_81
  · exact match_zero_fix ⟨116, by decide⟩ ⟨81, by decide⟩ p hp j hj hq fz1_116_81 fz2_116_81
  · exact match_zero_fix ⟨117, by decide⟩ ⟨81, by decide⟩ p hp j hj hq fz1_117_81 fz2_117_81
  · exact match_zero_fix ⟨118, by decide⟩ ⟨81, by decide⟩ p hp j hj hq fz1_118_81 fz2_118_81
  · exact match_zero_fix ⟨119, by decide⟩ ⟨81, by decide⟩ p hp j hj hq fz1_119_81 fz2_119_81
  · exact match_zero_fix ⟨120, by decide⟩ ⟨81, by decide⟩ p hp j hj hq fz1_120_81 fz2_120_81
  · exact pair_121_81 p hp hrep j hj hq
  · exact pair_122_81 p hp hrep j hj hq
  · exact pair_123_81 p hp hrep j hj hq
  · exact pair_124_81 p hp hrep j hj hq
  · exact pair_125_81 p hp hrep j hj hq
  · exact match_zero_fix ⟨126, by decide⟩ ⟨81, by decide⟩ p hp j hj hq fz1_126_81 fz2_126_81
  · exact match_zero_fix ⟨127, by decide⟩ ⟨81, by decide⟩ p hp j hj hq fz1_127_81 fz2_127_81
  · exact match_zero_fix ⟨128, by decide⟩ ⟨81, by decide⟩ p hp j hj hq fz1_128_81 fz2_128_81
  · exact match_zero_fix ⟨129, by decide⟩ ⟨81, by decide⟩ p hp j hj hq fz1_129_81 fz2_129_81
  · exact match_zero_fix ⟨130, by decide⟩ ⟨81, by decide⟩ p hp j hj hq fz1_130_81 fz2_130_81
  · exact match_zero_fix ⟨131, by decide⟩ ⟨81, by decide⟩ p hp j hj hq fz1_131_81 fz2_131_81
  · exact match_zero_fix ⟨132, by decide⟩ ⟨81, by decide⟩ p hp j hj hq fz1_132_81 fz2_132_81
  · exact match_zero_fix ⟨133, by decide⟩ ⟨81, by decide⟩ p hp j hj hq fz1_133_81 fz2_133_81
  · exact match_zero_fix ⟨134, by decide⟩ ⟨81, by decide⟩ p hp j hj hq fz1_134_81 fz2_134_81
  · exact match_zero_fix ⟨135, by decide⟩ ⟨81, by decide⟩ p hp j hj hq fz1_135_81 fz2_135_81
  · exact match_zero_fix ⟨136, by decide⟩ ⟨81, by decide⟩ p hp j hj hq fz1_136_81 fz2_136_81
  · exact match_zero_fix ⟨137, by decide⟩ ⟨81, by decide⟩ p hp j hj hq fz1_137_81 fz2_137_81
  · exact match_zero_fix ⟨138, by decide⟩ ⟨81, by decide⟩ p hp j hj hq fz1_138_81 fz2_138_81
  · exact match_zero_fix ⟨139, by decide⟩ ⟨81, by decide⟩ p hp j hj hq fz1_139_81 fz2_139_81
  · exact match_zero_fix ⟨140, by decide⟩ ⟨81, by decide⟩ p hp j hj hq fz1_140_81 fz2_140_81
  · exact pair_141_81 p hp hrep j hj hq
  · exact match_zero_fix ⟨142, by decide⟩ ⟨81, by decide⟩ p hp j hj hq fz1_142_81 fz2_142_81
  · exact match_zero_fix ⟨143, by decide⟩ ⟨81, by decide⟩ p hp j hj hq fz1_143_81 fz2_143_81
  · exact match_zero_fix ⟨144, by decide⟩ ⟨81, by decide⟩ p hp j hj hq fz1_144_81 fz2_144_81
  · exact match_zero_fix ⟨145, by decide⟩ ⟨81, by decide⟩ p hp j hj hq fz1_145_81 fz2_145_81
  · exact match_zero_fix ⟨146, by decide⟩ ⟨81, by decide⟩ p hp j hj hq fz1_146_81 fz2_146_81
  · exact pair_147_81 p hp hrep j hj hq

theorem master_82 (p : Nat) (hp : p < (Q2.transData.getD 82 []).length)
    (hrep : (Q2.cosetIsRep.getD 82 []).getD p false = true)
    (rK : Fin 148) (j : Nat) (hj : j < (repChars.getD rK.val []).length)
    (hq : (normIsRep.getD rK.val []).getD j false = true) :
    species (Q2.reps (⟨82, by decide⟩ : Fin 148)) (colE2 ⟨82, by decide⟩ p hp)
        (rowE2 rK j hj hq)
      = species (reps (⟨82, by decide⟩ : Fin 148))
        (colE1 ⟨82, by decide⟩ p (transLenTr ⟨82, by decide⟩ p hp)) (rowE1 rK j hj) := by
  rcases rK with ⟨nK, hnK⟩; interval_cases nK
  · exact match_zero_len ⟨0, by decide⟩ ⟨82, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨1, by decide⟩ ⟨82, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨2, by decide⟩ ⟨82, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨3, by decide⟩ ⟨82, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨4, by decide⟩ ⟨82, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨5, by decide⟩ ⟨82, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨6, by decide⟩ ⟨82, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨7, by decide⟩ ⟨82, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨8, by decide⟩ ⟨82, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨9, by decide⟩ ⟨82, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨10, by decide⟩ ⟨82, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨11, by decide⟩ ⟨82, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨12, by decide⟩ ⟨82, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨13, by decide⟩ ⟨82, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨14, by decide⟩ ⟨82, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨15, by decide⟩ ⟨82, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨16, by decide⟩ ⟨82, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨17, by decide⟩ ⟨82, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨18, by decide⟩ ⟨82, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨19, by decide⟩ ⟨82, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨20, by decide⟩ ⟨82, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨21, by decide⟩ ⟨82, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨22, by decide⟩ ⟨82, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨23, by decide⟩ ⟨82, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨24, by decide⟩ ⟨82, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨25, by decide⟩ ⟨82, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨26, by decide⟩ ⟨82, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨27, by decide⟩ ⟨82, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨28, by decide⟩ ⟨82, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨29, by decide⟩ ⟨82, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨30, by decide⟩ ⟨82, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨31, by decide⟩ ⟨82, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨32, by decide⟩ ⟨82, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨33, by decide⟩ ⟨82, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨34, by decide⟩ ⟨82, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨35, by decide⟩ ⟨82, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨36, by decide⟩ ⟨82, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨37, by decide⟩ ⟨82, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨38, by decide⟩ ⟨82, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨39, by decide⟩ ⟨82, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨40, by decide⟩ ⟨82, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨41, by decide⟩ ⟨82, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨42, by decide⟩ ⟨82, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨43, by decide⟩ ⟨82, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨44, by decide⟩ ⟨82, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨45, by decide⟩ ⟨82, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨46, by decide⟩ ⟨82, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨47, by decide⟩ ⟨82, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨48, by decide⟩ ⟨82, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨49, by decide⟩ ⟨82, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨50, by decide⟩ ⟨82, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨51, by decide⟩ ⟨82, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨52, by decide⟩ ⟨82, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨53, by decide⟩ ⟨82, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨54, by decide⟩ ⟨82, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_fix ⟨55, by decide⟩ ⟨82, by decide⟩ p hp j hj hq fz1_55_82 fz2_55_82
  · exact match_zero_fix ⟨56, by decide⟩ ⟨82, by decide⟩ p hp j hj hq fz1_56_82 fz2_56_82
  · exact match_zero_fix ⟨57, by decide⟩ ⟨82, by decide⟩ p hp j hj hq fz1_57_82 fz2_57_82
  · exact match_zero_fix ⟨58, by decide⟩ ⟨82, by decide⟩ p hp j hj hq fz1_58_82 fz2_58_82
  · exact match_zero_fix ⟨59, by decide⟩ ⟨82, by decide⟩ p hp j hj hq fz1_59_82 fz2_59_82
  · exact match_zero_fix ⟨60, by decide⟩ ⟨82, by decide⟩ p hp j hj hq fz1_60_82 fz2_60_82
  · exact match_zero_fix ⟨61, by decide⟩ ⟨82, by decide⟩ p hp j hj hq fz1_61_82 fz2_61_82
  · exact match_zero_fix ⟨62, by decide⟩ ⟨82, by decide⟩ p hp j hj hq fz1_62_82 fz2_62_82
  · exact match_zero_fix ⟨63, by decide⟩ ⟨82, by decide⟩ p hp j hj hq fz1_63_82 fz2_63_82
  · exact match_zero_fix ⟨64, by decide⟩ ⟨82, by decide⟩ p hp j hj hq fz1_64_82 fz2_64_82
  · exact match_zero_fix ⟨65, by decide⟩ ⟨82, by decide⟩ p hp j hj hq fz1_65_82 fz2_65_82
  · exact match_zero_fix ⟨66, by decide⟩ ⟨82, by decide⟩ p hp j hj hq fz1_66_82 fz2_66_82
  · exact match_zero_fix ⟨67, by decide⟩ ⟨82, by decide⟩ p hp j hj hq fz1_67_82 fz2_67_82
  · exact match_zero_fix ⟨68, by decide⟩ ⟨82, by decide⟩ p hp j hj hq fz1_68_82 fz2_68_82
  · exact match_zero_fix ⟨69, by decide⟩ ⟨82, by decide⟩ p hp j hj hq fz1_69_82 fz2_69_82
  · exact match_zero_fix ⟨70, by decide⟩ ⟨82, by decide⟩ p hp j hj hq fz1_70_82 fz2_70_82
  · exact match_zero_fix ⟨71, by decide⟩ ⟨82, by decide⟩ p hp j hj hq fz1_71_82 fz2_71_82
  · exact match_zero_fix ⟨72, by decide⟩ ⟨82, by decide⟩ p hp j hj hq fz1_72_82 fz2_72_82
  · exact match_zero_fix ⟨73, by decide⟩ ⟨82, by decide⟩ p hp j hj hq fz1_73_82 fz2_73_82
  · exact match_zero_fix ⟨74, by decide⟩ ⟨82, by decide⟩ p hp j hj hq fz1_74_82 fz2_74_82
  · exact match_zero_fix ⟨75, by decide⟩ ⟨82, by decide⟩ p hp j hj hq fz1_75_82 fz2_75_82
  · exact match_zero_fix ⟨76, by decide⟩ ⟨82, by decide⟩ p hp j hj hq fz1_76_82 fz2_76_82
  · exact match_zero_fix ⟨77, by decide⟩ ⟨82, by decide⟩ p hp j hj hq fz1_77_82 fz2_77_82
  · exact match_zero_fix ⟨78, by decide⟩ ⟨82, by decide⟩ p hp j hj hq fz1_78_82 fz2_78_82
  · exact match_zero_fix ⟨79, by decide⟩ ⟨82, by decide⟩ p hp j hj hq fz1_79_82 fz2_79_82
  · exact match_zero_fix ⟨80, by decide⟩ ⟨82, by decide⟩ p hp j hj hq fz1_80_82 fz2_80_82
  · exact match_zero_fix ⟨81, by decide⟩ ⟨82, by decide⟩ p hp j hj hq fz1_81_82 fz2_81_82
  · exact pair_82_82 p hp hrep j hj hq
  · exact match_zero_fix ⟨83, by decide⟩ ⟨82, by decide⟩ p hp j hj hq fz1_83_82 fz2_83_82
  · exact match_zero_fix ⟨84, by decide⟩ ⟨82, by decide⟩ p hp j hj hq fz1_84_82 fz2_84_82
  · exact match_zero_fix ⟨85, by decide⟩ ⟨82, by decide⟩ p hp j hj hq fz1_85_82 fz2_85_82
  · exact match_zero_fix ⟨86, by decide⟩ ⟨82, by decide⟩ p hp j hj hq fz1_86_82 fz2_86_82
  · exact match_zero_fix ⟨87, by decide⟩ ⟨82, by decide⟩ p hp j hj hq fz1_87_82 fz2_87_82
  · exact match_zero_fix ⟨88, by decide⟩ ⟨82, by decide⟩ p hp j hj hq fz1_88_82 fz2_88_82
  · exact match_zero_fix ⟨89, by decide⟩ ⟨82, by decide⟩ p hp j hj hq fz1_89_82 fz2_89_82
  · exact match_zero_fix ⟨90, by decide⟩ ⟨82, by decide⟩ p hp j hj hq fz1_90_82 fz2_90_82
  · exact match_zero_fix ⟨91, by decide⟩ ⟨82, by decide⟩ p hp j hj hq fz1_91_82 fz2_91_82
  · exact match_zero_fix ⟨92, by decide⟩ ⟨82, by decide⟩ p hp j hj hq fz1_92_82 fz2_92_82
  · exact match_zero_fix ⟨93, by decide⟩ ⟨82, by decide⟩ p hp j hj hq fz1_93_82 fz2_93_82
  · exact match_zero_fix ⟨94, by decide⟩ ⟨82, by decide⟩ p hp j hj hq fz1_94_82 fz2_94_82
  · exact match_zero_fix ⟨95, by decide⟩ ⟨82, by decide⟩ p hp j hj hq fz1_95_82 fz2_95_82
  · exact match_zero_fix ⟨96, by decide⟩ ⟨82, by decide⟩ p hp j hj hq fz1_96_82 fz2_96_82
  · exact match_zero_fix ⟨97, by decide⟩ ⟨82, by decide⟩ p hp j hj hq fz1_97_82 fz2_97_82
  · exact match_zero_fix ⟨98, by decide⟩ ⟨82, by decide⟩ p hp j hj hq fz1_98_82 fz2_98_82
  · exact match_zero_fix ⟨99, by decide⟩ ⟨82, by decide⟩ p hp j hj hq fz1_99_82 fz2_99_82
  · exact match_zero_fix ⟨100, by decide⟩ ⟨82, by decide⟩ p hp j hj hq fz1_100_82 fz2_100_82
  · exact match_zero_fix ⟨101, by decide⟩ ⟨82, by decide⟩ p hp j hj hq fz1_101_82 fz2_101_82
  · exact match_zero_fix ⟨102, by decide⟩ ⟨82, by decide⟩ p hp j hj hq fz1_102_82 fz2_102_82
  · exact match_zero_fix ⟨103, by decide⟩ ⟨82, by decide⟩ p hp j hj hq fz1_103_82 fz2_103_82
  · exact match_zero_fix ⟨104, by decide⟩ ⟨82, by decide⟩ p hp j hj hq fz1_104_82 fz2_104_82
  · exact match_zero_fix ⟨105, by decide⟩ ⟨82, by decide⟩ p hp j hj hq fz1_105_82 fz2_105_82
  · exact match_zero_fix ⟨106, by decide⟩ ⟨82, by decide⟩ p hp j hj hq fz1_106_82 fz2_106_82
  · exact match_zero_fix ⟨107, by decide⟩ ⟨82, by decide⟩ p hp j hj hq fz1_107_82 fz2_107_82
  · exact match_zero_fix ⟨108, by decide⟩ ⟨82, by decide⟩ p hp j hj hq fz1_108_82 fz2_108_82
  · exact match_zero_fix ⟨109, by decide⟩ ⟨82, by decide⟩ p hp j hj hq fz1_109_82 fz2_109_82
  · exact match_zero_fix ⟨110, by decide⟩ ⟨82, by decide⟩ p hp j hj hq fz1_110_82 fz2_110_82
  · exact match_zero_fix ⟨111, by decide⟩ ⟨82, by decide⟩ p hp j hj hq fz1_111_82 fz2_111_82
  · exact match_zero_fix ⟨112, by decide⟩ ⟨82, by decide⟩ p hp j hj hq fz1_112_82 fz2_112_82
  · exact match_zero_fix ⟨113, by decide⟩ ⟨82, by decide⟩ p hp j hj hq fz1_113_82 fz2_113_82
  · exact match_zero_fix ⟨114, by decide⟩ ⟨82, by decide⟩ p hp j hj hq fz1_114_82 fz2_114_82
  · exact match_zero_fix ⟨115, by decide⟩ ⟨82, by decide⟩ p hp j hj hq fz1_115_82 fz2_115_82
  · exact match_zero_fix ⟨116, by decide⟩ ⟨82, by decide⟩ p hp j hj hq fz1_116_82 fz2_116_82
  · exact match_zero_fix ⟨117, by decide⟩ ⟨82, by decide⟩ p hp j hj hq fz1_117_82 fz2_117_82
  · exact match_zero_fix ⟨118, by decide⟩ ⟨82, by decide⟩ p hp j hj hq fz1_118_82 fz2_118_82
  · exact match_zero_fix ⟨119, by decide⟩ ⟨82, by decide⟩ p hp j hj hq fz1_119_82 fz2_119_82
  · exact match_zero_fix ⟨120, by decide⟩ ⟨82, by decide⟩ p hp j hj hq fz1_120_82 fz2_120_82
  · exact match_zero_fix ⟨121, by decide⟩ ⟨82, by decide⟩ p hp j hj hq fz1_121_82 fz2_121_82
  · exact match_zero_fix ⟨122, by decide⟩ ⟨82, by decide⟩ p hp j hj hq fz1_122_82 fz2_122_82
  · exact match_zero_fix ⟨123, by decide⟩ ⟨82, by decide⟩ p hp j hj hq fz1_123_82 fz2_123_82
  · exact match_zero_fix ⟨124, by decide⟩ ⟨82, by decide⟩ p hp j hj hq fz1_124_82 fz2_124_82
  · exact match_zero_fix ⟨125, by decide⟩ ⟨82, by decide⟩ p hp j hj hq fz1_125_82 fz2_125_82
  · exact pair_126_82 p hp hrep j hj hq
  · exact pair_127_82 p hp hrep j hj hq
  · exact pair_128_82 p hp hrep j hj hq
  · exact pair_129_82 p hp hrep j hj hq
  · exact pair_130_82 p hp hrep j hj hq
  · exact match_zero_fix ⟨131, by decide⟩ ⟨82, by decide⟩ p hp j hj hq fz1_131_82 fz2_131_82
  · exact match_zero_fix ⟨132, by decide⟩ ⟨82, by decide⟩ p hp j hj hq fz1_132_82 fz2_132_82
  · exact match_zero_fix ⟨133, by decide⟩ ⟨82, by decide⟩ p hp j hj hq fz1_133_82 fz2_133_82
  · exact match_zero_fix ⟨134, by decide⟩ ⟨82, by decide⟩ p hp j hj hq fz1_134_82 fz2_134_82
  · exact match_zero_fix ⟨135, by decide⟩ ⟨82, by decide⟩ p hp j hj hq fz1_135_82 fz2_135_82
  · exact match_zero_fix ⟨136, by decide⟩ ⟨82, by decide⟩ p hp j hj hq fz1_136_82 fz2_136_82
  · exact match_zero_fix ⟨137, by decide⟩ ⟨82, by decide⟩ p hp j hj hq fz1_137_82 fz2_137_82
  · exact match_zero_fix ⟨138, by decide⟩ ⟨82, by decide⟩ p hp j hj hq fz1_138_82 fz2_138_82
  · exact match_zero_fix ⟨139, by decide⟩ ⟨82, by decide⟩ p hp j hj hq fz1_139_82 fz2_139_82
  · exact match_zero_fix ⟨140, by decide⟩ ⟨82, by decide⟩ p hp j hj hq fz1_140_82 fz2_140_82
  · exact pair_141_82 p hp hrep j hj hq
  · exact match_zero_fix ⟨142, by decide⟩ ⟨82, by decide⟩ p hp j hj hq fz1_142_82 fz2_142_82
  · exact match_zero_fix ⟨143, by decide⟩ ⟨82, by decide⟩ p hp j hj hq fz1_143_82 fz2_143_82
  · exact match_zero_fix ⟨144, by decide⟩ ⟨82, by decide⟩ p hp j hj hq fz1_144_82 fz2_144_82
  · exact match_zero_fix ⟨145, by decide⟩ ⟨82, by decide⟩ p hp j hj hq fz1_145_82 fz2_145_82
  · exact match_zero_fix ⟨146, by decide⟩ ⟨82, by decide⟩ p hp j hj hq fz1_146_82 fz2_146_82
  · exact pair_147_82 p hp hrep j hj hq

theorem master_83 (p : Nat) (hp : p < (Q2.transData.getD 83 []).length)
    (hrep : (Q2.cosetIsRep.getD 83 []).getD p false = true)
    (rK : Fin 148) (j : Nat) (hj : j < (repChars.getD rK.val []).length)
    (hq : (normIsRep.getD rK.val []).getD j false = true) :
    species (Q2.reps (⟨83, by decide⟩ : Fin 148)) (colE2 ⟨83, by decide⟩ p hp)
        (rowE2 rK j hj hq)
      = species (reps (⟨83, by decide⟩ : Fin 148))
        (colE1 ⟨83, by decide⟩ p (transLenTr ⟨83, by decide⟩ p hp)) (rowE1 rK j hj) := by
  rcases rK with ⟨nK, hnK⟩; interval_cases nK
  · exact match_zero_len ⟨0, by decide⟩ ⟨83, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨1, by decide⟩ ⟨83, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨2, by decide⟩ ⟨83, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨3, by decide⟩ ⟨83, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨4, by decide⟩ ⟨83, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨5, by decide⟩ ⟨83, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨6, by decide⟩ ⟨83, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨7, by decide⟩ ⟨83, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨8, by decide⟩ ⟨83, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨9, by decide⟩ ⟨83, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨10, by decide⟩ ⟨83, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨11, by decide⟩ ⟨83, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨12, by decide⟩ ⟨83, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨13, by decide⟩ ⟨83, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨14, by decide⟩ ⟨83, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨15, by decide⟩ ⟨83, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨16, by decide⟩ ⟨83, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨17, by decide⟩ ⟨83, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨18, by decide⟩ ⟨83, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨19, by decide⟩ ⟨83, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨20, by decide⟩ ⟨83, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨21, by decide⟩ ⟨83, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨22, by decide⟩ ⟨83, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨23, by decide⟩ ⟨83, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨24, by decide⟩ ⟨83, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨25, by decide⟩ ⟨83, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨26, by decide⟩ ⟨83, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨27, by decide⟩ ⟨83, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨28, by decide⟩ ⟨83, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨29, by decide⟩ ⟨83, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨30, by decide⟩ ⟨83, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨31, by decide⟩ ⟨83, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨32, by decide⟩ ⟨83, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨33, by decide⟩ ⟨83, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨34, by decide⟩ ⟨83, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨35, by decide⟩ ⟨83, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨36, by decide⟩ ⟨83, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨37, by decide⟩ ⟨83, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨38, by decide⟩ ⟨83, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨39, by decide⟩ ⟨83, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨40, by decide⟩ ⟨83, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨41, by decide⟩ ⟨83, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨42, by decide⟩ ⟨83, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨43, by decide⟩ ⟨83, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨44, by decide⟩ ⟨83, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨45, by decide⟩ ⟨83, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨46, by decide⟩ ⟨83, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨47, by decide⟩ ⟨83, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨48, by decide⟩ ⟨83, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨49, by decide⟩ ⟨83, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨50, by decide⟩ ⟨83, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨51, by decide⟩ ⟨83, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨52, by decide⟩ ⟨83, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨53, by decide⟩ ⟨83, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨54, by decide⟩ ⟨83, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_fix ⟨55, by decide⟩ ⟨83, by decide⟩ p hp j hj hq fz1_55_83 fz2_55_83
  · exact match_zero_fix ⟨56, by decide⟩ ⟨83, by decide⟩ p hp j hj hq fz1_56_83 fz2_56_83
  · exact match_zero_fix ⟨57, by decide⟩ ⟨83, by decide⟩ p hp j hj hq fz1_57_83 fz2_57_83
  · exact match_zero_fix ⟨58, by decide⟩ ⟨83, by decide⟩ p hp j hj hq fz1_58_83 fz2_58_83
  · exact match_zero_fix ⟨59, by decide⟩ ⟨83, by decide⟩ p hp j hj hq fz1_59_83 fz2_59_83
  · exact match_zero_fix ⟨60, by decide⟩ ⟨83, by decide⟩ p hp j hj hq fz1_60_83 fz2_60_83
  · exact match_zero_fix ⟨61, by decide⟩ ⟨83, by decide⟩ p hp j hj hq fz1_61_83 fz2_61_83
  · exact match_zero_fix ⟨62, by decide⟩ ⟨83, by decide⟩ p hp j hj hq fz1_62_83 fz2_62_83
  · exact match_zero_fix ⟨63, by decide⟩ ⟨83, by decide⟩ p hp j hj hq fz1_63_83 fz2_63_83
  · exact match_zero_fix ⟨64, by decide⟩ ⟨83, by decide⟩ p hp j hj hq fz1_64_83 fz2_64_83
  · exact match_zero_fix ⟨65, by decide⟩ ⟨83, by decide⟩ p hp j hj hq fz1_65_83 fz2_65_83
  · exact match_zero_fix ⟨66, by decide⟩ ⟨83, by decide⟩ p hp j hj hq fz1_66_83 fz2_66_83
  · exact match_zero_fix ⟨67, by decide⟩ ⟨83, by decide⟩ p hp j hj hq fz1_67_83 fz2_67_83
  · exact match_zero_fix ⟨68, by decide⟩ ⟨83, by decide⟩ p hp j hj hq fz1_68_83 fz2_68_83
  · exact match_zero_fix ⟨69, by decide⟩ ⟨83, by decide⟩ p hp j hj hq fz1_69_83 fz2_69_83
  · exact match_zero_fix ⟨70, by decide⟩ ⟨83, by decide⟩ p hp j hj hq fz1_70_83 fz2_70_83
  · exact match_zero_fix ⟨71, by decide⟩ ⟨83, by decide⟩ p hp j hj hq fz1_71_83 fz2_71_83
  · exact match_zero_fix ⟨72, by decide⟩ ⟨83, by decide⟩ p hp j hj hq fz1_72_83 fz2_72_83
  · exact match_zero_fix ⟨73, by decide⟩ ⟨83, by decide⟩ p hp j hj hq fz1_73_83 fz2_73_83
  · exact match_zero_fix ⟨74, by decide⟩ ⟨83, by decide⟩ p hp j hj hq fz1_74_83 fz2_74_83
  · exact match_zero_fix ⟨75, by decide⟩ ⟨83, by decide⟩ p hp j hj hq fz1_75_83 fz2_75_83
  · exact match_zero_fix ⟨76, by decide⟩ ⟨83, by decide⟩ p hp j hj hq fz1_76_83 fz2_76_83
  · exact match_zero_fix ⟨77, by decide⟩ ⟨83, by decide⟩ p hp j hj hq fz1_77_83 fz2_77_83
  · exact match_zero_fix ⟨78, by decide⟩ ⟨83, by decide⟩ p hp j hj hq fz1_78_83 fz2_78_83
  · exact match_zero_fix ⟨79, by decide⟩ ⟨83, by decide⟩ p hp j hj hq fz1_79_83 fz2_79_83
  · exact match_zero_fix ⟨80, by decide⟩ ⟨83, by decide⟩ p hp j hj hq fz1_80_83 fz2_80_83
  · exact match_zero_fix ⟨81, by decide⟩ ⟨83, by decide⟩ p hp j hj hq fz1_81_83 fz2_81_83
  · exact match_zero_fix ⟨82, by decide⟩ ⟨83, by decide⟩ p hp j hj hq fz1_82_83 fz2_82_83
  · exact pair_83_83 p hp hrep j hj hq
  · exact match_zero_fix ⟨84, by decide⟩ ⟨83, by decide⟩ p hp j hj hq fz1_84_83 fz2_84_83
  · exact match_zero_fix ⟨85, by decide⟩ ⟨83, by decide⟩ p hp j hj hq fz1_85_83 fz2_85_83
  · exact match_zero_fix ⟨86, by decide⟩ ⟨83, by decide⟩ p hp j hj hq fz1_86_83 fz2_86_83
  · exact match_zero_fix ⟨87, by decide⟩ ⟨83, by decide⟩ p hp j hj hq fz1_87_83 fz2_87_83
  · exact match_zero_fix ⟨88, by decide⟩ ⟨83, by decide⟩ p hp j hj hq fz1_88_83 fz2_88_83
  · exact match_zero_fix ⟨89, by decide⟩ ⟨83, by decide⟩ p hp j hj hq fz1_89_83 fz2_89_83
  · exact match_zero_fix ⟨90, by decide⟩ ⟨83, by decide⟩ p hp j hj hq fz1_90_83 fz2_90_83
  · exact match_zero_fix ⟨91, by decide⟩ ⟨83, by decide⟩ p hp j hj hq fz1_91_83 fz2_91_83
  · exact match_zero_fix ⟨92, by decide⟩ ⟨83, by decide⟩ p hp j hj hq fz1_92_83 fz2_92_83
  · exact match_zero_fix ⟨93, by decide⟩ ⟨83, by decide⟩ p hp j hj hq fz1_93_83 fz2_93_83
  · exact match_zero_fix ⟨94, by decide⟩ ⟨83, by decide⟩ p hp j hj hq fz1_94_83 fz2_94_83
  · exact match_zero_fix ⟨95, by decide⟩ ⟨83, by decide⟩ p hp j hj hq fz1_95_83 fz2_95_83
  · exact match_zero_fix ⟨96, by decide⟩ ⟨83, by decide⟩ p hp j hj hq fz1_96_83 fz2_96_83
  · exact match_zero_fix ⟨97, by decide⟩ ⟨83, by decide⟩ p hp j hj hq fz1_97_83 fz2_97_83
  · exact match_zero_fix ⟨98, by decide⟩ ⟨83, by decide⟩ p hp j hj hq fz1_98_83 fz2_98_83
  · exact match_zero_fix ⟨99, by decide⟩ ⟨83, by decide⟩ p hp j hj hq fz1_99_83 fz2_99_83
  · exact match_zero_fix ⟨100, by decide⟩ ⟨83, by decide⟩ p hp j hj hq fz1_100_83 fz2_100_83
  · exact match_zero_fix ⟨101, by decide⟩ ⟨83, by decide⟩ p hp j hj hq fz1_101_83 fz2_101_83
  · exact match_zero_fix ⟨102, by decide⟩ ⟨83, by decide⟩ p hp j hj hq fz1_102_83 fz2_102_83
  · exact match_zero_fix ⟨103, by decide⟩ ⟨83, by decide⟩ p hp j hj hq fz1_103_83 fz2_103_83
  · exact match_zero_fix ⟨104, by decide⟩ ⟨83, by decide⟩ p hp j hj hq fz1_104_83 fz2_104_83
  · exact match_zero_fix ⟨105, by decide⟩ ⟨83, by decide⟩ p hp j hj hq fz1_105_83 fz2_105_83
  · exact match_zero_fix ⟨106, by decide⟩ ⟨83, by decide⟩ p hp j hj hq fz1_106_83 fz2_106_83
  · exact match_zero_fix ⟨107, by decide⟩ ⟨83, by decide⟩ p hp j hj hq fz1_107_83 fz2_107_83
  · exact match_zero_fix ⟨108, by decide⟩ ⟨83, by decide⟩ p hp j hj hq fz1_108_83 fz2_108_83
  · exact match_zero_fix ⟨109, by decide⟩ ⟨83, by decide⟩ p hp j hj hq fz1_109_83 fz2_109_83
  · exact match_zero_fix ⟨110, by decide⟩ ⟨83, by decide⟩ p hp j hj hq fz1_110_83 fz2_110_83
  · exact match_zero_fix ⟨111, by decide⟩ ⟨83, by decide⟩ p hp j hj hq fz1_111_83 fz2_111_83
  · exact match_zero_fix ⟨112, by decide⟩ ⟨83, by decide⟩ p hp j hj hq fz1_112_83 fz2_112_83
  · exact match_zero_fix ⟨113, by decide⟩ ⟨83, by decide⟩ p hp j hj hq fz1_113_83 fz2_113_83
  · exact match_zero_fix ⟨114, by decide⟩ ⟨83, by decide⟩ p hp j hj hq fz1_114_83 fz2_114_83
  · exact match_zero_fix ⟨115, by decide⟩ ⟨83, by decide⟩ p hp j hj hq fz1_115_83 fz2_115_83
  · exact match_zero_fix ⟨116, by decide⟩ ⟨83, by decide⟩ p hp j hj hq fz1_116_83 fz2_116_83
  · exact match_zero_fix ⟨117, by decide⟩ ⟨83, by decide⟩ p hp j hj hq fz1_117_83 fz2_117_83
  · exact match_zero_fix ⟨118, by decide⟩ ⟨83, by decide⟩ p hp j hj hq fz1_118_83 fz2_118_83
  · exact match_zero_fix ⟨119, by decide⟩ ⟨83, by decide⟩ p hp j hj hq fz1_119_83 fz2_119_83
  · exact match_zero_fix ⟨120, by decide⟩ ⟨83, by decide⟩ p hp j hj hq fz1_120_83 fz2_120_83
  · exact match_zero_fix ⟨121, by decide⟩ ⟨83, by decide⟩ p hp j hj hq fz1_121_83 fz2_121_83
  · exact match_zero_fix ⟨122, by decide⟩ ⟨83, by decide⟩ p hp j hj hq fz1_122_83 fz2_122_83
  · exact match_zero_fix ⟨123, by decide⟩ ⟨83, by decide⟩ p hp j hj hq fz1_123_83 fz2_123_83
  · exact match_zero_fix ⟨124, by decide⟩ ⟨83, by decide⟩ p hp j hj hq fz1_124_83 fz2_124_83
  · exact match_zero_fix ⟨125, by decide⟩ ⟨83, by decide⟩ p hp j hj hq fz1_125_83 fz2_125_83
  · exact match_zero_fix ⟨126, by decide⟩ ⟨83, by decide⟩ p hp j hj hq fz1_126_83 fz2_126_83
  · exact match_zero_fix ⟨127, by decide⟩ ⟨83, by decide⟩ p hp j hj hq fz1_127_83 fz2_127_83
  · exact match_zero_fix ⟨128, by decide⟩ ⟨83, by decide⟩ p hp j hj hq fz1_128_83 fz2_128_83
  · exact match_zero_fix ⟨129, by decide⟩ ⟨83, by decide⟩ p hp j hj hq fz1_129_83 fz2_129_83
  · exact match_zero_fix ⟨130, by decide⟩ ⟨83, by decide⟩ p hp j hj hq fz1_130_83 fz2_130_83
  · exact pair_131_83 p hp hrep j hj hq
  · exact pair_132_83 p hp hrep j hj hq
  · exact pair_133_83 p hp hrep j hj hq
  · exact pair_134_83 p hp hrep j hj hq
  · exact pair_135_83 p hp hrep j hj hq
  · exact match_zero_fix ⟨136, by decide⟩ ⟨83, by decide⟩ p hp j hj hq fz1_136_83 fz2_136_83
  · exact match_zero_fix ⟨137, by decide⟩ ⟨83, by decide⟩ p hp j hj hq fz1_137_83 fz2_137_83
  · exact match_zero_fix ⟨138, by decide⟩ ⟨83, by decide⟩ p hp j hj hq fz1_138_83 fz2_138_83
  · exact match_zero_fix ⟨139, by decide⟩ ⟨83, by decide⟩ p hp j hj hq fz1_139_83 fz2_139_83
  · exact match_zero_fix ⟨140, by decide⟩ ⟨83, by decide⟩ p hp j hj hq fz1_140_83 fz2_140_83
  · exact pair_141_83 p hp hrep j hj hq
  · exact match_zero_fix ⟨142, by decide⟩ ⟨83, by decide⟩ p hp j hj hq fz1_142_83 fz2_142_83
  · exact match_zero_fix ⟨143, by decide⟩ ⟨83, by decide⟩ p hp j hj hq fz1_143_83 fz2_143_83
  · exact match_zero_fix ⟨144, by decide⟩ ⟨83, by decide⟩ p hp j hj hq fz1_144_83 fz2_144_83
  · exact match_zero_fix ⟨145, by decide⟩ ⟨83, by decide⟩ p hp j hj hq fz1_145_83 fz2_145_83
  · exact match_zero_fix ⟨146, by decide⟩ ⟨83, by decide⟩ p hp j hj hq fz1_146_83 fz2_146_83
  · exact pair_147_83 p hp hrep j hj hq

theorem master_84 (p : Nat) (hp : p < (Q2.transData.getD 84 []).length)
    (hrep : (Q2.cosetIsRep.getD 84 []).getD p false = true)
    (rK : Fin 148) (j : Nat) (hj : j < (repChars.getD rK.val []).length)
    (hq : (normIsRep.getD rK.val []).getD j false = true) :
    species (Q2.reps (⟨84, by decide⟩ : Fin 148)) (colE2 ⟨84, by decide⟩ p hp)
        (rowE2 rK j hj hq)
      = species (reps (⟨84, by decide⟩ : Fin 148))
        (colE1 ⟨84, by decide⟩ p (transLenTr ⟨84, by decide⟩ p hp)) (rowE1 rK j hj) := by
  rcases rK with ⟨nK, hnK⟩; interval_cases nK
  · exact match_zero_len ⟨0, by decide⟩ ⟨84, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨1, by decide⟩ ⟨84, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨2, by decide⟩ ⟨84, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨3, by decide⟩ ⟨84, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨4, by decide⟩ ⟨84, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨5, by decide⟩ ⟨84, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨6, by decide⟩ ⟨84, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨7, by decide⟩ ⟨84, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨8, by decide⟩ ⟨84, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨9, by decide⟩ ⟨84, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨10, by decide⟩ ⟨84, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨11, by decide⟩ ⟨84, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨12, by decide⟩ ⟨84, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨13, by decide⟩ ⟨84, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨14, by decide⟩ ⟨84, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨15, by decide⟩ ⟨84, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨16, by decide⟩ ⟨84, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨17, by decide⟩ ⟨84, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨18, by decide⟩ ⟨84, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨19, by decide⟩ ⟨84, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨20, by decide⟩ ⟨84, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨21, by decide⟩ ⟨84, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨22, by decide⟩ ⟨84, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨23, by decide⟩ ⟨84, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨24, by decide⟩ ⟨84, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨25, by decide⟩ ⟨84, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨26, by decide⟩ ⟨84, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨27, by decide⟩ ⟨84, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨28, by decide⟩ ⟨84, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨29, by decide⟩ ⟨84, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨30, by decide⟩ ⟨84, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨31, by decide⟩ ⟨84, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨32, by decide⟩ ⟨84, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨33, by decide⟩ ⟨84, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨34, by decide⟩ ⟨84, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨35, by decide⟩ ⟨84, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨36, by decide⟩ ⟨84, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨37, by decide⟩ ⟨84, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨38, by decide⟩ ⟨84, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨39, by decide⟩ ⟨84, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨40, by decide⟩ ⟨84, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨41, by decide⟩ ⟨84, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨42, by decide⟩ ⟨84, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨43, by decide⟩ ⟨84, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨44, by decide⟩ ⟨84, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨45, by decide⟩ ⟨84, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨46, by decide⟩ ⟨84, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨47, by decide⟩ ⟨84, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨48, by decide⟩ ⟨84, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨49, by decide⟩ ⟨84, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨50, by decide⟩ ⟨84, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨51, by decide⟩ ⟨84, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨52, by decide⟩ ⟨84, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨53, by decide⟩ ⟨84, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨54, by decide⟩ ⟨84, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_fix ⟨55, by decide⟩ ⟨84, by decide⟩ p hp j hj hq fz1_55_84 fz2_55_84
  · exact match_zero_fix ⟨56, by decide⟩ ⟨84, by decide⟩ p hp j hj hq fz1_56_84 fz2_56_84
  · exact match_zero_fix ⟨57, by decide⟩ ⟨84, by decide⟩ p hp j hj hq fz1_57_84 fz2_57_84
  · exact match_zero_fix ⟨58, by decide⟩ ⟨84, by decide⟩ p hp j hj hq fz1_58_84 fz2_58_84
  · exact match_zero_fix ⟨59, by decide⟩ ⟨84, by decide⟩ p hp j hj hq fz1_59_84 fz2_59_84
  · exact match_zero_fix ⟨60, by decide⟩ ⟨84, by decide⟩ p hp j hj hq fz1_60_84 fz2_60_84
  · exact match_zero_fix ⟨61, by decide⟩ ⟨84, by decide⟩ p hp j hj hq fz1_61_84 fz2_61_84
  · exact match_zero_fix ⟨62, by decide⟩ ⟨84, by decide⟩ p hp j hj hq fz1_62_84 fz2_62_84
  · exact match_zero_fix ⟨63, by decide⟩ ⟨84, by decide⟩ p hp j hj hq fz1_63_84 fz2_63_84
  · exact match_zero_fix ⟨64, by decide⟩ ⟨84, by decide⟩ p hp j hj hq fz1_64_84 fz2_64_84
  · exact match_zero_fix ⟨65, by decide⟩ ⟨84, by decide⟩ p hp j hj hq fz1_65_84 fz2_65_84
  · exact match_zero_fix ⟨66, by decide⟩ ⟨84, by decide⟩ p hp j hj hq fz1_66_84 fz2_66_84
  · exact match_zero_fix ⟨67, by decide⟩ ⟨84, by decide⟩ p hp j hj hq fz1_67_84 fz2_67_84
  · exact match_zero_fix ⟨68, by decide⟩ ⟨84, by decide⟩ p hp j hj hq fz1_68_84 fz2_68_84
  · exact match_zero_fix ⟨69, by decide⟩ ⟨84, by decide⟩ p hp j hj hq fz1_69_84 fz2_69_84
  · exact match_zero_fix ⟨70, by decide⟩ ⟨84, by decide⟩ p hp j hj hq fz1_70_84 fz2_70_84
  · exact match_zero_fix ⟨71, by decide⟩ ⟨84, by decide⟩ p hp j hj hq fz1_71_84 fz2_71_84
  · exact match_zero_fix ⟨72, by decide⟩ ⟨84, by decide⟩ p hp j hj hq fz1_72_84 fz2_72_84
  · exact match_zero_fix ⟨73, by decide⟩ ⟨84, by decide⟩ p hp j hj hq fz1_73_84 fz2_73_84
  · exact match_zero_fix ⟨74, by decide⟩ ⟨84, by decide⟩ p hp j hj hq fz1_74_84 fz2_74_84
  · exact match_zero_fix ⟨75, by decide⟩ ⟨84, by decide⟩ p hp j hj hq fz1_75_84 fz2_75_84
  · exact match_zero_fix ⟨76, by decide⟩ ⟨84, by decide⟩ p hp j hj hq fz1_76_84 fz2_76_84
  · exact match_zero_fix ⟨77, by decide⟩ ⟨84, by decide⟩ p hp j hj hq fz1_77_84 fz2_77_84
  · exact match_zero_fix ⟨78, by decide⟩ ⟨84, by decide⟩ p hp j hj hq fz1_78_84 fz2_78_84
  · exact match_zero_fix ⟨79, by decide⟩ ⟨84, by decide⟩ p hp j hj hq fz1_79_84 fz2_79_84
  · exact match_zero_fix ⟨80, by decide⟩ ⟨84, by decide⟩ p hp j hj hq fz1_80_84 fz2_80_84
  · exact match_zero_fix ⟨81, by decide⟩ ⟨84, by decide⟩ p hp j hj hq fz1_81_84 fz2_81_84
  · exact match_zero_fix ⟨82, by decide⟩ ⟨84, by decide⟩ p hp j hj hq fz1_82_84 fz2_82_84
  · exact match_zero_fix ⟨83, by decide⟩ ⟨84, by decide⟩ p hp j hj hq fz1_83_84 fz2_83_84
  · exact pair_84_84 p hp hrep j hj hq
  · exact match_zero_fix ⟨85, by decide⟩ ⟨84, by decide⟩ p hp j hj hq fz1_85_84 fz2_85_84
  · exact match_zero_fix ⟨86, by decide⟩ ⟨84, by decide⟩ p hp j hj hq fz1_86_84 fz2_86_84
  · exact match_zero_fix ⟨87, by decide⟩ ⟨84, by decide⟩ p hp j hj hq fz1_87_84 fz2_87_84
  · exact match_zero_fix ⟨88, by decide⟩ ⟨84, by decide⟩ p hp j hj hq fz1_88_84 fz2_88_84
  · exact match_zero_fix ⟨89, by decide⟩ ⟨84, by decide⟩ p hp j hj hq fz1_89_84 fz2_89_84
  · exact match_zero_fix ⟨90, by decide⟩ ⟨84, by decide⟩ p hp j hj hq fz1_90_84 fz2_90_84
  · exact match_zero_fix ⟨91, by decide⟩ ⟨84, by decide⟩ p hp j hj hq fz1_91_84 fz2_91_84
  · exact match_zero_fix ⟨92, by decide⟩ ⟨84, by decide⟩ p hp j hj hq fz1_92_84 fz2_92_84
  · exact match_zero_fix ⟨93, by decide⟩ ⟨84, by decide⟩ p hp j hj hq fz1_93_84 fz2_93_84
  · exact match_zero_fix ⟨94, by decide⟩ ⟨84, by decide⟩ p hp j hj hq fz1_94_84 fz2_94_84
  · exact match_zero_fix ⟨95, by decide⟩ ⟨84, by decide⟩ p hp j hj hq fz1_95_84 fz2_95_84
  · exact match_zero_fix ⟨96, by decide⟩ ⟨84, by decide⟩ p hp j hj hq fz1_96_84 fz2_96_84
  · exact match_zero_fix ⟨97, by decide⟩ ⟨84, by decide⟩ p hp j hj hq fz1_97_84 fz2_97_84
  · exact match_zero_fix ⟨98, by decide⟩ ⟨84, by decide⟩ p hp j hj hq fz1_98_84 fz2_98_84
  · exact match_zero_fix ⟨99, by decide⟩ ⟨84, by decide⟩ p hp j hj hq fz1_99_84 fz2_99_84
  · exact match_zero_fix ⟨100, by decide⟩ ⟨84, by decide⟩ p hp j hj hq fz1_100_84 fz2_100_84
  · exact match_zero_fix ⟨101, by decide⟩ ⟨84, by decide⟩ p hp j hj hq fz1_101_84 fz2_101_84
  · exact match_zero_fix ⟨102, by decide⟩ ⟨84, by decide⟩ p hp j hj hq fz1_102_84 fz2_102_84
  · exact match_zero_fix ⟨103, by decide⟩ ⟨84, by decide⟩ p hp j hj hq fz1_103_84 fz2_103_84
  · exact match_zero_fix ⟨104, by decide⟩ ⟨84, by decide⟩ p hp j hj hq fz1_104_84 fz2_104_84
  · exact match_zero_fix ⟨105, by decide⟩ ⟨84, by decide⟩ p hp j hj hq fz1_105_84 fz2_105_84
  · exact match_zero_fix ⟨106, by decide⟩ ⟨84, by decide⟩ p hp j hj hq fz1_106_84 fz2_106_84
  · exact match_zero_fix ⟨107, by decide⟩ ⟨84, by decide⟩ p hp j hj hq fz1_107_84 fz2_107_84
  · exact match_zero_fix ⟨108, by decide⟩ ⟨84, by decide⟩ p hp j hj hq fz1_108_84 fz2_108_84
  · exact match_zero_fix ⟨109, by decide⟩ ⟨84, by decide⟩ p hp j hj hq fz1_109_84 fz2_109_84
  · exact match_zero_fix ⟨110, by decide⟩ ⟨84, by decide⟩ p hp j hj hq fz1_110_84 fz2_110_84
  · exact match_zero_fix ⟨111, by decide⟩ ⟨84, by decide⟩ p hp j hj hq fz1_111_84 fz2_111_84
  · exact match_zero_fix ⟨112, by decide⟩ ⟨84, by decide⟩ p hp j hj hq fz1_112_84 fz2_112_84
  · exact match_zero_fix ⟨113, by decide⟩ ⟨84, by decide⟩ p hp j hj hq fz1_113_84 fz2_113_84
  · exact match_zero_fix ⟨114, by decide⟩ ⟨84, by decide⟩ p hp j hj hq fz1_114_84 fz2_114_84
  · exact match_zero_fix ⟨115, by decide⟩ ⟨84, by decide⟩ p hp j hj hq fz1_115_84 fz2_115_84
  · exact match_zero_fix ⟨116, by decide⟩ ⟨84, by decide⟩ p hp j hj hq fz1_116_84 fz2_116_84
  · exact match_zero_fix ⟨117, by decide⟩ ⟨84, by decide⟩ p hp j hj hq fz1_117_84 fz2_117_84
  · exact match_zero_fix ⟨118, by decide⟩ ⟨84, by decide⟩ p hp j hj hq fz1_118_84 fz2_118_84
  · exact match_zero_fix ⟨119, by decide⟩ ⟨84, by decide⟩ p hp j hj hq fz1_119_84 fz2_119_84
  · exact match_zero_fix ⟨120, by decide⟩ ⟨84, by decide⟩ p hp j hj hq fz1_120_84 fz2_120_84
  · exact match_zero_fix ⟨121, by decide⟩ ⟨84, by decide⟩ p hp j hj hq fz1_121_84 fz2_121_84
  · exact match_zero_fix ⟨122, by decide⟩ ⟨84, by decide⟩ p hp j hj hq fz1_122_84 fz2_122_84
  · exact match_zero_fix ⟨123, by decide⟩ ⟨84, by decide⟩ p hp j hj hq fz1_123_84 fz2_123_84
  · exact match_zero_fix ⟨124, by decide⟩ ⟨84, by decide⟩ p hp j hj hq fz1_124_84 fz2_124_84
  · exact match_zero_fix ⟨125, by decide⟩ ⟨84, by decide⟩ p hp j hj hq fz1_125_84 fz2_125_84
  · exact match_zero_fix ⟨126, by decide⟩ ⟨84, by decide⟩ p hp j hj hq fz1_126_84 fz2_126_84
  · exact match_zero_fix ⟨127, by decide⟩ ⟨84, by decide⟩ p hp j hj hq fz1_127_84 fz2_127_84
  · exact match_zero_fix ⟨128, by decide⟩ ⟨84, by decide⟩ p hp j hj hq fz1_128_84 fz2_128_84
  · exact match_zero_fix ⟨129, by decide⟩ ⟨84, by decide⟩ p hp j hj hq fz1_129_84 fz2_129_84
  · exact match_zero_fix ⟨130, by decide⟩ ⟨84, by decide⟩ p hp j hj hq fz1_130_84 fz2_130_84
  · exact match_zero_fix ⟨131, by decide⟩ ⟨84, by decide⟩ p hp j hj hq fz1_131_84 fz2_131_84
  · exact match_zero_fix ⟨132, by decide⟩ ⟨84, by decide⟩ p hp j hj hq fz1_132_84 fz2_132_84
  · exact match_zero_fix ⟨133, by decide⟩ ⟨84, by decide⟩ p hp j hj hq fz1_133_84 fz2_133_84
  · exact match_zero_fix ⟨134, by decide⟩ ⟨84, by decide⟩ p hp j hj hq fz1_134_84 fz2_134_84
  · exact match_zero_fix ⟨135, by decide⟩ ⟨84, by decide⟩ p hp j hj hq fz1_135_84 fz2_135_84
  · exact pair_136_84 p hp hrep j hj hq
  · exact pair_137_84 p hp hrep j hj hq
  · exact pair_138_84 p hp hrep j hj hq
  · exact pair_139_84 p hp hrep j hj hq
  · exact pair_140_84 p hp hrep j hj hq
  · exact pair_141_84 p hp hrep j hj hq
  · exact match_zero_fix ⟨142, by decide⟩ ⟨84, by decide⟩ p hp j hj hq fz1_142_84 fz2_142_84
  · exact match_zero_fix ⟨143, by decide⟩ ⟨84, by decide⟩ p hp j hj hq fz1_143_84 fz2_143_84
  · exact match_zero_fix ⟨144, by decide⟩ ⟨84, by decide⟩ p hp j hj hq fz1_144_84 fz2_144_84
  · exact match_zero_fix ⟨145, by decide⟩ ⟨84, by decide⟩ p hp j hj hq fz1_145_84 fz2_145_84
  · exact match_zero_fix ⟨146, by decide⟩ ⟨84, by decide⟩ p hp j hj hq fz1_146_84 fz2_146_84
  · exact pair_147_84 p hp hrep j hj hq

theorem master_85 (p : Nat) (hp : p < (Q2.transData.getD 85 []).length)
    (hrep : (Q2.cosetIsRep.getD 85 []).getD p false = true)
    (rK : Fin 148) (j : Nat) (hj : j < (repChars.getD rK.val []).length)
    (hq : (normIsRep.getD rK.val []).getD j false = true) :
    species (Q2.reps (⟨85, by decide⟩ : Fin 148)) (colE2 ⟨85, by decide⟩ p hp)
        (rowE2 rK j hj hq)
      = species (reps (⟨85, by decide⟩ : Fin 148))
        (colE1 ⟨85, by decide⟩ p (transLenTr ⟨85, by decide⟩ p hp)) (rowE1 rK j hj) := by
  rcases rK with ⟨nK, hnK⟩; interval_cases nK
  · exact match_zero_len ⟨0, by decide⟩ ⟨85, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨1, by decide⟩ ⟨85, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨2, by decide⟩ ⟨85, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨3, by decide⟩ ⟨85, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨4, by decide⟩ ⟨85, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨5, by decide⟩ ⟨85, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨6, by decide⟩ ⟨85, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨7, by decide⟩ ⟨85, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨8, by decide⟩ ⟨85, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨9, by decide⟩ ⟨85, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨10, by decide⟩ ⟨85, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨11, by decide⟩ ⟨85, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨12, by decide⟩ ⟨85, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨13, by decide⟩ ⟨85, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨14, by decide⟩ ⟨85, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨15, by decide⟩ ⟨85, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨16, by decide⟩ ⟨85, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨17, by decide⟩ ⟨85, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨18, by decide⟩ ⟨85, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨19, by decide⟩ ⟨85, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨20, by decide⟩ ⟨85, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨21, by decide⟩ ⟨85, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨22, by decide⟩ ⟨85, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨23, by decide⟩ ⟨85, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨24, by decide⟩ ⟨85, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨25, by decide⟩ ⟨85, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨26, by decide⟩ ⟨85, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨27, by decide⟩ ⟨85, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨28, by decide⟩ ⟨85, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨29, by decide⟩ ⟨85, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨30, by decide⟩ ⟨85, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨31, by decide⟩ ⟨85, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨32, by decide⟩ ⟨85, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨33, by decide⟩ ⟨85, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨34, by decide⟩ ⟨85, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨35, by decide⟩ ⟨85, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨36, by decide⟩ ⟨85, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨37, by decide⟩ ⟨85, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨38, by decide⟩ ⟨85, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨39, by decide⟩ ⟨85, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨40, by decide⟩ ⟨85, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨41, by decide⟩ ⟨85, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨42, by decide⟩ ⟨85, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨43, by decide⟩ ⟨85, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨44, by decide⟩ ⟨85, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨45, by decide⟩ ⟨85, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨46, by decide⟩ ⟨85, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨47, by decide⟩ ⟨85, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨48, by decide⟩ ⟨85, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨49, by decide⟩ ⟨85, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨50, by decide⟩ ⟨85, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨51, by decide⟩ ⟨85, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨52, by decide⟩ ⟨85, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨53, by decide⟩ ⟨85, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨54, by decide⟩ ⟨85, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_fix ⟨55, by decide⟩ ⟨85, by decide⟩ p hp j hj hq fz1_55_85 fz2_55_85
  · exact match_zero_fix ⟨56, by decide⟩ ⟨85, by decide⟩ p hp j hj hq fz1_56_85 fz2_56_85
  · exact match_zero_fix ⟨57, by decide⟩ ⟨85, by decide⟩ p hp j hj hq fz1_57_85 fz2_57_85
  · exact match_zero_fix ⟨58, by decide⟩ ⟨85, by decide⟩ p hp j hj hq fz1_58_85 fz2_58_85
  · exact match_zero_fix ⟨59, by decide⟩ ⟨85, by decide⟩ p hp j hj hq fz1_59_85 fz2_59_85
  · exact match_zero_fix ⟨60, by decide⟩ ⟨85, by decide⟩ p hp j hj hq fz1_60_85 fz2_60_85
  · exact match_zero_fix ⟨61, by decide⟩ ⟨85, by decide⟩ p hp j hj hq fz1_61_85 fz2_61_85
  · exact match_zero_fix ⟨62, by decide⟩ ⟨85, by decide⟩ p hp j hj hq fz1_62_85 fz2_62_85
  · exact match_zero_fix ⟨63, by decide⟩ ⟨85, by decide⟩ p hp j hj hq fz1_63_85 fz2_63_85
  · exact match_zero_fix ⟨64, by decide⟩ ⟨85, by decide⟩ p hp j hj hq fz1_64_85 fz2_64_85
  · exact match_zero_fix ⟨65, by decide⟩ ⟨85, by decide⟩ p hp j hj hq fz1_65_85 fz2_65_85
  · exact match_zero_fix ⟨66, by decide⟩ ⟨85, by decide⟩ p hp j hj hq fz1_66_85 fz2_66_85
  · exact match_zero_fix ⟨67, by decide⟩ ⟨85, by decide⟩ p hp j hj hq fz1_67_85 fz2_67_85
  · exact match_zero_fix ⟨68, by decide⟩ ⟨85, by decide⟩ p hp j hj hq fz1_68_85 fz2_68_85
  · exact match_zero_fix ⟨69, by decide⟩ ⟨85, by decide⟩ p hp j hj hq fz1_69_85 fz2_69_85
  · exact match_zero_fix ⟨70, by decide⟩ ⟨85, by decide⟩ p hp j hj hq fz1_70_85 fz2_70_85
  · exact match_zero_fix ⟨71, by decide⟩ ⟨85, by decide⟩ p hp j hj hq fz1_71_85 fz2_71_85
  · exact match_zero_fix ⟨72, by decide⟩ ⟨85, by decide⟩ p hp j hj hq fz1_72_85 fz2_72_85
  · exact match_zero_fix ⟨73, by decide⟩ ⟨85, by decide⟩ p hp j hj hq fz1_73_85 fz2_73_85
  · exact match_zero_fix ⟨74, by decide⟩ ⟨85, by decide⟩ p hp j hj hq fz1_74_85 fz2_74_85
  · exact match_zero_fix ⟨75, by decide⟩ ⟨85, by decide⟩ p hp j hj hq fz1_75_85 fz2_75_85
  · exact match_zero_fix ⟨76, by decide⟩ ⟨85, by decide⟩ p hp j hj hq fz1_76_85 fz2_76_85
  · exact match_zero_fix ⟨77, by decide⟩ ⟨85, by decide⟩ p hp j hj hq fz1_77_85 fz2_77_85
  · exact match_zero_fix ⟨78, by decide⟩ ⟨85, by decide⟩ p hp j hj hq fz1_78_85 fz2_78_85
  · exact match_zero_fix ⟨79, by decide⟩ ⟨85, by decide⟩ p hp j hj hq fz1_79_85 fz2_79_85
  · exact match_zero_fix ⟨80, by decide⟩ ⟨85, by decide⟩ p hp j hj hq fz1_80_85 fz2_80_85
  · exact match_zero_fix ⟨81, by decide⟩ ⟨85, by decide⟩ p hp j hj hq fz1_81_85 fz2_81_85
  · exact match_zero_fix ⟨82, by decide⟩ ⟨85, by decide⟩ p hp j hj hq fz1_82_85 fz2_82_85
  · exact match_zero_fix ⟨83, by decide⟩ ⟨85, by decide⟩ p hp j hj hq fz1_83_85 fz2_83_85
  · exact match_zero_fix ⟨84, by decide⟩ ⟨85, by decide⟩ p hp j hj hq fz1_84_85 fz2_84_85
  · exact pair_85_85 p hp hrep j hj hq
  · exact match_zero_fix ⟨86, by decide⟩ ⟨85, by decide⟩ p hp j hj hq fz1_86_85 fz2_86_85
  · exact match_zero_fix ⟨87, by decide⟩ ⟨85, by decide⟩ p hp j hj hq fz1_87_85 fz2_87_85
  · exact match_zero_fix ⟨88, by decide⟩ ⟨85, by decide⟩ p hp j hj hq fz1_88_85 fz2_88_85
  · exact match_zero_fix ⟨89, by decide⟩ ⟨85, by decide⟩ p hp j hj hq fz1_89_85 fz2_89_85
  · exact match_zero_fix ⟨90, by decide⟩ ⟨85, by decide⟩ p hp j hj hq fz1_90_85 fz2_90_85
  · exact match_zero_fix ⟨91, by decide⟩ ⟨85, by decide⟩ p hp j hj hq fz1_91_85 fz2_91_85
  · exact match_zero_fix ⟨92, by decide⟩ ⟨85, by decide⟩ p hp j hj hq fz1_92_85 fz2_92_85
  · exact match_zero_fix ⟨93, by decide⟩ ⟨85, by decide⟩ p hp j hj hq fz1_93_85 fz2_93_85
  · exact match_zero_fix ⟨94, by decide⟩ ⟨85, by decide⟩ p hp j hj hq fz1_94_85 fz2_94_85
  · exact match_zero_fix ⟨95, by decide⟩ ⟨85, by decide⟩ p hp j hj hq fz1_95_85 fz2_95_85
  · exact match_zero_fix ⟨96, by decide⟩ ⟨85, by decide⟩ p hp j hj hq fz1_96_85 fz2_96_85
  · exact match_zero_fix ⟨97, by decide⟩ ⟨85, by decide⟩ p hp j hj hq fz1_97_85 fz2_97_85
  · exact match_zero_fix ⟨98, by decide⟩ ⟨85, by decide⟩ p hp j hj hq fz1_98_85 fz2_98_85
  · exact match_zero_fix ⟨99, by decide⟩ ⟨85, by decide⟩ p hp j hj hq fz1_99_85 fz2_99_85
  · exact match_zero_fix ⟨100, by decide⟩ ⟨85, by decide⟩ p hp j hj hq fz1_100_85 fz2_100_85
  · exact match_zero_fix ⟨101, by decide⟩ ⟨85, by decide⟩ p hp j hj hq fz1_101_85 fz2_101_85
  · exact match_zero_fix ⟨102, by decide⟩ ⟨85, by decide⟩ p hp j hj hq fz1_102_85 fz2_102_85
  · exact match_zero_fix ⟨103, by decide⟩ ⟨85, by decide⟩ p hp j hj hq fz1_103_85 fz2_103_85
  · exact match_zero_fix ⟨104, by decide⟩ ⟨85, by decide⟩ p hp j hj hq fz1_104_85 fz2_104_85
  · exact match_zero_fix ⟨105, by decide⟩ ⟨85, by decide⟩ p hp j hj hq fz1_105_85 fz2_105_85
  · exact match_zero_fix ⟨106, by decide⟩ ⟨85, by decide⟩ p hp j hj hq fz1_106_85 fz2_106_85
  · exact match_zero_fix ⟨107, by decide⟩ ⟨85, by decide⟩ p hp j hj hq fz1_107_85 fz2_107_85
  · exact match_zero_fix ⟨108, by decide⟩ ⟨85, by decide⟩ p hp j hj hq fz1_108_85 fz2_108_85
  · exact match_zero_fix ⟨109, by decide⟩ ⟨85, by decide⟩ p hp j hj hq fz1_109_85 fz2_109_85
  · exact match_zero_fix ⟨110, by decide⟩ ⟨85, by decide⟩ p hp j hj hq fz1_110_85 fz2_110_85
  · exact match_zero_fix ⟨111, by decide⟩ ⟨85, by decide⟩ p hp j hj hq fz1_111_85 fz2_111_85
  · exact match_zero_fix ⟨112, by decide⟩ ⟨85, by decide⟩ p hp j hj hq fz1_112_85 fz2_112_85
  · exact match_zero_fix ⟨113, by decide⟩ ⟨85, by decide⟩ p hp j hj hq fz1_113_85 fz2_113_85
  · exact match_zero_fix ⟨114, by decide⟩ ⟨85, by decide⟩ p hp j hj hq fz1_114_85 fz2_114_85
  · exact match_zero_fix ⟨115, by decide⟩ ⟨85, by decide⟩ p hp j hj hq fz1_115_85 fz2_115_85
  · exact match_zero_fix ⟨116, by decide⟩ ⟨85, by decide⟩ p hp j hj hq fz1_116_85 fz2_116_85
  · exact match_zero_fix ⟨117, by decide⟩ ⟨85, by decide⟩ p hp j hj hq fz1_117_85 fz2_117_85
  · exact match_zero_fix ⟨118, by decide⟩ ⟨85, by decide⟩ p hp j hj hq fz1_118_85 fz2_118_85
  · exact match_zero_fix ⟨119, by decide⟩ ⟨85, by decide⟩ p hp j hj hq fz1_119_85 fz2_119_85
  · exact match_zero_fix ⟨120, by decide⟩ ⟨85, by decide⟩ p hp j hj hq fz1_120_85 fz2_120_85
  · exact match_zero_fix ⟨121, by decide⟩ ⟨85, by decide⟩ p hp j hj hq fz1_121_85 fz2_121_85
  · exact match_zero_fix ⟨122, by decide⟩ ⟨85, by decide⟩ p hp j hj hq fz1_122_85 fz2_122_85
  · exact match_zero_fix ⟨123, by decide⟩ ⟨85, by decide⟩ p hp j hj hq fz1_123_85 fz2_123_85
  · exact match_zero_fix ⟨124, by decide⟩ ⟨85, by decide⟩ p hp j hj hq fz1_124_85 fz2_124_85
  · exact match_zero_fix ⟨125, by decide⟩ ⟨85, by decide⟩ p hp j hj hq fz1_125_85 fz2_125_85
  · exact match_zero_fix ⟨126, by decide⟩ ⟨85, by decide⟩ p hp j hj hq fz1_126_85 fz2_126_85
  · exact match_zero_fix ⟨127, by decide⟩ ⟨85, by decide⟩ p hp j hj hq fz1_127_85 fz2_127_85
  · exact match_zero_fix ⟨128, by decide⟩ ⟨85, by decide⟩ p hp j hj hq fz1_128_85 fz2_128_85
  · exact match_zero_fix ⟨129, by decide⟩ ⟨85, by decide⟩ p hp j hj hq fz1_129_85 fz2_129_85
  · exact match_zero_fix ⟨130, by decide⟩ ⟨85, by decide⟩ p hp j hj hq fz1_130_85 fz2_130_85
  · exact match_zero_fix ⟨131, by decide⟩ ⟨85, by decide⟩ p hp j hj hq fz1_131_85 fz2_131_85
  · exact match_zero_fix ⟨132, by decide⟩ ⟨85, by decide⟩ p hp j hj hq fz1_132_85 fz2_132_85
  · exact match_zero_fix ⟨133, by decide⟩ ⟨85, by decide⟩ p hp j hj hq fz1_133_85 fz2_133_85
  · exact match_zero_fix ⟨134, by decide⟩ ⟨85, by decide⟩ p hp j hj hq fz1_134_85 fz2_134_85
  · exact match_zero_fix ⟨135, by decide⟩ ⟨85, by decide⟩ p hp j hj hq fz1_135_85 fz2_135_85
  · exact match_zero_fix ⟨136, by decide⟩ ⟨85, by decide⟩ p hp j hj hq fz1_136_85 fz2_136_85
  · exact match_zero_fix ⟨137, by decide⟩ ⟨85, by decide⟩ p hp j hj hq fz1_137_85 fz2_137_85
  · exact match_zero_fix ⟨138, by decide⟩ ⟨85, by decide⟩ p hp j hj hq fz1_138_85 fz2_138_85
  · exact match_zero_fix ⟨139, by decide⟩ ⟨85, by decide⟩ p hp j hj hq fz1_139_85 fz2_139_85
  · exact match_zero_fix ⟨140, by decide⟩ ⟨85, by decide⟩ p hp j hj hq fz1_140_85 fz2_140_85
  · exact pair_141_85 p hp hrep j hj hq
  · exact match_zero_fix ⟨142, by decide⟩ ⟨85, by decide⟩ p hp j hj hq fz1_142_85 fz2_142_85
  · exact match_zero_fix ⟨143, by decide⟩ ⟨85, by decide⟩ p hp j hj hq fz1_143_85 fz2_143_85
  · exact match_zero_fix ⟨144, by decide⟩ ⟨85, by decide⟩ p hp j hj hq fz1_144_85 fz2_144_85
  · exact match_zero_fix ⟨145, by decide⟩ ⟨85, by decide⟩ p hp j hj hq fz1_145_85 fz2_145_85
  · exact match_zero_fix ⟨146, by decide⟩ ⟨85, by decide⟩ p hp j hj hq fz1_146_85 fz2_146_85
  · exact pair_147_85 p hp hrep j hj hq

theorem master_86 (p : Nat) (hp : p < (Q2.transData.getD 86 []).length)
    (hrep : (Q2.cosetIsRep.getD 86 []).getD p false = true)
    (rK : Fin 148) (j : Nat) (hj : j < (repChars.getD rK.val []).length)
    (hq : (normIsRep.getD rK.val []).getD j false = true) :
    species (Q2.reps (⟨86, by decide⟩ : Fin 148)) (colE2 ⟨86, by decide⟩ p hp)
        (rowE2 rK j hj hq)
      = species (reps (⟨86, by decide⟩ : Fin 148))
        (colE1 ⟨86, by decide⟩ p (transLenTr ⟨86, by decide⟩ p hp)) (rowE1 rK j hj) := by
  rcases rK with ⟨nK, hnK⟩; interval_cases nK
  · exact match_zero_len ⟨0, by decide⟩ ⟨86, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨1, by decide⟩ ⟨86, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨2, by decide⟩ ⟨86, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨3, by decide⟩ ⟨86, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨4, by decide⟩ ⟨86, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨5, by decide⟩ ⟨86, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨6, by decide⟩ ⟨86, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨7, by decide⟩ ⟨86, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨8, by decide⟩ ⟨86, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨9, by decide⟩ ⟨86, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨10, by decide⟩ ⟨86, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨11, by decide⟩ ⟨86, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨12, by decide⟩ ⟨86, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨13, by decide⟩ ⟨86, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨14, by decide⟩ ⟨86, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨15, by decide⟩ ⟨86, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨16, by decide⟩ ⟨86, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨17, by decide⟩ ⟨86, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨18, by decide⟩ ⟨86, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨19, by decide⟩ ⟨86, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨20, by decide⟩ ⟨86, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨21, by decide⟩ ⟨86, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨22, by decide⟩ ⟨86, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨23, by decide⟩ ⟨86, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨24, by decide⟩ ⟨86, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨25, by decide⟩ ⟨86, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨26, by decide⟩ ⟨86, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨27, by decide⟩ ⟨86, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨28, by decide⟩ ⟨86, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨29, by decide⟩ ⟨86, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨30, by decide⟩ ⟨86, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨31, by decide⟩ ⟨86, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨32, by decide⟩ ⟨86, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨33, by decide⟩ ⟨86, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨34, by decide⟩ ⟨86, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨35, by decide⟩ ⟨86, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨36, by decide⟩ ⟨86, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨37, by decide⟩ ⟨86, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨38, by decide⟩ ⟨86, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨39, by decide⟩ ⟨86, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨40, by decide⟩ ⟨86, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨41, by decide⟩ ⟨86, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨42, by decide⟩ ⟨86, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨43, by decide⟩ ⟨86, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨44, by decide⟩ ⟨86, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨45, by decide⟩ ⟨86, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨46, by decide⟩ ⟨86, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨47, by decide⟩ ⟨86, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨48, by decide⟩ ⟨86, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨49, by decide⟩ ⟨86, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨50, by decide⟩ ⟨86, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨51, by decide⟩ ⟨86, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨52, by decide⟩ ⟨86, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨53, by decide⟩ ⟨86, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨54, by decide⟩ ⟨86, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_fix ⟨55, by decide⟩ ⟨86, by decide⟩ p hp j hj hq fz1_55_86 fz2_55_86
  · exact match_zero_fix ⟨56, by decide⟩ ⟨86, by decide⟩ p hp j hj hq fz1_56_86 fz2_56_86
  · exact match_zero_fix ⟨57, by decide⟩ ⟨86, by decide⟩ p hp j hj hq fz1_57_86 fz2_57_86
  · exact match_zero_fix ⟨58, by decide⟩ ⟨86, by decide⟩ p hp j hj hq fz1_58_86 fz2_58_86
  · exact match_zero_fix ⟨59, by decide⟩ ⟨86, by decide⟩ p hp j hj hq fz1_59_86 fz2_59_86
  · exact match_zero_fix ⟨60, by decide⟩ ⟨86, by decide⟩ p hp j hj hq fz1_60_86 fz2_60_86
  · exact match_zero_fix ⟨61, by decide⟩ ⟨86, by decide⟩ p hp j hj hq fz1_61_86 fz2_61_86
  · exact match_zero_fix ⟨62, by decide⟩ ⟨86, by decide⟩ p hp j hj hq fz1_62_86 fz2_62_86
  · exact match_zero_fix ⟨63, by decide⟩ ⟨86, by decide⟩ p hp j hj hq fz1_63_86 fz2_63_86
  · exact match_zero_fix ⟨64, by decide⟩ ⟨86, by decide⟩ p hp j hj hq fz1_64_86 fz2_64_86
  · exact match_zero_fix ⟨65, by decide⟩ ⟨86, by decide⟩ p hp j hj hq fz1_65_86 fz2_65_86
  · exact match_zero_fix ⟨66, by decide⟩ ⟨86, by decide⟩ p hp j hj hq fz1_66_86 fz2_66_86
  · exact match_zero_fix ⟨67, by decide⟩ ⟨86, by decide⟩ p hp j hj hq fz1_67_86 fz2_67_86
  · exact match_zero_fix ⟨68, by decide⟩ ⟨86, by decide⟩ p hp j hj hq fz1_68_86 fz2_68_86
  · exact match_zero_fix ⟨69, by decide⟩ ⟨86, by decide⟩ p hp j hj hq fz1_69_86 fz2_69_86
  · exact match_zero_fix ⟨70, by decide⟩ ⟨86, by decide⟩ p hp j hj hq fz1_70_86 fz2_70_86
  · exact match_zero_fix ⟨71, by decide⟩ ⟨86, by decide⟩ p hp j hj hq fz1_71_86 fz2_71_86
  · exact match_zero_fix ⟨72, by decide⟩ ⟨86, by decide⟩ p hp j hj hq fz1_72_86 fz2_72_86
  · exact match_zero_fix ⟨73, by decide⟩ ⟨86, by decide⟩ p hp j hj hq fz1_73_86 fz2_73_86
  · exact match_zero_fix ⟨74, by decide⟩ ⟨86, by decide⟩ p hp j hj hq fz1_74_86 fz2_74_86
  · exact match_zero_fix ⟨75, by decide⟩ ⟨86, by decide⟩ p hp j hj hq fz1_75_86 fz2_75_86
  · exact match_zero_fix ⟨76, by decide⟩ ⟨86, by decide⟩ p hp j hj hq fz1_76_86 fz2_76_86
  · exact match_zero_fix ⟨77, by decide⟩ ⟨86, by decide⟩ p hp j hj hq fz1_77_86 fz2_77_86
  · exact match_zero_fix ⟨78, by decide⟩ ⟨86, by decide⟩ p hp j hj hq fz1_78_86 fz2_78_86
  · exact match_zero_fix ⟨79, by decide⟩ ⟨86, by decide⟩ p hp j hj hq fz1_79_86 fz2_79_86
  · exact match_zero_fix ⟨80, by decide⟩ ⟨86, by decide⟩ p hp j hj hq fz1_80_86 fz2_80_86
  · exact match_zero_fix ⟨81, by decide⟩ ⟨86, by decide⟩ p hp j hj hq fz1_81_86 fz2_81_86
  · exact match_zero_fix ⟨82, by decide⟩ ⟨86, by decide⟩ p hp j hj hq fz1_82_86 fz2_82_86
  · exact match_zero_fix ⟨83, by decide⟩ ⟨86, by decide⟩ p hp j hj hq fz1_83_86 fz2_83_86
  · exact match_zero_fix ⟨84, by decide⟩ ⟨86, by decide⟩ p hp j hj hq fz1_84_86 fz2_84_86
  · exact match_zero_fix ⟨85, by decide⟩ ⟨86, by decide⟩ p hp j hj hq fz1_85_86 fz2_85_86
  · exact pair_86_86 p hp hrep j hj hq
  · exact match_zero_fix ⟨87, by decide⟩ ⟨86, by decide⟩ p hp j hj hq fz1_87_86 fz2_87_86
  · exact match_zero_fix ⟨88, by decide⟩ ⟨86, by decide⟩ p hp j hj hq fz1_88_86 fz2_88_86
  · exact match_zero_fix ⟨89, by decide⟩ ⟨86, by decide⟩ p hp j hj hq fz1_89_86 fz2_89_86
  · exact match_zero_fix ⟨90, by decide⟩ ⟨86, by decide⟩ p hp j hj hq fz1_90_86 fz2_90_86
  · exact match_zero_fix ⟨91, by decide⟩ ⟨86, by decide⟩ p hp j hj hq fz1_91_86 fz2_91_86
  · exact match_zero_fix ⟨92, by decide⟩ ⟨86, by decide⟩ p hp j hj hq fz1_92_86 fz2_92_86
  · exact match_zero_fix ⟨93, by decide⟩ ⟨86, by decide⟩ p hp j hj hq fz1_93_86 fz2_93_86
  · exact match_zero_fix ⟨94, by decide⟩ ⟨86, by decide⟩ p hp j hj hq fz1_94_86 fz2_94_86
  · exact match_zero_fix ⟨95, by decide⟩ ⟨86, by decide⟩ p hp j hj hq fz1_95_86 fz2_95_86
  · exact match_zero_fix ⟨96, by decide⟩ ⟨86, by decide⟩ p hp j hj hq fz1_96_86 fz2_96_86
  · exact match_zero_fix ⟨97, by decide⟩ ⟨86, by decide⟩ p hp j hj hq fz1_97_86 fz2_97_86
  · exact match_zero_fix ⟨98, by decide⟩ ⟨86, by decide⟩ p hp j hj hq fz1_98_86 fz2_98_86
  · exact match_zero_fix ⟨99, by decide⟩ ⟨86, by decide⟩ p hp j hj hq fz1_99_86 fz2_99_86
  · exact match_zero_fix ⟨100, by decide⟩ ⟨86, by decide⟩ p hp j hj hq fz1_100_86 fz2_100_86
  · exact match_zero_fix ⟨101, by decide⟩ ⟨86, by decide⟩ p hp j hj hq fz1_101_86 fz2_101_86
  · exact match_zero_fix ⟨102, by decide⟩ ⟨86, by decide⟩ p hp j hj hq fz1_102_86 fz2_102_86
  · exact match_zero_fix ⟨103, by decide⟩ ⟨86, by decide⟩ p hp j hj hq fz1_103_86 fz2_103_86
  · exact match_zero_fix ⟨104, by decide⟩ ⟨86, by decide⟩ p hp j hj hq fz1_104_86 fz2_104_86
  · exact match_zero_fix ⟨105, by decide⟩ ⟨86, by decide⟩ p hp j hj hq fz1_105_86 fz2_105_86
  · exact match_zero_fix ⟨106, by decide⟩ ⟨86, by decide⟩ p hp j hj hq fz1_106_86 fz2_106_86
  · exact match_zero_fix ⟨107, by decide⟩ ⟨86, by decide⟩ p hp j hj hq fz1_107_86 fz2_107_86
  · exact match_zero_fix ⟨108, by decide⟩ ⟨86, by decide⟩ p hp j hj hq fz1_108_86 fz2_108_86
  · exact match_zero_fix ⟨109, by decide⟩ ⟨86, by decide⟩ p hp j hj hq fz1_109_86 fz2_109_86
  · exact match_zero_fix ⟨110, by decide⟩ ⟨86, by decide⟩ p hp j hj hq fz1_110_86 fz2_110_86
  · exact match_zero_fix ⟨111, by decide⟩ ⟨86, by decide⟩ p hp j hj hq fz1_111_86 fz2_111_86
  · exact match_zero_fix ⟨112, by decide⟩ ⟨86, by decide⟩ p hp j hj hq fz1_112_86 fz2_112_86
  · exact match_zero_fix ⟨113, by decide⟩ ⟨86, by decide⟩ p hp j hj hq fz1_113_86 fz2_113_86
  · exact match_zero_fix ⟨114, by decide⟩ ⟨86, by decide⟩ p hp j hj hq fz1_114_86 fz2_114_86
  · exact match_zero_fix ⟨115, by decide⟩ ⟨86, by decide⟩ p hp j hj hq fz1_115_86 fz2_115_86
  · exact match_zero_fix ⟨116, by decide⟩ ⟨86, by decide⟩ p hp j hj hq fz1_116_86 fz2_116_86
  · exact match_zero_fix ⟨117, by decide⟩ ⟨86, by decide⟩ p hp j hj hq fz1_117_86 fz2_117_86
  · exact match_zero_fix ⟨118, by decide⟩ ⟨86, by decide⟩ p hp j hj hq fz1_118_86 fz2_118_86
  · exact match_zero_fix ⟨119, by decide⟩ ⟨86, by decide⟩ p hp j hj hq fz1_119_86 fz2_119_86
  · exact match_zero_fix ⟨120, by decide⟩ ⟨86, by decide⟩ p hp j hj hq fz1_120_86 fz2_120_86
  · exact match_zero_fix ⟨121, by decide⟩ ⟨86, by decide⟩ p hp j hj hq fz1_121_86 fz2_121_86
  · exact match_zero_fix ⟨122, by decide⟩ ⟨86, by decide⟩ p hp j hj hq fz1_122_86 fz2_122_86
  · exact match_zero_fix ⟨123, by decide⟩ ⟨86, by decide⟩ p hp j hj hq fz1_123_86 fz2_123_86
  · exact match_zero_fix ⟨124, by decide⟩ ⟨86, by decide⟩ p hp j hj hq fz1_124_86 fz2_124_86
  · exact match_zero_fix ⟨125, by decide⟩ ⟨86, by decide⟩ p hp j hj hq fz1_125_86 fz2_125_86
  · exact match_zero_fix ⟨126, by decide⟩ ⟨86, by decide⟩ p hp j hj hq fz1_126_86 fz2_126_86
  · exact match_zero_fix ⟨127, by decide⟩ ⟨86, by decide⟩ p hp j hj hq fz1_127_86 fz2_127_86
  · exact match_zero_fix ⟨128, by decide⟩ ⟨86, by decide⟩ p hp j hj hq fz1_128_86 fz2_128_86
  · exact match_zero_fix ⟨129, by decide⟩ ⟨86, by decide⟩ p hp j hj hq fz1_129_86 fz2_129_86
  · exact match_zero_fix ⟨130, by decide⟩ ⟨86, by decide⟩ p hp j hj hq fz1_130_86 fz2_130_86
  · exact match_zero_fix ⟨131, by decide⟩ ⟨86, by decide⟩ p hp j hj hq fz1_131_86 fz2_131_86
  · exact match_zero_fix ⟨132, by decide⟩ ⟨86, by decide⟩ p hp j hj hq fz1_132_86 fz2_132_86
  · exact match_zero_fix ⟨133, by decide⟩ ⟨86, by decide⟩ p hp j hj hq fz1_133_86 fz2_133_86
  · exact match_zero_fix ⟨134, by decide⟩ ⟨86, by decide⟩ p hp j hj hq fz1_134_86 fz2_134_86
  · exact match_zero_fix ⟨135, by decide⟩ ⟨86, by decide⟩ p hp j hj hq fz1_135_86 fz2_135_86
  · exact match_zero_fix ⟨136, by decide⟩ ⟨86, by decide⟩ p hp j hj hq fz1_136_86 fz2_136_86
  · exact match_zero_fix ⟨137, by decide⟩ ⟨86, by decide⟩ p hp j hj hq fz1_137_86 fz2_137_86
  · exact match_zero_fix ⟨138, by decide⟩ ⟨86, by decide⟩ p hp j hj hq fz1_138_86 fz2_138_86
  · exact match_zero_fix ⟨139, by decide⟩ ⟨86, by decide⟩ p hp j hj hq fz1_139_86 fz2_139_86
  · exact match_zero_fix ⟨140, by decide⟩ ⟨86, by decide⟩ p hp j hj hq fz1_140_86 fz2_140_86
  · exact pair_141_86 p hp hrep j hj hq
  · exact match_zero_fix ⟨142, by decide⟩ ⟨86, by decide⟩ p hp j hj hq fz1_142_86 fz2_142_86
  · exact match_zero_fix ⟨143, by decide⟩ ⟨86, by decide⟩ p hp j hj hq fz1_143_86 fz2_143_86
  · exact match_zero_fix ⟨144, by decide⟩ ⟨86, by decide⟩ p hp j hj hq fz1_144_86 fz2_144_86
  · exact match_zero_fix ⟨145, by decide⟩ ⟨86, by decide⟩ p hp j hj hq fz1_145_86 fz2_145_86
  · exact match_zero_fix ⟨146, by decide⟩ ⟨86, by decide⟩ p hp j hj hq fz1_146_86 fz2_146_86
  · exact pair_147_86 p hp hrep j hj hq

theorem master_87 (p : Nat) (hp : p < (Q2.transData.getD 87 []).length)
    (hrep : (Q2.cosetIsRep.getD 87 []).getD p false = true)
    (rK : Fin 148) (j : Nat) (hj : j < (repChars.getD rK.val []).length)
    (hq : (normIsRep.getD rK.val []).getD j false = true) :
    species (Q2.reps (⟨87, by decide⟩ : Fin 148)) (colE2 ⟨87, by decide⟩ p hp)
        (rowE2 rK j hj hq)
      = species (reps (⟨87, by decide⟩ : Fin 148))
        (colE1 ⟨87, by decide⟩ p (transLenTr ⟨87, by decide⟩ p hp)) (rowE1 rK j hj) := by
  rcases rK with ⟨nK, hnK⟩; interval_cases nK
  · exact match_zero_len ⟨0, by decide⟩ ⟨87, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨1, by decide⟩ ⟨87, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨2, by decide⟩ ⟨87, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨3, by decide⟩ ⟨87, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨4, by decide⟩ ⟨87, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨5, by decide⟩ ⟨87, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨6, by decide⟩ ⟨87, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨7, by decide⟩ ⟨87, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨8, by decide⟩ ⟨87, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨9, by decide⟩ ⟨87, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨10, by decide⟩ ⟨87, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨11, by decide⟩ ⟨87, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨12, by decide⟩ ⟨87, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨13, by decide⟩ ⟨87, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨14, by decide⟩ ⟨87, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨15, by decide⟩ ⟨87, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨16, by decide⟩ ⟨87, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨17, by decide⟩ ⟨87, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨18, by decide⟩ ⟨87, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨19, by decide⟩ ⟨87, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨20, by decide⟩ ⟨87, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨21, by decide⟩ ⟨87, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨22, by decide⟩ ⟨87, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨23, by decide⟩ ⟨87, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨24, by decide⟩ ⟨87, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨25, by decide⟩ ⟨87, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨26, by decide⟩ ⟨87, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨27, by decide⟩ ⟨87, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨28, by decide⟩ ⟨87, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨29, by decide⟩ ⟨87, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨30, by decide⟩ ⟨87, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨31, by decide⟩ ⟨87, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨32, by decide⟩ ⟨87, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨33, by decide⟩ ⟨87, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨34, by decide⟩ ⟨87, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨35, by decide⟩ ⟨87, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨36, by decide⟩ ⟨87, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨37, by decide⟩ ⟨87, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨38, by decide⟩ ⟨87, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨39, by decide⟩ ⟨87, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨40, by decide⟩ ⟨87, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨41, by decide⟩ ⟨87, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨42, by decide⟩ ⟨87, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨43, by decide⟩ ⟨87, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨44, by decide⟩ ⟨87, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨45, by decide⟩ ⟨87, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨46, by decide⟩ ⟨87, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨47, by decide⟩ ⟨87, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨48, by decide⟩ ⟨87, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨49, by decide⟩ ⟨87, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨50, by decide⟩ ⟨87, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨51, by decide⟩ ⟨87, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨52, by decide⟩ ⟨87, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨53, by decide⟩ ⟨87, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨54, by decide⟩ ⟨87, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_fix ⟨55, by decide⟩ ⟨87, by decide⟩ p hp j hj hq fz1_55_87 fz2_55_87
  · exact match_zero_fix ⟨56, by decide⟩ ⟨87, by decide⟩ p hp j hj hq fz1_56_87 fz2_56_87
  · exact match_zero_fix ⟨57, by decide⟩ ⟨87, by decide⟩ p hp j hj hq fz1_57_87 fz2_57_87
  · exact match_zero_fix ⟨58, by decide⟩ ⟨87, by decide⟩ p hp j hj hq fz1_58_87 fz2_58_87
  · exact match_zero_fix ⟨59, by decide⟩ ⟨87, by decide⟩ p hp j hj hq fz1_59_87 fz2_59_87
  · exact match_zero_fix ⟨60, by decide⟩ ⟨87, by decide⟩ p hp j hj hq fz1_60_87 fz2_60_87
  · exact match_zero_fix ⟨61, by decide⟩ ⟨87, by decide⟩ p hp j hj hq fz1_61_87 fz2_61_87
  · exact match_zero_fix ⟨62, by decide⟩ ⟨87, by decide⟩ p hp j hj hq fz1_62_87 fz2_62_87
  · exact match_zero_fix ⟨63, by decide⟩ ⟨87, by decide⟩ p hp j hj hq fz1_63_87 fz2_63_87
  · exact match_zero_fix ⟨64, by decide⟩ ⟨87, by decide⟩ p hp j hj hq fz1_64_87 fz2_64_87
  · exact match_zero_fix ⟨65, by decide⟩ ⟨87, by decide⟩ p hp j hj hq fz1_65_87 fz2_65_87
  · exact match_zero_fix ⟨66, by decide⟩ ⟨87, by decide⟩ p hp j hj hq fz1_66_87 fz2_66_87
  · exact match_zero_fix ⟨67, by decide⟩ ⟨87, by decide⟩ p hp j hj hq fz1_67_87 fz2_67_87
  · exact match_zero_fix ⟨68, by decide⟩ ⟨87, by decide⟩ p hp j hj hq fz1_68_87 fz2_68_87
  · exact match_zero_fix ⟨69, by decide⟩ ⟨87, by decide⟩ p hp j hj hq fz1_69_87 fz2_69_87
  · exact match_zero_fix ⟨70, by decide⟩ ⟨87, by decide⟩ p hp j hj hq fz1_70_87 fz2_70_87
  · exact match_zero_fix ⟨71, by decide⟩ ⟨87, by decide⟩ p hp j hj hq fz1_71_87 fz2_71_87
  · exact match_zero_fix ⟨72, by decide⟩ ⟨87, by decide⟩ p hp j hj hq fz1_72_87 fz2_72_87
  · exact match_zero_fix ⟨73, by decide⟩ ⟨87, by decide⟩ p hp j hj hq fz1_73_87 fz2_73_87
  · exact match_zero_fix ⟨74, by decide⟩ ⟨87, by decide⟩ p hp j hj hq fz1_74_87 fz2_74_87
  · exact match_zero_fix ⟨75, by decide⟩ ⟨87, by decide⟩ p hp j hj hq fz1_75_87 fz2_75_87
  · exact match_zero_fix ⟨76, by decide⟩ ⟨87, by decide⟩ p hp j hj hq fz1_76_87 fz2_76_87
  · exact match_zero_fix ⟨77, by decide⟩ ⟨87, by decide⟩ p hp j hj hq fz1_77_87 fz2_77_87
  · exact match_zero_fix ⟨78, by decide⟩ ⟨87, by decide⟩ p hp j hj hq fz1_78_87 fz2_78_87
  · exact match_zero_fix ⟨79, by decide⟩ ⟨87, by decide⟩ p hp j hj hq fz1_79_87 fz2_79_87
  · exact match_zero_fix ⟨80, by decide⟩ ⟨87, by decide⟩ p hp j hj hq fz1_80_87 fz2_80_87
  · exact match_zero_fix ⟨81, by decide⟩ ⟨87, by decide⟩ p hp j hj hq fz1_81_87 fz2_81_87
  · exact match_zero_fix ⟨82, by decide⟩ ⟨87, by decide⟩ p hp j hj hq fz1_82_87 fz2_82_87
  · exact match_zero_fix ⟨83, by decide⟩ ⟨87, by decide⟩ p hp j hj hq fz1_83_87 fz2_83_87
  · exact match_zero_fix ⟨84, by decide⟩ ⟨87, by decide⟩ p hp j hj hq fz1_84_87 fz2_84_87
  · exact match_zero_fix ⟨85, by decide⟩ ⟨87, by decide⟩ p hp j hj hq fz1_85_87 fz2_85_87
  · exact match_zero_fix ⟨86, by decide⟩ ⟨87, by decide⟩ p hp j hj hq fz1_86_87 fz2_86_87
  · exact pair_87_87 p hp hrep j hj hq
  · exact match_zero_fix ⟨88, by decide⟩ ⟨87, by decide⟩ p hp j hj hq fz1_88_87 fz2_88_87
  · exact match_zero_fix ⟨89, by decide⟩ ⟨87, by decide⟩ p hp j hj hq fz1_89_87 fz2_89_87
  · exact match_zero_fix ⟨90, by decide⟩ ⟨87, by decide⟩ p hp j hj hq fz1_90_87 fz2_90_87
  · exact match_zero_fix ⟨91, by decide⟩ ⟨87, by decide⟩ p hp j hj hq fz1_91_87 fz2_91_87
  · exact match_zero_fix ⟨92, by decide⟩ ⟨87, by decide⟩ p hp j hj hq fz1_92_87 fz2_92_87
  · exact match_zero_fix ⟨93, by decide⟩ ⟨87, by decide⟩ p hp j hj hq fz1_93_87 fz2_93_87
  · exact match_zero_fix ⟨94, by decide⟩ ⟨87, by decide⟩ p hp j hj hq fz1_94_87 fz2_94_87
  · exact match_zero_fix ⟨95, by decide⟩ ⟨87, by decide⟩ p hp j hj hq fz1_95_87 fz2_95_87
  · exact match_zero_fix ⟨96, by decide⟩ ⟨87, by decide⟩ p hp j hj hq fz1_96_87 fz2_96_87
  · exact match_zero_fix ⟨97, by decide⟩ ⟨87, by decide⟩ p hp j hj hq fz1_97_87 fz2_97_87
  · exact match_zero_fix ⟨98, by decide⟩ ⟨87, by decide⟩ p hp j hj hq fz1_98_87 fz2_98_87
  · exact match_zero_fix ⟨99, by decide⟩ ⟨87, by decide⟩ p hp j hj hq fz1_99_87 fz2_99_87
  · exact match_zero_fix ⟨100, by decide⟩ ⟨87, by decide⟩ p hp j hj hq fz1_100_87 fz2_100_87
  · exact match_zero_fix ⟨101, by decide⟩ ⟨87, by decide⟩ p hp j hj hq fz1_101_87 fz2_101_87
  · exact match_zero_fix ⟨102, by decide⟩ ⟨87, by decide⟩ p hp j hj hq fz1_102_87 fz2_102_87
  · exact match_zero_fix ⟨103, by decide⟩ ⟨87, by decide⟩ p hp j hj hq fz1_103_87 fz2_103_87
  · exact match_zero_fix ⟨104, by decide⟩ ⟨87, by decide⟩ p hp j hj hq fz1_104_87 fz2_104_87
  · exact match_zero_fix ⟨105, by decide⟩ ⟨87, by decide⟩ p hp j hj hq fz1_105_87 fz2_105_87
  · exact match_zero_fix ⟨106, by decide⟩ ⟨87, by decide⟩ p hp j hj hq fz1_106_87 fz2_106_87
  · exact match_zero_fix ⟨107, by decide⟩ ⟨87, by decide⟩ p hp j hj hq fz1_107_87 fz2_107_87
  · exact match_zero_fix ⟨108, by decide⟩ ⟨87, by decide⟩ p hp j hj hq fz1_108_87 fz2_108_87
  · exact match_zero_fix ⟨109, by decide⟩ ⟨87, by decide⟩ p hp j hj hq fz1_109_87 fz2_109_87
  · exact match_zero_fix ⟨110, by decide⟩ ⟨87, by decide⟩ p hp j hj hq fz1_110_87 fz2_110_87
  · exact match_zero_fix ⟨111, by decide⟩ ⟨87, by decide⟩ p hp j hj hq fz1_111_87 fz2_111_87
  · exact match_zero_fix ⟨112, by decide⟩ ⟨87, by decide⟩ p hp j hj hq fz1_112_87 fz2_112_87
  · exact match_zero_fix ⟨113, by decide⟩ ⟨87, by decide⟩ p hp j hj hq fz1_113_87 fz2_113_87
  · exact match_zero_fix ⟨114, by decide⟩ ⟨87, by decide⟩ p hp j hj hq fz1_114_87 fz2_114_87
  · exact match_zero_fix ⟨115, by decide⟩ ⟨87, by decide⟩ p hp j hj hq fz1_115_87 fz2_115_87
  · exact match_zero_fix ⟨116, by decide⟩ ⟨87, by decide⟩ p hp j hj hq fz1_116_87 fz2_116_87
  · exact match_zero_fix ⟨117, by decide⟩ ⟨87, by decide⟩ p hp j hj hq fz1_117_87 fz2_117_87
  · exact match_zero_fix ⟨118, by decide⟩ ⟨87, by decide⟩ p hp j hj hq fz1_118_87 fz2_118_87
  · exact match_zero_fix ⟨119, by decide⟩ ⟨87, by decide⟩ p hp j hj hq fz1_119_87 fz2_119_87
  · exact match_zero_fix ⟨120, by decide⟩ ⟨87, by decide⟩ p hp j hj hq fz1_120_87 fz2_120_87
  · exact match_zero_fix ⟨121, by decide⟩ ⟨87, by decide⟩ p hp j hj hq fz1_121_87 fz2_121_87
  · exact match_zero_fix ⟨122, by decide⟩ ⟨87, by decide⟩ p hp j hj hq fz1_122_87 fz2_122_87
  · exact match_zero_fix ⟨123, by decide⟩ ⟨87, by decide⟩ p hp j hj hq fz1_123_87 fz2_123_87
  · exact match_zero_fix ⟨124, by decide⟩ ⟨87, by decide⟩ p hp j hj hq fz1_124_87 fz2_124_87
  · exact match_zero_fix ⟨125, by decide⟩ ⟨87, by decide⟩ p hp j hj hq fz1_125_87 fz2_125_87
  · exact match_zero_fix ⟨126, by decide⟩ ⟨87, by decide⟩ p hp j hj hq fz1_126_87 fz2_126_87
  · exact match_zero_fix ⟨127, by decide⟩ ⟨87, by decide⟩ p hp j hj hq fz1_127_87 fz2_127_87
  · exact match_zero_fix ⟨128, by decide⟩ ⟨87, by decide⟩ p hp j hj hq fz1_128_87 fz2_128_87
  · exact match_zero_fix ⟨129, by decide⟩ ⟨87, by decide⟩ p hp j hj hq fz1_129_87 fz2_129_87
  · exact match_zero_fix ⟨130, by decide⟩ ⟨87, by decide⟩ p hp j hj hq fz1_130_87 fz2_130_87
  · exact match_zero_fix ⟨131, by decide⟩ ⟨87, by decide⟩ p hp j hj hq fz1_131_87 fz2_131_87
  · exact match_zero_fix ⟨132, by decide⟩ ⟨87, by decide⟩ p hp j hj hq fz1_132_87 fz2_132_87
  · exact match_zero_fix ⟨133, by decide⟩ ⟨87, by decide⟩ p hp j hj hq fz1_133_87 fz2_133_87
  · exact match_zero_fix ⟨134, by decide⟩ ⟨87, by decide⟩ p hp j hj hq fz1_134_87 fz2_134_87
  · exact match_zero_fix ⟨135, by decide⟩ ⟨87, by decide⟩ p hp j hj hq fz1_135_87 fz2_135_87
  · exact match_zero_fix ⟨136, by decide⟩ ⟨87, by decide⟩ p hp j hj hq fz1_136_87 fz2_136_87
  · exact match_zero_fix ⟨137, by decide⟩ ⟨87, by decide⟩ p hp j hj hq fz1_137_87 fz2_137_87
  · exact match_zero_fix ⟨138, by decide⟩ ⟨87, by decide⟩ p hp j hj hq fz1_138_87 fz2_138_87
  · exact match_zero_fix ⟨139, by decide⟩ ⟨87, by decide⟩ p hp j hj hq fz1_139_87 fz2_139_87
  · exact match_zero_fix ⟨140, by decide⟩ ⟨87, by decide⟩ p hp j hj hq fz1_140_87 fz2_140_87
  · exact pair_141_87 p hp hrep j hj hq
  · exact match_zero_fix ⟨142, by decide⟩ ⟨87, by decide⟩ p hp j hj hq fz1_142_87 fz2_142_87
  · exact match_zero_fix ⟨143, by decide⟩ ⟨87, by decide⟩ p hp j hj hq fz1_143_87 fz2_143_87
  · exact match_zero_fix ⟨144, by decide⟩ ⟨87, by decide⟩ p hp j hj hq fz1_144_87 fz2_144_87
  · exact match_zero_fix ⟨145, by decide⟩ ⟨87, by decide⟩ p hp j hj hq fz1_145_87 fz2_145_87
  · exact match_zero_fix ⟨146, by decide⟩ ⟨87, by decide⟩ p hp j hj hq fz1_146_87 fz2_146_87
  · exact pair_147_87 p hp hrep j hj hq

end LeanDring.P5Presentation
