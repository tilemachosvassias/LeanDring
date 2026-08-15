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
import LeanDring.P5.Data.MatchPair.C012
import LeanDring.P5.Data.MatchPair.C004
import LeanDring.P5.Data.MatchPair.C005
import LeanDring.P5.Data.MatchPair.C006
import LeanDring.P5.Data.MatchPair.C007
import LeanDring.P5.Data.MatchPair.C008
import LeanDring.P5.Data.MatchPair.C009
import LeanDring.P5.Data.MatchPair.C010

/-! # Stage-5 per-column-class master theorems, chunk 11 (auto-emitted).  -/

namespace LeanDring.P5Presentation

open MulAction Finset LeanDring.DRing LeanDring.MonGSet

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.style.longLine false

theorem master_88 (p : Nat) (hp : p < (Q2.transData.getD 88 []).length)
    (hrep : (Q2.cosetIsRep.getD 88 []).getD p false = true)
    (rK : Fin 148) (j : Nat) (hj : j < (repChars.getD rK.val []).length)
    (hq : (normIsRep.getD rK.val []).getD j false = true) :
    species (Q2.reps (⟨88, by decide⟩ : Fin 148)) (colE2 ⟨88, by decide⟩ p hp)
        (rowE2 rK j hj hq)
      = species (reps (⟨88, by decide⟩ : Fin 148))
        (colE1 ⟨88, by decide⟩ p (transLenTr ⟨88, by decide⟩ p hp)) (rowE1 rK j hj) := by
  rcases rK with ⟨nK, hnK⟩; interval_cases nK
  · exact match_zero_len ⟨0, by decide⟩ ⟨88, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨1, by decide⟩ ⟨88, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨2, by decide⟩ ⟨88, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨3, by decide⟩ ⟨88, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨4, by decide⟩ ⟨88, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨5, by decide⟩ ⟨88, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨6, by decide⟩ ⟨88, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨7, by decide⟩ ⟨88, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨8, by decide⟩ ⟨88, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨9, by decide⟩ ⟨88, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨10, by decide⟩ ⟨88, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨11, by decide⟩ ⟨88, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨12, by decide⟩ ⟨88, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨13, by decide⟩ ⟨88, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨14, by decide⟩ ⟨88, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨15, by decide⟩ ⟨88, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨16, by decide⟩ ⟨88, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨17, by decide⟩ ⟨88, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨18, by decide⟩ ⟨88, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨19, by decide⟩ ⟨88, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨20, by decide⟩ ⟨88, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨21, by decide⟩ ⟨88, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨22, by decide⟩ ⟨88, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨23, by decide⟩ ⟨88, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨24, by decide⟩ ⟨88, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨25, by decide⟩ ⟨88, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨26, by decide⟩ ⟨88, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨27, by decide⟩ ⟨88, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨28, by decide⟩ ⟨88, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨29, by decide⟩ ⟨88, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨30, by decide⟩ ⟨88, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨31, by decide⟩ ⟨88, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨32, by decide⟩ ⟨88, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨33, by decide⟩ ⟨88, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨34, by decide⟩ ⟨88, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨35, by decide⟩ ⟨88, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨36, by decide⟩ ⟨88, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨37, by decide⟩ ⟨88, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨38, by decide⟩ ⟨88, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨39, by decide⟩ ⟨88, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨40, by decide⟩ ⟨88, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨41, by decide⟩ ⟨88, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨42, by decide⟩ ⟨88, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨43, by decide⟩ ⟨88, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨44, by decide⟩ ⟨88, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨45, by decide⟩ ⟨88, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨46, by decide⟩ ⟨88, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨47, by decide⟩ ⟨88, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨48, by decide⟩ ⟨88, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨49, by decide⟩ ⟨88, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨50, by decide⟩ ⟨88, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨51, by decide⟩ ⟨88, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨52, by decide⟩ ⟨88, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨53, by decide⟩ ⟨88, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨54, by decide⟩ ⟨88, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_fix ⟨55, by decide⟩ ⟨88, by decide⟩ p hp j hj hq fz1_55_88 fz2_55_88
  · exact match_zero_fix ⟨56, by decide⟩ ⟨88, by decide⟩ p hp j hj hq fz1_56_88 fz2_56_88
  · exact match_zero_fix ⟨57, by decide⟩ ⟨88, by decide⟩ p hp j hj hq fz1_57_88 fz2_57_88
  · exact match_zero_fix ⟨58, by decide⟩ ⟨88, by decide⟩ p hp j hj hq fz1_58_88 fz2_58_88
  · exact match_zero_fix ⟨59, by decide⟩ ⟨88, by decide⟩ p hp j hj hq fz1_59_88 fz2_59_88
  · exact match_zero_fix ⟨60, by decide⟩ ⟨88, by decide⟩ p hp j hj hq fz1_60_88 fz2_60_88
  · exact match_zero_fix ⟨61, by decide⟩ ⟨88, by decide⟩ p hp j hj hq fz1_61_88 fz2_61_88
  · exact match_zero_fix ⟨62, by decide⟩ ⟨88, by decide⟩ p hp j hj hq fz1_62_88 fz2_62_88
  · exact match_zero_fix ⟨63, by decide⟩ ⟨88, by decide⟩ p hp j hj hq fz1_63_88 fz2_63_88
  · exact match_zero_fix ⟨64, by decide⟩ ⟨88, by decide⟩ p hp j hj hq fz1_64_88 fz2_64_88
  · exact match_zero_fix ⟨65, by decide⟩ ⟨88, by decide⟩ p hp j hj hq fz1_65_88 fz2_65_88
  · exact match_zero_fix ⟨66, by decide⟩ ⟨88, by decide⟩ p hp j hj hq fz1_66_88 fz2_66_88
  · exact match_zero_fix ⟨67, by decide⟩ ⟨88, by decide⟩ p hp j hj hq fz1_67_88 fz2_67_88
  · exact match_zero_fix ⟨68, by decide⟩ ⟨88, by decide⟩ p hp j hj hq fz1_68_88 fz2_68_88
  · exact match_zero_fix ⟨69, by decide⟩ ⟨88, by decide⟩ p hp j hj hq fz1_69_88 fz2_69_88
  · exact match_zero_fix ⟨70, by decide⟩ ⟨88, by decide⟩ p hp j hj hq fz1_70_88 fz2_70_88
  · exact match_zero_fix ⟨71, by decide⟩ ⟨88, by decide⟩ p hp j hj hq fz1_71_88 fz2_71_88
  · exact match_zero_fix ⟨72, by decide⟩ ⟨88, by decide⟩ p hp j hj hq fz1_72_88 fz2_72_88
  · exact match_zero_fix ⟨73, by decide⟩ ⟨88, by decide⟩ p hp j hj hq fz1_73_88 fz2_73_88
  · exact match_zero_fix ⟨74, by decide⟩ ⟨88, by decide⟩ p hp j hj hq fz1_74_88 fz2_74_88
  · exact match_zero_fix ⟨75, by decide⟩ ⟨88, by decide⟩ p hp j hj hq fz1_75_88 fz2_75_88
  · exact match_zero_fix ⟨76, by decide⟩ ⟨88, by decide⟩ p hp j hj hq fz1_76_88 fz2_76_88
  · exact match_zero_fix ⟨77, by decide⟩ ⟨88, by decide⟩ p hp j hj hq fz1_77_88 fz2_77_88
  · exact match_zero_fix ⟨78, by decide⟩ ⟨88, by decide⟩ p hp j hj hq fz1_78_88 fz2_78_88
  · exact match_zero_fix ⟨79, by decide⟩ ⟨88, by decide⟩ p hp j hj hq fz1_79_88 fz2_79_88
  · exact match_zero_fix ⟨80, by decide⟩ ⟨88, by decide⟩ p hp j hj hq fz1_80_88 fz2_80_88
  · exact match_zero_fix ⟨81, by decide⟩ ⟨88, by decide⟩ p hp j hj hq fz1_81_88 fz2_81_88
  · exact match_zero_fix ⟨82, by decide⟩ ⟨88, by decide⟩ p hp j hj hq fz1_82_88 fz2_82_88
  · exact match_zero_fix ⟨83, by decide⟩ ⟨88, by decide⟩ p hp j hj hq fz1_83_88 fz2_83_88
  · exact match_zero_fix ⟨84, by decide⟩ ⟨88, by decide⟩ p hp j hj hq fz1_84_88 fz2_84_88
  · exact match_zero_fix ⟨85, by decide⟩ ⟨88, by decide⟩ p hp j hj hq fz1_85_88 fz2_85_88
  · exact match_zero_fix ⟨86, by decide⟩ ⟨88, by decide⟩ p hp j hj hq fz1_86_88 fz2_86_88
  · exact match_zero_fix ⟨87, by decide⟩ ⟨88, by decide⟩ p hp j hj hq fz1_87_88 fz2_87_88
  · exact pair_88_88 p hp hrep j hj hq
  · exact match_zero_fix ⟨89, by decide⟩ ⟨88, by decide⟩ p hp j hj hq fz1_89_88 fz2_89_88
  · exact match_zero_fix ⟨90, by decide⟩ ⟨88, by decide⟩ p hp j hj hq fz1_90_88 fz2_90_88
  · exact match_zero_fix ⟨91, by decide⟩ ⟨88, by decide⟩ p hp j hj hq fz1_91_88 fz2_91_88
  · exact match_zero_fix ⟨92, by decide⟩ ⟨88, by decide⟩ p hp j hj hq fz1_92_88 fz2_92_88
  · exact match_zero_fix ⟨93, by decide⟩ ⟨88, by decide⟩ p hp j hj hq fz1_93_88 fz2_93_88
  · exact match_zero_fix ⟨94, by decide⟩ ⟨88, by decide⟩ p hp j hj hq fz1_94_88 fz2_94_88
  · exact match_zero_fix ⟨95, by decide⟩ ⟨88, by decide⟩ p hp j hj hq fz1_95_88 fz2_95_88
  · exact match_zero_fix ⟨96, by decide⟩ ⟨88, by decide⟩ p hp j hj hq fz1_96_88 fz2_96_88
  · exact match_zero_fix ⟨97, by decide⟩ ⟨88, by decide⟩ p hp j hj hq fz1_97_88 fz2_97_88
  · exact match_zero_fix ⟨98, by decide⟩ ⟨88, by decide⟩ p hp j hj hq fz1_98_88 fz2_98_88
  · exact match_zero_fix ⟨99, by decide⟩ ⟨88, by decide⟩ p hp j hj hq fz1_99_88 fz2_99_88
  · exact match_zero_fix ⟨100, by decide⟩ ⟨88, by decide⟩ p hp j hj hq fz1_100_88 fz2_100_88
  · exact match_zero_fix ⟨101, by decide⟩ ⟨88, by decide⟩ p hp j hj hq fz1_101_88 fz2_101_88
  · exact match_zero_fix ⟨102, by decide⟩ ⟨88, by decide⟩ p hp j hj hq fz1_102_88 fz2_102_88
  · exact match_zero_fix ⟨103, by decide⟩ ⟨88, by decide⟩ p hp j hj hq fz1_103_88 fz2_103_88
  · exact match_zero_fix ⟨104, by decide⟩ ⟨88, by decide⟩ p hp j hj hq fz1_104_88 fz2_104_88
  · exact match_zero_fix ⟨105, by decide⟩ ⟨88, by decide⟩ p hp j hj hq fz1_105_88 fz2_105_88
  · exact match_zero_fix ⟨106, by decide⟩ ⟨88, by decide⟩ p hp j hj hq fz1_106_88 fz2_106_88
  · exact match_zero_fix ⟨107, by decide⟩ ⟨88, by decide⟩ p hp j hj hq fz1_107_88 fz2_107_88
  · exact match_zero_fix ⟨108, by decide⟩ ⟨88, by decide⟩ p hp j hj hq fz1_108_88 fz2_108_88
  · exact match_zero_fix ⟨109, by decide⟩ ⟨88, by decide⟩ p hp j hj hq fz1_109_88 fz2_109_88
  · exact match_zero_fix ⟨110, by decide⟩ ⟨88, by decide⟩ p hp j hj hq fz1_110_88 fz2_110_88
  · exact match_zero_fix ⟨111, by decide⟩ ⟨88, by decide⟩ p hp j hj hq fz1_111_88 fz2_111_88
  · exact match_zero_fix ⟨112, by decide⟩ ⟨88, by decide⟩ p hp j hj hq fz1_112_88 fz2_112_88
  · exact match_zero_fix ⟨113, by decide⟩ ⟨88, by decide⟩ p hp j hj hq fz1_113_88 fz2_113_88
  · exact match_zero_fix ⟨114, by decide⟩ ⟨88, by decide⟩ p hp j hj hq fz1_114_88 fz2_114_88
  · exact match_zero_fix ⟨115, by decide⟩ ⟨88, by decide⟩ p hp j hj hq fz1_115_88 fz2_115_88
  · exact match_zero_fix ⟨116, by decide⟩ ⟨88, by decide⟩ p hp j hj hq fz1_116_88 fz2_116_88
  · exact match_zero_fix ⟨117, by decide⟩ ⟨88, by decide⟩ p hp j hj hq fz1_117_88 fz2_117_88
  · exact match_zero_fix ⟨118, by decide⟩ ⟨88, by decide⟩ p hp j hj hq fz1_118_88 fz2_118_88
  · exact match_zero_fix ⟨119, by decide⟩ ⟨88, by decide⟩ p hp j hj hq fz1_119_88 fz2_119_88
  · exact match_zero_fix ⟨120, by decide⟩ ⟨88, by decide⟩ p hp j hj hq fz1_120_88 fz2_120_88
  · exact match_zero_fix ⟨121, by decide⟩ ⟨88, by decide⟩ p hp j hj hq fz1_121_88 fz2_121_88
  · exact match_zero_fix ⟨122, by decide⟩ ⟨88, by decide⟩ p hp j hj hq fz1_122_88 fz2_122_88
  · exact match_zero_fix ⟨123, by decide⟩ ⟨88, by decide⟩ p hp j hj hq fz1_123_88 fz2_123_88
  · exact match_zero_fix ⟨124, by decide⟩ ⟨88, by decide⟩ p hp j hj hq fz1_124_88 fz2_124_88
  · exact match_zero_fix ⟨125, by decide⟩ ⟨88, by decide⟩ p hp j hj hq fz1_125_88 fz2_125_88
  · exact match_zero_fix ⟨126, by decide⟩ ⟨88, by decide⟩ p hp j hj hq fz1_126_88 fz2_126_88
  · exact match_zero_fix ⟨127, by decide⟩ ⟨88, by decide⟩ p hp j hj hq fz1_127_88 fz2_127_88
  · exact match_zero_fix ⟨128, by decide⟩ ⟨88, by decide⟩ p hp j hj hq fz1_128_88 fz2_128_88
  · exact match_zero_fix ⟨129, by decide⟩ ⟨88, by decide⟩ p hp j hj hq fz1_129_88 fz2_129_88
  · exact match_zero_fix ⟨130, by decide⟩ ⟨88, by decide⟩ p hp j hj hq fz1_130_88 fz2_130_88
  · exact match_zero_fix ⟨131, by decide⟩ ⟨88, by decide⟩ p hp j hj hq fz1_131_88 fz2_131_88
  · exact match_zero_fix ⟨132, by decide⟩ ⟨88, by decide⟩ p hp j hj hq fz1_132_88 fz2_132_88
  · exact match_zero_fix ⟨133, by decide⟩ ⟨88, by decide⟩ p hp j hj hq fz1_133_88 fz2_133_88
  · exact match_zero_fix ⟨134, by decide⟩ ⟨88, by decide⟩ p hp j hj hq fz1_134_88 fz2_134_88
  · exact match_zero_fix ⟨135, by decide⟩ ⟨88, by decide⟩ p hp j hj hq fz1_135_88 fz2_135_88
  · exact match_zero_fix ⟨136, by decide⟩ ⟨88, by decide⟩ p hp j hj hq fz1_136_88 fz2_136_88
  · exact match_zero_fix ⟨137, by decide⟩ ⟨88, by decide⟩ p hp j hj hq fz1_137_88 fz2_137_88
  · exact match_zero_fix ⟨138, by decide⟩ ⟨88, by decide⟩ p hp j hj hq fz1_138_88 fz2_138_88
  · exact match_zero_fix ⟨139, by decide⟩ ⟨88, by decide⟩ p hp j hj hq fz1_139_88 fz2_139_88
  · exact match_zero_fix ⟨140, by decide⟩ ⟨88, by decide⟩ p hp j hj hq fz1_140_88 fz2_140_88
  · exact pair_141_88 p hp hrep j hj hq
  · exact match_zero_fix ⟨142, by decide⟩ ⟨88, by decide⟩ p hp j hj hq fz1_142_88 fz2_142_88
  · exact match_zero_fix ⟨143, by decide⟩ ⟨88, by decide⟩ p hp j hj hq fz1_143_88 fz2_143_88
  · exact match_zero_fix ⟨144, by decide⟩ ⟨88, by decide⟩ p hp j hj hq fz1_144_88 fz2_144_88
  · exact match_zero_fix ⟨145, by decide⟩ ⟨88, by decide⟩ p hp j hj hq fz1_145_88 fz2_145_88
  · exact match_zero_fix ⟨146, by decide⟩ ⟨88, by decide⟩ p hp j hj hq fz1_146_88 fz2_146_88
  · exact pair_147_88 p hp hrep j hj hq

theorem master_89 (p : Nat) (hp : p < (Q2.transData.getD 89 []).length)
    (hrep : (Q2.cosetIsRep.getD 89 []).getD p false = true)
    (rK : Fin 148) (j : Nat) (hj : j < (repChars.getD rK.val []).length)
    (hq : (normIsRep.getD rK.val []).getD j false = true) :
    species (Q2.reps (⟨89, by decide⟩ : Fin 148)) (colE2 ⟨89, by decide⟩ p hp)
        (rowE2 rK j hj hq)
      = species (reps (⟨89, by decide⟩ : Fin 148))
        (colE1 ⟨89, by decide⟩ p (transLenTr ⟨89, by decide⟩ p hp)) (rowE1 rK j hj) := by
  rcases rK with ⟨nK, hnK⟩; interval_cases nK
  · exact match_zero_len ⟨0, by decide⟩ ⟨89, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨1, by decide⟩ ⟨89, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨2, by decide⟩ ⟨89, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨3, by decide⟩ ⟨89, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨4, by decide⟩ ⟨89, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨5, by decide⟩ ⟨89, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨6, by decide⟩ ⟨89, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨7, by decide⟩ ⟨89, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨8, by decide⟩ ⟨89, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨9, by decide⟩ ⟨89, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨10, by decide⟩ ⟨89, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨11, by decide⟩ ⟨89, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨12, by decide⟩ ⟨89, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨13, by decide⟩ ⟨89, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨14, by decide⟩ ⟨89, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨15, by decide⟩ ⟨89, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨16, by decide⟩ ⟨89, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨17, by decide⟩ ⟨89, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨18, by decide⟩ ⟨89, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨19, by decide⟩ ⟨89, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨20, by decide⟩ ⟨89, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨21, by decide⟩ ⟨89, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨22, by decide⟩ ⟨89, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨23, by decide⟩ ⟨89, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨24, by decide⟩ ⟨89, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨25, by decide⟩ ⟨89, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨26, by decide⟩ ⟨89, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨27, by decide⟩ ⟨89, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨28, by decide⟩ ⟨89, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨29, by decide⟩ ⟨89, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨30, by decide⟩ ⟨89, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨31, by decide⟩ ⟨89, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨32, by decide⟩ ⟨89, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨33, by decide⟩ ⟨89, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨34, by decide⟩ ⟨89, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨35, by decide⟩ ⟨89, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨36, by decide⟩ ⟨89, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨37, by decide⟩ ⟨89, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨38, by decide⟩ ⟨89, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨39, by decide⟩ ⟨89, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨40, by decide⟩ ⟨89, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨41, by decide⟩ ⟨89, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨42, by decide⟩ ⟨89, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨43, by decide⟩ ⟨89, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨44, by decide⟩ ⟨89, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨45, by decide⟩ ⟨89, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨46, by decide⟩ ⟨89, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨47, by decide⟩ ⟨89, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨48, by decide⟩ ⟨89, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨49, by decide⟩ ⟨89, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨50, by decide⟩ ⟨89, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨51, by decide⟩ ⟨89, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨52, by decide⟩ ⟨89, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨53, by decide⟩ ⟨89, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨54, by decide⟩ ⟨89, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_fix ⟨55, by decide⟩ ⟨89, by decide⟩ p hp j hj hq fz1_55_89 fz2_55_89
  · exact match_zero_fix ⟨56, by decide⟩ ⟨89, by decide⟩ p hp j hj hq fz1_56_89 fz2_56_89
  · exact match_zero_fix ⟨57, by decide⟩ ⟨89, by decide⟩ p hp j hj hq fz1_57_89 fz2_57_89
  · exact match_zero_fix ⟨58, by decide⟩ ⟨89, by decide⟩ p hp j hj hq fz1_58_89 fz2_58_89
  · exact match_zero_fix ⟨59, by decide⟩ ⟨89, by decide⟩ p hp j hj hq fz1_59_89 fz2_59_89
  · exact match_zero_fix ⟨60, by decide⟩ ⟨89, by decide⟩ p hp j hj hq fz1_60_89 fz2_60_89
  · exact match_zero_fix ⟨61, by decide⟩ ⟨89, by decide⟩ p hp j hj hq fz1_61_89 fz2_61_89
  · exact match_zero_fix ⟨62, by decide⟩ ⟨89, by decide⟩ p hp j hj hq fz1_62_89 fz2_62_89
  · exact match_zero_fix ⟨63, by decide⟩ ⟨89, by decide⟩ p hp j hj hq fz1_63_89 fz2_63_89
  · exact match_zero_fix ⟨64, by decide⟩ ⟨89, by decide⟩ p hp j hj hq fz1_64_89 fz2_64_89
  · exact match_zero_fix ⟨65, by decide⟩ ⟨89, by decide⟩ p hp j hj hq fz1_65_89 fz2_65_89
  · exact match_zero_fix ⟨66, by decide⟩ ⟨89, by decide⟩ p hp j hj hq fz1_66_89 fz2_66_89
  · exact match_zero_fix ⟨67, by decide⟩ ⟨89, by decide⟩ p hp j hj hq fz1_67_89 fz2_67_89
  · exact match_zero_fix ⟨68, by decide⟩ ⟨89, by decide⟩ p hp j hj hq fz1_68_89 fz2_68_89
  · exact match_zero_fix ⟨69, by decide⟩ ⟨89, by decide⟩ p hp j hj hq fz1_69_89 fz2_69_89
  · exact match_zero_fix ⟨70, by decide⟩ ⟨89, by decide⟩ p hp j hj hq fz1_70_89 fz2_70_89
  · exact match_zero_fix ⟨71, by decide⟩ ⟨89, by decide⟩ p hp j hj hq fz1_71_89 fz2_71_89
  · exact match_zero_fix ⟨72, by decide⟩ ⟨89, by decide⟩ p hp j hj hq fz1_72_89 fz2_72_89
  · exact match_zero_fix ⟨73, by decide⟩ ⟨89, by decide⟩ p hp j hj hq fz1_73_89 fz2_73_89
  · exact match_zero_fix ⟨74, by decide⟩ ⟨89, by decide⟩ p hp j hj hq fz1_74_89 fz2_74_89
  · exact match_zero_fix ⟨75, by decide⟩ ⟨89, by decide⟩ p hp j hj hq fz1_75_89 fz2_75_89
  · exact match_zero_fix ⟨76, by decide⟩ ⟨89, by decide⟩ p hp j hj hq fz1_76_89 fz2_76_89
  · exact match_zero_fix ⟨77, by decide⟩ ⟨89, by decide⟩ p hp j hj hq fz1_77_89 fz2_77_89
  · exact match_zero_fix ⟨78, by decide⟩ ⟨89, by decide⟩ p hp j hj hq fz1_78_89 fz2_78_89
  · exact match_zero_fix ⟨79, by decide⟩ ⟨89, by decide⟩ p hp j hj hq fz1_79_89 fz2_79_89
  · exact match_zero_fix ⟨80, by decide⟩ ⟨89, by decide⟩ p hp j hj hq fz1_80_89 fz2_80_89
  · exact match_zero_fix ⟨81, by decide⟩ ⟨89, by decide⟩ p hp j hj hq fz1_81_89 fz2_81_89
  · exact match_zero_fix ⟨82, by decide⟩ ⟨89, by decide⟩ p hp j hj hq fz1_82_89 fz2_82_89
  · exact match_zero_fix ⟨83, by decide⟩ ⟨89, by decide⟩ p hp j hj hq fz1_83_89 fz2_83_89
  · exact match_zero_fix ⟨84, by decide⟩ ⟨89, by decide⟩ p hp j hj hq fz1_84_89 fz2_84_89
  · exact match_zero_fix ⟨85, by decide⟩ ⟨89, by decide⟩ p hp j hj hq fz1_85_89 fz2_85_89
  · exact match_zero_fix ⟨86, by decide⟩ ⟨89, by decide⟩ p hp j hj hq fz1_86_89 fz2_86_89
  · exact match_zero_fix ⟨87, by decide⟩ ⟨89, by decide⟩ p hp j hj hq fz1_87_89 fz2_87_89
  · exact match_zero_fix ⟨88, by decide⟩ ⟨89, by decide⟩ p hp j hj hq fz1_88_89 fz2_88_89
  · exact pair_89_89 p hp hrep j hj hq
  · exact match_zero_fix ⟨90, by decide⟩ ⟨89, by decide⟩ p hp j hj hq fz1_90_89 fz2_90_89
  · exact match_zero_fix ⟨91, by decide⟩ ⟨89, by decide⟩ p hp j hj hq fz1_91_89 fz2_91_89
  · exact match_zero_fix ⟨92, by decide⟩ ⟨89, by decide⟩ p hp j hj hq fz1_92_89 fz2_92_89
  · exact match_zero_fix ⟨93, by decide⟩ ⟨89, by decide⟩ p hp j hj hq fz1_93_89 fz2_93_89
  · exact match_zero_fix ⟨94, by decide⟩ ⟨89, by decide⟩ p hp j hj hq fz1_94_89 fz2_94_89
  · exact match_zero_fix ⟨95, by decide⟩ ⟨89, by decide⟩ p hp j hj hq fz1_95_89 fz2_95_89
  · exact match_zero_fix ⟨96, by decide⟩ ⟨89, by decide⟩ p hp j hj hq fz1_96_89 fz2_96_89
  · exact match_zero_fix ⟨97, by decide⟩ ⟨89, by decide⟩ p hp j hj hq fz1_97_89 fz2_97_89
  · exact match_zero_fix ⟨98, by decide⟩ ⟨89, by decide⟩ p hp j hj hq fz1_98_89 fz2_98_89
  · exact match_zero_fix ⟨99, by decide⟩ ⟨89, by decide⟩ p hp j hj hq fz1_99_89 fz2_99_89
  · exact match_zero_fix ⟨100, by decide⟩ ⟨89, by decide⟩ p hp j hj hq fz1_100_89 fz2_100_89
  · exact match_zero_fix ⟨101, by decide⟩ ⟨89, by decide⟩ p hp j hj hq fz1_101_89 fz2_101_89
  · exact match_zero_fix ⟨102, by decide⟩ ⟨89, by decide⟩ p hp j hj hq fz1_102_89 fz2_102_89
  · exact match_zero_fix ⟨103, by decide⟩ ⟨89, by decide⟩ p hp j hj hq fz1_103_89 fz2_103_89
  · exact match_zero_fix ⟨104, by decide⟩ ⟨89, by decide⟩ p hp j hj hq fz1_104_89 fz2_104_89
  · exact match_zero_fix ⟨105, by decide⟩ ⟨89, by decide⟩ p hp j hj hq fz1_105_89 fz2_105_89
  · exact match_zero_fix ⟨106, by decide⟩ ⟨89, by decide⟩ p hp j hj hq fz1_106_89 fz2_106_89
  · exact match_zero_fix ⟨107, by decide⟩ ⟨89, by decide⟩ p hp j hj hq fz1_107_89 fz2_107_89
  · exact match_zero_fix ⟨108, by decide⟩ ⟨89, by decide⟩ p hp j hj hq fz1_108_89 fz2_108_89
  · exact match_zero_fix ⟨109, by decide⟩ ⟨89, by decide⟩ p hp j hj hq fz1_109_89 fz2_109_89
  · exact match_zero_fix ⟨110, by decide⟩ ⟨89, by decide⟩ p hp j hj hq fz1_110_89 fz2_110_89
  · exact match_zero_fix ⟨111, by decide⟩ ⟨89, by decide⟩ p hp j hj hq fz1_111_89 fz2_111_89
  · exact match_zero_fix ⟨112, by decide⟩ ⟨89, by decide⟩ p hp j hj hq fz1_112_89 fz2_112_89
  · exact match_zero_fix ⟨113, by decide⟩ ⟨89, by decide⟩ p hp j hj hq fz1_113_89 fz2_113_89
  · exact match_zero_fix ⟨114, by decide⟩ ⟨89, by decide⟩ p hp j hj hq fz1_114_89 fz2_114_89
  · exact match_zero_fix ⟨115, by decide⟩ ⟨89, by decide⟩ p hp j hj hq fz1_115_89 fz2_115_89
  · exact match_zero_fix ⟨116, by decide⟩ ⟨89, by decide⟩ p hp j hj hq fz1_116_89 fz2_116_89
  · exact match_zero_fix ⟨117, by decide⟩ ⟨89, by decide⟩ p hp j hj hq fz1_117_89 fz2_117_89
  · exact match_zero_fix ⟨118, by decide⟩ ⟨89, by decide⟩ p hp j hj hq fz1_118_89 fz2_118_89
  · exact match_zero_fix ⟨119, by decide⟩ ⟨89, by decide⟩ p hp j hj hq fz1_119_89 fz2_119_89
  · exact match_zero_fix ⟨120, by decide⟩ ⟨89, by decide⟩ p hp j hj hq fz1_120_89 fz2_120_89
  · exact match_zero_fix ⟨121, by decide⟩ ⟨89, by decide⟩ p hp j hj hq fz1_121_89 fz2_121_89
  · exact match_zero_fix ⟨122, by decide⟩ ⟨89, by decide⟩ p hp j hj hq fz1_122_89 fz2_122_89
  · exact match_zero_fix ⟨123, by decide⟩ ⟨89, by decide⟩ p hp j hj hq fz1_123_89 fz2_123_89
  · exact match_zero_fix ⟨124, by decide⟩ ⟨89, by decide⟩ p hp j hj hq fz1_124_89 fz2_124_89
  · exact match_zero_fix ⟨125, by decide⟩ ⟨89, by decide⟩ p hp j hj hq fz1_125_89 fz2_125_89
  · exact match_zero_fix ⟨126, by decide⟩ ⟨89, by decide⟩ p hp j hj hq fz1_126_89 fz2_126_89
  · exact match_zero_fix ⟨127, by decide⟩ ⟨89, by decide⟩ p hp j hj hq fz1_127_89 fz2_127_89
  · exact match_zero_fix ⟨128, by decide⟩ ⟨89, by decide⟩ p hp j hj hq fz1_128_89 fz2_128_89
  · exact match_zero_fix ⟨129, by decide⟩ ⟨89, by decide⟩ p hp j hj hq fz1_129_89 fz2_129_89
  · exact match_zero_fix ⟨130, by decide⟩ ⟨89, by decide⟩ p hp j hj hq fz1_130_89 fz2_130_89
  · exact match_zero_fix ⟨131, by decide⟩ ⟨89, by decide⟩ p hp j hj hq fz1_131_89 fz2_131_89
  · exact match_zero_fix ⟨132, by decide⟩ ⟨89, by decide⟩ p hp j hj hq fz1_132_89 fz2_132_89
  · exact match_zero_fix ⟨133, by decide⟩ ⟨89, by decide⟩ p hp j hj hq fz1_133_89 fz2_133_89
  · exact match_zero_fix ⟨134, by decide⟩ ⟨89, by decide⟩ p hp j hj hq fz1_134_89 fz2_134_89
  · exact match_zero_fix ⟨135, by decide⟩ ⟨89, by decide⟩ p hp j hj hq fz1_135_89 fz2_135_89
  · exact match_zero_fix ⟨136, by decide⟩ ⟨89, by decide⟩ p hp j hj hq fz1_136_89 fz2_136_89
  · exact match_zero_fix ⟨137, by decide⟩ ⟨89, by decide⟩ p hp j hj hq fz1_137_89 fz2_137_89
  · exact match_zero_fix ⟨138, by decide⟩ ⟨89, by decide⟩ p hp j hj hq fz1_138_89 fz2_138_89
  · exact match_zero_fix ⟨139, by decide⟩ ⟨89, by decide⟩ p hp j hj hq fz1_139_89 fz2_139_89
  · exact match_zero_fix ⟨140, by decide⟩ ⟨89, by decide⟩ p hp j hj hq fz1_140_89 fz2_140_89
  · exact pair_141_89 p hp hrep j hj hq
  · exact match_zero_fix ⟨142, by decide⟩ ⟨89, by decide⟩ p hp j hj hq fz1_142_89 fz2_142_89
  · exact match_zero_fix ⟨143, by decide⟩ ⟨89, by decide⟩ p hp j hj hq fz1_143_89 fz2_143_89
  · exact match_zero_fix ⟨144, by decide⟩ ⟨89, by decide⟩ p hp j hj hq fz1_144_89 fz2_144_89
  · exact match_zero_fix ⟨145, by decide⟩ ⟨89, by decide⟩ p hp j hj hq fz1_145_89 fz2_145_89
  · exact match_zero_fix ⟨146, by decide⟩ ⟨89, by decide⟩ p hp j hj hq fz1_146_89 fz2_146_89
  · exact pair_147_89 p hp hrep j hj hq

theorem master_90 (p : Nat) (hp : p < (Q2.transData.getD 90 []).length)
    (hrep : (Q2.cosetIsRep.getD 90 []).getD p false = true)
    (rK : Fin 148) (j : Nat) (hj : j < (repChars.getD rK.val []).length)
    (hq : (normIsRep.getD rK.val []).getD j false = true) :
    species (Q2.reps (⟨90, by decide⟩ : Fin 148)) (colE2 ⟨90, by decide⟩ p hp)
        (rowE2 rK j hj hq)
      = species (reps (⟨90, by decide⟩ : Fin 148))
        (colE1 ⟨90, by decide⟩ p (transLenTr ⟨90, by decide⟩ p hp)) (rowE1 rK j hj) := by
  rcases rK with ⟨nK, hnK⟩; interval_cases nK
  · exact match_zero_len ⟨0, by decide⟩ ⟨90, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨1, by decide⟩ ⟨90, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨2, by decide⟩ ⟨90, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨3, by decide⟩ ⟨90, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨4, by decide⟩ ⟨90, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨5, by decide⟩ ⟨90, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨6, by decide⟩ ⟨90, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨7, by decide⟩ ⟨90, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨8, by decide⟩ ⟨90, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨9, by decide⟩ ⟨90, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨10, by decide⟩ ⟨90, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨11, by decide⟩ ⟨90, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨12, by decide⟩ ⟨90, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨13, by decide⟩ ⟨90, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨14, by decide⟩ ⟨90, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨15, by decide⟩ ⟨90, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨16, by decide⟩ ⟨90, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨17, by decide⟩ ⟨90, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨18, by decide⟩ ⟨90, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨19, by decide⟩ ⟨90, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨20, by decide⟩ ⟨90, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨21, by decide⟩ ⟨90, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨22, by decide⟩ ⟨90, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨23, by decide⟩ ⟨90, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨24, by decide⟩ ⟨90, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨25, by decide⟩ ⟨90, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨26, by decide⟩ ⟨90, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨27, by decide⟩ ⟨90, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨28, by decide⟩ ⟨90, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨29, by decide⟩ ⟨90, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨30, by decide⟩ ⟨90, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨31, by decide⟩ ⟨90, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨32, by decide⟩ ⟨90, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨33, by decide⟩ ⟨90, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨34, by decide⟩ ⟨90, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨35, by decide⟩ ⟨90, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨36, by decide⟩ ⟨90, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨37, by decide⟩ ⟨90, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨38, by decide⟩ ⟨90, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨39, by decide⟩ ⟨90, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨40, by decide⟩ ⟨90, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨41, by decide⟩ ⟨90, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨42, by decide⟩ ⟨90, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨43, by decide⟩ ⟨90, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨44, by decide⟩ ⟨90, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨45, by decide⟩ ⟨90, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨46, by decide⟩ ⟨90, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨47, by decide⟩ ⟨90, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨48, by decide⟩ ⟨90, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨49, by decide⟩ ⟨90, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨50, by decide⟩ ⟨90, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨51, by decide⟩ ⟨90, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨52, by decide⟩ ⟨90, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨53, by decide⟩ ⟨90, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨54, by decide⟩ ⟨90, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_fix ⟨55, by decide⟩ ⟨90, by decide⟩ p hp j hj hq fz1_55_90 fz2_55_90
  · exact match_zero_fix ⟨56, by decide⟩ ⟨90, by decide⟩ p hp j hj hq fz1_56_90 fz2_56_90
  · exact match_zero_fix ⟨57, by decide⟩ ⟨90, by decide⟩ p hp j hj hq fz1_57_90 fz2_57_90
  · exact match_zero_fix ⟨58, by decide⟩ ⟨90, by decide⟩ p hp j hj hq fz1_58_90 fz2_58_90
  · exact match_zero_fix ⟨59, by decide⟩ ⟨90, by decide⟩ p hp j hj hq fz1_59_90 fz2_59_90
  · exact match_zero_fix ⟨60, by decide⟩ ⟨90, by decide⟩ p hp j hj hq fz1_60_90 fz2_60_90
  · exact match_zero_fix ⟨61, by decide⟩ ⟨90, by decide⟩ p hp j hj hq fz1_61_90 fz2_61_90
  · exact match_zero_fix ⟨62, by decide⟩ ⟨90, by decide⟩ p hp j hj hq fz1_62_90 fz2_62_90
  · exact match_zero_fix ⟨63, by decide⟩ ⟨90, by decide⟩ p hp j hj hq fz1_63_90 fz2_63_90
  · exact match_zero_fix ⟨64, by decide⟩ ⟨90, by decide⟩ p hp j hj hq fz1_64_90 fz2_64_90
  · exact match_zero_fix ⟨65, by decide⟩ ⟨90, by decide⟩ p hp j hj hq fz1_65_90 fz2_65_90
  · exact match_zero_fix ⟨66, by decide⟩ ⟨90, by decide⟩ p hp j hj hq fz1_66_90 fz2_66_90
  · exact match_zero_fix ⟨67, by decide⟩ ⟨90, by decide⟩ p hp j hj hq fz1_67_90 fz2_67_90
  · exact match_zero_fix ⟨68, by decide⟩ ⟨90, by decide⟩ p hp j hj hq fz1_68_90 fz2_68_90
  · exact match_zero_fix ⟨69, by decide⟩ ⟨90, by decide⟩ p hp j hj hq fz1_69_90 fz2_69_90
  · exact match_zero_fix ⟨70, by decide⟩ ⟨90, by decide⟩ p hp j hj hq fz1_70_90 fz2_70_90
  · exact match_zero_fix ⟨71, by decide⟩ ⟨90, by decide⟩ p hp j hj hq fz1_71_90 fz2_71_90
  · exact match_zero_fix ⟨72, by decide⟩ ⟨90, by decide⟩ p hp j hj hq fz1_72_90 fz2_72_90
  · exact match_zero_fix ⟨73, by decide⟩ ⟨90, by decide⟩ p hp j hj hq fz1_73_90 fz2_73_90
  · exact match_zero_fix ⟨74, by decide⟩ ⟨90, by decide⟩ p hp j hj hq fz1_74_90 fz2_74_90
  · exact match_zero_fix ⟨75, by decide⟩ ⟨90, by decide⟩ p hp j hj hq fz1_75_90 fz2_75_90
  · exact match_zero_fix ⟨76, by decide⟩ ⟨90, by decide⟩ p hp j hj hq fz1_76_90 fz2_76_90
  · exact match_zero_fix ⟨77, by decide⟩ ⟨90, by decide⟩ p hp j hj hq fz1_77_90 fz2_77_90
  · exact match_zero_fix ⟨78, by decide⟩ ⟨90, by decide⟩ p hp j hj hq fz1_78_90 fz2_78_90
  · exact match_zero_fix ⟨79, by decide⟩ ⟨90, by decide⟩ p hp j hj hq fz1_79_90 fz2_79_90
  · exact match_zero_fix ⟨80, by decide⟩ ⟨90, by decide⟩ p hp j hj hq fz1_80_90 fz2_80_90
  · exact match_zero_fix ⟨81, by decide⟩ ⟨90, by decide⟩ p hp j hj hq fz1_81_90 fz2_81_90
  · exact match_zero_fix ⟨82, by decide⟩ ⟨90, by decide⟩ p hp j hj hq fz1_82_90 fz2_82_90
  · exact match_zero_fix ⟨83, by decide⟩ ⟨90, by decide⟩ p hp j hj hq fz1_83_90 fz2_83_90
  · exact match_zero_fix ⟨84, by decide⟩ ⟨90, by decide⟩ p hp j hj hq fz1_84_90 fz2_84_90
  · exact match_zero_fix ⟨85, by decide⟩ ⟨90, by decide⟩ p hp j hj hq fz1_85_90 fz2_85_90
  · exact match_zero_fix ⟨86, by decide⟩ ⟨90, by decide⟩ p hp j hj hq fz1_86_90 fz2_86_90
  · exact match_zero_fix ⟨87, by decide⟩ ⟨90, by decide⟩ p hp j hj hq fz1_87_90 fz2_87_90
  · exact match_zero_fix ⟨88, by decide⟩ ⟨90, by decide⟩ p hp j hj hq fz1_88_90 fz2_88_90
  · exact match_zero_fix ⟨89, by decide⟩ ⟨90, by decide⟩ p hp j hj hq fz1_89_90 fz2_89_90
  · exact pair_90_90 p hp hrep j hj hq
  · exact match_zero_fix ⟨91, by decide⟩ ⟨90, by decide⟩ p hp j hj hq fz1_91_90 fz2_91_90
  · exact match_zero_fix ⟨92, by decide⟩ ⟨90, by decide⟩ p hp j hj hq fz1_92_90 fz2_92_90
  · exact match_zero_fix ⟨93, by decide⟩ ⟨90, by decide⟩ p hp j hj hq fz1_93_90 fz2_93_90
  · exact match_zero_fix ⟨94, by decide⟩ ⟨90, by decide⟩ p hp j hj hq fz1_94_90 fz2_94_90
  · exact match_zero_fix ⟨95, by decide⟩ ⟨90, by decide⟩ p hp j hj hq fz1_95_90 fz2_95_90
  · exact match_zero_fix ⟨96, by decide⟩ ⟨90, by decide⟩ p hp j hj hq fz1_96_90 fz2_96_90
  · exact match_zero_fix ⟨97, by decide⟩ ⟨90, by decide⟩ p hp j hj hq fz1_97_90 fz2_97_90
  · exact match_zero_fix ⟨98, by decide⟩ ⟨90, by decide⟩ p hp j hj hq fz1_98_90 fz2_98_90
  · exact match_zero_fix ⟨99, by decide⟩ ⟨90, by decide⟩ p hp j hj hq fz1_99_90 fz2_99_90
  · exact match_zero_fix ⟨100, by decide⟩ ⟨90, by decide⟩ p hp j hj hq fz1_100_90 fz2_100_90
  · exact match_zero_fix ⟨101, by decide⟩ ⟨90, by decide⟩ p hp j hj hq fz1_101_90 fz2_101_90
  · exact match_zero_fix ⟨102, by decide⟩ ⟨90, by decide⟩ p hp j hj hq fz1_102_90 fz2_102_90
  · exact match_zero_fix ⟨103, by decide⟩ ⟨90, by decide⟩ p hp j hj hq fz1_103_90 fz2_103_90
  · exact match_zero_fix ⟨104, by decide⟩ ⟨90, by decide⟩ p hp j hj hq fz1_104_90 fz2_104_90
  · exact match_zero_fix ⟨105, by decide⟩ ⟨90, by decide⟩ p hp j hj hq fz1_105_90 fz2_105_90
  · exact match_zero_fix ⟨106, by decide⟩ ⟨90, by decide⟩ p hp j hj hq fz1_106_90 fz2_106_90
  · exact match_zero_fix ⟨107, by decide⟩ ⟨90, by decide⟩ p hp j hj hq fz1_107_90 fz2_107_90
  · exact match_zero_fix ⟨108, by decide⟩ ⟨90, by decide⟩ p hp j hj hq fz1_108_90 fz2_108_90
  · exact match_zero_fix ⟨109, by decide⟩ ⟨90, by decide⟩ p hp j hj hq fz1_109_90 fz2_109_90
  · exact match_zero_fix ⟨110, by decide⟩ ⟨90, by decide⟩ p hp j hj hq fz1_110_90 fz2_110_90
  · exact match_zero_fix ⟨111, by decide⟩ ⟨90, by decide⟩ p hp j hj hq fz1_111_90 fz2_111_90
  · exact match_zero_fix ⟨112, by decide⟩ ⟨90, by decide⟩ p hp j hj hq fz1_112_90 fz2_112_90
  · exact match_zero_fix ⟨113, by decide⟩ ⟨90, by decide⟩ p hp j hj hq fz1_113_90 fz2_113_90
  · exact match_zero_fix ⟨114, by decide⟩ ⟨90, by decide⟩ p hp j hj hq fz1_114_90 fz2_114_90
  · exact match_zero_fix ⟨115, by decide⟩ ⟨90, by decide⟩ p hp j hj hq fz1_115_90 fz2_115_90
  · exact pair_116_90 p hp hrep j hj hq
  · exact match_zero_fix ⟨117, by decide⟩ ⟨90, by decide⟩ p hp j hj hq fz1_117_90 fz2_117_90
  · exact match_zero_fix ⟨118, by decide⟩ ⟨90, by decide⟩ p hp j hj hq fz1_118_90 fz2_118_90
  · exact match_zero_fix ⟨119, by decide⟩ ⟨90, by decide⟩ p hp j hj hq fz1_119_90 fz2_119_90
  · exact match_zero_fix ⟨120, by decide⟩ ⟨90, by decide⟩ p hp j hj hq fz1_120_90 fz2_120_90
  · exact match_zero_fix ⟨121, by decide⟩ ⟨90, by decide⟩ p hp j hj hq fz1_121_90 fz2_121_90
  · exact pair_122_90 p hp hrep j hj hq
  · exact match_zero_fix ⟨123, by decide⟩ ⟨90, by decide⟩ p hp j hj hq fz1_123_90 fz2_123_90
  · exact match_zero_fix ⟨124, by decide⟩ ⟨90, by decide⟩ p hp j hj hq fz1_124_90 fz2_124_90
  · exact match_zero_fix ⟨125, by decide⟩ ⟨90, by decide⟩ p hp j hj hq fz1_125_90 fz2_125_90
  · exact match_zero_fix ⟨126, by decide⟩ ⟨90, by decide⟩ p hp j hj hq fz1_126_90 fz2_126_90
  · exact match_zero_fix ⟨127, by decide⟩ ⟨90, by decide⟩ p hp j hj hq fz1_127_90 fz2_127_90
  · exact pair_128_90 p hp hrep j hj hq
  · exact match_zero_fix ⟨129, by decide⟩ ⟨90, by decide⟩ p hp j hj hq fz1_129_90 fz2_129_90
  · exact match_zero_fix ⟨130, by decide⟩ ⟨90, by decide⟩ p hp j hj hq fz1_130_90 fz2_130_90
  · exact match_zero_fix ⟨131, by decide⟩ ⟨90, by decide⟩ p hp j hj hq fz1_131_90 fz2_131_90
  · exact match_zero_fix ⟨132, by decide⟩ ⟨90, by decide⟩ p hp j hj hq fz1_132_90 fz2_132_90
  · exact match_zero_fix ⟨133, by decide⟩ ⟨90, by decide⟩ p hp j hj hq fz1_133_90 fz2_133_90
  · exact pair_134_90 p hp hrep j hj hq
  · exact match_zero_fix ⟨135, by decide⟩ ⟨90, by decide⟩ p hp j hj hq fz1_135_90 fz2_135_90
  · exact match_zero_fix ⟨136, by decide⟩ ⟨90, by decide⟩ p hp j hj hq fz1_136_90 fz2_136_90
  · exact match_zero_fix ⟨137, by decide⟩ ⟨90, by decide⟩ p hp j hj hq fz1_137_90 fz2_137_90
  · exact match_zero_fix ⟨138, by decide⟩ ⟨90, by decide⟩ p hp j hj hq fz1_138_90 fz2_138_90
  · exact match_zero_fix ⟨139, by decide⟩ ⟨90, by decide⟩ p hp j hj hq fz1_139_90 fz2_139_90
  · exact pair_140_90 p hp hrep j hj hq
  · exact match_zero_fix ⟨141, by decide⟩ ⟨90, by decide⟩ p hp j hj hq fz1_141_90 fz2_141_90
  · exact pair_142_90 p hp hrep j hj hq
  · exact match_zero_fix ⟨143, by decide⟩ ⟨90, by decide⟩ p hp j hj hq fz1_143_90 fz2_143_90
  · exact match_zero_fix ⟨144, by decide⟩ ⟨90, by decide⟩ p hp j hj hq fz1_144_90 fz2_144_90
  · exact match_zero_fix ⟨145, by decide⟩ ⟨90, by decide⟩ p hp j hj hq fz1_145_90 fz2_145_90
  · exact match_zero_fix ⟨146, by decide⟩ ⟨90, by decide⟩ p hp j hj hq fz1_146_90 fz2_146_90
  · exact pair_147_90 p hp hrep j hj hq

theorem master_91 (p : Nat) (hp : p < (Q2.transData.getD 91 []).length)
    (hrep : (Q2.cosetIsRep.getD 91 []).getD p false = true)
    (rK : Fin 148) (j : Nat) (hj : j < (repChars.getD rK.val []).length)
    (hq : (normIsRep.getD rK.val []).getD j false = true) :
    species (Q2.reps (⟨91, by decide⟩ : Fin 148)) (colE2 ⟨91, by decide⟩ p hp)
        (rowE2 rK j hj hq)
      = species (reps (⟨91, by decide⟩ : Fin 148))
        (colE1 ⟨91, by decide⟩ p (transLenTr ⟨91, by decide⟩ p hp)) (rowE1 rK j hj) := by
  rcases rK with ⟨nK, hnK⟩; interval_cases nK
  · exact match_zero_len ⟨0, by decide⟩ ⟨91, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨1, by decide⟩ ⟨91, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨2, by decide⟩ ⟨91, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨3, by decide⟩ ⟨91, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨4, by decide⟩ ⟨91, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨5, by decide⟩ ⟨91, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨6, by decide⟩ ⟨91, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨7, by decide⟩ ⟨91, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨8, by decide⟩ ⟨91, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨9, by decide⟩ ⟨91, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨10, by decide⟩ ⟨91, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨11, by decide⟩ ⟨91, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨12, by decide⟩ ⟨91, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨13, by decide⟩ ⟨91, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨14, by decide⟩ ⟨91, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨15, by decide⟩ ⟨91, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨16, by decide⟩ ⟨91, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨17, by decide⟩ ⟨91, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨18, by decide⟩ ⟨91, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨19, by decide⟩ ⟨91, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨20, by decide⟩ ⟨91, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨21, by decide⟩ ⟨91, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨22, by decide⟩ ⟨91, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨23, by decide⟩ ⟨91, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨24, by decide⟩ ⟨91, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨25, by decide⟩ ⟨91, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨26, by decide⟩ ⟨91, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨27, by decide⟩ ⟨91, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨28, by decide⟩ ⟨91, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨29, by decide⟩ ⟨91, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨30, by decide⟩ ⟨91, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨31, by decide⟩ ⟨91, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨32, by decide⟩ ⟨91, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨33, by decide⟩ ⟨91, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨34, by decide⟩ ⟨91, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨35, by decide⟩ ⟨91, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨36, by decide⟩ ⟨91, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨37, by decide⟩ ⟨91, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨38, by decide⟩ ⟨91, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨39, by decide⟩ ⟨91, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨40, by decide⟩ ⟨91, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨41, by decide⟩ ⟨91, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨42, by decide⟩ ⟨91, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨43, by decide⟩ ⟨91, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨44, by decide⟩ ⟨91, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨45, by decide⟩ ⟨91, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨46, by decide⟩ ⟨91, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨47, by decide⟩ ⟨91, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨48, by decide⟩ ⟨91, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨49, by decide⟩ ⟨91, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨50, by decide⟩ ⟨91, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨51, by decide⟩ ⟨91, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨52, by decide⟩ ⟨91, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨53, by decide⟩ ⟨91, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨54, by decide⟩ ⟨91, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_fix ⟨55, by decide⟩ ⟨91, by decide⟩ p hp j hj hq fz1_55_91 fz2_55_91
  · exact match_zero_fix ⟨56, by decide⟩ ⟨91, by decide⟩ p hp j hj hq fz1_56_91 fz2_56_91
  · exact match_zero_fix ⟨57, by decide⟩ ⟨91, by decide⟩ p hp j hj hq fz1_57_91 fz2_57_91
  · exact match_zero_fix ⟨58, by decide⟩ ⟨91, by decide⟩ p hp j hj hq fz1_58_91 fz2_58_91
  · exact match_zero_fix ⟨59, by decide⟩ ⟨91, by decide⟩ p hp j hj hq fz1_59_91 fz2_59_91
  · exact match_zero_fix ⟨60, by decide⟩ ⟨91, by decide⟩ p hp j hj hq fz1_60_91 fz2_60_91
  · exact match_zero_fix ⟨61, by decide⟩ ⟨91, by decide⟩ p hp j hj hq fz1_61_91 fz2_61_91
  · exact match_zero_fix ⟨62, by decide⟩ ⟨91, by decide⟩ p hp j hj hq fz1_62_91 fz2_62_91
  · exact match_zero_fix ⟨63, by decide⟩ ⟨91, by decide⟩ p hp j hj hq fz1_63_91 fz2_63_91
  · exact match_zero_fix ⟨64, by decide⟩ ⟨91, by decide⟩ p hp j hj hq fz1_64_91 fz2_64_91
  · exact match_zero_fix ⟨65, by decide⟩ ⟨91, by decide⟩ p hp j hj hq fz1_65_91 fz2_65_91
  · exact match_zero_fix ⟨66, by decide⟩ ⟨91, by decide⟩ p hp j hj hq fz1_66_91 fz2_66_91
  · exact match_zero_fix ⟨67, by decide⟩ ⟨91, by decide⟩ p hp j hj hq fz1_67_91 fz2_67_91
  · exact match_zero_fix ⟨68, by decide⟩ ⟨91, by decide⟩ p hp j hj hq fz1_68_91 fz2_68_91
  · exact match_zero_fix ⟨69, by decide⟩ ⟨91, by decide⟩ p hp j hj hq fz1_69_91 fz2_69_91
  · exact match_zero_fix ⟨70, by decide⟩ ⟨91, by decide⟩ p hp j hj hq fz1_70_91 fz2_70_91
  · exact match_zero_fix ⟨71, by decide⟩ ⟨91, by decide⟩ p hp j hj hq fz1_71_91 fz2_71_91
  · exact match_zero_fix ⟨72, by decide⟩ ⟨91, by decide⟩ p hp j hj hq fz1_72_91 fz2_72_91
  · exact match_zero_fix ⟨73, by decide⟩ ⟨91, by decide⟩ p hp j hj hq fz1_73_91 fz2_73_91
  · exact match_zero_fix ⟨74, by decide⟩ ⟨91, by decide⟩ p hp j hj hq fz1_74_91 fz2_74_91
  · exact match_zero_fix ⟨75, by decide⟩ ⟨91, by decide⟩ p hp j hj hq fz1_75_91 fz2_75_91
  · exact match_zero_fix ⟨76, by decide⟩ ⟨91, by decide⟩ p hp j hj hq fz1_76_91 fz2_76_91
  · exact match_zero_fix ⟨77, by decide⟩ ⟨91, by decide⟩ p hp j hj hq fz1_77_91 fz2_77_91
  · exact match_zero_fix ⟨78, by decide⟩ ⟨91, by decide⟩ p hp j hj hq fz1_78_91 fz2_78_91
  · exact match_zero_fix ⟨79, by decide⟩ ⟨91, by decide⟩ p hp j hj hq fz1_79_91 fz2_79_91
  · exact match_zero_fix ⟨80, by decide⟩ ⟨91, by decide⟩ p hp j hj hq fz1_80_91 fz2_80_91
  · exact match_zero_fix ⟨81, by decide⟩ ⟨91, by decide⟩ p hp j hj hq fz1_81_91 fz2_81_91
  · exact match_zero_fix ⟨82, by decide⟩ ⟨91, by decide⟩ p hp j hj hq fz1_82_91 fz2_82_91
  · exact match_zero_fix ⟨83, by decide⟩ ⟨91, by decide⟩ p hp j hj hq fz1_83_91 fz2_83_91
  · exact match_zero_fix ⟨84, by decide⟩ ⟨91, by decide⟩ p hp j hj hq fz1_84_91 fz2_84_91
  · exact match_zero_fix ⟨85, by decide⟩ ⟨91, by decide⟩ p hp j hj hq fz1_85_91 fz2_85_91
  · exact match_zero_fix ⟨86, by decide⟩ ⟨91, by decide⟩ p hp j hj hq fz1_86_91 fz2_86_91
  · exact match_zero_fix ⟨87, by decide⟩ ⟨91, by decide⟩ p hp j hj hq fz1_87_91 fz2_87_91
  · exact match_zero_fix ⟨88, by decide⟩ ⟨91, by decide⟩ p hp j hj hq fz1_88_91 fz2_88_91
  · exact match_zero_fix ⟨89, by decide⟩ ⟨91, by decide⟩ p hp j hj hq fz1_89_91 fz2_89_91
  · exact match_zero_fix ⟨90, by decide⟩ ⟨91, by decide⟩ p hp j hj hq fz1_90_91 fz2_90_91
  · exact pair_91_91 p hp hrep j hj hq
  · exact match_zero_fix ⟨92, by decide⟩ ⟨91, by decide⟩ p hp j hj hq fz1_92_91 fz2_92_91
  · exact match_zero_fix ⟨93, by decide⟩ ⟨91, by decide⟩ p hp j hj hq fz1_93_91 fz2_93_91
  · exact match_zero_fix ⟨94, by decide⟩ ⟨91, by decide⟩ p hp j hj hq fz1_94_91 fz2_94_91
  · exact match_zero_fix ⟨95, by decide⟩ ⟨91, by decide⟩ p hp j hj hq fz1_95_91 fz2_95_91
  · exact match_zero_fix ⟨96, by decide⟩ ⟨91, by decide⟩ p hp j hj hq fz1_96_91 fz2_96_91
  · exact match_zero_fix ⟨97, by decide⟩ ⟨91, by decide⟩ p hp j hj hq fz1_97_91 fz2_97_91
  · exact match_zero_fix ⟨98, by decide⟩ ⟨91, by decide⟩ p hp j hj hq fz1_98_91 fz2_98_91
  · exact match_zero_fix ⟨99, by decide⟩ ⟨91, by decide⟩ p hp j hj hq fz1_99_91 fz2_99_91
  · exact match_zero_fix ⟨100, by decide⟩ ⟨91, by decide⟩ p hp j hj hq fz1_100_91 fz2_100_91
  · exact match_zero_fix ⟨101, by decide⟩ ⟨91, by decide⟩ p hp j hj hq fz1_101_91 fz2_101_91
  · exact match_zero_fix ⟨102, by decide⟩ ⟨91, by decide⟩ p hp j hj hq fz1_102_91 fz2_102_91
  · exact match_zero_fix ⟨103, by decide⟩ ⟨91, by decide⟩ p hp j hj hq fz1_103_91 fz2_103_91
  · exact match_zero_fix ⟨104, by decide⟩ ⟨91, by decide⟩ p hp j hj hq fz1_104_91 fz2_104_91
  · exact match_zero_fix ⟨105, by decide⟩ ⟨91, by decide⟩ p hp j hj hq fz1_105_91 fz2_105_91
  · exact match_zero_fix ⟨106, by decide⟩ ⟨91, by decide⟩ p hp j hj hq fz1_106_91 fz2_106_91
  · exact match_zero_fix ⟨107, by decide⟩ ⟨91, by decide⟩ p hp j hj hq fz1_107_91 fz2_107_91
  · exact match_zero_fix ⟨108, by decide⟩ ⟨91, by decide⟩ p hp j hj hq fz1_108_91 fz2_108_91
  · exact match_zero_fix ⟨109, by decide⟩ ⟨91, by decide⟩ p hp j hj hq fz1_109_91 fz2_109_91
  · exact match_zero_fix ⟨110, by decide⟩ ⟨91, by decide⟩ p hp j hj hq fz1_110_91 fz2_110_91
  · exact match_zero_fix ⟨111, by decide⟩ ⟨91, by decide⟩ p hp j hj hq fz1_111_91 fz2_111_91
  · exact match_zero_fix ⟨112, by decide⟩ ⟨91, by decide⟩ p hp j hj hq fz1_112_91 fz2_112_91
  · exact match_zero_fix ⟨113, by decide⟩ ⟨91, by decide⟩ p hp j hj hq fz1_113_91 fz2_113_91
  · exact match_zero_fix ⟨114, by decide⟩ ⟨91, by decide⟩ p hp j hj hq fz1_114_91 fz2_114_91
  · exact match_zero_fix ⟨115, by decide⟩ ⟨91, by decide⟩ p hp j hj hq fz1_115_91 fz2_115_91
  · exact match_zero_fix ⟨116, by decide⟩ ⟨91, by decide⟩ p hp j hj hq fz1_116_91 fz2_116_91
  · exact pair_117_91 p hp hrep j hj hq
  · exact match_zero_fix ⟨118, by decide⟩ ⟨91, by decide⟩ p hp j hj hq fz1_118_91 fz2_118_91
  · exact match_zero_fix ⟨119, by decide⟩ ⟨91, by decide⟩ p hp j hj hq fz1_119_91 fz2_119_91
  · exact match_zero_fix ⟨120, by decide⟩ ⟨91, by decide⟩ p hp j hj hq fz1_120_91 fz2_120_91
  · exact match_zero_fix ⟨121, by decide⟩ ⟨91, by decide⟩ p hp j hj hq fz1_121_91 fz2_121_91
  · exact match_zero_fix ⟨122, by decide⟩ ⟨91, by decide⟩ p hp j hj hq fz1_122_91 fz2_122_91
  · exact pair_123_91 p hp hrep j hj hq
  · exact match_zero_fix ⟨124, by decide⟩ ⟨91, by decide⟩ p hp j hj hq fz1_124_91 fz2_124_91
  · exact match_zero_fix ⟨125, by decide⟩ ⟨91, by decide⟩ p hp j hj hq fz1_125_91 fz2_125_91
  · exact match_zero_fix ⟨126, by decide⟩ ⟨91, by decide⟩ p hp j hj hq fz1_126_91 fz2_126_91
  · exact match_zero_fix ⟨127, by decide⟩ ⟨91, by decide⟩ p hp j hj hq fz1_127_91 fz2_127_91
  · exact match_zero_fix ⟨128, by decide⟩ ⟨91, by decide⟩ p hp j hj hq fz1_128_91 fz2_128_91
  · exact pair_129_91 p hp hrep j hj hq
  · exact match_zero_fix ⟨130, by decide⟩ ⟨91, by decide⟩ p hp j hj hq fz1_130_91 fz2_130_91
  · exact match_zero_fix ⟨131, by decide⟩ ⟨91, by decide⟩ p hp j hj hq fz1_131_91 fz2_131_91
  · exact match_zero_fix ⟨132, by decide⟩ ⟨91, by decide⟩ p hp j hj hq fz1_132_91 fz2_132_91
  · exact match_zero_fix ⟨133, by decide⟩ ⟨91, by decide⟩ p hp j hj hq fz1_133_91 fz2_133_91
  · exact match_zero_fix ⟨134, by decide⟩ ⟨91, by decide⟩ p hp j hj hq fz1_134_91 fz2_134_91
  · exact pair_135_91 p hp hrep j hj hq
  · exact pair_136_91 p hp hrep j hj hq
  · exact match_zero_fix ⟨137, by decide⟩ ⟨91, by decide⟩ p hp j hj hq fz1_137_91 fz2_137_91
  · exact match_zero_fix ⟨138, by decide⟩ ⟨91, by decide⟩ p hp j hj hq fz1_138_91 fz2_138_91
  · exact match_zero_fix ⟨139, by decide⟩ ⟨91, by decide⟩ p hp j hj hq fz1_139_91 fz2_139_91
  · exact match_zero_fix ⟨140, by decide⟩ ⟨91, by decide⟩ p hp j hj hq fz1_140_91 fz2_140_91
  · exact match_zero_fix ⟨141, by decide⟩ ⟨91, by decide⟩ p hp j hj hq fz1_141_91 fz2_141_91
  · exact pair_142_91 p hp hrep j hj hq
  · exact match_zero_fix ⟨143, by decide⟩ ⟨91, by decide⟩ p hp j hj hq fz1_143_91 fz2_143_91
  · exact match_zero_fix ⟨144, by decide⟩ ⟨91, by decide⟩ p hp j hj hq fz1_144_91 fz2_144_91
  · exact match_zero_fix ⟨145, by decide⟩ ⟨91, by decide⟩ p hp j hj hq fz1_145_91 fz2_145_91
  · exact match_zero_fix ⟨146, by decide⟩ ⟨91, by decide⟩ p hp j hj hq fz1_146_91 fz2_146_91
  · exact pair_147_91 p hp hrep j hj hq

theorem master_92 (p : Nat) (hp : p < (Q2.transData.getD 92 []).length)
    (hrep : (Q2.cosetIsRep.getD 92 []).getD p false = true)
    (rK : Fin 148) (j : Nat) (hj : j < (repChars.getD rK.val []).length)
    (hq : (normIsRep.getD rK.val []).getD j false = true) :
    species (Q2.reps (⟨92, by decide⟩ : Fin 148)) (colE2 ⟨92, by decide⟩ p hp)
        (rowE2 rK j hj hq)
      = species (reps (⟨92, by decide⟩ : Fin 148))
        (colE1 ⟨92, by decide⟩ p (transLenTr ⟨92, by decide⟩ p hp)) (rowE1 rK j hj) := by
  rcases rK with ⟨nK, hnK⟩; interval_cases nK
  · exact match_zero_len ⟨0, by decide⟩ ⟨92, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨1, by decide⟩ ⟨92, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨2, by decide⟩ ⟨92, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨3, by decide⟩ ⟨92, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨4, by decide⟩ ⟨92, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨5, by decide⟩ ⟨92, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨6, by decide⟩ ⟨92, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨7, by decide⟩ ⟨92, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨8, by decide⟩ ⟨92, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨9, by decide⟩ ⟨92, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨10, by decide⟩ ⟨92, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨11, by decide⟩ ⟨92, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨12, by decide⟩ ⟨92, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨13, by decide⟩ ⟨92, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨14, by decide⟩ ⟨92, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨15, by decide⟩ ⟨92, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨16, by decide⟩ ⟨92, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨17, by decide⟩ ⟨92, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨18, by decide⟩ ⟨92, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨19, by decide⟩ ⟨92, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨20, by decide⟩ ⟨92, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨21, by decide⟩ ⟨92, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨22, by decide⟩ ⟨92, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨23, by decide⟩ ⟨92, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨24, by decide⟩ ⟨92, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨25, by decide⟩ ⟨92, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨26, by decide⟩ ⟨92, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨27, by decide⟩ ⟨92, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨28, by decide⟩ ⟨92, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨29, by decide⟩ ⟨92, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨30, by decide⟩ ⟨92, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨31, by decide⟩ ⟨92, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨32, by decide⟩ ⟨92, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨33, by decide⟩ ⟨92, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨34, by decide⟩ ⟨92, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨35, by decide⟩ ⟨92, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨36, by decide⟩ ⟨92, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨37, by decide⟩ ⟨92, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨38, by decide⟩ ⟨92, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨39, by decide⟩ ⟨92, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨40, by decide⟩ ⟨92, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨41, by decide⟩ ⟨92, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨42, by decide⟩ ⟨92, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨43, by decide⟩ ⟨92, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨44, by decide⟩ ⟨92, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨45, by decide⟩ ⟨92, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨46, by decide⟩ ⟨92, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨47, by decide⟩ ⟨92, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨48, by decide⟩ ⟨92, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨49, by decide⟩ ⟨92, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨50, by decide⟩ ⟨92, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨51, by decide⟩ ⟨92, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨52, by decide⟩ ⟨92, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨53, by decide⟩ ⟨92, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨54, by decide⟩ ⟨92, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_fix ⟨55, by decide⟩ ⟨92, by decide⟩ p hp j hj hq fz1_55_92 fz2_55_92
  · exact match_zero_fix ⟨56, by decide⟩ ⟨92, by decide⟩ p hp j hj hq fz1_56_92 fz2_56_92
  · exact match_zero_fix ⟨57, by decide⟩ ⟨92, by decide⟩ p hp j hj hq fz1_57_92 fz2_57_92
  · exact match_zero_fix ⟨58, by decide⟩ ⟨92, by decide⟩ p hp j hj hq fz1_58_92 fz2_58_92
  · exact match_zero_fix ⟨59, by decide⟩ ⟨92, by decide⟩ p hp j hj hq fz1_59_92 fz2_59_92
  · exact match_zero_fix ⟨60, by decide⟩ ⟨92, by decide⟩ p hp j hj hq fz1_60_92 fz2_60_92
  · exact match_zero_fix ⟨61, by decide⟩ ⟨92, by decide⟩ p hp j hj hq fz1_61_92 fz2_61_92
  · exact match_zero_fix ⟨62, by decide⟩ ⟨92, by decide⟩ p hp j hj hq fz1_62_92 fz2_62_92
  · exact match_zero_fix ⟨63, by decide⟩ ⟨92, by decide⟩ p hp j hj hq fz1_63_92 fz2_63_92
  · exact match_zero_fix ⟨64, by decide⟩ ⟨92, by decide⟩ p hp j hj hq fz1_64_92 fz2_64_92
  · exact match_zero_fix ⟨65, by decide⟩ ⟨92, by decide⟩ p hp j hj hq fz1_65_92 fz2_65_92
  · exact match_zero_fix ⟨66, by decide⟩ ⟨92, by decide⟩ p hp j hj hq fz1_66_92 fz2_66_92
  · exact match_zero_fix ⟨67, by decide⟩ ⟨92, by decide⟩ p hp j hj hq fz1_67_92 fz2_67_92
  · exact match_zero_fix ⟨68, by decide⟩ ⟨92, by decide⟩ p hp j hj hq fz1_68_92 fz2_68_92
  · exact match_zero_fix ⟨69, by decide⟩ ⟨92, by decide⟩ p hp j hj hq fz1_69_92 fz2_69_92
  · exact match_zero_fix ⟨70, by decide⟩ ⟨92, by decide⟩ p hp j hj hq fz1_70_92 fz2_70_92
  · exact match_zero_fix ⟨71, by decide⟩ ⟨92, by decide⟩ p hp j hj hq fz1_71_92 fz2_71_92
  · exact match_zero_fix ⟨72, by decide⟩ ⟨92, by decide⟩ p hp j hj hq fz1_72_92 fz2_72_92
  · exact match_zero_fix ⟨73, by decide⟩ ⟨92, by decide⟩ p hp j hj hq fz1_73_92 fz2_73_92
  · exact match_zero_fix ⟨74, by decide⟩ ⟨92, by decide⟩ p hp j hj hq fz1_74_92 fz2_74_92
  · exact match_zero_fix ⟨75, by decide⟩ ⟨92, by decide⟩ p hp j hj hq fz1_75_92 fz2_75_92
  · exact match_zero_fix ⟨76, by decide⟩ ⟨92, by decide⟩ p hp j hj hq fz1_76_92 fz2_76_92
  · exact match_zero_fix ⟨77, by decide⟩ ⟨92, by decide⟩ p hp j hj hq fz1_77_92 fz2_77_92
  · exact match_zero_fix ⟨78, by decide⟩ ⟨92, by decide⟩ p hp j hj hq fz1_78_92 fz2_78_92
  · exact match_zero_fix ⟨79, by decide⟩ ⟨92, by decide⟩ p hp j hj hq fz1_79_92 fz2_79_92
  · exact match_zero_fix ⟨80, by decide⟩ ⟨92, by decide⟩ p hp j hj hq fz1_80_92 fz2_80_92
  · exact match_zero_fix ⟨81, by decide⟩ ⟨92, by decide⟩ p hp j hj hq fz1_81_92 fz2_81_92
  · exact match_zero_fix ⟨82, by decide⟩ ⟨92, by decide⟩ p hp j hj hq fz1_82_92 fz2_82_92
  · exact match_zero_fix ⟨83, by decide⟩ ⟨92, by decide⟩ p hp j hj hq fz1_83_92 fz2_83_92
  · exact match_zero_fix ⟨84, by decide⟩ ⟨92, by decide⟩ p hp j hj hq fz1_84_92 fz2_84_92
  · exact match_zero_fix ⟨85, by decide⟩ ⟨92, by decide⟩ p hp j hj hq fz1_85_92 fz2_85_92
  · exact match_zero_fix ⟨86, by decide⟩ ⟨92, by decide⟩ p hp j hj hq fz1_86_92 fz2_86_92
  · exact match_zero_fix ⟨87, by decide⟩ ⟨92, by decide⟩ p hp j hj hq fz1_87_92 fz2_87_92
  · exact match_zero_fix ⟨88, by decide⟩ ⟨92, by decide⟩ p hp j hj hq fz1_88_92 fz2_88_92
  · exact match_zero_fix ⟨89, by decide⟩ ⟨92, by decide⟩ p hp j hj hq fz1_89_92 fz2_89_92
  · exact match_zero_fix ⟨90, by decide⟩ ⟨92, by decide⟩ p hp j hj hq fz1_90_92 fz2_90_92
  · exact match_zero_fix ⟨91, by decide⟩ ⟨92, by decide⟩ p hp j hj hq fz1_91_92 fz2_91_92
  · exact pair_92_92 p hp hrep j hj hq
  · exact match_zero_fix ⟨93, by decide⟩ ⟨92, by decide⟩ p hp j hj hq fz1_93_92 fz2_93_92
  · exact match_zero_fix ⟨94, by decide⟩ ⟨92, by decide⟩ p hp j hj hq fz1_94_92 fz2_94_92
  · exact match_zero_fix ⟨95, by decide⟩ ⟨92, by decide⟩ p hp j hj hq fz1_95_92 fz2_95_92
  · exact match_zero_fix ⟨96, by decide⟩ ⟨92, by decide⟩ p hp j hj hq fz1_96_92 fz2_96_92
  · exact match_zero_fix ⟨97, by decide⟩ ⟨92, by decide⟩ p hp j hj hq fz1_97_92 fz2_97_92
  · exact match_zero_fix ⟨98, by decide⟩ ⟨92, by decide⟩ p hp j hj hq fz1_98_92 fz2_98_92
  · exact match_zero_fix ⟨99, by decide⟩ ⟨92, by decide⟩ p hp j hj hq fz1_99_92 fz2_99_92
  · exact match_zero_fix ⟨100, by decide⟩ ⟨92, by decide⟩ p hp j hj hq fz1_100_92 fz2_100_92
  · exact match_zero_fix ⟨101, by decide⟩ ⟨92, by decide⟩ p hp j hj hq fz1_101_92 fz2_101_92
  · exact match_zero_fix ⟨102, by decide⟩ ⟨92, by decide⟩ p hp j hj hq fz1_102_92 fz2_102_92
  · exact match_zero_fix ⟨103, by decide⟩ ⟨92, by decide⟩ p hp j hj hq fz1_103_92 fz2_103_92
  · exact match_zero_fix ⟨104, by decide⟩ ⟨92, by decide⟩ p hp j hj hq fz1_104_92 fz2_104_92
  · exact match_zero_fix ⟨105, by decide⟩ ⟨92, by decide⟩ p hp j hj hq fz1_105_92 fz2_105_92
  · exact match_zero_fix ⟨106, by decide⟩ ⟨92, by decide⟩ p hp j hj hq fz1_106_92 fz2_106_92
  · exact match_zero_fix ⟨107, by decide⟩ ⟨92, by decide⟩ p hp j hj hq fz1_107_92 fz2_107_92
  · exact match_zero_fix ⟨108, by decide⟩ ⟨92, by decide⟩ p hp j hj hq fz1_108_92 fz2_108_92
  · exact match_zero_fix ⟨109, by decide⟩ ⟨92, by decide⟩ p hp j hj hq fz1_109_92 fz2_109_92
  · exact match_zero_fix ⟨110, by decide⟩ ⟨92, by decide⟩ p hp j hj hq fz1_110_92 fz2_110_92
  · exact match_zero_fix ⟨111, by decide⟩ ⟨92, by decide⟩ p hp j hj hq fz1_111_92 fz2_111_92
  · exact match_zero_fix ⟨112, by decide⟩ ⟨92, by decide⟩ p hp j hj hq fz1_112_92 fz2_112_92
  · exact match_zero_fix ⟨113, by decide⟩ ⟨92, by decide⟩ p hp j hj hq fz1_113_92 fz2_113_92
  · exact match_zero_fix ⟨114, by decide⟩ ⟨92, by decide⟩ p hp j hj hq fz1_114_92 fz2_114_92
  · exact match_zero_fix ⟨115, by decide⟩ ⟨92, by decide⟩ p hp j hj hq fz1_115_92 fz2_115_92
  · exact match_zero_fix ⟨116, by decide⟩ ⟨92, by decide⟩ p hp j hj hq fz1_116_92 fz2_116_92
  · exact match_zero_fix ⟨117, by decide⟩ ⟨92, by decide⟩ p hp j hj hq fz1_117_92 fz2_117_92
  · exact pair_118_92 p hp hrep j hj hq
  · exact match_zero_fix ⟨119, by decide⟩ ⟨92, by decide⟩ p hp j hj hq fz1_119_92 fz2_119_92
  · exact match_zero_fix ⟨120, by decide⟩ ⟨92, by decide⟩ p hp j hj hq fz1_120_92 fz2_120_92
  · exact match_zero_fix ⟨121, by decide⟩ ⟨92, by decide⟩ p hp j hj hq fz1_121_92 fz2_121_92
  · exact match_zero_fix ⟨122, by decide⟩ ⟨92, by decide⟩ p hp j hj hq fz1_122_92 fz2_122_92
  · exact match_zero_fix ⟨123, by decide⟩ ⟨92, by decide⟩ p hp j hj hq fz1_123_92 fz2_123_92
  · exact pair_124_92 p hp hrep j hj hq
  · exact match_zero_fix ⟨125, by decide⟩ ⟨92, by decide⟩ p hp j hj hq fz1_125_92 fz2_125_92
  · exact match_zero_fix ⟨126, by decide⟩ ⟨92, by decide⟩ p hp j hj hq fz1_126_92 fz2_126_92
  · exact match_zero_fix ⟨127, by decide⟩ ⟨92, by decide⟩ p hp j hj hq fz1_127_92 fz2_127_92
  · exact match_zero_fix ⟨128, by decide⟩ ⟨92, by decide⟩ p hp j hj hq fz1_128_92 fz2_128_92
  · exact match_zero_fix ⟨129, by decide⟩ ⟨92, by decide⟩ p hp j hj hq fz1_129_92 fz2_129_92
  · exact pair_130_92 p hp hrep j hj hq
  · exact pair_131_92 p hp hrep j hj hq
  · exact match_zero_fix ⟨132, by decide⟩ ⟨92, by decide⟩ p hp j hj hq fz1_132_92 fz2_132_92
  · exact match_zero_fix ⟨133, by decide⟩ ⟨92, by decide⟩ p hp j hj hq fz1_133_92 fz2_133_92
  · exact match_zero_fix ⟨134, by decide⟩ ⟨92, by decide⟩ p hp j hj hq fz1_134_92 fz2_134_92
  · exact match_zero_fix ⟨135, by decide⟩ ⟨92, by decide⟩ p hp j hj hq fz1_135_92 fz2_135_92
  · exact match_zero_fix ⟨136, by decide⟩ ⟨92, by decide⟩ p hp j hj hq fz1_136_92 fz2_136_92
  · exact pair_137_92 p hp hrep j hj hq
  · exact match_zero_fix ⟨138, by decide⟩ ⟨92, by decide⟩ p hp j hj hq fz1_138_92 fz2_138_92
  · exact match_zero_fix ⟨139, by decide⟩ ⟨92, by decide⟩ p hp j hj hq fz1_139_92 fz2_139_92
  · exact match_zero_fix ⟨140, by decide⟩ ⟨92, by decide⟩ p hp j hj hq fz1_140_92 fz2_140_92
  · exact match_zero_fix ⟨141, by decide⟩ ⟨92, by decide⟩ p hp j hj hq fz1_141_92 fz2_141_92
  · exact pair_142_92 p hp hrep j hj hq
  · exact match_zero_fix ⟨143, by decide⟩ ⟨92, by decide⟩ p hp j hj hq fz1_143_92 fz2_143_92
  · exact match_zero_fix ⟨144, by decide⟩ ⟨92, by decide⟩ p hp j hj hq fz1_144_92 fz2_144_92
  · exact match_zero_fix ⟨145, by decide⟩ ⟨92, by decide⟩ p hp j hj hq fz1_145_92 fz2_145_92
  · exact match_zero_fix ⟨146, by decide⟩ ⟨92, by decide⟩ p hp j hj hq fz1_146_92 fz2_146_92
  · exact pair_147_92 p hp hrep j hj hq

theorem master_93 (p : Nat) (hp : p < (Q2.transData.getD 93 []).length)
    (hrep : (Q2.cosetIsRep.getD 93 []).getD p false = true)
    (rK : Fin 148) (j : Nat) (hj : j < (repChars.getD rK.val []).length)
    (hq : (normIsRep.getD rK.val []).getD j false = true) :
    species (Q2.reps (⟨93, by decide⟩ : Fin 148)) (colE2 ⟨93, by decide⟩ p hp)
        (rowE2 rK j hj hq)
      = species (reps (⟨93, by decide⟩ : Fin 148))
        (colE1 ⟨93, by decide⟩ p (transLenTr ⟨93, by decide⟩ p hp)) (rowE1 rK j hj) := by
  rcases rK with ⟨nK, hnK⟩; interval_cases nK
  · exact match_zero_len ⟨0, by decide⟩ ⟨93, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨1, by decide⟩ ⟨93, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨2, by decide⟩ ⟨93, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨3, by decide⟩ ⟨93, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨4, by decide⟩ ⟨93, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨5, by decide⟩ ⟨93, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨6, by decide⟩ ⟨93, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨7, by decide⟩ ⟨93, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨8, by decide⟩ ⟨93, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨9, by decide⟩ ⟨93, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨10, by decide⟩ ⟨93, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨11, by decide⟩ ⟨93, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨12, by decide⟩ ⟨93, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨13, by decide⟩ ⟨93, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨14, by decide⟩ ⟨93, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨15, by decide⟩ ⟨93, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨16, by decide⟩ ⟨93, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨17, by decide⟩ ⟨93, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨18, by decide⟩ ⟨93, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨19, by decide⟩ ⟨93, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨20, by decide⟩ ⟨93, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨21, by decide⟩ ⟨93, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨22, by decide⟩ ⟨93, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨23, by decide⟩ ⟨93, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨24, by decide⟩ ⟨93, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨25, by decide⟩ ⟨93, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨26, by decide⟩ ⟨93, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨27, by decide⟩ ⟨93, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨28, by decide⟩ ⟨93, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨29, by decide⟩ ⟨93, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨30, by decide⟩ ⟨93, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨31, by decide⟩ ⟨93, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨32, by decide⟩ ⟨93, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨33, by decide⟩ ⟨93, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨34, by decide⟩ ⟨93, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨35, by decide⟩ ⟨93, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨36, by decide⟩ ⟨93, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨37, by decide⟩ ⟨93, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨38, by decide⟩ ⟨93, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨39, by decide⟩ ⟨93, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨40, by decide⟩ ⟨93, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨41, by decide⟩ ⟨93, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨42, by decide⟩ ⟨93, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨43, by decide⟩ ⟨93, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨44, by decide⟩ ⟨93, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨45, by decide⟩ ⟨93, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨46, by decide⟩ ⟨93, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨47, by decide⟩ ⟨93, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨48, by decide⟩ ⟨93, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨49, by decide⟩ ⟨93, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨50, by decide⟩ ⟨93, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨51, by decide⟩ ⟨93, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨52, by decide⟩ ⟨93, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨53, by decide⟩ ⟨93, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨54, by decide⟩ ⟨93, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_fix ⟨55, by decide⟩ ⟨93, by decide⟩ p hp j hj hq fz1_55_93 fz2_55_93
  · exact match_zero_fix ⟨56, by decide⟩ ⟨93, by decide⟩ p hp j hj hq fz1_56_93 fz2_56_93
  · exact match_zero_fix ⟨57, by decide⟩ ⟨93, by decide⟩ p hp j hj hq fz1_57_93 fz2_57_93
  · exact match_zero_fix ⟨58, by decide⟩ ⟨93, by decide⟩ p hp j hj hq fz1_58_93 fz2_58_93
  · exact match_zero_fix ⟨59, by decide⟩ ⟨93, by decide⟩ p hp j hj hq fz1_59_93 fz2_59_93
  · exact match_zero_fix ⟨60, by decide⟩ ⟨93, by decide⟩ p hp j hj hq fz1_60_93 fz2_60_93
  · exact match_zero_fix ⟨61, by decide⟩ ⟨93, by decide⟩ p hp j hj hq fz1_61_93 fz2_61_93
  · exact match_zero_fix ⟨62, by decide⟩ ⟨93, by decide⟩ p hp j hj hq fz1_62_93 fz2_62_93
  · exact match_zero_fix ⟨63, by decide⟩ ⟨93, by decide⟩ p hp j hj hq fz1_63_93 fz2_63_93
  · exact match_zero_fix ⟨64, by decide⟩ ⟨93, by decide⟩ p hp j hj hq fz1_64_93 fz2_64_93
  · exact match_zero_fix ⟨65, by decide⟩ ⟨93, by decide⟩ p hp j hj hq fz1_65_93 fz2_65_93
  · exact match_zero_fix ⟨66, by decide⟩ ⟨93, by decide⟩ p hp j hj hq fz1_66_93 fz2_66_93
  · exact match_zero_fix ⟨67, by decide⟩ ⟨93, by decide⟩ p hp j hj hq fz1_67_93 fz2_67_93
  · exact match_zero_fix ⟨68, by decide⟩ ⟨93, by decide⟩ p hp j hj hq fz1_68_93 fz2_68_93
  · exact match_zero_fix ⟨69, by decide⟩ ⟨93, by decide⟩ p hp j hj hq fz1_69_93 fz2_69_93
  · exact match_zero_fix ⟨70, by decide⟩ ⟨93, by decide⟩ p hp j hj hq fz1_70_93 fz2_70_93
  · exact match_zero_fix ⟨71, by decide⟩ ⟨93, by decide⟩ p hp j hj hq fz1_71_93 fz2_71_93
  · exact match_zero_fix ⟨72, by decide⟩ ⟨93, by decide⟩ p hp j hj hq fz1_72_93 fz2_72_93
  · exact match_zero_fix ⟨73, by decide⟩ ⟨93, by decide⟩ p hp j hj hq fz1_73_93 fz2_73_93
  · exact match_zero_fix ⟨74, by decide⟩ ⟨93, by decide⟩ p hp j hj hq fz1_74_93 fz2_74_93
  · exact match_zero_fix ⟨75, by decide⟩ ⟨93, by decide⟩ p hp j hj hq fz1_75_93 fz2_75_93
  · exact match_zero_fix ⟨76, by decide⟩ ⟨93, by decide⟩ p hp j hj hq fz1_76_93 fz2_76_93
  · exact match_zero_fix ⟨77, by decide⟩ ⟨93, by decide⟩ p hp j hj hq fz1_77_93 fz2_77_93
  · exact match_zero_fix ⟨78, by decide⟩ ⟨93, by decide⟩ p hp j hj hq fz1_78_93 fz2_78_93
  · exact match_zero_fix ⟨79, by decide⟩ ⟨93, by decide⟩ p hp j hj hq fz1_79_93 fz2_79_93
  · exact match_zero_fix ⟨80, by decide⟩ ⟨93, by decide⟩ p hp j hj hq fz1_80_93 fz2_80_93
  · exact match_zero_fix ⟨81, by decide⟩ ⟨93, by decide⟩ p hp j hj hq fz1_81_93 fz2_81_93
  · exact match_zero_fix ⟨82, by decide⟩ ⟨93, by decide⟩ p hp j hj hq fz1_82_93 fz2_82_93
  · exact match_zero_fix ⟨83, by decide⟩ ⟨93, by decide⟩ p hp j hj hq fz1_83_93 fz2_83_93
  · exact match_zero_fix ⟨84, by decide⟩ ⟨93, by decide⟩ p hp j hj hq fz1_84_93 fz2_84_93
  · exact match_zero_fix ⟨85, by decide⟩ ⟨93, by decide⟩ p hp j hj hq fz1_85_93 fz2_85_93
  · exact match_zero_fix ⟨86, by decide⟩ ⟨93, by decide⟩ p hp j hj hq fz1_86_93 fz2_86_93
  · exact match_zero_fix ⟨87, by decide⟩ ⟨93, by decide⟩ p hp j hj hq fz1_87_93 fz2_87_93
  · exact match_zero_fix ⟨88, by decide⟩ ⟨93, by decide⟩ p hp j hj hq fz1_88_93 fz2_88_93
  · exact match_zero_fix ⟨89, by decide⟩ ⟨93, by decide⟩ p hp j hj hq fz1_89_93 fz2_89_93
  · exact match_zero_fix ⟨90, by decide⟩ ⟨93, by decide⟩ p hp j hj hq fz1_90_93 fz2_90_93
  · exact match_zero_fix ⟨91, by decide⟩ ⟨93, by decide⟩ p hp j hj hq fz1_91_93 fz2_91_93
  · exact match_zero_fix ⟨92, by decide⟩ ⟨93, by decide⟩ p hp j hj hq fz1_92_93 fz2_92_93
  · exact pair_93_93 p hp hrep j hj hq
  · exact match_zero_fix ⟨94, by decide⟩ ⟨93, by decide⟩ p hp j hj hq fz1_94_93 fz2_94_93
  · exact match_zero_fix ⟨95, by decide⟩ ⟨93, by decide⟩ p hp j hj hq fz1_95_93 fz2_95_93
  · exact match_zero_fix ⟨96, by decide⟩ ⟨93, by decide⟩ p hp j hj hq fz1_96_93 fz2_96_93
  · exact match_zero_fix ⟨97, by decide⟩ ⟨93, by decide⟩ p hp j hj hq fz1_97_93 fz2_97_93
  · exact match_zero_fix ⟨98, by decide⟩ ⟨93, by decide⟩ p hp j hj hq fz1_98_93 fz2_98_93
  · exact match_zero_fix ⟨99, by decide⟩ ⟨93, by decide⟩ p hp j hj hq fz1_99_93 fz2_99_93
  · exact match_zero_fix ⟨100, by decide⟩ ⟨93, by decide⟩ p hp j hj hq fz1_100_93 fz2_100_93
  · exact match_zero_fix ⟨101, by decide⟩ ⟨93, by decide⟩ p hp j hj hq fz1_101_93 fz2_101_93
  · exact match_zero_fix ⟨102, by decide⟩ ⟨93, by decide⟩ p hp j hj hq fz1_102_93 fz2_102_93
  · exact match_zero_fix ⟨103, by decide⟩ ⟨93, by decide⟩ p hp j hj hq fz1_103_93 fz2_103_93
  · exact match_zero_fix ⟨104, by decide⟩ ⟨93, by decide⟩ p hp j hj hq fz1_104_93 fz2_104_93
  · exact match_zero_fix ⟨105, by decide⟩ ⟨93, by decide⟩ p hp j hj hq fz1_105_93 fz2_105_93
  · exact match_zero_fix ⟨106, by decide⟩ ⟨93, by decide⟩ p hp j hj hq fz1_106_93 fz2_106_93
  · exact match_zero_fix ⟨107, by decide⟩ ⟨93, by decide⟩ p hp j hj hq fz1_107_93 fz2_107_93
  · exact match_zero_fix ⟨108, by decide⟩ ⟨93, by decide⟩ p hp j hj hq fz1_108_93 fz2_108_93
  · exact match_zero_fix ⟨109, by decide⟩ ⟨93, by decide⟩ p hp j hj hq fz1_109_93 fz2_109_93
  · exact match_zero_fix ⟨110, by decide⟩ ⟨93, by decide⟩ p hp j hj hq fz1_110_93 fz2_110_93
  · exact match_zero_fix ⟨111, by decide⟩ ⟨93, by decide⟩ p hp j hj hq fz1_111_93 fz2_111_93
  · exact match_zero_fix ⟨112, by decide⟩ ⟨93, by decide⟩ p hp j hj hq fz1_112_93 fz2_112_93
  · exact match_zero_fix ⟨113, by decide⟩ ⟨93, by decide⟩ p hp j hj hq fz1_113_93 fz2_113_93
  · exact match_zero_fix ⟨114, by decide⟩ ⟨93, by decide⟩ p hp j hj hq fz1_114_93 fz2_114_93
  · exact match_zero_fix ⟨115, by decide⟩ ⟨93, by decide⟩ p hp j hj hq fz1_115_93 fz2_115_93
  · exact match_zero_fix ⟨116, by decide⟩ ⟨93, by decide⟩ p hp j hj hq fz1_116_93 fz2_116_93
  · exact match_zero_fix ⟨117, by decide⟩ ⟨93, by decide⟩ p hp j hj hq fz1_117_93 fz2_117_93
  · exact match_zero_fix ⟨118, by decide⟩ ⟨93, by decide⟩ p hp j hj hq fz1_118_93 fz2_118_93
  · exact pair_119_93 p hp hrep j hj hq
  · exact match_zero_fix ⟨120, by decide⟩ ⟨93, by decide⟩ p hp j hj hq fz1_120_93 fz2_120_93
  · exact match_zero_fix ⟨121, by decide⟩ ⟨93, by decide⟩ p hp j hj hq fz1_121_93 fz2_121_93
  · exact match_zero_fix ⟨122, by decide⟩ ⟨93, by decide⟩ p hp j hj hq fz1_122_93 fz2_122_93
  · exact match_zero_fix ⟨123, by decide⟩ ⟨93, by decide⟩ p hp j hj hq fz1_123_93 fz2_123_93
  · exact match_zero_fix ⟨124, by decide⟩ ⟨93, by decide⟩ p hp j hj hq fz1_124_93 fz2_124_93
  · exact pair_125_93 p hp hrep j hj hq
  · exact pair_126_93 p hp hrep j hj hq
  · exact match_zero_fix ⟨127, by decide⟩ ⟨93, by decide⟩ p hp j hj hq fz1_127_93 fz2_127_93
  · exact match_zero_fix ⟨128, by decide⟩ ⟨93, by decide⟩ p hp j hj hq fz1_128_93 fz2_128_93
  · exact match_zero_fix ⟨129, by decide⟩ ⟨93, by decide⟩ p hp j hj hq fz1_129_93 fz2_129_93
  · exact match_zero_fix ⟨130, by decide⟩ ⟨93, by decide⟩ p hp j hj hq fz1_130_93 fz2_130_93
  · exact match_zero_fix ⟨131, by decide⟩ ⟨93, by decide⟩ p hp j hj hq fz1_131_93 fz2_131_93
  · exact pair_132_93 p hp hrep j hj hq
  · exact match_zero_fix ⟨133, by decide⟩ ⟨93, by decide⟩ p hp j hj hq fz1_133_93 fz2_133_93
  · exact match_zero_fix ⟨134, by decide⟩ ⟨93, by decide⟩ p hp j hj hq fz1_134_93 fz2_134_93
  · exact match_zero_fix ⟨135, by decide⟩ ⟨93, by decide⟩ p hp j hj hq fz1_135_93 fz2_135_93
  · exact match_zero_fix ⟨136, by decide⟩ ⟨93, by decide⟩ p hp j hj hq fz1_136_93 fz2_136_93
  · exact match_zero_fix ⟨137, by decide⟩ ⟨93, by decide⟩ p hp j hj hq fz1_137_93 fz2_137_93
  · exact pair_138_93 p hp hrep j hj hq
  · exact match_zero_fix ⟨139, by decide⟩ ⟨93, by decide⟩ p hp j hj hq fz1_139_93 fz2_139_93
  · exact match_zero_fix ⟨140, by decide⟩ ⟨93, by decide⟩ p hp j hj hq fz1_140_93 fz2_140_93
  · exact match_zero_fix ⟨141, by decide⟩ ⟨93, by decide⟩ p hp j hj hq fz1_141_93 fz2_141_93
  · exact pair_142_93 p hp hrep j hj hq
  · exact match_zero_fix ⟨143, by decide⟩ ⟨93, by decide⟩ p hp j hj hq fz1_143_93 fz2_143_93
  · exact match_zero_fix ⟨144, by decide⟩ ⟨93, by decide⟩ p hp j hj hq fz1_144_93 fz2_144_93
  · exact match_zero_fix ⟨145, by decide⟩ ⟨93, by decide⟩ p hp j hj hq fz1_145_93 fz2_145_93
  · exact match_zero_fix ⟨146, by decide⟩ ⟨93, by decide⟩ p hp j hj hq fz1_146_93 fz2_146_93
  · exact pair_147_93 p hp hrep j hj hq

theorem master_94 (p : Nat) (hp : p < (Q2.transData.getD 94 []).length)
    (hrep : (Q2.cosetIsRep.getD 94 []).getD p false = true)
    (rK : Fin 148) (j : Nat) (hj : j < (repChars.getD rK.val []).length)
    (hq : (normIsRep.getD rK.val []).getD j false = true) :
    species (Q2.reps (⟨94, by decide⟩ : Fin 148)) (colE2 ⟨94, by decide⟩ p hp)
        (rowE2 rK j hj hq)
      = species (reps (⟨94, by decide⟩ : Fin 148))
        (colE1 ⟨94, by decide⟩ p (transLenTr ⟨94, by decide⟩ p hp)) (rowE1 rK j hj) := by
  rcases rK with ⟨nK, hnK⟩; interval_cases nK
  · exact match_zero_len ⟨0, by decide⟩ ⟨94, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨1, by decide⟩ ⟨94, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨2, by decide⟩ ⟨94, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨3, by decide⟩ ⟨94, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨4, by decide⟩ ⟨94, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨5, by decide⟩ ⟨94, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨6, by decide⟩ ⟨94, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨7, by decide⟩ ⟨94, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨8, by decide⟩ ⟨94, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨9, by decide⟩ ⟨94, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨10, by decide⟩ ⟨94, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨11, by decide⟩ ⟨94, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨12, by decide⟩ ⟨94, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨13, by decide⟩ ⟨94, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨14, by decide⟩ ⟨94, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨15, by decide⟩ ⟨94, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨16, by decide⟩ ⟨94, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨17, by decide⟩ ⟨94, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨18, by decide⟩ ⟨94, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨19, by decide⟩ ⟨94, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨20, by decide⟩ ⟨94, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨21, by decide⟩ ⟨94, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨22, by decide⟩ ⟨94, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨23, by decide⟩ ⟨94, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨24, by decide⟩ ⟨94, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨25, by decide⟩ ⟨94, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨26, by decide⟩ ⟨94, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨27, by decide⟩ ⟨94, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨28, by decide⟩ ⟨94, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨29, by decide⟩ ⟨94, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨30, by decide⟩ ⟨94, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨31, by decide⟩ ⟨94, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨32, by decide⟩ ⟨94, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨33, by decide⟩ ⟨94, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨34, by decide⟩ ⟨94, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨35, by decide⟩ ⟨94, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨36, by decide⟩ ⟨94, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨37, by decide⟩ ⟨94, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨38, by decide⟩ ⟨94, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨39, by decide⟩ ⟨94, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨40, by decide⟩ ⟨94, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨41, by decide⟩ ⟨94, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨42, by decide⟩ ⟨94, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨43, by decide⟩ ⟨94, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨44, by decide⟩ ⟨94, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨45, by decide⟩ ⟨94, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨46, by decide⟩ ⟨94, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨47, by decide⟩ ⟨94, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨48, by decide⟩ ⟨94, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨49, by decide⟩ ⟨94, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨50, by decide⟩ ⟨94, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨51, by decide⟩ ⟨94, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨52, by decide⟩ ⟨94, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨53, by decide⟩ ⟨94, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨54, by decide⟩ ⟨94, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_fix ⟨55, by decide⟩ ⟨94, by decide⟩ p hp j hj hq fz1_55_94 fz2_55_94
  · exact match_zero_fix ⟨56, by decide⟩ ⟨94, by decide⟩ p hp j hj hq fz1_56_94 fz2_56_94
  · exact match_zero_fix ⟨57, by decide⟩ ⟨94, by decide⟩ p hp j hj hq fz1_57_94 fz2_57_94
  · exact match_zero_fix ⟨58, by decide⟩ ⟨94, by decide⟩ p hp j hj hq fz1_58_94 fz2_58_94
  · exact match_zero_fix ⟨59, by decide⟩ ⟨94, by decide⟩ p hp j hj hq fz1_59_94 fz2_59_94
  · exact match_zero_fix ⟨60, by decide⟩ ⟨94, by decide⟩ p hp j hj hq fz1_60_94 fz2_60_94
  · exact match_zero_fix ⟨61, by decide⟩ ⟨94, by decide⟩ p hp j hj hq fz1_61_94 fz2_61_94
  · exact match_zero_fix ⟨62, by decide⟩ ⟨94, by decide⟩ p hp j hj hq fz1_62_94 fz2_62_94
  · exact match_zero_fix ⟨63, by decide⟩ ⟨94, by decide⟩ p hp j hj hq fz1_63_94 fz2_63_94
  · exact match_zero_fix ⟨64, by decide⟩ ⟨94, by decide⟩ p hp j hj hq fz1_64_94 fz2_64_94
  · exact match_zero_fix ⟨65, by decide⟩ ⟨94, by decide⟩ p hp j hj hq fz1_65_94 fz2_65_94
  · exact match_zero_fix ⟨66, by decide⟩ ⟨94, by decide⟩ p hp j hj hq fz1_66_94 fz2_66_94
  · exact match_zero_fix ⟨67, by decide⟩ ⟨94, by decide⟩ p hp j hj hq fz1_67_94 fz2_67_94
  · exact match_zero_fix ⟨68, by decide⟩ ⟨94, by decide⟩ p hp j hj hq fz1_68_94 fz2_68_94
  · exact match_zero_fix ⟨69, by decide⟩ ⟨94, by decide⟩ p hp j hj hq fz1_69_94 fz2_69_94
  · exact match_zero_fix ⟨70, by decide⟩ ⟨94, by decide⟩ p hp j hj hq fz1_70_94 fz2_70_94
  · exact match_zero_fix ⟨71, by decide⟩ ⟨94, by decide⟩ p hp j hj hq fz1_71_94 fz2_71_94
  · exact match_zero_fix ⟨72, by decide⟩ ⟨94, by decide⟩ p hp j hj hq fz1_72_94 fz2_72_94
  · exact match_zero_fix ⟨73, by decide⟩ ⟨94, by decide⟩ p hp j hj hq fz1_73_94 fz2_73_94
  · exact match_zero_fix ⟨74, by decide⟩ ⟨94, by decide⟩ p hp j hj hq fz1_74_94 fz2_74_94
  · exact match_zero_fix ⟨75, by decide⟩ ⟨94, by decide⟩ p hp j hj hq fz1_75_94 fz2_75_94
  · exact match_zero_fix ⟨76, by decide⟩ ⟨94, by decide⟩ p hp j hj hq fz1_76_94 fz2_76_94
  · exact match_zero_fix ⟨77, by decide⟩ ⟨94, by decide⟩ p hp j hj hq fz1_77_94 fz2_77_94
  · exact match_zero_fix ⟨78, by decide⟩ ⟨94, by decide⟩ p hp j hj hq fz1_78_94 fz2_78_94
  · exact match_zero_fix ⟨79, by decide⟩ ⟨94, by decide⟩ p hp j hj hq fz1_79_94 fz2_79_94
  · exact match_zero_fix ⟨80, by decide⟩ ⟨94, by decide⟩ p hp j hj hq fz1_80_94 fz2_80_94
  · exact match_zero_fix ⟨81, by decide⟩ ⟨94, by decide⟩ p hp j hj hq fz1_81_94 fz2_81_94
  · exact match_zero_fix ⟨82, by decide⟩ ⟨94, by decide⟩ p hp j hj hq fz1_82_94 fz2_82_94
  · exact match_zero_fix ⟨83, by decide⟩ ⟨94, by decide⟩ p hp j hj hq fz1_83_94 fz2_83_94
  · exact match_zero_fix ⟨84, by decide⟩ ⟨94, by decide⟩ p hp j hj hq fz1_84_94 fz2_84_94
  · exact match_zero_fix ⟨85, by decide⟩ ⟨94, by decide⟩ p hp j hj hq fz1_85_94 fz2_85_94
  · exact match_zero_fix ⟨86, by decide⟩ ⟨94, by decide⟩ p hp j hj hq fz1_86_94 fz2_86_94
  · exact match_zero_fix ⟨87, by decide⟩ ⟨94, by decide⟩ p hp j hj hq fz1_87_94 fz2_87_94
  · exact match_zero_fix ⟨88, by decide⟩ ⟨94, by decide⟩ p hp j hj hq fz1_88_94 fz2_88_94
  · exact match_zero_fix ⟨89, by decide⟩ ⟨94, by decide⟩ p hp j hj hq fz1_89_94 fz2_89_94
  · exact match_zero_fix ⟨90, by decide⟩ ⟨94, by decide⟩ p hp j hj hq fz1_90_94 fz2_90_94
  · exact match_zero_fix ⟨91, by decide⟩ ⟨94, by decide⟩ p hp j hj hq fz1_91_94 fz2_91_94
  · exact match_zero_fix ⟨92, by decide⟩ ⟨94, by decide⟩ p hp j hj hq fz1_92_94 fz2_92_94
  · exact match_zero_fix ⟨93, by decide⟩ ⟨94, by decide⟩ p hp j hj hq fz1_93_94 fz2_93_94
  · exact pair_94_94 p hp hrep j hj hq
  · exact match_zero_fix ⟨95, by decide⟩ ⟨94, by decide⟩ p hp j hj hq fz1_95_94 fz2_95_94
  · exact match_zero_fix ⟨96, by decide⟩ ⟨94, by decide⟩ p hp j hj hq fz1_96_94 fz2_96_94
  · exact match_zero_fix ⟨97, by decide⟩ ⟨94, by decide⟩ p hp j hj hq fz1_97_94 fz2_97_94
  · exact match_zero_fix ⟨98, by decide⟩ ⟨94, by decide⟩ p hp j hj hq fz1_98_94 fz2_98_94
  · exact match_zero_fix ⟨99, by decide⟩ ⟨94, by decide⟩ p hp j hj hq fz1_99_94 fz2_99_94
  · exact match_zero_fix ⟨100, by decide⟩ ⟨94, by decide⟩ p hp j hj hq fz1_100_94 fz2_100_94
  · exact match_zero_fix ⟨101, by decide⟩ ⟨94, by decide⟩ p hp j hj hq fz1_101_94 fz2_101_94
  · exact match_zero_fix ⟨102, by decide⟩ ⟨94, by decide⟩ p hp j hj hq fz1_102_94 fz2_102_94
  · exact match_zero_fix ⟨103, by decide⟩ ⟨94, by decide⟩ p hp j hj hq fz1_103_94 fz2_103_94
  · exact match_zero_fix ⟨104, by decide⟩ ⟨94, by decide⟩ p hp j hj hq fz1_104_94 fz2_104_94
  · exact match_zero_fix ⟨105, by decide⟩ ⟨94, by decide⟩ p hp j hj hq fz1_105_94 fz2_105_94
  · exact match_zero_fix ⟨106, by decide⟩ ⟨94, by decide⟩ p hp j hj hq fz1_106_94 fz2_106_94
  · exact match_zero_fix ⟨107, by decide⟩ ⟨94, by decide⟩ p hp j hj hq fz1_107_94 fz2_107_94
  · exact match_zero_fix ⟨108, by decide⟩ ⟨94, by decide⟩ p hp j hj hq fz1_108_94 fz2_108_94
  · exact match_zero_fix ⟨109, by decide⟩ ⟨94, by decide⟩ p hp j hj hq fz1_109_94 fz2_109_94
  · exact match_zero_fix ⟨110, by decide⟩ ⟨94, by decide⟩ p hp j hj hq fz1_110_94 fz2_110_94
  · exact match_zero_fix ⟨111, by decide⟩ ⟨94, by decide⟩ p hp j hj hq fz1_111_94 fz2_111_94
  · exact match_zero_fix ⟨112, by decide⟩ ⟨94, by decide⟩ p hp j hj hq fz1_112_94 fz2_112_94
  · exact match_zero_fix ⟨113, by decide⟩ ⟨94, by decide⟩ p hp j hj hq fz1_113_94 fz2_113_94
  · exact match_zero_fix ⟨114, by decide⟩ ⟨94, by decide⟩ p hp j hj hq fz1_114_94 fz2_114_94
  · exact match_zero_fix ⟨115, by decide⟩ ⟨94, by decide⟩ p hp j hj hq fz1_115_94 fz2_115_94
  · exact match_zero_fix ⟨116, by decide⟩ ⟨94, by decide⟩ p hp j hj hq fz1_116_94 fz2_116_94
  · exact match_zero_fix ⟨117, by decide⟩ ⟨94, by decide⟩ p hp j hj hq fz1_117_94 fz2_117_94
  · exact match_zero_fix ⟨118, by decide⟩ ⟨94, by decide⟩ p hp j hj hq fz1_118_94 fz2_118_94
  · exact match_zero_fix ⟨119, by decide⟩ ⟨94, by decide⟩ p hp j hj hq fz1_119_94 fz2_119_94
  · exact pair_120_94 p hp hrep j hj hq
  · exact pair_121_94 p hp hrep j hj hq
  · exact match_zero_fix ⟨122, by decide⟩ ⟨94, by decide⟩ p hp j hj hq fz1_122_94 fz2_122_94
  · exact match_zero_fix ⟨123, by decide⟩ ⟨94, by decide⟩ p hp j hj hq fz1_123_94 fz2_123_94
  · exact match_zero_fix ⟨124, by decide⟩ ⟨94, by decide⟩ p hp j hj hq fz1_124_94 fz2_124_94
  · exact match_zero_fix ⟨125, by decide⟩ ⟨94, by decide⟩ p hp j hj hq fz1_125_94 fz2_125_94
  · exact match_zero_fix ⟨126, by decide⟩ ⟨94, by decide⟩ p hp j hj hq fz1_126_94 fz2_126_94
  · exact pair_127_94 p hp hrep j hj hq
  · exact match_zero_fix ⟨128, by decide⟩ ⟨94, by decide⟩ p hp j hj hq fz1_128_94 fz2_128_94
  · exact match_zero_fix ⟨129, by decide⟩ ⟨94, by decide⟩ p hp j hj hq fz1_129_94 fz2_129_94
  · exact match_zero_fix ⟨130, by decide⟩ ⟨94, by decide⟩ p hp j hj hq fz1_130_94 fz2_130_94
  · exact match_zero_fix ⟨131, by decide⟩ ⟨94, by decide⟩ p hp j hj hq fz1_131_94 fz2_131_94
  · exact match_zero_fix ⟨132, by decide⟩ ⟨94, by decide⟩ p hp j hj hq fz1_132_94 fz2_132_94
  · exact pair_133_94 p hp hrep j hj hq
  · exact match_zero_fix ⟨134, by decide⟩ ⟨94, by decide⟩ p hp j hj hq fz1_134_94 fz2_134_94
  · exact match_zero_fix ⟨135, by decide⟩ ⟨94, by decide⟩ p hp j hj hq fz1_135_94 fz2_135_94
  · exact match_zero_fix ⟨136, by decide⟩ ⟨94, by decide⟩ p hp j hj hq fz1_136_94 fz2_136_94
  · exact match_zero_fix ⟨137, by decide⟩ ⟨94, by decide⟩ p hp j hj hq fz1_137_94 fz2_137_94
  · exact match_zero_fix ⟨138, by decide⟩ ⟨94, by decide⟩ p hp j hj hq fz1_138_94 fz2_138_94
  · exact pair_139_94 p hp hrep j hj hq
  · exact match_zero_fix ⟨140, by decide⟩ ⟨94, by decide⟩ p hp j hj hq fz1_140_94 fz2_140_94
  · exact match_zero_fix ⟨141, by decide⟩ ⟨94, by decide⟩ p hp j hj hq fz1_141_94 fz2_141_94
  · exact pair_142_94 p hp hrep j hj hq
  · exact match_zero_fix ⟨143, by decide⟩ ⟨94, by decide⟩ p hp j hj hq fz1_143_94 fz2_143_94
  · exact match_zero_fix ⟨144, by decide⟩ ⟨94, by decide⟩ p hp j hj hq fz1_144_94 fz2_144_94
  · exact match_zero_fix ⟨145, by decide⟩ ⟨94, by decide⟩ p hp j hj hq fz1_145_94 fz2_145_94
  · exact match_zero_fix ⟨146, by decide⟩ ⟨94, by decide⟩ p hp j hj hq fz1_146_94 fz2_146_94
  · exact pair_147_94 p hp hrep j hj hq

theorem master_95 (p : Nat) (hp : p < (Q2.transData.getD 95 []).length)
    (hrep : (Q2.cosetIsRep.getD 95 []).getD p false = true)
    (rK : Fin 148) (j : Nat) (hj : j < (repChars.getD rK.val []).length)
    (hq : (normIsRep.getD rK.val []).getD j false = true) :
    species (Q2.reps (⟨95, by decide⟩ : Fin 148)) (colE2 ⟨95, by decide⟩ p hp)
        (rowE2 rK j hj hq)
      = species (reps (⟨95, by decide⟩ : Fin 148))
        (colE1 ⟨95, by decide⟩ p (transLenTr ⟨95, by decide⟩ p hp)) (rowE1 rK j hj) := by
  rcases rK with ⟨nK, hnK⟩; interval_cases nK
  · exact match_zero_len ⟨0, by decide⟩ ⟨95, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨1, by decide⟩ ⟨95, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨2, by decide⟩ ⟨95, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨3, by decide⟩ ⟨95, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨4, by decide⟩ ⟨95, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨5, by decide⟩ ⟨95, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨6, by decide⟩ ⟨95, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨7, by decide⟩ ⟨95, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨8, by decide⟩ ⟨95, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨9, by decide⟩ ⟨95, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨10, by decide⟩ ⟨95, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨11, by decide⟩ ⟨95, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨12, by decide⟩ ⟨95, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨13, by decide⟩ ⟨95, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨14, by decide⟩ ⟨95, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨15, by decide⟩ ⟨95, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨16, by decide⟩ ⟨95, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨17, by decide⟩ ⟨95, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨18, by decide⟩ ⟨95, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨19, by decide⟩ ⟨95, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨20, by decide⟩ ⟨95, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨21, by decide⟩ ⟨95, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨22, by decide⟩ ⟨95, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨23, by decide⟩ ⟨95, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨24, by decide⟩ ⟨95, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨25, by decide⟩ ⟨95, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨26, by decide⟩ ⟨95, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨27, by decide⟩ ⟨95, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨28, by decide⟩ ⟨95, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨29, by decide⟩ ⟨95, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨30, by decide⟩ ⟨95, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨31, by decide⟩ ⟨95, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨32, by decide⟩ ⟨95, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨33, by decide⟩ ⟨95, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨34, by decide⟩ ⟨95, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨35, by decide⟩ ⟨95, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨36, by decide⟩ ⟨95, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨37, by decide⟩ ⟨95, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨38, by decide⟩ ⟨95, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨39, by decide⟩ ⟨95, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨40, by decide⟩ ⟨95, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨41, by decide⟩ ⟨95, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨42, by decide⟩ ⟨95, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨43, by decide⟩ ⟨95, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨44, by decide⟩ ⟨95, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨45, by decide⟩ ⟨95, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨46, by decide⟩ ⟨95, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨47, by decide⟩ ⟨95, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨48, by decide⟩ ⟨95, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨49, by decide⟩ ⟨95, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨50, by decide⟩ ⟨95, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨51, by decide⟩ ⟨95, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨52, by decide⟩ ⟨95, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨53, by decide⟩ ⟨95, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨54, by decide⟩ ⟨95, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_fix ⟨55, by decide⟩ ⟨95, by decide⟩ p hp j hj hq fz1_55_95 fz2_55_95
  · exact match_zero_fix ⟨56, by decide⟩ ⟨95, by decide⟩ p hp j hj hq fz1_56_95 fz2_56_95
  · exact match_zero_fix ⟨57, by decide⟩ ⟨95, by decide⟩ p hp j hj hq fz1_57_95 fz2_57_95
  · exact match_zero_fix ⟨58, by decide⟩ ⟨95, by decide⟩ p hp j hj hq fz1_58_95 fz2_58_95
  · exact match_zero_fix ⟨59, by decide⟩ ⟨95, by decide⟩ p hp j hj hq fz1_59_95 fz2_59_95
  · exact match_zero_fix ⟨60, by decide⟩ ⟨95, by decide⟩ p hp j hj hq fz1_60_95 fz2_60_95
  · exact match_zero_fix ⟨61, by decide⟩ ⟨95, by decide⟩ p hp j hj hq fz1_61_95 fz2_61_95
  · exact match_zero_fix ⟨62, by decide⟩ ⟨95, by decide⟩ p hp j hj hq fz1_62_95 fz2_62_95
  · exact match_zero_fix ⟨63, by decide⟩ ⟨95, by decide⟩ p hp j hj hq fz1_63_95 fz2_63_95
  · exact match_zero_fix ⟨64, by decide⟩ ⟨95, by decide⟩ p hp j hj hq fz1_64_95 fz2_64_95
  · exact match_zero_fix ⟨65, by decide⟩ ⟨95, by decide⟩ p hp j hj hq fz1_65_95 fz2_65_95
  · exact match_zero_fix ⟨66, by decide⟩ ⟨95, by decide⟩ p hp j hj hq fz1_66_95 fz2_66_95
  · exact match_zero_fix ⟨67, by decide⟩ ⟨95, by decide⟩ p hp j hj hq fz1_67_95 fz2_67_95
  · exact match_zero_fix ⟨68, by decide⟩ ⟨95, by decide⟩ p hp j hj hq fz1_68_95 fz2_68_95
  · exact match_zero_fix ⟨69, by decide⟩ ⟨95, by decide⟩ p hp j hj hq fz1_69_95 fz2_69_95
  · exact match_zero_fix ⟨70, by decide⟩ ⟨95, by decide⟩ p hp j hj hq fz1_70_95 fz2_70_95
  · exact match_zero_fix ⟨71, by decide⟩ ⟨95, by decide⟩ p hp j hj hq fz1_71_95 fz2_71_95
  · exact match_zero_fix ⟨72, by decide⟩ ⟨95, by decide⟩ p hp j hj hq fz1_72_95 fz2_72_95
  · exact match_zero_fix ⟨73, by decide⟩ ⟨95, by decide⟩ p hp j hj hq fz1_73_95 fz2_73_95
  · exact match_zero_fix ⟨74, by decide⟩ ⟨95, by decide⟩ p hp j hj hq fz1_74_95 fz2_74_95
  · exact match_zero_fix ⟨75, by decide⟩ ⟨95, by decide⟩ p hp j hj hq fz1_75_95 fz2_75_95
  · exact match_zero_fix ⟨76, by decide⟩ ⟨95, by decide⟩ p hp j hj hq fz1_76_95 fz2_76_95
  · exact match_zero_fix ⟨77, by decide⟩ ⟨95, by decide⟩ p hp j hj hq fz1_77_95 fz2_77_95
  · exact match_zero_fix ⟨78, by decide⟩ ⟨95, by decide⟩ p hp j hj hq fz1_78_95 fz2_78_95
  · exact match_zero_fix ⟨79, by decide⟩ ⟨95, by decide⟩ p hp j hj hq fz1_79_95 fz2_79_95
  · exact match_zero_fix ⟨80, by decide⟩ ⟨95, by decide⟩ p hp j hj hq fz1_80_95 fz2_80_95
  · exact match_zero_fix ⟨81, by decide⟩ ⟨95, by decide⟩ p hp j hj hq fz1_81_95 fz2_81_95
  · exact match_zero_fix ⟨82, by decide⟩ ⟨95, by decide⟩ p hp j hj hq fz1_82_95 fz2_82_95
  · exact match_zero_fix ⟨83, by decide⟩ ⟨95, by decide⟩ p hp j hj hq fz1_83_95 fz2_83_95
  · exact match_zero_fix ⟨84, by decide⟩ ⟨95, by decide⟩ p hp j hj hq fz1_84_95 fz2_84_95
  · exact match_zero_fix ⟨85, by decide⟩ ⟨95, by decide⟩ p hp j hj hq fz1_85_95 fz2_85_95
  · exact match_zero_fix ⟨86, by decide⟩ ⟨95, by decide⟩ p hp j hj hq fz1_86_95 fz2_86_95
  · exact match_zero_fix ⟨87, by decide⟩ ⟨95, by decide⟩ p hp j hj hq fz1_87_95 fz2_87_95
  · exact match_zero_fix ⟨88, by decide⟩ ⟨95, by decide⟩ p hp j hj hq fz1_88_95 fz2_88_95
  · exact match_zero_fix ⟨89, by decide⟩ ⟨95, by decide⟩ p hp j hj hq fz1_89_95 fz2_89_95
  · exact match_zero_fix ⟨90, by decide⟩ ⟨95, by decide⟩ p hp j hj hq fz1_90_95 fz2_90_95
  · exact match_zero_fix ⟨91, by decide⟩ ⟨95, by decide⟩ p hp j hj hq fz1_91_95 fz2_91_95
  · exact match_zero_fix ⟨92, by decide⟩ ⟨95, by decide⟩ p hp j hj hq fz1_92_95 fz2_92_95
  · exact match_zero_fix ⟨93, by decide⟩ ⟨95, by decide⟩ p hp j hj hq fz1_93_95 fz2_93_95
  · exact match_zero_fix ⟨94, by decide⟩ ⟨95, by decide⟩ p hp j hj hq fz1_94_95 fz2_94_95
  · exact pair_95_95 p hp hrep j hj hq
  · exact match_zero_fix ⟨96, by decide⟩ ⟨95, by decide⟩ p hp j hj hq fz1_96_95 fz2_96_95
  · exact match_zero_fix ⟨97, by decide⟩ ⟨95, by decide⟩ p hp j hj hq fz1_97_95 fz2_97_95
  · exact match_zero_fix ⟨98, by decide⟩ ⟨95, by decide⟩ p hp j hj hq fz1_98_95 fz2_98_95
  · exact match_zero_fix ⟨99, by decide⟩ ⟨95, by decide⟩ p hp j hj hq fz1_99_95 fz2_99_95
  · exact match_zero_fix ⟨100, by decide⟩ ⟨95, by decide⟩ p hp j hj hq fz1_100_95 fz2_100_95
  · exact match_zero_fix ⟨101, by decide⟩ ⟨95, by decide⟩ p hp j hj hq fz1_101_95 fz2_101_95
  · exact match_zero_fix ⟨102, by decide⟩ ⟨95, by decide⟩ p hp j hj hq fz1_102_95 fz2_102_95
  · exact match_zero_fix ⟨103, by decide⟩ ⟨95, by decide⟩ p hp j hj hq fz1_103_95 fz2_103_95
  · exact match_zero_fix ⟨104, by decide⟩ ⟨95, by decide⟩ p hp j hj hq fz1_104_95 fz2_104_95
  · exact match_zero_fix ⟨105, by decide⟩ ⟨95, by decide⟩ p hp j hj hq fz1_105_95 fz2_105_95
  · exact match_zero_fix ⟨106, by decide⟩ ⟨95, by decide⟩ p hp j hj hq fz1_106_95 fz2_106_95
  · exact match_zero_fix ⟨107, by decide⟩ ⟨95, by decide⟩ p hp j hj hq fz1_107_95 fz2_107_95
  · exact match_zero_fix ⟨108, by decide⟩ ⟨95, by decide⟩ p hp j hj hq fz1_108_95 fz2_108_95
  · exact match_zero_fix ⟨109, by decide⟩ ⟨95, by decide⟩ p hp j hj hq fz1_109_95 fz2_109_95
  · exact match_zero_fix ⟨110, by decide⟩ ⟨95, by decide⟩ p hp j hj hq fz1_110_95 fz2_110_95
  · exact match_zero_fix ⟨111, by decide⟩ ⟨95, by decide⟩ p hp j hj hq fz1_111_95 fz2_111_95
  · exact match_zero_fix ⟨112, by decide⟩ ⟨95, by decide⟩ p hp j hj hq fz1_112_95 fz2_112_95
  · exact match_zero_fix ⟨113, by decide⟩ ⟨95, by decide⟩ p hp j hj hq fz1_113_95 fz2_113_95
  · exact match_zero_fix ⟨114, by decide⟩ ⟨95, by decide⟩ p hp j hj hq fz1_114_95 fz2_114_95
  · exact match_zero_fix ⟨115, by decide⟩ ⟨95, by decide⟩ p hp j hj hq fz1_115_95 fz2_115_95
  · exact pair_116_95 p hp hrep j hj hq
  · exact match_zero_fix ⟨117, by decide⟩ ⟨95, by decide⟩ p hp j hj hq fz1_117_95 fz2_117_95
  · exact match_zero_fix ⟨118, by decide⟩ ⟨95, by decide⟩ p hp j hj hq fz1_118_95 fz2_118_95
  · exact match_zero_fix ⟨119, by decide⟩ ⟨95, by decide⟩ p hp j hj hq fz1_119_95 fz2_119_95
  · exact match_zero_fix ⟨120, by decide⟩ ⟨95, by decide⟩ p hp j hj hq fz1_120_95 fz2_120_95
  · exact match_zero_fix ⟨121, by decide⟩ ⟨95, by decide⟩ p hp j hj hq fz1_121_95 fz2_121_95
  · exact match_zero_fix ⟨122, by decide⟩ ⟨95, by decide⟩ p hp j hj hq fz1_122_95 fz2_122_95
  · exact match_zero_fix ⟨123, by decide⟩ ⟨95, by decide⟩ p hp j hj hq fz1_123_95 fz2_123_95
  · exact pair_124_95 p hp hrep j hj hq
  · exact match_zero_fix ⟨125, by decide⟩ ⟨95, by decide⟩ p hp j hj hq fz1_125_95 fz2_125_95
  · exact match_zero_fix ⟨126, by decide⟩ ⟨95, by decide⟩ p hp j hj hq fz1_126_95 fz2_126_95
  · exact pair_127_95 p hp hrep j hj hq
  · exact match_zero_fix ⟨128, by decide⟩ ⟨95, by decide⟩ p hp j hj hq fz1_128_95 fz2_128_95
  · exact match_zero_fix ⟨129, by decide⟩ ⟨95, by decide⟩ p hp j hj hq fz1_129_95 fz2_129_95
  · exact match_zero_fix ⟨130, by decide⟩ ⟨95, by decide⟩ p hp j hj hq fz1_130_95 fz2_130_95
  · exact match_zero_fix ⟨131, by decide⟩ ⟨95, by decide⟩ p hp j hj hq fz1_131_95 fz2_131_95
  · exact match_zero_fix ⟨132, by decide⟩ ⟨95, by decide⟩ p hp j hj hq fz1_132_95 fz2_132_95
  · exact match_zero_fix ⟨133, by decide⟩ ⟨95, by decide⟩ p hp j hj hq fz1_133_95 fz2_133_95
  · exact match_zero_fix ⟨134, by decide⟩ ⟨95, by decide⟩ p hp j hj hq fz1_134_95 fz2_134_95
  · exact pair_135_95 p hp hrep j hj hq
  · exact match_zero_fix ⟨136, by decide⟩ ⟨95, by decide⟩ p hp j hj hq fz1_136_95 fz2_136_95
  · exact match_zero_fix ⟨137, by decide⟩ ⟨95, by decide⟩ p hp j hj hq fz1_137_95 fz2_137_95
  · exact pair_138_95 p hp hrep j hj hq
  · exact match_zero_fix ⟨139, by decide⟩ ⟨95, by decide⟩ p hp j hj hq fz1_139_95 fz2_139_95
  · exact match_zero_fix ⟨140, by decide⟩ ⟨95, by decide⟩ p hp j hj hq fz1_140_95 fz2_140_95
  · exact match_zero_fix ⟨141, by decide⟩ ⟨95, by decide⟩ p hp j hj hq fz1_141_95 fz2_141_95
  · exact match_zero_fix ⟨142, by decide⟩ ⟨95, by decide⟩ p hp j hj hq fz1_142_95 fz2_142_95
  · exact pair_143_95 p hp hrep j hj hq
  · exact match_zero_fix ⟨144, by decide⟩ ⟨95, by decide⟩ p hp j hj hq fz1_144_95 fz2_144_95
  · exact match_zero_fix ⟨145, by decide⟩ ⟨95, by decide⟩ p hp j hj hq fz1_145_95 fz2_145_95
  · exact match_zero_fix ⟨146, by decide⟩ ⟨95, by decide⟩ p hp j hj hq fz1_146_95 fz2_146_95
  · exact pair_147_95 p hp hrep j hj hq

end LeanDring.P5Presentation
