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
import LeanDring.P5.Data.MatchPair.C005
import LeanDring.P5.Data.MatchPair.C006
import LeanDring.P5.Data.MatchPair.C007
import LeanDring.P5.Data.MatchPair.C008
import LeanDring.P5.Data.MatchPair.C009
import LeanDring.P5.Data.MatchPair.C010

/-! # Stage-5 per-column-class master theorems, chunk 14 (auto-emitted).  -/

namespace LeanDring.P5Presentation

open MulAction Finset LeanDring.DRing LeanDring.MonGSet

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.style.longLine false

theorem master_112 (p : Nat) (hp : p < (Q2.transData.getD 112 []).length)
    (hrep : (Q2.cosetIsRep.getD 112 []).getD p false = true)
    (rK : Fin 148) (j : Nat) (hj : j < (repChars.getD rK.val []).length)
    (hq : (normIsRep.getD rK.val []).getD j false = true) :
    species (Q2.reps (⟨112, by decide⟩ : Fin 148)) (colE2 ⟨112, by decide⟩ p hp)
        (rowE2 rK j hj hq)
      = species (reps (⟨112, by decide⟩ : Fin 148))
        (colE1 ⟨112, by decide⟩ p (transLenTr ⟨112, by decide⟩ p hp)) (rowE1 rK j hj) := by
  rcases rK with ⟨nK, hnK⟩; interval_cases nK
  · exact match_zero_len ⟨0, by decide⟩ ⟨112, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨1, by decide⟩ ⟨112, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨2, by decide⟩ ⟨112, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨3, by decide⟩ ⟨112, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨4, by decide⟩ ⟨112, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨5, by decide⟩ ⟨112, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨6, by decide⟩ ⟨112, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨7, by decide⟩ ⟨112, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨8, by decide⟩ ⟨112, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨9, by decide⟩ ⟨112, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨10, by decide⟩ ⟨112, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨11, by decide⟩ ⟨112, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨12, by decide⟩ ⟨112, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨13, by decide⟩ ⟨112, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨14, by decide⟩ ⟨112, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨15, by decide⟩ ⟨112, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨16, by decide⟩ ⟨112, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨17, by decide⟩ ⟨112, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨18, by decide⟩ ⟨112, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨19, by decide⟩ ⟨112, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨20, by decide⟩ ⟨112, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨21, by decide⟩ ⟨112, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨22, by decide⟩ ⟨112, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨23, by decide⟩ ⟨112, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨24, by decide⟩ ⟨112, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨25, by decide⟩ ⟨112, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨26, by decide⟩ ⟨112, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨27, by decide⟩ ⟨112, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨28, by decide⟩ ⟨112, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨29, by decide⟩ ⟨112, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨30, by decide⟩ ⟨112, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨31, by decide⟩ ⟨112, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨32, by decide⟩ ⟨112, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨33, by decide⟩ ⟨112, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨34, by decide⟩ ⟨112, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨35, by decide⟩ ⟨112, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨36, by decide⟩ ⟨112, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨37, by decide⟩ ⟨112, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨38, by decide⟩ ⟨112, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨39, by decide⟩ ⟨112, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨40, by decide⟩ ⟨112, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨41, by decide⟩ ⟨112, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨42, by decide⟩ ⟨112, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨43, by decide⟩ ⟨112, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨44, by decide⟩ ⟨112, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨45, by decide⟩ ⟨112, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨46, by decide⟩ ⟨112, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨47, by decide⟩ ⟨112, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨48, by decide⟩ ⟨112, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨49, by decide⟩ ⟨112, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨50, by decide⟩ ⟨112, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨51, by decide⟩ ⟨112, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨52, by decide⟩ ⟨112, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨53, by decide⟩ ⟨112, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨54, by decide⟩ ⟨112, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_fix ⟨55, by decide⟩ ⟨112, by decide⟩ p hp j hj hq fz1_55_112 fz2_55_112
  · exact match_zero_fix ⟨56, by decide⟩ ⟨112, by decide⟩ p hp j hj hq fz1_56_112 fz2_56_112
  · exact match_zero_fix ⟨57, by decide⟩ ⟨112, by decide⟩ p hp j hj hq fz1_57_112 fz2_57_112
  · exact match_zero_fix ⟨58, by decide⟩ ⟨112, by decide⟩ p hp j hj hq fz1_58_112 fz2_58_112
  · exact match_zero_fix ⟨59, by decide⟩ ⟨112, by decide⟩ p hp j hj hq fz1_59_112 fz2_59_112
  · exact match_zero_fix ⟨60, by decide⟩ ⟨112, by decide⟩ p hp j hj hq fz1_60_112 fz2_60_112
  · exact match_zero_fix ⟨61, by decide⟩ ⟨112, by decide⟩ p hp j hj hq fz1_61_112 fz2_61_112
  · exact match_zero_fix ⟨62, by decide⟩ ⟨112, by decide⟩ p hp j hj hq fz1_62_112 fz2_62_112
  · exact match_zero_fix ⟨63, by decide⟩ ⟨112, by decide⟩ p hp j hj hq fz1_63_112 fz2_63_112
  · exact match_zero_fix ⟨64, by decide⟩ ⟨112, by decide⟩ p hp j hj hq fz1_64_112 fz2_64_112
  · exact match_zero_fix ⟨65, by decide⟩ ⟨112, by decide⟩ p hp j hj hq fz1_65_112 fz2_65_112
  · exact match_zero_fix ⟨66, by decide⟩ ⟨112, by decide⟩ p hp j hj hq fz1_66_112 fz2_66_112
  · exact match_zero_fix ⟨67, by decide⟩ ⟨112, by decide⟩ p hp j hj hq fz1_67_112 fz2_67_112
  · exact match_zero_fix ⟨68, by decide⟩ ⟨112, by decide⟩ p hp j hj hq fz1_68_112 fz2_68_112
  · exact match_zero_fix ⟨69, by decide⟩ ⟨112, by decide⟩ p hp j hj hq fz1_69_112 fz2_69_112
  · exact match_zero_fix ⟨70, by decide⟩ ⟨112, by decide⟩ p hp j hj hq fz1_70_112 fz2_70_112
  · exact match_zero_fix ⟨71, by decide⟩ ⟨112, by decide⟩ p hp j hj hq fz1_71_112 fz2_71_112
  · exact match_zero_fix ⟨72, by decide⟩ ⟨112, by decide⟩ p hp j hj hq fz1_72_112 fz2_72_112
  · exact match_zero_fix ⟨73, by decide⟩ ⟨112, by decide⟩ p hp j hj hq fz1_73_112 fz2_73_112
  · exact match_zero_fix ⟨74, by decide⟩ ⟨112, by decide⟩ p hp j hj hq fz1_74_112 fz2_74_112
  · exact match_zero_fix ⟨75, by decide⟩ ⟨112, by decide⟩ p hp j hj hq fz1_75_112 fz2_75_112
  · exact match_zero_fix ⟨76, by decide⟩ ⟨112, by decide⟩ p hp j hj hq fz1_76_112 fz2_76_112
  · exact match_zero_fix ⟨77, by decide⟩ ⟨112, by decide⟩ p hp j hj hq fz1_77_112 fz2_77_112
  · exact match_zero_fix ⟨78, by decide⟩ ⟨112, by decide⟩ p hp j hj hq fz1_78_112 fz2_78_112
  · exact match_zero_fix ⟨79, by decide⟩ ⟨112, by decide⟩ p hp j hj hq fz1_79_112 fz2_79_112
  · exact match_zero_fix ⟨80, by decide⟩ ⟨112, by decide⟩ p hp j hj hq fz1_80_112 fz2_80_112
  · exact match_zero_fix ⟨81, by decide⟩ ⟨112, by decide⟩ p hp j hj hq fz1_81_112 fz2_81_112
  · exact match_zero_fix ⟨82, by decide⟩ ⟨112, by decide⟩ p hp j hj hq fz1_82_112 fz2_82_112
  · exact match_zero_fix ⟨83, by decide⟩ ⟨112, by decide⟩ p hp j hj hq fz1_83_112 fz2_83_112
  · exact match_zero_fix ⟨84, by decide⟩ ⟨112, by decide⟩ p hp j hj hq fz1_84_112 fz2_84_112
  · exact match_zero_fix ⟨85, by decide⟩ ⟨112, by decide⟩ p hp j hj hq fz1_85_112 fz2_85_112
  · exact match_zero_fix ⟨86, by decide⟩ ⟨112, by decide⟩ p hp j hj hq fz1_86_112 fz2_86_112
  · exact match_zero_fix ⟨87, by decide⟩ ⟨112, by decide⟩ p hp j hj hq fz1_87_112 fz2_87_112
  · exact match_zero_fix ⟨88, by decide⟩ ⟨112, by decide⟩ p hp j hj hq fz1_88_112 fz2_88_112
  · exact match_zero_fix ⟨89, by decide⟩ ⟨112, by decide⟩ p hp j hj hq fz1_89_112 fz2_89_112
  · exact match_zero_fix ⟨90, by decide⟩ ⟨112, by decide⟩ p hp j hj hq fz1_90_112 fz2_90_112
  · exact match_zero_fix ⟨91, by decide⟩ ⟨112, by decide⟩ p hp j hj hq fz1_91_112 fz2_91_112
  · exact match_zero_fix ⟨92, by decide⟩ ⟨112, by decide⟩ p hp j hj hq fz1_92_112 fz2_92_112
  · exact match_zero_fix ⟨93, by decide⟩ ⟨112, by decide⟩ p hp j hj hq fz1_93_112 fz2_93_112
  · exact match_zero_fix ⟨94, by decide⟩ ⟨112, by decide⟩ p hp j hj hq fz1_94_112 fz2_94_112
  · exact match_zero_fix ⟨95, by decide⟩ ⟨112, by decide⟩ p hp j hj hq fz1_95_112 fz2_95_112
  · exact match_zero_fix ⟨96, by decide⟩ ⟨112, by decide⟩ p hp j hj hq fz1_96_112 fz2_96_112
  · exact match_zero_fix ⟨97, by decide⟩ ⟨112, by decide⟩ p hp j hj hq fz1_97_112 fz2_97_112
  · exact match_zero_fix ⟨98, by decide⟩ ⟨112, by decide⟩ p hp j hj hq fz1_98_112 fz2_98_112
  · exact match_zero_fix ⟨99, by decide⟩ ⟨112, by decide⟩ p hp j hj hq fz1_99_112 fz2_99_112
  · exact match_zero_fix ⟨100, by decide⟩ ⟨112, by decide⟩ p hp j hj hq fz1_100_112 fz2_100_112
  · exact match_zero_fix ⟨101, by decide⟩ ⟨112, by decide⟩ p hp j hj hq fz1_101_112 fz2_101_112
  · exact match_zero_fix ⟨102, by decide⟩ ⟨112, by decide⟩ p hp j hj hq fz1_102_112 fz2_102_112
  · exact match_zero_fix ⟨103, by decide⟩ ⟨112, by decide⟩ p hp j hj hq fz1_103_112 fz2_103_112
  · exact match_zero_fix ⟨104, by decide⟩ ⟨112, by decide⟩ p hp j hj hq fz1_104_112 fz2_104_112
  · exact match_zero_fix ⟨105, by decide⟩ ⟨112, by decide⟩ p hp j hj hq fz1_105_112 fz2_105_112
  · exact match_zero_fix ⟨106, by decide⟩ ⟨112, by decide⟩ p hp j hj hq fz1_106_112 fz2_106_112
  · exact match_zero_fix ⟨107, by decide⟩ ⟨112, by decide⟩ p hp j hj hq fz1_107_112 fz2_107_112
  · exact match_zero_fix ⟨108, by decide⟩ ⟨112, by decide⟩ p hp j hj hq fz1_108_112 fz2_108_112
  · exact match_zero_fix ⟨109, by decide⟩ ⟨112, by decide⟩ p hp j hj hq fz1_109_112 fz2_109_112
  · exact match_zero_fix ⟨110, by decide⟩ ⟨112, by decide⟩ p hp j hj hq fz1_110_112 fz2_110_112
  · exact match_zero_fix ⟨111, by decide⟩ ⟨112, by decide⟩ p hp j hj hq fz1_111_112 fz2_111_112
  · exact pair_112_112 p hp hrep j hj hq
  · exact match_zero_fix ⟨113, by decide⟩ ⟨112, by decide⟩ p hp j hj hq fz1_113_112 fz2_113_112
  · exact match_zero_fix ⟨114, by decide⟩ ⟨112, by decide⟩ p hp j hj hq fz1_114_112 fz2_114_112
  · exact match_zero_fix ⟨115, by decide⟩ ⟨112, by decide⟩ p hp j hj hq fz1_115_112 fz2_115_112
  · exact match_zero_fix ⟨116, by decide⟩ ⟨112, by decide⟩ p hp j hj hq fz1_116_112 fz2_116_112
  · exact match_zero_fix ⟨117, by decide⟩ ⟨112, by decide⟩ p hp j hj hq fz1_117_112 fz2_117_112
  · exact pair_118_112 p hp hrep j hj hq
  · exact match_zero_fix ⟨119, by decide⟩ ⟨112, by decide⟩ p hp j hj hq fz1_119_112 fz2_119_112
  · exact match_zero_fix ⟨120, by decide⟩ ⟨112, by decide⟩ p hp j hj hq fz1_120_112 fz2_120_112
  · exact match_zero_fix ⟨121, by decide⟩ ⟨112, by decide⟩ p hp j hj hq fz1_121_112 fz2_121_112
  · exact match_zero_fix ⟨122, by decide⟩ ⟨112, by decide⟩ p hp j hj hq fz1_122_112 fz2_122_112
  · exact pair_123_112 p hp hrep j hj hq
  · exact match_zero_fix ⟨124, by decide⟩ ⟨112, by decide⟩ p hp j hj hq fz1_124_112 fz2_124_112
  · exact match_zero_fix ⟨125, by decide⟩ ⟨112, by decide⟩ p hp j hj hq fz1_125_112 fz2_125_112
  · exact match_zero_fix ⟨126, by decide⟩ ⟨112, by decide⟩ p hp j hj hq fz1_126_112 fz2_126_112
  · exact match_zero_fix ⟨127, by decide⟩ ⟨112, by decide⟩ p hp j hj hq fz1_127_112 fz2_127_112
  · exact pair_128_112 p hp hrep j hj hq
  · exact match_zero_fix ⟨129, by decide⟩ ⟨112, by decide⟩ p hp j hj hq fz1_129_112 fz2_129_112
  · exact match_zero_fix ⟨130, by decide⟩ ⟨112, by decide⟩ p hp j hj hq fz1_130_112 fz2_130_112
  · exact match_zero_fix ⟨131, by decide⟩ ⟨112, by decide⟩ p hp j hj hq fz1_131_112 fz2_131_112
  · exact match_zero_fix ⟨132, by decide⟩ ⟨112, by decide⟩ p hp j hj hq fz1_132_112 fz2_132_112
  · exact pair_133_112 p hp hrep j hj hq
  · exact match_zero_fix ⟨134, by decide⟩ ⟨112, by decide⟩ p hp j hj hq fz1_134_112 fz2_134_112
  · exact match_zero_fix ⟨135, by decide⟩ ⟨112, by decide⟩ p hp j hj hq fz1_135_112 fz2_135_112
  · exact match_zero_fix ⟨136, by decide⟩ ⟨112, by decide⟩ p hp j hj hq fz1_136_112 fz2_136_112
  · exact match_zero_fix ⟨137, by decide⟩ ⟨112, by decide⟩ p hp j hj hq fz1_137_112 fz2_137_112
  · exact pair_138_112 p hp hrep j hj hq
  · exact match_zero_fix ⟨139, by decide⟩ ⟨112, by decide⟩ p hp j hj hq fz1_139_112 fz2_139_112
  · exact match_zero_fix ⟨140, by decide⟩ ⟨112, by decide⟩ p hp j hj hq fz1_140_112 fz2_140_112
  · exact match_zero_fix ⟨141, by decide⟩ ⟨112, by decide⟩ p hp j hj hq fz1_141_112 fz2_141_112
  · exact match_zero_fix ⟨142, by decide⟩ ⟨112, by decide⟩ p hp j hj hq fz1_142_112 fz2_142_112
  · exact match_zero_fix ⟨143, by decide⟩ ⟨112, by decide⟩ p hp j hj hq fz1_143_112 fz2_143_112
  · exact match_zero_fix ⟨144, by decide⟩ ⟨112, by decide⟩ p hp j hj hq fz1_144_112 fz2_144_112
  · exact match_zero_fix ⟨145, by decide⟩ ⟨112, by decide⟩ p hp j hj hq fz1_145_112 fz2_145_112
  · exact pair_146_112 p hp hrep j hj hq
  · exact pair_147_112 p hp hrep j hj hq

theorem master_113 (p : Nat) (hp : p < (Q2.transData.getD 113 []).length)
    (hrep : (Q2.cosetIsRep.getD 113 []).getD p false = true)
    (rK : Fin 148) (j : Nat) (hj : j < (repChars.getD rK.val []).length)
    (hq : (normIsRep.getD rK.val []).getD j false = true) :
    species (Q2.reps (⟨113, by decide⟩ : Fin 148)) (colE2 ⟨113, by decide⟩ p hp)
        (rowE2 rK j hj hq)
      = species (reps (⟨113, by decide⟩ : Fin 148))
        (colE1 ⟨113, by decide⟩ p (transLenTr ⟨113, by decide⟩ p hp)) (rowE1 rK j hj) := by
  rcases rK with ⟨nK, hnK⟩; interval_cases nK
  · exact match_zero_len ⟨0, by decide⟩ ⟨113, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨1, by decide⟩ ⟨113, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨2, by decide⟩ ⟨113, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨3, by decide⟩ ⟨113, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨4, by decide⟩ ⟨113, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨5, by decide⟩ ⟨113, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨6, by decide⟩ ⟨113, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨7, by decide⟩ ⟨113, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨8, by decide⟩ ⟨113, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨9, by decide⟩ ⟨113, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨10, by decide⟩ ⟨113, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨11, by decide⟩ ⟨113, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨12, by decide⟩ ⟨113, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨13, by decide⟩ ⟨113, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨14, by decide⟩ ⟨113, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨15, by decide⟩ ⟨113, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨16, by decide⟩ ⟨113, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨17, by decide⟩ ⟨113, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨18, by decide⟩ ⟨113, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨19, by decide⟩ ⟨113, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨20, by decide⟩ ⟨113, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨21, by decide⟩ ⟨113, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨22, by decide⟩ ⟨113, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨23, by decide⟩ ⟨113, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨24, by decide⟩ ⟨113, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨25, by decide⟩ ⟨113, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨26, by decide⟩ ⟨113, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨27, by decide⟩ ⟨113, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨28, by decide⟩ ⟨113, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨29, by decide⟩ ⟨113, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨30, by decide⟩ ⟨113, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨31, by decide⟩ ⟨113, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨32, by decide⟩ ⟨113, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨33, by decide⟩ ⟨113, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨34, by decide⟩ ⟨113, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨35, by decide⟩ ⟨113, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨36, by decide⟩ ⟨113, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨37, by decide⟩ ⟨113, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨38, by decide⟩ ⟨113, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨39, by decide⟩ ⟨113, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨40, by decide⟩ ⟨113, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨41, by decide⟩ ⟨113, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨42, by decide⟩ ⟨113, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨43, by decide⟩ ⟨113, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨44, by decide⟩ ⟨113, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨45, by decide⟩ ⟨113, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨46, by decide⟩ ⟨113, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨47, by decide⟩ ⟨113, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨48, by decide⟩ ⟨113, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨49, by decide⟩ ⟨113, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨50, by decide⟩ ⟨113, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨51, by decide⟩ ⟨113, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨52, by decide⟩ ⟨113, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨53, by decide⟩ ⟨113, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨54, by decide⟩ ⟨113, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_fix ⟨55, by decide⟩ ⟨113, by decide⟩ p hp j hj hq fz1_55_113 fz2_55_113
  · exact match_zero_fix ⟨56, by decide⟩ ⟨113, by decide⟩ p hp j hj hq fz1_56_113 fz2_56_113
  · exact match_zero_fix ⟨57, by decide⟩ ⟨113, by decide⟩ p hp j hj hq fz1_57_113 fz2_57_113
  · exact match_zero_fix ⟨58, by decide⟩ ⟨113, by decide⟩ p hp j hj hq fz1_58_113 fz2_58_113
  · exact match_zero_fix ⟨59, by decide⟩ ⟨113, by decide⟩ p hp j hj hq fz1_59_113 fz2_59_113
  · exact match_zero_fix ⟨60, by decide⟩ ⟨113, by decide⟩ p hp j hj hq fz1_60_113 fz2_60_113
  · exact match_zero_fix ⟨61, by decide⟩ ⟨113, by decide⟩ p hp j hj hq fz1_61_113 fz2_61_113
  · exact match_zero_fix ⟨62, by decide⟩ ⟨113, by decide⟩ p hp j hj hq fz1_62_113 fz2_62_113
  · exact match_zero_fix ⟨63, by decide⟩ ⟨113, by decide⟩ p hp j hj hq fz1_63_113 fz2_63_113
  · exact match_zero_fix ⟨64, by decide⟩ ⟨113, by decide⟩ p hp j hj hq fz1_64_113 fz2_64_113
  · exact match_zero_fix ⟨65, by decide⟩ ⟨113, by decide⟩ p hp j hj hq fz1_65_113 fz2_65_113
  · exact match_zero_fix ⟨66, by decide⟩ ⟨113, by decide⟩ p hp j hj hq fz1_66_113 fz2_66_113
  · exact match_zero_fix ⟨67, by decide⟩ ⟨113, by decide⟩ p hp j hj hq fz1_67_113 fz2_67_113
  · exact match_zero_fix ⟨68, by decide⟩ ⟨113, by decide⟩ p hp j hj hq fz1_68_113 fz2_68_113
  · exact match_zero_fix ⟨69, by decide⟩ ⟨113, by decide⟩ p hp j hj hq fz1_69_113 fz2_69_113
  · exact match_zero_fix ⟨70, by decide⟩ ⟨113, by decide⟩ p hp j hj hq fz1_70_113 fz2_70_113
  · exact match_zero_fix ⟨71, by decide⟩ ⟨113, by decide⟩ p hp j hj hq fz1_71_113 fz2_71_113
  · exact match_zero_fix ⟨72, by decide⟩ ⟨113, by decide⟩ p hp j hj hq fz1_72_113 fz2_72_113
  · exact match_zero_fix ⟨73, by decide⟩ ⟨113, by decide⟩ p hp j hj hq fz1_73_113 fz2_73_113
  · exact match_zero_fix ⟨74, by decide⟩ ⟨113, by decide⟩ p hp j hj hq fz1_74_113 fz2_74_113
  · exact match_zero_fix ⟨75, by decide⟩ ⟨113, by decide⟩ p hp j hj hq fz1_75_113 fz2_75_113
  · exact match_zero_fix ⟨76, by decide⟩ ⟨113, by decide⟩ p hp j hj hq fz1_76_113 fz2_76_113
  · exact match_zero_fix ⟨77, by decide⟩ ⟨113, by decide⟩ p hp j hj hq fz1_77_113 fz2_77_113
  · exact match_zero_fix ⟨78, by decide⟩ ⟨113, by decide⟩ p hp j hj hq fz1_78_113 fz2_78_113
  · exact match_zero_fix ⟨79, by decide⟩ ⟨113, by decide⟩ p hp j hj hq fz1_79_113 fz2_79_113
  · exact match_zero_fix ⟨80, by decide⟩ ⟨113, by decide⟩ p hp j hj hq fz1_80_113 fz2_80_113
  · exact match_zero_fix ⟨81, by decide⟩ ⟨113, by decide⟩ p hp j hj hq fz1_81_113 fz2_81_113
  · exact match_zero_fix ⟨82, by decide⟩ ⟨113, by decide⟩ p hp j hj hq fz1_82_113 fz2_82_113
  · exact match_zero_fix ⟨83, by decide⟩ ⟨113, by decide⟩ p hp j hj hq fz1_83_113 fz2_83_113
  · exact match_zero_fix ⟨84, by decide⟩ ⟨113, by decide⟩ p hp j hj hq fz1_84_113 fz2_84_113
  · exact match_zero_fix ⟨85, by decide⟩ ⟨113, by decide⟩ p hp j hj hq fz1_85_113 fz2_85_113
  · exact match_zero_fix ⟨86, by decide⟩ ⟨113, by decide⟩ p hp j hj hq fz1_86_113 fz2_86_113
  · exact match_zero_fix ⟨87, by decide⟩ ⟨113, by decide⟩ p hp j hj hq fz1_87_113 fz2_87_113
  · exact match_zero_fix ⟨88, by decide⟩ ⟨113, by decide⟩ p hp j hj hq fz1_88_113 fz2_88_113
  · exact match_zero_fix ⟨89, by decide⟩ ⟨113, by decide⟩ p hp j hj hq fz1_89_113 fz2_89_113
  · exact match_zero_fix ⟨90, by decide⟩ ⟨113, by decide⟩ p hp j hj hq fz1_90_113 fz2_90_113
  · exact match_zero_fix ⟨91, by decide⟩ ⟨113, by decide⟩ p hp j hj hq fz1_91_113 fz2_91_113
  · exact match_zero_fix ⟨92, by decide⟩ ⟨113, by decide⟩ p hp j hj hq fz1_92_113 fz2_92_113
  · exact match_zero_fix ⟨93, by decide⟩ ⟨113, by decide⟩ p hp j hj hq fz1_93_113 fz2_93_113
  · exact match_zero_fix ⟨94, by decide⟩ ⟨113, by decide⟩ p hp j hj hq fz1_94_113 fz2_94_113
  · exact match_zero_fix ⟨95, by decide⟩ ⟨113, by decide⟩ p hp j hj hq fz1_95_113 fz2_95_113
  · exact match_zero_fix ⟨96, by decide⟩ ⟨113, by decide⟩ p hp j hj hq fz1_96_113 fz2_96_113
  · exact match_zero_fix ⟨97, by decide⟩ ⟨113, by decide⟩ p hp j hj hq fz1_97_113 fz2_97_113
  · exact match_zero_fix ⟨98, by decide⟩ ⟨113, by decide⟩ p hp j hj hq fz1_98_113 fz2_98_113
  · exact match_zero_fix ⟨99, by decide⟩ ⟨113, by decide⟩ p hp j hj hq fz1_99_113 fz2_99_113
  · exact match_zero_fix ⟨100, by decide⟩ ⟨113, by decide⟩ p hp j hj hq fz1_100_113 fz2_100_113
  · exact match_zero_fix ⟨101, by decide⟩ ⟨113, by decide⟩ p hp j hj hq fz1_101_113 fz2_101_113
  · exact match_zero_fix ⟨102, by decide⟩ ⟨113, by decide⟩ p hp j hj hq fz1_102_113 fz2_102_113
  · exact match_zero_fix ⟨103, by decide⟩ ⟨113, by decide⟩ p hp j hj hq fz1_103_113 fz2_103_113
  · exact match_zero_fix ⟨104, by decide⟩ ⟨113, by decide⟩ p hp j hj hq fz1_104_113 fz2_104_113
  · exact match_zero_fix ⟨105, by decide⟩ ⟨113, by decide⟩ p hp j hj hq fz1_105_113 fz2_105_113
  · exact match_zero_fix ⟨106, by decide⟩ ⟨113, by decide⟩ p hp j hj hq fz1_106_113 fz2_106_113
  · exact match_zero_fix ⟨107, by decide⟩ ⟨113, by decide⟩ p hp j hj hq fz1_107_113 fz2_107_113
  · exact match_zero_fix ⟨108, by decide⟩ ⟨113, by decide⟩ p hp j hj hq fz1_108_113 fz2_108_113
  · exact match_zero_fix ⟨109, by decide⟩ ⟨113, by decide⟩ p hp j hj hq fz1_109_113 fz2_109_113
  · exact match_zero_fix ⟨110, by decide⟩ ⟨113, by decide⟩ p hp j hj hq fz1_110_113 fz2_110_113
  · exact match_zero_fix ⟨111, by decide⟩ ⟨113, by decide⟩ p hp j hj hq fz1_111_113 fz2_111_113
  · exact match_zero_fix ⟨112, by decide⟩ ⟨113, by decide⟩ p hp j hj hq fz1_112_113 fz2_112_113
  · exact pair_113_113 p hp hrep j hj hq
  · exact match_zero_fix ⟨114, by decide⟩ ⟨113, by decide⟩ p hp j hj hq fz1_114_113 fz2_114_113
  · exact match_zero_fix ⟨115, by decide⟩ ⟨113, by decide⟩ p hp j hj hq fz1_115_113 fz2_115_113
  · exact match_zero_fix ⟨116, by decide⟩ ⟨113, by decide⟩ p hp j hj hq fz1_116_113 fz2_116_113
  · exact match_zero_fix ⟨117, by decide⟩ ⟨113, by decide⟩ p hp j hj hq fz1_117_113 fz2_117_113
  · exact match_zero_fix ⟨118, by decide⟩ ⟨113, by decide⟩ p hp j hj hq fz1_118_113 fz2_118_113
  · exact pair_119_113 p hp hrep j hj hq
  · exact match_zero_fix ⟨120, by decide⟩ ⟨113, by decide⟩ p hp j hj hq fz1_120_113 fz2_120_113
  · exact match_zero_fix ⟨121, by decide⟩ ⟨113, by decide⟩ p hp j hj hq fz1_121_113 fz2_121_113
  · exact match_zero_fix ⟨122, by decide⟩ ⟨113, by decide⟩ p hp j hj hq fz1_122_113 fz2_122_113
  · exact match_zero_fix ⟨123, by decide⟩ ⟨113, by decide⟩ p hp j hj hq fz1_123_113 fz2_123_113
  · exact pair_124_113 p hp hrep j hj hq
  · exact match_zero_fix ⟨125, by decide⟩ ⟨113, by decide⟩ p hp j hj hq fz1_125_113 fz2_125_113
  · exact match_zero_fix ⟨126, by decide⟩ ⟨113, by decide⟩ p hp j hj hq fz1_126_113 fz2_126_113
  · exact match_zero_fix ⟨127, by decide⟩ ⟨113, by decide⟩ p hp j hj hq fz1_127_113 fz2_127_113
  · exact match_zero_fix ⟨128, by decide⟩ ⟨113, by decide⟩ p hp j hj hq fz1_128_113 fz2_128_113
  · exact pair_129_113 p hp hrep j hj hq
  · exact match_zero_fix ⟨130, by decide⟩ ⟨113, by decide⟩ p hp j hj hq fz1_130_113 fz2_130_113
  · exact match_zero_fix ⟨131, by decide⟩ ⟨113, by decide⟩ p hp j hj hq fz1_131_113 fz2_131_113
  · exact match_zero_fix ⟨132, by decide⟩ ⟨113, by decide⟩ p hp j hj hq fz1_132_113 fz2_132_113
  · exact match_zero_fix ⟨133, by decide⟩ ⟨113, by decide⟩ p hp j hj hq fz1_133_113 fz2_133_113
  · exact pair_134_113 p hp hrep j hj hq
  · exact match_zero_fix ⟨135, by decide⟩ ⟨113, by decide⟩ p hp j hj hq fz1_135_113 fz2_135_113
  · exact match_zero_fix ⟨136, by decide⟩ ⟨113, by decide⟩ p hp j hj hq fz1_136_113 fz2_136_113
  · exact match_zero_fix ⟨137, by decide⟩ ⟨113, by decide⟩ p hp j hj hq fz1_137_113 fz2_137_113
  · exact match_zero_fix ⟨138, by decide⟩ ⟨113, by decide⟩ p hp j hj hq fz1_138_113 fz2_138_113
  · exact pair_139_113 p hp hrep j hj hq
  · exact match_zero_fix ⟨140, by decide⟩ ⟨113, by decide⟩ p hp j hj hq fz1_140_113 fz2_140_113
  · exact match_zero_fix ⟨141, by decide⟩ ⟨113, by decide⟩ p hp j hj hq fz1_141_113 fz2_141_113
  · exact match_zero_fix ⟨142, by decide⟩ ⟨113, by decide⟩ p hp j hj hq fz1_142_113 fz2_142_113
  · exact match_zero_fix ⟨143, by decide⟩ ⟨113, by decide⟩ p hp j hj hq fz1_143_113 fz2_143_113
  · exact match_zero_fix ⟨144, by decide⟩ ⟨113, by decide⟩ p hp j hj hq fz1_144_113 fz2_144_113
  · exact match_zero_fix ⟨145, by decide⟩ ⟨113, by decide⟩ p hp j hj hq fz1_145_113 fz2_145_113
  · exact pair_146_113 p hp hrep j hj hq
  · exact pair_147_113 p hp hrep j hj hq

theorem master_114 (p : Nat) (hp : p < (Q2.transData.getD 114 []).length)
    (hrep : (Q2.cosetIsRep.getD 114 []).getD p false = true)
    (rK : Fin 148) (j : Nat) (hj : j < (repChars.getD rK.val []).length)
    (hq : (normIsRep.getD rK.val []).getD j false = true) :
    species (Q2.reps (⟨114, by decide⟩ : Fin 148)) (colE2 ⟨114, by decide⟩ p hp)
        (rowE2 rK j hj hq)
      = species (reps (⟨114, by decide⟩ : Fin 148))
        (colE1 ⟨114, by decide⟩ p (transLenTr ⟨114, by decide⟩ p hp)) (rowE1 rK j hj) := by
  rcases rK with ⟨nK, hnK⟩; interval_cases nK
  · exact match_zero_len ⟨0, by decide⟩ ⟨114, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨1, by decide⟩ ⟨114, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨2, by decide⟩ ⟨114, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨3, by decide⟩ ⟨114, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨4, by decide⟩ ⟨114, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨5, by decide⟩ ⟨114, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨6, by decide⟩ ⟨114, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨7, by decide⟩ ⟨114, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨8, by decide⟩ ⟨114, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨9, by decide⟩ ⟨114, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨10, by decide⟩ ⟨114, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨11, by decide⟩ ⟨114, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨12, by decide⟩ ⟨114, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨13, by decide⟩ ⟨114, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨14, by decide⟩ ⟨114, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨15, by decide⟩ ⟨114, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨16, by decide⟩ ⟨114, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨17, by decide⟩ ⟨114, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨18, by decide⟩ ⟨114, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨19, by decide⟩ ⟨114, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨20, by decide⟩ ⟨114, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨21, by decide⟩ ⟨114, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨22, by decide⟩ ⟨114, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨23, by decide⟩ ⟨114, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨24, by decide⟩ ⟨114, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨25, by decide⟩ ⟨114, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨26, by decide⟩ ⟨114, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨27, by decide⟩ ⟨114, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨28, by decide⟩ ⟨114, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨29, by decide⟩ ⟨114, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨30, by decide⟩ ⟨114, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨31, by decide⟩ ⟨114, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨32, by decide⟩ ⟨114, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨33, by decide⟩ ⟨114, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨34, by decide⟩ ⟨114, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨35, by decide⟩ ⟨114, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨36, by decide⟩ ⟨114, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨37, by decide⟩ ⟨114, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨38, by decide⟩ ⟨114, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨39, by decide⟩ ⟨114, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨40, by decide⟩ ⟨114, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨41, by decide⟩ ⟨114, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨42, by decide⟩ ⟨114, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨43, by decide⟩ ⟨114, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨44, by decide⟩ ⟨114, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨45, by decide⟩ ⟨114, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨46, by decide⟩ ⟨114, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨47, by decide⟩ ⟨114, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨48, by decide⟩ ⟨114, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨49, by decide⟩ ⟨114, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨50, by decide⟩ ⟨114, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨51, by decide⟩ ⟨114, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨52, by decide⟩ ⟨114, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨53, by decide⟩ ⟨114, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨54, by decide⟩ ⟨114, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_fix ⟨55, by decide⟩ ⟨114, by decide⟩ p hp j hj hq fz1_55_114 fz2_55_114
  · exact match_zero_fix ⟨56, by decide⟩ ⟨114, by decide⟩ p hp j hj hq fz1_56_114 fz2_56_114
  · exact match_zero_fix ⟨57, by decide⟩ ⟨114, by decide⟩ p hp j hj hq fz1_57_114 fz2_57_114
  · exact match_zero_fix ⟨58, by decide⟩ ⟨114, by decide⟩ p hp j hj hq fz1_58_114 fz2_58_114
  · exact match_zero_fix ⟨59, by decide⟩ ⟨114, by decide⟩ p hp j hj hq fz1_59_114 fz2_59_114
  · exact match_zero_fix ⟨60, by decide⟩ ⟨114, by decide⟩ p hp j hj hq fz1_60_114 fz2_60_114
  · exact match_zero_fix ⟨61, by decide⟩ ⟨114, by decide⟩ p hp j hj hq fz1_61_114 fz2_61_114
  · exact match_zero_fix ⟨62, by decide⟩ ⟨114, by decide⟩ p hp j hj hq fz1_62_114 fz2_62_114
  · exact match_zero_fix ⟨63, by decide⟩ ⟨114, by decide⟩ p hp j hj hq fz1_63_114 fz2_63_114
  · exact match_zero_fix ⟨64, by decide⟩ ⟨114, by decide⟩ p hp j hj hq fz1_64_114 fz2_64_114
  · exact match_zero_fix ⟨65, by decide⟩ ⟨114, by decide⟩ p hp j hj hq fz1_65_114 fz2_65_114
  · exact match_zero_fix ⟨66, by decide⟩ ⟨114, by decide⟩ p hp j hj hq fz1_66_114 fz2_66_114
  · exact match_zero_fix ⟨67, by decide⟩ ⟨114, by decide⟩ p hp j hj hq fz1_67_114 fz2_67_114
  · exact match_zero_fix ⟨68, by decide⟩ ⟨114, by decide⟩ p hp j hj hq fz1_68_114 fz2_68_114
  · exact match_zero_fix ⟨69, by decide⟩ ⟨114, by decide⟩ p hp j hj hq fz1_69_114 fz2_69_114
  · exact match_zero_fix ⟨70, by decide⟩ ⟨114, by decide⟩ p hp j hj hq fz1_70_114 fz2_70_114
  · exact match_zero_fix ⟨71, by decide⟩ ⟨114, by decide⟩ p hp j hj hq fz1_71_114 fz2_71_114
  · exact match_zero_fix ⟨72, by decide⟩ ⟨114, by decide⟩ p hp j hj hq fz1_72_114 fz2_72_114
  · exact match_zero_fix ⟨73, by decide⟩ ⟨114, by decide⟩ p hp j hj hq fz1_73_114 fz2_73_114
  · exact match_zero_fix ⟨74, by decide⟩ ⟨114, by decide⟩ p hp j hj hq fz1_74_114 fz2_74_114
  · exact match_zero_fix ⟨75, by decide⟩ ⟨114, by decide⟩ p hp j hj hq fz1_75_114 fz2_75_114
  · exact match_zero_fix ⟨76, by decide⟩ ⟨114, by decide⟩ p hp j hj hq fz1_76_114 fz2_76_114
  · exact match_zero_fix ⟨77, by decide⟩ ⟨114, by decide⟩ p hp j hj hq fz1_77_114 fz2_77_114
  · exact match_zero_fix ⟨78, by decide⟩ ⟨114, by decide⟩ p hp j hj hq fz1_78_114 fz2_78_114
  · exact match_zero_fix ⟨79, by decide⟩ ⟨114, by decide⟩ p hp j hj hq fz1_79_114 fz2_79_114
  · exact match_zero_fix ⟨80, by decide⟩ ⟨114, by decide⟩ p hp j hj hq fz1_80_114 fz2_80_114
  · exact match_zero_fix ⟨81, by decide⟩ ⟨114, by decide⟩ p hp j hj hq fz1_81_114 fz2_81_114
  · exact match_zero_fix ⟨82, by decide⟩ ⟨114, by decide⟩ p hp j hj hq fz1_82_114 fz2_82_114
  · exact match_zero_fix ⟨83, by decide⟩ ⟨114, by decide⟩ p hp j hj hq fz1_83_114 fz2_83_114
  · exact match_zero_fix ⟨84, by decide⟩ ⟨114, by decide⟩ p hp j hj hq fz1_84_114 fz2_84_114
  · exact match_zero_fix ⟨85, by decide⟩ ⟨114, by decide⟩ p hp j hj hq fz1_85_114 fz2_85_114
  · exact match_zero_fix ⟨86, by decide⟩ ⟨114, by decide⟩ p hp j hj hq fz1_86_114 fz2_86_114
  · exact match_zero_fix ⟨87, by decide⟩ ⟨114, by decide⟩ p hp j hj hq fz1_87_114 fz2_87_114
  · exact match_zero_fix ⟨88, by decide⟩ ⟨114, by decide⟩ p hp j hj hq fz1_88_114 fz2_88_114
  · exact match_zero_fix ⟨89, by decide⟩ ⟨114, by decide⟩ p hp j hj hq fz1_89_114 fz2_89_114
  · exact match_zero_fix ⟨90, by decide⟩ ⟨114, by decide⟩ p hp j hj hq fz1_90_114 fz2_90_114
  · exact match_zero_fix ⟨91, by decide⟩ ⟨114, by decide⟩ p hp j hj hq fz1_91_114 fz2_91_114
  · exact match_zero_fix ⟨92, by decide⟩ ⟨114, by decide⟩ p hp j hj hq fz1_92_114 fz2_92_114
  · exact match_zero_fix ⟨93, by decide⟩ ⟨114, by decide⟩ p hp j hj hq fz1_93_114 fz2_93_114
  · exact match_zero_fix ⟨94, by decide⟩ ⟨114, by decide⟩ p hp j hj hq fz1_94_114 fz2_94_114
  · exact match_zero_fix ⟨95, by decide⟩ ⟨114, by decide⟩ p hp j hj hq fz1_95_114 fz2_95_114
  · exact match_zero_fix ⟨96, by decide⟩ ⟨114, by decide⟩ p hp j hj hq fz1_96_114 fz2_96_114
  · exact match_zero_fix ⟨97, by decide⟩ ⟨114, by decide⟩ p hp j hj hq fz1_97_114 fz2_97_114
  · exact match_zero_fix ⟨98, by decide⟩ ⟨114, by decide⟩ p hp j hj hq fz1_98_114 fz2_98_114
  · exact match_zero_fix ⟨99, by decide⟩ ⟨114, by decide⟩ p hp j hj hq fz1_99_114 fz2_99_114
  · exact match_zero_fix ⟨100, by decide⟩ ⟨114, by decide⟩ p hp j hj hq fz1_100_114 fz2_100_114
  · exact match_zero_fix ⟨101, by decide⟩ ⟨114, by decide⟩ p hp j hj hq fz1_101_114 fz2_101_114
  · exact match_zero_fix ⟨102, by decide⟩ ⟨114, by decide⟩ p hp j hj hq fz1_102_114 fz2_102_114
  · exact match_zero_fix ⟨103, by decide⟩ ⟨114, by decide⟩ p hp j hj hq fz1_103_114 fz2_103_114
  · exact match_zero_fix ⟨104, by decide⟩ ⟨114, by decide⟩ p hp j hj hq fz1_104_114 fz2_104_114
  · exact match_zero_fix ⟨105, by decide⟩ ⟨114, by decide⟩ p hp j hj hq fz1_105_114 fz2_105_114
  · exact match_zero_fix ⟨106, by decide⟩ ⟨114, by decide⟩ p hp j hj hq fz1_106_114 fz2_106_114
  · exact match_zero_fix ⟨107, by decide⟩ ⟨114, by decide⟩ p hp j hj hq fz1_107_114 fz2_107_114
  · exact match_zero_fix ⟨108, by decide⟩ ⟨114, by decide⟩ p hp j hj hq fz1_108_114 fz2_108_114
  · exact match_zero_fix ⟨109, by decide⟩ ⟨114, by decide⟩ p hp j hj hq fz1_109_114 fz2_109_114
  · exact match_zero_fix ⟨110, by decide⟩ ⟨114, by decide⟩ p hp j hj hq fz1_110_114 fz2_110_114
  · exact match_zero_fix ⟨111, by decide⟩ ⟨114, by decide⟩ p hp j hj hq fz1_111_114 fz2_111_114
  · exact match_zero_fix ⟨112, by decide⟩ ⟨114, by decide⟩ p hp j hj hq fz1_112_114 fz2_112_114
  · exact match_zero_fix ⟨113, by decide⟩ ⟨114, by decide⟩ p hp j hj hq fz1_113_114 fz2_113_114
  · exact pair_114_114 p hp hrep j hj hq
  · exact match_zero_fix ⟨115, by decide⟩ ⟨114, by decide⟩ p hp j hj hq fz1_115_114 fz2_115_114
  · exact match_zero_fix ⟨116, by decide⟩ ⟨114, by decide⟩ p hp j hj hq fz1_116_114 fz2_116_114
  · exact match_zero_fix ⟨117, by decide⟩ ⟨114, by decide⟩ p hp j hj hq fz1_117_114 fz2_117_114
  · exact match_zero_fix ⟨118, by decide⟩ ⟨114, by decide⟩ p hp j hj hq fz1_118_114 fz2_118_114
  · exact match_zero_fix ⟨119, by decide⟩ ⟨114, by decide⟩ p hp j hj hq fz1_119_114 fz2_119_114
  · exact pair_120_114 p hp hrep j hj hq
  · exact match_zero_fix ⟨121, by decide⟩ ⟨114, by decide⟩ p hp j hj hq fz1_121_114 fz2_121_114
  · exact match_zero_fix ⟨122, by decide⟩ ⟨114, by decide⟩ p hp j hj hq fz1_122_114 fz2_122_114
  · exact match_zero_fix ⟨123, by decide⟩ ⟨114, by decide⟩ p hp j hj hq fz1_123_114 fz2_123_114
  · exact match_zero_fix ⟨124, by decide⟩ ⟨114, by decide⟩ p hp j hj hq fz1_124_114 fz2_124_114
  · exact pair_125_114 p hp hrep j hj hq
  · exact match_zero_fix ⟨126, by decide⟩ ⟨114, by decide⟩ p hp j hj hq fz1_126_114 fz2_126_114
  · exact match_zero_fix ⟨127, by decide⟩ ⟨114, by decide⟩ p hp j hj hq fz1_127_114 fz2_127_114
  · exact match_zero_fix ⟨128, by decide⟩ ⟨114, by decide⟩ p hp j hj hq fz1_128_114 fz2_128_114
  · exact match_zero_fix ⟨129, by decide⟩ ⟨114, by decide⟩ p hp j hj hq fz1_129_114 fz2_129_114
  · exact pair_130_114 p hp hrep j hj hq
  · exact match_zero_fix ⟨131, by decide⟩ ⟨114, by decide⟩ p hp j hj hq fz1_131_114 fz2_131_114
  · exact match_zero_fix ⟨132, by decide⟩ ⟨114, by decide⟩ p hp j hj hq fz1_132_114 fz2_132_114
  · exact match_zero_fix ⟨133, by decide⟩ ⟨114, by decide⟩ p hp j hj hq fz1_133_114 fz2_133_114
  · exact match_zero_fix ⟨134, by decide⟩ ⟨114, by decide⟩ p hp j hj hq fz1_134_114 fz2_134_114
  · exact pair_135_114 p hp hrep j hj hq
  · exact match_zero_fix ⟨136, by decide⟩ ⟨114, by decide⟩ p hp j hj hq fz1_136_114 fz2_136_114
  · exact match_zero_fix ⟨137, by decide⟩ ⟨114, by decide⟩ p hp j hj hq fz1_137_114 fz2_137_114
  · exact match_zero_fix ⟨138, by decide⟩ ⟨114, by decide⟩ p hp j hj hq fz1_138_114 fz2_138_114
  · exact match_zero_fix ⟨139, by decide⟩ ⟨114, by decide⟩ p hp j hj hq fz1_139_114 fz2_139_114
  · exact pair_140_114 p hp hrep j hj hq
  · exact match_zero_fix ⟨141, by decide⟩ ⟨114, by decide⟩ p hp j hj hq fz1_141_114 fz2_141_114
  · exact match_zero_fix ⟨142, by decide⟩ ⟨114, by decide⟩ p hp j hj hq fz1_142_114 fz2_142_114
  · exact match_zero_fix ⟨143, by decide⟩ ⟨114, by decide⟩ p hp j hj hq fz1_143_114 fz2_143_114
  · exact match_zero_fix ⟨144, by decide⟩ ⟨114, by decide⟩ p hp j hj hq fz1_144_114 fz2_144_114
  · exact match_zero_fix ⟨145, by decide⟩ ⟨114, by decide⟩ p hp j hj hq fz1_145_114 fz2_145_114
  · exact pair_146_114 p hp hrep j hj hq
  · exact pair_147_114 p hp hrep j hj hq

theorem master_115 (p : Nat) (hp : p < (Q2.transData.getD 115 []).length)
    (hrep : (Q2.cosetIsRep.getD 115 []).getD p false = true)
    (rK : Fin 148) (j : Nat) (hj : j < (repChars.getD rK.val []).length)
    (hq : (normIsRep.getD rK.val []).getD j false = true) :
    species (Q2.reps (⟨115, by decide⟩ : Fin 148)) (colE2 ⟨115, by decide⟩ p hp)
        (rowE2 rK j hj hq)
      = species (reps (⟨115, by decide⟩ : Fin 148))
        (colE1 ⟨115, by decide⟩ p (transLenTr ⟨115, by decide⟩ p hp)) (rowE1 rK j hj) := by
  rcases rK with ⟨nK, hnK⟩; interval_cases nK
  · exact match_zero_len ⟨0, by decide⟩ ⟨115, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨1, by decide⟩ ⟨115, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨2, by decide⟩ ⟨115, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨3, by decide⟩ ⟨115, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨4, by decide⟩ ⟨115, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨5, by decide⟩ ⟨115, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨6, by decide⟩ ⟨115, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨7, by decide⟩ ⟨115, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨8, by decide⟩ ⟨115, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨9, by decide⟩ ⟨115, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨10, by decide⟩ ⟨115, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨11, by decide⟩ ⟨115, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨12, by decide⟩ ⟨115, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨13, by decide⟩ ⟨115, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨14, by decide⟩ ⟨115, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨15, by decide⟩ ⟨115, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨16, by decide⟩ ⟨115, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨17, by decide⟩ ⟨115, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨18, by decide⟩ ⟨115, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨19, by decide⟩ ⟨115, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨20, by decide⟩ ⟨115, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨21, by decide⟩ ⟨115, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨22, by decide⟩ ⟨115, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨23, by decide⟩ ⟨115, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨24, by decide⟩ ⟨115, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨25, by decide⟩ ⟨115, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨26, by decide⟩ ⟨115, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨27, by decide⟩ ⟨115, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨28, by decide⟩ ⟨115, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨29, by decide⟩ ⟨115, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨30, by decide⟩ ⟨115, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨31, by decide⟩ ⟨115, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨32, by decide⟩ ⟨115, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨33, by decide⟩ ⟨115, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨34, by decide⟩ ⟨115, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨35, by decide⟩ ⟨115, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨36, by decide⟩ ⟨115, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨37, by decide⟩ ⟨115, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨38, by decide⟩ ⟨115, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨39, by decide⟩ ⟨115, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨40, by decide⟩ ⟨115, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨41, by decide⟩ ⟨115, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨42, by decide⟩ ⟨115, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨43, by decide⟩ ⟨115, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨44, by decide⟩ ⟨115, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨45, by decide⟩ ⟨115, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨46, by decide⟩ ⟨115, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨47, by decide⟩ ⟨115, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨48, by decide⟩ ⟨115, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨49, by decide⟩ ⟨115, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨50, by decide⟩ ⟨115, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨51, by decide⟩ ⟨115, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨52, by decide⟩ ⟨115, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨53, by decide⟩ ⟨115, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨54, by decide⟩ ⟨115, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_fix ⟨55, by decide⟩ ⟨115, by decide⟩ p hp j hj hq fz1_55_115 fz2_55_115
  · exact match_zero_fix ⟨56, by decide⟩ ⟨115, by decide⟩ p hp j hj hq fz1_56_115 fz2_56_115
  · exact match_zero_fix ⟨57, by decide⟩ ⟨115, by decide⟩ p hp j hj hq fz1_57_115 fz2_57_115
  · exact match_zero_fix ⟨58, by decide⟩ ⟨115, by decide⟩ p hp j hj hq fz1_58_115 fz2_58_115
  · exact match_zero_fix ⟨59, by decide⟩ ⟨115, by decide⟩ p hp j hj hq fz1_59_115 fz2_59_115
  · exact match_zero_fix ⟨60, by decide⟩ ⟨115, by decide⟩ p hp j hj hq fz1_60_115 fz2_60_115
  · exact match_zero_fix ⟨61, by decide⟩ ⟨115, by decide⟩ p hp j hj hq fz1_61_115 fz2_61_115
  · exact match_zero_fix ⟨62, by decide⟩ ⟨115, by decide⟩ p hp j hj hq fz1_62_115 fz2_62_115
  · exact match_zero_fix ⟨63, by decide⟩ ⟨115, by decide⟩ p hp j hj hq fz1_63_115 fz2_63_115
  · exact match_zero_fix ⟨64, by decide⟩ ⟨115, by decide⟩ p hp j hj hq fz1_64_115 fz2_64_115
  · exact match_zero_fix ⟨65, by decide⟩ ⟨115, by decide⟩ p hp j hj hq fz1_65_115 fz2_65_115
  · exact match_zero_fix ⟨66, by decide⟩ ⟨115, by decide⟩ p hp j hj hq fz1_66_115 fz2_66_115
  · exact match_zero_fix ⟨67, by decide⟩ ⟨115, by decide⟩ p hp j hj hq fz1_67_115 fz2_67_115
  · exact match_zero_fix ⟨68, by decide⟩ ⟨115, by decide⟩ p hp j hj hq fz1_68_115 fz2_68_115
  · exact match_zero_fix ⟨69, by decide⟩ ⟨115, by decide⟩ p hp j hj hq fz1_69_115 fz2_69_115
  · exact match_zero_fix ⟨70, by decide⟩ ⟨115, by decide⟩ p hp j hj hq fz1_70_115 fz2_70_115
  · exact match_zero_fix ⟨71, by decide⟩ ⟨115, by decide⟩ p hp j hj hq fz1_71_115 fz2_71_115
  · exact match_zero_fix ⟨72, by decide⟩ ⟨115, by decide⟩ p hp j hj hq fz1_72_115 fz2_72_115
  · exact match_zero_fix ⟨73, by decide⟩ ⟨115, by decide⟩ p hp j hj hq fz1_73_115 fz2_73_115
  · exact match_zero_fix ⟨74, by decide⟩ ⟨115, by decide⟩ p hp j hj hq fz1_74_115 fz2_74_115
  · exact match_zero_fix ⟨75, by decide⟩ ⟨115, by decide⟩ p hp j hj hq fz1_75_115 fz2_75_115
  · exact match_zero_fix ⟨76, by decide⟩ ⟨115, by decide⟩ p hp j hj hq fz1_76_115 fz2_76_115
  · exact match_zero_fix ⟨77, by decide⟩ ⟨115, by decide⟩ p hp j hj hq fz1_77_115 fz2_77_115
  · exact match_zero_fix ⟨78, by decide⟩ ⟨115, by decide⟩ p hp j hj hq fz1_78_115 fz2_78_115
  · exact match_zero_fix ⟨79, by decide⟩ ⟨115, by decide⟩ p hp j hj hq fz1_79_115 fz2_79_115
  · exact match_zero_fix ⟨80, by decide⟩ ⟨115, by decide⟩ p hp j hj hq fz1_80_115 fz2_80_115
  · exact match_zero_fix ⟨81, by decide⟩ ⟨115, by decide⟩ p hp j hj hq fz1_81_115 fz2_81_115
  · exact match_zero_fix ⟨82, by decide⟩ ⟨115, by decide⟩ p hp j hj hq fz1_82_115 fz2_82_115
  · exact match_zero_fix ⟨83, by decide⟩ ⟨115, by decide⟩ p hp j hj hq fz1_83_115 fz2_83_115
  · exact match_zero_fix ⟨84, by decide⟩ ⟨115, by decide⟩ p hp j hj hq fz1_84_115 fz2_84_115
  · exact match_zero_fix ⟨85, by decide⟩ ⟨115, by decide⟩ p hp j hj hq fz1_85_115 fz2_85_115
  · exact match_zero_fix ⟨86, by decide⟩ ⟨115, by decide⟩ p hp j hj hq fz1_86_115 fz2_86_115
  · exact match_zero_fix ⟨87, by decide⟩ ⟨115, by decide⟩ p hp j hj hq fz1_87_115 fz2_87_115
  · exact match_zero_fix ⟨88, by decide⟩ ⟨115, by decide⟩ p hp j hj hq fz1_88_115 fz2_88_115
  · exact match_zero_fix ⟨89, by decide⟩ ⟨115, by decide⟩ p hp j hj hq fz1_89_115 fz2_89_115
  · exact match_zero_fix ⟨90, by decide⟩ ⟨115, by decide⟩ p hp j hj hq fz1_90_115 fz2_90_115
  · exact match_zero_fix ⟨91, by decide⟩ ⟨115, by decide⟩ p hp j hj hq fz1_91_115 fz2_91_115
  · exact match_zero_fix ⟨92, by decide⟩ ⟨115, by decide⟩ p hp j hj hq fz1_92_115 fz2_92_115
  · exact match_zero_fix ⟨93, by decide⟩ ⟨115, by decide⟩ p hp j hj hq fz1_93_115 fz2_93_115
  · exact match_zero_fix ⟨94, by decide⟩ ⟨115, by decide⟩ p hp j hj hq fz1_94_115 fz2_94_115
  · exact match_zero_fix ⟨95, by decide⟩ ⟨115, by decide⟩ p hp j hj hq fz1_95_115 fz2_95_115
  · exact match_zero_fix ⟨96, by decide⟩ ⟨115, by decide⟩ p hp j hj hq fz1_96_115 fz2_96_115
  · exact match_zero_fix ⟨97, by decide⟩ ⟨115, by decide⟩ p hp j hj hq fz1_97_115 fz2_97_115
  · exact match_zero_fix ⟨98, by decide⟩ ⟨115, by decide⟩ p hp j hj hq fz1_98_115 fz2_98_115
  · exact match_zero_fix ⟨99, by decide⟩ ⟨115, by decide⟩ p hp j hj hq fz1_99_115 fz2_99_115
  · exact match_zero_fix ⟨100, by decide⟩ ⟨115, by decide⟩ p hp j hj hq fz1_100_115 fz2_100_115
  · exact match_zero_fix ⟨101, by decide⟩ ⟨115, by decide⟩ p hp j hj hq fz1_101_115 fz2_101_115
  · exact match_zero_fix ⟨102, by decide⟩ ⟨115, by decide⟩ p hp j hj hq fz1_102_115 fz2_102_115
  · exact match_zero_fix ⟨103, by decide⟩ ⟨115, by decide⟩ p hp j hj hq fz1_103_115 fz2_103_115
  · exact match_zero_fix ⟨104, by decide⟩ ⟨115, by decide⟩ p hp j hj hq fz1_104_115 fz2_104_115
  · exact match_zero_fix ⟨105, by decide⟩ ⟨115, by decide⟩ p hp j hj hq fz1_105_115 fz2_105_115
  · exact match_zero_fix ⟨106, by decide⟩ ⟨115, by decide⟩ p hp j hj hq fz1_106_115 fz2_106_115
  · exact match_zero_fix ⟨107, by decide⟩ ⟨115, by decide⟩ p hp j hj hq fz1_107_115 fz2_107_115
  · exact match_zero_fix ⟨108, by decide⟩ ⟨115, by decide⟩ p hp j hj hq fz1_108_115 fz2_108_115
  · exact match_zero_fix ⟨109, by decide⟩ ⟨115, by decide⟩ p hp j hj hq fz1_109_115 fz2_109_115
  · exact match_zero_fix ⟨110, by decide⟩ ⟨115, by decide⟩ p hp j hj hq fz1_110_115 fz2_110_115
  · exact match_zero_fix ⟨111, by decide⟩ ⟨115, by decide⟩ p hp j hj hq fz1_111_115 fz2_111_115
  · exact match_zero_fix ⟨112, by decide⟩ ⟨115, by decide⟩ p hp j hj hq fz1_112_115 fz2_112_115
  · exact match_zero_fix ⟨113, by decide⟩ ⟨115, by decide⟩ p hp j hj hq fz1_113_115 fz2_113_115
  · exact match_zero_fix ⟨114, by decide⟩ ⟨115, by decide⟩ p hp j hj hq fz1_114_115 fz2_114_115
  · exact pair_115_115 p hp hrep j hj hq
  · exact match_zero_fix ⟨116, by decide⟩ ⟨115, by decide⟩ p hp j hj hq fz1_116_115 fz2_116_115
  · exact match_zero_fix ⟨117, by decide⟩ ⟨115, by decide⟩ p hp j hj hq fz1_117_115 fz2_117_115
  · exact match_zero_fix ⟨118, by decide⟩ ⟨115, by decide⟩ p hp j hj hq fz1_118_115 fz2_118_115
  · exact match_zero_fix ⟨119, by decide⟩ ⟨115, by decide⟩ p hp j hj hq fz1_119_115 fz2_119_115
  · exact match_zero_fix ⟨120, by decide⟩ ⟨115, by decide⟩ p hp j hj hq fz1_120_115 fz2_120_115
  · exact match_zero_fix ⟨121, by decide⟩ ⟨115, by decide⟩ p hp j hj hq fz1_121_115 fz2_121_115
  · exact match_zero_fix ⟨122, by decide⟩ ⟨115, by decide⟩ p hp j hj hq fz1_122_115 fz2_122_115
  · exact match_zero_fix ⟨123, by decide⟩ ⟨115, by decide⟩ p hp j hj hq fz1_123_115 fz2_123_115
  · exact match_zero_fix ⟨124, by decide⟩ ⟨115, by decide⟩ p hp j hj hq fz1_124_115 fz2_124_115
  · exact match_zero_fix ⟨125, by decide⟩ ⟨115, by decide⟩ p hp j hj hq fz1_125_115 fz2_125_115
  · exact match_zero_fix ⟨126, by decide⟩ ⟨115, by decide⟩ p hp j hj hq fz1_126_115 fz2_126_115
  · exact match_zero_fix ⟨127, by decide⟩ ⟨115, by decide⟩ p hp j hj hq fz1_127_115 fz2_127_115
  · exact match_zero_fix ⟨128, by decide⟩ ⟨115, by decide⟩ p hp j hj hq fz1_128_115 fz2_128_115
  · exact match_zero_fix ⟨129, by decide⟩ ⟨115, by decide⟩ p hp j hj hq fz1_129_115 fz2_129_115
  · exact match_zero_fix ⟨130, by decide⟩ ⟨115, by decide⟩ p hp j hj hq fz1_130_115 fz2_130_115
  · exact match_zero_fix ⟨131, by decide⟩ ⟨115, by decide⟩ p hp j hj hq fz1_131_115 fz2_131_115
  · exact match_zero_fix ⟨132, by decide⟩ ⟨115, by decide⟩ p hp j hj hq fz1_132_115 fz2_132_115
  · exact match_zero_fix ⟨133, by decide⟩ ⟨115, by decide⟩ p hp j hj hq fz1_133_115 fz2_133_115
  · exact match_zero_fix ⟨134, by decide⟩ ⟨115, by decide⟩ p hp j hj hq fz1_134_115 fz2_134_115
  · exact match_zero_fix ⟨135, by decide⟩ ⟨115, by decide⟩ p hp j hj hq fz1_135_115 fz2_135_115
  · exact match_zero_fix ⟨136, by decide⟩ ⟨115, by decide⟩ p hp j hj hq fz1_136_115 fz2_136_115
  · exact match_zero_fix ⟨137, by decide⟩ ⟨115, by decide⟩ p hp j hj hq fz1_137_115 fz2_137_115
  · exact match_zero_fix ⟨138, by decide⟩ ⟨115, by decide⟩ p hp j hj hq fz1_138_115 fz2_138_115
  · exact match_zero_fix ⟨139, by decide⟩ ⟨115, by decide⟩ p hp j hj hq fz1_139_115 fz2_139_115
  · exact match_zero_fix ⟨140, by decide⟩ ⟨115, by decide⟩ p hp j hj hq fz1_140_115 fz2_140_115
  · exact pair_141_115 p hp hrep j hj hq
  · exact pair_142_115 p hp hrep j hj hq
  · exact pair_143_115 p hp hrep j hj hq
  · exact pair_144_115 p hp hrep j hj hq
  · exact pair_145_115 p hp hrep j hj hq
  · exact pair_146_115 p hp hrep j hj hq
  · exact pair_147_115 p hp hrep j hj hq

theorem master_116 (p : Nat) (hp : p < (Q2.transData.getD 116 []).length)
    (hrep : (Q2.cosetIsRep.getD 116 []).getD p false = true)
    (rK : Fin 148) (j : Nat) (hj : j < (repChars.getD rK.val []).length)
    (hq : (normIsRep.getD rK.val []).getD j false = true) :
    species (Q2.reps (⟨116, by decide⟩ : Fin 148)) (colE2 ⟨116, by decide⟩ p hp)
        (rowE2 rK j hj hq)
      = species (reps (⟨116, by decide⟩ : Fin 148))
        (colE1 ⟨116, by decide⟩ p (transLenTr ⟨116, by decide⟩ p hp)) (rowE1 rK j hj) := by
  rcases rK with ⟨nK, hnK⟩; interval_cases nK
  · exact match_zero_len ⟨0, by decide⟩ ⟨116, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨1, by decide⟩ ⟨116, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨2, by decide⟩ ⟨116, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨3, by decide⟩ ⟨116, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨4, by decide⟩ ⟨116, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨5, by decide⟩ ⟨116, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨6, by decide⟩ ⟨116, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨7, by decide⟩ ⟨116, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨8, by decide⟩ ⟨116, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨9, by decide⟩ ⟨116, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨10, by decide⟩ ⟨116, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨11, by decide⟩ ⟨116, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨12, by decide⟩ ⟨116, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨13, by decide⟩ ⟨116, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨14, by decide⟩ ⟨116, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨15, by decide⟩ ⟨116, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨16, by decide⟩ ⟨116, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨17, by decide⟩ ⟨116, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨18, by decide⟩ ⟨116, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨19, by decide⟩ ⟨116, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨20, by decide⟩ ⟨116, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨21, by decide⟩ ⟨116, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨22, by decide⟩ ⟨116, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨23, by decide⟩ ⟨116, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨24, by decide⟩ ⟨116, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨25, by decide⟩ ⟨116, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨26, by decide⟩ ⟨116, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨27, by decide⟩ ⟨116, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨28, by decide⟩ ⟨116, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨29, by decide⟩ ⟨116, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨30, by decide⟩ ⟨116, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨31, by decide⟩ ⟨116, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨32, by decide⟩ ⟨116, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨33, by decide⟩ ⟨116, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨34, by decide⟩ ⟨116, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨35, by decide⟩ ⟨116, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨36, by decide⟩ ⟨116, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨37, by decide⟩ ⟨116, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨38, by decide⟩ ⟨116, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨39, by decide⟩ ⟨116, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨40, by decide⟩ ⟨116, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨41, by decide⟩ ⟨116, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨42, by decide⟩ ⟨116, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨43, by decide⟩ ⟨116, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨44, by decide⟩ ⟨116, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨45, by decide⟩ ⟨116, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨46, by decide⟩ ⟨116, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨47, by decide⟩ ⟨116, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨48, by decide⟩ ⟨116, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨49, by decide⟩ ⟨116, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨50, by decide⟩ ⟨116, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨51, by decide⟩ ⟨116, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨52, by decide⟩ ⟨116, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨53, by decide⟩ ⟨116, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨54, by decide⟩ ⟨116, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨55, by decide⟩ ⟨116, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨56, by decide⟩ ⟨116, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨57, by decide⟩ ⟨116, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨58, by decide⟩ ⟨116, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨59, by decide⟩ ⟨116, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨60, by decide⟩ ⟨116, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨61, by decide⟩ ⟨116, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨62, by decide⟩ ⟨116, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨63, by decide⟩ ⟨116, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨64, by decide⟩ ⟨116, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨65, by decide⟩ ⟨116, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨66, by decide⟩ ⟨116, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨67, by decide⟩ ⟨116, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨68, by decide⟩ ⟨116, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨69, by decide⟩ ⟨116, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨70, by decide⟩ ⟨116, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨71, by decide⟩ ⟨116, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨72, by decide⟩ ⟨116, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨73, by decide⟩ ⟨116, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨74, by decide⟩ ⟨116, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨75, by decide⟩ ⟨116, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨76, by decide⟩ ⟨116, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨77, by decide⟩ ⟨116, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨78, by decide⟩ ⟨116, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨79, by decide⟩ ⟨116, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨80, by decide⟩ ⟨116, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨81, by decide⟩ ⟨116, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨82, by decide⟩ ⟨116, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨83, by decide⟩ ⟨116, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨84, by decide⟩ ⟨116, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨85, by decide⟩ ⟨116, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨86, by decide⟩ ⟨116, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨87, by decide⟩ ⟨116, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨88, by decide⟩ ⟨116, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨89, by decide⟩ ⟨116, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨90, by decide⟩ ⟨116, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨91, by decide⟩ ⟨116, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨92, by decide⟩ ⟨116, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨93, by decide⟩ ⟨116, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨94, by decide⟩ ⟨116, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨95, by decide⟩ ⟨116, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨96, by decide⟩ ⟨116, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨97, by decide⟩ ⟨116, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨98, by decide⟩ ⟨116, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨99, by decide⟩ ⟨116, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨100, by decide⟩ ⟨116, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨101, by decide⟩ ⟨116, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨102, by decide⟩ ⟨116, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨103, by decide⟩ ⟨116, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨104, by decide⟩ ⟨116, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨105, by decide⟩ ⟨116, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨106, by decide⟩ ⟨116, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨107, by decide⟩ ⟨116, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨108, by decide⟩ ⟨116, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨109, by decide⟩ ⟨116, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨110, by decide⟩ ⟨116, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨111, by decide⟩ ⟨116, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨112, by decide⟩ ⟨116, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨113, by decide⟩ ⟨116, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨114, by decide⟩ ⟨116, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨115, by decide⟩ ⟨116, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact pair_116_116 p hp hrep j hj hq
  · exact match_zero_fix ⟨117, by decide⟩ ⟨116, by decide⟩ p hp j hj hq fz1_117_116 fz2_117_116
  · exact match_zero_fix ⟨118, by decide⟩ ⟨116, by decide⟩ p hp j hj hq fz1_118_116 fz2_118_116
  · exact match_zero_fix ⟨119, by decide⟩ ⟨116, by decide⟩ p hp j hj hq fz1_119_116 fz2_119_116
  · exact match_zero_fix ⟨120, by decide⟩ ⟨116, by decide⟩ p hp j hj hq fz1_120_116 fz2_120_116
  · exact match_zero_fix ⟨121, by decide⟩ ⟨116, by decide⟩ p hp j hj hq fz1_121_116 fz2_121_116
  · exact match_zero_fix ⟨122, by decide⟩ ⟨116, by decide⟩ p hp j hj hq fz1_122_116 fz2_122_116
  · exact match_zero_fix ⟨123, by decide⟩ ⟨116, by decide⟩ p hp j hj hq fz1_123_116 fz2_123_116
  · exact match_zero_fix ⟨124, by decide⟩ ⟨116, by decide⟩ p hp j hj hq fz1_124_116 fz2_124_116
  · exact match_zero_fix ⟨125, by decide⟩ ⟨116, by decide⟩ p hp j hj hq fz1_125_116 fz2_125_116
  · exact match_zero_fix ⟨126, by decide⟩ ⟨116, by decide⟩ p hp j hj hq fz1_126_116 fz2_126_116
  · exact match_zero_fix ⟨127, by decide⟩ ⟨116, by decide⟩ p hp j hj hq fz1_127_116 fz2_127_116
  · exact match_zero_fix ⟨128, by decide⟩ ⟨116, by decide⟩ p hp j hj hq fz1_128_116 fz2_128_116
  · exact match_zero_fix ⟨129, by decide⟩ ⟨116, by decide⟩ p hp j hj hq fz1_129_116 fz2_129_116
  · exact match_zero_fix ⟨130, by decide⟩ ⟨116, by decide⟩ p hp j hj hq fz1_130_116 fz2_130_116
  · exact match_zero_fix ⟨131, by decide⟩ ⟨116, by decide⟩ p hp j hj hq fz1_131_116 fz2_131_116
  · exact match_zero_fix ⟨132, by decide⟩ ⟨116, by decide⟩ p hp j hj hq fz1_132_116 fz2_132_116
  · exact match_zero_fix ⟨133, by decide⟩ ⟨116, by decide⟩ p hp j hj hq fz1_133_116 fz2_133_116
  · exact match_zero_fix ⟨134, by decide⟩ ⟨116, by decide⟩ p hp j hj hq fz1_134_116 fz2_134_116
  · exact match_zero_fix ⟨135, by decide⟩ ⟨116, by decide⟩ p hp j hj hq fz1_135_116 fz2_135_116
  · exact match_zero_fix ⟨136, by decide⟩ ⟨116, by decide⟩ p hp j hj hq fz1_136_116 fz2_136_116
  · exact match_zero_fix ⟨137, by decide⟩ ⟨116, by decide⟩ p hp j hj hq fz1_137_116 fz2_137_116
  · exact match_zero_fix ⟨138, by decide⟩ ⟨116, by decide⟩ p hp j hj hq fz1_138_116 fz2_138_116
  · exact match_zero_fix ⟨139, by decide⟩ ⟨116, by decide⟩ p hp j hj hq fz1_139_116 fz2_139_116
  · exact match_zero_fix ⟨140, by decide⟩ ⟨116, by decide⟩ p hp j hj hq fz1_140_116 fz2_140_116
  · exact match_zero_fix ⟨141, by decide⟩ ⟨116, by decide⟩ p hp j hj hq fz1_141_116 fz2_141_116
  · exact match_zero_fix ⟨142, by decide⟩ ⟨116, by decide⟩ p hp j hj hq fz1_142_116 fz2_142_116
  · exact match_zero_fix ⟨143, by decide⟩ ⟨116, by decide⟩ p hp j hj hq fz1_143_116 fz2_143_116
  · exact match_zero_fix ⟨144, by decide⟩ ⟨116, by decide⟩ p hp j hj hq fz1_144_116 fz2_144_116
  · exact match_zero_fix ⟨145, by decide⟩ ⟨116, by decide⟩ p hp j hj hq fz1_145_116 fz2_145_116
  · exact match_zero_fix ⟨146, by decide⟩ ⟨116, by decide⟩ p hp j hj hq fz1_146_116 fz2_146_116
  · exact pair_147_116 p hp hrep j hj hq

theorem master_117 (p : Nat) (hp : p < (Q2.transData.getD 117 []).length)
    (hrep : (Q2.cosetIsRep.getD 117 []).getD p false = true)
    (rK : Fin 148) (j : Nat) (hj : j < (repChars.getD rK.val []).length)
    (hq : (normIsRep.getD rK.val []).getD j false = true) :
    species (Q2.reps (⟨117, by decide⟩ : Fin 148)) (colE2 ⟨117, by decide⟩ p hp)
        (rowE2 rK j hj hq)
      = species (reps (⟨117, by decide⟩ : Fin 148))
        (colE1 ⟨117, by decide⟩ p (transLenTr ⟨117, by decide⟩ p hp)) (rowE1 rK j hj) := by
  rcases rK with ⟨nK, hnK⟩; interval_cases nK
  · exact match_zero_len ⟨0, by decide⟩ ⟨117, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨1, by decide⟩ ⟨117, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨2, by decide⟩ ⟨117, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨3, by decide⟩ ⟨117, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨4, by decide⟩ ⟨117, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨5, by decide⟩ ⟨117, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨6, by decide⟩ ⟨117, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨7, by decide⟩ ⟨117, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨8, by decide⟩ ⟨117, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨9, by decide⟩ ⟨117, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨10, by decide⟩ ⟨117, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨11, by decide⟩ ⟨117, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨12, by decide⟩ ⟨117, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨13, by decide⟩ ⟨117, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨14, by decide⟩ ⟨117, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨15, by decide⟩ ⟨117, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨16, by decide⟩ ⟨117, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨17, by decide⟩ ⟨117, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨18, by decide⟩ ⟨117, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨19, by decide⟩ ⟨117, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨20, by decide⟩ ⟨117, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨21, by decide⟩ ⟨117, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨22, by decide⟩ ⟨117, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨23, by decide⟩ ⟨117, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨24, by decide⟩ ⟨117, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨25, by decide⟩ ⟨117, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨26, by decide⟩ ⟨117, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨27, by decide⟩ ⟨117, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨28, by decide⟩ ⟨117, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨29, by decide⟩ ⟨117, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨30, by decide⟩ ⟨117, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨31, by decide⟩ ⟨117, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨32, by decide⟩ ⟨117, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨33, by decide⟩ ⟨117, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨34, by decide⟩ ⟨117, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨35, by decide⟩ ⟨117, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨36, by decide⟩ ⟨117, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨37, by decide⟩ ⟨117, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨38, by decide⟩ ⟨117, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨39, by decide⟩ ⟨117, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨40, by decide⟩ ⟨117, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨41, by decide⟩ ⟨117, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨42, by decide⟩ ⟨117, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨43, by decide⟩ ⟨117, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨44, by decide⟩ ⟨117, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨45, by decide⟩ ⟨117, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨46, by decide⟩ ⟨117, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨47, by decide⟩ ⟨117, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨48, by decide⟩ ⟨117, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨49, by decide⟩ ⟨117, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨50, by decide⟩ ⟨117, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨51, by decide⟩ ⟨117, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨52, by decide⟩ ⟨117, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨53, by decide⟩ ⟨117, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨54, by decide⟩ ⟨117, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨55, by decide⟩ ⟨117, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨56, by decide⟩ ⟨117, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨57, by decide⟩ ⟨117, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨58, by decide⟩ ⟨117, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨59, by decide⟩ ⟨117, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨60, by decide⟩ ⟨117, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨61, by decide⟩ ⟨117, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨62, by decide⟩ ⟨117, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨63, by decide⟩ ⟨117, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨64, by decide⟩ ⟨117, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨65, by decide⟩ ⟨117, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨66, by decide⟩ ⟨117, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨67, by decide⟩ ⟨117, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨68, by decide⟩ ⟨117, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨69, by decide⟩ ⟨117, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨70, by decide⟩ ⟨117, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨71, by decide⟩ ⟨117, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨72, by decide⟩ ⟨117, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨73, by decide⟩ ⟨117, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨74, by decide⟩ ⟨117, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨75, by decide⟩ ⟨117, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨76, by decide⟩ ⟨117, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨77, by decide⟩ ⟨117, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨78, by decide⟩ ⟨117, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨79, by decide⟩ ⟨117, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨80, by decide⟩ ⟨117, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨81, by decide⟩ ⟨117, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨82, by decide⟩ ⟨117, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨83, by decide⟩ ⟨117, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨84, by decide⟩ ⟨117, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨85, by decide⟩ ⟨117, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨86, by decide⟩ ⟨117, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨87, by decide⟩ ⟨117, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨88, by decide⟩ ⟨117, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨89, by decide⟩ ⟨117, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨90, by decide⟩ ⟨117, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨91, by decide⟩ ⟨117, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨92, by decide⟩ ⟨117, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨93, by decide⟩ ⟨117, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨94, by decide⟩ ⟨117, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨95, by decide⟩ ⟨117, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨96, by decide⟩ ⟨117, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨97, by decide⟩ ⟨117, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨98, by decide⟩ ⟨117, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨99, by decide⟩ ⟨117, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨100, by decide⟩ ⟨117, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨101, by decide⟩ ⟨117, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨102, by decide⟩ ⟨117, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨103, by decide⟩ ⟨117, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨104, by decide⟩ ⟨117, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨105, by decide⟩ ⟨117, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨106, by decide⟩ ⟨117, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨107, by decide⟩ ⟨117, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨108, by decide⟩ ⟨117, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨109, by decide⟩ ⟨117, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨110, by decide⟩ ⟨117, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨111, by decide⟩ ⟨117, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨112, by decide⟩ ⟨117, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨113, by decide⟩ ⟨117, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨114, by decide⟩ ⟨117, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨115, by decide⟩ ⟨117, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_fix ⟨116, by decide⟩ ⟨117, by decide⟩ p hp j hj hq fz1_116_117 fz2_116_117
  · exact pair_117_117 p hp hrep j hj hq
  · exact match_zero_fix ⟨118, by decide⟩ ⟨117, by decide⟩ p hp j hj hq fz1_118_117 fz2_118_117
  · exact match_zero_fix ⟨119, by decide⟩ ⟨117, by decide⟩ p hp j hj hq fz1_119_117 fz2_119_117
  · exact match_zero_fix ⟨120, by decide⟩ ⟨117, by decide⟩ p hp j hj hq fz1_120_117 fz2_120_117
  · exact match_zero_fix ⟨121, by decide⟩ ⟨117, by decide⟩ p hp j hj hq fz1_121_117 fz2_121_117
  · exact match_zero_fix ⟨122, by decide⟩ ⟨117, by decide⟩ p hp j hj hq fz1_122_117 fz2_122_117
  · exact match_zero_fix ⟨123, by decide⟩ ⟨117, by decide⟩ p hp j hj hq fz1_123_117 fz2_123_117
  · exact match_zero_fix ⟨124, by decide⟩ ⟨117, by decide⟩ p hp j hj hq fz1_124_117 fz2_124_117
  · exact match_zero_fix ⟨125, by decide⟩ ⟨117, by decide⟩ p hp j hj hq fz1_125_117 fz2_125_117
  · exact match_zero_fix ⟨126, by decide⟩ ⟨117, by decide⟩ p hp j hj hq fz1_126_117 fz2_126_117
  · exact match_zero_fix ⟨127, by decide⟩ ⟨117, by decide⟩ p hp j hj hq fz1_127_117 fz2_127_117
  · exact match_zero_fix ⟨128, by decide⟩ ⟨117, by decide⟩ p hp j hj hq fz1_128_117 fz2_128_117
  · exact match_zero_fix ⟨129, by decide⟩ ⟨117, by decide⟩ p hp j hj hq fz1_129_117 fz2_129_117
  · exact match_zero_fix ⟨130, by decide⟩ ⟨117, by decide⟩ p hp j hj hq fz1_130_117 fz2_130_117
  · exact match_zero_fix ⟨131, by decide⟩ ⟨117, by decide⟩ p hp j hj hq fz1_131_117 fz2_131_117
  · exact match_zero_fix ⟨132, by decide⟩ ⟨117, by decide⟩ p hp j hj hq fz1_132_117 fz2_132_117
  · exact match_zero_fix ⟨133, by decide⟩ ⟨117, by decide⟩ p hp j hj hq fz1_133_117 fz2_133_117
  · exact match_zero_fix ⟨134, by decide⟩ ⟨117, by decide⟩ p hp j hj hq fz1_134_117 fz2_134_117
  · exact match_zero_fix ⟨135, by decide⟩ ⟨117, by decide⟩ p hp j hj hq fz1_135_117 fz2_135_117
  · exact match_zero_fix ⟨136, by decide⟩ ⟨117, by decide⟩ p hp j hj hq fz1_136_117 fz2_136_117
  · exact match_zero_fix ⟨137, by decide⟩ ⟨117, by decide⟩ p hp j hj hq fz1_137_117 fz2_137_117
  · exact match_zero_fix ⟨138, by decide⟩ ⟨117, by decide⟩ p hp j hj hq fz1_138_117 fz2_138_117
  · exact match_zero_fix ⟨139, by decide⟩ ⟨117, by decide⟩ p hp j hj hq fz1_139_117 fz2_139_117
  · exact match_zero_fix ⟨140, by decide⟩ ⟨117, by decide⟩ p hp j hj hq fz1_140_117 fz2_140_117
  · exact match_zero_fix ⟨141, by decide⟩ ⟨117, by decide⟩ p hp j hj hq fz1_141_117 fz2_141_117
  · exact match_zero_fix ⟨142, by decide⟩ ⟨117, by decide⟩ p hp j hj hq fz1_142_117 fz2_142_117
  · exact match_zero_fix ⟨143, by decide⟩ ⟨117, by decide⟩ p hp j hj hq fz1_143_117 fz2_143_117
  · exact match_zero_fix ⟨144, by decide⟩ ⟨117, by decide⟩ p hp j hj hq fz1_144_117 fz2_144_117
  · exact match_zero_fix ⟨145, by decide⟩ ⟨117, by decide⟩ p hp j hj hq fz1_145_117 fz2_145_117
  · exact match_zero_fix ⟨146, by decide⟩ ⟨117, by decide⟩ p hp j hj hq fz1_146_117 fz2_146_117
  · exact pair_147_117 p hp hrep j hj hq

theorem master_118 (p : Nat) (hp : p < (Q2.transData.getD 118 []).length)
    (hrep : (Q2.cosetIsRep.getD 118 []).getD p false = true)
    (rK : Fin 148) (j : Nat) (hj : j < (repChars.getD rK.val []).length)
    (hq : (normIsRep.getD rK.val []).getD j false = true) :
    species (Q2.reps (⟨118, by decide⟩ : Fin 148)) (colE2 ⟨118, by decide⟩ p hp)
        (rowE2 rK j hj hq)
      = species (reps (⟨118, by decide⟩ : Fin 148))
        (colE1 ⟨118, by decide⟩ p (transLenTr ⟨118, by decide⟩ p hp)) (rowE1 rK j hj) := by
  rcases rK with ⟨nK, hnK⟩; interval_cases nK
  · exact match_zero_len ⟨0, by decide⟩ ⟨118, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨1, by decide⟩ ⟨118, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨2, by decide⟩ ⟨118, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨3, by decide⟩ ⟨118, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨4, by decide⟩ ⟨118, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨5, by decide⟩ ⟨118, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨6, by decide⟩ ⟨118, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨7, by decide⟩ ⟨118, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨8, by decide⟩ ⟨118, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨9, by decide⟩ ⟨118, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨10, by decide⟩ ⟨118, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨11, by decide⟩ ⟨118, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨12, by decide⟩ ⟨118, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨13, by decide⟩ ⟨118, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨14, by decide⟩ ⟨118, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨15, by decide⟩ ⟨118, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨16, by decide⟩ ⟨118, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨17, by decide⟩ ⟨118, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨18, by decide⟩ ⟨118, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨19, by decide⟩ ⟨118, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨20, by decide⟩ ⟨118, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨21, by decide⟩ ⟨118, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨22, by decide⟩ ⟨118, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨23, by decide⟩ ⟨118, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨24, by decide⟩ ⟨118, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨25, by decide⟩ ⟨118, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨26, by decide⟩ ⟨118, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨27, by decide⟩ ⟨118, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨28, by decide⟩ ⟨118, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨29, by decide⟩ ⟨118, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨30, by decide⟩ ⟨118, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨31, by decide⟩ ⟨118, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨32, by decide⟩ ⟨118, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨33, by decide⟩ ⟨118, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨34, by decide⟩ ⟨118, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨35, by decide⟩ ⟨118, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨36, by decide⟩ ⟨118, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨37, by decide⟩ ⟨118, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨38, by decide⟩ ⟨118, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨39, by decide⟩ ⟨118, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨40, by decide⟩ ⟨118, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨41, by decide⟩ ⟨118, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨42, by decide⟩ ⟨118, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨43, by decide⟩ ⟨118, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨44, by decide⟩ ⟨118, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨45, by decide⟩ ⟨118, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨46, by decide⟩ ⟨118, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨47, by decide⟩ ⟨118, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨48, by decide⟩ ⟨118, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨49, by decide⟩ ⟨118, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨50, by decide⟩ ⟨118, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨51, by decide⟩ ⟨118, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨52, by decide⟩ ⟨118, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨53, by decide⟩ ⟨118, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨54, by decide⟩ ⟨118, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨55, by decide⟩ ⟨118, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨56, by decide⟩ ⟨118, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨57, by decide⟩ ⟨118, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨58, by decide⟩ ⟨118, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨59, by decide⟩ ⟨118, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨60, by decide⟩ ⟨118, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨61, by decide⟩ ⟨118, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨62, by decide⟩ ⟨118, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨63, by decide⟩ ⟨118, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨64, by decide⟩ ⟨118, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨65, by decide⟩ ⟨118, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨66, by decide⟩ ⟨118, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨67, by decide⟩ ⟨118, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨68, by decide⟩ ⟨118, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨69, by decide⟩ ⟨118, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨70, by decide⟩ ⟨118, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨71, by decide⟩ ⟨118, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨72, by decide⟩ ⟨118, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨73, by decide⟩ ⟨118, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨74, by decide⟩ ⟨118, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨75, by decide⟩ ⟨118, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨76, by decide⟩ ⟨118, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨77, by decide⟩ ⟨118, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨78, by decide⟩ ⟨118, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨79, by decide⟩ ⟨118, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨80, by decide⟩ ⟨118, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨81, by decide⟩ ⟨118, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨82, by decide⟩ ⟨118, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨83, by decide⟩ ⟨118, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨84, by decide⟩ ⟨118, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨85, by decide⟩ ⟨118, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨86, by decide⟩ ⟨118, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨87, by decide⟩ ⟨118, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨88, by decide⟩ ⟨118, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨89, by decide⟩ ⟨118, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨90, by decide⟩ ⟨118, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨91, by decide⟩ ⟨118, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨92, by decide⟩ ⟨118, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨93, by decide⟩ ⟨118, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨94, by decide⟩ ⟨118, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨95, by decide⟩ ⟨118, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨96, by decide⟩ ⟨118, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨97, by decide⟩ ⟨118, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨98, by decide⟩ ⟨118, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨99, by decide⟩ ⟨118, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨100, by decide⟩ ⟨118, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨101, by decide⟩ ⟨118, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨102, by decide⟩ ⟨118, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨103, by decide⟩ ⟨118, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨104, by decide⟩ ⟨118, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨105, by decide⟩ ⟨118, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨106, by decide⟩ ⟨118, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨107, by decide⟩ ⟨118, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨108, by decide⟩ ⟨118, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨109, by decide⟩ ⟨118, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨110, by decide⟩ ⟨118, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨111, by decide⟩ ⟨118, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨112, by decide⟩ ⟨118, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨113, by decide⟩ ⟨118, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨114, by decide⟩ ⟨118, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨115, by decide⟩ ⟨118, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_fix ⟨116, by decide⟩ ⟨118, by decide⟩ p hp j hj hq fz1_116_118 fz2_116_118
  · exact match_zero_fix ⟨117, by decide⟩ ⟨118, by decide⟩ p hp j hj hq fz1_117_118 fz2_117_118
  · exact pair_118_118 p hp hrep j hj hq
  · exact match_zero_fix ⟨119, by decide⟩ ⟨118, by decide⟩ p hp j hj hq fz1_119_118 fz2_119_118
  · exact match_zero_fix ⟨120, by decide⟩ ⟨118, by decide⟩ p hp j hj hq fz1_120_118 fz2_120_118
  · exact match_zero_fix ⟨121, by decide⟩ ⟨118, by decide⟩ p hp j hj hq fz1_121_118 fz2_121_118
  · exact match_zero_fix ⟨122, by decide⟩ ⟨118, by decide⟩ p hp j hj hq fz1_122_118 fz2_122_118
  · exact match_zero_fix ⟨123, by decide⟩ ⟨118, by decide⟩ p hp j hj hq fz1_123_118 fz2_123_118
  · exact match_zero_fix ⟨124, by decide⟩ ⟨118, by decide⟩ p hp j hj hq fz1_124_118 fz2_124_118
  · exact match_zero_fix ⟨125, by decide⟩ ⟨118, by decide⟩ p hp j hj hq fz1_125_118 fz2_125_118
  · exact match_zero_fix ⟨126, by decide⟩ ⟨118, by decide⟩ p hp j hj hq fz1_126_118 fz2_126_118
  · exact match_zero_fix ⟨127, by decide⟩ ⟨118, by decide⟩ p hp j hj hq fz1_127_118 fz2_127_118
  · exact match_zero_fix ⟨128, by decide⟩ ⟨118, by decide⟩ p hp j hj hq fz1_128_118 fz2_128_118
  · exact match_zero_fix ⟨129, by decide⟩ ⟨118, by decide⟩ p hp j hj hq fz1_129_118 fz2_129_118
  · exact match_zero_fix ⟨130, by decide⟩ ⟨118, by decide⟩ p hp j hj hq fz1_130_118 fz2_130_118
  · exact match_zero_fix ⟨131, by decide⟩ ⟨118, by decide⟩ p hp j hj hq fz1_131_118 fz2_131_118
  · exact match_zero_fix ⟨132, by decide⟩ ⟨118, by decide⟩ p hp j hj hq fz1_132_118 fz2_132_118
  · exact match_zero_fix ⟨133, by decide⟩ ⟨118, by decide⟩ p hp j hj hq fz1_133_118 fz2_133_118
  · exact match_zero_fix ⟨134, by decide⟩ ⟨118, by decide⟩ p hp j hj hq fz1_134_118 fz2_134_118
  · exact match_zero_fix ⟨135, by decide⟩ ⟨118, by decide⟩ p hp j hj hq fz1_135_118 fz2_135_118
  · exact match_zero_fix ⟨136, by decide⟩ ⟨118, by decide⟩ p hp j hj hq fz1_136_118 fz2_136_118
  · exact match_zero_fix ⟨137, by decide⟩ ⟨118, by decide⟩ p hp j hj hq fz1_137_118 fz2_137_118
  · exact match_zero_fix ⟨138, by decide⟩ ⟨118, by decide⟩ p hp j hj hq fz1_138_118 fz2_138_118
  · exact match_zero_fix ⟨139, by decide⟩ ⟨118, by decide⟩ p hp j hj hq fz1_139_118 fz2_139_118
  · exact match_zero_fix ⟨140, by decide⟩ ⟨118, by decide⟩ p hp j hj hq fz1_140_118 fz2_140_118
  · exact match_zero_fix ⟨141, by decide⟩ ⟨118, by decide⟩ p hp j hj hq fz1_141_118 fz2_141_118
  · exact match_zero_fix ⟨142, by decide⟩ ⟨118, by decide⟩ p hp j hj hq fz1_142_118 fz2_142_118
  · exact match_zero_fix ⟨143, by decide⟩ ⟨118, by decide⟩ p hp j hj hq fz1_143_118 fz2_143_118
  · exact match_zero_fix ⟨144, by decide⟩ ⟨118, by decide⟩ p hp j hj hq fz1_144_118 fz2_144_118
  · exact match_zero_fix ⟨145, by decide⟩ ⟨118, by decide⟩ p hp j hj hq fz1_145_118 fz2_145_118
  · exact match_zero_fix ⟨146, by decide⟩ ⟨118, by decide⟩ p hp j hj hq fz1_146_118 fz2_146_118
  · exact pair_147_118 p hp hrep j hj hq

theorem master_119 (p : Nat) (hp : p < (Q2.transData.getD 119 []).length)
    (hrep : (Q2.cosetIsRep.getD 119 []).getD p false = true)
    (rK : Fin 148) (j : Nat) (hj : j < (repChars.getD rK.val []).length)
    (hq : (normIsRep.getD rK.val []).getD j false = true) :
    species (Q2.reps (⟨119, by decide⟩ : Fin 148)) (colE2 ⟨119, by decide⟩ p hp)
        (rowE2 rK j hj hq)
      = species (reps (⟨119, by decide⟩ : Fin 148))
        (colE1 ⟨119, by decide⟩ p (transLenTr ⟨119, by decide⟩ p hp)) (rowE1 rK j hj) := by
  rcases rK with ⟨nK, hnK⟩; interval_cases nK
  · exact match_zero_len ⟨0, by decide⟩ ⟨119, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨1, by decide⟩ ⟨119, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨2, by decide⟩ ⟨119, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨3, by decide⟩ ⟨119, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨4, by decide⟩ ⟨119, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨5, by decide⟩ ⟨119, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨6, by decide⟩ ⟨119, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨7, by decide⟩ ⟨119, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨8, by decide⟩ ⟨119, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨9, by decide⟩ ⟨119, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨10, by decide⟩ ⟨119, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨11, by decide⟩ ⟨119, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨12, by decide⟩ ⟨119, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨13, by decide⟩ ⟨119, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨14, by decide⟩ ⟨119, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨15, by decide⟩ ⟨119, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨16, by decide⟩ ⟨119, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨17, by decide⟩ ⟨119, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨18, by decide⟩ ⟨119, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨19, by decide⟩ ⟨119, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨20, by decide⟩ ⟨119, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨21, by decide⟩ ⟨119, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨22, by decide⟩ ⟨119, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨23, by decide⟩ ⟨119, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨24, by decide⟩ ⟨119, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨25, by decide⟩ ⟨119, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨26, by decide⟩ ⟨119, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨27, by decide⟩ ⟨119, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨28, by decide⟩ ⟨119, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨29, by decide⟩ ⟨119, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨30, by decide⟩ ⟨119, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨31, by decide⟩ ⟨119, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨32, by decide⟩ ⟨119, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨33, by decide⟩ ⟨119, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨34, by decide⟩ ⟨119, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨35, by decide⟩ ⟨119, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨36, by decide⟩ ⟨119, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨37, by decide⟩ ⟨119, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨38, by decide⟩ ⟨119, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨39, by decide⟩ ⟨119, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨40, by decide⟩ ⟨119, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨41, by decide⟩ ⟨119, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨42, by decide⟩ ⟨119, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨43, by decide⟩ ⟨119, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨44, by decide⟩ ⟨119, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨45, by decide⟩ ⟨119, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨46, by decide⟩ ⟨119, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨47, by decide⟩ ⟨119, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨48, by decide⟩ ⟨119, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨49, by decide⟩ ⟨119, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨50, by decide⟩ ⟨119, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨51, by decide⟩ ⟨119, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨52, by decide⟩ ⟨119, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨53, by decide⟩ ⟨119, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨54, by decide⟩ ⟨119, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨55, by decide⟩ ⟨119, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨56, by decide⟩ ⟨119, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨57, by decide⟩ ⟨119, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨58, by decide⟩ ⟨119, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨59, by decide⟩ ⟨119, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨60, by decide⟩ ⟨119, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨61, by decide⟩ ⟨119, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨62, by decide⟩ ⟨119, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨63, by decide⟩ ⟨119, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨64, by decide⟩ ⟨119, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨65, by decide⟩ ⟨119, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨66, by decide⟩ ⟨119, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨67, by decide⟩ ⟨119, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨68, by decide⟩ ⟨119, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨69, by decide⟩ ⟨119, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨70, by decide⟩ ⟨119, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨71, by decide⟩ ⟨119, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨72, by decide⟩ ⟨119, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨73, by decide⟩ ⟨119, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨74, by decide⟩ ⟨119, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨75, by decide⟩ ⟨119, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨76, by decide⟩ ⟨119, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨77, by decide⟩ ⟨119, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨78, by decide⟩ ⟨119, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨79, by decide⟩ ⟨119, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨80, by decide⟩ ⟨119, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨81, by decide⟩ ⟨119, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨82, by decide⟩ ⟨119, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨83, by decide⟩ ⟨119, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨84, by decide⟩ ⟨119, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨85, by decide⟩ ⟨119, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨86, by decide⟩ ⟨119, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨87, by decide⟩ ⟨119, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨88, by decide⟩ ⟨119, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨89, by decide⟩ ⟨119, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨90, by decide⟩ ⟨119, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨91, by decide⟩ ⟨119, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨92, by decide⟩ ⟨119, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨93, by decide⟩ ⟨119, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨94, by decide⟩ ⟨119, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨95, by decide⟩ ⟨119, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨96, by decide⟩ ⟨119, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨97, by decide⟩ ⟨119, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨98, by decide⟩ ⟨119, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨99, by decide⟩ ⟨119, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨100, by decide⟩ ⟨119, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨101, by decide⟩ ⟨119, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨102, by decide⟩ ⟨119, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨103, by decide⟩ ⟨119, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨104, by decide⟩ ⟨119, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨105, by decide⟩ ⟨119, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨106, by decide⟩ ⟨119, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨107, by decide⟩ ⟨119, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨108, by decide⟩ ⟨119, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨109, by decide⟩ ⟨119, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨110, by decide⟩ ⟨119, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨111, by decide⟩ ⟨119, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨112, by decide⟩ ⟨119, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨113, by decide⟩ ⟨119, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨114, by decide⟩ ⟨119, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨115, by decide⟩ ⟨119, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_fix ⟨116, by decide⟩ ⟨119, by decide⟩ p hp j hj hq fz1_116_119 fz2_116_119
  · exact match_zero_fix ⟨117, by decide⟩ ⟨119, by decide⟩ p hp j hj hq fz1_117_119 fz2_117_119
  · exact match_zero_fix ⟨118, by decide⟩ ⟨119, by decide⟩ p hp j hj hq fz1_118_119 fz2_118_119
  · exact pair_119_119 p hp hrep j hj hq
  · exact match_zero_fix ⟨120, by decide⟩ ⟨119, by decide⟩ p hp j hj hq fz1_120_119 fz2_120_119
  · exact match_zero_fix ⟨121, by decide⟩ ⟨119, by decide⟩ p hp j hj hq fz1_121_119 fz2_121_119
  · exact match_zero_fix ⟨122, by decide⟩ ⟨119, by decide⟩ p hp j hj hq fz1_122_119 fz2_122_119
  · exact match_zero_fix ⟨123, by decide⟩ ⟨119, by decide⟩ p hp j hj hq fz1_123_119 fz2_123_119
  · exact match_zero_fix ⟨124, by decide⟩ ⟨119, by decide⟩ p hp j hj hq fz1_124_119 fz2_124_119
  · exact match_zero_fix ⟨125, by decide⟩ ⟨119, by decide⟩ p hp j hj hq fz1_125_119 fz2_125_119
  · exact match_zero_fix ⟨126, by decide⟩ ⟨119, by decide⟩ p hp j hj hq fz1_126_119 fz2_126_119
  · exact match_zero_fix ⟨127, by decide⟩ ⟨119, by decide⟩ p hp j hj hq fz1_127_119 fz2_127_119
  · exact match_zero_fix ⟨128, by decide⟩ ⟨119, by decide⟩ p hp j hj hq fz1_128_119 fz2_128_119
  · exact match_zero_fix ⟨129, by decide⟩ ⟨119, by decide⟩ p hp j hj hq fz1_129_119 fz2_129_119
  · exact match_zero_fix ⟨130, by decide⟩ ⟨119, by decide⟩ p hp j hj hq fz1_130_119 fz2_130_119
  · exact match_zero_fix ⟨131, by decide⟩ ⟨119, by decide⟩ p hp j hj hq fz1_131_119 fz2_131_119
  · exact match_zero_fix ⟨132, by decide⟩ ⟨119, by decide⟩ p hp j hj hq fz1_132_119 fz2_132_119
  · exact match_zero_fix ⟨133, by decide⟩ ⟨119, by decide⟩ p hp j hj hq fz1_133_119 fz2_133_119
  · exact match_zero_fix ⟨134, by decide⟩ ⟨119, by decide⟩ p hp j hj hq fz1_134_119 fz2_134_119
  · exact match_zero_fix ⟨135, by decide⟩ ⟨119, by decide⟩ p hp j hj hq fz1_135_119 fz2_135_119
  · exact match_zero_fix ⟨136, by decide⟩ ⟨119, by decide⟩ p hp j hj hq fz1_136_119 fz2_136_119
  · exact match_zero_fix ⟨137, by decide⟩ ⟨119, by decide⟩ p hp j hj hq fz1_137_119 fz2_137_119
  · exact match_zero_fix ⟨138, by decide⟩ ⟨119, by decide⟩ p hp j hj hq fz1_138_119 fz2_138_119
  · exact match_zero_fix ⟨139, by decide⟩ ⟨119, by decide⟩ p hp j hj hq fz1_139_119 fz2_139_119
  · exact match_zero_fix ⟨140, by decide⟩ ⟨119, by decide⟩ p hp j hj hq fz1_140_119 fz2_140_119
  · exact match_zero_fix ⟨141, by decide⟩ ⟨119, by decide⟩ p hp j hj hq fz1_141_119 fz2_141_119
  · exact match_zero_fix ⟨142, by decide⟩ ⟨119, by decide⟩ p hp j hj hq fz1_142_119 fz2_142_119
  · exact match_zero_fix ⟨143, by decide⟩ ⟨119, by decide⟩ p hp j hj hq fz1_143_119 fz2_143_119
  · exact match_zero_fix ⟨144, by decide⟩ ⟨119, by decide⟩ p hp j hj hq fz1_144_119 fz2_144_119
  · exact match_zero_fix ⟨145, by decide⟩ ⟨119, by decide⟩ p hp j hj hq fz1_145_119 fz2_145_119
  · exact match_zero_fix ⟨146, by decide⟩ ⟨119, by decide⟩ p hp j hj hq fz1_146_119 fz2_146_119
  · exact pair_147_119 p hp hrep j hj hq

end LeanDring.P5Presentation
