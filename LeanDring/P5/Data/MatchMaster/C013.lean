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
import LeanDring.P5.Data.MatchPair.C012
import LeanDring.P5.Data.MatchPair.C005
import LeanDring.P5.Data.MatchPair.C006
import LeanDring.P5.Data.MatchPair.C007
import LeanDring.P5.Data.MatchPair.C008
import LeanDring.P5.Data.MatchPair.C009
import LeanDring.P5.Data.MatchPair.C010

/-! # Stage-5 per-column-class master theorems, chunk 12 (auto-emitted).  -/

namespace LeanDring.P5Presentation

open MulAction Finset LeanDring.DRing LeanDring.MonGSet

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.style.longLine false

theorem master_96 (p : Nat) (hp : p < (Q2.transData.getD 96 []).length)
    (hrep : (Q2.cosetIsRep.getD 96 []).getD p false = true)
    (rK : Fin 148) (j : Nat) (hj : j < (repChars.getD rK.val []).length)
    (hq : (normIsRep.getD rK.val []).getD j false = true) :
    species (Q2.reps (⟨96, by decide⟩ : Fin 148)) (colE2 ⟨96, by decide⟩ p hp)
        (rowE2 rK j hj hq)
      = species (reps (⟨96, by decide⟩ : Fin 148))
        (colE1 ⟨96, by decide⟩ p (transLenTr ⟨96, by decide⟩ p hp)) (rowE1 rK j hj) := by
  rcases rK with ⟨nK, hnK⟩; interval_cases nK
  · exact match_zero_len ⟨0, by decide⟩ ⟨96, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨1, by decide⟩ ⟨96, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨2, by decide⟩ ⟨96, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨3, by decide⟩ ⟨96, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨4, by decide⟩ ⟨96, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨5, by decide⟩ ⟨96, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨6, by decide⟩ ⟨96, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨7, by decide⟩ ⟨96, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨8, by decide⟩ ⟨96, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨9, by decide⟩ ⟨96, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨10, by decide⟩ ⟨96, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨11, by decide⟩ ⟨96, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨12, by decide⟩ ⟨96, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨13, by decide⟩ ⟨96, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨14, by decide⟩ ⟨96, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨15, by decide⟩ ⟨96, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨16, by decide⟩ ⟨96, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨17, by decide⟩ ⟨96, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨18, by decide⟩ ⟨96, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨19, by decide⟩ ⟨96, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨20, by decide⟩ ⟨96, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨21, by decide⟩ ⟨96, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨22, by decide⟩ ⟨96, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨23, by decide⟩ ⟨96, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨24, by decide⟩ ⟨96, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨25, by decide⟩ ⟨96, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨26, by decide⟩ ⟨96, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨27, by decide⟩ ⟨96, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨28, by decide⟩ ⟨96, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨29, by decide⟩ ⟨96, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨30, by decide⟩ ⟨96, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨31, by decide⟩ ⟨96, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨32, by decide⟩ ⟨96, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨33, by decide⟩ ⟨96, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨34, by decide⟩ ⟨96, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨35, by decide⟩ ⟨96, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨36, by decide⟩ ⟨96, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨37, by decide⟩ ⟨96, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨38, by decide⟩ ⟨96, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨39, by decide⟩ ⟨96, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨40, by decide⟩ ⟨96, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨41, by decide⟩ ⟨96, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨42, by decide⟩ ⟨96, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨43, by decide⟩ ⟨96, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨44, by decide⟩ ⟨96, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨45, by decide⟩ ⟨96, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨46, by decide⟩ ⟨96, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨47, by decide⟩ ⟨96, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨48, by decide⟩ ⟨96, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨49, by decide⟩ ⟨96, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨50, by decide⟩ ⟨96, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨51, by decide⟩ ⟨96, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨52, by decide⟩ ⟨96, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨53, by decide⟩ ⟨96, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨54, by decide⟩ ⟨96, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_fix ⟨55, by decide⟩ ⟨96, by decide⟩ p hp j hj hq fz1_55_96 fz2_55_96
  · exact match_zero_fix ⟨56, by decide⟩ ⟨96, by decide⟩ p hp j hj hq fz1_56_96 fz2_56_96
  · exact match_zero_fix ⟨57, by decide⟩ ⟨96, by decide⟩ p hp j hj hq fz1_57_96 fz2_57_96
  · exact match_zero_fix ⟨58, by decide⟩ ⟨96, by decide⟩ p hp j hj hq fz1_58_96 fz2_58_96
  · exact match_zero_fix ⟨59, by decide⟩ ⟨96, by decide⟩ p hp j hj hq fz1_59_96 fz2_59_96
  · exact match_zero_fix ⟨60, by decide⟩ ⟨96, by decide⟩ p hp j hj hq fz1_60_96 fz2_60_96
  · exact match_zero_fix ⟨61, by decide⟩ ⟨96, by decide⟩ p hp j hj hq fz1_61_96 fz2_61_96
  · exact match_zero_fix ⟨62, by decide⟩ ⟨96, by decide⟩ p hp j hj hq fz1_62_96 fz2_62_96
  · exact match_zero_fix ⟨63, by decide⟩ ⟨96, by decide⟩ p hp j hj hq fz1_63_96 fz2_63_96
  · exact match_zero_fix ⟨64, by decide⟩ ⟨96, by decide⟩ p hp j hj hq fz1_64_96 fz2_64_96
  · exact match_zero_fix ⟨65, by decide⟩ ⟨96, by decide⟩ p hp j hj hq fz1_65_96 fz2_65_96
  · exact match_zero_fix ⟨66, by decide⟩ ⟨96, by decide⟩ p hp j hj hq fz1_66_96 fz2_66_96
  · exact match_zero_fix ⟨67, by decide⟩ ⟨96, by decide⟩ p hp j hj hq fz1_67_96 fz2_67_96
  · exact match_zero_fix ⟨68, by decide⟩ ⟨96, by decide⟩ p hp j hj hq fz1_68_96 fz2_68_96
  · exact match_zero_fix ⟨69, by decide⟩ ⟨96, by decide⟩ p hp j hj hq fz1_69_96 fz2_69_96
  · exact match_zero_fix ⟨70, by decide⟩ ⟨96, by decide⟩ p hp j hj hq fz1_70_96 fz2_70_96
  · exact match_zero_fix ⟨71, by decide⟩ ⟨96, by decide⟩ p hp j hj hq fz1_71_96 fz2_71_96
  · exact match_zero_fix ⟨72, by decide⟩ ⟨96, by decide⟩ p hp j hj hq fz1_72_96 fz2_72_96
  · exact match_zero_fix ⟨73, by decide⟩ ⟨96, by decide⟩ p hp j hj hq fz1_73_96 fz2_73_96
  · exact match_zero_fix ⟨74, by decide⟩ ⟨96, by decide⟩ p hp j hj hq fz1_74_96 fz2_74_96
  · exact match_zero_fix ⟨75, by decide⟩ ⟨96, by decide⟩ p hp j hj hq fz1_75_96 fz2_75_96
  · exact match_zero_fix ⟨76, by decide⟩ ⟨96, by decide⟩ p hp j hj hq fz1_76_96 fz2_76_96
  · exact match_zero_fix ⟨77, by decide⟩ ⟨96, by decide⟩ p hp j hj hq fz1_77_96 fz2_77_96
  · exact match_zero_fix ⟨78, by decide⟩ ⟨96, by decide⟩ p hp j hj hq fz1_78_96 fz2_78_96
  · exact match_zero_fix ⟨79, by decide⟩ ⟨96, by decide⟩ p hp j hj hq fz1_79_96 fz2_79_96
  · exact match_zero_fix ⟨80, by decide⟩ ⟨96, by decide⟩ p hp j hj hq fz1_80_96 fz2_80_96
  · exact match_zero_fix ⟨81, by decide⟩ ⟨96, by decide⟩ p hp j hj hq fz1_81_96 fz2_81_96
  · exact match_zero_fix ⟨82, by decide⟩ ⟨96, by decide⟩ p hp j hj hq fz1_82_96 fz2_82_96
  · exact match_zero_fix ⟨83, by decide⟩ ⟨96, by decide⟩ p hp j hj hq fz1_83_96 fz2_83_96
  · exact match_zero_fix ⟨84, by decide⟩ ⟨96, by decide⟩ p hp j hj hq fz1_84_96 fz2_84_96
  · exact match_zero_fix ⟨85, by decide⟩ ⟨96, by decide⟩ p hp j hj hq fz1_85_96 fz2_85_96
  · exact match_zero_fix ⟨86, by decide⟩ ⟨96, by decide⟩ p hp j hj hq fz1_86_96 fz2_86_96
  · exact match_zero_fix ⟨87, by decide⟩ ⟨96, by decide⟩ p hp j hj hq fz1_87_96 fz2_87_96
  · exact match_zero_fix ⟨88, by decide⟩ ⟨96, by decide⟩ p hp j hj hq fz1_88_96 fz2_88_96
  · exact match_zero_fix ⟨89, by decide⟩ ⟨96, by decide⟩ p hp j hj hq fz1_89_96 fz2_89_96
  · exact match_zero_fix ⟨90, by decide⟩ ⟨96, by decide⟩ p hp j hj hq fz1_90_96 fz2_90_96
  · exact match_zero_fix ⟨91, by decide⟩ ⟨96, by decide⟩ p hp j hj hq fz1_91_96 fz2_91_96
  · exact match_zero_fix ⟨92, by decide⟩ ⟨96, by decide⟩ p hp j hj hq fz1_92_96 fz2_92_96
  · exact match_zero_fix ⟨93, by decide⟩ ⟨96, by decide⟩ p hp j hj hq fz1_93_96 fz2_93_96
  · exact match_zero_fix ⟨94, by decide⟩ ⟨96, by decide⟩ p hp j hj hq fz1_94_96 fz2_94_96
  · exact match_zero_fix ⟨95, by decide⟩ ⟨96, by decide⟩ p hp j hj hq fz1_95_96 fz2_95_96
  · exact pair_96_96 p hp hrep j hj hq
  · exact match_zero_fix ⟨97, by decide⟩ ⟨96, by decide⟩ p hp j hj hq fz1_97_96 fz2_97_96
  · exact match_zero_fix ⟨98, by decide⟩ ⟨96, by decide⟩ p hp j hj hq fz1_98_96 fz2_98_96
  · exact match_zero_fix ⟨99, by decide⟩ ⟨96, by decide⟩ p hp j hj hq fz1_99_96 fz2_99_96
  · exact match_zero_fix ⟨100, by decide⟩ ⟨96, by decide⟩ p hp j hj hq fz1_100_96 fz2_100_96
  · exact match_zero_fix ⟨101, by decide⟩ ⟨96, by decide⟩ p hp j hj hq fz1_101_96 fz2_101_96
  · exact match_zero_fix ⟨102, by decide⟩ ⟨96, by decide⟩ p hp j hj hq fz1_102_96 fz2_102_96
  · exact match_zero_fix ⟨103, by decide⟩ ⟨96, by decide⟩ p hp j hj hq fz1_103_96 fz2_103_96
  · exact match_zero_fix ⟨104, by decide⟩ ⟨96, by decide⟩ p hp j hj hq fz1_104_96 fz2_104_96
  · exact match_zero_fix ⟨105, by decide⟩ ⟨96, by decide⟩ p hp j hj hq fz1_105_96 fz2_105_96
  · exact match_zero_fix ⟨106, by decide⟩ ⟨96, by decide⟩ p hp j hj hq fz1_106_96 fz2_106_96
  · exact match_zero_fix ⟨107, by decide⟩ ⟨96, by decide⟩ p hp j hj hq fz1_107_96 fz2_107_96
  · exact match_zero_fix ⟨108, by decide⟩ ⟨96, by decide⟩ p hp j hj hq fz1_108_96 fz2_108_96
  · exact match_zero_fix ⟨109, by decide⟩ ⟨96, by decide⟩ p hp j hj hq fz1_109_96 fz2_109_96
  · exact match_zero_fix ⟨110, by decide⟩ ⟨96, by decide⟩ p hp j hj hq fz1_110_96 fz2_110_96
  · exact match_zero_fix ⟨111, by decide⟩ ⟨96, by decide⟩ p hp j hj hq fz1_111_96 fz2_111_96
  · exact match_zero_fix ⟨112, by decide⟩ ⟨96, by decide⟩ p hp j hj hq fz1_112_96 fz2_112_96
  · exact match_zero_fix ⟨113, by decide⟩ ⟨96, by decide⟩ p hp j hj hq fz1_113_96 fz2_113_96
  · exact match_zero_fix ⟨114, by decide⟩ ⟨96, by decide⟩ p hp j hj hq fz1_114_96 fz2_114_96
  · exact match_zero_fix ⟨115, by decide⟩ ⟨96, by decide⟩ p hp j hj hq fz1_115_96 fz2_115_96
  · exact match_zero_fix ⟨116, by decide⟩ ⟨96, by decide⟩ p hp j hj hq fz1_116_96 fz2_116_96
  · exact pair_117_96 p hp hrep j hj hq
  · exact match_zero_fix ⟨118, by decide⟩ ⟨96, by decide⟩ p hp j hj hq fz1_118_96 fz2_118_96
  · exact match_zero_fix ⟨119, by decide⟩ ⟨96, by decide⟩ p hp j hj hq fz1_119_96 fz2_119_96
  · exact match_zero_fix ⟨120, by decide⟩ ⟨96, by decide⟩ p hp j hj hq fz1_120_96 fz2_120_96
  · exact match_zero_fix ⟨121, by decide⟩ ⟨96, by decide⟩ p hp j hj hq fz1_121_96 fz2_121_96
  · exact match_zero_fix ⟨122, by decide⟩ ⟨96, by decide⟩ p hp j hj hq fz1_122_96 fz2_122_96
  · exact match_zero_fix ⟨123, by decide⟩ ⟨96, by decide⟩ p hp j hj hq fz1_123_96 fz2_123_96
  · exact match_zero_fix ⟨124, by decide⟩ ⟨96, by decide⟩ p hp j hj hq fz1_124_96 fz2_124_96
  · exact pair_125_96 p hp hrep j hj hq
  · exact match_zero_fix ⟨126, by decide⟩ ⟨96, by decide⟩ p hp j hj hq fz1_126_96 fz2_126_96
  · exact match_zero_fix ⟨127, by decide⟩ ⟨96, by decide⟩ p hp j hj hq fz1_127_96 fz2_127_96
  · exact pair_128_96 p hp hrep j hj hq
  · exact match_zero_fix ⟨129, by decide⟩ ⟨96, by decide⟩ p hp j hj hq fz1_129_96 fz2_129_96
  · exact match_zero_fix ⟨130, by decide⟩ ⟨96, by decide⟩ p hp j hj hq fz1_130_96 fz2_130_96
  · exact pair_131_96 p hp hrep j hj hq
  · exact match_zero_fix ⟨132, by decide⟩ ⟨96, by decide⟩ p hp j hj hq fz1_132_96 fz2_132_96
  · exact match_zero_fix ⟨133, by decide⟩ ⟨96, by decide⟩ p hp j hj hq fz1_133_96 fz2_133_96
  · exact match_zero_fix ⟨134, by decide⟩ ⟨96, by decide⟩ p hp j hj hq fz1_134_96 fz2_134_96
  · exact match_zero_fix ⟨135, by decide⟩ ⟨96, by decide⟩ p hp j hj hq fz1_135_96 fz2_135_96
  · exact match_zero_fix ⟨136, by decide⟩ ⟨96, by decide⟩ p hp j hj hq fz1_136_96 fz2_136_96
  · exact match_zero_fix ⟨137, by decide⟩ ⟨96, by decide⟩ p hp j hj hq fz1_137_96 fz2_137_96
  · exact match_zero_fix ⟨138, by decide⟩ ⟨96, by decide⟩ p hp j hj hq fz1_138_96 fz2_138_96
  · exact pair_139_96 p hp hrep j hj hq
  · exact match_zero_fix ⟨140, by decide⟩ ⟨96, by decide⟩ p hp j hj hq fz1_140_96 fz2_140_96
  · exact match_zero_fix ⟨141, by decide⟩ ⟨96, by decide⟩ p hp j hj hq fz1_141_96 fz2_141_96
  · exact match_zero_fix ⟨142, by decide⟩ ⟨96, by decide⟩ p hp j hj hq fz1_142_96 fz2_142_96
  · exact pair_143_96 p hp hrep j hj hq
  · exact match_zero_fix ⟨144, by decide⟩ ⟨96, by decide⟩ p hp j hj hq fz1_144_96 fz2_144_96
  · exact match_zero_fix ⟨145, by decide⟩ ⟨96, by decide⟩ p hp j hj hq fz1_145_96 fz2_145_96
  · exact match_zero_fix ⟨146, by decide⟩ ⟨96, by decide⟩ p hp j hj hq fz1_146_96 fz2_146_96
  · exact pair_147_96 p hp hrep j hj hq

theorem master_97 (p : Nat) (hp : p < (Q2.transData.getD 97 []).length)
    (hrep : (Q2.cosetIsRep.getD 97 []).getD p false = true)
    (rK : Fin 148) (j : Nat) (hj : j < (repChars.getD rK.val []).length)
    (hq : (normIsRep.getD rK.val []).getD j false = true) :
    species (Q2.reps (⟨97, by decide⟩ : Fin 148)) (colE2 ⟨97, by decide⟩ p hp)
        (rowE2 rK j hj hq)
      = species (reps (⟨97, by decide⟩ : Fin 148))
        (colE1 ⟨97, by decide⟩ p (transLenTr ⟨97, by decide⟩ p hp)) (rowE1 rK j hj) := by
  rcases rK with ⟨nK, hnK⟩; interval_cases nK
  · exact match_zero_len ⟨0, by decide⟩ ⟨97, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨1, by decide⟩ ⟨97, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨2, by decide⟩ ⟨97, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨3, by decide⟩ ⟨97, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨4, by decide⟩ ⟨97, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨5, by decide⟩ ⟨97, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨6, by decide⟩ ⟨97, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨7, by decide⟩ ⟨97, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨8, by decide⟩ ⟨97, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨9, by decide⟩ ⟨97, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨10, by decide⟩ ⟨97, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨11, by decide⟩ ⟨97, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨12, by decide⟩ ⟨97, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨13, by decide⟩ ⟨97, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨14, by decide⟩ ⟨97, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨15, by decide⟩ ⟨97, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨16, by decide⟩ ⟨97, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨17, by decide⟩ ⟨97, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨18, by decide⟩ ⟨97, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨19, by decide⟩ ⟨97, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨20, by decide⟩ ⟨97, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨21, by decide⟩ ⟨97, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨22, by decide⟩ ⟨97, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨23, by decide⟩ ⟨97, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨24, by decide⟩ ⟨97, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨25, by decide⟩ ⟨97, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨26, by decide⟩ ⟨97, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨27, by decide⟩ ⟨97, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨28, by decide⟩ ⟨97, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨29, by decide⟩ ⟨97, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨30, by decide⟩ ⟨97, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨31, by decide⟩ ⟨97, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨32, by decide⟩ ⟨97, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨33, by decide⟩ ⟨97, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨34, by decide⟩ ⟨97, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨35, by decide⟩ ⟨97, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨36, by decide⟩ ⟨97, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨37, by decide⟩ ⟨97, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨38, by decide⟩ ⟨97, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨39, by decide⟩ ⟨97, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨40, by decide⟩ ⟨97, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨41, by decide⟩ ⟨97, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨42, by decide⟩ ⟨97, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨43, by decide⟩ ⟨97, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨44, by decide⟩ ⟨97, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨45, by decide⟩ ⟨97, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨46, by decide⟩ ⟨97, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨47, by decide⟩ ⟨97, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨48, by decide⟩ ⟨97, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨49, by decide⟩ ⟨97, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨50, by decide⟩ ⟨97, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨51, by decide⟩ ⟨97, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨52, by decide⟩ ⟨97, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨53, by decide⟩ ⟨97, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨54, by decide⟩ ⟨97, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_fix ⟨55, by decide⟩ ⟨97, by decide⟩ p hp j hj hq fz1_55_97 fz2_55_97
  · exact match_zero_fix ⟨56, by decide⟩ ⟨97, by decide⟩ p hp j hj hq fz1_56_97 fz2_56_97
  · exact match_zero_fix ⟨57, by decide⟩ ⟨97, by decide⟩ p hp j hj hq fz1_57_97 fz2_57_97
  · exact match_zero_fix ⟨58, by decide⟩ ⟨97, by decide⟩ p hp j hj hq fz1_58_97 fz2_58_97
  · exact match_zero_fix ⟨59, by decide⟩ ⟨97, by decide⟩ p hp j hj hq fz1_59_97 fz2_59_97
  · exact match_zero_fix ⟨60, by decide⟩ ⟨97, by decide⟩ p hp j hj hq fz1_60_97 fz2_60_97
  · exact match_zero_fix ⟨61, by decide⟩ ⟨97, by decide⟩ p hp j hj hq fz1_61_97 fz2_61_97
  · exact match_zero_fix ⟨62, by decide⟩ ⟨97, by decide⟩ p hp j hj hq fz1_62_97 fz2_62_97
  · exact match_zero_fix ⟨63, by decide⟩ ⟨97, by decide⟩ p hp j hj hq fz1_63_97 fz2_63_97
  · exact match_zero_fix ⟨64, by decide⟩ ⟨97, by decide⟩ p hp j hj hq fz1_64_97 fz2_64_97
  · exact match_zero_fix ⟨65, by decide⟩ ⟨97, by decide⟩ p hp j hj hq fz1_65_97 fz2_65_97
  · exact match_zero_fix ⟨66, by decide⟩ ⟨97, by decide⟩ p hp j hj hq fz1_66_97 fz2_66_97
  · exact match_zero_fix ⟨67, by decide⟩ ⟨97, by decide⟩ p hp j hj hq fz1_67_97 fz2_67_97
  · exact match_zero_fix ⟨68, by decide⟩ ⟨97, by decide⟩ p hp j hj hq fz1_68_97 fz2_68_97
  · exact match_zero_fix ⟨69, by decide⟩ ⟨97, by decide⟩ p hp j hj hq fz1_69_97 fz2_69_97
  · exact match_zero_fix ⟨70, by decide⟩ ⟨97, by decide⟩ p hp j hj hq fz1_70_97 fz2_70_97
  · exact match_zero_fix ⟨71, by decide⟩ ⟨97, by decide⟩ p hp j hj hq fz1_71_97 fz2_71_97
  · exact match_zero_fix ⟨72, by decide⟩ ⟨97, by decide⟩ p hp j hj hq fz1_72_97 fz2_72_97
  · exact match_zero_fix ⟨73, by decide⟩ ⟨97, by decide⟩ p hp j hj hq fz1_73_97 fz2_73_97
  · exact match_zero_fix ⟨74, by decide⟩ ⟨97, by decide⟩ p hp j hj hq fz1_74_97 fz2_74_97
  · exact match_zero_fix ⟨75, by decide⟩ ⟨97, by decide⟩ p hp j hj hq fz1_75_97 fz2_75_97
  · exact match_zero_fix ⟨76, by decide⟩ ⟨97, by decide⟩ p hp j hj hq fz1_76_97 fz2_76_97
  · exact match_zero_fix ⟨77, by decide⟩ ⟨97, by decide⟩ p hp j hj hq fz1_77_97 fz2_77_97
  · exact match_zero_fix ⟨78, by decide⟩ ⟨97, by decide⟩ p hp j hj hq fz1_78_97 fz2_78_97
  · exact match_zero_fix ⟨79, by decide⟩ ⟨97, by decide⟩ p hp j hj hq fz1_79_97 fz2_79_97
  · exact match_zero_fix ⟨80, by decide⟩ ⟨97, by decide⟩ p hp j hj hq fz1_80_97 fz2_80_97
  · exact match_zero_fix ⟨81, by decide⟩ ⟨97, by decide⟩ p hp j hj hq fz1_81_97 fz2_81_97
  · exact match_zero_fix ⟨82, by decide⟩ ⟨97, by decide⟩ p hp j hj hq fz1_82_97 fz2_82_97
  · exact match_zero_fix ⟨83, by decide⟩ ⟨97, by decide⟩ p hp j hj hq fz1_83_97 fz2_83_97
  · exact match_zero_fix ⟨84, by decide⟩ ⟨97, by decide⟩ p hp j hj hq fz1_84_97 fz2_84_97
  · exact match_zero_fix ⟨85, by decide⟩ ⟨97, by decide⟩ p hp j hj hq fz1_85_97 fz2_85_97
  · exact match_zero_fix ⟨86, by decide⟩ ⟨97, by decide⟩ p hp j hj hq fz1_86_97 fz2_86_97
  · exact match_zero_fix ⟨87, by decide⟩ ⟨97, by decide⟩ p hp j hj hq fz1_87_97 fz2_87_97
  · exact match_zero_fix ⟨88, by decide⟩ ⟨97, by decide⟩ p hp j hj hq fz1_88_97 fz2_88_97
  · exact match_zero_fix ⟨89, by decide⟩ ⟨97, by decide⟩ p hp j hj hq fz1_89_97 fz2_89_97
  · exact match_zero_fix ⟨90, by decide⟩ ⟨97, by decide⟩ p hp j hj hq fz1_90_97 fz2_90_97
  · exact match_zero_fix ⟨91, by decide⟩ ⟨97, by decide⟩ p hp j hj hq fz1_91_97 fz2_91_97
  · exact match_zero_fix ⟨92, by decide⟩ ⟨97, by decide⟩ p hp j hj hq fz1_92_97 fz2_92_97
  · exact match_zero_fix ⟨93, by decide⟩ ⟨97, by decide⟩ p hp j hj hq fz1_93_97 fz2_93_97
  · exact match_zero_fix ⟨94, by decide⟩ ⟨97, by decide⟩ p hp j hj hq fz1_94_97 fz2_94_97
  · exact match_zero_fix ⟨95, by decide⟩ ⟨97, by decide⟩ p hp j hj hq fz1_95_97 fz2_95_97
  · exact match_zero_fix ⟨96, by decide⟩ ⟨97, by decide⟩ p hp j hj hq fz1_96_97 fz2_96_97
  · exact pair_97_97 p hp hrep j hj hq
  · exact match_zero_fix ⟨98, by decide⟩ ⟨97, by decide⟩ p hp j hj hq fz1_98_97 fz2_98_97
  · exact match_zero_fix ⟨99, by decide⟩ ⟨97, by decide⟩ p hp j hj hq fz1_99_97 fz2_99_97
  · exact match_zero_fix ⟨100, by decide⟩ ⟨97, by decide⟩ p hp j hj hq fz1_100_97 fz2_100_97
  · exact match_zero_fix ⟨101, by decide⟩ ⟨97, by decide⟩ p hp j hj hq fz1_101_97 fz2_101_97
  · exact match_zero_fix ⟨102, by decide⟩ ⟨97, by decide⟩ p hp j hj hq fz1_102_97 fz2_102_97
  · exact match_zero_fix ⟨103, by decide⟩ ⟨97, by decide⟩ p hp j hj hq fz1_103_97 fz2_103_97
  · exact match_zero_fix ⟨104, by decide⟩ ⟨97, by decide⟩ p hp j hj hq fz1_104_97 fz2_104_97
  · exact match_zero_fix ⟨105, by decide⟩ ⟨97, by decide⟩ p hp j hj hq fz1_105_97 fz2_105_97
  · exact match_zero_fix ⟨106, by decide⟩ ⟨97, by decide⟩ p hp j hj hq fz1_106_97 fz2_106_97
  · exact match_zero_fix ⟨107, by decide⟩ ⟨97, by decide⟩ p hp j hj hq fz1_107_97 fz2_107_97
  · exact match_zero_fix ⟨108, by decide⟩ ⟨97, by decide⟩ p hp j hj hq fz1_108_97 fz2_108_97
  · exact match_zero_fix ⟨109, by decide⟩ ⟨97, by decide⟩ p hp j hj hq fz1_109_97 fz2_109_97
  · exact match_zero_fix ⟨110, by decide⟩ ⟨97, by decide⟩ p hp j hj hq fz1_110_97 fz2_110_97
  · exact match_zero_fix ⟨111, by decide⟩ ⟨97, by decide⟩ p hp j hj hq fz1_111_97 fz2_111_97
  · exact match_zero_fix ⟨112, by decide⟩ ⟨97, by decide⟩ p hp j hj hq fz1_112_97 fz2_112_97
  · exact match_zero_fix ⟨113, by decide⟩ ⟨97, by decide⟩ p hp j hj hq fz1_113_97 fz2_113_97
  · exact match_zero_fix ⟨114, by decide⟩ ⟨97, by decide⟩ p hp j hj hq fz1_114_97 fz2_114_97
  · exact match_zero_fix ⟨115, by decide⟩ ⟨97, by decide⟩ p hp j hj hq fz1_115_97 fz2_115_97
  · exact match_zero_fix ⟨116, by decide⟩ ⟨97, by decide⟩ p hp j hj hq fz1_116_97 fz2_116_97
  · exact match_zero_fix ⟨117, by decide⟩ ⟨97, by decide⟩ p hp j hj hq fz1_117_97 fz2_117_97
  · exact pair_118_97 p hp hrep j hj hq
  · exact match_zero_fix ⟨119, by decide⟩ ⟨97, by decide⟩ p hp j hj hq fz1_119_97 fz2_119_97
  · exact match_zero_fix ⟨120, by decide⟩ ⟨97, by decide⟩ p hp j hj hq fz1_120_97 fz2_120_97
  · exact pair_121_97 p hp hrep j hj hq
  · exact match_zero_fix ⟨122, by decide⟩ ⟨97, by decide⟩ p hp j hj hq fz1_122_97 fz2_122_97
  · exact match_zero_fix ⟨123, by decide⟩ ⟨97, by decide⟩ p hp j hj hq fz1_123_97 fz2_123_97
  · exact match_zero_fix ⟨124, by decide⟩ ⟨97, by decide⟩ p hp j hj hq fz1_124_97 fz2_124_97
  · exact match_zero_fix ⟨125, by decide⟩ ⟨97, by decide⟩ p hp j hj hq fz1_125_97 fz2_125_97
  · exact match_zero_fix ⟨126, by decide⟩ ⟨97, by decide⟩ p hp j hj hq fz1_126_97 fz2_126_97
  · exact match_zero_fix ⟨127, by decide⟩ ⟨97, by decide⟩ p hp j hj hq fz1_127_97 fz2_127_97
  · exact match_zero_fix ⟨128, by decide⟩ ⟨97, by decide⟩ p hp j hj hq fz1_128_97 fz2_128_97
  · exact pair_129_97 p hp hrep j hj hq
  · exact match_zero_fix ⟨130, by decide⟩ ⟨97, by decide⟩ p hp j hj hq fz1_130_97 fz2_130_97
  · exact match_zero_fix ⟨131, by decide⟩ ⟨97, by decide⟩ p hp j hj hq fz1_131_97 fz2_131_97
  · exact pair_132_97 p hp hrep j hj hq
  · exact match_zero_fix ⟨133, by decide⟩ ⟨97, by decide⟩ p hp j hj hq fz1_133_97 fz2_133_97
  · exact match_zero_fix ⟨134, by decide⟩ ⟨97, by decide⟩ p hp j hj hq fz1_134_97 fz2_134_97
  · exact match_zero_fix ⟨135, by decide⟩ ⟨97, by decide⟩ p hp j hj hq fz1_135_97 fz2_135_97
  · exact match_zero_fix ⟨136, by decide⟩ ⟨97, by decide⟩ p hp j hj hq fz1_136_97 fz2_136_97
  · exact match_zero_fix ⟨137, by decide⟩ ⟨97, by decide⟩ p hp j hj hq fz1_137_97 fz2_137_97
  · exact match_zero_fix ⟨138, by decide⟩ ⟨97, by decide⟩ p hp j hj hq fz1_138_97 fz2_138_97
  · exact match_zero_fix ⟨139, by decide⟩ ⟨97, by decide⟩ p hp j hj hq fz1_139_97 fz2_139_97
  · exact pair_140_97 p hp hrep j hj hq
  · exact match_zero_fix ⟨141, by decide⟩ ⟨97, by decide⟩ p hp j hj hq fz1_141_97 fz2_141_97
  · exact match_zero_fix ⟨142, by decide⟩ ⟨97, by decide⟩ p hp j hj hq fz1_142_97 fz2_142_97
  · exact pair_143_97 p hp hrep j hj hq
  · exact match_zero_fix ⟨144, by decide⟩ ⟨97, by decide⟩ p hp j hj hq fz1_144_97 fz2_144_97
  · exact match_zero_fix ⟨145, by decide⟩ ⟨97, by decide⟩ p hp j hj hq fz1_145_97 fz2_145_97
  · exact match_zero_fix ⟨146, by decide⟩ ⟨97, by decide⟩ p hp j hj hq fz1_146_97 fz2_146_97
  · exact pair_147_97 p hp hrep j hj hq

theorem master_98 (p : Nat) (hp : p < (Q2.transData.getD 98 []).length)
    (hrep : (Q2.cosetIsRep.getD 98 []).getD p false = true)
    (rK : Fin 148) (j : Nat) (hj : j < (repChars.getD rK.val []).length)
    (hq : (normIsRep.getD rK.val []).getD j false = true) :
    species (Q2.reps (⟨98, by decide⟩ : Fin 148)) (colE2 ⟨98, by decide⟩ p hp)
        (rowE2 rK j hj hq)
      = species (reps (⟨98, by decide⟩ : Fin 148))
        (colE1 ⟨98, by decide⟩ p (transLenTr ⟨98, by decide⟩ p hp)) (rowE1 rK j hj) := by
  rcases rK with ⟨nK, hnK⟩; interval_cases nK
  · exact match_zero_len ⟨0, by decide⟩ ⟨98, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨1, by decide⟩ ⟨98, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨2, by decide⟩ ⟨98, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨3, by decide⟩ ⟨98, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨4, by decide⟩ ⟨98, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨5, by decide⟩ ⟨98, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨6, by decide⟩ ⟨98, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨7, by decide⟩ ⟨98, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨8, by decide⟩ ⟨98, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨9, by decide⟩ ⟨98, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨10, by decide⟩ ⟨98, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨11, by decide⟩ ⟨98, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨12, by decide⟩ ⟨98, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨13, by decide⟩ ⟨98, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨14, by decide⟩ ⟨98, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨15, by decide⟩ ⟨98, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨16, by decide⟩ ⟨98, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨17, by decide⟩ ⟨98, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨18, by decide⟩ ⟨98, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨19, by decide⟩ ⟨98, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨20, by decide⟩ ⟨98, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨21, by decide⟩ ⟨98, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨22, by decide⟩ ⟨98, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨23, by decide⟩ ⟨98, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨24, by decide⟩ ⟨98, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨25, by decide⟩ ⟨98, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨26, by decide⟩ ⟨98, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨27, by decide⟩ ⟨98, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨28, by decide⟩ ⟨98, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨29, by decide⟩ ⟨98, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨30, by decide⟩ ⟨98, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨31, by decide⟩ ⟨98, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨32, by decide⟩ ⟨98, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨33, by decide⟩ ⟨98, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨34, by decide⟩ ⟨98, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨35, by decide⟩ ⟨98, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨36, by decide⟩ ⟨98, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨37, by decide⟩ ⟨98, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨38, by decide⟩ ⟨98, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨39, by decide⟩ ⟨98, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨40, by decide⟩ ⟨98, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨41, by decide⟩ ⟨98, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨42, by decide⟩ ⟨98, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨43, by decide⟩ ⟨98, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨44, by decide⟩ ⟨98, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨45, by decide⟩ ⟨98, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨46, by decide⟩ ⟨98, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨47, by decide⟩ ⟨98, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨48, by decide⟩ ⟨98, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨49, by decide⟩ ⟨98, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨50, by decide⟩ ⟨98, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨51, by decide⟩ ⟨98, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨52, by decide⟩ ⟨98, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨53, by decide⟩ ⟨98, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨54, by decide⟩ ⟨98, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_fix ⟨55, by decide⟩ ⟨98, by decide⟩ p hp j hj hq fz1_55_98 fz2_55_98
  · exact match_zero_fix ⟨56, by decide⟩ ⟨98, by decide⟩ p hp j hj hq fz1_56_98 fz2_56_98
  · exact match_zero_fix ⟨57, by decide⟩ ⟨98, by decide⟩ p hp j hj hq fz1_57_98 fz2_57_98
  · exact match_zero_fix ⟨58, by decide⟩ ⟨98, by decide⟩ p hp j hj hq fz1_58_98 fz2_58_98
  · exact match_zero_fix ⟨59, by decide⟩ ⟨98, by decide⟩ p hp j hj hq fz1_59_98 fz2_59_98
  · exact match_zero_fix ⟨60, by decide⟩ ⟨98, by decide⟩ p hp j hj hq fz1_60_98 fz2_60_98
  · exact match_zero_fix ⟨61, by decide⟩ ⟨98, by decide⟩ p hp j hj hq fz1_61_98 fz2_61_98
  · exact match_zero_fix ⟨62, by decide⟩ ⟨98, by decide⟩ p hp j hj hq fz1_62_98 fz2_62_98
  · exact match_zero_fix ⟨63, by decide⟩ ⟨98, by decide⟩ p hp j hj hq fz1_63_98 fz2_63_98
  · exact match_zero_fix ⟨64, by decide⟩ ⟨98, by decide⟩ p hp j hj hq fz1_64_98 fz2_64_98
  · exact match_zero_fix ⟨65, by decide⟩ ⟨98, by decide⟩ p hp j hj hq fz1_65_98 fz2_65_98
  · exact match_zero_fix ⟨66, by decide⟩ ⟨98, by decide⟩ p hp j hj hq fz1_66_98 fz2_66_98
  · exact match_zero_fix ⟨67, by decide⟩ ⟨98, by decide⟩ p hp j hj hq fz1_67_98 fz2_67_98
  · exact match_zero_fix ⟨68, by decide⟩ ⟨98, by decide⟩ p hp j hj hq fz1_68_98 fz2_68_98
  · exact match_zero_fix ⟨69, by decide⟩ ⟨98, by decide⟩ p hp j hj hq fz1_69_98 fz2_69_98
  · exact match_zero_fix ⟨70, by decide⟩ ⟨98, by decide⟩ p hp j hj hq fz1_70_98 fz2_70_98
  · exact match_zero_fix ⟨71, by decide⟩ ⟨98, by decide⟩ p hp j hj hq fz1_71_98 fz2_71_98
  · exact match_zero_fix ⟨72, by decide⟩ ⟨98, by decide⟩ p hp j hj hq fz1_72_98 fz2_72_98
  · exact match_zero_fix ⟨73, by decide⟩ ⟨98, by decide⟩ p hp j hj hq fz1_73_98 fz2_73_98
  · exact match_zero_fix ⟨74, by decide⟩ ⟨98, by decide⟩ p hp j hj hq fz1_74_98 fz2_74_98
  · exact match_zero_fix ⟨75, by decide⟩ ⟨98, by decide⟩ p hp j hj hq fz1_75_98 fz2_75_98
  · exact match_zero_fix ⟨76, by decide⟩ ⟨98, by decide⟩ p hp j hj hq fz1_76_98 fz2_76_98
  · exact match_zero_fix ⟨77, by decide⟩ ⟨98, by decide⟩ p hp j hj hq fz1_77_98 fz2_77_98
  · exact match_zero_fix ⟨78, by decide⟩ ⟨98, by decide⟩ p hp j hj hq fz1_78_98 fz2_78_98
  · exact match_zero_fix ⟨79, by decide⟩ ⟨98, by decide⟩ p hp j hj hq fz1_79_98 fz2_79_98
  · exact match_zero_fix ⟨80, by decide⟩ ⟨98, by decide⟩ p hp j hj hq fz1_80_98 fz2_80_98
  · exact match_zero_fix ⟨81, by decide⟩ ⟨98, by decide⟩ p hp j hj hq fz1_81_98 fz2_81_98
  · exact match_zero_fix ⟨82, by decide⟩ ⟨98, by decide⟩ p hp j hj hq fz1_82_98 fz2_82_98
  · exact match_zero_fix ⟨83, by decide⟩ ⟨98, by decide⟩ p hp j hj hq fz1_83_98 fz2_83_98
  · exact match_zero_fix ⟨84, by decide⟩ ⟨98, by decide⟩ p hp j hj hq fz1_84_98 fz2_84_98
  · exact match_zero_fix ⟨85, by decide⟩ ⟨98, by decide⟩ p hp j hj hq fz1_85_98 fz2_85_98
  · exact match_zero_fix ⟨86, by decide⟩ ⟨98, by decide⟩ p hp j hj hq fz1_86_98 fz2_86_98
  · exact match_zero_fix ⟨87, by decide⟩ ⟨98, by decide⟩ p hp j hj hq fz1_87_98 fz2_87_98
  · exact match_zero_fix ⟨88, by decide⟩ ⟨98, by decide⟩ p hp j hj hq fz1_88_98 fz2_88_98
  · exact match_zero_fix ⟨89, by decide⟩ ⟨98, by decide⟩ p hp j hj hq fz1_89_98 fz2_89_98
  · exact match_zero_fix ⟨90, by decide⟩ ⟨98, by decide⟩ p hp j hj hq fz1_90_98 fz2_90_98
  · exact match_zero_fix ⟨91, by decide⟩ ⟨98, by decide⟩ p hp j hj hq fz1_91_98 fz2_91_98
  · exact match_zero_fix ⟨92, by decide⟩ ⟨98, by decide⟩ p hp j hj hq fz1_92_98 fz2_92_98
  · exact match_zero_fix ⟨93, by decide⟩ ⟨98, by decide⟩ p hp j hj hq fz1_93_98 fz2_93_98
  · exact match_zero_fix ⟨94, by decide⟩ ⟨98, by decide⟩ p hp j hj hq fz1_94_98 fz2_94_98
  · exact match_zero_fix ⟨95, by decide⟩ ⟨98, by decide⟩ p hp j hj hq fz1_95_98 fz2_95_98
  · exact match_zero_fix ⟨96, by decide⟩ ⟨98, by decide⟩ p hp j hj hq fz1_96_98 fz2_96_98
  · exact match_zero_fix ⟨97, by decide⟩ ⟨98, by decide⟩ p hp j hj hq fz1_97_98 fz2_97_98
  · exact pair_98_98 p hp hrep j hj hq
  · exact match_zero_fix ⟨99, by decide⟩ ⟨98, by decide⟩ p hp j hj hq fz1_99_98 fz2_99_98
  · exact match_zero_fix ⟨100, by decide⟩ ⟨98, by decide⟩ p hp j hj hq fz1_100_98 fz2_100_98
  · exact match_zero_fix ⟨101, by decide⟩ ⟨98, by decide⟩ p hp j hj hq fz1_101_98 fz2_101_98
  · exact match_zero_fix ⟨102, by decide⟩ ⟨98, by decide⟩ p hp j hj hq fz1_102_98 fz2_102_98
  · exact match_zero_fix ⟨103, by decide⟩ ⟨98, by decide⟩ p hp j hj hq fz1_103_98 fz2_103_98
  · exact match_zero_fix ⟨104, by decide⟩ ⟨98, by decide⟩ p hp j hj hq fz1_104_98 fz2_104_98
  · exact match_zero_fix ⟨105, by decide⟩ ⟨98, by decide⟩ p hp j hj hq fz1_105_98 fz2_105_98
  · exact match_zero_fix ⟨106, by decide⟩ ⟨98, by decide⟩ p hp j hj hq fz1_106_98 fz2_106_98
  · exact match_zero_fix ⟨107, by decide⟩ ⟨98, by decide⟩ p hp j hj hq fz1_107_98 fz2_107_98
  · exact match_zero_fix ⟨108, by decide⟩ ⟨98, by decide⟩ p hp j hj hq fz1_108_98 fz2_108_98
  · exact match_zero_fix ⟨109, by decide⟩ ⟨98, by decide⟩ p hp j hj hq fz1_109_98 fz2_109_98
  · exact match_zero_fix ⟨110, by decide⟩ ⟨98, by decide⟩ p hp j hj hq fz1_110_98 fz2_110_98
  · exact match_zero_fix ⟨111, by decide⟩ ⟨98, by decide⟩ p hp j hj hq fz1_111_98 fz2_111_98
  · exact match_zero_fix ⟨112, by decide⟩ ⟨98, by decide⟩ p hp j hj hq fz1_112_98 fz2_112_98
  · exact match_zero_fix ⟨113, by decide⟩ ⟨98, by decide⟩ p hp j hj hq fz1_113_98 fz2_113_98
  · exact match_zero_fix ⟨114, by decide⟩ ⟨98, by decide⟩ p hp j hj hq fz1_114_98 fz2_114_98
  · exact match_zero_fix ⟨115, by decide⟩ ⟨98, by decide⟩ p hp j hj hq fz1_115_98 fz2_115_98
  · exact match_zero_fix ⟨116, by decide⟩ ⟨98, by decide⟩ p hp j hj hq fz1_116_98 fz2_116_98
  · exact match_zero_fix ⟨117, by decide⟩ ⟨98, by decide⟩ p hp j hj hq fz1_117_98 fz2_117_98
  · exact match_zero_fix ⟨118, by decide⟩ ⟨98, by decide⟩ p hp j hj hq fz1_118_98 fz2_118_98
  · exact pair_119_98 p hp hrep j hj hq
  · exact match_zero_fix ⟨120, by decide⟩ ⟨98, by decide⟩ p hp j hj hq fz1_120_98 fz2_120_98
  · exact match_zero_fix ⟨121, by decide⟩ ⟨98, by decide⟩ p hp j hj hq fz1_121_98 fz2_121_98
  · exact pair_122_98 p hp hrep j hj hq
  · exact match_zero_fix ⟨123, by decide⟩ ⟨98, by decide⟩ p hp j hj hq fz1_123_98 fz2_123_98
  · exact match_zero_fix ⟨124, by decide⟩ ⟨98, by decide⟩ p hp j hj hq fz1_124_98 fz2_124_98
  · exact match_zero_fix ⟨125, by decide⟩ ⟨98, by decide⟩ p hp j hj hq fz1_125_98 fz2_125_98
  · exact match_zero_fix ⟨126, by decide⟩ ⟨98, by decide⟩ p hp j hj hq fz1_126_98 fz2_126_98
  · exact match_zero_fix ⟨127, by decide⟩ ⟨98, by decide⟩ p hp j hj hq fz1_127_98 fz2_127_98
  · exact match_zero_fix ⟨128, by decide⟩ ⟨98, by decide⟩ p hp j hj hq fz1_128_98 fz2_128_98
  · exact match_zero_fix ⟨129, by decide⟩ ⟨98, by decide⟩ p hp j hj hq fz1_129_98 fz2_129_98
  · exact pair_130_98 p hp hrep j hj hq
  · exact match_zero_fix ⟨131, by decide⟩ ⟨98, by decide⟩ p hp j hj hq fz1_131_98 fz2_131_98
  · exact match_zero_fix ⟨132, by decide⟩ ⟨98, by decide⟩ p hp j hj hq fz1_132_98 fz2_132_98
  · exact pair_133_98 p hp hrep j hj hq
  · exact match_zero_fix ⟨134, by decide⟩ ⟨98, by decide⟩ p hp j hj hq fz1_134_98 fz2_134_98
  · exact match_zero_fix ⟨135, by decide⟩ ⟨98, by decide⟩ p hp j hj hq fz1_135_98 fz2_135_98
  · exact pair_136_98 p hp hrep j hj hq
  · exact match_zero_fix ⟨137, by decide⟩ ⟨98, by decide⟩ p hp j hj hq fz1_137_98 fz2_137_98
  · exact match_zero_fix ⟨138, by decide⟩ ⟨98, by decide⟩ p hp j hj hq fz1_138_98 fz2_138_98
  · exact match_zero_fix ⟨139, by decide⟩ ⟨98, by decide⟩ p hp j hj hq fz1_139_98 fz2_139_98
  · exact match_zero_fix ⟨140, by decide⟩ ⟨98, by decide⟩ p hp j hj hq fz1_140_98 fz2_140_98
  · exact match_zero_fix ⟨141, by decide⟩ ⟨98, by decide⟩ p hp j hj hq fz1_141_98 fz2_141_98
  · exact match_zero_fix ⟨142, by decide⟩ ⟨98, by decide⟩ p hp j hj hq fz1_142_98 fz2_142_98
  · exact pair_143_98 p hp hrep j hj hq
  · exact match_zero_fix ⟨144, by decide⟩ ⟨98, by decide⟩ p hp j hj hq fz1_144_98 fz2_144_98
  · exact match_zero_fix ⟨145, by decide⟩ ⟨98, by decide⟩ p hp j hj hq fz1_145_98 fz2_145_98
  · exact match_zero_fix ⟨146, by decide⟩ ⟨98, by decide⟩ p hp j hj hq fz1_146_98 fz2_146_98
  · exact pair_147_98 p hp hrep j hj hq

theorem master_99 (p : Nat) (hp : p < (Q2.transData.getD 99 []).length)
    (hrep : (Q2.cosetIsRep.getD 99 []).getD p false = true)
    (rK : Fin 148) (j : Nat) (hj : j < (repChars.getD rK.val []).length)
    (hq : (normIsRep.getD rK.val []).getD j false = true) :
    species (Q2.reps (⟨99, by decide⟩ : Fin 148)) (colE2 ⟨99, by decide⟩ p hp)
        (rowE2 rK j hj hq)
      = species (reps (⟨99, by decide⟩ : Fin 148))
        (colE1 ⟨99, by decide⟩ p (transLenTr ⟨99, by decide⟩ p hp)) (rowE1 rK j hj) := by
  rcases rK with ⟨nK, hnK⟩; interval_cases nK
  · exact match_zero_len ⟨0, by decide⟩ ⟨99, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨1, by decide⟩ ⟨99, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨2, by decide⟩ ⟨99, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨3, by decide⟩ ⟨99, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨4, by decide⟩ ⟨99, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨5, by decide⟩ ⟨99, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨6, by decide⟩ ⟨99, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨7, by decide⟩ ⟨99, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨8, by decide⟩ ⟨99, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨9, by decide⟩ ⟨99, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨10, by decide⟩ ⟨99, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨11, by decide⟩ ⟨99, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨12, by decide⟩ ⟨99, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨13, by decide⟩ ⟨99, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨14, by decide⟩ ⟨99, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨15, by decide⟩ ⟨99, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨16, by decide⟩ ⟨99, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨17, by decide⟩ ⟨99, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨18, by decide⟩ ⟨99, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨19, by decide⟩ ⟨99, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨20, by decide⟩ ⟨99, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨21, by decide⟩ ⟨99, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨22, by decide⟩ ⟨99, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨23, by decide⟩ ⟨99, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨24, by decide⟩ ⟨99, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨25, by decide⟩ ⟨99, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨26, by decide⟩ ⟨99, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨27, by decide⟩ ⟨99, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨28, by decide⟩ ⟨99, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨29, by decide⟩ ⟨99, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨30, by decide⟩ ⟨99, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨31, by decide⟩ ⟨99, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨32, by decide⟩ ⟨99, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨33, by decide⟩ ⟨99, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨34, by decide⟩ ⟨99, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨35, by decide⟩ ⟨99, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨36, by decide⟩ ⟨99, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨37, by decide⟩ ⟨99, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨38, by decide⟩ ⟨99, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨39, by decide⟩ ⟨99, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨40, by decide⟩ ⟨99, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨41, by decide⟩ ⟨99, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨42, by decide⟩ ⟨99, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨43, by decide⟩ ⟨99, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨44, by decide⟩ ⟨99, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨45, by decide⟩ ⟨99, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨46, by decide⟩ ⟨99, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨47, by decide⟩ ⟨99, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨48, by decide⟩ ⟨99, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨49, by decide⟩ ⟨99, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨50, by decide⟩ ⟨99, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨51, by decide⟩ ⟨99, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨52, by decide⟩ ⟨99, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨53, by decide⟩ ⟨99, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨54, by decide⟩ ⟨99, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_fix ⟨55, by decide⟩ ⟨99, by decide⟩ p hp j hj hq fz1_55_99 fz2_55_99
  · exact match_zero_fix ⟨56, by decide⟩ ⟨99, by decide⟩ p hp j hj hq fz1_56_99 fz2_56_99
  · exact match_zero_fix ⟨57, by decide⟩ ⟨99, by decide⟩ p hp j hj hq fz1_57_99 fz2_57_99
  · exact match_zero_fix ⟨58, by decide⟩ ⟨99, by decide⟩ p hp j hj hq fz1_58_99 fz2_58_99
  · exact match_zero_fix ⟨59, by decide⟩ ⟨99, by decide⟩ p hp j hj hq fz1_59_99 fz2_59_99
  · exact match_zero_fix ⟨60, by decide⟩ ⟨99, by decide⟩ p hp j hj hq fz1_60_99 fz2_60_99
  · exact match_zero_fix ⟨61, by decide⟩ ⟨99, by decide⟩ p hp j hj hq fz1_61_99 fz2_61_99
  · exact match_zero_fix ⟨62, by decide⟩ ⟨99, by decide⟩ p hp j hj hq fz1_62_99 fz2_62_99
  · exact match_zero_fix ⟨63, by decide⟩ ⟨99, by decide⟩ p hp j hj hq fz1_63_99 fz2_63_99
  · exact match_zero_fix ⟨64, by decide⟩ ⟨99, by decide⟩ p hp j hj hq fz1_64_99 fz2_64_99
  · exact match_zero_fix ⟨65, by decide⟩ ⟨99, by decide⟩ p hp j hj hq fz1_65_99 fz2_65_99
  · exact match_zero_fix ⟨66, by decide⟩ ⟨99, by decide⟩ p hp j hj hq fz1_66_99 fz2_66_99
  · exact match_zero_fix ⟨67, by decide⟩ ⟨99, by decide⟩ p hp j hj hq fz1_67_99 fz2_67_99
  · exact match_zero_fix ⟨68, by decide⟩ ⟨99, by decide⟩ p hp j hj hq fz1_68_99 fz2_68_99
  · exact match_zero_fix ⟨69, by decide⟩ ⟨99, by decide⟩ p hp j hj hq fz1_69_99 fz2_69_99
  · exact match_zero_fix ⟨70, by decide⟩ ⟨99, by decide⟩ p hp j hj hq fz1_70_99 fz2_70_99
  · exact match_zero_fix ⟨71, by decide⟩ ⟨99, by decide⟩ p hp j hj hq fz1_71_99 fz2_71_99
  · exact match_zero_fix ⟨72, by decide⟩ ⟨99, by decide⟩ p hp j hj hq fz1_72_99 fz2_72_99
  · exact match_zero_fix ⟨73, by decide⟩ ⟨99, by decide⟩ p hp j hj hq fz1_73_99 fz2_73_99
  · exact match_zero_fix ⟨74, by decide⟩ ⟨99, by decide⟩ p hp j hj hq fz1_74_99 fz2_74_99
  · exact match_zero_fix ⟨75, by decide⟩ ⟨99, by decide⟩ p hp j hj hq fz1_75_99 fz2_75_99
  · exact match_zero_fix ⟨76, by decide⟩ ⟨99, by decide⟩ p hp j hj hq fz1_76_99 fz2_76_99
  · exact match_zero_fix ⟨77, by decide⟩ ⟨99, by decide⟩ p hp j hj hq fz1_77_99 fz2_77_99
  · exact match_zero_fix ⟨78, by decide⟩ ⟨99, by decide⟩ p hp j hj hq fz1_78_99 fz2_78_99
  · exact match_zero_fix ⟨79, by decide⟩ ⟨99, by decide⟩ p hp j hj hq fz1_79_99 fz2_79_99
  · exact match_zero_fix ⟨80, by decide⟩ ⟨99, by decide⟩ p hp j hj hq fz1_80_99 fz2_80_99
  · exact match_zero_fix ⟨81, by decide⟩ ⟨99, by decide⟩ p hp j hj hq fz1_81_99 fz2_81_99
  · exact match_zero_fix ⟨82, by decide⟩ ⟨99, by decide⟩ p hp j hj hq fz1_82_99 fz2_82_99
  · exact match_zero_fix ⟨83, by decide⟩ ⟨99, by decide⟩ p hp j hj hq fz1_83_99 fz2_83_99
  · exact match_zero_fix ⟨84, by decide⟩ ⟨99, by decide⟩ p hp j hj hq fz1_84_99 fz2_84_99
  · exact match_zero_fix ⟨85, by decide⟩ ⟨99, by decide⟩ p hp j hj hq fz1_85_99 fz2_85_99
  · exact match_zero_fix ⟨86, by decide⟩ ⟨99, by decide⟩ p hp j hj hq fz1_86_99 fz2_86_99
  · exact match_zero_fix ⟨87, by decide⟩ ⟨99, by decide⟩ p hp j hj hq fz1_87_99 fz2_87_99
  · exact match_zero_fix ⟨88, by decide⟩ ⟨99, by decide⟩ p hp j hj hq fz1_88_99 fz2_88_99
  · exact match_zero_fix ⟨89, by decide⟩ ⟨99, by decide⟩ p hp j hj hq fz1_89_99 fz2_89_99
  · exact match_zero_fix ⟨90, by decide⟩ ⟨99, by decide⟩ p hp j hj hq fz1_90_99 fz2_90_99
  · exact match_zero_fix ⟨91, by decide⟩ ⟨99, by decide⟩ p hp j hj hq fz1_91_99 fz2_91_99
  · exact match_zero_fix ⟨92, by decide⟩ ⟨99, by decide⟩ p hp j hj hq fz1_92_99 fz2_92_99
  · exact match_zero_fix ⟨93, by decide⟩ ⟨99, by decide⟩ p hp j hj hq fz1_93_99 fz2_93_99
  · exact match_zero_fix ⟨94, by decide⟩ ⟨99, by decide⟩ p hp j hj hq fz1_94_99 fz2_94_99
  · exact match_zero_fix ⟨95, by decide⟩ ⟨99, by decide⟩ p hp j hj hq fz1_95_99 fz2_95_99
  · exact match_zero_fix ⟨96, by decide⟩ ⟨99, by decide⟩ p hp j hj hq fz1_96_99 fz2_96_99
  · exact match_zero_fix ⟨97, by decide⟩ ⟨99, by decide⟩ p hp j hj hq fz1_97_99 fz2_97_99
  · exact match_zero_fix ⟨98, by decide⟩ ⟨99, by decide⟩ p hp j hj hq fz1_98_99 fz2_98_99
  · exact pair_99_99 p hp hrep j hj hq
  · exact match_zero_fix ⟨100, by decide⟩ ⟨99, by decide⟩ p hp j hj hq fz1_100_99 fz2_100_99
  · exact match_zero_fix ⟨101, by decide⟩ ⟨99, by decide⟩ p hp j hj hq fz1_101_99 fz2_101_99
  · exact match_zero_fix ⟨102, by decide⟩ ⟨99, by decide⟩ p hp j hj hq fz1_102_99 fz2_102_99
  · exact match_zero_fix ⟨103, by decide⟩ ⟨99, by decide⟩ p hp j hj hq fz1_103_99 fz2_103_99
  · exact match_zero_fix ⟨104, by decide⟩ ⟨99, by decide⟩ p hp j hj hq fz1_104_99 fz2_104_99
  · exact match_zero_fix ⟨105, by decide⟩ ⟨99, by decide⟩ p hp j hj hq fz1_105_99 fz2_105_99
  · exact match_zero_fix ⟨106, by decide⟩ ⟨99, by decide⟩ p hp j hj hq fz1_106_99 fz2_106_99
  · exact match_zero_fix ⟨107, by decide⟩ ⟨99, by decide⟩ p hp j hj hq fz1_107_99 fz2_107_99
  · exact match_zero_fix ⟨108, by decide⟩ ⟨99, by decide⟩ p hp j hj hq fz1_108_99 fz2_108_99
  · exact match_zero_fix ⟨109, by decide⟩ ⟨99, by decide⟩ p hp j hj hq fz1_109_99 fz2_109_99
  · exact match_zero_fix ⟨110, by decide⟩ ⟨99, by decide⟩ p hp j hj hq fz1_110_99 fz2_110_99
  · exact match_zero_fix ⟨111, by decide⟩ ⟨99, by decide⟩ p hp j hj hq fz1_111_99 fz2_111_99
  · exact match_zero_fix ⟨112, by decide⟩ ⟨99, by decide⟩ p hp j hj hq fz1_112_99 fz2_112_99
  · exact match_zero_fix ⟨113, by decide⟩ ⟨99, by decide⟩ p hp j hj hq fz1_113_99 fz2_113_99
  · exact match_zero_fix ⟨114, by decide⟩ ⟨99, by decide⟩ p hp j hj hq fz1_114_99 fz2_114_99
  · exact match_zero_fix ⟨115, by decide⟩ ⟨99, by decide⟩ p hp j hj hq fz1_115_99 fz2_115_99
  · exact match_zero_fix ⟨116, by decide⟩ ⟨99, by decide⟩ p hp j hj hq fz1_116_99 fz2_116_99
  · exact match_zero_fix ⟨117, by decide⟩ ⟨99, by decide⟩ p hp j hj hq fz1_117_99 fz2_117_99
  · exact match_zero_fix ⟨118, by decide⟩ ⟨99, by decide⟩ p hp j hj hq fz1_118_99 fz2_118_99
  · exact match_zero_fix ⟨119, by decide⟩ ⟨99, by decide⟩ p hp j hj hq fz1_119_99 fz2_119_99
  · exact pair_120_99 p hp hrep j hj hq
  · exact match_zero_fix ⟨121, by decide⟩ ⟨99, by decide⟩ p hp j hj hq fz1_121_99 fz2_121_99
  · exact match_zero_fix ⟨122, by decide⟩ ⟨99, by decide⟩ p hp j hj hq fz1_122_99 fz2_122_99
  · exact pair_123_99 p hp hrep j hj hq
  · exact match_zero_fix ⟨124, by decide⟩ ⟨99, by decide⟩ p hp j hj hq fz1_124_99 fz2_124_99
  · exact match_zero_fix ⟨125, by decide⟩ ⟨99, by decide⟩ p hp j hj hq fz1_125_99 fz2_125_99
  · exact pair_126_99 p hp hrep j hj hq
  · exact match_zero_fix ⟨127, by decide⟩ ⟨99, by decide⟩ p hp j hj hq fz1_127_99 fz2_127_99
  · exact match_zero_fix ⟨128, by decide⟩ ⟨99, by decide⟩ p hp j hj hq fz1_128_99 fz2_128_99
  · exact match_zero_fix ⟨129, by decide⟩ ⟨99, by decide⟩ p hp j hj hq fz1_129_99 fz2_129_99
  · exact match_zero_fix ⟨130, by decide⟩ ⟨99, by decide⟩ p hp j hj hq fz1_130_99 fz2_130_99
  · exact match_zero_fix ⟨131, by decide⟩ ⟨99, by decide⟩ p hp j hj hq fz1_131_99 fz2_131_99
  · exact match_zero_fix ⟨132, by decide⟩ ⟨99, by decide⟩ p hp j hj hq fz1_132_99 fz2_132_99
  · exact match_zero_fix ⟨133, by decide⟩ ⟨99, by decide⟩ p hp j hj hq fz1_133_99 fz2_133_99
  · exact pair_134_99 p hp hrep j hj hq
  · exact match_zero_fix ⟨135, by decide⟩ ⟨99, by decide⟩ p hp j hj hq fz1_135_99 fz2_135_99
  · exact match_zero_fix ⟨136, by decide⟩ ⟨99, by decide⟩ p hp j hj hq fz1_136_99 fz2_136_99
  · exact pair_137_99 p hp hrep j hj hq
  · exact match_zero_fix ⟨138, by decide⟩ ⟨99, by decide⟩ p hp j hj hq fz1_138_99 fz2_138_99
  · exact match_zero_fix ⟨139, by decide⟩ ⟨99, by decide⟩ p hp j hj hq fz1_139_99 fz2_139_99
  · exact match_zero_fix ⟨140, by decide⟩ ⟨99, by decide⟩ p hp j hj hq fz1_140_99 fz2_140_99
  · exact match_zero_fix ⟨141, by decide⟩ ⟨99, by decide⟩ p hp j hj hq fz1_141_99 fz2_141_99
  · exact match_zero_fix ⟨142, by decide⟩ ⟨99, by decide⟩ p hp j hj hq fz1_142_99 fz2_142_99
  · exact pair_143_99 p hp hrep j hj hq
  · exact match_zero_fix ⟨144, by decide⟩ ⟨99, by decide⟩ p hp j hj hq fz1_144_99 fz2_144_99
  · exact match_zero_fix ⟨145, by decide⟩ ⟨99, by decide⟩ p hp j hj hq fz1_145_99 fz2_145_99
  · exact match_zero_fix ⟨146, by decide⟩ ⟨99, by decide⟩ p hp j hj hq fz1_146_99 fz2_146_99
  · exact pair_147_99 p hp hrep j hj hq

theorem master_100 (p : Nat) (hp : p < (Q2.transData.getD 100 []).length)
    (hrep : (Q2.cosetIsRep.getD 100 []).getD p false = true)
    (rK : Fin 148) (j : Nat) (hj : j < (repChars.getD rK.val []).length)
    (hq : (normIsRep.getD rK.val []).getD j false = true) :
    species (Q2.reps (⟨100, by decide⟩ : Fin 148)) (colE2 ⟨100, by decide⟩ p hp)
        (rowE2 rK j hj hq)
      = species (reps (⟨100, by decide⟩ : Fin 148))
        (colE1 ⟨100, by decide⟩ p (transLenTr ⟨100, by decide⟩ p hp)) (rowE1 rK j hj) := by
  rcases rK with ⟨nK, hnK⟩; interval_cases nK
  · exact match_zero_len ⟨0, by decide⟩ ⟨100, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨1, by decide⟩ ⟨100, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨2, by decide⟩ ⟨100, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨3, by decide⟩ ⟨100, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨4, by decide⟩ ⟨100, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨5, by decide⟩ ⟨100, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨6, by decide⟩ ⟨100, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨7, by decide⟩ ⟨100, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨8, by decide⟩ ⟨100, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨9, by decide⟩ ⟨100, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨10, by decide⟩ ⟨100, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨11, by decide⟩ ⟨100, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨12, by decide⟩ ⟨100, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨13, by decide⟩ ⟨100, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨14, by decide⟩ ⟨100, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨15, by decide⟩ ⟨100, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨16, by decide⟩ ⟨100, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨17, by decide⟩ ⟨100, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨18, by decide⟩ ⟨100, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨19, by decide⟩ ⟨100, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨20, by decide⟩ ⟨100, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨21, by decide⟩ ⟨100, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨22, by decide⟩ ⟨100, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨23, by decide⟩ ⟨100, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨24, by decide⟩ ⟨100, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨25, by decide⟩ ⟨100, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨26, by decide⟩ ⟨100, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨27, by decide⟩ ⟨100, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨28, by decide⟩ ⟨100, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨29, by decide⟩ ⟨100, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨30, by decide⟩ ⟨100, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨31, by decide⟩ ⟨100, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨32, by decide⟩ ⟨100, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨33, by decide⟩ ⟨100, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨34, by decide⟩ ⟨100, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨35, by decide⟩ ⟨100, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨36, by decide⟩ ⟨100, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨37, by decide⟩ ⟨100, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨38, by decide⟩ ⟨100, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨39, by decide⟩ ⟨100, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨40, by decide⟩ ⟨100, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨41, by decide⟩ ⟨100, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨42, by decide⟩ ⟨100, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨43, by decide⟩ ⟨100, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨44, by decide⟩ ⟨100, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨45, by decide⟩ ⟨100, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨46, by decide⟩ ⟨100, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨47, by decide⟩ ⟨100, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨48, by decide⟩ ⟨100, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨49, by decide⟩ ⟨100, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨50, by decide⟩ ⟨100, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨51, by decide⟩ ⟨100, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨52, by decide⟩ ⟨100, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨53, by decide⟩ ⟨100, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨54, by decide⟩ ⟨100, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_fix ⟨55, by decide⟩ ⟨100, by decide⟩ p hp j hj hq fz1_55_100 fz2_55_100
  · exact match_zero_fix ⟨56, by decide⟩ ⟨100, by decide⟩ p hp j hj hq fz1_56_100 fz2_56_100
  · exact match_zero_fix ⟨57, by decide⟩ ⟨100, by decide⟩ p hp j hj hq fz1_57_100 fz2_57_100
  · exact match_zero_fix ⟨58, by decide⟩ ⟨100, by decide⟩ p hp j hj hq fz1_58_100 fz2_58_100
  · exact match_zero_fix ⟨59, by decide⟩ ⟨100, by decide⟩ p hp j hj hq fz1_59_100 fz2_59_100
  · exact match_zero_fix ⟨60, by decide⟩ ⟨100, by decide⟩ p hp j hj hq fz1_60_100 fz2_60_100
  · exact match_zero_fix ⟨61, by decide⟩ ⟨100, by decide⟩ p hp j hj hq fz1_61_100 fz2_61_100
  · exact match_zero_fix ⟨62, by decide⟩ ⟨100, by decide⟩ p hp j hj hq fz1_62_100 fz2_62_100
  · exact match_zero_fix ⟨63, by decide⟩ ⟨100, by decide⟩ p hp j hj hq fz1_63_100 fz2_63_100
  · exact match_zero_fix ⟨64, by decide⟩ ⟨100, by decide⟩ p hp j hj hq fz1_64_100 fz2_64_100
  · exact match_zero_fix ⟨65, by decide⟩ ⟨100, by decide⟩ p hp j hj hq fz1_65_100 fz2_65_100
  · exact match_zero_fix ⟨66, by decide⟩ ⟨100, by decide⟩ p hp j hj hq fz1_66_100 fz2_66_100
  · exact match_zero_fix ⟨67, by decide⟩ ⟨100, by decide⟩ p hp j hj hq fz1_67_100 fz2_67_100
  · exact match_zero_fix ⟨68, by decide⟩ ⟨100, by decide⟩ p hp j hj hq fz1_68_100 fz2_68_100
  · exact match_zero_fix ⟨69, by decide⟩ ⟨100, by decide⟩ p hp j hj hq fz1_69_100 fz2_69_100
  · exact match_zero_fix ⟨70, by decide⟩ ⟨100, by decide⟩ p hp j hj hq fz1_70_100 fz2_70_100
  · exact match_zero_fix ⟨71, by decide⟩ ⟨100, by decide⟩ p hp j hj hq fz1_71_100 fz2_71_100
  · exact match_zero_fix ⟨72, by decide⟩ ⟨100, by decide⟩ p hp j hj hq fz1_72_100 fz2_72_100
  · exact match_zero_fix ⟨73, by decide⟩ ⟨100, by decide⟩ p hp j hj hq fz1_73_100 fz2_73_100
  · exact match_zero_fix ⟨74, by decide⟩ ⟨100, by decide⟩ p hp j hj hq fz1_74_100 fz2_74_100
  · exact match_zero_fix ⟨75, by decide⟩ ⟨100, by decide⟩ p hp j hj hq fz1_75_100 fz2_75_100
  · exact match_zero_fix ⟨76, by decide⟩ ⟨100, by decide⟩ p hp j hj hq fz1_76_100 fz2_76_100
  · exact match_zero_fix ⟨77, by decide⟩ ⟨100, by decide⟩ p hp j hj hq fz1_77_100 fz2_77_100
  · exact match_zero_fix ⟨78, by decide⟩ ⟨100, by decide⟩ p hp j hj hq fz1_78_100 fz2_78_100
  · exact match_zero_fix ⟨79, by decide⟩ ⟨100, by decide⟩ p hp j hj hq fz1_79_100 fz2_79_100
  · exact match_zero_fix ⟨80, by decide⟩ ⟨100, by decide⟩ p hp j hj hq fz1_80_100 fz2_80_100
  · exact match_zero_fix ⟨81, by decide⟩ ⟨100, by decide⟩ p hp j hj hq fz1_81_100 fz2_81_100
  · exact match_zero_fix ⟨82, by decide⟩ ⟨100, by decide⟩ p hp j hj hq fz1_82_100 fz2_82_100
  · exact match_zero_fix ⟨83, by decide⟩ ⟨100, by decide⟩ p hp j hj hq fz1_83_100 fz2_83_100
  · exact match_zero_fix ⟨84, by decide⟩ ⟨100, by decide⟩ p hp j hj hq fz1_84_100 fz2_84_100
  · exact match_zero_fix ⟨85, by decide⟩ ⟨100, by decide⟩ p hp j hj hq fz1_85_100 fz2_85_100
  · exact match_zero_fix ⟨86, by decide⟩ ⟨100, by decide⟩ p hp j hj hq fz1_86_100 fz2_86_100
  · exact match_zero_fix ⟨87, by decide⟩ ⟨100, by decide⟩ p hp j hj hq fz1_87_100 fz2_87_100
  · exact match_zero_fix ⟨88, by decide⟩ ⟨100, by decide⟩ p hp j hj hq fz1_88_100 fz2_88_100
  · exact match_zero_fix ⟨89, by decide⟩ ⟨100, by decide⟩ p hp j hj hq fz1_89_100 fz2_89_100
  · exact match_zero_fix ⟨90, by decide⟩ ⟨100, by decide⟩ p hp j hj hq fz1_90_100 fz2_90_100
  · exact match_zero_fix ⟨91, by decide⟩ ⟨100, by decide⟩ p hp j hj hq fz1_91_100 fz2_91_100
  · exact match_zero_fix ⟨92, by decide⟩ ⟨100, by decide⟩ p hp j hj hq fz1_92_100 fz2_92_100
  · exact match_zero_fix ⟨93, by decide⟩ ⟨100, by decide⟩ p hp j hj hq fz1_93_100 fz2_93_100
  · exact match_zero_fix ⟨94, by decide⟩ ⟨100, by decide⟩ p hp j hj hq fz1_94_100 fz2_94_100
  · exact match_zero_fix ⟨95, by decide⟩ ⟨100, by decide⟩ p hp j hj hq fz1_95_100 fz2_95_100
  · exact match_zero_fix ⟨96, by decide⟩ ⟨100, by decide⟩ p hp j hj hq fz1_96_100 fz2_96_100
  · exact match_zero_fix ⟨97, by decide⟩ ⟨100, by decide⟩ p hp j hj hq fz1_97_100 fz2_97_100
  · exact match_zero_fix ⟨98, by decide⟩ ⟨100, by decide⟩ p hp j hj hq fz1_98_100 fz2_98_100
  · exact match_zero_fix ⟨99, by decide⟩ ⟨100, by decide⟩ p hp j hj hq fz1_99_100 fz2_99_100
  · exact pair_100_100 p hp hrep j hj hq
  · exact match_zero_fix ⟨101, by decide⟩ ⟨100, by decide⟩ p hp j hj hq fz1_101_100 fz2_101_100
  · exact match_zero_fix ⟨102, by decide⟩ ⟨100, by decide⟩ p hp j hj hq fz1_102_100 fz2_102_100
  · exact match_zero_fix ⟨103, by decide⟩ ⟨100, by decide⟩ p hp j hj hq fz1_103_100 fz2_103_100
  · exact match_zero_fix ⟨104, by decide⟩ ⟨100, by decide⟩ p hp j hj hq fz1_104_100 fz2_104_100
  · exact match_zero_fix ⟨105, by decide⟩ ⟨100, by decide⟩ p hp j hj hq fz1_105_100 fz2_105_100
  · exact match_zero_fix ⟨106, by decide⟩ ⟨100, by decide⟩ p hp j hj hq fz1_106_100 fz2_106_100
  · exact match_zero_fix ⟨107, by decide⟩ ⟨100, by decide⟩ p hp j hj hq fz1_107_100 fz2_107_100
  · exact match_zero_fix ⟨108, by decide⟩ ⟨100, by decide⟩ p hp j hj hq fz1_108_100 fz2_108_100
  · exact match_zero_fix ⟨109, by decide⟩ ⟨100, by decide⟩ p hp j hj hq fz1_109_100 fz2_109_100
  · exact match_zero_fix ⟨110, by decide⟩ ⟨100, by decide⟩ p hp j hj hq fz1_110_100 fz2_110_100
  · exact match_zero_fix ⟨111, by decide⟩ ⟨100, by decide⟩ p hp j hj hq fz1_111_100 fz2_111_100
  · exact match_zero_fix ⟨112, by decide⟩ ⟨100, by decide⟩ p hp j hj hq fz1_112_100 fz2_112_100
  · exact match_zero_fix ⟨113, by decide⟩ ⟨100, by decide⟩ p hp j hj hq fz1_113_100 fz2_113_100
  · exact match_zero_fix ⟨114, by decide⟩ ⟨100, by decide⟩ p hp j hj hq fz1_114_100 fz2_114_100
  · exact match_zero_fix ⟨115, by decide⟩ ⟨100, by decide⟩ p hp j hj hq fz1_115_100 fz2_115_100
  · exact pair_116_100 p hp hrep j hj hq
  · exact match_zero_fix ⟨117, by decide⟩ ⟨100, by decide⟩ p hp j hj hq fz1_117_100 fz2_117_100
  · exact match_zero_fix ⟨118, by decide⟩ ⟨100, by decide⟩ p hp j hj hq fz1_118_100 fz2_118_100
  · exact match_zero_fix ⟨119, by decide⟩ ⟨100, by decide⟩ p hp j hj hq fz1_119_100 fz2_119_100
  · exact match_zero_fix ⟨120, by decide⟩ ⟨100, by decide⟩ p hp j hj hq fz1_120_100 fz2_120_100
  · exact match_zero_fix ⟨121, by decide⟩ ⟨100, by decide⟩ p hp j hj hq fz1_121_100 fz2_121_100
  · exact match_zero_fix ⟨122, by decide⟩ ⟨100, by decide⟩ p hp j hj hq fz1_122_100 fz2_122_100
  · exact pair_123_100 p hp hrep j hj hq
  · exact match_zero_fix ⟨124, by decide⟩ ⟨100, by decide⟩ p hp j hj hq fz1_124_100 fz2_124_100
  · exact match_zero_fix ⟨125, by decide⟩ ⟨100, by decide⟩ p hp j hj hq fz1_125_100 fz2_125_100
  · exact match_zero_fix ⟨126, by decide⟩ ⟨100, by decide⟩ p hp j hj hq fz1_126_100 fz2_126_100
  · exact match_zero_fix ⟨127, by decide⟩ ⟨100, by decide⟩ p hp j hj hq fz1_127_100 fz2_127_100
  · exact match_zero_fix ⟨128, by decide⟩ ⟨100, by decide⟩ p hp j hj hq fz1_128_100 fz2_128_100
  · exact match_zero_fix ⟨129, by decide⟩ ⟨100, by decide⟩ p hp j hj hq fz1_129_100 fz2_129_100
  · exact pair_130_100 p hp hrep j hj hq
  · exact match_zero_fix ⟨131, by decide⟩ ⟨100, by decide⟩ p hp j hj hq fz1_131_100 fz2_131_100
  · exact pair_132_100 p hp hrep j hj hq
  · exact match_zero_fix ⟨133, by decide⟩ ⟨100, by decide⟩ p hp j hj hq fz1_133_100 fz2_133_100
  · exact match_zero_fix ⟨134, by decide⟩ ⟨100, by decide⟩ p hp j hj hq fz1_134_100 fz2_134_100
  · exact match_zero_fix ⟨135, by decide⟩ ⟨100, by decide⟩ p hp j hj hq fz1_135_100 fz2_135_100
  · exact match_zero_fix ⟨136, by decide⟩ ⟨100, by decide⟩ p hp j hj hq fz1_136_100 fz2_136_100
  · exact match_zero_fix ⟨137, by decide⟩ ⟨100, by decide⟩ p hp j hj hq fz1_137_100 fz2_137_100
  · exact match_zero_fix ⟨138, by decide⟩ ⟨100, by decide⟩ p hp j hj hq fz1_138_100 fz2_138_100
  · exact pair_139_100 p hp hrep j hj hq
  · exact match_zero_fix ⟨140, by decide⟩ ⟨100, by decide⟩ p hp j hj hq fz1_140_100 fz2_140_100
  · exact match_zero_fix ⟨141, by decide⟩ ⟨100, by decide⟩ p hp j hj hq fz1_141_100 fz2_141_100
  · exact match_zero_fix ⟨142, by decide⟩ ⟨100, by decide⟩ p hp j hj hq fz1_142_100 fz2_142_100
  · exact match_zero_fix ⟨143, by decide⟩ ⟨100, by decide⟩ p hp j hj hq fz1_143_100 fz2_143_100
  · exact pair_144_100 p hp hrep j hj hq
  · exact match_zero_fix ⟨145, by decide⟩ ⟨100, by decide⟩ p hp j hj hq fz1_145_100 fz2_145_100
  · exact match_zero_fix ⟨146, by decide⟩ ⟨100, by decide⟩ p hp j hj hq fz1_146_100 fz2_146_100
  · exact pair_147_100 p hp hrep j hj hq

theorem master_101 (p : Nat) (hp : p < (Q2.transData.getD 101 []).length)
    (hrep : (Q2.cosetIsRep.getD 101 []).getD p false = true)
    (rK : Fin 148) (j : Nat) (hj : j < (repChars.getD rK.val []).length)
    (hq : (normIsRep.getD rK.val []).getD j false = true) :
    species (Q2.reps (⟨101, by decide⟩ : Fin 148)) (colE2 ⟨101, by decide⟩ p hp)
        (rowE2 rK j hj hq)
      = species (reps (⟨101, by decide⟩ : Fin 148))
        (colE1 ⟨101, by decide⟩ p (transLenTr ⟨101, by decide⟩ p hp)) (rowE1 rK j hj) := by
  rcases rK with ⟨nK, hnK⟩; interval_cases nK
  · exact match_zero_len ⟨0, by decide⟩ ⟨101, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨1, by decide⟩ ⟨101, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨2, by decide⟩ ⟨101, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨3, by decide⟩ ⟨101, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨4, by decide⟩ ⟨101, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨5, by decide⟩ ⟨101, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨6, by decide⟩ ⟨101, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨7, by decide⟩ ⟨101, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨8, by decide⟩ ⟨101, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨9, by decide⟩ ⟨101, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨10, by decide⟩ ⟨101, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨11, by decide⟩ ⟨101, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨12, by decide⟩ ⟨101, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨13, by decide⟩ ⟨101, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨14, by decide⟩ ⟨101, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨15, by decide⟩ ⟨101, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨16, by decide⟩ ⟨101, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨17, by decide⟩ ⟨101, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨18, by decide⟩ ⟨101, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨19, by decide⟩ ⟨101, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨20, by decide⟩ ⟨101, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨21, by decide⟩ ⟨101, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨22, by decide⟩ ⟨101, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨23, by decide⟩ ⟨101, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨24, by decide⟩ ⟨101, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨25, by decide⟩ ⟨101, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨26, by decide⟩ ⟨101, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨27, by decide⟩ ⟨101, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨28, by decide⟩ ⟨101, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨29, by decide⟩ ⟨101, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨30, by decide⟩ ⟨101, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨31, by decide⟩ ⟨101, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨32, by decide⟩ ⟨101, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨33, by decide⟩ ⟨101, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨34, by decide⟩ ⟨101, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨35, by decide⟩ ⟨101, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨36, by decide⟩ ⟨101, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨37, by decide⟩ ⟨101, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨38, by decide⟩ ⟨101, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨39, by decide⟩ ⟨101, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨40, by decide⟩ ⟨101, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨41, by decide⟩ ⟨101, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨42, by decide⟩ ⟨101, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨43, by decide⟩ ⟨101, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨44, by decide⟩ ⟨101, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨45, by decide⟩ ⟨101, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨46, by decide⟩ ⟨101, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨47, by decide⟩ ⟨101, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨48, by decide⟩ ⟨101, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨49, by decide⟩ ⟨101, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨50, by decide⟩ ⟨101, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨51, by decide⟩ ⟨101, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨52, by decide⟩ ⟨101, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨53, by decide⟩ ⟨101, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨54, by decide⟩ ⟨101, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_fix ⟨55, by decide⟩ ⟨101, by decide⟩ p hp j hj hq fz1_55_101 fz2_55_101
  · exact match_zero_fix ⟨56, by decide⟩ ⟨101, by decide⟩ p hp j hj hq fz1_56_101 fz2_56_101
  · exact match_zero_fix ⟨57, by decide⟩ ⟨101, by decide⟩ p hp j hj hq fz1_57_101 fz2_57_101
  · exact match_zero_fix ⟨58, by decide⟩ ⟨101, by decide⟩ p hp j hj hq fz1_58_101 fz2_58_101
  · exact match_zero_fix ⟨59, by decide⟩ ⟨101, by decide⟩ p hp j hj hq fz1_59_101 fz2_59_101
  · exact match_zero_fix ⟨60, by decide⟩ ⟨101, by decide⟩ p hp j hj hq fz1_60_101 fz2_60_101
  · exact match_zero_fix ⟨61, by decide⟩ ⟨101, by decide⟩ p hp j hj hq fz1_61_101 fz2_61_101
  · exact match_zero_fix ⟨62, by decide⟩ ⟨101, by decide⟩ p hp j hj hq fz1_62_101 fz2_62_101
  · exact match_zero_fix ⟨63, by decide⟩ ⟨101, by decide⟩ p hp j hj hq fz1_63_101 fz2_63_101
  · exact match_zero_fix ⟨64, by decide⟩ ⟨101, by decide⟩ p hp j hj hq fz1_64_101 fz2_64_101
  · exact match_zero_fix ⟨65, by decide⟩ ⟨101, by decide⟩ p hp j hj hq fz1_65_101 fz2_65_101
  · exact match_zero_fix ⟨66, by decide⟩ ⟨101, by decide⟩ p hp j hj hq fz1_66_101 fz2_66_101
  · exact match_zero_fix ⟨67, by decide⟩ ⟨101, by decide⟩ p hp j hj hq fz1_67_101 fz2_67_101
  · exact match_zero_fix ⟨68, by decide⟩ ⟨101, by decide⟩ p hp j hj hq fz1_68_101 fz2_68_101
  · exact match_zero_fix ⟨69, by decide⟩ ⟨101, by decide⟩ p hp j hj hq fz1_69_101 fz2_69_101
  · exact match_zero_fix ⟨70, by decide⟩ ⟨101, by decide⟩ p hp j hj hq fz1_70_101 fz2_70_101
  · exact match_zero_fix ⟨71, by decide⟩ ⟨101, by decide⟩ p hp j hj hq fz1_71_101 fz2_71_101
  · exact match_zero_fix ⟨72, by decide⟩ ⟨101, by decide⟩ p hp j hj hq fz1_72_101 fz2_72_101
  · exact match_zero_fix ⟨73, by decide⟩ ⟨101, by decide⟩ p hp j hj hq fz1_73_101 fz2_73_101
  · exact match_zero_fix ⟨74, by decide⟩ ⟨101, by decide⟩ p hp j hj hq fz1_74_101 fz2_74_101
  · exact match_zero_fix ⟨75, by decide⟩ ⟨101, by decide⟩ p hp j hj hq fz1_75_101 fz2_75_101
  · exact match_zero_fix ⟨76, by decide⟩ ⟨101, by decide⟩ p hp j hj hq fz1_76_101 fz2_76_101
  · exact match_zero_fix ⟨77, by decide⟩ ⟨101, by decide⟩ p hp j hj hq fz1_77_101 fz2_77_101
  · exact match_zero_fix ⟨78, by decide⟩ ⟨101, by decide⟩ p hp j hj hq fz1_78_101 fz2_78_101
  · exact match_zero_fix ⟨79, by decide⟩ ⟨101, by decide⟩ p hp j hj hq fz1_79_101 fz2_79_101
  · exact match_zero_fix ⟨80, by decide⟩ ⟨101, by decide⟩ p hp j hj hq fz1_80_101 fz2_80_101
  · exact match_zero_fix ⟨81, by decide⟩ ⟨101, by decide⟩ p hp j hj hq fz1_81_101 fz2_81_101
  · exact match_zero_fix ⟨82, by decide⟩ ⟨101, by decide⟩ p hp j hj hq fz1_82_101 fz2_82_101
  · exact match_zero_fix ⟨83, by decide⟩ ⟨101, by decide⟩ p hp j hj hq fz1_83_101 fz2_83_101
  · exact match_zero_fix ⟨84, by decide⟩ ⟨101, by decide⟩ p hp j hj hq fz1_84_101 fz2_84_101
  · exact match_zero_fix ⟨85, by decide⟩ ⟨101, by decide⟩ p hp j hj hq fz1_85_101 fz2_85_101
  · exact match_zero_fix ⟨86, by decide⟩ ⟨101, by decide⟩ p hp j hj hq fz1_86_101 fz2_86_101
  · exact match_zero_fix ⟨87, by decide⟩ ⟨101, by decide⟩ p hp j hj hq fz1_87_101 fz2_87_101
  · exact match_zero_fix ⟨88, by decide⟩ ⟨101, by decide⟩ p hp j hj hq fz1_88_101 fz2_88_101
  · exact match_zero_fix ⟨89, by decide⟩ ⟨101, by decide⟩ p hp j hj hq fz1_89_101 fz2_89_101
  · exact match_zero_fix ⟨90, by decide⟩ ⟨101, by decide⟩ p hp j hj hq fz1_90_101 fz2_90_101
  · exact match_zero_fix ⟨91, by decide⟩ ⟨101, by decide⟩ p hp j hj hq fz1_91_101 fz2_91_101
  · exact match_zero_fix ⟨92, by decide⟩ ⟨101, by decide⟩ p hp j hj hq fz1_92_101 fz2_92_101
  · exact match_zero_fix ⟨93, by decide⟩ ⟨101, by decide⟩ p hp j hj hq fz1_93_101 fz2_93_101
  · exact match_zero_fix ⟨94, by decide⟩ ⟨101, by decide⟩ p hp j hj hq fz1_94_101 fz2_94_101
  · exact match_zero_fix ⟨95, by decide⟩ ⟨101, by decide⟩ p hp j hj hq fz1_95_101 fz2_95_101
  · exact match_zero_fix ⟨96, by decide⟩ ⟨101, by decide⟩ p hp j hj hq fz1_96_101 fz2_96_101
  · exact match_zero_fix ⟨97, by decide⟩ ⟨101, by decide⟩ p hp j hj hq fz1_97_101 fz2_97_101
  · exact match_zero_fix ⟨98, by decide⟩ ⟨101, by decide⟩ p hp j hj hq fz1_98_101 fz2_98_101
  · exact match_zero_fix ⟨99, by decide⟩ ⟨101, by decide⟩ p hp j hj hq fz1_99_101 fz2_99_101
  · exact match_zero_fix ⟨100, by decide⟩ ⟨101, by decide⟩ p hp j hj hq fz1_100_101 fz2_100_101
  · exact pair_101_101 p hp hrep j hj hq
  · exact match_zero_fix ⟨102, by decide⟩ ⟨101, by decide⟩ p hp j hj hq fz1_102_101 fz2_102_101
  · exact match_zero_fix ⟨103, by decide⟩ ⟨101, by decide⟩ p hp j hj hq fz1_103_101 fz2_103_101
  · exact match_zero_fix ⟨104, by decide⟩ ⟨101, by decide⟩ p hp j hj hq fz1_104_101 fz2_104_101
  · exact match_zero_fix ⟨105, by decide⟩ ⟨101, by decide⟩ p hp j hj hq fz1_105_101 fz2_105_101
  · exact match_zero_fix ⟨106, by decide⟩ ⟨101, by decide⟩ p hp j hj hq fz1_106_101 fz2_106_101
  · exact match_zero_fix ⟨107, by decide⟩ ⟨101, by decide⟩ p hp j hj hq fz1_107_101 fz2_107_101
  · exact match_zero_fix ⟨108, by decide⟩ ⟨101, by decide⟩ p hp j hj hq fz1_108_101 fz2_108_101
  · exact match_zero_fix ⟨109, by decide⟩ ⟨101, by decide⟩ p hp j hj hq fz1_109_101 fz2_109_101
  · exact match_zero_fix ⟨110, by decide⟩ ⟨101, by decide⟩ p hp j hj hq fz1_110_101 fz2_110_101
  · exact match_zero_fix ⟨111, by decide⟩ ⟨101, by decide⟩ p hp j hj hq fz1_111_101 fz2_111_101
  · exact match_zero_fix ⟨112, by decide⟩ ⟨101, by decide⟩ p hp j hj hq fz1_112_101 fz2_112_101
  · exact match_zero_fix ⟨113, by decide⟩ ⟨101, by decide⟩ p hp j hj hq fz1_113_101 fz2_113_101
  · exact match_zero_fix ⟨114, by decide⟩ ⟨101, by decide⟩ p hp j hj hq fz1_114_101 fz2_114_101
  · exact match_zero_fix ⟨115, by decide⟩ ⟨101, by decide⟩ p hp j hj hq fz1_115_101 fz2_115_101
  · exact match_zero_fix ⟨116, by decide⟩ ⟨101, by decide⟩ p hp j hj hq fz1_116_101 fz2_116_101
  · exact pair_117_101 p hp hrep j hj hq
  · exact match_zero_fix ⟨118, by decide⟩ ⟨101, by decide⟩ p hp j hj hq fz1_118_101 fz2_118_101
  · exact match_zero_fix ⟨119, by decide⟩ ⟨101, by decide⟩ p hp j hj hq fz1_119_101 fz2_119_101
  · exact match_zero_fix ⟨120, by decide⟩ ⟨101, by decide⟩ p hp j hj hq fz1_120_101 fz2_120_101
  · exact match_zero_fix ⟨121, by decide⟩ ⟨101, by decide⟩ p hp j hj hq fz1_121_101 fz2_121_101
  · exact match_zero_fix ⟨122, by decide⟩ ⟨101, by decide⟩ p hp j hj hq fz1_122_101 fz2_122_101
  · exact match_zero_fix ⟨123, by decide⟩ ⟨101, by decide⟩ p hp j hj hq fz1_123_101 fz2_123_101
  · exact pair_124_101 p hp hrep j hj hq
  · exact match_zero_fix ⟨125, by decide⟩ ⟨101, by decide⟩ p hp j hj hq fz1_125_101 fz2_125_101
  · exact pair_126_101 p hp hrep j hj hq
  · exact match_zero_fix ⟨127, by decide⟩ ⟨101, by decide⟩ p hp j hj hq fz1_127_101 fz2_127_101
  · exact match_zero_fix ⟨128, by decide⟩ ⟨101, by decide⟩ p hp j hj hq fz1_128_101 fz2_128_101
  · exact match_zero_fix ⟨129, by decide⟩ ⟨101, by decide⟩ p hp j hj hq fz1_129_101 fz2_129_101
  · exact match_zero_fix ⟨130, by decide⟩ ⟨101, by decide⟩ p hp j hj hq fz1_130_101 fz2_130_101
  · exact match_zero_fix ⟨131, by decide⟩ ⟨101, by decide⟩ p hp j hj hq fz1_131_101 fz2_131_101
  · exact match_zero_fix ⟨132, by decide⟩ ⟨101, by decide⟩ p hp j hj hq fz1_132_101 fz2_132_101
  · exact pair_133_101 p hp hrep j hj hq
  · exact match_zero_fix ⟨134, by decide⟩ ⟨101, by decide⟩ p hp j hj hq fz1_134_101 fz2_134_101
  · exact match_zero_fix ⟨135, by decide⟩ ⟨101, by decide⟩ p hp j hj hq fz1_135_101 fz2_135_101
  · exact match_zero_fix ⟨136, by decide⟩ ⟨101, by decide⟩ p hp j hj hq fz1_136_101 fz2_136_101
  · exact match_zero_fix ⟨137, by decide⟩ ⟨101, by decide⟩ p hp j hj hq fz1_137_101 fz2_137_101
  · exact match_zero_fix ⟨138, by decide⟩ ⟨101, by decide⟩ p hp j hj hq fz1_138_101 fz2_138_101
  · exact match_zero_fix ⟨139, by decide⟩ ⟨101, by decide⟩ p hp j hj hq fz1_139_101 fz2_139_101
  · exact pair_140_101 p hp hrep j hj hq
  · exact match_zero_fix ⟨141, by decide⟩ ⟨101, by decide⟩ p hp j hj hq fz1_141_101 fz2_141_101
  · exact match_zero_fix ⟨142, by decide⟩ ⟨101, by decide⟩ p hp j hj hq fz1_142_101 fz2_142_101
  · exact match_zero_fix ⟨143, by decide⟩ ⟨101, by decide⟩ p hp j hj hq fz1_143_101 fz2_143_101
  · exact pair_144_101 p hp hrep j hj hq
  · exact match_zero_fix ⟨145, by decide⟩ ⟨101, by decide⟩ p hp j hj hq fz1_145_101 fz2_145_101
  · exact match_zero_fix ⟨146, by decide⟩ ⟨101, by decide⟩ p hp j hj hq fz1_146_101 fz2_146_101
  · exact pair_147_101 p hp hrep j hj hq

theorem master_102 (p : Nat) (hp : p < (Q2.transData.getD 102 []).length)
    (hrep : (Q2.cosetIsRep.getD 102 []).getD p false = true)
    (rK : Fin 148) (j : Nat) (hj : j < (repChars.getD rK.val []).length)
    (hq : (normIsRep.getD rK.val []).getD j false = true) :
    species (Q2.reps (⟨102, by decide⟩ : Fin 148)) (colE2 ⟨102, by decide⟩ p hp)
        (rowE2 rK j hj hq)
      = species (reps (⟨102, by decide⟩ : Fin 148))
        (colE1 ⟨102, by decide⟩ p (transLenTr ⟨102, by decide⟩ p hp)) (rowE1 rK j hj) := by
  rcases rK with ⟨nK, hnK⟩; interval_cases nK
  · exact match_zero_len ⟨0, by decide⟩ ⟨102, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨1, by decide⟩ ⟨102, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨2, by decide⟩ ⟨102, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨3, by decide⟩ ⟨102, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨4, by decide⟩ ⟨102, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨5, by decide⟩ ⟨102, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨6, by decide⟩ ⟨102, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨7, by decide⟩ ⟨102, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨8, by decide⟩ ⟨102, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨9, by decide⟩ ⟨102, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨10, by decide⟩ ⟨102, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨11, by decide⟩ ⟨102, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨12, by decide⟩ ⟨102, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨13, by decide⟩ ⟨102, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨14, by decide⟩ ⟨102, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨15, by decide⟩ ⟨102, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨16, by decide⟩ ⟨102, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨17, by decide⟩ ⟨102, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨18, by decide⟩ ⟨102, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨19, by decide⟩ ⟨102, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨20, by decide⟩ ⟨102, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨21, by decide⟩ ⟨102, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨22, by decide⟩ ⟨102, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨23, by decide⟩ ⟨102, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨24, by decide⟩ ⟨102, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨25, by decide⟩ ⟨102, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨26, by decide⟩ ⟨102, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨27, by decide⟩ ⟨102, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨28, by decide⟩ ⟨102, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨29, by decide⟩ ⟨102, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨30, by decide⟩ ⟨102, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨31, by decide⟩ ⟨102, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨32, by decide⟩ ⟨102, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨33, by decide⟩ ⟨102, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨34, by decide⟩ ⟨102, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨35, by decide⟩ ⟨102, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨36, by decide⟩ ⟨102, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨37, by decide⟩ ⟨102, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨38, by decide⟩ ⟨102, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨39, by decide⟩ ⟨102, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨40, by decide⟩ ⟨102, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨41, by decide⟩ ⟨102, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨42, by decide⟩ ⟨102, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨43, by decide⟩ ⟨102, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨44, by decide⟩ ⟨102, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨45, by decide⟩ ⟨102, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨46, by decide⟩ ⟨102, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨47, by decide⟩ ⟨102, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨48, by decide⟩ ⟨102, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨49, by decide⟩ ⟨102, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨50, by decide⟩ ⟨102, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨51, by decide⟩ ⟨102, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨52, by decide⟩ ⟨102, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨53, by decide⟩ ⟨102, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨54, by decide⟩ ⟨102, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_fix ⟨55, by decide⟩ ⟨102, by decide⟩ p hp j hj hq fz1_55_102 fz2_55_102
  · exact match_zero_fix ⟨56, by decide⟩ ⟨102, by decide⟩ p hp j hj hq fz1_56_102 fz2_56_102
  · exact match_zero_fix ⟨57, by decide⟩ ⟨102, by decide⟩ p hp j hj hq fz1_57_102 fz2_57_102
  · exact match_zero_fix ⟨58, by decide⟩ ⟨102, by decide⟩ p hp j hj hq fz1_58_102 fz2_58_102
  · exact match_zero_fix ⟨59, by decide⟩ ⟨102, by decide⟩ p hp j hj hq fz1_59_102 fz2_59_102
  · exact match_zero_fix ⟨60, by decide⟩ ⟨102, by decide⟩ p hp j hj hq fz1_60_102 fz2_60_102
  · exact match_zero_fix ⟨61, by decide⟩ ⟨102, by decide⟩ p hp j hj hq fz1_61_102 fz2_61_102
  · exact match_zero_fix ⟨62, by decide⟩ ⟨102, by decide⟩ p hp j hj hq fz1_62_102 fz2_62_102
  · exact match_zero_fix ⟨63, by decide⟩ ⟨102, by decide⟩ p hp j hj hq fz1_63_102 fz2_63_102
  · exact match_zero_fix ⟨64, by decide⟩ ⟨102, by decide⟩ p hp j hj hq fz1_64_102 fz2_64_102
  · exact match_zero_fix ⟨65, by decide⟩ ⟨102, by decide⟩ p hp j hj hq fz1_65_102 fz2_65_102
  · exact match_zero_fix ⟨66, by decide⟩ ⟨102, by decide⟩ p hp j hj hq fz1_66_102 fz2_66_102
  · exact match_zero_fix ⟨67, by decide⟩ ⟨102, by decide⟩ p hp j hj hq fz1_67_102 fz2_67_102
  · exact match_zero_fix ⟨68, by decide⟩ ⟨102, by decide⟩ p hp j hj hq fz1_68_102 fz2_68_102
  · exact match_zero_fix ⟨69, by decide⟩ ⟨102, by decide⟩ p hp j hj hq fz1_69_102 fz2_69_102
  · exact match_zero_fix ⟨70, by decide⟩ ⟨102, by decide⟩ p hp j hj hq fz1_70_102 fz2_70_102
  · exact match_zero_fix ⟨71, by decide⟩ ⟨102, by decide⟩ p hp j hj hq fz1_71_102 fz2_71_102
  · exact match_zero_fix ⟨72, by decide⟩ ⟨102, by decide⟩ p hp j hj hq fz1_72_102 fz2_72_102
  · exact match_zero_fix ⟨73, by decide⟩ ⟨102, by decide⟩ p hp j hj hq fz1_73_102 fz2_73_102
  · exact match_zero_fix ⟨74, by decide⟩ ⟨102, by decide⟩ p hp j hj hq fz1_74_102 fz2_74_102
  · exact match_zero_fix ⟨75, by decide⟩ ⟨102, by decide⟩ p hp j hj hq fz1_75_102 fz2_75_102
  · exact match_zero_fix ⟨76, by decide⟩ ⟨102, by decide⟩ p hp j hj hq fz1_76_102 fz2_76_102
  · exact match_zero_fix ⟨77, by decide⟩ ⟨102, by decide⟩ p hp j hj hq fz1_77_102 fz2_77_102
  · exact match_zero_fix ⟨78, by decide⟩ ⟨102, by decide⟩ p hp j hj hq fz1_78_102 fz2_78_102
  · exact match_zero_fix ⟨79, by decide⟩ ⟨102, by decide⟩ p hp j hj hq fz1_79_102 fz2_79_102
  · exact match_zero_fix ⟨80, by decide⟩ ⟨102, by decide⟩ p hp j hj hq fz1_80_102 fz2_80_102
  · exact match_zero_fix ⟨81, by decide⟩ ⟨102, by decide⟩ p hp j hj hq fz1_81_102 fz2_81_102
  · exact match_zero_fix ⟨82, by decide⟩ ⟨102, by decide⟩ p hp j hj hq fz1_82_102 fz2_82_102
  · exact match_zero_fix ⟨83, by decide⟩ ⟨102, by decide⟩ p hp j hj hq fz1_83_102 fz2_83_102
  · exact match_zero_fix ⟨84, by decide⟩ ⟨102, by decide⟩ p hp j hj hq fz1_84_102 fz2_84_102
  · exact match_zero_fix ⟨85, by decide⟩ ⟨102, by decide⟩ p hp j hj hq fz1_85_102 fz2_85_102
  · exact match_zero_fix ⟨86, by decide⟩ ⟨102, by decide⟩ p hp j hj hq fz1_86_102 fz2_86_102
  · exact match_zero_fix ⟨87, by decide⟩ ⟨102, by decide⟩ p hp j hj hq fz1_87_102 fz2_87_102
  · exact match_zero_fix ⟨88, by decide⟩ ⟨102, by decide⟩ p hp j hj hq fz1_88_102 fz2_88_102
  · exact match_zero_fix ⟨89, by decide⟩ ⟨102, by decide⟩ p hp j hj hq fz1_89_102 fz2_89_102
  · exact match_zero_fix ⟨90, by decide⟩ ⟨102, by decide⟩ p hp j hj hq fz1_90_102 fz2_90_102
  · exact match_zero_fix ⟨91, by decide⟩ ⟨102, by decide⟩ p hp j hj hq fz1_91_102 fz2_91_102
  · exact match_zero_fix ⟨92, by decide⟩ ⟨102, by decide⟩ p hp j hj hq fz1_92_102 fz2_92_102
  · exact match_zero_fix ⟨93, by decide⟩ ⟨102, by decide⟩ p hp j hj hq fz1_93_102 fz2_93_102
  · exact match_zero_fix ⟨94, by decide⟩ ⟨102, by decide⟩ p hp j hj hq fz1_94_102 fz2_94_102
  · exact match_zero_fix ⟨95, by decide⟩ ⟨102, by decide⟩ p hp j hj hq fz1_95_102 fz2_95_102
  · exact match_zero_fix ⟨96, by decide⟩ ⟨102, by decide⟩ p hp j hj hq fz1_96_102 fz2_96_102
  · exact match_zero_fix ⟨97, by decide⟩ ⟨102, by decide⟩ p hp j hj hq fz1_97_102 fz2_97_102
  · exact match_zero_fix ⟨98, by decide⟩ ⟨102, by decide⟩ p hp j hj hq fz1_98_102 fz2_98_102
  · exact match_zero_fix ⟨99, by decide⟩ ⟨102, by decide⟩ p hp j hj hq fz1_99_102 fz2_99_102
  · exact match_zero_fix ⟨100, by decide⟩ ⟨102, by decide⟩ p hp j hj hq fz1_100_102 fz2_100_102
  · exact match_zero_fix ⟨101, by decide⟩ ⟨102, by decide⟩ p hp j hj hq fz1_101_102 fz2_101_102
  · exact pair_102_102 p hp hrep j hj hq
  · exact match_zero_fix ⟨103, by decide⟩ ⟨102, by decide⟩ p hp j hj hq fz1_103_102 fz2_103_102
  · exact match_zero_fix ⟨104, by decide⟩ ⟨102, by decide⟩ p hp j hj hq fz1_104_102 fz2_104_102
  · exact match_zero_fix ⟨105, by decide⟩ ⟨102, by decide⟩ p hp j hj hq fz1_105_102 fz2_105_102
  · exact match_zero_fix ⟨106, by decide⟩ ⟨102, by decide⟩ p hp j hj hq fz1_106_102 fz2_106_102
  · exact match_zero_fix ⟨107, by decide⟩ ⟨102, by decide⟩ p hp j hj hq fz1_107_102 fz2_107_102
  · exact match_zero_fix ⟨108, by decide⟩ ⟨102, by decide⟩ p hp j hj hq fz1_108_102 fz2_108_102
  · exact match_zero_fix ⟨109, by decide⟩ ⟨102, by decide⟩ p hp j hj hq fz1_109_102 fz2_109_102
  · exact match_zero_fix ⟨110, by decide⟩ ⟨102, by decide⟩ p hp j hj hq fz1_110_102 fz2_110_102
  · exact match_zero_fix ⟨111, by decide⟩ ⟨102, by decide⟩ p hp j hj hq fz1_111_102 fz2_111_102
  · exact match_zero_fix ⟨112, by decide⟩ ⟨102, by decide⟩ p hp j hj hq fz1_112_102 fz2_112_102
  · exact match_zero_fix ⟨113, by decide⟩ ⟨102, by decide⟩ p hp j hj hq fz1_113_102 fz2_113_102
  · exact match_zero_fix ⟨114, by decide⟩ ⟨102, by decide⟩ p hp j hj hq fz1_114_102 fz2_114_102
  · exact match_zero_fix ⟨115, by decide⟩ ⟨102, by decide⟩ p hp j hj hq fz1_115_102 fz2_115_102
  · exact match_zero_fix ⟨116, by decide⟩ ⟨102, by decide⟩ p hp j hj hq fz1_116_102 fz2_116_102
  · exact match_zero_fix ⟨117, by decide⟩ ⟨102, by decide⟩ p hp j hj hq fz1_117_102 fz2_117_102
  · exact pair_118_102 p hp hrep j hj hq
  · exact match_zero_fix ⟨119, by decide⟩ ⟨102, by decide⟩ p hp j hj hq fz1_119_102 fz2_119_102
  · exact match_zero_fix ⟨120, by decide⟩ ⟨102, by decide⟩ p hp j hj hq fz1_120_102 fz2_120_102
  · exact match_zero_fix ⟨121, by decide⟩ ⟨102, by decide⟩ p hp j hj hq fz1_121_102 fz2_121_102
  · exact match_zero_fix ⟨122, by decide⟩ ⟨102, by decide⟩ p hp j hj hq fz1_122_102 fz2_122_102
  · exact match_zero_fix ⟨123, by decide⟩ ⟨102, by decide⟩ p hp j hj hq fz1_123_102 fz2_123_102
  · exact match_zero_fix ⟨124, by decide⟩ ⟨102, by decide⟩ p hp j hj hq fz1_124_102 fz2_124_102
  · exact pair_125_102 p hp hrep j hj hq
  · exact match_zero_fix ⟨126, by decide⟩ ⟨102, by decide⟩ p hp j hj hq fz1_126_102 fz2_126_102
  · exact pair_127_102 p hp hrep j hj hq
  · exact match_zero_fix ⟨128, by decide⟩ ⟨102, by decide⟩ p hp j hj hq fz1_128_102 fz2_128_102
  · exact match_zero_fix ⟨129, by decide⟩ ⟨102, by decide⟩ p hp j hj hq fz1_129_102 fz2_129_102
  · exact match_zero_fix ⟨130, by decide⟩ ⟨102, by decide⟩ p hp j hj hq fz1_130_102 fz2_130_102
  · exact match_zero_fix ⟨131, by decide⟩ ⟨102, by decide⟩ p hp j hj hq fz1_131_102 fz2_131_102
  · exact match_zero_fix ⟨132, by decide⟩ ⟨102, by decide⟩ p hp j hj hq fz1_132_102 fz2_132_102
  · exact match_zero_fix ⟨133, by decide⟩ ⟨102, by decide⟩ p hp j hj hq fz1_133_102 fz2_133_102
  · exact pair_134_102 p hp hrep j hj hq
  · exact match_zero_fix ⟨135, by decide⟩ ⟨102, by decide⟩ p hp j hj hq fz1_135_102 fz2_135_102
  · exact pair_136_102 p hp hrep j hj hq
  · exact match_zero_fix ⟨137, by decide⟩ ⟨102, by decide⟩ p hp j hj hq fz1_137_102 fz2_137_102
  · exact match_zero_fix ⟨138, by decide⟩ ⟨102, by decide⟩ p hp j hj hq fz1_138_102 fz2_138_102
  · exact match_zero_fix ⟨139, by decide⟩ ⟨102, by decide⟩ p hp j hj hq fz1_139_102 fz2_139_102
  · exact match_zero_fix ⟨140, by decide⟩ ⟨102, by decide⟩ p hp j hj hq fz1_140_102 fz2_140_102
  · exact match_zero_fix ⟨141, by decide⟩ ⟨102, by decide⟩ p hp j hj hq fz1_141_102 fz2_141_102
  · exact match_zero_fix ⟨142, by decide⟩ ⟨102, by decide⟩ p hp j hj hq fz1_142_102 fz2_142_102
  · exact match_zero_fix ⟨143, by decide⟩ ⟨102, by decide⟩ p hp j hj hq fz1_143_102 fz2_143_102
  · exact pair_144_102 p hp hrep j hj hq
  · exact match_zero_fix ⟨145, by decide⟩ ⟨102, by decide⟩ p hp j hj hq fz1_145_102 fz2_145_102
  · exact match_zero_fix ⟨146, by decide⟩ ⟨102, by decide⟩ p hp j hj hq fz1_146_102 fz2_146_102
  · exact pair_147_102 p hp hrep j hj hq

theorem master_103 (p : Nat) (hp : p < (Q2.transData.getD 103 []).length)
    (hrep : (Q2.cosetIsRep.getD 103 []).getD p false = true)
    (rK : Fin 148) (j : Nat) (hj : j < (repChars.getD rK.val []).length)
    (hq : (normIsRep.getD rK.val []).getD j false = true) :
    species (Q2.reps (⟨103, by decide⟩ : Fin 148)) (colE2 ⟨103, by decide⟩ p hp)
        (rowE2 rK j hj hq)
      = species (reps (⟨103, by decide⟩ : Fin 148))
        (colE1 ⟨103, by decide⟩ p (transLenTr ⟨103, by decide⟩ p hp)) (rowE1 rK j hj) := by
  rcases rK with ⟨nK, hnK⟩; interval_cases nK
  · exact match_zero_len ⟨0, by decide⟩ ⟨103, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨1, by decide⟩ ⟨103, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨2, by decide⟩ ⟨103, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨3, by decide⟩ ⟨103, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨4, by decide⟩ ⟨103, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨5, by decide⟩ ⟨103, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨6, by decide⟩ ⟨103, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨7, by decide⟩ ⟨103, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨8, by decide⟩ ⟨103, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨9, by decide⟩ ⟨103, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨10, by decide⟩ ⟨103, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨11, by decide⟩ ⟨103, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨12, by decide⟩ ⟨103, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨13, by decide⟩ ⟨103, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨14, by decide⟩ ⟨103, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨15, by decide⟩ ⟨103, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨16, by decide⟩ ⟨103, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨17, by decide⟩ ⟨103, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨18, by decide⟩ ⟨103, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨19, by decide⟩ ⟨103, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨20, by decide⟩ ⟨103, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨21, by decide⟩ ⟨103, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨22, by decide⟩ ⟨103, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨23, by decide⟩ ⟨103, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨24, by decide⟩ ⟨103, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨25, by decide⟩ ⟨103, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨26, by decide⟩ ⟨103, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨27, by decide⟩ ⟨103, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨28, by decide⟩ ⟨103, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨29, by decide⟩ ⟨103, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨30, by decide⟩ ⟨103, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨31, by decide⟩ ⟨103, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨32, by decide⟩ ⟨103, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨33, by decide⟩ ⟨103, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨34, by decide⟩ ⟨103, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨35, by decide⟩ ⟨103, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨36, by decide⟩ ⟨103, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨37, by decide⟩ ⟨103, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨38, by decide⟩ ⟨103, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨39, by decide⟩ ⟨103, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨40, by decide⟩ ⟨103, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨41, by decide⟩ ⟨103, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨42, by decide⟩ ⟨103, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨43, by decide⟩ ⟨103, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨44, by decide⟩ ⟨103, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨45, by decide⟩ ⟨103, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨46, by decide⟩ ⟨103, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨47, by decide⟩ ⟨103, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨48, by decide⟩ ⟨103, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨49, by decide⟩ ⟨103, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨50, by decide⟩ ⟨103, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨51, by decide⟩ ⟨103, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨52, by decide⟩ ⟨103, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨53, by decide⟩ ⟨103, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨54, by decide⟩ ⟨103, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_fix ⟨55, by decide⟩ ⟨103, by decide⟩ p hp j hj hq fz1_55_103 fz2_55_103
  · exact match_zero_fix ⟨56, by decide⟩ ⟨103, by decide⟩ p hp j hj hq fz1_56_103 fz2_56_103
  · exact match_zero_fix ⟨57, by decide⟩ ⟨103, by decide⟩ p hp j hj hq fz1_57_103 fz2_57_103
  · exact match_zero_fix ⟨58, by decide⟩ ⟨103, by decide⟩ p hp j hj hq fz1_58_103 fz2_58_103
  · exact match_zero_fix ⟨59, by decide⟩ ⟨103, by decide⟩ p hp j hj hq fz1_59_103 fz2_59_103
  · exact match_zero_fix ⟨60, by decide⟩ ⟨103, by decide⟩ p hp j hj hq fz1_60_103 fz2_60_103
  · exact match_zero_fix ⟨61, by decide⟩ ⟨103, by decide⟩ p hp j hj hq fz1_61_103 fz2_61_103
  · exact match_zero_fix ⟨62, by decide⟩ ⟨103, by decide⟩ p hp j hj hq fz1_62_103 fz2_62_103
  · exact match_zero_fix ⟨63, by decide⟩ ⟨103, by decide⟩ p hp j hj hq fz1_63_103 fz2_63_103
  · exact match_zero_fix ⟨64, by decide⟩ ⟨103, by decide⟩ p hp j hj hq fz1_64_103 fz2_64_103
  · exact match_zero_fix ⟨65, by decide⟩ ⟨103, by decide⟩ p hp j hj hq fz1_65_103 fz2_65_103
  · exact match_zero_fix ⟨66, by decide⟩ ⟨103, by decide⟩ p hp j hj hq fz1_66_103 fz2_66_103
  · exact match_zero_fix ⟨67, by decide⟩ ⟨103, by decide⟩ p hp j hj hq fz1_67_103 fz2_67_103
  · exact match_zero_fix ⟨68, by decide⟩ ⟨103, by decide⟩ p hp j hj hq fz1_68_103 fz2_68_103
  · exact match_zero_fix ⟨69, by decide⟩ ⟨103, by decide⟩ p hp j hj hq fz1_69_103 fz2_69_103
  · exact match_zero_fix ⟨70, by decide⟩ ⟨103, by decide⟩ p hp j hj hq fz1_70_103 fz2_70_103
  · exact match_zero_fix ⟨71, by decide⟩ ⟨103, by decide⟩ p hp j hj hq fz1_71_103 fz2_71_103
  · exact match_zero_fix ⟨72, by decide⟩ ⟨103, by decide⟩ p hp j hj hq fz1_72_103 fz2_72_103
  · exact match_zero_fix ⟨73, by decide⟩ ⟨103, by decide⟩ p hp j hj hq fz1_73_103 fz2_73_103
  · exact match_zero_fix ⟨74, by decide⟩ ⟨103, by decide⟩ p hp j hj hq fz1_74_103 fz2_74_103
  · exact match_zero_fix ⟨75, by decide⟩ ⟨103, by decide⟩ p hp j hj hq fz1_75_103 fz2_75_103
  · exact match_zero_fix ⟨76, by decide⟩ ⟨103, by decide⟩ p hp j hj hq fz1_76_103 fz2_76_103
  · exact match_zero_fix ⟨77, by decide⟩ ⟨103, by decide⟩ p hp j hj hq fz1_77_103 fz2_77_103
  · exact match_zero_fix ⟨78, by decide⟩ ⟨103, by decide⟩ p hp j hj hq fz1_78_103 fz2_78_103
  · exact match_zero_fix ⟨79, by decide⟩ ⟨103, by decide⟩ p hp j hj hq fz1_79_103 fz2_79_103
  · exact match_zero_fix ⟨80, by decide⟩ ⟨103, by decide⟩ p hp j hj hq fz1_80_103 fz2_80_103
  · exact match_zero_fix ⟨81, by decide⟩ ⟨103, by decide⟩ p hp j hj hq fz1_81_103 fz2_81_103
  · exact match_zero_fix ⟨82, by decide⟩ ⟨103, by decide⟩ p hp j hj hq fz1_82_103 fz2_82_103
  · exact match_zero_fix ⟨83, by decide⟩ ⟨103, by decide⟩ p hp j hj hq fz1_83_103 fz2_83_103
  · exact match_zero_fix ⟨84, by decide⟩ ⟨103, by decide⟩ p hp j hj hq fz1_84_103 fz2_84_103
  · exact match_zero_fix ⟨85, by decide⟩ ⟨103, by decide⟩ p hp j hj hq fz1_85_103 fz2_85_103
  · exact match_zero_fix ⟨86, by decide⟩ ⟨103, by decide⟩ p hp j hj hq fz1_86_103 fz2_86_103
  · exact match_zero_fix ⟨87, by decide⟩ ⟨103, by decide⟩ p hp j hj hq fz1_87_103 fz2_87_103
  · exact match_zero_fix ⟨88, by decide⟩ ⟨103, by decide⟩ p hp j hj hq fz1_88_103 fz2_88_103
  · exact match_zero_fix ⟨89, by decide⟩ ⟨103, by decide⟩ p hp j hj hq fz1_89_103 fz2_89_103
  · exact match_zero_fix ⟨90, by decide⟩ ⟨103, by decide⟩ p hp j hj hq fz1_90_103 fz2_90_103
  · exact match_zero_fix ⟨91, by decide⟩ ⟨103, by decide⟩ p hp j hj hq fz1_91_103 fz2_91_103
  · exact match_zero_fix ⟨92, by decide⟩ ⟨103, by decide⟩ p hp j hj hq fz1_92_103 fz2_92_103
  · exact match_zero_fix ⟨93, by decide⟩ ⟨103, by decide⟩ p hp j hj hq fz1_93_103 fz2_93_103
  · exact match_zero_fix ⟨94, by decide⟩ ⟨103, by decide⟩ p hp j hj hq fz1_94_103 fz2_94_103
  · exact match_zero_fix ⟨95, by decide⟩ ⟨103, by decide⟩ p hp j hj hq fz1_95_103 fz2_95_103
  · exact match_zero_fix ⟨96, by decide⟩ ⟨103, by decide⟩ p hp j hj hq fz1_96_103 fz2_96_103
  · exact match_zero_fix ⟨97, by decide⟩ ⟨103, by decide⟩ p hp j hj hq fz1_97_103 fz2_97_103
  · exact match_zero_fix ⟨98, by decide⟩ ⟨103, by decide⟩ p hp j hj hq fz1_98_103 fz2_98_103
  · exact match_zero_fix ⟨99, by decide⟩ ⟨103, by decide⟩ p hp j hj hq fz1_99_103 fz2_99_103
  · exact match_zero_fix ⟨100, by decide⟩ ⟨103, by decide⟩ p hp j hj hq fz1_100_103 fz2_100_103
  · exact match_zero_fix ⟨101, by decide⟩ ⟨103, by decide⟩ p hp j hj hq fz1_101_103 fz2_101_103
  · exact match_zero_fix ⟨102, by decide⟩ ⟨103, by decide⟩ p hp j hj hq fz1_102_103 fz2_102_103
  · exact pair_103_103 p hp hrep j hj hq
  · exact match_zero_fix ⟨104, by decide⟩ ⟨103, by decide⟩ p hp j hj hq fz1_104_103 fz2_104_103
  · exact match_zero_fix ⟨105, by decide⟩ ⟨103, by decide⟩ p hp j hj hq fz1_105_103 fz2_105_103
  · exact match_zero_fix ⟨106, by decide⟩ ⟨103, by decide⟩ p hp j hj hq fz1_106_103 fz2_106_103
  · exact match_zero_fix ⟨107, by decide⟩ ⟨103, by decide⟩ p hp j hj hq fz1_107_103 fz2_107_103
  · exact match_zero_fix ⟨108, by decide⟩ ⟨103, by decide⟩ p hp j hj hq fz1_108_103 fz2_108_103
  · exact match_zero_fix ⟨109, by decide⟩ ⟨103, by decide⟩ p hp j hj hq fz1_109_103 fz2_109_103
  · exact match_zero_fix ⟨110, by decide⟩ ⟨103, by decide⟩ p hp j hj hq fz1_110_103 fz2_110_103
  · exact match_zero_fix ⟨111, by decide⟩ ⟨103, by decide⟩ p hp j hj hq fz1_111_103 fz2_111_103
  · exact match_zero_fix ⟨112, by decide⟩ ⟨103, by decide⟩ p hp j hj hq fz1_112_103 fz2_112_103
  · exact match_zero_fix ⟨113, by decide⟩ ⟨103, by decide⟩ p hp j hj hq fz1_113_103 fz2_113_103
  · exact match_zero_fix ⟨114, by decide⟩ ⟨103, by decide⟩ p hp j hj hq fz1_114_103 fz2_114_103
  · exact match_zero_fix ⟨115, by decide⟩ ⟨103, by decide⟩ p hp j hj hq fz1_115_103 fz2_115_103
  · exact match_zero_fix ⟨116, by decide⟩ ⟨103, by decide⟩ p hp j hj hq fz1_116_103 fz2_116_103
  · exact match_zero_fix ⟨117, by decide⟩ ⟨103, by decide⟩ p hp j hj hq fz1_117_103 fz2_117_103
  · exact match_zero_fix ⟨118, by decide⟩ ⟨103, by decide⟩ p hp j hj hq fz1_118_103 fz2_118_103
  · exact pair_119_103 p hp hrep j hj hq
  · exact match_zero_fix ⟨120, by decide⟩ ⟨103, by decide⟩ p hp j hj hq fz1_120_103 fz2_120_103
  · exact pair_121_103 p hp hrep j hj hq
  · exact match_zero_fix ⟨122, by decide⟩ ⟨103, by decide⟩ p hp j hj hq fz1_122_103 fz2_122_103
  · exact match_zero_fix ⟨123, by decide⟩ ⟨103, by decide⟩ p hp j hj hq fz1_123_103 fz2_123_103
  · exact match_zero_fix ⟨124, by decide⟩ ⟨103, by decide⟩ p hp j hj hq fz1_124_103 fz2_124_103
  · exact match_zero_fix ⟨125, by decide⟩ ⟨103, by decide⟩ p hp j hj hq fz1_125_103 fz2_125_103
  · exact match_zero_fix ⟨126, by decide⟩ ⟨103, by decide⟩ p hp j hj hq fz1_126_103 fz2_126_103
  · exact match_zero_fix ⟨127, by decide⟩ ⟨103, by decide⟩ p hp j hj hq fz1_127_103 fz2_127_103
  · exact pair_128_103 p hp hrep j hj hq
  · exact match_zero_fix ⟨129, by decide⟩ ⟨103, by decide⟩ p hp j hj hq fz1_129_103 fz2_129_103
  · exact match_zero_fix ⟨130, by decide⟩ ⟨103, by decide⟩ p hp j hj hq fz1_130_103 fz2_130_103
  · exact match_zero_fix ⟨131, by decide⟩ ⟨103, by decide⟩ p hp j hj hq fz1_131_103 fz2_131_103
  · exact match_zero_fix ⟨132, by decide⟩ ⟨103, by decide⟩ p hp j hj hq fz1_132_103 fz2_132_103
  · exact match_zero_fix ⟨133, by decide⟩ ⟨103, by decide⟩ p hp j hj hq fz1_133_103 fz2_133_103
  · exact match_zero_fix ⟨134, by decide⟩ ⟨103, by decide⟩ p hp j hj hq fz1_134_103 fz2_134_103
  · exact pair_135_103 p hp hrep j hj hq
  · exact match_zero_fix ⟨136, by decide⟩ ⟨103, by decide⟩ p hp j hj hq fz1_136_103 fz2_136_103
  · exact pair_137_103 p hp hrep j hj hq
  · exact match_zero_fix ⟨138, by decide⟩ ⟨103, by decide⟩ p hp j hj hq fz1_138_103 fz2_138_103
  · exact match_zero_fix ⟨139, by decide⟩ ⟨103, by decide⟩ p hp j hj hq fz1_139_103 fz2_139_103
  · exact match_zero_fix ⟨140, by decide⟩ ⟨103, by decide⟩ p hp j hj hq fz1_140_103 fz2_140_103
  · exact match_zero_fix ⟨141, by decide⟩ ⟨103, by decide⟩ p hp j hj hq fz1_141_103 fz2_141_103
  · exact match_zero_fix ⟨142, by decide⟩ ⟨103, by decide⟩ p hp j hj hq fz1_142_103 fz2_142_103
  · exact match_zero_fix ⟨143, by decide⟩ ⟨103, by decide⟩ p hp j hj hq fz1_143_103 fz2_143_103
  · exact pair_144_103 p hp hrep j hj hq
  · exact match_zero_fix ⟨145, by decide⟩ ⟨103, by decide⟩ p hp j hj hq fz1_145_103 fz2_145_103
  · exact match_zero_fix ⟨146, by decide⟩ ⟨103, by decide⟩ p hp j hj hq fz1_146_103 fz2_146_103
  · exact pair_147_103 p hp hrep j hj hq

end LeanDring.P5Presentation
