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

/-! # Stage-5 per-column-class master theorems, chunk 13 (auto-emitted).  -/

namespace LeanDring.P5Presentation

open MulAction Finset LeanDring.DRing LeanDring.MonGSet

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.style.longLine false

theorem master_104 (p : Nat) (hp : p < (Q2.transData.getD 104 []).length)
    (hrep : (Q2.cosetIsRep.getD 104 []).getD p false = true)
    (rK : Fin 148) (j : Nat) (hj : j < (repChars.getD rK.val []).length)
    (hq : (normIsRep.getD rK.val []).getD j false = true) :
    species (Q2.reps (⟨104, by decide⟩ : Fin 148)) (colE2 ⟨104, by decide⟩ p hp)
        (rowE2 rK j hj hq)
      = species (reps (⟨104, by decide⟩ : Fin 148))
        (colE1 ⟨104, by decide⟩ p (transLenTr ⟨104, by decide⟩ p hp)) (rowE1 rK j hj) := by
  rcases rK with ⟨nK, hnK⟩; interval_cases nK
  · exact match_zero_len ⟨0, by decide⟩ ⟨104, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨1, by decide⟩ ⟨104, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨2, by decide⟩ ⟨104, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨3, by decide⟩ ⟨104, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨4, by decide⟩ ⟨104, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨5, by decide⟩ ⟨104, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨6, by decide⟩ ⟨104, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨7, by decide⟩ ⟨104, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨8, by decide⟩ ⟨104, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨9, by decide⟩ ⟨104, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨10, by decide⟩ ⟨104, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨11, by decide⟩ ⟨104, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨12, by decide⟩ ⟨104, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨13, by decide⟩ ⟨104, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨14, by decide⟩ ⟨104, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨15, by decide⟩ ⟨104, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨16, by decide⟩ ⟨104, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨17, by decide⟩ ⟨104, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨18, by decide⟩ ⟨104, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨19, by decide⟩ ⟨104, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨20, by decide⟩ ⟨104, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨21, by decide⟩ ⟨104, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨22, by decide⟩ ⟨104, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨23, by decide⟩ ⟨104, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨24, by decide⟩ ⟨104, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨25, by decide⟩ ⟨104, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨26, by decide⟩ ⟨104, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨27, by decide⟩ ⟨104, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨28, by decide⟩ ⟨104, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨29, by decide⟩ ⟨104, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨30, by decide⟩ ⟨104, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨31, by decide⟩ ⟨104, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨32, by decide⟩ ⟨104, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨33, by decide⟩ ⟨104, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨34, by decide⟩ ⟨104, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨35, by decide⟩ ⟨104, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨36, by decide⟩ ⟨104, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨37, by decide⟩ ⟨104, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨38, by decide⟩ ⟨104, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨39, by decide⟩ ⟨104, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨40, by decide⟩ ⟨104, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨41, by decide⟩ ⟨104, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨42, by decide⟩ ⟨104, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨43, by decide⟩ ⟨104, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨44, by decide⟩ ⟨104, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨45, by decide⟩ ⟨104, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨46, by decide⟩ ⟨104, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨47, by decide⟩ ⟨104, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨48, by decide⟩ ⟨104, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨49, by decide⟩ ⟨104, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨50, by decide⟩ ⟨104, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨51, by decide⟩ ⟨104, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨52, by decide⟩ ⟨104, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨53, by decide⟩ ⟨104, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨54, by decide⟩ ⟨104, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_fix ⟨55, by decide⟩ ⟨104, by decide⟩ p hp j hj hq fz1_55_104 fz2_55_104
  · exact match_zero_fix ⟨56, by decide⟩ ⟨104, by decide⟩ p hp j hj hq fz1_56_104 fz2_56_104
  · exact match_zero_fix ⟨57, by decide⟩ ⟨104, by decide⟩ p hp j hj hq fz1_57_104 fz2_57_104
  · exact match_zero_fix ⟨58, by decide⟩ ⟨104, by decide⟩ p hp j hj hq fz1_58_104 fz2_58_104
  · exact match_zero_fix ⟨59, by decide⟩ ⟨104, by decide⟩ p hp j hj hq fz1_59_104 fz2_59_104
  · exact match_zero_fix ⟨60, by decide⟩ ⟨104, by decide⟩ p hp j hj hq fz1_60_104 fz2_60_104
  · exact match_zero_fix ⟨61, by decide⟩ ⟨104, by decide⟩ p hp j hj hq fz1_61_104 fz2_61_104
  · exact match_zero_fix ⟨62, by decide⟩ ⟨104, by decide⟩ p hp j hj hq fz1_62_104 fz2_62_104
  · exact match_zero_fix ⟨63, by decide⟩ ⟨104, by decide⟩ p hp j hj hq fz1_63_104 fz2_63_104
  · exact match_zero_fix ⟨64, by decide⟩ ⟨104, by decide⟩ p hp j hj hq fz1_64_104 fz2_64_104
  · exact match_zero_fix ⟨65, by decide⟩ ⟨104, by decide⟩ p hp j hj hq fz1_65_104 fz2_65_104
  · exact match_zero_fix ⟨66, by decide⟩ ⟨104, by decide⟩ p hp j hj hq fz1_66_104 fz2_66_104
  · exact match_zero_fix ⟨67, by decide⟩ ⟨104, by decide⟩ p hp j hj hq fz1_67_104 fz2_67_104
  · exact match_zero_fix ⟨68, by decide⟩ ⟨104, by decide⟩ p hp j hj hq fz1_68_104 fz2_68_104
  · exact match_zero_fix ⟨69, by decide⟩ ⟨104, by decide⟩ p hp j hj hq fz1_69_104 fz2_69_104
  · exact match_zero_fix ⟨70, by decide⟩ ⟨104, by decide⟩ p hp j hj hq fz1_70_104 fz2_70_104
  · exact match_zero_fix ⟨71, by decide⟩ ⟨104, by decide⟩ p hp j hj hq fz1_71_104 fz2_71_104
  · exact match_zero_fix ⟨72, by decide⟩ ⟨104, by decide⟩ p hp j hj hq fz1_72_104 fz2_72_104
  · exact match_zero_fix ⟨73, by decide⟩ ⟨104, by decide⟩ p hp j hj hq fz1_73_104 fz2_73_104
  · exact match_zero_fix ⟨74, by decide⟩ ⟨104, by decide⟩ p hp j hj hq fz1_74_104 fz2_74_104
  · exact match_zero_fix ⟨75, by decide⟩ ⟨104, by decide⟩ p hp j hj hq fz1_75_104 fz2_75_104
  · exact match_zero_fix ⟨76, by decide⟩ ⟨104, by decide⟩ p hp j hj hq fz1_76_104 fz2_76_104
  · exact match_zero_fix ⟨77, by decide⟩ ⟨104, by decide⟩ p hp j hj hq fz1_77_104 fz2_77_104
  · exact match_zero_fix ⟨78, by decide⟩ ⟨104, by decide⟩ p hp j hj hq fz1_78_104 fz2_78_104
  · exact match_zero_fix ⟨79, by decide⟩ ⟨104, by decide⟩ p hp j hj hq fz1_79_104 fz2_79_104
  · exact match_zero_fix ⟨80, by decide⟩ ⟨104, by decide⟩ p hp j hj hq fz1_80_104 fz2_80_104
  · exact match_zero_fix ⟨81, by decide⟩ ⟨104, by decide⟩ p hp j hj hq fz1_81_104 fz2_81_104
  · exact match_zero_fix ⟨82, by decide⟩ ⟨104, by decide⟩ p hp j hj hq fz1_82_104 fz2_82_104
  · exact match_zero_fix ⟨83, by decide⟩ ⟨104, by decide⟩ p hp j hj hq fz1_83_104 fz2_83_104
  · exact match_zero_fix ⟨84, by decide⟩ ⟨104, by decide⟩ p hp j hj hq fz1_84_104 fz2_84_104
  · exact match_zero_fix ⟨85, by decide⟩ ⟨104, by decide⟩ p hp j hj hq fz1_85_104 fz2_85_104
  · exact match_zero_fix ⟨86, by decide⟩ ⟨104, by decide⟩ p hp j hj hq fz1_86_104 fz2_86_104
  · exact match_zero_fix ⟨87, by decide⟩ ⟨104, by decide⟩ p hp j hj hq fz1_87_104 fz2_87_104
  · exact match_zero_fix ⟨88, by decide⟩ ⟨104, by decide⟩ p hp j hj hq fz1_88_104 fz2_88_104
  · exact match_zero_fix ⟨89, by decide⟩ ⟨104, by decide⟩ p hp j hj hq fz1_89_104 fz2_89_104
  · exact match_zero_fix ⟨90, by decide⟩ ⟨104, by decide⟩ p hp j hj hq fz1_90_104 fz2_90_104
  · exact match_zero_fix ⟨91, by decide⟩ ⟨104, by decide⟩ p hp j hj hq fz1_91_104 fz2_91_104
  · exact match_zero_fix ⟨92, by decide⟩ ⟨104, by decide⟩ p hp j hj hq fz1_92_104 fz2_92_104
  · exact match_zero_fix ⟨93, by decide⟩ ⟨104, by decide⟩ p hp j hj hq fz1_93_104 fz2_93_104
  · exact match_zero_fix ⟨94, by decide⟩ ⟨104, by decide⟩ p hp j hj hq fz1_94_104 fz2_94_104
  · exact match_zero_fix ⟨95, by decide⟩ ⟨104, by decide⟩ p hp j hj hq fz1_95_104 fz2_95_104
  · exact match_zero_fix ⟨96, by decide⟩ ⟨104, by decide⟩ p hp j hj hq fz1_96_104 fz2_96_104
  · exact match_zero_fix ⟨97, by decide⟩ ⟨104, by decide⟩ p hp j hj hq fz1_97_104 fz2_97_104
  · exact match_zero_fix ⟨98, by decide⟩ ⟨104, by decide⟩ p hp j hj hq fz1_98_104 fz2_98_104
  · exact match_zero_fix ⟨99, by decide⟩ ⟨104, by decide⟩ p hp j hj hq fz1_99_104 fz2_99_104
  · exact match_zero_fix ⟨100, by decide⟩ ⟨104, by decide⟩ p hp j hj hq fz1_100_104 fz2_100_104
  · exact match_zero_fix ⟨101, by decide⟩ ⟨104, by decide⟩ p hp j hj hq fz1_101_104 fz2_101_104
  · exact match_zero_fix ⟨102, by decide⟩ ⟨104, by decide⟩ p hp j hj hq fz1_102_104 fz2_102_104
  · exact match_zero_fix ⟨103, by decide⟩ ⟨104, by decide⟩ p hp j hj hq fz1_103_104 fz2_103_104
  · exact pair_104_104 p hp hrep j hj hq
  · exact match_zero_fix ⟨105, by decide⟩ ⟨104, by decide⟩ p hp j hj hq fz1_105_104 fz2_105_104
  · exact match_zero_fix ⟨106, by decide⟩ ⟨104, by decide⟩ p hp j hj hq fz1_106_104 fz2_106_104
  · exact match_zero_fix ⟨107, by decide⟩ ⟨104, by decide⟩ p hp j hj hq fz1_107_104 fz2_107_104
  · exact match_zero_fix ⟨108, by decide⟩ ⟨104, by decide⟩ p hp j hj hq fz1_108_104 fz2_108_104
  · exact match_zero_fix ⟨109, by decide⟩ ⟨104, by decide⟩ p hp j hj hq fz1_109_104 fz2_109_104
  · exact match_zero_fix ⟨110, by decide⟩ ⟨104, by decide⟩ p hp j hj hq fz1_110_104 fz2_110_104
  · exact match_zero_fix ⟨111, by decide⟩ ⟨104, by decide⟩ p hp j hj hq fz1_111_104 fz2_111_104
  · exact match_zero_fix ⟨112, by decide⟩ ⟨104, by decide⟩ p hp j hj hq fz1_112_104 fz2_112_104
  · exact match_zero_fix ⟨113, by decide⟩ ⟨104, by decide⟩ p hp j hj hq fz1_113_104 fz2_113_104
  · exact match_zero_fix ⟨114, by decide⟩ ⟨104, by decide⟩ p hp j hj hq fz1_114_104 fz2_114_104
  · exact match_zero_fix ⟨115, by decide⟩ ⟨104, by decide⟩ p hp j hj hq fz1_115_104 fz2_115_104
  · exact match_zero_fix ⟨116, by decide⟩ ⟨104, by decide⟩ p hp j hj hq fz1_116_104 fz2_116_104
  · exact match_zero_fix ⟨117, by decide⟩ ⟨104, by decide⟩ p hp j hj hq fz1_117_104 fz2_117_104
  · exact match_zero_fix ⟨118, by decide⟩ ⟨104, by decide⟩ p hp j hj hq fz1_118_104 fz2_118_104
  · exact match_zero_fix ⟨119, by decide⟩ ⟨104, by decide⟩ p hp j hj hq fz1_119_104 fz2_119_104
  · exact pair_120_104 p hp hrep j hj hq
  · exact match_zero_fix ⟨121, by decide⟩ ⟨104, by decide⟩ p hp j hj hq fz1_121_104 fz2_121_104
  · exact pair_122_104 p hp hrep j hj hq
  · exact match_zero_fix ⟨123, by decide⟩ ⟨104, by decide⟩ p hp j hj hq fz1_123_104 fz2_123_104
  · exact match_zero_fix ⟨124, by decide⟩ ⟨104, by decide⟩ p hp j hj hq fz1_124_104 fz2_124_104
  · exact match_zero_fix ⟨125, by decide⟩ ⟨104, by decide⟩ p hp j hj hq fz1_125_104 fz2_125_104
  · exact match_zero_fix ⟨126, by decide⟩ ⟨104, by decide⟩ p hp j hj hq fz1_126_104 fz2_126_104
  · exact match_zero_fix ⟨127, by decide⟩ ⟨104, by decide⟩ p hp j hj hq fz1_127_104 fz2_127_104
  · exact match_zero_fix ⟨128, by decide⟩ ⟨104, by decide⟩ p hp j hj hq fz1_128_104 fz2_128_104
  · exact pair_129_104 p hp hrep j hj hq
  · exact match_zero_fix ⟨130, by decide⟩ ⟨104, by decide⟩ p hp j hj hq fz1_130_104 fz2_130_104
  · exact pair_131_104 p hp hrep j hj hq
  · exact match_zero_fix ⟨132, by decide⟩ ⟨104, by decide⟩ p hp j hj hq fz1_132_104 fz2_132_104
  · exact match_zero_fix ⟨133, by decide⟩ ⟨104, by decide⟩ p hp j hj hq fz1_133_104 fz2_133_104
  · exact match_zero_fix ⟨134, by decide⟩ ⟨104, by decide⟩ p hp j hj hq fz1_134_104 fz2_134_104
  · exact match_zero_fix ⟨135, by decide⟩ ⟨104, by decide⟩ p hp j hj hq fz1_135_104 fz2_135_104
  · exact match_zero_fix ⟨136, by decide⟩ ⟨104, by decide⟩ p hp j hj hq fz1_136_104 fz2_136_104
  · exact match_zero_fix ⟨137, by decide⟩ ⟨104, by decide⟩ p hp j hj hq fz1_137_104 fz2_137_104
  · exact pair_138_104 p hp hrep j hj hq
  · exact match_zero_fix ⟨139, by decide⟩ ⟨104, by decide⟩ p hp j hj hq fz1_139_104 fz2_139_104
  · exact match_zero_fix ⟨140, by decide⟩ ⟨104, by decide⟩ p hp j hj hq fz1_140_104 fz2_140_104
  · exact match_zero_fix ⟨141, by decide⟩ ⟨104, by decide⟩ p hp j hj hq fz1_141_104 fz2_141_104
  · exact match_zero_fix ⟨142, by decide⟩ ⟨104, by decide⟩ p hp j hj hq fz1_142_104 fz2_142_104
  · exact match_zero_fix ⟨143, by decide⟩ ⟨104, by decide⟩ p hp j hj hq fz1_143_104 fz2_143_104
  · exact pair_144_104 p hp hrep j hj hq
  · exact match_zero_fix ⟨145, by decide⟩ ⟨104, by decide⟩ p hp j hj hq fz1_145_104 fz2_145_104
  · exact match_zero_fix ⟨146, by decide⟩ ⟨104, by decide⟩ p hp j hj hq fz1_146_104 fz2_146_104
  · exact pair_147_104 p hp hrep j hj hq

theorem master_105 (p : Nat) (hp : p < (Q2.transData.getD 105 []).length)
    (hrep : (Q2.cosetIsRep.getD 105 []).getD p false = true)
    (rK : Fin 148) (j : Nat) (hj : j < (repChars.getD rK.val []).length)
    (hq : (normIsRep.getD rK.val []).getD j false = true) :
    species (Q2.reps (⟨105, by decide⟩ : Fin 148)) (colE2 ⟨105, by decide⟩ p hp)
        (rowE2 rK j hj hq)
      = species (reps (⟨105, by decide⟩ : Fin 148))
        (colE1 ⟨105, by decide⟩ p (transLenTr ⟨105, by decide⟩ p hp)) (rowE1 rK j hj) := by
  rcases rK with ⟨nK, hnK⟩; interval_cases nK
  · exact match_zero_len ⟨0, by decide⟩ ⟨105, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨1, by decide⟩ ⟨105, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨2, by decide⟩ ⟨105, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨3, by decide⟩ ⟨105, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨4, by decide⟩ ⟨105, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨5, by decide⟩ ⟨105, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨6, by decide⟩ ⟨105, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨7, by decide⟩ ⟨105, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨8, by decide⟩ ⟨105, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨9, by decide⟩ ⟨105, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨10, by decide⟩ ⟨105, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨11, by decide⟩ ⟨105, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨12, by decide⟩ ⟨105, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨13, by decide⟩ ⟨105, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨14, by decide⟩ ⟨105, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨15, by decide⟩ ⟨105, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨16, by decide⟩ ⟨105, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨17, by decide⟩ ⟨105, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨18, by decide⟩ ⟨105, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨19, by decide⟩ ⟨105, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨20, by decide⟩ ⟨105, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨21, by decide⟩ ⟨105, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨22, by decide⟩ ⟨105, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨23, by decide⟩ ⟨105, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨24, by decide⟩ ⟨105, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨25, by decide⟩ ⟨105, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨26, by decide⟩ ⟨105, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨27, by decide⟩ ⟨105, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨28, by decide⟩ ⟨105, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨29, by decide⟩ ⟨105, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨30, by decide⟩ ⟨105, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨31, by decide⟩ ⟨105, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨32, by decide⟩ ⟨105, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨33, by decide⟩ ⟨105, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨34, by decide⟩ ⟨105, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨35, by decide⟩ ⟨105, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨36, by decide⟩ ⟨105, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨37, by decide⟩ ⟨105, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨38, by decide⟩ ⟨105, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨39, by decide⟩ ⟨105, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨40, by decide⟩ ⟨105, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨41, by decide⟩ ⟨105, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨42, by decide⟩ ⟨105, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨43, by decide⟩ ⟨105, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨44, by decide⟩ ⟨105, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨45, by decide⟩ ⟨105, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨46, by decide⟩ ⟨105, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨47, by decide⟩ ⟨105, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨48, by decide⟩ ⟨105, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨49, by decide⟩ ⟨105, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨50, by decide⟩ ⟨105, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨51, by decide⟩ ⟨105, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨52, by decide⟩ ⟨105, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨53, by decide⟩ ⟨105, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨54, by decide⟩ ⟨105, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_fix ⟨55, by decide⟩ ⟨105, by decide⟩ p hp j hj hq fz1_55_105 fz2_55_105
  · exact match_zero_fix ⟨56, by decide⟩ ⟨105, by decide⟩ p hp j hj hq fz1_56_105 fz2_56_105
  · exact match_zero_fix ⟨57, by decide⟩ ⟨105, by decide⟩ p hp j hj hq fz1_57_105 fz2_57_105
  · exact match_zero_fix ⟨58, by decide⟩ ⟨105, by decide⟩ p hp j hj hq fz1_58_105 fz2_58_105
  · exact match_zero_fix ⟨59, by decide⟩ ⟨105, by decide⟩ p hp j hj hq fz1_59_105 fz2_59_105
  · exact match_zero_fix ⟨60, by decide⟩ ⟨105, by decide⟩ p hp j hj hq fz1_60_105 fz2_60_105
  · exact match_zero_fix ⟨61, by decide⟩ ⟨105, by decide⟩ p hp j hj hq fz1_61_105 fz2_61_105
  · exact match_zero_fix ⟨62, by decide⟩ ⟨105, by decide⟩ p hp j hj hq fz1_62_105 fz2_62_105
  · exact match_zero_fix ⟨63, by decide⟩ ⟨105, by decide⟩ p hp j hj hq fz1_63_105 fz2_63_105
  · exact match_zero_fix ⟨64, by decide⟩ ⟨105, by decide⟩ p hp j hj hq fz1_64_105 fz2_64_105
  · exact match_zero_fix ⟨65, by decide⟩ ⟨105, by decide⟩ p hp j hj hq fz1_65_105 fz2_65_105
  · exact match_zero_fix ⟨66, by decide⟩ ⟨105, by decide⟩ p hp j hj hq fz1_66_105 fz2_66_105
  · exact match_zero_fix ⟨67, by decide⟩ ⟨105, by decide⟩ p hp j hj hq fz1_67_105 fz2_67_105
  · exact match_zero_fix ⟨68, by decide⟩ ⟨105, by decide⟩ p hp j hj hq fz1_68_105 fz2_68_105
  · exact match_zero_fix ⟨69, by decide⟩ ⟨105, by decide⟩ p hp j hj hq fz1_69_105 fz2_69_105
  · exact match_zero_fix ⟨70, by decide⟩ ⟨105, by decide⟩ p hp j hj hq fz1_70_105 fz2_70_105
  · exact match_zero_fix ⟨71, by decide⟩ ⟨105, by decide⟩ p hp j hj hq fz1_71_105 fz2_71_105
  · exact match_zero_fix ⟨72, by decide⟩ ⟨105, by decide⟩ p hp j hj hq fz1_72_105 fz2_72_105
  · exact match_zero_fix ⟨73, by decide⟩ ⟨105, by decide⟩ p hp j hj hq fz1_73_105 fz2_73_105
  · exact match_zero_fix ⟨74, by decide⟩ ⟨105, by decide⟩ p hp j hj hq fz1_74_105 fz2_74_105
  · exact match_zero_fix ⟨75, by decide⟩ ⟨105, by decide⟩ p hp j hj hq fz1_75_105 fz2_75_105
  · exact match_zero_fix ⟨76, by decide⟩ ⟨105, by decide⟩ p hp j hj hq fz1_76_105 fz2_76_105
  · exact match_zero_fix ⟨77, by decide⟩ ⟨105, by decide⟩ p hp j hj hq fz1_77_105 fz2_77_105
  · exact match_zero_fix ⟨78, by decide⟩ ⟨105, by decide⟩ p hp j hj hq fz1_78_105 fz2_78_105
  · exact match_zero_fix ⟨79, by decide⟩ ⟨105, by decide⟩ p hp j hj hq fz1_79_105 fz2_79_105
  · exact match_zero_fix ⟨80, by decide⟩ ⟨105, by decide⟩ p hp j hj hq fz1_80_105 fz2_80_105
  · exact match_zero_fix ⟨81, by decide⟩ ⟨105, by decide⟩ p hp j hj hq fz1_81_105 fz2_81_105
  · exact match_zero_fix ⟨82, by decide⟩ ⟨105, by decide⟩ p hp j hj hq fz1_82_105 fz2_82_105
  · exact match_zero_fix ⟨83, by decide⟩ ⟨105, by decide⟩ p hp j hj hq fz1_83_105 fz2_83_105
  · exact match_zero_fix ⟨84, by decide⟩ ⟨105, by decide⟩ p hp j hj hq fz1_84_105 fz2_84_105
  · exact match_zero_fix ⟨85, by decide⟩ ⟨105, by decide⟩ p hp j hj hq fz1_85_105 fz2_85_105
  · exact match_zero_fix ⟨86, by decide⟩ ⟨105, by decide⟩ p hp j hj hq fz1_86_105 fz2_86_105
  · exact match_zero_fix ⟨87, by decide⟩ ⟨105, by decide⟩ p hp j hj hq fz1_87_105 fz2_87_105
  · exact match_zero_fix ⟨88, by decide⟩ ⟨105, by decide⟩ p hp j hj hq fz1_88_105 fz2_88_105
  · exact match_zero_fix ⟨89, by decide⟩ ⟨105, by decide⟩ p hp j hj hq fz1_89_105 fz2_89_105
  · exact match_zero_fix ⟨90, by decide⟩ ⟨105, by decide⟩ p hp j hj hq fz1_90_105 fz2_90_105
  · exact match_zero_fix ⟨91, by decide⟩ ⟨105, by decide⟩ p hp j hj hq fz1_91_105 fz2_91_105
  · exact match_zero_fix ⟨92, by decide⟩ ⟨105, by decide⟩ p hp j hj hq fz1_92_105 fz2_92_105
  · exact match_zero_fix ⟨93, by decide⟩ ⟨105, by decide⟩ p hp j hj hq fz1_93_105 fz2_93_105
  · exact match_zero_fix ⟨94, by decide⟩ ⟨105, by decide⟩ p hp j hj hq fz1_94_105 fz2_94_105
  · exact match_zero_fix ⟨95, by decide⟩ ⟨105, by decide⟩ p hp j hj hq fz1_95_105 fz2_95_105
  · exact match_zero_fix ⟨96, by decide⟩ ⟨105, by decide⟩ p hp j hj hq fz1_96_105 fz2_96_105
  · exact match_zero_fix ⟨97, by decide⟩ ⟨105, by decide⟩ p hp j hj hq fz1_97_105 fz2_97_105
  · exact match_zero_fix ⟨98, by decide⟩ ⟨105, by decide⟩ p hp j hj hq fz1_98_105 fz2_98_105
  · exact match_zero_fix ⟨99, by decide⟩ ⟨105, by decide⟩ p hp j hj hq fz1_99_105 fz2_99_105
  · exact match_zero_fix ⟨100, by decide⟩ ⟨105, by decide⟩ p hp j hj hq fz1_100_105 fz2_100_105
  · exact match_zero_fix ⟨101, by decide⟩ ⟨105, by decide⟩ p hp j hj hq fz1_101_105 fz2_101_105
  · exact match_zero_fix ⟨102, by decide⟩ ⟨105, by decide⟩ p hp j hj hq fz1_102_105 fz2_102_105
  · exact match_zero_fix ⟨103, by decide⟩ ⟨105, by decide⟩ p hp j hj hq fz1_103_105 fz2_103_105
  · exact match_zero_fix ⟨104, by decide⟩ ⟨105, by decide⟩ p hp j hj hq fz1_104_105 fz2_104_105
  · exact pair_105_105 p hp hrep j hj hq
  · exact match_zero_fix ⟨106, by decide⟩ ⟨105, by decide⟩ p hp j hj hq fz1_106_105 fz2_106_105
  · exact match_zero_fix ⟨107, by decide⟩ ⟨105, by decide⟩ p hp j hj hq fz1_107_105 fz2_107_105
  · exact match_zero_fix ⟨108, by decide⟩ ⟨105, by decide⟩ p hp j hj hq fz1_108_105 fz2_108_105
  · exact match_zero_fix ⟨109, by decide⟩ ⟨105, by decide⟩ p hp j hj hq fz1_109_105 fz2_109_105
  · exact match_zero_fix ⟨110, by decide⟩ ⟨105, by decide⟩ p hp j hj hq fz1_110_105 fz2_110_105
  · exact match_zero_fix ⟨111, by decide⟩ ⟨105, by decide⟩ p hp j hj hq fz1_111_105 fz2_111_105
  · exact match_zero_fix ⟨112, by decide⟩ ⟨105, by decide⟩ p hp j hj hq fz1_112_105 fz2_112_105
  · exact match_zero_fix ⟨113, by decide⟩ ⟨105, by decide⟩ p hp j hj hq fz1_113_105 fz2_113_105
  · exact match_zero_fix ⟨114, by decide⟩ ⟨105, by decide⟩ p hp j hj hq fz1_114_105 fz2_114_105
  · exact match_zero_fix ⟨115, by decide⟩ ⟨105, by decide⟩ p hp j hj hq fz1_115_105 fz2_115_105
  · exact pair_116_105 p hp hrep j hj hq
  · exact match_zero_fix ⟨117, by decide⟩ ⟨105, by decide⟩ p hp j hj hq fz1_117_105 fz2_117_105
  · exact match_zero_fix ⟨118, by decide⟩ ⟨105, by decide⟩ p hp j hj hq fz1_118_105 fz2_118_105
  · exact match_zero_fix ⟨119, by decide⟩ ⟨105, by decide⟩ p hp j hj hq fz1_119_105 fz2_119_105
  · exact match_zero_fix ⟨120, by decide⟩ ⟨105, by decide⟩ p hp j hj hq fz1_120_105 fz2_120_105
  · exact match_zero_fix ⟨121, by decide⟩ ⟨105, by decide⟩ p hp j hj hq fz1_121_105 fz2_121_105
  · exact match_zero_fix ⟨122, by decide⟩ ⟨105, by decide⟩ p hp j hj hq fz1_122_105 fz2_122_105
  · exact match_zero_fix ⟨123, by decide⟩ ⟨105, by decide⟩ p hp j hj hq fz1_123_105 fz2_123_105
  · exact match_zero_fix ⟨124, by decide⟩ ⟨105, by decide⟩ p hp j hj hq fz1_124_105 fz2_124_105
  · exact pair_125_105 p hp hrep j hj hq
  · exact match_zero_fix ⟨126, by decide⟩ ⟨105, by decide⟩ p hp j hj hq fz1_126_105 fz2_126_105
  · exact match_zero_fix ⟨127, by decide⟩ ⟨105, by decide⟩ p hp j hj hq fz1_127_105 fz2_127_105
  · exact match_zero_fix ⟨128, by decide⟩ ⟨105, by decide⟩ p hp j hj hq fz1_128_105 fz2_128_105
  · exact pair_129_105 p hp hrep j hj hq
  · exact match_zero_fix ⟨130, by decide⟩ ⟨105, by decide⟩ p hp j hj hq fz1_130_105 fz2_130_105
  · exact match_zero_fix ⟨131, by decide⟩ ⟨105, by decide⟩ p hp j hj hq fz1_131_105 fz2_131_105
  · exact match_zero_fix ⟨132, by decide⟩ ⟨105, by decide⟩ p hp j hj hq fz1_132_105 fz2_132_105
  · exact pair_133_105 p hp hrep j hj hq
  · exact match_zero_fix ⟨134, by decide⟩ ⟨105, by decide⟩ p hp j hj hq fz1_134_105 fz2_134_105
  · exact match_zero_fix ⟨135, by decide⟩ ⟨105, by decide⟩ p hp j hj hq fz1_135_105 fz2_135_105
  · exact match_zero_fix ⟨136, by decide⟩ ⟨105, by decide⟩ p hp j hj hq fz1_136_105 fz2_136_105
  · exact pair_137_105 p hp hrep j hj hq
  · exact match_zero_fix ⟨138, by decide⟩ ⟨105, by decide⟩ p hp j hj hq fz1_138_105 fz2_138_105
  · exact match_zero_fix ⟨139, by decide⟩ ⟨105, by decide⟩ p hp j hj hq fz1_139_105 fz2_139_105
  · exact match_zero_fix ⟨140, by decide⟩ ⟨105, by decide⟩ p hp j hj hq fz1_140_105 fz2_140_105
  · exact match_zero_fix ⟨141, by decide⟩ ⟨105, by decide⟩ p hp j hj hq fz1_141_105 fz2_141_105
  · exact match_zero_fix ⟨142, by decide⟩ ⟨105, by decide⟩ p hp j hj hq fz1_142_105 fz2_142_105
  · exact match_zero_fix ⟨143, by decide⟩ ⟨105, by decide⟩ p hp j hj hq fz1_143_105 fz2_143_105
  · exact match_zero_fix ⟨144, by decide⟩ ⟨105, by decide⟩ p hp j hj hq fz1_144_105 fz2_144_105
  · exact pair_145_105 p hp hrep j hj hq
  · exact match_zero_fix ⟨146, by decide⟩ ⟨105, by decide⟩ p hp j hj hq fz1_146_105 fz2_146_105
  · exact pair_147_105 p hp hrep j hj hq

theorem master_106 (p : Nat) (hp : p < (Q2.transData.getD 106 []).length)
    (hrep : (Q2.cosetIsRep.getD 106 []).getD p false = true)
    (rK : Fin 148) (j : Nat) (hj : j < (repChars.getD rK.val []).length)
    (hq : (normIsRep.getD rK.val []).getD j false = true) :
    species (Q2.reps (⟨106, by decide⟩ : Fin 148)) (colE2 ⟨106, by decide⟩ p hp)
        (rowE2 rK j hj hq)
      = species (reps (⟨106, by decide⟩ : Fin 148))
        (colE1 ⟨106, by decide⟩ p (transLenTr ⟨106, by decide⟩ p hp)) (rowE1 rK j hj) := by
  rcases rK with ⟨nK, hnK⟩; interval_cases nK
  · exact match_zero_len ⟨0, by decide⟩ ⟨106, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨1, by decide⟩ ⟨106, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨2, by decide⟩ ⟨106, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨3, by decide⟩ ⟨106, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨4, by decide⟩ ⟨106, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨5, by decide⟩ ⟨106, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨6, by decide⟩ ⟨106, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨7, by decide⟩ ⟨106, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨8, by decide⟩ ⟨106, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨9, by decide⟩ ⟨106, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨10, by decide⟩ ⟨106, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨11, by decide⟩ ⟨106, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨12, by decide⟩ ⟨106, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨13, by decide⟩ ⟨106, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨14, by decide⟩ ⟨106, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨15, by decide⟩ ⟨106, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨16, by decide⟩ ⟨106, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨17, by decide⟩ ⟨106, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨18, by decide⟩ ⟨106, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨19, by decide⟩ ⟨106, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨20, by decide⟩ ⟨106, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨21, by decide⟩ ⟨106, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨22, by decide⟩ ⟨106, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨23, by decide⟩ ⟨106, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨24, by decide⟩ ⟨106, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨25, by decide⟩ ⟨106, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨26, by decide⟩ ⟨106, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨27, by decide⟩ ⟨106, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨28, by decide⟩ ⟨106, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨29, by decide⟩ ⟨106, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨30, by decide⟩ ⟨106, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨31, by decide⟩ ⟨106, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨32, by decide⟩ ⟨106, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨33, by decide⟩ ⟨106, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨34, by decide⟩ ⟨106, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨35, by decide⟩ ⟨106, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨36, by decide⟩ ⟨106, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨37, by decide⟩ ⟨106, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨38, by decide⟩ ⟨106, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨39, by decide⟩ ⟨106, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨40, by decide⟩ ⟨106, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨41, by decide⟩ ⟨106, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨42, by decide⟩ ⟨106, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨43, by decide⟩ ⟨106, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨44, by decide⟩ ⟨106, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨45, by decide⟩ ⟨106, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨46, by decide⟩ ⟨106, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨47, by decide⟩ ⟨106, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨48, by decide⟩ ⟨106, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨49, by decide⟩ ⟨106, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨50, by decide⟩ ⟨106, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨51, by decide⟩ ⟨106, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨52, by decide⟩ ⟨106, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨53, by decide⟩ ⟨106, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨54, by decide⟩ ⟨106, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_fix ⟨55, by decide⟩ ⟨106, by decide⟩ p hp j hj hq fz1_55_106 fz2_55_106
  · exact match_zero_fix ⟨56, by decide⟩ ⟨106, by decide⟩ p hp j hj hq fz1_56_106 fz2_56_106
  · exact match_zero_fix ⟨57, by decide⟩ ⟨106, by decide⟩ p hp j hj hq fz1_57_106 fz2_57_106
  · exact match_zero_fix ⟨58, by decide⟩ ⟨106, by decide⟩ p hp j hj hq fz1_58_106 fz2_58_106
  · exact match_zero_fix ⟨59, by decide⟩ ⟨106, by decide⟩ p hp j hj hq fz1_59_106 fz2_59_106
  · exact match_zero_fix ⟨60, by decide⟩ ⟨106, by decide⟩ p hp j hj hq fz1_60_106 fz2_60_106
  · exact match_zero_fix ⟨61, by decide⟩ ⟨106, by decide⟩ p hp j hj hq fz1_61_106 fz2_61_106
  · exact match_zero_fix ⟨62, by decide⟩ ⟨106, by decide⟩ p hp j hj hq fz1_62_106 fz2_62_106
  · exact match_zero_fix ⟨63, by decide⟩ ⟨106, by decide⟩ p hp j hj hq fz1_63_106 fz2_63_106
  · exact match_zero_fix ⟨64, by decide⟩ ⟨106, by decide⟩ p hp j hj hq fz1_64_106 fz2_64_106
  · exact match_zero_fix ⟨65, by decide⟩ ⟨106, by decide⟩ p hp j hj hq fz1_65_106 fz2_65_106
  · exact match_zero_fix ⟨66, by decide⟩ ⟨106, by decide⟩ p hp j hj hq fz1_66_106 fz2_66_106
  · exact match_zero_fix ⟨67, by decide⟩ ⟨106, by decide⟩ p hp j hj hq fz1_67_106 fz2_67_106
  · exact match_zero_fix ⟨68, by decide⟩ ⟨106, by decide⟩ p hp j hj hq fz1_68_106 fz2_68_106
  · exact match_zero_fix ⟨69, by decide⟩ ⟨106, by decide⟩ p hp j hj hq fz1_69_106 fz2_69_106
  · exact match_zero_fix ⟨70, by decide⟩ ⟨106, by decide⟩ p hp j hj hq fz1_70_106 fz2_70_106
  · exact match_zero_fix ⟨71, by decide⟩ ⟨106, by decide⟩ p hp j hj hq fz1_71_106 fz2_71_106
  · exact match_zero_fix ⟨72, by decide⟩ ⟨106, by decide⟩ p hp j hj hq fz1_72_106 fz2_72_106
  · exact match_zero_fix ⟨73, by decide⟩ ⟨106, by decide⟩ p hp j hj hq fz1_73_106 fz2_73_106
  · exact match_zero_fix ⟨74, by decide⟩ ⟨106, by decide⟩ p hp j hj hq fz1_74_106 fz2_74_106
  · exact match_zero_fix ⟨75, by decide⟩ ⟨106, by decide⟩ p hp j hj hq fz1_75_106 fz2_75_106
  · exact match_zero_fix ⟨76, by decide⟩ ⟨106, by decide⟩ p hp j hj hq fz1_76_106 fz2_76_106
  · exact match_zero_fix ⟨77, by decide⟩ ⟨106, by decide⟩ p hp j hj hq fz1_77_106 fz2_77_106
  · exact match_zero_fix ⟨78, by decide⟩ ⟨106, by decide⟩ p hp j hj hq fz1_78_106 fz2_78_106
  · exact match_zero_fix ⟨79, by decide⟩ ⟨106, by decide⟩ p hp j hj hq fz1_79_106 fz2_79_106
  · exact match_zero_fix ⟨80, by decide⟩ ⟨106, by decide⟩ p hp j hj hq fz1_80_106 fz2_80_106
  · exact match_zero_fix ⟨81, by decide⟩ ⟨106, by decide⟩ p hp j hj hq fz1_81_106 fz2_81_106
  · exact match_zero_fix ⟨82, by decide⟩ ⟨106, by decide⟩ p hp j hj hq fz1_82_106 fz2_82_106
  · exact match_zero_fix ⟨83, by decide⟩ ⟨106, by decide⟩ p hp j hj hq fz1_83_106 fz2_83_106
  · exact match_zero_fix ⟨84, by decide⟩ ⟨106, by decide⟩ p hp j hj hq fz1_84_106 fz2_84_106
  · exact match_zero_fix ⟨85, by decide⟩ ⟨106, by decide⟩ p hp j hj hq fz1_85_106 fz2_85_106
  · exact match_zero_fix ⟨86, by decide⟩ ⟨106, by decide⟩ p hp j hj hq fz1_86_106 fz2_86_106
  · exact match_zero_fix ⟨87, by decide⟩ ⟨106, by decide⟩ p hp j hj hq fz1_87_106 fz2_87_106
  · exact match_zero_fix ⟨88, by decide⟩ ⟨106, by decide⟩ p hp j hj hq fz1_88_106 fz2_88_106
  · exact match_zero_fix ⟨89, by decide⟩ ⟨106, by decide⟩ p hp j hj hq fz1_89_106 fz2_89_106
  · exact match_zero_fix ⟨90, by decide⟩ ⟨106, by decide⟩ p hp j hj hq fz1_90_106 fz2_90_106
  · exact match_zero_fix ⟨91, by decide⟩ ⟨106, by decide⟩ p hp j hj hq fz1_91_106 fz2_91_106
  · exact match_zero_fix ⟨92, by decide⟩ ⟨106, by decide⟩ p hp j hj hq fz1_92_106 fz2_92_106
  · exact match_zero_fix ⟨93, by decide⟩ ⟨106, by decide⟩ p hp j hj hq fz1_93_106 fz2_93_106
  · exact match_zero_fix ⟨94, by decide⟩ ⟨106, by decide⟩ p hp j hj hq fz1_94_106 fz2_94_106
  · exact match_zero_fix ⟨95, by decide⟩ ⟨106, by decide⟩ p hp j hj hq fz1_95_106 fz2_95_106
  · exact match_zero_fix ⟨96, by decide⟩ ⟨106, by decide⟩ p hp j hj hq fz1_96_106 fz2_96_106
  · exact match_zero_fix ⟨97, by decide⟩ ⟨106, by decide⟩ p hp j hj hq fz1_97_106 fz2_97_106
  · exact match_zero_fix ⟨98, by decide⟩ ⟨106, by decide⟩ p hp j hj hq fz1_98_106 fz2_98_106
  · exact match_zero_fix ⟨99, by decide⟩ ⟨106, by decide⟩ p hp j hj hq fz1_99_106 fz2_99_106
  · exact match_zero_fix ⟨100, by decide⟩ ⟨106, by decide⟩ p hp j hj hq fz1_100_106 fz2_100_106
  · exact match_zero_fix ⟨101, by decide⟩ ⟨106, by decide⟩ p hp j hj hq fz1_101_106 fz2_101_106
  · exact match_zero_fix ⟨102, by decide⟩ ⟨106, by decide⟩ p hp j hj hq fz1_102_106 fz2_102_106
  · exact match_zero_fix ⟨103, by decide⟩ ⟨106, by decide⟩ p hp j hj hq fz1_103_106 fz2_103_106
  · exact match_zero_fix ⟨104, by decide⟩ ⟨106, by decide⟩ p hp j hj hq fz1_104_106 fz2_104_106
  · exact match_zero_fix ⟨105, by decide⟩ ⟨106, by decide⟩ p hp j hj hq fz1_105_106 fz2_105_106
  · exact pair_106_106 p hp hrep j hj hq
  · exact match_zero_fix ⟨107, by decide⟩ ⟨106, by decide⟩ p hp j hj hq fz1_107_106 fz2_107_106
  · exact match_zero_fix ⟨108, by decide⟩ ⟨106, by decide⟩ p hp j hj hq fz1_108_106 fz2_108_106
  · exact match_zero_fix ⟨109, by decide⟩ ⟨106, by decide⟩ p hp j hj hq fz1_109_106 fz2_109_106
  · exact match_zero_fix ⟨110, by decide⟩ ⟨106, by decide⟩ p hp j hj hq fz1_110_106 fz2_110_106
  · exact match_zero_fix ⟨111, by decide⟩ ⟨106, by decide⟩ p hp j hj hq fz1_111_106 fz2_111_106
  · exact match_zero_fix ⟨112, by decide⟩ ⟨106, by decide⟩ p hp j hj hq fz1_112_106 fz2_112_106
  · exact match_zero_fix ⟨113, by decide⟩ ⟨106, by decide⟩ p hp j hj hq fz1_113_106 fz2_113_106
  · exact match_zero_fix ⟨114, by decide⟩ ⟨106, by decide⟩ p hp j hj hq fz1_114_106 fz2_114_106
  · exact match_zero_fix ⟨115, by decide⟩ ⟨106, by decide⟩ p hp j hj hq fz1_115_106 fz2_115_106
  · exact match_zero_fix ⟨116, by decide⟩ ⟨106, by decide⟩ p hp j hj hq fz1_116_106 fz2_116_106
  · exact pair_117_106 p hp hrep j hj hq
  · exact match_zero_fix ⟨118, by decide⟩ ⟨106, by decide⟩ p hp j hj hq fz1_118_106 fz2_118_106
  · exact match_zero_fix ⟨119, by decide⟩ ⟨106, by decide⟩ p hp j hj hq fz1_119_106 fz2_119_106
  · exact match_zero_fix ⟨120, by decide⟩ ⟨106, by decide⟩ p hp j hj hq fz1_120_106 fz2_120_106
  · exact pair_121_106 p hp hrep j hj hq
  · exact match_zero_fix ⟨122, by decide⟩ ⟨106, by decide⟩ p hp j hj hq fz1_122_106 fz2_122_106
  · exact match_zero_fix ⟨123, by decide⟩ ⟨106, by decide⟩ p hp j hj hq fz1_123_106 fz2_123_106
  · exact match_zero_fix ⟨124, by decide⟩ ⟨106, by decide⟩ p hp j hj hq fz1_124_106 fz2_124_106
  · exact match_zero_fix ⟨125, by decide⟩ ⟨106, by decide⟩ p hp j hj hq fz1_125_106 fz2_125_106
  · exact match_zero_fix ⟨126, by decide⟩ ⟨106, by decide⟩ p hp j hj hq fz1_126_106 fz2_126_106
  · exact match_zero_fix ⟨127, by decide⟩ ⟨106, by decide⟩ p hp j hj hq fz1_127_106 fz2_127_106
  · exact match_zero_fix ⟨128, by decide⟩ ⟨106, by decide⟩ p hp j hj hq fz1_128_106 fz2_128_106
  · exact match_zero_fix ⟨129, by decide⟩ ⟨106, by decide⟩ p hp j hj hq fz1_129_106 fz2_129_106
  · exact pair_130_106 p hp hrep j hj hq
  · exact match_zero_fix ⟨131, by decide⟩ ⟨106, by decide⟩ p hp j hj hq fz1_131_106 fz2_131_106
  · exact match_zero_fix ⟨132, by decide⟩ ⟨106, by decide⟩ p hp j hj hq fz1_132_106 fz2_132_106
  · exact match_zero_fix ⟨133, by decide⟩ ⟨106, by decide⟩ p hp j hj hq fz1_133_106 fz2_133_106
  · exact pair_134_106 p hp hrep j hj hq
  · exact match_zero_fix ⟨135, by decide⟩ ⟨106, by decide⟩ p hp j hj hq fz1_135_106 fz2_135_106
  · exact match_zero_fix ⟨136, by decide⟩ ⟨106, by decide⟩ p hp j hj hq fz1_136_106 fz2_136_106
  · exact match_zero_fix ⟨137, by decide⟩ ⟨106, by decide⟩ p hp j hj hq fz1_137_106 fz2_137_106
  · exact pair_138_106 p hp hrep j hj hq
  · exact match_zero_fix ⟨139, by decide⟩ ⟨106, by decide⟩ p hp j hj hq fz1_139_106 fz2_139_106
  · exact match_zero_fix ⟨140, by decide⟩ ⟨106, by decide⟩ p hp j hj hq fz1_140_106 fz2_140_106
  · exact match_zero_fix ⟨141, by decide⟩ ⟨106, by decide⟩ p hp j hj hq fz1_141_106 fz2_141_106
  · exact match_zero_fix ⟨142, by decide⟩ ⟨106, by decide⟩ p hp j hj hq fz1_142_106 fz2_142_106
  · exact match_zero_fix ⟨143, by decide⟩ ⟨106, by decide⟩ p hp j hj hq fz1_143_106 fz2_143_106
  · exact match_zero_fix ⟨144, by decide⟩ ⟨106, by decide⟩ p hp j hj hq fz1_144_106 fz2_144_106
  · exact pair_145_106 p hp hrep j hj hq
  · exact match_zero_fix ⟨146, by decide⟩ ⟨106, by decide⟩ p hp j hj hq fz1_146_106 fz2_146_106
  · exact pair_147_106 p hp hrep j hj hq

theorem master_107 (p : Nat) (hp : p < (Q2.transData.getD 107 []).length)
    (hrep : (Q2.cosetIsRep.getD 107 []).getD p false = true)
    (rK : Fin 148) (j : Nat) (hj : j < (repChars.getD rK.val []).length)
    (hq : (normIsRep.getD rK.val []).getD j false = true) :
    species (Q2.reps (⟨107, by decide⟩ : Fin 148)) (colE2 ⟨107, by decide⟩ p hp)
        (rowE2 rK j hj hq)
      = species (reps (⟨107, by decide⟩ : Fin 148))
        (colE1 ⟨107, by decide⟩ p (transLenTr ⟨107, by decide⟩ p hp)) (rowE1 rK j hj) := by
  rcases rK with ⟨nK, hnK⟩; interval_cases nK
  · exact match_zero_len ⟨0, by decide⟩ ⟨107, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨1, by decide⟩ ⟨107, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨2, by decide⟩ ⟨107, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨3, by decide⟩ ⟨107, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨4, by decide⟩ ⟨107, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨5, by decide⟩ ⟨107, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨6, by decide⟩ ⟨107, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨7, by decide⟩ ⟨107, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨8, by decide⟩ ⟨107, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨9, by decide⟩ ⟨107, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨10, by decide⟩ ⟨107, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨11, by decide⟩ ⟨107, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨12, by decide⟩ ⟨107, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨13, by decide⟩ ⟨107, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨14, by decide⟩ ⟨107, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨15, by decide⟩ ⟨107, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨16, by decide⟩ ⟨107, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨17, by decide⟩ ⟨107, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨18, by decide⟩ ⟨107, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨19, by decide⟩ ⟨107, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨20, by decide⟩ ⟨107, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨21, by decide⟩ ⟨107, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨22, by decide⟩ ⟨107, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨23, by decide⟩ ⟨107, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨24, by decide⟩ ⟨107, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨25, by decide⟩ ⟨107, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨26, by decide⟩ ⟨107, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨27, by decide⟩ ⟨107, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨28, by decide⟩ ⟨107, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨29, by decide⟩ ⟨107, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨30, by decide⟩ ⟨107, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨31, by decide⟩ ⟨107, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨32, by decide⟩ ⟨107, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨33, by decide⟩ ⟨107, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨34, by decide⟩ ⟨107, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨35, by decide⟩ ⟨107, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨36, by decide⟩ ⟨107, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨37, by decide⟩ ⟨107, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨38, by decide⟩ ⟨107, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨39, by decide⟩ ⟨107, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨40, by decide⟩ ⟨107, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨41, by decide⟩ ⟨107, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨42, by decide⟩ ⟨107, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨43, by decide⟩ ⟨107, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨44, by decide⟩ ⟨107, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨45, by decide⟩ ⟨107, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨46, by decide⟩ ⟨107, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨47, by decide⟩ ⟨107, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨48, by decide⟩ ⟨107, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨49, by decide⟩ ⟨107, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨50, by decide⟩ ⟨107, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨51, by decide⟩ ⟨107, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨52, by decide⟩ ⟨107, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨53, by decide⟩ ⟨107, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨54, by decide⟩ ⟨107, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_fix ⟨55, by decide⟩ ⟨107, by decide⟩ p hp j hj hq fz1_55_107 fz2_55_107
  · exact match_zero_fix ⟨56, by decide⟩ ⟨107, by decide⟩ p hp j hj hq fz1_56_107 fz2_56_107
  · exact match_zero_fix ⟨57, by decide⟩ ⟨107, by decide⟩ p hp j hj hq fz1_57_107 fz2_57_107
  · exact match_zero_fix ⟨58, by decide⟩ ⟨107, by decide⟩ p hp j hj hq fz1_58_107 fz2_58_107
  · exact match_zero_fix ⟨59, by decide⟩ ⟨107, by decide⟩ p hp j hj hq fz1_59_107 fz2_59_107
  · exact match_zero_fix ⟨60, by decide⟩ ⟨107, by decide⟩ p hp j hj hq fz1_60_107 fz2_60_107
  · exact match_zero_fix ⟨61, by decide⟩ ⟨107, by decide⟩ p hp j hj hq fz1_61_107 fz2_61_107
  · exact match_zero_fix ⟨62, by decide⟩ ⟨107, by decide⟩ p hp j hj hq fz1_62_107 fz2_62_107
  · exact match_zero_fix ⟨63, by decide⟩ ⟨107, by decide⟩ p hp j hj hq fz1_63_107 fz2_63_107
  · exact match_zero_fix ⟨64, by decide⟩ ⟨107, by decide⟩ p hp j hj hq fz1_64_107 fz2_64_107
  · exact match_zero_fix ⟨65, by decide⟩ ⟨107, by decide⟩ p hp j hj hq fz1_65_107 fz2_65_107
  · exact match_zero_fix ⟨66, by decide⟩ ⟨107, by decide⟩ p hp j hj hq fz1_66_107 fz2_66_107
  · exact match_zero_fix ⟨67, by decide⟩ ⟨107, by decide⟩ p hp j hj hq fz1_67_107 fz2_67_107
  · exact match_zero_fix ⟨68, by decide⟩ ⟨107, by decide⟩ p hp j hj hq fz1_68_107 fz2_68_107
  · exact match_zero_fix ⟨69, by decide⟩ ⟨107, by decide⟩ p hp j hj hq fz1_69_107 fz2_69_107
  · exact match_zero_fix ⟨70, by decide⟩ ⟨107, by decide⟩ p hp j hj hq fz1_70_107 fz2_70_107
  · exact match_zero_fix ⟨71, by decide⟩ ⟨107, by decide⟩ p hp j hj hq fz1_71_107 fz2_71_107
  · exact match_zero_fix ⟨72, by decide⟩ ⟨107, by decide⟩ p hp j hj hq fz1_72_107 fz2_72_107
  · exact match_zero_fix ⟨73, by decide⟩ ⟨107, by decide⟩ p hp j hj hq fz1_73_107 fz2_73_107
  · exact match_zero_fix ⟨74, by decide⟩ ⟨107, by decide⟩ p hp j hj hq fz1_74_107 fz2_74_107
  · exact match_zero_fix ⟨75, by decide⟩ ⟨107, by decide⟩ p hp j hj hq fz1_75_107 fz2_75_107
  · exact match_zero_fix ⟨76, by decide⟩ ⟨107, by decide⟩ p hp j hj hq fz1_76_107 fz2_76_107
  · exact match_zero_fix ⟨77, by decide⟩ ⟨107, by decide⟩ p hp j hj hq fz1_77_107 fz2_77_107
  · exact match_zero_fix ⟨78, by decide⟩ ⟨107, by decide⟩ p hp j hj hq fz1_78_107 fz2_78_107
  · exact match_zero_fix ⟨79, by decide⟩ ⟨107, by decide⟩ p hp j hj hq fz1_79_107 fz2_79_107
  · exact match_zero_fix ⟨80, by decide⟩ ⟨107, by decide⟩ p hp j hj hq fz1_80_107 fz2_80_107
  · exact match_zero_fix ⟨81, by decide⟩ ⟨107, by decide⟩ p hp j hj hq fz1_81_107 fz2_81_107
  · exact match_zero_fix ⟨82, by decide⟩ ⟨107, by decide⟩ p hp j hj hq fz1_82_107 fz2_82_107
  · exact match_zero_fix ⟨83, by decide⟩ ⟨107, by decide⟩ p hp j hj hq fz1_83_107 fz2_83_107
  · exact match_zero_fix ⟨84, by decide⟩ ⟨107, by decide⟩ p hp j hj hq fz1_84_107 fz2_84_107
  · exact match_zero_fix ⟨85, by decide⟩ ⟨107, by decide⟩ p hp j hj hq fz1_85_107 fz2_85_107
  · exact match_zero_fix ⟨86, by decide⟩ ⟨107, by decide⟩ p hp j hj hq fz1_86_107 fz2_86_107
  · exact match_zero_fix ⟨87, by decide⟩ ⟨107, by decide⟩ p hp j hj hq fz1_87_107 fz2_87_107
  · exact match_zero_fix ⟨88, by decide⟩ ⟨107, by decide⟩ p hp j hj hq fz1_88_107 fz2_88_107
  · exact match_zero_fix ⟨89, by decide⟩ ⟨107, by decide⟩ p hp j hj hq fz1_89_107 fz2_89_107
  · exact match_zero_fix ⟨90, by decide⟩ ⟨107, by decide⟩ p hp j hj hq fz1_90_107 fz2_90_107
  · exact match_zero_fix ⟨91, by decide⟩ ⟨107, by decide⟩ p hp j hj hq fz1_91_107 fz2_91_107
  · exact match_zero_fix ⟨92, by decide⟩ ⟨107, by decide⟩ p hp j hj hq fz1_92_107 fz2_92_107
  · exact match_zero_fix ⟨93, by decide⟩ ⟨107, by decide⟩ p hp j hj hq fz1_93_107 fz2_93_107
  · exact match_zero_fix ⟨94, by decide⟩ ⟨107, by decide⟩ p hp j hj hq fz1_94_107 fz2_94_107
  · exact match_zero_fix ⟨95, by decide⟩ ⟨107, by decide⟩ p hp j hj hq fz1_95_107 fz2_95_107
  · exact match_zero_fix ⟨96, by decide⟩ ⟨107, by decide⟩ p hp j hj hq fz1_96_107 fz2_96_107
  · exact match_zero_fix ⟨97, by decide⟩ ⟨107, by decide⟩ p hp j hj hq fz1_97_107 fz2_97_107
  · exact match_zero_fix ⟨98, by decide⟩ ⟨107, by decide⟩ p hp j hj hq fz1_98_107 fz2_98_107
  · exact match_zero_fix ⟨99, by decide⟩ ⟨107, by decide⟩ p hp j hj hq fz1_99_107 fz2_99_107
  · exact match_zero_fix ⟨100, by decide⟩ ⟨107, by decide⟩ p hp j hj hq fz1_100_107 fz2_100_107
  · exact match_zero_fix ⟨101, by decide⟩ ⟨107, by decide⟩ p hp j hj hq fz1_101_107 fz2_101_107
  · exact match_zero_fix ⟨102, by decide⟩ ⟨107, by decide⟩ p hp j hj hq fz1_102_107 fz2_102_107
  · exact match_zero_fix ⟨103, by decide⟩ ⟨107, by decide⟩ p hp j hj hq fz1_103_107 fz2_103_107
  · exact match_zero_fix ⟨104, by decide⟩ ⟨107, by decide⟩ p hp j hj hq fz1_104_107 fz2_104_107
  · exact match_zero_fix ⟨105, by decide⟩ ⟨107, by decide⟩ p hp j hj hq fz1_105_107 fz2_105_107
  · exact match_zero_fix ⟨106, by decide⟩ ⟨107, by decide⟩ p hp j hj hq fz1_106_107 fz2_106_107
  · exact pair_107_107 p hp hrep j hj hq
  · exact match_zero_fix ⟨108, by decide⟩ ⟨107, by decide⟩ p hp j hj hq fz1_108_107 fz2_108_107
  · exact match_zero_fix ⟨109, by decide⟩ ⟨107, by decide⟩ p hp j hj hq fz1_109_107 fz2_109_107
  · exact match_zero_fix ⟨110, by decide⟩ ⟨107, by decide⟩ p hp j hj hq fz1_110_107 fz2_110_107
  · exact match_zero_fix ⟨111, by decide⟩ ⟨107, by decide⟩ p hp j hj hq fz1_111_107 fz2_111_107
  · exact match_zero_fix ⟨112, by decide⟩ ⟨107, by decide⟩ p hp j hj hq fz1_112_107 fz2_112_107
  · exact match_zero_fix ⟨113, by decide⟩ ⟨107, by decide⟩ p hp j hj hq fz1_113_107 fz2_113_107
  · exact match_zero_fix ⟨114, by decide⟩ ⟨107, by decide⟩ p hp j hj hq fz1_114_107 fz2_114_107
  · exact match_zero_fix ⟨115, by decide⟩ ⟨107, by decide⟩ p hp j hj hq fz1_115_107 fz2_115_107
  · exact match_zero_fix ⟨116, by decide⟩ ⟨107, by decide⟩ p hp j hj hq fz1_116_107 fz2_116_107
  · exact match_zero_fix ⟨117, by decide⟩ ⟨107, by decide⟩ p hp j hj hq fz1_117_107 fz2_117_107
  · exact pair_118_107 p hp hrep j hj hq
  · exact match_zero_fix ⟨119, by decide⟩ ⟨107, by decide⟩ p hp j hj hq fz1_119_107 fz2_119_107
  · exact match_zero_fix ⟨120, by decide⟩ ⟨107, by decide⟩ p hp j hj hq fz1_120_107 fz2_120_107
  · exact match_zero_fix ⟨121, by decide⟩ ⟨107, by decide⟩ p hp j hj hq fz1_121_107 fz2_121_107
  · exact pair_122_107 p hp hrep j hj hq
  · exact match_zero_fix ⟨123, by decide⟩ ⟨107, by decide⟩ p hp j hj hq fz1_123_107 fz2_123_107
  · exact match_zero_fix ⟨124, by decide⟩ ⟨107, by decide⟩ p hp j hj hq fz1_124_107 fz2_124_107
  · exact match_zero_fix ⟨125, by decide⟩ ⟨107, by decide⟩ p hp j hj hq fz1_125_107 fz2_125_107
  · exact pair_126_107 p hp hrep j hj hq
  · exact match_zero_fix ⟨127, by decide⟩ ⟨107, by decide⟩ p hp j hj hq fz1_127_107 fz2_127_107
  · exact match_zero_fix ⟨128, by decide⟩ ⟨107, by decide⟩ p hp j hj hq fz1_128_107 fz2_128_107
  · exact match_zero_fix ⟨129, by decide⟩ ⟨107, by decide⟩ p hp j hj hq fz1_129_107 fz2_129_107
  · exact match_zero_fix ⟨130, by decide⟩ ⟨107, by decide⟩ p hp j hj hq fz1_130_107 fz2_130_107
  · exact match_zero_fix ⟨131, by decide⟩ ⟨107, by decide⟩ p hp j hj hq fz1_131_107 fz2_131_107
  · exact match_zero_fix ⟨132, by decide⟩ ⟨107, by decide⟩ p hp j hj hq fz1_132_107 fz2_132_107
  · exact match_zero_fix ⟨133, by decide⟩ ⟨107, by decide⟩ p hp j hj hq fz1_133_107 fz2_133_107
  · exact match_zero_fix ⟨134, by decide⟩ ⟨107, by decide⟩ p hp j hj hq fz1_134_107 fz2_134_107
  · exact pair_135_107 p hp hrep j hj hq
  · exact match_zero_fix ⟨136, by decide⟩ ⟨107, by decide⟩ p hp j hj hq fz1_136_107 fz2_136_107
  · exact match_zero_fix ⟨137, by decide⟩ ⟨107, by decide⟩ p hp j hj hq fz1_137_107 fz2_137_107
  · exact match_zero_fix ⟨138, by decide⟩ ⟨107, by decide⟩ p hp j hj hq fz1_138_107 fz2_138_107
  · exact pair_139_107 p hp hrep j hj hq
  · exact match_zero_fix ⟨140, by decide⟩ ⟨107, by decide⟩ p hp j hj hq fz1_140_107 fz2_140_107
  · exact match_zero_fix ⟨141, by decide⟩ ⟨107, by decide⟩ p hp j hj hq fz1_141_107 fz2_141_107
  · exact match_zero_fix ⟨142, by decide⟩ ⟨107, by decide⟩ p hp j hj hq fz1_142_107 fz2_142_107
  · exact match_zero_fix ⟨143, by decide⟩ ⟨107, by decide⟩ p hp j hj hq fz1_143_107 fz2_143_107
  · exact match_zero_fix ⟨144, by decide⟩ ⟨107, by decide⟩ p hp j hj hq fz1_144_107 fz2_144_107
  · exact pair_145_107 p hp hrep j hj hq
  · exact match_zero_fix ⟨146, by decide⟩ ⟨107, by decide⟩ p hp j hj hq fz1_146_107 fz2_146_107
  · exact pair_147_107 p hp hrep j hj hq

theorem master_108 (p : Nat) (hp : p < (Q2.transData.getD 108 []).length)
    (hrep : (Q2.cosetIsRep.getD 108 []).getD p false = true)
    (rK : Fin 148) (j : Nat) (hj : j < (repChars.getD rK.val []).length)
    (hq : (normIsRep.getD rK.val []).getD j false = true) :
    species (Q2.reps (⟨108, by decide⟩ : Fin 148)) (colE2 ⟨108, by decide⟩ p hp)
        (rowE2 rK j hj hq)
      = species (reps (⟨108, by decide⟩ : Fin 148))
        (colE1 ⟨108, by decide⟩ p (transLenTr ⟨108, by decide⟩ p hp)) (rowE1 rK j hj) := by
  rcases rK with ⟨nK, hnK⟩; interval_cases nK
  · exact match_zero_len ⟨0, by decide⟩ ⟨108, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨1, by decide⟩ ⟨108, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨2, by decide⟩ ⟨108, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨3, by decide⟩ ⟨108, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨4, by decide⟩ ⟨108, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨5, by decide⟩ ⟨108, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨6, by decide⟩ ⟨108, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨7, by decide⟩ ⟨108, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨8, by decide⟩ ⟨108, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨9, by decide⟩ ⟨108, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨10, by decide⟩ ⟨108, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨11, by decide⟩ ⟨108, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨12, by decide⟩ ⟨108, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨13, by decide⟩ ⟨108, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨14, by decide⟩ ⟨108, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨15, by decide⟩ ⟨108, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨16, by decide⟩ ⟨108, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨17, by decide⟩ ⟨108, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨18, by decide⟩ ⟨108, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨19, by decide⟩ ⟨108, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨20, by decide⟩ ⟨108, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨21, by decide⟩ ⟨108, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨22, by decide⟩ ⟨108, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨23, by decide⟩ ⟨108, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨24, by decide⟩ ⟨108, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨25, by decide⟩ ⟨108, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨26, by decide⟩ ⟨108, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨27, by decide⟩ ⟨108, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨28, by decide⟩ ⟨108, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨29, by decide⟩ ⟨108, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨30, by decide⟩ ⟨108, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨31, by decide⟩ ⟨108, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨32, by decide⟩ ⟨108, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨33, by decide⟩ ⟨108, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨34, by decide⟩ ⟨108, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨35, by decide⟩ ⟨108, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨36, by decide⟩ ⟨108, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨37, by decide⟩ ⟨108, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨38, by decide⟩ ⟨108, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨39, by decide⟩ ⟨108, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨40, by decide⟩ ⟨108, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨41, by decide⟩ ⟨108, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨42, by decide⟩ ⟨108, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨43, by decide⟩ ⟨108, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨44, by decide⟩ ⟨108, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨45, by decide⟩ ⟨108, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨46, by decide⟩ ⟨108, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨47, by decide⟩ ⟨108, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨48, by decide⟩ ⟨108, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨49, by decide⟩ ⟨108, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨50, by decide⟩ ⟨108, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨51, by decide⟩ ⟨108, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨52, by decide⟩ ⟨108, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨53, by decide⟩ ⟨108, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨54, by decide⟩ ⟨108, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_fix ⟨55, by decide⟩ ⟨108, by decide⟩ p hp j hj hq fz1_55_108 fz2_55_108
  · exact match_zero_fix ⟨56, by decide⟩ ⟨108, by decide⟩ p hp j hj hq fz1_56_108 fz2_56_108
  · exact match_zero_fix ⟨57, by decide⟩ ⟨108, by decide⟩ p hp j hj hq fz1_57_108 fz2_57_108
  · exact match_zero_fix ⟨58, by decide⟩ ⟨108, by decide⟩ p hp j hj hq fz1_58_108 fz2_58_108
  · exact match_zero_fix ⟨59, by decide⟩ ⟨108, by decide⟩ p hp j hj hq fz1_59_108 fz2_59_108
  · exact match_zero_fix ⟨60, by decide⟩ ⟨108, by decide⟩ p hp j hj hq fz1_60_108 fz2_60_108
  · exact match_zero_fix ⟨61, by decide⟩ ⟨108, by decide⟩ p hp j hj hq fz1_61_108 fz2_61_108
  · exact match_zero_fix ⟨62, by decide⟩ ⟨108, by decide⟩ p hp j hj hq fz1_62_108 fz2_62_108
  · exact match_zero_fix ⟨63, by decide⟩ ⟨108, by decide⟩ p hp j hj hq fz1_63_108 fz2_63_108
  · exact match_zero_fix ⟨64, by decide⟩ ⟨108, by decide⟩ p hp j hj hq fz1_64_108 fz2_64_108
  · exact match_zero_fix ⟨65, by decide⟩ ⟨108, by decide⟩ p hp j hj hq fz1_65_108 fz2_65_108
  · exact match_zero_fix ⟨66, by decide⟩ ⟨108, by decide⟩ p hp j hj hq fz1_66_108 fz2_66_108
  · exact match_zero_fix ⟨67, by decide⟩ ⟨108, by decide⟩ p hp j hj hq fz1_67_108 fz2_67_108
  · exact match_zero_fix ⟨68, by decide⟩ ⟨108, by decide⟩ p hp j hj hq fz1_68_108 fz2_68_108
  · exact match_zero_fix ⟨69, by decide⟩ ⟨108, by decide⟩ p hp j hj hq fz1_69_108 fz2_69_108
  · exact match_zero_fix ⟨70, by decide⟩ ⟨108, by decide⟩ p hp j hj hq fz1_70_108 fz2_70_108
  · exact match_zero_fix ⟨71, by decide⟩ ⟨108, by decide⟩ p hp j hj hq fz1_71_108 fz2_71_108
  · exact match_zero_fix ⟨72, by decide⟩ ⟨108, by decide⟩ p hp j hj hq fz1_72_108 fz2_72_108
  · exact match_zero_fix ⟨73, by decide⟩ ⟨108, by decide⟩ p hp j hj hq fz1_73_108 fz2_73_108
  · exact match_zero_fix ⟨74, by decide⟩ ⟨108, by decide⟩ p hp j hj hq fz1_74_108 fz2_74_108
  · exact match_zero_fix ⟨75, by decide⟩ ⟨108, by decide⟩ p hp j hj hq fz1_75_108 fz2_75_108
  · exact match_zero_fix ⟨76, by decide⟩ ⟨108, by decide⟩ p hp j hj hq fz1_76_108 fz2_76_108
  · exact match_zero_fix ⟨77, by decide⟩ ⟨108, by decide⟩ p hp j hj hq fz1_77_108 fz2_77_108
  · exact match_zero_fix ⟨78, by decide⟩ ⟨108, by decide⟩ p hp j hj hq fz1_78_108 fz2_78_108
  · exact match_zero_fix ⟨79, by decide⟩ ⟨108, by decide⟩ p hp j hj hq fz1_79_108 fz2_79_108
  · exact match_zero_fix ⟨80, by decide⟩ ⟨108, by decide⟩ p hp j hj hq fz1_80_108 fz2_80_108
  · exact match_zero_fix ⟨81, by decide⟩ ⟨108, by decide⟩ p hp j hj hq fz1_81_108 fz2_81_108
  · exact match_zero_fix ⟨82, by decide⟩ ⟨108, by decide⟩ p hp j hj hq fz1_82_108 fz2_82_108
  · exact match_zero_fix ⟨83, by decide⟩ ⟨108, by decide⟩ p hp j hj hq fz1_83_108 fz2_83_108
  · exact match_zero_fix ⟨84, by decide⟩ ⟨108, by decide⟩ p hp j hj hq fz1_84_108 fz2_84_108
  · exact match_zero_fix ⟨85, by decide⟩ ⟨108, by decide⟩ p hp j hj hq fz1_85_108 fz2_85_108
  · exact match_zero_fix ⟨86, by decide⟩ ⟨108, by decide⟩ p hp j hj hq fz1_86_108 fz2_86_108
  · exact match_zero_fix ⟨87, by decide⟩ ⟨108, by decide⟩ p hp j hj hq fz1_87_108 fz2_87_108
  · exact match_zero_fix ⟨88, by decide⟩ ⟨108, by decide⟩ p hp j hj hq fz1_88_108 fz2_88_108
  · exact match_zero_fix ⟨89, by decide⟩ ⟨108, by decide⟩ p hp j hj hq fz1_89_108 fz2_89_108
  · exact match_zero_fix ⟨90, by decide⟩ ⟨108, by decide⟩ p hp j hj hq fz1_90_108 fz2_90_108
  · exact match_zero_fix ⟨91, by decide⟩ ⟨108, by decide⟩ p hp j hj hq fz1_91_108 fz2_91_108
  · exact match_zero_fix ⟨92, by decide⟩ ⟨108, by decide⟩ p hp j hj hq fz1_92_108 fz2_92_108
  · exact match_zero_fix ⟨93, by decide⟩ ⟨108, by decide⟩ p hp j hj hq fz1_93_108 fz2_93_108
  · exact match_zero_fix ⟨94, by decide⟩ ⟨108, by decide⟩ p hp j hj hq fz1_94_108 fz2_94_108
  · exact match_zero_fix ⟨95, by decide⟩ ⟨108, by decide⟩ p hp j hj hq fz1_95_108 fz2_95_108
  · exact match_zero_fix ⟨96, by decide⟩ ⟨108, by decide⟩ p hp j hj hq fz1_96_108 fz2_96_108
  · exact match_zero_fix ⟨97, by decide⟩ ⟨108, by decide⟩ p hp j hj hq fz1_97_108 fz2_97_108
  · exact match_zero_fix ⟨98, by decide⟩ ⟨108, by decide⟩ p hp j hj hq fz1_98_108 fz2_98_108
  · exact match_zero_fix ⟨99, by decide⟩ ⟨108, by decide⟩ p hp j hj hq fz1_99_108 fz2_99_108
  · exact match_zero_fix ⟨100, by decide⟩ ⟨108, by decide⟩ p hp j hj hq fz1_100_108 fz2_100_108
  · exact match_zero_fix ⟨101, by decide⟩ ⟨108, by decide⟩ p hp j hj hq fz1_101_108 fz2_101_108
  · exact match_zero_fix ⟨102, by decide⟩ ⟨108, by decide⟩ p hp j hj hq fz1_102_108 fz2_102_108
  · exact match_zero_fix ⟨103, by decide⟩ ⟨108, by decide⟩ p hp j hj hq fz1_103_108 fz2_103_108
  · exact match_zero_fix ⟨104, by decide⟩ ⟨108, by decide⟩ p hp j hj hq fz1_104_108 fz2_104_108
  · exact match_zero_fix ⟨105, by decide⟩ ⟨108, by decide⟩ p hp j hj hq fz1_105_108 fz2_105_108
  · exact match_zero_fix ⟨106, by decide⟩ ⟨108, by decide⟩ p hp j hj hq fz1_106_108 fz2_106_108
  · exact match_zero_fix ⟨107, by decide⟩ ⟨108, by decide⟩ p hp j hj hq fz1_107_108 fz2_107_108
  · exact pair_108_108 p hp hrep j hj hq
  · exact match_zero_fix ⟨109, by decide⟩ ⟨108, by decide⟩ p hp j hj hq fz1_109_108 fz2_109_108
  · exact match_zero_fix ⟨110, by decide⟩ ⟨108, by decide⟩ p hp j hj hq fz1_110_108 fz2_110_108
  · exact match_zero_fix ⟨111, by decide⟩ ⟨108, by decide⟩ p hp j hj hq fz1_111_108 fz2_111_108
  · exact match_zero_fix ⟨112, by decide⟩ ⟨108, by decide⟩ p hp j hj hq fz1_112_108 fz2_112_108
  · exact match_zero_fix ⟨113, by decide⟩ ⟨108, by decide⟩ p hp j hj hq fz1_113_108 fz2_113_108
  · exact match_zero_fix ⟨114, by decide⟩ ⟨108, by decide⟩ p hp j hj hq fz1_114_108 fz2_114_108
  · exact match_zero_fix ⟨115, by decide⟩ ⟨108, by decide⟩ p hp j hj hq fz1_115_108 fz2_115_108
  · exact match_zero_fix ⟨116, by decide⟩ ⟨108, by decide⟩ p hp j hj hq fz1_116_108 fz2_116_108
  · exact match_zero_fix ⟨117, by decide⟩ ⟨108, by decide⟩ p hp j hj hq fz1_117_108 fz2_117_108
  · exact match_zero_fix ⟨118, by decide⟩ ⟨108, by decide⟩ p hp j hj hq fz1_118_108 fz2_118_108
  · exact pair_119_108 p hp hrep j hj hq
  · exact match_zero_fix ⟨120, by decide⟩ ⟨108, by decide⟩ p hp j hj hq fz1_120_108 fz2_120_108
  · exact match_zero_fix ⟨121, by decide⟩ ⟨108, by decide⟩ p hp j hj hq fz1_121_108 fz2_121_108
  · exact match_zero_fix ⟨122, by decide⟩ ⟨108, by decide⟩ p hp j hj hq fz1_122_108 fz2_122_108
  · exact pair_123_108 p hp hrep j hj hq
  · exact match_zero_fix ⟨124, by decide⟩ ⟨108, by decide⟩ p hp j hj hq fz1_124_108 fz2_124_108
  · exact match_zero_fix ⟨125, by decide⟩ ⟨108, by decide⟩ p hp j hj hq fz1_125_108 fz2_125_108
  · exact match_zero_fix ⟨126, by decide⟩ ⟨108, by decide⟩ p hp j hj hq fz1_126_108 fz2_126_108
  · exact pair_127_108 p hp hrep j hj hq
  · exact match_zero_fix ⟨128, by decide⟩ ⟨108, by decide⟩ p hp j hj hq fz1_128_108 fz2_128_108
  · exact match_zero_fix ⟨129, by decide⟩ ⟨108, by decide⟩ p hp j hj hq fz1_129_108 fz2_129_108
  · exact match_zero_fix ⟨130, by decide⟩ ⟨108, by decide⟩ p hp j hj hq fz1_130_108 fz2_130_108
  · exact pair_131_108 p hp hrep j hj hq
  · exact match_zero_fix ⟨132, by decide⟩ ⟨108, by decide⟩ p hp j hj hq fz1_132_108 fz2_132_108
  · exact match_zero_fix ⟨133, by decide⟩ ⟨108, by decide⟩ p hp j hj hq fz1_133_108 fz2_133_108
  · exact match_zero_fix ⟨134, by decide⟩ ⟨108, by decide⟩ p hp j hj hq fz1_134_108 fz2_134_108
  · exact match_zero_fix ⟨135, by decide⟩ ⟨108, by decide⟩ p hp j hj hq fz1_135_108 fz2_135_108
  · exact match_zero_fix ⟨136, by decide⟩ ⟨108, by decide⟩ p hp j hj hq fz1_136_108 fz2_136_108
  · exact match_zero_fix ⟨137, by decide⟩ ⟨108, by decide⟩ p hp j hj hq fz1_137_108 fz2_137_108
  · exact match_zero_fix ⟨138, by decide⟩ ⟨108, by decide⟩ p hp j hj hq fz1_138_108 fz2_138_108
  · exact match_zero_fix ⟨139, by decide⟩ ⟨108, by decide⟩ p hp j hj hq fz1_139_108 fz2_139_108
  · exact pair_140_108 p hp hrep j hj hq
  · exact match_zero_fix ⟨141, by decide⟩ ⟨108, by decide⟩ p hp j hj hq fz1_141_108 fz2_141_108
  · exact match_zero_fix ⟨142, by decide⟩ ⟨108, by decide⟩ p hp j hj hq fz1_142_108 fz2_142_108
  · exact match_zero_fix ⟨143, by decide⟩ ⟨108, by decide⟩ p hp j hj hq fz1_143_108 fz2_143_108
  · exact match_zero_fix ⟨144, by decide⟩ ⟨108, by decide⟩ p hp j hj hq fz1_144_108 fz2_144_108
  · exact pair_145_108 p hp hrep j hj hq
  · exact match_zero_fix ⟨146, by decide⟩ ⟨108, by decide⟩ p hp j hj hq fz1_146_108 fz2_146_108
  · exact pair_147_108 p hp hrep j hj hq

theorem master_109 (p : Nat) (hp : p < (Q2.transData.getD 109 []).length)
    (hrep : (Q2.cosetIsRep.getD 109 []).getD p false = true)
    (rK : Fin 148) (j : Nat) (hj : j < (repChars.getD rK.val []).length)
    (hq : (normIsRep.getD rK.val []).getD j false = true) :
    species (Q2.reps (⟨109, by decide⟩ : Fin 148)) (colE2 ⟨109, by decide⟩ p hp)
        (rowE2 rK j hj hq)
      = species (reps (⟨109, by decide⟩ : Fin 148))
        (colE1 ⟨109, by decide⟩ p (transLenTr ⟨109, by decide⟩ p hp)) (rowE1 rK j hj) := by
  rcases rK with ⟨nK, hnK⟩; interval_cases nK
  · exact match_zero_len ⟨0, by decide⟩ ⟨109, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨1, by decide⟩ ⟨109, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨2, by decide⟩ ⟨109, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨3, by decide⟩ ⟨109, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨4, by decide⟩ ⟨109, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨5, by decide⟩ ⟨109, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨6, by decide⟩ ⟨109, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨7, by decide⟩ ⟨109, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨8, by decide⟩ ⟨109, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨9, by decide⟩ ⟨109, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨10, by decide⟩ ⟨109, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨11, by decide⟩ ⟨109, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨12, by decide⟩ ⟨109, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨13, by decide⟩ ⟨109, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨14, by decide⟩ ⟨109, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨15, by decide⟩ ⟨109, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨16, by decide⟩ ⟨109, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨17, by decide⟩ ⟨109, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨18, by decide⟩ ⟨109, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨19, by decide⟩ ⟨109, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨20, by decide⟩ ⟨109, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨21, by decide⟩ ⟨109, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨22, by decide⟩ ⟨109, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨23, by decide⟩ ⟨109, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨24, by decide⟩ ⟨109, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨25, by decide⟩ ⟨109, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨26, by decide⟩ ⟨109, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨27, by decide⟩ ⟨109, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨28, by decide⟩ ⟨109, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨29, by decide⟩ ⟨109, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨30, by decide⟩ ⟨109, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨31, by decide⟩ ⟨109, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨32, by decide⟩ ⟨109, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨33, by decide⟩ ⟨109, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨34, by decide⟩ ⟨109, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨35, by decide⟩ ⟨109, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨36, by decide⟩ ⟨109, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨37, by decide⟩ ⟨109, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨38, by decide⟩ ⟨109, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨39, by decide⟩ ⟨109, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨40, by decide⟩ ⟨109, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨41, by decide⟩ ⟨109, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨42, by decide⟩ ⟨109, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨43, by decide⟩ ⟨109, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨44, by decide⟩ ⟨109, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨45, by decide⟩ ⟨109, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨46, by decide⟩ ⟨109, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨47, by decide⟩ ⟨109, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨48, by decide⟩ ⟨109, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨49, by decide⟩ ⟨109, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨50, by decide⟩ ⟨109, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨51, by decide⟩ ⟨109, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨52, by decide⟩ ⟨109, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨53, by decide⟩ ⟨109, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨54, by decide⟩ ⟨109, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_fix ⟨55, by decide⟩ ⟨109, by decide⟩ p hp j hj hq fz1_55_109 fz2_55_109
  · exact match_zero_fix ⟨56, by decide⟩ ⟨109, by decide⟩ p hp j hj hq fz1_56_109 fz2_56_109
  · exact match_zero_fix ⟨57, by decide⟩ ⟨109, by decide⟩ p hp j hj hq fz1_57_109 fz2_57_109
  · exact match_zero_fix ⟨58, by decide⟩ ⟨109, by decide⟩ p hp j hj hq fz1_58_109 fz2_58_109
  · exact match_zero_fix ⟨59, by decide⟩ ⟨109, by decide⟩ p hp j hj hq fz1_59_109 fz2_59_109
  · exact match_zero_fix ⟨60, by decide⟩ ⟨109, by decide⟩ p hp j hj hq fz1_60_109 fz2_60_109
  · exact match_zero_fix ⟨61, by decide⟩ ⟨109, by decide⟩ p hp j hj hq fz1_61_109 fz2_61_109
  · exact match_zero_fix ⟨62, by decide⟩ ⟨109, by decide⟩ p hp j hj hq fz1_62_109 fz2_62_109
  · exact match_zero_fix ⟨63, by decide⟩ ⟨109, by decide⟩ p hp j hj hq fz1_63_109 fz2_63_109
  · exact match_zero_fix ⟨64, by decide⟩ ⟨109, by decide⟩ p hp j hj hq fz1_64_109 fz2_64_109
  · exact match_zero_fix ⟨65, by decide⟩ ⟨109, by decide⟩ p hp j hj hq fz1_65_109 fz2_65_109
  · exact match_zero_fix ⟨66, by decide⟩ ⟨109, by decide⟩ p hp j hj hq fz1_66_109 fz2_66_109
  · exact match_zero_fix ⟨67, by decide⟩ ⟨109, by decide⟩ p hp j hj hq fz1_67_109 fz2_67_109
  · exact match_zero_fix ⟨68, by decide⟩ ⟨109, by decide⟩ p hp j hj hq fz1_68_109 fz2_68_109
  · exact match_zero_fix ⟨69, by decide⟩ ⟨109, by decide⟩ p hp j hj hq fz1_69_109 fz2_69_109
  · exact match_zero_fix ⟨70, by decide⟩ ⟨109, by decide⟩ p hp j hj hq fz1_70_109 fz2_70_109
  · exact match_zero_fix ⟨71, by decide⟩ ⟨109, by decide⟩ p hp j hj hq fz1_71_109 fz2_71_109
  · exact match_zero_fix ⟨72, by decide⟩ ⟨109, by decide⟩ p hp j hj hq fz1_72_109 fz2_72_109
  · exact match_zero_fix ⟨73, by decide⟩ ⟨109, by decide⟩ p hp j hj hq fz1_73_109 fz2_73_109
  · exact match_zero_fix ⟨74, by decide⟩ ⟨109, by decide⟩ p hp j hj hq fz1_74_109 fz2_74_109
  · exact match_zero_fix ⟨75, by decide⟩ ⟨109, by decide⟩ p hp j hj hq fz1_75_109 fz2_75_109
  · exact match_zero_fix ⟨76, by decide⟩ ⟨109, by decide⟩ p hp j hj hq fz1_76_109 fz2_76_109
  · exact match_zero_fix ⟨77, by decide⟩ ⟨109, by decide⟩ p hp j hj hq fz1_77_109 fz2_77_109
  · exact match_zero_fix ⟨78, by decide⟩ ⟨109, by decide⟩ p hp j hj hq fz1_78_109 fz2_78_109
  · exact match_zero_fix ⟨79, by decide⟩ ⟨109, by decide⟩ p hp j hj hq fz1_79_109 fz2_79_109
  · exact match_zero_fix ⟨80, by decide⟩ ⟨109, by decide⟩ p hp j hj hq fz1_80_109 fz2_80_109
  · exact match_zero_fix ⟨81, by decide⟩ ⟨109, by decide⟩ p hp j hj hq fz1_81_109 fz2_81_109
  · exact match_zero_fix ⟨82, by decide⟩ ⟨109, by decide⟩ p hp j hj hq fz1_82_109 fz2_82_109
  · exact match_zero_fix ⟨83, by decide⟩ ⟨109, by decide⟩ p hp j hj hq fz1_83_109 fz2_83_109
  · exact match_zero_fix ⟨84, by decide⟩ ⟨109, by decide⟩ p hp j hj hq fz1_84_109 fz2_84_109
  · exact match_zero_fix ⟨85, by decide⟩ ⟨109, by decide⟩ p hp j hj hq fz1_85_109 fz2_85_109
  · exact match_zero_fix ⟨86, by decide⟩ ⟨109, by decide⟩ p hp j hj hq fz1_86_109 fz2_86_109
  · exact match_zero_fix ⟨87, by decide⟩ ⟨109, by decide⟩ p hp j hj hq fz1_87_109 fz2_87_109
  · exact match_zero_fix ⟨88, by decide⟩ ⟨109, by decide⟩ p hp j hj hq fz1_88_109 fz2_88_109
  · exact match_zero_fix ⟨89, by decide⟩ ⟨109, by decide⟩ p hp j hj hq fz1_89_109 fz2_89_109
  · exact match_zero_fix ⟨90, by decide⟩ ⟨109, by decide⟩ p hp j hj hq fz1_90_109 fz2_90_109
  · exact match_zero_fix ⟨91, by decide⟩ ⟨109, by decide⟩ p hp j hj hq fz1_91_109 fz2_91_109
  · exact match_zero_fix ⟨92, by decide⟩ ⟨109, by decide⟩ p hp j hj hq fz1_92_109 fz2_92_109
  · exact match_zero_fix ⟨93, by decide⟩ ⟨109, by decide⟩ p hp j hj hq fz1_93_109 fz2_93_109
  · exact match_zero_fix ⟨94, by decide⟩ ⟨109, by decide⟩ p hp j hj hq fz1_94_109 fz2_94_109
  · exact match_zero_fix ⟨95, by decide⟩ ⟨109, by decide⟩ p hp j hj hq fz1_95_109 fz2_95_109
  · exact match_zero_fix ⟨96, by decide⟩ ⟨109, by decide⟩ p hp j hj hq fz1_96_109 fz2_96_109
  · exact match_zero_fix ⟨97, by decide⟩ ⟨109, by decide⟩ p hp j hj hq fz1_97_109 fz2_97_109
  · exact match_zero_fix ⟨98, by decide⟩ ⟨109, by decide⟩ p hp j hj hq fz1_98_109 fz2_98_109
  · exact match_zero_fix ⟨99, by decide⟩ ⟨109, by decide⟩ p hp j hj hq fz1_99_109 fz2_99_109
  · exact match_zero_fix ⟨100, by decide⟩ ⟨109, by decide⟩ p hp j hj hq fz1_100_109 fz2_100_109
  · exact match_zero_fix ⟨101, by decide⟩ ⟨109, by decide⟩ p hp j hj hq fz1_101_109 fz2_101_109
  · exact match_zero_fix ⟨102, by decide⟩ ⟨109, by decide⟩ p hp j hj hq fz1_102_109 fz2_102_109
  · exact match_zero_fix ⟨103, by decide⟩ ⟨109, by decide⟩ p hp j hj hq fz1_103_109 fz2_103_109
  · exact match_zero_fix ⟨104, by decide⟩ ⟨109, by decide⟩ p hp j hj hq fz1_104_109 fz2_104_109
  · exact match_zero_fix ⟨105, by decide⟩ ⟨109, by decide⟩ p hp j hj hq fz1_105_109 fz2_105_109
  · exact match_zero_fix ⟨106, by decide⟩ ⟨109, by decide⟩ p hp j hj hq fz1_106_109 fz2_106_109
  · exact match_zero_fix ⟨107, by decide⟩ ⟨109, by decide⟩ p hp j hj hq fz1_107_109 fz2_107_109
  · exact match_zero_fix ⟨108, by decide⟩ ⟨109, by decide⟩ p hp j hj hq fz1_108_109 fz2_108_109
  · exact pair_109_109 p hp hrep j hj hq
  · exact match_zero_fix ⟨110, by decide⟩ ⟨109, by decide⟩ p hp j hj hq fz1_110_109 fz2_110_109
  · exact match_zero_fix ⟨111, by decide⟩ ⟨109, by decide⟩ p hp j hj hq fz1_111_109 fz2_111_109
  · exact match_zero_fix ⟨112, by decide⟩ ⟨109, by decide⟩ p hp j hj hq fz1_112_109 fz2_112_109
  · exact match_zero_fix ⟨113, by decide⟩ ⟨109, by decide⟩ p hp j hj hq fz1_113_109 fz2_113_109
  · exact match_zero_fix ⟨114, by decide⟩ ⟨109, by decide⟩ p hp j hj hq fz1_114_109 fz2_114_109
  · exact match_zero_fix ⟨115, by decide⟩ ⟨109, by decide⟩ p hp j hj hq fz1_115_109 fz2_115_109
  · exact match_zero_fix ⟨116, by decide⟩ ⟨109, by decide⟩ p hp j hj hq fz1_116_109 fz2_116_109
  · exact match_zero_fix ⟨117, by decide⟩ ⟨109, by decide⟩ p hp j hj hq fz1_117_109 fz2_117_109
  · exact match_zero_fix ⟨118, by decide⟩ ⟨109, by decide⟩ p hp j hj hq fz1_118_109 fz2_118_109
  · exact match_zero_fix ⟨119, by decide⟩ ⟨109, by decide⟩ p hp j hj hq fz1_119_109 fz2_119_109
  · exact pair_120_109 p hp hrep j hj hq
  · exact match_zero_fix ⟨121, by decide⟩ ⟨109, by decide⟩ p hp j hj hq fz1_121_109 fz2_121_109
  · exact match_zero_fix ⟨122, by decide⟩ ⟨109, by decide⟩ p hp j hj hq fz1_122_109 fz2_122_109
  · exact match_zero_fix ⟨123, by decide⟩ ⟨109, by decide⟩ p hp j hj hq fz1_123_109 fz2_123_109
  · exact pair_124_109 p hp hrep j hj hq
  · exact match_zero_fix ⟨125, by decide⟩ ⟨109, by decide⟩ p hp j hj hq fz1_125_109 fz2_125_109
  · exact match_zero_fix ⟨126, by decide⟩ ⟨109, by decide⟩ p hp j hj hq fz1_126_109 fz2_126_109
  · exact match_zero_fix ⟨127, by decide⟩ ⟨109, by decide⟩ p hp j hj hq fz1_127_109 fz2_127_109
  · exact pair_128_109 p hp hrep j hj hq
  · exact match_zero_fix ⟨129, by decide⟩ ⟨109, by decide⟩ p hp j hj hq fz1_129_109 fz2_129_109
  · exact match_zero_fix ⟨130, by decide⟩ ⟨109, by decide⟩ p hp j hj hq fz1_130_109 fz2_130_109
  · exact match_zero_fix ⟨131, by decide⟩ ⟨109, by decide⟩ p hp j hj hq fz1_131_109 fz2_131_109
  · exact pair_132_109 p hp hrep j hj hq
  · exact match_zero_fix ⟨133, by decide⟩ ⟨109, by decide⟩ p hp j hj hq fz1_133_109 fz2_133_109
  · exact match_zero_fix ⟨134, by decide⟩ ⟨109, by decide⟩ p hp j hj hq fz1_134_109 fz2_134_109
  · exact match_zero_fix ⟨135, by decide⟩ ⟨109, by decide⟩ p hp j hj hq fz1_135_109 fz2_135_109
  · exact pair_136_109 p hp hrep j hj hq
  · exact match_zero_fix ⟨137, by decide⟩ ⟨109, by decide⟩ p hp j hj hq fz1_137_109 fz2_137_109
  · exact match_zero_fix ⟨138, by decide⟩ ⟨109, by decide⟩ p hp j hj hq fz1_138_109 fz2_138_109
  · exact match_zero_fix ⟨139, by decide⟩ ⟨109, by decide⟩ p hp j hj hq fz1_139_109 fz2_139_109
  · exact match_zero_fix ⟨140, by decide⟩ ⟨109, by decide⟩ p hp j hj hq fz1_140_109 fz2_140_109
  · exact match_zero_fix ⟨141, by decide⟩ ⟨109, by decide⟩ p hp j hj hq fz1_141_109 fz2_141_109
  · exact match_zero_fix ⟨142, by decide⟩ ⟨109, by decide⟩ p hp j hj hq fz1_142_109 fz2_142_109
  · exact match_zero_fix ⟨143, by decide⟩ ⟨109, by decide⟩ p hp j hj hq fz1_143_109 fz2_143_109
  · exact match_zero_fix ⟨144, by decide⟩ ⟨109, by decide⟩ p hp j hj hq fz1_144_109 fz2_144_109
  · exact pair_145_109 p hp hrep j hj hq
  · exact match_zero_fix ⟨146, by decide⟩ ⟨109, by decide⟩ p hp j hj hq fz1_146_109 fz2_146_109
  · exact pair_147_109 p hp hrep j hj hq

theorem master_110 (p : Nat) (hp : p < (Q2.transData.getD 110 []).length)
    (hrep : (Q2.cosetIsRep.getD 110 []).getD p false = true)
    (rK : Fin 148) (j : Nat) (hj : j < (repChars.getD rK.val []).length)
    (hq : (normIsRep.getD rK.val []).getD j false = true) :
    species (Q2.reps (⟨110, by decide⟩ : Fin 148)) (colE2 ⟨110, by decide⟩ p hp)
        (rowE2 rK j hj hq)
      = species (reps (⟨110, by decide⟩ : Fin 148))
        (colE1 ⟨110, by decide⟩ p (transLenTr ⟨110, by decide⟩ p hp)) (rowE1 rK j hj) := by
  rcases rK with ⟨nK, hnK⟩; interval_cases nK
  · exact match_zero_len ⟨0, by decide⟩ ⟨110, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨1, by decide⟩ ⟨110, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨2, by decide⟩ ⟨110, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨3, by decide⟩ ⟨110, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨4, by decide⟩ ⟨110, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨5, by decide⟩ ⟨110, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨6, by decide⟩ ⟨110, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨7, by decide⟩ ⟨110, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨8, by decide⟩ ⟨110, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨9, by decide⟩ ⟨110, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨10, by decide⟩ ⟨110, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨11, by decide⟩ ⟨110, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨12, by decide⟩ ⟨110, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨13, by decide⟩ ⟨110, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨14, by decide⟩ ⟨110, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨15, by decide⟩ ⟨110, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨16, by decide⟩ ⟨110, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨17, by decide⟩ ⟨110, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨18, by decide⟩ ⟨110, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨19, by decide⟩ ⟨110, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨20, by decide⟩ ⟨110, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨21, by decide⟩ ⟨110, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨22, by decide⟩ ⟨110, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨23, by decide⟩ ⟨110, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨24, by decide⟩ ⟨110, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨25, by decide⟩ ⟨110, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨26, by decide⟩ ⟨110, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨27, by decide⟩ ⟨110, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨28, by decide⟩ ⟨110, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨29, by decide⟩ ⟨110, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨30, by decide⟩ ⟨110, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨31, by decide⟩ ⟨110, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨32, by decide⟩ ⟨110, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨33, by decide⟩ ⟨110, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨34, by decide⟩ ⟨110, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨35, by decide⟩ ⟨110, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨36, by decide⟩ ⟨110, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨37, by decide⟩ ⟨110, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨38, by decide⟩ ⟨110, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨39, by decide⟩ ⟨110, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨40, by decide⟩ ⟨110, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨41, by decide⟩ ⟨110, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨42, by decide⟩ ⟨110, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨43, by decide⟩ ⟨110, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨44, by decide⟩ ⟨110, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨45, by decide⟩ ⟨110, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨46, by decide⟩ ⟨110, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨47, by decide⟩ ⟨110, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨48, by decide⟩ ⟨110, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨49, by decide⟩ ⟨110, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨50, by decide⟩ ⟨110, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨51, by decide⟩ ⟨110, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨52, by decide⟩ ⟨110, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨53, by decide⟩ ⟨110, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨54, by decide⟩ ⟨110, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_fix ⟨55, by decide⟩ ⟨110, by decide⟩ p hp j hj hq fz1_55_110 fz2_55_110
  · exact match_zero_fix ⟨56, by decide⟩ ⟨110, by decide⟩ p hp j hj hq fz1_56_110 fz2_56_110
  · exact match_zero_fix ⟨57, by decide⟩ ⟨110, by decide⟩ p hp j hj hq fz1_57_110 fz2_57_110
  · exact match_zero_fix ⟨58, by decide⟩ ⟨110, by decide⟩ p hp j hj hq fz1_58_110 fz2_58_110
  · exact match_zero_fix ⟨59, by decide⟩ ⟨110, by decide⟩ p hp j hj hq fz1_59_110 fz2_59_110
  · exact match_zero_fix ⟨60, by decide⟩ ⟨110, by decide⟩ p hp j hj hq fz1_60_110 fz2_60_110
  · exact match_zero_fix ⟨61, by decide⟩ ⟨110, by decide⟩ p hp j hj hq fz1_61_110 fz2_61_110
  · exact match_zero_fix ⟨62, by decide⟩ ⟨110, by decide⟩ p hp j hj hq fz1_62_110 fz2_62_110
  · exact match_zero_fix ⟨63, by decide⟩ ⟨110, by decide⟩ p hp j hj hq fz1_63_110 fz2_63_110
  · exact match_zero_fix ⟨64, by decide⟩ ⟨110, by decide⟩ p hp j hj hq fz1_64_110 fz2_64_110
  · exact match_zero_fix ⟨65, by decide⟩ ⟨110, by decide⟩ p hp j hj hq fz1_65_110 fz2_65_110
  · exact match_zero_fix ⟨66, by decide⟩ ⟨110, by decide⟩ p hp j hj hq fz1_66_110 fz2_66_110
  · exact match_zero_fix ⟨67, by decide⟩ ⟨110, by decide⟩ p hp j hj hq fz1_67_110 fz2_67_110
  · exact match_zero_fix ⟨68, by decide⟩ ⟨110, by decide⟩ p hp j hj hq fz1_68_110 fz2_68_110
  · exact match_zero_fix ⟨69, by decide⟩ ⟨110, by decide⟩ p hp j hj hq fz1_69_110 fz2_69_110
  · exact match_zero_fix ⟨70, by decide⟩ ⟨110, by decide⟩ p hp j hj hq fz1_70_110 fz2_70_110
  · exact match_zero_fix ⟨71, by decide⟩ ⟨110, by decide⟩ p hp j hj hq fz1_71_110 fz2_71_110
  · exact match_zero_fix ⟨72, by decide⟩ ⟨110, by decide⟩ p hp j hj hq fz1_72_110 fz2_72_110
  · exact match_zero_fix ⟨73, by decide⟩ ⟨110, by decide⟩ p hp j hj hq fz1_73_110 fz2_73_110
  · exact match_zero_fix ⟨74, by decide⟩ ⟨110, by decide⟩ p hp j hj hq fz1_74_110 fz2_74_110
  · exact match_zero_fix ⟨75, by decide⟩ ⟨110, by decide⟩ p hp j hj hq fz1_75_110 fz2_75_110
  · exact match_zero_fix ⟨76, by decide⟩ ⟨110, by decide⟩ p hp j hj hq fz1_76_110 fz2_76_110
  · exact match_zero_fix ⟨77, by decide⟩ ⟨110, by decide⟩ p hp j hj hq fz1_77_110 fz2_77_110
  · exact match_zero_fix ⟨78, by decide⟩ ⟨110, by decide⟩ p hp j hj hq fz1_78_110 fz2_78_110
  · exact match_zero_fix ⟨79, by decide⟩ ⟨110, by decide⟩ p hp j hj hq fz1_79_110 fz2_79_110
  · exact match_zero_fix ⟨80, by decide⟩ ⟨110, by decide⟩ p hp j hj hq fz1_80_110 fz2_80_110
  · exact match_zero_fix ⟨81, by decide⟩ ⟨110, by decide⟩ p hp j hj hq fz1_81_110 fz2_81_110
  · exact match_zero_fix ⟨82, by decide⟩ ⟨110, by decide⟩ p hp j hj hq fz1_82_110 fz2_82_110
  · exact match_zero_fix ⟨83, by decide⟩ ⟨110, by decide⟩ p hp j hj hq fz1_83_110 fz2_83_110
  · exact match_zero_fix ⟨84, by decide⟩ ⟨110, by decide⟩ p hp j hj hq fz1_84_110 fz2_84_110
  · exact match_zero_fix ⟨85, by decide⟩ ⟨110, by decide⟩ p hp j hj hq fz1_85_110 fz2_85_110
  · exact match_zero_fix ⟨86, by decide⟩ ⟨110, by decide⟩ p hp j hj hq fz1_86_110 fz2_86_110
  · exact match_zero_fix ⟨87, by decide⟩ ⟨110, by decide⟩ p hp j hj hq fz1_87_110 fz2_87_110
  · exact match_zero_fix ⟨88, by decide⟩ ⟨110, by decide⟩ p hp j hj hq fz1_88_110 fz2_88_110
  · exact match_zero_fix ⟨89, by decide⟩ ⟨110, by decide⟩ p hp j hj hq fz1_89_110 fz2_89_110
  · exact match_zero_fix ⟨90, by decide⟩ ⟨110, by decide⟩ p hp j hj hq fz1_90_110 fz2_90_110
  · exact match_zero_fix ⟨91, by decide⟩ ⟨110, by decide⟩ p hp j hj hq fz1_91_110 fz2_91_110
  · exact match_zero_fix ⟨92, by decide⟩ ⟨110, by decide⟩ p hp j hj hq fz1_92_110 fz2_92_110
  · exact match_zero_fix ⟨93, by decide⟩ ⟨110, by decide⟩ p hp j hj hq fz1_93_110 fz2_93_110
  · exact match_zero_fix ⟨94, by decide⟩ ⟨110, by decide⟩ p hp j hj hq fz1_94_110 fz2_94_110
  · exact match_zero_fix ⟨95, by decide⟩ ⟨110, by decide⟩ p hp j hj hq fz1_95_110 fz2_95_110
  · exact match_zero_fix ⟨96, by decide⟩ ⟨110, by decide⟩ p hp j hj hq fz1_96_110 fz2_96_110
  · exact match_zero_fix ⟨97, by decide⟩ ⟨110, by decide⟩ p hp j hj hq fz1_97_110 fz2_97_110
  · exact match_zero_fix ⟨98, by decide⟩ ⟨110, by decide⟩ p hp j hj hq fz1_98_110 fz2_98_110
  · exact match_zero_fix ⟨99, by decide⟩ ⟨110, by decide⟩ p hp j hj hq fz1_99_110 fz2_99_110
  · exact match_zero_fix ⟨100, by decide⟩ ⟨110, by decide⟩ p hp j hj hq fz1_100_110 fz2_100_110
  · exact match_zero_fix ⟨101, by decide⟩ ⟨110, by decide⟩ p hp j hj hq fz1_101_110 fz2_101_110
  · exact match_zero_fix ⟨102, by decide⟩ ⟨110, by decide⟩ p hp j hj hq fz1_102_110 fz2_102_110
  · exact match_zero_fix ⟨103, by decide⟩ ⟨110, by decide⟩ p hp j hj hq fz1_103_110 fz2_103_110
  · exact match_zero_fix ⟨104, by decide⟩ ⟨110, by decide⟩ p hp j hj hq fz1_104_110 fz2_104_110
  · exact match_zero_fix ⟨105, by decide⟩ ⟨110, by decide⟩ p hp j hj hq fz1_105_110 fz2_105_110
  · exact match_zero_fix ⟨106, by decide⟩ ⟨110, by decide⟩ p hp j hj hq fz1_106_110 fz2_106_110
  · exact match_zero_fix ⟨107, by decide⟩ ⟨110, by decide⟩ p hp j hj hq fz1_107_110 fz2_107_110
  · exact match_zero_fix ⟨108, by decide⟩ ⟨110, by decide⟩ p hp j hj hq fz1_108_110 fz2_108_110
  · exact match_zero_fix ⟨109, by decide⟩ ⟨110, by decide⟩ p hp j hj hq fz1_109_110 fz2_109_110
  · exact pair_110_110 p hp hrep j hj hq
  · exact match_zero_fix ⟨111, by decide⟩ ⟨110, by decide⟩ p hp j hj hq fz1_111_110 fz2_111_110
  · exact match_zero_fix ⟨112, by decide⟩ ⟨110, by decide⟩ p hp j hj hq fz1_112_110 fz2_112_110
  · exact match_zero_fix ⟨113, by decide⟩ ⟨110, by decide⟩ p hp j hj hq fz1_113_110 fz2_113_110
  · exact match_zero_fix ⟨114, by decide⟩ ⟨110, by decide⟩ p hp j hj hq fz1_114_110 fz2_114_110
  · exact match_zero_fix ⟨115, by decide⟩ ⟨110, by decide⟩ p hp j hj hq fz1_115_110 fz2_115_110
  · exact pair_116_110 p hp hrep j hj hq
  · exact match_zero_fix ⟨117, by decide⟩ ⟨110, by decide⟩ p hp j hj hq fz1_117_110 fz2_117_110
  · exact match_zero_fix ⟨118, by decide⟩ ⟨110, by decide⟩ p hp j hj hq fz1_118_110 fz2_118_110
  · exact match_zero_fix ⟨119, by decide⟩ ⟨110, by decide⟩ p hp j hj hq fz1_119_110 fz2_119_110
  · exact match_zero_fix ⟨120, by decide⟩ ⟨110, by decide⟩ p hp j hj hq fz1_120_110 fz2_120_110
  · exact pair_121_110 p hp hrep j hj hq
  · exact match_zero_fix ⟨122, by decide⟩ ⟨110, by decide⟩ p hp j hj hq fz1_122_110 fz2_122_110
  · exact match_zero_fix ⟨123, by decide⟩ ⟨110, by decide⟩ p hp j hj hq fz1_123_110 fz2_123_110
  · exact match_zero_fix ⟨124, by decide⟩ ⟨110, by decide⟩ p hp j hj hq fz1_124_110 fz2_124_110
  · exact match_zero_fix ⟨125, by decide⟩ ⟨110, by decide⟩ p hp j hj hq fz1_125_110 fz2_125_110
  · exact pair_126_110 p hp hrep j hj hq
  · exact match_zero_fix ⟨127, by decide⟩ ⟨110, by decide⟩ p hp j hj hq fz1_127_110 fz2_127_110
  · exact match_zero_fix ⟨128, by decide⟩ ⟨110, by decide⟩ p hp j hj hq fz1_128_110 fz2_128_110
  · exact match_zero_fix ⟨129, by decide⟩ ⟨110, by decide⟩ p hp j hj hq fz1_129_110 fz2_129_110
  · exact match_zero_fix ⟨130, by decide⟩ ⟨110, by decide⟩ p hp j hj hq fz1_130_110 fz2_130_110
  · exact pair_131_110 p hp hrep j hj hq
  · exact match_zero_fix ⟨132, by decide⟩ ⟨110, by decide⟩ p hp j hj hq fz1_132_110 fz2_132_110
  · exact match_zero_fix ⟨133, by decide⟩ ⟨110, by decide⟩ p hp j hj hq fz1_133_110 fz2_133_110
  · exact match_zero_fix ⟨134, by decide⟩ ⟨110, by decide⟩ p hp j hj hq fz1_134_110 fz2_134_110
  · exact match_zero_fix ⟨135, by decide⟩ ⟨110, by decide⟩ p hp j hj hq fz1_135_110 fz2_135_110
  · exact pair_136_110 p hp hrep j hj hq
  · exact match_zero_fix ⟨137, by decide⟩ ⟨110, by decide⟩ p hp j hj hq fz1_137_110 fz2_137_110
  · exact match_zero_fix ⟨138, by decide⟩ ⟨110, by decide⟩ p hp j hj hq fz1_138_110 fz2_138_110
  · exact match_zero_fix ⟨139, by decide⟩ ⟨110, by decide⟩ p hp j hj hq fz1_139_110 fz2_139_110
  · exact match_zero_fix ⟨140, by decide⟩ ⟨110, by decide⟩ p hp j hj hq fz1_140_110 fz2_140_110
  · exact match_zero_fix ⟨141, by decide⟩ ⟨110, by decide⟩ p hp j hj hq fz1_141_110 fz2_141_110
  · exact match_zero_fix ⟨142, by decide⟩ ⟨110, by decide⟩ p hp j hj hq fz1_142_110 fz2_142_110
  · exact match_zero_fix ⟨143, by decide⟩ ⟨110, by decide⟩ p hp j hj hq fz1_143_110 fz2_143_110
  · exact match_zero_fix ⟨144, by decide⟩ ⟨110, by decide⟩ p hp j hj hq fz1_144_110 fz2_144_110
  · exact match_zero_fix ⟨145, by decide⟩ ⟨110, by decide⟩ p hp j hj hq fz1_145_110 fz2_145_110
  · exact pair_146_110 p hp hrep j hj hq
  · exact pair_147_110 p hp hrep j hj hq

theorem master_111 (p : Nat) (hp : p < (Q2.transData.getD 111 []).length)
    (hrep : (Q2.cosetIsRep.getD 111 []).getD p false = true)
    (rK : Fin 148) (j : Nat) (hj : j < (repChars.getD rK.val []).length)
    (hq : (normIsRep.getD rK.val []).getD j false = true) :
    species (Q2.reps (⟨111, by decide⟩ : Fin 148)) (colE2 ⟨111, by decide⟩ p hp)
        (rowE2 rK j hj hq)
      = species (reps (⟨111, by decide⟩ : Fin 148))
        (colE1 ⟨111, by decide⟩ p (transLenTr ⟨111, by decide⟩ p hp)) (rowE1 rK j hj) := by
  rcases rK with ⟨nK, hnK⟩; interval_cases nK
  · exact match_zero_len ⟨0, by decide⟩ ⟨111, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨1, by decide⟩ ⟨111, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨2, by decide⟩ ⟨111, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨3, by decide⟩ ⟨111, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨4, by decide⟩ ⟨111, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨5, by decide⟩ ⟨111, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨6, by decide⟩ ⟨111, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨7, by decide⟩ ⟨111, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨8, by decide⟩ ⟨111, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨9, by decide⟩ ⟨111, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨10, by decide⟩ ⟨111, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨11, by decide⟩ ⟨111, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨12, by decide⟩ ⟨111, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨13, by decide⟩ ⟨111, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨14, by decide⟩ ⟨111, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨15, by decide⟩ ⟨111, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨16, by decide⟩ ⟨111, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨17, by decide⟩ ⟨111, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨18, by decide⟩ ⟨111, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨19, by decide⟩ ⟨111, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨20, by decide⟩ ⟨111, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨21, by decide⟩ ⟨111, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨22, by decide⟩ ⟨111, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨23, by decide⟩ ⟨111, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨24, by decide⟩ ⟨111, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨25, by decide⟩ ⟨111, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨26, by decide⟩ ⟨111, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨27, by decide⟩ ⟨111, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨28, by decide⟩ ⟨111, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨29, by decide⟩ ⟨111, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨30, by decide⟩ ⟨111, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨31, by decide⟩ ⟨111, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨32, by decide⟩ ⟨111, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨33, by decide⟩ ⟨111, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨34, by decide⟩ ⟨111, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨35, by decide⟩ ⟨111, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨36, by decide⟩ ⟨111, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨37, by decide⟩ ⟨111, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨38, by decide⟩ ⟨111, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨39, by decide⟩ ⟨111, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨40, by decide⟩ ⟨111, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨41, by decide⟩ ⟨111, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨42, by decide⟩ ⟨111, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨43, by decide⟩ ⟨111, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨44, by decide⟩ ⟨111, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨45, by decide⟩ ⟨111, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨46, by decide⟩ ⟨111, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨47, by decide⟩ ⟨111, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨48, by decide⟩ ⟨111, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨49, by decide⟩ ⟨111, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨50, by decide⟩ ⟨111, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨51, by decide⟩ ⟨111, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨52, by decide⟩ ⟨111, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨53, by decide⟩ ⟨111, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨54, by decide⟩ ⟨111, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_fix ⟨55, by decide⟩ ⟨111, by decide⟩ p hp j hj hq fz1_55_111 fz2_55_111
  · exact match_zero_fix ⟨56, by decide⟩ ⟨111, by decide⟩ p hp j hj hq fz1_56_111 fz2_56_111
  · exact match_zero_fix ⟨57, by decide⟩ ⟨111, by decide⟩ p hp j hj hq fz1_57_111 fz2_57_111
  · exact match_zero_fix ⟨58, by decide⟩ ⟨111, by decide⟩ p hp j hj hq fz1_58_111 fz2_58_111
  · exact match_zero_fix ⟨59, by decide⟩ ⟨111, by decide⟩ p hp j hj hq fz1_59_111 fz2_59_111
  · exact match_zero_fix ⟨60, by decide⟩ ⟨111, by decide⟩ p hp j hj hq fz1_60_111 fz2_60_111
  · exact match_zero_fix ⟨61, by decide⟩ ⟨111, by decide⟩ p hp j hj hq fz1_61_111 fz2_61_111
  · exact match_zero_fix ⟨62, by decide⟩ ⟨111, by decide⟩ p hp j hj hq fz1_62_111 fz2_62_111
  · exact match_zero_fix ⟨63, by decide⟩ ⟨111, by decide⟩ p hp j hj hq fz1_63_111 fz2_63_111
  · exact match_zero_fix ⟨64, by decide⟩ ⟨111, by decide⟩ p hp j hj hq fz1_64_111 fz2_64_111
  · exact match_zero_fix ⟨65, by decide⟩ ⟨111, by decide⟩ p hp j hj hq fz1_65_111 fz2_65_111
  · exact match_zero_fix ⟨66, by decide⟩ ⟨111, by decide⟩ p hp j hj hq fz1_66_111 fz2_66_111
  · exact match_zero_fix ⟨67, by decide⟩ ⟨111, by decide⟩ p hp j hj hq fz1_67_111 fz2_67_111
  · exact match_zero_fix ⟨68, by decide⟩ ⟨111, by decide⟩ p hp j hj hq fz1_68_111 fz2_68_111
  · exact match_zero_fix ⟨69, by decide⟩ ⟨111, by decide⟩ p hp j hj hq fz1_69_111 fz2_69_111
  · exact match_zero_fix ⟨70, by decide⟩ ⟨111, by decide⟩ p hp j hj hq fz1_70_111 fz2_70_111
  · exact match_zero_fix ⟨71, by decide⟩ ⟨111, by decide⟩ p hp j hj hq fz1_71_111 fz2_71_111
  · exact match_zero_fix ⟨72, by decide⟩ ⟨111, by decide⟩ p hp j hj hq fz1_72_111 fz2_72_111
  · exact match_zero_fix ⟨73, by decide⟩ ⟨111, by decide⟩ p hp j hj hq fz1_73_111 fz2_73_111
  · exact match_zero_fix ⟨74, by decide⟩ ⟨111, by decide⟩ p hp j hj hq fz1_74_111 fz2_74_111
  · exact match_zero_fix ⟨75, by decide⟩ ⟨111, by decide⟩ p hp j hj hq fz1_75_111 fz2_75_111
  · exact match_zero_fix ⟨76, by decide⟩ ⟨111, by decide⟩ p hp j hj hq fz1_76_111 fz2_76_111
  · exact match_zero_fix ⟨77, by decide⟩ ⟨111, by decide⟩ p hp j hj hq fz1_77_111 fz2_77_111
  · exact match_zero_fix ⟨78, by decide⟩ ⟨111, by decide⟩ p hp j hj hq fz1_78_111 fz2_78_111
  · exact match_zero_fix ⟨79, by decide⟩ ⟨111, by decide⟩ p hp j hj hq fz1_79_111 fz2_79_111
  · exact match_zero_fix ⟨80, by decide⟩ ⟨111, by decide⟩ p hp j hj hq fz1_80_111 fz2_80_111
  · exact match_zero_fix ⟨81, by decide⟩ ⟨111, by decide⟩ p hp j hj hq fz1_81_111 fz2_81_111
  · exact match_zero_fix ⟨82, by decide⟩ ⟨111, by decide⟩ p hp j hj hq fz1_82_111 fz2_82_111
  · exact match_zero_fix ⟨83, by decide⟩ ⟨111, by decide⟩ p hp j hj hq fz1_83_111 fz2_83_111
  · exact match_zero_fix ⟨84, by decide⟩ ⟨111, by decide⟩ p hp j hj hq fz1_84_111 fz2_84_111
  · exact match_zero_fix ⟨85, by decide⟩ ⟨111, by decide⟩ p hp j hj hq fz1_85_111 fz2_85_111
  · exact match_zero_fix ⟨86, by decide⟩ ⟨111, by decide⟩ p hp j hj hq fz1_86_111 fz2_86_111
  · exact match_zero_fix ⟨87, by decide⟩ ⟨111, by decide⟩ p hp j hj hq fz1_87_111 fz2_87_111
  · exact match_zero_fix ⟨88, by decide⟩ ⟨111, by decide⟩ p hp j hj hq fz1_88_111 fz2_88_111
  · exact match_zero_fix ⟨89, by decide⟩ ⟨111, by decide⟩ p hp j hj hq fz1_89_111 fz2_89_111
  · exact match_zero_fix ⟨90, by decide⟩ ⟨111, by decide⟩ p hp j hj hq fz1_90_111 fz2_90_111
  · exact match_zero_fix ⟨91, by decide⟩ ⟨111, by decide⟩ p hp j hj hq fz1_91_111 fz2_91_111
  · exact match_zero_fix ⟨92, by decide⟩ ⟨111, by decide⟩ p hp j hj hq fz1_92_111 fz2_92_111
  · exact match_zero_fix ⟨93, by decide⟩ ⟨111, by decide⟩ p hp j hj hq fz1_93_111 fz2_93_111
  · exact match_zero_fix ⟨94, by decide⟩ ⟨111, by decide⟩ p hp j hj hq fz1_94_111 fz2_94_111
  · exact match_zero_fix ⟨95, by decide⟩ ⟨111, by decide⟩ p hp j hj hq fz1_95_111 fz2_95_111
  · exact match_zero_fix ⟨96, by decide⟩ ⟨111, by decide⟩ p hp j hj hq fz1_96_111 fz2_96_111
  · exact match_zero_fix ⟨97, by decide⟩ ⟨111, by decide⟩ p hp j hj hq fz1_97_111 fz2_97_111
  · exact match_zero_fix ⟨98, by decide⟩ ⟨111, by decide⟩ p hp j hj hq fz1_98_111 fz2_98_111
  · exact match_zero_fix ⟨99, by decide⟩ ⟨111, by decide⟩ p hp j hj hq fz1_99_111 fz2_99_111
  · exact match_zero_fix ⟨100, by decide⟩ ⟨111, by decide⟩ p hp j hj hq fz1_100_111 fz2_100_111
  · exact match_zero_fix ⟨101, by decide⟩ ⟨111, by decide⟩ p hp j hj hq fz1_101_111 fz2_101_111
  · exact match_zero_fix ⟨102, by decide⟩ ⟨111, by decide⟩ p hp j hj hq fz1_102_111 fz2_102_111
  · exact match_zero_fix ⟨103, by decide⟩ ⟨111, by decide⟩ p hp j hj hq fz1_103_111 fz2_103_111
  · exact match_zero_fix ⟨104, by decide⟩ ⟨111, by decide⟩ p hp j hj hq fz1_104_111 fz2_104_111
  · exact match_zero_fix ⟨105, by decide⟩ ⟨111, by decide⟩ p hp j hj hq fz1_105_111 fz2_105_111
  · exact match_zero_fix ⟨106, by decide⟩ ⟨111, by decide⟩ p hp j hj hq fz1_106_111 fz2_106_111
  · exact match_zero_fix ⟨107, by decide⟩ ⟨111, by decide⟩ p hp j hj hq fz1_107_111 fz2_107_111
  · exact match_zero_fix ⟨108, by decide⟩ ⟨111, by decide⟩ p hp j hj hq fz1_108_111 fz2_108_111
  · exact match_zero_fix ⟨109, by decide⟩ ⟨111, by decide⟩ p hp j hj hq fz1_109_111 fz2_109_111
  · exact match_zero_fix ⟨110, by decide⟩ ⟨111, by decide⟩ p hp j hj hq fz1_110_111 fz2_110_111
  · exact pair_111_111 p hp hrep j hj hq
  · exact match_zero_fix ⟨112, by decide⟩ ⟨111, by decide⟩ p hp j hj hq fz1_112_111 fz2_112_111
  · exact match_zero_fix ⟨113, by decide⟩ ⟨111, by decide⟩ p hp j hj hq fz1_113_111 fz2_113_111
  · exact match_zero_fix ⟨114, by decide⟩ ⟨111, by decide⟩ p hp j hj hq fz1_114_111 fz2_114_111
  · exact match_zero_fix ⟨115, by decide⟩ ⟨111, by decide⟩ p hp j hj hq fz1_115_111 fz2_115_111
  · exact match_zero_fix ⟨116, by decide⟩ ⟨111, by decide⟩ p hp j hj hq fz1_116_111 fz2_116_111
  · exact pair_117_111 p hp hrep j hj hq
  · exact match_zero_fix ⟨118, by decide⟩ ⟨111, by decide⟩ p hp j hj hq fz1_118_111 fz2_118_111
  · exact match_zero_fix ⟨119, by decide⟩ ⟨111, by decide⟩ p hp j hj hq fz1_119_111 fz2_119_111
  · exact match_zero_fix ⟨120, by decide⟩ ⟨111, by decide⟩ p hp j hj hq fz1_120_111 fz2_120_111
  · exact match_zero_fix ⟨121, by decide⟩ ⟨111, by decide⟩ p hp j hj hq fz1_121_111 fz2_121_111
  · exact pair_122_111 p hp hrep j hj hq
  · exact match_zero_fix ⟨123, by decide⟩ ⟨111, by decide⟩ p hp j hj hq fz1_123_111 fz2_123_111
  · exact match_zero_fix ⟨124, by decide⟩ ⟨111, by decide⟩ p hp j hj hq fz1_124_111 fz2_124_111
  · exact match_zero_fix ⟨125, by decide⟩ ⟨111, by decide⟩ p hp j hj hq fz1_125_111 fz2_125_111
  · exact match_zero_fix ⟨126, by decide⟩ ⟨111, by decide⟩ p hp j hj hq fz1_126_111 fz2_126_111
  · exact pair_127_111 p hp hrep j hj hq
  · exact match_zero_fix ⟨128, by decide⟩ ⟨111, by decide⟩ p hp j hj hq fz1_128_111 fz2_128_111
  · exact match_zero_fix ⟨129, by decide⟩ ⟨111, by decide⟩ p hp j hj hq fz1_129_111 fz2_129_111
  · exact match_zero_fix ⟨130, by decide⟩ ⟨111, by decide⟩ p hp j hj hq fz1_130_111 fz2_130_111
  · exact match_zero_fix ⟨131, by decide⟩ ⟨111, by decide⟩ p hp j hj hq fz1_131_111 fz2_131_111
  · exact pair_132_111 p hp hrep j hj hq
  · exact match_zero_fix ⟨133, by decide⟩ ⟨111, by decide⟩ p hp j hj hq fz1_133_111 fz2_133_111
  · exact match_zero_fix ⟨134, by decide⟩ ⟨111, by decide⟩ p hp j hj hq fz1_134_111 fz2_134_111
  · exact match_zero_fix ⟨135, by decide⟩ ⟨111, by decide⟩ p hp j hj hq fz1_135_111 fz2_135_111
  · exact match_zero_fix ⟨136, by decide⟩ ⟨111, by decide⟩ p hp j hj hq fz1_136_111 fz2_136_111
  · exact pair_137_111 p hp hrep j hj hq
  · exact match_zero_fix ⟨138, by decide⟩ ⟨111, by decide⟩ p hp j hj hq fz1_138_111 fz2_138_111
  · exact match_zero_fix ⟨139, by decide⟩ ⟨111, by decide⟩ p hp j hj hq fz1_139_111 fz2_139_111
  · exact match_zero_fix ⟨140, by decide⟩ ⟨111, by decide⟩ p hp j hj hq fz1_140_111 fz2_140_111
  · exact match_zero_fix ⟨141, by decide⟩ ⟨111, by decide⟩ p hp j hj hq fz1_141_111 fz2_141_111
  · exact match_zero_fix ⟨142, by decide⟩ ⟨111, by decide⟩ p hp j hj hq fz1_142_111 fz2_142_111
  · exact match_zero_fix ⟨143, by decide⟩ ⟨111, by decide⟩ p hp j hj hq fz1_143_111 fz2_143_111
  · exact match_zero_fix ⟨144, by decide⟩ ⟨111, by decide⟩ p hp j hj hq fz1_144_111 fz2_144_111
  · exact match_zero_fix ⟨145, by decide⟩ ⟨111, by decide⟩ p hp j hj hq fz1_145_111 fz2_145_111
  · exact pair_146_111 p hp hrep j hj hq
  · exact pair_147_111 p hp hrep j hj hq

end LeanDring.P5Presentation
