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
import LeanDring.P5.Data.MatchPair.C002
import LeanDring.P5.Data.MatchPair.C011
import LeanDring.P5.Data.MatchPair.C003
import LeanDring.P5.Data.MatchPair.C006
import LeanDring.P5.Data.MatchPair.C007

/-! # Stage-5 per-column-class master theorems, chunk 8 (auto-emitted).  -/

namespace LeanDring.P5Presentation

open MulAction Finset LeanDring.DRing LeanDring.MonGSet

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.style.longLine false

theorem master_64 (p : Nat) (hp : p < (Q2.transData.getD 64 []).length)
    (hrep : (Q2.cosetIsRep.getD 64 []).getD p false = true)
    (rK : Fin 148) (j : Nat) (hj : j < (repChars.getD rK.val []).length)
    (hq : (normIsRep.getD rK.val []).getD j false = true) :
    species (Q2.reps (⟨64, by decide⟩ : Fin 148)) (colE2 ⟨64, by decide⟩ p hp)
        (rowE2 rK j hj hq)
      = species (reps (⟨64, by decide⟩ : Fin 148))
        (colE1 ⟨64, by decide⟩ p (transLenTr ⟨64, by decide⟩ p hp)) (rowE1 rK j hj) := by
  rcases rK with ⟨nK, hnK⟩; interval_cases nK
  · exact match_zero_len ⟨0, by decide⟩ ⟨64, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨1, by decide⟩ ⟨64, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨2, by decide⟩ ⟨64, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨3, by decide⟩ ⟨64, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨4, by decide⟩ ⟨64, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨5, by decide⟩ ⟨64, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨6, by decide⟩ ⟨64, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨7, by decide⟩ ⟨64, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨8, by decide⟩ ⟨64, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨9, by decide⟩ ⟨64, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨10, by decide⟩ ⟨64, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨11, by decide⟩ ⟨64, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨12, by decide⟩ ⟨64, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨13, by decide⟩ ⟨64, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨14, by decide⟩ ⟨64, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨15, by decide⟩ ⟨64, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨16, by decide⟩ ⟨64, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨17, by decide⟩ ⟨64, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨18, by decide⟩ ⟨64, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨19, by decide⟩ ⟨64, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨20, by decide⟩ ⟨64, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨21, by decide⟩ ⟨64, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨22, by decide⟩ ⟨64, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨23, by decide⟩ ⟨64, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨24, by decide⟩ ⟨64, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨25, by decide⟩ ⟨64, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨26, by decide⟩ ⟨64, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨27, by decide⟩ ⟨64, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨28, by decide⟩ ⟨64, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨29, by decide⟩ ⟨64, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨30, by decide⟩ ⟨64, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨31, by decide⟩ ⟨64, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨32, by decide⟩ ⟨64, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨33, by decide⟩ ⟨64, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨34, by decide⟩ ⟨64, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨35, by decide⟩ ⟨64, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨36, by decide⟩ ⟨64, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨37, by decide⟩ ⟨64, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨38, by decide⟩ ⟨64, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨39, by decide⟩ ⟨64, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨40, by decide⟩ ⟨64, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨41, by decide⟩ ⟨64, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨42, by decide⟩ ⟨64, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨43, by decide⟩ ⟨64, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨44, by decide⟩ ⟨64, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨45, by decide⟩ ⟨64, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨46, by decide⟩ ⟨64, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨47, by decide⟩ ⟨64, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨48, by decide⟩ ⟨64, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨49, by decide⟩ ⟨64, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨50, by decide⟩ ⟨64, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨51, by decide⟩ ⟨64, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨52, by decide⟩ ⟨64, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨53, by decide⟩ ⟨64, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨54, by decide⟩ ⟨64, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_fix ⟨55, by decide⟩ ⟨64, by decide⟩ p hp j hj hq fz1_55_64 fz2_55_64
  · exact match_zero_fix ⟨56, by decide⟩ ⟨64, by decide⟩ p hp j hj hq fz1_56_64 fz2_56_64
  · exact match_zero_fix ⟨57, by decide⟩ ⟨64, by decide⟩ p hp j hj hq fz1_57_64 fz2_57_64
  · exact match_zero_fix ⟨58, by decide⟩ ⟨64, by decide⟩ p hp j hj hq fz1_58_64 fz2_58_64
  · exact match_zero_fix ⟨59, by decide⟩ ⟨64, by decide⟩ p hp j hj hq fz1_59_64 fz2_59_64
  · exact match_zero_fix ⟨60, by decide⟩ ⟨64, by decide⟩ p hp j hj hq fz1_60_64 fz2_60_64
  · exact match_zero_fix ⟨61, by decide⟩ ⟨64, by decide⟩ p hp j hj hq fz1_61_64 fz2_61_64
  · exact match_zero_fix ⟨62, by decide⟩ ⟨64, by decide⟩ p hp j hj hq fz1_62_64 fz2_62_64
  · exact match_zero_fix ⟨63, by decide⟩ ⟨64, by decide⟩ p hp j hj hq fz1_63_64 fz2_63_64
  · exact pair_64_64 p hp hrep j hj hq
  · exact match_zero_fix ⟨65, by decide⟩ ⟨64, by decide⟩ p hp j hj hq fz1_65_64 fz2_65_64
  · exact match_zero_fix ⟨66, by decide⟩ ⟨64, by decide⟩ p hp j hj hq fz1_66_64 fz2_66_64
  · exact match_zero_fix ⟨67, by decide⟩ ⟨64, by decide⟩ p hp j hj hq fz1_67_64 fz2_67_64
  · exact match_zero_fix ⟨68, by decide⟩ ⟨64, by decide⟩ p hp j hj hq fz1_68_64 fz2_68_64
  · exact match_zero_fix ⟨69, by decide⟩ ⟨64, by decide⟩ p hp j hj hq fz1_69_64 fz2_69_64
  · exact match_zero_fix ⟨70, by decide⟩ ⟨64, by decide⟩ p hp j hj hq fz1_70_64 fz2_70_64
  · exact match_zero_fix ⟨71, by decide⟩ ⟨64, by decide⟩ p hp j hj hq fz1_71_64 fz2_71_64
  · exact match_zero_fix ⟨72, by decide⟩ ⟨64, by decide⟩ p hp j hj hq fz1_72_64 fz2_72_64
  · exact match_zero_fix ⟨73, by decide⟩ ⟨64, by decide⟩ p hp j hj hq fz1_73_64 fz2_73_64
  · exact match_zero_fix ⟨74, by decide⟩ ⟨64, by decide⟩ p hp j hj hq fz1_74_64 fz2_74_64
  · exact match_zero_fix ⟨75, by decide⟩ ⟨64, by decide⟩ p hp j hj hq fz1_75_64 fz2_75_64
  · exact match_zero_fix ⟨76, by decide⟩ ⟨64, by decide⟩ p hp j hj hq fz1_76_64 fz2_76_64
  · exact match_zero_fix ⟨77, by decide⟩ ⟨64, by decide⟩ p hp j hj hq fz1_77_64 fz2_77_64
  · exact match_zero_fix ⟨78, by decide⟩ ⟨64, by decide⟩ p hp j hj hq fz1_78_64 fz2_78_64
  · exact match_zero_fix ⟨79, by decide⟩ ⟨64, by decide⟩ p hp j hj hq fz1_79_64 fz2_79_64
  · exact match_zero_fix ⟨80, by decide⟩ ⟨64, by decide⟩ p hp j hj hq fz1_80_64 fz2_80_64
  · exact match_zero_fix ⟨81, by decide⟩ ⟨64, by decide⟩ p hp j hj hq fz1_81_64 fz2_81_64
  · exact match_zero_fix ⟨82, by decide⟩ ⟨64, by decide⟩ p hp j hj hq fz1_82_64 fz2_82_64
  · exact match_zero_fix ⟨83, by decide⟩ ⟨64, by decide⟩ p hp j hj hq fz1_83_64 fz2_83_64
  · exact match_zero_fix ⟨84, by decide⟩ ⟨64, by decide⟩ p hp j hj hq fz1_84_64 fz2_84_64
  · exact match_zero_fix ⟨85, by decide⟩ ⟨64, by decide⟩ p hp j hj hq fz1_85_64 fz2_85_64
  · exact match_zero_fix ⟨86, by decide⟩ ⟨64, by decide⟩ p hp j hj hq fz1_86_64 fz2_86_64
  · exact match_zero_fix ⟨87, by decide⟩ ⟨64, by decide⟩ p hp j hj hq fz1_87_64 fz2_87_64
  · exact match_zero_fix ⟨88, by decide⟩ ⟨64, by decide⟩ p hp j hj hq fz1_88_64 fz2_88_64
  · exact match_zero_fix ⟨89, by decide⟩ ⟨64, by decide⟩ p hp j hj hq fz1_89_64 fz2_89_64
  · exact match_zero_fix ⟨90, by decide⟩ ⟨64, by decide⟩ p hp j hj hq fz1_90_64 fz2_90_64
  · exact match_zero_fix ⟨91, by decide⟩ ⟨64, by decide⟩ p hp j hj hq fz1_91_64 fz2_91_64
  · exact match_zero_fix ⟨92, by decide⟩ ⟨64, by decide⟩ p hp j hj hq fz1_92_64 fz2_92_64
  · exact match_zero_fix ⟨93, by decide⟩ ⟨64, by decide⟩ p hp j hj hq fz1_93_64 fz2_93_64
  · exact match_zero_fix ⟨94, by decide⟩ ⟨64, by decide⟩ p hp j hj hq fz1_94_64 fz2_94_64
  · exact match_zero_fix ⟨95, by decide⟩ ⟨64, by decide⟩ p hp j hj hq fz1_95_64 fz2_95_64
  · exact match_zero_fix ⟨96, by decide⟩ ⟨64, by decide⟩ p hp j hj hq fz1_96_64 fz2_96_64
  · exact match_zero_fix ⟨97, by decide⟩ ⟨64, by decide⟩ p hp j hj hq fz1_97_64 fz2_97_64
  · exact match_zero_fix ⟨98, by decide⟩ ⟨64, by decide⟩ p hp j hj hq fz1_98_64 fz2_98_64
  · exact match_zero_fix ⟨99, by decide⟩ ⟨64, by decide⟩ p hp j hj hq fz1_99_64 fz2_99_64
  · exact match_zero_fix ⟨100, by decide⟩ ⟨64, by decide⟩ p hp j hj hq fz1_100_64 fz2_100_64
  · exact match_zero_fix ⟨101, by decide⟩ ⟨64, by decide⟩ p hp j hj hq fz1_101_64 fz2_101_64
  · exact match_zero_fix ⟨102, by decide⟩ ⟨64, by decide⟩ p hp j hj hq fz1_102_64 fz2_102_64
  · exact match_zero_fix ⟨103, by decide⟩ ⟨64, by decide⟩ p hp j hj hq fz1_103_64 fz2_103_64
  · exact match_zero_fix ⟨104, by decide⟩ ⟨64, by decide⟩ p hp j hj hq fz1_104_64 fz2_104_64
  · exact match_zero_fix ⟨105, by decide⟩ ⟨64, by decide⟩ p hp j hj hq fz1_105_64 fz2_105_64
  · exact match_zero_fix ⟨106, by decide⟩ ⟨64, by decide⟩ p hp j hj hq fz1_106_64 fz2_106_64
  · exact match_zero_fix ⟨107, by decide⟩ ⟨64, by decide⟩ p hp j hj hq fz1_107_64 fz2_107_64
  · exact match_zero_fix ⟨108, by decide⟩ ⟨64, by decide⟩ p hp j hj hq fz1_108_64 fz2_108_64
  · exact match_zero_fix ⟨109, by decide⟩ ⟨64, by decide⟩ p hp j hj hq fz1_109_64 fz2_109_64
  · exact match_zero_fix ⟨110, by decide⟩ ⟨64, by decide⟩ p hp j hj hq fz1_110_64 fz2_110_64
  · exact match_zero_fix ⟨111, by decide⟩ ⟨64, by decide⟩ p hp j hj hq fz1_111_64 fz2_111_64
  · exact match_zero_fix ⟨112, by decide⟩ ⟨64, by decide⟩ p hp j hj hq fz1_112_64 fz2_112_64
  · exact match_zero_fix ⟨113, by decide⟩ ⟨64, by decide⟩ p hp j hj hq fz1_113_64 fz2_113_64
  · exact match_zero_fix ⟨114, by decide⟩ ⟨64, by decide⟩ p hp j hj hq fz1_114_64 fz2_114_64
  · exact match_zero_fix ⟨115, by decide⟩ ⟨64, by decide⟩ p hp j hj hq fz1_115_64 fz2_115_64
  · exact match_zero_fix ⟨116, by decide⟩ ⟨64, by decide⟩ p hp j hj hq fz1_116_64 fz2_116_64
  · exact pair_117_64 p hp hrep j hj hq
  · exact match_zero_fix ⟨118, by decide⟩ ⟨64, by decide⟩ p hp j hj hq fz1_118_64 fz2_118_64
  · exact match_zero_fix ⟨119, by decide⟩ ⟨64, by decide⟩ p hp j hj hq fz1_119_64 fz2_119_64
  · exact match_zero_fix ⟨120, by decide⟩ ⟨64, by decide⟩ p hp j hj hq fz1_120_64 fz2_120_64
  · exact match_zero_fix ⟨121, by decide⟩ ⟨64, by decide⟩ p hp j hj hq fz1_121_64 fz2_121_64
  · exact match_zero_fix ⟨122, by decide⟩ ⟨64, by decide⟩ p hp j hj hq fz1_122_64 fz2_122_64
  · exact match_zero_fix ⟨123, by decide⟩ ⟨64, by decide⟩ p hp j hj hq fz1_123_64 fz2_123_64
  · exact match_zero_fix ⟨124, by decide⟩ ⟨64, by decide⟩ p hp j hj hq fz1_124_64 fz2_124_64
  · exact match_zero_fix ⟨125, by decide⟩ ⟨64, by decide⟩ p hp j hj hq fz1_125_64 fz2_125_64
  · exact match_zero_fix ⟨126, by decide⟩ ⟨64, by decide⟩ p hp j hj hq fz1_126_64 fz2_126_64
  · exact match_zero_fix ⟨127, by decide⟩ ⟨64, by decide⟩ p hp j hj hq fz1_127_64 fz2_127_64
  · exact match_zero_fix ⟨128, by decide⟩ ⟨64, by decide⟩ p hp j hj hq fz1_128_64 fz2_128_64
  · exact match_zero_fix ⟨129, by decide⟩ ⟨64, by decide⟩ p hp j hj hq fz1_129_64 fz2_129_64
  · exact match_zero_fix ⟨130, by decide⟩ ⟨64, by decide⟩ p hp j hj hq fz1_130_64 fz2_130_64
  · exact match_zero_fix ⟨131, by decide⟩ ⟨64, by decide⟩ p hp j hj hq fz1_131_64 fz2_131_64
  · exact match_zero_fix ⟨132, by decide⟩ ⟨64, by decide⟩ p hp j hj hq fz1_132_64 fz2_132_64
  · exact match_zero_fix ⟨133, by decide⟩ ⟨64, by decide⟩ p hp j hj hq fz1_133_64 fz2_133_64
  · exact match_zero_fix ⟨134, by decide⟩ ⟨64, by decide⟩ p hp j hj hq fz1_134_64 fz2_134_64
  · exact match_zero_fix ⟨135, by decide⟩ ⟨64, by decide⟩ p hp j hj hq fz1_135_64 fz2_135_64
  · exact match_zero_fix ⟨136, by decide⟩ ⟨64, by decide⟩ p hp j hj hq fz1_136_64 fz2_136_64
  · exact match_zero_fix ⟨137, by decide⟩ ⟨64, by decide⟩ p hp j hj hq fz1_137_64 fz2_137_64
  · exact match_zero_fix ⟨138, by decide⟩ ⟨64, by decide⟩ p hp j hj hq fz1_138_64 fz2_138_64
  · exact match_zero_fix ⟨139, by decide⟩ ⟨64, by decide⟩ p hp j hj hq fz1_139_64 fz2_139_64
  · exact match_zero_fix ⟨140, by decide⟩ ⟨64, by decide⟩ p hp j hj hq fz1_140_64 fz2_140_64
  · exact match_zero_fix ⟨141, by decide⟩ ⟨64, by decide⟩ p hp j hj hq fz1_141_64 fz2_141_64
  · exact match_zero_fix ⟨142, by decide⟩ ⟨64, by decide⟩ p hp j hj hq fz1_142_64 fz2_142_64
  · exact match_zero_fix ⟨143, by decide⟩ ⟨64, by decide⟩ p hp j hj hq fz1_143_64 fz2_143_64
  · exact match_zero_fix ⟨144, by decide⟩ ⟨64, by decide⟩ p hp j hj hq fz1_144_64 fz2_144_64
  · exact match_zero_fix ⟨145, by decide⟩ ⟨64, by decide⟩ p hp j hj hq fz1_145_64 fz2_145_64
  · exact match_zero_fix ⟨146, by decide⟩ ⟨64, by decide⟩ p hp j hj hq fz1_146_64 fz2_146_64
  · exact pair_147_64 p hp hrep j hj hq

theorem master_65 (p : Nat) (hp : p < (Q2.transData.getD 65 []).length)
    (hrep : (Q2.cosetIsRep.getD 65 []).getD p false = true)
    (rK : Fin 148) (j : Nat) (hj : j < (repChars.getD rK.val []).length)
    (hq : (normIsRep.getD rK.val []).getD j false = true) :
    species (Q2.reps (⟨65, by decide⟩ : Fin 148)) (colE2 ⟨65, by decide⟩ p hp)
        (rowE2 rK j hj hq)
      = species (reps (⟨65, by decide⟩ : Fin 148))
        (colE1 ⟨65, by decide⟩ p (transLenTr ⟨65, by decide⟩ p hp)) (rowE1 rK j hj) := by
  rcases rK with ⟨nK, hnK⟩; interval_cases nK
  · exact match_zero_len ⟨0, by decide⟩ ⟨65, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨1, by decide⟩ ⟨65, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨2, by decide⟩ ⟨65, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨3, by decide⟩ ⟨65, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨4, by decide⟩ ⟨65, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨5, by decide⟩ ⟨65, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨6, by decide⟩ ⟨65, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨7, by decide⟩ ⟨65, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨8, by decide⟩ ⟨65, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨9, by decide⟩ ⟨65, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨10, by decide⟩ ⟨65, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨11, by decide⟩ ⟨65, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨12, by decide⟩ ⟨65, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨13, by decide⟩ ⟨65, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨14, by decide⟩ ⟨65, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨15, by decide⟩ ⟨65, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨16, by decide⟩ ⟨65, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨17, by decide⟩ ⟨65, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨18, by decide⟩ ⟨65, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨19, by decide⟩ ⟨65, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨20, by decide⟩ ⟨65, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨21, by decide⟩ ⟨65, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨22, by decide⟩ ⟨65, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨23, by decide⟩ ⟨65, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨24, by decide⟩ ⟨65, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨25, by decide⟩ ⟨65, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨26, by decide⟩ ⟨65, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨27, by decide⟩ ⟨65, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨28, by decide⟩ ⟨65, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨29, by decide⟩ ⟨65, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨30, by decide⟩ ⟨65, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨31, by decide⟩ ⟨65, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨32, by decide⟩ ⟨65, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨33, by decide⟩ ⟨65, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨34, by decide⟩ ⟨65, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨35, by decide⟩ ⟨65, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨36, by decide⟩ ⟨65, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨37, by decide⟩ ⟨65, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨38, by decide⟩ ⟨65, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨39, by decide⟩ ⟨65, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨40, by decide⟩ ⟨65, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨41, by decide⟩ ⟨65, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨42, by decide⟩ ⟨65, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨43, by decide⟩ ⟨65, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨44, by decide⟩ ⟨65, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨45, by decide⟩ ⟨65, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨46, by decide⟩ ⟨65, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨47, by decide⟩ ⟨65, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨48, by decide⟩ ⟨65, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨49, by decide⟩ ⟨65, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨50, by decide⟩ ⟨65, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨51, by decide⟩ ⟨65, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨52, by decide⟩ ⟨65, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨53, by decide⟩ ⟨65, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨54, by decide⟩ ⟨65, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_fix ⟨55, by decide⟩ ⟨65, by decide⟩ p hp j hj hq fz1_55_65 fz2_55_65
  · exact match_zero_fix ⟨56, by decide⟩ ⟨65, by decide⟩ p hp j hj hq fz1_56_65 fz2_56_65
  · exact match_zero_fix ⟨57, by decide⟩ ⟨65, by decide⟩ p hp j hj hq fz1_57_65 fz2_57_65
  · exact match_zero_fix ⟨58, by decide⟩ ⟨65, by decide⟩ p hp j hj hq fz1_58_65 fz2_58_65
  · exact match_zero_fix ⟨59, by decide⟩ ⟨65, by decide⟩ p hp j hj hq fz1_59_65 fz2_59_65
  · exact match_zero_fix ⟨60, by decide⟩ ⟨65, by decide⟩ p hp j hj hq fz1_60_65 fz2_60_65
  · exact match_zero_fix ⟨61, by decide⟩ ⟨65, by decide⟩ p hp j hj hq fz1_61_65 fz2_61_65
  · exact match_zero_fix ⟨62, by decide⟩ ⟨65, by decide⟩ p hp j hj hq fz1_62_65 fz2_62_65
  · exact match_zero_fix ⟨63, by decide⟩ ⟨65, by decide⟩ p hp j hj hq fz1_63_65 fz2_63_65
  · exact match_zero_fix ⟨64, by decide⟩ ⟨65, by decide⟩ p hp j hj hq fz1_64_65 fz2_64_65
  · exact pair_65_65 p hp hrep j hj hq
  · exact match_zero_fix ⟨66, by decide⟩ ⟨65, by decide⟩ p hp j hj hq fz1_66_65 fz2_66_65
  · exact match_zero_fix ⟨67, by decide⟩ ⟨65, by decide⟩ p hp j hj hq fz1_67_65 fz2_67_65
  · exact match_zero_fix ⟨68, by decide⟩ ⟨65, by decide⟩ p hp j hj hq fz1_68_65 fz2_68_65
  · exact match_zero_fix ⟨69, by decide⟩ ⟨65, by decide⟩ p hp j hj hq fz1_69_65 fz2_69_65
  · exact match_zero_fix ⟨70, by decide⟩ ⟨65, by decide⟩ p hp j hj hq fz1_70_65 fz2_70_65
  · exact match_zero_fix ⟨71, by decide⟩ ⟨65, by decide⟩ p hp j hj hq fz1_71_65 fz2_71_65
  · exact match_zero_fix ⟨72, by decide⟩ ⟨65, by decide⟩ p hp j hj hq fz1_72_65 fz2_72_65
  · exact match_zero_fix ⟨73, by decide⟩ ⟨65, by decide⟩ p hp j hj hq fz1_73_65 fz2_73_65
  · exact match_zero_fix ⟨74, by decide⟩ ⟨65, by decide⟩ p hp j hj hq fz1_74_65 fz2_74_65
  · exact match_zero_fix ⟨75, by decide⟩ ⟨65, by decide⟩ p hp j hj hq fz1_75_65 fz2_75_65
  · exact match_zero_fix ⟨76, by decide⟩ ⟨65, by decide⟩ p hp j hj hq fz1_76_65 fz2_76_65
  · exact match_zero_fix ⟨77, by decide⟩ ⟨65, by decide⟩ p hp j hj hq fz1_77_65 fz2_77_65
  · exact match_zero_fix ⟨78, by decide⟩ ⟨65, by decide⟩ p hp j hj hq fz1_78_65 fz2_78_65
  · exact match_zero_fix ⟨79, by decide⟩ ⟨65, by decide⟩ p hp j hj hq fz1_79_65 fz2_79_65
  · exact match_zero_fix ⟨80, by decide⟩ ⟨65, by decide⟩ p hp j hj hq fz1_80_65 fz2_80_65
  · exact match_zero_fix ⟨81, by decide⟩ ⟨65, by decide⟩ p hp j hj hq fz1_81_65 fz2_81_65
  · exact match_zero_fix ⟨82, by decide⟩ ⟨65, by decide⟩ p hp j hj hq fz1_82_65 fz2_82_65
  · exact match_zero_fix ⟨83, by decide⟩ ⟨65, by decide⟩ p hp j hj hq fz1_83_65 fz2_83_65
  · exact match_zero_fix ⟨84, by decide⟩ ⟨65, by decide⟩ p hp j hj hq fz1_84_65 fz2_84_65
  · exact match_zero_fix ⟨85, by decide⟩ ⟨65, by decide⟩ p hp j hj hq fz1_85_65 fz2_85_65
  · exact match_zero_fix ⟨86, by decide⟩ ⟨65, by decide⟩ p hp j hj hq fz1_86_65 fz2_86_65
  · exact match_zero_fix ⟨87, by decide⟩ ⟨65, by decide⟩ p hp j hj hq fz1_87_65 fz2_87_65
  · exact match_zero_fix ⟨88, by decide⟩ ⟨65, by decide⟩ p hp j hj hq fz1_88_65 fz2_88_65
  · exact match_zero_fix ⟨89, by decide⟩ ⟨65, by decide⟩ p hp j hj hq fz1_89_65 fz2_89_65
  · exact match_zero_fix ⟨90, by decide⟩ ⟨65, by decide⟩ p hp j hj hq fz1_90_65 fz2_90_65
  · exact match_zero_fix ⟨91, by decide⟩ ⟨65, by decide⟩ p hp j hj hq fz1_91_65 fz2_91_65
  · exact match_zero_fix ⟨92, by decide⟩ ⟨65, by decide⟩ p hp j hj hq fz1_92_65 fz2_92_65
  · exact match_zero_fix ⟨93, by decide⟩ ⟨65, by decide⟩ p hp j hj hq fz1_93_65 fz2_93_65
  · exact match_zero_fix ⟨94, by decide⟩ ⟨65, by decide⟩ p hp j hj hq fz1_94_65 fz2_94_65
  · exact match_zero_fix ⟨95, by decide⟩ ⟨65, by decide⟩ p hp j hj hq fz1_95_65 fz2_95_65
  · exact match_zero_fix ⟨96, by decide⟩ ⟨65, by decide⟩ p hp j hj hq fz1_96_65 fz2_96_65
  · exact match_zero_fix ⟨97, by decide⟩ ⟨65, by decide⟩ p hp j hj hq fz1_97_65 fz2_97_65
  · exact match_zero_fix ⟨98, by decide⟩ ⟨65, by decide⟩ p hp j hj hq fz1_98_65 fz2_98_65
  · exact match_zero_fix ⟨99, by decide⟩ ⟨65, by decide⟩ p hp j hj hq fz1_99_65 fz2_99_65
  · exact match_zero_fix ⟨100, by decide⟩ ⟨65, by decide⟩ p hp j hj hq fz1_100_65 fz2_100_65
  · exact match_zero_fix ⟨101, by decide⟩ ⟨65, by decide⟩ p hp j hj hq fz1_101_65 fz2_101_65
  · exact match_zero_fix ⟨102, by decide⟩ ⟨65, by decide⟩ p hp j hj hq fz1_102_65 fz2_102_65
  · exact match_zero_fix ⟨103, by decide⟩ ⟨65, by decide⟩ p hp j hj hq fz1_103_65 fz2_103_65
  · exact match_zero_fix ⟨104, by decide⟩ ⟨65, by decide⟩ p hp j hj hq fz1_104_65 fz2_104_65
  · exact match_zero_fix ⟨105, by decide⟩ ⟨65, by decide⟩ p hp j hj hq fz1_105_65 fz2_105_65
  · exact match_zero_fix ⟨106, by decide⟩ ⟨65, by decide⟩ p hp j hj hq fz1_106_65 fz2_106_65
  · exact match_zero_fix ⟨107, by decide⟩ ⟨65, by decide⟩ p hp j hj hq fz1_107_65 fz2_107_65
  · exact match_zero_fix ⟨108, by decide⟩ ⟨65, by decide⟩ p hp j hj hq fz1_108_65 fz2_108_65
  · exact match_zero_fix ⟨109, by decide⟩ ⟨65, by decide⟩ p hp j hj hq fz1_109_65 fz2_109_65
  · exact match_zero_fix ⟨110, by decide⟩ ⟨65, by decide⟩ p hp j hj hq fz1_110_65 fz2_110_65
  · exact match_zero_fix ⟨111, by decide⟩ ⟨65, by decide⟩ p hp j hj hq fz1_111_65 fz2_111_65
  · exact match_zero_fix ⟨112, by decide⟩ ⟨65, by decide⟩ p hp j hj hq fz1_112_65 fz2_112_65
  · exact match_zero_fix ⟨113, by decide⟩ ⟨65, by decide⟩ p hp j hj hq fz1_113_65 fz2_113_65
  · exact match_zero_fix ⟨114, by decide⟩ ⟨65, by decide⟩ p hp j hj hq fz1_114_65 fz2_114_65
  · exact match_zero_fix ⟨115, by decide⟩ ⟨65, by decide⟩ p hp j hj hq fz1_115_65 fz2_115_65
  · exact match_zero_fix ⟨116, by decide⟩ ⟨65, by decide⟩ p hp j hj hq fz1_116_65 fz2_116_65
  · exact match_zero_fix ⟨117, by decide⟩ ⟨65, by decide⟩ p hp j hj hq fz1_117_65 fz2_117_65
  · exact pair_118_65 p hp hrep j hj hq
  · exact match_zero_fix ⟨119, by decide⟩ ⟨65, by decide⟩ p hp j hj hq fz1_119_65 fz2_119_65
  · exact match_zero_fix ⟨120, by decide⟩ ⟨65, by decide⟩ p hp j hj hq fz1_120_65 fz2_120_65
  · exact match_zero_fix ⟨121, by decide⟩ ⟨65, by decide⟩ p hp j hj hq fz1_121_65 fz2_121_65
  · exact match_zero_fix ⟨122, by decide⟩ ⟨65, by decide⟩ p hp j hj hq fz1_122_65 fz2_122_65
  · exact match_zero_fix ⟨123, by decide⟩ ⟨65, by decide⟩ p hp j hj hq fz1_123_65 fz2_123_65
  · exact match_zero_fix ⟨124, by decide⟩ ⟨65, by decide⟩ p hp j hj hq fz1_124_65 fz2_124_65
  · exact match_zero_fix ⟨125, by decide⟩ ⟨65, by decide⟩ p hp j hj hq fz1_125_65 fz2_125_65
  · exact match_zero_fix ⟨126, by decide⟩ ⟨65, by decide⟩ p hp j hj hq fz1_126_65 fz2_126_65
  · exact match_zero_fix ⟨127, by decide⟩ ⟨65, by decide⟩ p hp j hj hq fz1_127_65 fz2_127_65
  · exact match_zero_fix ⟨128, by decide⟩ ⟨65, by decide⟩ p hp j hj hq fz1_128_65 fz2_128_65
  · exact match_zero_fix ⟨129, by decide⟩ ⟨65, by decide⟩ p hp j hj hq fz1_129_65 fz2_129_65
  · exact match_zero_fix ⟨130, by decide⟩ ⟨65, by decide⟩ p hp j hj hq fz1_130_65 fz2_130_65
  · exact match_zero_fix ⟨131, by decide⟩ ⟨65, by decide⟩ p hp j hj hq fz1_131_65 fz2_131_65
  · exact match_zero_fix ⟨132, by decide⟩ ⟨65, by decide⟩ p hp j hj hq fz1_132_65 fz2_132_65
  · exact match_zero_fix ⟨133, by decide⟩ ⟨65, by decide⟩ p hp j hj hq fz1_133_65 fz2_133_65
  · exact match_zero_fix ⟨134, by decide⟩ ⟨65, by decide⟩ p hp j hj hq fz1_134_65 fz2_134_65
  · exact match_zero_fix ⟨135, by decide⟩ ⟨65, by decide⟩ p hp j hj hq fz1_135_65 fz2_135_65
  · exact match_zero_fix ⟨136, by decide⟩ ⟨65, by decide⟩ p hp j hj hq fz1_136_65 fz2_136_65
  · exact match_zero_fix ⟨137, by decide⟩ ⟨65, by decide⟩ p hp j hj hq fz1_137_65 fz2_137_65
  · exact match_zero_fix ⟨138, by decide⟩ ⟨65, by decide⟩ p hp j hj hq fz1_138_65 fz2_138_65
  · exact match_zero_fix ⟨139, by decide⟩ ⟨65, by decide⟩ p hp j hj hq fz1_139_65 fz2_139_65
  · exact match_zero_fix ⟨140, by decide⟩ ⟨65, by decide⟩ p hp j hj hq fz1_140_65 fz2_140_65
  · exact match_zero_fix ⟨141, by decide⟩ ⟨65, by decide⟩ p hp j hj hq fz1_141_65 fz2_141_65
  · exact match_zero_fix ⟨142, by decide⟩ ⟨65, by decide⟩ p hp j hj hq fz1_142_65 fz2_142_65
  · exact match_zero_fix ⟨143, by decide⟩ ⟨65, by decide⟩ p hp j hj hq fz1_143_65 fz2_143_65
  · exact match_zero_fix ⟨144, by decide⟩ ⟨65, by decide⟩ p hp j hj hq fz1_144_65 fz2_144_65
  · exact match_zero_fix ⟨145, by decide⟩ ⟨65, by decide⟩ p hp j hj hq fz1_145_65 fz2_145_65
  · exact match_zero_fix ⟨146, by decide⟩ ⟨65, by decide⟩ p hp j hj hq fz1_146_65 fz2_146_65
  · exact pair_147_65 p hp hrep j hj hq

theorem master_66 (p : Nat) (hp : p < (Q2.transData.getD 66 []).length)
    (hrep : (Q2.cosetIsRep.getD 66 []).getD p false = true)
    (rK : Fin 148) (j : Nat) (hj : j < (repChars.getD rK.val []).length)
    (hq : (normIsRep.getD rK.val []).getD j false = true) :
    species (Q2.reps (⟨66, by decide⟩ : Fin 148)) (colE2 ⟨66, by decide⟩ p hp)
        (rowE2 rK j hj hq)
      = species (reps (⟨66, by decide⟩ : Fin 148))
        (colE1 ⟨66, by decide⟩ p (transLenTr ⟨66, by decide⟩ p hp)) (rowE1 rK j hj) := by
  rcases rK with ⟨nK, hnK⟩; interval_cases nK
  · exact match_zero_len ⟨0, by decide⟩ ⟨66, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨1, by decide⟩ ⟨66, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨2, by decide⟩ ⟨66, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨3, by decide⟩ ⟨66, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨4, by decide⟩ ⟨66, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨5, by decide⟩ ⟨66, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨6, by decide⟩ ⟨66, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨7, by decide⟩ ⟨66, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨8, by decide⟩ ⟨66, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨9, by decide⟩ ⟨66, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨10, by decide⟩ ⟨66, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨11, by decide⟩ ⟨66, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨12, by decide⟩ ⟨66, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨13, by decide⟩ ⟨66, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨14, by decide⟩ ⟨66, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨15, by decide⟩ ⟨66, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨16, by decide⟩ ⟨66, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨17, by decide⟩ ⟨66, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨18, by decide⟩ ⟨66, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨19, by decide⟩ ⟨66, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨20, by decide⟩ ⟨66, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨21, by decide⟩ ⟨66, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨22, by decide⟩ ⟨66, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨23, by decide⟩ ⟨66, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨24, by decide⟩ ⟨66, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨25, by decide⟩ ⟨66, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨26, by decide⟩ ⟨66, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨27, by decide⟩ ⟨66, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨28, by decide⟩ ⟨66, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨29, by decide⟩ ⟨66, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨30, by decide⟩ ⟨66, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨31, by decide⟩ ⟨66, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨32, by decide⟩ ⟨66, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨33, by decide⟩ ⟨66, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨34, by decide⟩ ⟨66, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨35, by decide⟩ ⟨66, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨36, by decide⟩ ⟨66, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨37, by decide⟩ ⟨66, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨38, by decide⟩ ⟨66, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨39, by decide⟩ ⟨66, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨40, by decide⟩ ⟨66, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨41, by decide⟩ ⟨66, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨42, by decide⟩ ⟨66, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨43, by decide⟩ ⟨66, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨44, by decide⟩ ⟨66, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨45, by decide⟩ ⟨66, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨46, by decide⟩ ⟨66, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨47, by decide⟩ ⟨66, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨48, by decide⟩ ⟨66, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨49, by decide⟩ ⟨66, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨50, by decide⟩ ⟨66, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨51, by decide⟩ ⟨66, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨52, by decide⟩ ⟨66, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨53, by decide⟩ ⟨66, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨54, by decide⟩ ⟨66, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_fix ⟨55, by decide⟩ ⟨66, by decide⟩ p hp j hj hq fz1_55_66 fz2_55_66
  · exact match_zero_fix ⟨56, by decide⟩ ⟨66, by decide⟩ p hp j hj hq fz1_56_66 fz2_56_66
  · exact match_zero_fix ⟨57, by decide⟩ ⟨66, by decide⟩ p hp j hj hq fz1_57_66 fz2_57_66
  · exact match_zero_fix ⟨58, by decide⟩ ⟨66, by decide⟩ p hp j hj hq fz1_58_66 fz2_58_66
  · exact match_zero_fix ⟨59, by decide⟩ ⟨66, by decide⟩ p hp j hj hq fz1_59_66 fz2_59_66
  · exact match_zero_fix ⟨60, by decide⟩ ⟨66, by decide⟩ p hp j hj hq fz1_60_66 fz2_60_66
  · exact match_zero_fix ⟨61, by decide⟩ ⟨66, by decide⟩ p hp j hj hq fz1_61_66 fz2_61_66
  · exact match_zero_fix ⟨62, by decide⟩ ⟨66, by decide⟩ p hp j hj hq fz1_62_66 fz2_62_66
  · exact match_zero_fix ⟨63, by decide⟩ ⟨66, by decide⟩ p hp j hj hq fz1_63_66 fz2_63_66
  · exact match_zero_fix ⟨64, by decide⟩ ⟨66, by decide⟩ p hp j hj hq fz1_64_66 fz2_64_66
  · exact match_zero_fix ⟨65, by decide⟩ ⟨66, by decide⟩ p hp j hj hq fz1_65_66 fz2_65_66
  · exact pair_66_66 p hp hrep j hj hq
  · exact match_zero_fix ⟨67, by decide⟩ ⟨66, by decide⟩ p hp j hj hq fz1_67_66 fz2_67_66
  · exact match_zero_fix ⟨68, by decide⟩ ⟨66, by decide⟩ p hp j hj hq fz1_68_66 fz2_68_66
  · exact match_zero_fix ⟨69, by decide⟩ ⟨66, by decide⟩ p hp j hj hq fz1_69_66 fz2_69_66
  · exact match_zero_fix ⟨70, by decide⟩ ⟨66, by decide⟩ p hp j hj hq fz1_70_66 fz2_70_66
  · exact match_zero_fix ⟨71, by decide⟩ ⟨66, by decide⟩ p hp j hj hq fz1_71_66 fz2_71_66
  · exact match_zero_fix ⟨72, by decide⟩ ⟨66, by decide⟩ p hp j hj hq fz1_72_66 fz2_72_66
  · exact match_zero_fix ⟨73, by decide⟩ ⟨66, by decide⟩ p hp j hj hq fz1_73_66 fz2_73_66
  · exact match_zero_fix ⟨74, by decide⟩ ⟨66, by decide⟩ p hp j hj hq fz1_74_66 fz2_74_66
  · exact match_zero_fix ⟨75, by decide⟩ ⟨66, by decide⟩ p hp j hj hq fz1_75_66 fz2_75_66
  · exact match_zero_fix ⟨76, by decide⟩ ⟨66, by decide⟩ p hp j hj hq fz1_76_66 fz2_76_66
  · exact match_zero_fix ⟨77, by decide⟩ ⟨66, by decide⟩ p hp j hj hq fz1_77_66 fz2_77_66
  · exact match_zero_fix ⟨78, by decide⟩ ⟨66, by decide⟩ p hp j hj hq fz1_78_66 fz2_78_66
  · exact match_zero_fix ⟨79, by decide⟩ ⟨66, by decide⟩ p hp j hj hq fz1_79_66 fz2_79_66
  · exact match_zero_fix ⟨80, by decide⟩ ⟨66, by decide⟩ p hp j hj hq fz1_80_66 fz2_80_66
  · exact match_zero_fix ⟨81, by decide⟩ ⟨66, by decide⟩ p hp j hj hq fz1_81_66 fz2_81_66
  · exact match_zero_fix ⟨82, by decide⟩ ⟨66, by decide⟩ p hp j hj hq fz1_82_66 fz2_82_66
  · exact match_zero_fix ⟨83, by decide⟩ ⟨66, by decide⟩ p hp j hj hq fz1_83_66 fz2_83_66
  · exact match_zero_fix ⟨84, by decide⟩ ⟨66, by decide⟩ p hp j hj hq fz1_84_66 fz2_84_66
  · exact match_zero_fix ⟨85, by decide⟩ ⟨66, by decide⟩ p hp j hj hq fz1_85_66 fz2_85_66
  · exact match_zero_fix ⟨86, by decide⟩ ⟨66, by decide⟩ p hp j hj hq fz1_86_66 fz2_86_66
  · exact match_zero_fix ⟨87, by decide⟩ ⟨66, by decide⟩ p hp j hj hq fz1_87_66 fz2_87_66
  · exact match_zero_fix ⟨88, by decide⟩ ⟨66, by decide⟩ p hp j hj hq fz1_88_66 fz2_88_66
  · exact match_zero_fix ⟨89, by decide⟩ ⟨66, by decide⟩ p hp j hj hq fz1_89_66 fz2_89_66
  · exact match_zero_fix ⟨90, by decide⟩ ⟨66, by decide⟩ p hp j hj hq fz1_90_66 fz2_90_66
  · exact match_zero_fix ⟨91, by decide⟩ ⟨66, by decide⟩ p hp j hj hq fz1_91_66 fz2_91_66
  · exact match_zero_fix ⟨92, by decide⟩ ⟨66, by decide⟩ p hp j hj hq fz1_92_66 fz2_92_66
  · exact match_zero_fix ⟨93, by decide⟩ ⟨66, by decide⟩ p hp j hj hq fz1_93_66 fz2_93_66
  · exact match_zero_fix ⟨94, by decide⟩ ⟨66, by decide⟩ p hp j hj hq fz1_94_66 fz2_94_66
  · exact match_zero_fix ⟨95, by decide⟩ ⟨66, by decide⟩ p hp j hj hq fz1_95_66 fz2_95_66
  · exact match_zero_fix ⟨96, by decide⟩ ⟨66, by decide⟩ p hp j hj hq fz1_96_66 fz2_96_66
  · exact match_zero_fix ⟨97, by decide⟩ ⟨66, by decide⟩ p hp j hj hq fz1_97_66 fz2_97_66
  · exact match_zero_fix ⟨98, by decide⟩ ⟨66, by decide⟩ p hp j hj hq fz1_98_66 fz2_98_66
  · exact match_zero_fix ⟨99, by decide⟩ ⟨66, by decide⟩ p hp j hj hq fz1_99_66 fz2_99_66
  · exact match_zero_fix ⟨100, by decide⟩ ⟨66, by decide⟩ p hp j hj hq fz1_100_66 fz2_100_66
  · exact match_zero_fix ⟨101, by decide⟩ ⟨66, by decide⟩ p hp j hj hq fz1_101_66 fz2_101_66
  · exact match_zero_fix ⟨102, by decide⟩ ⟨66, by decide⟩ p hp j hj hq fz1_102_66 fz2_102_66
  · exact match_zero_fix ⟨103, by decide⟩ ⟨66, by decide⟩ p hp j hj hq fz1_103_66 fz2_103_66
  · exact match_zero_fix ⟨104, by decide⟩ ⟨66, by decide⟩ p hp j hj hq fz1_104_66 fz2_104_66
  · exact match_zero_fix ⟨105, by decide⟩ ⟨66, by decide⟩ p hp j hj hq fz1_105_66 fz2_105_66
  · exact match_zero_fix ⟨106, by decide⟩ ⟨66, by decide⟩ p hp j hj hq fz1_106_66 fz2_106_66
  · exact match_zero_fix ⟨107, by decide⟩ ⟨66, by decide⟩ p hp j hj hq fz1_107_66 fz2_107_66
  · exact match_zero_fix ⟨108, by decide⟩ ⟨66, by decide⟩ p hp j hj hq fz1_108_66 fz2_108_66
  · exact match_zero_fix ⟨109, by decide⟩ ⟨66, by decide⟩ p hp j hj hq fz1_109_66 fz2_109_66
  · exact match_zero_fix ⟨110, by decide⟩ ⟨66, by decide⟩ p hp j hj hq fz1_110_66 fz2_110_66
  · exact match_zero_fix ⟨111, by decide⟩ ⟨66, by decide⟩ p hp j hj hq fz1_111_66 fz2_111_66
  · exact match_zero_fix ⟨112, by decide⟩ ⟨66, by decide⟩ p hp j hj hq fz1_112_66 fz2_112_66
  · exact match_zero_fix ⟨113, by decide⟩ ⟨66, by decide⟩ p hp j hj hq fz1_113_66 fz2_113_66
  · exact match_zero_fix ⟨114, by decide⟩ ⟨66, by decide⟩ p hp j hj hq fz1_114_66 fz2_114_66
  · exact match_zero_fix ⟨115, by decide⟩ ⟨66, by decide⟩ p hp j hj hq fz1_115_66 fz2_115_66
  · exact match_zero_fix ⟨116, by decide⟩ ⟨66, by decide⟩ p hp j hj hq fz1_116_66 fz2_116_66
  · exact match_zero_fix ⟨117, by decide⟩ ⟨66, by decide⟩ p hp j hj hq fz1_117_66 fz2_117_66
  · exact pair_118_66 p hp hrep j hj hq
  · exact match_zero_fix ⟨119, by decide⟩ ⟨66, by decide⟩ p hp j hj hq fz1_119_66 fz2_119_66
  · exact match_zero_fix ⟨120, by decide⟩ ⟨66, by decide⟩ p hp j hj hq fz1_120_66 fz2_120_66
  · exact match_zero_fix ⟨121, by decide⟩ ⟨66, by decide⟩ p hp j hj hq fz1_121_66 fz2_121_66
  · exact match_zero_fix ⟨122, by decide⟩ ⟨66, by decide⟩ p hp j hj hq fz1_122_66 fz2_122_66
  · exact match_zero_fix ⟨123, by decide⟩ ⟨66, by decide⟩ p hp j hj hq fz1_123_66 fz2_123_66
  · exact match_zero_fix ⟨124, by decide⟩ ⟨66, by decide⟩ p hp j hj hq fz1_124_66 fz2_124_66
  · exact match_zero_fix ⟨125, by decide⟩ ⟨66, by decide⟩ p hp j hj hq fz1_125_66 fz2_125_66
  · exact match_zero_fix ⟨126, by decide⟩ ⟨66, by decide⟩ p hp j hj hq fz1_126_66 fz2_126_66
  · exact match_zero_fix ⟨127, by decide⟩ ⟨66, by decide⟩ p hp j hj hq fz1_127_66 fz2_127_66
  · exact match_zero_fix ⟨128, by decide⟩ ⟨66, by decide⟩ p hp j hj hq fz1_128_66 fz2_128_66
  · exact match_zero_fix ⟨129, by decide⟩ ⟨66, by decide⟩ p hp j hj hq fz1_129_66 fz2_129_66
  · exact match_zero_fix ⟨130, by decide⟩ ⟨66, by decide⟩ p hp j hj hq fz1_130_66 fz2_130_66
  · exact match_zero_fix ⟨131, by decide⟩ ⟨66, by decide⟩ p hp j hj hq fz1_131_66 fz2_131_66
  · exact match_zero_fix ⟨132, by decide⟩ ⟨66, by decide⟩ p hp j hj hq fz1_132_66 fz2_132_66
  · exact match_zero_fix ⟨133, by decide⟩ ⟨66, by decide⟩ p hp j hj hq fz1_133_66 fz2_133_66
  · exact match_zero_fix ⟨134, by decide⟩ ⟨66, by decide⟩ p hp j hj hq fz1_134_66 fz2_134_66
  · exact match_zero_fix ⟨135, by decide⟩ ⟨66, by decide⟩ p hp j hj hq fz1_135_66 fz2_135_66
  · exact match_zero_fix ⟨136, by decide⟩ ⟨66, by decide⟩ p hp j hj hq fz1_136_66 fz2_136_66
  · exact match_zero_fix ⟨137, by decide⟩ ⟨66, by decide⟩ p hp j hj hq fz1_137_66 fz2_137_66
  · exact match_zero_fix ⟨138, by decide⟩ ⟨66, by decide⟩ p hp j hj hq fz1_138_66 fz2_138_66
  · exact match_zero_fix ⟨139, by decide⟩ ⟨66, by decide⟩ p hp j hj hq fz1_139_66 fz2_139_66
  · exact match_zero_fix ⟨140, by decide⟩ ⟨66, by decide⟩ p hp j hj hq fz1_140_66 fz2_140_66
  · exact match_zero_fix ⟨141, by decide⟩ ⟨66, by decide⟩ p hp j hj hq fz1_141_66 fz2_141_66
  · exact match_zero_fix ⟨142, by decide⟩ ⟨66, by decide⟩ p hp j hj hq fz1_142_66 fz2_142_66
  · exact match_zero_fix ⟨143, by decide⟩ ⟨66, by decide⟩ p hp j hj hq fz1_143_66 fz2_143_66
  · exact match_zero_fix ⟨144, by decide⟩ ⟨66, by decide⟩ p hp j hj hq fz1_144_66 fz2_144_66
  · exact match_zero_fix ⟨145, by decide⟩ ⟨66, by decide⟩ p hp j hj hq fz1_145_66 fz2_145_66
  · exact match_zero_fix ⟨146, by decide⟩ ⟨66, by decide⟩ p hp j hj hq fz1_146_66 fz2_146_66
  · exact pair_147_66 p hp hrep j hj hq

theorem master_67 (p : Nat) (hp : p < (Q2.transData.getD 67 []).length)
    (hrep : (Q2.cosetIsRep.getD 67 []).getD p false = true)
    (rK : Fin 148) (j : Nat) (hj : j < (repChars.getD rK.val []).length)
    (hq : (normIsRep.getD rK.val []).getD j false = true) :
    species (Q2.reps (⟨67, by decide⟩ : Fin 148)) (colE2 ⟨67, by decide⟩ p hp)
        (rowE2 rK j hj hq)
      = species (reps (⟨67, by decide⟩ : Fin 148))
        (colE1 ⟨67, by decide⟩ p (transLenTr ⟨67, by decide⟩ p hp)) (rowE1 rK j hj) := by
  rcases rK with ⟨nK, hnK⟩; interval_cases nK
  · exact match_zero_len ⟨0, by decide⟩ ⟨67, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨1, by decide⟩ ⟨67, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨2, by decide⟩ ⟨67, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨3, by decide⟩ ⟨67, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨4, by decide⟩ ⟨67, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨5, by decide⟩ ⟨67, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨6, by decide⟩ ⟨67, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨7, by decide⟩ ⟨67, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨8, by decide⟩ ⟨67, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨9, by decide⟩ ⟨67, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨10, by decide⟩ ⟨67, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨11, by decide⟩ ⟨67, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨12, by decide⟩ ⟨67, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨13, by decide⟩ ⟨67, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨14, by decide⟩ ⟨67, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨15, by decide⟩ ⟨67, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨16, by decide⟩ ⟨67, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨17, by decide⟩ ⟨67, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨18, by decide⟩ ⟨67, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨19, by decide⟩ ⟨67, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨20, by decide⟩ ⟨67, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨21, by decide⟩ ⟨67, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨22, by decide⟩ ⟨67, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨23, by decide⟩ ⟨67, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨24, by decide⟩ ⟨67, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨25, by decide⟩ ⟨67, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨26, by decide⟩ ⟨67, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨27, by decide⟩ ⟨67, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨28, by decide⟩ ⟨67, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨29, by decide⟩ ⟨67, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨30, by decide⟩ ⟨67, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨31, by decide⟩ ⟨67, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨32, by decide⟩ ⟨67, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨33, by decide⟩ ⟨67, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨34, by decide⟩ ⟨67, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨35, by decide⟩ ⟨67, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨36, by decide⟩ ⟨67, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨37, by decide⟩ ⟨67, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨38, by decide⟩ ⟨67, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨39, by decide⟩ ⟨67, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨40, by decide⟩ ⟨67, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨41, by decide⟩ ⟨67, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨42, by decide⟩ ⟨67, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨43, by decide⟩ ⟨67, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨44, by decide⟩ ⟨67, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨45, by decide⟩ ⟨67, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨46, by decide⟩ ⟨67, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨47, by decide⟩ ⟨67, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨48, by decide⟩ ⟨67, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨49, by decide⟩ ⟨67, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨50, by decide⟩ ⟨67, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨51, by decide⟩ ⟨67, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨52, by decide⟩ ⟨67, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨53, by decide⟩ ⟨67, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨54, by decide⟩ ⟨67, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_fix ⟨55, by decide⟩ ⟨67, by decide⟩ p hp j hj hq fz1_55_67 fz2_55_67
  · exact match_zero_fix ⟨56, by decide⟩ ⟨67, by decide⟩ p hp j hj hq fz1_56_67 fz2_56_67
  · exact match_zero_fix ⟨57, by decide⟩ ⟨67, by decide⟩ p hp j hj hq fz1_57_67 fz2_57_67
  · exact match_zero_fix ⟨58, by decide⟩ ⟨67, by decide⟩ p hp j hj hq fz1_58_67 fz2_58_67
  · exact match_zero_fix ⟨59, by decide⟩ ⟨67, by decide⟩ p hp j hj hq fz1_59_67 fz2_59_67
  · exact match_zero_fix ⟨60, by decide⟩ ⟨67, by decide⟩ p hp j hj hq fz1_60_67 fz2_60_67
  · exact match_zero_fix ⟨61, by decide⟩ ⟨67, by decide⟩ p hp j hj hq fz1_61_67 fz2_61_67
  · exact match_zero_fix ⟨62, by decide⟩ ⟨67, by decide⟩ p hp j hj hq fz1_62_67 fz2_62_67
  · exact match_zero_fix ⟨63, by decide⟩ ⟨67, by decide⟩ p hp j hj hq fz1_63_67 fz2_63_67
  · exact match_zero_fix ⟨64, by decide⟩ ⟨67, by decide⟩ p hp j hj hq fz1_64_67 fz2_64_67
  · exact match_zero_fix ⟨65, by decide⟩ ⟨67, by decide⟩ p hp j hj hq fz1_65_67 fz2_65_67
  · exact match_zero_fix ⟨66, by decide⟩ ⟨67, by decide⟩ p hp j hj hq fz1_66_67 fz2_66_67
  · exact pair_67_67 p hp hrep j hj hq
  · exact match_zero_fix ⟨68, by decide⟩ ⟨67, by decide⟩ p hp j hj hq fz1_68_67 fz2_68_67
  · exact match_zero_fix ⟨69, by decide⟩ ⟨67, by decide⟩ p hp j hj hq fz1_69_67 fz2_69_67
  · exact match_zero_fix ⟨70, by decide⟩ ⟨67, by decide⟩ p hp j hj hq fz1_70_67 fz2_70_67
  · exact match_zero_fix ⟨71, by decide⟩ ⟨67, by decide⟩ p hp j hj hq fz1_71_67 fz2_71_67
  · exact match_zero_fix ⟨72, by decide⟩ ⟨67, by decide⟩ p hp j hj hq fz1_72_67 fz2_72_67
  · exact match_zero_fix ⟨73, by decide⟩ ⟨67, by decide⟩ p hp j hj hq fz1_73_67 fz2_73_67
  · exact match_zero_fix ⟨74, by decide⟩ ⟨67, by decide⟩ p hp j hj hq fz1_74_67 fz2_74_67
  · exact match_zero_fix ⟨75, by decide⟩ ⟨67, by decide⟩ p hp j hj hq fz1_75_67 fz2_75_67
  · exact match_zero_fix ⟨76, by decide⟩ ⟨67, by decide⟩ p hp j hj hq fz1_76_67 fz2_76_67
  · exact match_zero_fix ⟨77, by decide⟩ ⟨67, by decide⟩ p hp j hj hq fz1_77_67 fz2_77_67
  · exact match_zero_fix ⟨78, by decide⟩ ⟨67, by decide⟩ p hp j hj hq fz1_78_67 fz2_78_67
  · exact match_zero_fix ⟨79, by decide⟩ ⟨67, by decide⟩ p hp j hj hq fz1_79_67 fz2_79_67
  · exact match_zero_fix ⟨80, by decide⟩ ⟨67, by decide⟩ p hp j hj hq fz1_80_67 fz2_80_67
  · exact match_zero_fix ⟨81, by decide⟩ ⟨67, by decide⟩ p hp j hj hq fz1_81_67 fz2_81_67
  · exact match_zero_fix ⟨82, by decide⟩ ⟨67, by decide⟩ p hp j hj hq fz1_82_67 fz2_82_67
  · exact match_zero_fix ⟨83, by decide⟩ ⟨67, by decide⟩ p hp j hj hq fz1_83_67 fz2_83_67
  · exact match_zero_fix ⟨84, by decide⟩ ⟨67, by decide⟩ p hp j hj hq fz1_84_67 fz2_84_67
  · exact match_zero_fix ⟨85, by decide⟩ ⟨67, by decide⟩ p hp j hj hq fz1_85_67 fz2_85_67
  · exact match_zero_fix ⟨86, by decide⟩ ⟨67, by decide⟩ p hp j hj hq fz1_86_67 fz2_86_67
  · exact match_zero_fix ⟨87, by decide⟩ ⟨67, by decide⟩ p hp j hj hq fz1_87_67 fz2_87_67
  · exact match_zero_fix ⟨88, by decide⟩ ⟨67, by decide⟩ p hp j hj hq fz1_88_67 fz2_88_67
  · exact match_zero_fix ⟨89, by decide⟩ ⟨67, by decide⟩ p hp j hj hq fz1_89_67 fz2_89_67
  · exact match_zero_fix ⟨90, by decide⟩ ⟨67, by decide⟩ p hp j hj hq fz1_90_67 fz2_90_67
  · exact match_zero_fix ⟨91, by decide⟩ ⟨67, by decide⟩ p hp j hj hq fz1_91_67 fz2_91_67
  · exact match_zero_fix ⟨92, by decide⟩ ⟨67, by decide⟩ p hp j hj hq fz1_92_67 fz2_92_67
  · exact match_zero_fix ⟨93, by decide⟩ ⟨67, by decide⟩ p hp j hj hq fz1_93_67 fz2_93_67
  · exact match_zero_fix ⟨94, by decide⟩ ⟨67, by decide⟩ p hp j hj hq fz1_94_67 fz2_94_67
  · exact match_zero_fix ⟨95, by decide⟩ ⟨67, by decide⟩ p hp j hj hq fz1_95_67 fz2_95_67
  · exact match_zero_fix ⟨96, by decide⟩ ⟨67, by decide⟩ p hp j hj hq fz1_96_67 fz2_96_67
  · exact match_zero_fix ⟨97, by decide⟩ ⟨67, by decide⟩ p hp j hj hq fz1_97_67 fz2_97_67
  · exact match_zero_fix ⟨98, by decide⟩ ⟨67, by decide⟩ p hp j hj hq fz1_98_67 fz2_98_67
  · exact match_zero_fix ⟨99, by decide⟩ ⟨67, by decide⟩ p hp j hj hq fz1_99_67 fz2_99_67
  · exact match_zero_fix ⟨100, by decide⟩ ⟨67, by decide⟩ p hp j hj hq fz1_100_67 fz2_100_67
  · exact match_zero_fix ⟨101, by decide⟩ ⟨67, by decide⟩ p hp j hj hq fz1_101_67 fz2_101_67
  · exact match_zero_fix ⟨102, by decide⟩ ⟨67, by decide⟩ p hp j hj hq fz1_102_67 fz2_102_67
  · exact match_zero_fix ⟨103, by decide⟩ ⟨67, by decide⟩ p hp j hj hq fz1_103_67 fz2_103_67
  · exact match_zero_fix ⟨104, by decide⟩ ⟨67, by decide⟩ p hp j hj hq fz1_104_67 fz2_104_67
  · exact match_zero_fix ⟨105, by decide⟩ ⟨67, by decide⟩ p hp j hj hq fz1_105_67 fz2_105_67
  · exact match_zero_fix ⟨106, by decide⟩ ⟨67, by decide⟩ p hp j hj hq fz1_106_67 fz2_106_67
  · exact match_zero_fix ⟨107, by decide⟩ ⟨67, by decide⟩ p hp j hj hq fz1_107_67 fz2_107_67
  · exact match_zero_fix ⟨108, by decide⟩ ⟨67, by decide⟩ p hp j hj hq fz1_108_67 fz2_108_67
  · exact match_zero_fix ⟨109, by decide⟩ ⟨67, by decide⟩ p hp j hj hq fz1_109_67 fz2_109_67
  · exact match_zero_fix ⟨110, by decide⟩ ⟨67, by decide⟩ p hp j hj hq fz1_110_67 fz2_110_67
  · exact match_zero_fix ⟨111, by decide⟩ ⟨67, by decide⟩ p hp j hj hq fz1_111_67 fz2_111_67
  · exact match_zero_fix ⟨112, by decide⟩ ⟨67, by decide⟩ p hp j hj hq fz1_112_67 fz2_112_67
  · exact match_zero_fix ⟨113, by decide⟩ ⟨67, by decide⟩ p hp j hj hq fz1_113_67 fz2_113_67
  · exact match_zero_fix ⟨114, by decide⟩ ⟨67, by decide⟩ p hp j hj hq fz1_114_67 fz2_114_67
  · exact match_zero_fix ⟨115, by decide⟩ ⟨67, by decide⟩ p hp j hj hq fz1_115_67 fz2_115_67
  · exact match_zero_fix ⟨116, by decide⟩ ⟨67, by decide⟩ p hp j hj hq fz1_116_67 fz2_116_67
  · exact match_zero_fix ⟨117, by decide⟩ ⟨67, by decide⟩ p hp j hj hq fz1_117_67 fz2_117_67
  · exact pair_118_67 p hp hrep j hj hq
  · exact match_zero_fix ⟨119, by decide⟩ ⟨67, by decide⟩ p hp j hj hq fz1_119_67 fz2_119_67
  · exact match_zero_fix ⟨120, by decide⟩ ⟨67, by decide⟩ p hp j hj hq fz1_120_67 fz2_120_67
  · exact match_zero_fix ⟨121, by decide⟩ ⟨67, by decide⟩ p hp j hj hq fz1_121_67 fz2_121_67
  · exact match_zero_fix ⟨122, by decide⟩ ⟨67, by decide⟩ p hp j hj hq fz1_122_67 fz2_122_67
  · exact match_zero_fix ⟨123, by decide⟩ ⟨67, by decide⟩ p hp j hj hq fz1_123_67 fz2_123_67
  · exact match_zero_fix ⟨124, by decide⟩ ⟨67, by decide⟩ p hp j hj hq fz1_124_67 fz2_124_67
  · exact match_zero_fix ⟨125, by decide⟩ ⟨67, by decide⟩ p hp j hj hq fz1_125_67 fz2_125_67
  · exact match_zero_fix ⟨126, by decide⟩ ⟨67, by decide⟩ p hp j hj hq fz1_126_67 fz2_126_67
  · exact match_zero_fix ⟨127, by decide⟩ ⟨67, by decide⟩ p hp j hj hq fz1_127_67 fz2_127_67
  · exact match_zero_fix ⟨128, by decide⟩ ⟨67, by decide⟩ p hp j hj hq fz1_128_67 fz2_128_67
  · exact match_zero_fix ⟨129, by decide⟩ ⟨67, by decide⟩ p hp j hj hq fz1_129_67 fz2_129_67
  · exact match_zero_fix ⟨130, by decide⟩ ⟨67, by decide⟩ p hp j hj hq fz1_130_67 fz2_130_67
  · exact match_zero_fix ⟨131, by decide⟩ ⟨67, by decide⟩ p hp j hj hq fz1_131_67 fz2_131_67
  · exact match_zero_fix ⟨132, by decide⟩ ⟨67, by decide⟩ p hp j hj hq fz1_132_67 fz2_132_67
  · exact match_zero_fix ⟨133, by decide⟩ ⟨67, by decide⟩ p hp j hj hq fz1_133_67 fz2_133_67
  · exact match_zero_fix ⟨134, by decide⟩ ⟨67, by decide⟩ p hp j hj hq fz1_134_67 fz2_134_67
  · exact match_zero_fix ⟨135, by decide⟩ ⟨67, by decide⟩ p hp j hj hq fz1_135_67 fz2_135_67
  · exact match_zero_fix ⟨136, by decide⟩ ⟨67, by decide⟩ p hp j hj hq fz1_136_67 fz2_136_67
  · exact match_zero_fix ⟨137, by decide⟩ ⟨67, by decide⟩ p hp j hj hq fz1_137_67 fz2_137_67
  · exact match_zero_fix ⟨138, by decide⟩ ⟨67, by decide⟩ p hp j hj hq fz1_138_67 fz2_138_67
  · exact match_zero_fix ⟨139, by decide⟩ ⟨67, by decide⟩ p hp j hj hq fz1_139_67 fz2_139_67
  · exact match_zero_fix ⟨140, by decide⟩ ⟨67, by decide⟩ p hp j hj hq fz1_140_67 fz2_140_67
  · exact match_zero_fix ⟨141, by decide⟩ ⟨67, by decide⟩ p hp j hj hq fz1_141_67 fz2_141_67
  · exact match_zero_fix ⟨142, by decide⟩ ⟨67, by decide⟩ p hp j hj hq fz1_142_67 fz2_142_67
  · exact match_zero_fix ⟨143, by decide⟩ ⟨67, by decide⟩ p hp j hj hq fz1_143_67 fz2_143_67
  · exact match_zero_fix ⟨144, by decide⟩ ⟨67, by decide⟩ p hp j hj hq fz1_144_67 fz2_144_67
  · exact match_zero_fix ⟨145, by decide⟩ ⟨67, by decide⟩ p hp j hj hq fz1_145_67 fz2_145_67
  · exact match_zero_fix ⟨146, by decide⟩ ⟨67, by decide⟩ p hp j hj hq fz1_146_67 fz2_146_67
  · exact pair_147_67 p hp hrep j hj hq

theorem master_68 (p : Nat) (hp : p < (Q2.transData.getD 68 []).length)
    (hrep : (Q2.cosetIsRep.getD 68 []).getD p false = true)
    (rK : Fin 148) (j : Nat) (hj : j < (repChars.getD rK.val []).length)
    (hq : (normIsRep.getD rK.val []).getD j false = true) :
    species (Q2.reps (⟨68, by decide⟩ : Fin 148)) (colE2 ⟨68, by decide⟩ p hp)
        (rowE2 rK j hj hq)
      = species (reps (⟨68, by decide⟩ : Fin 148))
        (colE1 ⟨68, by decide⟩ p (transLenTr ⟨68, by decide⟩ p hp)) (rowE1 rK j hj) := by
  rcases rK with ⟨nK, hnK⟩; interval_cases nK
  · exact match_zero_len ⟨0, by decide⟩ ⟨68, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨1, by decide⟩ ⟨68, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨2, by decide⟩ ⟨68, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨3, by decide⟩ ⟨68, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨4, by decide⟩ ⟨68, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨5, by decide⟩ ⟨68, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨6, by decide⟩ ⟨68, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨7, by decide⟩ ⟨68, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨8, by decide⟩ ⟨68, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨9, by decide⟩ ⟨68, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨10, by decide⟩ ⟨68, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨11, by decide⟩ ⟨68, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨12, by decide⟩ ⟨68, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨13, by decide⟩ ⟨68, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨14, by decide⟩ ⟨68, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨15, by decide⟩ ⟨68, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨16, by decide⟩ ⟨68, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨17, by decide⟩ ⟨68, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨18, by decide⟩ ⟨68, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨19, by decide⟩ ⟨68, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨20, by decide⟩ ⟨68, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨21, by decide⟩ ⟨68, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨22, by decide⟩ ⟨68, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨23, by decide⟩ ⟨68, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨24, by decide⟩ ⟨68, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨25, by decide⟩ ⟨68, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨26, by decide⟩ ⟨68, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨27, by decide⟩ ⟨68, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨28, by decide⟩ ⟨68, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨29, by decide⟩ ⟨68, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨30, by decide⟩ ⟨68, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨31, by decide⟩ ⟨68, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨32, by decide⟩ ⟨68, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨33, by decide⟩ ⟨68, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨34, by decide⟩ ⟨68, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨35, by decide⟩ ⟨68, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨36, by decide⟩ ⟨68, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨37, by decide⟩ ⟨68, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨38, by decide⟩ ⟨68, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨39, by decide⟩ ⟨68, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨40, by decide⟩ ⟨68, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨41, by decide⟩ ⟨68, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨42, by decide⟩ ⟨68, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨43, by decide⟩ ⟨68, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨44, by decide⟩ ⟨68, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨45, by decide⟩ ⟨68, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨46, by decide⟩ ⟨68, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨47, by decide⟩ ⟨68, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨48, by decide⟩ ⟨68, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨49, by decide⟩ ⟨68, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨50, by decide⟩ ⟨68, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨51, by decide⟩ ⟨68, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨52, by decide⟩ ⟨68, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨53, by decide⟩ ⟨68, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨54, by decide⟩ ⟨68, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_fix ⟨55, by decide⟩ ⟨68, by decide⟩ p hp j hj hq fz1_55_68 fz2_55_68
  · exact match_zero_fix ⟨56, by decide⟩ ⟨68, by decide⟩ p hp j hj hq fz1_56_68 fz2_56_68
  · exact match_zero_fix ⟨57, by decide⟩ ⟨68, by decide⟩ p hp j hj hq fz1_57_68 fz2_57_68
  · exact match_zero_fix ⟨58, by decide⟩ ⟨68, by decide⟩ p hp j hj hq fz1_58_68 fz2_58_68
  · exact match_zero_fix ⟨59, by decide⟩ ⟨68, by decide⟩ p hp j hj hq fz1_59_68 fz2_59_68
  · exact match_zero_fix ⟨60, by decide⟩ ⟨68, by decide⟩ p hp j hj hq fz1_60_68 fz2_60_68
  · exact match_zero_fix ⟨61, by decide⟩ ⟨68, by decide⟩ p hp j hj hq fz1_61_68 fz2_61_68
  · exact match_zero_fix ⟨62, by decide⟩ ⟨68, by decide⟩ p hp j hj hq fz1_62_68 fz2_62_68
  · exact match_zero_fix ⟨63, by decide⟩ ⟨68, by decide⟩ p hp j hj hq fz1_63_68 fz2_63_68
  · exact match_zero_fix ⟨64, by decide⟩ ⟨68, by decide⟩ p hp j hj hq fz1_64_68 fz2_64_68
  · exact match_zero_fix ⟨65, by decide⟩ ⟨68, by decide⟩ p hp j hj hq fz1_65_68 fz2_65_68
  · exact match_zero_fix ⟨66, by decide⟩ ⟨68, by decide⟩ p hp j hj hq fz1_66_68 fz2_66_68
  · exact match_zero_fix ⟨67, by decide⟩ ⟨68, by decide⟩ p hp j hj hq fz1_67_68 fz2_67_68
  · exact pair_68_68 p hp hrep j hj hq
  · exact match_zero_fix ⟨69, by decide⟩ ⟨68, by decide⟩ p hp j hj hq fz1_69_68 fz2_69_68
  · exact match_zero_fix ⟨70, by decide⟩ ⟨68, by decide⟩ p hp j hj hq fz1_70_68 fz2_70_68
  · exact match_zero_fix ⟨71, by decide⟩ ⟨68, by decide⟩ p hp j hj hq fz1_71_68 fz2_71_68
  · exact match_zero_fix ⟨72, by decide⟩ ⟨68, by decide⟩ p hp j hj hq fz1_72_68 fz2_72_68
  · exact match_zero_fix ⟨73, by decide⟩ ⟨68, by decide⟩ p hp j hj hq fz1_73_68 fz2_73_68
  · exact match_zero_fix ⟨74, by decide⟩ ⟨68, by decide⟩ p hp j hj hq fz1_74_68 fz2_74_68
  · exact match_zero_fix ⟨75, by decide⟩ ⟨68, by decide⟩ p hp j hj hq fz1_75_68 fz2_75_68
  · exact match_zero_fix ⟨76, by decide⟩ ⟨68, by decide⟩ p hp j hj hq fz1_76_68 fz2_76_68
  · exact match_zero_fix ⟨77, by decide⟩ ⟨68, by decide⟩ p hp j hj hq fz1_77_68 fz2_77_68
  · exact match_zero_fix ⟨78, by decide⟩ ⟨68, by decide⟩ p hp j hj hq fz1_78_68 fz2_78_68
  · exact match_zero_fix ⟨79, by decide⟩ ⟨68, by decide⟩ p hp j hj hq fz1_79_68 fz2_79_68
  · exact match_zero_fix ⟨80, by decide⟩ ⟨68, by decide⟩ p hp j hj hq fz1_80_68 fz2_80_68
  · exact match_zero_fix ⟨81, by decide⟩ ⟨68, by decide⟩ p hp j hj hq fz1_81_68 fz2_81_68
  · exact match_zero_fix ⟨82, by decide⟩ ⟨68, by decide⟩ p hp j hj hq fz1_82_68 fz2_82_68
  · exact match_zero_fix ⟨83, by decide⟩ ⟨68, by decide⟩ p hp j hj hq fz1_83_68 fz2_83_68
  · exact match_zero_fix ⟨84, by decide⟩ ⟨68, by decide⟩ p hp j hj hq fz1_84_68 fz2_84_68
  · exact match_zero_fix ⟨85, by decide⟩ ⟨68, by decide⟩ p hp j hj hq fz1_85_68 fz2_85_68
  · exact match_zero_fix ⟨86, by decide⟩ ⟨68, by decide⟩ p hp j hj hq fz1_86_68 fz2_86_68
  · exact match_zero_fix ⟨87, by decide⟩ ⟨68, by decide⟩ p hp j hj hq fz1_87_68 fz2_87_68
  · exact match_zero_fix ⟨88, by decide⟩ ⟨68, by decide⟩ p hp j hj hq fz1_88_68 fz2_88_68
  · exact match_zero_fix ⟨89, by decide⟩ ⟨68, by decide⟩ p hp j hj hq fz1_89_68 fz2_89_68
  · exact match_zero_fix ⟨90, by decide⟩ ⟨68, by decide⟩ p hp j hj hq fz1_90_68 fz2_90_68
  · exact match_zero_fix ⟨91, by decide⟩ ⟨68, by decide⟩ p hp j hj hq fz1_91_68 fz2_91_68
  · exact match_zero_fix ⟨92, by decide⟩ ⟨68, by decide⟩ p hp j hj hq fz1_92_68 fz2_92_68
  · exact match_zero_fix ⟨93, by decide⟩ ⟨68, by decide⟩ p hp j hj hq fz1_93_68 fz2_93_68
  · exact match_zero_fix ⟨94, by decide⟩ ⟨68, by decide⟩ p hp j hj hq fz1_94_68 fz2_94_68
  · exact match_zero_fix ⟨95, by decide⟩ ⟨68, by decide⟩ p hp j hj hq fz1_95_68 fz2_95_68
  · exact match_zero_fix ⟨96, by decide⟩ ⟨68, by decide⟩ p hp j hj hq fz1_96_68 fz2_96_68
  · exact match_zero_fix ⟨97, by decide⟩ ⟨68, by decide⟩ p hp j hj hq fz1_97_68 fz2_97_68
  · exact match_zero_fix ⟨98, by decide⟩ ⟨68, by decide⟩ p hp j hj hq fz1_98_68 fz2_98_68
  · exact match_zero_fix ⟨99, by decide⟩ ⟨68, by decide⟩ p hp j hj hq fz1_99_68 fz2_99_68
  · exact match_zero_fix ⟨100, by decide⟩ ⟨68, by decide⟩ p hp j hj hq fz1_100_68 fz2_100_68
  · exact match_zero_fix ⟨101, by decide⟩ ⟨68, by decide⟩ p hp j hj hq fz1_101_68 fz2_101_68
  · exact match_zero_fix ⟨102, by decide⟩ ⟨68, by decide⟩ p hp j hj hq fz1_102_68 fz2_102_68
  · exact match_zero_fix ⟨103, by decide⟩ ⟨68, by decide⟩ p hp j hj hq fz1_103_68 fz2_103_68
  · exact match_zero_fix ⟨104, by decide⟩ ⟨68, by decide⟩ p hp j hj hq fz1_104_68 fz2_104_68
  · exact match_zero_fix ⟨105, by decide⟩ ⟨68, by decide⟩ p hp j hj hq fz1_105_68 fz2_105_68
  · exact match_zero_fix ⟨106, by decide⟩ ⟨68, by decide⟩ p hp j hj hq fz1_106_68 fz2_106_68
  · exact match_zero_fix ⟨107, by decide⟩ ⟨68, by decide⟩ p hp j hj hq fz1_107_68 fz2_107_68
  · exact match_zero_fix ⟨108, by decide⟩ ⟨68, by decide⟩ p hp j hj hq fz1_108_68 fz2_108_68
  · exact match_zero_fix ⟨109, by decide⟩ ⟨68, by decide⟩ p hp j hj hq fz1_109_68 fz2_109_68
  · exact match_zero_fix ⟨110, by decide⟩ ⟨68, by decide⟩ p hp j hj hq fz1_110_68 fz2_110_68
  · exact match_zero_fix ⟨111, by decide⟩ ⟨68, by decide⟩ p hp j hj hq fz1_111_68 fz2_111_68
  · exact match_zero_fix ⟨112, by decide⟩ ⟨68, by decide⟩ p hp j hj hq fz1_112_68 fz2_112_68
  · exact match_zero_fix ⟨113, by decide⟩ ⟨68, by decide⟩ p hp j hj hq fz1_113_68 fz2_113_68
  · exact match_zero_fix ⟨114, by decide⟩ ⟨68, by decide⟩ p hp j hj hq fz1_114_68 fz2_114_68
  · exact match_zero_fix ⟨115, by decide⟩ ⟨68, by decide⟩ p hp j hj hq fz1_115_68 fz2_115_68
  · exact match_zero_fix ⟨116, by decide⟩ ⟨68, by decide⟩ p hp j hj hq fz1_116_68 fz2_116_68
  · exact match_zero_fix ⟨117, by decide⟩ ⟨68, by decide⟩ p hp j hj hq fz1_117_68 fz2_117_68
  · exact pair_118_68 p hp hrep j hj hq
  · exact match_zero_fix ⟨119, by decide⟩ ⟨68, by decide⟩ p hp j hj hq fz1_119_68 fz2_119_68
  · exact match_zero_fix ⟨120, by decide⟩ ⟨68, by decide⟩ p hp j hj hq fz1_120_68 fz2_120_68
  · exact match_zero_fix ⟨121, by decide⟩ ⟨68, by decide⟩ p hp j hj hq fz1_121_68 fz2_121_68
  · exact match_zero_fix ⟨122, by decide⟩ ⟨68, by decide⟩ p hp j hj hq fz1_122_68 fz2_122_68
  · exact match_zero_fix ⟨123, by decide⟩ ⟨68, by decide⟩ p hp j hj hq fz1_123_68 fz2_123_68
  · exact match_zero_fix ⟨124, by decide⟩ ⟨68, by decide⟩ p hp j hj hq fz1_124_68 fz2_124_68
  · exact match_zero_fix ⟨125, by decide⟩ ⟨68, by decide⟩ p hp j hj hq fz1_125_68 fz2_125_68
  · exact match_zero_fix ⟨126, by decide⟩ ⟨68, by decide⟩ p hp j hj hq fz1_126_68 fz2_126_68
  · exact match_zero_fix ⟨127, by decide⟩ ⟨68, by decide⟩ p hp j hj hq fz1_127_68 fz2_127_68
  · exact match_zero_fix ⟨128, by decide⟩ ⟨68, by decide⟩ p hp j hj hq fz1_128_68 fz2_128_68
  · exact match_zero_fix ⟨129, by decide⟩ ⟨68, by decide⟩ p hp j hj hq fz1_129_68 fz2_129_68
  · exact match_zero_fix ⟨130, by decide⟩ ⟨68, by decide⟩ p hp j hj hq fz1_130_68 fz2_130_68
  · exact match_zero_fix ⟨131, by decide⟩ ⟨68, by decide⟩ p hp j hj hq fz1_131_68 fz2_131_68
  · exact match_zero_fix ⟨132, by decide⟩ ⟨68, by decide⟩ p hp j hj hq fz1_132_68 fz2_132_68
  · exact match_zero_fix ⟨133, by decide⟩ ⟨68, by decide⟩ p hp j hj hq fz1_133_68 fz2_133_68
  · exact match_zero_fix ⟨134, by decide⟩ ⟨68, by decide⟩ p hp j hj hq fz1_134_68 fz2_134_68
  · exact match_zero_fix ⟨135, by decide⟩ ⟨68, by decide⟩ p hp j hj hq fz1_135_68 fz2_135_68
  · exact match_zero_fix ⟨136, by decide⟩ ⟨68, by decide⟩ p hp j hj hq fz1_136_68 fz2_136_68
  · exact match_zero_fix ⟨137, by decide⟩ ⟨68, by decide⟩ p hp j hj hq fz1_137_68 fz2_137_68
  · exact match_zero_fix ⟨138, by decide⟩ ⟨68, by decide⟩ p hp j hj hq fz1_138_68 fz2_138_68
  · exact match_zero_fix ⟨139, by decide⟩ ⟨68, by decide⟩ p hp j hj hq fz1_139_68 fz2_139_68
  · exact match_zero_fix ⟨140, by decide⟩ ⟨68, by decide⟩ p hp j hj hq fz1_140_68 fz2_140_68
  · exact match_zero_fix ⟨141, by decide⟩ ⟨68, by decide⟩ p hp j hj hq fz1_141_68 fz2_141_68
  · exact match_zero_fix ⟨142, by decide⟩ ⟨68, by decide⟩ p hp j hj hq fz1_142_68 fz2_142_68
  · exact match_zero_fix ⟨143, by decide⟩ ⟨68, by decide⟩ p hp j hj hq fz1_143_68 fz2_143_68
  · exact match_zero_fix ⟨144, by decide⟩ ⟨68, by decide⟩ p hp j hj hq fz1_144_68 fz2_144_68
  · exact match_zero_fix ⟨145, by decide⟩ ⟨68, by decide⟩ p hp j hj hq fz1_145_68 fz2_145_68
  · exact match_zero_fix ⟨146, by decide⟩ ⟨68, by decide⟩ p hp j hj hq fz1_146_68 fz2_146_68
  · exact pair_147_68 p hp hrep j hj hq

theorem master_69 (p : Nat) (hp : p < (Q2.transData.getD 69 []).length)
    (hrep : (Q2.cosetIsRep.getD 69 []).getD p false = true)
    (rK : Fin 148) (j : Nat) (hj : j < (repChars.getD rK.val []).length)
    (hq : (normIsRep.getD rK.val []).getD j false = true) :
    species (Q2.reps (⟨69, by decide⟩ : Fin 148)) (colE2 ⟨69, by decide⟩ p hp)
        (rowE2 rK j hj hq)
      = species (reps (⟨69, by decide⟩ : Fin 148))
        (colE1 ⟨69, by decide⟩ p (transLenTr ⟨69, by decide⟩ p hp)) (rowE1 rK j hj) := by
  rcases rK with ⟨nK, hnK⟩; interval_cases nK
  · exact match_zero_len ⟨0, by decide⟩ ⟨69, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨1, by decide⟩ ⟨69, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨2, by decide⟩ ⟨69, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨3, by decide⟩ ⟨69, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨4, by decide⟩ ⟨69, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨5, by decide⟩ ⟨69, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨6, by decide⟩ ⟨69, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨7, by decide⟩ ⟨69, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨8, by decide⟩ ⟨69, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨9, by decide⟩ ⟨69, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨10, by decide⟩ ⟨69, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨11, by decide⟩ ⟨69, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨12, by decide⟩ ⟨69, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨13, by decide⟩ ⟨69, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨14, by decide⟩ ⟨69, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨15, by decide⟩ ⟨69, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨16, by decide⟩ ⟨69, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨17, by decide⟩ ⟨69, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨18, by decide⟩ ⟨69, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨19, by decide⟩ ⟨69, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨20, by decide⟩ ⟨69, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨21, by decide⟩ ⟨69, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨22, by decide⟩ ⟨69, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨23, by decide⟩ ⟨69, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨24, by decide⟩ ⟨69, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨25, by decide⟩ ⟨69, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨26, by decide⟩ ⟨69, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨27, by decide⟩ ⟨69, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨28, by decide⟩ ⟨69, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨29, by decide⟩ ⟨69, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨30, by decide⟩ ⟨69, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨31, by decide⟩ ⟨69, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨32, by decide⟩ ⟨69, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨33, by decide⟩ ⟨69, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨34, by decide⟩ ⟨69, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨35, by decide⟩ ⟨69, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨36, by decide⟩ ⟨69, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨37, by decide⟩ ⟨69, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨38, by decide⟩ ⟨69, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨39, by decide⟩ ⟨69, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨40, by decide⟩ ⟨69, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨41, by decide⟩ ⟨69, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨42, by decide⟩ ⟨69, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨43, by decide⟩ ⟨69, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨44, by decide⟩ ⟨69, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨45, by decide⟩ ⟨69, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨46, by decide⟩ ⟨69, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨47, by decide⟩ ⟨69, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨48, by decide⟩ ⟨69, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨49, by decide⟩ ⟨69, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨50, by decide⟩ ⟨69, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨51, by decide⟩ ⟨69, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨52, by decide⟩ ⟨69, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨53, by decide⟩ ⟨69, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨54, by decide⟩ ⟨69, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_fix ⟨55, by decide⟩ ⟨69, by decide⟩ p hp j hj hq fz1_55_69 fz2_55_69
  · exact match_zero_fix ⟨56, by decide⟩ ⟨69, by decide⟩ p hp j hj hq fz1_56_69 fz2_56_69
  · exact match_zero_fix ⟨57, by decide⟩ ⟨69, by decide⟩ p hp j hj hq fz1_57_69 fz2_57_69
  · exact match_zero_fix ⟨58, by decide⟩ ⟨69, by decide⟩ p hp j hj hq fz1_58_69 fz2_58_69
  · exact match_zero_fix ⟨59, by decide⟩ ⟨69, by decide⟩ p hp j hj hq fz1_59_69 fz2_59_69
  · exact match_zero_fix ⟨60, by decide⟩ ⟨69, by decide⟩ p hp j hj hq fz1_60_69 fz2_60_69
  · exact match_zero_fix ⟨61, by decide⟩ ⟨69, by decide⟩ p hp j hj hq fz1_61_69 fz2_61_69
  · exact match_zero_fix ⟨62, by decide⟩ ⟨69, by decide⟩ p hp j hj hq fz1_62_69 fz2_62_69
  · exact match_zero_fix ⟨63, by decide⟩ ⟨69, by decide⟩ p hp j hj hq fz1_63_69 fz2_63_69
  · exact match_zero_fix ⟨64, by decide⟩ ⟨69, by decide⟩ p hp j hj hq fz1_64_69 fz2_64_69
  · exact match_zero_fix ⟨65, by decide⟩ ⟨69, by decide⟩ p hp j hj hq fz1_65_69 fz2_65_69
  · exact match_zero_fix ⟨66, by decide⟩ ⟨69, by decide⟩ p hp j hj hq fz1_66_69 fz2_66_69
  · exact match_zero_fix ⟨67, by decide⟩ ⟨69, by decide⟩ p hp j hj hq fz1_67_69 fz2_67_69
  · exact match_zero_fix ⟨68, by decide⟩ ⟨69, by decide⟩ p hp j hj hq fz1_68_69 fz2_68_69
  · exact pair_69_69 p hp hrep j hj hq
  · exact match_zero_fix ⟨70, by decide⟩ ⟨69, by decide⟩ p hp j hj hq fz1_70_69 fz2_70_69
  · exact match_zero_fix ⟨71, by decide⟩ ⟨69, by decide⟩ p hp j hj hq fz1_71_69 fz2_71_69
  · exact match_zero_fix ⟨72, by decide⟩ ⟨69, by decide⟩ p hp j hj hq fz1_72_69 fz2_72_69
  · exact match_zero_fix ⟨73, by decide⟩ ⟨69, by decide⟩ p hp j hj hq fz1_73_69 fz2_73_69
  · exact match_zero_fix ⟨74, by decide⟩ ⟨69, by decide⟩ p hp j hj hq fz1_74_69 fz2_74_69
  · exact match_zero_fix ⟨75, by decide⟩ ⟨69, by decide⟩ p hp j hj hq fz1_75_69 fz2_75_69
  · exact match_zero_fix ⟨76, by decide⟩ ⟨69, by decide⟩ p hp j hj hq fz1_76_69 fz2_76_69
  · exact match_zero_fix ⟨77, by decide⟩ ⟨69, by decide⟩ p hp j hj hq fz1_77_69 fz2_77_69
  · exact match_zero_fix ⟨78, by decide⟩ ⟨69, by decide⟩ p hp j hj hq fz1_78_69 fz2_78_69
  · exact match_zero_fix ⟨79, by decide⟩ ⟨69, by decide⟩ p hp j hj hq fz1_79_69 fz2_79_69
  · exact match_zero_fix ⟨80, by decide⟩ ⟨69, by decide⟩ p hp j hj hq fz1_80_69 fz2_80_69
  · exact match_zero_fix ⟨81, by decide⟩ ⟨69, by decide⟩ p hp j hj hq fz1_81_69 fz2_81_69
  · exact match_zero_fix ⟨82, by decide⟩ ⟨69, by decide⟩ p hp j hj hq fz1_82_69 fz2_82_69
  · exact match_zero_fix ⟨83, by decide⟩ ⟨69, by decide⟩ p hp j hj hq fz1_83_69 fz2_83_69
  · exact match_zero_fix ⟨84, by decide⟩ ⟨69, by decide⟩ p hp j hj hq fz1_84_69 fz2_84_69
  · exact match_zero_fix ⟨85, by decide⟩ ⟨69, by decide⟩ p hp j hj hq fz1_85_69 fz2_85_69
  · exact match_zero_fix ⟨86, by decide⟩ ⟨69, by decide⟩ p hp j hj hq fz1_86_69 fz2_86_69
  · exact match_zero_fix ⟨87, by decide⟩ ⟨69, by decide⟩ p hp j hj hq fz1_87_69 fz2_87_69
  · exact match_zero_fix ⟨88, by decide⟩ ⟨69, by decide⟩ p hp j hj hq fz1_88_69 fz2_88_69
  · exact match_zero_fix ⟨89, by decide⟩ ⟨69, by decide⟩ p hp j hj hq fz1_89_69 fz2_89_69
  · exact match_zero_fix ⟨90, by decide⟩ ⟨69, by decide⟩ p hp j hj hq fz1_90_69 fz2_90_69
  · exact match_zero_fix ⟨91, by decide⟩ ⟨69, by decide⟩ p hp j hj hq fz1_91_69 fz2_91_69
  · exact match_zero_fix ⟨92, by decide⟩ ⟨69, by decide⟩ p hp j hj hq fz1_92_69 fz2_92_69
  · exact match_zero_fix ⟨93, by decide⟩ ⟨69, by decide⟩ p hp j hj hq fz1_93_69 fz2_93_69
  · exact match_zero_fix ⟨94, by decide⟩ ⟨69, by decide⟩ p hp j hj hq fz1_94_69 fz2_94_69
  · exact match_zero_fix ⟨95, by decide⟩ ⟨69, by decide⟩ p hp j hj hq fz1_95_69 fz2_95_69
  · exact match_zero_fix ⟨96, by decide⟩ ⟨69, by decide⟩ p hp j hj hq fz1_96_69 fz2_96_69
  · exact match_zero_fix ⟨97, by decide⟩ ⟨69, by decide⟩ p hp j hj hq fz1_97_69 fz2_97_69
  · exact match_zero_fix ⟨98, by decide⟩ ⟨69, by decide⟩ p hp j hj hq fz1_98_69 fz2_98_69
  · exact match_zero_fix ⟨99, by decide⟩ ⟨69, by decide⟩ p hp j hj hq fz1_99_69 fz2_99_69
  · exact match_zero_fix ⟨100, by decide⟩ ⟨69, by decide⟩ p hp j hj hq fz1_100_69 fz2_100_69
  · exact match_zero_fix ⟨101, by decide⟩ ⟨69, by decide⟩ p hp j hj hq fz1_101_69 fz2_101_69
  · exact match_zero_fix ⟨102, by decide⟩ ⟨69, by decide⟩ p hp j hj hq fz1_102_69 fz2_102_69
  · exact match_zero_fix ⟨103, by decide⟩ ⟨69, by decide⟩ p hp j hj hq fz1_103_69 fz2_103_69
  · exact match_zero_fix ⟨104, by decide⟩ ⟨69, by decide⟩ p hp j hj hq fz1_104_69 fz2_104_69
  · exact match_zero_fix ⟨105, by decide⟩ ⟨69, by decide⟩ p hp j hj hq fz1_105_69 fz2_105_69
  · exact match_zero_fix ⟨106, by decide⟩ ⟨69, by decide⟩ p hp j hj hq fz1_106_69 fz2_106_69
  · exact match_zero_fix ⟨107, by decide⟩ ⟨69, by decide⟩ p hp j hj hq fz1_107_69 fz2_107_69
  · exact match_zero_fix ⟨108, by decide⟩ ⟨69, by decide⟩ p hp j hj hq fz1_108_69 fz2_108_69
  · exact match_zero_fix ⟨109, by decide⟩ ⟨69, by decide⟩ p hp j hj hq fz1_109_69 fz2_109_69
  · exact match_zero_fix ⟨110, by decide⟩ ⟨69, by decide⟩ p hp j hj hq fz1_110_69 fz2_110_69
  · exact match_zero_fix ⟨111, by decide⟩ ⟨69, by decide⟩ p hp j hj hq fz1_111_69 fz2_111_69
  · exact match_zero_fix ⟨112, by decide⟩ ⟨69, by decide⟩ p hp j hj hq fz1_112_69 fz2_112_69
  · exact match_zero_fix ⟨113, by decide⟩ ⟨69, by decide⟩ p hp j hj hq fz1_113_69 fz2_113_69
  · exact match_zero_fix ⟨114, by decide⟩ ⟨69, by decide⟩ p hp j hj hq fz1_114_69 fz2_114_69
  · exact match_zero_fix ⟨115, by decide⟩ ⟨69, by decide⟩ p hp j hj hq fz1_115_69 fz2_115_69
  · exact match_zero_fix ⟨116, by decide⟩ ⟨69, by decide⟩ p hp j hj hq fz1_116_69 fz2_116_69
  · exact match_zero_fix ⟨117, by decide⟩ ⟨69, by decide⟩ p hp j hj hq fz1_117_69 fz2_117_69
  · exact pair_118_69 p hp hrep j hj hq
  · exact match_zero_fix ⟨119, by decide⟩ ⟨69, by decide⟩ p hp j hj hq fz1_119_69 fz2_119_69
  · exact match_zero_fix ⟨120, by decide⟩ ⟨69, by decide⟩ p hp j hj hq fz1_120_69 fz2_120_69
  · exact match_zero_fix ⟨121, by decide⟩ ⟨69, by decide⟩ p hp j hj hq fz1_121_69 fz2_121_69
  · exact match_zero_fix ⟨122, by decide⟩ ⟨69, by decide⟩ p hp j hj hq fz1_122_69 fz2_122_69
  · exact match_zero_fix ⟨123, by decide⟩ ⟨69, by decide⟩ p hp j hj hq fz1_123_69 fz2_123_69
  · exact match_zero_fix ⟨124, by decide⟩ ⟨69, by decide⟩ p hp j hj hq fz1_124_69 fz2_124_69
  · exact match_zero_fix ⟨125, by decide⟩ ⟨69, by decide⟩ p hp j hj hq fz1_125_69 fz2_125_69
  · exact match_zero_fix ⟨126, by decide⟩ ⟨69, by decide⟩ p hp j hj hq fz1_126_69 fz2_126_69
  · exact match_zero_fix ⟨127, by decide⟩ ⟨69, by decide⟩ p hp j hj hq fz1_127_69 fz2_127_69
  · exact match_zero_fix ⟨128, by decide⟩ ⟨69, by decide⟩ p hp j hj hq fz1_128_69 fz2_128_69
  · exact match_zero_fix ⟨129, by decide⟩ ⟨69, by decide⟩ p hp j hj hq fz1_129_69 fz2_129_69
  · exact match_zero_fix ⟨130, by decide⟩ ⟨69, by decide⟩ p hp j hj hq fz1_130_69 fz2_130_69
  · exact match_zero_fix ⟨131, by decide⟩ ⟨69, by decide⟩ p hp j hj hq fz1_131_69 fz2_131_69
  · exact match_zero_fix ⟨132, by decide⟩ ⟨69, by decide⟩ p hp j hj hq fz1_132_69 fz2_132_69
  · exact match_zero_fix ⟨133, by decide⟩ ⟨69, by decide⟩ p hp j hj hq fz1_133_69 fz2_133_69
  · exact match_zero_fix ⟨134, by decide⟩ ⟨69, by decide⟩ p hp j hj hq fz1_134_69 fz2_134_69
  · exact match_zero_fix ⟨135, by decide⟩ ⟨69, by decide⟩ p hp j hj hq fz1_135_69 fz2_135_69
  · exact match_zero_fix ⟨136, by decide⟩ ⟨69, by decide⟩ p hp j hj hq fz1_136_69 fz2_136_69
  · exact match_zero_fix ⟨137, by decide⟩ ⟨69, by decide⟩ p hp j hj hq fz1_137_69 fz2_137_69
  · exact match_zero_fix ⟨138, by decide⟩ ⟨69, by decide⟩ p hp j hj hq fz1_138_69 fz2_138_69
  · exact match_zero_fix ⟨139, by decide⟩ ⟨69, by decide⟩ p hp j hj hq fz1_139_69 fz2_139_69
  · exact match_zero_fix ⟨140, by decide⟩ ⟨69, by decide⟩ p hp j hj hq fz1_140_69 fz2_140_69
  · exact match_zero_fix ⟨141, by decide⟩ ⟨69, by decide⟩ p hp j hj hq fz1_141_69 fz2_141_69
  · exact match_zero_fix ⟨142, by decide⟩ ⟨69, by decide⟩ p hp j hj hq fz1_142_69 fz2_142_69
  · exact match_zero_fix ⟨143, by decide⟩ ⟨69, by decide⟩ p hp j hj hq fz1_143_69 fz2_143_69
  · exact match_zero_fix ⟨144, by decide⟩ ⟨69, by decide⟩ p hp j hj hq fz1_144_69 fz2_144_69
  · exact match_zero_fix ⟨145, by decide⟩ ⟨69, by decide⟩ p hp j hj hq fz1_145_69 fz2_145_69
  · exact match_zero_fix ⟨146, by decide⟩ ⟨69, by decide⟩ p hp j hj hq fz1_146_69 fz2_146_69
  · exact pair_147_69 p hp hrep j hj hq

theorem master_70 (p : Nat) (hp : p < (Q2.transData.getD 70 []).length)
    (hrep : (Q2.cosetIsRep.getD 70 []).getD p false = true)
    (rK : Fin 148) (j : Nat) (hj : j < (repChars.getD rK.val []).length)
    (hq : (normIsRep.getD rK.val []).getD j false = true) :
    species (Q2.reps (⟨70, by decide⟩ : Fin 148)) (colE2 ⟨70, by decide⟩ p hp)
        (rowE2 rK j hj hq)
      = species (reps (⟨70, by decide⟩ : Fin 148))
        (colE1 ⟨70, by decide⟩ p (transLenTr ⟨70, by decide⟩ p hp)) (rowE1 rK j hj) := by
  rcases rK with ⟨nK, hnK⟩; interval_cases nK
  · exact match_zero_len ⟨0, by decide⟩ ⟨70, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨1, by decide⟩ ⟨70, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨2, by decide⟩ ⟨70, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨3, by decide⟩ ⟨70, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨4, by decide⟩ ⟨70, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨5, by decide⟩ ⟨70, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨6, by decide⟩ ⟨70, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨7, by decide⟩ ⟨70, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨8, by decide⟩ ⟨70, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨9, by decide⟩ ⟨70, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨10, by decide⟩ ⟨70, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨11, by decide⟩ ⟨70, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨12, by decide⟩ ⟨70, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨13, by decide⟩ ⟨70, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨14, by decide⟩ ⟨70, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨15, by decide⟩ ⟨70, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨16, by decide⟩ ⟨70, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨17, by decide⟩ ⟨70, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨18, by decide⟩ ⟨70, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨19, by decide⟩ ⟨70, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨20, by decide⟩ ⟨70, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨21, by decide⟩ ⟨70, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨22, by decide⟩ ⟨70, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨23, by decide⟩ ⟨70, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨24, by decide⟩ ⟨70, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨25, by decide⟩ ⟨70, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨26, by decide⟩ ⟨70, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨27, by decide⟩ ⟨70, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨28, by decide⟩ ⟨70, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨29, by decide⟩ ⟨70, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨30, by decide⟩ ⟨70, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨31, by decide⟩ ⟨70, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨32, by decide⟩ ⟨70, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨33, by decide⟩ ⟨70, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨34, by decide⟩ ⟨70, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨35, by decide⟩ ⟨70, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨36, by decide⟩ ⟨70, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨37, by decide⟩ ⟨70, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨38, by decide⟩ ⟨70, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨39, by decide⟩ ⟨70, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨40, by decide⟩ ⟨70, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨41, by decide⟩ ⟨70, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨42, by decide⟩ ⟨70, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨43, by decide⟩ ⟨70, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨44, by decide⟩ ⟨70, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨45, by decide⟩ ⟨70, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨46, by decide⟩ ⟨70, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨47, by decide⟩ ⟨70, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨48, by decide⟩ ⟨70, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨49, by decide⟩ ⟨70, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨50, by decide⟩ ⟨70, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨51, by decide⟩ ⟨70, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨52, by decide⟩ ⟨70, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨53, by decide⟩ ⟨70, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨54, by decide⟩ ⟨70, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_fix ⟨55, by decide⟩ ⟨70, by decide⟩ p hp j hj hq fz1_55_70 fz2_55_70
  · exact match_zero_fix ⟨56, by decide⟩ ⟨70, by decide⟩ p hp j hj hq fz1_56_70 fz2_56_70
  · exact match_zero_fix ⟨57, by decide⟩ ⟨70, by decide⟩ p hp j hj hq fz1_57_70 fz2_57_70
  · exact match_zero_fix ⟨58, by decide⟩ ⟨70, by decide⟩ p hp j hj hq fz1_58_70 fz2_58_70
  · exact match_zero_fix ⟨59, by decide⟩ ⟨70, by decide⟩ p hp j hj hq fz1_59_70 fz2_59_70
  · exact match_zero_fix ⟨60, by decide⟩ ⟨70, by decide⟩ p hp j hj hq fz1_60_70 fz2_60_70
  · exact match_zero_fix ⟨61, by decide⟩ ⟨70, by decide⟩ p hp j hj hq fz1_61_70 fz2_61_70
  · exact match_zero_fix ⟨62, by decide⟩ ⟨70, by decide⟩ p hp j hj hq fz1_62_70 fz2_62_70
  · exact match_zero_fix ⟨63, by decide⟩ ⟨70, by decide⟩ p hp j hj hq fz1_63_70 fz2_63_70
  · exact match_zero_fix ⟨64, by decide⟩ ⟨70, by decide⟩ p hp j hj hq fz1_64_70 fz2_64_70
  · exact match_zero_fix ⟨65, by decide⟩ ⟨70, by decide⟩ p hp j hj hq fz1_65_70 fz2_65_70
  · exact match_zero_fix ⟨66, by decide⟩ ⟨70, by decide⟩ p hp j hj hq fz1_66_70 fz2_66_70
  · exact match_zero_fix ⟨67, by decide⟩ ⟨70, by decide⟩ p hp j hj hq fz1_67_70 fz2_67_70
  · exact match_zero_fix ⟨68, by decide⟩ ⟨70, by decide⟩ p hp j hj hq fz1_68_70 fz2_68_70
  · exact match_zero_fix ⟨69, by decide⟩ ⟨70, by decide⟩ p hp j hj hq fz1_69_70 fz2_69_70
  · exact pair_70_70 p hp hrep j hj hq
  · exact match_zero_fix ⟨71, by decide⟩ ⟨70, by decide⟩ p hp j hj hq fz1_71_70 fz2_71_70
  · exact match_zero_fix ⟨72, by decide⟩ ⟨70, by decide⟩ p hp j hj hq fz1_72_70 fz2_72_70
  · exact match_zero_fix ⟨73, by decide⟩ ⟨70, by decide⟩ p hp j hj hq fz1_73_70 fz2_73_70
  · exact match_zero_fix ⟨74, by decide⟩ ⟨70, by decide⟩ p hp j hj hq fz1_74_70 fz2_74_70
  · exact match_zero_fix ⟨75, by decide⟩ ⟨70, by decide⟩ p hp j hj hq fz1_75_70 fz2_75_70
  · exact match_zero_fix ⟨76, by decide⟩ ⟨70, by decide⟩ p hp j hj hq fz1_76_70 fz2_76_70
  · exact match_zero_fix ⟨77, by decide⟩ ⟨70, by decide⟩ p hp j hj hq fz1_77_70 fz2_77_70
  · exact match_zero_fix ⟨78, by decide⟩ ⟨70, by decide⟩ p hp j hj hq fz1_78_70 fz2_78_70
  · exact match_zero_fix ⟨79, by decide⟩ ⟨70, by decide⟩ p hp j hj hq fz1_79_70 fz2_79_70
  · exact match_zero_fix ⟨80, by decide⟩ ⟨70, by decide⟩ p hp j hj hq fz1_80_70 fz2_80_70
  · exact match_zero_fix ⟨81, by decide⟩ ⟨70, by decide⟩ p hp j hj hq fz1_81_70 fz2_81_70
  · exact match_zero_fix ⟨82, by decide⟩ ⟨70, by decide⟩ p hp j hj hq fz1_82_70 fz2_82_70
  · exact match_zero_fix ⟨83, by decide⟩ ⟨70, by decide⟩ p hp j hj hq fz1_83_70 fz2_83_70
  · exact match_zero_fix ⟨84, by decide⟩ ⟨70, by decide⟩ p hp j hj hq fz1_84_70 fz2_84_70
  · exact match_zero_fix ⟨85, by decide⟩ ⟨70, by decide⟩ p hp j hj hq fz1_85_70 fz2_85_70
  · exact match_zero_fix ⟨86, by decide⟩ ⟨70, by decide⟩ p hp j hj hq fz1_86_70 fz2_86_70
  · exact match_zero_fix ⟨87, by decide⟩ ⟨70, by decide⟩ p hp j hj hq fz1_87_70 fz2_87_70
  · exact match_zero_fix ⟨88, by decide⟩ ⟨70, by decide⟩ p hp j hj hq fz1_88_70 fz2_88_70
  · exact match_zero_fix ⟨89, by decide⟩ ⟨70, by decide⟩ p hp j hj hq fz1_89_70 fz2_89_70
  · exact match_zero_fix ⟨90, by decide⟩ ⟨70, by decide⟩ p hp j hj hq fz1_90_70 fz2_90_70
  · exact match_zero_fix ⟨91, by decide⟩ ⟨70, by decide⟩ p hp j hj hq fz1_91_70 fz2_91_70
  · exact match_zero_fix ⟨92, by decide⟩ ⟨70, by decide⟩ p hp j hj hq fz1_92_70 fz2_92_70
  · exact match_zero_fix ⟨93, by decide⟩ ⟨70, by decide⟩ p hp j hj hq fz1_93_70 fz2_93_70
  · exact match_zero_fix ⟨94, by decide⟩ ⟨70, by decide⟩ p hp j hj hq fz1_94_70 fz2_94_70
  · exact match_zero_fix ⟨95, by decide⟩ ⟨70, by decide⟩ p hp j hj hq fz1_95_70 fz2_95_70
  · exact match_zero_fix ⟨96, by decide⟩ ⟨70, by decide⟩ p hp j hj hq fz1_96_70 fz2_96_70
  · exact match_zero_fix ⟨97, by decide⟩ ⟨70, by decide⟩ p hp j hj hq fz1_97_70 fz2_97_70
  · exact match_zero_fix ⟨98, by decide⟩ ⟨70, by decide⟩ p hp j hj hq fz1_98_70 fz2_98_70
  · exact match_zero_fix ⟨99, by decide⟩ ⟨70, by decide⟩ p hp j hj hq fz1_99_70 fz2_99_70
  · exact match_zero_fix ⟨100, by decide⟩ ⟨70, by decide⟩ p hp j hj hq fz1_100_70 fz2_100_70
  · exact match_zero_fix ⟨101, by decide⟩ ⟨70, by decide⟩ p hp j hj hq fz1_101_70 fz2_101_70
  · exact match_zero_fix ⟨102, by decide⟩ ⟨70, by decide⟩ p hp j hj hq fz1_102_70 fz2_102_70
  · exact match_zero_fix ⟨103, by decide⟩ ⟨70, by decide⟩ p hp j hj hq fz1_103_70 fz2_103_70
  · exact match_zero_fix ⟨104, by decide⟩ ⟨70, by decide⟩ p hp j hj hq fz1_104_70 fz2_104_70
  · exact match_zero_fix ⟨105, by decide⟩ ⟨70, by decide⟩ p hp j hj hq fz1_105_70 fz2_105_70
  · exact match_zero_fix ⟨106, by decide⟩ ⟨70, by decide⟩ p hp j hj hq fz1_106_70 fz2_106_70
  · exact match_zero_fix ⟨107, by decide⟩ ⟨70, by decide⟩ p hp j hj hq fz1_107_70 fz2_107_70
  · exact match_zero_fix ⟨108, by decide⟩ ⟨70, by decide⟩ p hp j hj hq fz1_108_70 fz2_108_70
  · exact match_zero_fix ⟨109, by decide⟩ ⟨70, by decide⟩ p hp j hj hq fz1_109_70 fz2_109_70
  · exact match_zero_fix ⟨110, by decide⟩ ⟨70, by decide⟩ p hp j hj hq fz1_110_70 fz2_110_70
  · exact match_zero_fix ⟨111, by decide⟩ ⟨70, by decide⟩ p hp j hj hq fz1_111_70 fz2_111_70
  · exact match_zero_fix ⟨112, by decide⟩ ⟨70, by decide⟩ p hp j hj hq fz1_112_70 fz2_112_70
  · exact match_zero_fix ⟨113, by decide⟩ ⟨70, by decide⟩ p hp j hj hq fz1_113_70 fz2_113_70
  · exact match_zero_fix ⟨114, by decide⟩ ⟨70, by decide⟩ p hp j hj hq fz1_114_70 fz2_114_70
  · exact match_zero_fix ⟨115, by decide⟩ ⟨70, by decide⟩ p hp j hj hq fz1_115_70 fz2_115_70
  · exact match_zero_fix ⟨116, by decide⟩ ⟨70, by decide⟩ p hp j hj hq fz1_116_70 fz2_116_70
  · exact match_zero_fix ⟨117, by decide⟩ ⟨70, by decide⟩ p hp j hj hq fz1_117_70 fz2_117_70
  · exact match_zero_fix ⟨118, by decide⟩ ⟨70, by decide⟩ p hp j hj hq fz1_118_70 fz2_118_70
  · exact pair_119_70 p hp hrep j hj hq
  · exact match_zero_fix ⟨120, by decide⟩ ⟨70, by decide⟩ p hp j hj hq fz1_120_70 fz2_120_70
  · exact match_zero_fix ⟨121, by decide⟩ ⟨70, by decide⟩ p hp j hj hq fz1_121_70 fz2_121_70
  · exact match_zero_fix ⟨122, by decide⟩ ⟨70, by decide⟩ p hp j hj hq fz1_122_70 fz2_122_70
  · exact match_zero_fix ⟨123, by decide⟩ ⟨70, by decide⟩ p hp j hj hq fz1_123_70 fz2_123_70
  · exact match_zero_fix ⟨124, by decide⟩ ⟨70, by decide⟩ p hp j hj hq fz1_124_70 fz2_124_70
  · exact match_zero_fix ⟨125, by decide⟩ ⟨70, by decide⟩ p hp j hj hq fz1_125_70 fz2_125_70
  · exact match_zero_fix ⟨126, by decide⟩ ⟨70, by decide⟩ p hp j hj hq fz1_126_70 fz2_126_70
  · exact match_zero_fix ⟨127, by decide⟩ ⟨70, by decide⟩ p hp j hj hq fz1_127_70 fz2_127_70
  · exact match_zero_fix ⟨128, by decide⟩ ⟨70, by decide⟩ p hp j hj hq fz1_128_70 fz2_128_70
  · exact match_zero_fix ⟨129, by decide⟩ ⟨70, by decide⟩ p hp j hj hq fz1_129_70 fz2_129_70
  · exact match_zero_fix ⟨130, by decide⟩ ⟨70, by decide⟩ p hp j hj hq fz1_130_70 fz2_130_70
  · exact match_zero_fix ⟨131, by decide⟩ ⟨70, by decide⟩ p hp j hj hq fz1_131_70 fz2_131_70
  · exact match_zero_fix ⟨132, by decide⟩ ⟨70, by decide⟩ p hp j hj hq fz1_132_70 fz2_132_70
  · exact match_zero_fix ⟨133, by decide⟩ ⟨70, by decide⟩ p hp j hj hq fz1_133_70 fz2_133_70
  · exact match_zero_fix ⟨134, by decide⟩ ⟨70, by decide⟩ p hp j hj hq fz1_134_70 fz2_134_70
  · exact match_zero_fix ⟨135, by decide⟩ ⟨70, by decide⟩ p hp j hj hq fz1_135_70 fz2_135_70
  · exact match_zero_fix ⟨136, by decide⟩ ⟨70, by decide⟩ p hp j hj hq fz1_136_70 fz2_136_70
  · exact match_zero_fix ⟨137, by decide⟩ ⟨70, by decide⟩ p hp j hj hq fz1_137_70 fz2_137_70
  · exact match_zero_fix ⟨138, by decide⟩ ⟨70, by decide⟩ p hp j hj hq fz1_138_70 fz2_138_70
  · exact match_zero_fix ⟨139, by decide⟩ ⟨70, by decide⟩ p hp j hj hq fz1_139_70 fz2_139_70
  · exact match_zero_fix ⟨140, by decide⟩ ⟨70, by decide⟩ p hp j hj hq fz1_140_70 fz2_140_70
  · exact match_zero_fix ⟨141, by decide⟩ ⟨70, by decide⟩ p hp j hj hq fz1_141_70 fz2_141_70
  · exact match_zero_fix ⟨142, by decide⟩ ⟨70, by decide⟩ p hp j hj hq fz1_142_70 fz2_142_70
  · exact match_zero_fix ⟨143, by decide⟩ ⟨70, by decide⟩ p hp j hj hq fz1_143_70 fz2_143_70
  · exact match_zero_fix ⟨144, by decide⟩ ⟨70, by decide⟩ p hp j hj hq fz1_144_70 fz2_144_70
  · exact match_zero_fix ⟨145, by decide⟩ ⟨70, by decide⟩ p hp j hj hq fz1_145_70 fz2_145_70
  · exact match_zero_fix ⟨146, by decide⟩ ⟨70, by decide⟩ p hp j hj hq fz1_146_70 fz2_146_70
  · exact pair_147_70 p hp hrep j hj hq

theorem master_71 (p : Nat) (hp : p < (Q2.transData.getD 71 []).length)
    (hrep : (Q2.cosetIsRep.getD 71 []).getD p false = true)
    (rK : Fin 148) (j : Nat) (hj : j < (repChars.getD rK.val []).length)
    (hq : (normIsRep.getD rK.val []).getD j false = true) :
    species (Q2.reps (⟨71, by decide⟩ : Fin 148)) (colE2 ⟨71, by decide⟩ p hp)
        (rowE2 rK j hj hq)
      = species (reps (⟨71, by decide⟩ : Fin 148))
        (colE1 ⟨71, by decide⟩ p (transLenTr ⟨71, by decide⟩ p hp)) (rowE1 rK j hj) := by
  rcases rK with ⟨nK, hnK⟩; interval_cases nK
  · exact match_zero_len ⟨0, by decide⟩ ⟨71, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨1, by decide⟩ ⟨71, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨2, by decide⟩ ⟨71, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨3, by decide⟩ ⟨71, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨4, by decide⟩ ⟨71, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨5, by decide⟩ ⟨71, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨6, by decide⟩ ⟨71, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨7, by decide⟩ ⟨71, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨8, by decide⟩ ⟨71, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨9, by decide⟩ ⟨71, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨10, by decide⟩ ⟨71, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨11, by decide⟩ ⟨71, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨12, by decide⟩ ⟨71, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨13, by decide⟩ ⟨71, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨14, by decide⟩ ⟨71, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨15, by decide⟩ ⟨71, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨16, by decide⟩ ⟨71, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨17, by decide⟩ ⟨71, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨18, by decide⟩ ⟨71, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨19, by decide⟩ ⟨71, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨20, by decide⟩ ⟨71, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨21, by decide⟩ ⟨71, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨22, by decide⟩ ⟨71, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨23, by decide⟩ ⟨71, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨24, by decide⟩ ⟨71, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨25, by decide⟩ ⟨71, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨26, by decide⟩ ⟨71, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨27, by decide⟩ ⟨71, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨28, by decide⟩ ⟨71, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨29, by decide⟩ ⟨71, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨30, by decide⟩ ⟨71, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨31, by decide⟩ ⟨71, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨32, by decide⟩ ⟨71, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨33, by decide⟩ ⟨71, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨34, by decide⟩ ⟨71, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨35, by decide⟩ ⟨71, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨36, by decide⟩ ⟨71, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨37, by decide⟩ ⟨71, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨38, by decide⟩ ⟨71, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨39, by decide⟩ ⟨71, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨40, by decide⟩ ⟨71, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨41, by decide⟩ ⟨71, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨42, by decide⟩ ⟨71, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨43, by decide⟩ ⟨71, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨44, by decide⟩ ⟨71, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨45, by decide⟩ ⟨71, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨46, by decide⟩ ⟨71, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨47, by decide⟩ ⟨71, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨48, by decide⟩ ⟨71, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨49, by decide⟩ ⟨71, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨50, by decide⟩ ⟨71, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨51, by decide⟩ ⟨71, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨52, by decide⟩ ⟨71, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨53, by decide⟩ ⟨71, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨54, by decide⟩ ⟨71, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_fix ⟨55, by decide⟩ ⟨71, by decide⟩ p hp j hj hq fz1_55_71 fz2_55_71
  · exact match_zero_fix ⟨56, by decide⟩ ⟨71, by decide⟩ p hp j hj hq fz1_56_71 fz2_56_71
  · exact match_zero_fix ⟨57, by decide⟩ ⟨71, by decide⟩ p hp j hj hq fz1_57_71 fz2_57_71
  · exact match_zero_fix ⟨58, by decide⟩ ⟨71, by decide⟩ p hp j hj hq fz1_58_71 fz2_58_71
  · exact match_zero_fix ⟨59, by decide⟩ ⟨71, by decide⟩ p hp j hj hq fz1_59_71 fz2_59_71
  · exact match_zero_fix ⟨60, by decide⟩ ⟨71, by decide⟩ p hp j hj hq fz1_60_71 fz2_60_71
  · exact match_zero_fix ⟨61, by decide⟩ ⟨71, by decide⟩ p hp j hj hq fz1_61_71 fz2_61_71
  · exact match_zero_fix ⟨62, by decide⟩ ⟨71, by decide⟩ p hp j hj hq fz1_62_71 fz2_62_71
  · exact match_zero_fix ⟨63, by decide⟩ ⟨71, by decide⟩ p hp j hj hq fz1_63_71 fz2_63_71
  · exact match_zero_fix ⟨64, by decide⟩ ⟨71, by decide⟩ p hp j hj hq fz1_64_71 fz2_64_71
  · exact match_zero_fix ⟨65, by decide⟩ ⟨71, by decide⟩ p hp j hj hq fz1_65_71 fz2_65_71
  · exact match_zero_fix ⟨66, by decide⟩ ⟨71, by decide⟩ p hp j hj hq fz1_66_71 fz2_66_71
  · exact match_zero_fix ⟨67, by decide⟩ ⟨71, by decide⟩ p hp j hj hq fz1_67_71 fz2_67_71
  · exact match_zero_fix ⟨68, by decide⟩ ⟨71, by decide⟩ p hp j hj hq fz1_68_71 fz2_68_71
  · exact match_zero_fix ⟨69, by decide⟩ ⟨71, by decide⟩ p hp j hj hq fz1_69_71 fz2_69_71
  · exact match_zero_fix ⟨70, by decide⟩ ⟨71, by decide⟩ p hp j hj hq fz1_70_71 fz2_70_71
  · exact pair_71_71 p hp hrep j hj hq
  · exact match_zero_fix ⟨72, by decide⟩ ⟨71, by decide⟩ p hp j hj hq fz1_72_71 fz2_72_71
  · exact match_zero_fix ⟨73, by decide⟩ ⟨71, by decide⟩ p hp j hj hq fz1_73_71 fz2_73_71
  · exact match_zero_fix ⟨74, by decide⟩ ⟨71, by decide⟩ p hp j hj hq fz1_74_71 fz2_74_71
  · exact match_zero_fix ⟨75, by decide⟩ ⟨71, by decide⟩ p hp j hj hq fz1_75_71 fz2_75_71
  · exact match_zero_fix ⟨76, by decide⟩ ⟨71, by decide⟩ p hp j hj hq fz1_76_71 fz2_76_71
  · exact match_zero_fix ⟨77, by decide⟩ ⟨71, by decide⟩ p hp j hj hq fz1_77_71 fz2_77_71
  · exact match_zero_fix ⟨78, by decide⟩ ⟨71, by decide⟩ p hp j hj hq fz1_78_71 fz2_78_71
  · exact match_zero_fix ⟨79, by decide⟩ ⟨71, by decide⟩ p hp j hj hq fz1_79_71 fz2_79_71
  · exact match_zero_fix ⟨80, by decide⟩ ⟨71, by decide⟩ p hp j hj hq fz1_80_71 fz2_80_71
  · exact match_zero_fix ⟨81, by decide⟩ ⟨71, by decide⟩ p hp j hj hq fz1_81_71 fz2_81_71
  · exact match_zero_fix ⟨82, by decide⟩ ⟨71, by decide⟩ p hp j hj hq fz1_82_71 fz2_82_71
  · exact match_zero_fix ⟨83, by decide⟩ ⟨71, by decide⟩ p hp j hj hq fz1_83_71 fz2_83_71
  · exact match_zero_fix ⟨84, by decide⟩ ⟨71, by decide⟩ p hp j hj hq fz1_84_71 fz2_84_71
  · exact match_zero_fix ⟨85, by decide⟩ ⟨71, by decide⟩ p hp j hj hq fz1_85_71 fz2_85_71
  · exact match_zero_fix ⟨86, by decide⟩ ⟨71, by decide⟩ p hp j hj hq fz1_86_71 fz2_86_71
  · exact match_zero_fix ⟨87, by decide⟩ ⟨71, by decide⟩ p hp j hj hq fz1_87_71 fz2_87_71
  · exact match_zero_fix ⟨88, by decide⟩ ⟨71, by decide⟩ p hp j hj hq fz1_88_71 fz2_88_71
  · exact match_zero_fix ⟨89, by decide⟩ ⟨71, by decide⟩ p hp j hj hq fz1_89_71 fz2_89_71
  · exact match_zero_fix ⟨90, by decide⟩ ⟨71, by decide⟩ p hp j hj hq fz1_90_71 fz2_90_71
  · exact match_zero_fix ⟨91, by decide⟩ ⟨71, by decide⟩ p hp j hj hq fz1_91_71 fz2_91_71
  · exact match_zero_fix ⟨92, by decide⟩ ⟨71, by decide⟩ p hp j hj hq fz1_92_71 fz2_92_71
  · exact match_zero_fix ⟨93, by decide⟩ ⟨71, by decide⟩ p hp j hj hq fz1_93_71 fz2_93_71
  · exact match_zero_fix ⟨94, by decide⟩ ⟨71, by decide⟩ p hp j hj hq fz1_94_71 fz2_94_71
  · exact match_zero_fix ⟨95, by decide⟩ ⟨71, by decide⟩ p hp j hj hq fz1_95_71 fz2_95_71
  · exact match_zero_fix ⟨96, by decide⟩ ⟨71, by decide⟩ p hp j hj hq fz1_96_71 fz2_96_71
  · exact match_zero_fix ⟨97, by decide⟩ ⟨71, by decide⟩ p hp j hj hq fz1_97_71 fz2_97_71
  · exact match_zero_fix ⟨98, by decide⟩ ⟨71, by decide⟩ p hp j hj hq fz1_98_71 fz2_98_71
  · exact match_zero_fix ⟨99, by decide⟩ ⟨71, by decide⟩ p hp j hj hq fz1_99_71 fz2_99_71
  · exact match_zero_fix ⟨100, by decide⟩ ⟨71, by decide⟩ p hp j hj hq fz1_100_71 fz2_100_71
  · exact match_zero_fix ⟨101, by decide⟩ ⟨71, by decide⟩ p hp j hj hq fz1_101_71 fz2_101_71
  · exact match_zero_fix ⟨102, by decide⟩ ⟨71, by decide⟩ p hp j hj hq fz1_102_71 fz2_102_71
  · exact match_zero_fix ⟨103, by decide⟩ ⟨71, by decide⟩ p hp j hj hq fz1_103_71 fz2_103_71
  · exact match_zero_fix ⟨104, by decide⟩ ⟨71, by decide⟩ p hp j hj hq fz1_104_71 fz2_104_71
  · exact match_zero_fix ⟨105, by decide⟩ ⟨71, by decide⟩ p hp j hj hq fz1_105_71 fz2_105_71
  · exact match_zero_fix ⟨106, by decide⟩ ⟨71, by decide⟩ p hp j hj hq fz1_106_71 fz2_106_71
  · exact match_zero_fix ⟨107, by decide⟩ ⟨71, by decide⟩ p hp j hj hq fz1_107_71 fz2_107_71
  · exact match_zero_fix ⟨108, by decide⟩ ⟨71, by decide⟩ p hp j hj hq fz1_108_71 fz2_108_71
  · exact match_zero_fix ⟨109, by decide⟩ ⟨71, by decide⟩ p hp j hj hq fz1_109_71 fz2_109_71
  · exact match_zero_fix ⟨110, by decide⟩ ⟨71, by decide⟩ p hp j hj hq fz1_110_71 fz2_110_71
  · exact match_zero_fix ⟨111, by decide⟩ ⟨71, by decide⟩ p hp j hj hq fz1_111_71 fz2_111_71
  · exact match_zero_fix ⟨112, by decide⟩ ⟨71, by decide⟩ p hp j hj hq fz1_112_71 fz2_112_71
  · exact match_zero_fix ⟨113, by decide⟩ ⟨71, by decide⟩ p hp j hj hq fz1_113_71 fz2_113_71
  · exact match_zero_fix ⟨114, by decide⟩ ⟨71, by decide⟩ p hp j hj hq fz1_114_71 fz2_114_71
  · exact match_zero_fix ⟨115, by decide⟩ ⟨71, by decide⟩ p hp j hj hq fz1_115_71 fz2_115_71
  · exact match_zero_fix ⟨116, by decide⟩ ⟨71, by decide⟩ p hp j hj hq fz1_116_71 fz2_116_71
  · exact match_zero_fix ⟨117, by decide⟩ ⟨71, by decide⟩ p hp j hj hq fz1_117_71 fz2_117_71
  · exact match_zero_fix ⟨118, by decide⟩ ⟨71, by decide⟩ p hp j hj hq fz1_118_71 fz2_118_71
  · exact pair_119_71 p hp hrep j hj hq
  · exact match_zero_fix ⟨120, by decide⟩ ⟨71, by decide⟩ p hp j hj hq fz1_120_71 fz2_120_71
  · exact match_zero_fix ⟨121, by decide⟩ ⟨71, by decide⟩ p hp j hj hq fz1_121_71 fz2_121_71
  · exact match_zero_fix ⟨122, by decide⟩ ⟨71, by decide⟩ p hp j hj hq fz1_122_71 fz2_122_71
  · exact match_zero_fix ⟨123, by decide⟩ ⟨71, by decide⟩ p hp j hj hq fz1_123_71 fz2_123_71
  · exact match_zero_fix ⟨124, by decide⟩ ⟨71, by decide⟩ p hp j hj hq fz1_124_71 fz2_124_71
  · exact match_zero_fix ⟨125, by decide⟩ ⟨71, by decide⟩ p hp j hj hq fz1_125_71 fz2_125_71
  · exact match_zero_fix ⟨126, by decide⟩ ⟨71, by decide⟩ p hp j hj hq fz1_126_71 fz2_126_71
  · exact match_zero_fix ⟨127, by decide⟩ ⟨71, by decide⟩ p hp j hj hq fz1_127_71 fz2_127_71
  · exact match_zero_fix ⟨128, by decide⟩ ⟨71, by decide⟩ p hp j hj hq fz1_128_71 fz2_128_71
  · exact match_zero_fix ⟨129, by decide⟩ ⟨71, by decide⟩ p hp j hj hq fz1_129_71 fz2_129_71
  · exact match_zero_fix ⟨130, by decide⟩ ⟨71, by decide⟩ p hp j hj hq fz1_130_71 fz2_130_71
  · exact match_zero_fix ⟨131, by decide⟩ ⟨71, by decide⟩ p hp j hj hq fz1_131_71 fz2_131_71
  · exact match_zero_fix ⟨132, by decide⟩ ⟨71, by decide⟩ p hp j hj hq fz1_132_71 fz2_132_71
  · exact match_zero_fix ⟨133, by decide⟩ ⟨71, by decide⟩ p hp j hj hq fz1_133_71 fz2_133_71
  · exact match_zero_fix ⟨134, by decide⟩ ⟨71, by decide⟩ p hp j hj hq fz1_134_71 fz2_134_71
  · exact match_zero_fix ⟨135, by decide⟩ ⟨71, by decide⟩ p hp j hj hq fz1_135_71 fz2_135_71
  · exact match_zero_fix ⟨136, by decide⟩ ⟨71, by decide⟩ p hp j hj hq fz1_136_71 fz2_136_71
  · exact match_zero_fix ⟨137, by decide⟩ ⟨71, by decide⟩ p hp j hj hq fz1_137_71 fz2_137_71
  · exact match_zero_fix ⟨138, by decide⟩ ⟨71, by decide⟩ p hp j hj hq fz1_138_71 fz2_138_71
  · exact match_zero_fix ⟨139, by decide⟩ ⟨71, by decide⟩ p hp j hj hq fz1_139_71 fz2_139_71
  · exact match_zero_fix ⟨140, by decide⟩ ⟨71, by decide⟩ p hp j hj hq fz1_140_71 fz2_140_71
  · exact match_zero_fix ⟨141, by decide⟩ ⟨71, by decide⟩ p hp j hj hq fz1_141_71 fz2_141_71
  · exact match_zero_fix ⟨142, by decide⟩ ⟨71, by decide⟩ p hp j hj hq fz1_142_71 fz2_142_71
  · exact match_zero_fix ⟨143, by decide⟩ ⟨71, by decide⟩ p hp j hj hq fz1_143_71 fz2_143_71
  · exact match_zero_fix ⟨144, by decide⟩ ⟨71, by decide⟩ p hp j hj hq fz1_144_71 fz2_144_71
  · exact match_zero_fix ⟨145, by decide⟩ ⟨71, by decide⟩ p hp j hj hq fz1_145_71 fz2_145_71
  · exact match_zero_fix ⟨146, by decide⟩ ⟨71, by decide⟩ p hp j hj hq fz1_146_71 fz2_146_71
  · exact pair_147_71 p hp hrep j hj hq

end LeanDring.P5Presentation
