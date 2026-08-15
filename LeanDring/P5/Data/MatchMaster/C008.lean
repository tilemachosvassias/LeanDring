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
import LeanDring.P5.Data.MatchPair.C006

/-! # Stage-5 per-column-class master theorems, chunk 7 (auto-emitted).  -/

namespace LeanDring.P5Presentation

open MulAction Finset LeanDring.DRing LeanDring.MonGSet

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.style.longLine false

theorem master_56 (p : Nat) (hp : p < (Q2.transData.getD 56 []).length)
    (hrep : (Q2.cosetIsRep.getD 56 []).getD p false = true)
    (rK : Fin 148) (j : Nat) (hj : j < (repChars.getD rK.val []).length)
    (hq : (normIsRep.getD rK.val []).getD j false = true) :
    species (Q2.reps (⟨56, by decide⟩ : Fin 148)) (colE2 ⟨56, by decide⟩ p hp)
        (rowE2 rK j hj hq)
      = species (reps (⟨56, by decide⟩ : Fin 148))
        (colE1 ⟨56, by decide⟩ p (transLenTr ⟨56, by decide⟩ p hp)) (rowE1 rK j hj) := by
  rcases rK with ⟨nK, hnK⟩; interval_cases nK
  · exact match_zero_len ⟨0, by decide⟩ ⟨56, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨1, by decide⟩ ⟨56, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨2, by decide⟩ ⟨56, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨3, by decide⟩ ⟨56, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨4, by decide⟩ ⟨56, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨5, by decide⟩ ⟨56, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨6, by decide⟩ ⟨56, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨7, by decide⟩ ⟨56, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨8, by decide⟩ ⟨56, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨9, by decide⟩ ⟨56, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨10, by decide⟩ ⟨56, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨11, by decide⟩ ⟨56, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨12, by decide⟩ ⟨56, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨13, by decide⟩ ⟨56, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨14, by decide⟩ ⟨56, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨15, by decide⟩ ⟨56, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨16, by decide⟩ ⟨56, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨17, by decide⟩ ⟨56, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨18, by decide⟩ ⟨56, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨19, by decide⟩ ⟨56, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨20, by decide⟩ ⟨56, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨21, by decide⟩ ⟨56, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨22, by decide⟩ ⟨56, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨23, by decide⟩ ⟨56, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨24, by decide⟩ ⟨56, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨25, by decide⟩ ⟨56, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨26, by decide⟩ ⟨56, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨27, by decide⟩ ⟨56, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨28, by decide⟩ ⟨56, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨29, by decide⟩ ⟨56, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨30, by decide⟩ ⟨56, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨31, by decide⟩ ⟨56, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨32, by decide⟩ ⟨56, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨33, by decide⟩ ⟨56, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨34, by decide⟩ ⟨56, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨35, by decide⟩ ⟨56, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨36, by decide⟩ ⟨56, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨37, by decide⟩ ⟨56, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨38, by decide⟩ ⟨56, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨39, by decide⟩ ⟨56, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨40, by decide⟩ ⟨56, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨41, by decide⟩ ⟨56, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨42, by decide⟩ ⟨56, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨43, by decide⟩ ⟨56, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨44, by decide⟩ ⟨56, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨45, by decide⟩ ⟨56, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨46, by decide⟩ ⟨56, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨47, by decide⟩ ⟨56, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨48, by decide⟩ ⟨56, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨49, by decide⟩ ⟨56, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨50, by decide⟩ ⟨56, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨51, by decide⟩ ⟨56, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨52, by decide⟩ ⟨56, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨53, by decide⟩ ⟨56, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨54, by decide⟩ ⟨56, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_fix ⟨55, by decide⟩ ⟨56, by decide⟩ p hp j hj hq fz1_55_56 fz2_55_56
  · exact pair_56_56 p hp hrep j hj hq
  · exact match_zero_fix ⟨57, by decide⟩ ⟨56, by decide⟩ p hp j hj hq fz1_57_56 fz2_57_56
  · exact match_zero_fix ⟨58, by decide⟩ ⟨56, by decide⟩ p hp j hj hq fz1_58_56 fz2_58_56
  · exact match_zero_fix ⟨59, by decide⟩ ⟨56, by decide⟩ p hp j hj hq fz1_59_56 fz2_59_56
  · exact match_zero_fix ⟨60, by decide⟩ ⟨56, by decide⟩ p hp j hj hq fz1_60_56 fz2_60_56
  · exact match_zero_fix ⟨61, by decide⟩ ⟨56, by decide⟩ p hp j hj hq fz1_61_56 fz2_61_56
  · exact match_zero_fix ⟨62, by decide⟩ ⟨56, by decide⟩ p hp j hj hq fz1_62_56 fz2_62_56
  · exact match_zero_fix ⟨63, by decide⟩ ⟨56, by decide⟩ p hp j hj hq fz1_63_56 fz2_63_56
  · exact match_zero_fix ⟨64, by decide⟩ ⟨56, by decide⟩ p hp j hj hq fz1_64_56 fz2_64_56
  · exact match_zero_fix ⟨65, by decide⟩ ⟨56, by decide⟩ p hp j hj hq fz1_65_56 fz2_65_56
  · exact match_zero_fix ⟨66, by decide⟩ ⟨56, by decide⟩ p hp j hj hq fz1_66_56 fz2_66_56
  · exact match_zero_fix ⟨67, by decide⟩ ⟨56, by decide⟩ p hp j hj hq fz1_67_56 fz2_67_56
  · exact match_zero_fix ⟨68, by decide⟩ ⟨56, by decide⟩ p hp j hj hq fz1_68_56 fz2_68_56
  · exact match_zero_fix ⟨69, by decide⟩ ⟨56, by decide⟩ p hp j hj hq fz1_69_56 fz2_69_56
  · exact match_zero_fix ⟨70, by decide⟩ ⟨56, by decide⟩ p hp j hj hq fz1_70_56 fz2_70_56
  · exact match_zero_fix ⟨71, by decide⟩ ⟨56, by decide⟩ p hp j hj hq fz1_71_56 fz2_71_56
  · exact match_zero_fix ⟨72, by decide⟩ ⟨56, by decide⟩ p hp j hj hq fz1_72_56 fz2_72_56
  · exact match_zero_fix ⟨73, by decide⟩ ⟨56, by decide⟩ p hp j hj hq fz1_73_56 fz2_73_56
  · exact match_zero_fix ⟨74, by decide⟩ ⟨56, by decide⟩ p hp j hj hq fz1_74_56 fz2_74_56
  · exact match_zero_fix ⟨75, by decide⟩ ⟨56, by decide⟩ p hp j hj hq fz1_75_56 fz2_75_56
  · exact match_zero_fix ⟨76, by decide⟩ ⟨56, by decide⟩ p hp j hj hq fz1_76_56 fz2_76_56
  · exact match_zero_fix ⟨77, by decide⟩ ⟨56, by decide⟩ p hp j hj hq fz1_77_56 fz2_77_56
  · exact match_zero_fix ⟨78, by decide⟩ ⟨56, by decide⟩ p hp j hj hq fz1_78_56 fz2_78_56
  · exact match_zero_fix ⟨79, by decide⟩ ⟨56, by decide⟩ p hp j hj hq fz1_79_56 fz2_79_56
  · exact match_zero_fix ⟨80, by decide⟩ ⟨56, by decide⟩ p hp j hj hq fz1_80_56 fz2_80_56
  · exact match_zero_fix ⟨81, by decide⟩ ⟨56, by decide⟩ p hp j hj hq fz1_81_56 fz2_81_56
  · exact match_zero_fix ⟨82, by decide⟩ ⟨56, by decide⟩ p hp j hj hq fz1_82_56 fz2_82_56
  · exact match_zero_fix ⟨83, by decide⟩ ⟨56, by decide⟩ p hp j hj hq fz1_83_56 fz2_83_56
  · exact match_zero_fix ⟨84, by decide⟩ ⟨56, by decide⟩ p hp j hj hq fz1_84_56 fz2_84_56
  · exact match_zero_fix ⟨85, by decide⟩ ⟨56, by decide⟩ p hp j hj hq fz1_85_56 fz2_85_56
  · exact match_zero_fix ⟨86, by decide⟩ ⟨56, by decide⟩ p hp j hj hq fz1_86_56 fz2_86_56
  · exact match_zero_fix ⟨87, by decide⟩ ⟨56, by decide⟩ p hp j hj hq fz1_87_56 fz2_87_56
  · exact match_zero_fix ⟨88, by decide⟩ ⟨56, by decide⟩ p hp j hj hq fz1_88_56 fz2_88_56
  · exact match_zero_fix ⟨89, by decide⟩ ⟨56, by decide⟩ p hp j hj hq fz1_89_56 fz2_89_56
  · exact match_zero_fix ⟨90, by decide⟩ ⟨56, by decide⟩ p hp j hj hq fz1_90_56 fz2_90_56
  · exact match_zero_fix ⟨91, by decide⟩ ⟨56, by decide⟩ p hp j hj hq fz1_91_56 fz2_91_56
  · exact match_zero_fix ⟨92, by decide⟩ ⟨56, by decide⟩ p hp j hj hq fz1_92_56 fz2_92_56
  · exact match_zero_fix ⟨93, by decide⟩ ⟨56, by decide⟩ p hp j hj hq fz1_93_56 fz2_93_56
  · exact match_zero_fix ⟨94, by decide⟩ ⟨56, by decide⟩ p hp j hj hq fz1_94_56 fz2_94_56
  · exact match_zero_fix ⟨95, by decide⟩ ⟨56, by decide⟩ p hp j hj hq fz1_95_56 fz2_95_56
  · exact match_zero_fix ⟨96, by decide⟩ ⟨56, by decide⟩ p hp j hj hq fz1_96_56 fz2_96_56
  · exact match_zero_fix ⟨97, by decide⟩ ⟨56, by decide⟩ p hp j hj hq fz1_97_56 fz2_97_56
  · exact match_zero_fix ⟨98, by decide⟩ ⟨56, by decide⟩ p hp j hj hq fz1_98_56 fz2_98_56
  · exact match_zero_fix ⟨99, by decide⟩ ⟨56, by decide⟩ p hp j hj hq fz1_99_56 fz2_99_56
  · exact match_zero_fix ⟨100, by decide⟩ ⟨56, by decide⟩ p hp j hj hq fz1_100_56 fz2_100_56
  · exact match_zero_fix ⟨101, by decide⟩ ⟨56, by decide⟩ p hp j hj hq fz1_101_56 fz2_101_56
  · exact match_zero_fix ⟨102, by decide⟩ ⟨56, by decide⟩ p hp j hj hq fz1_102_56 fz2_102_56
  · exact match_zero_fix ⟨103, by decide⟩ ⟨56, by decide⟩ p hp j hj hq fz1_103_56 fz2_103_56
  · exact match_zero_fix ⟨104, by decide⟩ ⟨56, by decide⟩ p hp j hj hq fz1_104_56 fz2_104_56
  · exact match_zero_fix ⟨105, by decide⟩ ⟨56, by decide⟩ p hp j hj hq fz1_105_56 fz2_105_56
  · exact match_zero_fix ⟨106, by decide⟩ ⟨56, by decide⟩ p hp j hj hq fz1_106_56 fz2_106_56
  · exact match_zero_fix ⟨107, by decide⟩ ⟨56, by decide⟩ p hp j hj hq fz1_107_56 fz2_107_56
  · exact match_zero_fix ⟨108, by decide⟩ ⟨56, by decide⟩ p hp j hj hq fz1_108_56 fz2_108_56
  · exact match_zero_fix ⟨109, by decide⟩ ⟨56, by decide⟩ p hp j hj hq fz1_109_56 fz2_109_56
  · exact match_zero_fix ⟨110, by decide⟩ ⟨56, by decide⟩ p hp j hj hq fz1_110_56 fz2_110_56
  · exact match_zero_fix ⟨111, by decide⟩ ⟨56, by decide⟩ p hp j hj hq fz1_111_56 fz2_111_56
  · exact match_zero_fix ⟨112, by decide⟩ ⟨56, by decide⟩ p hp j hj hq fz1_112_56 fz2_112_56
  · exact match_zero_fix ⟨113, by decide⟩ ⟨56, by decide⟩ p hp j hj hq fz1_113_56 fz2_113_56
  · exact match_zero_fix ⟨114, by decide⟩ ⟨56, by decide⟩ p hp j hj hq fz1_114_56 fz2_114_56
  · exact match_zero_fix ⟨115, by decide⟩ ⟨56, by decide⟩ p hp j hj hq fz1_115_56 fz2_115_56
  · exact pair_116_56 p hp hrep j hj hq
  · exact match_zero_fix ⟨117, by decide⟩ ⟨56, by decide⟩ p hp j hj hq fz1_117_56 fz2_117_56
  · exact match_zero_fix ⟨118, by decide⟩ ⟨56, by decide⟩ p hp j hj hq fz1_118_56 fz2_118_56
  · exact match_zero_fix ⟨119, by decide⟩ ⟨56, by decide⟩ p hp j hj hq fz1_119_56 fz2_119_56
  · exact match_zero_fix ⟨120, by decide⟩ ⟨56, by decide⟩ p hp j hj hq fz1_120_56 fz2_120_56
  · exact match_zero_fix ⟨121, by decide⟩ ⟨56, by decide⟩ p hp j hj hq fz1_121_56 fz2_121_56
  · exact match_zero_fix ⟨122, by decide⟩ ⟨56, by decide⟩ p hp j hj hq fz1_122_56 fz2_122_56
  · exact match_zero_fix ⟨123, by decide⟩ ⟨56, by decide⟩ p hp j hj hq fz1_123_56 fz2_123_56
  · exact match_zero_fix ⟨124, by decide⟩ ⟨56, by decide⟩ p hp j hj hq fz1_124_56 fz2_124_56
  · exact match_zero_fix ⟨125, by decide⟩ ⟨56, by decide⟩ p hp j hj hq fz1_125_56 fz2_125_56
  · exact match_zero_fix ⟨126, by decide⟩ ⟨56, by decide⟩ p hp j hj hq fz1_126_56 fz2_126_56
  · exact match_zero_fix ⟨127, by decide⟩ ⟨56, by decide⟩ p hp j hj hq fz1_127_56 fz2_127_56
  · exact match_zero_fix ⟨128, by decide⟩ ⟨56, by decide⟩ p hp j hj hq fz1_128_56 fz2_128_56
  · exact match_zero_fix ⟨129, by decide⟩ ⟨56, by decide⟩ p hp j hj hq fz1_129_56 fz2_129_56
  · exact match_zero_fix ⟨130, by decide⟩ ⟨56, by decide⟩ p hp j hj hq fz1_130_56 fz2_130_56
  · exact match_zero_fix ⟨131, by decide⟩ ⟨56, by decide⟩ p hp j hj hq fz1_131_56 fz2_131_56
  · exact match_zero_fix ⟨132, by decide⟩ ⟨56, by decide⟩ p hp j hj hq fz1_132_56 fz2_132_56
  · exact match_zero_fix ⟨133, by decide⟩ ⟨56, by decide⟩ p hp j hj hq fz1_133_56 fz2_133_56
  · exact match_zero_fix ⟨134, by decide⟩ ⟨56, by decide⟩ p hp j hj hq fz1_134_56 fz2_134_56
  · exact match_zero_fix ⟨135, by decide⟩ ⟨56, by decide⟩ p hp j hj hq fz1_135_56 fz2_135_56
  · exact match_zero_fix ⟨136, by decide⟩ ⟨56, by decide⟩ p hp j hj hq fz1_136_56 fz2_136_56
  · exact match_zero_fix ⟨137, by decide⟩ ⟨56, by decide⟩ p hp j hj hq fz1_137_56 fz2_137_56
  · exact match_zero_fix ⟨138, by decide⟩ ⟨56, by decide⟩ p hp j hj hq fz1_138_56 fz2_138_56
  · exact match_zero_fix ⟨139, by decide⟩ ⟨56, by decide⟩ p hp j hj hq fz1_139_56 fz2_139_56
  · exact match_zero_fix ⟨140, by decide⟩ ⟨56, by decide⟩ p hp j hj hq fz1_140_56 fz2_140_56
  · exact match_zero_fix ⟨141, by decide⟩ ⟨56, by decide⟩ p hp j hj hq fz1_141_56 fz2_141_56
  · exact match_zero_fix ⟨142, by decide⟩ ⟨56, by decide⟩ p hp j hj hq fz1_142_56 fz2_142_56
  · exact match_zero_fix ⟨143, by decide⟩ ⟨56, by decide⟩ p hp j hj hq fz1_143_56 fz2_143_56
  · exact match_zero_fix ⟨144, by decide⟩ ⟨56, by decide⟩ p hp j hj hq fz1_144_56 fz2_144_56
  · exact match_zero_fix ⟨145, by decide⟩ ⟨56, by decide⟩ p hp j hj hq fz1_145_56 fz2_145_56
  · exact match_zero_fix ⟨146, by decide⟩ ⟨56, by decide⟩ p hp j hj hq fz1_146_56 fz2_146_56
  · exact pair_147_56 p hp hrep j hj hq

theorem master_57 (p : Nat) (hp : p < (Q2.transData.getD 57 []).length)
    (hrep : (Q2.cosetIsRep.getD 57 []).getD p false = true)
    (rK : Fin 148) (j : Nat) (hj : j < (repChars.getD rK.val []).length)
    (hq : (normIsRep.getD rK.val []).getD j false = true) :
    species (Q2.reps (⟨57, by decide⟩ : Fin 148)) (colE2 ⟨57, by decide⟩ p hp)
        (rowE2 rK j hj hq)
      = species (reps (⟨57, by decide⟩ : Fin 148))
        (colE1 ⟨57, by decide⟩ p (transLenTr ⟨57, by decide⟩ p hp)) (rowE1 rK j hj) := by
  rcases rK with ⟨nK, hnK⟩; interval_cases nK
  · exact match_zero_len ⟨0, by decide⟩ ⟨57, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨1, by decide⟩ ⟨57, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨2, by decide⟩ ⟨57, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨3, by decide⟩ ⟨57, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨4, by decide⟩ ⟨57, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨5, by decide⟩ ⟨57, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨6, by decide⟩ ⟨57, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨7, by decide⟩ ⟨57, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨8, by decide⟩ ⟨57, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨9, by decide⟩ ⟨57, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨10, by decide⟩ ⟨57, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨11, by decide⟩ ⟨57, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨12, by decide⟩ ⟨57, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨13, by decide⟩ ⟨57, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨14, by decide⟩ ⟨57, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨15, by decide⟩ ⟨57, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨16, by decide⟩ ⟨57, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨17, by decide⟩ ⟨57, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨18, by decide⟩ ⟨57, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨19, by decide⟩ ⟨57, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨20, by decide⟩ ⟨57, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨21, by decide⟩ ⟨57, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨22, by decide⟩ ⟨57, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨23, by decide⟩ ⟨57, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨24, by decide⟩ ⟨57, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨25, by decide⟩ ⟨57, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨26, by decide⟩ ⟨57, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨27, by decide⟩ ⟨57, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨28, by decide⟩ ⟨57, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨29, by decide⟩ ⟨57, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨30, by decide⟩ ⟨57, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨31, by decide⟩ ⟨57, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨32, by decide⟩ ⟨57, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨33, by decide⟩ ⟨57, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨34, by decide⟩ ⟨57, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨35, by decide⟩ ⟨57, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨36, by decide⟩ ⟨57, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨37, by decide⟩ ⟨57, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨38, by decide⟩ ⟨57, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨39, by decide⟩ ⟨57, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨40, by decide⟩ ⟨57, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨41, by decide⟩ ⟨57, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨42, by decide⟩ ⟨57, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨43, by decide⟩ ⟨57, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨44, by decide⟩ ⟨57, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨45, by decide⟩ ⟨57, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨46, by decide⟩ ⟨57, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨47, by decide⟩ ⟨57, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨48, by decide⟩ ⟨57, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨49, by decide⟩ ⟨57, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨50, by decide⟩ ⟨57, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨51, by decide⟩ ⟨57, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨52, by decide⟩ ⟨57, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨53, by decide⟩ ⟨57, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨54, by decide⟩ ⟨57, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_fix ⟨55, by decide⟩ ⟨57, by decide⟩ p hp j hj hq fz1_55_57 fz2_55_57
  · exact match_zero_fix ⟨56, by decide⟩ ⟨57, by decide⟩ p hp j hj hq fz1_56_57 fz2_56_57
  · exact pair_57_57 p hp hrep j hj hq
  · exact match_zero_fix ⟨58, by decide⟩ ⟨57, by decide⟩ p hp j hj hq fz1_58_57 fz2_58_57
  · exact match_zero_fix ⟨59, by decide⟩ ⟨57, by decide⟩ p hp j hj hq fz1_59_57 fz2_59_57
  · exact match_zero_fix ⟨60, by decide⟩ ⟨57, by decide⟩ p hp j hj hq fz1_60_57 fz2_60_57
  · exact match_zero_fix ⟨61, by decide⟩ ⟨57, by decide⟩ p hp j hj hq fz1_61_57 fz2_61_57
  · exact match_zero_fix ⟨62, by decide⟩ ⟨57, by decide⟩ p hp j hj hq fz1_62_57 fz2_62_57
  · exact match_zero_fix ⟨63, by decide⟩ ⟨57, by decide⟩ p hp j hj hq fz1_63_57 fz2_63_57
  · exact match_zero_fix ⟨64, by decide⟩ ⟨57, by decide⟩ p hp j hj hq fz1_64_57 fz2_64_57
  · exact match_zero_fix ⟨65, by decide⟩ ⟨57, by decide⟩ p hp j hj hq fz1_65_57 fz2_65_57
  · exact match_zero_fix ⟨66, by decide⟩ ⟨57, by decide⟩ p hp j hj hq fz1_66_57 fz2_66_57
  · exact match_zero_fix ⟨67, by decide⟩ ⟨57, by decide⟩ p hp j hj hq fz1_67_57 fz2_67_57
  · exact match_zero_fix ⟨68, by decide⟩ ⟨57, by decide⟩ p hp j hj hq fz1_68_57 fz2_68_57
  · exact match_zero_fix ⟨69, by decide⟩ ⟨57, by decide⟩ p hp j hj hq fz1_69_57 fz2_69_57
  · exact match_zero_fix ⟨70, by decide⟩ ⟨57, by decide⟩ p hp j hj hq fz1_70_57 fz2_70_57
  · exact match_zero_fix ⟨71, by decide⟩ ⟨57, by decide⟩ p hp j hj hq fz1_71_57 fz2_71_57
  · exact match_zero_fix ⟨72, by decide⟩ ⟨57, by decide⟩ p hp j hj hq fz1_72_57 fz2_72_57
  · exact match_zero_fix ⟨73, by decide⟩ ⟨57, by decide⟩ p hp j hj hq fz1_73_57 fz2_73_57
  · exact match_zero_fix ⟨74, by decide⟩ ⟨57, by decide⟩ p hp j hj hq fz1_74_57 fz2_74_57
  · exact match_zero_fix ⟨75, by decide⟩ ⟨57, by decide⟩ p hp j hj hq fz1_75_57 fz2_75_57
  · exact match_zero_fix ⟨76, by decide⟩ ⟨57, by decide⟩ p hp j hj hq fz1_76_57 fz2_76_57
  · exact match_zero_fix ⟨77, by decide⟩ ⟨57, by decide⟩ p hp j hj hq fz1_77_57 fz2_77_57
  · exact match_zero_fix ⟨78, by decide⟩ ⟨57, by decide⟩ p hp j hj hq fz1_78_57 fz2_78_57
  · exact match_zero_fix ⟨79, by decide⟩ ⟨57, by decide⟩ p hp j hj hq fz1_79_57 fz2_79_57
  · exact match_zero_fix ⟨80, by decide⟩ ⟨57, by decide⟩ p hp j hj hq fz1_80_57 fz2_80_57
  · exact match_zero_fix ⟨81, by decide⟩ ⟨57, by decide⟩ p hp j hj hq fz1_81_57 fz2_81_57
  · exact match_zero_fix ⟨82, by decide⟩ ⟨57, by decide⟩ p hp j hj hq fz1_82_57 fz2_82_57
  · exact match_zero_fix ⟨83, by decide⟩ ⟨57, by decide⟩ p hp j hj hq fz1_83_57 fz2_83_57
  · exact match_zero_fix ⟨84, by decide⟩ ⟨57, by decide⟩ p hp j hj hq fz1_84_57 fz2_84_57
  · exact match_zero_fix ⟨85, by decide⟩ ⟨57, by decide⟩ p hp j hj hq fz1_85_57 fz2_85_57
  · exact match_zero_fix ⟨86, by decide⟩ ⟨57, by decide⟩ p hp j hj hq fz1_86_57 fz2_86_57
  · exact match_zero_fix ⟨87, by decide⟩ ⟨57, by decide⟩ p hp j hj hq fz1_87_57 fz2_87_57
  · exact match_zero_fix ⟨88, by decide⟩ ⟨57, by decide⟩ p hp j hj hq fz1_88_57 fz2_88_57
  · exact match_zero_fix ⟨89, by decide⟩ ⟨57, by decide⟩ p hp j hj hq fz1_89_57 fz2_89_57
  · exact match_zero_fix ⟨90, by decide⟩ ⟨57, by decide⟩ p hp j hj hq fz1_90_57 fz2_90_57
  · exact match_zero_fix ⟨91, by decide⟩ ⟨57, by decide⟩ p hp j hj hq fz1_91_57 fz2_91_57
  · exact match_zero_fix ⟨92, by decide⟩ ⟨57, by decide⟩ p hp j hj hq fz1_92_57 fz2_92_57
  · exact match_zero_fix ⟨93, by decide⟩ ⟨57, by decide⟩ p hp j hj hq fz1_93_57 fz2_93_57
  · exact match_zero_fix ⟨94, by decide⟩ ⟨57, by decide⟩ p hp j hj hq fz1_94_57 fz2_94_57
  · exact match_zero_fix ⟨95, by decide⟩ ⟨57, by decide⟩ p hp j hj hq fz1_95_57 fz2_95_57
  · exact match_zero_fix ⟨96, by decide⟩ ⟨57, by decide⟩ p hp j hj hq fz1_96_57 fz2_96_57
  · exact match_zero_fix ⟨97, by decide⟩ ⟨57, by decide⟩ p hp j hj hq fz1_97_57 fz2_97_57
  · exact match_zero_fix ⟨98, by decide⟩ ⟨57, by decide⟩ p hp j hj hq fz1_98_57 fz2_98_57
  · exact match_zero_fix ⟨99, by decide⟩ ⟨57, by decide⟩ p hp j hj hq fz1_99_57 fz2_99_57
  · exact match_zero_fix ⟨100, by decide⟩ ⟨57, by decide⟩ p hp j hj hq fz1_100_57 fz2_100_57
  · exact match_zero_fix ⟨101, by decide⟩ ⟨57, by decide⟩ p hp j hj hq fz1_101_57 fz2_101_57
  · exact match_zero_fix ⟨102, by decide⟩ ⟨57, by decide⟩ p hp j hj hq fz1_102_57 fz2_102_57
  · exact match_zero_fix ⟨103, by decide⟩ ⟨57, by decide⟩ p hp j hj hq fz1_103_57 fz2_103_57
  · exact match_zero_fix ⟨104, by decide⟩ ⟨57, by decide⟩ p hp j hj hq fz1_104_57 fz2_104_57
  · exact match_zero_fix ⟨105, by decide⟩ ⟨57, by decide⟩ p hp j hj hq fz1_105_57 fz2_105_57
  · exact match_zero_fix ⟨106, by decide⟩ ⟨57, by decide⟩ p hp j hj hq fz1_106_57 fz2_106_57
  · exact match_zero_fix ⟨107, by decide⟩ ⟨57, by decide⟩ p hp j hj hq fz1_107_57 fz2_107_57
  · exact match_zero_fix ⟨108, by decide⟩ ⟨57, by decide⟩ p hp j hj hq fz1_108_57 fz2_108_57
  · exact match_zero_fix ⟨109, by decide⟩ ⟨57, by decide⟩ p hp j hj hq fz1_109_57 fz2_109_57
  · exact match_zero_fix ⟨110, by decide⟩ ⟨57, by decide⟩ p hp j hj hq fz1_110_57 fz2_110_57
  · exact match_zero_fix ⟨111, by decide⟩ ⟨57, by decide⟩ p hp j hj hq fz1_111_57 fz2_111_57
  · exact match_zero_fix ⟨112, by decide⟩ ⟨57, by decide⟩ p hp j hj hq fz1_112_57 fz2_112_57
  · exact match_zero_fix ⟨113, by decide⟩ ⟨57, by decide⟩ p hp j hj hq fz1_113_57 fz2_113_57
  · exact match_zero_fix ⟨114, by decide⟩ ⟨57, by decide⟩ p hp j hj hq fz1_114_57 fz2_114_57
  · exact match_zero_fix ⟨115, by decide⟩ ⟨57, by decide⟩ p hp j hj hq fz1_115_57 fz2_115_57
  · exact pair_116_57 p hp hrep j hj hq
  · exact match_zero_fix ⟨117, by decide⟩ ⟨57, by decide⟩ p hp j hj hq fz1_117_57 fz2_117_57
  · exact match_zero_fix ⟨118, by decide⟩ ⟨57, by decide⟩ p hp j hj hq fz1_118_57 fz2_118_57
  · exact match_zero_fix ⟨119, by decide⟩ ⟨57, by decide⟩ p hp j hj hq fz1_119_57 fz2_119_57
  · exact match_zero_fix ⟨120, by decide⟩ ⟨57, by decide⟩ p hp j hj hq fz1_120_57 fz2_120_57
  · exact match_zero_fix ⟨121, by decide⟩ ⟨57, by decide⟩ p hp j hj hq fz1_121_57 fz2_121_57
  · exact match_zero_fix ⟨122, by decide⟩ ⟨57, by decide⟩ p hp j hj hq fz1_122_57 fz2_122_57
  · exact match_zero_fix ⟨123, by decide⟩ ⟨57, by decide⟩ p hp j hj hq fz1_123_57 fz2_123_57
  · exact match_zero_fix ⟨124, by decide⟩ ⟨57, by decide⟩ p hp j hj hq fz1_124_57 fz2_124_57
  · exact match_zero_fix ⟨125, by decide⟩ ⟨57, by decide⟩ p hp j hj hq fz1_125_57 fz2_125_57
  · exact match_zero_fix ⟨126, by decide⟩ ⟨57, by decide⟩ p hp j hj hq fz1_126_57 fz2_126_57
  · exact match_zero_fix ⟨127, by decide⟩ ⟨57, by decide⟩ p hp j hj hq fz1_127_57 fz2_127_57
  · exact match_zero_fix ⟨128, by decide⟩ ⟨57, by decide⟩ p hp j hj hq fz1_128_57 fz2_128_57
  · exact match_zero_fix ⟨129, by decide⟩ ⟨57, by decide⟩ p hp j hj hq fz1_129_57 fz2_129_57
  · exact match_zero_fix ⟨130, by decide⟩ ⟨57, by decide⟩ p hp j hj hq fz1_130_57 fz2_130_57
  · exact match_zero_fix ⟨131, by decide⟩ ⟨57, by decide⟩ p hp j hj hq fz1_131_57 fz2_131_57
  · exact match_zero_fix ⟨132, by decide⟩ ⟨57, by decide⟩ p hp j hj hq fz1_132_57 fz2_132_57
  · exact match_zero_fix ⟨133, by decide⟩ ⟨57, by decide⟩ p hp j hj hq fz1_133_57 fz2_133_57
  · exact match_zero_fix ⟨134, by decide⟩ ⟨57, by decide⟩ p hp j hj hq fz1_134_57 fz2_134_57
  · exact match_zero_fix ⟨135, by decide⟩ ⟨57, by decide⟩ p hp j hj hq fz1_135_57 fz2_135_57
  · exact match_zero_fix ⟨136, by decide⟩ ⟨57, by decide⟩ p hp j hj hq fz1_136_57 fz2_136_57
  · exact match_zero_fix ⟨137, by decide⟩ ⟨57, by decide⟩ p hp j hj hq fz1_137_57 fz2_137_57
  · exact match_zero_fix ⟨138, by decide⟩ ⟨57, by decide⟩ p hp j hj hq fz1_138_57 fz2_138_57
  · exact match_zero_fix ⟨139, by decide⟩ ⟨57, by decide⟩ p hp j hj hq fz1_139_57 fz2_139_57
  · exact match_zero_fix ⟨140, by decide⟩ ⟨57, by decide⟩ p hp j hj hq fz1_140_57 fz2_140_57
  · exact match_zero_fix ⟨141, by decide⟩ ⟨57, by decide⟩ p hp j hj hq fz1_141_57 fz2_141_57
  · exact match_zero_fix ⟨142, by decide⟩ ⟨57, by decide⟩ p hp j hj hq fz1_142_57 fz2_142_57
  · exact match_zero_fix ⟨143, by decide⟩ ⟨57, by decide⟩ p hp j hj hq fz1_143_57 fz2_143_57
  · exact match_zero_fix ⟨144, by decide⟩ ⟨57, by decide⟩ p hp j hj hq fz1_144_57 fz2_144_57
  · exact match_zero_fix ⟨145, by decide⟩ ⟨57, by decide⟩ p hp j hj hq fz1_145_57 fz2_145_57
  · exact match_zero_fix ⟨146, by decide⟩ ⟨57, by decide⟩ p hp j hj hq fz1_146_57 fz2_146_57
  · exact pair_147_57 p hp hrep j hj hq

theorem master_58 (p : Nat) (hp : p < (Q2.transData.getD 58 []).length)
    (hrep : (Q2.cosetIsRep.getD 58 []).getD p false = true)
    (rK : Fin 148) (j : Nat) (hj : j < (repChars.getD rK.val []).length)
    (hq : (normIsRep.getD rK.val []).getD j false = true) :
    species (Q2.reps (⟨58, by decide⟩ : Fin 148)) (colE2 ⟨58, by decide⟩ p hp)
        (rowE2 rK j hj hq)
      = species (reps (⟨58, by decide⟩ : Fin 148))
        (colE1 ⟨58, by decide⟩ p (transLenTr ⟨58, by decide⟩ p hp)) (rowE1 rK j hj) := by
  rcases rK with ⟨nK, hnK⟩; interval_cases nK
  · exact match_zero_len ⟨0, by decide⟩ ⟨58, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨1, by decide⟩ ⟨58, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨2, by decide⟩ ⟨58, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨3, by decide⟩ ⟨58, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨4, by decide⟩ ⟨58, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨5, by decide⟩ ⟨58, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨6, by decide⟩ ⟨58, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨7, by decide⟩ ⟨58, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨8, by decide⟩ ⟨58, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨9, by decide⟩ ⟨58, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨10, by decide⟩ ⟨58, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨11, by decide⟩ ⟨58, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨12, by decide⟩ ⟨58, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨13, by decide⟩ ⟨58, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨14, by decide⟩ ⟨58, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨15, by decide⟩ ⟨58, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨16, by decide⟩ ⟨58, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨17, by decide⟩ ⟨58, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨18, by decide⟩ ⟨58, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨19, by decide⟩ ⟨58, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨20, by decide⟩ ⟨58, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨21, by decide⟩ ⟨58, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨22, by decide⟩ ⟨58, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨23, by decide⟩ ⟨58, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨24, by decide⟩ ⟨58, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨25, by decide⟩ ⟨58, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨26, by decide⟩ ⟨58, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨27, by decide⟩ ⟨58, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨28, by decide⟩ ⟨58, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨29, by decide⟩ ⟨58, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨30, by decide⟩ ⟨58, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨31, by decide⟩ ⟨58, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨32, by decide⟩ ⟨58, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨33, by decide⟩ ⟨58, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨34, by decide⟩ ⟨58, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨35, by decide⟩ ⟨58, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨36, by decide⟩ ⟨58, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨37, by decide⟩ ⟨58, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨38, by decide⟩ ⟨58, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨39, by decide⟩ ⟨58, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨40, by decide⟩ ⟨58, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨41, by decide⟩ ⟨58, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨42, by decide⟩ ⟨58, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨43, by decide⟩ ⟨58, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨44, by decide⟩ ⟨58, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨45, by decide⟩ ⟨58, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨46, by decide⟩ ⟨58, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨47, by decide⟩ ⟨58, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨48, by decide⟩ ⟨58, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨49, by decide⟩ ⟨58, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨50, by decide⟩ ⟨58, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨51, by decide⟩ ⟨58, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨52, by decide⟩ ⟨58, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨53, by decide⟩ ⟨58, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨54, by decide⟩ ⟨58, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_fix ⟨55, by decide⟩ ⟨58, by decide⟩ p hp j hj hq fz1_55_58 fz2_55_58
  · exact match_zero_fix ⟨56, by decide⟩ ⟨58, by decide⟩ p hp j hj hq fz1_56_58 fz2_56_58
  · exact match_zero_fix ⟨57, by decide⟩ ⟨58, by decide⟩ p hp j hj hq fz1_57_58 fz2_57_58
  · exact pair_58_58 p hp hrep j hj hq
  · exact match_zero_fix ⟨59, by decide⟩ ⟨58, by decide⟩ p hp j hj hq fz1_59_58 fz2_59_58
  · exact match_zero_fix ⟨60, by decide⟩ ⟨58, by decide⟩ p hp j hj hq fz1_60_58 fz2_60_58
  · exact match_zero_fix ⟨61, by decide⟩ ⟨58, by decide⟩ p hp j hj hq fz1_61_58 fz2_61_58
  · exact match_zero_fix ⟨62, by decide⟩ ⟨58, by decide⟩ p hp j hj hq fz1_62_58 fz2_62_58
  · exact match_zero_fix ⟨63, by decide⟩ ⟨58, by decide⟩ p hp j hj hq fz1_63_58 fz2_63_58
  · exact match_zero_fix ⟨64, by decide⟩ ⟨58, by decide⟩ p hp j hj hq fz1_64_58 fz2_64_58
  · exact match_zero_fix ⟨65, by decide⟩ ⟨58, by decide⟩ p hp j hj hq fz1_65_58 fz2_65_58
  · exact match_zero_fix ⟨66, by decide⟩ ⟨58, by decide⟩ p hp j hj hq fz1_66_58 fz2_66_58
  · exact match_zero_fix ⟨67, by decide⟩ ⟨58, by decide⟩ p hp j hj hq fz1_67_58 fz2_67_58
  · exact match_zero_fix ⟨68, by decide⟩ ⟨58, by decide⟩ p hp j hj hq fz1_68_58 fz2_68_58
  · exact match_zero_fix ⟨69, by decide⟩ ⟨58, by decide⟩ p hp j hj hq fz1_69_58 fz2_69_58
  · exact match_zero_fix ⟨70, by decide⟩ ⟨58, by decide⟩ p hp j hj hq fz1_70_58 fz2_70_58
  · exact match_zero_fix ⟨71, by decide⟩ ⟨58, by decide⟩ p hp j hj hq fz1_71_58 fz2_71_58
  · exact match_zero_fix ⟨72, by decide⟩ ⟨58, by decide⟩ p hp j hj hq fz1_72_58 fz2_72_58
  · exact match_zero_fix ⟨73, by decide⟩ ⟨58, by decide⟩ p hp j hj hq fz1_73_58 fz2_73_58
  · exact match_zero_fix ⟨74, by decide⟩ ⟨58, by decide⟩ p hp j hj hq fz1_74_58 fz2_74_58
  · exact match_zero_fix ⟨75, by decide⟩ ⟨58, by decide⟩ p hp j hj hq fz1_75_58 fz2_75_58
  · exact match_zero_fix ⟨76, by decide⟩ ⟨58, by decide⟩ p hp j hj hq fz1_76_58 fz2_76_58
  · exact match_zero_fix ⟨77, by decide⟩ ⟨58, by decide⟩ p hp j hj hq fz1_77_58 fz2_77_58
  · exact match_zero_fix ⟨78, by decide⟩ ⟨58, by decide⟩ p hp j hj hq fz1_78_58 fz2_78_58
  · exact match_zero_fix ⟨79, by decide⟩ ⟨58, by decide⟩ p hp j hj hq fz1_79_58 fz2_79_58
  · exact match_zero_fix ⟨80, by decide⟩ ⟨58, by decide⟩ p hp j hj hq fz1_80_58 fz2_80_58
  · exact match_zero_fix ⟨81, by decide⟩ ⟨58, by decide⟩ p hp j hj hq fz1_81_58 fz2_81_58
  · exact match_zero_fix ⟨82, by decide⟩ ⟨58, by decide⟩ p hp j hj hq fz1_82_58 fz2_82_58
  · exact match_zero_fix ⟨83, by decide⟩ ⟨58, by decide⟩ p hp j hj hq fz1_83_58 fz2_83_58
  · exact match_zero_fix ⟨84, by decide⟩ ⟨58, by decide⟩ p hp j hj hq fz1_84_58 fz2_84_58
  · exact match_zero_fix ⟨85, by decide⟩ ⟨58, by decide⟩ p hp j hj hq fz1_85_58 fz2_85_58
  · exact match_zero_fix ⟨86, by decide⟩ ⟨58, by decide⟩ p hp j hj hq fz1_86_58 fz2_86_58
  · exact match_zero_fix ⟨87, by decide⟩ ⟨58, by decide⟩ p hp j hj hq fz1_87_58 fz2_87_58
  · exact match_zero_fix ⟨88, by decide⟩ ⟨58, by decide⟩ p hp j hj hq fz1_88_58 fz2_88_58
  · exact match_zero_fix ⟨89, by decide⟩ ⟨58, by decide⟩ p hp j hj hq fz1_89_58 fz2_89_58
  · exact match_zero_fix ⟨90, by decide⟩ ⟨58, by decide⟩ p hp j hj hq fz1_90_58 fz2_90_58
  · exact match_zero_fix ⟨91, by decide⟩ ⟨58, by decide⟩ p hp j hj hq fz1_91_58 fz2_91_58
  · exact match_zero_fix ⟨92, by decide⟩ ⟨58, by decide⟩ p hp j hj hq fz1_92_58 fz2_92_58
  · exact match_zero_fix ⟨93, by decide⟩ ⟨58, by decide⟩ p hp j hj hq fz1_93_58 fz2_93_58
  · exact match_zero_fix ⟨94, by decide⟩ ⟨58, by decide⟩ p hp j hj hq fz1_94_58 fz2_94_58
  · exact match_zero_fix ⟨95, by decide⟩ ⟨58, by decide⟩ p hp j hj hq fz1_95_58 fz2_95_58
  · exact match_zero_fix ⟨96, by decide⟩ ⟨58, by decide⟩ p hp j hj hq fz1_96_58 fz2_96_58
  · exact match_zero_fix ⟨97, by decide⟩ ⟨58, by decide⟩ p hp j hj hq fz1_97_58 fz2_97_58
  · exact match_zero_fix ⟨98, by decide⟩ ⟨58, by decide⟩ p hp j hj hq fz1_98_58 fz2_98_58
  · exact match_zero_fix ⟨99, by decide⟩ ⟨58, by decide⟩ p hp j hj hq fz1_99_58 fz2_99_58
  · exact match_zero_fix ⟨100, by decide⟩ ⟨58, by decide⟩ p hp j hj hq fz1_100_58 fz2_100_58
  · exact match_zero_fix ⟨101, by decide⟩ ⟨58, by decide⟩ p hp j hj hq fz1_101_58 fz2_101_58
  · exact match_zero_fix ⟨102, by decide⟩ ⟨58, by decide⟩ p hp j hj hq fz1_102_58 fz2_102_58
  · exact match_zero_fix ⟨103, by decide⟩ ⟨58, by decide⟩ p hp j hj hq fz1_103_58 fz2_103_58
  · exact match_zero_fix ⟨104, by decide⟩ ⟨58, by decide⟩ p hp j hj hq fz1_104_58 fz2_104_58
  · exact match_zero_fix ⟨105, by decide⟩ ⟨58, by decide⟩ p hp j hj hq fz1_105_58 fz2_105_58
  · exact match_zero_fix ⟨106, by decide⟩ ⟨58, by decide⟩ p hp j hj hq fz1_106_58 fz2_106_58
  · exact match_zero_fix ⟨107, by decide⟩ ⟨58, by decide⟩ p hp j hj hq fz1_107_58 fz2_107_58
  · exact match_zero_fix ⟨108, by decide⟩ ⟨58, by decide⟩ p hp j hj hq fz1_108_58 fz2_108_58
  · exact match_zero_fix ⟨109, by decide⟩ ⟨58, by decide⟩ p hp j hj hq fz1_109_58 fz2_109_58
  · exact match_zero_fix ⟨110, by decide⟩ ⟨58, by decide⟩ p hp j hj hq fz1_110_58 fz2_110_58
  · exact match_zero_fix ⟨111, by decide⟩ ⟨58, by decide⟩ p hp j hj hq fz1_111_58 fz2_111_58
  · exact match_zero_fix ⟨112, by decide⟩ ⟨58, by decide⟩ p hp j hj hq fz1_112_58 fz2_112_58
  · exact match_zero_fix ⟨113, by decide⟩ ⟨58, by decide⟩ p hp j hj hq fz1_113_58 fz2_113_58
  · exact match_zero_fix ⟨114, by decide⟩ ⟨58, by decide⟩ p hp j hj hq fz1_114_58 fz2_114_58
  · exact match_zero_fix ⟨115, by decide⟩ ⟨58, by decide⟩ p hp j hj hq fz1_115_58 fz2_115_58
  · exact pair_116_58 p hp hrep j hj hq
  · exact match_zero_fix ⟨117, by decide⟩ ⟨58, by decide⟩ p hp j hj hq fz1_117_58 fz2_117_58
  · exact match_zero_fix ⟨118, by decide⟩ ⟨58, by decide⟩ p hp j hj hq fz1_118_58 fz2_118_58
  · exact match_zero_fix ⟨119, by decide⟩ ⟨58, by decide⟩ p hp j hj hq fz1_119_58 fz2_119_58
  · exact match_zero_fix ⟨120, by decide⟩ ⟨58, by decide⟩ p hp j hj hq fz1_120_58 fz2_120_58
  · exact match_zero_fix ⟨121, by decide⟩ ⟨58, by decide⟩ p hp j hj hq fz1_121_58 fz2_121_58
  · exact match_zero_fix ⟨122, by decide⟩ ⟨58, by decide⟩ p hp j hj hq fz1_122_58 fz2_122_58
  · exact match_zero_fix ⟨123, by decide⟩ ⟨58, by decide⟩ p hp j hj hq fz1_123_58 fz2_123_58
  · exact match_zero_fix ⟨124, by decide⟩ ⟨58, by decide⟩ p hp j hj hq fz1_124_58 fz2_124_58
  · exact match_zero_fix ⟨125, by decide⟩ ⟨58, by decide⟩ p hp j hj hq fz1_125_58 fz2_125_58
  · exact match_zero_fix ⟨126, by decide⟩ ⟨58, by decide⟩ p hp j hj hq fz1_126_58 fz2_126_58
  · exact match_zero_fix ⟨127, by decide⟩ ⟨58, by decide⟩ p hp j hj hq fz1_127_58 fz2_127_58
  · exact match_zero_fix ⟨128, by decide⟩ ⟨58, by decide⟩ p hp j hj hq fz1_128_58 fz2_128_58
  · exact match_zero_fix ⟨129, by decide⟩ ⟨58, by decide⟩ p hp j hj hq fz1_129_58 fz2_129_58
  · exact match_zero_fix ⟨130, by decide⟩ ⟨58, by decide⟩ p hp j hj hq fz1_130_58 fz2_130_58
  · exact match_zero_fix ⟨131, by decide⟩ ⟨58, by decide⟩ p hp j hj hq fz1_131_58 fz2_131_58
  · exact match_zero_fix ⟨132, by decide⟩ ⟨58, by decide⟩ p hp j hj hq fz1_132_58 fz2_132_58
  · exact match_zero_fix ⟨133, by decide⟩ ⟨58, by decide⟩ p hp j hj hq fz1_133_58 fz2_133_58
  · exact match_zero_fix ⟨134, by decide⟩ ⟨58, by decide⟩ p hp j hj hq fz1_134_58 fz2_134_58
  · exact match_zero_fix ⟨135, by decide⟩ ⟨58, by decide⟩ p hp j hj hq fz1_135_58 fz2_135_58
  · exact match_zero_fix ⟨136, by decide⟩ ⟨58, by decide⟩ p hp j hj hq fz1_136_58 fz2_136_58
  · exact match_zero_fix ⟨137, by decide⟩ ⟨58, by decide⟩ p hp j hj hq fz1_137_58 fz2_137_58
  · exact match_zero_fix ⟨138, by decide⟩ ⟨58, by decide⟩ p hp j hj hq fz1_138_58 fz2_138_58
  · exact match_zero_fix ⟨139, by decide⟩ ⟨58, by decide⟩ p hp j hj hq fz1_139_58 fz2_139_58
  · exact match_zero_fix ⟨140, by decide⟩ ⟨58, by decide⟩ p hp j hj hq fz1_140_58 fz2_140_58
  · exact match_zero_fix ⟨141, by decide⟩ ⟨58, by decide⟩ p hp j hj hq fz1_141_58 fz2_141_58
  · exact match_zero_fix ⟨142, by decide⟩ ⟨58, by decide⟩ p hp j hj hq fz1_142_58 fz2_142_58
  · exact match_zero_fix ⟨143, by decide⟩ ⟨58, by decide⟩ p hp j hj hq fz1_143_58 fz2_143_58
  · exact match_zero_fix ⟨144, by decide⟩ ⟨58, by decide⟩ p hp j hj hq fz1_144_58 fz2_144_58
  · exact match_zero_fix ⟨145, by decide⟩ ⟨58, by decide⟩ p hp j hj hq fz1_145_58 fz2_145_58
  · exact match_zero_fix ⟨146, by decide⟩ ⟨58, by decide⟩ p hp j hj hq fz1_146_58 fz2_146_58
  · exact pair_147_58 p hp hrep j hj hq

theorem master_59 (p : Nat) (hp : p < (Q2.transData.getD 59 []).length)
    (hrep : (Q2.cosetIsRep.getD 59 []).getD p false = true)
    (rK : Fin 148) (j : Nat) (hj : j < (repChars.getD rK.val []).length)
    (hq : (normIsRep.getD rK.val []).getD j false = true) :
    species (Q2.reps (⟨59, by decide⟩ : Fin 148)) (colE2 ⟨59, by decide⟩ p hp)
        (rowE2 rK j hj hq)
      = species (reps (⟨59, by decide⟩ : Fin 148))
        (colE1 ⟨59, by decide⟩ p (transLenTr ⟨59, by decide⟩ p hp)) (rowE1 rK j hj) := by
  rcases rK with ⟨nK, hnK⟩; interval_cases nK
  · exact match_zero_len ⟨0, by decide⟩ ⟨59, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨1, by decide⟩ ⟨59, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨2, by decide⟩ ⟨59, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨3, by decide⟩ ⟨59, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨4, by decide⟩ ⟨59, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨5, by decide⟩ ⟨59, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨6, by decide⟩ ⟨59, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨7, by decide⟩ ⟨59, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨8, by decide⟩ ⟨59, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨9, by decide⟩ ⟨59, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨10, by decide⟩ ⟨59, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨11, by decide⟩ ⟨59, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨12, by decide⟩ ⟨59, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨13, by decide⟩ ⟨59, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨14, by decide⟩ ⟨59, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨15, by decide⟩ ⟨59, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨16, by decide⟩ ⟨59, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨17, by decide⟩ ⟨59, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨18, by decide⟩ ⟨59, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨19, by decide⟩ ⟨59, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨20, by decide⟩ ⟨59, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨21, by decide⟩ ⟨59, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨22, by decide⟩ ⟨59, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨23, by decide⟩ ⟨59, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨24, by decide⟩ ⟨59, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨25, by decide⟩ ⟨59, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨26, by decide⟩ ⟨59, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨27, by decide⟩ ⟨59, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨28, by decide⟩ ⟨59, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨29, by decide⟩ ⟨59, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨30, by decide⟩ ⟨59, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨31, by decide⟩ ⟨59, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨32, by decide⟩ ⟨59, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨33, by decide⟩ ⟨59, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨34, by decide⟩ ⟨59, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨35, by decide⟩ ⟨59, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨36, by decide⟩ ⟨59, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨37, by decide⟩ ⟨59, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨38, by decide⟩ ⟨59, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨39, by decide⟩ ⟨59, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨40, by decide⟩ ⟨59, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨41, by decide⟩ ⟨59, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨42, by decide⟩ ⟨59, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨43, by decide⟩ ⟨59, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨44, by decide⟩ ⟨59, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨45, by decide⟩ ⟨59, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨46, by decide⟩ ⟨59, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨47, by decide⟩ ⟨59, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨48, by decide⟩ ⟨59, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨49, by decide⟩ ⟨59, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨50, by decide⟩ ⟨59, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨51, by decide⟩ ⟨59, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨52, by decide⟩ ⟨59, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨53, by decide⟩ ⟨59, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨54, by decide⟩ ⟨59, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_fix ⟨55, by decide⟩ ⟨59, by decide⟩ p hp j hj hq fz1_55_59 fz2_55_59
  · exact match_zero_fix ⟨56, by decide⟩ ⟨59, by decide⟩ p hp j hj hq fz1_56_59 fz2_56_59
  · exact match_zero_fix ⟨57, by decide⟩ ⟨59, by decide⟩ p hp j hj hq fz1_57_59 fz2_57_59
  · exact match_zero_fix ⟨58, by decide⟩ ⟨59, by decide⟩ p hp j hj hq fz1_58_59 fz2_58_59
  · exact pair_59_59 p hp hrep j hj hq
  · exact match_zero_fix ⟨60, by decide⟩ ⟨59, by decide⟩ p hp j hj hq fz1_60_59 fz2_60_59
  · exact match_zero_fix ⟨61, by decide⟩ ⟨59, by decide⟩ p hp j hj hq fz1_61_59 fz2_61_59
  · exact match_zero_fix ⟨62, by decide⟩ ⟨59, by decide⟩ p hp j hj hq fz1_62_59 fz2_62_59
  · exact match_zero_fix ⟨63, by decide⟩ ⟨59, by decide⟩ p hp j hj hq fz1_63_59 fz2_63_59
  · exact match_zero_fix ⟨64, by decide⟩ ⟨59, by decide⟩ p hp j hj hq fz1_64_59 fz2_64_59
  · exact match_zero_fix ⟨65, by decide⟩ ⟨59, by decide⟩ p hp j hj hq fz1_65_59 fz2_65_59
  · exact match_zero_fix ⟨66, by decide⟩ ⟨59, by decide⟩ p hp j hj hq fz1_66_59 fz2_66_59
  · exact match_zero_fix ⟨67, by decide⟩ ⟨59, by decide⟩ p hp j hj hq fz1_67_59 fz2_67_59
  · exact match_zero_fix ⟨68, by decide⟩ ⟨59, by decide⟩ p hp j hj hq fz1_68_59 fz2_68_59
  · exact match_zero_fix ⟨69, by decide⟩ ⟨59, by decide⟩ p hp j hj hq fz1_69_59 fz2_69_59
  · exact match_zero_fix ⟨70, by decide⟩ ⟨59, by decide⟩ p hp j hj hq fz1_70_59 fz2_70_59
  · exact match_zero_fix ⟨71, by decide⟩ ⟨59, by decide⟩ p hp j hj hq fz1_71_59 fz2_71_59
  · exact match_zero_fix ⟨72, by decide⟩ ⟨59, by decide⟩ p hp j hj hq fz1_72_59 fz2_72_59
  · exact match_zero_fix ⟨73, by decide⟩ ⟨59, by decide⟩ p hp j hj hq fz1_73_59 fz2_73_59
  · exact match_zero_fix ⟨74, by decide⟩ ⟨59, by decide⟩ p hp j hj hq fz1_74_59 fz2_74_59
  · exact match_zero_fix ⟨75, by decide⟩ ⟨59, by decide⟩ p hp j hj hq fz1_75_59 fz2_75_59
  · exact match_zero_fix ⟨76, by decide⟩ ⟨59, by decide⟩ p hp j hj hq fz1_76_59 fz2_76_59
  · exact match_zero_fix ⟨77, by decide⟩ ⟨59, by decide⟩ p hp j hj hq fz1_77_59 fz2_77_59
  · exact match_zero_fix ⟨78, by decide⟩ ⟨59, by decide⟩ p hp j hj hq fz1_78_59 fz2_78_59
  · exact match_zero_fix ⟨79, by decide⟩ ⟨59, by decide⟩ p hp j hj hq fz1_79_59 fz2_79_59
  · exact match_zero_fix ⟨80, by decide⟩ ⟨59, by decide⟩ p hp j hj hq fz1_80_59 fz2_80_59
  · exact match_zero_fix ⟨81, by decide⟩ ⟨59, by decide⟩ p hp j hj hq fz1_81_59 fz2_81_59
  · exact match_zero_fix ⟨82, by decide⟩ ⟨59, by decide⟩ p hp j hj hq fz1_82_59 fz2_82_59
  · exact match_zero_fix ⟨83, by decide⟩ ⟨59, by decide⟩ p hp j hj hq fz1_83_59 fz2_83_59
  · exact match_zero_fix ⟨84, by decide⟩ ⟨59, by decide⟩ p hp j hj hq fz1_84_59 fz2_84_59
  · exact match_zero_fix ⟨85, by decide⟩ ⟨59, by decide⟩ p hp j hj hq fz1_85_59 fz2_85_59
  · exact match_zero_fix ⟨86, by decide⟩ ⟨59, by decide⟩ p hp j hj hq fz1_86_59 fz2_86_59
  · exact match_zero_fix ⟨87, by decide⟩ ⟨59, by decide⟩ p hp j hj hq fz1_87_59 fz2_87_59
  · exact match_zero_fix ⟨88, by decide⟩ ⟨59, by decide⟩ p hp j hj hq fz1_88_59 fz2_88_59
  · exact match_zero_fix ⟨89, by decide⟩ ⟨59, by decide⟩ p hp j hj hq fz1_89_59 fz2_89_59
  · exact match_zero_fix ⟨90, by decide⟩ ⟨59, by decide⟩ p hp j hj hq fz1_90_59 fz2_90_59
  · exact match_zero_fix ⟨91, by decide⟩ ⟨59, by decide⟩ p hp j hj hq fz1_91_59 fz2_91_59
  · exact match_zero_fix ⟨92, by decide⟩ ⟨59, by decide⟩ p hp j hj hq fz1_92_59 fz2_92_59
  · exact match_zero_fix ⟨93, by decide⟩ ⟨59, by decide⟩ p hp j hj hq fz1_93_59 fz2_93_59
  · exact match_zero_fix ⟨94, by decide⟩ ⟨59, by decide⟩ p hp j hj hq fz1_94_59 fz2_94_59
  · exact match_zero_fix ⟨95, by decide⟩ ⟨59, by decide⟩ p hp j hj hq fz1_95_59 fz2_95_59
  · exact match_zero_fix ⟨96, by decide⟩ ⟨59, by decide⟩ p hp j hj hq fz1_96_59 fz2_96_59
  · exact match_zero_fix ⟨97, by decide⟩ ⟨59, by decide⟩ p hp j hj hq fz1_97_59 fz2_97_59
  · exact match_zero_fix ⟨98, by decide⟩ ⟨59, by decide⟩ p hp j hj hq fz1_98_59 fz2_98_59
  · exact match_zero_fix ⟨99, by decide⟩ ⟨59, by decide⟩ p hp j hj hq fz1_99_59 fz2_99_59
  · exact match_zero_fix ⟨100, by decide⟩ ⟨59, by decide⟩ p hp j hj hq fz1_100_59 fz2_100_59
  · exact match_zero_fix ⟨101, by decide⟩ ⟨59, by decide⟩ p hp j hj hq fz1_101_59 fz2_101_59
  · exact match_zero_fix ⟨102, by decide⟩ ⟨59, by decide⟩ p hp j hj hq fz1_102_59 fz2_102_59
  · exact match_zero_fix ⟨103, by decide⟩ ⟨59, by decide⟩ p hp j hj hq fz1_103_59 fz2_103_59
  · exact match_zero_fix ⟨104, by decide⟩ ⟨59, by decide⟩ p hp j hj hq fz1_104_59 fz2_104_59
  · exact match_zero_fix ⟨105, by decide⟩ ⟨59, by decide⟩ p hp j hj hq fz1_105_59 fz2_105_59
  · exact match_zero_fix ⟨106, by decide⟩ ⟨59, by decide⟩ p hp j hj hq fz1_106_59 fz2_106_59
  · exact match_zero_fix ⟨107, by decide⟩ ⟨59, by decide⟩ p hp j hj hq fz1_107_59 fz2_107_59
  · exact match_zero_fix ⟨108, by decide⟩ ⟨59, by decide⟩ p hp j hj hq fz1_108_59 fz2_108_59
  · exact match_zero_fix ⟨109, by decide⟩ ⟨59, by decide⟩ p hp j hj hq fz1_109_59 fz2_109_59
  · exact match_zero_fix ⟨110, by decide⟩ ⟨59, by decide⟩ p hp j hj hq fz1_110_59 fz2_110_59
  · exact match_zero_fix ⟨111, by decide⟩ ⟨59, by decide⟩ p hp j hj hq fz1_111_59 fz2_111_59
  · exact match_zero_fix ⟨112, by decide⟩ ⟨59, by decide⟩ p hp j hj hq fz1_112_59 fz2_112_59
  · exact match_zero_fix ⟨113, by decide⟩ ⟨59, by decide⟩ p hp j hj hq fz1_113_59 fz2_113_59
  · exact match_zero_fix ⟨114, by decide⟩ ⟨59, by decide⟩ p hp j hj hq fz1_114_59 fz2_114_59
  · exact match_zero_fix ⟨115, by decide⟩ ⟨59, by decide⟩ p hp j hj hq fz1_115_59 fz2_115_59
  · exact pair_116_59 p hp hrep j hj hq
  · exact match_zero_fix ⟨117, by decide⟩ ⟨59, by decide⟩ p hp j hj hq fz1_117_59 fz2_117_59
  · exact match_zero_fix ⟨118, by decide⟩ ⟨59, by decide⟩ p hp j hj hq fz1_118_59 fz2_118_59
  · exact match_zero_fix ⟨119, by decide⟩ ⟨59, by decide⟩ p hp j hj hq fz1_119_59 fz2_119_59
  · exact match_zero_fix ⟨120, by decide⟩ ⟨59, by decide⟩ p hp j hj hq fz1_120_59 fz2_120_59
  · exact match_zero_fix ⟨121, by decide⟩ ⟨59, by decide⟩ p hp j hj hq fz1_121_59 fz2_121_59
  · exact match_zero_fix ⟨122, by decide⟩ ⟨59, by decide⟩ p hp j hj hq fz1_122_59 fz2_122_59
  · exact match_zero_fix ⟨123, by decide⟩ ⟨59, by decide⟩ p hp j hj hq fz1_123_59 fz2_123_59
  · exact match_zero_fix ⟨124, by decide⟩ ⟨59, by decide⟩ p hp j hj hq fz1_124_59 fz2_124_59
  · exact match_zero_fix ⟨125, by decide⟩ ⟨59, by decide⟩ p hp j hj hq fz1_125_59 fz2_125_59
  · exact match_zero_fix ⟨126, by decide⟩ ⟨59, by decide⟩ p hp j hj hq fz1_126_59 fz2_126_59
  · exact match_zero_fix ⟨127, by decide⟩ ⟨59, by decide⟩ p hp j hj hq fz1_127_59 fz2_127_59
  · exact match_zero_fix ⟨128, by decide⟩ ⟨59, by decide⟩ p hp j hj hq fz1_128_59 fz2_128_59
  · exact match_zero_fix ⟨129, by decide⟩ ⟨59, by decide⟩ p hp j hj hq fz1_129_59 fz2_129_59
  · exact match_zero_fix ⟨130, by decide⟩ ⟨59, by decide⟩ p hp j hj hq fz1_130_59 fz2_130_59
  · exact match_zero_fix ⟨131, by decide⟩ ⟨59, by decide⟩ p hp j hj hq fz1_131_59 fz2_131_59
  · exact match_zero_fix ⟨132, by decide⟩ ⟨59, by decide⟩ p hp j hj hq fz1_132_59 fz2_132_59
  · exact match_zero_fix ⟨133, by decide⟩ ⟨59, by decide⟩ p hp j hj hq fz1_133_59 fz2_133_59
  · exact match_zero_fix ⟨134, by decide⟩ ⟨59, by decide⟩ p hp j hj hq fz1_134_59 fz2_134_59
  · exact match_zero_fix ⟨135, by decide⟩ ⟨59, by decide⟩ p hp j hj hq fz1_135_59 fz2_135_59
  · exact match_zero_fix ⟨136, by decide⟩ ⟨59, by decide⟩ p hp j hj hq fz1_136_59 fz2_136_59
  · exact match_zero_fix ⟨137, by decide⟩ ⟨59, by decide⟩ p hp j hj hq fz1_137_59 fz2_137_59
  · exact match_zero_fix ⟨138, by decide⟩ ⟨59, by decide⟩ p hp j hj hq fz1_138_59 fz2_138_59
  · exact match_zero_fix ⟨139, by decide⟩ ⟨59, by decide⟩ p hp j hj hq fz1_139_59 fz2_139_59
  · exact match_zero_fix ⟨140, by decide⟩ ⟨59, by decide⟩ p hp j hj hq fz1_140_59 fz2_140_59
  · exact match_zero_fix ⟨141, by decide⟩ ⟨59, by decide⟩ p hp j hj hq fz1_141_59 fz2_141_59
  · exact match_zero_fix ⟨142, by decide⟩ ⟨59, by decide⟩ p hp j hj hq fz1_142_59 fz2_142_59
  · exact match_zero_fix ⟨143, by decide⟩ ⟨59, by decide⟩ p hp j hj hq fz1_143_59 fz2_143_59
  · exact match_zero_fix ⟨144, by decide⟩ ⟨59, by decide⟩ p hp j hj hq fz1_144_59 fz2_144_59
  · exact match_zero_fix ⟨145, by decide⟩ ⟨59, by decide⟩ p hp j hj hq fz1_145_59 fz2_145_59
  · exact match_zero_fix ⟨146, by decide⟩ ⟨59, by decide⟩ p hp j hj hq fz1_146_59 fz2_146_59
  · exact pair_147_59 p hp hrep j hj hq

theorem master_60 (p : Nat) (hp : p < (Q2.transData.getD 60 []).length)
    (hrep : (Q2.cosetIsRep.getD 60 []).getD p false = true)
    (rK : Fin 148) (j : Nat) (hj : j < (repChars.getD rK.val []).length)
    (hq : (normIsRep.getD rK.val []).getD j false = true) :
    species (Q2.reps (⟨60, by decide⟩ : Fin 148)) (colE2 ⟨60, by decide⟩ p hp)
        (rowE2 rK j hj hq)
      = species (reps (⟨60, by decide⟩ : Fin 148))
        (colE1 ⟨60, by decide⟩ p (transLenTr ⟨60, by decide⟩ p hp)) (rowE1 rK j hj) := by
  rcases rK with ⟨nK, hnK⟩; interval_cases nK
  · exact match_zero_len ⟨0, by decide⟩ ⟨60, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨1, by decide⟩ ⟨60, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨2, by decide⟩ ⟨60, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨3, by decide⟩ ⟨60, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨4, by decide⟩ ⟨60, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨5, by decide⟩ ⟨60, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨6, by decide⟩ ⟨60, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨7, by decide⟩ ⟨60, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨8, by decide⟩ ⟨60, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨9, by decide⟩ ⟨60, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨10, by decide⟩ ⟨60, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨11, by decide⟩ ⟨60, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨12, by decide⟩ ⟨60, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨13, by decide⟩ ⟨60, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨14, by decide⟩ ⟨60, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨15, by decide⟩ ⟨60, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨16, by decide⟩ ⟨60, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨17, by decide⟩ ⟨60, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨18, by decide⟩ ⟨60, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨19, by decide⟩ ⟨60, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨20, by decide⟩ ⟨60, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨21, by decide⟩ ⟨60, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨22, by decide⟩ ⟨60, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨23, by decide⟩ ⟨60, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨24, by decide⟩ ⟨60, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨25, by decide⟩ ⟨60, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨26, by decide⟩ ⟨60, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨27, by decide⟩ ⟨60, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨28, by decide⟩ ⟨60, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨29, by decide⟩ ⟨60, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨30, by decide⟩ ⟨60, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨31, by decide⟩ ⟨60, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨32, by decide⟩ ⟨60, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨33, by decide⟩ ⟨60, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨34, by decide⟩ ⟨60, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨35, by decide⟩ ⟨60, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨36, by decide⟩ ⟨60, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨37, by decide⟩ ⟨60, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨38, by decide⟩ ⟨60, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨39, by decide⟩ ⟨60, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨40, by decide⟩ ⟨60, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨41, by decide⟩ ⟨60, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨42, by decide⟩ ⟨60, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨43, by decide⟩ ⟨60, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨44, by decide⟩ ⟨60, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨45, by decide⟩ ⟨60, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨46, by decide⟩ ⟨60, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨47, by decide⟩ ⟨60, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨48, by decide⟩ ⟨60, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨49, by decide⟩ ⟨60, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨50, by decide⟩ ⟨60, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨51, by decide⟩ ⟨60, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨52, by decide⟩ ⟨60, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨53, by decide⟩ ⟨60, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨54, by decide⟩ ⟨60, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_fix ⟨55, by decide⟩ ⟨60, by decide⟩ p hp j hj hq fz1_55_60 fz2_55_60
  · exact match_zero_fix ⟨56, by decide⟩ ⟨60, by decide⟩ p hp j hj hq fz1_56_60 fz2_56_60
  · exact match_zero_fix ⟨57, by decide⟩ ⟨60, by decide⟩ p hp j hj hq fz1_57_60 fz2_57_60
  · exact match_zero_fix ⟨58, by decide⟩ ⟨60, by decide⟩ p hp j hj hq fz1_58_60 fz2_58_60
  · exact match_zero_fix ⟨59, by decide⟩ ⟨60, by decide⟩ p hp j hj hq fz1_59_60 fz2_59_60
  · exact pair_60_60 p hp hrep j hj hq
  · exact match_zero_fix ⟨61, by decide⟩ ⟨60, by decide⟩ p hp j hj hq fz1_61_60 fz2_61_60
  · exact match_zero_fix ⟨62, by decide⟩ ⟨60, by decide⟩ p hp j hj hq fz1_62_60 fz2_62_60
  · exact match_zero_fix ⟨63, by decide⟩ ⟨60, by decide⟩ p hp j hj hq fz1_63_60 fz2_63_60
  · exact match_zero_fix ⟨64, by decide⟩ ⟨60, by decide⟩ p hp j hj hq fz1_64_60 fz2_64_60
  · exact match_zero_fix ⟨65, by decide⟩ ⟨60, by decide⟩ p hp j hj hq fz1_65_60 fz2_65_60
  · exact match_zero_fix ⟨66, by decide⟩ ⟨60, by decide⟩ p hp j hj hq fz1_66_60 fz2_66_60
  · exact match_zero_fix ⟨67, by decide⟩ ⟨60, by decide⟩ p hp j hj hq fz1_67_60 fz2_67_60
  · exact match_zero_fix ⟨68, by decide⟩ ⟨60, by decide⟩ p hp j hj hq fz1_68_60 fz2_68_60
  · exact match_zero_fix ⟨69, by decide⟩ ⟨60, by decide⟩ p hp j hj hq fz1_69_60 fz2_69_60
  · exact match_zero_fix ⟨70, by decide⟩ ⟨60, by decide⟩ p hp j hj hq fz1_70_60 fz2_70_60
  · exact match_zero_fix ⟨71, by decide⟩ ⟨60, by decide⟩ p hp j hj hq fz1_71_60 fz2_71_60
  · exact match_zero_fix ⟨72, by decide⟩ ⟨60, by decide⟩ p hp j hj hq fz1_72_60 fz2_72_60
  · exact match_zero_fix ⟨73, by decide⟩ ⟨60, by decide⟩ p hp j hj hq fz1_73_60 fz2_73_60
  · exact match_zero_fix ⟨74, by decide⟩ ⟨60, by decide⟩ p hp j hj hq fz1_74_60 fz2_74_60
  · exact match_zero_fix ⟨75, by decide⟩ ⟨60, by decide⟩ p hp j hj hq fz1_75_60 fz2_75_60
  · exact match_zero_fix ⟨76, by decide⟩ ⟨60, by decide⟩ p hp j hj hq fz1_76_60 fz2_76_60
  · exact match_zero_fix ⟨77, by decide⟩ ⟨60, by decide⟩ p hp j hj hq fz1_77_60 fz2_77_60
  · exact match_zero_fix ⟨78, by decide⟩ ⟨60, by decide⟩ p hp j hj hq fz1_78_60 fz2_78_60
  · exact match_zero_fix ⟨79, by decide⟩ ⟨60, by decide⟩ p hp j hj hq fz1_79_60 fz2_79_60
  · exact match_zero_fix ⟨80, by decide⟩ ⟨60, by decide⟩ p hp j hj hq fz1_80_60 fz2_80_60
  · exact match_zero_fix ⟨81, by decide⟩ ⟨60, by decide⟩ p hp j hj hq fz1_81_60 fz2_81_60
  · exact match_zero_fix ⟨82, by decide⟩ ⟨60, by decide⟩ p hp j hj hq fz1_82_60 fz2_82_60
  · exact match_zero_fix ⟨83, by decide⟩ ⟨60, by decide⟩ p hp j hj hq fz1_83_60 fz2_83_60
  · exact match_zero_fix ⟨84, by decide⟩ ⟨60, by decide⟩ p hp j hj hq fz1_84_60 fz2_84_60
  · exact match_zero_fix ⟨85, by decide⟩ ⟨60, by decide⟩ p hp j hj hq fz1_85_60 fz2_85_60
  · exact match_zero_fix ⟨86, by decide⟩ ⟨60, by decide⟩ p hp j hj hq fz1_86_60 fz2_86_60
  · exact match_zero_fix ⟨87, by decide⟩ ⟨60, by decide⟩ p hp j hj hq fz1_87_60 fz2_87_60
  · exact match_zero_fix ⟨88, by decide⟩ ⟨60, by decide⟩ p hp j hj hq fz1_88_60 fz2_88_60
  · exact match_zero_fix ⟨89, by decide⟩ ⟨60, by decide⟩ p hp j hj hq fz1_89_60 fz2_89_60
  · exact match_zero_fix ⟨90, by decide⟩ ⟨60, by decide⟩ p hp j hj hq fz1_90_60 fz2_90_60
  · exact match_zero_fix ⟨91, by decide⟩ ⟨60, by decide⟩ p hp j hj hq fz1_91_60 fz2_91_60
  · exact match_zero_fix ⟨92, by decide⟩ ⟨60, by decide⟩ p hp j hj hq fz1_92_60 fz2_92_60
  · exact match_zero_fix ⟨93, by decide⟩ ⟨60, by decide⟩ p hp j hj hq fz1_93_60 fz2_93_60
  · exact match_zero_fix ⟨94, by decide⟩ ⟨60, by decide⟩ p hp j hj hq fz1_94_60 fz2_94_60
  · exact match_zero_fix ⟨95, by decide⟩ ⟨60, by decide⟩ p hp j hj hq fz1_95_60 fz2_95_60
  · exact match_zero_fix ⟨96, by decide⟩ ⟨60, by decide⟩ p hp j hj hq fz1_96_60 fz2_96_60
  · exact match_zero_fix ⟨97, by decide⟩ ⟨60, by decide⟩ p hp j hj hq fz1_97_60 fz2_97_60
  · exact match_zero_fix ⟨98, by decide⟩ ⟨60, by decide⟩ p hp j hj hq fz1_98_60 fz2_98_60
  · exact match_zero_fix ⟨99, by decide⟩ ⟨60, by decide⟩ p hp j hj hq fz1_99_60 fz2_99_60
  · exact match_zero_fix ⟨100, by decide⟩ ⟨60, by decide⟩ p hp j hj hq fz1_100_60 fz2_100_60
  · exact match_zero_fix ⟨101, by decide⟩ ⟨60, by decide⟩ p hp j hj hq fz1_101_60 fz2_101_60
  · exact match_zero_fix ⟨102, by decide⟩ ⟨60, by decide⟩ p hp j hj hq fz1_102_60 fz2_102_60
  · exact match_zero_fix ⟨103, by decide⟩ ⟨60, by decide⟩ p hp j hj hq fz1_103_60 fz2_103_60
  · exact match_zero_fix ⟨104, by decide⟩ ⟨60, by decide⟩ p hp j hj hq fz1_104_60 fz2_104_60
  · exact match_zero_fix ⟨105, by decide⟩ ⟨60, by decide⟩ p hp j hj hq fz1_105_60 fz2_105_60
  · exact match_zero_fix ⟨106, by decide⟩ ⟨60, by decide⟩ p hp j hj hq fz1_106_60 fz2_106_60
  · exact match_zero_fix ⟨107, by decide⟩ ⟨60, by decide⟩ p hp j hj hq fz1_107_60 fz2_107_60
  · exact match_zero_fix ⟨108, by decide⟩ ⟨60, by decide⟩ p hp j hj hq fz1_108_60 fz2_108_60
  · exact match_zero_fix ⟨109, by decide⟩ ⟨60, by decide⟩ p hp j hj hq fz1_109_60 fz2_109_60
  · exact match_zero_fix ⟨110, by decide⟩ ⟨60, by decide⟩ p hp j hj hq fz1_110_60 fz2_110_60
  · exact match_zero_fix ⟨111, by decide⟩ ⟨60, by decide⟩ p hp j hj hq fz1_111_60 fz2_111_60
  · exact match_zero_fix ⟨112, by decide⟩ ⟨60, by decide⟩ p hp j hj hq fz1_112_60 fz2_112_60
  · exact match_zero_fix ⟨113, by decide⟩ ⟨60, by decide⟩ p hp j hj hq fz1_113_60 fz2_113_60
  · exact match_zero_fix ⟨114, by decide⟩ ⟨60, by decide⟩ p hp j hj hq fz1_114_60 fz2_114_60
  · exact match_zero_fix ⟨115, by decide⟩ ⟨60, by decide⟩ p hp j hj hq fz1_115_60 fz2_115_60
  · exact match_zero_fix ⟨116, by decide⟩ ⟨60, by decide⟩ p hp j hj hq fz1_116_60 fz2_116_60
  · exact pair_117_60 p hp hrep j hj hq
  · exact match_zero_fix ⟨118, by decide⟩ ⟨60, by decide⟩ p hp j hj hq fz1_118_60 fz2_118_60
  · exact match_zero_fix ⟨119, by decide⟩ ⟨60, by decide⟩ p hp j hj hq fz1_119_60 fz2_119_60
  · exact match_zero_fix ⟨120, by decide⟩ ⟨60, by decide⟩ p hp j hj hq fz1_120_60 fz2_120_60
  · exact match_zero_fix ⟨121, by decide⟩ ⟨60, by decide⟩ p hp j hj hq fz1_121_60 fz2_121_60
  · exact match_zero_fix ⟨122, by decide⟩ ⟨60, by decide⟩ p hp j hj hq fz1_122_60 fz2_122_60
  · exact match_zero_fix ⟨123, by decide⟩ ⟨60, by decide⟩ p hp j hj hq fz1_123_60 fz2_123_60
  · exact match_zero_fix ⟨124, by decide⟩ ⟨60, by decide⟩ p hp j hj hq fz1_124_60 fz2_124_60
  · exact match_zero_fix ⟨125, by decide⟩ ⟨60, by decide⟩ p hp j hj hq fz1_125_60 fz2_125_60
  · exact match_zero_fix ⟨126, by decide⟩ ⟨60, by decide⟩ p hp j hj hq fz1_126_60 fz2_126_60
  · exact match_zero_fix ⟨127, by decide⟩ ⟨60, by decide⟩ p hp j hj hq fz1_127_60 fz2_127_60
  · exact match_zero_fix ⟨128, by decide⟩ ⟨60, by decide⟩ p hp j hj hq fz1_128_60 fz2_128_60
  · exact match_zero_fix ⟨129, by decide⟩ ⟨60, by decide⟩ p hp j hj hq fz1_129_60 fz2_129_60
  · exact match_zero_fix ⟨130, by decide⟩ ⟨60, by decide⟩ p hp j hj hq fz1_130_60 fz2_130_60
  · exact match_zero_fix ⟨131, by decide⟩ ⟨60, by decide⟩ p hp j hj hq fz1_131_60 fz2_131_60
  · exact match_zero_fix ⟨132, by decide⟩ ⟨60, by decide⟩ p hp j hj hq fz1_132_60 fz2_132_60
  · exact match_zero_fix ⟨133, by decide⟩ ⟨60, by decide⟩ p hp j hj hq fz1_133_60 fz2_133_60
  · exact match_zero_fix ⟨134, by decide⟩ ⟨60, by decide⟩ p hp j hj hq fz1_134_60 fz2_134_60
  · exact match_zero_fix ⟨135, by decide⟩ ⟨60, by decide⟩ p hp j hj hq fz1_135_60 fz2_135_60
  · exact match_zero_fix ⟨136, by decide⟩ ⟨60, by decide⟩ p hp j hj hq fz1_136_60 fz2_136_60
  · exact match_zero_fix ⟨137, by decide⟩ ⟨60, by decide⟩ p hp j hj hq fz1_137_60 fz2_137_60
  · exact match_zero_fix ⟨138, by decide⟩ ⟨60, by decide⟩ p hp j hj hq fz1_138_60 fz2_138_60
  · exact match_zero_fix ⟨139, by decide⟩ ⟨60, by decide⟩ p hp j hj hq fz1_139_60 fz2_139_60
  · exact match_zero_fix ⟨140, by decide⟩ ⟨60, by decide⟩ p hp j hj hq fz1_140_60 fz2_140_60
  · exact match_zero_fix ⟨141, by decide⟩ ⟨60, by decide⟩ p hp j hj hq fz1_141_60 fz2_141_60
  · exact match_zero_fix ⟨142, by decide⟩ ⟨60, by decide⟩ p hp j hj hq fz1_142_60 fz2_142_60
  · exact match_zero_fix ⟨143, by decide⟩ ⟨60, by decide⟩ p hp j hj hq fz1_143_60 fz2_143_60
  · exact match_zero_fix ⟨144, by decide⟩ ⟨60, by decide⟩ p hp j hj hq fz1_144_60 fz2_144_60
  · exact match_zero_fix ⟨145, by decide⟩ ⟨60, by decide⟩ p hp j hj hq fz1_145_60 fz2_145_60
  · exact match_zero_fix ⟨146, by decide⟩ ⟨60, by decide⟩ p hp j hj hq fz1_146_60 fz2_146_60
  · exact pair_147_60 p hp hrep j hj hq

theorem master_61 (p : Nat) (hp : p < (Q2.transData.getD 61 []).length)
    (hrep : (Q2.cosetIsRep.getD 61 []).getD p false = true)
    (rK : Fin 148) (j : Nat) (hj : j < (repChars.getD rK.val []).length)
    (hq : (normIsRep.getD rK.val []).getD j false = true) :
    species (Q2.reps (⟨61, by decide⟩ : Fin 148)) (colE2 ⟨61, by decide⟩ p hp)
        (rowE2 rK j hj hq)
      = species (reps (⟨61, by decide⟩ : Fin 148))
        (colE1 ⟨61, by decide⟩ p (transLenTr ⟨61, by decide⟩ p hp)) (rowE1 rK j hj) := by
  rcases rK with ⟨nK, hnK⟩; interval_cases nK
  · exact match_zero_len ⟨0, by decide⟩ ⟨61, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨1, by decide⟩ ⟨61, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨2, by decide⟩ ⟨61, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨3, by decide⟩ ⟨61, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨4, by decide⟩ ⟨61, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨5, by decide⟩ ⟨61, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨6, by decide⟩ ⟨61, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨7, by decide⟩ ⟨61, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨8, by decide⟩ ⟨61, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨9, by decide⟩ ⟨61, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨10, by decide⟩ ⟨61, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨11, by decide⟩ ⟨61, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨12, by decide⟩ ⟨61, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨13, by decide⟩ ⟨61, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨14, by decide⟩ ⟨61, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨15, by decide⟩ ⟨61, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨16, by decide⟩ ⟨61, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨17, by decide⟩ ⟨61, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨18, by decide⟩ ⟨61, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨19, by decide⟩ ⟨61, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨20, by decide⟩ ⟨61, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨21, by decide⟩ ⟨61, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨22, by decide⟩ ⟨61, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨23, by decide⟩ ⟨61, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨24, by decide⟩ ⟨61, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨25, by decide⟩ ⟨61, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨26, by decide⟩ ⟨61, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨27, by decide⟩ ⟨61, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨28, by decide⟩ ⟨61, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨29, by decide⟩ ⟨61, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨30, by decide⟩ ⟨61, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨31, by decide⟩ ⟨61, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨32, by decide⟩ ⟨61, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨33, by decide⟩ ⟨61, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨34, by decide⟩ ⟨61, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨35, by decide⟩ ⟨61, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨36, by decide⟩ ⟨61, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨37, by decide⟩ ⟨61, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨38, by decide⟩ ⟨61, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨39, by decide⟩ ⟨61, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨40, by decide⟩ ⟨61, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨41, by decide⟩ ⟨61, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨42, by decide⟩ ⟨61, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨43, by decide⟩ ⟨61, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨44, by decide⟩ ⟨61, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨45, by decide⟩ ⟨61, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨46, by decide⟩ ⟨61, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨47, by decide⟩ ⟨61, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨48, by decide⟩ ⟨61, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨49, by decide⟩ ⟨61, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨50, by decide⟩ ⟨61, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨51, by decide⟩ ⟨61, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨52, by decide⟩ ⟨61, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨53, by decide⟩ ⟨61, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨54, by decide⟩ ⟨61, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_fix ⟨55, by decide⟩ ⟨61, by decide⟩ p hp j hj hq fz1_55_61 fz2_55_61
  · exact match_zero_fix ⟨56, by decide⟩ ⟨61, by decide⟩ p hp j hj hq fz1_56_61 fz2_56_61
  · exact match_zero_fix ⟨57, by decide⟩ ⟨61, by decide⟩ p hp j hj hq fz1_57_61 fz2_57_61
  · exact match_zero_fix ⟨58, by decide⟩ ⟨61, by decide⟩ p hp j hj hq fz1_58_61 fz2_58_61
  · exact match_zero_fix ⟨59, by decide⟩ ⟨61, by decide⟩ p hp j hj hq fz1_59_61 fz2_59_61
  · exact match_zero_fix ⟨60, by decide⟩ ⟨61, by decide⟩ p hp j hj hq fz1_60_61 fz2_60_61
  · exact pair_61_61 p hp hrep j hj hq
  · exact match_zero_fix ⟨62, by decide⟩ ⟨61, by decide⟩ p hp j hj hq fz1_62_61 fz2_62_61
  · exact match_zero_fix ⟨63, by decide⟩ ⟨61, by decide⟩ p hp j hj hq fz1_63_61 fz2_63_61
  · exact match_zero_fix ⟨64, by decide⟩ ⟨61, by decide⟩ p hp j hj hq fz1_64_61 fz2_64_61
  · exact match_zero_fix ⟨65, by decide⟩ ⟨61, by decide⟩ p hp j hj hq fz1_65_61 fz2_65_61
  · exact match_zero_fix ⟨66, by decide⟩ ⟨61, by decide⟩ p hp j hj hq fz1_66_61 fz2_66_61
  · exact match_zero_fix ⟨67, by decide⟩ ⟨61, by decide⟩ p hp j hj hq fz1_67_61 fz2_67_61
  · exact match_zero_fix ⟨68, by decide⟩ ⟨61, by decide⟩ p hp j hj hq fz1_68_61 fz2_68_61
  · exact match_zero_fix ⟨69, by decide⟩ ⟨61, by decide⟩ p hp j hj hq fz1_69_61 fz2_69_61
  · exact match_zero_fix ⟨70, by decide⟩ ⟨61, by decide⟩ p hp j hj hq fz1_70_61 fz2_70_61
  · exact match_zero_fix ⟨71, by decide⟩ ⟨61, by decide⟩ p hp j hj hq fz1_71_61 fz2_71_61
  · exact match_zero_fix ⟨72, by decide⟩ ⟨61, by decide⟩ p hp j hj hq fz1_72_61 fz2_72_61
  · exact match_zero_fix ⟨73, by decide⟩ ⟨61, by decide⟩ p hp j hj hq fz1_73_61 fz2_73_61
  · exact match_zero_fix ⟨74, by decide⟩ ⟨61, by decide⟩ p hp j hj hq fz1_74_61 fz2_74_61
  · exact match_zero_fix ⟨75, by decide⟩ ⟨61, by decide⟩ p hp j hj hq fz1_75_61 fz2_75_61
  · exact match_zero_fix ⟨76, by decide⟩ ⟨61, by decide⟩ p hp j hj hq fz1_76_61 fz2_76_61
  · exact match_zero_fix ⟨77, by decide⟩ ⟨61, by decide⟩ p hp j hj hq fz1_77_61 fz2_77_61
  · exact match_zero_fix ⟨78, by decide⟩ ⟨61, by decide⟩ p hp j hj hq fz1_78_61 fz2_78_61
  · exact match_zero_fix ⟨79, by decide⟩ ⟨61, by decide⟩ p hp j hj hq fz1_79_61 fz2_79_61
  · exact match_zero_fix ⟨80, by decide⟩ ⟨61, by decide⟩ p hp j hj hq fz1_80_61 fz2_80_61
  · exact match_zero_fix ⟨81, by decide⟩ ⟨61, by decide⟩ p hp j hj hq fz1_81_61 fz2_81_61
  · exact match_zero_fix ⟨82, by decide⟩ ⟨61, by decide⟩ p hp j hj hq fz1_82_61 fz2_82_61
  · exact match_zero_fix ⟨83, by decide⟩ ⟨61, by decide⟩ p hp j hj hq fz1_83_61 fz2_83_61
  · exact match_zero_fix ⟨84, by decide⟩ ⟨61, by decide⟩ p hp j hj hq fz1_84_61 fz2_84_61
  · exact match_zero_fix ⟨85, by decide⟩ ⟨61, by decide⟩ p hp j hj hq fz1_85_61 fz2_85_61
  · exact match_zero_fix ⟨86, by decide⟩ ⟨61, by decide⟩ p hp j hj hq fz1_86_61 fz2_86_61
  · exact match_zero_fix ⟨87, by decide⟩ ⟨61, by decide⟩ p hp j hj hq fz1_87_61 fz2_87_61
  · exact match_zero_fix ⟨88, by decide⟩ ⟨61, by decide⟩ p hp j hj hq fz1_88_61 fz2_88_61
  · exact match_zero_fix ⟨89, by decide⟩ ⟨61, by decide⟩ p hp j hj hq fz1_89_61 fz2_89_61
  · exact match_zero_fix ⟨90, by decide⟩ ⟨61, by decide⟩ p hp j hj hq fz1_90_61 fz2_90_61
  · exact match_zero_fix ⟨91, by decide⟩ ⟨61, by decide⟩ p hp j hj hq fz1_91_61 fz2_91_61
  · exact match_zero_fix ⟨92, by decide⟩ ⟨61, by decide⟩ p hp j hj hq fz1_92_61 fz2_92_61
  · exact match_zero_fix ⟨93, by decide⟩ ⟨61, by decide⟩ p hp j hj hq fz1_93_61 fz2_93_61
  · exact match_zero_fix ⟨94, by decide⟩ ⟨61, by decide⟩ p hp j hj hq fz1_94_61 fz2_94_61
  · exact match_zero_fix ⟨95, by decide⟩ ⟨61, by decide⟩ p hp j hj hq fz1_95_61 fz2_95_61
  · exact match_zero_fix ⟨96, by decide⟩ ⟨61, by decide⟩ p hp j hj hq fz1_96_61 fz2_96_61
  · exact match_zero_fix ⟨97, by decide⟩ ⟨61, by decide⟩ p hp j hj hq fz1_97_61 fz2_97_61
  · exact match_zero_fix ⟨98, by decide⟩ ⟨61, by decide⟩ p hp j hj hq fz1_98_61 fz2_98_61
  · exact match_zero_fix ⟨99, by decide⟩ ⟨61, by decide⟩ p hp j hj hq fz1_99_61 fz2_99_61
  · exact match_zero_fix ⟨100, by decide⟩ ⟨61, by decide⟩ p hp j hj hq fz1_100_61 fz2_100_61
  · exact match_zero_fix ⟨101, by decide⟩ ⟨61, by decide⟩ p hp j hj hq fz1_101_61 fz2_101_61
  · exact match_zero_fix ⟨102, by decide⟩ ⟨61, by decide⟩ p hp j hj hq fz1_102_61 fz2_102_61
  · exact match_zero_fix ⟨103, by decide⟩ ⟨61, by decide⟩ p hp j hj hq fz1_103_61 fz2_103_61
  · exact match_zero_fix ⟨104, by decide⟩ ⟨61, by decide⟩ p hp j hj hq fz1_104_61 fz2_104_61
  · exact match_zero_fix ⟨105, by decide⟩ ⟨61, by decide⟩ p hp j hj hq fz1_105_61 fz2_105_61
  · exact match_zero_fix ⟨106, by decide⟩ ⟨61, by decide⟩ p hp j hj hq fz1_106_61 fz2_106_61
  · exact match_zero_fix ⟨107, by decide⟩ ⟨61, by decide⟩ p hp j hj hq fz1_107_61 fz2_107_61
  · exact match_zero_fix ⟨108, by decide⟩ ⟨61, by decide⟩ p hp j hj hq fz1_108_61 fz2_108_61
  · exact match_zero_fix ⟨109, by decide⟩ ⟨61, by decide⟩ p hp j hj hq fz1_109_61 fz2_109_61
  · exact match_zero_fix ⟨110, by decide⟩ ⟨61, by decide⟩ p hp j hj hq fz1_110_61 fz2_110_61
  · exact match_zero_fix ⟨111, by decide⟩ ⟨61, by decide⟩ p hp j hj hq fz1_111_61 fz2_111_61
  · exact match_zero_fix ⟨112, by decide⟩ ⟨61, by decide⟩ p hp j hj hq fz1_112_61 fz2_112_61
  · exact match_zero_fix ⟨113, by decide⟩ ⟨61, by decide⟩ p hp j hj hq fz1_113_61 fz2_113_61
  · exact match_zero_fix ⟨114, by decide⟩ ⟨61, by decide⟩ p hp j hj hq fz1_114_61 fz2_114_61
  · exact match_zero_fix ⟨115, by decide⟩ ⟨61, by decide⟩ p hp j hj hq fz1_115_61 fz2_115_61
  · exact match_zero_fix ⟨116, by decide⟩ ⟨61, by decide⟩ p hp j hj hq fz1_116_61 fz2_116_61
  · exact pair_117_61 p hp hrep j hj hq
  · exact match_zero_fix ⟨118, by decide⟩ ⟨61, by decide⟩ p hp j hj hq fz1_118_61 fz2_118_61
  · exact match_zero_fix ⟨119, by decide⟩ ⟨61, by decide⟩ p hp j hj hq fz1_119_61 fz2_119_61
  · exact match_zero_fix ⟨120, by decide⟩ ⟨61, by decide⟩ p hp j hj hq fz1_120_61 fz2_120_61
  · exact match_zero_fix ⟨121, by decide⟩ ⟨61, by decide⟩ p hp j hj hq fz1_121_61 fz2_121_61
  · exact match_zero_fix ⟨122, by decide⟩ ⟨61, by decide⟩ p hp j hj hq fz1_122_61 fz2_122_61
  · exact match_zero_fix ⟨123, by decide⟩ ⟨61, by decide⟩ p hp j hj hq fz1_123_61 fz2_123_61
  · exact match_zero_fix ⟨124, by decide⟩ ⟨61, by decide⟩ p hp j hj hq fz1_124_61 fz2_124_61
  · exact match_zero_fix ⟨125, by decide⟩ ⟨61, by decide⟩ p hp j hj hq fz1_125_61 fz2_125_61
  · exact match_zero_fix ⟨126, by decide⟩ ⟨61, by decide⟩ p hp j hj hq fz1_126_61 fz2_126_61
  · exact match_zero_fix ⟨127, by decide⟩ ⟨61, by decide⟩ p hp j hj hq fz1_127_61 fz2_127_61
  · exact match_zero_fix ⟨128, by decide⟩ ⟨61, by decide⟩ p hp j hj hq fz1_128_61 fz2_128_61
  · exact match_zero_fix ⟨129, by decide⟩ ⟨61, by decide⟩ p hp j hj hq fz1_129_61 fz2_129_61
  · exact match_zero_fix ⟨130, by decide⟩ ⟨61, by decide⟩ p hp j hj hq fz1_130_61 fz2_130_61
  · exact match_zero_fix ⟨131, by decide⟩ ⟨61, by decide⟩ p hp j hj hq fz1_131_61 fz2_131_61
  · exact match_zero_fix ⟨132, by decide⟩ ⟨61, by decide⟩ p hp j hj hq fz1_132_61 fz2_132_61
  · exact match_zero_fix ⟨133, by decide⟩ ⟨61, by decide⟩ p hp j hj hq fz1_133_61 fz2_133_61
  · exact match_zero_fix ⟨134, by decide⟩ ⟨61, by decide⟩ p hp j hj hq fz1_134_61 fz2_134_61
  · exact match_zero_fix ⟨135, by decide⟩ ⟨61, by decide⟩ p hp j hj hq fz1_135_61 fz2_135_61
  · exact match_zero_fix ⟨136, by decide⟩ ⟨61, by decide⟩ p hp j hj hq fz1_136_61 fz2_136_61
  · exact match_zero_fix ⟨137, by decide⟩ ⟨61, by decide⟩ p hp j hj hq fz1_137_61 fz2_137_61
  · exact match_zero_fix ⟨138, by decide⟩ ⟨61, by decide⟩ p hp j hj hq fz1_138_61 fz2_138_61
  · exact match_zero_fix ⟨139, by decide⟩ ⟨61, by decide⟩ p hp j hj hq fz1_139_61 fz2_139_61
  · exact match_zero_fix ⟨140, by decide⟩ ⟨61, by decide⟩ p hp j hj hq fz1_140_61 fz2_140_61
  · exact match_zero_fix ⟨141, by decide⟩ ⟨61, by decide⟩ p hp j hj hq fz1_141_61 fz2_141_61
  · exact match_zero_fix ⟨142, by decide⟩ ⟨61, by decide⟩ p hp j hj hq fz1_142_61 fz2_142_61
  · exact match_zero_fix ⟨143, by decide⟩ ⟨61, by decide⟩ p hp j hj hq fz1_143_61 fz2_143_61
  · exact match_zero_fix ⟨144, by decide⟩ ⟨61, by decide⟩ p hp j hj hq fz1_144_61 fz2_144_61
  · exact match_zero_fix ⟨145, by decide⟩ ⟨61, by decide⟩ p hp j hj hq fz1_145_61 fz2_145_61
  · exact match_zero_fix ⟨146, by decide⟩ ⟨61, by decide⟩ p hp j hj hq fz1_146_61 fz2_146_61
  · exact pair_147_61 p hp hrep j hj hq

theorem master_62 (p : Nat) (hp : p < (Q2.transData.getD 62 []).length)
    (hrep : (Q2.cosetIsRep.getD 62 []).getD p false = true)
    (rK : Fin 148) (j : Nat) (hj : j < (repChars.getD rK.val []).length)
    (hq : (normIsRep.getD rK.val []).getD j false = true) :
    species (Q2.reps (⟨62, by decide⟩ : Fin 148)) (colE2 ⟨62, by decide⟩ p hp)
        (rowE2 rK j hj hq)
      = species (reps (⟨62, by decide⟩ : Fin 148))
        (colE1 ⟨62, by decide⟩ p (transLenTr ⟨62, by decide⟩ p hp)) (rowE1 rK j hj) := by
  rcases rK with ⟨nK, hnK⟩; interval_cases nK
  · exact match_zero_len ⟨0, by decide⟩ ⟨62, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨1, by decide⟩ ⟨62, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨2, by decide⟩ ⟨62, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨3, by decide⟩ ⟨62, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨4, by decide⟩ ⟨62, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨5, by decide⟩ ⟨62, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨6, by decide⟩ ⟨62, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨7, by decide⟩ ⟨62, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨8, by decide⟩ ⟨62, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨9, by decide⟩ ⟨62, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨10, by decide⟩ ⟨62, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨11, by decide⟩ ⟨62, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨12, by decide⟩ ⟨62, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨13, by decide⟩ ⟨62, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨14, by decide⟩ ⟨62, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨15, by decide⟩ ⟨62, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨16, by decide⟩ ⟨62, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨17, by decide⟩ ⟨62, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨18, by decide⟩ ⟨62, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨19, by decide⟩ ⟨62, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨20, by decide⟩ ⟨62, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨21, by decide⟩ ⟨62, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨22, by decide⟩ ⟨62, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨23, by decide⟩ ⟨62, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨24, by decide⟩ ⟨62, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨25, by decide⟩ ⟨62, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨26, by decide⟩ ⟨62, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨27, by decide⟩ ⟨62, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨28, by decide⟩ ⟨62, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨29, by decide⟩ ⟨62, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨30, by decide⟩ ⟨62, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨31, by decide⟩ ⟨62, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨32, by decide⟩ ⟨62, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨33, by decide⟩ ⟨62, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨34, by decide⟩ ⟨62, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨35, by decide⟩ ⟨62, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨36, by decide⟩ ⟨62, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨37, by decide⟩ ⟨62, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨38, by decide⟩ ⟨62, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨39, by decide⟩ ⟨62, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨40, by decide⟩ ⟨62, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨41, by decide⟩ ⟨62, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨42, by decide⟩ ⟨62, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨43, by decide⟩ ⟨62, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨44, by decide⟩ ⟨62, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨45, by decide⟩ ⟨62, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨46, by decide⟩ ⟨62, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨47, by decide⟩ ⟨62, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨48, by decide⟩ ⟨62, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨49, by decide⟩ ⟨62, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨50, by decide⟩ ⟨62, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨51, by decide⟩ ⟨62, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨52, by decide⟩ ⟨62, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨53, by decide⟩ ⟨62, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨54, by decide⟩ ⟨62, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_fix ⟨55, by decide⟩ ⟨62, by decide⟩ p hp j hj hq fz1_55_62 fz2_55_62
  · exact match_zero_fix ⟨56, by decide⟩ ⟨62, by decide⟩ p hp j hj hq fz1_56_62 fz2_56_62
  · exact match_zero_fix ⟨57, by decide⟩ ⟨62, by decide⟩ p hp j hj hq fz1_57_62 fz2_57_62
  · exact match_zero_fix ⟨58, by decide⟩ ⟨62, by decide⟩ p hp j hj hq fz1_58_62 fz2_58_62
  · exact match_zero_fix ⟨59, by decide⟩ ⟨62, by decide⟩ p hp j hj hq fz1_59_62 fz2_59_62
  · exact match_zero_fix ⟨60, by decide⟩ ⟨62, by decide⟩ p hp j hj hq fz1_60_62 fz2_60_62
  · exact match_zero_fix ⟨61, by decide⟩ ⟨62, by decide⟩ p hp j hj hq fz1_61_62 fz2_61_62
  · exact pair_62_62 p hp hrep j hj hq
  · exact match_zero_fix ⟨63, by decide⟩ ⟨62, by decide⟩ p hp j hj hq fz1_63_62 fz2_63_62
  · exact match_zero_fix ⟨64, by decide⟩ ⟨62, by decide⟩ p hp j hj hq fz1_64_62 fz2_64_62
  · exact match_zero_fix ⟨65, by decide⟩ ⟨62, by decide⟩ p hp j hj hq fz1_65_62 fz2_65_62
  · exact match_zero_fix ⟨66, by decide⟩ ⟨62, by decide⟩ p hp j hj hq fz1_66_62 fz2_66_62
  · exact match_zero_fix ⟨67, by decide⟩ ⟨62, by decide⟩ p hp j hj hq fz1_67_62 fz2_67_62
  · exact match_zero_fix ⟨68, by decide⟩ ⟨62, by decide⟩ p hp j hj hq fz1_68_62 fz2_68_62
  · exact match_zero_fix ⟨69, by decide⟩ ⟨62, by decide⟩ p hp j hj hq fz1_69_62 fz2_69_62
  · exact match_zero_fix ⟨70, by decide⟩ ⟨62, by decide⟩ p hp j hj hq fz1_70_62 fz2_70_62
  · exact match_zero_fix ⟨71, by decide⟩ ⟨62, by decide⟩ p hp j hj hq fz1_71_62 fz2_71_62
  · exact match_zero_fix ⟨72, by decide⟩ ⟨62, by decide⟩ p hp j hj hq fz1_72_62 fz2_72_62
  · exact match_zero_fix ⟨73, by decide⟩ ⟨62, by decide⟩ p hp j hj hq fz1_73_62 fz2_73_62
  · exact match_zero_fix ⟨74, by decide⟩ ⟨62, by decide⟩ p hp j hj hq fz1_74_62 fz2_74_62
  · exact match_zero_fix ⟨75, by decide⟩ ⟨62, by decide⟩ p hp j hj hq fz1_75_62 fz2_75_62
  · exact match_zero_fix ⟨76, by decide⟩ ⟨62, by decide⟩ p hp j hj hq fz1_76_62 fz2_76_62
  · exact match_zero_fix ⟨77, by decide⟩ ⟨62, by decide⟩ p hp j hj hq fz1_77_62 fz2_77_62
  · exact match_zero_fix ⟨78, by decide⟩ ⟨62, by decide⟩ p hp j hj hq fz1_78_62 fz2_78_62
  · exact match_zero_fix ⟨79, by decide⟩ ⟨62, by decide⟩ p hp j hj hq fz1_79_62 fz2_79_62
  · exact match_zero_fix ⟨80, by decide⟩ ⟨62, by decide⟩ p hp j hj hq fz1_80_62 fz2_80_62
  · exact match_zero_fix ⟨81, by decide⟩ ⟨62, by decide⟩ p hp j hj hq fz1_81_62 fz2_81_62
  · exact match_zero_fix ⟨82, by decide⟩ ⟨62, by decide⟩ p hp j hj hq fz1_82_62 fz2_82_62
  · exact match_zero_fix ⟨83, by decide⟩ ⟨62, by decide⟩ p hp j hj hq fz1_83_62 fz2_83_62
  · exact match_zero_fix ⟨84, by decide⟩ ⟨62, by decide⟩ p hp j hj hq fz1_84_62 fz2_84_62
  · exact match_zero_fix ⟨85, by decide⟩ ⟨62, by decide⟩ p hp j hj hq fz1_85_62 fz2_85_62
  · exact match_zero_fix ⟨86, by decide⟩ ⟨62, by decide⟩ p hp j hj hq fz1_86_62 fz2_86_62
  · exact match_zero_fix ⟨87, by decide⟩ ⟨62, by decide⟩ p hp j hj hq fz1_87_62 fz2_87_62
  · exact match_zero_fix ⟨88, by decide⟩ ⟨62, by decide⟩ p hp j hj hq fz1_88_62 fz2_88_62
  · exact match_zero_fix ⟨89, by decide⟩ ⟨62, by decide⟩ p hp j hj hq fz1_89_62 fz2_89_62
  · exact match_zero_fix ⟨90, by decide⟩ ⟨62, by decide⟩ p hp j hj hq fz1_90_62 fz2_90_62
  · exact match_zero_fix ⟨91, by decide⟩ ⟨62, by decide⟩ p hp j hj hq fz1_91_62 fz2_91_62
  · exact match_zero_fix ⟨92, by decide⟩ ⟨62, by decide⟩ p hp j hj hq fz1_92_62 fz2_92_62
  · exact match_zero_fix ⟨93, by decide⟩ ⟨62, by decide⟩ p hp j hj hq fz1_93_62 fz2_93_62
  · exact match_zero_fix ⟨94, by decide⟩ ⟨62, by decide⟩ p hp j hj hq fz1_94_62 fz2_94_62
  · exact match_zero_fix ⟨95, by decide⟩ ⟨62, by decide⟩ p hp j hj hq fz1_95_62 fz2_95_62
  · exact match_zero_fix ⟨96, by decide⟩ ⟨62, by decide⟩ p hp j hj hq fz1_96_62 fz2_96_62
  · exact match_zero_fix ⟨97, by decide⟩ ⟨62, by decide⟩ p hp j hj hq fz1_97_62 fz2_97_62
  · exact match_zero_fix ⟨98, by decide⟩ ⟨62, by decide⟩ p hp j hj hq fz1_98_62 fz2_98_62
  · exact match_zero_fix ⟨99, by decide⟩ ⟨62, by decide⟩ p hp j hj hq fz1_99_62 fz2_99_62
  · exact match_zero_fix ⟨100, by decide⟩ ⟨62, by decide⟩ p hp j hj hq fz1_100_62 fz2_100_62
  · exact match_zero_fix ⟨101, by decide⟩ ⟨62, by decide⟩ p hp j hj hq fz1_101_62 fz2_101_62
  · exact match_zero_fix ⟨102, by decide⟩ ⟨62, by decide⟩ p hp j hj hq fz1_102_62 fz2_102_62
  · exact match_zero_fix ⟨103, by decide⟩ ⟨62, by decide⟩ p hp j hj hq fz1_103_62 fz2_103_62
  · exact match_zero_fix ⟨104, by decide⟩ ⟨62, by decide⟩ p hp j hj hq fz1_104_62 fz2_104_62
  · exact match_zero_fix ⟨105, by decide⟩ ⟨62, by decide⟩ p hp j hj hq fz1_105_62 fz2_105_62
  · exact match_zero_fix ⟨106, by decide⟩ ⟨62, by decide⟩ p hp j hj hq fz1_106_62 fz2_106_62
  · exact match_zero_fix ⟨107, by decide⟩ ⟨62, by decide⟩ p hp j hj hq fz1_107_62 fz2_107_62
  · exact match_zero_fix ⟨108, by decide⟩ ⟨62, by decide⟩ p hp j hj hq fz1_108_62 fz2_108_62
  · exact match_zero_fix ⟨109, by decide⟩ ⟨62, by decide⟩ p hp j hj hq fz1_109_62 fz2_109_62
  · exact match_zero_fix ⟨110, by decide⟩ ⟨62, by decide⟩ p hp j hj hq fz1_110_62 fz2_110_62
  · exact match_zero_fix ⟨111, by decide⟩ ⟨62, by decide⟩ p hp j hj hq fz1_111_62 fz2_111_62
  · exact match_zero_fix ⟨112, by decide⟩ ⟨62, by decide⟩ p hp j hj hq fz1_112_62 fz2_112_62
  · exact match_zero_fix ⟨113, by decide⟩ ⟨62, by decide⟩ p hp j hj hq fz1_113_62 fz2_113_62
  · exact match_zero_fix ⟨114, by decide⟩ ⟨62, by decide⟩ p hp j hj hq fz1_114_62 fz2_114_62
  · exact match_zero_fix ⟨115, by decide⟩ ⟨62, by decide⟩ p hp j hj hq fz1_115_62 fz2_115_62
  · exact match_zero_fix ⟨116, by decide⟩ ⟨62, by decide⟩ p hp j hj hq fz1_116_62 fz2_116_62
  · exact pair_117_62 p hp hrep j hj hq
  · exact match_zero_fix ⟨118, by decide⟩ ⟨62, by decide⟩ p hp j hj hq fz1_118_62 fz2_118_62
  · exact match_zero_fix ⟨119, by decide⟩ ⟨62, by decide⟩ p hp j hj hq fz1_119_62 fz2_119_62
  · exact match_zero_fix ⟨120, by decide⟩ ⟨62, by decide⟩ p hp j hj hq fz1_120_62 fz2_120_62
  · exact match_zero_fix ⟨121, by decide⟩ ⟨62, by decide⟩ p hp j hj hq fz1_121_62 fz2_121_62
  · exact match_zero_fix ⟨122, by decide⟩ ⟨62, by decide⟩ p hp j hj hq fz1_122_62 fz2_122_62
  · exact match_zero_fix ⟨123, by decide⟩ ⟨62, by decide⟩ p hp j hj hq fz1_123_62 fz2_123_62
  · exact match_zero_fix ⟨124, by decide⟩ ⟨62, by decide⟩ p hp j hj hq fz1_124_62 fz2_124_62
  · exact match_zero_fix ⟨125, by decide⟩ ⟨62, by decide⟩ p hp j hj hq fz1_125_62 fz2_125_62
  · exact match_zero_fix ⟨126, by decide⟩ ⟨62, by decide⟩ p hp j hj hq fz1_126_62 fz2_126_62
  · exact match_zero_fix ⟨127, by decide⟩ ⟨62, by decide⟩ p hp j hj hq fz1_127_62 fz2_127_62
  · exact match_zero_fix ⟨128, by decide⟩ ⟨62, by decide⟩ p hp j hj hq fz1_128_62 fz2_128_62
  · exact match_zero_fix ⟨129, by decide⟩ ⟨62, by decide⟩ p hp j hj hq fz1_129_62 fz2_129_62
  · exact match_zero_fix ⟨130, by decide⟩ ⟨62, by decide⟩ p hp j hj hq fz1_130_62 fz2_130_62
  · exact match_zero_fix ⟨131, by decide⟩ ⟨62, by decide⟩ p hp j hj hq fz1_131_62 fz2_131_62
  · exact match_zero_fix ⟨132, by decide⟩ ⟨62, by decide⟩ p hp j hj hq fz1_132_62 fz2_132_62
  · exact match_zero_fix ⟨133, by decide⟩ ⟨62, by decide⟩ p hp j hj hq fz1_133_62 fz2_133_62
  · exact match_zero_fix ⟨134, by decide⟩ ⟨62, by decide⟩ p hp j hj hq fz1_134_62 fz2_134_62
  · exact match_zero_fix ⟨135, by decide⟩ ⟨62, by decide⟩ p hp j hj hq fz1_135_62 fz2_135_62
  · exact match_zero_fix ⟨136, by decide⟩ ⟨62, by decide⟩ p hp j hj hq fz1_136_62 fz2_136_62
  · exact match_zero_fix ⟨137, by decide⟩ ⟨62, by decide⟩ p hp j hj hq fz1_137_62 fz2_137_62
  · exact match_zero_fix ⟨138, by decide⟩ ⟨62, by decide⟩ p hp j hj hq fz1_138_62 fz2_138_62
  · exact match_zero_fix ⟨139, by decide⟩ ⟨62, by decide⟩ p hp j hj hq fz1_139_62 fz2_139_62
  · exact match_zero_fix ⟨140, by decide⟩ ⟨62, by decide⟩ p hp j hj hq fz1_140_62 fz2_140_62
  · exact match_zero_fix ⟨141, by decide⟩ ⟨62, by decide⟩ p hp j hj hq fz1_141_62 fz2_141_62
  · exact match_zero_fix ⟨142, by decide⟩ ⟨62, by decide⟩ p hp j hj hq fz1_142_62 fz2_142_62
  · exact match_zero_fix ⟨143, by decide⟩ ⟨62, by decide⟩ p hp j hj hq fz1_143_62 fz2_143_62
  · exact match_zero_fix ⟨144, by decide⟩ ⟨62, by decide⟩ p hp j hj hq fz1_144_62 fz2_144_62
  · exact match_zero_fix ⟨145, by decide⟩ ⟨62, by decide⟩ p hp j hj hq fz1_145_62 fz2_145_62
  · exact match_zero_fix ⟨146, by decide⟩ ⟨62, by decide⟩ p hp j hj hq fz1_146_62 fz2_146_62
  · exact pair_147_62 p hp hrep j hj hq

theorem master_63 (p : Nat) (hp : p < (Q2.transData.getD 63 []).length)
    (hrep : (Q2.cosetIsRep.getD 63 []).getD p false = true)
    (rK : Fin 148) (j : Nat) (hj : j < (repChars.getD rK.val []).length)
    (hq : (normIsRep.getD rK.val []).getD j false = true) :
    species (Q2.reps (⟨63, by decide⟩ : Fin 148)) (colE2 ⟨63, by decide⟩ p hp)
        (rowE2 rK j hj hq)
      = species (reps (⟨63, by decide⟩ : Fin 148))
        (colE1 ⟨63, by decide⟩ p (transLenTr ⟨63, by decide⟩ p hp)) (rowE1 rK j hj) := by
  rcases rK with ⟨nK, hnK⟩; interval_cases nK
  · exact match_zero_len ⟨0, by decide⟩ ⟨63, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨1, by decide⟩ ⟨63, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨2, by decide⟩ ⟨63, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨3, by decide⟩ ⟨63, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨4, by decide⟩ ⟨63, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨5, by decide⟩ ⟨63, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨6, by decide⟩ ⟨63, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨7, by decide⟩ ⟨63, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨8, by decide⟩ ⟨63, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨9, by decide⟩ ⟨63, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨10, by decide⟩ ⟨63, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨11, by decide⟩ ⟨63, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨12, by decide⟩ ⟨63, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨13, by decide⟩ ⟨63, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨14, by decide⟩ ⟨63, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨15, by decide⟩ ⟨63, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨16, by decide⟩ ⟨63, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨17, by decide⟩ ⟨63, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨18, by decide⟩ ⟨63, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨19, by decide⟩ ⟨63, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨20, by decide⟩ ⟨63, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨21, by decide⟩ ⟨63, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨22, by decide⟩ ⟨63, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨23, by decide⟩ ⟨63, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨24, by decide⟩ ⟨63, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨25, by decide⟩ ⟨63, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨26, by decide⟩ ⟨63, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨27, by decide⟩ ⟨63, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨28, by decide⟩ ⟨63, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨29, by decide⟩ ⟨63, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨30, by decide⟩ ⟨63, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨31, by decide⟩ ⟨63, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨32, by decide⟩ ⟨63, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨33, by decide⟩ ⟨63, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨34, by decide⟩ ⟨63, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨35, by decide⟩ ⟨63, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨36, by decide⟩ ⟨63, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨37, by decide⟩ ⟨63, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨38, by decide⟩ ⟨63, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨39, by decide⟩ ⟨63, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨40, by decide⟩ ⟨63, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨41, by decide⟩ ⟨63, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨42, by decide⟩ ⟨63, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨43, by decide⟩ ⟨63, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨44, by decide⟩ ⟨63, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨45, by decide⟩ ⟨63, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨46, by decide⟩ ⟨63, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨47, by decide⟩ ⟨63, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨48, by decide⟩ ⟨63, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨49, by decide⟩ ⟨63, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨50, by decide⟩ ⟨63, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨51, by decide⟩ ⟨63, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨52, by decide⟩ ⟨63, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨53, by decide⟩ ⟨63, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨54, by decide⟩ ⟨63, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_fix ⟨55, by decide⟩ ⟨63, by decide⟩ p hp j hj hq fz1_55_63 fz2_55_63
  · exact match_zero_fix ⟨56, by decide⟩ ⟨63, by decide⟩ p hp j hj hq fz1_56_63 fz2_56_63
  · exact match_zero_fix ⟨57, by decide⟩ ⟨63, by decide⟩ p hp j hj hq fz1_57_63 fz2_57_63
  · exact match_zero_fix ⟨58, by decide⟩ ⟨63, by decide⟩ p hp j hj hq fz1_58_63 fz2_58_63
  · exact match_zero_fix ⟨59, by decide⟩ ⟨63, by decide⟩ p hp j hj hq fz1_59_63 fz2_59_63
  · exact match_zero_fix ⟨60, by decide⟩ ⟨63, by decide⟩ p hp j hj hq fz1_60_63 fz2_60_63
  · exact match_zero_fix ⟨61, by decide⟩ ⟨63, by decide⟩ p hp j hj hq fz1_61_63 fz2_61_63
  · exact match_zero_fix ⟨62, by decide⟩ ⟨63, by decide⟩ p hp j hj hq fz1_62_63 fz2_62_63
  · exact pair_63_63 p hp hrep j hj hq
  · exact match_zero_fix ⟨64, by decide⟩ ⟨63, by decide⟩ p hp j hj hq fz1_64_63 fz2_64_63
  · exact match_zero_fix ⟨65, by decide⟩ ⟨63, by decide⟩ p hp j hj hq fz1_65_63 fz2_65_63
  · exact match_zero_fix ⟨66, by decide⟩ ⟨63, by decide⟩ p hp j hj hq fz1_66_63 fz2_66_63
  · exact match_zero_fix ⟨67, by decide⟩ ⟨63, by decide⟩ p hp j hj hq fz1_67_63 fz2_67_63
  · exact match_zero_fix ⟨68, by decide⟩ ⟨63, by decide⟩ p hp j hj hq fz1_68_63 fz2_68_63
  · exact match_zero_fix ⟨69, by decide⟩ ⟨63, by decide⟩ p hp j hj hq fz1_69_63 fz2_69_63
  · exact match_zero_fix ⟨70, by decide⟩ ⟨63, by decide⟩ p hp j hj hq fz1_70_63 fz2_70_63
  · exact match_zero_fix ⟨71, by decide⟩ ⟨63, by decide⟩ p hp j hj hq fz1_71_63 fz2_71_63
  · exact match_zero_fix ⟨72, by decide⟩ ⟨63, by decide⟩ p hp j hj hq fz1_72_63 fz2_72_63
  · exact match_zero_fix ⟨73, by decide⟩ ⟨63, by decide⟩ p hp j hj hq fz1_73_63 fz2_73_63
  · exact match_zero_fix ⟨74, by decide⟩ ⟨63, by decide⟩ p hp j hj hq fz1_74_63 fz2_74_63
  · exact match_zero_fix ⟨75, by decide⟩ ⟨63, by decide⟩ p hp j hj hq fz1_75_63 fz2_75_63
  · exact match_zero_fix ⟨76, by decide⟩ ⟨63, by decide⟩ p hp j hj hq fz1_76_63 fz2_76_63
  · exact match_zero_fix ⟨77, by decide⟩ ⟨63, by decide⟩ p hp j hj hq fz1_77_63 fz2_77_63
  · exact match_zero_fix ⟨78, by decide⟩ ⟨63, by decide⟩ p hp j hj hq fz1_78_63 fz2_78_63
  · exact match_zero_fix ⟨79, by decide⟩ ⟨63, by decide⟩ p hp j hj hq fz1_79_63 fz2_79_63
  · exact match_zero_fix ⟨80, by decide⟩ ⟨63, by decide⟩ p hp j hj hq fz1_80_63 fz2_80_63
  · exact match_zero_fix ⟨81, by decide⟩ ⟨63, by decide⟩ p hp j hj hq fz1_81_63 fz2_81_63
  · exact match_zero_fix ⟨82, by decide⟩ ⟨63, by decide⟩ p hp j hj hq fz1_82_63 fz2_82_63
  · exact match_zero_fix ⟨83, by decide⟩ ⟨63, by decide⟩ p hp j hj hq fz1_83_63 fz2_83_63
  · exact match_zero_fix ⟨84, by decide⟩ ⟨63, by decide⟩ p hp j hj hq fz1_84_63 fz2_84_63
  · exact match_zero_fix ⟨85, by decide⟩ ⟨63, by decide⟩ p hp j hj hq fz1_85_63 fz2_85_63
  · exact match_zero_fix ⟨86, by decide⟩ ⟨63, by decide⟩ p hp j hj hq fz1_86_63 fz2_86_63
  · exact match_zero_fix ⟨87, by decide⟩ ⟨63, by decide⟩ p hp j hj hq fz1_87_63 fz2_87_63
  · exact match_zero_fix ⟨88, by decide⟩ ⟨63, by decide⟩ p hp j hj hq fz1_88_63 fz2_88_63
  · exact match_zero_fix ⟨89, by decide⟩ ⟨63, by decide⟩ p hp j hj hq fz1_89_63 fz2_89_63
  · exact match_zero_fix ⟨90, by decide⟩ ⟨63, by decide⟩ p hp j hj hq fz1_90_63 fz2_90_63
  · exact match_zero_fix ⟨91, by decide⟩ ⟨63, by decide⟩ p hp j hj hq fz1_91_63 fz2_91_63
  · exact match_zero_fix ⟨92, by decide⟩ ⟨63, by decide⟩ p hp j hj hq fz1_92_63 fz2_92_63
  · exact match_zero_fix ⟨93, by decide⟩ ⟨63, by decide⟩ p hp j hj hq fz1_93_63 fz2_93_63
  · exact match_zero_fix ⟨94, by decide⟩ ⟨63, by decide⟩ p hp j hj hq fz1_94_63 fz2_94_63
  · exact match_zero_fix ⟨95, by decide⟩ ⟨63, by decide⟩ p hp j hj hq fz1_95_63 fz2_95_63
  · exact match_zero_fix ⟨96, by decide⟩ ⟨63, by decide⟩ p hp j hj hq fz1_96_63 fz2_96_63
  · exact match_zero_fix ⟨97, by decide⟩ ⟨63, by decide⟩ p hp j hj hq fz1_97_63 fz2_97_63
  · exact match_zero_fix ⟨98, by decide⟩ ⟨63, by decide⟩ p hp j hj hq fz1_98_63 fz2_98_63
  · exact match_zero_fix ⟨99, by decide⟩ ⟨63, by decide⟩ p hp j hj hq fz1_99_63 fz2_99_63
  · exact match_zero_fix ⟨100, by decide⟩ ⟨63, by decide⟩ p hp j hj hq fz1_100_63 fz2_100_63
  · exact match_zero_fix ⟨101, by decide⟩ ⟨63, by decide⟩ p hp j hj hq fz1_101_63 fz2_101_63
  · exact match_zero_fix ⟨102, by decide⟩ ⟨63, by decide⟩ p hp j hj hq fz1_102_63 fz2_102_63
  · exact match_zero_fix ⟨103, by decide⟩ ⟨63, by decide⟩ p hp j hj hq fz1_103_63 fz2_103_63
  · exact match_zero_fix ⟨104, by decide⟩ ⟨63, by decide⟩ p hp j hj hq fz1_104_63 fz2_104_63
  · exact match_zero_fix ⟨105, by decide⟩ ⟨63, by decide⟩ p hp j hj hq fz1_105_63 fz2_105_63
  · exact match_zero_fix ⟨106, by decide⟩ ⟨63, by decide⟩ p hp j hj hq fz1_106_63 fz2_106_63
  · exact match_zero_fix ⟨107, by decide⟩ ⟨63, by decide⟩ p hp j hj hq fz1_107_63 fz2_107_63
  · exact match_zero_fix ⟨108, by decide⟩ ⟨63, by decide⟩ p hp j hj hq fz1_108_63 fz2_108_63
  · exact match_zero_fix ⟨109, by decide⟩ ⟨63, by decide⟩ p hp j hj hq fz1_109_63 fz2_109_63
  · exact match_zero_fix ⟨110, by decide⟩ ⟨63, by decide⟩ p hp j hj hq fz1_110_63 fz2_110_63
  · exact match_zero_fix ⟨111, by decide⟩ ⟨63, by decide⟩ p hp j hj hq fz1_111_63 fz2_111_63
  · exact match_zero_fix ⟨112, by decide⟩ ⟨63, by decide⟩ p hp j hj hq fz1_112_63 fz2_112_63
  · exact match_zero_fix ⟨113, by decide⟩ ⟨63, by decide⟩ p hp j hj hq fz1_113_63 fz2_113_63
  · exact match_zero_fix ⟨114, by decide⟩ ⟨63, by decide⟩ p hp j hj hq fz1_114_63 fz2_114_63
  · exact match_zero_fix ⟨115, by decide⟩ ⟨63, by decide⟩ p hp j hj hq fz1_115_63 fz2_115_63
  · exact match_zero_fix ⟨116, by decide⟩ ⟨63, by decide⟩ p hp j hj hq fz1_116_63 fz2_116_63
  · exact pair_117_63 p hp hrep j hj hq
  · exact match_zero_fix ⟨118, by decide⟩ ⟨63, by decide⟩ p hp j hj hq fz1_118_63 fz2_118_63
  · exact match_zero_fix ⟨119, by decide⟩ ⟨63, by decide⟩ p hp j hj hq fz1_119_63 fz2_119_63
  · exact match_zero_fix ⟨120, by decide⟩ ⟨63, by decide⟩ p hp j hj hq fz1_120_63 fz2_120_63
  · exact match_zero_fix ⟨121, by decide⟩ ⟨63, by decide⟩ p hp j hj hq fz1_121_63 fz2_121_63
  · exact match_zero_fix ⟨122, by decide⟩ ⟨63, by decide⟩ p hp j hj hq fz1_122_63 fz2_122_63
  · exact match_zero_fix ⟨123, by decide⟩ ⟨63, by decide⟩ p hp j hj hq fz1_123_63 fz2_123_63
  · exact match_zero_fix ⟨124, by decide⟩ ⟨63, by decide⟩ p hp j hj hq fz1_124_63 fz2_124_63
  · exact match_zero_fix ⟨125, by decide⟩ ⟨63, by decide⟩ p hp j hj hq fz1_125_63 fz2_125_63
  · exact match_zero_fix ⟨126, by decide⟩ ⟨63, by decide⟩ p hp j hj hq fz1_126_63 fz2_126_63
  · exact match_zero_fix ⟨127, by decide⟩ ⟨63, by decide⟩ p hp j hj hq fz1_127_63 fz2_127_63
  · exact match_zero_fix ⟨128, by decide⟩ ⟨63, by decide⟩ p hp j hj hq fz1_128_63 fz2_128_63
  · exact match_zero_fix ⟨129, by decide⟩ ⟨63, by decide⟩ p hp j hj hq fz1_129_63 fz2_129_63
  · exact match_zero_fix ⟨130, by decide⟩ ⟨63, by decide⟩ p hp j hj hq fz1_130_63 fz2_130_63
  · exact match_zero_fix ⟨131, by decide⟩ ⟨63, by decide⟩ p hp j hj hq fz1_131_63 fz2_131_63
  · exact match_zero_fix ⟨132, by decide⟩ ⟨63, by decide⟩ p hp j hj hq fz1_132_63 fz2_132_63
  · exact match_zero_fix ⟨133, by decide⟩ ⟨63, by decide⟩ p hp j hj hq fz1_133_63 fz2_133_63
  · exact match_zero_fix ⟨134, by decide⟩ ⟨63, by decide⟩ p hp j hj hq fz1_134_63 fz2_134_63
  · exact match_zero_fix ⟨135, by decide⟩ ⟨63, by decide⟩ p hp j hj hq fz1_135_63 fz2_135_63
  · exact match_zero_fix ⟨136, by decide⟩ ⟨63, by decide⟩ p hp j hj hq fz1_136_63 fz2_136_63
  · exact match_zero_fix ⟨137, by decide⟩ ⟨63, by decide⟩ p hp j hj hq fz1_137_63 fz2_137_63
  · exact match_zero_fix ⟨138, by decide⟩ ⟨63, by decide⟩ p hp j hj hq fz1_138_63 fz2_138_63
  · exact match_zero_fix ⟨139, by decide⟩ ⟨63, by decide⟩ p hp j hj hq fz1_139_63 fz2_139_63
  · exact match_zero_fix ⟨140, by decide⟩ ⟨63, by decide⟩ p hp j hj hq fz1_140_63 fz2_140_63
  · exact match_zero_fix ⟨141, by decide⟩ ⟨63, by decide⟩ p hp j hj hq fz1_141_63 fz2_141_63
  · exact match_zero_fix ⟨142, by decide⟩ ⟨63, by decide⟩ p hp j hj hq fz1_142_63 fz2_142_63
  · exact match_zero_fix ⟨143, by decide⟩ ⟨63, by decide⟩ p hp j hj hq fz1_143_63 fz2_143_63
  · exact match_zero_fix ⟨144, by decide⟩ ⟨63, by decide⟩ p hp j hj hq fz1_144_63 fz2_144_63
  · exact match_zero_fix ⟨145, by decide⟩ ⟨63, by decide⟩ p hp j hj hq fz1_145_63 fz2_145_63
  · exact match_zero_fix ⟨146, by decide⟩ ⟨63, by decide⟩ p hp j hj hq fz1_146_63 fz2_146_63
  · exact pair_147_63 p hp hrep j hj hq

end LeanDring.P5Presentation
