/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Data.FixZero.C013
import LeanDring.P5.Data.FixZero.C014
import LeanDring.P5.Data.FixZero.C015
import LeanDring.P5.Data.FixZero.C016
import LeanDring.P5.Data.FixZero.C017
import LeanDring.P5.Data.FixZero.C018
import LeanDring.P5.Data.FixZero.C019
import LeanDring.P5.Data.FixZero.C020
import LeanDring.P5.Data.FixZero.C021
import LeanDring.P5.Data.FixZero.C022
import LeanDring.P5.Data.FixZero.C023
import LeanDring.P5.Data.FixZero.C024
import LeanDring.P5.Data.FixZero.C025
import LeanDring.P5.Data.FixZero.C026
import LeanDring.P5.Data.FixZero.C027
import LeanDring.P5.Data.FixZero.C028
import LeanDring.P5.Data.FixZero.C029
import LeanDring.P5.Data.FixZero.C030
import LeanDring.P5.Data.FixZero.C031
import LeanDring.P5.Data.FixZero.C032
import LeanDring.P5.Data.FixZero.C033
import LeanDring.P5.Data.FixZero.C034
import LeanDring.P5.Data.FixZero.C035
import LeanDring.P5.Data.FixZero.C036
import LeanDring.P5.Data.FixZero.C037
import LeanDring.P5.Data.FixZero.C038
import LeanDring.P5.Data.FixZero.C039
import LeanDring.P5.Data.FixZero.C040
import LeanDring.P5.Data.FixZero.C041
import LeanDring.P5.Data.FixZero.C042
import LeanDring.P5.Data.FixZero.C043
import LeanDring.P5.Data.FixZero.C044
import LeanDring.P5.Data.FixZero.C045
import LeanDring.P5.Data.FixZero.C046
import LeanDring.P5.Data.FixZero.C047
import LeanDring.P5.Data.FixZero.C048
import LeanDring.P5.Data.FixZero.C049
import LeanDring.P5.Data.FixZero.C050
import LeanDring.P5.Data.FixZero.C051
import LeanDring.P5.Data.FixZero.C052
import LeanDring.P5.Data.FixZero.C053
import LeanDring.P5.Data.FixZero.C054
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
import LeanDring.P5.Data.MatchPair.C001
import LeanDring.P5.Data.MatchPair.C002
import LeanDring.P5.Data.MatchPair.C011
import LeanDring.P5.Data.MatchPair.C003
import LeanDring.P5.Data.MatchPair.C005
import LeanDring.P5.Data.MatchPair.C006
import LeanDring.P5.Data.MatchPair.C007
import LeanDring.P5.Data.MatchPair.C008
import LeanDring.P5.Data.MatchPair.C009
import LeanDring.P5.Data.MatchPair.C010

/-! # Stage-5 per-column-class master theorems, chunk 4 (auto-emitted).  -/

namespace LeanDring.P5Presentation

open MulAction Finset LeanDring.DRing LeanDring.MonGSet

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.style.longLine false

theorem master_32 (p : Nat) (hp : p < (Q2.transData.getD 32 []).length)
    (hrep : (Q2.cosetIsRep.getD 32 []).getD p false = true)
    (rK : Fin 148) (j : Nat) (hj : j < (repChars.getD rK.val []).length)
    (hq : (normIsRep.getD rK.val []).getD j false = true) :
    species (Q2.reps (⟨32, by decide⟩ : Fin 148)) (colE2 ⟨32, by decide⟩ p hp)
        (rowE2 rK j hj hq)
      = species (reps (⟨32, by decide⟩ : Fin 148))
        (colE1 ⟨32, by decide⟩ p (transLenTr ⟨32, by decide⟩ p hp)) (rowE1 rK j hj) := by
  rcases rK with ⟨nK, hnK⟩; interval_cases nK
  · exact match_zero_len ⟨0, by decide⟩ ⟨32, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨1, by decide⟩ ⟨32, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨2, by decide⟩ ⟨32, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨3, by decide⟩ ⟨32, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨4, by decide⟩ ⟨32, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨5, by decide⟩ ⟨32, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨6, by decide⟩ ⟨32, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨7, by decide⟩ ⟨32, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨8, by decide⟩ ⟨32, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨9, by decide⟩ ⟨32, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨10, by decide⟩ ⟨32, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨11, by decide⟩ ⟨32, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨12, by decide⟩ ⟨32, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_fix ⟨13, by decide⟩ ⟨32, by decide⟩ p hp j hj hq fz1_13_32 fz2_13_32
  · exact match_zero_fix ⟨14, by decide⟩ ⟨32, by decide⟩ p hp j hj hq fz1_14_32 fz2_14_32
  · exact match_zero_fix ⟨15, by decide⟩ ⟨32, by decide⟩ p hp j hj hq fz1_15_32 fz2_15_32
  · exact match_zero_fix ⟨16, by decide⟩ ⟨32, by decide⟩ p hp j hj hq fz1_16_32 fz2_16_32
  · exact match_zero_fix ⟨17, by decide⟩ ⟨32, by decide⟩ p hp j hj hq fz1_17_32 fz2_17_32
  · exact match_zero_fix ⟨18, by decide⟩ ⟨32, by decide⟩ p hp j hj hq fz1_18_32 fz2_18_32
  · exact match_zero_fix ⟨19, by decide⟩ ⟨32, by decide⟩ p hp j hj hq fz1_19_32 fz2_19_32
  · exact match_zero_fix ⟨20, by decide⟩ ⟨32, by decide⟩ p hp j hj hq fz1_20_32 fz2_20_32
  · exact match_zero_fix ⟨21, by decide⟩ ⟨32, by decide⟩ p hp j hj hq fz1_21_32 fz2_21_32
  · exact match_zero_fix ⟨22, by decide⟩ ⟨32, by decide⟩ p hp j hj hq fz1_22_32 fz2_22_32
  · exact match_zero_fix ⟨23, by decide⟩ ⟨32, by decide⟩ p hp j hj hq fz1_23_32 fz2_23_32
  · exact match_zero_fix ⟨24, by decide⟩ ⟨32, by decide⟩ p hp j hj hq fz1_24_32 fz2_24_32
  · exact match_zero_fix ⟨25, by decide⟩ ⟨32, by decide⟩ p hp j hj hq fz1_25_32 fz2_25_32
  · exact match_zero_fix ⟨26, by decide⟩ ⟨32, by decide⟩ p hp j hj hq fz1_26_32 fz2_26_32
  · exact match_zero_fix ⟨27, by decide⟩ ⟨32, by decide⟩ p hp j hj hq fz1_27_32 fz2_27_32
  · exact match_zero_fix ⟨28, by decide⟩ ⟨32, by decide⟩ p hp j hj hq fz1_28_32 fz2_28_32
  · exact match_zero_fix ⟨29, by decide⟩ ⟨32, by decide⟩ p hp j hj hq fz1_29_32 fz2_29_32
  · exact match_zero_fix ⟨30, by decide⟩ ⟨32, by decide⟩ p hp j hj hq fz1_30_32 fz2_30_32
  · exact match_zero_fix ⟨31, by decide⟩ ⟨32, by decide⟩ p hp j hj hq fz1_31_32 fz2_31_32
  · exact pair_32_32 p hp hrep j hj hq
  · exact match_zero_fix ⟨33, by decide⟩ ⟨32, by decide⟩ p hp j hj hq fz1_33_32 fz2_33_32
  · exact match_zero_fix ⟨34, by decide⟩ ⟨32, by decide⟩ p hp j hj hq fz1_34_32 fz2_34_32
  · exact match_zero_fix ⟨35, by decide⟩ ⟨32, by decide⟩ p hp j hj hq fz1_35_32 fz2_35_32
  · exact match_zero_fix ⟨36, by decide⟩ ⟨32, by decide⟩ p hp j hj hq fz1_36_32 fz2_36_32
  · exact match_zero_fix ⟨37, by decide⟩ ⟨32, by decide⟩ p hp j hj hq fz1_37_32 fz2_37_32
  · exact match_zero_fix ⟨38, by decide⟩ ⟨32, by decide⟩ p hp j hj hq fz1_38_32 fz2_38_32
  · exact match_zero_fix ⟨39, by decide⟩ ⟨32, by decide⟩ p hp j hj hq fz1_39_32 fz2_39_32
  · exact match_zero_fix ⟨40, by decide⟩ ⟨32, by decide⟩ p hp j hj hq fz1_40_32 fz2_40_32
  · exact match_zero_fix ⟨41, by decide⟩ ⟨32, by decide⟩ p hp j hj hq fz1_41_32 fz2_41_32
  · exact match_zero_fix ⟨42, by decide⟩ ⟨32, by decide⟩ p hp j hj hq fz1_42_32 fz2_42_32
  · exact match_zero_fix ⟨43, by decide⟩ ⟨32, by decide⟩ p hp j hj hq fz1_43_32 fz2_43_32
  · exact match_zero_fix ⟨44, by decide⟩ ⟨32, by decide⟩ p hp j hj hq fz1_44_32 fz2_44_32
  · exact match_zero_fix ⟨45, by decide⟩ ⟨32, by decide⟩ p hp j hj hq fz1_45_32 fz2_45_32
  · exact match_zero_fix ⟨46, by decide⟩ ⟨32, by decide⟩ p hp j hj hq fz1_46_32 fz2_46_32
  · exact match_zero_fix ⟨47, by decide⟩ ⟨32, by decide⟩ p hp j hj hq fz1_47_32 fz2_47_32
  · exact match_zero_fix ⟨48, by decide⟩ ⟨32, by decide⟩ p hp j hj hq fz1_48_32 fz2_48_32
  · exact match_zero_fix ⟨49, by decide⟩ ⟨32, by decide⟩ p hp j hj hq fz1_49_32 fz2_49_32
  · exact match_zero_fix ⟨50, by decide⟩ ⟨32, by decide⟩ p hp j hj hq fz1_50_32 fz2_50_32
  · exact match_zero_fix ⟨51, by decide⟩ ⟨32, by decide⟩ p hp j hj hq fz1_51_32 fz2_51_32
  · exact match_zero_fix ⟨52, by decide⟩ ⟨32, by decide⟩ p hp j hj hq fz1_52_32 fz2_52_32
  · exact match_zero_fix ⟨53, by decide⟩ ⟨32, by decide⟩ p hp j hj hq fz1_53_32 fz2_53_32
  · exact match_zero_fix ⟨54, by decide⟩ ⟨32, by decide⟩ p hp j hj hq fz1_54_32 fz2_54_32
  · exact match_zero_fix ⟨55, by decide⟩ ⟨32, by decide⟩ p hp j hj hq fz1_55_32 fz2_55_32
  · exact match_zero_fix ⟨56, by decide⟩ ⟨32, by decide⟩ p hp j hj hq fz1_56_32 fz2_56_32
  · exact match_zero_fix ⟨57, by decide⟩ ⟨32, by decide⟩ p hp j hj hq fz1_57_32 fz2_57_32
  · exact match_zero_fix ⟨58, by decide⟩ ⟨32, by decide⟩ p hp j hj hq fz1_58_32 fz2_58_32
  · exact match_zero_fix ⟨59, by decide⟩ ⟨32, by decide⟩ p hp j hj hq fz1_59_32 fz2_59_32
  · exact match_zero_fix ⟨60, by decide⟩ ⟨32, by decide⟩ p hp j hj hq fz1_60_32 fz2_60_32
  · exact match_zero_fix ⟨61, by decide⟩ ⟨32, by decide⟩ p hp j hj hq fz1_61_32 fz2_61_32
  · exact match_zero_fix ⟨62, by decide⟩ ⟨32, by decide⟩ p hp j hj hq fz1_62_32 fz2_62_32
  · exact match_zero_fix ⟨63, by decide⟩ ⟨32, by decide⟩ p hp j hj hq fz1_63_32 fz2_63_32
  · exact match_zero_fix ⟨64, by decide⟩ ⟨32, by decide⟩ p hp j hj hq fz1_64_32 fz2_64_32
  · exact match_zero_fix ⟨65, by decide⟩ ⟨32, by decide⟩ p hp j hj hq fz1_65_32 fz2_65_32
  · exact match_zero_fix ⟨66, by decide⟩ ⟨32, by decide⟩ p hp j hj hq fz1_66_32 fz2_66_32
  · exact match_zero_fix ⟨67, by decide⟩ ⟨32, by decide⟩ p hp j hj hq fz1_67_32 fz2_67_32
  · exact match_zero_fix ⟨68, by decide⟩ ⟨32, by decide⟩ p hp j hj hq fz1_68_32 fz2_68_32
  · exact match_zero_fix ⟨69, by decide⟩ ⟨32, by decide⟩ p hp j hj hq fz1_69_32 fz2_69_32
  · exact match_zero_fix ⟨70, by decide⟩ ⟨32, by decide⟩ p hp j hj hq fz1_70_32 fz2_70_32
  · exact match_zero_fix ⟨71, by decide⟩ ⟨32, by decide⟩ p hp j hj hq fz1_71_32 fz2_71_32
  · exact match_zero_fix ⟨72, by decide⟩ ⟨32, by decide⟩ p hp j hj hq fz1_72_32 fz2_72_32
  · exact match_zero_fix ⟨73, by decide⟩ ⟨32, by decide⟩ p hp j hj hq fz1_73_32 fz2_73_32
  · exact match_zero_fix ⟨74, by decide⟩ ⟨32, by decide⟩ p hp j hj hq fz1_74_32 fz2_74_32
  · exact pair_75_32 p hp hrep j hj hq
  · exact pair_76_32 p hp hrep j hj hq
  · exact pair_77_32 p hp hrep j hj hq
  · exact pair_78_32 p hp hrep j hj hq
  · exact pair_79_32 p hp hrep j hj hq
  · exact match_zero_fix ⟨80, by decide⟩ ⟨32, by decide⟩ p hp j hj hq fz1_80_32 fz2_80_32
  · exact match_zero_fix ⟨81, by decide⟩ ⟨32, by decide⟩ p hp j hj hq fz1_81_32 fz2_81_32
  · exact match_zero_fix ⟨82, by decide⟩ ⟨32, by decide⟩ p hp j hj hq fz1_82_32 fz2_82_32
  · exact match_zero_fix ⟨83, by decide⟩ ⟨32, by decide⟩ p hp j hj hq fz1_83_32 fz2_83_32
  · exact match_zero_fix ⟨84, by decide⟩ ⟨32, by decide⟩ p hp j hj hq fz1_84_32 fz2_84_32
  · exact match_zero_fix ⟨85, by decide⟩ ⟨32, by decide⟩ p hp j hj hq fz1_85_32 fz2_85_32
  · exact match_zero_fix ⟨86, by decide⟩ ⟨32, by decide⟩ p hp j hj hq fz1_86_32 fz2_86_32
  · exact match_zero_fix ⟨87, by decide⟩ ⟨32, by decide⟩ p hp j hj hq fz1_87_32 fz2_87_32
  · exact match_zero_fix ⟨88, by decide⟩ ⟨32, by decide⟩ p hp j hj hq fz1_88_32 fz2_88_32
  · exact match_zero_fix ⟨89, by decide⟩ ⟨32, by decide⟩ p hp j hj hq fz1_89_32 fz2_89_32
  · exact match_zero_fix ⟨90, by decide⟩ ⟨32, by decide⟩ p hp j hj hq fz1_90_32 fz2_90_32
  · exact match_zero_fix ⟨91, by decide⟩ ⟨32, by decide⟩ p hp j hj hq fz1_91_32 fz2_91_32
  · exact match_zero_fix ⟨92, by decide⟩ ⟨32, by decide⟩ p hp j hj hq fz1_92_32 fz2_92_32
  · exact match_zero_fix ⟨93, by decide⟩ ⟨32, by decide⟩ p hp j hj hq fz1_93_32 fz2_93_32
  · exact pair_94_32 p hp hrep j hj hq
  · exact match_zero_fix ⟨95, by decide⟩ ⟨32, by decide⟩ p hp j hj hq fz1_95_32 fz2_95_32
  · exact match_zero_fix ⟨96, by decide⟩ ⟨32, by decide⟩ p hp j hj hq fz1_96_32 fz2_96_32
  · exact match_zero_fix ⟨97, by decide⟩ ⟨32, by decide⟩ p hp j hj hq fz1_97_32 fz2_97_32
  · exact match_zero_fix ⟨98, by decide⟩ ⟨32, by decide⟩ p hp j hj hq fz1_98_32 fz2_98_32
  · exact match_zero_fix ⟨99, by decide⟩ ⟨32, by decide⟩ p hp j hj hq fz1_99_32 fz2_99_32
  · exact match_zero_fix ⟨100, by decide⟩ ⟨32, by decide⟩ p hp j hj hq fz1_100_32 fz2_100_32
  · exact match_zero_fix ⟨101, by decide⟩ ⟨32, by decide⟩ p hp j hj hq fz1_101_32 fz2_101_32
  · exact match_zero_fix ⟨102, by decide⟩ ⟨32, by decide⟩ p hp j hj hq fz1_102_32 fz2_102_32
  · exact match_zero_fix ⟨103, by decide⟩ ⟨32, by decide⟩ p hp j hj hq fz1_103_32 fz2_103_32
  · exact match_zero_fix ⟨104, by decide⟩ ⟨32, by decide⟩ p hp j hj hq fz1_104_32 fz2_104_32
  · exact match_zero_fix ⟨105, by decide⟩ ⟨32, by decide⟩ p hp j hj hq fz1_105_32 fz2_105_32
  · exact match_zero_fix ⟨106, by decide⟩ ⟨32, by decide⟩ p hp j hj hq fz1_106_32 fz2_106_32
  · exact match_zero_fix ⟨107, by decide⟩ ⟨32, by decide⟩ p hp j hj hq fz1_107_32 fz2_107_32
  · exact match_zero_fix ⟨108, by decide⟩ ⟨32, by decide⟩ p hp j hj hq fz1_108_32 fz2_108_32
  · exact match_zero_fix ⟨109, by decide⟩ ⟨32, by decide⟩ p hp j hj hq fz1_109_32 fz2_109_32
  · exact match_zero_fix ⟨110, by decide⟩ ⟨32, by decide⟩ p hp j hj hq fz1_110_32 fz2_110_32
  · exact match_zero_fix ⟨111, by decide⟩ ⟨32, by decide⟩ p hp j hj hq fz1_111_32 fz2_111_32
  · exact match_zero_fix ⟨112, by decide⟩ ⟨32, by decide⟩ p hp j hj hq fz1_112_32 fz2_112_32
  · exact match_zero_fix ⟨113, by decide⟩ ⟨32, by decide⟩ p hp j hj hq fz1_113_32 fz2_113_32
  · exact match_zero_fix ⟨114, by decide⟩ ⟨32, by decide⟩ p hp j hj hq fz1_114_32 fz2_114_32
  · exact match_zero_fix ⟨115, by decide⟩ ⟨32, by decide⟩ p hp j hj hq fz1_115_32 fz2_115_32
  · exact match_zero_fix ⟨116, by decide⟩ ⟨32, by decide⟩ p hp j hj hq fz1_116_32 fz2_116_32
  · exact match_zero_fix ⟨117, by decide⟩ ⟨32, by decide⟩ p hp j hj hq fz1_117_32 fz2_117_32
  · exact match_zero_fix ⟨118, by decide⟩ ⟨32, by decide⟩ p hp j hj hq fz1_118_32 fz2_118_32
  · exact match_zero_fix ⟨119, by decide⟩ ⟨32, by decide⟩ p hp j hj hq fz1_119_32 fz2_119_32
  · exact pair_120_32 p hp hrep j hj hq
  · exact pair_121_32 p hp hrep j hj hq
  · exact match_zero_fix ⟨122, by decide⟩ ⟨32, by decide⟩ p hp j hj hq fz1_122_32 fz2_122_32
  · exact match_zero_fix ⟨123, by decide⟩ ⟨32, by decide⟩ p hp j hj hq fz1_123_32 fz2_123_32
  · exact match_zero_fix ⟨124, by decide⟩ ⟨32, by decide⟩ p hp j hj hq fz1_124_32 fz2_124_32
  · exact match_zero_fix ⟨125, by decide⟩ ⟨32, by decide⟩ p hp j hj hq fz1_125_32 fz2_125_32
  · exact match_zero_fix ⟨126, by decide⟩ ⟨32, by decide⟩ p hp j hj hq fz1_126_32 fz2_126_32
  · exact pair_127_32 p hp hrep j hj hq
  · exact match_zero_fix ⟨128, by decide⟩ ⟨32, by decide⟩ p hp j hj hq fz1_128_32 fz2_128_32
  · exact match_zero_fix ⟨129, by decide⟩ ⟨32, by decide⟩ p hp j hj hq fz1_129_32 fz2_129_32
  · exact match_zero_fix ⟨130, by decide⟩ ⟨32, by decide⟩ p hp j hj hq fz1_130_32 fz2_130_32
  · exact match_zero_fix ⟨131, by decide⟩ ⟨32, by decide⟩ p hp j hj hq fz1_131_32 fz2_131_32
  · exact match_zero_fix ⟨132, by decide⟩ ⟨32, by decide⟩ p hp j hj hq fz1_132_32 fz2_132_32
  · exact pair_133_32 p hp hrep j hj hq
  · exact match_zero_fix ⟨134, by decide⟩ ⟨32, by decide⟩ p hp j hj hq fz1_134_32 fz2_134_32
  · exact match_zero_fix ⟨135, by decide⟩ ⟨32, by decide⟩ p hp j hj hq fz1_135_32 fz2_135_32
  · exact match_zero_fix ⟨136, by decide⟩ ⟨32, by decide⟩ p hp j hj hq fz1_136_32 fz2_136_32
  · exact match_zero_fix ⟨137, by decide⟩ ⟨32, by decide⟩ p hp j hj hq fz1_137_32 fz2_137_32
  · exact match_zero_fix ⟨138, by decide⟩ ⟨32, by decide⟩ p hp j hj hq fz1_138_32 fz2_138_32
  · exact pair_139_32 p hp hrep j hj hq
  · exact match_zero_fix ⟨140, by decide⟩ ⟨32, by decide⟩ p hp j hj hq fz1_140_32 fz2_140_32
  · exact match_zero_fix ⟨141, by decide⟩ ⟨32, by decide⟩ p hp j hj hq fz1_141_32 fz2_141_32
  · exact pair_142_32 p hp hrep j hj hq
  · exact match_zero_fix ⟨143, by decide⟩ ⟨32, by decide⟩ p hp j hj hq fz1_143_32 fz2_143_32
  · exact match_zero_fix ⟨144, by decide⟩ ⟨32, by decide⟩ p hp j hj hq fz1_144_32 fz2_144_32
  · exact match_zero_fix ⟨145, by decide⟩ ⟨32, by decide⟩ p hp j hj hq fz1_145_32 fz2_145_32
  · exact match_zero_fix ⟨146, by decide⟩ ⟨32, by decide⟩ p hp j hj hq fz1_146_32 fz2_146_32
  · exact pair_147_32 p hp hrep j hj hq

theorem master_33 (p : Nat) (hp : p < (Q2.transData.getD 33 []).length)
    (hrep : (Q2.cosetIsRep.getD 33 []).getD p false = true)
    (rK : Fin 148) (j : Nat) (hj : j < (repChars.getD rK.val []).length)
    (hq : (normIsRep.getD rK.val []).getD j false = true) :
    species (Q2.reps (⟨33, by decide⟩ : Fin 148)) (colE2 ⟨33, by decide⟩ p hp)
        (rowE2 rK j hj hq)
      = species (reps (⟨33, by decide⟩ : Fin 148))
        (colE1 ⟨33, by decide⟩ p (transLenTr ⟨33, by decide⟩ p hp)) (rowE1 rK j hj) := by
  rcases rK with ⟨nK, hnK⟩; interval_cases nK
  · exact match_zero_len ⟨0, by decide⟩ ⟨33, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨1, by decide⟩ ⟨33, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨2, by decide⟩ ⟨33, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨3, by decide⟩ ⟨33, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨4, by decide⟩ ⟨33, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨5, by decide⟩ ⟨33, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨6, by decide⟩ ⟨33, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨7, by decide⟩ ⟨33, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨8, by decide⟩ ⟨33, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨9, by decide⟩ ⟨33, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨10, by decide⟩ ⟨33, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨11, by decide⟩ ⟨33, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨12, by decide⟩ ⟨33, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_fix ⟨13, by decide⟩ ⟨33, by decide⟩ p hp j hj hq fz1_13_33 fz2_13_33
  · exact match_zero_fix ⟨14, by decide⟩ ⟨33, by decide⟩ p hp j hj hq fz1_14_33 fz2_14_33
  · exact match_zero_fix ⟨15, by decide⟩ ⟨33, by decide⟩ p hp j hj hq fz1_15_33 fz2_15_33
  · exact match_zero_fix ⟨16, by decide⟩ ⟨33, by decide⟩ p hp j hj hq fz1_16_33 fz2_16_33
  · exact match_zero_fix ⟨17, by decide⟩ ⟨33, by decide⟩ p hp j hj hq fz1_17_33 fz2_17_33
  · exact match_zero_fix ⟨18, by decide⟩ ⟨33, by decide⟩ p hp j hj hq fz1_18_33 fz2_18_33
  · exact match_zero_fix ⟨19, by decide⟩ ⟨33, by decide⟩ p hp j hj hq fz1_19_33 fz2_19_33
  · exact match_zero_fix ⟨20, by decide⟩ ⟨33, by decide⟩ p hp j hj hq fz1_20_33 fz2_20_33
  · exact match_zero_fix ⟨21, by decide⟩ ⟨33, by decide⟩ p hp j hj hq fz1_21_33 fz2_21_33
  · exact match_zero_fix ⟨22, by decide⟩ ⟨33, by decide⟩ p hp j hj hq fz1_22_33 fz2_22_33
  · exact match_zero_fix ⟨23, by decide⟩ ⟨33, by decide⟩ p hp j hj hq fz1_23_33 fz2_23_33
  · exact match_zero_fix ⟨24, by decide⟩ ⟨33, by decide⟩ p hp j hj hq fz1_24_33 fz2_24_33
  · exact match_zero_fix ⟨25, by decide⟩ ⟨33, by decide⟩ p hp j hj hq fz1_25_33 fz2_25_33
  · exact match_zero_fix ⟨26, by decide⟩ ⟨33, by decide⟩ p hp j hj hq fz1_26_33 fz2_26_33
  · exact match_zero_fix ⟨27, by decide⟩ ⟨33, by decide⟩ p hp j hj hq fz1_27_33 fz2_27_33
  · exact match_zero_fix ⟨28, by decide⟩ ⟨33, by decide⟩ p hp j hj hq fz1_28_33 fz2_28_33
  · exact match_zero_fix ⟨29, by decide⟩ ⟨33, by decide⟩ p hp j hj hq fz1_29_33 fz2_29_33
  · exact match_zero_fix ⟨30, by decide⟩ ⟨33, by decide⟩ p hp j hj hq fz1_30_33 fz2_30_33
  · exact match_zero_fix ⟨31, by decide⟩ ⟨33, by decide⟩ p hp j hj hq fz1_31_33 fz2_31_33
  · exact match_zero_fix ⟨32, by decide⟩ ⟨33, by decide⟩ p hp j hj hq fz1_32_33 fz2_32_33
  · exact pair_33_33 p hp hrep j hj hq
  · exact match_zero_fix ⟨34, by decide⟩ ⟨33, by decide⟩ p hp j hj hq fz1_34_33 fz2_34_33
  · exact match_zero_fix ⟨35, by decide⟩ ⟨33, by decide⟩ p hp j hj hq fz1_35_33 fz2_35_33
  · exact match_zero_fix ⟨36, by decide⟩ ⟨33, by decide⟩ p hp j hj hq fz1_36_33 fz2_36_33
  · exact match_zero_fix ⟨37, by decide⟩ ⟨33, by decide⟩ p hp j hj hq fz1_37_33 fz2_37_33
  · exact match_zero_fix ⟨38, by decide⟩ ⟨33, by decide⟩ p hp j hj hq fz1_38_33 fz2_38_33
  · exact match_zero_fix ⟨39, by decide⟩ ⟨33, by decide⟩ p hp j hj hq fz1_39_33 fz2_39_33
  · exact match_zero_fix ⟨40, by decide⟩ ⟨33, by decide⟩ p hp j hj hq fz1_40_33 fz2_40_33
  · exact match_zero_fix ⟨41, by decide⟩ ⟨33, by decide⟩ p hp j hj hq fz1_41_33 fz2_41_33
  · exact match_zero_fix ⟨42, by decide⟩ ⟨33, by decide⟩ p hp j hj hq fz1_42_33 fz2_42_33
  · exact match_zero_fix ⟨43, by decide⟩ ⟨33, by decide⟩ p hp j hj hq fz1_43_33 fz2_43_33
  · exact match_zero_fix ⟨44, by decide⟩ ⟨33, by decide⟩ p hp j hj hq fz1_44_33 fz2_44_33
  · exact match_zero_fix ⟨45, by decide⟩ ⟨33, by decide⟩ p hp j hj hq fz1_45_33 fz2_45_33
  · exact match_zero_fix ⟨46, by decide⟩ ⟨33, by decide⟩ p hp j hj hq fz1_46_33 fz2_46_33
  · exact match_zero_fix ⟨47, by decide⟩ ⟨33, by decide⟩ p hp j hj hq fz1_47_33 fz2_47_33
  · exact match_zero_fix ⟨48, by decide⟩ ⟨33, by decide⟩ p hp j hj hq fz1_48_33 fz2_48_33
  · exact match_zero_fix ⟨49, by decide⟩ ⟨33, by decide⟩ p hp j hj hq fz1_49_33 fz2_49_33
  · exact match_zero_fix ⟨50, by decide⟩ ⟨33, by decide⟩ p hp j hj hq fz1_50_33 fz2_50_33
  · exact match_zero_fix ⟨51, by decide⟩ ⟨33, by decide⟩ p hp j hj hq fz1_51_33 fz2_51_33
  · exact match_zero_fix ⟨52, by decide⟩ ⟨33, by decide⟩ p hp j hj hq fz1_52_33 fz2_52_33
  · exact match_zero_fix ⟨53, by decide⟩ ⟨33, by decide⟩ p hp j hj hq fz1_53_33 fz2_53_33
  · exact match_zero_fix ⟨54, by decide⟩ ⟨33, by decide⟩ p hp j hj hq fz1_54_33 fz2_54_33
  · exact pair_55_33 p hp hrep j hj hq
  · exact pair_56_33 p hp hrep j hj hq
  · exact pair_57_33 p hp hrep j hj hq
  · exact pair_58_33 p hp hrep j hj hq
  · exact pair_59_33 p hp hrep j hj hq
  · exact match_zero_fix ⟨60, by decide⟩ ⟨33, by decide⟩ p hp j hj hq fz1_60_33 fz2_60_33
  · exact match_zero_fix ⟨61, by decide⟩ ⟨33, by decide⟩ p hp j hj hq fz1_61_33 fz2_61_33
  · exact match_zero_fix ⟨62, by decide⟩ ⟨33, by decide⟩ p hp j hj hq fz1_62_33 fz2_62_33
  · exact match_zero_fix ⟨63, by decide⟩ ⟨33, by decide⟩ p hp j hj hq fz1_63_33 fz2_63_33
  · exact match_zero_fix ⟨64, by decide⟩ ⟨33, by decide⟩ p hp j hj hq fz1_64_33 fz2_64_33
  · exact match_zero_fix ⟨65, by decide⟩ ⟨33, by decide⟩ p hp j hj hq fz1_65_33 fz2_65_33
  · exact match_zero_fix ⟨66, by decide⟩ ⟨33, by decide⟩ p hp j hj hq fz1_66_33 fz2_66_33
  · exact match_zero_fix ⟨67, by decide⟩ ⟨33, by decide⟩ p hp j hj hq fz1_67_33 fz2_67_33
  · exact match_zero_fix ⟨68, by decide⟩ ⟨33, by decide⟩ p hp j hj hq fz1_68_33 fz2_68_33
  · exact match_zero_fix ⟨69, by decide⟩ ⟨33, by decide⟩ p hp j hj hq fz1_69_33 fz2_69_33
  · exact match_zero_fix ⟨70, by decide⟩ ⟨33, by decide⟩ p hp j hj hq fz1_70_33 fz2_70_33
  · exact match_zero_fix ⟨71, by decide⟩ ⟨33, by decide⟩ p hp j hj hq fz1_71_33 fz2_71_33
  · exact match_zero_fix ⟨72, by decide⟩ ⟨33, by decide⟩ p hp j hj hq fz1_72_33 fz2_72_33
  · exact match_zero_fix ⟨73, by decide⟩ ⟨33, by decide⟩ p hp j hj hq fz1_73_33 fz2_73_33
  · exact match_zero_fix ⟨74, by decide⟩ ⟨33, by decide⟩ p hp j hj hq fz1_74_33 fz2_74_33
  · exact match_zero_fix ⟨75, by decide⟩ ⟨33, by decide⟩ p hp j hj hq fz1_75_33 fz2_75_33
  · exact match_zero_fix ⟨76, by decide⟩ ⟨33, by decide⟩ p hp j hj hq fz1_76_33 fz2_76_33
  · exact match_zero_fix ⟨77, by decide⟩ ⟨33, by decide⟩ p hp j hj hq fz1_77_33 fz2_77_33
  · exact match_zero_fix ⟨78, by decide⟩ ⟨33, by decide⟩ p hp j hj hq fz1_78_33 fz2_78_33
  · exact match_zero_fix ⟨79, by decide⟩ ⟨33, by decide⟩ p hp j hj hq fz1_79_33 fz2_79_33
  · exact match_zero_fix ⟨80, by decide⟩ ⟨33, by decide⟩ p hp j hj hq fz1_80_33 fz2_80_33
  · exact match_zero_fix ⟨81, by decide⟩ ⟨33, by decide⟩ p hp j hj hq fz1_81_33 fz2_81_33
  · exact match_zero_fix ⟨82, by decide⟩ ⟨33, by decide⟩ p hp j hj hq fz1_82_33 fz2_82_33
  · exact match_zero_fix ⟨83, by decide⟩ ⟨33, by decide⟩ p hp j hj hq fz1_83_33 fz2_83_33
  · exact match_zero_fix ⟨84, by decide⟩ ⟨33, by decide⟩ p hp j hj hq fz1_84_33 fz2_84_33
  · exact match_zero_fix ⟨85, by decide⟩ ⟨33, by decide⟩ p hp j hj hq fz1_85_33 fz2_85_33
  · exact match_zero_fix ⟨86, by decide⟩ ⟨33, by decide⟩ p hp j hj hq fz1_86_33 fz2_86_33
  · exact match_zero_fix ⟨87, by decide⟩ ⟨33, by decide⟩ p hp j hj hq fz1_87_33 fz2_87_33
  · exact match_zero_fix ⟨88, by decide⟩ ⟨33, by decide⟩ p hp j hj hq fz1_88_33 fz2_88_33
  · exact match_zero_fix ⟨89, by decide⟩ ⟨33, by decide⟩ p hp j hj hq fz1_89_33 fz2_89_33
  · exact match_zero_fix ⟨90, by decide⟩ ⟨33, by decide⟩ p hp j hj hq fz1_90_33 fz2_90_33
  · exact match_zero_fix ⟨91, by decide⟩ ⟨33, by decide⟩ p hp j hj hq fz1_91_33 fz2_91_33
  · exact match_zero_fix ⟨92, by decide⟩ ⟨33, by decide⟩ p hp j hj hq fz1_92_33 fz2_92_33
  · exact match_zero_fix ⟨93, by decide⟩ ⟨33, by decide⟩ p hp j hj hq fz1_93_33 fz2_93_33
  · exact match_zero_fix ⟨94, by decide⟩ ⟨33, by decide⟩ p hp j hj hq fz1_94_33 fz2_94_33
  · exact pair_95_33 p hp hrep j hj hq
  · exact match_zero_fix ⟨96, by decide⟩ ⟨33, by decide⟩ p hp j hj hq fz1_96_33 fz2_96_33
  · exact match_zero_fix ⟨97, by decide⟩ ⟨33, by decide⟩ p hp j hj hq fz1_97_33 fz2_97_33
  · exact match_zero_fix ⟨98, by decide⟩ ⟨33, by decide⟩ p hp j hj hq fz1_98_33 fz2_98_33
  · exact match_zero_fix ⟨99, by decide⟩ ⟨33, by decide⟩ p hp j hj hq fz1_99_33 fz2_99_33
  · exact match_zero_fix ⟨100, by decide⟩ ⟨33, by decide⟩ p hp j hj hq fz1_100_33 fz2_100_33
  · exact match_zero_fix ⟨101, by decide⟩ ⟨33, by decide⟩ p hp j hj hq fz1_101_33 fz2_101_33
  · exact match_zero_fix ⟨102, by decide⟩ ⟨33, by decide⟩ p hp j hj hq fz1_102_33 fz2_102_33
  · exact match_zero_fix ⟨103, by decide⟩ ⟨33, by decide⟩ p hp j hj hq fz1_103_33 fz2_103_33
  · exact match_zero_fix ⟨104, by decide⟩ ⟨33, by decide⟩ p hp j hj hq fz1_104_33 fz2_104_33
  · exact match_zero_fix ⟨105, by decide⟩ ⟨33, by decide⟩ p hp j hj hq fz1_105_33 fz2_105_33
  · exact match_zero_fix ⟨106, by decide⟩ ⟨33, by decide⟩ p hp j hj hq fz1_106_33 fz2_106_33
  · exact match_zero_fix ⟨107, by decide⟩ ⟨33, by decide⟩ p hp j hj hq fz1_107_33 fz2_107_33
  · exact match_zero_fix ⟨108, by decide⟩ ⟨33, by decide⟩ p hp j hj hq fz1_108_33 fz2_108_33
  · exact match_zero_fix ⟨109, by decide⟩ ⟨33, by decide⟩ p hp j hj hq fz1_109_33 fz2_109_33
  · exact match_zero_fix ⟨110, by decide⟩ ⟨33, by decide⟩ p hp j hj hq fz1_110_33 fz2_110_33
  · exact match_zero_fix ⟨111, by decide⟩ ⟨33, by decide⟩ p hp j hj hq fz1_111_33 fz2_111_33
  · exact match_zero_fix ⟨112, by decide⟩ ⟨33, by decide⟩ p hp j hj hq fz1_112_33 fz2_112_33
  · exact match_zero_fix ⟨113, by decide⟩ ⟨33, by decide⟩ p hp j hj hq fz1_113_33 fz2_113_33
  · exact match_zero_fix ⟨114, by decide⟩ ⟨33, by decide⟩ p hp j hj hq fz1_114_33 fz2_114_33
  · exact match_zero_fix ⟨115, by decide⟩ ⟨33, by decide⟩ p hp j hj hq fz1_115_33 fz2_115_33
  · exact pair_116_33 p hp hrep j hj hq
  · exact match_zero_fix ⟨117, by decide⟩ ⟨33, by decide⟩ p hp j hj hq fz1_117_33 fz2_117_33
  · exact match_zero_fix ⟨118, by decide⟩ ⟨33, by decide⟩ p hp j hj hq fz1_118_33 fz2_118_33
  · exact match_zero_fix ⟨119, by decide⟩ ⟨33, by decide⟩ p hp j hj hq fz1_119_33 fz2_119_33
  · exact match_zero_fix ⟨120, by decide⟩ ⟨33, by decide⟩ p hp j hj hq fz1_120_33 fz2_120_33
  · exact match_zero_fix ⟨121, by decide⟩ ⟨33, by decide⟩ p hp j hj hq fz1_121_33 fz2_121_33
  · exact match_zero_fix ⟨122, by decide⟩ ⟨33, by decide⟩ p hp j hj hq fz1_122_33 fz2_122_33
  · exact match_zero_fix ⟨123, by decide⟩ ⟨33, by decide⟩ p hp j hj hq fz1_123_33 fz2_123_33
  · exact pair_124_33 p hp hrep j hj hq
  · exact match_zero_fix ⟨125, by decide⟩ ⟨33, by decide⟩ p hp j hj hq fz1_125_33 fz2_125_33
  · exact match_zero_fix ⟨126, by decide⟩ ⟨33, by decide⟩ p hp j hj hq fz1_126_33 fz2_126_33
  · exact pair_127_33 p hp hrep j hj hq
  · exact match_zero_fix ⟨128, by decide⟩ ⟨33, by decide⟩ p hp j hj hq fz1_128_33 fz2_128_33
  · exact match_zero_fix ⟨129, by decide⟩ ⟨33, by decide⟩ p hp j hj hq fz1_129_33 fz2_129_33
  · exact match_zero_fix ⟨130, by decide⟩ ⟨33, by decide⟩ p hp j hj hq fz1_130_33 fz2_130_33
  · exact match_zero_fix ⟨131, by decide⟩ ⟨33, by decide⟩ p hp j hj hq fz1_131_33 fz2_131_33
  · exact match_zero_fix ⟨132, by decide⟩ ⟨33, by decide⟩ p hp j hj hq fz1_132_33 fz2_132_33
  · exact match_zero_fix ⟨133, by decide⟩ ⟨33, by decide⟩ p hp j hj hq fz1_133_33 fz2_133_33
  · exact match_zero_fix ⟨134, by decide⟩ ⟨33, by decide⟩ p hp j hj hq fz1_134_33 fz2_134_33
  · exact pair_135_33 p hp hrep j hj hq
  · exact match_zero_fix ⟨136, by decide⟩ ⟨33, by decide⟩ p hp j hj hq fz1_136_33 fz2_136_33
  · exact match_zero_fix ⟨137, by decide⟩ ⟨33, by decide⟩ p hp j hj hq fz1_137_33 fz2_137_33
  · exact pair_138_33 p hp hrep j hj hq
  · exact match_zero_fix ⟨139, by decide⟩ ⟨33, by decide⟩ p hp j hj hq fz1_139_33 fz2_139_33
  · exact match_zero_fix ⟨140, by decide⟩ ⟨33, by decide⟩ p hp j hj hq fz1_140_33 fz2_140_33
  · exact match_zero_fix ⟨141, by decide⟩ ⟨33, by decide⟩ p hp j hj hq fz1_141_33 fz2_141_33
  · exact match_zero_fix ⟨142, by decide⟩ ⟨33, by decide⟩ p hp j hj hq fz1_142_33 fz2_142_33
  · exact pair_143_33 p hp hrep j hj hq
  · exact match_zero_fix ⟨144, by decide⟩ ⟨33, by decide⟩ p hp j hj hq fz1_144_33 fz2_144_33
  · exact match_zero_fix ⟨145, by decide⟩ ⟨33, by decide⟩ p hp j hj hq fz1_145_33 fz2_145_33
  · exact match_zero_fix ⟨146, by decide⟩ ⟨33, by decide⟩ p hp j hj hq fz1_146_33 fz2_146_33
  · exact pair_147_33 p hp hrep j hj hq

theorem master_34 (p : Nat) (hp : p < (Q2.transData.getD 34 []).length)
    (hrep : (Q2.cosetIsRep.getD 34 []).getD p false = true)
    (rK : Fin 148) (j : Nat) (hj : j < (repChars.getD rK.val []).length)
    (hq : (normIsRep.getD rK.val []).getD j false = true) :
    species (Q2.reps (⟨34, by decide⟩ : Fin 148)) (colE2 ⟨34, by decide⟩ p hp)
        (rowE2 rK j hj hq)
      = species (reps (⟨34, by decide⟩ : Fin 148))
        (colE1 ⟨34, by decide⟩ p (transLenTr ⟨34, by decide⟩ p hp)) (rowE1 rK j hj) := by
  rcases rK with ⟨nK, hnK⟩; interval_cases nK
  · exact match_zero_len ⟨0, by decide⟩ ⟨34, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨1, by decide⟩ ⟨34, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨2, by decide⟩ ⟨34, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨3, by decide⟩ ⟨34, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨4, by decide⟩ ⟨34, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨5, by decide⟩ ⟨34, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨6, by decide⟩ ⟨34, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨7, by decide⟩ ⟨34, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨8, by decide⟩ ⟨34, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨9, by decide⟩ ⟨34, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨10, by decide⟩ ⟨34, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨11, by decide⟩ ⟨34, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨12, by decide⟩ ⟨34, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_fix ⟨13, by decide⟩ ⟨34, by decide⟩ p hp j hj hq fz1_13_34 fz2_13_34
  · exact match_zero_fix ⟨14, by decide⟩ ⟨34, by decide⟩ p hp j hj hq fz1_14_34 fz2_14_34
  · exact match_zero_fix ⟨15, by decide⟩ ⟨34, by decide⟩ p hp j hj hq fz1_15_34 fz2_15_34
  · exact match_zero_fix ⟨16, by decide⟩ ⟨34, by decide⟩ p hp j hj hq fz1_16_34 fz2_16_34
  · exact match_zero_fix ⟨17, by decide⟩ ⟨34, by decide⟩ p hp j hj hq fz1_17_34 fz2_17_34
  · exact match_zero_fix ⟨18, by decide⟩ ⟨34, by decide⟩ p hp j hj hq fz1_18_34 fz2_18_34
  · exact match_zero_fix ⟨19, by decide⟩ ⟨34, by decide⟩ p hp j hj hq fz1_19_34 fz2_19_34
  · exact match_zero_fix ⟨20, by decide⟩ ⟨34, by decide⟩ p hp j hj hq fz1_20_34 fz2_20_34
  · exact match_zero_fix ⟨21, by decide⟩ ⟨34, by decide⟩ p hp j hj hq fz1_21_34 fz2_21_34
  · exact match_zero_fix ⟨22, by decide⟩ ⟨34, by decide⟩ p hp j hj hq fz1_22_34 fz2_22_34
  · exact match_zero_fix ⟨23, by decide⟩ ⟨34, by decide⟩ p hp j hj hq fz1_23_34 fz2_23_34
  · exact match_zero_fix ⟨24, by decide⟩ ⟨34, by decide⟩ p hp j hj hq fz1_24_34 fz2_24_34
  · exact match_zero_fix ⟨25, by decide⟩ ⟨34, by decide⟩ p hp j hj hq fz1_25_34 fz2_25_34
  · exact match_zero_fix ⟨26, by decide⟩ ⟨34, by decide⟩ p hp j hj hq fz1_26_34 fz2_26_34
  · exact match_zero_fix ⟨27, by decide⟩ ⟨34, by decide⟩ p hp j hj hq fz1_27_34 fz2_27_34
  · exact match_zero_fix ⟨28, by decide⟩ ⟨34, by decide⟩ p hp j hj hq fz1_28_34 fz2_28_34
  · exact match_zero_fix ⟨29, by decide⟩ ⟨34, by decide⟩ p hp j hj hq fz1_29_34 fz2_29_34
  · exact match_zero_fix ⟨30, by decide⟩ ⟨34, by decide⟩ p hp j hj hq fz1_30_34 fz2_30_34
  · exact match_zero_fix ⟨31, by decide⟩ ⟨34, by decide⟩ p hp j hj hq fz1_31_34 fz2_31_34
  · exact match_zero_fix ⟨32, by decide⟩ ⟨34, by decide⟩ p hp j hj hq fz1_32_34 fz2_32_34
  · exact match_zero_fix ⟨33, by decide⟩ ⟨34, by decide⟩ p hp j hj hq fz1_33_34 fz2_33_34
  · exact pair_34_34 p hp hrep j hj hq
  · exact match_zero_fix ⟨35, by decide⟩ ⟨34, by decide⟩ p hp j hj hq fz1_35_34 fz2_35_34
  · exact match_zero_fix ⟨36, by decide⟩ ⟨34, by decide⟩ p hp j hj hq fz1_36_34 fz2_36_34
  · exact match_zero_fix ⟨37, by decide⟩ ⟨34, by decide⟩ p hp j hj hq fz1_37_34 fz2_37_34
  · exact match_zero_fix ⟨38, by decide⟩ ⟨34, by decide⟩ p hp j hj hq fz1_38_34 fz2_38_34
  · exact match_zero_fix ⟨39, by decide⟩ ⟨34, by decide⟩ p hp j hj hq fz1_39_34 fz2_39_34
  · exact match_zero_fix ⟨40, by decide⟩ ⟨34, by decide⟩ p hp j hj hq fz1_40_34 fz2_40_34
  · exact match_zero_fix ⟨41, by decide⟩ ⟨34, by decide⟩ p hp j hj hq fz1_41_34 fz2_41_34
  · exact match_zero_fix ⟨42, by decide⟩ ⟨34, by decide⟩ p hp j hj hq fz1_42_34 fz2_42_34
  · exact match_zero_fix ⟨43, by decide⟩ ⟨34, by decide⟩ p hp j hj hq fz1_43_34 fz2_43_34
  · exact match_zero_fix ⟨44, by decide⟩ ⟨34, by decide⟩ p hp j hj hq fz1_44_34 fz2_44_34
  · exact match_zero_fix ⟨45, by decide⟩ ⟨34, by decide⟩ p hp j hj hq fz1_45_34 fz2_45_34
  · exact match_zero_fix ⟨46, by decide⟩ ⟨34, by decide⟩ p hp j hj hq fz1_46_34 fz2_46_34
  · exact match_zero_fix ⟨47, by decide⟩ ⟨34, by decide⟩ p hp j hj hq fz1_47_34 fz2_47_34
  · exact match_zero_fix ⟨48, by decide⟩ ⟨34, by decide⟩ p hp j hj hq fz1_48_34 fz2_48_34
  · exact match_zero_fix ⟨49, by decide⟩ ⟨34, by decide⟩ p hp j hj hq fz1_49_34 fz2_49_34
  · exact match_zero_fix ⟨50, by decide⟩ ⟨34, by decide⟩ p hp j hj hq fz1_50_34 fz2_50_34
  · exact match_zero_fix ⟨51, by decide⟩ ⟨34, by decide⟩ p hp j hj hq fz1_51_34 fz2_51_34
  · exact match_zero_fix ⟨52, by decide⟩ ⟨34, by decide⟩ p hp j hj hq fz1_52_34 fz2_52_34
  · exact match_zero_fix ⟨53, by decide⟩ ⟨34, by decide⟩ p hp j hj hq fz1_53_34 fz2_53_34
  · exact match_zero_fix ⟨54, by decide⟩ ⟨34, by decide⟩ p hp j hj hq fz1_54_34 fz2_54_34
  · exact match_zero_fix ⟨55, by decide⟩ ⟨34, by decide⟩ p hp j hj hq fz1_55_34 fz2_55_34
  · exact match_zero_fix ⟨56, by decide⟩ ⟨34, by decide⟩ p hp j hj hq fz1_56_34 fz2_56_34
  · exact match_zero_fix ⟨57, by decide⟩ ⟨34, by decide⟩ p hp j hj hq fz1_57_34 fz2_57_34
  · exact match_zero_fix ⟨58, by decide⟩ ⟨34, by decide⟩ p hp j hj hq fz1_58_34 fz2_58_34
  · exact match_zero_fix ⟨59, by decide⟩ ⟨34, by decide⟩ p hp j hj hq fz1_59_34 fz2_59_34
  · exact pair_60_34 p hp hrep j hj hq
  · exact pair_61_34 p hp hrep j hj hq
  · exact pair_62_34 p hp hrep j hj hq
  · exact pair_63_34 p hp hrep j hj hq
  · exact pair_64_34 p hp hrep j hj hq
  · exact match_zero_fix ⟨65, by decide⟩ ⟨34, by decide⟩ p hp j hj hq fz1_65_34 fz2_65_34
  · exact match_zero_fix ⟨66, by decide⟩ ⟨34, by decide⟩ p hp j hj hq fz1_66_34 fz2_66_34
  · exact match_zero_fix ⟨67, by decide⟩ ⟨34, by decide⟩ p hp j hj hq fz1_67_34 fz2_67_34
  · exact match_zero_fix ⟨68, by decide⟩ ⟨34, by decide⟩ p hp j hj hq fz1_68_34 fz2_68_34
  · exact match_zero_fix ⟨69, by decide⟩ ⟨34, by decide⟩ p hp j hj hq fz1_69_34 fz2_69_34
  · exact match_zero_fix ⟨70, by decide⟩ ⟨34, by decide⟩ p hp j hj hq fz1_70_34 fz2_70_34
  · exact match_zero_fix ⟨71, by decide⟩ ⟨34, by decide⟩ p hp j hj hq fz1_71_34 fz2_71_34
  · exact match_zero_fix ⟨72, by decide⟩ ⟨34, by decide⟩ p hp j hj hq fz1_72_34 fz2_72_34
  · exact match_zero_fix ⟨73, by decide⟩ ⟨34, by decide⟩ p hp j hj hq fz1_73_34 fz2_73_34
  · exact match_zero_fix ⟨74, by decide⟩ ⟨34, by decide⟩ p hp j hj hq fz1_74_34 fz2_74_34
  · exact match_zero_fix ⟨75, by decide⟩ ⟨34, by decide⟩ p hp j hj hq fz1_75_34 fz2_75_34
  · exact match_zero_fix ⟨76, by decide⟩ ⟨34, by decide⟩ p hp j hj hq fz1_76_34 fz2_76_34
  · exact match_zero_fix ⟨77, by decide⟩ ⟨34, by decide⟩ p hp j hj hq fz1_77_34 fz2_77_34
  · exact match_zero_fix ⟨78, by decide⟩ ⟨34, by decide⟩ p hp j hj hq fz1_78_34 fz2_78_34
  · exact match_zero_fix ⟨79, by decide⟩ ⟨34, by decide⟩ p hp j hj hq fz1_79_34 fz2_79_34
  · exact match_zero_fix ⟨80, by decide⟩ ⟨34, by decide⟩ p hp j hj hq fz1_80_34 fz2_80_34
  · exact match_zero_fix ⟨81, by decide⟩ ⟨34, by decide⟩ p hp j hj hq fz1_81_34 fz2_81_34
  · exact match_zero_fix ⟨82, by decide⟩ ⟨34, by decide⟩ p hp j hj hq fz1_82_34 fz2_82_34
  · exact match_zero_fix ⟨83, by decide⟩ ⟨34, by decide⟩ p hp j hj hq fz1_83_34 fz2_83_34
  · exact match_zero_fix ⟨84, by decide⟩ ⟨34, by decide⟩ p hp j hj hq fz1_84_34 fz2_84_34
  · exact match_zero_fix ⟨85, by decide⟩ ⟨34, by decide⟩ p hp j hj hq fz1_85_34 fz2_85_34
  · exact match_zero_fix ⟨86, by decide⟩ ⟨34, by decide⟩ p hp j hj hq fz1_86_34 fz2_86_34
  · exact match_zero_fix ⟨87, by decide⟩ ⟨34, by decide⟩ p hp j hj hq fz1_87_34 fz2_87_34
  · exact match_zero_fix ⟨88, by decide⟩ ⟨34, by decide⟩ p hp j hj hq fz1_88_34 fz2_88_34
  · exact match_zero_fix ⟨89, by decide⟩ ⟨34, by decide⟩ p hp j hj hq fz1_89_34 fz2_89_34
  · exact match_zero_fix ⟨90, by decide⟩ ⟨34, by decide⟩ p hp j hj hq fz1_90_34 fz2_90_34
  · exact match_zero_fix ⟨91, by decide⟩ ⟨34, by decide⟩ p hp j hj hq fz1_91_34 fz2_91_34
  · exact match_zero_fix ⟨92, by decide⟩ ⟨34, by decide⟩ p hp j hj hq fz1_92_34 fz2_92_34
  · exact match_zero_fix ⟨93, by decide⟩ ⟨34, by decide⟩ p hp j hj hq fz1_93_34 fz2_93_34
  · exact match_zero_fix ⟨94, by decide⟩ ⟨34, by decide⟩ p hp j hj hq fz1_94_34 fz2_94_34
  · exact match_zero_fix ⟨95, by decide⟩ ⟨34, by decide⟩ p hp j hj hq fz1_95_34 fz2_95_34
  · exact pair_96_34 p hp hrep j hj hq
  · exact match_zero_fix ⟨97, by decide⟩ ⟨34, by decide⟩ p hp j hj hq fz1_97_34 fz2_97_34
  · exact match_zero_fix ⟨98, by decide⟩ ⟨34, by decide⟩ p hp j hj hq fz1_98_34 fz2_98_34
  · exact match_zero_fix ⟨99, by decide⟩ ⟨34, by decide⟩ p hp j hj hq fz1_99_34 fz2_99_34
  · exact match_zero_fix ⟨100, by decide⟩ ⟨34, by decide⟩ p hp j hj hq fz1_100_34 fz2_100_34
  · exact match_zero_fix ⟨101, by decide⟩ ⟨34, by decide⟩ p hp j hj hq fz1_101_34 fz2_101_34
  · exact match_zero_fix ⟨102, by decide⟩ ⟨34, by decide⟩ p hp j hj hq fz1_102_34 fz2_102_34
  · exact match_zero_fix ⟨103, by decide⟩ ⟨34, by decide⟩ p hp j hj hq fz1_103_34 fz2_103_34
  · exact match_zero_fix ⟨104, by decide⟩ ⟨34, by decide⟩ p hp j hj hq fz1_104_34 fz2_104_34
  · exact match_zero_fix ⟨105, by decide⟩ ⟨34, by decide⟩ p hp j hj hq fz1_105_34 fz2_105_34
  · exact match_zero_fix ⟨106, by decide⟩ ⟨34, by decide⟩ p hp j hj hq fz1_106_34 fz2_106_34
  · exact match_zero_fix ⟨107, by decide⟩ ⟨34, by decide⟩ p hp j hj hq fz1_107_34 fz2_107_34
  · exact match_zero_fix ⟨108, by decide⟩ ⟨34, by decide⟩ p hp j hj hq fz1_108_34 fz2_108_34
  · exact match_zero_fix ⟨109, by decide⟩ ⟨34, by decide⟩ p hp j hj hq fz1_109_34 fz2_109_34
  · exact match_zero_fix ⟨110, by decide⟩ ⟨34, by decide⟩ p hp j hj hq fz1_110_34 fz2_110_34
  · exact match_zero_fix ⟨111, by decide⟩ ⟨34, by decide⟩ p hp j hj hq fz1_111_34 fz2_111_34
  · exact match_zero_fix ⟨112, by decide⟩ ⟨34, by decide⟩ p hp j hj hq fz1_112_34 fz2_112_34
  · exact match_zero_fix ⟨113, by decide⟩ ⟨34, by decide⟩ p hp j hj hq fz1_113_34 fz2_113_34
  · exact match_zero_fix ⟨114, by decide⟩ ⟨34, by decide⟩ p hp j hj hq fz1_114_34 fz2_114_34
  · exact match_zero_fix ⟨115, by decide⟩ ⟨34, by decide⟩ p hp j hj hq fz1_115_34 fz2_115_34
  · exact match_zero_fix ⟨116, by decide⟩ ⟨34, by decide⟩ p hp j hj hq fz1_116_34 fz2_116_34
  · exact pair_117_34 p hp hrep j hj hq
  · exact match_zero_fix ⟨118, by decide⟩ ⟨34, by decide⟩ p hp j hj hq fz1_118_34 fz2_118_34
  · exact match_zero_fix ⟨119, by decide⟩ ⟨34, by decide⟩ p hp j hj hq fz1_119_34 fz2_119_34
  · exact match_zero_fix ⟨120, by decide⟩ ⟨34, by decide⟩ p hp j hj hq fz1_120_34 fz2_120_34
  · exact match_zero_fix ⟨121, by decide⟩ ⟨34, by decide⟩ p hp j hj hq fz1_121_34 fz2_121_34
  · exact match_zero_fix ⟨122, by decide⟩ ⟨34, by decide⟩ p hp j hj hq fz1_122_34 fz2_122_34
  · exact match_zero_fix ⟨123, by decide⟩ ⟨34, by decide⟩ p hp j hj hq fz1_123_34 fz2_123_34
  · exact match_zero_fix ⟨124, by decide⟩ ⟨34, by decide⟩ p hp j hj hq fz1_124_34 fz2_124_34
  · exact pair_125_34 p hp hrep j hj hq
  · exact match_zero_fix ⟨126, by decide⟩ ⟨34, by decide⟩ p hp j hj hq fz1_126_34 fz2_126_34
  · exact match_zero_fix ⟨127, by decide⟩ ⟨34, by decide⟩ p hp j hj hq fz1_127_34 fz2_127_34
  · exact pair_128_34 p hp hrep j hj hq
  · exact match_zero_fix ⟨129, by decide⟩ ⟨34, by decide⟩ p hp j hj hq fz1_129_34 fz2_129_34
  · exact match_zero_fix ⟨130, by decide⟩ ⟨34, by decide⟩ p hp j hj hq fz1_130_34 fz2_130_34
  · exact pair_131_34 p hp hrep j hj hq
  · exact match_zero_fix ⟨132, by decide⟩ ⟨34, by decide⟩ p hp j hj hq fz1_132_34 fz2_132_34
  · exact match_zero_fix ⟨133, by decide⟩ ⟨34, by decide⟩ p hp j hj hq fz1_133_34 fz2_133_34
  · exact match_zero_fix ⟨134, by decide⟩ ⟨34, by decide⟩ p hp j hj hq fz1_134_34 fz2_134_34
  · exact match_zero_fix ⟨135, by decide⟩ ⟨34, by decide⟩ p hp j hj hq fz1_135_34 fz2_135_34
  · exact match_zero_fix ⟨136, by decide⟩ ⟨34, by decide⟩ p hp j hj hq fz1_136_34 fz2_136_34
  · exact match_zero_fix ⟨137, by decide⟩ ⟨34, by decide⟩ p hp j hj hq fz1_137_34 fz2_137_34
  · exact match_zero_fix ⟨138, by decide⟩ ⟨34, by decide⟩ p hp j hj hq fz1_138_34 fz2_138_34
  · exact pair_139_34 p hp hrep j hj hq
  · exact match_zero_fix ⟨140, by decide⟩ ⟨34, by decide⟩ p hp j hj hq fz1_140_34 fz2_140_34
  · exact match_zero_fix ⟨141, by decide⟩ ⟨34, by decide⟩ p hp j hj hq fz1_141_34 fz2_141_34
  · exact match_zero_fix ⟨142, by decide⟩ ⟨34, by decide⟩ p hp j hj hq fz1_142_34 fz2_142_34
  · exact pair_143_34 p hp hrep j hj hq
  · exact match_zero_fix ⟨144, by decide⟩ ⟨34, by decide⟩ p hp j hj hq fz1_144_34 fz2_144_34
  · exact match_zero_fix ⟨145, by decide⟩ ⟨34, by decide⟩ p hp j hj hq fz1_145_34 fz2_145_34
  · exact match_zero_fix ⟨146, by decide⟩ ⟨34, by decide⟩ p hp j hj hq fz1_146_34 fz2_146_34
  · exact pair_147_34 p hp hrep j hj hq

theorem master_35 (p : Nat) (hp : p < (Q2.transData.getD 35 []).length)
    (hrep : (Q2.cosetIsRep.getD 35 []).getD p false = true)
    (rK : Fin 148) (j : Nat) (hj : j < (repChars.getD rK.val []).length)
    (hq : (normIsRep.getD rK.val []).getD j false = true) :
    species (Q2.reps (⟨35, by decide⟩ : Fin 148)) (colE2 ⟨35, by decide⟩ p hp)
        (rowE2 rK j hj hq)
      = species (reps (⟨35, by decide⟩ : Fin 148))
        (colE1 ⟨35, by decide⟩ p (transLenTr ⟨35, by decide⟩ p hp)) (rowE1 rK j hj) := by
  rcases rK with ⟨nK, hnK⟩; interval_cases nK
  · exact match_zero_len ⟨0, by decide⟩ ⟨35, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨1, by decide⟩ ⟨35, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨2, by decide⟩ ⟨35, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨3, by decide⟩ ⟨35, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨4, by decide⟩ ⟨35, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨5, by decide⟩ ⟨35, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨6, by decide⟩ ⟨35, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨7, by decide⟩ ⟨35, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨8, by decide⟩ ⟨35, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨9, by decide⟩ ⟨35, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨10, by decide⟩ ⟨35, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨11, by decide⟩ ⟨35, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨12, by decide⟩ ⟨35, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_fix ⟨13, by decide⟩ ⟨35, by decide⟩ p hp j hj hq fz1_13_35 fz2_13_35
  · exact match_zero_fix ⟨14, by decide⟩ ⟨35, by decide⟩ p hp j hj hq fz1_14_35 fz2_14_35
  · exact match_zero_fix ⟨15, by decide⟩ ⟨35, by decide⟩ p hp j hj hq fz1_15_35 fz2_15_35
  · exact match_zero_fix ⟨16, by decide⟩ ⟨35, by decide⟩ p hp j hj hq fz1_16_35 fz2_16_35
  · exact match_zero_fix ⟨17, by decide⟩ ⟨35, by decide⟩ p hp j hj hq fz1_17_35 fz2_17_35
  · exact match_zero_fix ⟨18, by decide⟩ ⟨35, by decide⟩ p hp j hj hq fz1_18_35 fz2_18_35
  · exact match_zero_fix ⟨19, by decide⟩ ⟨35, by decide⟩ p hp j hj hq fz1_19_35 fz2_19_35
  · exact match_zero_fix ⟨20, by decide⟩ ⟨35, by decide⟩ p hp j hj hq fz1_20_35 fz2_20_35
  · exact match_zero_fix ⟨21, by decide⟩ ⟨35, by decide⟩ p hp j hj hq fz1_21_35 fz2_21_35
  · exact match_zero_fix ⟨22, by decide⟩ ⟨35, by decide⟩ p hp j hj hq fz1_22_35 fz2_22_35
  · exact match_zero_fix ⟨23, by decide⟩ ⟨35, by decide⟩ p hp j hj hq fz1_23_35 fz2_23_35
  · exact match_zero_fix ⟨24, by decide⟩ ⟨35, by decide⟩ p hp j hj hq fz1_24_35 fz2_24_35
  · exact match_zero_fix ⟨25, by decide⟩ ⟨35, by decide⟩ p hp j hj hq fz1_25_35 fz2_25_35
  · exact match_zero_fix ⟨26, by decide⟩ ⟨35, by decide⟩ p hp j hj hq fz1_26_35 fz2_26_35
  · exact match_zero_fix ⟨27, by decide⟩ ⟨35, by decide⟩ p hp j hj hq fz1_27_35 fz2_27_35
  · exact match_zero_fix ⟨28, by decide⟩ ⟨35, by decide⟩ p hp j hj hq fz1_28_35 fz2_28_35
  · exact match_zero_fix ⟨29, by decide⟩ ⟨35, by decide⟩ p hp j hj hq fz1_29_35 fz2_29_35
  · exact match_zero_fix ⟨30, by decide⟩ ⟨35, by decide⟩ p hp j hj hq fz1_30_35 fz2_30_35
  · exact match_zero_fix ⟨31, by decide⟩ ⟨35, by decide⟩ p hp j hj hq fz1_31_35 fz2_31_35
  · exact match_zero_fix ⟨32, by decide⟩ ⟨35, by decide⟩ p hp j hj hq fz1_32_35 fz2_32_35
  · exact match_zero_fix ⟨33, by decide⟩ ⟨35, by decide⟩ p hp j hj hq fz1_33_35 fz2_33_35
  · exact match_zero_fix ⟨34, by decide⟩ ⟨35, by decide⟩ p hp j hj hq fz1_34_35 fz2_34_35
  · exact pair_35_35 p hp hrep j hj hq
  · exact match_zero_fix ⟨36, by decide⟩ ⟨35, by decide⟩ p hp j hj hq fz1_36_35 fz2_36_35
  · exact match_zero_fix ⟨37, by decide⟩ ⟨35, by decide⟩ p hp j hj hq fz1_37_35 fz2_37_35
  · exact match_zero_fix ⟨38, by decide⟩ ⟨35, by decide⟩ p hp j hj hq fz1_38_35 fz2_38_35
  · exact match_zero_fix ⟨39, by decide⟩ ⟨35, by decide⟩ p hp j hj hq fz1_39_35 fz2_39_35
  · exact match_zero_fix ⟨40, by decide⟩ ⟨35, by decide⟩ p hp j hj hq fz1_40_35 fz2_40_35
  · exact match_zero_fix ⟨41, by decide⟩ ⟨35, by decide⟩ p hp j hj hq fz1_41_35 fz2_41_35
  · exact match_zero_fix ⟨42, by decide⟩ ⟨35, by decide⟩ p hp j hj hq fz1_42_35 fz2_42_35
  · exact match_zero_fix ⟨43, by decide⟩ ⟨35, by decide⟩ p hp j hj hq fz1_43_35 fz2_43_35
  · exact match_zero_fix ⟨44, by decide⟩ ⟨35, by decide⟩ p hp j hj hq fz1_44_35 fz2_44_35
  · exact match_zero_fix ⟨45, by decide⟩ ⟨35, by decide⟩ p hp j hj hq fz1_45_35 fz2_45_35
  · exact match_zero_fix ⟨46, by decide⟩ ⟨35, by decide⟩ p hp j hj hq fz1_46_35 fz2_46_35
  · exact match_zero_fix ⟨47, by decide⟩ ⟨35, by decide⟩ p hp j hj hq fz1_47_35 fz2_47_35
  · exact match_zero_fix ⟨48, by decide⟩ ⟨35, by decide⟩ p hp j hj hq fz1_48_35 fz2_48_35
  · exact match_zero_fix ⟨49, by decide⟩ ⟨35, by decide⟩ p hp j hj hq fz1_49_35 fz2_49_35
  · exact match_zero_fix ⟨50, by decide⟩ ⟨35, by decide⟩ p hp j hj hq fz1_50_35 fz2_50_35
  · exact match_zero_fix ⟨51, by decide⟩ ⟨35, by decide⟩ p hp j hj hq fz1_51_35 fz2_51_35
  · exact match_zero_fix ⟨52, by decide⟩ ⟨35, by decide⟩ p hp j hj hq fz1_52_35 fz2_52_35
  · exact match_zero_fix ⟨53, by decide⟩ ⟨35, by decide⟩ p hp j hj hq fz1_53_35 fz2_53_35
  · exact match_zero_fix ⟨54, by decide⟩ ⟨35, by decide⟩ p hp j hj hq fz1_54_35 fz2_54_35
  · exact match_zero_fix ⟨55, by decide⟩ ⟨35, by decide⟩ p hp j hj hq fz1_55_35 fz2_55_35
  · exact match_zero_fix ⟨56, by decide⟩ ⟨35, by decide⟩ p hp j hj hq fz1_56_35 fz2_56_35
  · exact match_zero_fix ⟨57, by decide⟩ ⟨35, by decide⟩ p hp j hj hq fz1_57_35 fz2_57_35
  · exact match_zero_fix ⟨58, by decide⟩ ⟨35, by decide⟩ p hp j hj hq fz1_58_35 fz2_58_35
  · exact match_zero_fix ⟨59, by decide⟩ ⟨35, by decide⟩ p hp j hj hq fz1_59_35 fz2_59_35
  · exact match_zero_fix ⟨60, by decide⟩ ⟨35, by decide⟩ p hp j hj hq fz1_60_35 fz2_60_35
  · exact match_zero_fix ⟨61, by decide⟩ ⟨35, by decide⟩ p hp j hj hq fz1_61_35 fz2_61_35
  · exact match_zero_fix ⟨62, by decide⟩ ⟨35, by decide⟩ p hp j hj hq fz1_62_35 fz2_62_35
  · exact match_zero_fix ⟨63, by decide⟩ ⟨35, by decide⟩ p hp j hj hq fz1_63_35 fz2_63_35
  · exact match_zero_fix ⟨64, by decide⟩ ⟨35, by decide⟩ p hp j hj hq fz1_64_35 fz2_64_35
  · exact pair_65_35 p hp hrep j hj hq
  · exact pair_66_35 p hp hrep j hj hq
  · exact pair_67_35 p hp hrep j hj hq
  · exact pair_68_35 p hp hrep j hj hq
  · exact pair_69_35 p hp hrep j hj hq
  · exact match_zero_fix ⟨70, by decide⟩ ⟨35, by decide⟩ p hp j hj hq fz1_70_35 fz2_70_35
  · exact match_zero_fix ⟨71, by decide⟩ ⟨35, by decide⟩ p hp j hj hq fz1_71_35 fz2_71_35
  · exact match_zero_fix ⟨72, by decide⟩ ⟨35, by decide⟩ p hp j hj hq fz1_72_35 fz2_72_35
  · exact match_zero_fix ⟨73, by decide⟩ ⟨35, by decide⟩ p hp j hj hq fz1_73_35 fz2_73_35
  · exact match_zero_fix ⟨74, by decide⟩ ⟨35, by decide⟩ p hp j hj hq fz1_74_35 fz2_74_35
  · exact match_zero_fix ⟨75, by decide⟩ ⟨35, by decide⟩ p hp j hj hq fz1_75_35 fz2_75_35
  · exact match_zero_fix ⟨76, by decide⟩ ⟨35, by decide⟩ p hp j hj hq fz1_76_35 fz2_76_35
  · exact match_zero_fix ⟨77, by decide⟩ ⟨35, by decide⟩ p hp j hj hq fz1_77_35 fz2_77_35
  · exact match_zero_fix ⟨78, by decide⟩ ⟨35, by decide⟩ p hp j hj hq fz1_78_35 fz2_78_35
  · exact match_zero_fix ⟨79, by decide⟩ ⟨35, by decide⟩ p hp j hj hq fz1_79_35 fz2_79_35
  · exact match_zero_fix ⟨80, by decide⟩ ⟨35, by decide⟩ p hp j hj hq fz1_80_35 fz2_80_35
  · exact match_zero_fix ⟨81, by decide⟩ ⟨35, by decide⟩ p hp j hj hq fz1_81_35 fz2_81_35
  · exact match_zero_fix ⟨82, by decide⟩ ⟨35, by decide⟩ p hp j hj hq fz1_82_35 fz2_82_35
  · exact match_zero_fix ⟨83, by decide⟩ ⟨35, by decide⟩ p hp j hj hq fz1_83_35 fz2_83_35
  · exact match_zero_fix ⟨84, by decide⟩ ⟨35, by decide⟩ p hp j hj hq fz1_84_35 fz2_84_35
  · exact match_zero_fix ⟨85, by decide⟩ ⟨35, by decide⟩ p hp j hj hq fz1_85_35 fz2_85_35
  · exact match_zero_fix ⟨86, by decide⟩ ⟨35, by decide⟩ p hp j hj hq fz1_86_35 fz2_86_35
  · exact match_zero_fix ⟨87, by decide⟩ ⟨35, by decide⟩ p hp j hj hq fz1_87_35 fz2_87_35
  · exact match_zero_fix ⟨88, by decide⟩ ⟨35, by decide⟩ p hp j hj hq fz1_88_35 fz2_88_35
  · exact match_zero_fix ⟨89, by decide⟩ ⟨35, by decide⟩ p hp j hj hq fz1_89_35 fz2_89_35
  · exact match_zero_fix ⟨90, by decide⟩ ⟨35, by decide⟩ p hp j hj hq fz1_90_35 fz2_90_35
  · exact match_zero_fix ⟨91, by decide⟩ ⟨35, by decide⟩ p hp j hj hq fz1_91_35 fz2_91_35
  · exact match_zero_fix ⟨92, by decide⟩ ⟨35, by decide⟩ p hp j hj hq fz1_92_35 fz2_92_35
  · exact match_zero_fix ⟨93, by decide⟩ ⟨35, by decide⟩ p hp j hj hq fz1_93_35 fz2_93_35
  · exact match_zero_fix ⟨94, by decide⟩ ⟨35, by decide⟩ p hp j hj hq fz1_94_35 fz2_94_35
  · exact match_zero_fix ⟨95, by decide⟩ ⟨35, by decide⟩ p hp j hj hq fz1_95_35 fz2_95_35
  · exact match_zero_fix ⟨96, by decide⟩ ⟨35, by decide⟩ p hp j hj hq fz1_96_35 fz2_96_35
  · exact pair_97_35 p hp hrep j hj hq
  · exact match_zero_fix ⟨98, by decide⟩ ⟨35, by decide⟩ p hp j hj hq fz1_98_35 fz2_98_35
  · exact match_zero_fix ⟨99, by decide⟩ ⟨35, by decide⟩ p hp j hj hq fz1_99_35 fz2_99_35
  · exact match_zero_fix ⟨100, by decide⟩ ⟨35, by decide⟩ p hp j hj hq fz1_100_35 fz2_100_35
  · exact match_zero_fix ⟨101, by decide⟩ ⟨35, by decide⟩ p hp j hj hq fz1_101_35 fz2_101_35
  · exact match_zero_fix ⟨102, by decide⟩ ⟨35, by decide⟩ p hp j hj hq fz1_102_35 fz2_102_35
  · exact match_zero_fix ⟨103, by decide⟩ ⟨35, by decide⟩ p hp j hj hq fz1_103_35 fz2_103_35
  · exact match_zero_fix ⟨104, by decide⟩ ⟨35, by decide⟩ p hp j hj hq fz1_104_35 fz2_104_35
  · exact match_zero_fix ⟨105, by decide⟩ ⟨35, by decide⟩ p hp j hj hq fz1_105_35 fz2_105_35
  · exact match_zero_fix ⟨106, by decide⟩ ⟨35, by decide⟩ p hp j hj hq fz1_106_35 fz2_106_35
  · exact match_zero_fix ⟨107, by decide⟩ ⟨35, by decide⟩ p hp j hj hq fz1_107_35 fz2_107_35
  · exact match_zero_fix ⟨108, by decide⟩ ⟨35, by decide⟩ p hp j hj hq fz1_108_35 fz2_108_35
  · exact match_zero_fix ⟨109, by decide⟩ ⟨35, by decide⟩ p hp j hj hq fz1_109_35 fz2_109_35
  · exact match_zero_fix ⟨110, by decide⟩ ⟨35, by decide⟩ p hp j hj hq fz1_110_35 fz2_110_35
  · exact match_zero_fix ⟨111, by decide⟩ ⟨35, by decide⟩ p hp j hj hq fz1_111_35 fz2_111_35
  · exact match_zero_fix ⟨112, by decide⟩ ⟨35, by decide⟩ p hp j hj hq fz1_112_35 fz2_112_35
  · exact match_zero_fix ⟨113, by decide⟩ ⟨35, by decide⟩ p hp j hj hq fz1_113_35 fz2_113_35
  · exact match_zero_fix ⟨114, by decide⟩ ⟨35, by decide⟩ p hp j hj hq fz1_114_35 fz2_114_35
  · exact match_zero_fix ⟨115, by decide⟩ ⟨35, by decide⟩ p hp j hj hq fz1_115_35 fz2_115_35
  · exact match_zero_fix ⟨116, by decide⟩ ⟨35, by decide⟩ p hp j hj hq fz1_116_35 fz2_116_35
  · exact match_zero_fix ⟨117, by decide⟩ ⟨35, by decide⟩ p hp j hj hq fz1_117_35 fz2_117_35
  · exact pair_118_35 p hp hrep j hj hq
  · exact match_zero_fix ⟨119, by decide⟩ ⟨35, by decide⟩ p hp j hj hq fz1_119_35 fz2_119_35
  · exact match_zero_fix ⟨120, by decide⟩ ⟨35, by decide⟩ p hp j hj hq fz1_120_35 fz2_120_35
  · exact pair_121_35 p hp hrep j hj hq
  · exact match_zero_fix ⟨122, by decide⟩ ⟨35, by decide⟩ p hp j hj hq fz1_122_35 fz2_122_35
  · exact match_zero_fix ⟨123, by decide⟩ ⟨35, by decide⟩ p hp j hj hq fz1_123_35 fz2_123_35
  · exact match_zero_fix ⟨124, by decide⟩ ⟨35, by decide⟩ p hp j hj hq fz1_124_35 fz2_124_35
  · exact match_zero_fix ⟨125, by decide⟩ ⟨35, by decide⟩ p hp j hj hq fz1_125_35 fz2_125_35
  · exact match_zero_fix ⟨126, by decide⟩ ⟨35, by decide⟩ p hp j hj hq fz1_126_35 fz2_126_35
  · exact match_zero_fix ⟨127, by decide⟩ ⟨35, by decide⟩ p hp j hj hq fz1_127_35 fz2_127_35
  · exact match_zero_fix ⟨128, by decide⟩ ⟨35, by decide⟩ p hp j hj hq fz1_128_35 fz2_128_35
  · exact pair_129_35 p hp hrep j hj hq
  · exact match_zero_fix ⟨130, by decide⟩ ⟨35, by decide⟩ p hp j hj hq fz1_130_35 fz2_130_35
  · exact match_zero_fix ⟨131, by decide⟩ ⟨35, by decide⟩ p hp j hj hq fz1_131_35 fz2_131_35
  · exact pair_132_35 p hp hrep j hj hq
  · exact match_zero_fix ⟨133, by decide⟩ ⟨35, by decide⟩ p hp j hj hq fz1_133_35 fz2_133_35
  · exact match_zero_fix ⟨134, by decide⟩ ⟨35, by decide⟩ p hp j hj hq fz1_134_35 fz2_134_35
  · exact match_zero_fix ⟨135, by decide⟩ ⟨35, by decide⟩ p hp j hj hq fz1_135_35 fz2_135_35
  · exact match_zero_fix ⟨136, by decide⟩ ⟨35, by decide⟩ p hp j hj hq fz1_136_35 fz2_136_35
  · exact match_zero_fix ⟨137, by decide⟩ ⟨35, by decide⟩ p hp j hj hq fz1_137_35 fz2_137_35
  · exact match_zero_fix ⟨138, by decide⟩ ⟨35, by decide⟩ p hp j hj hq fz1_138_35 fz2_138_35
  · exact match_zero_fix ⟨139, by decide⟩ ⟨35, by decide⟩ p hp j hj hq fz1_139_35 fz2_139_35
  · exact pair_140_35 p hp hrep j hj hq
  · exact match_zero_fix ⟨141, by decide⟩ ⟨35, by decide⟩ p hp j hj hq fz1_141_35 fz2_141_35
  · exact match_zero_fix ⟨142, by decide⟩ ⟨35, by decide⟩ p hp j hj hq fz1_142_35 fz2_142_35
  · exact pair_143_35 p hp hrep j hj hq
  · exact match_zero_fix ⟨144, by decide⟩ ⟨35, by decide⟩ p hp j hj hq fz1_144_35 fz2_144_35
  · exact match_zero_fix ⟨145, by decide⟩ ⟨35, by decide⟩ p hp j hj hq fz1_145_35 fz2_145_35
  · exact match_zero_fix ⟨146, by decide⟩ ⟨35, by decide⟩ p hp j hj hq fz1_146_35 fz2_146_35
  · exact pair_147_35 p hp hrep j hj hq

theorem master_36 (p : Nat) (hp : p < (Q2.transData.getD 36 []).length)
    (hrep : (Q2.cosetIsRep.getD 36 []).getD p false = true)
    (rK : Fin 148) (j : Nat) (hj : j < (repChars.getD rK.val []).length)
    (hq : (normIsRep.getD rK.val []).getD j false = true) :
    species (Q2.reps (⟨36, by decide⟩ : Fin 148)) (colE2 ⟨36, by decide⟩ p hp)
        (rowE2 rK j hj hq)
      = species (reps (⟨36, by decide⟩ : Fin 148))
        (colE1 ⟨36, by decide⟩ p (transLenTr ⟨36, by decide⟩ p hp)) (rowE1 rK j hj) := by
  rcases rK with ⟨nK, hnK⟩; interval_cases nK
  · exact match_zero_len ⟨0, by decide⟩ ⟨36, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨1, by decide⟩ ⟨36, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨2, by decide⟩ ⟨36, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨3, by decide⟩ ⟨36, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨4, by decide⟩ ⟨36, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨5, by decide⟩ ⟨36, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨6, by decide⟩ ⟨36, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨7, by decide⟩ ⟨36, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨8, by decide⟩ ⟨36, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨9, by decide⟩ ⟨36, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨10, by decide⟩ ⟨36, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨11, by decide⟩ ⟨36, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨12, by decide⟩ ⟨36, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_fix ⟨13, by decide⟩ ⟨36, by decide⟩ p hp j hj hq fz1_13_36 fz2_13_36
  · exact match_zero_fix ⟨14, by decide⟩ ⟨36, by decide⟩ p hp j hj hq fz1_14_36 fz2_14_36
  · exact match_zero_fix ⟨15, by decide⟩ ⟨36, by decide⟩ p hp j hj hq fz1_15_36 fz2_15_36
  · exact match_zero_fix ⟨16, by decide⟩ ⟨36, by decide⟩ p hp j hj hq fz1_16_36 fz2_16_36
  · exact match_zero_fix ⟨17, by decide⟩ ⟨36, by decide⟩ p hp j hj hq fz1_17_36 fz2_17_36
  · exact match_zero_fix ⟨18, by decide⟩ ⟨36, by decide⟩ p hp j hj hq fz1_18_36 fz2_18_36
  · exact match_zero_fix ⟨19, by decide⟩ ⟨36, by decide⟩ p hp j hj hq fz1_19_36 fz2_19_36
  · exact match_zero_fix ⟨20, by decide⟩ ⟨36, by decide⟩ p hp j hj hq fz1_20_36 fz2_20_36
  · exact match_zero_fix ⟨21, by decide⟩ ⟨36, by decide⟩ p hp j hj hq fz1_21_36 fz2_21_36
  · exact match_zero_fix ⟨22, by decide⟩ ⟨36, by decide⟩ p hp j hj hq fz1_22_36 fz2_22_36
  · exact match_zero_fix ⟨23, by decide⟩ ⟨36, by decide⟩ p hp j hj hq fz1_23_36 fz2_23_36
  · exact match_zero_fix ⟨24, by decide⟩ ⟨36, by decide⟩ p hp j hj hq fz1_24_36 fz2_24_36
  · exact match_zero_fix ⟨25, by decide⟩ ⟨36, by decide⟩ p hp j hj hq fz1_25_36 fz2_25_36
  · exact match_zero_fix ⟨26, by decide⟩ ⟨36, by decide⟩ p hp j hj hq fz1_26_36 fz2_26_36
  · exact match_zero_fix ⟨27, by decide⟩ ⟨36, by decide⟩ p hp j hj hq fz1_27_36 fz2_27_36
  · exact match_zero_fix ⟨28, by decide⟩ ⟨36, by decide⟩ p hp j hj hq fz1_28_36 fz2_28_36
  · exact match_zero_fix ⟨29, by decide⟩ ⟨36, by decide⟩ p hp j hj hq fz1_29_36 fz2_29_36
  · exact match_zero_fix ⟨30, by decide⟩ ⟨36, by decide⟩ p hp j hj hq fz1_30_36 fz2_30_36
  · exact match_zero_fix ⟨31, by decide⟩ ⟨36, by decide⟩ p hp j hj hq fz1_31_36 fz2_31_36
  · exact match_zero_fix ⟨32, by decide⟩ ⟨36, by decide⟩ p hp j hj hq fz1_32_36 fz2_32_36
  · exact match_zero_fix ⟨33, by decide⟩ ⟨36, by decide⟩ p hp j hj hq fz1_33_36 fz2_33_36
  · exact match_zero_fix ⟨34, by decide⟩ ⟨36, by decide⟩ p hp j hj hq fz1_34_36 fz2_34_36
  · exact match_zero_fix ⟨35, by decide⟩ ⟨36, by decide⟩ p hp j hj hq fz1_35_36 fz2_35_36
  · exact pair_36_36 p hp hrep j hj hq
  · exact match_zero_fix ⟨37, by decide⟩ ⟨36, by decide⟩ p hp j hj hq fz1_37_36 fz2_37_36
  · exact match_zero_fix ⟨38, by decide⟩ ⟨36, by decide⟩ p hp j hj hq fz1_38_36 fz2_38_36
  · exact match_zero_fix ⟨39, by decide⟩ ⟨36, by decide⟩ p hp j hj hq fz1_39_36 fz2_39_36
  · exact match_zero_fix ⟨40, by decide⟩ ⟨36, by decide⟩ p hp j hj hq fz1_40_36 fz2_40_36
  · exact match_zero_fix ⟨41, by decide⟩ ⟨36, by decide⟩ p hp j hj hq fz1_41_36 fz2_41_36
  · exact match_zero_fix ⟨42, by decide⟩ ⟨36, by decide⟩ p hp j hj hq fz1_42_36 fz2_42_36
  · exact match_zero_fix ⟨43, by decide⟩ ⟨36, by decide⟩ p hp j hj hq fz1_43_36 fz2_43_36
  · exact match_zero_fix ⟨44, by decide⟩ ⟨36, by decide⟩ p hp j hj hq fz1_44_36 fz2_44_36
  · exact match_zero_fix ⟨45, by decide⟩ ⟨36, by decide⟩ p hp j hj hq fz1_45_36 fz2_45_36
  · exact match_zero_fix ⟨46, by decide⟩ ⟨36, by decide⟩ p hp j hj hq fz1_46_36 fz2_46_36
  · exact match_zero_fix ⟨47, by decide⟩ ⟨36, by decide⟩ p hp j hj hq fz1_47_36 fz2_47_36
  · exact match_zero_fix ⟨48, by decide⟩ ⟨36, by decide⟩ p hp j hj hq fz1_48_36 fz2_48_36
  · exact match_zero_fix ⟨49, by decide⟩ ⟨36, by decide⟩ p hp j hj hq fz1_49_36 fz2_49_36
  · exact match_zero_fix ⟨50, by decide⟩ ⟨36, by decide⟩ p hp j hj hq fz1_50_36 fz2_50_36
  · exact match_zero_fix ⟨51, by decide⟩ ⟨36, by decide⟩ p hp j hj hq fz1_51_36 fz2_51_36
  · exact match_zero_fix ⟨52, by decide⟩ ⟨36, by decide⟩ p hp j hj hq fz1_52_36 fz2_52_36
  · exact match_zero_fix ⟨53, by decide⟩ ⟨36, by decide⟩ p hp j hj hq fz1_53_36 fz2_53_36
  · exact match_zero_fix ⟨54, by decide⟩ ⟨36, by decide⟩ p hp j hj hq fz1_54_36 fz2_54_36
  · exact match_zero_fix ⟨55, by decide⟩ ⟨36, by decide⟩ p hp j hj hq fz1_55_36 fz2_55_36
  · exact match_zero_fix ⟨56, by decide⟩ ⟨36, by decide⟩ p hp j hj hq fz1_56_36 fz2_56_36
  · exact match_zero_fix ⟨57, by decide⟩ ⟨36, by decide⟩ p hp j hj hq fz1_57_36 fz2_57_36
  · exact match_zero_fix ⟨58, by decide⟩ ⟨36, by decide⟩ p hp j hj hq fz1_58_36 fz2_58_36
  · exact match_zero_fix ⟨59, by decide⟩ ⟨36, by decide⟩ p hp j hj hq fz1_59_36 fz2_59_36
  · exact match_zero_fix ⟨60, by decide⟩ ⟨36, by decide⟩ p hp j hj hq fz1_60_36 fz2_60_36
  · exact match_zero_fix ⟨61, by decide⟩ ⟨36, by decide⟩ p hp j hj hq fz1_61_36 fz2_61_36
  · exact match_zero_fix ⟨62, by decide⟩ ⟨36, by decide⟩ p hp j hj hq fz1_62_36 fz2_62_36
  · exact match_zero_fix ⟨63, by decide⟩ ⟨36, by decide⟩ p hp j hj hq fz1_63_36 fz2_63_36
  · exact match_zero_fix ⟨64, by decide⟩ ⟨36, by decide⟩ p hp j hj hq fz1_64_36 fz2_64_36
  · exact match_zero_fix ⟨65, by decide⟩ ⟨36, by decide⟩ p hp j hj hq fz1_65_36 fz2_65_36
  · exact match_zero_fix ⟨66, by decide⟩ ⟨36, by decide⟩ p hp j hj hq fz1_66_36 fz2_66_36
  · exact match_zero_fix ⟨67, by decide⟩ ⟨36, by decide⟩ p hp j hj hq fz1_67_36 fz2_67_36
  · exact match_zero_fix ⟨68, by decide⟩ ⟨36, by decide⟩ p hp j hj hq fz1_68_36 fz2_68_36
  · exact match_zero_fix ⟨69, by decide⟩ ⟨36, by decide⟩ p hp j hj hq fz1_69_36 fz2_69_36
  · exact pair_70_36 p hp hrep j hj hq
  · exact pair_71_36 p hp hrep j hj hq
  · exact pair_72_36 p hp hrep j hj hq
  · exact pair_73_36 p hp hrep j hj hq
  · exact pair_74_36 p hp hrep j hj hq
  · exact match_zero_fix ⟨75, by decide⟩ ⟨36, by decide⟩ p hp j hj hq fz1_75_36 fz2_75_36
  · exact match_zero_fix ⟨76, by decide⟩ ⟨36, by decide⟩ p hp j hj hq fz1_76_36 fz2_76_36
  · exact match_zero_fix ⟨77, by decide⟩ ⟨36, by decide⟩ p hp j hj hq fz1_77_36 fz2_77_36
  · exact match_zero_fix ⟨78, by decide⟩ ⟨36, by decide⟩ p hp j hj hq fz1_78_36 fz2_78_36
  · exact match_zero_fix ⟨79, by decide⟩ ⟨36, by decide⟩ p hp j hj hq fz1_79_36 fz2_79_36
  · exact match_zero_fix ⟨80, by decide⟩ ⟨36, by decide⟩ p hp j hj hq fz1_80_36 fz2_80_36
  · exact match_zero_fix ⟨81, by decide⟩ ⟨36, by decide⟩ p hp j hj hq fz1_81_36 fz2_81_36
  · exact match_zero_fix ⟨82, by decide⟩ ⟨36, by decide⟩ p hp j hj hq fz1_82_36 fz2_82_36
  · exact match_zero_fix ⟨83, by decide⟩ ⟨36, by decide⟩ p hp j hj hq fz1_83_36 fz2_83_36
  · exact match_zero_fix ⟨84, by decide⟩ ⟨36, by decide⟩ p hp j hj hq fz1_84_36 fz2_84_36
  · exact match_zero_fix ⟨85, by decide⟩ ⟨36, by decide⟩ p hp j hj hq fz1_85_36 fz2_85_36
  · exact match_zero_fix ⟨86, by decide⟩ ⟨36, by decide⟩ p hp j hj hq fz1_86_36 fz2_86_36
  · exact match_zero_fix ⟨87, by decide⟩ ⟨36, by decide⟩ p hp j hj hq fz1_87_36 fz2_87_36
  · exact match_zero_fix ⟨88, by decide⟩ ⟨36, by decide⟩ p hp j hj hq fz1_88_36 fz2_88_36
  · exact match_zero_fix ⟨89, by decide⟩ ⟨36, by decide⟩ p hp j hj hq fz1_89_36 fz2_89_36
  · exact match_zero_fix ⟨90, by decide⟩ ⟨36, by decide⟩ p hp j hj hq fz1_90_36 fz2_90_36
  · exact match_zero_fix ⟨91, by decide⟩ ⟨36, by decide⟩ p hp j hj hq fz1_91_36 fz2_91_36
  · exact match_zero_fix ⟨92, by decide⟩ ⟨36, by decide⟩ p hp j hj hq fz1_92_36 fz2_92_36
  · exact match_zero_fix ⟨93, by decide⟩ ⟨36, by decide⟩ p hp j hj hq fz1_93_36 fz2_93_36
  · exact match_zero_fix ⟨94, by decide⟩ ⟨36, by decide⟩ p hp j hj hq fz1_94_36 fz2_94_36
  · exact match_zero_fix ⟨95, by decide⟩ ⟨36, by decide⟩ p hp j hj hq fz1_95_36 fz2_95_36
  · exact match_zero_fix ⟨96, by decide⟩ ⟨36, by decide⟩ p hp j hj hq fz1_96_36 fz2_96_36
  · exact match_zero_fix ⟨97, by decide⟩ ⟨36, by decide⟩ p hp j hj hq fz1_97_36 fz2_97_36
  · exact pair_98_36 p hp hrep j hj hq
  · exact match_zero_fix ⟨99, by decide⟩ ⟨36, by decide⟩ p hp j hj hq fz1_99_36 fz2_99_36
  · exact match_zero_fix ⟨100, by decide⟩ ⟨36, by decide⟩ p hp j hj hq fz1_100_36 fz2_100_36
  · exact match_zero_fix ⟨101, by decide⟩ ⟨36, by decide⟩ p hp j hj hq fz1_101_36 fz2_101_36
  · exact match_zero_fix ⟨102, by decide⟩ ⟨36, by decide⟩ p hp j hj hq fz1_102_36 fz2_102_36
  · exact match_zero_fix ⟨103, by decide⟩ ⟨36, by decide⟩ p hp j hj hq fz1_103_36 fz2_103_36
  · exact match_zero_fix ⟨104, by decide⟩ ⟨36, by decide⟩ p hp j hj hq fz1_104_36 fz2_104_36
  · exact match_zero_fix ⟨105, by decide⟩ ⟨36, by decide⟩ p hp j hj hq fz1_105_36 fz2_105_36
  · exact match_zero_fix ⟨106, by decide⟩ ⟨36, by decide⟩ p hp j hj hq fz1_106_36 fz2_106_36
  · exact match_zero_fix ⟨107, by decide⟩ ⟨36, by decide⟩ p hp j hj hq fz1_107_36 fz2_107_36
  · exact match_zero_fix ⟨108, by decide⟩ ⟨36, by decide⟩ p hp j hj hq fz1_108_36 fz2_108_36
  · exact match_zero_fix ⟨109, by decide⟩ ⟨36, by decide⟩ p hp j hj hq fz1_109_36 fz2_109_36
  · exact match_zero_fix ⟨110, by decide⟩ ⟨36, by decide⟩ p hp j hj hq fz1_110_36 fz2_110_36
  · exact match_zero_fix ⟨111, by decide⟩ ⟨36, by decide⟩ p hp j hj hq fz1_111_36 fz2_111_36
  · exact match_zero_fix ⟨112, by decide⟩ ⟨36, by decide⟩ p hp j hj hq fz1_112_36 fz2_112_36
  · exact match_zero_fix ⟨113, by decide⟩ ⟨36, by decide⟩ p hp j hj hq fz1_113_36 fz2_113_36
  · exact match_zero_fix ⟨114, by decide⟩ ⟨36, by decide⟩ p hp j hj hq fz1_114_36 fz2_114_36
  · exact match_zero_fix ⟨115, by decide⟩ ⟨36, by decide⟩ p hp j hj hq fz1_115_36 fz2_115_36
  · exact match_zero_fix ⟨116, by decide⟩ ⟨36, by decide⟩ p hp j hj hq fz1_116_36 fz2_116_36
  · exact match_zero_fix ⟨117, by decide⟩ ⟨36, by decide⟩ p hp j hj hq fz1_117_36 fz2_117_36
  · exact match_zero_fix ⟨118, by decide⟩ ⟨36, by decide⟩ p hp j hj hq fz1_118_36 fz2_118_36
  · exact pair_119_36 p hp hrep j hj hq
  · exact match_zero_fix ⟨120, by decide⟩ ⟨36, by decide⟩ p hp j hj hq fz1_120_36 fz2_120_36
  · exact match_zero_fix ⟨121, by decide⟩ ⟨36, by decide⟩ p hp j hj hq fz1_121_36 fz2_121_36
  · exact pair_122_36 p hp hrep j hj hq
  · exact match_zero_fix ⟨123, by decide⟩ ⟨36, by decide⟩ p hp j hj hq fz1_123_36 fz2_123_36
  · exact match_zero_fix ⟨124, by decide⟩ ⟨36, by decide⟩ p hp j hj hq fz1_124_36 fz2_124_36
  · exact match_zero_fix ⟨125, by decide⟩ ⟨36, by decide⟩ p hp j hj hq fz1_125_36 fz2_125_36
  · exact match_zero_fix ⟨126, by decide⟩ ⟨36, by decide⟩ p hp j hj hq fz1_126_36 fz2_126_36
  · exact match_zero_fix ⟨127, by decide⟩ ⟨36, by decide⟩ p hp j hj hq fz1_127_36 fz2_127_36
  · exact match_zero_fix ⟨128, by decide⟩ ⟨36, by decide⟩ p hp j hj hq fz1_128_36 fz2_128_36
  · exact match_zero_fix ⟨129, by decide⟩ ⟨36, by decide⟩ p hp j hj hq fz1_129_36 fz2_129_36
  · exact pair_130_36 p hp hrep j hj hq
  · exact match_zero_fix ⟨131, by decide⟩ ⟨36, by decide⟩ p hp j hj hq fz1_131_36 fz2_131_36
  · exact match_zero_fix ⟨132, by decide⟩ ⟨36, by decide⟩ p hp j hj hq fz1_132_36 fz2_132_36
  · exact pair_133_36 p hp hrep j hj hq
  · exact match_zero_fix ⟨134, by decide⟩ ⟨36, by decide⟩ p hp j hj hq fz1_134_36 fz2_134_36
  · exact match_zero_fix ⟨135, by decide⟩ ⟨36, by decide⟩ p hp j hj hq fz1_135_36 fz2_135_36
  · exact pair_136_36 p hp hrep j hj hq
  · exact match_zero_fix ⟨137, by decide⟩ ⟨36, by decide⟩ p hp j hj hq fz1_137_36 fz2_137_36
  · exact match_zero_fix ⟨138, by decide⟩ ⟨36, by decide⟩ p hp j hj hq fz1_138_36 fz2_138_36
  · exact match_zero_fix ⟨139, by decide⟩ ⟨36, by decide⟩ p hp j hj hq fz1_139_36 fz2_139_36
  · exact match_zero_fix ⟨140, by decide⟩ ⟨36, by decide⟩ p hp j hj hq fz1_140_36 fz2_140_36
  · exact match_zero_fix ⟨141, by decide⟩ ⟨36, by decide⟩ p hp j hj hq fz1_141_36 fz2_141_36
  · exact match_zero_fix ⟨142, by decide⟩ ⟨36, by decide⟩ p hp j hj hq fz1_142_36 fz2_142_36
  · exact pair_143_36 p hp hrep j hj hq
  · exact match_zero_fix ⟨144, by decide⟩ ⟨36, by decide⟩ p hp j hj hq fz1_144_36 fz2_144_36
  · exact match_zero_fix ⟨145, by decide⟩ ⟨36, by decide⟩ p hp j hj hq fz1_145_36 fz2_145_36
  · exact match_zero_fix ⟨146, by decide⟩ ⟨36, by decide⟩ p hp j hj hq fz1_146_36 fz2_146_36
  · exact pair_147_36 p hp hrep j hj hq

theorem master_37 (p : Nat) (hp : p < (Q2.transData.getD 37 []).length)
    (hrep : (Q2.cosetIsRep.getD 37 []).getD p false = true)
    (rK : Fin 148) (j : Nat) (hj : j < (repChars.getD rK.val []).length)
    (hq : (normIsRep.getD rK.val []).getD j false = true) :
    species (Q2.reps (⟨37, by decide⟩ : Fin 148)) (colE2 ⟨37, by decide⟩ p hp)
        (rowE2 rK j hj hq)
      = species (reps (⟨37, by decide⟩ : Fin 148))
        (colE1 ⟨37, by decide⟩ p (transLenTr ⟨37, by decide⟩ p hp)) (rowE1 rK j hj) := by
  rcases rK with ⟨nK, hnK⟩; interval_cases nK
  · exact match_zero_len ⟨0, by decide⟩ ⟨37, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨1, by decide⟩ ⟨37, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨2, by decide⟩ ⟨37, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨3, by decide⟩ ⟨37, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨4, by decide⟩ ⟨37, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨5, by decide⟩ ⟨37, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨6, by decide⟩ ⟨37, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨7, by decide⟩ ⟨37, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨8, by decide⟩ ⟨37, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨9, by decide⟩ ⟨37, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨10, by decide⟩ ⟨37, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨11, by decide⟩ ⟨37, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨12, by decide⟩ ⟨37, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_fix ⟨13, by decide⟩ ⟨37, by decide⟩ p hp j hj hq fz1_13_37 fz2_13_37
  · exact match_zero_fix ⟨14, by decide⟩ ⟨37, by decide⟩ p hp j hj hq fz1_14_37 fz2_14_37
  · exact match_zero_fix ⟨15, by decide⟩ ⟨37, by decide⟩ p hp j hj hq fz1_15_37 fz2_15_37
  · exact match_zero_fix ⟨16, by decide⟩ ⟨37, by decide⟩ p hp j hj hq fz1_16_37 fz2_16_37
  · exact match_zero_fix ⟨17, by decide⟩ ⟨37, by decide⟩ p hp j hj hq fz1_17_37 fz2_17_37
  · exact match_zero_fix ⟨18, by decide⟩ ⟨37, by decide⟩ p hp j hj hq fz1_18_37 fz2_18_37
  · exact match_zero_fix ⟨19, by decide⟩ ⟨37, by decide⟩ p hp j hj hq fz1_19_37 fz2_19_37
  · exact match_zero_fix ⟨20, by decide⟩ ⟨37, by decide⟩ p hp j hj hq fz1_20_37 fz2_20_37
  · exact match_zero_fix ⟨21, by decide⟩ ⟨37, by decide⟩ p hp j hj hq fz1_21_37 fz2_21_37
  · exact match_zero_fix ⟨22, by decide⟩ ⟨37, by decide⟩ p hp j hj hq fz1_22_37 fz2_22_37
  · exact match_zero_fix ⟨23, by decide⟩ ⟨37, by decide⟩ p hp j hj hq fz1_23_37 fz2_23_37
  · exact match_zero_fix ⟨24, by decide⟩ ⟨37, by decide⟩ p hp j hj hq fz1_24_37 fz2_24_37
  · exact match_zero_fix ⟨25, by decide⟩ ⟨37, by decide⟩ p hp j hj hq fz1_25_37 fz2_25_37
  · exact match_zero_fix ⟨26, by decide⟩ ⟨37, by decide⟩ p hp j hj hq fz1_26_37 fz2_26_37
  · exact match_zero_fix ⟨27, by decide⟩ ⟨37, by decide⟩ p hp j hj hq fz1_27_37 fz2_27_37
  · exact match_zero_fix ⟨28, by decide⟩ ⟨37, by decide⟩ p hp j hj hq fz1_28_37 fz2_28_37
  · exact match_zero_fix ⟨29, by decide⟩ ⟨37, by decide⟩ p hp j hj hq fz1_29_37 fz2_29_37
  · exact match_zero_fix ⟨30, by decide⟩ ⟨37, by decide⟩ p hp j hj hq fz1_30_37 fz2_30_37
  · exact match_zero_fix ⟨31, by decide⟩ ⟨37, by decide⟩ p hp j hj hq fz1_31_37 fz2_31_37
  · exact match_zero_fix ⟨32, by decide⟩ ⟨37, by decide⟩ p hp j hj hq fz1_32_37 fz2_32_37
  · exact match_zero_fix ⟨33, by decide⟩ ⟨37, by decide⟩ p hp j hj hq fz1_33_37 fz2_33_37
  · exact match_zero_fix ⟨34, by decide⟩ ⟨37, by decide⟩ p hp j hj hq fz1_34_37 fz2_34_37
  · exact match_zero_fix ⟨35, by decide⟩ ⟨37, by decide⟩ p hp j hj hq fz1_35_37 fz2_35_37
  · exact match_zero_fix ⟨36, by decide⟩ ⟨37, by decide⟩ p hp j hj hq fz1_36_37 fz2_36_37
  · exact pair_37_37 p hp hrep j hj hq
  · exact match_zero_fix ⟨38, by decide⟩ ⟨37, by decide⟩ p hp j hj hq fz1_38_37 fz2_38_37
  · exact match_zero_fix ⟨39, by decide⟩ ⟨37, by decide⟩ p hp j hj hq fz1_39_37 fz2_39_37
  · exact match_zero_fix ⟨40, by decide⟩ ⟨37, by decide⟩ p hp j hj hq fz1_40_37 fz2_40_37
  · exact match_zero_fix ⟨41, by decide⟩ ⟨37, by decide⟩ p hp j hj hq fz1_41_37 fz2_41_37
  · exact match_zero_fix ⟨42, by decide⟩ ⟨37, by decide⟩ p hp j hj hq fz1_42_37 fz2_42_37
  · exact match_zero_fix ⟨43, by decide⟩ ⟨37, by decide⟩ p hp j hj hq fz1_43_37 fz2_43_37
  · exact match_zero_fix ⟨44, by decide⟩ ⟨37, by decide⟩ p hp j hj hq fz1_44_37 fz2_44_37
  · exact match_zero_fix ⟨45, by decide⟩ ⟨37, by decide⟩ p hp j hj hq fz1_45_37 fz2_45_37
  · exact match_zero_fix ⟨46, by decide⟩ ⟨37, by decide⟩ p hp j hj hq fz1_46_37 fz2_46_37
  · exact match_zero_fix ⟨47, by decide⟩ ⟨37, by decide⟩ p hp j hj hq fz1_47_37 fz2_47_37
  · exact match_zero_fix ⟨48, by decide⟩ ⟨37, by decide⟩ p hp j hj hq fz1_48_37 fz2_48_37
  · exact match_zero_fix ⟨49, by decide⟩ ⟨37, by decide⟩ p hp j hj hq fz1_49_37 fz2_49_37
  · exact match_zero_fix ⟨50, by decide⟩ ⟨37, by decide⟩ p hp j hj hq fz1_50_37 fz2_50_37
  · exact match_zero_fix ⟨51, by decide⟩ ⟨37, by decide⟩ p hp j hj hq fz1_51_37 fz2_51_37
  · exact match_zero_fix ⟨52, by decide⟩ ⟨37, by decide⟩ p hp j hj hq fz1_52_37 fz2_52_37
  · exact match_zero_fix ⟨53, by decide⟩ ⟨37, by decide⟩ p hp j hj hq fz1_53_37 fz2_53_37
  · exact match_zero_fix ⟨54, by decide⟩ ⟨37, by decide⟩ p hp j hj hq fz1_54_37 fz2_54_37
  · exact match_zero_fix ⟨55, by decide⟩ ⟨37, by decide⟩ p hp j hj hq fz1_55_37 fz2_55_37
  · exact match_zero_fix ⟨56, by decide⟩ ⟨37, by decide⟩ p hp j hj hq fz1_56_37 fz2_56_37
  · exact match_zero_fix ⟨57, by decide⟩ ⟨37, by decide⟩ p hp j hj hq fz1_57_37 fz2_57_37
  · exact match_zero_fix ⟨58, by decide⟩ ⟨37, by decide⟩ p hp j hj hq fz1_58_37 fz2_58_37
  · exact match_zero_fix ⟨59, by decide⟩ ⟨37, by decide⟩ p hp j hj hq fz1_59_37 fz2_59_37
  · exact match_zero_fix ⟨60, by decide⟩ ⟨37, by decide⟩ p hp j hj hq fz1_60_37 fz2_60_37
  · exact match_zero_fix ⟨61, by decide⟩ ⟨37, by decide⟩ p hp j hj hq fz1_61_37 fz2_61_37
  · exact match_zero_fix ⟨62, by decide⟩ ⟨37, by decide⟩ p hp j hj hq fz1_62_37 fz2_62_37
  · exact match_zero_fix ⟨63, by decide⟩ ⟨37, by decide⟩ p hp j hj hq fz1_63_37 fz2_63_37
  · exact match_zero_fix ⟨64, by decide⟩ ⟨37, by decide⟩ p hp j hj hq fz1_64_37 fz2_64_37
  · exact match_zero_fix ⟨65, by decide⟩ ⟨37, by decide⟩ p hp j hj hq fz1_65_37 fz2_65_37
  · exact match_zero_fix ⟨66, by decide⟩ ⟨37, by decide⟩ p hp j hj hq fz1_66_37 fz2_66_37
  · exact match_zero_fix ⟨67, by decide⟩ ⟨37, by decide⟩ p hp j hj hq fz1_67_37 fz2_67_37
  · exact match_zero_fix ⟨68, by decide⟩ ⟨37, by decide⟩ p hp j hj hq fz1_68_37 fz2_68_37
  · exact match_zero_fix ⟨69, by decide⟩ ⟨37, by decide⟩ p hp j hj hq fz1_69_37 fz2_69_37
  · exact match_zero_fix ⟨70, by decide⟩ ⟨37, by decide⟩ p hp j hj hq fz1_70_37 fz2_70_37
  · exact match_zero_fix ⟨71, by decide⟩ ⟨37, by decide⟩ p hp j hj hq fz1_71_37 fz2_71_37
  · exact match_zero_fix ⟨72, by decide⟩ ⟨37, by decide⟩ p hp j hj hq fz1_72_37 fz2_72_37
  · exact match_zero_fix ⟨73, by decide⟩ ⟨37, by decide⟩ p hp j hj hq fz1_73_37 fz2_73_37
  · exact match_zero_fix ⟨74, by decide⟩ ⟨37, by decide⟩ p hp j hj hq fz1_74_37 fz2_74_37
  · exact pair_75_37 p hp hrep j hj hq
  · exact pair_76_37 p hp hrep j hj hq
  · exact pair_77_37 p hp hrep j hj hq
  · exact pair_78_37 p hp hrep j hj hq
  · exact pair_79_37 p hp hrep j hj hq
  · exact match_zero_fix ⟨80, by decide⟩ ⟨37, by decide⟩ p hp j hj hq fz1_80_37 fz2_80_37
  · exact match_zero_fix ⟨81, by decide⟩ ⟨37, by decide⟩ p hp j hj hq fz1_81_37 fz2_81_37
  · exact match_zero_fix ⟨82, by decide⟩ ⟨37, by decide⟩ p hp j hj hq fz1_82_37 fz2_82_37
  · exact match_zero_fix ⟨83, by decide⟩ ⟨37, by decide⟩ p hp j hj hq fz1_83_37 fz2_83_37
  · exact match_zero_fix ⟨84, by decide⟩ ⟨37, by decide⟩ p hp j hj hq fz1_84_37 fz2_84_37
  · exact match_zero_fix ⟨85, by decide⟩ ⟨37, by decide⟩ p hp j hj hq fz1_85_37 fz2_85_37
  · exact match_zero_fix ⟨86, by decide⟩ ⟨37, by decide⟩ p hp j hj hq fz1_86_37 fz2_86_37
  · exact match_zero_fix ⟨87, by decide⟩ ⟨37, by decide⟩ p hp j hj hq fz1_87_37 fz2_87_37
  · exact match_zero_fix ⟨88, by decide⟩ ⟨37, by decide⟩ p hp j hj hq fz1_88_37 fz2_88_37
  · exact match_zero_fix ⟨89, by decide⟩ ⟨37, by decide⟩ p hp j hj hq fz1_89_37 fz2_89_37
  · exact match_zero_fix ⟨90, by decide⟩ ⟨37, by decide⟩ p hp j hj hq fz1_90_37 fz2_90_37
  · exact match_zero_fix ⟨91, by decide⟩ ⟨37, by decide⟩ p hp j hj hq fz1_91_37 fz2_91_37
  · exact match_zero_fix ⟨92, by decide⟩ ⟨37, by decide⟩ p hp j hj hq fz1_92_37 fz2_92_37
  · exact match_zero_fix ⟨93, by decide⟩ ⟨37, by decide⟩ p hp j hj hq fz1_93_37 fz2_93_37
  · exact match_zero_fix ⟨94, by decide⟩ ⟨37, by decide⟩ p hp j hj hq fz1_94_37 fz2_94_37
  · exact match_zero_fix ⟨95, by decide⟩ ⟨37, by decide⟩ p hp j hj hq fz1_95_37 fz2_95_37
  · exact match_zero_fix ⟨96, by decide⟩ ⟨37, by decide⟩ p hp j hj hq fz1_96_37 fz2_96_37
  · exact match_zero_fix ⟨97, by decide⟩ ⟨37, by decide⟩ p hp j hj hq fz1_97_37 fz2_97_37
  · exact match_zero_fix ⟨98, by decide⟩ ⟨37, by decide⟩ p hp j hj hq fz1_98_37 fz2_98_37
  · exact pair_99_37 p hp hrep j hj hq
  · exact match_zero_fix ⟨100, by decide⟩ ⟨37, by decide⟩ p hp j hj hq fz1_100_37 fz2_100_37
  · exact match_zero_fix ⟨101, by decide⟩ ⟨37, by decide⟩ p hp j hj hq fz1_101_37 fz2_101_37
  · exact match_zero_fix ⟨102, by decide⟩ ⟨37, by decide⟩ p hp j hj hq fz1_102_37 fz2_102_37
  · exact match_zero_fix ⟨103, by decide⟩ ⟨37, by decide⟩ p hp j hj hq fz1_103_37 fz2_103_37
  · exact match_zero_fix ⟨104, by decide⟩ ⟨37, by decide⟩ p hp j hj hq fz1_104_37 fz2_104_37
  · exact match_zero_fix ⟨105, by decide⟩ ⟨37, by decide⟩ p hp j hj hq fz1_105_37 fz2_105_37
  · exact match_zero_fix ⟨106, by decide⟩ ⟨37, by decide⟩ p hp j hj hq fz1_106_37 fz2_106_37
  · exact match_zero_fix ⟨107, by decide⟩ ⟨37, by decide⟩ p hp j hj hq fz1_107_37 fz2_107_37
  · exact match_zero_fix ⟨108, by decide⟩ ⟨37, by decide⟩ p hp j hj hq fz1_108_37 fz2_108_37
  · exact match_zero_fix ⟨109, by decide⟩ ⟨37, by decide⟩ p hp j hj hq fz1_109_37 fz2_109_37
  · exact match_zero_fix ⟨110, by decide⟩ ⟨37, by decide⟩ p hp j hj hq fz1_110_37 fz2_110_37
  · exact match_zero_fix ⟨111, by decide⟩ ⟨37, by decide⟩ p hp j hj hq fz1_111_37 fz2_111_37
  · exact match_zero_fix ⟨112, by decide⟩ ⟨37, by decide⟩ p hp j hj hq fz1_112_37 fz2_112_37
  · exact match_zero_fix ⟨113, by decide⟩ ⟨37, by decide⟩ p hp j hj hq fz1_113_37 fz2_113_37
  · exact match_zero_fix ⟨114, by decide⟩ ⟨37, by decide⟩ p hp j hj hq fz1_114_37 fz2_114_37
  · exact match_zero_fix ⟨115, by decide⟩ ⟨37, by decide⟩ p hp j hj hq fz1_115_37 fz2_115_37
  · exact match_zero_fix ⟨116, by decide⟩ ⟨37, by decide⟩ p hp j hj hq fz1_116_37 fz2_116_37
  · exact match_zero_fix ⟨117, by decide⟩ ⟨37, by decide⟩ p hp j hj hq fz1_117_37 fz2_117_37
  · exact match_zero_fix ⟨118, by decide⟩ ⟨37, by decide⟩ p hp j hj hq fz1_118_37 fz2_118_37
  · exact match_zero_fix ⟨119, by decide⟩ ⟨37, by decide⟩ p hp j hj hq fz1_119_37 fz2_119_37
  · exact pair_120_37 p hp hrep j hj hq
  · exact match_zero_fix ⟨121, by decide⟩ ⟨37, by decide⟩ p hp j hj hq fz1_121_37 fz2_121_37
  · exact match_zero_fix ⟨122, by decide⟩ ⟨37, by decide⟩ p hp j hj hq fz1_122_37 fz2_122_37
  · exact pair_123_37 p hp hrep j hj hq
  · exact match_zero_fix ⟨124, by decide⟩ ⟨37, by decide⟩ p hp j hj hq fz1_124_37 fz2_124_37
  · exact match_zero_fix ⟨125, by decide⟩ ⟨37, by decide⟩ p hp j hj hq fz1_125_37 fz2_125_37
  · exact pair_126_37 p hp hrep j hj hq
  · exact match_zero_fix ⟨127, by decide⟩ ⟨37, by decide⟩ p hp j hj hq fz1_127_37 fz2_127_37
  · exact match_zero_fix ⟨128, by decide⟩ ⟨37, by decide⟩ p hp j hj hq fz1_128_37 fz2_128_37
  · exact match_zero_fix ⟨129, by decide⟩ ⟨37, by decide⟩ p hp j hj hq fz1_129_37 fz2_129_37
  · exact match_zero_fix ⟨130, by decide⟩ ⟨37, by decide⟩ p hp j hj hq fz1_130_37 fz2_130_37
  · exact match_zero_fix ⟨131, by decide⟩ ⟨37, by decide⟩ p hp j hj hq fz1_131_37 fz2_131_37
  · exact match_zero_fix ⟨132, by decide⟩ ⟨37, by decide⟩ p hp j hj hq fz1_132_37 fz2_132_37
  · exact match_zero_fix ⟨133, by decide⟩ ⟨37, by decide⟩ p hp j hj hq fz1_133_37 fz2_133_37
  · exact pair_134_37 p hp hrep j hj hq
  · exact match_zero_fix ⟨135, by decide⟩ ⟨37, by decide⟩ p hp j hj hq fz1_135_37 fz2_135_37
  · exact match_zero_fix ⟨136, by decide⟩ ⟨37, by decide⟩ p hp j hj hq fz1_136_37 fz2_136_37
  · exact pair_137_37 p hp hrep j hj hq
  · exact match_zero_fix ⟨138, by decide⟩ ⟨37, by decide⟩ p hp j hj hq fz1_138_37 fz2_138_37
  · exact match_zero_fix ⟨139, by decide⟩ ⟨37, by decide⟩ p hp j hj hq fz1_139_37 fz2_139_37
  · exact match_zero_fix ⟨140, by decide⟩ ⟨37, by decide⟩ p hp j hj hq fz1_140_37 fz2_140_37
  · exact match_zero_fix ⟨141, by decide⟩ ⟨37, by decide⟩ p hp j hj hq fz1_141_37 fz2_141_37
  · exact match_zero_fix ⟨142, by decide⟩ ⟨37, by decide⟩ p hp j hj hq fz1_142_37 fz2_142_37
  · exact pair_143_37 p hp hrep j hj hq
  · exact match_zero_fix ⟨144, by decide⟩ ⟨37, by decide⟩ p hp j hj hq fz1_144_37 fz2_144_37
  · exact match_zero_fix ⟨145, by decide⟩ ⟨37, by decide⟩ p hp j hj hq fz1_145_37 fz2_145_37
  · exact match_zero_fix ⟨146, by decide⟩ ⟨37, by decide⟩ p hp j hj hq fz1_146_37 fz2_146_37
  · exact pair_147_37 p hp hrep j hj hq

theorem master_38 (p : Nat) (hp : p < (Q2.transData.getD 38 []).length)
    (hrep : (Q2.cosetIsRep.getD 38 []).getD p false = true)
    (rK : Fin 148) (j : Nat) (hj : j < (repChars.getD rK.val []).length)
    (hq : (normIsRep.getD rK.val []).getD j false = true) :
    species (Q2.reps (⟨38, by decide⟩ : Fin 148)) (colE2 ⟨38, by decide⟩ p hp)
        (rowE2 rK j hj hq)
      = species (reps (⟨38, by decide⟩ : Fin 148))
        (colE1 ⟨38, by decide⟩ p (transLenTr ⟨38, by decide⟩ p hp)) (rowE1 rK j hj) := by
  rcases rK with ⟨nK, hnK⟩; interval_cases nK
  · exact match_zero_len ⟨0, by decide⟩ ⟨38, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨1, by decide⟩ ⟨38, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨2, by decide⟩ ⟨38, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨3, by decide⟩ ⟨38, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨4, by decide⟩ ⟨38, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨5, by decide⟩ ⟨38, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨6, by decide⟩ ⟨38, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨7, by decide⟩ ⟨38, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨8, by decide⟩ ⟨38, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨9, by decide⟩ ⟨38, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨10, by decide⟩ ⟨38, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨11, by decide⟩ ⟨38, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨12, by decide⟩ ⟨38, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_fix ⟨13, by decide⟩ ⟨38, by decide⟩ p hp j hj hq fz1_13_38 fz2_13_38
  · exact match_zero_fix ⟨14, by decide⟩ ⟨38, by decide⟩ p hp j hj hq fz1_14_38 fz2_14_38
  · exact match_zero_fix ⟨15, by decide⟩ ⟨38, by decide⟩ p hp j hj hq fz1_15_38 fz2_15_38
  · exact match_zero_fix ⟨16, by decide⟩ ⟨38, by decide⟩ p hp j hj hq fz1_16_38 fz2_16_38
  · exact match_zero_fix ⟨17, by decide⟩ ⟨38, by decide⟩ p hp j hj hq fz1_17_38 fz2_17_38
  · exact match_zero_fix ⟨18, by decide⟩ ⟨38, by decide⟩ p hp j hj hq fz1_18_38 fz2_18_38
  · exact match_zero_fix ⟨19, by decide⟩ ⟨38, by decide⟩ p hp j hj hq fz1_19_38 fz2_19_38
  · exact match_zero_fix ⟨20, by decide⟩ ⟨38, by decide⟩ p hp j hj hq fz1_20_38 fz2_20_38
  · exact match_zero_fix ⟨21, by decide⟩ ⟨38, by decide⟩ p hp j hj hq fz1_21_38 fz2_21_38
  · exact match_zero_fix ⟨22, by decide⟩ ⟨38, by decide⟩ p hp j hj hq fz1_22_38 fz2_22_38
  · exact match_zero_fix ⟨23, by decide⟩ ⟨38, by decide⟩ p hp j hj hq fz1_23_38 fz2_23_38
  · exact match_zero_fix ⟨24, by decide⟩ ⟨38, by decide⟩ p hp j hj hq fz1_24_38 fz2_24_38
  · exact match_zero_fix ⟨25, by decide⟩ ⟨38, by decide⟩ p hp j hj hq fz1_25_38 fz2_25_38
  · exact match_zero_fix ⟨26, by decide⟩ ⟨38, by decide⟩ p hp j hj hq fz1_26_38 fz2_26_38
  · exact match_zero_fix ⟨27, by decide⟩ ⟨38, by decide⟩ p hp j hj hq fz1_27_38 fz2_27_38
  · exact match_zero_fix ⟨28, by decide⟩ ⟨38, by decide⟩ p hp j hj hq fz1_28_38 fz2_28_38
  · exact match_zero_fix ⟨29, by decide⟩ ⟨38, by decide⟩ p hp j hj hq fz1_29_38 fz2_29_38
  · exact match_zero_fix ⟨30, by decide⟩ ⟨38, by decide⟩ p hp j hj hq fz1_30_38 fz2_30_38
  · exact match_zero_fix ⟨31, by decide⟩ ⟨38, by decide⟩ p hp j hj hq fz1_31_38 fz2_31_38
  · exact match_zero_fix ⟨32, by decide⟩ ⟨38, by decide⟩ p hp j hj hq fz1_32_38 fz2_32_38
  · exact match_zero_fix ⟨33, by decide⟩ ⟨38, by decide⟩ p hp j hj hq fz1_33_38 fz2_33_38
  · exact match_zero_fix ⟨34, by decide⟩ ⟨38, by decide⟩ p hp j hj hq fz1_34_38 fz2_34_38
  · exact match_zero_fix ⟨35, by decide⟩ ⟨38, by decide⟩ p hp j hj hq fz1_35_38 fz2_35_38
  · exact match_zero_fix ⟨36, by decide⟩ ⟨38, by decide⟩ p hp j hj hq fz1_36_38 fz2_36_38
  · exact match_zero_fix ⟨37, by decide⟩ ⟨38, by decide⟩ p hp j hj hq fz1_37_38 fz2_37_38
  · exact pair_38_38 p hp hrep j hj hq
  · exact match_zero_fix ⟨39, by decide⟩ ⟨38, by decide⟩ p hp j hj hq fz1_39_38 fz2_39_38
  · exact match_zero_fix ⟨40, by decide⟩ ⟨38, by decide⟩ p hp j hj hq fz1_40_38 fz2_40_38
  · exact match_zero_fix ⟨41, by decide⟩ ⟨38, by decide⟩ p hp j hj hq fz1_41_38 fz2_41_38
  · exact match_zero_fix ⟨42, by decide⟩ ⟨38, by decide⟩ p hp j hj hq fz1_42_38 fz2_42_38
  · exact match_zero_fix ⟨43, by decide⟩ ⟨38, by decide⟩ p hp j hj hq fz1_43_38 fz2_43_38
  · exact match_zero_fix ⟨44, by decide⟩ ⟨38, by decide⟩ p hp j hj hq fz1_44_38 fz2_44_38
  · exact match_zero_fix ⟨45, by decide⟩ ⟨38, by decide⟩ p hp j hj hq fz1_45_38 fz2_45_38
  · exact match_zero_fix ⟨46, by decide⟩ ⟨38, by decide⟩ p hp j hj hq fz1_46_38 fz2_46_38
  · exact match_zero_fix ⟨47, by decide⟩ ⟨38, by decide⟩ p hp j hj hq fz1_47_38 fz2_47_38
  · exact match_zero_fix ⟨48, by decide⟩ ⟨38, by decide⟩ p hp j hj hq fz1_48_38 fz2_48_38
  · exact match_zero_fix ⟨49, by decide⟩ ⟨38, by decide⟩ p hp j hj hq fz1_49_38 fz2_49_38
  · exact match_zero_fix ⟨50, by decide⟩ ⟨38, by decide⟩ p hp j hj hq fz1_50_38 fz2_50_38
  · exact match_zero_fix ⟨51, by decide⟩ ⟨38, by decide⟩ p hp j hj hq fz1_51_38 fz2_51_38
  · exact match_zero_fix ⟨52, by decide⟩ ⟨38, by decide⟩ p hp j hj hq fz1_52_38 fz2_52_38
  · exact match_zero_fix ⟨53, by decide⟩ ⟨38, by decide⟩ p hp j hj hq fz1_53_38 fz2_53_38
  · exact match_zero_fix ⟨54, by decide⟩ ⟨38, by decide⟩ p hp j hj hq fz1_54_38 fz2_54_38
  · exact pair_55_38 p hp hrep j hj hq
  · exact pair_56_38 p hp hrep j hj hq
  · exact pair_57_38 p hp hrep j hj hq
  · exact pair_58_38 p hp hrep j hj hq
  · exact pair_59_38 p hp hrep j hj hq
  · exact match_zero_fix ⟨60, by decide⟩ ⟨38, by decide⟩ p hp j hj hq fz1_60_38 fz2_60_38
  · exact match_zero_fix ⟨61, by decide⟩ ⟨38, by decide⟩ p hp j hj hq fz1_61_38 fz2_61_38
  · exact match_zero_fix ⟨62, by decide⟩ ⟨38, by decide⟩ p hp j hj hq fz1_62_38 fz2_62_38
  · exact match_zero_fix ⟨63, by decide⟩ ⟨38, by decide⟩ p hp j hj hq fz1_63_38 fz2_63_38
  · exact match_zero_fix ⟨64, by decide⟩ ⟨38, by decide⟩ p hp j hj hq fz1_64_38 fz2_64_38
  · exact match_zero_fix ⟨65, by decide⟩ ⟨38, by decide⟩ p hp j hj hq fz1_65_38 fz2_65_38
  · exact match_zero_fix ⟨66, by decide⟩ ⟨38, by decide⟩ p hp j hj hq fz1_66_38 fz2_66_38
  · exact match_zero_fix ⟨67, by decide⟩ ⟨38, by decide⟩ p hp j hj hq fz1_67_38 fz2_67_38
  · exact match_zero_fix ⟨68, by decide⟩ ⟨38, by decide⟩ p hp j hj hq fz1_68_38 fz2_68_38
  · exact match_zero_fix ⟨69, by decide⟩ ⟨38, by decide⟩ p hp j hj hq fz1_69_38 fz2_69_38
  · exact match_zero_fix ⟨70, by decide⟩ ⟨38, by decide⟩ p hp j hj hq fz1_70_38 fz2_70_38
  · exact match_zero_fix ⟨71, by decide⟩ ⟨38, by decide⟩ p hp j hj hq fz1_71_38 fz2_71_38
  · exact match_zero_fix ⟨72, by decide⟩ ⟨38, by decide⟩ p hp j hj hq fz1_72_38 fz2_72_38
  · exact match_zero_fix ⟨73, by decide⟩ ⟨38, by decide⟩ p hp j hj hq fz1_73_38 fz2_73_38
  · exact match_zero_fix ⟨74, by decide⟩ ⟨38, by decide⟩ p hp j hj hq fz1_74_38 fz2_74_38
  · exact match_zero_fix ⟨75, by decide⟩ ⟨38, by decide⟩ p hp j hj hq fz1_75_38 fz2_75_38
  · exact match_zero_fix ⟨76, by decide⟩ ⟨38, by decide⟩ p hp j hj hq fz1_76_38 fz2_76_38
  · exact match_zero_fix ⟨77, by decide⟩ ⟨38, by decide⟩ p hp j hj hq fz1_77_38 fz2_77_38
  · exact match_zero_fix ⟨78, by decide⟩ ⟨38, by decide⟩ p hp j hj hq fz1_78_38 fz2_78_38
  · exact match_zero_fix ⟨79, by decide⟩ ⟨38, by decide⟩ p hp j hj hq fz1_79_38 fz2_79_38
  · exact match_zero_fix ⟨80, by decide⟩ ⟨38, by decide⟩ p hp j hj hq fz1_80_38 fz2_80_38
  · exact match_zero_fix ⟨81, by decide⟩ ⟨38, by decide⟩ p hp j hj hq fz1_81_38 fz2_81_38
  · exact match_zero_fix ⟨82, by decide⟩ ⟨38, by decide⟩ p hp j hj hq fz1_82_38 fz2_82_38
  · exact match_zero_fix ⟨83, by decide⟩ ⟨38, by decide⟩ p hp j hj hq fz1_83_38 fz2_83_38
  · exact match_zero_fix ⟨84, by decide⟩ ⟨38, by decide⟩ p hp j hj hq fz1_84_38 fz2_84_38
  · exact match_zero_fix ⟨85, by decide⟩ ⟨38, by decide⟩ p hp j hj hq fz1_85_38 fz2_85_38
  · exact match_zero_fix ⟨86, by decide⟩ ⟨38, by decide⟩ p hp j hj hq fz1_86_38 fz2_86_38
  · exact match_zero_fix ⟨87, by decide⟩ ⟨38, by decide⟩ p hp j hj hq fz1_87_38 fz2_87_38
  · exact match_zero_fix ⟨88, by decide⟩ ⟨38, by decide⟩ p hp j hj hq fz1_88_38 fz2_88_38
  · exact match_zero_fix ⟨89, by decide⟩ ⟨38, by decide⟩ p hp j hj hq fz1_89_38 fz2_89_38
  · exact match_zero_fix ⟨90, by decide⟩ ⟨38, by decide⟩ p hp j hj hq fz1_90_38 fz2_90_38
  · exact match_zero_fix ⟨91, by decide⟩ ⟨38, by decide⟩ p hp j hj hq fz1_91_38 fz2_91_38
  · exact match_zero_fix ⟨92, by decide⟩ ⟨38, by decide⟩ p hp j hj hq fz1_92_38 fz2_92_38
  · exact match_zero_fix ⟨93, by decide⟩ ⟨38, by decide⟩ p hp j hj hq fz1_93_38 fz2_93_38
  · exact match_zero_fix ⟨94, by decide⟩ ⟨38, by decide⟩ p hp j hj hq fz1_94_38 fz2_94_38
  · exact match_zero_fix ⟨95, by decide⟩ ⟨38, by decide⟩ p hp j hj hq fz1_95_38 fz2_95_38
  · exact match_zero_fix ⟨96, by decide⟩ ⟨38, by decide⟩ p hp j hj hq fz1_96_38 fz2_96_38
  · exact match_zero_fix ⟨97, by decide⟩ ⟨38, by decide⟩ p hp j hj hq fz1_97_38 fz2_97_38
  · exact match_zero_fix ⟨98, by decide⟩ ⟨38, by decide⟩ p hp j hj hq fz1_98_38 fz2_98_38
  · exact match_zero_fix ⟨99, by decide⟩ ⟨38, by decide⟩ p hp j hj hq fz1_99_38 fz2_99_38
  · exact pair_100_38 p hp hrep j hj hq
  · exact match_zero_fix ⟨101, by decide⟩ ⟨38, by decide⟩ p hp j hj hq fz1_101_38 fz2_101_38
  · exact match_zero_fix ⟨102, by decide⟩ ⟨38, by decide⟩ p hp j hj hq fz1_102_38 fz2_102_38
  · exact match_zero_fix ⟨103, by decide⟩ ⟨38, by decide⟩ p hp j hj hq fz1_103_38 fz2_103_38
  · exact match_zero_fix ⟨104, by decide⟩ ⟨38, by decide⟩ p hp j hj hq fz1_104_38 fz2_104_38
  · exact match_zero_fix ⟨105, by decide⟩ ⟨38, by decide⟩ p hp j hj hq fz1_105_38 fz2_105_38
  · exact match_zero_fix ⟨106, by decide⟩ ⟨38, by decide⟩ p hp j hj hq fz1_106_38 fz2_106_38
  · exact match_zero_fix ⟨107, by decide⟩ ⟨38, by decide⟩ p hp j hj hq fz1_107_38 fz2_107_38
  · exact match_zero_fix ⟨108, by decide⟩ ⟨38, by decide⟩ p hp j hj hq fz1_108_38 fz2_108_38
  · exact match_zero_fix ⟨109, by decide⟩ ⟨38, by decide⟩ p hp j hj hq fz1_109_38 fz2_109_38
  · exact match_zero_fix ⟨110, by decide⟩ ⟨38, by decide⟩ p hp j hj hq fz1_110_38 fz2_110_38
  · exact match_zero_fix ⟨111, by decide⟩ ⟨38, by decide⟩ p hp j hj hq fz1_111_38 fz2_111_38
  · exact match_zero_fix ⟨112, by decide⟩ ⟨38, by decide⟩ p hp j hj hq fz1_112_38 fz2_112_38
  · exact match_zero_fix ⟨113, by decide⟩ ⟨38, by decide⟩ p hp j hj hq fz1_113_38 fz2_113_38
  · exact match_zero_fix ⟨114, by decide⟩ ⟨38, by decide⟩ p hp j hj hq fz1_114_38 fz2_114_38
  · exact match_zero_fix ⟨115, by decide⟩ ⟨38, by decide⟩ p hp j hj hq fz1_115_38 fz2_115_38
  · exact pair_116_38 p hp hrep j hj hq
  · exact match_zero_fix ⟨117, by decide⟩ ⟨38, by decide⟩ p hp j hj hq fz1_117_38 fz2_117_38
  · exact match_zero_fix ⟨118, by decide⟩ ⟨38, by decide⟩ p hp j hj hq fz1_118_38 fz2_118_38
  · exact match_zero_fix ⟨119, by decide⟩ ⟨38, by decide⟩ p hp j hj hq fz1_119_38 fz2_119_38
  · exact match_zero_fix ⟨120, by decide⟩ ⟨38, by decide⟩ p hp j hj hq fz1_120_38 fz2_120_38
  · exact match_zero_fix ⟨121, by decide⟩ ⟨38, by decide⟩ p hp j hj hq fz1_121_38 fz2_121_38
  · exact match_zero_fix ⟨122, by decide⟩ ⟨38, by decide⟩ p hp j hj hq fz1_122_38 fz2_122_38
  · exact pair_123_38 p hp hrep j hj hq
  · exact match_zero_fix ⟨124, by decide⟩ ⟨38, by decide⟩ p hp j hj hq fz1_124_38 fz2_124_38
  · exact match_zero_fix ⟨125, by decide⟩ ⟨38, by decide⟩ p hp j hj hq fz1_125_38 fz2_125_38
  · exact match_zero_fix ⟨126, by decide⟩ ⟨38, by decide⟩ p hp j hj hq fz1_126_38 fz2_126_38
  · exact match_zero_fix ⟨127, by decide⟩ ⟨38, by decide⟩ p hp j hj hq fz1_127_38 fz2_127_38
  · exact match_zero_fix ⟨128, by decide⟩ ⟨38, by decide⟩ p hp j hj hq fz1_128_38 fz2_128_38
  · exact match_zero_fix ⟨129, by decide⟩ ⟨38, by decide⟩ p hp j hj hq fz1_129_38 fz2_129_38
  · exact pair_130_38 p hp hrep j hj hq
  · exact match_zero_fix ⟨131, by decide⟩ ⟨38, by decide⟩ p hp j hj hq fz1_131_38 fz2_131_38
  · exact pair_132_38 p hp hrep j hj hq
  · exact match_zero_fix ⟨133, by decide⟩ ⟨38, by decide⟩ p hp j hj hq fz1_133_38 fz2_133_38
  · exact match_zero_fix ⟨134, by decide⟩ ⟨38, by decide⟩ p hp j hj hq fz1_134_38 fz2_134_38
  · exact match_zero_fix ⟨135, by decide⟩ ⟨38, by decide⟩ p hp j hj hq fz1_135_38 fz2_135_38
  · exact match_zero_fix ⟨136, by decide⟩ ⟨38, by decide⟩ p hp j hj hq fz1_136_38 fz2_136_38
  · exact match_zero_fix ⟨137, by decide⟩ ⟨38, by decide⟩ p hp j hj hq fz1_137_38 fz2_137_38
  · exact match_zero_fix ⟨138, by decide⟩ ⟨38, by decide⟩ p hp j hj hq fz1_138_38 fz2_138_38
  · exact pair_139_38 p hp hrep j hj hq
  · exact match_zero_fix ⟨140, by decide⟩ ⟨38, by decide⟩ p hp j hj hq fz1_140_38 fz2_140_38
  · exact match_zero_fix ⟨141, by decide⟩ ⟨38, by decide⟩ p hp j hj hq fz1_141_38 fz2_141_38
  · exact match_zero_fix ⟨142, by decide⟩ ⟨38, by decide⟩ p hp j hj hq fz1_142_38 fz2_142_38
  · exact match_zero_fix ⟨143, by decide⟩ ⟨38, by decide⟩ p hp j hj hq fz1_143_38 fz2_143_38
  · exact pair_144_38 p hp hrep j hj hq
  · exact match_zero_fix ⟨145, by decide⟩ ⟨38, by decide⟩ p hp j hj hq fz1_145_38 fz2_145_38
  · exact match_zero_fix ⟨146, by decide⟩ ⟨38, by decide⟩ p hp j hj hq fz1_146_38 fz2_146_38
  · exact pair_147_38 p hp hrep j hj hq

theorem master_39 (p : Nat) (hp : p < (Q2.transData.getD 39 []).length)
    (hrep : (Q2.cosetIsRep.getD 39 []).getD p false = true)
    (rK : Fin 148) (j : Nat) (hj : j < (repChars.getD rK.val []).length)
    (hq : (normIsRep.getD rK.val []).getD j false = true) :
    species (Q2.reps (⟨39, by decide⟩ : Fin 148)) (colE2 ⟨39, by decide⟩ p hp)
        (rowE2 rK j hj hq)
      = species (reps (⟨39, by decide⟩ : Fin 148))
        (colE1 ⟨39, by decide⟩ p (transLenTr ⟨39, by decide⟩ p hp)) (rowE1 rK j hj) := by
  rcases rK with ⟨nK, hnK⟩; interval_cases nK
  · exact match_zero_len ⟨0, by decide⟩ ⟨39, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨1, by decide⟩ ⟨39, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨2, by decide⟩ ⟨39, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨3, by decide⟩ ⟨39, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨4, by decide⟩ ⟨39, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨5, by decide⟩ ⟨39, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨6, by decide⟩ ⟨39, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨7, by decide⟩ ⟨39, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨8, by decide⟩ ⟨39, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨9, by decide⟩ ⟨39, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨10, by decide⟩ ⟨39, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨11, by decide⟩ ⟨39, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨12, by decide⟩ ⟨39, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_fix ⟨13, by decide⟩ ⟨39, by decide⟩ p hp j hj hq fz1_13_39 fz2_13_39
  · exact match_zero_fix ⟨14, by decide⟩ ⟨39, by decide⟩ p hp j hj hq fz1_14_39 fz2_14_39
  · exact match_zero_fix ⟨15, by decide⟩ ⟨39, by decide⟩ p hp j hj hq fz1_15_39 fz2_15_39
  · exact match_zero_fix ⟨16, by decide⟩ ⟨39, by decide⟩ p hp j hj hq fz1_16_39 fz2_16_39
  · exact match_zero_fix ⟨17, by decide⟩ ⟨39, by decide⟩ p hp j hj hq fz1_17_39 fz2_17_39
  · exact match_zero_fix ⟨18, by decide⟩ ⟨39, by decide⟩ p hp j hj hq fz1_18_39 fz2_18_39
  · exact match_zero_fix ⟨19, by decide⟩ ⟨39, by decide⟩ p hp j hj hq fz1_19_39 fz2_19_39
  · exact match_zero_fix ⟨20, by decide⟩ ⟨39, by decide⟩ p hp j hj hq fz1_20_39 fz2_20_39
  · exact match_zero_fix ⟨21, by decide⟩ ⟨39, by decide⟩ p hp j hj hq fz1_21_39 fz2_21_39
  · exact match_zero_fix ⟨22, by decide⟩ ⟨39, by decide⟩ p hp j hj hq fz1_22_39 fz2_22_39
  · exact match_zero_fix ⟨23, by decide⟩ ⟨39, by decide⟩ p hp j hj hq fz1_23_39 fz2_23_39
  · exact match_zero_fix ⟨24, by decide⟩ ⟨39, by decide⟩ p hp j hj hq fz1_24_39 fz2_24_39
  · exact match_zero_fix ⟨25, by decide⟩ ⟨39, by decide⟩ p hp j hj hq fz1_25_39 fz2_25_39
  · exact match_zero_fix ⟨26, by decide⟩ ⟨39, by decide⟩ p hp j hj hq fz1_26_39 fz2_26_39
  · exact match_zero_fix ⟨27, by decide⟩ ⟨39, by decide⟩ p hp j hj hq fz1_27_39 fz2_27_39
  · exact match_zero_fix ⟨28, by decide⟩ ⟨39, by decide⟩ p hp j hj hq fz1_28_39 fz2_28_39
  · exact match_zero_fix ⟨29, by decide⟩ ⟨39, by decide⟩ p hp j hj hq fz1_29_39 fz2_29_39
  · exact match_zero_fix ⟨30, by decide⟩ ⟨39, by decide⟩ p hp j hj hq fz1_30_39 fz2_30_39
  · exact match_zero_fix ⟨31, by decide⟩ ⟨39, by decide⟩ p hp j hj hq fz1_31_39 fz2_31_39
  · exact match_zero_fix ⟨32, by decide⟩ ⟨39, by decide⟩ p hp j hj hq fz1_32_39 fz2_32_39
  · exact match_zero_fix ⟨33, by decide⟩ ⟨39, by decide⟩ p hp j hj hq fz1_33_39 fz2_33_39
  · exact match_zero_fix ⟨34, by decide⟩ ⟨39, by decide⟩ p hp j hj hq fz1_34_39 fz2_34_39
  · exact match_zero_fix ⟨35, by decide⟩ ⟨39, by decide⟩ p hp j hj hq fz1_35_39 fz2_35_39
  · exact match_zero_fix ⟨36, by decide⟩ ⟨39, by decide⟩ p hp j hj hq fz1_36_39 fz2_36_39
  · exact match_zero_fix ⟨37, by decide⟩ ⟨39, by decide⟩ p hp j hj hq fz1_37_39 fz2_37_39
  · exact match_zero_fix ⟨38, by decide⟩ ⟨39, by decide⟩ p hp j hj hq fz1_38_39 fz2_38_39
  · exact pair_39_39 p hp hrep j hj hq
  · exact match_zero_fix ⟨40, by decide⟩ ⟨39, by decide⟩ p hp j hj hq fz1_40_39 fz2_40_39
  · exact match_zero_fix ⟨41, by decide⟩ ⟨39, by decide⟩ p hp j hj hq fz1_41_39 fz2_41_39
  · exact match_zero_fix ⟨42, by decide⟩ ⟨39, by decide⟩ p hp j hj hq fz1_42_39 fz2_42_39
  · exact match_zero_fix ⟨43, by decide⟩ ⟨39, by decide⟩ p hp j hj hq fz1_43_39 fz2_43_39
  · exact match_zero_fix ⟨44, by decide⟩ ⟨39, by decide⟩ p hp j hj hq fz1_44_39 fz2_44_39
  · exact match_zero_fix ⟨45, by decide⟩ ⟨39, by decide⟩ p hp j hj hq fz1_45_39 fz2_45_39
  · exact match_zero_fix ⟨46, by decide⟩ ⟨39, by decide⟩ p hp j hj hq fz1_46_39 fz2_46_39
  · exact match_zero_fix ⟨47, by decide⟩ ⟨39, by decide⟩ p hp j hj hq fz1_47_39 fz2_47_39
  · exact match_zero_fix ⟨48, by decide⟩ ⟨39, by decide⟩ p hp j hj hq fz1_48_39 fz2_48_39
  · exact match_zero_fix ⟨49, by decide⟩ ⟨39, by decide⟩ p hp j hj hq fz1_49_39 fz2_49_39
  · exact match_zero_fix ⟨50, by decide⟩ ⟨39, by decide⟩ p hp j hj hq fz1_50_39 fz2_50_39
  · exact match_zero_fix ⟨51, by decide⟩ ⟨39, by decide⟩ p hp j hj hq fz1_51_39 fz2_51_39
  · exact match_zero_fix ⟨52, by decide⟩ ⟨39, by decide⟩ p hp j hj hq fz1_52_39 fz2_52_39
  · exact match_zero_fix ⟨53, by decide⟩ ⟨39, by decide⟩ p hp j hj hq fz1_53_39 fz2_53_39
  · exact match_zero_fix ⟨54, by decide⟩ ⟨39, by decide⟩ p hp j hj hq fz1_54_39 fz2_54_39
  · exact match_zero_fix ⟨55, by decide⟩ ⟨39, by decide⟩ p hp j hj hq fz1_55_39 fz2_55_39
  · exact match_zero_fix ⟨56, by decide⟩ ⟨39, by decide⟩ p hp j hj hq fz1_56_39 fz2_56_39
  · exact match_zero_fix ⟨57, by decide⟩ ⟨39, by decide⟩ p hp j hj hq fz1_57_39 fz2_57_39
  · exact match_zero_fix ⟨58, by decide⟩ ⟨39, by decide⟩ p hp j hj hq fz1_58_39 fz2_58_39
  · exact match_zero_fix ⟨59, by decide⟩ ⟨39, by decide⟩ p hp j hj hq fz1_59_39 fz2_59_39
  · exact pair_60_39 p hp hrep j hj hq
  · exact pair_61_39 p hp hrep j hj hq
  · exact pair_62_39 p hp hrep j hj hq
  · exact pair_63_39 p hp hrep j hj hq
  · exact pair_64_39 p hp hrep j hj hq
  · exact match_zero_fix ⟨65, by decide⟩ ⟨39, by decide⟩ p hp j hj hq fz1_65_39 fz2_65_39
  · exact match_zero_fix ⟨66, by decide⟩ ⟨39, by decide⟩ p hp j hj hq fz1_66_39 fz2_66_39
  · exact match_zero_fix ⟨67, by decide⟩ ⟨39, by decide⟩ p hp j hj hq fz1_67_39 fz2_67_39
  · exact match_zero_fix ⟨68, by decide⟩ ⟨39, by decide⟩ p hp j hj hq fz1_68_39 fz2_68_39
  · exact match_zero_fix ⟨69, by decide⟩ ⟨39, by decide⟩ p hp j hj hq fz1_69_39 fz2_69_39
  · exact match_zero_fix ⟨70, by decide⟩ ⟨39, by decide⟩ p hp j hj hq fz1_70_39 fz2_70_39
  · exact match_zero_fix ⟨71, by decide⟩ ⟨39, by decide⟩ p hp j hj hq fz1_71_39 fz2_71_39
  · exact match_zero_fix ⟨72, by decide⟩ ⟨39, by decide⟩ p hp j hj hq fz1_72_39 fz2_72_39
  · exact match_zero_fix ⟨73, by decide⟩ ⟨39, by decide⟩ p hp j hj hq fz1_73_39 fz2_73_39
  · exact match_zero_fix ⟨74, by decide⟩ ⟨39, by decide⟩ p hp j hj hq fz1_74_39 fz2_74_39
  · exact match_zero_fix ⟨75, by decide⟩ ⟨39, by decide⟩ p hp j hj hq fz1_75_39 fz2_75_39
  · exact match_zero_fix ⟨76, by decide⟩ ⟨39, by decide⟩ p hp j hj hq fz1_76_39 fz2_76_39
  · exact match_zero_fix ⟨77, by decide⟩ ⟨39, by decide⟩ p hp j hj hq fz1_77_39 fz2_77_39
  · exact match_zero_fix ⟨78, by decide⟩ ⟨39, by decide⟩ p hp j hj hq fz1_78_39 fz2_78_39
  · exact match_zero_fix ⟨79, by decide⟩ ⟨39, by decide⟩ p hp j hj hq fz1_79_39 fz2_79_39
  · exact match_zero_fix ⟨80, by decide⟩ ⟨39, by decide⟩ p hp j hj hq fz1_80_39 fz2_80_39
  · exact match_zero_fix ⟨81, by decide⟩ ⟨39, by decide⟩ p hp j hj hq fz1_81_39 fz2_81_39
  · exact match_zero_fix ⟨82, by decide⟩ ⟨39, by decide⟩ p hp j hj hq fz1_82_39 fz2_82_39
  · exact match_zero_fix ⟨83, by decide⟩ ⟨39, by decide⟩ p hp j hj hq fz1_83_39 fz2_83_39
  · exact match_zero_fix ⟨84, by decide⟩ ⟨39, by decide⟩ p hp j hj hq fz1_84_39 fz2_84_39
  · exact match_zero_fix ⟨85, by decide⟩ ⟨39, by decide⟩ p hp j hj hq fz1_85_39 fz2_85_39
  · exact match_zero_fix ⟨86, by decide⟩ ⟨39, by decide⟩ p hp j hj hq fz1_86_39 fz2_86_39
  · exact match_zero_fix ⟨87, by decide⟩ ⟨39, by decide⟩ p hp j hj hq fz1_87_39 fz2_87_39
  · exact match_zero_fix ⟨88, by decide⟩ ⟨39, by decide⟩ p hp j hj hq fz1_88_39 fz2_88_39
  · exact match_zero_fix ⟨89, by decide⟩ ⟨39, by decide⟩ p hp j hj hq fz1_89_39 fz2_89_39
  · exact match_zero_fix ⟨90, by decide⟩ ⟨39, by decide⟩ p hp j hj hq fz1_90_39 fz2_90_39
  · exact match_zero_fix ⟨91, by decide⟩ ⟨39, by decide⟩ p hp j hj hq fz1_91_39 fz2_91_39
  · exact match_zero_fix ⟨92, by decide⟩ ⟨39, by decide⟩ p hp j hj hq fz1_92_39 fz2_92_39
  · exact match_zero_fix ⟨93, by decide⟩ ⟨39, by decide⟩ p hp j hj hq fz1_93_39 fz2_93_39
  · exact match_zero_fix ⟨94, by decide⟩ ⟨39, by decide⟩ p hp j hj hq fz1_94_39 fz2_94_39
  · exact match_zero_fix ⟨95, by decide⟩ ⟨39, by decide⟩ p hp j hj hq fz1_95_39 fz2_95_39
  · exact match_zero_fix ⟨96, by decide⟩ ⟨39, by decide⟩ p hp j hj hq fz1_96_39 fz2_96_39
  · exact match_zero_fix ⟨97, by decide⟩ ⟨39, by decide⟩ p hp j hj hq fz1_97_39 fz2_97_39
  · exact match_zero_fix ⟨98, by decide⟩ ⟨39, by decide⟩ p hp j hj hq fz1_98_39 fz2_98_39
  · exact match_zero_fix ⟨99, by decide⟩ ⟨39, by decide⟩ p hp j hj hq fz1_99_39 fz2_99_39
  · exact match_zero_fix ⟨100, by decide⟩ ⟨39, by decide⟩ p hp j hj hq fz1_100_39 fz2_100_39
  · exact pair_101_39 p hp hrep j hj hq
  · exact match_zero_fix ⟨102, by decide⟩ ⟨39, by decide⟩ p hp j hj hq fz1_102_39 fz2_102_39
  · exact match_zero_fix ⟨103, by decide⟩ ⟨39, by decide⟩ p hp j hj hq fz1_103_39 fz2_103_39
  · exact match_zero_fix ⟨104, by decide⟩ ⟨39, by decide⟩ p hp j hj hq fz1_104_39 fz2_104_39
  · exact match_zero_fix ⟨105, by decide⟩ ⟨39, by decide⟩ p hp j hj hq fz1_105_39 fz2_105_39
  · exact match_zero_fix ⟨106, by decide⟩ ⟨39, by decide⟩ p hp j hj hq fz1_106_39 fz2_106_39
  · exact match_zero_fix ⟨107, by decide⟩ ⟨39, by decide⟩ p hp j hj hq fz1_107_39 fz2_107_39
  · exact match_zero_fix ⟨108, by decide⟩ ⟨39, by decide⟩ p hp j hj hq fz1_108_39 fz2_108_39
  · exact match_zero_fix ⟨109, by decide⟩ ⟨39, by decide⟩ p hp j hj hq fz1_109_39 fz2_109_39
  · exact match_zero_fix ⟨110, by decide⟩ ⟨39, by decide⟩ p hp j hj hq fz1_110_39 fz2_110_39
  · exact match_zero_fix ⟨111, by decide⟩ ⟨39, by decide⟩ p hp j hj hq fz1_111_39 fz2_111_39
  · exact match_zero_fix ⟨112, by decide⟩ ⟨39, by decide⟩ p hp j hj hq fz1_112_39 fz2_112_39
  · exact match_zero_fix ⟨113, by decide⟩ ⟨39, by decide⟩ p hp j hj hq fz1_113_39 fz2_113_39
  · exact match_zero_fix ⟨114, by decide⟩ ⟨39, by decide⟩ p hp j hj hq fz1_114_39 fz2_114_39
  · exact match_zero_fix ⟨115, by decide⟩ ⟨39, by decide⟩ p hp j hj hq fz1_115_39 fz2_115_39
  · exact match_zero_fix ⟨116, by decide⟩ ⟨39, by decide⟩ p hp j hj hq fz1_116_39 fz2_116_39
  · exact pair_117_39 p hp hrep j hj hq
  · exact match_zero_fix ⟨118, by decide⟩ ⟨39, by decide⟩ p hp j hj hq fz1_118_39 fz2_118_39
  · exact match_zero_fix ⟨119, by decide⟩ ⟨39, by decide⟩ p hp j hj hq fz1_119_39 fz2_119_39
  · exact match_zero_fix ⟨120, by decide⟩ ⟨39, by decide⟩ p hp j hj hq fz1_120_39 fz2_120_39
  · exact match_zero_fix ⟨121, by decide⟩ ⟨39, by decide⟩ p hp j hj hq fz1_121_39 fz2_121_39
  · exact match_zero_fix ⟨122, by decide⟩ ⟨39, by decide⟩ p hp j hj hq fz1_122_39 fz2_122_39
  · exact match_zero_fix ⟨123, by decide⟩ ⟨39, by decide⟩ p hp j hj hq fz1_123_39 fz2_123_39
  · exact pair_124_39 p hp hrep j hj hq
  · exact match_zero_fix ⟨125, by decide⟩ ⟨39, by decide⟩ p hp j hj hq fz1_125_39 fz2_125_39
  · exact pair_126_39 p hp hrep j hj hq
  · exact match_zero_fix ⟨127, by decide⟩ ⟨39, by decide⟩ p hp j hj hq fz1_127_39 fz2_127_39
  · exact match_zero_fix ⟨128, by decide⟩ ⟨39, by decide⟩ p hp j hj hq fz1_128_39 fz2_128_39
  · exact match_zero_fix ⟨129, by decide⟩ ⟨39, by decide⟩ p hp j hj hq fz1_129_39 fz2_129_39
  · exact match_zero_fix ⟨130, by decide⟩ ⟨39, by decide⟩ p hp j hj hq fz1_130_39 fz2_130_39
  · exact match_zero_fix ⟨131, by decide⟩ ⟨39, by decide⟩ p hp j hj hq fz1_131_39 fz2_131_39
  · exact match_zero_fix ⟨132, by decide⟩ ⟨39, by decide⟩ p hp j hj hq fz1_132_39 fz2_132_39
  · exact pair_133_39 p hp hrep j hj hq
  · exact match_zero_fix ⟨134, by decide⟩ ⟨39, by decide⟩ p hp j hj hq fz1_134_39 fz2_134_39
  · exact match_zero_fix ⟨135, by decide⟩ ⟨39, by decide⟩ p hp j hj hq fz1_135_39 fz2_135_39
  · exact match_zero_fix ⟨136, by decide⟩ ⟨39, by decide⟩ p hp j hj hq fz1_136_39 fz2_136_39
  · exact match_zero_fix ⟨137, by decide⟩ ⟨39, by decide⟩ p hp j hj hq fz1_137_39 fz2_137_39
  · exact match_zero_fix ⟨138, by decide⟩ ⟨39, by decide⟩ p hp j hj hq fz1_138_39 fz2_138_39
  · exact match_zero_fix ⟨139, by decide⟩ ⟨39, by decide⟩ p hp j hj hq fz1_139_39 fz2_139_39
  · exact pair_140_39 p hp hrep j hj hq
  · exact match_zero_fix ⟨141, by decide⟩ ⟨39, by decide⟩ p hp j hj hq fz1_141_39 fz2_141_39
  · exact match_zero_fix ⟨142, by decide⟩ ⟨39, by decide⟩ p hp j hj hq fz1_142_39 fz2_142_39
  · exact match_zero_fix ⟨143, by decide⟩ ⟨39, by decide⟩ p hp j hj hq fz1_143_39 fz2_143_39
  · exact pair_144_39 p hp hrep j hj hq
  · exact match_zero_fix ⟨145, by decide⟩ ⟨39, by decide⟩ p hp j hj hq fz1_145_39 fz2_145_39
  · exact match_zero_fix ⟨146, by decide⟩ ⟨39, by decide⟩ p hp j hj hq fz1_146_39 fz2_146_39
  · exact pair_147_39 p hp hrep j hj hq

end LeanDring.P5Presentation
