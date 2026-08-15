/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Data.FixZero.C001
import LeanDring.P5.Data.FixZero.C002
import LeanDring.P5.Data.FixZero.C011
import LeanDring.P5.Data.FixZero.C012
import LeanDring.P5.Data.FixZero.C013
import LeanDring.P5.Data.FixZero.C014
import LeanDring.P5.Data.FixZero.C015
import LeanDring.P5.Data.FixZero.C016
import LeanDring.P5.Data.FixZero.C017
import LeanDring.P5.Data.FixZero.C018
import LeanDring.P5.Data.FixZero.C019
import LeanDring.P5.Data.FixZero.C020
import LeanDring.P5.Data.FixZero.C003
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
import LeanDring.P5.Data.FixZero.C004
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
import LeanDring.P5.Data.FixZero.C005
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
import LeanDring.P5.Data.FixZero.C006
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
import LeanDring.P5.Data.FixZero.C007
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
import LeanDring.P5.Data.FixZero.C008
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
import LeanDring.P5.Data.FixZero.C009
import LeanDring.P5.Data.FixZero.C081
import LeanDring.P5.Data.FixZero.C082
import LeanDring.P5.Data.FixZero.C083
import LeanDring.P5.Data.FixZero.C084
import LeanDring.P5.Data.FixZero.C085
import LeanDring.P5.Data.FixZero.C086
import LeanDring.P5.Data.FixZero.C087
import LeanDring.P5.Data.FixZero.C088
import LeanDring.P5.Data.FixZero.C010
import LeanDring.P5.Certificate.RingIsomorphism.MatchCore
import LeanDring.P5.Data.MatchPair.C001
import LeanDring.P5.Data.MatchPair.C002
import LeanDring.P5.Data.MatchPair.C011
import LeanDring.P5.Data.MatchPair.C003
import LeanDring.P5.Data.MatchPair.C004
import LeanDring.P5.Data.MatchPair.C005
import LeanDring.P5.Data.MatchPair.C006
import LeanDring.P5.Data.MatchPair.C007
import LeanDring.P5.Data.MatchPair.C008
import LeanDring.P5.Data.MatchPair.C009
import LeanDring.P5.Data.MatchPair.C010

/-! # Stage-5 per-column-class master theorems, chunk 1 (auto-emitted).  -/

namespace LeanDring.P5Presentation

open MulAction Finset LeanDring.DRing LeanDring.MonGSet

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.style.longLine false

theorem master_8 (p : Nat) (hp : p < (Q2.transData.getD 8 []).length)
    (hrep : (Q2.cosetIsRep.getD 8 []).getD p false = true)
    (rK : Fin 148) (j : Nat) (hj : j < (repChars.getD rK.val []).length)
    (hq : (normIsRep.getD rK.val []).getD j false = true) :
    species (Q2.reps (⟨8, by decide⟩ : Fin 148)) (colE2 ⟨8, by decide⟩ p hp)
        (rowE2 rK j hj hq)
      = species (reps (⟨8, by decide⟩ : Fin 148))
        (colE1 ⟨8, by decide⟩ p (transLenTr ⟨8, by decide⟩ p hp)) (rowE1 rK j hj) := by
  rcases rK with ⟨nK, hnK⟩; interval_cases nK
  · exact match_zero_len ⟨0, by decide⟩ ⟨8, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_fix ⟨1, by decide⟩ ⟨8, by decide⟩ p hp j hj hq fz1_1_8 fz2_1_8
  · exact match_zero_fix ⟨2, by decide⟩ ⟨8, by decide⟩ p hp j hj hq fz1_2_8 fz2_2_8
  · exact match_zero_fix ⟨3, by decide⟩ ⟨8, by decide⟩ p hp j hj hq fz1_3_8 fz2_3_8
  · exact match_zero_fix ⟨4, by decide⟩ ⟨8, by decide⟩ p hp j hj hq fz1_4_8 fz2_4_8
  · exact match_zero_fix ⟨5, by decide⟩ ⟨8, by decide⟩ p hp j hj hq fz1_5_8 fz2_5_8
  · exact match_zero_fix ⟨6, by decide⟩ ⟨8, by decide⟩ p hp j hj hq fz1_6_8 fz2_6_8
  · exact match_zero_fix ⟨7, by decide⟩ ⟨8, by decide⟩ p hp j hj hq fz1_7_8 fz2_7_8
  · exact pair_8_8 p hp hrep j hj hq
  · exact match_zero_fix ⟨9, by decide⟩ ⟨8, by decide⟩ p hp j hj hq fz1_9_8 fz2_9_8
  · exact match_zero_fix ⟨10, by decide⟩ ⟨8, by decide⟩ p hp j hj hq fz1_10_8 fz2_10_8
  · exact match_zero_fix ⟨11, by decide⟩ ⟨8, by decide⟩ p hp j hj hq fz1_11_8 fz2_11_8
  · exact match_zero_fix ⟨12, by decide⟩ ⟨8, by decide⟩ p hp j hj hq fz1_12_8 fz2_12_8
  · exact pair_13_8 p hp hrep j hj hq
  · exact match_zero_fix ⟨14, by decide⟩ ⟨8, by decide⟩ p hp j hj hq fz1_14_8 fz2_14_8
  · exact match_zero_fix ⟨15, by decide⟩ ⟨8, by decide⟩ p hp j hj hq fz1_15_8 fz2_15_8
  · exact match_zero_fix ⟨16, by decide⟩ ⟨8, by decide⟩ p hp j hj hq fz1_16_8 fz2_16_8
  · exact match_zero_fix ⟨17, by decide⟩ ⟨8, by decide⟩ p hp j hj hq fz1_17_8 fz2_17_8
  · exact match_zero_fix ⟨18, by decide⟩ ⟨8, by decide⟩ p hp j hj hq fz1_18_8 fz2_18_8
  · exact match_zero_fix ⟨19, by decide⟩ ⟨8, by decide⟩ p hp j hj hq fz1_19_8 fz2_19_8
  · exact match_zero_fix ⟨20, by decide⟩ ⟨8, by decide⟩ p hp j hj hq fz1_20_8 fz2_20_8
  · exact match_zero_fix ⟨21, by decide⟩ ⟨8, by decide⟩ p hp j hj hq fz1_21_8 fz2_21_8
  · exact match_zero_fix ⟨22, by decide⟩ ⟨8, by decide⟩ p hp j hj hq fz1_22_8 fz2_22_8
  · exact match_zero_fix ⟨23, by decide⟩ ⟨8, by decide⟩ p hp j hj hq fz1_23_8 fz2_23_8
  · exact match_zero_fix ⟨24, by decide⟩ ⟨8, by decide⟩ p hp j hj hq fz1_24_8 fz2_24_8
  · exact match_zero_fix ⟨25, by decide⟩ ⟨8, by decide⟩ p hp j hj hq fz1_25_8 fz2_25_8
  · exact pair_26_8 p hp hrep j hj hq
  · exact match_zero_fix ⟨27, by decide⟩ ⟨8, by decide⟩ p hp j hj hq fz1_27_8 fz2_27_8
  · exact match_zero_fix ⟨28, by decide⟩ ⟨8, by decide⟩ p hp j hj hq fz1_28_8 fz2_28_8
  · exact match_zero_fix ⟨29, by decide⟩ ⟨8, by decide⟩ p hp j hj hq fz1_29_8 fz2_29_8
  · exact match_zero_fix ⟨30, by decide⟩ ⟨8, by decide⟩ p hp j hj hq fz1_30_8 fz2_30_8
  · exact match_zero_fix ⟨31, by decide⟩ ⟨8, by decide⟩ p hp j hj hq fz1_31_8 fz2_31_8
  · exact match_zero_fix ⟨32, by decide⟩ ⟨8, by decide⟩ p hp j hj hq fz1_32_8 fz2_32_8
  · exact match_zero_fix ⟨33, by decide⟩ ⟨8, by decide⟩ p hp j hj hq fz1_33_8 fz2_33_8
  · exact match_zero_fix ⟨34, by decide⟩ ⟨8, by decide⟩ p hp j hj hq fz1_34_8 fz2_34_8
  · exact match_zero_fix ⟨35, by decide⟩ ⟨8, by decide⟩ p hp j hj hq fz1_35_8 fz2_35_8
  · exact match_zero_fix ⟨36, by decide⟩ ⟨8, by decide⟩ p hp j hj hq fz1_36_8 fz2_36_8
  · exact match_zero_fix ⟨37, by decide⟩ ⟨8, by decide⟩ p hp j hj hq fz1_37_8 fz2_37_8
  · exact match_zero_fix ⟨38, by decide⟩ ⟨8, by decide⟩ p hp j hj hq fz1_38_8 fz2_38_8
  · exact match_zero_fix ⟨39, by decide⟩ ⟨8, by decide⟩ p hp j hj hq fz1_39_8 fz2_39_8
  · exact match_zero_fix ⟨40, by decide⟩ ⟨8, by decide⟩ p hp j hj hq fz1_40_8 fz2_40_8
  · exact match_zero_fix ⟨41, by decide⟩ ⟨8, by decide⟩ p hp j hj hq fz1_41_8 fz2_41_8
  · exact match_zero_fix ⟨42, by decide⟩ ⟨8, by decide⟩ p hp j hj hq fz1_42_8 fz2_42_8
  · exact match_zero_fix ⟨43, by decide⟩ ⟨8, by decide⟩ p hp j hj hq fz1_43_8 fz2_43_8
  · exact match_zero_fix ⟨44, by decide⟩ ⟨8, by decide⟩ p hp j hj hq fz1_44_8 fz2_44_8
  · exact match_zero_fix ⟨45, by decide⟩ ⟨8, by decide⟩ p hp j hj hq fz1_45_8 fz2_45_8
  · exact match_zero_fix ⟨46, by decide⟩ ⟨8, by decide⟩ p hp j hj hq fz1_46_8 fz2_46_8
  · exact match_zero_fix ⟨47, by decide⟩ ⟨8, by decide⟩ p hp j hj hq fz1_47_8 fz2_47_8
  · exact match_zero_fix ⟨48, by decide⟩ ⟨8, by decide⟩ p hp j hj hq fz1_48_8 fz2_48_8
  · exact match_zero_fix ⟨49, by decide⟩ ⟨8, by decide⟩ p hp j hj hq fz1_49_8 fz2_49_8
  · exact match_zero_fix ⟨50, by decide⟩ ⟨8, by decide⟩ p hp j hj hq fz1_50_8 fz2_50_8
  · exact match_zero_fix ⟨51, by decide⟩ ⟨8, by decide⟩ p hp j hj hq fz1_51_8 fz2_51_8
  · exact match_zero_fix ⟨52, by decide⟩ ⟨8, by decide⟩ p hp j hj hq fz1_52_8 fz2_52_8
  · exact match_zero_fix ⟨53, by decide⟩ ⟨8, by decide⟩ p hp j hj hq fz1_53_8 fz2_53_8
  · exact match_zero_fix ⟨54, by decide⟩ ⟨8, by decide⟩ p hp j hj hq fz1_54_8 fz2_54_8
  · exact match_zero_fix ⟨55, by decide⟩ ⟨8, by decide⟩ p hp j hj hq fz1_55_8 fz2_55_8
  · exact match_zero_fix ⟨56, by decide⟩ ⟨8, by decide⟩ p hp j hj hq fz1_56_8 fz2_56_8
  · exact match_zero_fix ⟨57, by decide⟩ ⟨8, by decide⟩ p hp j hj hq fz1_57_8 fz2_57_8
  · exact match_zero_fix ⟨58, by decide⟩ ⟨8, by decide⟩ p hp j hj hq fz1_58_8 fz2_58_8
  · exact pair_59_8 p hp hrep j hj hq
  · exact match_zero_fix ⟨60, by decide⟩ ⟨8, by decide⟩ p hp j hj hq fz1_60_8 fz2_60_8
  · exact match_zero_fix ⟨61, by decide⟩ ⟨8, by decide⟩ p hp j hj hq fz1_61_8 fz2_61_8
  · exact match_zero_fix ⟨62, by decide⟩ ⟨8, by decide⟩ p hp j hj hq fz1_62_8 fz2_62_8
  · exact match_zero_fix ⟨63, by decide⟩ ⟨8, by decide⟩ p hp j hj hq fz1_63_8 fz2_63_8
  · exact pair_64_8 p hp hrep j hj hq
  · exact match_zero_fix ⟨65, by decide⟩ ⟨8, by decide⟩ p hp j hj hq fz1_65_8 fz2_65_8
  · exact match_zero_fix ⟨66, by decide⟩ ⟨8, by decide⟩ p hp j hj hq fz1_66_8 fz2_66_8
  · exact match_zero_fix ⟨67, by decide⟩ ⟨8, by decide⟩ p hp j hj hq fz1_67_8 fz2_67_8
  · exact match_zero_fix ⟨68, by decide⟩ ⟨8, by decide⟩ p hp j hj hq fz1_68_8 fz2_68_8
  · exact pair_69_8 p hp hrep j hj hq
  · exact match_zero_fix ⟨70, by decide⟩ ⟨8, by decide⟩ p hp j hj hq fz1_70_8 fz2_70_8
  · exact match_zero_fix ⟨71, by decide⟩ ⟨8, by decide⟩ p hp j hj hq fz1_71_8 fz2_71_8
  · exact match_zero_fix ⟨72, by decide⟩ ⟨8, by decide⟩ p hp j hj hq fz1_72_8 fz2_72_8
  · exact match_zero_fix ⟨73, by decide⟩ ⟨8, by decide⟩ p hp j hj hq fz1_73_8 fz2_73_8
  · exact pair_74_8 p hp hrep j hj hq
  · exact match_zero_fix ⟨75, by decide⟩ ⟨8, by decide⟩ p hp j hj hq fz1_75_8 fz2_75_8
  · exact match_zero_fix ⟨76, by decide⟩ ⟨8, by decide⟩ p hp j hj hq fz1_76_8 fz2_76_8
  · exact match_zero_fix ⟨77, by decide⟩ ⟨8, by decide⟩ p hp j hj hq fz1_77_8 fz2_77_8
  · exact match_zero_fix ⟨78, by decide⟩ ⟨8, by decide⟩ p hp j hj hq fz1_78_8 fz2_78_8
  · exact pair_79_8 p hp hrep j hj hq
  · exact pair_80_8 p hp hrep j hj hq
  · exact match_zero_fix ⟨81, by decide⟩ ⟨8, by decide⟩ p hp j hj hq fz1_81_8 fz2_81_8
  · exact match_zero_fix ⟨82, by decide⟩ ⟨8, by decide⟩ p hp j hj hq fz1_82_8 fz2_82_8
  · exact match_zero_fix ⟨83, by decide⟩ ⟨8, by decide⟩ p hp j hj hq fz1_83_8 fz2_83_8
  · exact match_zero_fix ⟨84, by decide⟩ ⟨8, by decide⟩ p hp j hj hq fz1_84_8 fz2_84_8
  · exact match_zero_fix ⟨85, by decide⟩ ⟨8, by decide⟩ p hp j hj hq fz1_85_8 fz2_85_8
  · exact match_zero_fix ⟨86, by decide⟩ ⟨8, by decide⟩ p hp j hj hq fz1_86_8 fz2_86_8
  · exact match_zero_fix ⟨87, by decide⟩ ⟨8, by decide⟩ p hp j hj hq fz1_87_8 fz2_87_8
  · exact match_zero_fix ⟨88, by decide⟩ ⟨8, by decide⟩ p hp j hj hq fz1_88_8 fz2_88_8
  · exact pair_89_8 p hp hrep j hj hq
  · exact match_zero_fix ⟨90, by decide⟩ ⟨8, by decide⟩ p hp j hj hq fz1_90_8 fz2_90_8
  · exact match_zero_fix ⟨91, by decide⟩ ⟨8, by decide⟩ p hp j hj hq fz1_91_8 fz2_91_8
  · exact match_zero_fix ⟨92, by decide⟩ ⟨8, by decide⟩ p hp j hj hq fz1_92_8 fz2_92_8
  · exact match_zero_fix ⟨93, by decide⟩ ⟨8, by decide⟩ p hp j hj hq fz1_93_8 fz2_93_8
  · exact match_zero_fix ⟨94, by decide⟩ ⟨8, by decide⟩ p hp j hj hq fz1_94_8 fz2_94_8
  · exact match_zero_fix ⟨95, by decide⟩ ⟨8, by decide⟩ p hp j hj hq fz1_95_8 fz2_95_8
  · exact match_zero_fix ⟨96, by decide⟩ ⟨8, by decide⟩ p hp j hj hq fz1_96_8 fz2_96_8
  · exact match_zero_fix ⟨97, by decide⟩ ⟨8, by decide⟩ p hp j hj hq fz1_97_8 fz2_97_8
  · exact match_zero_fix ⟨98, by decide⟩ ⟨8, by decide⟩ p hp j hj hq fz1_98_8 fz2_98_8
  · exact match_zero_fix ⟨99, by decide⟩ ⟨8, by decide⟩ p hp j hj hq fz1_99_8 fz2_99_8
  · exact match_zero_fix ⟨100, by decide⟩ ⟨8, by decide⟩ p hp j hj hq fz1_100_8 fz2_100_8
  · exact match_zero_fix ⟨101, by decide⟩ ⟨8, by decide⟩ p hp j hj hq fz1_101_8 fz2_101_8
  · exact match_zero_fix ⟨102, by decide⟩ ⟨8, by decide⟩ p hp j hj hq fz1_102_8 fz2_102_8
  · exact match_zero_fix ⟨103, by decide⟩ ⟨8, by decide⟩ p hp j hj hq fz1_103_8 fz2_103_8
  · exact match_zero_fix ⟨104, by decide⟩ ⟨8, by decide⟩ p hp j hj hq fz1_104_8 fz2_104_8
  · exact match_zero_fix ⟨105, by decide⟩ ⟨8, by decide⟩ p hp j hj hq fz1_105_8 fz2_105_8
  · exact match_zero_fix ⟨106, by decide⟩ ⟨8, by decide⟩ p hp j hj hq fz1_106_8 fz2_106_8
  · exact match_zero_fix ⟨107, by decide⟩ ⟨8, by decide⟩ p hp j hj hq fz1_107_8 fz2_107_8
  · exact match_zero_fix ⟨108, by decide⟩ ⟨8, by decide⟩ p hp j hj hq fz1_108_8 fz2_108_8
  · exact match_zero_fix ⟨109, by decide⟩ ⟨8, by decide⟩ p hp j hj hq fz1_109_8 fz2_109_8
  · exact match_zero_fix ⟨110, by decide⟩ ⟨8, by decide⟩ p hp j hj hq fz1_110_8 fz2_110_8
  · exact match_zero_fix ⟨111, by decide⟩ ⟨8, by decide⟩ p hp j hj hq fz1_111_8 fz2_111_8
  · exact match_zero_fix ⟨112, by decide⟩ ⟨8, by decide⟩ p hp j hj hq fz1_112_8 fz2_112_8
  · exact match_zero_fix ⟨113, by decide⟩ ⟨8, by decide⟩ p hp j hj hq fz1_113_8 fz2_113_8
  · exact match_zero_fix ⟨114, by decide⟩ ⟨8, by decide⟩ p hp j hj hq fz1_114_8 fz2_114_8
  · exact match_zero_fix ⟨115, by decide⟩ ⟨8, by decide⟩ p hp j hj hq fz1_115_8 fz2_115_8
  · exact pair_116_8 p hp hrep j hj hq
  · exact pair_117_8 p hp hrep j hj hq
  · exact pair_118_8 p hp hrep j hj hq
  · exact pair_119_8 p hp hrep j hj hq
  · exact pair_120_8 p hp hrep j hj hq
  · exact match_zero_fix ⟨121, by decide⟩ ⟨8, by decide⟩ p hp j hj hq fz1_121_8 fz2_121_8
  · exact match_zero_fix ⟨122, by decide⟩ ⟨8, by decide⟩ p hp j hj hq fz1_122_8 fz2_122_8
  · exact match_zero_fix ⟨123, by decide⟩ ⟨8, by decide⟩ p hp j hj hq fz1_123_8 fz2_123_8
  · exact match_zero_fix ⟨124, by decide⟩ ⟨8, by decide⟩ p hp j hj hq fz1_124_8 fz2_124_8
  · exact match_zero_fix ⟨125, by decide⟩ ⟨8, by decide⟩ p hp j hj hq fz1_125_8 fz2_125_8
  · exact match_zero_fix ⟨126, by decide⟩ ⟨8, by decide⟩ p hp j hj hq fz1_126_8 fz2_126_8
  · exact match_zero_fix ⟨127, by decide⟩ ⟨8, by decide⟩ p hp j hj hq fz1_127_8 fz2_127_8
  · exact match_zero_fix ⟨128, by decide⟩ ⟨8, by decide⟩ p hp j hj hq fz1_128_8 fz2_128_8
  · exact match_zero_fix ⟨129, by decide⟩ ⟨8, by decide⟩ p hp j hj hq fz1_129_8 fz2_129_8
  · exact match_zero_fix ⟨130, by decide⟩ ⟨8, by decide⟩ p hp j hj hq fz1_130_8 fz2_130_8
  · exact match_zero_fix ⟨131, by decide⟩ ⟨8, by decide⟩ p hp j hj hq fz1_131_8 fz2_131_8
  · exact match_zero_fix ⟨132, by decide⟩ ⟨8, by decide⟩ p hp j hj hq fz1_132_8 fz2_132_8
  · exact match_zero_fix ⟨133, by decide⟩ ⟨8, by decide⟩ p hp j hj hq fz1_133_8 fz2_133_8
  · exact match_zero_fix ⟨134, by decide⟩ ⟨8, by decide⟩ p hp j hj hq fz1_134_8 fz2_134_8
  · exact match_zero_fix ⟨135, by decide⟩ ⟨8, by decide⟩ p hp j hj hq fz1_135_8 fz2_135_8
  · exact match_zero_fix ⟨136, by decide⟩ ⟨8, by decide⟩ p hp j hj hq fz1_136_8 fz2_136_8
  · exact match_zero_fix ⟨137, by decide⟩ ⟨8, by decide⟩ p hp j hj hq fz1_137_8 fz2_137_8
  · exact match_zero_fix ⟨138, by decide⟩ ⟨8, by decide⟩ p hp j hj hq fz1_138_8 fz2_138_8
  · exact match_zero_fix ⟨139, by decide⟩ ⟨8, by decide⟩ p hp j hj hq fz1_139_8 fz2_139_8
  · exact match_zero_fix ⟨140, by decide⟩ ⟨8, by decide⟩ p hp j hj hq fz1_140_8 fz2_140_8
  · exact pair_141_8 p hp hrep j hj hq
  · exact match_zero_fix ⟨142, by decide⟩ ⟨8, by decide⟩ p hp j hj hq fz1_142_8 fz2_142_8
  · exact match_zero_fix ⟨143, by decide⟩ ⟨8, by decide⟩ p hp j hj hq fz1_143_8 fz2_143_8
  · exact match_zero_fix ⟨144, by decide⟩ ⟨8, by decide⟩ p hp j hj hq fz1_144_8 fz2_144_8
  · exact match_zero_fix ⟨145, by decide⟩ ⟨8, by decide⟩ p hp j hj hq fz1_145_8 fz2_145_8
  · exact match_zero_fix ⟨146, by decide⟩ ⟨8, by decide⟩ p hp j hj hq fz1_146_8 fz2_146_8
  · exact pair_147_8 p hp hrep j hj hq

theorem master_9 (p : Nat) (hp : p < (Q2.transData.getD 9 []).length)
    (hrep : (Q2.cosetIsRep.getD 9 []).getD p false = true)
    (rK : Fin 148) (j : Nat) (hj : j < (repChars.getD rK.val []).length)
    (hq : (normIsRep.getD rK.val []).getD j false = true) :
    species (Q2.reps (⟨9, by decide⟩ : Fin 148)) (colE2 ⟨9, by decide⟩ p hp)
        (rowE2 rK j hj hq)
      = species (reps (⟨9, by decide⟩ : Fin 148))
        (colE1 ⟨9, by decide⟩ p (transLenTr ⟨9, by decide⟩ p hp)) (rowE1 rK j hj) := by
  rcases rK with ⟨nK, hnK⟩; interval_cases nK
  · exact match_zero_len ⟨0, by decide⟩ ⟨9, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_fix ⟨1, by decide⟩ ⟨9, by decide⟩ p hp j hj hq fz1_1_9 fz2_1_9
  · exact match_zero_fix ⟨2, by decide⟩ ⟨9, by decide⟩ p hp j hj hq fz1_2_9 fz2_2_9
  · exact match_zero_fix ⟨3, by decide⟩ ⟨9, by decide⟩ p hp j hj hq fz1_3_9 fz2_3_9
  · exact match_zero_fix ⟨4, by decide⟩ ⟨9, by decide⟩ p hp j hj hq fz1_4_9 fz2_4_9
  · exact match_zero_fix ⟨5, by decide⟩ ⟨9, by decide⟩ p hp j hj hq fz1_5_9 fz2_5_9
  · exact match_zero_fix ⟨6, by decide⟩ ⟨9, by decide⟩ p hp j hj hq fz1_6_9 fz2_6_9
  · exact match_zero_fix ⟨7, by decide⟩ ⟨9, by decide⟩ p hp j hj hq fz1_7_9 fz2_7_9
  · exact match_zero_fix ⟨8, by decide⟩ ⟨9, by decide⟩ p hp j hj hq fz1_8_9 fz2_8_9
  · exact pair_9_9 p hp hrep j hj hq
  · exact match_zero_fix ⟨10, by decide⟩ ⟨9, by decide⟩ p hp j hj hq fz1_10_9 fz2_10_9
  · exact match_zero_fix ⟨11, by decide⟩ ⟨9, by decide⟩ p hp j hj hq fz1_11_9 fz2_11_9
  · exact match_zero_fix ⟨12, by decide⟩ ⟨9, by decide⟩ p hp j hj hq fz1_12_9 fz2_12_9
  · exact pair_13_9 p hp hrep j hj hq
  · exact pair_14_9 p hp hrep j hj hq
  · exact pair_15_9 p hp hrep j hj hq
  · exact pair_16_9 p hp hrep j hj hq
  · exact pair_17_9 p hp hrep j hj hq
  · exact pair_18_9 p hp hrep j hj hq
  · exact match_zero_fix ⟨19, by decide⟩ ⟨9, by decide⟩ p hp j hj hq fz1_19_9 fz2_19_9
  · exact match_zero_fix ⟨20, by decide⟩ ⟨9, by decide⟩ p hp j hj hq fz1_20_9 fz2_20_9
  · exact match_zero_fix ⟨21, by decide⟩ ⟨9, by decide⟩ p hp j hj hq fz1_21_9 fz2_21_9
  · exact match_zero_fix ⟨22, by decide⟩ ⟨9, by decide⟩ p hp j hj hq fz1_22_9 fz2_22_9
  · exact match_zero_fix ⟨23, by decide⟩ ⟨9, by decide⟩ p hp j hj hq fz1_23_9 fz2_23_9
  · exact match_zero_fix ⟨24, by decide⟩ ⟨9, by decide⟩ p hp j hj hq fz1_24_9 fz2_24_9
  · exact match_zero_fix ⟨25, by decide⟩ ⟨9, by decide⟩ p hp j hj hq fz1_25_9 fz2_25_9
  · exact match_zero_fix ⟨26, by decide⟩ ⟨9, by decide⟩ p hp j hj hq fz1_26_9 fz2_26_9
  · exact pair_27_9 p hp hrep j hj hq
  · exact match_zero_fix ⟨28, by decide⟩ ⟨9, by decide⟩ p hp j hj hq fz1_28_9 fz2_28_9
  · exact match_zero_fix ⟨29, by decide⟩ ⟨9, by decide⟩ p hp j hj hq fz1_29_9 fz2_29_9
  · exact match_zero_fix ⟨30, by decide⟩ ⟨9, by decide⟩ p hp j hj hq fz1_30_9 fz2_30_9
  · exact match_zero_fix ⟨31, by decide⟩ ⟨9, by decide⟩ p hp j hj hq fz1_31_9 fz2_31_9
  · exact match_zero_fix ⟨32, by decide⟩ ⟨9, by decide⟩ p hp j hj hq fz1_32_9 fz2_32_9
  · exact match_zero_fix ⟨33, by decide⟩ ⟨9, by decide⟩ p hp j hj hq fz1_33_9 fz2_33_9
  · exact match_zero_fix ⟨34, by decide⟩ ⟨9, by decide⟩ p hp j hj hq fz1_34_9 fz2_34_9
  · exact match_zero_fix ⟨35, by decide⟩ ⟨9, by decide⟩ p hp j hj hq fz1_35_9 fz2_35_9
  · exact match_zero_fix ⟨36, by decide⟩ ⟨9, by decide⟩ p hp j hj hq fz1_36_9 fz2_36_9
  · exact match_zero_fix ⟨37, by decide⟩ ⟨9, by decide⟩ p hp j hj hq fz1_37_9 fz2_37_9
  · exact match_zero_fix ⟨38, by decide⟩ ⟨9, by decide⟩ p hp j hj hq fz1_38_9 fz2_38_9
  · exact match_zero_fix ⟨39, by decide⟩ ⟨9, by decide⟩ p hp j hj hq fz1_39_9 fz2_39_9
  · exact match_zero_fix ⟨40, by decide⟩ ⟨9, by decide⟩ p hp j hj hq fz1_40_9 fz2_40_9
  · exact match_zero_fix ⟨41, by decide⟩ ⟨9, by decide⟩ p hp j hj hq fz1_41_9 fz2_41_9
  · exact match_zero_fix ⟨42, by decide⟩ ⟨9, by decide⟩ p hp j hj hq fz1_42_9 fz2_42_9
  · exact match_zero_fix ⟨43, by decide⟩ ⟨9, by decide⟩ p hp j hj hq fz1_43_9 fz2_43_9
  · exact match_zero_fix ⟨44, by decide⟩ ⟨9, by decide⟩ p hp j hj hq fz1_44_9 fz2_44_9
  · exact match_zero_fix ⟨45, by decide⟩ ⟨9, by decide⟩ p hp j hj hq fz1_45_9 fz2_45_9
  · exact match_zero_fix ⟨46, by decide⟩ ⟨9, by decide⟩ p hp j hj hq fz1_46_9 fz2_46_9
  · exact match_zero_fix ⟨47, by decide⟩ ⟨9, by decide⟩ p hp j hj hq fz1_47_9 fz2_47_9
  · exact match_zero_fix ⟨48, by decide⟩ ⟨9, by decide⟩ p hp j hj hq fz1_48_9 fz2_48_9
  · exact match_zero_fix ⟨49, by decide⟩ ⟨9, by decide⟩ p hp j hj hq fz1_49_9 fz2_49_9
  · exact match_zero_fix ⟨50, by decide⟩ ⟨9, by decide⟩ p hp j hj hq fz1_50_9 fz2_50_9
  · exact match_zero_fix ⟨51, by decide⟩ ⟨9, by decide⟩ p hp j hj hq fz1_51_9 fz2_51_9
  · exact match_zero_fix ⟨52, by decide⟩ ⟨9, by decide⟩ p hp j hj hq fz1_52_9 fz2_52_9
  · exact match_zero_fix ⟨53, by decide⟩ ⟨9, by decide⟩ p hp j hj hq fz1_53_9 fz2_53_9
  · exact match_zero_fix ⟨54, by decide⟩ ⟨9, by decide⟩ p hp j hj hq fz1_54_9 fz2_54_9
  · exact pair_55_9 p hp hrep j hj hq
  · exact match_zero_fix ⟨56, by decide⟩ ⟨9, by decide⟩ p hp j hj hq fz1_56_9 fz2_56_9
  · exact match_zero_fix ⟨57, by decide⟩ ⟨9, by decide⟩ p hp j hj hq fz1_57_9 fz2_57_9
  · exact match_zero_fix ⟨58, by decide⟩ ⟨9, by decide⟩ p hp j hj hq fz1_58_9 fz2_58_9
  · exact match_zero_fix ⟨59, by decide⟩ ⟨9, by decide⟩ p hp j hj hq fz1_59_9 fz2_59_9
  · exact pair_60_9 p hp hrep j hj hq
  · exact match_zero_fix ⟨61, by decide⟩ ⟨9, by decide⟩ p hp j hj hq fz1_61_9 fz2_61_9
  · exact match_zero_fix ⟨62, by decide⟩ ⟨9, by decide⟩ p hp j hj hq fz1_62_9 fz2_62_9
  · exact match_zero_fix ⟨63, by decide⟩ ⟨9, by decide⟩ p hp j hj hq fz1_63_9 fz2_63_9
  · exact match_zero_fix ⟨64, by decide⟩ ⟨9, by decide⟩ p hp j hj hq fz1_64_9 fz2_64_9
  · exact pair_65_9 p hp hrep j hj hq
  · exact match_zero_fix ⟨66, by decide⟩ ⟨9, by decide⟩ p hp j hj hq fz1_66_9 fz2_66_9
  · exact match_zero_fix ⟨67, by decide⟩ ⟨9, by decide⟩ p hp j hj hq fz1_67_9 fz2_67_9
  · exact match_zero_fix ⟨68, by decide⟩ ⟨9, by decide⟩ p hp j hj hq fz1_68_9 fz2_68_9
  · exact match_zero_fix ⟨69, by decide⟩ ⟨9, by decide⟩ p hp j hj hq fz1_69_9 fz2_69_9
  · exact pair_70_9 p hp hrep j hj hq
  · exact match_zero_fix ⟨71, by decide⟩ ⟨9, by decide⟩ p hp j hj hq fz1_71_9 fz2_71_9
  · exact match_zero_fix ⟨72, by decide⟩ ⟨9, by decide⟩ p hp j hj hq fz1_72_9 fz2_72_9
  · exact match_zero_fix ⟨73, by decide⟩ ⟨9, by decide⟩ p hp j hj hq fz1_73_9 fz2_73_9
  · exact match_zero_fix ⟨74, by decide⟩ ⟨9, by decide⟩ p hp j hj hq fz1_74_9 fz2_74_9
  · exact pair_75_9 p hp hrep j hj hq
  · exact match_zero_fix ⟨76, by decide⟩ ⟨9, by decide⟩ p hp j hj hq fz1_76_9 fz2_76_9
  · exact match_zero_fix ⟨77, by decide⟩ ⟨9, by decide⟩ p hp j hj hq fz1_77_9 fz2_77_9
  · exact match_zero_fix ⟨78, by decide⟩ ⟨9, by decide⟩ p hp j hj hq fz1_78_9 fz2_78_9
  · exact match_zero_fix ⟨79, by decide⟩ ⟨9, by decide⟩ p hp j hj hq fz1_79_9 fz2_79_9
  · exact pair_80_9 p hp hrep j hj hq
  · exact match_zero_fix ⟨81, by decide⟩ ⟨9, by decide⟩ p hp j hj hq fz1_81_9 fz2_81_9
  · exact match_zero_fix ⟨82, by decide⟩ ⟨9, by decide⟩ p hp j hj hq fz1_82_9 fz2_82_9
  · exact match_zero_fix ⟨83, by decide⟩ ⟨9, by decide⟩ p hp j hj hq fz1_83_9 fz2_83_9
  · exact match_zero_fix ⟨84, by decide⟩ ⟨9, by decide⟩ p hp j hj hq fz1_84_9 fz2_84_9
  · exact pair_85_9 p hp hrep j hj hq
  · exact match_zero_fix ⟨86, by decide⟩ ⟨9, by decide⟩ p hp j hj hq fz1_86_9 fz2_86_9
  · exact match_zero_fix ⟨87, by decide⟩ ⟨9, by decide⟩ p hp j hj hq fz1_87_9 fz2_87_9
  · exact match_zero_fix ⟨88, by decide⟩ ⟨9, by decide⟩ p hp j hj hq fz1_88_9 fz2_88_9
  · exact match_zero_fix ⟨89, by decide⟩ ⟨9, by decide⟩ p hp j hj hq fz1_89_9 fz2_89_9
  · exact match_zero_fix ⟨90, by decide⟩ ⟨9, by decide⟩ p hp j hj hq fz1_90_9 fz2_90_9
  · exact match_zero_fix ⟨91, by decide⟩ ⟨9, by decide⟩ p hp j hj hq fz1_91_9 fz2_91_9
  · exact match_zero_fix ⟨92, by decide⟩ ⟨9, by decide⟩ p hp j hj hq fz1_92_9 fz2_92_9
  · exact match_zero_fix ⟨93, by decide⟩ ⟨9, by decide⟩ p hp j hj hq fz1_93_9 fz2_93_9
  · exact match_zero_fix ⟨94, by decide⟩ ⟨9, by decide⟩ p hp j hj hq fz1_94_9 fz2_94_9
  · exact match_zero_fix ⟨95, by decide⟩ ⟨9, by decide⟩ p hp j hj hq fz1_95_9 fz2_95_9
  · exact match_zero_fix ⟨96, by decide⟩ ⟨9, by decide⟩ p hp j hj hq fz1_96_9 fz2_96_9
  · exact match_zero_fix ⟨97, by decide⟩ ⟨9, by decide⟩ p hp j hj hq fz1_97_9 fz2_97_9
  · exact match_zero_fix ⟨98, by decide⟩ ⟨9, by decide⟩ p hp j hj hq fz1_98_9 fz2_98_9
  · exact match_zero_fix ⟨99, by decide⟩ ⟨9, by decide⟩ p hp j hj hq fz1_99_9 fz2_99_9
  · exact match_zero_fix ⟨100, by decide⟩ ⟨9, by decide⟩ p hp j hj hq fz1_100_9 fz2_100_9
  · exact match_zero_fix ⟨101, by decide⟩ ⟨9, by decide⟩ p hp j hj hq fz1_101_9 fz2_101_9
  · exact match_zero_fix ⟨102, by decide⟩ ⟨9, by decide⟩ p hp j hj hq fz1_102_9 fz2_102_9
  · exact match_zero_fix ⟨103, by decide⟩ ⟨9, by decide⟩ p hp j hj hq fz1_103_9 fz2_103_9
  · exact match_zero_fix ⟨104, by decide⟩ ⟨9, by decide⟩ p hp j hj hq fz1_104_9 fz2_104_9
  · exact match_zero_fix ⟨105, by decide⟩ ⟨9, by decide⟩ p hp j hj hq fz1_105_9 fz2_105_9
  · exact match_zero_fix ⟨106, by decide⟩ ⟨9, by decide⟩ p hp j hj hq fz1_106_9 fz2_106_9
  · exact match_zero_fix ⟨107, by decide⟩ ⟨9, by decide⟩ p hp j hj hq fz1_107_9 fz2_107_9
  · exact match_zero_fix ⟨108, by decide⟩ ⟨9, by decide⟩ p hp j hj hq fz1_108_9 fz2_108_9
  · exact match_zero_fix ⟨109, by decide⟩ ⟨9, by decide⟩ p hp j hj hq fz1_109_9 fz2_109_9
  · exact match_zero_fix ⟨110, by decide⟩ ⟨9, by decide⟩ p hp j hj hq fz1_110_9 fz2_110_9
  · exact match_zero_fix ⟨111, by decide⟩ ⟨9, by decide⟩ p hp j hj hq fz1_111_9 fz2_111_9
  · exact match_zero_fix ⟨112, by decide⟩ ⟨9, by decide⟩ p hp j hj hq fz1_112_9 fz2_112_9
  · exact match_zero_fix ⟨113, by decide⟩ ⟨9, by decide⟩ p hp j hj hq fz1_113_9 fz2_113_9
  · exact match_zero_fix ⟨114, by decide⟩ ⟨9, by decide⟩ p hp j hj hq fz1_114_9 fz2_114_9
  · exact match_zero_fix ⟨115, by decide⟩ ⟨9, by decide⟩ p hp j hj hq fz1_115_9 fz2_115_9
  · exact pair_116_9 p hp hrep j hj hq
  · exact pair_117_9 p hp hrep j hj hq
  · exact pair_118_9 p hp hrep j hj hq
  · exact pair_119_9 p hp hrep j hj hq
  · exact pair_120_9 p hp hrep j hj hq
  · exact match_zero_fix ⟨121, by decide⟩ ⟨9, by decide⟩ p hp j hj hq fz1_121_9 fz2_121_9
  · exact match_zero_fix ⟨122, by decide⟩ ⟨9, by decide⟩ p hp j hj hq fz1_122_9 fz2_122_9
  · exact match_zero_fix ⟨123, by decide⟩ ⟨9, by decide⟩ p hp j hj hq fz1_123_9 fz2_123_9
  · exact match_zero_fix ⟨124, by decide⟩ ⟨9, by decide⟩ p hp j hj hq fz1_124_9 fz2_124_9
  · exact match_zero_fix ⟨125, by decide⟩ ⟨9, by decide⟩ p hp j hj hq fz1_125_9 fz2_125_9
  · exact match_zero_fix ⟨126, by decide⟩ ⟨9, by decide⟩ p hp j hj hq fz1_126_9 fz2_126_9
  · exact match_zero_fix ⟨127, by decide⟩ ⟨9, by decide⟩ p hp j hj hq fz1_127_9 fz2_127_9
  · exact match_zero_fix ⟨128, by decide⟩ ⟨9, by decide⟩ p hp j hj hq fz1_128_9 fz2_128_9
  · exact match_zero_fix ⟨129, by decide⟩ ⟨9, by decide⟩ p hp j hj hq fz1_129_9 fz2_129_9
  · exact match_zero_fix ⟨130, by decide⟩ ⟨9, by decide⟩ p hp j hj hq fz1_130_9 fz2_130_9
  · exact match_zero_fix ⟨131, by decide⟩ ⟨9, by decide⟩ p hp j hj hq fz1_131_9 fz2_131_9
  · exact match_zero_fix ⟨132, by decide⟩ ⟨9, by decide⟩ p hp j hj hq fz1_132_9 fz2_132_9
  · exact match_zero_fix ⟨133, by decide⟩ ⟨9, by decide⟩ p hp j hj hq fz1_133_9 fz2_133_9
  · exact match_zero_fix ⟨134, by decide⟩ ⟨9, by decide⟩ p hp j hj hq fz1_134_9 fz2_134_9
  · exact match_zero_fix ⟨135, by decide⟩ ⟨9, by decide⟩ p hp j hj hq fz1_135_9 fz2_135_9
  · exact match_zero_fix ⟨136, by decide⟩ ⟨9, by decide⟩ p hp j hj hq fz1_136_9 fz2_136_9
  · exact match_zero_fix ⟨137, by decide⟩ ⟨9, by decide⟩ p hp j hj hq fz1_137_9 fz2_137_9
  · exact match_zero_fix ⟨138, by decide⟩ ⟨9, by decide⟩ p hp j hj hq fz1_138_9 fz2_138_9
  · exact match_zero_fix ⟨139, by decide⟩ ⟨9, by decide⟩ p hp j hj hq fz1_139_9 fz2_139_9
  · exact match_zero_fix ⟨140, by decide⟩ ⟨9, by decide⟩ p hp j hj hq fz1_140_9 fz2_140_9
  · exact pair_141_9 p hp hrep j hj hq
  · exact match_zero_fix ⟨142, by decide⟩ ⟨9, by decide⟩ p hp j hj hq fz1_142_9 fz2_142_9
  · exact match_zero_fix ⟨143, by decide⟩ ⟨9, by decide⟩ p hp j hj hq fz1_143_9 fz2_143_9
  · exact match_zero_fix ⟨144, by decide⟩ ⟨9, by decide⟩ p hp j hj hq fz1_144_9 fz2_144_9
  · exact match_zero_fix ⟨145, by decide⟩ ⟨9, by decide⟩ p hp j hj hq fz1_145_9 fz2_145_9
  · exact match_zero_fix ⟨146, by decide⟩ ⟨9, by decide⟩ p hp j hj hq fz1_146_9 fz2_146_9
  · exact pair_147_9 p hp hrep j hj hq

theorem master_10 (p : Nat) (hp : p < (Q2.transData.getD 10 []).length)
    (hrep : (Q2.cosetIsRep.getD 10 []).getD p false = true)
    (rK : Fin 148) (j : Nat) (hj : j < (repChars.getD rK.val []).length)
    (hq : (normIsRep.getD rK.val []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ p hp)
        (rowE2 rK j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ p (transLenTr ⟨10, by decide⟩ p hp)) (rowE1 rK j hj) := by
  rcases rK with ⟨nK, hnK⟩; interval_cases nK
  · exact match_zero_len ⟨0, by decide⟩ ⟨10, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_fix ⟨1, by decide⟩ ⟨10, by decide⟩ p hp j hj hq fz1_1_10 fz2_1_10
  · exact match_zero_fix ⟨2, by decide⟩ ⟨10, by decide⟩ p hp j hj hq fz1_2_10 fz2_2_10
  · exact match_zero_fix ⟨3, by decide⟩ ⟨10, by decide⟩ p hp j hj hq fz1_3_10 fz2_3_10
  · exact match_zero_fix ⟨4, by decide⟩ ⟨10, by decide⟩ p hp j hj hq fz1_4_10 fz2_4_10
  · exact match_zero_fix ⟨5, by decide⟩ ⟨10, by decide⟩ p hp j hj hq fz1_5_10 fz2_5_10
  · exact match_zero_fix ⟨6, by decide⟩ ⟨10, by decide⟩ p hp j hj hq fz1_6_10 fz2_6_10
  · exact match_zero_fix ⟨7, by decide⟩ ⟨10, by decide⟩ p hp j hj hq fz1_7_10 fz2_7_10
  · exact match_zero_fix ⟨8, by decide⟩ ⟨10, by decide⟩ p hp j hj hq fz1_8_10 fz2_8_10
  · exact match_zero_fix ⟨9, by decide⟩ ⟨10, by decide⟩ p hp j hj hq fz1_9_10 fz2_9_10
  · exact pair_10_10 p hp hrep j hj hq
  · exact match_zero_fix ⟨11, by decide⟩ ⟨10, by decide⟩ p hp j hj hq fz1_11_10 fz2_11_10
  · exact match_zero_fix ⟨12, by decide⟩ ⟨10, by decide⟩ p hp j hj hq fz1_12_10 fz2_12_10
  · exact pair_13_10 p hp hrep j hj hq
  · exact match_zero_fix ⟨14, by decide⟩ ⟨10, by decide⟩ p hp j hj hq fz1_14_10 fz2_14_10
  · exact match_zero_fix ⟨15, by decide⟩ ⟨10, by decide⟩ p hp j hj hq fz1_15_10 fz2_15_10
  · exact match_zero_fix ⟨16, by decide⟩ ⟨10, by decide⟩ p hp j hj hq fz1_16_10 fz2_16_10
  · exact match_zero_fix ⟨17, by decide⟩ ⟨10, by decide⟩ p hp j hj hq fz1_17_10 fz2_17_10
  · exact match_zero_fix ⟨18, by decide⟩ ⟨10, by decide⟩ p hp j hj hq fz1_18_10 fz2_18_10
  · exact match_zero_fix ⟨19, by decide⟩ ⟨10, by decide⟩ p hp j hj hq fz1_19_10 fz2_19_10
  · exact match_zero_fix ⟨20, by decide⟩ ⟨10, by decide⟩ p hp j hj hq fz1_20_10 fz2_20_10
  · exact match_zero_fix ⟨21, by decide⟩ ⟨10, by decide⟩ p hp j hj hq fz1_21_10 fz2_21_10
  · exact match_zero_fix ⟨22, by decide⟩ ⟨10, by decide⟩ p hp j hj hq fz1_22_10 fz2_22_10
  · exact match_zero_fix ⟨23, by decide⟩ ⟨10, by decide⟩ p hp j hj hq fz1_23_10 fz2_23_10
  · exact match_zero_fix ⟨24, by decide⟩ ⟨10, by decide⟩ p hp j hj hq fz1_24_10 fz2_24_10
  · exact match_zero_fix ⟨25, by decide⟩ ⟨10, by decide⟩ p hp j hj hq fz1_25_10 fz2_25_10
  · exact match_zero_fix ⟨26, by decide⟩ ⟨10, by decide⟩ p hp j hj hq fz1_26_10 fz2_26_10
  · exact match_zero_fix ⟨27, by decide⟩ ⟨10, by decide⟩ p hp j hj hq fz1_27_10 fz2_27_10
  · exact match_zero_fix ⟨28, by decide⟩ ⟨10, by decide⟩ p hp j hj hq fz1_28_10 fz2_28_10
  · exact match_zero_fix ⟨29, by decide⟩ ⟨10, by decide⟩ p hp j hj hq fz1_29_10 fz2_29_10
  · exact match_zero_fix ⟨30, by decide⟩ ⟨10, by decide⟩ p hp j hj hq fz1_30_10 fz2_30_10
  · exact match_zero_fix ⟨31, by decide⟩ ⟨10, by decide⟩ p hp j hj hq fz1_31_10 fz2_31_10
  · exact match_zero_fix ⟨32, by decide⟩ ⟨10, by decide⟩ p hp j hj hq fz1_32_10 fz2_32_10
  · exact match_zero_fix ⟨33, by decide⟩ ⟨10, by decide⟩ p hp j hj hq fz1_33_10 fz2_33_10
  · exact match_zero_fix ⟨34, by decide⟩ ⟨10, by decide⟩ p hp j hj hq fz1_34_10 fz2_34_10
  · exact match_zero_fix ⟨35, by decide⟩ ⟨10, by decide⟩ p hp j hj hq fz1_35_10 fz2_35_10
  · exact match_zero_fix ⟨36, by decide⟩ ⟨10, by decide⟩ p hp j hj hq fz1_36_10 fz2_36_10
  · exact match_zero_fix ⟨37, by decide⟩ ⟨10, by decide⟩ p hp j hj hq fz1_37_10 fz2_37_10
  · exact match_zero_fix ⟨38, by decide⟩ ⟨10, by decide⟩ p hp j hj hq fz1_38_10 fz2_38_10
  · exact match_zero_fix ⟨39, by decide⟩ ⟨10, by decide⟩ p hp j hj hq fz1_39_10 fz2_39_10
  · exact match_zero_fix ⟨40, by decide⟩ ⟨10, by decide⟩ p hp j hj hq fz1_40_10 fz2_40_10
  · exact match_zero_fix ⟨41, by decide⟩ ⟨10, by decide⟩ p hp j hj hq fz1_41_10 fz2_41_10
  · exact match_zero_fix ⟨42, by decide⟩ ⟨10, by decide⟩ p hp j hj hq fz1_42_10 fz2_42_10
  · exact match_zero_fix ⟨43, by decide⟩ ⟨10, by decide⟩ p hp j hj hq fz1_43_10 fz2_43_10
  · exact match_zero_fix ⟨44, by decide⟩ ⟨10, by decide⟩ p hp j hj hq fz1_44_10 fz2_44_10
  · exact match_zero_fix ⟨45, by decide⟩ ⟨10, by decide⟩ p hp j hj hq fz1_45_10 fz2_45_10
  · exact match_zero_fix ⟨46, by decide⟩ ⟨10, by decide⟩ p hp j hj hq fz1_46_10 fz2_46_10
  · exact match_zero_fix ⟨47, by decide⟩ ⟨10, by decide⟩ p hp j hj hq fz1_47_10 fz2_47_10
  · exact match_zero_fix ⟨48, by decide⟩ ⟨10, by decide⟩ p hp j hj hq fz1_48_10 fz2_48_10
  · exact match_zero_fix ⟨49, by decide⟩ ⟨10, by decide⟩ p hp j hj hq fz1_49_10 fz2_49_10
  · exact match_zero_fix ⟨50, by decide⟩ ⟨10, by decide⟩ p hp j hj hq fz1_50_10 fz2_50_10
  · exact match_zero_fix ⟨51, by decide⟩ ⟨10, by decide⟩ p hp j hj hq fz1_51_10 fz2_51_10
  · exact match_zero_fix ⟨52, by decide⟩ ⟨10, by decide⟩ p hp j hj hq fz1_52_10 fz2_52_10
  · exact pair_53_10 p hp hrep j hj hq
  · exact match_zero_fix ⟨54, by decide⟩ ⟨10, by decide⟩ p hp j hj hq fz1_54_10 fz2_54_10
  · exact match_zero_fix ⟨55, by decide⟩ ⟨10, by decide⟩ p hp j hj hq fz1_55_10 fz2_55_10
  · exact match_zero_fix ⟨56, by decide⟩ ⟨10, by decide⟩ p hp j hj hq fz1_56_10 fz2_56_10
  · exact match_zero_fix ⟨57, by decide⟩ ⟨10, by decide⟩ p hp j hj hq fz1_57_10 fz2_57_10
  · exact match_zero_fix ⟨58, by decide⟩ ⟨10, by decide⟩ p hp j hj hq fz1_58_10 fz2_58_10
  · exact match_zero_fix ⟨59, by decide⟩ ⟨10, by decide⟩ p hp j hj hq fz1_59_10 fz2_59_10
  · exact match_zero_fix ⟨60, by decide⟩ ⟨10, by decide⟩ p hp j hj hq fz1_60_10 fz2_60_10
  · exact match_zero_fix ⟨61, by decide⟩ ⟨10, by decide⟩ p hp j hj hq fz1_61_10 fz2_61_10
  · exact match_zero_fix ⟨62, by decide⟩ ⟨10, by decide⟩ p hp j hj hq fz1_62_10 fz2_62_10
  · exact match_zero_fix ⟨63, by decide⟩ ⟨10, by decide⟩ p hp j hj hq fz1_63_10 fz2_63_10
  · exact match_zero_fix ⟨64, by decide⟩ ⟨10, by decide⟩ p hp j hj hq fz1_64_10 fz2_64_10
  · exact match_zero_fix ⟨65, by decide⟩ ⟨10, by decide⟩ p hp j hj hq fz1_65_10 fz2_65_10
  · exact match_zero_fix ⟨66, by decide⟩ ⟨10, by decide⟩ p hp j hj hq fz1_66_10 fz2_66_10
  · exact match_zero_fix ⟨67, by decide⟩ ⟨10, by decide⟩ p hp j hj hq fz1_67_10 fz2_67_10
  · exact match_zero_fix ⟨68, by decide⟩ ⟨10, by decide⟩ p hp j hj hq fz1_68_10 fz2_68_10
  · exact match_zero_fix ⟨69, by decide⟩ ⟨10, by decide⟩ p hp j hj hq fz1_69_10 fz2_69_10
  · exact match_zero_fix ⟨70, by decide⟩ ⟨10, by decide⟩ p hp j hj hq fz1_70_10 fz2_70_10
  · exact match_zero_fix ⟨71, by decide⟩ ⟨10, by decide⟩ p hp j hj hq fz1_71_10 fz2_71_10
  · exact match_zero_fix ⟨72, by decide⟩ ⟨10, by decide⟩ p hp j hj hq fz1_72_10 fz2_72_10
  · exact match_zero_fix ⟨73, by decide⟩ ⟨10, by decide⟩ p hp j hj hq fz1_73_10 fz2_73_10
  · exact match_zero_fix ⟨74, by decide⟩ ⟨10, by decide⟩ p hp j hj hq fz1_74_10 fz2_74_10
  · exact match_zero_fix ⟨75, by decide⟩ ⟨10, by decide⟩ p hp j hj hq fz1_75_10 fz2_75_10
  · exact match_zero_fix ⟨76, by decide⟩ ⟨10, by decide⟩ p hp j hj hq fz1_76_10 fz2_76_10
  · exact match_zero_fix ⟨77, by decide⟩ ⟨10, by decide⟩ p hp j hj hq fz1_77_10 fz2_77_10
  · exact match_zero_fix ⟨78, by decide⟩ ⟨10, by decide⟩ p hp j hj hq fz1_78_10 fz2_78_10
  · exact match_zero_fix ⟨79, by decide⟩ ⟨10, by decide⟩ p hp j hj hq fz1_79_10 fz2_79_10
  · exact pair_80_10 p hp hrep j hj hq
  · exact pair_81_10 p hp hrep j hj hq
  · exact pair_82_10 p hp hrep j hj hq
  · exact pair_83_10 p hp hrep j hj hq
  · exact pair_84_10 p hp hrep j hj hq
  · exact match_zero_fix ⟨85, by decide⟩ ⟨10, by decide⟩ p hp j hj hq fz1_85_10 fz2_85_10
  · exact match_zero_fix ⟨86, by decide⟩ ⟨10, by decide⟩ p hp j hj hq fz1_86_10 fz2_86_10
  · exact match_zero_fix ⟨87, by decide⟩ ⟨10, by decide⟩ p hp j hj hq fz1_87_10 fz2_87_10
  · exact match_zero_fix ⟨88, by decide⟩ ⟨10, by decide⟩ p hp j hj hq fz1_88_10 fz2_88_10
  · exact match_zero_fix ⟨89, by decide⟩ ⟨10, by decide⟩ p hp j hj hq fz1_89_10 fz2_89_10
  · exact pair_90_10 p hp hrep j hj hq
  · exact pair_91_10 p hp hrep j hj hq
  · exact pair_92_10 p hp hrep j hj hq
  · exact pair_93_10 p hp hrep j hj hq
  · exact pair_94_10 p hp hrep j hj hq
  · exact pair_95_10 p hp hrep j hj hq
  · exact pair_96_10 p hp hrep j hj hq
  · exact pair_97_10 p hp hrep j hj hq
  · exact pair_98_10 p hp hrep j hj hq
  · exact pair_99_10 p hp hrep j hj hq
  · exact pair_100_10 p hp hrep j hj hq
  · exact pair_101_10 p hp hrep j hj hq
  · exact pair_102_10 p hp hrep j hj hq
  · exact pair_103_10 p hp hrep j hj hq
  · exact pair_104_10 p hp hrep j hj hq
  · exact pair_105_10 p hp hrep j hj hq
  · exact pair_106_10 p hp hrep j hj hq
  · exact pair_107_10 p hp hrep j hj hq
  · exact pair_108_10 p hp hrep j hj hq
  · exact pair_109_10 p hp hrep j hj hq
  · exact pair_110_10 p hp hrep j hj hq
  · exact pair_111_10 p hp hrep j hj hq
  · exact pair_112_10 p hp hrep j hj hq
  · exact pair_113_10 p hp hrep j hj hq
  · exact pair_114_10 p hp hrep j hj hq
  · exact pair_115_10 p hp hrep j hj hq
  · exact pair_116_10 p hp hrep j hj hq
  · exact pair_117_10 p hp hrep j hj hq
  · exact pair_118_10 p hp hrep j hj hq
  · exact pair_119_10 p hp hrep j hj hq
  · exact pair_120_10 p hp hrep j hj hq
  · exact pair_121_10 p hp hrep j hj hq
  · exact pair_122_10 p hp hrep j hj hq
  · exact pair_123_10 p hp hrep j hj hq
  · exact pair_124_10 p hp hrep j hj hq
  · exact pair_125_10 p hp hrep j hj hq
  · exact pair_126_10 p hp hrep j hj hq
  · exact pair_127_10 p hp hrep j hj hq
  · exact pair_128_10 p hp hrep j hj hq
  · exact pair_129_10 p hp hrep j hj hq
  · exact pair_130_10 p hp hrep j hj hq
  · exact pair_131_10 p hp hrep j hj hq
  · exact pair_132_10 p hp hrep j hj hq
  · exact pair_133_10 p hp hrep j hj hq
  · exact pair_134_10 p hp hrep j hj hq
  · exact pair_135_10 p hp hrep j hj hq
  · exact pair_136_10 p hp hrep j hj hq
  · exact pair_137_10 p hp hrep j hj hq
  · exact pair_138_10 p hp hrep j hj hq
  · exact pair_139_10 p hp hrep j hj hq
  · exact pair_140_10 p hp hrep j hj hq
  · exact pair_141_10 p hp hrep j hj hq
  · exact pair_142_10 p hp hrep j hj hq
  · exact pair_143_10 p hp hrep j hj hq
  · exact pair_144_10 p hp hrep j hj hq
  · exact pair_145_10 p hp hrep j hj hq
  · exact pair_146_10 p hp hrep j hj hq
  · exact pair_147_10 p hp hrep j hj hq

theorem master_11 (p : Nat) (hp : p < (Q2.transData.getD 11 []).length)
    (hrep : (Q2.cosetIsRep.getD 11 []).getD p false = true)
    (rK : Fin 148) (j : Nat) (hj : j < (repChars.getD rK.val []).length)
    (hq : (normIsRep.getD rK.val []).getD j false = true) :
    species (Q2.reps (⟨11, by decide⟩ : Fin 148)) (colE2 ⟨11, by decide⟩ p hp)
        (rowE2 rK j hj hq)
      = species (reps (⟨11, by decide⟩ : Fin 148))
        (colE1 ⟨11, by decide⟩ p (transLenTr ⟨11, by decide⟩ p hp)) (rowE1 rK j hj) := by
  rcases rK with ⟨nK, hnK⟩; interval_cases nK
  · exact match_zero_len ⟨0, by decide⟩ ⟨11, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_fix ⟨1, by decide⟩ ⟨11, by decide⟩ p hp j hj hq fz1_1_11 fz2_1_11
  · exact match_zero_fix ⟨2, by decide⟩ ⟨11, by decide⟩ p hp j hj hq fz1_2_11 fz2_2_11
  · exact match_zero_fix ⟨3, by decide⟩ ⟨11, by decide⟩ p hp j hj hq fz1_3_11 fz2_3_11
  · exact match_zero_fix ⟨4, by decide⟩ ⟨11, by decide⟩ p hp j hj hq fz1_4_11 fz2_4_11
  · exact match_zero_fix ⟨5, by decide⟩ ⟨11, by decide⟩ p hp j hj hq fz1_5_11 fz2_5_11
  · exact match_zero_fix ⟨6, by decide⟩ ⟨11, by decide⟩ p hp j hj hq fz1_6_11 fz2_6_11
  · exact match_zero_fix ⟨7, by decide⟩ ⟨11, by decide⟩ p hp j hj hq fz1_7_11 fz2_7_11
  · exact match_zero_fix ⟨8, by decide⟩ ⟨11, by decide⟩ p hp j hj hq fz1_8_11 fz2_8_11
  · exact match_zero_fix ⟨9, by decide⟩ ⟨11, by decide⟩ p hp j hj hq fz1_9_11 fz2_9_11
  · exact match_zero_fix ⟨10, by decide⟩ ⟨11, by decide⟩ p hp j hj hq fz1_10_11 fz2_10_11
  · exact pair_11_11 p hp hrep j hj hq
  · exact match_zero_fix ⟨12, by decide⟩ ⟨11, by decide⟩ p hp j hj hq fz1_12_11 fz2_12_11
  · exact match_zero_fix ⟨13, by decide⟩ ⟨11, by decide⟩ p hp j hj hq fz1_13_11 fz2_13_11
  · exact pair_14_11 p hp hrep j hj hq
  · exact pair_15_11 p hp hrep j hj hq
  · exact pair_16_11 p hp hrep j hj hq
  · exact pair_17_11 p hp hrep j hj hq
  · exact pair_18_11 p hp hrep j hj hq
  · exact match_zero_fix ⟨19, by decide⟩ ⟨11, by decide⟩ p hp j hj hq fz1_19_11 fz2_19_11
  · exact match_zero_fix ⟨20, by decide⟩ ⟨11, by decide⟩ p hp j hj hq fz1_20_11 fz2_20_11
  · exact match_zero_fix ⟨21, by decide⟩ ⟨11, by decide⟩ p hp j hj hq fz1_21_11 fz2_21_11
  · exact match_zero_fix ⟨22, by decide⟩ ⟨11, by decide⟩ p hp j hj hq fz1_22_11 fz2_22_11
  · exact match_zero_fix ⟨23, by decide⟩ ⟨11, by decide⟩ p hp j hj hq fz1_23_11 fz2_23_11
  · exact match_zero_fix ⟨24, by decide⟩ ⟨11, by decide⟩ p hp j hj hq fz1_24_11 fz2_24_11
  · exact match_zero_fix ⟨25, by decide⟩ ⟨11, by decide⟩ p hp j hj hq fz1_25_11 fz2_25_11
  · exact match_zero_fix ⟨26, by decide⟩ ⟨11, by decide⟩ p hp j hj hq fz1_26_11 fz2_26_11
  · exact match_zero_fix ⟨27, by decide⟩ ⟨11, by decide⟩ p hp j hj hq fz1_27_11 fz2_27_11
  · exact match_zero_fix ⟨28, by decide⟩ ⟨11, by decide⟩ p hp j hj hq fz1_28_11 fz2_28_11
  · exact match_zero_fix ⟨29, by decide⟩ ⟨11, by decide⟩ p hp j hj hq fz1_29_11 fz2_29_11
  · exact match_zero_fix ⟨30, by decide⟩ ⟨11, by decide⟩ p hp j hj hq fz1_30_11 fz2_30_11
  · exact match_zero_fix ⟨31, by decide⟩ ⟨11, by decide⟩ p hp j hj hq fz1_31_11 fz2_31_11
  · exact match_zero_fix ⟨32, by decide⟩ ⟨11, by decide⟩ p hp j hj hq fz1_32_11 fz2_32_11
  · exact match_zero_fix ⟨33, by decide⟩ ⟨11, by decide⟩ p hp j hj hq fz1_33_11 fz2_33_11
  · exact match_zero_fix ⟨34, by decide⟩ ⟨11, by decide⟩ p hp j hj hq fz1_34_11 fz2_34_11
  · exact match_zero_fix ⟨35, by decide⟩ ⟨11, by decide⟩ p hp j hj hq fz1_35_11 fz2_35_11
  · exact match_zero_fix ⟨36, by decide⟩ ⟨11, by decide⟩ p hp j hj hq fz1_36_11 fz2_36_11
  · exact match_zero_fix ⟨37, by decide⟩ ⟨11, by decide⟩ p hp j hj hq fz1_37_11 fz2_37_11
  · exact match_zero_fix ⟨38, by decide⟩ ⟨11, by decide⟩ p hp j hj hq fz1_38_11 fz2_38_11
  · exact match_zero_fix ⟨39, by decide⟩ ⟨11, by decide⟩ p hp j hj hq fz1_39_11 fz2_39_11
  · exact match_zero_fix ⟨40, by decide⟩ ⟨11, by decide⟩ p hp j hj hq fz1_40_11 fz2_40_11
  · exact match_zero_fix ⟨41, by decide⟩ ⟨11, by decide⟩ p hp j hj hq fz1_41_11 fz2_41_11
  · exact match_zero_fix ⟨42, by decide⟩ ⟨11, by decide⟩ p hp j hj hq fz1_42_11 fz2_42_11
  · exact match_zero_fix ⟨43, by decide⟩ ⟨11, by decide⟩ p hp j hj hq fz1_43_11 fz2_43_11
  · exact match_zero_fix ⟨44, by decide⟩ ⟨11, by decide⟩ p hp j hj hq fz1_44_11 fz2_44_11
  · exact match_zero_fix ⟨45, by decide⟩ ⟨11, by decide⟩ p hp j hj hq fz1_45_11 fz2_45_11
  · exact match_zero_fix ⟨46, by decide⟩ ⟨11, by decide⟩ p hp j hj hq fz1_46_11 fz2_46_11
  · exact match_zero_fix ⟨47, by decide⟩ ⟨11, by decide⟩ p hp j hj hq fz1_47_11 fz2_47_11
  · exact match_zero_fix ⟨48, by decide⟩ ⟨11, by decide⟩ p hp j hj hq fz1_48_11 fz2_48_11
  · exact match_zero_fix ⟨49, by decide⟩ ⟨11, by decide⟩ p hp j hj hq fz1_49_11 fz2_49_11
  · exact match_zero_fix ⟨50, by decide⟩ ⟨11, by decide⟩ p hp j hj hq fz1_50_11 fz2_50_11
  · exact match_zero_fix ⟨51, by decide⟩ ⟨11, by decide⟩ p hp j hj hq fz1_51_11 fz2_51_11
  · exact match_zero_fix ⟨52, by decide⟩ ⟨11, by decide⟩ p hp j hj hq fz1_52_11 fz2_52_11
  · exact match_zero_fix ⟨53, by decide⟩ ⟨11, by decide⟩ p hp j hj hq fz1_53_11 fz2_53_11
  · exact pair_54_11 p hp hrep j hj hq
  · exact match_zero_fix ⟨55, by decide⟩ ⟨11, by decide⟩ p hp j hj hq fz1_55_11 fz2_55_11
  · exact match_zero_fix ⟨56, by decide⟩ ⟨11, by decide⟩ p hp j hj hq fz1_56_11 fz2_56_11
  · exact match_zero_fix ⟨57, by decide⟩ ⟨11, by decide⟩ p hp j hj hq fz1_57_11 fz2_57_11
  · exact match_zero_fix ⟨58, by decide⟩ ⟨11, by decide⟩ p hp j hj hq fz1_58_11 fz2_58_11
  · exact match_zero_fix ⟨59, by decide⟩ ⟨11, by decide⟩ p hp j hj hq fz1_59_11 fz2_59_11
  · exact match_zero_fix ⟨60, by decide⟩ ⟨11, by decide⟩ p hp j hj hq fz1_60_11 fz2_60_11
  · exact match_zero_fix ⟨61, by decide⟩ ⟨11, by decide⟩ p hp j hj hq fz1_61_11 fz2_61_11
  · exact match_zero_fix ⟨62, by decide⟩ ⟨11, by decide⟩ p hp j hj hq fz1_62_11 fz2_62_11
  · exact match_zero_fix ⟨63, by decide⟩ ⟨11, by decide⟩ p hp j hj hq fz1_63_11 fz2_63_11
  · exact match_zero_fix ⟨64, by decide⟩ ⟨11, by decide⟩ p hp j hj hq fz1_64_11 fz2_64_11
  · exact match_zero_fix ⟨65, by decide⟩ ⟨11, by decide⟩ p hp j hj hq fz1_65_11 fz2_65_11
  · exact match_zero_fix ⟨66, by decide⟩ ⟨11, by decide⟩ p hp j hj hq fz1_66_11 fz2_66_11
  · exact match_zero_fix ⟨67, by decide⟩ ⟨11, by decide⟩ p hp j hj hq fz1_67_11 fz2_67_11
  · exact match_zero_fix ⟨68, by decide⟩ ⟨11, by decide⟩ p hp j hj hq fz1_68_11 fz2_68_11
  · exact match_zero_fix ⟨69, by decide⟩ ⟨11, by decide⟩ p hp j hj hq fz1_69_11 fz2_69_11
  · exact match_zero_fix ⟨70, by decide⟩ ⟨11, by decide⟩ p hp j hj hq fz1_70_11 fz2_70_11
  · exact match_zero_fix ⟨71, by decide⟩ ⟨11, by decide⟩ p hp j hj hq fz1_71_11 fz2_71_11
  · exact match_zero_fix ⟨72, by decide⟩ ⟨11, by decide⟩ p hp j hj hq fz1_72_11 fz2_72_11
  · exact match_zero_fix ⟨73, by decide⟩ ⟨11, by decide⟩ p hp j hj hq fz1_73_11 fz2_73_11
  · exact match_zero_fix ⟨74, by decide⟩ ⟨11, by decide⟩ p hp j hj hq fz1_74_11 fz2_74_11
  · exact match_zero_fix ⟨75, by decide⟩ ⟨11, by decide⟩ p hp j hj hq fz1_75_11 fz2_75_11
  · exact match_zero_fix ⟨76, by decide⟩ ⟨11, by decide⟩ p hp j hj hq fz1_76_11 fz2_76_11
  · exact match_zero_fix ⟨77, by decide⟩ ⟨11, by decide⟩ p hp j hj hq fz1_77_11 fz2_77_11
  · exact match_zero_fix ⟨78, by decide⟩ ⟨11, by decide⟩ p hp j hj hq fz1_78_11 fz2_78_11
  · exact match_zero_fix ⟨79, by decide⟩ ⟨11, by decide⟩ p hp j hj hq fz1_79_11 fz2_79_11
  · exact match_zero_fix ⟨80, by decide⟩ ⟨11, by decide⟩ p hp j hj hq fz1_80_11 fz2_80_11
  · exact match_zero_fix ⟨81, by decide⟩ ⟨11, by decide⟩ p hp j hj hq fz1_81_11 fz2_81_11
  · exact match_zero_fix ⟨82, by decide⟩ ⟨11, by decide⟩ p hp j hj hq fz1_82_11 fz2_82_11
  · exact match_zero_fix ⟨83, by decide⟩ ⟨11, by decide⟩ p hp j hj hq fz1_83_11 fz2_83_11
  · exact match_zero_fix ⟨84, by decide⟩ ⟨11, by decide⟩ p hp j hj hq fz1_84_11 fz2_84_11
  · exact pair_85_11 p hp hrep j hj hq
  · exact pair_86_11 p hp hrep j hj hq
  · exact pair_87_11 p hp hrep j hj hq
  · exact pair_88_11 p hp hrep j hj hq
  · exact pair_89_11 p hp hrep j hj hq
  · exact match_zero_fix ⟨90, by decide⟩ ⟨11, by decide⟩ p hp j hj hq fz1_90_11 fz2_90_11
  · exact match_zero_fix ⟨91, by decide⟩ ⟨11, by decide⟩ p hp j hj hq fz1_91_11 fz2_91_11
  · exact match_zero_fix ⟨92, by decide⟩ ⟨11, by decide⟩ p hp j hj hq fz1_92_11 fz2_92_11
  · exact match_zero_fix ⟨93, by decide⟩ ⟨11, by decide⟩ p hp j hj hq fz1_93_11 fz2_93_11
  · exact match_zero_fix ⟨94, by decide⟩ ⟨11, by decide⟩ p hp j hj hq fz1_94_11 fz2_94_11
  · exact match_zero_fix ⟨95, by decide⟩ ⟨11, by decide⟩ p hp j hj hq fz1_95_11 fz2_95_11
  · exact match_zero_fix ⟨96, by decide⟩ ⟨11, by decide⟩ p hp j hj hq fz1_96_11 fz2_96_11
  · exact match_zero_fix ⟨97, by decide⟩ ⟨11, by decide⟩ p hp j hj hq fz1_97_11 fz2_97_11
  · exact match_zero_fix ⟨98, by decide⟩ ⟨11, by decide⟩ p hp j hj hq fz1_98_11 fz2_98_11
  · exact match_zero_fix ⟨99, by decide⟩ ⟨11, by decide⟩ p hp j hj hq fz1_99_11 fz2_99_11
  · exact match_zero_fix ⟨100, by decide⟩ ⟨11, by decide⟩ p hp j hj hq fz1_100_11 fz2_100_11
  · exact match_zero_fix ⟨101, by decide⟩ ⟨11, by decide⟩ p hp j hj hq fz1_101_11 fz2_101_11
  · exact match_zero_fix ⟨102, by decide⟩ ⟨11, by decide⟩ p hp j hj hq fz1_102_11 fz2_102_11
  · exact match_zero_fix ⟨103, by decide⟩ ⟨11, by decide⟩ p hp j hj hq fz1_103_11 fz2_103_11
  · exact match_zero_fix ⟨104, by decide⟩ ⟨11, by decide⟩ p hp j hj hq fz1_104_11 fz2_104_11
  · exact match_zero_fix ⟨105, by decide⟩ ⟨11, by decide⟩ p hp j hj hq fz1_105_11 fz2_105_11
  · exact match_zero_fix ⟨106, by decide⟩ ⟨11, by decide⟩ p hp j hj hq fz1_106_11 fz2_106_11
  · exact match_zero_fix ⟨107, by decide⟩ ⟨11, by decide⟩ p hp j hj hq fz1_107_11 fz2_107_11
  · exact match_zero_fix ⟨108, by decide⟩ ⟨11, by decide⟩ p hp j hj hq fz1_108_11 fz2_108_11
  · exact match_zero_fix ⟨109, by decide⟩ ⟨11, by decide⟩ p hp j hj hq fz1_109_11 fz2_109_11
  · exact match_zero_fix ⟨110, by decide⟩ ⟨11, by decide⟩ p hp j hj hq fz1_110_11 fz2_110_11
  · exact match_zero_fix ⟨111, by decide⟩ ⟨11, by decide⟩ p hp j hj hq fz1_111_11 fz2_111_11
  · exact match_zero_fix ⟨112, by decide⟩ ⟨11, by decide⟩ p hp j hj hq fz1_112_11 fz2_112_11
  · exact match_zero_fix ⟨113, by decide⟩ ⟨11, by decide⟩ p hp j hj hq fz1_113_11 fz2_113_11
  · exact match_zero_fix ⟨114, by decide⟩ ⟨11, by decide⟩ p hp j hj hq fz1_114_11 fz2_114_11
  · exact pair_115_11 p hp hrep j hj hq
  · exact match_zero_fix ⟨116, by decide⟩ ⟨11, by decide⟩ p hp j hj hq fz1_116_11 fz2_116_11
  · exact match_zero_fix ⟨117, by decide⟩ ⟨11, by decide⟩ p hp j hj hq fz1_117_11 fz2_117_11
  · exact match_zero_fix ⟨118, by decide⟩ ⟨11, by decide⟩ p hp j hj hq fz1_118_11 fz2_118_11
  · exact match_zero_fix ⟨119, by decide⟩ ⟨11, by decide⟩ p hp j hj hq fz1_119_11 fz2_119_11
  · exact match_zero_fix ⟨120, by decide⟩ ⟨11, by decide⟩ p hp j hj hq fz1_120_11 fz2_120_11
  · exact match_zero_fix ⟨121, by decide⟩ ⟨11, by decide⟩ p hp j hj hq fz1_121_11 fz2_121_11
  · exact match_zero_fix ⟨122, by decide⟩ ⟨11, by decide⟩ p hp j hj hq fz1_122_11 fz2_122_11
  · exact match_zero_fix ⟨123, by decide⟩ ⟨11, by decide⟩ p hp j hj hq fz1_123_11 fz2_123_11
  · exact match_zero_fix ⟨124, by decide⟩ ⟨11, by decide⟩ p hp j hj hq fz1_124_11 fz2_124_11
  · exact match_zero_fix ⟨125, by decide⟩ ⟨11, by decide⟩ p hp j hj hq fz1_125_11 fz2_125_11
  · exact match_zero_fix ⟨126, by decide⟩ ⟨11, by decide⟩ p hp j hj hq fz1_126_11 fz2_126_11
  · exact match_zero_fix ⟨127, by decide⟩ ⟨11, by decide⟩ p hp j hj hq fz1_127_11 fz2_127_11
  · exact match_zero_fix ⟨128, by decide⟩ ⟨11, by decide⟩ p hp j hj hq fz1_128_11 fz2_128_11
  · exact match_zero_fix ⟨129, by decide⟩ ⟨11, by decide⟩ p hp j hj hq fz1_129_11 fz2_129_11
  · exact match_zero_fix ⟨130, by decide⟩ ⟨11, by decide⟩ p hp j hj hq fz1_130_11 fz2_130_11
  · exact match_zero_fix ⟨131, by decide⟩ ⟨11, by decide⟩ p hp j hj hq fz1_131_11 fz2_131_11
  · exact match_zero_fix ⟨132, by decide⟩ ⟨11, by decide⟩ p hp j hj hq fz1_132_11 fz2_132_11
  · exact match_zero_fix ⟨133, by decide⟩ ⟨11, by decide⟩ p hp j hj hq fz1_133_11 fz2_133_11
  · exact match_zero_fix ⟨134, by decide⟩ ⟨11, by decide⟩ p hp j hj hq fz1_134_11 fz2_134_11
  · exact match_zero_fix ⟨135, by decide⟩ ⟨11, by decide⟩ p hp j hj hq fz1_135_11 fz2_135_11
  · exact match_zero_fix ⟨136, by decide⟩ ⟨11, by decide⟩ p hp j hj hq fz1_136_11 fz2_136_11
  · exact match_zero_fix ⟨137, by decide⟩ ⟨11, by decide⟩ p hp j hj hq fz1_137_11 fz2_137_11
  · exact match_zero_fix ⟨138, by decide⟩ ⟨11, by decide⟩ p hp j hj hq fz1_138_11 fz2_138_11
  · exact match_zero_fix ⟨139, by decide⟩ ⟨11, by decide⟩ p hp j hj hq fz1_139_11 fz2_139_11
  · exact match_zero_fix ⟨140, by decide⟩ ⟨11, by decide⟩ p hp j hj hq fz1_140_11 fz2_140_11
  · exact pair_141_11 p hp hrep j hj hq
  · exact pair_142_11 p hp hrep j hj hq
  · exact pair_143_11 p hp hrep j hj hq
  · exact pair_144_11 p hp hrep j hj hq
  · exact pair_145_11 p hp hrep j hj hq
  · exact pair_146_11 p hp hrep j hj hq
  · exact pair_147_11 p hp hrep j hj hq

theorem master_12 (p : Nat) (hp : p < (Q2.transData.getD 12 []).length)
    (hrep : (Q2.cosetIsRep.getD 12 []).getD p false = true)
    (rK : Fin 148) (j : Nat) (hj : j < (repChars.getD rK.val []).length)
    (hq : (normIsRep.getD rK.val []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ p hp)
        (rowE2 rK j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ p (transLenTr ⟨12, by decide⟩ p hp)) (rowE1 rK j hj) := by
  rcases rK with ⟨nK, hnK⟩; interval_cases nK
  · exact match_zero_len ⟨0, by decide⟩ ⟨12, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_fix ⟨1, by decide⟩ ⟨12, by decide⟩ p hp j hj hq fz1_1_12 fz2_1_12
  · exact match_zero_fix ⟨2, by decide⟩ ⟨12, by decide⟩ p hp j hj hq fz1_2_12 fz2_2_12
  · exact match_zero_fix ⟨3, by decide⟩ ⟨12, by decide⟩ p hp j hj hq fz1_3_12 fz2_3_12
  · exact match_zero_fix ⟨4, by decide⟩ ⟨12, by decide⟩ p hp j hj hq fz1_4_12 fz2_4_12
  · exact match_zero_fix ⟨5, by decide⟩ ⟨12, by decide⟩ p hp j hj hq fz1_5_12 fz2_5_12
  · exact match_zero_fix ⟨6, by decide⟩ ⟨12, by decide⟩ p hp j hj hq fz1_6_12 fz2_6_12
  · exact match_zero_fix ⟨7, by decide⟩ ⟨12, by decide⟩ p hp j hj hq fz1_7_12 fz2_7_12
  · exact match_zero_fix ⟨8, by decide⟩ ⟨12, by decide⟩ p hp j hj hq fz1_8_12 fz2_8_12
  · exact match_zero_fix ⟨9, by decide⟩ ⟨12, by decide⟩ p hp j hj hq fz1_9_12 fz2_9_12
  · exact match_zero_fix ⟨10, by decide⟩ ⟨12, by decide⟩ p hp j hj hq fz1_10_12 fz2_10_12
  · exact match_zero_fix ⟨11, by decide⟩ ⟨12, by decide⟩ p hp j hj hq fz1_11_12 fz2_11_12
  · exact pair_12_12 p hp hrep j hj hq
  · exact match_zero_fix ⟨13, by decide⟩ ⟨12, by decide⟩ p hp j hj hq fz1_13_12 fz2_13_12
  · exact match_zero_fix ⟨14, by decide⟩ ⟨12, by decide⟩ p hp j hj hq fz1_14_12 fz2_14_12
  · exact match_zero_fix ⟨15, by decide⟩ ⟨12, by decide⟩ p hp j hj hq fz1_15_12 fz2_15_12
  · exact match_zero_fix ⟨16, by decide⟩ ⟨12, by decide⟩ p hp j hj hq fz1_16_12 fz2_16_12
  · exact match_zero_fix ⟨17, by decide⟩ ⟨12, by decide⟩ p hp j hj hq fz1_17_12 fz2_17_12
  · exact match_zero_fix ⟨18, by decide⟩ ⟨12, by decide⟩ p hp j hj hq fz1_18_12 fz2_18_12
  · exact pair_19_12 p hp hrep j hj hq
  · exact pair_20_12 p hp hrep j hj hq
  · exact pair_21_12 p hp hrep j hj hq
  · exact pair_22_12 p hp hrep j hj hq
  · exact pair_23_12 p hp hrep j hj hq
  · exact pair_24_12 p hp hrep j hj hq
  · exact pair_25_12 p hp hrep j hj hq
  · exact pair_26_12 p hp hrep j hj hq
  · exact pair_27_12 p hp hrep j hj hq
  · exact pair_28_12 p hp hrep j hj hq
  · exact pair_29_12 p hp hrep j hj hq
  · exact pair_30_12 p hp hrep j hj hq
  · exact pair_31_12 p hp hrep j hj hq
  · exact pair_32_12 p hp hrep j hj hq
  · exact pair_33_12 p hp hrep j hj hq
  · exact pair_34_12 p hp hrep j hj hq
  · exact pair_35_12 p hp hrep j hj hq
  · exact pair_36_12 p hp hrep j hj hq
  · exact pair_37_12 p hp hrep j hj hq
  · exact pair_38_12 p hp hrep j hj hq
  · exact pair_39_12 p hp hrep j hj hq
  · exact pair_40_12 p hp hrep j hj hq
  · exact pair_41_12 p hp hrep j hj hq
  · exact pair_42_12 p hp hrep j hj hq
  · exact pair_43_12 p hp hrep j hj hq
  · exact pair_44_12 p hp hrep j hj hq
  · exact pair_45_12 p hp hrep j hj hq
  · exact pair_46_12 p hp hrep j hj hq
  · exact pair_47_12 p hp hrep j hj hq
  · exact pair_48_12 p hp hrep j hj hq
  · exact pair_49_12 p hp hrep j hj hq
  · exact pair_50_12 p hp hrep j hj hq
  · exact pair_51_12 p hp hrep j hj hq
  · exact pair_52_12 p hp hrep j hj hq
  · exact pair_53_12 p hp hrep j hj hq
  · exact pair_54_12 p hp hrep j hj hq
  · exact pair_55_12 p hp hrep j hj hq
  · exact pair_56_12 p hp hrep j hj hq
  · exact pair_57_12 p hp hrep j hj hq
  · exact pair_58_12 p hp hrep j hj hq
  · exact pair_59_12 p hp hrep j hj hq
  · exact pair_60_12 p hp hrep j hj hq
  · exact pair_61_12 p hp hrep j hj hq
  · exact pair_62_12 p hp hrep j hj hq
  · exact pair_63_12 p hp hrep j hj hq
  · exact pair_64_12 p hp hrep j hj hq
  · exact pair_65_12 p hp hrep j hj hq
  · exact pair_66_12 p hp hrep j hj hq
  · exact pair_67_12 p hp hrep j hj hq
  · exact pair_68_12 p hp hrep j hj hq
  · exact pair_69_12 p hp hrep j hj hq
  · exact pair_70_12 p hp hrep j hj hq
  · exact pair_71_12 p hp hrep j hj hq
  · exact pair_72_12 p hp hrep j hj hq
  · exact pair_73_12 p hp hrep j hj hq
  · exact pair_74_12 p hp hrep j hj hq
  · exact pair_75_12 p hp hrep j hj hq
  · exact pair_76_12 p hp hrep j hj hq
  · exact pair_77_12 p hp hrep j hj hq
  · exact pair_78_12 p hp hrep j hj hq
  · exact pair_79_12 p hp hrep j hj hq
  · exact pair_80_12 p hp hrep j hj hq
  · exact pair_81_12 p hp hrep j hj hq
  · exact pair_82_12 p hp hrep j hj hq
  · exact pair_83_12 p hp hrep j hj hq
  · exact pair_84_12 p hp hrep j hj hq
  · exact pair_85_12 p hp hrep j hj hq
  · exact pair_86_12 p hp hrep j hj hq
  · exact pair_87_12 p hp hrep j hj hq
  · exact pair_88_12 p hp hrep j hj hq
  · exact pair_89_12 p hp hrep j hj hq
  · exact pair_90_12 p hp hrep j hj hq
  · exact pair_91_12 p hp hrep j hj hq
  · exact pair_92_12 p hp hrep j hj hq
  · exact pair_93_12 p hp hrep j hj hq
  · exact pair_94_12 p hp hrep j hj hq
  · exact pair_95_12 p hp hrep j hj hq
  · exact pair_96_12 p hp hrep j hj hq
  · exact pair_97_12 p hp hrep j hj hq
  · exact pair_98_12 p hp hrep j hj hq
  · exact pair_99_12 p hp hrep j hj hq
  · exact pair_100_12 p hp hrep j hj hq
  · exact pair_101_12 p hp hrep j hj hq
  · exact pair_102_12 p hp hrep j hj hq
  · exact pair_103_12 p hp hrep j hj hq
  · exact pair_104_12 p hp hrep j hj hq
  · exact pair_105_12 p hp hrep j hj hq
  · exact pair_106_12 p hp hrep j hj hq
  · exact pair_107_12 p hp hrep j hj hq
  · exact pair_108_12 p hp hrep j hj hq
  · exact pair_109_12 p hp hrep j hj hq
  · exact pair_110_12 p hp hrep j hj hq
  · exact pair_111_12 p hp hrep j hj hq
  · exact pair_112_12 p hp hrep j hj hq
  · exact pair_113_12 p hp hrep j hj hq
  · exact pair_114_12 p hp hrep j hj hq
  · exact pair_115_12 p hp hrep j hj hq
  · exact pair_116_12 p hp hrep j hj hq
  · exact pair_117_12 p hp hrep j hj hq
  · exact pair_118_12 p hp hrep j hj hq
  · exact pair_119_12 p hp hrep j hj hq
  · exact pair_120_12 p hp hrep j hj hq
  · exact pair_121_12 p hp hrep j hj hq
  · exact pair_122_12 p hp hrep j hj hq
  · exact pair_123_12 p hp hrep j hj hq
  · exact pair_124_12 p hp hrep j hj hq
  · exact pair_125_12 p hp hrep j hj hq
  · exact pair_126_12 p hp hrep j hj hq
  · exact pair_127_12 p hp hrep j hj hq
  · exact pair_128_12 p hp hrep j hj hq
  · exact pair_129_12 p hp hrep j hj hq
  · exact pair_130_12 p hp hrep j hj hq
  · exact pair_131_12 p hp hrep j hj hq
  · exact pair_132_12 p hp hrep j hj hq
  · exact pair_133_12 p hp hrep j hj hq
  · exact pair_134_12 p hp hrep j hj hq
  · exact pair_135_12 p hp hrep j hj hq
  · exact pair_136_12 p hp hrep j hj hq
  · exact pair_137_12 p hp hrep j hj hq
  · exact pair_138_12 p hp hrep j hj hq
  · exact pair_139_12 p hp hrep j hj hq
  · exact pair_140_12 p hp hrep j hj hq
  · exact pair_141_12 p hp hrep j hj hq
  · exact pair_142_12 p hp hrep j hj hq
  · exact pair_143_12 p hp hrep j hj hq
  · exact pair_144_12 p hp hrep j hj hq
  · exact pair_145_12 p hp hrep j hj hq
  · exact pair_146_12 p hp hrep j hj hq
  · exact pair_147_12 p hp hrep j hj hq

theorem master_13 (p : Nat) (hp : p < (Q2.transData.getD 13 []).length)
    (hrep : (Q2.cosetIsRep.getD 13 []).getD p false = true)
    (rK : Fin 148) (j : Nat) (hj : j < (repChars.getD rK.val []).length)
    (hq : (normIsRep.getD rK.val []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ p hp)
        (rowE2 rK j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ p (transLenTr ⟨13, by decide⟩ p hp)) (rowE1 rK j hj) := by
  rcases rK with ⟨nK, hnK⟩; interval_cases nK
  · exact match_zero_len ⟨0, by decide⟩ ⟨13, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨1, by decide⟩ ⟨13, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨2, by decide⟩ ⟨13, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨3, by decide⟩ ⟨13, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨4, by decide⟩ ⟨13, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨5, by decide⟩ ⟨13, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨6, by decide⟩ ⟨13, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨7, by decide⟩ ⟨13, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨8, by decide⟩ ⟨13, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨9, by decide⟩ ⟨13, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨10, by decide⟩ ⟨13, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨11, by decide⟩ ⟨13, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨12, by decide⟩ ⟨13, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact pair_13_13 p hp hrep j hj hq
  · exact match_zero_fix ⟨14, by decide⟩ ⟨13, by decide⟩ p hp j hj hq fz1_14_13 fz2_14_13
  · exact match_zero_fix ⟨15, by decide⟩ ⟨13, by decide⟩ p hp j hj hq fz1_15_13 fz2_15_13
  · exact match_zero_fix ⟨16, by decide⟩ ⟨13, by decide⟩ p hp j hj hq fz1_16_13 fz2_16_13
  · exact match_zero_fix ⟨17, by decide⟩ ⟨13, by decide⟩ p hp j hj hq fz1_17_13 fz2_17_13
  · exact match_zero_fix ⟨18, by decide⟩ ⟨13, by decide⟩ p hp j hj hq fz1_18_13 fz2_18_13
  · exact match_zero_fix ⟨19, by decide⟩ ⟨13, by decide⟩ p hp j hj hq fz1_19_13 fz2_19_13
  · exact match_zero_fix ⟨20, by decide⟩ ⟨13, by decide⟩ p hp j hj hq fz1_20_13 fz2_20_13
  · exact match_zero_fix ⟨21, by decide⟩ ⟨13, by decide⟩ p hp j hj hq fz1_21_13 fz2_21_13
  · exact match_zero_fix ⟨22, by decide⟩ ⟨13, by decide⟩ p hp j hj hq fz1_22_13 fz2_22_13
  · exact match_zero_fix ⟨23, by decide⟩ ⟨13, by decide⟩ p hp j hj hq fz1_23_13 fz2_23_13
  · exact match_zero_fix ⟨24, by decide⟩ ⟨13, by decide⟩ p hp j hj hq fz1_24_13 fz2_24_13
  · exact match_zero_fix ⟨25, by decide⟩ ⟨13, by decide⟩ p hp j hj hq fz1_25_13 fz2_25_13
  · exact match_zero_fix ⟨26, by decide⟩ ⟨13, by decide⟩ p hp j hj hq fz1_26_13 fz2_26_13
  · exact match_zero_fix ⟨27, by decide⟩ ⟨13, by decide⟩ p hp j hj hq fz1_27_13 fz2_27_13
  · exact match_zero_fix ⟨28, by decide⟩ ⟨13, by decide⟩ p hp j hj hq fz1_28_13 fz2_28_13
  · exact match_zero_fix ⟨29, by decide⟩ ⟨13, by decide⟩ p hp j hj hq fz1_29_13 fz2_29_13
  · exact match_zero_fix ⟨30, by decide⟩ ⟨13, by decide⟩ p hp j hj hq fz1_30_13 fz2_30_13
  · exact match_zero_fix ⟨31, by decide⟩ ⟨13, by decide⟩ p hp j hj hq fz1_31_13 fz2_31_13
  · exact match_zero_fix ⟨32, by decide⟩ ⟨13, by decide⟩ p hp j hj hq fz1_32_13 fz2_32_13
  · exact match_zero_fix ⟨33, by decide⟩ ⟨13, by decide⟩ p hp j hj hq fz1_33_13 fz2_33_13
  · exact match_zero_fix ⟨34, by decide⟩ ⟨13, by decide⟩ p hp j hj hq fz1_34_13 fz2_34_13
  · exact match_zero_fix ⟨35, by decide⟩ ⟨13, by decide⟩ p hp j hj hq fz1_35_13 fz2_35_13
  · exact match_zero_fix ⟨36, by decide⟩ ⟨13, by decide⟩ p hp j hj hq fz1_36_13 fz2_36_13
  · exact match_zero_fix ⟨37, by decide⟩ ⟨13, by decide⟩ p hp j hj hq fz1_37_13 fz2_37_13
  · exact match_zero_fix ⟨38, by decide⟩ ⟨13, by decide⟩ p hp j hj hq fz1_38_13 fz2_38_13
  · exact match_zero_fix ⟨39, by decide⟩ ⟨13, by decide⟩ p hp j hj hq fz1_39_13 fz2_39_13
  · exact match_zero_fix ⟨40, by decide⟩ ⟨13, by decide⟩ p hp j hj hq fz1_40_13 fz2_40_13
  · exact match_zero_fix ⟨41, by decide⟩ ⟨13, by decide⟩ p hp j hj hq fz1_41_13 fz2_41_13
  · exact match_zero_fix ⟨42, by decide⟩ ⟨13, by decide⟩ p hp j hj hq fz1_42_13 fz2_42_13
  · exact match_zero_fix ⟨43, by decide⟩ ⟨13, by decide⟩ p hp j hj hq fz1_43_13 fz2_43_13
  · exact match_zero_fix ⟨44, by decide⟩ ⟨13, by decide⟩ p hp j hj hq fz1_44_13 fz2_44_13
  · exact match_zero_fix ⟨45, by decide⟩ ⟨13, by decide⟩ p hp j hj hq fz1_45_13 fz2_45_13
  · exact match_zero_fix ⟨46, by decide⟩ ⟨13, by decide⟩ p hp j hj hq fz1_46_13 fz2_46_13
  · exact match_zero_fix ⟨47, by decide⟩ ⟨13, by decide⟩ p hp j hj hq fz1_47_13 fz2_47_13
  · exact match_zero_fix ⟨48, by decide⟩ ⟨13, by decide⟩ p hp j hj hq fz1_48_13 fz2_48_13
  · exact match_zero_fix ⟨49, by decide⟩ ⟨13, by decide⟩ p hp j hj hq fz1_49_13 fz2_49_13
  · exact match_zero_fix ⟨50, by decide⟩ ⟨13, by decide⟩ p hp j hj hq fz1_50_13 fz2_50_13
  · exact match_zero_fix ⟨51, by decide⟩ ⟨13, by decide⟩ p hp j hj hq fz1_51_13 fz2_51_13
  · exact match_zero_fix ⟨52, by decide⟩ ⟨13, by decide⟩ p hp j hj hq fz1_52_13 fz2_52_13
  · exact match_zero_fix ⟨53, by decide⟩ ⟨13, by decide⟩ p hp j hj hq fz1_53_13 fz2_53_13
  · exact match_zero_fix ⟨54, by decide⟩ ⟨13, by decide⟩ p hp j hj hq fz1_54_13 fz2_54_13
  · exact match_zero_fix ⟨55, by decide⟩ ⟨13, by decide⟩ p hp j hj hq fz1_55_13 fz2_55_13
  · exact match_zero_fix ⟨56, by decide⟩ ⟨13, by decide⟩ p hp j hj hq fz1_56_13 fz2_56_13
  · exact match_zero_fix ⟨57, by decide⟩ ⟨13, by decide⟩ p hp j hj hq fz1_57_13 fz2_57_13
  · exact match_zero_fix ⟨58, by decide⟩ ⟨13, by decide⟩ p hp j hj hq fz1_58_13 fz2_58_13
  · exact match_zero_fix ⟨59, by decide⟩ ⟨13, by decide⟩ p hp j hj hq fz1_59_13 fz2_59_13
  · exact match_zero_fix ⟨60, by decide⟩ ⟨13, by decide⟩ p hp j hj hq fz1_60_13 fz2_60_13
  · exact match_zero_fix ⟨61, by decide⟩ ⟨13, by decide⟩ p hp j hj hq fz1_61_13 fz2_61_13
  · exact match_zero_fix ⟨62, by decide⟩ ⟨13, by decide⟩ p hp j hj hq fz1_62_13 fz2_62_13
  · exact match_zero_fix ⟨63, by decide⟩ ⟨13, by decide⟩ p hp j hj hq fz1_63_13 fz2_63_13
  · exact match_zero_fix ⟨64, by decide⟩ ⟨13, by decide⟩ p hp j hj hq fz1_64_13 fz2_64_13
  · exact match_zero_fix ⟨65, by decide⟩ ⟨13, by decide⟩ p hp j hj hq fz1_65_13 fz2_65_13
  · exact match_zero_fix ⟨66, by decide⟩ ⟨13, by decide⟩ p hp j hj hq fz1_66_13 fz2_66_13
  · exact match_zero_fix ⟨67, by decide⟩ ⟨13, by decide⟩ p hp j hj hq fz1_67_13 fz2_67_13
  · exact match_zero_fix ⟨68, by decide⟩ ⟨13, by decide⟩ p hp j hj hq fz1_68_13 fz2_68_13
  · exact match_zero_fix ⟨69, by decide⟩ ⟨13, by decide⟩ p hp j hj hq fz1_69_13 fz2_69_13
  · exact match_zero_fix ⟨70, by decide⟩ ⟨13, by decide⟩ p hp j hj hq fz1_70_13 fz2_70_13
  · exact match_zero_fix ⟨71, by decide⟩ ⟨13, by decide⟩ p hp j hj hq fz1_71_13 fz2_71_13
  · exact match_zero_fix ⟨72, by decide⟩ ⟨13, by decide⟩ p hp j hj hq fz1_72_13 fz2_72_13
  · exact match_zero_fix ⟨73, by decide⟩ ⟨13, by decide⟩ p hp j hj hq fz1_73_13 fz2_73_13
  · exact match_zero_fix ⟨74, by decide⟩ ⟨13, by decide⟩ p hp j hj hq fz1_74_13 fz2_74_13
  · exact match_zero_fix ⟨75, by decide⟩ ⟨13, by decide⟩ p hp j hj hq fz1_75_13 fz2_75_13
  · exact match_zero_fix ⟨76, by decide⟩ ⟨13, by decide⟩ p hp j hj hq fz1_76_13 fz2_76_13
  · exact match_zero_fix ⟨77, by decide⟩ ⟨13, by decide⟩ p hp j hj hq fz1_77_13 fz2_77_13
  · exact match_zero_fix ⟨78, by decide⟩ ⟨13, by decide⟩ p hp j hj hq fz1_78_13 fz2_78_13
  · exact match_zero_fix ⟨79, by decide⟩ ⟨13, by decide⟩ p hp j hj hq fz1_79_13 fz2_79_13
  · exact pair_80_13 p hp hrep j hj hq
  · exact match_zero_fix ⟨81, by decide⟩ ⟨13, by decide⟩ p hp j hj hq fz1_81_13 fz2_81_13
  · exact match_zero_fix ⟨82, by decide⟩ ⟨13, by decide⟩ p hp j hj hq fz1_82_13 fz2_82_13
  · exact match_zero_fix ⟨83, by decide⟩ ⟨13, by decide⟩ p hp j hj hq fz1_83_13 fz2_83_13
  · exact match_zero_fix ⟨84, by decide⟩ ⟨13, by decide⟩ p hp j hj hq fz1_84_13 fz2_84_13
  · exact match_zero_fix ⟨85, by decide⟩ ⟨13, by decide⟩ p hp j hj hq fz1_85_13 fz2_85_13
  · exact match_zero_fix ⟨86, by decide⟩ ⟨13, by decide⟩ p hp j hj hq fz1_86_13 fz2_86_13
  · exact match_zero_fix ⟨87, by decide⟩ ⟨13, by decide⟩ p hp j hj hq fz1_87_13 fz2_87_13
  · exact match_zero_fix ⟨88, by decide⟩ ⟨13, by decide⟩ p hp j hj hq fz1_88_13 fz2_88_13
  · exact match_zero_fix ⟨89, by decide⟩ ⟨13, by decide⟩ p hp j hj hq fz1_89_13 fz2_89_13
  · exact match_zero_fix ⟨90, by decide⟩ ⟨13, by decide⟩ p hp j hj hq fz1_90_13 fz2_90_13
  · exact match_zero_fix ⟨91, by decide⟩ ⟨13, by decide⟩ p hp j hj hq fz1_91_13 fz2_91_13
  · exact match_zero_fix ⟨92, by decide⟩ ⟨13, by decide⟩ p hp j hj hq fz1_92_13 fz2_92_13
  · exact match_zero_fix ⟨93, by decide⟩ ⟨13, by decide⟩ p hp j hj hq fz1_93_13 fz2_93_13
  · exact match_zero_fix ⟨94, by decide⟩ ⟨13, by decide⟩ p hp j hj hq fz1_94_13 fz2_94_13
  · exact match_zero_fix ⟨95, by decide⟩ ⟨13, by decide⟩ p hp j hj hq fz1_95_13 fz2_95_13
  · exact match_zero_fix ⟨96, by decide⟩ ⟨13, by decide⟩ p hp j hj hq fz1_96_13 fz2_96_13
  · exact match_zero_fix ⟨97, by decide⟩ ⟨13, by decide⟩ p hp j hj hq fz1_97_13 fz2_97_13
  · exact match_zero_fix ⟨98, by decide⟩ ⟨13, by decide⟩ p hp j hj hq fz1_98_13 fz2_98_13
  · exact match_zero_fix ⟨99, by decide⟩ ⟨13, by decide⟩ p hp j hj hq fz1_99_13 fz2_99_13
  · exact match_zero_fix ⟨100, by decide⟩ ⟨13, by decide⟩ p hp j hj hq fz1_100_13 fz2_100_13
  · exact match_zero_fix ⟨101, by decide⟩ ⟨13, by decide⟩ p hp j hj hq fz1_101_13 fz2_101_13
  · exact match_zero_fix ⟨102, by decide⟩ ⟨13, by decide⟩ p hp j hj hq fz1_102_13 fz2_102_13
  · exact match_zero_fix ⟨103, by decide⟩ ⟨13, by decide⟩ p hp j hj hq fz1_103_13 fz2_103_13
  · exact match_zero_fix ⟨104, by decide⟩ ⟨13, by decide⟩ p hp j hj hq fz1_104_13 fz2_104_13
  · exact match_zero_fix ⟨105, by decide⟩ ⟨13, by decide⟩ p hp j hj hq fz1_105_13 fz2_105_13
  · exact match_zero_fix ⟨106, by decide⟩ ⟨13, by decide⟩ p hp j hj hq fz1_106_13 fz2_106_13
  · exact match_zero_fix ⟨107, by decide⟩ ⟨13, by decide⟩ p hp j hj hq fz1_107_13 fz2_107_13
  · exact match_zero_fix ⟨108, by decide⟩ ⟨13, by decide⟩ p hp j hj hq fz1_108_13 fz2_108_13
  · exact match_zero_fix ⟨109, by decide⟩ ⟨13, by decide⟩ p hp j hj hq fz1_109_13 fz2_109_13
  · exact match_zero_fix ⟨110, by decide⟩ ⟨13, by decide⟩ p hp j hj hq fz1_110_13 fz2_110_13
  · exact match_zero_fix ⟨111, by decide⟩ ⟨13, by decide⟩ p hp j hj hq fz1_111_13 fz2_111_13
  · exact match_zero_fix ⟨112, by decide⟩ ⟨13, by decide⟩ p hp j hj hq fz1_112_13 fz2_112_13
  · exact match_zero_fix ⟨113, by decide⟩ ⟨13, by decide⟩ p hp j hj hq fz1_113_13 fz2_113_13
  · exact match_zero_fix ⟨114, by decide⟩ ⟨13, by decide⟩ p hp j hj hq fz1_114_13 fz2_114_13
  · exact match_zero_fix ⟨115, by decide⟩ ⟨13, by decide⟩ p hp j hj hq fz1_115_13 fz2_115_13
  · exact pair_116_13 p hp hrep j hj hq
  · exact pair_117_13 p hp hrep j hj hq
  · exact pair_118_13 p hp hrep j hj hq
  · exact pair_119_13 p hp hrep j hj hq
  · exact pair_120_13 p hp hrep j hj hq
  · exact match_zero_fix ⟨121, by decide⟩ ⟨13, by decide⟩ p hp j hj hq fz1_121_13 fz2_121_13
  · exact match_zero_fix ⟨122, by decide⟩ ⟨13, by decide⟩ p hp j hj hq fz1_122_13 fz2_122_13
  · exact match_zero_fix ⟨123, by decide⟩ ⟨13, by decide⟩ p hp j hj hq fz1_123_13 fz2_123_13
  · exact match_zero_fix ⟨124, by decide⟩ ⟨13, by decide⟩ p hp j hj hq fz1_124_13 fz2_124_13
  · exact match_zero_fix ⟨125, by decide⟩ ⟨13, by decide⟩ p hp j hj hq fz1_125_13 fz2_125_13
  · exact match_zero_fix ⟨126, by decide⟩ ⟨13, by decide⟩ p hp j hj hq fz1_126_13 fz2_126_13
  · exact match_zero_fix ⟨127, by decide⟩ ⟨13, by decide⟩ p hp j hj hq fz1_127_13 fz2_127_13
  · exact match_zero_fix ⟨128, by decide⟩ ⟨13, by decide⟩ p hp j hj hq fz1_128_13 fz2_128_13
  · exact match_zero_fix ⟨129, by decide⟩ ⟨13, by decide⟩ p hp j hj hq fz1_129_13 fz2_129_13
  · exact match_zero_fix ⟨130, by decide⟩ ⟨13, by decide⟩ p hp j hj hq fz1_130_13 fz2_130_13
  · exact match_zero_fix ⟨131, by decide⟩ ⟨13, by decide⟩ p hp j hj hq fz1_131_13 fz2_131_13
  · exact match_zero_fix ⟨132, by decide⟩ ⟨13, by decide⟩ p hp j hj hq fz1_132_13 fz2_132_13
  · exact match_zero_fix ⟨133, by decide⟩ ⟨13, by decide⟩ p hp j hj hq fz1_133_13 fz2_133_13
  · exact match_zero_fix ⟨134, by decide⟩ ⟨13, by decide⟩ p hp j hj hq fz1_134_13 fz2_134_13
  · exact match_zero_fix ⟨135, by decide⟩ ⟨13, by decide⟩ p hp j hj hq fz1_135_13 fz2_135_13
  · exact match_zero_fix ⟨136, by decide⟩ ⟨13, by decide⟩ p hp j hj hq fz1_136_13 fz2_136_13
  · exact match_zero_fix ⟨137, by decide⟩ ⟨13, by decide⟩ p hp j hj hq fz1_137_13 fz2_137_13
  · exact match_zero_fix ⟨138, by decide⟩ ⟨13, by decide⟩ p hp j hj hq fz1_138_13 fz2_138_13
  · exact match_zero_fix ⟨139, by decide⟩ ⟨13, by decide⟩ p hp j hj hq fz1_139_13 fz2_139_13
  · exact match_zero_fix ⟨140, by decide⟩ ⟨13, by decide⟩ p hp j hj hq fz1_140_13 fz2_140_13
  · exact pair_141_13 p hp hrep j hj hq
  · exact match_zero_fix ⟨142, by decide⟩ ⟨13, by decide⟩ p hp j hj hq fz1_142_13 fz2_142_13
  · exact match_zero_fix ⟨143, by decide⟩ ⟨13, by decide⟩ p hp j hj hq fz1_143_13 fz2_143_13
  · exact match_zero_fix ⟨144, by decide⟩ ⟨13, by decide⟩ p hp j hj hq fz1_144_13 fz2_144_13
  · exact match_zero_fix ⟨145, by decide⟩ ⟨13, by decide⟩ p hp j hj hq fz1_145_13 fz2_145_13
  · exact match_zero_fix ⟨146, by decide⟩ ⟨13, by decide⟩ p hp j hj hq fz1_146_13 fz2_146_13
  · exact pair_147_13 p hp hrep j hj hq

theorem master_14 (p : Nat) (hp : p < (Q2.transData.getD 14 []).length)
    (hrep : (Q2.cosetIsRep.getD 14 []).getD p false = true)
    (rK : Fin 148) (j : Nat) (hj : j < (repChars.getD rK.val []).length)
    (hq : (normIsRep.getD rK.val []).getD j false = true) :
    species (Q2.reps (⟨14, by decide⟩ : Fin 148)) (colE2 ⟨14, by decide⟩ p hp)
        (rowE2 rK j hj hq)
      = species (reps (⟨14, by decide⟩ : Fin 148))
        (colE1 ⟨14, by decide⟩ p (transLenTr ⟨14, by decide⟩ p hp)) (rowE1 rK j hj) := by
  rcases rK with ⟨nK, hnK⟩; interval_cases nK
  · exact match_zero_len ⟨0, by decide⟩ ⟨14, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨1, by decide⟩ ⟨14, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨2, by decide⟩ ⟨14, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨3, by decide⟩ ⟨14, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨4, by decide⟩ ⟨14, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨5, by decide⟩ ⟨14, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨6, by decide⟩ ⟨14, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨7, by decide⟩ ⟨14, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨8, by decide⟩ ⟨14, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨9, by decide⟩ ⟨14, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨10, by decide⟩ ⟨14, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨11, by decide⟩ ⟨14, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨12, by decide⟩ ⟨14, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_fix ⟨13, by decide⟩ ⟨14, by decide⟩ p hp j hj hq fz1_13_14 fz2_13_14
  · exact pair_14_14 p hp hrep j hj hq
  · exact match_zero_fix ⟨15, by decide⟩ ⟨14, by decide⟩ p hp j hj hq fz1_15_14 fz2_15_14
  · exact match_zero_fix ⟨16, by decide⟩ ⟨14, by decide⟩ p hp j hj hq fz1_16_14 fz2_16_14
  · exact match_zero_fix ⟨17, by decide⟩ ⟨14, by decide⟩ p hp j hj hq fz1_17_14 fz2_17_14
  · exact match_zero_fix ⟨18, by decide⟩ ⟨14, by decide⟩ p hp j hj hq fz1_18_14 fz2_18_14
  · exact match_zero_fix ⟨19, by decide⟩ ⟨14, by decide⟩ p hp j hj hq fz1_19_14 fz2_19_14
  · exact match_zero_fix ⟨20, by decide⟩ ⟨14, by decide⟩ p hp j hj hq fz1_20_14 fz2_20_14
  · exact match_zero_fix ⟨21, by decide⟩ ⟨14, by decide⟩ p hp j hj hq fz1_21_14 fz2_21_14
  · exact match_zero_fix ⟨22, by decide⟩ ⟨14, by decide⟩ p hp j hj hq fz1_22_14 fz2_22_14
  · exact match_zero_fix ⟨23, by decide⟩ ⟨14, by decide⟩ p hp j hj hq fz1_23_14 fz2_23_14
  · exact match_zero_fix ⟨24, by decide⟩ ⟨14, by decide⟩ p hp j hj hq fz1_24_14 fz2_24_14
  · exact match_zero_fix ⟨25, by decide⟩ ⟨14, by decide⟩ p hp j hj hq fz1_25_14 fz2_25_14
  · exact match_zero_fix ⟨26, by decide⟩ ⟨14, by decide⟩ p hp j hj hq fz1_26_14 fz2_26_14
  · exact match_zero_fix ⟨27, by decide⟩ ⟨14, by decide⟩ p hp j hj hq fz1_27_14 fz2_27_14
  · exact match_zero_fix ⟨28, by decide⟩ ⟨14, by decide⟩ p hp j hj hq fz1_28_14 fz2_28_14
  · exact match_zero_fix ⟨29, by decide⟩ ⟨14, by decide⟩ p hp j hj hq fz1_29_14 fz2_29_14
  · exact match_zero_fix ⟨30, by decide⟩ ⟨14, by decide⟩ p hp j hj hq fz1_30_14 fz2_30_14
  · exact match_zero_fix ⟨31, by decide⟩ ⟨14, by decide⟩ p hp j hj hq fz1_31_14 fz2_31_14
  · exact match_zero_fix ⟨32, by decide⟩ ⟨14, by decide⟩ p hp j hj hq fz1_32_14 fz2_32_14
  · exact match_zero_fix ⟨33, by decide⟩ ⟨14, by decide⟩ p hp j hj hq fz1_33_14 fz2_33_14
  · exact match_zero_fix ⟨34, by decide⟩ ⟨14, by decide⟩ p hp j hj hq fz1_34_14 fz2_34_14
  · exact match_zero_fix ⟨35, by decide⟩ ⟨14, by decide⟩ p hp j hj hq fz1_35_14 fz2_35_14
  · exact match_zero_fix ⟨36, by decide⟩ ⟨14, by decide⟩ p hp j hj hq fz1_36_14 fz2_36_14
  · exact match_zero_fix ⟨37, by decide⟩ ⟨14, by decide⟩ p hp j hj hq fz1_37_14 fz2_37_14
  · exact match_zero_fix ⟨38, by decide⟩ ⟨14, by decide⟩ p hp j hj hq fz1_38_14 fz2_38_14
  · exact match_zero_fix ⟨39, by decide⟩ ⟨14, by decide⟩ p hp j hj hq fz1_39_14 fz2_39_14
  · exact match_zero_fix ⟨40, by decide⟩ ⟨14, by decide⟩ p hp j hj hq fz1_40_14 fz2_40_14
  · exact match_zero_fix ⟨41, by decide⟩ ⟨14, by decide⟩ p hp j hj hq fz1_41_14 fz2_41_14
  · exact match_zero_fix ⟨42, by decide⟩ ⟨14, by decide⟩ p hp j hj hq fz1_42_14 fz2_42_14
  · exact match_zero_fix ⟨43, by decide⟩ ⟨14, by decide⟩ p hp j hj hq fz1_43_14 fz2_43_14
  · exact match_zero_fix ⟨44, by decide⟩ ⟨14, by decide⟩ p hp j hj hq fz1_44_14 fz2_44_14
  · exact match_zero_fix ⟨45, by decide⟩ ⟨14, by decide⟩ p hp j hj hq fz1_45_14 fz2_45_14
  · exact match_zero_fix ⟨46, by decide⟩ ⟨14, by decide⟩ p hp j hj hq fz1_46_14 fz2_46_14
  · exact match_zero_fix ⟨47, by decide⟩ ⟨14, by decide⟩ p hp j hj hq fz1_47_14 fz2_47_14
  · exact match_zero_fix ⟨48, by decide⟩ ⟨14, by decide⟩ p hp j hj hq fz1_48_14 fz2_48_14
  · exact match_zero_fix ⟨49, by decide⟩ ⟨14, by decide⟩ p hp j hj hq fz1_49_14 fz2_49_14
  · exact match_zero_fix ⟨50, by decide⟩ ⟨14, by decide⟩ p hp j hj hq fz1_50_14 fz2_50_14
  · exact match_zero_fix ⟨51, by decide⟩ ⟨14, by decide⟩ p hp j hj hq fz1_51_14 fz2_51_14
  · exact match_zero_fix ⟨52, by decide⟩ ⟨14, by decide⟩ p hp j hj hq fz1_52_14 fz2_52_14
  · exact match_zero_fix ⟨53, by decide⟩ ⟨14, by decide⟩ p hp j hj hq fz1_53_14 fz2_53_14
  · exact match_zero_fix ⟨54, by decide⟩ ⟨14, by decide⟩ p hp j hj hq fz1_54_14 fz2_54_14
  · exact match_zero_fix ⟨55, by decide⟩ ⟨14, by decide⟩ p hp j hj hq fz1_55_14 fz2_55_14
  · exact match_zero_fix ⟨56, by decide⟩ ⟨14, by decide⟩ p hp j hj hq fz1_56_14 fz2_56_14
  · exact match_zero_fix ⟨57, by decide⟩ ⟨14, by decide⟩ p hp j hj hq fz1_57_14 fz2_57_14
  · exact match_zero_fix ⟨58, by decide⟩ ⟨14, by decide⟩ p hp j hj hq fz1_58_14 fz2_58_14
  · exact match_zero_fix ⟨59, by decide⟩ ⟨14, by decide⟩ p hp j hj hq fz1_59_14 fz2_59_14
  · exact match_zero_fix ⟨60, by decide⟩ ⟨14, by decide⟩ p hp j hj hq fz1_60_14 fz2_60_14
  · exact match_zero_fix ⟨61, by decide⟩ ⟨14, by decide⟩ p hp j hj hq fz1_61_14 fz2_61_14
  · exact match_zero_fix ⟨62, by decide⟩ ⟨14, by decide⟩ p hp j hj hq fz1_62_14 fz2_62_14
  · exact match_zero_fix ⟨63, by decide⟩ ⟨14, by decide⟩ p hp j hj hq fz1_63_14 fz2_63_14
  · exact match_zero_fix ⟨64, by decide⟩ ⟨14, by decide⟩ p hp j hj hq fz1_64_14 fz2_64_14
  · exact match_zero_fix ⟨65, by decide⟩ ⟨14, by decide⟩ p hp j hj hq fz1_65_14 fz2_65_14
  · exact match_zero_fix ⟨66, by decide⟩ ⟨14, by decide⟩ p hp j hj hq fz1_66_14 fz2_66_14
  · exact match_zero_fix ⟨67, by decide⟩ ⟨14, by decide⟩ p hp j hj hq fz1_67_14 fz2_67_14
  · exact match_zero_fix ⟨68, by decide⟩ ⟨14, by decide⟩ p hp j hj hq fz1_68_14 fz2_68_14
  · exact match_zero_fix ⟨69, by decide⟩ ⟨14, by decide⟩ p hp j hj hq fz1_69_14 fz2_69_14
  · exact match_zero_fix ⟨70, by decide⟩ ⟨14, by decide⟩ p hp j hj hq fz1_70_14 fz2_70_14
  · exact match_zero_fix ⟨71, by decide⟩ ⟨14, by decide⟩ p hp j hj hq fz1_71_14 fz2_71_14
  · exact match_zero_fix ⟨72, by decide⟩ ⟨14, by decide⟩ p hp j hj hq fz1_72_14 fz2_72_14
  · exact match_zero_fix ⟨73, by decide⟩ ⟨14, by decide⟩ p hp j hj hq fz1_73_14 fz2_73_14
  · exact match_zero_fix ⟨74, by decide⟩ ⟨14, by decide⟩ p hp j hj hq fz1_74_14 fz2_74_14
  · exact match_zero_fix ⟨75, by decide⟩ ⟨14, by decide⟩ p hp j hj hq fz1_75_14 fz2_75_14
  · exact match_zero_fix ⟨76, by decide⟩ ⟨14, by decide⟩ p hp j hj hq fz1_76_14 fz2_76_14
  · exact match_zero_fix ⟨77, by decide⟩ ⟨14, by decide⟩ p hp j hj hq fz1_77_14 fz2_77_14
  · exact match_zero_fix ⟨78, by decide⟩ ⟨14, by decide⟩ p hp j hj hq fz1_78_14 fz2_78_14
  · exact match_zero_fix ⟨79, by decide⟩ ⟨14, by decide⟩ p hp j hj hq fz1_79_14 fz2_79_14
  · exact match_zero_fix ⟨80, by decide⟩ ⟨14, by decide⟩ p hp j hj hq fz1_80_14 fz2_80_14
  · exact match_zero_fix ⟨81, by decide⟩ ⟨14, by decide⟩ p hp j hj hq fz1_81_14 fz2_81_14
  · exact match_zero_fix ⟨82, by decide⟩ ⟨14, by decide⟩ p hp j hj hq fz1_82_14 fz2_82_14
  · exact match_zero_fix ⟨83, by decide⟩ ⟨14, by decide⟩ p hp j hj hq fz1_83_14 fz2_83_14
  · exact match_zero_fix ⟨84, by decide⟩ ⟨14, by decide⟩ p hp j hj hq fz1_84_14 fz2_84_14
  · exact pair_85_14 p hp hrep j hj hq
  · exact match_zero_fix ⟨86, by decide⟩ ⟨14, by decide⟩ p hp j hj hq fz1_86_14 fz2_86_14
  · exact match_zero_fix ⟨87, by decide⟩ ⟨14, by decide⟩ p hp j hj hq fz1_87_14 fz2_87_14
  · exact match_zero_fix ⟨88, by decide⟩ ⟨14, by decide⟩ p hp j hj hq fz1_88_14 fz2_88_14
  · exact match_zero_fix ⟨89, by decide⟩ ⟨14, by decide⟩ p hp j hj hq fz1_89_14 fz2_89_14
  · exact match_zero_fix ⟨90, by decide⟩ ⟨14, by decide⟩ p hp j hj hq fz1_90_14 fz2_90_14
  · exact match_zero_fix ⟨91, by decide⟩ ⟨14, by decide⟩ p hp j hj hq fz1_91_14 fz2_91_14
  · exact match_zero_fix ⟨92, by decide⟩ ⟨14, by decide⟩ p hp j hj hq fz1_92_14 fz2_92_14
  · exact match_zero_fix ⟨93, by decide⟩ ⟨14, by decide⟩ p hp j hj hq fz1_93_14 fz2_93_14
  · exact match_zero_fix ⟨94, by decide⟩ ⟨14, by decide⟩ p hp j hj hq fz1_94_14 fz2_94_14
  · exact match_zero_fix ⟨95, by decide⟩ ⟨14, by decide⟩ p hp j hj hq fz1_95_14 fz2_95_14
  · exact match_zero_fix ⟨96, by decide⟩ ⟨14, by decide⟩ p hp j hj hq fz1_96_14 fz2_96_14
  · exact match_zero_fix ⟨97, by decide⟩ ⟨14, by decide⟩ p hp j hj hq fz1_97_14 fz2_97_14
  · exact match_zero_fix ⟨98, by decide⟩ ⟨14, by decide⟩ p hp j hj hq fz1_98_14 fz2_98_14
  · exact match_zero_fix ⟨99, by decide⟩ ⟨14, by decide⟩ p hp j hj hq fz1_99_14 fz2_99_14
  · exact match_zero_fix ⟨100, by decide⟩ ⟨14, by decide⟩ p hp j hj hq fz1_100_14 fz2_100_14
  · exact match_zero_fix ⟨101, by decide⟩ ⟨14, by decide⟩ p hp j hj hq fz1_101_14 fz2_101_14
  · exact match_zero_fix ⟨102, by decide⟩ ⟨14, by decide⟩ p hp j hj hq fz1_102_14 fz2_102_14
  · exact match_zero_fix ⟨103, by decide⟩ ⟨14, by decide⟩ p hp j hj hq fz1_103_14 fz2_103_14
  · exact match_zero_fix ⟨104, by decide⟩ ⟨14, by decide⟩ p hp j hj hq fz1_104_14 fz2_104_14
  · exact match_zero_fix ⟨105, by decide⟩ ⟨14, by decide⟩ p hp j hj hq fz1_105_14 fz2_105_14
  · exact match_zero_fix ⟨106, by decide⟩ ⟨14, by decide⟩ p hp j hj hq fz1_106_14 fz2_106_14
  · exact match_zero_fix ⟨107, by decide⟩ ⟨14, by decide⟩ p hp j hj hq fz1_107_14 fz2_107_14
  · exact match_zero_fix ⟨108, by decide⟩ ⟨14, by decide⟩ p hp j hj hq fz1_108_14 fz2_108_14
  · exact match_zero_fix ⟨109, by decide⟩ ⟨14, by decide⟩ p hp j hj hq fz1_109_14 fz2_109_14
  · exact match_zero_fix ⟨110, by decide⟩ ⟨14, by decide⟩ p hp j hj hq fz1_110_14 fz2_110_14
  · exact match_zero_fix ⟨111, by decide⟩ ⟨14, by decide⟩ p hp j hj hq fz1_111_14 fz2_111_14
  · exact match_zero_fix ⟨112, by decide⟩ ⟨14, by decide⟩ p hp j hj hq fz1_112_14 fz2_112_14
  · exact match_zero_fix ⟨113, by decide⟩ ⟨14, by decide⟩ p hp j hj hq fz1_113_14 fz2_113_14
  · exact match_zero_fix ⟨114, by decide⟩ ⟨14, by decide⟩ p hp j hj hq fz1_114_14 fz2_114_14
  · exact match_zero_fix ⟨115, by decide⟩ ⟨14, by decide⟩ p hp j hj hq fz1_115_14 fz2_115_14
  · exact match_zero_fix ⟨116, by decide⟩ ⟨14, by decide⟩ p hp j hj hq fz1_116_14 fz2_116_14
  · exact match_zero_fix ⟨117, by decide⟩ ⟨14, by decide⟩ p hp j hj hq fz1_117_14 fz2_117_14
  · exact match_zero_fix ⟨118, by decide⟩ ⟨14, by decide⟩ p hp j hj hq fz1_118_14 fz2_118_14
  · exact match_zero_fix ⟨119, by decide⟩ ⟨14, by decide⟩ p hp j hj hq fz1_119_14 fz2_119_14
  · exact match_zero_fix ⟨120, by decide⟩ ⟨14, by decide⟩ p hp j hj hq fz1_120_14 fz2_120_14
  · exact match_zero_fix ⟨121, by decide⟩ ⟨14, by decide⟩ p hp j hj hq fz1_121_14 fz2_121_14
  · exact match_zero_fix ⟨122, by decide⟩ ⟨14, by decide⟩ p hp j hj hq fz1_122_14 fz2_122_14
  · exact match_zero_fix ⟨123, by decide⟩ ⟨14, by decide⟩ p hp j hj hq fz1_123_14 fz2_123_14
  · exact match_zero_fix ⟨124, by decide⟩ ⟨14, by decide⟩ p hp j hj hq fz1_124_14 fz2_124_14
  · exact match_zero_fix ⟨125, by decide⟩ ⟨14, by decide⟩ p hp j hj hq fz1_125_14 fz2_125_14
  · exact match_zero_fix ⟨126, by decide⟩ ⟨14, by decide⟩ p hp j hj hq fz1_126_14 fz2_126_14
  · exact match_zero_fix ⟨127, by decide⟩ ⟨14, by decide⟩ p hp j hj hq fz1_127_14 fz2_127_14
  · exact match_zero_fix ⟨128, by decide⟩ ⟨14, by decide⟩ p hp j hj hq fz1_128_14 fz2_128_14
  · exact match_zero_fix ⟨129, by decide⟩ ⟨14, by decide⟩ p hp j hj hq fz1_129_14 fz2_129_14
  · exact match_zero_fix ⟨130, by decide⟩ ⟨14, by decide⟩ p hp j hj hq fz1_130_14 fz2_130_14
  · exact match_zero_fix ⟨131, by decide⟩ ⟨14, by decide⟩ p hp j hj hq fz1_131_14 fz2_131_14
  · exact match_zero_fix ⟨132, by decide⟩ ⟨14, by decide⟩ p hp j hj hq fz1_132_14 fz2_132_14
  · exact match_zero_fix ⟨133, by decide⟩ ⟨14, by decide⟩ p hp j hj hq fz1_133_14 fz2_133_14
  · exact match_zero_fix ⟨134, by decide⟩ ⟨14, by decide⟩ p hp j hj hq fz1_134_14 fz2_134_14
  · exact match_zero_fix ⟨135, by decide⟩ ⟨14, by decide⟩ p hp j hj hq fz1_135_14 fz2_135_14
  · exact match_zero_fix ⟨136, by decide⟩ ⟨14, by decide⟩ p hp j hj hq fz1_136_14 fz2_136_14
  · exact match_zero_fix ⟨137, by decide⟩ ⟨14, by decide⟩ p hp j hj hq fz1_137_14 fz2_137_14
  · exact match_zero_fix ⟨138, by decide⟩ ⟨14, by decide⟩ p hp j hj hq fz1_138_14 fz2_138_14
  · exact match_zero_fix ⟨139, by decide⟩ ⟨14, by decide⟩ p hp j hj hq fz1_139_14 fz2_139_14
  · exact match_zero_fix ⟨140, by decide⟩ ⟨14, by decide⟩ p hp j hj hq fz1_140_14 fz2_140_14
  · exact pair_141_14 p hp hrep j hj hq
  · exact match_zero_fix ⟨142, by decide⟩ ⟨14, by decide⟩ p hp j hj hq fz1_142_14 fz2_142_14
  · exact match_zero_fix ⟨143, by decide⟩ ⟨14, by decide⟩ p hp j hj hq fz1_143_14 fz2_143_14
  · exact match_zero_fix ⟨144, by decide⟩ ⟨14, by decide⟩ p hp j hj hq fz1_144_14 fz2_144_14
  · exact match_zero_fix ⟨145, by decide⟩ ⟨14, by decide⟩ p hp j hj hq fz1_145_14 fz2_145_14
  · exact match_zero_fix ⟨146, by decide⟩ ⟨14, by decide⟩ p hp j hj hq fz1_146_14 fz2_146_14
  · exact pair_147_14 p hp hrep j hj hq

theorem master_15 (p : Nat) (hp : p < (Q2.transData.getD 15 []).length)
    (hrep : (Q2.cosetIsRep.getD 15 []).getD p false = true)
    (rK : Fin 148) (j : Nat) (hj : j < (repChars.getD rK.val []).length)
    (hq : (normIsRep.getD rK.val []).getD j false = true) :
    species (Q2.reps (⟨15, by decide⟩ : Fin 148)) (colE2 ⟨15, by decide⟩ p hp)
        (rowE2 rK j hj hq)
      = species (reps (⟨15, by decide⟩ : Fin 148))
        (colE1 ⟨15, by decide⟩ p (transLenTr ⟨15, by decide⟩ p hp)) (rowE1 rK j hj) := by
  rcases rK with ⟨nK, hnK⟩; interval_cases nK
  · exact match_zero_len ⟨0, by decide⟩ ⟨15, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨1, by decide⟩ ⟨15, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨2, by decide⟩ ⟨15, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨3, by decide⟩ ⟨15, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨4, by decide⟩ ⟨15, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨5, by decide⟩ ⟨15, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨6, by decide⟩ ⟨15, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨7, by decide⟩ ⟨15, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨8, by decide⟩ ⟨15, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨9, by decide⟩ ⟨15, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨10, by decide⟩ ⟨15, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨11, by decide⟩ ⟨15, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨12, by decide⟩ ⟨15, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_fix ⟨13, by decide⟩ ⟨15, by decide⟩ p hp j hj hq fz1_13_15 fz2_13_15
  · exact match_zero_fix ⟨14, by decide⟩ ⟨15, by decide⟩ p hp j hj hq fz1_14_15 fz2_14_15
  · exact pair_15_15 p hp hrep j hj hq
  · exact match_zero_fix ⟨16, by decide⟩ ⟨15, by decide⟩ p hp j hj hq fz1_16_15 fz2_16_15
  · exact match_zero_fix ⟨17, by decide⟩ ⟨15, by decide⟩ p hp j hj hq fz1_17_15 fz2_17_15
  · exact match_zero_fix ⟨18, by decide⟩ ⟨15, by decide⟩ p hp j hj hq fz1_18_15 fz2_18_15
  · exact match_zero_fix ⟨19, by decide⟩ ⟨15, by decide⟩ p hp j hj hq fz1_19_15 fz2_19_15
  · exact match_zero_fix ⟨20, by decide⟩ ⟨15, by decide⟩ p hp j hj hq fz1_20_15 fz2_20_15
  · exact match_zero_fix ⟨21, by decide⟩ ⟨15, by decide⟩ p hp j hj hq fz1_21_15 fz2_21_15
  · exact match_zero_fix ⟨22, by decide⟩ ⟨15, by decide⟩ p hp j hj hq fz1_22_15 fz2_22_15
  · exact match_zero_fix ⟨23, by decide⟩ ⟨15, by decide⟩ p hp j hj hq fz1_23_15 fz2_23_15
  · exact match_zero_fix ⟨24, by decide⟩ ⟨15, by decide⟩ p hp j hj hq fz1_24_15 fz2_24_15
  · exact match_zero_fix ⟨25, by decide⟩ ⟨15, by decide⟩ p hp j hj hq fz1_25_15 fz2_25_15
  · exact match_zero_fix ⟨26, by decide⟩ ⟨15, by decide⟩ p hp j hj hq fz1_26_15 fz2_26_15
  · exact match_zero_fix ⟨27, by decide⟩ ⟨15, by decide⟩ p hp j hj hq fz1_27_15 fz2_27_15
  · exact match_zero_fix ⟨28, by decide⟩ ⟨15, by decide⟩ p hp j hj hq fz1_28_15 fz2_28_15
  · exact match_zero_fix ⟨29, by decide⟩ ⟨15, by decide⟩ p hp j hj hq fz1_29_15 fz2_29_15
  · exact match_zero_fix ⟨30, by decide⟩ ⟨15, by decide⟩ p hp j hj hq fz1_30_15 fz2_30_15
  · exact match_zero_fix ⟨31, by decide⟩ ⟨15, by decide⟩ p hp j hj hq fz1_31_15 fz2_31_15
  · exact match_zero_fix ⟨32, by decide⟩ ⟨15, by decide⟩ p hp j hj hq fz1_32_15 fz2_32_15
  · exact match_zero_fix ⟨33, by decide⟩ ⟨15, by decide⟩ p hp j hj hq fz1_33_15 fz2_33_15
  · exact match_zero_fix ⟨34, by decide⟩ ⟨15, by decide⟩ p hp j hj hq fz1_34_15 fz2_34_15
  · exact match_zero_fix ⟨35, by decide⟩ ⟨15, by decide⟩ p hp j hj hq fz1_35_15 fz2_35_15
  · exact match_zero_fix ⟨36, by decide⟩ ⟨15, by decide⟩ p hp j hj hq fz1_36_15 fz2_36_15
  · exact match_zero_fix ⟨37, by decide⟩ ⟨15, by decide⟩ p hp j hj hq fz1_37_15 fz2_37_15
  · exact match_zero_fix ⟨38, by decide⟩ ⟨15, by decide⟩ p hp j hj hq fz1_38_15 fz2_38_15
  · exact match_zero_fix ⟨39, by decide⟩ ⟨15, by decide⟩ p hp j hj hq fz1_39_15 fz2_39_15
  · exact match_zero_fix ⟨40, by decide⟩ ⟨15, by decide⟩ p hp j hj hq fz1_40_15 fz2_40_15
  · exact match_zero_fix ⟨41, by decide⟩ ⟨15, by decide⟩ p hp j hj hq fz1_41_15 fz2_41_15
  · exact match_zero_fix ⟨42, by decide⟩ ⟨15, by decide⟩ p hp j hj hq fz1_42_15 fz2_42_15
  · exact match_zero_fix ⟨43, by decide⟩ ⟨15, by decide⟩ p hp j hj hq fz1_43_15 fz2_43_15
  · exact match_zero_fix ⟨44, by decide⟩ ⟨15, by decide⟩ p hp j hj hq fz1_44_15 fz2_44_15
  · exact match_zero_fix ⟨45, by decide⟩ ⟨15, by decide⟩ p hp j hj hq fz1_45_15 fz2_45_15
  · exact match_zero_fix ⟨46, by decide⟩ ⟨15, by decide⟩ p hp j hj hq fz1_46_15 fz2_46_15
  · exact match_zero_fix ⟨47, by decide⟩ ⟨15, by decide⟩ p hp j hj hq fz1_47_15 fz2_47_15
  · exact match_zero_fix ⟨48, by decide⟩ ⟨15, by decide⟩ p hp j hj hq fz1_48_15 fz2_48_15
  · exact match_zero_fix ⟨49, by decide⟩ ⟨15, by decide⟩ p hp j hj hq fz1_49_15 fz2_49_15
  · exact match_zero_fix ⟨50, by decide⟩ ⟨15, by decide⟩ p hp j hj hq fz1_50_15 fz2_50_15
  · exact match_zero_fix ⟨51, by decide⟩ ⟨15, by decide⟩ p hp j hj hq fz1_51_15 fz2_51_15
  · exact match_zero_fix ⟨52, by decide⟩ ⟨15, by decide⟩ p hp j hj hq fz1_52_15 fz2_52_15
  · exact match_zero_fix ⟨53, by decide⟩ ⟨15, by decide⟩ p hp j hj hq fz1_53_15 fz2_53_15
  · exact match_zero_fix ⟨54, by decide⟩ ⟨15, by decide⟩ p hp j hj hq fz1_54_15 fz2_54_15
  · exact match_zero_fix ⟨55, by decide⟩ ⟨15, by decide⟩ p hp j hj hq fz1_55_15 fz2_55_15
  · exact match_zero_fix ⟨56, by decide⟩ ⟨15, by decide⟩ p hp j hj hq fz1_56_15 fz2_56_15
  · exact match_zero_fix ⟨57, by decide⟩ ⟨15, by decide⟩ p hp j hj hq fz1_57_15 fz2_57_15
  · exact match_zero_fix ⟨58, by decide⟩ ⟨15, by decide⟩ p hp j hj hq fz1_58_15 fz2_58_15
  · exact match_zero_fix ⟨59, by decide⟩ ⟨15, by decide⟩ p hp j hj hq fz1_59_15 fz2_59_15
  · exact match_zero_fix ⟨60, by decide⟩ ⟨15, by decide⟩ p hp j hj hq fz1_60_15 fz2_60_15
  · exact match_zero_fix ⟨61, by decide⟩ ⟨15, by decide⟩ p hp j hj hq fz1_61_15 fz2_61_15
  · exact match_zero_fix ⟨62, by decide⟩ ⟨15, by decide⟩ p hp j hj hq fz1_62_15 fz2_62_15
  · exact match_zero_fix ⟨63, by decide⟩ ⟨15, by decide⟩ p hp j hj hq fz1_63_15 fz2_63_15
  · exact match_zero_fix ⟨64, by decide⟩ ⟨15, by decide⟩ p hp j hj hq fz1_64_15 fz2_64_15
  · exact match_zero_fix ⟨65, by decide⟩ ⟨15, by decide⟩ p hp j hj hq fz1_65_15 fz2_65_15
  · exact match_zero_fix ⟨66, by decide⟩ ⟨15, by decide⟩ p hp j hj hq fz1_66_15 fz2_66_15
  · exact match_zero_fix ⟨67, by decide⟩ ⟨15, by decide⟩ p hp j hj hq fz1_67_15 fz2_67_15
  · exact match_zero_fix ⟨68, by decide⟩ ⟨15, by decide⟩ p hp j hj hq fz1_68_15 fz2_68_15
  · exact match_zero_fix ⟨69, by decide⟩ ⟨15, by decide⟩ p hp j hj hq fz1_69_15 fz2_69_15
  · exact match_zero_fix ⟨70, by decide⟩ ⟨15, by decide⟩ p hp j hj hq fz1_70_15 fz2_70_15
  · exact match_zero_fix ⟨71, by decide⟩ ⟨15, by decide⟩ p hp j hj hq fz1_71_15 fz2_71_15
  · exact match_zero_fix ⟨72, by decide⟩ ⟨15, by decide⟩ p hp j hj hq fz1_72_15 fz2_72_15
  · exact match_zero_fix ⟨73, by decide⟩ ⟨15, by decide⟩ p hp j hj hq fz1_73_15 fz2_73_15
  · exact match_zero_fix ⟨74, by decide⟩ ⟨15, by decide⟩ p hp j hj hq fz1_74_15 fz2_74_15
  · exact match_zero_fix ⟨75, by decide⟩ ⟨15, by decide⟩ p hp j hj hq fz1_75_15 fz2_75_15
  · exact match_zero_fix ⟨76, by decide⟩ ⟨15, by decide⟩ p hp j hj hq fz1_76_15 fz2_76_15
  · exact match_zero_fix ⟨77, by decide⟩ ⟨15, by decide⟩ p hp j hj hq fz1_77_15 fz2_77_15
  · exact match_zero_fix ⟨78, by decide⟩ ⟨15, by decide⟩ p hp j hj hq fz1_78_15 fz2_78_15
  · exact match_zero_fix ⟨79, by decide⟩ ⟨15, by decide⟩ p hp j hj hq fz1_79_15 fz2_79_15
  · exact match_zero_fix ⟨80, by decide⟩ ⟨15, by decide⟩ p hp j hj hq fz1_80_15 fz2_80_15
  · exact match_zero_fix ⟨81, by decide⟩ ⟨15, by decide⟩ p hp j hj hq fz1_81_15 fz2_81_15
  · exact match_zero_fix ⟨82, by decide⟩ ⟨15, by decide⟩ p hp j hj hq fz1_82_15 fz2_82_15
  · exact match_zero_fix ⟨83, by decide⟩ ⟨15, by decide⟩ p hp j hj hq fz1_83_15 fz2_83_15
  · exact match_zero_fix ⟨84, by decide⟩ ⟨15, by decide⟩ p hp j hj hq fz1_84_15 fz2_84_15
  · exact pair_85_15 p hp hrep j hj hq
  · exact match_zero_fix ⟨86, by decide⟩ ⟨15, by decide⟩ p hp j hj hq fz1_86_15 fz2_86_15
  · exact match_zero_fix ⟨87, by decide⟩ ⟨15, by decide⟩ p hp j hj hq fz1_87_15 fz2_87_15
  · exact match_zero_fix ⟨88, by decide⟩ ⟨15, by decide⟩ p hp j hj hq fz1_88_15 fz2_88_15
  · exact match_zero_fix ⟨89, by decide⟩ ⟨15, by decide⟩ p hp j hj hq fz1_89_15 fz2_89_15
  · exact match_zero_fix ⟨90, by decide⟩ ⟨15, by decide⟩ p hp j hj hq fz1_90_15 fz2_90_15
  · exact match_zero_fix ⟨91, by decide⟩ ⟨15, by decide⟩ p hp j hj hq fz1_91_15 fz2_91_15
  · exact match_zero_fix ⟨92, by decide⟩ ⟨15, by decide⟩ p hp j hj hq fz1_92_15 fz2_92_15
  · exact match_zero_fix ⟨93, by decide⟩ ⟨15, by decide⟩ p hp j hj hq fz1_93_15 fz2_93_15
  · exact match_zero_fix ⟨94, by decide⟩ ⟨15, by decide⟩ p hp j hj hq fz1_94_15 fz2_94_15
  · exact match_zero_fix ⟨95, by decide⟩ ⟨15, by decide⟩ p hp j hj hq fz1_95_15 fz2_95_15
  · exact match_zero_fix ⟨96, by decide⟩ ⟨15, by decide⟩ p hp j hj hq fz1_96_15 fz2_96_15
  · exact match_zero_fix ⟨97, by decide⟩ ⟨15, by decide⟩ p hp j hj hq fz1_97_15 fz2_97_15
  · exact match_zero_fix ⟨98, by decide⟩ ⟨15, by decide⟩ p hp j hj hq fz1_98_15 fz2_98_15
  · exact match_zero_fix ⟨99, by decide⟩ ⟨15, by decide⟩ p hp j hj hq fz1_99_15 fz2_99_15
  · exact match_zero_fix ⟨100, by decide⟩ ⟨15, by decide⟩ p hp j hj hq fz1_100_15 fz2_100_15
  · exact match_zero_fix ⟨101, by decide⟩ ⟨15, by decide⟩ p hp j hj hq fz1_101_15 fz2_101_15
  · exact match_zero_fix ⟨102, by decide⟩ ⟨15, by decide⟩ p hp j hj hq fz1_102_15 fz2_102_15
  · exact match_zero_fix ⟨103, by decide⟩ ⟨15, by decide⟩ p hp j hj hq fz1_103_15 fz2_103_15
  · exact match_zero_fix ⟨104, by decide⟩ ⟨15, by decide⟩ p hp j hj hq fz1_104_15 fz2_104_15
  · exact match_zero_fix ⟨105, by decide⟩ ⟨15, by decide⟩ p hp j hj hq fz1_105_15 fz2_105_15
  · exact match_zero_fix ⟨106, by decide⟩ ⟨15, by decide⟩ p hp j hj hq fz1_106_15 fz2_106_15
  · exact match_zero_fix ⟨107, by decide⟩ ⟨15, by decide⟩ p hp j hj hq fz1_107_15 fz2_107_15
  · exact match_zero_fix ⟨108, by decide⟩ ⟨15, by decide⟩ p hp j hj hq fz1_108_15 fz2_108_15
  · exact match_zero_fix ⟨109, by decide⟩ ⟨15, by decide⟩ p hp j hj hq fz1_109_15 fz2_109_15
  · exact match_zero_fix ⟨110, by decide⟩ ⟨15, by decide⟩ p hp j hj hq fz1_110_15 fz2_110_15
  · exact match_zero_fix ⟨111, by decide⟩ ⟨15, by decide⟩ p hp j hj hq fz1_111_15 fz2_111_15
  · exact match_zero_fix ⟨112, by decide⟩ ⟨15, by decide⟩ p hp j hj hq fz1_112_15 fz2_112_15
  · exact match_zero_fix ⟨113, by decide⟩ ⟨15, by decide⟩ p hp j hj hq fz1_113_15 fz2_113_15
  · exact match_zero_fix ⟨114, by decide⟩ ⟨15, by decide⟩ p hp j hj hq fz1_114_15 fz2_114_15
  · exact match_zero_fix ⟨115, by decide⟩ ⟨15, by decide⟩ p hp j hj hq fz1_115_15 fz2_115_15
  · exact match_zero_fix ⟨116, by decide⟩ ⟨15, by decide⟩ p hp j hj hq fz1_116_15 fz2_116_15
  · exact match_zero_fix ⟨117, by decide⟩ ⟨15, by decide⟩ p hp j hj hq fz1_117_15 fz2_117_15
  · exact match_zero_fix ⟨118, by decide⟩ ⟨15, by decide⟩ p hp j hj hq fz1_118_15 fz2_118_15
  · exact match_zero_fix ⟨119, by decide⟩ ⟨15, by decide⟩ p hp j hj hq fz1_119_15 fz2_119_15
  · exact match_zero_fix ⟨120, by decide⟩ ⟨15, by decide⟩ p hp j hj hq fz1_120_15 fz2_120_15
  · exact match_zero_fix ⟨121, by decide⟩ ⟨15, by decide⟩ p hp j hj hq fz1_121_15 fz2_121_15
  · exact match_zero_fix ⟨122, by decide⟩ ⟨15, by decide⟩ p hp j hj hq fz1_122_15 fz2_122_15
  · exact match_zero_fix ⟨123, by decide⟩ ⟨15, by decide⟩ p hp j hj hq fz1_123_15 fz2_123_15
  · exact match_zero_fix ⟨124, by decide⟩ ⟨15, by decide⟩ p hp j hj hq fz1_124_15 fz2_124_15
  · exact match_zero_fix ⟨125, by decide⟩ ⟨15, by decide⟩ p hp j hj hq fz1_125_15 fz2_125_15
  · exact match_zero_fix ⟨126, by decide⟩ ⟨15, by decide⟩ p hp j hj hq fz1_126_15 fz2_126_15
  · exact match_zero_fix ⟨127, by decide⟩ ⟨15, by decide⟩ p hp j hj hq fz1_127_15 fz2_127_15
  · exact match_zero_fix ⟨128, by decide⟩ ⟨15, by decide⟩ p hp j hj hq fz1_128_15 fz2_128_15
  · exact match_zero_fix ⟨129, by decide⟩ ⟨15, by decide⟩ p hp j hj hq fz1_129_15 fz2_129_15
  · exact match_zero_fix ⟨130, by decide⟩ ⟨15, by decide⟩ p hp j hj hq fz1_130_15 fz2_130_15
  · exact match_zero_fix ⟨131, by decide⟩ ⟨15, by decide⟩ p hp j hj hq fz1_131_15 fz2_131_15
  · exact match_zero_fix ⟨132, by decide⟩ ⟨15, by decide⟩ p hp j hj hq fz1_132_15 fz2_132_15
  · exact match_zero_fix ⟨133, by decide⟩ ⟨15, by decide⟩ p hp j hj hq fz1_133_15 fz2_133_15
  · exact match_zero_fix ⟨134, by decide⟩ ⟨15, by decide⟩ p hp j hj hq fz1_134_15 fz2_134_15
  · exact match_zero_fix ⟨135, by decide⟩ ⟨15, by decide⟩ p hp j hj hq fz1_135_15 fz2_135_15
  · exact match_zero_fix ⟨136, by decide⟩ ⟨15, by decide⟩ p hp j hj hq fz1_136_15 fz2_136_15
  · exact match_zero_fix ⟨137, by decide⟩ ⟨15, by decide⟩ p hp j hj hq fz1_137_15 fz2_137_15
  · exact match_zero_fix ⟨138, by decide⟩ ⟨15, by decide⟩ p hp j hj hq fz1_138_15 fz2_138_15
  · exact match_zero_fix ⟨139, by decide⟩ ⟨15, by decide⟩ p hp j hj hq fz1_139_15 fz2_139_15
  · exact match_zero_fix ⟨140, by decide⟩ ⟨15, by decide⟩ p hp j hj hq fz1_140_15 fz2_140_15
  · exact pair_141_15 p hp hrep j hj hq
  · exact match_zero_fix ⟨142, by decide⟩ ⟨15, by decide⟩ p hp j hj hq fz1_142_15 fz2_142_15
  · exact match_zero_fix ⟨143, by decide⟩ ⟨15, by decide⟩ p hp j hj hq fz1_143_15 fz2_143_15
  · exact match_zero_fix ⟨144, by decide⟩ ⟨15, by decide⟩ p hp j hj hq fz1_144_15 fz2_144_15
  · exact match_zero_fix ⟨145, by decide⟩ ⟨15, by decide⟩ p hp j hj hq fz1_145_15 fz2_145_15
  · exact match_zero_fix ⟨146, by decide⟩ ⟨15, by decide⟩ p hp j hj hq fz1_146_15 fz2_146_15
  · exact pair_147_15 p hp hrep j hj hq

end LeanDring.P5Presentation
