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

/-! # Stage-5 per-column-class master theorems, chunk 6 (auto-emitted).  -/

namespace LeanDring.P5Presentation

open MulAction Finset LeanDring.DRing LeanDring.MonGSet

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.style.longLine false

theorem master_48 (p : Nat) (hp : p < (Q2.transData.getD 48 []).length)
    (hrep : (Q2.cosetIsRep.getD 48 []).getD p false = true)
    (rK : Fin 148) (j : Nat) (hj : j < (repChars.getD rK.val []).length)
    (hq : (normIsRep.getD rK.val []).getD j false = true) :
    species (Q2.reps (⟨48, by decide⟩ : Fin 148)) (colE2 ⟨48, by decide⟩ p hp)
        (rowE2 rK j hj hq)
      = species (reps (⟨48, by decide⟩ : Fin 148))
        (colE1 ⟨48, by decide⟩ p (transLenTr ⟨48, by decide⟩ p hp)) (rowE1 rK j hj) := by
  rcases rK with ⟨nK, hnK⟩; interval_cases nK
  · exact match_zero_len ⟨0, by decide⟩ ⟨48, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨1, by decide⟩ ⟨48, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨2, by decide⟩ ⟨48, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨3, by decide⟩ ⟨48, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨4, by decide⟩ ⟨48, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨5, by decide⟩ ⟨48, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨6, by decide⟩ ⟨48, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨7, by decide⟩ ⟨48, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨8, by decide⟩ ⟨48, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨9, by decide⟩ ⟨48, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨10, by decide⟩ ⟨48, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨11, by decide⟩ ⟨48, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨12, by decide⟩ ⟨48, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_fix ⟨13, by decide⟩ ⟨48, by decide⟩ p hp j hj hq fz1_13_48 fz2_13_48
  · exact match_zero_fix ⟨14, by decide⟩ ⟨48, by decide⟩ p hp j hj hq fz1_14_48 fz2_14_48
  · exact match_zero_fix ⟨15, by decide⟩ ⟨48, by decide⟩ p hp j hj hq fz1_15_48 fz2_15_48
  · exact match_zero_fix ⟨16, by decide⟩ ⟨48, by decide⟩ p hp j hj hq fz1_16_48 fz2_16_48
  · exact match_zero_fix ⟨17, by decide⟩ ⟨48, by decide⟩ p hp j hj hq fz1_17_48 fz2_17_48
  · exact match_zero_fix ⟨18, by decide⟩ ⟨48, by decide⟩ p hp j hj hq fz1_18_48 fz2_18_48
  · exact match_zero_fix ⟨19, by decide⟩ ⟨48, by decide⟩ p hp j hj hq fz1_19_48 fz2_19_48
  · exact match_zero_fix ⟨20, by decide⟩ ⟨48, by decide⟩ p hp j hj hq fz1_20_48 fz2_20_48
  · exact match_zero_fix ⟨21, by decide⟩ ⟨48, by decide⟩ p hp j hj hq fz1_21_48 fz2_21_48
  · exact match_zero_fix ⟨22, by decide⟩ ⟨48, by decide⟩ p hp j hj hq fz1_22_48 fz2_22_48
  · exact match_zero_fix ⟨23, by decide⟩ ⟨48, by decide⟩ p hp j hj hq fz1_23_48 fz2_23_48
  · exact match_zero_fix ⟨24, by decide⟩ ⟨48, by decide⟩ p hp j hj hq fz1_24_48 fz2_24_48
  · exact match_zero_fix ⟨25, by decide⟩ ⟨48, by decide⟩ p hp j hj hq fz1_25_48 fz2_25_48
  · exact match_zero_fix ⟨26, by decide⟩ ⟨48, by decide⟩ p hp j hj hq fz1_26_48 fz2_26_48
  · exact match_zero_fix ⟨27, by decide⟩ ⟨48, by decide⟩ p hp j hj hq fz1_27_48 fz2_27_48
  · exact match_zero_fix ⟨28, by decide⟩ ⟨48, by decide⟩ p hp j hj hq fz1_28_48 fz2_28_48
  · exact match_zero_fix ⟨29, by decide⟩ ⟨48, by decide⟩ p hp j hj hq fz1_29_48 fz2_29_48
  · exact match_zero_fix ⟨30, by decide⟩ ⟨48, by decide⟩ p hp j hj hq fz1_30_48 fz2_30_48
  · exact match_zero_fix ⟨31, by decide⟩ ⟨48, by decide⟩ p hp j hj hq fz1_31_48 fz2_31_48
  · exact match_zero_fix ⟨32, by decide⟩ ⟨48, by decide⟩ p hp j hj hq fz1_32_48 fz2_32_48
  · exact match_zero_fix ⟨33, by decide⟩ ⟨48, by decide⟩ p hp j hj hq fz1_33_48 fz2_33_48
  · exact match_zero_fix ⟨34, by decide⟩ ⟨48, by decide⟩ p hp j hj hq fz1_34_48 fz2_34_48
  · exact match_zero_fix ⟨35, by decide⟩ ⟨48, by decide⟩ p hp j hj hq fz1_35_48 fz2_35_48
  · exact match_zero_fix ⟨36, by decide⟩ ⟨48, by decide⟩ p hp j hj hq fz1_36_48 fz2_36_48
  · exact match_zero_fix ⟨37, by decide⟩ ⟨48, by decide⟩ p hp j hj hq fz1_37_48 fz2_37_48
  · exact match_zero_fix ⟨38, by decide⟩ ⟨48, by decide⟩ p hp j hj hq fz1_38_48 fz2_38_48
  · exact match_zero_fix ⟨39, by decide⟩ ⟨48, by decide⟩ p hp j hj hq fz1_39_48 fz2_39_48
  · exact match_zero_fix ⟨40, by decide⟩ ⟨48, by decide⟩ p hp j hj hq fz1_40_48 fz2_40_48
  · exact match_zero_fix ⟨41, by decide⟩ ⟨48, by decide⟩ p hp j hj hq fz1_41_48 fz2_41_48
  · exact match_zero_fix ⟨42, by decide⟩ ⟨48, by decide⟩ p hp j hj hq fz1_42_48 fz2_42_48
  · exact match_zero_fix ⟨43, by decide⟩ ⟨48, by decide⟩ p hp j hj hq fz1_43_48 fz2_43_48
  · exact match_zero_fix ⟨44, by decide⟩ ⟨48, by decide⟩ p hp j hj hq fz1_44_48 fz2_44_48
  · exact match_zero_fix ⟨45, by decide⟩ ⟨48, by decide⟩ p hp j hj hq fz1_45_48 fz2_45_48
  · exact match_zero_fix ⟨46, by decide⟩ ⟨48, by decide⟩ p hp j hj hq fz1_46_48 fz2_46_48
  · exact match_zero_fix ⟨47, by decide⟩ ⟨48, by decide⟩ p hp j hj hq fz1_47_48 fz2_47_48
  · exact pair_48_48 p hp hrep j hj hq
  · exact match_zero_fix ⟨49, by decide⟩ ⟨48, by decide⟩ p hp j hj hq fz1_49_48 fz2_49_48
  · exact match_zero_fix ⟨50, by decide⟩ ⟨48, by decide⟩ p hp j hj hq fz1_50_48 fz2_50_48
  · exact match_zero_fix ⟨51, by decide⟩ ⟨48, by decide⟩ p hp j hj hq fz1_51_48 fz2_51_48
  · exact match_zero_fix ⟨52, by decide⟩ ⟨48, by decide⟩ p hp j hj hq fz1_52_48 fz2_52_48
  · exact match_zero_fix ⟨53, by decide⟩ ⟨48, by decide⟩ p hp j hj hq fz1_53_48 fz2_53_48
  · exact match_zero_fix ⟨54, by decide⟩ ⟨48, by decide⟩ p hp j hj hq fz1_54_48 fz2_54_48
  · exact pair_55_48 p hp hrep j hj hq
  · exact pair_56_48 p hp hrep j hj hq
  · exact pair_57_48 p hp hrep j hj hq
  · exact pair_58_48 p hp hrep j hj hq
  · exact pair_59_48 p hp hrep j hj hq
  · exact match_zero_fix ⟨60, by decide⟩ ⟨48, by decide⟩ p hp j hj hq fz1_60_48 fz2_60_48
  · exact match_zero_fix ⟨61, by decide⟩ ⟨48, by decide⟩ p hp j hj hq fz1_61_48 fz2_61_48
  · exact match_zero_fix ⟨62, by decide⟩ ⟨48, by decide⟩ p hp j hj hq fz1_62_48 fz2_62_48
  · exact match_zero_fix ⟨63, by decide⟩ ⟨48, by decide⟩ p hp j hj hq fz1_63_48 fz2_63_48
  · exact match_zero_fix ⟨64, by decide⟩ ⟨48, by decide⟩ p hp j hj hq fz1_64_48 fz2_64_48
  · exact match_zero_fix ⟨65, by decide⟩ ⟨48, by decide⟩ p hp j hj hq fz1_65_48 fz2_65_48
  · exact match_zero_fix ⟨66, by decide⟩ ⟨48, by decide⟩ p hp j hj hq fz1_66_48 fz2_66_48
  · exact match_zero_fix ⟨67, by decide⟩ ⟨48, by decide⟩ p hp j hj hq fz1_67_48 fz2_67_48
  · exact match_zero_fix ⟨68, by decide⟩ ⟨48, by decide⟩ p hp j hj hq fz1_68_48 fz2_68_48
  · exact match_zero_fix ⟨69, by decide⟩ ⟨48, by decide⟩ p hp j hj hq fz1_69_48 fz2_69_48
  · exact match_zero_fix ⟨70, by decide⟩ ⟨48, by decide⟩ p hp j hj hq fz1_70_48 fz2_70_48
  · exact match_zero_fix ⟨71, by decide⟩ ⟨48, by decide⟩ p hp j hj hq fz1_71_48 fz2_71_48
  · exact match_zero_fix ⟨72, by decide⟩ ⟨48, by decide⟩ p hp j hj hq fz1_72_48 fz2_72_48
  · exact match_zero_fix ⟨73, by decide⟩ ⟨48, by decide⟩ p hp j hj hq fz1_73_48 fz2_73_48
  · exact match_zero_fix ⟨74, by decide⟩ ⟨48, by decide⟩ p hp j hj hq fz1_74_48 fz2_74_48
  · exact match_zero_fix ⟨75, by decide⟩ ⟨48, by decide⟩ p hp j hj hq fz1_75_48 fz2_75_48
  · exact match_zero_fix ⟨76, by decide⟩ ⟨48, by decide⟩ p hp j hj hq fz1_76_48 fz2_76_48
  · exact match_zero_fix ⟨77, by decide⟩ ⟨48, by decide⟩ p hp j hj hq fz1_77_48 fz2_77_48
  · exact match_zero_fix ⟨78, by decide⟩ ⟨48, by decide⟩ p hp j hj hq fz1_78_48 fz2_78_48
  · exact match_zero_fix ⟨79, by decide⟩ ⟨48, by decide⟩ p hp j hj hq fz1_79_48 fz2_79_48
  · exact match_zero_fix ⟨80, by decide⟩ ⟨48, by decide⟩ p hp j hj hq fz1_80_48 fz2_80_48
  · exact match_zero_fix ⟨81, by decide⟩ ⟨48, by decide⟩ p hp j hj hq fz1_81_48 fz2_81_48
  · exact match_zero_fix ⟨82, by decide⟩ ⟨48, by decide⟩ p hp j hj hq fz1_82_48 fz2_82_48
  · exact match_zero_fix ⟨83, by decide⟩ ⟨48, by decide⟩ p hp j hj hq fz1_83_48 fz2_83_48
  · exact match_zero_fix ⟨84, by decide⟩ ⟨48, by decide⟩ p hp j hj hq fz1_84_48 fz2_84_48
  · exact match_zero_fix ⟨85, by decide⟩ ⟨48, by decide⟩ p hp j hj hq fz1_85_48 fz2_85_48
  · exact match_zero_fix ⟨86, by decide⟩ ⟨48, by decide⟩ p hp j hj hq fz1_86_48 fz2_86_48
  · exact match_zero_fix ⟨87, by decide⟩ ⟨48, by decide⟩ p hp j hj hq fz1_87_48 fz2_87_48
  · exact match_zero_fix ⟨88, by decide⟩ ⟨48, by decide⟩ p hp j hj hq fz1_88_48 fz2_88_48
  · exact match_zero_fix ⟨89, by decide⟩ ⟨48, by decide⟩ p hp j hj hq fz1_89_48 fz2_89_48
  · exact match_zero_fix ⟨90, by decide⟩ ⟨48, by decide⟩ p hp j hj hq fz1_90_48 fz2_90_48
  · exact match_zero_fix ⟨91, by decide⟩ ⟨48, by decide⟩ p hp j hj hq fz1_91_48 fz2_91_48
  · exact match_zero_fix ⟨92, by decide⟩ ⟨48, by decide⟩ p hp j hj hq fz1_92_48 fz2_92_48
  · exact match_zero_fix ⟨93, by decide⟩ ⟨48, by decide⟩ p hp j hj hq fz1_93_48 fz2_93_48
  · exact match_zero_fix ⟨94, by decide⟩ ⟨48, by decide⟩ p hp j hj hq fz1_94_48 fz2_94_48
  · exact match_zero_fix ⟨95, by decide⟩ ⟨48, by decide⟩ p hp j hj hq fz1_95_48 fz2_95_48
  · exact match_zero_fix ⟨96, by decide⟩ ⟨48, by decide⟩ p hp j hj hq fz1_96_48 fz2_96_48
  · exact match_zero_fix ⟨97, by decide⟩ ⟨48, by decide⟩ p hp j hj hq fz1_97_48 fz2_97_48
  · exact match_zero_fix ⟨98, by decide⟩ ⟨48, by decide⟩ p hp j hj hq fz1_98_48 fz2_98_48
  · exact match_zero_fix ⟨99, by decide⟩ ⟨48, by decide⟩ p hp j hj hq fz1_99_48 fz2_99_48
  · exact match_zero_fix ⟨100, by decide⟩ ⟨48, by decide⟩ p hp j hj hq fz1_100_48 fz2_100_48
  · exact match_zero_fix ⟨101, by decide⟩ ⟨48, by decide⟩ p hp j hj hq fz1_101_48 fz2_101_48
  · exact match_zero_fix ⟨102, by decide⟩ ⟨48, by decide⟩ p hp j hj hq fz1_102_48 fz2_102_48
  · exact match_zero_fix ⟨103, by decide⟩ ⟨48, by decide⟩ p hp j hj hq fz1_103_48 fz2_103_48
  · exact match_zero_fix ⟨104, by decide⟩ ⟨48, by decide⟩ p hp j hj hq fz1_104_48 fz2_104_48
  · exact match_zero_fix ⟨105, by decide⟩ ⟨48, by decide⟩ p hp j hj hq fz1_105_48 fz2_105_48
  · exact match_zero_fix ⟨106, by decide⟩ ⟨48, by decide⟩ p hp j hj hq fz1_106_48 fz2_106_48
  · exact match_zero_fix ⟨107, by decide⟩ ⟨48, by decide⟩ p hp j hj hq fz1_107_48 fz2_107_48
  · exact match_zero_fix ⟨108, by decide⟩ ⟨48, by decide⟩ p hp j hj hq fz1_108_48 fz2_108_48
  · exact match_zero_fix ⟨109, by decide⟩ ⟨48, by decide⟩ p hp j hj hq fz1_109_48 fz2_109_48
  · exact pair_110_48 p hp hrep j hj hq
  · exact match_zero_fix ⟨111, by decide⟩ ⟨48, by decide⟩ p hp j hj hq fz1_111_48 fz2_111_48
  · exact match_zero_fix ⟨112, by decide⟩ ⟨48, by decide⟩ p hp j hj hq fz1_112_48 fz2_112_48
  · exact match_zero_fix ⟨113, by decide⟩ ⟨48, by decide⟩ p hp j hj hq fz1_113_48 fz2_113_48
  · exact match_zero_fix ⟨114, by decide⟩ ⟨48, by decide⟩ p hp j hj hq fz1_114_48 fz2_114_48
  · exact match_zero_fix ⟨115, by decide⟩ ⟨48, by decide⟩ p hp j hj hq fz1_115_48 fz2_115_48
  · exact pair_116_48 p hp hrep j hj hq
  · exact match_zero_fix ⟨117, by decide⟩ ⟨48, by decide⟩ p hp j hj hq fz1_117_48 fz2_117_48
  · exact match_zero_fix ⟨118, by decide⟩ ⟨48, by decide⟩ p hp j hj hq fz1_118_48 fz2_118_48
  · exact match_zero_fix ⟨119, by decide⟩ ⟨48, by decide⟩ p hp j hj hq fz1_119_48 fz2_119_48
  · exact match_zero_fix ⟨120, by decide⟩ ⟨48, by decide⟩ p hp j hj hq fz1_120_48 fz2_120_48
  · exact pair_121_48 p hp hrep j hj hq
  · exact match_zero_fix ⟨122, by decide⟩ ⟨48, by decide⟩ p hp j hj hq fz1_122_48 fz2_122_48
  · exact match_zero_fix ⟨123, by decide⟩ ⟨48, by decide⟩ p hp j hj hq fz1_123_48 fz2_123_48
  · exact match_zero_fix ⟨124, by decide⟩ ⟨48, by decide⟩ p hp j hj hq fz1_124_48 fz2_124_48
  · exact match_zero_fix ⟨125, by decide⟩ ⟨48, by decide⟩ p hp j hj hq fz1_125_48 fz2_125_48
  · exact pair_126_48 p hp hrep j hj hq
  · exact match_zero_fix ⟨127, by decide⟩ ⟨48, by decide⟩ p hp j hj hq fz1_127_48 fz2_127_48
  · exact match_zero_fix ⟨128, by decide⟩ ⟨48, by decide⟩ p hp j hj hq fz1_128_48 fz2_128_48
  · exact match_zero_fix ⟨129, by decide⟩ ⟨48, by decide⟩ p hp j hj hq fz1_129_48 fz2_129_48
  · exact match_zero_fix ⟨130, by decide⟩ ⟨48, by decide⟩ p hp j hj hq fz1_130_48 fz2_130_48
  · exact pair_131_48 p hp hrep j hj hq
  · exact match_zero_fix ⟨132, by decide⟩ ⟨48, by decide⟩ p hp j hj hq fz1_132_48 fz2_132_48
  · exact match_zero_fix ⟨133, by decide⟩ ⟨48, by decide⟩ p hp j hj hq fz1_133_48 fz2_133_48
  · exact match_zero_fix ⟨134, by decide⟩ ⟨48, by decide⟩ p hp j hj hq fz1_134_48 fz2_134_48
  · exact match_zero_fix ⟨135, by decide⟩ ⟨48, by decide⟩ p hp j hj hq fz1_135_48 fz2_135_48
  · exact pair_136_48 p hp hrep j hj hq
  · exact match_zero_fix ⟨137, by decide⟩ ⟨48, by decide⟩ p hp j hj hq fz1_137_48 fz2_137_48
  · exact match_zero_fix ⟨138, by decide⟩ ⟨48, by decide⟩ p hp j hj hq fz1_138_48 fz2_138_48
  · exact match_zero_fix ⟨139, by decide⟩ ⟨48, by decide⟩ p hp j hj hq fz1_139_48 fz2_139_48
  · exact match_zero_fix ⟨140, by decide⟩ ⟨48, by decide⟩ p hp j hj hq fz1_140_48 fz2_140_48
  · exact match_zero_fix ⟨141, by decide⟩ ⟨48, by decide⟩ p hp j hj hq fz1_141_48 fz2_141_48
  · exact match_zero_fix ⟨142, by decide⟩ ⟨48, by decide⟩ p hp j hj hq fz1_142_48 fz2_142_48
  · exact match_zero_fix ⟨143, by decide⟩ ⟨48, by decide⟩ p hp j hj hq fz1_143_48 fz2_143_48
  · exact match_zero_fix ⟨144, by decide⟩ ⟨48, by decide⟩ p hp j hj hq fz1_144_48 fz2_144_48
  · exact match_zero_fix ⟨145, by decide⟩ ⟨48, by decide⟩ p hp j hj hq fz1_145_48 fz2_145_48
  · exact pair_146_48 p hp hrep j hj hq
  · exact pair_147_48 p hp hrep j hj hq

theorem master_49 (p : Nat) (hp : p < (Q2.transData.getD 49 []).length)
    (hrep : (Q2.cosetIsRep.getD 49 []).getD p false = true)
    (rK : Fin 148) (j : Nat) (hj : j < (repChars.getD rK.val []).length)
    (hq : (normIsRep.getD rK.val []).getD j false = true) :
    species (Q2.reps (⟨49, by decide⟩ : Fin 148)) (colE2 ⟨49, by decide⟩ p hp)
        (rowE2 rK j hj hq)
      = species (reps (⟨49, by decide⟩ : Fin 148))
        (colE1 ⟨49, by decide⟩ p (transLenTr ⟨49, by decide⟩ p hp)) (rowE1 rK j hj) := by
  rcases rK with ⟨nK, hnK⟩; interval_cases nK
  · exact match_zero_len ⟨0, by decide⟩ ⟨49, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨1, by decide⟩ ⟨49, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨2, by decide⟩ ⟨49, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨3, by decide⟩ ⟨49, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨4, by decide⟩ ⟨49, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨5, by decide⟩ ⟨49, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨6, by decide⟩ ⟨49, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨7, by decide⟩ ⟨49, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨8, by decide⟩ ⟨49, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨9, by decide⟩ ⟨49, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨10, by decide⟩ ⟨49, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨11, by decide⟩ ⟨49, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨12, by decide⟩ ⟨49, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_fix ⟨13, by decide⟩ ⟨49, by decide⟩ p hp j hj hq fz1_13_49 fz2_13_49
  · exact match_zero_fix ⟨14, by decide⟩ ⟨49, by decide⟩ p hp j hj hq fz1_14_49 fz2_14_49
  · exact match_zero_fix ⟨15, by decide⟩ ⟨49, by decide⟩ p hp j hj hq fz1_15_49 fz2_15_49
  · exact match_zero_fix ⟨16, by decide⟩ ⟨49, by decide⟩ p hp j hj hq fz1_16_49 fz2_16_49
  · exact match_zero_fix ⟨17, by decide⟩ ⟨49, by decide⟩ p hp j hj hq fz1_17_49 fz2_17_49
  · exact match_zero_fix ⟨18, by decide⟩ ⟨49, by decide⟩ p hp j hj hq fz1_18_49 fz2_18_49
  · exact match_zero_fix ⟨19, by decide⟩ ⟨49, by decide⟩ p hp j hj hq fz1_19_49 fz2_19_49
  · exact match_zero_fix ⟨20, by decide⟩ ⟨49, by decide⟩ p hp j hj hq fz1_20_49 fz2_20_49
  · exact match_zero_fix ⟨21, by decide⟩ ⟨49, by decide⟩ p hp j hj hq fz1_21_49 fz2_21_49
  · exact match_zero_fix ⟨22, by decide⟩ ⟨49, by decide⟩ p hp j hj hq fz1_22_49 fz2_22_49
  · exact match_zero_fix ⟨23, by decide⟩ ⟨49, by decide⟩ p hp j hj hq fz1_23_49 fz2_23_49
  · exact match_zero_fix ⟨24, by decide⟩ ⟨49, by decide⟩ p hp j hj hq fz1_24_49 fz2_24_49
  · exact match_zero_fix ⟨25, by decide⟩ ⟨49, by decide⟩ p hp j hj hq fz1_25_49 fz2_25_49
  · exact match_zero_fix ⟨26, by decide⟩ ⟨49, by decide⟩ p hp j hj hq fz1_26_49 fz2_26_49
  · exact match_zero_fix ⟨27, by decide⟩ ⟨49, by decide⟩ p hp j hj hq fz1_27_49 fz2_27_49
  · exact match_zero_fix ⟨28, by decide⟩ ⟨49, by decide⟩ p hp j hj hq fz1_28_49 fz2_28_49
  · exact match_zero_fix ⟨29, by decide⟩ ⟨49, by decide⟩ p hp j hj hq fz1_29_49 fz2_29_49
  · exact match_zero_fix ⟨30, by decide⟩ ⟨49, by decide⟩ p hp j hj hq fz1_30_49 fz2_30_49
  · exact match_zero_fix ⟨31, by decide⟩ ⟨49, by decide⟩ p hp j hj hq fz1_31_49 fz2_31_49
  · exact match_zero_fix ⟨32, by decide⟩ ⟨49, by decide⟩ p hp j hj hq fz1_32_49 fz2_32_49
  · exact match_zero_fix ⟨33, by decide⟩ ⟨49, by decide⟩ p hp j hj hq fz1_33_49 fz2_33_49
  · exact match_zero_fix ⟨34, by decide⟩ ⟨49, by decide⟩ p hp j hj hq fz1_34_49 fz2_34_49
  · exact match_zero_fix ⟨35, by decide⟩ ⟨49, by decide⟩ p hp j hj hq fz1_35_49 fz2_35_49
  · exact match_zero_fix ⟨36, by decide⟩ ⟨49, by decide⟩ p hp j hj hq fz1_36_49 fz2_36_49
  · exact match_zero_fix ⟨37, by decide⟩ ⟨49, by decide⟩ p hp j hj hq fz1_37_49 fz2_37_49
  · exact match_zero_fix ⟨38, by decide⟩ ⟨49, by decide⟩ p hp j hj hq fz1_38_49 fz2_38_49
  · exact match_zero_fix ⟨39, by decide⟩ ⟨49, by decide⟩ p hp j hj hq fz1_39_49 fz2_39_49
  · exact match_zero_fix ⟨40, by decide⟩ ⟨49, by decide⟩ p hp j hj hq fz1_40_49 fz2_40_49
  · exact match_zero_fix ⟨41, by decide⟩ ⟨49, by decide⟩ p hp j hj hq fz1_41_49 fz2_41_49
  · exact match_zero_fix ⟨42, by decide⟩ ⟨49, by decide⟩ p hp j hj hq fz1_42_49 fz2_42_49
  · exact match_zero_fix ⟨43, by decide⟩ ⟨49, by decide⟩ p hp j hj hq fz1_43_49 fz2_43_49
  · exact match_zero_fix ⟨44, by decide⟩ ⟨49, by decide⟩ p hp j hj hq fz1_44_49 fz2_44_49
  · exact match_zero_fix ⟨45, by decide⟩ ⟨49, by decide⟩ p hp j hj hq fz1_45_49 fz2_45_49
  · exact match_zero_fix ⟨46, by decide⟩ ⟨49, by decide⟩ p hp j hj hq fz1_46_49 fz2_46_49
  · exact match_zero_fix ⟨47, by decide⟩ ⟨49, by decide⟩ p hp j hj hq fz1_47_49 fz2_47_49
  · exact match_zero_fix ⟨48, by decide⟩ ⟨49, by decide⟩ p hp j hj hq fz1_48_49 fz2_48_49
  · exact pair_49_49 p hp hrep j hj hq
  · exact match_zero_fix ⟨50, by decide⟩ ⟨49, by decide⟩ p hp j hj hq fz1_50_49 fz2_50_49
  · exact match_zero_fix ⟨51, by decide⟩ ⟨49, by decide⟩ p hp j hj hq fz1_51_49 fz2_51_49
  · exact match_zero_fix ⟨52, by decide⟩ ⟨49, by decide⟩ p hp j hj hq fz1_52_49 fz2_52_49
  · exact match_zero_fix ⟨53, by decide⟩ ⟨49, by decide⟩ p hp j hj hq fz1_53_49 fz2_53_49
  · exact match_zero_fix ⟨54, by decide⟩ ⟨49, by decide⟩ p hp j hj hq fz1_54_49 fz2_54_49
  · exact match_zero_fix ⟨55, by decide⟩ ⟨49, by decide⟩ p hp j hj hq fz1_55_49 fz2_55_49
  · exact match_zero_fix ⟨56, by decide⟩ ⟨49, by decide⟩ p hp j hj hq fz1_56_49 fz2_56_49
  · exact match_zero_fix ⟨57, by decide⟩ ⟨49, by decide⟩ p hp j hj hq fz1_57_49 fz2_57_49
  · exact match_zero_fix ⟨58, by decide⟩ ⟨49, by decide⟩ p hp j hj hq fz1_58_49 fz2_58_49
  · exact match_zero_fix ⟨59, by decide⟩ ⟨49, by decide⟩ p hp j hj hq fz1_59_49 fz2_59_49
  · exact pair_60_49 p hp hrep j hj hq
  · exact pair_61_49 p hp hrep j hj hq
  · exact pair_62_49 p hp hrep j hj hq
  · exact pair_63_49 p hp hrep j hj hq
  · exact pair_64_49 p hp hrep j hj hq
  · exact match_zero_fix ⟨65, by decide⟩ ⟨49, by decide⟩ p hp j hj hq fz1_65_49 fz2_65_49
  · exact match_zero_fix ⟨66, by decide⟩ ⟨49, by decide⟩ p hp j hj hq fz1_66_49 fz2_66_49
  · exact match_zero_fix ⟨67, by decide⟩ ⟨49, by decide⟩ p hp j hj hq fz1_67_49 fz2_67_49
  · exact match_zero_fix ⟨68, by decide⟩ ⟨49, by decide⟩ p hp j hj hq fz1_68_49 fz2_68_49
  · exact match_zero_fix ⟨69, by decide⟩ ⟨49, by decide⟩ p hp j hj hq fz1_69_49 fz2_69_49
  · exact match_zero_fix ⟨70, by decide⟩ ⟨49, by decide⟩ p hp j hj hq fz1_70_49 fz2_70_49
  · exact match_zero_fix ⟨71, by decide⟩ ⟨49, by decide⟩ p hp j hj hq fz1_71_49 fz2_71_49
  · exact match_zero_fix ⟨72, by decide⟩ ⟨49, by decide⟩ p hp j hj hq fz1_72_49 fz2_72_49
  · exact match_zero_fix ⟨73, by decide⟩ ⟨49, by decide⟩ p hp j hj hq fz1_73_49 fz2_73_49
  · exact match_zero_fix ⟨74, by decide⟩ ⟨49, by decide⟩ p hp j hj hq fz1_74_49 fz2_74_49
  · exact match_zero_fix ⟨75, by decide⟩ ⟨49, by decide⟩ p hp j hj hq fz1_75_49 fz2_75_49
  · exact match_zero_fix ⟨76, by decide⟩ ⟨49, by decide⟩ p hp j hj hq fz1_76_49 fz2_76_49
  · exact match_zero_fix ⟨77, by decide⟩ ⟨49, by decide⟩ p hp j hj hq fz1_77_49 fz2_77_49
  · exact match_zero_fix ⟨78, by decide⟩ ⟨49, by decide⟩ p hp j hj hq fz1_78_49 fz2_78_49
  · exact match_zero_fix ⟨79, by decide⟩ ⟨49, by decide⟩ p hp j hj hq fz1_79_49 fz2_79_49
  · exact match_zero_fix ⟨80, by decide⟩ ⟨49, by decide⟩ p hp j hj hq fz1_80_49 fz2_80_49
  · exact match_zero_fix ⟨81, by decide⟩ ⟨49, by decide⟩ p hp j hj hq fz1_81_49 fz2_81_49
  · exact match_zero_fix ⟨82, by decide⟩ ⟨49, by decide⟩ p hp j hj hq fz1_82_49 fz2_82_49
  · exact match_zero_fix ⟨83, by decide⟩ ⟨49, by decide⟩ p hp j hj hq fz1_83_49 fz2_83_49
  · exact match_zero_fix ⟨84, by decide⟩ ⟨49, by decide⟩ p hp j hj hq fz1_84_49 fz2_84_49
  · exact match_zero_fix ⟨85, by decide⟩ ⟨49, by decide⟩ p hp j hj hq fz1_85_49 fz2_85_49
  · exact match_zero_fix ⟨86, by decide⟩ ⟨49, by decide⟩ p hp j hj hq fz1_86_49 fz2_86_49
  · exact match_zero_fix ⟨87, by decide⟩ ⟨49, by decide⟩ p hp j hj hq fz1_87_49 fz2_87_49
  · exact match_zero_fix ⟨88, by decide⟩ ⟨49, by decide⟩ p hp j hj hq fz1_88_49 fz2_88_49
  · exact match_zero_fix ⟨89, by decide⟩ ⟨49, by decide⟩ p hp j hj hq fz1_89_49 fz2_89_49
  · exact match_zero_fix ⟨90, by decide⟩ ⟨49, by decide⟩ p hp j hj hq fz1_90_49 fz2_90_49
  · exact match_zero_fix ⟨91, by decide⟩ ⟨49, by decide⟩ p hp j hj hq fz1_91_49 fz2_91_49
  · exact match_zero_fix ⟨92, by decide⟩ ⟨49, by decide⟩ p hp j hj hq fz1_92_49 fz2_92_49
  · exact match_zero_fix ⟨93, by decide⟩ ⟨49, by decide⟩ p hp j hj hq fz1_93_49 fz2_93_49
  · exact match_zero_fix ⟨94, by decide⟩ ⟨49, by decide⟩ p hp j hj hq fz1_94_49 fz2_94_49
  · exact match_zero_fix ⟨95, by decide⟩ ⟨49, by decide⟩ p hp j hj hq fz1_95_49 fz2_95_49
  · exact match_zero_fix ⟨96, by decide⟩ ⟨49, by decide⟩ p hp j hj hq fz1_96_49 fz2_96_49
  · exact match_zero_fix ⟨97, by decide⟩ ⟨49, by decide⟩ p hp j hj hq fz1_97_49 fz2_97_49
  · exact match_zero_fix ⟨98, by decide⟩ ⟨49, by decide⟩ p hp j hj hq fz1_98_49 fz2_98_49
  · exact match_zero_fix ⟨99, by decide⟩ ⟨49, by decide⟩ p hp j hj hq fz1_99_49 fz2_99_49
  · exact match_zero_fix ⟨100, by decide⟩ ⟨49, by decide⟩ p hp j hj hq fz1_100_49 fz2_100_49
  · exact match_zero_fix ⟨101, by decide⟩ ⟨49, by decide⟩ p hp j hj hq fz1_101_49 fz2_101_49
  · exact match_zero_fix ⟨102, by decide⟩ ⟨49, by decide⟩ p hp j hj hq fz1_102_49 fz2_102_49
  · exact match_zero_fix ⟨103, by decide⟩ ⟨49, by decide⟩ p hp j hj hq fz1_103_49 fz2_103_49
  · exact match_zero_fix ⟨104, by decide⟩ ⟨49, by decide⟩ p hp j hj hq fz1_104_49 fz2_104_49
  · exact match_zero_fix ⟨105, by decide⟩ ⟨49, by decide⟩ p hp j hj hq fz1_105_49 fz2_105_49
  · exact match_zero_fix ⟨106, by decide⟩ ⟨49, by decide⟩ p hp j hj hq fz1_106_49 fz2_106_49
  · exact match_zero_fix ⟨107, by decide⟩ ⟨49, by decide⟩ p hp j hj hq fz1_107_49 fz2_107_49
  · exact match_zero_fix ⟨108, by decide⟩ ⟨49, by decide⟩ p hp j hj hq fz1_108_49 fz2_108_49
  · exact match_zero_fix ⟨109, by decide⟩ ⟨49, by decide⟩ p hp j hj hq fz1_109_49 fz2_109_49
  · exact match_zero_fix ⟨110, by decide⟩ ⟨49, by decide⟩ p hp j hj hq fz1_110_49 fz2_110_49
  · exact pair_111_49 p hp hrep j hj hq
  · exact match_zero_fix ⟨112, by decide⟩ ⟨49, by decide⟩ p hp j hj hq fz1_112_49 fz2_112_49
  · exact match_zero_fix ⟨113, by decide⟩ ⟨49, by decide⟩ p hp j hj hq fz1_113_49 fz2_113_49
  · exact match_zero_fix ⟨114, by decide⟩ ⟨49, by decide⟩ p hp j hj hq fz1_114_49 fz2_114_49
  · exact match_zero_fix ⟨115, by decide⟩ ⟨49, by decide⟩ p hp j hj hq fz1_115_49 fz2_115_49
  · exact match_zero_fix ⟨116, by decide⟩ ⟨49, by decide⟩ p hp j hj hq fz1_116_49 fz2_116_49
  · exact pair_117_49 p hp hrep j hj hq
  · exact match_zero_fix ⟨118, by decide⟩ ⟨49, by decide⟩ p hp j hj hq fz1_118_49 fz2_118_49
  · exact match_zero_fix ⟨119, by decide⟩ ⟨49, by decide⟩ p hp j hj hq fz1_119_49 fz2_119_49
  · exact match_zero_fix ⟨120, by decide⟩ ⟨49, by decide⟩ p hp j hj hq fz1_120_49 fz2_120_49
  · exact match_zero_fix ⟨121, by decide⟩ ⟨49, by decide⟩ p hp j hj hq fz1_121_49 fz2_121_49
  · exact pair_122_49 p hp hrep j hj hq
  · exact match_zero_fix ⟨123, by decide⟩ ⟨49, by decide⟩ p hp j hj hq fz1_123_49 fz2_123_49
  · exact match_zero_fix ⟨124, by decide⟩ ⟨49, by decide⟩ p hp j hj hq fz1_124_49 fz2_124_49
  · exact match_zero_fix ⟨125, by decide⟩ ⟨49, by decide⟩ p hp j hj hq fz1_125_49 fz2_125_49
  · exact match_zero_fix ⟨126, by decide⟩ ⟨49, by decide⟩ p hp j hj hq fz1_126_49 fz2_126_49
  · exact pair_127_49 p hp hrep j hj hq
  · exact match_zero_fix ⟨128, by decide⟩ ⟨49, by decide⟩ p hp j hj hq fz1_128_49 fz2_128_49
  · exact match_zero_fix ⟨129, by decide⟩ ⟨49, by decide⟩ p hp j hj hq fz1_129_49 fz2_129_49
  · exact match_zero_fix ⟨130, by decide⟩ ⟨49, by decide⟩ p hp j hj hq fz1_130_49 fz2_130_49
  · exact match_zero_fix ⟨131, by decide⟩ ⟨49, by decide⟩ p hp j hj hq fz1_131_49 fz2_131_49
  · exact pair_132_49 p hp hrep j hj hq
  · exact match_zero_fix ⟨133, by decide⟩ ⟨49, by decide⟩ p hp j hj hq fz1_133_49 fz2_133_49
  · exact match_zero_fix ⟨134, by decide⟩ ⟨49, by decide⟩ p hp j hj hq fz1_134_49 fz2_134_49
  · exact match_zero_fix ⟨135, by decide⟩ ⟨49, by decide⟩ p hp j hj hq fz1_135_49 fz2_135_49
  · exact match_zero_fix ⟨136, by decide⟩ ⟨49, by decide⟩ p hp j hj hq fz1_136_49 fz2_136_49
  · exact pair_137_49 p hp hrep j hj hq
  · exact match_zero_fix ⟨138, by decide⟩ ⟨49, by decide⟩ p hp j hj hq fz1_138_49 fz2_138_49
  · exact match_zero_fix ⟨139, by decide⟩ ⟨49, by decide⟩ p hp j hj hq fz1_139_49 fz2_139_49
  · exact match_zero_fix ⟨140, by decide⟩ ⟨49, by decide⟩ p hp j hj hq fz1_140_49 fz2_140_49
  · exact match_zero_fix ⟨141, by decide⟩ ⟨49, by decide⟩ p hp j hj hq fz1_141_49 fz2_141_49
  · exact match_zero_fix ⟨142, by decide⟩ ⟨49, by decide⟩ p hp j hj hq fz1_142_49 fz2_142_49
  · exact match_zero_fix ⟨143, by decide⟩ ⟨49, by decide⟩ p hp j hj hq fz1_143_49 fz2_143_49
  · exact match_zero_fix ⟨144, by decide⟩ ⟨49, by decide⟩ p hp j hj hq fz1_144_49 fz2_144_49
  · exact match_zero_fix ⟨145, by decide⟩ ⟨49, by decide⟩ p hp j hj hq fz1_145_49 fz2_145_49
  · exact pair_146_49 p hp hrep j hj hq
  · exact pair_147_49 p hp hrep j hj hq

theorem master_50 (p : Nat) (hp : p < (Q2.transData.getD 50 []).length)
    (hrep : (Q2.cosetIsRep.getD 50 []).getD p false = true)
    (rK : Fin 148) (j : Nat) (hj : j < (repChars.getD rK.val []).length)
    (hq : (normIsRep.getD rK.val []).getD j false = true) :
    species (Q2.reps (⟨50, by decide⟩ : Fin 148)) (colE2 ⟨50, by decide⟩ p hp)
        (rowE2 rK j hj hq)
      = species (reps (⟨50, by decide⟩ : Fin 148))
        (colE1 ⟨50, by decide⟩ p (transLenTr ⟨50, by decide⟩ p hp)) (rowE1 rK j hj) := by
  rcases rK with ⟨nK, hnK⟩; interval_cases nK
  · exact match_zero_len ⟨0, by decide⟩ ⟨50, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨1, by decide⟩ ⟨50, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨2, by decide⟩ ⟨50, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨3, by decide⟩ ⟨50, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨4, by decide⟩ ⟨50, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨5, by decide⟩ ⟨50, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨6, by decide⟩ ⟨50, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨7, by decide⟩ ⟨50, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨8, by decide⟩ ⟨50, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨9, by decide⟩ ⟨50, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨10, by decide⟩ ⟨50, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨11, by decide⟩ ⟨50, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨12, by decide⟩ ⟨50, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_fix ⟨13, by decide⟩ ⟨50, by decide⟩ p hp j hj hq fz1_13_50 fz2_13_50
  · exact match_zero_fix ⟨14, by decide⟩ ⟨50, by decide⟩ p hp j hj hq fz1_14_50 fz2_14_50
  · exact match_zero_fix ⟨15, by decide⟩ ⟨50, by decide⟩ p hp j hj hq fz1_15_50 fz2_15_50
  · exact match_zero_fix ⟨16, by decide⟩ ⟨50, by decide⟩ p hp j hj hq fz1_16_50 fz2_16_50
  · exact match_zero_fix ⟨17, by decide⟩ ⟨50, by decide⟩ p hp j hj hq fz1_17_50 fz2_17_50
  · exact match_zero_fix ⟨18, by decide⟩ ⟨50, by decide⟩ p hp j hj hq fz1_18_50 fz2_18_50
  · exact match_zero_fix ⟨19, by decide⟩ ⟨50, by decide⟩ p hp j hj hq fz1_19_50 fz2_19_50
  · exact match_zero_fix ⟨20, by decide⟩ ⟨50, by decide⟩ p hp j hj hq fz1_20_50 fz2_20_50
  · exact match_zero_fix ⟨21, by decide⟩ ⟨50, by decide⟩ p hp j hj hq fz1_21_50 fz2_21_50
  · exact match_zero_fix ⟨22, by decide⟩ ⟨50, by decide⟩ p hp j hj hq fz1_22_50 fz2_22_50
  · exact match_zero_fix ⟨23, by decide⟩ ⟨50, by decide⟩ p hp j hj hq fz1_23_50 fz2_23_50
  · exact match_zero_fix ⟨24, by decide⟩ ⟨50, by decide⟩ p hp j hj hq fz1_24_50 fz2_24_50
  · exact match_zero_fix ⟨25, by decide⟩ ⟨50, by decide⟩ p hp j hj hq fz1_25_50 fz2_25_50
  · exact match_zero_fix ⟨26, by decide⟩ ⟨50, by decide⟩ p hp j hj hq fz1_26_50 fz2_26_50
  · exact match_zero_fix ⟨27, by decide⟩ ⟨50, by decide⟩ p hp j hj hq fz1_27_50 fz2_27_50
  · exact match_zero_fix ⟨28, by decide⟩ ⟨50, by decide⟩ p hp j hj hq fz1_28_50 fz2_28_50
  · exact match_zero_fix ⟨29, by decide⟩ ⟨50, by decide⟩ p hp j hj hq fz1_29_50 fz2_29_50
  · exact match_zero_fix ⟨30, by decide⟩ ⟨50, by decide⟩ p hp j hj hq fz1_30_50 fz2_30_50
  · exact match_zero_fix ⟨31, by decide⟩ ⟨50, by decide⟩ p hp j hj hq fz1_31_50 fz2_31_50
  · exact match_zero_fix ⟨32, by decide⟩ ⟨50, by decide⟩ p hp j hj hq fz1_32_50 fz2_32_50
  · exact match_zero_fix ⟨33, by decide⟩ ⟨50, by decide⟩ p hp j hj hq fz1_33_50 fz2_33_50
  · exact match_zero_fix ⟨34, by decide⟩ ⟨50, by decide⟩ p hp j hj hq fz1_34_50 fz2_34_50
  · exact match_zero_fix ⟨35, by decide⟩ ⟨50, by decide⟩ p hp j hj hq fz1_35_50 fz2_35_50
  · exact match_zero_fix ⟨36, by decide⟩ ⟨50, by decide⟩ p hp j hj hq fz1_36_50 fz2_36_50
  · exact match_zero_fix ⟨37, by decide⟩ ⟨50, by decide⟩ p hp j hj hq fz1_37_50 fz2_37_50
  · exact match_zero_fix ⟨38, by decide⟩ ⟨50, by decide⟩ p hp j hj hq fz1_38_50 fz2_38_50
  · exact match_zero_fix ⟨39, by decide⟩ ⟨50, by decide⟩ p hp j hj hq fz1_39_50 fz2_39_50
  · exact match_zero_fix ⟨40, by decide⟩ ⟨50, by decide⟩ p hp j hj hq fz1_40_50 fz2_40_50
  · exact match_zero_fix ⟨41, by decide⟩ ⟨50, by decide⟩ p hp j hj hq fz1_41_50 fz2_41_50
  · exact match_zero_fix ⟨42, by decide⟩ ⟨50, by decide⟩ p hp j hj hq fz1_42_50 fz2_42_50
  · exact match_zero_fix ⟨43, by decide⟩ ⟨50, by decide⟩ p hp j hj hq fz1_43_50 fz2_43_50
  · exact match_zero_fix ⟨44, by decide⟩ ⟨50, by decide⟩ p hp j hj hq fz1_44_50 fz2_44_50
  · exact match_zero_fix ⟨45, by decide⟩ ⟨50, by decide⟩ p hp j hj hq fz1_45_50 fz2_45_50
  · exact match_zero_fix ⟨46, by decide⟩ ⟨50, by decide⟩ p hp j hj hq fz1_46_50 fz2_46_50
  · exact match_zero_fix ⟨47, by decide⟩ ⟨50, by decide⟩ p hp j hj hq fz1_47_50 fz2_47_50
  · exact match_zero_fix ⟨48, by decide⟩ ⟨50, by decide⟩ p hp j hj hq fz1_48_50 fz2_48_50
  · exact match_zero_fix ⟨49, by decide⟩ ⟨50, by decide⟩ p hp j hj hq fz1_49_50 fz2_49_50
  · exact pair_50_50 p hp hrep j hj hq
  · exact match_zero_fix ⟨51, by decide⟩ ⟨50, by decide⟩ p hp j hj hq fz1_51_50 fz2_51_50
  · exact match_zero_fix ⟨52, by decide⟩ ⟨50, by decide⟩ p hp j hj hq fz1_52_50 fz2_52_50
  · exact match_zero_fix ⟨53, by decide⟩ ⟨50, by decide⟩ p hp j hj hq fz1_53_50 fz2_53_50
  · exact match_zero_fix ⟨54, by decide⟩ ⟨50, by decide⟩ p hp j hj hq fz1_54_50 fz2_54_50
  · exact match_zero_fix ⟨55, by decide⟩ ⟨50, by decide⟩ p hp j hj hq fz1_55_50 fz2_55_50
  · exact match_zero_fix ⟨56, by decide⟩ ⟨50, by decide⟩ p hp j hj hq fz1_56_50 fz2_56_50
  · exact match_zero_fix ⟨57, by decide⟩ ⟨50, by decide⟩ p hp j hj hq fz1_57_50 fz2_57_50
  · exact match_zero_fix ⟨58, by decide⟩ ⟨50, by decide⟩ p hp j hj hq fz1_58_50 fz2_58_50
  · exact match_zero_fix ⟨59, by decide⟩ ⟨50, by decide⟩ p hp j hj hq fz1_59_50 fz2_59_50
  · exact match_zero_fix ⟨60, by decide⟩ ⟨50, by decide⟩ p hp j hj hq fz1_60_50 fz2_60_50
  · exact match_zero_fix ⟨61, by decide⟩ ⟨50, by decide⟩ p hp j hj hq fz1_61_50 fz2_61_50
  · exact match_zero_fix ⟨62, by decide⟩ ⟨50, by decide⟩ p hp j hj hq fz1_62_50 fz2_62_50
  · exact match_zero_fix ⟨63, by decide⟩ ⟨50, by decide⟩ p hp j hj hq fz1_63_50 fz2_63_50
  · exact match_zero_fix ⟨64, by decide⟩ ⟨50, by decide⟩ p hp j hj hq fz1_64_50 fz2_64_50
  · exact pair_65_50 p hp hrep j hj hq
  · exact pair_66_50 p hp hrep j hj hq
  · exact pair_67_50 p hp hrep j hj hq
  · exact pair_68_50 p hp hrep j hj hq
  · exact pair_69_50 p hp hrep j hj hq
  · exact match_zero_fix ⟨70, by decide⟩ ⟨50, by decide⟩ p hp j hj hq fz1_70_50 fz2_70_50
  · exact match_zero_fix ⟨71, by decide⟩ ⟨50, by decide⟩ p hp j hj hq fz1_71_50 fz2_71_50
  · exact match_zero_fix ⟨72, by decide⟩ ⟨50, by decide⟩ p hp j hj hq fz1_72_50 fz2_72_50
  · exact match_zero_fix ⟨73, by decide⟩ ⟨50, by decide⟩ p hp j hj hq fz1_73_50 fz2_73_50
  · exact match_zero_fix ⟨74, by decide⟩ ⟨50, by decide⟩ p hp j hj hq fz1_74_50 fz2_74_50
  · exact match_zero_fix ⟨75, by decide⟩ ⟨50, by decide⟩ p hp j hj hq fz1_75_50 fz2_75_50
  · exact match_zero_fix ⟨76, by decide⟩ ⟨50, by decide⟩ p hp j hj hq fz1_76_50 fz2_76_50
  · exact match_zero_fix ⟨77, by decide⟩ ⟨50, by decide⟩ p hp j hj hq fz1_77_50 fz2_77_50
  · exact match_zero_fix ⟨78, by decide⟩ ⟨50, by decide⟩ p hp j hj hq fz1_78_50 fz2_78_50
  · exact match_zero_fix ⟨79, by decide⟩ ⟨50, by decide⟩ p hp j hj hq fz1_79_50 fz2_79_50
  · exact match_zero_fix ⟨80, by decide⟩ ⟨50, by decide⟩ p hp j hj hq fz1_80_50 fz2_80_50
  · exact match_zero_fix ⟨81, by decide⟩ ⟨50, by decide⟩ p hp j hj hq fz1_81_50 fz2_81_50
  · exact match_zero_fix ⟨82, by decide⟩ ⟨50, by decide⟩ p hp j hj hq fz1_82_50 fz2_82_50
  · exact match_zero_fix ⟨83, by decide⟩ ⟨50, by decide⟩ p hp j hj hq fz1_83_50 fz2_83_50
  · exact match_zero_fix ⟨84, by decide⟩ ⟨50, by decide⟩ p hp j hj hq fz1_84_50 fz2_84_50
  · exact match_zero_fix ⟨85, by decide⟩ ⟨50, by decide⟩ p hp j hj hq fz1_85_50 fz2_85_50
  · exact match_zero_fix ⟨86, by decide⟩ ⟨50, by decide⟩ p hp j hj hq fz1_86_50 fz2_86_50
  · exact match_zero_fix ⟨87, by decide⟩ ⟨50, by decide⟩ p hp j hj hq fz1_87_50 fz2_87_50
  · exact match_zero_fix ⟨88, by decide⟩ ⟨50, by decide⟩ p hp j hj hq fz1_88_50 fz2_88_50
  · exact match_zero_fix ⟨89, by decide⟩ ⟨50, by decide⟩ p hp j hj hq fz1_89_50 fz2_89_50
  · exact match_zero_fix ⟨90, by decide⟩ ⟨50, by decide⟩ p hp j hj hq fz1_90_50 fz2_90_50
  · exact match_zero_fix ⟨91, by decide⟩ ⟨50, by decide⟩ p hp j hj hq fz1_91_50 fz2_91_50
  · exact match_zero_fix ⟨92, by decide⟩ ⟨50, by decide⟩ p hp j hj hq fz1_92_50 fz2_92_50
  · exact match_zero_fix ⟨93, by decide⟩ ⟨50, by decide⟩ p hp j hj hq fz1_93_50 fz2_93_50
  · exact match_zero_fix ⟨94, by decide⟩ ⟨50, by decide⟩ p hp j hj hq fz1_94_50 fz2_94_50
  · exact match_zero_fix ⟨95, by decide⟩ ⟨50, by decide⟩ p hp j hj hq fz1_95_50 fz2_95_50
  · exact match_zero_fix ⟨96, by decide⟩ ⟨50, by decide⟩ p hp j hj hq fz1_96_50 fz2_96_50
  · exact match_zero_fix ⟨97, by decide⟩ ⟨50, by decide⟩ p hp j hj hq fz1_97_50 fz2_97_50
  · exact match_zero_fix ⟨98, by decide⟩ ⟨50, by decide⟩ p hp j hj hq fz1_98_50 fz2_98_50
  · exact match_zero_fix ⟨99, by decide⟩ ⟨50, by decide⟩ p hp j hj hq fz1_99_50 fz2_99_50
  · exact match_zero_fix ⟨100, by decide⟩ ⟨50, by decide⟩ p hp j hj hq fz1_100_50 fz2_100_50
  · exact match_zero_fix ⟨101, by decide⟩ ⟨50, by decide⟩ p hp j hj hq fz1_101_50 fz2_101_50
  · exact match_zero_fix ⟨102, by decide⟩ ⟨50, by decide⟩ p hp j hj hq fz1_102_50 fz2_102_50
  · exact match_zero_fix ⟨103, by decide⟩ ⟨50, by decide⟩ p hp j hj hq fz1_103_50 fz2_103_50
  · exact match_zero_fix ⟨104, by decide⟩ ⟨50, by decide⟩ p hp j hj hq fz1_104_50 fz2_104_50
  · exact match_zero_fix ⟨105, by decide⟩ ⟨50, by decide⟩ p hp j hj hq fz1_105_50 fz2_105_50
  · exact match_zero_fix ⟨106, by decide⟩ ⟨50, by decide⟩ p hp j hj hq fz1_106_50 fz2_106_50
  · exact match_zero_fix ⟨107, by decide⟩ ⟨50, by decide⟩ p hp j hj hq fz1_107_50 fz2_107_50
  · exact match_zero_fix ⟨108, by decide⟩ ⟨50, by decide⟩ p hp j hj hq fz1_108_50 fz2_108_50
  · exact match_zero_fix ⟨109, by decide⟩ ⟨50, by decide⟩ p hp j hj hq fz1_109_50 fz2_109_50
  · exact match_zero_fix ⟨110, by decide⟩ ⟨50, by decide⟩ p hp j hj hq fz1_110_50 fz2_110_50
  · exact match_zero_fix ⟨111, by decide⟩ ⟨50, by decide⟩ p hp j hj hq fz1_111_50 fz2_111_50
  · exact pair_112_50 p hp hrep j hj hq
  · exact match_zero_fix ⟨113, by decide⟩ ⟨50, by decide⟩ p hp j hj hq fz1_113_50 fz2_113_50
  · exact match_zero_fix ⟨114, by decide⟩ ⟨50, by decide⟩ p hp j hj hq fz1_114_50 fz2_114_50
  · exact match_zero_fix ⟨115, by decide⟩ ⟨50, by decide⟩ p hp j hj hq fz1_115_50 fz2_115_50
  · exact match_zero_fix ⟨116, by decide⟩ ⟨50, by decide⟩ p hp j hj hq fz1_116_50 fz2_116_50
  · exact match_zero_fix ⟨117, by decide⟩ ⟨50, by decide⟩ p hp j hj hq fz1_117_50 fz2_117_50
  · exact pair_118_50 p hp hrep j hj hq
  · exact match_zero_fix ⟨119, by decide⟩ ⟨50, by decide⟩ p hp j hj hq fz1_119_50 fz2_119_50
  · exact match_zero_fix ⟨120, by decide⟩ ⟨50, by decide⟩ p hp j hj hq fz1_120_50 fz2_120_50
  · exact match_zero_fix ⟨121, by decide⟩ ⟨50, by decide⟩ p hp j hj hq fz1_121_50 fz2_121_50
  · exact match_zero_fix ⟨122, by decide⟩ ⟨50, by decide⟩ p hp j hj hq fz1_122_50 fz2_122_50
  · exact pair_123_50 p hp hrep j hj hq
  · exact match_zero_fix ⟨124, by decide⟩ ⟨50, by decide⟩ p hp j hj hq fz1_124_50 fz2_124_50
  · exact match_zero_fix ⟨125, by decide⟩ ⟨50, by decide⟩ p hp j hj hq fz1_125_50 fz2_125_50
  · exact match_zero_fix ⟨126, by decide⟩ ⟨50, by decide⟩ p hp j hj hq fz1_126_50 fz2_126_50
  · exact match_zero_fix ⟨127, by decide⟩ ⟨50, by decide⟩ p hp j hj hq fz1_127_50 fz2_127_50
  · exact pair_128_50 p hp hrep j hj hq
  · exact match_zero_fix ⟨129, by decide⟩ ⟨50, by decide⟩ p hp j hj hq fz1_129_50 fz2_129_50
  · exact match_zero_fix ⟨130, by decide⟩ ⟨50, by decide⟩ p hp j hj hq fz1_130_50 fz2_130_50
  · exact match_zero_fix ⟨131, by decide⟩ ⟨50, by decide⟩ p hp j hj hq fz1_131_50 fz2_131_50
  · exact match_zero_fix ⟨132, by decide⟩ ⟨50, by decide⟩ p hp j hj hq fz1_132_50 fz2_132_50
  · exact pair_133_50 p hp hrep j hj hq
  · exact match_zero_fix ⟨134, by decide⟩ ⟨50, by decide⟩ p hp j hj hq fz1_134_50 fz2_134_50
  · exact match_zero_fix ⟨135, by decide⟩ ⟨50, by decide⟩ p hp j hj hq fz1_135_50 fz2_135_50
  · exact match_zero_fix ⟨136, by decide⟩ ⟨50, by decide⟩ p hp j hj hq fz1_136_50 fz2_136_50
  · exact match_zero_fix ⟨137, by decide⟩ ⟨50, by decide⟩ p hp j hj hq fz1_137_50 fz2_137_50
  · exact pair_138_50 p hp hrep j hj hq
  · exact match_zero_fix ⟨139, by decide⟩ ⟨50, by decide⟩ p hp j hj hq fz1_139_50 fz2_139_50
  · exact match_zero_fix ⟨140, by decide⟩ ⟨50, by decide⟩ p hp j hj hq fz1_140_50 fz2_140_50
  · exact match_zero_fix ⟨141, by decide⟩ ⟨50, by decide⟩ p hp j hj hq fz1_141_50 fz2_141_50
  · exact match_zero_fix ⟨142, by decide⟩ ⟨50, by decide⟩ p hp j hj hq fz1_142_50 fz2_142_50
  · exact match_zero_fix ⟨143, by decide⟩ ⟨50, by decide⟩ p hp j hj hq fz1_143_50 fz2_143_50
  · exact match_zero_fix ⟨144, by decide⟩ ⟨50, by decide⟩ p hp j hj hq fz1_144_50 fz2_144_50
  · exact match_zero_fix ⟨145, by decide⟩ ⟨50, by decide⟩ p hp j hj hq fz1_145_50 fz2_145_50
  · exact pair_146_50 p hp hrep j hj hq
  · exact pair_147_50 p hp hrep j hj hq

theorem master_51 (p : Nat) (hp : p < (Q2.transData.getD 51 []).length)
    (hrep : (Q2.cosetIsRep.getD 51 []).getD p false = true)
    (rK : Fin 148) (j : Nat) (hj : j < (repChars.getD rK.val []).length)
    (hq : (normIsRep.getD rK.val []).getD j false = true) :
    species (Q2.reps (⟨51, by decide⟩ : Fin 148)) (colE2 ⟨51, by decide⟩ p hp)
        (rowE2 rK j hj hq)
      = species (reps (⟨51, by decide⟩ : Fin 148))
        (colE1 ⟨51, by decide⟩ p (transLenTr ⟨51, by decide⟩ p hp)) (rowE1 rK j hj) := by
  rcases rK with ⟨nK, hnK⟩; interval_cases nK
  · exact match_zero_len ⟨0, by decide⟩ ⟨51, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨1, by decide⟩ ⟨51, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨2, by decide⟩ ⟨51, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨3, by decide⟩ ⟨51, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨4, by decide⟩ ⟨51, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨5, by decide⟩ ⟨51, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨6, by decide⟩ ⟨51, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨7, by decide⟩ ⟨51, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨8, by decide⟩ ⟨51, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨9, by decide⟩ ⟨51, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨10, by decide⟩ ⟨51, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨11, by decide⟩ ⟨51, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨12, by decide⟩ ⟨51, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_fix ⟨13, by decide⟩ ⟨51, by decide⟩ p hp j hj hq fz1_13_51 fz2_13_51
  · exact match_zero_fix ⟨14, by decide⟩ ⟨51, by decide⟩ p hp j hj hq fz1_14_51 fz2_14_51
  · exact match_zero_fix ⟨15, by decide⟩ ⟨51, by decide⟩ p hp j hj hq fz1_15_51 fz2_15_51
  · exact match_zero_fix ⟨16, by decide⟩ ⟨51, by decide⟩ p hp j hj hq fz1_16_51 fz2_16_51
  · exact match_zero_fix ⟨17, by decide⟩ ⟨51, by decide⟩ p hp j hj hq fz1_17_51 fz2_17_51
  · exact match_zero_fix ⟨18, by decide⟩ ⟨51, by decide⟩ p hp j hj hq fz1_18_51 fz2_18_51
  · exact match_zero_fix ⟨19, by decide⟩ ⟨51, by decide⟩ p hp j hj hq fz1_19_51 fz2_19_51
  · exact match_zero_fix ⟨20, by decide⟩ ⟨51, by decide⟩ p hp j hj hq fz1_20_51 fz2_20_51
  · exact match_zero_fix ⟨21, by decide⟩ ⟨51, by decide⟩ p hp j hj hq fz1_21_51 fz2_21_51
  · exact match_zero_fix ⟨22, by decide⟩ ⟨51, by decide⟩ p hp j hj hq fz1_22_51 fz2_22_51
  · exact match_zero_fix ⟨23, by decide⟩ ⟨51, by decide⟩ p hp j hj hq fz1_23_51 fz2_23_51
  · exact match_zero_fix ⟨24, by decide⟩ ⟨51, by decide⟩ p hp j hj hq fz1_24_51 fz2_24_51
  · exact match_zero_fix ⟨25, by decide⟩ ⟨51, by decide⟩ p hp j hj hq fz1_25_51 fz2_25_51
  · exact match_zero_fix ⟨26, by decide⟩ ⟨51, by decide⟩ p hp j hj hq fz1_26_51 fz2_26_51
  · exact match_zero_fix ⟨27, by decide⟩ ⟨51, by decide⟩ p hp j hj hq fz1_27_51 fz2_27_51
  · exact match_zero_fix ⟨28, by decide⟩ ⟨51, by decide⟩ p hp j hj hq fz1_28_51 fz2_28_51
  · exact match_zero_fix ⟨29, by decide⟩ ⟨51, by decide⟩ p hp j hj hq fz1_29_51 fz2_29_51
  · exact match_zero_fix ⟨30, by decide⟩ ⟨51, by decide⟩ p hp j hj hq fz1_30_51 fz2_30_51
  · exact match_zero_fix ⟨31, by decide⟩ ⟨51, by decide⟩ p hp j hj hq fz1_31_51 fz2_31_51
  · exact match_zero_fix ⟨32, by decide⟩ ⟨51, by decide⟩ p hp j hj hq fz1_32_51 fz2_32_51
  · exact match_zero_fix ⟨33, by decide⟩ ⟨51, by decide⟩ p hp j hj hq fz1_33_51 fz2_33_51
  · exact match_zero_fix ⟨34, by decide⟩ ⟨51, by decide⟩ p hp j hj hq fz1_34_51 fz2_34_51
  · exact match_zero_fix ⟨35, by decide⟩ ⟨51, by decide⟩ p hp j hj hq fz1_35_51 fz2_35_51
  · exact match_zero_fix ⟨36, by decide⟩ ⟨51, by decide⟩ p hp j hj hq fz1_36_51 fz2_36_51
  · exact match_zero_fix ⟨37, by decide⟩ ⟨51, by decide⟩ p hp j hj hq fz1_37_51 fz2_37_51
  · exact match_zero_fix ⟨38, by decide⟩ ⟨51, by decide⟩ p hp j hj hq fz1_38_51 fz2_38_51
  · exact match_zero_fix ⟨39, by decide⟩ ⟨51, by decide⟩ p hp j hj hq fz1_39_51 fz2_39_51
  · exact match_zero_fix ⟨40, by decide⟩ ⟨51, by decide⟩ p hp j hj hq fz1_40_51 fz2_40_51
  · exact match_zero_fix ⟨41, by decide⟩ ⟨51, by decide⟩ p hp j hj hq fz1_41_51 fz2_41_51
  · exact match_zero_fix ⟨42, by decide⟩ ⟨51, by decide⟩ p hp j hj hq fz1_42_51 fz2_42_51
  · exact match_zero_fix ⟨43, by decide⟩ ⟨51, by decide⟩ p hp j hj hq fz1_43_51 fz2_43_51
  · exact match_zero_fix ⟨44, by decide⟩ ⟨51, by decide⟩ p hp j hj hq fz1_44_51 fz2_44_51
  · exact match_zero_fix ⟨45, by decide⟩ ⟨51, by decide⟩ p hp j hj hq fz1_45_51 fz2_45_51
  · exact match_zero_fix ⟨46, by decide⟩ ⟨51, by decide⟩ p hp j hj hq fz1_46_51 fz2_46_51
  · exact match_zero_fix ⟨47, by decide⟩ ⟨51, by decide⟩ p hp j hj hq fz1_47_51 fz2_47_51
  · exact match_zero_fix ⟨48, by decide⟩ ⟨51, by decide⟩ p hp j hj hq fz1_48_51 fz2_48_51
  · exact match_zero_fix ⟨49, by decide⟩ ⟨51, by decide⟩ p hp j hj hq fz1_49_51 fz2_49_51
  · exact match_zero_fix ⟨50, by decide⟩ ⟨51, by decide⟩ p hp j hj hq fz1_50_51 fz2_50_51
  · exact pair_51_51 p hp hrep j hj hq
  · exact match_zero_fix ⟨52, by decide⟩ ⟨51, by decide⟩ p hp j hj hq fz1_52_51 fz2_52_51
  · exact match_zero_fix ⟨53, by decide⟩ ⟨51, by decide⟩ p hp j hj hq fz1_53_51 fz2_53_51
  · exact match_zero_fix ⟨54, by decide⟩ ⟨51, by decide⟩ p hp j hj hq fz1_54_51 fz2_54_51
  · exact match_zero_fix ⟨55, by decide⟩ ⟨51, by decide⟩ p hp j hj hq fz1_55_51 fz2_55_51
  · exact match_zero_fix ⟨56, by decide⟩ ⟨51, by decide⟩ p hp j hj hq fz1_56_51 fz2_56_51
  · exact match_zero_fix ⟨57, by decide⟩ ⟨51, by decide⟩ p hp j hj hq fz1_57_51 fz2_57_51
  · exact match_zero_fix ⟨58, by decide⟩ ⟨51, by decide⟩ p hp j hj hq fz1_58_51 fz2_58_51
  · exact match_zero_fix ⟨59, by decide⟩ ⟨51, by decide⟩ p hp j hj hq fz1_59_51 fz2_59_51
  · exact match_zero_fix ⟨60, by decide⟩ ⟨51, by decide⟩ p hp j hj hq fz1_60_51 fz2_60_51
  · exact match_zero_fix ⟨61, by decide⟩ ⟨51, by decide⟩ p hp j hj hq fz1_61_51 fz2_61_51
  · exact match_zero_fix ⟨62, by decide⟩ ⟨51, by decide⟩ p hp j hj hq fz1_62_51 fz2_62_51
  · exact match_zero_fix ⟨63, by decide⟩ ⟨51, by decide⟩ p hp j hj hq fz1_63_51 fz2_63_51
  · exact match_zero_fix ⟨64, by decide⟩ ⟨51, by decide⟩ p hp j hj hq fz1_64_51 fz2_64_51
  · exact match_zero_fix ⟨65, by decide⟩ ⟨51, by decide⟩ p hp j hj hq fz1_65_51 fz2_65_51
  · exact match_zero_fix ⟨66, by decide⟩ ⟨51, by decide⟩ p hp j hj hq fz1_66_51 fz2_66_51
  · exact match_zero_fix ⟨67, by decide⟩ ⟨51, by decide⟩ p hp j hj hq fz1_67_51 fz2_67_51
  · exact match_zero_fix ⟨68, by decide⟩ ⟨51, by decide⟩ p hp j hj hq fz1_68_51 fz2_68_51
  · exact match_zero_fix ⟨69, by decide⟩ ⟨51, by decide⟩ p hp j hj hq fz1_69_51 fz2_69_51
  · exact pair_70_51 p hp hrep j hj hq
  · exact pair_71_51 p hp hrep j hj hq
  · exact pair_72_51 p hp hrep j hj hq
  · exact pair_73_51 p hp hrep j hj hq
  · exact pair_74_51 p hp hrep j hj hq
  · exact match_zero_fix ⟨75, by decide⟩ ⟨51, by decide⟩ p hp j hj hq fz1_75_51 fz2_75_51
  · exact match_zero_fix ⟨76, by decide⟩ ⟨51, by decide⟩ p hp j hj hq fz1_76_51 fz2_76_51
  · exact match_zero_fix ⟨77, by decide⟩ ⟨51, by decide⟩ p hp j hj hq fz1_77_51 fz2_77_51
  · exact match_zero_fix ⟨78, by decide⟩ ⟨51, by decide⟩ p hp j hj hq fz1_78_51 fz2_78_51
  · exact match_zero_fix ⟨79, by decide⟩ ⟨51, by decide⟩ p hp j hj hq fz1_79_51 fz2_79_51
  · exact match_zero_fix ⟨80, by decide⟩ ⟨51, by decide⟩ p hp j hj hq fz1_80_51 fz2_80_51
  · exact match_zero_fix ⟨81, by decide⟩ ⟨51, by decide⟩ p hp j hj hq fz1_81_51 fz2_81_51
  · exact match_zero_fix ⟨82, by decide⟩ ⟨51, by decide⟩ p hp j hj hq fz1_82_51 fz2_82_51
  · exact match_zero_fix ⟨83, by decide⟩ ⟨51, by decide⟩ p hp j hj hq fz1_83_51 fz2_83_51
  · exact match_zero_fix ⟨84, by decide⟩ ⟨51, by decide⟩ p hp j hj hq fz1_84_51 fz2_84_51
  · exact match_zero_fix ⟨85, by decide⟩ ⟨51, by decide⟩ p hp j hj hq fz1_85_51 fz2_85_51
  · exact match_zero_fix ⟨86, by decide⟩ ⟨51, by decide⟩ p hp j hj hq fz1_86_51 fz2_86_51
  · exact match_zero_fix ⟨87, by decide⟩ ⟨51, by decide⟩ p hp j hj hq fz1_87_51 fz2_87_51
  · exact match_zero_fix ⟨88, by decide⟩ ⟨51, by decide⟩ p hp j hj hq fz1_88_51 fz2_88_51
  · exact match_zero_fix ⟨89, by decide⟩ ⟨51, by decide⟩ p hp j hj hq fz1_89_51 fz2_89_51
  · exact match_zero_fix ⟨90, by decide⟩ ⟨51, by decide⟩ p hp j hj hq fz1_90_51 fz2_90_51
  · exact match_zero_fix ⟨91, by decide⟩ ⟨51, by decide⟩ p hp j hj hq fz1_91_51 fz2_91_51
  · exact match_zero_fix ⟨92, by decide⟩ ⟨51, by decide⟩ p hp j hj hq fz1_92_51 fz2_92_51
  · exact match_zero_fix ⟨93, by decide⟩ ⟨51, by decide⟩ p hp j hj hq fz1_93_51 fz2_93_51
  · exact match_zero_fix ⟨94, by decide⟩ ⟨51, by decide⟩ p hp j hj hq fz1_94_51 fz2_94_51
  · exact match_zero_fix ⟨95, by decide⟩ ⟨51, by decide⟩ p hp j hj hq fz1_95_51 fz2_95_51
  · exact match_zero_fix ⟨96, by decide⟩ ⟨51, by decide⟩ p hp j hj hq fz1_96_51 fz2_96_51
  · exact match_zero_fix ⟨97, by decide⟩ ⟨51, by decide⟩ p hp j hj hq fz1_97_51 fz2_97_51
  · exact match_zero_fix ⟨98, by decide⟩ ⟨51, by decide⟩ p hp j hj hq fz1_98_51 fz2_98_51
  · exact match_zero_fix ⟨99, by decide⟩ ⟨51, by decide⟩ p hp j hj hq fz1_99_51 fz2_99_51
  · exact match_zero_fix ⟨100, by decide⟩ ⟨51, by decide⟩ p hp j hj hq fz1_100_51 fz2_100_51
  · exact match_zero_fix ⟨101, by decide⟩ ⟨51, by decide⟩ p hp j hj hq fz1_101_51 fz2_101_51
  · exact match_zero_fix ⟨102, by decide⟩ ⟨51, by decide⟩ p hp j hj hq fz1_102_51 fz2_102_51
  · exact match_zero_fix ⟨103, by decide⟩ ⟨51, by decide⟩ p hp j hj hq fz1_103_51 fz2_103_51
  · exact match_zero_fix ⟨104, by decide⟩ ⟨51, by decide⟩ p hp j hj hq fz1_104_51 fz2_104_51
  · exact match_zero_fix ⟨105, by decide⟩ ⟨51, by decide⟩ p hp j hj hq fz1_105_51 fz2_105_51
  · exact match_zero_fix ⟨106, by decide⟩ ⟨51, by decide⟩ p hp j hj hq fz1_106_51 fz2_106_51
  · exact match_zero_fix ⟨107, by decide⟩ ⟨51, by decide⟩ p hp j hj hq fz1_107_51 fz2_107_51
  · exact match_zero_fix ⟨108, by decide⟩ ⟨51, by decide⟩ p hp j hj hq fz1_108_51 fz2_108_51
  · exact match_zero_fix ⟨109, by decide⟩ ⟨51, by decide⟩ p hp j hj hq fz1_109_51 fz2_109_51
  · exact match_zero_fix ⟨110, by decide⟩ ⟨51, by decide⟩ p hp j hj hq fz1_110_51 fz2_110_51
  · exact match_zero_fix ⟨111, by decide⟩ ⟨51, by decide⟩ p hp j hj hq fz1_111_51 fz2_111_51
  · exact match_zero_fix ⟨112, by decide⟩ ⟨51, by decide⟩ p hp j hj hq fz1_112_51 fz2_112_51
  · exact pair_113_51 p hp hrep j hj hq
  · exact match_zero_fix ⟨114, by decide⟩ ⟨51, by decide⟩ p hp j hj hq fz1_114_51 fz2_114_51
  · exact match_zero_fix ⟨115, by decide⟩ ⟨51, by decide⟩ p hp j hj hq fz1_115_51 fz2_115_51
  · exact match_zero_fix ⟨116, by decide⟩ ⟨51, by decide⟩ p hp j hj hq fz1_116_51 fz2_116_51
  · exact match_zero_fix ⟨117, by decide⟩ ⟨51, by decide⟩ p hp j hj hq fz1_117_51 fz2_117_51
  · exact match_zero_fix ⟨118, by decide⟩ ⟨51, by decide⟩ p hp j hj hq fz1_118_51 fz2_118_51
  · exact pair_119_51 p hp hrep j hj hq
  · exact match_zero_fix ⟨120, by decide⟩ ⟨51, by decide⟩ p hp j hj hq fz1_120_51 fz2_120_51
  · exact match_zero_fix ⟨121, by decide⟩ ⟨51, by decide⟩ p hp j hj hq fz1_121_51 fz2_121_51
  · exact match_zero_fix ⟨122, by decide⟩ ⟨51, by decide⟩ p hp j hj hq fz1_122_51 fz2_122_51
  · exact match_zero_fix ⟨123, by decide⟩ ⟨51, by decide⟩ p hp j hj hq fz1_123_51 fz2_123_51
  · exact pair_124_51 p hp hrep j hj hq
  · exact match_zero_fix ⟨125, by decide⟩ ⟨51, by decide⟩ p hp j hj hq fz1_125_51 fz2_125_51
  · exact match_zero_fix ⟨126, by decide⟩ ⟨51, by decide⟩ p hp j hj hq fz1_126_51 fz2_126_51
  · exact match_zero_fix ⟨127, by decide⟩ ⟨51, by decide⟩ p hp j hj hq fz1_127_51 fz2_127_51
  · exact match_zero_fix ⟨128, by decide⟩ ⟨51, by decide⟩ p hp j hj hq fz1_128_51 fz2_128_51
  · exact pair_129_51 p hp hrep j hj hq
  · exact match_zero_fix ⟨130, by decide⟩ ⟨51, by decide⟩ p hp j hj hq fz1_130_51 fz2_130_51
  · exact match_zero_fix ⟨131, by decide⟩ ⟨51, by decide⟩ p hp j hj hq fz1_131_51 fz2_131_51
  · exact match_zero_fix ⟨132, by decide⟩ ⟨51, by decide⟩ p hp j hj hq fz1_132_51 fz2_132_51
  · exact match_zero_fix ⟨133, by decide⟩ ⟨51, by decide⟩ p hp j hj hq fz1_133_51 fz2_133_51
  · exact pair_134_51 p hp hrep j hj hq
  · exact match_zero_fix ⟨135, by decide⟩ ⟨51, by decide⟩ p hp j hj hq fz1_135_51 fz2_135_51
  · exact match_zero_fix ⟨136, by decide⟩ ⟨51, by decide⟩ p hp j hj hq fz1_136_51 fz2_136_51
  · exact match_zero_fix ⟨137, by decide⟩ ⟨51, by decide⟩ p hp j hj hq fz1_137_51 fz2_137_51
  · exact match_zero_fix ⟨138, by decide⟩ ⟨51, by decide⟩ p hp j hj hq fz1_138_51 fz2_138_51
  · exact pair_139_51 p hp hrep j hj hq
  · exact match_zero_fix ⟨140, by decide⟩ ⟨51, by decide⟩ p hp j hj hq fz1_140_51 fz2_140_51
  · exact match_zero_fix ⟨141, by decide⟩ ⟨51, by decide⟩ p hp j hj hq fz1_141_51 fz2_141_51
  · exact match_zero_fix ⟨142, by decide⟩ ⟨51, by decide⟩ p hp j hj hq fz1_142_51 fz2_142_51
  · exact match_zero_fix ⟨143, by decide⟩ ⟨51, by decide⟩ p hp j hj hq fz1_143_51 fz2_143_51
  · exact match_zero_fix ⟨144, by decide⟩ ⟨51, by decide⟩ p hp j hj hq fz1_144_51 fz2_144_51
  · exact match_zero_fix ⟨145, by decide⟩ ⟨51, by decide⟩ p hp j hj hq fz1_145_51 fz2_145_51
  · exact pair_146_51 p hp hrep j hj hq
  · exact pair_147_51 p hp hrep j hj hq

theorem master_52 (p : Nat) (hp : p < (Q2.transData.getD 52 []).length)
    (hrep : (Q2.cosetIsRep.getD 52 []).getD p false = true)
    (rK : Fin 148) (j : Nat) (hj : j < (repChars.getD rK.val []).length)
    (hq : (normIsRep.getD rK.val []).getD j false = true) :
    species (Q2.reps (⟨52, by decide⟩ : Fin 148)) (colE2 ⟨52, by decide⟩ p hp)
        (rowE2 rK j hj hq)
      = species (reps (⟨52, by decide⟩ : Fin 148))
        (colE1 ⟨52, by decide⟩ p (transLenTr ⟨52, by decide⟩ p hp)) (rowE1 rK j hj) := by
  rcases rK with ⟨nK, hnK⟩; interval_cases nK
  · exact match_zero_len ⟨0, by decide⟩ ⟨52, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨1, by decide⟩ ⟨52, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨2, by decide⟩ ⟨52, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨3, by decide⟩ ⟨52, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨4, by decide⟩ ⟨52, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨5, by decide⟩ ⟨52, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨6, by decide⟩ ⟨52, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨7, by decide⟩ ⟨52, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨8, by decide⟩ ⟨52, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨9, by decide⟩ ⟨52, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨10, by decide⟩ ⟨52, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨11, by decide⟩ ⟨52, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨12, by decide⟩ ⟨52, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_fix ⟨13, by decide⟩ ⟨52, by decide⟩ p hp j hj hq fz1_13_52 fz2_13_52
  · exact match_zero_fix ⟨14, by decide⟩ ⟨52, by decide⟩ p hp j hj hq fz1_14_52 fz2_14_52
  · exact match_zero_fix ⟨15, by decide⟩ ⟨52, by decide⟩ p hp j hj hq fz1_15_52 fz2_15_52
  · exact match_zero_fix ⟨16, by decide⟩ ⟨52, by decide⟩ p hp j hj hq fz1_16_52 fz2_16_52
  · exact match_zero_fix ⟨17, by decide⟩ ⟨52, by decide⟩ p hp j hj hq fz1_17_52 fz2_17_52
  · exact match_zero_fix ⟨18, by decide⟩ ⟨52, by decide⟩ p hp j hj hq fz1_18_52 fz2_18_52
  · exact match_zero_fix ⟨19, by decide⟩ ⟨52, by decide⟩ p hp j hj hq fz1_19_52 fz2_19_52
  · exact match_zero_fix ⟨20, by decide⟩ ⟨52, by decide⟩ p hp j hj hq fz1_20_52 fz2_20_52
  · exact match_zero_fix ⟨21, by decide⟩ ⟨52, by decide⟩ p hp j hj hq fz1_21_52 fz2_21_52
  · exact match_zero_fix ⟨22, by decide⟩ ⟨52, by decide⟩ p hp j hj hq fz1_22_52 fz2_22_52
  · exact match_zero_fix ⟨23, by decide⟩ ⟨52, by decide⟩ p hp j hj hq fz1_23_52 fz2_23_52
  · exact match_zero_fix ⟨24, by decide⟩ ⟨52, by decide⟩ p hp j hj hq fz1_24_52 fz2_24_52
  · exact match_zero_fix ⟨25, by decide⟩ ⟨52, by decide⟩ p hp j hj hq fz1_25_52 fz2_25_52
  · exact match_zero_fix ⟨26, by decide⟩ ⟨52, by decide⟩ p hp j hj hq fz1_26_52 fz2_26_52
  · exact match_zero_fix ⟨27, by decide⟩ ⟨52, by decide⟩ p hp j hj hq fz1_27_52 fz2_27_52
  · exact match_zero_fix ⟨28, by decide⟩ ⟨52, by decide⟩ p hp j hj hq fz1_28_52 fz2_28_52
  · exact match_zero_fix ⟨29, by decide⟩ ⟨52, by decide⟩ p hp j hj hq fz1_29_52 fz2_29_52
  · exact match_zero_fix ⟨30, by decide⟩ ⟨52, by decide⟩ p hp j hj hq fz1_30_52 fz2_30_52
  · exact match_zero_fix ⟨31, by decide⟩ ⟨52, by decide⟩ p hp j hj hq fz1_31_52 fz2_31_52
  · exact match_zero_fix ⟨32, by decide⟩ ⟨52, by decide⟩ p hp j hj hq fz1_32_52 fz2_32_52
  · exact match_zero_fix ⟨33, by decide⟩ ⟨52, by decide⟩ p hp j hj hq fz1_33_52 fz2_33_52
  · exact match_zero_fix ⟨34, by decide⟩ ⟨52, by decide⟩ p hp j hj hq fz1_34_52 fz2_34_52
  · exact match_zero_fix ⟨35, by decide⟩ ⟨52, by decide⟩ p hp j hj hq fz1_35_52 fz2_35_52
  · exact match_zero_fix ⟨36, by decide⟩ ⟨52, by decide⟩ p hp j hj hq fz1_36_52 fz2_36_52
  · exact match_zero_fix ⟨37, by decide⟩ ⟨52, by decide⟩ p hp j hj hq fz1_37_52 fz2_37_52
  · exact match_zero_fix ⟨38, by decide⟩ ⟨52, by decide⟩ p hp j hj hq fz1_38_52 fz2_38_52
  · exact match_zero_fix ⟨39, by decide⟩ ⟨52, by decide⟩ p hp j hj hq fz1_39_52 fz2_39_52
  · exact match_zero_fix ⟨40, by decide⟩ ⟨52, by decide⟩ p hp j hj hq fz1_40_52 fz2_40_52
  · exact match_zero_fix ⟨41, by decide⟩ ⟨52, by decide⟩ p hp j hj hq fz1_41_52 fz2_41_52
  · exact match_zero_fix ⟨42, by decide⟩ ⟨52, by decide⟩ p hp j hj hq fz1_42_52 fz2_42_52
  · exact match_zero_fix ⟨43, by decide⟩ ⟨52, by decide⟩ p hp j hj hq fz1_43_52 fz2_43_52
  · exact match_zero_fix ⟨44, by decide⟩ ⟨52, by decide⟩ p hp j hj hq fz1_44_52 fz2_44_52
  · exact match_zero_fix ⟨45, by decide⟩ ⟨52, by decide⟩ p hp j hj hq fz1_45_52 fz2_45_52
  · exact match_zero_fix ⟨46, by decide⟩ ⟨52, by decide⟩ p hp j hj hq fz1_46_52 fz2_46_52
  · exact match_zero_fix ⟨47, by decide⟩ ⟨52, by decide⟩ p hp j hj hq fz1_47_52 fz2_47_52
  · exact match_zero_fix ⟨48, by decide⟩ ⟨52, by decide⟩ p hp j hj hq fz1_48_52 fz2_48_52
  · exact match_zero_fix ⟨49, by decide⟩ ⟨52, by decide⟩ p hp j hj hq fz1_49_52 fz2_49_52
  · exact match_zero_fix ⟨50, by decide⟩ ⟨52, by decide⟩ p hp j hj hq fz1_50_52 fz2_50_52
  · exact match_zero_fix ⟨51, by decide⟩ ⟨52, by decide⟩ p hp j hj hq fz1_51_52 fz2_51_52
  · exact pair_52_52 p hp hrep j hj hq
  · exact match_zero_fix ⟨53, by decide⟩ ⟨52, by decide⟩ p hp j hj hq fz1_53_52 fz2_53_52
  · exact match_zero_fix ⟨54, by decide⟩ ⟨52, by decide⟩ p hp j hj hq fz1_54_52 fz2_54_52
  · exact match_zero_fix ⟨55, by decide⟩ ⟨52, by decide⟩ p hp j hj hq fz1_55_52 fz2_55_52
  · exact match_zero_fix ⟨56, by decide⟩ ⟨52, by decide⟩ p hp j hj hq fz1_56_52 fz2_56_52
  · exact match_zero_fix ⟨57, by decide⟩ ⟨52, by decide⟩ p hp j hj hq fz1_57_52 fz2_57_52
  · exact match_zero_fix ⟨58, by decide⟩ ⟨52, by decide⟩ p hp j hj hq fz1_58_52 fz2_58_52
  · exact match_zero_fix ⟨59, by decide⟩ ⟨52, by decide⟩ p hp j hj hq fz1_59_52 fz2_59_52
  · exact match_zero_fix ⟨60, by decide⟩ ⟨52, by decide⟩ p hp j hj hq fz1_60_52 fz2_60_52
  · exact match_zero_fix ⟨61, by decide⟩ ⟨52, by decide⟩ p hp j hj hq fz1_61_52 fz2_61_52
  · exact match_zero_fix ⟨62, by decide⟩ ⟨52, by decide⟩ p hp j hj hq fz1_62_52 fz2_62_52
  · exact match_zero_fix ⟨63, by decide⟩ ⟨52, by decide⟩ p hp j hj hq fz1_63_52 fz2_63_52
  · exact match_zero_fix ⟨64, by decide⟩ ⟨52, by decide⟩ p hp j hj hq fz1_64_52 fz2_64_52
  · exact match_zero_fix ⟨65, by decide⟩ ⟨52, by decide⟩ p hp j hj hq fz1_65_52 fz2_65_52
  · exact match_zero_fix ⟨66, by decide⟩ ⟨52, by decide⟩ p hp j hj hq fz1_66_52 fz2_66_52
  · exact match_zero_fix ⟨67, by decide⟩ ⟨52, by decide⟩ p hp j hj hq fz1_67_52 fz2_67_52
  · exact match_zero_fix ⟨68, by decide⟩ ⟨52, by decide⟩ p hp j hj hq fz1_68_52 fz2_68_52
  · exact match_zero_fix ⟨69, by decide⟩ ⟨52, by decide⟩ p hp j hj hq fz1_69_52 fz2_69_52
  · exact match_zero_fix ⟨70, by decide⟩ ⟨52, by decide⟩ p hp j hj hq fz1_70_52 fz2_70_52
  · exact match_zero_fix ⟨71, by decide⟩ ⟨52, by decide⟩ p hp j hj hq fz1_71_52 fz2_71_52
  · exact match_zero_fix ⟨72, by decide⟩ ⟨52, by decide⟩ p hp j hj hq fz1_72_52 fz2_72_52
  · exact match_zero_fix ⟨73, by decide⟩ ⟨52, by decide⟩ p hp j hj hq fz1_73_52 fz2_73_52
  · exact match_zero_fix ⟨74, by decide⟩ ⟨52, by decide⟩ p hp j hj hq fz1_74_52 fz2_74_52
  · exact pair_75_52 p hp hrep j hj hq
  · exact pair_76_52 p hp hrep j hj hq
  · exact pair_77_52 p hp hrep j hj hq
  · exact pair_78_52 p hp hrep j hj hq
  · exact pair_79_52 p hp hrep j hj hq
  · exact match_zero_fix ⟨80, by decide⟩ ⟨52, by decide⟩ p hp j hj hq fz1_80_52 fz2_80_52
  · exact match_zero_fix ⟨81, by decide⟩ ⟨52, by decide⟩ p hp j hj hq fz1_81_52 fz2_81_52
  · exact match_zero_fix ⟨82, by decide⟩ ⟨52, by decide⟩ p hp j hj hq fz1_82_52 fz2_82_52
  · exact match_zero_fix ⟨83, by decide⟩ ⟨52, by decide⟩ p hp j hj hq fz1_83_52 fz2_83_52
  · exact match_zero_fix ⟨84, by decide⟩ ⟨52, by decide⟩ p hp j hj hq fz1_84_52 fz2_84_52
  · exact match_zero_fix ⟨85, by decide⟩ ⟨52, by decide⟩ p hp j hj hq fz1_85_52 fz2_85_52
  · exact match_zero_fix ⟨86, by decide⟩ ⟨52, by decide⟩ p hp j hj hq fz1_86_52 fz2_86_52
  · exact match_zero_fix ⟨87, by decide⟩ ⟨52, by decide⟩ p hp j hj hq fz1_87_52 fz2_87_52
  · exact match_zero_fix ⟨88, by decide⟩ ⟨52, by decide⟩ p hp j hj hq fz1_88_52 fz2_88_52
  · exact match_zero_fix ⟨89, by decide⟩ ⟨52, by decide⟩ p hp j hj hq fz1_89_52 fz2_89_52
  · exact match_zero_fix ⟨90, by decide⟩ ⟨52, by decide⟩ p hp j hj hq fz1_90_52 fz2_90_52
  · exact match_zero_fix ⟨91, by decide⟩ ⟨52, by decide⟩ p hp j hj hq fz1_91_52 fz2_91_52
  · exact match_zero_fix ⟨92, by decide⟩ ⟨52, by decide⟩ p hp j hj hq fz1_92_52 fz2_92_52
  · exact match_zero_fix ⟨93, by decide⟩ ⟨52, by decide⟩ p hp j hj hq fz1_93_52 fz2_93_52
  · exact match_zero_fix ⟨94, by decide⟩ ⟨52, by decide⟩ p hp j hj hq fz1_94_52 fz2_94_52
  · exact match_zero_fix ⟨95, by decide⟩ ⟨52, by decide⟩ p hp j hj hq fz1_95_52 fz2_95_52
  · exact match_zero_fix ⟨96, by decide⟩ ⟨52, by decide⟩ p hp j hj hq fz1_96_52 fz2_96_52
  · exact match_zero_fix ⟨97, by decide⟩ ⟨52, by decide⟩ p hp j hj hq fz1_97_52 fz2_97_52
  · exact match_zero_fix ⟨98, by decide⟩ ⟨52, by decide⟩ p hp j hj hq fz1_98_52 fz2_98_52
  · exact match_zero_fix ⟨99, by decide⟩ ⟨52, by decide⟩ p hp j hj hq fz1_99_52 fz2_99_52
  · exact match_zero_fix ⟨100, by decide⟩ ⟨52, by decide⟩ p hp j hj hq fz1_100_52 fz2_100_52
  · exact match_zero_fix ⟨101, by decide⟩ ⟨52, by decide⟩ p hp j hj hq fz1_101_52 fz2_101_52
  · exact match_zero_fix ⟨102, by decide⟩ ⟨52, by decide⟩ p hp j hj hq fz1_102_52 fz2_102_52
  · exact match_zero_fix ⟨103, by decide⟩ ⟨52, by decide⟩ p hp j hj hq fz1_103_52 fz2_103_52
  · exact match_zero_fix ⟨104, by decide⟩ ⟨52, by decide⟩ p hp j hj hq fz1_104_52 fz2_104_52
  · exact match_zero_fix ⟨105, by decide⟩ ⟨52, by decide⟩ p hp j hj hq fz1_105_52 fz2_105_52
  · exact match_zero_fix ⟨106, by decide⟩ ⟨52, by decide⟩ p hp j hj hq fz1_106_52 fz2_106_52
  · exact match_zero_fix ⟨107, by decide⟩ ⟨52, by decide⟩ p hp j hj hq fz1_107_52 fz2_107_52
  · exact match_zero_fix ⟨108, by decide⟩ ⟨52, by decide⟩ p hp j hj hq fz1_108_52 fz2_108_52
  · exact match_zero_fix ⟨109, by decide⟩ ⟨52, by decide⟩ p hp j hj hq fz1_109_52 fz2_109_52
  · exact match_zero_fix ⟨110, by decide⟩ ⟨52, by decide⟩ p hp j hj hq fz1_110_52 fz2_110_52
  · exact match_zero_fix ⟨111, by decide⟩ ⟨52, by decide⟩ p hp j hj hq fz1_111_52 fz2_111_52
  · exact match_zero_fix ⟨112, by decide⟩ ⟨52, by decide⟩ p hp j hj hq fz1_112_52 fz2_112_52
  · exact match_zero_fix ⟨113, by decide⟩ ⟨52, by decide⟩ p hp j hj hq fz1_113_52 fz2_113_52
  · exact pair_114_52 p hp hrep j hj hq
  · exact match_zero_fix ⟨115, by decide⟩ ⟨52, by decide⟩ p hp j hj hq fz1_115_52 fz2_115_52
  · exact match_zero_fix ⟨116, by decide⟩ ⟨52, by decide⟩ p hp j hj hq fz1_116_52 fz2_116_52
  · exact match_zero_fix ⟨117, by decide⟩ ⟨52, by decide⟩ p hp j hj hq fz1_117_52 fz2_117_52
  · exact match_zero_fix ⟨118, by decide⟩ ⟨52, by decide⟩ p hp j hj hq fz1_118_52 fz2_118_52
  · exact match_zero_fix ⟨119, by decide⟩ ⟨52, by decide⟩ p hp j hj hq fz1_119_52 fz2_119_52
  · exact pair_120_52 p hp hrep j hj hq
  · exact match_zero_fix ⟨121, by decide⟩ ⟨52, by decide⟩ p hp j hj hq fz1_121_52 fz2_121_52
  · exact match_zero_fix ⟨122, by decide⟩ ⟨52, by decide⟩ p hp j hj hq fz1_122_52 fz2_122_52
  · exact match_zero_fix ⟨123, by decide⟩ ⟨52, by decide⟩ p hp j hj hq fz1_123_52 fz2_123_52
  · exact match_zero_fix ⟨124, by decide⟩ ⟨52, by decide⟩ p hp j hj hq fz1_124_52 fz2_124_52
  · exact pair_125_52 p hp hrep j hj hq
  · exact match_zero_fix ⟨126, by decide⟩ ⟨52, by decide⟩ p hp j hj hq fz1_126_52 fz2_126_52
  · exact match_zero_fix ⟨127, by decide⟩ ⟨52, by decide⟩ p hp j hj hq fz1_127_52 fz2_127_52
  · exact match_zero_fix ⟨128, by decide⟩ ⟨52, by decide⟩ p hp j hj hq fz1_128_52 fz2_128_52
  · exact match_zero_fix ⟨129, by decide⟩ ⟨52, by decide⟩ p hp j hj hq fz1_129_52 fz2_129_52
  · exact pair_130_52 p hp hrep j hj hq
  · exact match_zero_fix ⟨131, by decide⟩ ⟨52, by decide⟩ p hp j hj hq fz1_131_52 fz2_131_52
  · exact match_zero_fix ⟨132, by decide⟩ ⟨52, by decide⟩ p hp j hj hq fz1_132_52 fz2_132_52
  · exact match_zero_fix ⟨133, by decide⟩ ⟨52, by decide⟩ p hp j hj hq fz1_133_52 fz2_133_52
  · exact match_zero_fix ⟨134, by decide⟩ ⟨52, by decide⟩ p hp j hj hq fz1_134_52 fz2_134_52
  · exact pair_135_52 p hp hrep j hj hq
  · exact match_zero_fix ⟨136, by decide⟩ ⟨52, by decide⟩ p hp j hj hq fz1_136_52 fz2_136_52
  · exact match_zero_fix ⟨137, by decide⟩ ⟨52, by decide⟩ p hp j hj hq fz1_137_52 fz2_137_52
  · exact match_zero_fix ⟨138, by decide⟩ ⟨52, by decide⟩ p hp j hj hq fz1_138_52 fz2_138_52
  · exact match_zero_fix ⟨139, by decide⟩ ⟨52, by decide⟩ p hp j hj hq fz1_139_52 fz2_139_52
  · exact pair_140_52 p hp hrep j hj hq
  · exact match_zero_fix ⟨141, by decide⟩ ⟨52, by decide⟩ p hp j hj hq fz1_141_52 fz2_141_52
  · exact match_zero_fix ⟨142, by decide⟩ ⟨52, by decide⟩ p hp j hj hq fz1_142_52 fz2_142_52
  · exact match_zero_fix ⟨143, by decide⟩ ⟨52, by decide⟩ p hp j hj hq fz1_143_52 fz2_143_52
  · exact match_zero_fix ⟨144, by decide⟩ ⟨52, by decide⟩ p hp j hj hq fz1_144_52 fz2_144_52
  · exact match_zero_fix ⟨145, by decide⟩ ⟨52, by decide⟩ p hp j hj hq fz1_145_52 fz2_145_52
  · exact pair_146_52 p hp hrep j hj hq
  · exact pair_147_52 p hp hrep j hj hq

theorem master_53 (p : Nat) (hp : p < (Q2.transData.getD 53 []).length)
    (hrep : (Q2.cosetIsRep.getD 53 []).getD p false = true)
    (rK : Fin 148) (j : Nat) (hj : j < (repChars.getD rK.val []).length)
    (hq : (normIsRep.getD rK.val []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ p hp)
        (rowE2 rK j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ p (transLenTr ⟨53, by decide⟩ p hp)) (rowE1 rK j hj) := by
  rcases rK with ⟨nK, hnK⟩; interval_cases nK
  · exact match_zero_len ⟨0, by decide⟩ ⟨53, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨1, by decide⟩ ⟨53, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨2, by decide⟩ ⟨53, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨3, by decide⟩ ⟨53, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨4, by decide⟩ ⟨53, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨5, by decide⟩ ⟨53, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨6, by decide⟩ ⟨53, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨7, by decide⟩ ⟨53, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨8, by decide⟩ ⟨53, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨9, by decide⟩ ⟨53, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨10, by decide⟩ ⟨53, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨11, by decide⟩ ⟨53, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨12, by decide⟩ ⟨53, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_fix ⟨13, by decide⟩ ⟨53, by decide⟩ p hp j hj hq fz1_13_53 fz2_13_53
  · exact match_zero_fix ⟨14, by decide⟩ ⟨53, by decide⟩ p hp j hj hq fz1_14_53 fz2_14_53
  · exact match_zero_fix ⟨15, by decide⟩ ⟨53, by decide⟩ p hp j hj hq fz1_15_53 fz2_15_53
  · exact match_zero_fix ⟨16, by decide⟩ ⟨53, by decide⟩ p hp j hj hq fz1_16_53 fz2_16_53
  · exact match_zero_fix ⟨17, by decide⟩ ⟨53, by decide⟩ p hp j hj hq fz1_17_53 fz2_17_53
  · exact match_zero_fix ⟨18, by decide⟩ ⟨53, by decide⟩ p hp j hj hq fz1_18_53 fz2_18_53
  · exact match_zero_fix ⟨19, by decide⟩ ⟨53, by decide⟩ p hp j hj hq fz1_19_53 fz2_19_53
  · exact match_zero_fix ⟨20, by decide⟩ ⟨53, by decide⟩ p hp j hj hq fz1_20_53 fz2_20_53
  · exact match_zero_fix ⟨21, by decide⟩ ⟨53, by decide⟩ p hp j hj hq fz1_21_53 fz2_21_53
  · exact match_zero_fix ⟨22, by decide⟩ ⟨53, by decide⟩ p hp j hj hq fz1_22_53 fz2_22_53
  · exact match_zero_fix ⟨23, by decide⟩ ⟨53, by decide⟩ p hp j hj hq fz1_23_53 fz2_23_53
  · exact match_zero_fix ⟨24, by decide⟩ ⟨53, by decide⟩ p hp j hj hq fz1_24_53 fz2_24_53
  · exact match_zero_fix ⟨25, by decide⟩ ⟨53, by decide⟩ p hp j hj hq fz1_25_53 fz2_25_53
  · exact match_zero_fix ⟨26, by decide⟩ ⟨53, by decide⟩ p hp j hj hq fz1_26_53 fz2_26_53
  · exact match_zero_fix ⟨27, by decide⟩ ⟨53, by decide⟩ p hp j hj hq fz1_27_53 fz2_27_53
  · exact match_zero_fix ⟨28, by decide⟩ ⟨53, by decide⟩ p hp j hj hq fz1_28_53 fz2_28_53
  · exact match_zero_fix ⟨29, by decide⟩ ⟨53, by decide⟩ p hp j hj hq fz1_29_53 fz2_29_53
  · exact match_zero_fix ⟨30, by decide⟩ ⟨53, by decide⟩ p hp j hj hq fz1_30_53 fz2_30_53
  · exact match_zero_fix ⟨31, by decide⟩ ⟨53, by decide⟩ p hp j hj hq fz1_31_53 fz2_31_53
  · exact match_zero_fix ⟨32, by decide⟩ ⟨53, by decide⟩ p hp j hj hq fz1_32_53 fz2_32_53
  · exact match_zero_fix ⟨33, by decide⟩ ⟨53, by decide⟩ p hp j hj hq fz1_33_53 fz2_33_53
  · exact match_zero_fix ⟨34, by decide⟩ ⟨53, by decide⟩ p hp j hj hq fz1_34_53 fz2_34_53
  · exact match_zero_fix ⟨35, by decide⟩ ⟨53, by decide⟩ p hp j hj hq fz1_35_53 fz2_35_53
  · exact match_zero_fix ⟨36, by decide⟩ ⟨53, by decide⟩ p hp j hj hq fz1_36_53 fz2_36_53
  · exact match_zero_fix ⟨37, by decide⟩ ⟨53, by decide⟩ p hp j hj hq fz1_37_53 fz2_37_53
  · exact match_zero_fix ⟨38, by decide⟩ ⟨53, by decide⟩ p hp j hj hq fz1_38_53 fz2_38_53
  · exact match_zero_fix ⟨39, by decide⟩ ⟨53, by decide⟩ p hp j hj hq fz1_39_53 fz2_39_53
  · exact match_zero_fix ⟨40, by decide⟩ ⟨53, by decide⟩ p hp j hj hq fz1_40_53 fz2_40_53
  · exact match_zero_fix ⟨41, by decide⟩ ⟨53, by decide⟩ p hp j hj hq fz1_41_53 fz2_41_53
  · exact match_zero_fix ⟨42, by decide⟩ ⟨53, by decide⟩ p hp j hj hq fz1_42_53 fz2_42_53
  · exact match_zero_fix ⟨43, by decide⟩ ⟨53, by decide⟩ p hp j hj hq fz1_43_53 fz2_43_53
  · exact match_zero_fix ⟨44, by decide⟩ ⟨53, by decide⟩ p hp j hj hq fz1_44_53 fz2_44_53
  · exact match_zero_fix ⟨45, by decide⟩ ⟨53, by decide⟩ p hp j hj hq fz1_45_53 fz2_45_53
  · exact match_zero_fix ⟨46, by decide⟩ ⟨53, by decide⟩ p hp j hj hq fz1_46_53 fz2_46_53
  · exact match_zero_fix ⟨47, by decide⟩ ⟨53, by decide⟩ p hp j hj hq fz1_47_53 fz2_47_53
  · exact match_zero_fix ⟨48, by decide⟩ ⟨53, by decide⟩ p hp j hj hq fz1_48_53 fz2_48_53
  · exact match_zero_fix ⟨49, by decide⟩ ⟨53, by decide⟩ p hp j hj hq fz1_49_53 fz2_49_53
  · exact match_zero_fix ⟨50, by decide⟩ ⟨53, by decide⟩ p hp j hj hq fz1_50_53 fz2_50_53
  · exact match_zero_fix ⟨51, by decide⟩ ⟨53, by decide⟩ p hp j hj hq fz1_51_53 fz2_51_53
  · exact match_zero_fix ⟨52, by decide⟩ ⟨53, by decide⟩ p hp j hj hq fz1_52_53 fz2_52_53
  · exact pair_53_53 p hp hrep j hj hq
  · exact match_zero_fix ⟨54, by decide⟩ ⟨53, by decide⟩ p hp j hj hq fz1_54_53 fz2_54_53
  · exact match_zero_fix ⟨55, by decide⟩ ⟨53, by decide⟩ p hp j hj hq fz1_55_53 fz2_55_53
  · exact match_zero_fix ⟨56, by decide⟩ ⟨53, by decide⟩ p hp j hj hq fz1_56_53 fz2_56_53
  · exact match_zero_fix ⟨57, by decide⟩ ⟨53, by decide⟩ p hp j hj hq fz1_57_53 fz2_57_53
  · exact match_zero_fix ⟨58, by decide⟩ ⟨53, by decide⟩ p hp j hj hq fz1_58_53 fz2_58_53
  · exact match_zero_fix ⟨59, by decide⟩ ⟨53, by decide⟩ p hp j hj hq fz1_59_53 fz2_59_53
  · exact match_zero_fix ⟨60, by decide⟩ ⟨53, by decide⟩ p hp j hj hq fz1_60_53 fz2_60_53
  · exact match_zero_fix ⟨61, by decide⟩ ⟨53, by decide⟩ p hp j hj hq fz1_61_53 fz2_61_53
  · exact match_zero_fix ⟨62, by decide⟩ ⟨53, by decide⟩ p hp j hj hq fz1_62_53 fz2_62_53
  · exact match_zero_fix ⟨63, by decide⟩ ⟨53, by decide⟩ p hp j hj hq fz1_63_53 fz2_63_53
  · exact match_zero_fix ⟨64, by decide⟩ ⟨53, by decide⟩ p hp j hj hq fz1_64_53 fz2_64_53
  · exact match_zero_fix ⟨65, by decide⟩ ⟨53, by decide⟩ p hp j hj hq fz1_65_53 fz2_65_53
  · exact match_zero_fix ⟨66, by decide⟩ ⟨53, by decide⟩ p hp j hj hq fz1_66_53 fz2_66_53
  · exact match_zero_fix ⟨67, by decide⟩ ⟨53, by decide⟩ p hp j hj hq fz1_67_53 fz2_67_53
  · exact match_zero_fix ⟨68, by decide⟩ ⟨53, by decide⟩ p hp j hj hq fz1_68_53 fz2_68_53
  · exact match_zero_fix ⟨69, by decide⟩ ⟨53, by decide⟩ p hp j hj hq fz1_69_53 fz2_69_53
  · exact match_zero_fix ⟨70, by decide⟩ ⟨53, by decide⟩ p hp j hj hq fz1_70_53 fz2_70_53
  · exact match_zero_fix ⟨71, by decide⟩ ⟨53, by decide⟩ p hp j hj hq fz1_71_53 fz2_71_53
  · exact match_zero_fix ⟨72, by decide⟩ ⟨53, by decide⟩ p hp j hj hq fz1_72_53 fz2_72_53
  · exact match_zero_fix ⟨73, by decide⟩ ⟨53, by decide⟩ p hp j hj hq fz1_73_53 fz2_73_53
  · exact match_zero_fix ⟨74, by decide⟩ ⟨53, by decide⟩ p hp j hj hq fz1_74_53 fz2_74_53
  · exact match_zero_fix ⟨75, by decide⟩ ⟨53, by decide⟩ p hp j hj hq fz1_75_53 fz2_75_53
  · exact match_zero_fix ⟨76, by decide⟩ ⟨53, by decide⟩ p hp j hj hq fz1_76_53 fz2_76_53
  · exact match_zero_fix ⟨77, by decide⟩ ⟨53, by decide⟩ p hp j hj hq fz1_77_53 fz2_77_53
  · exact match_zero_fix ⟨78, by decide⟩ ⟨53, by decide⟩ p hp j hj hq fz1_78_53 fz2_78_53
  · exact match_zero_fix ⟨79, by decide⟩ ⟨53, by decide⟩ p hp j hj hq fz1_79_53 fz2_79_53
  · exact pair_80_53 p hp hrep j hj hq
  · exact pair_81_53 p hp hrep j hj hq
  · exact pair_82_53 p hp hrep j hj hq
  · exact pair_83_53 p hp hrep j hj hq
  · exact pair_84_53 p hp hrep j hj hq
  · exact match_zero_fix ⟨85, by decide⟩ ⟨53, by decide⟩ p hp j hj hq fz1_85_53 fz2_85_53
  · exact match_zero_fix ⟨86, by decide⟩ ⟨53, by decide⟩ p hp j hj hq fz1_86_53 fz2_86_53
  · exact match_zero_fix ⟨87, by decide⟩ ⟨53, by decide⟩ p hp j hj hq fz1_87_53 fz2_87_53
  · exact match_zero_fix ⟨88, by decide⟩ ⟨53, by decide⟩ p hp j hj hq fz1_88_53 fz2_88_53
  · exact match_zero_fix ⟨89, by decide⟩ ⟨53, by decide⟩ p hp j hj hq fz1_89_53 fz2_89_53
  · exact pair_90_53 p hp hrep j hj hq
  · exact pair_91_53 p hp hrep j hj hq
  · exact pair_92_53 p hp hrep j hj hq
  · exact pair_93_53 p hp hrep j hj hq
  · exact pair_94_53 p hp hrep j hj hq
  · exact pair_95_53 p hp hrep j hj hq
  · exact pair_96_53 p hp hrep j hj hq
  · exact pair_97_53 p hp hrep j hj hq
  · exact pair_98_53 p hp hrep j hj hq
  · exact pair_99_53 p hp hrep j hj hq
  · exact pair_100_53 p hp hrep j hj hq
  · exact pair_101_53 p hp hrep j hj hq
  · exact pair_102_53 p hp hrep j hj hq
  · exact pair_103_53 p hp hrep j hj hq
  · exact pair_104_53 p hp hrep j hj hq
  · exact pair_105_53 p hp hrep j hj hq
  · exact pair_106_53 p hp hrep j hj hq
  · exact pair_107_53 p hp hrep j hj hq
  · exact pair_108_53 p hp hrep j hj hq
  · exact pair_109_53 p hp hrep j hj hq
  · exact pair_110_53 p hp hrep j hj hq
  · exact pair_111_53 p hp hrep j hj hq
  · exact pair_112_53 p hp hrep j hj hq
  · exact pair_113_53 p hp hrep j hj hq
  · exact pair_114_53 p hp hrep j hj hq
  · exact pair_115_53 p hp hrep j hj hq
  · exact pair_116_53 p hp hrep j hj hq
  · exact pair_117_53 p hp hrep j hj hq
  · exact pair_118_53 p hp hrep j hj hq
  · exact pair_119_53 p hp hrep j hj hq
  · exact pair_120_53 p hp hrep j hj hq
  · exact pair_121_53 p hp hrep j hj hq
  · exact pair_122_53 p hp hrep j hj hq
  · exact pair_123_53 p hp hrep j hj hq
  · exact pair_124_53 p hp hrep j hj hq
  · exact pair_125_53 p hp hrep j hj hq
  · exact pair_126_53 p hp hrep j hj hq
  · exact pair_127_53 p hp hrep j hj hq
  · exact pair_128_53 p hp hrep j hj hq
  · exact pair_129_53 p hp hrep j hj hq
  · exact pair_130_53 p hp hrep j hj hq
  · exact pair_131_53 p hp hrep j hj hq
  · exact pair_132_53 p hp hrep j hj hq
  · exact pair_133_53 p hp hrep j hj hq
  · exact pair_134_53 p hp hrep j hj hq
  · exact pair_135_53 p hp hrep j hj hq
  · exact pair_136_53 p hp hrep j hj hq
  · exact pair_137_53 p hp hrep j hj hq
  · exact pair_138_53 p hp hrep j hj hq
  · exact pair_139_53 p hp hrep j hj hq
  · exact pair_140_53 p hp hrep j hj hq
  · exact pair_141_53 p hp hrep j hj hq
  · exact pair_142_53 p hp hrep j hj hq
  · exact pair_143_53 p hp hrep j hj hq
  · exact pair_144_53 p hp hrep j hj hq
  · exact pair_145_53 p hp hrep j hj hq
  · exact pair_146_53 p hp hrep j hj hq
  · exact pair_147_53 p hp hrep j hj hq

theorem master_54 (p : Nat) (hp : p < (Q2.transData.getD 54 []).length)
    (hrep : (Q2.cosetIsRep.getD 54 []).getD p false = true)
    (rK : Fin 148) (j : Nat) (hj : j < (repChars.getD rK.val []).length)
    (hq : (normIsRep.getD rK.val []).getD j false = true) :
    species (Q2.reps (⟨54, by decide⟩ : Fin 148)) (colE2 ⟨54, by decide⟩ p hp)
        (rowE2 rK j hj hq)
      = species (reps (⟨54, by decide⟩ : Fin 148))
        (colE1 ⟨54, by decide⟩ p (transLenTr ⟨54, by decide⟩ p hp)) (rowE1 rK j hj) := by
  rcases rK with ⟨nK, hnK⟩; interval_cases nK
  · exact match_zero_len ⟨0, by decide⟩ ⟨54, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨1, by decide⟩ ⟨54, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨2, by decide⟩ ⟨54, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨3, by decide⟩ ⟨54, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨4, by decide⟩ ⟨54, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨5, by decide⟩ ⟨54, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨6, by decide⟩ ⟨54, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨7, by decide⟩ ⟨54, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨8, by decide⟩ ⟨54, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨9, by decide⟩ ⟨54, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨10, by decide⟩ ⟨54, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨11, by decide⟩ ⟨54, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨12, by decide⟩ ⟨54, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_fix ⟨13, by decide⟩ ⟨54, by decide⟩ p hp j hj hq fz1_13_54 fz2_13_54
  · exact match_zero_fix ⟨14, by decide⟩ ⟨54, by decide⟩ p hp j hj hq fz1_14_54 fz2_14_54
  · exact match_zero_fix ⟨15, by decide⟩ ⟨54, by decide⟩ p hp j hj hq fz1_15_54 fz2_15_54
  · exact match_zero_fix ⟨16, by decide⟩ ⟨54, by decide⟩ p hp j hj hq fz1_16_54 fz2_16_54
  · exact match_zero_fix ⟨17, by decide⟩ ⟨54, by decide⟩ p hp j hj hq fz1_17_54 fz2_17_54
  · exact match_zero_fix ⟨18, by decide⟩ ⟨54, by decide⟩ p hp j hj hq fz1_18_54 fz2_18_54
  · exact match_zero_fix ⟨19, by decide⟩ ⟨54, by decide⟩ p hp j hj hq fz1_19_54 fz2_19_54
  · exact match_zero_fix ⟨20, by decide⟩ ⟨54, by decide⟩ p hp j hj hq fz1_20_54 fz2_20_54
  · exact match_zero_fix ⟨21, by decide⟩ ⟨54, by decide⟩ p hp j hj hq fz1_21_54 fz2_21_54
  · exact match_zero_fix ⟨22, by decide⟩ ⟨54, by decide⟩ p hp j hj hq fz1_22_54 fz2_22_54
  · exact match_zero_fix ⟨23, by decide⟩ ⟨54, by decide⟩ p hp j hj hq fz1_23_54 fz2_23_54
  · exact match_zero_fix ⟨24, by decide⟩ ⟨54, by decide⟩ p hp j hj hq fz1_24_54 fz2_24_54
  · exact match_zero_fix ⟨25, by decide⟩ ⟨54, by decide⟩ p hp j hj hq fz1_25_54 fz2_25_54
  · exact match_zero_fix ⟨26, by decide⟩ ⟨54, by decide⟩ p hp j hj hq fz1_26_54 fz2_26_54
  · exact match_zero_fix ⟨27, by decide⟩ ⟨54, by decide⟩ p hp j hj hq fz1_27_54 fz2_27_54
  · exact match_zero_fix ⟨28, by decide⟩ ⟨54, by decide⟩ p hp j hj hq fz1_28_54 fz2_28_54
  · exact match_zero_fix ⟨29, by decide⟩ ⟨54, by decide⟩ p hp j hj hq fz1_29_54 fz2_29_54
  · exact match_zero_fix ⟨30, by decide⟩ ⟨54, by decide⟩ p hp j hj hq fz1_30_54 fz2_30_54
  · exact match_zero_fix ⟨31, by decide⟩ ⟨54, by decide⟩ p hp j hj hq fz1_31_54 fz2_31_54
  · exact match_zero_fix ⟨32, by decide⟩ ⟨54, by decide⟩ p hp j hj hq fz1_32_54 fz2_32_54
  · exact match_zero_fix ⟨33, by decide⟩ ⟨54, by decide⟩ p hp j hj hq fz1_33_54 fz2_33_54
  · exact match_zero_fix ⟨34, by decide⟩ ⟨54, by decide⟩ p hp j hj hq fz1_34_54 fz2_34_54
  · exact match_zero_fix ⟨35, by decide⟩ ⟨54, by decide⟩ p hp j hj hq fz1_35_54 fz2_35_54
  · exact match_zero_fix ⟨36, by decide⟩ ⟨54, by decide⟩ p hp j hj hq fz1_36_54 fz2_36_54
  · exact match_zero_fix ⟨37, by decide⟩ ⟨54, by decide⟩ p hp j hj hq fz1_37_54 fz2_37_54
  · exact match_zero_fix ⟨38, by decide⟩ ⟨54, by decide⟩ p hp j hj hq fz1_38_54 fz2_38_54
  · exact match_zero_fix ⟨39, by decide⟩ ⟨54, by decide⟩ p hp j hj hq fz1_39_54 fz2_39_54
  · exact match_zero_fix ⟨40, by decide⟩ ⟨54, by decide⟩ p hp j hj hq fz1_40_54 fz2_40_54
  · exact match_zero_fix ⟨41, by decide⟩ ⟨54, by decide⟩ p hp j hj hq fz1_41_54 fz2_41_54
  · exact match_zero_fix ⟨42, by decide⟩ ⟨54, by decide⟩ p hp j hj hq fz1_42_54 fz2_42_54
  · exact match_zero_fix ⟨43, by decide⟩ ⟨54, by decide⟩ p hp j hj hq fz1_43_54 fz2_43_54
  · exact match_zero_fix ⟨44, by decide⟩ ⟨54, by decide⟩ p hp j hj hq fz1_44_54 fz2_44_54
  · exact match_zero_fix ⟨45, by decide⟩ ⟨54, by decide⟩ p hp j hj hq fz1_45_54 fz2_45_54
  · exact match_zero_fix ⟨46, by decide⟩ ⟨54, by decide⟩ p hp j hj hq fz1_46_54 fz2_46_54
  · exact match_zero_fix ⟨47, by decide⟩ ⟨54, by decide⟩ p hp j hj hq fz1_47_54 fz2_47_54
  · exact match_zero_fix ⟨48, by decide⟩ ⟨54, by decide⟩ p hp j hj hq fz1_48_54 fz2_48_54
  · exact match_zero_fix ⟨49, by decide⟩ ⟨54, by decide⟩ p hp j hj hq fz1_49_54 fz2_49_54
  · exact match_zero_fix ⟨50, by decide⟩ ⟨54, by decide⟩ p hp j hj hq fz1_50_54 fz2_50_54
  · exact match_zero_fix ⟨51, by decide⟩ ⟨54, by decide⟩ p hp j hj hq fz1_51_54 fz2_51_54
  · exact match_zero_fix ⟨52, by decide⟩ ⟨54, by decide⟩ p hp j hj hq fz1_52_54 fz2_52_54
  · exact match_zero_fix ⟨53, by decide⟩ ⟨54, by decide⟩ p hp j hj hq fz1_53_54 fz2_53_54
  · exact pair_54_54 p hp hrep j hj hq
  · exact match_zero_fix ⟨55, by decide⟩ ⟨54, by decide⟩ p hp j hj hq fz1_55_54 fz2_55_54
  · exact match_zero_fix ⟨56, by decide⟩ ⟨54, by decide⟩ p hp j hj hq fz1_56_54 fz2_56_54
  · exact match_zero_fix ⟨57, by decide⟩ ⟨54, by decide⟩ p hp j hj hq fz1_57_54 fz2_57_54
  · exact match_zero_fix ⟨58, by decide⟩ ⟨54, by decide⟩ p hp j hj hq fz1_58_54 fz2_58_54
  · exact match_zero_fix ⟨59, by decide⟩ ⟨54, by decide⟩ p hp j hj hq fz1_59_54 fz2_59_54
  · exact match_zero_fix ⟨60, by decide⟩ ⟨54, by decide⟩ p hp j hj hq fz1_60_54 fz2_60_54
  · exact match_zero_fix ⟨61, by decide⟩ ⟨54, by decide⟩ p hp j hj hq fz1_61_54 fz2_61_54
  · exact match_zero_fix ⟨62, by decide⟩ ⟨54, by decide⟩ p hp j hj hq fz1_62_54 fz2_62_54
  · exact match_zero_fix ⟨63, by decide⟩ ⟨54, by decide⟩ p hp j hj hq fz1_63_54 fz2_63_54
  · exact match_zero_fix ⟨64, by decide⟩ ⟨54, by decide⟩ p hp j hj hq fz1_64_54 fz2_64_54
  · exact match_zero_fix ⟨65, by decide⟩ ⟨54, by decide⟩ p hp j hj hq fz1_65_54 fz2_65_54
  · exact match_zero_fix ⟨66, by decide⟩ ⟨54, by decide⟩ p hp j hj hq fz1_66_54 fz2_66_54
  · exact match_zero_fix ⟨67, by decide⟩ ⟨54, by decide⟩ p hp j hj hq fz1_67_54 fz2_67_54
  · exact match_zero_fix ⟨68, by decide⟩ ⟨54, by decide⟩ p hp j hj hq fz1_68_54 fz2_68_54
  · exact match_zero_fix ⟨69, by decide⟩ ⟨54, by decide⟩ p hp j hj hq fz1_69_54 fz2_69_54
  · exact match_zero_fix ⟨70, by decide⟩ ⟨54, by decide⟩ p hp j hj hq fz1_70_54 fz2_70_54
  · exact match_zero_fix ⟨71, by decide⟩ ⟨54, by decide⟩ p hp j hj hq fz1_71_54 fz2_71_54
  · exact match_zero_fix ⟨72, by decide⟩ ⟨54, by decide⟩ p hp j hj hq fz1_72_54 fz2_72_54
  · exact match_zero_fix ⟨73, by decide⟩ ⟨54, by decide⟩ p hp j hj hq fz1_73_54 fz2_73_54
  · exact match_zero_fix ⟨74, by decide⟩ ⟨54, by decide⟩ p hp j hj hq fz1_74_54 fz2_74_54
  · exact match_zero_fix ⟨75, by decide⟩ ⟨54, by decide⟩ p hp j hj hq fz1_75_54 fz2_75_54
  · exact match_zero_fix ⟨76, by decide⟩ ⟨54, by decide⟩ p hp j hj hq fz1_76_54 fz2_76_54
  · exact match_zero_fix ⟨77, by decide⟩ ⟨54, by decide⟩ p hp j hj hq fz1_77_54 fz2_77_54
  · exact match_zero_fix ⟨78, by decide⟩ ⟨54, by decide⟩ p hp j hj hq fz1_78_54 fz2_78_54
  · exact match_zero_fix ⟨79, by decide⟩ ⟨54, by decide⟩ p hp j hj hq fz1_79_54 fz2_79_54
  · exact match_zero_fix ⟨80, by decide⟩ ⟨54, by decide⟩ p hp j hj hq fz1_80_54 fz2_80_54
  · exact match_zero_fix ⟨81, by decide⟩ ⟨54, by decide⟩ p hp j hj hq fz1_81_54 fz2_81_54
  · exact match_zero_fix ⟨82, by decide⟩ ⟨54, by decide⟩ p hp j hj hq fz1_82_54 fz2_82_54
  · exact match_zero_fix ⟨83, by decide⟩ ⟨54, by decide⟩ p hp j hj hq fz1_83_54 fz2_83_54
  · exact match_zero_fix ⟨84, by decide⟩ ⟨54, by decide⟩ p hp j hj hq fz1_84_54 fz2_84_54
  · exact pair_85_54 p hp hrep j hj hq
  · exact pair_86_54 p hp hrep j hj hq
  · exact pair_87_54 p hp hrep j hj hq
  · exact pair_88_54 p hp hrep j hj hq
  · exact pair_89_54 p hp hrep j hj hq
  · exact match_zero_fix ⟨90, by decide⟩ ⟨54, by decide⟩ p hp j hj hq fz1_90_54 fz2_90_54
  · exact match_zero_fix ⟨91, by decide⟩ ⟨54, by decide⟩ p hp j hj hq fz1_91_54 fz2_91_54
  · exact match_zero_fix ⟨92, by decide⟩ ⟨54, by decide⟩ p hp j hj hq fz1_92_54 fz2_92_54
  · exact match_zero_fix ⟨93, by decide⟩ ⟨54, by decide⟩ p hp j hj hq fz1_93_54 fz2_93_54
  · exact match_zero_fix ⟨94, by decide⟩ ⟨54, by decide⟩ p hp j hj hq fz1_94_54 fz2_94_54
  · exact match_zero_fix ⟨95, by decide⟩ ⟨54, by decide⟩ p hp j hj hq fz1_95_54 fz2_95_54
  · exact match_zero_fix ⟨96, by decide⟩ ⟨54, by decide⟩ p hp j hj hq fz1_96_54 fz2_96_54
  · exact match_zero_fix ⟨97, by decide⟩ ⟨54, by decide⟩ p hp j hj hq fz1_97_54 fz2_97_54
  · exact match_zero_fix ⟨98, by decide⟩ ⟨54, by decide⟩ p hp j hj hq fz1_98_54 fz2_98_54
  · exact match_zero_fix ⟨99, by decide⟩ ⟨54, by decide⟩ p hp j hj hq fz1_99_54 fz2_99_54
  · exact match_zero_fix ⟨100, by decide⟩ ⟨54, by decide⟩ p hp j hj hq fz1_100_54 fz2_100_54
  · exact match_zero_fix ⟨101, by decide⟩ ⟨54, by decide⟩ p hp j hj hq fz1_101_54 fz2_101_54
  · exact match_zero_fix ⟨102, by decide⟩ ⟨54, by decide⟩ p hp j hj hq fz1_102_54 fz2_102_54
  · exact match_zero_fix ⟨103, by decide⟩ ⟨54, by decide⟩ p hp j hj hq fz1_103_54 fz2_103_54
  · exact match_zero_fix ⟨104, by decide⟩ ⟨54, by decide⟩ p hp j hj hq fz1_104_54 fz2_104_54
  · exact match_zero_fix ⟨105, by decide⟩ ⟨54, by decide⟩ p hp j hj hq fz1_105_54 fz2_105_54
  · exact match_zero_fix ⟨106, by decide⟩ ⟨54, by decide⟩ p hp j hj hq fz1_106_54 fz2_106_54
  · exact match_zero_fix ⟨107, by decide⟩ ⟨54, by decide⟩ p hp j hj hq fz1_107_54 fz2_107_54
  · exact match_zero_fix ⟨108, by decide⟩ ⟨54, by decide⟩ p hp j hj hq fz1_108_54 fz2_108_54
  · exact match_zero_fix ⟨109, by decide⟩ ⟨54, by decide⟩ p hp j hj hq fz1_109_54 fz2_109_54
  · exact match_zero_fix ⟨110, by decide⟩ ⟨54, by decide⟩ p hp j hj hq fz1_110_54 fz2_110_54
  · exact match_zero_fix ⟨111, by decide⟩ ⟨54, by decide⟩ p hp j hj hq fz1_111_54 fz2_111_54
  · exact match_zero_fix ⟨112, by decide⟩ ⟨54, by decide⟩ p hp j hj hq fz1_112_54 fz2_112_54
  · exact match_zero_fix ⟨113, by decide⟩ ⟨54, by decide⟩ p hp j hj hq fz1_113_54 fz2_113_54
  · exact match_zero_fix ⟨114, by decide⟩ ⟨54, by decide⟩ p hp j hj hq fz1_114_54 fz2_114_54
  · exact pair_115_54 p hp hrep j hj hq
  · exact match_zero_fix ⟨116, by decide⟩ ⟨54, by decide⟩ p hp j hj hq fz1_116_54 fz2_116_54
  · exact match_zero_fix ⟨117, by decide⟩ ⟨54, by decide⟩ p hp j hj hq fz1_117_54 fz2_117_54
  · exact match_zero_fix ⟨118, by decide⟩ ⟨54, by decide⟩ p hp j hj hq fz1_118_54 fz2_118_54
  · exact match_zero_fix ⟨119, by decide⟩ ⟨54, by decide⟩ p hp j hj hq fz1_119_54 fz2_119_54
  · exact match_zero_fix ⟨120, by decide⟩ ⟨54, by decide⟩ p hp j hj hq fz1_120_54 fz2_120_54
  · exact match_zero_fix ⟨121, by decide⟩ ⟨54, by decide⟩ p hp j hj hq fz1_121_54 fz2_121_54
  · exact match_zero_fix ⟨122, by decide⟩ ⟨54, by decide⟩ p hp j hj hq fz1_122_54 fz2_122_54
  · exact match_zero_fix ⟨123, by decide⟩ ⟨54, by decide⟩ p hp j hj hq fz1_123_54 fz2_123_54
  · exact match_zero_fix ⟨124, by decide⟩ ⟨54, by decide⟩ p hp j hj hq fz1_124_54 fz2_124_54
  · exact match_zero_fix ⟨125, by decide⟩ ⟨54, by decide⟩ p hp j hj hq fz1_125_54 fz2_125_54
  · exact match_zero_fix ⟨126, by decide⟩ ⟨54, by decide⟩ p hp j hj hq fz1_126_54 fz2_126_54
  · exact match_zero_fix ⟨127, by decide⟩ ⟨54, by decide⟩ p hp j hj hq fz1_127_54 fz2_127_54
  · exact match_zero_fix ⟨128, by decide⟩ ⟨54, by decide⟩ p hp j hj hq fz1_128_54 fz2_128_54
  · exact match_zero_fix ⟨129, by decide⟩ ⟨54, by decide⟩ p hp j hj hq fz1_129_54 fz2_129_54
  · exact match_zero_fix ⟨130, by decide⟩ ⟨54, by decide⟩ p hp j hj hq fz1_130_54 fz2_130_54
  · exact match_zero_fix ⟨131, by decide⟩ ⟨54, by decide⟩ p hp j hj hq fz1_131_54 fz2_131_54
  · exact match_zero_fix ⟨132, by decide⟩ ⟨54, by decide⟩ p hp j hj hq fz1_132_54 fz2_132_54
  · exact match_zero_fix ⟨133, by decide⟩ ⟨54, by decide⟩ p hp j hj hq fz1_133_54 fz2_133_54
  · exact match_zero_fix ⟨134, by decide⟩ ⟨54, by decide⟩ p hp j hj hq fz1_134_54 fz2_134_54
  · exact match_zero_fix ⟨135, by decide⟩ ⟨54, by decide⟩ p hp j hj hq fz1_135_54 fz2_135_54
  · exact match_zero_fix ⟨136, by decide⟩ ⟨54, by decide⟩ p hp j hj hq fz1_136_54 fz2_136_54
  · exact match_zero_fix ⟨137, by decide⟩ ⟨54, by decide⟩ p hp j hj hq fz1_137_54 fz2_137_54
  · exact match_zero_fix ⟨138, by decide⟩ ⟨54, by decide⟩ p hp j hj hq fz1_138_54 fz2_138_54
  · exact match_zero_fix ⟨139, by decide⟩ ⟨54, by decide⟩ p hp j hj hq fz1_139_54 fz2_139_54
  · exact match_zero_fix ⟨140, by decide⟩ ⟨54, by decide⟩ p hp j hj hq fz1_140_54 fz2_140_54
  · exact pair_141_54 p hp hrep j hj hq
  · exact pair_142_54 p hp hrep j hj hq
  · exact pair_143_54 p hp hrep j hj hq
  · exact pair_144_54 p hp hrep j hj hq
  · exact pair_145_54 p hp hrep j hj hq
  · exact pair_146_54 p hp hrep j hj hq
  · exact pair_147_54 p hp hrep j hj hq

theorem master_55 (p : Nat) (hp : p < (Q2.transData.getD 55 []).length)
    (hrep : (Q2.cosetIsRep.getD 55 []).getD p false = true)
    (rK : Fin 148) (j : Nat) (hj : j < (repChars.getD rK.val []).length)
    (hq : (normIsRep.getD rK.val []).getD j false = true) :
    species (Q2.reps (⟨55, by decide⟩ : Fin 148)) (colE2 ⟨55, by decide⟩ p hp)
        (rowE2 rK j hj hq)
      = species (reps (⟨55, by decide⟩ : Fin 148))
        (colE1 ⟨55, by decide⟩ p (transLenTr ⟨55, by decide⟩ p hp)) (rowE1 rK j hj) := by
  rcases rK with ⟨nK, hnK⟩; interval_cases nK
  · exact match_zero_len ⟨0, by decide⟩ ⟨55, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨1, by decide⟩ ⟨55, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨2, by decide⟩ ⟨55, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨3, by decide⟩ ⟨55, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨4, by decide⟩ ⟨55, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨5, by decide⟩ ⟨55, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨6, by decide⟩ ⟨55, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨7, by decide⟩ ⟨55, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨8, by decide⟩ ⟨55, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨9, by decide⟩ ⟨55, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨10, by decide⟩ ⟨55, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨11, by decide⟩ ⟨55, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨12, by decide⟩ ⟨55, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨13, by decide⟩ ⟨55, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨14, by decide⟩ ⟨55, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨15, by decide⟩ ⟨55, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨16, by decide⟩ ⟨55, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨17, by decide⟩ ⟨55, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨18, by decide⟩ ⟨55, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨19, by decide⟩ ⟨55, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨20, by decide⟩ ⟨55, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨21, by decide⟩ ⟨55, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨22, by decide⟩ ⟨55, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨23, by decide⟩ ⟨55, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨24, by decide⟩ ⟨55, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨25, by decide⟩ ⟨55, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨26, by decide⟩ ⟨55, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨27, by decide⟩ ⟨55, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨28, by decide⟩ ⟨55, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨29, by decide⟩ ⟨55, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨30, by decide⟩ ⟨55, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨31, by decide⟩ ⟨55, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨32, by decide⟩ ⟨55, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨33, by decide⟩ ⟨55, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨34, by decide⟩ ⟨55, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨35, by decide⟩ ⟨55, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨36, by decide⟩ ⟨55, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨37, by decide⟩ ⟨55, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨38, by decide⟩ ⟨55, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨39, by decide⟩ ⟨55, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨40, by decide⟩ ⟨55, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨41, by decide⟩ ⟨55, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨42, by decide⟩ ⟨55, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨43, by decide⟩ ⟨55, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨44, by decide⟩ ⟨55, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨45, by decide⟩ ⟨55, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨46, by decide⟩ ⟨55, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨47, by decide⟩ ⟨55, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨48, by decide⟩ ⟨55, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨49, by decide⟩ ⟨55, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨50, by decide⟩ ⟨55, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨51, by decide⟩ ⟨55, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨52, by decide⟩ ⟨55, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨53, by decide⟩ ⟨55, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨54, by decide⟩ ⟨55, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact pair_55_55 p hp hrep j hj hq
  · exact match_zero_fix ⟨56, by decide⟩ ⟨55, by decide⟩ p hp j hj hq fz1_56_55 fz2_56_55
  · exact match_zero_fix ⟨57, by decide⟩ ⟨55, by decide⟩ p hp j hj hq fz1_57_55 fz2_57_55
  · exact match_zero_fix ⟨58, by decide⟩ ⟨55, by decide⟩ p hp j hj hq fz1_58_55 fz2_58_55
  · exact match_zero_fix ⟨59, by decide⟩ ⟨55, by decide⟩ p hp j hj hq fz1_59_55 fz2_59_55
  · exact match_zero_fix ⟨60, by decide⟩ ⟨55, by decide⟩ p hp j hj hq fz1_60_55 fz2_60_55
  · exact match_zero_fix ⟨61, by decide⟩ ⟨55, by decide⟩ p hp j hj hq fz1_61_55 fz2_61_55
  · exact match_zero_fix ⟨62, by decide⟩ ⟨55, by decide⟩ p hp j hj hq fz1_62_55 fz2_62_55
  · exact match_zero_fix ⟨63, by decide⟩ ⟨55, by decide⟩ p hp j hj hq fz1_63_55 fz2_63_55
  · exact match_zero_fix ⟨64, by decide⟩ ⟨55, by decide⟩ p hp j hj hq fz1_64_55 fz2_64_55
  · exact match_zero_fix ⟨65, by decide⟩ ⟨55, by decide⟩ p hp j hj hq fz1_65_55 fz2_65_55
  · exact match_zero_fix ⟨66, by decide⟩ ⟨55, by decide⟩ p hp j hj hq fz1_66_55 fz2_66_55
  · exact match_zero_fix ⟨67, by decide⟩ ⟨55, by decide⟩ p hp j hj hq fz1_67_55 fz2_67_55
  · exact match_zero_fix ⟨68, by decide⟩ ⟨55, by decide⟩ p hp j hj hq fz1_68_55 fz2_68_55
  · exact match_zero_fix ⟨69, by decide⟩ ⟨55, by decide⟩ p hp j hj hq fz1_69_55 fz2_69_55
  · exact match_zero_fix ⟨70, by decide⟩ ⟨55, by decide⟩ p hp j hj hq fz1_70_55 fz2_70_55
  · exact match_zero_fix ⟨71, by decide⟩ ⟨55, by decide⟩ p hp j hj hq fz1_71_55 fz2_71_55
  · exact match_zero_fix ⟨72, by decide⟩ ⟨55, by decide⟩ p hp j hj hq fz1_72_55 fz2_72_55
  · exact match_zero_fix ⟨73, by decide⟩ ⟨55, by decide⟩ p hp j hj hq fz1_73_55 fz2_73_55
  · exact match_zero_fix ⟨74, by decide⟩ ⟨55, by decide⟩ p hp j hj hq fz1_74_55 fz2_74_55
  · exact match_zero_fix ⟨75, by decide⟩ ⟨55, by decide⟩ p hp j hj hq fz1_75_55 fz2_75_55
  · exact match_zero_fix ⟨76, by decide⟩ ⟨55, by decide⟩ p hp j hj hq fz1_76_55 fz2_76_55
  · exact match_zero_fix ⟨77, by decide⟩ ⟨55, by decide⟩ p hp j hj hq fz1_77_55 fz2_77_55
  · exact match_zero_fix ⟨78, by decide⟩ ⟨55, by decide⟩ p hp j hj hq fz1_78_55 fz2_78_55
  · exact match_zero_fix ⟨79, by decide⟩ ⟨55, by decide⟩ p hp j hj hq fz1_79_55 fz2_79_55
  · exact match_zero_fix ⟨80, by decide⟩ ⟨55, by decide⟩ p hp j hj hq fz1_80_55 fz2_80_55
  · exact match_zero_fix ⟨81, by decide⟩ ⟨55, by decide⟩ p hp j hj hq fz1_81_55 fz2_81_55
  · exact match_zero_fix ⟨82, by decide⟩ ⟨55, by decide⟩ p hp j hj hq fz1_82_55 fz2_82_55
  · exact match_zero_fix ⟨83, by decide⟩ ⟨55, by decide⟩ p hp j hj hq fz1_83_55 fz2_83_55
  · exact match_zero_fix ⟨84, by decide⟩ ⟨55, by decide⟩ p hp j hj hq fz1_84_55 fz2_84_55
  · exact match_zero_fix ⟨85, by decide⟩ ⟨55, by decide⟩ p hp j hj hq fz1_85_55 fz2_85_55
  · exact match_zero_fix ⟨86, by decide⟩ ⟨55, by decide⟩ p hp j hj hq fz1_86_55 fz2_86_55
  · exact match_zero_fix ⟨87, by decide⟩ ⟨55, by decide⟩ p hp j hj hq fz1_87_55 fz2_87_55
  · exact match_zero_fix ⟨88, by decide⟩ ⟨55, by decide⟩ p hp j hj hq fz1_88_55 fz2_88_55
  · exact match_zero_fix ⟨89, by decide⟩ ⟨55, by decide⟩ p hp j hj hq fz1_89_55 fz2_89_55
  · exact match_zero_fix ⟨90, by decide⟩ ⟨55, by decide⟩ p hp j hj hq fz1_90_55 fz2_90_55
  · exact match_zero_fix ⟨91, by decide⟩ ⟨55, by decide⟩ p hp j hj hq fz1_91_55 fz2_91_55
  · exact match_zero_fix ⟨92, by decide⟩ ⟨55, by decide⟩ p hp j hj hq fz1_92_55 fz2_92_55
  · exact match_zero_fix ⟨93, by decide⟩ ⟨55, by decide⟩ p hp j hj hq fz1_93_55 fz2_93_55
  · exact match_zero_fix ⟨94, by decide⟩ ⟨55, by decide⟩ p hp j hj hq fz1_94_55 fz2_94_55
  · exact match_zero_fix ⟨95, by decide⟩ ⟨55, by decide⟩ p hp j hj hq fz1_95_55 fz2_95_55
  · exact match_zero_fix ⟨96, by decide⟩ ⟨55, by decide⟩ p hp j hj hq fz1_96_55 fz2_96_55
  · exact match_zero_fix ⟨97, by decide⟩ ⟨55, by decide⟩ p hp j hj hq fz1_97_55 fz2_97_55
  · exact match_zero_fix ⟨98, by decide⟩ ⟨55, by decide⟩ p hp j hj hq fz1_98_55 fz2_98_55
  · exact match_zero_fix ⟨99, by decide⟩ ⟨55, by decide⟩ p hp j hj hq fz1_99_55 fz2_99_55
  · exact match_zero_fix ⟨100, by decide⟩ ⟨55, by decide⟩ p hp j hj hq fz1_100_55 fz2_100_55
  · exact match_zero_fix ⟨101, by decide⟩ ⟨55, by decide⟩ p hp j hj hq fz1_101_55 fz2_101_55
  · exact match_zero_fix ⟨102, by decide⟩ ⟨55, by decide⟩ p hp j hj hq fz1_102_55 fz2_102_55
  · exact match_zero_fix ⟨103, by decide⟩ ⟨55, by decide⟩ p hp j hj hq fz1_103_55 fz2_103_55
  · exact match_zero_fix ⟨104, by decide⟩ ⟨55, by decide⟩ p hp j hj hq fz1_104_55 fz2_104_55
  · exact match_zero_fix ⟨105, by decide⟩ ⟨55, by decide⟩ p hp j hj hq fz1_105_55 fz2_105_55
  · exact match_zero_fix ⟨106, by decide⟩ ⟨55, by decide⟩ p hp j hj hq fz1_106_55 fz2_106_55
  · exact match_zero_fix ⟨107, by decide⟩ ⟨55, by decide⟩ p hp j hj hq fz1_107_55 fz2_107_55
  · exact match_zero_fix ⟨108, by decide⟩ ⟨55, by decide⟩ p hp j hj hq fz1_108_55 fz2_108_55
  · exact match_zero_fix ⟨109, by decide⟩ ⟨55, by decide⟩ p hp j hj hq fz1_109_55 fz2_109_55
  · exact match_zero_fix ⟨110, by decide⟩ ⟨55, by decide⟩ p hp j hj hq fz1_110_55 fz2_110_55
  · exact match_zero_fix ⟨111, by decide⟩ ⟨55, by decide⟩ p hp j hj hq fz1_111_55 fz2_111_55
  · exact match_zero_fix ⟨112, by decide⟩ ⟨55, by decide⟩ p hp j hj hq fz1_112_55 fz2_112_55
  · exact match_zero_fix ⟨113, by decide⟩ ⟨55, by decide⟩ p hp j hj hq fz1_113_55 fz2_113_55
  · exact match_zero_fix ⟨114, by decide⟩ ⟨55, by decide⟩ p hp j hj hq fz1_114_55 fz2_114_55
  · exact match_zero_fix ⟨115, by decide⟩ ⟨55, by decide⟩ p hp j hj hq fz1_115_55 fz2_115_55
  · exact pair_116_55 p hp hrep j hj hq
  · exact match_zero_fix ⟨117, by decide⟩ ⟨55, by decide⟩ p hp j hj hq fz1_117_55 fz2_117_55
  · exact match_zero_fix ⟨118, by decide⟩ ⟨55, by decide⟩ p hp j hj hq fz1_118_55 fz2_118_55
  · exact match_zero_fix ⟨119, by decide⟩ ⟨55, by decide⟩ p hp j hj hq fz1_119_55 fz2_119_55
  · exact match_zero_fix ⟨120, by decide⟩ ⟨55, by decide⟩ p hp j hj hq fz1_120_55 fz2_120_55
  · exact match_zero_fix ⟨121, by decide⟩ ⟨55, by decide⟩ p hp j hj hq fz1_121_55 fz2_121_55
  · exact match_zero_fix ⟨122, by decide⟩ ⟨55, by decide⟩ p hp j hj hq fz1_122_55 fz2_122_55
  · exact match_zero_fix ⟨123, by decide⟩ ⟨55, by decide⟩ p hp j hj hq fz1_123_55 fz2_123_55
  · exact match_zero_fix ⟨124, by decide⟩ ⟨55, by decide⟩ p hp j hj hq fz1_124_55 fz2_124_55
  · exact match_zero_fix ⟨125, by decide⟩ ⟨55, by decide⟩ p hp j hj hq fz1_125_55 fz2_125_55
  · exact match_zero_fix ⟨126, by decide⟩ ⟨55, by decide⟩ p hp j hj hq fz1_126_55 fz2_126_55
  · exact match_zero_fix ⟨127, by decide⟩ ⟨55, by decide⟩ p hp j hj hq fz1_127_55 fz2_127_55
  · exact match_zero_fix ⟨128, by decide⟩ ⟨55, by decide⟩ p hp j hj hq fz1_128_55 fz2_128_55
  · exact match_zero_fix ⟨129, by decide⟩ ⟨55, by decide⟩ p hp j hj hq fz1_129_55 fz2_129_55
  · exact match_zero_fix ⟨130, by decide⟩ ⟨55, by decide⟩ p hp j hj hq fz1_130_55 fz2_130_55
  · exact match_zero_fix ⟨131, by decide⟩ ⟨55, by decide⟩ p hp j hj hq fz1_131_55 fz2_131_55
  · exact match_zero_fix ⟨132, by decide⟩ ⟨55, by decide⟩ p hp j hj hq fz1_132_55 fz2_132_55
  · exact match_zero_fix ⟨133, by decide⟩ ⟨55, by decide⟩ p hp j hj hq fz1_133_55 fz2_133_55
  · exact match_zero_fix ⟨134, by decide⟩ ⟨55, by decide⟩ p hp j hj hq fz1_134_55 fz2_134_55
  · exact match_zero_fix ⟨135, by decide⟩ ⟨55, by decide⟩ p hp j hj hq fz1_135_55 fz2_135_55
  · exact match_zero_fix ⟨136, by decide⟩ ⟨55, by decide⟩ p hp j hj hq fz1_136_55 fz2_136_55
  · exact match_zero_fix ⟨137, by decide⟩ ⟨55, by decide⟩ p hp j hj hq fz1_137_55 fz2_137_55
  · exact match_zero_fix ⟨138, by decide⟩ ⟨55, by decide⟩ p hp j hj hq fz1_138_55 fz2_138_55
  · exact match_zero_fix ⟨139, by decide⟩ ⟨55, by decide⟩ p hp j hj hq fz1_139_55 fz2_139_55
  · exact match_zero_fix ⟨140, by decide⟩ ⟨55, by decide⟩ p hp j hj hq fz1_140_55 fz2_140_55
  · exact match_zero_fix ⟨141, by decide⟩ ⟨55, by decide⟩ p hp j hj hq fz1_141_55 fz2_141_55
  · exact match_zero_fix ⟨142, by decide⟩ ⟨55, by decide⟩ p hp j hj hq fz1_142_55 fz2_142_55
  · exact match_zero_fix ⟨143, by decide⟩ ⟨55, by decide⟩ p hp j hj hq fz1_143_55 fz2_143_55
  · exact match_zero_fix ⟨144, by decide⟩ ⟨55, by decide⟩ p hp j hj hq fz1_144_55 fz2_144_55
  · exact match_zero_fix ⟨145, by decide⟩ ⟨55, by decide⟩ p hp j hj hq fz1_145_55 fz2_145_55
  · exact match_zero_fix ⟨146, by decide⟩ ⟨55, by decide⟩ p hp j hj hq fz1_146_55 fz2_146_55
  · exact pair_147_55 p hp hrep j hj hq

end LeanDring.P5Presentation
