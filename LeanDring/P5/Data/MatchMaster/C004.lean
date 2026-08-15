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
import LeanDring.P5.Data.MatchPair.C004
import LeanDring.P5.Data.MatchPair.C005
import LeanDring.P5.Data.MatchPair.C006
import LeanDring.P5.Data.MatchPair.C007
import LeanDring.P5.Data.MatchPair.C008
import LeanDring.P5.Data.MatchPair.C009
import LeanDring.P5.Data.MatchPair.C010

/-! # Stage-5 per-column-class master theorems, chunk 3 (auto-emitted).  -/

namespace LeanDring.P5Presentation

open MulAction Finset LeanDring.DRing LeanDring.MonGSet

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.style.longLine false

theorem master_24 (p : Nat) (hp : p < (Q2.transData.getD 24 []).length)
    (hrep : (Q2.cosetIsRep.getD 24 []).getD p false = true)
    (rK : Fin 148) (j : Nat) (hj : j < (repChars.getD rK.val []).length)
    (hq : (normIsRep.getD rK.val []).getD j false = true) :
    species (Q2.reps (⟨24, by decide⟩ : Fin 148)) (colE2 ⟨24, by decide⟩ p hp)
        (rowE2 rK j hj hq)
      = species (reps (⟨24, by decide⟩ : Fin 148))
        (colE1 ⟨24, by decide⟩ p (transLenTr ⟨24, by decide⟩ p hp)) (rowE1 rK j hj) := by
  rcases rK with ⟨nK, hnK⟩; interval_cases nK
  · exact match_zero_len ⟨0, by decide⟩ ⟨24, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨1, by decide⟩ ⟨24, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨2, by decide⟩ ⟨24, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨3, by decide⟩ ⟨24, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨4, by decide⟩ ⟨24, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨5, by decide⟩ ⟨24, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨6, by decide⟩ ⟨24, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨7, by decide⟩ ⟨24, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨8, by decide⟩ ⟨24, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨9, by decide⟩ ⟨24, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨10, by decide⟩ ⟨24, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨11, by decide⟩ ⟨24, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨12, by decide⟩ ⟨24, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_fix ⟨13, by decide⟩ ⟨24, by decide⟩ p hp j hj hq fz1_13_24 fz2_13_24
  · exact match_zero_fix ⟨14, by decide⟩ ⟨24, by decide⟩ p hp j hj hq fz1_14_24 fz2_14_24
  · exact match_zero_fix ⟨15, by decide⟩ ⟨24, by decide⟩ p hp j hj hq fz1_15_24 fz2_15_24
  · exact match_zero_fix ⟨16, by decide⟩ ⟨24, by decide⟩ p hp j hj hq fz1_16_24 fz2_16_24
  · exact match_zero_fix ⟨17, by decide⟩ ⟨24, by decide⟩ p hp j hj hq fz1_17_24 fz2_17_24
  · exact match_zero_fix ⟨18, by decide⟩ ⟨24, by decide⟩ p hp j hj hq fz1_18_24 fz2_18_24
  · exact match_zero_fix ⟨19, by decide⟩ ⟨24, by decide⟩ p hp j hj hq fz1_19_24 fz2_19_24
  · exact match_zero_fix ⟨20, by decide⟩ ⟨24, by decide⟩ p hp j hj hq fz1_20_24 fz2_20_24
  · exact match_zero_fix ⟨21, by decide⟩ ⟨24, by decide⟩ p hp j hj hq fz1_21_24 fz2_21_24
  · exact match_zero_fix ⟨22, by decide⟩ ⟨24, by decide⟩ p hp j hj hq fz1_22_24 fz2_22_24
  · exact match_zero_fix ⟨23, by decide⟩ ⟨24, by decide⟩ p hp j hj hq fz1_23_24 fz2_23_24
  · exact pair_24_24 p hp hrep j hj hq
  · exact match_zero_fix ⟨25, by decide⟩ ⟨24, by decide⟩ p hp j hj hq fz1_25_24 fz2_25_24
  · exact match_zero_fix ⟨26, by decide⟩ ⟨24, by decide⟩ p hp j hj hq fz1_26_24 fz2_26_24
  · exact match_zero_fix ⟨27, by decide⟩ ⟨24, by decide⟩ p hp j hj hq fz1_27_24 fz2_27_24
  · exact match_zero_fix ⟨28, by decide⟩ ⟨24, by decide⟩ p hp j hj hq fz1_28_24 fz2_28_24
  · exact match_zero_fix ⟨29, by decide⟩ ⟨24, by decide⟩ p hp j hj hq fz1_29_24 fz2_29_24
  · exact match_zero_fix ⟨30, by decide⟩ ⟨24, by decide⟩ p hp j hj hq fz1_30_24 fz2_30_24
  · exact match_zero_fix ⟨31, by decide⟩ ⟨24, by decide⟩ p hp j hj hq fz1_31_24 fz2_31_24
  · exact match_zero_fix ⟨32, by decide⟩ ⟨24, by decide⟩ p hp j hj hq fz1_32_24 fz2_32_24
  · exact match_zero_fix ⟨33, by decide⟩ ⟨24, by decide⟩ p hp j hj hq fz1_33_24 fz2_33_24
  · exact match_zero_fix ⟨34, by decide⟩ ⟨24, by decide⟩ p hp j hj hq fz1_34_24 fz2_34_24
  · exact match_zero_fix ⟨35, by decide⟩ ⟨24, by decide⟩ p hp j hj hq fz1_35_24 fz2_35_24
  · exact match_zero_fix ⟨36, by decide⟩ ⟨24, by decide⟩ p hp j hj hq fz1_36_24 fz2_36_24
  · exact match_zero_fix ⟨37, by decide⟩ ⟨24, by decide⟩ p hp j hj hq fz1_37_24 fz2_37_24
  · exact match_zero_fix ⟨38, by decide⟩ ⟨24, by decide⟩ p hp j hj hq fz1_38_24 fz2_38_24
  · exact match_zero_fix ⟨39, by decide⟩ ⟨24, by decide⟩ p hp j hj hq fz1_39_24 fz2_39_24
  · exact match_zero_fix ⟨40, by decide⟩ ⟨24, by decide⟩ p hp j hj hq fz1_40_24 fz2_40_24
  · exact match_zero_fix ⟨41, by decide⟩ ⟨24, by decide⟩ p hp j hj hq fz1_41_24 fz2_41_24
  · exact match_zero_fix ⟨42, by decide⟩ ⟨24, by decide⟩ p hp j hj hq fz1_42_24 fz2_42_24
  · exact match_zero_fix ⟨43, by decide⟩ ⟨24, by decide⟩ p hp j hj hq fz1_43_24 fz2_43_24
  · exact match_zero_fix ⟨44, by decide⟩ ⟨24, by decide⟩ p hp j hj hq fz1_44_24 fz2_44_24
  · exact match_zero_fix ⟨45, by decide⟩ ⟨24, by decide⟩ p hp j hj hq fz1_45_24 fz2_45_24
  · exact match_zero_fix ⟨46, by decide⟩ ⟨24, by decide⟩ p hp j hj hq fz1_46_24 fz2_46_24
  · exact match_zero_fix ⟨47, by decide⟩ ⟨24, by decide⟩ p hp j hj hq fz1_47_24 fz2_47_24
  · exact match_zero_fix ⟨48, by decide⟩ ⟨24, by decide⟩ p hp j hj hq fz1_48_24 fz2_48_24
  · exact match_zero_fix ⟨49, by decide⟩ ⟨24, by decide⟩ p hp j hj hq fz1_49_24 fz2_49_24
  · exact match_zero_fix ⟨50, by decide⟩ ⟨24, by decide⟩ p hp j hj hq fz1_50_24 fz2_50_24
  · exact match_zero_fix ⟨51, by decide⟩ ⟨24, by decide⟩ p hp j hj hq fz1_51_24 fz2_51_24
  · exact match_zero_fix ⟨52, by decide⟩ ⟨24, by decide⟩ p hp j hj hq fz1_52_24 fz2_52_24
  · exact match_zero_fix ⟨53, by decide⟩ ⟨24, by decide⟩ p hp j hj hq fz1_53_24 fz2_53_24
  · exact match_zero_fix ⟨54, by decide⟩ ⟨24, by decide⟩ p hp j hj hq fz1_54_24 fz2_54_24
  · exact match_zero_fix ⟨55, by decide⟩ ⟨24, by decide⟩ p hp j hj hq fz1_55_24 fz2_55_24
  · exact match_zero_fix ⟨56, by decide⟩ ⟨24, by decide⟩ p hp j hj hq fz1_56_24 fz2_56_24
  · exact match_zero_fix ⟨57, by decide⟩ ⟨24, by decide⟩ p hp j hj hq fz1_57_24 fz2_57_24
  · exact pair_58_24 p hp hrep j hj hq
  · exact match_zero_fix ⟨59, by decide⟩ ⟨24, by decide⟩ p hp j hj hq fz1_59_24 fz2_59_24
  · exact match_zero_fix ⟨60, by decide⟩ ⟨24, by decide⟩ p hp j hj hq fz1_60_24 fz2_60_24
  · exact match_zero_fix ⟨61, by decide⟩ ⟨24, by decide⟩ p hp j hj hq fz1_61_24 fz2_61_24
  · exact match_zero_fix ⟨62, by decide⟩ ⟨24, by decide⟩ p hp j hj hq fz1_62_24 fz2_62_24
  · exact pair_63_24 p hp hrep j hj hq
  · exact match_zero_fix ⟨64, by decide⟩ ⟨24, by decide⟩ p hp j hj hq fz1_64_24 fz2_64_24
  · exact match_zero_fix ⟨65, by decide⟩ ⟨24, by decide⟩ p hp j hj hq fz1_65_24 fz2_65_24
  · exact match_zero_fix ⟨66, by decide⟩ ⟨24, by decide⟩ p hp j hj hq fz1_66_24 fz2_66_24
  · exact match_zero_fix ⟨67, by decide⟩ ⟨24, by decide⟩ p hp j hj hq fz1_67_24 fz2_67_24
  · exact pair_68_24 p hp hrep j hj hq
  · exact match_zero_fix ⟨69, by decide⟩ ⟨24, by decide⟩ p hp j hj hq fz1_69_24 fz2_69_24
  · exact match_zero_fix ⟨70, by decide⟩ ⟨24, by decide⟩ p hp j hj hq fz1_70_24 fz2_70_24
  · exact match_zero_fix ⟨71, by decide⟩ ⟨24, by decide⟩ p hp j hj hq fz1_71_24 fz2_71_24
  · exact match_zero_fix ⟨72, by decide⟩ ⟨24, by decide⟩ p hp j hj hq fz1_72_24 fz2_72_24
  · exact pair_73_24 p hp hrep j hj hq
  · exact match_zero_fix ⟨74, by decide⟩ ⟨24, by decide⟩ p hp j hj hq fz1_74_24 fz2_74_24
  · exact match_zero_fix ⟨75, by decide⟩ ⟨24, by decide⟩ p hp j hj hq fz1_75_24 fz2_75_24
  · exact match_zero_fix ⟨76, by decide⟩ ⟨24, by decide⟩ p hp j hj hq fz1_76_24 fz2_76_24
  · exact match_zero_fix ⟨77, by decide⟩ ⟨24, by decide⟩ p hp j hj hq fz1_77_24 fz2_77_24
  · exact pair_78_24 p hp hrep j hj hq
  · exact match_zero_fix ⟨79, by decide⟩ ⟨24, by decide⟩ p hp j hj hq fz1_79_24 fz2_79_24
  · exact pair_80_24 p hp hrep j hj hq
  · exact match_zero_fix ⟨81, by decide⟩ ⟨24, by decide⟩ p hp j hj hq fz1_81_24 fz2_81_24
  · exact match_zero_fix ⟨82, by decide⟩ ⟨24, by decide⟩ p hp j hj hq fz1_82_24 fz2_82_24
  · exact match_zero_fix ⟨83, by decide⟩ ⟨24, by decide⟩ p hp j hj hq fz1_83_24 fz2_83_24
  · exact match_zero_fix ⟨84, by decide⟩ ⟨24, by decide⟩ p hp j hj hq fz1_84_24 fz2_84_24
  · exact match_zero_fix ⟨85, by decide⟩ ⟨24, by decide⟩ p hp j hj hq fz1_85_24 fz2_85_24
  · exact match_zero_fix ⟨86, by decide⟩ ⟨24, by decide⟩ p hp j hj hq fz1_86_24 fz2_86_24
  · exact match_zero_fix ⟨87, by decide⟩ ⟨24, by decide⟩ p hp j hj hq fz1_87_24 fz2_87_24
  · exact pair_88_24 p hp hrep j hj hq
  · exact match_zero_fix ⟨89, by decide⟩ ⟨24, by decide⟩ p hp j hj hq fz1_89_24 fz2_89_24
  · exact match_zero_fix ⟨90, by decide⟩ ⟨24, by decide⟩ p hp j hj hq fz1_90_24 fz2_90_24
  · exact match_zero_fix ⟨91, by decide⟩ ⟨24, by decide⟩ p hp j hj hq fz1_91_24 fz2_91_24
  · exact match_zero_fix ⟨92, by decide⟩ ⟨24, by decide⟩ p hp j hj hq fz1_92_24 fz2_92_24
  · exact match_zero_fix ⟨93, by decide⟩ ⟨24, by decide⟩ p hp j hj hq fz1_93_24 fz2_93_24
  · exact match_zero_fix ⟨94, by decide⟩ ⟨24, by decide⟩ p hp j hj hq fz1_94_24 fz2_94_24
  · exact match_zero_fix ⟨95, by decide⟩ ⟨24, by decide⟩ p hp j hj hq fz1_95_24 fz2_95_24
  · exact match_zero_fix ⟨96, by decide⟩ ⟨24, by decide⟩ p hp j hj hq fz1_96_24 fz2_96_24
  · exact match_zero_fix ⟨97, by decide⟩ ⟨24, by decide⟩ p hp j hj hq fz1_97_24 fz2_97_24
  · exact match_zero_fix ⟨98, by decide⟩ ⟨24, by decide⟩ p hp j hj hq fz1_98_24 fz2_98_24
  · exact match_zero_fix ⟨99, by decide⟩ ⟨24, by decide⟩ p hp j hj hq fz1_99_24 fz2_99_24
  · exact match_zero_fix ⟨100, by decide⟩ ⟨24, by decide⟩ p hp j hj hq fz1_100_24 fz2_100_24
  · exact match_zero_fix ⟨101, by decide⟩ ⟨24, by decide⟩ p hp j hj hq fz1_101_24 fz2_101_24
  · exact match_zero_fix ⟨102, by decide⟩ ⟨24, by decide⟩ p hp j hj hq fz1_102_24 fz2_102_24
  · exact match_zero_fix ⟨103, by decide⟩ ⟨24, by decide⟩ p hp j hj hq fz1_103_24 fz2_103_24
  · exact match_zero_fix ⟨104, by decide⟩ ⟨24, by decide⟩ p hp j hj hq fz1_104_24 fz2_104_24
  · exact match_zero_fix ⟨105, by decide⟩ ⟨24, by decide⟩ p hp j hj hq fz1_105_24 fz2_105_24
  · exact match_zero_fix ⟨106, by decide⟩ ⟨24, by decide⟩ p hp j hj hq fz1_106_24 fz2_106_24
  · exact match_zero_fix ⟨107, by decide⟩ ⟨24, by decide⟩ p hp j hj hq fz1_107_24 fz2_107_24
  · exact match_zero_fix ⟨108, by decide⟩ ⟨24, by decide⟩ p hp j hj hq fz1_108_24 fz2_108_24
  · exact match_zero_fix ⟨109, by decide⟩ ⟨24, by decide⟩ p hp j hj hq fz1_109_24 fz2_109_24
  · exact match_zero_fix ⟨110, by decide⟩ ⟨24, by decide⟩ p hp j hj hq fz1_110_24 fz2_110_24
  · exact match_zero_fix ⟨111, by decide⟩ ⟨24, by decide⟩ p hp j hj hq fz1_111_24 fz2_111_24
  · exact match_zero_fix ⟨112, by decide⟩ ⟨24, by decide⟩ p hp j hj hq fz1_112_24 fz2_112_24
  · exact match_zero_fix ⟨113, by decide⟩ ⟨24, by decide⟩ p hp j hj hq fz1_113_24 fz2_113_24
  · exact match_zero_fix ⟨114, by decide⟩ ⟨24, by decide⟩ p hp j hj hq fz1_114_24 fz2_114_24
  · exact match_zero_fix ⟨115, by decide⟩ ⟨24, by decide⟩ p hp j hj hq fz1_115_24 fz2_115_24
  · exact pair_116_24 p hp hrep j hj hq
  · exact pair_117_24 p hp hrep j hj hq
  · exact pair_118_24 p hp hrep j hj hq
  · exact pair_119_24 p hp hrep j hj hq
  · exact pair_120_24 p hp hrep j hj hq
  · exact match_zero_fix ⟨121, by decide⟩ ⟨24, by decide⟩ p hp j hj hq fz1_121_24 fz2_121_24
  · exact match_zero_fix ⟨122, by decide⟩ ⟨24, by decide⟩ p hp j hj hq fz1_122_24 fz2_122_24
  · exact match_zero_fix ⟨123, by decide⟩ ⟨24, by decide⟩ p hp j hj hq fz1_123_24 fz2_123_24
  · exact match_zero_fix ⟨124, by decide⟩ ⟨24, by decide⟩ p hp j hj hq fz1_124_24 fz2_124_24
  · exact match_zero_fix ⟨125, by decide⟩ ⟨24, by decide⟩ p hp j hj hq fz1_125_24 fz2_125_24
  · exact match_zero_fix ⟨126, by decide⟩ ⟨24, by decide⟩ p hp j hj hq fz1_126_24 fz2_126_24
  · exact match_zero_fix ⟨127, by decide⟩ ⟨24, by decide⟩ p hp j hj hq fz1_127_24 fz2_127_24
  · exact match_zero_fix ⟨128, by decide⟩ ⟨24, by decide⟩ p hp j hj hq fz1_128_24 fz2_128_24
  · exact match_zero_fix ⟨129, by decide⟩ ⟨24, by decide⟩ p hp j hj hq fz1_129_24 fz2_129_24
  · exact match_zero_fix ⟨130, by decide⟩ ⟨24, by decide⟩ p hp j hj hq fz1_130_24 fz2_130_24
  · exact match_zero_fix ⟨131, by decide⟩ ⟨24, by decide⟩ p hp j hj hq fz1_131_24 fz2_131_24
  · exact match_zero_fix ⟨132, by decide⟩ ⟨24, by decide⟩ p hp j hj hq fz1_132_24 fz2_132_24
  · exact match_zero_fix ⟨133, by decide⟩ ⟨24, by decide⟩ p hp j hj hq fz1_133_24 fz2_133_24
  · exact match_zero_fix ⟨134, by decide⟩ ⟨24, by decide⟩ p hp j hj hq fz1_134_24 fz2_134_24
  · exact match_zero_fix ⟨135, by decide⟩ ⟨24, by decide⟩ p hp j hj hq fz1_135_24 fz2_135_24
  · exact match_zero_fix ⟨136, by decide⟩ ⟨24, by decide⟩ p hp j hj hq fz1_136_24 fz2_136_24
  · exact match_zero_fix ⟨137, by decide⟩ ⟨24, by decide⟩ p hp j hj hq fz1_137_24 fz2_137_24
  · exact match_zero_fix ⟨138, by decide⟩ ⟨24, by decide⟩ p hp j hj hq fz1_138_24 fz2_138_24
  · exact match_zero_fix ⟨139, by decide⟩ ⟨24, by decide⟩ p hp j hj hq fz1_139_24 fz2_139_24
  · exact match_zero_fix ⟨140, by decide⟩ ⟨24, by decide⟩ p hp j hj hq fz1_140_24 fz2_140_24
  · exact pair_141_24 p hp hrep j hj hq
  · exact match_zero_fix ⟨142, by decide⟩ ⟨24, by decide⟩ p hp j hj hq fz1_142_24 fz2_142_24
  · exact match_zero_fix ⟨143, by decide⟩ ⟨24, by decide⟩ p hp j hj hq fz1_143_24 fz2_143_24
  · exact match_zero_fix ⟨144, by decide⟩ ⟨24, by decide⟩ p hp j hj hq fz1_144_24 fz2_144_24
  · exact match_zero_fix ⟨145, by decide⟩ ⟨24, by decide⟩ p hp j hj hq fz1_145_24 fz2_145_24
  · exact match_zero_fix ⟨146, by decide⟩ ⟨24, by decide⟩ p hp j hj hq fz1_146_24 fz2_146_24
  · exact pair_147_24 p hp hrep j hj hq

theorem master_25 (p : Nat) (hp : p < (Q2.transData.getD 25 []).length)
    (hrep : (Q2.cosetIsRep.getD 25 []).getD p false = true)
    (rK : Fin 148) (j : Nat) (hj : j < (repChars.getD rK.val []).length)
    (hq : (normIsRep.getD rK.val []).getD j false = true) :
    species (Q2.reps (⟨25, by decide⟩ : Fin 148)) (colE2 ⟨25, by decide⟩ p hp)
        (rowE2 rK j hj hq)
      = species (reps (⟨25, by decide⟩ : Fin 148))
        (colE1 ⟨25, by decide⟩ p (transLenTr ⟨25, by decide⟩ p hp)) (rowE1 rK j hj) := by
  rcases rK with ⟨nK, hnK⟩; interval_cases nK
  · exact match_zero_len ⟨0, by decide⟩ ⟨25, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨1, by decide⟩ ⟨25, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨2, by decide⟩ ⟨25, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨3, by decide⟩ ⟨25, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨4, by decide⟩ ⟨25, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨5, by decide⟩ ⟨25, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨6, by decide⟩ ⟨25, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨7, by decide⟩ ⟨25, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨8, by decide⟩ ⟨25, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨9, by decide⟩ ⟨25, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨10, by decide⟩ ⟨25, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨11, by decide⟩ ⟨25, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨12, by decide⟩ ⟨25, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_fix ⟨13, by decide⟩ ⟨25, by decide⟩ p hp j hj hq fz1_13_25 fz2_13_25
  · exact match_zero_fix ⟨14, by decide⟩ ⟨25, by decide⟩ p hp j hj hq fz1_14_25 fz2_14_25
  · exact match_zero_fix ⟨15, by decide⟩ ⟨25, by decide⟩ p hp j hj hq fz1_15_25 fz2_15_25
  · exact match_zero_fix ⟨16, by decide⟩ ⟨25, by decide⟩ p hp j hj hq fz1_16_25 fz2_16_25
  · exact match_zero_fix ⟨17, by decide⟩ ⟨25, by decide⟩ p hp j hj hq fz1_17_25 fz2_17_25
  · exact match_zero_fix ⟨18, by decide⟩ ⟨25, by decide⟩ p hp j hj hq fz1_18_25 fz2_18_25
  · exact match_zero_fix ⟨19, by decide⟩ ⟨25, by decide⟩ p hp j hj hq fz1_19_25 fz2_19_25
  · exact match_zero_fix ⟨20, by decide⟩ ⟨25, by decide⟩ p hp j hj hq fz1_20_25 fz2_20_25
  · exact match_zero_fix ⟨21, by decide⟩ ⟨25, by decide⟩ p hp j hj hq fz1_21_25 fz2_21_25
  · exact match_zero_fix ⟨22, by decide⟩ ⟨25, by decide⟩ p hp j hj hq fz1_22_25 fz2_22_25
  · exact match_zero_fix ⟨23, by decide⟩ ⟨25, by decide⟩ p hp j hj hq fz1_23_25 fz2_23_25
  · exact match_zero_fix ⟨24, by decide⟩ ⟨25, by decide⟩ p hp j hj hq fz1_24_25 fz2_24_25
  · exact pair_25_25 p hp hrep j hj hq
  · exact match_zero_fix ⟨26, by decide⟩ ⟨25, by decide⟩ p hp j hj hq fz1_26_25 fz2_26_25
  · exact match_zero_fix ⟨27, by decide⟩ ⟨25, by decide⟩ p hp j hj hq fz1_27_25 fz2_27_25
  · exact match_zero_fix ⟨28, by decide⟩ ⟨25, by decide⟩ p hp j hj hq fz1_28_25 fz2_28_25
  · exact match_zero_fix ⟨29, by decide⟩ ⟨25, by decide⟩ p hp j hj hq fz1_29_25 fz2_29_25
  · exact match_zero_fix ⟨30, by decide⟩ ⟨25, by decide⟩ p hp j hj hq fz1_30_25 fz2_30_25
  · exact match_zero_fix ⟨31, by decide⟩ ⟨25, by decide⟩ p hp j hj hq fz1_31_25 fz2_31_25
  · exact match_zero_fix ⟨32, by decide⟩ ⟨25, by decide⟩ p hp j hj hq fz1_32_25 fz2_32_25
  · exact match_zero_fix ⟨33, by decide⟩ ⟨25, by decide⟩ p hp j hj hq fz1_33_25 fz2_33_25
  · exact match_zero_fix ⟨34, by decide⟩ ⟨25, by decide⟩ p hp j hj hq fz1_34_25 fz2_34_25
  · exact match_zero_fix ⟨35, by decide⟩ ⟨25, by decide⟩ p hp j hj hq fz1_35_25 fz2_35_25
  · exact match_zero_fix ⟨36, by decide⟩ ⟨25, by decide⟩ p hp j hj hq fz1_36_25 fz2_36_25
  · exact match_zero_fix ⟨37, by decide⟩ ⟨25, by decide⟩ p hp j hj hq fz1_37_25 fz2_37_25
  · exact match_zero_fix ⟨38, by decide⟩ ⟨25, by decide⟩ p hp j hj hq fz1_38_25 fz2_38_25
  · exact match_zero_fix ⟨39, by decide⟩ ⟨25, by decide⟩ p hp j hj hq fz1_39_25 fz2_39_25
  · exact match_zero_fix ⟨40, by decide⟩ ⟨25, by decide⟩ p hp j hj hq fz1_40_25 fz2_40_25
  · exact match_zero_fix ⟨41, by decide⟩ ⟨25, by decide⟩ p hp j hj hq fz1_41_25 fz2_41_25
  · exact match_zero_fix ⟨42, by decide⟩ ⟨25, by decide⟩ p hp j hj hq fz1_42_25 fz2_42_25
  · exact match_zero_fix ⟨43, by decide⟩ ⟨25, by decide⟩ p hp j hj hq fz1_43_25 fz2_43_25
  · exact match_zero_fix ⟨44, by decide⟩ ⟨25, by decide⟩ p hp j hj hq fz1_44_25 fz2_44_25
  · exact match_zero_fix ⟨45, by decide⟩ ⟨25, by decide⟩ p hp j hj hq fz1_45_25 fz2_45_25
  · exact match_zero_fix ⟨46, by decide⟩ ⟨25, by decide⟩ p hp j hj hq fz1_46_25 fz2_46_25
  · exact match_zero_fix ⟨47, by decide⟩ ⟨25, by decide⟩ p hp j hj hq fz1_47_25 fz2_47_25
  · exact match_zero_fix ⟨48, by decide⟩ ⟨25, by decide⟩ p hp j hj hq fz1_48_25 fz2_48_25
  · exact match_zero_fix ⟨49, by decide⟩ ⟨25, by decide⟩ p hp j hj hq fz1_49_25 fz2_49_25
  · exact match_zero_fix ⟨50, by decide⟩ ⟨25, by decide⟩ p hp j hj hq fz1_50_25 fz2_50_25
  · exact match_zero_fix ⟨51, by decide⟩ ⟨25, by decide⟩ p hp j hj hq fz1_51_25 fz2_51_25
  · exact match_zero_fix ⟨52, by decide⟩ ⟨25, by decide⟩ p hp j hj hq fz1_52_25 fz2_52_25
  · exact match_zero_fix ⟨53, by decide⟩ ⟨25, by decide⟩ p hp j hj hq fz1_53_25 fz2_53_25
  · exact match_zero_fix ⟨54, by decide⟩ ⟨25, by decide⟩ p hp j hj hq fz1_54_25 fz2_54_25
  · exact match_zero_fix ⟨55, by decide⟩ ⟨25, by decide⟩ p hp j hj hq fz1_55_25 fz2_55_25
  · exact match_zero_fix ⟨56, by decide⟩ ⟨25, by decide⟩ p hp j hj hq fz1_56_25 fz2_56_25
  · exact pair_57_25 p hp hrep j hj hq
  · exact match_zero_fix ⟨58, by decide⟩ ⟨25, by decide⟩ p hp j hj hq fz1_58_25 fz2_58_25
  · exact match_zero_fix ⟨59, by decide⟩ ⟨25, by decide⟩ p hp j hj hq fz1_59_25 fz2_59_25
  · exact match_zero_fix ⟨60, by decide⟩ ⟨25, by decide⟩ p hp j hj hq fz1_60_25 fz2_60_25
  · exact match_zero_fix ⟨61, by decide⟩ ⟨25, by decide⟩ p hp j hj hq fz1_61_25 fz2_61_25
  · exact pair_62_25 p hp hrep j hj hq
  · exact match_zero_fix ⟨63, by decide⟩ ⟨25, by decide⟩ p hp j hj hq fz1_63_25 fz2_63_25
  · exact match_zero_fix ⟨64, by decide⟩ ⟨25, by decide⟩ p hp j hj hq fz1_64_25 fz2_64_25
  · exact match_zero_fix ⟨65, by decide⟩ ⟨25, by decide⟩ p hp j hj hq fz1_65_25 fz2_65_25
  · exact match_zero_fix ⟨66, by decide⟩ ⟨25, by decide⟩ p hp j hj hq fz1_66_25 fz2_66_25
  · exact pair_67_25 p hp hrep j hj hq
  · exact match_zero_fix ⟨68, by decide⟩ ⟨25, by decide⟩ p hp j hj hq fz1_68_25 fz2_68_25
  · exact match_zero_fix ⟨69, by decide⟩ ⟨25, by decide⟩ p hp j hj hq fz1_69_25 fz2_69_25
  · exact match_zero_fix ⟨70, by decide⟩ ⟨25, by decide⟩ p hp j hj hq fz1_70_25 fz2_70_25
  · exact match_zero_fix ⟨71, by decide⟩ ⟨25, by decide⟩ p hp j hj hq fz1_71_25 fz2_71_25
  · exact pair_72_25 p hp hrep j hj hq
  · exact match_zero_fix ⟨73, by decide⟩ ⟨25, by decide⟩ p hp j hj hq fz1_73_25 fz2_73_25
  · exact match_zero_fix ⟨74, by decide⟩ ⟨25, by decide⟩ p hp j hj hq fz1_74_25 fz2_74_25
  · exact match_zero_fix ⟨75, by decide⟩ ⟨25, by decide⟩ p hp j hj hq fz1_75_25 fz2_75_25
  · exact match_zero_fix ⟨76, by decide⟩ ⟨25, by decide⟩ p hp j hj hq fz1_76_25 fz2_76_25
  · exact pair_77_25 p hp hrep j hj hq
  · exact match_zero_fix ⟨78, by decide⟩ ⟨25, by decide⟩ p hp j hj hq fz1_78_25 fz2_78_25
  · exact match_zero_fix ⟨79, by decide⟩ ⟨25, by decide⟩ p hp j hj hq fz1_79_25 fz2_79_25
  · exact pair_80_25 p hp hrep j hj hq
  · exact match_zero_fix ⟨81, by decide⟩ ⟨25, by decide⟩ p hp j hj hq fz1_81_25 fz2_81_25
  · exact match_zero_fix ⟨82, by decide⟩ ⟨25, by decide⟩ p hp j hj hq fz1_82_25 fz2_82_25
  · exact match_zero_fix ⟨83, by decide⟩ ⟨25, by decide⟩ p hp j hj hq fz1_83_25 fz2_83_25
  · exact match_zero_fix ⟨84, by decide⟩ ⟨25, by decide⟩ p hp j hj hq fz1_84_25 fz2_84_25
  · exact match_zero_fix ⟨85, by decide⟩ ⟨25, by decide⟩ p hp j hj hq fz1_85_25 fz2_85_25
  · exact match_zero_fix ⟨86, by decide⟩ ⟨25, by decide⟩ p hp j hj hq fz1_86_25 fz2_86_25
  · exact pair_87_25 p hp hrep j hj hq
  · exact match_zero_fix ⟨88, by decide⟩ ⟨25, by decide⟩ p hp j hj hq fz1_88_25 fz2_88_25
  · exact match_zero_fix ⟨89, by decide⟩ ⟨25, by decide⟩ p hp j hj hq fz1_89_25 fz2_89_25
  · exact match_zero_fix ⟨90, by decide⟩ ⟨25, by decide⟩ p hp j hj hq fz1_90_25 fz2_90_25
  · exact match_zero_fix ⟨91, by decide⟩ ⟨25, by decide⟩ p hp j hj hq fz1_91_25 fz2_91_25
  · exact match_zero_fix ⟨92, by decide⟩ ⟨25, by decide⟩ p hp j hj hq fz1_92_25 fz2_92_25
  · exact match_zero_fix ⟨93, by decide⟩ ⟨25, by decide⟩ p hp j hj hq fz1_93_25 fz2_93_25
  · exact match_zero_fix ⟨94, by decide⟩ ⟨25, by decide⟩ p hp j hj hq fz1_94_25 fz2_94_25
  · exact match_zero_fix ⟨95, by decide⟩ ⟨25, by decide⟩ p hp j hj hq fz1_95_25 fz2_95_25
  · exact match_zero_fix ⟨96, by decide⟩ ⟨25, by decide⟩ p hp j hj hq fz1_96_25 fz2_96_25
  · exact match_zero_fix ⟨97, by decide⟩ ⟨25, by decide⟩ p hp j hj hq fz1_97_25 fz2_97_25
  · exact match_zero_fix ⟨98, by decide⟩ ⟨25, by decide⟩ p hp j hj hq fz1_98_25 fz2_98_25
  · exact match_zero_fix ⟨99, by decide⟩ ⟨25, by decide⟩ p hp j hj hq fz1_99_25 fz2_99_25
  · exact match_zero_fix ⟨100, by decide⟩ ⟨25, by decide⟩ p hp j hj hq fz1_100_25 fz2_100_25
  · exact match_zero_fix ⟨101, by decide⟩ ⟨25, by decide⟩ p hp j hj hq fz1_101_25 fz2_101_25
  · exact match_zero_fix ⟨102, by decide⟩ ⟨25, by decide⟩ p hp j hj hq fz1_102_25 fz2_102_25
  · exact match_zero_fix ⟨103, by decide⟩ ⟨25, by decide⟩ p hp j hj hq fz1_103_25 fz2_103_25
  · exact match_zero_fix ⟨104, by decide⟩ ⟨25, by decide⟩ p hp j hj hq fz1_104_25 fz2_104_25
  · exact match_zero_fix ⟨105, by decide⟩ ⟨25, by decide⟩ p hp j hj hq fz1_105_25 fz2_105_25
  · exact match_zero_fix ⟨106, by decide⟩ ⟨25, by decide⟩ p hp j hj hq fz1_106_25 fz2_106_25
  · exact match_zero_fix ⟨107, by decide⟩ ⟨25, by decide⟩ p hp j hj hq fz1_107_25 fz2_107_25
  · exact match_zero_fix ⟨108, by decide⟩ ⟨25, by decide⟩ p hp j hj hq fz1_108_25 fz2_108_25
  · exact match_zero_fix ⟨109, by decide⟩ ⟨25, by decide⟩ p hp j hj hq fz1_109_25 fz2_109_25
  · exact match_zero_fix ⟨110, by decide⟩ ⟨25, by decide⟩ p hp j hj hq fz1_110_25 fz2_110_25
  · exact match_zero_fix ⟨111, by decide⟩ ⟨25, by decide⟩ p hp j hj hq fz1_111_25 fz2_111_25
  · exact match_zero_fix ⟨112, by decide⟩ ⟨25, by decide⟩ p hp j hj hq fz1_112_25 fz2_112_25
  · exact match_zero_fix ⟨113, by decide⟩ ⟨25, by decide⟩ p hp j hj hq fz1_113_25 fz2_113_25
  · exact match_zero_fix ⟨114, by decide⟩ ⟨25, by decide⟩ p hp j hj hq fz1_114_25 fz2_114_25
  · exact match_zero_fix ⟨115, by decide⟩ ⟨25, by decide⟩ p hp j hj hq fz1_115_25 fz2_115_25
  · exact pair_116_25 p hp hrep j hj hq
  · exact pair_117_25 p hp hrep j hj hq
  · exact pair_118_25 p hp hrep j hj hq
  · exact pair_119_25 p hp hrep j hj hq
  · exact pair_120_25 p hp hrep j hj hq
  · exact match_zero_fix ⟨121, by decide⟩ ⟨25, by decide⟩ p hp j hj hq fz1_121_25 fz2_121_25
  · exact match_zero_fix ⟨122, by decide⟩ ⟨25, by decide⟩ p hp j hj hq fz1_122_25 fz2_122_25
  · exact match_zero_fix ⟨123, by decide⟩ ⟨25, by decide⟩ p hp j hj hq fz1_123_25 fz2_123_25
  · exact match_zero_fix ⟨124, by decide⟩ ⟨25, by decide⟩ p hp j hj hq fz1_124_25 fz2_124_25
  · exact match_zero_fix ⟨125, by decide⟩ ⟨25, by decide⟩ p hp j hj hq fz1_125_25 fz2_125_25
  · exact match_zero_fix ⟨126, by decide⟩ ⟨25, by decide⟩ p hp j hj hq fz1_126_25 fz2_126_25
  · exact match_zero_fix ⟨127, by decide⟩ ⟨25, by decide⟩ p hp j hj hq fz1_127_25 fz2_127_25
  · exact match_zero_fix ⟨128, by decide⟩ ⟨25, by decide⟩ p hp j hj hq fz1_128_25 fz2_128_25
  · exact match_zero_fix ⟨129, by decide⟩ ⟨25, by decide⟩ p hp j hj hq fz1_129_25 fz2_129_25
  · exact match_zero_fix ⟨130, by decide⟩ ⟨25, by decide⟩ p hp j hj hq fz1_130_25 fz2_130_25
  · exact match_zero_fix ⟨131, by decide⟩ ⟨25, by decide⟩ p hp j hj hq fz1_131_25 fz2_131_25
  · exact match_zero_fix ⟨132, by decide⟩ ⟨25, by decide⟩ p hp j hj hq fz1_132_25 fz2_132_25
  · exact match_zero_fix ⟨133, by decide⟩ ⟨25, by decide⟩ p hp j hj hq fz1_133_25 fz2_133_25
  · exact match_zero_fix ⟨134, by decide⟩ ⟨25, by decide⟩ p hp j hj hq fz1_134_25 fz2_134_25
  · exact match_zero_fix ⟨135, by decide⟩ ⟨25, by decide⟩ p hp j hj hq fz1_135_25 fz2_135_25
  · exact match_zero_fix ⟨136, by decide⟩ ⟨25, by decide⟩ p hp j hj hq fz1_136_25 fz2_136_25
  · exact match_zero_fix ⟨137, by decide⟩ ⟨25, by decide⟩ p hp j hj hq fz1_137_25 fz2_137_25
  · exact match_zero_fix ⟨138, by decide⟩ ⟨25, by decide⟩ p hp j hj hq fz1_138_25 fz2_138_25
  · exact match_zero_fix ⟨139, by decide⟩ ⟨25, by decide⟩ p hp j hj hq fz1_139_25 fz2_139_25
  · exact match_zero_fix ⟨140, by decide⟩ ⟨25, by decide⟩ p hp j hj hq fz1_140_25 fz2_140_25
  · exact pair_141_25 p hp hrep j hj hq
  · exact match_zero_fix ⟨142, by decide⟩ ⟨25, by decide⟩ p hp j hj hq fz1_142_25 fz2_142_25
  · exact match_zero_fix ⟨143, by decide⟩ ⟨25, by decide⟩ p hp j hj hq fz1_143_25 fz2_143_25
  · exact match_zero_fix ⟨144, by decide⟩ ⟨25, by decide⟩ p hp j hj hq fz1_144_25 fz2_144_25
  · exact match_zero_fix ⟨145, by decide⟩ ⟨25, by decide⟩ p hp j hj hq fz1_145_25 fz2_145_25
  · exact match_zero_fix ⟨146, by decide⟩ ⟨25, by decide⟩ p hp j hj hq fz1_146_25 fz2_146_25
  · exact pair_147_25 p hp hrep j hj hq

theorem master_26 (p : Nat) (hp : p < (Q2.transData.getD 26 []).length)
    (hrep : (Q2.cosetIsRep.getD 26 []).getD p false = true)
    (rK : Fin 148) (j : Nat) (hj : j < (repChars.getD rK.val []).length)
    (hq : (normIsRep.getD rK.val []).getD j false = true) :
    species (Q2.reps (⟨26, by decide⟩ : Fin 148)) (colE2 ⟨26, by decide⟩ p hp)
        (rowE2 rK j hj hq)
      = species (reps (⟨26, by decide⟩ : Fin 148))
        (colE1 ⟨26, by decide⟩ p (transLenTr ⟨26, by decide⟩ p hp)) (rowE1 rK j hj) := by
  rcases rK with ⟨nK, hnK⟩; interval_cases nK
  · exact match_zero_len ⟨0, by decide⟩ ⟨26, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨1, by decide⟩ ⟨26, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨2, by decide⟩ ⟨26, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨3, by decide⟩ ⟨26, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨4, by decide⟩ ⟨26, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨5, by decide⟩ ⟨26, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨6, by decide⟩ ⟨26, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨7, by decide⟩ ⟨26, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨8, by decide⟩ ⟨26, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨9, by decide⟩ ⟨26, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨10, by decide⟩ ⟨26, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨11, by decide⟩ ⟨26, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨12, by decide⟩ ⟨26, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_fix ⟨13, by decide⟩ ⟨26, by decide⟩ p hp j hj hq fz1_13_26 fz2_13_26
  · exact match_zero_fix ⟨14, by decide⟩ ⟨26, by decide⟩ p hp j hj hq fz1_14_26 fz2_14_26
  · exact match_zero_fix ⟨15, by decide⟩ ⟨26, by decide⟩ p hp j hj hq fz1_15_26 fz2_15_26
  · exact match_zero_fix ⟨16, by decide⟩ ⟨26, by decide⟩ p hp j hj hq fz1_16_26 fz2_16_26
  · exact match_zero_fix ⟨17, by decide⟩ ⟨26, by decide⟩ p hp j hj hq fz1_17_26 fz2_17_26
  · exact match_zero_fix ⟨18, by decide⟩ ⟨26, by decide⟩ p hp j hj hq fz1_18_26 fz2_18_26
  · exact match_zero_fix ⟨19, by decide⟩ ⟨26, by decide⟩ p hp j hj hq fz1_19_26 fz2_19_26
  · exact match_zero_fix ⟨20, by decide⟩ ⟨26, by decide⟩ p hp j hj hq fz1_20_26 fz2_20_26
  · exact match_zero_fix ⟨21, by decide⟩ ⟨26, by decide⟩ p hp j hj hq fz1_21_26 fz2_21_26
  · exact match_zero_fix ⟨22, by decide⟩ ⟨26, by decide⟩ p hp j hj hq fz1_22_26 fz2_22_26
  · exact match_zero_fix ⟨23, by decide⟩ ⟨26, by decide⟩ p hp j hj hq fz1_23_26 fz2_23_26
  · exact match_zero_fix ⟨24, by decide⟩ ⟨26, by decide⟩ p hp j hj hq fz1_24_26 fz2_24_26
  · exact match_zero_fix ⟨25, by decide⟩ ⟨26, by decide⟩ p hp j hj hq fz1_25_26 fz2_25_26
  · exact pair_26_26 p hp hrep j hj hq
  · exact match_zero_fix ⟨27, by decide⟩ ⟨26, by decide⟩ p hp j hj hq fz1_27_26 fz2_27_26
  · exact match_zero_fix ⟨28, by decide⟩ ⟨26, by decide⟩ p hp j hj hq fz1_28_26 fz2_28_26
  · exact match_zero_fix ⟨29, by decide⟩ ⟨26, by decide⟩ p hp j hj hq fz1_29_26 fz2_29_26
  · exact match_zero_fix ⟨30, by decide⟩ ⟨26, by decide⟩ p hp j hj hq fz1_30_26 fz2_30_26
  · exact match_zero_fix ⟨31, by decide⟩ ⟨26, by decide⟩ p hp j hj hq fz1_31_26 fz2_31_26
  · exact match_zero_fix ⟨32, by decide⟩ ⟨26, by decide⟩ p hp j hj hq fz1_32_26 fz2_32_26
  · exact match_zero_fix ⟨33, by decide⟩ ⟨26, by decide⟩ p hp j hj hq fz1_33_26 fz2_33_26
  · exact match_zero_fix ⟨34, by decide⟩ ⟨26, by decide⟩ p hp j hj hq fz1_34_26 fz2_34_26
  · exact match_zero_fix ⟨35, by decide⟩ ⟨26, by decide⟩ p hp j hj hq fz1_35_26 fz2_35_26
  · exact match_zero_fix ⟨36, by decide⟩ ⟨26, by decide⟩ p hp j hj hq fz1_36_26 fz2_36_26
  · exact match_zero_fix ⟨37, by decide⟩ ⟨26, by decide⟩ p hp j hj hq fz1_37_26 fz2_37_26
  · exact match_zero_fix ⟨38, by decide⟩ ⟨26, by decide⟩ p hp j hj hq fz1_38_26 fz2_38_26
  · exact match_zero_fix ⟨39, by decide⟩ ⟨26, by decide⟩ p hp j hj hq fz1_39_26 fz2_39_26
  · exact match_zero_fix ⟨40, by decide⟩ ⟨26, by decide⟩ p hp j hj hq fz1_40_26 fz2_40_26
  · exact match_zero_fix ⟨41, by decide⟩ ⟨26, by decide⟩ p hp j hj hq fz1_41_26 fz2_41_26
  · exact match_zero_fix ⟨42, by decide⟩ ⟨26, by decide⟩ p hp j hj hq fz1_42_26 fz2_42_26
  · exact match_zero_fix ⟨43, by decide⟩ ⟨26, by decide⟩ p hp j hj hq fz1_43_26 fz2_43_26
  · exact match_zero_fix ⟨44, by decide⟩ ⟨26, by decide⟩ p hp j hj hq fz1_44_26 fz2_44_26
  · exact match_zero_fix ⟨45, by decide⟩ ⟨26, by decide⟩ p hp j hj hq fz1_45_26 fz2_45_26
  · exact match_zero_fix ⟨46, by decide⟩ ⟨26, by decide⟩ p hp j hj hq fz1_46_26 fz2_46_26
  · exact match_zero_fix ⟨47, by decide⟩ ⟨26, by decide⟩ p hp j hj hq fz1_47_26 fz2_47_26
  · exact match_zero_fix ⟨48, by decide⟩ ⟨26, by decide⟩ p hp j hj hq fz1_48_26 fz2_48_26
  · exact match_zero_fix ⟨49, by decide⟩ ⟨26, by decide⟩ p hp j hj hq fz1_49_26 fz2_49_26
  · exact match_zero_fix ⟨50, by decide⟩ ⟨26, by decide⟩ p hp j hj hq fz1_50_26 fz2_50_26
  · exact match_zero_fix ⟨51, by decide⟩ ⟨26, by decide⟩ p hp j hj hq fz1_51_26 fz2_51_26
  · exact match_zero_fix ⟨52, by decide⟩ ⟨26, by decide⟩ p hp j hj hq fz1_52_26 fz2_52_26
  · exact match_zero_fix ⟨53, by decide⟩ ⟨26, by decide⟩ p hp j hj hq fz1_53_26 fz2_53_26
  · exact match_zero_fix ⟨54, by decide⟩ ⟨26, by decide⟩ p hp j hj hq fz1_54_26 fz2_54_26
  · exact match_zero_fix ⟨55, by decide⟩ ⟨26, by decide⟩ p hp j hj hq fz1_55_26 fz2_55_26
  · exact match_zero_fix ⟨56, by decide⟩ ⟨26, by decide⟩ p hp j hj hq fz1_56_26 fz2_56_26
  · exact match_zero_fix ⟨57, by decide⟩ ⟨26, by decide⟩ p hp j hj hq fz1_57_26 fz2_57_26
  · exact match_zero_fix ⟨58, by decide⟩ ⟨26, by decide⟩ p hp j hj hq fz1_58_26 fz2_58_26
  · exact pair_59_26 p hp hrep j hj hq
  · exact match_zero_fix ⟨60, by decide⟩ ⟨26, by decide⟩ p hp j hj hq fz1_60_26 fz2_60_26
  · exact match_zero_fix ⟨61, by decide⟩ ⟨26, by decide⟩ p hp j hj hq fz1_61_26 fz2_61_26
  · exact match_zero_fix ⟨62, by decide⟩ ⟨26, by decide⟩ p hp j hj hq fz1_62_26 fz2_62_26
  · exact match_zero_fix ⟨63, by decide⟩ ⟨26, by decide⟩ p hp j hj hq fz1_63_26 fz2_63_26
  · exact pair_64_26 p hp hrep j hj hq
  · exact match_zero_fix ⟨65, by decide⟩ ⟨26, by decide⟩ p hp j hj hq fz1_65_26 fz2_65_26
  · exact match_zero_fix ⟨66, by decide⟩ ⟨26, by decide⟩ p hp j hj hq fz1_66_26 fz2_66_26
  · exact match_zero_fix ⟨67, by decide⟩ ⟨26, by decide⟩ p hp j hj hq fz1_67_26 fz2_67_26
  · exact match_zero_fix ⟨68, by decide⟩ ⟨26, by decide⟩ p hp j hj hq fz1_68_26 fz2_68_26
  · exact pair_69_26 p hp hrep j hj hq
  · exact match_zero_fix ⟨70, by decide⟩ ⟨26, by decide⟩ p hp j hj hq fz1_70_26 fz2_70_26
  · exact match_zero_fix ⟨71, by decide⟩ ⟨26, by decide⟩ p hp j hj hq fz1_71_26 fz2_71_26
  · exact match_zero_fix ⟨72, by decide⟩ ⟨26, by decide⟩ p hp j hj hq fz1_72_26 fz2_72_26
  · exact match_zero_fix ⟨73, by decide⟩ ⟨26, by decide⟩ p hp j hj hq fz1_73_26 fz2_73_26
  · exact pair_74_26 p hp hrep j hj hq
  · exact match_zero_fix ⟨75, by decide⟩ ⟨26, by decide⟩ p hp j hj hq fz1_75_26 fz2_75_26
  · exact match_zero_fix ⟨76, by decide⟩ ⟨26, by decide⟩ p hp j hj hq fz1_76_26 fz2_76_26
  · exact match_zero_fix ⟨77, by decide⟩ ⟨26, by decide⟩ p hp j hj hq fz1_77_26 fz2_77_26
  · exact match_zero_fix ⟨78, by decide⟩ ⟨26, by decide⟩ p hp j hj hq fz1_78_26 fz2_78_26
  · exact pair_79_26 p hp hrep j hj hq
  · exact pair_80_26 p hp hrep j hj hq
  · exact match_zero_fix ⟨81, by decide⟩ ⟨26, by decide⟩ p hp j hj hq fz1_81_26 fz2_81_26
  · exact match_zero_fix ⟨82, by decide⟩ ⟨26, by decide⟩ p hp j hj hq fz1_82_26 fz2_82_26
  · exact match_zero_fix ⟨83, by decide⟩ ⟨26, by decide⟩ p hp j hj hq fz1_83_26 fz2_83_26
  · exact match_zero_fix ⟨84, by decide⟩ ⟨26, by decide⟩ p hp j hj hq fz1_84_26 fz2_84_26
  · exact match_zero_fix ⟨85, by decide⟩ ⟨26, by decide⟩ p hp j hj hq fz1_85_26 fz2_85_26
  · exact match_zero_fix ⟨86, by decide⟩ ⟨26, by decide⟩ p hp j hj hq fz1_86_26 fz2_86_26
  · exact match_zero_fix ⟨87, by decide⟩ ⟨26, by decide⟩ p hp j hj hq fz1_87_26 fz2_87_26
  · exact match_zero_fix ⟨88, by decide⟩ ⟨26, by decide⟩ p hp j hj hq fz1_88_26 fz2_88_26
  · exact pair_89_26 p hp hrep j hj hq
  · exact match_zero_fix ⟨90, by decide⟩ ⟨26, by decide⟩ p hp j hj hq fz1_90_26 fz2_90_26
  · exact match_zero_fix ⟨91, by decide⟩ ⟨26, by decide⟩ p hp j hj hq fz1_91_26 fz2_91_26
  · exact match_zero_fix ⟨92, by decide⟩ ⟨26, by decide⟩ p hp j hj hq fz1_92_26 fz2_92_26
  · exact match_zero_fix ⟨93, by decide⟩ ⟨26, by decide⟩ p hp j hj hq fz1_93_26 fz2_93_26
  · exact match_zero_fix ⟨94, by decide⟩ ⟨26, by decide⟩ p hp j hj hq fz1_94_26 fz2_94_26
  · exact match_zero_fix ⟨95, by decide⟩ ⟨26, by decide⟩ p hp j hj hq fz1_95_26 fz2_95_26
  · exact match_zero_fix ⟨96, by decide⟩ ⟨26, by decide⟩ p hp j hj hq fz1_96_26 fz2_96_26
  · exact match_zero_fix ⟨97, by decide⟩ ⟨26, by decide⟩ p hp j hj hq fz1_97_26 fz2_97_26
  · exact match_zero_fix ⟨98, by decide⟩ ⟨26, by decide⟩ p hp j hj hq fz1_98_26 fz2_98_26
  · exact match_zero_fix ⟨99, by decide⟩ ⟨26, by decide⟩ p hp j hj hq fz1_99_26 fz2_99_26
  · exact match_zero_fix ⟨100, by decide⟩ ⟨26, by decide⟩ p hp j hj hq fz1_100_26 fz2_100_26
  · exact match_zero_fix ⟨101, by decide⟩ ⟨26, by decide⟩ p hp j hj hq fz1_101_26 fz2_101_26
  · exact match_zero_fix ⟨102, by decide⟩ ⟨26, by decide⟩ p hp j hj hq fz1_102_26 fz2_102_26
  · exact match_zero_fix ⟨103, by decide⟩ ⟨26, by decide⟩ p hp j hj hq fz1_103_26 fz2_103_26
  · exact match_zero_fix ⟨104, by decide⟩ ⟨26, by decide⟩ p hp j hj hq fz1_104_26 fz2_104_26
  · exact match_zero_fix ⟨105, by decide⟩ ⟨26, by decide⟩ p hp j hj hq fz1_105_26 fz2_105_26
  · exact match_zero_fix ⟨106, by decide⟩ ⟨26, by decide⟩ p hp j hj hq fz1_106_26 fz2_106_26
  · exact match_zero_fix ⟨107, by decide⟩ ⟨26, by decide⟩ p hp j hj hq fz1_107_26 fz2_107_26
  · exact match_zero_fix ⟨108, by decide⟩ ⟨26, by decide⟩ p hp j hj hq fz1_108_26 fz2_108_26
  · exact match_zero_fix ⟨109, by decide⟩ ⟨26, by decide⟩ p hp j hj hq fz1_109_26 fz2_109_26
  · exact match_zero_fix ⟨110, by decide⟩ ⟨26, by decide⟩ p hp j hj hq fz1_110_26 fz2_110_26
  · exact match_zero_fix ⟨111, by decide⟩ ⟨26, by decide⟩ p hp j hj hq fz1_111_26 fz2_111_26
  · exact match_zero_fix ⟨112, by decide⟩ ⟨26, by decide⟩ p hp j hj hq fz1_112_26 fz2_112_26
  · exact match_zero_fix ⟨113, by decide⟩ ⟨26, by decide⟩ p hp j hj hq fz1_113_26 fz2_113_26
  · exact match_zero_fix ⟨114, by decide⟩ ⟨26, by decide⟩ p hp j hj hq fz1_114_26 fz2_114_26
  · exact match_zero_fix ⟨115, by decide⟩ ⟨26, by decide⟩ p hp j hj hq fz1_115_26 fz2_115_26
  · exact pair_116_26 p hp hrep j hj hq
  · exact pair_117_26 p hp hrep j hj hq
  · exact pair_118_26 p hp hrep j hj hq
  · exact pair_119_26 p hp hrep j hj hq
  · exact pair_120_26 p hp hrep j hj hq
  · exact match_zero_fix ⟨121, by decide⟩ ⟨26, by decide⟩ p hp j hj hq fz1_121_26 fz2_121_26
  · exact match_zero_fix ⟨122, by decide⟩ ⟨26, by decide⟩ p hp j hj hq fz1_122_26 fz2_122_26
  · exact match_zero_fix ⟨123, by decide⟩ ⟨26, by decide⟩ p hp j hj hq fz1_123_26 fz2_123_26
  · exact match_zero_fix ⟨124, by decide⟩ ⟨26, by decide⟩ p hp j hj hq fz1_124_26 fz2_124_26
  · exact match_zero_fix ⟨125, by decide⟩ ⟨26, by decide⟩ p hp j hj hq fz1_125_26 fz2_125_26
  · exact match_zero_fix ⟨126, by decide⟩ ⟨26, by decide⟩ p hp j hj hq fz1_126_26 fz2_126_26
  · exact match_zero_fix ⟨127, by decide⟩ ⟨26, by decide⟩ p hp j hj hq fz1_127_26 fz2_127_26
  · exact match_zero_fix ⟨128, by decide⟩ ⟨26, by decide⟩ p hp j hj hq fz1_128_26 fz2_128_26
  · exact match_zero_fix ⟨129, by decide⟩ ⟨26, by decide⟩ p hp j hj hq fz1_129_26 fz2_129_26
  · exact match_zero_fix ⟨130, by decide⟩ ⟨26, by decide⟩ p hp j hj hq fz1_130_26 fz2_130_26
  · exact match_zero_fix ⟨131, by decide⟩ ⟨26, by decide⟩ p hp j hj hq fz1_131_26 fz2_131_26
  · exact match_zero_fix ⟨132, by decide⟩ ⟨26, by decide⟩ p hp j hj hq fz1_132_26 fz2_132_26
  · exact match_zero_fix ⟨133, by decide⟩ ⟨26, by decide⟩ p hp j hj hq fz1_133_26 fz2_133_26
  · exact match_zero_fix ⟨134, by decide⟩ ⟨26, by decide⟩ p hp j hj hq fz1_134_26 fz2_134_26
  · exact match_zero_fix ⟨135, by decide⟩ ⟨26, by decide⟩ p hp j hj hq fz1_135_26 fz2_135_26
  · exact match_zero_fix ⟨136, by decide⟩ ⟨26, by decide⟩ p hp j hj hq fz1_136_26 fz2_136_26
  · exact match_zero_fix ⟨137, by decide⟩ ⟨26, by decide⟩ p hp j hj hq fz1_137_26 fz2_137_26
  · exact match_zero_fix ⟨138, by decide⟩ ⟨26, by decide⟩ p hp j hj hq fz1_138_26 fz2_138_26
  · exact match_zero_fix ⟨139, by decide⟩ ⟨26, by decide⟩ p hp j hj hq fz1_139_26 fz2_139_26
  · exact match_zero_fix ⟨140, by decide⟩ ⟨26, by decide⟩ p hp j hj hq fz1_140_26 fz2_140_26
  · exact pair_141_26 p hp hrep j hj hq
  · exact match_zero_fix ⟨142, by decide⟩ ⟨26, by decide⟩ p hp j hj hq fz1_142_26 fz2_142_26
  · exact match_zero_fix ⟨143, by decide⟩ ⟨26, by decide⟩ p hp j hj hq fz1_143_26 fz2_143_26
  · exact match_zero_fix ⟨144, by decide⟩ ⟨26, by decide⟩ p hp j hj hq fz1_144_26 fz2_144_26
  · exact match_zero_fix ⟨145, by decide⟩ ⟨26, by decide⟩ p hp j hj hq fz1_145_26 fz2_145_26
  · exact match_zero_fix ⟨146, by decide⟩ ⟨26, by decide⟩ p hp j hj hq fz1_146_26 fz2_146_26
  · exact pair_147_26 p hp hrep j hj hq

theorem master_27 (p : Nat) (hp : p < (Q2.transData.getD 27 []).length)
    (hrep : (Q2.cosetIsRep.getD 27 []).getD p false = true)
    (rK : Fin 148) (j : Nat) (hj : j < (repChars.getD rK.val []).length)
    (hq : (normIsRep.getD rK.val []).getD j false = true) :
    species (Q2.reps (⟨27, by decide⟩ : Fin 148)) (colE2 ⟨27, by decide⟩ p hp)
        (rowE2 rK j hj hq)
      = species (reps (⟨27, by decide⟩ : Fin 148))
        (colE1 ⟨27, by decide⟩ p (transLenTr ⟨27, by decide⟩ p hp)) (rowE1 rK j hj) := by
  rcases rK with ⟨nK, hnK⟩; interval_cases nK
  · exact match_zero_len ⟨0, by decide⟩ ⟨27, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨1, by decide⟩ ⟨27, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨2, by decide⟩ ⟨27, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨3, by decide⟩ ⟨27, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨4, by decide⟩ ⟨27, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨5, by decide⟩ ⟨27, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨6, by decide⟩ ⟨27, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨7, by decide⟩ ⟨27, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨8, by decide⟩ ⟨27, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨9, by decide⟩ ⟨27, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨10, by decide⟩ ⟨27, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨11, by decide⟩ ⟨27, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨12, by decide⟩ ⟨27, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_fix ⟨13, by decide⟩ ⟨27, by decide⟩ p hp j hj hq fz1_13_27 fz2_13_27
  · exact match_zero_fix ⟨14, by decide⟩ ⟨27, by decide⟩ p hp j hj hq fz1_14_27 fz2_14_27
  · exact match_zero_fix ⟨15, by decide⟩ ⟨27, by decide⟩ p hp j hj hq fz1_15_27 fz2_15_27
  · exact match_zero_fix ⟨16, by decide⟩ ⟨27, by decide⟩ p hp j hj hq fz1_16_27 fz2_16_27
  · exact match_zero_fix ⟨17, by decide⟩ ⟨27, by decide⟩ p hp j hj hq fz1_17_27 fz2_17_27
  · exact match_zero_fix ⟨18, by decide⟩ ⟨27, by decide⟩ p hp j hj hq fz1_18_27 fz2_18_27
  · exact match_zero_fix ⟨19, by decide⟩ ⟨27, by decide⟩ p hp j hj hq fz1_19_27 fz2_19_27
  · exact match_zero_fix ⟨20, by decide⟩ ⟨27, by decide⟩ p hp j hj hq fz1_20_27 fz2_20_27
  · exact match_zero_fix ⟨21, by decide⟩ ⟨27, by decide⟩ p hp j hj hq fz1_21_27 fz2_21_27
  · exact match_zero_fix ⟨22, by decide⟩ ⟨27, by decide⟩ p hp j hj hq fz1_22_27 fz2_22_27
  · exact match_zero_fix ⟨23, by decide⟩ ⟨27, by decide⟩ p hp j hj hq fz1_23_27 fz2_23_27
  · exact match_zero_fix ⟨24, by decide⟩ ⟨27, by decide⟩ p hp j hj hq fz1_24_27 fz2_24_27
  · exact match_zero_fix ⟨25, by decide⟩ ⟨27, by decide⟩ p hp j hj hq fz1_25_27 fz2_25_27
  · exact match_zero_fix ⟨26, by decide⟩ ⟨27, by decide⟩ p hp j hj hq fz1_26_27 fz2_26_27
  · exact pair_27_27 p hp hrep j hj hq
  · exact match_zero_fix ⟨28, by decide⟩ ⟨27, by decide⟩ p hp j hj hq fz1_28_27 fz2_28_27
  · exact match_zero_fix ⟨29, by decide⟩ ⟨27, by decide⟩ p hp j hj hq fz1_29_27 fz2_29_27
  · exact match_zero_fix ⟨30, by decide⟩ ⟨27, by decide⟩ p hp j hj hq fz1_30_27 fz2_30_27
  · exact match_zero_fix ⟨31, by decide⟩ ⟨27, by decide⟩ p hp j hj hq fz1_31_27 fz2_31_27
  · exact match_zero_fix ⟨32, by decide⟩ ⟨27, by decide⟩ p hp j hj hq fz1_32_27 fz2_32_27
  · exact match_zero_fix ⟨33, by decide⟩ ⟨27, by decide⟩ p hp j hj hq fz1_33_27 fz2_33_27
  · exact match_zero_fix ⟨34, by decide⟩ ⟨27, by decide⟩ p hp j hj hq fz1_34_27 fz2_34_27
  · exact match_zero_fix ⟨35, by decide⟩ ⟨27, by decide⟩ p hp j hj hq fz1_35_27 fz2_35_27
  · exact match_zero_fix ⟨36, by decide⟩ ⟨27, by decide⟩ p hp j hj hq fz1_36_27 fz2_36_27
  · exact match_zero_fix ⟨37, by decide⟩ ⟨27, by decide⟩ p hp j hj hq fz1_37_27 fz2_37_27
  · exact match_zero_fix ⟨38, by decide⟩ ⟨27, by decide⟩ p hp j hj hq fz1_38_27 fz2_38_27
  · exact match_zero_fix ⟨39, by decide⟩ ⟨27, by decide⟩ p hp j hj hq fz1_39_27 fz2_39_27
  · exact match_zero_fix ⟨40, by decide⟩ ⟨27, by decide⟩ p hp j hj hq fz1_40_27 fz2_40_27
  · exact match_zero_fix ⟨41, by decide⟩ ⟨27, by decide⟩ p hp j hj hq fz1_41_27 fz2_41_27
  · exact match_zero_fix ⟨42, by decide⟩ ⟨27, by decide⟩ p hp j hj hq fz1_42_27 fz2_42_27
  · exact match_zero_fix ⟨43, by decide⟩ ⟨27, by decide⟩ p hp j hj hq fz1_43_27 fz2_43_27
  · exact match_zero_fix ⟨44, by decide⟩ ⟨27, by decide⟩ p hp j hj hq fz1_44_27 fz2_44_27
  · exact match_zero_fix ⟨45, by decide⟩ ⟨27, by decide⟩ p hp j hj hq fz1_45_27 fz2_45_27
  · exact match_zero_fix ⟨46, by decide⟩ ⟨27, by decide⟩ p hp j hj hq fz1_46_27 fz2_46_27
  · exact match_zero_fix ⟨47, by decide⟩ ⟨27, by decide⟩ p hp j hj hq fz1_47_27 fz2_47_27
  · exact match_zero_fix ⟨48, by decide⟩ ⟨27, by decide⟩ p hp j hj hq fz1_48_27 fz2_48_27
  · exact match_zero_fix ⟨49, by decide⟩ ⟨27, by decide⟩ p hp j hj hq fz1_49_27 fz2_49_27
  · exact match_zero_fix ⟨50, by decide⟩ ⟨27, by decide⟩ p hp j hj hq fz1_50_27 fz2_50_27
  · exact match_zero_fix ⟨51, by decide⟩ ⟨27, by decide⟩ p hp j hj hq fz1_51_27 fz2_51_27
  · exact match_zero_fix ⟨52, by decide⟩ ⟨27, by decide⟩ p hp j hj hq fz1_52_27 fz2_52_27
  · exact match_zero_fix ⟨53, by decide⟩ ⟨27, by decide⟩ p hp j hj hq fz1_53_27 fz2_53_27
  · exact match_zero_fix ⟨54, by decide⟩ ⟨27, by decide⟩ p hp j hj hq fz1_54_27 fz2_54_27
  · exact pair_55_27 p hp hrep j hj hq
  · exact match_zero_fix ⟨56, by decide⟩ ⟨27, by decide⟩ p hp j hj hq fz1_56_27 fz2_56_27
  · exact match_zero_fix ⟨57, by decide⟩ ⟨27, by decide⟩ p hp j hj hq fz1_57_27 fz2_57_27
  · exact match_zero_fix ⟨58, by decide⟩ ⟨27, by decide⟩ p hp j hj hq fz1_58_27 fz2_58_27
  · exact match_zero_fix ⟨59, by decide⟩ ⟨27, by decide⟩ p hp j hj hq fz1_59_27 fz2_59_27
  · exact pair_60_27 p hp hrep j hj hq
  · exact match_zero_fix ⟨61, by decide⟩ ⟨27, by decide⟩ p hp j hj hq fz1_61_27 fz2_61_27
  · exact match_zero_fix ⟨62, by decide⟩ ⟨27, by decide⟩ p hp j hj hq fz1_62_27 fz2_62_27
  · exact match_zero_fix ⟨63, by decide⟩ ⟨27, by decide⟩ p hp j hj hq fz1_63_27 fz2_63_27
  · exact match_zero_fix ⟨64, by decide⟩ ⟨27, by decide⟩ p hp j hj hq fz1_64_27 fz2_64_27
  · exact pair_65_27 p hp hrep j hj hq
  · exact match_zero_fix ⟨66, by decide⟩ ⟨27, by decide⟩ p hp j hj hq fz1_66_27 fz2_66_27
  · exact match_zero_fix ⟨67, by decide⟩ ⟨27, by decide⟩ p hp j hj hq fz1_67_27 fz2_67_27
  · exact match_zero_fix ⟨68, by decide⟩ ⟨27, by decide⟩ p hp j hj hq fz1_68_27 fz2_68_27
  · exact match_zero_fix ⟨69, by decide⟩ ⟨27, by decide⟩ p hp j hj hq fz1_69_27 fz2_69_27
  · exact pair_70_27 p hp hrep j hj hq
  · exact match_zero_fix ⟨71, by decide⟩ ⟨27, by decide⟩ p hp j hj hq fz1_71_27 fz2_71_27
  · exact match_zero_fix ⟨72, by decide⟩ ⟨27, by decide⟩ p hp j hj hq fz1_72_27 fz2_72_27
  · exact match_zero_fix ⟨73, by decide⟩ ⟨27, by decide⟩ p hp j hj hq fz1_73_27 fz2_73_27
  · exact match_zero_fix ⟨74, by decide⟩ ⟨27, by decide⟩ p hp j hj hq fz1_74_27 fz2_74_27
  · exact pair_75_27 p hp hrep j hj hq
  · exact match_zero_fix ⟨76, by decide⟩ ⟨27, by decide⟩ p hp j hj hq fz1_76_27 fz2_76_27
  · exact match_zero_fix ⟨77, by decide⟩ ⟨27, by decide⟩ p hp j hj hq fz1_77_27 fz2_77_27
  · exact match_zero_fix ⟨78, by decide⟩ ⟨27, by decide⟩ p hp j hj hq fz1_78_27 fz2_78_27
  · exact match_zero_fix ⟨79, by decide⟩ ⟨27, by decide⟩ p hp j hj hq fz1_79_27 fz2_79_27
  · exact pair_80_27 p hp hrep j hj hq
  · exact match_zero_fix ⟨81, by decide⟩ ⟨27, by decide⟩ p hp j hj hq fz1_81_27 fz2_81_27
  · exact match_zero_fix ⟨82, by decide⟩ ⟨27, by decide⟩ p hp j hj hq fz1_82_27 fz2_82_27
  · exact match_zero_fix ⟨83, by decide⟩ ⟨27, by decide⟩ p hp j hj hq fz1_83_27 fz2_83_27
  · exact match_zero_fix ⟨84, by decide⟩ ⟨27, by decide⟩ p hp j hj hq fz1_84_27 fz2_84_27
  · exact pair_85_27 p hp hrep j hj hq
  · exact match_zero_fix ⟨86, by decide⟩ ⟨27, by decide⟩ p hp j hj hq fz1_86_27 fz2_86_27
  · exact match_zero_fix ⟨87, by decide⟩ ⟨27, by decide⟩ p hp j hj hq fz1_87_27 fz2_87_27
  · exact match_zero_fix ⟨88, by decide⟩ ⟨27, by decide⟩ p hp j hj hq fz1_88_27 fz2_88_27
  · exact match_zero_fix ⟨89, by decide⟩ ⟨27, by decide⟩ p hp j hj hq fz1_89_27 fz2_89_27
  · exact match_zero_fix ⟨90, by decide⟩ ⟨27, by decide⟩ p hp j hj hq fz1_90_27 fz2_90_27
  · exact match_zero_fix ⟨91, by decide⟩ ⟨27, by decide⟩ p hp j hj hq fz1_91_27 fz2_91_27
  · exact match_zero_fix ⟨92, by decide⟩ ⟨27, by decide⟩ p hp j hj hq fz1_92_27 fz2_92_27
  · exact match_zero_fix ⟨93, by decide⟩ ⟨27, by decide⟩ p hp j hj hq fz1_93_27 fz2_93_27
  · exact match_zero_fix ⟨94, by decide⟩ ⟨27, by decide⟩ p hp j hj hq fz1_94_27 fz2_94_27
  · exact match_zero_fix ⟨95, by decide⟩ ⟨27, by decide⟩ p hp j hj hq fz1_95_27 fz2_95_27
  · exact match_zero_fix ⟨96, by decide⟩ ⟨27, by decide⟩ p hp j hj hq fz1_96_27 fz2_96_27
  · exact match_zero_fix ⟨97, by decide⟩ ⟨27, by decide⟩ p hp j hj hq fz1_97_27 fz2_97_27
  · exact match_zero_fix ⟨98, by decide⟩ ⟨27, by decide⟩ p hp j hj hq fz1_98_27 fz2_98_27
  · exact match_zero_fix ⟨99, by decide⟩ ⟨27, by decide⟩ p hp j hj hq fz1_99_27 fz2_99_27
  · exact match_zero_fix ⟨100, by decide⟩ ⟨27, by decide⟩ p hp j hj hq fz1_100_27 fz2_100_27
  · exact match_zero_fix ⟨101, by decide⟩ ⟨27, by decide⟩ p hp j hj hq fz1_101_27 fz2_101_27
  · exact match_zero_fix ⟨102, by decide⟩ ⟨27, by decide⟩ p hp j hj hq fz1_102_27 fz2_102_27
  · exact match_zero_fix ⟨103, by decide⟩ ⟨27, by decide⟩ p hp j hj hq fz1_103_27 fz2_103_27
  · exact match_zero_fix ⟨104, by decide⟩ ⟨27, by decide⟩ p hp j hj hq fz1_104_27 fz2_104_27
  · exact match_zero_fix ⟨105, by decide⟩ ⟨27, by decide⟩ p hp j hj hq fz1_105_27 fz2_105_27
  · exact match_zero_fix ⟨106, by decide⟩ ⟨27, by decide⟩ p hp j hj hq fz1_106_27 fz2_106_27
  · exact match_zero_fix ⟨107, by decide⟩ ⟨27, by decide⟩ p hp j hj hq fz1_107_27 fz2_107_27
  · exact match_zero_fix ⟨108, by decide⟩ ⟨27, by decide⟩ p hp j hj hq fz1_108_27 fz2_108_27
  · exact match_zero_fix ⟨109, by decide⟩ ⟨27, by decide⟩ p hp j hj hq fz1_109_27 fz2_109_27
  · exact match_zero_fix ⟨110, by decide⟩ ⟨27, by decide⟩ p hp j hj hq fz1_110_27 fz2_110_27
  · exact match_zero_fix ⟨111, by decide⟩ ⟨27, by decide⟩ p hp j hj hq fz1_111_27 fz2_111_27
  · exact match_zero_fix ⟨112, by decide⟩ ⟨27, by decide⟩ p hp j hj hq fz1_112_27 fz2_112_27
  · exact match_zero_fix ⟨113, by decide⟩ ⟨27, by decide⟩ p hp j hj hq fz1_113_27 fz2_113_27
  · exact match_zero_fix ⟨114, by decide⟩ ⟨27, by decide⟩ p hp j hj hq fz1_114_27 fz2_114_27
  · exact match_zero_fix ⟨115, by decide⟩ ⟨27, by decide⟩ p hp j hj hq fz1_115_27 fz2_115_27
  · exact pair_116_27 p hp hrep j hj hq
  · exact pair_117_27 p hp hrep j hj hq
  · exact pair_118_27 p hp hrep j hj hq
  · exact pair_119_27 p hp hrep j hj hq
  · exact pair_120_27 p hp hrep j hj hq
  · exact match_zero_fix ⟨121, by decide⟩ ⟨27, by decide⟩ p hp j hj hq fz1_121_27 fz2_121_27
  · exact match_zero_fix ⟨122, by decide⟩ ⟨27, by decide⟩ p hp j hj hq fz1_122_27 fz2_122_27
  · exact match_zero_fix ⟨123, by decide⟩ ⟨27, by decide⟩ p hp j hj hq fz1_123_27 fz2_123_27
  · exact match_zero_fix ⟨124, by decide⟩ ⟨27, by decide⟩ p hp j hj hq fz1_124_27 fz2_124_27
  · exact match_zero_fix ⟨125, by decide⟩ ⟨27, by decide⟩ p hp j hj hq fz1_125_27 fz2_125_27
  · exact match_zero_fix ⟨126, by decide⟩ ⟨27, by decide⟩ p hp j hj hq fz1_126_27 fz2_126_27
  · exact match_zero_fix ⟨127, by decide⟩ ⟨27, by decide⟩ p hp j hj hq fz1_127_27 fz2_127_27
  · exact match_zero_fix ⟨128, by decide⟩ ⟨27, by decide⟩ p hp j hj hq fz1_128_27 fz2_128_27
  · exact match_zero_fix ⟨129, by decide⟩ ⟨27, by decide⟩ p hp j hj hq fz1_129_27 fz2_129_27
  · exact match_zero_fix ⟨130, by decide⟩ ⟨27, by decide⟩ p hp j hj hq fz1_130_27 fz2_130_27
  · exact match_zero_fix ⟨131, by decide⟩ ⟨27, by decide⟩ p hp j hj hq fz1_131_27 fz2_131_27
  · exact match_zero_fix ⟨132, by decide⟩ ⟨27, by decide⟩ p hp j hj hq fz1_132_27 fz2_132_27
  · exact match_zero_fix ⟨133, by decide⟩ ⟨27, by decide⟩ p hp j hj hq fz1_133_27 fz2_133_27
  · exact match_zero_fix ⟨134, by decide⟩ ⟨27, by decide⟩ p hp j hj hq fz1_134_27 fz2_134_27
  · exact match_zero_fix ⟨135, by decide⟩ ⟨27, by decide⟩ p hp j hj hq fz1_135_27 fz2_135_27
  · exact match_zero_fix ⟨136, by decide⟩ ⟨27, by decide⟩ p hp j hj hq fz1_136_27 fz2_136_27
  · exact match_zero_fix ⟨137, by decide⟩ ⟨27, by decide⟩ p hp j hj hq fz1_137_27 fz2_137_27
  · exact match_zero_fix ⟨138, by decide⟩ ⟨27, by decide⟩ p hp j hj hq fz1_138_27 fz2_138_27
  · exact match_zero_fix ⟨139, by decide⟩ ⟨27, by decide⟩ p hp j hj hq fz1_139_27 fz2_139_27
  · exact match_zero_fix ⟨140, by decide⟩ ⟨27, by decide⟩ p hp j hj hq fz1_140_27 fz2_140_27
  · exact pair_141_27 p hp hrep j hj hq
  · exact match_zero_fix ⟨142, by decide⟩ ⟨27, by decide⟩ p hp j hj hq fz1_142_27 fz2_142_27
  · exact match_zero_fix ⟨143, by decide⟩ ⟨27, by decide⟩ p hp j hj hq fz1_143_27 fz2_143_27
  · exact match_zero_fix ⟨144, by decide⟩ ⟨27, by decide⟩ p hp j hj hq fz1_144_27 fz2_144_27
  · exact match_zero_fix ⟨145, by decide⟩ ⟨27, by decide⟩ p hp j hj hq fz1_145_27 fz2_145_27
  · exact match_zero_fix ⟨146, by decide⟩ ⟨27, by decide⟩ p hp j hj hq fz1_146_27 fz2_146_27
  · exact pair_147_27 p hp hrep j hj hq

theorem master_28 (p : Nat) (hp : p < (Q2.transData.getD 28 []).length)
    (hrep : (Q2.cosetIsRep.getD 28 []).getD p false = true)
    (rK : Fin 148) (j : Nat) (hj : j < (repChars.getD rK.val []).length)
    (hq : (normIsRep.getD rK.val []).getD j false = true) :
    species (Q2.reps (⟨28, by decide⟩ : Fin 148)) (colE2 ⟨28, by decide⟩ p hp)
        (rowE2 rK j hj hq)
      = species (reps (⟨28, by decide⟩ : Fin 148))
        (colE1 ⟨28, by decide⟩ p (transLenTr ⟨28, by decide⟩ p hp)) (rowE1 rK j hj) := by
  rcases rK with ⟨nK, hnK⟩; interval_cases nK
  · exact match_zero_len ⟨0, by decide⟩ ⟨28, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨1, by decide⟩ ⟨28, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨2, by decide⟩ ⟨28, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨3, by decide⟩ ⟨28, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨4, by decide⟩ ⟨28, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨5, by decide⟩ ⟨28, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨6, by decide⟩ ⟨28, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨7, by decide⟩ ⟨28, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨8, by decide⟩ ⟨28, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨9, by decide⟩ ⟨28, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨10, by decide⟩ ⟨28, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨11, by decide⟩ ⟨28, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨12, by decide⟩ ⟨28, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_fix ⟨13, by decide⟩ ⟨28, by decide⟩ p hp j hj hq fz1_13_28 fz2_13_28
  · exact match_zero_fix ⟨14, by decide⟩ ⟨28, by decide⟩ p hp j hj hq fz1_14_28 fz2_14_28
  · exact match_zero_fix ⟨15, by decide⟩ ⟨28, by decide⟩ p hp j hj hq fz1_15_28 fz2_15_28
  · exact match_zero_fix ⟨16, by decide⟩ ⟨28, by decide⟩ p hp j hj hq fz1_16_28 fz2_16_28
  · exact match_zero_fix ⟨17, by decide⟩ ⟨28, by decide⟩ p hp j hj hq fz1_17_28 fz2_17_28
  · exact match_zero_fix ⟨18, by decide⟩ ⟨28, by decide⟩ p hp j hj hq fz1_18_28 fz2_18_28
  · exact match_zero_fix ⟨19, by decide⟩ ⟨28, by decide⟩ p hp j hj hq fz1_19_28 fz2_19_28
  · exact match_zero_fix ⟨20, by decide⟩ ⟨28, by decide⟩ p hp j hj hq fz1_20_28 fz2_20_28
  · exact match_zero_fix ⟨21, by decide⟩ ⟨28, by decide⟩ p hp j hj hq fz1_21_28 fz2_21_28
  · exact match_zero_fix ⟨22, by decide⟩ ⟨28, by decide⟩ p hp j hj hq fz1_22_28 fz2_22_28
  · exact match_zero_fix ⟨23, by decide⟩ ⟨28, by decide⟩ p hp j hj hq fz1_23_28 fz2_23_28
  · exact match_zero_fix ⟨24, by decide⟩ ⟨28, by decide⟩ p hp j hj hq fz1_24_28 fz2_24_28
  · exact match_zero_fix ⟨25, by decide⟩ ⟨28, by decide⟩ p hp j hj hq fz1_25_28 fz2_25_28
  · exact match_zero_fix ⟨26, by decide⟩ ⟨28, by decide⟩ p hp j hj hq fz1_26_28 fz2_26_28
  · exact match_zero_fix ⟨27, by decide⟩ ⟨28, by decide⟩ p hp j hj hq fz1_27_28 fz2_27_28
  · exact pair_28_28 p hp hrep j hj hq
  · exact match_zero_fix ⟨29, by decide⟩ ⟨28, by decide⟩ p hp j hj hq fz1_29_28 fz2_29_28
  · exact match_zero_fix ⟨30, by decide⟩ ⟨28, by decide⟩ p hp j hj hq fz1_30_28 fz2_30_28
  · exact match_zero_fix ⟨31, by decide⟩ ⟨28, by decide⟩ p hp j hj hq fz1_31_28 fz2_31_28
  · exact match_zero_fix ⟨32, by decide⟩ ⟨28, by decide⟩ p hp j hj hq fz1_32_28 fz2_32_28
  · exact match_zero_fix ⟨33, by decide⟩ ⟨28, by decide⟩ p hp j hj hq fz1_33_28 fz2_33_28
  · exact match_zero_fix ⟨34, by decide⟩ ⟨28, by decide⟩ p hp j hj hq fz1_34_28 fz2_34_28
  · exact match_zero_fix ⟨35, by decide⟩ ⟨28, by decide⟩ p hp j hj hq fz1_35_28 fz2_35_28
  · exact match_zero_fix ⟨36, by decide⟩ ⟨28, by decide⟩ p hp j hj hq fz1_36_28 fz2_36_28
  · exact match_zero_fix ⟨37, by decide⟩ ⟨28, by decide⟩ p hp j hj hq fz1_37_28 fz2_37_28
  · exact match_zero_fix ⟨38, by decide⟩ ⟨28, by decide⟩ p hp j hj hq fz1_38_28 fz2_38_28
  · exact match_zero_fix ⟨39, by decide⟩ ⟨28, by decide⟩ p hp j hj hq fz1_39_28 fz2_39_28
  · exact match_zero_fix ⟨40, by decide⟩ ⟨28, by decide⟩ p hp j hj hq fz1_40_28 fz2_40_28
  · exact match_zero_fix ⟨41, by decide⟩ ⟨28, by decide⟩ p hp j hj hq fz1_41_28 fz2_41_28
  · exact match_zero_fix ⟨42, by decide⟩ ⟨28, by decide⟩ p hp j hj hq fz1_42_28 fz2_42_28
  · exact match_zero_fix ⟨43, by decide⟩ ⟨28, by decide⟩ p hp j hj hq fz1_43_28 fz2_43_28
  · exact match_zero_fix ⟨44, by decide⟩ ⟨28, by decide⟩ p hp j hj hq fz1_44_28 fz2_44_28
  · exact match_zero_fix ⟨45, by decide⟩ ⟨28, by decide⟩ p hp j hj hq fz1_45_28 fz2_45_28
  · exact match_zero_fix ⟨46, by decide⟩ ⟨28, by decide⟩ p hp j hj hq fz1_46_28 fz2_46_28
  · exact match_zero_fix ⟨47, by decide⟩ ⟨28, by decide⟩ p hp j hj hq fz1_47_28 fz2_47_28
  · exact match_zero_fix ⟨48, by decide⟩ ⟨28, by decide⟩ p hp j hj hq fz1_48_28 fz2_48_28
  · exact match_zero_fix ⟨49, by decide⟩ ⟨28, by decide⟩ p hp j hj hq fz1_49_28 fz2_49_28
  · exact match_zero_fix ⟨50, by decide⟩ ⟨28, by decide⟩ p hp j hj hq fz1_50_28 fz2_50_28
  · exact match_zero_fix ⟨51, by decide⟩ ⟨28, by decide⟩ p hp j hj hq fz1_51_28 fz2_51_28
  · exact match_zero_fix ⟨52, by decide⟩ ⟨28, by decide⟩ p hp j hj hq fz1_52_28 fz2_52_28
  · exact match_zero_fix ⟨53, by decide⟩ ⟨28, by decide⟩ p hp j hj hq fz1_53_28 fz2_53_28
  · exact match_zero_fix ⟨54, by decide⟩ ⟨28, by decide⟩ p hp j hj hq fz1_54_28 fz2_54_28
  · exact pair_55_28 p hp hrep j hj hq
  · exact pair_56_28 p hp hrep j hj hq
  · exact pair_57_28 p hp hrep j hj hq
  · exact pair_58_28 p hp hrep j hj hq
  · exact pair_59_28 p hp hrep j hj hq
  · exact match_zero_fix ⟨60, by decide⟩ ⟨28, by decide⟩ p hp j hj hq fz1_60_28 fz2_60_28
  · exact match_zero_fix ⟨61, by decide⟩ ⟨28, by decide⟩ p hp j hj hq fz1_61_28 fz2_61_28
  · exact match_zero_fix ⟨62, by decide⟩ ⟨28, by decide⟩ p hp j hj hq fz1_62_28 fz2_62_28
  · exact match_zero_fix ⟨63, by decide⟩ ⟨28, by decide⟩ p hp j hj hq fz1_63_28 fz2_63_28
  · exact match_zero_fix ⟨64, by decide⟩ ⟨28, by decide⟩ p hp j hj hq fz1_64_28 fz2_64_28
  · exact match_zero_fix ⟨65, by decide⟩ ⟨28, by decide⟩ p hp j hj hq fz1_65_28 fz2_65_28
  · exact match_zero_fix ⟨66, by decide⟩ ⟨28, by decide⟩ p hp j hj hq fz1_66_28 fz2_66_28
  · exact match_zero_fix ⟨67, by decide⟩ ⟨28, by decide⟩ p hp j hj hq fz1_67_28 fz2_67_28
  · exact match_zero_fix ⟨68, by decide⟩ ⟨28, by decide⟩ p hp j hj hq fz1_68_28 fz2_68_28
  · exact match_zero_fix ⟨69, by decide⟩ ⟨28, by decide⟩ p hp j hj hq fz1_69_28 fz2_69_28
  · exact match_zero_fix ⟨70, by decide⟩ ⟨28, by decide⟩ p hp j hj hq fz1_70_28 fz2_70_28
  · exact match_zero_fix ⟨71, by decide⟩ ⟨28, by decide⟩ p hp j hj hq fz1_71_28 fz2_71_28
  · exact match_zero_fix ⟨72, by decide⟩ ⟨28, by decide⟩ p hp j hj hq fz1_72_28 fz2_72_28
  · exact match_zero_fix ⟨73, by decide⟩ ⟨28, by decide⟩ p hp j hj hq fz1_73_28 fz2_73_28
  · exact match_zero_fix ⟨74, by decide⟩ ⟨28, by decide⟩ p hp j hj hq fz1_74_28 fz2_74_28
  · exact match_zero_fix ⟨75, by decide⟩ ⟨28, by decide⟩ p hp j hj hq fz1_75_28 fz2_75_28
  · exact match_zero_fix ⟨76, by decide⟩ ⟨28, by decide⟩ p hp j hj hq fz1_76_28 fz2_76_28
  · exact match_zero_fix ⟨77, by decide⟩ ⟨28, by decide⟩ p hp j hj hq fz1_77_28 fz2_77_28
  · exact match_zero_fix ⟨78, by decide⟩ ⟨28, by decide⟩ p hp j hj hq fz1_78_28 fz2_78_28
  · exact match_zero_fix ⟨79, by decide⟩ ⟨28, by decide⟩ p hp j hj hq fz1_79_28 fz2_79_28
  · exact match_zero_fix ⟨80, by decide⟩ ⟨28, by decide⟩ p hp j hj hq fz1_80_28 fz2_80_28
  · exact match_zero_fix ⟨81, by decide⟩ ⟨28, by decide⟩ p hp j hj hq fz1_81_28 fz2_81_28
  · exact match_zero_fix ⟨82, by decide⟩ ⟨28, by decide⟩ p hp j hj hq fz1_82_28 fz2_82_28
  · exact match_zero_fix ⟨83, by decide⟩ ⟨28, by decide⟩ p hp j hj hq fz1_83_28 fz2_83_28
  · exact match_zero_fix ⟨84, by decide⟩ ⟨28, by decide⟩ p hp j hj hq fz1_84_28 fz2_84_28
  · exact match_zero_fix ⟨85, by decide⟩ ⟨28, by decide⟩ p hp j hj hq fz1_85_28 fz2_85_28
  · exact match_zero_fix ⟨86, by decide⟩ ⟨28, by decide⟩ p hp j hj hq fz1_86_28 fz2_86_28
  · exact match_zero_fix ⟨87, by decide⟩ ⟨28, by decide⟩ p hp j hj hq fz1_87_28 fz2_87_28
  · exact match_zero_fix ⟨88, by decide⟩ ⟨28, by decide⟩ p hp j hj hq fz1_88_28 fz2_88_28
  · exact match_zero_fix ⟨89, by decide⟩ ⟨28, by decide⟩ p hp j hj hq fz1_89_28 fz2_89_28
  · exact pair_90_28 p hp hrep j hj hq
  · exact match_zero_fix ⟨91, by decide⟩ ⟨28, by decide⟩ p hp j hj hq fz1_91_28 fz2_91_28
  · exact match_zero_fix ⟨92, by decide⟩ ⟨28, by decide⟩ p hp j hj hq fz1_92_28 fz2_92_28
  · exact match_zero_fix ⟨93, by decide⟩ ⟨28, by decide⟩ p hp j hj hq fz1_93_28 fz2_93_28
  · exact match_zero_fix ⟨94, by decide⟩ ⟨28, by decide⟩ p hp j hj hq fz1_94_28 fz2_94_28
  · exact match_zero_fix ⟨95, by decide⟩ ⟨28, by decide⟩ p hp j hj hq fz1_95_28 fz2_95_28
  · exact match_zero_fix ⟨96, by decide⟩ ⟨28, by decide⟩ p hp j hj hq fz1_96_28 fz2_96_28
  · exact match_zero_fix ⟨97, by decide⟩ ⟨28, by decide⟩ p hp j hj hq fz1_97_28 fz2_97_28
  · exact match_zero_fix ⟨98, by decide⟩ ⟨28, by decide⟩ p hp j hj hq fz1_98_28 fz2_98_28
  · exact match_zero_fix ⟨99, by decide⟩ ⟨28, by decide⟩ p hp j hj hq fz1_99_28 fz2_99_28
  · exact match_zero_fix ⟨100, by decide⟩ ⟨28, by decide⟩ p hp j hj hq fz1_100_28 fz2_100_28
  · exact match_zero_fix ⟨101, by decide⟩ ⟨28, by decide⟩ p hp j hj hq fz1_101_28 fz2_101_28
  · exact match_zero_fix ⟨102, by decide⟩ ⟨28, by decide⟩ p hp j hj hq fz1_102_28 fz2_102_28
  · exact match_zero_fix ⟨103, by decide⟩ ⟨28, by decide⟩ p hp j hj hq fz1_103_28 fz2_103_28
  · exact match_zero_fix ⟨104, by decide⟩ ⟨28, by decide⟩ p hp j hj hq fz1_104_28 fz2_104_28
  · exact match_zero_fix ⟨105, by decide⟩ ⟨28, by decide⟩ p hp j hj hq fz1_105_28 fz2_105_28
  · exact match_zero_fix ⟨106, by decide⟩ ⟨28, by decide⟩ p hp j hj hq fz1_106_28 fz2_106_28
  · exact match_zero_fix ⟨107, by decide⟩ ⟨28, by decide⟩ p hp j hj hq fz1_107_28 fz2_107_28
  · exact match_zero_fix ⟨108, by decide⟩ ⟨28, by decide⟩ p hp j hj hq fz1_108_28 fz2_108_28
  · exact match_zero_fix ⟨109, by decide⟩ ⟨28, by decide⟩ p hp j hj hq fz1_109_28 fz2_109_28
  · exact match_zero_fix ⟨110, by decide⟩ ⟨28, by decide⟩ p hp j hj hq fz1_110_28 fz2_110_28
  · exact match_zero_fix ⟨111, by decide⟩ ⟨28, by decide⟩ p hp j hj hq fz1_111_28 fz2_111_28
  · exact match_zero_fix ⟨112, by decide⟩ ⟨28, by decide⟩ p hp j hj hq fz1_112_28 fz2_112_28
  · exact match_zero_fix ⟨113, by decide⟩ ⟨28, by decide⟩ p hp j hj hq fz1_113_28 fz2_113_28
  · exact match_zero_fix ⟨114, by decide⟩ ⟨28, by decide⟩ p hp j hj hq fz1_114_28 fz2_114_28
  · exact match_zero_fix ⟨115, by decide⟩ ⟨28, by decide⟩ p hp j hj hq fz1_115_28 fz2_115_28
  · exact pair_116_28 p hp hrep j hj hq
  · exact match_zero_fix ⟨117, by decide⟩ ⟨28, by decide⟩ p hp j hj hq fz1_117_28 fz2_117_28
  · exact match_zero_fix ⟨118, by decide⟩ ⟨28, by decide⟩ p hp j hj hq fz1_118_28 fz2_118_28
  · exact match_zero_fix ⟨119, by decide⟩ ⟨28, by decide⟩ p hp j hj hq fz1_119_28 fz2_119_28
  · exact match_zero_fix ⟨120, by decide⟩ ⟨28, by decide⟩ p hp j hj hq fz1_120_28 fz2_120_28
  · exact match_zero_fix ⟨121, by decide⟩ ⟨28, by decide⟩ p hp j hj hq fz1_121_28 fz2_121_28
  · exact pair_122_28 p hp hrep j hj hq
  · exact match_zero_fix ⟨123, by decide⟩ ⟨28, by decide⟩ p hp j hj hq fz1_123_28 fz2_123_28
  · exact match_zero_fix ⟨124, by decide⟩ ⟨28, by decide⟩ p hp j hj hq fz1_124_28 fz2_124_28
  · exact match_zero_fix ⟨125, by decide⟩ ⟨28, by decide⟩ p hp j hj hq fz1_125_28 fz2_125_28
  · exact match_zero_fix ⟨126, by decide⟩ ⟨28, by decide⟩ p hp j hj hq fz1_126_28 fz2_126_28
  · exact match_zero_fix ⟨127, by decide⟩ ⟨28, by decide⟩ p hp j hj hq fz1_127_28 fz2_127_28
  · exact pair_128_28 p hp hrep j hj hq
  · exact match_zero_fix ⟨129, by decide⟩ ⟨28, by decide⟩ p hp j hj hq fz1_129_28 fz2_129_28
  · exact match_zero_fix ⟨130, by decide⟩ ⟨28, by decide⟩ p hp j hj hq fz1_130_28 fz2_130_28
  · exact match_zero_fix ⟨131, by decide⟩ ⟨28, by decide⟩ p hp j hj hq fz1_131_28 fz2_131_28
  · exact match_zero_fix ⟨132, by decide⟩ ⟨28, by decide⟩ p hp j hj hq fz1_132_28 fz2_132_28
  · exact match_zero_fix ⟨133, by decide⟩ ⟨28, by decide⟩ p hp j hj hq fz1_133_28 fz2_133_28
  · exact pair_134_28 p hp hrep j hj hq
  · exact match_zero_fix ⟨135, by decide⟩ ⟨28, by decide⟩ p hp j hj hq fz1_135_28 fz2_135_28
  · exact match_zero_fix ⟨136, by decide⟩ ⟨28, by decide⟩ p hp j hj hq fz1_136_28 fz2_136_28
  · exact match_zero_fix ⟨137, by decide⟩ ⟨28, by decide⟩ p hp j hj hq fz1_137_28 fz2_137_28
  · exact match_zero_fix ⟨138, by decide⟩ ⟨28, by decide⟩ p hp j hj hq fz1_138_28 fz2_138_28
  · exact match_zero_fix ⟨139, by decide⟩ ⟨28, by decide⟩ p hp j hj hq fz1_139_28 fz2_139_28
  · exact pair_140_28 p hp hrep j hj hq
  · exact match_zero_fix ⟨141, by decide⟩ ⟨28, by decide⟩ p hp j hj hq fz1_141_28 fz2_141_28
  · exact pair_142_28 p hp hrep j hj hq
  · exact match_zero_fix ⟨143, by decide⟩ ⟨28, by decide⟩ p hp j hj hq fz1_143_28 fz2_143_28
  · exact match_zero_fix ⟨144, by decide⟩ ⟨28, by decide⟩ p hp j hj hq fz1_144_28 fz2_144_28
  · exact match_zero_fix ⟨145, by decide⟩ ⟨28, by decide⟩ p hp j hj hq fz1_145_28 fz2_145_28
  · exact match_zero_fix ⟨146, by decide⟩ ⟨28, by decide⟩ p hp j hj hq fz1_146_28 fz2_146_28
  · exact pair_147_28 p hp hrep j hj hq

theorem master_29 (p : Nat) (hp : p < (Q2.transData.getD 29 []).length)
    (hrep : (Q2.cosetIsRep.getD 29 []).getD p false = true)
    (rK : Fin 148) (j : Nat) (hj : j < (repChars.getD rK.val []).length)
    (hq : (normIsRep.getD rK.val []).getD j false = true) :
    species (Q2.reps (⟨29, by decide⟩ : Fin 148)) (colE2 ⟨29, by decide⟩ p hp)
        (rowE2 rK j hj hq)
      = species (reps (⟨29, by decide⟩ : Fin 148))
        (colE1 ⟨29, by decide⟩ p (transLenTr ⟨29, by decide⟩ p hp)) (rowE1 rK j hj) := by
  rcases rK with ⟨nK, hnK⟩; interval_cases nK
  · exact match_zero_len ⟨0, by decide⟩ ⟨29, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨1, by decide⟩ ⟨29, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨2, by decide⟩ ⟨29, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨3, by decide⟩ ⟨29, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨4, by decide⟩ ⟨29, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨5, by decide⟩ ⟨29, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨6, by decide⟩ ⟨29, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨7, by decide⟩ ⟨29, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨8, by decide⟩ ⟨29, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨9, by decide⟩ ⟨29, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨10, by decide⟩ ⟨29, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨11, by decide⟩ ⟨29, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨12, by decide⟩ ⟨29, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_fix ⟨13, by decide⟩ ⟨29, by decide⟩ p hp j hj hq fz1_13_29 fz2_13_29
  · exact match_zero_fix ⟨14, by decide⟩ ⟨29, by decide⟩ p hp j hj hq fz1_14_29 fz2_14_29
  · exact match_zero_fix ⟨15, by decide⟩ ⟨29, by decide⟩ p hp j hj hq fz1_15_29 fz2_15_29
  · exact match_zero_fix ⟨16, by decide⟩ ⟨29, by decide⟩ p hp j hj hq fz1_16_29 fz2_16_29
  · exact match_zero_fix ⟨17, by decide⟩ ⟨29, by decide⟩ p hp j hj hq fz1_17_29 fz2_17_29
  · exact match_zero_fix ⟨18, by decide⟩ ⟨29, by decide⟩ p hp j hj hq fz1_18_29 fz2_18_29
  · exact match_zero_fix ⟨19, by decide⟩ ⟨29, by decide⟩ p hp j hj hq fz1_19_29 fz2_19_29
  · exact match_zero_fix ⟨20, by decide⟩ ⟨29, by decide⟩ p hp j hj hq fz1_20_29 fz2_20_29
  · exact match_zero_fix ⟨21, by decide⟩ ⟨29, by decide⟩ p hp j hj hq fz1_21_29 fz2_21_29
  · exact match_zero_fix ⟨22, by decide⟩ ⟨29, by decide⟩ p hp j hj hq fz1_22_29 fz2_22_29
  · exact match_zero_fix ⟨23, by decide⟩ ⟨29, by decide⟩ p hp j hj hq fz1_23_29 fz2_23_29
  · exact match_zero_fix ⟨24, by decide⟩ ⟨29, by decide⟩ p hp j hj hq fz1_24_29 fz2_24_29
  · exact match_zero_fix ⟨25, by decide⟩ ⟨29, by decide⟩ p hp j hj hq fz1_25_29 fz2_25_29
  · exact match_zero_fix ⟨26, by decide⟩ ⟨29, by decide⟩ p hp j hj hq fz1_26_29 fz2_26_29
  · exact match_zero_fix ⟨27, by decide⟩ ⟨29, by decide⟩ p hp j hj hq fz1_27_29 fz2_27_29
  · exact match_zero_fix ⟨28, by decide⟩ ⟨29, by decide⟩ p hp j hj hq fz1_28_29 fz2_28_29
  · exact pair_29_29 p hp hrep j hj hq
  · exact match_zero_fix ⟨30, by decide⟩ ⟨29, by decide⟩ p hp j hj hq fz1_30_29 fz2_30_29
  · exact match_zero_fix ⟨31, by decide⟩ ⟨29, by decide⟩ p hp j hj hq fz1_31_29 fz2_31_29
  · exact match_zero_fix ⟨32, by decide⟩ ⟨29, by decide⟩ p hp j hj hq fz1_32_29 fz2_32_29
  · exact match_zero_fix ⟨33, by decide⟩ ⟨29, by decide⟩ p hp j hj hq fz1_33_29 fz2_33_29
  · exact match_zero_fix ⟨34, by decide⟩ ⟨29, by decide⟩ p hp j hj hq fz1_34_29 fz2_34_29
  · exact match_zero_fix ⟨35, by decide⟩ ⟨29, by decide⟩ p hp j hj hq fz1_35_29 fz2_35_29
  · exact match_zero_fix ⟨36, by decide⟩ ⟨29, by decide⟩ p hp j hj hq fz1_36_29 fz2_36_29
  · exact match_zero_fix ⟨37, by decide⟩ ⟨29, by decide⟩ p hp j hj hq fz1_37_29 fz2_37_29
  · exact match_zero_fix ⟨38, by decide⟩ ⟨29, by decide⟩ p hp j hj hq fz1_38_29 fz2_38_29
  · exact match_zero_fix ⟨39, by decide⟩ ⟨29, by decide⟩ p hp j hj hq fz1_39_29 fz2_39_29
  · exact match_zero_fix ⟨40, by decide⟩ ⟨29, by decide⟩ p hp j hj hq fz1_40_29 fz2_40_29
  · exact match_zero_fix ⟨41, by decide⟩ ⟨29, by decide⟩ p hp j hj hq fz1_41_29 fz2_41_29
  · exact match_zero_fix ⟨42, by decide⟩ ⟨29, by decide⟩ p hp j hj hq fz1_42_29 fz2_42_29
  · exact match_zero_fix ⟨43, by decide⟩ ⟨29, by decide⟩ p hp j hj hq fz1_43_29 fz2_43_29
  · exact match_zero_fix ⟨44, by decide⟩ ⟨29, by decide⟩ p hp j hj hq fz1_44_29 fz2_44_29
  · exact match_zero_fix ⟨45, by decide⟩ ⟨29, by decide⟩ p hp j hj hq fz1_45_29 fz2_45_29
  · exact match_zero_fix ⟨46, by decide⟩ ⟨29, by decide⟩ p hp j hj hq fz1_46_29 fz2_46_29
  · exact match_zero_fix ⟨47, by decide⟩ ⟨29, by decide⟩ p hp j hj hq fz1_47_29 fz2_47_29
  · exact match_zero_fix ⟨48, by decide⟩ ⟨29, by decide⟩ p hp j hj hq fz1_48_29 fz2_48_29
  · exact match_zero_fix ⟨49, by decide⟩ ⟨29, by decide⟩ p hp j hj hq fz1_49_29 fz2_49_29
  · exact match_zero_fix ⟨50, by decide⟩ ⟨29, by decide⟩ p hp j hj hq fz1_50_29 fz2_50_29
  · exact match_zero_fix ⟨51, by decide⟩ ⟨29, by decide⟩ p hp j hj hq fz1_51_29 fz2_51_29
  · exact match_zero_fix ⟨52, by decide⟩ ⟨29, by decide⟩ p hp j hj hq fz1_52_29 fz2_52_29
  · exact match_zero_fix ⟨53, by decide⟩ ⟨29, by decide⟩ p hp j hj hq fz1_53_29 fz2_53_29
  · exact match_zero_fix ⟨54, by decide⟩ ⟨29, by decide⟩ p hp j hj hq fz1_54_29 fz2_54_29
  · exact match_zero_fix ⟨55, by decide⟩ ⟨29, by decide⟩ p hp j hj hq fz1_55_29 fz2_55_29
  · exact match_zero_fix ⟨56, by decide⟩ ⟨29, by decide⟩ p hp j hj hq fz1_56_29 fz2_56_29
  · exact match_zero_fix ⟨57, by decide⟩ ⟨29, by decide⟩ p hp j hj hq fz1_57_29 fz2_57_29
  · exact match_zero_fix ⟨58, by decide⟩ ⟨29, by decide⟩ p hp j hj hq fz1_58_29 fz2_58_29
  · exact match_zero_fix ⟨59, by decide⟩ ⟨29, by decide⟩ p hp j hj hq fz1_59_29 fz2_59_29
  · exact pair_60_29 p hp hrep j hj hq
  · exact pair_61_29 p hp hrep j hj hq
  · exact pair_62_29 p hp hrep j hj hq
  · exact pair_63_29 p hp hrep j hj hq
  · exact pair_64_29 p hp hrep j hj hq
  · exact match_zero_fix ⟨65, by decide⟩ ⟨29, by decide⟩ p hp j hj hq fz1_65_29 fz2_65_29
  · exact match_zero_fix ⟨66, by decide⟩ ⟨29, by decide⟩ p hp j hj hq fz1_66_29 fz2_66_29
  · exact match_zero_fix ⟨67, by decide⟩ ⟨29, by decide⟩ p hp j hj hq fz1_67_29 fz2_67_29
  · exact match_zero_fix ⟨68, by decide⟩ ⟨29, by decide⟩ p hp j hj hq fz1_68_29 fz2_68_29
  · exact match_zero_fix ⟨69, by decide⟩ ⟨29, by decide⟩ p hp j hj hq fz1_69_29 fz2_69_29
  · exact match_zero_fix ⟨70, by decide⟩ ⟨29, by decide⟩ p hp j hj hq fz1_70_29 fz2_70_29
  · exact match_zero_fix ⟨71, by decide⟩ ⟨29, by decide⟩ p hp j hj hq fz1_71_29 fz2_71_29
  · exact match_zero_fix ⟨72, by decide⟩ ⟨29, by decide⟩ p hp j hj hq fz1_72_29 fz2_72_29
  · exact match_zero_fix ⟨73, by decide⟩ ⟨29, by decide⟩ p hp j hj hq fz1_73_29 fz2_73_29
  · exact match_zero_fix ⟨74, by decide⟩ ⟨29, by decide⟩ p hp j hj hq fz1_74_29 fz2_74_29
  · exact match_zero_fix ⟨75, by decide⟩ ⟨29, by decide⟩ p hp j hj hq fz1_75_29 fz2_75_29
  · exact match_zero_fix ⟨76, by decide⟩ ⟨29, by decide⟩ p hp j hj hq fz1_76_29 fz2_76_29
  · exact match_zero_fix ⟨77, by decide⟩ ⟨29, by decide⟩ p hp j hj hq fz1_77_29 fz2_77_29
  · exact match_zero_fix ⟨78, by decide⟩ ⟨29, by decide⟩ p hp j hj hq fz1_78_29 fz2_78_29
  · exact match_zero_fix ⟨79, by decide⟩ ⟨29, by decide⟩ p hp j hj hq fz1_79_29 fz2_79_29
  · exact match_zero_fix ⟨80, by decide⟩ ⟨29, by decide⟩ p hp j hj hq fz1_80_29 fz2_80_29
  · exact match_zero_fix ⟨81, by decide⟩ ⟨29, by decide⟩ p hp j hj hq fz1_81_29 fz2_81_29
  · exact match_zero_fix ⟨82, by decide⟩ ⟨29, by decide⟩ p hp j hj hq fz1_82_29 fz2_82_29
  · exact match_zero_fix ⟨83, by decide⟩ ⟨29, by decide⟩ p hp j hj hq fz1_83_29 fz2_83_29
  · exact match_zero_fix ⟨84, by decide⟩ ⟨29, by decide⟩ p hp j hj hq fz1_84_29 fz2_84_29
  · exact match_zero_fix ⟨85, by decide⟩ ⟨29, by decide⟩ p hp j hj hq fz1_85_29 fz2_85_29
  · exact match_zero_fix ⟨86, by decide⟩ ⟨29, by decide⟩ p hp j hj hq fz1_86_29 fz2_86_29
  · exact match_zero_fix ⟨87, by decide⟩ ⟨29, by decide⟩ p hp j hj hq fz1_87_29 fz2_87_29
  · exact match_zero_fix ⟨88, by decide⟩ ⟨29, by decide⟩ p hp j hj hq fz1_88_29 fz2_88_29
  · exact match_zero_fix ⟨89, by decide⟩ ⟨29, by decide⟩ p hp j hj hq fz1_89_29 fz2_89_29
  · exact match_zero_fix ⟨90, by decide⟩ ⟨29, by decide⟩ p hp j hj hq fz1_90_29 fz2_90_29
  · exact pair_91_29 p hp hrep j hj hq
  · exact match_zero_fix ⟨92, by decide⟩ ⟨29, by decide⟩ p hp j hj hq fz1_92_29 fz2_92_29
  · exact match_zero_fix ⟨93, by decide⟩ ⟨29, by decide⟩ p hp j hj hq fz1_93_29 fz2_93_29
  · exact match_zero_fix ⟨94, by decide⟩ ⟨29, by decide⟩ p hp j hj hq fz1_94_29 fz2_94_29
  · exact match_zero_fix ⟨95, by decide⟩ ⟨29, by decide⟩ p hp j hj hq fz1_95_29 fz2_95_29
  · exact match_zero_fix ⟨96, by decide⟩ ⟨29, by decide⟩ p hp j hj hq fz1_96_29 fz2_96_29
  · exact match_zero_fix ⟨97, by decide⟩ ⟨29, by decide⟩ p hp j hj hq fz1_97_29 fz2_97_29
  · exact match_zero_fix ⟨98, by decide⟩ ⟨29, by decide⟩ p hp j hj hq fz1_98_29 fz2_98_29
  · exact match_zero_fix ⟨99, by decide⟩ ⟨29, by decide⟩ p hp j hj hq fz1_99_29 fz2_99_29
  · exact match_zero_fix ⟨100, by decide⟩ ⟨29, by decide⟩ p hp j hj hq fz1_100_29 fz2_100_29
  · exact match_zero_fix ⟨101, by decide⟩ ⟨29, by decide⟩ p hp j hj hq fz1_101_29 fz2_101_29
  · exact match_zero_fix ⟨102, by decide⟩ ⟨29, by decide⟩ p hp j hj hq fz1_102_29 fz2_102_29
  · exact match_zero_fix ⟨103, by decide⟩ ⟨29, by decide⟩ p hp j hj hq fz1_103_29 fz2_103_29
  · exact match_zero_fix ⟨104, by decide⟩ ⟨29, by decide⟩ p hp j hj hq fz1_104_29 fz2_104_29
  · exact match_zero_fix ⟨105, by decide⟩ ⟨29, by decide⟩ p hp j hj hq fz1_105_29 fz2_105_29
  · exact match_zero_fix ⟨106, by decide⟩ ⟨29, by decide⟩ p hp j hj hq fz1_106_29 fz2_106_29
  · exact match_zero_fix ⟨107, by decide⟩ ⟨29, by decide⟩ p hp j hj hq fz1_107_29 fz2_107_29
  · exact match_zero_fix ⟨108, by decide⟩ ⟨29, by decide⟩ p hp j hj hq fz1_108_29 fz2_108_29
  · exact match_zero_fix ⟨109, by decide⟩ ⟨29, by decide⟩ p hp j hj hq fz1_109_29 fz2_109_29
  · exact match_zero_fix ⟨110, by decide⟩ ⟨29, by decide⟩ p hp j hj hq fz1_110_29 fz2_110_29
  · exact match_zero_fix ⟨111, by decide⟩ ⟨29, by decide⟩ p hp j hj hq fz1_111_29 fz2_111_29
  · exact match_zero_fix ⟨112, by decide⟩ ⟨29, by decide⟩ p hp j hj hq fz1_112_29 fz2_112_29
  · exact match_zero_fix ⟨113, by decide⟩ ⟨29, by decide⟩ p hp j hj hq fz1_113_29 fz2_113_29
  · exact match_zero_fix ⟨114, by decide⟩ ⟨29, by decide⟩ p hp j hj hq fz1_114_29 fz2_114_29
  · exact match_zero_fix ⟨115, by decide⟩ ⟨29, by decide⟩ p hp j hj hq fz1_115_29 fz2_115_29
  · exact match_zero_fix ⟨116, by decide⟩ ⟨29, by decide⟩ p hp j hj hq fz1_116_29 fz2_116_29
  · exact pair_117_29 p hp hrep j hj hq
  · exact match_zero_fix ⟨118, by decide⟩ ⟨29, by decide⟩ p hp j hj hq fz1_118_29 fz2_118_29
  · exact match_zero_fix ⟨119, by decide⟩ ⟨29, by decide⟩ p hp j hj hq fz1_119_29 fz2_119_29
  · exact match_zero_fix ⟨120, by decide⟩ ⟨29, by decide⟩ p hp j hj hq fz1_120_29 fz2_120_29
  · exact match_zero_fix ⟨121, by decide⟩ ⟨29, by decide⟩ p hp j hj hq fz1_121_29 fz2_121_29
  · exact match_zero_fix ⟨122, by decide⟩ ⟨29, by decide⟩ p hp j hj hq fz1_122_29 fz2_122_29
  · exact pair_123_29 p hp hrep j hj hq
  · exact match_zero_fix ⟨124, by decide⟩ ⟨29, by decide⟩ p hp j hj hq fz1_124_29 fz2_124_29
  · exact match_zero_fix ⟨125, by decide⟩ ⟨29, by decide⟩ p hp j hj hq fz1_125_29 fz2_125_29
  · exact match_zero_fix ⟨126, by decide⟩ ⟨29, by decide⟩ p hp j hj hq fz1_126_29 fz2_126_29
  · exact match_zero_fix ⟨127, by decide⟩ ⟨29, by decide⟩ p hp j hj hq fz1_127_29 fz2_127_29
  · exact match_zero_fix ⟨128, by decide⟩ ⟨29, by decide⟩ p hp j hj hq fz1_128_29 fz2_128_29
  · exact pair_129_29 p hp hrep j hj hq
  · exact match_zero_fix ⟨130, by decide⟩ ⟨29, by decide⟩ p hp j hj hq fz1_130_29 fz2_130_29
  · exact match_zero_fix ⟨131, by decide⟩ ⟨29, by decide⟩ p hp j hj hq fz1_131_29 fz2_131_29
  · exact match_zero_fix ⟨132, by decide⟩ ⟨29, by decide⟩ p hp j hj hq fz1_132_29 fz2_132_29
  · exact match_zero_fix ⟨133, by decide⟩ ⟨29, by decide⟩ p hp j hj hq fz1_133_29 fz2_133_29
  · exact match_zero_fix ⟨134, by decide⟩ ⟨29, by decide⟩ p hp j hj hq fz1_134_29 fz2_134_29
  · exact pair_135_29 p hp hrep j hj hq
  · exact pair_136_29 p hp hrep j hj hq
  · exact match_zero_fix ⟨137, by decide⟩ ⟨29, by decide⟩ p hp j hj hq fz1_137_29 fz2_137_29
  · exact match_zero_fix ⟨138, by decide⟩ ⟨29, by decide⟩ p hp j hj hq fz1_138_29 fz2_138_29
  · exact match_zero_fix ⟨139, by decide⟩ ⟨29, by decide⟩ p hp j hj hq fz1_139_29 fz2_139_29
  · exact match_zero_fix ⟨140, by decide⟩ ⟨29, by decide⟩ p hp j hj hq fz1_140_29 fz2_140_29
  · exact match_zero_fix ⟨141, by decide⟩ ⟨29, by decide⟩ p hp j hj hq fz1_141_29 fz2_141_29
  · exact pair_142_29 p hp hrep j hj hq
  · exact match_zero_fix ⟨143, by decide⟩ ⟨29, by decide⟩ p hp j hj hq fz1_143_29 fz2_143_29
  · exact match_zero_fix ⟨144, by decide⟩ ⟨29, by decide⟩ p hp j hj hq fz1_144_29 fz2_144_29
  · exact match_zero_fix ⟨145, by decide⟩ ⟨29, by decide⟩ p hp j hj hq fz1_145_29 fz2_145_29
  · exact match_zero_fix ⟨146, by decide⟩ ⟨29, by decide⟩ p hp j hj hq fz1_146_29 fz2_146_29
  · exact pair_147_29 p hp hrep j hj hq

theorem master_30 (p : Nat) (hp : p < (Q2.transData.getD 30 []).length)
    (hrep : (Q2.cosetIsRep.getD 30 []).getD p false = true)
    (rK : Fin 148) (j : Nat) (hj : j < (repChars.getD rK.val []).length)
    (hq : (normIsRep.getD rK.val []).getD j false = true) :
    species (Q2.reps (⟨30, by decide⟩ : Fin 148)) (colE2 ⟨30, by decide⟩ p hp)
        (rowE2 rK j hj hq)
      = species (reps (⟨30, by decide⟩ : Fin 148))
        (colE1 ⟨30, by decide⟩ p (transLenTr ⟨30, by decide⟩ p hp)) (rowE1 rK j hj) := by
  rcases rK with ⟨nK, hnK⟩; interval_cases nK
  · exact match_zero_len ⟨0, by decide⟩ ⟨30, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨1, by decide⟩ ⟨30, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨2, by decide⟩ ⟨30, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨3, by decide⟩ ⟨30, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨4, by decide⟩ ⟨30, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨5, by decide⟩ ⟨30, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨6, by decide⟩ ⟨30, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨7, by decide⟩ ⟨30, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨8, by decide⟩ ⟨30, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨9, by decide⟩ ⟨30, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨10, by decide⟩ ⟨30, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨11, by decide⟩ ⟨30, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨12, by decide⟩ ⟨30, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_fix ⟨13, by decide⟩ ⟨30, by decide⟩ p hp j hj hq fz1_13_30 fz2_13_30
  · exact match_zero_fix ⟨14, by decide⟩ ⟨30, by decide⟩ p hp j hj hq fz1_14_30 fz2_14_30
  · exact match_zero_fix ⟨15, by decide⟩ ⟨30, by decide⟩ p hp j hj hq fz1_15_30 fz2_15_30
  · exact match_zero_fix ⟨16, by decide⟩ ⟨30, by decide⟩ p hp j hj hq fz1_16_30 fz2_16_30
  · exact match_zero_fix ⟨17, by decide⟩ ⟨30, by decide⟩ p hp j hj hq fz1_17_30 fz2_17_30
  · exact match_zero_fix ⟨18, by decide⟩ ⟨30, by decide⟩ p hp j hj hq fz1_18_30 fz2_18_30
  · exact match_zero_fix ⟨19, by decide⟩ ⟨30, by decide⟩ p hp j hj hq fz1_19_30 fz2_19_30
  · exact match_zero_fix ⟨20, by decide⟩ ⟨30, by decide⟩ p hp j hj hq fz1_20_30 fz2_20_30
  · exact match_zero_fix ⟨21, by decide⟩ ⟨30, by decide⟩ p hp j hj hq fz1_21_30 fz2_21_30
  · exact match_zero_fix ⟨22, by decide⟩ ⟨30, by decide⟩ p hp j hj hq fz1_22_30 fz2_22_30
  · exact match_zero_fix ⟨23, by decide⟩ ⟨30, by decide⟩ p hp j hj hq fz1_23_30 fz2_23_30
  · exact match_zero_fix ⟨24, by decide⟩ ⟨30, by decide⟩ p hp j hj hq fz1_24_30 fz2_24_30
  · exact match_zero_fix ⟨25, by decide⟩ ⟨30, by decide⟩ p hp j hj hq fz1_25_30 fz2_25_30
  · exact match_zero_fix ⟨26, by decide⟩ ⟨30, by decide⟩ p hp j hj hq fz1_26_30 fz2_26_30
  · exact match_zero_fix ⟨27, by decide⟩ ⟨30, by decide⟩ p hp j hj hq fz1_27_30 fz2_27_30
  · exact match_zero_fix ⟨28, by decide⟩ ⟨30, by decide⟩ p hp j hj hq fz1_28_30 fz2_28_30
  · exact match_zero_fix ⟨29, by decide⟩ ⟨30, by decide⟩ p hp j hj hq fz1_29_30 fz2_29_30
  · exact pair_30_30 p hp hrep j hj hq
  · exact match_zero_fix ⟨31, by decide⟩ ⟨30, by decide⟩ p hp j hj hq fz1_31_30 fz2_31_30
  · exact match_zero_fix ⟨32, by decide⟩ ⟨30, by decide⟩ p hp j hj hq fz1_32_30 fz2_32_30
  · exact match_zero_fix ⟨33, by decide⟩ ⟨30, by decide⟩ p hp j hj hq fz1_33_30 fz2_33_30
  · exact match_zero_fix ⟨34, by decide⟩ ⟨30, by decide⟩ p hp j hj hq fz1_34_30 fz2_34_30
  · exact match_zero_fix ⟨35, by decide⟩ ⟨30, by decide⟩ p hp j hj hq fz1_35_30 fz2_35_30
  · exact match_zero_fix ⟨36, by decide⟩ ⟨30, by decide⟩ p hp j hj hq fz1_36_30 fz2_36_30
  · exact match_zero_fix ⟨37, by decide⟩ ⟨30, by decide⟩ p hp j hj hq fz1_37_30 fz2_37_30
  · exact match_zero_fix ⟨38, by decide⟩ ⟨30, by decide⟩ p hp j hj hq fz1_38_30 fz2_38_30
  · exact match_zero_fix ⟨39, by decide⟩ ⟨30, by decide⟩ p hp j hj hq fz1_39_30 fz2_39_30
  · exact match_zero_fix ⟨40, by decide⟩ ⟨30, by decide⟩ p hp j hj hq fz1_40_30 fz2_40_30
  · exact match_zero_fix ⟨41, by decide⟩ ⟨30, by decide⟩ p hp j hj hq fz1_41_30 fz2_41_30
  · exact match_zero_fix ⟨42, by decide⟩ ⟨30, by decide⟩ p hp j hj hq fz1_42_30 fz2_42_30
  · exact match_zero_fix ⟨43, by decide⟩ ⟨30, by decide⟩ p hp j hj hq fz1_43_30 fz2_43_30
  · exact match_zero_fix ⟨44, by decide⟩ ⟨30, by decide⟩ p hp j hj hq fz1_44_30 fz2_44_30
  · exact match_zero_fix ⟨45, by decide⟩ ⟨30, by decide⟩ p hp j hj hq fz1_45_30 fz2_45_30
  · exact match_zero_fix ⟨46, by decide⟩ ⟨30, by decide⟩ p hp j hj hq fz1_46_30 fz2_46_30
  · exact match_zero_fix ⟨47, by decide⟩ ⟨30, by decide⟩ p hp j hj hq fz1_47_30 fz2_47_30
  · exact match_zero_fix ⟨48, by decide⟩ ⟨30, by decide⟩ p hp j hj hq fz1_48_30 fz2_48_30
  · exact match_zero_fix ⟨49, by decide⟩ ⟨30, by decide⟩ p hp j hj hq fz1_49_30 fz2_49_30
  · exact match_zero_fix ⟨50, by decide⟩ ⟨30, by decide⟩ p hp j hj hq fz1_50_30 fz2_50_30
  · exact match_zero_fix ⟨51, by decide⟩ ⟨30, by decide⟩ p hp j hj hq fz1_51_30 fz2_51_30
  · exact match_zero_fix ⟨52, by decide⟩ ⟨30, by decide⟩ p hp j hj hq fz1_52_30 fz2_52_30
  · exact match_zero_fix ⟨53, by decide⟩ ⟨30, by decide⟩ p hp j hj hq fz1_53_30 fz2_53_30
  · exact match_zero_fix ⟨54, by decide⟩ ⟨30, by decide⟩ p hp j hj hq fz1_54_30 fz2_54_30
  · exact match_zero_fix ⟨55, by decide⟩ ⟨30, by decide⟩ p hp j hj hq fz1_55_30 fz2_55_30
  · exact match_zero_fix ⟨56, by decide⟩ ⟨30, by decide⟩ p hp j hj hq fz1_56_30 fz2_56_30
  · exact match_zero_fix ⟨57, by decide⟩ ⟨30, by decide⟩ p hp j hj hq fz1_57_30 fz2_57_30
  · exact match_zero_fix ⟨58, by decide⟩ ⟨30, by decide⟩ p hp j hj hq fz1_58_30 fz2_58_30
  · exact match_zero_fix ⟨59, by decide⟩ ⟨30, by decide⟩ p hp j hj hq fz1_59_30 fz2_59_30
  · exact match_zero_fix ⟨60, by decide⟩ ⟨30, by decide⟩ p hp j hj hq fz1_60_30 fz2_60_30
  · exact match_zero_fix ⟨61, by decide⟩ ⟨30, by decide⟩ p hp j hj hq fz1_61_30 fz2_61_30
  · exact match_zero_fix ⟨62, by decide⟩ ⟨30, by decide⟩ p hp j hj hq fz1_62_30 fz2_62_30
  · exact match_zero_fix ⟨63, by decide⟩ ⟨30, by decide⟩ p hp j hj hq fz1_63_30 fz2_63_30
  · exact match_zero_fix ⟨64, by decide⟩ ⟨30, by decide⟩ p hp j hj hq fz1_64_30 fz2_64_30
  · exact pair_65_30 p hp hrep j hj hq
  · exact pair_66_30 p hp hrep j hj hq
  · exact pair_67_30 p hp hrep j hj hq
  · exact pair_68_30 p hp hrep j hj hq
  · exact pair_69_30 p hp hrep j hj hq
  · exact match_zero_fix ⟨70, by decide⟩ ⟨30, by decide⟩ p hp j hj hq fz1_70_30 fz2_70_30
  · exact match_zero_fix ⟨71, by decide⟩ ⟨30, by decide⟩ p hp j hj hq fz1_71_30 fz2_71_30
  · exact match_zero_fix ⟨72, by decide⟩ ⟨30, by decide⟩ p hp j hj hq fz1_72_30 fz2_72_30
  · exact match_zero_fix ⟨73, by decide⟩ ⟨30, by decide⟩ p hp j hj hq fz1_73_30 fz2_73_30
  · exact match_zero_fix ⟨74, by decide⟩ ⟨30, by decide⟩ p hp j hj hq fz1_74_30 fz2_74_30
  · exact match_zero_fix ⟨75, by decide⟩ ⟨30, by decide⟩ p hp j hj hq fz1_75_30 fz2_75_30
  · exact match_zero_fix ⟨76, by decide⟩ ⟨30, by decide⟩ p hp j hj hq fz1_76_30 fz2_76_30
  · exact match_zero_fix ⟨77, by decide⟩ ⟨30, by decide⟩ p hp j hj hq fz1_77_30 fz2_77_30
  · exact match_zero_fix ⟨78, by decide⟩ ⟨30, by decide⟩ p hp j hj hq fz1_78_30 fz2_78_30
  · exact match_zero_fix ⟨79, by decide⟩ ⟨30, by decide⟩ p hp j hj hq fz1_79_30 fz2_79_30
  · exact match_zero_fix ⟨80, by decide⟩ ⟨30, by decide⟩ p hp j hj hq fz1_80_30 fz2_80_30
  · exact match_zero_fix ⟨81, by decide⟩ ⟨30, by decide⟩ p hp j hj hq fz1_81_30 fz2_81_30
  · exact match_zero_fix ⟨82, by decide⟩ ⟨30, by decide⟩ p hp j hj hq fz1_82_30 fz2_82_30
  · exact match_zero_fix ⟨83, by decide⟩ ⟨30, by decide⟩ p hp j hj hq fz1_83_30 fz2_83_30
  · exact match_zero_fix ⟨84, by decide⟩ ⟨30, by decide⟩ p hp j hj hq fz1_84_30 fz2_84_30
  · exact match_zero_fix ⟨85, by decide⟩ ⟨30, by decide⟩ p hp j hj hq fz1_85_30 fz2_85_30
  · exact match_zero_fix ⟨86, by decide⟩ ⟨30, by decide⟩ p hp j hj hq fz1_86_30 fz2_86_30
  · exact match_zero_fix ⟨87, by decide⟩ ⟨30, by decide⟩ p hp j hj hq fz1_87_30 fz2_87_30
  · exact match_zero_fix ⟨88, by decide⟩ ⟨30, by decide⟩ p hp j hj hq fz1_88_30 fz2_88_30
  · exact match_zero_fix ⟨89, by decide⟩ ⟨30, by decide⟩ p hp j hj hq fz1_89_30 fz2_89_30
  · exact match_zero_fix ⟨90, by decide⟩ ⟨30, by decide⟩ p hp j hj hq fz1_90_30 fz2_90_30
  · exact match_zero_fix ⟨91, by decide⟩ ⟨30, by decide⟩ p hp j hj hq fz1_91_30 fz2_91_30
  · exact pair_92_30 p hp hrep j hj hq
  · exact match_zero_fix ⟨93, by decide⟩ ⟨30, by decide⟩ p hp j hj hq fz1_93_30 fz2_93_30
  · exact match_zero_fix ⟨94, by decide⟩ ⟨30, by decide⟩ p hp j hj hq fz1_94_30 fz2_94_30
  · exact match_zero_fix ⟨95, by decide⟩ ⟨30, by decide⟩ p hp j hj hq fz1_95_30 fz2_95_30
  · exact match_zero_fix ⟨96, by decide⟩ ⟨30, by decide⟩ p hp j hj hq fz1_96_30 fz2_96_30
  · exact match_zero_fix ⟨97, by decide⟩ ⟨30, by decide⟩ p hp j hj hq fz1_97_30 fz2_97_30
  · exact match_zero_fix ⟨98, by decide⟩ ⟨30, by decide⟩ p hp j hj hq fz1_98_30 fz2_98_30
  · exact match_zero_fix ⟨99, by decide⟩ ⟨30, by decide⟩ p hp j hj hq fz1_99_30 fz2_99_30
  · exact match_zero_fix ⟨100, by decide⟩ ⟨30, by decide⟩ p hp j hj hq fz1_100_30 fz2_100_30
  · exact match_zero_fix ⟨101, by decide⟩ ⟨30, by decide⟩ p hp j hj hq fz1_101_30 fz2_101_30
  · exact match_zero_fix ⟨102, by decide⟩ ⟨30, by decide⟩ p hp j hj hq fz1_102_30 fz2_102_30
  · exact match_zero_fix ⟨103, by decide⟩ ⟨30, by decide⟩ p hp j hj hq fz1_103_30 fz2_103_30
  · exact match_zero_fix ⟨104, by decide⟩ ⟨30, by decide⟩ p hp j hj hq fz1_104_30 fz2_104_30
  · exact match_zero_fix ⟨105, by decide⟩ ⟨30, by decide⟩ p hp j hj hq fz1_105_30 fz2_105_30
  · exact match_zero_fix ⟨106, by decide⟩ ⟨30, by decide⟩ p hp j hj hq fz1_106_30 fz2_106_30
  · exact match_zero_fix ⟨107, by decide⟩ ⟨30, by decide⟩ p hp j hj hq fz1_107_30 fz2_107_30
  · exact match_zero_fix ⟨108, by decide⟩ ⟨30, by decide⟩ p hp j hj hq fz1_108_30 fz2_108_30
  · exact match_zero_fix ⟨109, by decide⟩ ⟨30, by decide⟩ p hp j hj hq fz1_109_30 fz2_109_30
  · exact match_zero_fix ⟨110, by decide⟩ ⟨30, by decide⟩ p hp j hj hq fz1_110_30 fz2_110_30
  · exact match_zero_fix ⟨111, by decide⟩ ⟨30, by decide⟩ p hp j hj hq fz1_111_30 fz2_111_30
  · exact match_zero_fix ⟨112, by decide⟩ ⟨30, by decide⟩ p hp j hj hq fz1_112_30 fz2_112_30
  · exact match_zero_fix ⟨113, by decide⟩ ⟨30, by decide⟩ p hp j hj hq fz1_113_30 fz2_113_30
  · exact match_zero_fix ⟨114, by decide⟩ ⟨30, by decide⟩ p hp j hj hq fz1_114_30 fz2_114_30
  · exact match_zero_fix ⟨115, by decide⟩ ⟨30, by decide⟩ p hp j hj hq fz1_115_30 fz2_115_30
  · exact match_zero_fix ⟨116, by decide⟩ ⟨30, by decide⟩ p hp j hj hq fz1_116_30 fz2_116_30
  · exact match_zero_fix ⟨117, by decide⟩ ⟨30, by decide⟩ p hp j hj hq fz1_117_30 fz2_117_30
  · exact pair_118_30 p hp hrep j hj hq
  · exact match_zero_fix ⟨119, by decide⟩ ⟨30, by decide⟩ p hp j hj hq fz1_119_30 fz2_119_30
  · exact match_zero_fix ⟨120, by decide⟩ ⟨30, by decide⟩ p hp j hj hq fz1_120_30 fz2_120_30
  · exact match_zero_fix ⟨121, by decide⟩ ⟨30, by decide⟩ p hp j hj hq fz1_121_30 fz2_121_30
  · exact match_zero_fix ⟨122, by decide⟩ ⟨30, by decide⟩ p hp j hj hq fz1_122_30 fz2_122_30
  · exact match_zero_fix ⟨123, by decide⟩ ⟨30, by decide⟩ p hp j hj hq fz1_123_30 fz2_123_30
  · exact pair_124_30 p hp hrep j hj hq
  · exact match_zero_fix ⟨125, by decide⟩ ⟨30, by decide⟩ p hp j hj hq fz1_125_30 fz2_125_30
  · exact match_zero_fix ⟨126, by decide⟩ ⟨30, by decide⟩ p hp j hj hq fz1_126_30 fz2_126_30
  · exact match_zero_fix ⟨127, by decide⟩ ⟨30, by decide⟩ p hp j hj hq fz1_127_30 fz2_127_30
  · exact match_zero_fix ⟨128, by decide⟩ ⟨30, by decide⟩ p hp j hj hq fz1_128_30 fz2_128_30
  · exact match_zero_fix ⟨129, by decide⟩ ⟨30, by decide⟩ p hp j hj hq fz1_129_30 fz2_129_30
  · exact pair_130_30 p hp hrep j hj hq
  · exact pair_131_30 p hp hrep j hj hq
  · exact match_zero_fix ⟨132, by decide⟩ ⟨30, by decide⟩ p hp j hj hq fz1_132_30 fz2_132_30
  · exact match_zero_fix ⟨133, by decide⟩ ⟨30, by decide⟩ p hp j hj hq fz1_133_30 fz2_133_30
  · exact match_zero_fix ⟨134, by decide⟩ ⟨30, by decide⟩ p hp j hj hq fz1_134_30 fz2_134_30
  · exact match_zero_fix ⟨135, by decide⟩ ⟨30, by decide⟩ p hp j hj hq fz1_135_30 fz2_135_30
  · exact match_zero_fix ⟨136, by decide⟩ ⟨30, by decide⟩ p hp j hj hq fz1_136_30 fz2_136_30
  · exact pair_137_30 p hp hrep j hj hq
  · exact match_zero_fix ⟨138, by decide⟩ ⟨30, by decide⟩ p hp j hj hq fz1_138_30 fz2_138_30
  · exact match_zero_fix ⟨139, by decide⟩ ⟨30, by decide⟩ p hp j hj hq fz1_139_30 fz2_139_30
  · exact match_zero_fix ⟨140, by decide⟩ ⟨30, by decide⟩ p hp j hj hq fz1_140_30 fz2_140_30
  · exact match_zero_fix ⟨141, by decide⟩ ⟨30, by decide⟩ p hp j hj hq fz1_141_30 fz2_141_30
  · exact pair_142_30 p hp hrep j hj hq
  · exact match_zero_fix ⟨143, by decide⟩ ⟨30, by decide⟩ p hp j hj hq fz1_143_30 fz2_143_30
  · exact match_zero_fix ⟨144, by decide⟩ ⟨30, by decide⟩ p hp j hj hq fz1_144_30 fz2_144_30
  · exact match_zero_fix ⟨145, by decide⟩ ⟨30, by decide⟩ p hp j hj hq fz1_145_30 fz2_145_30
  · exact match_zero_fix ⟨146, by decide⟩ ⟨30, by decide⟩ p hp j hj hq fz1_146_30 fz2_146_30
  · exact pair_147_30 p hp hrep j hj hq

theorem master_31 (p : Nat) (hp : p < (Q2.transData.getD 31 []).length)
    (hrep : (Q2.cosetIsRep.getD 31 []).getD p false = true)
    (rK : Fin 148) (j : Nat) (hj : j < (repChars.getD rK.val []).length)
    (hq : (normIsRep.getD rK.val []).getD j false = true) :
    species (Q2.reps (⟨31, by decide⟩ : Fin 148)) (colE2 ⟨31, by decide⟩ p hp)
        (rowE2 rK j hj hq)
      = species (reps (⟨31, by decide⟩ : Fin 148))
        (colE1 ⟨31, by decide⟩ p (transLenTr ⟨31, by decide⟩ p hp)) (rowE1 rK j hj) := by
  rcases rK with ⟨nK, hnK⟩; interval_cases nK
  · exact match_zero_len ⟨0, by decide⟩ ⟨31, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨1, by decide⟩ ⟨31, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨2, by decide⟩ ⟨31, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨3, by decide⟩ ⟨31, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨4, by decide⟩ ⟨31, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨5, by decide⟩ ⟨31, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨6, by decide⟩ ⟨31, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨7, by decide⟩ ⟨31, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨8, by decide⟩ ⟨31, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨9, by decide⟩ ⟨31, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨10, by decide⟩ ⟨31, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨11, by decide⟩ ⟨31, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨12, by decide⟩ ⟨31, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_fix ⟨13, by decide⟩ ⟨31, by decide⟩ p hp j hj hq fz1_13_31 fz2_13_31
  · exact match_zero_fix ⟨14, by decide⟩ ⟨31, by decide⟩ p hp j hj hq fz1_14_31 fz2_14_31
  · exact match_zero_fix ⟨15, by decide⟩ ⟨31, by decide⟩ p hp j hj hq fz1_15_31 fz2_15_31
  · exact match_zero_fix ⟨16, by decide⟩ ⟨31, by decide⟩ p hp j hj hq fz1_16_31 fz2_16_31
  · exact match_zero_fix ⟨17, by decide⟩ ⟨31, by decide⟩ p hp j hj hq fz1_17_31 fz2_17_31
  · exact match_zero_fix ⟨18, by decide⟩ ⟨31, by decide⟩ p hp j hj hq fz1_18_31 fz2_18_31
  · exact match_zero_fix ⟨19, by decide⟩ ⟨31, by decide⟩ p hp j hj hq fz1_19_31 fz2_19_31
  · exact match_zero_fix ⟨20, by decide⟩ ⟨31, by decide⟩ p hp j hj hq fz1_20_31 fz2_20_31
  · exact match_zero_fix ⟨21, by decide⟩ ⟨31, by decide⟩ p hp j hj hq fz1_21_31 fz2_21_31
  · exact match_zero_fix ⟨22, by decide⟩ ⟨31, by decide⟩ p hp j hj hq fz1_22_31 fz2_22_31
  · exact match_zero_fix ⟨23, by decide⟩ ⟨31, by decide⟩ p hp j hj hq fz1_23_31 fz2_23_31
  · exact match_zero_fix ⟨24, by decide⟩ ⟨31, by decide⟩ p hp j hj hq fz1_24_31 fz2_24_31
  · exact match_zero_fix ⟨25, by decide⟩ ⟨31, by decide⟩ p hp j hj hq fz1_25_31 fz2_25_31
  · exact match_zero_fix ⟨26, by decide⟩ ⟨31, by decide⟩ p hp j hj hq fz1_26_31 fz2_26_31
  · exact match_zero_fix ⟨27, by decide⟩ ⟨31, by decide⟩ p hp j hj hq fz1_27_31 fz2_27_31
  · exact match_zero_fix ⟨28, by decide⟩ ⟨31, by decide⟩ p hp j hj hq fz1_28_31 fz2_28_31
  · exact match_zero_fix ⟨29, by decide⟩ ⟨31, by decide⟩ p hp j hj hq fz1_29_31 fz2_29_31
  · exact match_zero_fix ⟨30, by decide⟩ ⟨31, by decide⟩ p hp j hj hq fz1_30_31 fz2_30_31
  · exact pair_31_31 p hp hrep j hj hq
  · exact match_zero_fix ⟨32, by decide⟩ ⟨31, by decide⟩ p hp j hj hq fz1_32_31 fz2_32_31
  · exact match_zero_fix ⟨33, by decide⟩ ⟨31, by decide⟩ p hp j hj hq fz1_33_31 fz2_33_31
  · exact match_zero_fix ⟨34, by decide⟩ ⟨31, by decide⟩ p hp j hj hq fz1_34_31 fz2_34_31
  · exact match_zero_fix ⟨35, by decide⟩ ⟨31, by decide⟩ p hp j hj hq fz1_35_31 fz2_35_31
  · exact match_zero_fix ⟨36, by decide⟩ ⟨31, by decide⟩ p hp j hj hq fz1_36_31 fz2_36_31
  · exact match_zero_fix ⟨37, by decide⟩ ⟨31, by decide⟩ p hp j hj hq fz1_37_31 fz2_37_31
  · exact match_zero_fix ⟨38, by decide⟩ ⟨31, by decide⟩ p hp j hj hq fz1_38_31 fz2_38_31
  · exact match_zero_fix ⟨39, by decide⟩ ⟨31, by decide⟩ p hp j hj hq fz1_39_31 fz2_39_31
  · exact match_zero_fix ⟨40, by decide⟩ ⟨31, by decide⟩ p hp j hj hq fz1_40_31 fz2_40_31
  · exact match_zero_fix ⟨41, by decide⟩ ⟨31, by decide⟩ p hp j hj hq fz1_41_31 fz2_41_31
  · exact match_zero_fix ⟨42, by decide⟩ ⟨31, by decide⟩ p hp j hj hq fz1_42_31 fz2_42_31
  · exact match_zero_fix ⟨43, by decide⟩ ⟨31, by decide⟩ p hp j hj hq fz1_43_31 fz2_43_31
  · exact match_zero_fix ⟨44, by decide⟩ ⟨31, by decide⟩ p hp j hj hq fz1_44_31 fz2_44_31
  · exact match_zero_fix ⟨45, by decide⟩ ⟨31, by decide⟩ p hp j hj hq fz1_45_31 fz2_45_31
  · exact match_zero_fix ⟨46, by decide⟩ ⟨31, by decide⟩ p hp j hj hq fz1_46_31 fz2_46_31
  · exact match_zero_fix ⟨47, by decide⟩ ⟨31, by decide⟩ p hp j hj hq fz1_47_31 fz2_47_31
  · exact match_zero_fix ⟨48, by decide⟩ ⟨31, by decide⟩ p hp j hj hq fz1_48_31 fz2_48_31
  · exact match_zero_fix ⟨49, by decide⟩ ⟨31, by decide⟩ p hp j hj hq fz1_49_31 fz2_49_31
  · exact match_zero_fix ⟨50, by decide⟩ ⟨31, by decide⟩ p hp j hj hq fz1_50_31 fz2_50_31
  · exact match_zero_fix ⟨51, by decide⟩ ⟨31, by decide⟩ p hp j hj hq fz1_51_31 fz2_51_31
  · exact match_zero_fix ⟨52, by decide⟩ ⟨31, by decide⟩ p hp j hj hq fz1_52_31 fz2_52_31
  · exact match_zero_fix ⟨53, by decide⟩ ⟨31, by decide⟩ p hp j hj hq fz1_53_31 fz2_53_31
  · exact match_zero_fix ⟨54, by decide⟩ ⟨31, by decide⟩ p hp j hj hq fz1_54_31 fz2_54_31
  · exact match_zero_fix ⟨55, by decide⟩ ⟨31, by decide⟩ p hp j hj hq fz1_55_31 fz2_55_31
  · exact match_zero_fix ⟨56, by decide⟩ ⟨31, by decide⟩ p hp j hj hq fz1_56_31 fz2_56_31
  · exact match_zero_fix ⟨57, by decide⟩ ⟨31, by decide⟩ p hp j hj hq fz1_57_31 fz2_57_31
  · exact match_zero_fix ⟨58, by decide⟩ ⟨31, by decide⟩ p hp j hj hq fz1_58_31 fz2_58_31
  · exact match_zero_fix ⟨59, by decide⟩ ⟨31, by decide⟩ p hp j hj hq fz1_59_31 fz2_59_31
  · exact match_zero_fix ⟨60, by decide⟩ ⟨31, by decide⟩ p hp j hj hq fz1_60_31 fz2_60_31
  · exact match_zero_fix ⟨61, by decide⟩ ⟨31, by decide⟩ p hp j hj hq fz1_61_31 fz2_61_31
  · exact match_zero_fix ⟨62, by decide⟩ ⟨31, by decide⟩ p hp j hj hq fz1_62_31 fz2_62_31
  · exact match_zero_fix ⟨63, by decide⟩ ⟨31, by decide⟩ p hp j hj hq fz1_63_31 fz2_63_31
  · exact match_zero_fix ⟨64, by decide⟩ ⟨31, by decide⟩ p hp j hj hq fz1_64_31 fz2_64_31
  · exact match_zero_fix ⟨65, by decide⟩ ⟨31, by decide⟩ p hp j hj hq fz1_65_31 fz2_65_31
  · exact match_zero_fix ⟨66, by decide⟩ ⟨31, by decide⟩ p hp j hj hq fz1_66_31 fz2_66_31
  · exact match_zero_fix ⟨67, by decide⟩ ⟨31, by decide⟩ p hp j hj hq fz1_67_31 fz2_67_31
  · exact match_zero_fix ⟨68, by decide⟩ ⟨31, by decide⟩ p hp j hj hq fz1_68_31 fz2_68_31
  · exact match_zero_fix ⟨69, by decide⟩ ⟨31, by decide⟩ p hp j hj hq fz1_69_31 fz2_69_31
  · exact pair_70_31 p hp hrep j hj hq
  · exact pair_71_31 p hp hrep j hj hq
  · exact pair_72_31 p hp hrep j hj hq
  · exact pair_73_31 p hp hrep j hj hq
  · exact pair_74_31 p hp hrep j hj hq
  · exact match_zero_fix ⟨75, by decide⟩ ⟨31, by decide⟩ p hp j hj hq fz1_75_31 fz2_75_31
  · exact match_zero_fix ⟨76, by decide⟩ ⟨31, by decide⟩ p hp j hj hq fz1_76_31 fz2_76_31
  · exact match_zero_fix ⟨77, by decide⟩ ⟨31, by decide⟩ p hp j hj hq fz1_77_31 fz2_77_31
  · exact match_zero_fix ⟨78, by decide⟩ ⟨31, by decide⟩ p hp j hj hq fz1_78_31 fz2_78_31
  · exact match_zero_fix ⟨79, by decide⟩ ⟨31, by decide⟩ p hp j hj hq fz1_79_31 fz2_79_31
  · exact match_zero_fix ⟨80, by decide⟩ ⟨31, by decide⟩ p hp j hj hq fz1_80_31 fz2_80_31
  · exact match_zero_fix ⟨81, by decide⟩ ⟨31, by decide⟩ p hp j hj hq fz1_81_31 fz2_81_31
  · exact match_zero_fix ⟨82, by decide⟩ ⟨31, by decide⟩ p hp j hj hq fz1_82_31 fz2_82_31
  · exact match_zero_fix ⟨83, by decide⟩ ⟨31, by decide⟩ p hp j hj hq fz1_83_31 fz2_83_31
  · exact match_zero_fix ⟨84, by decide⟩ ⟨31, by decide⟩ p hp j hj hq fz1_84_31 fz2_84_31
  · exact match_zero_fix ⟨85, by decide⟩ ⟨31, by decide⟩ p hp j hj hq fz1_85_31 fz2_85_31
  · exact match_zero_fix ⟨86, by decide⟩ ⟨31, by decide⟩ p hp j hj hq fz1_86_31 fz2_86_31
  · exact match_zero_fix ⟨87, by decide⟩ ⟨31, by decide⟩ p hp j hj hq fz1_87_31 fz2_87_31
  · exact match_zero_fix ⟨88, by decide⟩ ⟨31, by decide⟩ p hp j hj hq fz1_88_31 fz2_88_31
  · exact match_zero_fix ⟨89, by decide⟩ ⟨31, by decide⟩ p hp j hj hq fz1_89_31 fz2_89_31
  · exact match_zero_fix ⟨90, by decide⟩ ⟨31, by decide⟩ p hp j hj hq fz1_90_31 fz2_90_31
  · exact match_zero_fix ⟨91, by decide⟩ ⟨31, by decide⟩ p hp j hj hq fz1_91_31 fz2_91_31
  · exact match_zero_fix ⟨92, by decide⟩ ⟨31, by decide⟩ p hp j hj hq fz1_92_31 fz2_92_31
  · exact pair_93_31 p hp hrep j hj hq
  · exact match_zero_fix ⟨94, by decide⟩ ⟨31, by decide⟩ p hp j hj hq fz1_94_31 fz2_94_31
  · exact match_zero_fix ⟨95, by decide⟩ ⟨31, by decide⟩ p hp j hj hq fz1_95_31 fz2_95_31
  · exact match_zero_fix ⟨96, by decide⟩ ⟨31, by decide⟩ p hp j hj hq fz1_96_31 fz2_96_31
  · exact match_zero_fix ⟨97, by decide⟩ ⟨31, by decide⟩ p hp j hj hq fz1_97_31 fz2_97_31
  · exact match_zero_fix ⟨98, by decide⟩ ⟨31, by decide⟩ p hp j hj hq fz1_98_31 fz2_98_31
  · exact match_zero_fix ⟨99, by decide⟩ ⟨31, by decide⟩ p hp j hj hq fz1_99_31 fz2_99_31
  · exact match_zero_fix ⟨100, by decide⟩ ⟨31, by decide⟩ p hp j hj hq fz1_100_31 fz2_100_31
  · exact match_zero_fix ⟨101, by decide⟩ ⟨31, by decide⟩ p hp j hj hq fz1_101_31 fz2_101_31
  · exact match_zero_fix ⟨102, by decide⟩ ⟨31, by decide⟩ p hp j hj hq fz1_102_31 fz2_102_31
  · exact match_zero_fix ⟨103, by decide⟩ ⟨31, by decide⟩ p hp j hj hq fz1_103_31 fz2_103_31
  · exact match_zero_fix ⟨104, by decide⟩ ⟨31, by decide⟩ p hp j hj hq fz1_104_31 fz2_104_31
  · exact match_zero_fix ⟨105, by decide⟩ ⟨31, by decide⟩ p hp j hj hq fz1_105_31 fz2_105_31
  · exact match_zero_fix ⟨106, by decide⟩ ⟨31, by decide⟩ p hp j hj hq fz1_106_31 fz2_106_31
  · exact match_zero_fix ⟨107, by decide⟩ ⟨31, by decide⟩ p hp j hj hq fz1_107_31 fz2_107_31
  · exact match_zero_fix ⟨108, by decide⟩ ⟨31, by decide⟩ p hp j hj hq fz1_108_31 fz2_108_31
  · exact match_zero_fix ⟨109, by decide⟩ ⟨31, by decide⟩ p hp j hj hq fz1_109_31 fz2_109_31
  · exact match_zero_fix ⟨110, by decide⟩ ⟨31, by decide⟩ p hp j hj hq fz1_110_31 fz2_110_31
  · exact match_zero_fix ⟨111, by decide⟩ ⟨31, by decide⟩ p hp j hj hq fz1_111_31 fz2_111_31
  · exact match_zero_fix ⟨112, by decide⟩ ⟨31, by decide⟩ p hp j hj hq fz1_112_31 fz2_112_31
  · exact match_zero_fix ⟨113, by decide⟩ ⟨31, by decide⟩ p hp j hj hq fz1_113_31 fz2_113_31
  · exact match_zero_fix ⟨114, by decide⟩ ⟨31, by decide⟩ p hp j hj hq fz1_114_31 fz2_114_31
  · exact match_zero_fix ⟨115, by decide⟩ ⟨31, by decide⟩ p hp j hj hq fz1_115_31 fz2_115_31
  · exact match_zero_fix ⟨116, by decide⟩ ⟨31, by decide⟩ p hp j hj hq fz1_116_31 fz2_116_31
  · exact match_zero_fix ⟨117, by decide⟩ ⟨31, by decide⟩ p hp j hj hq fz1_117_31 fz2_117_31
  · exact match_zero_fix ⟨118, by decide⟩ ⟨31, by decide⟩ p hp j hj hq fz1_118_31 fz2_118_31
  · exact pair_119_31 p hp hrep j hj hq
  · exact match_zero_fix ⟨120, by decide⟩ ⟨31, by decide⟩ p hp j hj hq fz1_120_31 fz2_120_31
  · exact match_zero_fix ⟨121, by decide⟩ ⟨31, by decide⟩ p hp j hj hq fz1_121_31 fz2_121_31
  · exact match_zero_fix ⟨122, by decide⟩ ⟨31, by decide⟩ p hp j hj hq fz1_122_31 fz2_122_31
  · exact match_zero_fix ⟨123, by decide⟩ ⟨31, by decide⟩ p hp j hj hq fz1_123_31 fz2_123_31
  · exact match_zero_fix ⟨124, by decide⟩ ⟨31, by decide⟩ p hp j hj hq fz1_124_31 fz2_124_31
  · exact pair_125_31 p hp hrep j hj hq
  · exact pair_126_31 p hp hrep j hj hq
  · exact match_zero_fix ⟨127, by decide⟩ ⟨31, by decide⟩ p hp j hj hq fz1_127_31 fz2_127_31
  · exact match_zero_fix ⟨128, by decide⟩ ⟨31, by decide⟩ p hp j hj hq fz1_128_31 fz2_128_31
  · exact match_zero_fix ⟨129, by decide⟩ ⟨31, by decide⟩ p hp j hj hq fz1_129_31 fz2_129_31
  · exact match_zero_fix ⟨130, by decide⟩ ⟨31, by decide⟩ p hp j hj hq fz1_130_31 fz2_130_31
  · exact match_zero_fix ⟨131, by decide⟩ ⟨31, by decide⟩ p hp j hj hq fz1_131_31 fz2_131_31
  · exact pair_132_31 p hp hrep j hj hq
  · exact match_zero_fix ⟨133, by decide⟩ ⟨31, by decide⟩ p hp j hj hq fz1_133_31 fz2_133_31
  · exact match_zero_fix ⟨134, by decide⟩ ⟨31, by decide⟩ p hp j hj hq fz1_134_31 fz2_134_31
  · exact match_zero_fix ⟨135, by decide⟩ ⟨31, by decide⟩ p hp j hj hq fz1_135_31 fz2_135_31
  · exact match_zero_fix ⟨136, by decide⟩ ⟨31, by decide⟩ p hp j hj hq fz1_136_31 fz2_136_31
  · exact match_zero_fix ⟨137, by decide⟩ ⟨31, by decide⟩ p hp j hj hq fz1_137_31 fz2_137_31
  · exact pair_138_31 p hp hrep j hj hq
  · exact match_zero_fix ⟨139, by decide⟩ ⟨31, by decide⟩ p hp j hj hq fz1_139_31 fz2_139_31
  · exact match_zero_fix ⟨140, by decide⟩ ⟨31, by decide⟩ p hp j hj hq fz1_140_31 fz2_140_31
  · exact match_zero_fix ⟨141, by decide⟩ ⟨31, by decide⟩ p hp j hj hq fz1_141_31 fz2_141_31
  · exact pair_142_31 p hp hrep j hj hq
  · exact match_zero_fix ⟨143, by decide⟩ ⟨31, by decide⟩ p hp j hj hq fz1_143_31 fz2_143_31
  · exact match_zero_fix ⟨144, by decide⟩ ⟨31, by decide⟩ p hp j hj hq fz1_144_31 fz2_144_31
  · exact match_zero_fix ⟨145, by decide⟩ ⟨31, by decide⟩ p hp j hj hq fz1_145_31 fz2_145_31
  · exact match_zero_fix ⟨146, by decide⟩ ⟨31, by decide⟩ p hp j hj hq fz1_146_31 fz2_146_31
  · exact pair_147_31 p hp hrep j hj hq

end LeanDring.P5Presentation
