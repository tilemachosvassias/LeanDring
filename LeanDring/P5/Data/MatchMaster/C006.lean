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

/-! # Stage-5 per-column-class master theorems, chunk 5 (auto-emitted).  -/

namespace LeanDring.P5Presentation

open MulAction Finset LeanDring.DRing LeanDring.MonGSet

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.style.longLine false

theorem master_40 (p : Nat) (hp : p < (Q2.transData.getD 40 []).length)
    (hrep : (Q2.cosetIsRep.getD 40 []).getD p false = true)
    (rK : Fin 148) (j : Nat) (hj : j < (repChars.getD rK.val []).length)
    (hq : (normIsRep.getD rK.val []).getD j false = true) :
    species (Q2.reps (⟨40, by decide⟩ : Fin 148)) (colE2 ⟨40, by decide⟩ p hp)
        (rowE2 rK j hj hq)
      = species (reps (⟨40, by decide⟩ : Fin 148))
        (colE1 ⟨40, by decide⟩ p (transLenTr ⟨40, by decide⟩ p hp)) (rowE1 rK j hj) := by
  rcases rK with ⟨nK, hnK⟩; interval_cases nK
  · exact match_zero_len ⟨0, by decide⟩ ⟨40, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨1, by decide⟩ ⟨40, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨2, by decide⟩ ⟨40, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨3, by decide⟩ ⟨40, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨4, by decide⟩ ⟨40, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨5, by decide⟩ ⟨40, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨6, by decide⟩ ⟨40, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨7, by decide⟩ ⟨40, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨8, by decide⟩ ⟨40, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨9, by decide⟩ ⟨40, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨10, by decide⟩ ⟨40, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨11, by decide⟩ ⟨40, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨12, by decide⟩ ⟨40, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_fix ⟨13, by decide⟩ ⟨40, by decide⟩ p hp j hj hq fz1_13_40 fz2_13_40
  · exact match_zero_fix ⟨14, by decide⟩ ⟨40, by decide⟩ p hp j hj hq fz1_14_40 fz2_14_40
  · exact match_zero_fix ⟨15, by decide⟩ ⟨40, by decide⟩ p hp j hj hq fz1_15_40 fz2_15_40
  · exact match_zero_fix ⟨16, by decide⟩ ⟨40, by decide⟩ p hp j hj hq fz1_16_40 fz2_16_40
  · exact match_zero_fix ⟨17, by decide⟩ ⟨40, by decide⟩ p hp j hj hq fz1_17_40 fz2_17_40
  · exact match_zero_fix ⟨18, by decide⟩ ⟨40, by decide⟩ p hp j hj hq fz1_18_40 fz2_18_40
  · exact match_zero_fix ⟨19, by decide⟩ ⟨40, by decide⟩ p hp j hj hq fz1_19_40 fz2_19_40
  · exact match_zero_fix ⟨20, by decide⟩ ⟨40, by decide⟩ p hp j hj hq fz1_20_40 fz2_20_40
  · exact match_zero_fix ⟨21, by decide⟩ ⟨40, by decide⟩ p hp j hj hq fz1_21_40 fz2_21_40
  · exact match_zero_fix ⟨22, by decide⟩ ⟨40, by decide⟩ p hp j hj hq fz1_22_40 fz2_22_40
  · exact match_zero_fix ⟨23, by decide⟩ ⟨40, by decide⟩ p hp j hj hq fz1_23_40 fz2_23_40
  · exact match_zero_fix ⟨24, by decide⟩ ⟨40, by decide⟩ p hp j hj hq fz1_24_40 fz2_24_40
  · exact match_zero_fix ⟨25, by decide⟩ ⟨40, by decide⟩ p hp j hj hq fz1_25_40 fz2_25_40
  · exact match_zero_fix ⟨26, by decide⟩ ⟨40, by decide⟩ p hp j hj hq fz1_26_40 fz2_26_40
  · exact match_zero_fix ⟨27, by decide⟩ ⟨40, by decide⟩ p hp j hj hq fz1_27_40 fz2_27_40
  · exact match_zero_fix ⟨28, by decide⟩ ⟨40, by decide⟩ p hp j hj hq fz1_28_40 fz2_28_40
  · exact match_zero_fix ⟨29, by decide⟩ ⟨40, by decide⟩ p hp j hj hq fz1_29_40 fz2_29_40
  · exact match_zero_fix ⟨30, by decide⟩ ⟨40, by decide⟩ p hp j hj hq fz1_30_40 fz2_30_40
  · exact match_zero_fix ⟨31, by decide⟩ ⟨40, by decide⟩ p hp j hj hq fz1_31_40 fz2_31_40
  · exact match_zero_fix ⟨32, by decide⟩ ⟨40, by decide⟩ p hp j hj hq fz1_32_40 fz2_32_40
  · exact match_zero_fix ⟨33, by decide⟩ ⟨40, by decide⟩ p hp j hj hq fz1_33_40 fz2_33_40
  · exact match_zero_fix ⟨34, by decide⟩ ⟨40, by decide⟩ p hp j hj hq fz1_34_40 fz2_34_40
  · exact match_zero_fix ⟨35, by decide⟩ ⟨40, by decide⟩ p hp j hj hq fz1_35_40 fz2_35_40
  · exact match_zero_fix ⟨36, by decide⟩ ⟨40, by decide⟩ p hp j hj hq fz1_36_40 fz2_36_40
  · exact match_zero_fix ⟨37, by decide⟩ ⟨40, by decide⟩ p hp j hj hq fz1_37_40 fz2_37_40
  · exact match_zero_fix ⟨38, by decide⟩ ⟨40, by decide⟩ p hp j hj hq fz1_38_40 fz2_38_40
  · exact match_zero_fix ⟨39, by decide⟩ ⟨40, by decide⟩ p hp j hj hq fz1_39_40 fz2_39_40
  · exact pair_40_40 p hp hrep j hj hq
  · exact match_zero_fix ⟨41, by decide⟩ ⟨40, by decide⟩ p hp j hj hq fz1_41_40 fz2_41_40
  · exact match_zero_fix ⟨42, by decide⟩ ⟨40, by decide⟩ p hp j hj hq fz1_42_40 fz2_42_40
  · exact match_zero_fix ⟨43, by decide⟩ ⟨40, by decide⟩ p hp j hj hq fz1_43_40 fz2_43_40
  · exact match_zero_fix ⟨44, by decide⟩ ⟨40, by decide⟩ p hp j hj hq fz1_44_40 fz2_44_40
  · exact match_zero_fix ⟨45, by decide⟩ ⟨40, by decide⟩ p hp j hj hq fz1_45_40 fz2_45_40
  · exact match_zero_fix ⟨46, by decide⟩ ⟨40, by decide⟩ p hp j hj hq fz1_46_40 fz2_46_40
  · exact match_zero_fix ⟨47, by decide⟩ ⟨40, by decide⟩ p hp j hj hq fz1_47_40 fz2_47_40
  · exact match_zero_fix ⟨48, by decide⟩ ⟨40, by decide⟩ p hp j hj hq fz1_48_40 fz2_48_40
  · exact match_zero_fix ⟨49, by decide⟩ ⟨40, by decide⟩ p hp j hj hq fz1_49_40 fz2_49_40
  · exact match_zero_fix ⟨50, by decide⟩ ⟨40, by decide⟩ p hp j hj hq fz1_50_40 fz2_50_40
  · exact match_zero_fix ⟨51, by decide⟩ ⟨40, by decide⟩ p hp j hj hq fz1_51_40 fz2_51_40
  · exact match_zero_fix ⟨52, by decide⟩ ⟨40, by decide⟩ p hp j hj hq fz1_52_40 fz2_52_40
  · exact match_zero_fix ⟨53, by decide⟩ ⟨40, by decide⟩ p hp j hj hq fz1_53_40 fz2_53_40
  · exact match_zero_fix ⟨54, by decide⟩ ⟨40, by decide⟩ p hp j hj hq fz1_54_40 fz2_54_40
  · exact match_zero_fix ⟨55, by decide⟩ ⟨40, by decide⟩ p hp j hj hq fz1_55_40 fz2_55_40
  · exact match_zero_fix ⟨56, by decide⟩ ⟨40, by decide⟩ p hp j hj hq fz1_56_40 fz2_56_40
  · exact match_zero_fix ⟨57, by decide⟩ ⟨40, by decide⟩ p hp j hj hq fz1_57_40 fz2_57_40
  · exact match_zero_fix ⟨58, by decide⟩ ⟨40, by decide⟩ p hp j hj hq fz1_58_40 fz2_58_40
  · exact match_zero_fix ⟨59, by decide⟩ ⟨40, by decide⟩ p hp j hj hq fz1_59_40 fz2_59_40
  · exact match_zero_fix ⟨60, by decide⟩ ⟨40, by decide⟩ p hp j hj hq fz1_60_40 fz2_60_40
  · exact match_zero_fix ⟨61, by decide⟩ ⟨40, by decide⟩ p hp j hj hq fz1_61_40 fz2_61_40
  · exact match_zero_fix ⟨62, by decide⟩ ⟨40, by decide⟩ p hp j hj hq fz1_62_40 fz2_62_40
  · exact match_zero_fix ⟨63, by decide⟩ ⟨40, by decide⟩ p hp j hj hq fz1_63_40 fz2_63_40
  · exact match_zero_fix ⟨64, by decide⟩ ⟨40, by decide⟩ p hp j hj hq fz1_64_40 fz2_64_40
  · exact pair_65_40 p hp hrep j hj hq
  · exact pair_66_40 p hp hrep j hj hq
  · exact pair_67_40 p hp hrep j hj hq
  · exact pair_68_40 p hp hrep j hj hq
  · exact pair_69_40 p hp hrep j hj hq
  · exact match_zero_fix ⟨70, by decide⟩ ⟨40, by decide⟩ p hp j hj hq fz1_70_40 fz2_70_40
  · exact match_zero_fix ⟨71, by decide⟩ ⟨40, by decide⟩ p hp j hj hq fz1_71_40 fz2_71_40
  · exact match_zero_fix ⟨72, by decide⟩ ⟨40, by decide⟩ p hp j hj hq fz1_72_40 fz2_72_40
  · exact match_zero_fix ⟨73, by decide⟩ ⟨40, by decide⟩ p hp j hj hq fz1_73_40 fz2_73_40
  · exact match_zero_fix ⟨74, by decide⟩ ⟨40, by decide⟩ p hp j hj hq fz1_74_40 fz2_74_40
  · exact match_zero_fix ⟨75, by decide⟩ ⟨40, by decide⟩ p hp j hj hq fz1_75_40 fz2_75_40
  · exact match_zero_fix ⟨76, by decide⟩ ⟨40, by decide⟩ p hp j hj hq fz1_76_40 fz2_76_40
  · exact match_zero_fix ⟨77, by decide⟩ ⟨40, by decide⟩ p hp j hj hq fz1_77_40 fz2_77_40
  · exact match_zero_fix ⟨78, by decide⟩ ⟨40, by decide⟩ p hp j hj hq fz1_78_40 fz2_78_40
  · exact match_zero_fix ⟨79, by decide⟩ ⟨40, by decide⟩ p hp j hj hq fz1_79_40 fz2_79_40
  · exact match_zero_fix ⟨80, by decide⟩ ⟨40, by decide⟩ p hp j hj hq fz1_80_40 fz2_80_40
  · exact match_zero_fix ⟨81, by decide⟩ ⟨40, by decide⟩ p hp j hj hq fz1_81_40 fz2_81_40
  · exact match_zero_fix ⟨82, by decide⟩ ⟨40, by decide⟩ p hp j hj hq fz1_82_40 fz2_82_40
  · exact match_zero_fix ⟨83, by decide⟩ ⟨40, by decide⟩ p hp j hj hq fz1_83_40 fz2_83_40
  · exact match_zero_fix ⟨84, by decide⟩ ⟨40, by decide⟩ p hp j hj hq fz1_84_40 fz2_84_40
  · exact match_zero_fix ⟨85, by decide⟩ ⟨40, by decide⟩ p hp j hj hq fz1_85_40 fz2_85_40
  · exact match_zero_fix ⟨86, by decide⟩ ⟨40, by decide⟩ p hp j hj hq fz1_86_40 fz2_86_40
  · exact match_zero_fix ⟨87, by decide⟩ ⟨40, by decide⟩ p hp j hj hq fz1_87_40 fz2_87_40
  · exact match_zero_fix ⟨88, by decide⟩ ⟨40, by decide⟩ p hp j hj hq fz1_88_40 fz2_88_40
  · exact match_zero_fix ⟨89, by decide⟩ ⟨40, by decide⟩ p hp j hj hq fz1_89_40 fz2_89_40
  · exact match_zero_fix ⟨90, by decide⟩ ⟨40, by decide⟩ p hp j hj hq fz1_90_40 fz2_90_40
  · exact match_zero_fix ⟨91, by decide⟩ ⟨40, by decide⟩ p hp j hj hq fz1_91_40 fz2_91_40
  · exact match_zero_fix ⟨92, by decide⟩ ⟨40, by decide⟩ p hp j hj hq fz1_92_40 fz2_92_40
  · exact match_zero_fix ⟨93, by decide⟩ ⟨40, by decide⟩ p hp j hj hq fz1_93_40 fz2_93_40
  · exact match_zero_fix ⟨94, by decide⟩ ⟨40, by decide⟩ p hp j hj hq fz1_94_40 fz2_94_40
  · exact match_zero_fix ⟨95, by decide⟩ ⟨40, by decide⟩ p hp j hj hq fz1_95_40 fz2_95_40
  · exact match_zero_fix ⟨96, by decide⟩ ⟨40, by decide⟩ p hp j hj hq fz1_96_40 fz2_96_40
  · exact match_zero_fix ⟨97, by decide⟩ ⟨40, by decide⟩ p hp j hj hq fz1_97_40 fz2_97_40
  · exact match_zero_fix ⟨98, by decide⟩ ⟨40, by decide⟩ p hp j hj hq fz1_98_40 fz2_98_40
  · exact match_zero_fix ⟨99, by decide⟩ ⟨40, by decide⟩ p hp j hj hq fz1_99_40 fz2_99_40
  · exact match_zero_fix ⟨100, by decide⟩ ⟨40, by decide⟩ p hp j hj hq fz1_100_40 fz2_100_40
  · exact match_zero_fix ⟨101, by decide⟩ ⟨40, by decide⟩ p hp j hj hq fz1_101_40 fz2_101_40
  · exact pair_102_40 p hp hrep j hj hq
  · exact match_zero_fix ⟨103, by decide⟩ ⟨40, by decide⟩ p hp j hj hq fz1_103_40 fz2_103_40
  · exact match_zero_fix ⟨104, by decide⟩ ⟨40, by decide⟩ p hp j hj hq fz1_104_40 fz2_104_40
  · exact match_zero_fix ⟨105, by decide⟩ ⟨40, by decide⟩ p hp j hj hq fz1_105_40 fz2_105_40
  · exact match_zero_fix ⟨106, by decide⟩ ⟨40, by decide⟩ p hp j hj hq fz1_106_40 fz2_106_40
  · exact match_zero_fix ⟨107, by decide⟩ ⟨40, by decide⟩ p hp j hj hq fz1_107_40 fz2_107_40
  · exact match_zero_fix ⟨108, by decide⟩ ⟨40, by decide⟩ p hp j hj hq fz1_108_40 fz2_108_40
  · exact match_zero_fix ⟨109, by decide⟩ ⟨40, by decide⟩ p hp j hj hq fz1_109_40 fz2_109_40
  · exact match_zero_fix ⟨110, by decide⟩ ⟨40, by decide⟩ p hp j hj hq fz1_110_40 fz2_110_40
  · exact match_zero_fix ⟨111, by decide⟩ ⟨40, by decide⟩ p hp j hj hq fz1_111_40 fz2_111_40
  · exact match_zero_fix ⟨112, by decide⟩ ⟨40, by decide⟩ p hp j hj hq fz1_112_40 fz2_112_40
  · exact match_zero_fix ⟨113, by decide⟩ ⟨40, by decide⟩ p hp j hj hq fz1_113_40 fz2_113_40
  · exact match_zero_fix ⟨114, by decide⟩ ⟨40, by decide⟩ p hp j hj hq fz1_114_40 fz2_114_40
  · exact match_zero_fix ⟨115, by decide⟩ ⟨40, by decide⟩ p hp j hj hq fz1_115_40 fz2_115_40
  · exact match_zero_fix ⟨116, by decide⟩ ⟨40, by decide⟩ p hp j hj hq fz1_116_40 fz2_116_40
  · exact match_zero_fix ⟨117, by decide⟩ ⟨40, by decide⟩ p hp j hj hq fz1_117_40 fz2_117_40
  · exact pair_118_40 p hp hrep j hj hq
  · exact match_zero_fix ⟨119, by decide⟩ ⟨40, by decide⟩ p hp j hj hq fz1_119_40 fz2_119_40
  · exact match_zero_fix ⟨120, by decide⟩ ⟨40, by decide⟩ p hp j hj hq fz1_120_40 fz2_120_40
  · exact match_zero_fix ⟨121, by decide⟩ ⟨40, by decide⟩ p hp j hj hq fz1_121_40 fz2_121_40
  · exact match_zero_fix ⟨122, by decide⟩ ⟨40, by decide⟩ p hp j hj hq fz1_122_40 fz2_122_40
  · exact match_zero_fix ⟨123, by decide⟩ ⟨40, by decide⟩ p hp j hj hq fz1_123_40 fz2_123_40
  · exact match_zero_fix ⟨124, by decide⟩ ⟨40, by decide⟩ p hp j hj hq fz1_124_40 fz2_124_40
  · exact pair_125_40 p hp hrep j hj hq
  · exact match_zero_fix ⟨126, by decide⟩ ⟨40, by decide⟩ p hp j hj hq fz1_126_40 fz2_126_40
  · exact pair_127_40 p hp hrep j hj hq
  · exact match_zero_fix ⟨128, by decide⟩ ⟨40, by decide⟩ p hp j hj hq fz1_128_40 fz2_128_40
  · exact match_zero_fix ⟨129, by decide⟩ ⟨40, by decide⟩ p hp j hj hq fz1_129_40 fz2_129_40
  · exact match_zero_fix ⟨130, by decide⟩ ⟨40, by decide⟩ p hp j hj hq fz1_130_40 fz2_130_40
  · exact match_zero_fix ⟨131, by decide⟩ ⟨40, by decide⟩ p hp j hj hq fz1_131_40 fz2_131_40
  · exact match_zero_fix ⟨132, by decide⟩ ⟨40, by decide⟩ p hp j hj hq fz1_132_40 fz2_132_40
  · exact match_zero_fix ⟨133, by decide⟩ ⟨40, by decide⟩ p hp j hj hq fz1_133_40 fz2_133_40
  · exact pair_134_40 p hp hrep j hj hq
  · exact match_zero_fix ⟨135, by decide⟩ ⟨40, by decide⟩ p hp j hj hq fz1_135_40 fz2_135_40
  · exact pair_136_40 p hp hrep j hj hq
  · exact match_zero_fix ⟨137, by decide⟩ ⟨40, by decide⟩ p hp j hj hq fz1_137_40 fz2_137_40
  · exact match_zero_fix ⟨138, by decide⟩ ⟨40, by decide⟩ p hp j hj hq fz1_138_40 fz2_138_40
  · exact match_zero_fix ⟨139, by decide⟩ ⟨40, by decide⟩ p hp j hj hq fz1_139_40 fz2_139_40
  · exact match_zero_fix ⟨140, by decide⟩ ⟨40, by decide⟩ p hp j hj hq fz1_140_40 fz2_140_40
  · exact match_zero_fix ⟨141, by decide⟩ ⟨40, by decide⟩ p hp j hj hq fz1_141_40 fz2_141_40
  · exact match_zero_fix ⟨142, by decide⟩ ⟨40, by decide⟩ p hp j hj hq fz1_142_40 fz2_142_40
  · exact match_zero_fix ⟨143, by decide⟩ ⟨40, by decide⟩ p hp j hj hq fz1_143_40 fz2_143_40
  · exact pair_144_40 p hp hrep j hj hq
  · exact match_zero_fix ⟨145, by decide⟩ ⟨40, by decide⟩ p hp j hj hq fz1_145_40 fz2_145_40
  · exact match_zero_fix ⟨146, by decide⟩ ⟨40, by decide⟩ p hp j hj hq fz1_146_40 fz2_146_40
  · exact pair_147_40 p hp hrep j hj hq

theorem master_41 (p : Nat) (hp : p < (Q2.transData.getD 41 []).length)
    (hrep : (Q2.cosetIsRep.getD 41 []).getD p false = true)
    (rK : Fin 148) (j : Nat) (hj : j < (repChars.getD rK.val []).length)
    (hq : (normIsRep.getD rK.val []).getD j false = true) :
    species (Q2.reps (⟨41, by decide⟩ : Fin 148)) (colE2 ⟨41, by decide⟩ p hp)
        (rowE2 rK j hj hq)
      = species (reps (⟨41, by decide⟩ : Fin 148))
        (colE1 ⟨41, by decide⟩ p (transLenTr ⟨41, by decide⟩ p hp)) (rowE1 rK j hj) := by
  rcases rK with ⟨nK, hnK⟩; interval_cases nK
  · exact match_zero_len ⟨0, by decide⟩ ⟨41, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨1, by decide⟩ ⟨41, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨2, by decide⟩ ⟨41, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨3, by decide⟩ ⟨41, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨4, by decide⟩ ⟨41, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨5, by decide⟩ ⟨41, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨6, by decide⟩ ⟨41, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨7, by decide⟩ ⟨41, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨8, by decide⟩ ⟨41, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨9, by decide⟩ ⟨41, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨10, by decide⟩ ⟨41, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨11, by decide⟩ ⟨41, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨12, by decide⟩ ⟨41, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_fix ⟨13, by decide⟩ ⟨41, by decide⟩ p hp j hj hq fz1_13_41 fz2_13_41
  · exact match_zero_fix ⟨14, by decide⟩ ⟨41, by decide⟩ p hp j hj hq fz1_14_41 fz2_14_41
  · exact match_zero_fix ⟨15, by decide⟩ ⟨41, by decide⟩ p hp j hj hq fz1_15_41 fz2_15_41
  · exact match_zero_fix ⟨16, by decide⟩ ⟨41, by decide⟩ p hp j hj hq fz1_16_41 fz2_16_41
  · exact match_zero_fix ⟨17, by decide⟩ ⟨41, by decide⟩ p hp j hj hq fz1_17_41 fz2_17_41
  · exact match_zero_fix ⟨18, by decide⟩ ⟨41, by decide⟩ p hp j hj hq fz1_18_41 fz2_18_41
  · exact match_zero_fix ⟨19, by decide⟩ ⟨41, by decide⟩ p hp j hj hq fz1_19_41 fz2_19_41
  · exact match_zero_fix ⟨20, by decide⟩ ⟨41, by decide⟩ p hp j hj hq fz1_20_41 fz2_20_41
  · exact match_zero_fix ⟨21, by decide⟩ ⟨41, by decide⟩ p hp j hj hq fz1_21_41 fz2_21_41
  · exact match_zero_fix ⟨22, by decide⟩ ⟨41, by decide⟩ p hp j hj hq fz1_22_41 fz2_22_41
  · exact match_zero_fix ⟨23, by decide⟩ ⟨41, by decide⟩ p hp j hj hq fz1_23_41 fz2_23_41
  · exact match_zero_fix ⟨24, by decide⟩ ⟨41, by decide⟩ p hp j hj hq fz1_24_41 fz2_24_41
  · exact match_zero_fix ⟨25, by decide⟩ ⟨41, by decide⟩ p hp j hj hq fz1_25_41 fz2_25_41
  · exact match_zero_fix ⟨26, by decide⟩ ⟨41, by decide⟩ p hp j hj hq fz1_26_41 fz2_26_41
  · exact match_zero_fix ⟨27, by decide⟩ ⟨41, by decide⟩ p hp j hj hq fz1_27_41 fz2_27_41
  · exact match_zero_fix ⟨28, by decide⟩ ⟨41, by decide⟩ p hp j hj hq fz1_28_41 fz2_28_41
  · exact match_zero_fix ⟨29, by decide⟩ ⟨41, by decide⟩ p hp j hj hq fz1_29_41 fz2_29_41
  · exact match_zero_fix ⟨30, by decide⟩ ⟨41, by decide⟩ p hp j hj hq fz1_30_41 fz2_30_41
  · exact match_zero_fix ⟨31, by decide⟩ ⟨41, by decide⟩ p hp j hj hq fz1_31_41 fz2_31_41
  · exact match_zero_fix ⟨32, by decide⟩ ⟨41, by decide⟩ p hp j hj hq fz1_32_41 fz2_32_41
  · exact match_zero_fix ⟨33, by decide⟩ ⟨41, by decide⟩ p hp j hj hq fz1_33_41 fz2_33_41
  · exact match_zero_fix ⟨34, by decide⟩ ⟨41, by decide⟩ p hp j hj hq fz1_34_41 fz2_34_41
  · exact match_zero_fix ⟨35, by decide⟩ ⟨41, by decide⟩ p hp j hj hq fz1_35_41 fz2_35_41
  · exact match_zero_fix ⟨36, by decide⟩ ⟨41, by decide⟩ p hp j hj hq fz1_36_41 fz2_36_41
  · exact match_zero_fix ⟨37, by decide⟩ ⟨41, by decide⟩ p hp j hj hq fz1_37_41 fz2_37_41
  · exact match_zero_fix ⟨38, by decide⟩ ⟨41, by decide⟩ p hp j hj hq fz1_38_41 fz2_38_41
  · exact match_zero_fix ⟨39, by decide⟩ ⟨41, by decide⟩ p hp j hj hq fz1_39_41 fz2_39_41
  · exact match_zero_fix ⟨40, by decide⟩ ⟨41, by decide⟩ p hp j hj hq fz1_40_41 fz2_40_41
  · exact pair_41_41 p hp hrep j hj hq
  · exact match_zero_fix ⟨42, by decide⟩ ⟨41, by decide⟩ p hp j hj hq fz1_42_41 fz2_42_41
  · exact match_zero_fix ⟨43, by decide⟩ ⟨41, by decide⟩ p hp j hj hq fz1_43_41 fz2_43_41
  · exact match_zero_fix ⟨44, by decide⟩ ⟨41, by decide⟩ p hp j hj hq fz1_44_41 fz2_44_41
  · exact match_zero_fix ⟨45, by decide⟩ ⟨41, by decide⟩ p hp j hj hq fz1_45_41 fz2_45_41
  · exact match_zero_fix ⟨46, by decide⟩ ⟨41, by decide⟩ p hp j hj hq fz1_46_41 fz2_46_41
  · exact match_zero_fix ⟨47, by decide⟩ ⟨41, by decide⟩ p hp j hj hq fz1_47_41 fz2_47_41
  · exact match_zero_fix ⟨48, by decide⟩ ⟨41, by decide⟩ p hp j hj hq fz1_48_41 fz2_48_41
  · exact match_zero_fix ⟨49, by decide⟩ ⟨41, by decide⟩ p hp j hj hq fz1_49_41 fz2_49_41
  · exact match_zero_fix ⟨50, by decide⟩ ⟨41, by decide⟩ p hp j hj hq fz1_50_41 fz2_50_41
  · exact match_zero_fix ⟨51, by decide⟩ ⟨41, by decide⟩ p hp j hj hq fz1_51_41 fz2_51_41
  · exact match_zero_fix ⟨52, by decide⟩ ⟨41, by decide⟩ p hp j hj hq fz1_52_41 fz2_52_41
  · exact match_zero_fix ⟨53, by decide⟩ ⟨41, by decide⟩ p hp j hj hq fz1_53_41 fz2_53_41
  · exact match_zero_fix ⟨54, by decide⟩ ⟨41, by decide⟩ p hp j hj hq fz1_54_41 fz2_54_41
  · exact match_zero_fix ⟨55, by decide⟩ ⟨41, by decide⟩ p hp j hj hq fz1_55_41 fz2_55_41
  · exact match_zero_fix ⟨56, by decide⟩ ⟨41, by decide⟩ p hp j hj hq fz1_56_41 fz2_56_41
  · exact match_zero_fix ⟨57, by decide⟩ ⟨41, by decide⟩ p hp j hj hq fz1_57_41 fz2_57_41
  · exact match_zero_fix ⟨58, by decide⟩ ⟨41, by decide⟩ p hp j hj hq fz1_58_41 fz2_58_41
  · exact match_zero_fix ⟨59, by decide⟩ ⟨41, by decide⟩ p hp j hj hq fz1_59_41 fz2_59_41
  · exact match_zero_fix ⟨60, by decide⟩ ⟨41, by decide⟩ p hp j hj hq fz1_60_41 fz2_60_41
  · exact match_zero_fix ⟨61, by decide⟩ ⟨41, by decide⟩ p hp j hj hq fz1_61_41 fz2_61_41
  · exact match_zero_fix ⟨62, by decide⟩ ⟨41, by decide⟩ p hp j hj hq fz1_62_41 fz2_62_41
  · exact match_zero_fix ⟨63, by decide⟩ ⟨41, by decide⟩ p hp j hj hq fz1_63_41 fz2_63_41
  · exact match_zero_fix ⟨64, by decide⟩ ⟨41, by decide⟩ p hp j hj hq fz1_64_41 fz2_64_41
  · exact match_zero_fix ⟨65, by decide⟩ ⟨41, by decide⟩ p hp j hj hq fz1_65_41 fz2_65_41
  · exact match_zero_fix ⟨66, by decide⟩ ⟨41, by decide⟩ p hp j hj hq fz1_66_41 fz2_66_41
  · exact match_zero_fix ⟨67, by decide⟩ ⟨41, by decide⟩ p hp j hj hq fz1_67_41 fz2_67_41
  · exact match_zero_fix ⟨68, by decide⟩ ⟨41, by decide⟩ p hp j hj hq fz1_68_41 fz2_68_41
  · exact match_zero_fix ⟨69, by decide⟩ ⟨41, by decide⟩ p hp j hj hq fz1_69_41 fz2_69_41
  · exact pair_70_41 p hp hrep j hj hq
  · exact pair_71_41 p hp hrep j hj hq
  · exact pair_72_41 p hp hrep j hj hq
  · exact pair_73_41 p hp hrep j hj hq
  · exact pair_74_41 p hp hrep j hj hq
  · exact match_zero_fix ⟨75, by decide⟩ ⟨41, by decide⟩ p hp j hj hq fz1_75_41 fz2_75_41
  · exact match_zero_fix ⟨76, by decide⟩ ⟨41, by decide⟩ p hp j hj hq fz1_76_41 fz2_76_41
  · exact match_zero_fix ⟨77, by decide⟩ ⟨41, by decide⟩ p hp j hj hq fz1_77_41 fz2_77_41
  · exact match_zero_fix ⟨78, by decide⟩ ⟨41, by decide⟩ p hp j hj hq fz1_78_41 fz2_78_41
  · exact match_zero_fix ⟨79, by decide⟩ ⟨41, by decide⟩ p hp j hj hq fz1_79_41 fz2_79_41
  · exact match_zero_fix ⟨80, by decide⟩ ⟨41, by decide⟩ p hp j hj hq fz1_80_41 fz2_80_41
  · exact match_zero_fix ⟨81, by decide⟩ ⟨41, by decide⟩ p hp j hj hq fz1_81_41 fz2_81_41
  · exact match_zero_fix ⟨82, by decide⟩ ⟨41, by decide⟩ p hp j hj hq fz1_82_41 fz2_82_41
  · exact match_zero_fix ⟨83, by decide⟩ ⟨41, by decide⟩ p hp j hj hq fz1_83_41 fz2_83_41
  · exact match_zero_fix ⟨84, by decide⟩ ⟨41, by decide⟩ p hp j hj hq fz1_84_41 fz2_84_41
  · exact match_zero_fix ⟨85, by decide⟩ ⟨41, by decide⟩ p hp j hj hq fz1_85_41 fz2_85_41
  · exact match_zero_fix ⟨86, by decide⟩ ⟨41, by decide⟩ p hp j hj hq fz1_86_41 fz2_86_41
  · exact match_zero_fix ⟨87, by decide⟩ ⟨41, by decide⟩ p hp j hj hq fz1_87_41 fz2_87_41
  · exact match_zero_fix ⟨88, by decide⟩ ⟨41, by decide⟩ p hp j hj hq fz1_88_41 fz2_88_41
  · exact match_zero_fix ⟨89, by decide⟩ ⟨41, by decide⟩ p hp j hj hq fz1_89_41 fz2_89_41
  · exact match_zero_fix ⟨90, by decide⟩ ⟨41, by decide⟩ p hp j hj hq fz1_90_41 fz2_90_41
  · exact match_zero_fix ⟨91, by decide⟩ ⟨41, by decide⟩ p hp j hj hq fz1_91_41 fz2_91_41
  · exact match_zero_fix ⟨92, by decide⟩ ⟨41, by decide⟩ p hp j hj hq fz1_92_41 fz2_92_41
  · exact match_zero_fix ⟨93, by decide⟩ ⟨41, by decide⟩ p hp j hj hq fz1_93_41 fz2_93_41
  · exact match_zero_fix ⟨94, by decide⟩ ⟨41, by decide⟩ p hp j hj hq fz1_94_41 fz2_94_41
  · exact match_zero_fix ⟨95, by decide⟩ ⟨41, by decide⟩ p hp j hj hq fz1_95_41 fz2_95_41
  · exact match_zero_fix ⟨96, by decide⟩ ⟨41, by decide⟩ p hp j hj hq fz1_96_41 fz2_96_41
  · exact match_zero_fix ⟨97, by decide⟩ ⟨41, by decide⟩ p hp j hj hq fz1_97_41 fz2_97_41
  · exact match_zero_fix ⟨98, by decide⟩ ⟨41, by decide⟩ p hp j hj hq fz1_98_41 fz2_98_41
  · exact match_zero_fix ⟨99, by decide⟩ ⟨41, by decide⟩ p hp j hj hq fz1_99_41 fz2_99_41
  · exact match_zero_fix ⟨100, by decide⟩ ⟨41, by decide⟩ p hp j hj hq fz1_100_41 fz2_100_41
  · exact match_zero_fix ⟨101, by decide⟩ ⟨41, by decide⟩ p hp j hj hq fz1_101_41 fz2_101_41
  · exact match_zero_fix ⟨102, by decide⟩ ⟨41, by decide⟩ p hp j hj hq fz1_102_41 fz2_102_41
  · exact pair_103_41 p hp hrep j hj hq
  · exact match_zero_fix ⟨104, by decide⟩ ⟨41, by decide⟩ p hp j hj hq fz1_104_41 fz2_104_41
  · exact match_zero_fix ⟨105, by decide⟩ ⟨41, by decide⟩ p hp j hj hq fz1_105_41 fz2_105_41
  · exact match_zero_fix ⟨106, by decide⟩ ⟨41, by decide⟩ p hp j hj hq fz1_106_41 fz2_106_41
  · exact match_zero_fix ⟨107, by decide⟩ ⟨41, by decide⟩ p hp j hj hq fz1_107_41 fz2_107_41
  · exact match_zero_fix ⟨108, by decide⟩ ⟨41, by decide⟩ p hp j hj hq fz1_108_41 fz2_108_41
  · exact match_zero_fix ⟨109, by decide⟩ ⟨41, by decide⟩ p hp j hj hq fz1_109_41 fz2_109_41
  · exact match_zero_fix ⟨110, by decide⟩ ⟨41, by decide⟩ p hp j hj hq fz1_110_41 fz2_110_41
  · exact match_zero_fix ⟨111, by decide⟩ ⟨41, by decide⟩ p hp j hj hq fz1_111_41 fz2_111_41
  · exact match_zero_fix ⟨112, by decide⟩ ⟨41, by decide⟩ p hp j hj hq fz1_112_41 fz2_112_41
  · exact match_zero_fix ⟨113, by decide⟩ ⟨41, by decide⟩ p hp j hj hq fz1_113_41 fz2_113_41
  · exact match_zero_fix ⟨114, by decide⟩ ⟨41, by decide⟩ p hp j hj hq fz1_114_41 fz2_114_41
  · exact match_zero_fix ⟨115, by decide⟩ ⟨41, by decide⟩ p hp j hj hq fz1_115_41 fz2_115_41
  · exact match_zero_fix ⟨116, by decide⟩ ⟨41, by decide⟩ p hp j hj hq fz1_116_41 fz2_116_41
  · exact match_zero_fix ⟨117, by decide⟩ ⟨41, by decide⟩ p hp j hj hq fz1_117_41 fz2_117_41
  · exact match_zero_fix ⟨118, by decide⟩ ⟨41, by decide⟩ p hp j hj hq fz1_118_41 fz2_118_41
  · exact pair_119_41 p hp hrep j hj hq
  · exact match_zero_fix ⟨120, by decide⟩ ⟨41, by decide⟩ p hp j hj hq fz1_120_41 fz2_120_41
  · exact pair_121_41 p hp hrep j hj hq
  · exact match_zero_fix ⟨122, by decide⟩ ⟨41, by decide⟩ p hp j hj hq fz1_122_41 fz2_122_41
  · exact match_zero_fix ⟨123, by decide⟩ ⟨41, by decide⟩ p hp j hj hq fz1_123_41 fz2_123_41
  · exact match_zero_fix ⟨124, by decide⟩ ⟨41, by decide⟩ p hp j hj hq fz1_124_41 fz2_124_41
  · exact match_zero_fix ⟨125, by decide⟩ ⟨41, by decide⟩ p hp j hj hq fz1_125_41 fz2_125_41
  · exact match_zero_fix ⟨126, by decide⟩ ⟨41, by decide⟩ p hp j hj hq fz1_126_41 fz2_126_41
  · exact match_zero_fix ⟨127, by decide⟩ ⟨41, by decide⟩ p hp j hj hq fz1_127_41 fz2_127_41
  · exact pair_128_41 p hp hrep j hj hq
  · exact match_zero_fix ⟨129, by decide⟩ ⟨41, by decide⟩ p hp j hj hq fz1_129_41 fz2_129_41
  · exact match_zero_fix ⟨130, by decide⟩ ⟨41, by decide⟩ p hp j hj hq fz1_130_41 fz2_130_41
  · exact match_zero_fix ⟨131, by decide⟩ ⟨41, by decide⟩ p hp j hj hq fz1_131_41 fz2_131_41
  · exact match_zero_fix ⟨132, by decide⟩ ⟨41, by decide⟩ p hp j hj hq fz1_132_41 fz2_132_41
  · exact match_zero_fix ⟨133, by decide⟩ ⟨41, by decide⟩ p hp j hj hq fz1_133_41 fz2_133_41
  · exact match_zero_fix ⟨134, by decide⟩ ⟨41, by decide⟩ p hp j hj hq fz1_134_41 fz2_134_41
  · exact pair_135_41 p hp hrep j hj hq
  · exact match_zero_fix ⟨136, by decide⟩ ⟨41, by decide⟩ p hp j hj hq fz1_136_41 fz2_136_41
  · exact pair_137_41 p hp hrep j hj hq
  · exact match_zero_fix ⟨138, by decide⟩ ⟨41, by decide⟩ p hp j hj hq fz1_138_41 fz2_138_41
  · exact match_zero_fix ⟨139, by decide⟩ ⟨41, by decide⟩ p hp j hj hq fz1_139_41 fz2_139_41
  · exact match_zero_fix ⟨140, by decide⟩ ⟨41, by decide⟩ p hp j hj hq fz1_140_41 fz2_140_41
  · exact match_zero_fix ⟨141, by decide⟩ ⟨41, by decide⟩ p hp j hj hq fz1_141_41 fz2_141_41
  · exact match_zero_fix ⟨142, by decide⟩ ⟨41, by decide⟩ p hp j hj hq fz1_142_41 fz2_142_41
  · exact match_zero_fix ⟨143, by decide⟩ ⟨41, by decide⟩ p hp j hj hq fz1_143_41 fz2_143_41
  · exact pair_144_41 p hp hrep j hj hq
  · exact match_zero_fix ⟨145, by decide⟩ ⟨41, by decide⟩ p hp j hj hq fz1_145_41 fz2_145_41
  · exact match_zero_fix ⟨146, by decide⟩ ⟨41, by decide⟩ p hp j hj hq fz1_146_41 fz2_146_41
  · exact pair_147_41 p hp hrep j hj hq

theorem master_42 (p : Nat) (hp : p < (Q2.transData.getD 42 []).length)
    (hrep : (Q2.cosetIsRep.getD 42 []).getD p false = true)
    (rK : Fin 148) (j : Nat) (hj : j < (repChars.getD rK.val []).length)
    (hq : (normIsRep.getD rK.val []).getD j false = true) :
    species (Q2.reps (⟨42, by decide⟩ : Fin 148)) (colE2 ⟨42, by decide⟩ p hp)
        (rowE2 rK j hj hq)
      = species (reps (⟨42, by decide⟩ : Fin 148))
        (colE1 ⟨42, by decide⟩ p (transLenTr ⟨42, by decide⟩ p hp)) (rowE1 rK j hj) := by
  rcases rK with ⟨nK, hnK⟩; interval_cases nK
  · exact match_zero_len ⟨0, by decide⟩ ⟨42, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨1, by decide⟩ ⟨42, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨2, by decide⟩ ⟨42, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨3, by decide⟩ ⟨42, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨4, by decide⟩ ⟨42, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨5, by decide⟩ ⟨42, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨6, by decide⟩ ⟨42, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨7, by decide⟩ ⟨42, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨8, by decide⟩ ⟨42, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨9, by decide⟩ ⟨42, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨10, by decide⟩ ⟨42, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨11, by decide⟩ ⟨42, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨12, by decide⟩ ⟨42, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_fix ⟨13, by decide⟩ ⟨42, by decide⟩ p hp j hj hq fz1_13_42 fz2_13_42
  · exact match_zero_fix ⟨14, by decide⟩ ⟨42, by decide⟩ p hp j hj hq fz1_14_42 fz2_14_42
  · exact match_zero_fix ⟨15, by decide⟩ ⟨42, by decide⟩ p hp j hj hq fz1_15_42 fz2_15_42
  · exact match_zero_fix ⟨16, by decide⟩ ⟨42, by decide⟩ p hp j hj hq fz1_16_42 fz2_16_42
  · exact match_zero_fix ⟨17, by decide⟩ ⟨42, by decide⟩ p hp j hj hq fz1_17_42 fz2_17_42
  · exact match_zero_fix ⟨18, by decide⟩ ⟨42, by decide⟩ p hp j hj hq fz1_18_42 fz2_18_42
  · exact match_zero_fix ⟨19, by decide⟩ ⟨42, by decide⟩ p hp j hj hq fz1_19_42 fz2_19_42
  · exact match_zero_fix ⟨20, by decide⟩ ⟨42, by decide⟩ p hp j hj hq fz1_20_42 fz2_20_42
  · exact match_zero_fix ⟨21, by decide⟩ ⟨42, by decide⟩ p hp j hj hq fz1_21_42 fz2_21_42
  · exact match_zero_fix ⟨22, by decide⟩ ⟨42, by decide⟩ p hp j hj hq fz1_22_42 fz2_22_42
  · exact match_zero_fix ⟨23, by decide⟩ ⟨42, by decide⟩ p hp j hj hq fz1_23_42 fz2_23_42
  · exact match_zero_fix ⟨24, by decide⟩ ⟨42, by decide⟩ p hp j hj hq fz1_24_42 fz2_24_42
  · exact match_zero_fix ⟨25, by decide⟩ ⟨42, by decide⟩ p hp j hj hq fz1_25_42 fz2_25_42
  · exact match_zero_fix ⟨26, by decide⟩ ⟨42, by decide⟩ p hp j hj hq fz1_26_42 fz2_26_42
  · exact match_zero_fix ⟨27, by decide⟩ ⟨42, by decide⟩ p hp j hj hq fz1_27_42 fz2_27_42
  · exact match_zero_fix ⟨28, by decide⟩ ⟨42, by decide⟩ p hp j hj hq fz1_28_42 fz2_28_42
  · exact match_zero_fix ⟨29, by decide⟩ ⟨42, by decide⟩ p hp j hj hq fz1_29_42 fz2_29_42
  · exact match_zero_fix ⟨30, by decide⟩ ⟨42, by decide⟩ p hp j hj hq fz1_30_42 fz2_30_42
  · exact match_zero_fix ⟨31, by decide⟩ ⟨42, by decide⟩ p hp j hj hq fz1_31_42 fz2_31_42
  · exact match_zero_fix ⟨32, by decide⟩ ⟨42, by decide⟩ p hp j hj hq fz1_32_42 fz2_32_42
  · exact match_zero_fix ⟨33, by decide⟩ ⟨42, by decide⟩ p hp j hj hq fz1_33_42 fz2_33_42
  · exact match_zero_fix ⟨34, by decide⟩ ⟨42, by decide⟩ p hp j hj hq fz1_34_42 fz2_34_42
  · exact match_zero_fix ⟨35, by decide⟩ ⟨42, by decide⟩ p hp j hj hq fz1_35_42 fz2_35_42
  · exact match_zero_fix ⟨36, by decide⟩ ⟨42, by decide⟩ p hp j hj hq fz1_36_42 fz2_36_42
  · exact match_zero_fix ⟨37, by decide⟩ ⟨42, by decide⟩ p hp j hj hq fz1_37_42 fz2_37_42
  · exact match_zero_fix ⟨38, by decide⟩ ⟨42, by decide⟩ p hp j hj hq fz1_38_42 fz2_38_42
  · exact match_zero_fix ⟨39, by decide⟩ ⟨42, by decide⟩ p hp j hj hq fz1_39_42 fz2_39_42
  · exact match_zero_fix ⟨40, by decide⟩ ⟨42, by decide⟩ p hp j hj hq fz1_40_42 fz2_40_42
  · exact match_zero_fix ⟨41, by decide⟩ ⟨42, by decide⟩ p hp j hj hq fz1_41_42 fz2_41_42
  · exact pair_42_42 p hp hrep j hj hq
  · exact match_zero_fix ⟨43, by decide⟩ ⟨42, by decide⟩ p hp j hj hq fz1_43_42 fz2_43_42
  · exact match_zero_fix ⟨44, by decide⟩ ⟨42, by decide⟩ p hp j hj hq fz1_44_42 fz2_44_42
  · exact match_zero_fix ⟨45, by decide⟩ ⟨42, by decide⟩ p hp j hj hq fz1_45_42 fz2_45_42
  · exact match_zero_fix ⟨46, by decide⟩ ⟨42, by decide⟩ p hp j hj hq fz1_46_42 fz2_46_42
  · exact match_zero_fix ⟨47, by decide⟩ ⟨42, by decide⟩ p hp j hj hq fz1_47_42 fz2_47_42
  · exact match_zero_fix ⟨48, by decide⟩ ⟨42, by decide⟩ p hp j hj hq fz1_48_42 fz2_48_42
  · exact match_zero_fix ⟨49, by decide⟩ ⟨42, by decide⟩ p hp j hj hq fz1_49_42 fz2_49_42
  · exact match_zero_fix ⟨50, by decide⟩ ⟨42, by decide⟩ p hp j hj hq fz1_50_42 fz2_50_42
  · exact match_zero_fix ⟨51, by decide⟩ ⟨42, by decide⟩ p hp j hj hq fz1_51_42 fz2_51_42
  · exact match_zero_fix ⟨52, by decide⟩ ⟨42, by decide⟩ p hp j hj hq fz1_52_42 fz2_52_42
  · exact match_zero_fix ⟨53, by decide⟩ ⟨42, by decide⟩ p hp j hj hq fz1_53_42 fz2_53_42
  · exact match_zero_fix ⟨54, by decide⟩ ⟨42, by decide⟩ p hp j hj hq fz1_54_42 fz2_54_42
  · exact match_zero_fix ⟨55, by decide⟩ ⟨42, by decide⟩ p hp j hj hq fz1_55_42 fz2_55_42
  · exact match_zero_fix ⟨56, by decide⟩ ⟨42, by decide⟩ p hp j hj hq fz1_56_42 fz2_56_42
  · exact match_zero_fix ⟨57, by decide⟩ ⟨42, by decide⟩ p hp j hj hq fz1_57_42 fz2_57_42
  · exact match_zero_fix ⟨58, by decide⟩ ⟨42, by decide⟩ p hp j hj hq fz1_58_42 fz2_58_42
  · exact match_zero_fix ⟨59, by decide⟩ ⟨42, by decide⟩ p hp j hj hq fz1_59_42 fz2_59_42
  · exact match_zero_fix ⟨60, by decide⟩ ⟨42, by decide⟩ p hp j hj hq fz1_60_42 fz2_60_42
  · exact match_zero_fix ⟨61, by decide⟩ ⟨42, by decide⟩ p hp j hj hq fz1_61_42 fz2_61_42
  · exact match_zero_fix ⟨62, by decide⟩ ⟨42, by decide⟩ p hp j hj hq fz1_62_42 fz2_62_42
  · exact match_zero_fix ⟨63, by decide⟩ ⟨42, by decide⟩ p hp j hj hq fz1_63_42 fz2_63_42
  · exact match_zero_fix ⟨64, by decide⟩ ⟨42, by decide⟩ p hp j hj hq fz1_64_42 fz2_64_42
  · exact match_zero_fix ⟨65, by decide⟩ ⟨42, by decide⟩ p hp j hj hq fz1_65_42 fz2_65_42
  · exact match_zero_fix ⟨66, by decide⟩ ⟨42, by decide⟩ p hp j hj hq fz1_66_42 fz2_66_42
  · exact match_zero_fix ⟨67, by decide⟩ ⟨42, by decide⟩ p hp j hj hq fz1_67_42 fz2_67_42
  · exact match_zero_fix ⟨68, by decide⟩ ⟨42, by decide⟩ p hp j hj hq fz1_68_42 fz2_68_42
  · exact match_zero_fix ⟨69, by decide⟩ ⟨42, by decide⟩ p hp j hj hq fz1_69_42 fz2_69_42
  · exact match_zero_fix ⟨70, by decide⟩ ⟨42, by decide⟩ p hp j hj hq fz1_70_42 fz2_70_42
  · exact match_zero_fix ⟨71, by decide⟩ ⟨42, by decide⟩ p hp j hj hq fz1_71_42 fz2_71_42
  · exact match_zero_fix ⟨72, by decide⟩ ⟨42, by decide⟩ p hp j hj hq fz1_72_42 fz2_72_42
  · exact match_zero_fix ⟨73, by decide⟩ ⟨42, by decide⟩ p hp j hj hq fz1_73_42 fz2_73_42
  · exact match_zero_fix ⟨74, by decide⟩ ⟨42, by decide⟩ p hp j hj hq fz1_74_42 fz2_74_42
  · exact pair_75_42 p hp hrep j hj hq
  · exact pair_76_42 p hp hrep j hj hq
  · exact pair_77_42 p hp hrep j hj hq
  · exact pair_78_42 p hp hrep j hj hq
  · exact pair_79_42 p hp hrep j hj hq
  · exact match_zero_fix ⟨80, by decide⟩ ⟨42, by decide⟩ p hp j hj hq fz1_80_42 fz2_80_42
  · exact match_zero_fix ⟨81, by decide⟩ ⟨42, by decide⟩ p hp j hj hq fz1_81_42 fz2_81_42
  · exact match_zero_fix ⟨82, by decide⟩ ⟨42, by decide⟩ p hp j hj hq fz1_82_42 fz2_82_42
  · exact match_zero_fix ⟨83, by decide⟩ ⟨42, by decide⟩ p hp j hj hq fz1_83_42 fz2_83_42
  · exact match_zero_fix ⟨84, by decide⟩ ⟨42, by decide⟩ p hp j hj hq fz1_84_42 fz2_84_42
  · exact match_zero_fix ⟨85, by decide⟩ ⟨42, by decide⟩ p hp j hj hq fz1_85_42 fz2_85_42
  · exact match_zero_fix ⟨86, by decide⟩ ⟨42, by decide⟩ p hp j hj hq fz1_86_42 fz2_86_42
  · exact match_zero_fix ⟨87, by decide⟩ ⟨42, by decide⟩ p hp j hj hq fz1_87_42 fz2_87_42
  · exact match_zero_fix ⟨88, by decide⟩ ⟨42, by decide⟩ p hp j hj hq fz1_88_42 fz2_88_42
  · exact match_zero_fix ⟨89, by decide⟩ ⟨42, by decide⟩ p hp j hj hq fz1_89_42 fz2_89_42
  · exact match_zero_fix ⟨90, by decide⟩ ⟨42, by decide⟩ p hp j hj hq fz1_90_42 fz2_90_42
  · exact match_zero_fix ⟨91, by decide⟩ ⟨42, by decide⟩ p hp j hj hq fz1_91_42 fz2_91_42
  · exact match_zero_fix ⟨92, by decide⟩ ⟨42, by decide⟩ p hp j hj hq fz1_92_42 fz2_92_42
  · exact match_zero_fix ⟨93, by decide⟩ ⟨42, by decide⟩ p hp j hj hq fz1_93_42 fz2_93_42
  · exact match_zero_fix ⟨94, by decide⟩ ⟨42, by decide⟩ p hp j hj hq fz1_94_42 fz2_94_42
  · exact match_zero_fix ⟨95, by decide⟩ ⟨42, by decide⟩ p hp j hj hq fz1_95_42 fz2_95_42
  · exact match_zero_fix ⟨96, by decide⟩ ⟨42, by decide⟩ p hp j hj hq fz1_96_42 fz2_96_42
  · exact match_zero_fix ⟨97, by decide⟩ ⟨42, by decide⟩ p hp j hj hq fz1_97_42 fz2_97_42
  · exact match_zero_fix ⟨98, by decide⟩ ⟨42, by decide⟩ p hp j hj hq fz1_98_42 fz2_98_42
  · exact match_zero_fix ⟨99, by decide⟩ ⟨42, by decide⟩ p hp j hj hq fz1_99_42 fz2_99_42
  · exact match_zero_fix ⟨100, by decide⟩ ⟨42, by decide⟩ p hp j hj hq fz1_100_42 fz2_100_42
  · exact match_zero_fix ⟨101, by decide⟩ ⟨42, by decide⟩ p hp j hj hq fz1_101_42 fz2_101_42
  · exact match_zero_fix ⟨102, by decide⟩ ⟨42, by decide⟩ p hp j hj hq fz1_102_42 fz2_102_42
  · exact match_zero_fix ⟨103, by decide⟩ ⟨42, by decide⟩ p hp j hj hq fz1_103_42 fz2_103_42
  · exact pair_104_42 p hp hrep j hj hq
  · exact match_zero_fix ⟨105, by decide⟩ ⟨42, by decide⟩ p hp j hj hq fz1_105_42 fz2_105_42
  · exact match_zero_fix ⟨106, by decide⟩ ⟨42, by decide⟩ p hp j hj hq fz1_106_42 fz2_106_42
  · exact match_zero_fix ⟨107, by decide⟩ ⟨42, by decide⟩ p hp j hj hq fz1_107_42 fz2_107_42
  · exact match_zero_fix ⟨108, by decide⟩ ⟨42, by decide⟩ p hp j hj hq fz1_108_42 fz2_108_42
  · exact match_zero_fix ⟨109, by decide⟩ ⟨42, by decide⟩ p hp j hj hq fz1_109_42 fz2_109_42
  · exact match_zero_fix ⟨110, by decide⟩ ⟨42, by decide⟩ p hp j hj hq fz1_110_42 fz2_110_42
  · exact match_zero_fix ⟨111, by decide⟩ ⟨42, by decide⟩ p hp j hj hq fz1_111_42 fz2_111_42
  · exact match_zero_fix ⟨112, by decide⟩ ⟨42, by decide⟩ p hp j hj hq fz1_112_42 fz2_112_42
  · exact match_zero_fix ⟨113, by decide⟩ ⟨42, by decide⟩ p hp j hj hq fz1_113_42 fz2_113_42
  · exact match_zero_fix ⟨114, by decide⟩ ⟨42, by decide⟩ p hp j hj hq fz1_114_42 fz2_114_42
  · exact match_zero_fix ⟨115, by decide⟩ ⟨42, by decide⟩ p hp j hj hq fz1_115_42 fz2_115_42
  · exact match_zero_fix ⟨116, by decide⟩ ⟨42, by decide⟩ p hp j hj hq fz1_116_42 fz2_116_42
  · exact match_zero_fix ⟨117, by decide⟩ ⟨42, by decide⟩ p hp j hj hq fz1_117_42 fz2_117_42
  · exact match_zero_fix ⟨118, by decide⟩ ⟨42, by decide⟩ p hp j hj hq fz1_118_42 fz2_118_42
  · exact match_zero_fix ⟨119, by decide⟩ ⟨42, by decide⟩ p hp j hj hq fz1_119_42 fz2_119_42
  · exact pair_120_42 p hp hrep j hj hq
  · exact match_zero_fix ⟨121, by decide⟩ ⟨42, by decide⟩ p hp j hj hq fz1_121_42 fz2_121_42
  · exact pair_122_42 p hp hrep j hj hq
  · exact match_zero_fix ⟨123, by decide⟩ ⟨42, by decide⟩ p hp j hj hq fz1_123_42 fz2_123_42
  · exact match_zero_fix ⟨124, by decide⟩ ⟨42, by decide⟩ p hp j hj hq fz1_124_42 fz2_124_42
  · exact match_zero_fix ⟨125, by decide⟩ ⟨42, by decide⟩ p hp j hj hq fz1_125_42 fz2_125_42
  · exact match_zero_fix ⟨126, by decide⟩ ⟨42, by decide⟩ p hp j hj hq fz1_126_42 fz2_126_42
  · exact match_zero_fix ⟨127, by decide⟩ ⟨42, by decide⟩ p hp j hj hq fz1_127_42 fz2_127_42
  · exact match_zero_fix ⟨128, by decide⟩ ⟨42, by decide⟩ p hp j hj hq fz1_128_42 fz2_128_42
  · exact pair_129_42 p hp hrep j hj hq
  · exact match_zero_fix ⟨130, by decide⟩ ⟨42, by decide⟩ p hp j hj hq fz1_130_42 fz2_130_42
  · exact pair_131_42 p hp hrep j hj hq
  · exact match_zero_fix ⟨132, by decide⟩ ⟨42, by decide⟩ p hp j hj hq fz1_132_42 fz2_132_42
  · exact match_zero_fix ⟨133, by decide⟩ ⟨42, by decide⟩ p hp j hj hq fz1_133_42 fz2_133_42
  · exact match_zero_fix ⟨134, by decide⟩ ⟨42, by decide⟩ p hp j hj hq fz1_134_42 fz2_134_42
  · exact match_zero_fix ⟨135, by decide⟩ ⟨42, by decide⟩ p hp j hj hq fz1_135_42 fz2_135_42
  · exact match_zero_fix ⟨136, by decide⟩ ⟨42, by decide⟩ p hp j hj hq fz1_136_42 fz2_136_42
  · exact match_zero_fix ⟨137, by decide⟩ ⟨42, by decide⟩ p hp j hj hq fz1_137_42 fz2_137_42
  · exact pair_138_42 p hp hrep j hj hq
  · exact match_zero_fix ⟨139, by decide⟩ ⟨42, by decide⟩ p hp j hj hq fz1_139_42 fz2_139_42
  · exact match_zero_fix ⟨140, by decide⟩ ⟨42, by decide⟩ p hp j hj hq fz1_140_42 fz2_140_42
  · exact match_zero_fix ⟨141, by decide⟩ ⟨42, by decide⟩ p hp j hj hq fz1_141_42 fz2_141_42
  · exact match_zero_fix ⟨142, by decide⟩ ⟨42, by decide⟩ p hp j hj hq fz1_142_42 fz2_142_42
  · exact match_zero_fix ⟨143, by decide⟩ ⟨42, by decide⟩ p hp j hj hq fz1_143_42 fz2_143_42
  · exact pair_144_42 p hp hrep j hj hq
  · exact match_zero_fix ⟨145, by decide⟩ ⟨42, by decide⟩ p hp j hj hq fz1_145_42 fz2_145_42
  · exact match_zero_fix ⟨146, by decide⟩ ⟨42, by decide⟩ p hp j hj hq fz1_146_42 fz2_146_42
  · exact pair_147_42 p hp hrep j hj hq

theorem master_43 (p : Nat) (hp : p < (Q2.transData.getD 43 []).length)
    (hrep : (Q2.cosetIsRep.getD 43 []).getD p false = true)
    (rK : Fin 148) (j : Nat) (hj : j < (repChars.getD rK.val []).length)
    (hq : (normIsRep.getD rK.val []).getD j false = true) :
    species (Q2.reps (⟨43, by decide⟩ : Fin 148)) (colE2 ⟨43, by decide⟩ p hp)
        (rowE2 rK j hj hq)
      = species (reps (⟨43, by decide⟩ : Fin 148))
        (colE1 ⟨43, by decide⟩ p (transLenTr ⟨43, by decide⟩ p hp)) (rowE1 rK j hj) := by
  rcases rK with ⟨nK, hnK⟩; interval_cases nK
  · exact match_zero_len ⟨0, by decide⟩ ⟨43, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨1, by decide⟩ ⟨43, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨2, by decide⟩ ⟨43, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨3, by decide⟩ ⟨43, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨4, by decide⟩ ⟨43, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨5, by decide⟩ ⟨43, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨6, by decide⟩ ⟨43, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨7, by decide⟩ ⟨43, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨8, by decide⟩ ⟨43, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨9, by decide⟩ ⟨43, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨10, by decide⟩ ⟨43, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨11, by decide⟩ ⟨43, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨12, by decide⟩ ⟨43, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_fix ⟨13, by decide⟩ ⟨43, by decide⟩ p hp j hj hq fz1_13_43 fz2_13_43
  · exact match_zero_fix ⟨14, by decide⟩ ⟨43, by decide⟩ p hp j hj hq fz1_14_43 fz2_14_43
  · exact match_zero_fix ⟨15, by decide⟩ ⟨43, by decide⟩ p hp j hj hq fz1_15_43 fz2_15_43
  · exact match_zero_fix ⟨16, by decide⟩ ⟨43, by decide⟩ p hp j hj hq fz1_16_43 fz2_16_43
  · exact match_zero_fix ⟨17, by decide⟩ ⟨43, by decide⟩ p hp j hj hq fz1_17_43 fz2_17_43
  · exact match_zero_fix ⟨18, by decide⟩ ⟨43, by decide⟩ p hp j hj hq fz1_18_43 fz2_18_43
  · exact match_zero_fix ⟨19, by decide⟩ ⟨43, by decide⟩ p hp j hj hq fz1_19_43 fz2_19_43
  · exact match_zero_fix ⟨20, by decide⟩ ⟨43, by decide⟩ p hp j hj hq fz1_20_43 fz2_20_43
  · exact match_zero_fix ⟨21, by decide⟩ ⟨43, by decide⟩ p hp j hj hq fz1_21_43 fz2_21_43
  · exact match_zero_fix ⟨22, by decide⟩ ⟨43, by decide⟩ p hp j hj hq fz1_22_43 fz2_22_43
  · exact match_zero_fix ⟨23, by decide⟩ ⟨43, by decide⟩ p hp j hj hq fz1_23_43 fz2_23_43
  · exact match_zero_fix ⟨24, by decide⟩ ⟨43, by decide⟩ p hp j hj hq fz1_24_43 fz2_24_43
  · exact match_zero_fix ⟨25, by decide⟩ ⟨43, by decide⟩ p hp j hj hq fz1_25_43 fz2_25_43
  · exact match_zero_fix ⟨26, by decide⟩ ⟨43, by decide⟩ p hp j hj hq fz1_26_43 fz2_26_43
  · exact match_zero_fix ⟨27, by decide⟩ ⟨43, by decide⟩ p hp j hj hq fz1_27_43 fz2_27_43
  · exact match_zero_fix ⟨28, by decide⟩ ⟨43, by decide⟩ p hp j hj hq fz1_28_43 fz2_28_43
  · exact match_zero_fix ⟨29, by decide⟩ ⟨43, by decide⟩ p hp j hj hq fz1_29_43 fz2_29_43
  · exact match_zero_fix ⟨30, by decide⟩ ⟨43, by decide⟩ p hp j hj hq fz1_30_43 fz2_30_43
  · exact match_zero_fix ⟨31, by decide⟩ ⟨43, by decide⟩ p hp j hj hq fz1_31_43 fz2_31_43
  · exact match_zero_fix ⟨32, by decide⟩ ⟨43, by decide⟩ p hp j hj hq fz1_32_43 fz2_32_43
  · exact match_zero_fix ⟨33, by decide⟩ ⟨43, by decide⟩ p hp j hj hq fz1_33_43 fz2_33_43
  · exact match_zero_fix ⟨34, by decide⟩ ⟨43, by decide⟩ p hp j hj hq fz1_34_43 fz2_34_43
  · exact match_zero_fix ⟨35, by decide⟩ ⟨43, by decide⟩ p hp j hj hq fz1_35_43 fz2_35_43
  · exact match_zero_fix ⟨36, by decide⟩ ⟨43, by decide⟩ p hp j hj hq fz1_36_43 fz2_36_43
  · exact match_zero_fix ⟨37, by decide⟩ ⟨43, by decide⟩ p hp j hj hq fz1_37_43 fz2_37_43
  · exact match_zero_fix ⟨38, by decide⟩ ⟨43, by decide⟩ p hp j hj hq fz1_38_43 fz2_38_43
  · exact match_zero_fix ⟨39, by decide⟩ ⟨43, by decide⟩ p hp j hj hq fz1_39_43 fz2_39_43
  · exact match_zero_fix ⟨40, by decide⟩ ⟨43, by decide⟩ p hp j hj hq fz1_40_43 fz2_40_43
  · exact match_zero_fix ⟨41, by decide⟩ ⟨43, by decide⟩ p hp j hj hq fz1_41_43 fz2_41_43
  · exact match_zero_fix ⟨42, by decide⟩ ⟨43, by decide⟩ p hp j hj hq fz1_42_43 fz2_42_43
  · exact pair_43_43 p hp hrep j hj hq
  · exact match_zero_fix ⟨44, by decide⟩ ⟨43, by decide⟩ p hp j hj hq fz1_44_43 fz2_44_43
  · exact match_zero_fix ⟨45, by decide⟩ ⟨43, by decide⟩ p hp j hj hq fz1_45_43 fz2_45_43
  · exact match_zero_fix ⟨46, by decide⟩ ⟨43, by decide⟩ p hp j hj hq fz1_46_43 fz2_46_43
  · exact match_zero_fix ⟨47, by decide⟩ ⟨43, by decide⟩ p hp j hj hq fz1_47_43 fz2_47_43
  · exact match_zero_fix ⟨48, by decide⟩ ⟨43, by decide⟩ p hp j hj hq fz1_48_43 fz2_48_43
  · exact match_zero_fix ⟨49, by decide⟩ ⟨43, by decide⟩ p hp j hj hq fz1_49_43 fz2_49_43
  · exact match_zero_fix ⟨50, by decide⟩ ⟨43, by decide⟩ p hp j hj hq fz1_50_43 fz2_50_43
  · exact match_zero_fix ⟨51, by decide⟩ ⟨43, by decide⟩ p hp j hj hq fz1_51_43 fz2_51_43
  · exact match_zero_fix ⟨52, by decide⟩ ⟨43, by decide⟩ p hp j hj hq fz1_52_43 fz2_52_43
  · exact match_zero_fix ⟨53, by decide⟩ ⟨43, by decide⟩ p hp j hj hq fz1_53_43 fz2_53_43
  · exact match_zero_fix ⟨54, by decide⟩ ⟨43, by decide⟩ p hp j hj hq fz1_54_43 fz2_54_43
  · exact pair_55_43 p hp hrep j hj hq
  · exact pair_56_43 p hp hrep j hj hq
  · exact pair_57_43 p hp hrep j hj hq
  · exact pair_58_43 p hp hrep j hj hq
  · exact pair_59_43 p hp hrep j hj hq
  · exact match_zero_fix ⟨60, by decide⟩ ⟨43, by decide⟩ p hp j hj hq fz1_60_43 fz2_60_43
  · exact match_zero_fix ⟨61, by decide⟩ ⟨43, by decide⟩ p hp j hj hq fz1_61_43 fz2_61_43
  · exact match_zero_fix ⟨62, by decide⟩ ⟨43, by decide⟩ p hp j hj hq fz1_62_43 fz2_62_43
  · exact match_zero_fix ⟨63, by decide⟩ ⟨43, by decide⟩ p hp j hj hq fz1_63_43 fz2_63_43
  · exact match_zero_fix ⟨64, by decide⟩ ⟨43, by decide⟩ p hp j hj hq fz1_64_43 fz2_64_43
  · exact match_zero_fix ⟨65, by decide⟩ ⟨43, by decide⟩ p hp j hj hq fz1_65_43 fz2_65_43
  · exact match_zero_fix ⟨66, by decide⟩ ⟨43, by decide⟩ p hp j hj hq fz1_66_43 fz2_66_43
  · exact match_zero_fix ⟨67, by decide⟩ ⟨43, by decide⟩ p hp j hj hq fz1_67_43 fz2_67_43
  · exact match_zero_fix ⟨68, by decide⟩ ⟨43, by decide⟩ p hp j hj hq fz1_68_43 fz2_68_43
  · exact match_zero_fix ⟨69, by decide⟩ ⟨43, by decide⟩ p hp j hj hq fz1_69_43 fz2_69_43
  · exact match_zero_fix ⟨70, by decide⟩ ⟨43, by decide⟩ p hp j hj hq fz1_70_43 fz2_70_43
  · exact match_zero_fix ⟨71, by decide⟩ ⟨43, by decide⟩ p hp j hj hq fz1_71_43 fz2_71_43
  · exact match_zero_fix ⟨72, by decide⟩ ⟨43, by decide⟩ p hp j hj hq fz1_72_43 fz2_72_43
  · exact match_zero_fix ⟨73, by decide⟩ ⟨43, by decide⟩ p hp j hj hq fz1_73_43 fz2_73_43
  · exact match_zero_fix ⟨74, by decide⟩ ⟨43, by decide⟩ p hp j hj hq fz1_74_43 fz2_74_43
  · exact match_zero_fix ⟨75, by decide⟩ ⟨43, by decide⟩ p hp j hj hq fz1_75_43 fz2_75_43
  · exact match_zero_fix ⟨76, by decide⟩ ⟨43, by decide⟩ p hp j hj hq fz1_76_43 fz2_76_43
  · exact match_zero_fix ⟨77, by decide⟩ ⟨43, by decide⟩ p hp j hj hq fz1_77_43 fz2_77_43
  · exact match_zero_fix ⟨78, by decide⟩ ⟨43, by decide⟩ p hp j hj hq fz1_78_43 fz2_78_43
  · exact match_zero_fix ⟨79, by decide⟩ ⟨43, by decide⟩ p hp j hj hq fz1_79_43 fz2_79_43
  · exact match_zero_fix ⟨80, by decide⟩ ⟨43, by decide⟩ p hp j hj hq fz1_80_43 fz2_80_43
  · exact match_zero_fix ⟨81, by decide⟩ ⟨43, by decide⟩ p hp j hj hq fz1_81_43 fz2_81_43
  · exact match_zero_fix ⟨82, by decide⟩ ⟨43, by decide⟩ p hp j hj hq fz1_82_43 fz2_82_43
  · exact match_zero_fix ⟨83, by decide⟩ ⟨43, by decide⟩ p hp j hj hq fz1_83_43 fz2_83_43
  · exact match_zero_fix ⟨84, by decide⟩ ⟨43, by decide⟩ p hp j hj hq fz1_84_43 fz2_84_43
  · exact match_zero_fix ⟨85, by decide⟩ ⟨43, by decide⟩ p hp j hj hq fz1_85_43 fz2_85_43
  · exact match_zero_fix ⟨86, by decide⟩ ⟨43, by decide⟩ p hp j hj hq fz1_86_43 fz2_86_43
  · exact match_zero_fix ⟨87, by decide⟩ ⟨43, by decide⟩ p hp j hj hq fz1_87_43 fz2_87_43
  · exact match_zero_fix ⟨88, by decide⟩ ⟨43, by decide⟩ p hp j hj hq fz1_88_43 fz2_88_43
  · exact match_zero_fix ⟨89, by decide⟩ ⟨43, by decide⟩ p hp j hj hq fz1_89_43 fz2_89_43
  · exact match_zero_fix ⟨90, by decide⟩ ⟨43, by decide⟩ p hp j hj hq fz1_90_43 fz2_90_43
  · exact match_zero_fix ⟨91, by decide⟩ ⟨43, by decide⟩ p hp j hj hq fz1_91_43 fz2_91_43
  · exact match_zero_fix ⟨92, by decide⟩ ⟨43, by decide⟩ p hp j hj hq fz1_92_43 fz2_92_43
  · exact match_zero_fix ⟨93, by decide⟩ ⟨43, by decide⟩ p hp j hj hq fz1_93_43 fz2_93_43
  · exact match_zero_fix ⟨94, by decide⟩ ⟨43, by decide⟩ p hp j hj hq fz1_94_43 fz2_94_43
  · exact match_zero_fix ⟨95, by decide⟩ ⟨43, by decide⟩ p hp j hj hq fz1_95_43 fz2_95_43
  · exact match_zero_fix ⟨96, by decide⟩ ⟨43, by decide⟩ p hp j hj hq fz1_96_43 fz2_96_43
  · exact match_zero_fix ⟨97, by decide⟩ ⟨43, by decide⟩ p hp j hj hq fz1_97_43 fz2_97_43
  · exact match_zero_fix ⟨98, by decide⟩ ⟨43, by decide⟩ p hp j hj hq fz1_98_43 fz2_98_43
  · exact match_zero_fix ⟨99, by decide⟩ ⟨43, by decide⟩ p hp j hj hq fz1_99_43 fz2_99_43
  · exact match_zero_fix ⟨100, by decide⟩ ⟨43, by decide⟩ p hp j hj hq fz1_100_43 fz2_100_43
  · exact match_zero_fix ⟨101, by decide⟩ ⟨43, by decide⟩ p hp j hj hq fz1_101_43 fz2_101_43
  · exact match_zero_fix ⟨102, by decide⟩ ⟨43, by decide⟩ p hp j hj hq fz1_102_43 fz2_102_43
  · exact match_zero_fix ⟨103, by decide⟩ ⟨43, by decide⟩ p hp j hj hq fz1_103_43 fz2_103_43
  · exact match_zero_fix ⟨104, by decide⟩ ⟨43, by decide⟩ p hp j hj hq fz1_104_43 fz2_104_43
  · exact pair_105_43 p hp hrep j hj hq
  · exact match_zero_fix ⟨106, by decide⟩ ⟨43, by decide⟩ p hp j hj hq fz1_106_43 fz2_106_43
  · exact match_zero_fix ⟨107, by decide⟩ ⟨43, by decide⟩ p hp j hj hq fz1_107_43 fz2_107_43
  · exact match_zero_fix ⟨108, by decide⟩ ⟨43, by decide⟩ p hp j hj hq fz1_108_43 fz2_108_43
  · exact match_zero_fix ⟨109, by decide⟩ ⟨43, by decide⟩ p hp j hj hq fz1_109_43 fz2_109_43
  · exact match_zero_fix ⟨110, by decide⟩ ⟨43, by decide⟩ p hp j hj hq fz1_110_43 fz2_110_43
  · exact match_zero_fix ⟨111, by decide⟩ ⟨43, by decide⟩ p hp j hj hq fz1_111_43 fz2_111_43
  · exact match_zero_fix ⟨112, by decide⟩ ⟨43, by decide⟩ p hp j hj hq fz1_112_43 fz2_112_43
  · exact match_zero_fix ⟨113, by decide⟩ ⟨43, by decide⟩ p hp j hj hq fz1_113_43 fz2_113_43
  · exact match_zero_fix ⟨114, by decide⟩ ⟨43, by decide⟩ p hp j hj hq fz1_114_43 fz2_114_43
  · exact match_zero_fix ⟨115, by decide⟩ ⟨43, by decide⟩ p hp j hj hq fz1_115_43 fz2_115_43
  · exact pair_116_43 p hp hrep j hj hq
  · exact match_zero_fix ⟨117, by decide⟩ ⟨43, by decide⟩ p hp j hj hq fz1_117_43 fz2_117_43
  · exact match_zero_fix ⟨118, by decide⟩ ⟨43, by decide⟩ p hp j hj hq fz1_118_43 fz2_118_43
  · exact match_zero_fix ⟨119, by decide⟩ ⟨43, by decide⟩ p hp j hj hq fz1_119_43 fz2_119_43
  · exact match_zero_fix ⟨120, by decide⟩ ⟨43, by decide⟩ p hp j hj hq fz1_120_43 fz2_120_43
  · exact match_zero_fix ⟨121, by decide⟩ ⟨43, by decide⟩ p hp j hj hq fz1_121_43 fz2_121_43
  · exact match_zero_fix ⟨122, by decide⟩ ⟨43, by decide⟩ p hp j hj hq fz1_122_43 fz2_122_43
  · exact match_zero_fix ⟨123, by decide⟩ ⟨43, by decide⟩ p hp j hj hq fz1_123_43 fz2_123_43
  · exact match_zero_fix ⟨124, by decide⟩ ⟨43, by decide⟩ p hp j hj hq fz1_124_43 fz2_124_43
  · exact pair_125_43 p hp hrep j hj hq
  · exact match_zero_fix ⟨126, by decide⟩ ⟨43, by decide⟩ p hp j hj hq fz1_126_43 fz2_126_43
  · exact match_zero_fix ⟨127, by decide⟩ ⟨43, by decide⟩ p hp j hj hq fz1_127_43 fz2_127_43
  · exact match_zero_fix ⟨128, by decide⟩ ⟨43, by decide⟩ p hp j hj hq fz1_128_43 fz2_128_43
  · exact pair_129_43 p hp hrep j hj hq
  · exact match_zero_fix ⟨130, by decide⟩ ⟨43, by decide⟩ p hp j hj hq fz1_130_43 fz2_130_43
  · exact match_zero_fix ⟨131, by decide⟩ ⟨43, by decide⟩ p hp j hj hq fz1_131_43 fz2_131_43
  · exact match_zero_fix ⟨132, by decide⟩ ⟨43, by decide⟩ p hp j hj hq fz1_132_43 fz2_132_43
  · exact pair_133_43 p hp hrep j hj hq
  · exact match_zero_fix ⟨134, by decide⟩ ⟨43, by decide⟩ p hp j hj hq fz1_134_43 fz2_134_43
  · exact match_zero_fix ⟨135, by decide⟩ ⟨43, by decide⟩ p hp j hj hq fz1_135_43 fz2_135_43
  · exact match_zero_fix ⟨136, by decide⟩ ⟨43, by decide⟩ p hp j hj hq fz1_136_43 fz2_136_43
  · exact pair_137_43 p hp hrep j hj hq
  · exact match_zero_fix ⟨138, by decide⟩ ⟨43, by decide⟩ p hp j hj hq fz1_138_43 fz2_138_43
  · exact match_zero_fix ⟨139, by decide⟩ ⟨43, by decide⟩ p hp j hj hq fz1_139_43 fz2_139_43
  · exact match_zero_fix ⟨140, by decide⟩ ⟨43, by decide⟩ p hp j hj hq fz1_140_43 fz2_140_43
  · exact match_zero_fix ⟨141, by decide⟩ ⟨43, by decide⟩ p hp j hj hq fz1_141_43 fz2_141_43
  · exact match_zero_fix ⟨142, by decide⟩ ⟨43, by decide⟩ p hp j hj hq fz1_142_43 fz2_142_43
  · exact match_zero_fix ⟨143, by decide⟩ ⟨43, by decide⟩ p hp j hj hq fz1_143_43 fz2_143_43
  · exact match_zero_fix ⟨144, by decide⟩ ⟨43, by decide⟩ p hp j hj hq fz1_144_43 fz2_144_43
  · exact pair_145_43 p hp hrep j hj hq
  · exact match_zero_fix ⟨146, by decide⟩ ⟨43, by decide⟩ p hp j hj hq fz1_146_43 fz2_146_43
  · exact pair_147_43 p hp hrep j hj hq

theorem master_44 (p : Nat) (hp : p < (Q2.transData.getD 44 []).length)
    (hrep : (Q2.cosetIsRep.getD 44 []).getD p false = true)
    (rK : Fin 148) (j : Nat) (hj : j < (repChars.getD rK.val []).length)
    (hq : (normIsRep.getD rK.val []).getD j false = true) :
    species (Q2.reps (⟨44, by decide⟩ : Fin 148)) (colE2 ⟨44, by decide⟩ p hp)
        (rowE2 rK j hj hq)
      = species (reps (⟨44, by decide⟩ : Fin 148))
        (colE1 ⟨44, by decide⟩ p (transLenTr ⟨44, by decide⟩ p hp)) (rowE1 rK j hj) := by
  rcases rK with ⟨nK, hnK⟩; interval_cases nK
  · exact match_zero_len ⟨0, by decide⟩ ⟨44, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨1, by decide⟩ ⟨44, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨2, by decide⟩ ⟨44, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨3, by decide⟩ ⟨44, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨4, by decide⟩ ⟨44, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨5, by decide⟩ ⟨44, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨6, by decide⟩ ⟨44, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨7, by decide⟩ ⟨44, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨8, by decide⟩ ⟨44, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨9, by decide⟩ ⟨44, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨10, by decide⟩ ⟨44, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨11, by decide⟩ ⟨44, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨12, by decide⟩ ⟨44, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_fix ⟨13, by decide⟩ ⟨44, by decide⟩ p hp j hj hq fz1_13_44 fz2_13_44
  · exact match_zero_fix ⟨14, by decide⟩ ⟨44, by decide⟩ p hp j hj hq fz1_14_44 fz2_14_44
  · exact match_zero_fix ⟨15, by decide⟩ ⟨44, by decide⟩ p hp j hj hq fz1_15_44 fz2_15_44
  · exact match_zero_fix ⟨16, by decide⟩ ⟨44, by decide⟩ p hp j hj hq fz1_16_44 fz2_16_44
  · exact match_zero_fix ⟨17, by decide⟩ ⟨44, by decide⟩ p hp j hj hq fz1_17_44 fz2_17_44
  · exact match_zero_fix ⟨18, by decide⟩ ⟨44, by decide⟩ p hp j hj hq fz1_18_44 fz2_18_44
  · exact match_zero_fix ⟨19, by decide⟩ ⟨44, by decide⟩ p hp j hj hq fz1_19_44 fz2_19_44
  · exact match_zero_fix ⟨20, by decide⟩ ⟨44, by decide⟩ p hp j hj hq fz1_20_44 fz2_20_44
  · exact match_zero_fix ⟨21, by decide⟩ ⟨44, by decide⟩ p hp j hj hq fz1_21_44 fz2_21_44
  · exact match_zero_fix ⟨22, by decide⟩ ⟨44, by decide⟩ p hp j hj hq fz1_22_44 fz2_22_44
  · exact match_zero_fix ⟨23, by decide⟩ ⟨44, by decide⟩ p hp j hj hq fz1_23_44 fz2_23_44
  · exact match_zero_fix ⟨24, by decide⟩ ⟨44, by decide⟩ p hp j hj hq fz1_24_44 fz2_24_44
  · exact match_zero_fix ⟨25, by decide⟩ ⟨44, by decide⟩ p hp j hj hq fz1_25_44 fz2_25_44
  · exact match_zero_fix ⟨26, by decide⟩ ⟨44, by decide⟩ p hp j hj hq fz1_26_44 fz2_26_44
  · exact match_zero_fix ⟨27, by decide⟩ ⟨44, by decide⟩ p hp j hj hq fz1_27_44 fz2_27_44
  · exact match_zero_fix ⟨28, by decide⟩ ⟨44, by decide⟩ p hp j hj hq fz1_28_44 fz2_28_44
  · exact match_zero_fix ⟨29, by decide⟩ ⟨44, by decide⟩ p hp j hj hq fz1_29_44 fz2_29_44
  · exact match_zero_fix ⟨30, by decide⟩ ⟨44, by decide⟩ p hp j hj hq fz1_30_44 fz2_30_44
  · exact match_zero_fix ⟨31, by decide⟩ ⟨44, by decide⟩ p hp j hj hq fz1_31_44 fz2_31_44
  · exact match_zero_fix ⟨32, by decide⟩ ⟨44, by decide⟩ p hp j hj hq fz1_32_44 fz2_32_44
  · exact match_zero_fix ⟨33, by decide⟩ ⟨44, by decide⟩ p hp j hj hq fz1_33_44 fz2_33_44
  · exact match_zero_fix ⟨34, by decide⟩ ⟨44, by decide⟩ p hp j hj hq fz1_34_44 fz2_34_44
  · exact match_zero_fix ⟨35, by decide⟩ ⟨44, by decide⟩ p hp j hj hq fz1_35_44 fz2_35_44
  · exact match_zero_fix ⟨36, by decide⟩ ⟨44, by decide⟩ p hp j hj hq fz1_36_44 fz2_36_44
  · exact match_zero_fix ⟨37, by decide⟩ ⟨44, by decide⟩ p hp j hj hq fz1_37_44 fz2_37_44
  · exact match_zero_fix ⟨38, by decide⟩ ⟨44, by decide⟩ p hp j hj hq fz1_38_44 fz2_38_44
  · exact match_zero_fix ⟨39, by decide⟩ ⟨44, by decide⟩ p hp j hj hq fz1_39_44 fz2_39_44
  · exact match_zero_fix ⟨40, by decide⟩ ⟨44, by decide⟩ p hp j hj hq fz1_40_44 fz2_40_44
  · exact match_zero_fix ⟨41, by decide⟩ ⟨44, by decide⟩ p hp j hj hq fz1_41_44 fz2_41_44
  · exact match_zero_fix ⟨42, by decide⟩ ⟨44, by decide⟩ p hp j hj hq fz1_42_44 fz2_42_44
  · exact match_zero_fix ⟨43, by decide⟩ ⟨44, by decide⟩ p hp j hj hq fz1_43_44 fz2_43_44
  · exact pair_44_44 p hp hrep j hj hq
  · exact match_zero_fix ⟨45, by decide⟩ ⟨44, by decide⟩ p hp j hj hq fz1_45_44 fz2_45_44
  · exact match_zero_fix ⟨46, by decide⟩ ⟨44, by decide⟩ p hp j hj hq fz1_46_44 fz2_46_44
  · exact match_zero_fix ⟨47, by decide⟩ ⟨44, by decide⟩ p hp j hj hq fz1_47_44 fz2_47_44
  · exact match_zero_fix ⟨48, by decide⟩ ⟨44, by decide⟩ p hp j hj hq fz1_48_44 fz2_48_44
  · exact match_zero_fix ⟨49, by decide⟩ ⟨44, by decide⟩ p hp j hj hq fz1_49_44 fz2_49_44
  · exact match_zero_fix ⟨50, by decide⟩ ⟨44, by decide⟩ p hp j hj hq fz1_50_44 fz2_50_44
  · exact match_zero_fix ⟨51, by decide⟩ ⟨44, by decide⟩ p hp j hj hq fz1_51_44 fz2_51_44
  · exact match_zero_fix ⟨52, by decide⟩ ⟨44, by decide⟩ p hp j hj hq fz1_52_44 fz2_52_44
  · exact match_zero_fix ⟨53, by decide⟩ ⟨44, by decide⟩ p hp j hj hq fz1_53_44 fz2_53_44
  · exact match_zero_fix ⟨54, by decide⟩ ⟨44, by decide⟩ p hp j hj hq fz1_54_44 fz2_54_44
  · exact match_zero_fix ⟨55, by decide⟩ ⟨44, by decide⟩ p hp j hj hq fz1_55_44 fz2_55_44
  · exact match_zero_fix ⟨56, by decide⟩ ⟨44, by decide⟩ p hp j hj hq fz1_56_44 fz2_56_44
  · exact match_zero_fix ⟨57, by decide⟩ ⟨44, by decide⟩ p hp j hj hq fz1_57_44 fz2_57_44
  · exact match_zero_fix ⟨58, by decide⟩ ⟨44, by decide⟩ p hp j hj hq fz1_58_44 fz2_58_44
  · exact match_zero_fix ⟨59, by decide⟩ ⟨44, by decide⟩ p hp j hj hq fz1_59_44 fz2_59_44
  · exact pair_60_44 p hp hrep j hj hq
  · exact pair_61_44 p hp hrep j hj hq
  · exact pair_62_44 p hp hrep j hj hq
  · exact pair_63_44 p hp hrep j hj hq
  · exact pair_64_44 p hp hrep j hj hq
  · exact match_zero_fix ⟨65, by decide⟩ ⟨44, by decide⟩ p hp j hj hq fz1_65_44 fz2_65_44
  · exact match_zero_fix ⟨66, by decide⟩ ⟨44, by decide⟩ p hp j hj hq fz1_66_44 fz2_66_44
  · exact match_zero_fix ⟨67, by decide⟩ ⟨44, by decide⟩ p hp j hj hq fz1_67_44 fz2_67_44
  · exact match_zero_fix ⟨68, by decide⟩ ⟨44, by decide⟩ p hp j hj hq fz1_68_44 fz2_68_44
  · exact match_zero_fix ⟨69, by decide⟩ ⟨44, by decide⟩ p hp j hj hq fz1_69_44 fz2_69_44
  · exact match_zero_fix ⟨70, by decide⟩ ⟨44, by decide⟩ p hp j hj hq fz1_70_44 fz2_70_44
  · exact match_zero_fix ⟨71, by decide⟩ ⟨44, by decide⟩ p hp j hj hq fz1_71_44 fz2_71_44
  · exact match_zero_fix ⟨72, by decide⟩ ⟨44, by decide⟩ p hp j hj hq fz1_72_44 fz2_72_44
  · exact match_zero_fix ⟨73, by decide⟩ ⟨44, by decide⟩ p hp j hj hq fz1_73_44 fz2_73_44
  · exact match_zero_fix ⟨74, by decide⟩ ⟨44, by decide⟩ p hp j hj hq fz1_74_44 fz2_74_44
  · exact match_zero_fix ⟨75, by decide⟩ ⟨44, by decide⟩ p hp j hj hq fz1_75_44 fz2_75_44
  · exact match_zero_fix ⟨76, by decide⟩ ⟨44, by decide⟩ p hp j hj hq fz1_76_44 fz2_76_44
  · exact match_zero_fix ⟨77, by decide⟩ ⟨44, by decide⟩ p hp j hj hq fz1_77_44 fz2_77_44
  · exact match_zero_fix ⟨78, by decide⟩ ⟨44, by decide⟩ p hp j hj hq fz1_78_44 fz2_78_44
  · exact match_zero_fix ⟨79, by decide⟩ ⟨44, by decide⟩ p hp j hj hq fz1_79_44 fz2_79_44
  · exact match_zero_fix ⟨80, by decide⟩ ⟨44, by decide⟩ p hp j hj hq fz1_80_44 fz2_80_44
  · exact match_zero_fix ⟨81, by decide⟩ ⟨44, by decide⟩ p hp j hj hq fz1_81_44 fz2_81_44
  · exact match_zero_fix ⟨82, by decide⟩ ⟨44, by decide⟩ p hp j hj hq fz1_82_44 fz2_82_44
  · exact match_zero_fix ⟨83, by decide⟩ ⟨44, by decide⟩ p hp j hj hq fz1_83_44 fz2_83_44
  · exact match_zero_fix ⟨84, by decide⟩ ⟨44, by decide⟩ p hp j hj hq fz1_84_44 fz2_84_44
  · exact match_zero_fix ⟨85, by decide⟩ ⟨44, by decide⟩ p hp j hj hq fz1_85_44 fz2_85_44
  · exact match_zero_fix ⟨86, by decide⟩ ⟨44, by decide⟩ p hp j hj hq fz1_86_44 fz2_86_44
  · exact match_zero_fix ⟨87, by decide⟩ ⟨44, by decide⟩ p hp j hj hq fz1_87_44 fz2_87_44
  · exact match_zero_fix ⟨88, by decide⟩ ⟨44, by decide⟩ p hp j hj hq fz1_88_44 fz2_88_44
  · exact match_zero_fix ⟨89, by decide⟩ ⟨44, by decide⟩ p hp j hj hq fz1_89_44 fz2_89_44
  · exact match_zero_fix ⟨90, by decide⟩ ⟨44, by decide⟩ p hp j hj hq fz1_90_44 fz2_90_44
  · exact match_zero_fix ⟨91, by decide⟩ ⟨44, by decide⟩ p hp j hj hq fz1_91_44 fz2_91_44
  · exact match_zero_fix ⟨92, by decide⟩ ⟨44, by decide⟩ p hp j hj hq fz1_92_44 fz2_92_44
  · exact match_zero_fix ⟨93, by decide⟩ ⟨44, by decide⟩ p hp j hj hq fz1_93_44 fz2_93_44
  · exact match_zero_fix ⟨94, by decide⟩ ⟨44, by decide⟩ p hp j hj hq fz1_94_44 fz2_94_44
  · exact match_zero_fix ⟨95, by decide⟩ ⟨44, by decide⟩ p hp j hj hq fz1_95_44 fz2_95_44
  · exact match_zero_fix ⟨96, by decide⟩ ⟨44, by decide⟩ p hp j hj hq fz1_96_44 fz2_96_44
  · exact match_zero_fix ⟨97, by decide⟩ ⟨44, by decide⟩ p hp j hj hq fz1_97_44 fz2_97_44
  · exact match_zero_fix ⟨98, by decide⟩ ⟨44, by decide⟩ p hp j hj hq fz1_98_44 fz2_98_44
  · exact match_zero_fix ⟨99, by decide⟩ ⟨44, by decide⟩ p hp j hj hq fz1_99_44 fz2_99_44
  · exact match_zero_fix ⟨100, by decide⟩ ⟨44, by decide⟩ p hp j hj hq fz1_100_44 fz2_100_44
  · exact match_zero_fix ⟨101, by decide⟩ ⟨44, by decide⟩ p hp j hj hq fz1_101_44 fz2_101_44
  · exact match_zero_fix ⟨102, by decide⟩ ⟨44, by decide⟩ p hp j hj hq fz1_102_44 fz2_102_44
  · exact match_zero_fix ⟨103, by decide⟩ ⟨44, by decide⟩ p hp j hj hq fz1_103_44 fz2_103_44
  · exact match_zero_fix ⟨104, by decide⟩ ⟨44, by decide⟩ p hp j hj hq fz1_104_44 fz2_104_44
  · exact match_zero_fix ⟨105, by decide⟩ ⟨44, by decide⟩ p hp j hj hq fz1_105_44 fz2_105_44
  · exact pair_106_44 p hp hrep j hj hq
  · exact match_zero_fix ⟨107, by decide⟩ ⟨44, by decide⟩ p hp j hj hq fz1_107_44 fz2_107_44
  · exact match_zero_fix ⟨108, by decide⟩ ⟨44, by decide⟩ p hp j hj hq fz1_108_44 fz2_108_44
  · exact match_zero_fix ⟨109, by decide⟩ ⟨44, by decide⟩ p hp j hj hq fz1_109_44 fz2_109_44
  · exact match_zero_fix ⟨110, by decide⟩ ⟨44, by decide⟩ p hp j hj hq fz1_110_44 fz2_110_44
  · exact match_zero_fix ⟨111, by decide⟩ ⟨44, by decide⟩ p hp j hj hq fz1_111_44 fz2_111_44
  · exact match_zero_fix ⟨112, by decide⟩ ⟨44, by decide⟩ p hp j hj hq fz1_112_44 fz2_112_44
  · exact match_zero_fix ⟨113, by decide⟩ ⟨44, by decide⟩ p hp j hj hq fz1_113_44 fz2_113_44
  · exact match_zero_fix ⟨114, by decide⟩ ⟨44, by decide⟩ p hp j hj hq fz1_114_44 fz2_114_44
  · exact match_zero_fix ⟨115, by decide⟩ ⟨44, by decide⟩ p hp j hj hq fz1_115_44 fz2_115_44
  · exact match_zero_fix ⟨116, by decide⟩ ⟨44, by decide⟩ p hp j hj hq fz1_116_44 fz2_116_44
  · exact pair_117_44 p hp hrep j hj hq
  · exact match_zero_fix ⟨118, by decide⟩ ⟨44, by decide⟩ p hp j hj hq fz1_118_44 fz2_118_44
  · exact match_zero_fix ⟨119, by decide⟩ ⟨44, by decide⟩ p hp j hj hq fz1_119_44 fz2_119_44
  · exact match_zero_fix ⟨120, by decide⟩ ⟨44, by decide⟩ p hp j hj hq fz1_120_44 fz2_120_44
  · exact pair_121_44 p hp hrep j hj hq
  · exact match_zero_fix ⟨122, by decide⟩ ⟨44, by decide⟩ p hp j hj hq fz1_122_44 fz2_122_44
  · exact match_zero_fix ⟨123, by decide⟩ ⟨44, by decide⟩ p hp j hj hq fz1_123_44 fz2_123_44
  · exact match_zero_fix ⟨124, by decide⟩ ⟨44, by decide⟩ p hp j hj hq fz1_124_44 fz2_124_44
  · exact match_zero_fix ⟨125, by decide⟩ ⟨44, by decide⟩ p hp j hj hq fz1_125_44 fz2_125_44
  · exact match_zero_fix ⟨126, by decide⟩ ⟨44, by decide⟩ p hp j hj hq fz1_126_44 fz2_126_44
  · exact match_zero_fix ⟨127, by decide⟩ ⟨44, by decide⟩ p hp j hj hq fz1_127_44 fz2_127_44
  · exact match_zero_fix ⟨128, by decide⟩ ⟨44, by decide⟩ p hp j hj hq fz1_128_44 fz2_128_44
  · exact match_zero_fix ⟨129, by decide⟩ ⟨44, by decide⟩ p hp j hj hq fz1_129_44 fz2_129_44
  · exact pair_130_44 p hp hrep j hj hq
  · exact match_zero_fix ⟨131, by decide⟩ ⟨44, by decide⟩ p hp j hj hq fz1_131_44 fz2_131_44
  · exact match_zero_fix ⟨132, by decide⟩ ⟨44, by decide⟩ p hp j hj hq fz1_132_44 fz2_132_44
  · exact match_zero_fix ⟨133, by decide⟩ ⟨44, by decide⟩ p hp j hj hq fz1_133_44 fz2_133_44
  · exact pair_134_44 p hp hrep j hj hq
  · exact match_zero_fix ⟨135, by decide⟩ ⟨44, by decide⟩ p hp j hj hq fz1_135_44 fz2_135_44
  · exact match_zero_fix ⟨136, by decide⟩ ⟨44, by decide⟩ p hp j hj hq fz1_136_44 fz2_136_44
  · exact match_zero_fix ⟨137, by decide⟩ ⟨44, by decide⟩ p hp j hj hq fz1_137_44 fz2_137_44
  · exact pair_138_44 p hp hrep j hj hq
  · exact match_zero_fix ⟨139, by decide⟩ ⟨44, by decide⟩ p hp j hj hq fz1_139_44 fz2_139_44
  · exact match_zero_fix ⟨140, by decide⟩ ⟨44, by decide⟩ p hp j hj hq fz1_140_44 fz2_140_44
  · exact match_zero_fix ⟨141, by decide⟩ ⟨44, by decide⟩ p hp j hj hq fz1_141_44 fz2_141_44
  · exact match_zero_fix ⟨142, by decide⟩ ⟨44, by decide⟩ p hp j hj hq fz1_142_44 fz2_142_44
  · exact match_zero_fix ⟨143, by decide⟩ ⟨44, by decide⟩ p hp j hj hq fz1_143_44 fz2_143_44
  · exact match_zero_fix ⟨144, by decide⟩ ⟨44, by decide⟩ p hp j hj hq fz1_144_44 fz2_144_44
  · exact pair_145_44 p hp hrep j hj hq
  · exact match_zero_fix ⟨146, by decide⟩ ⟨44, by decide⟩ p hp j hj hq fz1_146_44 fz2_146_44
  · exact pair_147_44 p hp hrep j hj hq

theorem master_45 (p : Nat) (hp : p < (Q2.transData.getD 45 []).length)
    (hrep : (Q2.cosetIsRep.getD 45 []).getD p false = true)
    (rK : Fin 148) (j : Nat) (hj : j < (repChars.getD rK.val []).length)
    (hq : (normIsRep.getD rK.val []).getD j false = true) :
    species (Q2.reps (⟨45, by decide⟩ : Fin 148)) (colE2 ⟨45, by decide⟩ p hp)
        (rowE2 rK j hj hq)
      = species (reps (⟨45, by decide⟩ : Fin 148))
        (colE1 ⟨45, by decide⟩ p (transLenTr ⟨45, by decide⟩ p hp)) (rowE1 rK j hj) := by
  rcases rK with ⟨nK, hnK⟩; interval_cases nK
  · exact match_zero_len ⟨0, by decide⟩ ⟨45, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨1, by decide⟩ ⟨45, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨2, by decide⟩ ⟨45, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨3, by decide⟩ ⟨45, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨4, by decide⟩ ⟨45, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨5, by decide⟩ ⟨45, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨6, by decide⟩ ⟨45, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨7, by decide⟩ ⟨45, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨8, by decide⟩ ⟨45, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨9, by decide⟩ ⟨45, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨10, by decide⟩ ⟨45, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨11, by decide⟩ ⟨45, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨12, by decide⟩ ⟨45, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_fix ⟨13, by decide⟩ ⟨45, by decide⟩ p hp j hj hq fz1_13_45 fz2_13_45
  · exact match_zero_fix ⟨14, by decide⟩ ⟨45, by decide⟩ p hp j hj hq fz1_14_45 fz2_14_45
  · exact match_zero_fix ⟨15, by decide⟩ ⟨45, by decide⟩ p hp j hj hq fz1_15_45 fz2_15_45
  · exact match_zero_fix ⟨16, by decide⟩ ⟨45, by decide⟩ p hp j hj hq fz1_16_45 fz2_16_45
  · exact match_zero_fix ⟨17, by decide⟩ ⟨45, by decide⟩ p hp j hj hq fz1_17_45 fz2_17_45
  · exact match_zero_fix ⟨18, by decide⟩ ⟨45, by decide⟩ p hp j hj hq fz1_18_45 fz2_18_45
  · exact match_zero_fix ⟨19, by decide⟩ ⟨45, by decide⟩ p hp j hj hq fz1_19_45 fz2_19_45
  · exact match_zero_fix ⟨20, by decide⟩ ⟨45, by decide⟩ p hp j hj hq fz1_20_45 fz2_20_45
  · exact match_zero_fix ⟨21, by decide⟩ ⟨45, by decide⟩ p hp j hj hq fz1_21_45 fz2_21_45
  · exact match_zero_fix ⟨22, by decide⟩ ⟨45, by decide⟩ p hp j hj hq fz1_22_45 fz2_22_45
  · exact match_zero_fix ⟨23, by decide⟩ ⟨45, by decide⟩ p hp j hj hq fz1_23_45 fz2_23_45
  · exact match_zero_fix ⟨24, by decide⟩ ⟨45, by decide⟩ p hp j hj hq fz1_24_45 fz2_24_45
  · exact match_zero_fix ⟨25, by decide⟩ ⟨45, by decide⟩ p hp j hj hq fz1_25_45 fz2_25_45
  · exact match_zero_fix ⟨26, by decide⟩ ⟨45, by decide⟩ p hp j hj hq fz1_26_45 fz2_26_45
  · exact match_zero_fix ⟨27, by decide⟩ ⟨45, by decide⟩ p hp j hj hq fz1_27_45 fz2_27_45
  · exact match_zero_fix ⟨28, by decide⟩ ⟨45, by decide⟩ p hp j hj hq fz1_28_45 fz2_28_45
  · exact match_zero_fix ⟨29, by decide⟩ ⟨45, by decide⟩ p hp j hj hq fz1_29_45 fz2_29_45
  · exact match_zero_fix ⟨30, by decide⟩ ⟨45, by decide⟩ p hp j hj hq fz1_30_45 fz2_30_45
  · exact match_zero_fix ⟨31, by decide⟩ ⟨45, by decide⟩ p hp j hj hq fz1_31_45 fz2_31_45
  · exact match_zero_fix ⟨32, by decide⟩ ⟨45, by decide⟩ p hp j hj hq fz1_32_45 fz2_32_45
  · exact match_zero_fix ⟨33, by decide⟩ ⟨45, by decide⟩ p hp j hj hq fz1_33_45 fz2_33_45
  · exact match_zero_fix ⟨34, by decide⟩ ⟨45, by decide⟩ p hp j hj hq fz1_34_45 fz2_34_45
  · exact match_zero_fix ⟨35, by decide⟩ ⟨45, by decide⟩ p hp j hj hq fz1_35_45 fz2_35_45
  · exact match_zero_fix ⟨36, by decide⟩ ⟨45, by decide⟩ p hp j hj hq fz1_36_45 fz2_36_45
  · exact match_zero_fix ⟨37, by decide⟩ ⟨45, by decide⟩ p hp j hj hq fz1_37_45 fz2_37_45
  · exact match_zero_fix ⟨38, by decide⟩ ⟨45, by decide⟩ p hp j hj hq fz1_38_45 fz2_38_45
  · exact match_zero_fix ⟨39, by decide⟩ ⟨45, by decide⟩ p hp j hj hq fz1_39_45 fz2_39_45
  · exact match_zero_fix ⟨40, by decide⟩ ⟨45, by decide⟩ p hp j hj hq fz1_40_45 fz2_40_45
  · exact match_zero_fix ⟨41, by decide⟩ ⟨45, by decide⟩ p hp j hj hq fz1_41_45 fz2_41_45
  · exact match_zero_fix ⟨42, by decide⟩ ⟨45, by decide⟩ p hp j hj hq fz1_42_45 fz2_42_45
  · exact match_zero_fix ⟨43, by decide⟩ ⟨45, by decide⟩ p hp j hj hq fz1_43_45 fz2_43_45
  · exact match_zero_fix ⟨44, by decide⟩ ⟨45, by decide⟩ p hp j hj hq fz1_44_45 fz2_44_45
  · exact pair_45_45 p hp hrep j hj hq
  · exact match_zero_fix ⟨46, by decide⟩ ⟨45, by decide⟩ p hp j hj hq fz1_46_45 fz2_46_45
  · exact match_zero_fix ⟨47, by decide⟩ ⟨45, by decide⟩ p hp j hj hq fz1_47_45 fz2_47_45
  · exact match_zero_fix ⟨48, by decide⟩ ⟨45, by decide⟩ p hp j hj hq fz1_48_45 fz2_48_45
  · exact match_zero_fix ⟨49, by decide⟩ ⟨45, by decide⟩ p hp j hj hq fz1_49_45 fz2_49_45
  · exact match_zero_fix ⟨50, by decide⟩ ⟨45, by decide⟩ p hp j hj hq fz1_50_45 fz2_50_45
  · exact match_zero_fix ⟨51, by decide⟩ ⟨45, by decide⟩ p hp j hj hq fz1_51_45 fz2_51_45
  · exact match_zero_fix ⟨52, by decide⟩ ⟨45, by decide⟩ p hp j hj hq fz1_52_45 fz2_52_45
  · exact match_zero_fix ⟨53, by decide⟩ ⟨45, by decide⟩ p hp j hj hq fz1_53_45 fz2_53_45
  · exact match_zero_fix ⟨54, by decide⟩ ⟨45, by decide⟩ p hp j hj hq fz1_54_45 fz2_54_45
  · exact match_zero_fix ⟨55, by decide⟩ ⟨45, by decide⟩ p hp j hj hq fz1_55_45 fz2_55_45
  · exact match_zero_fix ⟨56, by decide⟩ ⟨45, by decide⟩ p hp j hj hq fz1_56_45 fz2_56_45
  · exact match_zero_fix ⟨57, by decide⟩ ⟨45, by decide⟩ p hp j hj hq fz1_57_45 fz2_57_45
  · exact match_zero_fix ⟨58, by decide⟩ ⟨45, by decide⟩ p hp j hj hq fz1_58_45 fz2_58_45
  · exact match_zero_fix ⟨59, by decide⟩ ⟨45, by decide⟩ p hp j hj hq fz1_59_45 fz2_59_45
  · exact match_zero_fix ⟨60, by decide⟩ ⟨45, by decide⟩ p hp j hj hq fz1_60_45 fz2_60_45
  · exact match_zero_fix ⟨61, by decide⟩ ⟨45, by decide⟩ p hp j hj hq fz1_61_45 fz2_61_45
  · exact match_zero_fix ⟨62, by decide⟩ ⟨45, by decide⟩ p hp j hj hq fz1_62_45 fz2_62_45
  · exact match_zero_fix ⟨63, by decide⟩ ⟨45, by decide⟩ p hp j hj hq fz1_63_45 fz2_63_45
  · exact match_zero_fix ⟨64, by decide⟩ ⟨45, by decide⟩ p hp j hj hq fz1_64_45 fz2_64_45
  · exact pair_65_45 p hp hrep j hj hq
  · exact pair_66_45 p hp hrep j hj hq
  · exact pair_67_45 p hp hrep j hj hq
  · exact pair_68_45 p hp hrep j hj hq
  · exact pair_69_45 p hp hrep j hj hq
  · exact match_zero_fix ⟨70, by decide⟩ ⟨45, by decide⟩ p hp j hj hq fz1_70_45 fz2_70_45
  · exact match_zero_fix ⟨71, by decide⟩ ⟨45, by decide⟩ p hp j hj hq fz1_71_45 fz2_71_45
  · exact match_zero_fix ⟨72, by decide⟩ ⟨45, by decide⟩ p hp j hj hq fz1_72_45 fz2_72_45
  · exact match_zero_fix ⟨73, by decide⟩ ⟨45, by decide⟩ p hp j hj hq fz1_73_45 fz2_73_45
  · exact match_zero_fix ⟨74, by decide⟩ ⟨45, by decide⟩ p hp j hj hq fz1_74_45 fz2_74_45
  · exact match_zero_fix ⟨75, by decide⟩ ⟨45, by decide⟩ p hp j hj hq fz1_75_45 fz2_75_45
  · exact match_zero_fix ⟨76, by decide⟩ ⟨45, by decide⟩ p hp j hj hq fz1_76_45 fz2_76_45
  · exact match_zero_fix ⟨77, by decide⟩ ⟨45, by decide⟩ p hp j hj hq fz1_77_45 fz2_77_45
  · exact match_zero_fix ⟨78, by decide⟩ ⟨45, by decide⟩ p hp j hj hq fz1_78_45 fz2_78_45
  · exact match_zero_fix ⟨79, by decide⟩ ⟨45, by decide⟩ p hp j hj hq fz1_79_45 fz2_79_45
  · exact match_zero_fix ⟨80, by decide⟩ ⟨45, by decide⟩ p hp j hj hq fz1_80_45 fz2_80_45
  · exact match_zero_fix ⟨81, by decide⟩ ⟨45, by decide⟩ p hp j hj hq fz1_81_45 fz2_81_45
  · exact match_zero_fix ⟨82, by decide⟩ ⟨45, by decide⟩ p hp j hj hq fz1_82_45 fz2_82_45
  · exact match_zero_fix ⟨83, by decide⟩ ⟨45, by decide⟩ p hp j hj hq fz1_83_45 fz2_83_45
  · exact match_zero_fix ⟨84, by decide⟩ ⟨45, by decide⟩ p hp j hj hq fz1_84_45 fz2_84_45
  · exact match_zero_fix ⟨85, by decide⟩ ⟨45, by decide⟩ p hp j hj hq fz1_85_45 fz2_85_45
  · exact match_zero_fix ⟨86, by decide⟩ ⟨45, by decide⟩ p hp j hj hq fz1_86_45 fz2_86_45
  · exact match_zero_fix ⟨87, by decide⟩ ⟨45, by decide⟩ p hp j hj hq fz1_87_45 fz2_87_45
  · exact match_zero_fix ⟨88, by decide⟩ ⟨45, by decide⟩ p hp j hj hq fz1_88_45 fz2_88_45
  · exact match_zero_fix ⟨89, by decide⟩ ⟨45, by decide⟩ p hp j hj hq fz1_89_45 fz2_89_45
  · exact match_zero_fix ⟨90, by decide⟩ ⟨45, by decide⟩ p hp j hj hq fz1_90_45 fz2_90_45
  · exact match_zero_fix ⟨91, by decide⟩ ⟨45, by decide⟩ p hp j hj hq fz1_91_45 fz2_91_45
  · exact match_zero_fix ⟨92, by decide⟩ ⟨45, by decide⟩ p hp j hj hq fz1_92_45 fz2_92_45
  · exact match_zero_fix ⟨93, by decide⟩ ⟨45, by decide⟩ p hp j hj hq fz1_93_45 fz2_93_45
  · exact match_zero_fix ⟨94, by decide⟩ ⟨45, by decide⟩ p hp j hj hq fz1_94_45 fz2_94_45
  · exact match_zero_fix ⟨95, by decide⟩ ⟨45, by decide⟩ p hp j hj hq fz1_95_45 fz2_95_45
  · exact match_zero_fix ⟨96, by decide⟩ ⟨45, by decide⟩ p hp j hj hq fz1_96_45 fz2_96_45
  · exact match_zero_fix ⟨97, by decide⟩ ⟨45, by decide⟩ p hp j hj hq fz1_97_45 fz2_97_45
  · exact match_zero_fix ⟨98, by decide⟩ ⟨45, by decide⟩ p hp j hj hq fz1_98_45 fz2_98_45
  · exact match_zero_fix ⟨99, by decide⟩ ⟨45, by decide⟩ p hp j hj hq fz1_99_45 fz2_99_45
  · exact match_zero_fix ⟨100, by decide⟩ ⟨45, by decide⟩ p hp j hj hq fz1_100_45 fz2_100_45
  · exact match_zero_fix ⟨101, by decide⟩ ⟨45, by decide⟩ p hp j hj hq fz1_101_45 fz2_101_45
  · exact match_zero_fix ⟨102, by decide⟩ ⟨45, by decide⟩ p hp j hj hq fz1_102_45 fz2_102_45
  · exact match_zero_fix ⟨103, by decide⟩ ⟨45, by decide⟩ p hp j hj hq fz1_103_45 fz2_103_45
  · exact match_zero_fix ⟨104, by decide⟩ ⟨45, by decide⟩ p hp j hj hq fz1_104_45 fz2_104_45
  · exact match_zero_fix ⟨105, by decide⟩ ⟨45, by decide⟩ p hp j hj hq fz1_105_45 fz2_105_45
  · exact match_zero_fix ⟨106, by decide⟩ ⟨45, by decide⟩ p hp j hj hq fz1_106_45 fz2_106_45
  · exact pair_107_45 p hp hrep j hj hq
  · exact match_zero_fix ⟨108, by decide⟩ ⟨45, by decide⟩ p hp j hj hq fz1_108_45 fz2_108_45
  · exact match_zero_fix ⟨109, by decide⟩ ⟨45, by decide⟩ p hp j hj hq fz1_109_45 fz2_109_45
  · exact match_zero_fix ⟨110, by decide⟩ ⟨45, by decide⟩ p hp j hj hq fz1_110_45 fz2_110_45
  · exact match_zero_fix ⟨111, by decide⟩ ⟨45, by decide⟩ p hp j hj hq fz1_111_45 fz2_111_45
  · exact match_zero_fix ⟨112, by decide⟩ ⟨45, by decide⟩ p hp j hj hq fz1_112_45 fz2_112_45
  · exact match_zero_fix ⟨113, by decide⟩ ⟨45, by decide⟩ p hp j hj hq fz1_113_45 fz2_113_45
  · exact match_zero_fix ⟨114, by decide⟩ ⟨45, by decide⟩ p hp j hj hq fz1_114_45 fz2_114_45
  · exact match_zero_fix ⟨115, by decide⟩ ⟨45, by decide⟩ p hp j hj hq fz1_115_45 fz2_115_45
  · exact match_zero_fix ⟨116, by decide⟩ ⟨45, by decide⟩ p hp j hj hq fz1_116_45 fz2_116_45
  · exact match_zero_fix ⟨117, by decide⟩ ⟨45, by decide⟩ p hp j hj hq fz1_117_45 fz2_117_45
  · exact pair_118_45 p hp hrep j hj hq
  · exact match_zero_fix ⟨119, by decide⟩ ⟨45, by decide⟩ p hp j hj hq fz1_119_45 fz2_119_45
  · exact match_zero_fix ⟨120, by decide⟩ ⟨45, by decide⟩ p hp j hj hq fz1_120_45 fz2_120_45
  · exact match_zero_fix ⟨121, by decide⟩ ⟨45, by decide⟩ p hp j hj hq fz1_121_45 fz2_121_45
  · exact pair_122_45 p hp hrep j hj hq
  · exact match_zero_fix ⟨123, by decide⟩ ⟨45, by decide⟩ p hp j hj hq fz1_123_45 fz2_123_45
  · exact match_zero_fix ⟨124, by decide⟩ ⟨45, by decide⟩ p hp j hj hq fz1_124_45 fz2_124_45
  · exact match_zero_fix ⟨125, by decide⟩ ⟨45, by decide⟩ p hp j hj hq fz1_125_45 fz2_125_45
  · exact pair_126_45 p hp hrep j hj hq
  · exact match_zero_fix ⟨127, by decide⟩ ⟨45, by decide⟩ p hp j hj hq fz1_127_45 fz2_127_45
  · exact match_zero_fix ⟨128, by decide⟩ ⟨45, by decide⟩ p hp j hj hq fz1_128_45 fz2_128_45
  · exact match_zero_fix ⟨129, by decide⟩ ⟨45, by decide⟩ p hp j hj hq fz1_129_45 fz2_129_45
  · exact match_zero_fix ⟨130, by decide⟩ ⟨45, by decide⟩ p hp j hj hq fz1_130_45 fz2_130_45
  · exact match_zero_fix ⟨131, by decide⟩ ⟨45, by decide⟩ p hp j hj hq fz1_131_45 fz2_131_45
  · exact match_zero_fix ⟨132, by decide⟩ ⟨45, by decide⟩ p hp j hj hq fz1_132_45 fz2_132_45
  · exact match_zero_fix ⟨133, by decide⟩ ⟨45, by decide⟩ p hp j hj hq fz1_133_45 fz2_133_45
  · exact match_zero_fix ⟨134, by decide⟩ ⟨45, by decide⟩ p hp j hj hq fz1_134_45 fz2_134_45
  · exact pair_135_45 p hp hrep j hj hq
  · exact match_zero_fix ⟨136, by decide⟩ ⟨45, by decide⟩ p hp j hj hq fz1_136_45 fz2_136_45
  · exact match_zero_fix ⟨137, by decide⟩ ⟨45, by decide⟩ p hp j hj hq fz1_137_45 fz2_137_45
  · exact match_zero_fix ⟨138, by decide⟩ ⟨45, by decide⟩ p hp j hj hq fz1_138_45 fz2_138_45
  · exact pair_139_45 p hp hrep j hj hq
  · exact match_zero_fix ⟨140, by decide⟩ ⟨45, by decide⟩ p hp j hj hq fz1_140_45 fz2_140_45
  · exact match_zero_fix ⟨141, by decide⟩ ⟨45, by decide⟩ p hp j hj hq fz1_141_45 fz2_141_45
  · exact match_zero_fix ⟨142, by decide⟩ ⟨45, by decide⟩ p hp j hj hq fz1_142_45 fz2_142_45
  · exact match_zero_fix ⟨143, by decide⟩ ⟨45, by decide⟩ p hp j hj hq fz1_143_45 fz2_143_45
  · exact match_zero_fix ⟨144, by decide⟩ ⟨45, by decide⟩ p hp j hj hq fz1_144_45 fz2_144_45
  · exact pair_145_45 p hp hrep j hj hq
  · exact match_zero_fix ⟨146, by decide⟩ ⟨45, by decide⟩ p hp j hj hq fz1_146_45 fz2_146_45
  · exact pair_147_45 p hp hrep j hj hq

theorem master_46 (p : Nat) (hp : p < (Q2.transData.getD 46 []).length)
    (hrep : (Q2.cosetIsRep.getD 46 []).getD p false = true)
    (rK : Fin 148) (j : Nat) (hj : j < (repChars.getD rK.val []).length)
    (hq : (normIsRep.getD rK.val []).getD j false = true) :
    species (Q2.reps (⟨46, by decide⟩ : Fin 148)) (colE2 ⟨46, by decide⟩ p hp)
        (rowE2 rK j hj hq)
      = species (reps (⟨46, by decide⟩ : Fin 148))
        (colE1 ⟨46, by decide⟩ p (transLenTr ⟨46, by decide⟩ p hp)) (rowE1 rK j hj) := by
  rcases rK with ⟨nK, hnK⟩; interval_cases nK
  · exact match_zero_len ⟨0, by decide⟩ ⟨46, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨1, by decide⟩ ⟨46, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨2, by decide⟩ ⟨46, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨3, by decide⟩ ⟨46, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨4, by decide⟩ ⟨46, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨5, by decide⟩ ⟨46, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨6, by decide⟩ ⟨46, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨7, by decide⟩ ⟨46, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨8, by decide⟩ ⟨46, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨9, by decide⟩ ⟨46, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨10, by decide⟩ ⟨46, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨11, by decide⟩ ⟨46, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨12, by decide⟩ ⟨46, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_fix ⟨13, by decide⟩ ⟨46, by decide⟩ p hp j hj hq fz1_13_46 fz2_13_46
  · exact match_zero_fix ⟨14, by decide⟩ ⟨46, by decide⟩ p hp j hj hq fz1_14_46 fz2_14_46
  · exact match_zero_fix ⟨15, by decide⟩ ⟨46, by decide⟩ p hp j hj hq fz1_15_46 fz2_15_46
  · exact match_zero_fix ⟨16, by decide⟩ ⟨46, by decide⟩ p hp j hj hq fz1_16_46 fz2_16_46
  · exact match_zero_fix ⟨17, by decide⟩ ⟨46, by decide⟩ p hp j hj hq fz1_17_46 fz2_17_46
  · exact match_zero_fix ⟨18, by decide⟩ ⟨46, by decide⟩ p hp j hj hq fz1_18_46 fz2_18_46
  · exact match_zero_fix ⟨19, by decide⟩ ⟨46, by decide⟩ p hp j hj hq fz1_19_46 fz2_19_46
  · exact match_zero_fix ⟨20, by decide⟩ ⟨46, by decide⟩ p hp j hj hq fz1_20_46 fz2_20_46
  · exact match_zero_fix ⟨21, by decide⟩ ⟨46, by decide⟩ p hp j hj hq fz1_21_46 fz2_21_46
  · exact match_zero_fix ⟨22, by decide⟩ ⟨46, by decide⟩ p hp j hj hq fz1_22_46 fz2_22_46
  · exact match_zero_fix ⟨23, by decide⟩ ⟨46, by decide⟩ p hp j hj hq fz1_23_46 fz2_23_46
  · exact match_zero_fix ⟨24, by decide⟩ ⟨46, by decide⟩ p hp j hj hq fz1_24_46 fz2_24_46
  · exact match_zero_fix ⟨25, by decide⟩ ⟨46, by decide⟩ p hp j hj hq fz1_25_46 fz2_25_46
  · exact match_zero_fix ⟨26, by decide⟩ ⟨46, by decide⟩ p hp j hj hq fz1_26_46 fz2_26_46
  · exact match_zero_fix ⟨27, by decide⟩ ⟨46, by decide⟩ p hp j hj hq fz1_27_46 fz2_27_46
  · exact match_zero_fix ⟨28, by decide⟩ ⟨46, by decide⟩ p hp j hj hq fz1_28_46 fz2_28_46
  · exact match_zero_fix ⟨29, by decide⟩ ⟨46, by decide⟩ p hp j hj hq fz1_29_46 fz2_29_46
  · exact match_zero_fix ⟨30, by decide⟩ ⟨46, by decide⟩ p hp j hj hq fz1_30_46 fz2_30_46
  · exact match_zero_fix ⟨31, by decide⟩ ⟨46, by decide⟩ p hp j hj hq fz1_31_46 fz2_31_46
  · exact match_zero_fix ⟨32, by decide⟩ ⟨46, by decide⟩ p hp j hj hq fz1_32_46 fz2_32_46
  · exact match_zero_fix ⟨33, by decide⟩ ⟨46, by decide⟩ p hp j hj hq fz1_33_46 fz2_33_46
  · exact match_zero_fix ⟨34, by decide⟩ ⟨46, by decide⟩ p hp j hj hq fz1_34_46 fz2_34_46
  · exact match_zero_fix ⟨35, by decide⟩ ⟨46, by decide⟩ p hp j hj hq fz1_35_46 fz2_35_46
  · exact match_zero_fix ⟨36, by decide⟩ ⟨46, by decide⟩ p hp j hj hq fz1_36_46 fz2_36_46
  · exact match_zero_fix ⟨37, by decide⟩ ⟨46, by decide⟩ p hp j hj hq fz1_37_46 fz2_37_46
  · exact match_zero_fix ⟨38, by decide⟩ ⟨46, by decide⟩ p hp j hj hq fz1_38_46 fz2_38_46
  · exact match_zero_fix ⟨39, by decide⟩ ⟨46, by decide⟩ p hp j hj hq fz1_39_46 fz2_39_46
  · exact match_zero_fix ⟨40, by decide⟩ ⟨46, by decide⟩ p hp j hj hq fz1_40_46 fz2_40_46
  · exact match_zero_fix ⟨41, by decide⟩ ⟨46, by decide⟩ p hp j hj hq fz1_41_46 fz2_41_46
  · exact match_zero_fix ⟨42, by decide⟩ ⟨46, by decide⟩ p hp j hj hq fz1_42_46 fz2_42_46
  · exact match_zero_fix ⟨43, by decide⟩ ⟨46, by decide⟩ p hp j hj hq fz1_43_46 fz2_43_46
  · exact match_zero_fix ⟨44, by decide⟩ ⟨46, by decide⟩ p hp j hj hq fz1_44_46 fz2_44_46
  · exact match_zero_fix ⟨45, by decide⟩ ⟨46, by decide⟩ p hp j hj hq fz1_45_46 fz2_45_46
  · exact pair_46_46 p hp hrep j hj hq
  · exact match_zero_fix ⟨47, by decide⟩ ⟨46, by decide⟩ p hp j hj hq fz1_47_46 fz2_47_46
  · exact match_zero_fix ⟨48, by decide⟩ ⟨46, by decide⟩ p hp j hj hq fz1_48_46 fz2_48_46
  · exact match_zero_fix ⟨49, by decide⟩ ⟨46, by decide⟩ p hp j hj hq fz1_49_46 fz2_49_46
  · exact match_zero_fix ⟨50, by decide⟩ ⟨46, by decide⟩ p hp j hj hq fz1_50_46 fz2_50_46
  · exact match_zero_fix ⟨51, by decide⟩ ⟨46, by decide⟩ p hp j hj hq fz1_51_46 fz2_51_46
  · exact match_zero_fix ⟨52, by decide⟩ ⟨46, by decide⟩ p hp j hj hq fz1_52_46 fz2_52_46
  · exact match_zero_fix ⟨53, by decide⟩ ⟨46, by decide⟩ p hp j hj hq fz1_53_46 fz2_53_46
  · exact match_zero_fix ⟨54, by decide⟩ ⟨46, by decide⟩ p hp j hj hq fz1_54_46 fz2_54_46
  · exact match_zero_fix ⟨55, by decide⟩ ⟨46, by decide⟩ p hp j hj hq fz1_55_46 fz2_55_46
  · exact match_zero_fix ⟨56, by decide⟩ ⟨46, by decide⟩ p hp j hj hq fz1_56_46 fz2_56_46
  · exact match_zero_fix ⟨57, by decide⟩ ⟨46, by decide⟩ p hp j hj hq fz1_57_46 fz2_57_46
  · exact match_zero_fix ⟨58, by decide⟩ ⟨46, by decide⟩ p hp j hj hq fz1_58_46 fz2_58_46
  · exact match_zero_fix ⟨59, by decide⟩ ⟨46, by decide⟩ p hp j hj hq fz1_59_46 fz2_59_46
  · exact match_zero_fix ⟨60, by decide⟩ ⟨46, by decide⟩ p hp j hj hq fz1_60_46 fz2_60_46
  · exact match_zero_fix ⟨61, by decide⟩ ⟨46, by decide⟩ p hp j hj hq fz1_61_46 fz2_61_46
  · exact match_zero_fix ⟨62, by decide⟩ ⟨46, by decide⟩ p hp j hj hq fz1_62_46 fz2_62_46
  · exact match_zero_fix ⟨63, by decide⟩ ⟨46, by decide⟩ p hp j hj hq fz1_63_46 fz2_63_46
  · exact match_zero_fix ⟨64, by decide⟩ ⟨46, by decide⟩ p hp j hj hq fz1_64_46 fz2_64_46
  · exact match_zero_fix ⟨65, by decide⟩ ⟨46, by decide⟩ p hp j hj hq fz1_65_46 fz2_65_46
  · exact match_zero_fix ⟨66, by decide⟩ ⟨46, by decide⟩ p hp j hj hq fz1_66_46 fz2_66_46
  · exact match_zero_fix ⟨67, by decide⟩ ⟨46, by decide⟩ p hp j hj hq fz1_67_46 fz2_67_46
  · exact match_zero_fix ⟨68, by decide⟩ ⟨46, by decide⟩ p hp j hj hq fz1_68_46 fz2_68_46
  · exact match_zero_fix ⟨69, by decide⟩ ⟨46, by decide⟩ p hp j hj hq fz1_69_46 fz2_69_46
  · exact pair_70_46 p hp hrep j hj hq
  · exact pair_71_46 p hp hrep j hj hq
  · exact pair_72_46 p hp hrep j hj hq
  · exact pair_73_46 p hp hrep j hj hq
  · exact pair_74_46 p hp hrep j hj hq
  · exact match_zero_fix ⟨75, by decide⟩ ⟨46, by decide⟩ p hp j hj hq fz1_75_46 fz2_75_46
  · exact match_zero_fix ⟨76, by decide⟩ ⟨46, by decide⟩ p hp j hj hq fz1_76_46 fz2_76_46
  · exact match_zero_fix ⟨77, by decide⟩ ⟨46, by decide⟩ p hp j hj hq fz1_77_46 fz2_77_46
  · exact match_zero_fix ⟨78, by decide⟩ ⟨46, by decide⟩ p hp j hj hq fz1_78_46 fz2_78_46
  · exact match_zero_fix ⟨79, by decide⟩ ⟨46, by decide⟩ p hp j hj hq fz1_79_46 fz2_79_46
  · exact match_zero_fix ⟨80, by decide⟩ ⟨46, by decide⟩ p hp j hj hq fz1_80_46 fz2_80_46
  · exact match_zero_fix ⟨81, by decide⟩ ⟨46, by decide⟩ p hp j hj hq fz1_81_46 fz2_81_46
  · exact match_zero_fix ⟨82, by decide⟩ ⟨46, by decide⟩ p hp j hj hq fz1_82_46 fz2_82_46
  · exact match_zero_fix ⟨83, by decide⟩ ⟨46, by decide⟩ p hp j hj hq fz1_83_46 fz2_83_46
  · exact match_zero_fix ⟨84, by decide⟩ ⟨46, by decide⟩ p hp j hj hq fz1_84_46 fz2_84_46
  · exact match_zero_fix ⟨85, by decide⟩ ⟨46, by decide⟩ p hp j hj hq fz1_85_46 fz2_85_46
  · exact match_zero_fix ⟨86, by decide⟩ ⟨46, by decide⟩ p hp j hj hq fz1_86_46 fz2_86_46
  · exact match_zero_fix ⟨87, by decide⟩ ⟨46, by decide⟩ p hp j hj hq fz1_87_46 fz2_87_46
  · exact match_zero_fix ⟨88, by decide⟩ ⟨46, by decide⟩ p hp j hj hq fz1_88_46 fz2_88_46
  · exact match_zero_fix ⟨89, by decide⟩ ⟨46, by decide⟩ p hp j hj hq fz1_89_46 fz2_89_46
  · exact match_zero_fix ⟨90, by decide⟩ ⟨46, by decide⟩ p hp j hj hq fz1_90_46 fz2_90_46
  · exact match_zero_fix ⟨91, by decide⟩ ⟨46, by decide⟩ p hp j hj hq fz1_91_46 fz2_91_46
  · exact match_zero_fix ⟨92, by decide⟩ ⟨46, by decide⟩ p hp j hj hq fz1_92_46 fz2_92_46
  · exact match_zero_fix ⟨93, by decide⟩ ⟨46, by decide⟩ p hp j hj hq fz1_93_46 fz2_93_46
  · exact match_zero_fix ⟨94, by decide⟩ ⟨46, by decide⟩ p hp j hj hq fz1_94_46 fz2_94_46
  · exact match_zero_fix ⟨95, by decide⟩ ⟨46, by decide⟩ p hp j hj hq fz1_95_46 fz2_95_46
  · exact match_zero_fix ⟨96, by decide⟩ ⟨46, by decide⟩ p hp j hj hq fz1_96_46 fz2_96_46
  · exact match_zero_fix ⟨97, by decide⟩ ⟨46, by decide⟩ p hp j hj hq fz1_97_46 fz2_97_46
  · exact match_zero_fix ⟨98, by decide⟩ ⟨46, by decide⟩ p hp j hj hq fz1_98_46 fz2_98_46
  · exact match_zero_fix ⟨99, by decide⟩ ⟨46, by decide⟩ p hp j hj hq fz1_99_46 fz2_99_46
  · exact match_zero_fix ⟨100, by decide⟩ ⟨46, by decide⟩ p hp j hj hq fz1_100_46 fz2_100_46
  · exact match_zero_fix ⟨101, by decide⟩ ⟨46, by decide⟩ p hp j hj hq fz1_101_46 fz2_101_46
  · exact match_zero_fix ⟨102, by decide⟩ ⟨46, by decide⟩ p hp j hj hq fz1_102_46 fz2_102_46
  · exact match_zero_fix ⟨103, by decide⟩ ⟨46, by decide⟩ p hp j hj hq fz1_103_46 fz2_103_46
  · exact match_zero_fix ⟨104, by decide⟩ ⟨46, by decide⟩ p hp j hj hq fz1_104_46 fz2_104_46
  · exact match_zero_fix ⟨105, by decide⟩ ⟨46, by decide⟩ p hp j hj hq fz1_105_46 fz2_105_46
  · exact match_zero_fix ⟨106, by decide⟩ ⟨46, by decide⟩ p hp j hj hq fz1_106_46 fz2_106_46
  · exact match_zero_fix ⟨107, by decide⟩ ⟨46, by decide⟩ p hp j hj hq fz1_107_46 fz2_107_46
  · exact pair_108_46 p hp hrep j hj hq
  · exact match_zero_fix ⟨109, by decide⟩ ⟨46, by decide⟩ p hp j hj hq fz1_109_46 fz2_109_46
  · exact match_zero_fix ⟨110, by decide⟩ ⟨46, by decide⟩ p hp j hj hq fz1_110_46 fz2_110_46
  · exact match_zero_fix ⟨111, by decide⟩ ⟨46, by decide⟩ p hp j hj hq fz1_111_46 fz2_111_46
  · exact match_zero_fix ⟨112, by decide⟩ ⟨46, by decide⟩ p hp j hj hq fz1_112_46 fz2_112_46
  · exact match_zero_fix ⟨113, by decide⟩ ⟨46, by decide⟩ p hp j hj hq fz1_113_46 fz2_113_46
  · exact match_zero_fix ⟨114, by decide⟩ ⟨46, by decide⟩ p hp j hj hq fz1_114_46 fz2_114_46
  · exact match_zero_fix ⟨115, by decide⟩ ⟨46, by decide⟩ p hp j hj hq fz1_115_46 fz2_115_46
  · exact match_zero_fix ⟨116, by decide⟩ ⟨46, by decide⟩ p hp j hj hq fz1_116_46 fz2_116_46
  · exact match_zero_fix ⟨117, by decide⟩ ⟨46, by decide⟩ p hp j hj hq fz1_117_46 fz2_117_46
  · exact match_zero_fix ⟨118, by decide⟩ ⟨46, by decide⟩ p hp j hj hq fz1_118_46 fz2_118_46
  · exact pair_119_46 p hp hrep j hj hq
  · exact match_zero_fix ⟨120, by decide⟩ ⟨46, by decide⟩ p hp j hj hq fz1_120_46 fz2_120_46
  · exact match_zero_fix ⟨121, by decide⟩ ⟨46, by decide⟩ p hp j hj hq fz1_121_46 fz2_121_46
  · exact match_zero_fix ⟨122, by decide⟩ ⟨46, by decide⟩ p hp j hj hq fz1_122_46 fz2_122_46
  · exact pair_123_46 p hp hrep j hj hq
  · exact match_zero_fix ⟨124, by decide⟩ ⟨46, by decide⟩ p hp j hj hq fz1_124_46 fz2_124_46
  · exact match_zero_fix ⟨125, by decide⟩ ⟨46, by decide⟩ p hp j hj hq fz1_125_46 fz2_125_46
  · exact match_zero_fix ⟨126, by decide⟩ ⟨46, by decide⟩ p hp j hj hq fz1_126_46 fz2_126_46
  · exact pair_127_46 p hp hrep j hj hq
  · exact match_zero_fix ⟨128, by decide⟩ ⟨46, by decide⟩ p hp j hj hq fz1_128_46 fz2_128_46
  · exact match_zero_fix ⟨129, by decide⟩ ⟨46, by decide⟩ p hp j hj hq fz1_129_46 fz2_129_46
  · exact match_zero_fix ⟨130, by decide⟩ ⟨46, by decide⟩ p hp j hj hq fz1_130_46 fz2_130_46
  · exact pair_131_46 p hp hrep j hj hq
  · exact match_zero_fix ⟨132, by decide⟩ ⟨46, by decide⟩ p hp j hj hq fz1_132_46 fz2_132_46
  · exact match_zero_fix ⟨133, by decide⟩ ⟨46, by decide⟩ p hp j hj hq fz1_133_46 fz2_133_46
  · exact match_zero_fix ⟨134, by decide⟩ ⟨46, by decide⟩ p hp j hj hq fz1_134_46 fz2_134_46
  · exact match_zero_fix ⟨135, by decide⟩ ⟨46, by decide⟩ p hp j hj hq fz1_135_46 fz2_135_46
  · exact match_zero_fix ⟨136, by decide⟩ ⟨46, by decide⟩ p hp j hj hq fz1_136_46 fz2_136_46
  · exact match_zero_fix ⟨137, by decide⟩ ⟨46, by decide⟩ p hp j hj hq fz1_137_46 fz2_137_46
  · exact match_zero_fix ⟨138, by decide⟩ ⟨46, by decide⟩ p hp j hj hq fz1_138_46 fz2_138_46
  · exact match_zero_fix ⟨139, by decide⟩ ⟨46, by decide⟩ p hp j hj hq fz1_139_46 fz2_139_46
  · exact pair_140_46 p hp hrep j hj hq
  · exact match_zero_fix ⟨141, by decide⟩ ⟨46, by decide⟩ p hp j hj hq fz1_141_46 fz2_141_46
  · exact match_zero_fix ⟨142, by decide⟩ ⟨46, by decide⟩ p hp j hj hq fz1_142_46 fz2_142_46
  · exact match_zero_fix ⟨143, by decide⟩ ⟨46, by decide⟩ p hp j hj hq fz1_143_46 fz2_143_46
  · exact match_zero_fix ⟨144, by decide⟩ ⟨46, by decide⟩ p hp j hj hq fz1_144_46 fz2_144_46
  · exact pair_145_46 p hp hrep j hj hq
  · exact match_zero_fix ⟨146, by decide⟩ ⟨46, by decide⟩ p hp j hj hq fz1_146_46 fz2_146_46
  · exact pair_147_46 p hp hrep j hj hq

theorem master_47 (p : Nat) (hp : p < (Q2.transData.getD 47 []).length)
    (hrep : (Q2.cosetIsRep.getD 47 []).getD p false = true)
    (rK : Fin 148) (j : Nat) (hj : j < (repChars.getD rK.val []).length)
    (hq : (normIsRep.getD rK.val []).getD j false = true) :
    species (Q2.reps (⟨47, by decide⟩ : Fin 148)) (colE2 ⟨47, by decide⟩ p hp)
        (rowE2 rK j hj hq)
      = species (reps (⟨47, by decide⟩ : Fin 148))
        (colE1 ⟨47, by decide⟩ p (transLenTr ⟨47, by decide⟩ p hp)) (rowE1 rK j hj) := by
  rcases rK with ⟨nK, hnK⟩; interval_cases nK
  · exact match_zero_len ⟨0, by decide⟩ ⟨47, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨1, by decide⟩ ⟨47, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨2, by decide⟩ ⟨47, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨3, by decide⟩ ⟨47, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨4, by decide⟩ ⟨47, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨5, by decide⟩ ⟨47, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨6, by decide⟩ ⟨47, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨7, by decide⟩ ⟨47, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨8, by decide⟩ ⟨47, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨9, by decide⟩ ⟨47, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨10, by decide⟩ ⟨47, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨11, by decide⟩ ⟨47, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨12, by decide⟩ ⟨47, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_fix ⟨13, by decide⟩ ⟨47, by decide⟩ p hp j hj hq fz1_13_47 fz2_13_47
  · exact match_zero_fix ⟨14, by decide⟩ ⟨47, by decide⟩ p hp j hj hq fz1_14_47 fz2_14_47
  · exact match_zero_fix ⟨15, by decide⟩ ⟨47, by decide⟩ p hp j hj hq fz1_15_47 fz2_15_47
  · exact match_zero_fix ⟨16, by decide⟩ ⟨47, by decide⟩ p hp j hj hq fz1_16_47 fz2_16_47
  · exact match_zero_fix ⟨17, by decide⟩ ⟨47, by decide⟩ p hp j hj hq fz1_17_47 fz2_17_47
  · exact match_zero_fix ⟨18, by decide⟩ ⟨47, by decide⟩ p hp j hj hq fz1_18_47 fz2_18_47
  · exact match_zero_fix ⟨19, by decide⟩ ⟨47, by decide⟩ p hp j hj hq fz1_19_47 fz2_19_47
  · exact match_zero_fix ⟨20, by decide⟩ ⟨47, by decide⟩ p hp j hj hq fz1_20_47 fz2_20_47
  · exact match_zero_fix ⟨21, by decide⟩ ⟨47, by decide⟩ p hp j hj hq fz1_21_47 fz2_21_47
  · exact match_zero_fix ⟨22, by decide⟩ ⟨47, by decide⟩ p hp j hj hq fz1_22_47 fz2_22_47
  · exact match_zero_fix ⟨23, by decide⟩ ⟨47, by decide⟩ p hp j hj hq fz1_23_47 fz2_23_47
  · exact match_zero_fix ⟨24, by decide⟩ ⟨47, by decide⟩ p hp j hj hq fz1_24_47 fz2_24_47
  · exact match_zero_fix ⟨25, by decide⟩ ⟨47, by decide⟩ p hp j hj hq fz1_25_47 fz2_25_47
  · exact match_zero_fix ⟨26, by decide⟩ ⟨47, by decide⟩ p hp j hj hq fz1_26_47 fz2_26_47
  · exact match_zero_fix ⟨27, by decide⟩ ⟨47, by decide⟩ p hp j hj hq fz1_27_47 fz2_27_47
  · exact match_zero_fix ⟨28, by decide⟩ ⟨47, by decide⟩ p hp j hj hq fz1_28_47 fz2_28_47
  · exact match_zero_fix ⟨29, by decide⟩ ⟨47, by decide⟩ p hp j hj hq fz1_29_47 fz2_29_47
  · exact match_zero_fix ⟨30, by decide⟩ ⟨47, by decide⟩ p hp j hj hq fz1_30_47 fz2_30_47
  · exact match_zero_fix ⟨31, by decide⟩ ⟨47, by decide⟩ p hp j hj hq fz1_31_47 fz2_31_47
  · exact match_zero_fix ⟨32, by decide⟩ ⟨47, by decide⟩ p hp j hj hq fz1_32_47 fz2_32_47
  · exact match_zero_fix ⟨33, by decide⟩ ⟨47, by decide⟩ p hp j hj hq fz1_33_47 fz2_33_47
  · exact match_zero_fix ⟨34, by decide⟩ ⟨47, by decide⟩ p hp j hj hq fz1_34_47 fz2_34_47
  · exact match_zero_fix ⟨35, by decide⟩ ⟨47, by decide⟩ p hp j hj hq fz1_35_47 fz2_35_47
  · exact match_zero_fix ⟨36, by decide⟩ ⟨47, by decide⟩ p hp j hj hq fz1_36_47 fz2_36_47
  · exact match_zero_fix ⟨37, by decide⟩ ⟨47, by decide⟩ p hp j hj hq fz1_37_47 fz2_37_47
  · exact match_zero_fix ⟨38, by decide⟩ ⟨47, by decide⟩ p hp j hj hq fz1_38_47 fz2_38_47
  · exact match_zero_fix ⟨39, by decide⟩ ⟨47, by decide⟩ p hp j hj hq fz1_39_47 fz2_39_47
  · exact match_zero_fix ⟨40, by decide⟩ ⟨47, by decide⟩ p hp j hj hq fz1_40_47 fz2_40_47
  · exact match_zero_fix ⟨41, by decide⟩ ⟨47, by decide⟩ p hp j hj hq fz1_41_47 fz2_41_47
  · exact match_zero_fix ⟨42, by decide⟩ ⟨47, by decide⟩ p hp j hj hq fz1_42_47 fz2_42_47
  · exact match_zero_fix ⟨43, by decide⟩ ⟨47, by decide⟩ p hp j hj hq fz1_43_47 fz2_43_47
  · exact match_zero_fix ⟨44, by decide⟩ ⟨47, by decide⟩ p hp j hj hq fz1_44_47 fz2_44_47
  · exact match_zero_fix ⟨45, by decide⟩ ⟨47, by decide⟩ p hp j hj hq fz1_45_47 fz2_45_47
  · exact match_zero_fix ⟨46, by decide⟩ ⟨47, by decide⟩ p hp j hj hq fz1_46_47 fz2_46_47
  · exact pair_47_47 p hp hrep j hj hq
  · exact match_zero_fix ⟨48, by decide⟩ ⟨47, by decide⟩ p hp j hj hq fz1_48_47 fz2_48_47
  · exact match_zero_fix ⟨49, by decide⟩ ⟨47, by decide⟩ p hp j hj hq fz1_49_47 fz2_49_47
  · exact match_zero_fix ⟨50, by decide⟩ ⟨47, by decide⟩ p hp j hj hq fz1_50_47 fz2_50_47
  · exact match_zero_fix ⟨51, by decide⟩ ⟨47, by decide⟩ p hp j hj hq fz1_51_47 fz2_51_47
  · exact match_zero_fix ⟨52, by decide⟩ ⟨47, by decide⟩ p hp j hj hq fz1_52_47 fz2_52_47
  · exact match_zero_fix ⟨53, by decide⟩ ⟨47, by decide⟩ p hp j hj hq fz1_53_47 fz2_53_47
  · exact match_zero_fix ⟨54, by decide⟩ ⟨47, by decide⟩ p hp j hj hq fz1_54_47 fz2_54_47
  · exact match_zero_fix ⟨55, by decide⟩ ⟨47, by decide⟩ p hp j hj hq fz1_55_47 fz2_55_47
  · exact match_zero_fix ⟨56, by decide⟩ ⟨47, by decide⟩ p hp j hj hq fz1_56_47 fz2_56_47
  · exact match_zero_fix ⟨57, by decide⟩ ⟨47, by decide⟩ p hp j hj hq fz1_57_47 fz2_57_47
  · exact match_zero_fix ⟨58, by decide⟩ ⟨47, by decide⟩ p hp j hj hq fz1_58_47 fz2_58_47
  · exact match_zero_fix ⟨59, by decide⟩ ⟨47, by decide⟩ p hp j hj hq fz1_59_47 fz2_59_47
  · exact match_zero_fix ⟨60, by decide⟩ ⟨47, by decide⟩ p hp j hj hq fz1_60_47 fz2_60_47
  · exact match_zero_fix ⟨61, by decide⟩ ⟨47, by decide⟩ p hp j hj hq fz1_61_47 fz2_61_47
  · exact match_zero_fix ⟨62, by decide⟩ ⟨47, by decide⟩ p hp j hj hq fz1_62_47 fz2_62_47
  · exact match_zero_fix ⟨63, by decide⟩ ⟨47, by decide⟩ p hp j hj hq fz1_63_47 fz2_63_47
  · exact match_zero_fix ⟨64, by decide⟩ ⟨47, by decide⟩ p hp j hj hq fz1_64_47 fz2_64_47
  · exact match_zero_fix ⟨65, by decide⟩ ⟨47, by decide⟩ p hp j hj hq fz1_65_47 fz2_65_47
  · exact match_zero_fix ⟨66, by decide⟩ ⟨47, by decide⟩ p hp j hj hq fz1_66_47 fz2_66_47
  · exact match_zero_fix ⟨67, by decide⟩ ⟨47, by decide⟩ p hp j hj hq fz1_67_47 fz2_67_47
  · exact match_zero_fix ⟨68, by decide⟩ ⟨47, by decide⟩ p hp j hj hq fz1_68_47 fz2_68_47
  · exact match_zero_fix ⟨69, by decide⟩ ⟨47, by decide⟩ p hp j hj hq fz1_69_47 fz2_69_47
  · exact match_zero_fix ⟨70, by decide⟩ ⟨47, by decide⟩ p hp j hj hq fz1_70_47 fz2_70_47
  · exact match_zero_fix ⟨71, by decide⟩ ⟨47, by decide⟩ p hp j hj hq fz1_71_47 fz2_71_47
  · exact match_zero_fix ⟨72, by decide⟩ ⟨47, by decide⟩ p hp j hj hq fz1_72_47 fz2_72_47
  · exact match_zero_fix ⟨73, by decide⟩ ⟨47, by decide⟩ p hp j hj hq fz1_73_47 fz2_73_47
  · exact match_zero_fix ⟨74, by decide⟩ ⟨47, by decide⟩ p hp j hj hq fz1_74_47 fz2_74_47
  · exact pair_75_47 p hp hrep j hj hq
  · exact pair_76_47 p hp hrep j hj hq
  · exact pair_77_47 p hp hrep j hj hq
  · exact pair_78_47 p hp hrep j hj hq
  · exact pair_79_47 p hp hrep j hj hq
  · exact match_zero_fix ⟨80, by decide⟩ ⟨47, by decide⟩ p hp j hj hq fz1_80_47 fz2_80_47
  · exact match_zero_fix ⟨81, by decide⟩ ⟨47, by decide⟩ p hp j hj hq fz1_81_47 fz2_81_47
  · exact match_zero_fix ⟨82, by decide⟩ ⟨47, by decide⟩ p hp j hj hq fz1_82_47 fz2_82_47
  · exact match_zero_fix ⟨83, by decide⟩ ⟨47, by decide⟩ p hp j hj hq fz1_83_47 fz2_83_47
  · exact match_zero_fix ⟨84, by decide⟩ ⟨47, by decide⟩ p hp j hj hq fz1_84_47 fz2_84_47
  · exact match_zero_fix ⟨85, by decide⟩ ⟨47, by decide⟩ p hp j hj hq fz1_85_47 fz2_85_47
  · exact match_zero_fix ⟨86, by decide⟩ ⟨47, by decide⟩ p hp j hj hq fz1_86_47 fz2_86_47
  · exact match_zero_fix ⟨87, by decide⟩ ⟨47, by decide⟩ p hp j hj hq fz1_87_47 fz2_87_47
  · exact match_zero_fix ⟨88, by decide⟩ ⟨47, by decide⟩ p hp j hj hq fz1_88_47 fz2_88_47
  · exact match_zero_fix ⟨89, by decide⟩ ⟨47, by decide⟩ p hp j hj hq fz1_89_47 fz2_89_47
  · exact match_zero_fix ⟨90, by decide⟩ ⟨47, by decide⟩ p hp j hj hq fz1_90_47 fz2_90_47
  · exact match_zero_fix ⟨91, by decide⟩ ⟨47, by decide⟩ p hp j hj hq fz1_91_47 fz2_91_47
  · exact match_zero_fix ⟨92, by decide⟩ ⟨47, by decide⟩ p hp j hj hq fz1_92_47 fz2_92_47
  · exact match_zero_fix ⟨93, by decide⟩ ⟨47, by decide⟩ p hp j hj hq fz1_93_47 fz2_93_47
  · exact match_zero_fix ⟨94, by decide⟩ ⟨47, by decide⟩ p hp j hj hq fz1_94_47 fz2_94_47
  · exact match_zero_fix ⟨95, by decide⟩ ⟨47, by decide⟩ p hp j hj hq fz1_95_47 fz2_95_47
  · exact match_zero_fix ⟨96, by decide⟩ ⟨47, by decide⟩ p hp j hj hq fz1_96_47 fz2_96_47
  · exact match_zero_fix ⟨97, by decide⟩ ⟨47, by decide⟩ p hp j hj hq fz1_97_47 fz2_97_47
  · exact match_zero_fix ⟨98, by decide⟩ ⟨47, by decide⟩ p hp j hj hq fz1_98_47 fz2_98_47
  · exact match_zero_fix ⟨99, by decide⟩ ⟨47, by decide⟩ p hp j hj hq fz1_99_47 fz2_99_47
  · exact match_zero_fix ⟨100, by decide⟩ ⟨47, by decide⟩ p hp j hj hq fz1_100_47 fz2_100_47
  · exact match_zero_fix ⟨101, by decide⟩ ⟨47, by decide⟩ p hp j hj hq fz1_101_47 fz2_101_47
  · exact match_zero_fix ⟨102, by decide⟩ ⟨47, by decide⟩ p hp j hj hq fz1_102_47 fz2_102_47
  · exact match_zero_fix ⟨103, by decide⟩ ⟨47, by decide⟩ p hp j hj hq fz1_103_47 fz2_103_47
  · exact match_zero_fix ⟨104, by decide⟩ ⟨47, by decide⟩ p hp j hj hq fz1_104_47 fz2_104_47
  · exact match_zero_fix ⟨105, by decide⟩ ⟨47, by decide⟩ p hp j hj hq fz1_105_47 fz2_105_47
  · exact match_zero_fix ⟨106, by decide⟩ ⟨47, by decide⟩ p hp j hj hq fz1_106_47 fz2_106_47
  · exact match_zero_fix ⟨107, by decide⟩ ⟨47, by decide⟩ p hp j hj hq fz1_107_47 fz2_107_47
  · exact match_zero_fix ⟨108, by decide⟩ ⟨47, by decide⟩ p hp j hj hq fz1_108_47 fz2_108_47
  · exact pair_109_47 p hp hrep j hj hq
  · exact match_zero_fix ⟨110, by decide⟩ ⟨47, by decide⟩ p hp j hj hq fz1_110_47 fz2_110_47
  · exact match_zero_fix ⟨111, by decide⟩ ⟨47, by decide⟩ p hp j hj hq fz1_111_47 fz2_111_47
  · exact match_zero_fix ⟨112, by decide⟩ ⟨47, by decide⟩ p hp j hj hq fz1_112_47 fz2_112_47
  · exact match_zero_fix ⟨113, by decide⟩ ⟨47, by decide⟩ p hp j hj hq fz1_113_47 fz2_113_47
  · exact match_zero_fix ⟨114, by decide⟩ ⟨47, by decide⟩ p hp j hj hq fz1_114_47 fz2_114_47
  · exact match_zero_fix ⟨115, by decide⟩ ⟨47, by decide⟩ p hp j hj hq fz1_115_47 fz2_115_47
  · exact match_zero_fix ⟨116, by decide⟩ ⟨47, by decide⟩ p hp j hj hq fz1_116_47 fz2_116_47
  · exact match_zero_fix ⟨117, by decide⟩ ⟨47, by decide⟩ p hp j hj hq fz1_117_47 fz2_117_47
  · exact match_zero_fix ⟨118, by decide⟩ ⟨47, by decide⟩ p hp j hj hq fz1_118_47 fz2_118_47
  · exact match_zero_fix ⟨119, by decide⟩ ⟨47, by decide⟩ p hp j hj hq fz1_119_47 fz2_119_47
  · exact pair_120_47 p hp hrep j hj hq
  · exact match_zero_fix ⟨121, by decide⟩ ⟨47, by decide⟩ p hp j hj hq fz1_121_47 fz2_121_47
  · exact match_zero_fix ⟨122, by decide⟩ ⟨47, by decide⟩ p hp j hj hq fz1_122_47 fz2_122_47
  · exact match_zero_fix ⟨123, by decide⟩ ⟨47, by decide⟩ p hp j hj hq fz1_123_47 fz2_123_47
  · exact pair_124_47 p hp hrep j hj hq
  · exact match_zero_fix ⟨125, by decide⟩ ⟨47, by decide⟩ p hp j hj hq fz1_125_47 fz2_125_47
  · exact match_zero_fix ⟨126, by decide⟩ ⟨47, by decide⟩ p hp j hj hq fz1_126_47 fz2_126_47
  · exact match_zero_fix ⟨127, by decide⟩ ⟨47, by decide⟩ p hp j hj hq fz1_127_47 fz2_127_47
  · exact pair_128_47 p hp hrep j hj hq
  · exact match_zero_fix ⟨129, by decide⟩ ⟨47, by decide⟩ p hp j hj hq fz1_129_47 fz2_129_47
  · exact match_zero_fix ⟨130, by decide⟩ ⟨47, by decide⟩ p hp j hj hq fz1_130_47 fz2_130_47
  · exact match_zero_fix ⟨131, by decide⟩ ⟨47, by decide⟩ p hp j hj hq fz1_131_47 fz2_131_47
  · exact pair_132_47 p hp hrep j hj hq
  · exact match_zero_fix ⟨133, by decide⟩ ⟨47, by decide⟩ p hp j hj hq fz1_133_47 fz2_133_47
  · exact match_zero_fix ⟨134, by decide⟩ ⟨47, by decide⟩ p hp j hj hq fz1_134_47 fz2_134_47
  · exact match_zero_fix ⟨135, by decide⟩ ⟨47, by decide⟩ p hp j hj hq fz1_135_47 fz2_135_47
  · exact pair_136_47 p hp hrep j hj hq
  · exact match_zero_fix ⟨137, by decide⟩ ⟨47, by decide⟩ p hp j hj hq fz1_137_47 fz2_137_47
  · exact match_zero_fix ⟨138, by decide⟩ ⟨47, by decide⟩ p hp j hj hq fz1_138_47 fz2_138_47
  · exact match_zero_fix ⟨139, by decide⟩ ⟨47, by decide⟩ p hp j hj hq fz1_139_47 fz2_139_47
  · exact match_zero_fix ⟨140, by decide⟩ ⟨47, by decide⟩ p hp j hj hq fz1_140_47 fz2_140_47
  · exact match_zero_fix ⟨141, by decide⟩ ⟨47, by decide⟩ p hp j hj hq fz1_141_47 fz2_141_47
  · exact match_zero_fix ⟨142, by decide⟩ ⟨47, by decide⟩ p hp j hj hq fz1_142_47 fz2_142_47
  · exact match_zero_fix ⟨143, by decide⟩ ⟨47, by decide⟩ p hp j hj hq fz1_143_47 fz2_143_47
  · exact match_zero_fix ⟨144, by decide⟩ ⟨47, by decide⟩ p hp j hj hq fz1_144_47 fz2_144_47
  · exact pair_145_47 p hp hrep j hj hq
  · exact match_zero_fix ⟨146, by decide⟩ ⟨47, by decide⟩ p hp j hj hq fz1_146_47 fz2_146_47
  · exact pair_147_47 p hp hrep j hj hq

end LeanDring.P5Presentation
