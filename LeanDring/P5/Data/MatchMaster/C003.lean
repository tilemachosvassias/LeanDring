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
import LeanDring.P5.Data.MatchPair.C006
import LeanDring.P5.Data.MatchPair.C007
import LeanDring.P5.Data.MatchPair.C008
import LeanDring.P5.Data.MatchPair.C009
import LeanDring.P5.Data.MatchPair.C010

/-! # Stage-5 per-column-class master theorems, chunk 2 (auto-emitted).  -/

namespace LeanDring.P5Presentation

open MulAction Finset LeanDring.DRing LeanDring.MonGSet

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.style.longLine false

theorem master_16 (p : Nat) (hp : p < (Q2.transData.getD 16 []).length)
    (hrep : (Q2.cosetIsRep.getD 16 []).getD p false = true)
    (rK : Fin 148) (j : Nat) (hj : j < (repChars.getD rK.val []).length)
    (hq : (normIsRep.getD rK.val []).getD j false = true) :
    species (Q2.reps (⟨16, by decide⟩ : Fin 148)) (colE2 ⟨16, by decide⟩ p hp)
        (rowE2 rK j hj hq)
      = species (reps (⟨16, by decide⟩ : Fin 148))
        (colE1 ⟨16, by decide⟩ p (transLenTr ⟨16, by decide⟩ p hp)) (rowE1 rK j hj) := by
  rcases rK with ⟨nK, hnK⟩; interval_cases nK
  · exact match_zero_len ⟨0, by decide⟩ ⟨16, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨1, by decide⟩ ⟨16, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨2, by decide⟩ ⟨16, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨3, by decide⟩ ⟨16, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨4, by decide⟩ ⟨16, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨5, by decide⟩ ⟨16, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨6, by decide⟩ ⟨16, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨7, by decide⟩ ⟨16, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨8, by decide⟩ ⟨16, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨9, by decide⟩ ⟨16, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨10, by decide⟩ ⟨16, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨11, by decide⟩ ⟨16, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨12, by decide⟩ ⟨16, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_fix ⟨13, by decide⟩ ⟨16, by decide⟩ p hp j hj hq fz1_13_16 fz2_13_16
  · exact match_zero_fix ⟨14, by decide⟩ ⟨16, by decide⟩ p hp j hj hq fz1_14_16 fz2_14_16
  · exact match_zero_fix ⟨15, by decide⟩ ⟨16, by decide⟩ p hp j hj hq fz1_15_16 fz2_15_16
  · exact pair_16_16 p hp hrep j hj hq
  · exact match_zero_fix ⟨17, by decide⟩ ⟨16, by decide⟩ p hp j hj hq fz1_17_16 fz2_17_16
  · exact match_zero_fix ⟨18, by decide⟩ ⟨16, by decide⟩ p hp j hj hq fz1_18_16 fz2_18_16
  · exact match_zero_fix ⟨19, by decide⟩ ⟨16, by decide⟩ p hp j hj hq fz1_19_16 fz2_19_16
  · exact match_zero_fix ⟨20, by decide⟩ ⟨16, by decide⟩ p hp j hj hq fz1_20_16 fz2_20_16
  · exact match_zero_fix ⟨21, by decide⟩ ⟨16, by decide⟩ p hp j hj hq fz1_21_16 fz2_21_16
  · exact match_zero_fix ⟨22, by decide⟩ ⟨16, by decide⟩ p hp j hj hq fz1_22_16 fz2_22_16
  · exact match_zero_fix ⟨23, by decide⟩ ⟨16, by decide⟩ p hp j hj hq fz1_23_16 fz2_23_16
  · exact match_zero_fix ⟨24, by decide⟩ ⟨16, by decide⟩ p hp j hj hq fz1_24_16 fz2_24_16
  · exact match_zero_fix ⟨25, by decide⟩ ⟨16, by decide⟩ p hp j hj hq fz1_25_16 fz2_25_16
  · exact match_zero_fix ⟨26, by decide⟩ ⟨16, by decide⟩ p hp j hj hq fz1_26_16 fz2_26_16
  · exact match_zero_fix ⟨27, by decide⟩ ⟨16, by decide⟩ p hp j hj hq fz1_27_16 fz2_27_16
  · exact match_zero_fix ⟨28, by decide⟩ ⟨16, by decide⟩ p hp j hj hq fz1_28_16 fz2_28_16
  · exact match_zero_fix ⟨29, by decide⟩ ⟨16, by decide⟩ p hp j hj hq fz1_29_16 fz2_29_16
  · exact match_zero_fix ⟨30, by decide⟩ ⟨16, by decide⟩ p hp j hj hq fz1_30_16 fz2_30_16
  · exact match_zero_fix ⟨31, by decide⟩ ⟨16, by decide⟩ p hp j hj hq fz1_31_16 fz2_31_16
  · exact match_zero_fix ⟨32, by decide⟩ ⟨16, by decide⟩ p hp j hj hq fz1_32_16 fz2_32_16
  · exact match_zero_fix ⟨33, by decide⟩ ⟨16, by decide⟩ p hp j hj hq fz1_33_16 fz2_33_16
  · exact match_zero_fix ⟨34, by decide⟩ ⟨16, by decide⟩ p hp j hj hq fz1_34_16 fz2_34_16
  · exact match_zero_fix ⟨35, by decide⟩ ⟨16, by decide⟩ p hp j hj hq fz1_35_16 fz2_35_16
  · exact match_zero_fix ⟨36, by decide⟩ ⟨16, by decide⟩ p hp j hj hq fz1_36_16 fz2_36_16
  · exact match_zero_fix ⟨37, by decide⟩ ⟨16, by decide⟩ p hp j hj hq fz1_37_16 fz2_37_16
  · exact match_zero_fix ⟨38, by decide⟩ ⟨16, by decide⟩ p hp j hj hq fz1_38_16 fz2_38_16
  · exact match_zero_fix ⟨39, by decide⟩ ⟨16, by decide⟩ p hp j hj hq fz1_39_16 fz2_39_16
  · exact match_zero_fix ⟨40, by decide⟩ ⟨16, by decide⟩ p hp j hj hq fz1_40_16 fz2_40_16
  · exact match_zero_fix ⟨41, by decide⟩ ⟨16, by decide⟩ p hp j hj hq fz1_41_16 fz2_41_16
  · exact match_zero_fix ⟨42, by decide⟩ ⟨16, by decide⟩ p hp j hj hq fz1_42_16 fz2_42_16
  · exact match_zero_fix ⟨43, by decide⟩ ⟨16, by decide⟩ p hp j hj hq fz1_43_16 fz2_43_16
  · exact match_zero_fix ⟨44, by decide⟩ ⟨16, by decide⟩ p hp j hj hq fz1_44_16 fz2_44_16
  · exact match_zero_fix ⟨45, by decide⟩ ⟨16, by decide⟩ p hp j hj hq fz1_45_16 fz2_45_16
  · exact match_zero_fix ⟨46, by decide⟩ ⟨16, by decide⟩ p hp j hj hq fz1_46_16 fz2_46_16
  · exact match_zero_fix ⟨47, by decide⟩ ⟨16, by decide⟩ p hp j hj hq fz1_47_16 fz2_47_16
  · exact match_zero_fix ⟨48, by decide⟩ ⟨16, by decide⟩ p hp j hj hq fz1_48_16 fz2_48_16
  · exact match_zero_fix ⟨49, by decide⟩ ⟨16, by decide⟩ p hp j hj hq fz1_49_16 fz2_49_16
  · exact match_zero_fix ⟨50, by decide⟩ ⟨16, by decide⟩ p hp j hj hq fz1_50_16 fz2_50_16
  · exact match_zero_fix ⟨51, by decide⟩ ⟨16, by decide⟩ p hp j hj hq fz1_51_16 fz2_51_16
  · exact match_zero_fix ⟨52, by decide⟩ ⟨16, by decide⟩ p hp j hj hq fz1_52_16 fz2_52_16
  · exact match_zero_fix ⟨53, by decide⟩ ⟨16, by decide⟩ p hp j hj hq fz1_53_16 fz2_53_16
  · exact match_zero_fix ⟨54, by decide⟩ ⟨16, by decide⟩ p hp j hj hq fz1_54_16 fz2_54_16
  · exact match_zero_fix ⟨55, by decide⟩ ⟨16, by decide⟩ p hp j hj hq fz1_55_16 fz2_55_16
  · exact match_zero_fix ⟨56, by decide⟩ ⟨16, by decide⟩ p hp j hj hq fz1_56_16 fz2_56_16
  · exact match_zero_fix ⟨57, by decide⟩ ⟨16, by decide⟩ p hp j hj hq fz1_57_16 fz2_57_16
  · exact match_zero_fix ⟨58, by decide⟩ ⟨16, by decide⟩ p hp j hj hq fz1_58_16 fz2_58_16
  · exact match_zero_fix ⟨59, by decide⟩ ⟨16, by decide⟩ p hp j hj hq fz1_59_16 fz2_59_16
  · exact match_zero_fix ⟨60, by decide⟩ ⟨16, by decide⟩ p hp j hj hq fz1_60_16 fz2_60_16
  · exact match_zero_fix ⟨61, by decide⟩ ⟨16, by decide⟩ p hp j hj hq fz1_61_16 fz2_61_16
  · exact match_zero_fix ⟨62, by decide⟩ ⟨16, by decide⟩ p hp j hj hq fz1_62_16 fz2_62_16
  · exact match_zero_fix ⟨63, by decide⟩ ⟨16, by decide⟩ p hp j hj hq fz1_63_16 fz2_63_16
  · exact match_zero_fix ⟨64, by decide⟩ ⟨16, by decide⟩ p hp j hj hq fz1_64_16 fz2_64_16
  · exact match_zero_fix ⟨65, by decide⟩ ⟨16, by decide⟩ p hp j hj hq fz1_65_16 fz2_65_16
  · exact match_zero_fix ⟨66, by decide⟩ ⟨16, by decide⟩ p hp j hj hq fz1_66_16 fz2_66_16
  · exact match_zero_fix ⟨67, by decide⟩ ⟨16, by decide⟩ p hp j hj hq fz1_67_16 fz2_67_16
  · exact match_zero_fix ⟨68, by decide⟩ ⟨16, by decide⟩ p hp j hj hq fz1_68_16 fz2_68_16
  · exact match_zero_fix ⟨69, by decide⟩ ⟨16, by decide⟩ p hp j hj hq fz1_69_16 fz2_69_16
  · exact match_zero_fix ⟨70, by decide⟩ ⟨16, by decide⟩ p hp j hj hq fz1_70_16 fz2_70_16
  · exact match_zero_fix ⟨71, by decide⟩ ⟨16, by decide⟩ p hp j hj hq fz1_71_16 fz2_71_16
  · exact match_zero_fix ⟨72, by decide⟩ ⟨16, by decide⟩ p hp j hj hq fz1_72_16 fz2_72_16
  · exact match_zero_fix ⟨73, by decide⟩ ⟨16, by decide⟩ p hp j hj hq fz1_73_16 fz2_73_16
  · exact match_zero_fix ⟨74, by decide⟩ ⟨16, by decide⟩ p hp j hj hq fz1_74_16 fz2_74_16
  · exact match_zero_fix ⟨75, by decide⟩ ⟨16, by decide⟩ p hp j hj hq fz1_75_16 fz2_75_16
  · exact match_zero_fix ⟨76, by decide⟩ ⟨16, by decide⟩ p hp j hj hq fz1_76_16 fz2_76_16
  · exact match_zero_fix ⟨77, by decide⟩ ⟨16, by decide⟩ p hp j hj hq fz1_77_16 fz2_77_16
  · exact match_zero_fix ⟨78, by decide⟩ ⟨16, by decide⟩ p hp j hj hq fz1_78_16 fz2_78_16
  · exact match_zero_fix ⟨79, by decide⟩ ⟨16, by decide⟩ p hp j hj hq fz1_79_16 fz2_79_16
  · exact match_zero_fix ⟨80, by decide⟩ ⟨16, by decide⟩ p hp j hj hq fz1_80_16 fz2_80_16
  · exact match_zero_fix ⟨81, by decide⟩ ⟨16, by decide⟩ p hp j hj hq fz1_81_16 fz2_81_16
  · exact match_zero_fix ⟨82, by decide⟩ ⟨16, by decide⟩ p hp j hj hq fz1_82_16 fz2_82_16
  · exact match_zero_fix ⟨83, by decide⟩ ⟨16, by decide⟩ p hp j hj hq fz1_83_16 fz2_83_16
  · exact match_zero_fix ⟨84, by decide⟩ ⟨16, by decide⟩ p hp j hj hq fz1_84_16 fz2_84_16
  · exact pair_85_16 p hp hrep j hj hq
  · exact match_zero_fix ⟨86, by decide⟩ ⟨16, by decide⟩ p hp j hj hq fz1_86_16 fz2_86_16
  · exact match_zero_fix ⟨87, by decide⟩ ⟨16, by decide⟩ p hp j hj hq fz1_87_16 fz2_87_16
  · exact match_zero_fix ⟨88, by decide⟩ ⟨16, by decide⟩ p hp j hj hq fz1_88_16 fz2_88_16
  · exact match_zero_fix ⟨89, by decide⟩ ⟨16, by decide⟩ p hp j hj hq fz1_89_16 fz2_89_16
  · exact match_zero_fix ⟨90, by decide⟩ ⟨16, by decide⟩ p hp j hj hq fz1_90_16 fz2_90_16
  · exact match_zero_fix ⟨91, by decide⟩ ⟨16, by decide⟩ p hp j hj hq fz1_91_16 fz2_91_16
  · exact match_zero_fix ⟨92, by decide⟩ ⟨16, by decide⟩ p hp j hj hq fz1_92_16 fz2_92_16
  · exact match_zero_fix ⟨93, by decide⟩ ⟨16, by decide⟩ p hp j hj hq fz1_93_16 fz2_93_16
  · exact match_zero_fix ⟨94, by decide⟩ ⟨16, by decide⟩ p hp j hj hq fz1_94_16 fz2_94_16
  · exact match_zero_fix ⟨95, by decide⟩ ⟨16, by decide⟩ p hp j hj hq fz1_95_16 fz2_95_16
  · exact match_zero_fix ⟨96, by decide⟩ ⟨16, by decide⟩ p hp j hj hq fz1_96_16 fz2_96_16
  · exact match_zero_fix ⟨97, by decide⟩ ⟨16, by decide⟩ p hp j hj hq fz1_97_16 fz2_97_16
  · exact match_zero_fix ⟨98, by decide⟩ ⟨16, by decide⟩ p hp j hj hq fz1_98_16 fz2_98_16
  · exact match_zero_fix ⟨99, by decide⟩ ⟨16, by decide⟩ p hp j hj hq fz1_99_16 fz2_99_16
  · exact match_zero_fix ⟨100, by decide⟩ ⟨16, by decide⟩ p hp j hj hq fz1_100_16 fz2_100_16
  · exact match_zero_fix ⟨101, by decide⟩ ⟨16, by decide⟩ p hp j hj hq fz1_101_16 fz2_101_16
  · exact match_zero_fix ⟨102, by decide⟩ ⟨16, by decide⟩ p hp j hj hq fz1_102_16 fz2_102_16
  · exact match_zero_fix ⟨103, by decide⟩ ⟨16, by decide⟩ p hp j hj hq fz1_103_16 fz2_103_16
  · exact match_zero_fix ⟨104, by decide⟩ ⟨16, by decide⟩ p hp j hj hq fz1_104_16 fz2_104_16
  · exact match_zero_fix ⟨105, by decide⟩ ⟨16, by decide⟩ p hp j hj hq fz1_105_16 fz2_105_16
  · exact match_zero_fix ⟨106, by decide⟩ ⟨16, by decide⟩ p hp j hj hq fz1_106_16 fz2_106_16
  · exact match_zero_fix ⟨107, by decide⟩ ⟨16, by decide⟩ p hp j hj hq fz1_107_16 fz2_107_16
  · exact match_zero_fix ⟨108, by decide⟩ ⟨16, by decide⟩ p hp j hj hq fz1_108_16 fz2_108_16
  · exact match_zero_fix ⟨109, by decide⟩ ⟨16, by decide⟩ p hp j hj hq fz1_109_16 fz2_109_16
  · exact match_zero_fix ⟨110, by decide⟩ ⟨16, by decide⟩ p hp j hj hq fz1_110_16 fz2_110_16
  · exact match_zero_fix ⟨111, by decide⟩ ⟨16, by decide⟩ p hp j hj hq fz1_111_16 fz2_111_16
  · exact match_zero_fix ⟨112, by decide⟩ ⟨16, by decide⟩ p hp j hj hq fz1_112_16 fz2_112_16
  · exact match_zero_fix ⟨113, by decide⟩ ⟨16, by decide⟩ p hp j hj hq fz1_113_16 fz2_113_16
  · exact match_zero_fix ⟨114, by decide⟩ ⟨16, by decide⟩ p hp j hj hq fz1_114_16 fz2_114_16
  · exact match_zero_fix ⟨115, by decide⟩ ⟨16, by decide⟩ p hp j hj hq fz1_115_16 fz2_115_16
  · exact match_zero_fix ⟨116, by decide⟩ ⟨16, by decide⟩ p hp j hj hq fz1_116_16 fz2_116_16
  · exact match_zero_fix ⟨117, by decide⟩ ⟨16, by decide⟩ p hp j hj hq fz1_117_16 fz2_117_16
  · exact match_zero_fix ⟨118, by decide⟩ ⟨16, by decide⟩ p hp j hj hq fz1_118_16 fz2_118_16
  · exact match_zero_fix ⟨119, by decide⟩ ⟨16, by decide⟩ p hp j hj hq fz1_119_16 fz2_119_16
  · exact match_zero_fix ⟨120, by decide⟩ ⟨16, by decide⟩ p hp j hj hq fz1_120_16 fz2_120_16
  · exact match_zero_fix ⟨121, by decide⟩ ⟨16, by decide⟩ p hp j hj hq fz1_121_16 fz2_121_16
  · exact match_zero_fix ⟨122, by decide⟩ ⟨16, by decide⟩ p hp j hj hq fz1_122_16 fz2_122_16
  · exact match_zero_fix ⟨123, by decide⟩ ⟨16, by decide⟩ p hp j hj hq fz1_123_16 fz2_123_16
  · exact match_zero_fix ⟨124, by decide⟩ ⟨16, by decide⟩ p hp j hj hq fz1_124_16 fz2_124_16
  · exact match_zero_fix ⟨125, by decide⟩ ⟨16, by decide⟩ p hp j hj hq fz1_125_16 fz2_125_16
  · exact match_zero_fix ⟨126, by decide⟩ ⟨16, by decide⟩ p hp j hj hq fz1_126_16 fz2_126_16
  · exact match_zero_fix ⟨127, by decide⟩ ⟨16, by decide⟩ p hp j hj hq fz1_127_16 fz2_127_16
  · exact match_zero_fix ⟨128, by decide⟩ ⟨16, by decide⟩ p hp j hj hq fz1_128_16 fz2_128_16
  · exact match_zero_fix ⟨129, by decide⟩ ⟨16, by decide⟩ p hp j hj hq fz1_129_16 fz2_129_16
  · exact match_zero_fix ⟨130, by decide⟩ ⟨16, by decide⟩ p hp j hj hq fz1_130_16 fz2_130_16
  · exact match_zero_fix ⟨131, by decide⟩ ⟨16, by decide⟩ p hp j hj hq fz1_131_16 fz2_131_16
  · exact match_zero_fix ⟨132, by decide⟩ ⟨16, by decide⟩ p hp j hj hq fz1_132_16 fz2_132_16
  · exact match_zero_fix ⟨133, by decide⟩ ⟨16, by decide⟩ p hp j hj hq fz1_133_16 fz2_133_16
  · exact match_zero_fix ⟨134, by decide⟩ ⟨16, by decide⟩ p hp j hj hq fz1_134_16 fz2_134_16
  · exact match_zero_fix ⟨135, by decide⟩ ⟨16, by decide⟩ p hp j hj hq fz1_135_16 fz2_135_16
  · exact match_zero_fix ⟨136, by decide⟩ ⟨16, by decide⟩ p hp j hj hq fz1_136_16 fz2_136_16
  · exact match_zero_fix ⟨137, by decide⟩ ⟨16, by decide⟩ p hp j hj hq fz1_137_16 fz2_137_16
  · exact match_zero_fix ⟨138, by decide⟩ ⟨16, by decide⟩ p hp j hj hq fz1_138_16 fz2_138_16
  · exact match_zero_fix ⟨139, by decide⟩ ⟨16, by decide⟩ p hp j hj hq fz1_139_16 fz2_139_16
  · exact match_zero_fix ⟨140, by decide⟩ ⟨16, by decide⟩ p hp j hj hq fz1_140_16 fz2_140_16
  · exact pair_141_16 p hp hrep j hj hq
  · exact match_zero_fix ⟨142, by decide⟩ ⟨16, by decide⟩ p hp j hj hq fz1_142_16 fz2_142_16
  · exact match_zero_fix ⟨143, by decide⟩ ⟨16, by decide⟩ p hp j hj hq fz1_143_16 fz2_143_16
  · exact match_zero_fix ⟨144, by decide⟩ ⟨16, by decide⟩ p hp j hj hq fz1_144_16 fz2_144_16
  · exact match_zero_fix ⟨145, by decide⟩ ⟨16, by decide⟩ p hp j hj hq fz1_145_16 fz2_145_16
  · exact match_zero_fix ⟨146, by decide⟩ ⟨16, by decide⟩ p hp j hj hq fz1_146_16 fz2_146_16
  · exact pair_147_16 p hp hrep j hj hq

theorem master_17 (p : Nat) (hp : p < (Q2.transData.getD 17 []).length)
    (hrep : (Q2.cosetIsRep.getD 17 []).getD p false = true)
    (rK : Fin 148) (j : Nat) (hj : j < (repChars.getD rK.val []).length)
    (hq : (normIsRep.getD rK.val []).getD j false = true) :
    species (Q2.reps (⟨17, by decide⟩ : Fin 148)) (colE2 ⟨17, by decide⟩ p hp)
        (rowE2 rK j hj hq)
      = species (reps (⟨17, by decide⟩ : Fin 148))
        (colE1 ⟨17, by decide⟩ p (transLenTr ⟨17, by decide⟩ p hp)) (rowE1 rK j hj) := by
  rcases rK with ⟨nK, hnK⟩; interval_cases nK
  · exact match_zero_len ⟨0, by decide⟩ ⟨17, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨1, by decide⟩ ⟨17, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨2, by decide⟩ ⟨17, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨3, by decide⟩ ⟨17, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨4, by decide⟩ ⟨17, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨5, by decide⟩ ⟨17, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨6, by decide⟩ ⟨17, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨7, by decide⟩ ⟨17, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨8, by decide⟩ ⟨17, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨9, by decide⟩ ⟨17, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨10, by decide⟩ ⟨17, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨11, by decide⟩ ⟨17, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨12, by decide⟩ ⟨17, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_fix ⟨13, by decide⟩ ⟨17, by decide⟩ p hp j hj hq fz1_13_17 fz2_13_17
  · exact match_zero_fix ⟨14, by decide⟩ ⟨17, by decide⟩ p hp j hj hq fz1_14_17 fz2_14_17
  · exact match_zero_fix ⟨15, by decide⟩ ⟨17, by decide⟩ p hp j hj hq fz1_15_17 fz2_15_17
  · exact match_zero_fix ⟨16, by decide⟩ ⟨17, by decide⟩ p hp j hj hq fz1_16_17 fz2_16_17
  · exact pair_17_17 p hp hrep j hj hq
  · exact match_zero_fix ⟨18, by decide⟩ ⟨17, by decide⟩ p hp j hj hq fz1_18_17 fz2_18_17
  · exact match_zero_fix ⟨19, by decide⟩ ⟨17, by decide⟩ p hp j hj hq fz1_19_17 fz2_19_17
  · exact match_zero_fix ⟨20, by decide⟩ ⟨17, by decide⟩ p hp j hj hq fz1_20_17 fz2_20_17
  · exact match_zero_fix ⟨21, by decide⟩ ⟨17, by decide⟩ p hp j hj hq fz1_21_17 fz2_21_17
  · exact match_zero_fix ⟨22, by decide⟩ ⟨17, by decide⟩ p hp j hj hq fz1_22_17 fz2_22_17
  · exact match_zero_fix ⟨23, by decide⟩ ⟨17, by decide⟩ p hp j hj hq fz1_23_17 fz2_23_17
  · exact match_zero_fix ⟨24, by decide⟩ ⟨17, by decide⟩ p hp j hj hq fz1_24_17 fz2_24_17
  · exact match_zero_fix ⟨25, by decide⟩ ⟨17, by decide⟩ p hp j hj hq fz1_25_17 fz2_25_17
  · exact match_zero_fix ⟨26, by decide⟩ ⟨17, by decide⟩ p hp j hj hq fz1_26_17 fz2_26_17
  · exact match_zero_fix ⟨27, by decide⟩ ⟨17, by decide⟩ p hp j hj hq fz1_27_17 fz2_27_17
  · exact match_zero_fix ⟨28, by decide⟩ ⟨17, by decide⟩ p hp j hj hq fz1_28_17 fz2_28_17
  · exact match_zero_fix ⟨29, by decide⟩ ⟨17, by decide⟩ p hp j hj hq fz1_29_17 fz2_29_17
  · exact match_zero_fix ⟨30, by decide⟩ ⟨17, by decide⟩ p hp j hj hq fz1_30_17 fz2_30_17
  · exact match_zero_fix ⟨31, by decide⟩ ⟨17, by decide⟩ p hp j hj hq fz1_31_17 fz2_31_17
  · exact match_zero_fix ⟨32, by decide⟩ ⟨17, by decide⟩ p hp j hj hq fz1_32_17 fz2_32_17
  · exact match_zero_fix ⟨33, by decide⟩ ⟨17, by decide⟩ p hp j hj hq fz1_33_17 fz2_33_17
  · exact match_zero_fix ⟨34, by decide⟩ ⟨17, by decide⟩ p hp j hj hq fz1_34_17 fz2_34_17
  · exact match_zero_fix ⟨35, by decide⟩ ⟨17, by decide⟩ p hp j hj hq fz1_35_17 fz2_35_17
  · exact match_zero_fix ⟨36, by decide⟩ ⟨17, by decide⟩ p hp j hj hq fz1_36_17 fz2_36_17
  · exact match_zero_fix ⟨37, by decide⟩ ⟨17, by decide⟩ p hp j hj hq fz1_37_17 fz2_37_17
  · exact match_zero_fix ⟨38, by decide⟩ ⟨17, by decide⟩ p hp j hj hq fz1_38_17 fz2_38_17
  · exact match_zero_fix ⟨39, by decide⟩ ⟨17, by decide⟩ p hp j hj hq fz1_39_17 fz2_39_17
  · exact match_zero_fix ⟨40, by decide⟩ ⟨17, by decide⟩ p hp j hj hq fz1_40_17 fz2_40_17
  · exact match_zero_fix ⟨41, by decide⟩ ⟨17, by decide⟩ p hp j hj hq fz1_41_17 fz2_41_17
  · exact match_zero_fix ⟨42, by decide⟩ ⟨17, by decide⟩ p hp j hj hq fz1_42_17 fz2_42_17
  · exact match_zero_fix ⟨43, by decide⟩ ⟨17, by decide⟩ p hp j hj hq fz1_43_17 fz2_43_17
  · exact match_zero_fix ⟨44, by decide⟩ ⟨17, by decide⟩ p hp j hj hq fz1_44_17 fz2_44_17
  · exact match_zero_fix ⟨45, by decide⟩ ⟨17, by decide⟩ p hp j hj hq fz1_45_17 fz2_45_17
  · exact match_zero_fix ⟨46, by decide⟩ ⟨17, by decide⟩ p hp j hj hq fz1_46_17 fz2_46_17
  · exact match_zero_fix ⟨47, by decide⟩ ⟨17, by decide⟩ p hp j hj hq fz1_47_17 fz2_47_17
  · exact match_zero_fix ⟨48, by decide⟩ ⟨17, by decide⟩ p hp j hj hq fz1_48_17 fz2_48_17
  · exact match_zero_fix ⟨49, by decide⟩ ⟨17, by decide⟩ p hp j hj hq fz1_49_17 fz2_49_17
  · exact match_zero_fix ⟨50, by decide⟩ ⟨17, by decide⟩ p hp j hj hq fz1_50_17 fz2_50_17
  · exact match_zero_fix ⟨51, by decide⟩ ⟨17, by decide⟩ p hp j hj hq fz1_51_17 fz2_51_17
  · exact match_zero_fix ⟨52, by decide⟩ ⟨17, by decide⟩ p hp j hj hq fz1_52_17 fz2_52_17
  · exact match_zero_fix ⟨53, by decide⟩ ⟨17, by decide⟩ p hp j hj hq fz1_53_17 fz2_53_17
  · exact match_zero_fix ⟨54, by decide⟩ ⟨17, by decide⟩ p hp j hj hq fz1_54_17 fz2_54_17
  · exact match_zero_fix ⟨55, by decide⟩ ⟨17, by decide⟩ p hp j hj hq fz1_55_17 fz2_55_17
  · exact match_zero_fix ⟨56, by decide⟩ ⟨17, by decide⟩ p hp j hj hq fz1_56_17 fz2_56_17
  · exact match_zero_fix ⟨57, by decide⟩ ⟨17, by decide⟩ p hp j hj hq fz1_57_17 fz2_57_17
  · exact match_zero_fix ⟨58, by decide⟩ ⟨17, by decide⟩ p hp j hj hq fz1_58_17 fz2_58_17
  · exact match_zero_fix ⟨59, by decide⟩ ⟨17, by decide⟩ p hp j hj hq fz1_59_17 fz2_59_17
  · exact match_zero_fix ⟨60, by decide⟩ ⟨17, by decide⟩ p hp j hj hq fz1_60_17 fz2_60_17
  · exact match_zero_fix ⟨61, by decide⟩ ⟨17, by decide⟩ p hp j hj hq fz1_61_17 fz2_61_17
  · exact match_zero_fix ⟨62, by decide⟩ ⟨17, by decide⟩ p hp j hj hq fz1_62_17 fz2_62_17
  · exact match_zero_fix ⟨63, by decide⟩ ⟨17, by decide⟩ p hp j hj hq fz1_63_17 fz2_63_17
  · exact match_zero_fix ⟨64, by decide⟩ ⟨17, by decide⟩ p hp j hj hq fz1_64_17 fz2_64_17
  · exact match_zero_fix ⟨65, by decide⟩ ⟨17, by decide⟩ p hp j hj hq fz1_65_17 fz2_65_17
  · exact match_zero_fix ⟨66, by decide⟩ ⟨17, by decide⟩ p hp j hj hq fz1_66_17 fz2_66_17
  · exact match_zero_fix ⟨67, by decide⟩ ⟨17, by decide⟩ p hp j hj hq fz1_67_17 fz2_67_17
  · exact match_zero_fix ⟨68, by decide⟩ ⟨17, by decide⟩ p hp j hj hq fz1_68_17 fz2_68_17
  · exact match_zero_fix ⟨69, by decide⟩ ⟨17, by decide⟩ p hp j hj hq fz1_69_17 fz2_69_17
  · exact match_zero_fix ⟨70, by decide⟩ ⟨17, by decide⟩ p hp j hj hq fz1_70_17 fz2_70_17
  · exact match_zero_fix ⟨71, by decide⟩ ⟨17, by decide⟩ p hp j hj hq fz1_71_17 fz2_71_17
  · exact match_zero_fix ⟨72, by decide⟩ ⟨17, by decide⟩ p hp j hj hq fz1_72_17 fz2_72_17
  · exact match_zero_fix ⟨73, by decide⟩ ⟨17, by decide⟩ p hp j hj hq fz1_73_17 fz2_73_17
  · exact match_zero_fix ⟨74, by decide⟩ ⟨17, by decide⟩ p hp j hj hq fz1_74_17 fz2_74_17
  · exact match_zero_fix ⟨75, by decide⟩ ⟨17, by decide⟩ p hp j hj hq fz1_75_17 fz2_75_17
  · exact match_zero_fix ⟨76, by decide⟩ ⟨17, by decide⟩ p hp j hj hq fz1_76_17 fz2_76_17
  · exact match_zero_fix ⟨77, by decide⟩ ⟨17, by decide⟩ p hp j hj hq fz1_77_17 fz2_77_17
  · exact match_zero_fix ⟨78, by decide⟩ ⟨17, by decide⟩ p hp j hj hq fz1_78_17 fz2_78_17
  · exact match_zero_fix ⟨79, by decide⟩ ⟨17, by decide⟩ p hp j hj hq fz1_79_17 fz2_79_17
  · exact match_zero_fix ⟨80, by decide⟩ ⟨17, by decide⟩ p hp j hj hq fz1_80_17 fz2_80_17
  · exact match_zero_fix ⟨81, by decide⟩ ⟨17, by decide⟩ p hp j hj hq fz1_81_17 fz2_81_17
  · exact match_zero_fix ⟨82, by decide⟩ ⟨17, by decide⟩ p hp j hj hq fz1_82_17 fz2_82_17
  · exact match_zero_fix ⟨83, by decide⟩ ⟨17, by decide⟩ p hp j hj hq fz1_83_17 fz2_83_17
  · exact match_zero_fix ⟨84, by decide⟩ ⟨17, by decide⟩ p hp j hj hq fz1_84_17 fz2_84_17
  · exact pair_85_17 p hp hrep j hj hq
  · exact match_zero_fix ⟨86, by decide⟩ ⟨17, by decide⟩ p hp j hj hq fz1_86_17 fz2_86_17
  · exact match_zero_fix ⟨87, by decide⟩ ⟨17, by decide⟩ p hp j hj hq fz1_87_17 fz2_87_17
  · exact match_zero_fix ⟨88, by decide⟩ ⟨17, by decide⟩ p hp j hj hq fz1_88_17 fz2_88_17
  · exact match_zero_fix ⟨89, by decide⟩ ⟨17, by decide⟩ p hp j hj hq fz1_89_17 fz2_89_17
  · exact match_zero_fix ⟨90, by decide⟩ ⟨17, by decide⟩ p hp j hj hq fz1_90_17 fz2_90_17
  · exact match_zero_fix ⟨91, by decide⟩ ⟨17, by decide⟩ p hp j hj hq fz1_91_17 fz2_91_17
  · exact match_zero_fix ⟨92, by decide⟩ ⟨17, by decide⟩ p hp j hj hq fz1_92_17 fz2_92_17
  · exact match_zero_fix ⟨93, by decide⟩ ⟨17, by decide⟩ p hp j hj hq fz1_93_17 fz2_93_17
  · exact match_zero_fix ⟨94, by decide⟩ ⟨17, by decide⟩ p hp j hj hq fz1_94_17 fz2_94_17
  · exact match_zero_fix ⟨95, by decide⟩ ⟨17, by decide⟩ p hp j hj hq fz1_95_17 fz2_95_17
  · exact match_zero_fix ⟨96, by decide⟩ ⟨17, by decide⟩ p hp j hj hq fz1_96_17 fz2_96_17
  · exact match_zero_fix ⟨97, by decide⟩ ⟨17, by decide⟩ p hp j hj hq fz1_97_17 fz2_97_17
  · exact match_zero_fix ⟨98, by decide⟩ ⟨17, by decide⟩ p hp j hj hq fz1_98_17 fz2_98_17
  · exact match_zero_fix ⟨99, by decide⟩ ⟨17, by decide⟩ p hp j hj hq fz1_99_17 fz2_99_17
  · exact match_zero_fix ⟨100, by decide⟩ ⟨17, by decide⟩ p hp j hj hq fz1_100_17 fz2_100_17
  · exact match_zero_fix ⟨101, by decide⟩ ⟨17, by decide⟩ p hp j hj hq fz1_101_17 fz2_101_17
  · exact match_zero_fix ⟨102, by decide⟩ ⟨17, by decide⟩ p hp j hj hq fz1_102_17 fz2_102_17
  · exact match_zero_fix ⟨103, by decide⟩ ⟨17, by decide⟩ p hp j hj hq fz1_103_17 fz2_103_17
  · exact match_zero_fix ⟨104, by decide⟩ ⟨17, by decide⟩ p hp j hj hq fz1_104_17 fz2_104_17
  · exact match_zero_fix ⟨105, by decide⟩ ⟨17, by decide⟩ p hp j hj hq fz1_105_17 fz2_105_17
  · exact match_zero_fix ⟨106, by decide⟩ ⟨17, by decide⟩ p hp j hj hq fz1_106_17 fz2_106_17
  · exact match_zero_fix ⟨107, by decide⟩ ⟨17, by decide⟩ p hp j hj hq fz1_107_17 fz2_107_17
  · exact match_zero_fix ⟨108, by decide⟩ ⟨17, by decide⟩ p hp j hj hq fz1_108_17 fz2_108_17
  · exact match_zero_fix ⟨109, by decide⟩ ⟨17, by decide⟩ p hp j hj hq fz1_109_17 fz2_109_17
  · exact match_zero_fix ⟨110, by decide⟩ ⟨17, by decide⟩ p hp j hj hq fz1_110_17 fz2_110_17
  · exact match_zero_fix ⟨111, by decide⟩ ⟨17, by decide⟩ p hp j hj hq fz1_111_17 fz2_111_17
  · exact match_zero_fix ⟨112, by decide⟩ ⟨17, by decide⟩ p hp j hj hq fz1_112_17 fz2_112_17
  · exact match_zero_fix ⟨113, by decide⟩ ⟨17, by decide⟩ p hp j hj hq fz1_113_17 fz2_113_17
  · exact match_zero_fix ⟨114, by decide⟩ ⟨17, by decide⟩ p hp j hj hq fz1_114_17 fz2_114_17
  · exact match_zero_fix ⟨115, by decide⟩ ⟨17, by decide⟩ p hp j hj hq fz1_115_17 fz2_115_17
  · exact match_zero_fix ⟨116, by decide⟩ ⟨17, by decide⟩ p hp j hj hq fz1_116_17 fz2_116_17
  · exact match_zero_fix ⟨117, by decide⟩ ⟨17, by decide⟩ p hp j hj hq fz1_117_17 fz2_117_17
  · exact match_zero_fix ⟨118, by decide⟩ ⟨17, by decide⟩ p hp j hj hq fz1_118_17 fz2_118_17
  · exact match_zero_fix ⟨119, by decide⟩ ⟨17, by decide⟩ p hp j hj hq fz1_119_17 fz2_119_17
  · exact match_zero_fix ⟨120, by decide⟩ ⟨17, by decide⟩ p hp j hj hq fz1_120_17 fz2_120_17
  · exact match_zero_fix ⟨121, by decide⟩ ⟨17, by decide⟩ p hp j hj hq fz1_121_17 fz2_121_17
  · exact match_zero_fix ⟨122, by decide⟩ ⟨17, by decide⟩ p hp j hj hq fz1_122_17 fz2_122_17
  · exact match_zero_fix ⟨123, by decide⟩ ⟨17, by decide⟩ p hp j hj hq fz1_123_17 fz2_123_17
  · exact match_zero_fix ⟨124, by decide⟩ ⟨17, by decide⟩ p hp j hj hq fz1_124_17 fz2_124_17
  · exact match_zero_fix ⟨125, by decide⟩ ⟨17, by decide⟩ p hp j hj hq fz1_125_17 fz2_125_17
  · exact match_zero_fix ⟨126, by decide⟩ ⟨17, by decide⟩ p hp j hj hq fz1_126_17 fz2_126_17
  · exact match_zero_fix ⟨127, by decide⟩ ⟨17, by decide⟩ p hp j hj hq fz1_127_17 fz2_127_17
  · exact match_zero_fix ⟨128, by decide⟩ ⟨17, by decide⟩ p hp j hj hq fz1_128_17 fz2_128_17
  · exact match_zero_fix ⟨129, by decide⟩ ⟨17, by decide⟩ p hp j hj hq fz1_129_17 fz2_129_17
  · exact match_zero_fix ⟨130, by decide⟩ ⟨17, by decide⟩ p hp j hj hq fz1_130_17 fz2_130_17
  · exact match_zero_fix ⟨131, by decide⟩ ⟨17, by decide⟩ p hp j hj hq fz1_131_17 fz2_131_17
  · exact match_zero_fix ⟨132, by decide⟩ ⟨17, by decide⟩ p hp j hj hq fz1_132_17 fz2_132_17
  · exact match_zero_fix ⟨133, by decide⟩ ⟨17, by decide⟩ p hp j hj hq fz1_133_17 fz2_133_17
  · exact match_zero_fix ⟨134, by decide⟩ ⟨17, by decide⟩ p hp j hj hq fz1_134_17 fz2_134_17
  · exact match_zero_fix ⟨135, by decide⟩ ⟨17, by decide⟩ p hp j hj hq fz1_135_17 fz2_135_17
  · exact match_zero_fix ⟨136, by decide⟩ ⟨17, by decide⟩ p hp j hj hq fz1_136_17 fz2_136_17
  · exact match_zero_fix ⟨137, by decide⟩ ⟨17, by decide⟩ p hp j hj hq fz1_137_17 fz2_137_17
  · exact match_zero_fix ⟨138, by decide⟩ ⟨17, by decide⟩ p hp j hj hq fz1_138_17 fz2_138_17
  · exact match_zero_fix ⟨139, by decide⟩ ⟨17, by decide⟩ p hp j hj hq fz1_139_17 fz2_139_17
  · exact match_zero_fix ⟨140, by decide⟩ ⟨17, by decide⟩ p hp j hj hq fz1_140_17 fz2_140_17
  · exact pair_141_17 p hp hrep j hj hq
  · exact match_zero_fix ⟨142, by decide⟩ ⟨17, by decide⟩ p hp j hj hq fz1_142_17 fz2_142_17
  · exact match_zero_fix ⟨143, by decide⟩ ⟨17, by decide⟩ p hp j hj hq fz1_143_17 fz2_143_17
  · exact match_zero_fix ⟨144, by decide⟩ ⟨17, by decide⟩ p hp j hj hq fz1_144_17 fz2_144_17
  · exact match_zero_fix ⟨145, by decide⟩ ⟨17, by decide⟩ p hp j hj hq fz1_145_17 fz2_145_17
  · exact match_zero_fix ⟨146, by decide⟩ ⟨17, by decide⟩ p hp j hj hq fz1_146_17 fz2_146_17
  · exact pair_147_17 p hp hrep j hj hq

theorem master_18 (p : Nat) (hp : p < (Q2.transData.getD 18 []).length)
    (hrep : (Q2.cosetIsRep.getD 18 []).getD p false = true)
    (rK : Fin 148) (j : Nat) (hj : j < (repChars.getD rK.val []).length)
    (hq : (normIsRep.getD rK.val []).getD j false = true) :
    species (Q2.reps (⟨18, by decide⟩ : Fin 148)) (colE2 ⟨18, by decide⟩ p hp)
        (rowE2 rK j hj hq)
      = species (reps (⟨18, by decide⟩ : Fin 148))
        (colE1 ⟨18, by decide⟩ p (transLenTr ⟨18, by decide⟩ p hp)) (rowE1 rK j hj) := by
  rcases rK with ⟨nK, hnK⟩; interval_cases nK
  · exact match_zero_len ⟨0, by decide⟩ ⟨18, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨1, by decide⟩ ⟨18, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨2, by decide⟩ ⟨18, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨3, by decide⟩ ⟨18, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨4, by decide⟩ ⟨18, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨5, by decide⟩ ⟨18, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨6, by decide⟩ ⟨18, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨7, by decide⟩ ⟨18, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨8, by decide⟩ ⟨18, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨9, by decide⟩ ⟨18, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨10, by decide⟩ ⟨18, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨11, by decide⟩ ⟨18, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨12, by decide⟩ ⟨18, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_fix ⟨13, by decide⟩ ⟨18, by decide⟩ p hp j hj hq fz1_13_18 fz2_13_18
  · exact match_zero_fix ⟨14, by decide⟩ ⟨18, by decide⟩ p hp j hj hq fz1_14_18 fz2_14_18
  · exact match_zero_fix ⟨15, by decide⟩ ⟨18, by decide⟩ p hp j hj hq fz1_15_18 fz2_15_18
  · exact match_zero_fix ⟨16, by decide⟩ ⟨18, by decide⟩ p hp j hj hq fz1_16_18 fz2_16_18
  · exact match_zero_fix ⟨17, by decide⟩ ⟨18, by decide⟩ p hp j hj hq fz1_17_18 fz2_17_18
  · exact pair_18_18 p hp hrep j hj hq
  · exact match_zero_fix ⟨19, by decide⟩ ⟨18, by decide⟩ p hp j hj hq fz1_19_18 fz2_19_18
  · exact match_zero_fix ⟨20, by decide⟩ ⟨18, by decide⟩ p hp j hj hq fz1_20_18 fz2_20_18
  · exact match_zero_fix ⟨21, by decide⟩ ⟨18, by decide⟩ p hp j hj hq fz1_21_18 fz2_21_18
  · exact match_zero_fix ⟨22, by decide⟩ ⟨18, by decide⟩ p hp j hj hq fz1_22_18 fz2_22_18
  · exact match_zero_fix ⟨23, by decide⟩ ⟨18, by decide⟩ p hp j hj hq fz1_23_18 fz2_23_18
  · exact match_zero_fix ⟨24, by decide⟩ ⟨18, by decide⟩ p hp j hj hq fz1_24_18 fz2_24_18
  · exact match_zero_fix ⟨25, by decide⟩ ⟨18, by decide⟩ p hp j hj hq fz1_25_18 fz2_25_18
  · exact match_zero_fix ⟨26, by decide⟩ ⟨18, by decide⟩ p hp j hj hq fz1_26_18 fz2_26_18
  · exact match_zero_fix ⟨27, by decide⟩ ⟨18, by decide⟩ p hp j hj hq fz1_27_18 fz2_27_18
  · exact match_zero_fix ⟨28, by decide⟩ ⟨18, by decide⟩ p hp j hj hq fz1_28_18 fz2_28_18
  · exact match_zero_fix ⟨29, by decide⟩ ⟨18, by decide⟩ p hp j hj hq fz1_29_18 fz2_29_18
  · exact match_zero_fix ⟨30, by decide⟩ ⟨18, by decide⟩ p hp j hj hq fz1_30_18 fz2_30_18
  · exact match_zero_fix ⟨31, by decide⟩ ⟨18, by decide⟩ p hp j hj hq fz1_31_18 fz2_31_18
  · exact match_zero_fix ⟨32, by decide⟩ ⟨18, by decide⟩ p hp j hj hq fz1_32_18 fz2_32_18
  · exact match_zero_fix ⟨33, by decide⟩ ⟨18, by decide⟩ p hp j hj hq fz1_33_18 fz2_33_18
  · exact match_zero_fix ⟨34, by decide⟩ ⟨18, by decide⟩ p hp j hj hq fz1_34_18 fz2_34_18
  · exact match_zero_fix ⟨35, by decide⟩ ⟨18, by decide⟩ p hp j hj hq fz1_35_18 fz2_35_18
  · exact match_zero_fix ⟨36, by decide⟩ ⟨18, by decide⟩ p hp j hj hq fz1_36_18 fz2_36_18
  · exact match_zero_fix ⟨37, by decide⟩ ⟨18, by decide⟩ p hp j hj hq fz1_37_18 fz2_37_18
  · exact match_zero_fix ⟨38, by decide⟩ ⟨18, by decide⟩ p hp j hj hq fz1_38_18 fz2_38_18
  · exact match_zero_fix ⟨39, by decide⟩ ⟨18, by decide⟩ p hp j hj hq fz1_39_18 fz2_39_18
  · exact match_zero_fix ⟨40, by decide⟩ ⟨18, by decide⟩ p hp j hj hq fz1_40_18 fz2_40_18
  · exact match_zero_fix ⟨41, by decide⟩ ⟨18, by decide⟩ p hp j hj hq fz1_41_18 fz2_41_18
  · exact match_zero_fix ⟨42, by decide⟩ ⟨18, by decide⟩ p hp j hj hq fz1_42_18 fz2_42_18
  · exact match_zero_fix ⟨43, by decide⟩ ⟨18, by decide⟩ p hp j hj hq fz1_43_18 fz2_43_18
  · exact match_zero_fix ⟨44, by decide⟩ ⟨18, by decide⟩ p hp j hj hq fz1_44_18 fz2_44_18
  · exact match_zero_fix ⟨45, by decide⟩ ⟨18, by decide⟩ p hp j hj hq fz1_45_18 fz2_45_18
  · exact match_zero_fix ⟨46, by decide⟩ ⟨18, by decide⟩ p hp j hj hq fz1_46_18 fz2_46_18
  · exact match_zero_fix ⟨47, by decide⟩ ⟨18, by decide⟩ p hp j hj hq fz1_47_18 fz2_47_18
  · exact match_zero_fix ⟨48, by decide⟩ ⟨18, by decide⟩ p hp j hj hq fz1_48_18 fz2_48_18
  · exact match_zero_fix ⟨49, by decide⟩ ⟨18, by decide⟩ p hp j hj hq fz1_49_18 fz2_49_18
  · exact match_zero_fix ⟨50, by decide⟩ ⟨18, by decide⟩ p hp j hj hq fz1_50_18 fz2_50_18
  · exact match_zero_fix ⟨51, by decide⟩ ⟨18, by decide⟩ p hp j hj hq fz1_51_18 fz2_51_18
  · exact match_zero_fix ⟨52, by decide⟩ ⟨18, by decide⟩ p hp j hj hq fz1_52_18 fz2_52_18
  · exact match_zero_fix ⟨53, by decide⟩ ⟨18, by decide⟩ p hp j hj hq fz1_53_18 fz2_53_18
  · exact match_zero_fix ⟨54, by decide⟩ ⟨18, by decide⟩ p hp j hj hq fz1_54_18 fz2_54_18
  · exact match_zero_fix ⟨55, by decide⟩ ⟨18, by decide⟩ p hp j hj hq fz1_55_18 fz2_55_18
  · exact match_zero_fix ⟨56, by decide⟩ ⟨18, by decide⟩ p hp j hj hq fz1_56_18 fz2_56_18
  · exact match_zero_fix ⟨57, by decide⟩ ⟨18, by decide⟩ p hp j hj hq fz1_57_18 fz2_57_18
  · exact match_zero_fix ⟨58, by decide⟩ ⟨18, by decide⟩ p hp j hj hq fz1_58_18 fz2_58_18
  · exact match_zero_fix ⟨59, by decide⟩ ⟨18, by decide⟩ p hp j hj hq fz1_59_18 fz2_59_18
  · exact match_zero_fix ⟨60, by decide⟩ ⟨18, by decide⟩ p hp j hj hq fz1_60_18 fz2_60_18
  · exact match_zero_fix ⟨61, by decide⟩ ⟨18, by decide⟩ p hp j hj hq fz1_61_18 fz2_61_18
  · exact match_zero_fix ⟨62, by decide⟩ ⟨18, by decide⟩ p hp j hj hq fz1_62_18 fz2_62_18
  · exact match_zero_fix ⟨63, by decide⟩ ⟨18, by decide⟩ p hp j hj hq fz1_63_18 fz2_63_18
  · exact match_zero_fix ⟨64, by decide⟩ ⟨18, by decide⟩ p hp j hj hq fz1_64_18 fz2_64_18
  · exact match_zero_fix ⟨65, by decide⟩ ⟨18, by decide⟩ p hp j hj hq fz1_65_18 fz2_65_18
  · exact match_zero_fix ⟨66, by decide⟩ ⟨18, by decide⟩ p hp j hj hq fz1_66_18 fz2_66_18
  · exact match_zero_fix ⟨67, by decide⟩ ⟨18, by decide⟩ p hp j hj hq fz1_67_18 fz2_67_18
  · exact match_zero_fix ⟨68, by decide⟩ ⟨18, by decide⟩ p hp j hj hq fz1_68_18 fz2_68_18
  · exact match_zero_fix ⟨69, by decide⟩ ⟨18, by decide⟩ p hp j hj hq fz1_69_18 fz2_69_18
  · exact match_zero_fix ⟨70, by decide⟩ ⟨18, by decide⟩ p hp j hj hq fz1_70_18 fz2_70_18
  · exact match_zero_fix ⟨71, by decide⟩ ⟨18, by decide⟩ p hp j hj hq fz1_71_18 fz2_71_18
  · exact match_zero_fix ⟨72, by decide⟩ ⟨18, by decide⟩ p hp j hj hq fz1_72_18 fz2_72_18
  · exact match_zero_fix ⟨73, by decide⟩ ⟨18, by decide⟩ p hp j hj hq fz1_73_18 fz2_73_18
  · exact match_zero_fix ⟨74, by decide⟩ ⟨18, by decide⟩ p hp j hj hq fz1_74_18 fz2_74_18
  · exact match_zero_fix ⟨75, by decide⟩ ⟨18, by decide⟩ p hp j hj hq fz1_75_18 fz2_75_18
  · exact match_zero_fix ⟨76, by decide⟩ ⟨18, by decide⟩ p hp j hj hq fz1_76_18 fz2_76_18
  · exact match_zero_fix ⟨77, by decide⟩ ⟨18, by decide⟩ p hp j hj hq fz1_77_18 fz2_77_18
  · exact match_zero_fix ⟨78, by decide⟩ ⟨18, by decide⟩ p hp j hj hq fz1_78_18 fz2_78_18
  · exact match_zero_fix ⟨79, by decide⟩ ⟨18, by decide⟩ p hp j hj hq fz1_79_18 fz2_79_18
  · exact match_zero_fix ⟨80, by decide⟩ ⟨18, by decide⟩ p hp j hj hq fz1_80_18 fz2_80_18
  · exact match_zero_fix ⟨81, by decide⟩ ⟨18, by decide⟩ p hp j hj hq fz1_81_18 fz2_81_18
  · exact match_zero_fix ⟨82, by decide⟩ ⟨18, by decide⟩ p hp j hj hq fz1_82_18 fz2_82_18
  · exact match_zero_fix ⟨83, by decide⟩ ⟨18, by decide⟩ p hp j hj hq fz1_83_18 fz2_83_18
  · exact match_zero_fix ⟨84, by decide⟩ ⟨18, by decide⟩ p hp j hj hq fz1_84_18 fz2_84_18
  · exact pair_85_18 p hp hrep j hj hq
  · exact match_zero_fix ⟨86, by decide⟩ ⟨18, by decide⟩ p hp j hj hq fz1_86_18 fz2_86_18
  · exact match_zero_fix ⟨87, by decide⟩ ⟨18, by decide⟩ p hp j hj hq fz1_87_18 fz2_87_18
  · exact match_zero_fix ⟨88, by decide⟩ ⟨18, by decide⟩ p hp j hj hq fz1_88_18 fz2_88_18
  · exact match_zero_fix ⟨89, by decide⟩ ⟨18, by decide⟩ p hp j hj hq fz1_89_18 fz2_89_18
  · exact match_zero_fix ⟨90, by decide⟩ ⟨18, by decide⟩ p hp j hj hq fz1_90_18 fz2_90_18
  · exact match_zero_fix ⟨91, by decide⟩ ⟨18, by decide⟩ p hp j hj hq fz1_91_18 fz2_91_18
  · exact match_zero_fix ⟨92, by decide⟩ ⟨18, by decide⟩ p hp j hj hq fz1_92_18 fz2_92_18
  · exact match_zero_fix ⟨93, by decide⟩ ⟨18, by decide⟩ p hp j hj hq fz1_93_18 fz2_93_18
  · exact match_zero_fix ⟨94, by decide⟩ ⟨18, by decide⟩ p hp j hj hq fz1_94_18 fz2_94_18
  · exact match_zero_fix ⟨95, by decide⟩ ⟨18, by decide⟩ p hp j hj hq fz1_95_18 fz2_95_18
  · exact match_zero_fix ⟨96, by decide⟩ ⟨18, by decide⟩ p hp j hj hq fz1_96_18 fz2_96_18
  · exact match_zero_fix ⟨97, by decide⟩ ⟨18, by decide⟩ p hp j hj hq fz1_97_18 fz2_97_18
  · exact match_zero_fix ⟨98, by decide⟩ ⟨18, by decide⟩ p hp j hj hq fz1_98_18 fz2_98_18
  · exact match_zero_fix ⟨99, by decide⟩ ⟨18, by decide⟩ p hp j hj hq fz1_99_18 fz2_99_18
  · exact match_zero_fix ⟨100, by decide⟩ ⟨18, by decide⟩ p hp j hj hq fz1_100_18 fz2_100_18
  · exact match_zero_fix ⟨101, by decide⟩ ⟨18, by decide⟩ p hp j hj hq fz1_101_18 fz2_101_18
  · exact match_zero_fix ⟨102, by decide⟩ ⟨18, by decide⟩ p hp j hj hq fz1_102_18 fz2_102_18
  · exact match_zero_fix ⟨103, by decide⟩ ⟨18, by decide⟩ p hp j hj hq fz1_103_18 fz2_103_18
  · exact match_zero_fix ⟨104, by decide⟩ ⟨18, by decide⟩ p hp j hj hq fz1_104_18 fz2_104_18
  · exact match_zero_fix ⟨105, by decide⟩ ⟨18, by decide⟩ p hp j hj hq fz1_105_18 fz2_105_18
  · exact match_zero_fix ⟨106, by decide⟩ ⟨18, by decide⟩ p hp j hj hq fz1_106_18 fz2_106_18
  · exact match_zero_fix ⟨107, by decide⟩ ⟨18, by decide⟩ p hp j hj hq fz1_107_18 fz2_107_18
  · exact match_zero_fix ⟨108, by decide⟩ ⟨18, by decide⟩ p hp j hj hq fz1_108_18 fz2_108_18
  · exact match_zero_fix ⟨109, by decide⟩ ⟨18, by decide⟩ p hp j hj hq fz1_109_18 fz2_109_18
  · exact match_zero_fix ⟨110, by decide⟩ ⟨18, by decide⟩ p hp j hj hq fz1_110_18 fz2_110_18
  · exact match_zero_fix ⟨111, by decide⟩ ⟨18, by decide⟩ p hp j hj hq fz1_111_18 fz2_111_18
  · exact match_zero_fix ⟨112, by decide⟩ ⟨18, by decide⟩ p hp j hj hq fz1_112_18 fz2_112_18
  · exact match_zero_fix ⟨113, by decide⟩ ⟨18, by decide⟩ p hp j hj hq fz1_113_18 fz2_113_18
  · exact match_zero_fix ⟨114, by decide⟩ ⟨18, by decide⟩ p hp j hj hq fz1_114_18 fz2_114_18
  · exact match_zero_fix ⟨115, by decide⟩ ⟨18, by decide⟩ p hp j hj hq fz1_115_18 fz2_115_18
  · exact match_zero_fix ⟨116, by decide⟩ ⟨18, by decide⟩ p hp j hj hq fz1_116_18 fz2_116_18
  · exact match_zero_fix ⟨117, by decide⟩ ⟨18, by decide⟩ p hp j hj hq fz1_117_18 fz2_117_18
  · exact match_zero_fix ⟨118, by decide⟩ ⟨18, by decide⟩ p hp j hj hq fz1_118_18 fz2_118_18
  · exact match_zero_fix ⟨119, by decide⟩ ⟨18, by decide⟩ p hp j hj hq fz1_119_18 fz2_119_18
  · exact match_zero_fix ⟨120, by decide⟩ ⟨18, by decide⟩ p hp j hj hq fz1_120_18 fz2_120_18
  · exact match_zero_fix ⟨121, by decide⟩ ⟨18, by decide⟩ p hp j hj hq fz1_121_18 fz2_121_18
  · exact match_zero_fix ⟨122, by decide⟩ ⟨18, by decide⟩ p hp j hj hq fz1_122_18 fz2_122_18
  · exact match_zero_fix ⟨123, by decide⟩ ⟨18, by decide⟩ p hp j hj hq fz1_123_18 fz2_123_18
  · exact match_zero_fix ⟨124, by decide⟩ ⟨18, by decide⟩ p hp j hj hq fz1_124_18 fz2_124_18
  · exact match_zero_fix ⟨125, by decide⟩ ⟨18, by decide⟩ p hp j hj hq fz1_125_18 fz2_125_18
  · exact match_zero_fix ⟨126, by decide⟩ ⟨18, by decide⟩ p hp j hj hq fz1_126_18 fz2_126_18
  · exact match_zero_fix ⟨127, by decide⟩ ⟨18, by decide⟩ p hp j hj hq fz1_127_18 fz2_127_18
  · exact match_zero_fix ⟨128, by decide⟩ ⟨18, by decide⟩ p hp j hj hq fz1_128_18 fz2_128_18
  · exact match_zero_fix ⟨129, by decide⟩ ⟨18, by decide⟩ p hp j hj hq fz1_129_18 fz2_129_18
  · exact match_zero_fix ⟨130, by decide⟩ ⟨18, by decide⟩ p hp j hj hq fz1_130_18 fz2_130_18
  · exact match_zero_fix ⟨131, by decide⟩ ⟨18, by decide⟩ p hp j hj hq fz1_131_18 fz2_131_18
  · exact match_zero_fix ⟨132, by decide⟩ ⟨18, by decide⟩ p hp j hj hq fz1_132_18 fz2_132_18
  · exact match_zero_fix ⟨133, by decide⟩ ⟨18, by decide⟩ p hp j hj hq fz1_133_18 fz2_133_18
  · exact match_zero_fix ⟨134, by decide⟩ ⟨18, by decide⟩ p hp j hj hq fz1_134_18 fz2_134_18
  · exact match_zero_fix ⟨135, by decide⟩ ⟨18, by decide⟩ p hp j hj hq fz1_135_18 fz2_135_18
  · exact match_zero_fix ⟨136, by decide⟩ ⟨18, by decide⟩ p hp j hj hq fz1_136_18 fz2_136_18
  · exact match_zero_fix ⟨137, by decide⟩ ⟨18, by decide⟩ p hp j hj hq fz1_137_18 fz2_137_18
  · exact match_zero_fix ⟨138, by decide⟩ ⟨18, by decide⟩ p hp j hj hq fz1_138_18 fz2_138_18
  · exact match_zero_fix ⟨139, by decide⟩ ⟨18, by decide⟩ p hp j hj hq fz1_139_18 fz2_139_18
  · exact match_zero_fix ⟨140, by decide⟩ ⟨18, by decide⟩ p hp j hj hq fz1_140_18 fz2_140_18
  · exact pair_141_18 p hp hrep j hj hq
  · exact match_zero_fix ⟨142, by decide⟩ ⟨18, by decide⟩ p hp j hj hq fz1_142_18 fz2_142_18
  · exact match_zero_fix ⟨143, by decide⟩ ⟨18, by decide⟩ p hp j hj hq fz1_143_18 fz2_143_18
  · exact match_zero_fix ⟨144, by decide⟩ ⟨18, by decide⟩ p hp j hj hq fz1_144_18 fz2_144_18
  · exact match_zero_fix ⟨145, by decide⟩ ⟨18, by decide⟩ p hp j hj hq fz1_145_18 fz2_145_18
  · exact match_zero_fix ⟨146, by decide⟩ ⟨18, by decide⟩ p hp j hj hq fz1_146_18 fz2_146_18
  · exact pair_147_18 p hp hrep j hj hq

theorem master_19 (p : Nat) (hp : p < (Q2.transData.getD 19 []).length)
    (hrep : (Q2.cosetIsRep.getD 19 []).getD p false = true)
    (rK : Fin 148) (j : Nat) (hj : j < (repChars.getD rK.val []).length)
    (hq : (normIsRep.getD rK.val []).getD j false = true) :
    species (Q2.reps (⟨19, by decide⟩ : Fin 148)) (colE2 ⟨19, by decide⟩ p hp)
        (rowE2 rK j hj hq)
      = species (reps (⟨19, by decide⟩ : Fin 148))
        (colE1 ⟨19, by decide⟩ p (transLenTr ⟨19, by decide⟩ p hp)) (rowE1 rK j hj) := by
  rcases rK with ⟨nK, hnK⟩; interval_cases nK
  · exact match_zero_len ⟨0, by decide⟩ ⟨19, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨1, by decide⟩ ⟨19, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨2, by decide⟩ ⟨19, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨3, by decide⟩ ⟨19, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨4, by decide⟩ ⟨19, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨5, by decide⟩ ⟨19, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨6, by decide⟩ ⟨19, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨7, by decide⟩ ⟨19, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨8, by decide⟩ ⟨19, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨9, by decide⟩ ⟨19, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨10, by decide⟩ ⟨19, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨11, by decide⟩ ⟨19, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨12, by decide⟩ ⟨19, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_fix ⟨13, by decide⟩ ⟨19, by decide⟩ p hp j hj hq fz1_13_19 fz2_13_19
  · exact match_zero_fix ⟨14, by decide⟩ ⟨19, by decide⟩ p hp j hj hq fz1_14_19 fz2_14_19
  · exact match_zero_fix ⟨15, by decide⟩ ⟨19, by decide⟩ p hp j hj hq fz1_15_19 fz2_15_19
  · exact match_zero_fix ⟨16, by decide⟩ ⟨19, by decide⟩ p hp j hj hq fz1_16_19 fz2_16_19
  · exact match_zero_fix ⟨17, by decide⟩ ⟨19, by decide⟩ p hp j hj hq fz1_17_19 fz2_17_19
  · exact match_zero_fix ⟨18, by decide⟩ ⟨19, by decide⟩ p hp j hj hq fz1_18_19 fz2_18_19
  · exact pair_19_19 p hp hrep j hj hq
  · exact match_zero_fix ⟨20, by decide⟩ ⟨19, by decide⟩ p hp j hj hq fz1_20_19 fz2_20_19
  · exact match_zero_fix ⟨21, by decide⟩ ⟨19, by decide⟩ p hp j hj hq fz1_21_19 fz2_21_19
  · exact match_zero_fix ⟨22, by decide⟩ ⟨19, by decide⟩ p hp j hj hq fz1_22_19 fz2_22_19
  · exact match_zero_fix ⟨23, by decide⟩ ⟨19, by decide⟩ p hp j hj hq fz1_23_19 fz2_23_19
  · exact match_zero_fix ⟨24, by decide⟩ ⟨19, by decide⟩ p hp j hj hq fz1_24_19 fz2_24_19
  · exact match_zero_fix ⟨25, by decide⟩ ⟨19, by decide⟩ p hp j hj hq fz1_25_19 fz2_25_19
  · exact match_zero_fix ⟨26, by decide⟩ ⟨19, by decide⟩ p hp j hj hq fz1_26_19 fz2_26_19
  · exact match_zero_fix ⟨27, by decide⟩ ⟨19, by decide⟩ p hp j hj hq fz1_27_19 fz2_27_19
  · exact match_zero_fix ⟨28, by decide⟩ ⟨19, by decide⟩ p hp j hj hq fz1_28_19 fz2_28_19
  · exact match_zero_fix ⟨29, by decide⟩ ⟨19, by decide⟩ p hp j hj hq fz1_29_19 fz2_29_19
  · exact match_zero_fix ⟨30, by decide⟩ ⟨19, by decide⟩ p hp j hj hq fz1_30_19 fz2_30_19
  · exact match_zero_fix ⟨31, by decide⟩ ⟨19, by decide⟩ p hp j hj hq fz1_31_19 fz2_31_19
  · exact match_zero_fix ⟨32, by decide⟩ ⟨19, by decide⟩ p hp j hj hq fz1_32_19 fz2_32_19
  · exact match_zero_fix ⟨33, by decide⟩ ⟨19, by decide⟩ p hp j hj hq fz1_33_19 fz2_33_19
  · exact match_zero_fix ⟨34, by decide⟩ ⟨19, by decide⟩ p hp j hj hq fz1_34_19 fz2_34_19
  · exact match_zero_fix ⟨35, by decide⟩ ⟨19, by decide⟩ p hp j hj hq fz1_35_19 fz2_35_19
  · exact match_zero_fix ⟨36, by decide⟩ ⟨19, by decide⟩ p hp j hj hq fz1_36_19 fz2_36_19
  · exact match_zero_fix ⟨37, by decide⟩ ⟨19, by decide⟩ p hp j hj hq fz1_37_19 fz2_37_19
  · exact match_zero_fix ⟨38, by decide⟩ ⟨19, by decide⟩ p hp j hj hq fz1_38_19 fz2_38_19
  · exact match_zero_fix ⟨39, by decide⟩ ⟨19, by decide⟩ p hp j hj hq fz1_39_19 fz2_39_19
  · exact match_zero_fix ⟨40, by decide⟩ ⟨19, by decide⟩ p hp j hj hq fz1_40_19 fz2_40_19
  · exact match_zero_fix ⟨41, by decide⟩ ⟨19, by decide⟩ p hp j hj hq fz1_41_19 fz2_41_19
  · exact match_zero_fix ⟨42, by decide⟩ ⟨19, by decide⟩ p hp j hj hq fz1_42_19 fz2_42_19
  · exact match_zero_fix ⟨43, by decide⟩ ⟨19, by decide⟩ p hp j hj hq fz1_43_19 fz2_43_19
  · exact match_zero_fix ⟨44, by decide⟩ ⟨19, by decide⟩ p hp j hj hq fz1_44_19 fz2_44_19
  · exact match_zero_fix ⟨45, by decide⟩ ⟨19, by decide⟩ p hp j hj hq fz1_45_19 fz2_45_19
  · exact match_zero_fix ⟨46, by decide⟩ ⟨19, by decide⟩ p hp j hj hq fz1_46_19 fz2_46_19
  · exact match_zero_fix ⟨47, by decide⟩ ⟨19, by decide⟩ p hp j hj hq fz1_47_19 fz2_47_19
  · exact match_zero_fix ⟨48, by decide⟩ ⟨19, by decide⟩ p hp j hj hq fz1_48_19 fz2_48_19
  · exact match_zero_fix ⟨49, by decide⟩ ⟨19, by decide⟩ p hp j hj hq fz1_49_19 fz2_49_19
  · exact match_zero_fix ⟨50, by decide⟩ ⟨19, by decide⟩ p hp j hj hq fz1_50_19 fz2_50_19
  · exact match_zero_fix ⟨51, by decide⟩ ⟨19, by decide⟩ p hp j hj hq fz1_51_19 fz2_51_19
  · exact match_zero_fix ⟨52, by decide⟩ ⟨19, by decide⟩ p hp j hj hq fz1_52_19 fz2_52_19
  · exact match_zero_fix ⟨53, by decide⟩ ⟨19, by decide⟩ p hp j hj hq fz1_53_19 fz2_53_19
  · exact match_zero_fix ⟨54, by decide⟩ ⟨19, by decide⟩ p hp j hj hq fz1_54_19 fz2_54_19
  · exact match_zero_fix ⟨55, by decide⟩ ⟨19, by decide⟩ p hp j hj hq fz1_55_19 fz2_55_19
  · exact pair_56_19 p hp hrep j hj hq
  · exact match_zero_fix ⟨57, by decide⟩ ⟨19, by decide⟩ p hp j hj hq fz1_57_19 fz2_57_19
  · exact match_zero_fix ⟨58, by decide⟩ ⟨19, by decide⟩ p hp j hj hq fz1_58_19 fz2_58_19
  · exact match_zero_fix ⟨59, by decide⟩ ⟨19, by decide⟩ p hp j hj hq fz1_59_19 fz2_59_19
  · exact match_zero_fix ⟨60, by decide⟩ ⟨19, by decide⟩ p hp j hj hq fz1_60_19 fz2_60_19
  · exact pair_61_19 p hp hrep j hj hq
  · exact match_zero_fix ⟨62, by decide⟩ ⟨19, by decide⟩ p hp j hj hq fz1_62_19 fz2_62_19
  · exact match_zero_fix ⟨63, by decide⟩ ⟨19, by decide⟩ p hp j hj hq fz1_63_19 fz2_63_19
  · exact match_zero_fix ⟨64, by decide⟩ ⟨19, by decide⟩ p hp j hj hq fz1_64_19 fz2_64_19
  · exact match_zero_fix ⟨65, by decide⟩ ⟨19, by decide⟩ p hp j hj hq fz1_65_19 fz2_65_19
  · exact pair_66_19 p hp hrep j hj hq
  · exact match_zero_fix ⟨67, by decide⟩ ⟨19, by decide⟩ p hp j hj hq fz1_67_19 fz2_67_19
  · exact match_zero_fix ⟨68, by decide⟩ ⟨19, by decide⟩ p hp j hj hq fz1_68_19 fz2_68_19
  · exact match_zero_fix ⟨69, by decide⟩ ⟨19, by decide⟩ p hp j hj hq fz1_69_19 fz2_69_19
  · exact match_zero_fix ⟨70, by decide⟩ ⟨19, by decide⟩ p hp j hj hq fz1_70_19 fz2_70_19
  · exact pair_71_19 p hp hrep j hj hq
  · exact match_zero_fix ⟨72, by decide⟩ ⟨19, by decide⟩ p hp j hj hq fz1_72_19 fz2_72_19
  · exact match_zero_fix ⟨73, by decide⟩ ⟨19, by decide⟩ p hp j hj hq fz1_73_19 fz2_73_19
  · exact match_zero_fix ⟨74, by decide⟩ ⟨19, by decide⟩ p hp j hj hq fz1_74_19 fz2_74_19
  · exact match_zero_fix ⟨75, by decide⟩ ⟨19, by decide⟩ p hp j hj hq fz1_75_19 fz2_75_19
  · exact pair_76_19 p hp hrep j hj hq
  · exact match_zero_fix ⟨77, by decide⟩ ⟨19, by decide⟩ p hp j hj hq fz1_77_19 fz2_77_19
  · exact match_zero_fix ⟨78, by decide⟩ ⟨19, by decide⟩ p hp j hj hq fz1_78_19 fz2_78_19
  · exact match_zero_fix ⟨79, by decide⟩ ⟨19, by decide⟩ p hp j hj hq fz1_79_19 fz2_79_19
  · exact pair_80_19 p hp hrep j hj hq
  · exact match_zero_fix ⟨81, by decide⟩ ⟨19, by decide⟩ p hp j hj hq fz1_81_19 fz2_81_19
  · exact match_zero_fix ⟨82, by decide⟩ ⟨19, by decide⟩ p hp j hj hq fz1_82_19 fz2_82_19
  · exact match_zero_fix ⟨83, by decide⟩ ⟨19, by decide⟩ p hp j hj hq fz1_83_19 fz2_83_19
  · exact match_zero_fix ⟨84, by decide⟩ ⟨19, by decide⟩ p hp j hj hq fz1_84_19 fz2_84_19
  · exact match_zero_fix ⟨85, by decide⟩ ⟨19, by decide⟩ p hp j hj hq fz1_85_19 fz2_85_19
  · exact pair_86_19 p hp hrep j hj hq
  · exact match_zero_fix ⟨87, by decide⟩ ⟨19, by decide⟩ p hp j hj hq fz1_87_19 fz2_87_19
  · exact match_zero_fix ⟨88, by decide⟩ ⟨19, by decide⟩ p hp j hj hq fz1_88_19 fz2_88_19
  · exact match_zero_fix ⟨89, by decide⟩ ⟨19, by decide⟩ p hp j hj hq fz1_89_19 fz2_89_19
  · exact match_zero_fix ⟨90, by decide⟩ ⟨19, by decide⟩ p hp j hj hq fz1_90_19 fz2_90_19
  · exact match_zero_fix ⟨91, by decide⟩ ⟨19, by decide⟩ p hp j hj hq fz1_91_19 fz2_91_19
  · exact match_zero_fix ⟨92, by decide⟩ ⟨19, by decide⟩ p hp j hj hq fz1_92_19 fz2_92_19
  · exact match_zero_fix ⟨93, by decide⟩ ⟨19, by decide⟩ p hp j hj hq fz1_93_19 fz2_93_19
  · exact match_zero_fix ⟨94, by decide⟩ ⟨19, by decide⟩ p hp j hj hq fz1_94_19 fz2_94_19
  · exact match_zero_fix ⟨95, by decide⟩ ⟨19, by decide⟩ p hp j hj hq fz1_95_19 fz2_95_19
  · exact match_zero_fix ⟨96, by decide⟩ ⟨19, by decide⟩ p hp j hj hq fz1_96_19 fz2_96_19
  · exact match_zero_fix ⟨97, by decide⟩ ⟨19, by decide⟩ p hp j hj hq fz1_97_19 fz2_97_19
  · exact match_zero_fix ⟨98, by decide⟩ ⟨19, by decide⟩ p hp j hj hq fz1_98_19 fz2_98_19
  · exact match_zero_fix ⟨99, by decide⟩ ⟨19, by decide⟩ p hp j hj hq fz1_99_19 fz2_99_19
  · exact match_zero_fix ⟨100, by decide⟩ ⟨19, by decide⟩ p hp j hj hq fz1_100_19 fz2_100_19
  · exact match_zero_fix ⟨101, by decide⟩ ⟨19, by decide⟩ p hp j hj hq fz1_101_19 fz2_101_19
  · exact match_zero_fix ⟨102, by decide⟩ ⟨19, by decide⟩ p hp j hj hq fz1_102_19 fz2_102_19
  · exact match_zero_fix ⟨103, by decide⟩ ⟨19, by decide⟩ p hp j hj hq fz1_103_19 fz2_103_19
  · exact match_zero_fix ⟨104, by decide⟩ ⟨19, by decide⟩ p hp j hj hq fz1_104_19 fz2_104_19
  · exact match_zero_fix ⟨105, by decide⟩ ⟨19, by decide⟩ p hp j hj hq fz1_105_19 fz2_105_19
  · exact match_zero_fix ⟨106, by decide⟩ ⟨19, by decide⟩ p hp j hj hq fz1_106_19 fz2_106_19
  · exact match_zero_fix ⟨107, by decide⟩ ⟨19, by decide⟩ p hp j hj hq fz1_107_19 fz2_107_19
  · exact match_zero_fix ⟨108, by decide⟩ ⟨19, by decide⟩ p hp j hj hq fz1_108_19 fz2_108_19
  · exact match_zero_fix ⟨109, by decide⟩ ⟨19, by decide⟩ p hp j hj hq fz1_109_19 fz2_109_19
  · exact match_zero_fix ⟨110, by decide⟩ ⟨19, by decide⟩ p hp j hj hq fz1_110_19 fz2_110_19
  · exact match_zero_fix ⟨111, by decide⟩ ⟨19, by decide⟩ p hp j hj hq fz1_111_19 fz2_111_19
  · exact match_zero_fix ⟨112, by decide⟩ ⟨19, by decide⟩ p hp j hj hq fz1_112_19 fz2_112_19
  · exact match_zero_fix ⟨113, by decide⟩ ⟨19, by decide⟩ p hp j hj hq fz1_113_19 fz2_113_19
  · exact match_zero_fix ⟨114, by decide⟩ ⟨19, by decide⟩ p hp j hj hq fz1_114_19 fz2_114_19
  · exact match_zero_fix ⟨115, by decide⟩ ⟨19, by decide⟩ p hp j hj hq fz1_115_19 fz2_115_19
  · exact pair_116_19 p hp hrep j hj hq
  · exact pair_117_19 p hp hrep j hj hq
  · exact pair_118_19 p hp hrep j hj hq
  · exact pair_119_19 p hp hrep j hj hq
  · exact pair_120_19 p hp hrep j hj hq
  · exact match_zero_fix ⟨121, by decide⟩ ⟨19, by decide⟩ p hp j hj hq fz1_121_19 fz2_121_19
  · exact match_zero_fix ⟨122, by decide⟩ ⟨19, by decide⟩ p hp j hj hq fz1_122_19 fz2_122_19
  · exact match_zero_fix ⟨123, by decide⟩ ⟨19, by decide⟩ p hp j hj hq fz1_123_19 fz2_123_19
  · exact match_zero_fix ⟨124, by decide⟩ ⟨19, by decide⟩ p hp j hj hq fz1_124_19 fz2_124_19
  · exact match_zero_fix ⟨125, by decide⟩ ⟨19, by decide⟩ p hp j hj hq fz1_125_19 fz2_125_19
  · exact match_zero_fix ⟨126, by decide⟩ ⟨19, by decide⟩ p hp j hj hq fz1_126_19 fz2_126_19
  · exact match_zero_fix ⟨127, by decide⟩ ⟨19, by decide⟩ p hp j hj hq fz1_127_19 fz2_127_19
  · exact match_zero_fix ⟨128, by decide⟩ ⟨19, by decide⟩ p hp j hj hq fz1_128_19 fz2_128_19
  · exact match_zero_fix ⟨129, by decide⟩ ⟨19, by decide⟩ p hp j hj hq fz1_129_19 fz2_129_19
  · exact match_zero_fix ⟨130, by decide⟩ ⟨19, by decide⟩ p hp j hj hq fz1_130_19 fz2_130_19
  · exact match_zero_fix ⟨131, by decide⟩ ⟨19, by decide⟩ p hp j hj hq fz1_131_19 fz2_131_19
  · exact match_zero_fix ⟨132, by decide⟩ ⟨19, by decide⟩ p hp j hj hq fz1_132_19 fz2_132_19
  · exact match_zero_fix ⟨133, by decide⟩ ⟨19, by decide⟩ p hp j hj hq fz1_133_19 fz2_133_19
  · exact match_zero_fix ⟨134, by decide⟩ ⟨19, by decide⟩ p hp j hj hq fz1_134_19 fz2_134_19
  · exact match_zero_fix ⟨135, by decide⟩ ⟨19, by decide⟩ p hp j hj hq fz1_135_19 fz2_135_19
  · exact match_zero_fix ⟨136, by decide⟩ ⟨19, by decide⟩ p hp j hj hq fz1_136_19 fz2_136_19
  · exact match_zero_fix ⟨137, by decide⟩ ⟨19, by decide⟩ p hp j hj hq fz1_137_19 fz2_137_19
  · exact match_zero_fix ⟨138, by decide⟩ ⟨19, by decide⟩ p hp j hj hq fz1_138_19 fz2_138_19
  · exact match_zero_fix ⟨139, by decide⟩ ⟨19, by decide⟩ p hp j hj hq fz1_139_19 fz2_139_19
  · exact match_zero_fix ⟨140, by decide⟩ ⟨19, by decide⟩ p hp j hj hq fz1_140_19 fz2_140_19
  · exact pair_141_19 p hp hrep j hj hq
  · exact match_zero_fix ⟨142, by decide⟩ ⟨19, by decide⟩ p hp j hj hq fz1_142_19 fz2_142_19
  · exact match_zero_fix ⟨143, by decide⟩ ⟨19, by decide⟩ p hp j hj hq fz1_143_19 fz2_143_19
  · exact match_zero_fix ⟨144, by decide⟩ ⟨19, by decide⟩ p hp j hj hq fz1_144_19 fz2_144_19
  · exact match_zero_fix ⟨145, by decide⟩ ⟨19, by decide⟩ p hp j hj hq fz1_145_19 fz2_145_19
  · exact match_zero_fix ⟨146, by decide⟩ ⟨19, by decide⟩ p hp j hj hq fz1_146_19 fz2_146_19
  · exact pair_147_19 p hp hrep j hj hq

theorem master_20 (p : Nat) (hp : p < (Q2.transData.getD 20 []).length)
    (hrep : (Q2.cosetIsRep.getD 20 []).getD p false = true)
    (rK : Fin 148) (j : Nat) (hj : j < (repChars.getD rK.val []).length)
    (hq : (normIsRep.getD rK.val []).getD j false = true) :
    species (Q2.reps (⟨20, by decide⟩ : Fin 148)) (colE2 ⟨20, by decide⟩ p hp)
        (rowE2 rK j hj hq)
      = species (reps (⟨20, by decide⟩ : Fin 148))
        (colE1 ⟨20, by decide⟩ p (transLenTr ⟨20, by decide⟩ p hp)) (rowE1 rK j hj) := by
  rcases rK with ⟨nK, hnK⟩; interval_cases nK
  · exact match_zero_len ⟨0, by decide⟩ ⟨20, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨1, by decide⟩ ⟨20, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨2, by decide⟩ ⟨20, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨3, by decide⟩ ⟨20, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨4, by decide⟩ ⟨20, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨5, by decide⟩ ⟨20, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨6, by decide⟩ ⟨20, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨7, by decide⟩ ⟨20, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨8, by decide⟩ ⟨20, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨9, by decide⟩ ⟨20, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨10, by decide⟩ ⟨20, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨11, by decide⟩ ⟨20, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨12, by decide⟩ ⟨20, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_fix ⟨13, by decide⟩ ⟨20, by decide⟩ p hp j hj hq fz1_13_20 fz2_13_20
  · exact match_zero_fix ⟨14, by decide⟩ ⟨20, by decide⟩ p hp j hj hq fz1_14_20 fz2_14_20
  · exact match_zero_fix ⟨15, by decide⟩ ⟨20, by decide⟩ p hp j hj hq fz1_15_20 fz2_15_20
  · exact match_zero_fix ⟨16, by decide⟩ ⟨20, by decide⟩ p hp j hj hq fz1_16_20 fz2_16_20
  · exact match_zero_fix ⟨17, by decide⟩ ⟨20, by decide⟩ p hp j hj hq fz1_17_20 fz2_17_20
  · exact match_zero_fix ⟨18, by decide⟩ ⟨20, by decide⟩ p hp j hj hq fz1_18_20 fz2_18_20
  · exact match_zero_fix ⟨19, by decide⟩ ⟨20, by decide⟩ p hp j hj hq fz1_19_20 fz2_19_20
  · exact pair_20_20 p hp hrep j hj hq
  · exact match_zero_fix ⟨21, by decide⟩ ⟨20, by decide⟩ p hp j hj hq fz1_21_20 fz2_21_20
  · exact match_zero_fix ⟨22, by decide⟩ ⟨20, by decide⟩ p hp j hj hq fz1_22_20 fz2_22_20
  · exact match_zero_fix ⟨23, by decide⟩ ⟨20, by decide⟩ p hp j hj hq fz1_23_20 fz2_23_20
  · exact match_zero_fix ⟨24, by decide⟩ ⟨20, by decide⟩ p hp j hj hq fz1_24_20 fz2_24_20
  · exact match_zero_fix ⟨25, by decide⟩ ⟨20, by decide⟩ p hp j hj hq fz1_25_20 fz2_25_20
  · exact match_zero_fix ⟨26, by decide⟩ ⟨20, by decide⟩ p hp j hj hq fz1_26_20 fz2_26_20
  · exact match_zero_fix ⟨27, by decide⟩ ⟨20, by decide⟩ p hp j hj hq fz1_27_20 fz2_27_20
  · exact match_zero_fix ⟨28, by decide⟩ ⟨20, by decide⟩ p hp j hj hq fz1_28_20 fz2_28_20
  · exact match_zero_fix ⟨29, by decide⟩ ⟨20, by decide⟩ p hp j hj hq fz1_29_20 fz2_29_20
  · exact match_zero_fix ⟨30, by decide⟩ ⟨20, by decide⟩ p hp j hj hq fz1_30_20 fz2_30_20
  · exact match_zero_fix ⟨31, by decide⟩ ⟨20, by decide⟩ p hp j hj hq fz1_31_20 fz2_31_20
  · exact match_zero_fix ⟨32, by decide⟩ ⟨20, by decide⟩ p hp j hj hq fz1_32_20 fz2_32_20
  · exact match_zero_fix ⟨33, by decide⟩ ⟨20, by decide⟩ p hp j hj hq fz1_33_20 fz2_33_20
  · exact match_zero_fix ⟨34, by decide⟩ ⟨20, by decide⟩ p hp j hj hq fz1_34_20 fz2_34_20
  · exact match_zero_fix ⟨35, by decide⟩ ⟨20, by decide⟩ p hp j hj hq fz1_35_20 fz2_35_20
  · exact match_zero_fix ⟨36, by decide⟩ ⟨20, by decide⟩ p hp j hj hq fz1_36_20 fz2_36_20
  · exact match_zero_fix ⟨37, by decide⟩ ⟨20, by decide⟩ p hp j hj hq fz1_37_20 fz2_37_20
  · exact match_zero_fix ⟨38, by decide⟩ ⟨20, by decide⟩ p hp j hj hq fz1_38_20 fz2_38_20
  · exact match_zero_fix ⟨39, by decide⟩ ⟨20, by decide⟩ p hp j hj hq fz1_39_20 fz2_39_20
  · exact match_zero_fix ⟨40, by decide⟩ ⟨20, by decide⟩ p hp j hj hq fz1_40_20 fz2_40_20
  · exact match_zero_fix ⟨41, by decide⟩ ⟨20, by decide⟩ p hp j hj hq fz1_41_20 fz2_41_20
  · exact match_zero_fix ⟨42, by decide⟩ ⟨20, by decide⟩ p hp j hj hq fz1_42_20 fz2_42_20
  · exact match_zero_fix ⟨43, by decide⟩ ⟨20, by decide⟩ p hp j hj hq fz1_43_20 fz2_43_20
  · exact match_zero_fix ⟨44, by decide⟩ ⟨20, by decide⟩ p hp j hj hq fz1_44_20 fz2_44_20
  · exact match_zero_fix ⟨45, by decide⟩ ⟨20, by decide⟩ p hp j hj hq fz1_45_20 fz2_45_20
  · exact match_zero_fix ⟨46, by decide⟩ ⟨20, by decide⟩ p hp j hj hq fz1_46_20 fz2_46_20
  · exact match_zero_fix ⟨47, by decide⟩ ⟨20, by decide⟩ p hp j hj hq fz1_47_20 fz2_47_20
  · exact match_zero_fix ⟨48, by decide⟩ ⟨20, by decide⟩ p hp j hj hq fz1_48_20 fz2_48_20
  · exact match_zero_fix ⟨49, by decide⟩ ⟨20, by decide⟩ p hp j hj hq fz1_49_20 fz2_49_20
  · exact match_zero_fix ⟨50, by decide⟩ ⟨20, by decide⟩ p hp j hj hq fz1_50_20 fz2_50_20
  · exact match_zero_fix ⟨51, by decide⟩ ⟨20, by decide⟩ p hp j hj hq fz1_51_20 fz2_51_20
  · exact match_zero_fix ⟨52, by decide⟩ ⟨20, by decide⟩ p hp j hj hq fz1_52_20 fz2_52_20
  · exact match_zero_fix ⟨53, by decide⟩ ⟨20, by decide⟩ p hp j hj hq fz1_53_20 fz2_53_20
  · exact match_zero_fix ⟨54, by decide⟩ ⟨20, by decide⟩ p hp j hj hq fz1_54_20 fz2_54_20
  · exact match_zero_fix ⟨55, by decide⟩ ⟨20, by decide⟩ p hp j hj hq fz1_55_20 fz2_55_20
  · exact match_zero_fix ⟨56, by decide⟩ ⟨20, by decide⟩ p hp j hj hq fz1_56_20 fz2_56_20
  · exact match_zero_fix ⟨57, by decide⟩ ⟨20, by decide⟩ p hp j hj hq fz1_57_20 fz2_57_20
  · exact match_zero_fix ⟨58, by decide⟩ ⟨20, by decide⟩ p hp j hj hq fz1_58_20 fz2_58_20
  · exact match_zero_fix ⟨59, by decide⟩ ⟨20, by decide⟩ p hp j hj hq fz1_59_20 fz2_59_20
  · exact match_zero_fix ⟨60, by decide⟩ ⟨20, by decide⟩ p hp j hj hq fz1_60_20 fz2_60_20
  · exact match_zero_fix ⟨61, by decide⟩ ⟨20, by decide⟩ p hp j hj hq fz1_61_20 fz2_61_20
  · exact match_zero_fix ⟨62, by decide⟩ ⟨20, by decide⟩ p hp j hj hq fz1_62_20 fz2_62_20
  · exact match_zero_fix ⟨63, by decide⟩ ⟨20, by decide⟩ p hp j hj hq fz1_63_20 fz2_63_20
  · exact match_zero_fix ⟨64, by decide⟩ ⟨20, by decide⟩ p hp j hj hq fz1_64_20 fz2_64_20
  · exact match_zero_fix ⟨65, by decide⟩ ⟨20, by decide⟩ p hp j hj hq fz1_65_20 fz2_65_20
  · exact match_zero_fix ⟨66, by decide⟩ ⟨20, by decide⟩ p hp j hj hq fz1_66_20 fz2_66_20
  · exact match_zero_fix ⟨67, by decide⟩ ⟨20, by decide⟩ p hp j hj hq fz1_67_20 fz2_67_20
  · exact match_zero_fix ⟨68, by decide⟩ ⟨20, by decide⟩ p hp j hj hq fz1_68_20 fz2_68_20
  · exact match_zero_fix ⟨69, by decide⟩ ⟨20, by decide⟩ p hp j hj hq fz1_69_20 fz2_69_20
  · exact match_zero_fix ⟨70, by decide⟩ ⟨20, by decide⟩ p hp j hj hq fz1_70_20 fz2_70_20
  · exact match_zero_fix ⟨71, by decide⟩ ⟨20, by decide⟩ p hp j hj hq fz1_71_20 fz2_71_20
  · exact match_zero_fix ⟨72, by decide⟩ ⟨20, by decide⟩ p hp j hj hq fz1_72_20 fz2_72_20
  · exact match_zero_fix ⟨73, by decide⟩ ⟨20, by decide⟩ p hp j hj hq fz1_73_20 fz2_73_20
  · exact match_zero_fix ⟨74, by decide⟩ ⟨20, by decide⟩ p hp j hj hq fz1_74_20 fz2_74_20
  · exact match_zero_fix ⟨75, by decide⟩ ⟨20, by decide⟩ p hp j hj hq fz1_75_20 fz2_75_20
  · exact match_zero_fix ⟨76, by decide⟩ ⟨20, by decide⟩ p hp j hj hq fz1_76_20 fz2_76_20
  · exact match_zero_fix ⟨77, by decide⟩ ⟨20, by decide⟩ p hp j hj hq fz1_77_20 fz2_77_20
  · exact match_zero_fix ⟨78, by decide⟩ ⟨20, by decide⟩ p hp j hj hq fz1_78_20 fz2_78_20
  · exact match_zero_fix ⟨79, by decide⟩ ⟨20, by decide⟩ p hp j hj hq fz1_79_20 fz2_79_20
  · exact match_zero_fix ⟨80, by decide⟩ ⟨20, by decide⟩ p hp j hj hq fz1_80_20 fz2_80_20
  · exact pair_81_20 p hp hrep j hj hq
  · exact match_zero_fix ⟨82, by decide⟩ ⟨20, by decide⟩ p hp j hj hq fz1_82_20 fz2_82_20
  · exact match_zero_fix ⟨83, by decide⟩ ⟨20, by decide⟩ p hp j hj hq fz1_83_20 fz2_83_20
  · exact match_zero_fix ⟨84, by decide⟩ ⟨20, by decide⟩ p hp j hj hq fz1_84_20 fz2_84_20
  · exact pair_85_20 p hp hrep j hj hq
  · exact pair_86_20 p hp hrep j hj hq
  · exact pair_87_20 p hp hrep j hj hq
  · exact pair_88_20 p hp hrep j hj hq
  · exact pair_89_20 p hp hrep j hj hq
  · exact match_zero_fix ⟨90, by decide⟩ ⟨20, by decide⟩ p hp j hj hq fz1_90_20 fz2_90_20
  · exact match_zero_fix ⟨91, by decide⟩ ⟨20, by decide⟩ p hp j hj hq fz1_91_20 fz2_91_20
  · exact match_zero_fix ⟨92, by decide⟩ ⟨20, by decide⟩ p hp j hj hq fz1_92_20 fz2_92_20
  · exact match_zero_fix ⟨93, by decide⟩ ⟨20, by decide⟩ p hp j hj hq fz1_93_20 fz2_93_20
  · exact match_zero_fix ⟨94, by decide⟩ ⟨20, by decide⟩ p hp j hj hq fz1_94_20 fz2_94_20
  · exact match_zero_fix ⟨95, by decide⟩ ⟨20, by decide⟩ p hp j hj hq fz1_95_20 fz2_95_20
  · exact match_zero_fix ⟨96, by decide⟩ ⟨20, by decide⟩ p hp j hj hq fz1_96_20 fz2_96_20
  · exact match_zero_fix ⟨97, by decide⟩ ⟨20, by decide⟩ p hp j hj hq fz1_97_20 fz2_97_20
  · exact match_zero_fix ⟨98, by decide⟩ ⟨20, by decide⟩ p hp j hj hq fz1_98_20 fz2_98_20
  · exact match_zero_fix ⟨99, by decide⟩ ⟨20, by decide⟩ p hp j hj hq fz1_99_20 fz2_99_20
  · exact match_zero_fix ⟨100, by decide⟩ ⟨20, by decide⟩ p hp j hj hq fz1_100_20 fz2_100_20
  · exact match_zero_fix ⟨101, by decide⟩ ⟨20, by decide⟩ p hp j hj hq fz1_101_20 fz2_101_20
  · exact match_zero_fix ⟨102, by decide⟩ ⟨20, by decide⟩ p hp j hj hq fz1_102_20 fz2_102_20
  · exact match_zero_fix ⟨103, by decide⟩ ⟨20, by decide⟩ p hp j hj hq fz1_103_20 fz2_103_20
  · exact match_zero_fix ⟨104, by decide⟩ ⟨20, by decide⟩ p hp j hj hq fz1_104_20 fz2_104_20
  · exact match_zero_fix ⟨105, by decide⟩ ⟨20, by decide⟩ p hp j hj hq fz1_105_20 fz2_105_20
  · exact match_zero_fix ⟨106, by decide⟩ ⟨20, by decide⟩ p hp j hj hq fz1_106_20 fz2_106_20
  · exact match_zero_fix ⟨107, by decide⟩ ⟨20, by decide⟩ p hp j hj hq fz1_107_20 fz2_107_20
  · exact match_zero_fix ⟨108, by decide⟩ ⟨20, by decide⟩ p hp j hj hq fz1_108_20 fz2_108_20
  · exact match_zero_fix ⟨109, by decide⟩ ⟨20, by decide⟩ p hp j hj hq fz1_109_20 fz2_109_20
  · exact match_zero_fix ⟨110, by decide⟩ ⟨20, by decide⟩ p hp j hj hq fz1_110_20 fz2_110_20
  · exact match_zero_fix ⟨111, by decide⟩ ⟨20, by decide⟩ p hp j hj hq fz1_111_20 fz2_111_20
  · exact match_zero_fix ⟨112, by decide⟩ ⟨20, by decide⟩ p hp j hj hq fz1_112_20 fz2_112_20
  · exact match_zero_fix ⟨113, by decide⟩ ⟨20, by decide⟩ p hp j hj hq fz1_113_20 fz2_113_20
  · exact match_zero_fix ⟨114, by decide⟩ ⟨20, by decide⟩ p hp j hj hq fz1_114_20 fz2_114_20
  · exact match_zero_fix ⟨115, by decide⟩ ⟨20, by decide⟩ p hp j hj hq fz1_115_20 fz2_115_20
  · exact match_zero_fix ⟨116, by decide⟩ ⟨20, by decide⟩ p hp j hj hq fz1_116_20 fz2_116_20
  · exact match_zero_fix ⟨117, by decide⟩ ⟨20, by decide⟩ p hp j hj hq fz1_117_20 fz2_117_20
  · exact match_zero_fix ⟨118, by decide⟩ ⟨20, by decide⟩ p hp j hj hq fz1_118_20 fz2_118_20
  · exact match_zero_fix ⟨119, by decide⟩ ⟨20, by decide⟩ p hp j hj hq fz1_119_20 fz2_119_20
  · exact match_zero_fix ⟨120, by decide⟩ ⟨20, by decide⟩ p hp j hj hq fz1_120_20 fz2_120_20
  · exact pair_121_20 p hp hrep j hj hq
  · exact pair_122_20 p hp hrep j hj hq
  · exact pair_123_20 p hp hrep j hj hq
  · exact pair_124_20 p hp hrep j hj hq
  · exact pair_125_20 p hp hrep j hj hq
  · exact match_zero_fix ⟨126, by decide⟩ ⟨20, by decide⟩ p hp j hj hq fz1_126_20 fz2_126_20
  · exact match_zero_fix ⟨127, by decide⟩ ⟨20, by decide⟩ p hp j hj hq fz1_127_20 fz2_127_20
  · exact match_zero_fix ⟨128, by decide⟩ ⟨20, by decide⟩ p hp j hj hq fz1_128_20 fz2_128_20
  · exact match_zero_fix ⟨129, by decide⟩ ⟨20, by decide⟩ p hp j hj hq fz1_129_20 fz2_129_20
  · exact match_zero_fix ⟨130, by decide⟩ ⟨20, by decide⟩ p hp j hj hq fz1_130_20 fz2_130_20
  · exact match_zero_fix ⟨131, by decide⟩ ⟨20, by decide⟩ p hp j hj hq fz1_131_20 fz2_131_20
  · exact match_zero_fix ⟨132, by decide⟩ ⟨20, by decide⟩ p hp j hj hq fz1_132_20 fz2_132_20
  · exact match_zero_fix ⟨133, by decide⟩ ⟨20, by decide⟩ p hp j hj hq fz1_133_20 fz2_133_20
  · exact match_zero_fix ⟨134, by decide⟩ ⟨20, by decide⟩ p hp j hj hq fz1_134_20 fz2_134_20
  · exact match_zero_fix ⟨135, by decide⟩ ⟨20, by decide⟩ p hp j hj hq fz1_135_20 fz2_135_20
  · exact match_zero_fix ⟨136, by decide⟩ ⟨20, by decide⟩ p hp j hj hq fz1_136_20 fz2_136_20
  · exact match_zero_fix ⟨137, by decide⟩ ⟨20, by decide⟩ p hp j hj hq fz1_137_20 fz2_137_20
  · exact match_zero_fix ⟨138, by decide⟩ ⟨20, by decide⟩ p hp j hj hq fz1_138_20 fz2_138_20
  · exact match_zero_fix ⟨139, by decide⟩ ⟨20, by decide⟩ p hp j hj hq fz1_139_20 fz2_139_20
  · exact match_zero_fix ⟨140, by decide⟩ ⟨20, by decide⟩ p hp j hj hq fz1_140_20 fz2_140_20
  · exact pair_141_20 p hp hrep j hj hq
  · exact match_zero_fix ⟨142, by decide⟩ ⟨20, by decide⟩ p hp j hj hq fz1_142_20 fz2_142_20
  · exact match_zero_fix ⟨143, by decide⟩ ⟨20, by decide⟩ p hp j hj hq fz1_143_20 fz2_143_20
  · exact match_zero_fix ⟨144, by decide⟩ ⟨20, by decide⟩ p hp j hj hq fz1_144_20 fz2_144_20
  · exact match_zero_fix ⟨145, by decide⟩ ⟨20, by decide⟩ p hp j hj hq fz1_145_20 fz2_145_20
  · exact match_zero_fix ⟨146, by decide⟩ ⟨20, by decide⟩ p hp j hj hq fz1_146_20 fz2_146_20
  · exact pair_147_20 p hp hrep j hj hq

theorem master_21 (p : Nat) (hp : p < (Q2.transData.getD 21 []).length)
    (hrep : (Q2.cosetIsRep.getD 21 []).getD p false = true)
    (rK : Fin 148) (j : Nat) (hj : j < (repChars.getD rK.val []).length)
    (hq : (normIsRep.getD rK.val []).getD j false = true) :
    species (Q2.reps (⟨21, by decide⟩ : Fin 148)) (colE2 ⟨21, by decide⟩ p hp)
        (rowE2 rK j hj hq)
      = species (reps (⟨21, by decide⟩ : Fin 148))
        (colE1 ⟨21, by decide⟩ p (transLenTr ⟨21, by decide⟩ p hp)) (rowE1 rK j hj) := by
  rcases rK with ⟨nK, hnK⟩; interval_cases nK
  · exact match_zero_len ⟨0, by decide⟩ ⟨21, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨1, by decide⟩ ⟨21, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨2, by decide⟩ ⟨21, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨3, by decide⟩ ⟨21, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨4, by decide⟩ ⟨21, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨5, by decide⟩ ⟨21, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨6, by decide⟩ ⟨21, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨7, by decide⟩ ⟨21, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨8, by decide⟩ ⟨21, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨9, by decide⟩ ⟨21, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨10, by decide⟩ ⟨21, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨11, by decide⟩ ⟨21, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨12, by decide⟩ ⟨21, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_fix ⟨13, by decide⟩ ⟨21, by decide⟩ p hp j hj hq fz1_13_21 fz2_13_21
  · exact match_zero_fix ⟨14, by decide⟩ ⟨21, by decide⟩ p hp j hj hq fz1_14_21 fz2_14_21
  · exact match_zero_fix ⟨15, by decide⟩ ⟨21, by decide⟩ p hp j hj hq fz1_15_21 fz2_15_21
  · exact match_zero_fix ⟨16, by decide⟩ ⟨21, by decide⟩ p hp j hj hq fz1_16_21 fz2_16_21
  · exact match_zero_fix ⟨17, by decide⟩ ⟨21, by decide⟩ p hp j hj hq fz1_17_21 fz2_17_21
  · exact match_zero_fix ⟨18, by decide⟩ ⟨21, by decide⟩ p hp j hj hq fz1_18_21 fz2_18_21
  · exact match_zero_fix ⟨19, by decide⟩ ⟨21, by decide⟩ p hp j hj hq fz1_19_21 fz2_19_21
  · exact match_zero_fix ⟨20, by decide⟩ ⟨21, by decide⟩ p hp j hj hq fz1_20_21 fz2_20_21
  · exact pair_21_21 p hp hrep j hj hq
  · exact match_zero_fix ⟨22, by decide⟩ ⟨21, by decide⟩ p hp j hj hq fz1_22_21 fz2_22_21
  · exact match_zero_fix ⟨23, by decide⟩ ⟨21, by decide⟩ p hp j hj hq fz1_23_21 fz2_23_21
  · exact match_zero_fix ⟨24, by decide⟩ ⟨21, by decide⟩ p hp j hj hq fz1_24_21 fz2_24_21
  · exact match_zero_fix ⟨25, by decide⟩ ⟨21, by decide⟩ p hp j hj hq fz1_25_21 fz2_25_21
  · exact match_zero_fix ⟨26, by decide⟩ ⟨21, by decide⟩ p hp j hj hq fz1_26_21 fz2_26_21
  · exact match_zero_fix ⟨27, by decide⟩ ⟨21, by decide⟩ p hp j hj hq fz1_27_21 fz2_27_21
  · exact match_zero_fix ⟨28, by decide⟩ ⟨21, by decide⟩ p hp j hj hq fz1_28_21 fz2_28_21
  · exact match_zero_fix ⟨29, by decide⟩ ⟨21, by decide⟩ p hp j hj hq fz1_29_21 fz2_29_21
  · exact match_zero_fix ⟨30, by decide⟩ ⟨21, by decide⟩ p hp j hj hq fz1_30_21 fz2_30_21
  · exact match_zero_fix ⟨31, by decide⟩ ⟨21, by decide⟩ p hp j hj hq fz1_31_21 fz2_31_21
  · exact match_zero_fix ⟨32, by decide⟩ ⟨21, by decide⟩ p hp j hj hq fz1_32_21 fz2_32_21
  · exact match_zero_fix ⟨33, by decide⟩ ⟨21, by decide⟩ p hp j hj hq fz1_33_21 fz2_33_21
  · exact match_zero_fix ⟨34, by decide⟩ ⟨21, by decide⟩ p hp j hj hq fz1_34_21 fz2_34_21
  · exact match_zero_fix ⟨35, by decide⟩ ⟨21, by decide⟩ p hp j hj hq fz1_35_21 fz2_35_21
  · exact match_zero_fix ⟨36, by decide⟩ ⟨21, by decide⟩ p hp j hj hq fz1_36_21 fz2_36_21
  · exact match_zero_fix ⟨37, by decide⟩ ⟨21, by decide⟩ p hp j hj hq fz1_37_21 fz2_37_21
  · exact match_zero_fix ⟨38, by decide⟩ ⟨21, by decide⟩ p hp j hj hq fz1_38_21 fz2_38_21
  · exact match_zero_fix ⟨39, by decide⟩ ⟨21, by decide⟩ p hp j hj hq fz1_39_21 fz2_39_21
  · exact match_zero_fix ⟨40, by decide⟩ ⟨21, by decide⟩ p hp j hj hq fz1_40_21 fz2_40_21
  · exact match_zero_fix ⟨41, by decide⟩ ⟨21, by decide⟩ p hp j hj hq fz1_41_21 fz2_41_21
  · exact match_zero_fix ⟨42, by decide⟩ ⟨21, by decide⟩ p hp j hj hq fz1_42_21 fz2_42_21
  · exact match_zero_fix ⟨43, by decide⟩ ⟨21, by decide⟩ p hp j hj hq fz1_43_21 fz2_43_21
  · exact match_zero_fix ⟨44, by decide⟩ ⟨21, by decide⟩ p hp j hj hq fz1_44_21 fz2_44_21
  · exact match_zero_fix ⟨45, by decide⟩ ⟨21, by decide⟩ p hp j hj hq fz1_45_21 fz2_45_21
  · exact match_zero_fix ⟨46, by decide⟩ ⟨21, by decide⟩ p hp j hj hq fz1_46_21 fz2_46_21
  · exact match_zero_fix ⟨47, by decide⟩ ⟨21, by decide⟩ p hp j hj hq fz1_47_21 fz2_47_21
  · exact match_zero_fix ⟨48, by decide⟩ ⟨21, by decide⟩ p hp j hj hq fz1_48_21 fz2_48_21
  · exact match_zero_fix ⟨49, by decide⟩ ⟨21, by decide⟩ p hp j hj hq fz1_49_21 fz2_49_21
  · exact match_zero_fix ⟨50, by decide⟩ ⟨21, by decide⟩ p hp j hj hq fz1_50_21 fz2_50_21
  · exact match_zero_fix ⟨51, by decide⟩ ⟨21, by decide⟩ p hp j hj hq fz1_51_21 fz2_51_21
  · exact match_zero_fix ⟨52, by decide⟩ ⟨21, by decide⟩ p hp j hj hq fz1_52_21 fz2_52_21
  · exact match_zero_fix ⟨53, by decide⟩ ⟨21, by decide⟩ p hp j hj hq fz1_53_21 fz2_53_21
  · exact match_zero_fix ⟨54, by decide⟩ ⟨21, by decide⟩ p hp j hj hq fz1_54_21 fz2_54_21
  · exact match_zero_fix ⟨55, by decide⟩ ⟨21, by decide⟩ p hp j hj hq fz1_55_21 fz2_55_21
  · exact match_zero_fix ⟨56, by decide⟩ ⟨21, by decide⟩ p hp j hj hq fz1_56_21 fz2_56_21
  · exact match_zero_fix ⟨57, by decide⟩ ⟨21, by decide⟩ p hp j hj hq fz1_57_21 fz2_57_21
  · exact match_zero_fix ⟨58, by decide⟩ ⟨21, by decide⟩ p hp j hj hq fz1_58_21 fz2_58_21
  · exact match_zero_fix ⟨59, by decide⟩ ⟨21, by decide⟩ p hp j hj hq fz1_59_21 fz2_59_21
  · exact match_zero_fix ⟨60, by decide⟩ ⟨21, by decide⟩ p hp j hj hq fz1_60_21 fz2_60_21
  · exact match_zero_fix ⟨61, by decide⟩ ⟨21, by decide⟩ p hp j hj hq fz1_61_21 fz2_61_21
  · exact match_zero_fix ⟨62, by decide⟩ ⟨21, by decide⟩ p hp j hj hq fz1_62_21 fz2_62_21
  · exact match_zero_fix ⟨63, by decide⟩ ⟨21, by decide⟩ p hp j hj hq fz1_63_21 fz2_63_21
  · exact match_zero_fix ⟨64, by decide⟩ ⟨21, by decide⟩ p hp j hj hq fz1_64_21 fz2_64_21
  · exact match_zero_fix ⟨65, by decide⟩ ⟨21, by decide⟩ p hp j hj hq fz1_65_21 fz2_65_21
  · exact match_zero_fix ⟨66, by decide⟩ ⟨21, by decide⟩ p hp j hj hq fz1_66_21 fz2_66_21
  · exact match_zero_fix ⟨67, by decide⟩ ⟨21, by decide⟩ p hp j hj hq fz1_67_21 fz2_67_21
  · exact match_zero_fix ⟨68, by decide⟩ ⟨21, by decide⟩ p hp j hj hq fz1_68_21 fz2_68_21
  · exact match_zero_fix ⟨69, by decide⟩ ⟨21, by decide⟩ p hp j hj hq fz1_69_21 fz2_69_21
  · exact match_zero_fix ⟨70, by decide⟩ ⟨21, by decide⟩ p hp j hj hq fz1_70_21 fz2_70_21
  · exact match_zero_fix ⟨71, by decide⟩ ⟨21, by decide⟩ p hp j hj hq fz1_71_21 fz2_71_21
  · exact match_zero_fix ⟨72, by decide⟩ ⟨21, by decide⟩ p hp j hj hq fz1_72_21 fz2_72_21
  · exact match_zero_fix ⟨73, by decide⟩ ⟨21, by decide⟩ p hp j hj hq fz1_73_21 fz2_73_21
  · exact match_zero_fix ⟨74, by decide⟩ ⟨21, by decide⟩ p hp j hj hq fz1_74_21 fz2_74_21
  · exact match_zero_fix ⟨75, by decide⟩ ⟨21, by decide⟩ p hp j hj hq fz1_75_21 fz2_75_21
  · exact match_zero_fix ⟨76, by decide⟩ ⟨21, by decide⟩ p hp j hj hq fz1_76_21 fz2_76_21
  · exact match_zero_fix ⟨77, by decide⟩ ⟨21, by decide⟩ p hp j hj hq fz1_77_21 fz2_77_21
  · exact match_zero_fix ⟨78, by decide⟩ ⟨21, by decide⟩ p hp j hj hq fz1_78_21 fz2_78_21
  · exact match_zero_fix ⟨79, by decide⟩ ⟨21, by decide⟩ p hp j hj hq fz1_79_21 fz2_79_21
  · exact match_zero_fix ⟨80, by decide⟩ ⟨21, by decide⟩ p hp j hj hq fz1_80_21 fz2_80_21
  · exact match_zero_fix ⟨81, by decide⟩ ⟨21, by decide⟩ p hp j hj hq fz1_81_21 fz2_81_21
  · exact pair_82_21 p hp hrep j hj hq
  · exact match_zero_fix ⟨83, by decide⟩ ⟨21, by decide⟩ p hp j hj hq fz1_83_21 fz2_83_21
  · exact match_zero_fix ⟨84, by decide⟩ ⟨21, by decide⟩ p hp j hj hq fz1_84_21 fz2_84_21
  · exact pair_85_21 p hp hrep j hj hq
  · exact pair_86_21 p hp hrep j hj hq
  · exact pair_87_21 p hp hrep j hj hq
  · exact pair_88_21 p hp hrep j hj hq
  · exact pair_89_21 p hp hrep j hj hq
  · exact match_zero_fix ⟨90, by decide⟩ ⟨21, by decide⟩ p hp j hj hq fz1_90_21 fz2_90_21
  · exact match_zero_fix ⟨91, by decide⟩ ⟨21, by decide⟩ p hp j hj hq fz1_91_21 fz2_91_21
  · exact match_zero_fix ⟨92, by decide⟩ ⟨21, by decide⟩ p hp j hj hq fz1_92_21 fz2_92_21
  · exact match_zero_fix ⟨93, by decide⟩ ⟨21, by decide⟩ p hp j hj hq fz1_93_21 fz2_93_21
  · exact match_zero_fix ⟨94, by decide⟩ ⟨21, by decide⟩ p hp j hj hq fz1_94_21 fz2_94_21
  · exact match_zero_fix ⟨95, by decide⟩ ⟨21, by decide⟩ p hp j hj hq fz1_95_21 fz2_95_21
  · exact match_zero_fix ⟨96, by decide⟩ ⟨21, by decide⟩ p hp j hj hq fz1_96_21 fz2_96_21
  · exact match_zero_fix ⟨97, by decide⟩ ⟨21, by decide⟩ p hp j hj hq fz1_97_21 fz2_97_21
  · exact match_zero_fix ⟨98, by decide⟩ ⟨21, by decide⟩ p hp j hj hq fz1_98_21 fz2_98_21
  · exact match_zero_fix ⟨99, by decide⟩ ⟨21, by decide⟩ p hp j hj hq fz1_99_21 fz2_99_21
  · exact match_zero_fix ⟨100, by decide⟩ ⟨21, by decide⟩ p hp j hj hq fz1_100_21 fz2_100_21
  · exact match_zero_fix ⟨101, by decide⟩ ⟨21, by decide⟩ p hp j hj hq fz1_101_21 fz2_101_21
  · exact match_zero_fix ⟨102, by decide⟩ ⟨21, by decide⟩ p hp j hj hq fz1_102_21 fz2_102_21
  · exact match_zero_fix ⟨103, by decide⟩ ⟨21, by decide⟩ p hp j hj hq fz1_103_21 fz2_103_21
  · exact match_zero_fix ⟨104, by decide⟩ ⟨21, by decide⟩ p hp j hj hq fz1_104_21 fz2_104_21
  · exact match_zero_fix ⟨105, by decide⟩ ⟨21, by decide⟩ p hp j hj hq fz1_105_21 fz2_105_21
  · exact match_zero_fix ⟨106, by decide⟩ ⟨21, by decide⟩ p hp j hj hq fz1_106_21 fz2_106_21
  · exact match_zero_fix ⟨107, by decide⟩ ⟨21, by decide⟩ p hp j hj hq fz1_107_21 fz2_107_21
  · exact match_zero_fix ⟨108, by decide⟩ ⟨21, by decide⟩ p hp j hj hq fz1_108_21 fz2_108_21
  · exact match_zero_fix ⟨109, by decide⟩ ⟨21, by decide⟩ p hp j hj hq fz1_109_21 fz2_109_21
  · exact match_zero_fix ⟨110, by decide⟩ ⟨21, by decide⟩ p hp j hj hq fz1_110_21 fz2_110_21
  · exact match_zero_fix ⟨111, by decide⟩ ⟨21, by decide⟩ p hp j hj hq fz1_111_21 fz2_111_21
  · exact match_zero_fix ⟨112, by decide⟩ ⟨21, by decide⟩ p hp j hj hq fz1_112_21 fz2_112_21
  · exact match_zero_fix ⟨113, by decide⟩ ⟨21, by decide⟩ p hp j hj hq fz1_113_21 fz2_113_21
  · exact match_zero_fix ⟨114, by decide⟩ ⟨21, by decide⟩ p hp j hj hq fz1_114_21 fz2_114_21
  · exact match_zero_fix ⟨115, by decide⟩ ⟨21, by decide⟩ p hp j hj hq fz1_115_21 fz2_115_21
  · exact match_zero_fix ⟨116, by decide⟩ ⟨21, by decide⟩ p hp j hj hq fz1_116_21 fz2_116_21
  · exact match_zero_fix ⟨117, by decide⟩ ⟨21, by decide⟩ p hp j hj hq fz1_117_21 fz2_117_21
  · exact match_zero_fix ⟨118, by decide⟩ ⟨21, by decide⟩ p hp j hj hq fz1_118_21 fz2_118_21
  · exact match_zero_fix ⟨119, by decide⟩ ⟨21, by decide⟩ p hp j hj hq fz1_119_21 fz2_119_21
  · exact match_zero_fix ⟨120, by decide⟩ ⟨21, by decide⟩ p hp j hj hq fz1_120_21 fz2_120_21
  · exact match_zero_fix ⟨121, by decide⟩ ⟨21, by decide⟩ p hp j hj hq fz1_121_21 fz2_121_21
  · exact match_zero_fix ⟨122, by decide⟩ ⟨21, by decide⟩ p hp j hj hq fz1_122_21 fz2_122_21
  · exact match_zero_fix ⟨123, by decide⟩ ⟨21, by decide⟩ p hp j hj hq fz1_123_21 fz2_123_21
  · exact match_zero_fix ⟨124, by decide⟩ ⟨21, by decide⟩ p hp j hj hq fz1_124_21 fz2_124_21
  · exact match_zero_fix ⟨125, by decide⟩ ⟨21, by decide⟩ p hp j hj hq fz1_125_21 fz2_125_21
  · exact pair_126_21 p hp hrep j hj hq
  · exact pair_127_21 p hp hrep j hj hq
  · exact pair_128_21 p hp hrep j hj hq
  · exact pair_129_21 p hp hrep j hj hq
  · exact pair_130_21 p hp hrep j hj hq
  · exact match_zero_fix ⟨131, by decide⟩ ⟨21, by decide⟩ p hp j hj hq fz1_131_21 fz2_131_21
  · exact match_zero_fix ⟨132, by decide⟩ ⟨21, by decide⟩ p hp j hj hq fz1_132_21 fz2_132_21
  · exact match_zero_fix ⟨133, by decide⟩ ⟨21, by decide⟩ p hp j hj hq fz1_133_21 fz2_133_21
  · exact match_zero_fix ⟨134, by decide⟩ ⟨21, by decide⟩ p hp j hj hq fz1_134_21 fz2_134_21
  · exact match_zero_fix ⟨135, by decide⟩ ⟨21, by decide⟩ p hp j hj hq fz1_135_21 fz2_135_21
  · exact match_zero_fix ⟨136, by decide⟩ ⟨21, by decide⟩ p hp j hj hq fz1_136_21 fz2_136_21
  · exact match_zero_fix ⟨137, by decide⟩ ⟨21, by decide⟩ p hp j hj hq fz1_137_21 fz2_137_21
  · exact match_zero_fix ⟨138, by decide⟩ ⟨21, by decide⟩ p hp j hj hq fz1_138_21 fz2_138_21
  · exact match_zero_fix ⟨139, by decide⟩ ⟨21, by decide⟩ p hp j hj hq fz1_139_21 fz2_139_21
  · exact match_zero_fix ⟨140, by decide⟩ ⟨21, by decide⟩ p hp j hj hq fz1_140_21 fz2_140_21
  · exact pair_141_21 p hp hrep j hj hq
  · exact match_zero_fix ⟨142, by decide⟩ ⟨21, by decide⟩ p hp j hj hq fz1_142_21 fz2_142_21
  · exact match_zero_fix ⟨143, by decide⟩ ⟨21, by decide⟩ p hp j hj hq fz1_143_21 fz2_143_21
  · exact match_zero_fix ⟨144, by decide⟩ ⟨21, by decide⟩ p hp j hj hq fz1_144_21 fz2_144_21
  · exact match_zero_fix ⟨145, by decide⟩ ⟨21, by decide⟩ p hp j hj hq fz1_145_21 fz2_145_21
  · exact match_zero_fix ⟨146, by decide⟩ ⟨21, by decide⟩ p hp j hj hq fz1_146_21 fz2_146_21
  · exact pair_147_21 p hp hrep j hj hq

theorem master_22 (p : Nat) (hp : p < (Q2.transData.getD 22 []).length)
    (hrep : (Q2.cosetIsRep.getD 22 []).getD p false = true)
    (rK : Fin 148) (j : Nat) (hj : j < (repChars.getD rK.val []).length)
    (hq : (normIsRep.getD rK.val []).getD j false = true) :
    species (Q2.reps (⟨22, by decide⟩ : Fin 148)) (colE2 ⟨22, by decide⟩ p hp)
        (rowE2 rK j hj hq)
      = species (reps (⟨22, by decide⟩ : Fin 148))
        (colE1 ⟨22, by decide⟩ p (transLenTr ⟨22, by decide⟩ p hp)) (rowE1 rK j hj) := by
  rcases rK with ⟨nK, hnK⟩; interval_cases nK
  · exact match_zero_len ⟨0, by decide⟩ ⟨22, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨1, by decide⟩ ⟨22, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨2, by decide⟩ ⟨22, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨3, by decide⟩ ⟨22, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨4, by decide⟩ ⟨22, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨5, by decide⟩ ⟨22, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨6, by decide⟩ ⟨22, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨7, by decide⟩ ⟨22, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨8, by decide⟩ ⟨22, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨9, by decide⟩ ⟨22, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨10, by decide⟩ ⟨22, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨11, by decide⟩ ⟨22, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨12, by decide⟩ ⟨22, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_fix ⟨13, by decide⟩ ⟨22, by decide⟩ p hp j hj hq fz1_13_22 fz2_13_22
  · exact match_zero_fix ⟨14, by decide⟩ ⟨22, by decide⟩ p hp j hj hq fz1_14_22 fz2_14_22
  · exact match_zero_fix ⟨15, by decide⟩ ⟨22, by decide⟩ p hp j hj hq fz1_15_22 fz2_15_22
  · exact match_zero_fix ⟨16, by decide⟩ ⟨22, by decide⟩ p hp j hj hq fz1_16_22 fz2_16_22
  · exact match_zero_fix ⟨17, by decide⟩ ⟨22, by decide⟩ p hp j hj hq fz1_17_22 fz2_17_22
  · exact match_zero_fix ⟨18, by decide⟩ ⟨22, by decide⟩ p hp j hj hq fz1_18_22 fz2_18_22
  · exact match_zero_fix ⟨19, by decide⟩ ⟨22, by decide⟩ p hp j hj hq fz1_19_22 fz2_19_22
  · exact match_zero_fix ⟨20, by decide⟩ ⟨22, by decide⟩ p hp j hj hq fz1_20_22 fz2_20_22
  · exact match_zero_fix ⟨21, by decide⟩ ⟨22, by decide⟩ p hp j hj hq fz1_21_22 fz2_21_22
  · exact pair_22_22 p hp hrep j hj hq
  · exact match_zero_fix ⟨23, by decide⟩ ⟨22, by decide⟩ p hp j hj hq fz1_23_22 fz2_23_22
  · exact match_zero_fix ⟨24, by decide⟩ ⟨22, by decide⟩ p hp j hj hq fz1_24_22 fz2_24_22
  · exact match_zero_fix ⟨25, by decide⟩ ⟨22, by decide⟩ p hp j hj hq fz1_25_22 fz2_25_22
  · exact match_zero_fix ⟨26, by decide⟩ ⟨22, by decide⟩ p hp j hj hq fz1_26_22 fz2_26_22
  · exact match_zero_fix ⟨27, by decide⟩ ⟨22, by decide⟩ p hp j hj hq fz1_27_22 fz2_27_22
  · exact match_zero_fix ⟨28, by decide⟩ ⟨22, by decide⟩ p hp j hj hq fz1_28_22 fz2_28_22
  · exact match_zero_fix ⟨29, by decide⟩ ⟨22, by decide⟩ p hp j hj hq fz1_29_22 fz2_29_22
  · exact match_zero_fix ⟨30, by decide⟩ ⟨22, by decide⟩ p hp j hj hq fz1_30_22 fz2_30_22
  · exact match_zero_fix ⟨31, by decide⟩ ⟨22, by decide⟩ p hp j hj hq fz1_31_22 fz2_31_22
  · exact match_zero_fix ⟨32, by decide⟩ ⟨22, by decide⟩ p hp j hj hq fz1_32_22 fz2_32_22
  · exact match_zero_fix ⟨33, by decide⟩ ⟨22, by decide⟩ p hp j hj hq fz1_33_22 fz2_33_22
  · exact match_zero_fix ⟨34, by decide⟩ ⟨22, by decide⟩ p hp j hj hq fz1_34_22 fz2_34_22
  · exact match_zero_fix ⟨35, by decide⟩ ⟨22, by decide⟩ p hp j hj hq fz1_35_22 fz2_35_22
  · exact match_zero_fix ⟨36, by decide⟩ ⟨22, by decide⟩ p hp j hj hq fz1_36_22 fz2_36_22
  · exact match_zero_fix ⟨37, by decide⟩ ⟨22, by decide⟩ p hp j hj hq fz1_37_22 fz2_37_22
  · exact match_zero_fix ⟨38, by decide⟩ ⟨22, by decide⟩ p hp j hj hq fz1_38_22 fz2_38_22
  · exact match_zero_fix ⟨39, by decide⟩ ⟨22, by decide⟩ p hp j hj hq fz1_39_22 fz2_39_22
  · exact match_zero_fix ⟨40, by decide⟩ ⟨22, by decide⟩ p hp j hj hq fz1_40_22 fz2_40_22
  · exact match_zero_fix ⟨41, by decide⟩ ⟨22, by decide⟩ p hp j hj hq fz1_41_22 fz2_41_22
  · exact match_zero_fix ⟨42, by decide⟩ ⟨22, by decide⟩ p hp j hj hq fz1_42_22 fz2_42_22
  · exact match_zero_fix ⟨43, by decide⟩ ⟨22, by decide⟩ p hp j hj hq fz1_43_22 fz2_43_22
  · exact match_zero_fix ⟨44, by decide⟩ ⟨22, by decide⟩ p hp j hj hq fz1_44_22 fz2_44_22
  · exact match_zero_fix ⟨45, by decide⟩ ⟨22, by decide⟩ p hp j hj hq fz1_45_22 fz2_45_22
  · exact match_zero_fix ⟨46, by decide⟩ ⟨22, by decide⟩ p hp j hj hq fz1_46_22 fz2_46_22
  · exact match_zero_fix ⟨47, by decide⟩ ⟨22, by decide⟩ p hp j hj hq fz1_47_22 fz2_47_22
  · exact match_zero_fix ⟨48, by decide⟩ ⟨22, by decide⟩ p hp j hj hq fz1_48_22 fz2_48_22
  · exact match_zero_fix ⟨49, by decide⟩ ⟨22, by decide⟩ p hp j hj hq fz1_49_22 fz2_49_22
  · exact match_zero_fix ⟨50, by decide⟩ ⟨22, by decide⟩ p hp j hj hq fz1_50_22 fz2_50_22
  · exact match_zero_fix ⟨51, by decide⟩ ⟨22, by decide⟩ p hp j hj hq fz1_51_22 fz2_51_22
  · exact match_zero_fix ⟨52, by decide⟩ ⟨22, by decide⟩ p hp j hj hq fz1_52_22 fz2_52_22
  · exact match_zero_fix ⟨53, by decide⟩ ⟨22, by decide⟩ p hp j hj hq fz1_53_22 fz2_53_22
  · exact match_zero_fix ⟨54, by decide⟩ ⟨22, by decide⟩ p hp j hj hq fz1_54_22 fz2_54_22
  · exact match_zero_fix ⟨55, by decide⟩ ⟨22, by decide⟩ p hp j hj hq fz1_55_22 fz2_55_22
  · exact match_zero_fix ⟨56, by decide⟩ ⟨22, by decide⟩ p hp j hj hq fz1_56_22 fz2_56_22
  · exact match_zero_fix ⟨57, by decide⟩ ⟨22, by decide⟩ p hp j hj hq fz1_57_22 fz2_57_22
  · exact match_zero_fix ⟨58, by decide⟩ ⟨22, by decide⟩ p hp j hj hq fz1_58_22 fz2_58_22
  · exact match_zero_fix ⟨59, by decide⟩ ⟨22, by decide⟩ p hp j hj hq fz1_59_22 fz2_59_22
  · exact match_zero_fix ⟨60, by decide⟩ ⟨22, by decide⟩ p hp j hj hq fz1_60_22 fz2_60_22
  · exact match_zero_fix ⟨61, by decide⟩ ⟨22, by decide⟩ p hp j hj hq fz1_61_22 fz2_61_22
  · exact match_zero_fix ⟨62, by decide⟩ ⟨22, by decide⟩ p hp j hj hq fz1_62_22 fz2_62_22
  · exact match_zero_fix ⟨63, by decide⟩ ⟨22, by decide⟩ p hp j hj hq fz1_63_22 fz2_63_22
  · exact match_zero_fix ⟨64, by decide⟩ ⟨22, by decide⟩ p hp j hj hq fz1_64_22 fz2_64_22
  · exact match_zero_fix ⟨65, by decide⟩ ⟨22, by decide⟩ p hp j hj hq fz1_65_22 fz2_65_22
  · exact match_zero_fix ⟨66, by decide⟩ ⟨22, by decide⟩ p hp j hj hq fz1_66_22 fz2_66_22
  · exact match_zero_fix ⟨67, by decide⟩ ⟨22, by decide⟩ p hp j hj hq fz1_67_22 fz2_67_22
  · exact match_zero_fix ⟨68, by decide⟩ ⟨22, by decide⟩ p hp j hj hq fz1_68_22 fz2_68_22
  · exact match_zero_fix ⟨69, by decide⟩ ⟨22, by decide⟩ p hp j hj hq fz1_69_22 fz2_69_22
  · exact match_zero_fix ⟨70, by decide⟩ ⟨22, by decide⟩ p hp j hj hq fz1_70_22 fz2_70_22
  · exact match_zero_fix ⟨71, by decide⟩ ⟨22, by decide⟩ p hp j hj hq fz1_71_22 fz2_71_22
  · exact match_zero_fix ⟨72, by decide⟩ ⟨22, by decide⟩ p hp j hj hq fz1_72_22 fz2_72_22
  · exact match_zero_fix ⟨73, by decide⟩ ⟨22, by decide⟩ p hp j hj hq fz1_73_22 fz2_73_22
  · exact match_zero_fix ⟨74, by decide⟩ ⟨22, by decide⟩ p hp j hj hq fz1_74_22 fz2_74_22
  · exact match_zero_fix ⟨75, by decide⟩ ⟨22, by decide⟩ p hp j hj hq fz1_75_22 fz2_75_22
  · exact match_zero_fix ⟨76, by decide⟩ ⟨22, by decide⟩ p hp j hj hq fz1_76_22 fz2_76_22
  · exact match_zero_fix ⟨77, by decide⟩ ⟨22, by decide⟩ p hp j hj hq fz1_77_22 fz2_77_22
  · exact match_zero_fix ⟨78, by decide⟩ ⟨22, by decide⟩ p hp j hj hq fz1_78_22 fz2_78_22
  · exact match_zero_fix ⟨79, by decide⟩ ⟨22, by decide⟩ p hp j hj hq fz1_79_22 fz2_79_22
  · exact match_zero_fix ⟨80, by decide⟩ ⟨22, by decide⟩ p hp j hj hq fz1_80_22 fz2_80_22
  · exact match_zero_fix ⟨81, by decide⟩ ⟨22, by decide⟩ p hp j hj hq fz1_81_22 fz2_81_22
  · exact match_zero_fix ⟨82, by decide⟩ ⟨22, by decide⟩ p hp j hj hq fz1_82_22 fz2_82_22
  · exact pair_83_22 p hp hrep j hj hq
  · exact match_zero_fix ⟨84, by decide⟩ ⟨22, by decide⟩ p hp j hj hq fz1_84_22 fz2_84_22
  · exact pair_85_22 p hp hrep j hj hq
  · exact pair_86_22 p hp hrep j hj hq
  · exact pair_87_22 p hp hrep j hj hq
  · exact pair_88_22 p hp hrep j hj hq
  · exact pair_89_22 p hp hrep j hj hq
  · exact match_zero_fix ⟨90, by decide⟩ ⟨22, by decide⟩ p hp j hj hq fz1_90_22 fz2_90_22
  · exact match_zero_fix ⟨91, by decide⟩ ⟨22, by decide⟩ p hp j hj hq fz1_91_22 fz2_91_22
  · exact match_zero_fix ⟨92, by decide⟩ ⟨22, by decide⟩ p hp j hj hq fz1_92_22 fz2_92_22
  · exact match_zero_fix ⟨93, by decide⟩ ⟨22, by decide⟩ p hp j hj hq fz1_93_22 fz2_93_22
  · exact match_zero_fix ⟨94, by decide⟩ ⟨22, by decide⟩ p hp j hj hq fz1_94_22 fz2_94_22
  · exact match_zero_fix ⟨95, by decide⟩ ⟨22, by decide⟩ p hp j hj hq fz1_95_22 fz2_95_22
  · exact match_zero_fix ⟨96, by decide⟩ ⟨22, by decide⟩ p hp j hj hq fz1_96_22 fz2_96_22
  · exact match_zero_fix ⟨97, by decide⟩ ⟨22, by decide⟩ p hp j hj hq fz1_97_22 fz2_97_22
  · exact match_zero_fix ⟨98, by decide⟩ ⟨22, by decide⟩ p hp j hj hq fz1_98_22 fz2_98_22
  · exact match_zero_fix ⟨99, by decide⟩ ⟨22, by decide⟩ p hp j hj hq fz1_99_22 fz2_99_22
  · exact match_zero_fix ⟨100, by decide⟩ ⟨22, by decide⟩ p hp j hj hq fz1_100_22 fz2_100_22
  · exact match_zero_fix ⟨101, by decide⟩ ⟨22, by decide⟩ p hp j hj hq fz1_101_22 fz2_101_22
  · exact match_zero_fix ⟨102, by decide⟩ ⟨22, by decide⟩ p hp j hj hq fz1_102_22 fz2_102_22
  · exact match_zero_fix ⟨103, by decide⟩ ⟨22, by decide⟩ p hp j hj hq fz1_103_22 fz2_103_22
  · exact match_zero_fix ⟨104, by decide⟩ ⟨22, by decide⟩ p hp j hj hq fz1_104_22 fz2_104_22
  · exact match_zero_fix ⟨105, by decide⟩ ⟨22, by decide⟩ p hp j hj hq fz1_105_22 fz2_105_22
  · exact match_zero_fix ⟨106, by decide⟩ ⟨22, by decide⟩ p hp j hj hq fz1_106_22 fz2_106_22
  · exact match_zero_fix ⟨107, by decide⟩ ⟨22, by decide⟩ p hp j hj hq fz1_107_22 fz2_107_22
  · exact match_zero_fix ⟨108, by decide⟩ ⟨22, by decide⟩ p hp j hj hq fz1_108_22 fz2_108_22
  · exact match_zero_fix ⟨109, by decide⟩ ⟨22, by decide⟩ p hp j hj hq fz1_109_22 fz2_109_22
  · exact match_zero_fix ⟨110, by decide⟩ ⟨22, by decide⟩ p hp j hj hq fz1_110_22 fz2_110_22
  · exact match_zero_fix ⟨111, by decide⟩ ⟨22, by decide⟩ p hp j hj hq fz1_111_22 fz2_111_22
  · exact match_zero_fix ⟨112, by decide⟩ ⟨22, by decide⟩ p hp j hj hq fz1_112_22 fz2_112_22
  · exact match_zero_fix ⟨113, by decide⟩ ⟨22, by decide⟩ p hp j hj hq fz1_113_22 fz2_113_22
  · exact match_zero_fix ⟨114, by decide⟩ ⟨22, by decide⟩ p hp j hj hq fz1_114_22 fz2_114_22
  · exact match_zero_fix ⟨115, by decide⟩ ⟨22, by decide⟩ p hp j hj hq fz1_115_22 fz2_115_22
  · exact match_zero_fix ⟨116, by decide⟩ ⟨22, by decide⟩ p hp j hj hq fz1_116_22 fz2_116_22
  · exact match_zero_fix ⟨117, by decide⟩ ⟨22, by decide⟩ p hp j hj hq fz1_117_22 fz2_117_22
  · exact match_zero_fix ⟨118, by decide⟩ ⟨22, by decide⟩ p hp j hj hq fz1_118_22 fz2_118_22
  · exact match_zero_fix ⟨119, by decide⟩ ⟨22, by decide⟩ p hp j hj hq fz1_119_22 fz2_119_22
  · exact match_zero_fix ⟨120, by decide⟩ ⟨22, by decide⟩ p hp j hj hq fz1_120_22 fz2_120_22
  · exact match_zero_fix ⟨121, by decide⟩ ⟨22, by decide⟩ p hp j hj hq fz1_121_22 fz2_121_22
  · exact match_zero_fix ⟨122, by decide⟩ ⟨22, by decide⟩ p hp j hj hq fz1_122_22 fz2_122_22
  · exact match_zero_fix ⟨123, by decide⟩ ⟨22, by decide⟩ p hp j hj hq fz1_123_22 fz2_123_22
  · exact match_zero_fix ⟨124, by decide⟩ ⟨22, by decide⟩ p hp j hj hq fz1_124_22 fz2_124_22
  · exact match_zero_fix ⟨125, by decide⟩ ⟨22, by decide⟩ p hp j hj hq fz1_125_22 fz2_125_22
  · exact match_zero_fix ⟨126, by decide⟩ ⟨22, by decide⟩ p hp j hj hq fz1_126_22 fz2_126_22
  · exact match_zero_fix ⟨127, by decide⟩ ⟨22, by decide⟩ p hp j hj hq fz1_127_22 fz2_127_22
  · exact match_zero_fix ⟨128, by decide⟩ ⟨22, by decide⟩ p hp j hj hq fz1_128_22 fz2_128_22
  · exact match_zero_fix ⟨129, by decide⟩ ⟨22, by decide⟩ p hp j hj hq fz1_129_22 fz2_129_22
  · exact match_zero_fix ⟨130, by decide⟩ ⟨22, by decide⟩ p hp j hj hq fz1_130_22 fz2_130_22
  · exact pair_131_22 p hp hrep j hj hq
  · exact pair_132_22 p hp hrep j hj hq
  · exact pair_133_22 p hp hrep j hj hq
  · exact pair_134_22 p hp hrep j hj hq
  · exact pair_135_22 p hp hrep j hj hq
  · exact match_zero_fix ⟨136, by decide⟩ ⟨22, by decide⟩ p hp j hj hq fz1_136_22 fz2_136_22
  · exact match_zero_fix ⟨137, by decide⟩ ⟨22, by decide⟩ p hp j hj hq fz1_137_22 fz2_137_22
  · exact match_zero_fix ⟨138, by decide⟩ ⟨22, by decide⟩ p hp j hj hq fz1_138_22 fz2_138_22
  · exact match_zero_fix ⟨139, by decide⟩ ⟨22, by decide⟩ p hp j hj hq fz1_139_22 fz2_139_22
  · exact match_zero_fix ⟨140, by decide⟩ ⟨22, by decide⟩ p hp j hj hq fz1_140_22 fz2_140_22
  · exact pair_141_22 p hp hrep j hj hq
  · exact match_zero_fix ⟨142, by decide⟩ ⟨22, by decide⟩ p hp j hj hq fz1_142_22 fz2_142_22
  · exact match_zero_fix ⟨143, by decide⟩ ⟨22, by decide⟩ p hp j hj hq fz1_143_22 fz2_143_22
  · exact match_zero_fix ⟨144, by decide⟩ ⟨22, by decide⟩ p hp j hj hq fz1_144_22 fz2_144_22
  · exact match_zero_fix ⟨145, by decide⟩ ⟨22, by decide⟩ p hp j hj hq fz1_145_22 fz2_145_22
  · exact match_zero_fix ⟨146, by decide⟩ ⟨22, by decide⟩ p hp j hj hq fz1_146_22 fz2_146_22
  · exact pair_147_22 p hp hrep j hj hq

theorem master_23 (p : Nat) (hp : p < (Q2.transData.getD 23 []).length)
    (hrep : (Q2.cosetIsRep.getD 23 []).getD p false = true)
    (rK : Fin 148) (j : Nat) (hj : j < (repChars.getD rK.val []).length)
    (hq : (normIsRep.getD rK.val []).getD j false = true) :
    species (Q2.reps (⟨23, by decide⟩ : Fin 148)) (colE2 ⟨23, by decide⟩ p hp)
        (rowE2 rK j hj hq)
      = species (reps (⟨23, by decide⟩ : Fin 148))
        (colE1 ⟨23, by decide⟩ p (transLenTr ⟨23, by decide⟩ p hp)) (rowE1 rK j hj) := by
  rcases rK with ⟨nK, hnK⟩; interval_cases nK
  · exact match_zero_len ⟨0, by decide⟩ ⟨23, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨1, by decide⟩ ⟨23, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨2, by decide⟩ ⟨23, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨3, by decide⟩ ⟨23, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨4, by decide⟩ ⟨23, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨5, by decide⟩ ⟨23, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨6, by decide⟩ ⟨23, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨7, by decide⟩ ⟨23, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨8, by decide⟩ ⟨23, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨9, by decide⟩ ⟨23, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨10, by decide⟩ ⟨23, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨11, by decide⟩ ⟨23, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_len ⟨12, by decide⟩ ⟨23, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_fix ⟨13, by decide⟩ ⟨23, by decide⟩ p hp j hj hq fz1_13_23 fz2_13_23
  · exact match_zero_fix ⟨14, by decide⟩ ⟨23, by decide⟩ p hp j hj hq fz1_14_23 fz2_14_23
  · exact match_zero_fix ⟨15, by decide⟩ ⟨23, by decide⟩ p hp j hj hq fz1_15_23 fz2_15_23
  · exact match_zero_fix ⟨16, by decide⟩ ⟨23, by decide⟩ p hp j hj hq fz1_16_23 fz2_16_23
  · exact match_zero_fix ⟨17, by decide⟩ ⟨23, by decide⟩ p hp j hj hq fz1_17_23 fz2_17_23
  · exact match_zero_fix ⟨18, by decide⟩ ⟨23, by decide⟩ p hp j hj hq fz1_18_23 fz2_18_23
  · exact match_zero_fix ⟨19, by decide⟩ ⟨23, by decide⟩ p hp j hj hq fz1_19_23 fz2_19_23
  · exact match_zero_fix ⟨20, by decide⟩ ⟨23, by decide⟩ p hp j hj hq fz1_20_23 fz2_20_23
  · exact match_zero_fix ⟨21, by decide⟩ ⟨23, by decide⟩ p hp j hj hq fz1_21_23 fz2_21_23
  · exact match_zero_fix ⟨22, by decide⟩ ⟨23, by decide⟩ p hp j hj hq fz1_22_23 fz2_22_23
  · exact pair_23_23 p hp hrep j hj hq
  · exact match_zero_fix ⟨24, by decide⟩ ⟨23, by decide⟩ p hp j hj hq fz1_24_23 fz2_24_23
  · exact match_zero_fix ⟨25, by decide⟩ ⟨23, by decide⟩ p hp j hj hq fz1_25_23 fz2_25_23
  · exact match_zero_fix ⟨26, by decide⟩ ⟨23, by decide⟩ p hp j hj hq fz1_26_23 fz2_26_23
  · exact match_zero_fix ⟨27, by decide⟩ ⟨23, by decide⟩ p hp j hj hq fz1_27_23 fz2_27_23
  · exact match_zero_fix ⟨28, by decide⟩ ⟨23, by decide⟩ p hp j hj hq fz1_28_23 fz2_28_23
  · exact match_zero_fix ⟨29, by decide⟩ ⟨23, by decide⟩ p hp j hj hq fz1_29_23 fz2_29_23
  · exact match_zero_fix ⟨30, by decide⟩ ⟨23, by decide⟩ p hp j hj hq fz1_30_23 fz2_30_23
  · exact match_zero_fix ⟨31, by decide⟩ ⟨23, by decide⟩ p hp j hj hq fz1_31_23 fz2_31_23
  · exact match_zero_fix ⟨32, by decide⟩ ⟨23, by decide⟩ p hp j hj hq fz1_32_23 fz2_32_23
  · exact match_zero_fix ⟨33, by decide⟩ ⟨23, by decide⟩ p hp j hj hq fz1_33_23 fz2_33_23
  · exact match_zero_fix ⟨34, by decide⟩ ⟨23, by decide⟩ p hp j hj hq fz1_34_23 fz2_34_23
  · exact match_zero_fix ⟨35, by decide⟩ ⟨23, by decide⟩ p hp j hj hq fz1_35_23 fz2_35_23
  · exact match_zero_fix ⟨36, by decide⟩ ⟨23, by decide⟩ p hp j hj hq fz1_36_23 fz2_36_23
  · exact match_zero_fix ⟨37, by decide⟩ ⟨23, by decide⟩ p hp j hj hq fz1_37_23 fz2_37_23
  · exact match_zero_fix ⟨38, by decide⟩ ⟨23, by decide⟩ p hp j hj hq fz1_38_23 fz2_38_23
  · exact match_zero_fix ⟨39, by decide⟩ ⟨23, by decide⟩ p hp j hj hq fz1_39_23 fz2_39_23
  · exact match_zero_fix ⟨40, by decide⟩ ⟨23, by decide⟩ p hp j hj hq fz1_40_23 fz2_40_23
  · exact match_zero_fix ⟨41, by decide⟩ ⟨23, by decide⟩ p hp j hj hq fz1_41_23 fz2_41_23
  · exact match_zero_fix ⟨42, by decide⟩ ⟨23, by decide⟩ p hp j hj hq fz1_42_23 fz2_42_23
  · exact match_zero_fix ⟨43, by decide⟩ ⟨23, by decide⟩ p hp j hj hq fz1_43_23 fz2_43_23
  · exact match_zero_fix ⟨44, by decide⟩ ⟨23, by decide⟩ p hp j hj hq fz1_44_23 fz2_44_23
  · exact match_zero_fix ⟨45, by decide⟩ ⟨23, by decide⟩ p hp j hj hq fz1_45_23 fz2_45_23
  · exact match_zero_fix ⟨46, by decide⟩ ⟨23, by decide⟩ p hp j hj hq fz1_46_23 fz2_46_23
  · exact match_zero_fix ⟨47, by decide⟩ ⟨23, by decide⟩ p hp j hj hq fz1_47_23 fz2_47_23
  · exact match_zero_fix ⟨48, by decide⟩ ⟨23, by decide⟩ p hp j hj hq fz1_48_23 fz2_48_23
  · exact match_zero_fix ⟨49, by decide⟩ ⟨23, by decide⟩ p hp j hj hq fz1_49_23 fz2_49_23
  · exact match_zero_fix ⟨50, by decide⟩ ⟨23, by decide⟩ p hp j hj hq fz1_50_23 fz2_50_23
  · exact match_zero_fix ⟨51, by decide⟩ ⟨23, by decide⟩ p hp j hj hq fz1_51_23 fz2_51_23
  · exact match_zero_fix ⟨52, by decide⟩ ⟨23, by decide⟩ p hp j hj hq fz1_52_23 fz2_52_23
  · exact match_zero_fix ⟨53, by decide⟩ ⟨23, by decide⟩ p hp j hj hq fz1_53_23 fz2_53_23
  · exact match_zero_fix ⟨54, by decide⟩ ⟨23, by decide⟩ p hp j hj hq fz1_54_23 fz2_54_23
  · exact match_zero_fix ⟨55, by decide⟩ ⟨23, by decide⟩ p hp j hj hq fz1_55_23 fz2_55_23
  · exact match_zero_fix ⟨56, by decide⟩ ⟨23, by decide⟩ p hp j hj hq fz1_56_23 fz2_56_23
  · exact match_zero_fix ⟨57, by decide⟩ ⟨23, by decide⟩ p hp j hj hq fz1_57_23 fz2_57_23
  · exact match_zero_fix ⟨58, by decide⟩ ⟨23, by decide⟩ p hp j hj hq fz1_58_23 fz2_58_23
  · exact match_zero_fix ⟨59, by decide⟩ ⟨23, by decide⟩ p hp j hj hq fz1_59_23 fz2_59_23
  · exact match_zero_fix ⟨60, by decide⟩ ⟨23, by decide⟩ p hp j hj hq fz1_60_23 fz2_60_23
  · exact match_zero_fix ⟨61, by decide⟩ ⟨23, by decide⟩ p hp j hj hq fz1_61_23 fz2_61_23
  · exact match_zero_fix ⟨62, by decide⟩ ⟨23, by decide⟩ p hp j hj hq fz1_62_23 fz2_62_23
  · exact match_zero_fix ⟨63, by decide⟩ ⟨23, by decide⟩ p hp j hj hq fz1_63_23 fz2_63_23
  · exact match_zero_fix ⟨64, by decide⟩ ⟨23, by decide⟩ p hp j hj hq fz1_64_23 fz2_64_23
  · exact match_zero_fix ⟨65, by decide⟩ ⟨23, by decide⟩ p hp j hj hq fz1_65_23 fz2_65_23
  · exact match_zero_fix ⟨66, by decide⟩ ⟨23, by decide⟩ p hp j hj hq fz1_66_23 fz2_66_23
  · exact match_zero_fix ⟨67, by decide⟩ ⟨23, by decide⟩ p hp j hj hq fz1_67_23 fz2_67_23
  · exact match_zero_fix ⟨68, by decide⟩ ⟨23, by decide⟩ p hp j hj hq fz1_68_23 fz2_68_23
  · exact match_zero_fix ⟨69, by decide⟩ ⟨23, by decide⟩ p hp j hj hq fz1_69_23 fz2_69_23
  · exact match_zero_fix ⟨70, by decide⟩ ⟨23, by decide⟩ p hp j hj hq fz1_70_23 fz2_70_23
  · exact match_zero_fix ⟨71, by decide⟩ ⟨23, by decide⟩ p hp j hj hq fz1_71_23 fz2_71_23
  · exact match_zero_fix ⟨72, by decide⟩ ⟨23, by decide⟩ p hp j hj hq fz1_72_23 fz2_72_23
  · exact match_zero_fix ⟨73, by decide⟩ ⟨23, by decide⟩ p hp j hj hq fz1_73_23 fz2_73_23
  · exact match_zero_fix ⟨74, by decide⟩ ⟨23, by decide⟩ p hp j hj hq fz1_74_23 fz2_74_23
  · exact match_zero_fix ⟨75, by decide⟩ ⟨23, by decide⟩ p hp j hj hq fz1_75_23 fz2_75_23
  · exact match_zero_fix ⟨76, by decide⟩ ⟨23, by decide⟩ p hp j hj hq fz1_76_23 fz2_76_23
  · exact match_zero_fix ⟨77, by decide⟩ ⟨23, by decide⟩ p hp j hj hq fz1_77_23 fz2_77_23
  · exact match_zero_fix ⟨78, by decide⟩ ⟨23, by decide⟩ p hp j hj hq fz1_78_23 fz2_78_23
  · exact match_zero_fix ⟨79, by decide⟩ ⟨23, by decide⟩ p hp j hj hq fz1_79_23 fz2_79_23
  · exact match_zero_fix ⟨80, by decide⟩ ⟨23, by decide⟩ p hp j hj hq fz1_80_23 fz2_80_23
  · exact match_zero_fix ⟨81, by decide⟩ ⟨23, by decide⟩ p hp j hj hq fz1_81_23 fz2_81_23
  · exact match_zero_fix ⟨82, by decide⟩ ⟨23, by decide⟩ p hp j hj hq fz1_82_23 fz2_82_23
  · exact match_zero_fix ⟨83, by decide⟩ ⟨23, by decide⟩ p hp j hj hq fz1_83_23 fz2_83_23
  · exact pair_84_23 p hp hrep j hj hq
  · exact pair_85_23 p hp hrep j hj hq
  · exact pair_86_23 p hp hrep j hj hq
  · exact pair_87_23 p hp hrep j hj hq
  · exact pair_88_23 p hp hrep j hj hq
  · exact pair_89_23 p hp hrep j hj hq
  · exact match_zero_fix ⟨90, by decide⟩ ⟨23, by decide⟩ p hp j hj hq fz1_90_23 fz2_90_23
  · exact match_zero_fix ⟨91, by decide⟩ ⟨23, by decide⟩ p hp j hj hq fz1_91_23 fz2_91_23
  · exact match_zero_fix ⟨92, by decide⟩ ⟨23, by decide⟩ p hp j hj hq fz1_92_23 fz2_92_23
  · exact match_zero_fix ⟨93, by decide⟩ ⟨23, by decide⟩ p hp j hj hq fz1_93_23 fz2_93_23
  · exact match_zero_fix ⟨94, by decide⟩ ⟨23, by decide⟩ p hp j hj hq fz1_94_23 fz2_94_23
  · exact match_zero_fix ⟨95, by decide⟩ ⟨23, by decide⟩ p hp j hj hq fz1_95_23 fz2_95_23
  · exact match_zero_fix ⟨96, by decide⟩ ⟨23, by decide⟩ p hp j hj hq fz1_96_23 fz2_96_23
  · exact match_zero_fix ⟨97, by decide⟩ ⟨23, by decide⟩ p hp j hj hq fz1_97_23 fz2_97_23
  · exact match_zero_fix ⟨98, by decide⟩ ⟨23, by decide⟩ p hp j hj hq fz1_98_23 fz2_98_23
  · exact match_zero_fix ⟨99, by decide⟩ ⟨23, by decide⟩ p hp j hj hq fz1_99_23 fz2_99_23
  · exact match_zero_fix ⟨100, by decide⟩ ⟨23, by decide⟩ p hp j hj hq fz1_100_23 fz2_100_23
  · exact match_zero_fix ⟨101, by decide⟩ ⟨23, by decide⟩ p hp j hj hq fz1_101_23 fz2_101_23
  · exact match_zero_fix ⟨102, by decide⟩ ⟨23, by decide⟩ p hp j hj hq fz1_102_23 fz2_102_23
  · exact match_zero_fix ⟨103, by decide⟩ ⟨23, by decide⟩ p hp j hj hq fz1_103_23 fz2_103_23
  · exact match_zero_fix ⟨104, by decide⟩ ⟨23, by decide⟩ p hp j hj hq fz1_104_23 fz2_104_23
  · exact match_zero_fix ⟨105, by decide⟩ ⟨23, by decide⟩ p hp j hj hq fz1_105_23 fz2_105_23
  · exact match_zero_fix ⟨106, by decide⟩ ⟨23, by decide⟩ p hp j hj hq fz1_106_23 fz2_106_23
  · exact match_zero_fix ⟨107, by decide⟩ ⟨23, by decide⟩ p hp j hj hq fz1_107_23 fz2_107_23
  · exact match_zero_fix ⟨108, by decide⟩ ⟨23, by decide⟩ p hp j hj hq fz1_108_23 fz2_108_23
  · exact match_zero_fix ⟨109, by decide⟩ ⟨23, by decide⟩ p hp j hj hq fz1_109_23 fz2_109_23
  · exact match_zero_fix ⟨110, by decide⟩ ⟨23, by decide⟩ p hp j hj hq fz1_110_23 fz2_110_23
  · exact match_zero_fix ⟨111, by decide⟩ ⟨23, by decide⟩ p hp j hj hq fz1_111_23 fz2_111_23
  · exact match_zero_fix ⟨112, by decide⟩ ⟨23, by decide⟩ p hp j hj hq fz1_112_23 fz2_112_23
  · exact match_zero_fix ⟨113, by decide⟩ ⟨23, by decide⟩ p hp j hj hq fz1_113_23 fz2_113_23
  · exact match_zero_fix ⟨114, by decide⟩ ⟨23, by decide⟩ p hp j hj hq fz1_114_23 fz2_114_23
  · exact match_zero_fix ⟨115, by decide⟩ ⟨23, by decide⟩ p hp j hj hq fz1_115_23 fz2_115_23
  · exact match_zero_fix ⟨116, by decide⟩ ⟨23, by decide⟩ p hp j hj hq fz1_116_23 fz2_116_23
  · exact match_zero_fix ⟨117, by decide⟩ ⟨23, by decide⟩ p hp j hj hq fz1_117_23 fz2_117_23
  · exact match_zero_fix ⟨118, by decide⟩ ⟨23, by decide⟩ p hp j hj hq fz1_118_23 fz2_118_23
  · exact match_zero_fix ⟨119, by decide⟩ ⟨23, by decide⟩ p hp j hj hq fz1_119_23 fz2_119_23
  · exact match_zero_fix ⟨120, by decide⟩ ⟨23, by decide⟩ p hp j hj hq fz1_120_23 fz2_120_23
  · exact match_zero_fix ⟨121, by decide⟩ ⟨23, by decide⟩ p hp j hj hq fz1_121_23 fz2_121_23
  · exact match_zero_fix ⟨122, by decide⟩ ⟨23, by decide⟩ p hp j hj hq fz1_122_23 fz2_122_23
  · exact match_zero_fix ⟨123, by decide⟩ ⟨23, by decide⟩ p hp j hj hq fz1_123_23 fz2_123_23
  · exact match_zero_fix ⟨124, by decide⟩ ⟨23, by decide⟩ p hp j hj hq fz1_124_23 fz2_124_23
  · exact match_zero_fix ⟨125, by decide⟩ ⟨23, by decide⟩ p hp j hj hq fz1_125_23 fz2_125_23
  · exact match_zero_fix ⟨126, by decide⟩ ⟨23, by decide⟩ p hp j hj hq fz1_126_23 fz2_126_23
  · exact match_zero_fix ⟨127, by decide⟩ ⟨23, by decide⟩ p hp j hj hq fz1_127_23 fz2_127_23
  · exact match_zero_fix ⟨128, by decide⟩ ⟨23, by decide⟩ p hp j hj hq fz1_128_23 fz2_128_23
  · exact match_zero_fix ⟨129, by decide⟩ ⟨23, by decide⟩ p hp j hj hq fz1_129_23 fz2_129_23
  · exact match_zero_fix ⟨130, by decide⟩ ⟨23, by decide⟩ p hp j hj hq fz1_130_23 fz2_130_23
  · exact match_zero_fix ⟨131, by decide⟩ ⟨23, by decide⟩ p hp j hj hq fz1_131_23 fz2_131_23
  · exact match_zero_fix ⟨132, by decide⟩ ⟨23, by decide⟩ p hp j hj hq fz1_132_23 fz2_132_23
  · exact match_zero_fix ⟨133, by decide⟩ ⟨23, by decide⟩ p hp j hj hq fz1_133_23 fz2_133_23
  · exact match_zero_fix ⟨134, by decide⟩ ⟨23, by decide⟩ p hp j hj hq fz1_134_23 fz2_134_23
  · exact match_zero_fix ⟨135, by decide⟩ ⟨23, by decide⟩ p hp j hj hq fz1_135_23 fz2_135_23
  · exact pair_136_23 p hp hrep j hj hq
  · exact pair_137_23 p hp hrep j hj hq
  · exact pair_138_23 p hp hrep j hj hq
  · exact pair_139_23 p hp hrep j hj hq
  · exact pair_140_23 p hp hrep j hj hq
  · exact pair_141_23 p hp hrep j hj hq
  · exact match_zero_fix ⟨142, by decide⟩ ⟨23, by decide⟩ p hp j hj hq fz1_142_23 fz2_142_23
  · exact match_zero_fix ⟨143, by decide⟩ ⟨23, by decide⟩ p hp j hj hq fz1_143_23 fz2_143_23
  · exact match_zero_fix ⟨144, by decide⟩ ⟨23, by decide⟩ p hp j hj hq fz1_144_23 fz2_144_23
  · exact match_zero_fix ⟨145, by decide⟩ ⟨23, by decide⟩ p hp j hj hq fz1_145_23 fz2_145_23
  · exact match_zero_fix ⟨146, by decide⟩ ⟨23, by decide⟩ p hp j hj hq fz1_146_23 fz2_146_23
  · exact pair_147_23 p hp hrep j hj hq

end LeanDring.P5Presentation
