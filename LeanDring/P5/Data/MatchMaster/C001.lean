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
import LeanDring.P5.Data.MatchPair.C006
import LeanDring.P5.Data.MatchPair.C007
import LeanDring.P5.Data.MatchPair.C008
import LeanDring.P5.Data.MatchPair.C009
import LeanDring.P5.Data.MatchPair.C010

/-! # Stage-5 per-column-class master theorems, chunk 0 (auto-emitted).  -/

namespace LeanDring.P5Presentation

open MulAction Finset LeanDring.DRing LeanDring.MonGSet

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.style.longLine false

theorem master_0 (p : Nat) (hp : p < (Q2.transData.getD 0 []).length)
    (_hrep : (Q2.cosetIsRep.getD 0 []).getD p false = true)
    (rK : Fin 148) (j : Nat) (hj : j < (repChars.getD rK.val []).length)
    (hq : (normIsRep.getD rK.val []).getD j false = true) :
    species (Q2.reps (⟨0, by decide⟩ : Fin 148)) (colE2 ⟨0, by decide⟩ p hp) (rowE2 rK j hj hq)
      = species (reps (⟨0, by decide⟩ : Fin 148))
        (colE1 ⟨0, by decide⟩ p (transLenTr ⟨0, by decide⟩ p hp)) (rowE1 rK j hj) :=
  match_bot rK p hp j hj hq

theorem master_1 (p : Nat) (hp : p < (Q2.transData.getD 1 []).length)
    (hrep : (Q2.cosetIsRep.getD 1 []).getD p false = true)
    (rK : Fin 148) (j : Nat) (hj : j < (repChars.getD rK.val []).length)
    (hq : (normIsRep.getD rK.val []).getD j false = true) :
    species (Q2.reps (⟨1, by decide⟩ : Fin 148)) (colE2 ⟨1, by decide⟩ p hp)
        (rowE2 rK j hj hq)
      = species (reps (⟨1, by decide⟩ : Fin 148))
        (colE1 ⟨1, by decide⟩ p (transLenTr ⟨1, by decide⟩ p hp)) (rowE1 rK j hj) := by
  rcases rK with ⟨nK, hnK⟩; interval_cases nK
  · exact match_zero_len ⟨0, by decide⟩ ⟨1, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact pair_1_1 p hp hrep j hj hq
  · exact match_zero_fix ⟨2, by decide⟩ ⟨1, by decide⟩ p hp j hj hq fz1_2_1 fz2_2_1
  · exact match_zero_fix ⟨3, by decide⟩ ⟨1, by decide⟩ p hp j hj hq fz1_3_1 fz2_3_1
  · exact match_zero_fix ⟨4, by decide⟩ ⟨1, by decide⟩ p hp j hj hq fz1_4_1 fz2_4_1
  · exact match_zero_fix ⟨5, by decide⟩ ⟨1, by decide⟩ p hp j hj hq fz1_5_1 fz2_5_1
  · exact match_zero_fix ⟨6, by decide⟩ ⟨1, by decide⟩ p hp j hj hq fz1_6_1 fz2_6_1
  · exact match_zero_fix ⟨7, by decide⟩ ⟨1, by decide⟩ p hp j hj hq fz1_7_1 fz2_7_1
  · exact match_zero_fix ⟨8, by decide⟩ ⟨1, by decide⟩ p hp j hj hq fz1_8_1 fz2_8_1
  · exact match_zero_fix ⟨9, by decide⟩ ⟨1, by decide⟩ p hp j hj hq fz1_9_1 fz2_9_1
  · exact match_zero_fix ⟨10, by decide⟩ ⟨1, by decide⟩ p hp j hj hq fz1_10_1 fz2_10_1
  · exact match_zero_fix ⟨11, by decide⟩ ⟨1, by decide⟩ p hp j hj hq fz1_11_1 fz2_11_1
  · exact match_zero_fix ⟨12, by decide⟩ ⟨1, by decide⟩ p hp j hj hq fz1_12_1 fz2_12_1
  · exact pair_13_1 p hp hrep j hj hq
  · exact match_zero_fix ⟨14, by decide⟩ ⟨1, by decide⟩ p hp j hj hq fz1_14_1 fz2_14_1
  · exact match_zero_fix ⟨15, by decide⟩ ⟨1, by decide⟩ p hp j hj hq fz1_15_1 fz2_15_1
  · exact match_zero_fix ⟨16, by decide⟩ ⟨1, by decide⟩ p hp j hj hq fz1_16_1 fz2_16_1
  · exact match_zero_fix ⟨17, by decide⟩ ⟨1, by decide⟩ p hp j hj hq fz1_17_1 fz2_17_1
  · exact match_zero_fix ⟨18, by decide⟩ ⟨1, by decide⟩ p hp j hj hq fz1_18_1 fz2_18_1
  · exact pair_19_1 p hp hrep j hj hq
  · exact match_zero_fix ⟨20, by decide⟩ ⟨1, by decide⟩ p hp j hj hq fz1_20_1 fz2_20_1
  · exact match_zero_fix ⟨21, by decide⟩ ⟨1, by decide⟩ p hp j hj hq fz1_21_1 fz2_21_1
  · exact match_zero_fix ⟨22, by decide⟩ ⟨1, by decide⟩ p hp j hj hq fz1_22_1 fz2_22_1
  · exact match_zero_fix ⟨23, by decide⟩ ⟨1, by decide⟩ p hp j hj hq fz1_23_1 fz2_23_1
  · exact match_zero_fix ⟨24, by decide⟩ ⟨1, by decide⟩ p hp j hj hq fz1_24_1 fz2_24_1
  · exact match_zero_fix ⟨25, by decide⟩ ⟨1, by decide⟩ p hp j hj hq fz1_25_1 fz2_25_1
  · exact match_zero_fix ⟨26, by decide⟩ ⟨1, by decide⟩ p hp j hj hq fz1_26_1 fz2_26_1
  · exact match_zero_fix ⟨27, by decide⟩ ⟨1, by decide⟩ p hp j hj hq fz1_27_1 fz2_27_1
  · exact match_zero_fix ⟨28, by decide⟩ ⟨1, by decide⟩ p hp j hj hq fz1_28_1 fz2_28_1
  · exact match_zero_fix ⟨29, by decide⟩ ⟨1, by decide⟩ p hp j hj hq fz1_29_1 fz2_29_1
  · exact match_zero_fix ⟨30, by decide⟩ ⟨1, by decide⟩ p hp j hj hq fz1_30_1 fz2_30_1
  · exact match_zero_fix ⟨31, by decide⟩ ⟨1, by decide⟩ p hp j hj hq fz1_31_1 fz2_31_1
  · exact match_zero_fix ⟨32, by decide⟩ ⟨1, by decide⟩ p hp j hj hq fz1_32_1 fz2_32_1
  · exact match_zero_fix ⟨33, by decide⟩ ⟨1, by decide⟩ p hp j hj hq fz1_33_1 fz2_33_1
  · exact match_zero_fix ⟨34, by decide⟩ ⟨1, by decide⟩ p hp j hj hq fz1_34_1 fz2_34_1
  · exact match_zero_fix ⟨35, by decide⟩ ⟨1, by decide⟩ p hp j hj hq fz1_35_1 fz2_35_1
  · exact match_zero_fix ⟨36, by decide⟩ ⟨1, by decide⟩ p hp j hj hq fz1_36_1 fz2_36_1
  · exact match_zero_fix ⟨37, by decide⟩ ⟨1, by decide⟩ p hp j hj hq fz1_37_1 fz2_37_1
  · exact match_zero_fix ⟨38, by decide⟩ ⟨1, by decide⟩ p hp j hj hq fz1_38_1 fz2_38_1
  · exact match_zero_fix ⟨39, by decide⟩ ⟨1, by decide⟩ p hp j hj hq fz1_39_1 fz2_39_1
  · exact match_zero_fix ⟨40, by decide⟩ ⟨1, by decide⟩ p hp j hj hq fz1_40_1 fz2_40_1
  · exact match_zero_fix ⟨41, by decide⟩ ⟨1, by decide⟩ p hp j hj hq fz1_41_1 fz2_41_1
  · exact match_zero_fix ⟨42, by decide⟩ ⟨1, by decide⟩ p hp j hj hq fz1_42_1 fz2_42_1
  · exact match_zero_fix ⟨43, by decide⟩ ⟨1, by decide⟩ p hp j hj hq fz1_43_1 fz2_43_1
  · exact match_zero_fix ⟨44, by decide⟩ ⟨1, by decide⟩ p hp j hj hq fz1_44_1 fz2_44_1
  · exact match_zero_fix ⟨45, by decide⟩ ⟨1, by decide⟩ p hp j hj hq fz1_45_1 fz2_45_1
  · exact match_zero_fix ⟨46, by decide⟩ ⟨1, by decide⟩ p hp j hj hq fz1_46_1 fz2_46_1
  · exact match_zero_fix ⟨47, by decide⟩ ⟨1, by decide⟩ p hp j hj hq fz1_47_1 fz2_47_1
  · exact match_zero_fix ⟨48, by decide⟩ ⟨1, by decide⟩ p hp j hj hq fz1_48_1 fz2_48_1
  · exact match_zero_fix ⟨49, by decide⟩ ⟨1, by decide⟩ p hp j hj hq fz1_49_1 fz2_49_1
  · exact match_zero_fix ⟨50, by decide⟩ ⟨1, by decide⟩ p hp j hj hq fz1_50_1 fz2_50_1
  · exact match_zero_fix ⟨51, by decide⟩ ⟨1, by decide⟩ p hp j hj hq fz1_51_1 fz2_51_1
  · exact match_zero_fix ⟨52, by decide⟩ ⟨1, by decide⟩ p hp j hj hq fz1_52_1 fz2_52_1
  · exact match_zero_fix ⟨53, by decide⟩ ⟨1, by decide⟩ p hp j hj hq fz1_53_1 fz2_53_1
  · exact match_zero_fix ⟨54, by decide⟩ ⟨1, by decide⟩ p hp j hj hq fz1_54_1 fz2_54_1
  · exact match_zero_fix ⟨55, by decide⟩ ⟨1, by decide⟩ p hp j hj hq fz1_55_1 fz2_55_1
  · exact pair_56_1 p hp hrep j hj hq
  · exact match_zero_fix ⟨57, by decide⟩ ⟨1, by decide⟩ p hp j hj hq fz1_57_1 fz2_57_1
  · exact match_zero_fix ⟨58, by decide⟩ ⟨1, by decide⟩ p hp j hj hq fz1_58_1 fz2_58_1
  · exact match_zero_fix ⟨59, by decide⟩ ⟨1, by decide⟩ p hp j hj hq fz1_59_1 fz2_59_1
  · exact match_zero_fix ⟨60, by decide⟩ ⟨1, by decide⟩ p hp j hj hq fz1_60_1 fz2_60_1
  · exact pair_61_1 p hp hrep j hj hq
  · exact match_zero_fix ⟨62, by decide⟩ ⟨1, by decide⟩ p hp j hj hq fz1_62_1 fz2_62_1
  · exact match_zero_fix ⟨63, by decide⟩ ⟨1, by decide⟩ p hp j hj hq fz1_63_1 fz2_63_1
  · exact match_zero_fix ⟨64, by decide⟩ ⟨1, by decide⟩ p hp j hj hq fz1_64_1 fz2_64_1
  · exact match_zero_fix ⟨65, by decide⟩ ⟨1, by decide⟩ p hp j hj hq fz1_65_1 fz2_65_1
  · exact pair_66_1 p hp hrep j hj hq
  · exact match_zero_fix ⟨67, by decide⟩ ⟨1, by decide⟩ p hp j hj hq fz1_67_1 fz2_67_1
  · exact match_zero_fix ⟨68, by decide⟩ ⟨1, by decide⟩ p hp j hj hq fz1_68_1 fz2_68_1
  · exact match_zero_fix ⟨69, by decide⟩ ⟨1, by decide⟩ p hp j hj hq fz1_69_1 fz2_69_1
  · exact match_zero_fix ⟨70, by decide⟩ ⟨1, by decide⟩ p hp j hj hq fz1_70_1 fz2_70_1
  · exact pair_71_1 p hp hrep j hj hq
  · exact match_zero_fix ⟨72, by decide⟩ ⟨1, by decide⟩ p hp j hj hq fz1_72_1 fz2_72_1
  · exact match_zero_fix ⟨73, by decide⟩ ⟨1, by decide⟩ p hp j hj hq fz1_73_1 fz2_73_1
  · exact match_zero_fix ⟨74, by decide⟩ ⟨1, by decide⟩ p hp j hj hq fz1_74_1 fz2_74_1
  · exact match_zero_fix ⟨75, by decide⟩ ⟨1, by decide⟩ p hp j hj hq fz1_75_1 fz2_75_1
  · exact pair_76_1 p hp hrep j hj hq
  · exact match_zero_fix ⟨77, by decide⟩ ⟨1, by decide⟩ p hp j hj hq fz1_77_1 fz2_77_1
  · exact match_zero_fix ⟨78, by decide⟩ ⟨1, by decide⟩ p hp j hj hq fz1_78_1 fz2_78_1
  · exact match_zero_fix ⟨79, by decide⟩ ⟨1, by decide⟩ p hp j hj hq fz1_79_1 fz2_79_1
  · exact pair_80_1 p hp hrep j hj hq
  · exact match_zero_fix ⟨81, by decide⟩ ⟨1, by decide⟩ p hp j hj hq fz1_81_1 fz2_81_1
  · exact match_zero_fix ⟨82, by decide⟩ ⟨1, by decide⟩ p hp j hj hq fz1_82_1 fz2_82_1
  · exact match_zero_fix ⟨83, by decide⟩ ⟨1, by decide⟩ p hp j hj hq fz1_83_1 fz2_83_1
  · exact match_zero_fix ⟨84, by decide⟩ ⟨1, by decide⟩ p hp j hj hq fz1_84_1 fz2_84_1
  · exact match_zero_fix ⟨85, by decide⟩ ⟨1, by decide⟩ p hp j hj hq fz1_85_1 fz2_85_1
  · exact pair_86_1 p hp hrep j hj hq
  · exact match_zero_fix ⟨87, by decide⟩ ⟨1, by decide⟩ p hp j hj hq fz1_87_1 fz2_87_1
  · exact match_zero_fix ⟨88, by decide⟩ ⟨1, by decide⟩ p hp j hj hq fz1_88_1 fz2_88_1
  · exact match_zero_fix ⟨89, by decide⟩ ⟨1, by decide⟩ p hp j hj hq fz1_89_1 fz2_89_1
  · exact match_zero_fix ⟨90, by decide⟩ ⟨1, by decide⟩ p hp j hj hq fz1_90_1 fz2_90_1
  · exact match_zero_fix ⟨91, by decide⟩ ⟨1, by decide⟩ p hp j hj hq fz1_91_1 fz2_91_1
  · exact match_zero_fix ⟨92, by decide⟩ ⟨1, by decide⟩ p hp j hj hq fz1_92_1 fz2_92_1
  · exact match_zero_fix ⟨93, by decide⟩ ⟨1, by decide⟩ p hp j hj hq fz1_93_1 fz2_93_1
  · exact match_zero_fix ⟨94, by decide⟩ ⟨1, by decide⟩ p hp j hj hq fz1_94_1 fz2_94_1
  · exact match_zero_fix ⟨95, by decide⟩ ⟨1, by decide⟩ p hp j hj hq fz1_95_1 fz2_95_1
  · exact match_zero_fix ⟨96, by decide⟩ ⟨1, by decide⟩ p hp j hj hq fz1_96_1 fz2_96_1
  · exact match_zero_fix ⟨97, by decide⟩ ⟨1, by decide⟩ p hp j hj hq fz1_97_1 fz2_97_1
  · exact match_zero_fix ⟨98, by decide⟩ ⟨1, by decide⟩ p hp j hj hq fz1_98_1 fz2_98_1
  · exact match_zero_fix ⟨99, by decide⟩ ⟨1, by decide⟩ p hp j hj hq fz1_99_1 fz2_99_1
  · exact match_zero_fix ⟨100, by decide⟩ ⟨1, by decide⟩ p hp j hj hq fz1_100_1 fz2_100_1
  · exact match_zero_fix ⟨101, by decide⟩ ⟨1, by decide⟩ p hp j hj hq fz1_101_1 fz2_101_1
  · exact match_zero_fix ⟨102, by decide⟩ ⟨1, by decide⟩ p hp j hj hq fz1_102_1 fz2_102_1
  · exact match_zero_fix ⟨103, by decide⟩ ⟨1, by decide⟩ p hp j hj hq fz1_103_1 fz2_103_1
  · exact match_zero_fix ⟨104, by decide⟩ ⟨1, by decide⟩ p hp j hj hq fz1_104_1 fz2_104_1
  · exact match_zero_fix ⟨105, by decide⟩ ⟨1, by decide⟩ p hp j hj hq fz1_105_1 fz2_105_1
  · exact match_zero_fix ⟨106, by decide⟩ ⟨1, by decide⟩ p hp j hj hq fz1_106_1 fz2_106_1
  · exact match_zero_fix ⟨107, by decide⟩ ⟨1, by decide⟩ p hp j hj hq fz1_107_1 fz2_107_1
  · exact match_zero_fix ⟨108, by decide⟩ ⟨1, by decide⟩ p hp j hj hq fz1_108_1 fz2_108_1
  · exact match_zero_fix ⟨109, by decide⟩ ⟨1, by decide⟩ p hp j hj hq fz1_109_1 fz2_109_1
  · exact match_zero_fix ⟨110, by decide⟩ ⟨1, by decide⟩ p hp j hj hq fz1_110_1 fz2_110_1
  · exact match_zero_fix ⟨111, by decide⟩ ⟨1, by decide⟩ p hp j hj hq fz1_111_1 fz2_111_1
  · exact match_zero_fix ⟨112, by decide⟩ ⟨1, by decide⟩ p hp j hj hq fz1_112_1 fz2_112_1
  · exact match_zero_fix ⟨113, by decide⟩ ⟨1, by decide⟩ p hp j hj hq fz1_113_1 fz2_113_1
  · exact match_zero_fix ⟨114, by decide⟩ ⟨1, by decide⟩ p hp j hj hq fz1_114_1 fz2_114_1
  · exact match_zero_fix ⟨115, by decide⟩ ⟨1, by decide⟩ p hp j hj hq fz1_115_1 fz2_115_1
  · exact pair_116_1 p hp hrep j hj hq
  · exact pair_117_1 p hp hrep j hj hq
  · exact pair_118_1 p hp hrep j hj hq
  · exact pair_119_1 p hp hrep j hj hq
  · exact pair_120_1 p hp hrep j hj hq
  · exact match_zero_fix ⟨121, by decide⟩ ⟨1, by decide⟩ p hp j hj hq fz1_121_1 fz2_121_1
  · exact match_zero_fix ⟨122, by decide⟩ ⟨1, by decide⟩ p hp j hj hq fz1_122_1 fz2_122_1
  · exact match_zero_fix ⟨123, by decide⟩ ⟨1, by decide⟩ p hp j hj hq fz1_123_1 fz2_123_1
  · exact match_zero_fix ⟨124, by decide⟩ ⟨1, by decide⟩ p hp j hj hq fz1_124_1 fz2_124_1
  · exact match_zero_fix ⟨125, by decide⟩ ⟨1, by decide⟩ p hp j hj hq fz1_125_1 fz2_125_1
  · exact match_zero_fix ⟨126, by decide⟩ ⟨1, by decide⟩ p hp j hj hq fz1_126_1 fz2_126_1
  · exact match_zero_fix ⟨127, by decide⟩ ⟨1, by decide⟩ p hp j hj hq fz1_127_1 fz2_127_1
  · exact match_zero_fix ⟨128, by decide⟩ ⟨1, by decide⟩ p hp j hj hq fz1_128_1 fz2_128_1
  · exact match_zero_fix ⟨129, by decide⟩ ⟨1, by decide⟩ p hp j hj hq fz1_129_1 fz2_129_1
  · exact match_zero_fix ⟨130, by decide⟩ ⟨1, by decide⟩ p hp j hj hq fz1_130_1 fz2_130_1
  · exact match_zero_fix ⟨131, by decide⟩ ⟨1, by decide⟩ p hp j hj hq fz1_131_1 fz2_131_1
  · exact match_zero_fix ⟨132, by decide⟩ ⟨1, by decide⟩ p hp j hj hq fz1_132_1 fz2_132_1
  · exact match_zero_fix ⟨133, by decide⟩ ⟨1, by decide⟩ p hp j hj hq fz1_133_1 fz2_133_1
  · exact match_zero_fix ⟨134, by decide⟩ ⟨1, by decide⟩ p hp j hj hq fz1_134_1 fz2_134_1
  · exact match_zero_fix ⟨135, by decide⟩ ⟨1, by decide⟩ p hp j hj hq fz1_135_1 fz2_135_1
  · exact match_zero_fix ⟨136, by decide⟩ ⟨1, by decide⟩ p hp j hj hq fz1_136_1 fz2_136_1
  · exact match_zero_fix ⟨137, by decide⟩ ⟨1, by decide⟩ p hp j hj hq fz1_137_1 fz2_137_1
  · exact match_zero_fix ⟨138, by decide⟩ ⟨1, by decide⟩ p hp j hj hq fz1_138_1 fz2_138_1
  · exact match_zero_fix ⟨139, by decide⟩ ⟨1, by decide⟩ p hp j hj hq fz1_139_1 fz2_139_1
  · exact match_zero_fix ⟨140, by decide⟩ ⟨1, by decide⟩ p hp j hj hq fz1_140_1 fz2_140_1
  · exact pair_141_1 p hp hrep j hj hq
  · exact match_zero_fix ⟨142, by decide⟩ ⟨1, by decide⟩ p hp j hj hq fz1_142_1 fz2_142_1
  · exact match_zero_fix ⟨143, by decide⟩ ⟨1, by decide⟩ p hp j hj hq fz1_143_1 fz2_143_1
  · exact match_zero_fix ⟨144, by decide⟩ ⟨1, by decide⟩ p hp j hj hq fz1_144_1 fz2_144_1
  · exact match_zero_fix ⟨145, by decide⟩ ⟨1, by decide⟩ p hp j hj hq fz1_145_1 fz2_145_1
  · exact match_zero_fix ⟨146, by decide⟩ ⟨1, by decide⟩ p hp j hj hq fz1_146_1 fz2_146_1
  · exact pair_147_1 p hp hrep j hj hq

theorem master_2 (p : Nat) (hp : p < (Q2.transData.getD 2 []).length)
    (hrep : (Q2.cosetIsRep.getD 2 []).getD p false = true)
    (rK : Fin 148) (j : Nat) (hj : j < (repChars.getD rK.val []).length)
    (hq : (normIsRep.getD rK.val []).getD j false = true) :
    species (Q2.reps (⟨2, by decide⟩ : Fin 148)) (colE2 ⟨2, by decide⟩ p hp)
        (rowE2 rK j hj hq)
      = species (reps (⟨2, by decide⟩ : Fin 148))
        (colE1 ⟨2, by decide⟩ p (transLenTr ⟨2, by decide⟩ p hp)) (rowE1 rK j hj) := by
  rcases rK with ⟨nK, hnK⟩; interval_cases nK
  · exact match_zero_len ⟨0, by decide⟩ ⟨2, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_fix ⟨1, by decide⟩ ⟨2, by decide⟩ p hp j hj hq fz1_1_2 fz2_1_2
  · exact pair_2_2 p hp hrep j hj hq
  · exact match_zero_fix ⟨3, by decide⟩ ⟨2, by decide⟩ p hp j hj hq fz1_3_2 fz2_3_2
  · exact match_zero_fix ⟨4, by decide⟩ ⟨2, by decide⟩ p hp j hj hq fz1_4_2 fz2_4_2
  · exact match_zero_fix ⟨5, by decide⟩ ⟨2, by decide⟩ p hp j hj hq fz1_5_2 fz2_5_2
  · exact match_zero_fix ⟨6, by decide⟩ ⟨2, by decide⟩ p hp j hj hq fz1_6_2 fz2_6_2
  · exact match_zero_fix ⟨7, by decide⟩ ⟨2, by decide⟩ p hp j hj hq fz1_7_2 fz2_7_2
  · exact match_zero_fix ⟨8, by decide⟩ ⟨2, by decide⟩ p hp j hj hq fz1_8_2 fz2_8_2
  · exact match_zero_fix ⟨9, by decide⟩ ⟨2, by decide⟩ p hp j hj hq fz1_9_2 fz2_9_2
  · exact match_zero_fix ⟨10, by decide⟩ ⟨2, by decide⟩ p hp j hj hq fz1_10_2 fz2_10_2
  · exact match_zero_fix ⟨11, by decide⟩ ⟨2, by decide⟩ p hp j hj hq fz1_11_2 fz2_11_2
  · exact match_zero_fix ⟨12, by decide⟩ ⟨2, by decide⟩ p hp j hj hq fz1_12_2 fz2_12_2
  · exact match_zero_fix ⟨13, by decide⟩ ⟨2, by decide⟩ p hp j hj hq fz1_13_2 fz2_13_2
  · exact pair_14_2 p hp hrep j hj hq
  · exact pair_15_2 p hp hrep j hj hq
  · exact pair_16_2 p hp hrep j hj hq
  · exact pair_17_2 p hp hrep j hj hq
  · exact pair_18_2 p hp hrep j hj hq
  · exact match_zero_fix ⟨19, by decide⟩ ⟨2, by decide⟩ p hp j hj hq fz1_19_2 fz2_19_2
  · exact pair_20_2 p hp hrep j hj hq
  · exact match_zero_fix ⟨21, by decide⟩ ⟨2, by decide⟩ p hp j hj hq fz1_21_2 fz2_21_2
  · exact match_zero_fix ⟨22, by decide⟩ ⟨2, by decide⟩ p hp j hj hq fz1_22_2 fz2_22_2
  · exact match_zero_fix ⟨23, by decide⟩ ⟨2, by decide⟩ p hp j hj hq fz1_23_2 fz2_23_2
  · exact match_zero_fix ⟨24, by decide⟩ ⟨2, by decide⟩ p hp j hj hq fz1_24_2 fz2_24_2
  · exact match_zero_fix ⟨25, by decide⟩ ⟨2, by decide⟩ p hp j hj hq fz1_25_2 fz2_25_2
  · exact match_zero_fix ⟨26, by decide⟩ ⟨2, by decide⟩ p hp j hj hq fz1_26_2 fz2_26_2
  · exact match_zero_fix ⟨27, by decide⟩ ⟨2, by decide⟩ p hp j hj hq fz1_27_2 fz2_27_2
  · exact match_zero_fix ⟨28, by decide⟩ ⟨2, by decide⟩ p hp j hj hq fz1_28_2 fz2_28_2
  · exact match_zero_fix ⟨29, by decide⟩ ⟨2, by decide⟩ p hp j hj hq fz1_29_2 fz2_29_2
  · exact match_zero_fix ⟨30, by decide⟩ ⟨2, by decide⟩ p hp j hj hq fz1_30_2 fz2_30_2
  · exact match_zero_fix ⟨31, by decide⟩ ⟨2, by decide⟩ p hp j hj hq fz1_31_2 fz2_31_2
  · exact match_zero_fix ⟨32, by decide⟩ ⟨2, by decide⟩ p hp j hj hq fz1_32_2 fz2_32_2
  · exact match_zero_fix ⟨33, by decide⟩ ⟨2, by decide⟩ p hp j hj hq fz1_33_2 fz2_33_2
  · exact match_zero_fix ⟨34, by decide⟩ ⟨2, by decide⟩ p hp j hj hq fz1_34_2 fz2_34_2
  · exact match_zero_fix ⟨35, by decide⟩ ⟨2, by decide⟩ p hp j hj hq fz1_35_2 fz2_35_2
  · exact match_zero_fix ⟨36, by decide⟩ ⟨2, by decide⟩ p hp j hj hq fz1_36_2 fz2_36_2
  · exact match_zero_fix ⟨37, by decide⟩ ⟨2, by decide⟩ p hp j hj hq fz1_37_2 fz2_37_2
  · exact match_zero_fix ⟨38, by decide⟩ ⟨2, by decide⟩ p hp j hj hq fz1_38_2 fz2_38_2
  · exact match_zero_fix ⟨39, by decide⟩ ⟨2, by decide⟩ p hp j hj hq fz1_39_2 fz2_39_2
  · exact match_zero_fix ⟨40, by decide⟩ ⟨2, by decide⟩ p hp j hj hq fz1_40_2 fz2_40_2
  · exact match_zero_fix ⟨41, by decide⟩ ⟨2, by decide⟩ p hp j hj hq fz1_41_2 fz2_41_2
  · exact match_zero_fix ⟨42, by decide⟩ ⟨2, by decide⟩ p hp j hj hq fz1_42_2 fz2_42_2
  · exact match_zero_fix ⟨43, by decide⟩ ⟨2, by decide⟩ p hp j hj hq fz1_43_2 fz2_43_2
  · exact match_zero_fix ⟨44, by decide⟩ ⟨2, by decide⟩ p hp j hj hq fz1_44_2 fz2_44_2
  · exact match_zero_fix ⟨45, by decide⟩ ⟨2, by decide⟩ p hp j hj hq fz1_45_2 fz2_45_2
  · exact match_zero_fix ⟨46, by decide⟩ ⟨2, by decide⟩ p hp j hj hq fz1_46_2 fz2_46_2
  · exact match_zero_fix ⟨47, by decide⟩ ⟨2, by decide⟩ p hp j hj hq fz1_47_2 fz2_47_2
  · exact match_zero_fix ⟨48, by decide⟩ ⟨2, by decide⟩ p hp j hj hq fz1_48_2 fz2_48_2
  · exact match_zero_fix ⟨49, by decide⟩ ⟨2, by decide⟩ p hp j hj hq fz1_49_2 fz2_49_2
  · exact match_zero_fix ⟨50, by decide⟩ ⟨2, by decide⟩ p hp j hj hq fz1_50_2 fz2_50_2
  · exact match_zero_fix ⟨51, by decide⟩ ⟨2, by decide⟩ p hp j hj hq fz1_51_2 fz2_51_2
  · exact match_zero_fix ⟨52, by decide⟩ ⟨2, by decide⟩ p hp j hj hq fz1_52_2 fz2_52_2
  · exact match_zero_fix ⟨53, by decide⟩ ⟨2, by decide⟩ p hp j hj hq fz1_53_2 fz2_53_2
  · exact match_zero_fix ⟨54, by decide⟩ ⟨2, by decide⟩ p hp j hj hq fz1_54_2 fz2_54_2
  · exact match_zero_fix ⟨55, by decide⟩ ⟨2, by decide⟩ p hp j hj hq fz1_55_2 fz2_55_2
  · exact match_zero_fix ⟨56, by decide⟩ ⟨2, by decide⟩ p hp j hj hq fz1_56_2 fz2_56_2
  · exact match_zero_fix ⟨57, by decide⟩ ⟨2, by decide⟩ p hp j hj hq fz1_57_2 fz2_57_2
  · exact match_zero_fix ⟨58, by decide⟩ ⟨2, by decide⟩ p hp j hj hq fz1_58_2 fz2_58_2
  · exact match_zero_fix ⟨59, by decide⟩ ⟨2, by decide⟩ p hp j hj hq fz1_59_2 fz2_59_2
  · exact match_zero_fix ⟨60, by decide⟩ ⟨2, by decide⟩ p hp j hj hq fz1_60_2 fz2_60_2
  · exact match_zero_fix ⟨61, by decide⟩ ⟨2, by decide⟩ p hp j hj hq fz1_61_2 fz2_61_2
  · exact match_zero_fix ⟨62, by decide⟩ ⟨2, by decide⟩ p hp j hj hq fz1_62_2 fz2_62_2
  · exact match_zero_fix ⟨63, by decide⟩ ⟨2, by decide⟩ p hp j hj hq fz1_63_2 fz2_63_2
  · exact match_zero_fix ⟨64, by decide⟩ ⟨2, by decide⟩ p hp j hj hq fz1_64_2 fz2_64_2
  · exact match_zero_fix ⟨65, by decide⟩ ⟨2, by decide⟩ p hp j hj hq fz1_65_2 fz2_65_2
  · exact match_zero_fix ⟨66, by decide⟩ ⟨2, by decide⟩ p hp j hj hq fz1_66_2 fz2_66_2
  · exact match_zero_fix ⟨67, by decide⟩ ⟨2, by decide⟩ p hp j hj hq fz1_67_2 fz2_67_2
  · exact match_zero_fix ⟨68, by decide⟩ ⟨2, by decide⟩ p hp j hj hq fz1_68_2 fz2_68_2
  · exact match_zero_fix ⟨69, by decide⟩ ⟨2, by decide⟩ p hp j hj hq fz1_69_2 fz2_69_2
  · exact match_zero_fix ⟨70, by decide⟩ ⟨2, by decide⟩ p hp j hj hq fz1_70_2 fz2_70_2
  · exact match_zero_fix ⟨71, by decide⟩ ⟨2, by decide⟩ p hp j hj hq fz1_71_2 fz2_71_2
  · exact match_zero_fix ⟨72, by decide⟩ ⟨2, by decide⟩ p hp j hj hq fz1_72_2 fz2_72_2
  · exact match_zero_fix ⟨73, by decide⟩ ⟨2, by decide⟩ p hp j hj hq fz1_73_2 fz2_73_2
  · exact match_zero_fix ⟨74, by decide⟩ ⟨2, by decide⟩ p hp j hj hq fz1_74_2 fz2_74_2
  · exact match_zero_fix ⟨75, by decide⟩ ⟨2, by decide⟩ p hp j hj hq fz1_75_2 fz2_75_2
  · exact match_zero_fix ⟨76, by decide⟩ ⟨2, by decide⟩ p hp j hj hq fz1_76_2 fz2_76_2
  · exact match_zero_fix ⟨77, by decide⟩ ⟨2, by decide⟩ p hp j hj hq fz1_77_2 fz2_77_2
  · exact match_zero_fix ⟨78, by decide⟩ ⟨2, by decide⟩ p hp j hj hq fz1_78_2 fz2_78_2
  · exact match_zero_fix ⟨79, by decide⟩ ⟨2, by decide⟩ p hp j hj hq fz1_79_2 fz2_79_2
  · exact match_zero_fix ⟨80, by decide⟩ ⟨2, by decide⟩ p hp j hj hq fz1_80_2 fz2_80_2
  · exact pair_81_2 p hp hrep j hj hq
  · exact match_zero_fix ⟨82, by decide⟩ ⟨2, by decide⟩ p hp j hj hq fz1_82_2 fz2_82_2
  · exact match_zero_fix ⟨83, by decide⟩ ⟨2, by decide⟩ p hp j hj hq fz1_83_2 fz2_83_2
  · exact match_zero_fix ⟨84, by decide⟩ ⟨2, by decide⟩ p hp j hj hq fz1_84_2 fz2_84_2
  · exact pair_85_2 p hp hrep j hj hq
  · exact pair_86_2 p hp hrep j hj hq
  · exact pair_87_2 p hp hrep j hj hq
  · exact pair_88_2 p hp hrep j hj hq
  · exact pair_89_2 p hp hrep j hj hq
  · exact match_zero_fix ⟨90, by decide⟩ ⟨2, by decide⟩ p hp j hj hq fz1_90_2 fz2_90_2
  · exact match_zero_fix ⟨91, by decide⟩ ⟨2, by decide⟩ p hp j hj hq fz1_91_2 fz2_91_2
  · exact match_zero_fix ⟨92, by decide⟩ ⟨2, by decide⟩ p hp j hj hq fz1_92_2 fz2_92_2
  · exact match_zero_fix ⟨93, by decide⟩ ⟨2, by decide⟩ p hp j hj hq fz1_93_2 fz2_93_2
  · exact match_zero_fix ⟨94, by decide⟩ ⟨2, by decide⟩ p hp j hj hq fz1_94_2 fz2_94_2
  · exact match_zero_fix ⟨95, by decide⟩ ⟨2, by decide⟩ p hp j hj hq fz1_95_2 fz2_95_2
  · exact match_zero_fix ⟨96, by decide⟩ ⟨2, by decide⟩ p hp j hj hq fz1_96_2 fz2_96_2
  · exact match_zero_fix ⟨97, by decide⟩ ⟨2, by decide⟩ p hp j hj hq fz1_97_2 fz2_97_2
  · exact match_zero_fix ⟨98, by decide⟩ ⟨2, by decide⟩ p hp j hj hq fz1_98_2 fz2_98_2
  · exact match_zero_fix ⟨99, by decide⟩ ⟨2, by decide⟩ p hp j hj hq fz1_99_2 fz2_99_2
  · exact match_zero_fix ⟨100, by decide⟩ ⟨2, by decide⟩ p hp j hj hq fz1_100_2 fz2_100_2
  · exact match_zero_fix ⟨101, by decide⟩ ⟨2, by decide⟩ p hp j hj hq fz1_101_2 fz2_101_2
  · exact match_zero_fix ⟨102, by decide⟩ ⟨2, by decide⟩ p hp j hj hq fz1_102_2 fz2_102_2
  · exact match_zero_fix ⟨103, by decide⟩ ⟨2, by decide⟩ p hp j hj hq fz1_103_2 fz2_103_2
  · exact match_zero_fix ⟨104, by decide⟩ ⟨2, by decide⟩ p hp j hj hq fz1_104_2 fz2_104_2
  · exact match_zero_fix ⟨105, by decide⟩ ⟨2, by decide⟩ p hp j hj hq fz1_105_2 fz2_105_2
  · exact match_zero_fix ⟨106, by decide⟩ ⟨2, by decide⟩ p hp j hj hq fz1_106_2 fz2_106_2
  · exact match_zero_fix ⟨107, by decide⟩ ⟨2, by decide⟩ p hp j hj hq fz1_107_2 fz2_107_2
  · exact match_zero_fix ⟨108, by decide⟩ ⟨2, by decide⟩ p hp j hj hq fz1_108_2 fz2_108_2
  · exact match_zero_fix ⟨109, by decide⟩ ⟨2, by decide⟩ p hp j hj hq fz1_109_2 fz2_109_2
  · exact match_zero_fix ⟨110, by decide⟩ ⟨2, by decide⟩ p hp j hj hq fz1_110_2 fz2_110_2
  · exact match_zero_fix ⟨111, by decide⟩ ⟨2, by decide⟩ p hp j hj hq fz1_111_2 fz2_111_2
  · exact match_zero_fix ⟨112, by decide⟩ ⟨2, by decide⟩ p hp j hj hq fz1_112_2 fz2_112_2
  · exact match_zero_fix ⟨113, by decide⟩ ⟨2, by decide⟩ p hp j hj hq fz1_113_2 fz2_113_2
  · exact match_zero_fix ⟨114, by decide⟩ ⟨2, by decide⟩ p hp j hj hq fz1_114_2 fz2_114_2
  · exact match_zero_fix ⟨115, by decide⟩ ⟨2, by decide⟩ p hp j hj hq fz1_115_2 fz2_115_2
  · exact match_zero_fix ⟨116, by decide⟩ ⟨2, by decide⟩ p hp j hj hq fz1_116_2 fz2_116_2
  · exact match_zero_fix ⟨117, by decide⟩ ⟨2, by decide⟩ p hp j hj hq fz1_117_2 fz2_117_2
  · exact match_zero_fix ⟨118, by decide⟩ ⟨2, by decide⟩ p hp j hj hq fz1_118_2 fz2_118_2
  · exact match_zero_fix ⟨119, by decide⟩ ⟨2, by decide⟩ p hp j hj hq fz1_119_2 fz2_119_2
  · exact match_zero_fix ⟨120, by decide⟩ ⟨2, by decide⟩ p hp j hj hq fz1_120_2 fz2_120_2
  · exact pair_121_2 p hp hrep j hj hq
  · exact pair_122_2 p hp hrep j hj hq
  · exact pair_123_2 p hp hrep j hj hq
  · exact pair_124_2 p hp hrep j hj hq
  · exact pair_125_2 p hp hrep j hj hq
  · exact match_zero_fix ⟨126, by decide⟩ ⟨2, by decide⟩ p hp j hj hq fz1_126_2 fz2_126_2
  · exact match_zero_fix ⟨127, by decide⟩ ⟨2, by decide⟩ p hp j hj hq fz1_127_2 fz2_127_2
  · exact match_zero_fix ⟨128, by decide⟩ ⟨2, by decide⟩ p hp j hj hq fz1_128_2 fz2_128_2
  · exact match_zero_fix ⟨129, by decide⟩ ⟨2, by decide⟩ p hp j hj hq fz1_129_2 fz2_129_2
  · exact match_zero_fix ⟨130, by decide⟩ ⟨2, by decide⟩ p hp j hj hq fz1_130_2 fz2_130_2
  · exact match_zero_fix ⟨131, by decide⟩ ⟨2, by decide⟩ p hp j hj hq fz1_131_2 fz2_131_2
  · exact match_zero_fix ⟨132, by decide⟩ ⟨2, by decide⟩ p hp j hj hq fz1_132_2 fz2_132_2
  · exact match_zero_fix ⟨133, by decide⟩ ⟨2, by decide⟩ p hp j hj hq fz1_133_2 fz2_133_2
  · exact match_zero_fix ⟨134, by decide⟩ ⟨2, by decide⟩ p hp j hj hq fz1_134_2 fz2_134_2
  · exact match_zero_fix ⟨135, by decide⟩ ⟨2, by decide⟩ p hp j hj hq fz1_135_2 fz2_135_2
  · exact match_zero_fix ⟨136, by decide⟩ ⟨2, by decide⟩ p hp j hj hq fz1_136_2 fz2_136_2
  · exact match_zero_fix ⟨137, by decide⟩ ⟨2, by decide⟩ p hp j hj hq fz1_137_2 fz2_137_2
  · exact match_zero_fix ⟨138, by decide⟩ ⟨2, by decide⟩ p hp j hj hq fz1_138_2 fz2_138_2
  · exact match_zero_fix ⟨139, by decide⟩ ⟨2, by decide⟩ p hp j hj hq fz1_139_2 fz2_139_2
  · exact match_zero_fix ⟨140, by decide⟩ ⟨2, by decide⟩ p hp j hj hq fz1_140_2 fz2_140_2
  · exact pair_141_2 p hp hrep j hj hq
  · exact match_zero_fix ⟨142, by decide⟩ ⟨2, by decide⟩ p hp j hj hq fz1_142_2 fz2_142_2
  · exact match_zero_fix ⟨143, by decide⟩ ⟨2, by decide⟩ p hp j hj hq fz1_143_2 fz2_143_2
  · exact match_zero_fix ⟨144, by decide⟩ ⟨2, by decide⟩ p hp j hj hq fz1_144_2 fz2_144_2
  · exact match_zero_fix ⟨145, by decide⟩ ⟨2, by decide⟩ p hp j hj hq fz1_145_2 fz2_145_2
  · exact match_zero_fix ⟨146, by decide⟩ ⟨2, by decide⟩ p hp j hj hq fz1_146_2 fz2_146_2
  · exact pair_147_2 p hp hrep j hj hq

theorem master_3 (p : Nat) (hp : p < (Q2.transData.getD 3 []).length)
    (hrep : (Q2.cosetIsRep.getD 3 []).getD p false = true)
    (rK : Fin 148) (j : Nat) (hj : j < (repChars.getD rK.val []).length)
    (hq : (normIsRep.getD rK.val []).getD j false = true) :
    species (Q2.reps (⟨3, by decide⟩ : Fin 148)) (colE2 ⟨3, by decide⟩ p hp)
        (rowE2 rK j hj hq)
      = species (reps (⟨3, by decide⟩ : Fin 148))
        (colE1 ⟨3, by decide⟩ p (transLenTr ⟨3, by decide⟩ p hp)) (rowE1 rK j hj) := by
  rcases rK with ⟨nK, hnK⟩; interval_cases nK
  · exact match_zero_len ⟨0, by decide⟩ ⟨3, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_fix ⟨1, by decide⟩ ⟨3, by decide⟩ p hp j hj hq fz1_1_3 fz2_1_3
  · exact match_zero_fix ⟨2, by decide⟩ ⟨3, by decide⟩ p hp j hj hq fz1_2_3 fz2_2_3
  · exact pair_3_3 p hp hrep j hj hq
  · exact match_zero_fix ⟨4, by decide⟩ ⟨3, by decide⟩ p hp j hj hq fz1_4_3 fz2_4_3
  · exact match_zero_fix ⟨5, by decide⟩ ⟨3, by decide⟩ p hp j hj hq fz1_5_3 fz2_5_3
  · exact match_zero_fix ⟨6, by decide⟩ ⟨3, by decide⟩ p hp j hj hq fz1_6_3 fz2_6_3
  · exact match_zero_fix ⟨7, by decide⟩ ⟨3, by decide⟩ p hp j hj hq fz1_7_3 fz2_7_3
  · exact match_zero_fix ⟨8, by decide⟩ ⟨3, by decide⟩ p hp j hj hq fz1_8_3 fz2_8_3
  · exact match_zero_fix ⟨9, by decide⟩ ⟨3, by decide⟩ p hp j hj hq fz1_9_3 fz2_9_3
  · exact match_zero_fix ⟨10, by decide⟩ ⟨3, by decide⟩ p hp j hj hq fz1_10_3 fz2_10_3
  · exact match_zero_fix ⟨11, by decide⟩ ⟨3, by decide⟩ p hp j hj hq fz1_11_3 fz2_11_3
  · exact match_zero_fix ⟨12, by decide⟩ ⟨3, by decide⟩ p hp j hj hq fz1_12_3 fz2_12_3
  · exact match_zero_fix ⟨13, by decide⟩ ⟨3, by decide⟩ p hp j hj hq fz1_13_3 fz2_13_3
  · exact pair_14_3 p hp hrep j hj hq
  · exact pair_15_3 p hp hrep j hj hq
  · exact pair_16_3 p hp hrep j hj hq
  · exact pair_17_3 p hp hrep j hj hq
  · exact pair_18_3 p hp hrep j hj hq
  · exact match_zero_fix ⟨19, by decide⟩ ⟨3, by decide⟩ p hp j hj hq fz1_19_3 fz2_19_3
  · exact match_zero_fix ⟨20, by decide⟩ ⟨3, by decide⟩ p hp j hj hq fz1_20_3 fz2_20_3
  · exact pair_21_3 p hp hrep j hj hq
  · exact match_zero_fix ⟨22, by decide⟩ ⟨3, by decide⟩ p hp j hj hq fz1_22_3 fz2_22_3
  · exact match_zero_fix ⟨23, by decide⟩ ⟨3, by decide⟩ p hp j hj hq fz1_23_3 fz2_23_3
  · exact match_zero_fix ⟨24, by decide⟩ ⟨3, by decide⟩ p hp j hj hq fz1_24_3 fz2_24_3
  · exact match_zero_fix ⟨25, by decide⟩ ⟨3, by decide⟩ p hp j hj hq fz1_25_3 fz2_25_3
  · exact match_zero_fix ⟨26, by decide⟩ ⟨3, by decide⟩ p hp j hj hq fz1_26_3 fz2_26_3
  · exact match_zero_fix ⟨27, by decide⟩ ⟨3, by decide⟩ p hp j hj hq fz1_27_3 fz2_27_3
  · exact match_zero_fix ⟨28, by decide⟩ ⟨3, by decide⟩ p hp j hj hq fz1_28_3 fz2_28_3
  · exact match_zero_fix ⟨29, by decide⟩ ⟨3, by decide⟩ p hp j hj hq fz1_29_3 fz2_29_3
  · exact match_zero_fix ⟨30, by decide⟩ ⟨3, by decide⟩ p hp j hj hq fz1_30_3 fz2_30_3
  · exact match_zero_fix ⟨31, by decide⟩ ⟨3, by decide⟩ p hp j hj hq fz1_31_3 fz2_31_3
  · exact match_zero_fix ⟨32, by decide⟩ ⟨3, by decide⟩ p hp j hj hq fz1_32_3 fz2_32_3
  · exact match_zero_fix ⟨33, by decide⟩ ⟨3, by decide⟩ p hp j hj hq fz1_33_3 fz2_33_3
  · exact match_zero_fix ⟨34, by decide⟩ ⟨3, by decide⟩ p hp j hj hq fz1_34_3 fz2_34_3
  · exact match_zero_fix ⟨35, by decide⟩ ⟨3, by decide⟩ p hp j hj hq fz1_35_3 fz2_35_3
  · exact match_zero_fix ⟨36, by decide⟩ ⟨3, by decide⟩ p hp j hj hq fz1_36_3 fz2_36_3
  · exact match_zero_fix ⟨37, by decide⟩ ⟨3, by decide⟩ p hp j hj hq fz1_37_3 fz2_37_3
  · exact match_zero_fix ⟨38, by decide⟩ ⟨3, by decide⟩ p hp j hj hq fz1_38_3 fz2_38_3
  · exact match_zero_fix ⟨39, by decide⟩ ⟨3, by decide⟩ p hp j hj hq fz1_39_3 fz2_39_3
  · exact match_zero_fix ⟨40, by decide⟩ ⟨3, by decide⟩ p hp j hj hq fz1_40_3 fz2_40_3
  · exact match_zero_fix ⟨41, by decide⟩ ⟨3, by decide⟩ p hp j hj hq fz1_41_3 fz2_41_3
  · exact match_zero_fix ⟨42, by decide⟩ ⟨3, by decide⟩ p hp j hj hq fz1_42_3 fz2_42_3
  · exact match_zero_fix ⟨43, by decide⟩ ⟨3, by decide⟩ p hp j hj hq fz1_43_3 fz2_43_3
  · exact match_zero_fix ⟨44, by decide⟩ ⟨3, by decide⟩ p hp j hj hq fz1_44_3 fz2_44_3
  · exact match_zero_fix ⟨45, by decide⟩ ⟨3, by decide⟩ p hp j hj hq fz1_45_3 fz2_45_3
  · exact match_zero_fix ⟨46, by decide⟩ ⟨3, by decide⟩ p hp j hj hq fz1_46_3 fz2_46_3
  · exact match_zero_fix ⟨47, by decide⟩ ⟨3, by decide⟩ p hp j hj hq fz1_47_3 fz2_47_3
  · exact match_zero_fix ⟨48, by decide⟩ ⟨3, by decide⟩ p hp j hj hq fz1_48_3 fz2_48_3
  · exact match_zero_fix ⟨49, by decide⟩ ⟨3, by decide⟩ p hp j hj hq fz1_49_3 fz2_49_3
  · exact match_zero_fix ⟨50, by decide⟩ ⟨3, by decide⟩ p hp j hj hq fz1_50_3 fz2_50_3
  · exact match_zero_fix ⟨51, by decide⟩ ⟨3, by decide⟩ p hp j hj hq fz1_51_3 fz2_51_3
  · exact match_zero_fix ⟨52, by decide⟩ ⟨3, by decide⟩ p hp j hj hq fz1_52_3 fz2_52_3
  · exact match_zero_fix ⟨53, by decide⟩ ⟨3, by decide⟩ p hp j hj hq fz1_53_3 fz2_53_3
  · exact match_zero_fix ⟨54, by decide⟩ ⟨3, by decide⟩ p hp j hj hq fz1_54_3 fz2_54_3
  · exact match_zero_fix ⟨55, by decide⟩ ⟨3, by decide⟩ p hp j hj hq fz1_55_3 fz2_55_3
  · exact match_zero_fix ⟨56, by decide⟩ ⟨3, by decide⟩ p hp j hj hq fz1_56_3 fz2_56_3
  · exact match_zero_fix ⟨57, by decide⟩ ⟨3, by decide⟩ p hp j hj hq fz1_57_3 fz2_57_3
  · exact match_zero_fix ⟨58, by decide⟩ ⟨3, by decide⟩ p hp j hj hq fz1_58_3 fz2_58_3
  · exact match_zero_fix ⟨59, by decide⟩ ⟨3, by decide⟩ p hp j hj hq fz1_59_3 fz2_59_3
  · exact match_zero_fix ⟨60, by decide⟩ ⟨3, by decide⟩ p hp j hj hq fz1_60_3 fz2_60_3
  · exact match_zero_fix ⟨61, by decide⟩ ⟨3, by decide⟩ p hp j hj hq fz1_61_3 fz2_61_3
  · exact match_zero_fix ⟨62, by decide⟩ ⟨3, by decide⟩ p hp j hj hq fz1_62_3 fz2_62_3
  · exact match_zero_fix ⟨63, by decide⟩ ⟨3, by decide⟩ p hp j hj hq fz1_63_3 fz2_63_3
  · exact match_zero_fix ⟨64, by decide⟩ ⟨3, by decide⟩ p hp j hj hq fz1_64_3 fz2_64_3
  · exact match_zero_fix ⟨65, by decide⟩ ⟨3, by decide⟩ p hp j hj hq fz1_65_3 fz2_65_3
  · exact match_zero_fix ⟨66, by decide⟩ ⟨3, by decide⟩ p hp j hj hq fz1_66_3 fz2_66_3
  · exact match_zero_fix ⟨67, by decide⟩ ⟨3, by decide⟩ p hp j hj hq fz1_67_3 fz2_67_3
  · exact match_zero_fix ⟨68, by decide⟩ ⟨3, by decide⟩ p hp j hj hq fz1_68_3 fz2_68_3
  · exact match_zero_fix ⟨69, by decide⟩ ⟨3, by decide⟩ p hp j hj hq fz1_69_3 fz2_69_3
  · exact match_zero_fix ⟨70, by decide⟩ ⟨3, by decide⟩ p hp j hj hq fz1_70_3 fz2_70_3
  · exact match_zero_fix ⟨71, by decide⟩ ⟨3, by decide⟩ p hp j hj hq fz1_71_3 fz2_71_3
  · exact match_zero_fix ⟨72, by decide⟩ ⟨3, by decide⟩ p hp j hj hq fz1_72_3 fz2_72_3
  · exact match_zero_fix ⟨73, by decide⟩ ⟨3, by decide⟩ p hp j hj hq fz1_73_3 fz2_73_3
  · exact match_zero_fix ⟨74, by decide⟩ ⟨3, by decide⟩ p hp j hj hq fz1_74_3 fz2_74_3
  · exact match_zero_fix ⟨75, by decide⟩ ⟨3, by decide⟩ p hp j hj hq fz1_75_3 fz2_75_3
  · exact match_zero_fix ⟨76, by decide⟩ ⟨3, by decide⟩ p hp j hj hq fz1_76_3 fz2_76_3
  · exact match_zero_fix ⟨77, by decide⟩ ⟨3, by decide⟩ p hp j hj hq fz1_77_3 fz2_77_3
  · exact match_zero_fix ⟨78, by decide⟩ ⟨3, by decide⟩ p hp j hj hq fz1_78_3 fz2_78_3
  · exact match_zero_fix ⟨79, by decide⟩ ⟨3, by decide⟩ p hp j hj hq fz1_79_3 fz2_79_3
  · exact match_zero_fix ⟨80, by decide⟩ ⟨3, by decide⟩ p hp j hj hq fz1_80_3 fz2_80_3
  · exact match_zero_fix ⟨81, by decide⟩ ⟨3, by decide⟩ p hp j hj hq fz1_81_3 fz2_81_3
  · exact pair_82_3 p hp hrep j hj hq
  · exact match_zero_fix ⟨83, by decide⟩ ⟨3, by decide⟩ p hp j hj hq fz1_83_3 fz2_83_3
  · exact match_zero_fix ⟨84, by decide⟩ ⟨3, by decide⟩ p hp j hj hq fz1_84_3 fz2_84_3
  · exact pair_85_3 p hp hrep j hj hq
  · exact pair_86_3 p hp hrep j hj hq
  · exact pair_87_3 p hp hrep j hj hq
  · exact pair_88_3 p hp hrep j hj hq
  · exact pair_89_3 p hp hrep j hj hq
  · exact match_zero_fix ⟨90, by decide⟩ ⟨3, by decide⟩ p hp j hj hq fz1_90_3 fz2_90_3
  · exact match_zero_fix ⟨91, by decide⟩ ⟨3, by decide⟩ p hp j hj hq fz1_91_3 fz2_91_3
  · exact match_zero_fix ⟨92, by decide⟩ ⟨3, by decide⟩ p hp j hj hq fz1_92_3 fz2_92_3
  · exact match_zero_fix ⟨93, by decide⟩ ⟨3, by decide⟩ p hp j hj hq fz1_93_3 fz2_93_3
  · exact match_zero_fix ⟨94, by decide⟩ ⟨3, by decide⟩ p hp j hj hq fz1_94_3 fz2_94_3
  · exact match_zero_fix ⟨95, by decide⟩ ⟨3, by decide⟩ p hp j hj hq fz1_95_3 fz2_95_3
  · exact match_zero_fix ⟨96, by decide⟩ ⟨3, by decide⟩ p hp j hj hq fz1_96_3 fz2_96_3
  · exact match_zero_fix ⟨97, by decide⟩ ⟨3, by decide⟩ p hp j hj hq fz1_97_3 fz2_97_3
  · exact match_zero_fix ⟨98, by decide⟩ ⟨3, by decide⟩ p hp j hj hq fz1_98_3 fz2_98_3
  · exact match_zero_fix ⟨99, by decide⟩ ⟨3, by decide⟩ p hp j hj hq fz1_99_3 fz2_99_3
  · exact match_zero_fix ⟨100, by decide⟩ ⟨3, by decide⟩ p hp j hj hq fz1_100_3 fz2_100_3
  · exact match_zero_fix ⟨101, by decide⟩ ⟨3, by decide⟩ p hp j hj hq fz1_101_3 fz2_101_3
  · exact match_zero_fix ⟨102, by decide⟩ ⟨3, by decide⟩ p hp j hj hq fz1_102_3 fz2_102_3
  · exact match_zero_fix ⟨103, by decide⟩ ⟨3, by decide⟩ p hp j hj hq fz1_103_3 fz2_103_3
  · exact match_zero_fix ⟨104, by decide⟩ ⟨3, by decide⟩ p hp j hj hq fz1_104_3 fz2_104_3
  · exact match_zero_fix ⟨105, by decide⟩ ⟨3, by decide⟩ p hp j hj hq fz1_105_3 fz2_105_3
  · exact match_zero_fix ⟨106, by decide⟩ ⟨3, by decide⟩ p hp j hj hq fz1_106_3 fz2_106_3
  · exact match_zero_fix ⟨107, by decide⟩ ⟨3, by decide⟩ p hp j hj hq fz1_107_3 fz2_107_3
  · exact match_zero_fix ⟨108, by decide⟩ ⟨3, by decide⟩ p hp j hj hq fz1_108_3 fz2_108_3
  · exact match_zero_fix ⟨109, by decide⟩ ⟨3, by decide⟩ p hp j hj hq fz1_109_3 fz2_109_3
  · exact match_zero_fix ⟨110, by decide⟩ ⟨3, by decide⟩ p hp j hj hq fz1_110_3 fz2_110_3
  · exact match_zero_fix ⟨111, by decide⟩ ⟨3, by decide⟩ p hp j hj hq fz1_111_3 fz2_111_3
  · exact match_zero_fix ⟨112, by decide⟩ ⟨3, by decide⟩ p hp j hj hq fz1_112_3 fz2_112_3
  · exact match_zero_fix ⟨113, by decide⟩ ⟨3, by decide⟩ p hp j hj hq fz1_113_3 fz2_113_3
  · exact match_zero_fix ⟨114, by decide⟩ ⟨3, by decide⟩ p hp j hj hq fz1_114_3 fz2_114_3
  · exact match_zero_fix ⟨115, by decide⟩ ⟨3, by decide⟩ p hp j hj hq fz1_115_3 fz2_115_3
  · exact match_zero_fix ⟨116, by decide⟩ ⟨3, by decide⟩ p hp j hj hq fz1_116_3 fz2_116_3
  · exact match_zero_fix ⟨117, by decide⟩ ⟨3, by decide⟩ p hp j hj hq fz1_117_3 fz2_117_3
  · exact match_zero_fix ⟨118, by decide⟩ ⟨3, by decide⟩ p hp j hj hq fz1_118_3 fz2_118_3
  · exact match_zero_fix ⟨119, by decide⟩ ⟨3, by decide⟩ p hp j hj hq fz1_119_3 fz2_119_3
  · exact match_zero_fix ⟨120, by decide⟩ ⟨3, by decide⟩ p hp j hj hq fz1_120_3 fz2_120_3
  · exact match_zero_fix ⟨121, by decide⟩ ⟨3, by decide⟩ p hp j hj hq fz1_121_3 fz2_121_3
  · exact match_zero_fix ⟨122, by decide⟩ ⟨3, by decide⟩ p hp j hj hq fz1_122_3 fz2_122_3
  · exact match_zero_fix ⟨123, by decide⟩ ⟨3, by decide⟩ p hp j hj hq fz1_123_3 fz2_123_3
  · exact match_zero_fix ⟨124, by decide⟩ ⟨3, by decide⟩ p hp j hj hq fz1_124_3 fz2_124_3
  · exact match_zero_fix ⟨125, by decide⟩ ⟨3, by decide⟩ p hp j hj hq fz1_125_3 fz2_125_3
  · exact pair_126_3 p hp hrep j hj hq
  · exact pair_127_3 p hp hrep j hj hq
  · exact pair_128_3 p hp hrep j hj hq
  · exact pair_129_3 p hp hrep j hj hq
  · exact pair_130_3 p hp hrep j hj hq
  · exact match_zero_fix ⟨131, by decide⟩ ⟨3, by decide⟩ p hp j hj hq fz1_131_3 fz2_131_3
  · exact match_zero_fix ⟨132, by decide⟩ ⟨3, by decide⟩ p hp j hj hq fz1_132_3 fz2_132_3
  · exact match_zero_fix ⟨133, by decide⟩ ⟨3, by decide⟩ p hp j hj hq fz1_133_3 fz2_133_3
  · exact match_zero_fix ⟨134, by decide⟩ ⟨3, by decide⟩ p hp j hj hq fz1_134_3 fz2_134_3
  · exact match_zero_fix ⟨135, by decide⟩ ⟨3, by decide⟩ p hp j hj hq fz1_135_3 fz2_135_3
  · exact match_zero_fix ⟨136, by decide⟩ ⟨3, by decide⟩ p hp j hj hq fz1_136_3 fz2_136_3
  · exact match_zero_fix ⟨137, by decide⟩ ⟨3, by decide⟩ p hp j hj hq fz1_137_3 fz2_137_3
  · exact match_zero_fix ⟨138, by decide⟩ ⟨3, by decide⟩ p hp j hj hq fz1_138_3 fz2_138_3
  · exact match_zero_fix ⟨139, by decide⟩ ⟨3, by decide⟩ p hp j hj hq fz1_139_3 fz2_139_3
  · exact match_zero_fix ⟨140, by decide⟩ ⟨3, by decide⟩ p hp j hj hq fz1_140_3 fz2_140_3
  · exact pair_141_3 p hp hrep j hj hq
  · exact match_zero_fix ⟨142, by decide⟩ ⟨3, by decide⟩ p hp j hj hq fz1_142_3 fz2_142_3
  · exact match_zero_fix ⟨143, by decide⟩ ⟨3, by decide⟩ p hp j hj hq fz1_143_3 fz2_143_3
  · exact match_zero_fix ⟨144, by decide⟩ ⟨3, by decide⟩ p hp j hj hq fz1_144_3 fz2_144_3
  · exact match_zero_fix ⟨145, by decide⟩ ⟨3, by decide⟩ p hp j hj hq fz1_145_3 fz2_145_3
  · exact match_zero_fix ⟨146, by decide⟩ ⟨3, by decide⟩ p hp j hj hq fz1_146_3 fz2_146_3
  · exact pair_147_3 p hp hrep j hj hq

theorem master_4 (p : Nat) (hp : p < (Q2.transData.getD 4 []).length)
    (hrep : (Q2.cosetIsRep.getD 4 []).getD p false = true)
    (rK : Fin 148) (j : Nat) (hj : j < (repChars.getD rK.val []).length)
    (hq : (normIsRep.getD rK.val []).getD j false = true) :
    species (Q2.reps (⟨4, by decide⟩ : Fin 148)) (colE2 ⟨4, by decide⟩ p hp)
        (rowE2 rK j hj hq)
      = species (reps (⟨4, by decide⟩ : Fin 148))
        (colE1 ⟨4, by decide⟩ p (transLenTr ⟨4, by decide⟩ p hp)) (rowE1 rK j hj) := by
  rcases rK with ⟨nK, hnK⟩; interval_cases nK
  · exact match_zero_len ⟨0, by decide⟩ ⟨4, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_fix ⟨1, by decide⟩ ⟨4, by decide⟩ p hp j hj hq fz1_1_4 fz2_1_4
  · exact match_zero_fix ⟨2, by decide⟩ ⟨4, by decide⟩ p hp j hj hq fz1_2_4 fz2_2_4
  · exact match_zero_fix ⟨3, by decide⟩ ⟨4, by decide⟩ p hp j hj hq fz1_3_4 fz2_3_4
  · exact pair_4_4 p hp hrep j hj hq
  · exact match_zero_fix ⟨5, by decide⟩ ⟨4, by decide⟩ p hp j hj hq fz1_5_4 fz2_5_4
  · exact match_zero_fix ⟨6, by decide⟩ ⟨4, by decide⟩ p hp j hj hq fz1_6_4 fz2_6_4
  · exact match_zero_fix ⟨7, by decide⟩ ⟨4, by decide⟩ p hp j hj hq fz1_7_4 fz2_7_4
  · exact match_zero_fix ⟨8, by decide⟩ ⟨4, by decide⟩ p hp j hj hq fz1_8_4 fz2_8_4
  · exact match_zero_fix ⟨9, by decide⟩ ⟨4, by decide⟩ p hp j hj hq fz1_9_4 fz2_9_4
  · exact match_zero_fix ⟨10, by decide⟩ ⟨4, by decide⟩ p hp j hj hq fz1_10_4 fz2_10_4
  · exact match_zero_fix ⟨11, by decide⟩ ⟨4, by decide⟩ p hp j hj hq fz1_11_4 fz2_11_4
  · exact match_zero_fix ⟨12, by decide⟩ ⟨4, by decide⟩ p hp j hj hq fz1_12_4 fz2_12_4
  · exact match_zero_fix ⟨13, by decide⟩ ⟨4, by decide⟩ p hp j hj hq fz1_13_4 fz2_13_4
  · exact pair_14_4 p hp hrep j hj hq
  · exact pair_15_4 p hp hrep j hj hq
  · exact pair_16_4 p hp hrep j hj hq
  · exact pair_17_4 p hp hrep j hj hq
  · exact pair_18_4 p hp hrep j hj hq
  · exact match_zero_fix ⟨19, by decide⟩ ⟨4, by decide⟩ p hp j hj hq fz1_19_4 fz2_19_4
  · exact match_zero_fix ⟨20, by decide⟩ ⟨4, by decide⟩ p hp j hj hq fz1_20_4 fz2_20_4
  · exact match_zero_fix ⟨21, by decide⟩ ⟨4, by decide⟩ p hp j hj hq fz1_21_4 fz2_21_4
  · exact pair_22_4 p hp hrep j hj hq
  · exact match_zero_fix ⟨23, by decide⟩ ⟨4, by decide⟩ p hp j hj hq fz1_23_4 fz2_23_4
  · exact match_zero_fix ⟨24, by decide⟩ ⟨4, by decide⟩ p hp j hj hq fz1_24_4 fz2_24_4
  · exact match_zero_fix ⟨25, by decide⟩ ⟨4, by decide⟩ p hp j hj hq fz1_25_4 fz2_25_4
  · exact match_zero_fix ⟨26, by decide⟩ ⟨4, by decide⟩ p hp j hj hq fz1_26_4 fz2_26_4
  · exact match_zero_fix ⟨27, by decide⟩ ⟨4, by decide⟩ p hp j hj hq fz1_27_4 fz2_27_4
  · exact match_zero_fix ⟨28, by decide⟩ ⟨4, by decide⟩ p hp j hj hq fz1_28_4 fz2_28_4
  · exact match_zero_fix ⟨29, by decide⟩ ⟨4, by decide⟩ p hp j hj hq fz1_29_4 fz2_29_4
  · exact match_zero_fix ⟨30, by decide⟩ ⟨4, by decide⟩ p hp j hj hq fz1_30_4 fz2_30_4
  · exact match_zero_fix ⟨31, by decide⟩ ⟨4, by decide⟩ p hp j hj hq fz1_31_4 fz2_31_4
  · exact match_zero_fix ⟨32, by decide⟩ ⟨4, by decide⟩ p hp j hj hq fz1_32_4 fz2_32_4
  · exact match_zero_fix ⟨33, by decide⟩ ⟨4, by decide⟩ p hp j hj hq fz1_33_4 fz2_33_4
  · exact match_zero_fix ⟨34, by decide⟩ ⟨4, by decide⟩ p hp j hj hq fz1_34_4 fz2_34_4
  · exact match_zero_fix ⟨35, by decide⟩ ⟨4, by decide⟩ p hp j hj hq fz1_35_4 fz2_35_4
  · exact match_zero_fix ⟨36, by decide⟩ ⟨4, by decide⟩ p hp j hj hq fz1_36_4 fz2_36_4
  · exact match_zero_fix ⟨37, by decide⟩ ⟨4, by decide⟩ p hp j hj hq fz1_37_4 fz2_37_4
  · exact match_zero_fix ⟨38, by decide⟩ ⟨4, by decide⟩ p hp j hj hq fz1_38_4 fz2_38_4
  · exact match_zero_fix ⟨39, by decide⟩ ⟨4, by decide⟩ p hp j hj hq fz1_39_4 fz2_39_4
  · exact match_zero_fix ⟨40, by decide⟩ ⟨4, by decide⟩ p hp j hj hq fz1_40_4 fz2_40_4
  · exact match_zero_fix ⟨41, by decide⟩ ⟨4, by decide⟩ p hp j hj hq fz1_41_4 fz2_41_4
  · exact match_zero_fix ⟨42, by decide⟩ ⟨4, by decide⟩ p hp j hj hq fz1_42_4 fz2_42_4
  · exact match_zero_fix ⟨43, by decide⟩ ⟨4, by decide⟩ p hp j hj hq fz1_43_4 fz2_43_4
  · exact match_zero_fix ⟨44, by decide⟩ ⟨4, by decide⟩ p hp j hj hq fz1_44_4 fz2_44_4
  · exact match_zero_fix ⟨45, by decide⟩ ⟨4, by decide⟩ p hp j hj hq fz1_45_4 fz2_45_4
  · exact match_zero_fix ⟨46, by decide⟩ ⟨4, by decide⟩ p hp j hj hq fz1_46_4 fz2_46_4
  · exact match_zero_fix ⟨47, by decide⟩ ⟨4, by decide⟩ p hp j hj hq fz1_47_4 fz2_47_4
  · exact match_zero_fix ⟨48, by decide⟩ ⟨4, by decide⟩ p hp j hj hq fz1_48_4 fz2_48_4
  · exact match_zero_fix ⟨49, by decide⟩ ⟨4, by decide⟩ p hp j hj hq fz1_49_4 fz2_49_4
  · exact match_zero_fix ⟨50, by decide⟩ ⟨4, by decide⟩ p hp j hj hq fz1_50_4 fz2_50_4
  · exact match_zero_fix ⟨51, by decide⟩ ⟨4, by decide⟩ p hp j hj hq fz1_51_4 fz2_51_4
  · exact match_zero_fix ⟨52, by decide⟩ ⟨4, by decide⟩ p hp j hj hq fz1_52_4 fz2_52_4
  · exact match_zero_fix ⟨53, by decide⟩ ⟨4, by decide⟩ p hp j hj hq fz1_53_4 fz2_53_4
  · exact match_zero_fix ⟨54, by decide⟩ ⟨4, by decide⟩ p hp j hj hq fz1_54_4 fz2_54_4
  · exact match_zero_fix ⟨55, by decide⟩ ⟨4, by decide⟩ p hp j hj hq fz1_55_4 fz2_55_4
  · exact match_zero_fix ⟨56, by decide⟩ ⟨4, by decide⟩ p hp j hj hq fz1_56_4 fz2_56_4
  · exact match_zero_fix ⟨57, by decide⟩ ⟨4, by decide⟩ p hp j hj hq fz1_57_4 fz2_57_4
  · exact match_zero_fix ⟨58, by decide⟩ ⟨4, by decide⟩ p hp j hj hq fz1_58_4 fz2_58_4
  · exact match_zero_fix ⟨59, by decide⟩ ⟨4, by decide⟩ p hp j hj hq fz1_59_4 fz2_59_4
  · exact match_zero_fix ⟨60, by decide⟩ ⟨4, by decide⟩ p hp j hj hq fz1_60_4 fz2_60_4
  · exact match_zero_fix ⟨61, by decide⟩ ⟨4, by decide⟩ p hp j hj hq fz1_61_4 fz2_61_4
  · exact match_zero_fix ⟨62, by decide⟩ ⟨4, by decide⟩ p hp j hj hq fz1_62_4 fz2_62_4
  · exact match_zero_fix ⟨63, by decide⟩ ⟨4, by decide⟩ p hp j hj hq fz1_63_4 fz2_63_4
  · exact match_zero_fix ⟨64, by decide⟩ ⟨4, by decide⟩ p hp j hj hq fz1_64_4 fz2_64_4
  · exact match_zero_fix ⟨65, by decide⟩ ⟨4, by decide⟩ p hp j hj hq fz1_65_4 fz2_65_4
  · exact match_zero_fix ⟨66, by decide⟩ ⟨4, by decide⟩ p hp j hj hq fz1_66_4 fz2_66_4
  · exact match_zero_fix ⟨67, by decide⟩ ⟨4, by decide⟩ p hp j hj hq fz1_67_4 fz2_67_4
  · exact match_zero_fix ⟨68, by decide⟩ ⟨4, by decide⟩ p hp j hj hq fz1_68_4 fz2_68_4
  · exact match_zero_fix ⟨69, by decide⟩ ⟨4, by decide⟩ p hp j hj hq fz1_69_4 fz2_69_4
  · exact match_zero_fix ⟨70, by decide⟩ ⟨4, by decide⟩ p hp j hj hq fz1_70_4 fz2_70_4
  · exact match_zero_fix ⟨71, by decide⟩ ⟨4, by decide⟩ p hp j hj hq fz1_71_4 fz2_71_4
  · exact match_zero_fix ⟨72, by decide⟩ ⟨4, by decide⟩ p hp j hj hq fz1_72_4 fz2_72_4
  · exact match_zero_fix ⟨73, by decide⟩ ⟨4, by decide⟩ p hp j hj hq fz1_73_4 fz2_73_4
  · exact match_zero_fix ⟨74, by decide⟩ ⟨4, by decide⟩ p hp j hj hq fz1_74_4 fz2_74_4
  · exact match_zero_fix ⟨75, by decide⟩ ⟨4, by decide⟩ p hp j hj hq fz1_75_4 fz2_75_4
  · exact match_zero_fix ⟨76, by decide⟩ ⟨4, by decide⟩ p hp j hj hq fz1_76_4 fz2_76_4
  · exact match_zero_fix ⟨77, by decide⟩ ⟨4, by decide⟩ p hp j hj hq fz1_77_4 fz2_77_4
  · exact match_zero_fix ⟨78, by decide⟩ ⟨4, by decide⟩ p hp j hj hq fz1_78_4 fz2_78_4
  · exact match_zero_fix ⟨79, by decide⟩ ⟨4, by decide⟩ p hp j hj hq fz1_79_4 fz2_79_4
  · exact match_zero_fix ⟨80, by decide⟩ ⟨4, by decide⟩ p hp j hj hq fz1_80_4 fz2_80_4
  · exact match_zero_fix ⟨81, by decide⟩ ⟨4, by decide⟩ p hp j hj hq fz1_81_4 fz2_81_4
  · exact match_zero_fix ⟨82, by decide⟩ ⟨4, by decide⟩ p hp j hj hq fz1_82_4 fz2_82_4
  · exact pair_83_4 p hp hrep j hj hq
  · exact match_zero_fix ⟨84, by decide⟩ ⟨4, by decide⟩ p hp j hj hq fz1_84_4 fz2_84_4
  · exact pair_85_4 p hp hrep j hj hq
  · exact pair_86_4 p hp hrep j hj hq
  · exact pair_87_4 p hp hrep j hj hq
  · exact pair_88_4 p hp hrep j hj hq
  · exact pair_89_4 p hp hrep j hj hq
  · exact match_zero_fix ⟨90, by decide⟩ ⟨4, by decide⟩ p hp j hj hq fz1_90_4 fz2_90_4
  · exact match_zero_fix ⟨91, by decide⟩ ⟨4, by decide⟩ p hp j hj hq fz1_91_4 fz2_91_4
  · exact match_zero_fix ⟨92, by decide⟩ ⟨4, by decide⟩ p hp j hj hq fz1_92_4 fz2_92_4
  · exact match_zero_fix ⟨93, by decide⟩ ⟨4, by decide⟩ p hp j hj hq fz1_93_4 fz2_93_4
  · exact match_zero_fix ⟨94, by decide⟩ ⟨4, by decide⟩ p hp j hj hq fz1_94_4 fz2_94_4
  · exact match_zero_fix ⟨95, by decide⟩ ⟨4, by decide⟩ p hp j hj hq fz1_95_4 fz2_95_4
  · exact match_zero_fix ⟨96, by decide⟩ ⟨4, by decide⟩ p hp j hj hq fz1_96_4 fz2_96_4
  · exact match_zero_fix ⟨97, by decide⟩ ⟨4, by decide⟩ p hp j hj hq fz1_97_4 fz2_97_4
  · exact match_zero_fix ⟨98, by decide⟩ ⟨4, by decide⟩ p hp j hj hq fz1_98_4 fz2_98_4
  · exact match_zero_fix ⟨99, by decide⟩ ⟨4, by decide⟩ p hp j hj hq fz1_99_4 fz2_99_4
  · exact match_zero_fix ⟨100, by decide⟩ ⟨4, by decide⟩ p hp j hj hq fz1_100_4 fz2_100_4
  · exact match_zero_fix ⟨101, by decide⟩ ⟨4, by decide⟩ p hp j hj hq fz1_101_4 fz2_101_4
  · exact match_zero_fix ⟨102, by decide⟩ ⟨4, by decide⟩ p hp j hj hq fz1_102_4 fz2_102_4
  · exact match_zero_fix ⟨103, by decide⟩ ⟨4, by decide⟩ p hp j hj hq fz1_103_4 fz2_103_4
  · exact match_zero_fix ⟨104, by decide⟩ ⟨4, by decide⟩ p hp j hj hq fz1_104_4 fz2_104_4
  · exact match_zero_fix ⟨105, by decide⟩ ⟨4, by decide⟩ p hp j hj hq fz1_105_4 fz2_105_4
  · exact match_zero_fix ⟨106, by decide⟩ ⟨4, by decide⟩ p hp j hj hq fz1_106_4 fz2_106_4
  · exact match_zero_fix ⟨107, by decide⟩ ⟨4, by decide⟩ p hp j hj hq fz1_107_4 fz2_107_4
  · exact match_zero_fix ⟨108, by decide⟩ ⟨4, by decide⟩ p hp j hj hq fz1_108_4 fz2_108_4
  · exact match_zero_fix ⟨109, by decide⟩ ⟨4, by decide⟩ p hp j hj hq fz1_109_4 fz2_109_4
  · exact match_zero_fix ⟨110, by decide⟩ ⟨4, by decide⟩ p hp j hj hq fz1_110_4 fz2_110_4
  · exact match_zero_fix ⟨111, by decide⟩ ⟨4, by decide⟩ p hp j hj hq fz1_111_4 fz2_111_4
  · exact match_zero_fix ⟨112, by decide⟩ ⟨4, by decide⟩ p hp j hj hq fz1_112_4 fz2_112_4
  · exact match_zero_fix ⟨113, by decide⟩ ⟨4, by decide⟩ p hp j hj hq fz1_113_4 fz2_113_4
  · exact match_zero_fix ⟨114, by decide⟩ ⟨4, by decide⟩ p hp j hj hq fz1_114_4 fz2_114_4
  · exact match_zero_fix ⟨115, by decide⟩ ⟨4, by decide⟩ p hp j hj hq fz1_115_4 fz2_115_4
  · exact match_zero_fix ⟨116, by decide⟩ ⟨4, by decide⟩ p hp j hj hq fz1_116_4 fz2_116_4
  · exact match_zero_fix ⟨117, by decide⟩ ⟨4, by decide⟩ p hp j hj hq fz1_117_4 fz2_117_4
  · exact match_zero_fix ⟨118, by decide⟩ ⟨4, by decide⟩ p hp j hj hq fz1_118_4 fz2_118_4
  · exact match_zero_fix ⟨119, by decide⟩ ⟨4, by decide⟩ p hp j hj hq fz1_119_4 fz2_119_4
  · exact match_zero_fix ⟨120, by decide⟩ ⟨4, by decide⟩ p hp j hj hq fz1_120_4 fz2_120_4
  · exact match_zero_fix ⟨121, by decide⟩ ⟨4, by decide⟩ p hp j hj hq fz1_121_4 fz2_121_4
  · exact match_zero_fix ⟨122, by decide⟩ ⟨4, by decide⟩ p hp j hj hq fz1_122_4 fz2_122_4
  · exact match_zero_fix ⟨123, by decide⟩ ⟨4, by decide⟩ p hp j hj hq fz1_123_4 fz2_123_4
  · exact match_zero_fix ⟨124, by decide⟩ ⟨4, by decide⟩ p hp j hj hq fz1_124_4 fz2_124_4
  · exact match_zero_fix ⟨125, by decide⟩ ⟨4, by decide⟩ p hp j hj hq fz1_125_4 fz2_125_4
  · exact match_zero_fix ⟨126, by decide⟩ ⟨4, by decide⟩ p hp j hj hq fz1_126_4 fz2_126_4
  · exact match_zero_fix ⟨127, by decide⟩ ⟨4, by decide⟩ p hp j hj hq fz1_127_4 fz2_127_4
  · exact match_zero_fix ⟨128, by decide⟩ ⟨4, by decide⟩ p hp j hj hq fz1_128_4 fz2_128_4
  · exact match_zero_fix ⟨129, by decide⟩ ⟨4, by decide⟩ p hp j hj hq fz1_129_4 fz2_129_4
  · exact match_zero_fix ⟨130, by decide⟩ ⟨4, by decide⟩ p hp j hj hq fz1_130_4 fz2_130_4
  · exact pair_131_4 p hp hrep j hj hq
  · exact pair_132_4 p hp hrep j hj hq
  · exact pair_133_4 p hp hrep j hj hq
  · exact pair_134_4 p hp hrep j hj hq
  · exact pair_135_4 p hp hrep j hj hq
  · exact match_zero_fix ⟨136, by decide⟩ ⟨4, by decide⟩ p hp j hj hq fz1_136_4 fz2_136_4
  · exact match_zero_fix ⟨137, by decide⟩ ⟨4, by decide⟩ p hp j hj hq fz1_137_4 fz2_137_4
  · exact match_zero_fix ⟨138, by decide⟩ ⟨4, by decide⟩ p hp j hj hq fz1_138_4 fz2_138_4
  · exact match_zero_fix ⟨139, by decide⟩ ⟨4, by decide⟩ p hp j hj hq fz1_139_4 fz2_139_4
  · exact match_zero_fix ⟨140, by decide⟩ ⟨4, by decide⟩ p hp j hj hq fz1_140_4 fz2_140_4
  · exact pair_141_4 p hp hrep j hj hq
  · exact match_zero_fix ⟨142, by decide⟩ ⟨4, by decide⟩ p hp j hj hq fz1_142_4 fz2_142_4
  · exact match_zero_fix ⟨143, by decide⟩ ⟨4, by decide⟩ p hp j hj hq fz1_143_4 fz2_143_4
  · exact match_zero_fix ⟨144, by decide⟩ ⟨4, by decide⟩ p hp j hj hq fz1_144_4 fz2_144_4
  · exact match_zero_fix ⟨145, by decide⟩ ⟨4, by decide⟩ p hp j hj hq fz1_145_4 fz2_145_4
  · exact match_zero_fix ⟨146, by decide⟩ ⟨4, by decide⟩ p hp j hj hq fz1_146_4 fz2_146_4
  · exact pair_147_4 p hp hrep j hj hq

theorem master_5 (p : Nat) (hp : p < (Q2.transData.getD 5 []).length)
    (hrep : (Q2.cosetIsRep.getD 5 []).getD p false = true)
    (rK : Fin 148) (j : Nat) (hj : j < (repChars.getD rK.val []).length)
    (hq : (normIsRep.getD rK.val []).getD j false = true) :
    species (Q2.reps (⟨5, by decide⟩ : Fin 148)) (colE2 ⟨5, by decide⟩ p hp)
        (rowE2 rK j hj hq)
      = species (reps (⟨5, by decide⟩ : Fin 148))
        (colE1 ⟨5, by decide⟩ p (transLenTr ⟨5, by decide⟩ p hp)) (rowE1 rK j hj) := by
  rcases rK with ⟨nK, hnK⟩; interval_cases nK
  · exact match_zero_len ⟨0, by decide⟩ ⟨5, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_fix ⟨1, by decide⟩ ⟨5, by decide⟩ p hp j hj hq fz1_1_5 fz2_1_5
  · exact match_zero_fix ⟨2, by decide⟩ ⟨5, by decide⟩ p hp j hj hq fz1_2_5 fz2_2_5
  · exact match_zero_fix ⟨3, by decide⟩ ⟨5, by decide⟩ p hp j hj hq fz1_3_5 fz2_3_5
  · exact match_zero_fix ⟨4, by decide⟩ ⟨5, by decide⟩ p hp j hj hq fz1_4_5 fz2_4_5
  · exact pair_5_5 p hp hrep j hj hq
  · exact match_zero_fix ⟨6, by decide⟩ ⟨5, by decide⟩ p hp j hj hq fz1_6_5 fz2_6_5
  · exact match_zero_fix ⟨7, by decide⟩ ⟨5, by decide⟩ p hp j hj hq fz1_7_5 fz2_7_5
  · exact match_zero_fix ⟨8, by decide⟩ ⟨5, by decide⟩ p hp j hj hq fz1_8_5 fz2_8_5
  · exact match_zero_fix ⟨9, by decide⟩ ⟨5, by decide⟩ p hp j hj hq fz1_9_5 fz2_9_5
  · exact match_zero_fix ⟨10, by decide⟩ ⟨5, by decide⟩ p hp j hj hq fz1_10_5 fz2_10_5
  · exact match_zero_fix ⟨11, by decide⟩ ⟨5, by decide⟩ p hp j hj hq fz1_11_5 fz2_11_5
  · exact match_zero_fix ⟨12, by decide⟩ ⟨5, by decide⟩ p hp j hj hq fz1_12_5 fz2_12_5
  · exact match_zero_fix ⟨13, by decide⟩ ⟨5, by decide⟩ p hp j hj hq fz1_13_5 fz2_13_5
  · exact pair_14_5 p hp hrep j hj hq
  · exact pair_15_5 p hp hrep j hj hq
  · exact pair_16_5 p hp hrep j hj hq
  · exact pair_17_5 p hp hrep j hj hq
  · exact pair_18_5 p hp hrep j hj hq
  · exact match_zero_fix ⟨19, by decide⟩ ⟨5, by decide⟩ p hp j hj hq fz1_19_5 fz2_19_5
  · exact match_zero_fix ⟨20, by decide⟩ ⟨5, by decide⟩ p hp j hj hq fz1_20_5 fz2_20_5
  · exact match_zero_fix ⟨21, by decide⟩ ⟨5, by decide⟩ p hp j hj hq fz1_21_5 fz2_21_5
  · exact match_zero_fix ⟨22, by decide⟩ ⟨5, by decide⟩ p hp j hj hq fz1_22_5 fz2_22_5
  · exact pair_23_5 p hp hrep j hj hq
  · exact match_zero_fix ⟨24, by decide⟩ ⟨5, by decide⟩ p hp j hj hq fz1_24_5 fz2_24_5
  · exact match_zero_fix ⟨25, by decide⟩ ⟨5, by decide⟩ p hp j hj hq fz1_25_5 fz2_25_5
  · exact match_zero_fix ⟨26, by decide⟩ ⟨5, by decide⟩ p hp j hj hq fz1_26_5 fz2_26_5
  · exact match_zero_fix ⟨27, by decide⟩ ⟨5, by decide⟩ p hp j hj hq fz1_27_5 fz2_27_5
  · exact match_zero_fix ⟨28, by decide⟩ ⟨5, by decide⟩ p hp j hj hq fz1_28_5 fz2_28_5
  · exact match_zero_fix ⟨29, by decide⟩ ⟨5, by decide⟩ p hp j hj hq fz1_29_5 fz2_29_5
  · exact match_zero_fix ⟨30, by decide⟩ ⟨5, by decide⟩ p hp j hj hq fz1_30_5 fz2_30_5
  · exact match_zero_fix ⟨31, by decide⟩ ⟨5, by decide⟩ p hp j hj hq fz1_31_5 fz2_31_5
  · exact match_zero_fix ⟨32, by decide⟩ ⟨5, by decide⟩ p hp j hj hq fz1_32_5 fz2_32_5
  · exact match_zero_fix ⟨33, by decide⟩ ⟨5, by decide⟩ p hp j hj hq fz1_33_5 fz2_33_5
  · exact match_zero_fix ⟨34, by decide⟩ ⟨5, by decide⟩ p hp j hj hq fz1_34_5 fz2_34_5
  · exact match_zero_fix ⟨35, by decide⟩ ⟨5, by decide⟩ p hp j hj hq fz1_35_5 fz2_35_5
  · exact match_zero_fix ⟨36, by decide⟩ ⟨5, by decide⟩ p hp j hj hq fz1_36_5 fz2_36_5
  · exact match_zero_fix ⟨37, by decide⟩ ⟨5, by decide⟩ p hp j hj hq fz1_37_5 fz2_37_5
  · exact match_zero_fix ⟨38, by decide⟩ ⟨5, by decide⟩ p hp j hj hq fz1_38_5 fz2_38_5
  · exact match_zero_fix ⟨39, by decide⟩ ⟨5, by decide⟩ p hp j hj hq fz1_39_5 fz2_39_5
  · exact match_zero_fix ⟨40, by decide⟩ ⟨5, by decide⟩ p hp j hj hq fz1_40_5 fz2_40_5
  · exact match_zero_fix ⟨41, by decide⟩ ⟨5, by decide⟩ p hp j hj hq fz1_41_5 fz2_41_5
  · exact match_zero_fix ⟨42, by decide⟩ ⟨5, by decide⟩ p hp j hj hq fz1_42_5 fz2_42_5
  · exact match_zero_fix ⟨43, by decide⟩ ⟨5, by decide⟩ p hp j hj hq fz1_43_5 fz2_43_5
  · exact match_zero_fix ⟨44, by decide⟩ ⟨5, by decide⟩ p hp j hj hq fz1_44_5 fz2_44_5
  · exact match_zero_fix ⟨45, by decide⟩ ⟨5, by decide⟩ p hp j hj hq fz1_45_5 fz2_45_5
  · exact match_zero_fix ⟨46, by decide⟩ ⟨5, by decide⟩ p hp j hj hq fz1_46_5 fz2_46_5
  · exact match_zero_fix ⟨47, by decide⟩ ⟨5, by decide⟩ p hp j hj hq fz1_47_5 fz2_47_5
  · exact match_zero_fix ⟨48, by decide⟩ ⟨5, by decide⟩ p hp j hj hq fz1_48_5 fz2_48_5
  · exact match_zero_fix ⟨49, by decide⟩ ⟨5, by decide⟩ p hp j hj hq fz1_49_5 fz2_49_5
  · exact match_zero_fix ⟨50, by decide⟩ ⟨5, by decide⟩ p hp j hj hq fz1_50_5 fz2_50_5
  · exact match_zero_fix ⟨51, by decide⟩ ⟨5, by decide⟩ p hp j hj hq fz1_51_5 fz2_51_5
  · exact match_zero_fix ⟨52, by decide⟩ ⟨5, by decide⟩ p hp j hj hq fz1_52_5 fz2_52_5
  · exact match_zero_fix ⟨53, by decide⟩ ⟨5, by decide⟩ p hp j hj hq fz1_53_5 fz2_53_5
  · exact match_zero_fix ⟨54, by decide⟩ ⟨5, by decide⟩ p hp j hj hq fz1_54_5 fz2_54_5
  · exact match_zero_fix ⟨55, by decide⟩ ⟨5, by decide⟩ p hp j hj hq fz1_55_5 fz2_55_5
  · exact match_zero_fix ⟨56, by decide⟩ ⟨5, by decide⟩ p hp j hj hq fz1_56_5 fz2_56_5
  · exact match_zero_fix ⟨57, by decide⟩ ⟨5, by decide⟩ p hp j hj hq fz1_57_5 fz2_57_5
  · exact match_zero_fix ⟨58, by decide⟩ ⟨5, by decide⟩ p hp j hj hq fz1_58_5 fz2_58_5
  · exact match_zero_fix ⟨59, by decide⟩ ⟨5, by decide⟩ p hp j hj hq fz1_59_5 fz2_59_5
  · exact match_zero_fix ⟨60, by decide⟩ ⟨5, by decide⟩ p hp j hj hq fz1_60_5 fz2_60_5
  · exact match_zero_fix ⟨61, by decide⟩ ⟨5, by decide⟩ p hp j hj hq fz1_61_5 fz2_61_5
  · exact match_zero_fix ⟨62, by decide⟩ ⟨5, by decide⟩ p hp j hj hq fz1_62_5 fz2_62_5
  · exact match_zero_fix ⟨63, by decide⟩ ⟨5, by decide⟩ p hp j hj hq fz1_63_5 fz2_63_5
  · exact match_zero_fix ⟨64, by decide⟩ ⟨5, by decide⟩ p hp j hj hq fz1_64_5 fz2_64_5
  · exact match_zero_fix ⟨65, by decide⟩ ⟨5, by decide⟩ p hp j hj hq fz1_65_5 fz2_65_5
  · exact match_zero_fix ⟨66, by decide⟩ ⟨5, by decide⟩ p hp j hj hq fz1_66_5 fz2_66_5
  · exact match_zero_fix ⟨67, by decide⟩ ⟨5, by decide⟩ p hp j hj hq fz1_67_5 fz2_67_5
  · exact match_zero_fix ⟨68, by decide⟩ ⟨5, by decide⟩ p hp j hj hq fz1_68_5 fz2_68_5
  · exact match_zero_fix ⟨69, by decide⟩ ⟨5, by decide⟩ p hp j hj hq fz1_69_5 fz2_69_5
  · exact match_zero_fix ⟨70, by decide⟩ ⟨5, by decide⟩ p hp j hj hq fz1_70_5 fz2_70_5
  · exact match_zero_fix ⟨71, by decide⟩ ⟨5, by decide⟩ p hp j hj hq fz1_71_5 fz2_71_5
  · exact match_zero_fix ⟨72, by decide⟩ ⟨5, by decide⟩ p hp j hj hq fz1_72_5 fz2_72_5
  · exact match_zero_fix ⟨73, by decide⟩ ⟨5, by decide⟩ p hp j hj hq fz1_73_5 fz2_73_5
  · exact match_zero_fix ⟨74, by decide⟩ ⟨5, by decide⟩ p hp j hj hq fz1_74_5 fz2_74_5
  · exact match_zero_fix ⟨75, by decide⟩ ⟨5, by decide⟩ p hp j hj hq fz1_75_5 fz2_75_5
  · exact match_zero_fix ⟨76, by decide⟩ ⟨5, by decide⟩ p hp j hj hq fz1_76_5 fz2_76_5
  · exact match_zero_fix ⟨77, by decide⟩ ⟨5, by decide⟩ p hp j hj hq fz1_77_5 fz2_77_5
  · exact match_zero_fix ⟨78, by decide⟩ ⟨5, by decide⟩ p hp j hj hq fz1_78_5 fz2_78_5
  · exact match_zero_fix ⟨79, by decide⟩ ⟨5, by decide⟩ p hp j hj hq fz1_79_5 fz2_79_5
  · exact match_zero_fix ⟨80, by decide⟩ ⟨5, by decide⟩ p hp j hj hq fz1_80_5 fz2_80_5
  · exact match_zero_fix ⟨81, by decide⟩ ⟨5, by decide⟩ p hp j hj hq fz1_81_5 fz2_81_5
  · exact match_zero_fix ⟨82, by decide⟩ ⟨5, by decide⟩ p hp j hj hq fz1_82_5 fz2_82_5
  · exact match_zero_fix ⟨83, by decide⟩ ⟨5, by decide⟩ p hp j hj hq fz1_83_5 fz2_83_5
  · exact pair_84_5 p hp hrep j hj hq
  · exact pair_85_5 p hp hrep j hj hq
  · exact pair_86_5 p hp hrep j hj hq
  · exact pair_87_5 p hp hrep j hj hq
  · exact pair_88_5 p hp hrep j hj hq
  · exact pair_89_5 p hp hrep j hj hq
  · exact match_zero_fix ⟨90, by decide⟩ ⟨5, by decide⟩ p hp j hj hq fz1_90_5 fz2_90_5
  · exact match_zero_fix ⟨91, by decide⟩ ⟨5, by decide⟩ p hp j hj hq fz1_91_5 fz2_91_5
  · exact match_zero_fix ⟨92, by decide⟩ ⟨5, by decide⟩ p hp j hj hq fz1_92_5 fz2_92_5
  · exact match_zero_fix ⟨93, by decide⟩ ⟨5, by decide⟩ p hp j hj hq fz1_93_5 fz2_93_5
  · exact match_zero_fix ⟨94, by decide⟩ ⟨5, by decide⟩ p hp j hj hq fz1_94_5 fz2_94_5
  · exact match_zero_fix ⟨95, by decide⟩ ⟨5, by decide⟩ p hp j hj hq fz1_95_5 fz2_95_5
  · exact match_zero_fix ⟨96, by decide⟩ ⟨5, by decide⟩ p hp j hj hq fz1_96_5 fz2_96_5
  · exact match_zero_fix ⟨97, by decide⟩ ⟨5, by decide⟩ p hp j hj hq fz1_97_5 fz2_97_5
  · exact match_zero_fix ⟨98, by decide⟩ ⟨5, by decide⟩ p hp j hj hq fz1_98_5 fz2_98_5
  · exact match_zero_fix ⟨99, by decide⟩ ⟨5, by decide⟩ p hp j hj hq fz1_99_5 fz2_99_5
  · exact match_zero_fix ⟨100, by decide⟩ ⟨5, by decide⟩ p hp j hj hq fz1_100_5 fz2_100_5
  · exact match_zero_fix ⟨101, by decide⟩ ⟨5, by decide⟩ p hp j hj hq fz1_101_5 fz2_101_5
  · exact match_zero_fix ⟨102, by decide⟩ ⟨5, by decide⟩ p hp j hj hq fz1_102_5 fz2_102_5
  · exact match_zero_fix ⟨103, by decide⟩ ⟨5, by decide⟩ p hp j hj hq fz1_103_5 fz2_103_5
  · exact match_zero_fix ⟨104, by decide⟩ ⟨5, by decide⟩ p hp j hj hq fz1_104_5 fz2_104_5
  · exact match_zero_fix ⟨105, by decide⟩ ⟨5, by decide⟩ p hp j hj hq fz1_105_5 fz2_105_5
  · exact match_zero_fix ⟨106, by decide⟩ ⟨5, by decide⟩ p hp j hj hq fz1_106_5 fz2_106_5
  · exact match_zero_fix ⟨107, by decide⟩ ⟨5, by decide⟩ p hp j hj hq fz1_107_5 fz2_107_5
  · exact match_zero_fix ⟨108, by decide⟩ ⟨5, by decide⟩ p hp j hj hq fz1_108_5 fz2_108_5
  · exact match_zero_fix ⟨109, by decide⟩ ⟨5, by decide⟩ p hp j hj hq fz1_109_5 fz2_109_5
  · exact match_zero_fix ⟨110, by decide⟩ ⟨5, by decide⟩ p hp j hj hq fz1_110_5 fz2_110_5
  · exact match_zero_fix ⟨111, by decide⟩ ⟨5, by decide⟩ p hp j hj hq fz1_111_5 fz2_111_5
  · exact match_zero_fix ⟨112, by decide⟩ ⟨5, by decide⟩ p hp j hj hq fz1_112_5 fz2_112_5
  · exact match_zero_fix ⟨113, by decide⟩ ⟨5, by decide⟩ p hp j hj hq fz1_113_5 fz2_113_5
  · exact match_zero_fix ⟨114, by decide⟩ ⟨5, by decide⟩ p hp j hj hq fz1_114_5 fz2_114_5
  · exact match_zero_fix ⟨115, by decide⟩ ⟨5, by decide⟩ p hp j hj hq fz1_115_5 fz2_115_5
  · exact match_zero_fix ⟨116, by decide⟩ ⟨5, by decide⟩ p hp j hj hq fz1_116_5 fz2_116_5
  · exact match_zero_fix ⟨117, by decide⟩ ⟨5, by decide⟩ p hp j hj hq fz1_117_5 fz2_117_5
  · exact match_zero_fix ⟨118, by decide⟩ ⟨5, by decide⟩ p hp j hj hq fz1_118_5 fz2_118_5
  · exact match_zero_fix ⟨119, by decide⟩ ⟨5, by decide⟩ p hp j hj hq fz1_119_5 fz2_119_5
  · exact match_zero_fix ⟨120, by decide⟩ ⟨5, by decide⟩ p hp j hj hq fz1_120_5 fz2_120_5
  · exact match_zero_fix ⟨121, by decide⟩ ⟨5, by decide⟩ p hp j hj hq fz1_121_5 fz2_121_5
  · exact match_zero_fix ⟨122, by decide⟩ ⟨5, by decide⟩ p hp j hj hq fz1_122_5 fz2_122_5
  · exact match_zero_fix ⟨123, by decide⟩ ⟨5, by decide⟩ p hp j hj hq fz1_123_5 fz2_123_5
  · exact match_zero_fix ⟨124, by decide⟩ ⟨5, by decide⟩ p hp j hj hq fz1_124_5 fz2_124_5
  · exact match_zero_fix ⟨125, by decide⟩ ⟨5, by decide⟩ p hp j hj hq fz1_125_5 fz2_125_5
  · exact match_zero_fix ⟨126, by decide⟩ ⟨5, by decide⟩ p hp j hj hq fz1_126_5 fz2_126_5
  · exact match_zero_fix ⟨127, by decide⟩ ⟨5, by decide⟩ p hp j hj hq fz1_127_5 fz2_127_5
  · exact match_zero_fix ⟨128, by decide⟩ ⟨5, by decide⟩ p hp j hj hq fz1_128_5 fz2_128_5
  · exact match_zero_fix ⟨129, by decide⟩ ⟨5, by decide⟩ p hp j hj hq fz1_129_5 fz2_129_5
  · exact match_zero_fix ⟨130, by decide⟩ ⟨5, by decide⟩ p hp j hj hq fz1_130_5 fz2_130_5
  · exact match_zero_fix ⟨131, by decide⟩ ⟨5, by decide⟩ p hp j hj hq fz1_131_5 fz2_131_5
  · exact match_zero_fix ⟨132, by decide⟩ ⟨5, by decide⟩ p hp j hj hq fz1_132_5 fz2_132_5
  · exact match_zero_fix ⟨133, by decide⟩ ⟨5, by decide⟩ p hp j hj hq fz1_133_5 fz2_133_5
  · exact match_zero_fix ⟨134, by decide⟩ ⟨5, by decide⟩ p hp j hj hq fz1_134_5 fz2_134_5
  · exact match_zero_fix ⟨135, by decide⟩ ⟨5, by decide⟩ p hp j hj hq fz1_135_5 fz2_135_5
  · exact pair_136_5 p hp hrep j hj hq
  · exact pair_137_5 p hp hrep j hj hq
  · exact pair_138_5 p hp hrep j hj hq
  · exact pair_139_5 p hp hrep j hj hq
  · exact pair_140_5 p hp hrep j hj hq
  · exact pair_141_5 p hp hrep j hj hq
  · exact match_zero_fix ⟨142, by decide⟩ ⟨5, by decide⟩ p hp j hj hq fz1_142_5 fz2_142_5
  · exact match_zero_fix ⟨143, by decide⟩ ⟨5, by decide⟩ p hp j hj hq fz1_143_5 fz2_143_5
  · exact match_zero_fix ⟨144, by decide⟩ ⟨5, by decide⟩ p hp j hj hq fz1_144_5 fz2_144_5
  · exact match_zero_fix ⟨145, by decide⟩ ⟨5, by decide⟩ p hp j hj hq fz1_145_5 fz2_145_5
  · exact match_zero_fix ⟨146, by decide⟩ ⟨5, by decide⟩ p hp j hj hq fz1_146_5 fz2_146_5
  · exact pair_147_5 p hp hrep j hj hq

theorem master_6 (p : Nat) (hp : p < (Q2.transData.getD 6 []).length)
    (hrep : (Q2.cosetIsRep.getD 6 []).getD p false = true)
    (rK : Fin 148) (j : Nat) (hj : j < (repChars.getD rK.val []).length)
    (hq : (normIsRep.getD rK.val []).getD j false = true) :
    species (Q2.reps (⟨6, by decide⟩ : Fin 148)) (colE2 ⟨6, by decide⟩ p hp)
        (rowE2 rK j hj hq)
      = species (reps (⟨6, by decide⟩ : Fin 148))
        (colE1 ⟨6, by decide⟩ p (transLenTr ⟨6, by decide⟩ p hp)) (rowE1 rK j hj) := by
  rcases rK with ⟨nK, hnK⟩; interval_cases nK
  · exact match_zero_len ⟨0, by decide⟩ ⟨6, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_fix ⟨1, by decide⟩ ⟨6, by decide⟩ p hp j hj hq fz1_1_6 fz2_1_6
  · exact match_zero_fix ⟨2, by decide⟩ ⟨6, by decide⟩ p hp j hj hq fz1_2_6 fz2_2_6
  · exact match_zero_fix ⟨3, by decide⟩ ⟨6, by decide⟩ p hp j hj hq fz1_3_6 fz2_3_6
  · exact match_zero_fix ⟨4, by decide⟩ ⟨6, by decide⟩ p hp j hj hq fz1_4_6 fz2_4_6
  · exact match_zero_fix ⟨5, by decide⟩ ⟨6, by decide⟩ p hp j hj hq fz1_5_6 fz2_5_6
  · exact pair_6_6 p hp hrep j hj hq
  · exact match_zero_fix ⟨7, by decide⟩ ⟨6, by decide⟩ p hp j hj hq fz1_7_6 fz2_7_6
  · exact match_zero_fix ⟨8, by decide⟩ ⟨6, by decide⟩ p hp j hj hq fz1_8_6 fz2_8_6
  · exact match_zero_fix ⟨9, by decide⟩ ⟨6, by decide⟩ p hp j hj hq fz1_9_6 fz2_9_6
  · exact match_zero_fix ⟨10, by decide⟩ ⟨6, by decide⟩ p hp j hj hq fz1_10_6 fz2_10_6
  · exact match_zero_fix ⟨11, by decide⟩ ⟨6, by decide⟩ p hp j hj hq fz1_11_6 fz2_11_6
  · exact match_zero_fix ⟨12, by decide⟩ ⟨6, by decide⟩ p hp j hj hq fz1_12_6 fz2_12_6
  · exact pair_13_6 p hp hrep j hj hq
  · exact match_zero_fix ⟨14, by decide⟩ ⟨6, by decide⟩ p hp j hj hq fz1_14_6 fz2_14_6
  · exact match_zero_fix ⟨15, by decide⟩ ⟨6, by decide⟩ p hp j hj hq fz1_15_6 fz2_15_6
  · exact match_zero_fix ⟨16, by decide⟩ ⟨6, by decide⟩ p hp j hj hq fz1_16_6 fz2_16_6
  · exact match_zero_fix ⟨17, by decide⟩ ⟨6, by decide⟩ p hp j hj hq fz1_17_6 fz2_17_6
  · exact match_zero_fix ⟨18, by decide⟩ ⟨6, by decide⟩ p hp j hj hq fz1_18_6 fz2_18_6
  · exact match_zero_fix ⟨19, by decide⟩ ⟨6, by decide⟩ p hp j hj hq fz1_19_6 fz2_19_6
  · exact match_zero_fix ⟨20, by decide⟩ ⟨6, by decide⟩ p hp j hj hq fz1_20_6 fz2_20_6
  · exact match_zero_fix ⟨21, by decide⟩ ⟨6, by decide⟩ p hp j hj hq fz1_21_6 fz2_21_6
  · exact match_zero_fix ⟨22, by decide⟩ ⟨6, by decide⟩ p hp j hj hq fz1_22_6 fz2_22_6
  · exact match_zero_fix ⟨23, by decide⟩ ⟨6, by decide⟩ p hp j hj hq fz1_23_6 fz2_23_6
  · exact pair_24_6 p hp hrep j hj hq
  · exact match_zero_fix ⟨25, by decide⟩ ⟨6, by decide⟩ p hp j hj hq fz1_25_6 fz2_25_6
  · exact match_zero_fix ⟨26, by decide⟩ ⟨6, by decide⟩ p hp j hj hq fz1_26_6 fz2_26_6
  · exact match_zero_fix ⟨27, by decide⟩ ⟨6, by decide⟩ p hp j hj hq fz1_27_6 fz2_27_6
  · exact match_zero_fix ⟨28, by decide⟩ ⟨6, by decide⟩ p hp j hj hq fz1_28_6 fz2_28_6
  · exact match_zero_fix ⟨29, by decide⟩ ⟨6, by decide⟩ p hp j hj hq fz1_29_6 fz2_29_6
  · exact match_zero_fix ⟨30, by decide⟩ ⟨6, by decide⟩ p hp j hj hq fz1_30_6 fz2_30_6
  · exact match_zero_fix ⟨31, by decide⟩ ⟨6, by decide⟩ p hp j hj hq fz1_31_6 fz2_31_6
  · exact match_zero_fix ⟨32, by decide⟩ ⟨6, by decide⟩ p hp j hj hq fz1_32_6 fz2_32_6
  · exact match_zero_fix ⟨33, by decide⟩ ⟨6, by decide⟩ p hp j hj hq fz1_33_6 fz2_33_6
  · exact match_zero_fix ⟨34, by decide⟩ ⟨6, by decide⟩ p hp j hj hq fz1_34_6 fz2_34_6
  · exact match_zero_fix ⟨35, by decide⟩ ⟨6, by decide⟩ p hp j hj hq fz1_35_6 fz2_35_6
  · exact match_zero_fix ⟨36, by decide⟩ ⟨6, by decide⟩ p hp j hj hq fz1_36_6 fz2_36_6
  · exact match_zero_fix ⟨37, by decide⟩ ⟨6, by decide⟩ p hp j hj hq fz1_37_6 fz2_37_6
  · exact match_zero_fix ⟨38, by decide⟩ ⟨6, by decide⟩ p hp j hj hq fz1_38_6 fz2_38_6
  · exact match_zero_fix ⟨39, by decide⟩ ⟨6, by decide⟩ p hp j hj hq fz1_39_6 fz2_39_6
  · exact match_zero_fix ⟨40, by decide⟩ ⟨6, by decide⟩ p hp j hj hq fz1_40_6 fz2_40_6
  · exact match_zero_fix ⟨41, by decide⟩ ⟨6, by decide⟩ p hp j hj hq fz1_41_6 fz2_41_6
  · exact match_zero_fix ⟨42, by decide⟩ ⟨6, by decide⟩ p hp j hj hq fz1_42_6 fz2_42_6
  · exact match_zero_fix ⟨43, by decide⟩ ⟨6, by decide⟩ p hp j hj hq fz1_43_6 fz2_43_6
  · exact match_zero_fix ⟨44, by decide⟩ ⟨6, by decide⟩ p hp j hj hq fz1_44_6 fz2_44_6
  · exact match_zero_fix ⟨45, by decide⟩ ⟨6, by decide⟩ p hp j hj hq fz1_45_6 fz2_45_6
  · exact match_zero_fix ⟨46, by decide⟩ ⟨6, by decide⟩ p hp j hj hq fz1_46_6 fz2_46_6
  · exact match_zero_fix ⟨47, by decide⟩ ⟨6, by decide⟩ p hp j hj hq fz1_47_6 fz2_47_6
  · exact match_zero_fix ⟨48, by decide⟩ ⟨6, by decide⟩ p hp j hj hq fz1_48_6 fz2_48_6
  · exact match_zero_fix ⟨49, by decide⟩ ⟨6, by decide⟩ p hp j hj hq fz1_49_6 fz2_49_6
  · exact match_zero_fix ⟨50, by decide⟩ ⟨6, by decide⟩ p hp j hj hq fz1_50_6 fz2_50_6
  · exact match_zero_fix ⟨51, by decide⟩ ⟨6, by decide⟩ p hp j hj hq fz1_51_6 fz2_51_6
  · exact match_zero_fix ⟨52, by decide⟩ ⟨6, by decide⟩ p hp j hj hq fz1_52_6 fz2_52_6
  · exact match_zero_fix ⟨53, by decide⟩ ⟨6, by decide⟩ p hp j hj hq fz1_53_6 fz2_53_6
  · exact match_zero_fix ⟨54, by decide⟩ ⟨6, by decide⟩ p hp j hj hq fz1_54_6 fz2_54_6
  · exact match_zero_fix ⟨55, by decide⟩ ⟨6, by decide⟩ p hp j hj hq fz1_55_6 fz2_55_6
  · exact match_zero_fix ⟨56, by decide⟩ ⟨6, by decide⟩ p hp j hj hq fz1_56_6 fz2_56_6
  · exact match_zero_fix ⟨57, by decide⟩ ⟨6, by decide⟩ p hp j hj hq fz1_57_6 fz2_57_6
  · exact pair_58_6 p hp hrep j hj hq
  · exact match_zero_fix ⟨59, by decide⟩ ⟨6, by decide⟩ p hp j hj hq fz1_59_6 fz2_59_6
  · exact match_zero_fix ⟨60, by decide⟩ ⟨6, by decide⟩ p hp j hj hq fz1_60_6 fz2_60_6
  · exact match_zero_fix ⟨61, by decide⟩ ⟨6, by decide⟩ p hp j hj hq fz1_61_6 fz2_61_6
  · exact match_zero_fix ⟨62, by decide⟩ ⟨6, by decide⟩ p hp j hj hq fz1_62_6 fz2_62_6
  · exact pair_63_6 p hp hrep j hj hq
  · exact match_zero_fix ⟨64, by decide⟩ ⟨6, by decide⟩ p hp j hj hq fz1_64_6 fz2_64_6
  · exact match_zero_fix ⟨65, by decide⟩ ⟨6, by decide⟩ p hp j hj hq fz1_65_6 fz2_65_6
  · exact match_zero_fix ⟨66, by decide⟩ ⟨6, by decide⟩ p hp j hj hq fz1_66_6 fz2_66_6
  · exact match_zero_fix ⟨67, by decide⟩ ⟨6, by decide⟩ p hp j hj hq fz1_67_6 fz2_67_6
  · exact pair_68_6 p hp hrep j hj hq
  · exact match_zero_fix ⟨69, by decide⟩ ⟨6, by decide⟩ p hp j hj hq fz1_69_6 fz2_69_6
  · exact match_zero_fix ⟨70, by decide⟩ ⟨6, by decide⟩ p hp j hj hq fz1_70_6 fz2_70_6
  · exact match_zero_fix ⟨71, by decide⟩ ⟨6, by decide⟩ p hp j hj hq fz1_71_6 fz2_71_6
  · exact match_zero_fix ⟨72, by decide⟩ ⟨6, by decide⟩ p hp j hj hq fz1_72_6 fz2_72_6
  · exact pair_73_6 p hp hrep j hj hq
  · exact match_zero_fix ⟨74, by decide⟩ ⟨6, by decide⟩ p hp j hj hq fz1_74_6 fz2_74_6
  · exact match_zero_fix ⟨75, by decide⟩ ⟨6, by decide⟩ p hp j hj hq fz1_75_6 fz2_75_6
  · exact match_zero_fix ⟨76, by decide⟩ ⟨6, by decide⟩ p hp j hj hq fz1_76_6 fz2_76_6
  · exact match_zero_fix ⟨77, by decide⟩ ⟨6, by decide⟩ p hp j hj hq fz1_77_6 fz2_77_6
  · exact pair_78_6 p hp hrep j hj hq
  · exact match_zero_fix ⟨79, by decide⟩ ⟨6, by decide⟩ p hp j hj hq fz1_79_6 fz2_79_6
  · exact pair_80_6 p hp hrep j hj hq
  · exact match_zero_fix ⟨81, by decide⟩ ⟨6, by decide⟩ p hp j hj hq fz1_81_6 fz2_81_6
  · exact match_zero_fix ⟨82, by decide⟩ ⟨6, by decide⟩ p hp j hj hq fz1_82_6 fz2_82_6
  · exact match_zero_fix ⟨83, by decide⟩ ⟨6, by decide⟩ p hp j hj hq fz1_83_6 fz2_83_6
  · exact match_zero_fix ⟨84, by decide⟩ ⟨6, by decide⟩ p hp j hj hq fz1_84_6 fz2_84_6
  · exact match_zero_fix ⟨85, by decide⟩ ⟨6, by decide⟩ p hp j hj hq fz1_85_6 fz2_85_6
  · exact match_zero_fix ⟨86, by decide⟩ ⟨6, by decide⟩ p hp j hj hq fz1_86_6 fz2_86_6
  · exact match_zero_fix ⟨87, by decide⟩ ⟨6, by decide⟩ p hp j hj hq fz1_87_6 fz2_87_6
  · exact pair_88_6 p hp hrep j hj hq
  · exact match_zero_fix ⟨89, by decide⟩ ⟨6, by decide⟩ p hp j hj hq fz1_89_6 fz2_89_6
  · exact match_zero_fix ⟨90, by decide⟩ ⟨6, by decide⟩ p hp j hj hq fz1_90_6 fz2_90_6
  · exact match_zero_fix ⟨91, by decide⟩ ⟨6, by decide⟩ p hp j hj hq fz1_91_6 fz2_91_6
  · exact match_zero_fix ⟨92, by decide⟩ ⟨6, by decide⟩ p hp j hj hq fz1_92_6 fz2_92_6
  · exact match_zero_fix ⟨93, by decide⟩ ⟨6, by decide⟩ p hp j hj hq fz1_93_6 fz2_93_6
  · exact match_zero_fix ⟨94, by decide⟩ ⟨6, by decide⟩ p hp j hj hq fz1_94_6 fz2_94_6
  · exact match_zero_fix ⟨95, by decide⟩ ⟨6, by decide⟩ p hp j hj hq fz1_95_6 fz2_95_6
  · exact match_zero_fix ⟨96, by decide⟩ ⟨6, by decide⟩ p hp j hj hq fz1_96_6 fz2_96_6
  · exact match_zero_fix ⟨97, by decide⟩ ⟨6, by decide⟩ p hp j hj hq fz1_97_6 fz2_97_6
  · exact match_zero_fix ⟨98, by decide⟩ ⟨6, by decide⟩ p hp j hj hq fz1_98_6 fz2_98_6
  · exact match_zero_fix ⟨99, by decide⟩ ⟨6, by decide⟩ p hp j hj hq fz1_99_6 fz2_99_6
  · exact match_zero_fix ⟨100, by decide⟩ ⟨6, by decide⟩ p hp j hj hq fz1_100_6 fz2_100_6
  · exact match_zero_fix ⟨101, by decide⟩ ⟨6, by decide⟩ p hp j hj hq fz1_101_6 fz2_101_6
  · exact match_zero_fix ⟨102, by decide⟩ ⟨6, by decide⟩ p hp j hj hq fz1_102_6 fz2_102_6
  · exact match_zero_fix ⟨103, by decide⟩ ⟨6, by decide⟩ p hp j hj hq fz1_103_6 fz2_103_6
  · exact match_zero_fix ⟨104, by decide⟩ ⟨6, by decide⟩ p hp j hj hq fz1_104_6 fz2_104_6
  · exact match_zero_fix ⟨105, by decide⟩ ⟨6, by decide⟩ p hp j hj hq fz1_105_6 fz2_105_6
  · exact match_zero_fix ⟨106, by decide⟩ ⟨6, by decide⟩ p hp j hj hq fz1_106_6 fz2_106_6
  · exact match_zero_fix ⟨107, by decide⟩ ⟨6, by decide⟩ p hp j hj hq fz1_107_6 fz2_107_6
  · exact match_zero_fix ⟨108, by decide⟩ ⟨6, by decide⟩ p hp j hj hq fz1_108_6 fz2_108_6
  · exact match_zero_fix ⟨109, by decide⟩ ⟨6, by decide⟩ p hp j hj hq fz1_109_6 fz2_109_6
  · exact match_zero_fix ⟨110, by decide⟩ ⟨6, by decide⟩ p hp j hj hq fz1_110_6 fz2_110_6
  · exact match_zero_fix ⟨111, by decide⟩ ⟨6, by decide⟩ p hp j hj hq fz1_111_6 fz2_111_6
  · exact match_zero_fix ⟨112, by decide⟩ ⟨6, by decide⟩ p hp j hj hq fz1_112_6 fz2_112_6
  · exact match_zero_fix ⟨113, by decide⟩ ⟨6, by decide⟩ p hp j hj hq fz1_113_6 fz2_113_6
  · exact match_zero_fix ⟨114, by decide⟩ ⟨6, by decide⟩ p hp j hj hq fz1_114_6 fz2_114_6
  · exact match_zero_fix ⟨115, by decide⟩ ⟨6, by decide⟩ p hp j hj hq fz1_115_6 fz2_115_6
  · exact pair_116_6 p hp hrep j hj hq
  · exact pair_117_6 p hp hrep j hj hq
  · exact pair_118_6 p hp hrep j hj hq
  · exact pair_119_6 p hp hrep j hj hq
  · exact pair_120_6 p hp hrep j hj hq
  · exact match_zero_fix ⟨121, by decide⟩ ⟨6, by decide⟩ p hp j hj hq fz1_121_6 fz2_121_6
  · exact match_zero_fix ⟨122, by decide⟩ ⟨6, by decide⟩ p hp j hj hq fz1_122_6 fz2_122_6
  · exact match_zero_fix ⟨123, by decide⟩ ⟨6, by decide⟩ p hp j hj hq fz1_123_6 fz2_123_6
  · exact match_zero_fix ⟨124, by decide⟩ ⟨6, by decide⟩ p hp j hj hq fz1_124_6 fz2_124_6
  · exact match_zero_fix ⟨125, by decide⟩ ⟨6, by decide⟩ p hp j hj hq fz1_125_6 fz2_125_6
  · exact match_zero_fix ⟨126, by decide⟩ ⟨6, by decide⟩ p hp j hj hq fz1_126_6 fz2_126_6
  · exact match_zero_fix ⟨127, by decide⟩ ⟨6, by decide⟩ p hp j hj hq fz1_127_6 fz2_127_6
  · exact match_zero_fix ⟨128, by decide⟩ ⟨6, by decide⟩ p hp j hj hq fz1_128_6 fz2_128_6
  · exact match_zero_fix ⟨129, by decide⟩ ⟨6, by decide⟩ p hp j hj hq fz1_129_6 fz2_129_6
  · exact match_zero_fix ⟨130, by decide⟩ ⟨6, by decide⟩ p hp j hj hq fz1_130_6 fz2_130_6
  · exact match_zero_fix ⟨131, by decide⟩ ⟨6, by decide⟩ p hp j hj hq fz1_131_6 fz2_131_6
  · exact match_zero_fix ⟨132, by decide⟩ ⟨6, by decide⟩ p hp j hj hq fz1_132_6 fz2_132_6
  · exact match_zero_fix ⟨133, by decide⟩ ⟨6, by decide⟩ p hp j hj hq fz1_133_6 fz2_133_6
  · exact match_zero_fix ⟨134, by decide⟩ ⟨6, by decide⟩ p hp j hj hq fz1_134_6 fz2_134_6
  · exact match_zero_fix ⟨135, by decide⟩ ⟨6, by decide⟩ p hp j hj hq fz1_135_6 fz2_135_6
  · exact match_zero_fix ⟨136, by decide⟩ ⟨6, by decide⟩ p hp j hj hq fz1_136_6 fz2_136_6
  · exact match_zero_fix ⟨137, by decide⟩ ⟨6, by decide⟩ p hp j hj hq fz1_137_6 fz2_137_6
  · exact match_zero_fix ⟨138, by decide⟩ ⟨6, by decide⟩ p hp j hj hq fz1_138_6 fz2_138_6
  · exact match_zero_fix ⟨139, by decide⟩ ⟨6, by decide⟩ p hp j hj hq fz1_139_6 fz2_139_6
  · exact match_zero_fix ⟨140, by decide⟩ ⟨6, by decide⟩ p hp j hj hq fz1_140_6 fz2_140_6
  · exact pair_141_6 p hp hrep j hj hq
  · exact match_zero_fix ⟨142, by decide⟩ ⟨6, by decide⟩ p hp j hj hq fz1_142_6 fz2_142_6
  · exact match_zero_fix ⟨143, by decide⟩ ⟨6, by decide⟩ p hp j hj hq fz1_143_6 fz2_143_6
  · exact match_zero_fix ⟨144, by decide⟩ ⟨6, by decide⟩ p hp j hj hq fz1_144_6 fz2_144_6
  · exact match_zero_fix ⟨145, by decide⟩ ⟨6, by decide⟩ p hp j hj hq fz1_145_6 fz2_145_6
  · exact match_zero_fix ⟨146, by decide⟩ ⟨6, by decide⟩ p hp j hj hq fz1_146_6 fz2_146_6
  · exact pair_147_6 p hp hrep j hj hq

theorem master_7 (p : Nat) (hp : p < (Q2.transData.getD 7 []).length)
    (hrep : (Q2.cosetIsRep.getD 7 []).getD p false = true)
    (rK : Fin 148) (j : Nat) (hj : j < (repChars.getD rK.val []).length)
    (hq : (normIsRep.getD rK.val []).getD j false = true) :
    species (Q2.reps (⟨7, by decide⟩ : Fin 148)) (colE2 ⟨7, by decide⟩ p hp)
        (rowE2 rK j hj hq)
      = species (reps (⟨7, by decide⟩ : Fin 148))
        (colE1 ⟨7, by decide⟩ p (transLenTr ⟨7, by decide⟩ p hp)) (rowE1 rK j hj) := by
  rcases rK with ⟨nK, hnK⟩; interval_cases nK
  · exact match_zero_len ⟨0, by decide⟩ ⟨7, by decide⟩ p hp j hj hq (by decide) (by decide)
  · exact match_zero_fix ⟨1, by decide⟩ ⟨7, by decide⟩ p hp j hj hq fz1_1_7 fz2_1_7
  · exact match_zero_fix ⟨2, by decide⟩ ⟨7, by decide⟩ p hp j hj hq fz1_2_7 fz2_2_7
  · exact match_zero_fix ⟨3, by decide⟩ ⟨7, by decide⟩ p hp j hj hq fz1_3_7 fz2_3_7
  · exact match_zero_fix ⟨4, by decide⟩ ⟨7, by decide⟩ p hp j hj hq fz1_4_7 fz2_4_7
  · exact match_zero_fix ⟨5, by decide⟩ ⟨7, by decide⟩ p hp j hj hq fz1_5_7 fz2_5_7
  · exact match_zero_fix ⟨6, by decide⟩ ⟨7, by decide⟩ p hp j hj hq fz1_6_7 fz2_6_7
  · exact pair_7_7 p hp hrep j hj hq
  · exact match_zero_fix ⟨8, by decide⟩ ⟨7, by decide⟩ p hp j hj hq fz1_8_7 fz2_8_7
  · exact match_zero_fix ⟨9, by decide⟩ ⟨7, by decide⟩ p hp j hj hq fz1_9_7 fz2_9_7
  · exact match_zero_fix ⟨10, by decide⟩ ⟨7, by decide⟩ p hp j hj hq fz1_10_7 fz2_10_7
  · exact match_zero_fix ⟨11, by decide⟩ ⟨7, by decide⟩ p hp j hj hq fz1_11_7 fz2_11_7
  · exact match_zero_fix ⟨12, by decide⟩ ⟨7, by decide⟩ p hp j hj hq fz1_12_7 fz2_12_7
  · exact pair_13_7 p hp hrep j hj hq
  · exact match_zero_fix ⟨14, by decide⟩ ⟨7, by decide⟩ p hp j hj hq fz1_14_7 fz2_14_7
  · exact match_zero_fix ⟨15, by decide⟩ ⟨7, by decide⟩ p hp j hj hq fz1_15_7 fz2_15_7
  · exact match_zero_fix ⟨16, by decide⟩ ⟨7, by decide⟩ p hp j hj hq fz1_16_7 fz2_16_7
  · exact match_zero_fix ⟨17, by decide⟩ ⟨7, by decide⟩ p hp j hj hq fz1_17_7 fz2_17_7
  · exact match_zero_fix ⟨18, by decide⟩ ⟨7, by decide⟩ p hp j hj hq fz1_18_7 fz2_18_7
  · exact match_zero_fix ⟨19, by decide⟩ ⟨7, by decide⟩ p hp j hj hq fz1_19_7 fz2_19_7
  · exact match_zero_fix ⟨20, by decide⟩ ⟨7, by decide⟩ p hp j hj hq fz1_20_7 fz2_20_7
  · exact match_zero_fix ⟨21, by decide⟩ ⟨7, by decide⟩ p hp j hj hq fz1_21_7 fz2_21_7
  · exact match_zero_fix ⟨22, by decide⟩ ⟨7, by decide⟩ p hp j hj hq fz1_22_7 fz2_22_7
  · exact match_zero_fix ⟨23, by decide⟩ ⟨7, by decide⟩ p hp j hj hq fz1_23_7 fz2_23_7
  · exact match_zero_fix ⟨24, by decide⟩ ⟨7, by decide⟩ p hp j hj hq fz1_24_7 fz2_24_7
  · exact pair_25_7 p hp hrep j hj hq
  · exact match_zero_fix ⟨26, by decide⟩ ⟨7, by decide⟩ p hp j hj hq fz1_26_7 fz2_26_7
  · exact match_zero_fix ⟨27, by decide⟩ ⟨7, by decide⟩ p hp j hj hq fz1_27_7 fz2_27_7
  · exact match_zero_fix ⟨28, by decide⟩ ⟨7, by decide⟩ p hp j hj hq fz1_28_7 fz2_28_7
  · exact match_zero_fix ⟨29, by decide⟩ ⟨7, by decide⟩ p hp j hj hq fz1_29_7 fz2_29_7
  · exact match_zero_fix ⟨30, by decide⟩ ⟨7, by decide⟩ p hp j hj hq fz1_30_7 fz2_30_7
  · exact match_zero_fix ⟨31, by decide⟩ ⟨7, by decide⟩ p hp j hj hq fz1_31_7 fz2_31_7
  · exact match_zero_fix ⟨32, by decide⟩ ⟨7, by decide⟩ p hp j hj hq fz1_32_7 fz2_32_7
  · exact match_zero_fix ⟨33, by decide⟩ ⟨7, by decide⟩ p hp j hj hq fz1_33_7 fz2_33_7
  · exact match_zero_fix ⟨34, by decide⟩ ⟨7, by decide⟩ p hp j hj hq fz1_34_7 fz2_34_7
  · exact match_zero_fix ⟨35, by decide⟩ ⟨7, by decide⟩ p hp j hj hq fz1_35_7 fz2_35_7
  · exact match_zero_fix ⟨36, by decide⟩ ⟨7, by decide⟩ p hp j hj hq fz1_36_7 fz2_36_7
  · exact match_zero_fix ⟨37, by decide⟩ ⟨7, by decide⟩ p hp j hj hq fz1_37_7 fz2_37_7
  · exact match_zero_fix ⟨38, by decide⟩ ⟨7, by decide⟩ p hp j hj hq fz1_38_7 fz2_38_7
  · exact match_zero_fix ⟨39, by decide⟩ ⟨7, by decide⟩ p hp j hj hq fz1_39_7 fz2_39_7
  · exact match_zero_fix ⟨40, by decide⟩ ⟨7, by decide⟩ p hp j hj hq fz1_40_7 fz2_40_7
  · exact match_zero_fix ⟨41, by decide⟩ ⟨7, by decide⟩ p hp j hj hq fz1_41_7 fz2_41_7
  · exact match_zero_fix ⟨42, by decide⟩ ⟨7, by decide⟩ p hp j hj hq fz1_42_7 fz2_42_7
  · exact match_zero_fix ⟨43, by decide⟩ ⟨7, by decide⟩ p hp j hj hq fz1_43_7 fz2_43_7
  · exact match_zero_fix ⟨44, by decide⟩ ⟨7, by decide⟩ p hp j hj hq fz1_44_7 fz2_44_7
  · exact match_zero_fix ⟨45, by decide⟩ ⟨7, by decide⟩ p hp j hj hq fz1_45_7 fz2_45_7
  · exact match_zero_fix ⟨46, by decide⟩ ⟨7, by decide⟩ p hp j hj hq fz1_46_7 fz2_46_7
  · exact match_zero_fix ⟨47, by decide⟩ ⟨7, by decide⟩ p hp j hj hq fz1_47_7 fz2_47_7
  · exact match_zero_fix ⟨48, by decide⟩ ⟨7, by decide⟩ p hp j hj hq fz1_48_7 fz2_48_7
  · exact match_zero_fix ⟨49, by decide⟩ ⟨7, by decide⟩ p hp j hj hq fz1_49_7 fz2_49_7
  · exact match_zero_fix ⟨50, by decide⟩ ⟨7, by decide⟩ p hp j hj hq fz1_50_7 fz2_50_7
  · exact match_zero_fix ⟨51, by decide⟩ ⟨7, by decide⟩ p hp j hj hq fz1_51_7 fz2_51_7
  · exact match_zero_fix ⟨52, by decide⟩ ⟨7, by decide⟩ p hp j hj hq fz1_52_7 fz2_52_7
  · exact match_zero_fix ⟨53, by decide⟩ ⟨7, by decide⟩ p hp j hj hq fz1_53_7 fz2_53_7
  · exact match_zero_fix ⟨54, by decide⟩ ⟨7, by decide⟩ p hp j hj hq fz1_54_7 fz2_54_7
  · exact match_zero_fix ⟨55, by decide⟩ ⟨7, by decide⟩ p hp j hj hq fz1_55_7 fz2_55_7
  · exact match_zero_fix ⟨56, by decide⟩ ⟨7, by decide⟩ p hp j hj hq fz1_56_7 fz2_56_7
  · exact pair_57_7 p hp hrep j hj hq
  · exact match_zero_fix ⟨58, by decide⟩ ⟨7, by decide⟩ p hp j hj hq fz1_58_7 fz2_58_7
  · exact match_zero_fix ⟨59, by decide⟩ ⟨7, by decide⟩ p hp j hj hq fz1_59_7 fz2_59_7
  · exact match_zero_fix ⟨60, by decide⟩ ⟨7, by decide⟩ p hp j hj hq fz1_60_7 fz2_60_7
  · exact match_zero_fix ⟨61, by decide⟩ ⟨7, by decide⟩ p hp j hj hq fz1_61_7 fz2_61_7
  · exact pair_62_7 p hp hrep j hj hq
  · exact match_zero_fix ⟨63, by decide⟩ ⟨7, by decide⟩ p hp j hj hq fz1_63_7 fz2_63_7
  · exact match_zero_fix ⟨64, by decide⟩ ⟨7, by decide⟩ p hp j hj hq fz1_64_7 fz2_64_7
  · exact match_zero_fix ⟨65, by decide⟩ ⟨7, by decide⟩ p hp j hj hq fz1_65_7 fz2_65_7
  · exact match_zero_fix ⟨66, by decide⟩ ⟨7, by decide⟩ p hp j hj hq fz1_66_7 fz2_66_7
  · exact pair_67_7 p hp hrep j hj hq
  · exact match_zero_fix ⟨68, by decide⟩ ⟨7, by decide⟩ p hp j hj hq fz1_68_7 fz2_68_7
  · exact match_zero_fix ⟨69, by decide⟩ ⟨7, by decide⟩ p hp j hj hq fz1_69_7 fz2_69_7
  · exact match_zero_fix ⟨70, by decide⟩ ⟨7, by decide⟩ p hp j hj hq fz1_70_7 fz2_70_7
  · exact match_zero_fix ⟨71, by decide⟩ ⟨7, by decide⟩ p hp j hj hq fz1_71_7 fz2_71_7
  · exact pair_72_7 p hp hrep j hj hq
  · exact match_zero_fix ⟨73, by decide⟩ ⟨7, by decide⟩ p hp j hj hq fz1_73_7 fz2_73_7
  · exact match_zero_fix ⟨74, by decide⟩ ⟨7, by decide⟩ p hp j hj hq fz1_74_7 fz2_74_7
  · exact match_zero_fix ⟨75, by decide⟩ ⟨7, by decide⟩ p hp j hj hq fz1_75_7 fz2_75_7
  · exact match_zero_fix ⟨76, by decide⟩ ⟨7, by decide⟩ p hp j hj hq fz1_76_7 fz2_76_7
  · exact pair_77_7 p hp hrep j hj hq
  · exact match_zero_fix ⟨78, by decide⟩ ⟨7, by decide⟩ p hp j hj hq fz1_78_7 fz2_78_7
  · exact match_zero_fix ⟨79, by decide⟩ ⟨7, by decide⟩ p hp j hj hq fz1_79_7 fz2_79_7
  · exact pair_80_7 p hp hrep j hj hq
  · exact match_zero_fix ⟨81, by decide⟩ ⟨7, by decide⟩ p hp j hj hq fz1_81_7 fz2_81_7
  · exact match_zero_fix ⟨82, by decide⟩ ⟨7, by decide⟩ p hp j hj hq fz1_82_7 fz2_82_7
  · exact match_zero_fix ⟨83, by decide⟩ ⟨7, by decide⟩ p hp j hj hq fz1_83_7 fz2_83_7
  · exact match_zero_fix ⟨84, by decide⟩ ⟨7, by decide⟩ p hp j hj hq fz1_84_7 fz2_84_7
  · exact match_zero_fix ⟨85, by decide⟩ ⟨7, by decide⟩ p hp j hj hq fz1_85_7 fz2_85_7
  · exact match_zero_fix ⟨86, by decide⟩ ⟨7, by decide⟩ p hp j hj hq fz1_86_7 fz2_86_7
  · exact pair_87_7 p hp hrep j hj hq
  · exact match_zero_fix ⟨88, by decide⟩ ⟨7, by decide⟩ p hp j hj hq fz1_88_7 fz2_88_7
  · exact match_zero_fix ⟨89, by decide⟩ ⟨7, by decide⟩ p hp j hj hq fz1_89_7 fz2_89_7
  · exact match_zero_fix ⟨90, by decide⟩ ⟨7, by decide⟩ p hp j hj hq fz1_90_7 fz2_90_7
  · exact match_zero_fix ⟨91, by decide⟩ ⟨7, by decide⟩ p hp j hj hq fz1_91_7 fz2_91_7
  · exact match_zero_fix ⟨92, by decide⟩ ⟨7, by decide⟩ p hp j hj hq fz1_92_7 fz2_92_7
  · exact match_zero_fix ⟨93, by decide⟩ ⟨7, by decide⟩ p hp j hj hq fz1_93_7 fz2_93_7
  · exact match_zero_fix ⟨94, by decide⟩ ⟨7, by decide⟩ p hp j hj hq fz1_94_7 fz2_94_7
  · exact match_zero_fix ⟨95, by decide⟩ ⟨7, by decide⟩ p hp j hj hq fz1_95_7 fz2_95_7
  · exact match_zero_fix ⟨96, by decide⟩ ⟨7, by decide⟩ p hp j hj hq fz1_96_7 fz2_96_7
  · exact match_zero_fix ⟨97, by decide⟩ ⟨7, by decide⟩ p hp j hj hq fz1_97_7 fz2_97_7
  · exact match_zero_fix ⟨98, by decide⟩ ⟨7, by decide⟩ p hp j hj hq fz1_98_7 fz2_98_7
  · exact match_zero_fix ⟨99, by decide⟩ ⟨7, by decide⟩ p hp j hj hq fz1_99_7 fz2_99_7
  · exact match_zero_fix ⟨100, by decide⟩ ⟨7, by decide⟩ p hp j hj hq fz1_100_7 fz2_100_7
  · exact match_zero_fix ⟨101, by decide⟩ ⟨7, by decide⟩ p hp j hj hq fz1_101_7 fz2_101_7
  · exact match_zero_fix ⟨102, by decide⟩ ⟨7, by decide⟩ p hp j hj hq fz1_102_7 fz2_102_7
  · exact match_zero_fix ⟨103, by decide⟩ ⟨7, by decide⟩ p hp j hj hq fz1_103_7 fz2_103_7
  · exact match_zero_fix ⟨104, by decide⟩ ⟨7, by decide⟩ p hp j hj hq fz1_104_7 fz2_104_7
  · exact match_zero_fix ⟨105, by decide⟩ ⟨7, by decide⟩ p hp j hj hq fz1_105_7 fz2_105_7
  · exact match_zero_fix ⟨106, by decide⟩ ⟨7, by decide⟩ p hp j hj hq fz1_106_7 fz2_106_7
  · exact match_zero_fix ⟨107, by decide⟩ ⟨7, by decide⟩ p hp j hj hq fz1_107_7 fz2_107_7
  · exact match_zero_fix ⟨108, by decide⟩ ⟨7, by decide⟩ p hp j hj hq fz1_108_7 fz2_108_7
  · exact match_zero_fix ⟨109, by decide⟩ ⟨7, by decide⟩ p hp j hj hq fz1_109_7 fz2_109_7
  · exact match_zero_fix ⟨110, by decide⟩ ⟨7, by decide⟩ p hp j hj hq fz1_110_7 fz2_110_7
  · exact match_zero_fix ⟨111, by decide⟩ ⟨7, by decide⟩ p hp j hj hq fz1_111_7 fz2_111_7
  · exact match_zero_fix ⟨112, by decide⟩ ⟨7, by decide⟩ p hp j hj hq fz1_112_7 fz2_112_7
  · exact match_zero_fix ⟨113, by decide⟩ ⟨7, by decide⟩ p hp j hj hq fz1_113_7 fz2_113_7
  · exact match_zero_fix ⟨114, by decide⟩ ⟨7, by decide⟩ p hp j hj hq fz1_114_7 fz2_114_7
  · exact match_zero_fix ⟨115, by decide⟩ ⟨7, by decide⟩ p hp j hj hq fz1_115_7 fz2_115_7
  · exact pair_116_7 p hp hrep j hj hq
  · exact pair_117_7 p hp hrep j hj hq
  · exact pair_118_7 p hp hrep j hj hq
  · exact pair_119_7 p hp hrep j hj hq
  · exact pair_120_7 p hp hrep j hj hq
  · exact match_zero_fix ⟨121, by decide⟩ ⟨7, by decide⟩ p hp j hj hq fz1_121_7 fz2_121_7
  · exact match_zero_fix ⟨122, by decide⟩ ⟨7, by decide⟩ p hp j hj hq fz1_122_7 fz2_122_7
  · exact match_zero_fix ⟨123, by decide⟩ ⟨7, by decide⟩ p hp j hj hq fz1_123_7 fz2_123_7
  · exact match_zero_fix ⟨124, by decide⟩ ⟨7, by decide⟩ p hp j hj hq fz1_124_7 fz2_124_7
  · exact match_zero_fix ⟨125, by decide⟩ ⟨7, by decide⟩ p hp j hj hq fz1_125_7 fz2_125_7
  · exact match_zero_fix ⟨126, by decide⟩ ⟨7, by decide⟩ p hp j hj hq fz1_126_7 fz2_126_7
  · exact match_zero_fix ⟨127, by decide⟩ ⟨7, by decide⟩ p hp j hj hq fz1_127_7 fz2_127_7
  · exact match_zero_fix ⟨128, by decide⟩ ⟨7, by decide⟩ p hp j hj hq fz1_128_7 fz2_128_7
  · exact match_zero_fix ⟨129, by decide⟩ ⟨7, by decide⟩ p hp j hj hq fz1_129_7 fz2_129_7
  · exact match_zero_fix ⟨130, by decide⟩ ⟨7, by decide⟩ p hp j hj hq fz1_130_7 fz2_130_7
  · exact match_zero_fix ⟨131, by decide⟩ ⟨7, by decide⟩ p hp j hj hq fz1_131_7 fz2_131_7
  · exact match_zero_fix ⟨132, by decide⟩ ⟨7, by decide⟩ p hp j hj hq fz1_132_7 fz2_132_7
  · exact match_zero_fix ⟨133, by decide⟩ ⟨7, by decide⟩ p hp j hj hq fz1_133_7 fz2_133_7
  · exact match_zero_fix ⟨134, by decide⟩ ⟨7, by decide⟩ p hp j hj hq fz1_134_7 fz2_134_7
  · exact match_zero_fix ⟨135, by decide⟩ ⟨7, by decide⟩ p hp j hj hq fz1_135_7 fz2_135_7
  · exact match_zero_fix ⟨136, by decide⟩ ⟨7, by decide⟩ p hp j hj hq fz1_136_7 fz2_136_7
  · exact match_zero_fix ⟨137, by decide⟩ ⟨7, by decide⟩ p hp j hj hq fz1_137_7 fz2_137_7
  · exact match_zero_fix ⟨138, by decide⟩ ⟨7, by decide⟩ p hp j hj hq fz1_138_7 fz2_138_7
  · exact match_zero_fix ⟨139, by decide⟩ ⟨7, by decide⟩ p hp j hj hq fz1_139_7 fz2_139_7
  · exact match_zero_fix ⟨140, by decide⟩ ⟨7, by decide⟩ p hp j hj hq fz1_140_7 fz2_140_7
  · exact pair_141_7 p hp hrep j hj hq
  · exact match_zero_fix ⟨142, by decide⟩ ⟨7, by decide⟩ p hp j hj hq fz1_142_7 fz2_142_7
  · exact match_zero_fix ⟨143, by decide⟩ ⟨7, by decide⟩ p hp j hj hq fz1_143_7 fz2_143_7
  · exact match_zero_fix ⟨144, by decide⟩ ⟨7, by decide⟩ p hp j hj hq fz1_144_7 fz2_144_7
  · exact match_zero_fix ⟨145, by decide⟩ ⟨7, by decide⟩ p hp j hj hq fz1_145_7 fz2_145_7
  · exact match_zero_fix ⟨146, by decide⟩ ⟨7, by decide⟩ p hp j hj hq fz1_146_7 fz2_146_7
  · exact pair_147_7 p hp hrep j hj hq

end LeanDring.P5Presentation
