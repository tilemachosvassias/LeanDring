/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Data.MatchMaster.C001
import LeanDring.P5.Data.MatchMaster.C002
import LeanDring.P5.Data.MatchMaster.C011
import LeanDring.P5.Data.MatchMaster.C012
import LeanDring.P5.Data.MatchMaster.C013
import LeanDring.P5.Data.MatchMaster.C014
import LeanDring.P5.Data.MatchMaster.C015
import LeanDring.P5.Data.MatchMaster.C016
import LeanDring.P5.Data.MatchMaster.C017
import LeanDring.P5.Data.MatchMaster.C018
import LeanDring.P5.Data.MatchMaster.C019
import LeanDring.P5.Data.MatchMaster.C003
import LeanDring.P5.Data.MatchMaster.C004
import LeanDring.P5.Data.MatchMaster.C005
import LeanDring.P5.Data.MatchMaster.C006
import LeanDring.P5.Data.MatchMaster.C007
import LeanDring.P5.Data.MatchMaster.C008
import LeanDring.P5.Data.MatchMaster.C009
import LeanDring.P5.Data.MatchMaster.C010

/-!
# Stage-5 — the master cell theorem

Every orbit-representative column of `Coordinate 2` agrees, on every pair-class
row, with the `Coordinate 1` column of the SAME index, the rows being matched by
the alignment `alnPos` (i.e. by `σ`).  148-way dispatch on the column class.
Auto-emitted by `python/p5_match_emit.py`.
-/

namespace LeanDring.P5Presentation

open MulAction Finset LeanDring.DRing LeanDring.MonGSet

set_option maxRecDepth 100000
set_option linter.style.setOption false
set_option linter.style.longLine false

set_option maxHeartbeats 4000000 in
-- kernel decide over large certified lists needs extra heartbeats
theorem master (rH : Fin 148) (p : Nat) (hp : p < (Q2.transData.getD rH.val []).length)
    (hrep : (Q2.cosetIsRep.getD rH.val []).getD p false = true)
    (rK : Fin 148) (j : Nat) (hj : j < (repChars.getD rK.val []).length)
    (hq : (normIsRep.getD rK.val []).getD j false = true) :
    species (Q2.reps rH) (colE2 rH p hp) (rowE2 rK j hj hq)
      = species (reps rH) (colE1 rH p (transLenTr rH p hp)) (rowE1 rK j hj) := by
  rcases rH with ⟨nH, hnH⟩; interval_cases nH
  · exact master_0 p hp hrep rK j hj hq
  · exact master_1 p hp hrep rK j hj hq
  · exact master_2 p hp hrep rK j hj hq
  · exact master_3 p hp hrep rK j hj hq
  · exact master_4 p hp hrep rK j hj hq
  · exact master_5 p hp hrep rK j hj hq
  · exact master_6 p hp hrep rK j hj hq
  · exact master_7 p hp hrep rK j hj hq
  · exact master_8 p hp hrep rK j hj hq
  · exact master_9 p hp hrep rK j hj hq
  · exact master_10 p hp hrep rK j hj hq
  · exact master_11 p hp hrep rK j hj hq
  · exact master_12 p hp hrep rK j hj hq
  · exact master_13 p hp hrep rK j hj hq
  · exact master_14 p hp hrep rK j hj hq
  · exact master_15 p hp hrep rK j hj hq
  · exact master_16 p hp hrep rK j hj hq
  · exact master_17 p hp hrep rK j hj hq
  · exact master_18 p hp hrep rK j hj hq
  · exact master_19 p hp hrep rK j hj hq
  · exact master_20 p hp hrep rK j hj hq
  · exact master_21 p hp hrep rK j hj hq
  · exact master_22 p hp hrep rK j hj hq
  · exact master_23 p hp hrep rK j hj hq
  · exact master_24 p hp hrep rK j hj hq
  · exact master_25 p hp hrep rK j hj hq
  · exact master_26 p hp hrep rK j hj hq
  · exact master_27 p hp hrep rK j hj hq
  · exact master_28 p hp hrep rK j hj hq
  · exact master_29 p hp hrep rK j hj hq
  · exact master_30 p hp hrep rK j hj hq
  · exact master_31 p hp hrep rK j hj hq
  · exact master_32 p hp hrep rK j hj hq
  · exact master_33 p hp hrep rK j hj hq
  · exact master_34 p hp hrep rK j hj hq
  · exact master_35 p hp hrep rK j hj hq
  · exact master_36 p hp hrep rK j hj hq
  · exact master_37 p hp hrep rK j hj hq
  · exact master_38 p hp hrep rK j hj hq
  · exact master_39 p hp hrep rK j hj hq
  · exact master_40 p hp hrep rK j hj hq
  · exact master_41 p hp hrep rK j hj hq
  · exact master_42 p hp hrep rK j hj hq
  · exact master_43 p hp hrep rK j hj hq
  · exact master_44 p hp hrep rK j hj hq
  · exact master_45 p hp hrep rK j hj hq
  · exact master_46 p hp hrep rK j hj hq
  · exact master_47 p hp hrep rK j hj hq
  · exact master_48 p hp hrep rK j hj hq
  · exact master_49 p hp hrep rK j hj hq
  · exact master_50 p hp hrep rK j hj hq
  · exact master_51 p hp hrep rK j hj hq
  · exact master_52 p hp hrep rK j hj hq
  · exact master_53 p hp hrep rK j hj hq
  · exact master_54 p hp hrep rK j hj hq
  · exact master_55 p hp hrep rK j hj hq
  · exact master_56 p hp hrep rK j hj hq
  · exact master_57 p hp hrep rK j hj hq
  · exact master_58 p hp hrep rK j hj hq
  · exact master_59 p hp hrep rK j hj hq
  · exact master_60 p hp hrep rK j hj hq
  · exact master_61 p hp hrep rK j hj hq
  · exact master_62 p hp hrep rK j hj hq
  · exact master_63 p hp hrep rK j hj hq
  · exact master_64 p hp hrep rK j hj hq
  · exact master_65 p hp hrep rK j hj hq
  · exact master_66 p hp hrep rK j hj hq
  · exact master_67 p hp hrep rK j hj hq
  · exact master_68 p hp hrep rK j hj hq
  · exact master_69 p hp hrep rK j hj hq
  · exact master_70 p hp hrep rK j hj hq
  · exact master_71 p hp hrep rK j hj hq
  · exact master_72 p hp hrep rK j hj hq
  · exact master_73 p hp hrep rK j hj hq
  · exact master_74 p hp hrep rK j hj hq
  · exact master_75 p hp hrep rK j hj hq
  · exact master_76 p hp hrep rK j hj hq
  · exact master_77 p hp hrep rK j hj hq
  · exact master_78 p hp hrep rK j hj hq
  · exact master_79 p hp hrep rK j hj hq
  · exact master_80 p hp hrep rK j hj hq
  · exact master_81 p hp hrep rK j hj hq
  · exact master_82 p hp hrep rK j hj hq
  · exact master_83 p hp hrep rK j hj hq
  · exact master_84 p hp hrep rK j hj hq
  · exact master_85 p hp hrep rK j hj hq
  · exact master_86 p hp hrep rK j hj hq
  · exact master_87 p hp hrep rK j hj hq
  · exact master_88 p hp hrep rK j hj hq
  · exact master_89 p hp hrep rK j hj hq
  · exact master_90 p hp hrep rK j hj hq
  · exact master_91 p hp hrep rK j hj hq
  · exact master_92 p hp hrep rK j hj hq
  · exact master_93 p hp hrep rK j hj hq
  · exact master_94 p hp hrep rK j hj hq
  · exact master_95 p hp hrep rK j hj hq
  · exact master_96 p hp hrep rK j hj hq
  · exact master_97 p hp hrep rK j hj hq
  · exact master_98 p hp hrep rK j hj hq
  · exact master_99 p hp hrep rK j hj hq
  · exact master_100 p hp hrep rK j hj hq
  · exact master_101 p hp hrep rK j hj hq
  · exact master_102 p hp hrep rK j hj hq
  · exact master_103 p hp hrep rK j hj hq
  · exact master_104 p hp hrep rK j hj hq
  · exact master_105 p hp hrep rK j hj hq
  · exact master_106 p hp hrep rK j hj hq
  · exact master_107 p hp hrep rK j hj hq
  · exact master_108 p hp hrep rK j hj hq
  · exact master_109 p hp hrep rK j hj hq
  · exact master_110 p hp hrep rK j hj hq
  · exact master_111 p hp hrep rK j hj hq
  · exact master_112 p hp hrep rK j hj hq
  · exact master_113 p hp hrep rK j hj hq
  · exact master_114 p hp hrep rK j hj hq
  · exact master_115 p hp hrep rK j hj hq
  · exact master_116 p hp hrep rK j hj hq
  · exact master_117 p hp hrep rK j hj hq
  · exact master_118 p hp hrep rK j hj hq
  · exact master_119 p hp hrep rK j hj hq
  · exact master_120 p hp hrep rK j hj hq
  · exact master_121 p hp hrep rK j hj hq
  · exact master_122 p hp hrep rK j hj hq
  · exact master_123 p hp hrep rK j hj hq
  · exact master_124 p hp hrep rK j hj hq
  · exact master_125 p hp hrep rK j hj hq
  · exact master_126 p hp hrep rK j hj hq
  · exact master_127 p hp hrep rK j hj hq
  · exact master_128 p hp hrep rK j hj hq
  · exact master_129 p hp hrep rK j hj hq
  · exact master_130 p hp hrep rK j hj hq
  · exact master_131 p hp hrep rK j hj hq
  · exact master_132 p hp hrep rK j hj hq
  · exact master_133 p hp hrep rK j hj hq
  · exact master_134 p hp hrep rK j hj hq
  · exact master_135 p hp hrep rK j hj hq
  · exact master_136 p hp hrep rK j hj hq
  · exact master_137 p hp hrep rK j hj hq
  · exact master_138 p hp hrep rK j hj hq
  · exact master_139 p hp hrep rK j hj hq
  · exact master_140 p hp hrep rK j hj hq
  · exact master_141 p hp hrep rK j hj hq
  · exact master_142 p hp hrep rK j hj hq
  · exact master_143 p hp hrep rK j hj hq
  · exact master_144 p hp hrep rK j hj hq
  · exact master_145 p hp hrep rK j hj hq
  · exact master_146 p hp hrep rK j hj hq
  · exact master_147 p hp hrep rK j hj hq

end LeanDring.P5Presentation
