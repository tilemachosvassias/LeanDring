/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.Characters.Twin1.CharComplete
import LeanDring.P5.Certificate.Characters.Twin1.CharComplete.Chunk01
import LeanDring.P5.Certificate.Characters.Twin1.CharComplete.Chunk02
import LeanDring.P5.Certificate.Characters.Twin1.CharComplete.Chunk03
import LeanDring.P5.Certificate.Characters.Twin1.CharComplete.Chunk04
import LeanDring.P5.Certificate.Characters.Twin1.CharComplete.Chunk05
import LeanDring.P5.Certificate.Characters.Twin1.CharComplete.Chunk06
import LeanDring.P5.Certificate.Characters.Twin1.CharComplete.Chunk07
import LeanDring.P5.Certificate.Characters.Twin1.CharComplete.Chunk08

/-!
# Discharging `CharsAtComplete` by decided exhaustiveness (assembly for `k ≤ 3`)

Combines the `k ≤ 2` exhaustiveness certificate `exhaustiveCheck_le54`
(representatives `0…54`) with the eight `k = 3` chunk certificates
`exhaustiveCheck_r55_62 … exhaustiveCheck_r111_115` (representatives `55…115`)
into a single exhaustiveness fact for every representative `r < 116`, and derives
the corresponding unconditional character-count / abelianization-order statements,
following the `_le54` pattern of
`LeanDring.P5.Certificate.Characters.Twin1.CharComplete` exactly.
-/

namespace LeanDring.P5Presentation

/-- **Exhaustiveness for every representative `r < 116`** (the `k ≤ 3` classes),
assembled from the `k ≤ 2` certificate `exhaustiveCheck_le54` and the eight
`k = 3` chunk certificates. -/
theorem exhaustiveCheck_le115 : ∀ r : ℕ, r < 116 → exhaustiveCheck r = true := by
  intro r hr
  by_cases h55 : r < 55
  · exact (List.all_eq_true.mp exhaustiveCheck_le54) r (List.mem_range.mpr h55)
  by_cases h63 : r < 63
  · exact (List.all_eq_true.mp exhaustiveCheck_r55_62) r
      (List.mem_range'_1.mpr ⟨by omega, by omega⟩)
  by_cases h71 : r < 71
  · exact (List.all_eq_true.mp exhaustiveCheck_r63_70) r
      (List.mem_range'_1.mpr ⟨by omega, by omega⟩)
  by_cases h79 : r < 79
  · exact (List.all_eq_true.mp exhaustiveCheck_r71_78) r
      (List.mem_range'_1.mpr ⟨by omega, by omega⟩)
  by_cases h87 : r < 87
  · exact (List.all_eq_true.mp exhaustiveCheck_r79_86) r
      (List.mem_range'_1.mpr ⟨by omega, by omega⟩)
  by_cases h95 : r < 95
  · exact (List.all_eq_true.mp exhaustiveCheck_r87_94) r
      (List.mem_range'_1.mpr ⟨by omega, by omega⟩)
  by_cases h103 : r < 103
  · exact (List.all_eq_true.mp exhaustiveCheck_r95_102) r
      (List.mem_range'_1.mpr ⟨by omega, by omega⟩)
  by_cases h111 : r < 111
  · exact (List.all_eq_true.mp exhaustiveCheck_r103_110) r
      (List.mem_range'_1.mpr ⟨by omega, by omega⟩)
  · exact (List.all_eq_true.mp exhaustiveCheck_r111_115) r
      (List.mem_range'_1.mpr ⟨by omega, by omega⟩)

/-- **Completeness for every `k ≤ 3` representative** (`r < 116`). -/
theorem charsAtComplete_le115 (r : Fin 148) (hr : r.val < 116) : CharsAtComplete r :=
  charsAtComplete_of_check r (exhaustiveCheck_le115 r.val hr)

/-- **Character count, unconditional for the `k ≤ 3` classes.** The number of
linear characters of `reps r` equals its certified count `charCounts r`. -/
theorem charsAt_complete_le115 (r : Fin 148) (hr : r.val < 116) :
    Nat.card (↥(reps r) →* ℂˣ) = charCounts.getD r.val 0 :=
  charsAt_complete r (charsAtComplete_le115 r hr)

/-- **Abelianization order, unconditional for the `k ≤ 3` classes.** -/
theorem card_abelianization_reps_le115 (r : Fin 148) (hr : r.val < 116) :
    Nat.card (Abelianization ↥(reps r)) = charCounts.getD r.val 0 :=
  card_abelianization_reps r (charsAtComplete_le115 r hr)

end LeanDring.P5Presentation
