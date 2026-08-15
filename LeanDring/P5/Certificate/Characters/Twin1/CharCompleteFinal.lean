/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.Characters.Twin1.CharCompleteStage3
import LeanDring.P5.Certificate.Characters.Twin1.CharBoxReps

/-!
# Full, unconditional completeness of the certified character enumeration

Combines the `k ≤ 3` brute-`decide` certificates (`charsAtComplete_le115`) with the
32 row-combination certificates (`charsAtComplete_116 … charsAtComplete_147`) for
the `k ≥ 4` classes into the unconditional `CharsAtComplete r` for *every*
representative `r`. This closes the converse: the certified list `charsAt r`
enumerates *all* linear characters of `reps r`, so `|Hom(reps r, ℂˣ)|` and
`|(reps r)ᵃᵇ|` equal the certified count `charCounts r` with no hypothesis.
-/

namespace LeanDring.P5Presentation

/-- **Completeness for every representative** (`r : Fin 148`), unconditional.
`k ≤ 3` via brute enumeration, `k ≥ 4` via the row-combination certificate. -/
theorem charsAtComplete_all (r : Fin 148) : CharsAtComplete r := by
  rcases lt_or_ge r.val 116 with h | h
  · exact charsAtComplete_le115 r h
  · have hub : r.val < 148 := r.isLt
    interval_cases hh : r.val
    · rw [show r = ⟨116, by norm_num⟩ from Fin.ext hh]; exact charsAtComplete_116
    · rw [show r = ⟨117, by norm_num⟩ from Fin.ext hh]; exact charsAtComplete_117
    · rw [show r = ⟨118, by norm_num⟩ from Fin.ext hh]; exact charsAtComplete_118
    · rw [show r = ⟨119, by norm_num⟩ from Fin.ext hh]; exact charsAtComplete_119
    · rw [show r = ⟨120, by norm_num⟩ from Fin.ext hh]; exact charsAtComplete_120
    · rw [show r = ⟨121, by norm_num⟩ from Fin.ext hh]; exact charsAtComplete_121
    · rw [show r = ⟨122, by norm_num⟩ from Fin.ext hh]; exact charsAtComplete_122
    · rw [show r = ⟨123, by norm_num⟩ from Fin.ext hh]; exact charsAtComplete_123
    · rw [show r = ⟨124, by norm_num⟩ from Fin.ext hh]; exact charsAtComplete_124
    · rw [show r = ⟨125, by norm_num⟩ from Fin.ext hh]; exact charsAtComplete_125
    · rw [show r = ⟨126, by norm_num⟩ from Fin.ext hh]; exact charsAtComplete_126
    · rw [show r = ⟨127, by norm_num⟩ from Fin.ext hh]; exact charsAtComplete_127
    · rw [show r = ⟨128, by norm_num⟩ from Fin.ext hh]; exact charsAtComplete_128
    · rw [show r = ⟨129, by norm_num⟩ from Fin.ext hh]; exact charsAtComplete_129
    · rw [show r = ⟨130, by norm_num⟩ from Fin.ext hh]; exact charsAtComplete_130
    · rw [show r = ⟨131, by norm_num⟩ from Fin.ext hh]; exact charsAtComplete_131
    · rw [show r = ⟨132, by norm_num⟩ from Fin.ext hh]; exact charsAtComplete_132
    · rw [show r = ⟨133, by norm_num⟩ from Fin.ext hh]; exact charsAtComplete_133
    · rw [show r = ⟨134, by norm_num⟩ from Fin.ext hh]; exact charsAtComplete_134
    · rw [show r = ⟨135, by norm_num⟩ from Fin.ext hh]; exact charsAtComplete_135
    · rw [show r = ⟨136, by norm_num⟩ from Fin.ext hh]; exact charsAtComplete_136
    · rw [show r = ⟨137, by norm_num⟩ from Fin.ext hh]; exact charsAtComplete_137
    · rw [show r = ⟨138, by norm_num⟩ from Fin.ext hh]; exact charsAtComplete_138
    · rw [show r = ⟨139, by norm_num⟩ from Fin.ext hh]; exact charsAtComplete_139
    · rw [show r = ⟨140, by norm_num⟩ from Fin.ext hh]; exact charsAtComplete_140
    · rw [show r = ⟨141, by norm_num⟩ from Fin.ext hh]; exact charsAtComplete_141
    · rw [show r = ⟨142, by norm_num⟩ from Fin.ext hh]; exact charsAtComplete_142
    · rw [show r = ⟨143, by norm_num⟩ from Fin.ext hh]; exact charsAtComplete_143
    · rw [show r = ⟨144, by norm_num⟩ from Fin.ext hh]; exact charsAtComplete_144
    · rw [show r = ⟨145, by norm_num⟩ from Fin.ext hh]; exact charsAtComplete_145
    · rw [show r = ⟨146, by norm_num⟩ from Fin.ext hh]; exact charsAtComplete_146
    · rw [show r = ⟨147, by norm_num⟩ from Fin.ext hh]; exact charsAtComplete_147

/-- **Character count, unconditional for all 148 representatives.** The number of
linear characters of `reps r` equals its certified count `charCounts r`. -/
theorem charsAt_complete_all (r : Fin 148) :
    Nat.card (↥(reps r) →* ℂˣ) = charCounts.getD r.val 0 :=
  charsAt_complete r (charsAtComplete_all r)

/-- **Abelianization order, unconditional for all 148 representatives.** The
generator-emitted count `charCounts r` is the genuine abelianization order of
`reps r`. -/
theorem card_abelianization_reps_all (r : Fin 148) :
    Nat.card (Abelianization ↥(reps r)) = charCounts.getD r.val 0 :=
  card_abelianization_reps r (charsAtComplete_all r)

end LeanDring.P5Presentation
