/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.Characters.Twin2.CharComplete
import LeanDring.P5.Certificate.Characters.Twin2.CharBoxReps

/-!
# Full, unconditional q=2 completeness of the certified character enumeration (Step 3, done)

The q=2 twin of `LeanDring/P5/Certificate/Characters/Twin1/CharCompleteFinal.lean`. Combines the `k
≤ 3` brute-`decide` certificate
`charsAtComplete2_le115` with the 32 q=2 row-combination certificates
(`charsAtComplete2_116 … charsAtComplete2_147`) for the `k ≥ 4` classes into the
unconditional `CharsAtComplete r` for *every* q=2 representative `r`. This closes the
Step-2 converse: the certified list `charsAt2 r` enumerates *all* linear characters
of `reps r`, so `|Hom(reps r, ℂˣ)|` and `|(reps r)ᵃᵇ|` equal the certified count
`charCounts r` with no hypothesis — for the q=2 twin SmallGroup(3125,69).
-/

namespace LeanDring.P5Presentation

namespace Q2

/-- **Completeness for every q=2 representative** (`r : Fin 148`), unconditional.
`k ≤ 3` via brute enumeration, `k ≥ 4` via the q=2 row-combination certificate. -/
theorem charsAtComplete_all2 (r : Fin 148) : CharsAtComplete r := by
  rcases lt_or_ge r.val 116 with h | h
  · exact charsAtComplete2_le115 r h
  · have hub : r.val < 148 := r.isLt
    interval_cases hh : r.val
    · rw [show r = ⟨116, by norm_num⟩ from Fin.ext hh]; exact charsAtComplete2_116
    · rw [show r = ⟨117, by norm_num⟩ from Fin.ext hh]; exact charsAtComplete2_117
    · rw [show r = ⟨118, by norm_num⟩ from Fin.ext hh]; exact charsAtComplete2_118
    · rw [show r = ⟨119, by norm_num⟩ from Fin.ext hh]; exact charsAtComplete2_119
    · rw [show r = ⟨120, by norm_num⟩ from Fin.ext hh]; exact charsAtComplete2_120
    · rw [show r = ⟨121, by norm_num⟩ from Fin.ext hh]; exact charsAtComplete2_121
    · rw [show r = ⟨122, by norm_num⟩ from Fin.ext hh]; exact charsAtComplete2_122
    · rw [show r = ⟨123, by norm_num⟩ from Fin.ext hh]; exact charsAtComplete2_123
    · rw [show r = ⟨124, by norm_num⟩ from Fin.ext hh]; exact charsAtComplete2_124
    · rw [show r = ⟨125, by norm_num⟩ from Fin.ext hh]; exact charsAtComplete2_125
    · rw [show r = ⟨126, by norm_num⟩ from Fin.ext hh]; exact charsAtComplete2_126
    · rw [show r = ⟨127, by norm_num⟩ from Fin.ext hh]; exact charsAtComplete2_127
    · rw [show r = ⟨128, by norm_num⟩ from Fin.ext hh]; exact charsAtComplete2_128
    · rw [show r = ⟨129, by norm_num⟩ from Fin.ext hh]; exact charsAtComplete2_129
    · rw [show r = ⟨130, by norm_num⟩ from Fin.ext hh]; exact charsAtComplete2_130
    · rw [show r = ⟨131, by norm_num⟩ from Fin.ext hh]; exact charsAtComplete2_131
    · rw [show r = ⟨132, by norm_num⟩ from Fin.ext hh]; exact charsAtComplete2_132
    · rw [show r = ⟨133, by norm_num⟩ from Fin.ext hh]; exact charsAtComplete2_133
    · rw [show r = ⟨134, by norm_num⟩ from Fin.ext hh]; exact charsAtComplete2_134
    · rw [show r = ⟨135, by norm_num⟩ from Fin.ext hh]; exact charsAtComplete2_135
    · rw [show r = ⟨136, by norm_num⟩ from Fin.ext hh]; exact charsAtComplete2_136
    · rw [show r = ⟨137, by norm_num⟩ from Fin.ext hh]; exact charsAtComplete2_137
    · rw [show r = ⟨138, by norm_num⟩ from Fin.ext hh]; exact charsAtComplete2_138
    · rw [show r = ⟨139, by norm_num⟩ from Fin.ext hh]; exact charsAtComplete2_139
    · rw [show r = ⟨140, by norm_num⟩ from Fin.ext hh]; exact charsAtComplete2_140
    · rw [show r = ⟨141, by norm_num⟩ from Fin.ext hh]; exact charsAtComplete2_141
    · rw [show r = ⟨142, by norm_num⟩ from Fin.ext hh]; exact charsAtComplete2_142
    · rw [show r = ⟨143, by norm_num⟩ from Fin.ext hh]; exact charsAtComplete2_143
    · rw [show r = ⟨144, by norm_num⟩ from Fin.ext hh]; exact charsAtComplete2_144
    · rw [show r = ⟨145, by norm_num⟩ from Fin.ext hh]; exact charsAtComplete2_145
    · rw [show r = ⟨146, by norm_num⟩ from Fin.ext hh]; exact charsAtComplete2_146
    · rw [show r = ⟨147, by norm_num⟩ from Fin.ext hh]; exact charsAtComplete2_147

/-- **Character count, unconditional for all 148 q=2 representatives.** -/
theorem charsAt_complete_all2 (r : Fin 148) :
    Nat.card (↥(reps r) →* ℂˣ) = charCounts.getD r.val 0 :=
  charsAt_complete r (charsAtComplete_all2 r)

/-- **Abelianization order, unconditional for all 148 q=2 representatives.** The
generator-emitted count `charCounts r` is the genuine abelianization order of the
q=2 subgroup `reps r`. -/
theorem card_abelianization_reps_all2 (r : Fin 148) :
    Nat.card (Abelianization ↥(reps r)) = charCounts.getD r.val 0 :=
  card_abelianization_reps r (charsAtComplete_all2 r)

end Q2

end LeanDring.P5Presentation
