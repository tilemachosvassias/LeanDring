/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.Characters.Twin2.CharComplete.Chunk01
import LeanDring.P5.Certificate.Characters.Twin2.CharComplete.Chunk02
import LeanDring.P5.Certificate.Characters.Twin2.CharComplete.Chunk03
import LeanDring.P5.Certificate.Characters.Twin2.CharComplete.Chunk04
import LeanDring.P5.Certificate.Characters.Twin2.CharComplete.Chunk05
import LeanDring.P5.Certificate.Characters.Twin2.CharComplete.Chunk06
import LeanDring.P5.Certificate.Characters.Twin2.CharComplete.Chunk07
import LeanDring.P5.Certificate.Characters.Twin2.CharComplete.Chunk08

/-!
# Discharging q=2 `CharsAtComplete` by decided exhaustiveness (Step 3, `k ≤ 3`)

The q=2 twin of `LeanDring/P5/Certificate/Characters/Twin1/CharComplete.lean` +
`LeanDring/P5/Certificate/Characters/Twin1/CharCompleteStage3.lean`. Combines the `k ≤ 2`
exhaustiveness certificate `exhaustiveCheck2_le54` (representatives `0…54`) with
the eight `k = 3` chunk certificates (`55…115`) into a single exhaustiveness fact
for every representative `r < 116`, and derives the unconditional q=2
character-count / abelianization-order statements. The `k ≥ 4` classes await the
row-combination (box) certificate.
-/

namespace LeanDring.P5Presentation

namespace Q2

set_option maxRecDepth 100000
-- file-level maxHeartbeats: the kernel `decide`s below exceed the default budget
set_option linter.style.setOption false
set_option maxHeartbeats 4000000

/-- **Exhaustiveness for the `k ≤ 2` classes** (representatives `0…54`): a single
kernel `decide` over the `≤ 25²` candidate exponent vectors of each (q=2 data). -/
theorem exhaustiveCheck2_le54 : (List.range 55).all exhaustiveCheck2 = true := by decide

/-- **Exhaustiveness for every representative `r < 116`** (the `k ≤ 3` classes),
assembled from the `k ≤ 2` certificate and the eight `k = 3` chunk certificates. -/
theorem exhaustiveCheck2_le115 : ∀ r : ℕ, r < 116 → exhaustiveCheck2 r = true := by
  intro r hr
  by_cases h55 : r < 55
  · exact (List.all_eq_true.mp exhaustiveCheck2_le54) r (List.mem_range.mpr h55)
  by_cases h63 : r < 63
  · exact (List.all_eq_true.mp exhaustiveCheck2_r55_62) r
      (List.mem_range'_1.mpr ⟨by omega, by omega⟩)
  by_cases h71 : r < 71
  · exact (List.all_eq_true.mp exhaustiveCheck2_r63_70) r
      (List.mem_range'_1.mpr ⟨by omega, by omega⟩)
  by_cases h79 : r < 79
  · exact (List.all_eq_true.mp exhaustiveCheck2_r71_78) r
      (List.mem_range'_1.mpr ⟨by omega, by omega⟩)
  by_cases h87 : r < 87
  · exact (List.all_eq_true.mp exhaustiveCheck2_r79_86) r
      (List.mem_range'_1.mpr ⟨by omega, by omega⟩)
  by_cases h95 : r < 95
  · exact (List.all_eq_true.mp exhaustiveCheck2_r87_94) r
      (List.mem_range'_1.mpr ⟨by omega, by omega⟩)
  by_cases h103 : r < 103
  · exact (List.all_eq_true.mp exhaustiveCheck2_r95_102) r
      (List.mem_range'_1.mpr ⟨by omega, by omega⟩)
  by_cases h111 : r < 111
  · exact (List.all_eq_true.mp exhaustiveCheck2_r103_110) r
      (List.mem_range'_1.mpr ⟨by omega, by omega⟩)
  · exact (List.all_eq_true.mp exhaustiveCheck2_r111_115) r
      (List.mem_range'_1.mpr ⟨by omega, by omega⟩)

/-- **Completeness for every `k ≤ 3` representative** (`r < 116`), q=2. -/
theorem charsAtComplete2_le115 (r : Fin 148) (hr : r.val < 116) : CharsAtComplete r :=
  charsAtComplete_of_check2 r (exhaustiveCheck2_le115 r.val hr)

/-- **Character count, unconditional for the q=2 `k ≤ 3` classes.** -/
theorem charsAt_complete2_le115 (r : Fin 148) (hr : r.val < 116) :
    Nat.card (↥(reps r) →* ℂˣ) = charCounts.getD r.val 0 :=
  charsAt_complete r (charsAtComplete2_le115 r hr)

/-- **Abelianization order, unconditional for the q=2 `k ≤ 3` classes.** -/
theorem card_abelianization_reps2_le115 (r : Fin 148) (hr : r.val < 116) :
    Nat.card (Abelianization ↥(reps r)) = charCounts.getD r.val 0 :=
  card_abelianization_reps r (charsAtComplete2_le115 r hr)

end Q2

end LeanDring.P5Presentation
