/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.Characters.Twin1.CharExhaust

/-!
# Discharging `CharsAtComplete` by decided exhaustiveness (the `k ≤ 2` classes)

`charsAtComplete_of_check` reduces the completeness obligation of a representative
to the Boolean `exhaustiveCheck r` — a kernel `decide` over `25^k` exponent
vectors (`k` = number of echelon generators). Here those decides are run, chunked
by generator count, and turned into unconditional character-count statements.

Coverage this file establishes unconditionally: the `k ≤ 2` classes
(representatives `0…54`), by a single `25²`-bounded `decide`. For these
representatives the certified list `charsAt r` provably enumerates *every* linear
character, so `|Hom(reps r, ℂˣ)| = |(reps r)ᵃᵇ| = charCounts r` holds with no
hypothesis. The `k = 3` classes (`55…115`) are decidable by the same enumeration
(a `25³` `decide` per representative), carried out in the `Chunk01`–`Chunk08`
submodules and assembled in
`LeanDring.P5.Certificate.Characters.Twin1.CharCompleteStage3`. The `k ≥ 4`
classes (`116…147`) exceed the brute-enumeration budget and are discharged by
the row-combination certificate of `…Twin1.CharBox` / `…Twin1.CharBoxReps`.
-/

namespace LeanDring.P5Presentation

set_option maxRecDepth 100000
-- file-level maxHeartbeats: the kernel `decide`s below exceed the default budget
set_option linter.style.setOption false
set_option maxHeartbeats 4000000

/-- **Exhaustiveness for the `k ≤ 2` classes** (representatives `0…54`): a single
kernel `decide` over the `≤ 25²` candidate exponent vectors of each. -/
theorem exhaustiveCheck_le54 : (List.range 55).all exhaustiveCheck = true := by decide

/-- **Completeness for every `k ≤ 2` representative.** -/
theorem charsAtComplete_le54 (r : Fin 148) (hr : r.val < 55) : CharsAtComplete r :=
  charsAtComplete_of_check r
    ((List.all_eq_true.mp exhaustiveCheck_le54) r.val (List.mem_range.mpr hr))

/-- **Character count, unconditional for the `k ≤ 2` classes.** The number of
linear characters of `reps r` equals its certified count `charCounts r`. -/
theorem charsAt_complete_le54 (r : Fin 148) (hr : r.val < 55) :
    Nat.card (↥(reps r) →* ℂˣ) = charCounts.getD r.val 0 :=
  charsAt_complete r (charsAtComplete_le54 r hr)

/-- **Abelianization order, unconditional for the `k ≤ 2` classes.** -/
theorem card_abelianization_reps_le54 (r : Fin 148) (hr : r.val < 55) :
    Nat.card (Abelianization ↥(reps r)) = charCounts.getD r.val 0 :=
  card_abelianization_reps r (charsAtComplete_le54 r hr)

end LeanDring.P5Presentation
