/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.Characters.Twin2.CharExtend
import LeanDring.P5.Certificate.Characters.Twin1.CharExhaust

/-!
# Exhaustiveness of the certified q=2 character enumeration (Step 3, twin q=2)

The q=2 twin of `LeanDring/P5/Certificate/Characters/Twin1/CharExhaust.lean`.
`charsAtComplete_of_exhaustive` (from
`LeanDring/P5/Certificate/Characters/Twin2/CharExtend.lean`) reduces the completeness obligation to
a purely combinatorial
statement: the certified list `charsAt2 r` contains *every* `charOK2`-valid
exponent vector of the right length. Here that statement is made kernel-decidable.

The group-independent enumeration machinery (`allVecs`, `mem_allVecs`) is reused
verbatim from `LeanDring/P5/Certificate/Characters/Twin1/CharExhaust.lean`; only the checker
`charOKrows` is fed the q=2 row
data `repPR2`/`repCR2`, bridged to `charOK2` by `charOKrows_iff2`.
-/

namespace LeanDring.P5Presentation

namespace Q2

open Fin.NatCast

set_option maxRecDepth 100000

/-- **Exhaustiveness check (q=2)** for representative `r`: every length-`k` vector
that passes the sift-free row checker `charOKrows` on the q=2 rows is listed in
`repChars2 r`. Pure `ZMod 25` arithmetic — kernel-decidable over `25^k` vectors. -/
def exhaustiveCheck2 (r : ℕ) : Bool :=
  (allVecs (repBases2.getD r []).length).all (fun e =>
    !(charOKrows (repPR2.getD r []) (repCR2.getD r []) e) || decide (e ∈ repChars2.getD r []))

/-- **From a decided exhaustiveness check to the reduction hypothesis (q=2).** -/
theorem exhaustive_of_check2 (r : Fin 148) (h : exhaustiveCheck2 r.val = true) :
    ∀ e : List (ZMod 25), charOK2 (basisAt2 r) e = true →
        e.length = (basisAt2 r).length → e ∈ charsAt2 r := by
  intro e hOK hlen
  have hrows := checker_at checkRows2_all r
  simp only [checkRows2, Bool.and_eq_true, decide_eq_true_eq] at hrows
  obtain ⟨hPR, hCR⟩ := hrows
  have hrowsE : charOKrows (repPR2.getD r.val []) (repCR2.getD r.val []) e = true := by
    rw [hPR, hCR]
    exact (charOKrows_iff2 (basisAt2 r) e).mpr hOK
  have hmem : e ∈ allVecs (repBases2.getD r.val []).length := mem_allVecs _ e hlen
  rw [exhaustiveCheck2, List.all_eq_true] at h
  have hcell := h e hmem
  rw [hrowsE] at hcell
  simp only [Bool.not_true, Bool.false_or, decide_eq_true_eq] at hcell
  exact hcell

/-- **Completeness from a decided exhaustiveness check (q=2).** -/
theorem charsAtComplete_of_check2 (r : Fin 148) (h : exhaustiveCheck2 r.val = true) :
    CharsAtComplete r :=
  charsAtComplete_of_exhaustive r (exhaustive_of_check2 r h)

end Q2

end LeanDring.P5Presentation
