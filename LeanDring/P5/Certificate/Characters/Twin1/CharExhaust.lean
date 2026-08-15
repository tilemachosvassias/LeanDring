/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.Characters.Twin1.CharExtend

/-!
# Exhaustiveness of the certified character enumeration, as a decidable check

`charsAtComplete_of_exhaustive` reduces the completeness obligation to a purely
combinatorial statement: the certified list `charsAt r` contains *every*
`charOK`-valid exponent vector of the right length. Here that statement is made
kernel-decidable.

The `charOK` checker is bridged (via the certified row equalities `checkRows`) to
the sift-free row checker `charOKrows` on the embedded `repPR`/`repCR` data — pure
`ZMod 25` linear algebra. The solution set is then enumerated by brute force over
`(ZMod 25)^k` (`allVecs k`) and each solution checked to be listed
(`exhaustiveCheck`). For a representative with `k` echelon generators this is a
`25^k`-element `decide`; feasible for the small-`k` classes, chunked by generator
count across `LeanDring.P5.Certificate.Characters.Twin1.CharComplete` and its
`Chunk01`–`Chunk08` submodules. The `k ≥ 4` classes are handled instead by the
row-combination certificate of `…Twin1.CharBox`.
-/

namespace LeanDring.P5Presentation

open Fin.NatCast

set_option maxRecDepth 100000

/-! ## Enumerating all exponent vectors of a given length -/

/-- All of `ZMod 25` (`= Fin 25`), computably. -/
def zmodAll : List (ZMod 25) := List.finRange 25

theorem mem_zmodAll (a : ZMod 25) : a ∈ zmodAll := List.mem_finRange a

/-- Every length-`k` `ZMod 25` vector, as a list. -/
def allVecs : ℕ → List (List (ZMod 25))
  | 0 => [[]]
  | k + 1 => zmodAll.flatMap (fun a => (allVecs k).map (fun v => a :: v))

theorem mem_allVecs : ∀ (k : ℕ) (e : List (ZMod 25)), e.length = k → e ∈ allVecs k := by
  intro k
  induction k with
  | zero =>
      intro e he
      rw [List.eq_nil_of_length_eq_zero he]
      simp [allVecs]
  | succ k ih =>
      intro e he
      match e, he with
      | a :: rest, he =>
          have hr : rest.length = k := by simpa using he
          rw [allVecs, List.mem_flatMap]
          exact ⟨a, mem_zmodAll a, List.mem_map.mpr ⟨rest, ih rest hr, rfl⟩⟩

/-! ## The per-representative exhaustiveness check -/

/-- **Exhaustiveness check** for representative `r`: every length-`k` vector that
passes the sift-free row checker `charOKrows` is listed in `repChars r`. Pure
`ZMod 25` arithmetic, no sift — kernel-decidable over `25^k` vectors. -/
def exhaustiveCheck (r : ℕ) : Bool :=
  (allVecs (repBases.getD r []).length).all (fun e =>
    !(charOKrows (repPR.getD r []) (repCR.getD r []) e) || decide (e ∈ repChars.getD r []))

/-- **From a decided exhaustiveness check to the reduction hypothesis.** If
`exhaustiveCheck r` holds, every `charOK`-valid vector of the right length is in
`charsAt r`. -/
theorem exhaustive_of_check (r : Fin 148) (h : exhaustiveCheck r.val = true) :
    ∀ e : List (ZMod 25), charOK (basisAt r) e = true →
        e.length = (basisAt r).length → e ∈ charsAt r := by
  intro e hOK hlen
  have hrows := checker_at checkRows_all r
  simp only [checkRows, Bool.and_eq_true, decide_eq_true_eq] at hrows
  obtain ⟨hPR, hCR⟩ := hrows
  have hrowsE : charOKrows (repPR.getD r.val []) (repCR.getD r.val []) e = true := by
    rw [hPR, hCR]
    exact (charOKrows_iff (basisAt r) e).mpr hOK
  have hmem : e ∈ allVecs (repBases.getD r.val []).length := mem_allVecs _ e hlen
  rw [exhaustiveCheck, List.all_eq_true] at h
  have hcell := h e hmem
  rw [hrowsE] at hcell
  simp only [Bool.not_true, Bool.false_or, decide_eq_true_eq] at hcell
  exact hcell

/-- **Completeness from a decided exhaustiveness check.** -/
theorem charsAtComplete_of_check (r : Fin 148) (h : exhaustiveCheck r.val = true) :
    CharsAtComplete r :=
  charsAtComplete_of_exhaustive r (exhaustive_of_check r h)

end LeanDring.P5Presentation
