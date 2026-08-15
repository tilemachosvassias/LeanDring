/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import Mathlib.Data.ZMod.Units
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.GroupTheory.OrderOfElement

/-!
# Units of `ZMod (p^k)` of `p`-power order are `≡ 1 mod p`

**EVEN-ORDER LAYER.** No `sorry`, three standard axioms.

The `Aut(C_{p^k})` input of `DedekindOddPGroup`
(`LeanDring/Even/DedekindOdd.lean`), isolated and proved.

In a `p`-group `P` with every subgroup normal, `⟨a⟩` is normal, so
conjugation by `b` sends `a ↦ a^r`; the automorphism it induces on
`⟨a⟩ ≅ C_{p^k}` has `p`-power order, because it is the image of `b` in a
quotient of `P`. The classical step is then that such an `r` satisfies
`r ≡ 1 mod p`, so that `[a,b] = a^{r-1} ∈ ⟨a^p⟩`. That step is this file.

The proof needs no case analysis and no structure theorem for
`(ZMod (p^k))ˣ` — only that reduction `mod p` is a homomorphism and that
`|(ZMod p)ˣ| = p - 1` is coprime to `p`. An element of `p`-power order
therefore has image of order dividing both `p^n` and `p-1`, hence trivial.

(Stated for every prime `p`. For `p = 2` it is vacuously true — every
unit is odd — and the oddness hypothesis of Dedekind's theorem is needed
elsewhere, not here.)
-/

namespace LeanDring

namespace Even

open ZMod

/-- Reduction `(ZMod (p^k))ˣ → (ZMod p)ˣ`. -/
noncomputable def unitsReduce (p k : ℕ) (hk : k ≠ 0) :
    (ZMod (p ^ k))ˣ →* (ZMod p)ˣ :=
  Units.map (ZMod.castHom (dvd_pow_self p hk) (ZMod p)).toMonoidHom

/-- **The `Aut(C_{p^k})` fact.** A unit of `ZMod (p^k)` whose order is a
power of `p` reduces to `1` mod `p`.

This is what forces `b⁻¹ab = a^r` with `p ∣ r - 1` in a Dedekind
`p`-group. -/
theorem unitsReduce_eq_one_of_orderOf_eq_pow
    {p k n : ℕ} [Fact p.Prime] (hk : k ≠ 0)
    (u : (ZMod (p ^ k))ˣ) (hu : orderOf u = p ^ n) :
    unitsReduce p k hk u = 1 := by
  classical
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  set v := unitsReduce p k hk u with hv
  -- the order of `v` divides `p ^ n` …
  have h1 : orderOf v ∣ p ^ n := by
    rw [← hu, hv]
    exact orderOf_map_dvd _ u
  -- … and divides `|(ZMod p)ˣ| = p - 1`
  have hcard : Fintype.card (ZMod p)ˣ = p - 1 := ZMod.card_units p
  have h2 : orderOf v ∣ p - 1 := by
    rw [← hcard]
    exact orderOf_dvd_card
  -- `p ^ n` and `p - 1` are coprime, so the order is `1`
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  have hcop : Nat.Coprime (p ^ n) (p - 1) := by
    refine Nat.Coprime.pow_left _ ?_
    -- `gcd p (p-1) = 1`: any common divisor divides their difference `1`
    have hsub : p - (p - 1) = 1 := by omega
    have hd : Nat.gcd p (p - 1) ∣ 1 := by
      have h1 : Nat.gcd p (p - 1) ∣ p := Nat.gcd_dvd_left _ _
      have h2 : Nat.gcd p (p - 1) ∣ (p - 1) := Nat.gcd_dvd_right _ _
      simpa [hsub] using Nat.dvd_sub h1 h2
    exact Nat.eq_one_of_dvd_one hd
  have h3 : orderOf v = 1 := Nat.eq_one_of_dvd_coprimes hcop h1 h2
  exact orderOf_eq_one_iff.mp h3

end Even

end LeanDring

/-! ## Axiom audit -/

#print axioms LeanDring.Even.unitsReduce_eq_one_of_orderOf_eq_pow
