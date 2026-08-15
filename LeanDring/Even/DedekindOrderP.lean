/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import Mathlib.GroupTheory.PGroup
import Mathlib.FieldTheory.Finite.Basic

-- Several statements below do not mention the section's `[Fintype _]` /
-- group binders, but their proofs need them for instance synthesis, so the
-- binders cannot be `omit`ted.  The linters' suggested rewrite to `[Finite _]`
-- plus `Fintype.ofFinite` is a genuine refactor, not a cleanup.
set_option linter.unusedSectionVars false

/-!
# In a Dedekind `p`-group, every element of order `p` is central

**EVEN-ORDER LAYER.** No `sorry`, three standard axioms.

A step towards `DedekindOddPGroup` (`LeanDring/Even/DedekindOdd.lean`), and the one
that shows *why* odd `p` behaves differently from `p = 2`.

If every subgroup of `P` is normal then `⟨x⟩ ⊴ P`, so conjugation reads
`y⁻¹xy = x^i`. Iterating it `p^n` times, where `y^(p^n) = 1`, gives
`x = x^(i^(p^n))`; when `|x| = p` this says `i^(p^n) ≡ 1 mod p`. But
Fermat gives `i^(p^n) ≡ i mod p`. Hence `i ≡ 1 mod p` and `x^i = x`: the
element is central.

No `Aut(C_{p^k})` and no structure theory is needed for this case — only
Fermat's little theorem. The argument is uniform in `p`, and it is
already enough to rule out the smallest non-abelian candidates: in the
modular group `M_{p³} = ⟨a,b: a^{p²} = b^p = 1, b⁻¹ab = a^{1+p}⟩` the
element `b` has order `p` and is *not* central, so `M_{p³}` is not
Dedekind — as one checks directly, `⟨b⟩` is not normal there.

## Main result

* `centralizes_of_orderOf_eq_prime` — in a `p`-group with every subgroup
  normal, an element of order `p` commutes with everything.
-/

namespace LeanDring

namespace Even

variable {p : ℕ} [Fact p.Prime] {P : Type*} [Group P] [Finite P]


/-- Conjugation by `y^m` raises the exponent to `i^m`. -/
theorem conj_pow_iterate {x y : P} {i : ℕ} (h : y⁻¹ * x * y = x ^ i) :
    ∀ m : ℕ, (y ^ m)⁻¹ * x * y ^ m = x ^ (i ^ m) := by
  intro m
  induction m with
  | zero => simp
  | succ n ih =>
      have hstep : (y ^ (n + 1))⁻¹ * x * y ^ (n + 1)
          = y⁻¹ * ((y ^ n)⁻¹ * x * y ^ n) * y := by
        rw [pow_succ]
        group
      rw [hstep, ih]
      -- conjugation is a homomorphism, so it acts on the power
      have hconj : y⁻¹ * x ^ (i ^ n) * y = (y⁻¹ * x * y) ^ (i ^ n) := by
        have := conj_pow (i := i ^ n) (a := y⁻¹) (b := x)
        simpa using this.symm
      rw [hconj, h, ← pow_mul, pow_succ, Nat.mul_comm]

/-- Fermat's little theorem, iterated: `i ^ p ^ m ≡ i mod p`. -/
theorem zmod_pow_ppow (i : ℕ) : ∀ m : ℕ, ((i : ZMod p)) ^ p ^ m = (i : ZMod p) := by
  intro m
  induction m with
  | zero => simp
  | succ k ih => rw [pow_succ, pow_mul, ih, ZMod.pow_card]

/-- **Every element of order `p` in a Dedekind `p`-group is central.**

The proof is Fermat's little theorem: conjugation acts on `⟨x⟩ ≅ C_p` by
some exponent `i`, iterating `p^n` times forces `i^(p^n) ≡ 1 mod p`, and
`i^(p^n) ≡ i mod p`. -/
theorem centralizes_of_orderOf_eq_prime (hP : IsPGroup p P)
    (hall : ∀ S : Subgroup P, S.Normal) {x : P} (hx : orderOf x = p)
    (y : P) : y * x = x * y := by
  classical
  -- `⟨x⟩` is normal, so conjugation stays inside it
  haveI : (Subgroup.zpowers x).Normal := hall _
  have hmem : y⁻¹ * x * y ∈ Subgroup.zpowers x := by
    have := (hall (Subgroup.zpowers x)).conj_mem x (Subgroup.mem_zpowers x) y⁻¹
    simpa using this
  have hfin : IsOfFinOrder x := isOfFinOrder_of_finite x
  obtain ⟨i, hi'⟩ := hfin.mem_powers_iff_mem_zpowers.mpr hmem
  have hi : y⁻¹ * x * y = x ^ i := hi'.symm
  -- `y` has `p`-power order, and iterating conjugation that often is trivial
  obtain ⟨n, hn⟩ := hP y
  have hiter := conj_pow_iterate hi (p ^ n)
  rw [hn] at hiter
  simp only [inv_one, one_mul, mul_one] at hiter
  -- so `x ^ (i ^ p ^ n) = x ^ 1`, i.e. `i ^ p ^ n ≡ 1 mod p`
  have hmod : i ^ p ^ n ≡ 1 [MOD p] := by
    have h1 : x ^ (i ^ p ^ n) = x ^ 1 := by rw [pow_one]; exact hiter.symm
    have := pow_eq_pow_iff_modEq.mp h1
    rwa [hx] at this
  -- Fermat, iterated: `i ^ p ^ n ≡ i mod p`
  have hfer : ((i : ZMod p)) ^ p ^ n = (i : ZMod p) := zmod_pow_ppow i n
  -- combine: `i ≡ 1 mod p`
  have hi1 : i ≡ 1 [MOD p] := by
    have h2 : ((i : ZMod p)) ^ p ^ n = ((1 : ℕ) : ZMod p) := by
      rw [← Nat.cast_pow]
      exact (ZMod.natCast_eq_natCast_iff _ _ _).mpr hmod
    rw [hfer] at h2
    exact (ZMod.natCast_eq_natCast_iff _ _ _).mp h2
  -- hence conjugation is trivial
  have hxi : x ^ i = x := by
    have : x ^ i = x ^ 1 := by
      refine pow_eq_pow_iff_modEq.mpr ?_
      rw [hx]; exact hi1
    rwa [pow_one] at this
  have : y⁻¹ * x * y = x := by rw [hi, hxi]
  have h3 := congrArg (fun t => y * t) this
  simpa [mul_assoc] using h3.symm

/-- **The general form**: in a Dedekind `p`-group, conjugation acts on
`⟨x⟩` by an exponent `≡ 1 mod p`, whatever the order of `x`.

The same argument as `centralizes_of_orderOf_eq_prime`, stopped one step
earlier: iterating conjugation forces `i ^ p ^ n ≡ 1 mod orderOf x`,
which reduces mod `p` since `p ∣ orderOf x`, and Fermat then gives
`i ≡ 1 mod p`. Equivalently `[x,y] = x^(i-1) ∈ ⟨x^p⟩`.

When `orderOf x = p` this collapses to centrality, which is the previous
theorem. In general it does not, and bridging that gap — from
"commutators lie in `⟨x^p⟩`" to "commutators are trivial" — is exactly
what still stands between this file and `DedekindOddPGroup`, and the
step where oddness must finally be used. -/
theorem exists_conj_exponent_one_mod_prime (hP : IsPGroup p P)
    (hall : ∀ S : Subgroup P, S.Normal) (x y : P) (hx : x ≠ 1) :
    ∃ i : ℕ, y⁻¹ * x * y = x ^ i ∧ i ≡ 1 [MOD p] := by
  classical
  haveI : (Subgroup.zpowers x).Normal := hall _
  have hmem : y⁻¹ * x * y ∈ Subgroup.zpowers x := by
    have := (hall (Subgroup.zpowers x)).conj_mem x (Subgroup.mem_zpowers x) y⁻¹
    simpa using this
  have hfin : IsOfFinOrder x := isOfFinOrder_of_finite x
  obtain ⟨i, hi'⟩ := hfin.mem_powers_iff_mem_zpowers.mpr hmem
  have hi : y⁻¹ * x * y = x ^ i := hi'.symm
  refine ⟨i, hi, ?_⟩
  obtain ⟨n, hn⟩ := hP y
  have hiter := conj_pow_iterate hi (p ^ n)
  rw [hn] at hiter
  simp only [inv_one, one_mul, mul_one] at hiter
  have hmodx : i ^ p ^ n ≡ 1 [MOD orderOf x] := by
    have h1 : x ^ (i ^ p ^ n) = x ^ 1 := by rw [pow_one]; exact hiter.symm
    exact pow_eq_pow_iff_modEq.mp h1
  have hpx : p ∣ orderOf x := hP.dvd_orderOf hx
  have hmod : i ^ p ^ n ≡ 1 [MOD p] := Nat.ModEq.of_dvd hpx hmodx
  have hfer : ((i : ZMod p)) ^ p ^ n = (i : ZMod p) := zmod_pow_ppow i n
  have h2 : ((i : ZMod p)) ^ p ^ n = ((1 : ℕ) : ZMod p) := by
    rw [← Nat.cast_pow]
    exact (ZMod.natCast_eq_natCast_iff _ _ _).mpr hmod
  rw [hfer] at h2
  exact (ZMod.natCast_eq_natCast_iff _ _ _).mp h2

end Even

end LeanDring

/-! ## Axiom audit -/

#print axioms LeanDring.Even.conj_pow_iterate
#print axioms LeanDring.Even.centralizes_of_orderOf_eq_prime
#print axioms LeanDring.Even.exists_conj_exponent_one_mod_prime
