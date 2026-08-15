/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P4.Hentry

/-!
# The exponent of the maximal abelian subgroup `A`

`subA_pow_psq`: every element of `A = subA p d` has order dividing `p²`, so every
character value `χ(x)` is a `p²`-th root of unity — the input to the `p²`-root
membership dichotomy for a *general* A-block element in the twin-separation
reduction `hentry`.
-/

namespace LeanDring.P4
open DRing Model

variable {p : ℕ} [Fact p.Prime] [Fact (Odd p)]

open scoped Classical in
theorem subA_pow_psq {d : ZMod p} (hp5 : 5 ≤ p) (x : subA p d) :
    x ^ (p ^ 2) = 1 := by
  have h_pow_p : x ^ p = zElt p d (d * (x : Model p d).u) := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, pow_p hp5 (x : Model p d)]
    have h_redp : redp p (x : Model p d).α = 0 := mem_subA_iff.mp x.2
    change (⟨liftp p (redp p (x:Model p d).α + d * (x:Model p d).u), 0, 0⟩ : Model p d) = _
    rw [h_redp, zero_add]
    rfl
  rw [pow_two, pow_mul, h_pow_p, zElt_pow_p hp5]

open scoped Classical in
/-- **The A-block order-`p²` classification at a general column `h ∈ A`.**  A
nonzero A-block entry at any `h ∈ A` lies in `ℤ[ζ_p]` **iff** `χ(h)^p = 1` — the
`ℤ[ζ_p]`-escape (the `z ∉ ℤ[ζ_p]` phenomenon) happens exactly for order-`p²`
character values, at **every** A-block column.  Uses `subA_pow_psq` (so `χ(h)`
is a `p²`-th root), `entry_factor_gen`/`disp_pow_p_gen` (the `χ(h)·bracket`
split with `bracket ∈ ℤ[ζ_p]`), and the `p²`-root membership dichotomy. -/
theorem A_block_mem_adjoin_iff_gen {d : ZMod p} (hp5 : 5 ≤ p) (χ : subA p d →* ℂˣ)
    (h : subA p d) (hne : species (subA p d) h (DRing.basisElt (subA p d) χ) ≠ 0) :
    species (subA p d) h (DRing.basisElt (subA p d) χ)
        ∈ (Algebra.adjoin ℤ {(zetaP2 p) ^ p} : Subalgebra ℤ ℂ)
      ↔ ((χ h : ℂˣ) : ℂ) ^ p = 1 := by
  have hp : p.Prime := Fact.out
  have hodd : Odd p := Fact.out
  haveI : Fact p.Prime := ⟨hp⟩
  have hζp2 : IsPrimitiveRoot (zetaP2 p) (p ^ 2) := by
    rw [zetaP2]; exact Complex.isPrimitiveRoot_exp (p ^ 2) (pow_ne_zero 2 hp.ne_zero)
  have hζp : IsPrimitiveRoot ((zetaP2 p) ^ p) p := hζp2.pow (pow_pos hp.pos 2) (by ring)
  have hχpsq : ((χ h : ℂˣ) : ℂ) ^ (p ^ 2) = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← map_pow, subA_pow_psq hp5, map_one, Units.val_one]
  have hroot : ∀ t : ZMod p,
      ((χ (h⁻¹ * conjA p d (aGen p d ^ t.val) h) : ℂˣ) : ℂ) ^ p = 1 := by
    intro t
    rw [← Units.val_pow_eq_pow_val, ← map_pow, disp_pow_p_gen hp5 h, map_one, Units.val_one]
  have hbracket : (∑ t : ZMod p,
      ((χ (h⁻¹ * conjA p d (aGen p d ^ t.val) h) : ℂˣ) : ℂ))
      ∈ (Algebra.adjoin ℤ {(zetaP2 p) ^ p} : Subalgebra ℤ ℂ) :=
    Subalgebra.sum_mem _ (fun t _ => mem_adjoin_of_pow_eq_one hp hζp (hroot t))
  constructor
  · intro hmem
    by_contra hp1
    have hprim : IsPrimitiveRoot ((χ h : ℂˣ) : ℂ) (p ^ 2) := by
      rw [IsPrimitiveRoot.iff_orderOf]
      exact orderOf_eq_prime_pow (by rw [pow_one]; exact hp1) hχpsq
    rw [entry_factor_gen] at hmem
    have hbz : (∑ t : ZMod p,
        ((χ (h⁻¹ * conjA p d (aGen p d ^ t.val) h) : ℂˣ) : ℂ)) * ((χ h : ℂˣ) : ℂ)
        ∈ (Algebra.adjoin ℤ {(zetaP2 p) ^ p} : Subalgebra ℤ ℂ) := by
      rw [mul_comm]; exact hmem
    have hb0 := eq_zero_of_mul_zetaP2_mem hp hodd hprim hζp hbracket hbz
    exact hne (by rw [entry_factor_gen, hb0, mul_zero])
  · intro hp1
    rw [entry_factor_gen]
    exact Subalgebra.mul_mem _ (mem_adjoin_of_pow_eq_one hp hζp hp1) hbracket

end LeanDring.P4
