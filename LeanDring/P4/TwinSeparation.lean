/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P4.Specializations
import LeanDring.P4.Endgame
import LeanDring.Theory.Gauss.GaussSignTheorem
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity

/-!
# Separating the last order-`p⁴` twin `(xii)/(xiii)`: number-theory bridge

The A-block species entries of the two model groups are, by
`P4.Model.g1_entry_gauss_form` / `g2_entry_gauss_form`,
`χ(s)·ψ(phase)·χ₂(2⁻¹)·g` where `g` is the quadratic Gauss sum. Using the
Gauss **sign** theorem (`GaussSign.gauss_eq`) and Mathlib's `(2/p)` supplement,
every factor becomes an explicit power of `ζ = exp(2πi/8p)` times `√p`. This
file is that number-theory bridge — the step that turns the raw Gauss-sum
entries into the `ζ`-power form of the value equation, which
`P4.value_equation_impossible` then refutes.

This file supplies:
* `zeta8` and its structural powers (`ζ^{8p}=1`, `ζ^{4p}=-1`, `ζ^{2p}=i`);
* `stdAddChar_eq_zeta_pow` — `ψ(x) = ζ^{8·x.val}` (the phase is a `ζ`-power);
* `gauss_eq_sqrt_mul` — `g = √p · c(p)`, `c(p) = 1` or `i` (the sign, folded
  the way `value_equation_impossible` consumes it).
-/

namespace LeanDring.P4

open Complex

/-- `ζ = exp(2πi / 8p)`, the primitive `8p`-th root of unity in which the
value equation is written. -/
noncomputable def zeta8 (p : ℕ) : ℂ :=
  Complex.exp (2 * Real.pi * I / ((8 * p : ℕ) : ℂ))

variable {p : ℕ} [Fact p.Prime] [Fact (Odd p)]

omit [Fact (Odd p)] in
theorem zeta8_pow_eight : (zeta8 p) ^ 8 = Complex.exp (2 * Real.pi * I / (p : ℂ)) := by
  have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  rw [zeta8, ← Complex.exp_nat_mul,
    show ((8 : ℕ) : ℂ) * (2 * Real.pi * I / ((8 * p : ℕ) : ℂ)) =
      2 * Real.pi * I / (p : ℂ) by push_cast; field_simp]

omit [Fact (Odd p)] in
theorem zeta8_pow_four_p : (zeta8 p) ^ (4 * p) = -1 := by
  have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  rw [zeta8, ← Complex.exp_nat_mul,
    show ((4 * p : ℕ) : ℂ) * (2 * Real.pi * I / ((8 * p : ℕ) : ℂ)) =
      (Real.pi : ℂ) * I by push_cast; field_simp; ring]
  exact Complex.exp_pi_mul_I

omit [Fact (Odd p)] in
theorem zeta8_pow_two_p : (zeta8 p) ^ (2 * p) = I := by
  have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  rw [zeta8, ← Complex.exp_nat_mul,
    show ((2 * p : ℕ) : ℂ) * (2 * Real.pi * I / ((8 * p : ℕ) : ℂ)) =
      (Real.pi : ℂ) / 2 * I by push_cast; field_simp; ring]
  exact Complex.exp_pi_div_two_mul_I

omit [Fact (Odd p)] in
theorem zeta8_pow_six_p : (zeta8 p) ^ (6 * p) = -I := by
  rw [show 6 * p = 4 * p + 2 * p by ring, pow_add, zeta8_pow_four_p, zeta8_pow_two_p]
  ring

omit [Fact (Odd p)] in
/-- The standard additive character is a power of `ζ`:
`ψ(x) = ζ^{8·x.val}` (since `ψ(1) = exp(2πi/p) = ζ^8`). -/
theorem stdAddChar_eq_zeta_pow (x : ZMod p) :
    (ZMod.stdAddChar : AddChar (ZMod p) ℂ) x = (zeta8 p) ^ (8 * x.val) := by
  have h1 : (ZMod.stdAddChar : AddChar (ZMod p) ℂ) 1 = (zeta8 p) ^ 8 := by
    rw [show (1 : ZMod p) = ((1 : ℤ) : ZMod p) by norm_cast, ZMod.stdAddChar_coe,
      zeta8_pow_eight]
    congr 1
    push_cast
    ring
  rw [addChar_apply_val _ x, h1, ← pow_mul]

omit [Fact (Odd p)] in
/-- The quadratic Gauss sum factored as `√p · c(p)` with `c(p) = 1` if
`p ≡ 1 (4)`, `i` if `p ≡ 3 (4)` — exactly the `c(p)` of
`value_equation_impossible`. -/
theorem gauss_eq_sqrt_mul (hp2 : p ≠ 2) :
    LeanDring.GaussSign.gauss p =
      (Real.sqrt p : ℂ) * (if p % 4 = 1 then (1 : ℂ) else I) := by
  rw [LeanDring.GaussSign.gauss_eq hp2]
  by_cases h : p % 4 = 1
  · rw [if_pos h, if_pos h, mul_one]
  · rw [if_neg h, if_neg h, mul_comm]

namespace Model

open DRing AddChar ZMod

variable {d : ZMod p}

/-- `8 ≠ 0` in the odd-prime field `ZMod p`, for the phase denominator. -/
private theorem eight_ne_zero' : (8 : ZMod p) ≠ 0 := by
  rw [show (8 : ZMod p) = 2 * 2 * 2 by ring]
  exact mul_ne_zero (mul_ne_zero two_ne_zero' two_ne_zero') two_ne_zero'

/-- `4·2⁻¹ = 2` in `ZMod p`, used to de-nest `(4·2⁻¹)⁻¹ = 2⁻¹`. -/
private theorem four_mul_two_inv : (4 : ZMod p) * (2 : ZMod p)⁻¹ = 2 := by
  rw [show (4 : ZMod p) = 2 * 2 by ring, mul_assoc,
    mul_inv_cancel₀ (two_ne_zero' (p := p)), mul_one]

/-- **The `G₁` phase collapses to `-(1+2β)²·8⁻¹`.**  In `ZMod p` (`p` odd),
`1 - 2⁻¹ = 2⁻¹` and `(4·2⁻¹)⁻¹ = 2⁻¹`, so the `G₁` quadratic phase argument
`-(1-2⁻¹+β)²·(4·2⁻¹)⁻¹` equals `-(1+2β)²·8⁻¹` — pulling out the odd square
`(1+2β)²` of the value equation. -/
theorem g1_phase_simp (β : ZMod p) :
    (- ((1 : ZMod p) - (2 : ZMod p)⁻¹ + β) ^ 2 * (4 * (2 : ZMod p)⁻¹)⁻¹)
      = - (1 + 2 * β) ^ 2 * (8 : ZMod p)⁻¹ := by
  have h2 := two_ne_zero' (p := p)
  have h8 := eight_ne_zero' (p := p)
  rw [four_mul_two_inv]
  field_simp
  ring

/-- **The `G₂` inner phase collapses to `-8⁻¹`, so the shifted phase is
`-d⁻¹·8⁻¹`.**  Since `d - 2⁻¹ - d = -2⁻¹`, the `G₂` argument
`-(d-2⁻¹-d)²·(4·2⁻¹)⁻¹ = -8⁻¹`; multiplying by the shift `d⁻¹` gives
`-d⁻¹·8⁻¹` — pulling out the `d⁻¹` of the value equation. -/
theorem g2_phase_simp (d : ZMod p) :
    (d⁻¹ : ZMod p) * (- (d - (2 : ZMod p)⁻¹ - d) ^ 2 * (4 * (2 : ZMod p)⁻¹)⁻¹)
      = - (d⁻¹ * (8 : ZMod p)⁻¹) := by
  have h2 := two_ne_zero' (p := p)
  have h8 := eight_ne_zero' (p := p)
  have hinner : (- (-(2 : ZMod p)⁻¹) ^ 2 * (2 : ZMod p)⁻¹) = -(8 : ZMod p)⁻¹ := by
    field_simp; ring
  rw [show d - (2 : ZMod p)⁻¹ - d = - (2 : ZMod p)⁻¹ by ring, four_mul_two_inv, hinner]
  ring

/-- **The `G₁` entry in `ζ`-power form.**  Substituting `stdAddChar(phase) = ζ^{8·…}`
(`stdAddChar_eq_zeta_pow`) and `g = √p·c(p)` (`gauss_eq_sqrt_mul`) into
`g1_entry_gauss_form`, the `G₁` (`d = 1`) A-block entry at `s = ca` becomes
`χ(s) · ζ₈ₚ^{8·phase.val} · (2⁻¹∣p) · √p · c(p)`.  Every transcendental factor
is now an explicit power of `ζ = exp(2πi/8p)` times `√p`; this is the left-hand
side of the value equation, up to the `ζ_{p²}` conductor cancellation. -/
theorem g1_entry_zeta_form (χ : subA p (1 : ZMod p) →* ℂˣ) (β : ZMod p)
    (hz : zChar χ = (stdAddChar : AddChar (ZMod p) ℂ))
    (hb : bChar χ = (stdAddChar : AddChar (ZMod p) ℂ).mulShift β) :
    species (subA p (1 : ZMod p)) (sElt p 1)
        (DRing.basisElt (subA p (1 : ZMod p)) χ) =
      ((χ (sElt p 1) : ℂˣ) : ℂ) *
        ((zeta8 p) ^ (8 * (- ((1 : ZMod p) - (2 : ZMod p)⁻¹ + β) ^ 2 *
            (4 * (2 : ZMod p)⁻¹)⁻¹).val) *
          (χq p ((2 : ZMod p)⁻¹) *
            ((Real.sqrt p : ℂ) * (if p % 4 = 1 then (1 : ℂ) else I)))) := by
  have hp2 : p ≠ 2 := by rintro rfl; exact (by decide : ¬ Odd 2) Fact.out
  rw [g1_entry_gauss_form χ β hz hb, stdAddChar_eq_zeta_pow, gauss_eq_sqrt_mul hp2]

/-- **General-`h` A-block entry in `ζ`-power form** (the value-step generalization
of `g1_entry_zeta_form` from `s = ca` to an arbitrary order-`p²` column element
`h ∈ A`, `d = 1`).  Applying the two bridge lemmas to `species_A_block_gauss`,
`φ_{A,h}[A,χ] = χ(h) · ζ₈ₚ^{8·phase.val} · (u/2 ∣ p) · √p · c(p)`, where
`u = h.u`, `v = h.v`, and the quadratic phase is
`-(u + v - u/2 + κu)²·(4·(u/2))⁻¹`.  For `h = ca` (`u=1, v=0`) this is
`g1_entry_zeta_form`. -/
theorem A_block_gauss_zeta (χ : subA p (1 : ZMod p) →* ℂˣ) (h : subA p (1 : ZMod p))
    (hu : (h : Model p 1).u ≠ 0) (κ : ZMod p)
    (hz : zChar χ = (stdAddChar : AddChar (ZMod p) ℂ))
    (hb : bChar χ = (stdAddChar : AddChar (ZMod p) ℂ).mulShift κ) :
    species (subA p (1 : ZMod p)) h (DRing.basisElt (subA p (1 : ZMod p)) χ) =
      ((χ h : ℂˣ) : ℂ) *
        ((zeta8 p) ^ (8 * (- ((1 : ZMod p) * (h : Model p 1).u + (h : Model p 1).v -
            (h : Model p 1).u * (2 : ZMod p)⁻¹ + κ * (h : Model p 1).u) ^ 2 *
            (4 * ((h : Model p 1).u * (2 : ZMod p)⁻¹))⁻¹).val) *
          (χq p ((h : Model p 1).u * (2 : ZMod p)⁻¹) *
            ((Real.sqrt p : ℂ) * (if p % 4 = 1 then (1 : ℂ) else I)))) := by
  have hp2 : p ≠ 2 := by rintro rfl; exact (by decide : ¬ Odd 2) Fact.out
  have hψ : zChar χ ≠ 1 := by
    rw [hz]; simpa using (isPrimitive_stdAddChar p) (one_ne_zero : (1 : ZMod p) ≠ 0)
  have hκ : bChar χ = (zChar χ).mulShift κ := by rw [hz]; exact hb
  rw [species_A_block_gauss χ h hψ hu κ hκ, hz, stdAddChar_eq_zeta_pow,
    show gaussSum (χq p) (stdAddChar : AddChar (ZMod p) ℂ) = LeanDring.GaussSign.gauss p from rfl,
    gauss_eq_sqrt_mul hp2]

/-- **The general A-block phase collapses to `-(u(2⁻¹+κ)+v)²·(2u)⁻¹`.**  In
`ZMod p`, `1 - 2⁻¹ = 2⁻¹` and `4·(u·2⁻¹) = 2u`, so the `species_A_block_gauss`
phase argument (for `d = 1`) simplifies; this exposes the quadratic
`(u(2⁻¹+κ)+v)²` whose square-completion drives the general Gauss reciprocity. -/
theorem phase_gen_simp (u v κ : ZMod p) (hu : u ≠ 0) :
    (- ((1 : ZMod p) * u + v - u * (2 : ZMod p)⁻¹ + κ * u) ^ 2 *
        (4 * (u * (2 : ZMod p)⁻¹))⁻¹)
      = - (u * ((2 : ZMod p)⁻¹ + κ) + v) ^ 2 * (2 * u)⁻¹ := by
  have h2 := two_ne_zero' (p := p)
  have h2u : (2 : ZMod p) * u ≠ 0 := mul_ne_zero h2 hu
  have h42u : (4 : ZMod p) * (u * (2 : ZMod p)⁻¹) = 2 * u := by
    calc (4 : ZMod p) * (u * (2 : ZMod p)⁻¹) = 2 * (2 * (2 : ZMod p)⁻¹) * u := by ring
      _ = 2 * 1 * u := by rw [mul_inv_cancel₀ h2]
      _ = 2 * u := by ring
  rw [h42u]
  field_simp
  ring

/-- **The `G₂` entry in `ζ`-power form.**  The `G₂` (`d ≠ 0`) distinguished A-block
entry.  Beyond the two bridge substitutions of `g1_entry_zeta_form`, the central
character here is the *shifted* `stdAddChar.mulShift d⁻¹`, so the Gauss sum is
`gaussSum χq (stdAddChar.mulShift d⁻¹) = χq(d⁻¹)·g` (Mathlib's
`gaussSum_mulShift_eq`, with `χq⁻¹ = χq` since `χq` is quadratic).  The entry
becomes `χ(s) · ζ₈ₚ^{8·(d⁻¹·phase).val} · (2⁻¹∣p) · (d⁻¹∣p) · √p · c(p)` — the
right-hand side of the value equation, up to the `ζ_{p²}` conductor cancellation. -/
theorem g2_entry_zeta_form (χ : subA p d →* ℂˣ) (hd : d ≠ 0)
    (hz : zChar χ = (stdAddChar : AddChar (ZMod p) ℂ).mulShift d⁻¹)
    (hb : bChar χ = (stdAddChar : AddChar (ZMod p) ℂ).mulShift (-1)) :
    species (subA p d) (sElt p d) (DRing.basisElt (subA p d) χ) =
      ((χ (sElt p d) : ℂˣ) : ℂ) *
        ((zeta8 p) ^ (8 * ((d⁻¹ : ZMod p) *
            (- (d - (2 : ZMod p)⁻¹ - d) ^ 2 * (4 * (2 : ZMod p)⁻¹)⁻¹)).val) *
          (χq p ((2 : ZMod p)⁻¹) *
            (χq p (d⁻¹ : ZMod p) *
              ((Real.sqrt p : ℂ) * (if p % 4 = 1 then (1 : ℂ) else I))))) := by
  have hp2 : p ≠ 2 := by rintro rfl; exact (by decide : ¬ Odd 2) Fact.out
  have hunit : IsUnit (d⁻¹ : ZMod p) := isUnit_iff_ne_zero.mpr (inv_ne_zero hd)
  have hgs : gaussSum (χq p) ((stdAddChar : AddChar (ZMod p) ℂ).mulShift d⁻¹)
      = χq p (d⁻¹ : ZMod p) * LeanDring.GaussSign.gauss p := by
    have h := gaussSum_mulShift_eq (χq p) (stdAddChar : AddChar (ZMod p) ℂ) hunit.unit
    rw [hunit.unit_spec, χq_isQuadratic.inv] at h
    exact h
  rw [g2_entry_gauss_form χ hd hz hb, AddChar.mulShift_apply, stdAddChar_eq_zeta_pow,
    hgs, gauss_eq_sqrt_mul hp2]

/-- **The `G₁` root-of-unity identity.**  The specific
instance of the theta/Landsberg–Schaar transformation the `G₁` entry needs:
the Gauss-sum entry `ζ₈ₚ^{8·phase.val}·(2⁻¹∣p)·c(p)` equals
`ζ₈ₚ^{p-(1+2β)²}`.  Proved by folding the sign `(2⁻¹∣p)·c(p)` into a `ζ₈ₚ`
power (case split on `p mod 8`, `(2∣p) = χ₈ p`) and a mod-`8p` CRT congruence
(mod `p` via `8·8⁻¹=1`, mod `8` via `(1+2β)²≡1`), exactly as in
`value_equation_impossible`. -/
theorem g1_exponent_identity (β : ZMod p) :
    (zeta8 p) ^ (8 * (- (1 + 2 * β) ^ 2 * (8 : ZMod p)⁻¹).val)
        * (χq p ((2 : ZMod p)⁻¹) : ℂ) * (if p % 4 = 1 then (1 : ℂ) else I)
      = (zeta8 p) ^ ((p : ℤ) - (1 + 2 * (β.val : ℤ)) ^ 2) := by
  have hp : p.Prime := Fact.out
  have hodd : Odd p := Fact.out
  have hp2 : p ≠ 2 := by rintro rfl; exact (by decide : ¬ Odd 2) hodd
  have h2ne : (2 : ZMod p) ≠ 0 := two_ne_zero'
  have h8ne : (8 : ZMod p) ≠ 0 := eight_ne_zero'
  have hinvne : (2 : ZMod p)⁻¹ ≠ 0 := inv_ne_zero h2ne
  have hne : zeta8 p ≠ 0 := by rw [zeta8]; exact Complex.exp_ne_zero _
  have hζ : IsPrimitiveRoot (zeta8 p) (8 * p) :=
    Complex.isPrimitiveRoot_exp (8 * p) (Nat.mul_ne_zero (by norm_num) hp.ne_zero)
  -- the sign value `χq(2⁻¹) = χ₈ p`
  have hls : quadraticChar (ZMod p) (2 : ZMod p) = χ₈ (p : ℕ) := by
    have h := legendreSym.at_two (p := p) hp2
    rwa [legendreSym, show (((2 : ℤ)) : ZMod p) = (2 : ZMod p) by norm_cast] at h
  have hqc : quadraticChar (ZMod p) ((2 : ZMod p)⁻¹) = χ₈ (p : ℕ) := by
    rw [show (2 : ZMod p)⁻¹ = 2 * ((2 : ZMod p)⁻¹) ^ 2 by field_simp,
      map_mul, quadraticChar_sq_one' hinvne, mul_one, hls]
  have hsign : (χq p ((2 : ZMod p)⁻¹) : ℂ) = ((χ₈ (p : ℕ) : ℤ) : ℂ) := by
    simp only [χq, MulChar.ringHomComp_apply, hqc, eq_intCast]
  rw [hsign, mul_assoc]
  -- `p`-divisibility of the exponent gap (`Cz`-independent part)
  have hpdvd : (p : ℤ) ∣
      (8 * ((- (1 + 2 * β) ^ 2 * (8 : ZMod p)⁻¹).val : ℤ) + (1 + 2 * (β.val : ℤ)) ^ 2) := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast [ZMod.natCast_val, ZMod.cast_id]
    field_simp
    ring
  -- odd square is `1 mod 8`
  obtain ⟨s, hs⟩ := LeanDring.P4.odd_sq_mod_eight (β.val : ℤ)
  -- coprimality `8 ⟂ p`
  have hcop : IsCoprime (8 : ℤ) (p : ℤ) := by
    have hnc : Nat.Coprime 8 p := Nat.Coprime.pow_left 3 (Nat.coprime_two_left.mpr hodd)
    exact Int.isCoprime_iff_gcd_eq_one.mpr (by exact_mod_cast hnc)
  -- close from a `ζ`-power for the sign and an `8p`-divisibility
  have hclose : ∀ Cz : ℤ, ((χ₈ (p : ℕ) : ℤ) : ℂ) * (if p % 4 = 1 then (1 : ℂ) else I)
        = (zeta8 p) ^ Cz →
      (8 : ℤ) ∣ (8 * ((- (1 + 2 * β) ^ 2 * (8 : ZMod p)⁻¹).val : ℤ) + Cz
        - ((p : ℤ) - (1 + 2 * (β.val : ℤ)) ^ 2)) →
      (p : ℤ) ∣ Cz →
      (zeta8 p) ^ (8 * (- (1 + 2 * β) ^ 2 * (8 : ZMod p)⁻¹).val)
          * (((χ₈ (p : ℕ) : ℤ) : ℂ) * (if p % 4 = 1 then (1 : ℂ) else I))
        = (zeta8 p) ^ ((p : ℤ) - (1 + 2 * (β.val : ℤ)) ^ 2) := by
    intro Cz hCz h8 hpCz
    rw [hCz, ← zpow_natCast (zeta8 p) (8 * _), ← zpow_add₀ hne]
    set B : ℤ := (p : ℤ) - (1 + 2 * (β.val : ℤ)) ^ 2 with hB
    set A : ℤ := ((8 * (- (1 + 2 * β) ^ 2 * (8 : ZMod p)⁻¹).val : ℕ) : ℤ) with hA
    have hpgap : (p : ℤ) ∣ (A + Cz - B) := by
      have hp1 : (p : ℤ) ∣ (A + (1 + 2 * (β.val : ℤ)) ^ 2) := by rw [hA]; push_cast; exact hpdvd
      have hAB : A - B = (A + (1 + 2 * (β.val : ℤ)) ^ 2) - p := by rw [hB]; ring
      have hpAB : (p : ℤ) ∣ (A - B) := by rw [hAB]; exact dvd_sub hp1 (dvd_refl _)
      have := dvd_add hpAB hpCz
      rwa [show A - B + Cz = A + Cz - B by ring] at this
    have hdvd : (8 * p : ℤ) ∣ (A + Cz - B) := hcop.mul_dvd h8 hpgap
    have h1 : (zeta8 p) ^ (A + Cz - B) = 1 := by
      rw [show (8 * p : ℤ) = ((8 * p : ℕ) : ℤ) by push_cast; ring] at hdvd
      exact (hζ.zpow_eq_one_iff_dvd _).mpr hdvd
    rw [show A + Cz = (A + Cz - B) + B by ring, zpow_add₀ hne, h1, one_mul]
  -- case split on `p mod 8`
  have hr : p % 8 = 1 ∨ p % 8 = 3 ∨ p % 8 = 5 ∨ p % 8 = 7 := by
    have := Nat.odd_iff.mp hodd; omega
  rcases hr with h | h | h | h
  · refine hclose 0 ?_ ?_ ?_
    · rw [χ₈_nat_eq_if_mod_eight, if_neg (by omega), if_pos (by omega), if_pos (by omega),
        zpow_zero]
      norm_num
    · rw [hs]; omega
    · exact dvd_zero _
  · refine hclose (6 * p) ?_ ?_ ?_
    · have hzz : (zeta8 p) ^ (6 * (p : ℤ)) = -I := by
        rw [show (6 * (p : ℤ)) = ((6 * p : ℕ) : ℤ) by push_cast; ring, zpow_natCast]
        exact zeta8_pow_six_p
      rw [χ₈_nat_eq_if_mod_eight, if_neg (by omega), if_neg (by omega), if_neg (by omega), hzz]
      push_cast; ring
    · rw [hs]; omega
    · exact ⟨6, by ring⟩
  · refine hclose (4 * p) ?_ ?_ ?_
    · have hzz : (zeta8 p) ^ (4 * (p : ℤ)) = -1 := by
        rw [show (4 * (p : ℤ)) = ((4 * p : ℕ) : ℤ) by push_cast; ring, zpow_natCast]
        exact zeta8_pow_four_p
      rw [χ₈_nat_eq_if_mod_eight, if_neg (by omega), if_neg (by omega), if_pos (by omega), hzz]
      push_cast; ring
    · rw [hs]; omega
    · exact ⟨4, by ring⟩
  · refine hclose (2 * p) ?_ ?_ ?_
    · have hzz : (zeta8 p) ^ (2 * (p : ℤ)) = I := by
        rw [show (2 * (p : ℤ)) = ((2 * p : ℕ) : ℤ) by push_cast; ring, zpow_natCast]
        exact zeta8_pow_two_p
      rw [χ₈_nat_eq_if_mod_eight, if_neg (by omega), if_pos (by omega), if_neg (by omega), hzz]
      push_cast; ring
    · rw [hs]; omega
    · exact ⟨2, by ring⟩

/-- **The `G₁` entry, closed form.**  Assembling `g1_entry_zeta_form`, the phase
collapse `g1_phase_simp`, and the root-of-unity identity `g1_exponent_identity`,
the `G₁` distinguished A-block entry at `s = ca` is exactly
`χ(s) · √p · ζ₈ₚ^{p-(1+2β)²}` (with `χ(s) = ζ_{p²}^{1+mp}` the order-`p²`
character value).  This is the left-hand side of the value equation. -/
theorem g1_entry_form (χ : subA p (1 : ZMod p) →* ℂˣ) (β : ZMod p)
    (hz : zChar χ = (stdAddChar : AddChar (ZMod p) ℂ))
    (hb : bChar χ = (stdAddChar : AddChar (ZMod p) ℂ).mulShift β) :
    species (subA p (1 : ZMod p)) (sElt p 1)
        (DRing.basisElt (subA p (1 : ZMod p)) χ) =
      ((χ (sElt p 1) : ℂˣ) : ℂ) *
        ((Real.sqrt p : ℂ) * (zeta8 p) ^ ((p : ℤ) - (1 + 2 * (β.val : ℤ)) ^ 2)) := by
  rw [g1_entry_zeta_form χ β hz hb, g1_phase_simp, ← g1_exponent_identity β]
  ring

/-- **The `G₂` exponent identity.**  The `ζ₈ₚ`-power of the shifted phase
`-(d⁻¹·8⁻¹)` equals `ζ₈ₚ^{-d⁻¹(p+1)³}` (with `d' = (d⁻¹).val`):
a sign-free mod-`8p` CRT congruence (mod `p` via `8·8⁻¹=1` and `(p+1)³≡1`;
mod `8` via `8 ∣ (p+1)³`).  No `p mod 8` case split — unlike `G₁`, the value equation
keeps `G₂`'s sign separate from its `ζ`-power. -/
theorem g2_exponent_identity (d : ZMod p) (hd : d ≠ 0) :
    (zeta8 p) ^ (8 * (-(d⁻¹ * (8 : ZMod p)⁻¹)).val)
      = (zeta8 p) ^ (-(((d⁻¹ : ZMod p).val : ℤ) * ((p : ℤ) + 1) ^ 3)) := by
  have hp : p.Prime := Fact.out
  have hodd : Odd p := Fact.out
  have h8ne : (8 : ZMod p) ≠ 0 := eight_ne_zero'
  have hne : zeta8 p ≠ 0 := by rw [zeta8]; exact Complex.exp_ne_zero _
  have hζ : IsPrimitiveRoot (zeta8 p) (8 * p) :=
    Complex.isPrimitiveRoot_exp (8 * p) (Nat.mul_ne_zero (by norm_num) hp.ne_zero)
  have hcop : IsCoprime (8 : ℤ) (p : ℤ) := by
    have hnc : Nat.Coprime 8 p := Nat.Coprime.pow_left 3 (Nat.coprime_two_left.mpr hodd)
    exact Int.isCoprime_iff_gcd_eq_one.mpr (by exact_mod_cast hnc)
  rw [← zpow_natCast (zeta8 p) (8 * _)]
  set A : ℤ := ((8 * (-(d⁻¹ * (8 : ZMod p)⁻¹)).val : ℕ) : ℤ) with hA
  set B : ℤ := -(((d⁻¹ : ZMod p).val : ℤ) * ((p : ℤ) + 1) ^ 3) with hB
  have hpdvd : (p : ℤ) ∣ (A - B) := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, hA, hB]
    push_cast [ZMod.natCast_val, ZMod.cast_id, ZMod.natCast_self]
    field_simp
    ring
  have h8dvd : (8 : ℤ) ∣ (A - B) := by
    obtain ⟨w, hw⟩ := LeanDring.P4.eight_dvd_succ_cube hodd
    refine ⟨((-(d⁻¹ * (8 : ZMod p)⁻¹)).val : ℤ) + ((d⁻¹ : ZMod p).val : ℤ) * w, ?_⟩
    rw [hA, hB, hw]; push_cast; ring
  have hdvd : (8 * p : ℤ) ∣ (A - B) := hcop.mul_dvd h8dvd hpdvd
  have h1 : (zeta8 p) ^ (A - B) = 1 := by
    rw [show (8 * p : ℤ) = ((8 * p : ℕ) : ℤ) by push_cast; ring] at hdvd
    exact (hζ.zpow_eq_one_iff_dvd _).mpr hdvd
  rw [show A = (A - B) + B by ring, zpow_add₀ hne, h1, one_mul]

/-- **The `G₂` sign identity** (the Legendre-symbol
factorization).  For `d` a quadratic non-residue, the sign
`(2⁻¹∣p)·(d⁻¹∣p)` equals `(-1)^{(p²+7)/8}`: since `(d⁻¹∣p) = (d∣p) = -1` and
`(2⁻¹∣p) = (2∣p) = χ₈ p`, this is `χ₈ p · (-1) = (-1)^{(p²+7)/8}`, checked on
the four residues `p mod 8` (with the `(p²+7)/8` parities of
`value_equation_impossible`). -/
theorem g2_sign_identity (d : ZMod p) (hd : d ≠ 0)
    (hd_qnr : quadraticChar (ZMod p) d = -1) :
    (χq p ((2 : ZMod p)⁻¹) : ℂ) * (χq p (d⁻¹ : ZMod p) : ℂ)
      = (-1 : ℂ) ^ ((p ^ 2 + 7) / 8) := by
  have hp : p.Prime := Fact.out
  have hodd : Odd p := Fact.out
  have hp2 : p ≠ 2 := by rintro rfl; exact (by decide : ¬ Odd 2) hodd
  have h2ne : (2 : ZMod p) ≠ 0 := two_ne_zero'
  have hinvne : (2 : ZMod p)⁻¹ ≠ 0 := inv_ne_zero h2ne
  have hdinvne : (d⁻¹ : ZMod p) ≠ 0 := inv_ne_zero hd
  -- `χq(2⁻¹) = χ₈ p`
  have hls : quadraticChar (ZMod p) (2 : ZMod p) = χ₈ (p : ℕ) := by
    have h := legendreSym.at_two (p := p) hp2
    rwa [legendreSym, show (((2 : ℤ)) : ZMod p) = (2 : ZMod p) by norm_cast] at h
  have h2sign : (χq p ((2 : ZMod p)⁻¹) : ℂ) = ((χ₈ (p : ℕ) : ℤ) : ℂ) := by
    have hqc : quadraticChar (ZMod p) ((2 : ZMod p)⁻¹) = χ₈ (p : ℕ) := by
      rw [show (2 : ZMod p)⁻¹ = 2 * ((2 : ZMod p)⁻¹) ^ 2 by field_simp,
        map_mul, quadraticChar_sq_one' hinvne, mul_one, hls]
    simp only [χq, MulChar.ringHomComp_apply, hqc, eq_intCast]
  -- `χq(d⁻¹) = (d∣p) = -1`
  have hdsign : (χq p (d⁻¹ : ZMod p) : ℂ) = -1 := by
    have hqc : quadraticChar (ZMod p) (d⁻¹ : ZMod p) = quadraticChar (ZMod p) d := by
      rw [show (d⁻¹ : ZMod p) = d * (d⁻¹) ^ 2 by field_simp,
        map_mul, quadraticChar_sq_one' hdinvne, mul_one]
    simp only [χq, MulChar.ringHomComp_apply, hqc, hd_qnr]
    norm_num
  rw [h2sign, hdsign]
  -- case split on `p mod 8`, matching `χ₈ p · (-1)` to `(-1)^{(p²+7)/8}`
  have hr : p % 8 = 1 ∨ p % 8 = 3 ∨ p % 8 = 5 ∨ p % 8 = 7 := by
    have := Nat.odd_iff.mp hodd; omega
  rcases hr with h | h | h | h
  · obtain ⟨k, hk⟩ : ∃ k, p = 8 * k + 1 := ⟨p / 8, by omega⟩
    have hdiv : (p ^ 2 + 7) / 8 = 8 * k ^ 2 + 2 * k + 1 := by
      have : p ^ 2 + 7 = 8 * (8 * k ^ 2 + 2 * k + 1) := by subst hk; ring
      omega
    have hpar : Odd ((p ^ 2 + 7) / 8) := by rw [hdiv, Nat.odd_iff]; omega
    rw [χ₈_nat_eq_if_mod_eight, if_neg (by omega), if_pos (by omega), hpar.neg_one_pow]
    norm_num
  · obtain ⟨k, hk⟩ : ∃ k, p = 8 * k + 3 := ⟨p / 8, by omega⟩
    have hdiv : (p ^ 2 + 7) / 8 = 8 * k ^ 2 + 6 * k + 2 := by
      have : p ^ 2 + 7 = 8 * (8 * k ^ 2 + 6 * k + 2) := by subst hk; ring
      omega
    have hpar : Even ((p ^ 2 + 7) / 8) := by rw [hdiv, Nat.even_iff]; omega
    rw [χ₈_nat_eq_if_mod_eight, if_neg (by omega), if_neg (by omega), hpar.neg_one_pow]
    norm_num
  · obtain ⟨k, hk⟩ : ∃ k, p = 8 * k + 5 := ⟨p / 8, by omega⟩
    have hdiv : (p ^ 2 + 7) / 8 = 8 * k ^ 2 + 10 * k + 4 := by
      have : p ^ 2 + 7 = 8 * (8 * k ^ 2 + 10 * k + 4) := by subst hk; ring
      omega
    have hpar : Even ((p ^ 2 + 7) / 8) := by rw [hdiv, Nat.even_iff]; omega
    rw [χ₈_nat_eq_if_mod_eight, if_neg (by omega), if_neg (by omega), hpar.neg_one_pow]
    norm_num
  · obtain ⟨k, hk⟩ : ∃ k, p = 8 * k + 7 := ⟨p / 8, by omega⟩
    have hdiv : (p ^ 2 + 7) / 8 = 8 * k ^ 2 + 14 * k + 7 := by
      have : p ^ 2 + 7 = 8 * (8 * k ^ 2 + 14 * k + 7) := by subst hk; ring
      omega
    have hpar : Odd ((p ^ 2 + 7) / 8) := by rw [hdiv, Nat.odd_iff]; omega
    rw [χ₈_nat_eq_if_mod_eight, if_neg (by omega), if_pos (by omega), hpar.neg_one_pow]
    norm_num

/-- **The `G₂` entry, closed form.**  Assembling `g2_entry_zeta_form`,
`g2_phase_simp`, `g2_exponent_identity` (the sign-free `ζ`-power) and
`g2_sign_identity` (`(2⁻¹∣p)·(d⁻¹∣p) = (-1)^{(p²+7)/8}` for `d` a QNR), the
`G₂` distinguished A-block entry at `s = ca^d` is exactly
`χ(s) · (-1)^{(p²+7)/8} · c(p) · √p · ζ₈ₚ^{-d⁻¹(p+1)³}` (with `χ(s) = ζ_{p²}`).
This is the right-hand side of the value equation. -/
theorem g2_entry_form (χ : subA p d →* ℂˣ) (hd : d ≠ 0)
    (hd_qnr : quadraticChar (ZMod p) d = -1)
    (hz : zChar χ = (stdAddChar : AddChar (ZMod p) ℂ).mulShift d⁻¹)
    (hb : bChar χ = (stdAddChar : AddChar (ZMod p) ℂ).mulShift (-1)) :
    species (subA p d) (sElt p d) (DRing.basisElt (subA p d) χ) =
      ((χ (sElt p d) : ℂˣ) : ℂ) *
        ((-1 : ℂ) ^ ((p ^ 2 + 7) / 8) * ((if p % 4 = 1 then (1 : ℂ) else I) *
          ((Real.sqrt p : ℂ) *
            (zeta8 p) ^ (-(((d⁻¹ : ZMod p).val : ℤ) * ((p : ℤ) + 1) ^ 3))))) := by
  have hsgn := g2_sign_identity d hd hd_qnr
  rw [g2_entry_zeta_form χ hd hz hb, g2_phase_simp, g2_exponent_identity d hd]
  linear_combination ((χ (sElt p d) : ℂˣ) : ℂ) *
    (zeta8 p) ^ (-(((d⁻¹ : ZMod p).val : ℤ) * ((p : ℤ) + 1) ^ 3)) *
    (Real.sqrt p : ℂ) * (if p % 4 = 1 then (1 : ℂ) else I) * hsgn

end Model

open Complex

/-- `ζ_{p²} = exp(2πi/p²)`, the value of the order-`p²` characters `χ(ca^d)`. -/
noncomputable def zetaP2 (p : ℕ) : ℂ :=
  Complex.exp (2 * Real.pi * I / ((p ^ 2 : ℕ) : ℂ))

variable {p : ℕ} [Fact p.Prime] [Fact (Odd p)]

omit [Fact (Odd p)] in
/-- `ζ_{p²}^{mp} = ζ₈ₚ^{8m}`: both equal `exp(2πi·m/p)`.  This is the identity
that turns the `ζ_{p²}` conductor freedom on the left of the value equation
into its `+8m` term when cancelling `ζ_{p²}`. -/
theorem zetaP2_pow_eq (m : ℕ) : zetaP2 p ^ (m * p) = zeta8 p ^ (8 * m) := by
  have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  rw [zetaP2, zeta8, ← Complex.exp_nat_mul, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  field_simp

omit [Fact (Odd p)] in
/-- **Character-value extraction (root-of-unity core of the `G₁` entry).**
Any `w : ℂ` with `w^p = ζ_{p²}^p` (`= ζ_p`) is `ζ_{p²}^{1+mp}` for some `m`.
This is the abstract content of "`χ((ca)^p) = χ(a^p) = ζ_p` forces
`χ(ca) = ζ_{p²}^{1+mp}`" (the `G₁` opening): the distinguished
order-`p²` character value is a `1 mod p` power of `ζ_{p²}`.  No group
structure — purely that `ζ_{p²}` is a primitive `p²`-th root and `ζ_{p²}^p` a
primitive `p`-th root. -/
theorem exists_eq_zetaP2_pow_of_pow_eq (w : ℂ) (hw : w ^ p = zetaP2 p ^ p) :
    ∃ m : ℕ, w = zetaP2 p ^ (1 + m * p) := by
  have hp : p.Prime := Fact.out
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hprim : IsPrimitiveRoot (zetaP2 p) (p ^ 2) := by
    rw [zetaP2]; exact Complex.isPrimitiveRoot_exp (p ^ 2) (pow_ne_zero 2 hp.ne_zero)
  have hz2ne : zetaP2 p ≠ 0 := hprim.ne_zero (pow_ne_zero 2 hp.ne_zero)
  have hηprim : IsPrimitiveRoot (zetaP2 p ^ p) p :=
    hprim.pow (pow_pos hp.pos 2) (by ring)
  have hquot : (w * (zetaP2 p)⁻¹) ^ p = 1 := by
    rw [mul_pow, hw, inv_pow, mul_inv_cancel₀ (pow_ne_zero p hz2ne)]
  obtain ⟨i, _, hieq⟩ := hηprim.eq_pow_of_pow_eq_one hquot
  refine ⟨i, ?_⟩
  rw [pow_add, pow_one, mul_comm i p, pow_mul, hieq]
  field_simp

/-- **The cancellation step.**  The distinguished
entry equality that a species-table isomorphism produces — the `G₁` entry
(with `χ(ca) = ζ_{p²}^{1+mp}`) equal to the `G₂` entry `z`
(`χ(ca^d) = ζ_{p²}`) — is impossible: cancelling the common
`√p · ζ_{p²}` (and folding `ζ_{p²}^{1+mp}/ζ_{p²} = ζ₈ₚ^{8m}` via `zetaP2_pow_eq`)
yields exactly the value equation, refuted by `value_equation_impossible`.  This
discharges the arithmetic of the endgame, leaving only the structural
extraction of the entry equality from a table iso. -/
theorem twin_entry_equality_impossible (m β : ℕ) (d' : ℤ)
    (heq : zetaP2 p ^ (1 + m * p) *
        ((Real.sqrt p : ℂ) * zeta8 p ^ ((p : ℤ) - (1 + 2 * (β : ℤ)) ^ 2))
      = zetaP2 p * ((-1 : ℂ) ^ ((p ^ 2 + 7) / 8) *
          ((if p % 4 = 1 then (1 : ℂ) else I) *
            ((Real.sqrt p : ℂ) * zeta8 p ^ (-(d' * ((p : ℤ) + 1) ^ 3)))))) :
    False := by
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := by
    have hodd : Odd p := Fact.out; rintro rfl; exact (by decide : ¬ Odd 2) hodd
  have hsqrt : (Real.sqrt p : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    exact Real.sqrt_ne_zero'.mpr (by exact_mod_cast hp.pos)
  have hzp2 : zetaP2 p ≠ 0 := by rw [zetaP2]; exact Complex.exp_ne_zero _
  have hz8 : zeta8 p ≠ 0 := by rw [zeta8]; exact Complex.exp_ne_zero _
  refine value_equation_impossible p hp hp2 m β d' ?_
  rw [show Complex.exp (2 * Real.pi * I / ((8 * p : ℕ) : ℂ)) = zeta8 p from rfl]
  rw [pow_add, pow_one, zetaP2_pow_eq] at heq
  apply mul_left_cancel₀ (mul_ne_zero hzp2 hsqrt)
  rw [show ((p : ℤ) - (1 + 2 * (β : ℤ)) ^ 2 + 8 * (m : ℤ))
        = ((p : ℤ) - (1 + 2 * (β : ℤ)) ^ 2) + ((8 * m : ℕ) : ℤ) by push_cast; ring,
    zpow_add₀ hz8, zpow_natCast]
  linear_combination heq

namespace Model

/-- **The `G₁` distinguished character value.**  A character `χ` of `A = subA p 1`
that restricts to the standard additive character on the centre (`zChar χ = stdAddChar`,
i.e. `χ(aᵖ) = ζ_p`) sends the `C_{p²}` generator `s = ca` to `ζ_{p²}^{1+mp}` for some
`m` — the `G₁` entry opening. -/
theorem char_sElt_extraction (hp5 : 5 ≤ p) (χ : subA p (1 : ZMod p) →* ℂˣ)
    (hz : zChar χ = (ZMod.stdAddChar : AddChar (ZMod p) ℂ)) :
    ∃ m : ℕ, ((χ (sElt p 1) : ℂˣ) : ℂ) = zetaP2 p ^ (1 + m * p) := by
  have h1 : (sElt p 1 : subA p 1) ^ p = zElt p 1 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, sElt_coe, pow_p hp5 (⟨0, 1, 0⟩ : Model p 1)]
    change (⟨liftp p (redp p 0 + 1 * 1), 0, 0⟩ : Model p 1) = ⟨liftp p 1, 0, 0⟩
    congr 2
    rw [map_zero (redp p)]
    ring
  have h2 : (ZMod.stdAddChar : AddChar (ZMod p) ℂ) 1 = zetaP2 p ^ p := by
    have hval : (1 : ZMod p).val = 1 := ZMod.val_one p
    have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
    rw [stdAddChar_eq_zeta_pow 1, hval, mul_one]
    rw [zeta8_pow_eight]
    rw [zetaP2, ← Complex.exp_nat_mul]
    congr 1
    have hpow : ((p ^ 2 : ℕ) : ℂ) = (p : ℂ) ^ 2 := by push_cast; rfl
    rw [hpow]
    field_simp
  have h3 : (((χ (sElt p 1) : ℂˣ) : ℂ) ^ p) = zetaP2 p ^ p := by
    rw [← Units.val_pow_eq_pow_val, ← map_pow, h1]
    have hdef : ((χ (zElt p 1 1) : ℂˣ) : ℂ) = zChar χ 1 := rfl
    rw [hdef, hz]
    exact h2
  exact exists_eq_zetaP2_pow_of_pow_eq _ h3

/-- **The `ζ_{p²}`-matching forces `u = 1`, so the non-residue case is
vacuous.**  For `h ∈ A = subA p 1` and `χ` with `zChar χ = stdAddChar`: if
`χ(h)^p = ζ_{p²}^p` — which is exactly the conclusion of
`eq_pow_of_mul_eq_zetaP2_mul` when the A-block entry equals the `G₂`
distinguished value `z` — then the `s`-coordinate `h.u = 1`.  Indeed `h ∈ subA`
has `redp α = 0`, so `pow_p` gives `h^p = zElt(u)` and hence
`χ(h)^p = zChar χ (u) = stdAddChar(u)`; comparing with `ζ_{p²}^p = ζ₈ₚ^8 =
stdAddChar(1)` and using that `stdAddChar` is a primitive-root power of `ζ₈ₚ`
pins `u = 1`.  Consequence: **every entry that can equal `z` has `u = 1 = 1²`, a
quadratic residue** — `A_block_qr_closed_form` (with `t = 1`) applies and the
non-residue case never occurs. -/
theorem u_eq_one_of_char_pow (hp5 : 5 ≤ p) (χ : subA p (1 : ZMod p) →* ℂˣ)
    (h : subA p (1 : ZMod p))
    (hz : zChar χ = (ZMod.stdAddChar : AddChar (ZMod p) ℂ))
    (hpow : ((χ h : ℂˣ) : ℂ) ^ p = zetaP2 p ^ p) :
    (h : Model p 1).u = 1 := by
  have hp : p.Prime := Fact.out
  -- `h ∈ subA` (`redp α = 0`) makes `hᵖ = zElt(u)`
  have hhp : (h ^ p) = zElt p 1 ((h : Model p 1).u) := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, pow_p hp5 (h : Model p 1), mem_subA_iff.mp h.2, zero_add, one_mul]
    rfl
  -- so `χ(h)ᵖ = stdAddChar(u)`
  have hval : ((χ h : ℂˣ) : ℂ) ^ p
      = (ZMod.stdAddChar : AddChar (ZMod p) ℂ) ((h : Model p 1).u) := by
    rw [← Units.val_pow_eq_pow_val, ← map_pow, hhp, ← hz]; rfl
  -- `ζ_{p²}ᵖ = ζ₈ₚ⁸`
  have hzp : zetaP2 p ^ p = zeta8 p ^ 8 := by
    rw [zeta8_pow_eight, zetaP2, ← Complex.exp_nat_mul]
    congr 1
    have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
    rw [show ((p ^ 2 : ℕ) : ℂ) = (p : ℂ) ^ 2 by push_cast; rfl]
    field_simp
  -- `ζ₈ₚ^{8·u.val} = ζ₈ₚ⁸`, so `u.val = 1` by primitivity
  have hstd : (zeta8 p) ^ (8 * (h : Model p 1).u.val) = zeta8 p ^ 8 := by
    rw [← stdAddChar_eq_zeta_pow, ← hval, hpow, hzp]
  have hζ : IsPrimitiveRoot (zeta8 p) (8 * p) :=
    Complex.isPrimitiveRoot_exp (8 * p) (Nat.mul_ne_zero (by norm_num) hp.ne_zero)
  have hlt1 : 8 * (h : Model p 1).u.val < 8 * p := by
    have := ZMod.val_lt (h : Model p 1).u; omega
  have heq : 8 * (h : Model p 1).u.val = 8 := hζ.pow_inj hlt1 (by omega) hstd
  have huval : (h : Model p 1).u.val = 1 := by omega
  rw [show (h : Model p 1).u = (((h : Model p 1).u.val : ℕ) : ZMod p) by
    rw [ZMod.natCast_val, ZMod.cast_id], huval, Nat.cast_one]

/-- **`ζ_{p²}`-matching forces `u = k⁻¹` for a general central shift `k`.**
Generalises `u_eq_one_of_char_pow` (the `k = 1` case): if `zChar χ =
stdAddChar.mulShift k` (`k ≠ 0`) and `χ(h)ᵖ = ζ_{p²}ᵖ`, then `h.u = k⁻¹`.  Same
route — `hᵖ = zElt(u)` gives `χ(h)ᵖ = stdAddChar(k·u)`, matched to
`stdAddChar(1)` forces `k·u = 1`.  This is the coordinate the general column
character produces; with it the Gauss leading sign is `χq(u·2⁻¹)·χq(k) =
χq(2⁻¹)`, so the entry's sign and phase are *uniformly* of the `G₁` shape and no
residue/non-residue split is needed. -/
theorem u_eq_kinv_of_char_pow (hp5 : 5 ≤ p) (χ : subA p (1 : ZMod p) →* ℂˣ)
    (h : subA p (1 : ZMod p)) (k : ZMod p)
    (hz : zChar χ = (ZMod.stdAddChar : AddChar (ZMod p) ℂ).mulShift k)
    (hpow : ((χ h : ℂˣ) : ℂ) ^ p = zetaP2 p ^ p) :
    (h : Model p 1).u = k⁻¹ := by
  have hp : p.Prime := Fact.out
  have hhp : (h ^ p) = zElt p 1 ((h : Model p 1).u) := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, pow_p hp5 (h : Model p 1), mem_subA_iff.mp h.2, zero_add, one_mul]
    rfl
  have hval : ((χ h : ℂˣ) : ℂ) ^ p
      = (ZMod.stdAddChar : AddChar (ZMod p) ℂ) (k * (h : Model p 1).u) := by
    rw [← Units.val_pow_eq_pow_val, ← map_pow, hhp]
    change zChar χ ((h : Model p 1).u) = _
    rw [hz, AddChar.mulShift_apply]
  have hzp : zetaP2 p ^ p = zeta8 p ^ 8 := by
    rw [zeta8_pow_eight, zetaP2, ← Complex.exp_nat_mul]
    congr 1
    have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
    rw [show ((p ^ 2 : ℕ) : ℂ) = (p : ℂ) ^ 2 by push_cast; rfl]
    field_simp
  have hstd : (zeta8 p) ^ (8 * (k * (h : Model p 1).u).val) = zeta8 p ^ 8 := by
    rw [← stdAddChar_eq_zeta_pow, ← hval, hpow, hzp]
  have hζ : IsPrimitiveRoot (zeta8 p) (8 * p) :=
    Complex.isPrimitiveRoot_exp (8 * p) (Nat.mul_ne_zero (by norm_num) hp.ne_zero)
  have hlt1 : 8 * (k * (h : Model p 1).u).val < 8 * p := by
    have := ZMod.val_lt (k * (h : Model p 1).u); omega
  have heq : 8 * (k * (h : Model p 1).u).val = 8 := hζ.pow_inj hlt1 (by omega) hstd
  have hku : k * (h : Model p 1).u = 1 := by
    rw [show k * (h : Model p 1).u = (((k * (h : Model p 1).u).val : ℕ) : ZMod p) by
      rw [ZMod.natCast_val, ZMod.cast_id], show (k * (h : Model p 1).u).val = 1 by omega,
      Nat.cast_one]
  exact (inv_eq_of_mul_eq_one_right hku).symm

/-- **The general-`k` phase collapses to the `G₁` phase `-(1+2β)²·8⁻¹`** with
`β = κ + k·v`, once `u = k⁻¹`.  Multiplying the `species_A_block_gauss` phase
argument (at `d = 1`, `u = k⁻¹`) by the central shift `k` and simplifying:
`k·(-(k⁻¹+v-k⁻¹/2+κk⁻¹)²·(4·(k⁻¹/2))⁻¹) = -(1+2(κ+kv))²·8⁻¹`. -/
theorem kphase_simp (v κ k : ZMod p) (hk : k ≠ 0) :
    k * (- ((1 : ZMod p) * k⁻¹ + v - k⁻¹ * (2 : ZMod p)⁻¹ + κ * k⁻¹) ^ 2 *
        (4 * (k⁻¹ * (2 : ZMod p)⁻¹))⁻¹)
      = - (1 + 2 * (κ + k * v)) ^ 2 * (8 : ZMod p)⁻¹ := by
  have h2 : (2 : ZMod p) ≠ 0 := two_ne_zero'
  have h8 : (8 : ZMod p) ≠ 0 := eight_ne_zero'
  have hden : (4 : ZMod p) * (k⁻¹ * (2 : ZMod p)⁻¹) = 2 * k⁻¹ := by
    rw [show k⁻¹ * (2 : ZMod p)⁻¹ = (2 : ZMod p)⁻¹ * k⁻¹ by ring, ← mul_assoc, four_mul_two_inv]
  rw [hden]
  field_simp
  ring

end Model

end LeanDring.P4
