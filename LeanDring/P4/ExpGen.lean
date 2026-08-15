/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P4.TwinSeparation

/-!
# The `G₁` A-block entry at a general column and a general central shift

`g1_entry_form` evaluates the `G₁` A-block entry at the distinguished column
element `ca` and the distinguished character. The value step needs it at an
*arbitrary* column element `h ∈ A` and an arbitrary central shift, and this file
supplies that:

* `A_block_qr_closed_form` — for a column whose `s`-coordinate `u` is a nonzero
  quadratic residue, the entry collapses onto the `G₁` entry value
  `χ(h)·√p·ζ₈ₚ^{p-(1+2β)²}`;
* `A_block_kgen_closed_form` — the same closed form for every column forced by
  `u_eq_kinv_of_char_pow` (namely `u = k⁻¹` for the central shift `k`), with no
  residue/non-residue split.

`exp_phase_qr` and `sign_qr` are the two pieces of `ZMod p` arithmetic that make
the quadratic-residue case collapse.
-/

namespace LeanDring.P4.Model

open DRing ZMod

variable {p : ℕ} [Fact p.Prime] [Fact (Odd p)]

/-- For `u = t²` (`t ≠ 0`), the general A-block phase `-(u(2⁻¹+κ)+v)²·(2u)⁻¹`
equals `g1`'s phase `-(1+2β)²·8⁻¹` with `β = (u(2⁻¹+κ)+v)·t⁻¹ − 2⁻¹`. -/
theorem exp_phase_qr (u v κ t : ZMod p) (ht : t ^ 2 = u) (ht0 : t ≠ 0) :
    (- (u * ((2 : ZMod p)⁻¹ + κ) + v) ^ 2 * (2 * u)⁻¹)
      = - (1 + 2 * ((u * ((2 : ZMod p)⁻¹ + κ) + v) * t⁻¹ - (2 : ZMod p)⁻¹)) ^ 2
          * (8 : ZMod p)⁻¹ := by
  have h2 : (2 : ZMod p) ≠ 0 := two_ne_zero' (p := p)
  have h8 : (8 : ZMod p) ≠ 0 := by
    have : (8 : ZMod p) = 2 ^ 3 := by norm_num
    rw [this]
    exact pow_ne_zero 3 h2
  subst ht
  field_simp
  ring

omit [Fact (Odd p)] in
/-- For `u = t²` (`t ≠ 0`), `χq(u·2⁻¹) = χq(2⁻¹)` in `ℂ` (the extra `(u∣p)=1`). -/
theorem sign_qr (u t : ZMod p) (ht : t ^ 2 = u) (ht0 : t ≠ 0) :
    (χq p (u * (2 : ZMod p)⁻¹) : ℂ) = (χq p ((2 : ZMod p)⁻¹) : ℂ) := by
  have h_mul : χq p (u * (2 : ZMod p)⁻¹) = χq p u * χq p ((2 : ZMod p)⁻¹) :=
    map_mul (χq p) u ((2 : ZMod p)⁻¹)
  rw [h_mul]
  have h_u : χq p u = 1 := by
    have h_u_q : quadraticChar (ZMod p) u = 1 := by
      subst ht
      exact quadraticChar_sq_one' ht0
    change (((quadraticChar (ZMod p) u : ℤ) : ℂ)) = 1
    rw [h_u_q]
    norm_num
  rw [h_u, one_mul]

/-- **The QR-slice general-`h` A-block entry, closed form.**  When the column
element's `s`-coordinate `u = h.u` is a quadratic residue (`u = t²`, `t ≠ 0`),
the general `G₁` A-block entry collapses *exactly* onto the `G₁` entry
value `χ(h) · √p · ζ₈ₚ^{p-(1+2β)²}`, with `β = (u(2⁻¹+κ)+v)·t⁻¹ − 2⁻¹`.
Assembles `A_block_gauss_zeta` (general `ζ`-form) + `phase_gen_simp` (phase
collapse) + `exp_phase_qr`/`sign_qr` (the QR arithmetic) +
`g1_exponent_identity` (the `u=1` reciprocity).  With `char_sElt_extraction`'s
`χ(h)=ζ_{p²}^{1+mp}` this is the left side of the value equation, so every
**quadratic-residue** column entry feeds `value_equation_impossible` — it cannot
equal the `G₂` entry `z`.  (The non-residue case cannot occur; see
`u_eq_one_of_char_pow`.) -/
theorem A_block_qr_closed_form (χ : subA p (1 : ZMod p) →* ℂˣ)
    (h : subA p (1 : ZMod p)) (hu : (h : Model p 1).u ≠ 0) (κ t : ZMod p)
    (ht : t ^ 2 = (h : Model p 1).u) (ht0 : t ≠ 0)
    (hz : zChar χ = (stdAddChar : AddChar (ZMod p) ℂ))
    (hb : bChar χ = (stdAddChar : AddChar (ZMod p) ℂ).mulShift κ) :
    species (subA p (1 : ZMod p)) h (DRing.basisElt (subA p (1 : ZMod p)) χ) =
      ((χ h : ℂˣ) : ℂ) *
        ((Real.sqrt p : ℂ) * (zeta8 p) ^ ((p : ℤ) -
          (1 + 2 * ((((h : Model p 1).u * ((2 : ZMod p)⁻¹ + κ) + (h : Model p 1).v)
            * t⁻¹ - (2 : ZMod p)⁻¹).val : ℤ)) ^ 2)) := by
  rw [A_block_gauss_zeta χ h hu κ hz hb]
  set u := (h : Model p 1).u with hu_def
  set v := (h : Model p 1).v with hv_def
  congr 1
  rw [phase_gen_simp u v κ hu, exp_phase_qr u v κ t ht ht0, sign_qr u t ht ht0,
    ← g1_exponent_identity ((u * ((2 : ZMod p)⁻¹ + κ) + v) * t⁻¹ - (2 : ZMod p)⁻¹)]
  ring

/-- **The general-`k` A-block entry, closed form** — the ω-scaling of the value
step.  For `h ∈ A = subA p 1` with `u = k⁻¹` (the coordinate
forced by `u_eq_kinv_of_char_pow`), central shift `zChar χ = stdAddChar.mulShift k`
(`k ≠ 0`), and `b`-shift `κ`, the entry is `χ(h)·√p·ζ₈ₚ^{p-(1+2β)²}` with
`β = κ + k·v`.  No residue/non-residue split: `u = k⁻¹` makes the Gauss leading
sign `χq(u/2)·χq(k) = χq(2⁻¹)` and the phase `k·(…) = -(1+2β)²·8⁻¹`
(`kphase_simp`) collapse uniformly onto `g1_exponent_identity`.  This settles the
value half of the reduction: every A-block entry that can equal the `G₂` value
`z` has this `G₁` entry form, so `hentry` needs only the row/column matching. -/
theorem A_block_kgen_closed_form (χ : subA p (1 : ZMod p) →* ℂˣ)
    (h : subA p (1 : ZMod p)) (k κ : ZMod p) (hk : k ≠ 0)
    (huk : (h : Model p 1).u = k⁻¹)
    (hz : zChar χ = (stdAddChar : AddChar (ZMod p) ℂ).mulShift k)
    (hb : bChar χ = (zChar χ).mulShift κ) :
    species (subA p (1 : ZMod p)) h (DRing.basisElt (subA p (1 : ZMod p)) χ) =
      ((χ h : ℂˣ) : ℂ) * ((Real.sqrt p : ℂ) *
        (zeta8 p) ^ ((p : ℤ) - (1 + 2 * ((κ + k * (h : Model p 1).v).val : ℤ)) ^ 2)) := by
  have hp2 : p ≠ 2 := by rintro rfl; exact (by decide : ¬ Odd 2) Fact.out
  have hu : (h : Model p 1).u ≠ 0 := by rw [huk]; exact inv_ne_zero hk
  have hunit : IsUnit k := isUnit_iff_ne_zero.mpr hk
  have hψ : zChar χ ≠ 1 := by rw [hz]; exact (ZMod.isPrimitive_stdAddChar p) hk
  have hgs : gaussSum (χq p) ((stdAddChar : AddChar (ZMod p) ℂ).mulShift k)
      = χq p k * LeanDring.GaussSign.gauss p := by
    have hh := gaussSum_mulShift_eq (χq p) (stdAddChar : AddChar (ZMod p) ℂ) hunit.unit
    rw [hunit.unit_spec, χq_isQuadratic.inv] at hh
    exact hh
  have hsign : χq p (k⁻¹ * (2 : ZMod p)⁻¹) * χq p k = χq p ((2 : ZMod p)⁻¹) := by
    rw [← map_mul]; congr 1; field_simp
  rw [species_A_block_gauss χ h hψ hu κ hb, hz, AddChar.mulShift_apply,
    stdAddChar_eq_zeta_pow, hgs, gauss_eq_sqrt_mul hp2, huk,
    kphase_simp (h : Model p 1).v κ k hk]
  congr 1
  rw [← g1_exponent_identity (κ + k * (h : Model p 1).v),
    show χq p (k⁻¹ * (2 : ZMod p)⁻¹) * (χq p k * ((Real.sqrt p : ℂ) *
        (if p % 4 = 1 then (1 : ℂ) else Complex.I)))
      = (χq p (k⁻¹ * (2 : ZMod p)⁻¹) * χq p k) * ((Real.sqrt p : ℂ) *
        (if p % 4 = 1 then (1 : ℂ) else Complex.I)) by ring, hsign]
  ring

end LeanDring.P4.Model
