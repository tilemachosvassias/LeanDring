/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P4.Hentry
import LeanDring.P4.ExpGen
import LeanDring.P4.ExpA

/-!
# The value contradiction: a `G₁` A-block entry cannot equal `z`

`A_block_entry_eq_z_impossible`: if a `Model p 1` A-block species entry
(general column character `χ₁`, column element `h₁ ∈ A`) equals the `G₂`
distinguished entry `z` (`χ_dist(ca^d) = ζ_{p²}`, `d` a non-residue),
then `False`. This is the entire value content of `hentry`, threading:

* `entry_not_mem_adjoin` — `z ∉ ℤ[ζ_p]`;
* `A_block_mem_adjoin_iff_gen` — so `χ₁(h₁)ᵖ ≠ 1`, hence `zChar χ₁ ≠ 1`;
* `addChar_eq_mulShift` — extract the central shift `k` and `b`-shift `κ`;
* `eq_pow_of_mul_eq_zetaP2_mul` — `χ₁(h₁)ᵖ = ζ_{p²}ᵖ` from the entry
  and `z` factorisations `χ₁(h₁)·bracket₁ = ζ_{p²}·bracket₂`;
* `u_eq_kinv_of_char_pow` — `h₁.u = k⁻¹`;
* `A_block_kgen_closed_form` — the entry is in the `G₁` entry form;
* `exists_eq_zetaP2_pow_of_pow_eq` — `χ₁(h₁) = ζ_{p²}^{1+mp}`;
* `twin_entry_equality_impossible` — the resulting value equation has no solution.

`hentry` then needs only the structural row/column matching to produce such a
`χ₁, h₁` from a species-table isomorphism.
-/

namespace LeanDring.P4

open DRing MonGSet Model MulAction Complex

variable {p : ℕ} [Fact p.Prime] [Fact (Odd p)]

open scoped Classical in
/-- **The value contradiction.**  A `Model p 1` A-block entry equal to the `G₂`
distinguished value `z` is impossible. -/
theorem A_block_entry_eq_z_impossible (hp5 : 5 ≤ p) {d : ZMod p} (hd : d ≠ 0)
    (hd_qnr : quadraticChar (ZMod p) d = -1)
    (χ₁ : subA p (1 : ZMod p) →* ℂˣ) (h₁ : subA p (1 : ZMod p))
    (χdist : subA p d →* ℂˣ)
    (hχz : zChar χdist = (ZMod.stdAddChar : AddChar (ZMod p) ℂ).mulShift d⁻¹)
    (hχb : bChar χdist = (ZMod.stdAddChar : AddChar (ZMod p) ℂ).mulShift (-1))
    (hχs : ((χdist (sElt p d) : ℂˣ) : ℂ) = zetaP2 p)
    (heq : species (subA p (1 : ZMod p)) h₁ (DRing.basisElt (subA p (1 : ZMod p)) χ₁)
         = species (subA p d) (sElt p d) (DRing.basisElt (subA p d) χdist)) :
    False := by
  have hp : p.Prime := Fact.out
  have hodd : Odd p := Fact.out
  have hp2 : p ≠ 2 := by rintro rfl; exact (by decide : ¬ Odd 2) hodd
  have hζp2 : IsPrimitiveRoot (zetaP2 p) (p ^ 2) := by
    rw [zetaP2]; exact Complex.isPrimitiveRoot_exp (p ^ 2) (pow_ne_zero 2 hp.ne_zero)
  have hζp : IsPrimitiveRoot ((zetaP2 p) ^ p) p := hζp2.pow (pow_pos hp.pos 2) (by ring)
  -- `z` in closed form and its nonvanishing / non-membership
  set z := species (subA p d) (sElt p d) (DRing.basisElt (subA p d) χdist) with hz_def
  have hzform : z = zetaP2 p * ((-1 : ℂ) ^ ((p ^ 2 + 7) / 8) *
      ((if p % 4 = 1 then (1 : ℂ) else I) *
        ((Real.sqrt p : ℂ) * zeta8 p ^
          (-(((d⁻¹ : ZMod p).val : ℤ) * ((p : ℤ) + 1) ^ 3))))) := by
    rw [hz_def, g2_entry_form χdist hd hd_qnr hχz hχb, hχs]
  have hz_ne : z ≠ 0 := by
    rw [hzform]
    have h1 : zetaP2 p ≠ 0 := by rw [zetaP2]; exact Complex.exp_ne_zero _
    have h2 : ((-1 : ℂ) ^ ((p ^ 2 + 7) / 8)) ≠ 0 := pow_ne_zero _ (by norm_num)
    have h3 : (if p % 4 = 1 then (1 : ℂ) else I) ≠ 0 := by
      split <;> simp [Complex.I_ne_zero]
    have h4 : (Real.sqrt p : ℂ) ≠ 0 := by
      simp only [ne_eq, Complex.ofReal_eq_zero]
      exact Real.sqrt_ne_zero'.mpr (by exact_mod_cast hp.pos)
    have h5 : zeta8 p ^ (-(((d⁻¹ : ZMod p).val : ℤ) * ((p : ℤ) + 1) ^ 3)) ≠ 0 :=
      zpow_ne_zero _ (by rw [zeta8]; exact Complex.exp_ne_zero _)
    exact mul_ne_zero h1 (mul_ne_zero h2 (mul_ne_zero h3 (mul_ne_zero h4 h5)))
  have hz_notmem : z ∉ (Algebra.adjoin ℤ {(zetaP2 p) ^ p} : Subalgebra ℤ ℂ) :=
    entry_not_mem_adjoin hp5 χdist hχs hz_ne
  -- transfer to the `G₁` entry
  have hent_ne :
      species (subA p (1 : ZMod p)) h₁ (DRing.basisElt (subA p (1 : ZMod p)) χ₁) ≠ 0 := by
    rw [heq]; exact hz_ne
  have hent_notmem :
      species (subA p (1 : ZMod p)) h₁ (DRing.basisElt (subA p (1 : ZMod p)) χ₁)
        ∉ (Algebra.adjoin ℤ {(zetaP2 p) ^ p} : Subalgebra ℤ ℂ) := by
    rw [heq]; exact hz_notmem
  have hpow_ne : ((χ₁ h₁ : ℂˣ) : ℂ) ^ p ≠ 1 := fun hcon =>
    hent_notmem ((A_block_mem_adjoin_iff_gen hp5 χ₁ h₁ hent_ne).mpr hcon)
  -- extract the central shift `k`
  obtain ⟨k, hk⟩ := addChar_eq_mulShift (ZMod.stdAddChar : AddChar (ZMod p) ℂ) (zChar χ₁)
    (LeanDring.GaussSign.stdAddChar_ne_one p)
  -- factorisations `entry = χ₁(h₁)·bracket₁`, `z = ζ_{p²}·bracket₂`,
  -- brackets in `ℤ[ζ_p]`
  set br₁ : ℂ := ∑ t : ZMod p,
    ((χ₁ ((h₁)⁻¹ * conjA p 1 (aGen p 1 ^ t.val) h₁) : ℂˣ) : ℂ) with hbr₁_def
  set br₂ : ℂ := ∑ t : ZMod p,
    ((χdist ((sElt p d)⁻¹ * conjA p d (aGen p d ^ t.val) (sElt p d)) : ℂˣ) : ℂ)
    with hbr₂_def
  have hentfac : species (subA p (1 : ZMod p)) h₁ (DRing.basisElt (subA p (1 : ZMod p)) χ₁)
      = ((χ₁ h₁ : ℂˣ) : ℂ) * br₁ := entry_factor_gen χ₁ h₁
  have hzfac : z = zetaP2 p * br₂ := by rw [hz_def, entry_factor χdist, hχs]
  have hbr₁_mem : br₁ ∈ (Algebra.adjoin ℤ {(zetaP2 p) ^ p} : Subalgebra ℤ ℂ) :=
    Subalgebra.sum_mem _ fun t _ => mem_adjoin_of_pow_eq_one hp hζp (by
      rw [← Units.val_pow_eq_pow_val, ← map_pow, disp_pow_p_gen hp5 h₁ t, map_one,
        Units.val_one])
  have hbr₂_mem : br₂ ∈ (Algebra.adjoin ℤ {(zetaP2 p) ^ p} : Subalgebra ℤ ℂ) :=
    Subalgebra.sum_mem _ fun t _ => mem_adjoin_of_pow_eq_one hp hζp (by
      rw [← Units.val_pow_eq_pow_val, ← map_pow, disp_pow_p hp5 t, map_one, Units.val_one])
  have hbr₁_ne : br₁ ≠ 0 := by
    intro h0; apply hent_ne; rw [hentfac, h0, mul_zero]
  have hmuleq : ((χ₁ h₁ : ℂˣ) : ℂ) * br₁ = zetaP2 p * br₂ := by
    rw [← hentfac, heq, ← hzfac]
  have hw : ((χ₁ h₁ : ℂˣ) : ℂ) ^ (p ^ 2) = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← map_pow, subA_pow_psq hp5 h₁, map_one, Units.val_one]
  have hgem7 : ((χ₁ h₁ : ℂˣ) : ℂ) ^ p = zetaP2 p ^ p :=
    eq_pow_of_mul_eq_zetaP2_mul hp hodd hζp2 hζp hw hbr₁_mem hbr₂_mem hbr₁_ne hmuleq
  -- `zChar χ₁ ≠ 1`, hence `k ≠ 0`
  have hh₁p : (h₁ ^ p) = zElt p 1 ((h₁ : Model p 1).u) := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, pow_p hp5 (h₁ : Model p 1), mem_subA_iff.mp h₁.2, zero_add, one_mul]
    rfl
  have hzc_ne : zChar χ₁ ≠ 1 := by
    intro hcon
    apply hpow_ne
    have hval : ((χ₁ h₁ : ℂˣ) : ℂ) ^ p = zChar χ₁ ((h₁ : Model p 1).u) := by
      rw [← Units.val_pow_eq_pow_val, ← map_pow, hh₁p]; rfl
    rw [hval, hcon]; rfl
  have hk0 : k ≠ 0 := by
    intro hcon; rw [hcon, AddChar.mulShift_zero] at hk; exact hzc_ne hk
  obtain ⟨κ, hκ⟩ := addChar_eq_mulShift (zChar χ₁) (bChar χ₁) hzc_ne
  have huk : (h₁ : Model p 1).u = k⁻¹ := u_eq_kinv_of_char_pow hp5 χ₁ h₁ k hk hgem7
  obtain ⟨m, hm⟩ := exists_eq_zetaP2_pow_of_pow_eq ((χ₁ h₁ : ℂˣ) : ℂ) hgem7
  -- assemble the value equation and refute it
  refine twin_entry_equality_impossible (p := p) m (κ + k * (h₁ : Model p 1).v).val
    ((d⁻¹ : ZMod p).val : ℤ) ?_
  have hL : zetaP2 p ^ (1 + m * p) *
        ((Real.sqrt p : ℂ) * zeta8 p ^ ((p : ℤ) -
          (1 + 2 * (((κ + k * (h₁ : Model p 1).v).val : ℕ) : ℤ)) ^ 2))
      = species (subA p (1 : ZMod p)) h₁ (DRing.basisElt (subA p (1 : ZMod p)) χ₁) := by
    rw [A_block_kgen_closed_form χ₁ h₁ k κ hk0 huk hk hκ, hm]
  rw [hL, heq]; exact hzform

end LeanDring.P4
