/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P4.CharDist
import LeanDring.P4.ARowDetect
import LeanDring.P4.HentryValue

/-!
# The last twin `(xii)/(xiii)` has non-isomorphic species tables

`isEmpty_tableIso_model_model`: for `5 ≤ p` and `d ≠ 0` a quadratic non-residue,
there is no
`SpeciesTableIso (Model p 1) (Model p d)`. This assembles the whole endgame:
* `exists_charDist` — the distinguished `G₂` character `χdist`, giving the entry `z`;
* the row `ρ` with `z` as its `G₁` entry, built explicitly below (the statement
  form is `exists_G1_entry_eq`);
* the `⊥`-mark transport pins `|ρ.out.1| = p³`, and `z ∉ ℤ[ζ_p]` supplies a
  primitive character value, so `eq_subA_of_char_primitive` forces `ρ.out.1 = subA`;
* `species_A_row_eq_zero_of_not_le` + `species_le_normal_eq` reduce to an A-block
  entry, and `A_block_entry_eq_z_impossible` refutes it.
-/

namespace LeanDring.P4

open DRing MonGSet Model MulAction Complex

variable {p : ℕ} [Fact p.Prime] [Fact (Odd p)]

/-- **The twin separation.** For `5 ≤ p`, the order-`p⁴` twins `Model p 1` and
`Model p d` (`d` a quadratic non-residue) have non-isomorphic species tables. -/
theorem isEmpty_tableIso_model_model (hp5 : 5 ≤ p) {d : ZMod p} (hd : d ≠ 0)
    (hd_qnr : quadraticChar (ZMod p) d = -1) :
    IsEmpty (SpeciesTableIso (Model p 1) (Model p d)) := by
  have hp : p.Prime := Fact.out
  have hζp2 : IsPrimitiveRoot (zetaP2 p) (p ^ 2) := by
    rw [zetaP2]; exact Complex.isPrimitiveRoot_exp (p ^ 2) (pow_ne_zero 2 hp.ne_zero)
  have hζp : IsPrimitiveRoot ((zetaP2 p) ^ p) p := hζp2.pow (pow_pos hp.pos 2) (by ring)
  constructor
  intro T
  obtain ⟨χdist, hχs, hχz, hχb⟩ := exists_charDist hp5 hd
  set z := species (subA p d) (sElt p d) (DRing.basisElt (subA p d) χdist) with hz_def
  -- `z ≠ 0` and `z ∉ ℤ[ζ_p]`
  have hz_ne : z ≠ 0 := by
    rw [hz_def, g2_entry_form χdist hd hd_qnr hχz hχb, hχs]
    have h1 : zetaP2 p ≠ 0 := by rw [zetaP2]; exact Complex.exp_ne_zero _
    have h2 : ((-1 : ℂ) ^ ((p ^ 2 + 7) / 8)) ≠ 0 := pow_ne_zero _ (by norm_num)
    have h3 : (if p % 4 = 1 then (1 : ℂ) else I) ≠ 0 := by split <;> simp [Complex.I_ne_zero]
    have h4 : (Real.sqrt p : ℂ) ≠ 0 := by
      simp only [ne_eq, Complex.ofReal_eq_zero]
      exact Real.sqrt_ne_zero'.mpr (by exact_mod_cast hp.pos)
    have h5 : zeta8 p ^ (-(((d⁻¹ : ZMod p).val : ℤ) * ((p : ℤ) + 1) ^ 3)) ≠ 0 :=
      zpow_ne_zero _ (by rw [zeta8]; exact Complex.exp_ne_zero _)
    exact mul_ne_zero h1 (mul_ne_zero h2 (mul_ne_zero h3 (mul_ne_zero h4 h5)))
  have hz_notmem : z ∉ (Algebra.adjoin ℤ {(zetaP2 p) ^ p} : Subalgebra ℤ ℂ) :=
    entry_not_mem_adjoin hp5 χdist hχs hz_ne
  -- `z` occurs as a `G₁` entry over the row `ρ` (keep the construction explicit)
  set ρ : CharPairClass (Model p 1) ℂˣ :=
    T.rows.symm (⟦⟨subA p d, χdist⟩⟧ : CharPairClass (Model p d) ℂˣ) with hρdef
  set H₁ : Subgroup (Model p 1) := T.sub' (subA p d) with hH₁def
  set h₁ : H₁ := T.el' (sElt p d) with hh₁def
  have hρ : species H₁ h₁ (classElt ρ) = z := by
    rw [hz_def, hρdef, ← classElt_mk (⟨subA p d, χdist⟩ : CharPair (Model p d) ℂˣ)]
    exact T.entry' (subA p d) (sElt p d) (⟦⟨subA p d, χdist⟩⟧)
  -- `|ρ.out.1| = p³` from the `⊥`-mark, transported through `T.symm`
  have hout1 : Nat.card (⟦⟨subA p d, χdist⟩⟧ : CharPairClass (Model p d) ℂˣ).out.1 = p ^ 3 := by
    obtain ⟨a, hmem, -⟩ :=
      Quotient.exact (Quotient.out_eq (⟦⟨subA p d, χdist⟩⟧ : CharPairClass (Model p d) ℂˣ))
    rw [← card_subA (p := p) (d := d)]
    refine Nat.card_congr
      { toFun := fun k => ⟨a * (k : Model p d) * a⁻¹, (hmem (k : Model p d)).mp k.2⟩
        invFun := fun k => ⟨a⁻¹ * (k : Model p d) * a, ?_⟩
        left_inv := fun k => Subtype.ext (by simp only; group)
        right_inv := fun k => Subtype.ext (by simp only; group) }
    have h := hmem (a⁻¹ * (k : Model p d) * a)
    rw [show a * (a⁻¹ * (k : Model p d) * a) * a⁻¹ = (k : Model p d) by group] at h
    exact h.mpr k.2
  have hmark : species (⊥ : Subgroup (Model p 1)) 1 (classElt ρ) = (p : ℂ) := by
    have htrans := T.symm.species_one_rows (⟦⟨subA p d, χdist⟩⟧) ⊥
    rw [T.symm.sub_bot] at htrans
    have hρ' : classElt (T.symm.rows (⟦⟨subA p d, χdist⟩⟧ : CharPairClass (Model p d) ℂˣ))
        = classElt ρ := rfl
    rw [hρ'] at htrans
    rw [htrans, species_one_classElt, card_fixedPoints_bot]
    have hq2 : Nat.card (Model p d ⧸
        (⟦⟨subA p d, χdist⟩⟧ : CharPairClass (Model p d) ℂˣ).out.1) = p := by
      have := Subgroup.card_eq_card_quotient_mul_card_subgroup
        (⟦⟨subA p d, χdist⟩⟧ : CharPairClass (Model p d) ℂˣ).out.1
      rw [card_model, hout1, show p ^ 4 = p * p ^ 3 by ring] at this
      exact Nat.eq_of_mul_eq_mul_right (pow_pos hp.pos 3) this.symm
    rw [hq2]
  have hcard : Nat.card ρ.out.1 = p ^ 3 := by
    rw [species_one_classElt, card_fixedPoints_bot] at hmark
    have hnat : Nat.card (Model p 1 ⧸ ρ.out.1) = p := by exact_mod_cast hmark
    have hq1 : Nat.card (Model p 1 ⧸ ρ.out.1) * Nat.card ρ.out.1 = p ^ 4 := by
      rw [← Subgroup.card_eq_card_quotient_mul_card_subgroup, card_model]
    rw [hnat, show p ^ 4 = p * p ^ 3 by ring] at hq1
    exact Nat.eq_of_mul_eq_mul_left hp.pos hq1
  -- a primitive character value on `ρ.out.1` (else `z ∈ ℤ[ζ_p]`)
  have hprim : ∃ g : ρ.out.1, ((ρ.out.2 g : ℂˣ) : ℂ) ^ p ≠ 1 := by
    by_contra hcon
    push Not at hcon
    apply hz_notmem
    rw [← hρ]
    change species H₁ h₁ (basisElt ρ.out.1 ρ.out.2) ∈ _
    rw [species_basisElt]
    exact Subalgebra.sum_mem _ fun q _ => mem_adjoin_of_pow_eq_one hp hζp (hcon _)
  obtain ⟨g, hg⟩ := hprim
  -- row = A
  have hrowA : ρ.out.1 = subA p 1 := eq_subA_of_char_primitive hp5 ρ.out.1 hcard ρ.out.2 g hg
  -- reduce to an A-block entry and refute (generalise the subgroup, then subst)
  suffices hfin : ∀ (K : Subgroup (Model p 1)) (χ₁ : K →* ℂˣ), K = subA p 1 →
      species H₁ h₁ (DRing.basisElt K χ₁) = z → False by
    exact hfin ρ.out.1 ρ.out.2 hrowA (by rw [← classElt]; exact hρ)
  intro K χ₁ hK hentA
  subst hK
  have hHle : H₁ ≤ subA p 1 := by
    by_contra hnotle
    exact hz_ne (by rw [← hentA]; exact species_A_row_eq_zero_of_not_le hnotle h₁ χ₁)
  exact A_block_entry_eq_z_impossible hp5 hd hd_qnr χ₁ ⟨(h₁ : Model p 1), hHle h₁.2⟩ χdist
    hχz hχb hχs ((species_le_normal_eq hHle h₁ χ₁).symm.trans (hentA.trans hz_def))

end LeanDring.P4
