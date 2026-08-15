/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.Theory.DRing.SplitDG
import LeanDring.Theory.DRing.BridgeRecognition
import Mathlib.RingTheory.IntegralDomain

-- The `[Fintype _]` binders below are unused in several *statements* but are
-- load-bearing in their *proofs* (instance synthesis for cardinality and basis
-- constructions), so they cannot be `omit`ted.  The linter's suggested rewrite
-- to `[Finite _]` + `Fintype.ofFinite` is a genuine refactor, not a cleanup.
set_option linter.unusedFintypeInType false

/-!
# Higman for the character subring: torsion elements of `ℤĜ` are `±[G,λ]`

The `b`-part of Müller's Satz 2.6.3. Main results (sorry-free):

* `charValue_norm_one` — character values have modulus `1`;
* `sum_char_mul_inv_char` — **orthogonality** of the multiplicative
  characters of a finite group (via `sum_hom_units_eq_zero`);
* `torsion_topSpan_eq_charElt` — **Higman's theorem for `ℤĜ ⊆ D(G)`**:
  a torsion element of the character span is `±[G,λ]` for a unique
  character. Proof: Parseval — the top-column species function
  `g ↦ φ_{⊤,g}(b)` is a ℤ-combination of characters with unit-modulus
  values, so the sum of squared coefficients is `1`.

Combined with `torsion_unit_factorization`, every torsion unit of `D(G)`
is `± charElt λ · (1 + a)` with `a` in the proper ideal
(`torsion_unit_eq_charElt_mul`).
-/

namespace LeanDring

open Finset

universe u

namespace DRing

open MonGSet MonRing

variable {G : Type u} [Group G] [Fintype G]

/-- Character values have modulus `1`. -/
theorem charValue_norm_one (l : G →* ℂˣ) (g : G) :
    ‖((l g : ℂˣ) : ℂ)‖ = 1 := by
  have hpow : ((l g : ℂˣ) : ℂ) ^ Fintype.card G = 1 := by
    have h1 : g ^ Fintype.card G = 1 := pow_card_eq_one
    calc ((l g : ℂˣ) : ℂ) ^ Fintype.card G
        = (((l g) ^ Fintype.card G : ℂˣ) : ℂ) := by
          rw [Units.val_pow_eq_pow_val]
      _ = ((l (g ^ Fintype.card G) : ℂˣ) : ℂ) := by rw [map_pow]
      _ = 1 := by rw [h1, map_one]; rfl
  exact Complex.norm_eq_one_of_pow_eq_one hpow Fintype.card_ne_zero

open Classical in
/-- **Orthogonality of multiplicative characters**. -/
theorem sum_char_mul_inv_char (l m : G →* ℂˣ) :
    (∑ g : G, (((l g * (m g)⁻¹ : ℂˣ)) : ℂ)) =
      if l = m then (Fintype.card G : ℂ) else 0 := by
  by_cases h : l = m
  · subst h
    rw [if_pos rfl]
    have hval : ∀ g : G, (((l g * (l g)⁻¹ : ℂˣ)) : ℂ) = 1 := by
      intro g
      rw [mul_inv_cancel]
      rfl
    rw [Finset.sum_congr rfl fun g _ => hval g, Finset.sum_const,
      nsmul_eq_mul, mul_one, Finset.card_univ]
  · rw [if_neg h]
    have hne : (Units.coeHom ℂ).comp (l * m⁻¹) ≠ 1 := by
      intro hcon
      apply h
      refine MonoidHom.ext fun g => ?_
      have h1 := DFunLike.congr_fun hcon g
      have h2 : (((l * m⁻¹) g : ℂˣ) : ℂ) = 1 := h1
      have h3 : ((l * m⁻¹) g : ℂˣ) = 1 := Units.ext h2
      have h4 : l g * (m g)⁻¹ = 1 := h3
      have h5 : l g = m g := by
        have := congrArg (fun z => z * m g) h4
        simpa [mul_assoc] using this
      exact h5
    have h0 := sum_hom_units_eq_zero ((Units.coeHom ℂ).comp (l * m⁻¹)) hne
    calc (∑ g : G, (((l g * (m g)⁻¹ : ℂˣ)) : ℂ))
        = ∑ g : G, ((Units.coeHom ℂ).comp (l * m⁻¹)) g :=
          Finset.sum_congr rfl fun g _ => rfl
      _ = 0 := h0

/-- **Higman for the character subring**: a torsion element of
`ℤĜ ⊆ D(G)` is `± charElt λ`. -/
theorem torsion_topSpan_eq_charElt {b : DRing G} (hb : b ∈ topSpan G)
    {n : ℕ} (hn : 0 < n) (hbn : b ^ n = 1) :
    ∃ l : G →* ℂˣ, b = charElt l ∨ b = -charElt l := by
  classical
  obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hb
  -- the top-column species function is the character combination
  have hFval : ∀ g : G, species ⊤ (topHom G g) b =
      ∑ l ∈ c.support, ((c l : ℤ) : ℂ) * ((l g : ℂˣ) : ℂ) := by
    intro g
    rw [← hc]
    rw [Finsupp.sum]
    rw [map_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_zsmul, species_charElt, zsmul_eq_mul]
    rfl
  -- unit modulus
  have hFnorm : ∀ g : G, ‖species ⊤ (topHom G g) b‖ = 1 := by
    intro g
    have hpow : (species ⊤ (topHom G g) b) ^ n = 1 := by
      rw [← map_pow, hbn, map_one]
    exact Complex.norm_eq_one_of_pow_eq_one hpow hn.ne'
  -- conjugation inverts unit-modulus values
  have hconjinv : ∀ (z : ℂ), ‖z‖ = 1 → (starRingEnd ℂ) z = z⁻¹ := by
    intro z hz
    have h1 : z * (starRingEnd ℂ) z = 1 := by
      rw [Complex.mul_conj]
      norm_cast
      rw [Complex.normSq_eq_norm_sq, hz]
      norm_num
    exact eq_inv_of_mul_eq_one_right h1
  have hFconj : ∀ g : G, (starRingEnd ℂ) (species ⊤ (topHom G g) b) =
      ∑ m ∈ c.support, ((c m : ℤ) : ℂ) * (((m g)⁻¹ : ℂˣ) : ℂ) := by
    intro g
    rw [hFval, map_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [map_mul]
    congr 1
    · exact map_intCast (starRingEnd ℂ) _
    · rw [hconjinv _ (charValue_norm_one m g)]
      exact (Units.val_inv_eq_inv_val (m g)).symm
  -- Parseval: sum of |F g|² over the group
  have hLHS : (∑ g : G, species ⊤ (topHom G g) b *
      (starRingEnd ℂ) (species ⊤ (topHom G g) b)) =
      (Fintype.card G : ℂ) := by
    have hval : ∀ g : G, species ⊤ (topHom G g) b *
        (starRingEnd ℂ) (species ⊤ (topHom G g) b) = 1 := by
      intro g
      rw [Complex.mul_conj]
      norm_cast
      rw [Complex.normSq_eq_norm_sq, hFnorm]
      norm_num
    rw [Finset.sum_congr rfl fun g _ => hval g, Finset.sum_const,
      nsmul_eq_mul, mul_one, Finset.card_univ]
  have hRHS : (∑ g : G, species ⊤ (topHom G g) b *
      (starRingEnd ℂ) (species ⊤ (topHom G g) b)) =
      ∑ l ∈ c.support, ∑ m ∈ c.support,
        ((c l : ℤ) : ℂ) * ((c m : ℤ) : ℂ) *
          (∑ g : G, (((l g * (m g)⁻¹ : ℂˣ)) : ℂ)) := by
    have hstep : ∀ g : G, species ⊤ (topHom G g) b *
        (starRingEnd ℂ) (species ⊤ (topHom G g) b) =
        ∑ l ∈ c.support, ∑ m ∈ c.support,
          ((c l : ℤ) : ℂ) * ((c m : ℤ) : ℂ) *
            (((l g * (m g)⁻¹ : ℂˣ)) : ℂ) := by
      intro g
      rw [hFconj g, hFval g, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      refine Finset.sum_congr rfl fun m _ => ?_
      have hu : (((l g * (m g)⁻¹ : ℂˣ)) : ℂ) =
          ((l g : ℂˣ) : ℂ) * (((m g)⁻¹ : ℂˣ) : ℂ) := rfl
      rw [hu]
      ring
    rw [Finset.sum_congr rfl fun g _ => hstep g]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [← Finset.mul_sum]
  -- collapse the double sum by orthogonality
  have hdouble : (∑ l ∈ c.support, ∑ m ∈ c.support,
      ((c l : ℤ) : ℂ) * ((c m : ℤ) : ℂ) *
        (∑ g : G, (((l g * (m g)⁻¹ : ℂˣ)) : ℂ))) =
      (∑ l ∈ c.support, ((c l : ℤ) : ℂ) ^ 2) * (Fintype.card G : ℂ) := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun l hl => ?_
    have hinner : ∀ m ∈ c.support,
        ((c l : ℤ) : ℂ) * ((c m : ℤ) : ℂ) *
          (∑ g : G, (((l g * (m g)⁻¹ : ℂˣ)) : ℂ)) =
        if l = m then ((c l : ℤ) : ℂ) * ((c m : ℤ) : ℂ) *
          (Fintype.card G : ℂ) else 0 := by
      intro m _
      rw [sum_char_mul_inv_char]
      by_cases h : l = m
      · rw [if_pos h, if_pos h]
      · rw [if_neg h, if_neg h, mul_zero]
    rw [Finset.sum_congr rfl hinner,
      Finset.sum_ite_eq c.support l
        (fun m => ((c l : ℤ) : ℂ) * ((c m : ℤ) : ℂ) *
          (Fintype.card G : ℂ)),
      if_pos hl]
    ring
  -- sum of squared coefficients is 1
  have hsq : (∑ l ∈ c.support, ((c l : ℤ) : ℂ) ^ 2) = 1 := by
    have h1 : (∑ l ∈ c.support, ((c l : ℤ) : ℂ) ^ 2) *
        (Fintype.card G : ℂ) = 1 * (Fintype.card G : ℂ) := by
      rw [one_mul, ← hdouble, ← hRHS, hLHS]
    have hcard : (Fintype.card G : ℂ) ≠ 0 := by
      exact_mod_cast Fintype.card_ne_zero
    exact mul_right_cancel₀ hcard h1
  have hsqZ : (∑ l ∈ c.support, (c l) ^ 2) = 1 := by
    have hcast : ((∑ l ∈ c.support, (c l) ^ 2 : ℤ) : ℂ) = 1 := by
      push_cast
      exact hsq
    exact_mod_cast hcast
  -- the support is a single character with coefficient ±1
  have hposs : ∀ l ∈ c.support, 1 ≤ (c l) ^ 2 := by
    intro l hl
    have hne : c l ≠ 0 := Finsupp.mem_support_iff.mp hl
    rcases lt_or_gt_of_ne hne with h | h
    · nlinarith
    · nlinarith
  have hcardle : (c.support.card : ℤ) ≤ ∑ l ∈ c.support, (c l) ^ 2 := by
    calc (c.support.card : ℤ) = ∑ _l ∈ c.support, (1 : ℤ) := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_one]
      _ ≤ _ := Finset.sum_le_sum hposs
  have hnonempty : c.support.Nonempty := by
    by_contra hcon
    rw [Finset.not_nonempty_iff_eq_empty] at hcon
    rw [hcon, Finset.sum_empty] at hsqZ
    norm_num at hsqZ
  have hcard1 : c.support.card = 1 := by
    have h1 : 1 ≤ c.support.card := Finset.card_pos.mpr hnonempty
    have h2 : (c.support.card : ℤ) ≤ 1 := by
      rw [hsqZ] at hcardle
      exact hcardle
    omega
  obtain ⟨l₀, hl₀⟩ := Finset.card_eq_one.mp hcard1
  have hcl₀ : (c l₀) ^ 2 = 1 := by
    rw [hl₀, Finset.sum_singleton] at hsqZ
    exact hsqZ
  have hpm : c l₀ = 1 ∨ c l₀ = -1 := by
    have h1 : c l₀ * c l₀ = 1 := by
      rw [← pow_two]
      exact hcl₀
    rcases Int.mul_eq_one_iff_eq_one_or_neg_one.mp h1 with ⟨h2, -⟩ | ⟨h2, -⟩
    · exact Or.inl h2
    · exact Or.inr h2
  have hb' : b = c l₀ • charElt l₀ := by
    rw [← hc, Finsupp.sum, hl₀, Finset.sum_singleton]
  rcases hpm with h | h
  · exact ⟨l₀, Or.inl (by rw [hb', h, one_smul])⟩
  · refine ⟨l₀, Or.inr ?_⟩
    rw [hb', h]
    exact neg_one_zsmul _

/-- **Satz 2.6.3, modulo the unipotent part**: every torsion unit of
`D(G)` is `± charElt λ · (1 + a)` with `a` in the proper ideal and
`1 + a` torsion. -/
theorem torsion_unit_eq_charElt_mul {u : DRing G} {n : ℕ} (hn : 0 < n)
    (hu : u ^ n = 1) :
    ∃ (l : G →* ℂˣ) (a : DRing G), a ∈ smallSpan G ∧ (1 + a) ^ n = 1 ∧
      (u = charElt l * (1 + a) ∨ u = -(charElt l * (1 + a))) := by
  obtain ⟨b, a, hbmem, hamem, hbn, han, hfact⟩ :=
    torsion_unit_factorization hn hu
  obtain ⟨l, hl⟩ := torsion_topSpan_eq_charElt hbmem hn hbn
  rcases hl with h | h
  · exact ⟨l, a, hamem, han, Or.inl (by rw [hfact, h])⟩
  · refine ⟨l, a, hamem, han, Or.inr ?_⟩
    rw [hfact, h]
    ring

end DRing

end LeanDring
