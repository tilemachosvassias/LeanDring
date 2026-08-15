/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.Theory.DRing.CharTorsion
import Mathlib.GroupTheory.Nilpotent
import Mathlib.GroupTheory.Sylow

-- The `[Fintype _]` binders below are unused in several *statements* but are
-- load-bearing in their *proofs* (instance synthesis for cardinality and basis
-- constructions), so they cannot be `omit`ted.  The linter's suggested rewrite
-- to `[Finite _]` + `Fintype.ofFinite` is a genuine refactor, not a cleanup.
set_option linter.unusedFintypeInType false

/-!
# The unipotent step of Satz 2.6.3

`(1 + a)ⁿ = 1` with `a` in the proper ideal forces `a = 0`
(under the normalizer-growth hypothesis `|N(K)/K| ≥ 3` for proper `K`,
satisfied by `p`-groups for odd `p`) — and, on top of it, Satz 2.6.3
itself.

The two reusable engines:

* `sum_sq_eq_one_of_norm_one` — **generalized Parseval**: a ℤ-linear
  combination of multiplicative characters of a finite group whose
  values all have modulus `1` has squared-coefficient sum `1`;
* `species_basisElt_eq_zero_of_card_lt` — **layer vanishing**: the
  `(H,h)`-entry of `[K,λ]` vanishes when `|K| < |H|`.

The results built on them:

* `eq_zero_of_one_add_pow_eq_one` — **the unipotent step**, under the
  normalizer-growth hypothesis stated as `3 ≤ #(G/K)^K` for proper `K`;
* `mass_ge_three_of_pgroup` — that hypothesis holds for `p`-groups with
  `p ≥ 3`;
* `torsion_unit_eq_pm_charElt` / `torsion_unit_eq_pm_charElt_of_pgroup` —
  **Satz 2.6.3**: every torsion unit of `D(G)` is `± charElt λ`.
-/

namespace LeanDring

open Finset

universe u

namespace DRing

open MonGSet MonRing

/-- **Generalized Parseval**: if `F = ∑_ξ N_ξ · ξ` (a finite ℤ-linear
combination of multiplicative characters of a finite group `H`) has
`‖F h‖ = 1` for every `h`, then `∑_ξ N_ξ² = 1`. -/
theorem sum_sq_eq_one_of_norm_one {H : Type u} [Group H] [Fintype H]
    (N : (H →* ℂˣ) →₀ ℤ)
    (hnorm : ∀ x : H,
      ‖∑ ξ ∈ N.support, ((N ξ : ℤ) : ℂ) * ((ξ x : ℂˣ) : ℂ)‖ = 1) :
    (∑ ξ ∈ N.support, (N ξ) ^ 2) = 1 := by
  classical
  set F : H → ℂ := fun x =>
    ∑ ξ ∈ N.support, ((N ξ : ℤ) : ℂ) * ((ξ x : ℂˣ) : ℂ) with hF
  have hconjinv : ∀ (z : ℂ), ‖z‖ = 1 → (starRingEnd ℂ) z = z⁻¹ := by
    intro z hz
    have h1 : z * (starRingEnd ℂ) z = 1 := by
      rw [Complex.mul_conj]
      norm_cast
      rw [Complex.normSq_eq_norm_sq, hz]
      norm_num
    exact eq_inv_of_mul_eq_one_right h1
  have hFconj : ∀ x : H, (starRingEnd ℂ) (F x) =
      ∑ ξ ∈ N.support, ((N ξ : ℤ) : ℂ) * (((ξ x)⁻¹ : ℂˣ) : ℂ) := by
    intro x
    rw [hF]
    rw [map_sum]
    refine Finset.sum_congr rfl fun ξ _ => ?_
    rw [map_mul]
    congr 1
    · exact map_intCast (starRingEnd ℂ) _
    · rw [hconjinv _ (charValue_norm_one ξ x)]
      exact (Units.val_inv_eq_inv_val (ξ x)).symm
  have hLHS : (∑ x : H, F x * (starRingEnd ℂ) (F x)) =
      (Fintype.card H : ℂ) := by
    have hval : ∀ x : H, F x * (starRingEnd ℂ) (F x) = 1 := by
      intro x
      rw [Complex.mul_conj]
      norm_cast
      rw [Complex.normSq_eq_norm_sq, hnorm]
      norm_num
    rw [Finset.sum_congr rfl fun x _ => hval x, Finset.sum_const,
      nsmul_eq_mul, mul_one, Finset.card_univ]
  have hRHS : (∑ x : H, F x * (starRingEnd ℂ) (F x)) =
      ∑ ξ ∈ N.support, ∑ μ ∈ N.support,
        ((N ξ : ℤ) : ℂ) * ((N μ : ℤ) : ℂ) *
          (∑ x : H, (((ξ x * (μ x)⁻¹ : ℂˣ)) : ℂ)) := by
    have hstep : ∀ x : H, F x * (starRingEnd ℂ) (F x) =
        ∑ ξ ∈ N.support, ∑ μ ∈ N.support,
          ((N ξ : ℤ) : ℂ) * ((N μ : ℤ) : ℂ) *
            (((ξ x * (μ x)⁻¹ : ℂˣ)) : ℂ) := by
      intro x
      rw [hFconj x, hF, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun ξ _ => ?_
      refine Finset.sum_congr rfl fun μ _ => ?_
      have hu : (((ξ x * (μ x)⁻¹ : ℂˣ)) : ℂ) =
          ((ξ x : ℂˣ) : ℂ) * (((μ x)⁻¹ : ℂˣ) : ℂ) := rfl
      rw [hu]
      ring
    rw [Finset.sum_congr rfl fun x _ => hstep x]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun ξ _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [← Finset.mul_sum]
  have hdouble : (∑ ξ ∈ N.support, ∑ μ ∈ N.support,
      ((N ξ : ℤ) : ℂ) * ((N μ : ℤ) : ℂ) *
        (∑ x : H, (((ξ x * (μ x)⁻¹ : ℂˣ)) : ℂ))) =
      (∑ ξ ∈ N.support, ((N ξ : ℤ) : ℂ) ^ 2) * (Fintype.card H : ℂ) := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun ξ hξ => ?_
    have hinner : ∀ μ ∈ N.support,
        ((N ξ : ℤ) : ℂ) * ((N μ : ℤ) : ℂ) *
          (∑ x : H, (((ξ x * (μ x)⁻¹ : ℂˣ)) : ℂ)) =
        if ξ = μ then ((N ξ : ℤ) : ℂ) * ((N μ : ℤ) : ℂ) *
          (Fintype.card H : ℂ) else 0 := by
      intro μ _
      rw [sum_char_mul_inv_char]
      by_cases h : ξ = μ
      · rw [if_pos h, if_pos h]
      · rw [if_neg h, if_neg h, mul_zero]
    rw [Finset.sum_congr rfl hinner,
      Finset.sum_ite_eq N.support ξ
        (fun μ => ((N ξ : ℤ) : ℂ) * ((N μ : ℤ) : ℂ) *
          (Fintype.card H : ℂ)),
      if_pos hξ]
    ring
  have hsq : (∑ ξ ∈ N.support, ((N ξ : ℤ) : ℂ) ^ 2) = 1 := by
    have h1 : (∑ ξ ∈ N.support, ((N ξ : ℤ) : ℂ) ^ 2) *
        (Fintype.card H : ℂ) = 1 * (Fintype.card H : ℂ) := by
      rw [one_mul, ← hdouble, ← hRHS, hLHS]
    have hcard : (Fintype.card H : ℂ) ≠ 0 := by
      exact_mod_cast Fintype.card_ne_zero
    exact mul_right_cancel₀ hcard h1
  have hcast : ((∑ ξ ∈ N.support, (N ξ) ^ 2 : ℤ) : ℂ) = 1 := by
    push_cast
    exact hsq
  exact_mod_cast hcast

variable {G : Type u} [Group G] [Fintype G]

/-- **Layer vanishing**: the `(H,h)`-entry of `[K,λ]` is zero when
`|K| < |H|` (no `H`-fixed cosets in `G/K`). -/
theorem species_basisElt_eq_zero_of_card_lt {H K : Subgroup G}
    (hlt : Nat.card K < Nat.card H) (h : H) (l : K →* ℂˣ) :
    species H h (basisElt K l) = 0 := by
  classical
  rw [species_basisElt]
  haveI : IsEmpty (MulAction.fixedPoints H
      (induced K l : MonGSet G ℂˣ).carrier) := by
    constructor
    rintro ⟨q, hq⟩
    -- an `H`-fixed coset gives `H` subconjugate to `K`
    have hne : Nat.card (MulAction.fixedPoints H (G ⧸ K)) ≠ 0 := by
      refine Nat.card_ne_zero.mpr ⟨⟨⟨q, hq⟩⟩, ?_⟩
      exact Subtype.finite
    obtain ⟨g, hg⟩ := (mark_ne_zero_iff H K).mp hne
    have hle : Nat.card H ≤ Nat.card K := card_le_of_subconj hg
    omega
  rw [Finset.univ_eq_empty, Finset.sum_empty]

open MulAction in
/-- The character of `K₀` induced at a `K₀`-fixed coset of `G/K`:
`h ↦ λ(s(q)⁻¹ h s(q))`. -/
noncomputable def conjChar (K₀ K : Subgroup G) (l : K →* ℂˣ)
    (q : G ⧸ K) (hq : ∀ h : K₀, (h : G) • q = q) : K₀ →* ℂˣ where
  toFun h := l ⟨q.out⁻¹ * (h : G) * q.out,
    MonGSet.sectionConj_mem K K₀ h q (hq h)⟩
  map_one' := by
    have harg : (⟨q.out⁻¹ * ((1 : K₀) : G) * q.out,
        MonGSet.sectionConj_mem K K₀ 1 q (hq 1)⟩ : K) = 1 := by
      refine Subtype.ext ?_
      change q.out⁻¹ * ((1 : K₀) : G) * q.out = 1
      have h1 : ((1 : K₀) : G) = 1 := rfl
      rw [h1]
      group
    rw [harg, map_one]
  map_mul' := by
    intro h₁ h₂
    have harg : (⟨q.out⁻¹ * ((h₁ * h₂ : K₀) : G) * q.out,
        MonGSet.sectionConj_mem K K₀ (h₁ * h₂) q (hq (h₁ * h₂))⟩ : K) =
        ⟨q.out⁻¹ * (h₁ : G) * q.out,
          MonGSet.sectionConj_mem K K₀ h₁ q (hq h₁)⟩ *
        ⟨q.out⁻¹ * (h₂ : G) * q.out,
          MonGSet.sectionConj_mem K K₀ h₂ q (hq h₂)⟩ := by
      refine Subtype.ext ?_
      change q.out⁻¹ * ((h₁ : G) * (h₂ : G)) * q.out =
        (q.out⁻¹ * (h₁ : G) * q.out) * (q.out⁻¹ * (h₂ : G) * q.out)
      group
    rw [harg, map_mul]

open MulAction in
/-- The `(K₀,h)`-entry of `[K,λ]`, regrouped as a sum of induced
characters over the fixed cosets. -/
theorem species_basisElt_eq_sum_conjChar (K₀ K : Subgroup G)
    (l : K →* ℂˣ) (h : K₀) :
    species K₀ h (basisElt K l) =
      ∑ q : fixedPoints K₀ (induced K l : MonGSet G ℂˣ).carrier,
        ((conjChar K₀ K l q.1 q.2) h : ℂ) := by
  rw [species_basisElt]
  rfl

/-! ## The mass source

The diagonal top class `[K,1]` has a species that is **constant in `h`**,
equal to the number of `K`-fixed cosets `#(G/K)^K = |N_G(K) : K|`. Under
the normalizer-growth hypothesis (`|N(K)/K| ≥ 3`, satisfied by `p`-groups
for odd `p`) this mass is at least `3`, which is what forces the
case-analysis endgame. -/

open MulAction in
/-- The trivial-character basis element has species equal to the mark:
`φ_{H,h}[K,1] = #(G/K)^H`. -/
theorem species_basisElt_one (K H : Subgroup G) (h : H) :
    species H h (basisElt K (1 : K →* ℂˣ)) =
      (Fintype.card (fixedPoints H
        (induced K (1 : K →* ℂˣ) : MonGSet G ℂˣ).carrier) : ℂ) := by
  rw [species_basisElt]
  simp only [MonoidHom.one_apply, Units.val_one]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]

open MulAction in
/-- At the identity, the species of **any** basis element is the mark:
`φ_{H,1}[K,λ] = #(G/K)^H` (the conjugated argument collapses to `1`). -/
theorem species_basisElt_one_eq_card (K H : Subgroup G) (l : K →* ℂˣ) :
    species H (1 : H) (basisElt K l) =
      (Fintype.card (fixedPoints H
        (induced K l : MonGSet G ℂˣ).carrier) : ℂ) := by
  rw [species_basisElt]
  have hone : ∀ q : fixedPoints H (induced K l : MonGSet G ℂˣ).carrier,
      ((l ⟨q.1.out⁻¹ * ((1 : H) : G) * q.1.out,
        sectionConj_mem K H 1 q.1 (q.2 1)⟩ : ℂˣ) : ℂ) = 1 := by
    intro q
    have harg : (⟨q.1.out⁻¹ * ((1 : H) : G) * q.1.out,
        sectionConj_mem K H 1 q.1 (q.2 1)⟩ : K) = 1 := by
      refine Subtype.ext ?_
      change q.1.out⁻¹ * ((1 : H) : G) * q.1.out = 1
      have h1 : ((1 : H) : G) = 1 := rfl
      rw [h1]; group
    rw [harg, map_one]; rfl
  rw [Finset.sum_congr rfl fun q _ => hone q, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, mul_one]

open MulAction in
/-- The diagonal species of the trivial-character top class is the mark:
`φ_{K,h}[K,1] = #(G/K)^K`, independent of `h`. -/
theorem species_basisElt_self_one (K : Subgroup G) (h : K) :
    species K h (basisElt K (1 : K →* ℂˣ)) =
      (Fintype.card (fixedPoints K
        (induced K (1 : K →* ℂˣ) : MonGSet G ℂˣ).carrier) : ℂ) :=
  species_basisElt_one K K h

open MulAction in
/-- **The mass source**: the `K`-fixed cosets of `G/K` are `N_G(K)/K`, so
`#(G/K)^K = |N_G(K) : K|` — the mass the normalizer-growth hypothesis
(`≥ 3` for `p`-groups, odd `p`) lower-bounds. -/
theorem card_fixedPoints_self_normalizer (K : Subgroup G) :
    Nat.card (fixedPoints K (G ⧸ K)) =
      Nat.card (Subgroup.normalizer K ⧸
        K.comap (Subgroup.normalizer K).subtype) :=
  Nat.card_congr (Sylow.fixedPointsMulLeftCosetsEquivQuotient K)

/-! ## The disjointness core: `conjChar` recovers its class -/

open MulAction in
/-- At a `K₀`-fixed coset `q` of `G/K` with `|K₀| = |K|`, `conjChar` is a
genuine conjugate character: `(K₀, conjChar q) ∼ (K, λ)`. -/
theorem conjChar_isConjPair (K₀ K : Subgroup G) (l : K →* ℂˣ) (q : G ⧸ K)
    (hq : ∀ h : K₀, (h : G) • q = q) (hcard : Nat.card K₀ = Nat.card K) :
    IsConjPair K₀ K (conjChar K₀ K l q hq) l := by
  have hsub : ∀ x ∈ K₀, q.out⁻¹ * x * q.out ∈ K := fun x hx =>
    sectionConj_mem K K₀ ⟨x, hx⟩ q (hq ⟨x, hx⟩)
  have hmapeq : K₀.map (MulAut.conj q.out⁻¹).toMonoidHom = K :=
    map_conj_eq_of_subconj_card (g := q.out) hsub hcard
  refine ⟨q.out⁻¹, fun k => ⟨fun hk => by rw [inv_inv]; exact hsub k hk,
    fun hk => ?_⟩,
    fun k hk => by
      refine congrArg l (Subtype.ext ?_)
      change q.out⁻¹ * k * q.out⁻¹⁻¹ = q.out⁻¹ * (k : G) * q.out
      rw [inv_inv]⟩
  have hkK : q.out⁻¹ * k * q.out ∈ K := by rwa [inv_inv] at hk
  have hmap : q.out⁻¹ * k * q.out ∈
      K₀.map (MulAut.conj q.out⁻¹).toMonoidHom :=
    (SetLike.ext_iff.mp hmapeq (q.out⁻¹ * k * q.out)).mpr hkK
  obtain ⟨y, hy, hyeq⟩ := Subgroup.mem_map.mp hmap
  have hconj : q.out⁻¹ * y * q.out = q.out⁻¹ * k * q.out := by
    have hval : q.out⁻¹ * y * q.out⁻¹⁻¹ = q.out⁻¹ * k * q.out := hyeq
    rwa [inv_inv] at hval
  have hyk : y = k := mul_left_cancel (mul_right_cancel hconj)
  rw [← hyk]; exact hy

/-- **Class recovery**: `conjChar` at a fixed coset represents the same
conjugacy class as `(K, λ)`. -/
theorem classElt_conjChar_eq (K₀ K : Subgroup G) (l : K →* ℂˣ) (q : G ⧸ K)
    (hq : ∀ h : K₀, (h : G) • q = q) (hcard : Nat.card K₀ = Nat.card K) :
    (⟦(⟨K₀, conjChar K₀ K l q hq⟩ : CharPair G ℂˣ)⟧ : CharPairClass G ℂˣ) =
      ⟦(⟨K, l⟩ : CharPair G ℂˣ)⟧ :=
  Quotient.sound (conjChar_isConjPair K₀ K l q hq hcard)

/-- **Trivial-character routing**: `conjChar` is trivial exactly when the
underlying character is — so only the diagonal class `[K₀,1]` feeds the
trivial-character coefficient. -/
theorem conjChar_eq_one_iff (K₀ K : Subgroup G) (l : K →* ℂˣ) (q : G ⧸ K)
    (hq : ∀ h : K₀, (h : G) • q = q) (hcard : Nat.card K₀ = Nat.card K) :
    conjChar K₀ K l q hq = 1 ↔ l = 1 := by
  have hmapeq : K₀.map (MulAut.conj q.out⁻¹).toMonoidHom = K :=
    map_conj_eq_of_subconj_card (g := q.out)
      (fun x hx => sectionConj_mem K K₀ ⟨x, hx⟩ q (hq ⟨x, hx⟩)) hcard
  constructor
  · intro h
    refine MonoidHom.ext fun k => ?_
    obtain ⟨k, hk⟩ := k
    have hmap : k ∈ K₀.map (MulAut.conj q.out⁻¹).toMonoidHom :=
      (SetLike.ext_iff.mp hmapeq k).mpr hk
    obtain ⟨y, hy, hyeq⟩ := Subgroup.mem_map.mp hmap
    have hval : q.out⁻¹ * y * q.out = k := by
      have h1 : q.out⁻¹ * y * q.out⁻¹⁻¹ = k := hyeq
      rwa [inv_inv] at h1
    have := congrFun (congrArg DFunLike.coe h) ⟨y, hy⟩
    change (conjChar K₀ K l q hq ⟨y, hy⟩ : ℂˣ) = (1 : ℂˣ) at this
    rw [show (l ⟨k, hk⟩ : ℂˣ) = conjChar K₀ K l q hq ⟨y, hy⟩ from
      congrArg l (Subtype.ext hval.symm), this]
    rfl
  · intro h
    subst h
    refine MonoidHom.ext fun k => ?_
    rfl

/-! ## Class-level wrappers -/

open MulAction in
/-- Layer vanishing at the class level. -/
theorem species_classElt_eq_zero_of_card_lt (H : Subgroup G) (h : H)
    (c : CharPairClass G ℂˣ) (hlt : Nat.card c.out.1 < Nat.card H) :
    species H h (classElt c) = 0 :=
  species_basisElt_eq_zero_of_card_lt hlt h c.out.2

open MulAction in
/-- Class-level `conjChar` regrouping. -/
theorem species_classElt_eq_sum_conjChar (K₀ : Subgroup G) (h : K₀)
    (c : CharPairClass G ℂˣ) :
    species K₀ h (classElt c) =
      ∑ q : fixedPoints K₀ (induced c.out.1 c.out.2 : MonGSet G ℂˣ).carrier,
        ((conjChar K₀ c.out.1 c.out.2 q.1 q.2) h : ℂ) :=
  species_basisElt_eq_sum_conjChar K₀ c.out.1 c.out.2 h

/-! ## The unipotent step -/

/-- Integer arithmetic behind the mass bound: with `m ≥ 3` and `x ≠ 0`,
`(1 + m·x)²` cannot be `≤ 1`. -/
private theorem sq_one_add_mul_contra {m x : ℤ} (hm : 3 ≤ m) (hx : x ≠ 0)
    (h : (1 + m * x) ^ 2 ≤ 1) : False := by
  rcases lt_or_gt_of_ne hx with hneg | hpos
  · have hx1 : x ≤ -1 := by omega
    nlinarith [h, hm, hx1, sq_nonneg (m * x + 3),
      mul_nonneg (by linarith : (0 : ℤ) ≤ m - 3) (by linarith : (0 : ℤ) ≤ -1 - x)]
  · have hx1 : 1 ≤ x := by omega
    nlinarith [h, hm, hx1, sq_nonneg (m * x - 3),
      mul_nonneg (by linarith : (0 : ℤ) ≤ m - 3) (by linarith : (0 : ℤ) ≤ x - 1)]

open MulAction in
/-- **The unipotent step of Satz 2.6.3**: `(1 + a)ⁿ = 1` with `a` in the
proper ideal forces `a = 0`, under the normalizer-growth hypothesis
`3 ≤ #(G/K)^K` for every proper `K` (satisfied by `p`-groups, odd `p`). -/
theorem eq_zero_of_one_add_pow_eq_one
    (hmass : ∀ K : Subgroup G, Nat.card K < Nat.card G →
      3 ≤ Nat.card (fixedPoints K (G ⧸ K)))
    {a : DRing G} (ha : a ∈ smallSpan G) {n : ℕ} (hn : 0 < n)
    (hpow : (1 + a) ^ n = 1) : a = 0 := by
  classical
  by_contra hane
  set r := basisOfCharPairClass.repr a with hr
  have hbcoe : ⇑(basisOfCharPairClass (G := G)) = classElt :=
    Module.Basis.coe_mk _ _
  -- support of `a` consists of proper (small) classes
  have hspanmem : a ∈ Submodule.span ℤ
      (⇑(basisOfCharPairClass (G := G)) '' {c | SmallClass G c}) := by
    rw [hbcoe]; exact smallSpan_le ha
  have hsmall : ↑r.support ⊆ {c : CharPairClass G ℂˣ | SmallClass G c} :=
    (Module.Basis.mem_span_image (b := basisOfCharPairClass)).mp hspanmem
  -- the support is nonempty (`a ≠ 0`)
  have hrne : r.support.Nonempty := by
    rw [Finsupp.support_nonempty_iff, hr, ne_eq, LinearEquiv.map_eq_zero_iff]
    exact hane
  -- pick a maximal-order support class
  obtain ⟨cS, hcSmem, hcSmax⟩ :=
    r.support.exists_max_image (fun c => Nat.card c.out.1) hrne
  set K₀ := cS.out.1 with hK₀
  set M := Nat.card K₀ with hMdef
  have hK₀prop : Nat.card K₀ < Nat.card G := hsmall hcSmem
  have hmass3 : 3 ≤ Nat.card (fixedPoints K₀ (G ⧸ K₀)) := hmass K₀ hK₀prop
  -- `a` in the class basis
  have ha_sum : a = r.sum (fun c z => z • classElt c) := by
    have h1 := basisOfCharPairClass.linearCombination_repr a
    rw [Finsupp.linearCombination_apply] at h1
    rw [← h1]; simp only [hbcoe, ← hr]
  set topSupp := r.support.filter (fun c => Nat.card c.out.1 = M) with hTS
  -- species of `a` at `(K₀, h)`: only the maximal layer survives
  have hspec_a : ∀ h : K₀, species K₀ h a =
      ∑ c ∈ topSupp, ∑ q : fixedPoints K₀
        (induced c.out.1 c.out.2 : MonGSet G ℂˣ).carrier,
        ((r c : ℤ) : ℂ) *
          ((conjChar K₀ c.out.1 c.out.2 q.1 q.2 h : ℂˣ) : ℂ) := by
    intro h
    have hexp : species K₀ h a =
        ∑ c ∈ r.support, ((r c : ℤ) : ℂ) * species K₀ h (classElt c) := by
      rw [ha_sum, Finsupp.sum, map_sum]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [map_zsmul, zsmul_eq_mul]
    rw [hexp, ← Finset.sum_filter_add_sum_filter_not r.support
      (fun c => Nat.card c.out.1 = M)]
    have hother : ∑ c ∈ r.support.filter (fun c => ¬ Nat.card c.out.1 = M),
        ((r c : ℤ) : ℂ) * species K₀ h (classElt c) = 0 := by
      refine Finset.sum_eq_zero fun c hc => ?_
      rw [Finset.mem_filter] at hc
      have hlt : Nat.card c.out.1 < M :=
        lt_of_le_of_ne (hcSmax c hc.1) hc.2
      rw [species_classElt_eq_zero_of_card_lt K₀ h c hlt, mul_zero]
    rw [hother, add_zero, ← hTS]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [species_classElt_eq_sum_conjChar K₀ h c, Finset.mul_sum]
  -- the character finsupp `N`
  set N : (K₀ →* ℂˣ) →₀ ℤ :=
    Finsupp.single (1 : K₀ →* ℂˣ) 1 +
      ∑ c ∈ topSupp, ∑ q : fixedPoints K₀
        (induced c.out.1 c.out.2 : MonGSet G ℂˣ).carrier,
        Finsupp.single (conjChar K₀ c.out.1 c.out.2 q.1 q.2) (r c) with hNdef
  -- evaluation homomorphism at `h`
  set ev : K₀ → ((K₀ →* ℂˣ) →₀ ℤ) →+ ℂ := fun h =>
    Finsupp.liftAddHom fun ξ =>
      (AddMonoidHom.mulRight ((ξ h : ℂˣ) : ℂ)).comp (Int.castAddHom ℂ)
    with hevdef
  have hev_single : ∀ (h : K₀) (ξ : K₀ →* ℂˣ) (z : ℤ),
      ev h (Finsupp.single ξ z) = ((z : ℤ) : ℂ) * ((ξ h : ℂˣ) : ℂ) := by
    intro h ξ z
    rw [hevdef]
    simp only [Finsupp.liftAddHom_apply_single, AddMonoidHom.coe_comp,
      Function.comp_apply, AddMonoidHom.coe_mulRight, Int.coe_castAddHom]
  have hevsum : ∀ (h : K₀) (N' : (K₀ →* ℂˣ) →₀ ℤ),
      ev h N' = ∑ ξ ∈ N'.support, ((N' ξ : ℤ) : ℂ) * ((ξ h : ℂˣ) : ℂ) :=
    fun h N' => rfl
  -- `ev h N` reproduces the species of `1 + a`
  have hFN : ∀ h : K₀, species K₀ h (1 + a) = ev h N := by
    intro h
    rw [map_add, map_one, hspec_a h, hNdef, map_add, map_sum]
    have h1 : ev h (Finsupp.single (1 : K₀ →* ℂˣ) 1) = 1 := by
      simp only [hev_single, MonoidHom.one_apply, Units.val_one, Int.cast_one,
        mul_one]
    rw [h1]
    refine congrArg (1 + ·) ?_
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [map_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [hev_single h _ (r c)]
  -- Parseval: the sum of squared coefficients is `1`
  have hsq : (∑ ξ ∈ N.support, (N ξ) ^ 2) = 1 := by
    refine sum_sq_eq_one_of_norm_one N (fun h => ?_)
    rw [← hevsum h N, ← hFN h]
    have hpn : (species K₀ h (1 + a)) ^ n = 1 := by
      rw [← map_pow, hpow, map_one]
    exact Complex.norm_eq_one_of_pow_eq_one hpn hn.ne'
  -- every coefficient of `N` is `-1`, `0`, or `1`
  have hNle : ∀ ξ : K₀ →* ℂˣ, (N ξ) ^ 2 ≤ 1 := by
    intro ξ
    by_cases hξ : ξ ∈ N.support
    · calc (N ξ) ^ 2 ≤ ∑ η ∈ N.support, (N η) ^ 2 :=
            Finset.single_le_sum (fun η _ => sq_nonneg _) hξ
        _ = 1 := hsq
    · have h0 : N ξ = 0 := by
        by_contra h0; exact hξ (Finsupp.mem_support_iff.mpr h0)
      rw [h0]; norm_num
  -- the coefficient of a character `ξ` as an indicator sum
  have hNval : ∀ ξ : K₀ →* ℂˣ, N ξ =
      (if (1 : K₀ →* ℂˣ) = ξ then (1 : ℤ) else 0) +
      ∑ c ∈ topSupp, ∑ q : fixedPoints K₀
        (induced c.out.1 c.out.2 : MonGSet G ℂˣ).carrier,
        (if conjChar K₀ c.out.1 c.out.2 q.1 q.2 = ξ then r c else 0) := by
    intro ξ
    rw [hNdef, Finsupp.add_apply, Finsupp.single_apply,
      Finsupp.finsetSum_apply]
    congr 1
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Finsupp.finsetSum_apply]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [Finsupp.single_apply]
  have hcardTS : ∀ c ∈ topSupp, Nat.card K₀ = Nat.card c.out.1 :=
    fun c hc => ((Finset.mem_filter.mp hc).2).symm
  -- only the class `⟦K₀, ξ⟧` feeds the `ξ`-coefficient (disjointness)
  have hinner_zero : ∀ (ξ : K₀ →* ℂˣ) (c : CharPairClass G ℂˣ),
      c ∈ topSupp →
      (⟦(⟨K₀, ξ⟩ : CharPair G ℂˣ)⟧ : CharPairClass G ℂˣ) ≠ c →
      ∑ q : fixedPoints K₀ (induced c.out.1 c.out.2 : MonGSet G ℂˣ).carrier,
        (if conjChar K₀ c.out.1 c.out.2 q.1 q.2 = ξ then r c else 0) = 0 := by
    intro ξ c hc hne
    refine Finset.sum_eq_zero fun q _ => ?_
    rw [if_neg]
    intro heq
    refine hne ?_
    rw [← heq, classElt_conjChar_eq K₀ c.out.1 c.out.2 q.1 q.2 (hcardTS c hc)]
    exact Quotient.out_eq c
  have hNval2 : ∀ (ξ : K₀ →* ℂˣ) (cD : CharPairClass G ℂˣ), cD ∈ topSupp →
      (⟦(⟨K₀, ξ⟩ : CharPair G ℂˣ)⟧ : CharPairClass G ℂˣ) = cD →
      N ξ = (if (1 : K₀ →* ℂˣ) = ξ then (1 : ℤ) else 0) +
        ∑ q : fixedPoints K₀
          (induced cD.out.1 cD.out.2 : MonGSet G ℂˣ).carrier,
          (if conjChar K₀ cD.out.1 cD.out.2 q.1 q.2 = ξ then r cD else 0) := by
    intro ξ cD hcDmem hcDeq
    rw [hNval ξ]
    congr 1
    refine Finset.sum_eq_single_of_mem cD hcDmem (fun c hc hne => ?_)
    exact hinner_zero ξ c hc (fun heq2 => hne (heq2.symm.trans hcDeq))
  -- the trivial-diagonal class carries mass `≥ 3`
  have hmass_triv : ∀ cD : CharPairClass G ℂˣ,
      (⟦(⟨K₀, (1 : K₀ →* ℂˣ)⟩ : CharPair G ℂˣ)⟧ : CharPairClass G ℂˣ) = cD →
      cD.out.2 = (1 : cD.out.1 →* ℂˣ) ∧
      3 ≤ Fintype.card (fixedPoints K₀
        (induced cD.out.1 cD.out.2 : MonGSet G ℂˣ).carrier) := by
    intro cD hcD
    have hout2 : cD.out.2 = (1 : cD.out.1 →* ℂˣ) := by
      have hconj := Quotient.mk_out (s := charPairSetoid G ℂˣ)
        (⟨K₀, (1 : K₀ →* ℂˣ)⟩ : CharPair G ℂˣ)
      rw [hcD] at hconj
      obtain ⟨g, hmem, hl⟩ := hconj
      refine MonoidHom.ext fun k => ?_
      obtain ⟨k, hk⟩ := k
      exact (hl k hk).symm
    refine ⟨hout2, ?_⟩
    have hbe : basisElt cD.out.1 cD.out.2 = basisElt K₀ (1 : K₀ →* ℂˣ) := by
      have hcm := classElt_mk (⟨K₀, (1 : K₀ →* ℂˣ)⟩ : CharPair G ℂˣ)
      rw [hcD] at hcm; exact hcm
    have hcards : (Fintype.card (fixedPoints K₀
        (induced cD.out.1 cD.out.2 : MonGSet G ℂˣ).carrier) : ℂ) =
        (Fintype.card (fixedPoints K₀
          (induced K₀ (1 : K₀ →* ℂˣ) : MonGSet G ℂˣ).carrier) : ℂ) := by
      rw [← species_basisElt_one_eq_card cD.out.1 K₀ cD.out.2,
        ← species_basisElt_one_eq_card K₀ K₀ (1 : K₀ →* ℂˣ), hbe]
    have hcardsN : Fintype.card (fixedPoints K₀
        (induced cD.out.1 cD.out.2 : MonGSet G ℂˣ).carrier) =
        Fintype.card (fixedPoints K₀
          (induced K₀ (1 : K₀ →* ℂˣ) : MonGSet G ℂˣ).carrier) := by
      exact_mod_cast hcards
    rw [hcardsN, ← Nat.card_eq_fintype_card]
    exact hmass3
  -- a witness fixed coset for `cS` and its induced character
  have hFixne : Nonempty (fixedPoints K₀
      (induced cS.out.1 cS.out.2 : MonGSet G ℂˣ).carrier) := by
    have hpos : 0 < Nat.card (fixedPoints K₀ (G ⧸ K₀)) := by omega
    exact (Nat.card_pos_iff.mp hpos).1
  obtain ⟨qS⟩ := hFixne
  set ξS : K₀ →* ℂˣ := conjChar K₀ cS.out.1 cS.out.2 qS.1 qS.2 with hξS
  have hcStop : cS ∈ topSupp := Finset.mem_filter.mpr ⟨hcSmem, rfl⟩
  have hcSrec : (⟦(⟨K₀, ξS⟩ : CharPair G ℂˣ)⟧ : CharPairClass G ℂˣ) = cS := by
    rw [hξS, classElt_conjChar_eq K₀ cS.out.1 cS.out.2 qS.1 qS.2
      (hcardTS cS hcStop)]
    exact Quotient.out_eq cS
  have hrcS : r cS ≠ 0 := Finsupp.mem_support_iff.mp hcSmem
  by_cases hξS1 : ξS = 1
  · -- `ξS = 1`: `cS` is the trivial diagonal; the mass kills `r cS`
    have hcSeq : (⟦(⟨K₀, (1 : K₀ →* ℂˣ)⟩ : CharPair G ℂˣ)⟧ :
        CharPairClass G ℂˣ) = cS := by rw [← hcSrec, hξS1]
    obtain ⟨hout2, hmass3'⟩ := hmass_triv cS hcSeq
    have hall : ∀ q : fixedPoints K₀
        (induced cS.out.1 cS.out.2 : MonGSet G ℂˣ).carrier,
        conjChar K₀ cS.out.1 cS.out.2 q.1 q.2 = 1 :=
      fun q => (conjChar_eq_one_iff K₀ cS.out.1 cS.out.2 q.1 q.2
        (hcardTS cS hcStop)).mpr hout2
    have hN1val : N (1 : K₀ →* ℂˣ) = 1 + (Fintype.card (fixedPoints K₀
        (induced cS.out.1 cS.out.2 : MonGSet G ℂˣ).carrier) : ℤ) * r cS := by
      rw [hNval2 (1 : K₀ →* ℂˣ) cS hcStop hcSeq, if_pos rfl]
      congr 1
      rw [Finset.sum_congr rfl fun q _ => by rw [if_pos (hall q)],
        Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have hle := hNle (1 : K₀ →* ℂˣ)
    rw [hN1val] at hle
    have hm3 : (3 : ℤ) ≤ (Fintype.card (fixedPoints K₀
        (induced cS.out.1 cS.out.2 : MonGSet G ℂˣ).carrier) : ℤ) := by
      exact_mod_cast hmass3'
    exact sq_one_add_mul_contra hm3 hrcS hle
  · -- `ξS ≠ 1`: pin `N 1 = 1`, then `N ξS = 0` kills `r cS`
    have hN1 : N (1 : K₀ →* ℂˣ) = 1 := by
      by_cases hc0mem : (⟦(⟨K₀, (1 : K₀ →* ℂˣ)⟩ : CharPair G ℂˣ)⟧ :
          CharPairClass G ℂˣ) ∈ topSupp
      · obtain ⟨hout2, hmass3'⟩ := hmass_triv _ rfl
        set c0 := (⟦(⟨K₀, (1 : K₀ →* ℂˣ)⟩ : CharPair G ℂˣ)⟧ :
          CharPairClass G ℂˣ) with hc0def
        have hall : ∀ q : fixedPoints K₀
            (induced c0.out.1 c0.out.2 : MonGSet G ℂˣ).carrier,
            conjChar K₀ c0.out.1 c0.out.2 q.1 q.2 = 1 :=
          fun q => (conjChar_eq_one_iff K₀ c0.out.1 c0.out.2 q.1 q.2
            (hcardTS c0 hc0mem)).mpr hout2
        have hN1val : N (1 : K₀ →* ℂˣ) = 1 + (Fintype.card (fixedPoints K₀
            (induced c0.out.1 c0.out.2 : MonGSet G ℂˣ).carrier) : ℤ) *
            r c0 := by
          rw [hNval2 (1 : K₀ →* ℂˣ) c0 hc0mem rfl, if_pos rfl]
          congr 1
          rw [Finset.sum_congr rfl fun q _ => by rw [if_pos (hall q)],
            Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        have hrc0 : r c0 = 0 := by
          by_contra hrc0
          have hle := hNle (1 : K₀ →* ℂˣ)
          rw [hN1val] at hle
          have hm3 : (3 : ℤ) ≤ (Fintype.card (fixedPoints K₀
              (induced c0.out.1 c0.out.2 : MonGSet G ℂˣ).carrier) : ℤ) := by
            exact_mod_cast hmass3'
          exact sq_one_add_mul_contra hm3 hrc0 hle
        rw [hN1val, hrc0, mul_zero, add_zero]
      · rw [hNval (1 : K₀ →* ℂˣ), if_pos rfl]
        have hz : ∑ c ∈ topSupp, ∑ q : fixedPoints K₀
            (induced c.out.1 c.out.2 : MonGSet G ℂˣ).carrier,
            (if conjChar K₀ c.out.1 c.out.2 q.1 q.2 = 1 then r c else 0)
            = 0 := by
          refine Finset.sum_eq_zero fun c hc => ?_
          exact hinner_zero (1 : K₀ →* ℂˣ) c hc (fun heq => hc0mem (heq ▸ hc))
        rw [hz, add_zero]
    -- `N ξS = 0`
    have hNξS0 : N ξS = 0 := by
      by_cases hmem : ξS ∈ N.support
      · have h1mem : (1 : K₀ →* ℂˣ) ∈ N.support := by
          rw [Finsupp.mem_support_iff, hN1]; norm_num
        have hne : (1 : K₀ →* ℂˣ) ≠ ξS := fun h => hξS1 h.symm
        have hsub : ({(1 : K₀ →* ℂˣ), ξS} : Finset (K₀ →* ℂˣ)) ⊆
            N.support := by
          intro η hη
          rw [Finset.mem_insert, Finset.mem_singleton] at hη
          rcases hη with rfl | rfl
          · exact h1mem
          · exact hmem
        have hle2 := Finset.sum_le_sum_of_subset_of_nonneg hsub
          (fun η _ _ => sq_nonneg (N η))
        rw [Finset.sum_pair hne] at hle2
        have hpair : (N (1 : K₀ →* ℂˣ)) ^ 2 + (N ξS) ^ 2 ≤
            ∑ η ∈ N.support, (N η) ^ 2 := hle2
        rw [hsq, hN1] at hpair
        have h2 : (N ξS) ^ 2 = 0 := le_antisymm (by nlinarith [hpair])
          (sq_nonneg _)
        exact pow_eq_zero_iff (two_ne_zero) |>.mp h2
      · by_contra h; exact hmem (Finsupp.mem_support_iff.mpr h)
    -- expand and factor out `r cS`
    rw [hNval2 ξS cS hcStop hcSrec, if_neg fun h => hξS1 h.symm,
      zero_add] at hNξS0
    have hfactor : (∑ q : fixedPoints K₀
        (induced cS.out.1 cS.out.2 : MonGSet G ℂˣ).carrier,
        (if conjChar K₀ cS.out.1 cS.out.2 q.1 q.2 = ξS then (1 : ℤ)
          else 0)) * r cS = 0 := by
      have hrw : (∑ q : fixedPoints K₀
          (induced cS.out.1 cS.out.2 : MonGSet G ℂˣ).carrier,
          (if conjChar K₀ cS.out.1 cS.out.2 q.1 q.2 = ξS then (1 : ℤ)
            else 0)) * r cS =
          ∑ q : fixedPoints K₀
            (induced cS.out.1 cS.out.2 : MonGSet G ℂˣ).carrier,
            (if conjChar K₀ cS.out.1 cS.out.2 q.1 q.2 = ξS then r cS
              else 0) := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun q _ => ?_
        split_ifs <;> ring
      rw [hrw, hNξS0]
    have hcount_pos : 0 < ∑ q : fixedPoints K₀
        (induced cS.out.1 cS.out.2 : MonGSet G ℂˣ).carrier,
        (if conjChar K₀ cS.out.1 cS.out.2 q.1 q.2 = ξS then (1 : ℤ)
          else 0) := by
      refine Finset.sum_pos' (fun q _ => by split_ifs <;> norm_num)
        ⟨qS, Finset.mem_univ _, ?_⟩
      rw [if_pos hξS.symm]; norm_num
    rcases mul_eq_zero.mp hfactor with hcount0 | hr0
    · exact absurd hcount0 hcount_pos.ne'
    · exact hrcS hr0

open MulAction in
/-- **The mass hypothesis holds for `p`-groups, `p ≥ 3`**: normalizers
grow (nilpotency), and the index `|N(K):K| = #(G/K)^K` is a nontrivial
`p`-power. -/
theorem mass_ge_three_of_pgroup {p : ℕ} [Fact p.Prime] (hp3 : 3 ≤ p)
    {t : ℕ} (hcard : Nat.card G = p ^ t) :
    ∀ K : Subgroup G, Nat.card K < Nat.card G →
      3 ≤ Nat.card (fixedPoints K (G ⧸ K)) := by
  intro K hK
  have hpg : IsPGroup p G := IsPGroup.of_card hcard
  haveI : Group.IsNilpotent G := IsPGroup.isNilpotent hpg
  have hNC : NormalizerCondition G := Group.normalizerCondition_of_isNilpotent
  -- `K` is proper, hence properly contained in its normalizer
  have hKtop : K < ⊤ := by
    refine lt_of_le_of_ne le_top fun h => ?_
    rw [h, Subgroup.card_top] at hK
    exact lt_irrefl _ hK
  have hKN : K < Subgroup.normalizer (K : Set G) := hNC K hKtop
  -- the mass `m = |N(K):K|` satisfies `m·|K| = |N(K)|`
  have hmul := card_fixedPoints_coset K
  set m := Nat.card (fixedPoints K (G ⧸ K)) with hm
  -- `m ≠ 0`
  have hm0 : m ≠ 0 := mark_self_ne_zero K
  -- `m ≠ 1`: else `K = N(K)`, contradicting growth
  have hm1 : m ≠ 1 := by
    intro h1
    rw [h1, one_mul] at hmul
    have heq : K = Subgroup.normalizer (K : Set G) :=
      Subgroup.eq_of_le_of_card_ge hKN.le (le_of_eq hmul.symm)
    exact hKN.ne heq
  -- `m` divides `|G| = p^t`
  have hmdvd : m ∣ p ^ t := by
    have h1 : m ∣ Nat.card (Subgroup.normalizer (K : Set G)) :=
      ⟨Nat.card K, hmul.symm⟩
    have h2 : Nat.card (Subgroup.normalizer (K : Set G)) ∣ Nat.card G :=
      Subgroup.card_subgroup_dvd_card _
    rw [hcard] at h2
    exact dvd_trans h1 h2
  -- hence `m` is a `p`-power `≥ p ≥ 3`
  obtain ⟨j, hj, hmj⟩ := (Nat.dvd_prime_pow (Fact.out : p.Prime)).mp hmdvd
  have hj1 : 1 ≤ j := by
    by_contra hj0
    have : j = 0 := by omega
    rw [this, pow_zero] at hmj
    exact hm1 hmj
  calc (3 : ℕ) ≤ p := hp3
    _ ≤ p ^ j := Nat.le_self_pow (by omega) p
    _ = m := hmj.symm

open MulAction in
-- hypothesis kept: signature is paper-facing (AxiomAudit.lean:28,
-- `#print axioms LeanDring.DRing.torsion_unit_eq_pm_charElt`).
/-- **Satz 2.6.3 (Müller)**: under the normalizer-growth hypothesis,
every torsion unit of `D(G)` is `± charElt λ` — the torsion units are
exactly `±Ĝ`. -/
theorem torsion_unit_eq_pm_charElt
    (hmass : ∀ K : Subgroup G, Nat.card K < Nat.card G →
      3 ≤ Nat.card (fixedPoints K (G ⧸ K)))
    {u : DRing G} {n : ℕ} (hn : 0 < n) (hu : u ^ n = 1) :
    ∃ l : G →* ℂˣ, u = charElt l ∨ u = -charElt l := by
  obtain ⟨l, a, ha, han, hcase⟩ := torsion_unit_eq_charElt_mul hn hu
  have ha0 : a = 0 := eq_zero_of_one_add_pow_eq_one hmass ha hn han
  subst ha0
  refine ⟨l, ?_⟩
  rcases hcase with h | h
  · left
    rw [h, add_zero, mul_one]
  · right
    rw [h, add_zero, mul_one]

open MulAction in
-- hypothesis kept: signature is paper-facing (AxiomAudit.lean:29,
-- `#print axioms LeanDring.DRing.torsion_unit_eq_pm_charElt_of_pgroup`).
/-- **Satz 2.6.3 for `p`-groups, `p ≥ 3`**: the torsion units of `D(G)`
are exactly `±Ĝ`. -/
theorem torsion_unit_eq_pm_charElt_of_pgroup {p : ℕ} [Fact p.Prime]
    (hp3 : 3 ≤ p) {t : ℕ} (hcard : Nat.card G = p ^ t)
    {u : DRing G} {n : ℕ} (hn : 0 < n) (hu : u ^ n = 1) :
    ∃ l : G →* ℂˣ, u = charElt l ∨ u = -charElt l :=
  torsion_unit_eq_pm_charElt (mass_ge_three_of_pgroup hp3 hcard) hn hu

end DRing

end LeanDring
