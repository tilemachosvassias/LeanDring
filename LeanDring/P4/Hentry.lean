/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P4.NoTableIso
import LeanDring.Theory.Cyclotomic.CyclotomicNonMem

/-!
# The structural reduction `hentry`

The number-theoretic core of the twin separation (the `G₁`/`G₂` entry formulas,
the value equation and its refutation) lives in `P4TwinSeparation` and
`P4Endgame`. This file supplies the structural half: the steps that turn a
`SpeciesTableIso` between the two order-`p⁴` twins into the entry equality that
`P4.twin_entry_equality_impossible` refutes.

The route avoids tracking the isomorphism's column maps (`T.sub'`/`T.el'`),
which the `SpeciesTableIso` interface constrains only loosely — they need not
preserve the maximal abelian subgroup or the order of an element. Instead the
`G₂` distinguished value `z` is classified against the *model's own* entries:

> every species entry of `Model p 1` that does **not** lie in `ℤ[ζ_p]` is an
> A-block entry at an order-`p²` character, hence has the `G₁` entry form
> `√p · ζ₈ₚ^{p-(1+2β)²} · ζ_{p²}^{1+mp}`.

The pieces proved here are:

1. `exists_G1_entry_eq` — a table iso `T` exhibits *some* `Model p 1` species
   entry equal to the `G₂` distinguished entry `z`; pure `T.entry'` plumbing.
2. `entry_not_mem_adjoin` — `z ∉ ℤ[ζ_p]`, from `ζ_{p²} ∉ ℤ[ζ_p]`
   (`LeanDring.Theory.Cyclotomic.CyclotomicNonMem`) and the factorization
   `entry = χ(s)·bracket` with `bracket ∈ ℤ[ζ_p]`.
3. `species_A_row_eq_zero_of_not_le` and `species_le_normal_eq` — the row/column
   reduction that turns a nonzero entry over the A-row into an A-block entry.
4. `A_block_mem_adjoin_iff` — the converse classification at the distinguished
   column: an A-block entry escapes `ℤ[ζ_p]` exactly at order-`p²` characters.

`P4ExpA` and `P4ExpGen` generalize 4 and the entry formula to an arbitrary
A-block column, and `P4TwinFinal` assembles the whole reduction.
-/

namespace LeanDring.P4

open DRing MonGSet Model MulAction

variable {p : ℕ} [Fact p.Prime] [Fact (Odd p)]

/-- **Step 1 of `hentry`: a table iso exhibits the `G₂` distinguished entry as a
`G₁` species entry.**  For any character `χ` of the `G₂` maximal abelian
subgroup, the `G₂` A-block entry `s_{(A,ca^d)}([A,χ])` occurs verbatim as a
`Model p 1` species entry — at the column/row image under `T.symm`.  This is the
"`z` appears in `G₁`'s table" step, and needs no control over the isomorphism's
column maps: it is a direct instance of the entry-equality axiom `T.entry'`. -/
theorem exists_G1_entry_eq {d : ZMod p}
    (T : SpeciesTableIso (Model p 1) (Model p d)) (χ : subA p d →* ℂˣ) :
    ∃ (H₁ : Subgroup (Model p 1)) (h₁ : H₁) (ρ : CharPairClass (Model p 1) ℂˣ),
      species H₁ h₁ (classElt ρ)
        = species (subA p d) (sElt p d) (DRing.basisElt (subA p d) χ) := by
  refine ⟨T.sub' (subA p d), T.el' (sElt p d),
    T.rows.symm (⟦⟨subA p d, χ⟩⟧ : CharPairClass (Model p d) ℂˣ), ?_⟩
  rw [← classElt_mk (⟨subA p d, χ⟩ : CharPair (Model p d) ℂˣ)]
  exact T.entry' (subA p d) (sElt p d) (⟦⟨subA p d, χ⟩⟧)

/-- **The A-block entry factors as `χ(ca^d) · bracket`.**
Pulling the character value at the distinguished generator `s = ca^d` out of
each conjugate term of `species_A_block`, the entry becomes `χ(s)` times a sum
of the values `χ(s⁻¹ · s^{aⁿ})` on the conjugation "displacements".  Each
displacement `s⁻¹ · s^{aⁿ}` lies in `A` with trivial `s`-coordinate (`u = 0`),
so it has order dividing `p` and its `χ`-value is a `p`-th root of unity — hence
the bracket lies in `ℤ[ζ_p]` (proved separately, feeding the `z ∉ ℤ[ζ_p]`
step).  This factorization needs no group-law computation: it is `χ(s·g) = χ(s)·χ(g)`
term by term, with `s · (s⁻¹ · s^{aⁿ}) = s^{aⁿ}`. -/
theorem entry_factor {d : ZMod p} (χ : subA p d →* ℂˣ) :
    species (subA p d) (sElt p d) (DRing.basisElt (subA p d) χ)
      = ((χ (sElt p d) : ℂˣ) : ℂ) *
        ∑ t : ZMod p,
          ((χ ((sElt p d)⁻¹ * conjA p d (aGen p d ^ t.val) (sElt p d)) : ℂˣ) : ℂ) := by
  rw [species_A_block, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  rw [← Units.val_mul, ← map_mul, mul_inv_cancel_left]

/-- **The conjugation displacements have order dividing `p`.**  Each
`g_t := s⁻¹ · s^{aᵗ}` lies in `A` (so `redp g_t.α = 0`) with trivial
`s`-coordinate (`g_t.u = 0`, since `u` is additive under the group law and both
`s⁻¹` and `s^{aᵗ}` have `s`-coordinate `∓1`); hence `g_t^p = 1` by the
model's `x^p = 1 ⇔ redp α + d·u = 0` criterion.  Consequently `χ(g_t)` is a
`p`-th root of unity and the `entry_factor` bracket lies in `ℤ[ζ_p]`. -/
theorem disp_pow_p {d : ZMod p} (hp5 : 5 ≤ p) (t : ZMod p) :
    ((sElt p d)⁻¹ * conjA p d (aGen p d ^ t.val) (sElt p d)) ^ p = 1 := by
  set g : subA p d := (sElt p d)⁻¹ * conjA p d (aGen p d ^ t.val) (sElt p d) with hg
  have hconj : ((conjA p d (aGen p d ^ t.val) (sElt p d) : subA p d) : Model p d).u
      = ((sElt p d : subA p d) : Model p d).u := by rw [conjA_aGen_pow]
  have hu : ((g : subA p d) : Model p d).u = 0 := by
    rw [hg, Subgroup.coe_mul, Subgroup.coe_inv]
    change -((sElt p d : subA p d) : Model p d).u +
      ((conjA p d (aGen p d ^ t.val) (sElt p d) : subA p d) : Model p d).u = 0
    rw [hconj]; ring
  have hα : redp p ((g : subA p d) : Model p d).α = 0 := mem_subA_iff.mp g.2
  apply Subtype.ext
  rw [Subgroup.coe_pow, Subgroup.coe_one, pow_p_eq_one_iff hp5, hα, hu]
  ring

/-- **The distinguished `G₂` entry is not in `ℤ[ζ_p]`.**
Combining `entry_factor` (`entry = χ(s)·bracket`), `disp_pow_p` (the bracket is a
sum of `p`-th roots, so `bracket ∈ ℤ[ζ_p]` by `mem_adjoin_of_pow_eq_one`), and
the hypothesis `χ(s) = ζ_{p²}`: if the entry were in `ℤ[ζ_p]` then
`bracket·ζ_{p²} ∈ ℤ[ζ_p]`, forcing `bracket = 0` (`eq_zero_of_mul_zetaP2_mem`),
hence `entry = 0` — contradicting `entry ≠ 0` (`|entry| = √p`).  This is the
`z ∉ ℤ[ζ_p]` input to the entry classification. -/
theorem entry_not_mem_adjoin {d : ZMod p} (hp5 : 5 ≤ p) (χ : subA p d →* ℂˣ)
    (hχs : ((χ (sElt p d) : ℂˣ) : ℂ) = zetaP2 p)
    (hne : species (subA p d) (sElt p d) (DRing.basisElt (subA p d) χ) ≠ 0) :
    species (subA p d) (sElt p d) (DRing.basisElt (subA p d) χ)
      ∉ (Algebra.adjoin ℤ {(zetaP2 p) ^ p} : Subalgebra ℤ ℂ) := by
  have hp : p.Prime := Fact.out
  have hodd : Odd p := Fact.out
  have hζp2 : IsPrimitiveRoot (zetaP2 p) (p ^ 2) := by
    rw [zetaP2]; exact Complex.isPrimitiveRoot_exp (p ^ 2) (pow_ne_zero 2 hp.ne_zero)
  have hζp : IsPrimitiveRoot ((zetaP2 p) ^ p) p := hζp2.pow (pow_pos hp.pos 2) (by ring)
  -- each bracket term is a `p`-th root of unity
  have hroot : ∀ t : ZMod p,
      ((χ ((sElt p d)⁻¹ * conjA p d (aGen p d ^ t.val) (sElt p d)) : ℂˣ) : ℂ) ^ p = 1 := by
    intro t
    rw [← Units.val_pow_eq_pow_val, ← map_pow, disp_pow_p hp5, map_one, Units.val_one]
  -- hence the bracket lies in `ℤ[ζ_p]`
  have hbracket : (∑ t : ZMod p,
      ((χ ((sElt p d)⁻¹ * conjA p d (aGen p d ^ t.val) (sElt p d)) : ℂˣ) : ℂ))
      ∈ (Algebra.adjoin ℤ {(zetaP2 p) ^ p} : Subalgebra ℤ ℂ) :=
    Subalgebra.sum_mem _ (fun t _ => mem_adjoin_of_pow_eq_one hp hζp (hroot t))
  intro hmem
  rw [entry_factor, hχs] at hmem
  have hbz : (∑ t : ZMod p,
      ((χ ((sElt p d)⁻¹ * conjA p d (aGen p d ^ t.val) (sElt p d)) : ℂˣ) : ℂ)) * zetaP2 p
      ∈ (Algebra.adjoin ℤ {(zetaP2 p) ^ p} : Subalgebra ℤ ℂ) := by
    rw [mul_comm]; exact hmem
  have hb0 := eq_zero_of_mul_zetaP2_mem hp hodd hζp2 hζp hbracket hbz
  exact hne (by rw [entry_factor, hχs, hb0, mul_zero])

/-! ### The `H`-reduction: an A-row entry vanishes off the A-block -/

/-- **`H`-reduction: an entry over the A-row vanishes unless the column
subgroup lies in `A`.**  Because `A = subA p d` is normal of index `p`, a coset
`qA` of `G/A` is `H`-fixed iff `q⁻¹Hq ⊆ A` iff `H ⊆ A`.  So if `H ⊄ A` the
`H`-fixed-point set of `G/A` is empty and the species sum is empty — the
entry is `0`.  Contrapositive: a **nonzero** entry over the A-row forces the
column `H ⊆ A`, reducing it to an A-block entry (no norm, no ω-scaling). -/
theorem species_A_row_eq_zero_of_not_le {d : ZMod p} {H : Subgroup (Model p d)}
    (hH : ¬ H ≤ subA p d) (h : H) (χ : subA p d →* ℂˣ) :
    species H h (DRing.basisElt (subA p d) χ) = 0 := by
  classical
  rw [species_basisElt]
  haveI : IsEmpty (fixedPoints H
      (induced (subA p d) χ : MonGSet (Model p d) ℂˣ).carrier) := by
    constructor
    rintro ⟨q, hq⟩
    obtain ⟨k, hkH, hkA⟩ : ∃ k : Model p d, k ∈ H ∧ k ∉ subA p d := by
      by_contra hcon
      push Not at hcon
      exact hH fun x hx => hcon x hx
    have hfix := hq ⟨k, hkH⟩
    obtain ⟨g⟩ := q
    have h2 : ((k * g : Model p d) : Model p d ⧸ subA p d)
        = (g : Model p d ⧸ subA p d) := hfix
    have h3 := (QuotientGroup.eq).mp h2
    have h4 : g⁻¹ * k⁻¹ * g ∈ subA p d := by
      have he : (k * g)⁻¹ * g = g⁻¹ * k⁻¹ * g := by group
      rwa [he] at h3
    apply hkA
    have h5 : k⁻¹ ∈ subA p d := by
      have := (inferInstance : (subA p d).Normal).conj_mem _ h4 g
      rwa [show g * (g⁻¹ * k⁻¹ * g) * g⁻¹ = k⁻¹ by group] at this
    simpa using (subA p d).inv_mem h5
  rw [Finset.univ_eq_empty, Finset.sum_empty]

/-- **Companion to the `H`-reduction: over a normal row the column collapses to
`K`.**  For `K ⊴ G`, `H ≤ K`, and `h ∈ H`, the entry `φ_{H,h}[K,χ]` equals the
`K`-column entry `φ_{K,h}[K,χ]`: both fixed-point sets are all of `G/K` (since
`K` — hence `H ≤ K` — acts trivially on `G/K`), and the summand depends only on
`h`.  Combined with `species_A_row_eq_zero_of_not_le`, a nonzero A-row entry
becomes an A-block entry `species_A_block`. -/
theorem species_le_normal_eq {G : Type u} [Group G] [Fintype G] {K : Subgroup G}
    [K.Normal] {H : Subgroup G} (hHK : H ≤ K) (h : H) (χ : K →* ℂˣ) :
    species H h (DRing.basisElt K χ) = species K ⟨h, hHK h.2⟩ (DRing.basisElt K χ) := by
  classical
  rw [species_basisElt, species_basisElt]
  refine Fintype.sum_equiv
    (Equiv.subtypeEquivProp (funext fun q => ?_)) _ _ (fun q => ?_)
  · -- `q ∈ fixedPoints H (G/K) ↔ q ∈ fixedPoints K (G/K)`: both hold for all `q`
    exact propext ⟨fun _ => coset_mem_fixedPoints K q,
      fun _ k => coset_mem_fixedPoints K q ⟨(k : G), hHK k.2⟩⟩
  · rfl

/-! ### Order facts: `s = ca^d` has order dividing `p²` -/

/-- The central generators `zElt` have order dividing `p` (they are `a^{p·z}`). -/
theorem zElt_pow_p {d : ZMod p} (hp5 : 5 ≤ p) (z : ZMod p) :
    (zElt p d z) ^ p = 1 := by
  apply Subtype.ext
  rw [Subgroup.coe_pow, Subgroup.coe_one, pow_p_eq_one_iff hp5]
  change redp p (liftp p z) + d * 0 = 0
  rw [redp_liftp, mul_zero, add_zero]

/-- `s^p = a^{dp} = zElt d`. -/
theorem sElt_pow_p {d : ZMod p} (hp5 : 5 ≤ p) :
    (sElt p d) ^ p = zElt p d d := by
  apply Subtype.ext
  rw [Subgroup.coe_pow, sElt_coe, pow_p hp5 (⟨0, 1, 0⟩ : Model p d)]
  change (⟨liftp p (redp p 0 + d * 1), 0, 0⟩ : Model p d) = ⟨liftp p d, 0, 0⟩
  rw [map_zero (redp p)]
  congr 2
  ring

/-- **The distinguished generator `s = ca^d` has order dividing `p²`.**  Hence
every character value `χ(s)` is a `p²`-th root of unity — the input to the
`p²`-root membership dichotomy. -/
theorem sElt_pow_psq {d : ZMod p} (hp5 : 5 ≤ p) :
    (sElt p d) ^ (p ^ 2) = 1 := by
  rw [pow_two, pow_mul, sElt_pow_p hp5, zElt_pow_p hp5]

/-- **The A-block order-`p²` classification (`s = ca` column).**  A nonzero
A-block entry at `s` lies in `ℤ[ζ_p]` **iff** the character value `χ(s)` is a
`p`-th root of unity — i.e. iff `χ` is *not* an order-`p²` character.  The escape
from `ℤ[ζ_p]` (the `z ∉ ℤ[ζ_p]` phenomenon) happens exactly for order-`p²`
characters.  Combines `entry_factor` (`entry = χ(s)·bracket`, `bracket ∈ ℤ[ζ_p]`),
the `p²`-root fact `sElt_pow_psq`, and — for the forward direction — the
dichotomy via `eq_zero_of_mul_zetaP2_mem` with `ζ_{p²} := χ(s)`. -/
theorem A_block_mem_adjoin_iff {d : ZMod p} (hp5 : 5 ≤ p) (χ : subA p d →* ℂˣ)
    (hne : species (subA p d) (sElt p d) (DRing.basisElt (subA p d) χ) ≠ 0) :
    species (subA p d) (sElt p d) (DRing.basisElt (subA p d) χ)
        ∈ (Algebra.adjoin ℤ {(zetaP2 p) ^ p} : Subalgebra ℤ ℂ)
      ↔ ((χ (sElt p d) : ℂˣ) : ℂ) ^ p = 1 := by
  have hp : p.Prime := Fact.out
  have hodd : Odd p := Fact.out
  haveI : Fact p.Prime := ⟨hp⟩
  have hζp2 : IsPrimitiveRoot (zetaP2 p) (p ^ 2) := by
    rw [zetaP2]; exact Complex.isPrimitiveRoot_exp (p ^ 2) (pow_ne_zero 2 hp.ne_zero)
  have hζp : IsPrimitiveRoot ((zetaP2 p) ^ p) p := hζp2.pow (pow_pos hp.pos 2) (by ring)
  have hχpsq : ((χ (sElt p d) : ℂˣ) : ℂ) ^ (p ^ 2) = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← map_pow, sElt_pow_psq hp5, map_one, Units.val_one]
  have hroot : ∀ t : ZMod p,
      ((χ ((sElt p d)⁻¹ * conjA p d (aGen p d ^ t.val) (sElt p d)) : ℂˣ) : ℂ) ^ p = 1 := by
    intro t
    rw [← Units.val_pow_eq_pow_val, ← map_pow, disp_pow_p hp5, map_one, Units.val_one]
  have hbracket : (∑ t : ZMod p,
      ((χ ((sElt p d)⁻¹ * conjA p d (aGen p d ^ t.val) (sElt p d)) : ℂˣ) : ℂ))
      ∈ (Algebra.adjoin ℤ {(zetaP2 p) ^ p} : Subalgebra ℤ ℂ) :=
    Subalgebra.sum_mem _ (fun t _ => mem_adjoin_of_pow_eq_one hp hζp (hroot t))
  constructor
  · intro hmem
    by_contra hp1
    have hprim : IsPrimitiveRoot ((χ (sElt p d) : ℂˣ) : ℂ) (p ^ 2) := by
      rw [IsPrimitiveRoot.iff_orderOf]
      exact orderOf_eq_prime_pow (by rw [pow_one]; exact hp1) hχpsq
    rw [entry_factor] at hmem
    have hbz : (∑ t : ZMod p,
        ((χ ((sElt p d)⁻¹ * conjA p d (aGen p d ^ t.val) (sElt p d)) : ℂˣ) : ℂ))
        * ((χ (sElt p d) : ℂˣ) : ℂ)
        ∈ (Algebra.adjoin ℤ {(zetaP2 p) ^ p} : Subalgebra ℤ ℂ) := by
      rw [mul_comm]; exact hmem
    have hb0 := eq_zero_of_mul_zetaP2_mem hp hodd hprim hζp hbracket hbz
    exact hne (by rw [entry_factor, hb0, mul_zero])
  · intro hp1
    rw [entry_factor]
    exact Subalgebra.mul_mem _ (mem_adjoin_of_pow_eq_one hp hζp hp1) hbracket

/-! ### General A-block column `h ∈ A` (via `subA_pow_psq`) -/

/-- **Displacements at a general A-column have order dividing `p`.**  Generalizes
`disp_pow_p` from `s` to any `h ∈ A`: `h⁻¹ · h^{aⁿ}` has `u`-coordinate `0`
(conjugation preserves `u`, `h⁻¹` negates it) and lies in `A`. -/
theorem disp_pow_p_gen {d : ZMod p} (hp5 : 5 ≤ p) (h : subA p d) (t : ZMod p) :
    (h⁻¹ * conjA p d (aGen p d ^ t.val) h) ^ p = 1 := by
  set g : subA p d := h⁻¹ * conjA p d (aGen p d ^ t.val) h with hg
  have hconj : ((conjA p d (aGen p d ^ t.val) h : subA p d) : Model p d).u
      = ((h : subA p d) : Model p d).u := by rw [conjA_aGen_pow]
  have hu : ((g : subA p d) : Model p d).u = 0 := by
    rw [hg, Subgroup.coe_mul, Subgroup.coe_inv]
    change -((h : subA p d) : Model p d).u +
      ((conjA p d (aGen p d ^ t.val) h : subA p d) : Model p d).u = 0
    rw [hconj]; ring
  have hα : redp p ((g : subA p d) : Model p d).α = 0 := mem_subA_iff.mp g.2
  apply Subtype.ext
  rw [Subgroup.coe_pow, Subgroup.coe_one, pow_p_eq_one_iff hp5, hα, hu]
  ring

/-- **Factorization of a general A-block entry** (`entry_factor` for any `h ∈ A`). -/
theorem entry_factor_gen {d : ZMod p} (χ : subA p d →* ℂˣ) (h : subA p d) :
    species (subA p d) h (DRing.basisElt (subA p d) χ)
      = ((χ h : ℂˣ) : ℂ) *
        ∑ t : ZMod p,
          ((χ (h⁻¹ * conjA p d (aGen p d ^ t.val) h) : ℂˣ) : ℂ) := by
  rw [species_A_block, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  rw [← Units.val_mul, ← map_mul, mul_inv_cancel_left]

end LeanDring.P4
