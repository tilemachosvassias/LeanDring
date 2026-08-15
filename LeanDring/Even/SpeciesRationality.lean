/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.Even.SpeciesSurjectivity

/-!
# Fully fused ⟹ rational: the backward half of `ConductorPairDictionary`

**EVEN-ORDER LAYER.** Inside the root module's build closure and audit:
no `sorry`, three standard axioms. The results here are
verified *implications*; their hypotheses are named `Prop`s (see §7.6 of
the paper).

`LeanDring/Even/ConductorDictionaryGalois.lean` proved the *forward* Galois
implication — an integer point is Adams-stable, hence its pair is fully fused.
This file proves the **converse**:

> if the pair class `(H, h⁅H,H⁆)` is `FullyFused`, then every value
> `φ_{H,h}(x)` is rational, hence (being an algebraic integer) an honest
> rational integer, and `φ_{H,h}` is the complexification of an integer point
> `p: D(G) →+* ℤ`.

## The Galois descent, without Galois theory

The analytic core is `rat_of_pow_twist_eq`:

> a `ℤ`-combination `v = ∑ cᵢ wᵢ` of `N`-th roots of unity which is fixed by
> **every** twist `wᵢ ↦ wᵢᵃ`, `gcd(a, N) = 1`, is rational.

No Galois group, no cyclotomic field object is constructed.  Writing
`wᵢ = ζ^{kᵢ}` for `ζ = exp(2πi/N)` makes `v = f(ζ)` for an explicit
`f ∈ ℚ[X]`; the twist hypothesis says `f(ρ) = v` at *every* primitive `N`-th
root of unity `ρ` (they are exactly the `ζᵃ`).  Replacing `f` by its remainder
`r = f %ₘ Φ_N` (legitimate: `Φ_N` vanishes at every primitive root) gives a
rational polynomial of degree `< φ(N)` taking the constant value `v` at
`φ(N)` distinct points — so `r - v` is the zero polynomial by the pigeonhole
bound `Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero'`, whence
`v = r.coeff 0 ∈ ℚ`.

This is the exact mirror image's `sum_pow_eq_of_sum_eq_rat`
(rational ⟹ twist-invariant); together they make "fully fused" and "rational"
equivalent.

## The group-theoretic input

`FullyFused H h` says `hᵃ` is `N_G(H)`-conjugate to `h` modulo `⁅H,H⁆`.  Both
moves leave the species unchanged — conjugation by `DRing.species_conj`
(`LeanDring/Theory/DRing/SpeciesConj.lean`) specialized to the normalizer, and the
`⁅H,H⁆`-shift by `DRing.species_congr_coset` — so
`φ_{H,hᵃ} = φ_{H,h}` (`species_pow_eq_of_fullyFused`), which is precisely the
twist-invariance hypothesis of `rat_of_pow_twist_eq`.

No `sorry`, no custom axiom.
-/

set_option linter.unusedFintypeInType false

namespace LeanDring

open MulAction

universe u

/-! ## The descent: a twist-invariant sum of roots of unity is rational -/

section Descent

open Polynomial

/-- **Galois descent for sums of roots of unity, elementary form.**  If a
`ℤ`-linear combination of `N`-th roots of unity is unchanged by every twist
`w ↦ wᵃ` with `gcd(a, N) = 1`, then it is rational.

This is the converse of `sum_pow_eq_of_sum_eq_rat`. -/
theorem rat_of_pow_twist_eq {N : ℕ} (hN : 0 < N) {ι : Type*} [Fintype ι]
    (c : ι → ℤ) (w : ι → ℂ) (hw : ∀ i, w i ^ N = 1)
    (hinv : ∀ a : ℕ, Nat.Coprime a N →
      ∑ i, (c i : ℂ) * (w i) ^ a = ∑ i, (c i : ℂ) * w i) :
    ∃ q : ℚ, ∑ i, (c i : ℂ) * w i = (q : ℂ) := by
  classical
  haveI : NeZero N := ⟨hN.ne'⟩
  set ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / N) with hζdef
  have hζ : IsPrimitiveRoot ζ N := Complex.isPrimitiveRoot_exp N hN.ne'
  -- write every `w i` as a power of `ζ`
  have hk : ∀ i, ∃ k : ℕ, ζ ^ k = w i := fun i => by
    obtain ⟨k, _, hkw⟩ := hζ.eq_pow_of_pow_eq_one (hw i)
    exact ⟨k, hkw⟩
  choose k hkspec using hk
  set f : ℚ[X] := ∑ i, C ((c i : ℚ)) * X ^ (k i) with hfdef
  have hfeval : ∀ z : ℂ, aeval z f = ∑ i, (c i : ℂ) * z ^ (k i) := by
    intro z
    rw [hfdef, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, aeval_C, map_pow, aeval_X, eq_ratCast]
    norm_num
  -- `f` takes the value `v` at *every* primitive `N`-th root of unity
  have hprim : ∀ ρ ∈ primitiveRoots N ℂ, aeval ρ f = ∑ i, (c i : ℂ) * w i := by
    intro ρ hρ
    rw [mem_primitiveRoots hN] at hρ
    obtain ⟨a, _, hae⟩ := hζ.eq_pow_of_pow_eq_one hρ.pow_eq_one
    have hcop : Nat.Coprime a N := (hζ.pow_iff_coprime hN a).mp (hae ▸ hρ)
    rw [hfeval, ← hae, ← hinv a hcop]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← hkspec i, ← pow_mul, ← pow_mul, Nat.mul_comm]
  -- reduce modulo the cyclotomic polynomial
  have hmonic : (cyclotomic N ℚ).Monic := cyclotomic.monic N ℚ
  set r : ℚ[X] := f %ₘ (cyclotomic N ℚ) with hrdef
  have hcyc : ∀ ρ ∈ primitiveRoots N ℂ, aeval ρ (cyclotomic N ℚ) = 0 := by
    intro ρ hρ
    rw [mem_primitiveRoots hN] at hρ
    rw [aeval_def, eval₂_eq_eval_map, map_cyclotomic]
    exact isRoot_cyclotomic_iff.mpr hρ
  have hreval : ∀ ρ ∈ primitiveRoots N ℂ, aeval ρ r = ∑ i, (c i : ℂ) * w i := by
    intro ρ hρ
    have hsplit : r + cyclotomic N ℚ * (f /ₘ cyclotomic N ℚ) = f :=
      modByMonic_add_div f (cyclotomic N ℚ)
    have := congrArg (fun p : ℚ[X] => aeval ρ p) hsplit
    simp only [map_add, map_mul, hcyc ρ hρ, zero_mul, add_zero] at this
    rw [this]
    exact hprim ρ hρ
  -- degree bound
  have hrdeg : r.natDegree < Nat.totient N := by
    rcases eq_or_ne r 0 with h0 | h0
    · rw [h0, natDegree_zero]
      exact Nat.totient_pos.mpr hN
    · refine (natDegree_lt_iff_degree_lt h0).mpr ?_
      have := degree_modByMonic_lt f hmonic
      rwa [degree_cyclotomic] at this
  -- the polynomial `r - v` vanishes at all `φ(N)` primitive roots
  set P : ℂ[X] := r.map (algebraMap ℚ ℂ) - C (∑ i, (c i : ℂ) * w i) with hPdef
  have hPzero : P = 0 := by
    refine eq_zero_of_natDegree_lt_card_of_eval_eq_zero' P (primitiveRoots N ℂ)
      (fun ρ hρ => ?_) ?_
    · have : eval ρ (r.map (algebraMap ℚ ℂ)) = aeval ρ r := by
        rw [aeval_def, eval₂_eq_eval_map]
      simp only [hPdef, eval_sub, eval_C, this, hreval ρ hρ, sub_self]
    · rw [Complex.card_primitiveRoots]
      calc P.natDegree ≤ max (r.map (algebraMap ℚ ℂ)).natDegree
              (C (∑ i, (c i : ℂ) * w i)).natDegree := natDegree_sub_le _ _
        _ ≤ max r.natDegree 0 := by
            exact max_le_max (natDegree_map_le) (le_of_eq (natDegree_C _))
        _ < Nat.totient N := by simpa using hrdeg
  refine ⟨r.coeff 0, ?_⟩
  have hmapC : r.map (algebraMap ℚ ℂ) = C (∑ i, (c i : ℂ) * w i) := by
    rw [← sub_eq_zero]; exact hPzero
  have := congrArg (fun p : ℂ[X] => p.coeff 0) hmapC
  simpa [coeff_map, eq_ratCast] using this.symm

end Descent

namespace Even

open MonRing MonGSet

variable {G : Type u} [Group G] [Fintype G]

/-! ## Species are invariant under `N_G(H)`-conjugation of the element -/

omit [Fintype G] in
/-- Transport of a species along an equality of subgroups. -/
theorem species_congr_subgroup {H K : Subgroup G} (hHK : H = K) (h : H) (k : K)
    (hv : (h : G) = (k : G)) : DRing.species H h = DRing.species K k := by
  subst hHK
  exact congrArg _ (Subtype.ext hv)

omit [Fintype G] in
/-- **Conjugating the element by a normalizer element does not change the
species.**  Specialization of `DRing.species_conj` to `g ∈ N_G(H)`, where the
conjugated subgroup is `H` itself. -/
theorem species_conj_of_mem_normalizer (H : Subgroup G) (h : H) {g : G}
    (hg : g ∈ Subgroup.normalizer H) (hmem : g * (h : G) * g⁻¹ ∈ H) :
    DRing.species H ⟨g * (h : G) * g⁻¹, hmem⟩ = DRing.species H h := by
  have hHm : H.map (MulAut.conj g).toMonoidHom = H :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hg
  have h1 : DRing.species H ⟨g * (h : G) * g⁻¹, hmem⟩ =
      DRing.species (H.map (MulAut.conj g).toMonoidHom)
        ⟨g * (h : G) * g⁻¹, Subgroup.mem_map.mpr ⟨h, h.2, rfl⟩⟩ :=
    species_congr_subgroup hHm.symm _ _ rfl
  rw [h1]
  exact RingHom.ext fun x => DRing.species_conj H h g x

omit [Fintype G] in
/-- **Fully fused ⟹ Adams-stable**: if the pair class `(H, h⁅H,H⁆)` is fully
fused, then `φ_{H,hᵃ} = φ_{H,h}` for every `a` coprime to `|G|`.  Both moves
allowed by `FullyFused` — conjugation by an element of `N_G(H)` and a shift by
`⁅H,H⁆` — leave the species unchanged. -/
theorem species_pow_eq_of_fullyFused (H : Subgroup G) (h : H)
    (hff : FullyFused H h) {a : ℕ} (ha : Nat.Coprime a (Nat.card G)) :
    DRing.species H (h ^ a) = DRing.species H h := by
  obtain ⟨g, hg, hc⟩ := hff a ha
  have hmem : g * (h : G) * g⁻¹ ∈ H := (Subgroup.mem_normalizer_iff.mp hg (h : G)).mp h.2
  have hcast : (((h ^ a : H) : G)) = ((h : G)) ^ a := by push_cast; rfl
  have hcoset : ((⟨g * (h : G) * g⁻¹, hmem⟩ : H) : G) * (((h ^ a : H) : G))⁻¹ ∈ ⁅H, H⁆ := by
    rw [hcast]; exact hc
  have h1 : DRing.species H ⟨g * (h : G) * g⁻¹, hmem⟩ = DRing.species H (h ^ a) :=
    DRing.species_congr_coset H _ _ hcoset
  rw [← h1]
  exact species_conj_of_mem_normalizer H h hg hmem

/-! ## Fully fused ⟹ every species value is rational -/

/-- **The backward Galois implication**: a fully fused pair has rational
species values. -/
theorem species_rat_of_fullyFused (H : Subgroup G) (h : H) (hff : FullyFused H h)
    (x : DRing G) : ∃ q : ℚ, DRing.species H h x = (q : ℂ) := by
  classical
  have hpx : ∀ a : ℕ, Nat.Coprime a (Nat.card G) →
      DRing.species H (h ^ a) x = DRing.species H h x :=
    fun a ha => DFunLike.congr_fun (species_pow_eq_of_fullyFused H h hff ha) x
  obtain ⟨⟨u, v⟩⟩ := x
  obtain ⟨X⟩ := u
  obtain ⟨Y⟩ := v
  change ∀ a : ℕ, Nat.Coprime a (Nat.card G) →
    (MonGSet.speciesSum (Units.coeHom ℂ) H (h ^ a) X
      - MonGSet.speciesSum (Units.coeHom ℂ) H (h ^ a) Y : ℂ)
      = MonGSet.speciesSum (Units.coeHom ℂ) H h X
        - MonGSet.speciesSum (Units.coeHom ℂ) H h Y at hpx
  change ∃ q : ℚ, (MonGSet.speciesSum (Units.coeHom ℂ) H h X
    - MonGSet.speciesSum (Units.coeHom ℂ) H h Y : ℂ) = (q : ℂ)
  set ι := (MulAction.fixedPoints H X.carrier) ⊕ (MulAction.fixedPoints H Y.carrier)
    with hι
  set c : ι → ℤ := Sum.elim (fun _ => (1 : ℤ)) (fun _ => (-1 : ℤ)) with hc
  set w : ι → ℂ := Sum.elim (fun x => (Units.coeHom ℂ) (X.fixedWeight H x h))
    (fun y => (Units.coeHom ℂ) (Y.fixedWeight H y h)) with hw
  have hwroot : ∀ i, w i ^ (Nat.card G) = 1 := by
    rintro (x | y)
    · exact fixedWeight_pow_card X H h x
    · exact fixedWeight_pow_card Y H h y
  -- the `a`-twisted combination *is* the species sum at `hᵃ`
  have key : ∀ a : ℕ, ∑ i, (c i : ℂ) * (w i) ^ a =
      MonGSet.speciesSum (Units.coeHom ℂ) H (h ^ a) X
        - MonGSet.speciesSum (Units.coeHom ℂ) H (h ^ a) Y := by
    intro a
    have hX : ∀ (Z : MonGSet G ℂˣ) (z : MulAction.fixedPoints H Z.carrier),
        (Units.coeHom ℂ) (Z.fixedWeight H z (h ^ a))
          = ((Units.coeHom ℂ) (Z.fixedWeight H z h)) ^ a := by
      intro Z z; rw [map_pow, map_pow]
    rw [Fintype.sum_sum_type]
    simp only [hc, hw, Sum.elim_inl, Sum.elim_inr, MonGSet.speciesSum]
    rw [Finset.sum_congr rfl fun x _ => hX X x, Finset.sum_congr rfl fun y _ => hX Y y]
    simp [sub_eq_add_neg, Finset.sum_neg_distrib]
  have hbase : ∑ i, (c i : ℂ) * w i =
      MonGSet.speciesSum (Units.coeHom ℂ) H h X
        - MonGSet.speciesSum (Units.coeHom ℂ) H h Y := by
    have := key 1
    simpa using this
  rw [← hbase]
  refine rat_of_pow_twist_eq (N := Nat.card G) Nat.card_pos c w hwroot ?_
  intro a ha
  rw [key a, hbase]
  exact hpx a ha

/-- **A fully fused pair is an integer point.**  Combining
`species_rat_of_fullyFused` with the integrality of species values
(`DRing.isIntegral_species`) and `ℤ` being integrally closed
(`DRing.exists_intPoint_of_species_rat`). -/
theorem exists_intPoint_of_fullyFused (H : Subgroup G) (h : H)
    (hff : FullyFused H h) :
    ∃ p : DRing G →+* ℤ, complexify (DRing G) p = DRing.species H h :=
  DRing.exists_intPoint_of_species_rat H h (species_rat_of_fullyFused H h hff)

/-- **Fully fused ⟺ rational**, the two Galois halves of item (2) of the
dictionary put together. -/
theorem fullyFused_iff_exists_intPoint (H : Subgroup G) (h : H) :
    FullyFused H h ↔
      ∃ p : DRing G →+* ℤ, complexify (DRing G) p = DRing.species H h :=
  ⟨exists_intPoint_of_fullyFused H h, fun ⟨_, hp⟩ => fullyFused_of_intPoint' H h hp⟩

/-! ## A note on `EnoughSpecies`: the cross-subgroup half is a marks statement

`LeanDring/Even/SpeciesSeparation.lean` separates two species at a *common* subgroup
`H`.  The remaining separation — species at *different* subgroups — reduces to
the table of marks, because the trivial-character column of the species table
is the marks column (`DRing.species_comp_eta`): equal species force equal mark
homomorphisms, and "marks separate subgroups up to conjugacy" is then the only
group-theoretic input.  (That statement, like Brauer's permutation lemma, is
not in Mathlib.) -/

omit [Fintype G] in
/-- **Equal species have equal marks**: if `φ_{H,h} = φ_{K,k}` then the mark
homomorphisms of `H` and `K` on the Burnside ring agree. -/
theorem mark_eq_of_species_eq (H K : Subgroup G) (h : H) (k : K)
    (hs : DRing.species H h = DRing.species K k) :
    (BurnsideRing.mark H : BurnsideRing G →+* ℤ) = BurnsideRing.mark K := by
  have hc : (Int.castRingHom ℂ).comp (BurnsideRing.mark H) =
      (Int.castRingHom ℂ).comp (BurnsideRing.mark K) := by
    rw [← DRing.species_comp_eta, ← DRing.species_comp_eta, hs]
  refine RingHom.ext fun x => ?_
  have := DFunLike.congr_fun hc x
  simp only [RingHom.comp_apply, eq_intCast] at this
  exact_mod_cast this

/-! ## The backward direction of `ConductorPairDictionary` -/

/-- There are only finitely many `ℂ`-points of `D(G)` (Dedekind bound). -/
instance finite_ringHom_complex : Finite (DRing G →+* ℂ) := by
  classical
  rw [← not_infinite_iff_finite]
  intro hinf
  haveI : Fintype (MonGSet.CharPairClass G ℂˣ) := Fintype.ofFinite _
  set n := Fintype.card (MonGSet.CharPairClass G ℂˣ) with hn
  set e := Infinite.natEmbedding (DRing G →+* ℂ) with he
  have hinj : Function.Injective (fun i : Fin (n + 1) => e (i : ℕ)) :=
    fun i j hij => Fin.val_injective (e.injective hij)
  have := card_ringHom_le (DRing.basisOfCharPairClass (G := G)) _ hinj
  rw [Fintype.card_fin] at this
  omega

/-- Hence only finitely many integer points. -/
instance finite_intPoint : Finite (DRing G →+* ℤ) :=
  Finite.of_injective (fun p : DRing G →+* ℤ => (Int.castRingHom ℂ).comp p)
    (fun p q hpq => RingHom.ext fun x => by
      have h1 := DFunLike.congr_fun hpq x
      simp only [RingHom.comp_apply, eq_intCast] at h1
      exact_mod_cast h1)

/-- **The backward direction of `ConductorPairDictionary`**, granted Müller's
conductor formula: every fully fused pair contributes an integer point of the
predicted conductor, so that conductor multiplicity is nonzero. -/
theorem conductorPairDictionary_backward (hC : ConductorAtSpecies G) (c : ℕ)
    (H : Subgroup G) (h : H) (hff : FullyFused H h)
    (hidx : c * Nat.card ↥⁅H, H⁆ = Nat.card (pairNormalizer H (h : G))) :
    conductorMultiplicity (DRing G) c ≠ 0 := by
  obtain ⟨p, hp⟩ := exists_intPoint_of_fullyFused H h hff
  have hcard : conductor (DRing G) p * Nat.card ↥⁅H, H⁆ =
      Nat.card (pairNormalizer H (h : G)) := hC H h p hp
  have hcomm : 0 < Nat.card ↥⁅H, H⁆ := Nat.card_pos
  have hceq : conductor (DRing G) p = c := by
    have : conductor (DRing G) p * Nat.card ↥⁅H, H⁆ = c * Nat.card ↥⁅H, H⁆ := by
      rw [hcard, hidx]
    exact Nat.eq_of_mul_eq_mul_right hcomm this
  exact Nat.card_ne_zero.mpr ⟨⟨⟨p, hceq⟩⟩, inferInstance⟩

/-- **The conductor dictionary for `G`**, reduced to exactly the two named
inputs `EnoughSpecies` (Brauer's permutation lemma) and `ConductorAtSpecies`
(Müller Satz 2.3.3). -/
theorem conductorPairDictionary_of (hE : EnoughSpecies G)
    (hC : ConductorAtSpecies G) (c : ℕ) :
    conductorMultiplicity (DRing G) c ≠ 0 ↔
      ∃ (H : Subgroup G) (h : H), FullyFused H h ∧
        c * Nat.card ↥⁅H, H⁆ = Nat.card (pairNormalizer H (h : G)) :=
  ⟨conductorPairDictionary_forward hE hC c,
    fun ⟨H, h, hff, hidx⟩ => conductorPairDictionary_backward hC c H h hff hidx⟩

end Even

end LeanDring

/-! ## Axiom audit -/

#print axioms LeanDring.rat_of_pow_twist_eq
#print axioms LeanDring.Even.species_congr_subgroup
#print axioms LeanDring.Even.species_conj_of_mem_normalizer
#print axioms LeanDring.Even.species_pow_eq_of_fullyFused
#print axioms LeanDring.Even.species_rat_of_fullyFused
#print axioms LeanDring.Even.exists_intPoint_of_fullyFused
#print axioms LeanDring.Even.fullyFused_iff_exists_intPoint
#print axioms LeanDring.Even.mark_eq_of_species_eq
#print axioms LeanDring.Even.conductorPairDictionary_backward
#print axioms LeanDring.Even.conductorPairDictionary_of
