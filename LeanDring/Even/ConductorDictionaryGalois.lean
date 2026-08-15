/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.Even.ConductorDictionaryProofs
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.RingTheory.RootsOfUnity.Complex

/-!
# Item (2) of the conductor dictionary: the analytic half

**EVEN-ORDER LAYER.** Inside the root module's build closure and audit:
no `sorry`, three standard axioms. The results here are
verified *implications*; their hypotheses are named `Prop`s (see §7.6 of
the paper).

`ConductorPairDictionary` splits into four items, of which
`LeanDring/Even/ConductorDictionaryProofs.lean` discharged the ring-theoretic substrate
of item (3) and the algebraic half of item (2)
(`species_adamsStable_iff`, on top of `DRing.species_comp_psi`).  What remains
is the **analytic half**: species values are
cyclotomic integers, an integer point is a *rational* species, and rationality
plus the Galois action forces the pair class to be fully fused.

This file discharges that, unconditionally except for two honestly named
hypotheses:

* **(a) coset-dependence** — `speciesSum_mul_commutator`, `species_mul_commutator`:
  `φ_{H,h}` depends only on the coset `h·H'`.  Reason: at an `H`-fixed point the
  weight is a *homomorphism* `H →* ℂˣ` into a commutative group, hence kills the
  derived subgroup of `H`.  This is the lemma the write-up flagged as
  missing; it is what makes the index set `{(H, hH')}` well defined.
* **(b) integrality** — `isIntegral_speciesSum`, `DRing.isIntegral_species`:
  every species value is an algebraic integer (a sum of `|H|`-th roots of unity).
* **(c) rational ⟹ integer** — `exists_int_of_isIntegral_rat` (ℤ is integrally
  closed), and its packaging `DRing.exists_intPoint_of_species_rat`: a species
  all of whose values are rational *is* the complexification of an honest
  integer point `D(G) →+* ℤ`.  This is the converse half of item (1).
* **(d) assembly** — `fullyFused_of_intPoint`: if an integer point `p` has
  `complexify p = φ_{H,h}` then `(H, hH')` is `FullyFused`.

the **cyclotomic Galois twist is proven**, not assumed
(`aeval_pow_eq_of_aeval_eq_rat`, `sum_pow_eq_of_sum_eq_rat`,
`Even.species_pow_eq_of_rat_value`): the twist is not built as a field
endomorphism of `ℂ` (which would need a transcendence basis) but in the only
form the assembly consumes — *a rational `ℤ`-combination of `N`-th roots of
unity is unchanged by `ζ ↦ ζᵃ`*, proven from
`minpoly ℚ ζ = Φ_N = minpoly ℚ (ζᵃ)`.

Item (d) therefore consumes exactly *one* named hypothesis:

* `SpeciesPairSeparation` — equal species at a common `H` means the two
  elements are conjugate modulo `H'` (Müller's species table is indexed by
  pair *classes*; this is item (1) of the chain).  it is a
  **theorem**, `Even.speciesPairSeparation` in `LeanDring/Even/SpeciesSeparation.lean`;
  it is kept as a named `Prop` here only so that this file stays self-contained
  (that file imports this one).

No `sorry`, no custom axiom.
-/

set_option linter.unusedFintypeInType false

namespace LeanDring

open MulAction

universe u v

namespace MonGSet

variable {G : Type u} [Group G] {A : Type v} [CommGroup A]
variable {R : Type*} [CommRing R]

/-! ## (a) Coset-dependence: the species only sees `h·⁅H,H⁆` -/

/-- The fixed-point weight character kills the derived subgroup of `H`:
it is a homomorphism into a *commutative* group. -/
theorem fixedWeight_commutator (X : MonGSet G A) (H : Subgroup G)
    (x : fixedPoints H X.carrier) {d : H} (hd : d ∈ commutator (H : Type u)) :
    X.fixedWeight H x d = 1 :=
  Abelianization.commutator_subset_ker (X.fixedWeight H x) hd

/-- **Coset-dependence of the species sum.** Multiplying the group element by
an element of the derived subgroup `⁅H,H⁆` does not change `φ_{H,h}`. -/
theorem speciesSum_mul_commutator (χ : A →* R) (H : Subgroup G) (h : H) {d : H}
    (hd : d ∈ commutator (H : Type u)) (X : MonGSet G A) :
    speciesSum χ H (h * d) X = speciesSum χ H h X := by
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [map_mul, fixedWeight_commutator X H x hd, mul_one]

end MonGSet

/-! ### The derived subgroup of `↥H` versus `⁅H, H⁆ ≤ G` -/

section CommutatorCompat

variable {G : Type u} [Group G]

/-- The derived subgroup of `↥H`, pushed into `G`, is `⁅H, H⁆`. -/
theorem map_commutator_subtype (H : Subgroup G) :
    (commutator (H : Type u)).map H.subtype = ⁅H, H⁆ := by
  rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
    H.range_subtype]

/-- Membership transfer: `h₁h₂⁻¹ ∈ ⁅H,H⁆` inside `G` is membership in the
derived subgroup of `↥H`. -/
theorem mem_commutator_of_coe {H : Subgroup G} {k : H}
    (hk : (k : G) ∈ ⁅H, H⁆) : k ∈ commutator (H : Type u) := by
  rw [← map_commutator_subtype H] at hk
  obtain ⟨e, he, hce⟩ := Subgroup.mem_map.mp hk
  have : e = k := Subtype.ext hce
  exact this ▸ he

end CommutatorCompat

namespace MonRing

open MonGSet

variable {G : Type u} [Group G] {A : Type v} [CommGroup A]
variable {R : Type*} [CommRing R]

/-- Coset-dependence, semiring level. -/
theorem speciesHom_mul_commutator (χ : A →* R) (H : Subgroup G) (h : H) {d : H}
    (hd : d ∈ commutator (H : Type u)) :
    speciesHom χ H (h * d) = speciesHom χ H h :=
  RingHom.ext (Quotient.ind fun X => speciesSum_mul_commutator χ H h hd X)

/-- **Coset-dependence of the species**, as ring homomorphisms on `B^A(G)`:
`φ_{H, h·d} = φ_{H, h}` for `d` in the derived subgroup of `H`. -/
theorem species_mul_commutator (χ : A →* R) (H : Subgroup G) (h : H) {d : H}
    (hd : d ∈ commutator (H : Type u)) :
    species χ H (h * d) = species χ H h := by
  rw [species, species, speciesHom_mul_commutator χ H h hd]

end MonRing

namespace DRing

open MonGSet MonRing

variable {G : Type u} [Group G]

/-- **The species of `D(G)` depends only on the coset `h⁅H,H⁆`** — stated in
the `G`-side language used by `LeanDring/Even/ConductorDictionary.lean`: if
`h₁h₂⁻¹ ∈ ⁅H,H⁆` then `φ_{H,h₁} = φ_{H,h₂}`. -/
theorem species_congr_coset (H : Subgroup G) (h k : H)
    (hk : ((h : G) * (k : G)⁻¹) ∈ ⁅H, H⁆) : species H h = species H k := by
  have hmem : k⁻¹ * h ∈ commutator (H : Type u) := by
    refine mem_commutator_of_coe (H := H) (k := k⁻¹ * h) ?_
    have hinv : (((k⁻¹ * h : H) : G)) = (k : G)⁻¹ * (h : G) := by simp
    rw [hinv]
    have hg : (k : G)⁻¹ ∈ Subgroup.normalizer H :=
      Subgroup.le_normalizer (inv_mem k.2)
    have := Even.conj_mem_commutator_of_mem_normalizer hg hk
    simpa [mul_assoc] using this
  have := MonRing.species_mul_commutator (Units.coeHom ℂ) H k hmem
  rw [show k * (k⁻¹ * h) = h by group] at this
  exact this

end DRing

/-! ## (b) Integrality: species values are cyclotomic integers -/

section Integrality

variable {G : Type u} [Group G]

open MonGSet

/-- A complex number of finite multiplicative order is an algebraic integer. -/
theorem isIntegral_of_pow_eq_one {z : ℂ} {n : ℕ} (hn : 0 < n) (hz : z ^ n = 1) :
    IsIntegral ℤ z :=
  IsIntegral.of_pow hn (by rw [hz]; exact isIntegral_one)

/-- Each species summand is a root of unity, hence an algebraic integer. -/
theorem isIntegral_fixedWeight [Finite G] (X : MonGSet G ℂˣ) (H : Subgroup G)
    (h : H) (x : fixedPoints H X.carrier) :
    IsIntegral ℤ ((Units.coeHom ℂ) (X.fixedWeight H x h)) := by
  have hfin : Finite (H : Type u) := inferInstance
  refine isIntegral_of_pow_eq_one (n := Nat.card (H : Type u)) Nat.card_pos ?_
  rw [← map_pow, ← map_pow, pow_card_eq_one', map_one, map_one]

/-- **(b) Integrality of species sums**: the species of a monomial `G`-set is a
sum of roots of unity, hence an algebraic integer. -/
theorem isIntegral_speciesSum [Finite G] (H : Subgroup G) (h : H)
    (X : MonGSet G ℂˣ) :
    IsIntegral ℤ (speciesSum (Units.coeHom ℂ) H h X) := by
  have : ∀ x : fixedPoints H X.carrier,
      (Units.coeHom ℂ) (X.fixedWeight H x h) ∈ integralClosure ℤ ℂ :=
    fun x => isIntegral_fixedWeight X H h x
  exact Subalgebra.sum_mem _ fun x _ => this x

/-- **(b) Integrality of species values on `D(G)`**: `φ_{H,h}(x)` is an
algebraic integer for every `x: D(G)`. -/
theorem isIntegral_speciesHom [Finite G] (H : Subgroup G) (h : H)
    (a : MonGSet.Skel G ℂˣ) :
    IsIntegral ℤ (MonRing.speciesHom (Units.coeHom ℂ) H h a) := by
  obtain ⟨X⟩ := a
  exact isIntegral_speciesSum H h X

theorem DRing.isIntegral_species [Finite G] (H : Subgroup G) (h : H)
    (x : DRing G) : IsIntegral ℤ (DRing.species H h x) := by
  obtain ⟨p⟩ := x
  change IsIntegral ℤ ((MonRing.speciesHom (Units.coeHom ℂ) H h p.1 : ℂ) -
    MonRing.speciesHom (Units.coeHom ℂ) H h p.2)
  exact (isIntegral_speciesHom H h p.1).sub (isIntegral_speciesHom H h p.2)

end Integrality

/-! ## (c) Rational algebraic integers are integers -/

section Rationality

/-- **(c)** An algebraic integer that is rational is a rational *integer*
(`ℤ` is integrally closed in `ℚ`). -/
theorem exists_int_of_isIntegral_rat {z : ℂ} (hz : IsIntegral ℤ z) {q : ℚ}
    (hq : z = (q : ℂ)) : ∃ n : ℤ, z = (n : ℂ) := by
  haveI : IsScalarTower ℤ ℚ ℂ :=
    IsScalarTower.of_algebraMap_eq (fun n => by simp)
  have hQ : IsIntegral ℤ ((algebraMap ℚ ℂ) q) := by
    simpa [hq] using hz
  have hq' : IsIntegral ℤ q :=
    hQ.tower_bot (by exact fun a b hab => by exact_mod_cast hab)
  obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.mp hq'
  refine ⟨n, ?_⟩
  rw [hq, ← hn]
  simp

end Rationality

/-! ## (b') The cyclotomic Galois twist, in the only form the assembly needs

Rather than constructing a field endomorphism of `ℂ` (which would need a
transcendence basis), we discharge the Galois input as a statement about
*sums of roots of unity*:

> if `∑ cᵢ ζᵢ` is rational, with all `ζᵢ` `N`-th roots of unity and
> `gcd(a, N) = 1`, then `∑ cᵢ ζᵢᵃ` equals the same rational number.

The proof is the minimal-polynomial form of the Galois argument: write
`ζᵢ = ζ^{kᵢ}` for a fixed primitive `N`-th root `ζ`, so the sum is `f(ζ)` for
an explicit `f ∈ ℚ[X]`; then `ζ` is a root of `f - q`, so `Φ_N = minpoly ℚ ζ`
divides `f - q`; and `ζᵃ` is again a primitive `N`-th root, hence has the same
minimal polynomial `Φ_N`, hence is also a root of `f - q`. -/

section Cyclotomic

open Polynomial

/-- **The Galois twist, minimal-polynomial form.** If a `ℚ`-polynomial takes a
rational value at a primitive `N`-th root of unity `ζ`, it takes the *same*
value at `ζᵃ` for every `a` coprime to `N`. -/
theorem aeval_pow_eq_of_aeval_eq_rat {N : ℕ} (hN : 0 < N) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ N) {a : ℕ} (ha : Nat.Coprime a N) (f : ℚ[X]) {q : ℚ}
    (hf : aeval ζ f = (q : ℂ)) : aeval (ζ ^ a) f = (q : ℂ) := by
  have hCq : (aeval (R := ℚ) (A := ℂ) ζ) (C q) = (q : ℂ) := by
    simp [aeval_C, eq_ratCast]
  have hCq' : (aeval (R := ℚ) (A := ℂ) (ζ ^ a)) (C q) = (q : ℂ) := by
    simp [aeval_C, eq_ratCast]
  have hroot : aeval ζ (f - C q) = 0 := by rw [map_sub, hf, hCq, sub_self]
  have hdvd : minpoly ℚ ζ ∣ (f - C q) := minpoly.dvd ℚ _ hroot
  have hmin : minpoly ℚ (ζ ^ a) = minpoly ℚ ζ := by
    rw [← cyclotomic_eq_minpoly_rat (hζ.pow_of_coprime a ha) hN,
      ← cyclotomic_eq_minpoly_rat hζ hN]
  obtain ⟨g, hg⟩ := hdvd
  have : aeval (ζ ^ a) (f - C q) = 0 := by
    rw [hg, map_mul, ← hmin, minpoly.aeval, zero_mul]
  rw [map_sub, hCq', sub_eq_zero] at this
  exact this

/-- **The Galois twist, root-of-unity form.** A `ℤ`-linear combination of
`N`-th roots of unity that is rational is unchanged by `ζ ↦ ζᵃ`,
`gcd(a, N) = 1`. -/
theorem sum_pow_eq_of_sum_eq_rat {N : ℕ} (hN : 0 < N) {a : ℕ}
    (ha : Nat.Coprime a N) {ι : Type*} [Fintype ι] (c : ι → ℤ) (w : ι → ℂ)
    (hw : ∀ i, w i ^ N = 1) {q : ℚ}
    (hsum : ∑ i, (c i : ℂ) * w i = (q : ℂ)) :
    ∑ i, (c i : ℂ) * (w i) ^ a = (q : ℂ) := by
  classical
  haveI : NeZero N := ⟨hN.ne'⟩
  set ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / N) with hζdef
  have hζ : IsPrimitiveRoot ζ N := Complex.isPrimitiveRoot_exp N hN.ne'
  -- write each root of unity as a power of `ζ`
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
  have hfζ : aeval ζ f = (q : ℂ) := by
    rw [hfeval]
    rw [← hsum]
    exact Finset.sum_congr rfl fun i _ => by rw [hkspec i]
  have := aeval_pow_eq_of_aeval_eq_rat hN hζ ha f hfζ
  rw [hfeval] at this
  rw [← this]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← hkspec i, ← pow_mul, ← pow_mul, Nat.mul_comm]

end Cyclotomic

namespace Even

open MonRing

universe w

variable {G : Type u} [Group G] [Fintype G]

/-- A ℚ-valued species is ℤ-valued (combining (b) and (c)). -/
theorem species_exists_int (H : Subgroup G) (h : H)
    (hrat : ∀ x : DRing G, ∃ q : ℚ, DRing.species H h x = (q : ℂ)) (x : DRing G) :
    ∃ n : ℤ, DRing.species H h x = (n : ℂ) := by
  obtain ⟨q, hq⟩ := hrat x
  exact exists_int_of_isIntegral_rat (DRing.isIntegral_species H h x) hq

/-- **The converse half of item (1)**: a species all of whose values are
rational *is* the complexification of an honest integer point
`p: D(G) →+* ℤ`. -/
theorem DRing.exists_intPoint_of_species_rat (H : Subgroup G) (h : H)
    (hrat : ∀ x : DRing G, ∃ q : ℚ, DRing.species H h x = (q : ℂ)) :
    ∃ p : DRing G →+* ℤ, complexify (DRing G) p = DRing.species H h := by
  classical
  have hex : ∀ x : DRing G, ∃ n : ℤ, DRing.species H h x = (n : ℂ) :=
    species_exists_int H h hrat
  set f : DRing G → ℤ := fun x => (hex x).choose with hf
  have hfspec : ∀ x, DRing.species H h x = ((f x : ℤ) : ℂ) := fun x => (hex x).choose_spec
  have hinj : Function.Injective (Int.cast : ℤ → ℂ) := Int.cast_injective
  have hone : f 1 = 1 := by
    apply hinj; rw [← hfspec, map_one]; norm_num
  have hzero : f 0 = 0 := by
    apply hinj; rw [← hfspec, map_zero]; norm_num
  have hadd : ∀ x y, f (x + y) = f x + f y := by
    intro x y
    apply hinj
    rw [← hfspec, map_add, hfspec x, hfspec y]
    push_cast; ring
  have hmul : ∀ x y, f (x * y) = f x * f y := by
    intro x y
    apply hinj
    rw [← hfspec, map_mul, hfspec x, hfspec y]
    push_cast; ring
  refine ⟨{ toFun := f, map_one' := hone, map_zero' := hzero,
            map_add' := hadd, map_mul' := hmul }, ?_⟩
  refine RingHom.ext fun x => ?_
  exact (hfspec x).symm

/-! ### The Galois twist on species values

`sum_pow_eq_of_sum_eq_rat` is now instantiated at the species: a species value
is a `±1`-combination of `|G|`-th roots of unity (the fixed-point weights),
and replacing `h` by `hᵃ` raises every one of them to the `a`-th power. -/

omit [Fintype G] in
/-- Each species summand is an `|G|`-th root of unity. -/
theorem fixedWeight_pow_card (X : MonGSet G ℂˣ) (H : Subgroup G) (h : H)
    (x : MulAction.fixedPoints H X.carrier) :
    ((Units.coeHom ℂ) (X.fixedWeight H x h)) ^ (Nat.card G) = 1 := by
  obtain ⟨m, hm⟩ := Subgroup.card_subgroup_dvd_card H
  have hpow : h ^ (Nat.card G) = 1 := by
    rw [hm, pow_mul, pow_card_eq_one', one_pow]
  rw [← map_pow, ← map_pow, hpow, map_one, map_one]

/-- **The Galois twist for a difference of species sums.** If
`φ_{H,h}(X) - φ_{H,h}(Y)` is rational, then it is unchanged by `h ↦ hᵃ`
for `a` coprime to `|G|`. -/
theorem speciesSum_sub_pow_eq_of_rat (H : Subgroup G) (h : H) {a : ℕ}
    (ha : Nat.Coprime a (Nat.card G)) (X Y : MonGSet G ℂˣ) {q : ℚ}
    (hq : MonGSet.speciesSum (Units.coeHom ℂ) H h X
        - MonGSet.speciesSum (Units.coeHom ℂ) H h Y = (q : ℂ)) :
    MonGSet.speciesSum (Units.coeHom ℂ) H (h ^ a) X
      - MonGSet.speciesSum (Units.coeHom ℂ) H (h ^ a) Y = (q : ℂ) := by
  classical
  set ι := (MulAction.fixedPoints H X.carrier) ⊕ (MulAction.fixedPoints H Y.carrier)
    with hι
  set c : ι → ℤ := Sum.elim (fun _ => (1 : ℤ)) (fun _ => (-1 : ℤ)) with hc
  set w : ι → ℂ := Sum.elim (fun x => (Units.coeHom ℂ) (X.fixedWeight H x h))
    (fun y => (Units.coeHom ℂ) (Y.fixedWeight H y h)) with hw
  have hwroot : ∀ i, w i ^ (Nat.card G) = 1 := by
    rintro (x | y)
    · exact fixedWeight_pow_card X H h x
    · exact fixedWeight_pow_card Y H h y
  have hsum : ∑ i, (c i : ℂ) * w i = (q : ℂ) := by
    rw [Fintype.sum_sum_type, ← hq]
    simp [hc, hw, MonGSet.speciesSum, sub_eq_add_neg, Finset.sum_neg_distrib]
  have := sum_pow_eq_of_sum_eq_rat (N := Nat.card G) Nat.card_pos ha c w hwroot hsum
  rw [Fintype.sum_sum_type] at this
  rw [← this]
  have hX : ∀ (Z : MonGSet G ℂˣ) (z : MulAction.fixedPoints H Z.carrier),
      (Units.coeHom ℂ) (Z.fixedWeight H z (h ^ a))
        = ((Units.coeHom ℂ) (Z.fixedWeight H z h)) ^ a := by
    intro Z z; rw [map_pow, map_pow]
  simp only [hc, hw, Sum.elim_inl, Sum.elim_inr, MonGSet.speciesSum]
  rw [Finset.sum_congr rfl fun x _ => hX X x, Finset.sum_congr rfl fun y _ => hX Y y]
  simp [sub_eq_add_neg, Finset.sum_neg_distrib]

/-- **The Galois twist on `D(G)`**: a rational species value is unchanged when
the group element is replaced by `hᵃ`, `gcd(a, |G|) = 1`. -/
theorem species_pow_eq_of_rat_value (H : Subgroup G) (h : H) {a : ℕ}
    (ha : Nat.Coprime a (Nat.card G)) (x : DRing G) {q : ℚ}
    (hx : DRing.species H h x = (q : ℂ)) :
    DRing.species H (h ^ a) x = (q : ℂ) := by
  obtain ⟨⟨u, v⟩⟩ := x
  obtain ⟨X⟩ := u
  obtain ⟨Y⟩ := v
  change (MonGSet.speciesSum (Units.coeHom ℂ) H h X
    - MonGSet.speciesSum (Units.coeHom ℂ) H h Y : ℂ) = (q : ℂ) at hx
  change (MonGSet.speciesSum (Units.coeHom ℂ) H (h ^ a) X
    - MonGSet.speciesSum (Units.coeHom ℂ) H (h ^ a) Y : ℂ) = (q : ℂ)
  exact speciesSum_sub_pow_eq_of_rat H h ha X Y hx

/-! ## (d) Assembly: an integer point is fully fused

Only *one* hypothesis is left here: that the species table is indexed by pair
classes.  The cyclotomic Galois input is no longer a hypothesis — it is
`species_pow_eq_of_rat_value` above. -/

/-- **Item (1): the species table is indexed by pair classes.** Two elements
of `H` with the same species are conjugate modulo `⁅H,H⁆` by an element of
`N_G(H)`.

Kept as a named `Prop` so that this file stays self-contained; it is *proven*
downstream in `LeanDring/Even/SpeciesSeparation.lean`
(`Even.speciesPairSeparation`), whence `Even.fullyFused_of_intPoint'`
is the hypothesis-free form of `fullyFused_of_intPoint` below. -/
def SpeciesPairSeparation : Prop :=
  ∀ (G : Type u) [Group G] [Fintype G] (H : Subgroup G) (h k : H),
    DRing.species H h = DRing.species H k →
      ∃ g ∈ Subgroup.normalizer H, (g * (h : G) * g⁻¹) * (k : G)⁻¹ ∈ ⁅H, H⁆

/-- **The Galois half of item (2)**: an integer point that is a species is
Adams-stable, i.e. `φ_{H,hᵃ} = φ_{H,h}` for all `a` coprime to `|G|`.

Proof: every value of `φ_{H,h}` is a rational integer, hence in particular
rational, so `species_pow_eq_of_rat_value` (the cyclotomic Galois twist in its
minimal-polynomial form) leaves it unchanged under `h ↦ hᵃ`. -/
theorem species_pow_eq_of_intPoint
    (H : Subgroup G) (h : H) {p : DRing G →+* ℤ}
    (hp : complexify (DRing G) p = DRing.species H h) {a : ℕ}
    (ha : Nat.Coprime a (Nat.card G)) :
    DRing.species H (h ^ a) = DRing.species H h := by
  refine RingHom.ext fun x => ?_
  have hval : DRing.species H h x = ((p x : ℤ) : ℂ) := by
    rw [← hp]; rfl
  have hq : DRing.species H h x = (((p x : ℚ)) : ℂ) := by
    rw [hval]; push_cast; ring
  rw [species_pow_eq_of_rat_value H h ha x hq, hval]
  push_cast; ring

/-- **Item (2), assembled**: if an integer point `p: D(G) →+* ℤ` is (the
complexification of) the species `φ_{H,h}`, then the pair class `(H, h⁅H,H⁆)`
is `FullyFused` — exactly the qualifier `ConductorPairDictionary` carries. -/
theorem fullyFused_of_intPoint
    (hsep : SpeciesPairSeparation.{u}) (H : Subgroup G) (h : H)
    {p : DRing G →+* ℤ} (hp : complexify (DRing G) p = DRing.species H h) :
    FullyFused H h := by
  intro a ha
  have hspec : DRing.species H h = DRing.species H (h ^ a) :=
    (species_pow_eq_of_intPoint H h hp ha).symm
  obtain ⟨g, hgN, hgc⟩ := hsep G H h (h ^ a) hspec
  refine ⟨g, hgN, ?_⟩
  have hcast : (((h ^ a : H) : G)) = ((h : G)) ^ a := by push_cast; rfl
  rwa [hcast] at hgc

/-- Packaged as the `AdamsStable` predicate of `LeanDring/Even/ConductorDictionaryProofs.lean`:
integer species points are Adams-stable. -/
theorem adamsStable_of_intPoint
    (H : Subgroup G) (h : H) {p : DRing G →+* ℤ}
    (hp : complexify (DRing G) p = DRing.species H h) :
    AdamsStable G (DRing.species H h) :=
  (species_adamsStable_iff H h).mpr fun _ ha =>
    species_pow_eq_of_intPoint H h hp ha

end Even

end LeanDring

/-! ## Axiom audit -/

#print axioms LeanDring.MonGSet.fixedWeight_commutator
#print axioms LeanDring.MonGSet.speciesSum_mul_commutator
#print axioms LeanDring.map_commutator_subtype
#print axioms LeanDring.mem_commutator_of_coe
#print axioms LeanDring.MonRing.species_mul_commutator
#print axioms LeanDring.DRing.species_congr_coset
#print axioms LeanDring.isIntegral_speciesSum
#print axioms LeanDring.DRing.isIntegral_species
#print axioms LeanDring.exists_int_of_isIntegral_rat
#print axioms LeanDring.Even.species_exists_int
#print axioms LeanDring.Even.DRing.exists_intPoint_of_species_rat
#print axioms LeanDring.aeval_pow_eq_of_aeval_eq_rat
#print axioms LeanDring.sum_pow_eq_of_sum_eq_rat
#print axioms LeanDring.Even.fixedWeight_pow_card
#print axioms LeanDring.Even.speciesSum_sub_pow_eq_of_rat
#print axioms LeanDring.Even.species_pow_eq_of_rat_value
#print axioms LeanDring.Even.species_pow_eq_of_intPoint
#print axioms LeanDring.Even.fullyFused_of_intPoint
#print axioms LeanDring.Even.adamsStable_of_intPoint
