/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.Theory.DRing.FreeBasis
import LeanDring.Theory.DRing.SpeciesInjectivity
import LeanDring.Even.SpeciesSeparation
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-!
# Counting the points of `D(G)`: how many ring homs `D(G) →+* ℂ` are there?

The linear-algebra core of the missing half of `ConductorPairDictionary`
("every point of `D(G)` is a species").

Two ingredients are already in the repository:

* `DRing.basisOfCharPairClass: Basis (CharPairClass G ℂˣ) ℤ (DRing G)` —
  the free `ℤ`-basis `[K, λ]` (`LeanDring/Theory/DRing/FreeBasis.lean`, Satz 2.1.1);
* Dedekind's linear independence of characters (Mathlib
  `linearIndependent_monoidHom`).

Combining them gives the **upper bound**

`#{ring homs D(G) →+* ℂ} ≤ rank D(G) = #{(K, λ)}/G` (`card_ringHom_le`),

and hence: *any* injective family of species indexed by the pair classes
already exhausts `Hom(D(G), ℂ)` (`ringHom_eq_species_of_enough`,
`EnoughSpecies`). What is left over is the purely combinatorial statement
`EnoughSpecies`: there are at least `rank D(G)` pairwise distinct species,
i.e. the count of species classes `(H, hH')` is at least the count of
character-pair classes `(K, λ)`. (These two counts are equal — for each `K`
the linear characters of `K` and the elements of `K/K'` are in
`N_G(K)`-equivariantly equinumerous *orbit-wise* by Brauer's permutation
lemma — but that is not formalized here.)

This file is inside the root module's build closure, via
`LeanDring/Even.lean`: `EnoughSpecies` and `ConductorAtSpecies` are the
named `Prop`s that `LeanDring/Even/SpeciesRationality.lean` consumes, and
`conductorPairDictionary_forward` is one half of the dictionary it
assembles.
-/

namespace LeanDring

namespace Even

open Module

universe u

/-! ## The Dedekind bound for a finite free `ℤ`-algebra -/

section Counting

variable {R : Type u} [CommRing R]

/-- **Coordinates of distinct points are `ℂ`-linearly independent.**
If `b` is a `ℤ`-basis of `R` and `p` an injective family of ring
homomorphisms `R →+* ℂ`, then the coordinate vectors `i ↦ p j (b i)` are
linearly independent over `ℂ`. (Dedekind's independence of characters,
transported to the basis: a relation between the coordinate vectors is a
relation between the `p j` as functions on `R`, because every element of
`R` is a `ℤ`-combination of basis vectors.) -/
theorem linearIndependent_coords {ι : Type*} (b : Module.Basis ι ℤ R)
    {J : Type*} (p : J → (R →+* ℂ)) (hinj : Function.Injective p) :
    LinearIndependent ℂ (fun (j : J) (i : ι) => p j (b i)) := by
  classical
  -- Dedekind: distinct monoid homs `R →* ℂ` are independent
  have hmon : Function.Injective (fun j : J => ((p j : R →* ℂ))) := by
    intro x y hxy
    exact hinj (RingHom.ext fun r => DFunLike.congr_fun hxy r)
  have hLI : LinearIndependent ℂ (fun j : J => ((p j : R →* ℂ) : R → ℂ)) :=
    (linearIndependent_monoidHom R ℂ).comp _ hmon
  rw [linearIndependent_iff'] at hLI ⊢
  intro S c hc j hj
  refine hLI S c ?_ j hj
  funext x
  have hcoord : ∀ j : J, p j x =
      ∑ i ∈ (b.repr x).support, ((b.repr x i : ℤ) : ℂ) * p j (b i) := by
    intro j
    conv_lhs => rw [← b.linearCombination_repr x]
    rw [Finsupp.linearCombination_apply, Finsupp.sum, map_sum]
    exact Finset.sum_congr rfl fun i _ => by
      rw [map_zsmul]; simp [zsmul_eq_mul]
  have hc' : ∀ i : ι, ∑ j ∈ S, c j * p j (b i) = 0 := by
    intro i
    have := congrFun hc i
    simpa using this
  have : ∑ j ∈ S, c j * p j x = 0 := by
    calc ∑ j ∈ S, c j * p j x
        = ∑ j ∈ S, ∑ i ∈ (b.repr x).support,
            ((b.repr x i : ℤ) : ℂ) * (c j * p j (b i)) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [hcoord j, Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => by ring
      _ = ∑ i ∈ (b.repr x).support,
            ((b.repr x i : ℤ) : ℂ) * ∑ j ∈ S, c j * p j (b i) := by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun i _ => by rw [Finset.mul_sum]
      _ = 0 := by
          refine Finset.sum_eq_zero fun i _ => ?_
          rw [hc' i, mul_zero]
  simpa using this

/-- **The Dedekind bound**: a finite free `ℤ`-algebra of rank `n` has at
most `n` ring homomorphisms to `ℂ`. -/
theorem card_ringHom_le {ι : Type*} [Fintype ι] (b : Module.Basis ι ℤ R)
    {J : Type*} [Fintype J] (p : J → (R →+* ℂ)) (hinj : Function.Injective p) :
    Fintype.card J ≤ Fintype.card ι := by
  have h := (linearIndependent_coords b p hinj).fintype_card_le_finrank
  rwa [Module.finrank_fintype_fun_eq_card] at h

set_option linter.unusedFintypeInType false in
/-- **Exhaustion**: an injective family of points indexed by a basis index
type is *all* the points. -/
theorem eq_of_basis_indexed_family {ι : Type*} [Fintype ι]
    (b : Module.Basis ι ℤ R) (φ : ι → (R →+* ℂ)) (hφ : Function.Injective φ)
    (p : R →+* ℂ) : ∃ i, p = φ i := by
  by_contra hcon
  simp only [not_exists] at hcon
  set q : Option ι → (R →+* ℂ) := fun o => o.elim p φ with hq
  have hqinj : Function.Injective q := by
    rintro (_ | x) (_ | y) h
    · rfl
    · exact absurd h (hcon y)
    · exact absurd h.symm (hcon x)
    · exact congrArg some (hφ h)
  have := card_ringHom_le b q hqinj
  rw [Fintype.card_option] at this
  omega

end Counting

/-! ## Specialization to `D(G)` -/

section DRing

variable (G : Type u) [Group G] [Fintype G]

set_option linter.unusedFintypeInType false in
instance finite_charPair : Finite (MonGSet.CharPair G ℂˣ) := by
  haveI : ∀ K : Subgroup G, Finite (↥K →* ℂˣ) := fun K => by
    haveI : Finite ↥K := Subtype.finite
    infer_instance
  infer_instance

set_option linter.unusedFintypeInType false in
set_option linter.unusedFintypeInType false in
instance finite_charPairClass : Finite (MonGSet.CharPairClass G ℂˣ) :=
  Quotient.finite _

/-- **There are at least `rank D(G)` distinct species**: an injection from
the character-pair classes into the species of `G`.

This is the one remaining ingredient of "every point of `D(G)` is a
species" (the second half of `ConductorPairDictionary`). Its content is
Brauer's permutation lemma applied to the `N_G(K)`-action on `K/K'` and on
its dual `Hom(K, ℂˣ)`: the two orbit counts agree, so pair classes
`(K, λ)` and species classes `(H, hH')` are equinumerous. Injectivity of
the resulting family of species is then `DRing.species_injective`-free —
it is exactly the separation statement `Even.speciesPairSeparation`
supplies at a fixed subgroup. -/
def EnoughSpecies : Prop :=
  ∃ φ : MonGSet.CharPairClass G ℂˣ → Σ H : Subgroup G, H,
    Function.Injective fun c => DRing.species (φ c).1 (φ c).2

variable {G}

set_option linter.unusedFintypeInType false in
/-- **Every point of `D(G)` is a species**, granted `EnoughSpecies`.
This is the surjectivity half of the species dictionary: the map
`(H, hH') ↦ φ_{H,h}` from pair classes onto `Hom(D(G), ℂ)` is onto. -/
theorem ringHom_eq_species_of_enough (h : EnoughSpecies G) (p : DRing G →+* ℂ) :
    ∃ (H : Subgroup G) (m : H), p = DRing.species H m := by
  classical
  obtain ⟨φ, hφ⟩ := h
  haveI : Fintype (MonGSet.CharPairClass G ℂˣ) := Fintype.ofFinite _
  obtain ⟨c, hc⟩ := eq_of_basis_indexed_family DRing.basisOfCharPairClass
    (fun c => DRing.species (φ c).1 (φ c).2) hφ p
  exact ⟨(φ c).1, (φ c).2, hc⟩

set_option linter.unusedFintypeInType false in
/-- **Every integer point of `D(G)` is a species**, granted
`EnoughSpecies`: the complexification of `p: D(G) →+* ℤ` is a species.
This is precisely the input `Even.fullyFused_of_intPoint'` and
`Even.adamsStable_of_intPoint` consume. -/
theorem intPoint_eq_species_of_enough (h : EnoughSpecies G) (p : DRing G →+* ℤ) :
    ∃ (H : Subgroup G) (m : H),
      (Int.castRingHom ℂ).comp p = DRing.species H m :=
  ringHom_eq_species_of_enough h _

set_option linter.unusedFintypeInType false in
/-- Conversely — with no hypothesis — there are **at most** `rank D(G)`
distinct species: any injective family of species is indexed by at most
the pair classes. -/
theorem card_species_le {J : Type*} [Fintype J] (ψ : J → Σ H : Subgroup G, H)
    (hψ : Function.Injective fun j => DRing.species (ψ j).1 (ψ j).2) :
    Fintype.card J ≤ Nat.card (MonGSet.CharPairClass G ℂˣ) := by
  classical
  haveI : Fintype (MonGSet.CharPairClass G ℂˣ) := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card]
  exact card_ringHom_le DRing.basisOfCharPairClass _ hψ

end DRing

/-! ## What is left of the forward direction of `ConductorPairDictionary` -/

section Dictionary

variable (G : Type u) [Group G] [Fintype G]

/-- **Müller Satz 2.3.3, as a named Prop**: the conductor of an integer
point whose complexification is the species `φ_{H,h}` is the index
`(N_G(H, hH'): H')`, in division-free form. -/
def ConductorAtSpecies : Prop :=
  ∀ (H : Subgroup G) (h : H) (p : DRing G →+* ℤ),
    complexify (DRing G) p = DRing.species H h →
      conductor (DRing G) p * Nat.card ↥⁅H, H⁆ =
        Nat.card (pairNormalizer H (h : G))

variable {G}

set_option linter.unusedFintypeInType false in
/-- **The forward direction of `ConductorPairDictionary` follows from
`EnoughSpecies` + `ConductorAtSpecies`.** Every conductor value is the
index of a fully fused pair: the integer point realizing the conductor is
a species by `EnoughSpecies`, its pair is fully fused unconditionally
(`fullyFused_of_intPoint'`), and its conductor is the index by
`ConductorAtSpecies`. -/
theorem conductorPairDictionary_forward (hE : EnoughSpecies G)
    (hC : ConductorAtSpecies G) (c : ℕ)
    (hc : conductorMultiplicity (DRing G) c ≠ 0) :
    ∃ (H : Subgroup G) (h : H), FullyFused H h ∧
      c * Nat.card ↥⁅H, H⁆ = Nat.card (pairNormalizer H (h : G)) := by
  obtain ⟨⟨p, hp⟩⟩ := (Nat.card_ne_zero.mp hc).1
  obtain ⟨H, h, hHh⟩ := ringHom_eq_species_of_enough hE (complexify (DRing G) p)
  exact ⟨H, h, fullyFused_of_intPoint' H h hHh, by rw [← hp]; exact hC H h p hHh⟩

end Dictionary

end Even

end LeanDring

/-! ## Axiom audit -/

#print axioms LeanDring.Even.linearIndependent_coords
#print axioms LeanDring.Even.card_ringHom_le
#print axioms LeanDring.Even.eq_of_basis_indexed_family
#print axioms LeanDring.Even.ringHom_eq_species_of_enough
#print axioms LeanDring.Even.intPoint_eq_species_of_enough
#print axioms LeanDring.Even.card_species_le
#print axioms LeanDring.Even.conductorPairDictionary_forward
