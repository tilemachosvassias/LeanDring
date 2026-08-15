/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.Theory.DRing.DecideIso
import LeanDring.Theory.DRing.SpeciesConj
import LeanDring.P5.Certificate.ConjugacyClasses.Twin1.ConjClasses

/-!
# The `SpeciesColumn` bridge: reducing the species table to conjugacy classes of `(H, hH')`

The column-side counterpart of the row-side pair classes
(`LeanDring/P5/Certificate/ConjugacyClasses/Twin1/PairClass.lean`).
`DecideIso.HasSpeciesMatch` — the
mathematical species-matching condition consumed by the certificate layer — asks
that *every* species column `(H', h')` of the target be reproduced by *some*
column `(H, h)` of the source (`bridge_species` / `hcompat`).  The column index is
`SpeciesColumn G = (H : Subgroup G) × H`, an unwieldy `Σ`-type of size
`Σ_{H ≤ G} |H|`.  Müller's table is really indexed by *conjugacy classes of pairs
`(H, hH')`* with `H' = [H,H]` — for `q = 1` there are only `2724` of them
(`speciesOrbitTotal`).  This file supplies the two invariances that collapse a
column to its class, and the abstract reduction theorem that upgrades a match on
any *complete family of representatives* to the full `HasSpeciesMatch`.

## The two moves

* `species_eq_of_abelianization_eq` — **the `hH'`-invariance** (the mathematical
  heart, and the potential surprise): `φ_{H,h} = φ_{H,h'}` whenever `hH' = h'H'`,
  i.e. `Abelianization.of h = Abelianization.of h'`.  It is *easy*: the fixed-point
  weight `μ(·, x) : H →* ℂˣ` is a **group homomorphism** into an abelian group
  (Müller's degeneration, `fixedWeight`), so it kills the commutator subgroup
  (`Abelianization.commutator_subset_ker`).  Every summand of the species sum is
  therefore unchanged when `h` is multiplied by an element of `[H,H]`.  This is the
  two-sided generalisation of `OddOrder.species_eq_one_of_trivialFibre` (the case
  `h' = 1`), and it is exactly why the species table is indexed by `hH'` rather
  than by `h`.

* `DRing.species_conj` (already proved, `SpeciesConj`) — **the conjugation
  invariance** `φ_{H^g, h^g} = φ_{H,h}`.

## The abstract reduction

* `SpeciesColsComplete cols` — a finite representative family `cols : ι → SpeciesColumn G`
  is *complete* if every column has the same species ring-hom as one of the `cols i`.
* `hasSpeciesMatch_of_reduced` — a checked match between two complete representative
  families upgrades to the full `HasSpeciesMatch G G'`.  **Only the target family
  needs to be complete**, and **no injectivity of the representatives is required**:
  the column side of `HasSpeciesMatch` is purely existential.  This is the precise
  sense in which distinctness of the `2724` columns is *not* load-bearing for a
  positive certificate.

The concrete `q = 1` instance — `SpeciesColsComplete` for the `2724` orbit
representatives — is proved in `Twin1/SpeciesComplete.lean` as
`speciesColsComplete_coordinate1`.  Its three steps (conjugate to `reps r`;
reduce `h` mod `H'` to a transversal position; normalise to the orbit
representative) are the two moves above fed by the certified data of
`Twin1/SpeciesLink.lean` and `Twin1/SpeciesOrbits.lean`.  The first step is
discharged here as `species_col_conj_to_reps`.
-/

namespace LeanDring.DRing

open MonGSet MonRing MulAction SpeciesTableEncoding

universe u

/-! ## The `hH'`-invariance -/

variable {G : Type u} [Group G]

/-- **The `hH'`-invariance of species** (Müller: the species table is indexed by
`(H, hH')`).  If `h` and `h'` have the same image in the abelianization
`H^ab = H/[H,H]` — equivalently `hH' = h'H'` — then `φ_{H,h} = φ_{H,h'}` on all of
`D(G)`.  Proof: at every `H`-fixed point `x`, the weight `μ(·,x) : H →* ℂˣ` is a
homomorphism to an abelian group, hence trivial on `[H,H]`
(`Abelianization.commutator_subset_ker`); so `μ(h,x) = μ(h',x)` summand-by-summand. -/
theorem species_eq_of_abelianization_eq (H : Subgroup G) (h h' : H)
    (hab : Abelianization.of h = Abelianization.of h') :
    species H h = species H h' := by
  refine GrothendieckRing.hom_ext fun a => ?_
  obtain ⟨X⟩ := a
  simp only [DRing.species, MonRing.species, GrothendieckRing.lift_of]
  change MonGSet.speciesSum (Units.coeHom ℂ) H h X =
    MonGSet.speciesSum (Units.coeHom ℂ) H h' X
  refine Finset.sum_congr rfl fun x _ => ?_
  have hcomm : (h : H) * (h' : H)⁻¹ ∈ commutator H := by
    rw [← Abelianization.ker_of, MonoidHom.mem_ker, map_mul, map_inv, hab]
    exact mul_inv_cancel _
  have hker := Abelianization.commutator_subset_ker (X.fixedWeight H x) hcomm
  rw [MonoidHom.mem_ker, map_mul, map_inv] at hker
  rw [mul_inv_eq_one.mp hker]

/-! ## The conjugation move as a `SpeciesColumn` reduction -/

/-- **The conjugation move, column form.**  If `g` conjugates `K` onto `H`
(`K^g = H`) and the element `h : H` is `g·k·g⁻¹`, then the columns `(H, h)` and
`(K, k)` carry the same species ring homomorphism.  Repackages `DRing.species_conj`
so the target subgroup/element is an arbitrary `(H, h)` rather than the syntactic
conjugate `K.map (conj g)`. -/
theorem species_of_conjSub (K : Subgroup G) (k : K) (g : G) {H : Subgroup G}
    (hg : K.map (MulAut.conj g).toMonoidHom = H) (h : H)
    (hval : (h : G) = g * (k : G) * g⁻¹) :
    species H h = species K k := by
  subst hg
  ext x
  rw [← species_conj K k g x]
  exact congrArg (fun z : ↥(K.map (MulAut.conj g).toMonoidHom) =>
    species (K.map (MulAut.conj g).toMonoidHom) z x) (Subtype.ext hval)

/-! ## The abstract class-reduced column bridge -/

/-- **Column completeness.** A representative family `cols : ι → SpeciesColumn G`
is *complete* if every species column `(H, h)` has the same species ring
homomorphism `D(G) →+* ℂ` as one of the representatives `cols i`.  (For `G` finite
this holds for the `2724` orbit representatives; see the file docstring.) -/
def SpeciesColsComplete {ι : Type*} (cols : ι → SpeciesColumn G) : Prop :=
  ∀ col : SpeciesColumn G, ∃ i : ι,
    species col.1 col.2 = species (cols i).1 (cols i).2

variable {G' : Type u} [Group G'] [Fintype G] [Fintype G']

/-- **The class-reduced column bridge.**  Suppose the target columns are covered by
a complete representative family `colsG'` and there is a row bijection `σ` under
which every *representative* column of `G'` is reproduced by some column of `G`.
Then the full `HasSpeciesMatch G G'` holds — the condition the certificate layer
(`Bridge.nonempty_dringEquiv_of_speciesMatch`, `DecideIso`) actually consumes.

Only the *target* family need be complete, and no injectivity of either family is
used: the column side of `HasSpeciesMatch` is purely existential, so a positive
certificate never needs the `2724` columns to be pairwise distinct. -/
theorem hasSpeciesMatch_of_reduced {ι ι' : Type*}
    (colsG : ι → SpeciesColumn G) (colsG' : ι' → SpeciesColumn G')
    (hcompl : SpeciesColsComplete colsG')
    (σ : CharPairClass G ℂˣ ≃ CharPairClass G' ℂˣ)
    (hmatch : ∀ i' : ι', ∃ i : ι, ∀ c : CharPairClass G ℂˣ,
        species (colsG' i').1 (colsG' i').2 (classElt (σ c)) =
          species (colsG i).1 (colsG i).2 (classElt c)) :
    HasSpeciesMatch G G' := by
  refine ⟨σ, fun H' h' => ?_⟩
  obtain ⟨i', hi'⟩ := hcompl ⟨H', h'⟩
  obtain ⟨i, hi⟩ := hmatch i'
  refine ⟨(colsG i).1, (colsG i).2, fun c => ?_⟩
  have e1 := DFunLike.congr_fun hi' (classElt (σ c))
  rw [e1]
  exact hi c

/-- Capstone: a class-reduced match yields an abstract D-ring isomorphism, without
enumerating the full column `Σ`-type. -/
theorem nonempty_dringEquiv_of_reduced {ι ι' : Type*}
    (colsG : ι → SpeciesColumn G) (colsG' : ι' → SpeciesColumn G')
    (hcompl : SpeciesColsComplete colsG')
    (σ : CharPairClass G ℂˣ ≃ CharPairClass G' ℂˣ)
    (hmatch : ∀ i' : ι', ∃ i : ι, ∀ c : CharPairClass G ℂˣ,
        species (colsG' i').1 (colsG' i').2 (classElt (σ c)) =
          species (colsG i).1 (colsG i).2 (classElt c)) :
    Nonempty (DRing G ≃+* DRing G') := by
  obtain ⟨σ', hσ'⟩ := hasSpeciesMatch_of_reduced colsG colsG' hcompl σ hmatch
  exact nonempty_dringEquiv_of_speciesMatch σ' hσ'

/-! ## Concrete step 1 (`q = 1`): every column conjugates onto a class representative

The first of the three concrete reductions that assemble `SpeciesColsComplete` for
`Coordinate 1`.  Uses `reps_complete` (every subgroup is
conjugate to one of the `148` `reps r`) and the conjugation move above.  Steps 2
(reduce `h` mod `H'` to a `transData` transversal position, via
`species_eq_of_abelianization_eq` + transversal completeness) and 3 (normalise to
the orbit representative, via `speciesOrbit_semantically_closed` + `cosetActOK`)
are carried out in `Twin1/SpeciesComplete.lean`. -/

open P5Presentation (reps reps_complete conjSub)

/-- **Concrete step 1.** Every species column `(H, h)` of `Coordinate 1` has the same
species as a column `(reps r, h')` on one of the `148` subgroup-class
representatives. -/
theorem species_col_conj_to_reps (H : Subgroup (P5Presentation.Coordinate 1))
    (h : H) :
    ∃ (r : Fin 148) (h' : reps r), species H h = species (reps r) h' := by
  obtain ⟨r, g, hg⟩ := reps_complete H
  have hmem : g⁻¹ * (h : P5Presentation.Coordinate 1) * g ∈ reps r := by
    have hh : (h : P5Presentation.Coordinate 1) ∈ conjSub g (reps r) := by
      rw [hg]; exact h.2
    rw [conjSub, Subgroup.mem_map] at hh
    obtain ⟨y, hy, hyeq⟩ := hh
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hyeq
    have hyv : g⁻¹ * (h : P5Presentation.Coordinate 1) * g = y := by rw [← hyeq]; group
    rw [hyv]; exact hy
  refine ⟨r, ⟨g⁻¹ * (h : P5Presentation.Coordinate 1) * g, hmem⟩, ?_⟩
  refine species_of_conjSub (reps r) ⟨g⁻¹ * (h : P5Presentation.Coordinate 1) * g, hmem⟩
    g hg h ?_
  change (h : P5Presentation.Coordinate 1)
    = g * (g⁻¹ * (h : P5Presentation.Coordinate 1) * g) * g⁻¹
  group

end LeanDring.DRing
