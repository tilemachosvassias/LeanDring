# v_task73 — free basis (already present), the Dedekind point bound, and
# surjectivity reduced to Brauer's permutation lemma

Date 2026-08-08.  New file `lean_dring/LeanDring/Even/SpeciesSurjectivity.lean`
(~255 lines).  0 `sorry`, 0 errors, 0 warnings, no custom axiom.

## Stage (1) — free basis: ALREADY IN THE REPO

`Theory/DRing/FreeBasis.lean` (pre-existing, sorry-free) has

```lean
noncomputable def DRing.basisOfCharPairClass :
    Module.Basis (CharPairClass G ℂˣ) ℤ (DRing G)
theorem DRing.rank_dring : lift (#(CharPairClass G ℂˣ)) = lift (Module.rank ℤ (DRing G))
```

with `linearIndependent_classElt` (via the census uniqueness
`basisElt_sum_unique`, splitting an integer relation into two ℕ-parts) and
`span_classElt` (via `exists_basisElt_decomposition`).  The index is
`CharPairClass G ℂˣ = (Σ K : Subgroup G, K →* ℂˣ)/G-conjugacy`
(`Theory/DRing/Census.lean`), and `classElt c = basisElt c.out.1 c.out.2`.
The v_task72 write-up's claim that "linear independence / spanning of the
`[K,λ]` is not formalized" is **wrong**; NOTES §4bm addendum 7 records the
correction.  No new work was needed for stage (1).

## Stage (2) — counting: the point bound, and what surjectivity still needs

Proven, for an arbitrary finite free ℤ-algebra `R`:

| lemma | statement |
|---|---|
| `linearIndependent_coords` | for a ℤ-basis `b` of `R` and an injective family `p : J → (R →+* ℂ)`, the coordinate vectors `j ↦ (i ↦ p j (b i))` are ℂ-linearly independent |
| `card_ringHom_le` | `#J ≤ #ι` — **at most rank-many ℂ-points** |
| `eq_of_basis_indexed_family` | an injective family of points indexed by the basis index type is *all* the points |

`linearIndependent_coords` is Dedekind transported to the basis: a relation
among the coordinate vectors gives, for every `x = ∑ᵢ (b.repr x i) • b i`,
`∑_j c_j p_j x = ∑_i (b.repr x i) · (∑_j c_j p_j (b i)) = 0`, i.e. a relation
among the `p_j` as functions on `R`, killed by Mathlib's
`linearIndependent_monoidHom R ℂ`.  `card_ringHom_le` then follows from
`LinearIndependent.fintype_card_le_finrank` in `ι → ℂ`.

Specialization to `D(G)` (needs `Finite (CharPairClass G ℂˣ)`, proven here
from `Finite (↥K →* ℂˣ)` — Mathlib's instance via
`HasEnoughRootsOfUnity ℂ (exponent K)`):

```lean
def EnoughSpecies (G) : Prop :=
  ∃ φ : CharPairClass G ℂˣ → Σ H : Subgroup G, H,
    Function.Injective fun c => DRing.species (φ c).1 (φ c).2

theorem ringHom_eq_species_of_enough (h : EnoughSpecies G) (p : DRing G →+* ℂ) :
    ∃ (H : Subgroup G) (m : H), p = DRing.species H m
theorem intPoint_eq_species_of_enough (h : EnoughSpecies G) (p : DRing G →+* ℤ) :
    ∃ (H : Subgroup G) (m : H), (Int.castRingHom ℂ).comp p = DRing.species H m
theorem card_species_le … : Fintype.card J ≤ Nat.card (CharPairClass G ℂˣ)  -- no hypothesis
```

**So "every point is a species" is now exactly one counting statement away.**
`EnoughSpecies` says there are at least rank-many pairwise distinct species.
Its mathematical content is **Brauer's permutation lemma**: for each `K`, the
group `N_G(K)` acts on `K/K'` and on its dual `Hom(K, ℂˣ)` with the same
number of orbits, so pair classes `(K,λ)` and species classes `(H, hH')` are
equinumerous.  Brauer's permutation lemma is *not* in Mathlib (checked), and
proving it needs the character-theoretic trace argument over a field
containing enough roots of unity; that is a task of its own size.  It was not
attempted here.  Note `card_species_le` gives the ≤ direction of the same
count for free, so `EnoughSpecies` is the exact residue.

Why the briefed "species-matrix injectivity" shortcut does **not** work: the
repo has `DRing.species_injective` over **ℤ**, and an injective ℤ-linear map
`ℤⁿ → ℂᵐ` does *not* force `n ≤ m` (ℚ-independent vectors need not be
ℂ-independent).  One would need injectivity after `⊗ℂ`, which is equivalent
to the nondegeneracy of the square species matrix — i.e. to the same counting
fact.

## Stage (3) — Müller's conductor formula: NOT attempted, but wired in

`ConductorAtSpecies G : Prop` (Satz 2.3.3, division-free form)

```lean
∀ H h (p : DRing G →+* ℤ), complexify (DRing G) p = DRing.species H h →
  conductor (DRing G) p * Nat.card ↥⁅H,H⁆ = Nat.card (pairNormalizer H (h : G))
```

and

```lean
theorem conductorPairDictionary_forward (hE : EnoughSpecies G)
    (hC : ConductorAtSpecies G) (c : ℕ) (hc : conductorMultiplicity (DRing G) c ≠ 0) :
    ∃ H h, FullyFused H h ∧ c * Nat.card ↥⁅H,H⁆ = Nat.card (pairNormalizer H (h : G))
```

— the forward half of `ConductorPairDictionary` is now a two-line consequence
of `EnoughSpecies` + `ConductorAtSpecies` + the unconditional
`fullyFused_of_intPoint'` (v_task72).  The backward half additionally needs
`DRing.exists_intPoint_of_species_rat` (v_task70) fed by the rationality of a
fully fused species — the remaining piece there is "fully fused ⇒ all species
values rational", the Galois argument of `ConductorDictionaryGalois.lean` run
in reverse.

## Verification

```
taskset -c 0 lake build LeanDring.Even.SpeciesSurjectivity   # 0 err, 0 warn
taskset -c 0 lake build                                       # 4718 jobs, OK
```

Axiom audit (in-file `#print axioms`), all seven new declarations
(`linearIndependent_coords`, `card_ringHom_le`, `eq_of_basis_indexed_family`,
`ringHom_eq_species_of_enough`, `intPoint_eq_species_of_enough`,
`card_species_le`, `conductorPairDictionary_forward`):

```
[propext, Classical.choice, Quot.sound]
```

New Mathlib imports: `LinearAlgebra.Dimension.Finite`,
`LinearAlgebra.Dimension.Constructions`,
`RingTheory.RootsOfUnity.AlgebraicallyClosed`.  Exploratory layer (not
imported by the root module); build by name.

## Remaining surface of `ConductorPairDictionary`

1. `EnoughSpecies` — Brauer's permutation lemma (counting only).
2. `ConductorAtSpecies` — Müller Satz 2.3.3 (the idempotent/witness
   computation; untouched).
3. "fully fused ⇒ species values rational" for the backward direction.
