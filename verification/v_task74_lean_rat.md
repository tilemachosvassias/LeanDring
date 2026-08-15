# v_task74 — fully fused ⟹ rational: the backward half of the conductor
# dictionary; `EnoughSpecies` re-examined

Date 2026-08-08.  New file `lean_dring/LeanDring/Even/SpeciesRationality.lean`
(~360 lines).  0 `sorry`, 0 errors, 0 warnings, no custom axiom.

## (c) Fully fused ⟹ species values rational — **DONE**

### The analytic core, without Galois theory

```lean
theorem rat_of_pow_twist_eq {N : ℕ} (hN : 0 < N) {ι} [Fintype ι]
    (c : ι → ℤ) (w : ι → ℂ) (hw : ∀ i, w i ^ N = 1)
    (hinv : ∀ a : ℕ, Nat.Coprime a N →
      ∑ i, (c i : ℂ) * (w i) ^ a = ∑ i, (c i : ℂ) * w i) :
    ∃ q : ℚ, ∑ i, (c i : ℂ) * w i = (q : ℂ)
```

This is the exact converse of v_task71's `sum_pow_eq_of_sum_eq_rat`.  No
cyclotomic field object, no `IsGalois`, no fixed-field theorem, and no
Ramanujan/Möbius trace computation is needed.  Proof:

1. `ζ = exp(2πi/N)`, write `w i = ζ^{k i}`, so the value is `aeval ζ f` for
   `f = ∑ᵢ C(cᵢ) X^{kᵢ} ∈ ℚ[X]`.
2. Every primitive `N`-th root `ρ` is `ζᵃ` with `gcd(a,N)=1`
   (`IsPrimitiveRoot.eq_pow_of_pow_eq_one` + `IsPrimitiveRoot.pow_iff_coprime`),
   so the twist hypothesis says `aeval ρ f = v` for **all** `ρ ∈ primitiveRoots N ℂ`.
3. Replace `f` by `r = f %ₘ cyclotomic N ℚ`; `aeval ρ (cyclotomic N ℚ) = 0`
   (`map_cyclotomic` + `isRoot_cyclotomic_iff`), so `aeval ρ r = v` too, and
   `degree r < degree Φ_N = φ(N)` (`degree_modByMonic_lt`, `degree_cyclotomic`).
4. `r.map (algebraMap ℚ ℂ) - C v` has `natDegree < φ(N) =
   #(primitiveRoots N ℂ)` (`Complex.card_primitiveRoots`) and vanishes on that
   whole finset, hence is `0`
   (`Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero'`).
5. Comparing constant coefficients: `v = algebraMap ℚ ℂ (r.coeff 0)`. ∎

### The group-theoretic input

`FullyFused H h` (`Even/ConductorDictionary.lean`) gives, for each `a` coprime
to `|G|`, some `g ∈ N_G(H)` with `(g h g⁻¹)(hᵃ)⁻¹ ∈ ⁅H,H⁆`.  Both moves are
species-invariant:

| lemma | content |
|---|---|
| `species_congr_subgroup` | transport of `DRing.species` along `H = K` |
| `species_conj_of_mem_normalizer` | `DRing.species_conj` (`Theory/DRing/SpeciesConj.lean`) specialized via `Subgroup.mem_normalizer_iff_map_conj_eq`, so the conjugated subgroup is `H` itself |
| `DRing.species_congr_coset` | v_task71: the `⁅H,H⁆`-shift |

whence `species_pow_eq_of_fullyFused : FullyFused H h → φ_{H,hᵃ} = φ_{H,h}`.

### Assembled

```lean
theorem species_rat_of_fullyFused (H) (h : H) (hff : FullyFused H h) (x : DRing G) :
    ∃ q : ℚ, DRing.species H h x = (q : ℂ)
theorem exists_intPoint_of_fullyFused (H) (h : H) (hff : FullyFused H h) :
    ∃ p : DRing G →+* ℤ, complexify (DRing G) p = DRing.species H h
theorem fullyFused_iff_exists_intPoint (H) (h : H) :
    FullyFused H h ↔ ∃ p : DRing G →+* ℤ, complexify (DRing G) p = DRing.species H h
```

The `⟸` direction is v_task72's `fullyFused_of_intPoint'`; the `⟹` direction
is new and runs through `DRing.exists_intPoint_of_species_rat` (v_task71:
integrality + `ℤ` integrally closed).  **Fully fused and rational are now
equivalent, formally.**

### The backward dictionary direction

```lean
instance finite_ringHom_complex : Finite (DRing G →+* ℂ)   -- from card_ringHom_le
instance finite_intPoint : Finite (DRing G →+* ℤ)

theorem conductorPairDictionary_backward (hC : ConductorAtSpecies G) (c : ℕ)
    (H) (h : H) (hff : FullyFused H h)
    (hidx : c * Nat.card ↥⁅H,H⁆ = Nat.card (pairNormalizer H (h : G))) :
    conductorMultiplicity (DRing G) c ≠ 0

theorem conductorPairDictionary_of (hE : EnoughSpecies G) (hC : ConductorAtSpecies G)
    (c : ℕ) : conductorMultiplicity (DRing G) c ≠ 0 ↔
      ∃ H h, FullyFused H h ∧ c * Nat.card ↥⁅H,H⁆ = Nat.card (pairNormalizer H (h : G))
```

The finiteness instances are needed because `conductorMultiplicity` is a
`Nat.card`: `Nat.card_ne_zero` wants nonempty *and* finite.  Finiteness of
`Hom(D(G), ℂ)` follows from v_task73's Dedekind bound (an infinite type would
give `rank + 1` distinct points).

**So the whole dictionary for a fixed `G` now follows from exactly two named
inputs: `EnoughSpecies` and `ConductorAtSpecies`.**

## (a) `EnoughSpecies` — re-examined, still open

The briefed shortcut does **not** apply.  `DRing.species_injective`
(`Theory/DRing/SpeciesInjectivity.lean`) reads

```lean
Function.Injective (fun x : DRing G => fun (H : Subgroup G) (m : H) => species H m x)
```

— injectivity in the *element* `x` (the ghost-ring embedding `D(G) ↪ ∏ℂ`), not
an injection of pair classes into ring homomorphisms.  `EnoughSpecies` needs
the latter, so the two statements do not match and the one-line discharge is
not available; v_task73's assessment stands.

One structural reduction was added.  The separation needed for `EnoughSpecies`
splits into a same-`H` half — **proven**, `Even.speciesPairSeparation`
(v_task72) — and a cross-subgroup half, which is a statement about *marks*:

```lean
theorem mark_eq_of_species_eq (H K : Subgroup G) (h : H) (k : K)
    (hs : DRing.species H h = DRing.species K k) :
    (BurnsideRing.mark H : BurnsideRing G →+* ℤ) = BurnsideRing.mark K
```

(immediate from the trivial-character column `DRing.species_comp_eta`).  What
remains for that half is the classical "marks separate subgroups up to
conjugacy" — note the repo's `BurnsideRing.mark_injective` is again
injectivity in the *element*, not in the subgroup — and, for the count itself,
Brauer's permutation lemma.  Neither is in Mathlib.  Not attempted.

## Verification

```
taskset -c 0 lake build LeanDring.Even.SpeciesRationality   # 0 err, 0 warn
taskset -c 0 lake build                                     # clean, serial
```

Axiom audit (in-file `#print axioms`) for all ten new declarations
(`rat_of_pow_twist_eq`, `species_congr_subgroup`,
`species_conj_of_mem_normalizer`, `species_pow_eq_of_fullyFused`,
`species_rat_of_fullyFused`, `exists_intPoint_of_fullyFused`,
`fullyFused_iff_exists_intPoint`, `mark_eq_of_species_eq`,
`conductorPairDictionary_backward`, `conductorPairDictionary_of`):

```
[propext, Classical.choice, Quot.sound]
```

No new Mathlib imports (the file imports only `Even/SpeciesSurjectivity.lean`;
the cyclotomic machinery was already pulled in by
`Even/ConductorDictionaryGalois.lean`).  Exploratory layer, not imported by
the root module; build by name.

## Remaining surface of `ConductorPairDictionary`

1. `EnoughSpecies` — Brauer's permutation lemma (counting), plus "marks
   separate subgroups" for the cross-subgroup separation.
2. `ConductorAtSpecies` — Müller Satz 2.3.3 (untouched).

Item 3 of the v_task73 list ("fully fused ⇒ species values rational") is
**closed**.
