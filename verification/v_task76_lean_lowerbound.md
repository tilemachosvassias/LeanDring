# v_task76 — `SpeciesConductorLowerBound`: the total-species functional,
# the fusion bound, and Satz 2.3.3 (lower half) at the TOP pair

Date 2026-08-08.  `lean_dring/LeanDring/Even/ConductorAtSpecies.lean`
extended by §6–§7 (~200 lines).  0 `sorry`, 0 errors, 0 warnings, no
custom axiom; full serial `lake build` clean.

**Status: REDUCED, not discharged.**  `SpeciesConductorLowerBound` in
full generality is *not* proven; what is proven is (a) a general,
unconditional divisibility (`card_dvd_mul_fusionCount`) and (b) the
instance of `SpeciesConductorLowerBound` at the top pair `(G, gG')`,
unconditionally.

## Why the route in the task brief does not close the general case

The brief proposed expanding `x` on the `[K,λ]` basis and using
triangularity to argue that the species `φ_{H,·}` see only the `H`-block.
**The triangularity runs the other way.**  `φ_{H,h}[K,λ]` is a sum over
the *`H`-fixed cosets of `G ⧸ K`*, which are nonempty iff `H` is
subconjugate to `K`.  So the `H`-column of the species table sees the
`H`-block **and every block `K ⊋ H`**; only the blocks `K` not containing
a conjugate of `H` drop out.  Solving for the `H`-block coordinates
therefore requires having already solved every larger block — i.e. the
full Möbius inversion over the subgroup lattice, which is exactly
Müller's route through `ind^G_H`, Boltje's congruence and `μ(H,G)`.  A
one-block Fourier inversion does not exist.

(The stated coefficient `|H'|/|N_G(H,hH')|` of `[H,1]_G` in `e_{(H,hH')}`
is likewise a statement about the *inverse* species table, not about one
block.)

## What is proven instead: sum the whole `H`-column

Fix `H` and sum the species over all `h ∈ H`.  On a basis element the
inner index is a fixed coset `q ∈ (G/K)^H`, and

```lean
noncomputable def conjHom (K H : Subgroup G) (q : FixCosetOf H K) : H →* K
```

— conjugation `h ↦ s(q)⁻¹ h s(q)` is a *group homomorphism* `H →* K`.
Hence `∑_{h∈H} λ(s(q)⁻¹ h s(q))` is a character sum over the finite
group `H`, equal to `|H|` if the twisted character `λ ∘ conjHom` is
trivial and `0` otherwise (Mathlib `sum_hom_units`).  Therefore

```lean
theorem exists_sum_species_basisElt (H K : Subgroup G) [Fintype ↥H] (l : K →* ℂˣ) :
    ∃ m : ℕ, ∑ h : H, DRing.species H h (DRing.basisElt K l) = (Nat.card ↥H : ℂ) * m
theorem exists_sum_species (H : Subgroup G) [Fintype ↥H] (y : DRing G) :
    ∃ m : ℤ, ∑ h : H, DRing.species H h y = (Nat.card ↥H : ℂ) * m
```

the second by transporting the first along the additive span
(`speciesTotal : DRing G →+ ℂ`, the preimage `AddSubgroup` of
`zmultiples |H|`, and `exists_basisElt_decomposition`).  **The `H`-column
sum of the species table is an integral functional with values in
`|H|·ℤ`** — a clean, previously unrecorded integrality statement.

Feeding an isolating element into it gives the general bound:

```lean
theorem card_dvd_mul_fusionCount (H : Subgroup G) (h₀ : H) (p : DRing G →+* ℤ)
    (hp : complexify (DRing G) p = DRing.species H h₀)
    (x : DRing G) (n : ℕ) (hx : Isolates p x n) :
    Nat.card ↥H ∣ n * Nat.card {h : H // DRing.species H h = DRing.species H h₀}
```

(the column sum is `n` on the fusion class of `h₀` and `0` elsewhere, by
`Isolates`).  This is Müller's lower bound with `(H : H')` in place of
`(N_G(H,hH') : H')`: strictly weaker in general, exact when
`N_G(H,hH') = N_G(H) = H`-ish; see "sharpening" below.

## Two structural lemmas needed on the way (both new, both sorry-free)

```lean
theorem dring_ringHom_ext {f g : DRing G →+* ℂ}
    (hgen : ∀ K l, f (DRing.basisElt K l) = g (DRing.basisElt K l)) : f = g
theorem species_eq_of_mul_inv_mem_commutator (H : Subgroup G) (h k : H)
    (hk : (h : G) * (k : G)⁻¹ ∈ ⁅H, H⁆) : DRing.species H h = DRing.species H k
```

The second is the converse direction of `speciesPairSeparation`
(previously missing): `λ ∘ conjHom` is a homomorphism into the
*commutative* group `ℂˣ`, so it kills `commutator ↥H`
(`Abelianization.commutator_subset_ker` + `mem_commutator_of_coe`), and
`dring_ringHom_ext` lifts the agreement on basis elements to equality of
ring homomorphisms.

## The top pair: `SpeciesConductorLowerBound` proven there

At `H = ⊤` conjugation is trivial modulo the derived subgroup, so
`speciesPairSeparation` and `species_eq_of_mul_inv_mem_commutator`
combine into an exact description of the fusion class:

```lean
theorem species_top_eq_iff (h k : (⊤ : Subgroup G)) :
    DRing.species ⊤ h = DRing.species ⊤ k ↔ (h : G) * (k : G)⁻¹ ∈ ⁅(⊤ : Subgroup G), ⊤⁆
```

so the fusion class of `h₀` is the coset `h₀·G'`, of size `|G'|`, and
`pairNormalizer ⊤ g = ⊤` (`pairNormalizer_top`).  The fusion bound then
reads `|G| ∣ n·|G'|`:

```lean
theorem speciesConductorLowerBound_top (h₀ : (⊤ : Subgroup G))
    (p : DRing G →+* ℤ) (hp : complexify (DRing G) p = DRing.species (⊤ : Subgroup G) h₀)
    (x : DRing G) (n : ℕ) (hx : Isolates p x n) :
    Nat.card (pairNormalizer (⊤ : Subgroup G) (h₀ : G)) ∣ n * Nat.card ↥⁅(⊤ : Subgroup G), ⊤⁆
```

This is the exact instance of `SpeciesConductorLowerBound` at the top
pair, and the mirror image of v_task75's `conductorAtSpecies_trivial` at
the bottom pair.  (Note the two are genuinely different halves: at the
bottom pair the *whole* of Satz 2.3.3 is a theorem; at the top pair only
the lower-bound half is, the witness half at `(G,gG')` still being part
of `SpeciesIsolatingWitness`.)

## Sharpening path (not taken here)

1. **Compute the fusion count for general `H`.**  By
   `speciesPairSeparation` + `species_conj_of_mem_normalizer`
   (`Even/SpeciesRationality.lean`), the fusion class of `h₀` in `H` is
   the `N_G(H)`-orbit of the coset `h₀H'`, so orbit–stabilizer gives
   `#fusion = |H'| · (N_G(H) : N_G(H,h₀H'))`.  Substituted into
   `card_dvd_mul_fusionCount` this yields the unconditional
   `|H| · |N_G(H,h₀H')| ∣ n · |H'| · |N_G(H)|`, which **is** Müller's
   bound whenever `N_G(H,h₀H') = N_G(H)` (in particular at `H = ⊤`, and
   for every pair whose coset is `N_G(H)`-stable) and weaker otherwise.
   Estimated ~1 session; needs orbit–stabilizer on cosets `hH'` under
   `N_G(H)`.
2. **The genuine general case** needs the `ℤ[ζ]`-twisted column sums
   `∑_{h∈H} λ(h)⁻¹ φ_{H,h}`, whose value on `[K,μ]` is
   `|H| · #{q : μ ∘ conjHom_q = λ}` — i.e. the good-coset count of
   `card_pairNormalizer_eq_mul` — but whose integrality statement lives
   in the ring of algebraic integers, not `ℤ`.  That is Müller's own
   `D_{ℤ[ζ]}(G)` argument, and it is the same machinery the witness half
   needs.

## Verification

```
taskset -c 0 lake build LeanDring.Even.ConductorAtSpecies   # 0 err, 0 warn
taskset -c 0 lake build                                     # clean, serial
```

Axiom audit (in-file `#print axioms`) for the nine new declarations
`exists_sum_species_basisElt`, `speciesTotal_apply`, `exists_sum_species`,
`dring_ringHom_ext`, `species_eq_of_mul_inv_mem_commutator`,
`card_dvd_mul_fusionCount`, `pairNormalizer_top`, `species_top_eq_iff`,
`speciesConductorLowerBound_top`:

```
[propext, Classical.choice, Quot.sound]
```

New imports of the exploratory file: `Even.SpeciesSeparation`,
`Theory.DRing.FreeBasis`, `Mathlib.RingTheory.IntegralDomain`
(for `sum_hom_units`).  Still not imported by the root module.

## Remaining surface of `ConductorPairDictionary`

Unchanged in shape, sharper in content:

1. `SpeciesIsolatingWitness` — `ind^G_H`, the Burnside top idempotent,
   Möbius `μ(H,G)`, Boltje's congruence.  ≥ 2 sessions.  Untouched.
2. `SpeciesConductorLowerBound` — **now proven at the top pair, and
   proven in general with `(H:H')` in place of `(N_G(H,hH'):H')`.**
   What is missing is precisely the gap between `|H|` and
   `|N_G(H,h₀H')|`, i.e. the good-coset factor of
   `card_pairNormalizer_eq_mul`, reachable only through the `ℤ[ζ]`-twisted
   column sums (item 2 of the sharpening path).
