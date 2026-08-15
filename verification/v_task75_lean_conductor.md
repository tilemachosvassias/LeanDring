# v_task75 — `ConductorAtSpecies` (Müller Satz 2.3.3): `EnoughSpecies`
# eliminated, the trivial pair closed, Satz 2.3.3 split into Müller's own
# two halves

Date 2026-08-08.  New file `lean_dring/LeanDring/Even/ConductorAtSpecies.lean`
(~300 lines + audit).  0 `sorry`, 0 errors, 0 warnings, no custom axiom.
Full serial `lake build` clean.

## The headline: `EnoughSpecies` was never needed

`Theory/OddOrder/OddOrder.lean:493` already contains, sorry-free and
**with no odd-order hypothesis**,

```lean
theorem OddOrder.everyComplexPointIsSpecies (G) [Group G] [Fintype G] :
    ∀ s : DRing G →+* ℂ, ∃ (H : Subgroup G) (h : H), s = DRing.species H h
```

proved by complexifying `D(G)`, embedding it in the species algebra
(`complexTotalSpeciesAlgHom_injective`) and applying
`Subalgebra.exists_algHom_eq_eval`.  This is exactly what v_task73's
`EnoughSpecies` was introduced to supply, and what v_task73/74 declared
open pending **Brauer's permutation lemma**.  That assessment was wrong;
the counting route is simply unnecessary.  Hence

```lean
theorem ringHom_eq_species (p : DRing G →+* ℂ) : ∃ H m, p = DRing.species H m
theorem conductorPairDictionary_forward' (hC : ConductorAtSpecies G) (c : ℕ) …
theorem conductorPairDictionary' (hC : ConductorAtSpecies G) (c : ℕ) :
    conductorMultiplicity (DRing G) c ≠ 0 ↔
      ∃ H h, FullyFused H h ∧ c * Nat.card ↥⁅H,H⁆ = Nat.card (pairNormalizer H (h : G))
```

**The conductor dictionary for a fixed `G` now rests on ONE named input,
`ConductorAtSpecies`.**  (Brauer's permutation lemma remains genuinely
absent from Mathlib, but it is no longer on the critical path.)

## Satz 2.3.3 at the trivial pair — unconditional theorem

```lean
theorem intPoint_ext {p q : DRing G →+* ℤ} :
    complexify (DRing G) p = complexify (DRing G) q → p = q
theorem conductorAtSpecies_trivial (p : DRing G →+* ℤ)
    (hp : complexify (DRing G) p = DRing.species (⊥ : Subgroup G) 1) :
    conductor (DRing G) p * Nat.card ↥⁅(⊥ : Subgroup G), ⊥⁆ =
      Nat.card (pairNormalizer (⊥ : Subgroup G) 1)
```

An integer point is determined by its complexification, so `p` *is*
`trivialPoint G`; then `conductor_trivialPoint` (v_task-earlier,
`Even/MullerIsolation.lean`) plus `pairNormalizer_bot = ⊤` and
`⁅⊥,⊥⁆ = ⊥` give `|G| · 1 = |G|`.  So the `(1,1)` instance of Satz 2.3.3
is a theorem, not a hypothesis.

## Satz 2.3.3, split into Müller's two halves — and the split is exact

Müller's proof (dissertation §2.3; witness = `ind^G_H((H:H')·e^{D(H)}_{(H,hH')})`
by Lemma 2.2.2 (ii); lower bound = the coefficient of `[H,1]_G` in
`e_{(H,hH')}` being `|H'|/|N_G(H,hH')|`) has exactly two contentful
halves.  Both are now named, division-free `Prop`s:

```lean
def SpeciesIsolatingWitness (G) : Prop :=
  ∀ H (h : H) (n : ℕ), n * Nat.card ↥⁅H,H⁆ = Nat.card (pairNormalizer H (h : G)) →
    ∃ x : DRing G, DRing.species H h x = (n : ℂ) ∧
      ∀ K (k : K), DRing.species K k ≠ DRing.species H h → DRing.species K k x = 0

def SpeciesConductorLowerBound (G) : Prop :=
  ∀ H (h : H) (p : DRing G →+* ℤ), complexify (DRing G) p = DRing.species H h →
    ∀ (x : DRing G) (n : ℕ), Isolates p x n →
      Nat.card (pairNormalizer H (h : G)) ∣ n * Nat.card ↥⁅H,H⁆
```

and

```lean
theorem isolates_of_witness (hW : SpeciesIsolatingWitness G) … : ∃ x, Isolates p x n
theorem conductorAtSpecies_of (hW : SpeciesIsolatingWitness G)
    (hL : SpeciesConductorLowerBound G) : ConductorAtSpecies G
```

Two points worth recording.

1. `Isolates p x n` quantifies over **all** ring homs `D(G) →+* ℂ`, not
   over species, so a species-level witness would normally be too weak.
   `ringHom_eq_species` closes that gap — this is where the OddOrder
   spectrum theorem earns its keep, and it is why the witness half may be
   stated purely in Müller's own language.
2. The reduction is exact arithmetic, not an approximation: with
   `n := |N_G(H,hH')| / |H'|` (legitimate by
   `card_commutator_dvd_card_pairNormalizer`), `conductor_dvd` gives
   `c ∣ n` from the witness and the lower bound gives `n ∣ c` from the
   *attained* conductor element (`conductor_spec`), so `c = n` and
   `c·|H'| = |N_G(H,hH')|`.

## Supporting lemmas actually proven (not hypotheses)

### The vanishing lemma

```lean
theorem species_basisElt_gen (H K) (l : H →* ℂˣ) (k : K) :
    DRing.species K k (DRing.basisElt H l) =
      ∑ q : FixCosetOf K H, ((l (conjRepOf H K k q) : ℂˣ) : ℂ)
theorem species_basisElt_eq_zero_of_not_subconj (H K) (l) (k)
    (hsub : ∀ g : G, ∃ u : K, g⁻¹ * (u : G) * g ∉ H) :
    DRing.species K k (DRing.basisElt H l) = 0
theorem exists_conj_le_of_species_basisElt_ne_zero … :
    ∃ g : G, ∀ u : K, g⁻¹ * (u : G) * g ∈ H
```

`φ_{K,k}[H,λ] = 0` unless a conjugate of `K` lies in `H`: the index set
of Müller's formula, the `K`-fixed cosets of `G/H`, is then literally
empty (`MonGSet.sectionConj_mem` applied to `s(q)` gives the conjugation
that is assumed not to exist).  This is the triangularity that makes
Müller's witness isolate.

### The Fourier form of an integral combination

```lean
theorem species_sum_basisElt (H K) (k : K) [Fintype (H →* ℂˣ)] (c : (H →* ℂˣ) → ℤ) :
    DRing.species K k (∑ l, c l • DRing.basisElt H l) =
      ∑ q : FixCosetOf K H, ∑ l, (c l : ℂ) * ((l (conjRepOf H K k q) : ℂˣ) : ℂ)
```

— the inner sum of formula (2.8), with the coefficient function left
free.  (Note: the *delta* case `ĉ = |H:H'|·1_{hH'}`, which is what
orthogonality produces, forces `c_λ = λ(h)⁻¹`, so it is realizable only
over `ℤ[ζ]`.  This is precisely why Müller's integrality argument runs
through `D_{ℤ[ζ]}(G)`, Boltje's congruence and the Möbius function, and
why the witness half is a hypothesis here rather than a two-line
computation.)

### The arithmetic core of the coefficient computation

```lean
def IsGoodCoset (q : FixCosetOf H H) : Prop := (conjRepOf H H h q : G) * (h : G)⁻¹ ∈ ⁅H,H⁆
theorem isGoodCoset_iff_out_mem (q) : IsGoodCoset H h q ↔ (q.1.out)⁻¹ ∈ pairNormalizer H (h : G)
theorem isGoodCoset_iff_mem     (q) : IsGoodCoset H h q ↔ (q.1.out : G) ∈ pairNormalizer H (h : G)
theorem card_pairNormalizer_eq_mul :
    Nat.card (pairNormalizer H (h : G)) = Nat.card (GoodCoset H h) * Nat.card ↥H
```

**The cosets surviving the orthogonality are exactly the cosets of `H`
inside `N_G(H, hH')`**, so there are `(N_G(H,hH') : H)` of them —
whence `|H:H'| · #good = |N_G(H,hH')| / |H'|`, the conductor.  Proof:
`out_mem_pairNormalizer` (the pair normalizer contains `H`, so the choice
of representative is irrelevant), `mem_fixCosetOf_of_mem_normalizer`, and
a bijection `↥N ⧸ H.subgroupOf N ≃ GoodCoset H h` fed into Lagrange
(`Subgroup.card_eq_card_quotient_mul_card_subgroup`,
`Subgroup.subgroupOfEquivOfLe`).

## Verification

```
taskset -c 0 lake build LeanDring.Even.ConductorAtSpecies   # 0 err, 0 warn
taskset -c 0 lake build                                     # clean, serial
```

Axiom audit (in-file `#print axioms`) for all 18 new declarations —
`ringHom_eq_species`, `conductorPairDictionary_forward'`,
`conductorPairDictionary'`, `intPoint_ext`, `conductorAtSpecies_trivial`,
`species_basisElt_gen`, `species_basisElt_eq_zero_of_not_subconj`,
`exists_conj_le_of_species_basisElt_ne_zero`, `species_sum_basisElt`,
`isGoodCoset_iff_out_mem`, `isGoodCoset_iff_mem`,
`out_mem_pairNormalizer`, `mem_fixCosetOf_of_mem_normalizer`,
`goodOfMem_surjective`, `goodOfMem_eq_iff`, `card_pairNormalizer_eq_mul`,
`isolates_of_witness`, `conductorAtSpecies_of`:

```
[propext, Classical.choice, Quot.sound]
```

No new Mathlib imports (only `Even.MullerIsolation` and
`Theory.OddOrder.OddOrder`, both already in the corpus).  Exploratory
layer, not imported by the root module; build by name.

## Remaining surface

Of `ConductorPairDictionary` for a fixed `G`, one item is left, and it
now has two clearly separated sub-items:

1. `SpeciesIsolatingWitness` — Müller (2.8) + Lemma 2.2.2 (ii): the
   induction functor `ind^G_H` (not yet formalized), the Burnside top
   idempotent `e^{B(G)}_G` with its Möbius coefficients, and Boltje's
   integrality congruence (Satz 2.3.1 / [Bo04, Cor. 2.8]) together with
   Hartmann's `(N_G(H):H) ∣ m·μ(H,G)` (Lemma 2.3.2).  This is the real
   remaining work; estimate ≥ 2 sessions, mostly building `ind^G_H` and
   the Möbius function of the subgroup lattice.
2. `SpeciesConductorLowerBound` — the coefficient of `[H,1]_G` in
   `e_{(H,hH')}`.  With the free basis (`FreeBasis.lean`) and the
   vanishing lemma above, this is a coefficient extraction in a known
   basis; the missing piece is the `[H,1]`-coordinate functional and its
   compatibility with the species table.

Closed by this task: `EnoughSpecies` (redundant), the `(1,1)` case of
Satz 2.3.3, and the coset arithmetic `|N_G(H,hH')| = #good · |H|`.
