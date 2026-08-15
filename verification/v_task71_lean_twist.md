# v_task71 — `GaloisSpeciesTwist` discharged

Date 2026-08-08.  Edited file (only one):
`lean_dring/LeanDring/Even/ConductorDictionaryGalois.lean` (357 → ~470 lines).

**Result: the cyclotomic Galois hypothesis is GONE.**  `GaloisSpeciesTwist` is
deleted from the development; `species_pow_eq_of_intPoint`,
`fullyFused_of_intPoint`, `adamsStable_of_intPoint` no longer take it (or any
Galois input).  0 `sorry`, 0 errors, 0 warnings, no custom axiom.

---

## 1. Route taken — and why *not* the recommended one

v_task70 §5 recommended retargeting the species at `ℤ[ζ_N]` / `ℚ(ζ_N)` and
pulling `σ_a` out of `IsCyclotomicExtension.autEquivPow`.  That was estimated at
~300 lines and would have meant re-plumbing `MonGSet.speciesSum` (which is
hard-wired to `χ : A →* R` with `R = ℂ`) or living with `Subalgebra`-subtype
coercions everywhere.

Inspecting what the assembly actually *consumes* showed a much smaller target.
`species_pow_eq_of_intPoint` only ever applies `σ` to **one value at a time**,
and only to values that are already known rational.  So no automorphism object
is needed at all — the Galois content can be stated as an identity between two
complex numbers:

> **If `∑ᵢ cᵢ ζᵢ` (`cᵢ ∈ ℤ`, `ζᵢᴺ = 1`) is rational and `gcd(a, N) = 1`,
> then `∑ᵢ cᵢ ζᵢᵃ` is the same rational number.**

This is the Galois argument written out in minimal polynomials, and it needs
neither a cyclotomic extension as an object, nor a field embedding, nor the
extension of `σ` to `ℂ` (which would have required a transcendence basis).
~110 lines total, all in the existing file.

## 2. The proof

`ζ := exp(2πi/N)` (`Complex.isPrimitiveRoot_exp`), `N := |G|`.

| lemma | statement |
|---|---|
| **`aeval_pow_eq_of_aeval_eq_rat`** | `IsPrimitiveRoot ζ N → gcd(a,N)=1 → aeval ζ f = q → aeval (ζᵃ) f = q`  (`f : ℚ[X]`, `q : ℚ`) |
| **`sum_pow_eq_of_sum_eq_rat`** | `(∀ i, wᵢᴺ = 1) → ∑ cᵢ wᵢ = q → ∑ cᵢ wᵢᵃ = q` |

* `aeval_pow_eq_of_aeval_eq_rat`: `ζ` is a root of `f - C q`, so
  `minpoly ℚ ζ ∣ f - C q` (`minpoly.dvd`).  `ζᵃ` is again a primitive `N`-th
  root (`IsPrimitiveRoot.pow_of_coprime`), and *both* minimal polynomials equal
  `Φ_N` by `Polynomial.cyclotomic_eq_minpoly_rat`.  Hence
  `aeval (ζᵃ) (f - C q) = 0`.
  **This single equality `minpoly ℚ ζ = minpoly ℚ (ζᵃ)` is the whole Galois
  input**; it is exactly irreducibility of `Φ_N` over `ℚ`, which Mathlib has.
* `sum_pow_eq_of_sum_eq_rat`: write `wᵢ = ζ^{kᵢ}`
  (`IsPrimitiveRoot.eq_pow_of_pow_eq_one`), set `f := ∑ᵢ C cᵢ · X^{kᵢ}`, apply
  the above, and use `(ζ^{kᵢ})ᵃ = (ζᵃ)^{kᵢ}`.

## 3. Instantiation at the species

| lemma | statement |
|---|---|
| `Even.fixedWeight_pow_card` | `(χ (X.fixedWeight H x h))^{\|G\|} = 1` — via `Subgroup.card_subgroup_dvd_card` + `pow_card_eq_one'` on `↥H` |
| `Even.speciesSum_sub_pow_eq_of_rat` | `φ_{H,h}(X) − φ_{H,h}(Y) = q ∈ ℚ ⟹ φ_{H,hᵃ}(X) − φ_{H,hᵃ}(Y) = q` |
| **`Even.species_pow_eq_of_rat_value`** | `φ_{H,h}(x) = q ∈ ℚ ⟹ φ_{H,hᵃ}(x) = q`, all `x : D(G)` |

The index type is `Fix_H(X) ⊕ Fix_H(Y)` with coefficients `+1 / −1`: an element
of `D(G)` is a Grothendieck difference of two skeleton classes, each a sum of
fixed-point weights.  The step `h ↦ hᵃ` raises every weight to the `a`-th power
because `fixedWeight H x` is a **monoid hom** `↥H →* ℂˣ` (`map_pow` twice, once
for the weight, once for `Units.coeHom`).  That is the same degeneration that
(a) exploits — no new geometry.

## 4. Downstream: hypothesis removed

```
theorem species_pow_eq_of_intPoint (H) (h) {p : DRing G →+* ℤ}
    (hp : complexify (DRing G) p = DRing.species H h) {a} (ha : a.Coprime |G|) :
  DRing.species H (h ^ a) = DRing.species H h
```
— no `hgal`.  Proof: each value is `(p x : ℤ)`, cast through `ℚ`, then
`species_pow_eq_of_rat_value`.  `fullyFused_of_intPoint` now takes only
`hsep : SpeciesPairSeparation`; `adamsStable_of_intPoint` takes nothing.

Note the *earlier* simplification (v_task70) that "`σ` fixes `ℤ` automatically"
is superseded: the new lemma fixes anything **rational**, so the (c) step
"rational algebraic integer ⇒ integer" is no longer logically required for the
Galois step — it is still used to *produce* the integer point in
`DRing.exists_intPoint_of_species_rat`, so nothing was deleted.

## 5. Verification

Serial, one `taskset -c 0` process:

```
cd lean_dring
taskset -c 0 lake env lean LeanDring/Even/ConductorDictionaryGalois.lean
taskset -c 0 lake build -j1
```

0 errors, 0 warnings, 0 `sorry`.  Axiom audit — every audited declaration,
including the six new ones, reports

```
[propext, Classical.choice, Quot.sound]
```

New imports: `Mathlib.RingTheory.Polynomial.Cyclotomic.Roots`,
`Mathlib.RingTheory.RootsOfUnity.Complex`.

## 6. Remaining surface for `ConductorPairDictionary`

Down from three named Props to **two**:

1. **`SpeciesPairSeparation`** — species determine the pair class (item (1)).
   Tool: `SpeciesInjectivity` / `count_eq_of_speciesSum_eq`, already in repo.
2. **The conductor computation** `conductor = (N_G(H,hH') : H')` (Müller Satz
   2.3.3) plus "every integer point is a species" — needs the primitive
   idempotents of `D(G) ⊗ ℚ`.

Stale documentation worth a later touch-up (not edited, to avoid a downstream
rebuild): `Even/ConductorDictionaryProofs.lean` lines 256–263 still say the
analytic half "needs cyclotomic Galois theory ... is still missing".
