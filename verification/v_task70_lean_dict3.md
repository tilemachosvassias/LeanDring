# v_task70 — the conductor dictionary, part 3: item (2), the analytic half

Date 2026-08-08.  New file:
`lean_dring/LeanDring/Even/ConductorDictionaryGalois.lean` (~340 lines),
purely additive — no pre-existing file was edited, so
`ConductorDictionary`, `ConductorDictionaryProofs`, `BCSeparation`,
`ATSeparation`, `OrderTransfer` are untouched.

Checked serially, one `taskset -c 0` process:

```
cd lean_dring
taskset -c 0 lake env lean LeanDring/Even/ConductorDictionaryGalois.lean
taskset -c 0 lake build LeanDring.Even.ConductorDictionary \
  LeanDring.Even.ConductorDictionaryProofs LeanDring.Even.BCSeparation \
  LeanDring.Even.ATSeparation LeanDring.Even.OrderTransfer
```

**0 errors, 0 warnings, 0 `sorry`.**  Every audited declaration:
`[propext, Classical.choice, Quot.sound]` — no custom axiom.

---

## 1. What v_task69 left open

v_task69 §(e) closed the *algebraic* half of item (2) — `species_adamsStable_iff`
on top of `DRing.species_comp_psi` (`φ_{H,h} ∘ ψᵃ = φ_{H,hᵃ}`) — and flagged the
analytic half as missing: "values lie in `ℤ[ζ_{|G|}]`, `σ_a ∘ φ_{H,h} = φ_{H,hᵃ}`,
`ℤ[ζ] ∩ ℚ = ℤ`", plus the coset-dependence lemma that makes the index set
`{(H, hH')}` well defined at all.  All of that except the one genuinely
Galois-theoretic statement is now proven.

## 2. Proven, unconditionally

### (a) Coset-dependence — the lemma v_task69 flagged

`φ_{H,h}` only sees the coset `h·⁅H,H⁆`.  Reason found in the actual Lean
definition: `MonGSet.fixedWeight H x : H →* A` is a **homomorphism** into a
*commutative* group (Müller's degeneration at a fixed point), so it kills the
derived subgroup of `H` — no character sum manipulation needed.

| lemma | statement |
|---|---|
| `MonGSet.fixedWeight_commutator` | `d ∈ commutator ↥H → X.fixedWeight H x d = 1` |
| `MonGSet.speciesSum_mul_commutator` | `speciesSum χ H (h*d) X = speciesSum χ H h X` |
| `MonRing.speciesHom_mul_commutator` | same, semiring level |
| `MonRing.species_mul_commutator` | `φ_{H,h·d} = φ_{H,h}` as ring homs on `B^A(G)` |
| `map_commutator_subtype` | `(commutator ↥H).map H.subtype = ⁅H,H⁆` |
| `mem_commutator_of_coe` | `(k : G) ∈ ⁅H,H⁆ → k ∈ commutator ↥H` |
| **`DRing.species_congr_coset`** | `(h : G) * (k : G)⁻¹ ∈ ⁅H,H⁆ → φ_{H,h} = φ_{H,k}` |

The last one is stated in exactly the `⁅H,H⁆ ≤ G` language that
`Even/ConductorDictionary.lean` (`pairNormalizer`, `FullyFused`) uses; the two
bridge lemmas convert between `commutator ↥H` and `⁅H,H⁆`.  This is what makes
`ConductorPairDictionary`'s indexing by cosets `hH'` legitimate.

### (b) Integrality

| lemma | statement |
|---|---|
| `isIntegral_of_pow_eq_one` | `0 < n → z ^ n = 1 → IsIntegral ℤ z` |
| `isIntegral_fixedWeight` | each species summand is a `|H|`-th root of unity, hence integral |
| `isIntegral_speciesSum` | `IsIntegral ℤ (speciesSum (Units.coeHom ℂ) H h X)` |
| `isIntegral_speciesHom` | same on the skeleton `Skel G ℂˣ` |
| **`DRing.isIntegral_species`** | `∀ x : D(G), IsIntegral ℤ (φ_{H,h} x)` |

Note the proof does *not* need cyclotomic fields as objects: a species value is
a finite sum of elements of `ℂˣ` of order dividing `Nat.card ↥H`
(`pow_card_eq_one'`), each integral by `IsIntegral.of_pow`, and the integral
elements form the subalgebra `integralClosure ℤ ℂ`.  On `D(G)` an element is a
difference of two skeleton classes, so `IsIntegral.sub` finishes.

### (c) Rational ⟹ integer, and the integer point it produces

| lemma | statement |
|---|---|
| `exists_int_of_isIntegral_rat` | `IsIntegral ℤ z → z = (q : ℂ) → ∃ n : ℤ, z = n` |
| `Even.species_exists_int` | ℚ-valued species ⟹ each value is an `ℤ`-cast |
| **`Even.DRing.exists_intPoint_of_species_rat`** | `(∀ x, ∃ q : ℚ, φ_{H,h} x = q) → ∃ p : D(G) →+* ℤ, complexify p = φ_{H,h}` |

`exists_int_of_isIntegral_rat` is `IsIntegral.tower_bot` down `ℤ ⊆ ℚ ⊆ ℂ`
followed by `IsIntegrallyClosed.isIntegral_iff` for `ℤ`.  The last theorem is
the **converse half of item (1)**: it turns "the species is rational" into an
honest integer point of `D(G)`, which is the object `conductor` ranges over.
The ring-hom structure is transported through `Int.cast_injective`.

### (d) Assembly — an integer species point is fully fused

```
theorem fullyFused_of_intPoint (hgal : GaloisSpeciesTwist) (hsep : SpeciesPairSeparation)
    (H : Subgroup G) (h : H) {p : DRing G →+* ℤ}
    (hp : complexify (DRing G) p = DRing.species H h) : FullyFused H h
```

matching `FullyFused` verbatim as defined in `Even/ConductorDictionary.lean`
(`∀ a coprime to |G|, ∃ g ∈ N_G(H), (g h g⁻¹)(hᵃ)⁻¹ ∈ ⁅H,H⁆`).  Two further
results on the way:

* `Even.species_pow_eq_of_intPoint` : `φ_{H,hᵃ} = φ_{H,h}` for `a` coprime to
  `|G|`, whenever `φ_{H,h}` is an integer point.
* `Even.adamsStable_of_intPoint` : hence `AdamsStable G (φ_{H,h})`, closing the
  loop with v_task69's `species_adamsStable_iff`.

**A simplification worth recording.**  The argument does *not* need `σ` to fix
`ℚ` — every ring hom `ℂ →+* ℂ` fixes `ℤ` automatically (`map_intCast`).  So the
arithmetic input is exactly (b)+(c): values are algebraic integers, and a
rational algebraic integer is an integer.  That is why the Galois hypothesis
below can be stated with a bare `ℂ →+* ℂ` and no field-theory side conditions.

## 3. The two named hypotheses (0 sorries; honest stubs)

```
def GaloisSpeciesTwist : Prop :=
  ∀ (G) [Group G] [Fintype G] (H : Subgroup G) (h : H) (a : ℕ),
    Nat.Coprime a (Nat.card G) →
      ∃ σ : ℂ →+* ℂ, σ.comp (DRing.species H h) = DRing.species H (h ^ a)

def SpeciesPairSeparation : Prop :=
  ∀ (G) [Group G] [Fintype G] (H : Subgroup G) (h k : H),
    DRing.species H h = DRing.species H k →
      ∃ g ∈ Subgroup.normalizer H, (g * (h : G) * g⁻¹) * (k : G)⁻¹ ∈ ⁅H,H⁆
```

* `GaloisSpeciesTwist` is the cyclotomic Galois action `ζ ↦ ζᵃ` on `|G|`-th
  roots of unity, extended to `ℂ`.  Standard, but formalizing it means either
  choosing a compatible system of embeddings `ℚ(ζ_n) ↪ ℂ` and extending by
  Steinitz/Zorn, or refactoring the species to land in `ℤ[ζ_{exp G}]` instead of
  `ℂ`.  **The second route is the recommended one** (see §5).
* `SpeciesPairSeparation` is item (1) of the v_task68 chain, restricted to a
  common `H` — the statement that Müller's species table is indexed by pair
  *classes*.  Its "only if" direction is already proven
  (`DRing.species_conj` + the new `species_congr_coset`); the converse is the
  open half.

## 4. What remains of item (2)

Nothing analytic, except `GaloisSpeciesTwist`.  Concretely, of the four things
v_task69 listed as missing:

| v_task69 item | status now |
|---|---|
| coset-dependence of `φ_{H,h}` | **PROVEN** (`species_congr_coset`) |
| values lie in `ℤ[ζ_{|G|}]` | **PROVEN** in the form actually needed: `IsIntegral ℤ` |
| `ℤ[ζ] ∩ ℚ = ℤ` | **PROVEN** (`exists_int_of_isIntegral_rat`) |
| `σ_a ∘ φ_{H,h} = φ_{H,hᵃ}` | **hypothesis** `GaloisSpeciesTwist` |
| integer point ⟹ fully fused | **PROVEN from it** (`fullyFused_of_intPoint`) |
| ℚ-valued species ⟹ integer point exists | **PROVEN** |

## 5. Updated remaining surface for `ConductorPairDictionary`

Three named Props now stand between the Lean development and the dictionary
(down from four items stated informally in v_task68):

1. **`SpeciesPairSeparation`** — species determine the pair class (item (1)).
2. **`GaloisSpeciesTwist`** — the cyclotomic Galois action on species.
3. **The conductor computation** `conductor = (N_G(H,hH') : H')` for the point
   `φ_{H,h}` (Müller Satz 2.3.3 proper), plus the surjectivity statement that
   *every* integer point of `D(G)` is a species — the remaining half of item (1).

Estimated effort, unchanged in kind but reduced in size:

* (2) is the only genuinely new mathematics-in-Lean and is best killed by
  **retargeting the species at `ℤ[ζ_N]`, `N = exp G`** (a `MonoidHom ℂˣ`-free
  formulation), where Mathlib's `IsCyclotomicExtension` / `IsPrimitiveRoot`
  API gives `σ_a` directly and `species_comp_psi` transports unchanged.
  Estimate: a self-contained ~300-line file, no dependence on the rest.
* (1) is a counting/orthogonality argument on the species table; the
  `SpeciesInjectivity` machinery (Dedekind independence, `count_eq_of_speciesSum_eq`)
  is the right tool and is already in the repo.
* (3) is the last one and needs the primitive idempotents of `D(G) ⊗ ℚ`, i.e.
  genuine ghost-ring bookkeeping.  Unchanged in difficulty.

Everything downstream (`BCSeparation`, `ATSeparation`, `OrderTransfer`,
`isIndexValue_iff`) is unaffected and still compiles.
