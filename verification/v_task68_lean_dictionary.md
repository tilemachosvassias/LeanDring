# v_task68 — the conductor dictionary, formalized: `LeanDring/Even/ConductorDictionary.lean`

Date 2026-08-08.  File: `lean_dring/LeanDring/Even/ConductorDictionary.lean`
(new, ~250 lines).  Checked serially, one taskset-pinned process:

```
cd lean_dring
taskset -c 0 lake build LeanDring.Even.BCSeparation        # unchanged, 0 errors
taskset -c 0 lake env lean LeanDring/Even/ConductorDictionary.lean
taskset -c 0 lake env lean LeanDring/Even/ATSeparation.lean # unchanged, 0 errors
```

**0 errors, 0 warnings, 0 `sorry`** (the single string `sorry` in the file is
prose in the module docstring).  Nothing shared was edited, so
`BCSeparation`/`ATSeparation` are untouched and still compile.

---

## 1. What the existing formal definitions actually are

This matters, because the dictionary can only be as faithful as they are.

* `DRing G := MonRing G ℂˣ = GrothendieckRing (MonGSet.Skel G ℂˣ)`
  (`Theory/DRing/Monomial.lean:307`) — the `ℂˣ`-fibered Burnside ring.
* `DRing.species (H : Subgroup G) (h : H) : DRing G →+* ℂ`
  (`Theory/DRing/Species.lean:236`) — Müller's species, ℂ-valued, indexed by
  *pairs*, conjugation-invariant (`SpeciesConj.species_conj`), and jointly
  injective (`SpeciesInjectivity.species_injective`).
* **`conductor` is not defined via species at all.**
  `Even/OrderTransfer.lean:85`:
  ```
  Isolates p x n  :=  p x = n ∧ ∀ q : R →+* ℂ, q ≠ complexify p → q x = 0
  conductor R p   :=  sInf {n | 0 < n ∧ ∃ x, Isolates p x n}     -- p : R →+* ℤ
  conductorMultiplicity R c := Nat.card {p : R →+* ℤ // conductor R p = c}
  ```
  i.e. the conductor is the least positive value isolated at an **integer
  point** `p : DRing G →+* ℤ` — ring-theoretically `x = n·e_p`, so this *is*
  Müller's Führer of the primitive idempotent, stated basis-free.  That
  basis-freeness is exactly why `conductorMultiplicity_eq_of_ringEquiv`
  (`OrderTransfer.lean:150`) is unconditional, and hence why
  `IsIndexValue.transfer` works.
* `IsIndexValue G x := ∃ c, conductorMultiplicity (DRing G) c ≠ 0 ∧ c * x = |G|`
  (`BCSeparation.lean:199`).

Müller's index set (`sources/mueller_dissertation.md:950–963`):
`D(G) = {(H,hH') : H ≤ G, h ∈ H}`, `H' = ⁅H,H⁆`, `G` acting by simultaneous
conjugation, `N_G(H,hH')` the stabilizer, with
`H ≤ H·C_G(H) ≤ N_G(H,hH') ≤ N_G(H)`.  **Satz 2.3.3**: the Führer of
`e^{D(G)}_{(H,hH')}` is `(N_G(H,hH') : H')`.

## 2. The fusion caveat — a genuine finding, not a technicality

`conductor` quantifies over **integer** points `DRing G →+* ℤ`, but
`DRing.species H h` is ℂ-valued and lands in `ℤ[ζ]` in general.  A species is
ℤ-valued exactly when it is fixed by the Galois action `hH' ↦ h^a H'`,
`gcd(a,|G|)=1` — the **fully fused / rational** classes
(`docs/normalization_program_step1.md:25` says the same: "the rational species
are exactly the fully fused classes").  So the honest dictionary in *this*
formalization is

> `conductorMultiplicity (DRing G) c ≠ 0` ⟺ `c = (N_G(H,hH') : H')` for some
> **fully fused** pair class `(H,hH')`.

Consequences for the campaign, both benign:

* **BC-n hypothesis `hB`** (existence of an index value `v`) is witnessed by
  `H = ⟨−r_e⟩` with the **identity coset** `h = 1`; identity-coset pairs are
  trivially fully fused, so the witness survives the restriction.
* **BC-n hypothesis `hC` / AT hypothesis** (universal statements over all
  index values) become *weaker* under the restriction — fewer pairs to check.
  So the restriction can only help the assumed side.

`FullyFused` is defined in the file so the qualifier is on the record rather
than silently dropped.

## 3. What is proven

New group theory, proven outright in Mathlib (no hypotheses):

| lemma | statement |
|---|---|
| `conj_mem_commutator_of_mem_normalizer` | `g ∈ N_G(H), d ∈ ⁅H,H⁆ ⟹ gdg⁻¹ ∈ ⁅H,H⁆` |
| `pairNormalizer H h : Subgroup G` | `{g ∈ N_G(H) : ghg⁻¹h⁻¹ ∈ ⁅H,H⁆}` — **now a subgroup** (BCSeparation had only a `Set`); closure proofs use the identity `abh(ab)⁻¹h⁻¹ = a(bhb⁻¹h⁻¹)a⁻¹·(aha⁻¹h⁻¹)` |
| `coe_pairNormalizer` | it is `rfl`-equal to `BCSeparation.PairNormalizer`, so the erratum-repair lemma there is about this object |
| `pairNormalizer_le_normalizer'` | `N_G(H,hH') ≤ N_G(H)` (subgroup form of the v_task65 repair) |
| `le_pairNormalizer` | `H ≤ N_G(H,hH')` for `h ∈ H` (Müller's `H ≤ HC_G(H) ≤ N_G(H,hH')`) |
| `commutator_le_pairNormalizer` | `H' ≤ N_G(H,hH')` |
| `card_commutator_dvd_card_pairNormalizer` | `\|H'\| ∣ \|N_G(H,hH')\|` — the index `(N_G(H,hH'):H')` is an honest ℕ |
| `pairNormalizer_bot`, `fullyFused_bot` | `N_G(1,1) = G`, and the trivial pair is fully fused |

Group-theoretic side, defined division-free:

```
IsIndStarValue G x := ∃ (H : Subgroup G) (h : H), FullyFused H h ∧
    x * Nat.card (pairNormalizer H h) = Nat.card G * Nat.card ⁅H, H⁆
```

(`x·|N_G(H,hH')| = |G|·|H'|`, i.e. `x = |G| / (N_G(H,hH') : H')`.)

The one named hypothesis (Satz 2.3.3 + §2 fusion identification):

```
ConductorPairDictionary : Prop :=
  ∀ (G) [Group G] [Fintype G] (c : ℕ),
    conductorMultiplicity (DRing G) c ≠ 0 ↔
      ∃ (H : Subgroup G) (h : H), FullyFused H h ∧
        c * Nat.card ⁅H, H⁆ = Nat.card (pairNormalizer H h)
```

**The theorem** (`isIndexValue_iff`), proven from it:

```
theorem isIndexValue_iff (hdict : ConductorPairDictionary.{u})
    (G : Type u) [Group G] [Fintype G] (x : ℕ) :
    IsIndexValue G x ↔ IsIndStarValue G x
```

Both directions are real: `←` requires producing the conductor
`c = |N_G(H,hH')| / |H'|`, which needs `card_commutator_dvd_card_pairNormalizer`
and cancellation by `|H'| > 0`.  Corollaries: `isIndexValue_one` (orientation
sanity check — the trivial pair `(1,1)` has conductor `|G|`, so `ind* = 1` is
always an index value, matching Satz 2.3.4) and `IsIndStarValue.transfer`
(index values in `ind*` form transport along `DRing G ≃+* DRing H`).

## 4. Axiom audit

```
conj_mem_commutator_of_mem_normalizer   : [propext, Classical.choice, Quot.sound]
le_pairNormalizer                        : [propext, Classical.choice, Quot.sound]
commutator_le_pairNormalizer             : [propext, Classical.choice, Quot.sound]
card_commutator_dvd_card_pairNormalizer  : [propext, Classical.choice, Quot.sound]
pairNormalizer_bot                       : [propext, Classical.choice, Quot.sound]
fullyFused_bot                           : [propext, Classical.choice, Quot.sound]
isIndexValue_iff                         : [propext, Classical.choice, Quot.sound]
isIndexValue_one                         : [propext, Classical.choice, Quot.sound]
IsIndStarValue.transfer                  : [propext, Classical.choice, Quot.sound]
```

No custom axiom, no `sorry`.

## 5. What remains — the lemma chain to discharge `ConductorPairDictionary`

The reduction is now one clean Prop, but that Prop is genuinely the whole of
Müller §2.3.  Discharging it needs, in order:

1. **`species_surjective_onto_points`** — every ring hom `DRing G →+* ℂ` is
   `DRing.species H h` for some pair, and `species H h = species U u` iff the
   pairs are `G`-conjugate.  (`species_injective` gives the *dual* statement —
   points separate ring elements — not this.  Needs: `D(G)` is spanned by the
   basis `[K,λ]`, and a ring hom is determined by its values there, plus the
   species-table triangularity of `Theory/DRing/Marks.lean` /
   `MarkInjectivity.lean`.)  **This is the largest single item.**
2. **`integerPoint_iff_fullyFused`** — `species H h` factors through `ℤ` iff
   `[H,hH']` is fully fused.  Needs: values of `species H h` are sums of
   `|G|`-th roots of unity, plus the Galois action on species
   (`species H h ∘ σ = species H (h^a)`), plus `ℤ[ζ] ∩ ℚ = ℤ`.
3. **`idempotent_exists`** — for each point `p`, the primitive idempotent
   `e_p ∈ D_{ℚ(ζ)}(G)` exists and `Isolates p x n ↔ x = n·e_p`.  Needs the
   species table to be invertible over ℚ(ζ), i.e. `species_injective`
   upgraded to a basis statement (`Theory/DRing/Marks.lean` has the Burnside
   analogue).
4. **`conductor_eq_index`** — Müller formula (2.8)
   `e^{D(G)}_{(H,hH')} = (N_G(H,hH'):H')⁻¹ · ind^G_H((H:H')·e^{D(H)}_{(H,hH')})`,
   and the coefficient computation showing the Führer is exactly
   `(N_G(H,hH') : H')`.  This is Müller's own proof of Satz 2.3.3 and needs
   induction `ind^G_H` on `D`, which the corpus has in
   `Theory/DRing/Induced.lean` (worth checking how far it goes).

**Honest effort estimate.**  Item 1 alone is a multi-session job (it is the
D-ring analogue of `MarkInjectivity`, and the existing `species_injective`
proof — Dedekind independence + minimal-orbit induction — is ~430 lines).
Items 2–3 are each ~1 session given item 1.  Item 4 needs `Induced.lean` to
carry a working `ind^G_H` with a Mackey/coefficient formula; if it does not,
add another 1–2 sessions.  **Total: 4–6 focused sessions**, and it is the
right next target, because it simultaneously discharges
`SimpleRigidity.ConductorDictionary` (the conductor-`1` case, `= perfect
self-normalizing classes`) and `OrderTransfer.MullerIsolation` /
`MullerTrivialBound` (Satz 2.3.4), i.e. three currently-open Props in the
`Even/` layer collapse to one.

A cheaper intermediate milestone, if the full chain stalls: prove the *easy
inequality* `conductor p ≤ |G|` for all integer points (`MullerIsolation`
alone), which already gives `IsIndexValue G x → x ≥ 1` uniformly and makes
`mullerOrder (D(G)) ≤ |G|` unconditional.
