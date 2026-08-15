# v_task77 — the fusion count (orbit–stabilizer) and the λ-twisted
# column sums; `SpeciesConductorLowerBound` for self-normalizing `H`

Date 2026-08-08.  `lean_dring/LeanDring/Even/ConductorAtSpecies.lean`
extended by §8–§9 (~300 lines).  0 `sorry`, 0 errors, 0 warnings, no
custom axiom; full serial `lake build` clean (4718 jobs).

**Status: further REDUCED, still not discharged in general.**  Stage 1
(the cheap sharpening) landed in full and yields a genuinely new
unconditional theorem plus a new proven case of
`SpeciesConductorLowerBound`.  Stage 2 (the twisted column sums) landed as
Lean theorems, and in the process turned out to be **provably unable** to
close the general case — see "the obstruction, sharpened" below.  Stage 3
(`SpeciesIsolatingWitness`) was therefore not attempted.

## Stage 1 — the fusion count, by double counting

The incidence relation

```lean
def Fuses (h : H) (g : ↥(Subgroup.normalizer (H : Set G))) : Prop :=
  (g : G) * (h₀ : G) * (g : G)⁻¹ * (h : G)⁻¹ ∈ ⁅H, H⁆
```

("`g` carries the coset `h₀H'` to `hH'`") is counted in both directions.

* **Left fibres** (`card_fuses_left`): for fixed `g ∈ N_G(H)` the set of
  `h` is the coset `g h₀ g⁻¹ · H'`, in bijection with `H'` under
  `h ↦ g h₀ g⁻¹ h⁻¹`.  Size `|H'|`.
* **Right fibres**: for `h` *outside* the fusion class the fibre is empty
  (`isEmpty_fuses`: `species_conj_of_mem_normalizer` +
  `DRing.species_congr_coset` would force `φ_{H,h} = φ_{H,h₀}`); for `h`
  *inside* it, `speciesPairSeparation` supplies one `g₀`, and the fibre is
  the coset `g₀ · N_G(H,h₀H')` (`card_fuses_right`), of size
  `|N_G(H,h₀H')|`.  Both membership computations are `conj_mem_commutator_of_mem_normalizer`
  applied to a free-group identity discharged by `group`.

The double count (`Finset.card_filter` + `Finset.sum_comm`) gives

```lean
theorem card_fusionClass_mul_card_pairNormalizer (H : Subgroup G) (h₀ : H) :
    Nat.card {h : H // DRing.species H h = DRing.species H h₀} *
        Nat.card ↥(pairNormalizer H (h₀ : G)) =
      Nat.card ↥(Subgroup.normalizer (H : Set G)) * Nat.card ↥⁅H, H⁆
```

i.e. `#fusion = |H'| · (N_G(H) : N_G(H,h₀H'))` — the orbit–stabilizer
statement asked for, in division-free form.  Fed into v_task76's
`card_dvd_mul_fusionCount`:

```lean
theorem card_mul_card_pairNormalizer_dvd … (hx : Isolates p x n) :
    Nat.card ↥H * Nat.card ↥(pairNormalizer H (h₀ : G)) ∣
      n * (Nat.card ↥(Subgroup.normalizer (H : Set G)) * Nat.card ↥⁅H, H⁆)
```

**unconditionally** — `|H|·|N_G(H,h₀H')| ∣ n·|H'|·|N_G(H)|`.

### The gcd relation with Müller's target

Write `N = N_G(H)`, `P = N_G(H,h₀H')`, so `H' ≤ H ≤ P ≤ N` and
`m := (N : P)` is the orbit length.  The bound above is
`(H : H') ∣ n · m`.  Müller's target is `|P| ∣ n·|H'|`, i.e.
`(P : H') = (H : H')·(P : H) ∣ n`.  So the two agree **iff `m = 1` and
`P = H`**, i.e. iff `N_G(H) = H`.  (The guess recorded in v_task76 — that
`P = N` suffices — is *not* enough: it gives `(H:H') ∣ n`, while the target
is then `(N:H') ∣ n`.)  Hence:

```lean
theorem speciesConductorLowerBound_of_selfNormalizing
    (hself : Subgroup.normalizer (H : Set G) = H) … :
    Nat.card ↥(pairNormalizer H (h₀ : G)) ∣ n * Nat.card ↥⁅H, H⁆
```

**`SpeciesConductorLowerBound` holds at every self-normalizing subgroup**,
unconditionally, for every `h₀`.  This strictly contains v_task76's
`speciesConductorLowerBound_top` (`H = ⊤`) and covers, e.g., every
maximal non-normal subgroup, every Sylow normalizer, every Carter
subgroup.

## Stage 2 — the λ-twisted column sums

```lean
noncomputable def twistedSum (H : Subgroup G) [Fintype ↥H] (lam : H →* ℂˣ) :
    DRing G →+ ℂ := fun y ↦ ∑ h : H, (lam h)⁻¹ * DRing.species H h y
```

On a basis element the inner sum is a character sum over `H` for the
homomorphism `(μ ∘ conj_q) · λ⁻¹ : H →* ℂˣ`, so `sum_hom_units` collapses
it exactly as in v_task76:

```lean
theorem exists_twistedSum_basisElt … : ∃ m : ℕ,
    twistedSum H lam (DRing.basisElt K l) = (Nat.card ↥H : ℂ) * m
theorem exists_twistedSum … (y : DRing G) : ∃ m : ℤ,
    twistedSum H lam y = (Nat.card ↥H : ℂ) * m
theorem exists_twisted_fusion_sum … (hx : Isolates p x n) : ∃ m : ℤ,
    (n : ℂ) * ∑ h ∈ univ.filter (fun h : H => φ_{H,h} = φ_{H,h₀}),
      ((lam h)⁻¹ : ℂ) = (Nat.card ↥H : ℂ) * m
```

The `m` on `[K,μ]` is the count of `H`-fixed cosets `q` of `G ⧸ K` with
`μ ∘ conj_q = λ` — the same good-coset count as
`card_pairNormalizer_eq_mul`.  **Notably no `ℤ[ζ]` is needed**: although
the summands are roots of unity, every value of `twistedSum` is a
rational integer multiple of `|H|`, so `IsIntegral`/cyclotomic machinery
never enters.  (v_task76 predicted this step would live in the ring of
algebraic integers; it does not.)

### The obstruction, sharpened — why stage 2 cannot close the general case

Every `λ : H →* ℂˣ` is trivial on `⁅H,H⁆` (target abelian), so the fusion
class — a union of `m` cosets of `H'` by stage 1 — contributes

`∑_{h ∈ fusion} λ(h)⁻¹ = |H'| · Σ_λ`,  `Σ_λ := ∑_{j=1}^{m} λ(h_j)⁻¹`

over orbit representatives `h_j`.  The whole family of stage-2 relations
is therefore

`(H : H') ∣ n · Σ_λ`  for all `λ ∈ Hom(H, ℂˣ)`,

and the ideal of `ℤ[ζ]` generated by `{Σ_λ}` already contains
`∑_λ λ(h₀)Σ_λ = (H:H')`, while each individual relation is implied by the
untwisted one after multiplying by a root of unity.  So the twisted
family is **equivalent to**, not stronger than, `|H| ∣ n·#fusion` — the
stage-1 bound.  The missing factor `(N_G(H,h₀H') : H)` is invisible to
the `H`-column of the species table, twisted or not; it is a statement
about the *inverse* species table (the coefficient of `[H,1]_G` in
`e_{(H,hH')}`), i.e. about `ind^G_H`.  This confirms and sharpens the
diagnosis of v_task76 §"Why the route … does not close the general case":
**both remaining halves need `ind^G_H`, and nothing short of it.**

Stage 3 (`SpeciesIsolatingWitness`) was not attempted: its witness is
`ind^G_H` of the Burnside-style idempotent, so it depends on exactly the
machinery just shown to be unavoidable.

## Verification

```
taskset -c 0 lake build LeanDring.Even.ConductorAtSpecies   # 0 err, 0 warn
taskset -c 0 lake build                                     # clean, serial, 4718 jobs
```

Axiom audit (in-file `#print axioms`) for the eleven new declarations
`commutator_le_self`, `card_fuses_left`, `isEmpty_fuses`,
`card_fuses_right`, `card_fusionClass_mul_card_pairNormalizer`,
`card_mul_card_pairNormalizer_dvd`,
`speciesConductorLowerBound_of_selfNormalizing`,
`exists_twistedSum_basisElt`, `exists_twistedSum`,
`exists_twisted_fusion_sum` (and `twistedSum_apply`):

```
[propext, Classical.choice, Quot.sound]
```

No new imports.  The file is still not imported by the root module.

## Remaining surface of `ConductorPairDictionary`

1. `SpeciesIsolatingWitness` — `ind^G_H`, the Burnside top idempotent,
   Möbius `μ(H,G)`, Boltje's congruence.  ≥ 2 sessions.  Untouched.
2. `SpeciesConductorLowerBound` — proven for **every self-normalizing
   `H`** (hence at `⊤`), and in general in the weaker form
   `(H:H') ∣ n·(N_G(H) : N_G(H,h₀H'))`.  The residual gap is the single
   factor `(N_G(H,h₀H') : H)`, and it is now known **not** to be
   reachable from the `H`-column of the species table: it needs `ind^G_H`
   — the same input as item 1.

Net effect: the two remaining halves are no longer independent problems.
A single piece of machinery (`ind^G_H` + Boltje/Möbius integrality)
discharges both, and no cheaper route through species columns exists.
